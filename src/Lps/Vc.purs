-- | Verification-condition generation: checking-mode traversal of each
-- | spec'd declaration (see docs/PLAN.md, "Semantics"). Sound but
-- | deliberately imprecise: anything outside the embeddable fragment is a
-- | per-function error, never a silent pass (ADR-006).
module Lps.Vc
  ( Obligation
  , FnResult
  , checkModule
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Lps.CoreFn.Types (Alt, AltResult(..), Bind(..), Binder(..), Expr(..), Literal(..), Module, Qualified, Span, spanOf)
import Lps.Logic (Op(..), Sort, Term(..), subst, sortOf, tTrue)
import Lps.Resolve (Prim(..), PrimTable, buildTable, resolveGlobal)
import Lps.Spec.Syntax (RType, SpecFile, baseSort)

type Env = Map String Sort

type Ctx = { env :: Env, assumps :: Array Term }

type Obligation =
  { fnName :: String
  , span :: Span
  , decls :: Array (Tuple String Sort)
  , assumps :: Array Term
  , goal :: Term
  }

type FnResult = { fnName :: String, result :: Either String (Array Obligation) }

type St = { table :: PrimTable, modName :: String }

checkModule :: Module -> SpecFile -> Array FnResult
checkModule mod spec =
  Map.toUnfoldable spec.fns <#> \(Tuple fnName fnSpec) ->
    { fnName
    , result: case Map.lookup fnName declMap of
        Nothing -> Left "no declaration with this name in the module"
        Just expr -> checkFn st fnName fnSpec expr
    }
  where
  st = { table: buildTable mod, modName: mod.name }

  declMap :: Map String Expr
  declMap = Map.fromFoldable (Array.concatMap flat mod.decls)
    where
    flat = case _ of
      NonRec name expr -> [ Tuple name expr ]
      Rec binds -> map (\b -> Tuple b.name b.expr) binds

checkFn
  :: St
  -> String
  -> { args :: Array RType, result :: RType }
  -> Expr
  -> Either String (Array Obligation)
checkFn st fnName fnSpec = peel [] emptyCtx fnSpec.args
  where
  emptyCtx = { env: Map.empty, assumps: [] }

  -- Peel one lambda per spec argument, renaming spec binders to the
  -- CoreFn binder names as we go.
  peel :: Array (Tuple String String) -> Ctx -> Array RType -> Expr -> Either String (Array Obligation)
  peel sub ctx argSpecs expr = case Array.uncons argSpecs of
    Nothing -> do
      let res = fnSpec.result { pred = applySub sub fnSpec.result.pred }
      checkBody st fnName ctx res expr
    Just { head: a, tail } -> case expr of
      EAbs _ x body ->
        let
          sub' = if a.binder == "_" then sub else Array.snoc sub (Tuple a.binder x)
          assumption = applySub sub' a.pred
          ctx' =
            { env: Map.insert x (baseSort a.base) ctx.env
            , assumps: pushNonTrivial assumption ctx.assumps
            }
        in
          peel sub' ctx' tail body
      _ -> Left "body has fewer lambdas than the spec has arguments"

applySub :: Array (Tuple String String) -> Term -> Term
applySub sub t = Array.foldl (\acc (Tuple b n) -> subst b (TVar n) acc) t sub

pushNonTrivial :: Term -> Array Term -> Array Term
pushNonTrivial t ts = if t == tTrue then ts else Array.snoc ts t

checkBody :: St -> String -> Ctx -> RType -> Expr -> Either String (Array Obligation)
checkBody st fnName ctx res = case _ of
  ECase _ [ scrut ] alts -> do
    scrutT <- embed st ctx.env scrut
    checkAlts st fnName ctx res scrutT alts
  ECase _ _ _ -> Left "multi-scrutinee case is unsupported in the slice"
  ELet _ binds body -> do
    ctx' <- foldM (bindLet st) ctx binds
    checkBody st fnName ctx' res body
  EAbs _ _ _ -> Left "lambda beyond the spec's arity (HOF unsupported in the slice)"
  e -> do
    t <- embed st ctx.env e
    let goal = subst res.binder t res.pred
    pure [ mkObligation fnName (spanOf e) ctx goal ]

mkObligation :: String -> Span -> Ctx -> Term -> Obligation
mkObligation fnName span ctx goal =
  { fnName
  , span
  , decls: Map.toUnfoldable ctx.env
  , assumps: ctx.assumps
  , goal
  }

bindLet :: St -> Ctx -> Bind -> Either String Ctx
bindLet st ctx = case _ of
  NonRec x e -> do
    t <- embed st ctx.env e
    sort <- case sortOf ctx.env t of
      Just s -> Right s
      Nothing -> Left ("cannot infer sort of let-bound " <> x)
    pure
      { env: Map.insert x sort ctx.env
      , assumps: Array.snoc ctx.assumps (TBin Eq (TVar x) t)
      }
  Rec _ -> Left "recursive let is unsupported in the slice"

checkAlts :: St -> String -> Ctx -> RType -> Term -> Array Alt -> Either String (Array Obligation)
checkAlts st fnName ctx res scrutT alts = do
  result <- foldM step { negs: [], obls: [] } alts
  pure result.obls
  where
  step acc alt = case alt.binders of
    [ BLit (LBool true) ] -> do
      obls <- withPath acc.negs [ scrutT ] alt.result
      pure { negs: Array.snoc acc.negs (TNot scrutT), obls: acc.obls <> obls }
    [ BLit (LBool false) ] -> do
      obls <- withPath acc.negs [ TNot scrutT ] alt.result
      pure { negs: Array.snoc acc.negs scrutT, obls: acc.obls <> obls }
    [ BNull ] -> do
      obls <- withPath acc.negs [] alt.result
      pure { negs: acc.negs, obls: acc.obls <> obls }
    [ BVar x ] -> do
      sort <- case sortOf ctx.env scrutT of
        Just s -> Right s
        Nothing -> Left "cannot infer scrutinee sort"
      let binding = TBin Eq (TVar x) scrutT
      obls <- withPathIn
        (ctx { env = Map.insert x sort ctx.env })
        acc.negs
        [ binding ]
        alt.result
      pure { negs: acc.negs, obls: acc.obls <> obls }
    [ b ] -> Left ("unsupported binder in the slice: " <> binderTag b)
    _ -> Left "multi-binder alternative is unsupported in the slice"

  withPath = withPathIn ctx

  withPathIn baseCtx negs conds altResult =
    let
      ctx' = baseCtx { assumps = baseCtx.assumps <> negs <> conds }
    in
      case altResult of
        Unconditional e -> checkBody st fnName ctx' res e
        Guarded gs -> do
          result <- foldM
            ( \acc g -> do
                gt <- embed st ctx'.env g.guard
                obls <- checkBody st fnName
                  (ctx' { assumps = ctx'.assumps <> acc.notPrev <> [ gt ] })
                  res
                  g.expr
                pure { notPrev: Array.snoc acc.notPrev (TNot gt), obls: acc.obls <> obls }
            )
            { notPrev: [], obls: [] }
            gs
          pure result.obls

binderTag :: Binder -> String
binderTag = case _ of
  BLit _ -> "literal binder"
  BVar _ -> "var binder"
  BNull -> "null binder"
  BOther t -> t

-- | Embed a CoreFn expression as a logic term.
embed :: St -> Env -> Expr -> Either String Term
embed st env = go
  where
  go = case _ of
    ELit _ (LInt n) -> pure (TInt n)
    ELit _ (LBool b) -> pure (TBool b)
    ELit sp (LOther tag) -> cannot sp ("literal " <> tag)
    EVar sp q -> embedVar sp q
    e@(EApp _ _ _) -> embedApp e
    e -> cannot (spanOf e) (exprTag e)

  cannot sp what = Left
    ( "cannot embed " <> what <> loc <> " (outside the slice fragment)"
    )
    where
    -- synthetic nodes carry a 0,0 span
    loc = if sp.startLine == 0 then "" else " at line " <> show sp.startLine

  embedVar sp q = case q.modName of
    Nothing ->
      if Map.member q.ident env then pure (TVar q.ident)
      else cannot sp ("unbound variable " <> q.ident)
    Just "Data.Boolean" | q.ident == "otherwise" -> pure (TBool true)
    Just m -> cannot sp ("reference to " <> m <> "." <> q.ident)

  embedApp e = do
    let spine = flatten e []
    case spine.head of
      EVar sp q -> case localPrim q of
        Just prim -> applyPrim sp prim spine.args
        Nothing -> case Array.uncons spine.args of
          Just { head: EVar _ dict, tail } ->
            case resolveGlobal q dict of
              Just prim -> applyPrim sp prim tail
              Nothing -> cannot sp ("call to " <> qualShow q)
          _ -> cannot sp ("call to " <> qualShow q)
      other -> cannot (spanOf other) "higher-order application"

  localPrim q = case q.modName of
    Just m | m == st.modName -> Map.lookup q.ident st.table
    _ -> Nothing

  applyPrim sp prim args = do
    ts <- traverse go args
    case prim, ts of
      Prim2 op, [ l, r ] -> pure (TBin op l r)
      PrimNeg, [ t ] -> pure (TNeg t)
      PrimNot, [ t ] -> pure (TNot t)
      _, _ -> cannot sp "partially applied primitive"

  flatten expr args = case expr of
    EApp _ f a -> flatten f (Array.cons a args)
    head -> { head, args }

exprTag :: Expr -> String
exprTag = case _ of
  EVar _ _ -> "variable"
  ELit _ _ -> "literal"
  EAbs _ _ _ -> "lambda"
  EApp _ _ _ -> "application"
  ECase _ _ _ -> "case"
  ELet _ _ _ -> "let"
  EOther _ tag -> tag

qualShow :: Qualified -> String
qualShow q = case q.modName of
  Just m -> m <> "." <> q.ident
  Nothing -> q.ident
