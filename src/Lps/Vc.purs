-- | Verification-condition generation: checking-mode traversal of each
-- | spec'd declaration (see docs/PLAN.md, "Semantics"). Sound but
-- | deliberately imprecise: anything outside the embeddable fragment is a
-- | per-function error, never a silent pass (ADR-006).
-- |
-- | Phase 1: calls to spec'd functions emit precondition obligations at the
-- | call site and bind a fresh result variable carrying the instantiated
-- | result refinement; recursive calls assume the function's own spec
-- | (standard partial-correctness reasoning). `assume` specs do the same
-- | for imported/FFI functions, on trust. Call facts are scoped to the
-- | path that made the call, so a spec assumption justified under one
-- | branch never leaks into a sibling branch.
module Lps.Vc
  ( Obligation
  , FnResult
  , checkModule
  ) where

import Prelude

import Control.Monad.State.Trans (StateT, evalStateT, get, modify_, put)
import Control.Monad.Trans.Class (lift)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Traversable (for_, traverse)
import Data.Tuple (Tuple(..))
import Lps.CoreFn.Types (Alt, AltResult(..), Bind(..), Binder(..), Expr(..), Literal(..), Module, Qualified, Span, spanOf)
import Lps.Logic (Op(..), Sort, Term(..), subst, sortOf, tTrue)
import Lps.Resolve (FloatMap, Prim(..), PrimTable, buildFloats, buildTable, resolveGlobal)
import Lps.Spec.Syntax (FnSpec, RType, SpecFile, baseSort)

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

type St =
  { table :: PrimTable
  , floats :: FloatMap
  , modName :: String
  , spec :: SpecFile
  }

-- | Generator state. `fresh` only ever grows; `vars`/`facts`/`obls` are
-- | the call facts of the current scope (see `scoped`).
type GenSt =
  { fresh :: Int
  , vars :: Array (Tuple String Sort)
  , facts :: Array Term
  , obls :: Array Obligation
  }

type M a = StateT GenSt (Either String) a

throw :: forall a. String -> M a
throw = lift <<< Left

-- | Run a computation collecting its call facts separately, restoring the
-- | enclosing scope's facts afterwards (the fresh counter carries through).
scoped
  :: forall a
   . M a
  -> M { value :: a, vars :: Array (Tuple String Sort), facts :: Array Term, obls :: Array Obligation }
scoped m = do
  saved <- get
  put saved { vars = [], facts = [], obls = [] }
  value <- m
  st <- get
  put st { vars = saved.vars, facts = saved.facts, obls = saved.obls }
  pure { value, vars: st.vars, facts: st.facts, obls: st.obls }

-- | Extend a context with the call facts of a scoped run.
extend :: Ctx -> Array (Tuple String Sort) -> Array Term -> Ctx
extend ctx vars facts =
  { env: Map.union ctx.env (Map.fromFoldable vars)
  , assumps: ctx.assumps <> facts
  }

checkModule :: Module -> SpecFile -> Array FnResult
checkModule mod spec =
  Map.toUnfoldable spec.fns <#> \(Tuple fnName fnSpec) ->
    { fnName
    , result: case Map.lookup fnName declMap of
        Nothing -> Left "no declaration with this name in the module"
        Just expr -> evalStateT
          (checkFn st fnName fnSpec expr)
          { fresh: 0, vars: [], facts: [], obls: [] }
    }
  where
  st =
    { table: buildTable mod
    , floats: buildFloats mod
    , modName: mod.name
    , spec
    }

  declMap :: Map String Expr
  declMap = Map.fromFoldable (Array.concatMap flat mod.decls)
    where
    flat = case _ of
      NonRec name expr -> [ Tuple name expr ]
      Rec binds -> map (\b -> Tuple b.name b.expr) binds

checkFn :: St -> String -> FnSpec -> Expr -> M (Array Obligation)
checkFn st fnName fnSpec = peel [] emptyCtx fnSpec.args
  where
  emptyCtx = { env: Map.empty, assumps: [] }

  -- Peel one lambda per spec argument, renaming spec binders to the
  -- CoreFn binder names as we go.
  peel :: Array (Tuple String String) -> Ctx -> Array RType -> Expr -> M (Array Obligation)
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
      _ -> throw "body has fewer lambdas than the spec has arguments"

applySub :: Array (Tuple String String) -> Term -> Term
applySub sub t = Array.foldl (\acc (Tuple b n) -> subst b (TVar n) acc) t sub

pushNonTrivial :: Term -> Array Term -> Array Term
pushNonTrivial t ts = if t == tTrue then ts else Array.snoc ts t

checkBody :: St -> String -> Ctx -> RType -> Expr -> M (Array Obligation)
checkBody st fnName ctx res = case _ of
  ECase _ scruts alts -> do
    r <- scoped (traverse (embed st fnName ctx) scruts)
    let ctx0 = extend ctx r.vars r.facts
    obls <- checkAlts st fnName ctx0 res r.value alts
    pure (r.obls <> obls)
  ELet _ binds body -> do
    r <- scoped (foldM (bindLet st fnName) ctx binds)
    obls <- checkBody st fnName (extend r.value r.vars r.facts) res body
    pure (r.obls <> obls)
  EAbs _ _ _ -> throw "lambda beyond the spec's arity (HOF unsupported)"
  e -> do
    r <- scoped (embed st fnName ctx e)
    let
      ctx' = extend ctx r.vars r.facts
      goal = subst res.binder r.value res.pred
    pure (r.obls <> [ mkObligation fnName (spanOf e) ctx' goal ])

mkObligation :: String -> Span -> Ctx -> Term -> Obligation
mkObligation fnName span ctx goal =
  { fnName
  , span
  , decls: Map.toUnfoldable ctx.env
  , assumps: ctx.assumps
  , goal
  }

bindLet :: St -> String -> Ctx -> Bind -> M Ctx
bindLet st fnName ctx = case _ of
  NonRec x e -> do
    t <- embed st fnName ctx e
    -- sort inference must see fresh call-result vars, so consult the
    -- in-flight scope vars as well as the context env
    scope <- get
    let envNow = Map.union ctx.env (Map.fromFoldable scope.vars)
    sort <- case sortOf envNow t of
      Just s -> pure s
      Nothing -> throw ("cannot infer sort of let-bound " <> x)
    pure
      { env: Map.insert x sort ctx.env
      , assumps: Array.snoc ctx.assumps (TBin Eq (TVar x) t)
      }
  Rec _ -> throw "recursive let is unsupported"

-- | One alternative's binder row against the scrutinee terms.
type BinderRow =
  { conds :: Array Term -- literal equations this row must satisfy
  , binds :: Array { name :: String, term :: Term } -- var binders
  }

binderRow :: Ctx -> Array Term -> Array Binder -> Either String BinderRow
binderRow ctx scruts binders =
  if Array.length binders /= Array.length scruts then
    Left "binder/scrutinee arity mismatch"
  else
    Array.foldM step { conds: [], binds: [] } (Array.zip binders scruts)
  where
  step acc (Tuple b scrutT) = case b of
    BLit (LInt k) -> Right acc { conds = Array.snoc acc.conds (TBin Eq scrutT (TInt k)) }
    BLit (LBool v) -> Right acc { conds = Array.snoc acc.conds (TBin Eq scrutT (TBool v)) }
    BLit (LOther tag) -> Left ("unsupported literal binder: " <> tag)
    BVar x -> case sortOf ctx.env scrutT of
      Just _ -> Right acc { binds = Array.snoc acc.binds { name: x, term: scrutT } }
      Nothing -> Left "cannot infer scrutinee sort for var binder"
    BNull -> Right acc
    BOther tag -> Left ("unsupported binder: " <> tag)

conjOf :: Array Term -> Term
conjOf ts = case Array.uncons ts of
  Nothing -> tTrue
  Just { head, tail } -> Array.foldl (TBin And) head tail

checkAlts :: St -> String -> Ctx -> RType -> Array Term -> Array Alt -> M (Array Obligation)
checkAlts st fnName ctx res scruts alts = do
  result <- foldM step { negs: [], obls: [] } alts
  pure result.obls
  where
  step acc alt = do
    row <- lift (binderRow ctx scruts alt.binders)
    let
      bindEnv = Map.fromFoldable
        (Array.mapMaybe (\b -> map (Tuple b.name) (sortOf ctx.env b.term)) row.binds)
      bindEqs = map (\b -> TBin Eq (TVar b.name) b.term) row.binds
      ctxAlt =
        { env: Map.union ctx.env bindEnv
        , assumps: ctx.assumps <> acc.negs <> row.conds <> bindEqs
        }
    obls <- checkResult ctxAlt alt.result
    let
      negs' =
        if Array.null row.conds then acc.negs -- irrefutable row: nothing to negate
        else Array.snoc acc.negs (TNot (conjOf row.conds))
    pure { negs: negs', obls: acc.obls <> obls }

  checkResult ctxAlt = case _ of
    Unconditional e -> checkBody st fnName ctxAlt res e
    Guarded gs -> do
      result <- foldM
        ( \acc g -> do
            r <- scoped (embed st fnName ctxAlt g.guard)
            let ctxG = extend ctxAlt r.vars r.facts
            obls <- checkBody st fnName
              (ctxG { assumps = ctxG.assumps <> acc.notPrev <> [ r.value ] })
              res
              g.expr
            pure
              { notPrev: Array.snoc acc.notPrev (TNot r.value)
              , obls: acc.obls <> r.obls <> obls
              }
        )
        { notPrev: [], obls: [] }
        gs
      pure result.obls

-- | Embed a CoreFn expression as a logic term, recording call facts and
-- | call-precondition obligations in the generator state.
embed :: St -> String -> Ctx -> Expr -> M Term
embed st fnName ctx = go
  where
  go = case _ of
    ELit _ (LInt n) -> pure (TInt n)
    ELit _ (LBool b) -> pure (TBool b)
    ELit sp (LOther tag) -> cannot sp ("literal " <> tag)
    EVar sp q -> embedVar sp q
    e@(EApp _ _ _) -> embedApp e
    e -> cannot (spanOf e) (exprTag e)

  cannot :: forall a. Span -> String -> M a
  cannot sp what = throw
    ("cannot embed " <> what <> loc <> " (outside the supported fragment)")
    where
    loc = if sp.startLine == 0 then "" else " at line " <> show sp.startLine

  embedVar sp q = case q.modName of
    Nothing ->
      if Map.member q.ident ctx.env then pure (TVar q.ident)
      else cannot sp ("unbound variable " <> q.ident)
    Just "Data.Boolean" | q.ident == "otherwise" -> pure (TBool true)
    Just m -> cannot sp ("reference to " <> m <> "." <> q.ident)

  embedApp e = do
    let spine = flatten e []
    case spine.head of
      EVar sp q -> case localPrim q of
        Just prim -> applyPrim sp prim spine.args
        Nothing -> case Array.uncons spine.args of
          Just { head: EVar _ dict, tail }
            | Just prim <- resolveGlobal q dict -> applyPrim sp prim tail
          _ -> case callSpec q of
            Just spec -> emitCall (spanOf e) q spec spine.args
            Nothing -> cannot sp ("call to " <> qualShow q)
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

  -- A spec for this callee: a checked spec for a module-local function
  -- (including the function under verification itself — recursion), or an
  -- `assume` spec matched by unqualified name, through the float map for
  -- floated class methods like `min`.
  callSpec :: Qualified -> Maybe FnSpec
  callSpec q = case q.modName of
    Just m | m == st.modName ->
      case Map.lookup q.ident st.spec.fns of
        Just s -> Just s
        Nothing -> Map.lookup q.ident st.floats >>= \method ->
          Map.lookup method.ident st.spec.assumes
    Just _ -> Map.lookup q.ident st.spec.assumes
    Nothing -> Nothing

  emitCall :: Span -> Qualified -> FnSpec -> Array Expr -> M Term
  emitCall sp q spec args = do
    when (Array.length args /= Array.length spec.args)
      ( cannot sp
          ( "call to " <> qualShow q <> " with " <> show (Array.length args)
              <> " args against a " <> show (Array.length spec.args)
              <> "-arg spec (partial application unsupported)"
          )
      )
    ts <- traverse go args
    let
      pairs = Array.zip spec.args ts
      instantiate p = Array.foldl
        (\acc (Tuple a t) -> if a.binder == "_" then acc else subst a.binder t acc)
        p
        pairs
    -- preconditions: each nontrivial argument refinement becomes an
    -- obligation at the call site, under the context as it stands here
    scope <- get
    let ctxHere = extend ctx scope.vars scope.facts
    for_ pairs \(Tuple a t) -> do
      let goalRaw = instantiate a.pred
      -- the arg's own binder denotes the arg value
      let goal = if a.binder == "_" then goalRaw else subst a.binder t goalRaw
      when (goal /= tTrue)
        (modify_ \s -> s { obls = Array.snoc s.obls (mkObligation fnName sp ctxHere goal) })
    -- result: a fresh variable carrying the instantiated result refinement
    n <- freshName q.ident
    let
      resSort = baseSort spec.result.base
      fact = subst spec.result.binder (TVar n) (instantiate spec.result.pred)
    modify_ \s -> s
      { vars = Array.snoc s.vars (Tuple n resSort)
      , facts = if fact == tTrue then s.facts else Array.snoc s.facts fact
      }
    pure (TVar n)

  freshName base = do
    s <- get
    put s { fresh = s.fresh + 1 }
    pure ("$" <> base <> show s.fresh)

  flatten expr args = case expr of
    EApp _ f a -> flatten f (Array.cons a args)
    head -> { head, args }

qualShow :: Qualified -> String
qualShow q = case q.modName of
  Just m -> m <> "." <> q.ident
  Nothing -> q.ident

exprTag :: Expr -> String
exprTag = case _ of
  EVar _ _ -> "variable"
  ELit _ _ -> "literal"
  EAbs _ _ _ -> "lambda"
  EApp _ _ _ -> "application"
  ECase _ _ _ -> "case"
  ELet _ _ _ -> "let"
  EOther _ tag -> tag
