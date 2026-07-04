-- | Verification-condition generation: checking-mode traversal of each
-- | spec'd declaration (see docs/PLAN.md, "Semantics"). Sound but
-- | deliberately imprecise: anything outside the embeddable fragment is a
-- | per-function error, never a silent pass (ADR-006).
-- |
-- | Phase 1: calls to spec'd functions emit precondition obligations at the
-- | call site and bind a fresh result variable carrying the instantiated
-- | result refinement; recursive calls assume the function's own spec.
-- | `assume` specs do the same for imported/FFI functions, on trust. Call
-- | facts are scoped to the path that made the call.
-- |
-- | Phase 2: user data types are opaque SMT sorts characterized by
-- | measures. A constructor binder contributes an is<Ctor> discriminator
-- | plus each measure's equation for that constructor as path facts; a
-- | constructor application binds a fresh value with the same facts.
-- | Measure result refinements (e.g. `len xs >= 0`) are instantiated at
-- | every application occurring in an obligation — the standard move that
-- | keeps the logic quantifier-free.
module Lps.Vc
  ( Obligation
  , FnResult
  , checkModule
  , discName
  ) where

import Prelude

import Control.Monad.State.Trans (StateT, evalStateT, get, modify_, put)
import Control.Monad.Trans.Class (lift)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Traversable (for, for_, traverse)
import Data.Tuple (Tuple(..))
import Lps.CoreFn.Types (Alt, AltResult(..), Bind(..), Binder(..), Expr(..), Literal(..), Module, Qualified, Span, spanOf)
import Lps.Logic (Op(..), Sort(..), Term(..), apps, subst, sortOf, tTrue)
import Lps.Resolve (FloatMap, Prim(..), PrimTable, buildFloats, buildTable, resolveGlobal)
import Lps.Spec.Syntax (Base, DataDef, FnSpec, MeasureDef, RType, SpecFile, baseSort)

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

type CtorInfo = { dataName :: String, fields :: Array Base, siblings :: Array String }

type St =
  { table :: PrimTable
  , floats :: FloatMap
  , modName :: String
  , spec :: SpecFile
  , ctors :: Map String CtorInfo
  , measuresByData :: Map String (Array MeasureDef)
  , funSorts :: Map String Sort
  }

mkSt :: Module -> SpecFile -> St
mkSt mod spec =
  { table: buildTable mod
  , floats: buildFloats mod
  , modName: mod.name
  , spec
  , ctors
  , measuresByData
  , funSorts
  }
  where
  ctors = Map.fromFoldable do
    Tuple dataName d <- Map.toUnfoldable spec.datas :: Array (Tuple String DataDef)
    c <- d.ctors
    pure $ Tuple c.name
      { dataName
      , fields: c.fields
      , siblings: Array.filter (_ /= c.name) (map _.name d.ctors)
      }

  measuresByData = Array.foldl
    (\acc (Tuple _ m) -> Map.insertWith (<>) m.dataName [ m ] acc)
    Map.empty
    (Map.toUnfoldable spec.measures :: Array (Tuple String MeasureDef))

  funSorts = Map.fromFoldable $
    map (\(Tuple name m) -> Tuple name (baseSort m.result.base))
      (Map.toUnfoldable spec.measures :: Array (Tuple String MeasureDef))
      <> map (\(Tuple name _) -> Tuple (discName name) SBool)
        (Map.toUnfoldable ctors :: Array (Tuple String CtorInfo))

discName :: String -> String
discName ctor = "is" <> ctor

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

freshName :: String -> M String
freshName base = do
  s <- get
  put s { fresh = s.fresh + 1 }
  pure ("$" <> base <> show s.fresh)

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
  st = mkSt mod spec

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
    let
      ctx0' = extend ctx r.vars r.facts
      -- scrutinizing a measured data value: some declared constructor holds
      exhaustive = Array.mapMaybe (exhaustFact st ctx0'.env) r.value
      ctx0 = ctx0' { assumps = ctx0'.assumps <> exhaustive }
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
    pure (r.obls <> [ mkObligation st fnName (spanOf e) ctx' goal ])

exhaustFact :: St -> Env -> Term -> Maybe Term
exhaustFact st env t = case sortOf st.funSorts env t of
  Just (SData d) -> do
    dataDef <- Map.lookup d st.spec.datas
    { head, tail } <- Array.uncons (map (\c -> TApp (discName c.name) [ t ]) dataDef.ctors)
    pure (Array.foldl (TBin Or) head tail)
  _ -> Nothing

-- | Instantiate measure result refinements for every measure application
-- | occurring in the obligation (assumptions and goal alike).
mkObligation :: St -> String -> Span -> Ctx -> Term -> Obligation
mkObligation st fnName span ctx goal =
  { fnName
  , span
  , decls: Map.toUnfoldable ctx.env
  , assumps: ctx.assumps <> instanceFacts
  , goal
  }
  where
  instanceFacts = Array.nubEq do
    a <- Array.concatMap apps (Array.snoc ctx.assumps goal)
    case Map.lookup a.fn st.spec.measures of
      Just m | m.result.pred /= tTrue ->
        [ subst m.result.binder (TApp a.fn a.args) m.result.pred ]
      _ -> []

bindLet :: St -> String -> Ctx -> Bind -> M Ctx
bindLet st fnName ctx = case _ of
  NonRec x e -> do
    t <- embed st fnName ctx e
    scope <- get
    let envNow = Map.union ctx.env (Map.fromFoldable scope.vars)
    sort <- case sortOf st.funSorts envNow t of
      Just s -> pure s
      Nothing -> throw ("cannot infer sort of let-bound " <> x)
    pure
      { env: Map.insert x sort ctx.env
      , assumps: Array.snoc ctx.assumps (TBin Eq (TVar x) t)
      }
  Rec _ -> throw "recursive let is unsupported"

-- | One alternative's binder row against the scrutinee terms.
type BinderRow =
  { conds :: Array Term -- refutable conditions (negated for later alts)
  , facts :: Array Term -- assumed but never negated (measure equations)
  , binds :: Array { name :: String, term :: Term } -- var binders
  , newVars :: Array (Tuple String Sort) -- constructor field binders
  }

emptyRow :: BinderRow
emptyRow = { conds: [], facts: [], binds: [], newVars: [] }

binderRow :: St -> Ctx -> Array Term -> Array Binder -> M BinderRow
binderRow st ctx scruts binders =
  if Array.length binders /= Array.length scruts then
    throw "binder/scrutinee arity mismatch"
  else
    foldM step emptyRow (Array.zip binders scruts)
  where
  step acc (Tuple b scrutT) = case b of
    BLit (LInt k) -> pure acc { conds = Array.snoc acc.conds (TBin Eq scrutT (TInt k)) }
    BLit (LBool v) -> pure acc { conds = Array.snoc acc.conds (TBin Eq scrutT (TBool v)) }
    BLit (LArray _) -> throw "array patterns are unsupported (match on length instead)"
    BLit (LOther tag) -> throw ("unsupported literal binder: " <> tag)
    BVar x -> case sortOf st.funSorts ctx.env scrutT of
      Just _ -> pure acc { binds = Array.snoc acc.binds { name: x, term: scrutT } }
      Nothing -> throw "cannot infer scrutinee sort for var binder"
    BNull -> pure acc
    BCtor ctorName subs -> do
      info <- case Map.lookup ctorName st.ctors of
        Just i -> pure i
        Nothing -> throw
          ( "constructor " <> ctorName
              <> " is not declared in the spec file (add a data declaration)"
          )
      when (Array.length subs /= Array.length info.fields)
        (throw ("constructor " <> ctorName <> " arity mismatch"))
      -- each field gets a variable: the binder's own name, or fresh
      fieldVars <- for (Array.zip subs info.fields) \(Tuple sub base) ->
        case sub of
          BVar x -> pure (Tuple x (baseSort base))
          BNull -> do
            n <- freshName "f"
            pure (Tuple n (baseSort base))
          _ -> throw ("nested pattern in " <> ctorName <> " is unsupported (bind a variable and match again)")
      let
        fieldTerms = map (\(Tuple n _) -> TVar n) fieldVars
        measureFacts = ctorFacts st info.dataName ctorName scrutT fieldTerms
      pure acc
        { conds = Array.snoc acc.conds (TApp (discName ctorName) [ scrutT ])
        , facts = acc.facts <> measureFacts
        , newVars = acc.newVars <> fieldVars
        }
    BOther tag -> throw ("unsupported binder: " <> tag)

-- | The facts a constructor contributes about a value: its discriminator,
-- | its siblings' negated discriminators, and each measure's equation.
ctorFacts :: St -> String -> String -> Term -> Array Term -> Array Term
ctorFacts st dataName ctorName value fieldTerms =
  siblingFacts <> measureFacts
  where
  info = Map.lookup ctorName st.ctors
  siblingFacts = case info of
    Just i -> map (\s -> TNot (TApp (discName s) [ value ])) i.siblings
    Nothing -> []
  measureFacts = do
    m <- fromMaybe [] (Map.lookup dataName st.measuresByData)
    case Map.lookup ctorName m.eqns of
      Just eqn ->
        let
          rhs = Array.foldl
            (\acc (Tuple p t) -> subst p t acc)
            eqn.rhs
            (Array.zip eqn.params fieldTerms)
        in
          [ TBin Eq (TApp m.name [ value ]) rhs ]
      Nothing -> []

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
    row <- binderRow st ctx scruts alt.binders
    let
      bindEnv = Map.fromFoldable
        ( Array.mapMaybe
            (\b -> map (Tuple b.name) (sortOf st.funSorts ctx.env b.term))
            row.binds
        )
      bindEqs = map (\b -> TBin Eq (TVar b.name) b.term) row.binds
      ctxAlt =
        { env: Map.union ctx.env (Map.union bindEnv (Map.fromFoldable row.newVars))
        , assumps: ctx.assumps <> acc.negs <> row.conds <> row.facts <> bindEqs
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
    ELit _ (LArray elems) -> do
      -- element values are erased (only length is visible to the logic),
      -- but embedding each element still fires any call obligations inside
      _ <- traverse go elems
      n <- freshName "arr"
      modify_ \s -> s
        { vars = Array.snoc s.vars (Tuple n (SData "Array"))
        , facts = Array.snoc s.facts
            (TBin Eq (TApp "length" [ TVar n ]) (TInt (Array.length elems)))
        }
      pure (TVar n)
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
    Just _ -> case Map.lookup q.ident st.ctors of
      Just info | Array.null info.fields -> mkCtorTerm q.ident info []
      _ -> cannot sp ("reference to " <> qualShow q)

  embedApp e = do
    let spine = flatten e []
    case spine.head of
      EVar sp q -> case localPrim q of
        Just prim -> applyPrim sp prim spine.args
        Nothing -> case Array.uncons spine.args of
          Just { head: EVar _ dict, tail }
            | Just prim <- resolveGlobal q dict -> applyPrim sp prim tail
          _ -> case Map.lookup q.ident st.ctors of
            Just info -> do
              when (Array.length spine.args /= Array.length info.fields)
                (cannot sp ("partial application of constructor " <> q.ident))
              ts <- traverse go spine.args
              mkCtorTerm q.ident info ts
            Nothing -> case callSpec q of
              Just spec -> emitCall (spanOf e) q spec spine.args
              Nothing -> cannot sp ("call to " <> qualShow q)
      other -> cannot (spanOf other) "higher-order application"

  -- a constructor application: a fresh value plus everything the
  -- constructor implies about it
  mkCtorTerm ctorName info argTerms = do
    n <- freshName ctorName
    let
      value = TVar n
      facts =
        [ TApp (discName ctorName) [ value ] ]
          <> ctorFacts st info.dataName ctorName value argTerms
    modify_ \s -> s
      { vars = Array.snoc s.vars (Tuple n (SData info.dataName))
      , facts = s.facts <> facts
      }
    pure value

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
    scope <- get
    let ctxHere = extend ctx scope.vars scope.facts
    for_ pairs \(Tuple a t) -> do
      let goalRaw = instantiate a.pred
      let goal = if a.binder == "_" then goalRaw else subst a.binder t goalRaw
      when (goal /= tTrue)
        (modify_ \s -> s { obls = Array.snoc s.obls (mkObligation st fnName sp ctxHere goal) })
    n <- freshName q.ident
    let
      resSort = baseSort spec.result.base
      fact = subst spec.result.binder (TVar n) (instantiate spec.result.pred)
    modify_ \s -> s
      { vars = Array.snoc s.vars (Tuple n resSort)
      , facts = if fact == tTrue then s.facts else Array.snoc s.facts fact
      }
    pure (TVar n)

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
