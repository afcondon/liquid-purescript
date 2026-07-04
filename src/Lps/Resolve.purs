-- | Primitive-operation resolution.
-- |
-- | purs floats type-class methods into synthetic module-local decls:
-- | `n > 0` compiles to `App (App (Var Demo.greaterThan) n) 0` with a decl
-- | `Demo.greaterThan = Data.Ord.greaterThan ordInt` elsewhere in the module
-- | (probed on purs 0.15.15). This pass scans the module for decls of that
-- | shape and builds a table mapping local names to SMT primitives; the
-- | embedder also uses `resolveGlobal` for non-floated fully-applied uses.
module Lps.Resolve
  ( Prim(..)
  , PrimTable
  , FloatMap
  , buildTable
  , buildFloats
  , resolveGlobal
  ) where

import Prelude

import Data.Array (find, mapMaybe)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Lps.CoreFn.Types (Bind(..), Expr(..), Module, Qualified)
import Lps.Logic (Op(..))

data Prim
  = Prim2 Op
  | PrimNeg
  | PrimNot

-- | Local identifier (in the module under verification) -> primitive.
type PrimTable = Map String Prim

-- | (method module, method name, dictionary name) -> primitive.
-- | The dictionary pins the instance: `sub ringInt` is integer subtraction;
-- | `sub` at some other instance is not our business.
known :: Array (Tuple { m :: String, f :: String, dict :: String } Prim)
known =
  [ entry "Data.Ord" "greaterThan" "ordInt" (Prim2 Gt)
  , entry "Data.Ord" "lessThan" "ordInt" (Prim2 Lt)
  , entry "Data.Ord" "greaterThanOrEq" "ordInt" (Prim2 Ge)
  , entry "Data.Ord" "lessThanOrEq" "ordInt" (Prim2 Le)
  , entry "Data.Semiring" "add" "semiringInt" (Prim2 Add)
  , entry "Data.Semiring" "mul" "semiringInt" (Prim2 Mul)
  , entry "Data.Ring" "sub" "ringInt" (Prim2 Sub)
  , entry "Data.Ring" "negate" "ringInt" PrimNeg
  , entry "Data.EuclideanRing" "div" "euclideanRingInt" (Prim2 Div)
  , entry "Data.EuclideanRing" "mod" "euclideanRingInt" (Prim2 Mod)
  , entry "Data.Eq" "eq" "eqInt" (Prim2 Eq)
  , entry "Data.Eq" "notEq" "eqInt" (Prim2 Neq)
  , entry "Data.Eq" "eq" "eqBoolean" (Prim2 Eq)
  , entry "Data.Eq" "notEq" "eqBoolean" (Prim2 Neq)
  , entry "Data.HeytingAlgebra" "conj" "heytingAlgebraBoolean" (Prim2 And)
  , entry "Data.HeytingAlgebra" "disj" "heytingAlgebraBoolean" (Prim2 Or)
  , entry "Data.HeytingAlgebra" "not" "heytingAlgebraBoolean" PrimNot
  ]
  where
  entry m f dict prim = Tuple { m, f, dict } prim

-- | Resolve a class method applied to a dictionary, e.g.
-- | `Data.Ord.greaterThan` + `ordInt`.
resolveGlobal :: Qualified -> Qualified -> Maybe Prim
resolveGlobal method dict = case method.modName of
  Nothing -> Nothing
  Just m ->
    let
      match (Tuple k _) = k.m == m && k.f == method.ident && k.dict == dict.ident
    in
      map (\(Tuple _ p) -> p) (find match known)

-- | Scan the module for floated decls `local = <method> <dict>`.
buildTable :: Module -> PrimTable
buildTable mod = Map.fromFoldable (mapMaybe floated mod.decls)
  where
  floated = case _ of
    NonRec name (EApp _ (EVar _ method) (EVar _ dict)) ->
      map (Tuple name) (resolveGlobal method dict)
    _ -> Nothing

-- | Every floated alias, primitive or not: local name -> underlying method.
-- | Used to match `assume` specs against class methods like `min`
-- | (floated as `Demo.min = Data.Ord.min ordInt`).
type FloatMap = Map String Qualified

buildFloats :: Module -> FloatMap
buildFloats mod = Map.fromFoldable (mapMaybe floated mod.decls)
  where
  floated = case _ of
    NonRec name (EApp _ (EVar _ method) (EVar _ _)) -> Just (Tuple name method)
    _ -> Nothing
