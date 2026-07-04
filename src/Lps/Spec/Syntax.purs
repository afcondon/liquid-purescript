-- | The surface refinement language, after alias expansion.
module Lps.Spec.Syntax
  ( Base(..)
  , RType
  , FnSpec
  , CtorDef
  , DataDef
  , MeasureEqn
  , MeasureDef
  , SpecFile
  , baseSort
  , trivial
  ) where

import Prelude

import Data.Map (Map)
import Lps.Logic (Sort(..), Term, tTrue)

data Base
  = BInt
  | BBool
  -- | A user data type declared with a `data` line in the spec file.
  -- | Opaque at the SMT level; characterized by measures (Phase 2).
  | BData String

derive instance Eq Base

baseSort :: Base -> Sort
baseSort = case _ of
  BInt -> SInt
  BBool -> SBool
  BData name -> SData name

-- | `{ binder : base | pred }`; a bare base type is `{ _ : base | true }`.
type RType = { binder :: String, base :: Base, pred :: Term }

trivial :: Base -> RType
trivial b = { binder: "_", base: b, pred: tTrue }

-- | Earlier argument binders scope over later preds and the result pred.
type FnSpec = { args :: Array RType, result :: RType }

type CtorDef = { name :: String, fields :: Array Base }

type DataDef = { name :: String, ctors :: Array CtorDef }

-- | One measure equation: `Cons x xs = 1 + len xs`.
type MeasureEqn = { params :: Array String, rhs :: Term }

-- | A logic-level function over one data sort, defined by one equation per
-- | constructor, with a result refinement instantiated at every
-- | application site (e.g. `len xs >= 0`).
type MeasureDef =
  { name :: String
  , dataName :: String
  , result :: RType
  , eqns :: Map String MeasureEqn
  }

-- | `fns` are checked; `assumes` are trusted specs for imported/FFI
-- | functions (the LH `assume` move), keyed by unqualified identifier.
type SpecFile =
  { fns :: Map String FnSpec
  , assumes :: Map String FnSpec
  , datas :: Map String DataDef
  , measures :: Map String MeasureDef
  }
