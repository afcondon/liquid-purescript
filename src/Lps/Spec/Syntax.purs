-- | The surface refinement language, after alias expansion.
module Lps.Spec.Syntax
  ( Base(..)
  , RType
  , FnSpec
  , SpecFile
  , baseSort
  , trivial
  ) where

import Data.Map (Map)
import Lps.Logic (Sort(..), Term, tTrue)

data Base = BInt | BBool

baseSort :: Base -> Sort
baseSort = case _ of
  BInt -> SInt
  BBool -> SBool

-- | `{ binder : base | pred }`; a bare base type is `{ _ : base | true }`.
type RType = { binder :: String, base :: Base, pred :: Term }

trivial :: Base -> RType
trivial b = { binder: "_", base: b, pred: tTrue }

-- | Earlier argument binders scope over later preds and the result pred.
type FnSpec = { args :: Array RType, result :: RType }

type SpecFile = { fns :: Map String FnSpec }
