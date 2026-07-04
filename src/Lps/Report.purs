-- | Verdict rendering: one line per function, spans and countermodels on
-- | failure. A function is SAFE only if every obligation is valid.
module Lps.Report
  ( FnVerdict(..)
  , renderFn
  , anyUnsafe
  ) where

import Prelude

import Data.Array as Array
import Data.String (joinWith)
import Lps.CoreFn.Types (Span)
import Lps.Logic (Term, pretty)

data FnVerdict
  = Safe String
  | Unsafe String { path :: String, span :: Span, goal :: Term, model :: String }
  | Errored String String
  | Solverless String String

renderFn :: FnVerdict -> String
renderFn = case _ of
  Safe name ->
    name <> "  ✓ SAFE"
  Unsafe name f ->
    joinWith "\n"
      [ name <> "  ✗ UNSAFE"
      , "    at " <> f.path <> ":" <> show f.span.startLine <> ":" <> show f.span.startCol
      , "    cannot prove: " <> pretty f.goal
      , "    counterexample: " <> f.model
      ]
  Errored name msg ->
    name <> "  ? UNSUPPORTED — " <> msg
  Solverless name msg ->
    name <> "  ? UNKNOWN — solver said: " <> msg

anyUnsafe :: Array FnVerdict -> Boolean
anyUnsafe = Array.any case _ of
  Safe _ -> false
  _ -> true
