-- | The solver boundary: SMT-LIB2 text in, verdict out, via `z3 -in`
-- | (ADR-004 — swappable for z3 WASM later without touching the pipeline).
module Lps.Solver.Z3
  ( Verdict(..)
  , solve
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), Replacement(..), replaceAll, split, trim)
import Data.String as String
import Data.String.CodeUnits (fromCharArray, toCharArray)
import Effect (Effect)

foreign import runZ3Impl :: String -> Effect String

data Verdict
  = Valid
  -- | Refuted, with the raw countermodel text from z3.
  | Refuted String
  | Unknown String

-- | The script asserts the negation of the goal, so:
-- | unsat = the implication is valid; sat = refuted (model follows).
solve :: String -> Effect Verdict
solve script = do
  out <- runZ3Impl script
  let outLines = Array.filter (not <<< String.null) (map trim (split (Pattern "\n") out))
  pure case Array.uncons outLines of
    Just { head: "unsat" } -> Valid
    Just { head: "sat", tail } -> Refuted (prettyModel (String.joinWith "\n" tail))
    _ -> Unknown out

-- | Collapse z3's model s-expression to `n = 0, m = (- 1)` form.
prettyModel :: String -> String
prettyModel raw =
  case Array.mapMaybe defn chunks of
    [] -> trim raw
    ds -> String.joinWith ", " ds
  where
  flat = replaceAll (Pattern "\n") (Replacement " ") raw
  chunks = Array.drop 1 (split (Pattern "(define-fun ") flat)

  -- chunk looks like: "n () Int 0) )" or "m () Int (- 1)) )"
  defn chunk =
    let
      ws = Array.filter (_ /= "") (split (Pattern " ") chunk)
    in
      case Array.uncons ws of
        Just { head: name, tail } ->
          let
            value = takeBalanced (String.joinWith " " (Array.drop 2 tail))
          in
            if value == "" then Nothing else Just (name <> " = " <> value)
        Nothing -> Nothing

  -- Take characters until the paren depth of the enclosing define-fun closes.
  takeBalanced s = trim (fromCharArray (go 0 (toCharArray s)))
    where
    go depth cs = case Array.uncons cs of
      Nothing -> []
      Just { head: c, tail }
        | c == '(' -> Array.cons c (go (depth + 1) tail)
        | c == ')' -> if depth == 0 then [] else Array.cons c (go (depth - 1) tail)
        | otherwise -> Array.cons c (go depth tail)
