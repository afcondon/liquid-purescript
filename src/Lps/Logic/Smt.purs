-- | Render one obligation as an SMT-LIB2 script. The transport is text so
-- | every obligation is an inspectable, replayable artifact (ADR-004).
module Lps.Logic.Smt
  ( Query
  , render
  ) where

import Prelude

import Data.Array as Array
import Data.Tuple (Tuple(..))
import Lps.Logic (Op(..), Sort(..), Term(..))

type Query =
  { decls :: Array (Tuple String Sort)
  , assumps :: Array Term
  , goal :: Term
  }

smtSort :: Sort -> String
smtSort = case _ of
  SInt -> "Int"
  SBool -> "Bool"

smtOp :: Op -> String
smtOp = case _ of
  Add -> "+"
  Sub -> "-"
  Mul -> "*"
  Div -> "div"
  Mod -> "mod"
  And -> "and"
  Or -> "or"
  Eq -> "="
  Neq -> "distinct"
  Lt -> "<"
  Le -> "<="
  Gt -> ">"
  Ge -> ">="

smtTerm :: Term -> String
smtTerm = case _ of
  TInt n
    | n < 0 -> "(- " <> show (negate n) <> ")"
    | otherwise -> show n
  TBool b -> show b
  TVar x -> x
  TBin op l r -> "(" <> smtOp op <> " " <> smtTerm l <> " " <> smtTerm r <> ")"
  TNeg t -> "(- " <> smtTerm t <> ")"
  TNot t -> "(not " <> smtTerm t <> ")"

-- | Validity of (assumps => goal) via unsatisfiability of (assumps && not goal).
-- | We always ask for a model; when the result is unsat, z3 answers the
-- | get-model with an error s-expression, which the driver ignores.
render :: Query -> String
render q = Array.intercalate "\n" $
  map declLine q.decls
    <> map (\t -> "(assert " <> smtTerm t <> ")") q.assumps
    <> [ "(assert (not " <> smtTerm q.goal <> "))"
       , "(check-sat)"
       , "(get-model)"
       ]
  where
  declLine (Tuple name sort) =
    "(declare-const " <> name <> " " <> smtSort sort <> ")"
