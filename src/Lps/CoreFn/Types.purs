-- | The subset of CoreFn the verifier consumes. Anything outside the
-- | fragment decodes to `EOther`/`BOther`/`LOther` with its tag preserved,
-- | so unsupported constructs fail with an honest message, never silently.
module Lps.CoreFn.Types where

import Data.Maybe (Maybe)

type Span = { startLine :: Int, startCol :: Int }

type Qualified = { modName :: Maybe String, ident :: String }

data Literal
  = LInt Int
  | LBool Boolean
  | LOther String

data Binder
  = BLit Literal
  | BVar String
  | BNull
  | BOther String

data AltResult
  = Unconditional Expr
  | Guarded (Array { guard :: Expr, expr :: Expr })

type Alt = { binders :: Array Binder, result :: AltResult }

data Expr
  = EVar Span Qualified
  | ELit Span Literal
  | EAbs Span String Expr
  | EApp Span Expr Expr
  | ECase Span (Array Expr) (Array Alt)
  | ELet Span (Array Bind) Expr
  | EOther Span String

data Bind
  = NonRec String Expr
  | Rec (Array { name :: String, expr :: Expr })

type Module =
  { name :: String
  , path :: String
  , decls :: Array Bind
  }

spanOf :: Expr -> Span
spanOf = case _ of
  EVar s _ -> s
  ELit s _ -> s
  EAbs s _ _ -> s
  EApp s _ _ -> s
  ECase s _ _ -> s
  ELet s _ _ -> s
  EOther s _ -> s
