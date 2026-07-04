-- | The refinement logic: Boolean-sorted terms double as predicates.
-- | Kept inside QF_LIA so Z3 is a decision procedure (ADR-005).
module Lps.Logic
  ( Sort(..)
  , Op(..)
  , Term(..)
  , tTrue
  , conj
  , subst
  , freeVars
  , apps
  , sortOf
  , pretty
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set

data Sort
  = SInt
  | SBool
  -- | An opaque, SMT-declared sort for a user data type (Phase 2:
  -- | constructors are not modelled directly; measures characterize them).
  | SData String

derive instance Eq Sort

instance Show Sort where
  show = case _ of
    SInt -> "Int"
    SBool -> "Boolean"
    SData name -> name

data Op
  = Add
  | Sub
  | Mul
  | Div
  | Mod
  | And
  | Or
  | Eq
  | Neq
  | Lt
  | Le
  | Gt
  | Ge

derive instance Eq Op

data Term
  = TInt Int
  | TBool Boolean
  | TVar String
  | TBin Op Term Term
  | TNeg Term
  | TNot Term
  -- | Application of an uninterpreted function (a measure, or an
  -- | auto-generated is<Ctor> discriminator).
  | TApp String (Array Term)

derive instance Eq Term

tTrue :: Term
tTrue = TBool true

conj :: Array Term -> Term
conj ts = case Array.uncons (Array.filter (_ /= tTrue) ts) of
  Nothing -> tTrue
  Just { head, tail } -> foldl (TBin And) head tail

-- | Capture-free substitution: our terms have no binders.
subst :: String -> Term -> Term -> Term
subst x replacement = go
  where
  go = case _ of
    t@(TInt _) -> t
    t@(TBool _) -> t
    t@(TVar y) -> if y == x then replacement else t
    TBin op l r -> TBin op (go l) (go r)
    TNeg t -> TNeg (go t)
    TNot t -> TNot (go t)
    TApp f args -> TApp f (map go args)

freeVars :: Term -> Set String
freeVars = case _ of
  TInt _ -> Set.empty
  TBool _ -> Set.empty
  TVar x -> Set.singleton x
  TBin _ l r -> freeVars l <> freeVars r
  TNeg t -> freeVars t
  TNot t -> freeVars t
  TApp _ args -> Array.foldMap freeVars args

-- | Every uninterpreted application occurring in a term.
apps :: Term -> Array { fn :: String, args :: Array Term }
apps = case _ of
  TInt _ -> []
  TBool _ -> []
  TVar _ -> []
  TBin _ l r -> apps l <> apps r
  TNeg t -> apps t
  TNot t -> apps t
  TApp fn args -> [ { fn, args } ] <> Array.foldMap apps args

opResultSort :: Op -> Sort
opResultSort = case _ of
  Add -> SInt
  Sub -> SInt
  Mul -> SInt
  Div -> SInt
  Mod -> SInt
  _ -> SBool

-- | `funs` maps uninterpreted function names to their result sorts.
sortOf :: Map String Sort -> Map String Sort -> Term -> Maybe Sort
sortOf funs env = case _ of
  TInt _ -> Just SInt
  TBool _ -> Just SBool
  TVar x -> Map.lookup x env
  TBin op _ _ -> Just (opResultSort op)
  TNeg _ -> Just SInt
  TNot _ -> Just SBool
  TApp f _ -> Map.lookup f funs

prettyOp :: Op -> String
prettyOp = case _ of
  Add -> "+"
  Sub -> "-"
  Mul -> "*"
  Div -> "/"
  Mod -> "%"
  And -> "&&"
  Or -> "||"
  Eq -> "=="
  Neq -> "/="
  Lt -> "<"
  Le -> "<="
  Gt -> ">"
  Ge -> ">="

pretty :: Term -> String
pretty = case _ of
  TInt n -> show n
  TBool b -> show b
  TVar x -> x
  TBin op l r -> "(" <> pretty l <> " " <> prettyOp op <> " " <> pretty r <> ")"
  TNeg t -> "(- " <> pretty t <> ")"
  TNot t -> "(not " <> pretty t <> ")"
  TApp f args -> "(" <> f <> " " <> Array.intercalate " " (map pretty args) <> ")"
