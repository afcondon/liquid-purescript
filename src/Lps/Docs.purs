-- | Signature cross-check against `docs.json` (externs are CBOR in purs
-- | 0.15.x; docs.json is the JSON source of truth for type signatures).
-- | Catches spec/code drift: a spec whose arity or base types disagree
-- | with the function's actual PureScript type fails before any solving.
module Lps.Docs
  ( SigMap
  , readSigs
  , crossCheck
  ) where

import Prelude

import Data.Argonaut.Core (Json, caseJsonObject, toArray, toString)
import Data.Array as Array
import Data.Either (Either(..), hush, note)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (joinWith)
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Foreign.Object (Object)
import Foreign.Object as Object
import Lps.Spec.Syntax (Base(..), FnSpec)

-- | Function name -> argument bases + result base, for every value
-- | declaration whose type lies in the first-order Int/Boolean fragment.
-- | Functions with types outside the fragment map to Nothing (known to
-- | exist, not checkable).
type SigMap = Map String (Maybe (Array Base))

asObject :: Json -> Either String (Object Json)
asObject = caseJsonObject (Left "expected object") Right

field :: Object Json -> String -> Either String Json
field o k = note ("missing field " <> k) (Object.lookup k o)

readSigs :: Json -> Either String SigMap
readSigs j = do
  o <- asObject j
  decls <- field o "declarations" >>= (note "expected array" <<< toArray)
  pure (Map.fromFoldable (Array.mapMaybe sig decls))
  where
  sig dj = hush do
    o <- asObject dj
    title <- field o "title" >>= (note "string" <<< toString)
    info <- field o "info" >>= asObject
    declType <- field info "declType" >>= (note "string" <<< toString)
    if declType == "value" then do
      ty <- field info "type"
      pure (Tuple title (flatten ty))
    else Left "not a value"

-- | Flatten `a -> b -> c` into [a, b, c]; Nothing if any component is not
-- | Prim.Int / Prim.Boolean (polymorphism, records, other constructors).
flatten :: Json -> Maybe (Array Base)
flatten ty = case fnParts ty of
  Just { arg, rest } -> do
    b <- baseOf arg
    bs <- flatten rest
    pure (Array.cons b bs)
  Nothing -> map pure (baseOf ty)
  where
  fnParts t = do
    o <- hush (asObject t)
    tag <- Object.lookup "tag" o >>= toString
    guardJust (tag == "TypeApp")
    parts <- Object.lookup "contents" o >>= toArray
    case parts of
      [ f, rest ] -> do
        fo <- hush (asObject f)
        ftag <- Object.lookup "tag" fo >>= toString
        guardJust (ftag == "TypeApp")
        fparts <- Object.lookup "contents" fo >>= toArray
        case fparts of
          [ fnCon, arg ] -> do
            guardJust (constructorName fnCon == Just "Prim.Function")
            pure { arg, rest }
          _ -> Nothing
      _ -> Nothing

  baseOf t = case constructorName t of
    Just "Prim.Int" -> Just BInt
    Just "Prim.Boolean" -> Just BBool
    -- any other non-parametric constructor: compare by unqualified name
    -- against a spec-declared data type
    Just qualified -> Just (BData (lastSegment qualified))
    _ -> Nothing

  lastSegment s = fromMaybe s (Array.last (String.split (String.Pattern ".") s))

  constructorName t = do
    o <- hush (asObject t)
    tag <- Object.lookup "tag" o >>= toString
    guardJust (tag == "TypeConstructor")
    parts <- Object.lookup "contents" o >>= toArray
    case parts of
      [ modParts, name ] -> do
        ms <- toArray modParts
        mods <- traverse toString ms
        n <- toString name
        pure (joinWith "." mods <> "." <> n)
      _ -> Nothing

  guardJust b = if b then Just unit else Nothing

-- | Nothing = spec agrees with (or cannot be checked against) the type.
-- | A type outside the flattenable fragment — polymorphic, constrained,
-- | parameterized — is passed through silently: a spec may legitimately
-- | pin a monomorphic instance of a polymorphic function (trivial
-- | lifting), and the checker itself fails honestly on anything it cannot
-- | embed, so no silent blessing is possible here.
crossCheck :: SigMap -> String -> FnSpec -> Maybe String
crossCheck sigs name spec = case Map.lookup name sigs of
  Nothing -> Nothing -- not in docs.json (or not a value decl); nothing to say
  Just Nothing -> Nothing -- type not flattenable; the checker is the backstop
  Just (Just bases) ->
    let
      specBases = map _.base spec.args <> [ spec.result.base ]
    in
      if Array.length bases /= Array.length specBases then
        Just
          ( "spec has " <> show (Array.length specBases - 1)
              <> " argument(s) but the declared type has "
              <> show (Array.length bases - 1)
          )
      else if bases /= specBases then
        Just "spec base types disagree with the declared type"
      else Nothing
