-- | Hand-written decoders from corefn.json (purs 0.15.x shape, probed
-- | 2026-07-04) into the Lps.CoreFn.Types subset.
module Lps.CoreFn.Decode
  ( decodeModule
  ) where

import Prelude

import Data.Argonaut.Core (Json, caseJsonObject, toArray, toBoolean, toNumber, toString)
import Data.Either (Either(..), note)
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.String (joinWith)
import Data.Traversable (traverse)
import Foreign.Object (Object)
import Foreign.Object as Object
import Lps.CoreFn.Types (Alt, AltResult(..), Bind(..), Binder(..), Expr(..), Literal(..), Module, Qualified, Span)

type Dec a = Either String a

asObject :: Json -> Dec (Object Json)
asObject j = caseJsonObject (Left "expected object") Right j

field :: Object Json -> String -> Dec Json
field o k = note ("missing field " <> k) (Object.lookup k o)

asString :: Json -> Dec String
asString = note "expected string" <<< toString

asInt :: Json -> Dec Int
asInt j = do
  n <- note "expected number" (toNumber j)
  note "expected integer" (Int.fromNumber n)

asBool :: Json -> Dec Boolean
asBool = note "expected boolean" <<< toBoolean

asArray :: Json -> Dec (Array Json)
asArray = note "expected array" <<< toArray

strField :: Object Json -> String -> Dec String
strField o k = field o k >>= asString

decodeSpan :: Object Json -> Dec Span
decodeSpan o = do
  ann <- field o "annotation" >>= asObject
  ss <- field ann "sourceSpan" >>= asObject
  start <- field ss "start" >>= asArray >>= traverse asInt
  case start of
    [ line, col ] -> pure { startLine: line, startCol: col }
    _ -> Left "malformed sourceSpan"

decodeQualified :: Json -> Dec Qualified
decodeQualified j = do
  o <- asObject j
  ident <- strField o "identifier"
  modName <- case Object.lookup "moduleName" o of
    Nothing -> pure Nothing
    Just mn -> case toArray mn of
      Nothing -> pure Nothing
      Just parts -> Just <<< joinWith "." <$> traverse asString parts
  pure { modName, ident }

decodeLiteral :: Json -> Dec Literal
decodeLiteral j = do
  o <- asObject j
  litType <- strField o "literalType"
  case litType of
    "IntLiteral" -> LInt <$> (field o "value" >>= asInt)
    "BooleanLiteral" -> LBool <$> (field o "value" >>= asBool)
    other -> pure (LOther other)

decodeBinder :: Json -> Dec Binder
decodeBinder j = do
  o <- asObject j
  binderType <- strField o "binderType"
  case binderType of
    "LiteralBinder" -> BLit <$> (field o "literal" >>= decodeLiteral)
    "VarBinder" -> BVar <$> strField o "identifier"
    "NullBinder" -> pure BNull
    "ConstructorBinder" -> do
      ctor <- field o "constructorName" >>= decodeQualified
      subs <- field o "binders" >>= asArray >>= traverse decodeBinder
      pure (BCtor ctor.ident subs)
    other -> pure (BOther other)

decodeGuarded :: Json -> Dec { guard :: Expr, expr :: Expr }
decodeGuarded j = do
  o <- asObject j
  guard <- field o "guard" >>= decodeExpr
  expr <- field o "expression" >>= decodeExpr
  pure { guard, expr }

decodeAlt :: Json -> Dec Alt
decodeAlt j = do
  o <- asObject j
  binders <- field o "binders" >>= asArray >>= traverse decodeBinder
  isGuarded <- field o "isGuarded" >>= asBool
  result <-
    if isGuarded then
      Guarded <$> (field o "expressions" >>= asArray >>= traverse decodeGuarded)
    else
      Unconditional <$> (field o "expression" >>= decodeExpr)
  pure { binders, result }

decodeExpr :: Json -> Dec Expr
decodeExpr j = do
  o <- asObject j
  span <- decodeSpan o
  exprType <- strField o "type"
  case exprType of
    "Var" -> EVar span <$> (field o "value" >>= decodeQualified)
    "Literal" -> ELit span <$> (field o "value" >>= decodeLiteral)
    "Abs" -> EAbs span <$> strField o "argument" <*> (field o "body" >>= decodeExpr)
    "App" -> EApp span
      <$> (field o "abstraction" >>= decodeExpr)
      <*> (field o "argument" >>= decodeExpr)
    "Case" -> ECase span
      <$> (field o "caseExpressions" >>= asArray >>= traverse decodeExpr)
      <*> (field o "caseAlternatives" >>= asArray >>= traverse decodeAlt)
    "Let" -> ELet span
      <$> (field o "binds" >>= asArray >>= traverse decodeBind)
      <*> (field o "expression" >>= decodeExpr)
    other -> pure (EOther span other)

decodeBind :: Json -> Dec Bind
decodeBind j = do
  o <- asObject j
  bindType <- strField o "bindType"
  case bindType of
    "NonRec" -> NonRec <$> strField o "identifier" <*> (field o "expression" >>= decodeExpr)
    "Rec" -> do
      binds <- field o "binds" >>= asArray
      Rec <$> traverse decodeRecBind binds
    other -> Left ("unknown bindType " <> other)
  where
  decodeRecBind bj = do
    bo <- asObject bj
    name <- strField bo "identifier"
    expr <- field bo "expression" >>= decodeExpr
    pure { name, expr }

decodeModule :: Json -> Dec Module
decodeModule j = do
  o <- asObject j
  nameParts <- field o "moduleName" >>= asArray >>= traverse asString
  path <- strField o "modulePath"
  decls <- field o "decls" >>= asArray >>= traverse decodeBind
  pure { name: joinWith "." nameParts, path, decls }
