-- | Parser for `.lps` spec files (ADR-003: specs live beside sources, the
-- | .purs file is untouched). Rejects non-linear arithmetic at parse time
-- | so every obligation stays decidable (ADR-005).
module Lps.Spec.Parser
  ( parseSpecFile
  ) where

import Prelude

import Control.Alt ((<|>))
import Control.Lazy (fix)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM, traverse_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.String.CodeUnits (fromCharArray)
import Data.Traversable (traverse)
import Lps.Logic (Op(..), Term(..))
import Lps.Spec.Syntax (Base(..), RType, SpecFile, trivial)
import Parsing (Parser, runParser, parseErrorMessage, fail)
import Parsing.Combinators (many, notFollowedBy, option, sepBy1, try)
import Parsing.Expr (Assoc(..), Operator(..), buildExprParser)
import Parsing.String (char, eof, string)
import Parsing.String.Basic (alphaNum, intDecimal, lower, skipSpaces, upper)

-- Surface declarations before alias resolution
data RTypeRaw
  = RRef String
  | RConcrete RType

data Decl
  = DAlias String RTypeRaw
  | DFn String (Array RTypeRaw)
  | DAssume String (Array RTypeRaw)

type P a = Parser String a

lexeme :: forall a. P a -> P a
lexeme p = p <* skipSpaces

symbol :: String -> P String
symbol s = lexeme (try (string s))

keyword :: String -> P String
keyword s = lexeme (try (string s <* notFollowedBy alphaNum))

identChar :: P Char
identChar = alphaNum <|> char '_' <|> char '\''

varId :: P String
varId = lexeme do
  c <- lower <|> char '_'
  cs <- many identChar
  pure (fromCharArray ([ c ] <> Array.fromFoldable cs))

conId :: P String
conId = lexeme do
  c <- upper
  cs <- many identChar
  pure (fromCharArray ([ c ] <> Array.fromFoldable cs))

term :: P Term
term = fix \p ->
  let
    atom =
      (TInt <$> lexeme intDecimal)
        <|> (keyword "true" $> TBool true)
        <|> (keyword "false" $> TBool false)
        <|> (TVar <$> varId)
        <|> (symbol "(" *> p <* symbol ")")

    infixOp s op assoc = Infix (symbol s $> TBin op) assoc

    table =
      [ [ Prefix (keyword "not" $> TNot) ]
      , [ infixOp "*" Mul AssocLeft ]
      , [ infixOp "+" Add AssocLeft, infixOp "-" Sub AssocLeft ]
      , [ infixOp "==" Eq AssocNone
        , infixOp "/=" Neq AssocNone
        , infixOp "<=" Le AssocNone
        , infixOp ">=" Ge AssocNone
        , infixOp "<" Lt AssocNone
        , infixOp ">" Gt AssocNone
        ]
      , [ infixOp "&&" And AssocRight ]
      , [ infixOp "||" Or AssocRight ]
      ]
  in
    buildExprParser table atom

base :: String -> Maybe Base
base = case _ of
  "Int" -> Just BInt
  "Boolean" -> Just BBool
  _ -> Nothing

rtypeRaw :: P RTypeRaw
rtypeRaw = refined <|> named
  where
  named = do
    name <- conId
    pure case base name of
      Just b -> RConcrete (trivial b)
      Nothing -> RRef name

  refined = do
    _ <- symbol "{"
    binder <- varId
    _ <- symbol ":"
    name <- conId
    b <- case base name of
      Just b -> pure b
      Nothing -> fail ("refined base must be Int or Boolean, got " <> name)
    pred <- option (TBool true) (symbol "|" *> term)
    _ <- symbol "}"
    pure (RConcrete { binder, base: b, pred })

decl :: P Decl
decl = alias <|> assumeSpec <|> fnSpec
  where
  alias = do
    _ <- keyword "type"
    name <- conId
    _ <- symbol "="
    DAlias name <$> rtypeRaw

  assumeSpec = do
    _ <- keyword "assume"
    name <- varId
    _ <- symbol "::"
    tys <- sepBy1 rtypeRaw (symbol "->")
    pure (DAssume name (Array.fromFoldable tys))

  fnSpec = do
    name <- varId
    _ <- symbol "::"
    tys <- sepBy1 rtypeRaw (symbol "->")
    pure (DFn name (Array.fromFoldable tys))

specFile :: P (Array Decl)
specFile = skipSpaces *> (Array.fromFoldable <$> many decl) <* eof

-- | Line comments (`-- ...`) are stripped before parsing.
stripComments :: String -> String
stripComments input =
  String.joinWith "\n" (map stripLine (String.split (String.Pattern "\n") input))
  where
  stripLine line = case String.indexOf (String.Pattern "--") line of
    Just i -> String.take i line
    Nothing -> line

-- | Only linear arithmetic: at least one side of every `*` is a literal.
checkLinear :: Term -> Either String Unit
checkLinear = case _ of
  TInt _ -> pure unit
  TBool _ -> pure unit
  TVar _ -> pure unit
  TBin Mul l r -> do
    case l, r of
      TInt _, _ -> pure unit
      _, TInt _ -> pure unit
      _, _ -> Left "non-linear multiplication in refinement (both operands are non-literals)"
    checkLinear l *> checkLinear r
  TBin _ l r -> checkLinear l *> checkLinear r
  TNeg t -> checkLinear t
  TNot t -> checkLinear t

type Acc =
  { aliases :: Map String RType
  , fns :: Map String { args :: Array RType, result :: RType }
  , assumes :: Map String { args :: Array RType, result :: RType }
  }

resolve :: Array Decl -> Either String SpecFile
resolve decls = do
  result <- foldM step { aliases: Map.empty, fns: Map.empty, assumes: Map.empty } decls
  pure { fns: result.fns, assumes: result.assumes }
  where
  step :: Acc -> Decl -> Either String Acc
  step acc = case _ of
    DAlias name raw -> do
      rt <- resolveRaw acc.aliases raw
      checkLinear rt.pred
      pure acc { aliases = Map.insert name rt acc.aliases }
    DFn name raws -> do
      fnSpec <- mkFnSpec acc name raws
      pure acc { fns = Map.insert name fnSpec acc.fns }
    DAssume name raws -> do
      fnSpec <- mkFnSpec acc name raws
      pure acc { assumes = Map.insert name fnSpec acc.assumes }

  mkFnSpec acc name raws = do
    tys <- traverse (resolveRaw acc.aliases) raws
    traverse_ (\rt -> checkLinear rt.pred) tys
    case Array.unsnoc tys of
      Nothing -> Left ("empty spec for " <> name)
      Just { init, last } -> pure { args: init, result: last }

  resolveRaw aliases = case _ of
    RConcrete rt -> Right rt
    RRef name -> case Map.lookup name aliases of
      Just rt -> Right rt
      Nothing -> Left ("unknown type alias " <> name)

parseSpecFile :: String -> Either String SpecFile
parseSpecFile input =
  case runParser (stripComments input) specFile of
    Left err -> Left ("spec parse error: " <> parseErrorMessage err)
    Right decls -> resolve decls
