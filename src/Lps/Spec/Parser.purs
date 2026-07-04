-- | Parser for `.lps` spec files (ADR-003: specs live beside sources, the
-- | .purs file is untouched). Rejects non-linear arithmetic at parse time
-- | so every obligation stays decidable (ADR-005).
-- |
-- | Phase 2 declarations:
-- |
-- |   data IntList = INil | ICons Int IntList
-- |   measure len :: IntList -> { v : Int | v >= 0 }
-- |     INil = 0
-- |     ICons x xs = 1 + len xs
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
import Data.Set (Set)
import Data.Set as Set
import Data.String as String
import Data.String.CodeUnits (fromCharArray)
import Data.Traversable (traverse)
import Lps.Logic (Op(..), Term(..))
import Lps.Spec.Syntax (Base(..), FnSpec, RType, SpecFile, trivial)
import Parsing (Parser, fail, runParser, parseErrorMessage)
import Parsing.Combinators (many, notFollowedBy, option, sepBy1, try)
import Parsing.Expr (Assoc(..), Operator(..), buildExprParser)
import Parsing.String (char, eof, string)
import Parsing.String.Basic (alphaNum, intDecimal, lower, skipSpaces, upper)

-- Surface declarations before name resolution
data RTypeRaw
  = RRef String
  | RRefined { binder :: String, baseName :: String, pred :: Term }

data Decl
  = DAlias String RTypeRaw
  | DFn String (Array RTypeRaw)
  | DAssume String (Array RTypeRaw)
  | DData String (Array { name :: String, fieldNames :: Array String })
  | DMeasure
      { name :: String
      , arg :: RTypeRaw
      , result :: RTypeRaw
      , eqns :: Array { ctor :: String, params :: Array String, rhs :: Term }
      }

type P a = Parser String a

lexeme :: forall a. P a -> P a
lexeme p = p <* skipSpaces

symbol :: String -> P String
symbol s = lexeme (try (string s))

keyword :: String -> P String
keyword s = lexeme (try (string s <* notFollowedBy alphaNum))

identChar :: P Char
identChar = alphaNum <|> char '_' <|> char '\''

-- | Reserved words may not be variable names — without this, the
-- | juxtaposition application parser (`len xs`) would swallow a following
-- | `type`/`data`/... keyword as another argument.
reserved :: Set String
reserved = Set.fromFoldable
  [ "type", "data", "measure", "assume", "not", "true", "false" ]

varId :: P String
varId = try $ lexeme do
  c <- lower <|> char '_'
  cs <- many identChar
  let name = fromCharArray ([ c ] <> Array.fromFoldable cs)
  when (Set.member name reserved) (fail (name <> " is reserved"))
  pure name

conId :: P String
conId = lexeme do
  c <- upper
  cs <- many identChar
  pure (fromCharArray ([ c ] <> Array.fromFoldable cs))

term :: P Term
term = fix \p ->
  let
    -- an atom that is not an application (application arguments)
    atomNoApp =
      (TInt <$> lexeme intDecimal)
        <|> (keyword "true" $> TBool true)
        <|> (keyword "false" $> TBool false)
        <|> (TVar <$> varId)
        <|> (symbol "(" *> p <* symbol ")")

    -- `len xs` juxtaposition: a variable followed by atoms is an
    -- uninterpreted (measure) application
    atom =
      (TInt <$> lexeme intDecimal)
        <|> (keyword "true" $> TBool true)
        <|> (keyword "false" $> TBool false)
        <|> appOrVar
        <|> (symbol "(" *> p <* symbol ")")

    appOrVar = do
      name <- varId
      args <- many atomNoApp
      pure case Array.fromFoldable args of
        [] -> TVar name
        as -> TApp name as

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

rtypeRaw :: P RTypeRaw
rtypeRaw = refined <|> (RRef <$> conId)
  where
  refined = do
    _ <- symbol "{"
    binder <- varId
    _ <- symbol ":"
    baseName <- conId
    pred <- option (TBool true) (symbol "|" *> term)
    _ <- symbol "}"
    pure (RRefined { binder, baseName, pred })

fnShape :: P (Array RTypeRaw)
fnShape = Array.fromFoldable <$> sepBy1 rtypeRaw (symbol "->")

decl :: P Decl
decl = alias <|> dataDecl <|> measureDecl <|> assumeSpec <|> fnSpec
  where
  alias = do
    _ <- keyword "type"
    name <- conId
    _ <- symbol "="
    DAlias name <$> rtypeRaw

  dataDecl = do
    _ <- keyword "data"
    name <- conId
    _ <- symbol "="
    ctors <- sepBy1 ctor (symbol "|")
    pure (DData name (Array.fromFoldable ctors))

  ctor = do
    name <- conId
    fieldNames <- Array.fromFoldable <$> many conId
    pure { name, fieldNames }

  measureDecl = do
    _ <- keyword "measure"
    name <- varId
    _ <- symbol "::"
    shape <- fnShape
    { arg, result } <- case shape of
      [ arg, result ] -> pure { arg, result }
      _ -> fail "a measure has exactly one argument"
    eqns <- Array.fromFoldable <$> many eqn
    pure (DMeasure { name, arg, result, eqns })

  eqn = try do
    ctorName <- conId
    params <- Array.fromFoldable <$> many varId
    _ <- symbol "="
    rhs <- term
    pure { ctor: ctorName, params, rhs }

  assumeSpec = do
    _ <- keyword "assume"
    name <- varId
    _ <- symbol "::"
    DAssume name <$> fnShape

  fnSpec = do
    name <- varId
    _ <- symbol "::"
    DFn name <$> fnShape

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
-- | Uninterpreted applications count as non-literal atoms.
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
  TApp _ args -> traverse_ checkLinear args

type Acc =
  { aliases :: Map String RType
  , fns :: Map String FnSpec
  , assumes :: Map String FnSpec
  , datas :: Map String { name :: String, ctors :: Array { name :: String, fields :: Array Base } }
  , measures :: Map String { name :: String, dataName :: String, result :: RType, eqns :: Map String { params :: Array String, rhs :: Term } }
  }

resolve :: Array Decl -> Either String SpecFile
resolve decls = do
  result <- foldM step
    { aliases: Map.empty, fns: Map.empty, assumes: Map.empty, datas: Map.empty, measures: Map.empty }
    decls
  pure
    { fns: result.fns
    , assumes: result.assumes
    , datas: result.datas
    , measures: result.measures
    }
  where
  -- data names are visible to every declaration, including forward ones
  dataNames :: Set String
  dataNames = Set.fromFoldable (Array.mapMaybe dataName decls)
    where
    dataName = case _ of
      DData name _ -> Just name
      _ -> Nothing

  baseName :: String -> Maybe Base
  baseName = case _ of
    "Int" -> Just BInt
    "Boolean" -> Just BBool
    name | Set.member name dataNames -> Just (BData name)
    _ -> Nothing

  step :: Acc -> Decl -> Either String Acc
  step acc = case _ of
    DAlias name raw -> do
      rt <- resolveRaw acc raw
      checkLinear rt.pred
      pure acc { aliases = Map.insert name rt acc.aliases }
    DFn name raws -> do
      fnSpec <- mkFnSpec acc name raws
      pure acc { fns = Map.insert name fnSpec acc.fns }
    DAssume name raws -> do
      fnSpec <- mkFnSpec acc name raws
      pure acc { assumes = Map.insert name fnSpec acc.assumes }
    DData name ctors -> do
      resolved <- traverse
        ( \c -> do
            fields <- traverse
              ( \fn -> case baseName fn of
                  Just b -> Right b
                  Nothing -> Left ("unknown type " <> fn <> " in constructor " <> c.name)
              )
              c.fieldNames
            pure { name: c.name, fields }
        )
        ctors
      pure acc { datas = Map.insert name { name, ctors: resolved } acc.datas }
    DMeasure m -> do
      argT <- resolveRaw acc m.arg
      resultT <- resolveRaw acc m.result
      checkLinear resultT.pred
      dataName <- case argT.base of
        BData d -> Right d
        _ -> Left ("measure " <> m.name <> " must take a declared data type")
      dataDef <- case Map.lookup dataName acc.datas of
        Just d -> Right d
        Nothing -> Left ("measure " <> m.name <> ": data " <> dataName <> " not declared yet")
      eqns <- foldM
        ( \eqAcc e -> do
            ctorDef <- case Array.find (\c -> c.name == e.ctor) dataDef.ctors of
              Just c -> Right c
              Nothing -> Left ("measure " <> m.name <> ": " <> e.ctor <> " is not a constructor of " <> dataName)
            when (Array.length e.params /= Array.length ctorDef.fields)
              ( Left
                  ( "measure " <> m.name <> ": " <> e.ctor <> " has "
                      <> show (Array.length ctorDef.fields)
                      <> " field(s), equation binds "
                      <> show (Array.length e.params)
                  )
              )
            checkLinear e.rhs
            pure (Map.insert e.ctor { params: e.params, rhs: e.rhs } eqAcc)
        )
        Map.empty
        m.eqns
      when (Map.size eqns /= Array.length dataDef.ctors)
        (Left ("measure " <> m.name <> " must have exactly one equation per constructor of " <> dataName))
      pure acc
        { measures = Map.insert m.name
            { name: m.name, dataName, result: resultT, eqns }
            acc.measures
        }

  mkFnSpec acc name raws = do
    tys <- traverse (resolveRaw acc) raws
    traverse_ (\rt -> checkLinear rt.pred) tys
    case Array.unsnoc tys of
      Nothing -> Left ("empty spec for " <> name)
      Just { init, last } -> pure { args: init, result: last }

  resolveRaw :: Acc -> RTypeRaw -> Either String RType
  resolveRaw acc = case _ of
    RRef name -> case baseName name of
      Just b -> Right (trivial b)
      Nothing -> case Map.lookup name acc.aliases of
        Just rt -> Right rt
        Nothing -> Left ("unknown type " <> name)
    RRefined r -> case baseName r.baseName of
      Just b -> Right { binder: r.binder, base: b, pred: r.pred }
      Nothing -> Left ("refined base must be Int, Boolean, or a declared data type; got " <> r.baseName)

parseSpecFile :: String -> Either String SpecFile
parseSpecFile input =
  case runParser (stripComments input) specFile of
    Left err -> Left ("spec parse error: " <> parseErrorMessage err)
    Right decls -> resolve decls
