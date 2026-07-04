-- | CLI: `lps verify --output <dir> <ModuleName> [--spec <file>]`
-- |
-- | Reads <dir>/<ModuleName>/corefn.json; the spec file defaults to the
-- | module's source path with `.purs` -> `.lps`, resolved against the
-- | output directory's parent (spago builds from the workspace root).
module Lps.Main
  ( main
  ) where

import Prelude

import Data.Argonaut.Parser (jsonParser)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), Replacement(..), lastIndexOf, replace, take)
import Data.Traversable (for, for_)
import Effect (Effect)
import Effect.Console (error, log)
import Lps.CoreFn.Decode (decodeModule)
import Lps.CoreFn.Types (Module)
import Lps.Logic.Smt as Smt
import Lps.Report (FnVerdict(..), anyUnsafe, renderFn)
import Lps.Solver.Z3 (Verdict(..), solve)
import Lps.Spec.Parser (parseSpecFile)
import Lps.Vc (Obligation, checkModule)
import Node.Encoding (Encoding(..))
import Node.FS.Sync (readTextFile)
import Node.Process (argv, setExitCode)

type Args = { output :: String, moduleName :: String, spec :: Maybe String }

parseArgs :: Array String -> Either String Args
parseArgs = go { output: "output", moduleName: "", spec: Nothing }
  where
  go acc args = case Array.uncons args of
    Nothing ->
      if acc.moduleName == "" then Left usage else Right acc
    Just { head, tail } -> case head of
      "verify" -> go acc tail
      "--output" -> withValue tail \v rest -> go (acc { output = v }) rest
      "--spec" -> withValue tail \v rest -> go (acc { spec = Just v }) rest
      name -> go (acc { moduleName = name }) tail

  withValue args f = case Array.uncons args of
    Just { head, tail } -> f head tail
    Nothing -> Left "missing value for option"

  usage = "usage: lps verify --output <dir> <ModuleName> [--spec <file>]"

dirname :: String -> String
dirname p = case lastIndexOf (Pattern "/") p of
  Just i -> take i p
  Nothing -> "."

defaultSpecPath :: String -> Module -> String
defaultSpecPath outputDir mod =
  dirname outputDir <> "/" <> replace (Pattern ".purs") (Replacement ".lps") mod.path

main :: Effect Unit
main = do
  args <- argv
  case parseArgs (Array.drop 2 args) of
    Left msg -> do
      error msg
      setExitCode 2
    Right a -> run a

run :: Args -> Effect Unit
run a = do
  let corefnPath = a.output <> "/" <> a.moduleName <> "/corefn.json"
  corefnText <- readTextFile UTF8 corefnPath
  case jsonParser corefnText >>= decodeModule of
    Left msg -> do
      error ("failed to read " <> corefnPath <> ": " <> msg)
      setExitCode 2
    Right mod -> do
      let specPath = fromMaybe (defaultSpecPath a.output mod) a.spec
      specText <- readTextFile UTF8 specPath
      case parseSpecFile specText of
        Left msg -> do
          error (specPath <> ": " <> msg)
          setExitCode 2
        Right spec -> do
          verdicts <- for (checkModule mod spec) \fn -> do
            let qualified = mod.name <> "." <> fn.fnName
            case fn.result of
              Left msg -> pure (Errored qualified msg)
              Right obligations -> do
                results <- for obligations \o -> do
                  verdict <- solve (Smt.render { decls: o.decls, assumps: o.assumps, goal: o.goal })
                  pure { o, verdict }
                pure (summarize mod qualified results)
          for_ verdicts (log <<< renderFn)
          when (anyUnsafe verdicts) (setExitCode 1)

summarize
  :: Module
  -> String
  -> Array { o :: Obligation, verdict :: Verdict }
  -> FnVerdict
summarize mod qualified results =
  case Array.findMap failing results of
    Just v -> v
    Nothing -> Safe qualified
  where
  failing { o, verdict } = case verdict of
    Valid -> Nothing
    Refuted model -> Just
      (Unsafe qualified { path: mod.path, span: o.span, goal: o.goal, model })
    Unknown out -> Just (Solverless qualified out)
