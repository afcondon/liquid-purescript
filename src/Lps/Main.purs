-- | CLI.
-- |
-- |   lps verify     --output <dir> <ModuleName> [--spec <file>]
-- |                  [--include <file>]... [--smt2-dir <dir>]
-- |   lps verify-all --output <dir> [--include <file>]... [--smt2-dir <dir>]
-- |
-- | `verify-all` scans every module under the output directory and
-- | verifies each one that has a sibling `.lps` spec file — the shape
-- | needed to run as a spago backend cmd. `--include` files (shared spec
-- | corpora like lib/prelude.lps) are concatenated ahead of the module's
-- | own spec, so module declarations win on name collisions.
module Lps.Main
  ( main
  ) where

import Prelude

import Data.Argonaut.Parser (jsonParser)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), Replacement(..), joinWith, lastIndexOf, replace, take)
import Data.Traversable (for, for_)
import Data.TraversableWithIndex (forWithIndex)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Console (error, log)
import Lps.CoreFn.Decode (decodeModule)
import Lps.CoreFn.Types (Module)
import Lps.Docs (SigMap, crossCheck, readSigs)
import Lps.Logic (Sort(..))
import Lps.Logic.Smt as Smt
import Lps.Report (FnVerdict(..), anyUnsafe, renderFn)
import Lps.Solver.Z3 (Verdict(..), solve)
import Lps.Spec.Parser (parseSpecFile)
import Lps.Spec.Syntax (SpecFile, baseSort)
import Lps.Vc (Obligation, checkModule, discName)
import Node.Encoding (Encoding(..))
import Node.FS.Perms (permsAll)
import Node.FS.Sync (exists, mkdir', readTextFile, readdir, writeTextFile)
import Node.Process (argv, setExitCode)

type Args =
  { command :: String
  , output :: String
  , moduleName :: String
  , spec :: Maybe String
  , includes :: Array String
  , smt2Dir :: Maybe String
  }

parseArgs :: Array String -> Either String Args
parseArgs = go
  { command: ""
  , output: "output"
  , moduleName: ""
  , spec: Nothing
  , includes: []
  , smt2Dir: Nothing
  }
  where
  go acc args = case Array.uncons args of
    Nothing -> case acc.command of
      "verify" | acc.moduleName /= "" -> Right acc
      "verify-all" -> Right acc
      _ -> Left usage
    Just { head, tail } -> case head of
      "verify" -> go (acc { command = "verify" }) tail
      "verify-all" -> go (acc { command = "verify-all" }) tail
      "--output" -> withValue tail \v rest -> go (acc { output = v }) rest
      "--spec" -> withValue tail \v rest -> go (acc { spec = Just v }) rest
      "--include" -> withValue tail \v rest ->
        go (acc { includes = Array.snoc acc.includes v }) rest
      "--smt2-dir" -> withValue tail \v rest -> go (acc { smt2Dir = Just v }) rest
      name -> go (acc { moduleName = name }) tail

  withValue args f = case Array.uncons args of
    Just { head, tail } -> f head tail
    Nothing -> Left "missing value for option"

  usage = joinWith "\n"
    [ "usage: lps verify     --output <dir> <ModuleName> [--spec <file>] [--include <file>]... [--smt2-dir <dir>]"
    , "       lps verify-all --output <dir> [--include <file>]... [--smt2-dir <dir>]"
    ]

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
    Right a
      | a.command == "verify-all" -> runAll a
      | otherwise -> do
          unsafe <- runModule a a.moduleName
          when unsafe (setExitCode 1)

runAll :: Args -> Effect Unit
runAll a = do
  entries <- readdir a.output
  results <- for entries \entry -> do
    hasCorefn <- exists (a.output <> "/" <> entry <> "/corefn.json")
    if hasCorefn then hasSpec entry else pure Nothing
  let modules = Array.catMaybes results
  if Array.null modules then
    log "lps: no modules with .lps specs found"
  else do
    unsafes <- for modules (runModule a)
    when (Array.any identity unsafes) (setExitCode 1)
  where
  -- a module participates if its default (or only plausible) spec exists
  hasSpec name = do
    text <- readTextFile UTF8 (a.output <> "/" <> name <> "/corefn.json")
    case jsonParser text >>= decodeModule of
      Left _ -> pure Nothing
      Right mod -> do
        present <- exists (defaultSpecPath a.output mod)
        pure (if present then Just name else Nothing)

-- | Verify one module; returns whether anything was UNSAFE/UNSUPPORTED.
runModule :: Args -> String -> Effect Boolean
runModule a moduleName = do
  let corefnPath = a.output <> "/" <> moduleName <> "/corefn.json"
  corefnText <- readTextFile UTF8 corefnPath
  case jsonParser corefnText >>= decodeModule of
    Left msg -> do
      error ("failed to read " <> corefnPath <> ": " <> msg)
      setExitCode 2
      pure false
    Right mod -> do
      let specPath = fromMaybe (defaultSpecPath a.output mod) a.spec
      includeTexts <- for a.includes (readTextFile UTF8)
      specText <- readTextFile UTF8 specPath
      case parseSpecFile (joinWith "\n" (Array.snoc includeTexts specText)) of
        Left msg -> do
          error (specPath <> ": " <> msg)
          setExitCode 2
          pure false
        Right spec -> do
          sigs <- readSigMap (a.output <> "/" <> moduleName <> "/docs.json")
          let
            mismatches = Array.mapMaybe
              ( \(Tuple name s) ->
                  map (\msg -> Errored (mod.name <> "." <> name) ("spec/type mismatch: " <> msg))
                    (crossCheck sigs name s)
              )
              (Map.toUnfoldable spec.fns)
          verdicts <- verifyModule a mod (dropMismatched sigs spec)
          let allVerdicts = mismatches <> verdicts
          for_ allVerdicts (log <<< renderFn)
          pure (anyUnsafe allVerdicts)

-- Signature mismatches are reported as Errored verdicts; drop them from
-- the spec so the checker doesn't also run on a wrong-shaped spec.
dropMismatched :: SigMap -> SpecFile -> SpecFile
dropMismatched sigs spec =
  spec { fns = Map.filterWithKey (\name s -> crossCheck sigs name s == Nothing) spec.fns }

readSigMap :: String -> Effect SigMap
readSigMap path = do
  present <- exists path
  if present then do
    text <- readTextFile UTF8 path
    case jsonParser text >>= readSigs of
      Left _ -> pure Map.empty
      Right sigs -> pure sigs
  else pure Map.empty

verifyModule :: Args -> Module -> SpecFile -> Effect (Array FnVerdict)
verifyModule a mod spec = do
  for_ a.smt2Dir \dir -> mkdir' dir { recursive: true, mode: permsAll }
  let
    sorts = Array.fromFoldable (Map.keys spec.datas)
    funs =
      ( Map.toUnfoldable spec.measures <#> \(Tuple name m) ->
          { name, args: [ SData m.dataName ], res: baseSort m.result.base }
      )
        <>
          ( do
              Tuple dataName d <- Map.toUnfoldable spec.datas
              c <- d.ctors
              pure { name: discName c.name, args: [ SData dataName ], res: SBool }
          )
  for (checkModule mod spec) \fn -> do
    let qualified = mod.name <> "." <> fn.fnName
    case fn.result of
      Left msg -> pure (Errored qualified msg)
      Right obligations -> do
        results <- forWithIndex obligations \i o -> do
          let script = Smt.render { sorts, funs, decls: o.decls, assumps: o.assumps, goal: o.goal }
          for_ a.smt2Dir \dir ->
            writeTextFile UTF8
              (dir <> "/" <> mod.name <> "." <> fn.fnName <> "-" <> show i <> ".smt2")
              (script <> "\n")
          verdict <- solve script
          pure { o, verdict }
        pure (summarize mod qualified results)

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
