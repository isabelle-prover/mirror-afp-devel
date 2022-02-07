module Runner (tests) where

import Distribution.TestSuite
  ( Progress (Finished),
    Result (Fail, Pass),
    Test (Test),
    TestInstance (TestInstance, name, options, run, setOption, tags),
  )
import ProofExtractor (initExtract, extSurgery, removeNoopRules, expandMultiRules)
import Prover (secavProverCode)
import SeCaVTranslator (genInit)
import ShortParser (programParser, sequentParser)
import System.Directory
  ( copyFile,
    createDirectoryIfMissing,
    removeDirectoryRecursive,
  )
import System.Exit (ExitCode (ExitFailure, ExitSuccess))
import System.Process (readProcessWithExitCode)
import System.Timeout (timeout)
import Tests (testcases)
import Unshortener (genFile)

tests :: IO [Test]
tests = do
  let testDir = "test-tmp"
  setup testDir
  let testResults = map (createTest testDir) testcases
  pure testResults

setup :: String -> IO ()
setup = createDirectoryIfMissing False

tearDown :: String -> IO ()
tearDown = removeDirectoryRecursive

createTest :: String -> (String, String) -> Test
createTest topdir (testDir, f) =
  let test testDir f =
        TestInstance
          { run = Finished <$> performTest (topdir <> "/" <> testDir) f,
            name = f,
            tags = [],
            options = [],
            setOption = \_ _ -> Right $ test testDir f
          }
   in Test $ test testDir f

performTest :: String -> String -> IO Result
performTest testDir f = do
  createDirectoryIfMissing False testDir
  copyFile "isabelle/SeCaV.thy" $ testDir <> "/SeCaV.thy"
  copyFile "test/completeness/ROOT" $ testDir <> "/ROOT"

  let parse = sequentParser f
  case parse of
    Left e -> pure $ Fail $ show e
    Right fm -> do
      let (formula, names) = genInit fm
      let proofTree = secavProverCode formula
      let shortProof = initExtract names $ removeNoopRules $ extSurgery $ removeNoopRules $ expandMultiRules proofTree
      let proofParse = programParser shortProof
      case proofParse of
        Left e -> pure $ Fail $ show e
        Right proofAst -> do
          let isabelleProof = genFile "Test" proofAst
          writeFile (testDir <> "/Test.thy") isabelleProof
          (exit, _, error) <- readProcessWithExitCode "isabelle" ["build", "-D", testDir] []
          case exit of
            ExitFailure _ -> pure $ Fail error
            ExitSuccess -> pure Pass
