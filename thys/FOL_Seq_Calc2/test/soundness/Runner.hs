module Runner (tests) where

import Distribution.TestSuite
  ( Progress (Finished),
    Result (Fail, Pass),
    Test (Test),
    TestInstance (TestInstance, name, options, run, setOption, tags),
  )
import ProofExtractor (initExtract)
import Prover (secavProverCode)
import SeCaVTranslator (genInit)
import ShortParser (programParser, sequentParser)
import System.Exit (ExitCode (ExitFailure, ExitSuccess))
import System.Process (readProcessWithExitCode)
import System.Timeout (timeout)
import Tests (testcases)
import Unshortener (genFile)

tests :: IO [Test]
tests = do
  let testResults = map createTest testcases
  pure testResults

createTest :: (String, String) -> Test
createTest (_, f) =
  let test f =
        TestInstance
          { run = Finished <$> performTest f,
            name = f,
            tags = [],
            options = [],
            setOption = \_ _ -> Right $ test f
          }
   in Test $ test f

performTest :: String -> IO Result
performTest f = do
  let parse = sequentParser f
  case parse of
    Left e -> pure $ Fail $ show e
    Right fm -> do
      (exit, _, error) <- readProcessWithExitCode "timeout" ["10s", "cabal", "run", "secav-prover", "--", f] []
      case exit of
        ExitFailure 124 -> pure Pass
        e -> pure $ Fail $ "proof succeeded on invalid formula" <> show e
