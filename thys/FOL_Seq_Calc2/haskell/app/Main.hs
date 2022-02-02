module Main where

import Options.Applicative
    ( optional,
      (<**>),
      argument,
      fullDesc,
      header,
      help,
      info,
      long,
      metavar,
      progDesc,
      short,
      str,
      strOption,
      execParser,
      helper,
      Parser )
import ProofExtractor
    ( expandMultiRules, removeNoopRules, extSurgery, initExtract )
import Prover ( secavProverCode )
import SeCaVTranslator ( genInit )
import ShortParser ( programParser, sequentParser )
import System.FilePath (takeBaseName)
import Unshortener (genFile)

data Arguments = Arguments
  { formula :: String
  , isabelle :: Maybe String
  }

arguments :: Parser Arguments
arguments = Arguments
            <$> argument str (metavar "FORMULA" <> help "Formula to attempt to prove")
            <*> optional (strOption
                  $ long "isabelle"
                    <> short 'i'
                    <> metavar "FILENAME"
                    <> help "Output an Isabelle proof in FILENAME")

main :: IO ()
main = run =<< execParser opts
  where
    opts = info (arguments <**> helper)
      ( fullDesc
      <> progDesc "Attempt to prove the first-order formula FORMULA"
      <> header "secav-prover - a prover for SeCaV" )

run :: Arguments -> IO ()
run (Arguments f i) =
  case sequentParser f of
    Left e -> print e
    Right s ->
      let (formulas, names) = genInit s in
        let proofTree = secavProverCode formulas in
          let shortProof = initExtract names $ removeNoopRules $ extSurgery $ removeNoopRules $ expandMultiRules proofTree in
            case i of
              Just file ->
                let parse = programParser shortProof in
                  case parse of
                    Left e -> print e
                    Right ast ->
                      let isabelleProof = genFile (takeBaseName file) ast in
                        writeFile file isabelleProof
              Nothing ->
                putStrLn shortProof
