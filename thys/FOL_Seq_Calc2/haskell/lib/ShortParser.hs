module ShortParser where

import Data.Function (fix)
import ShortAST
    ( Program(..),
      Proof(..),
      Intertext(..),
      Application(..),
      ShortRule(..),
      Formula(..),
      Term(..),
      Index,
      Name )
import ShortLexer
    ( mParens,
      mIdentifier,
      mInteger,
      mBrackets,
      mCommaSep,
      mStringLiteral,
      mCommaSep1,
      mReserved,
      mReservedOp,
      mWhiteSpace )
import Text.Parsec
    ( choice,
      eof,
      many1,
      option,
      optionMaybe,
      sepBy,
      (<?>),
      many,
      parse,
      try,
      ParseError,
      Parsec )

type SParser a = Parsec String () a

name :: SParser Name
name = mIdentifier

index :: SParser Index
index = mInteger

fun :: SParser Term
fun = do
  f <- name
  args <- option [] termList
  pure $ Fun f args

var :: SParser Term
var = Var <$> index

term :: SParser Term
term = fix allTerms
  where
    allTerms _ = choice
      [ fun
      , var
      ] <?> "a function name or a variable"

termList :: SParser [Term]
termList = fix $ const (mBrackets $ mCommaSep term)

-- Parsing of formulas
predicate :: SParser Formula
predicate = Pre <$> name <*> option [] termList

implication :: SParser Formula
implication = fix $ const $ mReserved "Imp" *> (Imp <$> formula <*> formula)

disjunction :: SParser Formula
disjunction = fix $ const $ mReserved "Dis" *> (Dis <$> formula <*> formula)

conjunction :: SParser Formula
conjunction = fix $ const $ mReserved "Con" *> (Con <$> formula <*> formula)

existential :: SParser Formula
existential = fix $ const $ mReserved "Exi" *> (Exi <$> formula)

universal :: SParser Formula
universal = fix $ const $ mReserved "Uni" *> (Uni <$> formula)

negation :: SParser Formula
negation = fix $ const $ mReserved "Neg" *> (Neg <$> formula)

formula :: SParser Formula
formula = fix allFormulas
  where
    allFormulas _ = choice
      [ predicate
      , implication
      , disjunction
      , conjunction
      , existential
      , universal
      , negation
      , mParens formula
      ] <?> "a formula"


sequent :: SParser [Formula]
sequent = mCommaSep1 formula

-- Parsing of proof rules
basic :: SParser ShortRule
basic = do
  mReserved "Basic"
  pure SBasic

alphaDis :: SParser ShortRule
alphaDis = do
  mReserved "AlphaDis"
  pure SAlphaDis

alphaImp :: SParser ShortRule
alphaImp = do
  mReserved "AlphaImp"
  pure SAlphaImp

alphaCon :: SParser ShortRule
alphaCon = do
  mReserved "AlphaCon"
  pure SAlphaCon

betaDis :: SParser ShortRule
betaDis = do
  mReserved "BetaDis"
  pure SBetaDis

betaImp :: SParser ShortRule
betaImp = do
  mReserved "BetaImp"
  pure SBetaImp

betaCon :: SParser ShortRule
betaCon = do
  mReserved "BetaCon"
  pure SBetaCon

gammaExi :: SParser ShortRule
gammaExi = do
  mReserved "GammaExi"
  t <- optionMaybe (mBrackets term)
  pure $ SGammaExi t

gammaUni :: SParser ShortRule
gammaUni = do
  mReserved "GammaUni"
  t <- optionMaybe (mBrackets term)
  pure $ SGammaUni t

deltaUni :: SParser ShortRule
deltaUni = do
  mReserved "DeltaUni"
  pure SDeltaUni

deltaExi :: SParser ShortRule
deltaExi = do
  mReserved "DeltaExi"
  pure SDeltaExi

ext :: SParser ShortRule
ext = do
  mReserved "Ext"
  pure SExt

neg :: SParser ShortRule
neg = do
  mReserved "NegNeg"
  pure SNeg

rule :: SParser ShortRule
rule = fix allRules
  where
    allRules _ = choice
      [ basic
      , alphaDis
      , alphaImp
      , alphaCon
      , betaDis
      , betaImp
      , betaCon
      , gammaExi
      , gammaUni
      , deltaUni
      , deltaExi
      , neg
      , ext
      ] <?> "a proof rule"

-- Parsing of rule applications
application :: SParser Application
application = do
  r <- rule
  l <- many formula `sepBy` mReservedOp "+"
  pure $ Application r l

section :: SParser Intertext
section = do
  mReservedOp "#"
  t <- optionMaybe mStringLiteral
  pure $ Section t

text :: SParser Intertext
text = do
  mReservedOp "-"
  t <- optionMaybe mStringLiteral
  pure $ Text t

intertext :: SParser Intertext
intertext = choice [section, text]

-- Parsing of proofs
proof :: SParser Proof
proof = do
  t <- many1 intertext
  f <- formula
  l <- many1 application
  pure $ Proof t f l

firstProof :: SParser Proof
firstProof = do
  t <- many intertext
  f <- formula
  l <- many1 application
  pure $ Proof t f l

-- Parsing of whole files
program :: SParser Program
program = do
  first <- firstProof
  l <- many $ try proof
  t <- many intertext
  pure $ Program (first:l) t

programParser :: String -> Either ParseError Program
programParser = parse (mWhiteSpace *> program <* eof) ""

sequentParser :: String -> Either ParseError [Formula]
sequentParser = parse (mWhiteSpace *> sequent <* eof) ""
