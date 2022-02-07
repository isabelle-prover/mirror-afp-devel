module ShortLexer where

import Control.Applicative ( Alternative((<|>)) )
import Control.Monad.Identity (Identity)
import Text.Parsec (ParsecT)
import Text.Parsec.Char ( alphaNum, letter, oneOf )
import Text.Parsec.Language ( emptyDef )
import Text.Parsec.Token
    ( GenLanguageDef(commentStart, commentEnd, commentLine,
                     nestedComments, identStart, identLetter, opStart, opLetter,
                     reservedNames, reservedOpNames, caseSensitive),
      LanguageDef,
      makeTokenParser,
      GenTokenParser(TokenParser, parens, identifier, integer, brackets,
                     commaSep, stringLiteral, commaSep1, reserved, reservedOp,
                     whiteSpace) )

languageDef :: LanguageDef st
languageDef = emptyDef
  { commentStart = "(*"
  , commentEnd = "*)"
  , commentLine = ""
  , nestedComments = False
  , identStart = letter
  , identLetter = alphaNum <|> oneOf ['_', '\'']
  , opStart = oneOf ['+', '-', '#']
  , opLetter = oneOf ['+', '-', '#']
  , reservedNames = [ "Var"
                    , "Imp"
                    , "Dis"
                    , "Con"
                    , "Exi"
                    , "Uni"
                    , "Neg"
                    , "Basic"
                    , "AlphaDis"
                    , "AlphaImp"
                    , "AlphaCon"
                    , "BetaCon"
                    , "BetaImp"
                    , "BetaDis"
                    , "GammaExi"
                    , "GammaUni"
                    , "DeltaUni"
                    , "DeltaExi"
                    , "NegNeg"
                    , "Ext"
                    ]
  , reservedOpNames = ["+", "-", "#"]
  , caseSensitive = True
  }

mParens :: ParsecT String u Identity a -> ParsecT String u Identity a
mIdentifier :: ParsecT String u Identity String
mInteger :: ParsecT String u Identity Integer
mBrackets :: ParsecT String u Identity a -> ParsecT String u Identity a
mCommaSep :: ParsecT String u Identity a -> ParsecT String u Identity [a]
mStringLiteral :: ParsecT String u Identity String
mCommaSep1 :: ParsecT String u Identity a -> ParsecT String u Identity [a]
mReserved :: String -> ParsecT String u Identity ()
mReservedOp :: String -> ParsecT String u Identity ()
mWhiteSpace :: ParsecT String u Identity ()

TokenParser
  { parens = mParens
  , identifier = mIdentifier
  , integer = mInteger
  , brackets = mBrackets
  , commaSep = mCommaSep
  , stringLiteral = mStringLiteral
  , commaSep1 = mCommaSep1
  , reserved = mReserved
  , reservedOp = mReservedOp
  , whiteSpace = mWhiteSpace
  } = makeTokenParser languageDef
