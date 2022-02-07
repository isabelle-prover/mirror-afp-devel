module ShortAST where

import Control.Monad.State ( State )
import Data.Bimap ( Bimap )

type Name = String
type Index = Integer

data Term
  = Fun Name [Term]
  | Var Index
  deriving (Show)

data Formula
  = Pre Name [Term]
  | Imp Formula Formula
  | Dis Formula Formula
  | Con Formula Formula
  | Exi Formula
  | Uni Formula
  | Neg Formula
  deriving (Show)

data ShortRule
  = SBasic
  | SAlphaDis
  | SAlphaImp
  | SAlphaCon
  | SBetaCon
  | SBetaImp
  | SBetaDis
  | SGammaExi (Maybe Term)
  | SGammaUni (Maybe Term)
  | SDeltaUni
  | SDeltaExi
  | SNeg
  | SExt
  deriving (Show)

data Application
  = Application ShortRule [[Formula]]
  deriving (Show)

data Intertext
  = Section (Maybe String)
  | Text (Maybe String)
  deriving (Show)

data Proof
  = Proof [Intertext] Formula [Application]
  deriving (Show)

data Program = Program [Proof] [Intertext]
  deriving (Show)

data NameState = NameState
  { preCount :: Integer
  , funCount :: Integer
  , existingPres :: Bimap Name Integer
  , existingFuns :: Bimap Name Integer
  }

type NameGen a = State NameState a

newtype BoundNameState = BoundNameState { depth :: Integer }

type BoundNameGen a = State BoundNameState a
