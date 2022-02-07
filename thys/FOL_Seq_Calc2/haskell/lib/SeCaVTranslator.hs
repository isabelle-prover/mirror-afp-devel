module SeCaVTranslator where

import Arith ( Nat(..) )
import Control.Monad.State
    ( liftM2, modify, runState, MonadState(get) )
import qualified Data.Bimap as Map
import SeCaV ( Fm(..), Tm(..) )
import ShortAST as AST
    ( NameGen, NameState(..), Formula(..), Term(..), Index, Name )

genInit :: [Formula] -> ([Fm], NameState)
genInit fs =
  let initState = NameState
        { preCount = 0
        , funCount = 0
        , existingPres = Map.empty
        , existingFuns = Map.empty
        }
  in runState (genSequent fs) initState

genSequent :: [Formula] -> NameGen [Fm]
genSequent = foldr (liftM2 (:) . genFormula) (pure [])

genFormula :: Formula -> NameGen Fm
genFormula (AST.Pre n l) = do
  preName <- genPreName n
  termNames <- traverse genTerm l
  pure $ SeCaV.Pre preName termNames
genFormula (AST.Imp a b) = do
  fa <- genFormula a
  fb <- genFormula b
  pure $ SeCaV.Imp fa fb
genFormula (AST.Dis a b) = do
  fa <- genFormula a
  fb <- genFormula b
  pure $ SeCaV.Dis fa fb
genFormula (AST.Con a b) = do
  fa <- genFormula a
  fb <- genFormula b
  pure $ SeCaV.Con fa fb
genFormula (AST.Exi f) = do
  ff <- genFormula f
  pure $ SeCaV.Exi ff
genFormula (AST.Uni f) = do
  ff <- genFormula f
  pure $ SeCaV.Uni ff
genFormula (AST.Neg f) = do
  ff <- genFormula f
  pure $ SeCaV.Neg ff

genTerm :: Term -> NameGen Tm
genTerm (AST.Fun n l) = do
  fName <- genFunName n
  termNames <- traverse genTerm l
  pure $ SeCaV.Fun fName termNames
genTerm (AST.Var n) = pure $ SeCaV.Var $ Nat n

genIndex :: Index -> NameGen Nat
genIndex n = pure $ Nat n

genFunName :: Name -> NameGen Nat
genFunName n = do
  s <- get
  case Map.lookup n (existingFuns s) of
    Just index -> pure $ Nat index
    Nothing -> do
      _ <- modify (\st -> st { funCount = funCount s + 1
                             , existingFuns = Map.insert n (funCount s) (existingFuns s)
                             })
      pure $ Nat $ funCount s

genPreName :: Name -> NameGen Nat
genPreName n = do
  s <- get
  case Map.lookup n (existingPres s) of
    Just index -> pure $ Nat index
    Nothing -> do
      _ <- modify (\st -> st { preCount = preCount s + 1
                             , existingPres = Map.insert n (preCount s) (existingPres s)
                             })
      pure $ Nat $ preCount s
