module Unshortener where

import Control.Monad.State (get, modify, put, runState, evalState)
import Data.Bimap as Map
    ( empty, insert, lookup, null, toList, Bimap )
import Data.List
    ( null, genericReplicate, intercalate, sortBy, uncons )
import ShortAST
    ( BoundNameGen,
      BoundNameState(..),
      NameGen,
      NameState(NameState, existingFuns, funCount, existingPres,
                preCount),
      Program(..),
      Proof(..),
      Intertext(..),
      Application(..),
      ShortRule(..),
      Formula(..),
      Term(..),
      Index,
      Name )

initialBoundNameState :: BoundNameState
initialBoundNameState = BoundNameState { depth = 0 }

dropEnd :: Integer -> String -> String
dropEnd n = reverse . drop (fromIntegral n) . reverse

unsnoc :: [a] -> Maybe ([a], a)
unsnoc [] = Nothing
unsnoc [x] = Just ([], x)
unsnoc (x:xs) = Just (x:a, b)
    where Just (a,b) = unsnoc xs

genBoundName :: Integer -> String
genBoundName x | x < 0 = "?"
genBoundName 0 = "x"
genBoundName 1 = "y"
genBoundName 2 = "z"
genBoundName 3 = "u"
genBoundName 4 = "v"
genBoundName 5 = "w"
genBoundName x = "w" <> genericReplicate (x - 5) '\''

genPropFormula :: Formula -> BoundNameGen String
genPropFormula (Pre n l) = do
  termNames <- traverse genPropTerm l
  pure $ if Data.List.null l then n else n <> " " <> unwords termNames
genPropFormula f = drop 1 . dropEnd 1 <$> genPropFormula' f

genPropFormula' :: Formula -> BoundNameGen String
genPropFormula' (Pre n l) = do
  termNames <- traverse genPropTerm l
  pure $ if Data.List.null l then n else "(" <> n <> " " <> unwords termNames <> ")"
genPropFormula' (Imp a b) = do
  fa <- genPropFormula' a
  fb <- genPropFormula' b
  pure $ "(" <> fa <> " \\<longrightarrow> " <> fb <> ")"
genPropFormula' (Dis a b) = do
  fa <- genPropFormula' a
  fb <- genPropFormula' b
  pure $ "(" <> fa <> " \\<or> " <> fb <> ")"
genPropFormula' (Con a b) = do
  fa <- genPropFormula' a
  fb <- genPropFormula' b
  pure $ "(" <> fa <> " \\<and> " <> fb <> ")"
genPropFormula' (Exi f) = do
  s <- get
  let name = genBoundName (depth s)
  _ <- modify (\st -> st { depth = depth s + 1 })
  ff <- genPropFormula' f
  _ <- put s
  pure $ "(" <> "\\<exists>" <> name <> ". " <> ff <> ")"
genPropFormula' (Uni f) = do
  s <- get
  let name = genBoundName (depth s)
  _ <- modify (\st -> st { depth = depth s + 1 })
  ff <- genPropFormula' f
  _ <- put s
  pure $ "(" <> "\\<forall>" <> name <> ". " <> ff <> ")"
genPropFormula' (Neg f) = do
  ff <- genPropFormula' f
  pure $ "(" <> "\\<not>" <> ff <> ")"

genPropTerm :: Term -> BoundNameGen String
genPropTerm (Fun n l) = do
  termNames <- traverse genPropTerm l
  pure $ if Data.List.null l then n else "(" <> n <> " " <> unwords termNames <> ")"
genPropTerm (Var n) | n < 0 = pure "?"
genPropTerm (Var n) = do
  s <- get
  let relativeIndex = depth s - n - 1
  pure $ genBoundName relativeIndex

mappingList :: Map.Bimap Name Integer -> [(Name, Integer)]
mappingList m =
  let l = Map.toList m in
  sortBy cmp l
  where
    cmp a b =
      let i1 = snd a in
      let i2 = snd b in
      compare i1 i2

genNameMappings :: Map.Bimap Name Integer -> String -> String
genNameMappings m name =
  let l = mappingList m in
  let mappings = genNameMap <$> l in
  "  " <> name <> "\n\n    " <> intercalate "\n\n    " mappings

genNameMap :: (Name, Integer) -> String
genNameMap t =
  let n = fst t in
  let i = snd t in
  show i <> " = " <> n

genProgram :: Program -> String
genProgram (Program l t) =
  let proofs = genProofInit <$> l in
  let proofText = intercalate "\n\n" proofs in
  proofText <> "\n\n" <> genIntertexts t

genIntertext :: Intertext -> String
genIntertext (Section Nothing) = "\n"
genIntertext (Section (Just t)) = "section \\<open>" <> t <> "\\<close>\n\n"
genIntertext (Text Nothing) = ""
genIntertext (Text (Just t)) = "text \\<open>" <> t <> "\\<close>\n\n"

genIntertexts :: [Intertext] -> String
genIntertexts titles =
  intercalate "" $ genIntertext <$> titles

genProofInit :: Proof -> String
genProofInit p@(Proof t f _) =
  let initState = NameState
        { preCount = 0
        , funCount = 0
        , existingPres = empty
        , existingFuns = empty
        } in
  let result = runState (genProof p) initState in
  let prop = evalState (genPropFormula f) initialBoundNameState in
  let text = fst result in
  let finalState = snd result in
  genIntertexts t <>
  "proposition \\<open>" <> prop <> "\\<close> by metis" <> "\n\ntext \\<open>\n" <>
  genNameMappings (existingPres finalState) "Predicate numbers" <>
  "\n" <> (if not $ Map.null (existingFuns finalState)
           then genNameMappings (existingFuns finalState) "Function numbers" <> "\n"
           else "") <> "  \\<close>\n" <> text

genProof :: Proof -> NameGen String
genProof (Proof _ f l) =
  let formula = genFormula f in
  let gr = genApplicationRule in
  let gf = genApplicationFormulas in
  let midRule r = do
        grr <- gr r
        gfr <- gf r
        pure $ "\n  with " <> grr <> " have ?thesis " <> gfr <> "\n    using that by simp" in
    do
      form <- formula
      rules <- case uncons l of
                 Just (first, rest) ->
                   (case unsnoc rest of
                      Just (middle, lastf) -> do
                        grf <- gr first
                        gff <- gf first
                        grl <- gr lastf
                        middleRules <- traverse midRule middle
                        pure $ if Data.List.null middle
                               then
                                 "\n  from " <> grf <> " have ?thesis " <> gff <> "\n    using that by simp" <> "\n  with " <> grl <> " show ?thesis\n    by simp"
                               else
                                 "\n  from " <> grf <> " have ?thesis " <> gff <> "\n    using that by simp" <> intercalate "" middleRules <> "\n  with " <> grl <> " show ?thesis\n    by simp"
                      Nothing -> do
                        grf <- gr first
                        pure ("\n  from " <> grf <> " show ?thesis\n    by simp")
                   )
                 Nothing -> pure ""
      pure $ "\nlemma \\<open>\\<tturnstile>\n  [\n    " <> form <> "\n  ]\n  \\<close>\nproof -" <> rules <> "\nqed"

genApplicationRule :: Application -> NameGen String
genApplicationRule (Application r _) = genRule r

genApplicationFormulas :: Application -> NameGen String
genApplicationFormulas (Application _ l) =
  let restApp a = do
        formulas <- traverse genFormula a
        pure $ " and \\<open>\\<tturnstile>\n    [\n      " <> intercalate ",\n      " formulas <> "\n    ]\n    \\<close>" in
  case uncons l of
    Nothing -> pure ""
    Just (first, rest) -> do
      firstF <- traverse genFormula first
      restF <- traverse restApp rest
      pure $ "if \\<open>\\<tturnstile>\n    [\n      " <> intercalate ",\n      " firstF <> "\n    ]\n    \\<close>" <> intercalate "" restF

genRule :: ShortRule -> NameGen String
genRule SBasic = pure "Basic"
genRule SAlphaDis = pure "AlphaDis"
genRule SAlphaImp = pure "AlphaImp"
genRule SAlphaCon = pure "AlphaCon"
genRule SBetaCon = pure "BetaCon"
genRule SBetaImp = pure "BetaImp"
genRule SBetaDis = pure "BetaDis"
genRule (SGammaExi Nothing) = pure "GammaExi"
genRule (SGammaExi (Just t)) = do
  term <- genTerm t
  pure $ "GammaExi[where t=\\<open>" <> term <> "\\<close>]"
genRule (SGammaUni Nothing) = pure "GammaUni"
genRule (SGammaUni (Just t)) = do
  term <- genTerm t
  pure $ "GammaUni[where t=\\<open>" <> term <> "\\<close>]"
genRule SDeltaUni = pure "DeltaUni"
genRule SDeltaExi = pure "DeltaExi"
genRule SNeg = pure "Neg"
genRule SExt = pure "Ext"

genFormula :: Formula -> NameGen String
genFormula f = drop 1 . dropEnd 1 <$> genFormula' f

genFormula' :: Formula -> NameGen String
genFormula' (Pre n l) = do
  preName <- genPreName n
  termNames <- traverse genTerm l
  pure $ "(" <> "Pre " <> preName <> " [" <> intercalate ", " termNames <> "])"
genFormula' (Imp a b) = do
  fa <- genFormula' a
  fb <- genFormula' b
  pure $ "(" <> "Imp " <> fa <> " " <> fb <> ")"
genFormula' (Dis a b) = do
  fa <- genFormula' a
  fb <- genFormula' b
  pure $ "(" <> "Dis " <> fa <> " " <> fb <> ")"
genFormula' (Con a b) = do
  fa <- genFormula' a
  fb <- genFormula' b
  pure $ "(" <> "Con " <> fa <> " " <> fb <> ")"
genFormula' (Exi f) = do
  ff <- genFormula' f
  pure $ "(" <> "Exi " <> ff <> ")"
genFormula' (Uni f) = do
  ff <- genFormula' f
  pure $ "(" <> "Uni " <> ff <> ")"
genFormula' (Neg f) = do
  ff <- genFormula' f
  pure $ "(" <> "Neg " <> ff <> ")"

genTerm :: Term -> NameGen String
genTerm (Fun n l) = do
  fName <- genFunName n
  termNames <- traverse genTerm l
  pure $ "Fun " <> fName <> " [" <> intercalate ", " termNames <> "]"
genTerm (Var n) = do
  index <- genIndex n
  pure $ "Var " <> index

genIndex :: Index -> NameGen String
genIndex n = pure $ show n

genFunName :: Name -> NameGen String
genFunName n = do
  s <- get
  case Map.lookup n (existingFuns s) of
    Just index -> pure $ show index
    Nothing -> do
      _ <- modify (\st -> st { funCount = funCount s + 1
                               , existingFuns = Map.insert n (funCount s) (existingFuns s)
                               })
      pure $ show (funCount s)

genPreName :: Name -> NameGen String
genPreName n = do
  s <- get
  case Map.lookup n (existingPres s) of
    Just index -> pure $ show index
    Nothing -> do
      _ <- modify (\st -> st { preCount = preCount s + 1
                               , existingPres = Map.insert n (preCount s) (existingPres s)
                               })
      pure $ show (preCount s)

genFile :: String -> Program -> String
genFile name p =
  "theory " <> name <> " imports SeCaV begin\n\n"
    <> genProgram p
    <> "\n\nend"
