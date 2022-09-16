import Prelude
import Data.Char (chr, ord)
import Data.List (intersperse)
import System.Environment

import Arith
import Prover

instance Show Arith.Nat where
  show (Nat n) = show n

charFrom :: Char -> Arith.Nat -> Char
charFrom c n = chr (ord c + fromInteger (Arith.integer_of_nat n))

instance Show Tm where
  show (Var n) = show n
  show (Fun f []) = charFrom 'a' f : ""
  show (Fun f ts) = charFrom 'f' f : "(" ++ concat (intersperse ", " (map show ts)) ++ ")"

instance Show Fm where
  show Falsity = "Fls"
  show (Pre p []) = charFrom 'P' p : ""
  show (Pre p ts) = charFrom 'P' p : "(" ++ concat (intersperse ", " (map show ts)) ++ ")"
  show (Imp p q) = "(" ++ show p ++ ") -> (" ++ show q ++ ")"
  show (Uni p) = "forall " ++ show p

showRule :: Rule -> String
showRule (Axiom n ts) = "Axiom on " ++ show (Pre n ts)
showRule FlsL = "FlsL"
showRule FlsR = "FlsR"
showRule Idle = "Idle"
showRule (ImpL p q) = "ImpL on " ++ show p ++ " and " ++ show q
showRule (ImpR p q) = "ImpR on " ++ show p ++ " and " ++ show q
showRule (UniL t p) = "UniL on " ++ show t ++ " and " ++ show p
showRule (UniR p) = "UniR on " ++ show p

showFms :: [Fm] -> String
showFms ps = concat (intersperse ", " (map show ps))

showTree :: Int -> Tree (([Fm], [Fm]), Rule) -> String
showTree n (Node ((l, r), rule) (Abs_fset (Set ts))) =
  let inc = if length ts > 1 then 2 else 0 in
  replicate n ' ' ++ showFms l ++ " |- " ++ showFms r ++ "\n" ++
  replicate n ' ' ++ " + " ++ showRule rule ++ "\n" ++
  concat (map (showTree (n + inc)) ts)

instance Read Arith.Nat where
  readsPrec d s = map (\(n, s) -> (Arith.Nat n, s)) (readsPrec d s :: [(Integer, String)])

deriving instance Read Tm
deriving instance Read Fm

main :: IO ()
main = do
  args <- getArgs
  let p = read (head args) :: Fm
  let res = prove p
  putStrLn (showTree 0 res)

