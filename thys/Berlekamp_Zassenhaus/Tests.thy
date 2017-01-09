(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
theory Tests
  imports 
  "~~/src/HOL/Library/Code_Target_Numeral"
  "~~/src/HOL/Library/Code_Char"
  "../Show/Show_Instances"
  Factorize_Int_Poly
  Factorize_Rat_Poly
begin

(* 
-- compile by: 
   ghc --make Main.hs -O2
-- then run:
-- time ./Main --intern 1 2 4 3 1
-- time ./Main --extern `cat testBig.txt`

-- for profiling: ghc --make Main.hs -prof -fprof-auto -O2
-- then run:
-- time ./Main --intern `cat testBig.txt` +RTS -p -RTS
{-# LANGUAGE LambdaCase #-}
module Main(main)
  where
import System.Environment
import Factorize

main = do args <- getArgs
          runCommands args

runCommands [] = return ()
runCommands (h:lst)
  = do putStrLn (case h of
                     "--extern" -> test_extern f
                     "--intern" -> test_intern f
                     _ -> "Please use --extern or --intern (you used "++h++")")
       runCommands r
    where (f',r) = break (\case {'-':'-':_ -> True; _ -> False}) lst
          f :: [Integer]
          f = concat (map readsMe f')
          readsMe [] = []
          readsMe c@(_:tl)
            = case reads c of
                   [] -> readsMe tl
                   (r,rs):_ -> r:readsMe rs

*)

definition test_intern :: "integer list \<Rightarrow> string" where 
  "test_intern p = (show (map_prod id (map (map_prod id Suc)) (factorize_int_poly (poly_of_list (map (int_of_integer) p)))))" 

consts external_factorization :: "integer list \<Rightarrow> (integer list \<times> integer)list" 
  
code_printing code_module "Mathematica" => (Haskell) {*
import System.Process;
import System.IO.Unsafe;
import System.IO;

-- path to binary of Mathematica
binary = "/Applications/Mathematica.app/Contents/MacOS/WolframKernel";

-- params to Mathematica
params = ["-rawmode"];


bef :: String;
bef = "Inp := ";

aft :: String;
aft = "; " ++
   "P := Expand[FromDigits[Reverse[Inp], x]]; " ++   -- convert list to polynomial
   "Facts := FactorList[P]; " ++                     -- factorize
   "Outp := Map[Function[fi, {CoefficientList[First[fi], x], {First[Rest[fi]]}}], Facts]; " ++   -- convert polynomials into coefficient lists
   "Outp";                                           -- and print result

change_braces :: String -> String -> String -> String;
change_braces [o1,c1] [o2,c2] = map (\ c -> if c == o1 then o2 else if c == c1 then c2 else c);

-- input which is send to Mathematica
m_input :: [Integer] -> String;
m_input p = bef ++ change_braces "[]" "{}" (show p) ++ aft;

-- parsing output from Mathematica
m_output :: String -> [([Integer], Integer)];
m_output xs = let
  ys = dropWhile (\ c -> c /= '=') xs;
  zs = filter (\ c -> (c >= '0' && c <= '9') || c `elem` ",-{}") ys;
  fact_list = read (change_braces "{}" "[]" zs);
  in map (\ [fi,[i]] -> (fi,i)) fact_list;

-- starting Mathematica process
m_in_out :: (Handle, Handle);
m_in_out = unsafePerformIO (do {
       (Just hin, Just hout, _, _) <-
         createProcess (proc binary params) { std_out = CreatePipe, std_in = CreatePipe };
       hSetBuffering hin LineBuffering;
       hSetBuffering hout LineBuffering;
       next_output_plain hout;
       return (hin, hout);
    });

m_in = fst m_in_out;
m_out = snd m_in_out;

drop_output_eq :: Handle -> IO ();
drop_output_eq hout = do {
  x <- hGetChar hout;
  if x == '=' then return () else drop_output_eq hout
  };

next_output_plain :: Handle -> IO String;
next_output_plain hout = next hout "";
next hout xs = (if take 3 xs == "[nI" then (drop_output_eq hout >> return (reverse (drop 3 xs))) else 
              do {
                x <- hGetChar hout;
                next hout (x : xs)
              });
  
next_output :: () -> IO [([Integer], Integer)];
next_output _ = do {
    x <- next_output_plain m_out;
    return (m_output x);
  };

next_input :: [Integer] -> IO ();
next_input xs = hPutStrLn m_in (m_input xs) >> hFlush m_in;

factorize :: [Integer] -> [([Integer],Integer)];
factorize x = 
    unsafePerformIO (do {
    next_input x;
    res <- next_output ();
    return res;
  });

*}

definition test_extern :: "integer list \<Rightarrow> string" where
  "test_extern p = (show (map (\<lambda> (f,i). (poly_of_list (map int_of_integer f), int_of_integer i)) (external_factorization p)))" 

code_reserved Haskell Mathematica

code_printing
  constant external_factorization \<rightharpoonup> (Haskell) "Mathematica.factorize"

export_code test_intern test_extern in Haskell module_name "Factorize" file "~/Code"
 
end
