module Mathematica(mathematica_oracle) where {

-- factorization oracle via Mathematica
--
-- in order to include the oracle into the generated code, one has to 
-- replace the definition of "external_factorization_main" in the
-- generated code by the following two lines
--
--    import Mathematica;
--    external_factorization_main = mathematica_oracle; 
-- 
-- one might also need to adapt the call to Mathematica depending
-- on the installation of Mathematica


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
   "Fs := Map[First, Facts]; " ++                    -- since input is assumed to be square-free, drop exponents
   "Outp := Map[Function[q, CoefficientList[q, x]], Fs]; " ++   -- convert polynomials into coefficient lists
   "Outp";                                           -- and print result

change_braces :: String -> String -> String -> String;
change_braces [o1,c1] [o2,c2] = map (\ c -> if c == o1 then o2 else if c == c1 then c2 else c);

-- input which is send to Mathematica
m_input :: [Integer] -> String;
m_input p = bef ++ change_braces "[]" "{}" (show p) ++ aft;

-- parsing output from Mathematica
m_output :: String -> [[Integer]];
m_output xs = let
  ys = dropWhile (\ c -> c /= '=') xs;
  zs = filter (\ c -> (c >= '0' && c <= '9') || c `elem` ",-{}") ys;
  fact_list = read (change_braces "{}" "[]" zs);
  const_parts = filter (\ f -> length f == 1) fact_list;
  c = foldr (\ x p -> p * head x) 1 const_parts; 
  other_parts = filter (\ f -> length f /= 1) fact_list;
  in if c == 1 then other_parts else 
     if other_parts == [] then [[c]] else
     map ((*) c) (head other_parts) : tail other_parts;

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
  
next_output :: () -> IO [[Integer]];
next_output _ = do {
    x <- next_output_plain m_out;
    return (m_output x);
  };

next_input :: [Integer] -> IO ();
next_input xs = hPutStrLn m_in (m_input xs) >> hFlush m_in;

mathematica_oracle :: [Integer] -> [[Integer]];
mathematica_oracle x = 
    unsafePerformIO (do {
    -- putStr "<" >> hFlush stdout;
    next_input x;
    res <- next_output ();
    -- putStr ">" >> hFlush stdout;
    return res;
  });

}
