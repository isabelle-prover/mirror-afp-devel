(*
    Authors:    Sebastiaan Joosten
                René Thiemann
*)
subsection \<open>A Haskell Interface to the FPLLL-Solver\<close>

theory FPLLL_Solver
  imports LLL_Certification
begin

text \<open>We define @{const external_lll_solver} via an invocation of the fplll solver.
  For eta we use the default value of fplll, and delta is chosen so that 
  the required precision of alpha will be guaranteed. We use the command-line
  option -bvu in order to get the witnesses that are required for certification.\<close>

text \<open>Warning: Since we only define a Haskell binding for FPLLL, 
  the target languages do no longer evaluate to the same results on @{const short_vector_hybrid}!\<close>

code_printing
  code_module "FPLLL_Solver" \<rightharpoonup> (Haskell) \<open>
import System.IO.Unsafe (unsafePerformIO);
import System.IO (stderr,hPutStrLn,hPutStr);
import System.Process (readProcessWithExitCode);
import GHC.IO.Exception (ExitCode(ExitSuccess));
import Data.Char (isNumber, isSpace);
import Data.List (intercalate);

fplll_command :: String;
fplll_command = "fplll";

default_eta :: Double;
default_eta = 0.51;

alpha_to_delta :: (Integer,Integer) -> Double;
alpha_to_delta (num,denom) = (fromIntegral denom / fromIntegral num) + 
  (default_eta * default_eta);

showrow :: [Integer] -> String;
showrow rowA = "["++ intercalate " " (map show rowA) ++ "]";
showmat :: [[Integer]] -> String;
showmat matA = "["++ intercalate "\n " (map showrow matA) ++"]";


fplll_solver :: (Integer,Integer) -> [[Integer]] -> ([[Integer]],([[Integer]],[[Integer]]));
fplll_solver alpha in_mat = unsafePerformIO $ do {
  (code,res,err) <- readProcessWithExitCode fplll_command ["-e", show default_eta, "-d", show (alpha_to_delta alpha), "-of", "bvu"] (showmat in_mat);
  if code == ExitSuccess && err == ""
    then parseRes res
    else hPutStr stderr err >> fail_to_execute }
 where {
   parseMat ('[':as) = do {
     rem0 <- parseSpaces as;
     (rows,rem1) <- parseRows rem0;
     case rem1 of
       ']':rem2 -> do {
         rem3 <- parseSpaces rem2;
         return (rows,rem3)
         };
       _ -> abort$ "Expecting closing ']' while parsing a matrix.\n"
       };
   parseMat _ = abort "Expecting opening '[' while parsing a matrix";
   parseRows ('[':rem0) = do {
     rem1 <- parseSpaces rem0;
     (nums,rem2)<-parseNums rem1;
     case rem2 of
       ']':rem3 -> do { rem4 <- parseSpaces rem3;
                        (rows,rem5) <- parseRows rem4;
                        return (map read nums:rows,rem5) }
       _ -> abort$ "Expecting closing ']' while parsing a row\n" ++ rem2
       };
   parseRows x = return ([],x);
   parseNums o@(a:rem0) =
     if isNumber a || a == '-' then do {
       (num,rem1) <- parseNum rem0;
       rem2 <- parseSpaces rem1;
       (nums,rem3) <- parseNums rem2;
       return ((a:num):nums,rem3) }
     else if isSpace a then do {
       rem1 <- parseSpaces rem0;
       parseNums rem1}
     else return ([],o);
   parseNums [] = return ([],[]);
   parseNum o@(a:rem0) =
     if isNumber a then do {
       (num,rem1) <- parseNum rem0;
       return (a:num,rem1) 
       }
     else return ([],o);
   parseNum o = return ([],o);
   parseSpaces o@(a:as) = if isSpace a then parseSpaces as else return o;
   parseSpaces [] = return [];
   parseRes :: String -> IO ([[Integer]], ([[Integer]], [[Integer]]));
   parseRes res = do {
     rem0 <- parseSpaces res;
     if length rem0 <= 0
       then default_answer
       else do {
         (m1,rem1) <- parseMat rem0;
         (m2,rem2) <- parseMat rem1;
         (m3,rem3) <- parseMat rem2;
          if length rem3 > 0
            then abort "Unexpected output after parsing three matrices."
            else return (m1,(m2,m3))
            }
        };
   fail_to_execute = seq sendError default_answer;
   
   default_answer = -- not small enough, but it'll be accepted
     return (in_mat,(id_ofsize (length in_mat),id_ofsize (length in_mat)));
   abort str = error$ "Runtime exception in parsing fplll output:\n"++str;
   };
   

sendError :: (); -- bad trick using unsafeIO to make this error only appear once. I believe this is OK since the error is non-critical and the 'only appear once' is non-critical too.
sendError = unsafePerformIO $ do {
  hPutStrLn stderr "--- WARNING ---";
  hPutStrLn stderr "Failed to run fplll.";
  hPutStrLn stderr "To remove this warning, either:";
  hPutStrLn stderr "  - install fplll and ensure it is in your path.";
  hPutStrLn stderr "  - create an executable fplll that always returns successfully without generating output.";
  hPutStrLn stderr "Installing fplll correctly helps to reduce time spent verifying your certificate.";
  hPutStrLn stderr "--- END OF WARNING ---"
  };

id_ofsize :: Int -> [[Integer]];
id_ofsize n = [[if i == j then 1 else 0 | j <- [0..n-1]] | i <- [0..n-1]];
\<close>

code_reserved Haskell FPLLL_Solver fplll_solver

code_printing
  constant external_lll_solver \<rightharpoonup> (Haskell) "FPLLL'_Solver.fplll'_solver"
| constant enable_external_lll_solver \<rightharpoonup> (Haskell) "True"

text \<open>Note that since we only enabled the external LLL solver for Haskell, the result of 
  @{const short_vector_hybrid} will usually differ when executed in Haskell in
  comparison to any of the other target languages. For instance, consider the 
  invocation of:\<close>

value (code) "short_vector_test_hybrid [[1,4903,4902], [0,39023,0], [0,0,39023]]" 

text \<open>The above value-command evaluates the expression in Eval/SML to 77714 (by computing
  a short vector solely by the verified @{const short_vector} algorithm, whereas
  the generated Haskell-code via the external LLL solver yields 60414!\<close>

(* export_code short_vector_test_hybrid in Haskell module_name LLL file "~/Code" *)
end