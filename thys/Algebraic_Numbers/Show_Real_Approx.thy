(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Show for Real (Algebraic) Numbers -- Approximate Representation\<close>

text \<open>We implement the show-function for real (algebraic) numbers by calculating the
  number precisely for three digits after the comma.\<close>
theory Show_Real_Approx
imports
  Show_Real_Alg
  "$AFP/Show/Show_Instances"
begin

defs show_real_alg[code]: "show_real_alg x \<equiv> let 
  x1000 = floor (1000 * x);
  (bef,aft) = divmod_int x1000 1000;
  a' = show aft;
  a = replicate (3-length a') (CHR ''0'') @ a'
  in 
  '' ~'' @ show bef @ ''.'' @ a"

end