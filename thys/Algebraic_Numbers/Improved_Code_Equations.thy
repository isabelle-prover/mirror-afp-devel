(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
subsection \<open>Improved Code Equations\<close>

text \<open>This theory contains improved code equations for certain algorithms.\<close>

theory Improved_Code_Equations
imports 
  "~~/src/HOL/Library/Polynomial"
  Code_Numeral
begin

subsubsection \<open>@{const divmod_integer}.\<close>

text \<open>We improve @{thm divmod_integer_code}.\<close>

(* led to an improvement of 25 % on factorization example *)
lemma divmod_integer_code': "divmod_integer k l =
  (if k = 0 then (0, 0)
    else if l > 0 then
            (if k > 0 then Code_Numeral.divmod_abs k l
             else case Code_Numeral.divmod_abs k l of (r, s) \<Rightarrow>
                  if s = 0 then (- r, 0) else (- r - 1, l - s))
    else if l = 0 then (0, k)
    else apsnd uminus
            (if k < 0 then Code_Numeral.divmod_abs k l
             else case Code_Numeral.divmod_abs k l of (r, s) \<Rightarrow>
                  if s = 0 then (- r, 0) else (- r - 1, - l - s)))"
proof -
  have [simp]: "apsnd (op * (1 :: integer)) = id" 
    by (intro ext, auto)
  show ?thesis
    unfolding divmod_integer_code 
    by (cases "l = 0"; cases "l < 0"; cases "l > 0"; auto split: prod.splits)
qed

text \<open>We guard the application of divmod-abs' with the condition @{term "x \<ge> 0 \<and> y \<ge> 0"}, 
  so that application can be ensured on non-negative values. Hence, one can drop "abs" in 
   target language setup.\<close>

definition divmod_abs' where 
  "x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> divmod_abs' x y = Code_Numeral.divmod_abs x y" 

(* led to an another 10 % improvement on factorization example *)

lemma divmod_integer_code''[code]: "divmod_integer k l =
  (if k = 0 then (0, 0)
    else if l > 0 then
            (if k > 0 then divmod_abs' k l
             else case divmod_abs' (- k) l of (r, s) \<Rightarrow>
                  if s = 0 then (- r, 0) else (- r - 1, l - s))
    else if l = 0 then (0, k)
    else apsnd uminus
            (if k < 0 then divmod_abs' (-k) (-l)
             else case divmod_abs' k (-l) of (r, s) \<Rightarrow>
                  if s = 0 then (- r, 0) else (- r - 1, - l - s)))"
   unfolding divmod_integer_code'
   by (cases "l = 0"; cases "l < 0"; cases "l > 0"; auto split: prod.splits simp: divmod_abs'_def divmod_abs_def)

code_printing
  constant divmod_abs' \<rightharpoonup>
    (SML) "IntInf.divMod/ ( _,/ _ )"
    and (OCaml) "Big'_int.quomod'_big'_int/ ( _ )/ ( _ )"
    and (Haskell) "divMod/ ( _ )/ ( _ )"
    and (Scala) "!((k: BigInt) => (l: BigInt) =>/ if (l == 0)/ (BigInt(0), k) else/ (k '/% l))"
    and (Eval) "Integer.div'_mod/ ( _ )/ ( _ )"

subsubsection \<open>@{const pdivmod}.\<close>

text \<open>We improve @{thm pdivmod_fold_coeffs} by only doing one division.\<close>

lemma pdivmod_fold_coeffs_code[code]: "pdivmod p q = (if q = 0 then (0, p)
    else let n = degree q; x = inverse (coeff q n) 
    in fold_coeffs (\<lambda>a (s, r).
      let ar = pCons a r; b = coeff ar n * x
      in (pCons b s, ar - smult b q)
   ) p (0, 0))"
   unfolding pdivmod_fold_coeffs by (simp add: Let_def divide_inverse)
 
end