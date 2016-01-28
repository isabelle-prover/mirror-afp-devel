(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Improved Code Equations\<close>

text \<open>This theory contains improved code equations for certain algorithms.\<close>

theory Improved_Code_Equations
imports 
  "~~/src/HOL/Library/Polynomial"
  Code_Numeral 
  Binomial
begin

subsection \<open>@{const divmod_integer}.\<close>

text \<open>We improve @{thm divmod_integer_code} by deleting @{const sgn}-expressions.\<close>

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

subsection \<open>@{const Divides.divmod_nat}.\<close>
text \<open>We implement @{const Divides.divmod_nat} via @{const divmod_integer}
  instead of invoking both division and modulo separately, 
  and we further simplify the case-analysis which is
  performed in @{thm divmod_integer_code''}.\<close>

context
includes natural.lifting integer.lifting
begin

lemma divmod_nat_code: "Divides.divmod_nat m n = map_prod nat_of_integer nat_of_integer 
  (divmod_integer (integer_of_nat m) (integer_of_nat n))"
  unfolding divmod_nat_div_mod divmod_integer_def map_prod_def split prod.simps
proof 
  show "m div n = nat_of_integer
     (integer_of_nat m div integer_of_nat n)"
    by (transfer, simp add: nat_div_distrib)
  show "m mod n = nat_of_integer
     (integer_of_nat m mod integer_of_nat n)"
    by (transfer, simp add: nat_mod_distrib)
qed
end

lemma int_of_nat_gt_zero: "integer_of_nat m > 0 \<longleftrightarrow> integer_of_nat m \<noteq> 0"
  using integer_of_nat_eq_of_nat by auto

lemma divmod_nat_code'[code]: "Divides.divmod_nat m n = (
  let k = integer_of_nat m; l = integer_of_nat n
  in map_prod nat_of_integer nat_of_integer
  (if k = 0 then (0, 0)
    else if l = 0 then (0,k) else
            divmod_abs' k l))"
  unfolding divmod_nat_code Let_def divmod_integer_code'' 
  by (simp split: if_splits add: int_of_nat_gt_zero)

subsection \<open>@{const pdivmod}.\<close>

text \<open>We improve @{thm pdivmod_fold_coeffs} by only doing one division.\<close>

lemma pdivmod_fold_coeffs_code[code]: "pdivmod p q = (if q = 0 then (0, p)
    else let n = degree q; x = inverse (coeff q n) 
    in fold_coeffs (\<lambda>a (s, r).
      let ar = pCons a r; b = coeff ar n * x
      in (pCons b s, ar - smult b q)
   ) p (0, 0))"
   unfolding pdivmod_fold_coeffs by (simp add: Let_def divide_inverse)

subsection \<open>@{const binomial}\<close>

lemma binomial_code[code]:
  "n choose k = (if k \<le> n then fact n div (fact k * fact (n - k)) else 0)"
  using binomial_eq_0[of n k] binomial_altdef_nat[of k n] by simp

end
