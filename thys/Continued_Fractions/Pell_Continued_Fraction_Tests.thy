(*
  File:     Continued_Fractions/Pell_Continued_Fraction_Tests.thy
  Author:   Manuel Eberl, University of Innsbruck
*)
section \<open>Tests for Continued Fractions of Square Roots and Pell's Equation\<close>
theory Pell_Continued_Fraction_Tests
imports
  Pell.Efficient_Discrete_Sqrt
  "HOL-Library.Code_Lazy"
  "HOL-Library.Code_Target_Numeral"
  Pell_Continued_Fraction
  Pell_Lifting
begin

code_lazy_type stream

(* TODO Move *)
lemma lnth_code [code]:
 "lnth xs 0 = (if lnull xs then undefined (0 :: nat) else lhd xs)"
 "lnth xs (Suc n) = (if lnull xs then undefined (Suc n) else lnth (ltl xs) n)"
  by (auto simp: lnth.simps split: llist.splits)

value "let c = sqrt_cfrac 1339 in map (cfrac_nth c) [0..<30]"


fun arg_max_list where
  "arg_max_list _ [] = undefined"
| "arg_max_list f (x # xs) = 
     foldl (\<lambda>(x, y) x'. let y' = f x' in if y' > y then (x', y') else (x, y)) (x, f x) xs"


value [code] "sqrt_cfrac_info 17"
value [code] "sqrt_cfrac_info 1339"
value [code] "sqrt_cfrac_info 121"
value [code] "sqrt_nat_period_length 410286423278424"

text \<open>
  For which number $D < 100000$ does $\sqrt{D}$ have the longest period?
\<close>
value [code] "arg_max_list sqrt_nat_period_length [0..<100000]"


subsection \<open>Fundamental solutions of Pell's equation\<close>

value [code] "pell.fund_sol 12"
value [code] "pell.fund_sol 13"
value [code] "pell.fund_sol 61"
value [code] "pell.fund_sol 661"
value [code] "pell.fund_sol 6661"
value [code] "pell.fund_sol 4729494"

text \<open>
  Project Euler problem \#66:
  For which $D < 1000$ does Pell's equation have the largest fundamental solution?
\<close>

value [code] "arg_max_list (fst \<circ> find_fund_sol) [0..<1001]"


text \<open>
  The same for $D < 100000$:
\<close>

value [code] "arg_max_list (fst \<circ> find_fund_sol) [0..<100000]"


text \<open>
  The solution to the next example, which is at the core of Archimedes' cattle problem,
  is so big that termifying the result takes extremely long.
  Therefore, we simply compute the number of decimal digits in the result instead.
\<close>

fun log10_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "log10_aux acc n =
     (if n \<ge> 10000000000 then log10_aux (acc + 10) (n div 10000000000)
      else if n = 0 then acc else log10_aux (Suc acc) (n div 10))"

definition log10 where "log10 = log10_aux 0"

value [code] "map_prod log10 log10 (pell.fund_sol 410286423278424)"

text \<open>
  Factoring out the square factor \<open>9314\<^sup>2\<close> does yield a significant speed-up in this case:
\<close>
value [code] "map_prod log10 log10 (find_fund_sol_fast 410286423278424)"


subsection \<open>Tests for other operations\<close>

value [code] "pell.nth_solution 13 100"
value [code] "pell.nth_solution 4729494 3"

value [code] "stake 10 (pell_solutions 13)"
value [code] "stake 10 (pell_solutions 61)"

value [code] "pell.nth_solution 23 8"

end