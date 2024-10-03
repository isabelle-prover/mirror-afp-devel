theory PNT_Notation
imports
  "Prime_Number_Theorem.Prime_Counting_Functions"
begin

definition "PNT_const_C\<^sub>1 \<equiv> 1 / 952320 :: real"

abbreviation nat_powr
  (infixr \<open>nat'_powr\<close> 80)
where
  "n nat_powr x \<equiv> (of_nat n) powr x"

bundle pnt_syntax
begin
notation PNT_const_C\<^sub>1 (\<open>C\<^sub>1\<close>)
notation norm (\<open>\<parallel>_\<parallel>\<close>)
notation Suc (\<open>_\<^sub>+\<close> [101] 100)
end

bundle no_pnt_syntax
begin
no_notation PNT_const_C\<^sub>1 (\<open>C\<^sub>1\<close>)
no_notation norm (\<open>\<parallel>_\<parallel>\<close>)
no_notation Suc (\<open>_\<^sub>+\<close> [101] 100)
end

end
