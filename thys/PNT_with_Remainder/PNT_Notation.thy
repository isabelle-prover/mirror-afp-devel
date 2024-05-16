theory PNT_Notation
imports
  "Prime_Number_Theorem.Prime_Counting_Functions"
begin

definition "PNT_const_C\<^sub>1 \<equiv> 1 / 952320 :: real"

abbreviation nat_powr
  (infixr "nat'_powr" 80)
where
  "n nat_powr x \<equiv> (of_nat n) powr x"

bundle pnt_notation
begin
notation PNT_const_C\<^sub>1 ("C\<^sub>1")
notation norm ("\<parallel>_\<parallel>")
notation Suc ("_\<^sub>+" [101] 100)
end

bundle no_pnt_notation
begin
no_notation PNT_const_C\<^sub>1 ("C\<^sub>1")
no_notation norm ("\<parallel>_\<parallel>")
no_notation Suc ("_\<^sub>+" [101] 100)
end

end
