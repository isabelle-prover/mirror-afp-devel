section {* Optimizations for Code Integer *}
theory Optimize_Integer
imports
  Complex_Main
  "~~/src/HOL/Library/Code_Target_Numeral"
begin

text {* TODO: Missing? code post rule? *}

lemma [code_post]: "int_of_integer (- 1) = - 1"
  by simp

text {* shallowly embed log and power *}

definition log2::"int \<Rightarrow> int"
  where "log2 a = floor (log 2 (of_int a))"

context includes integer.lifting begin

lift_definition log2_integer :: "integer \<Rightarrow> integer"
  is "log2 :: int \<Rightarrow> int"
  .

end

lemma [code]: "log2 (int_of_integer a) = int_of_integer (log2_integer a)"
  by (simp add: log2_integer.rep_eq)

code_printing
  constant "log2_integer :: integer \<Rightarrow> _" \<rightharpoonup>
    (SML) "IntInf.log2"

definition power_int::"int \<Rightarrow> int \<Rightarrow> int"
  where "power_int a b = a ^ (nat b)"

context includes integer.lifting begin

lift_definition power_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer"
  is "power_int :: int \<Rightarrow> int \<Rightarrow> int"
  .

end

code_printing
  constant "power_integer :: integer \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
    (SML) "IntInf.pow ((_), (_))"

lemma [code]: "power_int (int_of_integer a) (int_of_integer b) = int_of_integer (power_integer a b)"
  by (simp add: power_integer.rep_eq)

end

