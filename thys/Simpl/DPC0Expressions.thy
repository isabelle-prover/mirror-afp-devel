header {* SHORTENED! Parallel expressions in DPC/Hoare. *}

theory DPC0Expressions imports Main begin

consts
  p_not :: "bool list => bool list"

syntax (xsymbols)
  p_not :: "bool list => bool list"		("\<not>\<^sub>p")

defs
  p_not_def: "p_not == map Not"


constdefs
  elem_wise :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list"
  "elem_wise f xs ys == map (\<lambda> (x, y). f x y) (zip xs ys)"

consts
  p_and  :: "bool list => bool list => bool list"	(infixl "pand"  35)

syntax (xsymbols)
  p_and  :: "bool list => bool list => bool list"	(infixl "\<and>\<^sub>p"  35)

defs
  p_and_def:  "p_and  == elem_wise op&"

end
