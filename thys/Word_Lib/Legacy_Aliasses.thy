

section \<open>Legacy aliasses\<close>

theory Legacy_Aliasses
  imports "HOL-Library.Word"
begin

definition
  complement :: "'a :: len word \<Rightarrow> 'a word"  where
 "complement x \<equiv> NOT x"

lemma complement_mask:
  "complement (2 ^ n - 1) = NOT (mask n)"
  unfolding complement_def mask_eq_decr_exp by simp

lemmas less_def = less_eq [symmetric]
lemmas le_def = not_less [symmetric, where ?'a = nat]

end
