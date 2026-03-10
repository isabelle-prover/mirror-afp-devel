theory Weak_Typing_Magma
  imports 
    Weak_Typing
    Abstract_Substitution.Natural_Magma
begin

locale weakly_welltyped_magma_lifting = weakly_welltyped_lifting + natural_magma
begin

lemma weakly_welltyped_add [simp]:
  "weakly_welltyped (add l C) \<longleftrightarrow> sub_weakly_welltyped l \<and> weakly_welltyped C"
  unfolding weakly_welltyped_def
  by auto

lemma weakly_welltyped_plus [simp]:
  "weakly_welltyped (plus expr expr') \<longleftrightarrow>
   weakly_welltyped expr \<and> weakly_welltyped expr'"
  unfolding weakly_welltyped_def
  by auto

end

locale weakly_welltyped_magma_with_empty_lifting = 
  weakly_welltyped_magma_lifting + natural_magma_with_empty
begin

lemma weakly_welltyped_empty [intro]: "weakly_welltyped empty"
  unfolding weakly_welltyped_def
  by simp

end

end
