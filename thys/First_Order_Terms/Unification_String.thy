subsection \<open>A variable disjoint unification algorithm for terms with string variables\<close>

theory Unification_String
imports
  Unification
  Renaming2_String
begin
definition "mgu_vd_string = mgu_vd string_rename" 

lemma mgu_vd_string_code[code]: "mgu_vd_string = mgu_var_disjoint_generic (Cons (CHR ''x'')) (Cons (CHR ''y''))" 
  unfolding mgu_vd_string_def mgu_vd_def
  by (transfer, auto)

lemma mgu_vd_string_sound: 
  "mgu_vd_string s t = Some (\<gamma>1, \<gamma>2) \<Longrightarrow> s \<cdot> \<gamma>1 = t \<cdot> \<gamma>2"
  unfolding mgu_vd_string_def by (rule mgu_vd_sound)

lemma mgu_vd_string_complete:
  fixes \<sigma> :: "('f, string) subst" and \<tau> :: "('f, string) subst" 
  assumes "s \<cdot> \<sigma> = t \<cdot> \<tau>"
  shows "\<exists>\<mu>1 \<mu>2 \<delta>. mgu_vd_string s t = Some (\<mu>1, \<mu>2) \<and>
    \<sigma> = \<mu>1 \<circ>\<^sub>s \<delta> \<and>
    \<tau> = \<mu>2 \<circ>\<^sub>s \<delta> \<and>
    s \<cdot> \<mu>1 = t \<cdot> \<mu>2"
  unfolding mgu_vd_string_def
  by (rule mgu_vd_complete[OF assms])
end