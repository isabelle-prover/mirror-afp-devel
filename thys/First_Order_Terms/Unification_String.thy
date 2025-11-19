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

abbreviation (input) x_var :: "string \<Rightarrow> string" where "x_var \<equiv> Cons (CHR ''x'')"
abbreviation (input) y_var :: "string \<Rightarrow> string" where "y_var \<equiv> Cons (CHR ''y'')"
abbreviation (input) z_var :: "string \<Rightarrow> string" where "z_var \<equiv> Cons (CHR ''z'')"

text \<open>Here, only the t-term is renamed.\<close>
lemma mgu_var_disjoint_right_string:
  fixes s t :: "('f, string) term" and \<sigma> \<tau> :: "('f, string) subst"
  assumes s: "vars_term s \<subseteq> range x_var \<union> range z_var"
    and id: "s \<cdot> \<sigma> = t \<cdot> \<tau>"
  shows "\<exists> \<mu> \<delta>. mgu s (map_vars_term y_var t) = Some \<mu> \<and>
    s \<cdot> \<sigma> = s \<cdot> \<mu> \<cdot> \<delta> \<and> (\<forall>t::('f, string) term. t \<cdot> \<tau> = map_vars_term y_var t \<cdot> \<mu> \<cdot> \<delta>) \<and>
    (\<forall>x \<in> range x_var \<union> range z_var. \<sigma> x = \<mu> x \<cdot> \<delta>)"
proof -
  have inj: "inj y_var" unfolding inj_on_def by simp
  show ?thesis
    by (rule mgu_var_disjoint_right[OF s inj _ id], auto)
qed

end