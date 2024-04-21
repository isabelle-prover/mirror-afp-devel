\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Composing Functions\<close>
theory Binary_Relations_Function_Composition
  imports
    Binary_Relations_Clean_Function
    Restricted_Equality
begin

lemma dep_bin_rel_eval_rel_comp_if_dep_bin_rel_if_crel_dep_fun:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  and "\<And>x. A x \<Longrightarrow> ({\<Sum>}y : B x. C x y) R'"
  shows "({\<Sum>}x : A. C x (R`x)) (R \<circ>\<circ> R')"
  using assms by force

lemma crel_dep_fun_eval_rel_comp_if_rel_dep_fun_if_crel_dep_fun:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  and "\<And>x. A x \<Longrightarrow> ((y : B x) \<rightarrow> C x y) R'"
  shows "((x : A) \<rightarrow>\<^sub>c C x (R`x)) (R \<circ>\<circ> R')"
proof (intro crel_dep_funI' dep_bin_relI
  (*TODO: should be solved by some type-checking automation*)
  mono_left_total_on_comp[THEN dep_mono_wrt_predD, THEN mono_wrt_predD]
  mono_right_unique_on_comp[THEN dep_mono_wrt_predD, THEN mono_wrt_predD])
  from assms show "left_total_on (in_codom R\<restriction>\<^bsub>A\<^esub>) R'" by force
  from assms show "right_unique_on (in_codom R\<restriction>\<^bsub>A\<^esub>) R'" by (fast dest: right_unique_onD)
qed (use assms in \<open>auto elim: rel_dep_fun_relE crel_dep_fun_relE\<close>)

lemma rel_comp_eval_eq_if_rel_dep_fun_if_crel_dep_funI [simp]:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  and "\<And>x. A x \<Longrightarrow> ((y : B x) \<rightarrow> C x y) R'"
  and "A x"
  shows "(R \<circ>\<circ> R')`x = R'`(R`x)"
proof (rule eval_eq_if_right_unique_onI)
  from assms have "((x : A) \<rightarrow>\<^sub>c C x (R`x)) (R \<circ>\<circ> R')"
    by (intro crel_dep_fun_eval_rel_comp_if_rel_dep_fun_if_crel_dep_fun) auto
  then show "right_unique_on A (R \<circ>\<circ> R')" by blast
  from assms show "(R \<circ>\<circ> R') x (R'`(R`x))" by (blast intro: rel_eval_if_rel_dep_funI)
qed (fact assms)

lemma eq_restrict_comp_eq_if_crel_dep_fun [simp]:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  shows "(=\<^bsub>A\<^esub>) \<circ>\<circ> R = R"
  using assms by force

lemma comp_eq_restrict_if_crel_dep_fun [simp]:
  assumes "(A \<rightarrow>\<^sub>c B) R"
  shows "R \<circ>\<circ> (=\<^bsub>B\<^esub>) = R"
  using assms by force

end
