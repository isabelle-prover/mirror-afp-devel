section \<open>Axiom of Choice\<close>

theory Axiom_Of_Choice
  imports Coproduct
begin

text \<open>The two definitions below correspond to Definition 2.7.1 in Halvorson.\<close>
definition section_of :: "cfunc \<Rightarrow> cfunc \<Rightarrow> bool" (infix "sectionof" 90)
  where "s sectionof f \<longleftrightarrow> s : codomain f \<rightarrow> domain f \<and> f \<circ>\<^sub>c s = id (codomain f)"

definition split_epimorphism :: "cfunc \<Rightarrow> bool"
  where "split_epimorphism f \<longleftrightarrow> (\<exists> s.  s : codomain f \<rightarrow> domain f \<and> f \<circ>\<^sub>c s = id (codomain f))"

lemma split_epimorphism_def2: 
  assumes f_type: "f : X \<rightarrow> Y"
  assumes f_split_epic: "split_epimorphism f"
  shows "\<exists> s. (f \<circ>\<^sub>c s = id Y) \<and> (s: Y \<rightarrow> X)"
  using cfunc_type_def f_split_epic f_type split_epimorphism_def by auto

lemma sections_define_splits:
  assumes "s sectionof f"
  assumes "s : Y \<rightarrow> X"
  shows "f : X \<rightarrow> Y \<and> split_epimorphism(f)"
  using assms cfunc_type_def section_of_def split_epimorphism_def by auto

text \<open>The axiomatization below corresponds to Axiom 11 (Axiom of Choice) in Halvorson.\<close>
axiomatization
  where
  axiom_of_choice: "epimorphism f \<longrightarrow> (\<exists> g . g sectionof f)"

lemma epis_give_monos:  
  assumes f_type: "f : X \<rightarrow> Y"
  assumes f_epi: "epimorphism f"
  shows "\<exists>g. g: Y \<rightarrow> X \<and> monomorphism g \<and> f \<circ>\<^sub>c g = id Y"
  using assms  
  by (typecheck_cfuncs_prems, metis axiom_of_choice cfunc_type_def comp_monic_imp_monic f_epi id_isomorphism iso_imp_epi_and_monic section_of_def)

corollary epis_are_split:
  assumes f_type: "f : X \<rightarrow> Y"
  assumes f_epi: "epimorphism f"
  shows "split_epimorphism f"
  using epis_give_monos cfunc_type_def  f_epi split_epimorphism_def by blast

text \<open>The lemma below corresponds to Proposition 2.6.8 in Halvorson.\<close>
lemma monos_give_epis:
  assumes f_type[type_rule]: "f : X \<rightarrow> Y"
  assumes f_mono: "monomorphism f"
  assumes X_nonempty: "nonempty X"
  shows "\<exists>g. g: Y \<rightarrow> X \<and> epimorphism g \<and> g \<circ>\<^sub>c f = id X"
proof -
  obtain g m E where g_type[type_rule]: "g : X \<rightarrow> E" and m_type[type_rule]: "m : E \<rightarrow> Y" and
      g_epi: "epimorphism g" and m_mono[type_rule]: "monomorphism m" and f_eq: "f = m \<circ>\<^sub>c g"
    using epi_monic_factorization2 f_type by blast

  have g_mono: "monomorphism g"
  proof (typecheck_cfuncs, unfold monomorphism_def3, clarify)
    fix x y A
    assume x_type[type_rule]: "x : A \<rightarrow> X" and y_type[type_rule]: "y : A \<rightarrow> X"
    assume "g \<circ>\<^sub>c x = g \<circ>\<^sub>c y"
    then have "(m \<circ>\<^sub>c g) \<circ>\<^sub>c x = (m \<circ>\<^sub>c g) \<circ>\<^sub>c y"
      by (typecheck_cfuncs, smt comp_associative2)
    then have "f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"
      unfolding f_eq by auto
    then show "x = y"
      using f_mono f_type monomorphism_def2 x_type y_type by blast
  qed

  have g_iso: "isomorphism g"
    by (simp add: epi_mon_is_iso g_epi g_mono)
  then obtain g_inv where g_inv_type[type_rule]: "g_inv : E \<rightarrow> X" and
      g_g_inv: "g \<circ>\<^sub>c g_inv = id E" and g_inv_g: "g_inv \<circ>\<^sub>c g = id X"
    using cfunc_type_def g_type isomorphism_def by auto

  obtain x where x_type[type_rule]: "x \<in>\<^sub>c X"
    using X_nonempty nonempty_def by blast

  show "\<exists>g. g: Y \<rightarrow> X \<and> epimorphism g \<and> g \<circ>\<^sub>c f = id\<^sub>c X"
  proof (intro exI[where x="(g_inv \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (E, m)\<^esub>)) \<circ>\<^sub>c try_cast m"], safe, typecheck_cfuncs)
    have func_f_elem_eq: "\<And> y. y \<in>\<^sub>c X \<Longrightarrow> (g_inv \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (E, m)\<^esub>) \<circ>\<^sub>c try_cast m) \<circ>\<^sub>c f \<circ>\<^sub>c y = y"
    proof -
      fix y
      assume y_type[type_rule]: "y \<in>\<^sub>c X"

      have "(g_inv \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (E, m)\<^esub>) \<circ>\<^sub>c try_cast m) \<circ>\<^sub>c f \<circ>\<^sub>c y
          = g_inv \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (E, m)\<^esub>) \<circ>\<^sub>c (try_cast m \<circ>\<^sub>c m) \<circ>\<^sub>c g \<circ>\<^sub>c y"
        unfolding f_eq by (typecheck_cfuncs, smt comp_associative2)
      also have "... = (g_inv \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (E, m)\<^esub>) \<circ>\<^sub>c left_coproj E (Y \<setminus> (E,m))) \<circ>\<^sub>c g \<circ>\<^sub>c y"
        by (typecheck_cfuncs, smt comp_associative2 m_mono try_cast_m_m)
      also have "... = (g_inv \<circ>\<^sub>c g) \<circ>\<^sub>c y"
        by (typecheck_cfuncs, simp add: comp_associative2 left_coproj_cfunc_coprod)
      also have "... = y"
        by (typecheck_cfuncs, simp add: g_inv_g id_left_unit2)
      finally show "(g_inv \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (E, m)\<^esub>) \<circ>\<^sub>c try_cast m) \<circ>\<^sub>c f \<circ>\<^sub>c y = y".
    qed
    show "epimorphism (g_inv \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (E, m)\<^esub>) \<circ>\<^sub>c try_cast m)"
    proof (rule surjective_is_epimorphism, etcs_subst surjective_def2, clarify)
      fix y
      assume y_type[type_rule]: "y \<in>\<^sub>c X"
      show "\<exists>xa. xa \<in>\<^sub>c Y \<and> (g_inv \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (E, m)\<^esub>) \<circ>\<^sub>c try_cast m) \<circ>\<^sub>c xa = y"
        by (rule exI[where x="f \<circ>\<^sub>c y"], typecheck_cfuncs, smt func_f_elem_eq)
    qed
    show "(g_inv \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (E, m)\<^esub>) \<circ>\<^sub>c try_cast m) \<circ>\<^sub>c f = id\<^sub>c X"
      by (insert comp_associative2 func_f_elem_eq id_left_unit2, typecheck_cfuncs, rule one_separator, auto)
  qed
qed

text \<open>The lemma below corresponds to Exercise 2.7.2(i) in Halvorson.\<close>
lemma split_epis_are_regular: 
  assumes f_type[type_rule]: "f : X \<rightarrow> Y"
  assumes "split_epimorphism f"
  shows "regular_epimorphism f"
proof - 
  obtain s where s_type[type_rule]: "s : Y \<rightarrow> X" and s_splits:  "f \<circ>\<^sub>c s = id Y"
    by (meson assms(2) f_type split_epimorphism_def2)
  then have "coequalizer Y f (s \<circ>\<^sub>c f) (id X)"
    unfolding coequalizer_def 
    by (typecheck_cfuncs, smt (verit, del_insts) comp_associative2 comp_type id_left_unit2 id_right_unit2 s_splits)
  then show ?thesis
    using assms coequalizer_is_epimorphism epimorphisms_are_regular by blast
qed

text \<open>The lemma below corresponds to Exercise 2.7.2(ii) in Halvorson.\<close>
lemma sections_are_regular_monos: 
  assumes s_type:  "s : Y \<rightarrow> X"
  assumes "s sectionof f"
  shows "regular_monomorphism s"
proof -   
  have "coequalizer Y f (s \<circ>\<^sub>c f) (id X)"
    unfolding coequalizer_def 
    by (rule exI[where x="X"], intro exI[where x="X"], typecheck_cfuncs,
        smt (z3) assms cfunc_type_def comp_associative2 comp_type id_left_unit id_right_unit2 section_of_def)
  then show ?thesis
    by (metis assms(2) cfunc_type_def comp_monic_imp_monic' id_isomorphism iso_imp_epi_and_monic mono_is_regmono section_of_def)
qed

end