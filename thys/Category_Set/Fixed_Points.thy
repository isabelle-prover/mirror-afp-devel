section \<open>Fixed Points and Cantor's Theorems\<close>

theory Fixed_Points
  imports Axiom_Of_Choice Pred_Logic Cardinality
begin

text \<open>The definitions below correspond to Definition 2.6.12 in Halvorson.\<close>
definition fixed_point :: "cfunc \<Rightarrow> cfunc \<Rightarrow> bool" where
  "fixed_point a g \<longleftrightarrow> (\<exists> A. g : A \<rightarrow> A \<and> a \<in>\<^sub>c A \<and> g \<circ>\<^sub>c a = a)"
definition has_fixed_point :: "cfunc \<Rightarrow> bool" where
  "has_fixed_point g \<longleftrightarrow> (\<exists> a. fixed_point a g)"
definition fixed_point_property :: "cset \<Rightarrow> bool" where
  "fixed_point_property A \<longleftrightarrow> (\<forall> g. g : A \<rightarrow> A \<longrightarrow> has_fixed_point g)"

lemma fixed_point_def2: 
  assumes "g : A \<rightarrow> A" "a \<in>\<^sub>c A"
  shows "fixed_point a g = (g \<circ>\<^sub>c a = a)"
  unfolding fixed_point_def using assms by blast

text \<open>The lemma below corresponds to Theorem 2.6.13 in Halvorson.\<close>
lemma Lawveres_fixed_point_theorem:
  assumes p_type[type_rule]: "p : X \<rightarrow> A\<^bsup>X\<^esup>"
  assumes p_surj: "surjective p"
  shows "fixed_point_property A"
  unfolding fixed_point_property_def has_fixed_point_def
proof(clarify) 
  fix g 
  assume g_type[type_rule]: "g : A \<rightarrow> A"
  obtain \<phi> where \<phi>_def: "\<phi> = p\<^sup>\<flat>"
    by auto
  then have \<phi>_type[type_rule]: "\<phi> : X \<times>\<^sub>c X \<rightarrow> A"
    by (simp add: flat_type p_type)
  obtain f where f_def: "f = g \<circ>\<^sub>c \<phi> \<circ>\<^sub>c diagonal(X)"
    by auto
  then have f_type[type_rule]:"f : X \<rightarrow> A"
    using \<phi>_type comp_type diagonal_type f_def g_type by blast
  obtain x_f where x_f: "metafunc f = p \<circ>\<^sub>c x_f" and x_f_type[type_rule]: "x_f \<in>\<^sub>c X"
    using assms by (typecheck_cfuncs, metis p_surj surjective_def2)
  have "\<phi>\<^bsub>[-,x_f]\<^esub> = f"
  proof(etcs_rule one_separator)
    fix x 
    assume x_type[type_rule]: "x \<in>\<^sub>c X"
    have "\<phi>\<^bsub>[-,x_f]\<^esub> \<circ>\<^sub>c x = \<phi> \<circ>\<^sub>c \<langle>x, x_f\<rangle>"
      by (typecheck_cfuncs, meson right_param_on_el x_f)
    also have "... = ((eval_func A X) \<circ>\<^sub>c (id X \<times>\<^sub>f p)) \<circ>\<^sub>c \<langle>x, x_f\<rangle>"
      using assms \<phi>_def inv_transpose_func_def3 by auto
    also have "... = (eval_func A X) \<circ>\<^sub>c (id X \<times>\<^sub>f p) \<circ>\<^sub>c \<langle>x, x_f\<rangle>"
      by (typecheck_cfuncs, metis comp_associative2)
    also have "... = (eval_func A X) \<circ>\<^sub>c \<langle>id X  \<circ>\<^sub>c  x, p \<circ>\<^sub>c x_f\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod x_f by (typecheck_cfuncs, force)
    also have "... = (eval_func A X) \<circ>\<^sub>c \<langle>x, metafunc f\<rangle>"
      using id_left_unit2 x_f by (typecheck_cfuncs, auto)
    also have "... = f \<circ>\<^sub>c x"
      by (simp add: eval_lemma f_type x_type)
    finally show "\<phi>\<^bsub>[-,x_f]\<^esub> \<circ>\<^sub>c x = f \<circ>\<^sub>c x".
  qed
  then have "\<phi>\<^bsub>[-,x_f]\<^esub> \<circ>\<^sub>c x_f = g \<circ>\<^sub>c \<phi> \<circ>\<^sub>c diagonal(X) \<circ>\<^sub>c x_f"
    by (typecheck_cfuncs, smt (z3) cfunc_type_def comp_associative domain_comp f_def x_f)
  then have "\<phi> \<circ>\<^sub>c \<langle>x_f, x_f\<rangle> = g \<circ>\<^sub>c \<phi> \<circ>\<^sub>c \<langle>x_f, x_f\<rangle>"
    using  diag_on_elements right_param_on_el x_f by (typecheck_cfuncs, auto)
  then have "fixed_point (\<phi> \<circ>\<^sub>c \<langle>x_f, x_f\<rangle>) g"
    using fixed_point_def2 by (typecheck_cfuncs, auto)
  then show "\<exists>a. fixed_point a g"
    using fixed_point_def by auto
qed

text \<open>The theorem below corresponds to Theorem 2.6.14 in Halvorson.\<close>
theorem Cantors_Negative_Theorem:
  "\<nexists> s. s : X \<rightarrow> \<P> X \<and> surjective s"
proof(rule ccontr, clarify)
  fix s 
  assume s_type: "s : X \<rightarrow> \<P> X"
  assume s_surj: "surjective s"
  then have Omega_has_ffp: "fixed_point_property \<Omega>"
    using Lawveres_fixed_point_theorem powerset_def s_type by auto
  have Omega_doesnt_have_ffp: "\<not>(fixed_point_property \<Omega>)"
    unfolding fixed_point_property_def has_fixed_point_def fixed_point_def
  proof    
    assume BWOC: "\<forall>g. g : \<Omega> \<rightarrow> \<Omega> \<longrightarrow> (\<exists>a A. g : A \<rightarrow> A \<and> a \<in>\<^sub>c A \<and> g \<circ>\<^sub>c a = a)"
    have  "NOT : \<Omega> \<rightarrow> \<Omega> \<and> (\<forall>a. \<forall>A. a \<in>\<^sub>c A \<longrightarrow> NOT : A \<rightarrow> A \<longrightarrow> NOT \<circ>\<^sub>c a \<noteq> a \<or> \<not> a \<in>\<^sub>c \<Omega>)"
      by (typecheck_cfuncs, metis AND_complementary AND_idempotent OR_complementary OR_idempotent true_false_distinct)
    then have "\<exists>g. g : \<Omega> \<rightarrow> \<Omega> \<and> (\<forall>a. \<forall>A. a \<in>\<^sub>c A \<longrightarrow> g : A \<rightarrow> A \<longrightarrow> g \<circ>\<^sub>c a \<noteq> a)"
      by (metis cfunc_type_def)
    then show False
      using BWOC by presburger
  qed
  show False
    using Omega_doesnt_have_ffp Omega_has_ffp by auto
qed

text \<open>The theorem below corresponds to Exercise 2.6.15 in Halvorson.\<close>
theorem Cantors_Positive_Theorem:
  "\<exists>m. m : X \<rightarrow> \<Omega>\<^bsup>X\<^esup> \<and> injective m"
proof - 
  have eq_pred_sharp_type[type_rule]: "eq_pred X\<^sup>\<sharp> : X \<rightarrow>  \<Omega>\<^bsup>X\<^esup>"
    by typecheck_cfuncs
  have "injective(eq_pred X\<^sup>\<sharp>)"
    unfolding injective_def
  proof (clarify)
    fix x y 
    assume "x \<in>\<^sub>c domain (eq_pred X\<^sup>\<sharp>)" then have x_type[type_rule]: "x \<in>\<^sub>c X"
      using cfunc_type_def eq_pred_sharp_type by auto
    assume "y \<in>\<^sub>c domain (eq_pred X\<^sup>\<sharp>)" then have y_type[type_rule]:"y \<in>\<^sub>c X"
      using cfunc_type_def eq_pred_sharp_type by auto
    assume eq: "eq_pred X\<^sup>\<sharp> \<circ>\<^sub>c x = eq_pred X\<^sup>\<sharp> \<circ>\<^sub>c y"
    have "eq_pred X \<circ>\<^sub>c \<langle>x, x\<rangle> = eq_pred X \<circ>\<^sub>c \<langle>x, y\<rangle>"
    proof - 
      have "eq_pred X \<circ>\<^sub>c \<langle>x, x\<rangle> = ((eval_func \<Omega> X) \<circ>\<^sub>c (id X \<times>\<^sub>f (eq_pred X\<^sup>\<sharp>)) ) \<circ>\<^sub>c \<langle>x, x\<rangle>"
        using transpose_func_def by (typecheck_cfuncs, presburger)
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c (id X \<times>\<^sub>f (eq_pred X\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>x, x\<rangle>"
        by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c \<langle>id X \<circ>\<^sub>c x, (eq_pred X\<^sup>\<sharp>) \<circ>\<^sub>c x\<rangle>"
        using cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, force)
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c \<langle>id X \<circ>\<^sub>c x, (eq_pred X\<^sup>\<sharp>) \<circ>\<^sub>c y\<rangle>"
        by (simp add: eq)
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c (id X \<times>\<^sub>f (eq_pred X\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>x, y\<rangle>"
        by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
      also have "... = ((eval_func \<Omega> X) \<circ>\<^sub>c (id X \<times>\<^sub>f (eq_pred X\<^sup>\<sharp>)) ) \<circ>\<^sub>c \<langle>x, y\<rangle>"
        using comp_associative2 by (typecheck_cfuncs, blast)
      also have "... = eq_pred X \<circ>\<^sub>c \<langle>x, y\<rangle>"
        using transpose_func_def by (typecheck_cfuncs, presburger)
      finally show ?thesis.
    qed
    then show "x = y"
      by (metis eq_pred_iff_eq x_type y_type)
  qed
  then show "\<exists>m. m : X \<rightarrow> \<Omega>\<^bsup>X\<^esup> \<and> injective m"
    using eq_pred_sharp_type injective_imp_monomorphism by blast
qed

text \<open>The corollary below corresponds to Corollary 2.6.16 in Halvorson.\<close>
corollary 
  "X \<le>\<^sub>c \<P> X \<and> \<not> (X \<cong> \<P> X)"
  using Cantors_Negative_Theorem Cantors_Positive_Theorem
  unfolding is_smaller_than_def is_isomorphic_def powerset_def
  by (metis epi_is_surj injective_imp_monomorphism iso_imp_epi_and_monic)

corollary Generalized_Cantors_Positive_Theorem:
  assumes "\<not> terminal_object Y"
  assumes "\<not> initial_object Y"
  shows "X  \<le>\<^sub>c Y\<^bsup>X\<^esup>"
proof - 
  have "\<Omega> \<le>\<^sub>c Y"
    by (simp add: assms non_init_non_ter_sets)
  then have fact: "\<Omega>\<^bsup>X\<^esup> \<le>\<^sub>c  Y\<^bsup>X\<^esup>"
    by (simp add: exp_preserves_card2)
  have "X \<le>\<^sub>c \<Omega>\<^bsup>X\<^esup>"
    by (meson Cantors_Positive_Theorem CollectI injective_imp_monomorphism is_smaller_than_def)
  then show ?thesis
    using fact set_card_transitive by blast
qed

corollary Generalized_Cantors_Negative_Theorem:
  assumes "\<not> initial_object X"
  assumes "\<not> terminal_object Y"
  shows "\<nexists> s. s : X \<rightarrow> Y\<^bsup>X\<^esup> \<and> surjective s"
proof(rule ccontr, clarify) 
  fix s 
  assume s_type: "s : X \<rightarrow> Y\<^bsup>X\<^esup>"
  assume s_surj: "surjective s"
  obtain m where m_type: "m : Y\<^bsup>X\<^esup> \<rightarrow> X" and m_mono: "monomorphism(m)"
    by (meson epis_give_monos s_surj s_type surjective_is_epimorphism)
  have "nonempty X"
    using is_empty_def assms(1) iso_empty_initial no_el_iff_iso_empty nonempty_def by blast

  then have nonempty: "nonempty (\<Omega>\<^bsup>X\<^esup>)"
    using nonempty_def nonempty_to_nonempty true_func_type by blast
  show False
  proof(cases "initial_object Y")
    assume "initial_object Y"
    then have "Y\<^bsup>X\<^esup> \<cong> \<emptyset>"
      by (simp add: \<open>nonempty X\<close> empty_to_nonempty initial_iso_empty no_el_iff_iso_empty)      
    then show False
      by (meson is_empty_def assms(1) comp_type iso_empty_initial no_el_iff_iso_empty s_type) 
  next
    assume "\<not> initial_object Y"
    then have "\<Omega> \<le>\<^sub>c Y"
      by (simp add: assms(2) non_init_non_ter_sets)
    then obtain n where n_type: "n : \<Omega>\<^bsup>X\<^esup> \<rightarrow> Y\<^bsup>X\<^esup>" and n_mono: "monomorphism(n)"
      by (meson exp_preserves_card2 is_smaller_than_def)
    then have mn_type: "m \<circ>\<^sub>c n :  \<Omega>\<^bsup>X\<^esup> \<rightarrow> X"
      by (meson comp_type m_type)
    have mn_mono: "monomorphism(m \<circ>\<^sub>c n)"
      using cfunc_type_def composition_of_monic_pair_is_monic m_mono m_type n_mono n_type by presburger
    then have "\<exists>g. g: X  \<rightarrow> \<Omega>\<^bsup>X\<^esup> \<and> epimorphism(g) \<and> g \<circ>\<^sub>c (m \<circ>\<^sub>c n) = id (\<Omega>\<^bsup>X\<^esup>)"
      by (simp add: mn_type monos_give_epis nonempty)
    then show False
      by (metis Cantors_Negative_Theorem epi_is_surj powerset_def)
  qed
qed

end