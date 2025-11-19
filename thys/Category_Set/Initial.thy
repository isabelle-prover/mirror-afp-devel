section  \<open>Empty Set and Initial Objects\<close>

theory Initial
  imports Coproduct
begin

text \<open>The axiomatization below corresponds to Axiom 8 (Empty Set) in Halvorson.\<close>
axiomatization
  initial_func :: "cset \<Rightarrow> cfunc" ("\<alpha>\<^bsub>_\<^esub>" 100) and
  emptyset :: "cset" ("\<emptyset>")
where
  initial_func_type[type_rule]: "initial_func X :  \<emptyset> \<rightarrow> X" and
  initial_func_unique: "h : \<emptyset> \<rightarrow> X \<Longrightarrow> h = initial_func X" and
  emptyset_is_empty: "\<not>(x \<in>\<^sub>c \<emptyset>)"

definition initial_object :: "cset \<Rightarrow> bool" where
  "initial_object(X) \<longleftrightarrow> (\<forall> Y. \<exists>! f. f : X \<rightarrow> Y)"

lemma emptyset_is_initial:
  "initial_object(\<emptyset>)"
  using initial_func_type initial_func_unique initial_object_def by blast

lemma initial_iso_empty:
  assumes "initial_object(X)"
  shows "X \<cong> \<emptyset>"
  by (metis assms cfunc_type_def comp_type emptyset_is_empty epi_mon_is_iso initial_object_def injective_def injective_imp_monomorphism is_isomorphic_def surjective_def surjective_is_epimorphism)

text \<open>The lemma below corresponds to Exercise 2.4.6 in Halvorson.\<close>
lemma coproduct_with_empty:
  shows "X \<Coprod> \<emptyset> \<cong> X"
proof -
  have comp1: "(left_coproj X \<emptyset> \<circ>\<^sub>c (id X \<amalg> \<alpha>\<^bsub>X\<^esub>)) \<circ>\<^sub>c left_coproj X \<emptyset> = left_coproj X \<emptyset>"
  proof -
    have "(left_coproj X \<emptyset> \<circ>\<^sub>c (id X \<amalg> \<alpha>\<^bsub>X\<^esub>)) \<circ>\<^sub>c left_coproj X \<emptyset> =
            left_coproj X \<emptyset> \<circ>\<^sub>c (id X \<amalg> \<alpha>\<^bsub>X\<^esub> \<circ>\<^sub>c left_coproj X \<emptyset>)"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = left_coproj X \<emptyset> \<circ>\<^sub>c id(X)"
      by (typecheck_cfuncs, metis left_coproj_cfunc_coprod)
    also have "... = left_coproj X \<emptyset>"
      by (typecheck_cfuncs, metis id_right_unit2)
    finally show ?thesis.
  qed
  have comp2: "(left_coproj X \<emptyset> \<circ>\<^sub>c (id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>)) \<circ>\<^sub>c right_coproj X \<emptyset> = right_coproj X \<emptyset>"
  proof -
    have "((left_coproj X \<emptyset>) \<circ>\<^sub>c (id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>)) \<circ>\<^sub>c (right_coproj X \<emptyset>) = 
             (left_coproj X \<emptyset>) \<circ>\<^sub>c ((id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>) \<circ>\<^sub>c (right_coproj X \<emptyset>))"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (left_coproj X \<emptyset>) \<circ>\<^sub>c \<alpha>\<^bsub>X\<^esub>"
      by (typecheck_cfuncs, metis right_coproj_cfunc_coprod)
    also have "... = right_coproj X \<emptyset>"
      by (typecheck_cfuncs, metis initial_func_unique)
    finally show ?thesis.
  qed
  then have fact1: "(left_coproj X \<emptyset>)\<amalg>(right_coproj X \<emptyset>) \<circ>\<^sub>c left_coproj X \<emptyset> = left_coproj X \<emptyset>"
    using left_coproj_cfunc_coprod by (typecheck_cfuncs, blast)
  then have fact2: "((left_coproj X \<emptyset>)\<amalg>(right_coproj X \<emptyset>)) \<circ>\<^sub>c (right_coproj X \<emptyset>) = right_coproj X \<emptyset>"
    using right_coproj_cfunc_coprod by (typecheck_cfuncs, blast)
  then have concl: "(left_coproj X \<emptyset>) \<circ>\<^sub>c (id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>) = ((left_coproj X \<emptyset>)\<amalg>(right_coproj X \<emptyset>))"
    using cfunc_coprod_unique comp1 comp2 by (typecheck_cfuncs, blast)
  also have "... = id(X\<Coprod>\<emptyset>)"
    using cfunc_coprod_unique id_left_unit2 by (typecheck_cfuncs, auto)
  then have "isomorphism(id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>)"
    unfolding isomorphism_def 
    by (intro exI[where x="left_coproj X \<emptyset>"], typecheck_cfuncs, simp add: cfunc_type_def concl left_coproj_cfunc_coprod)
  then show "X\<Coprod>\<emptyset> \<cong> X"
    using cfunc_coprod_type id_type initial_func_type is_isomorphic_def by blast
qed

text \<open>The lemma below corresponds to Proposition 2.4.7 in Halvorson.\<close>
lemma function_to_empty_is_iso:
  assumes "f: X \<rightarrow> \<emptyset>"
  shows "isomorphism(f)"
  by (metis assms cfunc_type_def comp_type emptyset_is_empty epi_mon_is_iso injective_def injective_imp_monomorphism  surjective_def surjective_is_epimorphism)

lemma empty_prod_X:
  "\<emptyset> \<times>\<^sub>c X \<cong> \<emptyset>"
  using cfunc_type_def function_to_empty_is_iso is_isomorphic_def left_cart_proj_type by blast

lemma X_prod_empty: 
  "X \<times>\<^sub>c \<emptyset> \<cong> \<emptyset>"
  using cfunc_type_def function_to_empty_is_iso is_isomorphic_def right_cart_proj_type by blast

text \<open>The lemma below corresponds to Proposition 2.4.8 in Halvorson.\<close>
lemma no_el_iff_iso_empty:
  "is_empty X \<longleftrightarrow> X \<cong> \<emptyset>"
proof safe
  show "X \<cong> \<emptyset> \<Longrightarrow> is_empty X"
    by (meson is_empty_def comp_type emptyset_is_empty is_isomorphic_def)
next 
  assume "is_empty X"
  obtain f where f_type: "f: \<emptyset> \<rightarrow> X"
    using initial_func_type by blast
 
  have  f_inj: "injective(f)"
    using cfunc_type_def emptyset_is_empty f_type injective_def by auto
  then have f_mono: "monomorphism(f)"
    using  cfunc_type_def f_type injective_imp_monomorphism by blast
  have f_surj: "surjective(f)"
    using is_empty_def \<open>is_empty X\<close> f_type surjective_def2 by presburger
  then have epi_f: "epimorphism(f)"
    using surjective_is_epimorphism by blast
  then have iso_f: "isomorphism(f)"
    using cfunc_type_def epi_mon_is_iso f_mono f_type by blast
  then show "X \<cong> \<emptyset>"
    using f_type is_isomorphic_def isomorphic_is_symmetric by blast
qed

lemma initial_maps_mono:
  assumes "initial_object(X)"
  assumes "f : X \<rightarrow> Y"
  shows "monomorphism(f)"
  by (metis assms cfunc_type_def initial_iso_empty injective_def injective_imp_monomorphism no_el_iff_iso_empty is_empty_def)

lemma iso_empty_initial:
  assumes "X \<cong> \<emptyset>"
  shows "initial_object X"
  unfolding initial_object_def
  by (meson assms comp_type is_isomorphic_def isomorphic_is_symmetric isomorphic_is_transitive no_el_iff_iso_empty is_empty_def one_separator terminal_func_type)

lemma function_to_empty_set_is_iso:
  assumes "f: X \<rightarrow> Y"
  assumes "is_empty Y"
  shows "isomorphism f"
  by (metis assms cfunc_type_def comp_type epi_mon_is_iso injective_def injective_imp_monomorphism is_empty_def surjective_def surjective_is_epimorphism)

lemma prod_iso_to_empty_right:
  assumes "nonempty X"
  assumes "X \<times>\<^sub>c Y \<cong> \<emptyset>"
  shows "is_empty Y"
  by (metis emptyset_is_empty is_empty_def cfunc_prod_type epi_is_surj is_isomorphic_def iso_imp_epi_and_monic isomorphic_is_symmetric nonempty_def surjective_def2 assms)

lemma prod_iso_to_empty_left:
  assumes "nonempty Y"
  assumes "X \<times>\<^sub>c Y \<cong> \<emptyset>"
  shows "is_empty X"
  by (meson is_empty_def nonempty_def prod_iso_to_empty_right assms)

lemma empty_subset: "(\<emptyset>, \<alpha>\<^bsub>X\<^esub>) \<subseteq>\<^sub>c X"
  by (metis cfunc_type_def emptyset_is_empty initial_func_type injective_def injective_imp_monomorphism subobject_of_def2)

text \<open>The lemma below corresponds to Proposition 2.2.1 in Halvorson.\<close>
lemma one_has_two_subsets:
  "card ({(X,m). (X,m) \<subseteq>\<^sub>c \<one>}//{((X1,m1),(X2,m2)). X1 \<cong> X2}) = 2"
proof -
  have one_subobject: "(\<one>, id \<one>) \<subseteq>\<^sub>c \<one>"
    using element_monomorphism id_type subobject_of_def2 by blast
  have empty_subobject: "(\<emptyset>, \<alpha>\<^bsub>\<one>\<^esub>) \<subseteq>\<^sub>c \<one>"
    by (simp add: empty_subset)

  have subobject_one_or_empty: "\<And>X m. (X,m) \<subseteq>\<^sub>c \<one> \<Longrightarrow> X \<cong> \<one> \<or> X \<cong> \<emptyset>"
  proof -
    fix X m
    assume X_m_subobject: "(X, m) \<subseteq>\<^sub>c \<one>"

    obtain \<chi> where \<chi>_pullback: "is_pullback X \<one> \<one> \<Omega> (\<beta>\<^bsub>X\<^esub>) \<t> m \<chi>"
      using X_m_subobject characteristic_function_exists subobject_of_def2 by blast
    then have \<chi>_true_or_false: "\<chi> = \<t> \<or> \<chi> = \<f>"
      unfolding is_pullback_def  using true_false_only_truth_values by auto

    have true_iso_one: "\<chi> = \<t> \<Longrightarrow> X \<cong> \<one>"
    proof -
      assume \<chi>_true: "\<chi> = \<t>"
      then have "\<exists>!j. j \<in>\<^sub>c X \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c j = id\<^sub>c \<one> \<and> m \<circ>\<^sub>c j = id\<^sub>c \<one>"
        using \<chi>_pullback \<chi>_true is_pullback_def by (typecheck_cfuncs, auto)
      then show "X \<cong> \<one>"
        using single_elem_iso_one
        by (metis X_m_subobject subobject_of_def2 terminal_func_comp_elem terminal_func_unique) 
    qed

    have false_iso_one: "\<chi> = \<f> \<Longrightarrow> X \<cong> \<emptyset>"
    proof -
      assume \<chi>_false: "\<chi> = \<f>"
      have "\<nexists> x. x \<in>\<^sub>c X"
      proof clarify
        fix x
        assume x_in_X: "x \<in>\<^sub>c X"
        have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> = \<f> \<circ>\<^sub>c m"
          using \<chi>_false \<chi>_pullback is_pullback_def by auto
        then have "\<t> \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x) = \<f> \<circ>\<^sub>c (m \<circ>\<^sub>c x)"
          by (smt X_m_subobject comp_associative2 false_func_type subobject_of_def2
              terminal_func_type true_func_type x_in_X)
        then have "\<t> = \<f>"
          by (smt X_m_subobject cfunc_type_def comp_type false_func_type id_right_unit id_type
              subobject_of_def2 terminal_func_unique true_func_type x_in_X)
        then show False
          using true_false_distinct by auto
      qed
      then show "X \<cong> \<emptyset>"
        using is_empty_def \<open>\<nexists>x. x \<in>\<^sub>c X\<close> no_el_iff_iso_empty by blast
    qed

    show "X \<cong> \<one> \<or> X \<cong> \<emptyset>"
      using \<chi>_true_or_false false_iso_one true_iso_one by blast
  qed

  have classes_distinct: "{(X, m). X \<cong> \<emptyset>} \<noteq> {(X, m). X \<cong> \<one>}"
    by (metis case_prod_eta curry_case_prod emptyset_is_empty id_isomorphism id_type is_isomorphic_def mem_Collect_eq)

  have "{(X, m). (X, m) \<subseteq>\<^sub>c \<one>} // {((X1, m1), (X2, m2)). X1 \<cong> X2} = {{(X, m). X \<cong> \<emptyset>}, {(X, m). X \<cong> \<one>}}"
  proof
    show "{(X, m). (X, m) \<subseteq>\<^sub>c \<one>} // {((X1, m1), (X2, m2)). X1 \<cong> X2} \<subseteq> {{(X, m). X \<cong> \<emptyset>}, {(X, m). X \<cong> \<one>}}"
      unfolding quotient_def by (auto, insert isomorphic_is_symmetric isomorphic_is_transitive subobject_one_or_empty, blast+)
  next
    show "{{(X, m). X \<cong> \<emptyset>}, {(X, m). X \<cong> \<one>}} \<subseteq> {(X, m). (X, m) \<subseteq>\<^sub>c \<one>} // {((X1, m1), X2, m2). X1 \<cong> X2}"
      unfolding quotient_def by (insert empty_subobject one_subobject, auto simp add: isomorphic_is_symmetric)
  qed
  then show "card ({(X, m). (X, m) \<subseteq>\<^sub>c \<one>} // {((X, m1), (Y, m2)). X \<cong> Y}) = 2"
    by (simp add: classes_distinct)
qed

lemma coprod_with_init_obj1: 
  assumes "initial_object Y"
  shows "X \<Coprod> Y \<cong> X"
  by (meson assms coprod_pres_iso coproduct_with_empty initial_iso_empty isomorphic_is_reflexive isomorphic_is_transitive)

lemma coprod_with_init_obj2: 
  assumes "initial_object X"
  shows "X \<Coprod> Y \<cong> Y"
  using assms coprod_with_init_obj1 coproduct_commutes isomorphic_is_transitive by blast

lemma prod_with_term_obj1:
  assumes "terminal_object(X)" 
  shows  "X \<times>\<^sub>c Y \<cong> Y" 
  by (meson assms isomorphic_is_reflexive isomorphic_is_transitive one_terminal_object one_x_A_iso_A prod_pres_iso terminal_objects_isomorphic)

lemma prod_with_term_obj2:
  assumes "terminal_object(Y)" 
  shows  "X \<times>\<^sub>c Y \<cong> X"
  by (meson assms isomorphic_is_transitive prod_with_term_obj1 product_commutes)

end