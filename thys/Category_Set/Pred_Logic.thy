section \<open>Predicate Logic Functions\<close>

theory Pred_Logic
  imports Coproduct
begin

subsection \<open>NOT\<close>

definition NOT :: "cfunc" where
  "NOT = (THE \<chi>. is_pullback \<one> \<one> \<Omega> \<Omega> (\<beta>\<^bsub>\<one>\<^esub>) \<t> \<f> \<chi>)"

lemma NOT_is_pullback:
  "is_pullback \<one> \<one> \<Omega> \<Omega> (\<beta>\<^bsub>\<one>\<^esub>) \<t> \<f> NOT"
  unfolding NOT_def
  using characteristic_function_exists false_func_type element_monomorphism
  by (subst the1I2, auto)

lemma NOT_type[type_rule]:
  "NOT : \<Omega> \<rightarrow> \<Omega>"
  using NOT_is_pullback unfolding is_pullback_def  by auto

lemma NOT_false_is_true:
  "NOT \<circ>\<^sub>c \<f> = \<t>"
  using NOT_is_pullback unfolding is_pullback_def 
  by (metis cfunc_type_def id_right_unit id_type one_unique_element)

lemma NOT_true_is_false:
  "NOT \<circ>\<^sub>c \<t> = \<f>"
proof(rule ccontr)
  assume "NOT \<circ>\<^sub>c \<t> \<noteq> \<f>"
  then have "NOT \<circ>\<^sub>c \<t> = \<t>"
    using true_false_only_truth_values by (typecheck_cfuncs, blast)
  then have "\<t> \<circ>\<^sub>c id\<^sub>c \<one> = NOT \<circ>\<^sub>c \<t>"
    using id_right_unit2 true_func_type by auto
  then obtain j where j_type: "j \<in>\<^sub>c \<one>" and j_id: "\<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = id\<^sub>c \<one>" and f_j_eq_t: "\<f> \<circ>\<^sub>c j = \<t>"
    using NOT_is_pullback unfolding is_pullback_def by (typecheck_cfuncs, blast)
  then have "j = id\<^sub>c \<one>"
    using id_type one_unique_element by blast
  then have "\<f> = \<t>"
    using f_j_eq_t false_func_type id_right_unit2 by auto
  then show False
    using true_false_distinct by auto
qed
  
lemma NOT_is_true_implies_false:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "NOT \<circ>\<^sub>c p = \<t> \<Longrightarrow> p = \<f>"
  using NOT_true_is_false assms true_false_only_truth_values by fastforce

lemma NOT_is_false_implies_true:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "NOT \<circ>\<^sub>c p = \<f> \<Longrightarrow> p = \<t>"
  using NOT_false_is_true assms true_false_only_truth_values by fastforce

lemma double_negation:
  "NOT \<circ>\<^sub>c NOT =  id \<Omega>"
  by (typecheck_cfuncs, smt (verit, del_insts) 
  NOT_false_is_true NOT_true_is_false cfunc_type_def comp_associative id_left_unit2 one_separator
  true_false_only_truth_values)

subsection \<open>AND\<close>

definition AND :: "cfunc" where
  "AND = (THE \<chi>. is_pullback \<one> \<one> (\<Omega> \<times>\<^sub>c \<Omega>) \<Omega> (\<beta>\<^bsub>\<one>\<^esub>) \<t> \<langle>\<t>,\<t>\<rangle> \<chi>)"

lemma AND_is_pullback:
  "is_pullback \<one> \<one> (\<Omega> \<times>\<^sub>c \<Omega>) \<Omega> (\<beta>\<^bsub>\<one>\<^esub>) \<t> \<langle>\<t>,\<t>\<rangle> AND"
  unfolding AND_def
  using element_monomorphism characteristic_function_exists
  by (typecheck_cfuncs, subst the1I2, auto)

lemma AND_type[type_rule]:
  "AND : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega>"
  using AND_is_pullback unfolding is_pullback_def by auto

lemma AND_true_true_is_true:
  "AND \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle> = \<t>"
  using AND_is_pullback unfolding is_pullback_def
  by (metis cfunc_type_def id_right_unit id_type one_unique_element)

lemma AND_false_left_is_false:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "AND \<circ>\<^sub>c \<langle>\<f>,p\<rangle> = \<f>"
proof (rule ccontr)
  assume "AND \<circ>\<^sub>c \<langle>\<f>,p\<rangle> \<noteq> \<f>"
  then have "AND \<circ>\<^sub>c \<langle>\<f>,p\<rangle> = \<t>"
    using assms true_false_only_truth_values by (typecheck_cfuncs, blast)
  then have "\<t> \<circ>\<^sub>c id \<one> = AND \<circ>\<^sub>c \<langle>\<f>,p\<rangle>"
    using assms by (typecheck_cfuncs, simp add: id_right_unit2)
  then obtain j where j_type: "j \<in>\<^sub>c \<one>" and j_id: "\<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = id\<^sub>c \<one>" and tt_j_eq_fp: "\<langle>\<t>,\<t>\<rangle> \<circ>\<^sub>c j = \<langle>\<f>,p\<rangle>"
    using AND_is_pullback assms unfolding is_pullback_def by (typecheck_cfuncs, blast)
  then have "j = id\<^sub>c \<one>"
    using id_type one_unique_element by auto
  then have "\<langle>\<t>,\<t>\<rangle> = \<langle>\<f>,p\<rangle>"
    by (typecheck_cfuncs, metis tt_j_eq_fp id_right_unit2)
  then have "\<t> = \<f>"
    using assms cart_prod_eq2 by (typecheck_cfuncs, auto)
  then show False
    using true_false_distinct by auto
qed

lemma AND_false_right_is_false:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "AND \<circ>\<^sub>c \<langle>p,\<f>\<rangle> = \<f>"
proof(rule ccontr)
  assume "AND \<circ>\<^sub>c \<langle>p,\<f>\<rangle> \<noteq> \<f>"
  then have "AND \<circ>\<^sub>c \<langle>p,\<f>\<rangle> = \<t>"
    using assms true_false_only_truth_values by (typecheck_cfuncs, blast)
  then have "\<t> \<circ>\<^sub>c id \<one> = AND \<circ>\<^sub>c \<langle>p,\<f>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: id_right_unit2)
  then obtain j where j_type: "j \<in>\<^sub>c \<one>" and j_id: "\<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = id\<^sub>c \<one>" and tt_j_eq_fp: "\<langle>\<t>,\<t>\<rangle> \<circ>\<^sub>c j = \<langle>p,\<f>\<rangle>"
    using AND_is_pullback assms unfolding is_pullback_def by (typecheck_cfuncs, blast)
  then have "j = id\<^sub>c \<one>"
    using id_type one_unique_element by auto
  then have "\<langle>\<t>,\<t>\<rangle> = \<langle>p,\<f>\<rangle>"
    by (typecheck_cfuncs, metis tt_j_eq_fp id_right_unit2)
  then have "\<t> = \<f>"
    using assms cart_prod_eq2 by (typecheck_cfuncs, auto)
  then show "False"
    using true_false_distinct by auto
qed

lemma AND_commutative:
  assumes "p \<in>\<^sub>c \<Omega>"
  assumes "q \<in>\<^sub>c \<Omega>"
  shows "AND \<circ>\<^sub>c \<langle>p,q\<rangle> = AND \<circ>\<^sub>c \<langle>q,p\<rangle>"
  by (metis AND_false_left_is_false AND_false_right_is_false assms true_false_only_truth_values)

lemma AND_idempotent:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "AND \<circ>\<^sub>c \<langle>p,p\<rangle> = p"
  using AND_false_right_is_false AND_true_true_is_true assms true_false_only_truth_values by blast

lemma AND_associative:
  assumes "p \<in>\<^sub>c \<Omega>"
  assumes "q \<in>\<^sub>c \<Omega>"
  assumes "r \<in>\<^sub>c \<Omega>"
  shows "AND \<circ>\<^sub>c \<langle>AND \<circ>\<^sub>c \<langle>p,q\<rangle>, r\<rangle> = AND \<circ>\<^sub>c \<langle>p, AND \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle>"
  by (metis AND_commutative AND_false_left_is_false AND_true_true_is_true assms true_false_only_truth_values)

lemma AND_complementary:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "AND \<circ>\<^sub>c \<langle>p, NOT \<circ>\<^sub>c p\<rangle> =  \<f>"
  by (metis AND_false_left_is_false AND_false_right_is_false NOT_false_is_true NOT_true_is_false assms true_false_only_truth_values true_func_type)

subsection \<open>NOR\<close>

definition NOR :: "cfunc" where
  "NOR = (THE \<chi>. is_pullback  \<one> \<one> (\<Omega> \<times>\<^sub>c \<Omega>) \<Omega> (\<beta>\<^bsub>\<one>\<^esub>) \<t> \<langle>\<f>, \<f>\<rangle> \<chi>)"

lemma NOR_is_pullback:
  "is_pullback  \<one> \<one> (\<Omega> \<times>\<^sub>c \<Omega>) \<Omega> (\<beta>\<^bsub>\<one>\<^esub>) \<t> \<langle>\<f>, \<f>\<rangle> NOR"
  unfolding NOR_def
  using characteristic_function_exists element_monomorphism
  by (typecheck_cfuncs, simp add: the1I2)

lemma NOR_type[type_rule]:
  "NOR : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega>"
  using NOR_is_pullback unfolding is_pullback_def by auto

lemma NOR_false_false_is_true:
  "NOR \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle> = \<t>"
  using NOR_is_pullback unfolding is_pullback_def 
  by (auto, metis cfunc_type_def id_right_unit id_type one_unique_element)

lemma NOR_left_true_is_false:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "NOR \<circ>\<^sub>c \<langle>\<t>,p\<rangle> = \<f>"
proof (rule ccontr)
  assume "NOR \<circ>\<^sub>c \<langle>\<t>,p\<rangle> \<noteq> \<f>"
  then have "NOR \<circ>\<^sub>c \<langle>\<t>,p\<rangle> = \<t>"
    using assms true_false_only_truth_values by (typecheck_cfuncs, blast)
  then have "NOR \<circ>\<^sub>c \<langle>\<t>,p\<rangle> = \<t> \<circ>\<^sub>c id \<one>"
    using id_right_unit2 true_func_type by auto
  then obtain j where j_type: "j \<in>\<^sub>c \<one>" and j_id: "\<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = id \<one>" and ff_j_eq_tp: "\<langle>\<f>,\<f>\<rangle> \<circ>\<^sub>c j = \<langle>\<t>,p\<rangle>"
    using NOR_is_pullback assms unfolding is_pullback_def by (typecheck_cfuncs, metis)
  then have "j = id \<one>"
    using id_type one_unique_element by blast
  then have "\<langle>\<f>,\<f>\<rangle> = \<langle>\<t>,p\<rangle>"
    using cfunc_prod_comp false_func_type ff_j_eq_tp id_right_unit2 j_type by auto
  then have "\<f> = \<t>"
    using assms cart_prod_eq2 false_func_type true_func_type by auto
  then show False
    using true_false_distinct by auto
qed

lemma NOR_right_true_is_false:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "NOR \<circ>\<^sub>c \<langle>p,\<t>\<rangle> = \<f>"
proof (rule ccontr)
  assume "NOR \<circ>\<^sub>c \<langle>p,\<t>\<rangle> \<noteq> \<f>"
  then have "NOR \<circ>\<^sub>c \<langle>p,\<t>\<rangle> = \<t>"
    using assms true_false_only_truth_values by (typecheck_cfuncs, blast)
  then have "NOR \<circ>\<^sub>c \<langle>p,\<t>\<rangle> = \<t> \<circ>\<^sub>c id \<one>"
    using id_right_unit2 true_func_type by auto
  then obtain j where j_type: "j \<in>\<^sub>c \<one>" and j_id: "\<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = id \<one>" and ff_j_eq_tp: "\<langle>\<f>,\<f>\<rangle> \<circ>\<^sub>c j = \<langle>p,\<t>\<rangle>"
    using NOR_is_pullback assms unfolding is_pullback_def by (typecheck_cfuncs, metis)
  then have "j = id \<one>"
    using id_type one_unique_element by blast
  then have "\<langle>\<f>,\<f>\<rangle> = \<langle>p,\<t>\<rangle>"
    using cfunc_prod_comp false_func_type ff_j_eq_tp id_right_unit2 j_type by auto
  then have "\<f> = \<t>"
    using assms cart_prod_eq2 false_func_type true_func_type by auto
  then show False
    using true_false_distinct by auto
qed

lemma NOR_true_implies_both_false:
  assumes X_nonempty: "nonempty X" and Y_nonempty: "nonempty Y"
  assumes P_Q_types[type_rule]: "P : X \<rightarrow> \<Omega>" "Q : Y \<rightarrow> \<Omega>"
  assumes NOR_true: "NOR \<circ>\<^sub>c (P \<times>\<^sub>f Q) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
  shows "P = \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<and> Q = \<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
proof -
  obtain z where z_type[type_rule]: "z : X \<times>\<^sub>c Y \<rightarrow> \<one>" and "P \<times>\<^sub>f Q = \<langle>\<f>,\<f>\<rangle> \<circ>\<^sub>c z"
    using NOR_is_pullback NOR_true unfolding is_pullback_def
    by (metis P_Q_types cfunc_cross_prod_type terminal_func_type) 
  then have "P \<times>\<^sub>f Q = \<langle>\<f>,\<f>\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
    using terminal_func_unique by auto
  then have "P \<times>\<^sub>f Q = \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>, \<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>\<rangle>"
    by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  then have "P \<times>\<^sub>f Q = \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c left_cart_proj X Y, \<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c right_cart_proj X Y\<rangle>"
    by (typecheck_cfuncs_prems, metis left_cart_proj_type right_cart_proj_type terminal_func_comp)
  then have "\<langle>P \<circ>\<^sub>c left_cart_proj X Y, Q \<circ>\<^sub>c right_cart_proj X Y\<rangle>
      = \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c left_cart_proj X Y, \<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c right_cart_proj X Y\<rangle>"
    by (typecheck_cfuncs, unfold cfunc_cross_prod_def2, auto)
  then have "P \<circ>\<^sub>c left_cart_proj X Y = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c left_cart_proj X Y
      \<and> Q \<circ>\<^sub>c right_cart_proj X Y = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c right_cart_proj X Y"
    using  cart_prod_eq2 by (typecheck_cfuncs, auto simp add: comp_associative2)
  then have eqs: "P = \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<and> Q = \<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
    using assms epimorphism_def3 nonempty_left_imp_right_proj_epimorphism nonempty_right_imp_left_proj_epimorphism
    by (typecheck_cfuncs_prems, blast)
  then have "P \<noteq> \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<and> Q \<noteq> \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
  proof safe
    show "\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<Longrightarrow> False"
      by (typecheck_cfuncs_prems, smt X_nonempty comp_associative2 nonempty_def one_separator_contrapos terminal_func_comp terminal_func_unique true_false_distinct)
    show "\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> \<Longrightarrow> False"
      by (typecheck_cfuncs_prems, smt Y_nonempty comp_associative2 nonempty_def one_separator_contrapos terminal_func_comp terminal_func_unique true_false_distinct)
  qed
  then show ?thesis
    using eqs by linarith
qed

lemma NOR_true_implies_neither_true:
  assumes X_nonempty: "nonempty X" and Y_nonempty: "nonempty Y"
  assumes P_Q_types[type_rule]: "P : X \<rightarrow> \<Omega>" "Q : Y \<rightarrow> \<Omega>"
  assumes NOR_true: "NOR \<circ>\<^sub>c (P \<times>\<^sub>f Q) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
  shows "\<not> (P = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<or> Q = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)"
  by (smt (verit, ccfv_SIG) NOR_true NOT_false_is_true NOT_true_is_false NOT_type X_nonempty Y_nonempty assms(3,4) comp_associative2 comp_type nonempty_def terminal_func_type true_false_distinct true_false_only_truth_values NOR_true_implies_both_false)

subsection \<open>OR\<close>

definition OR :: "cfunc" where
  "OR = (THE \<chi>. is_pullback (\<one>\<Coprod>(\<one>\<Coprod>\<one>)) \<one> (\<Omega>\<times>\<^sub>c\<Omega>) \<Omega> (\<beta>\<^bsub>(\<one>\<Coprod>(\<one>\<Coprod>\<one>))\<^esub>) \<t> (\<langle>\<t>, \<t>\<rangle>\<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<chi>)"

lemma pre_OR_type[type_rule]: 
  "\<langle>\<t>, \<t>\<rangle>\<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>) : \<one>\<Coprod>(\<one>\<Coprod>\<one>) \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega>"
  by typecheck_cfuncs

lemma set_three: 
  "{x. x \<in>\<^sub>c (\<one>\<Coprod>(\<one>\<Coprod>\<one>))} = {
 (left_coproj \<one> (\<one>\<Coprod>\<one>)) , 
 (right_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c left_coproj \<one> \<one>), 
  right_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c(right_coproj \<one> \<one>)}"
  by(typecheck_cfuncs, safe, typecheck_cfuncs, smt (z3) comp_associative2 coprojs_jointly_surj one_unique_element)

lemma set_three_card: 
 "card {x. x \<in>\<^sub>c (\<one>\<Coprod>(\<one>\<Coprod>\<one>))} = 3"
proof - 
  have f1: "left_coproj \<one> (\<one> \<Coprod> \<one>) \<noteq> right_coproj \<one> (\<one> \<Coprod> \<one>) \<circ>\<^sub>c left_coproj \<one> \<one>"
    by (typecheck_cfuncs, metis cfunc_type_def coproducts_disjoint id_right_unit id_type)
  have f2: "left_coproj \<one> (\<one> \<Coprod> \<one>) \<noteq> right_coproj \<one> (\<one> \<Coprod> \<one>) \<circ>\<^sub>c right_coproj \<one> \<one>"
    by (typecheck_cfuncs, metis cfunc_type_def coproducts_disjoint id_right_unit id_type)
  have f3: "right_coproj \<one> (\<one> \<Coprod> \<one>) \<circ>\<^sub>c left_coproj \<one> \<one> \<noteq> right_coproj \<one> (\<one> \<Coprod> \<one>) \<circ>\<^sub>c right_coproj \<one> \<one>"
    by (typecheck_cfuncs, metis cfunc_type_def coproducts_disjoint monomorphism_def one_unique_element right_coproj_are_monomorphisms)
  show ?thesis
    by (simp add: f1 f2 f3 set_three)
qed

lemma pre_OR_injective:
  "injective(\<langle>\<t>, \<t>\<rangle>\<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>))"
  unfolding injective_def
proof(clarify)
  fix x y 
  assume "x \<in>\<^sub>c domain (\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle>)" 
  then have x_type: "x \<in>\<^sub>c (\<one>\<Coprod>(\<one>\<Coprod>\<one>))"  
    using cfunc_type_def pre_OR_type by force
  then have x_form: "(\<exists> w. (w \<in>\<^sub>c \<one> \<and> x = (left_coproj \<one> (\<one>\<Coprod>\<one>)) \<circ>\<^sub>c w))
      \<or>  (\<exists> w. (w \<in>\<^sub>c (\<one>\<Coprod>\<one>) \<and> x = (right_coproj \<one> (\<one>\<Coprod>\<one>)) \<circ>\<^sub>c w))"
    using coprojs_jointly_surj by auto

  assume "y \<in>\<^sub>c domain (\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle>)" 
  then have y_type: "y \<in>\<^sub>c (\<one>\<Coprod>(\<one>\<Coprod>\<one>))"  
    using cfunc_type_def pre_OR_type by force
  then have y_form: "(\<exists> w. (w \<in>\<^sub>c \<one> \<and> y = (left_coproj \<one> (\<one>\<Coprod>\<one>)) \<circ>\<^sub>c w))
      \<or>  (\<exists> w. (w \<in>\<^sub>c (\<one>\<Coprod>\<one>) \<and> y = (right_coproj \<one> (\<one>\<Coprod>\<one>)) \<circ>\<^sub>c w))"
    using coprojs_jointly_surj by auto

  assume mx_eqs_my: "\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c x = \<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c y"

  have f1: "\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c left_coproj \<one> (\<one> \<Coprod> \<one>) = \<langle>\<t>,\<t>\<rangle>"
    by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
  have f2: "\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c (right_coproj \<one> (\<one>\<Coprod>\<one>)\<circ>\<^sub>c left_coproj \<one> \<one>) = \<langle>\<t>,\<f>\<rangle>"
  proof- 
    have "\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c (right_coproj \<one> (\<one>\<Coprod>\<one>)\<circ>\<^sub>c left_coproj \<one> \<one>) = 
          (\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c right_coproj \<one> (\<one>\<Coprod>\<one>) )\<circ>\<^sub>c left_coproj \<one> \<one>"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c left_coproj \<one> \<one>"
      using right_coproj_cfunc_coprod by (typecheck_cfuncs, smt)
    also have "... = \<langle>\<t>,\<f>\<rangle>"
      by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
    finally show ?thesis.
  qed
  have f3: "\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c (right_coproj \<one> (\<one>\<Coprod>\<one>)\<circ>\<^sub>c right_coproj \<one> \<one>) = \<langle>\<f>,\<t>\<rangle>"
  proof- 
    have "\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c (right_coproj \<one> (\<one>\<Coprod>\<one>)\<circ>\<^sub>c right_coproj \<one> \<one>) = 
          (\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c right_coproj \<one> (\<one>\<Coprod>\<one>) )\<circ>\<^sub>c right_coproj \<one> \<one>"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c right_coproj \<one> \<one>"
      using right_coproj_cfunc_coprod by (typecheck_cfuncs, smt)
    also have "... = \<langle>\<f>,\<t>\<rangle>"
      by (typecheck_cfuncs, simp add: right_coproj_cfunc_coprod)
    finally show ?thesis.
  qed
  show "x = y"
  proof(cases "x = left_coproj \<one> (\<one> \<Coprod> \<one>)")
    assume case1: "x = left_coproj \<one> (\<one> \<Coprod> \<one>)"
    then show "x = y"
      by (typecheck_cfuncs, smt (z3) mx_eqs_my element_pair_eq f1 f2 f3 false_func_type maps_into_1u1 terminal_func_unique true_false_distinct true_func_type x_form y_form)
  next
    assume not_case1: "x \<noteq> left_coproj \<one> (\<one> \<Coprod> \<one>)"
    then have case2_or_3: "x = (right_coproj \<one> (\<one>\<Coprod>\<one>)\<circ>\<^sub>c left_coproj \<one> \<one>)\<or> 
               x = right_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c(right_coproj \<one> \<one>)"
      by (metis id_right_unit2 id_type left_proj_type maps_into_1u1 terminal_func_unique x_form)
    show "x = y"
    proof(cases "x = (right_coproj \<one> (\<one>\<Coprod>\<one>)\<circ>\<^sub>c left_coproj \<one> \<one>)")
      assume case2: "x = right_coproj \<one> (\<one> \<Coprod> \<one>) \<circ>\<^sub>c left_coproj \<one> \<one>"
      then show "x = y"
        by (typecheck_cfuncs, smt (z3) cart_prod_eq2 case2 f1 f2 f3 false_func_type id_right_unit2 left_proj_type maps_into_1u1 mx_eqs_my terminal_func_comp terminal_func_comp_elem terminal_func_unique true_false_distinct true_func_type y_form)        
    next
      assume not_case2: "x \<noteq> right_coproj \<one> (\<one> \<Coprod> \<one>) \<circ>\<^sub>c left_coproj \<one> \<one>"
      then have case3: "x = right_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c(right_coproj \<one> \<one>)"
        using case2_or_3 by blast
      then show "x = y"
        by (smt (verit, best) f1 f2 f3  NOR_false_false_is_true NOR_is_pullback case3 cfunc_prod_comp comp_associative2 element_pair_eq false_func_type is_pullback_def left_proj_type maps_into_1u1 mx_eqs_my pre_OR_type terminal_func_unique true_false_distinct true_func_type y_form)
    qed
  qed
qed

lemma OR_is_pullback:
  "is_pullback (\<one>\<Coprod>(\<one>\<Coprod>\<one>)) \<one> (\<Omega>\<times>\<^sub>c\<Omega>) \<Omega> (\<beta>\<^bsub>(\<one>\<Coprod>(\<one>\<Coprod>\<one>))\<^esub>) \<t> (\<langle>\<t>, \<t>\<rangle>\<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) OR"
  unfolding OR_def
  using element_monomorphism characteristic_function_exists
  by (typecheck_cfuncs, simp add: the1I2 injective_imp_monomorphism pre_OR_injective)
      
lemma OR_type[type_rule]:
  "OR : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega>"
  unfolding OR_def
  by (metis OR_def OR_is_pullback is_pullback_def) 

lemma OR_true_left_is_true:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "OR \<circ>\<^sub>c \<langle>\<t>,p\<rangle> = \<t>"
proof - 
  have "\<exists> j. j \<in>\<^sub>c \<one>\<Coprod>(\<one>\<Coprod>\<one>) \<and> (\<langle>\<t>, \<t>\<rangle>\<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<circ>\<^sub>c j  = \<langle>\<t>,p\<rangle>"
    by (typecheck_cfuncs, smt (z3) assms comp_associative2 comp_type left_coproj_cfunc_coprod
        left_proj_type right_coproj_cfunc_coprod right_proj_type true_false_only_truth_values)
  then show ?thesis 
    by (typecheck_cfuncs, smt (verit, ccfv_SIG)  NOT_false_is_true NOT_is_pullback OR_is_pullback
        comp_associative2 is_pullback_def terminal_func_comp)
qed

lemma OR_true_right_is_true:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "OR \<circ>\<^sub>c \<langle>p,\<t>\<rangle> = \<t>"
proof - 
  have "\<exists> j. j \<in>\<^sub>c \<one>\<Coprod>(\<one>\<Coprod>\<one>) \<and> (\<langle>\<t>, \<t>\<rangle>\<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<circ>\<^sub>c j = \<langle>p,\<t>\<rangle>"
    by (typecheck_cfuncs, smt (z3) assms comp_associative2 comp_type left_coproj_cfunc_coprod
        left_proj_type right_coproj_cfunc_coprod right_proj_type true_false_only_truth_values)
  then show ?thesis 
    by (typecheck_cfuncs, smt (verit, ccfv_SIG) NOT_false_is_true NOT_is_pullback OR_is_pullback
        comp_associative2 is_pullback_def  terminal_func_comp)
qed

lemma OR_false_false_is_false:
  "OR \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle> = \<f>"
proof(rule ccontr)
  assume "OR \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle> \<noteq> \<f>"
  then have "OR \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle> = \<t>"
    using  true_false_only_truth_values by (typecheck_cfuncs, blast)
  then obtain j where  j_type[type_rule]: "j \<in>\<^sub>c \<one>\<Coprod>(\<one>\<Coprod>\<one>)" and j_def: "(\<langle>\<t>, \<t>\<rangle>\<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<circ>\<^sub>c j  = \<langle>\<f>,\<f>\<rangle>"
    using  OR_is_pullback unfolding is_pullback_def 
    by (typecheck_cfuncs, metis id_right_unit2 id_type)
  have trichotomy: "(\<langle>\<t>, \<t>\<rangle> = \<langle>\<f>,\<f>\<rangle>) \<or> ((\<langle>\<t>, \<f>\<rangle> = \<langle>\<f>,\<f>\<rangle>) \<or> (\<langle>\<f>, \<t>\<rangle> = \<langle>\<f>,\<f>\<rangle>))"
  proof(cases "j = left_coproj \<one> (\<one> \<Coprod> \<one>)")
    assume case1: "j = left_coproj \<one> (\<one> \<Coprod> \<one>)"
    then show ?thesis
      using case1 cfunc_coprod_type j_def left_coproj_cfunc_coprod by (typecheck_cfuncs, force)
  next
    assume not_case1: "j \<noteq> left_coproj \<one> (\<one> \<Coprod> \<one>)"
    then have case2_or_3: "j = right_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c left_coproj \<one> \<one>   \<or> 
                           j = right_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c right_coproj \<one> \<one>"
      using not_case1 set_three by (typecheck_cfuncs, auto)
    show ?thesis
    proof(cases "j = (right_coproj \<one> (\<one>\<Coprod>\<one>)\<circ>\<^sub>c left_coproj \<one> \<one>)")
      assume case2: "j = right_coproj \<one> (\<one> \<Coprod> \<one>) \<circ>\<^sub>c left_coproj \<one> \<one>"
      have "\<langle>\<t>, \<f>\<rangle> = \<langle>\<f>,\<f>\<rangle>"
      proof - 
        have "(\<langle>\<t>, \<t>\<rangle>\<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<circ>\<^sub>c j = ((\<langle>\<t>, \<t>\<rangle>\<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<circ>\<^sub>c right_coproj \<one> (\<one> \<Coprod> \<one>)) \<circ>\<^sub>c left_coproj \<one> \<one>"
          by (typecheck_cfuncs, simp add: case2 comp_associative2)
        also have "... = (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>) \<circ>\<^sub>c left_coproj \<one> \<one>"
          using right_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
        also have "... = \<langle>\<t>, \<f>\<rangle>"
          by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
        finally show ?thesis
          using j_def by simp
      qed
      then show ?thesis
        by blast
    next
      assume not_case2: "j \<noteq> right_coproj \<one> (\<one> \<Coprod> \<one>) \<circ>\<^sub>c left_coproj \<one> \<one>"
      then have case3: "j = right_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c right_coproj \<one> \<one>"
        using case2_or_3 by blast
      have "\<langle>\<f>, \<t>\<rangle> = \<langle>\<f>,\<f>\<rangle>"
      proof - 
        have "(\<langle>\<t>, \<t>\<rangle>\<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<circ>\<^sub>c j = ((\<langle>\<t>, \<t>\<rangle>\<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<circ>\<^sub>c right_coproj \<one> (\<one> \<Coprod> \<one>)) \<circ>\<^sub>c right_coproj \<one> \<one>"
          by (typecheck_cfuncs, simp add: case3 comp_associative2)
        also have "... = (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>) \<circ>\<^sub>c right_coproj \<one> \<one>"
          using right_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
        also have "... = \<langle>\<f>, \<t>\<rangle>"
          by (typecheck_cfuncs, simp add: right_coproj_cfunc_coprod)
        finally show ?thesis
          using j_def by simp
      qed
      then show ?thesis
        by blast
    qed
  qed
    then have "\<t> = \<f>"
      using trichotomy cart_prod_eq2 by (typecheck_cfuncs, force)
    then show False
      using true_false_distinct by smt
qed

lemma OR_true_implies_one_is_true:
  assumes "p \<in>\<^sub>c \<Omega>" 
  assumes "q \<in>\<^sub>c \<Omega>"
  assumes "OR \<circ>\<^sub>c \<langle>p,q\<rangle> = \<t>"
  shows "(p = \<t>) \<or> (q = \<t>)"
  by (metis OR_false_false_is_false assms true_false_only_truth_values)

lemma NOT_NOR_is_OR:
 "OR = NOT \<circ>\<^sub>c NOR"
proof(etcs_rule one_separator)
  fix x 
  assume x_type[type_rule]: "x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>"
  then obtain p q where p_type[type_rule]: "p \<in>\<^sub>c \<Omega>" and q_type[type_rule]:  "q \<in>\<^sub>c \<Omega>" and x_def: "x = \<langle>p,q\<rangle>"
    by (meson cart_prod_decomp)
  show "OR \<circ>\<^sub>c x = (NOT \<circ>\<^sub>c NOR) \<circ>\<^sub>c x"
  proof(cases "p = \<t>")
    show "p = \<t> \<Longrightarrow> OR \<circ>\<^sub>c x = (NOT \<circ>\<^sub>c NOR) \<circ>\<^sub>c x"
      by (typecheck_cfuncs, metis NOR_left_true_is_false NOT_false_is_true OR_true_left_is_true comp_associative2 q_type x_def)
  next
    assume "p \<noteq> \<t>"
    then have "p = \<f>"
      using p_type true_false_only_truth_values by blast
    show "OR \<circ>\<^sub>c x = (NOT \<circ>\<^sub>c NOR) \<circ>\<^sub>c x"
    proof(cases "q = \<t>")
      show "q = \<t> \<Longrightarrow> OR \<circ>\<^sub>c x = (NOT \<circ>\<^sub>c NOR) \<circ>\<^sub>c x"
        by (typecheck_cfuncs, metis NOR_right_true_is_false NOT_false_is_true OR_true_right_is_true 
            cfunc_type_def comp_associative p_type x_def)
    next
      assume "q \<noteq> \<t>"
      then show ?thesis
        by (typecheck_cfuncs,metis NOR_false_false_is_true NOT_is_true_implies_false OR_false_false_is_false
            \<open>p = \<f>\<close>  comp_associative2 q_type true_false_only_truth_values x_def)
    qed
  qed
qed

lemma OR_commutative:
  assumes "p \<in>\<^sub>c \<Omega>"
  assumes "q \<in>\<^sub>c \<Omega>"
  shows "OR \<circ>\<^sub>c \<langle>p,q\<rangle> = OR \<circ>\<^sub>c \<langle>q,p\<rangle>"
  by (metis OR_true_left_is_true OR_true_right_is_true assms true_false_only_truth_values)

lemma OR_idempotent:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "OR \<circ>\<^sub>c \<langle>p,p\<rangle> = p"
  using OR_false_false_is_false OR_true_left_is_true assms true_false_only_truth_values by blast

lemma OR_associative:
  assumes "p \<in>\<^sub>c \<Omega>"
  assumes "q \<in>\<^sub>c \<Omega>"
  assumes "r \<in>\<^sub>c \<Omega>"
  shows "OR \<circ>\<^sub>c \<langle>OR \<circ>\<^sub>c \<langle>p,q\<rangle>, r\<rangle> = OR \<circ>\<^sub>c \<langle>p, OR \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle>"
  by (metis OR_commutative OR_false_false_is_false OR_true_right_is_true assms true_false_only_truth_values)

lemma OR_complementary:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "OR \<circ>\<^sub>c \<langle>p, NOT \<circ>\<^sub>c p\<rangle> =  \<t>"
  by (metis NOT_false_is_true NOT_true_is_false OR_true_left_is_true OR_true_right_is_true assms false_func_type true_false_only_truth_values)

subsection \<open>XOR\<close>

definition XOR :: "cfunc" where
  "XOR = (THE \<chi>. is_pullback (\<one>\<Coprod>\<one>) \<one> (\<Omega>\<times>\<^sub>c\<Omega>) \<Omega> (\<beta>\<^bsub>(\<one>\<Coprod>\<one>)\<^esub>) \<t> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>) \<chi>)"

lemma pre_XOR_type[type_rule]: 
  "\<langle>\<t>, \<f>\<rangle> \<amalg> \<langle>\<f>, \<t>\<rangle> : \<one>\<Coprod>\<one> \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega>"
  by typecheck_cfuncs

lemma pre_XOR_injective:
 "injective(\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)"
 unfolding injective_def
proof(clarify)
  fix x y 
  assume "x \<in>\<^sub>c domain (\<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle>)" 
  then have x_type: "x \<in>\<^sub>c \<one>\<Coprod>\<one>"  
    using cfunc_type_def pre_XOR_type by force
  then have x_form: "(\<exists> w. w \<in>\<^sub>c \<one> \<and> x = left_coproj \<one> \<one> \<circ>\<^sub>c w)
                  \<or>  (\<exists> w. w \<in>\<^sub>c \<one> \<and> x = right_coproj \<one> \<one> \<circ>\<^sub>c w)"
    using coprojs_jointly_surj by auto

  assume "y \<in>\<^sub>c domain (\<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle>)" 
  then have y_type: "y \<in>\<^sub>c \<one>\<Coprod>\<one>"  
    using cfunc_type_def pre_XOR_type by force
  then have y_form: "(\<exists> w. w \<in>\<^sub>c \<one> \<and> y = left_coproj \<one> \<one> \<circ>\<^sub>c w)
                 \<or>  (\<exists> w. w \<in>\<^sub>c \<one> \<and> y = right_coproj \<one> \<one> \<circ>\<^sub>c w)"
    using coprojs_jointly_surj by auto

  assume eqs: "\<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c x = \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c y"

  show "x = y"
  proof(cases "\<exists> w. w \<in>\<^sub>c \<one> \<and> x = left_coproj \<one> \<one> \<circ>\<^sub>c w")
    assume a1: "\<exists> w. w \<in>\<^sub>c \<one> \<and> x = left_coproj \<one> \<one> \<circ>\<^sub>c w"
    then obtain w where x_def: "w \<in>\<^sub>c \<one> \<and> x = left_coproj \<one> \<one> \<circ>\<^sub>c w"
      by blast
    then have w_is: "w = id(\<one>)"
      by (typecheck_cfuncs, metis terminal_func_unique x_def)
    have "\<exists> v. v \<in>\<^sub>c \<one> \<and> y = left_coproj \<one> \<one> \<circ>\<^sub>c v"
    proof(rule ccontr)
      assume a2: "\<nexists>v. v \<in>\<^sub>c \<one> \<and> y = left_coproj \<one> \<one> \<circ>\<^sub>c v"
      then obtain v where y_def:  "v \<in>\<^sub>c \<one> \<and> y = right_coproj \<one> \<one> \<circ>\<^sub>c v"
        using y_form by (typecheck_cfuncs, blast)
      then have v_is: "v = id(\<one>)"
        by (typecheck_cfuncs, metis terminal_func_unique y_def)
      then have "\<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c left_coproj \<one> \<one> = \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c right_coproj \<one> \<one>"
        using w_is eqs id_right_unit2 x_def y_def by (typecheck_cfuncs, force)
      then have "\<langle>\<t>,\<f>\<rangle> = \<langle>\<f>,\<t>\<rangle>"
        by (typecheck_cfuncs, smt (z3) cfunc_coprod_unique coprod_eq2 pre_XOR_type right_coproj_cfunc_coprod)      
      then have "\<t> = \<f> \<and> \<f> = \<t>"
        using cart_prod_eq2 false_func_type true_func_type by blast
      then show False
        using true_false_distinct by blast
    qed
    then obtain v where y_def: "v \<in>\<^sub>c \<one> \<and> y = left_coproj \<one> \<one> \<circ>\<^sub>c v"
      by blast
    then have "v = id(\<one>)"
      by (typecheck_cfuncs, metis terminal_func_unique)
    then show ?thesis
      by (simp add: w_is x_def y_def)
  next
    assume "\<nexists>w. w \<in>\<^sub>c \<one> \<and> x = left_coproj \<one> \<one> \<circ>\<^sub>c w"
    then obtain w where x_def: "w \<in>\<^sub>c \<one> \<and> x = right_coproj \<one> \<one> \<circ>\<^sub>c w"
      using x_form by force
    then have w_is: "w = id \<one>"
      by (typecheck_cfuncs, metis terminal_func_unique x_def)
    have "\<exists> v. v \<in>\<^sub>c \<one> \<and> y = right_coproj \<one> \<one> \<circ>\<^sub>c v"
    proof(rule ccontr)
      assume a2: "\<nexists>v. v \<in>\<^sub>c \<one> \<and> y = right_coproj \<one> \<one> \<circ>\<^sub>c v"
      then obtain v where y_def:  "v \<in>\<^sub>c \<one> \<and> y = left_coproj \<one> \<one> \<circ>\<^sub>c v"
        using y_form by (typecheck_cfuncs, blast)
      then have "v = id \<one>"
        by (typecheck_cfuncs, metis terminal_func_unique y_def)
      then have "\<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c left_coproj \<one> \<one> = \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c right_coproj \<one> \<one>"
        using w_is eqs id_right_unit2 x_def y_def by (typecheck_cfuncs, force)
      then have "\<langle>\<t>,\<f>\<rangle> = \<langle>\<f>,\<t>\<rangle>"
        by (typecheck_cfuncs, smt (z3)  cfunc_coprod_unique coprod_eq2 pre_XOR_type right_coproj_cfunc_coprod)      
      then have "\<t> = \<f> \<and> \<f> = \<t>"
        using cart_prod_eq2 false_func_type true_func_type by blast
      then show False
        using true_false_distinct by blast
    qed
    then obtain v where y_def: "v \<in>\<^sub>c \<one> \<and> y = right_coproj \<one> \<one> \<circ>\<^sub>c v"
      by blast
    then have "v = id \<one>"
      by (typecheck_cfuncs, metis terminal_func_unique)
    then show ?thesis
      by (simp add: w_is x_def y_def)
  qed
qed

lemma XOR_is_pullback:
  "is_pullback (\<one>\<Coprod>\<one>) \<one> (\<Omega> \<times>\<^sub>c \<Omega>) \<Omega> (\<beta>\<^bsub>(\<one>\<Coprod>\<one>)\<^esub>) \<t> (\<langle>\<t>, \<f>\<rangle> \<amalg> \<langle>\<f>, \<t>\<rangle>) XOR"
  unfolding XOR_def
  using element_monomorphism characteristic_function_exists
  by (typecheck_cfuncs, simp add: the1I2 injective_imp_monomorphism pre_XOR_injective)
      
lemma XOR_type[type_rule]:
  "XOR : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega>"
  unfolding XOR_def
  by (metis XOR_def XOR_is_pullback is_pullback_def)

lemma XOR_only_true_left_is_true:
  "XOR \<circ>\<^sub>c  \<langle>\<t>,\<f>\<rangle> = \<t>"
proof -   
  have "\<exists> j. j \<in>\<^sub>c \<one>\<Coprod>\<one> \<and> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>) \<circ>\<^sub>c j  = \<langle>\<t>,\<f>\<rangle>"
    by (typecheck_cfuncs, meson left_coproj_cfunc_coprod left_proj_type)
  then show ?thesis
    by (smt (verit, best) XOR_is_pullback comp_associative2 id_right_unit2 is_pullback_def terminal_func_comp_elem)
qed

lemma XOR_only_true_right_is_true:
  "XOR \<circ>\<^sub>c  \<langle>\<f>,\<t>\<rangle> = \<t>"
proof -   
  have "\<exists> j. j \<in>\<^sub>c \<one>\<Coprod>\<one> \<and> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>) \<circ>\<^sub>c j  = \<langle>\<f>,\<t>\<rangle>"
    by (typecheck_cfuncs, meson right_coproj_cfunc_coprod right_proj_type)
  then show ?thesis
    by (smt (verit, best) XOR_is_pullback  comp_associative2 id_right_unit2 is_pullback_def terminal_func_comp_elem)
qed

lemma XOR_false_false_is_false:
   "XOR \<circ>\<^sub>c  \<langle>\<f>,\<f>\<rangle> = \<f>"
proof(rule ccontr)
  assume "XOR \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle> \<noteq> \<f>"
  then have "XOR \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle>  = \<t>"
    by (metis NOR_is_pullback XOR_type comp_type is_pullback_def  true_false_only_truth_values)
  then obtain j where j_def: "j \<in>\<^sub>c \<one>\<Coprod>\<one> \<and> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>) \<circ>\<^sub>c j  = \<langle>\<f>,\<f>\<rangle>"
    by (typecheck_cfuncs, auto, smt (verit, ccfv_threshold) XOR_is_pullback id_right_unit2 id_type is_pullback_def)
  show False
  proof(cases "j = left_coproj \<one> \<one>")
    assume "j = left_coproj \<one> \<one>"
    then have "(\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>) \<circ>\<^sub>c j  = \<langle>\<t>, \<f>\<rangle>"
      using  left_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
    then have "\<langle>\<t>, \<f>\<rangle> = \<langle>\<f>,\<f>\<rangle>"
      using j_def by auto
    then have "\<t> = \<f>"
      using cart_prod_eq2 false_func_type true_func_type by auto
    then show False
      using true_false_distinct by auto
  next
    assume "j \<noteq> left_coproj \<one> \<one>"
    then have "j = right_coproj \<one> \<one>"
      by (meson j_def maps_into_1u1)
    then have "(\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>) \<circ>\<^sub>c j  = \<langle>\<f>, \<t>\<rangle>"
      using  right_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
    then have "\<langle>\<f>, \<t>\<rangle> = \<langle>\<f>,\<f>\<rangle>"
      using j_def by auto
    then have "\<t> = \<f>"
      using cart_prod_eq2 false_func_type true_func_type by auto
    then show False
      using true_false_distinct by auto
  qed
qed

lemma XOR_true_true_is_false:
   "XOR \<circ>\<^sub>c  \<langle>\<t>,\<t>\<rangle> = \<f>"
proof(rule ccontr)
  assume "XOR \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle> \<noteq> \<f>"
  then have "XOR \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle>  = \<t>"
    by (metis XOR_type comp_type diag_on_elements diagonal_type true_false_only_truth_values true_func_type)
  then obtain j where j_def: "j \<in>\<^sub>c \<one>\<Coprod>\<one> \<and> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>) \<circ>\<^sub>c j  = \<langle>\<t>,\<t>\<rangle>"
    by (typecheck_cfuncs, auto, smt (verit, ccfv_threshold) XOR_is_pullback id_right_unit2 id_type is_pullback_def)
  show False
  proof(cases "j = left_coproj \<one> \<one>")
    assume "j = left_coproj \<one> \<one>"
    then have "(\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>) \<circ>\<^sub>c j  = \<langle>\<t>, \<f>\<rangle>"
      using  left_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
    then have "\<langle>\<t>, \<f>\<rangle> = \<langle>\<t>,\<t>\<rangle>"
      using j_def by auto
    then have "\<t> = \<f>"
      using cart_prod_eq2 false_func_type true_func_type by auto
    then show False
      using true_false_distinct by auto
  next
    assume "j \<noteq> left_coproj \<one> \<one>"
    then have "j = right_coproj \<one> \<one>"
      by (meson j_def maps_into_1u1)
    then have "(\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>) \<circ>\<^sub>c j  = \<langle>\<f>, \<t>\<rangle>"
      using  right_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
    then have "\<langle>\<f>, \<t>\<rangle> = \<langle>\<t>,\<t>\<rangle>"
      using j_def by auto
    then have "\<t> = \<f>"
      using cart_prod_eq2 false_func_type true_func_type by auto
    then show False
      using true_false_distinct by auto
  qed
qed

subsection \<open>NAND\<close>
definition NAND :: "cfunc" where
  "NAND = (THE \<chi>. is_pullback (\<one>\<Coprod>(\<one>\<Coprod>\<one>)) \<one> (\<Omega> \<times>\<^sub>c \<Omega>) \<Omega> (\<beta>\<^bsub>(\<one>\<Coprod>(\<one>\<Coprod>\<one>))\<^esub>) \<t> (\<langle>\<f>, \<f>\<rangle>\<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<chi>)"

lemma pre_NAND_type[type_rule]: 
  "\<langle>\<f>, \<f>\<rangle> \<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg> \<langle>\<f>, \<t>\<rangle>) : \<one>\<Coprod>(\<one>\<Coprod>\<one>) \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega>"
  by typecheck_cfuncs

lemma pre_NAND_injective:
  "injective(\<langle>\<f>, \<f>\<rangle> \<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg> \<langle>\<f>, \<t>\<rangle>))"
  unfolding injective_def
proof(clarify)
  fix x y 
  assume x_type: "x \<in>\<^sub>c domain (\<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle>)" 
  then have x_type': "x \<in>\<^sub>c \<one> \<Coprod> (\<one>\<Coprod>\<one>)"  
    using cfunc_type_def pre_NAND_type by force
  then have x_form: "(\<exists> w. w \<in>\<^sub>c \<one> \<and> x = left_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c w)
      \<or>  (\<exists> w. w \<in>\<^sub>c \<one>\<Coprod>\<one> \<and> x = right_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c w)"
    using coprojs_jointly_surj by auto

  assume y_type: "y \<in>\<^sub>c domain (\<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle>)" 
  then have y_type': "y \<in>\<^sub>c \<one>\<Coprod> (\<one>\<Coprod>\<one>)"  
    using cfunc_type_def pre_NAND_type by force
  then have y_form: "(\<exists> w. w \<in>\<^sub>c \<one> \<and> y = left_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c w)
      \<or>  (\<exists> w. w \<in>\<^sub>c \<one>\<Coprod>\<one> \<and> y = right_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c w)"
    using coprojs_jointly_surj by auto

  assume mx_eqs_my: "\<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c x = \<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c y"

  have f1: "\<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c left_coproj \<one> (\<one> \<Coprod> \<one>) = \<langle>\<f>, \<f>\<rangle>"
    by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
  have f2: "\<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c (right_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c left_coproj \<one> \<one>) = \<langle>\<t>,\<f>\<rangle>"
  proof- 
    have "\<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c right_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c left_coproj \<one> \<one> = 
          (\<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c right_coproj \<one> (\<one>\<Coprod>\<one>)) \<circ>\<^sub>c left_coproj \<one> \<one>"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c left_coproj \<one> \<one>"
      using right_coproj_cfunc_coprod by (typecheck_cfuncs, smt)
    also have "... = \<langle>\<t>,\<f>\<rangle>"
      by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
    finally show ?thesis.
  qed
  have f3: "\<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c (right_coproj \<one> (\<one>\<Coprod>\<one>)\<circ>\<^sub>c right_coproj \<one> \<one>) = \<langle>\<f>,\<t>\<rangle>"
  proof- 
    have "\<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c (right_coproj \<one> (\<one>\<Coprod>\<one>)\<circ>\<^sub>c right_coproj \<one> \<one>) = 
          (\<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c right_coproj \<one> (\<one>\<Coprod>\<one>) )\<circ>\<^sub>c right_coproj \<one> \<one>"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = \<langle>\<t>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c right_coproj \<one> \<one>"
      using right_coproj_cfunc_coprod by (typecheck_cfuncs, smt)
    also have "... = \<langle>\<f>,\<t>\<rangle>"
      by (typecheck_cfuncs, simp add: right_coproj_cfunc_coprod)
    finally show ?thesis.
  qed
  show "x = y"
  proof(cases "x = left_coproj \<one> (\<one> \<Coprod> \<one>)")
    assume case1: "x = left_coproj \<one> (\<one> \<Coprod> \<one>)"
    then show "x = y"
      by (typecheck_cfuncs, smt (z3) mx_eqs_my element_pair_eq f1 f2 f3 false_func_type maps_into_1u1 terminal_func_unique true_false_distinct true_func_type x_form y_form)
  next
    assume not_case1: "x \<noteq> left_coproj \<one> (\<one> \<Coprod> \<one>)"
    then have case2_or_3: "x = right_coproj \<one> (\<one>\<Coprod>\<one>)\<circ>\<^sub>c left_coproj \<one> \<one> \<or> 
               x = right_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c right_coproj \<one> \<one>"
      by (metis id_right_unit2 id_type left_proj_type maps_into_1u1 terminal_func_unique x_form)
    show "x = y"
    proof(cases "x = right_coproj \<one> (\<one>\<Coprod>\<one>)\<circ>\<^sub>c left_coproj \<one> \<one>")
      assume case2: "x = right_coproj \<one> (\<one> \<Coprod> \<one>) \<circ>\<^sub>c left_coproj \<one> \<one>"
      then show "x = y"
        by (smt (z3) NOT_false_is_true NOT_is_pullback NOT_true_is_false NOT_type x_type x_type' cart_prod_eq2 case2 cfunc_type_def characteristic_func_eq characteristic_func_is_pullback characteristic_function_exists comp_associative diag_on_elements diagonal_type element_monomorphism f1 f2 f3 false_func_type left_proj_type maps_into_1u1 mx_eqs_my terminal_func_unique true_false_distinct true_func_type x_type y_form)
    next
      assume not_case2: "x \<noteq> right_coproj \<one> (\<one> \<Coprod> \<one>) \<circ>\<^sub>c left_coproj \<one> \<one>"
      then have case3: "x = right_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c right_coproj \<one> \<one>"
        using case2_or_3 by blast
      then show "x = y"
        by (smt (z3) NOT_false_is_true NOT_is_pullback NOT_true_is_false NOT_type x_type x_type' cart_prod_eq2 case3 cfunc_type_def characteristic_func_eq characteristic_func_is_pullback characteristic_function_exists comp_associative diag_on_elements diagonal_type element_monomorphism f1 f2 f3 false_func_type left_proj_type maps_into_1u1 mx_eqs_my terminal_func_unique true_false_distinct true_func_type x_type y_form)
    qed
  qed
qed

lemma NAND_is_pullback:
  "is_pullback (\<one>\<Coprod>(\<one>\<Coprod>\<one>)) \<one> (\<Omega>\<times>\<^sub>c\<Omega>) \<Omega> (\<beta>\<^bsub>(\<one>\<Coprod>(\<one>\<Coprod>\<one>))\<^esub>) \<t> (\<langle>\<f>, \<f>\<rangle>\<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) NAND"
  unfolding NAND_def
  using element_monomorphism characteristic_function_exists
  by (typecheck_cfuncs, simp add: the1I2 injective_imp_monomorphism pre_NAND_injective)
      
lemma NAND_type[type_rule]:
  "NAND : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega>"
  unfolding NAND_def
  by (metis NAND_def NAND_is_pullback is_pullback_def) 

lemma NAND_left_false_is_true:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "NAND \<circ>\<^sub>c \<langle>\<f>,p\<rangle> = \<t>"
proof - 
  have "\<exists> j. j \<in>\<^sub>c \<one>\<Coprod>(\<one>\<Coprod>\<one>) \<and> (\<langle>\<f>, \<f>\<rangle> \<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<circ>\<^sub>c j  = \<langle>\<f>,p\<rangle>"
    by (typecheck_cfuncs, smt (z3) assms comp_associative2 comp_type left_coproj_cfunc_coprod left_proj_type right_coproj_cfunc_coprod right_proj_type true_false_only_truth_values)
  then show ?thesis 
    by (typecheck_cfuncs, smt (verit, ccfv_threshold) NAND_is_pullback comp_associative2 id_right_unit2 is_pullback_def terminal_func_comp_elem)
qed

lemma NAND_right_false_is_true:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "NAND \<circ>\<^sub>c \<langle>p,\<f>\<rangle> = \<t>"
proof - 
  have "\<exists> j. j \<in>\<^sub>c \<one>\<Coprod>(\<one>\<Coprod>\<one>) \<and> (\<langle>\<f>, \<f>\<rangle>\<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<circ>\<^sub>c j  = \<langle>p,\<f>\<rangle>"
    by (typecheck_cfuncs, smt (z3) assms comp_associative2 comp_type left_coproj_cfunc_coprod left_proj_type right_coproj_cfunc_coprod right_proj_type true_false_only_truth_values)
  then show ?thesis 
    by (typecheck_cfuncs, smt (verit, ccfv_SIG) NAND_is_pullback NOT_false_is_true NOT_is_pullback  comp_associative2 is_pullback_def  terminal_func_comp)
qed

lemma NAND_true_true_is_false:
 "NAND \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle> = \<f>"
proof(rule ccontr)
  assume "NAND \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle> \<noteq> \<f>"
  then have "NAND \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle> = \<t>"
    using  true_false_only_truth_values by (typecheck_cfuncs, blast)
  then obtain j where j_type[type_rule]:  "j \<in>\<^sub>c \<one>\<Coprod>(\<one>\<Coprod>\<one>)" and j_def: "(\<langle>\<f>, \<f>\<rangle>\<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<circ>\<^sub>c j  = \<langle>\<t>,\<t>\<rangle>"
    using NAND_is_pullback unfolding is_pullback_def
    by (typecheck_cfuncs, smt (z3) NAND_is_pullback id_right_unit2 id_type)
  then have trichotomy: "(\<langle>\<f>,\<f>\<rangle> = \<langle>\<t>,\<t>\<rangle>) \<or> (\<langle>\<t>, \<f>\<rangle> = \<langle>\<t>,\<t>\<rangle>) \<or> (\<langle>\<f>, \<t>\<rangle> = \<langle>\<t>,\<t>\<rangle>)"
  proof(cases "j = left_coproj \<one> (\<one> \<Coprod> \<one>)")
    assume case1: "j = left_coproj \<one> (\<one> \<Coprod> \<one>)"
    then show ?thesis
      by (metis cfunc_coprod_type cfunc_prod_type false_func_type j_def left_coproj_cfunc_coprod true_func_type)
  next
    assume not_case1: "j \<noteq> left_coproj \<one> (\<one> \<Coprod> \<one>)"
    then have case2_or_3: "j = right_coproj \<one> (\<one>\<Coprod>\<one>)\<circ>\<^sub>c left_coproj \<one> \<one> \<or> 
               j = right_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c right_coproj \<one> \<one>"
      using not_case1 set_three by (typecheck_cfuncs, auto)
    show ?thesis
    proof(cases "j = right_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c left_coproj \<one> \<one>")
      assume case2: "j = right_coproj \<one> (\<one> \<Coprod> \<one>) \<circ>\<^sub>c left_coproj \<one> \<one>"
      have "\<langle>\<t>, \<f>\<rangle> = \<langle>\<t>,\<t>\<rangle>"
      proof - 
        have "(\<langle>\<f>, \<f>\<rangle>\<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<circ>\<^sub>c j = ((\<langle>\<f>, \<f>\<rangle>\<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<circ>\<^sub>c right_coproj \<one> (\<one> \<Coprod> \<one>)) \<circ>\<^sub>c left_coproj \<one> \<one>"
          by (typecheck_cfuncs, simp add: case2 comp_associative2)
        also have "... = (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>) \<circ>\<^sub>c left_coproj \<one> \<one>"
          using right_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
        also have "... = \<langle>\<t>, \<f>\<rangle>"
          by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
        finally show ?thesis
          using j_def by simp
      qed
      then show ?thesis
        by blast
    next
      assume not_case2: "j \<noteq> right_coproj \<one> (\<one> \<Coprod> \<one>) \<circ>\<^sub>c left_coproj \<one> \<one>"
      then have case3: "j = right_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c right_coproj \<one> \<one>"
        using case2_or_3 by blast
      have "\<langle>\<f>, \<t>\<rangle> = \<langle>\<t>,\<t>\<rangle>"
      proof - 
        have "(\<langle>\<f>, \<f>\<rangle>\<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<circ>\<^sub>c j = ((\<langle>\<f>, \<f>\<rangle>\<amalg> (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<circ>\<^sub>c right_coproj \<one> (\<one> \<Coprod> \<one>)) \<circ>\<^sub>c right_coproj \<one> \<one>"
          by (typecheck_cfuncs, simp add: case3 comp_associative2)
        also have "... = (\<langle>\<t>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>) \<circ>\<^sub>c right_coproj \<one> \<one>"
          using right_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
        also have "... = \<langle>\<f>, \<t>\<rangle>"
          by (typecheck_cfuncs, simp add: right_coproj_cfunc_coprod)
        finally show ?thesis
          using j_def by simp
      qed
      then show ?thesis
        by blast
    qed
  qed
    then have "\<t> = \<f>"
      using trichotomy cart_prod_eq2 by (typecheck_cfuncs, force)
    then show False
      using true_false_distinct by auto  
qed

lemma NAND_true_implies_one_is_false:
  assumes "p \<in>\<^sub>c \<Omega>" 
  assumes "q \<in>\<^sub>c \<Omega>"
  assumes "NAND \<circ>\<^sub>c \<langle>p,q\<rangle> = \<t>"
  shows "p = \<f> \<or> q = \<f>"
  by (metis (no_types) NAND_true_true_is_false assms true_false_only_truth_values)

lemma NOT_AND_is_NAND:
 "NAND = NOT \<circ>\<^sub>c AND"
proof(etcs_rule one_separator)
  fix x 
  assume x_type: "x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>"
  then obtain p q where x_def: "p \<in>\<^sub>c \<Omega> \<and> q \<in>\<^sub>c \<Omega> \<and> x = \<langle>p,q\<rangle>"
    by (meson cart_prod_decomp)
  show "NAND \<circ>\<^sub>c x = (NOT \<circ>\<^sub>c AND) \<circ>\<^sub>c x"
    by (typecheck_cfuncs, metis AND_false_left_is_false AND_false_right_is_false AND_true_true_is_true NAND_left_false_is_true NAND_right_false_is_true NAND_true_implies_one_is_false NOT_false_is_true NOT_true_is_false comp_associative2 true_false_only_truth_values x_def x_type)
qed

lemma NAND_not_idempotent:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "NAND \<circ>\<^sub>c \<langle>p,p\<rangle> = NOT \<circ>\<^sub>c p"
  using NAND_right_false_is_true NAND_true_true_is_false NOT_false_is_true NOT_true_is_false assms true_false_only_truth_values by fastforce

subsection \<open>IFF\<close>

definition IFF :: "cfunc" where
  "IFF = (THE \<chi>. is_pullback (\<one>\<Coprod>\<one>) \<one> (\<Omega> \<times>\<^sub>c \<Omega>) \<Omega> (\<beta>\<^bsub>(\<one>\<Coprod>\<one>)\<^esub>) \<t> (\<langle>\<t>, \<t>\<rangle> \<amalg>\<langle>\<f>, \<f>\<rangle>) \<chi>)"

lemma pre_IFF_type[type_rule]: 
  "\<langle>\<t>, \<t>\<rangle> \<amalg> \<langle>\<f>, \<f>\<rangle> : \<one>\<Coprod>\<one> \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega>"
  by typecheck_cfuncs

lemma pre_IFF_injective:
 "injective(\<langle>\<t>, \<t>\<rangle> \<amalg>\<langle>\<f>, \<f>\<rangle>)"
 unfolding injective_def
proof(clarify)
  fix x y 
  assume "x \<in>\<^sub>c domain (\<langle>\<t>, \<t>\<rangle> \<amalg>\<langle>\<f>, \<f>\<rangle>)" 
  then have x_type: "x \<in>\<^sub>c (\<one>\<Coprod>\<one>)"  
    using cfunc_type_def pre_IFF_type by force
  then have x_form: "(\<exists> w. (w \<in>\<^sub>c \<one> \<and> x = (left_coproj \<one> \<one>) \<circ>\<^sub>c w))
      \<or>  (\<exists> w. (w \<in>\<^sub>c \<one> \<and> x = (right_coproj \<one> \<one>) \<circ>\<^sub>c w))"
    using coprojs_jointly_surj by auto

  assume "y \<in>\<^sub>c domain (\<langle>\<t>, \<t>\<rangle> \<amalg>\<langle>\<f>, \<f>\<rangle>)" 
  then have y_type: "y \<in>\<^sub>c (\<one>\<Coprod>\<one>)"  
    using cfunc_type_def pre_IFF_type by force
  then have y_form: "(\<exists> w. (w \<in>\<^sub>c \<one> \<and> y = (left_coproj \<one> \<one>) \<circ>\<^sub>c w))
      \<or>  (\<exists> w. (w \<in>\<^sub>c \<one> \<and> y = (right_coproj \<one> \<one>) \<circ>\<^sub>c w))"
    using coprojs_jointly_surj by auto

  assume eqs: "\<langle>\<t>, \<t>\<rangle> \<amalg>\<langle>\<f>, \<f>\<rangle> \<circ>\<^sub>c x = \<langle>\<t>, \<t>\<rangle> \<amalg>\<langle>\<f>, \<f>\<rangle> \<circ>\<^sub>c y"

  show "x = y"
  proof(cases "\<exists> w. w \<in>\<^sub>c \<one> \<and> x = left_coproj \<one> \<one> \<circ>\<^sub>c w")
    assume a1: "\<exists> w. w \<in>\<^sub>c \<one> \<and> x = left_coproj \<one> \<one> \<circ>\<^sub>c w"
    then obtain w where x_def: "w \<in>\<^sub>c \<one> \<and> x = left_coproj \<one> \<one> \<circ>\<^sub>c w"
      by blast
    then have "w = id \<one>"
      by (typecheck_cfuncs, metis terminal_func_unique x_def)
    have "\<exists> v. v \<in>\<^sub>c \<one> \<and> y = left_coproj \<one> \<one> \<circ>\<^sub>c v"
    proof(rule ccontr)
      assume a2: "\<nexists>v. v \<in>\<^sub>c \<one> \<and> y = left_coproj \<one> \<one> \<circ>\<^sub>c v"
      then obtain v where y_def:  "v \<in>\<^sub>c \<one> \<and> y = right_coproj \<one> \<one> \<circ>\<^sub>c v"
        using y_form by (typecheck_cfuncs, blast)
      then have "v = id \<one>"
        by (typecheck_cfuncs, metis terminal_func_unique y_def)
      then have "\<langle>\<t>, \<t>\<rangle> \<amalg>\<langle>\<f>, \<f>\<rangle> \<circ>\<^sub>c left_coproj \<one> \<one> = \<langle>\<t>, \<t>\<rangle> \<amalg>\<langle>\<f>, \<f>\<rangle> \<circ>\<^sub>c right_coproj \<one> \<one>"
        using \<open>v = id\<^sub>c \<one>\<close> \<open>w = id\<^sub>c \<one>\<close> eqs id_right_unit2 x_def y_def by (typecheck_cfuncs, force)
      then have "\<langle>\<t>, \<t>\<rangle> = \<langle>\<f>,\<f>\<rangle>"
        by (typecheck_cfuncs, smt (z3)  cfunc_coprod_unique coprod_eq2 pre_IFF_type right_coproj_cfunc_coprod)      
      then have "\<t> = \<f>"
        using cart_prod_eq2 false_func_type true_func_type by blast
      then show False
        using true_false_distinct by blast
    qed
    then obtain v where y_def: "v \<in>\<^sub>c \<one> \<and> y = left_coproj \<one> \<one> \<circ>\<^sub>c v"
      by blast
    then have "v = id \<one>"
      by (typecheck_cfuncs, metis terminal_func_unique)
    then show ?thesis
      by (simp add: \<open>w = id\<^sub>c \<one>\<close> x_def y_def)
  next
    assume "\<nexists>w. w \<in>\<^sub>c \<one> \<and> x = left_coproj \<one> \<one> \<circ>\<^sub>c w"
    then obtain w where x_def: "w \<in>\<^sub>c \<one> \<and> x = right_coproj \<one> \<one> \<circ>\<^sub>c w"
      using x_form by force
    then have "w = id \<one>"
      by (typecheck_cfuncs, metis terminal_func_unique x_def)
    have "\<exists> v. v \<in>\<^sub>c \<one> \<and> y = right_coproj \<one> \<one> \<circ>\<^sub>c v"
    proof(rule ccontr)
      assume a2: "\<nexists>v. v \<in>\<^sub>c \<one> \<and> y = right_coproj \<one> \<one> \<circ>\<^sub>c v"
      then obtain v where y_def:  "v \<in>\<^sub>c \<one> \<and> y = left_coproj \<one> \<one> \<circ>\<^sub>c v"
        using y_form by (typecheck_cfuncs, blast)
      then have "v = id \<one>"
        by (typecheck_cfuncs, metis terminal_func_unique y_def)
      then have "\<langle>\<t>, \<t>\<rangle> \<amalg>\<langle>\<f>, \<f>\<rangle> \<circ>\<^sub>c left_coproj \<one> \<one> = \<langle>\<t>, \<t>\<rangle> \<amalg>\<langle>\<f>, \<f>\<rangle> \<circ>\<^sub>c right_coproj \<one> \<one>"
        using \<open>v = id\<^sub>c \<one>\<close> \<open>w = id\<^sub>c \<one>\<close> eqs id_right_unit2 x_def y_def by (typecheck_cfuncs, force)
      then have "\<langle>\<t>, \<t>\<rangle> = \<langle>\<f>, \<f>\<rangle>"
        by (typecheck_cfuncs, smt (z3)  cfunc_coprod_unique coprod_eq2 pre_IFF_type right_coproj_cfunc_coprod)      
      then have "\<t> = \<f>"
        using cart_prod_eq2 false_func_type true_func_type by blast
      then show False
        using true_false_distinct by blast
    qed
    then obtain v where y_def: "v \<in>\<^sub>c \<one> \<and> y = (right_coproj \<one> \<one>) \<circ>\<^sub>c v"
      by blast
    then have "v = id \<one>"
      by (typecheck_cfuncs, metis terminal_func_unique)
    then show ?thesis
      by (simp add: \<open>w = id\<^sub>c \<one>\<close> x_def y_def)
  qed
qed

lemma IFF_is_pullback:
  "is_pullback (\<one>\<Coprod>\<one>) \<one> (\<Omega>\<times>\<^sub>c\<Omega>) \<Omega> (\<beta>\<^bsub>(\<one>\<Coprod>\<one>)\<^esub>) \<t> (\<langle>\<t>, \<t>\<rangle> \<amalg>\<langle>\<f>, \<f>\<rangle>) IFF"
  unfolding IFF_def
  using element_monomorphism characteristic_function_exists
  by (typecheck_cfuncs, simp add: the1I2 injective_imp_monomorphism pre_IFF_injective)

lemma IFF_type[type_rule]:
  "IFF : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega>"
  unfolding IFF_def
  by (metis IFF_def IFF_is_pullback is_pullback_def)

lemma IFF_true_true_is_true:
 "IFF \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle> = \<t>"
proof - 
  have "\<exists> j. j \<in>\<^sub>c (\<one>\<Coprod>\<one>) \<and> (\<langle>\<t>, \<t>\<rangle> \<amalg>\<langle>\<f>, \<f>\<rangle>) \<circ>\<^sub>c j  = \<langle>\<t>,\<t>\<rangle>"
    by (typecheck_cfuncs, smt (z3)  comp_associative2 comp_type left_coproj_cfunc_coprod left_proj_type right_coproj_cfunc_coprod right_proj_type true_false_only_truth_values)
  then show ?thesis 
    by (smt (verit, ccfv_threshold) AND_is_pullback AND_true_true_is_true IFF_is_pullback comp_associative2 is_pullback_def  terminal_func_comp)
qed

lemma IFF_false_false_is_true:
 "IFF \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle> = \<t>"
proof - 
  have "\<exists> j. j \<in>\<^sub>c (\<one>\<Coprod>\<one>) \<and> (\<langle>\<t>, \<t>\<rangle> \<amalg>\<langle>\<f>, \<f>\<rangle>) \<circ>\<^sub>c j  = \<langle>\<f>,\<f>\<rangle>"
    by (typecheck_cfuncs, smt (z3)  comp_associative2 comp_type left_coproj_cfunc_coprod left_proj_type right_coproj_cfunc_coprod right_proj_type true_false_only_truth_values)
  then show ?thesis 
    by (smt (verit, ccfv_threshold) AND_is_pullback AND_true_true_is_true IFF_is_pullback comp_associative2 is_pullback_def  terminal_func_comp)
qed

lemma IFF_true_false_is_false:
 "IFF \<circ>\<^sub>c \<langle>\<t>,\<f>\<rangle> = \<f>"
proof(rule ccontr)
  assume "IFF \<circ>\<^sub>c \<langle>\<t>,\<f>\<rangle> \<noteq> \<f>"
  then have "IFF \<circ>\<^sub>c \<langle>\<t>,\<f>\<rangle>  = \<t>"
    using true_false_only_truth_values by (typecheck_cfuncs, blast)    
  then obtain j where j_type[type_rule]: "j \<in>\<^sub>c \<one>\<Coprod>\<one> \<and> (\<langle>\<t>, \<t>\<rangle> \<amalg>\<langle>\<f>, \<f>\<rangle>) \<circ>\<^sub>c j  = \<langle>\<t>,\<f>\<rangle>"
    by (typecheck_cfuncs, smt (verit, ccfv_threshold) IFF_is_pullback characteristic_function_exists element_monomorphism is_pullback_def)
  show False
  proof(cases "j = left_coproj \<one> \<one>")
    assume "j = left_coproj \<one> \<one>"
    then have "(\<langle>\<t>, \<t>\<rangle> \<amalg>\<langle>\<f>, \<f>\<rangle>) \<circ>\<^sub>c j  = \<langle>\<t>, \<t>\<rangle>"
      using  left_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
    then have "\<langle>\<t>, \<f>\<rangle> = \<langle>\<t>,\<t>\<rangle>"
      using  j_type by argo
    then have "\<t> = \<f>"
      using cart_prod_eq2 false_func_type true_func_type by auto
    then show False
      using true_false_distinct by auto
  next
    assume "j \<noteq> left_coproj \<one> \<one>"
    then have "j = right_coproj \<one> \<one>"
      using j_type maps_into_1u1 by auto
    then have "(\<langle>\<t>, \<t>\<rangle> \<amalg>\<langle>\<f>, \<f>\<rangle>) \<circ>\<^sub>c j  = \<langle>\<f>, \<f>\<rangle>"
      using  right_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
    then have "\<langle>\<f>, \<t>\<rangle> = \<langle>\<f>, \<f>\<rangle>"
      using XOR_false_false_is_false XOR_only_true_left_is_true j_type by argo
    then have "\<t> = \<f>"
      using cart_prod_eq2 false_func_type true_func_type by auto
    then show False
      using true_false_distinct by auto
 qed
qed

lemma IFF_false_true_is_false:
 "IFF \<circ>\<^sub>c \<langle>\<f>,\<t>\<rangle> = \<f>"
proof(rule ccontr)
  assume "IFF \<circ>\<^sub>c \<langle>\<f>,\<t>\<rangle> \<noteq> \<f>"
  then have "IFF \<circ>\<^sub>c \<langle>\<f>,\<t>\<rangle>  = \<t>"
    using true_false_only_truth_values by (typecheck_cfuncs, blast)
  then obtain j where j_type[type_rule]: "j \<in>\<^sub>c \<one>\<Coprod>\<one>" and j_def:  "(\<langle>\<t>, \<t>\<rangle> \<amalg>\<langle>\<f>, \<f>\<rangle>) \<circ>\<^sub>c j  = \<langle>\<f>,\<t>\<rangle>"
    by (typecheck_cfuncs, smt (verit, ccfv_threshold) IFF_is_pullback id_right_unit2 is_pullback_def one_unique_element terminal_func_comp terminal_func_comp_elem terminal_func_unique)
  show False
  proof(cases "j = left_coproj \<one> \<one>")
    assume "j = left_coproj \<one> \<one>"
    then have "(\<langle>\<t>, \<t>\<rangle> \<amalg>\<langle>\<f>, \<f>\<rangle>) \<circ>\<^sub>c j  = \<langle>\<t>, \<t>\<rangle>"
      using  left_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
    then have "\<langle>\<f>,\<t>\<rangle> = \<langle>\<t>,\<t>\<rangle>"
      using j_def by auto
    then have "\<t> = \<f>"
      using cart_prod_eq2 false_func_type true_func_type by auto
    then show False
      using true_false_distinct by auto
  next
    assume "j \<noteq> left_coproj \<one> \<one>"
    then have "j = right_coproj \<one> \<one>"
      using j_type maps_into_1u1 by blast
    then have "(\<langle>\<t>, \<t>\<rangle> \<amalg>\<langle>\<f>, \<f>\<rangle>) \<circ>\<^sub>c j  = \<langle>\<f>, \<f>\<rangle>"
      using  right_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
    then have "\<langle>\<f>,\<t>\<rangle> = \<langle>\<f>, \<f>\<rangle>"
      using XOR_false_false_is_false XOR_only_true_left_is_true j_def by fastforce
    then have "\<t> = \<f>"
      using cart_prod_eq2 false_func_type true_func_type by auto
    then show False
      using true_false_distinct by auto
 qed
qed

lemma NOT_IFF_is_XOR: 
  "NOT \<circ>\<^sub>c IFF = XOR"
proof(etcs_rule one_separator)
  fix x   
  assume x_type: "x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>"
  then obtain u w where x_def: "u \<in>\<^sub>c \<Omega> \<and> w \<in>\<^sub>c \<Omega> \<and> x = \<langle>u,w\<rangle>"
    using cart_prod_decomp by blast
  show "(NOT \<circ>\<^sub>c IFF) \<circ>\<^sub>c x = XOR \<circ>\<^sub>c x"
  proof(cases "u = \<t>")
    show "(NOT \<circ>\<^sub>c IFF) \<circ>\<^sub>c x = XOR \<circ>\<^sub>c x"
    proof(cases "w = \<t>")
      show "(NOT \<circ>\<^sub>c IFF) \<circ>\<^sub>c x = XOR \<circ>\<^sub>c x"
        by (metis IFF_false_false_is_true IFF_false_true_is_false IFF_true_false_is_false IFF_true_true_is_true IFF_type NOT_false_is_true NOT_true_is_false NOT_type XOR_false_false_is_false XOR_only_true_left_is_true XOR_only_true_right_is_true XOR_true_true_is_false cfunc_type_def comp_associative true_false_only_truth_values x_def x_type)
    next 
      assume "w \<noteq> \<t>"
      then have "w = \<f>"
        by (metis true_false_only_truth_values x_def)
      then show "(NOT \<circ>\<^sub>c IFF) \<circ>\<^sub>c x = XOR \<circ>\<^sub>c x"
        by (metis IFF_false_false_is_true IFF_true_false_is_false IFF_type NOT_false_is_true NOT_true_is_false NOT_type XOR_false_false_is_false XOR_only_true_left_is_true comp_associative2 true_false_only_truth_values x_def x_type)
    qed
  next 
    assume "u \<noteq> \<t>"
    then have "u = \<f>"
      by (metis true_false_only_truth_values x_def)
    show "(NOT \<circ>\<^sub>c IFF) \<circ>\<^sub>c x = XOR \<circ>\<^sub>c x"
    proof(cases "w = \<t>")
      show "(NOT \<circ>\<^sub>c IFF) \<circ>\<^sub>c x = XOR \<circ>\<^sub>c x"
        by (metis IFF_false_false_is_true IFF_false_true_is_false IFF_type NOT_false_is_true NOT_true_is_false NOT_type XOR_false_false_is_false XOR_only_true_right_is_true \<open>u = \<f>\<close> comp_associative2 true_false_only_truth_values x_def x_type)
    next
      assume "w \<noteq> \<t>"
      then have "w = \<f>"
        by (metis true_false_only_truth_values x_def)
      then show "(NOT \<circ>\<^sub>c IFF) \<circ>\<^sub>c x = XOR \<circ>\<^sub>c x"
        by (metis IFF_false_false_is_true IFF_type NOT_true_is_false NOT_type XOR_false_false_is_false \<open>u = \<f>\<close> cfunc_type_def comp_associative x_def x_type)
    qed
  qed
qed

subsection \<open>IMPLIES\<close>

definition IMPLIES :: "cfunc" where
  "IMPLIES = (THE \<chi>. is_pullback (\<one>\<Coprod>(\<one>\<Coprod>\<one>)) \<one> (\<Omega>\<times>\<^sub>c\<Omega>) \<Omega> (\<beta>\<^bsub>(\<one>\<Coprod>(\<one>\<Coprod>\<one>))\<^esub>) \<t> (\<langle>\<t>, \<t>\<rangle>\<amalg> (\<langle>\<f>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<chi>)"

lemma pre_IMPLIES_type[type_rule]: 
  "\<langle>\<t>, \<t>\<rangle> \<amalg> (\<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<f>, \<t>\<rangle>) : \<one> \<Coprod> (\<one> \<Coprod> \<one>) \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega>"
  by typecheck_cfuncs

lemma pre_IMPLIES_injective:
  "injective(\<langle>\<t>, \<t>\<rangle> \<amalg> (\<langle>\<f>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>))"
  unfolding injective_def
proof(clarify)
  fix x y 
  assume a1: "x \<in>\<^sub>c domain (\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle>)" 
  then have x_type[type_rule]: "x \<in>\<^sub>c (\<one>\<Coprod>(\<one>\<Coprod>\<one>))"  
    using cfunc_type_def pre_IMPLIES_type by force
  then have x_form: "(\<exists> w. (w \<in>\<^sub>c \<one> \<and> x = (left_coproj \<one> (\<one>\<Coprod>\<one>)) \<circ>\<^sub>c w))
      \<or>  (\<exists> w. (w \<in>\<^sub>c (\<one>\<Coprod>\<one>) \<and> x = (right_coproj \<one> (\<one>\<Coprod>\<one>)) \<circ>\<^sub>c w))"
    using coprojs_jointly_surj by auto

  assume "y \<in>\<^sub>c domain (\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle>)" 
  then have y_type: "y \<in>\<^sub>c (\<one>\<Coprod>(\<one>\<Coprod>\<one>))"  
    using cfunc_type_def pre_IMPLIES_type by force
  then have y_form: "(\<exists> w. (w \<in>\<^sub>c \<one> \<and> y = (left_coproj \<one> (\<one>\<Coprod>\<one>)) \<circ>\<^sub>c w))
      \<or>  (\<exists> w. (w \<in>\<^sub>c (\<one>\<Coprod>\<one>) \<and> y = (right_coproj \<one> (\<one>\<Coprod>\<one>)) \<circ>\<^sub>c w))"
    using coprojs_jointly_surj by auto

  assume mx_eqs_my: "\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c x = \<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c y"

  have f1: "\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c left_coproj \<one> (\<one> \<Coprod> \<one>) = \<langle>\<t>,\<t>\<rangle>"
    by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
  have f2: "\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c (right_coproj \<one> (\<one>\<Coprod>\<one>)\<circ>\<^sub>c left_coproj \<one> \<one>) = \<langle>\<f>, \<f>\<rangle>"
  proof- 
    have "\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c (right_coproj \<one> (\<one>\<Coprod>\<one>)\<circ>\<^sub>c left_coproj \<one> \<one>) = 
          (\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c right_coproj \<one> (\<one>\<Coprod>\<one>) )\<circ>\<^sub>c left_coproj \<one> \<one>"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = \<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c left_coproj \<one> \<one>"
      using right_coproj_cfunc_coprod by (typecheck_cfuncs, smt)
    also have "... = \<langle>\<f>, \<f>\<rangle>"
      by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
    finally show ?thesis.      
  qed
  have f3: "\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c (right_coproj \<one> (\<one>\<Coprod>\<one>)\<circ>\<^sub>c right_coproj \<one> \<one>) = \<langle>\<f>,\<t>\<rangle>"
  proof- 
    have "\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c right_coproj \<one> (\<one>\<Coprod>\<one>)\<circ>\<^sub>c right_coproj \<one> \<one> = 
          (\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c right_coproj \<one> (\<one>\<Coprod>\<one>))\<circ>\<^sub>c right_coproj \<one> \<one>"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = \<langle>\<f>, \<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c right_coproj \<one> \<one>"
      using right_coproj_cfunc_coprod by (typecheck_cfuncs, smt)
    also have "... = \<langle>\<f>,\<t>\<rangle>"
      by (typecheck_cfuncs, simp add: right_coproj_cfunc_coprod)
    finally show ?thesis.
  qed
  show "x = y"
  proof(cases "x = left_coproj \<one> (\<one> \<Coprod> \<one>)")
    assume case1: "x = left_coproj \<one> (\<one> \<Coprod> \<one>)"
    then show "x = y"
      by (typecheck_cfuncs, smt (z3) mx_eqs_my element_pair_eq f1 f2 f3 false_func_type maps_into_1u1 terminal_func_unique true_false_distinct true_func_type x_form y_form)
  next
    assume not_case1: "x \<noteq> left_coproj \<one> (\<one> \<Coprod> \<one>)"
    then have case2_or_3: "x = (right_coproj \<one> (\<one>\<Coprod>\<one>)\<circ>\<^sub>c left_coproj \<one> \<one>)\<or> 
               x = right_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c(right_coproj \<one> \<one>)"
      by (metis id_right_unit2 id_type left_proj_type maps_into_1u1 terminal_func_unique x_form)
    show "x = y"
    proof(cases "x = right_coproj \<one> (\<one>\<Coprod>\<one>)\<circ>\<^sub>c left_coproj \<one> \<one>")
      assume case2: "x = right_coproj \<one> (\<one> \<Coprod> \<one>) \<circ>\<^sub>c left_coproj \<one> \<one>"
      then show "x = y"
        by (typecheck_cfuncs, smt (z3) a1 NOT_false_is_true NOT_is_pullback  cart_prod_eq2 cfunc_prod_comp cfunc_type_def characteristic_func_eq characteristic_func_is_pullback characteristic_function_exists comp_associative element_monomorphism f1 f2 f3 false_func_type left_proj_type maps_into_1u1 mx_eqs_my terminal_func_unique true_false_distinct true_func_type y_form)
    next
      assume not_case2: "x \<noteq> right_coproj \<one> (\<one> \<Coprod> \<one>) \<circ>\<^sub>c left_coproj \<one> \<one>"
      then have case3: "x = right_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c(right_coproj \<one> \<one>)"
        using case2_or_3 by blast
      then show "x = y"
        by (smt (z3) NOT_false_is_true NOT_is_pullback a1 cart_prod_eq2 cfunc_type_def characteristic_func_eq characteristic_func_is_pullback characteristic_function_exists comp_associative diag_on_elements diagonal_type element_monomorphism f1 f2 f3 false_func_type left_proj_type maps_into_1u1 mx_eqs_my terminal_func_unique true_false_distinct true_func_type x_type y_form)
    qed
  qed
qed

lemma IMPLIES_is_pullback:
  "is_pullback (\<one>\<Coprod>(\<one>\<Coprod>\<one>)) \<one> (\<Omega>\<times>\<^sub>c\<Omega>) \<Omega> (\<beta>\<^bsub>(\<one>\<Coprod>(\<one>\<Coprod>\<one>))\<^esub>) \<t> (\<langle>\<t>, \<t>\<rangle>\<amalg> (\<langle>\<f>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) IMPLIES"
  unfolding IMPLIES_def
  using element_monomorphism characteristic_function_exists
  by (typecheck_cfuncs, simp add: the1I2 injective_imp_monomorphism pre_IMPLIES_injective)
      
lemma IMPLIES_type[type_rule]:
  "IMPLIES : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega>"
  unfolding IMPLIES_def
  by (metis IMPLIES_def IMPLIES_is_pullback is_pullback_def)

lemma IMPLIES_true_true_is_true:
  "IMPLIES \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle> = \<t>"
proof -   
  have "\<exists> j. j \<in>\<^sub>c \<one> \<Coprod> (\<one>\<Coprod>\<one>) \<and> (\<langle>\<t>, \<t>\<rangle>\<amalg> (\<langle>\<f>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<circ>\<^sub>c j  = \<langle>\<t>,\<t>\<rangle>"
    by (typecheck_cfuncs, meson left_coproj_cfunc_coprod left_proj_type)
  then show ?thesis
    by (smt (verit, ccfv_threshold) IMPLIES_is_pullback NOT_false_is_true NOT_is_pullback comp_associative2 is_pullback_def  terminal_func_comp)
qed 

lemma IMPLIES_false_true_is_true:
  "IMPLIES \<circ>\<^sub>c \<langle>\<f>,\<t>\<rangle> = \<t>"
proof -   
  have "\<exists> j. j \<in>\<^sub>c \<one>\<Coprod>(\<one>\<Coprod>\<one>) \<and> (\<langle>\<t>, \<t>\<rangle>\<amalg> (\<langle>\<f>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<circ>\<^sub>c j  = \<langle>\<f>,\<t>\<rangle>"
    by (typecheck_cfuncs, smt (z3) comp_associative2 comp_type right_coproj_cfunc_coprod right_proj_type)
  then show ?thesis
    by (smt (verit, ccfv_threshold) IMPLIES_is_pullback NOT_false_is_true NOT_is_pullback comp_associative2 is_pullback_def  terminal_func_comp)
qed 

lemma IMPLIES_false_false_is_true:
  "IMPLIES \<circ>\<^sub>c  \<langle>\<f>,\<f>\<rangle> = \<t>"
proof -   
  have "\<exists> j. j \<in>\<^sub>c \<one>\<Coprod>(\<one>\<Coprod>\<one>) \<and> (\<langle>\<t>, \<t>\<rangle>\<amalg> (\<langle>\<f>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<circ>\<^sub>c j  = \<langle>\<f>,\<f>\<rangle>"
    by (typecheck_cfuncs, smt (verit, ccfv_SIG) cfunc_type_def comp_associative comp_type left_coproj_cfunc_coprod left_proj_type right_coproj_cfunc_coprod right_proj_type)
  then show ?thesis
    by (smt (verit, ccfv_threshold) IMPLIES_is_pullback NOT_false_is_true NOT_is_pullback comp_associative2 is_pullback_def  terminal_func_comp)
qed 

lemma IMPLIES_true_false_is_false:
  "IMPLIES \<circ>\<^sub>c  \<langle>\<t>,\<f>\<rangle> = \<f>"
proof(rule ccontr)  
  assume "IMPLIES \<circ>\<^sub>c \<langle>\<t>,\<f>\<rangle> \<noteq> \<f>"
  then have "IMPLIES \<circ>\<^sub>c \<langle>\<t>,\<f>\<rangle> = \<t>"
    using true_false_only_truth_values by (typecheck_cfuncs, blast)
  then obtain j where j_def: "j \<in>\<^sub>c \<one>\<Coprod>(\<one>\<Coprod>\<one>) \<and> (\<langle>\<t>, \<t>\<rangle>\<amalg> (\<langle>\<f>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<circ>\<^sub>c j  = \<langle>\<t>,\<f>\<rangle>"
    by (typecheck_cfuncs, smt (verit, ccfv_threshold) IMPLIES_is_pullback  id_right_unit2 is_pullback_def one_unique_element terminal_func_comp terminal_func_comp_elem terminal_func_unique)
  show False
  proof(cases "j = left_coproj \<one> (\<one>\<Coprod>\<one>)")
    assume case1: "j = left_coproj \<one> (\<one>\<Coprod>\<one>)"
    show False
    proof - 
      have "(\<langle>\<t>, \<t>\<rangle>\<amalg> (\<langle>\<f>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<circ>\<^sub>c j = \<langle>\<t>, \<t>\<rangle>"
        by (typecheck_cfuncs, simp add: case1 left_coproj_cfunc_coprod)
      then have "\<langle>\<t>, \<t>\<rangle> = \<langle>\<t>,\<f>\<rangle>"
        using j_def by presburger
      then have "\<t> = \<f>"
        using IFF_true_false_is_false IFF_true_true_is_true by auto
      then show False
        using true_false_distinct by blast
    qed
  next
    assume "j \<noteq> left_coproj \<one> (\<one> \<Coprod> \<one>)"
    then have case2_or_3: "j = right_coproj \<one> (\<one>\<Coprod>\<one>)\<circ>\<^sub>c left_coproj \<one> \<one> \<or> 
                      j = right_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c right_coproj \<one> \<one>"
      by (metis coprojs_jointly_surj id_right_unit2 id_type j_def left_proj_type maps_into_1u1 one_unique_element)
    show False
    proof(cases "j = right_coproj \<one> (\<one>\<Coprod>\<one>)\<circ>\<^sub>c left_coproj \<one> \<one>")
      assume case2: "j = right_coproj \<one> (\<one>\<Coprod>\<one>)\<circ>\<^sub>c left_coproj \<one> \<one>"
      show False
      proof - 
        have "(\<langle>\<t>, \<t>\<rangle>\<amalg> (\<langle>\<f>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<circ>\<^sub>c j = \<langle>\<f>, \<f>\<rangle>"
          by (typecheck_cfuncs, smt (z3) case2 comp_associative2 left_coproj_cfunc_coprod left_proj_type right_coproj_cfunc_coprod right_proj_type)
        then have "\<langle>\<t>, \<t>\<rangle> = \<langle>\<f>,\<f>\<rangle>"
          using XOR_false_false_is_false XOR_only_true_left_is_true j_def by auto
        then have "\<t> = \<f>"
          by (metis XOR_only_true_left_is_true XOR_true_true_is_false \<open>\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<f>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle> \<circ>\<^sub>c j = \<langle>\<f>,\<f>\<rangle>\<close> j_def)
        then show False
          using true_false_distinct by blast
      qed
    next
      assume "j \<noteq> right_coproj \<one> (\<one> \<Coprod> \<one>) \<circ>\<^sub>c left_coproj \<one> \<one>"
      then have case3: "j = right_coproj \<one> (\<one>\<Coprod>\<one>) \<circ>\<^sub>c right_coproj \<one> \<one>"
        using case2_or_3 by blast
      show False
      proof - 
        have "(\<langle>\<t>, \<t>\<rangle>\<amalg> (\<langle>\<f>, \<f>\<rangle> \<amalg>\<langle>\<f>, \<t>\<rangle>)) \<circ>\<^sub>c j = \<langle>\<f>, \<t>\<rangle>"
          by (typecheck_cfuncs, smt (z3) case3 comp_associative2 left_coproj_cfunc_coprod left_proj_type right_coproj_cfunc_coprod right_proj_type)
        then have "\<langle>\<t>, \<t>\<rangle> = \<langle>\<f>, \<t>\<rangle>"
          by (metis cart_prod_eq2 false_func_type j_def true_func_type)
        then have "\<t> = \<f>"
          using XOR_only_true_right_is_true XOR_true_true_is_false by auto
        then show False
          using true_false_distinct by blast
      qed
    qed
  qed
qed

lemma IMPLIES_false_is_true_false:
  assumes "p \<in>\<^sub>c \<Omega>"
  assumes "q \<in>\<^sub>c \<Omega>"  
  assumes "IMPLIES \<circ>\<^sub>c  \<langle>p,q\<rangle> = \<f>"
  shows "p = \<t> \<and> q = \<f>"
  by (metis IMPLIES_false_false_is_true IMPLIES_false_true_is_true IMPLIES_true_true_is_true assms true_false_only_truth_values)

text \<open>ETCS analog to $(A \iff B) = (A \implies B) \land (B \implies A)$\<close>
lemma iff_is_and_implies_implies_swap:
"IFF = AND \<circ>\<^sub>c  \<langle>IMPLIES, IMPLIES \<circ>\<^sub>c  swap \<Omega> \<Omega>\<rangle>"
proof(etcs_rule one_separator)
  fix x 
  assume x_type: "x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>"
  then obtain p q where x_def: "p \<in>\<^sub>c \<Omega> \<and> q \<in>\<^sub>c \<Omega> \<and> x = \<langle>p,q\<rangle>"
    by (meson cart_prod_decomp)
  show "IFF \<circ>\<^sub>c x = (AND \<circ>\<^sub>c \<langle>IMPLIES,IMPLIES \<circ>\<^sub>c swap \<Omega> \<Omega>\<rangle>) \<circ>\<^sub>c x"
  proof(cases "p = \<t>")
    assume "p = \<t>"
    show ?thesis
    proof(cases "q = \<t>")
      assume "q = \<t>"
      show ?thesis
      proof - 
        have "(AND \<circ>\<^sub>c \<langle>IMPLIES,IMPLIES \<circ>\<^sub>c swap \<Omega> \<Omega>\<rangle>) \<circ>\<^sub>c x =    
               AND \<circ>\<^sub>c \<langle>IMPLIES,IMPLIES \<circ>\<^sub>c swap \<Omega> \<Omega>\<rangle>  \<circ>\<^sub>c x"
          using comp_associative2 x_type by (typecheck_cfuncs, force)
        also have "... = AND \<circ>\<^sub>c \<langle>IMPLIES \<circ>\<^sub>c x,IMPLIES \<circ>\<^sub>c swap \<Omega> \<Omega> \<circ>\<^sub>c x\<rangle>"
          using cfunc_prod_comp comp_associative2 x_type by (typecheck_cfuncs, force)
        also have "... = AND \<circ>\<^sub>c \<langle>IMPLIES \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle>, IMPLIES \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle>\<rangle>"
          using \<open>p = \<t>\<close> \<open>q = \<t>\<close> swap_ap x_def by (typecheck_cfuncs, presburger)
        also have "... = AND \<circ>\<^sub>c \<langle>\<t>, \<t>\<rangle>"
          using IMPLIES_true_true_is_true by presburger
        also have "... = \<t>"
          by (simp add: AND_true_true_is_true)
        also have "... = IFF \<circ>\<^sub>c x"
          by (simp add: IFF_true_true_is_true \<open>p = \<t>\<close> \<open>q = \<t>\<close> x_def)
        finally show ?thesis
          by simp
      qed
    next
      assume "q \<noteq> \<t>"
      then have "q = \<f>"
        by (meson true_false_only_truth_values x_def)
      show ?thesis
      proof - 
        have "(AND \<circ>\<^sub>c \<langle>IMPLIES,IMPLIES \<circ>\<^sub>c swap \<Omega> \<Omega>\<rangle>) \<circ>\<^sub>c x =    
               AND \<circ>\<^sub>c \<langle>IMPLIES,IMPLIES \<circ>\<^sub>c swap \<Omega> \<Omega>\<rangle>  \<circ>\<^sub>c x"
          using comp_associative2 x_type by (typecheck_cfuncs, force)
        also have "... = AND \<circ>\<^sub>c \<langle>IMPLIES \<circ>\<^sub>c x,IMPLIES \<circ>\<^sub>c swap \<Omega> \<Omega> \<circ>\<^sub>c x\<rangle>"
          using cfunc_prod_comp comp_associative2 x_type by (typecheck_cfuncs, force)
        also have "... = AND \<circ>\<^sub>c \<langle>IMPLIES \<circ>\<^sub>c \<langle>\<t>,\<f>\<rangle>, IMPLIES \<circ>\<^sub>c \<langle>\<f>,\<t>\<rangle>\<rangle>"
          using \<open>p = \<t>\<close> \<open>q = \<f>\<close> swap_ap x_def by (typecheck_cfuncs, presburger)
        also have "... = AND \<circ>\<^sub>c \<langle>\<f>, \<t>\<rangle>"
          using IMPLIES_false_true_is_true IMPLIES_true_false_is_false by presburger
        also have "... = \<f>"
          by (simp add: AND_false_left_is_false true_func_type)
        also have "... = IFF \<circ>\<^sub>c x"
          by (simp add: IFF_true_false_is_false \<open>p = \<t>\<close> \<open>q = \<f>\<close> x_def)
        finally show ?thesis
          by simp
      qed
    qed
  next
    assume "p \<noteq> \<t>"
    then have "p = \<f>"
      using true_false_only_truth_values x_def by blast
    show ?thesis
    proof(cases "q = \<t>")
      assume "q = \<t>"
      show ?thesis
      proof - 
        have "(AND \<circ>\<^sub>c \<langle>IMPLIES,IMPLIES \<circ>\<^sub>c swap \<Omega> \<Omega>\<rangle>) \<circ>\<^sub>c x =    
               AND \<circ>\<^sub>c \<langle>IMPLIES,IMPLIES \<circ>\<^sub>c swap \<Omega> \<Omega>\<rangle>  \<circ>\<^sub>c x"
          using comp_associative2 x_type by (typecheck_cfuncs, force)
        also have "... = AND \<circ>\<^sub>c \<langle>IMPLIES \<circ>\<^sub>c x,IMPLIES \<circ>\<^sub>c swap \<Omega> \<Omega> \<circ>\<^sub>c x\<rangle>"
          using cfunc_prod_comp comp_associative2 x_type by (typecheck_cfuncs, force)
        also have "... = AND \<circ>\<^sub>c \<langle>IMPLIES \<circ>\<^sub>c \<langle>\<f>,\<t>\<rangle>, IMPLIES \<circ>\<^sub>c \<langle>\<t>,\<f>\<rangle>\<rangle>"
          using \<open>p = \<f>\<close> \<open>q = \<t>\<close> swap_ap x_def by (typecheck_cfuncs, presburger)
        also have "... = AND \<circ>\<^sub>c \<langle>\<t>, \<f>\<rangle>"
          by (simp add: IMPLIES_false_true_is_true IMPLIES_true_false_is_false)
        also have "... = \<f>"
          by (simp add: AND_false_right_is_false true_func_type)
        also have "... = IFF \<circ>\<^sub>c x"
          by (simp add: IFF_false_true_is_false \<open>p = \<f>\<close> \<open>q = \<t>\<close> x_def)
        finally show ?thesis
          by simp
      qed
    next
      assume "q \<noteq> \<t>"
      then have "q = \<f>"
        by (meson true_false_only_truth_values x_def)
      show ?thesis
      proof - 
        have "(AND \<circ>\<^sub>c \<langle>IMPLIES,IMPLIES \<circ>\<^sub>c swap \<Omega> \<Omega>\<rangle>) \<circ>\<^sub>c x =    
               AND \<circ>\<^sub>c \<langle>IMPLIES,IMPLIES \<circ>\<^sub>c swap \<Omega> \<Omega>\<rangle>  \<circ>\<^sub>c x"
          using comp_associative2 x_type by (typecheck_cfuncs, force)
        also have "... = AND \<circ>\<^sub>c \<langle>IMPLIES \<circ>\<^sub>c x,IMPLIES \<circ>\<^sub>c swap \<Omega> \<Omega> \<circ>\<^sub>c x\<rangle>"
          using cfunc_prod_comp comp_associative2 x_type by (typecheck_cfuncs, force)
        also have "... = AND \<circ>\<^sub>c \<langle>IMPLIES \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle>, IMPLIES \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle>\<rangle>"
          using \<open>p = \<f>\<close> \<open>q = \<f>\<close> swap_ap x_def by (typecheck_cfuncs, presburger)
        also have "... = AND \<circ>\<^sub>c \<langle>\<t>, \<t>\<rangle>"
          by (simp add: IMPLIES_false_false_is_true)
        also have "... = \<t>"
          by (simp add: AND_true_true_is_true)
        also have "... = IFF \<circ>\<^sub>c x"
          by (simp add: IFF_false_false_is_true \<open>p = \<f>\<close> \<open>q = \<f>\<close> x_def)
        finally show ?thesis
          by simp
      qed
    qed
  qed
qed

lemma IMPLIES_is_OR_NOT_id:
  "IMPLIES = OR \<circ>\<^sub>c (NOT \<times>\<^sub>f id(\<Omega>))"
proof(etcs_rule one_separator)
  fix x 
  assume x_type: "x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>"
  then obtain u v where x_form: "u \<in>\<^sub>c \<Omega> \<and> v \<in>\<^sub>c \<Omega> \<and> x = \<langle>u, v\<rangle>"
    using cart_prod_decomp by blast
  show "IMPLIES \<circ>\<^sub>c x = (OR \<circ>\<^sub>c NOT \<times>\<^sub>f id\<^sub>c \<Omega>) \<circ>\<^sub>c x"
  proof(cases "u = \<t>")
    assume "u = \<t>"
    show ?thesis
    proof(cases "v = \<t>")
      assume "v = \<t>"
      have "(OR \<circ>\<^sub>c NOT \<times>\<^sub>f id\<^sub>c \<Omega>) \<circ>\<^sub>c x = OR \<circ>\<^sub>c (NOT \<times>\<^sub>f id\<^sub>c \<Omega>) \<circ>\<^sub>c x"
        using comp_associative2 x_type by (typecheck_cfuncs, force)
      also have "... = OR \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c \<t>, id\<^sub>c \<Omega> \<circ>\<^sub>c \<t>\<rangle>"
        by (typecheck_cfuncs, simp add: \<open>u = \<t>\<close> \<open>v = \<t>\<close> cfunc_cross_prod_comp_cfunc_prod x_form)
      also have "... = OR \<circ>\<^sub>c \<langle>\<f>, \<t>\<rangle>"
        by (typecheck_cfuncs, simp add: NOT_true_is_false id_left_unit2)
      also have "... = \<t>"
        by (simp add: OR_true_right_is_true false_func_type)
      also have "... = IMPLIES \<circ>\<^sub>c x"
        by (simp add: IMPLIES_true_true_is_true \<open>u = \<t>\<close> \<open>v = \<t>\<close> x_form)
      finally show ?thesis
        by simp
    next
      assume "v \<noteq> \<t>"
      then have "v = \<f>"
        by (metis true_false_only_truth_values x_form)
      have "(OR \<circ>\<^sub>c NOT \<times>\<^sub>f id\<^sub>c \<Omega>) \<circ>\<^sub>c x = OR \<circ>\<^sub>c (NOT \<times>\<^sub>f id\<^sub>c \<Omega>) \<circ>\<^sub>c x"
        using comp_associative2 x_type by (typecheck_cfuncs, force)
      also have "... = OR \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c \<t>, id\<^sub>c \<Omega> \<circ>\<^sub>c \<f>\<rangle>"
        by (typecheck_cfuncs, simp add: \<open>u = \<t>\<close> \<open>v = \<f>\<close> cfunc_cross_prod_comp_cfunc_prod x_form)
      also have "... = OR \<circ>\<^sub>c \<langle>\<f>, \<f>\<rangle>"
        by (typecheck_cfuncs, simp add: NOT_true_is_false id_left_unit2)
      also have "... = \<f>"
        by (simp add: OR_false_false_is_false false_func_type)
      also have "... = IMPLIES \<circ>\<^sub>c x"
        by (simp add: IMPLIES_true_false_is_false \<open>u = \<t>\<close> \<open>v = \<f>\<close> x_form)
      finally show ?thesis
        by simp
      qed
  next
    assume "u \<noteq> \<t>"
    then have "u = \<f>"
        by (metis true_false_only_truth_values x_form)
    show ?thesis 
    proof(cases "v = \<t>")
      assume "v = \<t>"
      have "(OR \<circ>\<^sub>c NOT \<times>\<^sub>f id\<^sub>c \<Omega>) \<circ>\<^sub>c x = OR \<circ>\<^sub>c (NOT \<times>\<^sub>f id\<^sub>c \<Omega>) \<circ>\<^sub>c x"
        using comp_associative2 x_type by (typecheck_cfuncs, force)
      also have "... = OR \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c \<f>, id\<^sub>c \<Omega> \<circ>\<^sub>c \<t>\<rangle>"
        by (typecheck_cfuncs, simp add: \<open>u = \<f>\<close> \<open>v = \<t>\<close> cfunc_cross_prod_comp_cfunc_prod x_form)
      also have "... = OR \<circ>\<^sub>c \<langle>\<t>, \<t>\<rangle>"
        using NOT_false_is_true id_left_unit2 true_func_type by smt
      also have "... = \<t>"
        by (simp add: OR_true_right_is_true true_func_type)
      also have "... = IMPLIES \<circ>\<^sub>c x"
        by (simp add: IMPLIES_false_true_is_true \<open>u = \<f>\<close> \<open>v = \<t>\<close> x_form)
      finally show ?thesis
        by simp
    next
      assume "v \<noteq> \<t>"
      then have "v = \<f>"
        by (metis true_false_only_truth_values x_form)
      have "(OR \<circ>\<^sub>c NOT \<times>\<^sub>f id\<^sub>c \<Omega>) \<circ>\<^sub>c x = OR \<circ>\<^sub>c (NOT \<times>\<^sub>f id\<^sub>c \<Omega>) \<circ>\<^sub>c x"
        using comp_associative2 x_type by (typecheck_cfuncs, force)
      also have "... = OR \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c \<f>, id\<^sub>c \<Omega> \<circ>\<^sub>c \<f>\<rangle>"
        by (typecheck_cfuncs, simp add: \<open>u = \<f>\<close> \<open>v = \<f>\<close> cfunc_cross_prod_comp_cfunc_prod x_form)
      also have "... = OR \<circ>\<^sub>c \<langle>\<t>, \<f>\<rangle>"
        using NOT_false_is_true false_func_type id_left_unit2 by presburger
      also have "... = \<t>"
        by (simp add: OR_true_left_is_true false_func_type)
      also have "... = IMPLIES \<circ>\<^sub>c x"
        by (simp add: IMPLIES_false_false_is_true \<open>u = \<f>\<close> \<open>v = \<f>\<close> x_form)
      finally show ?thesis
        by simp
      qed
  qed
qed

lemma IMPLIES_implies_implies:
  assumes P_type[type_rule]: "P : X \<rightarrow> \<Omega>" and Q_type[type_rule]: "Q : Y \<rightarrow> \<Omega>"
  assumes X_nonempty: "\<exists>x. x \<in>\<^sub>c X"
  assumes IMPLIES_true: "IMPLIES \<circ>\<^sub>c (P \<times>\<^sub>f Q) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
  shows "P = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<Longrightarrow> Q = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
proof -
  obtain z where z_type[type_rule]: "z : X \<times>\<^sub>c Y \<rightarrow> \<one> \<Coprod> \<one> \<Coprod> \<one>"
    and z_eq: "P \<times>\<^sub>f Q = (\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<f>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle>) \<circ>\<^sub>c z"
    using IMPLIES_is_pullback unfolding is_pullback_def
    by (auto, typecheck_cfuncs, metis IMPLIES_true terminal_func_type)  
  assume P_true: "P = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>"
  
  have "left_cart_proj \<Omega> \<Omega> \<circ>\<^sub>c (P \<times>\<^sub>f Q) = left_cart_proj \<Omega> \<Omega> \<circ>\<^sub>c (\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<f>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle>) \<circ>\<^sub>c z"
    using z_eq by simp
  then have "P \<circ>\<^sub>c left_cart_proj X Y = (left_cart_proj \<Omega> \<Omega> \<circ>\<^sub>c (\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<f>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle>)) \<circ>\<^sub>c z"
    using Q_type comp_associative2 left_cart_proj_cfunc_cross_prod by (typecheck_cfuncs, force)
  then have "P \<circ>\<^sub>c left_cart_proj X Y
    = ((left_cart_proj \<Omega> \<Omega> \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle>) \<amalg> (left_cart_proj \<Omega> \<Omega> \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle>) \<amalg> (left_cart_proj \<Omega> \<Omega> \<circ>\<^sub>c \<langle>\<f>,\<t>\<rangle>)) \<circ>\<^sub>c z"
    by (typecheck_cfuncs_prems, simp add: cfunc_coprod_comp)
  then have "P \<circ>\<^sub>c left_cart_proj X Y = (\<t> \<amalg> \<f> \<amalg> \<f>) \<circ>\<^sub>c z"
    by (typecheck_cfuncs_prems, smt left_cart_proj_cfunc_prod)

  show "Q = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
  proof (etcs_rule one_separator)
    fix y
    assume y_in_Y[type_rule]: "y \<in>\<^sub>c Y"
    obtain x where x_in_X[type_rule]: "x \<in>\<^sub>c X"
      using X_nonempty by blast

    have "z \<circ>\<^sub>c \<langle>x,y\<rangle> = left_coproj \<one> (\<one> \<Coprod> \<one>)
        \<or> z \<circ>\<^sub>c \<langle>x,y\<rangle> = right_coproj \<one> (\<one> \<Coprod> \<one>) \<circ>\<^sub>c left_coproj \<one> \<one>
        \<or> z \<circ>\<^sub>c \<langle>x,y\<rangle> = right_coproj \<one> (\<one> \<Coprod> \<one>) \<circ>\<^sub>c right_coproj \<one> \<one>"
      by (typecheck_cfuncs, smt comp_associative2 coprojs_jointly_surj one_unique_element)
    then show "Q \<circ>\<^sub>c y = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c y"
    proof safe
      assume "z \<circ>\<^sub>c \<langle>x,y\<rangle> = left_coproj \<one> (\<one> \<Coprod> \<one>)"
      then have "(P \<times>\<^sub>f Q) \<circ>\<^sub>c \<langle>x,y\<rangle> = (\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<f>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle>) \<circ>\<^sub>c left_coproj \<one> (\<one> \<Coprod> \<one>)"
        by (typecheck_cfuncs, smt comp_associative2 z_eq z_type)
      then have "(P \<times>\<^sub>f Q) \<circ>\<^sub>c \<langle>x,y\<rangle> = \<langle>\<t>,\<t>\<rangle>"
        by (typecheck_cfuncs_prems, smt left_coproj_cfunc_coprod)
      then have "Q \<circ>\<^sub>c y = \<t>"
        by (typecheck_cfuncs_prems, smt (verit, best) cfunc_cross_prod_comp_cfunc_prod comp_associative2 comp_type id_right_unit2 right_cart_proj_cfunc_prod)
      then show "Q \<circ>\<^sub>c y = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c y"
        by (smt (verit, best) comp_associative2 id_right_unit2 terminal_func_comp_elem terminal_func_type true_func_type y_in_Y)
    next
      assume "z \<circ>\<^sub>c \<langle>x,y\<rangle> = right_coproj \<one> (\<one> \<Coprod> \<one>) \<circ>\<^sub>c left_coproj \<one> \<one>"
      then have "(P \<times>\<^sub>f Q) \<circ>\<^sub>c \<langle>x,y\<rangle> = (\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<f>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle>) \<circ>\<^sub>c right_coproj \<one> (\<one> \<Coprod> \<one>) \<circ>\<^sub>c left_coproj \<one> \<one>"
        by (typecheck_cfuncs, smt comp_associative2 z_eq z_type)
      then have "(P \<times>\<^sub>f Q) \<circ>\<^sub>c \<langle>x,y\<rangle> = (\<langle>\<f>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle>) \<circ>\<^sub>c left_coproj \<one> \<one>"
        by (typecheck_cfuncs_prems, smt right_coproj_cfunc_coprod comp_associative2)
      then have "(P \<times>\<^sub>f Q) \<circ>\<^sub>c \<langle>x,y\<rangle> = \<langle>\<f>,\<f>\<rangle>"
        by (typecheck_cfuncs_prems, smt left_coproj_cfunc_coprod)
      then have "P \<circ>\<^sub>c x = \<f>"
        by (typecheck_cfuncs_prems, smt (verit, best) cfunc_cross_prod_comp_cfunc_prod comp_associative2 comp_type id_right_unit2 left_cart_proj_cfunc_prod)
      also have "P \<circ>\<^sub>c x = \<t>"
        using P_true by (typecheck_cfuncs_prems, smt (z3) comp_associative2 id_right_unit2 id_type one_unique_element terminal_func_comp terminal_func_type x_in_X)
      ultimately have False
        using true_false_distinct by simp
      then show "Q \<circ>\<^sub>c y = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c y"
        by simp
    next
      assume "z \<circ>\<^sub>c \<langle>x,y\<rangle> = right_coproj \<one> (\<one> \<Coprod> \<one>) \<circ>\<^sub>c right_coproj \<one> \<one>"
      then have "(P \<times>\<^sub>f Q) \<circ>\<^sub>c \<langle>x,y\<rangle> = (\<langle>\<t>,\<t>\<rangle> \<amalg> \<langle>\<f>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle>) \<circ>\<^sub>c right_coproj \<one> (\<one> \<Coprod> \<one>) \<circ>\<^sub>c right_coproj \<one> \<one>"
        by (typecheck_cfuncs, smt comp_associative2 z_eq z_type)
      then have "(P \<times>\<^sub>f Q) \<circ>\<^sub>c \<langle>x,y\<rangle> = (\<langle>\<f>,\<f>\<rangle> \<amalg> \<langle>\<f>,\<t>\<rangle>) \<circ>\<^sub>c right_coproj \<one> \<one>"
        by (typecheck_cfuncs_prems, smt right_coproj_cfunc_coprod comp_associative2)
      then have "(P \<times>\<^sub>f Q) \<circ>\<^sub>c \<langle>x,y\<rangle> = \<langle>\<f>,\<t>\<rangle>"
        by (typecheck_cfuncs_prems, smt right_coproj_cfunc_coprod)
      then have "Q \<circ>\<^sub>c y = \<t>"
        by (typecheck_cfuncs_prems, smt (verit, best) cfunc_cross_prod_comp_cfunc_prod comp_associative2 comp_type id_right_unit2 right_cart_proj_cfunc_prod)
      then show "Q \<circ>\<^sub>c y = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c y"
        by (typecheck_cfuncs, smt (z3) comp_associative2 id_right_unit2 id_type one_unique_element terminal_func_comp terminal_func_type)
    qed
  qed
qed

lemma IMPLIES_elim:
  assumes IMPLIES_true: "IMPLIES \<circ>\<^sub>c (P \<times>\<^sub>f Q) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
  assumes P_type[type_rule]: "P : X \<rightarrow> \<Omega>" and Q_type[type_rule]: "Q : Y \<rightarrow> \<Omega>"
  assumes X_nonempty: "\<exists>x. x \<in>\<^sub>c X"
  shows "(P = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<Longrightarrow> ((Q = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<Longrightarrow> R) \<Longrightarrow> R"
  using IMPLIES_implies_implies assms by blast

lemma IMPLIES_elim'':
  assumes IMPLIES_true: "IMPLIES \<circ>\<^sub>c (P \<times>\<^sub>f Q) = \<t>"
  assumes P_type[type_rule]: "P : \<one> \<rightarrow> \<Omega>" and Q_type[type_rule]: "Q : \<one> \<rightarrow> \<Omega>"
  shows "(P = \<t>) \<Longrightarrow> ((Q = \<t>) \<Longrightarrow> R) \<Longrightarrow> R"
proof -
  have one_nonempty: "\<exists>x. x \<in>\<^sub>c \<one>"
    using one_unique_element by blast
  have "(IMPLIES \<circ>\<^sub>c (P \<times>\<^sub>f Q) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<one> \<times>\<^sub>c \<one>\<^esub>)"
    by (typecheck_cfuncs, metis IMPLIES_true id_right_unit2 id_type one_unique_element terminal_func_comp terminal_func_type)
  then have "(P = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub>) \<Longrightarrow> ((Q = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub>) \<Longrightarrow> R) \<Longrightarrow> R"
    using one_nonempty by (-, etcs_erule IMPLIES_elim, auto)
  then show "(P = \<t>) \<Longrightarrow> ((Q = \<t>) \<Longrightarrow> R) \<Longrightarrow> R"
    by (typecheck_cfuncs, metis id_right_unit2 id_type one_unique_element terminal_func_type)
qed

lemma IMPLIES_elim':
  assumes IMPLIES_true: "IMPLIES \<circ>\<^sub>c \<langle>P, Q\<rangle> = \<t>"
  assumes P_type[type_rule]: "P : \<one> \<rightarrow> \<Omega>" and Q_type[type_rule]: "Q : \<one> \<rightarrow> \<Omega>"
  shows "(P = \<t>) \<Longrightarrow> ((Q = \<t>) \<Longrightarrow> R) \<Longrightarrow> R"
  using IMPLIES_true IMPLIES_true_false_is_false Q_type true_false_only_truth_values by force

lemma implies_implies_IMPLIES:
  assumes P_type[type_rule]: "P : \<one> \<rightarrow> \<Omega>" and Q_type[type_rule]: "Q : \<one> \<rightarrow> \<Omega>"
  shows  "(P = \<t> \<Longrightarrow> Q = \<t>) \<Longrightarrow> IMPLIES \<circ>\<^sub>c \<langle>P, Q\<rangle> = \<t>"
  by (typecheck_cfuncs, metis IMPLIES_false_is_true_false true_false_only_truth_values)

subsection \<open>Other Boolean Identities\<close>

lemma AND_OR_distributive:
  assumes "p \<in>\<^sub>c \<Omega>"
  assumes "q \<in>\<^sub>c \<Omega>"
  assumes "r \<in>\<^sub>c \<Omega>"
  shows "AND \<circ>\<^sub>c \<langle>p, OR \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle> = OR \<circ>\<^sub>c \<langle>AND \<circ>\<^sub>c \<langle>p,q\<rangle>, AND \<circ>\<^sub>c \<langle>p,r\<rangle>\<rangle>"
  by (metis AND_commutative AND_false_right_is_false AND_true_true_is_true OR_false_false_is_false OR_true_left_is_true OR_true_right_is_true assms true_false_only_truth_values)

lemma OR_AND_distributive:
  assumes "p \<in>\<^sub>c \<Omega>"
  assumes "q \<in>\<^sub>c \<Omega>"
  assumes "r \<in>\<^sub>c \<Omega>"
  shows "OR \<circ>\<^sub>c \<langle>p, AND \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle> = AND \<circ>\<^sub>c \<langle>OR \<circ>\<^sub>c \<langle>p,q\<rangle>, OR \<circ>\<^sub>c \<langle>p,r\<rangle>\<rangle>"
  by (smt (z3) AND_commutative AND_false_right_is_false AND_true_true_is_true OR_commutative OR_false_false_is_false OR_true_right_is_true assms true_false_only_truth_values)

lemma OR_AND_absorption:
  assumes "p \<in>\<^sub>c \<Omega>"
  assumes "q \<in>\<^sub>c \<Omega>"
  shows "OR \<circ>\<^sub>c \<langle>p, AND \<circ>\<^sub>c \<langle>p,q\<rangle>\<rangle> = p"
  by (metis AND_commutative AND_complementary AND_idempotent NOT_true_is_false OR_false_false_is_false OR_true_left_is_true assms true_false_only_truth_values)

lemma AND_OR_absorption:
  assumes "p \<in>\<^sub>c \<Omega>"
  assumes "q \<in>\<^sub>c \<Omega>"
  shows "AND \<circ>\<^sub>c \<langle>p, OR \<circ>\<^sub>c \<langle>p,q\<rangle>\<rangle> = p"
  by (metis AND_commutative AND_complementary AND_idempotent NOT_true_is_false OR_AND_absorption OR_commutative assms true_false_only_truth_values)

lemma deMorgan_Law1:
  assumes "p \<in>\<^sub>c \<Omega>"
  assumes "q \<in>\<^sub>c \<Omega>"
  shows "NOT \<circ>\<^sub>c OR \<circ>\<^sub>c \<langle>p,q\<rangle> = AND \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c p, NOT \<circ>\<^sub>c q\<rangle>"
  by (metis AND_OR_absorption AND_complementary AND_true_true_is_true NOT_false_is_true NOT_true_is_false OR_AND_absorption OR_commutative OR_idempotent assms false_func_type true_false_only_truth_values)

lemma deMorgan_Law2:
  assumes "p \<in>\<^sub>c \<Omega>"
  assumes "q \<in>\<^sub>c \<Omega>"
  shows "NOT \<circ>\<^sub>c AND \<circ>\<^sub>c \<langle>p,q\<rangle> = OR \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c p, NOT \<circ>\<^sub>c q\<rangle>"
  by (metis AND_complementary AND_idempotent NOT_false_is_true NOT_true_is_false OR_complementary OR_false_false_is_false OR_idempotent assms true_false_only_truth_values true_func_type)
 
end