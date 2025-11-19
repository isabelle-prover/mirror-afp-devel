section \<open>Quantifiers\<close>

theory Quant_Logic
  imports Pred_Logic Exponential_Objects
begin

subsection \<open>Universal Quantification\<close>

definition FORALL :: "cset \<Rightarrow> cfunc" where
  "FORALL X = (THE \<chi>. is_pullback \<one> \<one> (\<Omega>\<^bsup>X\<^esup>) \<Omega> (\<beta>\<^bsub>\<one>\<^esub>) \<t> ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp>) \<chi>)"

lemma FORALL_is_pullback:
  "is_pullback \<one> \<one> (\<Omega>\<^bsup>X\<^esup>) \<Omega> (\<beta>\<^bsub>\<one>\<^esub>) \<t> ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp>) (FORALL X)"
  unfolding FORALL_def
  using characteristic_function_exists element_monomorphism
  by (typecheck_cfuncs, simp add: the1I2)

lemma FORALL_type[type_rule]:
  "FORALL X : \<Omega>\<^bsup>X\<^esup> \<rightarrow> \<Omega>"
  using FORALL_is_pullback unfolding is_pullback_def  by auto

lemma all_true_implies_FORALL_true:
  assumes p_type[type_rule]: "p : X \<rightarrow> \<Omega>" and all_p_true: "\<And> x. x \<in>\<^sub>c X \<Longrightarrow> p \<circ>\<^sub>c x = \<t>"
  shows "FORALL X \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj X \<one>)\<^sup>\<sharp> = \<t>"
proof -
  have "p \<circ>\<^sub>c left_cart_proj X \<one> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>"
  proof (etcs_rule one_separator)
    fix x
    assume x_type: "x \<in>\<^sub>c X \<times>\<^sub>c \<one>"

    have "(p \<circ>\<^sub>c left_cart_proj X \<one>) \<circ>\<^sub>c x = p \<circ>\<^sub>c (left_cart_proj X \<one> \<circ>\<^sub>c x)"
      using x_type p_type comp_associative2 by (typecheck_cfuncs, auto)
    also have "... = \<t>"
      using x_type all_p_true by (typecheck_cfuncs, auto)
    also have "... = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c x "
      using x_type by (typecheck_cfuncs, metis id_right_unit2 id_type one_unique_element)
    also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c x"
      using x_type comp_associative2 by (typecheck_cfuncs, auto)    
    finally show "(p \<circ>\<^sub>c left_cart_proj X \<one>) \<circ>\<^sub>c x = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c x".
  qed
  then have "(p \<circ>\<^sub>c left_cart_proj X \<one>)\<^sup>\<sharp> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp>"
    by simp
  then have "FORALL X \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj X \<one>)\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub>"
    using FORALL_is_pullback unfolding is_pullback_def  by auto
  then show "FORALL X \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj X \<one>)\<^sup>\<sharp> = \<t>"
    using NOT_false_is_true NOT_is_pullback is_pullback_def  by auto
qed

lemma all_true_implies_FORALL_true2:
  assumes p_type[type_rule]: "p : X \<times>\<^sub>c Y \<rightarrow> \<Omega>" and all_p_true: "\<And> xy. xy \<in>\<^sub>c X \<times>\<^sub>c Y \<Longrightarrow> p \<circ>\<^sub>c xy = \<t>"
  shows "FORALL X \<circ>\<^sub>c p\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
proof -
  have "p = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
  proof (etcs_rule one_separator)
    fix xy
    assume xy_type[type_rule]: "xy \<in>\<^sub>c X \<times>\<^sub>c Y"
    then have "p \<circ>\<^sub>c xy = \<t>"
      using all_p_true by blast
    then have "p \<circ>\<^sub>c xy = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub> \<circ>\<^sub>c xy)"
      by (typecheck_cfuncs, metis id_right_unit2 id_type one_unique_element)
    then show "p \<circ>\<^sub>c xy = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>) \<circ>\<^sub>c xy"
      by (typecheck_cfuncs, smt comp_associative2)
  qed
  then have "p\<^sup>\<sharp> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>)\<^sup>\<sharp>"
    by blast
  then have "p\<^sup>\<sharp> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c (id X \<times>\<^sub>f \<beta>\<^bsub>Y\<^esub>))\<^sup>\<sharp>"
    by (typecheck_cfuncs, metis terminal_func_unique)
  then have "p\<^sup>\<sharp> = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c (id X \<times>\<^sub>f \<beta>\<^bsub>Y\<^esub>))\<^sup>\<sharp>"
    by (typecheck_cfuncs, smt comp_associative2)
  then have "p\<^sup>\<sharp> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
    by (typecheck_cfuncs, simp add: sharp_comp)
  then have "FORALL X \<circ>\<^sub>c p\<^sup>\<sharp> = (FORALL X \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
    by (typecheck_cfuncs, smt comp_associative2)
  then have "FORALL X \<circ>\<^sub>c p\<^sup>\<sharp> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub>) \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
    using FORALL_is_pullback unfolding is_pullback_def  by auto
  then show "FORALL X \<circ>\<^sub>c p\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
    by (metis id_right_unit2 id_type terminal_func_unique true_func_type)
qed

lemma all_true_implies_FORALL_true3:
  assumes p_type[type_rule]: "p : X \<times>\<^sub>c \<one> \<rightarrow> \<Omega>" and all_p_true: "\<And> x. x \<in>\<^sub>c X \<Longrightarrow> p \<circ>\<^sub>c \<langle>x, id \<one>\<rangle> = \<t>"
  shows "FORALL X \<circ>\<^sub>c p\<^sup>\<sharp> = \<t>"
proof -
  have "FORALL X \<circ>\<^sub>c p\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub>"
    by (etcs_rule all_true_implies_FORALL_true2, metis all_p_true cart_prod_decomp id_type one_unique_element)
  then show ?thesis
    by (metis id_right_unit2 id_type terminal_func_unique true_func_type)
qed

lemma FORALL_true_implies_all_true:
  assumes p_type: "p : X \<rightarrow> \<Omega>" and FORALL_p_true: "FORALL X \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj X \<one>)\<^sup>\<sharp> = \<t>"
  shows "\<And> x. x \<in>\<^sub>c X \<Longrightarrow> p \<circ>\<^sub>c x = \<t>"
proof (rule ccontr)
  fix x
  assume x_type: "x \<in>\<^sub>c X"
  assume "p \<circ>\<^sub>c x \<noteq> \<t>"
  then have "p \<circ>\<^sub>c x = \<f>"
    using comp_type p_type true_false_only_truth_values x_type by blast
  then have "p \<circ>\<^sub>c left_cart_proj X \<one> \<circ>\<^sub>c \<langle>x, id \<one>\<rangle> = \<f>"
    using id_type left_cart_proj_cfunc_prod x_type by auto
  then have p_left_proj_false: "p \<circ>\<^sub>c left_cart_proj X \<one> \<circ>\<^sub>c \<langle>x, id \<one>\<rangle> = \<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c \<langle>x, id \<one>\<rangle>"
    using x_type by (typecheck_cfuncs, metis id_right_unit2 one_unique_element)

  have "\<t> \<circ>\<^sub>c id \<one> = FORALL X \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj X \<one>)\<^sup>\<sharp>"
    using FORALL_p_true id_right_unit2 true_func_type by auto
  then obtain j where 
      j_type: "j \<in>\<^sub>c \<one>" and 
      j_id: "\<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = id \<one>" and
      t_j_eq_p_left_proj: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c j = (p \<circ>\<^sub>c left_cart_proj X \<one>)\<^sup>\<sharp>"
    using FORALL_is_pullback p_type unfolding is_pullback_def by (typecheck_cfuncs, blast)
  then have "j = id \<one>"
    using id_type one_unique_element by blast
  then have "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> = (p \<circ>\<^sub>c left_cart_proj X \<one>)\<^sup>\<sharp>"
    using id_right_unit2 t_j_eq_p_left_proj p_type by (typecheck_cfuncs, auto)
  then have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> = p \<circ>\<^sub>c left_cart_proj X \<one>"
    using p_type by (typecheck_cfuncs, metis flat_cancels_sharp)
  then have p_left_proj_true: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c \<langle>x, id \<one>\<rangle> = p \<circ>\<^sub>c left_cart_proj X \<one> \<circ>\<^sub>c \<langle>x, id \<one>\<rangle>"
    using p_type x_type comp_associative2 by (typecheck_cfuncs, auto)

  have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c \<langle>x, id \<one>\<rangle> = \<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c \<langle>x, id \<one>\<rangle>"
    using p_left_proj_false p_left_proj_true by auto
  then have "\<t> \<circ>\<^sub>c id \<one> = \<f> \<circ>\<^sub>c id \<one>"
    by (metis id_type right_cart_proj_cfunc_prod right_cart_proj_type terminal_func_unique x_type)
  then have "\<t> = \<f>"
    using true_func_type false_func_type id_right_unit2 by auto
  then show False
    using true_false_distinct by auto
qed

lemma FORALL_true_implies_all_true2:
  assumes p_type[type_rule]: "p : X \<times>\<^sub>c Y \<rightarrow> \<Omega>" and FORALL_p_true: "FORALL X \<circ>\<^sub>c p\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
  shows "\<And> x y. x \<in>\<^sub>c X \<Longrightarrow> y \<in>\<^sub>c Y \<Longrightarrow> p \<circ>\<^sub>c \<langle>x, y\<rangle> = \<t>"
proof -
  have "p\<^sup>\<sharp> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
    using FORALL_is_pullback FORALL_p_true unfolding is_pullback_def 
    by (typecheck_cfuncs, metis terminal_func_unique)
  then have "p\<^sup>\<sharp> = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c (id X \<times>\<^sub>f \<beta>\<^bsub>Y\<^esub>))\<^sup>\<sharp>"
    by (typecheck_cfuncs, simp add: sharp_comp)
  then have "p\<^sup>\<sharp> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>)\<^sup>\<sharp>"
    by (typecheck_cfuncs_prems, smt (z3) comp_associative2 terminal_func_comp)
  then have "p = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
    by (typecheck_cfuncs, metis flat_cancels_sharp)
  then have "\<And> x y. x \<in>\<^sub>c X \<Longrightarrow> y \<in>\<^sub>c Y \<Longrightarrow> p \<circ>\<^sub>c \<langle>x, y\<rangle> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>) \<circ>\<^sub>c \<langle>x, y\<rangle>"
    by auto
  then show "\<And> x y. x \<in>\<^sub>c X \<Longrightarrow> y \<in>\<^sub>c Y \<Longrightarrow> p \<circ>\<^sub>c \<langle>x, y\<rangle> = \<t>"
  proof -
    fix x y
    assume xy_types[type_rule]: "x \<in>\<^sub>c X" "y \<in>\<^sub>c Y"
    assume "\<And>x y. x \<in>\<^sub>c X \<Longrightarrow> y \<in>\<^sub>c Y \<Longrightarrow> p \<circ>\<^sub>c \<langle>x,y\<rangle> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>) \<circ>\<^sub>c \<langle>x,y\<rangle>"
    then have "p \<circ>\<^sub>c \<langle>x,y\<rangle> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>) \<circ>\<^sub>c \<langle>x,y\<rangle>"
      using xy_types by auto
    then have "p \<circ>\<^sub>c \<langle>x,y\<rangle> = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub> \<circ>\<^sub>c \<langle>x,y\<rangle>)"
      by (typecheck_cfuncs, smt comp_associative2)
    then show "p \<circ>\<^sub>c \<langle>x, y\<rangle> = \<t>"
      by (typecheck_cfuncs_prems, metis id_right_unit2 id_type one_unique_element)
  qed
qed

lemma FORALL_true_implies_all_true3:
  assumes p_type[type_rule]: "p : X \<times>\<^sub>c \<one> \<rightarrow> \<Omega>" and FORALL_p_true: "FORALL X \<circ>\<^sub>c p\<^sup>\<sharp> = \<t>"
  shows "\<And> x. x \<in>\<^sub>c X  \<Longrightarrow> p \<circ>\<^sub>c \<langle>x, id \<one>\<rangle> = \<t>"
  using FORALL_p_true FORALL_true_implies_all_true2 id_right_unit2 terminal_func_unique by (typecheck_cfuncs, auto)

lemma FORALL_elim:
  assumes FORALL_p_true: "FORALL X \<circ>\<^sub>c p\<^sup>\<sharp> = \<t>" and p_type[type_rule]: "p : X \<times>\<^sub>c \<one> \<rightarrow> \<Omega>"
  assumes x_type[type_rule]: "x \<in>\<^sub>c X"
  shows "(p \<circ>\<^sub>c \<langle>x, id \<one>\<rangle> = \<t> \<Longrightarrow> P) \<Longrightarrow> P"
  using FORALL_p_true FORALL_true_implies_all_true3 p_type x_type by blast

lemma FORALL_elim':
  assumes FORALL_p_true: "FORALL X \<circ>\<^sub>c p\<^sup>\<sharp> = \<t>" and p_type[type_rule]: "p : X \<times>\<^sub>c \<one> \<rightarrow> \<Omega>"
  shows "((\<And>x. x \<in>\<^sub>c X \<Longrightarrow> p \<circ>\<^sub>c \<langle>x, id \<one>\<rangle> = \<t>) \<Longrightarrow> P) \<Longrightarrow> P"
  using FORALL_p_true FORALL_true_implies_all_true3 p_type by auto

subsection \<open>Existential Quantification\<close>

definition EXISTS :: "cset \<Rightarrow> cfunc" where
  "EXISTS X = NOT \<circ>\<^sub>c FORALL X \<circ>\<^sub>c NOT\<^bsup>X\<^esup>\<^sub>f"

lemma EXISTS_type[type_rule]:
  "EXISTS X : \<Omega>\<^bsup>X\<^esup> \<rightarrow> \<Omega>"
  unfolding EXISTS_def by typecheck_cfuncs

lemma EXISTS_true_implies_exists_true:
  assumes p_type: "p : X \<rightarrow> \<Omega>" and EXISTS_p_true: "EXISTS X \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj X \<one>)\<^sup>\<sharp> = \<t>"
  shows "\<exists> x. x \<in>\<^sub>c X \<and> p \<circ>\<^sub>c x = \<t>"
proof -
  have "NOT \<circ>\<^sub>c FORALL X \<circ>\<^sub>c NOT\<^bsup>X\<^esup>\<^sub>f \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj X \<one>)\<^sup>\<sharp> = \<t>"
    using p_type EXISTS_p_true cfunc_type_def comp_associative comp_type
    unfolding EXISTS_def
    by (typecheck_cfuncs, auto)
  then have "NOT \<circ>\<^sub>c FORALL X \<circ>\<^sub>c (NOT \<circ>\<^sub>c p \<circ>\<^sub>c left_cart_proj X \<one>)\<^sup>\<sharp> = \<t>"
    using p_type transpose_of_comp by (typecheck_cfuncs, auto)
  then have "FORALL X \<circ>\<^sub>c (NOT \<circ>\<^sub>c p \<circ>\<^sub>c left_cart_proj X \<one>)\<^sup>\<sharp> \<noteq> \<t>"
    using NOT_true_is_false true_false_distinct by auto
  then have "FORALL X \<circ>\<^sub>c ((NOT \<circ>\<^sub>c p) \<circ>\<^sub>c left_cart_proj X \<one>)\<^sup>\<sharp> \<noteq> \<t>"
    using p_type comp_associative2 by (typecheck_cfuncs, auto)
  then have "\<not> (\<forall> x. x \<in>\<^sub>c X \<longrightarrow> (NOT \<circ>\<^sub>c p) \<circ>\<^sub>c x = \<t>)"
    using NOT_type all_true_implies_FORALL_true comp_type p_type by blast
  then have "\<not> (\<forall> x. x \<in>\<^sub>c X \<longrightarrow> NOT \<circ>\<^sub>c (p \<circ>\<^sub>c x) = \<t>)"
    using p_type comp_associative2 by (typecheck_cfuncs, auto)
  then have "\<not> (\<forall> x. x \<in>\<^sub>c X \<longrightarrow> p \<circ>\<^sub>c x \<noteq> \<t>)"
    using NOT_false_is_true comp_type p_type true_false_only_truth_values by fastforce
  then show "\<exists>x. x \<in>\<^sub>c X \<and> p \<circ>\<^sub>c x = \<t>"
    by blast
qed

lemma EXISTS_elim:
  assumes EXISTS_p_true: "EXISTS X \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj X \<one>)\<^sup>\<sharp> = \<t>" and p_type: "p : X \<rightarrow> \<Omega>"
  shows "(\<And> x. x \<in>\<^sub>c X \<Longrightarrow> p \<circ>\<^sub>c x = \<t> \<Longrightarrow> Q) \<Longrightarrow> Q"
  using EXISTS_p_true EXISTS_true_implies_exists_true p_type by auto

lemma exists_true_implies_EXISTS_true:
  assumes p_type: "p : X \<rightarrow> \<Omega>" and exists_p_true: "\<exists> x. x \<in>\<^sub>c X \<and> p \<circ>\<^sub>c x = \<t>"
  shows  "EXISTS X \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj X \<one>)\<^sup>\<sharp> = \<t>"
proof -
 have "\<not> (\<forall> x. x \<in>\<^sub>c X \<longrightarrow> p \<circ>\<^sub>c x \<noteq> \<t>)"
   using exists_p_true by blast
 then have "\<not> (\<forall> x. x \<in>\<^sub>c X \<longrightarrow> NOT \<circ>\<^sub>c (p \<circ>\<^sub>c x) = \<t>)"
   using NOT_true_is_false true_false_distinct by auto
 then have "\<not> (\<forall> x. x \<in>\<^sub>c X \<longrightarrow> (NOT \<circ>\<^sub>c p) \<circ>\<^sub>c x = \<t>)"
   using p_type by (typecheck_cfuncs, metis NOT_true_is_false cfunc_type_def comp_associative exists_p_true true_false_distinct)
 then have "FORALL X \<circ>\<^sub>c ((NOT \<circ>\<^sub>c p) \<circ>\<^sub>c left_cart_proj X \<one>)\<^sup>\<sharp> \<noteq> \<t>"
   using FORALL_true_implies_all_true NOT_type comp_type p_type by blast
 then have "FORALL X \<circ>\<^sub>c (NOT \<circ>\<^sub>c p \<circ>\<^sub>c left_cart_proj X \<one>)\<^sup>\<sharp> \<noteq> \<t>"
   using NOT_type cfunc_type_def comp_associative left_cart_proj_type p_type by auto
 then have "NOT \<circ>\<^sub>c FORALL X \<circ>\<^sub>c (NOT \<circ>\<^sub>c p \<circ>\<^sub>c left_cart_proj X \<one>)\<^sup>\<sharp> = \<t>"
   using assms NOT_is_false_implies_true true_false_only_truth_values by (typecheck_cfuncs, blast)
 then have "NOT \<circ>\<^sub>c FORALL X \<circ>\<^sub>c NOT\<^bsup>X\<^esup>\<^sub>f \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj X \<one>)\<^sup>\<sharp> = \<t>"
   using assms transpose_of_comp by (typecheck_cfuncs, auto)
 then have "(NOT \<circ>\<^sub>c FORALL X \<circ>\<^sub>c NOT\<^bsup>X\<^esup>\<^sub>f) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj X \<one>)\<^sup>\<sharp> = \<t>"
    using assms cfunc_type_def comp_associative by (typecheck_cfuncs,auto)
 then show "EXISTS X \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj X \<one>)\<^sup>\<sharp> = \<t>"
  by (simp add: EXISTS_def)
qed

end