section \<open>Natural Number Parity and Halving\<close>

theory Nat_Parity
  imports Nats Quant_Logic
begin

subsection \<open>Nth Even Number\<close>

definition nth_even :: "cfunc" where
  "nth_even = (THE u. u: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> 
    u \<circ>\<^sub>c zero = zero \<and>
    (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c u = u \<circ>\<^sub>c successor)"

lemma nth_even_def2:
  "nth_even: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> nth_even \<circ>\<^sub>c zero = zero \<and> (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even = nth_even \<circ>\<^sub>c successor"
  unfolding nth_even_def by (rule theI', etcs_rule natural_number_object_property2)

lemma nth_even_type[type_rule]:
  "nth_even: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
  by (simp add: nth_even_def2)

lemma nth_even_zero:
  "nth_even \<circ>\<^sub>c zero = zero"
  by (simp add: nth_even_def2)

lemma nth_even_successor:
  "nth_even \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
  by (simp add: nth_even_def2)

lemma nth_even_successor2:
  "nth_even \<circ>\<^sub>c successor = successor \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even"
  using comp_associative2 nth_even_def2 by (typecheck_cfuncs, auto)

subsection \<open>Nth Odd Number\<close>

definition nth_odd :: "cfunc" where
  "nth_odd = (THE u. u: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> 
    u \<circ>\<^sub>c zero = successor \<circ>\<^sub>c zero \<and>
    (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c u = u \<circ>\<^sub>c successor)"

lemma nth_odd_def2:
  "nth_odd: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> nth_odd \<circ>\<^sub>c zero = successor \<circ>\<^sub>c zero \<and> (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd = nth_odd \<circ>\<^sub>c successor"
  unfolding nth_odd_def by (rule theI', etcs_rule natural_number_object_property2)

lemma nth_odd_type[type_rule]:
  "nth_odd: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
  by (simp add: nth_odd_def2)

lemma nth_odd_zero:
  "nth_odd \<circ>\<^sub>c zero = successor \<circ>\<^sub>c zero"
  by (simp add: nth_odd_def2)

lemma nth_odd_successor:
  "nth_odd \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
  by (simp add: nth_odd_def2)

lemma nth_odd_successor2:
  "nth_odd \<circ>\<^sub>c successor = successor \<circ>\<^sub>c successor \<circ>\<^sub>c nth_odd"
  using comp_associative2 nth_odd_def2 by (typecheck_cfuncs, auto)

lemma nth_odd_is_succ_nth_even:
  "nth_odd = successor \<circ>\<^sub>c nth_even"
proof (etcs_rule natural_number_object_func_unique[where X="\<nat>\<^sub>c", where f="successor \<circ>\<^sub>c successor"])
  show "nth_odd \<circ>\<^sub>c zero = (successor \<circ>\<^sub>c nth_even) \<circ>\<^sub>c zero"
  proof -
    have "nth_odd \<circ>\<^sub>c zero = successor \<circ>\<^sub>c zero"
      by (simp add: nth_odd_zero)
    also have "... = (successor \<circ>\<^sub>c nth_even) \<circ>\<^sub>c zero"
      using comp_associative2 nth_even_def2 successor_type zero_type by fastforce
    finally show ?thesis.
  qed

  show "nth_odd \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
    by (simp add: nth_odd_successor)

  show "(successor \<circ>\<^sub>c nth_even) \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even"
  proof -
    have "(successor \<circ>\<^sub>c nth_even) \<circ>\<^sub>c successor = successor \<circ>\<^sub>c nth_even \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even"
      by (simp add: nth_even_successor2)
    also have "... = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even"
      by (typecheck_cfuncs, simp add: comp_associative2)
    finally show ?thesis.
  qed
qed

lemma succ_nth_odd_is_nth_even_succ:
  "successor \<circ>\<^sub>c nth_odd = nth_even \<circ>\<^sub>c successor"
proof (etcs_rule natural_number_object_func_unique[where f="successor \<circ>\<^sub>c successor"])
  show "(successor \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c zero = (nth_even \<circ>\<^sub>c successor) \<circ>\<^sub>c zero"
    by (simp add: nth_even_successor2 nth_odd_is_succ_nth_even)
  show "(successor \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c successor \<circ>\<^sub>c nth_odd"
    by (metis cfunc_type_def codomain_comp comp_associative nth_odd_def2 successor_type)
  then show "(nth_even \<circ>\<^sub>c successor) \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even \<circ>\<^sub>c successor"
    using nth_even_successor2 nth_odd_is_succ_nth_even by auto
qed

subsection \<open>Checking if a Number is Even\<close>

definition is_even :: "cfunc" where
  "is_even = (THE u. u: \<nat>\<^sub>c \<rightarrow> \<Omega> \<and> u \<circ>\<^sub>c zero = \<t> \<and> NOT \<circ>\<^sub>c u = u \<circ>\<^sub>c successor)"

lemma is_even_def2:
  "is_even : \<nat>\<^sub>c \<rightarrow> \<Omega> \<and> is_even \<circ>\<^sub>c zero = \<t> \<and> NOT \<circ>\<^sub>c is_even = is_even \<circ>\<^sub>c successor"
  unfolding is_even_def by (rule theI', etcs_rule natural_number_object_property2)

lemma is_even_type[type_rule]:
  "is_even : \<nat>\<^sub>c \<rightarrow> \<Omega>"
  by (simp add: is_even_def2)

lemma is_even_zero:
  "is_even \<circ>\<^sub>c zero = \<t>"
  by (simp add: is_even_def2)

lemma is_even_successor:
  "is_even \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c is_even"
  by (simp add: is_even_def2)

subsection \<open>Checking if a Number is Odd\<close>

definition is_odd :: "cfunc" where
  "is_odd = (THE u. u: \<nat>\<^sub>c \<rightarrow> \<Omega> \<and> u \<circ>\<^sub>c zero = \<f> \<and> NOT \<circ>\<^sub>c u = u \<circ>\<^sub>c successor)"

lemma is_odd_def2:
  "is_odd : \<nat>\<^sub>c \<rightarrow> \<Omega> \<and> is_odd \<circ>\<^sub>c zero = \<f> \<and> NOT \<circ>\<^sub>c is_odd = is_odd \<circ>\<^sub>c successor"
  unfolding is_odd_def by (rule theI', etcs_rule natural_number_object_property2)

lemma is_odd_type[type_rule]:
  "is_odd : \<nat>\<^sub>c \<rightarrow> \<Omega>"
  by (simp add: is_odd_def2)

lemma is_odd_zero:
  "is_odd \<circ>\<^sub>c zero = \<f>"
  by (simp add: is_odd_def2)

lemma is_odd_successor:
  "is_odd \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c is_odd"
  by (simp add: is_odd_def2)

lemma is_even_not_is_odd:
  "is_even = NOT \<circ>\<^sub>c is_odd"
proof (typecheck_cfuncs, rule natural_number_object_func_unique[where f="NOT", where X="\<Omega>"], clarify)
  show "is_even \<circ>\<^sub>c zero = (NOT \<circ>\<^sub>c is_odd) \<circ>\<^sub>c zero"
    by (typecheck_cfuncs, metis NOT_false_is_true cfunc_type_def comp_associative is_even_def2 is_odd_def2)

  show "is_even \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c is_even"
    by (simp add: is_even_successor)

  show "(NOT \<circ>\<^sub>c is_odd) \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c NOT \<circ>\<^sub>c is_odd"
    by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative is_odd_def2)
qed

lemma is_odd_not_is_even:
  "is_odd = NOT \<circ>\<^sub>c is_even"
proof (typecheck_cfuncs, rule natural_number_object_func_unique[where f="NOT", where X="\<Omega>"], clarify)
  show "is_odd \<circ>\<^sub>c zero = (NOT \<circ>\<^sub>c is_even) \<circ>\<^sub>c zero"
    by (typecheck_cfuncs, metis NOT_true_is_false cfunc_type_def comp_associative is_even_def2 is_odd_def2)

  show "is_odd \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c is_odd"
    by (simp add: is_odd_successor)

  show "(NOT \<circ>\<^sub>c is_even) \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c NOT \<circ>\<^sub>c is_even"
    by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative is_even_def2)
qed

lemma not_even_and_odd:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "\<not>(is_even \<circ>\<^sub>c m = \<t> \<and> is_odd \<circ>\<^sub>c m = \<t>)"
  using assms NOT_true_is_false NOT_type comp_associative2 is_even_not_is_odd true_false_distinct by (typecheck_cfuncs, fastforce)

lemma even_or_odd:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "is_even \<circ>\<^sub>c n = \<t> \<or> is_odd \<circ>\<^sub>c n = \<t>"
  by (typecheck_cfuncs, metis NOT_false_is_true NOT_type comp_associative2 is_even_not_is_odd true_false_only_truth_values assms)

lemma is_even_nth_even_true:
  "is_even \<circ>\<^sub>c nth_even = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
proof (etcs_rule natural_number_object_func_unique[where f="id \<Omega>", where X=\<Omega>])
  show "(is_even \<circ>\<^sub>c nth_even) \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
  proof -
    have "(is_even \<circ>\<^sub>c nth_even) \<circ>\<^sub>c zero = is_even \<circ>\<^sub>c nth_even \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = \<t>"
      by (simp add: is_even_zero nth_even_zero)
    also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, metis comp_associative2 id_right_unit2 terminal_func_comp_elem)
    finally show ?thesis.
  qed

  show "(is_even \<circ>\<^sub>c nth_even) \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c is_even \<circ>\<^sub>c nth_even"
  proof -
    have "(is_even \<circ>\<^sub>c nth_even) \<circ>\<^sub>c successor = is_even \<circ>\<^sub>c nth_even \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = is_even \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even"
      by (simp add: nth_even_successor2)
    also have "... = ((is_even \<circ>\<^sub>c successor) \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
      by (typecheck_cfuncs, smt comp_associative2)
    also have "... =  is_even \<circ>\<^sub>c nth_even"
      using is_even_def2 is_even_not_is_odd is_odd_def2 is_odd_not_is_even by (typecheck_cfuncs, auto)
    also have "... = id \<Omega> \<circ>\<^sub>c is_even \<circ>\<^sub>c nth_even"
      by (typecheck_cfuncs, simp add: id_left_unit2)
    finally show ?thesis.
  qed

  show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
    by (typecheck_cfuncs, smt comp_associative2 id_left_unit2 terminal_func_comp)
qed

lemma is_odd_nth_odd_true:
  "is_odd \<circ>\<^sub>c nth_odd = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
proof (etcs_rule natural_number_object_func_unique[where f="id \<Omega>", where X=\<Omega>])
  show "(is_odd \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
  proof -
    have "(is_odd \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c zero = is_odd \<circ>\<^sub>c nth_odd \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = \<t>"
      using comp_associative2 is_even_not_is_odd is_even_zero is_odd_def2 nth_odd_def2 successor_type zero_type by auto
    also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, metis comp_associative2 is_even_nth_even_true is_even_type is_even_zero nth_even_def2)
    finally show ?thesis.
  qed

  show "(is_odd \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c is_odd \<circ>\<^sub>c nth_odd"
  proof -
    have "(is_odd \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c successor = is_odd \<circ>\<^sub>c nth_odd \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = is_odd \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c nth_odd"
      by (simp add: nth_odd_successor2)
    also have "... = ((is_odd \<circ>\<^sub>c successor) \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
      by (typecheck_cfuncs, smt comp_associative2)
    also have "... =  is_odd \<circ>\<^sub>c nth_odd"
      using is_even_def2 is_even_not_is_odd is_odd_def2 is_odd_not_is_even by (typecheck_cfuncs, auto)
    also have "... = id \<Omega> \<circ>\<^sub>c is_odd \<circ>\<^sub>c nth_odd"
      by (typecheck_cfuncs, simp add: id_left_unit2)
    finally show ?thesis.
  qed
  show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
    by (typecheck_cfuncs, smt comp_associative2 id_left_unit2 terminal_func_comp)
qed

lemma is_odd_nth_even_false:
  "is_odd \<circ>\<^sub>c nth_even = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
  by (smt NOT_true_is_false NOT_type comp_associative2 is_even_def2 is_even_nth_even_true
      is_odd_not_is_even nth_even_def2 terminal_func_type true_func_type)

lemma is_even_nth_odd_false:
  "is_even \<circ>\<^sub>c nth_odd = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
  by (smt NOT_true_is_false NOT_type comp_associative2 is_odd_def2 is_odd_nth_odd_true
      is_even_not_is_odd nth_odd_def2 terminal_func_type true_func_type)

lemma EXISTS_zero_nth_even:
  "(EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c zero = \<t>"
proof -
  have  "(EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c zero
      = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero"
    by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero))\<^sup>\<sharp>"
    by (typecheck_cfuncs, simp add: comp_associative2 sharp_comp)
  also have "... = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (nth_even \<times>\<^sub>f zero))\<^sup>\<sharp>"
    by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_cross_prod id_left_unit2 id_right_unit2)
  also have "... = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_even \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<one>\<^esub>\<rangle> )\<^sup>\<sharp>"
    by (typecheck_cfuncs, metis cfunc_cross_prod_def cfunc_type_def right_cart_proj_type terminal_func_unique)
  also have "... = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_even \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>, (zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>\<rangle> )\<^sup>\<sharp>"
    by (typecheck_cfuncs, smt comp_associative2 terminal_func_comp)
  also have "... = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_even, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>"
    by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
  also have "... = \<t>"
  proof (rule exists_true_implies_EXISTS_true)
    show "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_even,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "\<exists>x. x \<in>\<^sub>c \<nat>\<^sub>c \<and> (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_even,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c x = \<t>"
    proof (typecheck_cfuncs, intro exI[where x="zero"], clarify)
      have "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_even,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero
        = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_even,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c zero"
        by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_even \<circ>\<^sub>c zero, zero\<rangle>"
        by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 id_right_unit2 terminal_func_comp_elem)
      also have "... = \<t>"
        using eq_pred_iff_eq nth_even_zero by (typecheck_cfuncs, blast)
      finally show "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_even,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero = \<t>".
    qed
  qed
  finally show ?thesis.
qed

lemma not_EXISTS_zero_nth_odd:
  "(EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_odd \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c zero = \<f>"
proof -
  have  "(EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_odd \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c zero = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_odd \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero"
    by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (nth_odd \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero))\<^sup>\<sharp>"
    by (typecheck_cfuncs, simp add: comp_associative2 sharp_comp)
  also have "... = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (nth_odd \<times>\<^sub>f zero))\<^sup>\<sharp>"
    by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_cross_prod id_left_unit2 id_right_unit2)
  also have "... = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_odd \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<one>\<^esub>\<rangle> )\<^sup>\<sharp>"
    by (typecheck_cfuncs, metis cfunc_cross_prod_def cfunc_type_def right_cart_proj_type terminal_func_unique)
  also have "... = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_odd \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>, (zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>\<rangle> )\<^sup>\<sharp>"
    by (typecheck_cfuncs, smt comp_associative2 terminal_func_comp)
  also have "... = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_odd, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>"
    by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
  also have "... = \<f>"
  proof -
    have "\<nexists> x. x \<in>\<^sub>c \<nat>\<^sub>c \<and> (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_odd, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c x = \<t>"
    proof clarify
      fix x
      assume x_type[type_rule]: "x \<in>\<^sub>c \<nat>\<^sub>c"
      assume "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_odd,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c x = \<t>"
      then have "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_odd, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c x = \<t>"
        by (typecheck_cfuncs, simp add: comp_associative2)
      then have "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_odd \<circ>\<^sub>c x, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c x\<rangle> = \<t>"
        by (typecheck_cfuncs_prems, auto simp add: cfunc_prod_comp comp_associative2)
      then have "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_odd \<circ>\<^sub>c x, zero\<rangle> = \<t>"
        by (typecheck_cfuncs_prems, metis cfunc_type_def id_right_unit id_type one_unique_element)
      then have "nth_odd \<circ>\<^sub>c x = zero"
        using eq_pred_iff_eq by (typecheck_cfuncs_prems, blast)
      then show False
        by (typecheck_cfuncs_prems, smt comp_associative2 comp_type nth_even_def2 nth_odd_is_succ_nth_even successor_type zero_is_not_successor)
    qed
    then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_odd,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp> \<noteq> \<t>"
      using EXISTS_true_implies_exists_true by (typecheck_cfuncs, blast)
    then show "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_odd,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp> = \<f>"
      using true_false_only_truth_values by (typecheck_cfuncs, blast)
  qed
  finally show ?thesis.
qed

subsection \<open>Natural Number Halving\<close>

definition halve_with_parity :: "cfunc" where
  "halve_with_parity = (THE u. u: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<and> 
    u \<circ>\<^sub>c zero = left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero \<and>
    (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c u = u \<circ>\<^sub>c successor)"

lemma halve_with_parity_def2:
  "halve_with_parity : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<and> 
    halve_with_parity \<circ>\<^sub>c zero = left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero \<and>
    (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity = halve_with_parity \<circ>\<^sub>c successor"
  unfolding halve_with_parity_def by (rule theI', etcs_rule natural_number_object_property2)

lemma halve_with_parity_type[type_rule]:
  "halve_with_parity : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c"
  by (simp add: halve_with_parity_def2)

lemma halve_with_parity_zero:
  "halve_with_parity \<circ>\<^sub>c zero = left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
  by (simp add: halve_with_parity_def2)

lemma halve_with_parity_successor:
  "(right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity = halve_with_parity \<circ>\<^sub>c successor"
  by (simp add: halve_with_parity_def2)

lemma halve_with_parity_nth_even:
  "halve_with_parity \<circ>\<^sub>c nth_even = left_coproj \<nat>\<^sub>c \<nat>\<^sub>c"
proof (etcs_rule natural_number_object_func_unique[where X="\<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c", where f="(left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<amalg> (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)"])
  show "(halve_with_parity \<circ>\<^sub>c nth_even) \<circ>\<^sub>c zero = left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
  proof -
    have "(halve_with_parity \<circ>\<^sub>c nth_even) \<circ>\<^sub>c zero = halve_with_parity \<circ>\<^sub>c nth_even \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = halve_with_parity \<circ>\<^sub>c zero"
      by (simp add: nth_even_zero)
    also have "... = left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
      by (simp add: halve_with_parity_zero)
    finally show ?thesis.
  qed

  show "(halve_with_parity \<circ>\<^sub>c nth_even) \<circ>\<^sub>c successor =
      ((left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<amalg> (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c nth_even"
  proof -
    have "(halve_with_parity \<circ>\<^sub>c nth_even) \<circ>\<^sub>c successor = halve_with_parity \<circ>\<^sub>c nth_even \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = halve_with_parity \<circ>\<^sub>c (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
      by (simp add: nth_even_successor)
    also have "... = ((halve_with_parity \<circ>\<^sub>c successor) \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (((right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
      by (simp add: halve_with_parity_def2)
    also have "... = (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor))
        \<circ>\<^sub>c (halve_with_parity \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor))
        \<circ>\<^sub>c ((right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c nth_even"
      by (simp add: halve_with_parity_def2)
    also have "... = ((right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor))
        \<circ>\<^sub>c (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)))
        \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c nth_even"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = ((left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<amalg> (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor))
        \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c nth_even"
      by (typecheck_cfuncs, smt cfunc_coprod_comp comp_associative2 left_coproj_cfunc_coprod right_coproj_cfunc_coprod)
    finally show ?thesis.
  qed

  show "left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor =
    (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<amalg> (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<circ>\<^sub>c left_coproj \<nat>\<^sub>c \<nat>\<^sub>c"
    by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
qed

lemma halve_with_parity_nth_odd:
  "halve_with_parity \<circ>\<^sub>c nth_odd = right_coproj \<nat>\<^sub>c \<nat>\<^sub>c"
proof (etcs_rule natural_number_object_func_unique[where X="\<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c", where f="(left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<amalg> (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)"])
  show "(halve_with_parity \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c zero = right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
  proof -
    have "(halve_with_parity \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c zero = halve_with_parity \<circ>\<^sub>c nth_odd \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = halve_with_parity \<circ>\<^sub>c successor \<circ>\<^sub>c zero"
      by (simp add: nth_odd_def2)
    also have "... = (halve_with_parity \<circ>\<^sub>c successor) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c zero"
      by (simp add: halve_with_parity_def2)
    also have "... = right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<circ>\<^sub>c left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
      by (simp add: halve_with_parity_def2)
    also have "... = (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<circ>\<^sub>c left_coproj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
    finally  show ?thesis.
  qed

  show "(halve_with_parity \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c successor =
      (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<amalg> (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c nth_odd"
  proof -
    have "(halve_with_parity \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c successor = halve_with_parity \<circ>\<^sub>c nth_odd \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = halve_with_parity \<circ>\<^sub>c (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
      by (simp add: nth_odd_successor)
    also have "... = ((halve_with_parity \<circ>\<^sub>c successor) \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = ((right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<circ>\<^sub>c halve_with_parity) 
        \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
      by (simp add: halve_with_parity_successor)
    also have "... = (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)
        \<circ>\<^sub>c (halve_with_parity \<circ>\<^sub>c successor)) \<circ>\<^sub>c nth_odd"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)
        \<circ>\<^sub>c (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<circ>\<^sub>c halve_with_parity)) \<circ>\<^sub>c nth_odd"
      by (simp add: halve_with_parity_successor)
    also have "... = (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)
        \<circ>\<^sub>c right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c nth_odd"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = ((left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<amalg> (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c nth_odd"
      by (typecheck_cfuncs, smt cfunc_coprod_comp comp_associative2 left_coproj_cfunc_coprod right_coproj_cfunc_coprod)
    finally show ?thesis.
  qed

  show "right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor =
      (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<amalg> (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<circ>\<^sub>c right_coproj \<nat>\<^sub>c \<nat>\<^sub>c"
    by (typecheck_cfuncs, simp add: right_coproj_cfunc_coprod)
qed

lemma nth_even_nth_odd_halve_with_parity:
  "(nth_even \<amalg> nth_odd) \<circ>\<^sub>c halve_with_parity = id \<nat>\<^sub>c"
proof (etcs_rule natural_number_object_func_unique[where X="\<nat>\<^sub>c", where f="successor"])
  show "(nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c zero = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
  proof -
    have "(nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c zero = nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = nth_even \<amalg> nth_odd \<circ>\<^sub>c left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
      by (simp add: halve_with_parity_zero)
    also have "... = (nth_even \<amalg> nth_odd \<circ>\<^sub>c left_coproj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = nth_even \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
    also have "... = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
      using id_left_unit2 nth_even_def2 zero_type by auto
    finally show ?thesis.
  qed

  show "(nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c successor =
    successor \<circ>\<^sub>c nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity"
  proof -
    have "(nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c successor = nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = nth_even \<amalg> nth_odd \<circ>\<^sub>c right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<circ>\<^sub>c halve_with_parity"
      by (simp add: halve_with_parity_successor)
    also have "... = (nth_even \<amalg> nth_odd \<circ>\<^sub>c right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = nth_odd \<amalg> (nth_even \<circ>\<^sub>c successor) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, smt cfunc_coprod_comp comp_associative2 left_coproj_cfunc_coprod right_coproj_cfunc_coprod)
    also have "... = (successor \<circ>\<^sub>c nth_even) \<amalg> ((successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even) \<circ>\<^sub>c halve_with_parity"
      by (simp add: nth_even_successor nth_odd_is_succ_nth_even)
    also have "... = (successor \<circ>\<^sub>c nth_even) \<amalg> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (successor \<circ>\<^sub>c nth_even) \<amalg> (successor \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c halve_with_parity"
      by (simp add: nth_odd_is_succ_nth_even)
    also have "... = successor \<circ>\<^sub>c nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: cfunc_coprod_comp comp_associative2)
    finally show ?thesis.
  qed
  show "id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor = successor \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c"
    using id_left_unit2 id_right_unit2 successor_type by auto
qed

lemma halve_with_parity_nth_even_nth_odd:
  "halve_with_parity \<circ>\<^sub>c (nth_even \<amalg> nth_odd) = id (\<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c)"
  by (typecheck_cfuncs, smt cfunc_coprod_comp halve_with_parity_nth_even halve_with_parity_nth_odd id_coprod)

lemma even_odd_iso:
  "isomorphism (nth_even \<amalg> nth_odd)"
  unfolding isomorphism_def
proof (intro exI[where x=halve_with_parity], safe)
  show "domain halve_with_parity = codomain (nth_even \<amalg> nth_odd)"
    by (typecheck_cfuncs, unfold cfunc_type_def, auto)
  show "codomain halve_with_parity = domain (nth_even \<amalg> nth_odd)"
    by (typecheck_cfuncs, unfold cfunc_type_def, auto)
  show "halve_with_parity \<circ>\<^sub>c nth_even \<amalg> nth_odd = id\<^sub>c (domain (nth_even \<amalg> nth_odd))"
    by (typecheck_cfuncs, unfold cfunc_type_def, auto simp add: halve_with_parity_nth_even_nth_odd)
  show "nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity = id\<^sub>c (domain halve_with_parity)"
    by (typecheck_cfuncs, unfold cfunc_type_def, auto simp add: nth_even_nth_odd_halve_with_parity)
qed

lemma halve_with_parity_iso:
  "isomorphism halve_with_parity"
   unfolding isomorphism_def
proof (intro exI[where x="nth_even \<amalg> nth_odd"], safe)
  show "domain (nth_even \<amalg> nth_odd) = codomain halve_with_parity"
    by (typecheck_cfuncs, unfold cfunc_type_def, auto)
  show "codomain (nth_even \<amalg> nth_odd) = domain halve_with_parity"
    by (typecheck_cfuncs, unfold cfunc_type_def, auto)
  show "nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity = id\<^sub>c (domain halve_with_parity)"
    by (typecheck_cfuncs, unfold cfunc_type_def, auto simp add: nth_even_nth_odd_halve_with_parity)
  show "halve_with_parity \<circ>\<^sub>c nth_even \<amalg> nth_odd = id\<^sub>c (domain (nth_even \<amalg> nth_odd))"
    by (typecheck_cfuncs, unfold cfunc_type_def, auto simp add: halve_with_parity_nth_even_nth_odd)
qed

definition halve :: "cfunc" where
  "halve = (id \<nat>\<^sub>c \<amalg> id \<nat>\<^sub>c) \<circ>\<^sub>c halve_with_parity"

lemma halve_type[type_rule]:
  "halve : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
  unfolding halve_def by typecheck_cfuncs

lemma halve_nth_even:
  "halve \<circ>\<^sub>c nth_even = id \<nat>\<^sub>c"
  unfolding halve_def by (typecheck_cfuncs, smt comp_associative2 halve_with_parity_nth_even left_coproj_cfunc_coprod)

lemma halve_nth_odd:
  "halve \<circ>\<^sub>c nth_odd = id \<nat>\<^sub>c"
  unfolding halve_def by (typecheck_cfuncs, smt comp_associative2 halve_with_parity_nth_odd right_coproj_cfunc_coprod)

lemma is_even_def3:
  "is_even = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)) \<circ>\<^sub>c halve_with_parity"
proof (etcs_rule natural_number_object_func_unique[where X=\<Omega>, where f=NOT])
  show "is_even \<circ>\<^sub>c zero = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c zero"
  proof -
    have "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c zero
      = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, metis cfunc_type_def comp_associative halve_with_parity_zero)
    also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2 left_coproj_cfunc_coprod)
    also have "... = \<t>"
      using comp_associative2 is_even_def2 is_even_nth_even_true nth_even_def2 by (typecheck_cfuncs, force)
    also have "... = is_even \<circ>\<^sub>c zero"
      by (simp add: is_even_zero)
    finally show ?thesis
      by simp
  qed

  show "is_even \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c is_even"
    by (simp add: is_even_successor)

  show "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c successor =
    NOT \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity"
  proof -
    have "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c successor
      = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: comp_associative2 halve_with_parity_successor)
    also have "... = 
        (((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c right_coproj \<nat>\<^sub>c \<nat>\<^sub>c)
          \<amalg> 
        ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor))
          \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, smt cfunc_coprod_comp comp_associative2)
    also have "... = ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: comp_associative2 left_coproj_cfunc_coprod right_coproj_cfunc_coprod)
    also have "... = ((NOT \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (NOT \<circ>\<^sub>c \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: NOT_false_is_true NOT_true_is_false comp_associative2)
    also have "... = NOT \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, smt cfunc_coprod_comp comp_associative2 terminal_func_unique)
    finally show ?thesis.
  qed
qed

lemma is_odd_def3:
  "is_odd = ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)) \<circ>\<^sub>c halve_with_parity"
proof (etcs_rule natural_number_object_func_unique[where X=\<Omega>, where f=NOT])
  show "is_odd \<circ>\<^sub>c zero = ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c zero"
  proof -
    have "((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c zero
      = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, metis cfunc_type_def comp_associative halve_with_parity_zero)
    also have "... = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2 left_coproj_cfunc_coprod)
    also have "... = \<f>"
      using comp_associative2 is_odd_nth_even_false is_odd_type is_odd_zero nth_even_def2 by (typecheck_cfuncs, force)
    also have "... = is_odd \<circ>\<^sub>c zero"
      by (simp add: is_odd_def2)
    finally show ?thesis
      by simp
  qed

  show "is_odd \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c is_odd"
    by (simp add: is_odd_successor)

  show "((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c successor =
    NOT \<circ>\<^sub>c (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity"
  proof -
    have "((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c successor
      = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: comp_associative2 halve_with_parity_successor)
    also have "... = 
        (((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c right_coproj \<nat>\<^sub>c \<nat>\<^sub>c)
          \<amalg> 
        ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor))
          \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, smt cfunc_coprod_comp comp_associative2)
    also have "... = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: comp_associative2 left_coproj_cfunc_coprod right_coproj_cfunc_coprod)
    also have "... = ((NOT \<circ>\<^sub>c \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (NOT \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: NOT_false_is_true NOT_true_is_false comp_associative2)
    also have "... = NOT \<circ>\<^sub>c (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, smt cfunc_coprod_comp comp_associative2 terminal_func_unique)
    finally show ?thesis.
  qed
qed

lemma nth_even_or_nth_odd:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(\<exists> m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> nth_even \<circ>\<^sub>c m = n) \<or> (\<exists> m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> nth_odd \<circ>\<^sub>c m = n)"
proof -
  have "(\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> halve_with_parity \<circ>\<^sub>c n = left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m)
      \<or> (\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> halve_with_parity \<circ>\<^sub>c n = right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m)"
    by (rule coprojs_jointly_surj, insert assms, typecheck_cfuncs)
  then show ?thesis
  proof 
    assume "\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> halve_with_parity \<circ>\<^sub>c n = left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m"
    then obtain m where m_type: "m \<in>\<^sub>c \<nat>\<^sub>c" and m_def: "halve_with_parity \<circ>\<^sub>c n = left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m"
      by auto
    then have "((nth_even \<amalg> nth_odd) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c n = ((nth_even \<amalg> nth_odd) \<circ>\<^sub>c left_coproj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c m"
      by (typecheck_cfuncs, smt assms comp_associative2)
    then have "n = nth_even \<circ>\<^sub>c m"
      using assms by (typecheck_cfuncs_prems, smt comp_associative2 halve_with_parity_nth_even id_left_unit2 nth_even_nth_odd_halve_with_parity)
    then have "\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> nth_even \<circ>\<^sub>c m = n"
      using m_type by auto
    then show ?thesis
      by simp
  next
    assume "\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> halve_with_parity \<circ>\<^sub>c n = right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m"
    then obtain m where m_type: "m \<in>\<^sub>c \<nat>\<^sub>c" and m_def: "halve_with_parity \<circ>\<^sub>c n = right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m"
      by auto
    then have "((nth_even \<amalg> nth_odd) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c n = ((nth_even \<amalg> nth_odd) \<circ>\<^sub>c right_coproj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c m"
      by (typecheck_cfuncs, smt assms comp_associative2)
    then have "n = nth_odd \<circ>\<^sub>c m"
      using assms by (typecheck_cfuncs_prems, smt comp_associative2 halve_with_parity_nth_odd id_left_unit2 nth_even_nth_odd_halve_with_parity)
    then show ?thesis
      using m_type by auto
  qed
qed

lemma is_even_exists_nth_even:
  assumes "is_even \<circ>\<^sub>c n = \<t>" and n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> n = nth_even \<circ>\<^sub>c m"
proof (rule ccontr)
  assume "\<nexists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> n = nth_even \<circ>\<^sub>c m"
  then obtain m where m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_def: "n = nth_odd \<circ>\<^sub>c m"
    using n_type nth_even_or_nth_odd by blast
  then have "is_even \<circ>\<^sub>c nth_odd \<circ>\<^sub>c m = \<t>"
    using assms(1) by blast
  then have "is_odd \<circ>\<^sub>c nth_odd \<circ>\<^sub>c m = \<f>"
    using NOT_true_is_false NOT_type comp_associative2 is_even_def2 is_odd_not_is_even n_def n_type by fastforce
  then have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m = \<f>"
    by (typecheck_cfuncs_prems, smt comp_associative2 is_odd_nth_odd_true terminal_func_type true_func_type)
  then have "\<t> = \<f>"
    by (typecheck_cfuncs_prems, metis id_right_unit2 id_type one_unique_element)
  then show False
    using true_false_distinct by auto
qed

lemma is_odd_exists_nth_odd:
  assumes "is_odd \<circ>\<^sub>c n = \<t>" and n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> n = nth_odd \<circ>\<^sub>c m"
proof (rule ccontr)
  assume "\<nexists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> n = nth_odd \<circ>\<^sub>c m"
  then obtain m where m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_def: "n = nth_even \<circ>\<^sub>c m"
    using n_type nth_even_or_nth_odd by blast
  then have "is_odd \<circ>\<^sub>c nth_even \<circ>\<^sub>c m = \<t>"
    using assms(1) by blast
  then have "is_even \<circ>\<^sub>c nth_even \<circ>\<^sub>c m = \<f>"
    using NOT_true_is_false NOT_type comp_associative2 is_even_not_is_odd is_odd_def2 n_def n_type by fastforce
  then have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m = \<f>"
    by (typecheck_cfuncs_prems, smt comp_associative2 is_even_nth_even_true terminal_func_type true_func_type)
  then have "\<t> = \<f>"
    by (typecheck_cfuncs_prems, metis id_right_unit2 id_type one_unique_element)
  then show False
    using true_false_distinct by auto
qed

end