section \<open>Truth Values and Characteristic Functions\<close>

theory Truth
  imports Equalizer
begin

text \<open>The axiomatization below corresponds to Axiom 5 (Truth-Value Object) in Halvorson.\<close>
axiomatization
  true_func :: "cfunc" ("\<t>") and
  false_func  :: "cfunc" ("\<f>") and
  truth_value_set :: "cset" ("\<Omega>")
where
  true_func_type[type_rule]: "\<t> \<in>\<^sub>c \<Omega>" and
  false_func_type[type_rule]: "\<f> \<in>\<^sub>c \<Omega>" and
  true_false_distinct: "\<t> \<noteq> \<f>" and
  true_false_only_truth_values: "x \<in>\<^sub>c \<Omega> \<Longrightarrow> x = \<f> \<or> x = \<t>" and
  characteristic_function_exists:
    "m : B \<rightarrow> X \<Longrightarrow> monomorphism m \<Longrightarrow> \<exists>! \<chi>. is_pullback B \<one> X \<Omega> (\<beta>\<^bsub>B\<^esub>) \<t> m \<chi>"

definition characteristic_func :: "cfunc \<Rightarrow> cfunc" where
  "characteristic_func m =
    (THE \<chi>. monomorphism m \<longrightarrow> is_pullback (domain m) \<one> (codomain m) \<Omega> (\<beta>\<^bsub>domain m\<^esub>) \<t> m \<chi>)"

lemma characteristic_func_is_pullback:
  assumes "m : B \<rightarrow> X" "monomorphism m"
  shows "is_pullback B \<one> X \<Omega> (\<beta>\<^bsub>B\<^esub>) \<t> m (characteristic_func m)"
proof -
  obtain \<chi> where chi_is_pullback: "is_pullback B \<one> X \<Omega> (\<beta>\<^bsub>B\<^esub>) \<t> m \<chi>"
    using assms characteristic_function_exists by blast

  have "monomorphism m \<longrightarrow> is_pullback (domain m) \<one> (codomain m) \<Omega> (\<beta>\<^bsub>domain m\<^esub>) \<t> m (characteristic_func m)"
    unfolding characteristic_func_def
  proof (rule theI', rule ex1I[where a= \<chi>], clarify)
    show "is_pullback (domain m) \<one> (codomain m) \<Omega> (\<beta>\<^bsub>domain m\<^esub>) \<t> m \<chi>"
      using assms(1) cfunc_type_def chi_is_pullback by auto
    show "\<And>x. monomorphism m \<longrightarrow> is_pullback (domain m) \<one> (codomain m) \<Omega> (\<beta>\<^bsub>domain m\<^esub>) \<t> m x \<Longrightarrow> x = \<chi>"
      using assms cfunc_type_def characteristic_function_exists chi_is_pullback by fastforce
  qed
  then show "is_pullback B \<one> X \<Omega> (\<beta>\<^bsub>B\<^esub>) \<t> m (characteristic_func m)"
    using assms cfunc_type_def by auto
qed

lemma characteristic_func_type[type_rule]:
  assumes "m : B \<rightarrow> X" "monomorphism m"
  shows "characteristic_func m : X \<rightarrow> \<Omega>"
proof -
  have "is_pullback B \<one> X \<Omega> (\<beta>\<^bsub>B\<^esub>) \<t> m (characteristic_func m)"
    using assms by (rule characteristic_func_is_pullback)
  then show "characteristic_func m : X \<rightarrow> \<Omega>"
    unfolding is_pullback_def by auto
qed

lemma characteristic_func_eq:
  assumes "m : B \<rightarrow> X" "monomorphism m"
  shows "characteristic_func m \<circ>\<^sub>c m = \<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>"
  using assms characteristic_func_is_pullback unfolding is_pullback_def by auto

lemma monomorphism_equalizes_char_func:
  assumes m_type[type_rule]: "m : B \<rightarrow> X" and m_mono[type_rule]: "monomorphism m"
  shows "equalizer B m (characteristic_func m) (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>)"
  unfolding equalizer_def
proof (rule exI[where x=X], rule exI[where x=\<Omega>], safe)
  show "characteristic_func m : X \<rightarrow> \<Omega>"
    by typecheck_cfuncs
  show "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<Omega>"
    by typecheck_cfuncs
  show "m : B \<rightarrow> X"
    by typecheck_cfuncs
  have comm: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub> = characteristic_func m \<circ>\<^sub>c m"
    using characteristic_func_eq m_mono m_type by auto
  then have "\<beta>\<^bsub>B\<^esub> = \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c m"
    using m_type terminal_func_comp by auto
  then show "characteristic_func m \<circ>\<^sub>c m = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c m"
    using comm comp_associative2 by (typecheck_cfuncs, auto)
next
  show "\<And>h F. h : F \<rightarrow> X \<Longrightarrow> characteristic_func m \<circ>\<^sub>c h = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c h \<Longrightarrow> \<exists>k. k : F \<rightarrow> B \<and> m \<circ>\<^sub>c k = h"
    by (typecheck_cfuncs, smt (verit, ccfv_threshold) cfunc_type_def characteristic_func_is_pullback comp_associative comp_type is_pullback_def m_mono)
next
  show "\<And>F k y.  characteristic_func m \<circ>\<^sub>c m \<circ>\<^sub>c k = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c m \<circ>\<^sub>c k \<Longrightarrow> k : F \<rightarrow> B \<Longrightarrow> y : F \<rightarrow> B \<Longrightarrow> m \<circ>\<^sub>c y = m \<circ>\<^sub>c k \<Longrightarrow> k = y"
      by (typecheck_cfuncs, smt m_mono monomorphism_def2)
qed

lemma characteristic_func_true_relative_member:
  assumes "m : B \<rightarrow> X" "monomorphism m" "x \<in>\<^sub>c X"
  assumes characteristic_func_true: "characteristic_func m \<circ>\<^sub>c x = \<t>"
  shows "x \<in>\<^bsub>X\<^esub> (B,m)"
  unfolding relative_member_def2 factors_through_def
proof (insert assms, clarify)
  have "is_pullback B \<one> X \<Omega> (\<beta>\<^bsub>B\<^esub>) \<t> m (characteristic_func m)"
    by (simp add: assms characteristic_func_is_pullback)
  then have "\<exists>j. j : \<one> \<rightarrow> B \<and> \<beta>\<^bsub>B\<^esub> \<circ>\<^sub>c j = id \<one> \<and> m \<circ>\<^sub>c j = x"
    unfolding is_pullback_def using assms by (metis id_right_unit2 id_type true_func_type)
  then show "\<exists>j. j : domain x \<rightarrow> domain m \<and> m \<circ>\<^sub>c j = x"
    using assms(1,3) cfunc_type_def by auto
qed

lemma characteristic_func_false_not_relative_member:
  assumes "m : B \<rightarrow> X" "monomorphism m" "x \<in>\<^sub>c X"
  assumes characteristic_func_true: "characteristic_func m \<circ>\<^sub>c x = \<f>"
  shows "\<not> (x \<in>\<^bsub>X\<^esub> (B,m))"
  unfolding relative_member_def2 factors_through_def
proof (insert assms, clarify)
  fix h
  assume x_def: "x = m \<circ>\<^sub>c h"
  assume "h : domain (m \<circ>\<^sub>c h) \<rightarrow> domain m"
  then have h_type: "h \<in>\<^sub>c B"
    using assms(1,3) cfunc_type_def x_def by auto

  have "is_pullback B \<one> X \<Omega> (\<beta>\<^bsub>B\<^esub>) \<t> m (characteristic_func m)"
    by (simp add: assms characteristic_func_is_pullback)
  then have char_m_true: "characteristic_func m \<circ>\<^sub>c m = \<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>"
    unfolding is_pullback_def by auto

  then have "characteristic_func m \<circ>\<^sub>c m \<circ>\<^sub>c h = \<f>"
    using x_def characteristic_func_true by auto
  then have "(characteristic_func m \<circ>\<^sub>c m) \<circ>\<^sub>c h = \<f>"
    using assms h_type by (typecheck_cfuncs, simp add: comp_associative2)
  then have "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>) \<circ>\<^sub>c h = \<f>"    
    using char_m_true by auto
  then have "\<t> = \<f>"
    by (metis cfunc_type_def comp_associative h_type id_right_unit2 id_type one_unique_element
        terminal_func_comp terminal_func_type true_func_type)
  then show False
    using true_false_distinct by auto
qed

lemma rel_mem_char_func_true:
  assumes "m : B \<rightarrow> X" "monomorphism m" "x \<in>\<^sub>c X"
  assumes "x \<in>\<^bsub>X\<^esub> (B,m)"
  shows "characteristic_func m \<circ>\<^sub>c x = \<t>"
  by (meson assms(4) characteristic_func_false_not_relative_member characteristic_func_type comp_type relative_member_def2 true_false_only_truth_values)

lemma not_rel_mem_char_func_false:
  assumes "m : B \<rightarrow> X" "monomorphism m" "x \<in>\<^sub>c X"
  assumes "\<not> (x \<in>\<^bsub>X\<^esub> (B,m))"
  shows "characteristic_func m \<circ>\<^sub>c x = \<f>"
  by (meson assms characteristic_func_true_relative_member characteristic_func_type comp_type true_false_only_truth_values)

text \<open>The lemma below corresponds to Proposition 2.2.2 in Halvorson.\<close>
lemma "card {x. x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>} = 4"
proof -
  have "{x. x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>} = {\<langle>\<t>,\<t>\<rangle>, \<langle>\<t>,\<f>\<rangle>, \<langle>\<f>,\<t>\<rangle>, \<langle>\<f>,\<f>\<rangle>}"
    by (auto simp add: cfunc_prod_type true_func_type false_func_type,
        smt cfunc_prod_unique comp_type left_cart_proj_type right_cart_proj_type true_false_only_truth_values)
  then show "card {x. x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>} = 4"
    using element_pair_eq false_func_type true_false_distinct true_func_type by auto
qed

subsection \<open>Equality Predicate\<close>

definition eq_pred :: "cset \<Rightarrow> cfunc" where
  "eq_pred X = (THE \<chi>. is_pullback X \<one> (X \<times>\<^sub>c X) \<Omega> (\<beta>\<^bsub>X\<^esub>) \<t> (diagonal X) \<chi>)"

lemma eq_pred_pullback: "is_pullback X \<one> (X \<times>\<^sub>c X) \<Omega> (\<beta>\<^bsub>X\<^esub>) \<t> (diagonal X) (eq_pred X)"
  unfolding eq_pred_def
  by (rule the1I2, simp_all add: characteristic_function_exists diag_mono diagonal_type)

lemma eq_pred_type[type_rule]:
  "eq_pred X : X \<times>\<^sub>c X \<rightarrow> \<Omega>"
  using eq_pred_pullback unfolding is_pullback_def  by auto

lemma eq_pred_square: "eq_pred X \<circ>\<^sub>c diagonal X = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>"
  using eq_pred_pullback unfolding is_pullback_def  by auto

lemma eq_pred_iff_eq:
  assumes "x : \<one> \<rightarrow> X" "y : \<one> \<rightarrow> X"
  shows "(x = y) = (eq_pred X \<circ>\<^sub>c \<langle>x, y\<rangle> = \<t>)"
proof safe
  assume x_eq_y: "x = y"

  have "(eq_pred X \<circ>\<^sub>c \<langle>id\<^sub>c X,id\<^sub>c X\<rangle>) \<circ>\<^sub>c y = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c y"
    using eq_pred_square unfolding diagonal_def by auto
  then have "eq_pred X \<circ>\<^sub>c \<langle>y, y\<rangle> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c y"
    using assms diagonal_type id_type
    by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 diagonal_def id_left_unit2)
  then show "eq_pred X \<circ>\<^sub>c \<langle>y, y\<rangle> = \<t>"
    using assms id_type
    by (typecheck_cfuncs, smt comp_associative2 terminal_func_comp terminal_func_type terminal_func_unique id_right_unit2)
next
  assume "eq_pred X \<circ>\<^sub>c \<langle>x,y\<rangle> = \<t>"
  then have "eq_pred X \<circ>\<^sub>c \<langle>x,y\<rangle> = \<t> \<circ>\<^sub>c id \<one>"
    using id_right_unit2 true_func_type by auto
  then obtain j  where j_type: "j : \<one> \<rightarrow> X" and "diagonal X \<circ>\<^sub>c j = \<langle>x,y\<rangle>"
    using eq_pred_pullback assms unfolding is_pullback_def by (metis cfunc_prod_type id_type)
  then have "\<langle>j,j\<rangle> = \<langle>x,y\<rangle>"
    using diag_on_elements by auto
  then show "x = y"
    using assms element_pair_eq j_type by auto
qed

lemma eq_pred_iff_eq_conv:
  assumes "x : \<one> \<rightarrow> X" "y : \<one> \<rightarrow> X"
  shows "(x \<noteq> y) = (eq_pred X \<circ>\<^sub>c \<langle>x, y\<rangle> = \<f>)"
proof(safe)
  assume "x \<noteq> y"
  then show "eq_pred X \<circ>\<^sub>c \<langle>x,y\<rangle> = \<f>"
    using assms eq_pred_iff_eq true_false_only_truth_values by (typecheck_cfuncs, blast)
next
  show "eq_pred X \<circ>\<^sub>c \<langle>y,y\<rangle> = \<f> \<Longrightarrow> x = y \<Longrightarrow> False"
    by (metis assms(1) eq_pred_iff_eq true_false_distinct)
qed

lemma eq_pred_iff_eq_conv2:
  assumes "x : \<one> \<rightarrow> X" "y : \<one> \<rightarrow> X"
  shows "(x \<noteq> y) = (eq_pred X \<circ>\<^sub>c \<langle>x, y\<rangle> \<noteq> \<t>)"
  using assms eq_pred_iff_eq by presburger

lemma eq_pred_of_monomorphism:
  assumes m_type[type_rule]: "m : X \<rightarrow> Y" and m_mono: "monomorphism m"
  shows "eq_pred Y \<circ>\<^sub>c (m \<times>\<^sub>f m) = eq_pred X"
proof (rule one_separator[where X="X \<times>\<^sub>c X", where Y=\<Omega>])
  show "eq_pred Y \<circ>\<^sub>c m \<times>\<^sub>f m : X \<times>\<^sub>c X \<rightarrow> \<Omega>"
    by typecheck_cfuncs
  show "eq_pred X : X \<times>\<^sub>c X \<rightarrow> \<Omega>"
    by typecheck_cfuncs
next
  fix x
  assume "x \<in>\<^sub>c X \<times>\<^sub>c X"
  then obtain x1 x2 where x_def: "x = \<langle>x1, x2\<rangle>" and x1_type[type_rule]: "x1 \<in>\<^sub>c X" and x2_type[type_rule]: "x2 \<in>\<^sub>c X"
    using cart_prod_decomp by blast
  show "(eq_pred Y \<circ>\<^sub>c m \<times>\<^sub>f m) \<circ>\<^sub>c x = eq_pred X \<circ>\<^sub>c x"
    unfolding x_def
  proof (cases "(eq_pred Y \<circ>\<^sub>c m \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = \<t>")
    assume LHS: "(eq_pred Y \<circ>\<^sub>c m \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = \<t>"
    then have "eq_pred Y \<circ>\<^sub>c (m \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = \<t>"
      by (typecheck_cfuncs, simp add: comp_associative2)
    then have "eq_pred Y \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c x1, m \<circ>\<^sub>c x2\<rangle> = \<t>"
      by (typecheck_cfuncs, auto simp add: cfunc_cross_prod_comp_cfunc_prod)
    then have "m \<circ>\<^sub>c x1 = m \<circ>\<^sub>c x2"
      by (typecheck_cfuncs_prems, simp add: eq_pred_iff_eq)
    then have "x1 = x2"
      using m_mono m_type monomorphism_def3 x1_type x2_type by blast
    then have RHS: "eq_pred X \<circ>\<^sub>c \<langle>x1,x2\<rangle> = \<t>"
      by (typecheck_cfuncs, insert eq_pred_iff_eq, blast)
    show "(eq_pred Y \<circ>\<^sub>c m \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = eq_pred X \<circ>\<^sub>c \<langle>x1,x2\<rangle>"
      using LHS RHS by auto
  next
    assume "(eq_pred Y \<circ>\<^sub>c m \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>x1,x2\<rangle> \<noteq> \<t>"
    then have LHS: "(eq_pred Y \<circ>\<^sub>c m \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = \<f>"
      by (typecheck_cfuncs, meson true_false_only_truth_values)
    then have "eq_pred Y \<circ>\<^sub>c (m \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = \<f>"
      by (typecheck_cfuncs, simp add: comp_associative2)
    then have "eq_pred Y \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c x1, m \<circ>\<^sub>c x2\<rangle> = \<f>"
      by (typecheck_cfuncs, auto simp add: cfunc_cross_prod_comp_cfunc_prod)
    then have "m \<circ>\<^sub>c x1 \<noteq> m \<circ>\<^sub>c x2"
      using eq_pred_iff_eq_conv by (typecheck_cfuncs_prems, blast)
    then have "x1 \<noteq> x2"
      by auto
    then have RHS: "eq_pred X \<circ>\<^sub>c \<langle>x1,x2\<rangle> = \<f>"
      using eq_pred_iff_eq_conv by (typecheck_cfuncs, blast)
    show "(eq_pred Y \<circ>\<^sub>c m \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = eq_pred X \<circ>\<^sub>c \<langle>x1,x2\<rangle>"
      using LHS RHS by auto
  qed
qed

lemma eq_pred_true_extract_right: 
    assumes "x \<in>\<^sub>c X" 
    shows  "eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>, id X\<rangle> \<circ>\<^sub>c x = \<t>"
    using assms cart_prod_extract_right eq_pred_iff_eq by fastforce

lemma eq_pred_false_extract_right: 
    assumes "x \<in>\<^sub>c X"  "y \<in>\<^sub>c X" "x \<noteq> y"
    shows  "eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>, id X\<rangle> \<circ>\<^sub>c y = \<f>"
    using assms cart_prod_extract_right eq_pred_iff_eq true_false_only_truth_values  by (typecheck_cfuncs, fastforce)

subsection \<open>Properties of Monomorphisms and Epimorphisms\<close>

text \<open>The lemma below corresponds to Exercise 2.2.3 in Halvorson.\<close>
lemma regmono_is_mono: "regular_monomorphism m \<Longrightarrow> monomorphism m"
  using equalizer_is_monomorphism regular_monomorphism_def by blast

text \<open>The lemma below corresponds to Proposition 2.2.4 in Halvorson.\<close>
lemma mono_is_regmono:
  shows "monomorphism m \<Longrightarrow> regular_monomorphism m"
  unfolding regular_monomorphism_def
  by (rule exI[where x="characteristic_func m"], 
      rule exI[where x="\<t> \<circ>\<^sub>c \<beta>\<^bsub>codomain(m)\<^esub>"], 
      typecheck_cfuncs, auto simp add: cfunc_type_def monomorphism_equalizes_char_func)

text \<open>The lemma below corresponds to Proposition 2.2.5 in Halvorson.\<close>
lemma epi_mon_is_iso:
  assumes "epimorphism f" "monomorphism f"
  shows "isomorphism f"
  using assms epi_regmon_is_iso mono_is_regmono by auto

text \<open>The lemma below corresponds to Proposition 2.2.8 in Halvorson.\<close>
lemma epi_is_surj:
  assumes "p: X \<rightarrow> Y" "epimorphism p"
  shows "surjective p"
  unfolding surjective_def
proof(rule ccontr)
  assume a1: "\<not> (\<forall>y. y \<in>\<^sub>c codomain p \<longrightarrow> (\<exists>x. x \<in>\<^sub>c domain p \<and> p \<circ>\<^sub>c x = y))"
  have "\<exists>y. y \<in>\<^sub>c Y \<and> \<not>(\<exists>x. x \<in>\<^sub>c X \<and> p \<circ>\<^sub>c x = y)"
    using a1 assms(1) cfunc_type_def by auto
  then obtain y0 where y_def: "y0 \<in>\<^sub>c Y \<and> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> p \<circ>\<^sub>c x \<noteq> y0)"
    by auto
  have mono: "monomorphism y0"
    using element_monomorphism y_def by blast
  obtain g where g_def: "g = eq_pred Y \<circ>\<^sub>c \<langle>y0 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id Y\<rangle>"
    by simp
  have g_right_arg_type: "\<langle>y0 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id Y\<rangle> : Y \<rightarrow> Y \<times>\<^sub>c Y"
    by (meson cfunc_prod_type comp_type id_type terminal_func_type y_def)
  then have g_type[type_rule]: "g: Y \<rightarrow> \<Omega>"
    using comp_type eq_pred_type g_def by blast

  have gpx_Eqs_f: "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> g \<circ>\<^sub>c p \<circ>\<^sub>c x = \<f>"
  proof(rule ccontr)
    assume "\<not> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> g \<circ>\<^sub>c p \<circ>\<^sub>c x = \<f>)"
    then obtain x where x_type: "x \<in>\<^sub>c X" and bwoc: "g \<circ>\<^sub>c p \<circ>\<^sub>c x \<noteq> \<f>"
      by blast
    (* have contradiction: "\<exists>s. s \<in>\<^sub>c p\<^sup>-\<^sup>1{y0}" *)
    show False
      by (smt (verit) assms(1) bwoc cfunc_type_def comp_associative comp_type eq_pred_false_extract_right eq_pred_type g_def g_right_arg_type x_type y_def)
  qed
  obtain h where h_def: "h = \<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>" and h_type[type_rule]:"h: Y \<rightarrow> \<Omega>"
    by (typecheck_cfuncs, simp)
  have hpx_eqs_f: "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> h \<circ>\<^sub>c p \<circ>\<^sub>c x = \<f>"
    by (smt assms(1) cfunc_type_def codomain_comp comp_associative false_func_type h_def id_right_unit2 id_type terminal_func_comp terminal_func_type terminal_func_unique)
  have gp_eqs_hp: "g \<circ>\<^sub>c p = h \<circ>\<^sub>c p"
  proof(rule one_separator[where X=X,where Y=\<Omega>])
    show "g \<circ>\<^sub>c p : X \<rightarrow> \<Omega>"
      using assms by typecheck_cfuncs
    show "h \<circ>\<^sub>c p : X \<rightarrow> \<Omega>"
      using assms by typecheck_cfuncs
    show "\<And>x. x \<in>\<^sub>c X \<Longrightarrow> (g \<circ>\<^sub>c p) \<circ>\<^sub>c x = (h \<circ>\<^sub>c p) \<circ>\<^sub>c x"
      using assms(1) comp_associative2 g_type gpx_Eqs_f h_type hpx_eqs_f by auto
  qed
  have g_not_h: "g \<noteq> h"
  proof -
   have f1: "\<forall>c. \<beta>\<^bsub>codomain c\<^esub> \<circ>\<^sub>c c = \<beta>\<^bsub>domain c\<^esub>"
    by (simp add: cfunc_type_def terminal_func_comp)
   have f2: "domain \<langle>y0 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>,id\<^sub>c Y\<rangle> = Y"
    using cfunc_type_def g_right_arg_type by blast
  have f3: "codomain \<langle>y0 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>,id\<^sub>c Y\<rangle> = Y \<times>\<^sub>c Y"
    using cfunc_type_def g_right_arg_type by blast
  have f4: "codomain y0 = Y"
    using cfunc_type_def y_def by presburger
  have "\<forall>c. domain (eq_pred c) = c \<times>\<^sub>c c"
    using cfunc_type_def eq_pred_type by auto
  then have "g \<circ>\<^sub>c y0 \<noteq> \<f>"
    using f4 f3 f2 by (metis (no_types) eq_pred_true_extract_right comp_associative g_def true_false_distinct y_def)
  then show ?thesis
    using f1 by (metis (no_types) cfunc_type_def comp_associative false_func_type h_def id_right_unit2 id_type one_unique_element terminal_func_type y_def)
qed
  then show False
    using gp_eqs_hp assms cfunc_type_def epimorphism_def g_type h_type by auto
qed

text \<open>The lemma below corresponds to Proposition 2.2.9 in Halvorson.\<close>
lemma pullback_of_epi_is_epi1:
assumes "f: Y \<rightarrow> Z" "epimorphism f" "is_pullback A Y X Z q1 f q0 g"
shows "epimorphism q0" 
proof - 
  have surj_f: "surjective f"
    using assms(1,2) epi_is_surj by auto
  have "surjective (q0)"
    unfolding surjective_def
  proof(clarify)
    fix y
    assume y_type: "y \<in>\<^sub>c codomain q0"
    then have codomain_gy: "g \<circ>\<^sub>c y \<in>\<^sub>c Z"
      using assms(3) cfunc_type_def is_pullback_def  by (typecheck_cfuncs, auto)
    then have z_exists: "\<exists> z. z \<in>\<^sub>c Y \<and> f \<circ>\<^sub>c z = g \<circ>\<^sub>c y"
      using assms(1) cfunc_type_def surj_f surjective_def by auto
    then obtain z where z_def: "z \<in>\<^sub>c Y \<and> f \<circ>\<^sub>c z = g \<circ>\<^sub>c y"
      by blast
    then have "\<exists>! k. k: \<one> \<rightarrow> A \<and> q0 \<circ>\<^sub>c k = y \<and> q1 \<circ>\<^sub>c k =z"
      by (smt (verit, ccfv_threshold) assms(3) cfunc_type_def is_pullback_def y_type)
    then show "\<exists>x. x \<in>\<^sub>c domain q0 \<and> q0 \<circ>\<^sub>c x = y"
      using assms(3) cfunc_type_def is_pullback_def  by auto
  qed 
  then show ?thesis
    using surjective_is_epimorphism by blast
qed

text \<open>The lemma below corresponds to Proposition 2.2.9b in Halvorson.\<close>
lemma pullback_of_epi_is_epi2:
assumes "g: X \<rightarrow> Z" "epimorphism g" "is_pullback A Y X Z q1 f q0 g"
shows "epimorphism q1" 
proof - 
  have surj_g: "surjective g"
    using assms(1) assms(2) epi_is_surj by auto
  have "surjective q1"
    unfolding surjective_def
  proof(clarify)
    fix y
    assume y_type: "y \<in>\<^sub>c codomain q1"
    then have codomain_gy: "f \<circ>\<^sub>c y \<in>\<^sub>c Z"
      using assms(3) cfunc_type_def comp_type is_pullback_def  by auto
    then have z_exists: "\<exists> z. z \<in>\<^sub>c X \<and> g \<circ>\<^sub>c z = f \<circ>\<^sub>c y"
      using assms(1) cfunc_type_def surj_g surjective_def by auto
    then obtain z where z_def: "z \<in>\<^sub>c X \<and> g \<circ>\<^sub>c z = f \<circ>\<^sub>c y"
      by blast
    then have "\<exists>! k. k: \<one> \<rightarrow> A \<and> q0 \<circ>\<^sub>c k = z \<and> q1 \<circ>\<^sub>c k =y"
      by (smt (verit, ccfv_threshold) assms(3) cfunc_type_def is_pullback_def  y_type)      
    then show "\<exists>x. x \<in>\<^sub>c domain q1 \<and> q1 \<circ>\<^sub>c x = y"
      using assms(3) cfunc_type_def is_pullback_def  by auto
  qed
  then show ?thesis
    using surjective_is_epimorphism by blast
qed

text \<open>The lemma below corresponds to Proposition 2.2.9c in Halvorson.\<close>
lemma pullback_of_mono_is_mono1:
assumes "g: X \<rightarrow> Z" "monomorphism f" "is_pullback A Y X Z q1 f q0 g"
shows "monomorphism q0" 
  unfolding monomorphism_def2
proof(clarify)
  fix u v Q a x
  assume u_type: "u : Q \<rightarrow> a"  
  assume v_type: "v : Q \<rightarrow> a"
  assume q0_type: "q0 :  a \<rightarrow> x"    
  assume equals: "q0 \<circ>\<^sub>c u = q0 \<circ>\<^sub>c v" 

  have a_is_A: "a = A"
    using assms(3) cfunc_type_def is_pullback_def q0_type  by force
  have x_is_X: "x = X"
    using assms(3) cfunc_type_def is_pullback_def q0_type  by fastforce
  have u_type2[type_rule]: "u : Q \<rightarrow> A"
    using a_is_A u_type by blast
  have v_type2[type_rule]: "v : Q \<rightarrow> A"
    using a_is_A v_type by blast
  have q1_type2[type_rule]: "q0 : A \<rightarrow> X"
    using a_is_A q0_type x_is_X by blast

  have eqn1: "g \<circ>\<^sub>c (q0 \<circ>\<^sub>c u) = f \<circ>\<^sub>c (q1 \<circ>\<^sub>c v)"
  proof - 
    have "g \<circ>\<^sub>c (q0 \<circ>\<^sub>c u) = g \<circ>\<^sub>c q0 \<circ>\<^sub>c v"
      by (simp add: equals)
    also have "... = f \<circ>\<^sub>c (q1 \<circ>\<^sub>c v)"
      using assms(3) cfunc_type_def comp_associative is_pullback_def by (typecheck_cfuncs, force)
    finally show ?thesis.
  qed 

  have eqn2: "q1 \<circ>\<^sub>c u =  q1  \<circ>\<^sub>c v"
  proof - 
    have f1: "f \<circ>\<^sub>c q1 \<circ>\<^sub>c u = g \<circ>\<^sub>c q0 \<circ>\<^sub>c u"
      using assms(3) comp_associative2 is_pullback_def  by (typecheck_cfuncs, auto)
    also have "... = g \<circ>\<^sub>c q0 \<circ>\<^sub>c v"
      by (simp add: equals)
    also have "... = f \<circ>\<^sub>c q1 \<circ>\<^sub>c v"
      using eqn1 equals by fastforce
    then show ?thesis
      by (typecheck_cfuncs, smt (verit, ccfv_threshold) f1 assms(2,3) eqn1 is_pullback_def monomorphism_def3)
  qed

  have uniqueness: "\<exists>! j. (j : Q \<rightarrow> A \<and> q1 \<circ>\<^sub>c j = q1 \<circ>\<^sub>c v \<and> q0 \<circ>\<^sub>c j = q0 \<circ>\<^sub>c u)"
   by (typecheck_cfuncs, smt (verit, ccfv_threshold) assms(3) eqn1 is_pullback_def)
  then show "u = v"
    using eqn2 equals uniqueness by (typecheck_cfuncs, auto)
qed

text \<open>The lemma below corresponds to Proposition 2.2.9d in Halvorson.\<close>
lemma pullback_of_mono_is_mono2:
assumes "g: X \<rightarrow> Z" "monomorphism g" "is_pullback A Y X Z q1 f q0 g"
shows "monomorphism q1" 
  unfolding monomorphism_def2
proof(clarify)
  fix u v Q a y
  assume u_type: "u : Q \<rightarrow> a"  
  assume v_type: "v : Q \<rightarrow> a"
  assume q1_type: "q1 :  a \<rightarrow> y" 
  assume equals: "q1 \<circ>\<^sub>c u = q1 \<circ>\<^sub>c v" 

  have a_is_A: "a = A"
    using assms(3) cfunc_type_def is_pullback_def q1_type  by force
  have y_is_Y: "y = Y"
    using assms(3) cfunc_type_def is_pullback_def q1_type  by fastforce
  have u_type2[type_rule]: "u : Q \<rightarrow> A"
    using a_is_A u_type by blast
  have v_type2[type_rule]: "v : Q \<rightarrow> A"
    using a_is_A v_type by blast
  have q1_type2[type_rule]: "q1 : A \<rightarrow> Y"
    using a_is_A q1_type y_is_Y by blast

  have eqn1: "f \<circ>\<^sub>c (q1 \<circ>\<^sub>c u) = g \<circ>\<^sub>c (q0 \<circ>\<^sub>c v)"
  proof - 
    have "f \<circ>\<^sub>c (q1 \<circ>\<^sub>c u) = f \<circ>\<^sub>c q1 \<circ>\<^sub>c v"
      by (simp add: equals)
    also have "... = g \<circ>\<^sub>c (q0 \<circ>\<^sub>c v)"
      using assms(3) cfunc_type_def comp_associative is_pullback_def  by (typecheck_cfuncs, force)
    finally show ?thesis.
  qed 

  have eqn2: "q0 \<circ>\<^sub>c u =  q0  \<circ>\<^sub>c v"
  proof - 
    have f1: "g \<circ>\<^sub>c q0 \<circ>\<^sub>c u = f \<circ>\<^sub>c q1 \<circ>\<^sub>c u"
      using assms(3) comp_associative2 is_pullback_def  by (typecheck_cfuncs, auto)
    also have "... = f \<circ>\<^sub>c q1 \<circ>\<^sub>c v"
      by (simp add: equals)
    also have "... = g \<circ>\<^sub>c q0 \<circ>\<^sub>c v"
      using eqn1 equals by fastforce
    then show ?thesis
      by (typecheck_cfuncs, smt (verit, ccfv_threshold) f1 assms(2,3) eqn1 is_pullback_def monomorphism_def3)
  qed
  have uniqueness: "\<exists>! j. (j : Q \<rightarrow> A \<and> q0 \<circ>\<^sub>c j = q0 \<circ>\<^sub>c v \<and> q1 \<circ>\<^sub>c j = q1 \<circ>\<^sub>c u)"
   by (typecheck_cfuncs, smt (verit, ccfv_threshold) assms(3) eqn1 is_pullback_def)
  then show "u = v"
    using eqn2 equals uniqueness by (typecheck_cfuncs, auto)
qed

subsection \<open>Fiber Over an Element and its Connection to the Fibered Product\<close>

text \<open>The definition below corresponds to Definition 2.2.6 in Halvorson.\<close>
definition fiber :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cset" ("_\<^sup>-\<^sup>1{_}" [100,100]100) where
  "f\<^sup>-\<^sup>1{y} = (f\<^sup>-\<^sup>1\<lparr>\<one>\<rparr>\<^bsub>y\<^esub>)"

definition fiber_morphism :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" where
  "fiber_morphism f y = left_cart_proj (domain f) \<one> \<circ>\<^sub>c inverse_image_mapping f \<one> y"

lemma fiber_morphism_type[type_rule]:
  assumes "f : X \<rightarrow> Y" "y \<in>\<^sub>c Y"
  shows "fiber_morphism f y : f\<^sup>-\<^sup>1{y} \<rightarrow> X"
  unfolding fiber_def fiber_morphism_def
  using assms cfunc_type_def element_monomorphism inverse_image_subobject subobject_of_def2
  by (typecheck_cfuncs, auto)

lemma fiber_subset: 
  assumes "f : X \<rightarrow> Y" "y \<in>\<^sub>c Y"
  shows "(f\<^sup>-\<^sup>1{y}, fiber_morphism f y) \<subseteq>\<^sub>c X"
  unfolding fiber_def fiber_morphism_def
  using assms cfunc_type_def element_monomorphism inverse_image_subobject inverse_image_subobject_mapping_def
  by (typecheck_cfuncs, auto)

lemma fiber_morphism_monomorphism:
  assumes "f : X \<rightarrow> Y" "y \<in>\<^sub>c Y"
  shows "monomorphism (fiber_morphism f y)"
  using assms cfunc_type_def element_monomorphism fiber_morphism_def inverse_image_monomorphism by auto

lemma fiber_morphism_eq:
  assumes "f : X \<rightarrow> Y" "y \<in>\<^sub>c Y"
  shows "f \<circ>\<^sub>c fiber_morphism f y  = y \<circ>\<^sub>c \<beta>\<^bsub>f\<^sup>-\<^sup>1{y}\<^esub>"
proof -
  have "f \<circ>\<^sub>c fiber_morphism f y = f \<circ>\<^sub>c left_cart_proj (domain f) \<one> \<circ>\<^sub>c inverse_image_mapping f \<one> y"
    unfolding fiber_morphism_def by auto
  also have "... = y \<circ>\<^sub>c right_cart_proj X \<one> \<circ>\<^sub>c inverse_image_mapping f \<one> y"
    using assms cfunc_type_def element_monomorphism inverse_image_mapping_eq by auto
  also have "... = y \<circ>\<^sub>c \<beta>\<^bsub>f\<^sup>-\<^sup>1\<lparr>\<one>\<rparr>\<^bsub>y\<^esub>\<^esub>"
    using assms by (typecheck_cfuncs, metis element_monomorphism terminal_func_unique)
  also have "... = y \<circ>\<^sub>c \<beta>\<^bsub>f\<^sup>-\<^sup>1{y}\<^esub>"
    unfolding fiber_def by auto
  finally show ?thesis.
qed

text \<open>The lemma below corresponds to Proposition 2.2.7 in Halvorson.\<close>
lemma not_surjective_has_some_empty_preimage:
  assumes p_type[type_rule]: "p: X \<rightarrow> Y" and p_not_surj: "\<not> surjective p"
  shows "\<exists> y. y \<in>\<^sub>c Y \<and> is_empty(p\<^sup>-\<^sup>1{y})"
proof -
  have nonempty: "nonempty(Y)"
    using assms cfunc_type_def nonempty_def surjective_def by auto
  obtain y0 where y0_type[type_rule]: "y0 \<in>\<^sub>c Y" "\<forall> x. x \<in>\<^sub>c X \<longrightarrow> p\<circ>\<^sub>c x \<noteq> y0"
    using assms cfunc_type_def surjective_def by auto

  have "\<not>nonempty(p\<^sup>-\<^sup>1{y0})"
  proof (rule ccontr, clarify)
    assume a1: "nonempty(p\<^sup>-\<^sup>1{y0})"
    obtain z where z_type[type_rule]: "z \<in>\<^sub>c p\<^sup>-\<^sup>1{y0}"
      using a1 nonempty_def by blast
    have fiber_z_type: "fiber_morphism p y0 \<circ>\<^sub>c z \<in>\<^sub>c X"
      using assms(1) comp_type fiber_morphism_type y0_type z_type by auto
    have contradiction: "p \<circ>\<^sub>c fiber_morphism p y0 \<circ>\<^sub>c z = y0"
      by (typecheck_cfuncs, smt (z3) comp_associative2 fiber_morphism_eq id_right_unit2 id_type one_unique_element terminal_func_comp terminal_func_type)
    have "p \<circ>\<^sub>c (fiber_morphism p y0 \<circ>\<^sub>c z) \<noteq> y0"
      by (simp add: fiber_z_type y0_type)
    then show False
      using contradiction by blast
  qed
  then show ?thesis
    using is_empty_def nonempty_def y0_type by blast
qed

lemma fiber_iso_fibered_prod:
  assumes f_type[type_rule]: "f : X \<rightarrow> Y"
  assumes y_type[type_rule]: "y : \<one> \<rightarrow> Y"
  shows "f\<^sup>-\<^sup>1{y} \<cong> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>y\<^esub>\<one>"
  using element_monomorphism equalizers_isomorphic f_type fiber_def fibered_product_equalizer inverse_image_is_equalizer is_isomorphic_def y_type by moura

lemma fib_prod_left_id_iso:
  assumes "g : Y \<rightarrow> X"
  shows "(X \<^bsub>id(X)\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<cong> Y"
proof - 
  have is_pullback: "is_pullback (X \<^bsub>id(X)\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) Y X X (fibered_product_right_proj X (id(X)) g Y) g (fibered_product_left_proj X (id(X)) g Y) (id(X))"
    using assms fibered_product_is_pullback by (typecheck_cfuncs, blast)
  then have mono: "monomorphism(fibered_product_right_proj X (id(X)) g Y)"
    using assms by (typecheck_cfuncs, meson id_isomorphism iso_imp_epi_and_monic pullback_of_mono_is_mono2)
  have "epimorphism(fibered_product_right_proj X (id(X)) g Y)"
    by (meson id_isomorphism id_type is_pullback iso_imp_epi_and_monic pullback_of_epi_is_epi2)
  then have "isomorphism(fibered_product_right_proj X (id(X)) g Y)"
    by (simp add: epi_mon_is_iso mono)
  then show ?thesis
    using assms fibered_product_right_proj_type id_type is_isomorphic_def by blast
qed

lemma fib_prod_right_id_iso:
  assumes "f : X \<rightarrow> Y"
  shows "(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>id(Y)\<^esub> Y) \<cong> X"
proof - 
  have is_pullback: "is_pullback (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>id(Y)\<^esub> Y) Y X Y (fibered_product_right_proj X f (id(Y)) Y) (id(Y)) (fibered_product_left_proj X f (id(Y)) Y) f "
    using assms fibered_product_is_pullback by (typecheck_cfuncs, blast)
    
  then have mono: "monomorphism(fibered_product_left_proj X f (id(Y)) Y)"
    using assms by (typecheck_cfuncs, meson id_isomorphism is_pullback iso_imp_epi_and_monic pullback_of_mono_is_mono1)
  have "epimorphism(fibered_product_left_proj X f (id(Y)) Y)"
    by (meson id_isomorphism id_type is_pullback iso_imp_epi_and_monic pullback_of_epi_is_epi1)
  then have "isomorphism(fibered_product_left_proj X f (id(Y)) Y)"
    by (simp add: epi_mon_is_iso mono)
  then show ?thesis
    using assms fibered_product_left_proj_type id_type is_isomorphic_def by blast
qed

text \<open>The lemma below corresponds to the discussion at the top of page 42 in Halvorson.\<close>
lemma kernel_pair_connection:
  assumes f_type[type_rule]: "f : X \<rightarrow> Y" and g_type[type_rule]: "g : X \<rightarrow> E"
  assumes g_epi: "epimorphism g"
  assumes h_g_eq_f: "h \<circ>\<^sub>c g = f"
  assumes g_eq: "g \<circ>\<^sub>c fibered_product_left_proj X f f X = g \<circ>\<^sub>c fibered_product_right_proj X f f X "
  assumes h_type[type_rule]: "h : E \<rightarrow> Y"
  shows "\<exists>! b. b : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E \<and>
    fibered_product_left_proj E h h E \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_left_proj X f f X \<and>
    fibered_product_right_proj E h h E \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_right_proj X f f X \<and>
    epimorphism b"
proof -
  have gxg_fpmorph_eq: "(h \<circ>\<^sub>c left_cart_proj E E) \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X
        = (h \<circ>\<^sub>c right_cart_proj E E) \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X"
  proof -
    have "(h \<circ>\<^sub>c left_cart_proj E E) \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X
        = h \<circ>\<^sub>c (left_cart_proj E E \<circ>\<^sub>c (g \<times>\<^sub>f g)) \<circ>\<^sub>c fibered_product_morphism X f f X"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = h \<circ>\<^sub>c (g \<circ>\<^sub>c left_cart_proj X X) \<circ>\<^sub>c fibered_product_morphism X f f X"
      by (typecheck_cfuncs, simp add: comp_associative2 left_cart_proj_cfunc_cross_prod)
    also have "... = (h \<circ>\<^sub>c g) \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c fibered_product_morphism X f f X"
      by (typecheck_cfuncs, smt comp_associative2)
    also have "... = f \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c fibered_product_morphism X f f X"
      by (simp add: h_g_eq_f)
    also have "... = f \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c fibered_product_morphism X f f X"
      using f_type fibered_product_left_proj_def fibered_product_proj_eq fibered_product_right_proj_def by auto
    also have "... = (h \<circ>\<^sub>c g) \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c fibered_product_morphism X f f X"
      by (simp add: h_g_eq_f)
    also have "... = h \<circ>\<^sub>c (g \<circ>\<^sub>c right_cart_proj X X) \<circ>\<^sub>c fibered_product_morphism X f f X"
      by (typecheck_cfuncs, smt comp_associative2)
    also have "... = h \<circ>\<^sub>c right_cart_proj E E \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X"
      by (typecheck_cfuncs, simp add: comp_associative2 right_cart_proj_cfunc_cross_prod)
    also have "... = (h \<circ>\<^sub>c right_cart_proj E E) \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X"
      by (typecheck_cfuncs, smt comp_associative2)
    finally show ?thesis.
  qed
  have h_equalizer: "equalizer (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E) (fibered_product_morphism E h h E) (h \<circ>\<^sub>c left_cart_proj E E) (h \<circ>\<^sub>c right_cart_proj E E)"
    using fibered_product_morphism_equalizer h_type by auto
  then have "\<forall>j F. j : F \<rightarrow> E \<times>\<^sub>c E \<and> (h \<circ>\<^sub>c left_cart_proj E E) \<circ>\<^sub>c j = (h \<circ>\<^sub>c right_cart_proj E E) \<circ>\<^sub>c j \<longrightarrow>
               (\<exists>!k. k : F \<rightarrow> E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E \<and> fibered_product_morphism E h h E \<circ>\<^sub>c k = j)"
    unfolding equalizer_def using cfunc_type_def fibered_product_morphism_type h_type by (smt (verit))
  then have "(g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X  : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> E \<times>\<^sub>c E \<and> (h \<circ>\<^sub>c left_cart_proj E E) \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X = (h \<circ>\<^sub>c right_cart_proj E E) \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X \<longrightarrow>
               (\<exists>!k. k : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E \<and> fibered_product_morphism E h h E \<circ>\<^sub>c k = (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X)"
    by auto
  then obtain b where b_type[type_rule]: "b : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E"
          and b_eq: "fibered_product_morphism E h h E \<circ>\<^sub>c b = (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X"
    by (meson cfunc_cross_prod_type comp_type f_type fibered_product_morphism_type g_type gxg_fpmorph_eq)

  have "is_pullback (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) (X \<times>\<^sub>c X) (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E) (E \<times>\<^sub>c E)
      (fibered_product_morphism X f f X) (g \<times>\<^sub>f g) b (fibered_product_morphism E h h E)"
    unfolding is_pullback_def
  proof (typecheck_cfuncs, safe, metis b_eq)
    fix Z k j
    assume k_type[type_rule]: "k : Z \<rightarrow> X \<times>\<^sub>c X" and h_type[type_rule]: "j : Z \<rightarrow> E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E"
    assume k_h_eq: "(g \<times>\<^sub>f g) \<circ>\<^sub>c k = fibered_product_morphism E h h E \<circ>\<^sub>c j"

    have left_k_right_k_eq: "f \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c k = f \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c k"
    proof -
      have "f \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c k = h \<circ>\<^sub>c g \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c k"
        by (smt (z3) assms(6) comp_associative2 comp_type g_type h_g_eq_f k_type left_cart_proj_type)
      also have "... = h \<circ>\<^sub>c left_cart_proj E E \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c k"
        by (typecheck_cfuncs, simp add: comp_associative2 left_cart_proj_cfunc_cross_prod)
      also have "... = h \<circ>\<^sub>c left_cart_proj E E \<circ>\<^sub>c fibered_product_morphism E h h E \<circ>\<^sub>c j"
        by (simp add: k_h_eq)
      also have "... = ((h \<circ>\<^sub>c left_cart_proj E E) \<circ>\<^sub>c fibered_product_morphism E h h E) \<circ>\<^sub>c j"
        by (typecheck_cfuncs, smt comp_associative2)
      also have "... = ((h \<circ>\<^sub>c right_cart_proj E E) \<circ>\<^sub>c fibered_product_morphism E h h E) \<circ>\<^sub>c j"
        using equalizer_def h_equalizer by auto
      also have "... = h \<circ>\<^sub>c right_cart_proj E E \<circ>\<^sub>c fibered_product_morphism E h h E \<circ>\<^sub>c j"
        by (typecheck_cfuncs, smt comp_associative2)
      also have "... = h \<circ>\<^sub>c right_cart_proj E E \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c k"
        by (simp add: k_h_eq)
      also have "... = h \<circ>\<^sub>c g \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c k"
        by (typecheck_cfuncs, simp add: comp_associative2 right_cart_proj_cfunc_cross_prod)
      also have "... = f \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c k"
        using assms(6) comp_associative2 comp_type g_type h_g_eq_f k_type right_cart_proj_type by blast
      finally show ?thesis.
    qed

    have "is_pullback (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) X X Y
        (fibered_product_right_proj X f f X) f (fibered_product_left_proj X f f X) f"
      by (simp add: f_type fibered_product_is_pullback)
    then have "right_cart_proj X X \<circ>\<^sub>c k : Z \<rightarrow> X \<Longrightarrow> left_cart_proj X X \<circ>\<^sub>c k : Z \<rightarrow> X \<Longrightarrow> f \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c k = f \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c k \<Longrightarrow>
      (\<exists>!j. j : Z \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<and>
        fibered_product_right_proj X f f X \<circ>\<^sub>c j = right_cart_proj X X \<circ>\<^sub>c k
        \<and> fibered_product_left_proj X f f X \<circ>\<^sub>c j = left_cart_proj X X \<circ>\<^sub>c k)"
      unfolding is_pullback_def by auto
    then obtain z where z_type[type_rule]: "z : Z \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X"
        and k_right_eq: "fibered_product_right_proj X f f X \<circ>\<^sub>c z = right_cart_proj X X \<circ>\<^sub>c k" 
        and k_left_eq: "fibered_product_left_proj X f f X \<circ>\<^sub>c z = left_cart_proj X X \<circ>\<^sub>c k"
        and z_unique: "\<And>j. j : Z \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X 
          \<and> fibered_product_right_proj X f f X \<circ>\<^sub>c j = right_cart_proj X X \<circ>\<^sub>c k
          \<and> fibered_product_left_proj X f f X \<circ>\<^sub>c j = left_cart_proj X X \<circ>\<^sub>c k \<Longrightarrow> z = j"
      using left_k_right_k_eq by (typecheck_cfuncs, auto)

    have k_eq: "fibered_product_morphism X f f X \<circ>\<^sub>c z = k"
      using k_right_eq k_left_eq
      unfolding fibered_product_right_proj_def fibered_product_left_proj_def
      by (typecheck_cfuncs_prems, smt cfunc_prod_comp cfunc_prod_unique)

    then show "\<exists>l. l : Z \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<and> fibered_product_morphism X f f X \<circ>\<^sub>c l = k \<and> b \<circ>\<^sub>c l = j"
    proof (intro exI[where x=z], clarify)
      assume k_def: "k = fibered_product_morphism X f f X \<circ>\<^sub>c z"
      have "fibered_product_morphism E h h E \<circ>\<^sub>c j = (g \<times>\<^sub>f g) \<circ>\<^sub>c k"
        by (simp add: k_h_eq)
      also have "... = (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X \<circ>\<^sub>c z"
        by (simp add: k_eq)
      also have "... = fibered_product_morphism E h h E \<circ>\<^sub>c b \<circ>\<^sub>c z"
        by (typecheck_cfuncs, simp add: b_eq comp_associative2)
      then show "z : Z \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<and> fibered_product_morphism X f f X \<circ>\<^sub>c z = fibered_product_morphism X f f X \<circ>\<^sub>c z \<and> b \<circ>\<^sub>c z = j"
        by (typecheck_cfuncs, metis assms(6) fibered_product_morphism_monomorphism fibered_product_morphism_type k_def k_h_eq monomorphism_def3)
    qed

    show "\<And> j y. j : Z \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<Longrightarrow> y : Z \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<Longrightarrow>
        fibered_product_morphism X f f X \<circ>\<^sub>c y = fibered_product_morphism X f f X \<circ>\<^sub>c j \<Longrightarrow>
        j = y"
      using fibered_product_morphism_monomorphism monomorphism_def2 by (typecheck_cfuncs_prems, metis)
  qed
  then have b_epi: "epimorphism b"
    using g_epi g_type cfunc_cross_prod_type cfunc_cross_prod_surj  pullback_of_epi_is_epi1 h_type
    by (meson epi_is_surj surjective_is_epimorphism)

  have existence: "\<exists>b. b : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E \<and>
        fibered_product_left_proj E h h E \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_left_proj X f f X \<and>
        fibered_product_right_proj E h h E \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_right_proj X f f X \<and>
        epimorphism b"
  proof (intro exI[where x=b], safe)
    show "b : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E"
      by typecheck_cfuncs
    show "fibered_product_left_proj E h h E \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_left_proj X f f X"
    proof -
      have "fibered_product_left_proj E h h E \<circ>\<^sub>c b
          = left_cart_proj E E \<circ>\<^sub>c fibered_product_morphism E h h E \<circ>\<^sub>c b"
        unfolding fibered_product_left_proj_def by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = left_cart_proj E E \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X"
        by (simp add: b_eq)
      also have "... = g \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c fibered_product_morphism X f f X"
        by (typecheck_cfuncs, simp add: comp_associative2 left_cart_proj_cfunc_cross_prod)
      also have "... = g \<circ>\<^sub>c fibered_product_left_proj X f f X"
        unfolding fibered_product_left_proj_def by (typecheck_cfuncs)
      finally show ?thesis.
    qed
    show "fibered_product_right_proj E h h E \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_right_proj X f f X"
    proof -
      have "fibered_product_right_proj E h h E \<circ>\<^sub>c b
          = right_cart_proj E E \<circ>\<^sub>c fibered_product_morphism E h h E \<circ>\<^sub>c b"
        unfolding fibered_product_right_proj_def by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = right_cart_proj E E \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X"
        by (simp add: b_eq)
      also have "... = g \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c fibered_product_morphism X f f X"
        by (typecheck_cfuncs, simp add: comp_associative2 right_cart_proj_cfunc_cross_prod)
      also have "... = g \<circ>\<^sub>c fibered_product_right_proj X f f X"
        unfolding fibered_product_right_proj_def by (typecheck_cfuncs)
      finally show ?thesis.
    qed
    show "epimorphism b"
      by (simp add: b_epi)
  qed  
  show "\<exists>!b. b : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E \<and>
         fibered_product_left_proj E h h E \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_left_proj X f f X \<and>
         fibered_product_right_proj E h h E \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_right_proj X f f X \<and>
         epimorphism b"
    by (typecheck_cfuncs, metis epimorphism_def2 existence g_eq iso_imp_epi_and_monic kern_pair_proj_iso_TFAE2 monomorphism_def3)
qed

section \<open>Set Subtraction\<close>

definition set_subtraction :: "cset \<Rightarrow> cset \<times> cfunc \<Rightarrow> cset" (infix "\<setminus>" 60) where
  "Y \<setminus> X = (SOME E. \<exists> m'.  equalizer E m' (characteristic_func (snd X)) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>))"

lemma set_subtraction_equalizer:
  assumes "m : X \<rightarrow> Y" "monomorphism m"
  shows "\<exists> m'.  equalizer (Y \<setminus> (X,m)) m' (characteristic_func m) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)"
proof -
  have "\<exists> E m'. equalizer E m' (characteristic_func m) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)"
    using assms equalizer_exists by (typecheck_cfuncs, auto)
  then have "\<exists> m'.  equalizer (Y \<setminus> (X,m)) m' (characteristic_func (snd (X,m))) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)"
    unfolding set_subtraction_def by (subst someI_ex, auto)
  then show "\<exists> m'.  equalizer (Y \<setminus> (X,m)) m' (characteristic_func m) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)"
    by auto
qed

definition complement_morphism :: "cfunc \<Rightarrow> cfunc" ("_\<^sup>c" [1000]) where
  "m\<^sup>c = (SOME m'.  equalizer (codomain m \<setminus> (domain m, m)) m' (characteristic_func m) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>codomain m\<^esub>))"

lemma complement_morphism_equalizer:
  assumes "m : X \<rightarrow> Y" "monomorphism m"
  shows "equalizer (Y \<setminus> (X,m)) m\<^sup>c (characteristic_func m) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)"
proof -
  have "\<exists> m'. equalizer (codomain m \<setminus> (domain m, m)) m' (characteristic_func m) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>codomain m\<^esub>)"
    by (simp add: assms cfunc_type_def set_subtraction_equalizer)
  then have "equalizer (codomain m \<setminus> (domain m, m)) m\<^sup>c (characteristic_func m) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>codomain m\<^esub>)"
    unfolding complement_morphism_def by (subst someI_ex, auto)
  then show "equalizer (Y \<setminus> (X, m)) m\<^sup>c (characteristic_func m) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)"
    using assms unfolding cfunc_type_def by auto
qed

lemma complement_morphism_type[type_rule]:
  assumes "m : X \<rightarrow> Y" "monomorphism m"
  shows "m\<^sup>c : Y \<setminus> (X,m) \<rightarrow> Y"
  using assms cfunc_type_def characteristic_func_type complement_morphism_equalizer equalizer_def by auto

lemma complement_morphism_mono:
  assumes "m : X \<rightarrow> Y" "monomorphism m"
  shows "monomorphism m\<^sup>c"
  using assms complement_morphism_equalizer equalizer_is_monomorphism by blast

lemma complement_morphism_eq:
  assumes "m : X \<rightarrow> Y" "monomorphism m"
  shows "characteristic_func m \<circ>\<^sub>c m\<^sup>c  = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c m\<^sup>c"
  using assms complement_morphism_equalizer unfolding equalizer_def by auto

lemma characteristic_func_true_not_complement_member:
  assumes "m : B \<rightarrow> X" "monomorphism m" "x \<in>\<^sub>c X"
  assumes characteristic_func_true: "characteristic_func m \<circ>\<^sub>c x = \<t>"
  shows "\<not> x \<in>\<^bsub>X\<^esub> (X \<setminus> (B, m),m\<^sup>c)"
proof
  assume in_complement: "x \<in>\<^bsub>X\<^esub> (X \<setminus> (B, m), m\<^sup>c)"
  then obtain x' where x'_type: "x' \<in>\<^sub>c X \<setminus> (B,m)" and x'_def: "m\<^sup>c \<circ>\<^sub>c x' = x"
    using assms cfunc_type_def complement_morphism_type factors_through_def relative_member_def2
    by auto
  then have "characteristic_func m \<circ>\<^sub>c m\<^sup>c = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c m\<^sup>c"
    using assms complement_morphism_equalizer equalizer_def by blast
  then have "characteristic_func m \<circ>\<^sub>c x = \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x"
    using assms x'_type complement_morphism_type
    by (typecheck_cfuncs, smt x'_def assms cfunc_type_def comp_associative domain_comp)
  then have "characteristic_func m \<circ>\<^sub>c x = \<f>"
    using assms by (typecheck_cfuncs, metis id_right_unit2 id_type one_unique_element terminal_func_comp terminal_func_type)
  then show False
    using characteristic_func_true true_false_distinct by auto
qed

lemma characteristic_func_false_complement_member:
  assumes "m : B \<rightarrow> X" "monomorphism m" "x \<in>\<^sub>c X"
  assumes characteristic_func_false: "characteristic_func m \<circ>\<^sub>c x = \<f>"
  shows "x \<in>\<^bsub>X\<^esub> (X \<setminus> (B, m),m\<^sup>c)"
proof -
  have x_equalizes: "characteristic_func m \<circ>\<^sub>c x = \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x"
    by (metis assms(3) characteristic_func_false false_func_type id_right_unit2 id_type one_unique_element terminal_func_comp terminal_func_type)
  have "\<And>h F. h : F \<rightarrow> X \<and> characteristic_func m \<circ>\<^sub>c h = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c h \<longrightarrow>
                  (\<exists>!k. k : F \<rightarrow> X \<setminus> (B, m) \<and> m\<^sup>c \<circ>\<^sub>c k = h)"
    using assms complement_morphism_equalizer unfolding equalizer_def
    by (smt cfunc_type_def characteristic_func_type) 
  then obtain x' where x'_type: "x' \<in>\<^sub>c X \<setminus> (B, m)" and x'_def: "m\<^sup>c \<circ>\<^sub>c x' = x"
    by (metis assms(3) cfunc_type_def comp_associative false_func_type terminal_func_type x_equalizes)
  then show "x \<in>\<^bsub>X\<^esub> (X \<setminus> (B, m),m\<^sup>c)"
    unfolding relative_member_def factors_through_def
    using assms complement_morphism_mono complement_morphism_type cfunc_type_def by auto
qed

lemma in_complement_not_in_subset:
  assumes "m : X \<rightarrow> Y" "monomorphism m" "x \<in>\<^sub>c Y"
  assumes "x \<in>\<^bsub>Y\<^esub> (Y \<setminus> (X,m), m\<^sup>c)"
  shows "\<not> x \<in>\<^bsub>Y\<^esub> (X, m)"
  using assms characteristic_func_false_not_relative_member
    characteristic_func_true_not_complement_member characteristic_func_type comp_type
    true_false_only_truth_values by blast

lemma not_in_subset_in_complement:
  assumes "m : X \<rightarrow> Y" "monomorphism m" "x \<in>\<^sub>c Y"
  assumes "\<not> x \<in>\<^bsub>Y\<^esub> (X, m)"
  shows "x \<in>\<^bsub>Y\<^esub> (Y \<setminus> (X,m), m\<^sup>c)"
  using assms characteristic_func_false_complement_member characteristic_func_true_relative_member
    characteristic_func_type comp_type true_false_only_truth_values by blast

lemma complement_disjoint:
  assumes "m : X \<rightarrow> Y" "monomorphism m"
  assumes "x \<in>\<^sub>c X" "x' \<in>\<^sub>c Y \<setminus> (X,m)"
  shows "m \<circ>\<^sub>c x \<noteq> m\<^sup>c \<circ>\<^sub>c x'"
proof 
  assume "m \<circ>\<^sub>c x = m\<^sup>c \<circ>\<^sub>c x'"
  then have "characteristic_func m \<circ>\<^sub>c m \<circ>\<^sub>c x = characteristic_func m \<circ>\<^sub>c m\<^sup>c \<circ>\<^sub>c x'"
    by auto
  then have "(characteristic_func m \<circ>\<^sub>c m) \<circ>\<^sub>c x = (characteristic_func m \<circ>\<^sub>c m\<^sup>c) \<circ>\<^sub>c x'"
    using assms comp_associative2 by (typecheck_cfuncs, auto)
  then have "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x = ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c m\<^sup>c) \<circ>\<^sub>c x'"
    using assms characteristic_func_eq complement_morphism_eq by auto
  then have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x = \<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c m\<^sup>c \<circ>\<^sub>c x'"
    using assms comp_associative2 by (typecheck_cfuncs, smt terminal_func_comp terminal_func_type)
  then have "\<t> \<circ>\<^sub>c id \<one> = \<f> \<circ>\<^sub>c id \<one>"
    using assms by (smt cfunc_type_def comp_associative complement_morphism_type id_type one_unique_element terminal_func_comp terminal_func_type)
  then have "\<t> = \<f>"
    using false_func_type id_right_unit2 true_func_type by auto
  then show False
    using true_false_distinct by auto
qed

lemma set_subtraction_right_iso:
  assumes m_type[type_rule]: "m : A \<rightarrow> C" and m_mono[type_rule]: "monomorphism m"
  assumes i_type[type_rule]: "i : B \<rightarrow> A" and i_iso: "isomorphism i"
  shows "C \<setminus> (A,m) = C \<setminus> (B, m \<circ>\<^sub>c i)"
proof -
  have mi_mono[type_rule]: "monomorphism (m \<circ>\<^sub>c i)"
    using cfunc_type_def composition_of_monic_pair_is_monic i_iso i_type iso_imp_epi_and_monic m_mono m_type by presburger
  obtain \<chi>m where \<chi>m_type[type_rule]: "\<chi>m : C \<rightarrow> \<Omega>" and \<chi>m_def: "\<chi>m = characteristic_func m"
    using characteristic_func_type m_mono m_type by blast
  obtain \<chi>mi where \<chi>mi_type[type_rule]: "\<chi>mi : C \<rightarrow> \<Omega>" and \<chi>mi_def: "\<chi>mi = characteristic_func (m \<circ>\<^sub>c i)"
    by (typecheck_cfuncs, simp)
  have "\<And> c. c \<in>\<^sub>c C \<Longrightarrow> (\<chi>m \<circ>\<^sub>c c = \<t>) = (\<chi>mi \<circ>\<^sub>c c = \<t>)"
  proof -
    fix c
    assume c_type[type_rule]: "c \<in>\<^sub>c C"
    have "(\<chi>m \<circ>\<^sub>c c = \<t>) = (c \<in>\<^bsub>C\<^esub> (A,m))"
      by (typecheck_cfuncs, metis \<chi>m_def m_mono not_rel_mem_char_func_false rel_mem_char_func_true true_false_distinct)
    also have "... = (\<exists> a. a \<in>\<^sub>c A \<and> c = m \<circ>\<^sub>c a)"
      using cfunc_type_def factors_through_def m_mono relative_member_def2 by (typecheck_cfuncs, auto)
    also have "... = (\<exists> b. b \<in>\<^sub>c B \<and> c = m \<circ>\<^sub>c i \<circ>\<^sub>c b)"
      by (typecheck_cfuncs, smt (z3) cfunc_type_def comp_type epi_is_surj i_iso iso_imp_epi_and_monic surjective_def)
    also have "... = (c \<in>\<^bsub>C\<^esub> (B,m \<circ>\<^sub>c i))"
      using cfunc_type_def comp_associative2 composition_of_monic_pair_is_monic factors_through_def2 i_iso iso_imp_epi_and_monic m_mono relative_member_def2
      by (typecheck_cfuncs, auto)
    also have "... = (\<chi>mi \<circ>\<^sub>c c = \<t>)"
      by (typecheck_cfuncs, metis \<chi>mi_def mi_mono not_rel_mem_char_func_false rel_mem_char_func_true true_false_distinct)
    finally show "(\<chi>m \<circ>\<^sub>c c = \<t>) = (\<chi>mi \<circ>\<^sub>c c = \<t>)".
  qed
  then have "\<chi>m = \<chi>mi"
    by (typecheck_cfuncs, smt (verit, best) comp_type one_separator true_false_only_truth_values) 
  then show "C \<setminus> (A,m) = C \<setminus> (B, m \<circ>\<^sub>c i)"
    using \<chi>m_def \<chi>mi_def isomorphic_is_reflexive set_subtraction_def by auto
qed

lemma set_subtraction_left_iso:
  assumes m_type[type_rule]: "m : C \<rightarrow> A" and m_mono[type_rule]: "monomorphism m"
  assumes i_type[type_rule]: "i : A \<rightarrow> B" and i_iso: "isomorphism i"
  shows "A \<setminus> (C,m) \<cong> B \<setminus> (C, i \<circ>\<^sub>c m)"
proof -
  have im_mono[type_rule]: "monomorphism (i \<circ>\<^sub>c m)"
    using cfunc_type_def composition_of_monic_pair_is_monic i_iso i_type iso_imp_epi_and_monic m_mono m_type by presburger
  obtain \<chi>m where \<chi>m_type[type_rule]: "\<chi>m : A \<rightarrow> \<Omega>" and \<chi>m_def: "\<chi>m = characteristic_func m"
    using characteristic_func_type m_mono m_type by blast
  obtain \<chi>im where \<chi>im_type[type_rule]: "\<chi>im : B \<rightarrow> \<Omega>" and \<chi>im_def: "\<chi>im = characteristic_func (i \<circ>\<^sub>c m)"
    by (typecheck_cfuncs, simp)
  have \<chi>im_pullback: "is_pullback C \<one> B \<Omega> (\<beta>\<^bsub>C\<^esub>) \<t> (i \<circ>\<^sub>c m) \<chi>im"
    using \<chi>im_def characteristic_func_is_pullback comp_type i_type im_mono m_type by blast
  have "is_pullback C \<one> A \<Omega> (\<beta>\<^bsub>C\<^esub>) \<t> m (\<chi>im \<circ>\<^sub>c i)"
    unfolding is_pullback_def
  proof (typecheck_cfuncs, safe)
    show "\<t> \<circ>\<^sub>c \<beta>\<^bsub>C\<^esub> = (\<chi>im \<circ>\<^sub>c i) \<circ>\<^sub>c m"
      by (typecheck_cfuncs, etcs_assocr, metis \<chi>im_def characteristic_func_eq comp_type im_mono)
  next
    fix Z k h
    assume k_type[type_rule]: "k : Z \<rightarrow> \<one>" and h_type[type_rule]: "h : Z \<rightarrow> A"
    assume eq: "\<t> \<circ>\<^sub>c k = (\<chi>im \<circ>\<^sub>c i) \<circ>\<^sub>c h"
    then obtain j where j_type[type_rule]: "j : Z \<rightarrow> C" and j_def: "i \<circ>\<^sub>c h = (i \<circ>\<^sub>c m) \<circ>\<^sub>c j"
      using \<chi>im_pullback unfolding is_pullback_def by (typecheck_cfuncs, smt (verit, ccfv_threshold) comp_associative2 k_type)
    then show "\<exists>j. j : Z \<rightarrow> C \<and> \<beta>\<^bsub>C\<^esub> \<circ>\<^sub>c j = k \<and> m \<circ>\<^sub>c j = h"
      by (intro exI[where x=j], typecheck_cfuncs, smt comp_associative2 i_iso iso_imp_epi_and_monic monomorphism_def2 terminal_func_unique)
  next
    fix Z j y
    assume j_type[type_rule]: "j : Z \<rightarrow> C" and y_type[type_rule]: "y : Z \<rightarrow> C"
    assume "\<t> \<circ>\<^sub>c \<beta>\<^bsub>C\<^esub> \<circ>\<^sub>c j = (\<chi>im \<circ>\<^sub>c i) \<circ>\<^sub>c m \<circ>\<^sub>c j" "\<beta>\<^bsub>C\<^esub> \<circ>\<^sub>c y = \<beta>\<^bsub>C\<^esub> \<circ>\<^sub>c j" "m \<circ>\<^sub>c y = m \<circ>\<^sub>c j"
    then show "j = y"
      using m_mono monomorphism_def2 by (typecheck_cfuncs_prems, blast)
  qed
  then have \<chi>im_i_eq_\<chi>m: "\<chi>im \<circ>\<^sub>c i = \<chi>m"
    using \<chi>m_def characteristic_func_is_pullback characteristic_function_exists m_mono m_type by blast
  then have "\<chi>im \<circ>\<^sub>c (i \<circ>\<^sub>c m\<^sup>c) = \<f> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub> \<circ>\<^sub>c (i \<circ>\<^sub>c m\<^sup>c)"
    by (etcs_assocl, typecheck_cfuncs, smt (verit, best) \<chi>m_def comp_associative2 complement_morphism_eq m_mono terminal_func_comp)
  then obtain i' where i'_type[type_rule]: "i' : A \<setminus> (C, m) \<rightarrow> B \<setminus> (C, i \<circ>\<^sub>c m)" and i'_def: "i \<circ>\<^sub>c m\<^sup>c = (i \<circ>\<^sub>c m)\<^sup>c \<circ>\<^sub>c i'"
    using complement_morphism_equalizer unfolding equalizer_def
    by (-, typecheck_cfuncs, smt \<chi>im_def cfunc_type_def comp_associative2 im_mono)

  have "\<chi>m \<circ>\<^sub>c (i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c) = \<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub> \<circ>\<^sub>c (i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c)"
  proof -
    have "\<chi>m \<circ>\<^sub>c (i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c) = \<chi>im \<circ>\<^sub>c (i \<circ>\<^sub>c i\<^bold>\<inverse>) \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c"
      by (typecheck_cfuncs, simp add: \<chi>im_i_eq_\<chi>m cfunc_type_def comp_associative i_iso)
    also have "... = \<chi>im \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c"
      using i_iso id_left_unit2 inv_right by (typecheck_cfuncs, auto)
    also have "... = \<f> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c"
      by (typecheck_cfuncs, simp add: \<chi>im_def comp_associative2 complement_morphism_eq im_mono)
    also have "... = \<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub> \<circ>\<^sub>c (i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c)"
      by (typecheck_cfuncs, metis i_iso terminal_func_unique)
    finally show ?thesis.
  qed
  then obtain i'_inv where i'_inv_type[type_rule]: "i'_inv : B \<setminus> (C, i \<circ>\<^sub>c m) \<rightarrow> A \<setminus> (C, m)"
    and i'_inv_def: "(i \<circ>\<^sub>c m)\<^sup>c = (i \<circ>\<^sub>c m\<^sup>c) \<circ>\<^sub>c i'_inv"
    using complement_morphism_equalizer[where m="m", where X=C, where Y=A] unfolding equalizer_def
    by (-, typecheck_cfuncs, smt (z3) \<chi>m_def cfunc_type_def comp_associative2 i_iso id_left_unit2 inv_right m_mono)

  have "isomorphism i'"
  proof (etcs_subst isomorphism_def3, intro exI[where x = "i'_inv"], safe)
    show "i'_inv : B \<setminus> (C, i \<circ>\<^sub>c m) \<rightarrow> A \<setminus> (C, m)"
      by typecheck_cfuncs
    have "i \<circ>\<^sub>c m\<^sup>c = (i \<circ>\<^sub>c m\<^sup>c) \<circ>\<^sub>c i'_inv \<circ>\<^sub>c i'"
      using i'_inv_def by (etcs_subst i'_def, etcs_assocl, auto)
    then show "i'_inv \<circ>\<^sub>c i' = id\<^sub>c (A \<setminus> (C, m))"
      by (typecheck_cfuncs_prems, smt (verit, best) cfunc_type_def complement_morphism_mono composition_of_monic_pair_is_monic i_iso id_right_unit2 id_type iso_imp_epi_and_monic m_mono monomorphism_def3)
  next
    have "(i \<circ>\<^sub>c m)\<^sup>c = (i \<circ>\<^sub>c m)\<^sup>c \<circ>\<^sub>c i' \<circ>\<^sub>c i'_inv"
      using i'_def by (etcs_subst i'_inv_def, etcs_assocl, auto)
    then show "i' \<circ>\<^sub>c i'_inv = id\<^sub>c (B \<setminus> (C, i \<circ>\<^sub>c m))"
      by (typecheck_cfuncs_prems, metis complement_morphism_mono id_right_unit2 id_type im_mono monomorphism_def3)
  qed
  then show "A \<setminus> (C, m) \<cong> B \<setminus> (C, i \<circ>\<^sub>c m)"
    using i'_type is_isomorphic_def by blast
qed

section  \<open>Graphs\<close>

definition functional_on :: "cset \<Rightarrow> cset \<Rightarrow> cset \<times> cfunc \<Rightarrow> bool" where
  "functional_on X Y R = (R  \<subseteq>\<^sub>c X \<times>\<^sub>c Y \<and>
    (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> (\<exists>! y.  y \<in>\<^sub>c Y \<and>  
      \<langle>x,y\<rangle> \<in>\<^bsub>X\<times>\<^sub>cY\<^esub> R)))" 

text \<open>The definition below corresponds to Definition 2.3.12 in Halvorson.\<close>
definition graph :: "cfunc \<Rightarrow> cset" where
 "graph f = (SOME E. \<exists> m. equalizer E m (f \<circ>\<^sub>c left_cart_proj (domain f) (codomain f)) (right_cart_proj (domain f) (codomain f)))"

lemma graph_equalizer:
  "\<exists> m. equalizer (graph f) m (f \<circ>\<^sub>c left_cart_proj (domain f) (codomain f)) (right_cart_proj (domain f) (codomain f))"
  unfolding graph_def
  by (typecheck_cfuncs, rule someI_ex, simp add: cfunc_type_def equalizer_exists)
  
lemma graph_equalizer2:
  assumes "f : X \<rightarrow> Y"
  shows "\<exists> m. equalizer (graph f) m (f \<circ>\<^sub>c left_cart_proj X Y) (right_cart_proj X Y)"
  using assms by (typecheck_cfuncs, metis cfunc_type_def graph_equalizer)

definition graph_morph :: "cfunc \<Rightarrow> cfunc" where
 "graph_morph f = (SOME m. equalizer (graph f) m (f \<circ>\<^sub>c left_cart_proj (domain f) (codomain f)) (right_cart_proj (domain f) (codomain f)))"

lemma graph_equalizer3:
  "equalizer (graph f) (graph_morph f) (f \<circ>\<^sub>c left_cart_proj (domain f) (codomain f)) (right_cart_proj (domain f) (codomain f))"
  unfolding graph_morph_def by (rule someI_ex, simp add: graph_equalizer)

lemma graph_equalizer4:
  assumes "f : X \<rightarrow> Y"
  shows "equalizer (graph f) (graph_morph f) (f \<circ>\<^sub>c left_cart_proj X Y) (right_cart_proj X Y)"
  using assms cfunc_type_def graph_equalizer3 by auto

lemma graph_subobject:
  assumes "f : X \<rightarrow> Y"
  shows "(graph f, graph_morph f) \<subseteq>\<^sub>c (X \<times>\<^sub>c Y)"
  by (metis assms cfunc_type_def equalizer_def equalizer_is_monomorphism graph_equalizer3 right_cart_proj_type subobject_of_def2)

lemma graph_morph_type[type_rule]:
  assumes "f : X \<rightarrow> Y"
  shows "graph_morph(f) : graph f \<rightarrow> X \<times>\<^sub>c Y"
  using graph_subobject subobject_of_def2 assms by auto

text \<open>The lemma below corresponds to Exercise 2.3.13 in Halvorson.\<close>
lemma graphs_are_functional:
  assumes "f : X \<rightarrow> Y"
  shows "functional_on X Y (graph f, graph_morph f)"
  unfolding functional_on_def
proof(safe)
  show graph_subobj: "(graph f, graph_morph f)  \<subseteq>\<^sub>c (X\<times>\<^sub>c Y)"
    by (simp add: assms graph_subobject)
  show "\<And>x. x \<in>\<^sub>c X \<Longrightarrow> \<exists>y. y \<in>\<^sub>c Y \<and> \<langle>x,y\<rangle> \<in>\<^bsub>X \<times>\<^sub>c Y\<^esub> (graph f, graph_morph f)"
  proof - 
    fix x 
    assume x_type[type_rule]: "x \<in>\<^sub>c X"
    obtain y where y_def: "y = f \<circ>\<^sub>c x"
      by simp
    then have y_type[type_rule]: "y \<in>\<^sub>c Y"
      using assms comp_type x_type y_def by blast

    have "\<langle>x,y\<rangle> \<in>\<^bsub>X \<times>\<^sub>c Y\<^esub> (graph f, graph_morph f)"
      unfolding relative_member_def
    proof(typecheck_cfuncs, safe)
      show "monomorphism (snd (graph f, graph_morph f))"
        using graph_subobj subobject_of_def by auto
      show " snd (graph f, graph_morph f) : fst (graph f, graph_morph f) \<rightarrow> X \<times>\<^sub>c Y"
        by (simp add: assms graph_morph_type)
      have "\<langle>x,y\<rangle> factorsthru graph_morph f"
      proof(subst xfactorthru_equalizer_iff_fx_eq_gx[where E = "graph f", where m = "graph_morph f",  
                                                     where f = "(f \<circ>\<^sub>c left_cart_proj X Y)", where g = "right_cart_proj X Y", where X = "X \<times>\<^sub>c Y", where Y = Y,
                                                     where x ="\<langle>x,y\<rangle>"])
        show "f \<circ>\<^sub>c left_cart_proj X Y : X \<times>\<^sub>c Y \<rightarrow> Y"
          using assms by typecheck_cfuncs
        show "right_cart_proj X Y : X \<times>\<^sub>c Y \<rightarrow> Y"
          by  typecheck_cfuncs
        show "equalizer (graph f) (graph_morph f) (f \<circ>\<^sub>c left_cart_proj X Y) (right_cart_proj X Y)"
          by (simp add: assms graph_equalizer4)
        show "\<langle>x,y\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Y"
          by typecheck_cfuncs
        show "(f \<circ>\<^sub>c left_cart_proj X Y) \<circ>\<^sub>c \<langle>x,y\<rangle> = right_cart_proj X Y \<circ>\<^sub>c \<langle>x,y\<rangle>"
          using assms  
          by (typecheck_cfuncs, smt (z3) comp_associative2 left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod y_def)
      qed
      then show "\<langle>x,y\<rangle> factorsthru snd (graph f, graph_morph f)"
        by simp
    qed
    then show "\<exists>y. y \<in>\<^sub>c Y \<and> \<langle>x,y\<rangle> \<in>\<^bsub>X \<times>\<^sub>c Y\<^esub> (graph f, graph_morph f)"
      using y_type by blast
  qed
  show "\<And>x y ya.
       x \<in>\<^sub>c X \<Longrightarrow>
       y \<in>\<^sub>c Y \<Longrightarrow>
       \<langle>x,y\<rangle> \<in>\<^bsub>X \<times>\<^sub>c Y\<^esub> (graph f, graph_morph f) \<Longrightarrow> 
        ya \<in>\<^sub>c Y \<Longrightarrow> 
        \<langle>x,ya\<rangle> \<in>\<^bsub>X \<times>\<^sub>c Y\<^esub> (graph f, graph_morph f)
         \<Longrightarrow> y = ya"
    using assms  
    by (smt (z3) comp_associative2 equalizer_def factors_through_def2 graph_equalizer4 left_cart_proj_cfunc_prod left_cart_proj_type relative_member_def2 right_cart_proj_cfunc_prod)
qed

lemma functional_on_isomorphism:
  assumes "functional_on X Y (R,m)"
  shows "isomorphism(left_cart_proj X Y \<circ>\<^sub>c m)"
proof-
  have m_mono: "monomorphism(m)"
    using assms functional_on_def subobject_of_def2 by blast
  have pi0_m_type[type_rule]: "left_cart_proj X Y \<circ>\<^sub>c m : R \<rightarrow> X"
    using assms functional_on_def subobject_of_def2 by (typecheck_cfuncs, blast)
  have surj: "surjective(left_cart_proj X Y \<circ>\<^sub>c m)"
    unfolding surjective_def
  proof(clarify)
    fix x 
    assume "x \<in>\<^sub>c codomain (left_cart_proj X Y \<circ>\<^sub>c m)"
    then have [type_rule]: "x \<in>\<^sub>c X"
      using cfunc_type_def pi0_m_type by force
    then have "\<exists>! y. (y \<in>\<^sub>c Y \<and>  \<langle>x,y\<rangle> \<in>\<^bsub>X\<times>\<^sub>cY\<^esub> (R,m))"
      using assms functional_on_def  by force
    then show "\<exists>z. z \<in>\<^sub>c domain (left_cart_proj X Y \<circ>\<^sub>c m) \<and> (left_cart_proj X Y \<circ>\<^sub>c m) \<circ>\<^sub>c z = x"
      by (typecheck_cfuncs, smt (verit, best) cfunc_type_def comp_associative factors_through_def2 left_cart_proj_cfunc_prod relative_member_def2)
  qed
  have inj: "injective(left_cart_proj X Y \<circ>\<^sub>c m)"
  proof(unfold injective_def, clarify)
    fix r1 r2 
    assume "r1 \<in>\<^sub>c domain (left_cart_proj X Y \<circ>\<^sub>c m)" then have r1_type[type_rule]: "r1 \<in>\<^sub>c R"
      by (metis cfunc_type_def pi0_m_type)
    assume "r2 \<in>\<^sub>c domain (left_cart_proj X Y \<circ>\<^sub>c m)" then have r2_type[type_rule]: "r2 \<in>\<^sub>c R"
      by (metis cfunc_type_def pi0_m_type)
    assume "(left_cart_proj X Y \<circ>\<^sub>c m) \<circ>\<^sub>c r1 = (left_cart_proj X Y \<circ>\<^sub>c m) \<circ>\<^sub>c r2"
    then have eq: "left_cart_proj X Y \<circ>\<^sub>c m \<circ>\<^sub>c r1 = left_cart_proj X Y \<circ>\<^sub>c m \<circ>\<^sub>c r2"
      using assms cfunc_type_def comp_associative functional_on_def subobject_of_def2 by (typecheck_cfuncs, auto)
    have mx_type[type_rule]: "m \<circ>\<^sub>c r1 \<in>\<^sub>c X\<times>\<^sub>cY"
      using assms functional_on_def subobject_of_def2 by (typecheck_cfuncs, blast)
    then obtain x1 and y1 where m1r1_eqs: "m \<circ>\<^sub>c r1 = \<langle>x1, y1\<rangle> \<and> x1 \<in>\<^sub>c X \<and> y1 \<in>\<^sub>c Y"
      using cart_prod_decomp by presburger
    have my_type[type_rule]: "m \<circ>\<^sub>c r2 \<in>\<^sub>c X\<times>\<^sub>cY"
      using assms functional_on_def subobject_of_def2 by (typecheck_cfuncs, blast)
    then obtain x2 and y2 where m2r2_eqs:"m \<circ>\<^sub>c r2 = \<langle>x2, y2\<rangle> \<and> x2 \<in>\<^sub>c X \<and> y2 \<in>\<^sub>c Y"
      using cart_prod_decomp by presburger
    have x_equal: "x1 = x2"
      using eq left_cart_proj_cfunc_prod m1r1_eqs m2r2_eqs by force
    have functional: "\<exists>! y. (y \<in>\<^sub>c Y \<and>  \<langle>x1,y\<rangle> \<in>\<^bsub>X\<times>\<^sub>cY\<^esub> (R,m))"
      using assms functional_on_def m1r1_eqs by force
    then have y_equal: "y1 = y2"
      by (metis prod.sel factors_through_def2 m1r1_eqs m2r2_eqs mx_type my_type r1_type r2_type relative_member_def x_equal)
    then show "r1 = r2"
      by (metis functional cfunc_type_def m1r1_eqs m2r2_eqs monomorphism_def r1_type r2_type relative_member_def2 x_equal)
  qed
  show "isomorphism(left_cart_proj X Y \<circ>\<^sub>c m)"
    by (metis epi_mon_is_iso inj injective_imp_monomorphism surj surjective_is_epimorphism)
qed

text \<open>The lemma below corresponds to Proposition 2.3.14 in Halvorson.\<close>
lemma functional_relations_are_graphs:
  assumes "functional_on X Y (R,m)"
  shows "\<exists>! f. f : X \<rightarrow> Y \<and> 
    (\<exists> i. i : R \<rightarrow> graph(f) \<and> isomorphism(i) \<and> m = graph_morph(f) \<circ>\<^sub>c i)"
proof safe
  have m_type[type_rule]: "m : R \<rightarrow> X \<times>\<^sub>c Y"
    using assms unfolding functional_on_def subobject_of_def2 by auto
  have m_mono[type_rule]: "monomorphism(m)"
    using assms functional_on_def subobject_of_def2 by blast
  have isomorphism[type_rule]: "isomorphism(left_cart_proj X Y \<circ>\<^sub>c m)"
    using assms functional_on_isomorphism by force
  
  obtain h where h_type[type_rule]: "h: X \<rightarrow> R" and h_def: "h = (left_cart_proj X Y \<circ>\<^sub>c m)\<^bold>\<inverse>"
    by (typecheck_cfuncs, simp)
  obtain f where f_def: "f = (right_cart_proj X Y) \<circ>\<^sub>c m \<circ>\<^sub>c h"
    by auto
  then have f_type[type_rule]: "f : X \<rightarrow> Y"
    by (metis assms comp_type f_def functional_on_def h_type right_cart_proj_type subobject_of_def2)

  have eq: "f \<circ>\<^sub>c left_cart_proj X Y \<circ>\<^sub>c m = right_cart_proj X Y \<circ>\<^sub>c m"
    unfolding f_def h_def by (typecheck_cfuncs, smt comp_associative2 id_right_unit2 inv_left isomorphism)

  show "\<exists>f. f : X \<rightarrow> Y \<and> (\<exists>i. i : R \<rightarrow> graph f \<and> isomorphism i \<and> m = graph_morph f \<circ>\<^sub>c i)"
  proof (intro exI[where x=f], safe, typecheck_cfuncs)
    have graph_equalizer: "equalizer (graph f) (graph_morph f) (f \<circ>\<^sub>c left_cart_proj X Y) (right_cart_proj X Y)"
      by (simp add: f_type graph_equalizer4)
    then have "\<forall>h F. h : F \<rightarrow> X \<times>\<^sub>c Y \<and> (f \<circ>\<^sub>c left_cart_proj X Y) \<circ>\<^sub>c h = right_cart_proj X Y \<circ>\<^sub>c h \<longrightarrow>
          (\<exists>!k. k : F \<rightarrow> graph f \<and> graph_morph f \<circ>\<^sub>c k = h)"
      unfolding equalizer_def using cfunc_type_def by (typecheck_cfuncs, auto)
    then obtain i where i_type[type_rule]: "i : R \<rightarrow> graph f" and i_eq: "graph_morph f \<circ>\<^sub>c i = m"
      by (typecheck_cfuncs, smt comp_associative2 eq left_cart_proj_type)
    have "surjective i"
    proof (etcs_subst surjective_def2, clarify)
      fix y'
      assume y'_type[type_rule]: "y' \<in>\<^sub>c graph f"

      define x where "x = left_cart_proj X Y \<circ>\<^sub>c graph_morph(f) \<circ>\<^sub>c y'"
      then have x_type[type_rule]: "x \<in>\<^sub>c X"
        unfolding x_def by typecheck_cfuncs

      obtain y where y_type[type_rule]: "y \<in>\<^sub>c Y" and x_y_in_R: "\<langle>x,y\<rangle> \<in>\<^bsub>X \<times>\<^sub>c Y\<^esub> (R, m)"
        and y_unique: "\<forall> z. (z \<in>\<^sub>c Y \<and> \<langle>x,z\<rangle> \<in>\<^bsub>X \<times>\<^sub>c Y\<^esub> (R, m)) \<longrightarrow> z = y"
        by (metis assms functional_on_def x_type)

      obtain x' where x'_type[type_rule]: "x' \<in>\<^sub>c R" and x'_eq: "m \<circ>\<^sub>c x' = \<langle>x, y\<rangle>"
        using x_y_in_R unfolding relative_member_def2 by (-, etcs_subst_asm factors_through_def2, auto)

      have "graph_morph(f) \<circ>\<^sub>c i \<circ>\<^sub>c x' = graph_morph(f) \<circ>\<^sub>c y'"
      proof (typecheck_cfuncs, rule cart_prod_eqI, safe)
        show left: "left_cart_proj X Y \<circ>\<^sub>c graph_morph f \<circ>\<^sub>c i \<circ>\<^sub>c x' = left_cart_proj X Y \<circ>\<^sub>c graph_morph f \<circ>\<^sub>c y'"
        proof -
          have "left_cart_proj X Y \<circ>\<^sub>c graph_morph(f) \<circ>\<^sub>c i \<circ>\<^sub>c x' = left_cart_proj X Y \<circ>\<^sub>c m \<circ>\<^sub>c x'"
            by (typecheck_cfuncs, smt comp_associative2 i_eq)
          also have "... = x"
            unfolding x'_eq using left_cart_proj_cfunc_prod by (typecheck_cfuncs, blast)
          also have "... = left_cart_proj X Y \<circ>\<^sub>c graph_morph f \<circ>\<^sub>c y'"
            unfolding x_def by auto
          finally show ?thesis.
        qed

        show "right_cart_proj X Y \<circ>\<^sub>c graph_morph f \<circ>\<^sub>c i \<circ>\<^sub>c x' = right_cart_proj X Y \<circ>\<^sub>c graph_morph f \<circ>\<^sub>c y'"
        proof -
          have "right_cart_proj X Y \<circ>\<^sub>c graph_morph f \<circ>\<^sub>c i \<circ>\<^sub>c x' = f \<circ>\<^sub>c left_cart_proj X Y \<circ>\<^sub>c graph_morph f \<circ>\<^sub>c i \<circ>\<^sub>c x'"
            by (etcs_assocl, typecheck_cfuncs, metis graph_equalizer equalizer_eq)
          also have "... = f \<circ>\<^sub>c left_cart_proj X Y \<circ>\<^sub>c graph_morph f \<circ>\<^sub>c y'"
            by (subst left, simp)
          also have "... = right_cart_proj X Y \<circ>\<^sub>c graph_morph f \<circ>\<^sub>c y'"
            by (etcs_assocl, typecheck_cfuncs, metis graph_equalizer equalizer_eq)
          finally show ?thesis.
        qed
      qed
      then have "i \<circ>\<^sub>c x' = y'"
        using equalizer_is_monomorphism graph_equalizer monomorphism_def2 by (typecheck_cfuncs_prems, blast)
      then show "\<exists>x'. x' \<in>\<^sub>c R \<and> i \<circ>\<^sub>c x' = y'"
        by (intro exI[where x=x'], simp add: x'_type)
    qed
    then have "isomorphism i"
      by (metis comp_monic_imp_monic' epi_mon_is_iso f_type graph_morph_type i_eq i_type m_mono surjective_is_epimorphism)
    then show "\<exists>i. i : R \<rightarrow> graph f \<and> isomorphism i \<and> m = graph_morph f \<circ>\<^sub>c i"
      by (intro exI[where x=i], simp add: i_type i_eq)
  qed
next
  fix f1 f2 i1 i2
  assume f1_type[type_rule]: "f1 : X \<rightarrow> Y"
  assume f2_type[type_rule]: "f2 : X \<rightarrow> Y"
  assume i1_type[type_rule]: "i1 : R \<rightarrow> graph f1"
  assume i2_type[type_rule]: "i2 : R \<rightarrow> graph f2"
  assume i1_iso: "isomorphism i1"
  assume i2_iso: "isomorphism i2"
  assume eq1: "m = graph_morph f1 \<circ>\<^sub>c i1"
  assume eq2: "graph_morph f1 \<circ>\<^sub>c i1 = graph_morph f2 \<circ>\<^sub>c i2" 

  have m_type[type_rule]: "m : R \<rightarrow> X \<times>\<^sub>c Y"
    using assms unfolding functional_on_def subobject_of_def2 by auto
  have isomorphism[type_rule]: "isomorphism(left_cart_proj X Y \<circ>\<^sub>c m)"
    using assms functional_on_isomorphism by force  
  obtain h where h_type[type_rule]: "h: X \<rightarrow> R" and h_def: "h = (left_cart_proj X Y \<circ>\<^sub>c m)\<^bold>\<inverse>"
    by (typecheck_cfuncs, simp)
  have "f1 \<circ>\<^sub>c left_cart_proj X Y \<circ>\<^sub>c m = f2 \<circ>\<^sub>c left_cart_proj X Y \<circ>\<^sub>c m"
  proof - 
    have "f1 \<circ>\<^sub>c left_cart_proj X Y \<circ>\<^sub>c m = (f1 \<circ>\<^sub>c left_cart_proj X Y) \<circ>\<^sub>c graph_morph f1 \<circ>\<^sub>c i1"
      using comp_associative2 eq1 eq2 by (typecheck_cfuncs, force)
    also have "... = (right_cart_proj X Y) \<circ>\<^sub>c graph_morph f1 \<circ>\<^sub>c i1"
      by (typecheck_cfuncs, smt comp_associative2 equalizer_def graph_equalizer4)
    also have "... = (right_cart_proj X Y) \<circ>\<^sub>c graph_morph f2 \<circ>\<^sub>c i2"
      by (simp add: eq2)
    also have "... = (f2 \<circ>\<^sub>c left_cart_proj X Y) \<circ>\<^sub>c graph_morph f2 \<circ>\<^sub>c i2"
      by (typecheck_cfuncs, smt comp_associative2 equalizer_eq graph_equalizer4)
    also have "... = f2 \<circ>\<^sub>c left_cart_proj X Y \<circ>\<^sub>c m"
      by (typecheck_cfuncs, metis comp_associative2 eq1 eq2)
    finally show ?thesis.
  qed
  then show "f1 = f2"
    by (typecheck_cfuncs, metis cfunc_type_def comp_associative h_def h_type id_right_unit2 inverse_def2 isomorphism)
qed

end