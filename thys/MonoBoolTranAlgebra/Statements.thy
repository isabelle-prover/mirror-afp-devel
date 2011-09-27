header {* Program statements, Hoare and refinement rules *}

theory  Statements
imports Assertion_Algebra
begin

text {*In this section we introduce assume, if, and while program statements
as well as Hoare triples, and data refienment. We prove Hoare correctness
rules for the program statements and we prove some theorems linking Hoare
correctness statement to (data) refinement. Most of the theorems assume
a monotonic boolean transformers algebra. The theorem stating the 
equivalence between a Hoare
correctness triple and a refinement statement holds under the
assumption that we have a monotonic boolean transformers algebra with
post condition statement. Finally the Hoare rules for fixpoint
and while statement are proved asumming that we have a complete
monotonic boolean transformers algebra.*}

definition
  "assume" :: "'a::mbt_algebra Assertion \<Rightarrow> 'a"  ("[\<cdot> _ ]" [0] 1000) where
  "[\<cdot>p] =  {\<cdot>p} ^ o"

lemma [simp]: "{\<cdot>p} * \<top> \<sqinter> [\<cdot>p] = {\<cdot>p}"
  apply (subgoal_tac "{\<cdot>p} \<in> assertion")
  apply (subst (asm) assertion_def, simp add: assume_def)
  by simp

lemma [simp]: "[\<cdot>p] * x \<squnion> {\<cdot>-p} * \<top> = [\<cdot>p] * x"
  by (simp add: assume_def  uminus_Assertion_def)

lemma [simp]: "{\<cdot>p} * \<top> \<squnion> [\<cdot>-p] * x = [\<cdot>-p] * x"
  by (simp add: assume_def  uminus_Assertion_def)

lemma assert_sup: "{\<cdot>p \<squnion> q} = {\<cdot>p} \<squnion> {\<cdot>q}"
  by (simp add: sup_Assertion_def)

lemma assert_inf: "{\<cdot>p \<sqinter> q} = {\<cdot>p} \<sqinter> {\<cdot>q}"
  by (simp add: inf_Assertion_def)

lemma assert_neg: "{\<cdot>-p} = neg_assert {\<cdot>p}"
  by (simp add: uminus_Assertion_def)

lemma if_Assertion_assumption: "({\<cdot>p} * x) \<squnion> ({\<cdot>-p} * y) = ([\<cdot>p] * x) \<sqinter> ([\<cdot>-p] * y)"
proof -
    have "({\<cdot>p} * x) \<squnion> {\<cdot>-p} * y = ({\<cdot>p} * \<top> \<sqinter> [\<cdot>p]) * x \<squnion> ({\<cdot>-p} * \<top> \<sqinter> [\<cdot>-p]) * y" by simp
    also have "\<dots> = ({\<cdot>p} * \<top> \<sqinter> ([\<cdot>p] * x)) \<squnion> ({\<cdot>-p} * \<top> \<sqinter> ([\<cdot>-p] * y))" by (unfold inf_comp, simp)
    also have "\<dots> = (({\<cdot>p} * \<top> \<sqinter> ([\<cdot>p] * x)) \<squnion> ({\<cdot>-p} * \<top>)) \<sqinter> (({\<cdot>p} * \<top> \<sqinter> ([\<cdot>p] * x)) \<squnion> ([\<cdot>-p] * y))" by (simp add: sup_inf_distrib)
    also have "\<dots> = (({\<cdot>p} * \<top>  \<squnion> ({\<cdot>-p} * \<top>)) \<sqinter> (([\<cdot>p] * x))) \<sqinter> (([\<cdot>-p] * y) \<sqinter> (([\<cdot>p] * x) \<squnion> ([\<cdot>-p] * y)))"
      by (simp add: sup_inf_distrib2)
    also have "\<dots> = ([\<cdot>p] * x) \<sqinter>  ([\<cdot>-p] * y) \<sqinter> (([\<cdot>p] * x) \<squnion> ([\<cdot>-p] * y))"
      apply (simp add: sup_comp [THEN sym] )
      by (simp add: assert_sup [THEN sym] inf_assoc sup_compl_top)
    also have "\<dots> = ([\<cdot>p] * x) \<sqinter>  ([\<cdot>-p] * y)"
      by (rule antisym, simp_all add: inf_assoc)
    finally show ?thesis .
  qed

definition
  "wp x p = abs_wpt (x * {\<cdot>p})"

lemma wp_assume: "wp [\<cdot>p] q = -p \<squnion> q"
  apply (simp add: wp_def abs_wpt_def)
  apply (rule assert_injective)
  apply simp
  by (simp add: assert_sup assert_neg assume_def wpt_dual_assertion_comp)


lemma assert_commute: "y \<in> conjunctive \<Longrightarrow> y * {\<cdot>p} = {\<cdot> wp y p } * y"
  apply (simp add: wp_def abs_wpt_def)
  by (rule assertion_commute, simp_all)

lemma wp_assert: "wp {\<cdot>p} q = p \<sqinter> q"
  by (simp add: wp_def assertion_inf_comp_eq [THEN sym] assert_inf [THEN sym])

lemma wp_mono [simp]: "mono (wp x)"
  apply (simp add: le_fun_def wp_def abs_wpt_def less_eq_Assertion_def mono_def)
  apply (simp add: wpt_def, safe)
  apply (rule_tac y = " x * {\<cdot> xa } * \<top>" in order_trans, simp_all)
  apply (rule le_comp_right)
  by (rule le_comp, simp)

lemma wp_fun_mono [simp]: "mono wp"
  apply (simp add: le_fun_def wp_def abs_wpt_def less_eq_Assertion_def mono_def)
  apply (simp add: wpt_def, safe)
  apply (rule_tac y = " x * {\<cdot> xa } * \<top>" in order_trans, simp_all)
  apply (rule le_comp_right)
  by (rule le_comp_right, simp) 


lemma wp_fun_mono2: "x \<le> y \<Longrightarrow> wp x p \<le> wp y p"
  apply (cut_tac wp_fun_mono)
  apply (unfold mono_def)
  apply (simp add: le_fun_def)
  by blast


lemma wp_comp: "wp (x * y) p = wp x (wp y p)"
  apply (simp add: wp_def abs_wpt_def)
  by (unfold wpt_comp_2 [THEN sym] mult_assoc, simp)

lemma wp_choice: "wp (x \<sqinter> y) = wp x \<sqinter> wp y"
  apply (simp add: fun_eq_iff wp_def inf_fun_def inf_comp inf_Assertion_def abs_wpt_def)
  by (simp add: wpt_choice)

lemma Assertion_wp: "{\<cdot>wp x p} = (x * {\<cdot>p} * \<top>) \<sqinter> 1"
  apply (simp add: wp_def abs_wpt_def)
  by (simp add: wpt_def)

definition
  "hoare p S q = (p \<le> wp S q)"

definition
  "grd x = - (wp x \<bottom>)"

lemma grd_comp: "[\<cdot>grd x] * x = x"
  apply (simp add: grd_def wp_def uminus_Assertion_def assume_def neg_assert_def abs_wpt_def dual_sup sup_comp)
  apply (simp add: wpt_def dual_inf sup_comp dual_comp bot_Assertion_def)
  by (rule antisym, simp_all)

lemma assert_assume: "{\<cdot>p} * [\<cdot>p] = {\<cdot> p}"
  by (simp add: assume_def)

lemma dual_assume: "[\<cdot>p] ^ o = {\<cdot>p}"
  by (simp add: assume_def)

lemma assume_prop: "([\<cdot>p] * \<bottom>) \<squnion> 1 = [\<cdot>p]"
  by (simp add: assume_def dual_assertion_prop)

text{*An alternative definition of a Hoare triple*}

definition "hoare1 p S q = ([\<cdot> p ] * S * [\<cdot> -q ] = \<top>)"

lemma "hoare1  p S q = hoare p S q"
  apply (simp add: hoare1_def dual_inf dual_comp)
  apply (simp add: hoare_def wp_def less_eq_Assertion_def abs_wpt_def)
  apply (simp add: wpt_def)
  apply safe
  proof -
    assume A: "[\<cdot> p ] * S * [\<cdot> - q ] = \<top>"
    have "{\<cdot>p} \<le> {\<cdot>p} * \<top>" by simp
    also have "... \<le> {\<cdot>p} * \<top> * \<bottom>" by (unfold mult_assoc, simp)
    also have "... = {\<cdot>p} * [\<cdot> p ] * S * [\<cdot> - q ] * \<bottom>" by (subst A [THEN sym], simp add: mult_assoc)
    also have "... = {\<cdot>p} * S * [\<cdot> - q ] * \<bottom>" by (simp add: assert_assume)
    also have "... \<le> {\<cdot>p} * S * {\<cdot> q } * \<top>"
      apply (simp add: mult_assoc)
      apply (rule le_comp, rule le_comp)
      apply (simp add: assume_def uminus_Assertion_def)
      by (simp add: neg_assert_def dual_inf dual_comp sup_comp)
    also have "... \<le> S * {\<cdot> q } * \<top>" by (simp add: mult_assoc)
    finally show "{\<cdot>p} \<le> S * {\<cdot> q } * \<top>" .
  next
    assume A: "{\<cdot> p } \<le> S * {\<cdot> q } * \<top>"
    have "\<top> = ((S * {\<cdot>q}) ^ o) * \<bottom> \<squnion> S * {\<cdot>q} * \<top>" by simp
    also have "\<dots> \<le> [\<cdot>p] * \<bottom> \<squnion> S * {\<cdot>q} * \<top>"
      apply (simp del: dual_neg_top)
      apply (rule_tac y = "[\<cdot>p] * \<bottom>" in order_trans, simp_all)
      apply (subst dual_le)
      apply (simp add: dual_comp dual_assume)
      apply (cut_tac x = "{\<cdot>p}" and y = "S * {\<cdot>q} * \<top>" and z = \<top> in le_comp_right)
      apply (rule A)
      by (simp add: mult_assoc)
    also have "\<dots> = [\<cdot>p] * S * ({\<cdot>q} * \<top>)"
      apply (subst (2) assume_prop [THEN sym])
      by (simp_all add: sup_comp mult_assoc)
    also have "\<dots> \<le> [\<cdot>p] * S * ({\<cdot>q} * \<top> \<squnion> 1)"
      by (rule le_comp, simp)
    also have "\<dots> = [\<cdot>p] * S * [\<cdot>-q]"
      apply (simp add: assume_def uminus_Assertion_def)
      by (simp add: neg_assert_def dual_inf dual_comp)
    finally show "[\<cdot>p] * S * [\<cdot> - q] = \<top>"
      by (rule_tac antisym, simp_all)
  qed

lemma hoare_choice: "hoare p (x \<sqinter> y) q = ((hoare p) x q & (hoare p y q))"
  apply (unfold hoare_def wp_choice inf_fun_def)
  by auto

definition
  if_stm:: "'a::mbt_algebra Assertion \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("(If (_)/ then (_)/ else (_))" [0, 0, 10] 10) where
  "if_stm b x y = (([\<cdot> b ] * x) \<sqinter> ([\<cdot> -b ] * y))"

lemma (in boolean_algebra) sup_neg_inf:
  "(p \<le> q \<squnion> r) = (p \<sqinter> -q \<le> r)"
  apply (safe)
  apply(cut_tac a = p and c = "q \<squnion> r" and b = "-q" and d = "-q" in inf_mono)
  apply simp apply simp apply (simp add: inf_sup_distrib2 inf_compl_bot)
  apply(cut_tac b = "p \<sqinter> - q" and d = "r" and a = "q" and c = "q" in sup_mono)
  apply simp apply simp  by (simp add: sup_inf_distrib sup_compl_top)

lemma hoare_if: "hoare p (If b then x else y) q = (hoare (p \<sqinter> b) x q \<and> hoare (p \<sqinter> -b) y q)"
  by (simp add: hoare_def if_stm_def wp_choice inf_fun_def wp_comp wp_assume sup_neg_inf)

lemma hoare_comp: "hoare p (x * y) q = (\<exists> r . (hoare p x r) \<and> (hoare r y q))"
   apply (simp add: hoare_def wp_comp)
   apply safe
   apply (rule_tac x = "wp y q" in exI, simp)
   apply (rule_tac y = "wp x r" in order_trans, simp)
   apply (rule_tac f = "wp x" in monoD)
   by simp_all


lemma hoare_refinement: "hoare p S q = ({\<cdot>p} * (post {\<cdot>q}) \<le> S)"
  apply (simp add: hoare_def less_eq_Assertion_def Assertion_wp)
  proof
    assume A: "{\<cdot>p} \<le> S * {\<cdot>q} * \<top>"
    have "{\<cdot>p} * post {\<cdot>q} = ({\<cdot>p} * \<top> \<sqinter> 1) * post {\<cdot>q}" by (simp add: assertion_prop)
    also have "\<dots> = {\<cdot>p} * \<top> \<sqinter> post {\<cdot>q}" by (simp add: inf_comp)
    also have "\<dots> \<le> S * {\<cdot>q} * \<top> \<sqinter> post {\<cdot>q}" apply simp
      apply (rule_tac y = "{\<cdot>p} * \<top>" in order_trans, simp_all)
      apply (cut_tac x = "{\<cdot>p}" and y = "S * {\<cdot>q} * \<top>" and z = \<top> in le_comp_right)
      by (rule A, simp)
    also have "\<dots> \<le> S" by (simp add: post_2)
    finally show "{\<cdot>p} * post {\<cdot>q} \<le> S".
  next
    assume A: "{\<cdot>p} * post {\<cdot>q} \<le> S"
    have "{\<cdot>p} = {\<cdot>p} * \<top> \<sqinter> 1" by (simp add: assertion_prop)
    also have "\<dots> = {\<cdot>p} * ((post {\<cdot>q}) * {\<cdot>q} * \<top>) \<sqinter> 1" by (simp add: post_1)
    also have "\<dots> \<le> {\<cdot>p} * ((post {\<cdot>q}) * {\<cdot>q} * \<top>)" by simp
    also have "\<dots> \<le> S * {\<cdot>q} * \<top>" 
      apply (cut_tac x = "{\<cdot>p} * post {\<cdot>q}" and y = S and z = "{\<cdot>q} * \<top>" in le_comp_right)
      apply (simp add: A)
      by (simp add: mult_assoc)
    finally show "{\<cdot>p} \<le> S * {\<cdot>q} * \<top>" .
  qed

theorem hoare_fixpoint:
  "F x = x \<Longrightarrow> mono F 
     \<Longrightarrow> (!! w f . hoare (Sup_less p w) f q \<Longrightarrow> hoare (p w) (F f) q) 
     \<Longrightarrow> hoare (Sup (range p)) x q"
  apply (simp add: hoare_refinement assert_Sup_range assert_Sup_less)
  apply (cut_tac x = x and f = F and y = "\<lambda> w . {\<cdot>p w} * post {\<cdot>q}" in fp_wf_induction, simp_all)
  apply safe
  apply (subgoal_tac "Sup_less (assert o p) w * post {\<cdot>q} \<le> (Sup_less (\<lambda>w\<Colon>'b. {\<cdot>p w} * post {\<cdot>q}) w)")
  apply simp
  apply (simp add: Sup_less_def Sup_comp SUP_def)
  apply (subgoal_tac "((\<lambda>x . x * post {\<cdot>q}) ` {y. \<exists>v<w. y = {\<cdot>p v}}) = {y\<Colon>'a. \<exists>v<w. y = {\<cdot>p v} * post {\<cdot>q}}")
  apply simp
  apply auto [1]
  apply (subgoal_tac "Sup (range (\<lambda>w . {\<cdot>p w} * post {\<cdot>q})) = (Sup (range (assert o p))) * post {\<cdot>q}", simp)
  apply (simp add: Sup_comp SUP_def)
  apply (subgoal_tac "range (\<lambda>w. {\<cdot>p w} * post {\<cdot>q}) = ((\<lambda>x . x * post {\<cdot>q}) ` range (assert o p))")
  by auto
 

definition
  while:: "'a::mbt_algebra Assertion \<Rightarrow> 'a \<Rightarrow> 'a" ("(While (_)/ do (_))" [0, 10] 10) where
  "while p x = ([\<cdot> p] * x) ^ \<omega> * [\<cdot> -p ]"


lemma hoare_while:
  "(\<forall> w::'b::well_founded_transitive . hoare ((p w) \<sqinter> b) x (Sup_less p w)) \<Longrightarrow> 
       hoare  (Sup (range p)) (While b do x) ((Sup (range p)) \<sqinter> -b)"
  apply (unfold while_def omega_lfp)
  apply (subgoal_tac "mono (\<lambda>z. [\<cdot> b ] * x * z \<sqinter> [\<cdot> - b ])")
  apply (rule_tac F = "\<lambda>z. [\<cdot> b ] * x * z \<sqinter> [\<cdot> - b ]" in hoare_fixpoint)
  apply (cut_tac f = "\<lambda>z. [\<cdot> b ] * x * z \<sqinter> [\<cdot> - b ]" in lfp_unfold)
  apply simp_all
  apply (unfold hoare_choice)
  apply safe
  apply (simp_all add: hoare_def wp_comp wp_assume sup_neg_inf)
  apply (rule_tac y = "wp x (Sup_less p w)" in order_trans, simp)
  apply (rule_tac f = "wp x" in monoD, simp_all) 
  apply (rule_tac y = "p w" in order_trans, simp_all)
  apply (rule Sup_upper, simp)
  apply (simp add: mono_def)
  apply safe
  apply (rule_tac y = "[\<cdot> b ] * x * xa" in order_trans, simp)
  by (rule le_comp, simp)


definition 
  "datarefin S S1 D D1 = (D * S \<le> S1 * D1)"

lemma "hoare p S q \<Longrightarrow> datarefin S S1 D D1 \<Longrightarrow> hoare (wp D p) S1 (wp D1 q)"
  apply (simp add: hoare_def datarefin_def)
  apply (simp add: wp_comp [THEN sym] mult_assoc [THEN sym])
  apply (rule_tac y = "wp (D * S) q" in order_trans)
  apply (subst wp_comp)
  apply (rule monoD, simp_all)
  by (rule wp_fun_mono2, simp_all)

lemma "hoare p S q \<Longrightarrow> datarefin ({\<cdot>p} * S) S1 D D1 \<Longrightarrow> hoare (wp D p) S1 (wp D1 q)"
  apply (simp add: hoare_def datarefin_def)
  apply (rule_tac y = "wp (D * {\<cdot>p} * S) q" in order_trans)
  apply (simp add: mult_assoc)
  apply (subst wp_comp)
  apply (rule monoD, simp_all)
  apply (subst wp_comp)
  apply (unfold wp_assert, simp)
  apply (unfold wp_comp [THEN sym])
  apply (rule wp_fun_mono2)
  by (simp add: mult_assoc)

end