theory Ground_Ordered_Resolution
  imports
    First_Order_Clause.Selection_Function
    First_Order_Clause.Ground_Order
    First_Order_Clause.Literal_Functor
begin

section \<open>Resolution Calculus\<close>

locale ground_ordered_resolution_calculus =
  ground_order where less\<^sub>t = less\<^sub>t +
  selection_function select
for
  less\<^sub>t :: "'t \<Rightarrow> 't \<Rightarrow> bool" and
  select :: "'t clause \<Rightarrow> 't clause"
begin

subsection \<open>Resolution Calculus\<close>

inductive resolution :: "'t clause \<Rightarrow> 't clause \<Rightarrow> 't clause \<Rightarrow> bool" where
  resolutionI: 
  "E = add_mset l\<^sub>1 E' \<Longrightarrow>
   D = add_mset l\<^sub>2 D' \<Longrightarrow>
   l\<^sub>1 = Neg t \<Longrightarrow>
   l\<^sub>2 = Pos t \<Longrightarrow>
   C = (E' + D') \<Longrightarrow>
   resolution D E C"
if 
 "D \<prec>\<^sub>c E"
 "select E = {#} \<and> is_maximal l\<^sub>1 E \<or> is_maximal l\<^sub>1 (select E)"
 "select D = {#}"
 "is_strictly_maximal l\<^sub>2 D"

inductive factoring :: "'t clause \<Rightarrow> 't clause \<Rightarrow> bool" where
  factoringI: 
  "D = add_mset l (add_mset l D') \<Longrightarrow>
   l = Pos t \<Longrightarrow>
   C = add_mset l D' \<Longrightarrow>
   factoring D C"
if
  "select D = {#}"
  "is_maximal l D"

subsection \<open>Ground Layer\<close>

abbreviation resolution_inferences where
  "resolution_inferences \<equiv> {Infer [D, E] C | D E C. resolution D E C}"

abbreviation factoring_inferences where
  "factoring_inferences \<equiv> {Infer [D] C | D C. factoring D C}"

definition G_Inf :: "'t clause inference set" where
  "G_Inf =
    {Infer [D, E] C | D E C. resolution D E C} \<union>
    {Infer [D] C | D C. factoring D C}"

abbreviation G_Bot :: "'t clause set" where
  "G_Bot \<equiv> {{#}}"

definition G_entails :: "'t clause set \<Rightarrow> 't clause set \<Rightarrow> bool" where
  "G_entails N\<^sub>1 N\<^sub>2 \<longleftrightarrow> (\<forall> I. I \<TTurnstile>s N\<^sub>1 \<longrightarrow> I \<TTurnstile>s N\<^sub>2)"

subsection \<open>Smaller Conclussions\<close>

lemma ground_resolution_smaller_conclusion:
  assumes
    step: "resolution D E C"
  shows "C \<prec>\<^sub>c E"
  using step
proof (cases D E C rule: resolution.cases)
  case (resolutionI l\<^sub>1 l\<^sub>2 E' D' t)

  have "\<forall>k\<in>#D'. k \<prec>\<^sub>l Pos t"
    using \<open>is_strictly_maximal l\<^sub>2 D\<close> \<open>D = add_mset l\<^sub>2 D'\<close>
    using is_strictly_maximal_def resolutionI(8)
    by fastforce

  moreover have "\<And>A. Pos A \<prec>\<^sub>l Neg A"
    unfolding literal.order.multiset_extension_def
    by auto

  ultimately have "\<forall>k\<in>#D'. k \<prec>\<^sub>l Neg t"
    using literal.order.order.strict_trans
    by blast

  hence "D' \<prec>\<^sub>c {#Neg t#}"
    using one_step_implies_multp[of "{#Neg t#}" D' "(\<prec>\<^sub>l)" "{#}"]
    by (simp add: less\<^sub>c_def)

  hence "D' + E' \<prec>\<^sub>c add_mset (Neg t) E'"
    using multp_cancel[of "(\<prec>\<^sub>l)" E' D' "{#Neg t#}"] less\<^sub>c_def 
    by force

  thus ?thesis
    unfolding resolutionI
    by (simp only: add.commute)
qed

lemma ground_factoring_smaller_conclusion:
  assumes step: "factoring D C"
  shows "C \<prec>\<^sub>c D"
  using step
proof (cases D C rule: factoring.cases)
  case (factoringI l D' t)
 
  have "C = add_mset l D'"
    using factoringI
    by argo

  then show ?thesis
    by (metis (lifting) add.comm_neutral add_mset_add_single add_mset_not_empty 
        clause.order.multiset_extension_def empty_iff local.factoringI(3)
        one_step_implies_multp set_mset_empty)
qed

end

subsection \<open>Redundancy Criterion\<close>

sublocale ground_ordered_resolution_calculus \<subseteq> consequence_relation where
  Bot = G_Bot and
  entails = G_entails
proof unfold_locales

  show "G_Bot \<noteq> {}"
    by simp
next

  show "\<And>B N. B \<in> G_Bot \<Longrightarrow> G_entails {B} N"
    by (simp add: G_entails_def)
next

  show "\<And>N2 N1. N2 \<subseteq> N1 \<Longrightarrow> G_entails N1 N2"
    by (auto simp: G_entails_def elim!: true_clss_mono[rotated])
next
  fix N1 N2 
  assume ball_G_entails: "\<forall>C \<in> N2. G_entails N1 {C}"

  show "G_entails N1 N2"
    unfolding G_entails_def
  proof (intro allI impI)
    fix I :: "'t set"
    assume "I \<TTurnstile>s N1"

    hence "\<forall>C \<in> N2. I \<TTurnstile>s {C}"
      using ball_G_entails 
      by (simp add: G_entails_def)

    then show "I \<TTurnstile>s N2"
      by (simp add: true_clss_def)
  qed
next

  show "\<And>N1 N2 N3. G_entails N1 N2 \<Longrightarrow> G_entails N2 N3 \<Longrightarrow> G_entails N1 N3"
    using G_entails_def 
    by simp
qed

sublocale ground_ordered_resolution_calculus \<subseteq> calculus_with_finitary_standard_redundancy where
  Inf = G_Inf and
  Bot = G_Bot and
  entails = G_entails and
  less = "(\<prec>\<^sub>c)"
  defines GRed_I = Red_I and GRed_F = Red_F
proof unfold_locales

  show "transp (\<prec>\<^sub>c)"
    by simp
next

  show "wfP (\<prec>\<^sub>c)"
    by auto
next

  show "\<And>\<iota>. \<iota> \<in> G_Inf \<Longrightarrow> prems_of \<iota> \<noteq> []"
    by (auto simp: G_Inf_def)
next
  fix \<iota>

  have "concl_of \<iota> \<prec>\<^sub>c main_prem_of \<iota>"
    if \<iota>_def: "\<iota> = Infer [D, E] C" and
      infer: "resolution D E C"
    for E D C
    unfolding \<iota>_def
    using infer
    using ground_resolution_smaller_conclusion
    by simp

  moreover have "concl_of \<iota> \<prec>\<^sub>c main_prem_of \<iota>"
    if \<iota>_def: "\<iota> = Infer [D] C" and
      infer: "factoring D C"
    for D C
    unfolding \<iota>_def
    using infer
    using ground_factoring_smaller_conclusion
    by simp

  ultimately show "\<iota> \<in> G_Inf \<Longrightarrow> concl_of \<iota> \<prec>\<^sub>c main_prem_of \<iota>"
    unfolding G_Inf_def
    by fast
qed

end
