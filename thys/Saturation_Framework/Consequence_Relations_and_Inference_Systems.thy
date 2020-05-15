(*  Title:       Consequence Relations and Inference Systems of the Saturation Framework
 *   Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2018-2020 *)

section \<open>Consequence Relations and Inference Systems\<close>

text \<open>This section introduces the most basic notions upon which the framework is
  built: consequence relations and inference systems. It also defines the notion
  of a family of consequence relations. This corresponds to section 2.1 of the report.\<close>

theory Consequence_Relations_and_Inference_Systems
  imports Main
begin

subsection \<open>Consequence Relations\<close>

locale consequence_relation =
  fixes
    Bot :: "'f set" and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50)
  assumes
    bot_not_empty: "Bot \<noteq> {}" and
    bot_entails_all: "B \<in> Bot \<Longrightarrow> {B} \<Turnstile> N1" and
    subset_entailed: "N2 \<subseteq> N1 \<Longrightarrow> N1 \<Turnstile> N2" and
    all_formulas_entailed: "(\<forall>C \<in> N2. N1 \<Turnstile> {C}) \<Longrightarrow> N1 \<Turnstile> N2" and
    entails_trans[trans]: "N1 \<Turnstile> N2 \<Longrightarrow> N2 \<Turnstile> N3 \<Longrightarrow> N1 \<Turnstile> N3"
begin

lemma entail_set_all_formulas: "N1 \<Turnstile> N2 \<longleftrightarrow> (\<forall>C \<in> N2. N1 \<Turnstile> {C})"
  by (meson all_formulas_entailed empty_subsetI insert_subset subset_entailed entails_trans)

lemma entail_union: "N \<Turnstile> N1 \<and> N \<Turnstile> N2 \<longleftrightarrow> N \<Turnstile> N1 \<union> N2"
  using entail_set_all_formulas[of N N1] entail_set_all_formulas[of N N2]
    entail_set_all_formulas[of N "N1 \<union> N2"] by blast

lemma entail_unions: "(\<forall>i \<in> I. N \<Turnstile> Ni i) \<longleftrightarrow> N \<Turnstile> \<Union> (Ni ` I)"
  using entail_set_all_formulas[of N "\<Union> (Ni ` I)"] entail_set_all_formulas[of N]
    Complete_Lattices.UN_ball_bex_simps(2)[of Ni I "\<lambda>C. N \<Turnstile> {C}", symmetric]
  by meson

lemma entail_all_bot: "(\<exists>B \<in> Bot. N \<Turnstile> {B}) \<Longrightarrow> (\<forall>B' \<in> Bot. N \<Turnstile> {B'})"
  using bot_entails_all entails_trans by blast

lemma entails_trans_strong: "N1 \<Turnstile> N2 \<Longrightarrow> N1 \<union> N2 \<Turnstile> N3 \<Longrightarrow> N1 \<Turnstile> N3"
  by (meson entail_union entails_trans order_refl subset_entailed)

end

subsection \<open>Families of Consequence Relations\<close>

locale consequence_relation_family =
  fixes
    Bot :: "'f set" and
    Q :: "'q set" and
    entails_q :: "'q \<Rightarrow> ('f set \<Rightarrow> 'f set \<Rightarrow> bool)"
  assumes
    Q_nonempty: "Q \<noteq> {}" and
    q_cons_rel: "\<forall>q \<in> Q. consequence_relation Bot (entails_q q)"
begin

lemma bot_not_empty: "Bot \<noteq> {}"
  using Q_nonempty consequence_relation.bot_not_empty consequence_relation_family.q_cons_rel
    consequence_relation_family_axioms by blast

definition entails_Q :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>Q" 50) where
  "N1 \<Turnstile>Q N2 \<longleftrightarrow> (\<forall>q \<in> Q. entails_q q N1 N2)"

(* lem:intersection-of-conseq-rel *)
lemma intersect_cons_rel_family: "consequence_relation Bot entails_Q"
  unfolding consequence_relation_def entails_Q_def
  by (intro conjI bot_not_empty) (metis consequence_relation_def q_cons_rel)+

end

subsection \<open>Inference Systems\<close>

datatype 'f inference =
  Infer (prems_of: "'f list") (concl_of: "'f")

locale inference_system =
  fixes
    Inf :: \<open>'f inference set\<close>
begin

definition Inf_from :: "'f set \<Rightarrow> 'f inference set" where
  "Inf_from N = {\<iota> \<in> Inf. set (prems_of \<iota>) \<subseteq> N}"

definition Inf_from2 :: "'f set \<Rightarrow> 'f set \<Rightarrow> 'f inference set" where
  "Inf_from2 N M = Inf_from (N \<union> M) - Inf_from (N - M)"

lemma Inf_if_Inf_from: "\<iota> \<in> Inf_from N \<Longrightarrow> \<iota> \<in> Inf"
  unfolding Inf_from_def by simp

lemma Inf_if_Inf_from2: "\<iota> \<in> Inf_from2 N M \<Longrightarrow> \<iota> \<in> Inf"
  unfolding Inf_from2_def Inf_from_def by simp

lemma Inf_from2_alt:
  "Inf_from2 N M = {\<iota> \<in> Inf. \<iota> \<in> Inf_from (N \<union> M) \<and> set (prems_of \<iota>) \<inter> M \<noteq> {}}"
  unfolding Inf_from_def Inf_from2_def by auto

lemma Inf_from_mono: "N \<subseteq> N' \<Longrightarrow> Inf_from N \<subseteq> Inf_from N'"
  unfolding Inf_from_def by auto

lemma Inf_from2_mono: "N \<subseteq> N' \<Longrightarrow> M \<subseteq> M' \<Longrightarrow> Inf_from2 N M \<subseteq> Inf_from2 N' M'"
  unfolding Inf_from2_alt using Inf_from_mono[of "N \<union> M" "N' \<union> M'"] by auto

end

subsection \<open>Families of Inference Systems\<close>

locale inference_system_family =
  fixes
    Q :: "'q set" and
    Inf_q :: "'q \<Rightarrow> 'f inference set"
  assumes
    Q_nonempty: "Q \<noteq> {}"
begin

definition Inf_from_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f inference set" where
  "Inf_from_q q = inference_system.Inf_from (Inf_q q)"

definition Inf_from2_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow> 'f inference set" where
  "Inf_from2_q q = inference_system.Inf_from2 (Inf_q q)"

lemma Inf_from2_q_alt:
  "Inf_from2_q q N M = {\<iota> \<in> Inf_q q. \<iota> \<in> Inf_from_q q (N \<union> M) \<and> set (prems_of \<iota>) \<inter> M \<noteq> {}}"
  unfolding Inf_from_q_def Inf_from2_q_def inference_system.Inf_from2_alt by auto

end

end
