theory Horn_Inference
  imports Main
begin

datatype 'a horn = horn "'a list" 'a (infix "\<rightarrow>\<^sub>h" 55)

locale horn =
  fixes \<H> :: "'a horn set"
begin

inductive_set saturate :: "'a set" where
  infer: "as \<rightarrow>\<^sub>h a \<in> \<H> \<Longrightarrow> (\<And>x. x \<in> set as \<Longrightarrow> x \<in> saturate) \<Longrightarrow> a \<in> saturate"

definition infer0 where
  "infer0 = {a. [] \<rightarrow>\<^sub>h a \<in> \<H>}"

definition infer1 where
  "infer1 x B = {a |as a. as \<rightarrow>\<^sub>h a \<in> \<H> \<and> x \<in> set as \<and> set as \<subseteq> B \<union> {x}}"

inductive step :: "'a set \<times> 'a set \<Rightarrow> 'a set \<times> 'a set \<Rightarrow> bool" (infix "\<turnstile>" 50) where
  delete: "x \<in> B \<Longrightarrow> (insert x G, B) \<turnstile> (G, B)"
| propagate: "(insert x G, B) \<turnstile> (G \<union> infer1 x B, insert x B)"
| refl: "(G, B) \<turnstile> (G, B)"
| trans: "(G, B) \<turnstile> (G', B') \<Longrightarrow> (G', B') \<turnstile> (G'', B'') \<Longrightarrow> (G, B) \<turnstile> (G'', B'')"

lemma step_mono:
  "(G, B) \<turnstile> (G', B') \<Longrightarrow> (H \<union> G, B) \<turnstile> (H \<union> G', B')"
  by (induction "(G, B)" "(G', B')" arbitrary: G B G' B' rule: step.induct)
    (auto intro: step.intros simp: Un_assoc[symmetric])

fun invariant where
  "invariant (G, B) \<longleftrightarrow> G \<subseteq> saturate \<and> B \<subseteq> saturate \<and> (\<forall>a as. as \<rightarrow>\<^sub>h a \<in> \<H> \<and> set as \<subseteq> B \<longrightarrow> a \<in> G \<union> B)"

lemma inv_start:
  shows "invariant (infer0, {})"
  by (auto simp: infer0_def invariant.simps intro: infer)

lemma inv_step:
  assumes "invariant (G, B)" "(G, B) \<turnstile> (G', B')"
  shows "invariant (G', B')"
  using assms(2,1)
proof (induction "(G, B)" "(G', B')" arbitrary: G B G' B' rule: step.induct)
  case (propagate x G B)
  let ?G' = "G \<union> local.infer1 x B" and ?B' = "insert x B"
  have "?G' \<subseteq> saturate" "?B' \<subseteq> saturate"
    using assms(1) propagate by (auto 0 3 simp: infer1_def intro: saturate.infer)
  moreover have "as \<rightarrow>\<^sub>h a \<in> \<H> \<Longrightarrow> set as \<subseteq> ?B' \<Longrightarrow> a \<in> ?G' \<union> ?B'" for a as
    using assms(1) propagate by (fastforce simp: infer1_def)
  ultimately show ?case by auto
qed auto

lemma inv_end:
  assumes "invariant ({}, B)"
  shows "B = saturate"
proof (intro set_eqI iffI, goal_cases lr rl)
  case (lr x) then show ?case using assms by auto
next
  case (rl x) then show ?case using assms
    by (induct x rule: saturate.induct) fastforce
qed

lemma step_sound:
  "(infer0, {}) \<turnstile> ({}, B) \<Longrightarrow> B = saturate"
  by (metis inv_start inv_step inv_end)

end

lemma horn_infer0_union:
  "horn.infer0 (\<H>\<^sub>1 \<union> \<H>\<^sub>2) = horn.infer0 \<H>\<^sub>1 \<union> horn.infer0 \<H>\<^sub>2"
  by (auto simp: horn.infer0_def)

lemma horn_infer1_union:
  "horn.infer1 (\<H>\<^sub>1 \<union> \<H>\<^sub>2) x B = horn.infer1 \<H>\<^sub>1 x B \<union> horn.infer1 \<H>\<^sub>2 x B"
  by (auto simp: horn.infer1_def)

end
