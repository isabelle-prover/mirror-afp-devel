theory Induce_L_Verification
  imports 
    "../abs-proof/Abs_Induce_L_Verification"
    "../def/Induce_L"
begin

section "Induce L Refinement"

lemma abs_induce_l_step_to_r0:
  "i < length SA \<Longrightarrow> abs_induce_l_step (B, SA, i) (\<alpha>, T) = induce_l_step_r0 (B, SA, i) (\<alpha>, T)"
  by (clarsimp simp: Let_def split: prod.splits nat.splits SL_types.splits)

lemma induce_l_step_r0_to:
  "\<lbrakk>length ST = length T; \<forall>k < length ST. ST ! k = suffix_type T k\<rbrakk> \<Longrightarrow>
    induce_l_step_r0 (B, SA, i) (\<alpha>, T) = induce_l_step (B, SA, i) (\<alpha>, T, ST)"
  by (clarsimp simp: Let_def split: prod.splits nat.splits SL_types.splits)

lemma abs_induce_l_step_to:
  assumes "i < length SA"
  and     "length ST = length T"
  and     "\<forall>k < length ST. ST ! k = suffix_type T k"
shows "abs_induce_l_step (B, SA, i) (\<alpha>, T) = induce_l_step (B, SA, i) (\<alpha>, T, ST)"
  by (metis assms induce_l_step_r0_to abs_induce_l_step_to_r0)

lemma repeat_abs_induce_l_step_to:
  assumes "n \<le> length SA"
  and     "length ST = length T"
  and     "\<forall>k < length ST. ST ! k = suffix_type T k"
shows "repeat n abs_induce_l_step (B, SA, 0) (\<alpha>, T) = repeat n induce_l_step (B, SA, 0) (\<alpha>, T, ST)"
  using assms(1)
proof (induct n)
case 0
  then show ?case
    by (simp add: repeat_0)
next
  case (Suc n)
  note IH = this

  from repeat_step[of n abs_induce_l_step "(B, SA, 0)" "(\<alpha>, T)"]
  have A: "repeat (Suc n) abs_induce_l_step (B, SA, 0) (\<alpha>, T) =
            abs_induce_l_step (repeat n abs_induce_l_step (B, SA, 0) (\<alpha>, T)) (\<alpha>, T)"
    by assumption

  from repeat_step[of n induce_l_step "(B, SA, 0)" "(\<alpha>, T, ST)"]
  have B: "repeat (Suc n) induce_l_step (B, SA, 0) (\<alpha>, T, ST) =
            induce_l_step (repeat n induce_l_step (B, SA, 0) (\<alpha>, T, ST)) (\<alpha>, T, ST)"
    by assumption

  from repeat_abs_induce_l_step_index[of n B SA 0 \<alpha> T]
  obtain B' SA' where
    C: "repeat n abs_induce_l_step (B, SA, 0) (\<alpha>, T) = (B', SA', n)"
    by auto
  with IH
  have D: "repeat n induce_l_step (B, SA, 0) (\<alpha>, T, ST) = (B', SA', n)"
    by simp

  from IH(2)
  have "n < length SA"
    by simp
  with repeat_abs_induce_l_step_lengths[OF C]
  have "n < length SA'"
    by simp

  from abs_induce_l_step_to[OF `n < length SA'` assms(2-), of B']
       A B C D
  show ?case
    by simp
qed

lemma abs_induce_l_base_to:
  assumes "length SA = length T"
  and     "length ST = length T"
  and     "\<forall>i < length ST. ST ! i = suffix_type T i"
shows "abs_induce_l_base \<alpha> T B SA = induce_l_base \<alpha> T ST B SA"
  unfolding induce_l_base_def abs_induce_l_base_def
  by (simp add: assms(1, 2,3) repeat_abs_induce_l_step_to)

lemma abs_induce_l_eq:
  assumes "length SA = length T"
  and     "length ST = length T"
  and     "\<forall>i < length ST. ST ! i = suffix_type T i"
shows "abs_induce_l \<alpha> T B SA = induce_l \<alpha> T ST B SA"
  by (metis assms abs_induce_l_base_to abs_induce_l_def induce_l_def)

end