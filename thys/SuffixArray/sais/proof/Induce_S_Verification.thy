theory Induce_S_Verification
  imports 
    "../abs-proof/Abs_Induce_S_Verification"
    "../def/Induce_S"
begin

section "Induce S Refinement"

lemma abs_induce_s_step_to_r0:
  shows "induce_s_step_r0 (B, SA, i) (\<alpha>, T) = abs_induce_s_step (B, SA, i) (\<alpha>, T)"
proof (cases i)
  case 0
  then show ?thesis
    by simp
next
  case (Suc n)
  assume "i = Suc n"
  then show ?thesis
  proof (cases "Suc n < length SA")
    assume "Suc n < length SA"
    show ?thesis
    proof (cases "SA ! Suc n < length T")
      assume "SA ! Suc n < length T"
      show ?thesis
      proof (cases "SA ! Suc n")
        case 0
        then show ?thesis
          by (clarsimp simp: \<open>i = _\<close> \<open>Suc n < length _\<close>  \<open>SA ! _ < _\<close>)
      next
        case (Suc j)
        assume "SA ! Suc n = Suc j"
        hence "Suc j < length T"
          using \<open>SA ! Suc n < length T\<close> by auto
        then show ?thesis
          by (clarsimp simp: \<open>i = _\<close> \<open>Suc n < length _\<close>  \<open>SA ! _ < _\<close>)
      qed
    next
      assume "\<not> SA ! Suc n < length T"
      then show ?thesis
        by simp
    qed
  next
    assume "\<not> Suc n < length SA"
    show ?thesis
      by (clarsimp simp: \<open>i = _\<close> \<open>\<not> _\<close>)
  qed
qed

lemma induce_s_step_r0_to_r1:
  assumes "length ST = length T"
  and     "\<forall>k < length ST. ST ! k = suffix_type T k"
shows "induce_s_step_r1 (B, SA, i) (\<alpha>, T, ST) = induce_s_step_r0 (B, SA, i) (\<alpha>, T)"
proof (cases i)
  case 0
  then show ?thesis
    by auto
next
  case (Suc n)
  assume "i = Suc n"
  then show ?thesis
  proof (cases "Suc n < length SA \<and> SA ! Suc n < length T")
    assume "Suc n < length SA \<and> SA ! Suc n < length T"
    hence "Suc n < length SA" "SA ! Suc n < length T"
      by blast+
    then show ?thesis
    proof (cases "SA ! Suc n")
      case 0
      then show ?thesis
        by (clarsimp simp: \<open>i = _\<close> \<open>Suc n < length _\<close> \<open>SA ! _ < _\<close>)
    next
      case (Suc j)
      assume "SA ! Suc n = Suc j"
      hence "ST ! j = suffix_type T j"
        using \<open>SA ! Suc n < length T\<close> assms(1,2) by force
      then show ?thesis
        by (clarsimp simp: \<open>i = _\<close> \<open>Suc n < length _\<close> \<open>SA ! _ < _\<close> \<open>SA ! _ = _\<close>)
    qed
  next
    assume "\<not> (Suc n < length SA \<and> SA ! Suc n < length T)"
    show ?thesis
      by (simp add: \<open>\<not> _\<close>\<open>i = Suc n\<close>)
  qed
qed

lemma abs_induce_s_step_to_r1:
  assumes "length ST = length T"
  and     "\<forall>k < length ST. ST ! k = suffix_type T k"
shows "induce_s_step_r1 (B, SA, i) (\<alpha>, T, ST) = abs_induce_s_step (B, SA, i) (\<alpha>, T)"
  by (metis assms induce_s_step_r0_to_r1 abs_induce_s_step_to_r0)

lemma induce_s_step_r1_to_r2:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  shows "induce_s_step_r2 (B, SA, i) (\<alpha>, T, ST) = induce_s_step_r1 (B, SA, i) (\<alpha>, T, ST)"
proof (cases i)
  case 0
  then show ?thesis
    by simp
next
  case (Suc n)
  then show ?thesis
  proof (cases "Suc n < length SA")
    assume "Suc n < length SA"
    moreover
    have "SA ! Suc n < length T"
      by (metis Suc assms calculation dual_order.refl s_perm_inv_elims(5) s_seen_invD(1))
    ultimately show ?thesis
    proof (cases "SA ! Suc n")
      case 0
      then show ?thesis
        using \<open>i = Suc n\<close> \<open>Suc n < length SA\<close> \<open>SA ! Suc n < length T\<close>
        by simp
    next
      case (Suc j)
      assume "SA ! Suc n = Suc j"
      then show ?thesis
      proof (cases "ST ! j")
        assume "ST ! j = S_type"
        then show ?thesis
          using \<open>i = Suc n\<close> \<open>Suc n < length SA\<close> \<open>SA ! Suc n < length T\<close> \<open>SA ! Suc n = Suc j\<close>
          by (clarsimp simp: Let_def)
      next
        assume "ST ! j = L_type"
        then show ?thesis
          using \<open>i = Suc n\<close> \<open>Suc n < length SA\<close> \<open>SA ! Suc n < length T\<close> \<open>SA ! Suc n = Suc j\<close>
          by (clarsimp simp: Let_def)
        qed
    qed
  next
    assume "i = Suc n" "\<not>Suc n < length SA"
    then show ?thesis
      by simp
  qed
qed

lemma abs_induce_s_step_to_r2:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "length ST = length T"
  and     "\<forall>k < length ST. ST ! k = suffix_type T k"
shows "induce_s_step_r2 (B, SA, i) (\<alpha>, T, ST) = abs_induce_s_step (B, SA, i) (\<alpha>, T)"
  by (metis assms induce_s_step_r1_to_r2 induce_s_step_r0_to_r1 abs_induce_s_step_to_r0)

lemma induce_s_step_r2_to:
  "i < length SA \<Longrightarrow> induce_s_step (B, SA, i) (\<alpha>, T, ST) = induce_s_step_r2 (B, SA, i) (\<alpha>, T, ST)"
  by (clarsimp simp: Let_def split: nat.splits)

lemma abs_induce_s_step_to:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "length ST = length T"
  and     "\<forall>k < length ST. ST ! k = suffix_type T k"
  and     "i < length SA"
shows "induce_s_step (B, SA, i) (\<alpha>, T, ST) = abs_induce_s_step (B, SA, i) (\<alpha>, T)"
  by (metis abs_induce_s_step_to_r2 assms induce_s_step_r2_to)

lemma abs_induce_s_base_to':
  assumes "s_perm_inv \<alpha> T B SA0 SA n"
  and     "length ST = length T"
  and     "\<forall>k < length ST. ST ! k = suffix_type T k"
  and     "n < length SA"
shows "repeat m induce_s_step (B, SA, n) (\<alpha>, T, ST) = repeat m abs_induce_s_step (B, SA, n) (\<alpha>, T)"
  using assms(1,4)
proof (induct m arbitrary: B SA n)
  case 0
  then show ?case
    by (simp add: repeat_0)
next
  case (Suc m)
  note IH = this and
       R0 = repeat_step[of m abs_induce_s_step "(B, SA, n)" "(\<alpha>, T)"] and
       R1 = repeat_step[of m induce_s_step "(B, SA, n)" "(\<alpha>, T, ST)"]

  from repeat_abs_induce_s_step_index[of m B SA n \<alpha> T]
  obtain B' SA' where S: 
    "repeat m abs_induce_s_step (B, SA, n) (\<alpha>, T) = (B', SA', n - m)"
    "length SA' = length SA"
    "length B' = length B"
    by blast

  have "n - m < length SA"
    using Suc.prems(2) by auto
  hence "n - m < length SA'"
    using S(2) by fastforce

  from IH(1)[OF IH(2,3)] R1 S
  have "repeat (Suc m) induce_s_step (B, SA, n) (\<alpha>, T, ST)
          = induce_s_step (B', SA', n - m) (\<alpha>, T, ST)"
    by simp
  moreover
  from IH(1)[OF IH(2)] R0 S
  have "repeat (Suc m) abs_induce_s_step (B, SA, n) (\<alpha>, T)
          = abs_induce_s_step (B', SA', n - m) (\<alpha>, T)"
    by simp
  moreover
  let ?P = "\<lambda>(B, SA, i). s_perm_inv \<alpha> T B SA0 SA i"
  have "s_perm_inv \<alpha> T B' SA0 SA' (n - m)"
    by (rule repeat_maintain_inv[of ?P abs_induce_s_step "(\<alpha>, T)" "(B, SA, n)" m,
                                  simplified S, simplified, OF _ IH(2)];
        clarsimp simp del: abs_induce_s_step.simps;
        erule (1) abs_induce_s_perm_step)
  with abs_induce_s_step_to[OF _ assms(2,3) `n - m < length SA'`, of \<alpha> B' SA0]
  have "induce_s_step (B', SA', n - m) (\<alpha>, T, ST) = abs_induce_s_step (B', SA', n - m) (\<alpha>, T)"
    by blast
  ultimately show ?case 
    by simp
qed

lemma repeat_abs_induce_step_gre_length:
  assumes "length SA = length T"
  shows
    "length T \<le> Suc n \<Longrightarrow>
     repeat (Suc m) abs_induce_s_step (B, SA, Suc n) (\<alpha>, T)
      = repeat m abs_induce_s_step (B, SA, n) (\<alpha>, T)"
proof (induct m arbitrary: n)
  case 0
  then show ?case
    by (simp add: repeat_0 repeat_step Let_def assms)
next
  case (Suc m)
  note IH = this

  from repeat_step[of "Suc m" abs_induce_s_step "(B, SA, Suc n)" "(\<alpha>, T)"]
       IH(1)[OF IH(2)]
  have "repeat (Suc (Suc m)) abs_induce_s_step (B, SA, Suc n) (\<alpha>, T)
          = abs_induce_s_step (repeat m abs_induce_s_step (B, SA, n) (\<alpha>, T)) (\<alpha>, T)"
    by presburger
  with repeat_step[of m abs_induce_s_step "(B, SA, n)" "(\<alpha>, T)"]
  show ?case
    by presburger
qed

lemma abs_induce_s_base_to:
  assumes "s_perm_pre \<alpha> T B SA (length T)"
  and     "length ST = length T"
  and     "\<forall>k < length ST. ST ! k = suffix_type T k"
shows "induce_s_base \<alpha> T ST B SA = abs_induce_s_base \<alpha> T B SA"
proof -
  note A = assms(1)[simplified s_perm_pre_def]

  from assms(1)[simplified s_perm_pre_def]
  have "s_perm_inv \<alpha> T B SA SA (length T)"
    by (simp add: s_perm_inv_established)
  with abs_induce_s_base_to'[OF _ assms(2-)]
  have "repeat (length T - Suc 0) induce_s_step (B, SA, length T - Suc 0) (\<alpha>, T, ST)
        = repeat (length T - Suc 0) abs_induce_s_step (B, SA, length T - Suc 0) (\<alpha>, T)"
    by (metis Suc_lessD Suc_pred A diff_Suc_less s_perm_inv_maintained_step_c1)
  moreover
  have "repeat (length T) abs_induce_s_step (B, SA, length T) (\<alpha>, T)
        = repeat (length T - Suc 0) abs_induce_s_step (B, SA, length T - Suc 0) (\<alpha>, T)"
    by (metis Suc_lessD Suc_pred A repeat_abs_induce_step_gre_length)
  ultimately show ?thesis
    by (simp add: abs_induce_s_base_def induce_s_base_def)
qed

lemma abs_induce_s_eq:
  assumes "s_perm_pre \<alpha> T B SA (length T)"
  and     "length ST = length T"
  and     "\<forall>k < length ST. ST ! k = suffix_type T k"
shows "abs_induce_s \<alpha> T B SA = induce_s \<alpha> T ST B SA"
  by (simp add: assms abs_induce_s_base_to abs_induce_s_def induce_s_def)

end