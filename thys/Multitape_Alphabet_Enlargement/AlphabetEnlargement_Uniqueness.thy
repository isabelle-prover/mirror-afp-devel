theory AlphabetEnlargement_Uniqueness
  imports AlphabetEnlargement_Simulation
begin

subsection \<open>Block-predicate identities (VFwd exclusion support)\<close>

text \<open>Identities relating \<open>is_pure_block\<close>,
  \<open>is_padded_block\<close>, \<open>LE_block\<close>, and \<open>bl_block\<close>.
  Used by the VFwd 6-fold pairwise exclusion lemmas below
  (and downstream by the reverse-arm trace decoder).  Located here
  because the proofs need \<open>c_idx_enum_nth\<close> to construct
  index witnesses inside the existential in
  \<open>is_padded_block\<close>.\<close>

lemma is_pure_not_padded:
  fixes f :: "'c :: enum \<Rightarrow> 'a"
  shows "is_pure_block bl f \<Longrightarrow> \<not> is_padded_block bl f"
  unfolding is_pure_block_def is_padded_block_def
proof clarify
  fix k :: nat
  assume pure: "\<forall>x :: 'c. f x \<noteq> bl"
     and k_lb: "1 \<le> k"
     and k_ub: "k < length (enum_class.enum :: 'c list)"
     and suffix: "\<forall>x :: 'c. k \<le> c_idx x \<longrightarrow> f x = bl"
  let ?x = "(enum_class.enum :: 'c list) ! k"
  have "c_idx ?x = k" using c_idx_enum_nth[OF k_ub] .
  hence "k \<le> c_idx ?x" by simp
  hence "f ?x = bl" using suffix by blast
  thus False using pure by blast
qed

lemma not_is_pure_bl_block:
  "\<not> is_pure_block (bl :: 'a) (bl_block bl :: 'c :: enum \<Rightarrow> 'a)"
  unfolding is_pure_block_def bl_block_def by simp

lemma not_is_padded_bl_block:
  "\<not> is_padded_block (bl :: 'a) (bl_block bl :: 'c :: enum \<Rightarrow> 'a)"
  unfolding is_padded_block_def bl_block_def
proof clarify
  fix k :: nat
  assume k_lb: "1 \<le> k"
     and k_ub: "k < length (enum_class.enum :: 'c list)"
     and prefix: "\<forall>x :: 'c. c_idx x < k \<longrightarrow> (\<lambda>_. bl) x \<noteq> bl"
  have len_pos: "0 < length (enum_class.enum :: 'c list)" using k_lb k_ub by linarith
  let ?x = "(enum_class.enum :: 'c list) ! 0"
  have "c_idx ?x = 0" using c_idx_enum_nth[OF len_pos] .
  hence "c_idx ?x < k" using k_lb by linarith
  hence "(\<lambda>_ :: 'c. bl) ?x \<noteq> bl" using prefix by blast
  thus False by simp
qed

lemma is_pure_LE_block:
  "(le :: 'a) \<noteq> bl \<Longrightarrow>
     is_pure_block bl (LE_block le :: 'c :: enum \<Rightarrow> 'a)"
  unfolding is_pure_block_def LE_block_def by simp

lemma not_is_padded_LE_block:
  "(le :: 'a) \<noteq> bl \<Longrightarrow>
     \<not> is_padded_block bl (LE_block le :: 'c :: enum \<Rightarrow> 'a)"
  using is_pure_LE_block is_pure_not_padded by metis

lemma LE_block_eq_bl_block_imp_eq:
  fixes le bl :: 'a
  assumes "(LE_block le :: 'c :: enum \<Rightarrow> 'a) = bl_block bl"
  shows "le = bl"
proof -
  have len_pos: "0 < length (enum_class.enum :: 'c list)"
    using c_idx_in_range(1)[of "c_first :: 'c"] by linarith
  let ?x = "(enum_class.enum :: 'c list) ! 0"
  from assms have "(LE_block le :: 'c \<Rightarrow> 'a) ?x = bl_block bl ?x" by simp
  thus ?thesis unfolding LE_block_def bl_block_def by simp
qed

subsection \<open>VFwd 6-fold within-phase exclusion\<close>

text \<open>The four VFwd-source relations (advance, \<open>to_padded\<close>,
  \<open>to_ret\<close>, reject) are pairwise disjoint under
  \<open>le_neq_bl\<close>.\<close>

lemma ae_delta_val_fwd_advance_to_padded_disjoint:
  fixes M :: "('q, 'a) mttm"
    and a :: "nat \<Rightarrow> 'c :: enum \<Rightarrow> 'a"
  assumes "le_tm M \<noteq> bl_tm M"
      and "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_advance M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_padded M"
  shows "False"
proof -
  have alt: "a 0 = LE_block (le_tm M)
              \<or> is_pure_block (bl_tm M) (a 0)"
    using assms(2) unfolding ae_delta_val_fwd_advance_def by auto
  have padded: "is_padded_block (bl_tm M) (a 0)"
    using assms(3) unfolding ae_delta_val_fwd_to_padded_def by auto
  from alt show False
  proof
    assume "a 0 = LE_block (le_tm M)"
    thus False using padded assms(1) not_is_padded_LE_block by metis
  next
    assume "is_pure_block (bl_tm M) (a 0)"
    thus False using padded is_pure_not_padded by metis
  qed
qed

lemma ae_delta_val_fwd_advance_to_ret_disjoint:
  fixes M :: "('q, 'a) mttm"
    and a :: "nat \<Rightarrow> 'c :: enum \<Rightarrow> 'a"
  assumes "le_tm M \<noteq> bl_tm M"
      and "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_advance M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_ret M"
  shows "False"
proof -
  have alt: "a 0 = LE_block (le_tm M)
              \<or> is_pure_block (bl_tm M) (a 0)"
    using assms(2) unfolding ae_delta_val_fwd_advance_def by auto
  have to_ret: "a 0 = bl_block (bl_tm M)"
    using assms(3) unfolding ae_delta_val_fwd_to_ret_def by auto
  from alt show False
  proof
    assume "a 0 = LE_block (le_tm M)"
    with to_ret have eq: "(LE_block (le_tm M) :: 'c \<Rightarrow> 'a) = bl_block (bl_tm M)" by simp
    hence "le_tm M = bl_tm M" by (rule LE_block_eq_bl_block_imp_eq)
    thus False using assms(1) by simp
  next
    assume "is_pure_block (bl_tm M) (a 0)"
    with to_ret have "is_pure_block (bl_tm M) (bl_block (bl_tm M) :: 'c \<Rightarrow> 'a)" by simp
    thus False using not_is_pure_bl_block[where 'c='c and bl="bl_tm M"] by simp
  qed
qed

lemma ae_delta_val_fwd_advance_reject_disjoint:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_advance M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_reject M"
  shows "False"
  using assms
  unfolding ae_delta_val_fwd_advance_def ae_delta_val_fwd_reject_def
            is_canonical_block_def
  by auto

lemma ae_delta_val_fwd_to_padded_to_ret_disjoint:
  fixes M :: "('q, 'a) mttm"
    and a :: "nat \<Rightarrow> 'c :: enum \<Rightarrow> 'a"
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_to_padded M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_ret M"
  shows "False"
proof -
  have padded: "is_padded_block (bl_tm M) (a 0)"
    using assms(1) unfolding ae_delta_val_fwd_to_padded_def by auto
  have to_ret: "a 0 = bl_block (bl_tm M)"
    using assms(2) unfolding ae_delta_val_fwd_to_ret_def by auto
  from padded to_ret
    have "is_padded_block (bl_tm M) (bl_block (bl_tm M) :: 'c \<Rightarrow> 'a)" by simp
  thus False using not_is_padded_bl_block[where 'c='c and bl="bl_tm M"] by simp
qed

lemma ae_delta_val_fwd_to_padded_reject_disjoint:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_to_padded M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_reject M"
  shows "False"
  using assms
  unfolding ae_delta_val_fwd_to_padded_def ae_delta_val_fwd_reject_def
            is_canonical_block_def
  by auto

lemma ae_delta_val_fwd_to_ret_reject_disjoint:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_to_ret M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_reject M"
  shows "False"
  using assms
  unfolding ae_delta_val_fwd_to_ret_def ae_delta_val_fwd_reject_def
  by auto

text \<open>V-marker dispatch helpers: package the within-cluster
  multi-relation disjunction + pairwise disjointness + per-relation
  functionality into a single \<open>_functional\<close> lemma per V marker.
  Used by \<open>alphabet_enlarge_delta_functional\<close>'s V cases.\<close>

lemma ae_delta_VFwd_functional:
  fixes M :: "('q, 'a) mttm"
  assumes le_neq_bl: "le_tm M \<noteq> bl_tm M"
      and h1: "(s, a, s1, a1, d1) \<in> alphabet_enlarge_delta M"
      and h2: "(s, a, s2, a2, d2) \<in> alphabet_enlarge_delta M"
      and idx: "snd (snd (snd (snd s))) = VFwd"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
proof -
  have alt1: "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_advance M
                \<or> (s, a, s1, a1, d1) \<in> ae_delta_val_fwd_to_padded M
                \<or> (s, a, s1, a1, d1) \<in> ae_delta_val_fwd_reject M
                \<or> (s, a, s1, a1, d1) \<in> ae_delta_val_fwd_to_ret M"
    using h1 idx
    unfolding alphabet_enlarge_delta_def
              ae_delta_val_pad_to_ret_def
              ae_delta_val_pad_reject_def
              ae_delta_val_ret_step_def
              ae_delta_val_ret_to_sim_def
              ae_delta_ss1_ss2_def
              ae_delta_ss2_ss3_def
              ae_delta_ss3_ss4_def
              ae_delta_ss4_ss5_def
              ae_delta_ss5_ss6_def
              ae_delta_ss6_ss7_def
              ae_delta_ss7_ss8_def
              ae_delta_ss8_ss1_def
    by auto
  have alt2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_advance M
                \<or> (s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_padded M
                \<or> (s, a, s2, a2, d2) \<in> ae_delta_val_fwd_reject M
                \<or> (s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_ret M"
    using h2 idx
    unfolding alphabet_enlarge_delta_def
              ae_delta_val_pad_to_ret_def
              ae_delta_val_pad_reject_def
              ae_delta_val_ret_step_def
              ae_delta_val_ret_to_sim_def
              ae_delta_ss1_ss2_def
              ae_delta_ss2_ss3_def
              ae_delta_ss3_ss4_def
              ae_delta_ss4_ss5_def
              ae_delta_ss5_ss6_def
              ae_delta_ss6_ss7_def
              ae_delta_ss7_ss8_def
              ae_delta_ss8_ss1_def
    by auto
  from alt1 show ?thesis
  proof (elim disjE)
    assume A1: "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_advance M"
    from alt2 show ?thesis
    proof (elim disjE)
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_advance M"
      show ?thesis using ae_delta_val_fwd_advance_functional[OF A1 A2] by simp
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_padded M"
      have False using ae_delta_val_fwd_advance_to_padded_disjoint[OF le_neq_bl A1 A2] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_reject M"
      have False using ae_delta_val_fwd_advance_reject_disjoint[OF A1 A2] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_ret M"
      have False using ae_delta_val_fwd_advance_to_ret_disjoint[OF le_neq_bl A1 A2] .
      thus ?thesis ..
    qed
  next
    assume A1: "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_to_padded M"
    from alt2 show ?thesis
    proof (elim disjE)
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_advance M"
      have False using ae_delta_val_fwd_advance_to_padded_disjoint[OF le_neq_bl A2 A1] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_padded M"
      show ?thesis using ae_delta_val_fwd_to_padded_functional[OF A1 A2] by simp
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_reject M"
      have False using ae_delta_val_fwd_to_padded_reject_disjoint[OF A1 A2] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_ret M"
      have False using ae_delta_val_fwd_to_padded_to_ret_disjoint[OF A1 A2] .
      thus ?thesis ..
    qed
  next
    assume A1: "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_reject M"
    from alt2 show ?thesis
    proof (elim disjE)
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_advance M"
      have False using ae_delta_val_fwd_advance_reject_disjoint[OF A2 A1] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_padded M"
      have False using ae_delta_val_fwd_to_padded_reject_disjoint[OF A2 A1] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_reject M"
      show ?thesis using ae_delta_val_fwd_reject_functional[OF A1 A2] by simp
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_ret M"
      have False using ae_delta_val_fwd_to_ret_reject_disjoint[OF A2 A1] .
      thus ?thesis ..
    qed
  next
    assume A1: "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_to_ret M"
    from alt2 show ?thesis
    proof (elim disjE)
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_advance M"
      have False using ae_delta_val_fwd_advance_to_ret_disjoint[OF le_neq_bl A2 A1] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_padded M"
      have False using ae_delta_val_fwd_to_padded_to_ret_disjoint[OF A2 A1] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_reject M"
      have False using ae_delta_val_fwd_to_ret_reject_disjoint[OF A1 A2] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_ret M"
      show ?thesis using ae_delta_val_fwd_to_ret_functional[OF A1 A2] by simp
    qed
  qed
qed

lemma ae_delta_VRet_functional:
  fixes M :: "('q, 'a) mttm"
  assumes h1: "(s, a, s1, a1, d1) \<in> alphabet_enlarge_delta M"
      and h2: "(s, a, s2, a2, d2) \<in> alphabet_enlarge_delta M"
      and idx: "snd (snd (snd (snd s))) = VRet"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
proof -
  have alt1: "(s, a, s1, a1, d1) \<in> ae_delta_val_ret_step M
                \<or> (s, a, s1, a1, d1) \<in> ae_delta_val_ret_to_sim M"
    using h1 idx
    unfolding alphabet_enlarge_delta_def
              ae_delta_val_fwd_advance_def
              ae_delta_val_fwd_to_padded_def
              ae_delta_val_fwd_reject_def
              ae_delta_val_fwd_to_ret_def
              ae_delta_val_pad_to_ret_def
              ae_delta_val_pad_reject_def
              ae_delta_ss1_ss2_def
              ae_delta_ss2_ss3_def
              ae_delta_ss3_ss4_def
              ae_delta_ss4_ss5_def
              ae_delta_ss5_ss6_def
              ae_delta_ss6_ss7_def
              ae_delta_ss7_ss8_def
              ae_delta_ss8_ss1_def
    by auto
  have alt2: "(s, a, s2, a2, d2) \<in> ae_delta_val_ret_step M
                \<or> (s, a, s2, a2, d2) \<in> ae_delta_val_ret_to_sim M"
    using h2 idx
    unfolding alphabet_enlarge_delta_def
              ae_delta_val_fwd_advance_def
              ae_delta_val_fwd_to_padded_def
              ae_delta_val_fwd_reject_def
              ae_delta_val_fwd_to_ret_def
              ae_delta_val_pad_to_ret_def
              ae_delta_val_pad_reject_def
              ae_delta_ss1_ss2_def
              ae_delta_ss2_ss3_def
              ae_delta_ss3_ss4_def
              ae_delta_ss4_ss5_def
              ae_delta_ss5_ss6_def
              ae_delta_ss6_ss7_def
              ae_delta_ss7_ss8_def
              ae_delta_ss8_ss1_def
    by auto
  from alt1 show ?thesis
  proof
    assume A1: "(s, a, s1, a1, d1) \<in> ae_delta_val_ret_step M"
    from alt2 show ?thesis
    proof
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_ret_step M"
      show ?thesis using ae_delta_val_ret_step_functional[OF A1 A2] by simp
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_ret_to_sim M"
      have False using ae_delta_val_ret_step_ret_to_sim_disjoint[OF A1 A2] .
      thus ?thesis ..
    qed
  next
    assume A1: "(s, a, s1, a1, d1) \<in> ae_delta_val_ret_to_sim M"
    from alt2 show ?thesis
    proof
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_ret_step M"
      have False using ae_delta_val_ret_step_ret_to_sim_disjoint[OF A2 A1] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_ret_to_sim M"
      show ?thesis using ae_delta_val_ret_to_sim_functional[OF A1 A2] by simp
    qed
  qed
qed

lemma ae_delta_VFwdPad_functional:
  fixes M :: "('q, 'a) mttm"
  assumes h1: "(s, a, s1, a1, d1) \<in> alphabet_enlarge_delta M"
      and h2: "(s, a, s2, a2, d2) \<in> alphabet_enlarge_delta M"
      and idx: "snd (snd (snd (snd s))) = VFwdPad"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
proof -
  have alt1: "(s, a, s1, a1, d1) \<in> ae_delta_val_pad_to_ret M
                \<or> (s, a, s1, a1, d1) \<in> ae_delta_val_pad_reject M"
    using h1 idx
    unfolding alphabet_enlarge_delta_def
              ae_delta_val_fwd_advance_def
              ae_delta_val_fwd_to_padded_def
              ae_delta_val_fwd_reject_def
              ae_delta_val_fwd_to_ret_def
              ae_delta_val_ret_step_def
              ae_delta_val_ret_to_sim_def
              ae_delta_ss1_ss2_def
              ae_delta_ss2_ss3_def
              ae_delta_ss3_ss4_def
              ae_delta_ss4_ss5_def
              ae_delta_ss5_ss6_def
              ae_delta_ss6_ss7_def
              ae_delta_ss7_ss8_def
              ae_delta_ss8_ss1_def
    by auto
  have alt2: "(s, a, s2, a2, d2) \<in> ae_delta_val_pad_to_ret M
                \<or> (s, a, s2, a2, d2) \<in> ae_delta_val_pad_reject M"
    using h2 idx
    unfolding alphabet_enlarge_delta_def
              ae_delta_val_fwd_advance_def
              ae_delta_val_fwd_to_padded_def
              ae_delta_val_fwd_reject_def
              ae_delta_val_fwd_to_ret_def
              ae_delta_val_ret_step_def
              ae_delta_val_ret_to_sim_def
              ae_delta_ss1_ss2_def
              ae_delta_ss2_ss3_def
              ae_delta_ss3_ss4_def
              ae_delta_ss4_ss5_def
              ae_delta_ss5_ss6_def
              ae_delta_ss6_ss7_def
              ae_delta_ss7_ss8_def
              ae_delta_ss8_ss1_def
    by auto
  from alt1 show ?thesis
  proof
    assume A1: "(s, a, s1, a1, d1) \<in> ae_delta_val_pad_to_ret M"
    from alt2 show ?thesis
    proof
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_pad_to_ret M"
      show ?thesis using ae_delta_val_pad_to_ret_functional[OF A1 A2] by simp
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_pad_reject M"
      have False using ae_delta_val_pad_to_ret_pad_reject_disjoint[OF A1 A2] .
      thus ?thesis ..
    qed
  next
    assume A1: "(s, a, s1, a1, d1) \<in> ae_delta_val_pad_reject M"
    from alt2 show ?thesis
    proof
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_pad_to_ret M"
      have False using ae_delta_val_pad_to_ret_pad_reject_disjoint[OF A2 A1] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_pad_reject M"
      show ?thesis using ae_delta_val_pad_reject_functional[OF A1 A2] by simp
    qed
  qed
qed


subsection \<open>Chain uniqueness --- single-step functionality\<close>

text \<open>Under \<open>valid_mttm M\<close>, \<open>det_mttm M\<close>, and
  \<open>le_tm M \<noteq> bl_tm M\<close>, the alphabet-enlargement
  transition relation is functional in its source pair.  Proof
  case-splits on the source substep index: \<open>SSN\<close> cases dispatch
  via the matching \<open>ae_delta_ssN_only\<close> + \<open>*_functional\<close>
  pair; V-marker cases (\<open>VFwd\<close>, \<open>VFwdPad\<close>, \<open>VRet\<close>) use
  within-cluster disjointness to collapse the multi-relation
  alternative, then apply the surviving sub-relation's functionality
  lemma.\<close>

lemma alphabet_enlarge_delta_functional:
  fixes M :: "('q, 'a) mttm"
  assumes vM:  "valid_mttm M"
      and det: "det_mttm M"
      and le_neq_bl: "le_tm M \<noteq> bl_tm M"
      and h1: "(s, a, s1, a1, d1) \<in> alphabet_enlarge_delta M"
      and h2: "(s, a, s2, a2, d2) \<in> alphabet_enlarge_delta M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
proof (cases "snd (snd (snd (snd s)))")
  case VFwd
  show ?thesis by (rule ae_delta_VFwd_functional[OF le_neq_bl h1 h2 VFwd])
next
  case VFwdPad
  show ?thesis by (rule ae_delta_VFwdPad_functional[OF h1 h2 VFwdPad])
next
  case VRet
  show ?thesis by (rule ae_delta_VRet_functional[OF h1 h2 VRet])
next
  case SS1
  have e1: "(s, a, s1, a1, d1) \<in> ae_delta_ss1_ss2 M"
    by (rule ae_delta_ss1_only[OF h1 SS1])
  have e2: "(s, a, s2, a2, d2) \<in> ae_delta_ss1_ss2 M"
    by (rule ae_delta_ss1_only[OF h2 SS1])
  show ?thesis using ae_delta_ss1_ss2_functional[OF e1 e2] by simp
next
  case SS2
  have e1: "(s, a, s1, a1, d1) \<in> ae_delta_ss2_ss3 M"
    by (rule ae_delta_ss2_only[OF h1 SS2])
  have e2: "(s, a, s2, a2, d2) \<in> ae_delta_ss2_ss3 M"
    by (rule ae_delta_ss2_only[OF h2 SS2])
  show ?thesis using ae_delta_ss2_ss3_functional[OF e1 e2] by simp
next
  case SS3
  have e1: "(s, a, s1, a1, d1) \<in> ae_delta_ss3_ss4 M"
    by (rule ae_delta_ss3_only[OF h1 SS3])
  have e2: "(s, a, s2, a2, d2) \<in> ae_delta_ss3_ss4 M"
    by (rule ae_delta_ss3_only[OF h2 SS3])
  show ?thesis using ae_delta_ss3_ss4_functional[OF e1 e2] by simp
next
  case SS4
  have e1: "(s, a, s1, a1, d1) \<in> ae_delta_ss4_ss5 M"
    by (rule ae_delta_ss4_only[OF h1 SS4])
  have e2: "(s, a, s2, a2, d2) \<in> ae_delta_ss4_ss5 M"
    by (rule ae_delta_ss4_only[OF h2 SS4])
  show ?thesis using ae_delta_ss4_ss5_functional[OF vM det e1 e2] by simp
next
  case SS5
  have e1: "(s, a, s1, a1, d1) \<in> ae_delta_ss5_ss6 M"
    by (rule ae_delta_ss5_only[OF h1 SS5])
  have e2: "(s, a, s2, a2, d2) \<in> ae_delta_ss5_ss6 M"
    by (rule ae_delta_ss5_only[OF h2 SS5])
  show ?thesis using ae_delta_ss5_ss6_functional[OF e1 e2] by simp
next
  case SS6
  have e1: "(s, a, s1, a1, d1) \<in> ae_delta_ss6_ss7 M"
    by (rule ae_delta_ss6_only[OF h1 SS6])
  have e2: "(s, a, s2, a2, d2) \<in> ae_delta_ss6_ss7 M"
    by (rule ae_delta_ss6_only[OF h2 SS6])
  show ?thesis using ae_delta_ss6_ss7_functional[OF e1 e2] by simp
next
  case SS7
  have e1: "(s, a, s1, a1, d1) \<in> ae_delta_ss7_ss8 M"
    by (rule ae_delta_ss7_only[OF h1 SS7])
  have e2: "(s, a, s2, a2, d2) \<in> ae_delta_ss7_ss8 M"
    by (rule ae_delta_ss7_only[OF h2 SS7])
  show ?thesis using ae_delta_ss7_ss8_functional[OF e1 e2] by simp
next
  case SS8
  have e1: "(s, a, s1, a1, d1) \<in> ae_delta_ss8_ss1 M"
    by (rule ae_delta_ss8_only[OF h1 SS8])
  have e2: "(s, a, s2, a2, d2) \<in> ae_delta_ss8_ss1 M"
    by (rule ae_delta_ss8_only[OF h2 SS8])
  show ?thesis using ae_delta_ss8_ss1_functional[OF e1 e2] by simp
qed

text \<open>Lifting chain uniqueness from \<open>alphabet_enlarge_delta\<close>
  to \<open>mttm_step (alphabet_enlarge_delta M)\<close>: single-step then
  \<open>n\<close>-fold via standard induction.  Consumed in stage 6 to identify
  the forward arm's produced \<open>c'''\<close> with the backward arm's
  given \<open>c''\<close>.\<close>

lemma mttm_step_alphabet_enlarge_functional:
  fixes M :: "('q, 'a) mttm"
  assumes vM:  "valid_mttm M"
      and det: "det_mttm M"
      and le_neq_bl: "le_tm M \<noteq> bl_tm M"
      and h1: "(c, c1) \<in> mttm_step (alphabet_enlarge_delta M)"
      and h2: "(c, c2) \<in> mttm_step (alphabet_enlarge_delta M)"
  shows "c1 = c2"
proof -
  from h1 obtain q ts n q1 a1 dir1 where
      c_eq1:  "c  = Config\<^sub>M q ts n"
    and c1_eq: "c1 = Config\<^sub>M q1 (\<lambda>k. (ts k)(n k := a1 k))
                                  (\<lambda>k. go_dir (dir1 k) (n k))"
    and tr1: "(q, \<lambda>k. ts k (n k), q1, a1, dir1)
                \<in> alphabet_enlarge_delta M"
    by (auto elim: mttm_step.cases)
  from h2 obtain q' ts' n' q2 a2 dir2 where
      c_eq2:  "c  = Config\<^sub>M q' ts' n'"
    and c2_eq: "c2 = Config\<^sub>M q2 (\<lambda>k. (ts' k)(n' k := a2 k))
                                  (\<lambda>k. go_dir (dir2 k) (n' k))"
    and tr2: "(q', \<lambda>k. ts' k (n' k), q2, a2, dir2)
                \<in> alphabet_enlarge_delta M"
    by (auto elim: mttm_step.cases)
  from c_eq1 c_eq2
  have qq: "q = q'" and tsts: "ts = ts'" and nn: "n = n'"
    by auto
  from tr1 qq tsts nn
  have tr1': "(q, \<lambda>k. ts k (n k), q1, a1, dir1)
                \<in> alphabet_enlarge_delta M" by simp
  from tr2 qq tsts nn
  have tr2': "(q, \<lambda>k. ts k (n k), q2, a2, dir2)
                \<in> alphabet_enlarge_delta M" by simp
  have "q1 = q2 \<and> a1 = a2 \<and> dir1 = dir2"
    using alphabet_enlarge_delta_functional[OF vM det le_neq_bl tr1' tr2'] .
  thus ?thesis using c1_eq c2_eq tsts nn by simp
qed

lemma mttm_step_alphabet_enlarge_relpow_functional:
  fixes M :: "('q, 'a) mttm"
  assumes vM:  "valid_mttm M"
      and det: "det_mttm M"
      and le_neq_bl: "le_tm M \<noteq> bl_tm M"
      and h1: "(c, c1) \<in> mttm_step (alphabet_enlarge_delta M) ^^ n"
      and h2: "(c, c2) \<in> mttm_step (alphabet_enlarge_delta M) ^^ n"
  shows "c1 = c2"
  using h1 h2
proof (induction n arbitrary: c c1 c2)
  case 0
  thus ?case by simp
next
  case (Suc n)
  from Suc.prems(1) obtain c1' where
      step1: "(c, c1') \<in> mttm_step (alphabet_enlarge_delta M)"
    and rest1: "(c1', c1) \<in> mttm_step (alphabet_enlarge_delta M) ^^ n"
    by (meson relpow_Suc_D2)
  from Suc.prems(2) obtain c2' where
      step2: "(c, c2') \<in> mttm_step (alphabet_enlarge_delta M)"
    and rest2: "(c2', c2) \<in> mttm_step (alphabet_enlarge_delta M) ^^ n"
    by (meson relpow_Suc_D2)
  have c'_eq: "c1' = c2'"
    by (rule mttm_step_alphabet_enlarge_functional
              [OF vM det le_neq_bl step1 step2])
  show ?case using Suc.IH[OF rest1] rest2 c'_eq by simp
qed


text \<open>\<open>det\<close>-free chain uniqueness for the \<^emph>\<open>validation\<close>
  prefix.  \<open>alphabet_enlarge_delta\<close>'s only nondeterministic source is
  the SS4\<open>\<rightarrow>\<close>SS5 macro-step; every other stage marker dispatches to a
  functional substep builder.  In particular, from a validation marker
  (\<open>VFwd\<close> / \<open>VFwdPad\<close> / \<open>VRet\<close>) the transition is single-valued
  with no appeal to \<open>det_mttm M\<close> --- the det-free analogue of
  \<open>alphabet_enlarge_delta_functional\<close> restricted to validation
  sources.  Consumed by \<open>alphabet_enlarge_language\<close>'s reverse arm to
  identify the unique validation prefix from \<open>ae_init_config\<close> without
  the \<open>det\<close> hypothesis of Hopcroft--Ullman's speed-up theorems
  \<^cite>\<open>\<open>Theorems 12.3, 12.4\<close> in "Hopcroft1979:introduction"\<close>.\<close>

lemma alphabet_enlarge_delta_val_functional:
  fixes M :: "('q, 'a) mttm"
  assumes le_neq_bl: "le_tm M \<noteq> bl_tm M"
      and h1: "(s, a, s1, a1, d1) \<in> alphabet_enlarge_delta M"
      and h2: "(s, a, s2, a2, d2) \<in> alphabet_enlarge_delta M"
      and idx: "snd (snd (snd (snd s))) \<in> {VFwd, VFwdPad, VRet}"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
proof -
  consider (VFwd) "snd (snd (snd (snd s))) = VFwd"
         | (VFwdPad) "snd (snd (snd (snd s))) = VFwdPad"
         | (VRet) "snd (snd (snd (snd s))) = VRet"
    using idx by blast
  thus ?thesis
  proof cases
    case VFwd
    show ?thesis by (rule ae_delta_VFwd_functional[OF le_neq_bl h1 h2 VFwd])
  next
    case VFwdPad
    show ?thesis by (rule ae_delta_VFwdPad_functional[OF h1 h2 VFwdPad])
  next
    case VRet
    show ?thesis by (rule ae_delta_VRet_functional[OF h1 h2 VRet])
  qed
qed

lemma mttm_step_alphabet_enlarge_val_functional:
  fixes M :: "('q, 'a) mttm"
  assumes le_neq_bl: "le_tm M \<noteq> bl_tm M"
      and h1: "(c, c1) \<in> mttm_step (alphabet_enlarge_delta M)"
      and h2: "(c, c2) \<in> mttm_step (alphabet_enlarge_delta M)"
      and idx: "snd (snd (snd (snd (mt_state c)))) \<in> {VFwd, VFwdPad, VRet}"
  shows "c1 = c2"
proof -
  from h1 obtain q ts n q1 a1 dir1 where
      c_eq1:  "c  = Config\<^sub>M q ts n"
    and c1_eq: "c1 = Config\<^sub>M q1 (\<lambda>k. (ts k)(n k := a1 k))
                                  (\<lambda>k. go_dir (dir1 k) (n k))"
    and tr1: "(q, \<lambda>k. ts k (n k), q1, a1, dir1) \<in> alphabet_enlarge_delta M"
    by (auto elim: mttm_step.cases)
  from h2 obtain q' ts' n' q2 a2 dir2 where
      c_eq2:  "c  = Config\<^sub>M q' ts' n'"
    and c2_eq: "c2 = Config\<^sub>M q2 (\<lambda>k. (ts' k)(n' k := a2 k))
                                  (\<lambda>k. go_dir (dir2 k) (n' k))"
    and tr2: "(q', \<lambda>k. ts' k (n' k), q2, a2, dir2) \<in> alphabet_enlarge_delta M"
    by (auto elim: mttm_step.cases)
  from c_eq1 c_eq2 have qq: "q = q'" and tsts: "ts = ts'" and nn: "n = n'"
    by auto
  from tr2 qq tsts nn
  have tr2': "(q, \<lambda>k. ts k (n k), q2, a2, dir2) \<in> alphabet_enlarge_delta M"
    by simp
  have idx': "snd (snd (snd (snd q))) \<in> {VFwd, VFwdPad, VRet}"
    using idx c_eq1 by simp
  have "q1 = q2 \<and> a1 = a2 \<and> dir1 = dir2"
    by (rule alphabet_enlarge_delta_val_functional[OF le_neq_bl tr1 tr2' idx'])
  thus ?thesis using c1_eq c2_eq tsts nn by simp
qed

text \<open>The relpow lift: an \<open>R\<close>-chain whose every source config (every
  config strictly before the end) sits at a validation marker is unique.
  The discharge supplies the invariant for an \<open>ae_init_config\<close> prefix
  that stays within the validation sweep.\<close>

lemma mttm_step_alphabet_enlarge_val_relpow_functional:
  fixes M :: "('q, 'a) mttm"
  assumes le_neq_bl: "le_tm M \<noteq> bl_tm M"
      and h1: "(c, c1) \<in> mttm_step (alphabet_enlarge_delta M) ^^ n"
      and h2: "(c, c2) \<in> mttm_step (alphabet_enlarge_delta M) ^^ n"
      and inv: "\<forall>i<n. \<forall>d. (c, d) \<in> mttm_step (alphabet_enlarge_delta M) ^^ i
                    \<longrightarrow> snd (snd (snd (snd (mt_state d))))
                          \<in> {VFwd, VFwdPad, VRet}"
  shows "c1 = c2"
  using h1 h2 inv
proof (induction n arbitrary: c c1 c2)
  case 0
  thus ?case by simp
next
  case (Suc n)
  from Suc.prems(1) obtain c1' where
      step1: "(c, c1') \<in> mttm_step (alphabet_enlarge_delta M)"
    and rest1: "(c1', c1) \<in> mttm_step (alphabet_enlarge_delta M) ^^ n"
    by (meson relpow_Suc_D2)
  from Suc.prems(2) obtain c2' where
      step2: "(c, c2') \<in> mttm_step (alphabet_enlarge_delta M)"
    and rest2: "(c2', c2) \<in> mttm_step (alphabet_enlarge_delta M) ^^ n"
    by (meson relpow_Suc_D2)
  have c_val: "snd (snd (snd (snd (mt_state c)))) \<in> {VFwd, VFwdPad, VRet}"
  proof -
    have a: "(c, c) \<in> mttm_step (alphabet_enlarge_delta M) ^^ 0" by simp
    have b: "(0::nat) < Suc n" by simp
    show ?thesis using Suc.prems(3) a b by blast
  qed
  have c'_eq: "c1' = c2'"
    by (rule mttm_step_alphabet_enlarge_val_functional
                [OF le_neq_bl step1 step2 c_val])
  have rest2': "(c1', c2) \<in> mttm_step (alphabet_enlarge_delta M) ^^ n"
    using rest2 c'_eq by simp
  have inv':
      "\<forall>i<n. \<forall>d. (c1', d) \<in> mttm_step (alphabet_enlarge_delta M) ^^ i
                    \<longrightarrow> snd (snd (snd (snd (mt_state d))))
                          \<in> {VFwd, VFwdPad, VRet}"
  proof (intro allI impI)
    fix i d
    assume i_lt: "i < n"
      and reach: "(c1', d) \<in> mttm_step (alphabet_enlarge_delta M) ^^ i"
    have "(c, d) \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc i"
      by (rule relpow_Suc_I2[OF step1 reach])
    moreover have "Suc i < Suc n" using i_lt by simp
    ultimately show "snd (snd (snd (snd (mt_state d))))
                        \<in> {VFwd, VFwdPad, VRet}"
      using Suc.prems(3) by blast
  qed
  show ?case by (rule Suc.IH[OF rest1 rest2' inv'])
qed


end
