theory AlphabetEnlargement_Uniqueness
  imports AlphabetEnlargement_Simulation
begin

subsection \<open>Identities between the block predicates\<close>

text \<open>Identities relating \<open>is_pure_block\<close>,
  \<open>is_padded_block\<close>, \<open>LE_block\<close>, and \<open>bl_block\<close>.
  Used by the VFwd 6-fold pairwise exclusion lemmas below
  (and downstream by the reverse-direction trace decoder).\<close>

lemma is_pure_not_padded:
  fixes f :: "nat \<Rightarrow> 'a"
  assumes pure: "is_pure_block m bl f"
  shows "\<not> is_padded_block m bl f"
proof
  assume "is_padded_block m bl f"
  then obtain k where k_ub: "k < m"
      and suffix: "\<forall>x<m. k \<le> x \<longrightarrow> f x = bl"
    unfolding is_padded_block_def by auto
  from suffix k_ub have "f k = bl" by simp
  with pure k_ub show False unfolding is_pure_block_def by blast
qed

lemma not_is_pure_bl_block:
  "0 < m \<Longrightarrow> \<not> is_pure_block m (bl :: 'a) (bl_block m bl :: nat \<Rightarrow> 'a)"
  unfolding is_pure_block_def bl_block_def by auto

lemma not_is_padded_bl_block:
  "\<not> is_padded_block m (bl :: 'a) (bl_block m bl :: nat \<Rightarrow> 'a)"
proof
  assume "is_padded_block m bl (bl_block m bl :: nat \<Rightarrow> 'a)"
  then obtain k where k_lb: "1 \<le> k" and k_ub: "k < m"
      and prefix: "\<forall>x<m. x < k \<longrightarrow> (bl_block m bl :: nat \<Rightarrow> 'a) x \<noteq> bl"
    unfolding is_padded_block_def by auto
  from prefix k_lb k_ub have "(bl_block m bl :: nat \<Rightarrow> 'a) 0 \<noteq> bl"
    by simp
  with k_ub show False by (simp add: bl_block_def)
qed

lemma is_pure_LE_block:
  "(le :: 'a) \<noteq> bl \<Longrightarrow>
     is_pure_block m bl (LE_block m le :: nat \<Rightarrow> 'a)"
  unfolding is_pure_block_def LE_block_def by simp

lemma not_is_padded_LE_block:
  "(le :: 'a) \<noteq> bl \<Longrightarrow>
     \<not> is_padded_block m bl (LE_block m le :: nat \<Rightarrow> 'a)"
  using is_pure_LE_block is_pure_not_padded by metis

lemma LE_block_eq_bl_block_imp_eq:
  fixes le bl :: 'a
  assumes "(LE_block m le :: nat \<Rightarrow> 'a) = bl_block m bl"
      and "0 < m"
  shows "le = bl"
proof -
  from assms(1) have "(LE_block m le :: nat \<Rightarrow> 'a) 0 = bl_block m bl 0" by simp
  thus ?thesis using assms(2) unfolding LE_block_def bl_block_def by simp
qed

lemma LE_block_neq_bl_block:
  "0 < m \<Longrightarrow> (le :: 'a) \<noteq> bl \<Longrightarrow> (LE_block m le :: nat \<Rightarrow> 'a) \<noteq> bl_block m bl"
  using LE_block_eq_bl_block_imp_eq by metis

subsection \<open>The forward validation scan's transitions are disjoint\<close>

text \<open>The four VFwd-source relations (advance, \<open>to_padded\<close>,
  \<open>to_ret\<close>, reject) are pairwise disjoint under
  \<open>le_neq_bl\<close>.\<close>

lemma ae_delta_val_fwd_advance_to_padded_disjoint:
  fixes M :: "('q, 'a) ktm"
    and a :: "nat \<Rightarrow> nat \<Rightarrow> 'a"
  assumes "le_ktm M \<noteq> bl_ktm M"
      and "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_advance m M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_padded m M"
  shows "False"
proof -
  have alt: "a 0 = LE_block m (le_ktm M)
              \<or> is_pure_block m (bl_ktm M) (a 0)"
    using assms(2) unfolding ae_delta_val_fwd_advance_def by auto
  have padded: "is_padded_block m (bl_ktm M) (a 0)"
    using assms(3) unfolding ae_delta_val_fwd_to_padded_def by auto
  from alt show False
  proof
    assume "a 0 = LE_block m (le_ktm M)"
    thus False using padded assms(1) not_is_padded_LE_block by metis
  next
    assume "is_pure_block m (bl_ktm M) (a 0)"
    thus False using padded is_pure_not_padded by metis
  qed
qed

lemma ae_delta_val_fwd_advance_to_ret_disjoint:
  fixes M :: "('q, 'a) ktm"
    and a :: "nat \<Rightarrow> nat \<Rightarrow> 'a"
  assumes "le_ktm M \<noteq> bl_ktm M"
      and "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_advance m M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_ret m M"
      and m_pos: "0 < m"
  shows "False"
proof -
  have alt: "a 0 = LE_block m (le_ktm M)
              \<or> is_pure_block m (bl_ktm M) (a 0)"
    using assms(2) unfolding ae_delta_val_fwd_advance_def by auto
  have to_ret: "a 0 = bl_block m (bl_ktm M)"
    using assms(3) unfolding ae_delta_val_fwd_to_ret_def by auto
  from alt show False
  proof
    assume "a 0 = LE_block m (le_ktm M)"
    with to_ret have eq: "(LE_block m (le_ktm M) :: nat \<Rightarrow> 'a) = bl_block m (bl_ktm M)" by simp
    hence "le_ktm M = bl_ktm M" by (rule LE_block_eq_bl_block_imp_eq[OF _ m_pos])
    thus False using assms(1) by simp
  next
    assume "is_pure_block m (bl_ktm M) (a 0)"
    with to_ret have "is_pure_block m (bl_ktm M) (bl_block m (bl_ktm M) :: nat \<Rightarrow> 'a)" by simp
    thus False using not_is_pure_bl_block[OF m_pos, where bl="bl_ktm M"] by simp
  qed
qed

lemma ae_delta_val_fwd_advance_reject_disjoint:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_advance m M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_reject m M"
  shows "False"
  using assms
  unfolding ae_delta_val_fwd_advance_def ae_delta_val_fwd_reject_def
            is_canonical_block_def
  by auto

lemma ae_delta_val_fwd_to_padded_to_ret_disjoint:
  fixes M :: "('q, 'a) ktm"
    and a :: "nat \<Rightarrow> nat \<Rightarrow> 'a"
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_to_padded m M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_ret m M"
  shows "False"
proof -
  have padded: "is_padded_block m (bl_ktm M) (a 0)"
    using assms(1) unfolding ae_delta_val_fwd_to_padded_def by auto
  have to_ret: "a 0 = bl_block m (bl_ktm M)"
    using assms(2) unfolding ae_delta_val_fwd_to_ret_def by auto
  from padded to_ret
    have "is_padded_block m (bl_ktm M) (bl_block m (bl_ktm M) :: nat \<Rightarrow> 'a)" by simp
  thus False using not_is_padded_bl_block[where bl="bl_ktm M"] by simp
qed

lemma ae_delta_val_fwd_to_padded_reject_disjoint:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_to_padded m M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_reject m M"
  shows "False"
  using assms
  unfolding ae_delta_val_fwd_to_padded_def ae_delta_val_fwd_reject_def
            is_canonical_block_def
  by auto

lemma ae_delta_val_fwd_to_ret_reject_disjoint:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_to_ret m M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_reject m M"
  shows "False"
  using assms
  unfolding ae_delta_val_fwd_to_ret_def ae_delta_val_fwd_reject_def
  by auto

text \<open>V-marker dispatch helpers: package the within-cluster
  multi-relation disjunction + pairwise disjointness + per-relation
  functionality into a single \<open>_functional\<close> lemma per V marker.
  Used by \<open>alphabet_enlarge_delta_functional\<close>'s V cases.\<close>

lemma ae_delta_VFwd_functional:
  fixes M :: "('q, 'a) ktm"
  assumes le_neq_bl: "le_ktm M \<noteq> bl_ktm M"
      and h1: "(s, a, s1, a1, d1) \<in> alphabet_enlarge_delta m M"
      and h2: "(s, a, s2, a2, d2) \<in> alphabet_enlarge_delta m M"
      and idx: "snd (snd (snd (snd s))) = VFwd"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
proof -
  have alt1: "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_advance m M
                \<or> (s, a, s1, a1, d1) \<in> ae_delta_val_fwd_to_padded m M
                \<or> (s, a, s1, a1, d1) \<in> ae_delta_val_fwd_reject m M
                \<or> (s, a, s1, a1, d1) \<in> ae_delta_val_fwd_to_ret m M"
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
  have alt2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_advance m M
                \<or> (s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_padded m M
                \<or> (s, a, s2, a2, d2) \<in> ae_delta_val_fwd_reject m M
                \<or> (s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_ret m M"
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
    assume A1: "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_advance m M"
    from alt2 show ?thesis
    proof (elim disjE)
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_advance m M"
      show ?thesis using ae_delta_val_fwd_advance_functional[OF A1 A2] by simp
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_padded m M"
      have False using ae_delta_val_fwd_advance_to_padded_disjoint[OF le_neq_bl A1 A2] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_reject m M"
      have False using ae_delta_val_fwd_advance_reject_disjoint[OF A1 A2] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_ret m M"
      have False using ae_delta_val_fwd_advance_to_ret_disjoint[OF le_neq_bl A1 A2
        alphabet_enlarge_delta_width_pos[OF h1]] .
      thus ?thesis ..
    qed
  next
    assume A1: "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_to_padded m M"
    from alt2 show ?thesis
    proof (elim disjE)
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_advance m M"
      have False using ae_delta_val_fwd_advance_to_padded_disjoint[OF le_neq_bl A2 A1] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_padded m M"
      show ?thesis using ae_delta_val_fwd_to_padded_functional[OF A1 A2] by simp
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_reject m M"
      have False using ae_delta_val_fwd_to_padded_reject_disjoint[OF A1 A2] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_ret m M"
      have False using ae_delta_val_fwd_to_padded_to_ret_disjoint[OF A1 A2] .
      thus ?thesis ..
    qed
  next
    assume A1: "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_reject m M"
    from alt2 show ?thesis
    proof (elim disjE)
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_advance m M"
      have False using ae_delta_val_fwd_advance_reject_disjoint[OF A2 A1] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_padded m M"
      have False using ae_delta_val_fwd_to_padded_reject_disjoint[OF A2 A1] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_reject m M"
      show ?thesis using ae_delta_val_fwd_reject_functional[OF A1 A2] by simp
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_ret m M"
      have False using ae_delta_val_fwd_to_ret_reject_disjoint[OF A2 A1] .
      thus ?thesis ..
    qed
  next
    assume A1: "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_to_ret m M"
    from alt2 show ?thesis
    proof (elim disjE)
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_advance m M"
      have False using ae_delta_val_fwd_advance_to_ret_disjoint[OF le_neq_bl A2 A1
        alphabet_enlarge_delta_width_pos[OF h1]] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_padded m M"
      have False using ae_delta_val_fwd_to_padded_to_ret_disjoint[OF A2 A1] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_reject m M"
      have False using ae_delta_val_fwd_to_ret_reject_disjoint[OF A1 A2] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_ret m M"
      show ?thesis using ae_delta_val_fwd_to_ret_functional[OF A1 A2] by simp
    qed
  qed
qed

lemma ae_delta_VRet_functional:
  fixes M :: "('q, 'a) ktm"
  assumes h1: "(s, a, s1, a1, d1) \<in> alphabet_enlarge_delta m M"
      and h2: "(s, a, s2, a2, d2) \<in> alphabet_enlarge_delta m M"
      and idx: "snd (snd (snd (snd s))) = VRet"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
proof -
  have alt1: "(s, a, s1, a1, d1) \<in> ae_delta_val_ret_step m M
                \<or> (s, a, s1, a1, d1) \<in> ae_delta_val_ret_to_sim m M"
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
  have alt2: "(s, a, s2, a2, d2) \<in> ae_delta_val_ret_step m M
                \<or> (s, a, s2, a2, d2) \<in> ae_delta_val_ret_to_sim m M"
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
    assume A1: "(s, a, s1, a1, d1) \<in> ae_delta_val_ret_step m M"
    from alt2 show ?thesis
    proof
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_ret_step m M"
      show ?thesis using ae_delta_val_ret_step_functional[OF A1 A2] by simp
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_ret_to_sim m M"
      have False using ae_delta_val_ret_step_ret_to_sim_disjoint[OF A1 A2] .
      thus ?thesis ..
    qed
  next
    assume A1: "(s, a, s1, a1, d1) \<in> ae_delta_val_ret_to_sim m M"
    from alt2 show ?thesis
    proof
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_ret_step m M"
      have False using ae_delta_val_ret_step_ret_to_sim_disjoint[OF A2 A1] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_ret_to_sim m M"
      show ?thesis using ae_delta_val_ret_to_sim_functional[OF A1 A2] by simp
    qed
  qed
qed

lemma ae_delta_VFwdPad_functional:
  fixes M :: "('q, 'a) ktm"
  assumes h1: "(s, a, s1, a1, d1) \<in> alphabet_enlarge_delta m M"
      and h2: "(s, a, s2, a2, d2) \<in> alphabet_enlarge_delta m M"
      and idx: "snd (snd (snd (snd s))) = VFwdPad"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
proof -
  have alt1: "(s, a, s1, a1, d1) \<in> ae_delta_val_pad_to_ret m M
                \<or> (s, a, s1, a1, d1) \<in> ae_delta_val_pad_reject m M"
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
  have alt2: "(s, a, s2, a2, d2) \<in> ae_delta_val_pad_to_ret m M
                \<or> (s, a, s2, a2, d2) \<in> ae_delta_val_pad_reject m M"
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
    assume A1: "(s, a, s1, a1, d1) \<in> ae_delta_val_pad_to_ret m M"
    from alt2 show ?thesis
    proof
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_pad_to_ret m M"
      show ?thesis using ae_delta_val_pad_to_ret_functional[OF A1 A2] by simp
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_pad_reject m M"
      have False using ae_delta_val_pad_to_ret_pad_reject_disjoint[OF A1 A2] .
      thus ?thesis ..
    qed
  next
    assume A1: "(s, a, s1, a1, d1) \<in> ae_delta_val_pad_reject m M"
    from alt2 show ?thesis
    proof
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_pad_to_ret m M"
      have False using ae_delta_val_pad_to_ret_pad_reject_disjoint[OF A2 A1] .
      thus ?thesis ..
    next
      assume A2: "(s, a, s2, a2, d2) \<in> ae_delta_val_pad_reject m M"
      show ?thesis using ae_delta_val_pad_reject_functional[OF A1 A2] by simp
    qed
  qed
qed


subsection \<open>Each step has at most one successor\<close>

text \<open>Under \<open>valid_ktm M\<close>, \<open>det_ktm M\<close>, and
  \<open>le_ktm M \<noteq> bl_ktm M\<close>, the alphabet-enlargement
  transition relation is functional in its source pair.  Proof
  case-splits on the source substep index: \<open>SSN\<close> cases dispatch
  via the matching \<open>ae_delta_ssN_only\<close> + \<open>*_functional\<close>
  pair; V-marker cases (\<open>VFwd\<close>, \<open>VFwdPad\<close>, \<open>VRet\<close>) use
  within-cluster disjointness to collapse the multi-relation
  alternative, then apply the surviving sub-relation's functionality
  lemma.\<close>

lemma alphabet_enlarge_delta_functional:
  fixes M :: "('q, 'a) ktm"
  assumes vM:  "valid_ktm M"
      and det: "det_ktm M"
      and le_neq_bl: "le_ktm M \<noteq> bl_ktm M"
      and h1: "(s, a, s1, a1, d1) \<in> alphabet_enlarge_delta m M"
      and h2: "(s, a, s2, a2, d2) \<in> alphabet_enlarge_delta m M"
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
  have e1: "(s, a, s1, a1, d1) \<in> ae_delta_ss1_ss2 m M"
    by (rule ae_delta_ss1_only[OF h1 SS1])
  have e2: "(s, a, s2, a2, d2) \<in> ae_delta_ss1_ss2 m M"
    by (rule ae_delta_ss1_only[OF h2 SS1])
  show ?thesis using ae_delta_ss1_ss2_functional[OF e1 e2] by simp
next
  case SS2
  have e1: "(s, a, s1, a1, d1) \<in> ae_delta_ss2_ss3 m M"
    by (rule ae_delta_ss2_only[OF h1 SS2])
  have e2: "(s, a, s2, a2, d2) \<in> ae_delta_ss2_ss3 m M"
    by (rule ae_delta_ss2_only[OF h2 SS2])
  show ?thesis using ae_delta_ss2_ss3_functional[OF e1 e2] by simp
next
  case SS3
  have e1: "(s, a, s1, a1, d1) \<in> ae_delta_ss3_ss4 m M"
    by (rule ae_delta_ss3_only[OF h1 SS3])
  have e2: "(s, a, s2, a2, d2) \<in> ae_delta_ss3_ss4 m M"
    by (rule ae_delta_ss3_only[OF h2 SS3])
  show ?thesis using ae_delta_ss3_ss4_functional[OF e1 e2] by simp
next
  case SS4
  have e1: "(s, a, s1, a1, d1) \<in> ae_delta_ss4_ss5 m M"
    by (rule ae_delta_ss4_only[OF h1 SS4])
  have e2: "(s, a, s2, a2, d2) \<in> ae_delta_ss4_ss5 m M"
    by (rule ae_delta_ss4_only[OF h2 SS4])
  show ?thesis using ae_delta_ss4_ss5_functional[OF vM det e1 e2] by simp
next
  case SS5
  have e1: "(s, a, s1, a1, d1) \<in> ae_delta_ss5_ss6 m M"
    by (rule ae_delta_ss5_only[OF h1 SS5])
  have e2: "(s, a, s2, a2, d2) \<in> ae_delta_ss5_ss6 m M"
    by (rule ae_delta_ss5_only[OF h2 SS5])
  show ?thesis using ae_delta_ss5_ss6_functional[OF e1 e2] by simp
next
  case SS6
  have e1: "(s, a, s1, a1, d1) \<in> ae_delta_ss6_ss7 m M"
    by (rule ae_delta_ss6_only[OF h1 SS6])
  have e2: "(s, a, s2, a2, d2) \<in> ae_delta_ss6_ss7 m M"
    by (rule ae_delta_ss6_only[OF h2 SS6])
  show ?thesis using ae_delta_ss6_ss7_functional[OF e1 e2] by simp
next
  case SS7
  have e1: "(s, a, s1, a1, d1) \<in> ae_delta_ss7_ss8 m M"
    by (rule ae_delta_ss7_only[OF h1 SS7])
  have e2: "(s, a, s2, a2, d2) \<in> ae_delta_ss7_ss8 m M"
    by (rule ae_delta_ss7_only[OF h2 SS7])
  show ?thesis using ae_delta_ss7_ss8_functional[OF e1 e2] by simp
next
  case SS8
  have e1: "(s, a, s1, a1, d1) \<in> ae_delta_ss8_ss1 m M"
    by (rule ae_delta_ss8_only[OF h1 SS8])
  have e2: "(s, a, s2, a2, d2) \<in> ae_delta_ss8_ss1 m M"
    by (rule ae_delta_ss8_only[OF h2 SS8])
  show ?thesis using ae_delta_ss8_ss1_functional[OF e1 e2] by simp
qed

text \<open>Lifting chain uniqueness from \<open>alphabet_enlarge_delta\<close>
  to \<open>ktm_step (alphabet_enlarge_delta M)\<close>: single-step then
  \<open>n\<close>-fold via standard induction.  Consumed in stage 6 to identify
  the forward direction's produced \<open>c'''\<close> with the reverse direction's
  given \<open>c''\<close>.\<close>

lemma ktm_step_alphabet_enlarge_functional:
  fixes M :: "('q, 'a) ktm"
  assumes vM:  "valid_ktm M"
      and det: "det_ktm M"
      and le_neq_bl: "le_ktm M \<noteq> bl_ktm M"
      and h1: "(c, c1) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and h2: "(c, c2) \<in> ktm_step (alphabet_enlarge_delta m M)"
  shows "c1 = c2"
proof -
  from h1 obtain q ts n q1 a1 dir1 where
      c_eq1:  "c  = KConfig q ts n"
    and c1_eq: "c1 = KConfig q1 (\<lambda>k. (ts k)(n k := a1 k))
                                  (\<lambda>k. go_move (dir1 k) (n k))"
    and tr1: "(q, \<lambda>k. ts k (n k), q1, a1, dir1)
                \<in> alphabet_enlarge_delta m M"
    by (auto elim: ktm_step.cases)
  from h2 obtain q' ts' n' q2 a2 dir2 where
      c_eq2:  "c  = KConfig q' ts' n'"
    and c2_eq: "c2 = KConfig q2 (\<lambda>k. (ts' k)(n' k := a2 k))
                                  (\<lambda>k. go_move (dir2 k) (n' k))"
    and tr2: "(q', \<lambda>k. ts' k (n' k), q2, a2, dir2)
                \<in> alphabet_enlarge_delta m M"
    by (auto elim: ktm_step.cases)
  from c_eq1 c_eq2
  have qq: "q = q'" and tsts: "ts = ts'" and nn: "n = n'"
    by auto
  from tr1 qq tsts nn
  have tr1': "(q, \<lambda>k. ts k (n k), q1, a1, dir1)
                \<in> alphabet_enlarge_delta m M" by simp
  from tr2 qq tsts nn
  have tr2': "(q, \<lambda>k. ts k (n k), q2, a2, dir2)
                \<in> alphabet_enlarge_delta m M" by simp
  have "q1 = q2 \<and> a1 = a2 \<and> dir1 = dir2"
    using alphabet_enlarge_delta_functional[OF vM det le_neq_bl tr1' tr2'] .
  thus ?thesis using c1_eq c2_eq tsts nn by simp
qed

lemma ktm_step_alphabet_enlarge_relpow_functional:
  fixes M :: "('q, 'a) ktm"
  assumes vM:  "valid_ktm M"
      and det: "det_ktm M"
      and le_neq_bl: "le_ktm M \<noteq> bl_ktm M"
      and h1: "(c, c1) \<in> ktm_step (alphabet_enlarge_delta m M) ^^ n"
      and h2: "(c, c2) \<in> ktm_step (alphabet_enlarge_delta m M) ^^ n"
  shows "c1 = c2"
  using h1 h2
proof (induction n arbitrary: c c1 c2)
  case 0
  thus ?case by simp
next
  case (Suc n)
  from Suc.prems(1) obtain c1' where
      step1: "(c, c1') \<in> ktm_step (alphabet_enlarge_delta m M)"
    and rest1: "(c1', c1) \<in> ktm_step (alphabet_enlarge_delta m M) ^^ n"
    by (meson relpow_Suc_D2)
  from Suc.prems(2) obtain c2' where
      step2: "(c, c2') \<in> ktm_step (alphabet_enlarge_delta m M)"
    and rest2: "(c2', c2) \<in> ktm_step (alphabet_enlarge_delta m M) ^^ n"
    by (meson relpow_Suc_D2)
  have c'_eq: "c1' = c2'"
    by (rule ktm_step_alphabet_enlarge_functional
              [OF vM det le_neq_bl step1 step2])
  show ?case using Suc.IH[OF rest1] rest2 c'_eq by simp
qed


text \<open>\<open>det\<close>-free chain uniqueness for the \<^emph>\<open>validation\<close>
  prefix.  \<open>alphabet_enlarge_delta\<close>'s only nondeterministic source is
  the SS4\<open>\<rightarrow>\<close>SS5 macro-step; every other stage marker dispatches to a
  functional substep builder.  In particular, from a validation marker
  (\<open>VFwd\<close> / \<open>VFwdPad\<close> / \<open>VRet\<close>) the transition is single-valued
  with no appeal to \<open>det_ktm M\<close> --- the det-free analogue of
  \<open>alphabet_enlarge_delta_functional\<close> restricted to validation
  sources.  Consumed by \<open>alphabet_enlarge_language\<close>'s reverse direction to
  identify the unique validation prefix from \<open>ae_init_config\<close> without
  the \<open>det\<close> hypothesis of Hopcroft--Ullman's speed-up theorems
  \<^cite>\<open>\<open>Theorems 12.3, 12.4\<close> in "Hopcroft1979:introduction"\<close>.\<close>

lemma alphabet_enlarge_delta_val_functional:
  fixes M :: "('q, 'a) ktm"
  assumes le_neq_bl: "le_ktm M \<noteq> bl_ktm M"
      and h1: "(s, a, s1, a1, d1) \<in> alphabet_enlarge_delta m M"
      and h2: "(s, a, s2, a2, d2) \<in> alphabet_enlarge_delta m M"
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

lemma ktm_step_alphabet_enlarge_val_functional:
  fixes M :: "('q, 'a) ktm"
  assumes le_neq_bl: "le_ktm M \<noteq> bl_ktm M"
      and h1: "(c, c1) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and h2: "(c, c2) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and idx: "snd (snd (snd (snd (ktc_state c)))) \<in> {VFwd, VFwdPad, VRet}"
  shows "c1 = c2"
proof -
  from h1 obtain q ts n q1 a1 dir1 where
      c_eq1:  "c  = KConfig q ts n"
    and c1_eq: "c1 = KConfig q1 (\<lambda>k. (ts k)(n k := a1 k))
                                  (\<lambda>k. go_move (dir1 k) (n k))"
    and tr1: "(q, \<lambda>k. ts k (n k), q1, a1, dir1) \<in> alphabet_enlarge_delta m M"
    by (auto elim: ktm_step.cases)
  from h2 obtain q' ts' n' q2 a2 dir2 where
      c_eq2:  "c  = KConfig q' ts' n'"
    and c2_eq: "c2 = KConfig q2 (\<lambda>k. (ts' k)(n' k := a2 k))
                                  (\<lambda>k. go_move (dir2 k) (n' k))"
    and tr2: "(q', \<lambda>k. ts' k (n' k), q2, a2, dir2) \<in> alphabet_enlarge_delta m M"
    by (auto elim: ktm_step.cases)
  from c_eq1 c_eq2 have qq: "q = q'" and tsts: "ts = ts'" and nn: "n = n'"
    by auto
  from tr2 qq tsts nn
  have tr2': "(q, \<lambda>k. ts k (n k), q2, a2, dir2) \<in> alphabet_enlarge_delta m M"
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

lemma ktm_step_alphabet_enlarge_val_relpow_functional:
  fixes M :: "('q, 'a) ktm"
  assumes le_neq_bl: "le_ktm M \<noteq> bl_ktm M"
      and h1: "(c, c1) \<in> ktm_step (alphabet_enlarge_delta m M) ^^ n"
      and h2: "(c, c2) \<in> ktm_step (alphabet_enlarge_delta m M) ^^ n"
      and inv: "\<forall>i<n. \<forall>d. (c, d) \<in> ktm_step (alphabet_enlarge_delta m M) ^^ i
                    \<longrightarrow> snd (snd (snd (snd (ktc_state d))))
                          \<in> {VFwd, VFwdPad, VRet}"
  shows "c1 = c2"
  using h1 h2 inv
proof (induction n arbitrary: c c1 c2)
  case 0
  thus ?case by simp
next
  case (Suc n)
  from Suc.prems(1) obtain c1' where
      step1: "(c, c1') \<in> ktm_step (alphabet_enlarge_delta m M)"
    and rest1: "(c1', c1) \<in> ktm_step (alphabet_enlarge_delta m M) ^^ n"
    by (meson relpow_Suc_D2)
  from Suc.prems(2) obtain c2' where
      step2: "(c, c2') \<in> ktm_step (alphabet_enlarge_delta m M)"
    and rest2: "(c2', c2) \<in> ktm_step (alphabet_enlarge_delta m M) ^^ n"
    by (meson relpow_Suc_D2)
  have c_val: "snd (snd (snd (snd (ktc_state c)))) \<in> {VFwd, VFwdPad, VRet}"
  proof -
    have a: "(c, c) \<in> ktm_step (alphabet_enlarge_delta m M) ^^ 0" by simp
    have b: "(0::nat) < Suc n" by simp
    show ?thesis using Suc.prems(3) a b by blast
  qed
  have c'_eq: "c1' = c2'"
    by (rule ktm_step_alphabet_enlarge_val_functional
                [OF le_neq_bl step1 step2 c_val])
  have rest2': "(c1', c2) \<in> ktm_step (alphabet_enlarge_delta m M) ^^ n"
    using rest2 c'_eq by simp
  have inv':
      "\<forall>i<n. \<forall>d. (c1', d) \<in> ktm_step (alphabet_enlarge_delta m M) ^^ i
                    \<longrightarrow> snd (snd (snd (snd (ktc_state d))))
                          \<in> {VFwd, VFwdPad, VRet}"
  proof (intro allI impI)
    fix i d
    assume i_lt: "i < n"
      and reach: "(c1', d) \<in> ktm_step (alphabet_enlarge_delta m M) ^^ i"
    have "(c, d) \<in> ktm_step (alphabet_enlarge_delta m M) ^^ Suc i"
      by (rule relpow_Suc_I2[OF step1 reach])
    moreover have "Suc i < Suc n" using i_lt by simp
    ultimately show "snd (snd (snd (snd (ktc_state d))))
                        \<in> {VFwd, VFwdPad, VRet}"
      using Suc.prems(3) by blast
  qed
  show ?case by (rule Suc.IH[OF rest1 rest2' inv'])
qed


end
