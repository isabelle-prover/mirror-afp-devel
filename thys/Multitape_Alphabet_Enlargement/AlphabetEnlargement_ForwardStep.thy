theory AlphabetEnlargement_ForwardStep
  imports AlphabetEnlargement_ForwardCells
begin

subsection \<open>Forward-stage SS5--SS8 super-step\<close>

text \<open>The middle link of the forward-stage chain
  \<open>ForwardCells \<rightarrow> ForwardStep \<rightarrow> ForwardStage\<close>: the
  SS5\<open>\<rightarrow>\<close>SS8 substep chain of
  \<open>ae_simulates_forward_stage_general\<close>.  From the SS5-entry config
  \<open>c4\<close> (its invariant \<open>ae_inv_ss5\<close>, the
  \<open>\<gamma>\<close>-block and buffer side-bands, and the per-tape
  regime data) it runs the four substeps \<open>ae_delta_ss5_ss6\<close>,
  \<open>ae_delta_ss6_ss7\<close>, \<open>ae_delta_ss7_ss8\<close>,
  \<open>ae_delta_ss8_ss1\<close>, exposing the intermediate configs
  \<open>c5\<close>, \<open>c6\<close>, \<open>c7\<close>, \<open>c8\<close>, their shared
  SS-stage state tuple \<open>(q5, ofs5, buf5, dest5)\<close> =
  \<open>(q6, ofs6, buf6, dest6)\<close>, and the per-tape position and
  tape-content facts the reconstruction leaves
  (\<open>AlphabetEnlargement_ForwardCells\<close>) consume.
  Carved out of \<open>ae_simulates_forward_stage_general\<close> as its
  widest single seam (17 assumptions, 29 conclusions); the call site
  re-binds the named facts verbatim.\<close>
lemma ae_forward_stage_step_chain:
  fixes M :: "('q, 'a) mttm"
    and cM :: "('a, 'q) mt_config"
    and c' c1 c2 c3 c4 :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) mt_config"
  assumes vM:        "valid_mttm M"
      and le_anchor:
      "\<forall>k<k_tm M. mt_tape c' k 0 = LE_block (le_tm M)"
      and no_le_per_tape:
      "\<forall>k. (mt_pos c' k \<ge> 2
      \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
      \<longrightarrow> mt_tape cM k
      ((mt_pos c' k - 2) * card (UNIV :: 'c set) + 1 + i)
      \<noteq> le_tm M))
      \<and> (mt_pos c' k = 1
      \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
      \<longrightarrow> mt_tape cM k (Suc i) \<noteq> le_tm M))
      \<and> (mt_pos c' k = 0
      \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
      \<longrightarrow> mt_tape cM k (Suc i) \<noteq> le_tm M))"
      and tape_corr: "\<forall>k<k_tm M. ae_tape_correspondence (le_tm M)
      (mt_tape cM k) (mt_tape c' k)"
      and step1_sub: "(c', c1) \<in> mttm_step (ae_delta_ss1_ss2 M)"
      and step2_sub: "(c1, c2) \<in> mttm_step (ae_delta_ss2_ss3 M)"
      and step3_sub: "(c2, c3) \<in> mttm_step (ae_delta_ss3_ss4 M)"
      and c_ge_1: "1 \<le> card (UNIV :: 'c set)"
      and c_eq_len: "card (UNIV :: 'c set) = length (enum_class.enum :: 'c list)"
      and home_classification:
      "\<forall>k<k_tm M. (mt_pos c' k = 0
      \<longrightarrow> mt_tape c' k (mt_pos c' k) = LE_block (le_tm M))
      \<and> (mt_pos c' k \<ge> 1
      \<longrightarrow> mt_tape c' k (mt_pos c' k) \<noteq> LE_block (le_tm M))"
      and c3_pos: "\<And>k. k < k_tm M \<Longrightarrow> mt_pos c3 k = mt_pos c' k + 1"
      and bl_neq_le:
      "(bl_block (bl_tm M) :: 'c \<Rightarrow> 'a) \<noteq> LE_block (le_tm M)"
      and step4_sub: "(c3, c4) \<in> mttm_step (ae_delta_ss4_ss5 M)"
      and c4_buf_not_le_per_tape:
      "case mt_state c4 of (_, _, b, _, _) \<Rightarrow>
      \<forall>kk<k_tm M. (mt_pos c' kk = 0
      \<longrightarrow> fst (b kk) \<noteq> LE_block (le_tm M)
      \<and> snd (snd (b kk)) \<noteq> LE_block (le_tm M))
      \<and> (mt_pos c' kk = 1
      \<longrightarrow> fst (snd (b kk)) \<noteq> LE_block (le_tm M)
      \<and> snd (snd (b kk)) \<noteq> LE_block (le_tm M))
      \<and> (mt_pos c' kk \<ge> 2
      \<longrightarrow> fst (b kk) \<noteq> LE_block (le_tm M)
      \<and> fst (snd (b kk)) \<noteq> LE_block (le_tm M)
      \<and> snd (snd (b kk)) \<noteq> LE_block (le_tm M))"
      and inv_ss5: "ae_inv_ss5 M c4"
      and gamma_c4: "ae_tape_in_gamma_block M c4"
      and buf_gamma_c4: "ae_buffer_in_gamma_block M c4"
  obtains c5 q5 ofs5 buf5 dest5 c6 c7 q6 ofs6 buf6 dest6 c8
    where "(c4, c5) \<in> mttm_step (ae_delta_ss5_ss6 M)"
      and "(c4, c5) \<in> mttm_step (alphabet_enlarge_delta M)"
      and "mt_state c4 = (q5, ofs5, buf5, dest5, SS5)"
      and "mt_state c5 = (q5, ofs5, buf5, dest5, SS6)"
      and "mt_tape c4 = mt_tape c'"
      and
      "\<forall>k<k_tm M. (mt_pos c' k = 0
      \<longrightarrow> fst (buf5 k) \<noteq> LE_block (le_tm M)
      \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))
      \<and> (mt_pos c' k = 1
      \<longrightarrow> fst (snd (buf5 k)) \<noteq> LE_block (le_tm M)
      \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))
      \<and> (mt_pos c' k \<ge> 2
      \<longrightarrow> fst (buf5 k) \<noteq> LE_block (le_tm M)
      \<and> fst (snd (buf5 k)) \<noteq> LE_block (le_tm M)
      \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))"
      and
      "\<forall>k. mt_tape c' k (mt_pos c' k + 1) \<noteq> LE_block (le_tm M)"
      and "\<forall>kk. kk < k_tm M \<longrightarrow> mt_pos c4 kk = mt_pos c' kk"
      and "\<forall>k<k_tm M. mt_tape c5 k 0 = LE_block (le_tm M)"
      and
      "\<forall>kk. kk < k_tm M \<longrightarrow> mt_pos c' kk = 1 \<longrightarrow> dest5 kk \<noteq> AE_Left
      \<longrightarrow> mt_pos c5 kk = 0"
      and "(c5, c6) \<in> mttm_step (ae_delta_ss6_ss7 M)"
      and "(c5, c6) \<in> mttm_step (alphabet_enlarge_delta M)"
      and "(c6, c7) \<in> mttm_step (ae_delta_ss7_ss8 M)"
      and "(c6, c7) \<in> mttm_step (alphabet_enlarge_delta M)"
      and "ae_tape_in_gamma_block M c7"
      and "ae_buffer_in_gamma_block M c7"
      and "mt_state c6 = (q6, ofs6, buf6, dest6, SS7)"
      and "mt_state c7 = (q6, ofs6, buf6, dest6, SS8)"
      and "buf6 = buf5"
      and "q6 = q5"
      and "ofs6 = ofs5"
      and "dest6 = dest5"
      and
      "\<forall>kk. kk < k_tm M \<longrightarrow> mt_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
      \<longrightarrow> mt_pos c5 kk = 2"
      and
      "\<forall>kk. kk < k_tm M \<longrightarrow> mt_pos c' kk = 1
      \<longrightarrow> mt_tape c5 kk 1 = fst (snd (buf5 kk))"
      and
      "\<forall>kk. kk < k_tm M \<longrightarrow> mt_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
      \<longrightarrow> mt_pos c6 kk = 1"
      and
      "\<forall>kk. kk < k_tm M \<longrightarrow> mt_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
      \<longrightarrow> mt_pos c7 kk = 0"
      and
      "\<forall>kk. kk < k_tm M \<longrightarrow> mt_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
      \<longrightarrow> mt_tape c7 kk 0 = LE_block (le_tm M)"
      and "(c7, c8) \<in> mttm_step (ae_delta_ss8_ss1 M)"
      and "(c7, c8) \<in> mttm_step (alphabet_enlarge_delta M)"
proof -
  obtain c5 where
      step5_sub: "(c4, c5) \<in> mttm_step (ae_delta_ss5_ss6 M)"
    and step5: "(c4, c5) \<in> mttm_step (alphabet_enlarge_delta M)"
    using ae_step_ss5_ss6_exists[OF inv_ss5 gamma_c4 buf_gamma_c4] by blast
  have inv_ss6: "ae_inv_ss6 M c5"
    using ae_step_ss5_ss6_invariant[OF vM inv_ss5 step5_sub] .
  have gamma_c5: "ae_tape_in_gamma_block M c5"
    using ae_step_alphabet_enlarge_gamma_preserve[OF gamma_c4 step5] .
  have buf_gamma_c5: "ae_buffer_in_gamma_block M c5"
    using ae_step_alphabet_enlarge_buffer_gamma_preserve[OF vM buf_gamma_c4
                                                            gamma_c4 step5] .

  \<comment> \<open>State shapes at \<open>c4\<close> (idx SS5) and \<open>c5\<close> (idx SS6).
      Identical derivation across regimes; the substep preserves
      \<open>(q, ofs, buf, dest)\<close> and flips only the stage index.\<close>
  obtain q5 ofs5 buf5 dest5 where
      c4_state: "mt_state c4 = (q5, ofs5, buf5, dest5, SS5)"
    using inv_ss5 unfolding ae_inv_ss5_def
    by (cases "mt_state c4") auto
  have c5_state: "mt_state c5 = (q5, ofs5, buf5, dest5, SS6)"
    using step5_sub c4_state
    by (auto simp: ae_delta_ss5_ss6_def elim: mttm_step.cases)

  \<comment> \<open>Sub-step 5b: M'-tape preservation through SS1\<open>\<rightarrow>\<close>SS2 \<open>\<rightarrow>\<close>
      \<open>\<dots>\<close> \<open>\<rightarrow>\<close>SS5.  Each sub-delta has \<open>a' = a\<close> (idempotent
      on \<open>M'\<close>-tape), so the cumulative tape is unchanged through
      \<open>c1\<close>\<open>\<dots>\<close>\<open>c4\<close>.  Uniform across regimes.\<close>
  have nw_12: "\<And>q a q' a' d.
                  (q, a, q', a', d) \<in> ae_delta_ss1_ss2 M \<Longrightarrow> a' = a"
    by (auto simp: ae_delta_ss1_ss2_def)
  have nw_23: "\<And>q a q' a' d.
                  (q, a, q', a', d) \<in> ae_delta_ss2_ss3 M \<Longrightarrow> a' = a"
    by (auto simp: ae_delta_ss2_ss3_def)
  have nw_34: "\<And>q a q' a' d.
                  (q, a, q', a', d) \<in> ae_delta_ss3_ss4 M \<Longrightarrow> a' = a"
    by (auto simp: ae_delta_ss3_ss4_def)
  have nw_45: "\<And>q a q' a' d.
                  (q, a, q', a', d) \<in> ae_delta_ss4_ss5 M \<Longrightarrow> a' = a"
    by (auto simp: ae_delta_ss4_ss5_def)
  have tape_c1_eq: "mt_tape c1 = mt_tape c'"
    using mttm_step_no_write_tape[OF step1_sub nw_12] .
  have tape_c2_eq: "mt_tape c2 = mt_tape c1"
    using mttm_step_no_write_tape[OF step2_sub nw_23] .
  have tape_c3_eq: "mt_tape c3 = mt_tape c2"
    using mttm_step_no_write_tape[OF step3_sub nw_34] .
  have tape_c4_eq: "mt_tape c4 = mt_tape c3"
    using mttm_step_no_write_tape[OF step4_sub nw_45] .
  have tape_c4_eq_c': "mt_tape c4 = mt_tape c'"
    using tape_c1_eq tape_c2_eq tape_c3_eq tape_c4_eq by simp

  \<comment> \<open>Buf5 per-tape regime-aware non-LE shape, transferred from
      \<open>c4_buf_not_le_per_tape\<close> via \<open>c4_state\<close>.  Pos=0 tapes have
      left+right non-LE; pos=1 tapes have home+right non-LE; pos\<open>\<ge>\<close>2
      tapes have all three non-LE.  This is the regime-aware
      generalisation of \<open>buf5_not_le_lr\<close> (le0) and \<open>buf5_not_le_hr\<close>
      (le1) and the steady-state full \<open>buf5_not_le\<close>.\<close>
  have buf5_not_le_per_tape:
      "\<forall>k<k_tm M. (mt_pos c' k = 0
             \<longrightarrow> fst (buf5 k) \<noteq> LE_block (le_tm M)
                \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))
           \<and> (mt_pos c' k = 1
                \<longrightarrow> fst (snd (buf5 k)) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))
           \<and> (mt_pos c' k \<ge> 2
                \<longrightarrow> fst (buf5 k) \<noteq> LE_block (le_tm M)
                  \<and> fst (snd (buf5 k)) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))"
    using c4_buf_not_le_per_tape c4_state by simp

  \<comment> \<open>Sub-step 5c: \<open>right_not_le_c'\<close>.  The unified "right-of-home
      not LE" fact at \<open>c'\<close>: for every tape, the block at
      \<open>mt_pos c' k + 1\<close> is not \<open>LE_block\<close>.  Powers the SS4\<open>\<rightarrow>\<close>SS5
      head-trajectory derivation (\<open>c3\<close> reads at \<open>mt_pos c3 = mt_pos c' + 1\<close>,
      direction \<open>L\<close> when read \<open>\<noteq> LE\<close>).  Per-tape case-split on regime:
      pos=0 uses \<open>no_le\<close> i=0 (cell 1); pos=1 uses \<open>no_le\<close> i=c (cell c+1);
      pos\<open>\<ge>\<close>2 uses \<open>no_le\<close> i=2c (cell pos\<open>\<cdot>\<close>c+1).  All three cell
      indices coincide with the correspondence-derived address
      \<open>mt_pos c' k \<cdot> c + 1\<close>.\<close>
  have right_not_le_c':
      "\<forall>k. mt_tape c' k (mt_pos c' k + 1) \<noteq> LE_block (le_tm M)"
  proof (intro allI)
    fix k :: nat
    show "mt_tape c' k (mt_pos c' k + 1) \<noteq> LE_block (le_tm M)"
    proof (cases "k < k_tm M")
      case True
    let ?x = "(enum_class.enum :: 'c list) ! 0"
    let ?c = "card (UNIV :: 'c set)"
    have zero_lt_len: "0 < length (enum_class.enum :: 'c list)"
      using c_ge_1 c_eq_len by linarith
    have x_idx0: "c_idx ?x = 0"
      using c_idx_enum_nth[OF zero_lt_len] .
    have tc_k: "ae_tape_correspondence (le_tm M) (mt_tape cM k) (mt_tape c' k)"
      using tape_corr[rule_format, OF True] .
    have addr_via_tc:
        "mt_tape cM k (mt_pos c' k * ?c + 1)
          = mt_tape c' k (mt_pos c' k + 1) ?x"
    proof -
      from tc_k have unf:
          "\<forall>s\<ge>1. \<forall>i. mt_tape cM k ((s - 1) * ?c + c_idx i + 1)
                      = mt_tape c' k s i"
        unfolding ae_tape_correspondence_def by simp
      have s_ge1: "mt_pos c' k + 1 \<ge> 1" by simp
      from unf s_ge1 have eq:
          "mt_tape cM k ((mt_pos c' k + 1 - 1) * ?c + c_idx ?x + 1)
            = mt_tape c' k (mt_pos c' k + 1) ?x"
        by blast
      thus ?thesis using x_idx0 by simp
    qed
    consider (le0) "mt_pos c' k = 0"
           | (le1) "mt_pos c' k = 1"
           | (steady) "mt_pos c' k \<ge> 2"
      by linarith
    hence "mt_tape c' k (mt_pos c' k + 1) ?x \<noteq> le_tm M"
    proof cases
      case le0
      have idx_lt: "(0 :: nat) < ?c" using c_ge_1 by simp
      have nle: "mt_tape cM k (Suc 0) \<noteq> le_tm M"
        using no_le_per_tape le0 idx_lt by blast
      thus ?thesis using addr_via_tc le0 by simp
    next
      case le1
      have idx_lt: "?c < 2 * ?c" using c_ge_1 by simp
      have nle: "mt_tape cM k (Suc ?c) \<noteq> le_tm M"
        using no_le_per_tape le1 idx_lt by blast
      hence "mt_tape cM k (1 * ?c + 1) \<noteq> le_tm M" by simp
      thus ?thesis using addr_via_tc le1 by simp
    next
      case steady
      have idx_lt: "2 * ?c < 3 * ?c" using c_ge_1 by simp
      have addr_eq:
          "(mt_pos c' k - 2) * ?c + 1 + 2 * ?c = mt_pos c' k * ?c + 1"
        using steady by (simp add: algebra_simps diff_mult_distrib)
      have nle: "mt_tape cM k ((mt_pos c' k - 2) * ?c + 1 + 2 * ?c) \<noteq> le_tm M"
        using no_le_per_tape steady idx_lt by blast
      thus ?thesis using addr_via_tc addr_eq by simp
    qed
    thus "mt_tape c' k (mt_pos c' k + 1) \<noteq> LE_block (le_tm M)"
      unfolding LE_block_def by auto
    next
      case False
      hence kge: "k_tm M \<le> k" by simp
      have "mt_tape c' k (mt_pos c' k + 1) = bl_block (bl_tm M)"
        using gamma_c4 kge
        unfolding ae_tape_in_gamma_block_def tape_c4_eq_c'[symmetric]
        by simp
      thus ?thesis using bl_neq_le by simp
    qed
  qed

  \<comment> \<open>Sub-step 5d: SS4\<open>\<rightarrow>\<close>SS5 head trajectory.  At \<open>c3\<close>'s head
      position \<open>mt_pos c3 k = mt_pos c' k + 1\<close>, the M'-tape reads
      \<open>mt_tape c' k (mt_pos c' k + 1)\<close> (via \<open>tape_c3_eq_c'\<close>) which
      is not \<open>LE_block\<close> by \<open>right_not_le_c'\<close>.  Hence
      \<open>ae_delta_ss4_ss5\<close>'s direction is \<open>L\<close>, landing \<open>c4\<close>'s head
      at \<open>mt_pos c' k\<close>.  Uniform across regimes: pos=0 lands at 0,
      pos=1 lands at 1, pos\<open>\<ge>\<close>2 lands at pos.\<close>
  have tape_c3_eq_c': "mt_tape c3 = mt_tape c'"
    using tape_c1_eq tape_c2_eq tape_c3_eq by simp
  have c4_pos: "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c4 kk = mt_pos c' kk"
  proof -
    fix kk assume kklt: "kk < k_tm M"
    obtain qq tts nn qq' aa4 dr4 where
        c3_eq4: "c3 = Config\<^sub>M qq tts nn"
      and c4_eq: "c4 = Config\<^sub>M qq'
                          (\<lambda>k. (tts k)(nn k := aa4 k))
                          (\<lambda>k. go_dir (dr4 k) (nn k))"
      and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa4, dr4)
                    \<in> ae_delta_ss4_ss5 M"
      using step4_sub by (auto elim: mttm_step.cases)
    have dr4_eq:
        "dr4 = (\<lambda>k. if k < k_tm M
                     then (if tts k (nn k) = LE_block (le_tm M)
                           then dir.N else dir.L)
                     else dir.N)"
      using tr_in by (auto simp: ae_delta_ss4_ss5_def)
    have nn_kk: "nn kk = mt_pos c3 kk" using c3_eq4 by simp
    have tts_kk: "tts kk (nn kk) = mt_tape c3 kk (mt_pos c3 kk)"
      using c3_eq4 nn_kk by simp
    have c3_kk: "mt_pos c3 kk = mt_pos c' kk + 1"
      using c3_pos kklt by simp
    have read_at_c3:
        "tts kk (nn kk) = mt_tape c' kk (mt_pos c' kk + 1)"
      using tts_kk c3_kk tape_c3_eq_c' by simp
    have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      using read_at_c3 right_not_le_c' by simp
    have dr4_L: "dr4 kk = dir.L"
      using dr4_eq read_ne_LE kklt by simp
    have "mt_pos c4 kk = go_dir (dr4 kk) (nn kk)" using c4_eq by simp
    also have "\<dots> = (nn kk) - 1" using dr4_L by simp
    also have "\<dots> = (mt_pos c3 kk) - 1" using nn_kk by simp
    also have "\<dots> = (mt_pos c' kk + 1) - 1" using c3_kk by simp
    also have "\<dots> = mt_pos c' kk" by simp
    finally show "mt_pos c4 kk = mt_pos c' kk" .
  qed

  \<comment> \<open>Sub-step 5e: \<open>tape_c5_zero_le\<close>.  The M'-tape cell 0 stays
      \<open>LE_block\<close> across SS5.  For pos\<open>\<ge>\<close>1 tapes \<open>c4_pos \<noteq> 0\<close>, so
      cell 0 is off-head and preserved from \<open>c4\<close> (which equals \<open>c'\<close>
      by \<open>tape_c4_eq_c'\<close>, hence \<open>LE_block\<close> by \<open>le_anchor\<close>).  For pos=0
      tapes \<open>c4_pos = 0\<close>, so the SS5 action fires at cell 0; but the
      LE-guard fires (read = \<open>LE_block\<close> via \<open>le_anchor\<close>) and
      idempotently writes \<open>LE_block\<close> back.  Either way cell 0 stays.\<close>
  have tape_c5_zero_le: "\<forall>k<k_tm M. mt_tape c5 k 0 = LE_block (le_tm M)"
  proof (intro allI impI)
    fix k assume klt: "k < k_tm M"
    consider (le0) "mt_pos c' k = 0" | (rest) "mt_pos c' k \<ge> 1" by linarith
    thus "mt_tape c5 k 0 = LE_block (le_tm M)"
    proof cases
      case rest
      have c4_kk_ne0: "mt_pos c4 k \<noteq> 0"
        using c4_pos[OF klt] rest by simp
      have zero_ne_pos: "(0 :: nat) \<noteq> mt_pos c4 k" using c4_kk_ne0 by simp
      have c5_zero_eq_c4: "mt_tape c5 k 0 = mt_tape c4 k 0"
        using mttm_step_tape_off_head[OF step5 zero_ne_pos] .
      have "mt_tape c4 k 0 = mt_tape c' k 0"
        using tape_c4_eq_c' by simp
      also have "\<dots> = LE_block (le_tm M)"
        using le_anchor[rule_format, OF klt] by simp
      finally show ?thesis using c5_zero_eq_c4 by simp
    next
      case le0
      have c4_pos_kk: "mt_pos c4 k = 0"
        using c4_pos[OF klt] le0 by simp
      obtain qq tts nn qq' aa5 dr5 where
          c4_eq5: "c4 = Config\<^sub>M qq tts nn"
        and c5_eq: "c5 = Config\<^sub>M qq'
                            (\<lambda>k. (tts k)(nn k := aa5 k))
                            (\<lambda>k. go_dir (dr5 k) (nn k))"
        and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa5, dr5)
                      \<in> ae_delta_ss5_ss6 M"
        using step5_sub by (auto elim: mttm_step.cases)
      obtain q ofs buf dest where
          qq_eq: "qq = (q, ofs, buf, dest, SS5)"
        and aa5_eq: "aa5 = (\<lambda>k. if k < k_tm M
                                  then fst (ae_ss5_action (le_tm M)
                                             (tts k (nn k)) (buf k) (dest k))
                                  else bl_block (bl_tm M))"
        using tr_in by (auto simp: ae_delta_ss5_ss6_def)
      have nn_kk: "nn k = mt_pos c4 k" using c4_eq5 by simp
      have nn_kk_0: "nn k = 0" using nn_kk c4_pos_kk by simp
      have tts_kk: "tts k (nn k) = mt_tape c4 k (mt_pos c4 k)"
        using c4_eq5 nn_kk by simp
      have read_at: "tts k (nn k) = mt_tape c' k 0"
        using tts_kk c4_pos_kk tape_c4_eq_c' by simp
      have read_LE: "tts k (nn k) = LE_block (le_tm M)"
        using read_at le_anchor[rule_format, OF klt] by simp
      obtain l h r where buf_k: "buf k = (l, h, r)"
        by (cases "buf k") auto
      have aa5_LE: "aa5 k = LE_block (le_tm M)"
        using aa5_eq read_LE buf_k klt by simp
      have step_apply: "mt_tape c5 k 0 = ((tts k)(nn k := aa5 k)) 0"
        using c5_eq by simp
      have hit: "((tts k)(nn k := aa5 k)) 0 = aa5 k"
        using nn_kk_0 by simp
      show ?thesis using step_apply hit aa5_LE by simp
    qed
  qed

  \<comment> \<open>Sub-step 5f: head trajectory at SS5 for pos=1 tapes.  When
      the regime is pos=1 and \<open>dest5 k \<noteq> AE_Left\<close>, the SS5 action
      moves \<open>L\<close>, landing \<open>c5\<close>'s head at block 0 (the LE
      position).  Read at \<open>c4_pos = 1\<close> is \<open>mt_tape c' k 1 \<noteq> LE\<close>
      (via \<open>home_classification\<close> pos\<open>\<ge>\<close>1 branch); buf5 home \<open>\<noteq> LE\<close>
      (via \<open>buf5_not_le_per_tape\<close> pos=1 branch).  Neither LE-guard
      in \<open>ae_ss5_action\<close> fires; direction is \<open>L\<close> when
      \<open>dest \<noteq> AE_Left\<close>.\<close>
  have c5_pos_for_pos1:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1 \<Longrightarrow> dest5 kk \<noteq> AE_Left
            \<Longrightarrow> mt_pos c5 kk = 0"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume pos_kk: "mt_pos c' kk = 1"
    assume dest_ne: "dest5 kk \<noteq> AE_Left"
    obtain qq tts nn qq' aa5 dr5 where
        c4_eq5: "c4 = Config\<^sub>M qq tts nn"
      and c5_eq: "c5 = Config\<^sub>M qq'
                          (\<lambda>k. (tts k)(nn k := aa5 k))
                          (\<lambda>k. go_dir (dr5 k) (nn k))"
      and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa5, dr5)
                    \<in> ae_delta_ss5_ss6 M"
      using step5_sub by (auto elim: mttm_step.cases)
    obtain q ofs buf dest where
        qq_eq: "qq = (q, ofs, buf, dest, SS5)"
      and dr5_eq:
          "dr5 = (\<lambda>k. if k < k_tm M
                       then snd (ae_ss5_action (le_tm M)
                                  (tts k (nn k)) (buf k) (dest k))
                       else dir.N)"
      using tr_in by (auto simp: ae_delta_ss5_ss6_def)
    have qq_state: "qq = (q5, ofs5, buf5, dest5, SS5)"
      using c4_state c4_eq5 by simp
    have buf_eq: "buf = buf5" using qq_eq qq_state by simp
    have dest_eq: "dest = dest5" using qq_eq qq_state by simp
    have nn_kk: "nn kk = mt_pos c4 kk" using c4_eq5 by simp
    have c4_kk: "mt_pos c4 kk = 1" using c4_pos kklt pos_kk by simp
    have tts_kk: "tts kk (nn kk) = mt_tape c4 kk (mt_pos c4 kk)"
      using c4_eq5 nn_kk by simp
    have read_at_home:
        "tts kk (nn kk) = mt_tape c' kk 1"
      using tts_kk c4_kk tape_c4_eq_c' by simp
    have home_ne_LE: "mt_tape c' kk 1 \<noteq> LE_block (le_tm M)"
    proof -
      have pos_ge1: "(1 :: nat) \<le> mt_pos c' kk" using pos_kk by simp
      have "mt_tape c' kk (mt_pos c' kk) \<noteq> LE_block (le_tm M)"
        using home_classification[rule_format, OF kklt] pos_ge1 by blast
      thus ?thesis using pos_kk by simp
    qed
    have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      using read_at_home home_ne_LE by simp
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have h_ne_LE: "hh \<noteq> LE_block (le_tm M)"
    proof -
      have "fst (snd (buf5 kk)) \<noteq> LE_block (le_tm M)"
        using buf5_not_le_per_tape[rule_format, OF kklt] pos_kk by blast
      thus ?thesis using buf5_kk by simp
    qed
    have dr5_kk:
        "dr5 kk = (if dest5 kk = AE_Left then dir.R else dir.L)"
      using dr5_eq buf_eq dest_eq buf5_kk read_ne_LE h_ne_LE kklt by simp
    have dr5_kk_L: "dr5 kk = dir.L"
      using dr5_kk dest_ne by simp
    have "mt_pos c5 kk = go_dir (dr5 kk) (nn kk)"
      using c5_eq by simp
    also have "\<dots> = (nn kk) - 1" using dr5_kk_L by simp
    also have "\<dots> = mt_pos c4 kk - 1" using nn_kk by simp
    also have "\<dots> = 1 - 1" using c4_kk by simp
    also have "\<dots> = 0" by simp
    finally show "mt_pos c5 kk = 0" .
  qed

  \<comment> \<open>Sub-step 5g: \<open>pos_link_c5\<close>.  Discharges
      \<open>ae_position_link M c5\<close> from regime-aware buffer facts +
      head trajectory.  Two conjuncts at idx=SS6: right-slot non-LE
      (uniform, follows from each regime branch of
      \<open>buf5_not_le_per_tape\<close>) and the SS6 conditional
      (\<open>dest \<noteq> AE_Left\<close> + \<open>fst (buf k) = LE_block\<close> implies
      head reads \<open>LE_block\<close>).  The SS6 conditional case-splits
      per-tape: pos=0/\<open>\<ge>\<close>2 tapes have \<open>fst (buf5 k) \<noteq> LE_block\<close>
      so the antecedent is false (vacuous); pos=1 tapes use
      \<open>c5_pos_for_pos1\<close> + \<open>tape_c5_zero_le\<close> for the substantive
      case.\<close>
  have pos_link_c5: "ae_position_link M c5"
  proof -
    have r_not_le: "\<forall>k<k_tm M. snd (snd (buf5 k)) \<noteq> LE_block (le_tm M)"
    proof (intro allI impI)
      fix k
      assume klt: "k < k_tm M"
      consider (le0) "mt_pos c' k = 0"
             | (le1) "mt_pos c' k = 1"
             | (steady) "mt_pos c' k \<ge> 2"
        by linarith
      thus "snd (snd (buf5 k)) \<noteq> LE_block (le_tm M)"
      proof cases
        case le0    thus ?thesis using buf5_not_le_per_tape[rule_format, OF klt] by blast
      next
        case le1    thus ?thesis using buf5_not_le_per_tape[rule_format, OF klt] by blast
      next
        case steady thus ?thesis using buf5_not_le_per_tape[rule_format, OF klt] by blast
      qed
    qed
    have ss6_cond:
        "\<forall>k<k_tm M. dest5 k \<noteq> AE_Left
                \<longrightarrow> fst (buf5 k) = LE_block (le_tm M)
                \<longrightarrow> mt_tape c5 k (mt_pos c5 k) = LE_block (le_tm M)"
    proof (intro allI impI)
      fix k
      assume klt: "k < k_tm M"
      assume dest_ne: "dest5 k \<noteq> AE_Left"
      assume l_eq_le: "fst (buf5 k) = LE_block (le_tm M)"
      consider (le0) "mt_pos c' k = 0"
             | (le1) "mt_pos c' k = 1"
             | (steady) "mt_pos c' k \<ge> 2"
        by linarith
      thus "mt_tape c5 k (mt_pos c5 k) = LE_block (le_tm M)"
      proof cases
        case le0
        have "fst (buf5 k) \<noteq> LE_block (le_tm M)"
          using buf5_not_le_per_tape[rule_format, OF klt] le0 by blast
        thus ?thesis using l_eq_le by simp
      next
        case le1
        have c5_pos_zero: "mt_pos c5 k = 0"
          using c5_pos_for_pos1[OF klt le1 dest_ne] .
        have "mt_tape c5 k 0 = LE_block (le_tm M)"
          using tape_c5_zero_le[rule_format, OF klt] by simp
        thus ?thesis using c5_pos_zero by simp
      next
        case steady
        have "fst (buf5 k) \<noteq> LE_block (le_tm M)"
          using buf5_not_le_per_tape[rule_format, OF klt] steady by blast
        thus ?thesis using l_eq_le by simp
      qed
    qed
    show ?thesis
      unfolding ae_position_link_def
      using r_not_le ss6_cond c5_state by simp
  qed

  \<comment> \<open>Sub-step 5h: SS6\<open>\<rightarrow>\<close>SS7 invocation.  Discharge \<open>ae_le_compat_ss6\<close>
      from \<open>pos_link_c5\<close>; invoke \<open>ae_step_ss6_ss7_exists\<close>.  Propagate
      \<open>pos_link\<close> from \<open>c5\<close> (idx SS6) to \<open>c6\<close> via the arm-agnostic
      preservation lemma (the three aux conditionals are vacuous: idx-pre
      is SS6, not SS4/5/7).  Identical to the corresponding le0/le1 / steady
      blocks.\<close>
  have le_compat_ss6_c5: "ae_le_compat_ss6 M c5"
    using ae_position_link_discharges_ss6[OF inv_ss6 pos_link_c5] .
  obtain c6 where
      step6_sub: "(c5, c6) \<in> mttm_step (ae_delta_ss6_ss7 M)"
    and step6: "(c5, c6) \<in> mttm_step (alphabet_enlarge_delta M)"
    using ae_step_ss6_ss7_exists[OF inv_ss6 gamma_c5 buf_gamma_c5
                                    le_compat_ss6_c5] by blast
  have inv_ss7: "ae_inv_ss7 M c6"
    using ae_step_ss6_ss7_invariant[OF vM inv_ss6 step6_sub] .
  have gamma_c6: "ae_tape_in_gamma_block M c6"
    using ae_step_alphabet_enlarge_gamma_preserve[OF gamma_c5 step6] .
  have buf_gamma_c6: "ae_buffer_in_gamma_block M c6"
    using ae_step_alphabet_enlarge_buffer_gamma_preserve[OF vM buf_gamma_c5
                                                            gamma_c5 step6] .
  have c5_idx_ss6: "snd (snd (snd (snd (mt_state c5)))) = SS6"
    using c5_state by simp
  have aux_45_at_c5: "(c5, c6) \<in> mttm_step (ae_delta_ss4_ss5 M)
                        \<Longrightarrow> ae_position_link M c6"
    using ae_pos_link_aux_void_ss4_ss5[where M = M and c_pre = c5 and c_post = c6]
          c5_idx_ss6 by simp
  have aux_56_at_c5: "(c5, c6) \<in> mttm_step (ae_delta_ss5_ss6 M)
                        \<Longrightarrow> ae_position_link M c6"
    using ae_pos_link_aux_void_ss5_ss6[where M = M and c_pre = c5 and c_post = c6]
          c5_idx_ss6 by simp
  have aux_78_at_c5: "(c5, c6) \<in> mttm_step (ae_delta_ss7_ss8 M)
                        \<Longrightarrow> ae_position_link M c6"
    using ae_pos_link_aux_void_ss7_ss8[where M = M and c_pre = c5 and c_post = c6]
          c5_idx_ss6 by simp
  have pos_link_c6: "ae_position_link M c6"
    using ae_step_alphabet_enlarge_position_link_preserve[OF pos_link_c5
            step6 aux_45_at_c5 aux_56_at_c5 aux_78_at_c5] .

  \<comment> \<open>Sub-step 5i: SS7\<open>\<rightarrow>\<close>SS8 invocation.  Discharge \<open>ae_le_compat_ss7\<close>
      from \<open>pos_link_c6\<close>; invoke \<open>ae_step_ss7_ss8_exists\<close>.  Buffer
      content is preserved across SS5\<open>\<rightarrow>\<close>SS6\<open>\<rightarrow>\<close>SS7 (the substeps
      change only the tape and stage index, not the buffer component),
      so the \<open>buf5\<close> per-tape non-LE shape transfers to \<open>buf6 = buf5\<close>
      and \<open>c7\<close>'s state inherits the same buffer triple.\<close>
  have le_compat_ss7_c6: "ae_le_compat_ss7 M c6"
    using ae_position_link_discharges_ss7[OF inv_ss7 pos_link_c6] .
  obtain c7 where
      step7_sub: "(c6, c7) \<in> mttm_step (ae_delta_ss7_ss8 M)"
    and step7: "(c6, c7) \<in> mttm_step (alphabet_enlarge_delta M)"
    using ae_step_ss7_ss8_exists[OF inv_ss7 gamma_c6 buf_gamma_c6
                                    le_compat_ss7_c6] by blast
  have inv_ss8: "ae_inv_ss8 M c7"
    using ae_step_ss7_ss8_invariant[OF vM inv_ss7 step7_sub] .
  have gamma_c7: "ae_tape_in_gamma_block M c7"
    using ae_step_alphabet_enlarge_gamma_preserve[OF gamma_c6 step7] .
  have buf_gamma_c7: "ae_buffer_in_gamma_block M c7"
    using ae_step_alphabet_enlarge_buffer_gamma_preserve[OF vM buf_gamma_c6
                                                            gamma_c6 step7] .

  obtain q6 ofs6 buf6 dest6 where
      c5_state_eq: "mt_state c5 = (q6, ofs6, buf6, dest6, SS6)"
    using inv_ss6 unfolding ae_inv_ss6_def
    by (cases "mt_state c5") auto
  have c6_state: "mt_state c6 = (q6, ofs6, buf6, dest6, SS7)"
    using step6_sub c5_state_eq
    by (auto simp: ae_delta_ss6_ss7_def elim: mttm_step.cases)
  have c7_state: "mt_state c7 = (q6, ofs6, buf6, dest6, SS8)"
    using step7_sub c6_state
    by (auto simp: ae_delta_ss7_ss8_def elim: mttm_step.cases)
  have buf6_eq_buf5: "buf6 = buf5"
    using c5_state_eq c5_state by simp
  have q6_eq_q5: "q6 = q5"
    using c5_state_eq c5_state by simp
  have ofs6_eq_ofs5: "ofs6 = ofs5"
    using c5_state_eq c5_state by simp
  have dest6_eq_dest5: "dest6 = dest5"
    using c5_state_eq c5_state by simp

  \<comment> \<open>Sub-step 5j: head trajectory at SS5 for pos=1 tapes under
      \<open>dest = AE_Left\<close>.  Mirror of \<open>c5_pos_for_pos1\<close> with R-direction
      (when \<open>dest = AE_Left\<close>, \<open>ae_ss5_action\<close>'s else-branch returns
      \<open>(h, R)\<close>); head lands at block 2.  Plus \<open>tape_c5_at_one_pos1\<close>:
      the SS5 write at \<open>c4_pos = 1\<close> records the home buffer slot
      \<open>fst (snd (buf5 k))\<close> at \<open>c5\<close>'s cell 1.\<close>
  have c5_pos_for_pos1_dest_left:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1 \<Longrightarrow> dest5 kk = AE_Left
            \<Longrightarrow> mt_pos c5 kk = 2"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume pos_kk: "mt_pos c' kk = 1"
    assume dest_eq: "dest5 kk = AE_Left"
    obtain qq tts nn qq' aa5 dr5 where
        c4_eq5: "c4 = Config\<^sub>M qq tts nn"
      and c5_eq: "c5 = Config\<^sub>M qq'
                          (\<lambda>k. (tts k)(nn k := aa5 k))
                          (\<lambda>k. go_dir (dr5 k) (nn k))"
      and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa5, dr5)
                    \<in> ae_delta_ss5_ss6 M"
      using step5_sub by (auto elim: mttm_step.cases)
    obtain q ofs buf dest where
        qq_eq: "qq = (q, ofs, buf, dest, SS5)"
      and dr5_eq:
          "dr5 = (\<lambda>k. if k < k_tm M
                       then snd (ae_ss5_action (le_tm M)
                                  (tts k (nn k)) (buf k) (dest k))
                       else dir.N)"
      using tr_in by (auto simp: ae_delta_ss5_ss6_def)
    have qq_state: "qq = (q5, ofs5, buf5, dest5, SS5)"
      using c4_state c4_eq5 by simp
    have buf_eq: "buf = buf5" using qq_eq qq_state by simp
    have dest_eq2: "dest = dest5" using qq_eq qq_state by simp
    have nn_kk: "nn kk = mt_pos c4 kk" using c4_eq5 by simp
    have c4_kk: "mt_pos c4 kk = 1" using c4_pos kklt pos_kk by simp
    have tts_kk: "tts kk (nn kk) = mt_tape c4 kk (mt_pos c4 kk)"
      using c4_eq5 nn_kk by simp
    have read_at_home: "tts kk (nn kk) = mt_tape c' kk 1"
      using tts_kk c4_kk tape_c4_eq_c' by simp
    have home_ne_LE: "mt_tape c' kk 1 \<noteq> LE_block (le_tm M)"
    proof -
      have pos_ge1: "(1 :: nat) \<le> mt_pos c' kk" using pos_kk by simp
      have "mt_tape c' kk (mt_pos c' kk) \<noteq> LE_block (le_tm M)"
        using home_classification[rule_format, OF kklt] pos_ge1 by blast
      thus ?thesis using pos_kk by simp
    qed
    have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      using read_at_home home_ne_LE by simp
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have h_ne_LE: "hh \<noteq> LE_block (le_tm M)"
    proof -
      have "fst (snd (buf5 kk)) \<noteq> LE_block (le_tm M)"
        using buf5_not_le_per_tape[rule_format, OF kklt] pos_kk by blast
      thus ?thesis using buf5_kk by simp
    qed
    have dr5_kk:
        "dr5 kk = (if dest5 kk = AE_Left then dir.R else dir.L)"
      using dr5_eq buf_eq dest_eq2 buf5_kk read_ne_LE h_ne_LE kklt by simp
    have dr5_kk_R: "dr5 kk = dir.R"
      using dr5_kk dest_eq by simp
    have "mt_pos c5 kk = go_dir (dr5 kk) (nn kk)"
      using c5_eq by simp
    also have "\<dots> = Suc (nn kk)" using dr5_kk_R by simp
    also have "\<dots> = Suc (mt_pos c4 kk)" using nn_kk by simp
    also have "\<dots> = Suc 1" using c4_kk by simp
    also have "\<dots> = 2" by simp
    finally show "mt_pos c5 kk = 2" .
  qed

  have tape_c5_at_one_pos1:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1
            \<Longrightarrow> mt_tape c5 kk 1 = fst (snd (buf5 kk))"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume pos_kk: "mt_pos c' kk = 1"
    obtain qq tts nn qq' aa5 dr5 where
        c4_eq5: "c4 = Config\<^sub>M qq tts nn"
      and c5_eq: "c5 = Config\<^sub>M qq'
                          (\<lambda>k. (tts k)(nn k := aa5 k))
                          (\<lambda>k. go_dir (dr5 k) (nn k))"
      and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa5, dr5)
                    \<in> ae_delta_ss5_ss6 M"
      using step5_sub by (auto elim: mttm_step.cases)
    obtain q ofs buf dest where
        qq_eq: "qq = (q, ofs, buf, dest, SS5)"
      and aa5_eq:
          "aa5 = (\<lambda>k. if k < k_tm M then fst (ae_ss5_action (le_tm M)
                              (tts k (nn k)) (buf k) (dest k)) else bl_block (bl_tm M))"
      using tr_in by (auto simp: ae_delta_ss5_ss6_def)
    have qq_state: "qq = (q5, ofs5, buf5, dest5, SS5)"
      using c4_state c4_eq5 by simp
    have buf_eq: "buf = buf5" using qq_eq qq_state by simp
    have dest_eq: "dest = dest5" using qq_eq qq_state by simp
    have nn_kk: "nn kk = mt_pos c4 kk" using c4_eq5 by simp
    have c4_kk: "mt_pos c4 kk = 1" using c4_pos kklt pos_kk by simp
    have tts_kk: "tts kk (nn kk) = mt_tape c4 kk (mt_pos c4 kk)"
      using c4_eq5 nn_kk by simp
    have read_at_home: "tts kk (nn kk) = mt_tape c' kk 1"
      using tts_kk c4_kk tape_c4_eq_c' by simp
    have home_ne_LE: "mt_tape c' kk 1 \<noteq> LE_block (le_tm M)"
    proof -
      have pos_ge1: "(1 :: nat) \<le> mt_pos c' kk" using pos_kk by simp
      have "mt_tape c' kk (mt_pos c' kk) \<noteq> LE_block (le_tm M)"
        using home_classification[rule_format, OF kklt] pos_ge1 by blast
      thus ?thesis using pos_kk by simp
    qed
    have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      using read_at_home home_ne_LE by simp
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have h_ne_LE: "hh \<noteq> LE_block (le_tm M)"
    proof -
      have "fst (snd (buf5 kk)) \<noteq> LE_block (le_tm M)"
        using buf5_not_le_per_tape[rule_format, OF kklt] pos_kk by blast
      thus ?thesis using buf5_kk by simp
    qed
    have aa5_kk: "aa5 kk = fst (snd (buf5 kk))"
      using aa5_eq buf_eq dest_eq buf5_kk read_ne_LE h_ne_LE kklt by simp
    have c5_tape_kk: "mt_tape c5 kk = (tts kk)(nn kk := aa5 kk)"
      using c5_eq by simp
    have step_apply: "mt_tape c5 kk 1 = ((tts kk)(nn kk := aa5 kk)) 1"
      using c5_tape_kk by simp
    have hit: "((tts kk)(nn kk := aa5 kk)) 1 = aa5 kk"
      using nn_kk c4_kk by simp
    show "mt_tape c5 kk 1 = fst (snd (buf5 kk))"
      using step_apply hit aa5_kk by simp
  qed

  \<comment> \<open>Sub-step 5k: c6 trajectory for pos=1 + dest=\<open>AE_Left\<close>.
      \<open>c5_pos = 2\<close>; SS6 reads \<open>mt_tape c5 k 2\<close> which is off-head
      from SS5's write at \<open>c4_pos = 1\<close>, so \<open>= mt_tape c4 k 2
      = mt_tape c' k 2\<close>.  \<open>right_not_le_c'\<close> instantiated at pos=1
      gives \<open>\<noteq> LE_block\<close>.  Buf5 home \<open>\<noteq> LE\<close> (\<open>buf5_not_le_per_tape\<close>).
      \<open>ae_ss6_action\<close>'s else-branch fires with \<open>ds = AE_Left\<close>:
      writes \<open>r\<close>, direction \<open>L\<close>; head lands at \<open>c6_pos = c5_pos - 1
      = 1\<close>.  Plus \<open>tape_c6_zero_le_pos1_dest_left\<close>: cell 0
      is off-head from SS6's write at \<open>c5_pos = 2\<close>, hence \<open>= LE\<close>
      via \<open>tape_c5_zero_le\<close>.\<close>
  have c6_pos_for_pos1_dest_left:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1 \<Longrightarrow> dest5 kk = AE_Left
            \<Longrightarrow> mt_pos c6 kk = 1"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume pos_kk: "mt_pos c' kk = 1"
    assume dest_eq: "dest5 kk = AE_Left"
    obtain qq tts nn qq' aa6 dr6 where
        c5_eq6: "c5 = Config\<^sub>M qq tts nn"
      and c6_eq: "c6 = Config\<^sub>M qq'
                          (\<lambda>k. (tts k)(nn k := aa6 k))
                          (\<lambda>k. go_dir (dr6 k) (nn k))"
      and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa6, dr6)
                    \<in> ae_delta_ss6_ss7 M"
      using step6_sub by (auto elim: mttm_step.cases)
    obtain q ofs buf dest where
        qq_eq: "qq = (q, ofs, buf, dest, SS6)"
      and dr6_eq:
          "dr6 = (\<lambda>k. if k < k_tm M then snd (ae_ss6_action (le_tm M)
                              (tts k (nn k)) (buf k) (dest k)) else dir.N)"
      using tr_in by (auto simp: ae_delta_ss6_ss7_def)
    have qq_state: "qq = (q5, ofs5, buf5, dest5, SS6)"
      using c5_state c5_eq6 by simp
    have buf_eq: "buf = buf5" using qq_eq qq_state by simp
    have dest_eq2: "dest = dest5" using qq_eq qq_state by simp
    have nn_kk: "nn kk = mt_pos c5 kk" using c5_eq6 by simp
    have c5_kk: "mt_pos c5 kk = 2"
      using c5_pos_for_pos1_dest_left[OF kklt pos_kk dest_eq] .
    have tts_kk: "tts kk (nn kk) = mt_tape c5 kk (mt_pos c5 kk)"
      using c5_eq6 nn_kk by simp
    have c5_tape_at_2: "mt_tape c5 kk 2 = mt_tape c4 kk 2"
    proof -
      have two_ne_pos_c4: "(2 :: nat) \<noteq> mt_pos c4 kk"
        using c4_pos kklt pos_kk by simp
      show ?thesis
        using mttm_step_tape_off_head[OF step5 two_ne_pos_c4] .
    qed
    have c4_tape_at_2: "mt_tape c4 kk 2 = mt_tape c' kk 2"
      using tape_c4_eq_c' by simp
    have read_at_right:
        "tts kk (nn kk) = mt_tape c' kk 2"
      using tts_kk c5_kk c5_tape_at_2 c4_tape_at_2 by simp
    have right_ne_LE_pos1: "mt_tape c' kk 2 \<noteq> LE_block (le_tm M)"
    proof -
      have "mt_tape c' kk (mt_pos c' kk + 1) \<noteq> LE_block (le_tm M)"
        using right_not_le_c' by blast
      thus ?thesis using pos_kk by (simp add: numeral_2_eq_2)
    qed
    have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      using read_at_right right_ne_LE_pos1 by simp
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have h_ne_LE: "hh \<noteq> LE_block (le_tm M)"
    proof -
      have "fst (snd (buf5 kk)) \<noteq> LE_block (le_tm M)"
        using buf5_not_le_per_tape[rule_format, OF kklt] pos_kk by blast
      thus ?thesis using buf5_kk by simp
    qed
    have dr6_kk:
        "dr6 kk = (if dest5 kk = AE_Left then dir.L else dir.R)"
      using dr6_eq buf_eq dest_eq2 buf5_kk read_ne_LE h_ne_LE kklt by simp
    have dr6_kk_L: "dr6 kk = dir.L"
      using dr6_kk dest_eq by simp
    have "mt_pos c6 kk = go_dir (dr6 kk) (nn kk)"
      using c6_eq by simp
    also have "\<dots> = (nn kk) - 1" using dr6_kk_L by simp
    also have "\<dots> = (mt_pos c5 kk) - 1" using nn_kk by simp
    also have "\<dots> = 2 - 1" using c5_kk by simp
    also have "\<dots> = 1" by simp
    finally show "mt_pos c6 kk = 1" .
  qed

  have tape_c6_zero_le_pos1_dest_left:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1 \<Longrightarrow> dest5 kk = AE_Left
            \<Longrightarrow> mt_tape c6 kk 0 = LE_block (le_tm M)"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume pos_kk: "mt_pos c' kk = 1"
    assume dest_eq: "dest5 kk = AE_Left"
    have zero_ne_pos_c5: "(0 :: nat) \<noteq> mt_pos c5 kk"
      using c5_pos_for_pos1_dest_left[OF kklt pos_kk dest_eq] by simp
    have c6_zero_eq_c5:
        "mt_tape c6 kk 0 = mt_tape c5 kk 0"
      using mttm_step_tape_off_head[OF step6 zero_ne_pos_c5] .
    have c5_zero_le: "mt_tape c5 kk 0 = LE_block (le_tm M)"
      using tape_c5_zero_le[rule_format, OF kklt] by simp
    show "mt_tape c6 kk 0 = LE_block (le_tm M)"
      using c6_zero_eq_c5 c5_zero_le by simp
  qed

  \<comment> \<open>Sub-step 5l: c7 trajectory for pos=1 + dest=\<open>AE_Left\<close>.  \<open>c6_pos = 1\<close>;
      SS7 reads \<open>mt_tape c6 k 1 = mt_tape c5 k 1\<close> (off-head from SS6's
      write at \<open>c5_pos = 2\<close>), and \<open>mt_tape c5 k 1 = fst (snd (buf5 k))\<close>
      (via \<open>tape_c5_at_one_pos1\<close>) = home buffer slot, \<open>\<noteq> LE\<close>.
      \<open>ae_ss7_action\<close>'s else-branch fires with \<open>ds = AE_Left\<close>:
      writes \<open>a\<close>, direction \<open>L\<close>; \<open>c7_pos = c6_pos - 1 = 0\<close>.  Plus
      \<open>tape_c7_zero_le\<close>: cell 0 off-head from SS7's write at \<open>c6_pos = 1\<close>,
      so \<open>= LE\<close> via \<open>tape_c6_zero_le_pos1_dest_left\<close>.\<close>
  have c7_pos_for_pos1_dest_left:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1 \<Longrightarrow> dest5 kk = AE_Left
            \<Longrightarrow> mt_pos c7 kk = 0"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume pos_kk: "mt_pos c' kk = 1"
    assume dest_eq: "dest5 kk = AE_Left"
    obtain qq tts nn qq' aa7 dr7 where
        c6_eq7: "c6 = Config\<^sub>M qq tts nn"
      and c7_eq: "c7 = Config\<^sub>M qq'
                          (\<lambda>k. (tts k)(nn k := aa7 k))
                          (\<lambda>k. go_dir (dr7 k) (nn k))"
      and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa7, dr7)
                    \<in> ae_delta_ss7_ss8 M"
      using step7_sub by (auto elim: mttm_step.cases)
    obtain q ofs buf dest where
        qq_eq: "qq = (q, ofs, buf, dest, SS7)"
      and dr7_eq:
          "dr7 = (\<lambda>k. if k < k_tm M then snd (ae_ss7_action (le_tm M)
                              (tts k (nn k)) (buf k) (dest k)) else dir.N)"
      using tr_in by (auto simp: ae_delta_ss7_ss8_def)
    have qq_state: "qq = (q5, ofs5, buf5, dest5, SS7)"
      using c6_state c6_eq7 q6_eq_q5 ofs6_eq_ofs5
            buf6_eq_buf5 dest6_eq_dest5 by simp
    have buf_eq: "buf = buf5" using qq_eq qq_state by simp
    have dest_eq2: "dest = dest5" using qq_eq qq_state by simp
    have nn_kk: "nn kk = mt_pos c6 kk" using c6_eq7 by simp
    have c6_kk: "mt_pos c6 kk = 1"
      using c6_pos_for_pos1_dest_left[OF kklt pos_kk dest_eq] .
    have tts_kk: "tts kk (nn kk) = mt_tape c6 kk (mt_pos c6 kk)"
      using c6_eq7 nn_kk by simp
    have one_ne_pos_c5: "(1 :: nat) \<noteq> mt_pos c5 kk"
      using c5_pos_for_pos1_dest_left[OF kklt pos_kk dest_eq] by simp
    have c6_at_one: "mt_tape c6 kk 1 = mt_tape c5 kk 1"
      using mttm_step_tape_off_head[OF step6 one_ne_pos_c5] .
    have c6_at_one_eq_h:
        "mt_tape c6 kk 1 = fst (snd (buf5 kk))"
      using c6_at_one tape_c5_at_one_pos1[OF kklt pos_kk] by simp
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have h_ne_LE: "hh \<noteq> LE_block (le_tm M)"
    proof -
      have "fst (snd (buf5 kk)) \<noteq> LE_block (le_tm M)"
        using buf5_not_le_per_tape[rule_format, OF kklt] pos_kk by blast
      thus ?thesis using buf5_kk by simp
    qed
    have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      using tts_kk c6_kk c6_at_one_eq_h buf5_kk h_ne_LE by simp
    have dr7_kk:
        "dr7 kk = (if dest5 kk = AE_Left then dir.L else dir.R)"
      using dr7_eq buf_eq dest_eq2 buf5_kk read_ne_LE h_ne_LE kklt by simp
    have dr7_kk_L: "dr7 kk = dir.L"
      using dr7_kk dest_eq by simp
    have "mt_pos c7 kk = go_dir (dr7 kk) (nn kk)"
      using c7_eq by simp
    also have "\<dots> = (nn kk) - 1" using dr7_kk_L by simp
    also have "\<dots> = (mt_pos c6 kk) - 1" using nn_kk by simp
    also have "\<dots> = 1 - 1" using c6_kk by simp
    also have "\<dots> = 0" by simp
    finally show "mt_pos c7 kk = 0" .
  qed

  have tape_c7_zero_le_pos1_dest_left:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1 \<Longrightarrow> dest5 kk = AE_Left
            \<Longrightarrow> mt_tape c7 kk 0 = LE_block (le_tm M)"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume pos_kk: "mt_pos c' kk = 1"
    assume dest_eq: "dest5 kk = AE_Left"
    have zero_ne_pos_c6: "(0 :: nat) \<noteq> mt_pos c6 kk"
      using c6_pos_for_pos1_dest_left[OF kklt pos_kk dest_eq] by simp
    have c7_zero_eq_c6:
        "mt_tape c7 kk 0 = mt_tape c6 kk 0"
      using mttm_step_tape_off_head[OF step7 zero_ne_pos_c6] .
    show "mt_tape c7 kk 0 = LE_block (le_tm M)"
      using c7_zero_eq_c6 tape_c6_zero_le_pos1_dest_left[OF kklt pos_kk dest_eq]
      by simp
  qed

  \<comment> \<open>Sub-step 5m: \<open>pos_link_c7\<close> + SS8\<open>\<rightarrow>\<close>SS1 invocation.  Mirror
      of \<open>pos_link_c5\<close>: right-slot uniform non-LE from buf5
      (= buf6) regime case-split; SS8 conditional substantive only
      for pos=1 + dest=\<open>AE_Left\<close>, vacuous for pos=0/\<open>\<ge>\<close>2.
      Then \<open>le_compat_ss8\<close> from \<open>pos_link_c7\<close>, invoke
      \<open>ae_step_ss8_ss1_exists\<close>.\<close>
  have pos_link_c7: "ae_position_link M c7"
  proof -
    have r_not_le: "\<forall>k<k_tm M. snd (snd (buf6 k)) \<noteq> LE_block (le_tm M)"
    proof (intro allI impI)
      fix k
      assume klt: "k < k_tm M"
      consider (le0) "mt_pos c' k = 0"
             | (le1) "mt_pos c' k = 1"
             | (steady) "mt_pos c' k \<ge> 2"
        by linarith
      thus "snd (snd (buf6 k)) \<noteq> LE_block (le_tm M)"
      proof cases
        case le0    thus ?thesis using buf5_not_le_per_tape[rule_format, OF klt] buf6_eq_buf5 by blast
      next
        case le1    thus ?thesis using buf5_not_le_per_tape[rule_format, OF klt] buf6_eq_buf5 by blast
      next
        case steady thus ?thesis using buf5_not_le_per_tape[rule_format, OF klt] buf6_eq_buf5 by blast
      qed
    qed
    have ss8_cond:
        "\<forall>k<k_tm M. dest6 k = AE_Left
                \<longrightarrow> fst (buf6 k) = LE_block (le_tm M)
                \<longrightarrow> mt_tape c7 k (mt_pos c7 k) = LE_block (le_tm M)"
    proof (intro allI impI)
      fix k
      assume klt: "k < k_tm M"
      assume dest_eq: "dest6 k = AE_Left"
      assume l_eq_le: "fst (buf6 k) = LE_block (le_tm M)"
      have dest5_eq: "dest5 k = AE_Left" using dest_eq dest6_eq_dest5 by simp
      have l_eq_le_buf5: "fst (buf5 k) = LE_block (le_tm M)"
        using l_eq_le buf6_eq_buf5 by simp
      consider (le0) "mt_pos c' k = 0"
             | (le1) "mt_pos c' k = 1"
             | (steady) "mt_pos c' k \<ge> 2"
        by linarith
      thus "mt_tape c7 k (mt_pos c7 k) = LE_block (le_tm M)"
      proof cases
        case le0
        have "fst (buf5 k) \<noteq> LE_block (le_tm M)"
          using buf5_not_le_per_tape[rule_format, OF klt] le0 by blast
        thus ?thesis using l_eq_le_buf5 by simp
      next
        case le1
        have c7_pos_k: "mt_pos c7 k = 0"
          using c7_pos_for_pos1_dest_left[OF klt le1 dest5_eq] .
        have "mt_tape c7 k 0 = LE_block (le_tm M)"
          using tape_c7_zero_le_pos1_dest_left[OF klt le1 dest5_eq] .
        thus ?thesis using c7_pos_k by simp
      next
        case steady
        have "fst (buf5 k) \<noteq> LE_block (le_tm M)"
          using buf5_not_le_per_tape[rule_format, OF klt] steady by blast
        thus ?thesis using l_eq_le_buf5 by simp
      qed
    qed
    show ?thesis
      unfolding ae_position_link_def
      using r_not_le ss8_cond c7_state by simp
  qed

  have le_compat_ss8_c7: "ae_le_compat_ss8 M c7"
    using ae_position_link_discharges_ss8[OF inv_ss8 pos_link_c7] .
  obtain c8 where
      step8_sub: "(c7, c8) \<in> mttm_step (ae_delta_ss8_ss1 M)"
    and step8: "(c7, c8) \<in> mttm_step (alphabet_enlarge_delta M)"
    using ae_step_ss8_ss1_exists[OF vM inv_ss8 gamma_c7 buf_gamma_c7
                                    le_compat_ss8_c7] by blast
  \<comment> \<open>Re-express the per-tape \<open>\<And>kk\<close> facts as object-level
      \<open>\<forall>kk\<close> before feeding \<open>that\<close>: the nested meta-implication
      under the obtains witness binders defeats elim-resolution at the call
      site.  The call site recovers the
      \<open>\<And>kk\<close> form via \<open>[rule_format]\<close>.\<close>
  have c4_pos_all: "\<forall>kk. kk < k_tm M \<longrightarrow> mt_pos c4 kk = mt_pos c' kk"
    using c4_pos by blast
  have c5_pos_for_pos1_all:
      "\<forall>kk. kk < k_tm M \<longrightarrow> mt_pos c' kk = 1 \<longrightarrow> dest5 kk \<noteq> AE_Left
       \<longrightarrow> mt_pos c5 kk = 0"
    using c5_pos_for_pos1 by blast
  have c5_pos_for_pos1_dest_left_all:
      "\<forall>kk. kk < k_tm M \<longrightarrow> mt_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
       \<longrightarrow> mt_pos c5 kk = 2"
    using c5_pos_for_pos1_dest_left by blast
  have tape_c5_at_one_pos1_all:
      "\<forall>kk. kk < k_tm M \<longrightarrow> mt_pos c' kk = 1
       \<longrightarrow> mt_tape c5 kk 1 = fst (snd (buf5 kk))"
    using tape_c5_at_one_pos1 by blast
  have c6_pos_for_pos1_dest_left_all:
      "\<forall>kk. kk < k_tm M \<longrightarrow> mt_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
       \<longrightarrow> mt_pos c6 kk = 1"
    using c6_pos_for_pos1_dest_left by blast
  have c7_pos_for_pos1_dest_left_all:
      "\<forall>kk. kk < k_tm M \<longrightarrow> mt_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
       \<longrightarrow> mt_pos c7 kk = 0"
    using c7_pos_for_pos1_dest_left by blast
  have tape_c7_zero_le_pos1_dest_left_all:
      "\<forall>kk. kk < k_tm M \<longrightarrow> mt_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
       \<longrightarrow> mt_tape c7 kk 0 = LE_block (le_tm M)"
    using tape_c7_zero_le_pos1_dest_left by blast
  show thesis by (rule that[OF step5_sub step5 c4_state c5_state tape_c4_eq_c'
        buf5_not_le_per_tape right_not_le_c' c4_pos_all tape_c5_zero_le
        c5_pos_for_pos1_all step6_sub step6 step7_sub step7 gamma_c7 buf_gamma_c7
        c6_state c7_state buf6_eq_buf5 q6_eq_q5 ofs6_eq_ofs5 dest6_eq_dest5
        c5_pos_for_pos1_dest_left_all tape_c5_at_one_pos1_all
        c6_pos_for_pos1_dest_left_all c7_pos_for_pos1_dest_left_all
        tape_c7_zero_le_pos1_dest_left_all step8_sub step8])
qed

end
