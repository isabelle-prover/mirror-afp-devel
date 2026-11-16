theory AlphabetEnlargement_ForwardStep
  imports AlphabetEnlargement_ForwardCells
begin

subsection \<open>One forward stage: substeps 5 to 8\<close>

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
  fixes M :: "('q, 'a) ktm"
    and cM :: "('a, 'q) ktc_config"
    and c' c1 c2 c3 c4 :: "(nat \<Rightarrow> 'a,
                'q \<times> 'a ae_stage) ktc_config"
  assumes vM:        "valid_ktm M"
      and le_anchor:
      "\<forall>k<k_ktm M. ktc_tape c' k 0 = LE_block m (le_ktm M)"
      and no_le_per_tape:
      "\<forall>k. (ktc_pos c' k \<ge> 2
      \<longrightarrow> (\<forall>i. i < 3 * m
      \<longrightarrow> ktc_tape cM k
      ((ktc_pos c' k - 2) * m + 1 + i)
      \<noteq> le_ktm M))
      \<and> (ktc_pos c' k = 1
      \<longrightarrow> (\<forall>i. i < 2 * m
      \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))
      \<and> (ktc_pos c' k = 0
      \<longrightarrow> (\<forall>i. i < m
      \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))"
      and tape_corr: "\<forall>k<k_ktm M. ae_tape_correspondence m (le_ktm M)
      (ktc_tape cM k) (ktc_tape c' k)"
      and step1_sub: "(c', c1) \<in> ktm_step (ae_delta_ss1_ss2 m M)"
      and step2_sub: "(c1, c2) \<in> ktm_step (ae_delta_ss2_ss3 m M)"
      and step3_sub: "(c2, c3) \<in> ktm_step (ae_delta_ss3_ss4 m M)"
      and c_ge_1: "1 \<le> m"
      and c_eq_len: "m = length [0..<m]"
      and home_classification:
      "\<forall>k<k_ktm M. (ktc_pos c' k = 0
      \<longrightarrow> ktc_tape c' k (ktc_pos c' k) = LE_block m (le_ktm M))
      \<and> (ktc_pos c' k \<ge> 1
      \<longrightarrow> ktc_tape c' k (ktc_pos c' k) \<noteq> LE_block m (le_ktm M))"
      and c3_pos: "\<And>k. k < k_ktm M \<Longrightarrow> ktc_pos c3 k = ktc_pos c' k + 1"
      and bl_neq_le:
      "(bl_block m (bl_ktm M) :: nat \<Rightarrow> 'a) \<noteq> LE_block m (le_ktm M)"
      and step4_sub: "(c3, c4) \<in> ktm_step (ae_delta_ss4_ss5 m M)"
      and c4_buf_not_le_per_tape:
      "case ktc_state c4 of (_, _, b, _, _) \<Rightarrow>
      \<forall>kk<k_ktm M. (ktc_pos c' kk = 0
      \<longrightarrow> fst (b kk) \<noteq> LE_block m (le_ktm M)
      \<and> snd (snd (b kk)) \<noteq> LE_block m (le_ktm M))
      \<and> (ktc_pos c' kk = 1
      \<longrightarrow> fst (snd (b kk)) \<noteq> LE_block m (le_ktm M)
      \<and> snd (snd (b kk)) \<noteq> LE_block m (le_ktm M))
      \<and> (ktc_pos c' kk \<ge> 2
      \<longrightarrow> fst (b kk) \<noteq> LE_block m (le_ktm M)
      \<and> fst (snd (b kk)) \<noteq> LE_block m (le_ktm M)
      \<and> snd (snd (b kk)) \<noteq> LE_block m (le_ktm M))"
      and inv_ss5: "ae_inv_ss5 M c4"
      and gamma_c4: "ae_tape_in_gamma_block m M c4"
      and buf_gamma_c4: "ae_buffer_in_gamma_block m M c4"
  obtains c5 q5 ofs5 buf5 dest5 c6 c7 q6 ofs6 buf6 dest6 c8
    where "(c4, c5) \<in> ktm_step (ae_delta_ss5_ss6 m M)"
      and "(c4, c5) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and "ktc_state c4 = (q5, ofs5, buf5, dest5, SS5)"
      and "ktc_state c5 = (q5, ofs5, buf5, dest5, SS6)"
      and "ktc_tape c4 = ktc_tape c'"
      and
      "\<forall>k<k_ktm M. (ktc_pos c' k = 0
      \<longrightarrow> fst (buf5 k) \<noteq> LE_block m (le_ktm M)
      \<and> snd (snd (buf5 k)) \<noteq> LE_block m (le_ktm M))
      \<and> (ktc_pos c' k = 1
      \<longrightarrow> fst (snd (buf5 k)) \<noteq> LE_block m (le_ktm M)
      \<and> snd (snd (buf5 k)) \<noteq> LE_block m (le_ktm M))
      \<and> (ktc_pos c' k \<ge> 2
      \<longrightarrow> fst (buf5 k) \<noteq> LE_block m (le_ktm M)
      \<and> fst (snd (buf5 k)) \<noteq> LE_block m (le_ktm M)
      \<and> snd (snd (buf5 k)) \<noteq> LE_block m (le_ktm M))"
      and
      "\<forall>k. ktc_tape c' k (ktc_pos c' k + 1) \<noteq> LE_block m (le_ktm M)"
      and "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c4 kk = ktc_pos c' kk"
      and "\<forall>k<k_ktm M. ktc_tape c5 k 0 = LE_block m (le_ktm M)"
      and
      "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk \<noteq> AE_Left
      \<longrightarrow> ktc_pos c5 kk = 0"
      and "(c5, c6) \<in> ktm_step (ae_delta_ss6_ss7 m M)"
      and "(c5, c6) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and "(c6, c7) \<in> ktm_step (ae_delta_ss7_ss8 m M)"
      and "(c6, c7) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and "ae_tape_in_gamma_block m M c7"
      and "ae_buffer_in_gamma_block m M c7"
      and "ktc_state c6 = (q6, ofs6, buf6, dest6, SS7)"
      and "ktc_state c7 = (q6, ofs6, buf6, dest6, SS8)"
      and "buf6 = buf5"
      and "q6 = q5"
      and "ofs6 = ofs5"
      and "dest6 = dest5"
      and
      "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
      \<longrightarrow> ktc_pos c5 kk = 2"
      and
      "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1
      \<longrightarrow> ktc_tape c5 kk 1 = fst (snd (buf5 kk))"
      and
      "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
      \<longrightarrow> ktc_pos c6 kk = 1"
      and
      "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
      \<longrightarrow> ktc_pos c7 kk = 0"
      and
      "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
      \<longrightarrow> ktc_tape c7 kk 0 = LE_block m (le_ktm M)"
      and "(c7, c8) \<in> ktm_step (ae_delta_ss8_ss1 m M)"
      and "(c7, c8) \<in> ktm_step (alphabet_enlarge_delta m M)"
proof -
  obtain c5 where
      step5_sub: "(c4, c5) \<in> ktm_step (ae_delta_ss5_ss6 m M)"
    and step5: "(c4, c5) \<in> ktm_step (alphabet_enlarge_delta m M)"
    using ae_step_ss5_ss6_exists[OF inv_ss5 gamma_c4 buf_gamma_c4] by blast
  have inv_ss6: "ae_inv_ss6 M c5"
    using ae_step_ss5_ss6_invariant[OF vM inv_ss5 step5_sub] .
  have gamma_c5: "ae_tape_in_gamma_block m M c5"
    using ae_step_alphabet_enlarge_gamma_preserve[OF gamma_c4 step5] .
  have buf_gamma_c5: "ae_buffer_in_gamma_block m M c5"
    using ae_step_alphabet_enlarge_buffer_gamma_preserve[OF step5] .

  \<comment> \<open>State shapes at \<open>c4\<close> (idx SS5) and \<open>c5\<close> (idx SS6).
      Identical derivation across regimes; the substep preserves
      \<open>(q, ofs, buf, dest)\<close> and flips only the stage index.\<close>
  obtain q5 ofs5 buf5 dest5 where
      c4_state: "ktc_state c4 = (q5, ofs5, buf5, dest5, SS5)"
    using inv_ss5 unfolding ae_inv_ss5_def
    by (cases "ktc_state c4") auto
  have c5_state: "ktc_state c5 = (q5, ofs5, buf5, dest5, SS6)"
    using step5_sub c4_state
    by (auto simp: ae_delta_ss5_ss6_def elim: ktm_step.cases)

  \<comment> \<open>Sub-step 5b: M'-tape preservation through SS1\<open>\<rightarrow>\<close>SS2 \<open>\<rightarrow>\<close>
      \<open>\<dots>\<close> \<open>\<rightarrow>\<close>SS5.  Each sub-delta has \<open>a' = a\<close> (idempotent
      on \<open>M'\<close>-tape), so the cumulative tape is unchanged through
      \<open>c1\<close>\<open>\<dots>\<close>\<open>c4\<close>.  Uniform across regimes.\<close>
  have nw_12: "\<And>q a q' a' d.
                  (q, a, q', a', d) \<in> ae_delta_ss1_ss2 m M \<Longrightarrow> a' = a"
    by (auto simp: ae_delta_ss1_ss2_def)
  have nw_23: "\<And>q a q' a' d.
                  (q, a, q', a', d) \<in> ae_delta_ss2_ss3 m M \<Longrightarrow> a' = a"
    by (auto simp: ae_delta_ss2_ss3_def)
  have nw_34: "\<And>q a q' a' d.
                  (q, a, q', a', d) \<in> ae_delta_ss3_ss4 m M \<Longrightarrow> a' = a"
    by (auto simp: ae_delta_ss3_ss4_def)
  have nw_45: "\<And>q a q' a' d.
                  (q, a, q', a', d) \<in> ae_delta_ss4_ss5 m M \<Longrightarrow> a' = a"
    by (auto simp: ae_delta_ss4_ss5_def)
  have tape_c1_eq: "ktc_tape c1 = ktc_tape c'"
    using ktm_step_no_write_tape[OF step1_sub nw_12] .
  have tape_c2_eq: "ktc_tape c2 = ktc_tape c1"
    using ktm_step_no_write_tape[OF step2_sub nw_23] .
  have tape_c3_eq: "ktc_tape c3 = ktc_tape c2"
    using ktm_step_no_write_tape[OF step3_sub nw_34] .
  have tape_c4_eq: "ktc_tape c4 = ktc_tape c3"
    using ktm_step_no_write_tape[OF step4_sub nw_45] .
  have tape_c4_eq_c': "ktc_tape c4 = ktc_tape c'"
    using tape_c1_eq tape_c2_eq tape_c3_eq tape_c4_eq by simp

  \<comment> \<open>Buf5 per-tape regime-aware non-LE shape, transferred from
      \<open>c4_buf_not_le_per_tape\<close> via \<open>c4_state\<close>.  Pos=0 tapes have
      left+right non-LE; pos=1 tapes have home+right non-LE; pos\<open>\<ge>\<close>2
      tapes have all three non-LE.  This is the regime-aware
      generalisation of \<open>buf5_not_le_lr\<close> (le0) and \<open>buf5_not_le_hr\<close>
      (le1) and the steady-state full \<open>buf5_not_le\<close>.\<close>
  have buf5_not_le_per_tape:
      "\<forall>k<k_ktm M. (ktc_pos c' k = 0
             \<longrightarrow> fst (buf5 k) \<noteq> LE_block m (le_ktm M)
                \<and> snd (snd (buf5 k)) \<noteq> LE_block m (le_ktm M))
           \<and> (ktc_pos c' k = 1
                \<longrightarrow> fst (snd (buf5 k)) \<noteq> LE_block m (le_ktm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block m (le_ktm M))
           \<and> (ktc_pos c' k \<ge> 2
                \<longrightarrow> fst (buf5 k) \<noteq> LE_block m (le_ktm M)
                  \<and> fst (snd (buf5 k)) \<noteq> LE_block m (le_ktm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block m (le_ktm M))"
    using c4_buf_not_le_per_tape c4_state by simp

  \<comment> \<open>Sub-step 5c: \<open>right_not_le_c'\<close>.  The unified "right-of-home
      not LE" fact at \<open>c'\<close>: for every tape, the block at
      \<open>ktc_pos c' k + 1\<close> is not \<open>LE_block\<close>.  Powers the SS4\<open>\<rightarrow>\<close>SS5
      head-trajectory derivation (\<open>c3\<close> reads at \<open>ktc_pos c3 = ktc_pos c' + 1\<close>,
      direction \<open>L\<close> when read \<open>\<noteq> LE\<close>).  Per-tape case-split on regime:
      pos=0 uses \<open>no_le\<close> i=0 (cell 1); pos=1 uses \<open>no_le\<close> i=c (cell c+1);
      pos\<open>\<ge>\<close>2 uses \<open>no_le\<close> i=2c (cell pos\<open>\<cdot>\<close>c+1).  All three cell
      indices coincide with the correspondence-derived address
      \<open>ktc_pos c' k \<cdot> c + 1\<close>.\<close>
  have right_not_le_c':
      "\<forall>k. ktc_tape c' k (ktc_pos c' k + 1) \<noteq> LE_block m (le_ktm M)"
  proof (intro allI)
    fix k :: nat
    show "ktc_tape c' k (ktc_pos c' k + 1) \<noteq> LE_block m (le_ktm M)"
    proof (cases "k < k_ktm M")
      case True
    let ?x = "[0..<m] ! 0"
    let ?c = "m"
    have zero_lt_len: "0 < length [0..<m]"
      using c_ge_1 c_eq_len by linarith
    have x_idx0: "?x = 0"
      using zero_lt_len by simp
    have tc_k: "ae_tape_correspondence m (le_ktm M) (ktc_tape cM k) (ktc_tape c' k)"
      using tape_corr[rule_format, OF True] .
    have addr_via_tc:
        "ktc_tape cM k (ktc_pos c' k * ?c + 1)
          = ktc_tape c' k (ktc_pos c' k + 1) ?x"
    proof -
      from tc_k have unf:
          "\<forall>s\<ge>1. \<forall>i<m. ktc_tape cM k ((s - 1) * ?c + i + 1)
                      = ktc_tape c' k s i"
        unfolding ae_tape_correspondence_def by simp
      have s_ge1: "ktc_pos c' k + 1 \<ge> 1" by simp
      have x_lt: "?x < m" using c_ge_1 by simp
      from unf s_ge1 x_lt have eq:
          "ktc_tape cM k ((ktc_pos c' k + 1 - 1) * ?c + ?x + 1)
            = ktc_tape c' k (ktc_pos c' k + 1) ?x"
        by blast
      thus ?thesis using x_idx0 by simp
    qed
    consider (le0) "ktc_pos c' k = 0"
           | (le1) "ktc_pos c' k = 1"
           | (steady) "ktc_pos c' k \<ge> 2"
      by linarith
    hence "ktc_tape c' k (ktc_pos c' k + 1) ?x \<noteq> le_ktm M"
    proof cases
      case le0
      have idx_lt: "(0 :: nat) < ?c" using c_ge_1 by simp
      have nle: "ktc_tape cM k (Suc 0) \<noteq> le_ktm M"
        using no_le_per_tape le0 idx_lt by blast
      thus ?thesis using addr_via_tc le0 by simp
    next
      case le1
      have idx_lt: "?c < 2 * ?c" using c_ge_1 by simp
      have nle: "ktc_tape cM k (Suc ?c) \<noteq> le_ktm M"
        using no_le_per_tape le1 idx_lt by blast
      hence "ktc_tape cM k (1 * ?c + 1) \<noteq> le_ktm M" by simp
      thus ?thesis using addr_via_tc le1 by simp
    next
      case steady
      have idx_lt: "2 * ?c < 3 * ?c" using c_ge_1 by simp
      have addr_eq:
          "(ktc_pos c' k - 2) * ?c + 1 + 2 * ?c = ktc_pos c' k * ?c + 1"
        using steady by (simp add: algebra_simps diff_mult_distrib)
      have nle: "ktc_tape cM k ((ktc_pos c' k - 2) * ?c + 1 + 2 * ?c) \<noteq> le_ktm M"
        using no_le_per_tape steady idx_lt by blast
      thus ?thesis using addr_via_tc addr_eq by simp
    qed
    thus "ktc_tape c' k (ktc_pos c' k + 1) \<noteq> LE_block m (le_ktm M)"
      using c_ge_1 unfolding LE_block_def by auto
    next
      case False
      hence kge: "k_ktm M \<le> k" by simp
      have "ktc_tape c' k (ktc_pos c' k + 1) = bl_block m (bl_ktm M)"
        using gamma_c4 kge
        unfolding ae_tape_in_gamma_block_def tape_c4_eq_c'[symmetric]
        by simp
      thus ?thesis using bl_neq_le by simp
    qed
  qed

  \<comment> \<open>Sub-step 5d: SS4\<open>\<rightarrow>\<close>SS5 head trajectory.  At \<open>c3\<close>'s head
      position \<open>ktc_pos c3 k = ktc_pos c' k + 1\<close>, the M'-tape reads
      \<open>ktc_tape c' k (ktc_pos c' k + 1)\<close> (via \<open>tape_c3_eq_c'\<close>) which
      is not \<open>LE_block\<close> by \<open>right_not_le_c'\<close>.  Hence
      \<open>ae_delta_ss4_ss5\<close>'s direction is \<open>L\<close>, landing \<open>c4\<close>'s head
      at \<open>ktc_pos c' k\<close>.  Uniform across regimes: pos=0 lands at 0,
      pos=1 lands at 1, pos\<open>\<ge>\<close>2 lands at pos.\<close>
  have tape_c3_eq_c': "ktc_tape c3 = ktc_tape c'"
    using tape_c1_eq tape_c2_eq tape_c3_eq by simp
  have c4_pos: "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c4 kk = ktc_pos c' kk"
  proof -
    fix kk assume kklt: "kk < k_ktm M"
    obtain qq tts nn qq' aa4 dr4 where
        c3_eq4: "c3 = KConfig qq tts nn"
      and c4_eq: "c4 = KConfig qq'
                          (\<lambda>k. (tts k)(nn k := aa4 k))
                          (\<lambda>k. go_move (dr4 k) (nn k))"
      and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa4, dr4)
                    \<in> ae_delta_ss4_ss5 m M"
      using step4_sub by (auto elim: ktm_step.cases)
    have dr4_eq:
        "dr4 = (\<lambda>k. if k < k_ktm M
                     then (if tts k (nn k) = LE_block m (le_ktm M)
                           then MoveN else MoveL)
                     else MoveN)"
      using tr_in by (auto simp: ae_delta_ss4_ss5_def)
    have nn_kk: "nn kk = ktc_pos c3 kk" using c3_eq4 by simp
    have tts_kk: "tts kk (nn kk) = ktc_tape c3 kk (ktc_pos c3 kk)"
      using c3_eq4 nn_kk by simp
    have c3_kk: "ktc_pos c3 kk = ktc_pos c' kk + 1"
      using c3_pos kklt by simp
    have read_at_c3:
        "tts kk (nn kk) = ktc_tape c' kk (ktc_pos c' kk + 1)"
      using tts_kk c3_kk tape_c3_eq_c' by simp
    have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block m (le_ktm M)"
      using read_at_c3 right_not_le_c' by simp
    have dr4_L: "dr4 kk = MoveL"
      using dr4_eq read_ne_LE kklt by simp
    have "ktc_pos c4 kk = go_move (dr4 kk) (nn kk)" using c4_eq by simp
    also have "\<dots> = (nn kk) - 1" using dr4_L by simp
    also have "\<dots> = (ktc_pos c3 kk) - 1" using nn_kk by simp
    also have "\<dots> = (ktc_pos c' kk + 1) - 1" using c3_kk by simp
    also have "\<dots> = ktc_pos c' kk" by simp
    finally show "ktc_pos c4 kk = ktc_pos c' kk" .
  qed

  \<comment> \<open>Sub-step 5e: \<open>tape_c5_zero_le\<close>.  The M'-tape cell 0 stays
      \<open>LE_block\<close> across SS5.  For pos\<open>\<ge>\<close>1 tapes \<open>c4_pos \<noteq> 0\<close>, so
      cell 0 is off-head and preserved from \<open>c4\<close> (which equals \<open>c'\<close>
      by \<open>tape_c4_eq_c'\<close>, hence \<open>LE_block\<close> by \<open>le_anchor\<close>).  For pos=0
      tapes \<open>c4_pos = 0\<close>, so the SS5 action fires at cell 0; but the
      LE-guard fires (read = \<open>LE_block\<close> via \<open>le_anchor\<close>) and
      idempotently writes \<open>LE_block\<close> back.  Either way cell 0 stays.\<close>
  have tape_c5_zero_le: "\<forall>k<k_ktm M. ktc_tape c5 k 0 = LE_block m (le_ktm M)"
  proof (intro allI impI)
    fix k assume klt: "k < k_ktm M"
    show "ktc_tape c5 k 0 = LE_block m (le_ktm M)"
      using ae_ss5_step_tape(2)[OF step5_sub c4_state klt] tape_c4_eq_c'
            le_anchor[rule_format, OF klt]
      by (cases "ktc_pos c4 k = 0") simp_all
  qed

  \<comment> \<open>Sub-step 5f: head trajectory at SS5 for pos=1 tapes.  When
      the regime is pos=1 and \<open>dest5 k \<noteq> AE_Left\<close>, the SS5 action
      moves \<open>L\<close>, landing \<open>c5\<close>'s head at block 0 (the LE
      position).  Read at \<open>c4_pos = 1\<close> is \<open>ktc_tape c' k 1 \<noteq> LE\<close>
      (via \<open>home_classification\<close> pos\<open>\<ge>\<close>1 branch); buf5 home \<open>\<noteq> LE\<close>
      (via \<open>buf5_not_le_per_tape\<close> pos=1 branch).  Neither LE-guard
      in \<open>ae_ss5_action\<close> fires; direction is \<open>L\<close> when
      \<open>dest \<noteq> AE_Left\<close>.\<close>
  have c4_reads_pos1:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1
            \<Longrightarrow> ktc_pos c4 kk = 1
              \<and> ktc_tape c4 kk 1 \<noteq> LE_block m (le_ktm M)
              \<and> fst (snd (buf5 kk)) \<noteq> LE_block m (le_ktm M)"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume pos_kk: "ktc_pos c' kk = 1"
    have c4_kk: "ktc_pos c4 kk = 1" using c4_pos kklt pos_kk by simp
    moreover have "ktc_tape c4 kk 1 \<noteq> LE_block m (le_ktm M)"
      using c4_kk tape_c4_eq_c' home_classification[rule_format, OF kklt] pos_kk
      by auto
    moreover have "fst (snd (buf5 kk)) \<noteq> LE_block m (le_ktm M)"
      using buf5_not_le_per_tape[rule_format, OF kklt] pos_kk by blast
    ultimately show "ktc_pos c4 kk = 1
              \<and> ktc_tape c4 kk 1 \<noteq> LE_block m (le_ktm M)
              \<and> fst (snd (buf5 kk)) \<noteq> LE_block m (le_ktm M)"
      by blast
  qed

  have c5_move_for_pos1:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1
            \<Longrightarrow> ktc_pos c5 kk = go_move (if dest5 kk = AE_Left then MoveR else MoveL) 1"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume pos_kk: "ktc_pos c' kk = 1"
    show "ktc_pos c5 kk = go_move (if dest5 kk = AE_Left then MoveR else MoveL) 1"
      using c4_reads_pos1[OF kklt pos_kk] ae_ss5_step_tape(1)[OF step5_sub c4_state kklt]
      by (simp add: ae_ss5_action_buf)
  qed

  have c5_pos_for_pos1:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1 \<Longrightarrow> dest5 kk \<noteq> AE_Left
            \<Longrightarrow> ktc_pos c5 kk = 0"
    using c5_move_for_pos1 by simp

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
  have pos_link_c5: "ae_position_link m M c5"
  proof -
    have r_not_le: "\<forall>k<k_ktm M. snd (snd (buf5 k)) \<noteq> LE_block m (le_ktm M)"
    proof (intro allI impI)
      fix k
      assume klt: "k < k_ktm M"
      consider (le0) "ktc_pos c' k = 0"
             | (le1) "ktc_pos c' k = 1"
             | (steady) "ktc_pos c' k \<ge> 2"
        by linarith
      thus "snd (snd (buf5 k)) \<noteq> LE_block m (le_ktm M)"
      proof cases
        case le0    thus ?thesis using buf5_not_le_per_tape[rule_format, OF klt] by blast
      next
        case le1    thus ?thesis using buf5_not_le_per_tape[rule_format, OF klt] by blast
      next
        case steady thus ?thesis using buf5_not_le_per_tape[rule_format, OF klt] by blast
      qed
    qed
    have ss6_cond:
        "\<forall>k<k_ktm M. dest5 k \<noteq> AE_Left
                \<longrightarrow> fst (buf5 k) = LE_block m (le_ktm M)
                \<longrightarrow> ktc_tape c5 k (ktc_pos c5 k) = LE_block m (le_ktm M)"
    proof (intro allI impI)
      fix k
      assume klt: "k < k_ktm M"
      assume dest_ne: "dest5 k \<noteq> AE_Left"
      assume l_eq_le: "fst (buf5 k) = LE_block m (le_ktm M)"
      consider (le0) "ktc_pos c' k = 0"
             | (le1) "ktc_pos c' k = 1"
             | (steady) "ktc_pos c' k \<ge> 2"
        by linarith
      thus "ktc_tape c5 k (ktc_pos c5 k) = LE_block m (le_ktm M)"
      proof cases
        case le0
        have "fst (buf5 k) \<noteq> LE_block m (le_ktm M)"
          using buf5_not_le_per_tape[rule_format, OF klt] le0 by blast
        thus ?thesis using l_eq_le by simp
      next
        case le1
        have c5_pos_zero: "ktc_pos c5 k = 0"
          using c5_pos_for_pos1[OF klt le1 dest_ne] .
        have "ktc_tape c5 k 0 = LE_block m (le_ktm M)"
          using tape_c5_zero_le[rule_format, OF klt] by simp
        thus ?thesis using c5_pos_zero by simp
      next
        case steady
        have "fst (buf5 k) \<noteq> LE_block m (le_ktm M)"
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
  have le_compat_ss6_c5: "ae_le_compat_ss6 m M c5"
    using ae_position_link_discharges_ss6[OF inv_ss6 pos_link_c5] .
  obtain c6 where
      step6_sub: "(c5, c6) \<in> ktm_step (ae_delta_ss6_ss7 m M)"
    and step6: "(c5, c6) \<in> ktm_step (alphabet_enlarge_delta m M)"
    using ae_step_ss6_ss7_exists[OF inv_ss6 gamma_c5 buf_gamma_c5
                                    le_compat_ss6_c5] by blast
  have inv_ss7: "ae_inv_ss7 M c6"
    using ae_step_ss6_ss7_invariant[OF vM inv_ss6 step6_sub] .
  have gamma_c6: "ae_tape_in_gamma_block m M c6"
    using ae_step_alphabet_enlarge_gamma_preserve[OF gamma_c5 step6] .
  have buf_gamma_c6: "ae_buffer_in_gamma_block m M c6"
    using ae_step_alphabet_enlarge_buffer_gamma_preserve[OF step6] .
  have c5_idx_ss6: "snd (snd (snd (snd (ktc_state c5)))) = SS6"
    using c5_state by simp
  have aux_45_at_c5: "(c5, c6) \<in> ktm_step (ae_delta_ss4_ss5 m M)
                        \<Longrightarrow> ae_position_link m M c6"
    using ae_pos_link_aux_void_ss4_ss5[where M = M and c_pre = c5 and c_post = c6]
          c5_idx_ss6 by simp
  have aux_56_at_c5: "(c5, c6) \<in> ktm_step (ae_delta_ss5_ss6 m M)
                        \<Longrightarrow> ae_position_link m M c6"
    using ae_pos_link_aux_void_ss5_ss6[where M = M and c_pre = c5 and c_post = c6]
          c5_idx_ss6 by simp
  have aux_78_at_c5: "(c5, c6) \<in> ktm_step (ae_delta_ss7_ss8 m M)
                        \<Longrightarrow> ae_position_link m M c6"
    using ae_pos_link_aux_void_ss7_ss8[where M = M and c_pre = c5 and c_post = c6]
          c5_idx_ss6 by simp
  have pos_link_c6: "ae_position_link m M c6"
    using ae_step_alphabet_enlarge_position_link_preserve[OF pos_link_c5
            step6 aux_45_at_c5 aux_56_at_c5 aux_78_at_c5] .

  \<comment> \<open>Sub-step 5i: SS7\<open>\<rightarrow>\<close>SS8 invocation.  Discharge \<open>ae_le_compat_ss7\<close>
      from \<open>pos_link_c6\<close>; invoke \<open>ae_step_ss7_ss8_exists\<close>.  Buffer
      content is preserved across SS5\<open>\<rightarrow>\<close>SS6\<open>\<rightarrow>\<close>SS7 (the substeps
      change only the tape and stage index, not the buffer component),
      so the \<open>buf5\<close> per-tape non-LE shape transfers to \<open>buf6 = buf5\<close>
      and \<open>c7\<close>'s state inherits the same buffer triple.\<close>
  have le_compat_ss7_c6: "ae_le_compat_ss7 m M c6"
    using ae_position_link_discharges_ss7[OF inv_ss7 pos_link_c6] .
  obtain c7 where
      step7_sub: "(c6, c7) \<in> ktm_step (ae_delta_ss7_ss8 m M)"
    and step7: "(c6, c7) \<in> ktm_step (alphabet_enlarge_delta m M)"
    using ae_step_ss7_ss8_exists[OF inv_ss7 gamma_c6 buf_gamma_c6
                                    le_compat_ss7_c6] by blast
  have inv_ss8: "ae_inv_ss8 M c7"
    using ae_step_ss7_ss8_invariant[OF vM inv_ss7 step7_sub] .
  have gamma_c7: "ae_tape_in_gamma_block m M c7"
    using ae_step_alphabet_enlarge_gamma_preserve[OF gamma_c6 step7] .
  have buf_gamma_c7: "ae_buffer_in_gamma_block m M c7"
    using ae_step_alphabet_enlarge_buffer_gamma_preserve[OF step7] .

  obtain q6 ofs6 buf6 dest6 where
      c5_state_eq: "ktc_state c5 = (q6, ofs6, buf6, dest6, SS6)"
    using inv_ss6 unfolding ae_inv_ss6_def
    by (cases "ktc_state c5") auto
  have c6_state: "ktc_state c6 = (q6, ofs6, buf6, dest6, SS7)"
    using step6_sub c5_state_eq
    by (auto simp: ae_delta_ss6_ss7_def elim: ktm_step.cases)
  have c7_state: "ktc_state c7 = (q6, ofs6, buf6, dest6, SS8)"
    using step7_sub c6_state
    by (auto simp: ae_delta_ss7_ss8_def elim: ktm_step.cases)
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
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1 \<Longrightarrow> dest5 kk = AE_Left
            \<Longrightarrow> ktc_pos c5 kk = 2"
    using c5_move_for_pos1 by simp

  have tape_c5_at_one_pos1:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1
            \<Longrightarrow> ktc_tape c5 kk 1 = fst (snd (buf5 kk))"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume pos_kk: "ktc_pos c' kk = 1"
    show "ktc_tape c5 kk 1 = fst (snd (buf5 kk))"
      using c4_reads_pos1[OF kklt pos_kk] ae_ss5_step_tape(2)[OF step5_sub c4_state kklt]
      by (simp add: ae_ss5_action_buf)
  qed

  \<comment> \<open>Sub-step 5k: c6 trajectory for pos=1 + dest=\<open>AE_Left\<close>.
      \<open>c5_pos = 2\<close>; SS6 reads \<open>ktc_tape c5 k 2\<close> which is off-head
      from SS5's write at \<open>c4_pos = 1\<close>, so \<open>= ktc_tape c4 k 2
      = ktc_tape c' k 2\<close>.  \<open>right_not_le_c'\<close> instantiated at pos=1
      gives \<open>\<noteq> LE_block\<close>.  Buf5 home \<open>\<noteq> LE\<close> (\<open>buf5_not_le_per_tape\<close>).
      \<open>ae_ss6_action\<close>'s else-branch fires with \<open>ds = AE_Left\<close>:
      writes \<open>r\<close>, direction \<open>L\<close>; head lands at \<open>c6_pos = c5_pos - 1
      = 1\<close>.  Plus \<open>tape_c6_zero_le_pos1_dest_left\<close>: cell 0
      is off-head from SS6's write at \<open>c5_pos = 2\<close>, hence \<open>= LE\<close>
      via \<open>tape_c5_zero_le\<close>.\<close>
  have c6_pos_for_pos1_dest_left:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1 \<Longrightarrow> dest5 kk = AE_Left
            \<Longrightarrow> ktc_pos c6 kk = 1"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume pos_kk: "ktc_pos c' kk = 1"
    assume dest_eq: "dest5 kk = AE_Left"
    have c5_kk: "ktc_pos c5 kk = 2"
      using c5_pos_for_pos1_dest_left[OF kklt pos_kk dest_eq] .
    have two_ne_pos_c4: "(2 :: nat) \<noteq> ktc_pos c4 kk"
      using c4_pos kklt pos_kk by simp
    have "ktc_tape c5 kk (ktc_pos c5 kk) \<noteq> LE_block m (le_ktm M)"
      using c5_kk ktm_step_tape_off_head[OF step5 two_ne_pos_c4] tape_c4_eq_c'
            right_not_le_c'[rule_format, of kk] pos_kk
      by (simp add: numeral_2_eq_2)
    then show "ktc_pos c6 kk = 1"
      using ae_ss6_step_tape(1)[OF step6_sub c5_state kklt] c5_kk
            c4_reads_pos1[OF kklt pos_kk] dest_eq
      by (simp add: ae_ss6_action_buf)
  qed

  have tape_c6_zero_le_pos1_dest_left:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1 \<Longrightarrow> dest5 kk = AE_Left
            \<Longrightarrow> ktc_tape c6 kk 0 = LE_block m (le_ktm M)"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume pos_kk: "ktc_pos c' kk = 1"
    assume dest_eq: "dest5 kk = AE_Left"
    have zero_ne_pos_c5: "(0 :: nat) \<noteq> ktc_pos c5 kk"
      using c5_pos_for_pos1_dest_left[OF kklt pos_kk dest_eq] by simp
    have c6_zero_eq_c5:
        "ktc_tape c6 kk 0 = ktc_tape c5 kk 0"
      using ktm_step_tape_off_head[OF step6 zero_ne_pos_c5] .
    have c5_zero_le: "ktc_tape c5 kk 0 = LE_block m (le_ktm M)"
      using tape_c5_zero_le[rule_format, OF kklt] by simp
    show "ktc_tape c6 kk 0 = LE_block m (le_ktm M)"
      using c6_zero_eq_c5 c5_zero_le by simp
  qed

  \<comment> \<open>Sub-step 5l: c7 trajectory for pos=1 + dest=\<open>AE_Left\<close>.  \<open>c6_pos = 1\<close>;
      SS7 reads \<open>ktc_tape c6 k 1 = ktc_tape c5 k 1\<close> (off-head from SS6's
      write at \<open>c5_pos = 2\<close>), and \<open>ktc_tape c5 k 1 = fst (snd (buf5 k))\<close>
      (via \<open>tape_c5_at_one_pos1\<close>) = home buffer slot, \<open>\<noteq> LE\<close>.
      \<open>ae_ss7_action\<close>'s else-branch fires with \<open>ds = AE_Left\<close>:
      writes \<open>a\<close>, direction \<open>L\<close>; \<open>c7_pos = c6_pos - 1 = 0\<close>.  Plus
      \<open>tape_c7_zero_le\<close>: cell 0 off-head from SS7's write at \<open>c6_pos = 1\<close>,
      so \<open>= LE\<close> via \<open>tape_c6_zero_le_pos1_dest_left\<close>.\<close>
  have c7_pos_for_pos1_dest_left:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1 \<Longrightarrow> dest5 kk = AE_Left
            \<Longrightarrow> ktc_pos c7 kk = 0"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume pos_kk: "ktc_pos c' kk = 1"
    assume dest_eq: "dest5 kk = AE_Left"
    have c6_kk: "ktc_pos c6 kk = 1"
      using c6_pos_for_pos1_dest_left[OF kklt pos_kk dest_eq] .
    have one_ne_pos_c5: "(1 :: nat) \<noteq> ktc_pos c5 kk"
      using c5_pos_for_pos1_dest_left[OF kklt pos_kk dest_eq] by simp
    have "ktc_tape c6 kk (ktc_pos c6 kk) = fst (snd (buf5 kk))"
      using c6_kk ktm_step_tape_off_head[OF step6 one_ne_pos_c5]
            tape_c5_at_one_pos1[OF kklt pos_kk]
      by simp
    then show "ktc_pos c7 kk = 0"
      using ae_ss7_step_tape(1)[OF step7_sub c6_state kklt] c6_kk
            c4_reads_pos1[OF kklt pos_kk] buf6_eq_buf5 dest6_eq_dest5 dest_eq
      by (simp add: ae_ss7_action_buf)
  qed

  have tape_c7_zero_le_pos1_dest_left:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1 \<Longrightarrow> dest5 kk = AE_Left
            \<Longrightarrow> ktc_tape c7 kk 0 = LE_block m (le_ktm M)"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume pos_kk: "ktc_pos c' kk = 1"
    assume dest_eq: "dest5 kk = AE_Left"
    have zero_ne_pos_c6: "(0 :: nat) \<noteq> ktc_pos c6 kk"
      using c6_pos_for_pos1_dest_left[OF kklt pos_kk dest_eq] by simp
    have c7_zero_eq_c6:
        "ktc_tape c7 kk 0 = ktc_tape c6 kk 0"
      using ktm_step_tape_off_head[OF step7 zero_ne_pos_c6] .
    show "ktc_tape c7 kk 0 = LE_block m (le_ktm M)"
      using c7_zero_eq_c6 tape_c6_zero_le_pos1_dest_left[OF kklt pos_kk dest_eq]
      by simp
  qed

  \<comment> \<open>Sub-step 5m: \<open>pos_link_c7\<close> + SS8\<open>\<rightarrow>\<close>SS1 invocation.  Mirror
      of \<open>pos_link_c5\<close>: right-slot uniform non-LE from buf5
      (= buf6) regime case-split; SS8 conditional substantive only
      for pos=1 + dest=\<open>AE_Left\<close>, vacuous for pos=0/\<open>\<ge>\<close>2.
      Then \<open>le_compat_ss8\<close> from \<open>pos_link_c7\<close>, invoke
      \<open>ae_step_ss8_ss1_exists\<close>.\<close>
  have pos_link_c7: "ae_position_link m M c7"
  proof -
    have r_not_le: "\<forall>k<k_ktm M. snd (snd (buf6 k)) \<noteq> LE_block m (le_ktm M)"
    proof (intro allI impI)
      fix k
      assume klt: "k < k_ktm M"
      consider (le0) "ktc_pos c' k = 0"
             | (le1) "ktc_pos c' k = 1"
             | (steady) "ktc_pos c' k \<ge> 2"
        by linarith
      thus "snd (snd (buf6 k)) \<noteq> LE_block m (le_ktm M)"
      proof cases
        case le0    thus ?thesis using buf5_not_le_per_tape[rule_format, OF klt] buf6_eq_buf5 by blast
      next
        case le1    thus ?thesis using buf5_not_le_per_tape[rule_format, OF klt] buf6_eq_buf5 by blast
      next
        case steady thus ?thesis using buf5_not_le_per_tape[rule_format, OF klt] buf6_eq_buf5 by blast
      qed
    qed
    have ss8_cond:
        "\<forall>k<k_ktm M. dest6 k = AE_Left
                \<longrightarrow> fst (buf6 k) = LE_block m (le_ktm M)
                \<longrightarrow> ktc_tape c7 k (ktc_pos c7 k) = LE_block m (le_ktm M)"
    proof (intro allI impI)
      fix k
      assume klt: "k < k_ktm M"
      assume dest_eq: "dest6 k = AE_Left"
      assume l_eq_le: "fst (buf6 k) = LE_block m (le_ktm M)"
      have dest5_eq: "dest5 k = AE_Left" using dest_eq dest6_eq_dest5 by simp
      have l_eq_le_buf5: "fst (buf5 k) = LE_block m (le_ktm M)"
        using l_eq_le buf6_eq_buf5 by simp
      consider (le0) "ktc_pos c' k = 0"
             | (le1) "ktc_pos c' k = 1"
             | (steady) "ktc_pos c' k \<ge> 2"
        by linarith
      thus "ktc_tape c7 k (ktc_pos c7 k) = LE_block m (le_ktm M)"
      proof cases
        case le0
        have "fst (buf5 k) \<noteq> LE_block m (le_ktm M)"
          using buf5_not_le_per_tape[rule_format, OF klt] le0 by blast
        thus ?thesis using l_eq_le_buf5 by simp
      next
        case le1
        have c7_pos_k: "ktc_pos c7 k = 0"
          using c7_pos_for_pos1_dest_left[OF klt le1 dest5_eq] .
        have "ktc_tape c7 k 0 = LE_block m (le_ktm M)"
          using tape_c7_zero_le_pos1_dest_left[OF klt le1 dest5_eq] .
        thus ?thesis using c7_pos_k by simp
      next
        case steady
        have "fst (buf5 k) \<noteq> LE_block m (le_ktm M)"
          using buf5_not_le_per_tape[rule_format, OF klt] steady by blast
        thus ?thesis using l_eq_le_buf5 by simp
      qed
    qed
    show ?thesis
      unfolding ae_position_link_def
      using r_not_le ss8_cond c7_state by simp
  qed

  have le_compat_ss8_c7: "ae_le_compat_ss8 m M c7"
    using ae_position_link_discharges_ss8[OF inv_ss8 pos_link_c7] .
  obtain c8 where
      step8_sub: "(c7, c8) \<in> ktm_step (ae_delta_ss8_ss1 m M)"
    and step8: "(c7, c8) \<in> ktm_step (alphabet_enlarge_delta m M)"
    using ae_step_ss8_ss1_exists[OF vM inv_ss8 gamma_c7 buf_gamma_c7
                                    le_compat_ss8_c7] by blast
  \<comment> \<open>Re-express the per-tape \<open>\<And>kk\<close> facts as object-level
      \<open>\<forall>kk\<close> before feeding \<open>that\<close>: the nested meta-implication
      under the obtains witness binders defeats elim-resolution at the call
      site.  The call site recovers the
      \<open>\<And>kk\<close> form via \<open>[rule_format]\<close>.\<close>
  have c4_pos_all: "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c4 kk = ktc_pos c' kk"
    using c4_pos by blast
  have c5_pos_for_pos1_all:
      "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk \<noteq> AE_Left
       \<longrightarrow> ktc_pos c5 kk = 0"
    using c5_pos_for_pos1 by blast
  have c5_pos_for_pos1_dest_left_all:
      "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
       \<longrightarrow> ktc_pos c5 kk = 2"
    using c5_pos_for_pos1_dest_left by blast
  have tape_c5_at_one_pos1_all:
      "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1
       \<longrightarrow> ktc_tape c5 kk 1 = fst (snd (buf5 kk))"
    using tape_c5_at_one_pos1 by blast
  have c6_pos_for_pos1_dest_left_all:
      "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
       \<longrightarrow> ktc_pos c6 kk = 1"
    using c6_pos_for_pos1_dest_left by blast
  have c7_pos_for_pos1_dest_left_all:
      "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
       \<longrightarrow> ktc_pos c7 kk = 0"
    using c7_pos_for_pos1_dest_left by blast
  have tape_c7_zero_le_pos1_dest_left_all:
      "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
       \<longrightarrow> ktc_tape c7 kk 0 = LE_block m (le_ktm M)"
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
