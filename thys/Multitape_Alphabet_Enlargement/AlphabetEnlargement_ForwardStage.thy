theory AlphabetEnlargement_ForwardStage
  imports AlphabetEnlargement_ForwardStep
begin

subsection \<open>Per-tape unified forward stage\<close>

text \<open>The primary forward-stage statement, feeding
  \<open>ae_simulation_phase_step_count\<close> (theory
  \<open>AlphabetEnlargement_Acceptance\<close>).  Tip of the forward-stage
  chain \<open>ForwardCells \<rightarrow> ForwardStep \<rightarrow> ForwardStage\<close>: it
  applies the SS5\<open>\<rightarrow>\<close>SS8 super-step
  (\<open>ae_forward_stage_step_chain\<close>) and the per-tape reconstruction
  leaves (theory \<open>AlphabetEnlargement_ForwardCells\<close>) to advance the
  simulation by one \<open>M\<close>-step.

  Each tape \<open>k\<close> picks its regime (steady / le1 / le0)
  independently from its own \<open>mt_pos c' k\<close>; mixed
  configurations across tapes are handled natively, with no
  uniform-regime case-split at the call site.  Per-tape dispatch is
  mandatory: the regimes can differ from tape to tape.

  The \<open>no_le_per_tape\<close> hypothesis bundles a per-tape
  LE-free window whose start and width depend on the tape's
  block position: \<open>3c\<close>-cell window starting at the
  left neighbour for steady tapes, \<open>2c\<close>-cell window
  starting at position 1 for le1 tapes, \<open>c\<close>-cell window
  starting at position 1 for le0 tapes.  Discharged at the call
  site via substrate's \<open>valid_reach_LE_only_pos0_mttm\<close>
  for any reach-from-init configuration.

  The displacement disjunct's leftward branch is conditioned on
  \<open>mt_pos c' kk > 0\<close> — le0 tapes cannot move left from
  block 0.\<close>

lemma ae_simulates_forward_stage_general:
  fixes M :: "('q, 'a) mttm"
    and cM cM_k :: "('a, 'q) mt_config"
    and c' :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) mt_config"
    and k :: nat
  assumes vM:        "valid_mttm M"
      and lu:        "le_unique M"
      and sim:       "ae_simulates M cM c'"
      and qM_in_Q:   "mt_state cM \<in> Q_tm M"
      and q_neq_t:   "mt_state cM \<noteq> t_tm M"
      and q_neq_r:   "mt_state cM \<noteq> r_tm M"
      and buf_gamma: "ae_buffer_in_gamma_block M c'"
      and k_le:      "k \<le> card (UNIV :: 'c set)"
      and trace:     "(cM, cM_k) \<in> mttm_step (delta_tm M) ^^ k"
      and end_or_halt:
            "k = card (UNIV :: 'c set)
              \<or> mt_state cM_k \<in> {t_tm M, r_tm M}"
      and le_anchor:
            "\<forall>k<k_tm M. mt_tape c' k 0 = LE_block (le_tm M)"
      and le_neq_bl:
            "le_tm M \<noteq> bl_tm M"
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
  obtains c'' c1 c2 c3 c4 c5 c6 c7 ofs_f buf_f dest_f where
      "(c', c'') \<in> mttm_step (alphabet_enlarge_delta M) ^^ 8"
    and "ae_simulates M cM_k c''"
    and "ae_buffer_in_gamma_block M c''"
    and "\<forall>kk<k_tm M. mt_tape c'' kk 0 = LE_block (le_tm M)"
    \<comment> \<open>SS5 exposure for the det-free reverse arm
        (\<open>nae_sim_proto\<close>): the full substep chain, the SS5 state
        shape + window correspondence in \<open>(dest, ofs)\<close> bp form, and
        the buffer \<open>\<gamma>\<close>-block carrying the frozen inactive
        tails.\<close>
    and "(c', c1) \<in> mttm_step (ae_delta_ss1_ss2 M)"
    and "(c1, c2) \<in> mttm_step (ae_delta_ss2_ss3 M)"
    and "(c2, c3) \<in> mttm_step (ae_delta_ss3_ss4 M)"
    and "(c3, c4) \<in> mttm_step (ae_delta_ss4_ss5 M)"
    and "(c4, c5) \<in> mttm_step (ae_delta_ss5_ss6 M)"
    and "(c5, c6) \<in> mttm_step (ae_delta_ss6_ss7 M)"
    and "(c6, c7) \<in> mttm_step (ae_delta_ss7_ss8 M)"
    and "(c7, c'') \<in> mttm_step (ae_delta_ss8_ss1 M)"
    and "mt_state c4 = (mt_state cM_k, ofs_f, buf_f, dest_f, SS5)"
    and "\<forall>kk<k_tm M. ae_window_invariant_general
              (mt_tape cM_k kk) (mt_pos cM_k kk)
              (dest_f kk, ofs_f kk) (buf_f kk) (mt_pos c' kk) (le_tm M)"
    and "ae_buffer_in_gamma_block M c4"
proof -
  \<comment> \<open>Unpack \<open>ae_simulates\<close> at SS1 entry via the shared
      regime-agnostic helper.  No regime-specific hypothesis enters
      here — the unpack is uniform across steady / le1 / le0.\<close>
  obtain qM' ofs buf dest where
      c'_state: "mt_state c' = (qM', ofs, buf, dest, SS1)"
    and qM_eq: "mt_state cM = qM'"
    and qM'_in_Q: "qM' \<in> Q_tm M"
    and qM'_neq_t: "qM' \<noteq> t_tm M"
    and qM'_neq_r: "qM' \<noteq> r_tm M"
    and tape_corr: "\<forall>k<k_tm M. ae_tape_correspondence (le_tm M)
                          (mt_tape cM k) (mt_tape c' k)"
    and pos_corr:  "\<forall>k<k_tm M. mt_pos cM k = ae_decode_pos (mt_pos c' k) (ofs k)"
    and gamma_c':  "ae_tape_in_gamma_block M c'"
    and inv_ss1:   "ae_inv_ss1 M c'"
    and pos_link_c': "ae_position_link M c'"
    by (rule ae_forward_stage_unpack_sim[OF sim qM_in_Q q_neq_t q_neq_r])

  \<comment> \<open>Buffer-load substeps SS1\<open>\<rightarrow>\<close>SS2\<open>\<rightarrow>\<close>SS3
      \<open>\<rightarrow>\<close>SS4 via the shared regime-agnostic load-chain
      helper.  Yields the SS4-entry config \<open>c3\<close> together with
      its SS4 invariant, gamma and buffer-gamma side-bands, state
      preservation, and position-link side-band.  Each per-tape
      branch will refine the buffer-content characterisation
      separately in the regime-aware substeps that follow.\<close>
  obtain c1 c2 c3 where
      step1_sub: "(c', c1) \<in> mttm_step (ae_delta_ss1_ss2 M)"
    and step1:   "(c', c1) \<in> mttm_step (alphabet_enlarge_delta M)"
    and step2_sub: "(c1, c2) \<in> mttm_step (ae_delta_ss2_ss3 M)"
    and step2:   "(c1, c2) \<in> mttm_step (alphabet_enlarge_delta M)"
    and step3_sub: "(c2, c3) \<in> mttm_step (ae_delta_ss3_ss4 M)"
    and step3:   "(c2, c3) \<in> mttm_step (alphabet_enlarge_delta M)"
    and inv_ss4: "ae_inv_ss4 M c3"
    and gamma_c3:    "ae_tape_in_gamma_block M c3"
    and buf_gamma_c3: "ae_buffer_in_gamma_block M c3"
    and c3_fst_eq:   "fst (mt_state c3) = qM'"
    and pos_link_c3: "ae_position_link M c3"
    by (rule ae_forward_stage_load_chain[OF vM c'_state inv_ss1 gamma_c'
                                            buf_gamma pos_link_c'
                                            qM'_neq_t qM'_neq_r])
  have c3_fst_neq_t: "fst (mt_state c3) \<noteq> t_tm M"
    using c3_fst_eq qM'_neq_t by simp
  have c3_fst_neq_r: "fst (mt_state c3) \<noteq> r_tm M"
    using c3_fst_eq qM'_neq_r by simp

  \<comment> \<open>Per-tape home-cell classification: each tape \<open>k\<close>
      either has \<open>mt_pos c' k = 0\<close> with home = \<open>LE_block\<close>
      (forward arm via \<open>le_anchor\<close>) or
      \<open>mt_pos c' k \<ge> 1\<close> with home \<open>\<noteq> LE_block\<close>
      (backward arm via \<open>ae_tape_correspondence\<close> at the home
      block with witness \<open>c_idx x = 0\<close>, projecting
      \<open>no_le_per_tape\<close> to the regime branch).\<close>
  have c_ge_1: "1 \<le> card (UNIV :: 'c set)"
    using c_idx_lt_card[of "SOME x :: 'c. True"] by simp
  have c_eq_len: "card (UNIV :: 'c set) = length (enum_class.enum :: 'c list)"
    using enum_class.UNIV_enum enum_class.enum_distinct
    by (metis distinct_card length_remdups_card_conv set_remdups)

  have home_classification:
      "\<forall>k<k_tm M. (mt_pos c' k = 0
              \<longrightarrow> mt_tape c' k (mt_pos c' k) = LE_block (le_tm M))
           \<and> (mt_pos c' k \<ge> 1
              \<longrightarrow> mt_tape c' k (mt_pos c' k) \<noteq> LE_block (le_tm M))"
    by (rule ae_home_classification[OF le_anchor no_le_per_tape tape_corr])

  \<comment> \<open>SS4-entry characterisation via the per-tape unified
      buffer-chars helper.  Buffer at SS4 is per-tape: tapes at
      \<open>pos = 0\<close> get \<open>(bl_block, LE_block, snd (snd (buf k)))\<close>
      (the LE-arm shape from \<open>ae_ss1_to_ss4_buffer_chars_le0\<close>);
      tapes at \<open>pos \<ge> 1\<close> get \<open>(mt_tape c' k (pos - 1),
      mt_tape c' k pos, snd (snd (buf k)))\<close> (the steady-arm shape
      from \<open>ae_ss1_to_ss4_buffer_chars\<close>).  Tape and position
      conclusions are uniform across regimes.\<close>
  have c3_state:
      "mt_state c3 = (qM', ofs,
                       (\<lambda>k. if k < k_tm M
                              then (if mt_pos c' k = 0
                                      then (bl_block (bl_tm M),
                                            LE_block (le_tm M),
                                            snd (snd (buf k)))
                                      else (mt_tape c' k (mt_pos c' k - 1),
                                            mt_tape c' k (mt_pos c' k),
                                            snd (snd (buf k))))
                              else init_buffer (le_tm M) k),
                       dest, SS4)"
    using ae_ss1_to_ss4_buffer_chars_general(1)[OF c'_state step1_sub
                                                   step2_sub step3_sub
                                                   home_classification] .
  have c3_tape: "mt_tape c3 = mt_tape c'"
    using ae_ss1_to_ss4_buffer_chars_general(2)[OF c'_state step1_sub
                                                   step2_sub step3_sub
                                                   home_classification] .
  have c3_pos: "\<And>k. k < k_tm M \<Longrightarrow> mt_pos c3 k = mt_pos c' k + 1"
    using ae_ss1_to_ss4_buffer_chars_general(3)[OF c'_state step1_sub
                                                   step2_sub step3_sub
                                                   home_classification] .

  \<comment> \<open>Per-tape SS4 window invariant via the unified
      from-correspondence helper.  The buffer triple is the
      regime-aware shape that \<open>ae_delta_ss4_ss5\<close> reads from
      \<open>c3\<close>: left and home from the SS4-entry per-tape buffer,
      right freshly read at \<open>mt_pos c' k + 1\<close>.  The conclusion
      is the per-tape \<open>ae_window_invariant_general\<close>, indexed
      by \<open>mt_pos c' k\<close> (the frozen regime selector).\<close>
  have window_at_ss4:
      "\<forall>k<k_tm M. ae_window_invariant_general
              (mt_tape cM k) (mt_pos cM k)
              (AE_Home, ofs k)
              (if mt_pos c' k = 0
                 then (bl_block (bl_tm M),
                       LE_block (le_tm M),
                       mt_tape c' k 1)
               else if mt_pos c' k = 1
                 then (mt_tape c' k 0,
                       mt_tape c' k 1,
                       mt_tape c' k 2)
               else (mt_tape c' k (mt_pos c' k - 1),
                     mt_tape c' k (mt_pos c' k),
                     mt_tape c' k (mt_pos c' k + 1)))
              (mt_pos c' k)
              (le_tm M)"
    using ae_ss4_window_from_correspondence_general[OF sim c'_state
                                                       le_anchor
                                                       no_le_per_tape] .

  \<comment> \<open>Re-express \<open>cM\<close> via \<open>Config\<^sub>M\<close> to
      match the trace lemma's toolkit hypothesis shape (arm-uniform
      with le0 / le1 / steady).  Surfaces \<open>ts_cM = mt_tape cM\<close>
      and \<open>n_cM = mt_pos cM\<close> for direct substitution into the
      trace, no-LE and window hypotheses.\<close>
  obtain ts_cM n_cM where cM_eq:
      "cM = Config\<^sub>M qM' ts_cM n_cM"
    using qM_eq by (cases cM) auto
  have ts_cM_eq: "ts_cM = mt_tape cM" using cM_eq by simp
  have n_cM_eq: "n_cM = mt_pos cM" using cM_eq by simp

  \<comment> \<open>Trace toolkit: rewrite the precondition's
      \<open>(cM, cM_k) \<in> mttm_step^^k\<close> shape into the trace
      lemma's
      \<open>(Config\<^sub>M (fst (mt_state c3)) ts_cM n_cM, cM_k) \<in> \<dots>\<close>
      form, via \<open>cM_eq\<close> and \<open>c3_fst_eq\<close>.\<close>
  have trace_toolkit:
      "(Config\<^sub>M (fst (mt_state c3)) ts_cM n_cM, cM_k)
          \<in> mttm_step (delta_tm M) ^^ k"
    using trace cM_eq c3_fst_eq by simp

  \<comment> \<open>No-LE toolkit: rephrase \<open>no_le_per_tape\<close> in terms
      of \<open>ts_cM\<close> (= \<open>mt_tape cM\<close>) for the trace lemma's
      \<open>tsM\<close>-parameter.  Same shape modulo the rewrite of
      \<open>mt_tape cM\<close> to \<open>ts_cM\<close>.\<close>
  have no_le_toolkit_general:
      "\<forall>kk. (mt_pos c' kk = 0
              \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                        \<longrightarrow> ts_cM kk (Suc i) \<noteq> le_tm M))
           \<and> (mt_pos c' kk = 1
                \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                          \<longrightarrow> ts_cM kk (Suc i) \<noteq> le_tm M))
           \<and> (mt_pos c' kk \<ge> 2
                \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                          \<longrightarrow> ts_cM kk
                                ((mt_pos c' kk - 2) * card (UNIV :: 'c set)
                                  + 1 + i)
                              \<noteq> le_tm M))"
    using no_le_per_tape ts_cM_eq by simp

  \<comment> \<open>Left-slot guard for pos=0 tapes at \<open>c3\<close>: the SS4-entry
      left slot for tapes at block 0 is \<open>bl_block (bl_tm M)\<close>
      (per \<open>c3_state\<close>'s if-branch), distinct from
      \<open>LE_block (le_tm M)\<close> via \<open>le_neq_bl\<close>.  Le1 and
      steady tapes carry no obligation here (the trace lemma's
      hypothesis is \<open>pos k = 0 \<longrightarrow> \<dots>\<close>).\<close>
  have bl_neq_le:
      "(bl_block (bl_tm M) :: 'c \<Rightarrow> 'a) \<noteq> LE_block (le_tm M)"
  proof
    assume eq: "(bl_block (bl_tm M) :: 'c \<Rightarrow> 'a) = LE_block (le_tm M)"
    have "bl_block (bl_tm M) (SOME x :: 'c. True)
            = LE_block (le_tm M) (SOME x :: 'c. True)"
      using eq by simp
    hence "bl_tm M = le_tm M"
      unfolding bl_block_def LE_block_def by simp
    with le_neq_bl show False by simp
  qed
  have left_not_le_c3_toolkit:
      "case mt_state c3 of (_, _, b, _, _) \<Rightarrow>
           \<forall>kk<k_tm M. mt_pos c' kk = 0
                 \<longrightarrow> fst (b kk) \<noteq> LE_block (le_tm M)"
    using c3_state bl_neq_le by simp

  \<comment> \<open>Window-invariant toolkit: convert \<open>window_at_ss4\<close>
      from its \<open>c'\<close>-tape if-then-else form into the
      \<open>case mt_state c3\<close> form expected by the trace lemma.
      Per-tape regime case-split on \<open>mt_pos c' kk\<close>; in each
      branch, \<open>c3_state\<close>'s if-then-else and the
      \<open>window_at_ss4\<close> nested-if reduce to the same buffer triple.\<close>
  have window_toolkit_general:
      "\<forall>kk<k_tm M. ae_window_invariant_general (ts_cM kk) (n_cM kk)
              (case mt_state c3 of (_, ofs', _, _, _)
                  \<Rightarrow> (AE_Home, ofs' kk))
              (case mt_state c3 of (_, _, buf', _, _)
                  \<Rightarrow> (fst (buf' kk), fst (snd (buf' kk)),
                      mt_tape c3 kk (mt_pos c3 kk)))
              (mt_pos c' kk) (le_tm M)"
  proof (intro allI impI)
    fix kk
    assume kklt: "kk < k_tm M"
    have c3_buf_triple:
        "(case mt_state c3 of (_, _, buf', _, _) \<Rightarrow>
              (fst (buf' kk), fst (snd (buf' kk)),
               mt_tape c3 kk (mt_pos c3 kk)))
          = (if mt_pos c' kk = 0
                then (bl_block (bl_tm M), LE_block (le_tm M),
                      mt_tape c' kk (mt_pos c' kk + 1))
             else (mt_tape c' kk (mt_pos c' kk - 1),
                   mt_tape c' kk (mt_pos c' kk),
                   mt_tape c' kk (mt_pos c' kk + 1)))"
      using c3_state c3_tape c3_pos kklt by simp
    have c3_ofs_pair:
        "(case mt_state c3 of (_, ofs', _, _, _) \<Rightarrow> (AE_Home, ofs' kk))
          = (AE_Home, ofs kk)"
      using c3_state by simp
    have win_at_ss4_kk:
        "ae_window_invariant_general (mt_tape cM kk) (mt_pos cM kk)
              (AE_Home, ofs kk)
              (if mt_pos c' kk = 0
                 then (bl_block (bl_tm M), LE_block (le_tm M),
                       mt_tape c' kk 1)
               else if mt_pos c' kk = 1
                 then (mt_tape c' kk 0,
                       mt_tape c' kk 1,
                       mt_tape c' kk 2)
               else (mt_tape c' kk (mt_pos c' kk - 1),
                     mt_tape c' kk (mt_pos c' kk),
                     mt_tape c' kk (mt_pos c' kk + 1)))
              (mt_pos c' kk) (le_tm M)"
      using window_at_ss4 kklt by blast
    consider (le0) "mt_pos c' kk = 0"
           | (le1) "mt_pos c' kk = 1"
           | (steady) "mt_pos c' kk \<ge> 2"
      by linarith
    thus "ae_window_invariant_general (ts_cM kk) (n_cM kk)
            (case mt_state c3 of (_, ofs', _, _, _)
                \<Rightarrow> (AE_Home, ofs' kk))
            (case mt_state c3 of (_, _, buf', _, _)
                \<Rightarrow> (fst (buf' kk), fst (snd (buf' kk)),
                    mt_tape c3 kk (mt_pos c3 kk)))
            (mt_pos c' kk) (le_tm M)"
    proof cases
      case le0
      show ?thesis
        using win_at_ss4_kk c3_buf_triple c3_ofs_pair le0
              ts_cM_eq n_cM_eq
        by simp
    next
      case le1
      show ?thesis
        using win_at_ss4_kk c3_buf_triple c3_ofs_pair le1
              ts_cM_eq n_cM_eq
        by (simp add: numeral_2_eq_2)
    next
      case steady
      have pos_ne_0: "mt_pos c' kk \<noteq> 0" using steady by simp
      have pos_ne_1: "mt_pos c' kk \<noteq> 1" using steady by simp
      show ?thesis
        using win_at_ss4_kk c3_buf_triple c3_ofs_pair pos_ne_0 pos_ne_1
              ts_cM_eq n_cM_eq
        by simp
    qed
  qed

  \<comment> \<open>Invoke the trace-driven SS4\<open>\<rightarrow>\<close>SS5 helper
      for the per-tape unified case.  The trace lemma's
      \<open>pos\<close> parameter is inferred from
      \<open>window_toolkit_general\<close>'s \<open>mt_pos c' kk\<close>
      regime selector, giving \<open>pos := mt_pos c'\<close>.\<close>
  obtain c4 where
      step4_sub: "(c3, c4) \<in> mttm_step (ae_delta_ss4_ss5 M)"
    and step4: "(c3, c4) \<in> mttm_step (alphabet_enlarge_delta M)"
    and c4_q_out: "case mt_state c4 of (q_out, _, _, _, _)
                     \<Rightarrow> q_out = mt_state cM_k"
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
    and c4_window_general:
            "case mt_state c4 of (_, ofs', buf', dest', _) \<Rightarrow>
                 \<forall>kk<k_tm M. ae_window_invariant_general
                       (mt_tape cM_k kk) (mt_pos cM_k kk)
                       (dest' kk, ofs' kk) (buf' kk)
                       (mt_pos c' kk) (le_tm M)"
    using ae_step_ss4_ss5_exists_general_trace[OF vM lu inv_ss4 gamma_c3
                                                  buf_gamma_c3
                                                  c3_fst_neq_t c3_fst_neq_r
                                                  window_toolkit_general
                                                  no_le_toolkit_general
                                                  trace_toolkit k_le
                                                  end_or_halt
                                                  left_not_le_c3_toolkit]
    by blast

  \<comment> \<open>Sub-step 5a: SS5\<open>\<rightarrow>\<close>SS6 invocation.  Arm-uniform with
      the three per-regime variants: \<open>inv_ss5\<close>, gamma + buf-gamma
      at \<open>c4\<close> propagate from \<open>c3\<close> via the arm-agnostic
      preservation lemmas.  \<open>ae_step_ss5_ss6_exists\<close> takes only
      these three (no pos-link required at SS5), so \<open>c5\<close> is
      obtained directly.\<close>
  have inv_ss5: "ae_inv_ss5 M c4"
    using ae_step_ss4_ss5_invariant[OF vM inv_ss4 step4_sub] .
  have gamma_c4: "ae_tape_in_gamma_block M c4"
    using ae_step_alphabet_enlarge_gamma_preserve[OF gamma_c3 step4] .
  have buf_gamma_c4: "ae_buffer_in_gamma_block M c4"
    using ae_step_alphabet_enlarge_buffer_gamma_preserve[OF vM buf_gamma_c3
                                                            gamma_c3 step4] .
  \<comment> \<open>The SS5\<open>\<rightarrow>\<close>SS8 super-step: extracted to
      \<open>ae_forward_stage_step_chain\<close>.  Re-binds the 12 intermediate
      witnesses and 29 named facts the per-tape reconstruction below
      consumes.\<close>
  obtain c5 q5 ofs5 buf5 dest5 c6 c7 q6 ofs6 buf6 dest6 c8
    where step5_sub: "(c4, c5) \<in> mttm_step (ae_delta_ss5_ss6 M)"
      and step5: "(c4, c5) \<in> mttm_step (alphabet_enlarge_delta M)"
      and c4_state: "mt_state c4 = (q5, ofs5, buf5, dest5, SS5)"
      and c5_state: "mt_state c5 = (q5, ofs5, buf5, dest5, SS6)"
      and tape_c4_eq_c': "mt_tape c4 = mt_tape c'"
      and buf5_not_le_per_tape:
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
      and right_not_le_c':
      "\<forall>k. mt_tape c' k (mt_pos c' k + 1) \<noteq> LE_block (le_tm M)"
      and c4_pos_all: "\<forall>kk. kk < k_tm M \<longrightarrow> mt_pos c4 kk = mt_pos c' kk"
      and tape_c5_zero_le: "\<forall>k<k_tm M. mt_tape c5 k 0 = LE_block (le_tm M)"
      and c5_pos_for_pos1_all:
      "\<forall>kk. kk < k_tm M \<longrightarrow> mt_pos c' kk = 1 \<longrightarrow> dest5 kk \<noteq> AE_Left
      \<longrightarrow> mt_pos c5 kk = 0"
      and step6_sub: "(c5, c6) \<in> mttm_step (ae_delta_ss6_ss7 M)"
      and step6: "(c5, c6) \<in> mttm_step (alphabet_enlarge_delta M)"
      and step7_sub: "(c6, c7) \<in> mttm_step (ae_delta_ss7_ss8 M)"
      and step7: "(c6, c7) \<in> mttm_step (alphabet_enlarge_delta M)"
      and gamma_c7: "ae_tape_in_gamma_block M c7"
      and buf_gamma_c7: "ae_buffer_in_gamma_block M c7"
      and c6_state: "mt_state c6 = (q6, ofs6, buf6, dest6, SS7)"
      and c7_state: "mt_state c7 = (q6, ofs6, buf6, dest6, SS8)"
      and buf6_eq_buf5: "buf6 = buf5"
      and q6_eq_q5: "q6 = q5"
      and ofs6_eq_ofs5: "ofs6 = ofs5"
      and dest6_eq_dest5: "dest6 = dest5"
      and c5_pos_for_pos1_dest_left_all:
      "\<forall>kk. kk < k_tm M \<longrightarrow> mt_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
      \<longrightarrow> mt_pos c5 kk = 2"
      and tape_c5_at_one_pos1_all:
      "\<forall>kk. kk < k_tm M \<longrightarrow> mt_pos c' kk = 1
      \<longrightarrow> mt_tape c5 kk 1 = fst (snd (buf5 kk))"
      and c6_pos_for_pos1_dest_left_all:
      "\<forall>kk. kk < k_tm M \<longrightarrow> mt_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
      \<longrightarrow> mt_pos c6 kk = 1"
      and c7_pos_for_pos1_dest_left_all:
      "\<forall>kk. kk < k_tm M \<longrightarrow> mt_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
      \<longrightarrow> mt_pos c7 kk = 0"
      and tape_c7_zero_le_pos1_dest_left_all:
      "\<forall>kk. kk < k_tm M \<longrightarrow> mt_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
      \<longrightarrow> mt_tape c7 kk 0 = LE_block (le_tm M)"
      and step8_sub: "(c7, c8) \<in> mttm_step (ae_delta_ss8_ss1 M)"
      and step8: "(c7, c8) \<in> mttm_step (alphabet_enlarge_delta M)"
    by (rule ae_forward_stage_step_chain[OF vM le_anchor no_le_per_tape
          tape_corr step1_sub step2_sub step3_sub c_ge_1 c_eq_len
          home_classification c3_pos bl_neq_le step4_sub c4_buf_not_le_per_tape
          inv_ss5 gamma_c4 buf_gamma_c4])
  \<comment> \<open>Recover the \<open>\<And>kk\<close> form of the per-tape facts
      (the chain helper exposes them as \<open>\<forall>kk\<close> to survive
      elim-resolution) so the per-tape
      reconstruction below uses them unchanged.\<close>
  note c4_pos = c4_pos_all[rule_format]
  note c5_pos_for_pos1 = c5_pos_for_pos1_all[rule_format]
  note c5_pos_for_pos1_dest_left = c5_pos_for_pos1_dest_left_all[rule_format]
  note tape_c5_at_one_pos1 = tape_c5_at_one_pos1_all[rule_format]
  note c6_pos_for_pos1_dest_left = c6_pos_for_pos1_dest_left_all[rule_format]
  note c7_pos_for_pos1_dest_left = c7_pos_for_pos1_dest_left_all[rule_format]
  note tape_c7_zero_le_pos1_dest_left = tape_c7_zero_le_pos1_dest_left_all[rule_format]
  \<comment> \<open>Sub-step 6a: chain composition + c8 state shape +
      arm-uniform reconstruction facts (\<open>sim_i\<close>, \<open>sim_ii\<close>, gamma, buf-gamma).
      The chain composition uses \<open>relpow_Suc_I\<close> Suc-by-Suc; the c8
      state shape is the halt-aware \<open>?stage8\<close> let-term from
      \<open>ae_delta_ss8_ss1\<close>.\<close>
  let ?rel = "mttm_step (alphabet_enlarge_delta M)"
  have chain1: "(c', c1) \<in> ?rel ^^ Suc 0"
    using step1 by simp
  have chain2: "(c', c2) \<in> ?rel ^^ Suc (Suc 0)"
    using chain1 step2 by (rule relpow_Suc_I)
  have chain3: "(c', c3) \<in> ?rel ^^ Suc (Suc (Suc 0))"
    using chain2 step3 by (rule relpow_Suc_I)
  have chain4: "(c', c4) \<in> ?rel ^^ Suc (Suc (Suc (Suc 0)))"
    using chain3 step4 by (rule relpow_Suc_I)
  have chain5: "(c', c5) \<in> ?rel ^^ Suc (Suc (Suc (Suc (Suc 0))))"
    using chain4 step5 by (rule relpow_Suc_I)
  have chain6: "(c', c6) \<in> ?rel ^^ Suc (Suc (Suc (Suc (Suc (Suc 0)))))"
    using chain5 step6 by (rule relpow_Suc_I)
  have chain7:
      "(c', c7) \<in> ?rel ^^ Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))"
    using chain6 step7 by (rule relpow_Suc_I)
  have chain8_suc:
      "(c', c8) \<in> ?rel ^^ Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))"
    using chain7 step8 by (rule relpow_Suc_I)
  have chain8: "(c', c8) \<in> ?rel ^^ 8"
    using chain8_suc by (simp add: numeral_eq_Suc)

  let ?stage8 = "if q6 \<in> {t_tm M, r_tm M}
                 then init_stage (le_tm M)
                 else (ofs6, buf6, init_dest, SS1)"
  have c8_state: "mt_state c8 = (q6, ?stage8)"
    using step8_sub c7_state
    by (auto simp: ae_delta_ss8_ss1_def elim: mttm_step.cases)

  \<comment> \<open>\<open>sim_i\<close>: state-tuple disjunction at \<open>c8\<close>.  The SS8\<open>\<rightarrow>\<close>SS1
      rule's \<open>?stage'\<close> case-splits on \<open>q \<in> {t_tm M, r_tm M}\<close>:
      halt routes to \<open>init_stage le\<close>, non-halt to \<open>(ofs, buf, init_dest, SS1)\<close>.
      The disjunction is XOR-style, with each branch matching one of the
      \<open>ae_simulates\<close>-defining disjuncts directly.\<close>
  have sim_i_c8:
      "case mt_state c8 of (qq8, ofs8, buf8, dest8, idx8) \<Rightarrow>
           (idx8 = SS1 \<and> qq8 \<notin> {t_tm M, r_tm M})
         \<or> (qq8 \<in> {t_tm M, r_tm M}
              \<and> (ofs8, buf8, dest8, idx8) = init_stage (le_tm M))"
  proof (cases "q6 \<in> {t_tm M, r_tm M}")
    case True
    have shape: "?stage8 = init_stage (le_tm M)" using True by simp
    have "mt_state c8 = (q6, init_stage (le_tm M))"
      using c8_state shape by simp
    thus ?thesis using True by (simp add: init_stage_def)
  next
    case False
    have shape: "?stage8 = (ofs6, buf6, init_dest, SS1)" using False by simp
    have "mt_state c8 = (q6, ofs6, buf6, init_dest, SS1)"
      using c8_state shape by simp
    thus ?thesis using False by simp
  qed

  \<comment> \<open>\<open>sim_ii\<close>: \<open>mt_state cM_k = q6\<close>.  q5 = q6 (no q changes through
      SS5/SS6/SS7); q5 = c4's M-state projection = \<open>mt_state cM_k\<close>
      (via \<open>c4_q_out\<close> from the trace lemma).\<close>
  have q5_eq_q6: "q5 = q6" using q6_eq_q5 by simp
  have q5_eq_cM_k: "q5 = mt_state cM_k"
    using c4_q_out c4_state by simp
  have q6_eq_cM_k: "q6 = mt_state cM_k"
    using q5_eq_q6 q5_eq_cM_k by simp
  have sim_ii_c8:
      "case mt_state c8 of (qq8, _, _, _, _) \<Rightarrow> mt_state cM_k = qq8"
    using c8_state q6_eq_cM_k by simp

  \<comment> \<open>gamma + buf-gamma at \<open>c8\<close>: chained preservation.\<close>
  have gamma_c8: "ae_tape_in_gamma_block M c8"
    using ae_step_alphabet_enlarge_gamma_preserve[OF gamma_c7 step8] .
  have buf_gamma_c8: "ae_buffer_in_gamma_block M c8"
    using ae_step_alphabet_enlarge_buffer_gamma_preserve[OF vM buf_gamma_c7
                                                            gamma_c7 step8] .

  \<comment> \<open>Sub-step 6b1: per-tape regime-aware \<open>cM_k\<close>-side window
      invariant.  Projection of \<open>c4_window_general\<close> through
      \<open>c4_state\<close> = \<open>(q5, ofs5, buf5, dest5, SS5)\<close>: each tape
      \<open>kk\<close> has the hybrid \<open>ae_window_invariant_general\<close>
      indexed by its regime selector \<open>mt_pos c' kk\<close>.  This
      single fact unpacks into le0/le1/steady sub-invariants
      per tape via the definition's case-split on \<open>pos = 0\<close>,
      \<open>pos = 1\<close>, \<open>pos \<ge> 2\<close>.\<close>
  have cM_k_window_general:
      "\<forall>kk<k_tm M. ae_window_invariant_general
              (mt_tape cM_k kk) (mt_pos cM_k kk)
              (dest5 kk, ofs5 kk) (buf5 kk)
              (mt_pos c' kk) (le_tm M)"
    using c4_window_general c4_state by simp

  \<comment> \<open>Sub-step 6b1: \<open>cM_k\<close>'s tape at position 0 is
      \<open>LE_block (le_tm M)\<close>, equivalently \<open>le_tm M\<close> as a
      bare tape value — the s=0 conjunct of \<open>ae_tape_correspondence\<close>.
      Per-tape regime case-split: pos=0 and pos=1 extract the
      \<open>tM 0 = le\<close> clause directly from the regime-specific
      window invariant (\<open>ae_window_invariant_le0_def\<close> and
      \<open>_le1_def\<close>); pos\<open>\<ge>\<close>2 has no such clause in its
      window invariant (which only constrains
      \<open>[p_start, p_start + 3c)\<close>) so the M-side entry
      correspondence at s=0 (\<open>mt_tape cM kk 0 = le\<close>) chains
      with \<open>mttm_relpow_tape_off_window\<close>'s zero preservation
      (\<open>mt_pos cM kk \<ge> c + 1 > k\<close> for pos\<open>\<ge>\<close>2 tapes).\<close>
  let ?c = "card (UNIV :: 'c set)"
  have c_ge1: "(1 :: nat) \<le> ?c"
    using c_idx_lt_card[of "SOME x :: 'c. True"] by linarith
  have cM_k_zero: "\<And>kk. kk < k_tm M \<Longrightarrow> mt_tape cM_k kk 0 = le_tm M"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    show "mt_tape cM_k kk 0 = le_tm M"
    proof (cases "mt_pos c' kk = 0")
      case True
      have win_kk:
          "ae_window_invariant_le0
                (mt_tape cM_k kk) (mt_pos cM_k kk)
                (dest5 kk, ofs5 kk) (buf5 kk) (le_tm M)"
        using cM_k_window_general[rule_format, OF kklt] True
        unfolding ae_window_invariant_general_def by blast
      thus ?thesis unfolding ae_window_invariant_le0_def by simp
    next
      case ne0: False
      show ?thesis
      proof (cases "mt_pos c' kk = 1")
        case True
        have win_kk:
            "ae_window_invariant_le1
                  (mt_tape cM_k kk) (mt_pos cM_k kk)
                  (dest5 kk, ofs5 kk) (buf5 kk) (le_tm M)"
          using cM_k_window_general[rule_format, OF kklt] True
          unfolding ae_window_invariant_general_def by blast
        thus ?thesis unfolding ae_window_invariant_le1_def by simp
      next
        case ne1: False
        have hge2: "mt_pos c' kk \<ge> 2" using ne0 ne1 by linarith
        have decode:
            "mt_pos cM kk = (mt_pos c' kk - 1) * ?c + c_idx (ofs kk) + 1"
          using pos_corr kklt hge2 by (simp add: ae_decode_pos_def)
        have step_mult: "(mt_pos c' kk - 1) * ?c \<ge> ?c"
        proof -
          have "(mt_pos c' kk - 1) \<ge> 1" using hge2 by linarith
          hence "(mt_pos c' kk - 1) * ?c \<ge> 1 * ?c"
            by (rule mult_le_mono1)
          thus ?thesis by simp
        qed
        have pos_ge_c1: "mt_pos cM kk \<ge> ?c + 1"
          using decode step_mult by linarith
        have k_lt: "k < mt_pos cM kk" using k_le pos_ge_c1 by linarith
        have far_disj:
            "(0 :: nat) > mt_pos cM kk + k \<or> (0 :: nat) + k < mt_pos cM kk"
          using k_lt by simp
        have entry_zero: "mt_tape cM kk 0 = le_tm M"
          using tape_corr[rule_format, OF kklt] unfolding ae_tape_correspondence_def by simp
        have "mt_tape cM_k kk 0 = mt_tape cM kk 0"
          using mttm_relpow_tape_off_window[OF trace far_disj] .
        thus ?thesis using entry_zero by simp
      qed
    qed
  qed

  \<comment> \<open>Sub-step 6b2: M-side off-window preservation per tape regime.
      Each regime gives a different M-side window characterisation;
      \<open>mttm_relpow_tape_off_window\<close> applied with the entry
      M-head position (\<open>pos_corr\<close> + \<open>ae_decode_pos\<close>) and
      displacement bound \<open>\<le> k \<le> c\<close> closes each branch.\<close>
  have m_tape_off_window_le0:
      "\<And>kk p. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 0
              \<Longrightarrow> p > ?c
              \<Longrightarrow> mt_tape cM_k kk p = mt_tape cM kk p"
  proof -
    fix kk and p :: nat
    assume kklt: "kk < k_tm M"
    assume pos_eq: "mt_pos c' kk = 0"
    assume p_gt: "p > ?c"
    have m_pos_zero: "mt_pos cM kk = 0"
      using pos_corr kklt pos_eq by (simp add: ae_decode_pos_def)
    have far: "p > mt_pos cM kk + k" using p_gt m_pos_zero k_le by linarith
    have far_disj: "p > mt_pos cM kk + k \<or> p + k < mt_pos cM kk"
      using far by simp
    show "mt_tape cM_k kk p = mt_tape cM kk p"
      using mttm_relpow_tape_off_window[OF trace far_disj] .
  qed
  have m_tape_off_window_le1:
      "\<And>kk p. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1
              \<Longrightarrow> p > 2 * ?c
              \<Longrightarrow> mt_tape cM_k kk p = mt_tape cM kk p"
  proof -
    fix kk and p :: nat
    assume kklt: "kk < k_tm M"
    assume pos_eq: "mt_pos c' kk = 1"
    assume p_gt: "p > 2 * ?c"
    have m_pos_le_c: "mt_pos cM kk \<le> ?c"
    proof -
      have decode: "mt_pos cM kk = Suc (c_idx (ofs kk))"
        using pos_corr kklt pos_eq by (simp add: ae_decode_pos_def)
      have idx_lt: "c_idx (ofs kk) < ?c" by (rule c_idx_lt_card)
      show ?thesis using decode idx_lt by linarith
    qed
    have far: "p > mt_pos cM kk + k"
      using p_gt m_pos_le_c k_le by linarith
    have far_disj: "p > mt_pos cM kk + k \<or> p + k < mt_pos cM kk"
      using far by simp
    show "mt_tape cM_k kk p = mt_tape cM kk p"
      using mttm_relpow_tape_off_window[OF trace far_disj] .
  qed
  have m_tape_off_window_steady:
      "\<And>kk p. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
              \<Longrightarrow> p < (mt_pos c' kk - 2) * ?c + 1
                  \<or> p \<ge> (mt_pos c' kk - 2) * ?c + 1 + 3 * ?c
              \<Longrightarrow> mt_tape cM_k kk p = mt_tape cM kk p"
  proof -
    fix kk and p :: nat
    assume kklt: "kk < k_tm M"
    assume hge2: "mt_pos c' kk \<ge> 2"
    assume p_off: "p < (mt_pos c' kk - 2) * ?c + 1
                    \<or> p \<ge> (mt_pos c' kk - 2) * ?c + 1 + 3 * ?c"
    have decode:
        "mt_pos cM kk = (mt_pos c' kk - 1) * ?c + c_idx (ofs kk) + 1"
      using pos_corr kklt hge2 by (simp add: ae_decode_pos_def)
    have ws_alt:
        "(mt_pos c' kk - 1) * ?c = (mt_pos c' kk - 2) * ?c + ?c"
    proof -
      have suc_eq: "Suc (mt_pos c' kk - 2) = mt_pos c' kk - 1"
        using hge2 by simp
      have "Suc (mt_pos c' kk - 2) * ?c = (mt_pos c' kk - 2) * ?c + ?c"
        by simp
      with suc_eq show ?thesis by simp
    qed
    have m_pos_eq:
        "mt_pos cM kk = (mt_pos c' kk - 2) * ?c + 1 + ?c + c_idx (ofs kk)"
      using decode ws_alt by simp
    have idx_lt: "c_idx (ofs kk) < ?c" by (rule c_idx_lt_card)
    have far_disj: "p > mt_pos cM kk + k \<or> p + k < mt_pos cM kk"
      using p_off k_le m_pos_eq idx_lt by linarith
    show "mt_tape cM_k kk p = mt_tape cM kk p"
      using mttm_relpow_tape_off_window[OF trace far_disj] .
  qed

  \<comment> \<open>Sub-step 6b3: head trajectory \<open>c5_pos\<close> for pos=0 tapes.
      For pos=0, \<open>c4_pos kk = 0\<close> by \<open>c4_pos\<close>, so SS5 reads
      \<open>mt_tape c4 kk 0 = mt_tape c' kk 0 = LE_block\<close> by
      \<open>le_anchor\<close>.  \<open>ae_ss5_action\<close>'s first branch
      (\<open>a = LE_block\<close>) fires: write \<open>a\<close> (no-op), direction N.
      Head stays at 0.\<close>
  have c5_pos_for_pos0:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 0 \<Longrightarrow> mt_pos c5 kk = 0"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume pos_kk: "mt_pos c' kk = 0"
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
    have nn_kk: "nn kk = mt_pos c4 kk" using c4_eq5 by simp
    have c4_kk: "mt_pos c4 kk = 0" using c4_pos kklt pos_kk by simp
    have nn_kk_0: "nn kk = 0" using nn_kk c4_kk by simp
    have read_LE: "tts kk (nn kk) = LE_block (le_tm M)"
    proof -
      have "tts kk (nn kk) = mt_tape c4 kk (mt_pos c4 kk)"
        using c4_eq5 nn_kk by simp
      also have "\<dots> = mt_tape c' kk 0"
        using c4_kk tape_c4_eq_c' by simp
      also have "\<dots> = LE_block (le_tm M)" using le_anchor[rule_format, OF kklt] by simp
      finally show ?thesis .
    qed
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have dr5_kk: "dr5 kk = dir.N"
      using dr5_eq buf_eq buf5_kk read_LE kklt by simp
    have "mt_pos c5 kk = go_dir (dr5 kk) (nn kk)"
      using c5_eq by simp
    also have "\<dots> = nn kk" using dr5_kk by simp
    also have "\<dots> = 0" using nn_kk_0 .
    finally show "mt_pos c5 kk = 0" .
  qed

  \<comment> \<open>Sub-step 6b3: head trajectory \<open>c5_pos\<close> for pos\<open>\<ge>\<close>2 tapes.
      Two sub-cases on \<open>dest5 kk\<close>.  For \<open>dest \<noteq> AE_Left\<close>:
      SS5's else branch fires with direction L, head lands at
      \<open>c4_pos - 1 = mt_pos c' kk - 1\<close>.  For \<open>dest = AE_Left\<close>:
      SS5's else branch fires with direction R, head lands at
      \<open>c4_pos + 1 = mt_pos c' kk + 1\<close>.  Mirrors the pos=1
      derivations \<open>c5_pos_for_pos1\<close> and \<open>_dest_left\<close>, but
      with \<open>mt_pos c' kk \<ge> 2\<close> so the result is
      \<open>mt_pos c' kk \<mp> 1\<close> rather than landing at the
      \<open>LE_block\<close> sentinel.\<close>
  have c5_pos_for_pos_ge2:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2 \<Longrightarrow> dest5 kk \<noteq> AE_Left
            \<Longrightarrow> mt_pos c5 kk = mt_pos c' kk - 1"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume hge2: "mt_pos c' kk \<ge> 2"
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
    have c4_kk: "mt_pos c4 kk = mt_pos c' kk"
      using c4_pos kklt by simp
    have pos_ge1: "(1 :: nat) \<le> mt_pos c' kk" using hge2 by linarith
    have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
    proof -
      have "tts kk (nn kk) = mt_tape c4 kk (mt_pos c4 kk)"
        using c4_eq5 nn_kk by simp
      also have "\<dots> = mt_tape c' kk (mt_pos c' kk)"
        using c4_kk tape_c4_eq_c' by simp
      finally have read_eq: "tts kk (nn kk) = mt_tape c' kk (mt_pos c' kk)" .
      have "mt_tape c' kk (mt_pos c' kk) \<noteq> LE_block (le_tm M)"
        using home_classification[rule_format, OF kklt] pos_ge1 by blast
      thus ?thesis using read_eq by simp
    qed
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have h_ne_LE: "hh \<noteq> LE_block (le_tm M)"
    proof -
      have "fst (snd (buf5 kk)) \<noteq> LE_block (le_tm M)"
        using buf5_not_le_per_tape[rule_format, OF kklt] hge2 by blast
      thus ?thesis using buf5_kk by simp
    qed
    have dr5_kk:
        "dr5 kk = (if dest5 kk = AE_Left then dir.R else dir.L)"
      using dr5_eq buf_eq dest_eq buf5_kk read_ne_LE h_ne_LE kklt by simp
    have dr5_kk_L: "dr5 kk = dir.L" using dr5_kk dest_ne by simp
    have "mt_pos c5 kk = go_dir (dr5 kk) (nn kk)"
      using c5_eq by simp
    also have "\<dots> = (nn kk) - 1" using dr5_kk_L by simp
    also have "\<dots> = mt_pos c' kk - 1" using nn_kk c4_kk by simp
    finally show "mt_pos c5 kk = mt_pos c' kk - 1" .
  qed

  have c5_pos_for_pos_ge2_dest_left:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2 \<Longrightarrow> dest5 kk = AE_Left
            \<Longrightarrow> mt_pos c5 kk = mt_pos c' kk + 1"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume hge2: "mt_pos c' kk \<ge> 2"
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
    have dest_eq': "dest = dest5" using qq_eq qq_state by simp
    have nn_kk: "nn kk = mt_pos c4 kk" using c4_eq5 by simp
    have c4_kk: "mt_pos c4 kk = mt_pos c' kk" using c4_pos kklt by simp
    have pos_ge1: "(1 :: nat) \<le> mt_pos c' kk" using hge2 by linarith
    have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
    proof -
      have "tts kk (nn kk) = mt_tape c4 kk (mt_pos c4 kk)"
        using c4_eq5 nn_kk by simp
      also have "\<dots> = mt_tape c' kk (mt_pos c' kk)"
        using c4_kk tape_c4_eq_c' by simp
      finally have read_eq: "tts kk (nn kk) = mt_tape c' kk (mt_pos c' kk)" .
      have "mt_tape c' kk (mt_pos c' kk) \<noteq> LE_block (le_tm M)"
        using home_classification[rule_format, OF kklt] pos_ge1 by blast
      thus ?thesis using read_eq by simp
    qed
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have h_ne_LE: "hh \<noteq> LE_block (le_tm M)"
    proof -
      have "fst (snd (buf5 kk)) \<noteq> LE_block (le_tm M)"
        using buf5_not_le_per_tape[rule_format, OF kklt] hge2 by blast
      thus ?thesis using buf5_kk by simp
    qed
    have dr5_kk:
        "dr5 kk = (if dest5 kk = AE_Left then dir.R else dir.L)"
      using dr5_eq buf_eq dest_eq' buf5_kk read_ne_LE h_ne_LE kklt by simp
    have dr5_kk_R: "dr5 kk = dir.R" using dr5_kk dest_eq by simp
    have "mt_pos c5 kk = go_dir (dr5 kk) (nn kk)"
      using c5_eq by simp
    also have "\<dots> = Suc (nn kk)" using dr5_kk_R by simp
    also have "\<dots> = mt_pos c' kk + 1" using nn_kk c4_kk by simp
    finally show "mt_pos c5 kk = mt_pos c' kk + 1" .
  qed

  \<comment> \<open>Sub-step 6b3 helper: \<open>left_not_le_c'_steady\<close>.  Mirror of
      \<open>right_not_le_c'\<close> for the left side at pos\<open>\<ge>\<close>2: block
      \<open>mt_pos c' k - 1\<close> mapped via the tape correspondence at
      sub-index 0 (which gives cell address \<open>(mt_pos c' k - 2) \<cdot> c + 1\<close>),
      then no-LE via \<open>no_le_per_tape\<close>'s steady branch at \<open>i = 0\<close>.
      Powers the SS5\<open>\<rightarrow>\<close>SS6 head-trajectory for pos\<open>\<ge>\<close>2
      tapes with \<open>dest \<noteq> AE_Left\<close>: c5 reads the cell at
      \<open>c5_pos = pos - 1\<close>, which is c'-side block pos-1.\<close>
  have left_not_le_c'_steady:
      "\<forall>k. mt_pos c' k \<ge> 2
            \<longrightarrow> mt_tape c' k (mt_pos c' k - 1) \<noteq> LE_block (le_tm M)"
  proof (intro allI impI)
    fix k :: nat
    assume hge2: "mt_pos c' k \<ge> 2"
    show "mt_tape c' k (mt_pos c' k - 1) \<noteq> LE_block (le_tm M)"
    proof (cases "k < k_tm M")
      case True
    let ?x = "(enum_class.enum :: 'c list) ! 0"
    let ?c = "card (UNIV :: 'c set)"
    have zero_lt_len: "0 < length (enum_class.enum :: 'c list)"
      using c_ge_1 c_eq_len by linarith
    have x_idx0: "c_idx ?x = 0"
      using c_idx_enum_nth[OF zero_lt_len] .
    have tc_k: "ae_tape_correspondence (le_tm M) (mt_tape cM k) (mt_tape c' k)"
      using tape_corr[rule_format, OF True] by simp
    have s_ge1: "mt_pos c' k - 1 \<ge> 1" using hge2 by linarith
    have addr_via_tc:
        "mt_tape cM k ((mt_pos c' k - 2) * ?c + 1)
          = mt_tape c' k (mt_pos c' k - 1) ?x"
    proof -
      from tc_k have unf:
          "\<forall>s\<ge>1. \<forall>i. mt_tape cM k ((s - 1) * ?c + c_idx i + 1)
                      = mt_tape c' k s i"
        unfolding ae_tape_correspondence_def by simp
      from unf s_ge1 have eq:
          "mt_tape cM k ((mt_pos c' k - 1 - 1) * ?c + c_idx ?x + 1)
            = mt_tape c' k (mt_pos c' k - 1) ?x"
        by blast
      have idx_arith:
          "mt_pos c' k - 1 - 1 = mt_pos c' k - 2"
        using hge2 by simp
      thus ?thesis using eq x_idx0 idx_arith by simp
    qed
    have idx_lt: "(0 :: nat) < 3 * ?c" using c_ge_1 by simp
    have nle: "mt_tape cM k ((mt_pos c' k - 2) * ?c + 1 + 0) \<noteq> le_tm M"
      using no_le_per_tape hge2 idx_lt by blast
    hence nle': "mt_tape cM k ((mt_pos c' k - 2) * ?c + 1) \<noteq> le_tm M"
      by simp
    have "mt_tape c' k (mt_pos c' k - 1) ?x \<noteq> le_tm M"
      using nle' addr_via_tc by simp
    thus "mt_tape c' k (mt_pos c' k - 1) \<noteq> LE_block (le_tm M)"
      unfolding LE_block_def by auto
    next
      case False
      hence kge: "k_tm M \<le> k" by simp
      have "mt_tape c' k (mt_pos c' k - 1) = bl_block (bl_tm M)"
        using gamma_c4 kge
        unfolding ae_tape_in_gamma_block_def tape_c4_eq_c'[symmetric]
        by simp
      thus ?thesis using bl_neq_le by simp
    qed
  qed

  \<comment> \<open>Sub-step 6b3 helpers: positive buffer-slot characterisations
      projected from \<open>c4_window_general\<close>'s regime-specific clauses.
      For pos=0 tapes, \<open>ae_window_invariant_le0\<close> contributes
      \<open>fst (snd blocks) = LE_block\<close> (the head buffer slot is LE).
      For pos=1 tapes, \<open>ae_window_invariant_le1\<close> contributes
      \<open>fst blocks = LE_block\<close> (the left buffer slot is LE).
      These complement \<open>buf5_not_le_per_tape\<close> (negative facts)
      with positive identifications, powering the SS7 LE-guard
      branches that fire for pos=0 (\<open>h = LE\<close>) and the SS8
      \<open>AE_Left\<close> dispatch for pos=1 (\<open>l = LE\<close>).\<close>
  have buf5_h_le_for_pos0:
      "\<forall>k<k_tm M. mt_pos c' k = 0 \<longrightarrow> fst (snd (buf5 k)) = LE_block (le_tm M)"
  proof (intro allI impI)
    fix k :: nat
    assume klt: "k < k_tm M"
    assume pos_k: "mt_pos c' k = 0"
    have wi: "ae_window_invariant_general
                (mt_tape cM_k k) (mt_pos cM_k k)
                (dest5 k, ofs5 k) (buf5 k)
                (mt_pos c' k) (le_tm M)"
      using cM_k_window_general[rule_format, OF klt] by simp
    hence "ae_window_invariant_le0
              (mt_tape cM_k k) (mt_pos cM_k k)
              (dest5 k, ofs5 k) (buf5 k) (le_tm M)"
      using pos_k unfolding ae_window_invariant_general_def by simp
    thus "fst (snd (buf5 k)) = LE_block (le_tm M)"
      unfolding ae_window_invariant_le0_def by simp
  qed

  have buf5_l_le_for_pos1:
      "\<forall>k<k_tm M. mt_pos c' k = 1 \<longrightarrow> fst (buf5 k) = LE_block (le_tm M)"
  proof (intro allI impI)
    fix k :: nat
    assume klt: "k < k_tm M"
    assume pos_k: "mt_pos c' k = 1"
    have wi: "ae_window_invariant_general
                (mt_tape cM_k k) (mt_pos cM_k k)
                (dest5 k, ofs5 k) (buf5 k)
                (mt_pos c' k) (le_tm M)"
      using cM_k_window_general[rule_format, OF klt] by simp
    hence "ae_window_invariant_le1
              (mt_tape cM_k k) (mt_pos cM_k k)
              (dest5 k, ofs5 k) (buf5 k) (le_tm M)"
      using pos_k unfolding ae_window_invariant_general_def by simp
    thus "fst (buf5 k) = LE_block (le_tm M)"
      unfolding ae_window_invariant_le1_def by simp
  qed

  \<comment> \<open>Sub-step 6b3: head trajectory \<open>c6_pos\<close> for pos=0 tapes.
      \<open>c5_pos = 0\<close> (\<open>c5_pos_for_pos0\<close>); SS6 reads
      \<open>mt_tape c5 kk 0 = LE_block\<close> via \<open>tape_c5_zero_le\<close>.
      \<open>ae_ss6_action\<close>'s first branch fires (\<open>a = LE_block\<close>),
      writing a (no-op), direction R.  Head lands at
      \<open>c5_pos + 1 = 1\<close>.\<close>
  have c6_pos_for_pos0:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 0 \<Longrightarrow> mt_pos c6 kk = 1"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume pos_kk: "mt_pos c' kk = 0"
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
    have nn_kk: "nn kk = mt_pos c5 kk" using c5_eq6 by simp
    have c5_kk: "mt_pos c5 kk = 0" using c5_pos_for_pos0[OF kklt pos_kk] .
    have nn_kk_0: "nn kk = 0" using nn_kk c5_kk by simp
    have read_LE: "tts kk (nn kk) = LE_block (le_tm M)"
    proof -
      have "tts kk (nn kk) = mt_tape c5 kk (mt_pos c5 kk)"
        using c5_eq6 nn_kk by simp
      also have "\<dots> = mt_tape c5 kk 0" using c5_kk by simp
      also have "\<dots> = LE_block (le_tm M)" using tape_c5_zero_le[rule_format, OF kklt] by simp
      finally show ?thesis .
    qed
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have dr6_kk: "dr6 kk = dir.R"
      using dr6_eq buf_eq buf5_kk read_LE kklt by simp
    have "mt_pos c6 kk = go_dir (dr6 kk) (nn kk)"
      using c6_eq by simp
    also have "\<dots> = Suc (nn kk)" using dr6_kk by simp
    also have "\<dots> = 1" using nn_kk_0 by simp
    finally show "mt_pos c6 kk = 1" .
  qed

  \<comment> \<open>Sub-step 6b3: head trajectory \<open>c6_pos\<close> for pos\<open>\<ge>\<close>2 tapes.
      Both dest branches converge to \<open>c6_pos = pos\<close> (SS6 writes the
      home block and returns the head to home).  Case-split on
      \<open>dest5 kk = AE_Left\<close>.  For \<open>dest = AE_Left\<close>: \<open>c5_pos = pos + 1\<close>,
      SS6 reads at \<open>pos + 1\<close> non-LE (\<open>right_not_le_c'\<close>), \<open>h\<close> non-LE
      (\<open>buf5_not_le_per_tape\<close> pos\<open>\<ge>\<close>2), action's else branch
      direction L, head lands at \<open>c5_pos - 1 = pos\<close>.  For
      \<open>dest \<noteq> AE_Left\<close>: \<open>c5_pos = pos - 1\<close>, SS6 reads at \<open>pos - 1\<close>
      non-LE (\<open>left_not_le_c'_steady\<close>), \<open>h\<close> non-LE, action's else
      branch direction R, head lands at \<open>c5_pos + 1 = pos\<close>.
      Extracted to \<open>ae_fwd_c6_pos_for_pos_ge2\<close>.\<close>
  have c6_pos_for_pos_ge2:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2 \<Longrightarrow> mt_pos c6 kk = mt_pos c' kk"
    by (rule ae_fwd_c6_pos_for_pos_ge2[OF step5 c5_state tape_c4_eq_c'
          buf5_not_le_per_tape right_not_le_c' c4_pos step6_sub
          c5_pos_for_pos_ge2 c5_pos_for_pos_ge2_dest_left left_not_le_c'_steady])
  \<comment> \<open>Sub-step 6b4: head trajectory \<open>c7_pos\<close> for pos=0 tapes.
      \<open>c6_pos = 1\<close> (\<open>c6_pos_for_pos0\<close>); SS7 reads
      \<open>mt_tape c6 kk 1\<close> which off-traces through SS6 (\<open>c5_pos = 0\<close>),
      SS5 (\<open>c4_pos = 0\<close>) to \<open>mt_tape c' kk 1\<close>, non-LE via
      \<open>right_not_le_c'\<close>.  Buffer's head slot \<open>h = LE_block\<close>
      (\<open>buf5_h_le_for_pos0\<close>), so \<open>ae_ss7_action\<close>'s second branch
      fires: writes \<open>r\<close>, direction \<open>N\<close> if \<open>dest = AE_Right\<close>
      else \<open>L\<close>.  Head lands at \<open>1\<close> (\<open>dest = AE_Right\<close>) or \<open>0\<close>
      (otherwise).\<close>
  have c7_pos_for_pos0:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 0
            \<Longrightarrow> mt_pos c7 kk = (if dest5 kk = AE_Right then 1 else 0)"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume pos_kk: "mt_pos c' kk = 0"
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
    have qq_state: "qq = (q6, ofs6, buf6, dest6, SS7)"
      using c6_state c6_eq7 by simp
    have buf_eq: "buf = buf6" using qq_eq qq_state by simp
    have dest_eq: "dest = dest6" using qq_eq qq_state by simp
    have nn_kk: "nn kk = mt_pos c6 kk" using c6_eq7 by simp
    have c6_kk: "mt_pos c6 kk = 1" using c6_pos_for_pos0[OF kklt pos_kk] .
    have nn_kk_1: "nn kk = 1" using nn_kk c6_kk by simp
    have one_ne_c5_pos: "(1 :: nat) \<noteq> mt_pos c5 kk"
      using c5_pos_for_pos0[OF kklt pos_kk] by simp
    have one_ne_c4_pos: "(1 :: nat) \<noteq> mt_pos c4 kk"
      using c4_pos kklt pos_kk by simp
    have c6_at_1: "mt_tape c6 kk 1 = mt_tape c' kk 1"
    proof -
      have "mt_tape c6 kk 1 = mt_tape c5 kk 1"
        using mttm_step_tape_off_head[OF step6 one_ne_c5_pos] .
      also have "\<dots> = mt_tape c4 kk 1"
        using mttm_step_tape_off_head[OF step5 one_ne_c4_pos] .
      also have "\<dots> = mt_tape c' kk 1"
        using tape_c4_eq_c' by simp
      finally show ?thesis .
    qed
    have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
    proof -
      have "tts kk (nn kk) = mt_tape c6 kk (mt_pos c6 kk)"
        using c6_eq7 nn_kk by simp
      also have "\<dots> = mt_tape c6 kk 1" using c6_kk by simp
      also have "\<dots> = mt_tape c' kk 1" using c6_at_1 .
      finally have read_eq: "tts kk (nn kk) = mt_tape c' kk 1" .
      have "mt_tape c' kk (mt_pos c' kk + 1) \<noteq> LE_block (le_tm M)"
        using right_not_le_c' by blast
      hence "mt_tape c' kk 1 \<noteq> LE_block (le_tm M)" using pos_kk by simp
      thus ?thesis using read_eq by simp
    qed
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have hh_le: "hh = LE_block (le_tm M)"
    proof -
      have "fst (snd (buf5 kk)) = LE_block (le_tm M)"
        using buf5_h_le_for_pos0[rule_format, OF kklt] pos_kk by blast
      thus ?thesis using buf5_kk by simp
    qed
    have buf6_kk: "buf6 kk = (ll, hh, rr)"
      using buf5_kk buf6_eq_buf5 by simp
    have dr7_kk:
        "dr7 kk = (if dest6 kk = AE_Right then dir.N else dir.L)"
      using dr7_eq buf_eq dest_eq buf6_kk hh_le read_ne_LE kklt by simp
    show "mt_pos c7 kk = (if dest5 kk = AE_Right then 1 else 0)"
    proof (cases "dest5 kk = AE_Right")
      case True
      have dest6_eq: "dest6 kk = AE_Right"
        using True dest6_eq_dest5 by simp
      have dr7_kk_N: "dr7 kk = dir.N" using dr7_kk dest6_eq by simp
      have "mt_pos c7 kk = go_dir (dr7 kk) (nn kk)"
        using c7_eq by simp
      also have "\<dots> = nn kk" using dr7_kk_N by simp
      also have "\<dots> = 1" using nn_kk_1 .
      finally show ?thesis using True by simp
    next
      case False
      have dest6_ne: "dest6 kk \<noteq> AE_Right"
        using False dest6_eq_dest5 by simp
      have dr7_kk_L: "dr7 kk = dir.L" using dr7_kk dest6_ne by simp
      have "mt_pos c7 kk = go_dir (dr7 kk) (nn kk)"
        using c7_eq by simp
      also have "\<dots> = (nn kk) - 1" using dr7_kk_L by simp
      also have "\<dots> = 0" using nn_kk_1 by simp
      finally show ?thesis using False by simp
    qed
  qed

  \<comment> \<open>Sub-step 6b4 helper: SS5's write at \<open>c4_pos = pos\<close> for
      pos\<open>\<ge>\<close>2 tapes records the home buffer slot \<open>fst (snd
      (buf5 k))\<close>.  Action \<open>ae_ss5_action\<close>'s else branch fires
      (read non-LE via \<open>home_classification\<close>, head buf slot non-LE
      via \<open>buf5_not_le_per_tape\<close> pos\<open>\<ge>\<close>2), writing \<open>h\<close>.
      Powers the SS7 read characterisation at \<open>c6_pos = pos\<close>
      (off-write from SS6 which writes at \<open>c5_pos = pos \<mp> 1\<close>).\<close>
  have tape_c5_at_pos_for_pos_ge2:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
            \<Longrightarrow> mt_tape c5 kk (mt_pos c' kk) = fst (snd (buf5 kk))"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume hge2: "mt_pos c' kk \<ge> 2"
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
    have nn_kk: "nn kk = mt_pos c4 kk" using c4_eq5 by simp
    have c4_kk: "mt_pos c4 kk = mt_pos c' kk" using c4_pos kklt by simp
    have pos_ge1: "(1 :: nat) \<le> mt_pos c' kk" using hge2 by linarith
    have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
    proof -
      have "tts kk (nn kk) = mt_tape c4 kk (mt_pos c4 kk)"
        using c4_eq5 nn_kk by simp
      also have "\<dots> = mt_tape c' kk (mt_pos c' kk)"
        using c4_kk tape_c4_eq_c' by simp
      finally have read_eq:
          "tts kk (nn kk) = mt_tape c' kk (mt_pos c' kk)" .
      have "mt_tape c' kk (mt_pos c' kk) \<noteq> LE_block (le_tm M)"
        using home_classification[rule_format, OF kklt] pos_ge1 by blast
      thus ?thesis using read_eq by simp
    qed
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have h_ne_LE: "hh \<noteq> LE_block (le_tm M)"
    proof -
      have "fst (snd (buf5 kk)) \<noteq> LE_block (le_tm M)"
        using buf5_not_le_per_tape[rule_format, OF kklt] hge2 by blast
      thus ?thesis using buf5_kk by simp
    qed
    have aa5_kk: "aa5 kk = hh"
      using aa5_eq buf_eq buf5_kk read_ne_LE h_ne_LE kklt by simp
    have "mt_tape c5 kk (mt_pos c' kk) = aa5 kk"
      using c5_eq nn_kk c4_kk by simp
    also have "\<dots> = hh" using aa5_kk .
    also have "\<dots> = fst (snd (buf5 kk))" using buf5_kk by simp
    finally show "mt_tape c5 kk (mt_pos c' kk) = fst (snd (buf5 kk))" .
  qed

  \<comment> \<open>Sub-step 6b4: head trajectory \<open>c7_pos\<close> for pos\<open>\<ge>\<close>2
      tapes.  \<open>c6_pos = pos\<close> (\<open>c6_pos_for_pos_ge2\<close>); SS7 reads
      \<open>mt_tape c6 kk pos\<close> = \<open>mt_tape c5 kk pos\<close> (off-write from
      SS6 at \<open>c5_pos = pos \<mp> 1\<close>) = \<open>fst (snd (buf5 kk))\<close>
      (\<open>tape_c5_at_pos_for_pos_ge2\<close>), non-LE via
      \<open>buf5_not_le_per_tape\<close>.  \<open>h = fst (snd (buf6 kk))\<close>
      non-LE.  \<open>ae_ss7_action\<close>'s else branch fires: dir L if
      \<open>dest = AE_Left\<close> else R.  Head lands at \<open>pos - 1\<close>
      (\<open>dest = AE_Left\<close>) or \<open>pos + 1\<close> (otherwise).\<close>
  have c7_pos_for_pos_ge2:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
            \<Longrightarrow> mt_pos c7 kk = (if dest5 kk = AE_Left
                                  then mt_pos c' kk - 1
                                  else mt_pos c' kk + 1)"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume hge2: "mt_pos c' kk \<ge> 2"
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
    have qq_state: "qq = (q6, ofs6, buf6, dest6, SS7)"
      using c6_state c6_eq7 by simp
    have buf_eq: "buf = buf6" using qq_eq qq_state by simp
    have dest_eq: "dest = dest6" using qq_eq qq_state by simp
    have nn_kk: "nn kk = mt_pos c6 kk" using c6_eq7 by simp
    have c6_kk: "mt_pos c6 kk = mt_pos c' kk"
      using c6_pos_for_pos_ge2[OF kklt hge2] .
    have nn_kk_val: "nn kk = mt_pos c' kk" using nn_kk c6_kk by simp
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have buf6_kk: "buf6 kk = (ll, hh, rr)"
      using buf5_kk buf6_eq_buf5 by simp
    have h_ne_LE: "hh \<noteq> LE_block (le_tm M)"
    proof -
      have "fst (snd (buf5 kk)) \<noteq> LE_block (le_tm M)"
        using buf5_not_le_per_tape[rule_format, OF kklt] hge2 by blast
      thus ?thesis using buf5_kk by simp
    qed
    have pos_ne_c5_pos: "mt_pos c' kk \<noteq> mt_pos c5 kk"
    proof (cases "dest5 kk = AE_Left")
      case True
      have "mt_pos c5 kk = mt_pos c' kk + 1"
        using c5_pos_for_pos_ge2_dest_left[OF kklt hge2 True] .
      thus ?thesis by linarith
    next
      case False
      have "mt_pos c5 kk = mt_pos c' kk - 1"
        using c5_pos_for_pos_ge2[OF kklt hge2 False] .
      thus ?thesis using hge2 by linarith
    qed
    have c6_at_pos: "mt_tape c6 kk (mt_pos c' kk) = mt_tape c5 kk (mt_pos c' kk)"
      using mttm_step_tape_off_head[OF step6 pos_ne_c5_pos] .
    have c5_at_pos:
        "mt_tape c5 kk (mt_pos c' kk) = fst (snd (buf5 kk))"
      using tape_c5_at_pos_for_pos_ge2[OF kklt hge2] .
    have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
    proof -
      have "tts kk (nn kk) = mt_tape c6 kk (mt_pos c6 kk)"
        using c6_eq7 nn_kk by simp
      also have "\<dots> = mt_tape c6 kk (mt_pos c' kk)" using c6_kk by simp
      also have "\<dots> = mt_tape c5 kk (mt_pos c' kk)" using c6_at_pos .
      also have "\<dots> = fst (snd (buf5 kk))" using c5_at_pos .
      also have "\<dots> = hh" using buf5_kk by simp
      finally have read_eq: "tts kk (nn kk) = hh" .
      show ?thesis using read_eq h_ne_LE by simp
    qed
    have dr7_kk:
        "dr7 kk = (if dest6 kk = AE_Left then dir.L else dir.R)"
      using dr7_eq buf_eq dest_eq buf6_kk h_ne_LE read_ne_LE kklt by simp
    show "mt_pos c7 kk = (if dest5 kk = AE_Left
                            then mt_pos c' kk - 1
                            else mt_pos c' kk + 1)"
    proof (cases "dest5 kk = AE_Left")
      case True
      have dest6_eq: "dest6 kk = AE_Left" using True dest6_eq_dest5 by simp
      have dr7_kk_L: "dr7 kk = dir.L" using dr7_kk dest6_eq by simp
      have "mt_pos c7 kk = go_dir (dr7 kk) (nn kk)"
        using c7_eq by simp
      also have "\<dots> = (nn kk) - 1" using dr7_kk_L by simp
      also have "\<dots> = mt_pos c' kk - 1" using nn_kk_val by simp
      finally show ?thesis using True by simp
    next
      case False
      have dest6_ne: "dest6 kk \<noteq> AE_Left" using False dest6_eq_dest5 by simp
      have dr7_kk_R: "dr7 kk = dir.R" using dr7_kk dest6_ne by simp
      have "mt_pos c7 kk = go_dir (dr7 kk) (nn kk)"
        using c7_eq by simp
      also have "\<dots> = Suc (nn kk)" using dr7_kk_R by simp
      also have "\<dots> = mt_pos c' kk + 1" using nn_kk_val by simp
      finally show ?thesis using False by simp
    qed
  qed

  \<comment> \<open>Sub-step 6b4: head trajectory \<open>c6_pos\<close> for pos=1 tapes,
      uniform across \<open>dest\<close>.  \<open>dest = AE_Left\<close> routes via
      \<open>c6_pos_for_pos1_dest_left\<close> (\<open>c5_pos = 2\<close>, dir L);
      \<open>dest \<noteq> AE_Left\<close> routes via \<open>c5_pos_for_pos1\<close>
      (\<open>c5_pos = 0\<close>): SS6 reads LE at 0 (\<open>tape_c5_zero_le\<close>),
      action's first branch (a = LE) fires with direction R,
      head lands at \<open>c5_pos + 1 = 1\<close>.\<close>
  have c6_pos_for_pos1:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1 \<Longrightarrow> mt_pos c6 kk = 1"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume pos_kk: "mt_pos c' kk = 1"
    show "mt_pos c6 kk = 1"
    proof (cases "dest5 kk = AE_Left")
      case True
      show ?thesis using c6_pos_for_pos1_dest_left[OF kklt pos_kk True] .
    next
      case False
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
      have nn_kk: "nn kk = mt_pos c5 kk" using c5_eq6 by simp
      have c5_kk: "mt_pos c5 kk = 0"
        using c5_pos_for_pos1[OF kklt pos_kk False] .
      have nn_kk_0: "nn kk = 0" using nn_kk c5_kk by simp
      have read_LE: "tts kk (nn kk) = LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c5 kk (mt_pos c5 kk)"
          using c5_eq6 nn_kk by simp
        also have "\<dots> = mt_tape c5 kk 0" using c5_kk by simp
        also have "\<dots> = LE_block (le_tm M)" using tape_c5_zero_le[rule_format, OF kklt] by simp
        finally show ?thesis .
      qed
      obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
        using prod.exhaust by metis
      have dr6_kk: "dr6 kk = dir.R"
        using dr6_eq buf_eq buf5_kk read_LE kklt by simp
      have "mt_pos c6 kk = go_dir (dr6 kk) (nn kk)"
        using c6_eq by simp
      also have "\<dots> = Suc (nn kk)" using dr6_kk by simp
      also have "\<dots> = 1" using nn_kk_0 by simp
      finally show ?thesis .
    qed
  qed

  \<comment> \<open>Sub-step 6b4: head trajectory \<open>c7_pos\<close> for pos=1 tapes.
      \<open>c6_pos = 1\<close> uniformly.  For \<open>dest = AE_Left\<close>: defers to
      the sub-step 5 lemma \<open>c7_pos_for_pos1_dest_left\<close>
      (\<open>c7_pos = 0\<close>).  For \<open>dest \<noteq> AE_Left\<close>: SS7 reads
      \<open>mt_tape c6 kk 1 = mt_tape c5 kk 1\<close> (off-write from SS6 at
      \<open>c5_pos = 0\<close>) \<open>= fst (snd (buf5 kk)) = hh\<close>
      (\<open>tape_c5_at_one_pos1\<close>), non-LE (\<open>buf5_not_le_per_tape\<close>
      pos=1).  \<open>h\<close> non-LE; \<open>ae_ss7_action\<close>'s else branch
      with \<open>dest \<noteq> AE_Left\<close> gives dir R, head lands at \<open>2\<close>.\<close>
  have c7_pos_for_pos1:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1
            \<Longrightarrow> mt_pos c7 kk = (if dest5 kk = AE_Left then 0 else 2)"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume pos_kk: "mt_pos c' kk = 1"
    show "mt_pos c7 kk = (if dest5 kk = AE_Left then 0 else 2)"
    proof (cases "dest5 kk = AE_Left")
      case True
      have "mt_pos c7 kk = 0"
        using c7_pos_for_pos1_dest_left[OF kklt pos_kk True] .
      thus ?thesis using True by simp
    next
      case False
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
      have qq_state: "qq = (q6, ofs6, buf6, dest6, SS7)"
        using c6_state c6_eq7 by simp
      have buf_eq: "buf = buf6" using qq_eq qq_state by simp
      have dest_eq: "dest = dest6" using qq_eq qq_state by simp
      have nn_kk: "nn kk = mt_pos c6 kk" using c6_eq7 by simp
      have c6_kk: "mt_pos c6 kk = 1" using c6_pos_for_pos1[OF kklt pos_kk] .
      have nn_kk_1: "nn kk = 1" using nn_kk c6_kk by simp
      have one_ne_c5_pos: "(1 :: nat) \<noteq> mt_pos c5 kk"
        using c5_pos_for_pos1[OF kklt pos_kk False] by simp
      have c6_at_1: "mt_tape c6 kk 1 = mt_tape c5 kk 1"
        using mttm_step_tape_off_head[OF step6 one_ne_c5_pos] .
      obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
        using prod.exhaust by metis
      have buf6_kk: "buf6 kk = (ll, hh, rr)"
        using buf5_kk buf6_eq_buf5 by simp
      have c5_at_1: "mt_tape c5 kk 1 = hh"
      proof -
        have "mt_tape c5 kk 1 = fst (snd (buf5 kk))"
          using tape_c5_at_one_pos1[OF kklt pos_kk] .
        thus ?thesis using buf5_kk by simp
      qed
      have h_ne_LE: "hh \<noteq> LE_block (le_tm M)"
      proof -
        have "fst (snd (buf5 kk)) \<noteq> LE_block (le_tm M)"
          using buf5_not_le_per_tape[rule_format, OF kklt] pos_kk by blast
        thus ?thesis using buf5_kk by simp
      qed
      have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c6 kk (mt_pos c6 kk)"
          using c6_eq7 nn_kk by simp
        also have "\<dots> = mt_tape c6 kk 1" using c6_kk by simp
        also have "\<dots> = mt_tape c5 kk 1" using c6_at_1 .
        also have "\<dots> = hh" using c5_at_1 .
        finally have "tts kk (nn kk) = hh" .
        thus ?thesis using h_ne_LE by simp
      qed
      have dr7_kk:
          "dr7 kk = (if dest6 kk = AE_Left then dir.L else dir.R)"
        using dr7_eq buf_eq dest_eq buf6_kk h_ne_LE read_ne_LE kklt by simp
      have dest6_ne: "dest6 kk \<noteq> AE_Left" using False dest6_eq_dest5 by simp
      have dr7_kk_R: "dr7 kk = dir.R" using dr7_kk dest6_ne by simp
      have "mt_pos c7 kk = go_dir (dr7 kk) (nn kk)"
        using c7_eq by simp
      also have "\<dots> = Suc (nn kk)" using dr7_kk_R by simp
      also have "\<dots> = 2" using nn_kk_1 by simp
      finally show ?thesis using False by simp
    qed
  qed

  \<comment> \<open>Sub-step 6b5 helper: \<open>c6\<close> tape at cell 0 for pos=0 tapes.
      SS6 writes at \<open>c5_pos = 0\<close>, reading \<open>c5@0 = LE_block\<close>
      (\<open>tape_c5_zero_le\<close>); action's first branch \<open>a = LE\<close> fires,
      writing \<open>a = LE_block\<close> back.  So \<open>c6@0 = LE_block\<close>.\<close>
  have tape_c6_zero_le_for_pos0:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 0 \<Longrightarrow> mt_tape c6 kk 0 = LE_block (le_tm M)"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume pos_kk: "mt_pos c' kk = 0"
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
      and aa6_eq:
          "aa6 = (\<lambda>k. if k < k_tm M then fst (ae_ss6_action (le_tm M)
                              (tts k (nn k)) (buf k) (dest k)) else bl_block (bl_tm M))"
      using tr_in by (auto simp: ae_delta_ss6_ss7_def)
    have qq_state: "qq = (q5, ofs5, buf5, dest5, SS6)"
      using c5_state c5_eq6 by simp
    have buf_eq: "buf = buf5" using qq_eq qq_state by simp
    have nn_kk: "nn kk = mt_pos c5 kk" using c5_eq6 by simp
    have c5_kk: "mt_pos c5 kk = 0" using c5_pos_for_pos0[OF kklt pos_kk] .
    have nn_kk_0: "nn kk = 0" using nn_kk c5_kk by simp
    have read_LE: "tts kk (nn kk) = LE_block (le_tm M)"
    proof -
      have "tts kk (nn kk) = mt_tape c5 kk (mt_pos c5 kk)"
        using c5_eq6 nn_kk by simp
      also have "\<dots> = mt_tape c5 kk 0" using c5_kk by simp
      also have "\<dots> = LE_block (le_tm M)" using tape_c5_zero_le[rule_format, OF kklt] by simp
      finally show ?thesis .
    qed
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have aa6_kk: "aa6 kk = LE_block (le_tm M)"
      using aa6_eq buf_eq buf5_kk read_LE kklt by simp
    have "mt_tape c6 kk 0 = aa6 kk"
      using c6_eq nn_kk_0 by simp
    also have "\<dots> = LE_block (le_tm M)" using aa6_kk .
    finally show "mt_tape c6 kk 0 = LE_block (le_tm M)" .
  qed

  \<comment> \<open>Sub-step 6b5 helper: \<open>c7\<close> tape at cell 1 for pos=0 tapes
      under \<open>dest = AE_Right\<close>.  SS7 writes at \<open>c6_pos = 1\<close>,
      reading \<open>c6@1\<close> non-LE and with home-slot \<open>h = LE\<close>;
      action's second branch fires (h = LE), and with \<open>dest =
      AE_Right\<close> writes \<open>r = snd (snd (buf5 kk))\<close>.\<close>
  have tape_c7_at_one_for_pos0_right:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 0 \<Longrightarrow> dest5 kk = AE_Right
            \<Longrightarrow> mt_tape c7 kk 1 = snd (snd (buf5 kk))"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume pos_kk: "mt_pos c' kk = 0"
    assume dest_eq: "dest5 kk = AE_Right"
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
      and aa7_eq:
          "aa7 = (\<lambda>k. if k < k_tm M then fst (ae_ss7_action (le_tm M)
                              (tts k (nn k)) (buf k) (dest k)) else bl_block (bl_tm M))"
      using tr_in by (auto simp: ae_delta_ss7_ss8_def)
    have qq_state: "qq = (q6, ofs6, buf6, dest6, SS7)"
      using c6_state c6_eq7 by simp
    have buf_eq: "buf = buf6" using qq_eq qq_state by simp
    have dest_eq2: "dest = dest6" using qq_eq qq_state by simp
    have nn_kk: "nn kk = mt_pos c6 kk" using c6_eq7 by simp
    have c6_kk: "mt_pos c6 kk = 1" using c6_pos_for_pos0[OF kklt pos_kk] .
    have nn_kk_1: "nn kk = 1" using nn_kk c6_kk by simp
    have one_ne_c5_pos: "(1 :: nat) \<noteq> mt_pos c5 kk"
      using c5_pos_for_pos0[OF kklt pos_kk] by simp
    have one_ne_c4_pos: "(1 :: nat) \<noteq> mt_pos c4 kk"
      using c4_pos kklt pos_kk by simp
    have c6_at_1: "mt_tape c6 kk 1 = mt_tape c' kk 1"
    proof -
      have "mt_tape c6 kk 1 = mt_tape c5 kk 1"
        using mttm_step_tape_off_head[OF step6 one_ne_c5_pos] .
      also have "\<dots> = mt_tape c4 kk 1"
        using mttm_step_tape_off_head[OF step5 one_ne_c4_pos] .
      also have "\<dots> = mt_tape c' kk 1" using tape_c4_eq_c' by simp
      finally show ?thesis .
    qed
    have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
    proof -
      have "tts kk (nn kk) = mt_tape c6 kk (mt_pos c6 kk)"
        using c6_eq7 nn_kk by simp
      also have "\<dots> = mt_tape c6 kk 1" using c6_kk by simp
      also have "\<dots> = mt_tape c' kk 1" using c6_at_1 .
      finally have read_eq: "tts kk (nn kk) = mt_tape c' kk 1" .
      have "mt_tape c' kk (mt_pos c' kk + 1) \<noteq> LE_block (le_tm M)"
        using right_not_le_c' by blast
      hence "mt_tape c' kk 1 \<noteq> LE_block (le_tm M)" using pos_kk by simp
      thus ?thesis using read_eq by simp
    qed
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have buf6_kk: "buf6 kk = (ll, hh, rr)"
      using buf5_kk buf6_eq_buf5 by simp
    have hh_le: "hh = LE_block (le_tm M)"
    proof -
      have "fst (snd (buf5 kk)) = LE_block (le_tm M)"
        using buf5_h_le_for_pos0[rule_format, OF kklt] pos_kk by blast
      thus ?thesis using buf5_kk by simp
    qed
    have dest6_eq: "dest6 kk = AE_Right" using dest_eq dest6_eq_dest5 by simp
    have aa7_kk: "aa7 kk = rr"
      using aa7_eq buf_eq dest_eq2 dest6_eq buf6_kk hh_le read_ne_LE kklt by simp
    have "mt_tape c7 kk 1 = aa7 kk" using c7_eq nn_kk_1 by simp
    also have "\<dots> = rr" using aa7_kk .
    also have "\<dots> = snd (snd (buf5 kk))" using buf5_kk by simp
    finally show "mt_tape c7 kk 1 = snd (snd (buf5 kk))" .
  qed

  \<comment> \<open>Sub-step 6b4: head trajectory \<open>c8_pos\<close> for pos=0 tapes.
      Internal case-split on \<open>dest5 kk = AE_Right\<close>.  For
      \<open>dest = AE_Right\<close>: \<open>c7_pos = 1\<close>, read \<open>r\<close> non-LE,
      \<open>h = LE\<close>, action's h-LE branch with \<open>dest = AE_Right\<close>
      gives \<open>(r, N)\<close>; \<open>c8_pos = 1\<close>.  For \<open>dest \<noteq>
      AE_Right\<close>: \<open>c7_pos = 0\<close>, read LE (\<open>c6@0 = LE\<close> via
      \<open>tape_c6_zero_le_for_pos0\<close>, off-write at SS7);
      action's first branch \<open>a = LE\<close> gives \<open>(a, N)\<close>;
      \<open>c8_pos = 0\<close>.\<close>
  have c8_pos_for_pos0:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 0
            \<Longrightarrow> mt_pos c8 kk = (if dest5 kk = AE_Right then 1 else 0)"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume pos_kk: "mt_pos c' kk = 0"
    obtain qq tts nn qq' aa8 dr8 where
        c7_eq8: "c7 = Config\<^sub>M qq tts nn"
      and c8_eq: "c8 = Config\<^sub>M qq'
                          (\<lambda>k. (tts k)(nn k := aa8 k))
                          (\<lambda>k. go_dir (dr8 k) (nn k))"
      and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa8, dr8)
                    \<in> ae_delta_ss8_ss1 M"
      using step8_sub by (auto elim: mttm_step.cases)
    obtain q ofs buf dest where
        qq_eq: "qq = (q, ofs, buf, dest, SS8)"
      and dr8_eq:
          "dr8 = (\<lambda>k. if k < k_tm M then snd (ae_ss8_action (le_tm M)
                              (tts k (nn k)) (buf k) (dest k)) else dir.N)"
      using tr_in by (auto simp: ae_delta_ss8_ss1_def)
    have qq_state: "qq = (q6, ofs6, buf6, dest6, SS8)"
      using c7_state c7_eq8 by simp
    have buf_eq: "buf = buf6" using qq_eq qq_state by simp
    have dest_eq: "dest = dest6" using qq_eq qq_state by simp
    have nn_kk: "nn kk = mt_pos c7 kk" using c7_eq8 by simp
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have buf6_kk: "buf6 kk = (ll, hh, rr)"
      using buf5_kk buf6_eq_buf5 by simp
    have hh_le: "hh = LE_block (le_tm M)"
    proof -
      have "fst (snd (buf5 kk)) = LE_block (le_tm M)"
        using buf5_h_le_for_pos0[rule_format, OF kklt] pos_kk by blast
      thus ?thesis using buf5_kk by simp
    qed
    show "mt_pos c8 kk = (if dest5 kk = AE_Right then 1 else 0)"
    proof (cases "dest5 kk = AE_Right")
      case True
      have dest6_eq: "dest6 kk = AE_Right" using True dest6_eq_dest5 by simp
      have c7_kk: "mt_pos c7 kk = 1" using c7_pos_for_pos0[OF kklt pos_kk] True by simp
      have nn_kk_1: "nn kk = 1" using nn_kk c7_kk by simp
      have rr_ne_LE: "rr \<noteq> LE_block (le_tm M)"
      proof -
        have "snd (snd (buf5 kk)) \<noteq> LE_block (le_tm M)"
          using buf5_not_le_per_tape[rule_format, OF kklt] pos_kk by blast
        thus ?thesis using buf5_kk by simp
      qed
      have c7_at_1: "mt_tape c7 kk 1 = rr"
      proof -
        have "mt_tape c7 kk 1 = snd (snd (buf5 kk))"
          using tape_c7_at_one_for_pos0_right[OF kklt pos_kk True] .
        thus ?thesis using buf5_kk by simp
      qed
      have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c7 kk (mt_pos c7 kk)"
          using c7_eq8 nn_kk by simp
        also have "\<dots> = mt_tape c7 kk 1" using c7_kk by simp
        also have "\<dots> = rr" using c7_at_1 .
        finally have "tts kk (nn kk) = rr" .
        thus ?thesis using rr_ne_LE by simp
      qed
      have dr8_kk: "dr8 kk = dir.N"
        using dr8_eq buf_eq dest_eq dest6_eq buf6_kk hh_le read_ne_LE kklt by simp
      have "mt_pos c8 kk = go_dir (dr8 kk) (nn kk)"
        using c8_eq by simp
      also have "\<dots> = nn kk" using dr8_kk by simp
      also have "\<dots> = 1" using nn_kk_1 .
      finally show ?thesis using True by simp
    next
      case False
      have c7_kk: "mt_pos c7 kk = 0"
        using c7_pos_for_pos0[OF kklt pos_kk] False by simp
      have nn_kk_0: "nn kk = 0" using nn_kk c7_kk by simp
      have zero_ne_c6_pos: "(0 :: nat) \<noteq> mt_pos c6 kk"
        using c6_pos_for_pos0[OF kklt pos_kk] by simp
      have c7_at_0: "mt_tape c7 kk 0 = mt_tape c6 kk 0"
        using mttm_step_tape_off_head[OF step7 zero_ne_c6_pos] .
      have read_LE: "tts kk (nn kk) = LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c7 kk (mt_pos c7 kk)"
          using c7_eq8 nn_kk by simp
        also have "\<dots> = mt_tape c7 kk 0" using c7_kk by simp
        also have "\<dots> = mt_tape c6 kk 0" using c7_at_0 .
        also have "\<dots> = LE_block (le_tm M)"
          using tape_c6_zero_le_for_pos0[OF kklt pos_kk] .
        finally show ?thesis .
      qed
      have dr8_kk: "dr8 kk = dir.N"
        using dr8_eq read_LE kklt by simp
      have "mt_pos c8 kk = go_dir (dr8 kk) (nn kk)"
        using c8_eq by simp
      also have "\<dots> = nn kk" using dr8_kk by simp
      also have "\<dots> = 0" using nn_kk_0 .
      finally show ?thesis using False by simp
    qed
  qed

  \<comment> \<open>Sub-step 6b4: head trajectory \<open>c8_pos\<close> for pos\<open>\<ge>\<close>2
      tapes.  Three-way case-split on \<open>dest5 kk\<close>.  For
      \<open>AE_Left\<close>: \<open>c7_pos = pos - 1\<close>, SS8 reads
      \<open>mt_tape c' kk (pos - 1)\<close> non-LE (via
      \<open>left_not_le_c'_steady\<close>, chained off SS5/SS6/SS7
      writes); action's else branch \<open>AE_Left\<close> gives \<open>(l, N)\<close>;
      \<open>c8_pos = pos - 1\<close>.  For \<open>AE_Home\<close>: \<open>c7_pos = pos + 1\<close>,
      reads \<open>mt_tape c' kk (pos + 1)\<close> non-LE (via
      \<open>right_not_le_c'\<close>); else branch \<open>AE_Home\<close> gives
      \<open>(r, L)\<close>; \<open>c8_pos = pos\<close>.  For \<open>AE_Right\<close>:
      same read as \<open>AE_Home\<close>; else branch \<open>AE_Right\<close> gives
      \<open>(r, N)\<close>; \<open>c8_pos = pos + 1\<close>.  Extracted to
      \<open>ae_fwd_c8_pos_for_pos_ge2\<close>.\<close>
  have c8_pos_for_pos_ge2:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
            \<Longrightarrow> mt_pos c8 kk = (case dest5 kk of
                                  AE_Left  \<Rightarrow> mt_pos c' kk - 1
                                | AE_Home  \<Rightarrow> mt_pos c' kk
                                | AE_Right \<Rightarrow> mt_pos c' kk + 1)"
    by (rule ae_fwd_c8_pos_for_pos_ge2[OF step5 tape_c4_eq_c'
          buf5_not_le_per_tape right_not_le_c' c4_pos step6 step7 c7_state
          buf6_eq_buf5 dest6_eq_dest5 step8_sub c5_pos_for_pos_ge2
          c5_pos_for_pos_ge2_dest_left left_not_le_c'_steady c6_pos_for_pos_ge2
          c7_pos_for_pos_ge2])
  \<comment> \<open>Sub-step 6b4: head trajectory \<open>c8_pos\<close> for pos=1 tapes.
      Three-way case-split on \<open>dest5 kk\<close>.  For \<open>AE_Left\<close>:
      defers to sub-step 5's \<open>c7_pos_for_pos1_dest_left\<close>
      (\<open>c7_pos = 0\<close>) and \<open>tape_c7_zero_le_pos1_dest_left\<close>
      (\<open>c7@0 = LE\<close>); SS8's a=LE first branch gives \<open>(a, N)\<close>;
      \<open>c8_pos = 0\<close>.  For \<open>AE_Home\<close>/\<open>AE_Right\<close>:
      \<open>c7_pos = 2\<close>, SS8 reads \<open>mt_tape c' kk 2\<close> non-LE
      (via \<open>right_not_le_c'\<close> at pos=1); \<open>h\<close> non-LE
      (\<open>buf5_not_le_per_tape\<close> pos=1); else branch dispatches
      \<open>AE_Home\<close> to dir L (\<open>c8_pos = 1\<close>), \<open>AE_Right\<close> to
      dir N (\<open>c8_pos = 2\<close>).  Extracted to
      \<open>ae_fwd_c8_pos_for_pos1\<close>.\<close>
  have c8_pos_for_pos1:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1
            \<Longrightarrow> mt_pos c8 kk = (case dest5 kk of
                                  AE_Left  \<Rightarrow> 0
                                | AE_Home  \<Rightarrow> 1
                                | AE_Right \<Rightarrow> 2)"
    by (rule ae_fwd_c8_pos_for_pos1[OF step5 tape_c4_eq_c' buf5_not_le_per_tape
          right_not_le_c' c4_pos c5_pos_for_pos1 step6 step7 c7_state
          buf6_eq_buf5 dest6_eq_dest5 c7_pos_for_pos1_dest_left
          tape_c7_zero_le_pos1_dest_left step8_sub c6_pos_for_pos1
          c7_pos_for_pos1])
  \<comment> \<open>Sub-step 6d: \<open>tape_c6_zero_le\<close>.  Cell 0 of \<open>c6\<close>
      is \<open>LE_block\<close> for every tape.  Case-split on whether SS6's
      write site \<open>mt_pos c5 kk\<close> equals 0.  If yes (pos=0 always,
      or pos=1 with \<open>dest \<noteq> AE_Left\<close>): SS6 reads
      \<open>c5@0 = LE\<close> (\<open>tape_c5_zero_le\<close>) and writes LE back via
      the first branch.  If no (pos=1 with \<open>dest = AE_Left\<close>
      has \<open>c5_pos = 2\<close>; pos\<open>\<ge>\<close>2 has
      \<open>c5_pos \<in> {pos-1, pos+1}\<close>): SS6 writes off cell 0, so
      \<open>c6@0 = c5@0 = LE\<close>.\<close>
  have tape_c6_zero_le: "\<forall>kk<k_tm M. mt_tape c6 kk 0 = LE_block (le_tm M)"
  proof (intro allI impI)
    fix kk
    assume kklt: "kk < k_tm M"
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
      and aa6_eq:
          "aa6 = (\<lambda>k. if k < k_tm M then fst (ae_ss6_action (le_tm M)
                              (tts k (nn k)) (buf k) (dest k)) else bl_block (bl_tm M))"
      using tr_in by (auto simp: ae_delta_ss6_ss7_def)
    have qq_state: "qq = (q5, ofs5, buf5, dest5, SS6)"
      using c5_state c5_eq6 by simp
    have buf_eq: "buf = buf5" using qq_eq qq_state by simp
    have nn_kk: "nn kk = mt_pos c5 kk" using c5_eq6 by simp
    show "mt_tape c6 kk 0 = LE_block (le_tm M)"
    proof (cases "mt_pos c5 kk = 0")
      case True
      have nn_kk_0: "nn kk = 0" using nn_kk True by simp
      have read_LE: "tts kk (nn kk) = LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c5 kk (mt_pos c5 kk)"
          using c5_eq6 nn_kk by simp
        also have "\<dots> = mt_tape c5 kk 0" using True by simp
        also have "\<dots> = LE_block (le_tm M)" using tape_c5_zero_le[rule_format, OF kklt] by simp
        finally show ?thesis .
      qed
      obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
        using prod.exhaust by metis
      have aa6_kk: "aa6 kk = LE_block (le_tm M)"
        using aa6_eq buf_eq buf5_kk read_LE kklt by simp
      have "mt_tape c6 kk 0 = aa6 kk" using c6_eq nn_kk_0 by simp
      also have "\<dots> = LE_block (le_tm M)" using aa6_kk .
      finally show ?thesis .
    next
      case False
      have zero_ne_c5: "(0 :: nat) \<noteq> mt_pos c5 kk" using False by simp
      have "mt_tape c6 kk 0 = mt_tape c5 kk 0"
        using mttm_step_tape_off_head[OF step6 zero_ne_c5] .
      also have "\<dots> = LE_block (le_tm M)" using tape_c5_zero_le[rule_format, OF kklt] by simp
      finally show ?thesis .
    qed
  qed

  \<comment> \<open>Sub-step 6d: \<open>tape_c7_zero_le\<close>.  Cell 0 of \<open>c7\<close>
      is \<open>LE_block\<close>.  SS7's write site \<open>mt_pos c6 kk\<close> is
      never 0: pos=0 has \<open>c6_pos = 1\<close>; pos=1 has \<open>c6_pos = 1\<close>;
      pos\<open>\<ge>\<close>2 has \<open>c6_pos = pos \<ge> 2\<close>.  Off-write,
      \<open>c7@0 = c6@0 = LE\<close>.\<close>
  have tape_c7_zero_le: "\<forall>kk<k_tm M. mt_tape c7 kk 0 = LE_block (le_tm M)"
  proof (intro allI impI)
    fix kk
    assume kklt: "kk < k_tm M"
    have zero_ne_c6: "(0 :: nat) \<noteq> mt_pos c6 kk"
    proof -
      consider (le0) "mt_pos c' kk = 0"
             | (le1) "mt_pos c' kk = 1"
             | (steady) "mt_pos c' kk \<ge> 2"
        by linarith
      thus ?thesis
      proof cases
        case le0    thus ?thesis using c6_pos_for_pos0[OF kklt le0] by simp
      next
        case le1    thus ?thesis using c6_pos_for_pos1[OF kklt le1] by simp
      next
        case steady thus ?thesis using c6_pos_for_pos_ge2[OF kklt steady] by linarith
      qed
    qed
    have "mt_tape c7 kk 0 = mt_tape c6 kk 0"
      using mttm_step_tape_off_head[OF step7 zero_ne_c6] .
    also have "\<dots> = LE_block (le_tm M)"
      using tape_c6_zero_le[rule_format, OF kklt] by simp
    finally show "mt_tape c7 kk 0 = LE_block (le_tm M)" .
  qed

  \<comment> \<open>Sub-step 6d: \<open>tape_c8_zero_le\<close>.  Cell 0 of \<open>c8\<close>
      is \<open>LE_block\<close>.  Case-split on whether SS8's write site
      \<open>mt_pos c7 kk\<close> equals 0.  If yes (pos=0 with \<open>dest \<noteq>
      AE_Right\<close>, or pos=1 with \<open>dest = AE_Left\<close>): SS8 reads
      \<open>c7@0 = LE\<close> (\<open>tape_c7_zero_le\<close>) and writes LE back
      via the first branch.  If no: SS8 writes off 0, so
      \<open>c8@0 = c7@0 = LE\<close>.\<close>
  have tape_c8_zero_le: "\<forall>kk<k_tm M. mt_tape c8 kk 0 = LE_block (le_tm M)"
  proof (intro allI impI)
    fix kk
    assume kklt: "kk < k_tm M"
    obtain qq tts nn qq' aa8 dr8 where
        c7_eq8: "c7 = Config\<^sub>M qq tts nn"
      and c8_eq: "c8 = Config\<^sub>M qq'
                          (\<lambda>k. (tts k)(nn k := aa8 k))
                          (\<lambda>k. go_dir (dr8 k) (nn k))"
      and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa8, dr8)
                    \<in> ae_delta_ss8_ss1 M"
      using step8_sub by (auto elim: mttm_step.cases)
    obtain q ofs buf dest where
        qq_eq: "qq = (q, ofs, buf, dest, SS8)"
      and aa8_eq:
          "aa8 = (\<lambda>k. if k < k_tm M then fst (ae_ss8_action (le_tm M)
                              (tts k (nn k)) (buf k) (dest k)) else bl_block (bl_tm M))"
      using tr_in by (auto simp: ae_delta_ss8_ss1_def)
    have nn_kk: "nn kk = mt_pos c7 kk" using c7_eq8 by simp
    show "mt_tape c8 kk 0 = LE_block (le_tm M)"
    proof (cases "mt_pos c7 kk = 0")
      case True
      have nn_kk_0: "nn kk = 0" using nn_kk True by simp
      have read_LE: "tts kk (nn kk) = LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c7 kk (mt_pos c7 kk)"
          using c7_eq8 nn_kk by simp
        also have "\<dots> = mt_tape c7 kk 0" using True by simp
        also have "\<dots> = LE_block (le_tm M)"
          using tape_c7_zero_le[rule_format, OF kklt] by simp
        finally show ?thesis .
      qed
      obtain ll hh rr where buf_kk: "buf kk = (ll, hh, rr)"
        using prod.exhaust by metis
      have aa8_kk: "aa8 kk = LE_block (le_tm M)"
        using aa8_eq buf_kk read_LE kklt by simp
      have "mt_tape c8 kk 0 = aa8 kk" using c8_eq nn_kk_0 by simp
      also have "\<dots> = LE_block (le_tm M)" using aa8_kk .
      finally show ?thesis .
    next
      case False
      have zero_ne_c7: "(0 :: nat) \<noteq> mt_pos c7 kk" using False by simp
      have "mt_tape c8 kk 0 = mt_tape c7 kk 0"
        using mttm_step_tape_off_head[OF step8 zero_ne_c7] .
      also have "\<dots> = LE_block (le_tm M)"
        using tape_c7_zero_le[rule_format, OF kklt] by simp
      finally show ?thesis .
    qed
  qed

  \<comment> \<open>Sub-step 6b6: M'-side off-window preservation.
      Regime-agnostic form: cells outside all four SS5\<open>\<dots>\<close>SS8 write
      sites are preserved from \<open>c'\<close>.  Each substep writes at one
      per-tape position; chaining the four \<open>mttm_step_tape_off_head\<close>
      facts plus \<open>tape_c4_eq_c'\<close> gives the result.  Per-regime
      instantiation provides the s-not-in-window precondition.\<close>
  have c8_tape_off_window:
      "\<And>kk s. s \<noteq> mt_pos c4 kk \<Longrightarrow> s \<noteq> mt_pos c5 kk
              \<Longrightarrow> s \<noteq> mt_pos c6 kk \<Longrightarrow> s \<noteq> mt_pos c7 kk
              \<Longrightarrow> mt_tape c8 kk s = mt_tape c' kk s"
  proof -
    fix kk
    fix s :: nat
    assume s_ne_c4: "s \<noteq> mt_pos c4 kk"
    assume s_ne_c5: "s \<noteq> mt_pos c5 kk"
    assume s_ne_c6: "s \<noteq> mt_pos c6 kk"
    assume s_ne_c7: "s \<noteq> mt_pos c7 kk"
    have c5_eq_c4: "mt_tape c5 kk s = mt_tape c4 kk s"
      using mttm_step_tape_off_head[OF step5 s_ne_c4] .
    have c6_eq_c5: "mt_tape c6 kk s = mt_tape c5 kk s"
      using mttm_step_tape_off_head[OF step6 s_ne_c5] .
    have c7_eq_c6: "mt_tape c7 kk s = mt_tape c6 kk s"
      using mttm_step_tape_off_head[OF step7 s_ne_c6] .
    have c8_eq_c7: "mt_tape c8 kk s = mt_tape c7 kk s"
      using mttm_step_tape_off_head[OF step8 s_ne_c7] .
    show "mt_tape c8 kk s = mt_tape c' kk s"
      using c8_eq_c7 c7_eq_c6 c6_eq_c5 c5_eq_c4 tape_c4_eq_c' by simp
  qed

  \<comment> \<open>Sub-step 6b5: pos=0 in-window c8 value at block 1.
      Uniformly \<open>c8@1 = rr\<close> (= the buf5 right slot).  Case-split
      on \<open>dest5 kk = AE_Right\<close>.  For \<open>dest = AE_Right\<close>:
      SS7 wrote \<open>r\<close> at \<open>c6_pos = 1\<close>; SS8 wrote at \<open>c7_pos = 1\<close>
      with action h=LE+dest=Right giving \<open>(r, N)\<close>; \<open>c8@1 = r\<close>.
      For \<open>dest \<noteq> AE_Right\<close>: SS7 wrote \<open>r\<close> at \<open>c6_pos = 1\<close>
      (action h=LE+dest\<open>\<ne>\<close>Right gives \<open>(r, L)\<close>); SS8 wrote at
      \<open>c7_pos = 0 \<noteq> 1\<close>, off-write; \<open>c8@1 = c7@1 = r\<close>.
      Extracted to \<open>ae_fwd_c8_at_one_for_pos0\<close>.\<close>
  have c8_tape_at_one_for_pos0:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 0
            \<Longrightarrow> mt_tape c8 kk 1 = snd (snd (buf5 kk))"
    by (rule ae_fwd_c8_at_one_for_pos0[OF step5 tape_c4_eq_c'
          buf5_not_le_per_tape right_not_le_c' c4_pos step6 step7_sub c6_state
          c7_state buf6_eq_buf5 dest6_eq_dest5 step8_sub step8 c5_pos_for_pos0
          buf5_h_le_for_pos0 c6_pos_for_pos0 c7_pos_for_pos0])
  \<comment> \<open>Sub-step 6b5 helper: \<open>c7\<close>'s block 1 for pos=1 tapes.
      Uniformly \<open>c7@1 = hh\<close>.  SS7 writes \<open>aa7\<close> at \<open>c6_pos = 1\<close>;
      action reads \<open>a = c6@1 = c5@1 = hh\<close> (via off SS6 write at
      \<open>c5_pos \<in> {0, 2}\<close>, then \<open>tape_c5_at_one_pos1\<close>), h non-LE;
      else branch writes \<open>a = hh\<close> regardless of \<open>dest\<close>.\<close>
  have c7_tape_at_one_for_pos1:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1
            \<Longrightarrow> mt_tape c7 kk 1 = fst (snd (buf5 kk))"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume pos_kk: "mt_pos c' kk = 1"
    obtain qq tts nn qq' aa7 dr7 where
        c6_eq7: "c6 = Config\<^sub>M qq tts nn"
      and c7_eq: "c7 = Config\<^sub>M qq'
                          (\<lambda>k. (tts k)(nn k := aa7 k))
                          (\<lambda>k. go_dir (dr7 k) (nn k))"
      and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa7, dr7)
                    \<in> ae_delta_ss7_ss8 M"
      using step7_sub by (auto elim: mttm_step.cases)
    obtain q7 ofs7 buf7 dest7 where
        qq_eq: "qq = (q7, ofs7, buf7, dest7, SS7)"
      and aa7_eq:
          "aa7 = (\<lambda>k. if k < k_tm M then fst (ae_ss7_action (le_tm M)
                              (tts k (nn k)) (buf7 k) (dest7 k)) else bl_block (bl_tm M))"
      using tr_in by (auto simp: ae_delta_ss7_ss8_def)
    have qq_state: "qq = (q6, ofs6, buf6, dest6, SS7)"
      using c6_state c6_eq7 by simp
    have buf7_eq: "buf7 = buf6" using qq_eq qq_state by simp
    have dest7_eq: "dest7 = dest6" using qq_eq qq_state by simp
    have nn_kk: "nn kk = mt_pos c6 kk" using c6_eq7 by simp
    have c6_kk: "mt_pos c6 kk = 1" using c6_pos_for_pos1[OF kklt pos_kk] .
    have nn_kk_1: "nn kk = 1" using nn_kk c6_kk by simp
    have one_ne_c5_pos: "(1 :: nat) \<noteq> mt_pos c5 kk"
    proof (cases "dest5 kk = AE_Left")
      case True
      have "mt_pos c5 kk = 2"
        using c5_pos_for_pos1_dest_left[OF kklt pos_kk True] .
      thus ?thesis by simp
    next
      case False
      have "mt_pos c5 kk = 0"
        using c5_pos_for_pos1[OF kklt pos_kk False] .
      thus ?thesis by simp
    qed
    have c6_at_1_eq_hh:
        "mt_tape c6 kk 1 = fst (snd (buf5 kk))"
    proof -
      have "mt_tape c6 kk 1 = mt_tape c5 kk 1"
        using mttm_step_tape_off_head[OF step6 one_ne_c5_pos] .
      also have "\<dots> = fst (snd (buf5 kk))"
        using tape_c5_at_one_pos1[OF kklt pos_kk] .
      finally show ?thesis .
    qed
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have buf6_kk: "buf6 kk = (ll, hh, rr)"
      using buf5_kk buf6_eq_buf5 by simp
    have h_ne_LE: "hh \<noteq> LE_block (le_tm M)"
    proof -
      have "fst (snd (buf5 kk)) \<noteq> LE_block (le_tm M)"
        using buf5_not_le_per_tape[rule_format, OF kklt] pos_kk by blast
      thus ?thesis using buf5_kk by simp
    qed
    have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
    proof -
      have "tts kk (nn kk) = mt_tape c6 kk (mt_pos c6 kk)"
        using c6_eq7 nn_kk by simp
      also have "\<dots> = mt_tape c6 kk 1" using c6_kk by simp
      also have "\<dots> = fst (snd (buf5 kk))" using c6_at_1_eq_hh .
      also have "\<dots> = hh" using buf5_kk by simp
      finally have "tts kk (nn kk) = hh" .
      thus ?thesis using h_ne_LE by simp
    qed
    \<comment> \<open>Action's else branch fires, returning \<open>(a, _)\<close> regardless
        of \<open>dest\<close>.\<close>
    have aa7_kk: "aa7 kk = tts kk (nn kk)"
      using aa7_eq buf7_eq buf6_kk h_ne_LE read_ne_LE kklt by simp
    have tts_eq_hh: "tts kk (nn kk) = hh"
    proof -
      have "tts kk (nn kk) = mt_tape c6 kk 1"
        using c6_eq7 nn_kk_1 by simp
      also have "\<dots> = fst (snd (buf5 kk))" using c6_at_1_eq_hh .
      also have "\<dots> = hh" using buf5_kk by simp
      finally show ?thesis .
    qed
    have "mt_tape c7 kk 1 = aa7 kk" using c7_eq nn_kk_1 by simp
    also have "\<dots> = tts kk (nn kk)" using aa7_kk .
    also have "\<dots> = hh" using tts_eq_hh .
    also have "\<dots> = fst (snd (buf5 kk))" using buf5_kk by simp
    finally show "mt_tape c7 kk 1 = fst (snd (buf5 kk))" .
  qed

  \<comment> \<open>Sub-step 6b5: pos=1 in-window c8 value at block 1.
      \<open>c7_pos \<in> {0, 2}\<close>, never 1; so SS8 writes off cell 1.
      \<open>c8@1 = c7@1 = hh\<close>.\<close>
  have c8_tape_at_one_for_pos1:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1
            \<Longrightarrow> mt_tape c8 kk 1 = fst (snd (buf5 kk))"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume pos_kk: "mt_pos c' kk = 1"
    have c7_pos_ne_1: "mt_pos c7 kk \<noteq> 1"
    proof (cases "dest5 kk = AE_Left")
      case True
      have "mt_pos c7 kk = 0"
        using c7_pos_for_pos1_dest_left[OF kklt pos_kk True] .
      thus ?thesis by simp
    next
      case False
      have "mt_pos c7 kk = 2"
        using c7_pos_for_pos1[OF kklt pos_kk] False by simp
      thus ?thesis by simp
    qed
    have ne: "(1 :: nat) \<noteq> mt_pos c7 kk" using c7_pos_ne_1 by simp
    have "mt_tape c8 kk 1 = mt_tape c7 kk 1"
      using mttm_step_tape_off_head[OF step8 ne] .
    also have "\<dots> = fst (snd (buf5 kk))"
      using c7_tape_at_one_for_pos1[OF kklt pos_kk] .
    finally show "mt_tape c8 kk 1 = fst (snd (buf5 kk))" .
  qed

  \<comment> \<open>Sub-step 6b5: pos=1 in-window c8 value at block 2.
      Three-way case-split on \<open>dest5 kk\<close>; uniformly \<open>c8@2 = rr\<close>.
      For \<open>AE_Left\<close>: SS6 writes \<open>r\<close> at \<open>c5_pos = 2\<close>
      (action's else branch with \<open>ds = AE_Left\<close> gives \<open>(r, L)\<close>);
      SS7, SS8 off cell 2.  For \<open>AE_Home\<close>/\<open>AE_Right\<close>: SS6,
      SS7 off cell 2; SS8 writes \<open>r\<close> at \<open>c7_pos = 2\<close> (action's
      else branch with \<open>ds = AE_Home\<close> gives \<open>(r, L)\<close>,
      \<open>ds = AE_Right\<close> gives \<open>(r, N)\<close>).  Extracted to
      \<open>ae_fwd_c8_at_two_for_pos1\<close>.\<close>
  have c8_tape_at_two_for_pos1:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1
            \<Longrightarrow> mt_tape c8 kk 2 = snd (snd (buf5 kk))"
    by (rule ae_fwd_c8_at_two_for_pos1[OF step5 c5_state tape_c4_eq_c'
          buf5_not_le_per_tape right_not_le_c' c4_pos c5_pos_for_pos1 step6_sub
          step6 step7 c7_state buf6_eq_buf5 dest6_eq_dest5
          c5_pos_for_pos1_dest_left c7_pos_for_pos1_dest_left step8_sub step8
          c6_pos_for_pos1 c7_pos_for_pos1])
  \<comment> \<open>Sub-step 6b5 helper: \<open>c7\<close>'s block pos for pos\<open>\<ge>\<close>2.
      Uniformly \<open>c7@pos = hh\<close>.  SS7 writes \<open>aa7\<close> at \<open>c6_pos =
      pos\<close>; action reads \<open>a = c6@pos = c5@pos = hh\<close> (via off
      SS6 write at \<open>c5_pos = pos \<mp> 1\<close>, then
      \<open>tape_c5_at_pos_for_pos_ge2\<close>); else branch writes \<open>a = hh\<close>
      regardless of \<open>dest\<close>.\<close>
  have c7_tape_at_pos_for_pos_ge2:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
            \<Longrightarrow> mt_tape c7 kk (mt_pos c' kk) = fst (snd (buf5 kk))"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume hge2: "mt_pos c' kk \<ge> 2"
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
      and aa7_eq:
          "aa7 = (\<lambda>k. if k < k_tm M then fst (ae_ss7_action (le_tm M)
                              (tts k (nn k)) (buf k) (dest k)) else bl_block (bl_tm M))"
      using tr_in by (auto simp: ae_delta_ss7_ss8_def)
    have qq_state: "qq = (q6, ofs6, buf6, dest6, SS7)"
      using c6_state c6_eq7 by simp
    have buf_eq: "buf = buf6" using qq_eq qq_state by simp
    have nn_kk: "nn kk = mt_pos c6 kk" using c6_eq7 by simp
    have c6_kk: "mt_pos c6 kk = mt_pos c' kk"
      using c6_pos_for_pos_ge2[OF kklt hge2] .
    have nn_kk_pos: "nn kk = mt_pos c' kk" using nn_kk c6_kk by simp
    have pos_ne_c5: "mt_pos c' kk \<noteq> mt_pos c5 kk"
    proof (cases "dest5 kk = AE_Left")
      case True
      have "mt_pos c5 kk = mt_pos c' kk + 1"
        using c5_pos_for_pos_ge2_dest_left[OF kklt hge2 True] .
      thus ?thesis by linarith
    next
      case False
      have "mt_pos c5 kk = mt_pos c' kk - 1"
        using c5_pos_for_pos_ge2[OF kklt hge2 False] .
      thus ?thesis using hge2 by linarith
    qed
    have c6_at_pos:
        "mt_tape c6 kk (mt_pos c' kk) = fst (snd (buf5 kk))"
    proof -
      have "mt_tape c6 kk (mt_pos c' kk) = mt_tape c5 kk (mt_pos c' kk)"
        using mttm_step_tape_off_head[OF step6 pos_ne_c5] .
      also have "\<dots> = fst (snd (buf5 kk))"
        using tape_c5_at_pos_for_pos_ge2[OF kklt hge2] .
      finally show ?thesis .
    qed
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have buf6_kk: "buf6 kk = (ll, hh, rr)"
      using buf5_kk buf6_eq_buf5 by simp
    have h_ne_LE: "hh \<noteq> LE_block (le_tm M)"
    proof -
      have "fst (snd (buf5 kk)) \<noteq> LE_block (le_tm M)"
        using buf5_not_le_per_tape[rule_format, OF kklt] hge2 by blast
      thus ?thesis using buf5_kk by simp
    qed
    have read_eq_hh: "tts kk (nn kk) = hh"
    proof -
      have "tts kk (nn kk) = mt_tape c6 kk (mt_pos c6 kk)"
        using c6_eq7 nn_kk by simp
      also have "\<dots> = mt_tape c6 kk (mt_pos c' kk)" using c6_kk by simp
      also have "\<dots> = fst (snd (buf5 kk))" using c6_at_pos .
      also have "\<dots> = hh" using buf5_kk by simp
      finally show ?thesis .
    qed
    have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      using read_eq_hh h_ne_LE by simp
    have aa7_kk: "aa7 kk = tts kk (nn kk)"
      using aa7_eq buf_eq buf6_kk h_ne_LE read_ne_LE kklt by simp
    have "mt_tape c7 kk (mt_pos c' kk) = aa7 kk"
      using c7_eq nn_kk_pos by simp
    also have "\<dots> = tts kk (nn kk)" using aa7_kk .
    also have "\<dots> = hh" using read_eq_hh .
    also have "\<dots> = fst (snd (buf5 kk))" using buf5_kk by simp
    finally show "mt_tape c7 kk (mt_pos c' kk) = fst (snd (buf5 kk))" .
  qed

  \<comment> \<open>Sub-step 6b5: pos\<open>\<ge>\<close>2 in-window c8 value at block
      pos.  Uniformly \<open>c8@pos = hh\<close>.  SS8 writes at \<open>c7_pos = pos \<mp> 1\<close>,
      never pos for pos\<open>\<ge>\<close>2; \<open>c8@pos = c7@pos = hh\<close>
      via off-write preservation and \<open>c7_tape_at_pos_for_pos_ge2\<close>.\<close>
  have c8_tape_at_pos_for_pos_ge2:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
            \<Longrightarrow> mt_tape c8 kk (mt_pos c' kk) = fst (snd (buf5 kk))"
  proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume hge2: "mt_pos c' kk \<ge> 2"
    have pos_ne_c7: "mt_pos c' kk \<noteq> mt_pos c7 kk"
    proof (cases "dest5 kk = AE_Left")
      case True
      have "mt_pos c7 kk = mt_pos c' kk - 1"
        using c7_pos_for_pos_ge2[OF kklt hge2] True by simp
      thus ?thesis using hge2 by linarith
    next
      case False
      have "mt_pos c7 kk = mt_pos c' kk + 1"
        using c7_pos_for_pos_ge2[OF kklt hge2] False by simp
      thus ?thesis by linarith
    qed
    have "mt_tape c8 kk (mt_pos c' kk) = mt_tape c7 kk (mt_pos c' kk)"
      using mttm_step_tape_off_head[OF step8 pos_ne_c7] .
    also have "\<dots> = fst (snd (buf5 kk))"
      using c7_tape_at_pos_for_pos_ge2[OF kklt hge2] .
    finally show "mt_tape c8 kk (mt_pos c' kk) = fst (snd (buf5 kk))" .
  qed

  \<comment> \<open>Sub-step 6b5: pos\<open>\<ge>\<close>2 in-window c8 value at block
      pos-1.  Uniformly \<open>c8@(pos-1) = ll\<close>.  Three-way dest case-split.
      For \<open>AE_Left\<close>: SS5/SS6/SS7 off pos-1; SS8 writes \<open>l\<close> at
      \<open>c7_pos = pos - 1\<close> (action's else branch with \<open>ds = AE_Left\<close>
      gives \<open>(l, N)\<close>).  For \<open>AE_Home\<close>/\<open>AE_Right\<close>: SS6 writes
      \<open>l\<close> at \<open>c5_pos = pos - 1\<close> (action's else branch with
      \<open>ds \<noteq> AE_Left\<close> gives \<open>(l, R)\<close>); SS7, SS8 off pos-1.
      Extracted to \<open>ae_fwd_c8_at_pos_minus_1_ge2\<close>.\<close>
  have c8_tape_at_pos_minus_1_for_pos_ge2:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
            \<Longrightarrow> mt_tape c8 kk (mt_pos c' kk - 1) = fst (buf5 kk)"
    by (rule ae_fwd_c8_at_pos_minus_1_ge2[OF step5 c5_state tape_c4_eq_c'
          buf5_not_le_per_tape c4_pos step6_sub step6 step7 c7_state
          buf6_eq_buf5 dest6_eq_dest5 step8_sub step8 c5_pos_for_pos_ge2
          c5_pos_for_pos_ge2_dest_left left_not_le_c'_steady
          c6_pos_for_pos_ge2 c7_pos_for_pos_ge2])
  \<comment> \<open>Sub-step 6b5: pos\<open>\<ge>\<close>2 in-window c8 value at block
      pos+1.  Uniformly \<open>c8@(pos+1) = rr\<close>.  Three-way dest case-split.
      For \<open>AE_Left\<close>: SS6 writes \<open>r\<close> at \<open>c5_pos = pos + 1\<close>
      (else branch with \<open>ds = AE_Left\<close> gives \<open>(r, L)\<close>); SS7, SS8
      off pos+1.  For \<open>AE_Home\<close>/\<open>AE_Right\<close>: SS6/SS7 off pos+1;
      SS8 writes \<open>r\<close> at \<open>c7_pos = pos + 1\<close> (else branch with
      \<open>ds = AE_Home\<close> gives \<open>(r, L)\<close>, \<open>ds = AE_Right\<close> gives
      \<open>(r, N)\<close>).  Extracted to \<open>ae_fwd_c8_at_pos_plus_1_ge2\<close>.\<close>
  have c8_tape_at_pos_plus_1_for_pos_ge2:
      "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
            \<Longrightarrow> mt_tape c8 kk (mt_pos c' kk + 1) = snd (snd (buf5 kk))"
    by (rule ae_fwd_c8_at_pos_plus_1_ge2[OF step5 c5_state tape_c4_eq_c'
          buf5_not_le_per_tape right_not_le_c' c4_pos step6_sub step6 step7
          c7_state buf6_eq_buf5 dest6_eq_dest5 step8_sub step8
          c5_pos_for_pos_ge2 c5_pos_for_pos_ge2_dest_left c6_pos_for_pos_ge2
          c7_pos_for_pos_ge2])
  let ?c = "card (UNIV :: 'c set)"

  \<comment> \<open>Sub-step 6b5: M-side buf-lin transfers per regime, per
      in-window block.  Projects the window invariant's
      linearisation clause for each \<open>(regime, s)\<close> pair.  Six
      lemmas: pos=0/s=1; pos=1/s=1,2; pos\<open>\<ge>\<close>2/s=pos-1,pos,pos+1.\<close>
  have tape_cM_k_at_one_for_pos0:
      "\<And>kk i. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 0
              \<Longrightarrow> mt_tape cM_k kk (Suc (c_idx (i :: 'c)))
                    = (snd (snd (buf5 kk))) i"
  proof -
    fix kk
    fix i :: 'c
    assume kklt: "kk < k_tm M"
    assume pos_kk: "mt_pos c' kk = 0"
    have c_idx_lt: "c_idx i < ?c" by (rule c_idx_lt_card)
    have wi: "ae_window_invariant_general
                (mt_tape cM_k kk) (mt_pos cM_k kk)
                (dest5 kk, ofs5 kk) (buf5 kk)
                (mt_pos c' kk) (le_tm M)"
      using cM_k_window_general[rule_format, OF kklt] by simp
    hence win_le0: "ae_window_invariant_le0
              (mt_tape cM_k kk) (mt_pos cM_k kk)
              (dest5 kk, ofs5 kk) (buf5 kk) (le_tm M)"
      using pos_kk unfolding ae_window_invariant_general_def by simp
    have buf_eq:
        "mt_tape cM_k kk (Suc (c_idx i))
            = buf_lin_at (buf5 kk) (2 * ?c + c_idx i)"
      using win_le0 c_idx_lt unfolding ae_window_invariant_le0_def by blast
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have not_lt_c: "\<not> 2 * ?c + c_idx i < ?c" by simp
    have not_lt_2c: "\<not> 2 * ?c + c_idx i < 2 * ?c" by simp
    have buf_lin_eq:
        "buf_lin_at (buf5 kk) (2 * ?c + c_idx i)
            = rr ((enum_class.enum :: 'c list) ! ((2 * ?c + c_idx i) - 2 * ?c))"
      using buf5_kk not_lt_c not_lt_2c
      unfolding buf_lin_at_def Let_def by simp
    have sub_simp: "(2 * ?c + c_idx i) - 2 * ?c = c_idx i" by simp
    have enum_at_idx:
        "(enum_class.enum :: 'c list) ! c_idx i = i"
      by (rule c_idx_in_range(2))
    show "mt_tape cM_k kk (Suc (c_idx i)) = (snd (snd (buf5 kk))) i"
      using buf_eq buf_lin_eq sub_simp enum_at_idx buf5_kk by simp
  qed

  have tape_cM_k_at_one_for_pos1:
      "\<And>kk i. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1
              \<Longrightarrow> mt_tape cM_k kk (Suc (c_idx (i :: 'c)))
                    = (fst (snd (buf5 kk))) i"
  proof -
    fix kk
    fix i :: 'c
    assume kklt: "kk < k_tm M"
    assume pos_kk: "mt_pos c' kk = 1"
    have c_idx_lt: "c_idx i < ?c" by (rule c_idx_lt_card)
    have c_idx_lt_2c: "c_idx i < 2 * ?c" using c_idx_lt by linarith
    have wi: "ae_window_invariant_general
                (mt_tape cM_k kk) (mt_pos cM_k kk)
                (dest5 kk, ofs5 kk) (buf5 kk)
                (mt_pos c' kk) (le_tm M)"
      using cM_k_window_general[rule_format, OF kklt] by simp
    hence win_le1: "ae_window_invariant_le1
              (mt_tape cM_k kk) (mt_pos cM_k kk)
              (dest5 kk, ofs5 kk) (buf5 kk) (le_tm M)"
      using pos_kk unfolding ae_window_invariant_general_def by simp
    have buf_eq:
        "mt_tape cM_k kk (Suc (c_idx i))
            = buf_lin_at (buf5 kk) (?c + c_idx i)"
      using win_le1 c_idx_lt_2c unfolding ae_window_invariant_le1_def by blast
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have lt_2c: "?c + c_idx i < 2 * ?c" using c_idx_lt by linarith
    have not_lt_c: "\<not> ?c + c_idx i < ?c" by simp
    have buf_lin_eq:
        "buf_lin_at (buf5 kk) (?c + c_idx i)
            = hh ((enum_class.enum :: 'c list) ! ((?c + c_idx i) - ?c))"
      using buf5_kk not_lt_c lt_2c
      unfolding buf_lin_at_def Let_def by simp
    have sub_simp: "(?c + c_idx i) - ?c = c_idx i" by simp
    have enum_at_idx:
        "(enum_class.enum :: 'c list) ! c_idx i = i"
      by (rule c_idx_in_range(2))
    show "mt_tape cM_k kk (Suc (c_idx i)) = (fst (snd (buf5 kk))) i"
      using buf_eq buf_lin_eq sub_simp enum_at_idx buf5_kk by simp
  qed

  have tape_cM_k_at_two_for_pos1:
      "\<And>kk i. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1
              \<Longrightarrow> mt_tape cM_k kk (Suc (?c + c_idx (i :: 'c)))
                    = (snd (snd (buf5 kk))) i"
  proof -
    fix kk
    fix i :: 'c
    assume kklt: "kk < k_tm M"
    assume pos_kk: "mt_pos c' kk = 1"
    have c_idx_lt: "c_idx i < ?c" by (rule c_idx_lt_card)
    have addr_lt_2c: "?c + c_idx i < 2 * ?c" using c_idx_lt by linarith
    have wi: "ae_window_invariant_general
                (mt_tape cM_k kk) (mt_pos cM_k kk)
                (dest5 kk, ofs5 kk) (buf5 kk)
                (mt_pos c' kk) (le_tm M)"
      using cM_k_window_general[rule_format, OF kklt] by simp
    hence win_le1: "ae_window_invariant_le1
              (mt_tape cM_k kk) (mt_pos cM_k kk)
              (dest5 kk, ofs5 kk) (buf5 kk) (le_tm M)"
      using pos_kk unfolding ae_window_invariant_general_def by simp
    have buf_eq:
        "mt_tape cM_k kk (Suc (?c + c_idx i))
            = buf_lin_at (buf5 kk) (?c + (?c + c_idx i))"
      using win_le1 addr_lt_2c unfolding ae_window_invariant_le1_def by blast
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have addr_eq: "?c + (?c + c_idx i) = 2 * ?c + c_idx i" by simp
    have not_lt_c: "\<not> 2 * ?c + c_idx i < ?c" by simp
    have not_lt_2c: "\<not> 2 * ?c + c_idx i < 2 * ?c" by simp
    have buf_lin_eq:
        "buf_lin_at (buf5 kk) (2 * ?c + c_idx i)
            = rr ((enum_class.enum :: 'c list) ! ((2 * ?c + c_idx i) - 2 * ?c))"
      using buf5_kk not_lt_c not_lt_2c
      unfolding buf_lin_at_def Let_def by simp
    have sub_simp: "(2 * ?c + c_idx i) - 2 * ?c = c_idx i" by simp
    have enum_at_idx:
        "(enum_class.enum :: 'c list) ! c_idx i = i"
      by (rule c_idx_in_range(2))
    show "mt_tape cM_k kk (Suc (?c + c_idx i)) = (snd (snd (buf5 kk))) i"
      using buf_eq addr_eq buf_lin_eq sub_simp enum_at_idx buf5_kk by simp
  qed

  have tape_cM_k_at_pos_minus_1_for_pos_ge2:
      "\<And>kk i. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
              \<Longrightarrow> mt_tape cM_k kk ((mt_pos c' kk - 2) * ?c
                                    + c_idx (i :: 'c) + 1)
                    = (fst (buf5 kk)) i"
  proof -
    fix kk
    fix i :: 'c
    assume kklt: "kk < k_tm M"
    assume hge2: "mt_pos c' kk \<ge> 2"
    have c_idx_lt: "c_idx i < ?c" by (rule c_idx_lt_card)
    have c_idx_lt_3c: "c_idx i < 3 * ?c" using c_idx_lt by linarith
    have wi: "ae_window_invariant_general
                (mt_tape cM_k kk) (mt_pos cM_k kk)
                (dest5 kk, ofs5 kk) (buf5 kk)
                (mt_pos c' kk) (le_tm M)"
      using cM_k_window_general[rule_format, OF kklt] by simp
    hence win_steady:
        "ae_window_invariant (mt_tape cM_k kk) (mt_pos cM_k kk)
            (dest5 kk, ofs5 kk) (buf5 kk)
            ((mt_pos c' kk - 2) * ?c + 1)"
      using hge2 unfolding ae_window_invariant_general_def by simp
    have buf_eq:
        "mt_tape cM_k kk (((mt_pos c' kk - 2) * ?c + 1) + c_idx i)
            = buf_lin_at (buf5 kk) (c_idx i)"
      using win_steady c_idx_lt_3c
      unfolding ae_window_invariant_def by blast
    have addr_simp:
        "((mt_pos c' kk - 2) * ?c + 1) + c_idx i
          = (mt_pos c' kk - 2) * ?c + c_idx i + 1" by simp
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have buf_lin_eq:
        "buf_lin_at (buf5 kk) (c_idx i)
            = ll ((enum_class.enum :: 'c list) ! c_idx i)"
      using buf5_kk c_idx_lt unfolding buf_lin_at_def Let_def by simp
    have enum_at_idx:
        "(enum_class.enum :: 'c list) ! c_idx i = i"
      by (rule c_idx_in_range(2))
    show "mt_tape cM_k kk ((mt_pos c' kk - 2) * ?c + c_idx i + 1)
            = (fst (buf5 kk)) i"
      using buf_eq addr_simp buf_lin_eq enum_at_idx buf5_kk by simp
  qed

  have tape_cM_k_at_pos_for_pos_ge2:
      "\<And>kk i. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
              \<Longrightarrow> mt_tape cM_k kk ((mt_pos c' kk - 1) * ?c
                                    + c_idx (i :: 'c) + 1)
                    = (fst (snd (buf5 kk))) i"
  proof -
    fix kk
    fix i :: 'c
    assume kklt: "kk < k_tm M"
    assume hge2: "mt_pos c' kk \<ge> 2"
    have c_idx_lt: "c_idx i < ?c" by (rule c_idx_lt_card)
    have addr_lt_3c: "?c + c_idx i < 3 * ?c" using c_idx_lt by linarith
    have wi: "ae_window_invariant_general
                (mt_tape cM_k kk) (mt_pos cM_k kk)
                (dest5 kk, ofs5 kk) (buf5 kk)
                (mt_pos c' kk) (le_tm M)"
      using cM_k_window_general[rule_format, OF kklt] by simp
    hence win_steady:
        "ae_window_invariant (mt_tape cM_k kk) (mt_pos cM_k kk)
            (dest5 kk, ofs5 kk) (buf5 kk)
            ((mt_pos c' kk - 2) * ?c + 1)"
      using hge2 unfolding ae_window_invariant_general_def by simp
    have buf_eq:
        "mt_tape cM_k kk (((mt_pos c' kk - 2) * ?c + 1) + (?c + c_idx i))
            = buf_lin_at (buf5 kk) (?c + c_idx i)"
      using win_steady addr_lt_3c
      unfolding ae_window_invariant_def by blast
    have addr_simp:
        "((mt_pos c' kk - 2) * ?c + 1) + (?c + c_idx i)
          = (mt_pos c' kk - 1) * ?c + c_idx i + 1"
      using hge2 by (simp add: algebra_simps diff_mult_distrib)
    have buf_eq_rewritten:
        "mt_tape cM_k kk ((mt_pos c' kk - 1) * ?c + c_idx i + 1)
            = buf_lin_at (buf5 kk) (?c + c_idx i)"
      using buf_eq[unfolded addr_simp] .
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have not_lt_c: "\<not> ?c + c_idx i < ?c" by simp
    have lt_2c: "?c + c_idx i < 2 * ?c" using c_idx_lt by linarith
    have buf_lin_eq:
        "buf_lin_at (buf5 kk) (?c + c_idx i)
            = hh ((enum_class.enum :: 'c list) ! ((?c + c_idx i) - ?c))"
      using buf5_kk not_lt_c lt_2c
      unfolding buf_lin_at_def Let_def by simp
    have sub_simp: "(?c + c_idx i) - ?c = c_idx i" by simp
    have enum_at_idx:
        "(enum_class.enum :: 'c list) ! c_idx i = i"
      by (rule c_idx_in_range(2))
    show "mt_tape cM_k kk ((mt_pos c' kk - 1) * ?c + c_idx i + 1)
            = (fst (snd (buf5 kk))) i"
      using buf_eq_rewritten buf_lin_eq sub_simp enum_at_idx buf5_kk by simp
  qed

  have tape_cM_k_at_pos_plus_1_for_pos_ge2:
      "\<And>kk i. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
              \<Longrightarrow> mt_tape cM_k kk (mt_pos c' kk * ?c
                                    + c_idx (i :: 'c) + 1)
                    = (snd (snd (buf5 kk))) i"
  proof -
    fix kk
    fix i :: 'c
    assume kklt: "kk < k_tm M"
    assume hge2: "mt_pos c' kk \<ge> 2"
    have c_idx_lt: "c_idx i < ?c" by (rule c_idx_lt_card)
    have addr_lt_3c: "2 * ?c + c_idx i < 3 * ?c" using c_idx_lt by linarith
    have wi: "ae_window_invariant_general
                (mt_tape cM_k kk) (mt_pos cM_k kk)
                (dest5 kk, ofs5 kk) (buf5 kk)
                (mt_pos c' kk) (le_tm M)"
      using cM_k_window_general[rule_format, OF kklt] by simp
    hence win_steady:
        "ae_window_invariant (mt_tape cM_k kk) (mt_pos cM_k kk)
            (dest5 kk, ofs5 kk) (buf5 kk)
            ((mt_pos c' kk - 2) * ?c + 1)"
      using hge2 unfolding ae_window_invariant_general_def by simp
    have buf_eq:
        "mt_tape cM_k kk (((mt_pos c' kk - 2) * ?c + 1) + (2 * ?c + c_idx i))
            = buf_lin_at (buf5 kk) (2 * ?c + c_idx i)"
      using win_steady addr_lt_3c
      unfolding ae_window_invariant_def by blast
    have addr_simp:
        "((mt_pos c' kk - 2) * ?c + 1) + (2 * ?c + c_idx i)
          = mt_pos c' kk * ?c + c_idx i + 1"
      using hge2 by (simp add: algebra_simps diff_mult_distrib)
    have buf_eq_rewritten:
        "mt_tape cM_k kk (mt_pos c' kk * ?c + c_idx i + 1)
            = buf_lin_at (buf5 kk) (2 * ?c + c_idx i)"
      using buf_eq[unfolded addr_simp] .
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have not_lt_c: "\<not> 2 * ?c + c_idx i < ?c" by simp
    have not_lt_2c: "\<not> 2 * ?c + c_idx i < 2 * ?c" by simp
    have buf_lin_eq:
        "buf_lin_at (buf5 kk) (2 * ?c + c_idx i)
            = rr ((enum_class.enum :: 'c list) ! ((2 * ?c + c_idx i) - 2 * ?c))"
      using buf5_kk not_lt_c not_lt_2c
      unfolding buf_lin_at_def Let_def by simp
    have sub_simp: "(2 * ?c + c_idx i) - 2 * ?c = c_idx i" by simp
    have enum_at_idx:
        "(enum_class.enum :: 'c list) ! c_idx i = i"
      by (rule c_idx_in_range(2))
    show "mt_tape cM_k kk (mt_pos c' kk * ?c + c_idx i + 1)
            = (snd (snd (buf5 kk))) i"
      using buf_eq_rewritten buf_lin_eq sub_simp enum_at_idx buf5_kk by simp
  qed

  \<comment> \<open>Sub-step 6b-assemble: per-tape regime-aware
      \<open>ae_tape_correspondence\<close> between \<open>cM_k\<close> and \<open>c8\<close>.
      Per-tape branches on \<open>mt_pos c' kk\<close>; within each regime,
      per-block branches on \<open>s\<close> match an in-window value
      (buf-lin transfer + c8 in-window value coincide on buf5 slot)
      or an off-window value (\<open>cM_k = cM = c'\<close> M-side via
      \<open>m_tape_off_window\<close> + \<open>tape_corr\<close>; \<open>c8 = c'\<close> M'-side via
      \<open>c8_tape_off_window\<close>).  Extracted to \<open>ae_fwd_tape_corr_c8\<close>.\<close>
  have tape_corr_c8:
      "\<forall>kk<k_tm M. ae_tape_correspondence (le_tm M)
              (mt_tape cM_k kk) (mt_tape c8 kk)"
    by (rule ae_fwd_tape_corr_c8[OF tape_corr c_ge_1 c4_pos c5_pos_for_pos1
          c5_pos_for_pos1_dest_left c7_pos_for_pos1_dest_left cM_k_zero
          m_tape_off_window_le0 m_tape_off_window_le1 m_tape_off_window_steady
          c5_pos_for_pos0 c5_pos_for_pos_ge2 c5_pos_for_pos_ge2_dest_left
          c6_pos_for_pos0 c6_pos_for_pos_ge2 c7_pos_for_pos0 c7_pos_for_pos_ge2
          c6_pos_for_pos1 c7_pos_for_pos1 c8_tape_off_window
          c8_tape_at_one_for_pos0 c8_tape_at_one_for_pos1 c8_tape_at_two_for_pos1
          c8_tape_at_pos_for_pos_ge2 c8_tape_at_pos_minus_1_for_pos_ge2
          c8_tape_at_pos_plus_1_for_pos_ge2 tape_cM_k_at_one_for_pos0
          tape_cM_k_at_one_for_pos1 tape_cM_k_at_two_for_pos1
          tape_cM_k_at_pos_minus_1_for_pos_ge2 tape_cM_k_at_pos_for_pos_ge2
          tape_cM_k_at_pos_plus_1_for_pos_ge2])
  \<comment> \<open>Sub-step 6c: position decode at \<open>c8\<close>.  Per-tape regime
      case-split on \<open>mt_pos c' kk\<close>, then per-dest case-split.
      The \<open>idx = SS1\<close> antecedent excludes the halt branch
      (which lands at \<open>init_stage\<close> = VFwd).  Extracted to
      \<open>ae_fwd_pos_decode_c8\<close>.\<close>
  have pos_decode_c8:
      "(case mt_state c8 of (_, _, _, _, idx) \<Rightarrow> idx = SS1)
        \<longrightarrow> (\<forall>k<k_tm M. mt_pos cM_k k
                  = ae_decode_pos (mt_pos c8 k)
                      (case mt_state c8 of (_, off, _, _, _) \<Rightarrow> off k))"
    by (rule ae_fwd_pos_decode_c8[OF ofs6_eq_ofs5 c8_state cM_k_window_general
          c8_pos_for_pos0 c8_pos_for_pos_ge2 c8_pos_for_pos1])
  \<comment> \<open>Sub-step 6f: final assembly via \<open>rule that\<close>.  The four
      obligations of the \<open>obtains\<close>: chain composition (\<open>chain8\<close>),
      \<open>ae_simulates M cM_k c8\<close> (the four per-conjunct facts
      \<open>conj_i\<close>, \<open>conj_ii\<close>, \<open>tape_corr_c8\<close>,
      \<open>pos_decode_c8\<close>, plus gamma and buf-gamma side-bands),
      \<open>ae_buffer_in_gamma_block M c8\<close>, and \<open>c8\<close> cell 0 is
      \<open>LE_block\<close>.\<close>
  \<comment> \<open>SS5 exposure (det-free reverse arm): the SS5 state in
      \<open>(q_out, ofs, buf, dest)\<close> form (\<open>q_out = mt_state cM_k\<close> via
      \<open>c4_q_out\<close>) and the window correspondence in \<open>(dest, ofs)\<close>
      bp form (from \<open>c4_window_general\<close> under \<open>c4_state\<close>).\<close>
  have q5_eq: "q5 = mt_state cM_k"
    using c4_q_out c4_state by simp
  have c4f_state_exp: "mt_state c4 = (mt_state cM_k, ofs5, buf5, dest5, SS5)"
    using c4_state q5_eq by simp
  have fwd_window_exp:
      "\<forall>kk<k_tm M. ae_window_invariant_general
              (mt_tape cM_k kk) (mt_pos cM_k kk)
              (dest5 kk, ofs5 kk) (buf5 kk) (mt_pos c' kk) (le_tm M)"
    using c4_window_general c4_state by simp

  obtain qq8 ofs8 buf8 dest8 idx8 where
      c8_full: "mt_state c8 = (qq8, ofs8, buf8, dest8, idx8)"
    by (cases "mt_state c8") auto
  have conj_i:
      "(idx8 = SS1 \<and> qq8 \<notin> {t_tm M, r_tm M})
        \<or> (qq8 \<in> {t_tm M, r_tm M}
             \<and> (ofs8, buf8, dest8, idx8) = init_stage (le_tm M))"
    using sim_i_c8 c8_full by simp
  have conj_ii: "mt_state cM_k = qq8"
    using sim_ii_c8 c8_full by simp
  have conj_iv:
      "idx8 = SS1
        \<longrightarrow> (\<forall>k<k_tm M. mt_pos cM_k k = ae_decode_pos (mt_pos c8 k) (ofs8 k))"
    using pos_decode_c8 c8_full by simp
  have sim_c8: "ae_simulates M cM_k c8"
    unfolding ae_simulates_def
    using conj_i conj_ii conj_iv tape_corr_c8 gamma_c8 c8_full
    by simp

  show ?thesis
    by (rule that[OF chain8 sim_c8 buf_gamma_c8 tape_c8_zero_le
                     step1_sub step2_sub step3_sub step4_sub
                     step5_sub step6_sub step7_sub step8_sub
                     c4f_state_exp fwd_window_exp buf_gamma_c4])
qed

end
