theory AlphabetEnlargement_ForwardArms
  imports AlphabetEnlargement_ForwardStep
begin

subsection \<open>One stage of the forward simulation\<close>

text \<open>One stage of the enlarged machine is the eight substeps
  \<open>SS1\<close> to \<open>SS8\<close>, and the proof that it simulates \<open>m\<close> steps of \<open>M\<close>,
  \<open>ae_simulates_forward_stage_general\<close> in the next theory,
  \<open>AlphabetEnlargement_ForwardStage\<close>, is put together from four arms: \<open>ae_fwd_load_compute\<close> (the buffer
  loads and the compute step, to the \<open>SS5\<close> configuration),
  \<open>ae_fwd_m_side_window\<close> (what holds of \<open>M\<close>'s configuration after
  those steps), \<open>ae_fwd_head_positions\<close> (where each head is after
  each write-back substep) and \<open>ae_fwd_cells_c8\<close> (the tape contents
  after the last one).\<close>

text \<open>First arm of \<open>ae_simulates_forward_stage_general\<close>: from the
  \<open>SS1\<close> entry \<open>c'\<close> through the three buffer-load substeps
  (\<open>c1\<close>, \<open>c2\<close>, \<open>c3\<close>) and the compute substep to the \<open>SS5\<close>
  configuration \<open>c4\<close>, with what the write-back substeps read there:
  the per-tape home-cell classification at \<open>c'\<close>, the buffer guard and
  the window invariant at \<open>c4\<close>, and the side-bands.\<close>

lemma ae_fwd_load_compute:
  fixes M :: "('q, 'a) ktm"
    and cM cM_k :: "('a, 'q) ktc_config"
    and c' :: "(nat \<Rightarrow> 'a,
                'q \<times> 'a ae_stage) ktc_config"
    and k :: nat
  assumes vM:        "valid_ktm M"
      and lu:        "le_unique M"
      and sim:       "ae_simulates m M cM c'"
      and qM_in_Q:   "ktc_state cM \<in> Q_ktm M"
      and q_neq_t:   "ktc_state cM \<noteq> t_ktm M"
      and q_neq_r:   "ktc_state cM \<noteq> r_ktm M"
      and buf_gamma: "ae_buffer_in_gamma_block m M c'"
      and k_le:      "k \<le> m"
      and trace:     "(cM, cM_k) \<in> ktm_step (delta_ktm M) ^^ k"
      and end_or_halt:
            "k = m
              \<or> ktc_state cM_k \<in> {t_ktm M, r_ktm M}"
      and le_anchor:
            "\<forall>k<k_ktm M. ktc_tape c' k 0 = LE_block m (le_ktm M)"
      and le_neq_bl:
            "le_ktm M \<noteq> bl_ktm M"
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
  obtains ofs c1 c2 c3 c4
    where "\<forall>k<k_ktm M. ae_tape_correspondence m (le_ktm M)
              (ktc_tape cM k) (ktc_tape c' k)"
      and "\<forall>k<k_ktm M. ktc_pos cM k = ae_decode_pos m (ktc_pos c' k) (ofs k)"
      and "(c', c1) \<in> ktm_step (ae_delta_ss1_ss2 m M)"
      and "(c', c1) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and "(c1, c2) \<in> ktm_step (ae_delta_ss2_ss3 m M)"
      and "(c1, c2) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and "(c2, c3) \<in> ktm_step (ae_delta_ss3_ss4 m M)"
      and "(c2, c3) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and "1 \<le> m"
      and "\<forall>k. ofs k < m"
      and "m = length [0..<m]"
      and "\<forall>k<k_ktm M. (ktc_pos c' k = 0
                \<longrightarrow> ktc_tape c' k (ktc_pos c' k) = LE_block m (le_ktm M))
              \<and> (ktc_pos c' k \<ge> 1
                \<longrightarrow> ktc_tape c' k (ktc_pos c' k) \<noteq> LE_block m (le_ktm M))"
      and "\<forall>k<k_ktm M. ktc_pos c3 k = ktc_pos c' k + 1"
      and "(bl_block m (bl_ktm M) :: nat \<Rightarrow> 'a) \<noteq> LE_block m (le_ktm M)"
      and "(c3, c4) \<in> ktm_step (ae_delta_ss4_ss5 m M)"
      and "(c3, c4) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and "case ktc_state c4 of (q_out, _, _, _, _) \<Rightarrow> q_out = ktc_state cM_k"
      and "case ktc_state c4 of (_, _, b, _, _) \<Rightarrow>
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
      and "case ktc_state c4 of (_, ofs', buf', dest', _) \<Rightarrow>
             \<forall>kk<k_ktm M. ae_window_invariant_general m
               (ktc_tape cM_k kk) (ktc_pos cM_k kk)
               (dest' kk, ofs' kk) (buf' kk) (ktc_pos c' kk) (le_ktm M)"
      and "ae_inv_ss5 M c4"
      and "ae_tape_in_gamma_block m M c4"
      and "ae_buffer_in_gamma_block m M c4"
proof -
  \<comment> \<open>Unpack \<open>ae_simulates\<close> at SS1 entry via the shared
      regime-agnostic helper.  No regime-specific hypothesis enters
      here — the unpack is uniform across steady / le1 / le0.\<close>
  obtain qM' ofs buf dest where
      c'_state: "ktc_state c' = (qM', ofs, buf, dest, SS1)"
    and qM_eq: "ktc_state cM = qM'"
    and qM'_in_Q: "qM' \<in> Q_ktm M"
    and qM'_neq_t: "qM' \<noteq> t_ktm M"
    and qM'_neq_r: "qM' \<noteq> r_ktm M"
    and tape_corr: "\<forall>k<k_ktm M. ae_tape_correspondence m (le_ktm M)
                          (ktc_tape cM k) (ktc_tape c' k)"
    and pos_corr:  "\<forall>k<k_ktm M. ktc_pos cM k = ae_decode_pos m (ktc_pos c' k) (ofs k)"
    and gamma_c':  "ae_tape_in_gamma_block m M c'"
    and inv_ss1:   "ae_inv_ss1 M c'"
    and pos_link_c': "ae_position_link m M c'"
    by (rule ae_forward_stage_unpack_sim[OF sim qM_in_Q q_neq_t q_neq_r])

  \<comment> \<open>Buffer-load substeps SS1\<open>\<rightarrow>\<close>SS2\<open>\<rightarrow>\<close>SS3
      \<open>\<rightarrow>\<close>SS4 via the shared regime-agnostic load-chain
      helper.  Yields the SS4-entry config \<open>c3\<close> together with
      its SS4 invariant, gamma and buffer-gamma side-bands, state
      preservation, and position-link side-band.  Each per-tape
      branch will refine the buffer-content characterisation
      separately in the regime-aware substeps that follow.\<close>
  obtain c1 c2 c3 where
      step1_sub: "(c', c1) \<in> ktm_step (ae_delta_ss1_ss2 m M)"
    and step1:   "(c', c1) \<in> ktm_step (alphabet_enlarge_delta m M)"
    and step2_sub: "(c1, c2) \<in> ktm_step (ae_delta_ss2_ss3 m M)"
    and step2:   "(c1, c2) \<in> ktm_step (alphabet_enlarge_delta m M)"
    and step3_sub: "(c2, c3) \<in> ktm_step (ae_delta_ss3_ss4 m M)"
    and step3:   "(c2, c3) \<in> ktm_step (alphabet_enlarge_delta m M)"
    and inv_ss4: "ae_inv_ss4 M c3"
    and gamma_c3:    "ae_tape_in_gamma_block m M c3"
    and buf_gamma_c3: "ae_buffer_in_gamma_block m M c3"
    and c3_fst_eq:   "fst (ktc_state c3) = qM'"
    and pos_link_c3: "ae_position_link m M c3"
    by (rule ae_forward_stage_load_chain[OF vM c'_state inv_ss1 gamma_c'
                                            buf_gamma pos_link_c'
                                            qM'_neq_t qM'_neq_r])
  have c3_fst_neq_t: "fst (ktc_state c3) \<noteq> t_ktm M"
    using c3_fst_eq qM'_neq_t by simp
  have c3_fst_neq_r: "fst (ktc_state c3) \<noteq> r_ktm M"
    using c3_fst_eq qM'_neq_r by simp

  \<comment> \<open>Per-tape home-cell classification: each tape \<open>k\<close>
      either has \<open>ktc_pos c' k = 0\<close> with home = \<open>LE_block\<close>
      (from \<open>le_anchor\<close>) or
      \<open>ktc_pos c' k \<ge> 1\<close> with home \<open>\<noteq> LE_block\<close>
      (from \<open>ae_tape_correspondence\<close> at the home
      block with witness \<open>x = 0\<close>, projecting
      \<open>no_le_per_tape\<close> to the regime branch).\<close>
  have c_ge_1: "1 \<le> m"
    using ae_buffer_in_gamma_block_width_pos[OF buf_gamma] by simp
  have m_pos: "0 < m" using c_ge_1 by simp
  have ofs_lt: "\<forall>k. ofs k < m"
    by (rule ae_buffer_in_gamma_block_offsets[OF buf_gamma c'_state])
  have c_eq_len: "m = length [0..<m]"
    by simp

  have home_classification:
      "\<forall>k<k_ktm M. (ktc_pos c' k = 0
              \<longrightarrow> ktc_tape c' k (ktc_pos c' k) = LE_block m (le_ktm M))
           \<and> (ktc_pos c' k \<ge> 1
              \<longrightarrow> ktc_tape c' k (ktc_pos c' k) \<noteq> LE_block m (le_ktm M))"
    by (rule ae_home_classification[OF le_anchor no_le_per_tape tape_corr m_pos])

  \<comment> \<open>SS4-entry characterisation via the per-tape unified
      buffer-chars helper.  Buffer at SS4 is per-tape: tapes at
      \<open>pos = 0\<close> get \<open>(bl_block, LE_block, snd (snd (buf k)))\<close>
      (the LE-arm shape from \<open>ae_ss1_to_ss4_buffer_chars_le0\<close>);
      tapes at \<open>pos \<ge> 1\<close> get \<open>(ktc_tape c' k (pos - 1),
      ktc_tape c' k pos, snd (snd (buf k)))\<close> (the steady-arm shape
      from \<open>ae_ss1_to_ss4_buffer_chars\<close>).  Tape and position
      conclusions are uniform across regimes.\<close>
  have c3_state:
      "ktc_state c3 = (qM', ofs,
                       (\<lambda>k. if k < k_ktm M
                              then (if ktc_pos c' k = 0
                                      then (bl_block m (bl_ktm M),
                                            LE_block m (le_ktm M),
                                            snd (snd (buf k)))
                                      else (ktc_tape c' k (ktc_pos c' k - 1),
                                            ktc_tape c' k (ktc_pos c' k),
                                            snd (snd (buf k))))
                              else init_buffer m (le_ktm M) k),
                       dest, SS4)"
    using ae_ss1_to_ss4_buffer_chars_general(1)[OF c'_state step1_sub
                                                   step2_sub step3_sub
                                                   home_classification] .
  have c3_tape: "ktc_tape c3 = ktc_tape c'"
    using ae_ss1_to_ss4_buffer_chars_general(2)[OF c'_state step1_sub
                                                   step2_sub step3_sub
                                                   home_classification] .
  have c3_pos: "\<And>k. k < k_ktm M \<Longrightarrow> ktc_pos c3 k = ktc_pos c' k + 1"
    using ae_ss1_to_ss4_buffer_chars_general(3)[OF c'_state step1_sub
                                                   step2_sub step3_sub
                                                   home_classification] .

  \<comment> \<open>Per-tape SS4 window invariant via the unified
      from-correspondence helper.  The buffer triple is the
      regime-aware shape that \<open>ae_delta_ss4_ss5\<close> reads from
      \<open>c3\<close>: left and home from the SS4-entry per-tape buffer,
      right freshly read at \<open>ktc_pos c' k + 1\<close>.  The conclusion
      is the per-tape \<open>ae_window_invariant_general\<close>, indexed
      by \<open>ktc_pos c' k\<close> (the frozen regime selector).\<close>
  have window_at_ss4:
      "\<forall>k<k_ktm M. ae_window_invariant_general m
              (ktc_tape cM k) (ktc_pos cM k)
              (AE_Home, ofs k)
              (if ktc_pos c' k = 0
                 then (bl_block m (bl_ktm M),
                       LE_block m (le_ktm M),
                       ktc_tape c' k 1)
               else if ktc_pos c' k = 1
                 then (ktc_tape c' k 0,
                       ktc_tape c' k 1,
                       ktc_tape c' k 2)
               else (ktc_tape c' k (ktc_pos c' k - 1),
                     ktc_tape c' k (ktc_pos c' k),
                     ktc_tape c' k (ktc_pos c' k + 1)))
              (ktc_pos c' k)
              (le_ktm M)"
    using ae_ss4_window_from_correspondence_general[OF sim c'_state
                                                       le_anchor
                                                       ae_buffer_in_gamma_block_offsets[OF buf_gamma c'_state]] .

  \<comment> \<open>Re-express \<open>cM\<close> via \<open>KConfig\<close> to
      match the trace lemma's toolkit hypothesis shape (arm-uniform
      with le0 / le1 / steady).  Surfaces \<open>ts_cM = ktc_tape cM\<close>
      and \<open>n_cM = ktc_pos cM\<close> for direct substitution into the
      trace, no-LE and window hypotheses.\<close>
  obtain ts_cM n_cM where cM_eq:
      "cM = KConfig qM' ts_cM n_cM"
    using qM_eq by (cases cM) auto
  have ts_cM_eq: "ts_cM = ktc_tape cM" using cM_eq by simp
  have n_cM_eq: "n_cM = ktc_pos cM" using cM_eq by simp

  \<comment> \<open>Trace toolkit: rewrite the precondition's
      \<open>(cM, cM_k) \<in> ktm_step^^k\<close> shape into the trace
      lemma's
      \<open>(KConfig (fst (ktc_state c3)) ts_cM n_cM, cM_k) \<in> \<dots>\<close>
      form, via \<open>cM_eq\<close> and \<open>c3_fst_eq\<close>.\<close>
  have trace_toolkit:
      "(KConfig (fst (ktc_state c3)) ts_cM n_cM, cM_k)
          \<in> ktm_step (delta_ktm M) ^^ k"
    using trace cM_eq c3_fst_eq by simp

  \<comment> \<open>No-LE toolkit: rephrase \<open>no_le_per_tape\<close> in terms
      of \<open>ts_cM\<close> (= \<open>ktc_tape cM\<close>) for the trace lemma's
      \<open>tsM\<close>-parameter.  Same shape modulo the rewrite of
      \<open>ktc_tape cM\<close> to \<open>ts_cM\<close>.\<close>
  have no_le_toolkit_general:
      "\<forall>kk. (ktc_pos c' kk = 0
              \<longrightarrow> (\<forall>i. i < m
                        \<longrightarrow> ts_cM kk (Suc i) \<noteq> le_ktm M))
           \<and> (ktc_pos c' kk = 1
                \<longrightarrow> (\<forall>i. i < 2 * m
                          \<longrightarrow> ts_cM kk (Suc i) \<noteq> le_ktm M))
           \<and> (ktc_pos c' kk \<ge> 2
                \<longrightarrow> (\<forall>i. i < 3 * m
                          \<longrightarrow> ts_cM kk
                                ((ktc_pos c' kk - 2) * m
                                  + 1 + i)
                              \<noteq> le_ktm M))"
    using no_le_per_tape ts_cM_eq by simp

  \<comment> \<open>Left-slot guard for pos=0 tapes at \<open>c3\<close>: the SS4-entry
      left slot for tapes at block 0 is \<open>bl_block (bl_ktm M)\<close>
      (per \<open>c3_state\<close>'s if-branch), distinct from
      \<open>LE_block (le_ktm M)\<close> via \<open>le_neq_bl\<close>.  Le1 and
      steady tapes carry no obligation here (the trace lemma's
      hypothesis is \<open>pos k = 0 \<longrightarrow> \<dots>\<close>).\<close>
  have bl_neq_le:
      "(bl_block m (bl_ktm M) :: nat \<Rightarrow> 'a) \<noteq> LE_block m (le_ktm M)"
    using LE_block_neq_bl_block[OF m_pos le_neq_bl] by metis
  have left_not_le_c3_toolkit:
      "case ktc_state c3 of (_, _, b, _, _) \<Rightarrow>
           \<forall>kk<k_ktm M. ktc_pos c' kk = 0
                 \<longrightarrow> fst (b kk) \<noteq> LE_block m (le_ktm M)"
    using c3_state bl_neq_le by simp

  \<comment> \<open>Window-invariant toolkit: convert \<open>window_at_ss4\<close>
      from its \<open>c'\<close>-tape if-then-else form into the
      \<open>case ktc_state c3\<close> form expected by the trace lemma.
      Per-tape regime case-split on \<open>ktc_pos c' kk\<close>; in each
      branch, \<open>c3_state\<close>'s if-then-else and the
      \<open>window_at_ss4\<close> nested-if reduce to the same buffer triple.\<close>
  have window_toolkit_general:
      "\<forall>kk<k_ktm M. ae_window_invariant_general m (ts_cM kk) (n_cM kk)
              (case ktc_state c3 of (_, ofs', _, _, _)
                  \<Rightarrow> (AE_Home, ofs' kk))
              (case ktc_state c3 of (_, _, buf', _, _)
                  \<Rightarrow> (fst (buf' kk), fst (snd (buf' kk)),
                      ktc_tape c3 kk (ktc_pos c3 kk)))
              (ktc_pos c' kk) (le_ktm M)"
  proof (intro allI impI)
    fix kk
    assume kklt: "kk < k_ktm M"
    have c3_buf_triple:
        "(case ktc_state c3 of (_, _, buf', _, _) \<Rightarrow>
              (fst (buf' kk), fst (snd (buf' kk)),
               ktc_tape c3 kk (ktc_pos c3 kk)))
          = (if ktc_pos c' kk = 0
                then (bl_block m (bl_ktm M), LE_block m (le_ktm M),
                      ktc_tape c' kk (ktc_pos c' kk + 1))
             else (ktc_tape c' kk (ktc_pos c' kk - 1),
                   ktc_tape c' kk (ktc_pos c' kk),
                   ktc_tape c' kk (ktc_pos c' kk + 1)))"
      using c3_state c3_tape c3_pos kklt by simp
    have c3_ofs_pair:
        "(case ktc_state c3 of (_, ofs', _, _, _) \<Rightarrow> (AE_Home, ofs' kk))
          = (AE_Home, ofs kk)"
      using c3_state by simp
    have win_at_ss4_kk:
        "ae_window_invariant_general m (ktc_tape cM kk) (ktc_pos cM kk)
              (AE_Home, ofs kk)
              (if ktc_pos c' kk = 0
                 then (bl_block m (bl_ktm M), LE_block m (le_ktm M),
                       ktc_tape c' kk 1)
               else if ktc_pos c' kk = 1
                 then (ktc_tape c' kk 0,
                       ktc_tape c' kk 1,
                       ktc_tape c' kk 2)
               else (ktc_tape c' kk (ktc_pos c' kk - 1),
                     ktc_tape c' kk (ktc_pos c' kk),
                     ktc_tape c' kk (ktc_pos c' kk + 1)))
              (ktc_pos c' kk) (le_ktm M)"
      using window_at_ss4 kklt by blast
    consider (le0) "ktc_pos c' kk = 0"
           | (le1) "ktc_pos c' kk = 1"
           | (steady) "ktc_pos c' kk \<ge> 2"
      by linarith
    thus "ae_window_invariant_general m (ts_cM kk) (n_cM kk)
            (case ktc_state c3 of (_, ofs', _, _, _)
                \<Rightarrow> (AE_Home, ofs' kk))
            (case ktc_state c3 of (_, _, buf', _, _)
                \<Rightarrow> (fst (buf' kk), fst (snd (buf' kk)),
                    ktc_tape c3 kk (ktc_pos c3 kk)))
            (ktc_pos c' kk) (le_ktm M)"
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
      have pos_ne_0: "ktc_pos c' kk \<noteq> 0" using steady by simp
      have pos_ne_1: "ktc_pos c' kk \<noteq> 1" using steady by simp
      show ?thesis
        using win_at_ss4_kk c3_buf_triple c3_ofs_pair pos_ne_0 pos_ne_1
              ts_cM_eq n_cM_eq
        by simp
    qed
  qed

  \<comment> \<open>Invoke the trace-driven SS4\<open>\<rightarrow>\<close>SS5 helper
      for the per-tape unified case.  The trace lemma's
      \<open>pos\<close> parameter is inferred from
      \<open>window_toolkit_general\<close>'s \<open>ktc_pos c' kk\<close>
      regime selector, giving \<open>pos := ktc_pos c'\<close>.\<close>
  obtain c4 where
      step4_sub: "(c3, c4) \<in> ktm_step (ae_delta_ss4_ss5 m M)"
    and step4: "(c3, c4) \<in> ktm_step (alphabet_enlarge_delta m M)"
    and c4_q_out: "case ktc_state c4 of (q_out, _, _, _, _)
                     \<Rightarrow> q_out = ktc_state cM_k"
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
    and c4_window_general:
            "case ktc_state c4 of (_, ofs', buf', dest', _) \<Rightarrow>
                 \<forall>kk<k_ktm M. ae_window_invariant_general m
                       (ktc_tape cM_k kk) (ktc_pos cM_k kk)
                       (dest' kk, ofs' kk) (buf' kk)
                       (ktc_pos c' kk) (le_ktm M)"
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
  have gamma_c4: "ae_tape_in_gamma_block m M c4"
    using ae_step_alphabet_enlarge_gamma_preserve[OF gamma_c3 step4] .
  have buf_gamma_c4: "ae_buffer_in_gamma_block m M c4"
    using ae_step_alphabet_enlarge_buffer_gamma_preserve[OF step4] .
  have c3_pos_all: "\<forall>k<k_ktm M. ktc_pos c3 k = ktc_pos c' k + 1"
    using c3_pos by blast
  show thesis
    by (rule that[OF tape_corr pos_corr step1_sub step1 step2_sub step2
                     step3_sub step3 c_ge_1 ofs_lt c_eq_len home_classification
                     c3_pos_all bl_neq_le step4_sub step4 c4_q_out
                     c4_buf_not_le_per_tape c4_window_general inv_ss5 gamma_c4
                     buf_gamma_c4])
qed

text \<open>Second arm of \<open>ae_simulates_forward_stage_general\<close>: the
  \<open>M\<close>-side facts the write-back substeps are checked against.  At
  \<open>cM_k\<close> (\<open>k \<le> m\<close> simulated steps on) each tape has the window
  invariant of its regime, cell 0 still holds the left endmarker, and
  outside the regime's window the tape is that of \<open>cM\<close>.\<close>

lemma ae_fwd_m_side_window:
  fixes M :: "('q, 'a) ktm"
    and cM cM_k :: "('a, 'q) ktc_config"
    and c' c4 :: "(nat \<Rightarrow> 'a,
                   'q \<times> 'a ae_stage) ktc_config"
    and k :: nat
  assumes tape_corr: "\<forall>k<k_ktm M. ae_tape_correspondence m (le_ktm M)
                         (ktc_tape cM k) (ktc_tape c' k)"
      and pos_corr: "\<forall>k<k_ktm M. ktc_pos cM k = ae_decode_pos m (ktc_pos c' k) (ofs k)"
      and ofs_lt: "\<forall>k. ofs k < m"
      and c4_window_general:
            "case ktc_state c4 of (_, ofs', buf', dest', _) \<Rightarrow>
               \<forall>kk<k_ktm M. ae_window_invariant_general m
                 (ktc_tape cM_k kk) (ktc_pos cM_k kk)
                 (dest' kk, ofs' kk) (buf' kk) (ktc_pos c' kk) (le_ktm M)"
      and k_le: "k \<le> m"
      and trace: "(cM, cM_k) \<in> ktm_step (delta_ktm M) ^^ k"
      and c4_state: "ktc_state c4 = (q5, ofs5, buf5, dest5, SS5)"
  shows "\<forall>kk<k_ktm M. ae_window_invariant_general m
            (ktc_tape cM_k kk) (ktc_pos cM_k kk)
            (dest5 kk, ofs5 kk) (buf5 kk) (ktc_pos c' kk) (le_ktm M)"
          (is ?window)
    and "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_tape cM_k kk 0 = le_ktm M"
          (is "PROP ?zero")
    and "\<And>kk p. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 0 \<Longrightarrow> p > m
            \<Longrightarrow> ktc_tape cM_k kk p = ktc_tape cM kk p"
          (is "PROP ?off_le0")
    and "\<And>kk p. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1 \<Longrightarrow> p > 2 * m
            \<Longrightarrow> ktc_tape cM_k kk p = ktc_tape cM kk p"
          (is "PROP ?off_le1")
    and "\<And>kk p. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2
            \<Longrightarrow> p < (ktc_pos c' kk - 2) * m + 1
                \<or> p \<ge> (ktc_pos c' kk - 2) * m + 1 + 3 * m
            \<Longrightarrow> ktc_tape cM_k kk p = ktc_tape cM kk p"
          (is "PROP ?off_steady")
proof -
  \<comment> \<open>Sub-step 6b1: per-tape regime-aware \<open>cM_k\<close>-side window
      invariant.  Projection of \<open>c4_window_general\<close> through
      \<open>c4_state\<close> = \<open>(q5, ofs5, buf5, dest5, SS5)\<close>: each tape
      \<open>kk\<close> has the hybrid \<open>ae_window_invariant_general\<close>
      indexed by its regime selector \<open>ktc_pos c' kk\<close>.  This
      single fact unpacks into le0/le1/steady sub-invariants
      per tape via the definition's case-split on \<open>pos = 0\<close>,
      \<open>pos = 1\<close>, \<open>pos \<ge> 2\<close>.\<close>
  have cM_k_window_general:
      "\<forall>kk<k_ktm M. ae_window_invariant_general m
              (ktc_tape cM_k kk) (ktc_pos cM_k kk)
              (dest5 kk, ofs5 kk) (buf5 kk)
              (ktc_pos c' kk) (le_ktm M)"
    using c4_window_general c4_state by simp

  \<comment> \<open>Sub-step 6b1: \<open>cM_k\<close>'s tape at position 0 is
      \<open>LE_block (le_ktm M)\<close>, equivalently \<open>le_ktm M\<close> as a
      bare tape value — the s=0 conjunct of \<open>ae_tape_correspondence\<close>.
      Per-tape regime case-split: pos=0 and pos=1 extract the
      \<open>tM 0 = le\<close> clause directly from the regime-specific
      window invariant (\<open>ae_window_invariant_le0_def\<close> and
      \<open>_le1_def\<close>); pos\<open>\<ge>\<close>2 has no such clause in its
      window invariant (which only constrains
      \<open>[p_start, p_start + 3c)\<close>) so the M-side entry
      correspondence at s=0 (\<open>ktc_tape cM kk 0 = le\<close>) chains
      with \<open>ktm_relpow_tape_off_window\<close>'s zero preservation
      (\<open>ktc_pos cM kk \<ge> c + 1 > k\<close> for pos\<open>\<ge>\<close>2 tapes).\<close>
  let ?c = "m"
  have cM_k_zero: "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_tape cM_k kk 0 = le_ktm M"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    show "ktc_tape cM_k kk 0 = le_ktm M"
    proof (cases "ktc_pos c' kk = 0")
      case True
      have win_kk:
          "ae_window_invariant_le0 m
                (ktc_tape cM_k kk) (ktc_pos cM_k kk)
                (dest5 kk, ofs5 kk) (buf5 kk) (le_ktm M)"
        using cM_k_window_general[rule_format, OF kklt] True
        unfolding ae_window_invariant_general_def by blast
      thus ?thesis unfolding ae_window_invariant_le0_def by simp
    next
      case ne0: False
      show ?thesis
      proof (cases "ktc_pos c' kk = 1")
        case True
        have win_kk:
            "ae_window_invariant_le1 m
                  (ktc_tape cM_k kk) (ktc_pos cM_k kk)
                  (dest5 kk, ofs5 kk) (buf5 kk) (le_ktm M)"
          using cM_k_window_general[rule_format, OF kklt] True
          unfolding ae_window_invariant_general_def by blast
        thus ?thesis unfolding ae_window_invariant_le1_def by simp
      next
        case ne1: False
        have hge2: "ktc_pos c' kk \<ge> 2" using ne0 ne1 by linarith
        have decode:
            "ktc_pos cM kk = (ktc_pos c' kk - 1) * ?c + ofs kk + 1"
          using pos_corr kklt hge2 by (simp add: ae_decode_pos_def)
        have step_mult: "(ktc_pos c' kk - 1) * ?c \<ge> ?c"
        proof -
          have "(ktc_pos c' kk - 1) \<ge> 1" using hge2 by linarith
          hence "(ktc_pos c' kk - 1) * ?c \<ge> 1 * ?c"
            by (rule mult_le_mono1)
          thus ?thesis by simp
        qed
        have pos_ge_c1: "ktc_pos cM kk \<ge> ?c + 1"
          using decode step_mult by linarith
        have k_lt: "k < ktc_pos cM kk" using k_le pos_ge_c1 by linarith
        have far_disj:
            "(0 :: nat) > ktc_pos cM kk + k \<or> (0 :: nat) + k < ktc_pos cM kk"
          using k_lt by simp
        have entry_zero: "ktc_tape cM kk 0 = le_ktm M"
          using tape_corr[rule_format, OF kklt] unfolding ae_tape_correspondence_def by simp
        have "ktc_tape cM_k kk 0 = ktc_tape cM kk 0"
          using ktm_relpow_tape_off_window[OF trace far_disj] .
        thus ?thesis using entry_zero by simp
      qed
    qed
  qed

  \<comment> \<open>Sub-step 6b2: M-side off-window preservation per tape regime.
      Each regime gives a different M-side window characterisation;
      \<open>ktm_relpow_tape_off_window\<close> applied with the entry
      M-head position (\<open>pos_corr\<close> + \<open>ae_decode_pos\<close>) and
      displacement bound \<open>\<le> k \<le> c\<close> closes each branch.\<close>
  have m_tape_off_window_le0:
      "\<And>kk p. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 0
              \<Longrightarrow> p > ?c
              \<Longrightarrow> ktc_tape cM_k kk p = ktc_tape cM kk p"
  proof -
    fix kk and p :: nat
    assume kklt: "kk < k_ktm M"
    assume pos_eq: "ktc_pos c' kk = 0"
    assume p_gt: "p > ?c"
    have m_pos_zero: "ktc_pos cM kk = 0"
      using pos_corr kklt pos_eq by (simp add: ae_decode_pos_def)
    have far: "p > ktc_pos cM kk + k" using p_gt m_pos_zero k_le by linarith
    have far_disj: "p > ktc_pos cM kk + k \<or> p + k < ktc_pos cM kk"
      using far by simp
    show "ktc_tape cM_k kk p = ktc_tape cM kk p"
      using ktm_relpow_tape_off_window[OF trace far_disj] .
  qed
  have m_tape_off_window_le1:
      "\<And>kk p. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1
              \<Longrightarrow> p > 2 * ?c
              \<Longrightarrow> ktc_tape cM_k kk p = ktc_tape cM kk p"
  proof -
    fix kk and p :: nat
    assume kklt: "kk < k_ktm M"
    assume pos_eq: "ktc_pos c' kk = 1"
    assume p_gt: "p > 2 * ?c"
    have m_pos_le_c: "ktc_pos cM kk \<le> ?c"
    proof -
      have decode: "ktc_pos cM kk = Suc (ofs kk)"
        using pos_corr kklt pos_eq by (simp add: ae_decode_pos_def)
      have idx_lt: "ofs kk < ?c" using ofs_lt by simp
      show ?thesis using decode idx_lt by linarith
    qed
    have far: "p > ktc_pos cM kk + k"
      using p_gt m_pos_le_c k_le by linarith
    have far_disj: "p > ktc_pos cM kk + k \<or> p + k < ktc_pos cM kk"
      using far by simp
    show "ktc_tape cM_k kk p = ktc_tape cM kk p"
      using ktm_relpow_tape_off_window[OF trace far_disj] .
  qed
  have m_tape_off_window_steady:
      "\<And>kk p. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2
              \<Longrightarrow> p < (ktc_pos c' kk - 2) * ?c + 1
                  \<or> p \<ge> (ktc_pos c' kk - 2) * ?c + 1 + 3 * ?c
              \<Longrightarrow> ktc_tape cM_k kk p = ktc_tape cM kk p"
  proof -
    fix kk and p :: nat
    assume kklt: "kk < k_ktm M"
    assume hge2: "ktc_pos c' kk \<ge> 2"
    assume p_off: "p < (ktc_pos c' kk - 2) * ?c + 1
                    \<or> p \<ge> (ktc_pos c' kk - 2) * ?c + 1 + 3 * ?c"
    have decode:
        "ktc_pos cM kk = (ktc_pos c' kk - 1) * ?c + ofs kk + 1"
      using pos_corr kklt hge2 by (simp add: ae_decode_pos_def)
    have ws_alt:
        "(ktc_pos c' kk - 1) * ?c = (ktc_pos c' kk - 2) * ?c + ?c"
    proof -
      have suc_eq: "Suc (ktc_pos c' kk - 2) = ktc_pos c' kk - 1"
        using hge2 by simp
      have "Suc (ktc_pos c' kk - 2) * ?c = (ktc_pos c' kk - 2) * ?c + ?c"
        by simp
      with suc_eq show ?thesis by simp
    qed
    have m_pos_eq:
        "ktc_pos cM kk = (ktc_pos c' kk - 2) * ?c + 1 + ?c + ofs kk"
      using decode ws_alt by simp
    have idx_lt: "ofs kk < ?c" using ofs_lt by simp
    have far_disj: "p > ktc_pos cM kk + k \<or> p + k < ktc_pos cM kk"
      using p_off k_le m_pos_eq idx_lt by linarith
    show "ktc_tape cM_k kk p = ktc_tape cM kk p"
      using ktm_relpow_tape_off_window[OF trace far_disj] .
  qed
  show ?window by (fact cM_k_window_general)
  show "PROP ?zero" by (fact cM_k_zero)
  show "PROP ?off_le0" by (fact m_tape_off_window_le0)
  show "PROP ?off_le1" by (fact m_tape_off_window_le1)
  show "PROP ?off_steady" by (fact m_tape_off_window_steady)
qed

text \<open>Third arm of \<open>ae_simulates_forward_stage_general\<close>: where each
  head stands after each write-back substep \<open>SS5\<close> to \<open>SS8\<close>, by the
  tape's regime (block position 0, 1, or at least 2) and its direction
  \<open>dest5\<close>, with the few cell facts the trajectory depends on.\<close>

lemma ae_fwd_head_positions:
  fixes M :: "('q, 'a) ktm"
    and cM cM_k :: "('a, 'q) ktc_config"
    and c' c4 c5 c6 c7 c8 :: "(nat \<Rightarrow> 'a,
                                 'q \<times> 'a ae_stage) ktc_config"
  assumes le_anchor:
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
      and c_ge_1: "1 \<le> m"
      and c_eq_len: "m = length [0..<m]"
      and home_classification:
            "\<forall>k<k_ktm M. (ktc_pos c' k = 0
                \<longrightarrow> ktc_tape c' k (ktc_pos c' k) = LE_block m (le_ktm M))
              \<and> (ktc_pos c' k \<ge> 1
                \<longrightarrow> ktc_tape c' k (ktc_pos c' k) \<noteq> LE_block m (le_ktm M))"
      and bl_neq_le:
            "(bl_block m (bl_ktm M) :: nat \<Rightarrow> 'a) \<noteq> LE_block m (le_ktm M)"
      and gamma_c4: "ae_tape_in_gamma_block m M c4"
      and step5_sub: "(c4, c5) \<in> ktm_step (ae_delta_ss5_ss6 m M)"
      and step5: "(c4, c5) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and c4_state: "ktc_state c4 = (q5, ofs5, buf5, dest5, SS5)"
      and c5_state: "ktc_state c5 = (q5, ofs5, buf5, dest5, SS6)"
      and tape_c4_eq_c': "ktc_tape c4 = ktc_tape c'"
      and buf5_not_le_per_tape:
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
      and right_not_le_c':
          "\<forall>k. ktc_tape c' k (ktc_pos c' k + 1) \<noteq> LE_block m (le_ktm M)"
      and c4_pos_all: "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c4 kk = ktc_pos c' kk"
      and tape_c5_zero_le: "\<forall>k<k_ktm M. ktc_tape c5 k 0 = LE_block m (le_ktm M)"
      and c5_pos_for_pos1_all:
          "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk \<noteq> AE_Left
          \<longrightarrow> ktc_pos c5 kk = 0"
      and step6_sub: "(c5, c6) \<in> ktm_step (ae_delta_ss6_ss7 m M)"
      and step6: "(c5, c6) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and step7_sub: "(c6, c7) \<in> ktm_step (ae_delta_ss7_ss8 m M)"
      and step7: "(c6, c7) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and c6_state: "ktc_state c6 = (q6, ofs6, buf6, dest6, SS7)"
      and c7_state: "ktc_state c7 = (q6, ofs6, buf6, dest6, SS8)"
      and buf6_eq_buf5: "buf6 = buf5"
      and dest6_eq_dest5: "dest6 = dest5"
      and tape_c5_at_one_pos1_all:
          "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1
          \<longrightarrow> ktc_tape c5 kk 1 = fst (snd (buf5 kk))"
      and c6_pos_for_pos1_dest_left_all:
          "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
          \<longrightarrow> ktc_pos c6 kk = 1"
      and c7_pos_for_pos1_dest_left_all:
          "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
          \<longrightarrow> ktc_pos c7 kk = 0"
      and tape_c7_zero_le_pos1_dest_left_all:
          "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
          \<longrightarrow> ktc_tape c7 kk 0 = LE_block m (le_ktm M)"
      and step8_sub: "(c7, c8) \<in> ktm_step (ae_delta_ss8_ss1 m M)"
      and cM_k_window_general:
          "\<forall>kk<k_ktm M. ae_window_invariant_general m
             (ktc_tape cM_k kk) (ktc_pos cM_k kk)
             (dest5 kk, ofs5 kk) (buf5 kk) (ktc_pos c' kk) (le_ktm M)"
  shows "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 0 \<Longrightarrow> ktc_pos c5 kk = 0"
          (is "PROP ?o1")
    and "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2
             \<Longrightarrow> ktc_pos c5 kk = go_move (if dest5 kk = AE_Left then MoveR else MoveL)
                                          (ktc_pos c' kk)"
          (is "PROP ?o2")
    and "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2 \<Longrightarrow> dest5 kk \<noteq> AE_Left
             \<Longrightarrow> ktc_pos c5 kk = ktc_pos c' kk - 1"
          (is "PROP ?o3")
    and "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2 \<Longrightarrow> dest5 kk = AE_Left
             \<Longrightarrow> ktc_pos c5 kk = ktc_pos c' kk + 1"
          (is "PROP ?o4")
    and "\<forall>k. ktc_pos c' k \<ge> 2
             \<longrightarrow> ktc_tape c' k (ktc_pos c' k - 1) \<noteq> LE_block m (le_ktm M)"
          (is "PROP ?o5")
    and "\<forall>k<k_ktm M. ktc_pos c' k = 0 \<longrightarrow> fst (snd (buf5 k)) = LE_block m (le_ktm M)"
          (is "PROP ?o6")
    and "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 0 \<Longrightarrow> ktc_pos c6 kk = 1"
          (is "PROP ?o7")
    and "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2 \<Longrightarrow> ktc_pos c6 kk = ktc_pos c' kk"
          (is "PROP ?o8")
    and "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 0
             \<Longrightarrow> ktc_pos c7 kk = (if dest5 kk = AE_Right then 1 else 0)"
          (is "PROP ?o9")
    and "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2
             \<Longrightarrow> ktc_tape c5 kk (ktc_pos c' kk) = fst (snd (buf5 kk))"
          (is "PROP ?o10")
    and "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2
             \<Longrightarrow> ktc_pos c7 kk = (if dest5 kk = AE_Left
                                   then ktc_pos c' kk - 1
                                   else ktc_pos c' kk + 1)"
          (is "PROP ?o11")
    and "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1 \<Longrightarrow> ktc_pos c6 kk = 1"
          (is "PROP ?o12")
    and "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1
             \<Longrightarrow> ktc_pos c7 kk = (if dest5 kk = AE_Left then 0 else 2)"
          (is "PROP ?o13")
    and "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 0
             \<Longrightarrow> ktc_pos c8 kk = (if dest5 kk = AE_Right then 1 else 0)"
          (is "PROP ?o14")
    and "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2
             \<Longrightarrow> ktc_pos c8 kk = (case dest5 kk of
                                   AE_Left  \<Rightarrow> ktc_pos c' kk - 1
                                 | AE_Home  \<Rightarrow> ktc_pos c' kk
                                 | AE_Right \<Rightarrow> ktc_pos c' kk + 1)"
          (is "PROP ?o15")
    and "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1
             \<Longrightarrow> ktc_pos c8 kk = (case dest5 kk of
                                   AE_Left  \<Rightarrow> 0
                                 | AE_Home  \<Rightarrow> 1
                                 | AE_Right \<Rightarrow> 2)"
          (is "PROP ?o16")
proof -
  note c4_pos = c4_pos_all[rule_format]
  note c5_pos_for_pos1 = c5_pos_for_pos1_all[rule_format]
  note tape_c5_at_one_pos1 = tape_c5_at_one_pos1_all[rule_format]
  note c6_pos_for_pos1_dest_left = c6_pos_for_pos1_dest_left_all[rule_format]
  note c7_pos_for_pos1_dest_left = c7_pos_for_pos1_dest_left_all[rule_format]
  note tape_c7_zero_le_pos1_dest_left = tape_c7_zero_le_pos1_dest_left_all[rule_format]
  \<comment> \<open>Sub-step 6b3: head trajectory \<open>c5_pos\<close> for pos=0 tapes.
      For pos=0, \<open>c4_pos kk = 0\<close> by \<open>c4_pos\<close>, so SS5 reads
      \<open>ktc_tape c4 kk 0 = ktc_tape c' kk 0 = LE_block\<close> by
      \<open>le_anchor\<close>.  \<open>ae_ss5_action\<close>'s first branch
      (\<open>a = LE_block\<close>) fires: write \<open>a\<close> (no-op), direction N.
      Head stays at 0.\<close>
  have c5_pos_for_pos0:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 0 \<Longrightarrow> ktc_pos c5 kk = 0"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume pos_kk: "ktc_pos c' kk = 0"
    have c4_kk: "ktc_pos c4 kk = 0" using c4_pos kklt pos_kk by simp
    have "ktc_tape c4 kk (ktc_pos c4 kk) = LE_block m (le_ktm M)"
      using c4_kk tape_c4_eq_c' le_anchor[rule_format, OF kklt] by simp
    then show "ktc_pos c5 kk = 0"
      using ae_ss5_step_tape(1)[OF step5_sub c4_state kklt] c4_kk by simp
  qed

  \<comment> \<open>Sub-step 6b3: head trajectory \<open>c5_pos\<close> for pos\<open>\<ge>\<close>2 tapes.
      SS5 reads a non-LE block and its buffer's home block is not LE, so
      its last branch fires: direction L when \<open>dest5 kk \<noteq> AE_Left\<close>,
      landing at \<open>ktc_pos c' kk - 1\<close>, and R otherwise, landing at
      \<open>ktc_pos c' kk + 1\<close>.  Mirrors the pos=1 derivations
      \<open>c5_pos_for_pos1\<close> and \<open>_dest_left\<close>, but with
      \<open>ktc_pos c' kk \<ge> 2\<close> so the head does not reach the
      \<open>LE_block\<close> sentinel.\<close>
  have c5_move_for_pos_ge2:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2
            \<Longrightarrow> ktc_pos c5 kk = go_move (if dest5 kk = AE_Left then MoveR else MoveL)
                                         (ktc_pos c' kk)"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume hge2: "ktc_pos c' kk \<ge> 2"
    have c4_kk: "ktc_pos c4 kk = ktc_pos c' kk" using c4_pos kklt by simp
    have "ktc_tape c4 kk (ktc_pos c4 kk) \<noteq> LE_block m (le_ktm M)"
      using c4_kk tape_c4_eq_c' home_classification[rule_format, OF kklt] hge2
      by auto
    moreover have "fst (snd (buf5 kk)) \<noteq> LE_block m (le_ktm M)"
      using buf5_not_le_per_tape[rule_format, OF kklt] hge2 by blast
    ultimately show "ktc_pos c5 kk = go_move (if dest5 kk = AE_Left then MoveR else MoveL)
                                             (ktc_pos c' kk)"
      using ae_ss5_step_tape(1)[OF step5_sub c4_state kklt] c4_kk
      by (simp add: ae_ss5_action_buf)
  qed

  have c5_pos_for_pos_ge2:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2 \<Longrightarrow> dest5 kk \<noteq> AE_Left
            \<Longrightarrow> ktc_pos c5 kk = ktc_pos c' kk - 1"
    using c5_move_for_pos_ge2 by simp

  have c5_pos_for_pos_ge2_dest_left:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2 \<Longrightarrow> dest5 kk = AE_Left
            \<Longrightarrow> ktc_pos c5 kk = ktc_pos c' kk + 1"
    using c5_move_for_pos_ge2 by simp

  \<comment> \<open>Sub-step 6b3 helper: \<open>left_not_le_c'_steady\<close>.  Mirror of
      \<open>right_not_le_c'\<close> for the left side at pos\<open>\<ge>\<close>2: block
      \<open>ktc_pos c' k - 1\<close> mapped via the tape correspondence at
      sub-index 0 (which gives cell address \<open>(ktc_pos c' k - 2) \<cdot> c + 1\<close>),
      then no-LE via \<open>no_le_per_tape\<close>'s steady branch at \<open>i = 0\<close>.
      Powers the SS5\<open>\<rightarrow>\<close>SS6 head-trajectory for pos\<open>\<ge>\<close>2
      tapes with \<open>dest \<noteq> AE_Left\<close>: c5 reads the cell at
      \<open>c5_pos = pos - 1\<close>, which is c'-side block pos-1.\<close>
  have left_not_le_c'_steady:
      "\<forall>k. ktc_pos c' k \<ge> 2
            \<longrightarrow> ktc_tape c' k (ktc_pos c' k - 1) \<noteq> LE_block m (le_ktm M)"
  proof (intro allI impI)
    fix k :: nat
    assume hge2: "ktc_pos c' k \<ge> 2"
    show "ktc_tape c' k (ktc_pos c' k - 1) \<noteq> LE_block m (le_ktm M)"
    proof (cases "k < k_ktm M")
      case True
    let ?x = "[0..<m] ! 0"
    let ?c = "m"
    have zero_lt_len: "0 < length [0..<m]"
      using c_ge_1 c_eq_len by linarith
    have x_idx0: "?x = 0"
      using zero_lt_len by simp
    have tc_k: "ae_tape_correspondence m (le_ktm M) (ktc_tape cM k) (ktc_tape c' k)"
      using tape_corr[rule_format, OF True] by simp
    have s_ge1: "ktc_pos c' k - 1 \<ge> 1" using hge2 by linarith
    have addr_via_tc:
        "ktc_tape cM k ((ktc_pos c' k - 2) * ?c + 1)
          = ktc_tape c' k (ktc_pos c' k - 1) ?x"
    proof -
      from tc_k have unf:
          "\<forall>s\<ge>1. \<forall>i<m. ktc_tape cM k ((s - 1) * ?c + i + 1)
                      = ktc_tape c' k s i"
        unfolding ae_tape_correspondence_def by simp
      have x_lt: "?x < m" using c_ge_1 by simp
      from unf s_ge1 x_lt have eq:
          "ktc_tape cM k ((ktc_pos c' k - 1 - 1) * ?c + ?x + 1)
            = ktc_tape c' k (ktc_pos c' k - 1) ?x"
        by blast
      have idx_arith:
          "ktc_pos c' k - 1 - 1 = ktc_pos c' k - 2"
        using hge2 by simp
      thus ?thesis using eq x_idx0 idx_arith by simp
    qed
    have idx_lt: "(0 :: nat) < 3 * ?c" using c_ge_1 by simp
    have nle: "ktc_tape cM k ((ktc_pos c' k - 2) * ?c + 1 + 0) \<noteq> le_ktm M"
      using no_le_per_tape hge2 idx_lt by blast
    hence nle': "ktc_tape cM k ((ktc_pos c' k - 2) * ?c + 1) \<noteq> le_ktm M"
      by simp
    have "ktc_tape c' k (ktc_pos c' k - 1) ?x \<noteq> le_ktm M"
      using nle' addr_via_tc by simp
    thus "ktc_tape c' k (ktc_pos c' k - 1) \<noteq> LE_block m (le_ktm M)"
      using c_ge_1 unfolding LE_block_def by auto
    next
      case False
      hence kge: "k_ktm M \<le> k" by simp
      have "ktc_tape c' k (ktc_pos c' k - 1) = bl_block m (bl_ktm M)"
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
      "\<forall>k<k_ktm M. ktc_pos c' k = 0 \<longrightarrow> fst (snd (buf5 k)) = LE_block m (le_ktm M)"
  proof (intro allI impI)
    fix k :: nat
    assume klt: "k < k_ktm M"
    assume pos_k: "ktc_pos c' k = 0"
    have wi: "ae_window_invariant_general m
                (ktc_tape cM_k k) (ktc_pos cM_k k)
                (dest5 k, ofs5 k) (buf5 k)
                (ktc_pos c' k) (le_ktm M)"
      using cM_k_window_general[rule_format, OF klt] by simp
    hence "ae_window_invariant_le0 m
              (ktc_tape cM_k k) (ktc_pos cM_k k)
              (dest5 k, ofs5 k) (buf5 k) (le_ktm M)"
      using pos_k unfolding ae_window_invariant_general_def by simp
    thus "fst (snd (buf5 k)) = LE_block m (le_ktm M)"
      unfolding ae_window_invariant_le0_def by simp
  qed


  \<comment> \<open>Sub-step 6b3: head trajectory \<open>c6_pos\<close> for pos=0 tapes.
      \<open>c5_pos = 0\<close> (\<open>c5_pos_for_pos0\<close>); SS6 reads
      \<open>ktc_tape c5 kk 0 = LE_block\<close> via \<open>tape_c5_zero_le\<close>.
      \<open>ae_ss6_action\<close>'s first branch fires (\<open>a = LE_block\<close>),
      writing a (no-op), direction R.  Head lands at
      \<open>c5_pos + 1 = 1\<close>.\<close>
  have c6_pos_for_pos0:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 0 \<Longrightarrow> ktc_pos c6 kk = 1"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume pos_kk: "ktc_pos c' kk = 0"
    have c5_kk: "ktc_pos c5 kk = 0" using c5_pos_for_pos0[OF kklt pos_kk] .
    then show "ktc_pos c6 kk = 1"
      using ae_ss6_step_tape(1)[OF step6_sub c5_state kklt]
            tape_c5_zero_le[rule_format, OF kklt]
      by simp
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
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2 \<Longrightarrow> ktc_pos c6 kk = ktc_pos c' kk"
    by (rule ae_fwd_c6_pos_for_pos_ge2[OF step5 c5_state tape_c4_eq_c'
          buf5_not_le_per_tape right_not_le_c' c4_pos step6_sub
          c5_pos_for_pos_ge2 c5_pos_for_pos_ge2_dest_left left_not_le_c'_steady])
  \<comment> \<open>Sub-step 6b4: head trajectory \<open>c7_pos\<close> for pos=0 tapes.
      \<open>c6_pos = 1\<close> (\<open>c6_pos_for_pos0\<close>); SS7 reads
      \<open>ktc_tape c6 kk 1\<close> which off-traces through SS6 (\<open>c5_pos = 0\<close>),
      SS5 (\<open>c4_pos = 0\<close>) to \<open>ktc_tape c' kk 1\<close>, non-LE via
      \<open>right_not_le_c'\<close>.  Buffer's head slot \<open>h = LE_block\<close>
      (\<open>buf5_h_le_for_pos0\<close>), so \<open>ae_ss7_action\<close>'s second branch
      fires: writes \<open>r\<close>, direction \<open>N\<close> if \<open>dest = AE_Right\<close>
      else \<open>L\<close>.  Head lands at \<open>1\<close> (\<open>dest = AE_Right\<close>) or \<open>0\<close>
      (otherwise).\<close>
  have c7_pos_for_pos0:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 0
            \<Longrightarrow> ktc_pos c7 kk = (if dest5 kk = AE_Right then 1 else 0)"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume pos_kk: "ktc_pos c' kk = 0"
    have c6_kk: "ktc_pos c6 kk = 1" using c6_pos_for_pos0[OF kklt pos_kk] .
    have one_ne_c5_pos: "(1 :: nat) \<noteq> ktc_pos c5 kk"
      using c5_pos_for_pos0[OF kklt pos_kk] by simp
    have one_ne_c4_pos: "(1 :: nat) \<noteq> ktc_pos c4 kk"
      using c4_pos kklt pos_kk by simp
    have c6_at_1: "ktc_tape c6 kk 1 = ktc_tape c' kk 1"
    proof -
      have "ktc_tape c6 kk 1 = ktc_tape c5 kk 1"
        using ktm_step_tape_off_head[OF step6 one_ne_c5_pos] .
      also have "\<dots> = ktc_tape c4 kk 1"
        using ktm_step_tape_off_head[OF step5 one_ne_c4_pos] .
      also have "\<dots> = ktc_tape c' kk 1"
        using tape_c4_eq_c' by simp
      finally show ?thesis .
    qed
    have "ktc_tape c6 kk (ktc_pos c6 kk) \<noteq> LE_block m (le_ktm M)"
      using c6_kk c6_at_1 right_not_le_c'[rule_format, of kk] pos_kk by simp
    moreover have "fst (snd (buf6 kk)) = LE_block m (le_ktm M)"
      using buf5_h_le_for_pos0[rule_format, OF kklt pos_kk] buf6_eq_buf5 by simp
    ultimately show "ktc_pos c7 kk = (if dest5 kk = AE_Right then 1 else 0)"
      using ae_ss7_step_tape(1)[OF step7_sub c6_state kklt] c6_kk dest6_eq_dest5
      by (cases "dest5 kk = AE_Right") (simp_all add: ae_ss7_action_buf)
  qed

  \<comment> \<open>Sub-step 6b4 helper: SS5's write at \<open>c4_pos = pos\<close> for
      pos\<open>\<ge>\<close>2 tapes records the home buffer slot \<open>fst (snd
      (buf5 k))\<close>.  Action \<open>ae_ss5_action\<close>'s else branch fires
      (read non-LE via \<open>home_classification\<close>, head buf slot non-LE
      via \<open>buf5_not_le_per_tape\<close> pos\<open>\<ge>\<close>2), writing \<open>h\<close>.
      Powers the SS7 read characterisation at \<open>c6_pos = pos\<close>
      (off-write from SS6 which writes at \<open>c5_pos = pos \<mp> 1\<close>).\<close>
  have tape_c5_at_pos_for_pos_ge2:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2
            \<Longrightarrow> ktc_tape c5 kk (ktc_pos c' kk) = fst (snd (buf5 kk))"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume hge2: "ktc_pos c' kk \<ge> 2"
    have c4_kk: "ktc_pos c4 kk = ktc_pos c' kk" using c4_pos kklt by simp
    have "ktc_tape c4 kk (ktc_pos c4 kk) \<noteq> LE_block m (le_ktm M)"
      using c4_kk tape_c4_eq_c' home_classification[rule_format, OF kklt] hge2
      by auto
    moreover have "fst (snd (buf5 kk)) \<noteq> LE_block m (le_ktm M)"
      using buf5_not_le_per_tape[rule_format, OF kklt] hge2 by blast
    ultimately show "ktc_tape c5 kk (ktc_pos c' kk) = fst (snd (buf5 kk))"
      using ae_ss5_step_tape(2)[OF step5_sub c4_state kklt] c4_kk
      by (simp add: ae_ss5_action_buf)
  qed

  \<comment> \<open>Sub-step 6b4: head trajectory \<open>c7_pos\<close> for pos\<open>\<ge>\<close>2
      tapes.  \<open>c6_pos = pos\<close> (\<open>c6_pos_for_pos_ge2\<close>); SS7 reads
      \<open>ktc_tape c6 kk pos\<close> = \<open>ktc_tape c5 kk pos\<close> (off-write from
      SS6 at \<open>c5_pos = pos \<mp> 1\<close>) = \<open>fst (snd (buf5 kk))\<close>
      (\<open>tape_c5_at_pos_for_pos_ge2\<close>), non-LE via
      \<open>buf5_not_le_per_tape\<close>.  \<open>h = fst (snd (buf6 kk))\<close>
      non-LE.  \<open>ae_ss7_action\<close>'s else branch fires: dir L if
      \<open>dest = AE_Left\<close> else R.  Head lands at \<open>pos - 1\<close>
      (\<open>dest = AE_Left\<close>) or \<open>pos + 1\<close> (otherwise).\<close>
  have c7_pos_for_pos_ge2:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2
            \<Longrightarrow> ktc_pos c7 kk = (if dest5 kk = AE_Left
                                  then ktc_pos c' kk - 1
                                  else ktc_pos c' kk + 1)"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume hge2: "ktc_pos c' kk \<ge> 2"
    have c6_kk: "ktc_pos c6 kk = ktc_pos c' kk"
      using c6_pos_for_pos_ge2[OF kklt hge2] .
    have pos_ne_c5_pos: "ktc_pos c' kk \<noteq> ktc_pos c5 kk"
      using c5_move_for_pos_ge2[OF kklt hge2] hge2
      by (cases "dest5 kk = AE_Left") auto
    have h5: "fst (snd (buf5 kk)) \<noteq> LE_block m (le_ktm M)"
      using buf5_not_le_per_tape[rule_format, OF kklt] hge2 by blast
    have "ktc_tape c6 kk (ktc_pos c6 kk) = fst (snd (buf5 kk))"
      using c6_kk ktm_step_tape_off_head[OF step6 pos_ne_c5_pos]
            tape_c5_at_pos_for_pos_ge2[OF kklt hge2]
      by simp
    then show "ktc_pos c7 kk = (if dest5 kk = AE_Left
                                then ktc_pos c' kk - 1
                                else ktc_pos c' kk + 1)"
      using ae_ss7_step_tape(1)[OF step7_sub c6_state kklt] c6_kk h5
            buf6_eq_buf5 dest6_eq_dest5
      by (cases "dest5 kk = AE_Left") (simp_all add: ae_ss7_action_buf)
  qed

  \<comment> \<open>Sub-step 6b4: head trajectory \<open>c6_pos\<close> for pos=1 tapes,
      uniform across \<open>dest\<close>.  \<open>dest = AE_Left\<close> routes via
      \<open>c6_pos_for_pos1_dest_left\<close> (\<open>c5_pos = 2\<close>, dir L);
      \<open>dest \<noteq> AE_Left\<close> routes via \<open>c5_pos_for_pos1\<close>
      (\<open>c5_pos = 0\<close>): SS6 reads LE at 0 (\<open>tape_c5_zero_le\<close>),
      action's first branch (a = LE) fires with direction R,
      head lands at \<open>c5_pos + 1 = 1\<close>.\<close>
  have c6_pos_for_pos1:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1 \<Longrightarrow> ktc_pos c6 kk = 1"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume pos_kk: "ktc_pos c' kk = 1"
    show "ktc_pos c6 kk = 1"
    proof (cases "dest5 kk = AE_Left")
      case True
      show ?thesis using c6_pos_for_pos1_dest_left[OF kklt pos_kk True] .
    next
      case False
      have c5_kk: "ktc_pos c5 kk = 0"
        using c5_pos_for_pos1[OF kklt pos_kk False] .
      then show ?thesis
        using ae_ss6_step_tape(1)[OF step6_sub c5_state kklt]
              tape_c5_zero_le[rule_format, OF kklt]
        by simp
    qed
  qed

  \<comment> \<open>Sub-step 6b4: head trajectory \<open>c7_pos\<close> for pos=1 tapes.
      \<open>c6_pos = 1\<close> uniformly.  For \<open>dest = AE_Left\<close>: defers to
      the sub-step 5 lemma \<open>c7_pos_for_pos1_dest_left\<close>
      (\<open>c7_pos = 0\<close>).  For \<open>dest \<noteq> AE_Left\<close>: SS7 reads
      \<open>ktc_tape c6 kk 1 = ktc_tape c5 kk 1\<close> (off-write from SS6 at
      \<open>c5_pos = 0\<close>) \<open>= fst (snd (buf5 kk)) = hh\<close>
      (\<open>tape_c5_at_one_pos1\<close>), non-LE (\<open>buf5_not_le_per_tape\<close>
      pos=1).  \<open>h\<close> non-LE; \<open>ae_ss7_action\<close>'s else branch
      with \<open>dest \<noteq> AE_Left\<close> gives dir R, head lands at \<open>2\<close>.\<close>
  have c7_pos_for_pos1:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1
            \<Longrightarrow> ktc_pos c7 kk = (if dest5 kk = AE_Left then 0 else 2)"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume pos_kk: "ktc_pos c' kk = 1"
    show "ktc_pos c7 kk = (if dest5 kk = AE_Left then 0 else 2)"
    proof (cases "dest5 kk = AE_Left")
      case True
      have "ktc_pos c7 kk = 0"
        using c7_pos_for_pos1_dest_left[OF kklt pos_kk True] .
      thus ?thesis using True by simp
    next
      case False
      have c6_kk: "ktc_pos c6 kk = 1" using c6_pos_for_pos1[OF kklt pos_kk] .
      have one_ne_c5_pos: "(1 :: nat) \<noteq> ktc_pos c5 kk"
        using c5_pos_for_pos1[OF kklt pos_kk False] by simp
      have h5: "fst (snd (buf5 kk)) \<noteq> LE_block m (le_ktm M)"
        using buf5_not_le_per_tape[rule_format, OF kklt] pos_kk by blast
      have "ktc_tape c6 kk (ktc_pos c6 kk) = fst (snd (buf5 kk))"
        using c6_kk ktm_step_tape_off_head[OF step6 one_ne_c5_pos]
              tape_c5_at_one_pos1[OF kklt pos_kk]
        by simp
      then show ?thesis
        using ae_ss7_step_tape(1)[OF step7_sub c6_state kklt] c6_kk h5 False
              buf6_eq_buf5 dest6_eq_dest5
        by (simp add: ae_ss7_action_buf)
    qed
  qed

  \<comment> \<open>Sub-step 6b5 helper: \<open>c6\<close> tape at cell 0 for pos=0 tapes.
      SS6 writes at \<open>c5_pos = 0\<close>, reading \<open>c5@0 = LE_block\<close>
      (\<open>tape_c5_zero_le\<close>); action's first branch \<open>a = LE\<close> fires,
      writing \<open>a = LE_block\<close> back.  So \<open>c6@0 = LE_block\<close>.\<close>
  have tape_c6_zero_le_for_pos0:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 0 \<Longrightarrow> ktc_tape c6 kk 0 = LE_block m (le_ktm M)"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume pos_kk: "ktc_pos c' kk = 0"
    have c5_kk: "ktc_pos c5 kk = 0" using c5_pos_for_pos0[OF kklt pos_kk] .
    then show "ktc_tape c6 kk 0 = LE_block m (le_ktm M)"
      using ae_ss6_step_tape(2)[OF step6_sub c5_state kklt]
            tape_c5_zero_le[rule_format, OF kklt]
      by simp
  qed

  \<comment> \<open>Sub-step 6b5 helper: \<open>c7\<close> tape at cell 1 for pos=0 tapes
      under \<open>dest = AE_Right\<close>.  SS7 writes at \<open>c6_pos = 1\<close>,
      reading \<open>c6@1\<close> non-LE and with home-slot \<open>h = LE\<close>;
      action's second branch fires (h = LE), and with \<open>dest =
      AE_Right\<close> writes \<open>r = snd (snd (buf5 kk))\<close>.\<close>
  have tape_c7_at_one_for_pos0_right:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 0 \<Longrightarrow> dest5 kk = AE_Right
            \<Longrightarrow> ktc_tape c7 kk 1 = snd (snd (buf5 kk))"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume pos_kk: "ktc_pos c' kk = 0"
    assume dest_eq: "dest5 kk = AE_Right"
    have c6_kk: "ktc_pos c6 kk = 1" using c6_pos_for_pos0[OF kklt pos_kk] .
    have one_ne_c5_pos: "(1 :: nat) \<noteq> ktc_pos c5 kk"
      using c5_pos_for_pos0[OF kklt pos_kk] by simp
    have one_ne_c4_pos: "(1 :: nat) \<noteq> ktc_pos c4 kk"
      using c4_pos kklt pos_kk by simp
    have c6_at_1: "ktc_tape c6 kk 1 = ktc_tape c' kk 1"
      using ktm_step_tape_off_head[OF step6 one_ne_c5_pos]
            ktm_step_tape_off_head[OF step5 one_ne_c4_pos] tape_c4_eq_c'
      by simp
    have "ktc_tape c6 kk (ktc_pos c6 kk) \<noteq> LE_block m (le_ktm M)"
      using c6_kk c6_at_1 right_not_le_c'[rule_format, of kk] pos_kk by simp
    moreover have "fst (snd (buf6 kk)) = LE_block m (le_ktm M)"
      using buf5_h_le_for_pos0[rule_format, OF kklt pos_kk] buf6_eq_buf5 by simp
    ultimately show "ktc_tape c7 kk 1 = snd (snd (buf5 kk))"
      using ae_ss7_step_tape(2)[OF step7_sub c6_state kklt] c6_kk dest_eq
            buf6_eq_buf5 dest6_eq_dest5
      by (simp add: ae_ss7_action_buf)
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
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 0
            \<Longrightarrow> ktc_pos c8 kk = (if dest5 kk = AE_Right then 1 else 0)"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume pos_kk: "ktc_pos c' kk = 0"
    note step8_kk = ae_ss8_step_tape(1)[OF step8_sub c7_state kklt]
    show "ktc_pos c8 kk = (if dest5 kk = AE_Right then 1 else 0)"
    proof (cases "dest5 kk = AE_Right")
      case True
      have c7_kk: "ktc_pos c7 kk = 1" using c7_pos_for_pos0[OF kklt pos_kk] True by simp
      have "snd (snd (buf5 kk)) \<noteq> LE_block m (le_ktm M)"
        using buf5_not_le_per_tape[rule_format, OF kklt] pos_kk by blast
      moreover have "fst (snd (buf6 kk)) = LE_block m (le_ktm M)"
        using buf5_h_le_for_pos0[rule_format, OF kklt pos_kk] buf6_eq_buf5 by simp
      ultimately show ?thesis
        using step8_kk c7_kk tape_c7_at_one_for_pos0_right[OF kklt pos_kk True]
              True dest6_eq_dest5
        by (simp add: ae_ss8_action_buf)
    next
      case False
      have c7_kk: "ktc_pos c7 kk = 0"
        using c7_pos_for_pos0[OF kklt pos_kk] False by simp
      have zero_ne_c6_pos: "(0 :: nat) \<noteq> ktc_pos c6 kk"
        using c6_pos_for_pos0[OF kklt pos_kk] by simp
      show ?thesis
        using step8_kk c7_kk False ktm_step_tape_off_head[OF step7 zero_ne_c6_pos]
              tape_c6_zero_le_for_pos0[OF kklt pos_kk]
        by simp
    qed
  qed

  \<comment> \<open>Sub-step 6b4: head trajectory \<open>c8_pos\<close> for pos\<open>\<ge>\<close>2
      tapes.  Three-way case-split on \<open>dest5 kk\<close>.  For
      \<open>AE_Left\<close>: \<open>c7_pos = pos - 1\<close>, SS8 reads
      \<open>ktc_tape c' kk (pos - 1)\<close> non-LE (via
      \<open>left_not_le_c'_steady\<close>, chained off SS5/SS6/SS7
      writes); action's else branch \<open>AE_Left\<close> gives \<open>(l, N)\<close>;
      \<open>c8_pos = pos - 1\<close>.  For \<open>AE_Home\<close>: \<open>c7_pos = pos + 1\<close>,
      reads \<open>ktc_tape c' kk (pos + 1)\<close> non-LE (via
      \<open>right_not_le_c'\<close>); else branch \<open>AE_Home\<close> gives
      \<open>(r, L)\<close>; \<open>c8_pos = pos\<close>.  For \<open>AE_Right\<close>:
      same read as \<open>AE_Home\<close>; else branch \<open>AE_Right\<close> gives
      \<open>(r, N)\<close>; \<open>c8_pos = pos + 1\<close>.  Extracted to
      \<open>ae_fwd_c8_pos_for_pos_ge2\<close>.\<close>
  have c8_pos_for_pos_ge2:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2
            \<Longrightarrow> ktc_pos c8 kk = (case dest5 kk of
                                  AE_Left  \<Rightarrow> ktc_pos c' kk - 1
                                | AE_Home  \<Rightarrow> ktc_pos c' kk
                                | AE_Right \<Rightarrow> ktc_pos c' kk + 1)"
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
      \<open>c7_pos = 2\<close>, SS8 reads \<open>ktc_tape c' kk 2\<close> non-LE
      (via \<open>right_not_le_c'\<close> at pos=1); \<open>h\<close> non-LE
      (\<open>buf5_not_le_per_tape\<close> pos=1); else branch dispatches
      \<open>AE_Home\<close> to dir L (\<open>c8_pos = 1\<close>), \<open>AE_Right\<close> to
      dir N (\<open>c8_pos = 2\<close>).  Extracted to
      \<open>ae_fwd_c8_pos_for_pos1\<close>.\<close>
  have c8_pos_for_pos1:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1
            \<Longrightarrow> ktc_pos c8 kk = (case dest5 kk of
                                  AE_Left  \<Rightarrow> 0
                                | AE_Home  \<Rightarrow> 1
                                | AE_Right \<Rightarrow> 2)"
    by (rule ae_fwd_c8_pos_for_pos1[OF step5 tape_c4_eq_c' buf5_not_le_per_tape
          right_not_le_c' c4_pos c5_pos_for_pos1 step6 step7 c7_state
          buf6_eq_buf5 dest6_eq_dest5 c7_pos_for_pos1_dest_left
          tape_c7_zero_le_pos1_dest_left step8_sub c6_pos_for_pos1
          c7_pos_for_pos1])
  show "PROP ?o1" by (fact c5_pos_for_pos0)
  show "PROP ?o2" by (fact c5_move_for_pos_ge2)
  show "PROP ?o3" by (fact c5_pos_for_pos_ge2)
  show "PROP ?o4" by (fact c5_pos_for_pos_ge2_dest_left)
  show "PROP ?o5" by (fact left_not_le_c'_steady)
  show "PROP ?o6" by (fact buf5_h_le_for_pos0)
  show "PROP ?o7" by (fact c6_pos_for_pos0)
  show "PROP ?o8" by (fact c6_pos_for_pos_ge2)
  show "PROP ?o9" by (fact c7_pos_for_pos0)
  show "PROP ?o10" by (fact tape_c5_at_pos_for_pos_ge2)
  show "PROP ?o11" by (fact c7_pos_for_pos_ge2)
  show "PROP ?o12" by (fact c6_pos_for_pos1)
  show "PROP ?o13" by (fact c7_pos_for_pos1)
  show "PROP ?o14" by (fact c8_pos_for_pos0)
  show "PROP ?o15" by (fact c8_pos_for_pos_ge2)
  show "PROP ?o16" by (fact c8_pos_for_pos1)
qed

text \<open>Fourth arm of \<open>ae_simulates_forward_stage_general\<close>: the tape
  contents at \<open>c8\<close>.  Given the head positions of
  \<open>ae_fwd_head_positions\<close> and the \<open>M\<close>-side facts of
  \<open>ae_fwd_m_side_window\<close>, cell 0 of every tape still holds the
  \<open>LE_block\<close>, and each tape of \<open>c8\<close> corresponds to that of
  \<open>cM_k\<close>: the in-window blocks were written from the buffer, the rest
  is untouched.\<close>

lemma ae_fwd_cells_c8:
  fixes M :: "('q, 'a) ktm"
    and cM cM_k :: "('a, 'q) ktc_config"
    and c' c4 c5 c6 c7 c8 :: "(nat \<Rightarrow> 'a,
                                 'q \<times> 'a ae_stage) ktc_config"
  assumes tape_corr: "\<forall>k<k_ktm M. ae_tape_correspondence m (le_ktm M)
                            (ktc_tape cM k) (ktc_tape c' k)"
      and c_ge_1: "1 \<le> m"
      and step5: "(c4, c5) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and c5_state: "ktc_state c5 = (q5, ofs5, buf5, dest5, SS6)"
      and tape_c4_eq_c': "ktc_tape c4 = ktc_tape c'"
      and buf5_not_le_per_tape:
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
      and right_not_le_c':
          "\<forall>k. ktc_tape c' k (ktc_pos c' k + 1) \<noteq> LE_block m (le_ktm M)"
      and c4_pos_all: "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c4 kk = ktc_pos c' kk"
      and tape_c5_zero_le: "\<forall>k<k_ktm M. ktc_tape c5 k 0 = LE_block m (le_ktm M)"
      and c5_pos_for_pos1_all:
          "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk \<noteq> AE_Left
          \<longrightarrow> ktc_pos c5 kk = 0"
      and step6_sub: "(c5, c6) \<in> ktm_step (ae_delta_ss6_ss7 m M)"
      and step6: "(c5, c6) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and step7_sub: "(c6, c7) \<in> ktm_step (ae_delta_ss7_ss8 m M)"
      and step7: "(c6, c7) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and c6_state: "ktc_state c6 = (q6, ofs6, buf6, dest6, SS7)"
      and c7_state: "ktc_state c7 = (q6, ofs6, buf6, dest6, SS8)"
      and buf6_eq_buf5: "buf6 = buf5"
      and dest6_eq_dest5: "dest6 = dest5"
      and c5_pos_for_pos1_dest_left_all:
          "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
          \<longrightarrow> ktc_pos c5 kk = 2"
      and tape_c5_at_one_pos1_all:
          "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1
          \<longrightarrow> ktc_tape c5 kk 1 = fst (snd (buf5 kk))"
      and c7_pos_for_pos1_dest_left_all:
          "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
          \<longrightarrow> ktc_pos c7 kk = 0"
      and step8_sub: "(c7, c8) \<in> ktm_step (ae_delta_ss8_ss1 m M)"
      and step8: "(c7, c8) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and cM_k_window_general:
          "\<forall>kk<k_ktm M. ae_window_invariant_general m
                 (ktc_tape cM_k kk) (ktc_pos cM_k kk)
                 (dest5 kk, ofs5 kk) (buf5 kk)
                 (ktc_pos c' kk) (le_ktm M)"
      and cM_k_zero: "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_tape cM_k kk 0 = le_ktm M"
      and m_tape_off_window_le0:
          "\<And>kk p. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 0
                 \<Longrightarrow> p > m
                 \<Longrightarrow> ktc_tape cM_k kk p = ktc_tape cM kk p"
      and m_tape_off_window_le1:
          "\<And>kk p. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1
                 \<Longrightarrow> p > 2 * m
                 \<Longrightarrow> ktc_tape cM_k kk p = ktc_tape cM kk p"
      and m_tape_off_window_steady:
          "\<And>kk p. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2
                 \<Longrightarrow> p < (ktc_pos c' kk - 2) * m + 1
                     \<or> p \<ge> (ktc_pos c' kk - 2) * m + 1 + 3 * m
                 \<Longrightarrow> ktc_tape cM_k kk p = ktc_tape cM kk p"
      and c5_pos_for_pos0:
          "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 0 \<Longrightarrow> ktc_pos c5 kk = 0"
      and c5_move_for_pos_ge2:
          "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2
               \<Longrightarrow> ktc_pos c5 kk = go_move (if dest5 kk = AE_Left then MoveR else MoveL)
                                            (ktc_pos c' kk)"
      and c5_pos_for_pos_ge2:
          "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2 \<Longrightarrow> dest5 kk \<noteq> AE_Left
               \<Longrightarrow> ktc_pos c5 kk = ktc_pos c' kk - 1"
      and c5_pos_for_pos_ge2_dest_left:
          "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2 \<Longrightarrow> dest5 kk = AE_Left
               \<Longrightarrow> ktc_pos c5 kk = ktc_pos c' kk + 1"
      and left_not_le_c'_steady:
          "\<forall>k. ktc_pos c' k \<ge> 2
               \<longrightarrow> ktc_tape c' k (ktc_pos c' k - 1) \<noteq> LE_block m (le_ktm M)"
      and buf5_h_le_for_pos0:
          "\<forall>k<k_ktm M. ktc_pos c' k = 0 \<longrightarrow> fst (snd (buf5 k)) = LE_block m (le_ktm M)"
      and c6_pos_for_pos0:
          "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 0 \<Longrightarrow> ktc_pos c6 kk = 1"
      and c6_pos_for_pos_ge2:
          "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2 \<Longrightarrow> ktc_pos c6 kk = ktc_pos c' kk"
      and c7_pos_for_pos0:
          "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 0
               \<Longrightarrow> ktc_pos c7 kk = (if dest5 kk = AE_Right then 1 else 0)"
      and tape_c5_at_pos_for_pos_ge2:
          "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2
               \<Longrightarrow> ktc_tape c5 kk (ktc_pos c' kk) = fst (snd (buf5 kk))"
      and c7_pos_for_pos_ge2:
          "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2
               \<Longrightarrow> ktc_pos c7 kk = (if dest5 kk = AE_Left
                                     then ktc_pos c' kk - 1
                                     else ktc_pos c' kk + 1)"
      and c6_pos_for_pos1:
          "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1 \<Longrightarrow> ktc_pos c6 kk = 1"
      and c7_pos_for_pos1:
          "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1
               \<Longrightarrow> ktc_pos c7 kk = (if dest5 kk = AE_Left then 0 else 2)"
  shows "\<forall>kk<k_ktm M. ktc_tape c8 kk 0 = LE_block m (le_ktm M)"
          (is "PROP ?o1")
    and "\<forall>kk<k_ktm M. ae_tape_correspondence m (le_ktm M)
               (ktc_tape cM_k kk) (ktc_tape c8 kk)"
          (is "PROP ?o2")
proof -
  note c4_pos = c4_pos_all[rule_format]
  note c5_pos_for_pos1 = c5_pos_for_pos1_all[rule_format]
  note c5_pos_for_pos1_dest_left = c5_pos_for_pos1_dest_left_all[rule_format]
  note tape_c5_at_one_pos1 = tape_c5_at_one_pos1_all[rule_format]
  note c7_pos_for_pos1_dest_left = c7_pos_for_pos1_dest_left_all[rule_format]
  \<comment> \<open>Sub-step 6d: \<open>tape_c6_zero_le\<close>.  Cell 0 of \<open>c6\<close>
      is \<open>LE_block\<close> for every tape.  Case-split on whether SS6's
      write site \<open>ktc_pos c5 kk\<close> equals 0.  If yes (pos=0 always,
      or pos=1 with \<open>dest \<noteq> AE_Left\<close>): SS6 reads
      \<open>c5@0 = LE\<close> (\<open>tape_c5_zero_le\<close>) and writes LE back via
      the first branch.  If no (pos=1 with \<open>dest = AE_Left\<close>
      has \<open>c5_pos = 2\<close>; pos\<open>\<ge>\<close>2 has
      \<open>c5_pos \<in> {pos-1, pos+1}\<close>): SS6 writes off cell 0, so
      \<open>c6@0 = c5@0 = LE\<close>.\<close>
  have tape_c6_zero_le: "\<forall>kk<k_ktm M. ktc_tape c6 kk 0 = LE_block m (le_ktm M)"
  proof (intro allI impI)
    fix kk
    assume kklt: "kk < k_ktm M"
    show "ktc_tape c6 kk 0 = LE_block m (le_ktm M)"
      using ae_ss6_step_tape(2)[OF step6_sub c5_state kklt]
            tape_c5_zero_le[rule_format, OF kklt]
      by (cases "ktc_pos c5 kk = 0") simp_all
  qed

  \<comment> \<open>Sub-step 6d: \<open>tape_c7_zero_le\<close>.  Cell 0 of \<open>c7\<close>
      is \<open>LE_block\<close>.  SS7's write site \<open>ktc_pos c6 kk\<close> is
      never 0: pos=0 has \<open>c6_pos = 1\<close>; pos=1 has \<open>c6_pos = 1\<close>;
      pos\<open>\<ge>\<close>2 has \<open>c6_pos = pos \<ge> 2\<close>.  Off-write,
      \<open>c7@0 = c6@0 = LE\<close>.\<close>
  have tape_c7_zero_le: "\<forall>kk<k_ktm M. ktc_tape c7 kk 0 = LE_block m (le_ktm M)"
  proof (intro allI impI)
    fix kk
    assume kklt: "kk < k_ktm M"
    have zero_ne_c6: "(0 :: nat) \<noteq> ktc_pos c6 kk"
    proof -
      consider (le0) "ktc_pos c' kk = 0"
             | (le1) "ktc_pos c' kk = 1"
             | (steady) "ktc_pos c' kk \<ge> 2"
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
    have "ktc_tape c7 kk 0 = ktc_tape c6 kk 0"
      using ktm_step_tape_off_head[OF step7 zero_ne_c6] .
    also have "\<dots> = LE_block m (le_ktm M)"
      using tape_c6_zero_le[rule_format, OF kklt] by simp
    finally show "ktc_tape c7 kk 0 = LE_block m (le_ktm M)" .
  qed

  \<comment> \<open>Sub-step 6d: \<open>tape_c8_zero_le\<close>.  Cell 0 of \<open>c8\<close>
      is \<open>LE_block\<close>.  Case-split on whether SS8's write site
      \<open>ktc_pos c7 kk\<close> equals 0.  If yes (pos=0 with \<open>dest \<noteq>
      AE_Right\<close>, or pos=1 with \<open>dest = AE_Left\<close>): SS8 reads
      \<open>c7@0 = LE\<close> (\<open>tape_c7_zero_le\<close>) and writes LE back
      via the first branch.  If no: SS8 writes off 0, so
      \<open>c8@0 = c7@0 = LE\<close>.\<close>
  have tape_c8_zero_le: "\<forall>kk<k_ktm M. ktc_tape c8 kk 0 = LE_block m (le_ktm M)"
  proof (intro allI impI)
    fix kk
    assume kklt: "kk < k_ktm M"
    show "ktc_tape c8 kk 0 = LE_block m (le_ktm M)"
      using ae_ss8_step_tape(2)[OF step8_sub c7_state kklt]
            tape_c7_zero_le[rule_format, OF kklt]
      by (cases "ktc_pos c7 kk = 0") simp_all
  qed

  \<comment> \<open>Sub-step 6b6: M'-side off-window preservation.
      Regime-agnostic form: cells outside all four SS5\<open>\<dots>\<close>SS8 write
      sites are preserved from \<open>c'\<close>.  Each substep writes at one
      per-tape position; chaining the four \<open>ktm_step_tape_off_head\<close>
      facts plus \<open>tape_c4_eq_c'\<close> gives the result.  Per-regime
      instantiation provides the s-not-in-window precondition.\<close>
  have c8_tape_off_window:
      "\<And>kk s. s \<noteq> ktc_pos c4 kk \<Longrightarrow> s \<noteq> ktc_pos c5 kk
              \<Longrightarrow> s \<noteq> ktc_pos c6 kk \<Longrightarrow> s \<noteq> ktc_pos c7 kk
              \<Longrightarrow> ktc_tape c8 kk s = ktc_tape c' kk s"
  proof -
    fix kk
    fix s :: nat
    assume s_ne_c4: "s \<noteq> ktc_pos c4 kk"
    assume s_ne_c5: "s \<noteq> ktc_pos c5 kk"
    assume s_ne_c6: "s \<noteq> ktc_pos c6 kk"
    assume s_ne_c7: "s \<noteq> ktc_pos c7 kk"
    have c5_eq_c4: "ktc_tape c5 kk s = ktc_tape c4 kk s"
      using ktm_step_tape_off_head[OF step5 s_ne_c4] .
    have c6_eq_c5: "ktc_tape c6 kk s = ktc_tape c5 kk s"
      using ktm_step_tape_off_head[OF step6 s_ne_c5] .
    have c7_eq_c6: "ktc_tape c7 kk s = ktc_tape c6 kk s"
      using ktm_step_tape_off_head[OF step7 s_ne_c6] .
    have c8_eq_c7: "ktc_tape c8 kk s = ktc_tape c7 kk s"
      using ktm_step_tape_off_head[OF step8 s_ne_c7] .
    show "ktc_tape c8 kk s = ktc_tape c' kk s"
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
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 0
            \<Longrightarrow> ktc_tape c8 kk 1 = snd (snd (buf5 kk))"
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
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1
            \<Longrightarrow> ktc_tape c7 kk 1 = fst (snd (buf5 kk))"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume pos_kk: "ktc_pos c' kk = 1"
    have c6_kk: "ktc_pos c6 kk = 1" using c6_pos_for_pos1[OF kklt pos_kk] .
    have one_ne_c5_pos: "(1 :: nat) \<noteq> ktc_pos c5 kk"
      using c5_pos_for_pos1_dest_left[OF kklt pos_kk] c5_pos_for_pos1[OF kklt pos_kk]
      by (cases "dest5 kk = AE_Left") auto
    have "fst (snd (buf5 kk)) \<noteq> LE_block m (le_ktm M)"
      using buf5_not_le_per_tape[rule_format, OF kklt] pos_kk by blast
    moreover have "ktc_tape c6 kk (ktc_pos c6 kk) = fst (snd (buf5 kk))"
      using c6_kk ktm_step_tape_off_head[OF step6 one_ne_c5_pos]
            tape_c5_at_one_pos1[OF kklt pos_kk]
      by simp
    ultimately show "ktc_tape c7 kk 1 = fst (snd (buf5 kk))"
      using ae_ss7_step_tape(2)[OF step7_sub c6_state kklt] c6_kk buf6_eq_buf5
      by (simp add: ae_ss7_action_buf)
  qed

  \<comment> \<open>Sub-step 6b5: pos=1 in-window c8 value at block 1.
      \<open>c7_pos \<in> {0, 2}\<close>, never 1; so SS8 writes off cell 1.
      \<open>c8@1 = c7@1 = hh\<close>.\<close>
  have c8_tape_at_one_for_pos1:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1
            \<Longrightarrow> ktc_tape c8 kk 1 = fst (snd (buf5 kk))"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume pos_kk: "ktc_pos c' kk = 1"
    have c7_pos_ne_1: "ktc_pos c7 kk \<noteq> 1"
    proof (cases "dest5 kk = AE_Left")
      case True
      have "ktc_pos c7 kk = 0"
        using c7_pos_for_pos1_dest_left[OF kklt pos_kk True] .
      thus ?thesis by simp
    next
      case False
      have "ktc_pos c7 kk = 2"
        using c7_pos_for_pos1[OF kklt pos_kk] False by simp
      thus ?thesis by simp
    qed
    have ne: "(1 :: nat) \<noteq> ktc_pos c7 kk" using c7_pos_ne_1 by simp
    have "ktc_tape c8 kk 1 = ktc_tape c7 kk 1"
      using ktm_step_tape_off_head[OF step8 ne] .
    also have "\<dots> = fst (snd (buf5 kk))"
      using c7_tape_at_one_for_pos1[OF kklt pos_kk] .
    finally show "ktc_tape c8 kk 1 = fst (snd (buf5 kk))" .
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
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1
            \<Longrightarrow> ktc_tape c8 kk 2 = snd (snd (buf5 kk))"
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
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2
            \<Longrightarrow> ktc_tape c7 kk (ktc_pos c' kk) = fst (snd (buf5 kk))"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume hge2: "ktc_pos c' kk \<ge> 2"
    have c6_kk: "ktc_pos c6 kk = ktc_pos c' kk"
      using c6_pos_for_pos_ge2[OF kklt hge2] .
    have pos_ne_c5: "ktc_pos c' kk \<noteq> ktc_pos c5 kk"
      using c5_move_for_pos_ge2[OF kklt hge2] hge2
      by (cases "dest5 kk = AE_Left") auto
    have "fst (snd (buf5 kk)) \<noteq> LE_block m (le_ktm M)"
      using buf5_not_le_per_tape[rule_format, OF kklt] hge2 by blast
    moreover have "ktc_tape c6 kk (ktc_pos c6 kk) = fst (snd (buf5 kk))"
      using c6_kk ktm_step_tape_off_head[OF step6 pos_ne_c5]
            tape_c5_at_pos_for_pos_ge2[OF kklt hge2]
      by simp
    ultimately show "ktc_tape c7 kk (ktc_pos c' kk) = fst (snd (buf5 kk))"
      using ae_ss7_step_tape(2)[OF step7_sub c6_state kklt] c6_kk buf6_eq_buf5
      by (simp add: ae_ss7_action_buf)
  qed

  \<comment> \<open>Sub-step 6b5: pos\<open>\<ge>\<close>2 in-window c8 value at block
      pos.  Uniformly \<open>c8@pos = hh\<close>.  SS8 writes at \<open>c7_pos = pos \<mp> 1\<close>,
      never pos for pos\<open>\<ge>\<close>2; \<open>c8@pos = c7@pos = hh\<close>
      via off-write preservation and \<open>c7_tape_at_pos_for_pos_ge2\<close>.\<close>
  have c8_tape_at_pos_for_pos_ge2:
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2
            \<Longrightarrow> ktc_tape c8 kk (ktc_pos c' kk) = fst (snd (buf5 kk))"
  proof -
    fix kk
    assume kklt: "kk < k_ktm M"
    assume hge2: "ktc_pos c' kk \<ge> 2"
    have pos_ne_c7: "ktc_pos c' kk \<noteq> ktc_pos c7 kk"
    proof (cases "dest5 kk = AE_Left")
      case True
      have "ktc_pos c7 kk = ktc_pos c' kk - 1"
        using c7_pos_for_pos_ge2[OF kklt hge2] True by simp
      thus ?thesis using hge2 by linarith
    next
      case False
      have "ktc_pos c7 kk = ktc_pos c' kk + 1"
        using c7_pos_for_pos_ge2[OF kklt hge2] False by simp
      thus ?thesis by linarith
    qed
    have "ktc_tape c8 kk (ktc_pos c' kk) = ktc_tape c7 kk (ktc_pos c' kk)"
      using ktm_step_tape_off_head[OF step8 pos_ne_c7] .
    also have "\<dots> = fst (snd (buf5 kk))"
      using c7_tape_at_pos_for_pos_ge2[OF kklt hge2] .
    finally show "ktc_tape c8 kk (ktc_pos c' kk) = fst (snd (buf5 kk))" .
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
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2
            \<Longrightarrow> ktc_tape c8 kk (ktc_pos c' kk - 1) = fst (buf5 kk)"
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
      "\<And>kk. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2
            \<Longrightarrow> ktc_tape c8 kk (ktc_pos c' kk + 1) = snd (snd (buf5 kk))"
    by (rule ae_fwd_c8_at_pos_plus_1_ge2[OF step5 c5_state tape_c4_eq_c'
          buf5_not_le_per_tape right_not_le_c' c4_pos step6_sub step6 step7
          c7_state buf6_eq_buf5 dest6_eq_dest5 step8_sub step8
          c5_pos_for_pos_ge2 c5_pos_for_pos_ge2_dest_left c6_pos_for_pos_ge2
          c7_pos_for_pos_ge2])
  let ?c = "m"

  \<comment> \<open>Sub-step 6b5: M-side buf-lin transfers per regime, per
      in-window block.  Projects the window invariant's
      linearisation clause for each \<open>(regime, s)\<close> pair.  Six
      lemmas: pos=0/s=1; pos=1/s=1,2; pos\<open>\<ge>\<close>2/s=pos-1,pos,pos+1.\<close>
  have tape_cM_k_at_one_for_pos0:
      "\<And>kk i. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 0 \<Longrightarrow> i < m
              \<Longrightarrow> ktc_tape cM_k kk (Suc (i :: nat))
                    = (snd (snd (buf5 kk))) i"
  proof -
    fix kk
    fix i :: nat
    assume kklt: "kk < k_ktm M"
    assume pos_kk: "ktc_pos c' kk = 0"
    assume i_lt: "i < m"
    have wi: "ae_window_invariant_general m
                (ktc_tape cM_k kk) (ktc_pos cM_k kk)
                (dest5 kk, ofs5 kk) (buf5 kk)
                (ktc_pos c' kk) (le_ktm M)"
      using cM_k_window_general[rule_format, OF kklt] by simp
    hence win_le0: "ae_window_invariant_le0 m
              (ktc_tape cM_k kk) (ktc_pos cM_k kk)
              (dest5 kk, ofs5 kk) (buf5 kk) (le_ktm M)"
      using pos_kk unfolding ae_window_invariant_general_def by simp
    have buf_eq:
        "ktc_tape cM_k kk (Suc i)
            = buf_lin_at m (buf5 kk) (2 * ?c + i)"
      using win_le0 i_lt unfolding ae_window_invariant_le0_def by blast
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have not_lt_c: "\<not> 2 * ?c + i < ?c" by simp
    have not_lt_2c: "\<not> 2 * ?c + i < 2 * ?c" by simp
    have buf_lin_eq:
        "buf_lin_at m (buf5 kk) (2 * ?c + i)
            = rr ([0..<m] ! ((2 * ?c + i) - 2 * ?c))"
      using buf5_kk not_lt_c not_lt_2c
      unfolding buf_lin_at_def Let_def by simp
    have sub_simp: "(2 * ?c + i) - 2 * ?c = i" by simp
    have enum_at_idx:
        "[0..<m] ! i = i"
      using i_lt by simp
    show "ktc_tape cM_k kk (Suc i) = (snd (snd (buf5 kk))) i"
      using buf_eq buf_lin_eq sub_simp enum_at_idx buf5_kk by simp
  qed

  have tape_cM_k_at_one_for_pos1:
      "\<And>kk i. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1 \<Longrightarrow> i < m
              \<Longrightarrow> ktc_tape cM_k kk (Suc (i :: nat))
                    = (fst (snd (buf5 kk))) i"
  proof -
    fix kk
    fix i :: nat
    assume kklt: "kk < k_ktm M"
    assume pos_kk: "ktc_pos c' kk = 1"
    assume i_lt: "i < m"
    have i_lt_2c: "i < 2 * ?c" using i_lt by linarith
    have wi: "ae_window_invariant_general m
                (ktc_tape cM_k kk) (ktc_pos cM_k kk)
                (dest5 kk, ofs5 kk) (buf5 kk)
                (ktc_pos c' kk) (le_ktm M)"
      using cM_k_window_general[rule_format, OF kklt] by simp
    hence win_le1: "ae_window_invariant_le1 m
              (ktc_tape cM_k kk) (ktc_pos cM_k kk)
              (dest5 kk, ofs5 kk) (buf5 kk) (le_ktm M)"
      using pos_kk unfolding ae_window_invariant_general_def by simp
    have buf_eq:
        "ktc_tape cM_k kk (Suc i)
            = buf_lin_at m (buf5 kk) (?c + i)"
      using win_le1 i_lt_2c unfolding ae_window_invariant_le1_def by blast
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have lt_2c: "?c + i < 2 * ?c" using i_lt by linarith
    have not_lt_c: "\<not> ?c + i < ?c" by simp
    have buf_lin_eq:
        "buf_lin_at m (buf5 kk) (?c + i)
            = hh ([0..<m] ! ((?c + i) - ?c))"
      using buf5_kk not_lt_c lt_2c
      unfolding buf_lin_at_def Let_def by simp
    have sub_simp: "(?c + i) - ?c = i" by simp
    have enum_at_idx:
        "[0..<m] ! i = i"
      using i_lt by simp
    show "ktc_tape cM_k kk (Suc i) = (fst (snd (buf5 kk))) i"
      using buf_eq buf_lin_eq sub_simp enum_at_idx buf5_kk by simp
  qed

  have tape_cM_k_at_two_for_pos1:
      "\<And>kk i. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk = 1 \<Longrightarrow> i < m
              \<Longrightarrow> ktc_tape cM_k kk (Suc (?c + (i :: nat)))
                    = (snd (snd (buf5 kk))) i"
  proof -
    fix kk
    fix i :: nat
    assume kklt: "kk < k_ktm M"
    assume pos_kk: "ktc_pos c' kk = 1"
    assume i_lt: "i < m"
    have addr_lt_2c: "?c + i < 2 * ?c" using i_lt by linarith
    have wi: "ae_window_invariant_general m
                (ktc_tape cM_k kk) (ktc_pos cM_k kk)
                (dest5 kk, ofs5 kk) (buf5 kk)
                (ktc_pos c' kk) (le_ktm M)"
      using cM_k_window_general[rule_format, OF kklt] by simp
    hence win_le1: "ae_window_invariant_le1 m
              (ktc_tape cM_k kk) (ktc_pos cM_k kk)
              (dest5 kk, ofs5 kk) (buf5 kk) (le_ktm M)"
      using pos_kk unfolding ae_window_invariant_general_def by simp
    have buf_eq:
        "ktc_tape cM_k kk (Suc (?c + i))
            = buf_lin_at m (buf5 kk) (?c + (?c + i))"
      using win_le1 addr_lt_2c unfolding ae_window_invariant_le1_def by blast
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have addr_eq: "?c + (?c + i) = 2 * ?c + i" by simp
    have not_lt_c: "\<not> 2 * ?c + i < ?c" by simp
    have not_lt_2c: "\<not> 2 * ?c + i < 2 * ?c" by simp
    have buf_lin_eq:
        "buf_lin_at m (buf5 kk) (2 * ?c + i)
            = rr ([0..<m] ! ((2 * ?c + i) - 2 * ?c))"
      using buf5_kk not_lt_c not_lt_2c
      unfolding buf_lin_at_def Let_def by simp
    have sub_simp: "(2 * ?c + i) - 2 * ?c = i" by simp
    have enum_at_idx:
        "[0..<m] ! i = i"
      using i_lt by simp
    show "ktc_tape cM_k kk (Suc (?c + i)) = (snd (snd (buf5 kk))) i"
      using buf_eq addr_eq buf_lin_eq sub_simp enum_at_idx buf5_kk by simp
  qed

  have tape_cM_k_at_pos_minus_1_for_pos_ge2:
      "\<And>kk i. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2 \<Longrightarrow> i < m
              \<Longrightarrow> ktc_tape cM_k kk ((ktc_pos c' kk - 2) * ?c
                                    + (i :: nat) + 1)
                    = (fst (buf5 kk)) i"
  proof -
    fix kk
    fix i :: nat
    assume kklt: "kk < k_ktm M"
    assume hge2: "ktc_pos c' kk \<ge> 2"
    assume i_lt: "i < m"
    have i_lt_3c: "i < 3 * ?c" using i_lt by linarith
    have wi: "ae_window_invariant_general m
                (ktc_tape cM_k kk) (ktc_pos cM_k kk)
                (dest5 kk, ofs5 kk) (buf5 kk)
                (ktc_pos c' kk) (le_ktm M)"
      using cM_k_window_general[rule_format, OF kklt] by simp
    hence win_steady:
        "ae_window_invariant m (ktc_tape cM_k kk) (ktc_pos cM_k kk)
            (dest5 kk, ofs5 kk) (buf5 kk)
            ((ktc_pos c' kk - 2) * ?c + 1)"
      using hge2 unfolding ae_window_invariant_general_def by simp
    have buf_eq:
        "ktc_tape cM_k kk (((ktc_pos c' kk - 2) * ?c + 1) + i)
            = buf_lin_at m (buf5 kk) i"
      using win_steady i_lt_3c
      unfolding ae_window_invariant_def by blast
    have addr_simp:
        "((ktc_pos c' kk - 2) * ?c + 1) + i
          = (ktc_pos c' kk - 2) * ?c + i + 1" by simp
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have buf_lin_eq:
        "buf_lin_at m (buf5 kk) i
            = ll ([0..<m] ! i)"
      using buf5_kk i_lt unfolding buf_lin_at_def Let_def by simp
    have enum_at_idx:
        "[0..<m] ! i = i"
      using i_lt by simp
    show "ktc_tape cM_k kk ((ktc_pos c' kk - 2) * ?c + i + 1)
            = (fst (buf5 kk)) i"
      using buf_eq addr_simp buf_lin_eq enum_at_idx buf5_kk by simp
  qed

  have tape_cM_k_at_pos_for_pos_ge2:
      "\<And>kk i. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2 \<Longrightarrow> i < m
              \<Longrightarrow> ktc_tape cM_k kk ((ktc_pos c' kk - 1) * ?c
                                    + (i :: nat) + 1)
                    = (fst (snd (buf5 kk))) i"
  proof -
    fix kk
    fix i :: nat
    assume kklt: "kk < k_ktm M"
    assume hge2: "ktc_pos c' kk \<ge> 2"
    assume i_lt: "i < m"
    have addr_lt_3c: "?c + i < 3 * ?c" using i_lt by linarith
    have wi: "ae_window_invariant_general m
                (ktc_tape cM_k kk) (ktc_pos cM_k kk)
                (dest5 kk, ofs5 kk) (buf5 kk)
                (ktc_pos c' kk) (le_ktm M)"
      using cM_k_window_general[rule_format, OF kklt] by simp
    hence win_steady:
        "ae_window_invariant m (ktc_tape cM_k kk) (ktc_pos cM_k kk)
            (dest5 kk, ofs5 kk) (buf5 kk)
            ((ktc_pos c' kk - 2) * ?c + 1)"
      using hge2 unfolding ae_window_invariant_general_def by simp
    have buf_eq:
        "ktc_tape cM_k kk (((ktc_pos c' kk - 2) * ?c + 1) + (?c + i))
            = buf_lin_at m (buf5 kk) (?c + i)"
      using win_steady addr_lt_3c
      unfolding ae_window_invariant_def by blast
    have addr_simp:
        "((ktc_pos c' kk - 2) * ?c + 1) + (?c + i)
          = (ktc_pos c' kk - 1) * ?c + i + 1"
    proof -
      obtain q where q: "ktc_pos c' kk = q + 2"
        using hge2 by (metis le_add_diff_inverse2)
      show ?thesis unfolding q by (simp add: algebra_simps)
    qed
    have buf_eq_rewritten:
        "ktc_tape cM_k kk ((ktc_pos c' kk - 1) * ?c + i + 1)
            = buf_lin_at m (buf5 kk) (?c + i)"
      using buf_eq[unfolded addr_simp] .
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have not_lt_c: "\<not> ?c + i < ?c" by simp
    have lt_2c: "?c + i < 2 * ?c" using i_lt by linarith
    have buf_lin_eq:
        "buf_lin_at m (buf5 kk) (?c + i)
            = hh ([0..<m] ! ((?c + i) - ?c))"
      using buf5_kk not_lt_c lt_2c
      unfolding buf_lin_at_def Let_def by simp
    have sub_simp: "(?c + i) - ?c = i" by simp
    have enum_at_idx:
        "[0..<m] ! i = i"
      using i_lt by simp
    show "ktc_tape cM_k kk ((ktc_pos c' kk - 1) * ?c + i + 1)
            = (fst (snd (buf5 kk))) i"
      using buf_eq_rewritten buf_lin_eq sub_simp enum_at_idx buf5_kk by simp
  qed

  have tape_cM_k_at_pos_plus_1_for_pos_ge2:
      "\<And>kk i. kk < k_ktm M \<Longrightarrow> ktc_pos c' kk \<ge> 2 \<Longrightarrow> i < m
              \<Longrightarrow> ktc_tape cM_k kk (ktc_pos c' kk * ?c
                                    + (i :: nat) + 1)
                    = (snd (snd (buf5 kk))) i"
  proof -
    fix kk
    fix i :: nat
    assume kklt: "kk < k_ktm M"
    assume hge2: "ktc_pos c' kk \<ge> 2"
    assume i_lt: "i < m"
    have addr_lt_3c: "2 * ?c + i < 3 * ?c" using i_lt by linarith
    have wi: "ae_window_invariant_general m
                (ktc_tape cM_k kk) (ktc_pos cM_k kk)
                (dest5 kk, ofs5 kk) (buf5 kk)
                (ktc_pos c' kk) (le_ktm M)"
      using cM_k_window_general[rule_format, OF kklt] by simp
    hence win_steady:
        "ae_window_invariant m (ktc_tape cM_k kk) (ktc_pos cM_k kk)
            (dest5 kk, ofs5 kk) (buf5 kk)
            ((ktc_pos c' kk - 2) * ?c + 1)"
      using hge2 unfolding ae_window_invariant_general_def by simp
    have buf_eq:
        "ktc_tape cM_k kk (((ktc_pos c' kk - 2) * ?c + 1) + (2 * ?c + i))
            = buf_lin_at m (buf5 kk) (2 * ?c + i)"
      using win_steady addr_lt_3c
      unfolding ae_window_invariant_def by blast
    have addr_simp:
        "((ktc_pos c' kk - 2) * ?c + 1) + (2 * ?c + i)
          = ktc_pos c' kk * ?c + i + 1"
      using hge2 by (simp add: algebra_simps diff_mult_distrib)
    have buf_eq_rewritten:
        "ktc_tape cM_k kk (ktc_pos c' kk * ?c + i + 1)
            = buf_lin_at m (buf5 kk) (2 * ?c + i)"
      using buf_eq[unfolded addr_simp] .
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have not_lt_c: "\<not> 2 * ?c + i < ?c" by simp
    have not_lt_2c: "\<not> 2 * ?c + i < 2 * ?c" by simp
    have buf_lin_eq:
        "buf_lin_at m (buf5 kk) (2 * ?c + i)
            = rr ([0..<m] ! ((2 * ?c + i) - 2 * ?c))"
      using buf5_kk not_lt_c not_lt_2c
      unfolding buf_lin_at_def Let_def by simp
    have sub_simp: "(2 * ?c + i) - 2 * ?c = i" by simp
    have enum_at_idx:
        "[0..<m] ! i = i"
      using i_lt by simp
    show "ktc_tape cM_k kk (ktc_pos c' kk * ?c + i + 1)
            = (snd (snd (buf5 kk))) i"
      using buf_eq_rewritten buf_lin_eq sub_simp enum_at_idx buf5_kk by simp
  qed

  \<comment> \<open>Sub-step 6b-assemble: per-tape regime-aware
      \<open>ae_tape_correspondence\<close> between \<open>cM_k\<close> and \<open>c8\<close>.
      Per-tape branches on \<open>ktc_pos c' kk\<close>; within each regime,
      per-block branches on \<open>s\<close> match an in-window value
      (buf-lin transfer + c8 in-window value coincide on buf5 slot)
      or an off-window value (\<open>cM_k = cM = c'\<close> M-side via
      \<open>m_tape_off_window\<close> + \<open>tape_corr\<close>; \<open>c8 = c'\<close> M'-side via
      \<open>c8_tape_off_window\<close>).  Extracted to \<open>ae_fwd_tape_corr_c8\<close>.\<close>
  have tape_corr_c8:
      "\<forall>kk<k_ktm M. ae_tape_correspondence m (le_ktm M)
              (ktc_tape cM_k kk) (ktc_tape c8 kk)"
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
  show "PROP ?o1" by (fact tape_c8_zero_le)
  show "PROP ?o2" by (fact tape_corr_c8)
qed

end
