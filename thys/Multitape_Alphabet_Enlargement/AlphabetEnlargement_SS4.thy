theory AlphabetEnlargement_SS4
  imports AlphabetEnlargement_ComputeCorrect
begin

subsection \<open>SS4 trace-existence and buffer characterisations\<close>

subsubsection \<open>SS4\<open>\<rightarrow>\<close>SS5 trace-existence\<close>

text \<open>Trace-driven SS4\<open>\<rightarrow>\<close>SS5 step existence.
  Takes the external M-trace prefix
  \<open>(Config qM tsM nM, cM_k) \<in> delta_tm^^kM\<close> with its
  no-pre-halt and end-or-full structure, and produces a
  SS4\<open>\<rightarrow>\<close>SS5 step whose buffered-run choice aligns with the
  external trace's \<open>cM_k\<close> endpoint.  Used by the chain
  proof in \<open>ae_simulates_forward_stage\<close> to keep the
  constructed \<open>M'\<close>-trace aligned with the externally-given
  M-trace; the conclusion exposes \<open>q_out = mt_state cM_k\<close> at
  the SS5 boundary so the chain proof carries the state
  correspondence forward.\<close>

text \<open>Shared substep-tuple construction for the SS4\<open>\<rightarrow>\<close>SS5
  trace-existence lemmas.  Given a buffered \<open>m_steps_buffered\<close>
  result over the SS4-entry buffer (with the right slot holding the
  freshly-read tape value at the substrate head) and the arm-uniform
  preconditions \<open>q \<in> Q_tm M\<close>, non-halt, and gamma-block, produces
  an SS5-stage config \<open>c''\<close> with both step relations
  (substep-specific and full alphabet-enlarge), the expected state
  shape, and unchanged substrate tape (SS4\<open>\<rightarrow>\<close>SS5 is a
  no-write substep on the substrate).  Consumed by the three
  \<open>ae_step_ss4_ss5_exists_*_trace\<close> variants: the arm-specific
  difference lives only in the buffer non-LE claim and the
  arm-specific post-trace window predicate, both of which the
  callers derive separately.\<close>

lemma ae_step_ss4_ss5_construct_from_buffered:
  fixes M :: "('q, 'a) mttm"
    and c' :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) mt_config"
    and q :: 'q
    and ofs :: "nat \<Rightarrow> 'c"
    and buf :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest :: "nat \<Rightarrow> ae_dest"
    and ts :: "nat \<Rightarrow> nat \<Rightarrow> ('c \<Rightarrow> 'a)"
    and n :: "nat \<Rightarrow> nat"
    and q_out :: 'q
    and buf' :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and end_pos :: "nat \<Rightarrow> 'c bp"
  assumes vM:     "valid_mttm M"
      and c'_eq:  "c' = Config\<^sub>M (q, ofs, buf, dest, SS4) ts n"
      and q_in:   "q \<in> Q_tm M"
      and nhalt:  "q \<noteq> t_tm M \<and> q \<noteq> r_tm M"
      and gamma:  "ae_tape_in_gamma_block M c'"
      and bufv:   "ae_buffer_in_gamma_block M c'"
      and mst:    "((q, \<lambda>k. (fst (buf k),
                                 if k < k_tm M then fst (snd (buf k)) else ts k (n k),
                                 ts k (n k)),
                          \<lambda>k. (AE_Home, ofs k)),
                    (q_out, buf', end_pos)) \<in> m_steps_buffered M"
  obtains c'' where
      "(c', c'') \<in> mttm_step (ae_delta_ss4_ss5 M)"
    and "(c', c'') \<in> mttm_step (alphabet_enlarge_delta M)"
    and "mt_state c'' = (q_out,
            \<lambda>k. if k < k_tm M then snd (end_pos k) else init_offset k,
            \<lambda>k. if k < k_tm M then buf' k else init_buffer (le_tm M) k,
            \<lambda>k. if k < k_tm M then fst (end_pos k) else init_dest k, SS5)"
    and "mt_tape c'' = ts"
proof -
  let ?a = "\<lambda>k. ts k (n k)"
  have a_support: "\<forall>j\<ge>k_tm M. ?a j = bl_block (bl_tm M)"
    using gamma c'_eq unfolding ae_tape_in_gamma_block_def by auto
  let ?d = "\<lambda>k. if k < k_tm M
                  then (if ?a k = LE_block (le_tm M) then dir.N else dir.L)
                  else dir.N"
  let ?ofs'  = "\<lambda>k. if k < k_tm M then snd (end_pos k) else init_offset k"
  let ?buf'g = "\<lambda>k. if k < k_tm M then buf' k else init_buffer (le_tm M) k"
  let ?dest' = "\<lambda>k. if k < k_tm M then fst (end_pos k) else init_dest k"
  let ?c'' = "Config\<^sub>M (q_out, ?ofs', ?buf'g, ?dest', SS5) ts
                       (\<lambda>k. go_dir (?d k) (n k))"
  have rel_in: "((q, ofs, buf, dest, SS4), ?a,
                  (q_out, ?ofs', ?buf'g, ?dest', SS5), ?a, ?d)
                  \<in> ae_delta_ss4_ss5 M"
    unfolding ae_delta_ss4_ss5_def using q_in nhalt mst a_support by blast
  have gamma_a: "\<forall>k. ?a k \<in> gamma_block (\<Gamma>_tm M)"
    using gamma c'_eq unfolding ae_tape_in_gamma_block_def by simp
  have src_valid: "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M)
                      (snd ((q, ofs, buf, dest, SS4)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using bufv c'_eq
    unfolding ae_buffer_in_gamma_block_def ae_valid_stage_def by simp
  have dst_valid: "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M)
                      (snd ((q_out, ?ofs', ?buf'g, ?dest', SS5)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    by (rule ae_delta_ss4_ss5_dest_valid[OF vM rel_in gamma_a src_valid])
  have aed_in: "((q, ofs, buf, dest, SS4), ?a,
                  (q_out, ?ofs', ?buf'g, ?dest', SS5), ?a, ?d)
                  \<in> alphabet_enlarge_delta M"
    unfolding alphabet_enlarge_delta_def
    using rel_in gamma_a src_valid dst_valid by auto
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts"
    by (rule ext) auto
  have step_sub_raw:
    "(Config\<^sub>M (q, ofs, buf, dest, SS4) ts n,
       Config\<^sub>M (q_out, ?ofs', ?buf'g, ?dest', SS5)
         (\<lambda>k. (ts k)(n k := ?a k))
         (\<lambda>k. go_dir (?d k) (n k)))
       \<in> mttm_step (ae_delta_ss4_ss5 M)"
    by (rule mttm_step.intros) (rule rel_in)
  have step_sub: "(c', ?c'') \<in> mttm_step (ae_delta_ss4_ss5 M)"
    using step_sub_raw c'_eq ts_unchanged by simp
  have step_full_raw:
    "(Config\<^sub>M (q, ofs, buf, dest, SS4) ts n,
       Config\<^sub>M (q_out, ?ofs', ?buf'g, ?dest', SS5)
         (\<lambda>k. (ts k)(n k := ?a k))
         (\<lambda>k. go_dir (?d k) (n k)))
       \<in> mttm_step (alphabet_enlarge_delta M)"
    by (rule mttm_step.intros) (rule aed_in)
  have step_full: "(c', ?c'') \<in> mttm_step (alphabet_enlarge_delta M)"
    using step_full_raw c'_eq ts_unchanged by simp
  show thesis
  proof (rule that[where c''="?c''"])
    show "(c', ?c'') \<in> mttm_step (ae_delta_ss4_ss5 M)" using step_sub .
    show "(c', ?c'') \<in> mttm_step (alphabet_enlarge_delta M)"
      using step_full .
    show "mt_state ?c'' = (q_out, ?ofs', ?buf'g, ?dest', SS5)" by simp
    show "mt_tape ?c'' = ts" by simp
  qed
qed


text \<open>Per-tape unified companion of
  \<open>ae_step_ss4_ss5_exists_trace\<close>, \<open>_le0_trace\<close>, and
  \<open>_le1_trace\<close>.  A trace-driven SS4\<open>\<rightarrow>\<close>SS5
  step-existence wrapper.  Takes a per-tape regime selector
  \<open>pos = mt_pos c' k\<close>, the per-tape hybrid window invariant,
  the per-tape regime-guarded \<open>no_le\<close>, and the
  \<open>pos = 0\<close>-conditional left-slot guard.  Invokes
  \<open>ae_m_steps_buffered_correct_trace_general\<close> and then
  \<open>ae_step_ss4_ss5_construct_from_buffered\<close> to package
  the substep transition and the per-tape regime-aware buffer
  slot non-LE-ness in an \<open>obtains\<close>-style witness.

  Per-tape regime-aware output: each tape's buffer slot
  non-LE-ness depends on its regime — \<open>pos = 0\<close> tapes have
  left and right slots non-LE (home is \<open>LE_block\<close> by le0 window
  invariant); \<open>pos = 1\<close> tapes have home and right slots
  non-LE (left is \<open>LE_block\<close> by le1 window invariant);
  \<open>pos \<ge> 2\<close> tapes have all three slots non-LE.

  Consumer: \<open>ae_simulates_forward_stage_general\<close>'s body.\<close>

lemma ae_step_ss4_ss5_exists_general_trace:
  fixes M :: "('q, 'a) mttm"
    and c' :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) mt_config"
    and tsM :: "nat \<Rightarrow> nat \<Rightarrow> 'a"
    and nM :: "nat \<Rightarrow> nat"
    and pos :: "nat \<Rightarrow> nat"
    and kM :: nat
    and cM_k :: "('a, 'q) mt_config"
  assumes vM:        "valid_mttm M"
      and lu:        "le_unique M"
      and inv:       "ae_inv_ss4 M c'"
      and gamma:     "ae_tape_in_gamma_block M c'"
      and bufv:      "ae_buffer_in_gamma_block M c'"
      and q_neq_t:   "fst (mt_state c') \<noteq> t_tm M"
      and q_neq_r:   "fst (mt_state c') \<noteq> r_tm M"
      and window:
            "\<forall>k<k_tm M. ae_window_invariant_general (tsM k) (nM k)
                   (case mt_state c' of (_, ofs, _, _, _)
                        \<Rightarrow> (AE_Home, ofs k))
                   (case mt_state c' of (_, _, buf, _, _)
                        \<Rightarrow> (fst (buf k), fst (snd (buf k)),
                            mt_tape c' k (mt_pos c' k)))
                   (pos k) (le_tm M)"
      and no_le:
            "\<forall>k. (pos k = 0
                    \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                              \<longrightarrow> tsM k (Suc i) \<noteq> le_tm M))
                 \<and> (pos k = 1
                      \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                                \<longrightarrow> tsM k (Suc i) \<noteq> le_tm M))
                 \<and> (pos k \<ge> 2
                      \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                                \<longrightarrow> tsM k
                                      ((pos k - 2) * card (UNIV :: 'c set)
                                        + 1 + i)
                                    \<noteq> le_tm M))"
      and trace:
            "(Config\<^sub>M (fst (mt_state c')) tsM nM, cM_k)
                \<in> mttm_step (delta_tm M) ^^ kM"
      and kM_le:     "kM \<le> card (UNIV :: 'c set)"
      and end_or_halt:
            "kM = card (UNIV :: 'c set)
              \<or> mt_state cM_k \<in> {t_tm M, r_tm M}"
      and left_not_le_pos0:
            "case mt_state c' of (_, _, buf, _, _) \<Rightarrow>
                 \<forall>k<k_tm M. pos k = 0 \<longrightarrow> fst (buf k) \<noteq> LE_block (le_tm M)"
  obtains c'' where
      "(c', c'') \<in> mttm_step (ae_delta_ss4_ss5 M)"
    and "(c', c'') \<in> mttm_step (alphabet_enlarge_delta M)"
    and "case mt_state c'' of (q_out, _, _, _, _)
            \<Rightarrow> q_out = mt_state cM_k"
    and "case mt_state c'' of (_, _, buf', _, _) \<Rightarrow>
            \<forall>k<k_tm M. (pos k = 0
                    \<longrightarrow> fst (buf' k) \<noteq> LE_block (le_tm M)
                      \<and> snd (snd (buf' k)) \<noteq> LE_block (le_tm M))
                 \<and> (pos k = 1
                      \<longrightarrow> fst (snd (buf' k)) \<noteq> LE_block (le_tm M)
                        \<and> snd (snd (buf' k)) \<noteq> LE_block (le_tm M))
                 \<and> (pos k \<ge> 2
                      \<longrightarrow> fst (buf' k) \<noteq> LE_block (le_tm M)
                        \<and> fst (snd (buf' k)) \<noteq> LE_block (le_tm M)
                        \<and> snd (snd (buf' k)) \<noteq> LE_block (le_tm M))"
    and "case mt_state c'' of (_, ofs', buf', dest', _) \<Rightarrow>
            \<forall>k<k_tm M. ae_window_invariant_general
                  (mt_tape cM_k k) (mt_pos cM_k k)
                  (dest' k, ofs' k) (buf' k) (pos k) (le_tm M)"
proof -
  obtain q ofs buf dest where
      state_eq: "mt_state c' = (q, ofs, buf, dest, SS4)"
      and q_in: "q \<in> Q_tm M"
    using inv unfolding ae_inv_ss4_def
    by (cases "mt_state c'") auto
  obtain ts n where c'_eq: "c' = Config\<^sub>M (q, ofs, buf, dest, SS4) ts n"
    using state_eq by (cases c') auto
  let ?a = "\<lambda>k. ts k (n k)"
  let ?d = "\<lambda>k. if ?a k = LE_block (le_tm M) then dir.N else dir.L"
  let ?buf_full = "\<lambda>k. (fst (buf k),
                          if k < k_tm M then fst (snd (buf k)) else ?a k,
                          ?a k)"
  have nhalt: "q \<noteq> t_tm M \<and> q \<noteq> r_tm M"
    using q_neq_t q_neq_r state_eq by simp
  have window':
      "\<forall>k<k_tm M. ae_window_invariant_general (tsM k) (nM k) (AE_Home, ofs k)
                                        (?buf_full k) (pos k) (le_tm M)"
    using window c'_eq by simp
  have pad_home':
      "\<forall>k\<ge>k_tm M. fst (snd (?buf_full k)) = bl_block (bl_tm M)"
  proof (intro allI impI)
    fix k assume kge: "k_tm M \<le> k"
    have "ts k (n k) = bl_block (bl_tm M)"
      using gamma c'_eq kge unfolding ae_tape_in_gamma_block_def by simp
    thus "fst (snd (?buf_full k)) = bl_block (bl_tm M)" using kge by simp
  qed
  have q_eq: "fst (mt_state c') = q" using state_eq by simp
  have trace': "(Config\<^sub>M q tsM nM, cM_k)
                  \<in> mttm_step (delta_tm M) ^^ kM"
    using trace q_eq by simp
  have left_not_le_buf_full:
      "\<forall>k<k_tm M. pos k = 0 \<longrightarrow> fst (?buf_full k) \<noteq> LE_block (le_tm M)"
    using left_not_le_pos0 state_eq by simp
  obtain q_out buf' end_pos where
      mst_in: "((q, ?buf_full, \<lambda>k. (AE_Home, ofs k)),
                 (q_out, buf', end_pos)) \<in> m_steps_buffered M"
    and q_out_eq: "q_out = mt_state cM_k"
    and new_window:
        "\<forall>k<k_tm M. ae_window_invariant_general
              (mt_tape cM_k k) (mt_pos cM_k k)
              (end_pos k) (buf' k) (pos k) (le_tm M)"
    and post_no_le:
        "\<forall>k. (pos k = 0
                \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                          \<longrightarrow> mt_tape cM_k k (Suc i) \<noteq> le_tm M))
             \<and> (pos k = 1
                  \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                            \<longrightarrow> mt_tape cM_k k (Suc i) \<noteq> le_tm M))
             \<and> (pos k \<ge> 2
                  \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                            \<longrightarrow> mt_tape cM_k k
                                  ((pos k - 2) * card (UNIV :: 'c set)
                                    + 1 + i)
                                \<noteq> le_tm M))"
    and post_left_not_le_pos0:
        "\<forall>k<k_tm M. pos k = 0
              \<longrightarrow> fst (buf' k) \<noteq> LE_block (le_tm M)"
    by (rule ae_m_steps_buffered_correct_trace_general[OF vM lu q_in window'
                                                          pad_home' no_le trace'
                                                          kM_le end_or_halt
                                                          left_not_le_buf_full])
  \<comment> \<open>Per-tape regime-aware derivation of buffer-slot
      non-LE-ness.  Each branch reads off the relevant
      buf-linearisation slot via the corresponding sibling window
      invariant, combined with the \<open>post_no_le\<close> hypothesis at the
      slot's M-tape index.\<close>
  have c_ge_1: "1 \<le> card (UNIV :: 'c set)"
    using c_idx_lt_card[of "SOME x :: 'c. True"] by simp
  let ?c = "card (UNIV :: 'c set)"
  have buf_per_tape_not_le:
      "\<forall>k<k_tm M. (pos k = 0
              \<longrightarrow> fst (buf' k) \<noteq> LE_block (le_tm M)
                \<and> snd (snd (buf' k)) \<noteq> LE_block (le_tm M))
           \<and> (pos k = 1
                \<longrightarrow> fst (snd (buf' k)) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf' k)) \<noteq> LE_block (le_tm M))
           \<and> (pos k \<ge> 2
                \<longrightarrow> fst (buf' k) \<noteq> LE_block (le_tm M)
                  \<and> fst (snd (buf' k)) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf' k)) \<noteq> LE_block (le_tm M))"
  proof (intro allI impI)
    fix k
    assume klt: "k < k_tm M"
    obtain l h r where buf_k: "buf' k = (l, h, r)"
      by (cases "buf' k") auto
    show "(pos k = 0
              \<longrightarrow> fst (buf' k) \<noteq> LE_block (le_tm M)
                \<and> snd (snd (buf' k)) \<noteq> LE_block (le_tm M))
           \<and> (pos k = 1
                \<longrightarrow> fst (snd (buf' k)) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf' k)) \<noteq> LE_block (le_tm M))
           \<and> (pos k \<ge> 2
                \<longrightarrow> fst (buf' k) \<noteq> LE_block (le_tm M)
                  \<and> fst (snd (buf' k)) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf' k)) \<noteq> LE_block (le_tm M))"
    proof (intro conjI)
      \<comment> \<open>Branch pos = 0 ::: left and right slots non-LE.\<close>
      show "pos k = 0
            \<longrightarrow> fst (buf' k) \<noteq> LE_block (le_tm M)
              \<and> snd (snd (buf' k)) \<noteq> LE_block (le_tm M)"
    proof
      assume hpos: "pos k = 0"
      have win_k_le0:
          "ae_window_invariant_le0 (mt_tape cM_k k) (mt_pos cM_k k)
                (end_pos k) (buf' k) (le_tm M)"
        using new_window[rule_format, OF klt] hpos
        unfolding ae_window_invariant_general_def by blast
      have post_no_le_k:
          "\<forall>i. i < ?c \<longrightarrow> mt_tape cM_k k (Suc i) \<noteq> le_tm M"
        using post_no_le hpos by blast
      have lt_0c: "(0 :: nat) < ?c" using c_ge_1 by simp
      have eq_1:
          "mt_tape cM_k k (Suc 0) = buf_lin_at (buf' k) (2 * ?c + 0)"
        using win_k_le0 lt_0c
        unfolding ae_window_invariant_le0_def by blast
      have not_lt_c: "\<not> (2 * ?c) < ?c" by simp
      have not_lt_2c: "\<not> (2 * ?c) < 2 * ?c" by simp
      have buf_at_2c:
          "buf_lin_at (buf' k) (2 * ?c) = r ((enum_class.enum :: 'c list) ! 0)"
        using buf_k not_lt_c not_lt_2c
        unfolding buf_lin_at_def Let_def by simp
      have post_at_1: "mt_tape cM_k k (Suc 0) \<noteq> le_tm M"
        using post_no_le_k lt_0c by blast
      have r_at_0_ne: "r ((enum_class.enum :: 'c list) ! 0) \<noteq> le_tm M"
        using eq_1 buf_at_2c post_at_1 by simp
      have r_ne_le_fn: "r \<noteq> (\<lambda>_. le_tm M)"
      proof
        assume "r = (\<lambda>_. le_tm M)"
        hence "r ((enum_class.enum :: 'c list) ! 0) = le_tm M" by simp
        with r_at_0_ne show False by simp
      qed
      have l_not_le: "fst (buf' k) \<noteq> LE_block (le_tm M)"
        using post_left_not_le_pos0 hpos klt by blast
      have r_not_le: "snd (snd (buf' k)) \<noteq> LE_block (le_tm M)"
        using buf_k r_ne_le_fn unfolding LE_block_def by simp
      show "fst (buf' k) \<noteq> LE_block (le_tm M)
            \<and> snd (snd (buf' k)) \<noteq> LE_block (le_tm M)"
        using l_not_le r_not_le by blast
    qed
    \<comment> \<open>Branch pos = 1 ::: home and right slots non-LE.\<close>
    show "pos k = 1
            \<longrightarrow> fst (snd (buf' k)) \<noteq> LE_block (le_tm M)
              \<and> snd (snd (buf' k)) \<noteq> LE_block (le_tm M)"
    proof
      assume hpos: "pos k = 1"
      have win_k_le1:
          "ae_window_invariant_le1 (mt_tape cM_k k) (mt_pos cM_k k)
                (end_pos k) (buf' k) (le_tm M)"
        using new_window[rule_format, OF klt] hpos
        unfolding ae_window_invariant_general_def by blast
      have post_no_le_k:
          "\<forall>i. i < 2 * ?c \<longrightarrow> mt_tape cM_k k (Suc i) \<noteq> le_tm M"
        using post_no_le hpos by blast
      \<comment> \<open>h-slot: i = 0, buf index = c + 0 = c.\<close>
      have lt_0_2c: "(0 :: nat) < 2 * ?c" using c_ge_1 by simp
      have eq_1_h:
          "mt_tape cM_k k (Suc 0) = buf_lin_at (buf' k) (?c + 0)"
        using win_k_le1 lt_0_2c
        unfolding ae_window_invariant_le1_def by blast
      have not_lt_c: "\<not> ?c < ?c" by simp
      have c_lt_2c: "?c < 2 * ?c" using c_ge_1 by simp
      have buf_at_c:
          "buf_lin_at (buf' k) ?c = h ((enum_class.enum :: 'c list) ! 0)"
        using buf_k not_lt_c c_lt_2c
        unfolding buf_lin_at_def Let_def by simp
      have post_at_1: "mt_tape cM_k k (Suc 0) \<noteq> le_tm M"
        using post_no_le_k lt_0_2c by blast
      have h_at_0_ne: "h ((enum_class.enum :: 'c list) ! 0) \<noteq> le_tm M"
        using eq_1_h buf_at_c post_at_1 by simp
      have h_ne_le_fn: "h \<noteq> (\<lambda>_. le_tm M)"
      proof
        assume "h = (\<lambda>_. le_tm M)"
        hence "h ((enum_class.enum :: 'c list) ! 0) = le_tm M" by simp
        with h_at_0_ne show False by simp
      qed
      have h_not_le: "fst (snd (buf' k)) \<noteq> LE_block (le_tm M)"
        using buf_k h_ne_le_fn unfolding LE_block_def by simp
      \<comment> \<open>r-slot: i = c, buf index = c + c = 2c.\<close>
      have lt_c_2c: "?c < 2 * ?c" using c_ge_1 by simp
      have eq_cp1:
          "mt_tape cM_k k (Suc ?c) = buf_lin_at (buf' k) (?c + ?c)"
        using win_k_le1 lt_c_2c
        unfolding ae_window_invariant_le1_def by blast
      have cc_eq_2c: "?c + ?c = 2 * ?c" by simp
      have not_lt_c2: "\<not> (2 * ?c) < ?c" by simp
      have not_lt_2c2: "\<not> (2 * ?c) < 2 * ?c" by simp
      have buf_at_2c:
          "buf_lin_at (buf' k) (2 * ?c) = r ((enum_class.enum :: 'c list) ! 0)"
        using buf_k not_lt_c2 not_lt_2c2
        unfolding buf_lin_at_def Let_def by simp
      have post_at_cp1: "mt_tape cM_k k (Suc ?c) \<noteq> le_tm M"
        using post_no_le_k lt_c_2c by blast
      have r_at_0_ne: "r ((enum_class.enum :: 'c list) ! 0) \<noteq> le_tm M"
        using eq_cp1 cc_eq_2c buf_at_2c post_at_cp1 by simp
      have r_ne_le_fn: "r \<noteq> (\<lambda>_. le_tm M)"
      proof
        assume "r = (\<lambda>_. le_tm M)"
        hence "r ((enum_class.enum :: 'c list) ! 0) = le_tm M" by simp
        with r_at_0_ne show False by simp
      qed
      have r_not_le: "snd (snd (buf' k)) \<noteq> LE_block (le_tm M)"
        using buf_k r_ne_le_fn unfolding LE_block_def by simp
      show "fst (snd (buf' k)) \<noteq> LE_block (le_tm M)
            \<and> snd (snd (buf' k)) \<noteq> LE_block (le_tm M)"
        using h_not_le r_not_le by blast
    qed
    \<comment> \<open>Branch pos >= 2 ::: all three slots non-LE.\<close>
    show "pos k \<ge> 2
            \<longrightarrow> fst (buf' k) \<noteq> LE_block (le_tm M)
              \<and> fst (snd (buf' k)) \<noteq> LE_block (le_tm M)
              \<and> snd (snd (buf' k)) \<noteq> LE_block (le_tm M)"
    proof
      assume hpos: "pos k \<ge> 2"
      let ?p_start = "(pos k - 2) * ?c + 1"
      have win_k_steady:
          "ae_window_invariant (mt_tape cM_k k) (mt_pos cM_k k)
                (end_pos k) (buf' k) ?p_start"
        using new_window[rule_format, OF klt] hpos
        unfolding ae_window_invariant_general_def by blast
      have post_no_le_k:
          "\<forall>i. i < 3 * ?c
                \<longrightarrow> mt_tape cM_k k (?p_start + i) \<noteq> le_tm M"
        using post_no_le hpos by blast
      \<comment> \<open>l-slot: i = 0, buf index = 0.\<close>
      have lt_0: "(0 :: nat) < 3 * ?c" using c_ge_1 by simp
      have eq_0:
          "mt_tape cM_k k (?p_start + 0) = buf_lin_at (buf' k) 0"
        using win_k_steady lt_0
        unfolding ae_window_invariant_def by blast
      have buf_at_0:
          "buf_lin_at (buf' k) 0 = l ((enum_class.enum :: 'c list) ! 0)"
        using buf_k c_ge_1 unfolding buf_lin_at_def Let_def by simp
      have post_at_0: "mt_tape cM_k k (?p_start + 0) \<noteq> le_tm M"
        using post_no_le_k lt_0 by blast
      have l_at_0_ne: "l ((enum_class.enum :: 'c list) ! 0) \<noteq> le_tm M"
        using eq_0 buf_at_0 post_at_0 by simp
      have l_ne_le_fn: "l \<noteq> (\<lambda>_. le_tm M)"
      proof
        assume "l = (\<lambda>_. le_tm M)"
        hence "l ((enum_class.enum :: 'c list) ! 0) = le_tm M" by simp
        with l_at_0_ne show False by simp
      qed
      have l_not_le: "fst (buf' k) \<noteq> LE_block (le_tm M)"
        using buf_k l_ne_le_fn unfolding LE_block_def by simp
      \<comment> \<open>h-slot: i = c, buf index = c.\<close>
      have lt_c: "?c < 3 * ?c" using c_ge_1 by simp
      have eq_c:
          "mt_tape cM_k k (?p_start + ?c) = buf_lin_at (buf' k) ?c"
        using win_k_steady lt_c
        unfolding ae_window_invariant_def by blast
      have c_not_lt_c: "\<not> ?c < ?c" by simp
      have c_lt_2c: "?c < 2 * ?c" using c_ge_1 by simp
      have buf_at_c:
          "buf_lin_at (buf' k) ?c = h ((enum_class.enum :: 'c list) ! 0)"
        using buf_k c_not_lt_c c_lt_2c
        unfolding buf_lin_at_def Let_def by simp
      have post_at_c: "mt_tape cM_k k (?p_start + ?c) \<noteq> le_tm M"
        using post_no_le_k lt_c by blast
      have h_at_0_ne: "h ((enum_class.enum :: 'c list) ! 0) \<noteq> le_tm M"
        using eq_c buf_at_c post_at_c by simp
      have h_ne_le_fn: "h \<noteq> (\<lambda>_. le_tm M)"
      proof
        assume "h = (\<lambda>_. le_tm M)"
        hence "h ((enum_class.enum :: 'c list) ! 0) = le_tm M" by simp
        with h_at_0_ne show False by simp
      qed
      have h_not_le: "fst (snd (buf' k)) \<noteq> LE_block (le_tm M)"
        using buf_k h_ne_le_fn unfolding LE_block_def by simp
      \<comment> \<open>r-slot: i = 2c, buf index = 2c.\<close>
      have lt_2c: "2 * ?c < 3 * ?c" using c_ge_1 by simp
      have eq_2c:
          "mt_tape cM_k k (?p_start + 2 * ?c) = buf_lin_at (buf' k) (2 * ?c)"
        using win_k_steady lt_2c
        unfolding ae_window_invariant_def by blast
      have not_lt_c2: "\<not> (2 * ?c) < ?c" by simp
      have not_lt_2c2: "\<not> (2 * ?c) < 2 * ?c" by simp
      have buf_at_2c:
          "buf_lin_at (buf' k) (2 * ?c) = r ((enum_class.enum :: 'c list) ! 0)"
        using buf_k not_lt_c2 not_lt_2c2
        unfolding buf_lin_at_def Let_def by simp
      have post_at_2c: "mt_tape cM_k k (?p_start + 2 * ?c) \<noteq> le_tm M"
        using post_no_le_k lt_2c by blast
      have r_at_0_ne: "r ((enum_class.enum :: 'c list) ! 0) \<noteq> le_tm M"
        using eq_2c buf_at_2c post_at_2c by simp
      have r_ne_le_fn: "r \<noteq> (\<lambda>_. le_tm M)"
      proof
        assume "r = (\<lambda>_. le_tm M)"
        hence "r ((enum_class.enum :: 'c list) ! 0) = le_tm M" by simp
        with r_at_0_ne show False by simp
      qed
      have r_not_le: "snd (snd (buf' k)) \<noteq> LE_block (le_tm M)"
        using buf_k r_ne_le_fn unfolding LE_block_def by simp
      show "fst (buf' k) \<noteq> LE_block (le_tm M)
            \<and> fst (snd (buf' k)) \<noteq> LE_block (le_tm M)
            \<and> snd (snd (buf' k)) \<noteq> LE_block (le_tm M)"
        using l_not_le h_not_le r_not_le by blast
    qed
    qed
  qed
  \<comment> \<open>Substep tuple via the arm-uniform construction helper.\<close>
  obtain c'' where
      step_sub:  "(c', c'') \<in> mttm_step (ae_delta_ss4_ss5 M)"
    and step_full: "(c', c'') \<in> mttm_step (alphabet_enlarge_delta M)"
    and c''_state: "mt_state c'' = (q_out,
            \<lambda>k. if k < k_tm M then snd (end_pos k) else init_offset k,
            \<lambda>k. if k < k_tm M then buf' k else init_buffer (le_tm M) k,
            \<lambda>k. if k < k_tm M then fst (end_pos k) else init_dest k, SS5)"
    and c''_tape:  "mt_tape c'' = ts"
    by (rule ae_step_ss4_ss5_construct_from_buffered[OF vM c'_eq q_in nhalt gamma bufv mst_in])
  show thesis
  proof (rule that[where c''=c''])
    show "(c', c'') \<in> mttm_step (ae_delta_ss4_ss5 M)" using step_sub .
    show "(c', c'') \<in> mttm_step (alphabet_enlarge_delta M)" using step_full .
    show "case mt_state c'' of (q_out', _, _, _, _)
            \<Rightarrow> q_out' = mt_state cM_k"
      unfolding c''_state using q_out_eq by simp
    show "case mt_state c'' of (_, _, buf', _, _) \<Rightarrow>
            \<forall>k<k_tm M. (pos k = 0
                    \<longrightarrow> fst (buf' k) \<noteq> LE_block (le_tm M)
                      \<and> snd (snd (buf' k)) \<noteq> LE_block (le_tm M))
                 \<and> (pos k = 1
                      \<longrightarrow> fst (snd (buf' k)) \<noteq> LE_block (le_tm M)
                        \<and> snd (snd (buf' k)) \<noteq> LE_block (le_tm M))
                 \<and> (pos k \<ge> 2
                      \<longrightarrow> fst (buf' k) \<noteq> LE_block (le_tm M)
                        \<and> fst (snd (buf' k)) \<noteq> LE_block (le_tm M)
                        \<and> snd (snd (buf' k)) \<noteq> LE_block (le_tm M))"
      unfolding c''_state using buf_per_tape_not_le by simp
    show "case mt_state c'' of (_, ofs', buf', dest', _) \<Rightarrow>
            \<forall>k<k_tm M. ae_window_invariant_general
                  (mt_tape cM_k k) (mt_pos cM_k k)
                  (dest' k, ofs' k) (buf' k) (pos k) (le_tm M)"
      unfolding c''_state using new_window by simp
  qed
qed


subsubsection \<open>Buffer characterisations at SS4 entry\<close>

text \<open>Per-tape unified variant of the SS4-entry buffer
  characterisation, threading per-tape regime via the
  \<open>home_class\<close> hypothesis (parallel to the
  \<open>home_classification\<close> fact established in the body of
  \<open>ae_simulates_forward_stage_general\<close>).  Each tape's
  home-cell content classifies it as either an LE-arm tape
  (\<open>mt_pos c' k = 0\<close>, home = \<open>LE_block\<close>) or a
  steady-arm tape (\<open>mt_pos c' k \<ge> 1\<close>, home
  \<open>\<noteq> LE_block\<close>); per-tape dispatch is needed because
  the \<open>forward_stage_general\<close> caller doesn't guarantee
  uniform regime across tapes.

  Position closed-forms remain uniform thanks to \<open>nat\<close>
  arithmetic: \<open>pos_c1 = n - 1\<close>, \<open>pos_c2 = n\<close>,
  \<open>pos_c3 = n + 1\<close>.  Each holds in both regimes because in
  the LE arm \<open>n = 0\<close>, so \<open>0 - 1 = 0\<close>,
  \<open>go_dir N 0 = 0\<close>, etc., agree with the steady-arm
  formulae evaluated at \<open>n = 0\<close>.

  The SS4-entry buffer is per-tape: tapes at \<open>pos = 0\<close>
  get \<open>(bl_block, LE_block, snd (snd (buf k)))\<close>; tapes at
  \<open>pos \<ge> 1\<close> get
  \<open>(mt_tape c' k (pos - 1), mt_tape c' k pos,
   snd (snd (buf k)))\<close>.\<close>

lemma ae_ss1_to_ss4_buffer_chars_general:
  fixes M :: "('q, 'a) mttm"
    and c' c1 c2 c3 :: "('c :: enum \<Rightarrow> 'a,
                          'q \<times> ('a, 'c) ae_stage) mt_config"
    and qM' :: 'q
    and ofs :: "nat \<Rightarrow> 'c"
    and buf :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest :: "nat \<Rightarrow> ae_dest"
  assumes c'_state:    "mt_state c' = (qM', ofs, buf, dest, SS1)"
      and step12:      "(c', c1) \<in> mttm_step (ae_delta_ss1_ss2 M)"
      and step23:      "(c1, c2) \<in> mttm_step (ae_delta_ss2_ss3 M)"
      and step34:      "(c2, c3) \<in> mttm_step (ae_delta_ss3_ss4 M)"
      and home_class:
            "\<forall>k<k_tm M. (mt_pos c' k = 0
                     \<longrightarrow> mt_tape c' k (mt_pos c' k) = LE_block (le_tm M))
                  \<and> (mt_pos c' k \<ge> 1
                     \<longrightarrow> mt_tape c' k (mt_pos c' k) \<noteq> LE_block (le_tm M))"
  shows "mt_state c3
          = (qM', ofs,
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
    and "mt_tape c3 = mt_tape c'"
    and "\<And>k. k < k_tm M \<Longrightarrow> mt_pos c3 k = mt_pos c' k + 1"
proof -
  \<comment> \<open>Destructure \<open>c'\<close>; introduce \<open>?a\<close> for the home read.\<close>
  obtain ts n where c'_eq:
      "c' = Config\<^sub>M (qM', ofs, buf, dest, SS1) ts n"
    using c'_state by (cases c') auto
  let ?a = "\<lambda>k :: nat. ts k (n k)"

  \<comment> \<open>Per-tape regime equivalence \<open>?a k = LE_block \<longleftrightarrow> n k = 0\<close>
      on active tapes (\<open>k < k_tm M\<close>); past tape count the value-level
      builders freeze every per-tape field, so no regime fact is
      needed there.\<close>
  have a_le_iff: "\<And>k. k < k_tm M
                       \<Longrightarrow> (?a k = LE_block (le_tm M)) \<longleftrightarrow> n k = 0"
  proof -
    fix k assume klt: "k < k_tm M"
    have a_eq: "?a k = mt_tape c' k (mt_pos c' k)" using c'_eq by simp
    have pos_eq: "mt_pos c' k = n k" using c'_eq by simp
    show "(?a k = LE_block (le_tm M)) \<longleftrightarrow> n k = 0"
    proof
      assume H: "?a k = LE_block (le_tm M)"
      show "n k = 0"
      proof (rule ccontr)
        assume "n k \<noteq> 0"
        hence "mt_pos c' k \<ge> 1" using pos_eq by simp
        hence "mt_tape c' k (mt_pos c' k) \<noteq> LE_block (le_tm M)"
          using home_class klt by blast
        thus False using H a_eq by simp
      qed
    next
      assume "n k = 0"
      hence "mt_pos c' k = 0" using pos_eq by simp
      hence "mt_tape c' k (mt_pos c' k) = LE_block (le_tm M)"
        using home_class klt by blast
      thus "?a k = LE_block (le_tm M)" using a_eq by simp
    qed
  qed

  \<comment> \<open>SS1\<open>\<rightarrow>\<close>SS2 unfolding.  The value-level builder guards
      every per-tape field: on active tapes (\<open>k < k_tm M\<close>) the
      buffer takes the home read and the head moves \<open>L\<close>
      (steady) or \<open>N\<close> (LE-stage, \<open>n k = 0\<close>); past tape count the
      buffer freezes to \<open>init_buffer (le_tm M)\<close> and the head
      does not move (direction \<open>N\<close>).\<close>
  let ?buf1 = "\<lambda>k. if k < k_tm M
                     then (fst (buf k), ?a k, snd (snd (buf k)))
                     else init_buffer (le_tm M) k"
  let ?n1 = "\<lambda>k :: nat. if k < k_tm M then n k - 1 else n k"
  have c1_struct:
      "c1 = Config\<^sub>M (qM', ofs, ?buf1, dest, SS2) ts ?n1"
  proof -
    from step12 c'_eq obtain a buf' d where
        in_delta: "((qM', ofs, buf, dest, SS1), a,
                    (qM', ofs, buf', dest, SS2), a, d)
                       \<in> ae_delta_ss1_ss2 M"
      and a_eq: "a = ?a"
      and c1_eq: "c1 = Config\<^sub>M (qM', ofs, buf', dest, SS2)
                          (\<lambda>k. (ts k)(n k := a k))
                          (\<lambda>k. go_dir (d k) (n k))"
      by (auto elim!: mttm_step.cases simp: ae_delta_ss1_ss2_def)
    have buf'_eq: "buf' = ?buf1"
      using in_delta a_eq unfolding ae_delta_ss1_ss2_def by auto
    have d_eq: "\<And>k. d k = (if k < k_tm M
                              then (if a k = LE_block (le_tm M)
                                      then dir.N else dir.L)
                              else dir.N)"
      using in_delta unfolding ae_delta_ss1_ss2_def by auto
    have ts_unchanged: "\<And>k. (ts k)(n k := a k) = ts k"
      using a_eq by (intro ext) auto
    have pos_uniform: "\<And>k. go_dir (d k) (n k)
                            = (if k < k_tm M then n k - 1 else n k)"
    proof -
      fix k
      show "go_dir (d k) (n k) = (if k < k_tm M then n k - 1 else n k)"
      proof (cases "k < k_tm M")
        case True
        hence dk: "d k = (if a k = LE_block (le_tm M)
                            then dir.N else dir.L)"
          using d_eq by simp
        consider (le) "a k = LE_block (le_tm M)"
               | (nle) "a k \<noteq> LE_block (le_tm M)" by blast
        thus ?thesis
        proof cases
          case le
          hence "d k = dir.N" using dk by simp
          moreover have "n k = 0" using a_le_iff[OF True] le a_eq by simp
          ultimately show ?thesis using True by simp
        next
          case nle
          hence "d k = dir.L" using dk by simp
          thus ?thesis using True by simp
        qed
      next
        case False
        hence "d k = dir.N" using d_eq by simp
        thus ?thesis using False by simp
      qed
    qed
    have pos_fun: "(\<lambda>k. go_dir (d k) (n k)) = ?n1"
      using pos_uniform by (intro ext) auto
    have tape_fun: "(\<lambda>k. (ts k)(n k := a k)) = ts"
      using ts_unchanged by (intro ext) auto
    show ?thesis
      using c1_eq buf'_eq pos_fun tape_fun by simp
  qed

  \<comment> \<open>SS2\<open>\<rightarrow>\<close>SS3 unfolding.  On active tapes the buffer becomes
      \<open>?buf2\<close>: home slot stays \<open>?a k\<close>; left slot is
      \<open>bl_block\<close> in the LE arm or \<open>ts k (n k - 1)\<close> in the
      steady arm.  Position returns to \<open>n k\<close> in every regime
      (incl. past tape count, where the head never left).\<close>
  let ?a' = "\<lambda>k :: nat. ts k (n k - 1)"
  let ?buf2 = "\<lambda>k. if k < k_tm M
                     then (if ?a k = LE_block (le_tm M)
                              then bl_block (bl_tm M)
                              else ?a' k,
                           ?a k,
                           snd (snd (buf k)))
                     else init_buffer (le_tm M) k"
  let ?n2 = "\<lambda>k :: nat. n k"
  have c2_struct:
      "c2 = Config\<^sub>M (qM', ofs, ?buf2, dest, SS3) ts ?n2"
  proof -
    from step23 c1_struct obtain a2 buf'' d' where
        in_delta2: "((qM', ofs, ?buf1, dest, SS2), a2,
                     (qM', ofs, buf'', dest, SS3), a2, d')
                        \<in> ae_delta_ss2_ss3 M"
      and a2_eq: "a2 = (\<lambda>k. ts k (?n1 k))"
      and c2_eq: "c2 = Config\<^sub>M (qM', ofs, buf'', dest, SS3)
                          (\<lambda>k. (ts k)(?n1 k := a2 k))
                          (\<lambda>k. go_dir (d' k) (?n1 k))"
      by (auto elim!: mttm_step.cases simp: ae_delta_ss2_ss3_def)
    have buf''_eq:
        "buf'' = (\<lambda>k. if k < k_tm M
                       then (let (l, h, r) = ?buf1 k in
                              (if h = LE_block (le_tm M)
                                  then bl_block (bl_tm M) else a2 k,
                               h, r))
                       else init_buffer (le_tm M) k)"
      and d'_eq: "\<And>k. d' k = (if k < k_tm M
                                then (if fst (snd (?buf1 k)) = LE_block (le_tm M)
                                       then dir.N else dir.R)
                                else dir.N)"
      using in_delta2 unfolding ae_delta_ss2_ss3_def by auto
    have h_buf1: "\<And>k. k < k_tm M \<Longrightarrow> fst (snd (?buf1 k)) = ?a k"
      by simp
    have buf''_simp: "buf'' = ?buf2"
    proof (intro ext)
      fix k
      show "buf'' k = ?buf2 k"
      proof (cases "k < k_tm M")
        case True
        have a2k: "a2 k = ?a' k" using a2_eq True by simp
        have b1: "?buf1 k = (fst (buf k), ?a k, snd (snd (buf k)))"
          using True by simp
        have "buf'' k = (let (l, h, r) = ?buf1 k in
                          (if h = LE_block (le_tm M)
                              then bl_block (bl_tm M) else a2 k, h, r))"
          using buf''_eq True by simp
        also have "\<dots> = (if ?a k = LE_block (le_tm M)
                            then bl_block (bl_tm M) else a2 k,
                         ?a k, snd (snd (buf k)))"
          using b1 by (simp add: case_prod_beta')
        also have "\<dots> = ?buf2 k" using True a2k by simp
        finally show ?thesis .
      next
        case False
        have "buf'' k = init_buffer (le_tm M) k"
          using buf''_eq False by simp
        also have "\<dots> = ?buf2 k" using False by simp
        finally show ?thesis .
      qed
    qed
    have ts_unchanged2: "\<And>k. (ts k)(?n1 k := a2 k) = ts k"
      using a2_eq by (intro ext) auto
    have pos_uniform2: "\<And>k. go_dir (d' k) (?n1 k) = n k"
    proof -
      fix k
      show "go_dir (d' k) (?n1 k) = n k"
      proof (cases "k < k_tm M")
        case True
        hence d'k: "d' k = (if ?a k = LE_block (le_tm M)
                              then dir.N else dir.R)"
          using d'_eq h_buf1[OF True] by simp
        consider (le) "?a k = LE_block (le_tm M)"
               | (nle) "?a k \<noteq> LE_block (le_tm M)" by blast
        thus ?thesis
        proof cases
          case le
          hence "d' k = dir.N" using d'k by simp
          moreover have "n k = 0" using a_le_iff[OF True] le by simp
          ultimately show ?thesis using True by simp
        next
          case nle
          hence "d' k = dir.R" using d'k by simp
          moreover have "n k \<ge> 1" using a_le_iff[OF True] nle by simp
          ultimately show ?thesis using True by simp
        qed
      next
        case False
        hence "d' k = dir.N" using d'_eq by simp
        thus ?thesis using False by simp
      qed
    qed
    have pos_fun2: "(\<lambda>k. go_dir (d' k) (?n1 k)) = ?n2"
      using pos_uniform2 by (intro ext) auto
    have tape_fun2: "(\<lambda>k. (ts k)(?n1 k := a2 k)) = ts"
      using ts_unchanged2 by (intro ext) auto
    show ?thesis
      using c2_eq buf''_simp pos_fun2 tape_fun2 by simp
  qed
  have c2_state: "mt_state c2 = (qM', ofs, ?buf2, dest, SS3)"
    using c2_struct by simp
  have c2_tape: "mt_tape c2 = ts" using c2_struct by simp
  have c2_pos: "\<And>k. mt_pos c2 k = n k" using c2_struct by simp

  \<comment> \<open>SS3\<open>\<rightarrow>\<close>SS4: active tapes move \<open>R\<close> (\<open>n k + 1\<close>),
      inactive tapes are frozen (\<open>N\<close>); no buffer update.\<close>
  let ?n3 = "\<lambda>k :: nat. if k < k_tm M then n k + 1 else n k"
  have c3_struct:
      "c3 = Config\<^sub>M (qM', ofs, ?buf2, dest, SS4) ts ?n3"
    using step34 c2_state c2_tape c2_pos
    by (auto simp: ae_delta_ss3_ss4_def
             elim!: mttm_step.cases
             intro!: ext mt_config.expand
             split: if_splits)

  \<comment> \<open>Re-express the SS4-entry buffer on the \<open>c'\<close>-side
      (guarded: active tapes carry the regime-split triple, past
      tape count the frozen \<open>init_buffer\<close>).\<close>
  have tape_c'_at: "\<And>k. mt_tape c' k = ts k" using c'_eq by simp
  have pos_c'_at:  "\<And>k. mt_pos c' k = n k" using c'_eq by simp
  have buf2_to_concl: "?buf2 =
      (\<lambda>k. if k < k_tm M
              then (if mt_pos c' k = 0
                      then (bl_block (bl_tm M),
                            LE_block (le_tm M),
                            snd (snd (buf k)))
                      else (mt_tape c' k (mt_pos c' k - 1),
                            mt_tape c' k (mt_pos c' k),
                            snd (snd (buf k))))
              else init_buffer (le_tm M) k)"
  proof (intro ext)
    fix k
    show "?buf2 k
            = (if k < k_tm M
                  then (if mt_pos c' k = 0
                          then (bl_block (bl_tm M),
                                LE_block (le_tm M),
                                snd (snd (buf k)))
                          else (mt_tape c' k (mt_pos c' k - 1),
                                mt_tape c' k (mt_pos c' k),
                                snd (snd (buf k))))
                  else init_buffer (le_tm M) k)"
    proof (cases "k < k_tm M")
      case True
      consider (le) "?a k = LE_block (le_tm M)"
             | (nle) "?a k \<noteq> LE_block (le_tm M)" by blast
      thus ?thesis
      proof cases
        case le
        have n0: "n k = 0" using a_le_iff[OF True] le by simp
        have pos0: "mt_pos c' k = 0" using pos_c'_at n0 by simp
        have lhs: "?buf2 k = (bl_block (bl_tm M), ?a k, snd (snd (buf k)))"
          using le True by simp
        have a_is_le: "?a k = LE_block (le_tm M)" using le .
        show ?thesis using lhs pos0 a_is_le True by simp
      next
        case nle
        have npos: "n k \<ge> 1" using a_le_iff[OF True] nle by simp
        have pos_ge1: "mt_pos c' k \<ge> 1" using pos_c'_at npos by simp
        have pos_ne0: "mt_pos c' k \<noteq> 0" using pos_ge1 by simp
        have a'_tape: "?a' k = mt_tape c' k (mt_pos c' k - 1)"
          using tape_c'_at pos_c'_at by simp
        have a_tape: "?a k = mt_tape c' k (mt_pos c' k)"
          using tape_c'_at pos_c'_at by simp
        have lhs: "?buf2 k = (?a' k, ?a k, snd (snd (buf k)))"
          using nle True by simp
        show ?thesis using lhs pos_ne0 a'_tape a_tape True by simp
      qed
    next
      case False
      thus ?thesis by simp
    qed
  qed

  show "mt_state c3
          = (qM', ofs,
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
    using c3_struct buf2_to_concl by simp
  show "mt_tape c3 = mt_tape c'"
    using c3_struct c'_eq by simp
  show "\<And>k. k < k_tm M \<Longrightarrow> mt_pos c3 k = mt_pos c' k + 1"
  proof -
    fix k assume klt: "k < k_tm M"
    have "mt_pos c3 k = (if k < k_tm M then n k + 1 else n k)"
      using c3_struct by simp
    thus "mt_pos c3 k = mt_pos c' k + 1"
      using klt pos_c'_at by simp
  qed
qed


text \<open>Per-tape unified window-from-correspondence helper.
  Establishes the per-tape \<open>ae_window_invariant_general\<close>
  from the \<open>forward_stage_general\<close> precondition shapes:
  simulation invariant (for \<open>tape_corr\<close> and \<open>pos_corr\<close>),
  LE-anchor (for tape cell 0 = LE), and the three-prong
  \<open>no_le_per_tape\<close> hypothesis (per-tape, per-regime non-LE
  guarantees on the M-window).  The buffer triple is the SS4-entry
  per-tape buffer with the right slot replaced by the freshly-read
  block at \<open>mt_pos c' k + 1\<close> — matching the buffer
  shape that \<open>ae_delta_ss4_ss5\<close> feeds into
  \<open>m_step_buffered\<close>.

  The proof case-splits per-tape on \<open>mt_pos c' k\<close>'s regime
  (\<open>0\<close> / \<open>1\<close> / \<open>\<ge> 2\<close>) and dispatches each
  branch to the corresponding existing per-arm helper's conclusion
  shape.\<close>

lemma ae_ss4_window_from_correspondence_general:
  fixes M :: "('q, 'a) mttm"
    and cM :: "('a, 'q) mt_config"
    and c' :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) mt_config"
    and qM' :: 'q
    and ofs :: "nat \<Rightarrow> 'c"
    and buf :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest :: "nat \<Rightarrow> ae_dest"
  assumes sim:         "ae_simulates M cM c'"
      and c'_state:    "mt_state c' = (qM', ofs, buf, dest, SS1)"
      and le_anchor:   "\<forall>k<k_tm M. mt_tape c' k 0 = LE_block (le_tm M)"
      and no_le_per_tape:
            "\<forall>k. (mt_pos c' k \<ge> 2
                    \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                              \<longrightarrow> mt_tape cM k
                                    ((mt_pos c' k - 2)
                                       * card (UNIV :: 'c set) + 1 + i)
                                  \<noteq> le_tm M))
                 \<and> (mt_pos c' k = 1
                      \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                                \<longrightarrow> mt_tape cM k (Suc i) \<noteq> le_tm M))
                 \<and> (mt_pos c' k = 0
                      \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                                \<longrightarrow> mt_tape cM k (Suc i) \<noteq> le_tm M))"
  shows "\<forall>k<k_tm M. ae_window_invariant_general
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
proof -
  let ?c = "card (UNIV :: 'c set)"
  let ?enum_c = "enum_class.enum :: 'c list"
  have c_eq_len: "?c = length ?enum_c"
    using enum_class.UNIV_enum enum_class.enum_distinct
    by (metis distinct_card length_remdups_card_conv set_remdups)

  \<comment> \<open>Extract the simulation invariant's tape-correspondence
      and position-decoding facts uniformly; both will be projected
      per-tape inside each regime branch.\<close>
  have tape_corr: "\<forall>k<k_tm M. ae_tape_correspondence (le_tm M)
                          (mt_tape cM k) (mt_tape c' k)"
    using sim c'_state unfolding ae_simulates_def by auto
  have pos_corr: "\<forall>k<k_tm M. mt_pos cM k
                          = ae_decode_pos (mt_pos c' k) (ofs k)"
    using sim c'_state unfolding ae_simulates_def by auto

  show ?thesis
  proof (intro allI impI)
    fix k
    assume k_lt: "k < k_tm M"
    have tape_corr_k: "ae_tape_correspondence (le_tm M)
                          (mt_tape cM k) (mt_tape c' k)"
      using tape_corr k_lt by blast
    have pos_corr_k: "mt_pos cM k
                        = ae_decode_pos (mt_pos c' k) (ofs k)"
      using pos_corr k_lt by simp
    have anchor_k: "mt_tape c' k 0 = LE_block (le_tm M)"
      using le_anchor k_lt by blast
    have cM_zero: "mt_tape cM k 0 = le_tm M"
      using tape_corr_k unfolding ae_tape_correspondence_def by simp
    have tc_app: "\<And>s' i'. s' \<ge> 1
                \<Longrightarrow> mt_tape cM k ((s' - 1) * ?c + c_idx i' + 1)
                    = mt_tape c' k s' i'"
      using tape_corr_k unfolding ae_tape_correspondence_def by simp

    consider (le0) "mt_pos c' k = 0"
           | (le1) "mt_pos c' k = 1"
           | (steady) "mt_pos c' k \<ge> 2"
      by linarith
    thus "ae_window_invariant_general
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
    proof cases
      case le0
      have decode_k: "mt_pos cM k = 0"
      proof -
        have "ae_decode_pos 0 (ofs k) = 0"
          unfolding ae_decode_pos_def by simp
        thus ?thesis using pos_corr_k le0 by simp
      qed
      have part_1: "fst (snd (bl_block (bl_tm M),
                                LE_block (le_tm M),
                                mt_tape c' k 1))
                      = LE_block (le_tm M)"
        by simp
      have part_2: "mt_tape cM k 0 = le_tm M" by (rule cM_zero)
      have part_3:
          "(case fst (AE_Home, ofs k) of
              AE_Home  \<Rightarrow> mt_pos cM k = 0
            | AE_Right \<Rightarrow> mt_pos cM k
                            = Suc (c_idx (snd (AE_Home, ofs k)))
            | AE_Left  \<Rightarrow> False)"
        using decode_k by simp
      have part_4: "\<forall>i. i < ?c
                        \<longrightarrow> mt_tape cM k (Suc i)
                            = buf_lin_at
                                (bl_block (bl_tm M),
                                 LE_block (le_tm M),
                                 mt_tape c' k 1) (2 * ?c + i)"
      proof (intro allI impI)
        fix i :: nat
        assume i_lt: "i < ?c"
        let ?x = "?enum_c ! i"
        have i_lt_len: "i < length ?enum_c" using i_lt c_eq_len by simp
        have cidx_x: "c_idx ?x = i" using c_idx_enum_nth[OF i_lt_len] .
        have addr_eq: "Suc i = (1 - 1) * ?c + c_idx ?x + 1"
          using cidx_x by simp
        have one_ge1: "(1 :: nat) \<ge> 1" by simp
        have "mt_tape cM k (Suc i) = mt_tape c' k 1 ?x"
          using tc_app[OF one_ge1, of ?x] addr_eq by simp
        also have "... = buf_lin_at
                          (bl_block (bl_tm M),
                           LE_block (le_tm M),
                           mt_tape c' k 1) (2 * ?c + i)"
          using i_lt by (simp add: buf_lin_at_def Let_def)
        finally show "mt_tape cM k (Suc i)
                        = buf_lin_at
                            (bl_block (bl_tm M),
                             LE_block (le_tm M),
                             mt_tape c' k 1) (2 * ?c + i)" .
      qed
      have inv_le0:
          "ae_window_invariant_le0 (mt_tape cM k) (mt_pos cM k)
              (AE_Home, ofs k)
              (bl_block (bl_tm M),
               LE_block (le_tm M),
               mt_tape c' k 1)
              (le_tm M)"
        unfolding ae_window_invariant_le0_def
        using part_1 part_2 part_3 part_4 by blast
      show ?thesis
        unfolding ae_window_invariant_general_def
        using inv_le0 le0 by simp
    next
      case le1
      have decode_k: "mt_pos cM k = Suc (c_idx (ofs k))"
      proof -
        have step: "ae_decode_pos 1 (ofs k)
                      = (1 - 1) * ?c + c_idx (ofs k) + 1"
          unfolding ae_decode_pos_def by simp
        hence "ae_decode_pos 1 (ofs k) = Suc (c_idx (ofs k))" by simp
        thus ?thesis using pos_corr_k le1 by simp
      qed
      have part_1: "fst (mt_tape c' k 0, mt_tape c' k 1, mt_tape c' k 2)
                      = LE_block (le_tm M)"
        using anchor_k by simp
      have part_2: "mt_tape cM k 0 = le_tm M" by (rule cM_zero)
      have part_3:
          "(case fst (AE_Home, ofs k) of
              AE_Left  \<Rightarrow> snd (AE_Home, ofs k) = c_last
                           \<and> mt_pos cM k = 0
            | AE_Home  \<Rightarrow> mt_pos cM k
                            = Suc (c_idx (snd (AE_Home, ofs k)))
            | AE_Right \<Rightarrow> mt_pos cM k
                            = Suc (?c + c_idx (snd (AE_Home, ofs k))))"
        using decode_k by simp
      have part_4: "\<forall>i. i < 2 * ?c
                        \<longrightarrow> mt_tape cM k (Suc i)
                            = buf_lin_at
                                (mt_tape c' k 0,
                                 mt_tape c' k 1,
                                 mt_tape c' k 2) (?c + i)"
      proof (intro allI impI)
        fix i :: nat
        assume i_lt: "i < 2 * ?c"
        consider (H) "i < ?c" | (R) "?c \<le> i \<and> i < 2 * ?c"
          using i_lt by linarith
        thus "mt_tape cM k (Suc i)
                = buf_lin_at
                    (mt_tape c' k 0,
                     mt_tape c' k 1,
                     mt_tape c' k 2) (?c + i)"
        proof cases
          case H
          let ?x = "?enum_c ! i"
          have i_lt_len: "i < length ?enum_c" using H c_eq_len by simp
          have cidx_x: "c_idx ?x = i" using c_idx_enum_nth[OF i_lt_len] .
          have addr_eq: "Suc i = (1 - 1) * ?c + c_idx ?x + 1"
            using cidx_x by simp
          have one_ge1: "(1 :: nat) \<ge> 1" by simp
          have "mt_tape cM k (Suc i) = mt_tape c' k 1 ?x"
            using tc_app[OF one_ge1, of ?x] addr_eq by simp
          also have "... = buf_lin_at
                            (mt_tape c' k 0,
                             mt_tape c' k 1,
                             mt_tape c' k 2) (?c + i)"
            using H by (simp add: buf_lin_at_def Let_def)
          finally show ?thesis .
        next
          case R
          let ?x = "?enum_c ! (i - ?c)"
          have im_lt: "i - ?c < ?c" using R by linarith
          have im_lt_len: "i - ?c < length ?enum_c"
            using im_lt c_eq_len by simp
          have cidx_x: "c_idx ?x = i - ?c"
            using c_idx_enum_nth[OF im_lt_len] .
          have shift: "Suc i = (2 - 1) * ?c + (i - ?c) + 1"
            using R by simp
          have addr_eq: "Suc i = (2 - 1) * ?c + c_idx ?x + 1"
            using shift cidx_x by simp
          have two_ge1: "(2 :: nat) \<ge> 1" by simp
          have "mt_tape cM k (Suc i) = mt_tape c' k 2 ?x"
            using tc_app[OF two_ge1, of ?x] addr_eq by simp
          also have "... = buf_lin_at
                            (mt_tape c' k 0,
                             mt_tape c' k 1,
                             mt_tape c' k 2) (?c + i)"
            using R by (simp add: buf_lin_at_def Let_def)
          finally show ?thesis .
        qed
      qed
      have inv_le1:
          "ae_window_invariant_le1 (mt_tape cM k) (mt_pos cM k)
              (AE_Home, ofs k)
              (mt_tape c' k 0,
               mt_tape c' k 1,
               mt_tape c' k 2)
              (le_tm M)"
        unfolding ae_window_invariant_le1_def
        using part_1 part_2 part_3 part_4 by blast
      show ?thesis
        unfolding ae_window_invariant_general_def
        using inv_le1 le1 by simp
    next
      case steady
      let ?p_start = "(mt_pos c' k - 2) * ?c + 1"
      have s_ge2: "mt_pos c' k \<ge> 2" using steady .
      have s_ge1: "mt_pos c' k \<ge> 1" using s_ge2 by simp
      have decode_k: "mt_pos cM k
                        = (mt_pos c' k - 1) * ?c + c_idx (ofs k) + 1"
      proof -
        have "mt_pos c' k \<noteq> 0" using s_ge1 by simp
        thus ?thesis
          using pos_corr_k unfolding ae_decode_pos_def by simp
      qed
      have part_a: "?p_start \<ge> 1" by simp
      have part_b: "mt_pos cM k = ?p_start + bp_linear (AE_Home, ofs k)"
      proof -
        have bp: "bp_linear (AE_Home, ofs k) = ?c + c_idx (ofs k)"
          unfolding bp_linear_def by simp
        have step_sub: "(mt_pos c' k - 2) + 1 = mt_pos c' k - 1"
          using s_ge2 by arith
        have "?p_start + bp_linear (AE_Home, ofs k)
                = (mt_pos c' k - 2) * ?c + 1 + (?c + c_idx (ofs k))"
          using bp by simp
        also have "... = (mt_pos c' k - 2) * ?c + ?c
                          + c_idx (ofs k) + 1"
          by simp
        also have "... = ((mt_pos c' k - 2) + 1) * ?c
                          + c_idx (ofs k) + 1"
          by (simp add: algebra_simps)
        also have "... = (mt_pos c' k - 1) * ?c + c_idx (ofs k) + 1"
          using step_sub by simp
        also have "... = mt_pos cM k" using decode_k by simp
        finally show ?thesis by simp
      qed
      have part_c: "\<forall>i. i < 3 * ?c
                        \<longrightarrow> mt_tape cM k (?p_start + i)
                            = buf_lin_at
                                (mt_tape c' k (mt_pos c' k - 1),
                                 mt_tape c' k (mt_pos c' k),
                                 mt_tape c' k (mt_pos c' k + 1)) i"
      proof (intro allI impI)
        fix i :: nat
        assume i_lt: "i < 3 * ?c"
        consider (L) "i < ?c" | (H) "?c \<le> i \<and> i < 2 * ?c"
                                | (R) "2 * ?c \<le> i \<and> i < 3 * ?c"
          using i_lt by linarith
        thus "mt_tape cM k (?p_start + i)
                = buf_lin_at
                    (mt_tape c' k (mt_pos c' k - 1),
                     mt_tape c' k (mt_pos c' k),
                     mt_tape c' k (mt_pos c' k + 1)) i"
        proof cases
          case L
          let ?x = "?enum_c ! i"
          have i_lt_len: "i < length ?enum_c" using L c_eq_len by simp
          have cidx_x: "c_idx ?x = i" using c_idx_enum_nth[OF i_lt_len] .
          have sub_lhs: "(mt_pos c' k - 1) - 1 = mt_pos c' k - 2"
            using s_ge2 by arith
          have addr_eq: "?p_start + i
                            = ((mt_pos c' k - 1) - 1) * ?c
                              + c_idx ?x + 1"
            using cidx_x sub_lhs by simp
          have s_minus_1_ge1: "mt_pos c' k - 1 \<ge> 1" using s_ge2 by arith
          have "mt_tape cM k (?p_start + i)
                  = mt_tape c' k (mt_pos c' k - 1) ?x"
            using tc_app[OF s_minus_1_ge1, of ?x] addr_eq by simp
          also have "... = buf_lin_at
                            (mt_tape c' k (mt_pos c' k - 1),
                             mt_tape c' k (mt_pos c' k),
                             mt_tape c' k (mt_pos c' k + 1)) i"
            using L by (simp add: buf_lin_at_def Let_def)
          finally show ?thesis .
        next
          case H
          let ?x = "?enum_c ! (i - ?c)"
          have im_lt: "i - ?c < ?c" using H by linarith
          have im_lt_len: "i - ?c < length ?enum_c"
            using im_lt c_eq_len by simp
          have cidx_x: "c_idx ?x = i - ?c"
            using c_idx_enum_nth[OF im_lt_len] .
          have shift: "(mt_pos c' k - 2) * ?c + 1 + i
                         = (mt_pos c' k - 1) * ?c + (i - ?c) + 1"
          proof -
            have "(mt_pos c' k - 1) * ?c
                    = (mt_pos c' k - 2) * ?c + ?c"
              using s_ge2 by (simp add: algebra_simps)
            thus ?thesis using H by simp
          qed
          have addr_eq: "?p_start + i
                            = (mt_pos c' k - 1) * ?c + c_idx ?x + 1"
            using shift cidx_x by simp
          have "mt_tape cM k (?p_start + i)
                  = mt_tape c' k (mt_pos c' k) ?x"
            using tc_app[OF s_ge1, of ?x] addr_eq by simp
          also have "... = buf_lin_at
                            (mt_tape c' k (mt_pos c' k - 1),
                             mt_tape c' k (mt_pos c' k),
                             mt_tape c' k (mt_pos c' k + 1)) i"
            using H by (simp add: buf_lin_at_def Let_def)
          finally show ?thesis .
        next
          case R
          let ?x = "?enum_c ! (i - 2 * ?c)"
          have ir_lt: "i - 2 * ?c < ?c" using R by linarith
          have ir_lt_len: "i - 2 * ?c < length ?enum_c"
            using ir_lt c_eq_len by simp
          have cidx_x: "c_idx ?x = i - 2 * ?c"
            using c_idx_enum_nth[OF ir_lt_len] .
          have shift: "(mt_pos c' k - 2) * ?c + 1 + i
                         = mt_pos c' k * ?c + (i - 2 * ?c) + 1"
          proof -
            have "mt_pos c' k * ?c
                    = (mt_pos c' k - 2) * ?c + 2 * ?c"
              using s_ge2 by (simp add: algebra_simps)
            thus ?thesis using R by simp
          qed
          have splus_minus: "(mt_pos c' k + 1) - 1 = mt_pos c' k"
            by simp
          have addr_eq: "?p_start + i
                            = ((mt_pos c' k + 1) - 1) * ?c
                              + c_idx ?x + 1"
            using shift cidx_x splus_minus by simp
          have splus_ge1: "mt_pos c' k + 1 \<ge> 1" by simp
          have "mt_tape cM k (?p_start + i)
                  = mt_tape c' k (mt_pos c' k + 1) ?x"
            using tc_app[OF splus_ge1, of ?x] addr_eq by simp
          also have "... = buf_lin_at
                            (mt_tape c' k (mt_pos c' k - 1),
                             mt_tape c' k (mt_pos c' k),
                             mt_tape c' k (mt_pos c' k + 1)) i"
            using R by (simp add: buf_lin_at_def Let_def)
          finally show ?thesis .
        qed
      qed
      have inv_steady:
          "ae_window_invariant (mt_tape cM k) (mt_pos cM k)
              (AE_Home, ofs k)
              (mt_tape c' k (mt_pos c' k - 1),
               mt_tape c' k (mt_pos c' k),
               mt_tape c' k (mt_pos c' k + 1))
              ?p_start"
        unfolding ae_window_invariant_def
        using part_a part_b part_c by blast
      show ?thesis
        unfolding ae_window_invariant_general_def
        using inv_steady steady by simp
    qed
  qed
qed

end
