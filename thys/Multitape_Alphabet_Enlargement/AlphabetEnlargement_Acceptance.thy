theory AlphabetEnlargement_Acceptance
  imports AlphabetEnlargement_ForwardStage
begin

subsection \<open>Halting correspondence and step counts\<close>

subsubsection \<open>Halting correspondence and initial setup\<close>

text \<open>Halting correspondence: when \<open>M\<close> is in a halting state \<open>q\<close> (accept
  or reject), \<open>M'\<close> is in the canonical halt config
  \<open>(q, init_stage le_M)\<close>.  Direct from \<open>ae_simulates_def\<close>'s halt-arm
  disjunct, which pins down \<open>(off, buf, dest, idx) = init_stage le_M\<close>
  exactly when \<open>qM' \<in> {t_ktm M, r_ktm M}\<close>, plus the
  \<open>q\<close>-correspondence conjunct.  Stated for either halting state, so that
  the step-count engine below transports rejecting runs as well as
  accepting ones.\<close>

lemma ae_simulates_terminal_state:
  assumes sim: "ae_simulates M c d"
      and terminal: "q \<in> {t_ktm M, r_ktm M}"
      and state: "ktc_state c = q"
  shows "ktc_state d = (q, init_stage (le_ktm M))"
proof -
  obtain p off buf dest idx where shape:
    "ktc_state d = (p, off, buf, dest, idx)" by (cases "ktc_state d")
  have paired: "ktc_state c = p" and phase:
    "(idx = SS1 \<and> p \<notin> {t_ktm M, r_ktm M}) \<or>
      (p \<in> {t_ktm M, r_ktm M} \<and> (off, buf, dest, idx) = init_stage (le_ktm M))"
    using sim unfolding ae_simulates_def Let_def shape by simp_all
  have p: "p = q" using paired state by simp
  have canonical: "(off, buf, dest, idx) = init_stage (le_ktm M)"
    using phase terminal p by blast
  show ?thesis using shape p canonical by simp
qed

subsubsection \<open>Step counts, and the induction over simulated stages\<close>

text \<open>Step-counting lemmas: the simulation phase is bounded by
  \<open>8 \<cdot> \<lceil>T(c \<cdot> n) / c\<rceil>\<close>.  The validation phase's bound,
  \<open>2 \<cdot> n + f\<^sub>v\<close>, is \<open>ae_validation_steps_bound\<close> of theory
  \<open>AlphabetEnlargement_ValidationBound\<close>.\<close>

text \<open>Chunked-induction engine for the simulation-phase
  step count.  Given a specific (finite) accepting \<open>M\<close>-path
  of length \<open>n\<close> from a reachable \<open>cM\<close> with a paired SS1
  M'-config \<open>c'\<close> satisfying the invariants \<open>buf_gamma\<close>,
  \<open>le_anchor\<close>, exhibit a corresponding accepting \<open>M'\<close>-path
  of length at most \<open>8 \<cdot> \<lceil>n / c\<rceil>\<close>.

  Proof structure (when discharged): induction on the M-path
  length \<open>n\<close>, taking the next chunk of up to
  \<open>c = card (UNIV :: 'c set)\<close> M-steps per stage and
  invoking \<open>ae_simulates_forward_stage_general\<close>.  The
  invariant \<open>buf_gamma c'_j \<and> le_anchor c'_j\<close> is
  preserved by \<open>forward_stage_general\<close>'s output
  conjuncts (just strengthened in the previous commit).  The
  M-side \<open>no_le_per_tape\<close> hypothesis for the per-tape
  unified forward stage is discharged from
  \<open>valid_reach_LE_only_pos0_ktm\<close> on the substrate,
  threaded through \<open>reach_M\<close>.

  Wrapped by \<open>ae_simulation_phase_step_count\<close> below to
  produce the named-bound \<open>obtains\<close>-form.\<close>

lemma ae_simulation_phase_chunked:
  fixes M :: "('q, 'a) ktm"
    and w :: "'a list"
    and cM cM_final :: "('a, 'q) ktc_config"
    and c' :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) ktc_config"
    and n :: nat
  assumes vM:         "valid_ktm M"
      and lu:         "le_unique M"
      and w_sub:      "set w \<subseteq> Sigma_ktm M"
      and le_neq_bl:  "le_ktm M \<noteq> bl_ktm M"
      and s_neq_t:    "s_ktm M \<noteq> t_ktm M"
      and s_neq_r:    "s_ktm M \<noteq> r_ktm M"
      and terminal: "q_stop \<in> {t_ktm M, r_ktm M}"
      and reach_M:    "(init_config_ktm M w, cM)
                          \<in> (ktm_step (delta_ktm M))\<^sup>*"
      and trace:      "(cM, cM_final) \<in> (ktm_step (delta_ktm M))^^n"
      and accept:     "ktc_state cM_final = q_stop"
      and sim:        "ae_simulates M cM c'"
      and buf_gamma:  "ae_buffer_in_gamma_block M c'"
      and le_anchor:  "\<forall>kk<k_ktm M. ktc_tape c' kk 0 = LE_block (le_ktm M)"
  shows "\<exists>m c''. m \<le> 8 * ((n + card (UNIV :: 'c set) - 1)
                            div card (UNIV :: 'c set))
              \<and> (c', c'') \<in> (ktm_step (alphabet_enlarge_delta M))^^m
              \<and> ktc_state c'' = (q_stop, init_stage (le_ktm M))"
  using reach_M trace accept sim buf_gamma le_anchor
proof (induction n arbitrary: cM cM_final c' rule: less_induct)
  case (less n)
  \<comment> \<open>Strong-induction case for path-length \<open>n\<close>.  The hypotheses
      \<open>reach_M\<close>, \<open>trace\<close>, \<open>accept\<close>, \<open>sim\<close>, \<open>buf_gamma\<close>,
      \<open>le_anchor\<close> have been re-quantified over \<open>cM\<close>,
      \<open>cM_final\<close>, \<open>c'\<close> by the induction; \<open>less.prems\<close>
      restates them for this \<open>n\<close>, and \<open>less.IH\<close> gives the
      conclusion for every strictly smaller \<open>n'\<close> (with its
      own fresh \<open>cM'\<close>, \<open>cM_final'\<close>, \<open>c''\<close>).\<close>
  show ?case
  proof (cases n)
    case 0
    \<comment> \<open>Base case: \<open>n = 0\<close> means \<open>cM = cM_final\<close> (length-0
        trace), so \<open>ktc_state cM = q_stop\<close> by \<open>accept\<close>.
        \<open>ae_simulates_accept_iff\<close> then forces
        \<open>ktc_state c' = (q_stop, init_stage (le_ktm M))\<close>.
        Witness: \<open>m = 0\<close>, \<open>c'' = c'\<close>.\<close>
    have trace_zero: "(cM, cM_final) \<in> (ktm_step (delta_ktm M))^^0"
      using less.prems(2) \<open>n = 0\<close> by simp
    have cM_eq: "cM_final = cM"
      using trace_zero by simp
    have ktc_cM: "ktc_state cM = q_stop"
      using less.prems(3) cM_eq by simp
    have state_c': "ktc_state c' = (q_stop, init_stage (le_ktm M))"
      by (rule ae_simulates_terminal_state[OF less.prems(4) terminal ktc_cM])
    have run_zero:
        "(c', c') \<in> (ktm_step (alphabet_enlarge_delta M))^^0"
      by simp
    have bound_zero:
        "(0 :: nat) \<le> 8 * ((n + card (UNIV :: 'c set) - 1)
                             div card (UNIV :: 'c set))"
      by simp
    show ?thesis
      using bound_zero run_zero state_c' by blast
  next
    case (Suc n_minus_1)
    \<comment> \<open>Inductive case: \<open>n > 0\<close>.  Select the chunk size
        \<open>k_chunk \<le> c\<close>: the earliest halt index in
        \<open>[1..min n c]\<close>, or \<open>c\<close> if no halt in that range.
        Split the trace as \<open>cM \<rightarrow>k_chunk cM_k \<rightarrow>(n - k_chunk)
        cM_final\<close>; apply \<open>forward_stage_general\<close> to get an
        M'-witness for the first chunk; apply \<open>less.IH\<close>
        on \<open>n - k_chunk < n\<close> for the remaining trace.\<close>
    \<comment> \<open>Substep A: extract the first M-step from the
        non-empty trace and derive \<open>cM\<close>'s status
        (non-halt, in Q) from \<open>ktm_step_src\<close>.\<close>
    have trace_Suc: "(cM, cM_final)
                       \<in> ktm_step (delta_ktm M) ^^ Suc n_minus_1"
      using less.prems(2) Suc by simp
    obtain cM_1 where
        step_first: "(cM, cM_1) \<in> ktm_step (delta_ktm M)"
      and rest_trace: "(cM_1, cM_final)
                          \<in> ktm_step (delta_ktm M) ^^ n_minus_1"
      using relpow_Suc_D2[OF trace_Suc] by blast
    have cM_in_Q:  "ktc_state cM \<in> Q_ktm M"
      using ktm_step_src_in_Q[OF vM step_first] .
    have cM_neq_t: "ktc_state cM \<noteq> t_ktm M"
      using ktm_step_src_neq_t[OF vM step_first] .
    have cM_neq_r: "ktc_state cM \<noteq> r_ktm M"
      using ktm_step_src_neq_r[OF vM step_first] .
    \<comment> \<open>Substep B: name the alphabet-grouping size \<open>c\<close> and
        define the chunk size as \<open>k_chunk = min n c\<close>.
        The chunk satisfies \<open>end_or_halt\<close>, which holds via
        \<open>k_chunk = n = halt\<close> when \<open>n \<le> c\<close>, or via
        \<open>k_chunk = c\<close> when \<open>n > c\<close>.\<close>
    define c where "c \<equiv> card (UNIV :: 'c set)"
    have c_pos: "0 < c"
    proof -
      have "(c_first :: 'c) \<in> UNIV" by simp
      thus ?thesis unfolding c_def by (simp add: card_gt_0_iff)
    qed
    define k_chunk where "k_chunk \<equiv> min n c"
    have k_chunk_pos:  "0 < k_chunk"
      using c_pos Suc unfolding k_chunk_def by simp
    have k_chunk_le_n: "k_chunk \<le> n"
      unfolding k_chunk_def by simp
    have k_chunk_le_c: "k_chunk \<le> c"
      unfolding k_chunk_def by simp
    \<comment> \<open>Substep C: split the M-trace at \<open>k_chunk\<close>.  Since
        \<open>k_chunk \<le> n\<close>, \<open>k_chunk + (n - k_chunk) = n\<close>;
        \<open>relpow_add\<close> turns \<open>rel ^^ n\<close> into the composition
        \<open>rel ^^ k_chunk O rel ^^ (n - k_chunk)\<close>, which a single
        unpacking exposes \<open>cM_k\<close>.\<close>
    have trace_split_rel:
        "(cM, cM_final) \<in> (ktm_step (delta_ktm M) ^^ k_chunk)
                           O (ktm_step (delta_ktm M) ^^ (n - k_chunk))"
    proof -
      have sum_eq: "k_chunk + (n - k_chunk) = n"
        using k_chunk_le_n by simp
      have "(cM, cM_final) \<in> ktm_step (delta_ktm M)
                                ^^ (k_chunk + (n - k_chunk))"
        using less.prems(2) sum_eq by simp
      thus ?thesis by (simp add: relpow_add)
    qed
    obtain cM_k where
        chunk_trace: "(cM, cM_k) \<in> ktm_step (delta_ktm M) ^^ k_chunk"
      and rest_after_chunk:
          "(cM_k, cM_final) \<in> ktm_step (delta_ktm M) ^^ (n - k_chunk)"
      using trace_split_rel by auto
    \<comment> \<open>Substep E: \<open>end_or_halt\<close>.  Two cases:
          - \<open>k_chunk = n\<close>: \<open>n \<le> c\<close>, \<open>cM_k = cM_final\<close>
            (from length-zero remaining trace), state is \<open>t_ktm M\<close>
            by \<open>accept\<close>.  Second disjunct fires.
          - \<open>k_chunk < n\<close>: \<open>n > c\<close>, so \<open>min n c = c\<close>, i.e.,
            \<open>k_chunk = c\<close>.  First disjunct fires.\<close>
    have end_or_halt:
        "k_chunk = c \<or> ktc_state cM_k \<in> {t_ktm M, r_ktm M}"
    proof (cases "k_chunk = n")
      case True
      hence "n - k_chunk = 0" by simp
      hence "cM_k = cM_final"
        using rest_after_chunk by simp
      hence "ktc_state cM_k = q_stop"
        using less.prems(3) by simp
      thus ?thesis using terminal by simp
    next
      case False
      hence "k_chunk < n" using k_chunk_le_n by linarith
      hence "min n c < n" unfolding k_chunk_def by simp
      hence "c < n" by linarith
      hence "min n c = c" by simp
      hence "k_chunk = c" unfolding k_chunk_def by simp
      thus ?thesis by simp
    qed
    \<comment> \<open>Substep F: derive \<open>no_le_per_tape\<close> for \<open>cM\<close> from
        substrate reachability.  Each disjunct of
        \<open>no_le_per_tape\<close> asserts that an \<open>M\<close>-tape cell at some
        positive index is not the left-end marker.  The substrate
        lemma \<open>valid_reach_LE_only_pos0_ktm\<close> exactly delivers
        this for every cell index \<open>p \<noteq> 0\<close> along a reachable
        trace from \<open>init_config_ktm M w\<close>; the three disjuncts'
        cell indices (\<open>(ktc_pos c' kk - 2) * c + 1 + i\<close> and
        \<open>Suc i\<close> twice) are all syntactically positive, so the
        \<open>p \<noteq> 0\<close> obligation is discharged by \<open>by simp\<close>.\<close>
    have reach_cM: "(init_config_ktm M w, cM)
                       \<in> (ktm_step (delta_ktm M))\<^sup>*"
      using less.prems(1) .
    have no_le_per_tape:
        "\<forall>kk. (ktc_pos c' kk \<ge> 2
                \<longrightarrow> (\<forall>i. i < 3 * c
                          \<longrightarrow> ktc_tape cM kk
                                ((ktc_pos c' kk - 2) * c + 1 + i)
                              \<noteq> le_ktm M))
             \<and> (ktc_pos c' kk = 1
                  \<longrightarrow> (\<forall>i. i < 2 * c
                            \<longrightarrow> ktc_tape cM kk (Suc i) \<noteq> le_ktm M))
             \<and> (ktc_pos c' kk = 0
                  \<longrightarrow> (\<forall>i. i < c
                            \<longrightarrow> ktc_tape cM kk (Suc i) \<noteq> le_ktm M))"
    proof (intro allI conjI impI allI impI)
      fix kk :: nat and i :: nat
      assume "2 \<le> ktc_pos c' kk" and "i < 3 * c"
      have idx_nz: "(ktc_pos c' kk - 2) * c + 1 + i \<noteq> 0" by simp
      show "ktc_tape cM kk ((ktc_pos c' kk - 2) * c + 1 + i) \<noteq> le_ktm M"
        using valid_reach_LE_only_pos0_ktm
                [OF vM lu w_sub reach_cM idx_nz le_neq_bl[symmetric]] .
    next
      fix kk :: nat and i :: nat
      assume "ktc_pos c' kk = 1" and "i < 2 * c"
      have idx_nz: "Suc i \<noteq> 0" by simp
      show "ktc_tape cM kk (Suc i) \<noteq> le_ktm M"
        using valid_reach_LE_only_pos0_ktm
                [OF vM lu w_sub reach_cM idx_nz le_neq_bl[symmetric]] .
    next
      fix kk :: nat and i :: nat
      assume "ktc_pos c' kk = 0" and "i < c"
      have idx_nz: "Suc i \<noteq> 0" by simp
      show "ktc_tape cM kk (Suc i) \<noteq> le_ktm M"
        using valid_reach_LE_only_pos0_ktm
                [OF vM lu w_sub reach_cM idx_nz le_neq_bl[symmetric]] .
    qed
    \<comment> \<open>Substep G: invoke \<open>forward_stage_general\<close> on the
        first chunk \<open>cM \<rightarrow>k_chunk cM_k\<close> to obtain an
        M'-witness \<open>c8\<close> of length 8 satisfying the invariants
        needed to recurse on the remaining trace.  All twelve
        hypotheses are now in hand: \<open>vM\<close>, \<open>sim\<close> (from
        \<open>less.prems\<close>), \<open>cM\<close> in \<open>Q\<close> + non-halt (substep A),
        \<open>buf_gamma\<close> + \<open>le_anchor\<close> (from \<open>less.prems\<close>),
        \<open>k_chunk_le_c\<close> (substep B), \<open>chunk_trace\<close> (substep
        C), \<open>end_or_halt\<close> (substep E), \<open>le_neq_bl\<close> (outer
        assume), \<open>no_le_per_tape\<close> (substep F).  Uses
        \<open>obtain ... by (rule ...)\<close> as the \<open>obtains\<close>-elim
        pattern (automation diverges on \<open>obtains\<close> rules
        with multiple output conjuncts).\<close>
    have k_chunk_le_card: "k_chunk \<le> card (UNIV :: 'c set)"
      using k_chunk_le_c unfolding c_def .
    have end_or_halt_card:
        "k_chunk = card (UNIV :: 'c set)
          \<or> ktc_state cM_k \<in> {t_ktm M, r_ktm M}"
      using end_or_halt unfolding c_def .
    have no_le_per_tape_card:
        "\<forall>kk. (ktc_pos c' kk \<ge> 2
                \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                          \<longrightarrow> ktc_tape cM kk
                                ((ktc_pos c' kk - 2) * card (UNIV :: 'c set) + 1 + i)
                              \<noteq> le_ktm M))
             \<and> (ktc_pos c' kk = 1
                  \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                            \<longrightarrow> ktc_tape cM kk (Suc i) \<noteq> le_ktm M))
             \<and> (ktc_pos c' kk = 0
                  \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                            \<longrightarrow> ktc_tape cM kk (Suc i) \<noteq> le_ktm M))"
      using no_le_per_tape unfolding c_def .
    obtain c8 where
        chain8: "(c', c8) \<in> ktm_step (alphabet_enlarge_delta M) ^^ 8"
      and sim_c8: "ae_simulates M cM_k c8"
      and buf_gamma_c8: "ae_buffer_in_gamma_block M c8"
      and le_anchor_c8: "\<forall>kk<k_ktm M. ktc_tape c8 kk 0 = LE_block (le_ktm M)"
      by (rule ae_simulates_forward_stage_general
                 [OF vM lu less.prems(4) cM_in_Q cM_neq_t cM_neq_r
                     less.prems(5) k_chunk_le_card chunk_trace
                     end_or_halt_card less.prems(6) le_neq_bl
                     no_le_per_tape_card])
    \<comment> \<open>Substep H: extend the substrate-reachability of \<open>cM\<close>
        to \<open>cM_k\<close>.  Composes \<open>reach_cM\<close> (an \<open>rtrancl\<close>
        certificate) with \<open>chunk_trace\<close> (a \<open>relpow\<close>
        certificate of length \<open>k_chunk\<close>) by lifting the
        \<open>relpow\<close> to \<open>rtrancl\<close> via \<open>relpow_imp_rtrancl\<close>,
        then composing via \<open>rtrancl_trans\<close>.  Needed because
        the IH recursion requires the substrate-reachability of
        the recursion's starting M-config (here, \<open>cM_k\<close>).\<close>
    have chunk_in_rtrancl: "(cM, cM_k) \<in> (ktm_step (delta_ktm M))\<^sup>*"
      using chunk_trace by (rule relpow_imp_rtrancl)
    have reach_cM_k: "(init_config_ktm M w, cM_k)
                         \<in> (ktm_step (delta_ktm M))\<^sup>*"
      using reach_cM chunk_in_rtrancl by (rule rtrancl_trans)
    \<comment> \<open>Substep I: apply \<open>less.IH\<close> for the remaining trace
        \<open>cM_k \<rightarrow>(n - k_chunk) cM_final\<close>.  Recursion is on
        \<open>n - k_chunk < n\<close> (which holds because
        \<open>k_chunk \<ge> 1\<close> and \<open>n \<ge> 1\<close>); the re-quantified
        hypotheses are \<open>reach_cM_k\<close> (substep H),
        \<open>rest_after_chunk\<close> (substep C),
        \<open>less.prems(3)\<close> (accept), \<open>sim_c8\<close>, \<open>buf_gamma_c8\<close>,
        \<open>le_anchor_c8\<close> (substep G).  Yields the recursion-arm
        witness \<open>(m_rec, c'')\<close>: an M'-path of length \<open>m_rec\<close>
        from \<open>c8\<close> ending in canonical halt, with \<open>m_rec\<close>
        bounded by \<open>8 \<cdot> \<lceil>(n - k_chunk) / c\<rceil>\<close>.\<close>
    have n_minus_lt_n: "n - k_chunk < n"
      using k_chunk_pos Suc by linarith
    obtain m_rec c'' where
        bound_rec: "m_rec \<le> 8 * ((n - k_chunk + card (UNIV :: 'c set) - 1)
                                   div card (UNIV :: 'c set))"
      and chain_rec: "(c8, c'') \<in> (ktm_step (alphabet_enlarge_delta M))^^m_rec"
      and state_c'': "ktc_state c'' = (q_stop, init_stage (le_ktm M))"
      using less.IH[OF n_minus_lt_n reach_cM_k rest_after_chunk
                       less.prems(3) sim_c8 buf_gamma_c8 le_anchor_c8]
      by blast
    \<comment> \<open>Substep J: compose the 8-step forward chunk \<open>chain8\<close>
        with the recursion-arm \<open>chain_rec\<close> via \<open>relpow_add\<close>:
        \<open>rel ^^ 8 O rel ^^ m_rec = rel ^^ (8 + m_rec)\<close>.\<close>
    have chain_compose:
        "(c', c'') \<in> (ktm_step (alphabet_enlarge_delta M))^^(8 + m_rec)"
      using chain8 chain_rec by (auto simp: relpow_add)
    \<comment> \<open>Substep K: arithmetic bound \<open>8 + m_rec \<le> 8 \<cdot> \<lceil>n/c\<rceil>\<close>.
        Case-split mirroring substep E's:
          - \<open>k_chunk = n\<close>: \<open>n - k_chunk = 0\<close> so \<open>m_rec = 0\<close>
            (IH base case yields zero-bound on a zero-length
            trace); and \<open>n \<ge> 1\<close> gives \<open>\<lceil>n/c\<rceil> \<ge> 1\<close>, so the
            target \<open>8 \<le> 8 \<cdot> 1\<close> holds.
          - \<open>k_chunk \<ne> n\<close>: substep E forces \<open>k_chunk = c\<close>
            (and \<open>c < n\<close>); the IH bound becomes
            \<open>m_rec \<le> 8 \<cdot> \<lceil>(n-1)/c\<rceil>\<close>, and the identity
            \<open>\<lceil>n/c\<rceil> = \<lceil>(n-1)/c\<rceil> + 1\<close> (which holds for
            \<open>n \<ge> 1, c \<ge> 1\<close>) gives the target with equality.\<close>
    have n_pos: "0 < n" using Suc by simp
    have bound_compose:
        "8 + m_rec
          \<le> 8 * ((n + card (UNIV :: 'c set) - 1)
                    div card (UNIV :: 'c set))"
    proof (cases "k_chunk = n")
      case True
      have m_rec_zero: "m_rec = 0"
      proof -
        have "n - k_chunk = 0" using True by simp
        hence "(n - k_chunk + card (UNIV :: 'c set) - 1)
                  div card (UNIV :: 'c set) = 0"
          using c_pos[unfolded c_def] by simp
        thus ?thesis using bound_rec by simp
      qed
      have one_le_ceil:
          "1 \<le> (n + card (UNIV :: 'c set) - 1)
                  div card (UNIV :: 'c set)"
      proof -
        have "card (UNIV :: 'c set) \<le> n + card (UNIV :: 'c set) - 1"
          using n_pos by simp
        hence "card (UNIV :: 'c set) div card (UNIV :: 'c set)
                \<le> (n + card (UNIV :: 'c set) - 1)
                    div card (UNIV :: 'c set)"
          using div_le_mono by blast
        thus ?thesis using c_pos[unfolded c_def] by simp
      qed
      show ?thesis using m_rec_zero one_le_ceil by simp
    next
      case False
      have k_chunk_eq_c: "k_chunk = c"
      proof -
        have "k_chunk < n" using k_chunk_le_n False by linarith
        hence "min n c < n" unfolding k_chunk_def by simp
        hence "c < n" by linarith
        hence "min n c = c" by simp
        thus ?thesis unfolding k_chunk_def by simp
      qed
      have n_gt_c: "c < n"
        using False k_chunk_le_n k_chunk_eq_c by linarith
      have n_minus_eq: "n - k_chunk + c - 1 = n - 1"
        using k_chunk_eq_c n_gt_c by simp
      have rec_bound:
          "m_rec \<le> 8 * ((n - 1) div card (UNIV :: 'c set))"
        using bound_rec n_minus_eq unfolding c_def by simp
      have ceil_step:
          "(n + card (UNIV :: 'c set) - 1)
              div card (UNIV :: 'c set)
            = (n - 1) div card (UNIV :: 'c set) + 1"
      proof -
        have c_nz: "card (UNIV :: 'c set) \<noteq> 0"
          using c_pos unfolding c_def by simp
        have sum_eq: "n + card (UNIV :: 'c set) - 1
                       = (n - 1) + card (UNIV :: 'c set)"
          using n_pos by simp
        have div_step:
            "((n - 1) + card (UNIV :: 'c set))
                div card (UNIV :: 'c set)
              = (n - 1) div card (UNIV :: 'c set) + 1"
          using div_add_self2[OF c_nz] .
        show ?thesis using sum_eq div_step by simp
      qed
      have "8 + m_rec
              \<le> 8 + 8 * ((n - 1) div card (UNIV :: 'c set))"
        using rec_bound by simp
      also have "\<dots> = 8 * ((n - 1) div card (UNIV :: 'c set) + 1)"
        by simp
      also have "\<dots> = 8 * ((n + card (UNIV :: 'c set) - 1)
                            div card (UNIV :: 'c set))"
        using ceil_step by simp
      finally show ?thesis .
    qed
    \<comment> \<open>Final assembly: witnesses \<open>(8 + m_rec, c'')\<close> satisfy
        the bound \<open>(8 + m_rec) \<le> 8 \<cdot> \<lceil>n/c\<rceil>\<close>, the chain
        \<open>(c', c'') \<in> alphabet_enlarge_delta^^(8 + m_rec)\<close>, and
        the canonical halt state \<open>(t_ktm M, init_stage le_M)\<close>.\<close>
    show ?thesis
      using bound_compose chain_compose state_c'' by blast
  qed
qed


text \<open>Simulation-phase step count under weak acceptance.  If
  \<open>M\<close> accepts \<open>u\<close> within time \<open>T (length u)\<close> (an accepting
  \<open>M\<close>-path of length at most \<open>T (length u)\<close> from
  \<open>init_config_ktm M u\<close> to a config in state \<open>t_ktm M\<close>),
  then from any simulation-paired SS1 config \<open>c'\<close> there is an
  accepting \<open>M'\<close>-path of length at most \<open>8 * \<lceil>T(length u) / c\<rceil>\<close>
  ending at \<open>(t_ktm M, init_stage (le_ktm M))\<close>.

  Under the weak time-bounded acceptance convention
  (\<open>accepts_in_time_ktm\<close>).  Hypothesis
  \<open>accepts_in_time_ktm M u (T (length u))\<close> replaces the
  universal-path-bound \<open>upperb_time_ktm M T\<close>; conclusion drops
  the \<open>r_ktm\<close>-arm (under weak acceptance, "reject" just means
  "no accepting path"; no canonical \<open>r_ktm\<close> config is tracked
  explicitly).  Thin
  wrapper around \<open>ae_simulation_phase_chunked\<close>: unpacks
  the weak-acceptance witness, lifts the tight bound
  \<open>(n0 + c - 1) div c\<close> to the \<open>T (length u)\<close> bound
  via monotonicity of division, and adapts to the
  \<open>obtains\<close>-form.\<close>

lemma ae_simulation_phase_step_count:
  fixes M :: "('q, 'a) ktm"
    and T :: "nat \<Rightarrow> nat"
    and u :: "'a list"
    and c' :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes vM:         "valid_ktm M"
      and lu:         "le_unique M"
      and terminal: "q_stop \<in> {t_ktm M, r_ktm M}"
      and m_accepts:  "reaches_state_in_time_ktm M u q_stop (T (length u))"
      and u_sub:      "set u \<subseteq> Sigma_ktm M"
      and sim:        "ae_simulates M (init_config_ktm M u) c'"
      and buf_gamma_c': "ae_buffer_in_gamma_block M c'"
      and le_anchor_c': "\<forall>kk<k_ktm M. ktc_tape c' kk 0 = LE_block (le_ktm M)"
      and s_neq_t:    "s_ktm M \<noteq> t_ktm M"
      and s_neq_r:    "s_ktm M \<noteq> r_ktm M"
      and le_neq_bl:  "le_ktm M \<noteq> bl_ktm M"
  obtains n_steps :: nat and c'' where
      "n_steps \<le> 8 * ((T (length u) + card (UNIV :: 'c set) - 1)
                       div card (UNIV :: 'c set))"
    and "(c', c'') \<in> ktm_step (alphabet_enlarge_delta M) ^^ n_steps"
    and "ktc_state c'' = (q_stop, init_stage (le_ktm M))"
proof -
  \<comment> \<open>Step 1: unpack the weak-acceptance witness — the specific
      terminal \<open>M\<close>-path of length \<open>n0 \<le> T (length u)\<close>
      from \<open>init_config_ktm M u\<close> to a config in state \<open>t_ktm M\<close>.\<close>
  from m_accepts obtain n0 cM_n0 where
      n0_bd:  "n0 \<le> T (length u)"
    and n0_run: "(init_config_ktm M u, cM_n0)
                    \<in> ktm_step (delta_ktm M) ^^ n0"
    and n0_acc: "ktc_state cM_n0 = q_stop"
    unfolding reaches_state_in_time_ktm_def by blast
  \<comment> \<open>Step 2: invoke the chunked-induction helper.  Reachability
      of the starting M-config (\<open>init_config_ktm M u\<close>) from
      itself is reflexive.  The helper returns an M'-witness path
      with the tight bound \<open>8 \<cdot> \<lceil>n0/c\<rceil>\<close>; the wrapper relaxes
      this to \<open>8 \<cdot> \<lceil>T(|u|)/c\<rceil>\<close> via monotonicity of
      \<open>(_ + c - 1) div c\<close> in the dividend.\<close>
  have init_reach:
      "(init_config_ktm M u, init_config_ktm M u)
          \<in> (ktm_step (delta_ktm M))\<^sup>*"
    by simp
  obtain n_steps c'' where
      tight_bound: "n_steps \<le> 8 * ((n0 + card (UNIV :: 'c set) - 1)
                                       div card (UNIV :: 'c set))"
    and run:   "(c', c'') \<in> ktm_step (alphabet_enlarge_delta M) ^^ n_steps"
    and halt:  "ktc_state c'' = (q_stop, init_stage (le_ktm M))"
    using ae_simulation_phase_chunked[OF vM lu u_sub le_neq_bl s_neq_t s_neq_r terminal
                                          init_reach n0_run n0_acc sim
                                          buf_gamma_c' le_anchor_c']
    by blast
  \<comment> \<open>Step 3: arithmetic — relax the tight \<open>n0\<close>-bound to the
      loose \<open>T(|u|)\<close>-bound using \<open>n0 \<le> T (length u)\<close> and
      monotonicity of \<open>div\<close> on the dividend.\<close>
  have div_mono:
      "(n0 + card (UNIV :: 'c set) - 1) div card (UNIV :: 'c set)
         \<le> (T (length u) + card (UNIV :: 'c set) - 1)
              div card (UNIV :: 'c set)"
    using n0_bd by (intro div_le_mono add_le_mono) auto
  have loose_bound:
      "n_steps \<le> 8 * ((T (length u) + card (UNIV :: 'c set) - 1)
                       div card (UNIV :: 'c set))"
    using tight_bound div_mono by linarith
  show ?thesis
  proof (rule that)
    show "n_steps \<le> 8 * ((T (length u) + card (UNIV :: 'c set) - 1)
                            div card (UNIV :: 'c set))"
      using loose_bound .
    show "(c', c'') \<in> ktm_step (alphabet_enlarge_delta M) ^^ n_steps"
      using run .
    show "ktc_state c'' = (q_stop, init_stage (le_ktm M))"
      using halt .
  qed
qed


end
