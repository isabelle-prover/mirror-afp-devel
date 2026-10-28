theory AlphabetEnlargement
  imports AlphabetEnlargement_Acceptance
begin

text \<open>The three top-level theorems characterising
  \<open>alphabet_enlarge\<close>, at the end of the forward-simulation
  chain that begins in
  \<open>AlphabetEnlargement_ComputeCorrect\<close>: the linear time
  bound \<open>alphabet_enlarge_time\<close>, well-formedness
  preservation \<open>alphabet_enlarge_wf\<close>, and forward language
  preservation \<open>alphabet_enlarge_language_forward\<close>.  The
  reverse direction of the language biconditional
  (\<open>alphabet_enlarge_language\<close>) and the nondeterministic
  corollary live in \<open>AlphabetEnlargement_Reverse\<close>.\<close>

subsection \<open>Top-level theorems\<close>

text \<open>Time bound, encoded form: \<open>M' = alphabet_enlarge M\<close>
  on input \<open>encode_input (bl_ktm M) w\<close> runs in time
  \<open>\<alpha> \<cdot> \<lceil>n/c\<rceil> + 8 \<cdot> \<lceil>T(n) / c\<rceil> + f\<close> for structural
  additive constants \<open>\<alpha>, f\<close> independent of \<open>M\<close>, where
  \<open>c = card (UNIV :: 'c set)\<close> is the grouping factor and \<open>n\<close> is
  \<open>M\<close>'s input length \<open>length w\<close>.  \<open>M'\<close>'s input is the
  consolidated block-encoding \<open>encode_input (bl_ktm M) w\<close> of
  length \<open>\<lceil>n/c\<rceil>\<close>.

  This is the linear-speedup theorem in \<^emph>\<open>encoded form\<close>:
  the input bijection
  \<open>encode_input\<close> is exposed externally; \<open>M'\<close>'s job is to
  validate the encoded input's shape and simulate \<open>M\<close>.  The
  classical same-alphabet statement (Hartmanis and Stearns
  \<^cite>\<open>\<open>Theorem 2\<close> in "Hartmanis1965:computational"\<close>, modernised as
  Hopcroft and Ullman \<^cite>\<open>\<open>Theorem 12.3\<close> in "Hopcroft1979:introduction"\<close>)
  follows as a corollary by
  composing this with a wrap combinator that runs an encoder pass
  first.

  Cost breakdown:
  \<^item> \<open>\<alpha> \<cdot> \<lceil>n/c\<rceil>\<close>: validation-phase pass over the
    encoded input of length \<open>\<lceil>n/c\<rceil>\<close> (forward scan + return
    scan; \<open>\<alpha> = 2\<close>).
  \<^item> \<open>8 \<cdot> \<lceil>T(n) / c\<rceil>\<close>: 8 \<open>M'\<close>-substeps per simulated
    \<open>c\<close>-fold \<open>M\<close>-step group; \<open>\<lceil>T(n)/c\<rceil>\<close> such groups suffice
    to cover \<open>M\<close>'s \<open>T(n)\<close>-step accepting path.
  \<^item> \<open>f\<close>: validation-phase setup additive (\<open>f_v\<close>).

  The \<open>T(n)\<close> argument (not \<open>T(c \<cdot> n)\<close>) reflects that
  \<open>M\<close>'s and \<open>M'\<close>'s input represent the same problem instance
  of size \<open>n\<close>; \<open>M'\<close>'s tape just compresses it by a factor
  of \<open>c\<close>.

  \<^emph>\<open>Existential acceptance.\<close>  Hypothesis and conclusion both at
  \<open>accepts_in_time_ktm\<close> (the existential accepting-path
  predicate).  The constants \<open>\<alpha>\<close>, \<open>f\<close>
  depend only on \<open>M\<close> (and the type-level \<open>'c\<close>), not
  on \<open>w\<close>; the universal-\<open>w\<close> form inside \<open>obtains\<close> encodes
  this.

  \<^emph>\<open>The same-alphabet form follows as a corollary\<close> by composing with
  the wrap combinator (\<open>encoding_wrap\<close> in
  \<open>Wrap_Defs.thy\<close>).  Theorem 12.3's setup-phase
  cost \<open>n + \<lceil>n/m\<rceil>\<close> appears in the wrapped form as the
  inline encoder's cost (\<open>O(n)\<close>) plus this lemma's
  \<open>\<lceil>n/c\<rceil>\<close> validation cost.  Together with the speedup
  factor \<open>1/c\<close> applied to \<open>T(n)\<close>, this gives the textbook
  bound \<open>c_0 \<cdot> T(n)\<close> for any \<open>c_0 > 0\<close> when
  \<open>inf T(n)/n = \<infinity>\<close> (Theorem 12.3); the companion
  \<^cite>\<open>\<open>Theorem 12.4\<close> in "Hopcroft1979:introduction"\<close> patches the
  linear case \<open>T(n) = \<Theta>(n)\<close> via a different choice of \<open>c\<close>.\<close>

theorem alphabet_enlarge_terminal_time:
  fixes M :: "('q, 'a) ktm"
    and T :: "nat \<Rightarrow> nat"
  assumes wf:        "well_formed_ktm M"
      and terminal: "q_stop \<in> {t_ktm M, r_ktm M}"
  shows "\<forall>w. set w \<subseteq> Sigma_ktm M
                \<longrightarrow> reaches_state_in_time_ktm M w q_stop (T (length w))
                \<longrightarrow> reaches_state_in_time_ktm
                      (alphabet_enlarge M
                         :: ('q \<times> ('a, ('c :: enum)) ae_stage,
                             'c \<Rightarrow> 'a) ktm)
                      (encode_input (bl_ktm M) w)
                      (q_stop, init_stage (le_ktm M))
                      (2 * ((length w + card (UNIV :: 'c set) - 1)
                              div card (UNIV :: 'c set))
                       + 8 * ((T (length w) + card (UNIV :: 'c set) - 1)
                               div card (UNIV :: 'c set))
                       + 4)"
proof -
  from wf have vM:        "valid_ktm M"
           and lu:        "le_unique M"
           and s_neq_t:   "s_ktm M \<noteq> t_ktm M"
           and s_neq_r:   "s_ktm M \<noteq> r_ktm M"
           and le_neq_bl: "le_ktm M \<noteq> bl_ktm M"
    by auto

  let ?c = "card (UNIV :: 'c set)"
  let ?M' = "alphabet_enlarge M
               :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) ktm"

    show "\<forall>w. set w \<subseteq> Sigma_ktm M
                \<longrightarrow> reaches_state_in_time_ktm M w q_stop (T (length w))
                \<longrightarrow> reaches_state_in_time_ktm ?M' (encode_input (bl_ktm M) w)
                      (q_stop, init_stage (le_ktm M))
                      (2 * ((length w + ?c - 1) div ?c)
                       + 8 * ((T (length w) + ?c - 1) div ?c)
                       + 4)"
    proof (intro allI impI)
      fix w :: "'a list"
      assume w_sub: "set w \<subseteq> Sigma_ktm M"
      assume m_acc: "reaches_state_in_time_ktm M w q_stop (T (length w))"

      \<comment> \<open>Step 1: encoded-input setup — gamma-block containment,
          well-formedness, and \<open>s_ktm M \<in> Q_ktm M\<close>.\<close>
      let ?ew = "encode_input (bl_ktm M) w
                  :: ('c \<Rightarrow> 'a) list"
      have ew_sub: "set ?ew \<subseteq> gamma_block (Sigma_ktm M \<union> {bl_ktm M})"
        by (rule encode_input_in_gamma_block[OF w_sub])
      have ew_wf: "ae_input_well_formed (bl_ktm M) ?ew"
        by (rule encode_input_well_formed[OF vM w_sub])
      have s_in_Q: "s_ktm M \<in> Q_ktm M"
        by (rule valid_ktm_s_in_Q[OF vM])

      \<comment> \<open>Step 2: validation chain — exact length
          \<open>2 \<cdot> |?ew| + 4\<close>, landing at the canonical SS1
          configuration with the tape unchanged from
          \<open>ae_init_config M ?ew\<close>.\<close>
      let ?c1 = "KConfig (s_ktm M, init_offset,
                             init_buffer (le_ktm M), init_dest, SS1)
                           (ktc_tape (ae_init_config M ?ew))
                           (\<lambda>_ :: nat. 0)
                   :: ('c \<Rightarrow> 'a,
                       'q \<times> ('a, 'c) ae_stage) ktc_config"
      have val_chain:
          "(ae_init_config M ?ew, ?c1)
              \<in> ktm_step (alphabet_enlarge_delta M)
                  ^^ (2 * length ?ew + 4)"
        by (rule ae_validation_well_formed_to_SS1
                   [OF vM ew_sub ew_wf s_in_Q s_neq_t s_neq_r le_neq_bl])

      \<comment> \<open>Step 3: post-validation invariants on \<open>?c1\<close>.

          (a) \<open>le_anchor\<close>: tape position 0 is the LE-block.
              \<open>ktc_tape ?c1 = ktc_tape (ae_init_config M ?ew)\<close>
              by construction, and \<open>ae_init_config_tape_le\<close>
              gives the LE-anchor.

          (b) \<open>buf_gamma\<close>: every component of the buffer
              \<open>init_buffer (le_ktm M) = (LE_block le, LE_block le,
              LE_block le)\<close> is in \<open>gamma_block (\<Gamma>_ktm M)\<close>;
              follows from \<open>le_ktm M \<in> \<Gamma>_ktm M\<close> via
              \<open>LE_block_in_gamma_block\<close>.

          (c) \<open>ae_simulates\<close>: SS1-branch with the canonical
              start state.  All five conjuncts derived directly
              from the start-config shape and the tape-side
              invariants on \<open>ae_init_config\<close>.\<close>
      have le_anchor: "\<forall>kk<k_ktm M. ktc_tape ?c1 kk 0 = LE_block (le_ktm M)"
      proof (intro allI impI)
        fix kk assume kk_lt: "kk < k_ktm M"
        have "ktc_tape ?c1 kk 0 = ktc_tape (ae_init_config M ?ew) kk 0"
          by simp
        also have "\<dots> = LE_block (le_ktm M)"
          by (rule ae_init_config_tape_le[OF kk_lt])
        finally show "ktc_tape ?c1 kk 0 = LE_block (le_ktm M)" .
      qed

      have buf_gamma: "ae_buffer_in_gamma_block M ?c1"
        unfolding ae_buffer_in_gamma_block_def init_buffer_def
        using LE_block_in_gamma_block[OF valid_ktm_LE_in_Gamma[OF vM]]
        by simp

      have tape_corr:
          "\<forall>k<k_ktm M. ae_tape_correspondence (le_ktm M)
                  (ktc_tape (init_config_ktm M w) k)
                  (ktc_tape (ae_init_config M ?ew) k)"
        by (rule ae_tape_correspondence_init[OF vM w_sub])
      have subst_pos_zero:
          "\<forall>k. ktc_pos (init_config_ktm M w) k = 0"
        by (cases M) simp
      have c1_pos_zero: "\<forall>k. ktc_pos ?c1 k = 0" by simp
      have pos_corr_c1:
          "\<forall>k. ktc_pos (init_config_ktm M w) k
                  = ae_decode_pos (ktc_pos ?c1 k)
                                  ((init_offset :: nat \<Rightarrow> 'c) k)"
        using c1_pos_zero subst_pos_zero
        unfolding ae_decode_pos_def by simp
      have qM_subst: "ktc_state (init_config_ktm M w) = s_ktm M"
        by (cases M) simp
      have c1_state:
          "ktc_state ?c1 = (s_ktm M, init_offset,
                            init_buffer (le_ktm M), init_dest, SS1)"
        by simp
      have gamma_block_c1: "ae_tape_in_gamma_block M ?c1"
        unfolding ae_tape_in_gamma_block_def
      proof (intro conjI)
        show "\<forall>k p. ktc_tape ?c1 k p \<in> gamma_block (\<Gamma>_ktm M)"
          using ae_init_config_in_gamma_block[OF vM ew_sub] by simp
        show "\<forall>j\<ge>k_ktm M. \<forall>p. ktc_tape ?c1 j p = bl_block (bl_ktm M)"
          by (simp add: ae_init_config_tape_blank_tail)
      qed
      have sim: "ae_simulates M (init_config_ktm M w) ?c1"
        unfolding ae_simulates_def Let_def c1_state
        using qM_subst tape_corr pos_corr_c1 gamma_block_c1
              s_neq_t s_neq_r by simp

      \<comment> \<open>Step 4: simulation-phase step count via
          \<open>ae_simulation_phase_step_count\<close>: yields an
          \<open>M'\<close>-chain from \<open>?c1\<close> to the canonical halt
          configuration of length at most
          \<open>8 \<cdot> \<lceil>T(|w|) / c\<rceil>\<close>.\<close>
      obtain n_sim c'' where
          n_sim_bd:
              "n_sim \<le> 8 * ((T (length w) + ?c - 1) div ?c)"
        and sim_chain:
            "(?c1, c'') \<in> ktm_step (alphabet_enlarge_delta M) ^^ n_sim"
        and c''_state: "ktc_state c'' = (q_stop, init_stage (le_ktm M))"
        using ae_simulation_phase_step_count
                [where M = M and T = T and u = w and c' = ?c1,
                 OF vM lu terminal m_acc w_sub sim buf_gamma le_anchor
                    s_neq_t s_neq_r le_neq_bl]
        by metis

      \<comment> \<open>Step 5: compose validation and simulation chains.\<close>
      have chain_compose:
          "(ae_init_config M ?ew, c'')
              \<in> ktm_step (alphabet_enlarge_delta M)
                  ^^ ((2 * length ?ew + 4) + n_sim)"
        using val_chain sim_chain by (auto simp: relpow_add)

      \<comment> \<open>Step 6: arithmetic bound.  \<open>length ?ew = \<lceil>|w|/c\<rceil>\<close>
          by \<open>length_encode_input\<close>; \<open>n_sim\<close> already
          bounded by \<open>8 \<cdot> \<lceil>T(|w|)/c\<rceil>\<close>.\<close>
      have len_ew: "length ?ew = (length w + ?c - 1) div ?c"
        by (rule length_encode_input)
      let ?total = "(2 * length ?ew + 4) + n_sim"
      let ?target = "2 * ((length w + ?c - 1) div ?c)
                      + 8 * ((T (length w) + ?c - 1) div ?c)
                      + 4"
      have bound: "?total \<le> ?target"
        using n_sim_bd len_ew by simp

      \<comment> \<open>Step 7: bridge to substrate-level expressions and
          conclude \<open>accepts_in_time_ktm\<close>.\<close>
      have init_bridge:
          "init_config_ktm ?M' ?ew = ae_init_config M ?ew"
        by (rule init_config_alphabet_enlarge)
      have delta_bridge:
          "delta_ktm ?M' = alphabet_enlarge_delta M"
        by (rule delta_ktm_alphabet_enlarge)

      show "reaches_state_in_time_ktm ?M' ?ew (q_stop, init_stage (le_ktm M)) ?target"
        unfolding reaches_state_in_time_ktm_def
      proof (intro exI conjI)
        show "?total \<le> ?target" using bound .
        show "(init_config_ktm ?M' ?ew, c'')
                \<in> (ktm_step (delta_ktm ?M')) ^^ ?total"
          using chain_compose init_bridge delta_bridge by simp
        show "ktc_state c'' = (q_stop, init_stage (le_ktm M))"
          by (rule c''_state)
      qed
    qed
qed

text \<open>The accepting instance: the time bound above at the accept state.\<close>

theorem alphabet_enlarge_time_explicit:
  fixes M :: "('q, 'a) ktm"
    and T :: "nat \<Rightarrow> nat"
  assumes wf:        "well_formed_ktm M"
  shows "\<forall>w. set w \<subseteq> Sigma_ktm M
                \<longrightarrow> accepts_in_time_ktm M w (T (length w))
                \<longrightarrow> accepts_in_time_ktm
                      (alphabet_enlarge M
                         :: ('q \<times> ('a, ('c :: enum)) ae_stage,
                             'c \<Rightarrow> 'a) ktm)
                      (encode_input (bl_ktm M) w)
                      (2 * ((length w + card (UNIV :: 'c set) - 1)
                              div card (UNIV :: 'c set))
                       + 8 * ((T (length w) + card (UNIV :: 'c set) - 1)
                               div card (UNIV :: 'c set))
                       + 4)"
  unfolding accepts_in_time_ktm_iff_reaches t_ktm_alphabet_enlarge
  by (rule alphabet_enlarge_terminal_time [OF wf]) simp

text \<open>The classical HU-form of the linear-speedup time bound: the
  additive constants \<open>\<alpha>\<close>, \<open>f\<close> instantiated at \<open>\<alpha> = 2\<close>, \<open>f = 4\<close>
  from \<open>alphabet_enlarge_time_explicit\<close>.  The per-block simulation
  constant \<open>8\<close> and the speedup divisor \<open>card (UNIV :: 'c set)\<close> are already
  explicit in the statement.\<close>

theorem alphabet_enlarge_time:
  fixes M :: "('q, 'a) ktm"
    and T :: "nat \<Rightarrow> nat"
  assumes wf: "well_formed_ktm M"
  obtains \<alpha> f :: nat
    where "\<forall>w. set w \<subseteq> Sigma_ktm M
                \<longrightarrow> accepts_in_time_ktm M w (T (length w))
                \<longrightarrow> accepts_in_time_ktm
                      (alphabet_enlarge M
                         :: ('q \<times> ('a, ('c :: enum)) ae_stage,
                             'c \<Rightarrow> 'a) ktm)
                      (encode_input (bl_ktm M) w)
                      (\<alpha> * ((length w + card (UNIV :: 'c set) - 1)
                              div card (UNIV :: 'c set))
                       + 8 * ((T (length w) + card (UNIV :: 'c set) - 1)
                               div card (UNIV :: 'c set))
                       + f)"
proof (rule that[of 2 4])
  show "\<forall>w. set w \<subseteq> Sigma_ktm M
                \<longrightarrow> accepts_in_time_ktm M w (T (length w))
                \<longrightarrow> accepts_in_time_ktm
                      (alphabet_enlarge M
                         :: ('q \<times> ('a, ('c :: enum)) ae_stage,
                             'c \<Rightarrow> 'a) ktm)
                      (encode_input (bl_ktm M) w)
                      (2 * ((length w + card (UNIV :: 'c set) - 1)
                              div card (UNIV :: 'c set))
                       + 8 * ((T (length w) + card (UNIV :: 'c set) - 1)
                               div card (UNIV :: 'c set))
                       + 4)"
    by (rule alphabet_enlarge_time_explicit[OF wf])
qed

text \<open>Forward language inclusion modulo input encoding: a word
  \<open>w\<close> with \<open>set w \<subseteq> \<Sigma>_M\<close> that is in
  \<open>M\<close>'s language has its canonical block-encoding (using
  \<open>M\<close>'s blank for padding) in
  \<open>M' = alphabet_enlarge M\<close>'s language.  This is the
  forward leg of the language-equivalence claim; the reverse leg
  (\<open>encode_input w \<in> Lang_ktm M' \<Longrightarrow> w \<in> Lang_ktm M\<close>)
  holds for every well-formed \<open>M\<close> --- with no determinism
  hypothesis, the original \<open>det_ktm M\<close> dependency having been
  removed in refactoring --- and lives in
  \<open>AlphabetEnlargement_Reverse.thy\<close> as the biconditional
  \<open>alphabet_enlarge_language\<close>.

  Hypotheses align with \<open>alphabet_enlarge_time\<close>:
  \<open>s \<noteq> t\<close>, \<open>s \<noteq> r\<close>, \<open>le \<noteq> bl\<close>.  The first
  two would be redundant if we manually handled the degenerate
  always-accept (\<open>s = t\<close>) and always-reject (\<open>s = r\<close>)
  cases, but matching the \<open>_time\<close> signature keeps the call
  sites uniform.  \<open>le \<noteq> bl\<close> is genuinely necessary: the
  simulation infrastructure requires it (compute substep's buffer-
  write composition), and the \<open>Sigma_ktm\<close> containment for
  encoded inputs uses it to exclude \<open>LE_block\<close>.

  The \<open>set w \<subseteq> Sigma_ktm M\<close> antecedent inside the
  \<open>\<forall>w\<close> is required: without it the inclusion fails for
  \<open>w\<close> containing blank symbols (such \<open>w\<close> are outside
  \<open>Lang_ktm M\<close> by the substrate's \<open>Lang_ktm\<close>
  definition, but their encodings can still pass M'-validation
  and be M'-accepted).

  Strategy: extract an accepting M-path of length \<open>n0\<close>;
  instantiate \<open>alphabet_enlarge_time\<close> with
  \<open>T = (\<lambda>_. n0)\<close> to obtain a bounded M'-witness; drop the
  bound and conclude.\<close>

theorem alphabet_enlarge_language_forward:
  fixes M :: "('q, 'a) ktm"
  assumes wf:        "well_formed_ktm M"
  shows "\<forall>w. set w \<subseteq> Sigma_ktm M
              \<longrightarrow> w \<in> Lang_ktm M
              \<longrightarrow> encode_input (bl_ktm M) w \<in> Lang_ktm
                    (alphabet_enlarge M
                       :: ('q \<times> ('a, ('c :: enum)) ae_stage,
                           'c \<Rightarrow> 'a) ktm)"
proof -
  from wf have vM:        "valid_ktm M"
           and lu:        "le_unique M"
           and s_neq_t:   "s_ktm M \<noteq> t_ktm M"
           and s_neq_r:   "s_ktm M \<noteq> r_ktm M"
           and le_neq_bl: "le_ktm M \<noteq> bl_ktm M"
    by auto

  let ?c = "card (UNIV :: 'c set)"
  let ?M' = "alphabet_enlarge M
               :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) ktm"

  show ?thesis
  proof (intro allI impI)
    fix w :: "'a list"
    assume w_sub: "set w \<subseteq> Sigma_ktm M"
    assume w_in_M: "w \<in> Lang_ktm M"

    \<comment> \<open>Set-containment for the encoded input under
        \<open>alphabet_enlarge M\<close>'s \<open>\<Sigma>\<close>: gamma-block
        membership minus the two excluded markers.\<close>
    have enc_in_gamma:
        "set (encode_input (bl_ktm M) w :: ('c \<Rightarrow> 'a) list)
            \<subseteq> gamma_block (Sigma_ktm M \<union> {bl_ktm M})"
      by (rule encode_input_in_gamma_block[OF w_sub])
    have enc_no_bl:
        "bl_block (bl_ktm M)
            \<notin> set (encode_input (bl_ktm M) w :: ('c \<Rightarrow> 'a) list)"
      by (rule encode_input_no_bl_block[OF vM w_sub])
    have enc_no_LE:
        "LE_block (le_ktm M)
            \<notin> set (encode_input (bl_ktm M) w :: ('c \<Rightarrow> 'a) list)"
      by (rule encode_input_no_LE_block[OF vM w_sub])
    have enc_sub:
        "set (encode_input (bl_ktm M) w :: ('c \<Rightarrow> 'a) list)
            \<subseteq> Sigma_ktm ?M'"
      unfolding Sigma_ktm_alphabet_enlarge
      using enc_in_gamma enc_no_bl enc_no_LE by blast

    \<comment> \<open>Strategy: extract a specific accepting M-path of length
        \<open>n0\<close>; instantiate \<open>alphabet_enlarge_time\<close> with
        \<open>T = (\<lambda>_. n0)\<close> to obtain a bounded M'-witness;
        drop the bound and conclude.\<close>
    from w_in_M obtain wM' nM where
        m_path: "(init_config_ktm M w,
                  KConfig (t_ktm M) wM' nM)
                    \<in> (ktm_step (delta_ktm M))\<^sup>*"
      unfolding Lang_ktm_def by blast
    obtain n0 where m_pow:
        "(init_config_ktm M w, KConfig (t_ktm M) wM' nM)
            \<in> (ktm_step (delta_ktm M)) ^^ n0"
      using m_path rtrancl_imp_relpow by metis
    have m_acc: "accepts_in_time_ktm M w n0"
      unfolding accepts_in_time_ktm_def
    proof (intro exI conjI)
      show "(n0 :: nat) \<le> n0" by simp
      show "(init_config_ktm M w, KConfig (t_ktm M) wM' nM)
              \<in> ktm_step (delta_ktm M) ^^ n0"
        using m_pow .
      show "ktc_state (KConfig (t_ktm M) wM' nM) = t_ktm M"
        by simp
    qed

    obtain \<alpha> f :: nat where AE_time:
        "\<forall>w_arg. set w_arg \<subseteq> Sigma_ktm M
                  \<longrightarrow> accepts_in_time_ktm M w_arg n0
                  \<longrightarrow> accepts_in_time_ktm ?M'
                        (encode_input (bl_ktm M) w_arg)
                        (\<alpha> * ((length w_arg + ?c - 1) div ?c)
                         + 8 * ((n0 + ?c - 1) div ?c) + f)"
      by (rule alphabet_enlarge_time
                 [where T = "\<lambda>_. n0", OF wf])
    from AE_time w_sub m_acc have m'_acc:
        "accepts_in_time_ktm ?M' (encode_input (bl_ktm M) w)
            (\<alpha> * ((length w + ?c - 1) div ?c)
             + 8 * ((n0 + ?c - 1) div ?c) + f)"
      by blast
    from m'_acc obtain n_m' c_acc where
        run: "(init_config_ktm ?M' (encode_input (bl_ktm M) w),
               c_acc)
                \<in> (ktm_step (delta_ktm ?M')) ^^ n_m'"
      and acc: "ktc_state c_acc = t_ktm ?M'"
      unfolding accepts_in_time_ktm_def by blast
    obtain wM_acc' nM_acc where c_acc_eq:
        "c_acc = KConfig (t_ktm ?M') wM_acc' nM_acc"
      using acc by (cases c_acc) simp
    have run_star:
        "(init_config_ktm ?M' (encode_input (bl_ktm M) w),
          KConfig (t_ktm ?M') wM_acc' nM_acc)
            \<in> (ktm_step (delta_ktm ?M'))\<^sup>*"
      using run c_acc_eq relpow_imp_rtrancl by metis
    show "encode_input (bl_ktm M) w \<in> Lang_ktm ?M'"
      unfolding Lang_ktm_def
      using enc_sub run_star by blast
  qed
qed

end

