theory AlphabetReduction_Theorems
  imports AlphabetReduction_Forward
begin

subsection \<open>Top-level theorems\<close>

text \<open>Per-substep typing facts: for each substep relation in
  the five-substep union, the source and target states' \<open>'q\<close>
  components lie in \<open>Q_tm M\<close>, and the source's
  \<open>ar_substep_idx\<close> tag is the relation-specific value
  (never \<open>AR_HaltAccept\<close> or \<open>AR_HaltReject\<close>).
  Used by \<open>alphabet_reduce_wf\<close>'s \<open>\<delta>'\<close>-typing
  conjunct to show \<open>\<delta>'\<close>-tuples land in
  \<open>(Q' - \<lbrace>t', r'\<rbrace>) \<times> \<dots> \<times> Q' \<times> \<dots>\<close>.\<close>

lemma ar_delta_read_typing:
  assumes "(s, a, s', a', d) \<in> ar_delta_read M"
  shows "fst s \<in> Q_tm M \<and> fst (snd s) = AR_SimRead
         \<and> fst s' \<in> Q_tm M"
  using assms
  unfolding ar_delta_read_def
  by (cases M) auto

lemma ar_delta_compute_typing:
  assumes valM: "valid_mttm M"
    and tr: "(s, a, s', a', d) \<in> ar_delta_compute M"
  shows "fst s \<in> Q_tm M \<and> fst (snd s) = AR_SimCompute
         \<and> fst s' \<in> Q_tm M"
proof -
  from tr obtain q buf q' m_a' m_d tk i dvec posk a'' d''
    where decomp: "s = (q, AR_SimCompute, tk, i, buf, dvec, posk)"
      and decomp': "s' = (q', AR_SimWrite, 0, 0, m_a', m_d, posk)"
      and m_tr: "(q, buf, q', m_a', m_d) \<in> delta_tm M"
    unfolding ar_delta_compute_def by auto
  from valid_mttm_delta_set[OF valM] m_tr
  have "q \<in> Q_tm M" and "q' \<in> Q_tm M" by auto
  thus ?thesis using decomp decomp' by simp
qed

lemma ar_delta_write_typing:
  assumes "(s, a, s', a', d) \<in> ar_delta_write M"
  shows "fst s \<in> Q_tm M \<and> fst (snd s) = AR_SimWrite
         \<and> fst s' \<in> Q_tm M"
  using assms
  unfolding ar_delta_write_def
  by (cases M) auto

lemma ar_delta_advance_typing:
  assumes "(s, a, s', a', d) \<in> ar_delta_advance M"
  shows "fst s \<in> Q_tm M \<and> fst (snd s) = AR_SimAdvance
         \<and> fst s' \<in> Q_tm M"
  using assms
  unfolding ar_delta_advance_def
  by (cases M) auto

lemma ar_delta_next_typing:
  assumes valM: "valid_mttm M"
    and tr: "(s, a, s', a', d) \<in> ar_delta_next M"
  shows "fst s \<in> Q_tm M \<and> fst (snd s) = AR_SimNext
         \<and> fst s' \<in> Q_tm M"
proof -
  from valid_mttm_t_in_Q[OF valM] valid_mttm_r_in_Q[OF valM]
  have "t_tm M \<in> Q_tm M" and "r_tm M \<in> Q_tm M" by auto
  thus ?thesis
    using tr
    unfolding ar_delta_next_def
    by (cases M) auto
qed


text \<open>State-shape extraction for \<open>alphabet_reduce_delta\<close>: every
  transition's source and target carry an \<open>M\<close>-state in \<open>Q\<close>,
  and the source stage's index is a \<^emph>\<open>simulation\<close> index — never a
  halt index — so the source state is distinct from both canonical halt
  states.  Case-split across the five substep relations (the delta is
  their union intersected with global guards, so membership lands in the
  union), each branch discharged by its typing lemma; the halt-index
  distinctness is datatype-level.\<close>
lemma alphabet_reduce_delta_state_shape:
  assumes valM: "valid_mttm M"
      and mem: "(s, a, s', a', d) \<in> alphabet_reduce_delta M"
  shows "fst s \<in> Q_tm M \<and> fst s' \<in> Q_tm M
           \<and> fst (snd s) \<noteq> AR_HaltAccept
           \<and> fst (snd s) \<noteq> AR_HaltReject"
proof -
  have memU: "(s, a, s', a', d)
                \<in> ar_delta_read M \<union> ar_delta_compute M
                    \<union> ar_delta_write M \<union> ar_delta_advance M
                    \<union> ar_delta_next M"
    using mem unfolding alphabet_reduce_delta_def by blast
  then show ?thesis
  proof (elim UnE)
    assume "(s, a, s', a', d) \<in> ar_delta_read M"
    from ar_delta_read_typing[OF this] show ?thesis by auto
  next
    assume "(s, a, s', a', d) \<in> ar_delta_compute M"
    from ar_delta_compute_typing[OF valM this] show ?thesis by auto
  next
    assume "(s, a, s', a', d) \<in> ar_delta_write M"
    from ar_delta_write_typing[OF this] show ?thesis by auto
  next
    assume "(s, a, s', a', d) \<in> ar_delta_advance M"
    from ar_delta_advance_typing[OF this] show ?thesis by auto
  next
    assume "(s, a, s', a', d) \<in> ar_delta_next M"
    from ar_delta_next_typing[OF valM this] show ?thesis by auto
  qed
qed

text \<open>Output well-formedness: \<open>alphabet_reduce\<close> preserves the
  substrate's wf predicate when the input tape alphabet has at
  least 4 symbols.  The reduced machine's tape alphabet is the whole
  finite type \<open>sym4\<close>, so the read / write codomain conditions are
  vacuous (\<open>UNIV\<close>), and the \<open>\<delta>LE\<close>-preservation,
  \<open>\<delta>LE\<close>-no-write, and \<open>\<delta>\<close>-support-past-tape-count
  conjuncts are read straight off \<open>alphabet_reduce_delta\<close>'s three
  intersection guards — no substep-builder unfold.  The only structural
  work is finite \<open>Q'\<close> (product of finite \<open>Q\<close> with the
  bounded valid stages, \<open>finite_ar_valid_stages\<close>), the three
  distinguished states landing in \<open>Q'\<close> (their stages are valid and
  bounded), and the \<open>\<delta>\<close>-shape's source / target state
  membership (\<open>alphabet_reduce_delta_state_shape\<close> plus the stage
  guards).\<close>

theorem alphabet_reduce_wf:
  fixes M :: "('q, 'a) mttm"
  assumes valM: "valid_mttm M"
      and cardG: "card (\<Gamma>_tm M) \<ge> 4"
  shows "valid_mttm
           (alphabet_reduce M
              :: ('q \<times> 'a ar_stage, sym4) mttm)"
proof -
  obtain Q\<^sub>M \<Sigma>\<^sub>M \<Gamma>\<^sub>M bl\<^sub>M le\<^sub>M \<delta>\<^sub>M s\<^sub>M t\<^sub>M r\<^sub>M k\<^sub>M where
    M_eq: "M = MTTM Q\<^sub>M \<Sigma>\<^sub>M \<Gamma>\<^sub>M bl\<^sub>M le\<^sub>M \<delta>\<^sub>M s\<^sub>M t\<^sub>M r\<^sub>M k\<^sub>M"
    using mttm.exhaust by metis

  have fin_Gamma: "finite \<Gamma>\<^sub>M"
    using valid_mttm_finite_Gamma[OF valM] M_eq by simp
  have kpos: "0 < k\<^sub>M"
    using valid_mttm_k_pos[OF valM] M_eq by simp
  have kfor1: "1 \<le> block_width \<Gamma>\<^sub>M" by (rule block_width_pos)

  \<comment> \<open>The reduced machine, expanded under \<open>M_eq\<close>.\<close>
  have ar_eq: "(alphabet_reduce M :: ('q \<times> 'a ar_stage, sym4) mttm) =
                MTTM (Q\<^sub>M \<times> {stg. ar_valid_stage \<Gamma>\<^sub>M bl\<^sub>M stg
                                   \<and> ar_stage_bounded bl\<^sub>M k\<^sub>M stg})
                     {BIT0, BIT1}
                     (UNIV :: sym4 set)
                     BLANK4 LE4
                     (alphabet_reduce_delta M)
                     (s\<^sub>M, ar_init_stage bl\<^sub>M)
                     (t\<^sub>M, ar_accept_stage bl\<^sub>M)
                     (r\<^sub>M, ar_reject_stage bl\<^sub>M)
                     k\<^sub>M"
    unfolding M_eq alphabet_reduce_def by simp

  \<comment> \<open>The three distinguished stages are valid and bounded: counter
     \<open>0 < 2 \<cdot> b\<close>, current-tape \<open>0 < k\<close>, frozen tails.\<close>
  have init_P: "ar_valid_stage \<Gamma>\<^sub>M bl\<^sub>M (ar_init_stage bl\<^sub>M)
                  \<and> ar_stage_bounded bl\<^sub>M k\<^sub>M (ar_init_stage bl\<^sub>M)"
    using kfor1 kpos
    by (simp add: ar_valid_stage_def ar_stage_bounded_def ar_init_stage_def)
  have acc_P: "ar_valid_stage \<Gamma>\<^sub>M bl\<^sub>M (ar_accept_stage bl\<^sub>M)
                 \<and> ar_stage_bounded bl\<^sub>M k\<^sub>M (ar_accept_stage bl\<^sub>M)"
    using kfor1 kpos
    by (simp add: ar_valid_stage_def ar_stage_bounded_def ar_accept_stage_def)
  have rej_P: "ar_valid_stage \<Gamma>\<^sub>M bl\<^sub>M (ar_reject_stage bl\<^sub>M)
                 \<and> ar_stage_bounded bl\<^sub>M k\<^sub>M (ar_reject_stage bl\<^sub>M)"
    using kfor1 kpos
    by (simp add: ar_valid_stage_def ar_stage_bounded_def ar_reject_stage_def)

  show "valid_mttm
          (alphabet_reduce M :: ('q \<times> 'a ar_stage, sym4) mttm)"
    unfolding ar_eq valid_mttm.simps
  proof (intro conjI)
    \<comment> \<open>(1) finite \<open>Q'\<close>: product of finite \<open>Q\<close> and the
       bounded valid stages.\<close>
    show "finite (Q\<^sub>M \<times>
                    ({stg. ar_valid_stage \<Gamma>\<^sub>M bl\<^sub>M stg
                            \<and> ar_stage_bounded bl\<^sub>M k\<^sub>M stg}
                       :: 'a ar_stage set))"
      using valid_mttm_finite_Q[OF valM] M_eq
            finite_ar_valid_stages[OF fin_Gamma]
      by (auto intro: finite_cartesian_product)

    \<comment> \<open>(2) finite \<open>\<Gamma>'\<close>: the whole finite type \<open>sym4\<close>.\<close>
    show "finite (UNIV :: sym4 set)" by (simp add: sym4_UNIV)

    \<comment> \<open>(3) \<open>\<Sigma>' \<subseteq> \<Gamma>'\<close>\<close>
    show "{BIT0, BIT1} \<subseteq> (UNIV :: sym4 set)" by simp

    \<comment> \<open>(4)-(6) the three distinguished states land in \<open>Q'\<close>.\<close>
    show "(s\<^sub>M, ar_init_stage bl\<^sub>M)
            \<in> Q\<^sub>M \<times> {stg. ar_valid_stage \<Gamma>\<^sub>M bl\<^sub>M stg
                            \<and> ar_stage_bounded bl\<^sub>M k\<^sub>M stg}"
      using valid_mttm_s_in_Q[OF valM] M_eq init_P by simp
    show "(t\<^sub>M, ar_accept_stage bl\<^sub>M)
            \<in> Q\<^sub>M \<times> {stg. ar_valid_stage \<Gamma>\<^sub>M bl\<^sub>M stg
                            \<and> ar_stage_bounded bl\<^sub>M k\<^sub>M stg}"
      using valid_mttm_t_in_Q[OF valM] M_eq acc_P by simp
    show "(r\<^sub>M, ar_reject_stage bl\<^sub>M)
            \<in> Q\<^sub>M \<times> {stg. ar_valid_stage \<Gamma>\<^sub>M bl\<^sub>M stg
                            \<and> ar_stage_bounded bl\<^sub>M k\<^sub>M stg}"
      using valid_mttm_r_in_Q[OF valM] M_eq rej_P by simp

    \<comment> \<open>(7a)-(8b) blank / LE in \<open>\<Gamma>'\<close>, not in \<open>\<Sigma>'\<close>.\<close>
    show "BLANK4 \<in> (UNIV :: sym4 set)" by simp
    show "BLANK4 \<notin> {BIT0, BIT1}" by simp
    show "LE4 \<in> (UNIV :: sym4 set)" by simp
    show "LE4 \<notin> {BIT0, BIT1}" by simp

    \<comment> \<open>(9) accept \<open>\<noteq>\<close> reject (states differ in \<open>M\<close>-component).\<close>
    show "(t\<^sub>M, ar_accept_stage bl\<^sub>M) \<noteq> (r\<^sub>M, ar_reject_stage bl\<^sub>M)"
      using valid_mttm_t_neq_r[OF valM] M_eq by simp

    \<comment> \<open>(0) \<open>0 < k'\<close>: reduction keeps \<open>M\<close>'s tape count.\<close>
    show "0 < k\<^sub>M" using kpos .

    \<comment> \<open>(10) \<open>\<delta>\<close>-shape.  Read / write codomains are \<open>UNIV\<close>
       (vacuous); source / target state membership from
       \<open>alphabet_reduce_delta_state_shape\<close> (discrete \<open>M\<close>-state)
       plus the stage-validity / boundedness guards (off the
       intersection, no builder unfold).\<close>
    show "alphabet_reduce_delta M
            \<subseteq> ((Q\<^sub>M \<times> {stg. ar_valid_stage \<Gamma>\<^sub>M bl\<^sub>M stg
                                  \<and> ar_stage_bounded bl\<^sub>M k\<^sub>M stg})
                  - {(t\<^sub>M, ar_accept_stage bl\<^sub>M),
                     (r\<^sub>M, ar_reject_stage bl\<^sub>M)})
            \<times> (UNIV \<rightarrow> (UNIV :: sym4 set))
            \<times> (Q\<^sub>M \<times> {stg. ar_valid_stage \<Gamma>\<^sub>M bl\<^sub>M stg
                                  \<and> ar_stage_bounded bl\<^sub>M k\<^sub>M stg})
            \<times> (UNIV \<rightarrow> (UNIV :: sym4 set))
            \<times> (UNIV \<rightarrow> UNIV)"
    proof (rule subsetI)
      fix x assume xin: "x \<in> alphabet_reduce_delta M"
      obtain s a s' a' d where x_eq: "x = (s, a, s', a', d)"
        by (cases x) auto
      from xin have mem_t: "(s, a, s', a', d) \<in> alphabet_reduce_delta M"
        unfolding x_eq by simp
      \<comment> \<open>Stage validity / boundedness off the intersection guards.\<close>
      from mem_t have inter:
        "ar_valid_stage (\<Gamma>_tm M) (bl_tm M) (snd s)
           \<and> ar_valid_stage (\<Gamma>_tm M) (bl_tm M) (snd s')
           \<and> ar_stage_bounded (bl_tm M) (k_tm M) (snd s)
           \<and> ar_stage_bounded (bl_tm M) (k_tm M) (snd s')"
        unfolding alphabet_reduce_delta_def by simp
      \<comment> \<open>Discrete \<open>M\<close>-state shape from the substep builders.\<close>
      have shape: "fst s \<in> Q_tm M \<and> fst s' \<in> Q_tm M
                     \<and> fst (snd s) \<noteq> AR_HaltAccept
                     \<and> fst (snd s) \<noteq> AR_HaltReject"
        by (rule alphabet_reduce_delta_state_shape[OF valM mem_t])
      have s_in: "s \<in> (Q\<^sub>M \<times> {stg. ar_valid_stage \<Gamma>\<^sub>M bl\<^sub>M stg
                                      \<and> ar_stage_bounded bl\<^sub>M k\<^sub>M stg})
                          - {(t\<^sub>M, ar_accept_stage bl\<^sub>M),
                             (r\<^sub>M, ar_reject_stage bl\<^sub>M)}"
        using shape inter M_eq
        by (cases s) (auto simp: ar_accept_stage_def ar_reject_stage_def)
      have s'_in: "s' \<in> Q\<^sub>M \<times> {stg. ar_valid_stage \<Gamma>\<^sub>M bl\<^sub>M stg
                                      \<and> ar_stage_bounded bl\<^sub>M k\<^sub>M stg}"
        using shape inter M_eq by (cases s') auto
      show "x \<in> ((Q\<^sub>M \<times> {stg. ar_valid_stage \<Gamma>\<^sub>M bl\<^sub>M stg
                                    \<and> ar_stage_bounded bl\<^sub>M k\<^sub>M stg})
                      - {(t\<^sub>M, ar_accept_stage bl\<^sub>M),
                         (r\<^sub>M, ar_reject_stage bl\<^sub>M)})
                  \<times> (UNIV \<rightarrow> (UNIV :: sym4 set))
                  \<times> (Q\<^sub>M \<times> {stg. ar_valid_stage \<Gamma>\<^sub>M bl\<^sub>M stg
                                    \<and> ar_stage_bounded bl\<^sub>M k\<^sub>M stg})
                  \<times> (UNIV \<rightarrow> (UNIV :: sym4 set))
                  \<times> (UNIV \<rightarrow> UNIV)"
        unfolding x_eq using s_in s'_in
        by (auto simp: mem_Times_iff Pi_iff)
    qed

    \<comment> \<open>(11) \<open>\<delta>LE\<close> preservation — exactly the second intersection
       guard.\<close>
    show "\<forall>q a q' a' d j.
            (q, a, q', a', d) \<in> alphabet_reduce_delta M \<longrightarrow>
            a j = LE4 \<longrightarrow> a' j = LE4 \<and> d j \<in> {dir.N, dir.R}"
      unfolding alphabet_reduce_delta_def by auto

    \<comment> \<open>(12) \<open>\<delta>\<close>-support past tape count — exactly the padding-read
       intersection guard.\<close>
    show "\<forall>q a q' a' d.
            (q, a, q', a', d) \<in> alphabet_reduce_delta M \<longrightarrow>
            (\<forall>j\<ge>k\<^sub>M. a j = BLANK4 \<and> a' j = BLANK4 \<and> d j = dir.N)"
      unfolding alphabet_reduce_delta_def using M_eq by auto
  qed
qed

text \<open>The reduced machine is \<^emph>\<open>le-unique\<close> unconditionally: its
  \<open>\<delta>'\<close> is intersected with the support filter
  \<open>{(s, a, s', a', d). \<forall>k. a' k = LE4 \<longrightarrow> a k = LE4}\<close>
  (the \<open>le_unique\<close> clause, with \<open>le_tm (alphabet_reduce M) =
  LE4\<close>), so every produced transition writes \<open>LE4\<close> only where it
  read \<open>LE4\<close> — no hypothesis on \<open>M\<close> at all.  This is the
  output-side guarantee that makes \<open>alphabet_reduce\<close> a
  \<^emph>\<open>cut-absorbing\<close> normaliser: even a source machine that has
  planted a fresh \<open>le\<close> (cut its tape) reduces to a machine whose
  only \<open>LE4\<close> cell is the mandatory boundary.\<close>

lemma alphabet_reduce_le_unique:
  "le_unique (alphabet_reduce M)"
proof (unfold le_unique_def, intro allI impI)
  fix q a q' a' d j
  assume mem: "(q, a, q', a', d) \<in> delta_tm (alphabet_reduce M)"
    and a'le: "a' j = le_tm (alphabet_reduce M)"
  have "(q, a, q', a', d)
          \<in> {(s, a, s', a', d). \<forall>k. a' k = LE4 \<longrightarrow> a k = LE4}"
    using mem unfolding alphabet_reduce_delta alphabet_reduce_delta_def by blast
  hence allk: "\<forall>k. a' k = LE4 \<longrightarrow> a k = LE4" by simp
  from a'le have "a' j = LE4" by simp
  with allk have "a j = LE4" by blast
  thus "a j = le_tm (alphabet_reduce M)" by simp
qed

text \<open>Output well-formedness, the strong form: \<open>alphabet_reduce\<close>
  maps any valid \<open>M\<close> (with a \<open>\<ge> 4\<close>-symbol tape alphabet) to a
  \<^emph>\<open>well-formed\<close> machine — \<open>valid_mttm\<close> plus the three
  non-degeneracy conditions plus \<open>le_unique\<close>.  The
  start-vs-halt-state distinctness is structural (the
  \<open>AR_SimRead\<close> init stage differs from the \<open>AR_HaltAccept\<close>
  / \<open>AR_HaltReject\<close> halt stages in its substep tag), so no
  \<open>s \<noteq> t\<close> hypothesis on \<open>M\<close> is needed.  This is the
  precondition the alphabet-enlargement combinator requires of its
  input, so it is the bridge that lets \<open>alphabet_reduce\<close>'s output
  feed \<open>alphabet_enlarge\<close> in a composition.\<close>

theorem alphabet_reduce_well_formed:
  fixes M :: "('q, 'a) mttm"
  assumes valM: "valid_mttm M"
      and cardG: "card (\<Gamma>_tm M) \<ge> 4"
  shows "well_formed_mttm
           (alphabet_reduce M :: ('q \<times> 'a ar_stage, sym4) mttm)"
proof -
  have v: "valid_mttm (alphabet_reduce M)" by (rule alphabet_reduce_wf[OF valM cardG])
  have lu: "le_unique (alphabet_reduce M)" by (rule alphabet_reduce_le_unique)
  have st: "s_tm (alphabet_reduce M) \<noteq> t_tm (alphabet_reduce M)"
    by (simp add: ar_init_stage_def ar_accept_stage_def)
  have sr: "s_tm (alphabet_reduce M) \<noteq> r_tm (alphabet_reduce M)"
    by (simp add: ar_init_stage_def ar_reject_stage_def)
  have lebl: "le_tm (alphabet_reduce M) \<noteq> bl_tm (alphabet_reduce M)"
    by simp
  from v st sr lebl lu show ?thesis by blast
qed

text \<open>Initial-configuration accessors, in terms of the machine's
  structural projections.  Generic (any \<open>M\<close>); they let the
  init-correspondence proofs read the start tape / state / heads
  without an inline \<open>cases M\<close>.\<close>

lemma mt_tape_init_config:
  "mt_tape (init_config_mttm M w)
     = (\<lambda>k n. if k < k_tm M
              then (if n = 0 then le_tm M
                    else if k = 0 \<and> n \<le> length w then w ! (n - 1)
                    else bl_tm M)
              else bl_tm M)"
proof (cases M)
  case (MTTM Q Sg Gm bl le dl s tt rr kk)
  then have lhs: "mt_tape (init_config_mttm M w)
                    = (\<lambda>k n. if k < kk
                             then (if n = 0 then le
                                   else if k = 0 \<and> n \<le> length w then w ! (n - 1)
                                   else bl)
                             else bl)"
    and le': "le_tm M = le" and bl': "bl_tm M = bl" and kk': "k_tm M = kk"
    by simp_all
  show ?thesis by (simp only: lhs le' bl' kk')
qed

lemma mt_state_init_config:
  "mt_state (init_config_mttm M w) = s_tm M"
proof (cases M)
  case (MTTM Q Sg Gm bl le dl s tt rr kk)
  then have lhs: "mt_state (init_config_mttm M w) = s" and s': "s_tm M = s"
    by simp_all
  show ?thesis by (simp only: lhs s')
qed

lemma mt_pos_init_config:
  "mt_pos (init_config_mttm M w) = (\<lambda>_. 0)"
  by (cases M) simp

text \<open>Specialised initial tape of the reduced machine: \<open>LE4\<close> at
  position 0, the (already-encoded) input \<open>w'\<close> on tape 0, and
  \<open>BLANK4\<close> everywhere else.  Stated with \<open>w'\<close> free and an
  \<open>M\<close>-free right-hand side, so it closes by the same
  \<open>cases M\<close>/\<open>alphabet_reduce_def\<close> route as the structural
  projections — sidestepping selector-reduction on \<open>\<Gamma>_tm M\<close>
  etc.\<close>
lemma mt_tape_init_config_ar:
  "mt_tape (init_config_mttm (alphabet_reduce M) w')
     = (\<lambda>k n. if k < k_tm M
              then (if n = 0 then LE4
                    else if k = 0 \<and> n \<le> length w' then w' ! (n - 1)
                    else BLANK4)
              else BLANK4)"
  by (cases M) (simp add: alphabet_reduce_def)

text \<open>Initial-tape correspondence: at the start configuration the
  encoded input \<open>encode_input_ar \<Gamma> bl w\<close> lays out, block by
  block, exactly as \<open>cell_repr\<close> demands of M's initial tape.
  The proper region (M-position \<open>1 \<le> p \<le> |w|\<close>) reads off
  \<open>nth_encode_input_ar\<close>; the blank tail (\<open>p > |w|\<close>) and the
  non-input tapes (\<open>k \<noteq> 0\<close>) both reduce to the all-\<open>BLANK4\<close>
  block \<open>cell_repr \<Gamma> bl bl\<close>.\<close>
lemma ar_tape_correspondence_init:
  fixes M :: "('q, 'a) mttm"
  assumes vM: "valid_mttm M"
      and wS: "set w \<subseteq> Sigma_tm M"
      and kK: "k < k_tm M"
  shows "ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
           (mt_tape (init_config_mttm M w) k)
           (mt_tape (init_config_mttm (alphabet_reduce M)
                       (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w)) k)"
  (is "ar_tape_correspondence ?G ?le ?bl ?tM ?tM'")
proof -
  let ?K = "block_width ?G"
  let ?w' = "encode_input_ar ?G ?bl w"
  have len_w': "length ?w' = ?K * length w" by (rule length_encode_input_ar)
  have bl_notin: "?bl \<notin> Sigma_tm M" using vM by (cases M) auto
  have tM_eq: "?tM = (\<lambda>n. if n = 0 then ?le
                          else if k = 0 \<and> n \<le> length w then w ! (n - 1)
                          else ?bl)"
    by (simp add: mt_tape_init_config kK)
  have tM'_eq: "?tM' = (\<lambda>n. if n = 0 then LE4
                            else if k = 0 \<and> n \<le> length ?w' then ?w' ! (n - 1)
                            else BLANK4)"
    by (simp add: mt_tape_init_config_ar kK)
  have blank_repr: "cell_repr ?G ?bl ?bl ! j = BLANK4" if "j < ?K" for j
    using that by (simp add: cell_repr_def)
  show ?thesis
    unfolding ar_tape_correspondence_def
  proof (intro conjI)
    show "?tM 0 = ?le" by (simp add: tM_eq)
  next
    show "?tM' 0 = LE4" by (simp add: tM'_eq)
  next
    show "\<forall>p. 1 \<le> p \<longrightarrow> (\<forall>j. j < ?K \<longrightarrow>
            ?tM' (sim_pos ?K p + j) = cell_repr ?G ?bl (?tM p) ! j)"
    proof (intro allI impI)
      fix p j :: nat
      assume p1: "1 \<le> p" and jK: "j < ?K"
      obtain p0 where p_eq: "p = Suc p0" using p1 by (cases p) auto
      have sp: "sim_pos ?K p = p0 * ?K + 1"
        by (simp add: p_eq sim_pos_def)
      have q_ge1: "1 \<le> sim_pos ?K p + j" using sp by simp
      have sppos: "0 < sim_pos ?K p" using sp by simp
      show "?tM' (sim_pos ?K p + j) = cell_repr ?G ?bl (?tM p) ! j"
      proof (cases "k = 0")
        case False
        have "?tM p = ?bl" using False p1 by (simp add: tM_eq)
        moreover have "?tM' (sim_pos ?K p + j) = BLANK4"
          using False sppos by (simp add: tM'_eq)
        ultimately show ?thesis using blank_repr[OF jK] by simp
      next
        case True
        note k0 = True
        show ?thesis
        proof (cases "p \<le> length w")
          case True
          note pw = True
          have p0w: "p0 < length w" using pw p_eq by simp
          have neq: "w ! p0 \<noteq> ?bl"
          proof -
            have "w ! p0 \<in> set w" using p0w by simp
            hence "w ! p0 \<in> Sigma_tm M" using wS by blast
            thus ?thesis using bl_notin by auto
          qed
          have qle: "sim_pos ?K p + j \<le> length ?w'"
          proof -
            have "sim_pos ?K p + j = p0 * ?K + 1 + j" using sp by simp
            also have "\<dots> \<le> p0 * ?K + ?K" using jK by linarith
            also have "\<dots> = Suc p0 * ?K" by (simp add: mult_Suc)
            also have "\<dots> \<le> length w * ?K"
              using Suc_leI[OF p0w] by (rule mult_le_mono1)
            also have "\<dots> = length ?w'" using len_w' by (simp add: mult.commute)
            finally show ?thesis .
          qed
          have lhs: "?tM' (sim_pos ?K p + j) = encode_symbol ?G ?bl (w ! p0) ! j"
          proof -
            have idx: "sim_pos ?K p + j - 1 = p0 * ?K + j" using sp by simp
            have "?tM' (sim_pos ?K p + j) = ?w' ! (sim_pos ?K p + j - 1)"
              unfolding tM'_eq using k0 sppos qle by simp
            also have "\<dots> = ?w' ! (p0 * ?K + j)" using idx by simp
            also have "\<dots> = encode_symbol ?G ?bl (w ! p0) ! j"
              using p0w jK by (simp add: nth_encode_input_ar)
            finally show ?thesis .
          qed
          have rhs: "cell_repr ?G ?bl (?tM p) ! j = encode_symbol ?G ?bl (w ! p0) ! j"
          proof -
            have "?tM p = w ! p0" unfolding tM_eq using k0 pw p_eq by simp
            thus ?thesis using neq by (simp add: cell_repr_def)
          qed
          show ?thesis using lhs rhs by simp
        next
          case False
          note pw = False
          have lwle: "length w \<le> p0" using pw p_eq by simp
          have "?tM p = ?bl" unfolding tM_eq using k0 pw p_eq by simp
          hence rhs: "cell_repr ?G ?bl (?tM p) ! j = BLANK4"
            using blank_repr[OF jK] by simp
          have qgt: "length ?w' < sim_pos ?K p + j"
          proof -
            have a: "length w * ?K \<le> p0 * ?K" using lwle by (rule mult_le_mono1)
            have b: "sim_pos ?K p + j = p0 * ?K + 1 + j" using sp by simp
            have c: "length ?w' = length w * ?K" using len_w' by (simp add: mult.commute)
            show ?thesis using a b c by linarith
          qed
          have "?tM' (sim_pos ?K p + j) = BLANK4"
            unfolding tM'_eq using k0 sppos qgt by simp
          thus ?thesis using rhs by simp
        qed
      qed
    qed
  qed
qed

text \<open>The three simulation invariants at the start configuration —
  the entry premises the chunked engine \<open>ar_simulation_phase_chunked\<close>
  consumes.  \<open>ar_simulates_init\<close> carries the weight (its
  \<open>AR_SimRead\<close> arm needs \<open>s \<noteq> t\<close>, \<open>s \<noteq> r\<close>
  from \<open>valid_mttm\<close>, and its tape clause is
  \<open>ar_tape_correspondence_init\<close>); the other two read straight
  off \<open>ar_init_stage\<close>.\<close>

lemma ar_simulates_init:
  fixes M :: "('q, 'a) mttm"
  assumes vM: "valid_mttm M"
      and wS: "set w \<subseteq> Sigma_tm M"
      and snt: "s_tm M \<noteq> t_tm M"
      and snr: "s_tm M \<noteq> r_tm M"
  shows "ar_simulates M (init_config_mttm M w)
           (init_config_mttm (alphabet_reduce M)
              (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w))"
proof -
  let ?cM = "init_config_mttm M w"
  let ?c' = "init_config_mttm (alphabet_reduce M)
               (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w)"
  have st: "mt_state ?c' = (s_tm M, ar_init_stage (bl_tm M))"
    by (simp add: mt_state_init_config)
  have stM: "mt_state ?cM = s_tm M" by (simp add: mt_state_init_config)
  have tc: "\<forall>k < k_tm M. ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
              (mt_tape ?cM k) (mt_tape ?c' k)"
    using ar_tape_correspondence_init[OF vM wS] by blast
  have posM: "mt_pos ?cM = (\<lambda>_. 0)" and pos': "mt_pos ?c' = (\<lambda>_. 0)"
    by (simp_all add: mt_pos_init_config)
  show ?thesis
    unfolding ar_simulates_def Let_def
    by (simp add: st stM tc posM pos' ar_init_stage_def sim_pos_def snt snr)
qed

lemma ar_posk_consistent_init:
  shows "ar_posk_consistent M (init_config_mttm M w)
           (init_config_mttm (alphabet_reduce M)
              (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w))"
  unfolding ar_posk_consistent_def
  by (simp add: mt_state_init_config mt_pos_init_config ar_init_stage_def)

lemma ar_at_read_boundary_init:
  assumes vM: "valid_mttm M"
  shows "ar_at_read_boundary M
           (init_config_mttm (alphabet_reduce M)
              (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w))"
proof -
  let ?M' = "alphabet_reduce M"
  let ?c' = "init_config_mttm ?M' (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w)"
  have kpos: "0 < k_tm M" using vM by (cases M) auto
  \<comment> \<open>The padding tapes \<open>j \<ge> k_tm M\<close> of the reduced machine's
     initial config read its blank \<open>BLANK4\<close> (else-branch of
     \<open>init_config_mttm\<close>; \<open>k_tm ?M' = k_tm M\<close>).\<close>
  have pad: "\<forall>j \<ge> k_tm M. mt_tape ?c' j (mt_pos ?c' j) = BLANK4"
    by (cases M) (auto simp: alphabet_reduce_def)
  show ?thesis
    unfolding ar_at_read_boundary_def
    using pad kpos
    by (simp add: mt_state_init_config ar_init_stage_def ar_stage_bounded_def)
qed

text \<open>The encoded input is a \<open>BIT0\<close>/\<open>BIT1\<close> string,
  unconditionally: every block is \<open>encode_symbol\<close>'s image,
  whose cells lie in \<open>\<lbrace>BIT0, BIT1\<rbrace>\<close> by
  \<open>encode_symbol_cell_domain\<close> — so this needs no
  \<open>set w \<subseteq> \<Sigma>\<close> hypothesis.  It discharges the
  set-containment side of \<open>Lang_mttm (alphabet_reduce M)\<close>
  membership.\<close>
lemma set_encode_input_ar:
  "set (encode_input_ar \<Gamma> bl w) \<subseteq> {BIT0, BIT1}"
proof (induct w)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have "encode_input_ar \<Gamma> bl (x # xs)
          = encode_symbol \<Gamma> bl x @ encode_input_ar \<Gamma> bl xs"
    by (simp add: encode_input_ar_def)
  thus ?case using Cons.hyps encode_symbol_cell_domain[of \<Gamma> bl x] by auto
qed

text \<open>Forward language preservation: an accepting \<open>M\<close>-run on
  \<open>w\<close> lifts to an accepting \<open>M'\<close>-run on the encoded
  input, via the chunked engine off the initial correspondence.
  This is the forward half of \<open>alphabet_reduce_language\<close>;
  it mirrors \<open>alphabet_enlarge_language_forward\<close>.  The reverse
  half, and the full biconditional \<open>alphabet_reduce_language\<close>,
  live in \<open>AlphabetReduction_Reverse.thy\<close> (which imports this
  theory), supplied by the chunked-reverse engine
  \<open>ar_simulation_phase_chunked_reverse\<close>.\<close>
theorem alphabet_reduce_language_forward:
  fixes M :: "('q, 'a) mttm"
  assumes vM: "valid_mttm M"
      and s_neq_t: "s_tm M \<noteq> t_tm M"
      and s_neq_r: "s_tm M \<noteq> r_tm M"
      and le_neq_bl: "le_tm M \<noteq> bl_tm M"
      and card_ge: "card (\<Gamma>_tm M) \<ge> 4"
  shows "\<forall>w. set w \<subseteq> Sigma_tm M \<longrightarrow> w \<in> Lang_mttm M
              \<longrightarrow> encode_input_ar (\<Gamma>_tm M) (bl_tm M) w
                    \<in> Lang_mttm (alphabet_reduce M
                         :: ('q \<times> 'a ar_stage, sym4) mttm)"
proof -
  let ?M' = "alphabet_reduce M :: ('q \<times> 'a ar_stage, sym4) mttm"
  show ?thesis
  proof (intro allI impI)
    fix w :: "'a list"
    assume w_sub: "set w \<subseteq> Sigma_tm M"
    assume w_in: "w \<in> Lang_mttm M"
    from w_in obtain w' nw where
        run_star: "(init_config_mttm M w, Config\<^sub>M (t_tm M) w' nw)
                     \<in> (mttm_step (delta_tm M))\<^sup>*"
      unfolding Lang_mttm_def by blast
    then obtain nn where
        trace: "(init_config_mttm M w, Config\<^sub>M (t_tm M) w' nw)
                  \<in> (mttm_step (delta_tm M)) ^^ nn"
      using rtrancl_imp_relpow by blast
    let ?c' = "init_config_mttm ?M' (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w)"
    have reach0: "(init_config_mttm M w, init_config_mttm M w)
                    \<in> (mttm_step (delta_tm M))\<^sup>*" by blast
    have accf: "mt_state (Config\<^sub>M (t_tm M) w' nw) = t_tm M" by simp
    have sim: "ar_simulates M (init_config_mttm M w) ?c'"
      by (rule ar_simulates_init[OF vM w_sub s_neq_t s_neq_r])
    have posk: "ar_posk_consistent M (init_config_mttm M w) ?c'"
      by (rule ar_posk_consistent_init)
    have rbnd: "ar_at_read_boundary M ?c'"
      by (rule ar_at_read_boundary_init[OF vM])
    obtain m c'' where
        run: "(?c', c'') \<in> (mttm_step (alphabet_reduce_delta M)) ^^ m"
      and st'': "mt_state c'' = (t_tm M, ar_accept_stage (bl_tm M))"
      using ar_simulation_phase_chunked
              [OF vM w_sub card_ge reach0 trace accf sim posk rbnd le_neq_bl]
      by blast
    have st2: "mt_state c'' = t_tm ?M'" using st'' by simp
    obtain wM' nM' where c''_eq: "c'' = Config\<^sub>M (t_tm ?M') wM' nM'"
      using st2 by (cases c'') simp
    have run': "(?c', c'') \<in> (mttm_step (delta_tm ?M')) ^^ m"
      using run by simp
    have run_star': "(?c', Config\<^sub>M (t_tm ?M') wM' nM')
                       \<in> (mttm_step (delta_tm ?M'))\<^sup>*"
      using run' c''_eq relpow_imp_rtrancl by metis
    have enc_sub: "set (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w)
                     \<subseteq> Sigma_tm ?M'"
      using set_encode_input_ar by simp
    show "encode_input_ar (\<Gamma>_tm M) (bl_tm M) w \<in> Lang_mttm ?M'"
      unfolding Lang_mttm_def using enc_sub run_star' by blast
  qed
qed

text \<open>The per-\<open>M\<close>-step super-step count \<open>C \<cdot> (5 \<cdot> k + 2) + 2\<close>
  (\<open>C = k_tm M\<close>, \<open>k = b = block_width\<close>) folds into one \<open>b\<close>-factor
  \<open>(6 \<cdot> C + 1) \<cdot> k\<close>.  The slack is \<open>(C + 1) \<cdot> (k - 2) \<ge> 0\<close>, tight at
  \<open>k = 2\<close> --- so \<open>6 \<cdot> C + 1\<close> is the least factor that absorbs the count
  for every \<open>k \<ge> 2\<close>.  The reduction always encodes into blocks of width
  \<open>\<ge> 2\<close> (from \<open>card \<Gamma>_M \<ge> 4\<close>), so the \<open>b \<ge> 2\<close> precondition is always
  met; the looser \<open>b \<ge> 1\<close> fold to \<open>7 \<cdot> C + 2\<close> is unnecessary.\<close>
lemma ar_time_bound_arith_sharp:
  fixes C k :: nat
  assumes "2 \<le> k"
  shows "C * (5 * k + 2) + 2 \<le> (6 * C + 1) * k"
proof -
  obtain k0 where k: "k = 2 + k0" using le_Suc_ex[OF assms] by blast
  have "(6 * C + 1) * k = C * (5 * k + 2) + 2 + (C + 1) * k0"
    by (simp add: k algebra_simps)
  thus ?thesis by linarith
qed

text \<open>Time bound under weak time-bounded acceptance, with explicit
  constants.  If \<open>M\<close> accepts \<open>w\<close> within \<open>T(|w|)\<close> steps, the output
  machine accepts the encoded input within
  \<open>(6 \<cdot> k_tm M + 1) \<cdot> b \<cdot> T(|w|)\<close> steps, where
  \<open>b = block_width (\<Gamma>_tm M)\<close> is the per-symbol block length (in
  \<open>sym4\<close> cells) and \<open>k_tm M\<close> is
  the tape count.  The exact per-\<open>M\<close>-step super-step count is
  \<open>k_tm M \<cdot> (5 \<cdot> b + 2) + 2\<close>, folded up to \<open>(6 \<cdot> k_tm M + 1) \<cdot> b\<close> using
  \<open>b \<ge> 2\<close> (\<open>ar_time_bound_arith_sharp\<close>; \<open>b \<ge> 2\<close> holds because
  \<open>card (\<Gamma>_tm M) \<ge> 4\<close>, and the factor is tight at \<open>b = 2\<close>, i.e.\
  \<open>card (\<Gamma>_tm M) = 4\<close>); the linear-in-\<open>|w|\<close> coefficient and the
  additive constant are both \<open>0\<close>.  \<open>b\<close> is logarithmic in the
  source-alphabet cardinality \<open>card (\<Gamma>_tm M)\<close> (the binary-encoding design
  point) --- a \<^emph>\<open>ceiling\<close> log, so the slowdown factor is a step
  function of \<open>card (\<Gamma>_tm M)\<close> that jumps by one at each power of two
  (the band \<open>2 ^ (b - 1) < card (\<Gamma>_tm M) \<le> 2 ^ b\<close> is pinned by
  \<open>card_le_two_pow_block_width\<close> and \<open>two_pow_block_width_pred_less_card\<close>).
  The count is the whole alphabet, blank included at index \<open>0\<close> (the
  endmarker \<open>le\<close> is a genuinely coded symbol, so it too is counted); so
  \<open>b\<close> is the uniform-code width, one cell above the coding minimum
  \<open>\<lceil>log\<^sub>2 (card (\<Gamma>_tm M) - 1)\<rceil>\<close> just past a power of two
  --- see \<open>block_width\<close>.
  Weak acceptance, not the strong all-paths \<open>upperb_time_mttm\<close>, is
  the target: the strong bound is unprovable for the no-validation
  construction, and weak acceptance serves both the DTM and NDTM
  applications.  Mirrors \<open>alphabet_enlarge_time_explicit\<close>.  The classical
  existential form is the \<open>obtains\<close>-corollary \<open>alphabet_reduce_time\<close> below.\<close>

theorem alphabet_reduce_time_explicit:
  fixes M :: "('q, 'a) mttm"
    and T :: "nat \<Rightarrow> nat"
  assumes vM: "valid_mttm M"
      and s_neq_t: "s_tm M \<noteq> t_tm M"
      and s_neq_r: "s_tm M \<noteq> r_tm M"
      and le_neq_bl: "le_tm M \<noteq> bl_tm M"
      and card_ge: "card (\<Gamma>_tm M) \<ge> 4"
    shows "\<forall>w. set w \<subseteq> Sigma_tm M
              \<longrightarrow> accepts_in_time_mttm M w (T (length w))
              \<longrightarrow> accepts_in_time_mttm
                    (alphabet_reduce M
                       :: ('q \<times> 'a ar_stage, sym4) mttm)
                    (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w)
                    ((6 * k_tm M + 1) * block_width (\<Gamma>_tm M) * T (length w))"
proof -
  let ?C = "k_tm M"
  let ?k = "block_width (\<Gamma>_tm M)"
  let ?M' = "alphabet_reduce M :: ('q \<times> 'a ar_stage, sym4) mttm"
  let ?d = "6 * ?C + 1"
  \<comment> \<open>encoding length \<open>\<ge> 2\<close> from \<open>card \<Gamma>_M \<ge> 4\<close>, as in the walker\<close>
  have kge2: "2 \<le> ?k"
  proof -
    have "(2::nat) ^ 2 \<le> 2 ^ ?k"
      using card_ge card_le_two_pow_block_width[of "\<Gamma>_tm M"] by simp
    thus "2 \<le> ?k" using power_le_imp_le_exp[of "2::nat" 2 ?k] by simp
  qed
  have bnd: "?C * (5 * ?k + 2) + 2 \<le> ?d * ?k"
    by (rule ar_time_bound_arith_sharp[OF kge2])
  show "\<forall>w. set w \<subseteq> Sigma_tm M
            \<longrightarrow> accepts_in_time_mttm M w (T (length w))
            \<longrightarrow> accepts_in_time_mttm ?M'
                  (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w)
                  (?d * ?k * T (length w))"
  proof (intro allI impI)
      fix w :: "'a list"
      assume w_sub: "set w \<subseteq> Sigma_tm M"
      assume m_acc: "accepts_in_time_mttm M w (T (length w))"
      from m_acc obtain n_T cMf where
          nT_le: "n_T \<le> T (length w)"
        and trace: "(init_config_mttm M w, cMf)
                      \<in> (mttm_step (delta_tm M)) ^^ n_T"
        and accf: "mt_state cMf = t_tm M"
        unfolding accepts_in_time_mttm_def by blast
      let ?c' = "init_config_mttm ?M' (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w)"
      have reach0: "(init_config_mttm M w, init_config_mttm M w)
                      \<in> (mttm_step (delta_tm M))\<^sup>*" by blast
      have sim: "ar_simulates M (init_config_mttm M w) ?c'"
        by (rule ar_simulates_init[OF vM w_sub s_neq_t s_neq_r])
      have posk: "ar_posk_consistent M (init_config_mttm M w) ?c'"
        by (rule ar_posk_consistent_init)
      have rbnd: "ar_at_read_boundary M ?c'"
        by (rule ar_at_read_boundary_init[OF vM])
      obtain m c'' where
          m_le: "m \<le> (?C * (5 * ?k + 2) + 2) * n_T"
        and run: "(?c', c'') \<in> (mttm_step (alphabet_reduce_delta M)) ^^ m"
        and st'': "mt_state c'' = (t_tm M, ar_accept_stage (bl_tm M))"
        using ar_simulation_phase_chunked
                [OF vM w_sub card_ge reach0 trace accf sim posk rbnd le_neq_bl]
        by blast
      have m_bound: "m \<le> ?d * ?k * T (length w)"
      proof -
        have "m \<le> (?C * (5 * ?k + 2) + 2) * n_T" by (rule m_le)
        also have "\<dots> \<le> (?d * ?k) * n_T" using bnd by (rule mult_le_mono1)
        also have "\<dots> \<le> (?d * ?k) * T (length w)"
          using nT_le by (rule mult_le_mono2)
        finally show ?thesis by (simp add: mult.assoc)
      qed
      have run': "(?c', c'') \<in> (mttm_step (delta_tm ?M')) ^^ m"
        using run by simp
      have st''': "mt_state c'' = t_tm ?M'" using st'' by simp
      show "accepts_in_time_mttm ?M'
              (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w)
              (?d * ?k * T (length w))"
        unfolding accepts_in_time_mttm_def
        using m_bound run' st''' by blast
  qed
qed

text \<open>Linear-time slowdown, classical existential form: reducing the tape
  alphabet to the fixed type \<open>sym4\<close> multiplies the running time by only a
  constant times the per-symbol block width.  The \<open>obtains\<close>-corollary of
  \<open>alphabet_reduce_time_explicit\<close> above, hiding its four explicit constants
  behind existentials instantiated at \<open>d = 6 \<cdot> k_tm M + 1\<close>,
  \<open>e = f = 0\<close>, and \<open>b = block_width (\<Gamma>_tm M)\<close>.\<close>

theorem alphabet_reduce_time:
  fixes M :: "('q, 'a) mttm"
    and T :: "nat \<Rightarrow> nat"
  assumes vM: "valid_mttm M"
      and s_neq_t: "s_tm M \<noteq> t_tm M"
      and s_neq_r: "s_tm M \<noteq> r_tm M"
      and le_neq_bl: "le_tm M \<noteq> bl_tm M"
      and card_ge: "card (\<Gamma>_tm M) \<ge> 4"
  obtains d e f b :: nat
    where "b \<ge> 1"
      and "\<forall>w. set w \<subseteq> Sigma_tm M
              \<longrightarrow> accepts_in_time_mttm M w (T (length w))
              \<longrightarrow> accepts_in_time_mttm
                    (alphabet_reduce M
                       :: ('q \<times> 'a ar_stage, sym4) mttm)
                    (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w)
                    (d * b * T (length w) + e * b * length w + f)"
proof -
  have P: "\<forall>w. set w \<subseteq> Sigma_tm M
              \<longrightarrow> accepts_in_time_mttm M w (T (length w))
              \<longrightarrow> accepts_in_time_mttm
                    (alphabet_reduce M
                       :: ('q \<times> 'a ar_stage, sym4) mttm)
                    (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w)
                    ((6 * k_tm M + 1) * block_width (\<Gamma>_tm M) * T (length w)
                       + 0 * block_width (\<Gamma>_tm M) * length w + 0)"
    using alphabet_reduce_time_explicit[OF vM s_neq_t s_neq_r le_neq_bl card_ge]
    by simp
  show ?thesis
  proof (rule that)
    show "(block_width (\<Gamma>_tm M) :: nat) \<ge> 1" by (rule block_width_pos)
  next
    show "\<forall>w. set w \<subseteq> Sigma_tm M
              \<longrightarrow> accepts_in_time_mttm M w (T (length w))
              \<longrightarrow> accepts_in_time_mttm
                    (alphabet_reduce M
                       :: ('q \<times> 'a ar_stage, sym4) mttm)
                    (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w)
                    ((6 * k_tm M + 1) * block_width (\<Gamma>_tm M) * T (length w)
                       + 0 * block_width (\<Gamma>_tm M) * length w + 0)"
      by (rule P)
  qed
qed

text \<open>Output alphabet: the reduced machine's tape alphabet is the
  whole finite type \<open>sym4\<close>, of cardinality exactly four.\<close>

theorem alphabet_reduce_produces_alphabet_size_4:
  shows "card (UNIV :: sym4 set) = 4"
  by (rule sym4_card)

text \<open>Tape-count preservation: the reduction re-encodes the tape
  alphabet symbol by symbol without changing the number of tapes, so
  the reduced machine has exactly \<open>M\<close>'s tape count.  This is the
  formal counterpart of the headline ``tape count preserved'', and the
  point of contrast with a tape-\<^emph>\<open>count\<close> reduction such as
  Book--Greibach--Wegbreit.\<close>

theorem alphabet_reduce_preserves_tape_count:
  fixes M :: "('q, 'a) mttm"
  shows "k_tm (alphabet_reduce M :: ('q \<times> 'a ar_stage, sym4) mttm)
           = k_tm M"
  by (cases M) (simp add: alphabet_reduce_def)

end
