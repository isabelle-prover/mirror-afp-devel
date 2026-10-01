theory AlphabetReduction_Determinism
  imports AlphabetReduction_Delta
begin

subsection \<open>Determinism preservation\<close>

text \<open>The alphabet-reduction combinator preserves determinism: if
  \<open>M\<close> is deterministic then so is \<open>alphabet_reduce M\<close>.  The
  language, time, and well-formedness theorems assume only
  well-formedness, so they already cover nondeterministic \<open>M\<close>;
  the result below extends the reduction \<^emph>\<open>up\<close> to deterministic
  machines, turning the determinism-agnostic construction into a
  determinism-preserving one.

  The argument is structural.  \<open>alphabet_reduce_delta M\<close> is the
  union of the five phase builders \<open>ar_delta_read\<close>,
  \<open>ar_delta_compute\<close>, \<open>ar_delta_write\<close>,
  \<open>ar_delta_advance\<close>, \<open>ar_delta_next\<close>, intersected with
  side conditions.  Each builder is single-valued: among the five, only
  \<open>ar_delta_compute\<close> consults \<open>M\<close>'s own transition
  relation, so it is the sole place \<open>M\<close>-determinism enters; the
  other four are single-valued by pure case analysis on the bit-counter,
  the tape index, and the read cell (\<open>ar_delta_next\<close> additionally
  needs \<open>t \<noteq> r\<close>, which \<open>valid_mttm\<close> supplies).  The five
  builders are keyed to disjoint source substep tags, so two transitions
  sharing a source land in the same builder; and intersection with the
  side conditions only shrinks the relation, so single-valuedness of the
  union transfers to \<open>alphabet_reduce_delta M\<close> and hence to the
  reduced machine.

  Each per-builder lemma below splits the \<^emph>\<open>source\<close> tuple into its
  arms with \<open>elim UnE\<close> and closes every arm against the full target
  builder: with the source fixed the arm discriminants are pinned, so the
  target collapses to one matching arm.  The \<open>block_width_pos\<close> fact
  (\<open>1 \<le> b\<close>) rules out the degenerate \<open>b = 0\<close>
  aliasing where the per-bit arm boundaries would coincide.
  Throughout, \<open>b\<close> abbreviates \<open>block_width \<Gamma>\<close> (the per-symbol cell width).\<close>

lemma ar_delta_read_functional:
  assumes h1: "(s, a, s1, a1, d1) \<in> ar_delta_read M"
      and h2: "(s, a, s2, a2, d2) \<in> ar_delta_read M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
  using h1 unfolding ar_delta_read_def
  by (elim UnE;
      use h2 block_width_pos[of "\<Gamma>_tm M"] in \<open>auto simp: ar_delta_read_def\<close>)

lemma ar_delta_write_functional:
  assumes h1: "(s, a, s1, a1, d1) \<in> ar_delta_write M"
      and h2: "(s, a, s2, a2, d2) \<in> ar_delta_write M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
  using h1 unfolding ar_delta_write_def
  by (elim UnE;
      use h2 block_width_pos[of "\<Gamma>_tm M"] in \<open>auto simp: ar_delta_write_def\<close>)

lemma ar_delta_advance_functional:
  assumes h1: "(s, a, s1, a1, d1) \<in> ar_delta_advance M"
      and h2: "(s, a, s2, a2, d2) \<in> ar_delta_advance M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
  using h1 unfolding ar_delta_advance_def
  by (elim UnE;
      use h2 block_width_pos[of "\<Gamma>_tm M"] in \<open>auto simp: ar_delta_advance_def\<close>)

lemma ar_delta_next_functional:
  assumes tr: "t_tm M \<noteq> r_tm M"
      and h1: "(s, a, s1, a1, d1) \<in> ar_delta_next M"
      and h2: "(s, a, s2, a2, d2) \<in> ar_delta_next M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
  using h1 unfolding ar_delta_next_def
  by (elim UnE; use h2 tr in \<open>auto simp: ar_delta_next_def\<close>)

text \<open>The compute substep is the one place \<open>M\<close>'s transition
  relation enters \<open>alphabet_reduce_delta\<close>: a single
  \<open>\<delta>'\<close>-tuple per \<open>M\<close>-\<open>\<delta>\<close>-tuple, matching the
  source-stage decoded symbol vector \<open>buf\<close>.  Single-valuedness
  here is exactly \<open>M\<close>-determinism transported through that match.\<close>

lemma ar_delta_compute_functional:
  fixes M :: "('q, 'a) mttm"
  assumes det: "det_mttm M"
      and h1: "(s, a, s1, a1, d1) \<in> ar_delta_compute M"
      and h2: "(s, a, s2, a2, d2) \<in> ar_delta_compute M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
proof -
  from h1 obtain qa buf qa' m_aa' m_da tka ia dveca poska where
        sa:  "s = (qa, AR_SimCompute, tka, ia, buf, dveca, poska)"
    and s1a: "s1 = (qa', AR_SimWrite, 0, 0, m_aa', m_da, poska)"
    and a1a: "a1 = a"
    and d1a: "d1 = (\<lambda>_. dir.N)"
    and ma:  "(qa, buf, qa', m_aa', m_da) \<in> delta_tm M"
    unfolding ar_delta_compute_def by auto
  from h2 obtain qb bufb qb' m_ab' m_db tkb ib dvecb poskb where
        sb:  "s = (qb, AR_SimCompute, tkb, ib, bufb, dvecb, poskb)"
    and s2b: "s2 = (qb', AR_SimWrite, 0, 0, m_ab', m_db, poskb)"
    and a2b: "a2 = a"
    and d2b: "d2 = (\<lambda>_. dir.N)"
    and mb:  "(qb, bufb, qb', m_ab', m_db) \<in> delta_tm M"
    unfolding ar_delta_compute_def by auto
  from sa sb have qeq: "qb = qa" and bufeq: "bufb = buf"
    and poskeq: "poskb = poska"
    by simp_all
  have mb': "(qa, buf, qb', m_ab', m_db) \<in> delta_tm M"
    using mb qeq bufeq by simp
  have "(qa', m_aa', m_da) = (qb', m_ab', m_db)"
    using ma mb' det unfolding det_mttm_def by blast
  hence qe: "qa' = qb'" and mae: "m_aa' = m_ab'" and mde: "m_da = m_db"
    by simp_all
  show ?thesis
    using s1a s2b a1a a2b d1a d2b poskeq qe mae mde by simp
qed

text \<open>Dispatch on the source substep tag: the five builders have
  pairwise-disjoint source tags, so two transitions out of a common
  source \<open>s\<close> are governed by the same builder, and per-builder
  single-valuedness applies.  The two halt tags carry no transition.\<close>

lemma alphabet_reduce_delta_functional:
  fixes M :: "('q, 'a) mttm"
  assumes valM: "valid_mttm M"
      and detM: "det_mttm M"
      and h1: "(s, a, s1, a1, d1) \<in> alphabet_reduce_delta M"
      and h2: "(s, a, s2, a2, d2) \<in> alphabet_reduce_delta M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
proof -
  have tr: "t_tm M \<noteq> r_tm M" by (rule valid_mttm_t_neq_r[OF valM])
  from h1 have u1: "(s, a, s1, a1, d1) \<in>
      ar_delta_read M \<union> ar_delta_compute M \<union> ar_delta_write M
        \<union> ar_delta_advance M \<union> ar_delta_next M"
    unfolding alphabet_reduce_delta_def by blast
  from h2 have u2: "(s, a, s2, a2, d2) \<in>
      ar_delta_read M \<union> ar_delta_compute M \<union> ar_delta_write M
        \<union> ar_delta_advance M \<union> ar_delta_next M"
    unfolding alphabet_reduce_delta_def by blast
  show ?thesis
  proof (cases "fst (snd s)")
    case AR_SimRead
    have e1: "(s, a, s1, a1, d1) \<in> ar_delta_read M"
      using u1 AR_SimRead
      by (auto simp: ar_delta_compute_def ar_delta_write_def
                     ar_delta_advance_def ar_delta_next_def)
    have e2: "(s, a, s2, a2, d2) \<in> ar_delta_read M"
      using u2 AR_SimRead
      by (auto simp: ar_delta_compute_def ar_delta_write_def
                     ar_delta_advance_def ar_delta_next_def)
    show ?thesis by (rule ar_delta_read_functional[OF e1 e2])
  next
    case AR_SimCompute
    have e1: "(s, a, s1, a1, d1) \<in> ar_delta_compute M"
      using u1 AR_SimCompute
      by (auto simp: ar_delta_read_def ar_delta_write_def
                     ar_delta_advance_def ar_delta_next_def)
    have e2: "(s, a, s2, a2, d2) \<in> ar_delta_compute M"
      using u2 AR_SimCompute
      by (auto simp: ar_delta_read_def ar_delta_write_def
                     ar_delta_advance_def ar_delta_next_def)
    show ?thesis by (rule ar_delta_compute_functional[OF detM e1 e2])
  next
    case AR_SimWrite
    have e1: "(s, a, s1, a1, d1) \<in> ar_delta_write M"
      using u1 AR_SimWrite
      by (auto simp: ar_delta_read_def ar_delta_compute_def
                     ar_delta_advance_def ar_delta_next_def)
    have e2: "(s, a, s2, a2, d2) \<in> ar_delta_write M"
      using u2 AR_SimWrite
      by (auto simp: ar_delta_read_def ar_delta_compute_def
                     ar_delta_advance_def ar_delta_next_def)
    show ?thesis by (rule ar_delta_write_functional[OF e1 e2])
  next
    case AR_SimAdvance
    have e1: "(s, a, s1, a1, d1) \<in> ar_delta_advance M"
      using u1 AR_SimAdvance
      by (auto simp: ar_delta_read_def ar_delta_compute_def
                     ar_delta_write_def ar_delta_next_def)
    have e2: "(s, a, s2, a2, d2) \<in> ar_delta_advance M"
      using u2 AR_SimAdvance
      by (auto simp: ar_delta_read_def ar_delta_compute_def
                     ar_delta_write_def ar_delta_next_def)
    show ?thesis by (rule ar_delta_advance_functional[OF e1 e2])
  next
    case AR_SimNext
    have e1: "(s, a, s1, a1, d1) \<in> ar_delta_next M"
      using u1 AR_SimNext
      by (auto simp: ar_delta_read_def ar_delta_compute_def
                     ar_delta_write_def ar_delta_advance_def)
    have e2: "(s, a, s2, a2, d2) \<in> ar_delta_next M"
      using u2 AR_SimNext
      by (auto simp: ar_delta_read_def ar_delta_compute_def
                     ar_delta_write_def ar_delta_advance_def)
    show ?thesis by (rule ar_delta_next_functional[OF tr e1 e2])
  next
    case AR_HaltAccept
    with u1 show ?thesis
      by (auto simp: ar_delta_read_def ar_delta_compute_def ar_delta_write_def
                     ar_delta_advance_def ar_delta_next_def)
  next
    case AR_HaltReject
    with u1 show ?thesis
      by (auto simp: ar_delta_read_def ar_delta_compute_def ar_delta_write_def
                     ar_delta_advance_def ar_delta_next_def)
  qed
qed

text \<open>Headline result: the alphabet-reduction combinator carries
  determinism of \<open>M\<close> over to \<open>alphabet_reduce M\<close>.  With the
  determinism-agnostic language / time / output theorems this completes
  the picture for deterministic machines.\<close>

theorem alphabet_reduce_det:
  fixes M :: "('q, 'a) mttm"
  assumes valM: "valid_mttm M"
      and detM: "det_mttm M"
  shows "det_mttm (alphabet_reduce M :: ('q \<times> 'a ar_stage, sym4) mttm)"
  unfolding det_mttm_def
proof (intro allI impI)
  fix q a p1 b1 dd1 p2 b2 dd2
  assume "(q, a, p1, b1, dd1) \<in> delta_tm (alphabet_reduce M)"
     and "(q, a, p2, b2, dd2) \<in> delta_tm (alphabet_reduce M)"
  hence m1: "(q, a, p1, b1, dd1) \<in> alphabet_reduce_delta M"
    and m2: "(q, a, p2, b2, dd2) \<in> alphabet_reduce_delta M"
    by simp_all
  from alphabet_reduce_delta_functional[OF valM detM m1 m2]
  show "(p1, b1, dd1) = (p2, b2, dd2)" by simp
qed

end
