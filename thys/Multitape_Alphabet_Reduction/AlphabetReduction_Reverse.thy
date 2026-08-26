theory AlphabetReduction_Reverse
  imports AlphabetReduction_Theorems
begin

section \<open>Alphabet reduction: reverse language inclusion\<close>

text \<open>The reverse leg of \<open>alphabet_reduce_language\<close>:
  \<open>encode_input_ar (\<Gamma>_tm M) (bl_tm M) w \<in> Lang_mttm (alphabet_reduce M)
   \<Longrightarrow> w \<in> Lang_mttm M\<close>, the converse of the proven
  \<open>alphabet_reduce_language_forward\<close>.

  Unlike AE's reverse arm, which restricts to \<open>det_mttm M\<close> and
  closes via chain uniqueness (Path C), AR proves this
  unconditionally — deterministic and nondeterministic \<open>M\<close>
  alike.  The counterexample probe is negative: AR's
  nondeterminism gateway \<open>ar_delta_compute\<close> is a direct
  single-step embedding of \<open>delta_tm M\<close> (one substrate tuple per
  \<open>M\<close>-tuple, no AE-style \<open>m_steps_buffered\<close> slack), so every
  accepting \<open>M'\<close>-path decodes branch-by-branch to a genuine
  accepting \<open>M\<close>-path.

  Strategy (Strategy B, direct backward inversion): a per-cycle
  backward step lemma reads the \<open>M\<close>-transition straight off the
  compute tuple on the given \<open>M'\<close>-path and reuses the forward
  arm's invariants \<open>ar_simulates\<close>, \<open>ar_posk_consistent\<close>,
  \<open>ar_at_read_boundary\<close> read backward; a backward chunked engine
  aggregates the per-cycle steps into an \<open>M\<close>-run.
  Throughout, \<open>b\<close> abbreviates \<open>block_width \<Gamma>\<close> (the per-symbol cell width).\<close>

subsection \<open>Terminal accept configuration\<close>

text \<open>Base case of the backward engine: the accept state
  \<open>t_tm (alphabet_reduce M)\<close> is terminal.  A valid machine never
  steps from its accept state (substrate \<open>mttm_step_src_neq_t\<close>),
  and \<open>alphabet_reduce M\<close> is valid by \<open>alphabet_reduce_wf\<close>;
  its accept state is \<open>(t_tm M, ar_accept_stage (bl_tm M))\<close> by
  \<open>alphabet_reduce_accept\<close>.

  Itself currently uncalled: the backward engine kills reject boundaries
  mid-trace via \<open>ar_reject_terminal\<close>, not accept ones; retained as the
  documented half of the accept/reject terminal pair.\<close>

lemma ar_accept_terminal:
  fixes M :: "('q, 'a) mttm"
    and c c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM:      "valid_mttm M"
      and card_ge: "card (\<Gamma>_tm M) \<ge> 4"
      and step:    "(c, c') \<in> mttm_step (alphabet_reduce_delta M)"
  shows "mt_state c \<noteq> (t_tm M, ar_accept_stage (bl_tm M))"
proof -
  let ?M' = "alphabet_reduce M :: ('q \<times> 'a ar_stage, sym4) mttm"
  have valM': "valid_mttm ?M'" by (rule alphabet_reduce_wf[OF vM card_ge])
  have step': "(c, c') \<in> mttm_step (delta_tm ?M')" using step by simp
  have "mt_state c \<noteq> t_tm ?M'" by (rule mttm_step_src_neq_t[OF valM' step'])
  thus ?thesis by simp
qed

text \<open>Reject companion of \<open>ar_accept_terminal\<close>: the reject state
  \<open>r_tm (alphabet_reduce M) = (r_tm M, ar_reject_stage (bl_tm M))\<close>
  (by \<open>alphabet_reduce_reject\<close>) is terminal too (substrate
  \<open>mttm_step_src_neq_r\<close>).  The backward engine uses it to kill a
  reject boundary reached mid-trace: the trace runs to the accept
  config, so a reject config can carry no outgoing step.\<close>

lemma ar_reject_terminal:
  fixes M :: "('q, 'a) mttm"
    and c c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM:      "valid_mttm M"
      and card_ge: "card (\<Gamma>_tm M) \<ge> 4"
      and step:    "(c, c') \<in> mttm_step (alphabet_reduce_delta M)"
  shows "mt_state c \<noteq> (r_tm M, ar_reject_stage (bl_tm M))"
proof -
  let ?M' = "alphabet_reduce M :: ('q \<times> 'a ar_stage, sym4) mttm"
  have valM': "valid_mttm ?M'" by (rule alphabet_reduce_wf[OF vM card_ge])
  have step': "(c, c') \<in> mttm_step (delta_tm ?M')" using step by simp
  have "mt_state c \<noteq> r_tm ?M'" by (rule mttm_step_src_neq_r[OF valM' step'])
  thus ?thesis by simp
qed

subsection \<open>Source substep-tags partition the substep relations\<close>

text \<open>Each of the five substep relations carries a uniform source
  substep-tag (\<open>fst (snd s)\<close> for a source state \<open>s = (q, stg)\<close>),
  and the five tags are pairwise distinct datatype constructors.  This
  is the structural fact every step-inversion lemma rests on: a step
  whose source is at substep \<open>X\<close> can only come from the relation
  whose sources carry tag \<open>X\<close>.\<close>

lemma ar_delta_read_src:
  "(s, a, s', a', d) \<in> ar_delta_read M \<Longrightarrow> fst (snd s) = AR_SimRead"
  by (auto simp: ar_delta_read_def)

lemma ar_delta_compute_src:
  "(s, a, s', a', d) \<in> ar_delta_compute M \<Longrightarrow> fst (snd s) = AR_SimCompute"
  by (auto simp: ar_delta_compute_def)

lemma ar_delta_write_src:
  "(s, a, s', a', d) \<in> ar_delta_write M \<Longrightarrow> fst (snd s) = AR_SimWrite"
  by (auto simp: ar_delta_write_def)

lemma ar_delta_advance_src:
  "(s, a, s', a', d) \<in> ar_delta_advance M \<Longrightarrow> fst (snd s) = AR_SimAdvance"
  by (auto simp: ar_delta_advance_def)

lemma ar_delta_next_src:
  "(s, a, s', a', d) \<in> ar_delta_next M \<Longrightarrow> fst (snd s) = AR_SimNext"
  by (auto simp: ar_delta_next_def)

subsection \<open>Destination substep-tags carve the cycle's substep order\<close>

text \<open>Each substep relation's destination tag is confined to a
  small set: read loops to itself or transitions to compute; compute
  is the unique non-deterministic step and lands at write; write
  loops or advances; advance loops or hands off to next; next closes
  the cycle (back to read) or dispatches to a halt-coerced
  configuration.  These five facts encode the substep transition
  graph and underpin the chain-shape arguments used in the reverse
  arm's pinning lemmas.\<close>

lemma ar_delta_read_dest:
  "(s, a, s', a', d) \<in> ar_delta_read M \<Longrightarrow>
     fst (snd s') = AR_SimRead \<or> fst (snd s') = AR_SimCompute"
  by (auto simp: ar_delta_read_def)

lemma ar_delta_compute_dest:
  "(s, a, s', a', d) \<in> ar_delta_compute M \<Longrightarrow> fst (snd s') = AR_SimWrite"
  by (auto simp: ar_delta_compute_def)

lemma ar_delta_write_dest:
  "(s, a, s', a', d) \<in> ar_delta_write M \<Longrightarrow>
     fst (snd s') = AR_SimWrite \<or> fst (snd s') = AR_SimAdvance"
  by (auto simp: ar_delta_write_def)

lemma ar_delta_advance_dest:
  "(s, a, s', a', d) \<in> ar_delta_advance M \<Longrightarrow>
     fst (snd s') = AR_SimAdvance \<or> fst (snd s') = AR_SimNext"
  by (auto simp: ar_delta_advance_def)

lemma ar_delta_next_dest:
  "(s, a, s', a', d) \<in> ar_delta_next M \<Longrightarrow>
     fst (snd s') = AR_SimRead \<or> fst (snd s') = AR_HaltAccept
        \<or> fst (snd s') = AR_HaltReject"
  by (auto simp: ar_delta_next_def ar_accept_stage_def ar_reject_stage_def)

text \<open>Union-disambiguation: a tuple in \<open>alphabet_reduce_delta M\<close>
  whose source is at \<open>AR_SimCompute\<close> must lie in the compute
  relation \<open>ar_delta_compute M\<close>.  The intersection filters of
  \<open>alphabet_reduce_delta\<close> (\<open>\<delta>LE\<close> and the valid-stage
  guards) only shrink the union, so membership of the union is all we
  need; the other four source-tag lemmas rule out the other disjuncts
  by constructor-distinctness.\<close>

lemma ar_delta_compute_from_src:
  assumes mem: "(s, a, s', a', d) \<in> alphabet_reduce_delta M"
      and src: "fst (snd s) = AR_SimCompute"
  shows "(s, a, s', a', d) \<in> ar_delta_compute M"
proof -
  from mem
  have u: "(s, a, s', a', d) \<in> ar_delta_read M \<union> ar_delta_compute M
              \<union> ar_delta_write M \<union> ar_delta_advance M \<union> ar_delta_next M"
    unfolding alphabet_reduce_delta_def by blast
  have nr: "(s, a, s', a', d) \<notin> ar_delta_read M"
  proof
    assume "(s, a, s', a', d) \<in> ar_delta_read M"
    from ar_delta_read_src[OF this] src show False by simp
  qed
  have nw: "(s, a, s', a', d) \<notin> ar_delta_write M"
  proof
    assume "(s, a, s', a', d) \<in> ar_delta_write M"
    from ar_delta_write_src[OF this] src show False by simp
  qed
  have nad: "(s, a, s', a', d) \<notin> ar_delta_advance M"
  proof
    assume "(s, a, s', a', d) \<in> ar_delta_advance M"
    from ar_delta_advance_src[OF this] src show False by simp
  qed
  have nx: "(s, a, s', a', d) \<notin> ar_delta_next M"
  proof
    assume "(s, a, s', a', d) \<in> ar_delta_next M"
    from ar_delta_next_src[OF this] src show False by simp
  qed
  from u nr nw nad nx show ?thesis by blast
qed

subsection \<open>Compute-step inversion\<close>

text \<open>The keystone of the reverse arm: a single \<open>M'\<close>-step out of
  an \<open>AR_SimCompute\<close> configuration reads the simulated
  \<open>M\<close>-transition straight off the compute tuple.  Because
  \<open>ar_delta_compute\<close> is a direct single-step embedding of
  \<open>delta_tm M\<close>, the inversion yields a genuine
  \<open>(q, buf, q', m_a', m_d) \<in> delta_tm M\<close> with no chain-uniqueness
  or determinism assumption — this is where AR's ND-generality is
  earned.  Compute neither writes nor moves: the tape and head
  positions are unchanged (read symbol equals write symbol, direction
  \<open>N\<close>).\<close>

lemma ar_compute_step_inv_sub:
  fixes M :: "('q, 'a) mttm"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes step: "(c', c'') \<in> mttm_step (ar_delta_compute M)"
      and stg:  "mt_state c' = (q, AR_SimCompute, tk, i, buf, dvec, posk)"
  obtains q' m_a' m_d where
      "(q, buf, q', m_a', m_d) \<in> delta_tm M"
    and "mt_state c'' = (q', AR_SimWrite, 0, 0, m_a', m_d, posk)"
    and "mt_tape c'' = mt_tape c'"
    and "mt_pos c'' = mt_pos c'"
proof -
  from step obtain S ts n S'' aw dir where
      c'_eq:   "c' = Config\<^sub>M S ts n"
    and c''_eq: "c'' = Config\<^sub>M S'' (\<lambda>k. (ts k)(n k := aw k))
                        (\<lambda>k. go_dir (dir k) (n k))"
    and rel:   "(S, (\<lambda>k. ts k (n k)), S'', aw, dir)
                   \<in> ar_delta_compute M"
    by (auto elim: mttm_step.cases)
  have S_eq: "S = (q, AR_SimCompute, tk, i, buf, dvec, posk)"
    using stg c'_eq by simp
  have crel: "((q, AR_SimCompute, tk, i, buf, dvec, posk),
                 (\<lambda>k. ts k (n k)), S'', aw, dir) \<in> ar_delta_compute M"
    using rel S_eq by simp
  from crel obtain q' m_a' m_d where
      mdelta:  "(q, buf, q', m_a', m_d) \<in> delta_tm M"
    and S''_eq: "S'' = (q', AR_SimWrite, 0, 0, m_a', m_d, posk)"
    and aw_eq: "aw = (\<lambda>k. ts k (n k))"
    and dir_eq: "dir = (\<lambda>_. dir.N)"
    unfolding ar_delta_compute_def by auto
  have state: "mt_state c'' = (q', AR_SimWrite, 0, 0, m_a', m_d, posk)"
    using c''_eq S''_eq by simp
  have tape: "mt_tape c'' = mt_tape c'"
  proof -
    have "mt_tape c'' = (\<lambda>k. (ts k)(n k := aw k))" using c''_eq by simp
    also have "\<dots> = ts" by (simp add: aw_eq fun_upd_triv)
    finally show ?thesis using c'_eq by simp
  qed
  have pos: "mt_pos c'' = mt_pos c'"
  proof -
    have "mt_pos c'' = (\<lambda>k. go_dir (dir k) (n k))" using c''_eq by simp
    also have "\<dots> = n" by (simp add: dir_eq)
    finally show ?thesis using c'_eq by simp
  qed
  show ?thesis by (rule that[OF mdelta state tape pos])
qed

text \<open>The union-step face of the inversion: lift the union step into
  the compute sub-relation (\<open>ar_step_compute_lift\<close>) and invert there.
  Used by the forward walker preservation \<open>ar_walker_step_from_at_compute\<close>;
  the reverse cycle-close inverts the walker's own sub-relation compute
  step directly via \<open>ar_compute_step_inv_sub\<close>.\<close>

lemma ar_compute_step_inv:
  fixes M :: "('q, 'a) mttm"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes step: "(c', c'') \<in> mttm_step (alphabet_reduce_delta M)"
      and stg:  "mt_state c' = (q, AR_SimCompute, tk, i, buf, dvec, posk)"
  obtains q' m_a' m_d where
      "(q, buf, q', m_a', m_d) \<in> delta_tm M"
    and "mt_state c'' = (q', AR_SimWrite, 0, 0, m_a', m_d, posk)"
    and "mt_tape c'' = mt_tape c'"
    and "mt_pos c'' = mt_pos c'"
proof -
  from step obtain S ts n S'' aw dir where
      c'_eq:   "c' = Config\<^sub>M S ts n"
    and c''_eq: "c'' = Config\<^sub>M S'' (\<lambda>k. (ts k)(n k := aw k))
                        (\<lambda>k. go_dir (dir k) (n k))"
    and rel:   "(S, (\<lambda>k. ts k (n k)), S'', aw, dir)
                   \<in> alphabet_reduce_delta M"
    by (auto elim: mttm_step.cases)
  have src: "fst (snd S) = AR_SimCompute" using stg c'_eq by simp
  have crel: "(S, (\<lambda>k. ts k (n k)), S'', aw, dir) \<in> ar_delta_compute M"
    by (rule ar_delta_compute_from_src[OF rel src])
  have step_explicit:
      "(Config\<^sub>M S ts n, Config\<^sub>M S'' (\<lambda>k. (ts k)(n k := aw k))
          (\<lambda>k. go_dir (dir k) (n k))) \<in> mttm_step (ar_delta_compute M)"
    using crel by (rule mttm_step.step)
  have sub: "(c', c'') \<in> mttm_step (ar_delta_compute M)"
    using step_explicit c'_eq c''_eq by simp
  show thesis
  proof (rule ar_compute_step_inv_sub[OF sub stg])
    fix q' m_a' m_d
    assume "(q, buf, q', m_a', m_d) \<in> delta_tm M"
       and "mt_state c'' = (q', AR_SimWrite, 0, 0, m_a', m_d, posk)"
       and "mt_tape c'' = mt_tape c'"
       and "mt_pos c'' = mt_pos c'"
    thus thesis by (rule that)
  qed
qed

subsection \<open>Next-step inversion (cycle closure / halt dispatch)\<close>

text \<open>Source disambiguation for \<open>AR_SimNext\<close>, mirroring
  \<open>ar_delta_compute_from_src\<close>.\<close>

lemma ar_delta_next_from_src:
  assumes mem: "(s, a, s', a', d) \<in> alphabet_reduce_delta M"
      and src: "fst (snd s) = AR_SimNext"
  shows "(s, a, s', a', d) \<in> ar_delta_next M"
proof -
  from mem
  have u: "(s, a, s', a', d) \<in> ar_delta_read M \<union> ar_delta_compute M
              \<union> ar_delta_write M \<union> ar_delta_advance M \<union> ar_delta_next M"
    unfolding alphabet_reduce_delta_def by blast
  have nr: "(s, a, s', a', d) \<notin> ar_delta_read M"
  proof
    assume "(s, a, s', a', d) \<in> ar_delta_read M"
    from ar_delta_read_src[OF this] src show False by simp
  qed
  have nc: "(s, a, s', a', d) \<notin> ar_delta_compute M"
  proof
    assume "(s, a, s', a', d) \<in> ar_delta_compute M"
    from ar_delta_compute_src[OF this] src show False by simp
  qed
  have nw: "(s, a, s', a', d) \<notin> ar_delta_write M"
  proof
    assume "(s, a, s', a', d) \<in> ar_delta_write M"
    from ar_delta_write_src[OF this] src show False by simp
  qed
  have nad: "(s, a, s', a', d) \<notin> ar_delta_advance M"
  proof
    assume "(s, a, s', a', d) \<in> ar_delta_advance M"
    from ar_delta_advance_src[OF this] src show False by simp
  qed
  from u nr nc nw nad show ?thesis by blast
qed

text \<open>A single \<open>M'\<close>-step out of an \<open>AR_SimNext\<close>
  configuration neither writes nor moves, and dispatches on the
  simulated \<open>M\<close>-state \<open>q\<close>: continue to the next
  \<open>AR_SimRead\<close> boundary when \<open>q\<close> is non-halting, or land
  in the accept/reject halt stage when \<open>q\<close> is \<open>M\<close>'s
  accept/reject state.  The accept landing is exactly
  \<open>t_tm (alphabet_reduce M)\<close>.\<close>

lemma ar_next_step_inv:
  fixes M :: "('q, 'a) mttm"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes step: "(c', c'') \<in> mttm_step (alphabet_reduce_delta M)"
      and stg:  "mt_state c' = (q, AR_SimNext, tk, i, buf, dvec, posk)"
  shows "mt_tape c'' = mt_tape c' \<and> mt_pos c'' = mt_pos c'
         \<and> ((q \<notin> {t_tm M, r_tm M}
               \<and> mt_state c'' = (q, AR_SimRead, 0, 0, buf, dvec, posk))
            \<or> (q = t_tm M
               \<and> mt_state c'' = (t_tm M, ar_accept_stage (bl_tm M)))
            \<or> (q = r_tm M
               \<and> mt_state c'' = (r_tm M, ar_reject_stage (bl_tm M))))"
proof -
  from step obtain S ts n S'' aw dir where
      c'_eq:   "c' = Config\<^sub>M S ts n"
    and c''_eq: "c'' = Config\<^sub>M S'' (\<lambda>k. (ts k)(n k := aw k))
                        (\<lambda>k. go_dir (dir k) (n k))"
    and rel:   "(S, (\<lambda>k. ts k (n k)), S'', aw, dir)
                   \<in> alphabet_reduce_delta M"
    by (auto elim: mttm_step.cases)
  have S_eq: "S = (q, AR_SimNext, tk, i, buf, dvec, posk)"
    using stg c'_eq by simp
  have src: "fst (snd S) = AR_SimNext" using S_eq by simp
  have nrel: "((q, AR_SimNext, tk, i, buf, dvec, posk),
                 (\<lambda>k. ts k (n k)), S'', aw, dir) \<in> ar_delta_next M"
    using ar_delta_next_from_src[OF rel src] S_eq by simp
  have core: "aw = (\<lambda>k. ts k (n k)) \<and> dir = (\<lambda>_. dir.N)
       \<and> ((q \<notin> {t_tm M, r_tm M}
              \<and> S'' = (q, AR_SimRead, 0, 0, buf, dvec, posk))
          \<or> (q = t_tm M \<and> S'' = (t_tm M, ar_accept_stage (bl_tm M)))
          \<or> (q = r_tm M \<and> S'' = (r_tm M, ar_reject_stage (bl_tm M))))"
    using nrel
    unfolding ar_delta_next_def ar_accept_stage_def ar_reject_stage_def
    by auto
  have tape: "mt_tape c'' = mt_tape c'"
  proof -
    have "mt_tape c'' = (\<lambda>k. (ts k)(n k := aw k))" using c''_eq by simp
    also have "\<dots> = ts" using core by (simp add: fun_upd_triv)
    finally show ?thesis using c'_eq by simp
  qed
  have pos: "mt_pos c'' = mt_pos c'"
  proof -
    have "mt_pos c'' = (\<lambda>k. go_dir (dir k) (n k))" using c''_eq by simp
    also have "\<dots> = n" using core by simp
    finally show ?thesis using c'_eq by simp
  qed
  have st: "mt_state c'' = S''" using c''_eq by simp
  show ?thesis using tape pos core st by simp
qed

subsection \<open>Determinism of the read substep\<close>

text \<open>The read relation is a *function* of (source state, read
  symbol): for a fixed source \<open>s\<close> and read vector \<open>a\<close> the
  target state, written vector, and direction are uniquely determined.
  The seven arms partition by the bit-counter \<open>i\<close>, then within an
  \<open>i\<close>-class by \<open>posk tk\<close> / \<open>a tk\<close> / \<open>is_last_k M tk\<close>.
  The one non-obvious exclusion is arm 4 (\<open>i = Suc 0\<close>) versus arms
  6/7 (\<open>i = Suc (b)\<close>): these collide only if
  \<open>b = 0\<close>, ruled out by \<open>block_width_pos\<close> (which is
  therefore load-bearing here, not decorative).\<close>

lemma ar_delta_read_func:
  fixes M :: "('q, 'a) mttm"
  assumes "(s, a, s\<^sub>1, a\<^sub>1, d\<^sub>1) \<in> ar_delta_read M"
      and "(s, a, s\<^sub>2, a\<^sub>2, d\<^sub>2) \<in> ar_delta_read M"
  shows "(s\<^sub>1, a\<^sub>1, d\<^sub>1) = (s\<^sub>2, a\<^sub>2, d\<^sub>2)"
  using assms block_width_pos[of "\<Gamma>_tm M"]
  by (auto simp: ar_delta_read_def)

text \<open>Write is a function of (source, read vector): the LE arms
  (\<open>buf tk = le\<close>) split from the proper arms by the buf cell,
  and the proper back-walk / forward-write / boundary arms partition by
  the bit-counter ranges \<open>[0, b-1]\<close>, \<open>[b, 2b-2]\<close>,
  \<open>{2b-1}\<close>, separated arithmetically; \<open>is_last_k\<close> splits
  the last-tape arms.\<close>

lemma ar_delta_write_func:
  fixes M :: "('q, 'a) mttm"
  assumes "(s, a, s\<^sub>1, a\<^sub>1, d\<^sub>1) \<in> ar_delta_write M"
      and "(s, a, s\<^sub>2, a\<^sub>2, d\<^sub>2) \<in> ar_delta_write M"
  shows "(s\<^sub>1, a\<^sub>1, d\<^sub>1) = (s\<^sub>2, a\<^sub>2, d\<^sub>2)"
  using assms
  by (auto simp: ar_delta_write_def)

text \<open>Advance is a function of (source, read vector).  The stepping
  arm (\<open>Suc i < ar_disp b (dvec tk) (posk tk)\<close>) is excluded from
  the \<open>R\<close>-direction boundary sub-case by
  \<open>ar_disp _ dir.R _ = 0\<close> (the first \<open>ar_disp\<close>
  equation), and from the non-\<open>R\<close> boundary by \<open><\<close>
  versus \<open>=\<close> on the displacement; \<open>is_last_k\<close> splits the
  two boundary arms.\<close>

lemma ar_delta_advance_func:
  fixes M :: "('q, 'a) mttm"
  assumes "(s, a, s\<^sub>1, a\<^sub>1, d\<^sub>1) \<in> ar_delta_advance M"
      and "(s, a, s\<^sub>2, a\<^sub>2, d\<^sub>2) \<in> ar_delta_advance M"
  shows "(s\<^sub>1, a\<^sub>1, d\<^sub>1) = (s\<^sub>2, a\<^sub>2, d\<^sub>2)"
  using assms
  by (auto simp: ar_delta_advance_def)

text \<open>Next is a function of the source: the continue / accept /
  reject arms partition on the simulated \<open>M\<close>-state \<open>q\<close> by
  \<open>q \<notin> {t, r}\<close> / \<open>q = t\<close> / \<open>q = r\<close>, mutually
  exclusive precisely because \<open>valid_mttm M\<close> supplies
  \<open>t_tm M \<noteq> r_tm M\<close>.

  Currently uncalled: the \<open>next\<close> substep is the cycle closer, handled
  by bespoke inversion (\<open>ar_next_step_inv\<close>) rather than functional
  pinning, so this member of the per-substep determinism family goes
  unused; kept to keep that family complete.\<close>

lemma ar_delta_next_func:
  fixes M :: "('q, 'a) mttm"
  assumes vM: "valid_mttm M"
      and "(s, a, s\<^sub>1, a\<^sub>1, d\<^sub>1) \<in> ar_delta_next M"
      and "(s, a, s\<^sub>2, a\<^sub>2, d\<^sub>2) \<in> ar_delta_next M"
  shows "(s\<^sub>1, a\<^sub>1, d\<^sub>1) = (s\<^sub>2, a\<^sub>2, d\<^sub>2)"
proof -
  have tr: "t_tm M \<noteq> r_tm M" using vM by (cases M) auto
  show ?thesis using assms(2,3) tr by (auto simp: ar_delta_next_def)
qed

subsection \<open>Source disambiguation for the remaining substeps\<close>

text \<open>Source disambiguation for the remaining three substeps,
  completing the \<open>from_src\<close> family alongside
  \<open>ar_delta_compute_from_src\<close> / \<open>ar_delta_next_from_src\<close>.\<close>

lemma ar_delta_read_from_src:
  assumes "(s, a, s', a', d) \<in> alphabet_reduce_delta M"
      and "fst (snd s) = AR_SimRead"
  shows "(s, a, s', a', d) \<in> ar_delta_read M"
  using assms unfolding alphabet_reduce_delta_def
  by (auto dest: ar_delta_compute_src ar_delta_write_src
                 ar_delta_advance_src ar_delta_next_src)

lemma ar_delta_write_from_src:
  assumes "(s, a, s', a', d) \<in> alphabet_reduce_delta M"
      and "fst (snd s) = AR_SimWrite"
  shows "(s, a, s', a', d) \<in> ar_delta_write M"
  using assms unfolding alphabet_reduce_delta_def
  by (auto dest: ar_delta_read_src ar_delta_compute_src
                 ar_delta_advance_src ar_delta_next_src)

lemma ar_delta_advance_from_src:
  assumes "(s, a, s', a', d) \<in> alphabet_reduce_delta M"
      and "fst (snd s) = AR_SimAdvance"
  shows "(s, a, s', a', d) \<in> ar_delta_advance M"
  using assms unfolding alphabet_reduce_delta_def
  by (auto dest: ar_delta_read_src ar_delta_compute_src
                 ar_delta_write_src ar_delta_next_src)

text \<open>Every \<open>alphabet_reduce_delta\<close> tuple has its source at one
  of the five substep tags (the halt tags never appear as sources).\<close>

lemma alphabet_reduce_delta_src_tag:
  assumes "(s, a, s', a', d) \<in> alphabet_reduce_delta M"
  shows "fst (snd s) \<in> {AR_SimRead, AR_SimCompute, AR_SimWrite,
                          AR_SimAdvance, AR_SimNext}"
  using assms unfolding alphabet_reduce_delta_def
  by (auto dest: ar_delta_read_src ar_delta_compute_src ar_delta_write_src
                 ar_delta_advance_src ar_delta_next_src)

subsection \<open>Substep step semantics — \<open>mttm_step\<close>-level lands-at\<close>

text \<open>Lift the per-relation destination-tag lemmas
  (\<open>ar_delta_X_dest\<close>) up through \<open>mttm_step\<close>: an
  \<open>M'\<close>-step out of a configuration whose source idx is
  \<open>AR_SimX\<close> lands at a configuration whose idx is in
  \<open>X\<close>'s dest set.  The five lemmas compose
  \<open>mttm_step.cases\<close> (extract the firing tuple), the
  \<open>from_src\<close> union-disambiguation helpers, and
  \<open>ar_delta_X_dest\<close>.  Together they encode the cycle's
  substep transition graph at the level the substep-walker engine
  consumes: SimRead-loop-or-compute, compute-to-write,
  write-loop-or-advance, advance-loop-or-next,
  next-to-read-or-halt.\<close>

lemma ar_step_from_SimRead_lands:
  assumes step: "(c, c') \<in> mttm_step (alphabet_reduce_delta M)"
      and src:  "fst (snd (mt_state c)) = AR_SimRead"
  shows "fst (snd (mt_state c')) = AR_SimRead
       \<or> fst (snd (mt_state c')) = AR_SimCompute"
proof -
  from step obtain S ts n S' aw dir where
      c_eq:  "c = Config\<^sub>M S ts n"
    and c'_eq: "c' = Config\<^sub>M S' (\<lambda>k. (ts k)(n k := aw k))
                          (\<lambda>k. go_dir (dir k) (n k))"
    and rel:  "(S, (\<lambda>k. ts k (n k)), S', aw, dir)
                  \<in> alphabet_reduce_delta M"
    by (auto elim: mttm_step.cases)
  have src_S: "fst (snd S) = AR_SimRead" using src c_eq by simp
  have "(S, (\<lambda>k. ts k (n k)), S', aw, dir) \<in> ar_delta_read M"
    using ar_delta_read_from_src[OF rel src_S] .
  hence "fst (snd S') = AR_SimRead \<or> fst (snd S') = AR_SimCompute"
    by (rule ar_delta_read_dest)
  thus ?thesis using c'_eq by simp
qed

text \<open>The \<open>compute\<close> member of the five-lemma lands-at family above is
  currently uncalled: the compute substep is the nondeterministic branch
  point, handled by bespoke reconstruct-and-reuse reasoning rather than the
  generic lands-at lift.  Retained to keep the substep transition graph
  complete.\<close>

lemma ar_step_from_SimCompute_lands:
  assumes step: "(c, c') \<in> mttm_step (alphabet_reduce_delta M)"
      and src:  "fst (snd (mt_state c)) = AR_SimCompute"
  shows "fst (snd (mt_state c')) = AR_SimWrite"
proof -
  from step obtain S ts n S' aw dir where
      c_eq:  "c = Config\<^sub>M S ts n"
    and c'_eq: "c' = Config\<^sub>M S' (\<lambda>k. (ts k)(n k := aw k))
                          (\<lambda>k. go_dir (dir k) (n k))"
    and rel:  "(S, (\<lambda>k. ts k (n k)), S', aw, dir)
                  \<in> alphabet_reduce_delta M"
    by (auto elim: mttm_step.cases)
  have src_S: "fst (snd S) = AR_SimCompute" using src c_eq by simp
  have "(S, (\<lambda>k. ts k (n k)), S', aw, dir) \<in> ar_delta_compute M"
    using ar_delta_compute_from_src[OF rel src_S] .
  hence "fst (snd S') = AR_SimWrite" by (rule ar_delta_compute_dest)
  thus ?thesis using c'_eq by simp
qed

lemma ar_step_from_SimWrite_lands:
  assumes step: "(c, c') \<in> mttm_step (alphabet_reduce_delta M)"
      and src:  "fst (snd (mt_state c)) = AR_SimWrite"
  shows "fst (snd (mt_state c')) = AR_SimWrite
       \<or> fst (snd (mt_state c')) = AR_SimAdvance"
proof -
  from step obtain S ts n S' aw dir where
      c_eq:  "c = Config\<^sub>M S ts n"
    and c'_eq: "c' = Config\<^sub>M S' (\<lambda>k. (ts k)(n k := aw k))
                          (\<lambda>k. go_dir (dir k) (n k))"
    and rel:  "(S, (\<lambda>k. ts k (n k)), S', aw, dir)
                  \<in> alphabet_reduce_delta M"
    by (auto elim: mttm_step.cases)
  have src_S: "fst (snd S) = AR_SimWrite" using src c_eq by simp
  have "(S, (\<lambda>k. ts k (n k)), S', aw, dir) \<in> ar_delta_write M"
    using ar_delta_write_from_src[OF rel src_S] .
  hence "fst (snd S') = AR_SimWrite \<or> fst (snd S') = AR_SimAdvance"
    by (rule ar_delta_write_dest)
  thus ?thesis using c'_eq by simp
qed

lemma ar_step_from_SimAdvance_lands:
  assumes step: "(c, c') \<in> mttm_step (alphabet_reduce_delta M)"
      and src:  "fst (snd (mt_state c)) = AR_SimAdvance"
  shows "fst (snd (mt_state c')) = AR_SimAdvance
       \<or> fst (snd (mt_state c')) = AR_SimNext"
proof -
  from step obtain S ts n S' aw dir where
      c_eq:  "c = Config\<^sub>M S ts n"
    and c'_eq: "c' = Config\<^sub>M S' (\<lambda>k. (ts k)(n k := aw k))
                          (\<lambda>k. go_dir (dir k) (n k))"
    and rel:  "(S, (\<lambda>k. ts k (n k)), S', aw, dir)
                  \<in> alphabet_reduce_delta M"
    by (auto elim: mttm_step.cases)
  have src_S: "fst (snd S) = AR_SimAdvance" using src c_eq by simp
  have "(S, (\<lambda>k. ts k (n k)), S', aw, dir) \<in> ar_delta_advance M"
    using ar_delta_advance_from_src[OF rel src_S] .
  hence "fst (snd S') = AR_SimAdvance \<or> fst (snd S') = AR_SimNext"
    by (rule ar_delta_advance_dest)
  thus ?thesis using c'_eq by simp
qed

lemma ar_step_from_SimNext_lands:
  assumes step: "(c, c') \<in> mttm_step (alphabet_reduce_delta M)"
      and src:  "fst (snd (mt_state c)) = AR_SimNext"
  shows "fst (snd (mt_state c')) = AR_SimRead
       \<or> fst (snd (mt_state c')) = AR_HaltAccept
       \<or> fst (snd (mt_state c')) = AR_HaltReject"
proof -
  from step obtain S ts n S' aw dir where
      c_eq:  "c = Config\<^sub>M S ts n"
    and c'_eq: "c' = Config\<^sub>M S' (\<lambda>k. (ts k)(n k := aw k))
                          (\<lambda>k. go_dir (dir k) (n k))"
    and rel:  "(S, (\<lambda>k. ts k (n k)), S', aw, dir)
                  \<in> alphabet_reduce_delta M"
    by (auto elim: mttm_step.cases)
  have src_S: "fst (snd S) = AR_SimNext" using src c_eq by simp
  have "(S, (\<lambda>k. ts k (n k)), S', aw, dir) \<in> ar_delta_next M"
    using ar_delta_next_from_src[OF rel src_S] .
  hence "fst (snd S') = AR_SimRead \<or> fst (snd S') = AR_HaltAccept
       \<or> fst (snd S') = AR_HaltReject"
    by (rule ar_delta_next_dest)
  thus ?thesis using c'_eq by simp
qed

subsection \<open>Walker invariants — per-substep stage predicates\<close>

text \<open>The substep-walker is a per-step induction over the
  \<open>M'\<close>-path that tracks where in the cycle we are by reading
  the substep idx off each visited configuration's state.  Six stage
  predicates carry the per-substep relationship between the cycle's
  source \<open>M\<close>-config \<open>cM\<close> and the current
  \<open>M'\<close>-configuration \<open>c'\<close>:

  \<^item> \<open>ar_walker_at_boundary M cM c'\<close>: fresh cycle start —
    \<open>c'\<close> at \<open>AR_SimRead\<close> boundary, the three
    forward invariants hold for \<open>cM\<close>.
  \<^item> \<open>ar_walker_in_read M cM c'\<close>: mid-read-phase —
    reachable from a boundary by \<open>ar_delta_read\<close>-only
    steps, still at \<open>AR_SimRead\<close>.
  \<^item> \<open>ar_walker_at_compute M cM c'\<close>: read complete —
    reachable from a boundary by \<open>ar_delta_read\<close>-only
    steps, now at \<open>AR_SimCompute\<close>.  The next M'-step on
    the path extracts the M-tuple via
    \<open>ar_compute_step_inv\<close>.
  \<^item> \<open>ar_walker_in_write M cM c'\<close>: M-tuple
    extracted, mid-write-phase — at \<open>AR_SimWrite\<close>.
  \<^item> \<open>ar_walker_in_advance M cM c'\<close>: write done,
    mid-advance-phase — at \<open>AR_SimAdvance\<close>.
  \<^item> \<open>ar_walker_at_next M cM c'\<close>: at
    \<open>AR_SimNext\<close>, about to dispatch to next boundary or
    halt via \<open>ar_next_step_inv\<close>.

  The witness-chain formulation (rather than concrete per-state
  conditions) makes preservation lemmas mechanical: at a config with
  substep tag T, an M'-step fires the unique substep relation with
  src tag T (by \<open>ar_delta_T_src\<close> + \<open>from_src\<close>);
  extending the witness chain by one step preserves the invariant.
  Chain shape (no cycle-wrap before completing this cycle) follows
  from the witness chain living in the *specific* substep relation
  \<open>mttm_step (ar_delta_T M)\<close>, which by
  \<open>ar_delta_T_src\<close> can only fire from sources at T —
  ruling out the wrap.\<close>

definition ar_walker_at_boundary ::
  "('q, 'a) mttm
    \<Rightarrow> ('a, 'q) mt_config
    \<Rightarrow> (sym4, 'q \<times> 'a ar_stage) mt_config \<Rightarrow> bool" where
  "ar_walker_at_boundary M cM c' \<longleftrightarrow>
     ar_simulates M cM c'
   \<and> ar_posk_consistent M cM c'
   \<and> ar_at_read_boundary M c'"

definition ar_walker_in_read ::
  "('q, 'a) mttm
    \<Rightarrow> ('a, 'q) mt_config
    \<Rightarrow> (sym4, 'q \<times> 'a ar_stage) mt_config \<Rightarrow> bool" where
  "ar_walker_in_read M cM c' \<longleftrightarrow>
     fst (snd (mt_state c')) = AR_SimRead
   \<and> (\<exists>c_b m. ar_walker_at_boundary M cM c_b
                \<and> (c_b, c') \<in> (mttm_step (ar_delta_read M)) ^^ m)"

definition ar_walker_at_compute ::
  "('q, 'a) mttm
    \<Rightarrow> ('a, 'q) mt_config
    \<Rightarrow> (sym4, 'q \<times> 'a ar_stage) mt_config \<Rightarrow> bool" where
  "ar_walker_at_compute M cM c' \<longleftrightarrow>
     fst (snd (mt_state c')) = AR_SimCompute
   \<and> (\<exists>c_b m. ar_walker_at_boundary M cM c_b
                \<and> (c_b, c') \<in> (mttm_step (ar_delta_read M)) ^^ m)"

definition ar_walker_in_write ::
  "('q, 'a) mttm
    \<Rightarrow> ('a, 'q) mt_config
    \<Rightarrow> (sym4, 'q \<times> 'a ar_stage) mt_config \<Rightarrow> bool" where
  "ar_walker_in_write M cM c' \<longleftrightarrow>
     fst (snd (mt_state c')) = AR_SimWrite
   \<and> (\<exists>c_b c_w m_r m_w.
        ar_walker_at_boundary M cM c_b
        \<and> (c_b, c_w) \<in> (mttm_step (ar_delta_read M)) ^^ m_r
        \<and> fst (snd (mt_state c_w)) = AR_SimCompute
        \<and> (\<exists>c_w_post. (c_w, c_w_post) \<in> mttm_step (ar_delta_compute M)
                       \<and> (c_w_post, c') \<in> (mttm_step (ar_delta_write M)) ^^ m_w))"

definition ar_walker_in_advance ::
  "('q, 'a) mttm
    \<Rightarrow> ('a, 'q) mt_config
    \<Rightarrow> (sym4, 'q \<times> 'a ar_stage) mt_config \<Rightarrow> bool" where
  "ar_walker_in_advance M cM c' \<longleftrightarrow>
     fst (snd (mt_state c')) = AR_SimAdvance
   \<and> (\<exists>c_b c_w c_a m_r m_w m_a.
        ar_walker_at_boundary M cM c_b
        \<and> (c_b, c_w) \<in> (mttm_step (ar_delta_read M)) ^^ m_r
        \<and> fst (snd (mt_state c_w)) = AR_SimCompute
        \<and> fst (snd (mt_state c_a)) = AR_SimAdvance
        \<and> (\<exists>c_w_post. (c_w, c_w_post) \<in> mttm_step (ar_delta_compute M)
                       \<and> (c_w_post, c_a) \<in> (mttm_step (ar_delta_write M)) ^^ m_w
                       \<and> (c_a, c') \<in> (mttm_step (ar_delta_advance M)) ^^ m_a))"

definition ar_walker_at_next ::
  "('q, 'a) mttm
    \<Rightarrow> ('a, 'q) mt_config
    \<Rightarrow> (sym4, 'q \<times> 'a ar_stage) mt_config \<Rightarrow> bool" where
  "ar_walker_at_next M cM c' \<longleftrightarrow>
     fst (snd (mt_state c')) = AR_SimNext
   \<and> (\<exists>c_b c_w c_a c_n m_r m_w m_a.
        ar_walker_at_boundary M cM c_b
        \<and> (c_b, c_w) \<in> (mttm_step (ar_delta_read M)) ^^ m_r
        \<and> fst (snd (mt_state c_w)) = AR_SimCompute
        \<and> fst (snd (mt_state c_a)) = AR_SimAdvance
        \<and> (\<exists>c_w_post. (c_w, c_w_post) \<in> mttm_step (ar_delta_compute M)
                       \<and> (c_w_post, c_a) \<in> (mttm_step (ar_delta_write M)) ^^ m_w
                       \<and> (c_a, c_n) \<in> (mttm_step (ar_delta_advance M)) ^^ m_a
                       \<and> c_n = c'))"

subsection \<open>Step lifts — \<open>mttm_step\<close> to specific substep\<close>

text \<open>Five \<open>mttm_step\<close>-to-specific-substep lifts: an
  \<open>M'\<close>-step in \<open>mttm_step (alphabet_reduce_delta M)\<close>
  whose source carries substep tag T is in fact in the smaller
  \<open>mttm_step (ar_delta_T M)\<close>.  Each composes
  \<open>mttm_step.cases\<close> (destructure the step), the matching
  \<open>ar_delta_T_from_src\<close> helper (narrow the firing tuple by
  src-tag uniqueness), and \<open>mttm_step.step\<close> with
  \<open>where ts = ts and n = n\<close> instantiation (break the
  higher-order unification ambiguity inherent in
  \<open>mttm_step.step\<close>'s pattern when matched against concrete
  tuples).  The walker preservation lemmas chain these lifts with
  the dest-tag dispatch (lands-at lemmas) to advance the witness
  chain by one step.\<close>

lemma ar_step_read_lift:
  fixes M :: "('q, 'a) mttm"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes src:  "fst (snd (mt_state c')) = AR_SimRead"
      and step: "(c', c'') \<in> mttm_step (alphabet_reduce_delta M)"
  shows "(c', c'') \<in> mttm_step (ar_delta_read M)"
proof -
  from step obtain S ts n S' aw dir where
      c'_eq:  "c' = Config\<^sub>M S ts n"
    and c''_eq: "c'' = Config\<^sub>M S' (\<lambda>k. (ts k)(n k := aw k))
                          (\<lambda>k. go_dir (dir k) (n k))"
    and rel:  "(S, (\<lambda>k. ts k (n k)), S', aw, dir)
                  \<in> alphabet_reduce_delta M"
    by (auto elim: mttm_step.cases)
  have src_S: "fst (snd S) = AR_SimRead" using src c'_eq by simp
  have rel_T: "(S, (\<lambda>k. ts k (n k)), S', aw, dir) \<in> ar_delta_read M"
    using ar_delta_read_from_src[OF rel src_S] .
  have step_aux: "(Config\<^sub>M S ts n,
                    Config\<^sub>M S' (\<lambda>k. (ts k)(n k := aw k))
                                (\<lambda>k. go_dir (dir k) (n k)))
                     \<in> mttm_step (ar_delta_read M)"
    by (rule mttm_step.step[where ts = ts and n = n, OF rel_T])
  show ?thesis using step_aux c'_eq c''_eq by simp
qed

lemma ar_step_compute_lift:
  fixes M :: "('q, 'a) mttm"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes src:  "fst (snd (mt_state c')) = AR_SimCompute"
      and step: "(c', c'') \<in> mttm_step (alphabet_reduce_delta M)"
  shows "(c', c'') \<in> mttm_step (ar_delta_compute M)"
proof -
  from step obtain S ts n S' aw dir where
      c'_eq:  "c' = Config\<^sub>M S ts n"
    and c''_eq: "c'' = Config\<^sub>M S' (\<lambda>k. (ts k)(n k := aw k))
                          (\<lambda>k. go_dir (dir k) (n k))"
    and rel:  "(S, (\<lambda>k. ts k (n k)), S', aw, dir)
                  \<in> alphabet_reduce_delta M"
    by (auto elim: mttm_step.cases)
  have src_S: "fst (snd S) = AR_SimCompute" using src c'_eq by simp
  have rel_T: "(S, (\<lambda>k. ts k (n k)), S', aw, dir) \<in> ar_delta_compute M"
    using ar_delta_compute_from_src[OF rel src_S] .
  have step_aux: "(Config\<^sub>M S ts n,
                    Config\<^sub>M S' (\<lambda>k. (ts k)(n k := aw k))
                                (\<lambda>k. go_dir (dir k) (n k)))
                     \<in> mttm_step (ar_delta_compute M)"
    by (rule mttm_step.step[where ts = ts and n = n, OF rel_T])
  show ?thesis using step_aux c'_eq c''_eq by simp
qed

lemma ar_step_write_lift:
  fixes M :: "('q, 'a) mttm"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes src:  "fst (snd (mt_state c')) = AR_SimWrite"
      and step: "(c', c'') \<in> mttm_step (alphabet_reduce_delta M)"
  shows "(c', c'') \<in> mttm_step (ar_delta_write M)"
proof -
  from step obtain S ts n S' aw dir where
      c'_eq:  "c' = Config\<^sub>M S ts n"
    and c''_eq: "c'' = Config\<^sub>M S' (\<lambda>k. (ts k)(n k := aw k))
                          (\<lambda>k. go_dir (dir k) (n k))"
    and rel:  "(S, (\<lambda>k. ts k (n k)), S', aw, dir)
                  \<in> alphabet_reduce_delta M"
    by (auto elim: mttm_step.cases)
  have src_S: "fst (snd S) = AR_SimWrite" using src c'_eq by simp
  have rel_T: "(S, (\<lambda>k. ts k (n k)), S', aw, dir) \<in> ar_delta_write M"
    using ar_delta_write_from_src[OF rel src_S] .
  have step_aux: "(Config\<^sub>M S ts n,
                    Config\<^sub>M S' (\<lambda>k. (ts k)(n k := aw k))
                                (\<lambda>k. go_dir (dir k) (n k)))
                     \<in> mttm_step (ar_delta_write M)"
    by (rule mttm_step.step[where ts = ts and n = n, OF rel_T])
  show ?thesis using step_aux c'_eq c''_eq by simp
qed

lemma ar_step_advance_lift:
  fixes M :: "('q, 'a) mttm"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes src:  "fst (snd (mt_state c')) = AR_SimAdvance"
      and step: "(c', c'') \<in> mttm_step (alphabet_reduce_delta M)"
  shows "(c', c'') \<in> mttm_step (ar_delta_advance M)"
proof -
  from step obtain S ts n S' aw dir where
      c'_eq:  "c' = Config\<^sub>M S ts n"
    and c''_eq: "c'' = Config\<^sub>M S' (\<lambda>k. (ts k)(n k := aw k))
                          (\<lambda>k. go_dir (dir k) (n k))"
    and rel:  "(S, (\<lambda>k. ts k (n k)), S', aw, dir)
                  \<in> alphabet_reduce_delta M"
    by (auto elim: mttm_step.cases)
  have src_S: "fst (snd S) = AR_SimAdvance" using src c'_eq by simp
  have rel_T: "(S, (\<lambda>k. ts k (n k)), S', aw, dir) \<in> ar_delta_advance M"
    using ar_delta_advance_from_src[OF rel src_S] .
  have step_aux: "(Config\<^sub>M S ts n,
                    Config\<^sub>M S' (\<lambda>k. (ts k)(n k := aw k))
                                (\<lambda>k. go_dir (dir k) (n k)))
                     \<in> mttm_step (ar_delta_advance M)"
    by (rule mttm_step.step[where ts = ts and n = n, OF rel_T])
  show ?thesis using step_aux c'_eq c''_eq by simp
qed

text \<open>Existence-lift wrappers around the \<open>ar_step_X_lift\<close>
  lemmas for the three generic substeps (read, write, advance):
  convert an existential conclusion
  \<open>\<exists>c''. (c', c'') \<in> mttm_step (alphabet_reduce_delta M)
    \<and> P c''\<close> into the same existential with the step in
  \<open>mttm_step (ar_delta_X M)\<close>, given the source tag of \<open>c'\<close>.
  These collapse the leaf-in-sub boilerplate (the
  \<open>obtain \<dots> using ar_step_X_lift[OF src \<dots>] \<dots>
   show ?thesis using \<dots> by blast\<close>
  scaffold) into a single application.  The other two substeps carry
  no wrapper: compute is the nondeterministic branch and next closes
  the cycle, so both are handled by the cycle-close's
  reconstruct-and-reuse machinery rather than a generic lift.\<close>

lemma ar_exists_step_in_sub_read:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and P :: "(sym4, 'q \<times> 'a ar_stage) mt_config \<Rightarrow> bool"
  assumes orig: "\<exists>c''. (c', c'') \<in> mttm_step (alphabet_reduce_delta M)
                       \<and> P c''"
      and src:  "fst (snd (mt_state c')) = AR_SimRead"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (ar_delta_read M) \<and> P c''"
proof -
  obtain c'' where step: "(c', c'') \<in> mttm_step (alphabet_reduce_delta M)"
                 and pc:   "P c''"
    using orig by blast
  have step_sub: "(c', c'') \<in> mttm_step (ar_delta_read M)"
    using ar_step_read_lift[OF src step] .
  show ?thesis using step_sub pc by blast
qed

lemma ar_exists_step_in_sub_write:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and P :: "(sym4, 'q \<times> 'a ar_stage) mt_config \<Rightarrow> bool"
  assumes orig: "\<exists>c''. (c', c'') \<in> mttm_step (alphabet_reduce_delta M)
                       \<and> P c''"
      and src:  "fst (snd (mt_state c')) = AR_SimWrite"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (ar_delta_write M) \<and> P c''"
proof -
  obtain c'' where step: "(c', c'') \<in> mttm_step (alphabet_reduce_delta M)"
                 and pc:   "P c''"
    using orig by blast
  have step_sub: "(c', c'') \<in> mttm_step (ar_delta_write M)"
    using ar_step_write_lift[OF src step] .
  show ?thesis using step_sub pc by blast
qed

lemma ar_exists_step_in_sub_advance:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and P :: "(sym4, 'q \<times> 'a ar_stage) mt_config \<Rightarrow> bool"
  assumes orig: "\<exists>c''. (c', c'') \<in> mttm_step (alphabet_reduce_delta M)
                       \<and> P c''"
      and src:  "fst (snd (mt_state c')) = AR_SimAdvance"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (ar_delta_advance M) \<and> P c''"
proof -
  obtain c'' where step: "(c', c'') \<in> mttm_step (alphabet_reduce_delta M)"
                 and pc:   "P c''"
    using orig by blast
  have step_sub: "(c', c'') \<in> mttm_step (ar_delta_advance M)"
    using ar_step_advance_lift[OF src step] .
  show ?thesis using step_sub pc by blast
qed

subsection \<open>Chain pinning in \<open>mttm_step (ar_delta_read M)\<close>\<close>

text \<open>Two structural facts about chains in the read sub-relation:
  the sub-relation is *functional* (lifted from
  \<open>ar_delta_read_func\<close> via \<open>mttm_step\<close>'s shape), so its
  \<open>m\<close>-step extension of any seed is unique; and it cannot fire
  from a source whose substep tag is \<open>AR_SimCompute\<close> (by
  \<open>ar_delta_read_src\<close>).  Together these pin a chain ending at
  \<open>AR_SimCompute\<close> uniquely on both its length and its endpoint:
  if two chains in the sub-relation start at the same seed and both
  end at an \<open>AR_SimCompute\<close>-tagged config, they coincide.  This
  is what bridges the walker's by-construction \<open>R_read\<close> witness
  chain to the existence chain produced by the (re-mirrored)
  \<open>ar_read_phase_in_sub\<close>: the witness chain inherits the latter's
  stated endpoint state shape, including the load-bearing
  \<open>buf = \<lambda>k. mt_tape cM k (mt_pos cM k)\<close>.\<close>

lemma mttm_step_ar_delta_read_func:
  fixes M :: "('q, 'a) mttm"
    and c c\<^sub>1 c\<^sub>2 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes h\<^sub>1: "(c, c\<^sub>1) \<in> mttm_step (ar_delta_read M)"
      and h\<^sub>2: "(c, c\<^sub>2) \<in> mttm_step (ar_delta_read M)"
  shows "c\<^sub>1 = c\<^sub>2"
proof -
  from h\<^sub>1 obtain S ts n S\<^sub>1 aw\<^sub>1 dir\<^sub>1 where
      ceq\<^sub>1: "c = Config\<^sub>M S ts n"
    and c\<^sub>1eq: "c\<^sub>1 = Config\<^sub>M S\<^sub>1 (\<lambda>k. (ts k)(n k := aw\<^sub>1 k))
                          (\<lambda>k. go_dir (dir\<^sub>1 k) (n k))"
    and rel\<^sub>1: "(S, (\<lambda>k. ts k (n k)), S\<^sub>1, aw\<^sub>1, dir\<^sub>1) \<in> ar_delta_read M"
    by (auto elim: mttm_step.cases)
  from h\<^sub>2 obtain S' ts' n' S\<^sub>2 aw\<^sub>2 dir\<^sub>2 where
      ceq\<^sub>2: "c = Config\<^sub>M S' ts' n'"
    and c\<^sub>2eq: "c\<^sub>2 = Config\<^sub>M S\<^sub>2 (\<lambda>k. (ts' k)(n' k := aw\<^sub>2 k))
                          (\<lambda>k. go_dir (dir\<^sub>2 k) (n' k))"
    and rel\<^sub>2: "(S', (\<lambda>k. ts' k (n' k)), S\<^sub>2, aw\<^sub>2, dir\<^sub>2) \<in> ar_delta_read M"
    by (auto elim: mttm_step.cases)
  have eq: "S = S' \<and> ts = ts' \<and> n = n'" using ceq\<^sub>1 ceq\<^sub>2 by simp
  have rel\<^sub>2': "(S, (\<lambda>k. ts k (n k)), S\<^sub>2, aw\<^sub>2, dir\<^sub>2) \<in> ar_delta_read M"
    using rel\<^sub>2 eq by simp
  have "(S\<^sub>1, aw\<^sub>1, dir\<^sub>1) = (S\<^sub>2, aw\<^sub>2, dir\<^sub>2)"
    using ar_delta_read_func[OF rel\<^sub>1 rel\<^sub>2'] .
  hence "S\<^sub>1 = S\<^sub>2 \<and> aw\<^sub>1 = aw\<^sub>2 \<and> dir\<^sub>1 = dir\<^sub>2" by simp
  thus ?thesis using c\<^sub>1eq c\<^sub>2eq eq by simp
qed

lemma chain_ar_delta_read_func:
  fixes M :: "('q, 'a) mttm"
  shows "(c, c\<^sub>1) \<in> (mttm_step (ar_delta_read M)) ^^ m
          \<Longrightarrow> (c, c\<^sub>2) \<in> (mttm_step (ar_delta_read M)) ^^ m
          \<Longrightarrow> c\<^sub>1 = c\<^sub>2"
proof (induction m arbitrary: c\<^sub>1 c\<^sub>2)
  case 0
  thus ?case by auto
next
  case (Suc m)
  obtain c\<^sub>1' where
      a: "(c, c\<^sub>1') \<in> (mttm_step (ar_delta_read M)) ^^ m"
    and b: "(c\<^sub>1', c\<^sub>1) \<in> mttm_step (ar_delta_read M)"
    using Suc(2) by (auto elim: relpow_Suc_E)
  obtain c\<^sub>2' where
      c: "(c, c\<^sub>2') \<in> (mttm_step (ar_delta_read M)) ^^ m"
    and d: "(c\<^sub>2', c\<^sub>2) \<in> mttm_step (ar_delta_read M)"
    using Suc(3) by (auto elim: relpow_Suc_E)
  have "c\<^sub>1' = c\<^sub>2'" using Suc(1)[OF a c] .
  thus ?case using b d mttm_step_ar_delta_read_func by simp
qed

lemma ar_delta_read_no_step_from_SimCompute:
  fixes M :: "('q, 'a) mttm"
    and c c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes "fst (snd (mt_state c)) = AR_SimCompute"
  shows "(c, c') \<notin> mttm_step (ar_delta_read M)"
proof
  assume h: "(c, c') \<in> mttm_step (ar_delta_read M)"
  from h obtain S ts n S' aw dir where
      ceq: "c = Config\<^sub>M S ts n"
    and rel: "(S, (\<lambda>k. ts k (n k)), S', aw, dir) \<in> ar_delta_read M"
    by (auto elim: mttm_step.cases)
  have "fst (snd S) = AR_SimRead" using ar_delta_read_src[OF rel] .
  hence "fst (snd (mt_state c)) = AR_SimRead" using ceq by simp
  with assms show False by simp
qed

lemma chain_ar_delta_read_to_SimCompute_uniq:
  fixes M :: "('q, 'a) mttm"
    and c c\<^sub>1 c\<^sub>2 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes h\<^sub>1: "(c, c\<^sub>1) \<in> (mttm_step (ar_delta_read M)) ^^ m"
      and h\<^sub>2: "(c, c\<^sub>2) \<in> (mttm_step (ar_delta_read M)) ^^ n"
      and c\<^sub>1cpu: "fst (snd (mt_state c\<^sub>1)) = AR_SimCompute"
      and c\<^sub>2cpu: "fst (snd (mt_state c\<^sub>2)) = AR_SimCompute"
  shows "m = n \<and> c\<^sub>1 = c\<^sub>2"
proof -
  have aux:
    "\<And>m n c\<^sub>1 c\<^sub>2. (c, c\<^sub>1) \<in> (mttm_step (ar_delta_read M)) ^^ m
                  \<Longrightarrow> (c, c\<^sub>2) \<in> (mttm_step (ar_delta_read M)) ^^ n
                  \<Longrightarrow> fst (snd (mt_state c\<^sub>1)) = AR_SimCompute
                  \<Longrightarrow> m \<le> n
                  \<Longrightarrow> m = n"
  proof -
    fix m n c\<^sub>1 c\<^sub>2
    assume a\<^sub>1: "(c, c\<^sub>1) \<in> (mttm_step (ar_delta_read M)) ^^ m"
       and a\<^sub>2: "(c, c\<^sub>2) \<in> (mttm_step (ar_delta_read M)) ^^ n"
       and acpu: "fst (snd (mt_state c\<^sub>1)) = AR_SimCompute"
       and ale: "m \<le> n"
    obtain dm where ndecomp: "n = m + dm" using ale le_Suc_ex by blast
    have "(c, c\<^sub>2) \<in> ((mttm_step (ar_delta_read M)) ^^ m)
                       O ((mttm_step (ar_delta_read M)) ^^ dm)"
      using a\<^sub>2 ndecomp by (simp add: relpow_add)
    then obtain c\<^sub>m where
        am: "(c, c\<^sub>m) \<in> (mttm_step (ar_delta_read M)) ^^ m"
      and adm: "(c\<^sub>m, c\<^sub>2) \<in> (mttm_step (ar_delta_read M)) ^^ dm"
      by auto
    have cm_eq: "c\<^sub>m = c\<^sub>1" using chain_ar_delta_read_func[OF am a\<^sub>1] .
    show "m = n"
    proof (rule ccontr)
      assume "m \<noteq> n"
      hence dm_pos: "0 < dm" using ndecomp by simp
      then obtain dm' where dm_eq: "dm = Suc dm'" using gr0_implies_Suc by blast
      have hsuc: "(c\<^sub>1, c\<^sub>2) \<in> (mttm_step (ar_delta_read M)) ^^ (Suc dm')"
        using adm cm_eq dm_eq by simp
      obtain c_next where
          first: "(c\<^sub>1, c_next) \<in> mttm_step (ar_delta_read M)"
        using relpow_Suc_D2[OF hsuc] by blast
      have "(c\<^sub>1, c_next) \<notin> mttm_step (ar_delta_read M)"
        using acpu by (rule ar_delta_read_no_step_from_SimCompute)
      thus False using first by simp
    qed
  qed
  have mn_eq: "m = n"
  proof (cases "m \<le> n")
    case True
    show ?thesis using aux[OF h\<^sub>1 h\<^sub>2 c\<^sub>1cpu True] .
  next
    case False
    hence nle: "n \<le> m" by simp
    show ?thesis using aux[OF h\<^sub>2 h\<^sub>1 c\<^sub>2cpu nle] by simp
  qed
  have "c\<^sub>1 = c\<^sub>2"
    using chain_ar_delta_read_func[OF h\<^sub>1 h\<^sub>2[unfolded mn_eq[symmetric]]] .
  thus ?thesis using mn_eq by simp
qed

text \<open>Two parallel chain-pinning suites for the write and advance
  sub-relations, mirroring the read suite verbatim with
  \<open>ar_delta_write\<close> / \<open>ar_delta_advance\<close> in place of
  \<open>ar_delta_read\<close> and \<open>AR_SimAdvance\<close> / \<open>AR_SimNext\<close>
  in place of \<open>AR_SimCompute\<close>.  Functional projections
  (\<open>ar_delta_write_func\<close>, \<open>ar_delta_advance_func\<close>) and src
  uniqueness (\<open>ar_delta_write_src\<close>, \<open>ar_delta_advance_src\<close>)
  feed the same scaffold.  These suites are used by the cycle-close
  bridging lemma to pin walker write/advance chains against the
  forward \<open>ar_write_phase\<close> / \<open>ar_advance_phase\<close>
  constructions.\<close>

lemma mttm_step_ar_delta_write_func:
  fixes M :: "('q, 'a) mttm"
    and c c\<^sub>1 c\<^sub>2 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes h\<^sub>1: "(c, c\<^sub>1) \<in> mttm_step (ar_delta_write M)"
      and h\<^sub>2: "(c, c\<^sub>2) \<in> mttm_step (ar_delta_write M)"
  shows "c\<^sub>1 = c\<^sub>2"
proof -
  from h\<^sub>1 obtain S ts n S\<^sub>1 aw\<^sub>1 dir\<^sub>1 where
      ceq\<^sub>1: "c = Config\<^sub>M S ts n"
    and c\<^sub>1eq: "c\<^sub>1 = Config\<^sub>M S\<^sub>1 (\<lambda>k. (ts k)(n k := aw\<^sub>1 k))
                          (\<lambda>k. go_dir (dir\<^sub>1 k) (n k))"
    and rel\<^sub>1: "(S, (\<lambda>k. ts k (n k)), S\<^sub>1, aw\<^sub>1, dir\<^sub>1) \<in> ar_delta_write M"
    by (auto elim: mttm_step.cases)
  from h\<^sub>2 obtain S' ts' n' S\<^sub>2 aw\<^sub>2 dir\<^sub>2 where
      ceq\<^sub>2: "c = Config\<^sub>M S' ts' n'"
    and c\<^sub>2eq: "c\<^sub>2 = Config\<^sub>M S\<^sub>2 (\<lambda>k. (ts' k)(n' k := aw\<^sub>2 k))
                          (\<lambda>k. go_dir (dir\<^sub>2 k) (n' k))"
    and rel\<^sub>2: "(S', (\<lambda>k. ts' k (n' k)), S\<^sub>2, aw\<^sub>2, dir\<^sub>2) \<in> ar_delta_write M"
    by (auto elim: mttm_step.cases)
  have eq: "S = S' \<and> ts = ts' \<and> n = n'" using ceq\<^sub>1 ceq\<^sub>2 by simp
  have rel\<^sub>2': "(S, (\<lambda>k. ts k (n k)), S\<^sub>2, aw\<^sub>2, dir\<^sub>2) \<in> ar_delta_write M"
    using rel\<^sub>2 eq by simp
  have "(S\<^sub>1, aw\<^sub>1, dir\<^sub>1) = (S\<^sub>2, aw\<^sub>2, dir\<^sub>2)"
    using ar_delta_write_func[OF rel\<^sub>1 rel\<^sub>2'] .
  hence "S\<^sub>1 = S\<^sub>2 \<and> aw\<^sub>1 = aw\<^sub>2 \<and> dir\<^sub>1 = dir\<^sub>2" by simp
  thus ?thesis using c\<^sub>1eq c\<^sub>2eq eq by simp
qed

lemma chain_ar_delta_write_func:
  fixes M :: "('q, 'a) mttm"
  shows "(c, c\<^sub>1) \<in> (mttm_step (ar_delta_write M)) ^^ m
          \<Longrightarrow> (c, c\<^sub>2) \<in> (mttm_step (ar_delta_write M)) ^^ m
          \<Longrightarrow> c\<^sub>1 = c\<^sub>2"
proof (induction m arbitrary: c\<^sub>1 c\<^sub>2)
  case 0
  thus ?case by auto
next
  case (Suc m)
  obtain c\<^sub>1' where
      a: "(c, c\<^sub>1') \<in> (mttm_step (ar_delta_write M)) ^^ m"
    and b: "(c\<^sub>1', c\<^sub>1) \<in> mttm_step (ar_delta_write M)"
    using Suc(2) by (auto elim: relpow_Suc_E)
  obtain c\<^sub>2' where
      c: "(c, c\<^sub>2') \<in> (mttm_step (ar_delta_write M)) ^^ m"
    and d: "(c\<^sub>2', c\<^sub>2) \<in> mttm_step (ar_delta_write M)"
    using Suc(3) by (auto elim: relpow_Suc_E)
  have "c\<^sub>1' = c\<^sub>2'" using Suc(1)[OF a c] .
  thus ?case using b d mttm_step_ar_delta_write_func by simp
qed

lemma ar_delta_write_no_step_from_SimAdvance:
  fixes M :: "('q, 'a) mttm"
    and c c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes "fst (snd (mt_state c)) = AR_SimAdvance"
  shows "(c, c') \<notin> mttm_step (ar_delta_write M)"
proof
  assume h: "(c, c') \<in> mttm_step (ar_delta_write M)"
  from h obtain S ts n S' aw dir where
      ceq: "c = Config\<^sub>M S ts n"
    and rel: "(S, (\<lambda>k. ts k (n k)), S', aw, dir) \<in> ar_delta_write M"
    by (auto elim: mttm_step.cases)
  have "fst (snd S) = AR_SimWrite" using ar_delta_write_src[OF rel] .
  hence "fst (snd (mt_state c)) = AR_SimWrite" using ceq by simp
  with assms show False by simp
qed

lemma chain_ar_delta_write_to_SimAdvance_uniq:
  fixes M :: "('q, 'a) mttm"
    and c c\<^sub>1 c\<^sub>2 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes h\<^sub>1: "(c, c\<^sub>1) \<in> (mttm_step (ar_delta_write M)) ^^ m"
      and h\<^sub>2: "(c, c\<^sub>2) \<in> (mttm_step (ar_delta_write M)) ^^ n"
      and c\<^sub>1adv: "fst (snd (mt_state c\<^sub>1)) = AR_SimAdvance"
      and c\<^sub>2adv: "fst (snd (mt_state c\<^sub>2)) = AR_SimAdvance"
  shows "m = n \<and> c\<^sub>1 = c\<^sub>2"
proof -
  have aux:
    "\<And>m n c\<^sub>1 c\<^sub>2. (c, c\<^sub>1) \<in> (mttm_step (ar_delta_write M)) ^^ m
                  \<Longrightarrow> (c, c\<^sub>2) \<in> (mttm_step (ar_delta_write M)) ^^ n
                  \<Longrightarrow> fst (snd (mt_state c\<^sub>1)) = AR_SimAdvance
                  \<Longrightarrow> m \<le> n
                  \<Longrightarrow> m = n"
  proof -
    fix m n c\<^sub>1 c\<^sub>2
    assume a\<^sub>1: "(c, c\<^sub>1) \<in> (mttm_step (ar_delta_write M)) ^^ m"
       and a\<^sub>2: "(c, c\<^sub>2) \<in> (mttm_step (ar_delta_write M)) ^^ n"
       and aadv: "fst (snd (mt_state c\<^sub>1)) = AR_SimAdvance"
       and ale: "m \<le> n"
    obtain dm where ndecomp: "n = m + dm" using ale le_Suc_ex by blast
    have "(c, c\<^sub>2) \<in> ((mttm_step (ar_delta_write M)) ^^ m)
                       O ((mttm_step (ar_delta_write M)) ^^ dm)"
      using a\<^sub>2 ndecomp by (simp add: relpow_add)
    then obtain c\<^sub>m where
        am: "(c, c\<^sub>m) \<in> (mttm_step (ar_delta_write M)) ^^ m"
      and adm: "(c\<^sub>m, c\<^sub>2) \<in> (mttm_step (ar_delta_write M)) ^^ dm"
      by auto
    have cm_eq: "c\<^sub>m = c\<^sub>1" using chain_ar_delta_write_func[OF am a\<^sub>1] .
    show "m = n"
    proof (rule ccontr)
      assume "m \<noteq> n"
      hence dm_pos: "0 < dm" using ndecomp by simp
      then obtain dm' where dm_eq: "dm = Suc dm'" using gr0_implies_Suc by blast
      have hsuc: "(c\<^sub>1, c\<^sub>2) \<in> (mttm_step (ar_delta_write M)) ^^ (Suc dm')"
        using adm cm_eq dm_eq by simp
      obtain c_next where
          first: "(c\<^sub>1, c_next) \<in> mttm_step (ar_delta_write M)"
        using relpow_Suc_D2[OF hsuc] by blast
      have "(c\<^sub>1, c_next) \<notin> mttm_step (ar_delta_write M)"
        using aadv by (rule ar_delta_write_no_step_from_SimAdvance)
      thus False using first by simp
    qed
  qed
  have mn_eq: "m = n"
  proof (cases "m \<le> n")
    case True
    show ?thesis using aux[OF h\<^sub>1 h\<^sub>2 c\<^sub>1adv True] .
  next
    case False
    hence nle: "n \<le> m" by simp
    show ?thesis using aux[OF h\<^sub>2 h\<^sub>1 c\<^sub>2adv nle] by simp
  qed
  have "c\<^sub>1 = c\<^sub>2"
    using chain_ar_delta_write_func[OF h\<^sub>1 h\<^sub>2[unfolded mn_eq[symmetric]]] .
  thus ?thesis using mn_eq by simp
qed

lemma mttm_step_ar_delta_advance_func:
  fixes M :: "('q, 'a) mttm"
    and c c\<^sub>1 c\<^sub>2 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes h\<^sub>1: "(c, c\<^sub>1) \<in> mttm_step (ar_delta_advance M)"
      and h\<^sub>2: "(c, c\<^sub>2) \<in> mttm_step (ar_delta_advance M)"
  shows "c\<^sub>1 = c\<^sub>2"
proof -
  from h\<^sub>1 obtain S ts n S\<^sub>1 aw\<^sub>1 dir\<^sub>1 where
      ceq\<^sub>1: "c = Config\<^sub>M S ts n"
    and c\<^sub>1eq: "c\<^sub>1 = Config\<^sub>M S\<^sub>1 (\<lambda>k. (ts k)(n k := aw\<^sub>1 k))
                          (\<lambda>k. go_dir (dir\<^sub>1 k) (n k))"
    and rel\<^sub>1: "(S, (\<lambda>k. ts k (n k)), S\<^sub>1, aw\<^sub>1, dir\<^sub>1) \<in> ar_delta_advance M"
    by (auto elim: mttm_step.cases)
  from h\<^sub>2 obtain S' ts' n' S\<^sub>2 aw\<^sub>2 dir\<^sub>2 where
      ceq\<^sub>2: "c = Config\<^sub>M S' ts' n'"
    and c\<^sub>2eq: "c\<^sub>2 = Config\<^sub>M S\<^sub>2 (\<lambda>k. (ts' k)(n' k := aw\<^sub>2 k))
                          (\<lambda>k. go_dir (dir\<^sub>2 k) (n' k))"
    and rel\<^sub>2: "(S', (\<lambda>k. ts' k (n' k)), S\<^sub>2, aw\<^sub>2, dir\<^sub>2) \<in> ar_delta_advance M"
    by (auto elim: mttm_step.cases)
  have eq: "S = S' \<and> ts = ts' \<and> n = n'" using ceq\<^sub>1 ceq\<^sub>2 by simp
  have rel\<^sub>2': "(S, (\<lambda>k. ts k (n k)), S\<^sub>2, aw\<^sub>2, dir\<^sub>2) \<in> ar_delta_advance M"
    using rel\<^sub>2 eq by simp
  have "(S\<^sub>1, aw\<^sub>1, dir\<^sub>1) = (S\<^sub>2, aw\<^sub>2, dir\<^sub>2)"
    using ar_delta_advance_func[OF rel\<^sub>1 rel\<^sub>2'] .
  hence "S\<^sub>1 = S\<^sub>2 \<and> aw\<^sub>1 = aw\<^sub>2 \<and> dir\<^sub>1 = dir\<^sub>2" by simp
  thus ?thesis using c\<^sub>1eq c\<^sub>2eq eq by simp
qed

lemma chain_ar_delta_advance_func:
  fixes M :: "('q, 'a) mttm"
  shows "(c, c\<^sub>1) \<in> (mttm_step (ar_delta_advance M)) ^^ m
          \<Longrightarrow> (c, c\<^sub>2) \<in> (mttm_step (ar_delta_advance M)) ^^ m
          \<Longrightarrow> c\<^sub>1 = c\<^sub>2"
proof (induction m arbitrary: c\<^sub>1 c\<^sub>2)
  case 0
  thus ?case by auto
next
  case (Suc m)
  obtain c\<^sub>1' where
      a: "(c, c\<^sub>1') \<in> (mttm_step (ar_delta_advance M)) ^^ m"
    and b: "(c\<^sub>1', c\<^sub>1) \<in> mttm_step (ar_delta_advance M)"
    using Suc(2) by (auto elim: relpow_Suc_E)
  obtain c\<^sub>2' where
      c: "(c, c\<^sub>2') \<in> (mttm_step (ar_delta_advance M)) ^^ m"
    and d: "(c\<^sub>2', c\<^sub>2) \<in> mttm_step (ar_delta_advance M)"
    using Suc(3) by (auto elim: relpow_Suc_E)
  have "c\<^sub>1' = c\<^sub>2'" using Suc(1)[OF a c] .
  thus ?case using b d mttm_step_ar_delta_advance_func by simp
qed

lemma ar_delta_advance_no_step_from_SimNext:
  fixes M :: "('q, 'a) mttm"
    and c c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes "fst (snd (mt_state c)) = AR_SimNext"
  shows "(c, c') \<notin> mttm_step (ar_delta_advance M)"
proof
  assume h: "(c, c') \<in> mttm_step (ar_delta_advance M)"
  from h obtain S ts n S' aw dir where
      ceq: "c = Config\<^sub>M S ts n"
    and rel: "(S, (\<lambda>k. ts k (n k)), S', aw, dir) \<in> ar_delta_advance M"
    by (auto elim: mttm_step.cases)
  have "fst (snd S) = AR_SimAdvance" using ar_delta_advance_src[OF rel] .
  hence "fst (snd (mt_state c)) = AR_SimAdvance" using ceq by simp
  with assms show False by simp
qed

lemma chain_ar_delta_advance_to_SimNext_uniq:
  fixes M :: "('q, 'a) mttm"
    and c c\<^sub>1 c\<^sub>2 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes h\<^sub>1: "(c, c\<^sub>1) \<in> (mttm_step (ar_delta_advance M)) ^^ m"
      and h\<^sub>2: "(c, c\<^sub>2) \<in> (mttm_step (ar_delta_advance M)) ^^ n"
      and c\<^sub>1nxt: "fst (snd (mt_state c\<^sub>1)) = AR_SimNext"
      and c\<^sub>2nxt: "fst (snd (mt_state c\<^sub>2)) = AR_SimNext"
  shows "m = n \<and> c\<^sub>1 = c\<^sub>2"
proof -
  have aux:
    "\<And>m n c\<^sub>1 c\<^sub>2. (c, c\<^sub>1) \<in> (mttm_step (ar_delta_advance M)) ^^ m
                  \<Longrightarrow> (c, c\<^sub>2) \<in> (mttm_step (ar_delta_advance M)) ^^ n
                  \<Longrightarrow> fst (snd (mt_state c\<^sub>1)) = AR_SimNext
                  \<Longrightarrow> m \<le> n
                  \<Longrightarrow> m = n"
  proof -
    fix m n c\<^sub>1 c\<^sub>2
    assume a\<^sub>1: "(c, c\<^sub>1) \<in> (mttm_step (ar_delta_advance M)) ^^ m"
       and a\<^sub>2: "(c, c\<^sub>2) \<in> (mttm_step (ar_delta_advance M)) ^^ n"
       and anxt: "fst (snd (mt_state c\<^sub>1)) = AR_SimNext"
       and ale: "m \<le> n"
    obtain dm where ndecomp: "n = m + dm" using ale le_Suc_ex by blast
    have "(c, c\<^sub>2) \<in> ((mttm_step (ar_delta_advance M)) ^^ m)
                       O ((mttm_step (ar_delta_advance M)) ^^ dm)"
      using a\<^sub>2 ndecomp by (simp add: relpow_add)
    then obtain c\<^sub>m where
        am: "(c, c\<^sub>m) \<in> (mttm_step (ar_delta_advance M)) ^^ m"
      and adm: "(c\<^sub>m, c\<^sub>2) \<in> (mttm_step (ar_delta_advance M)) ^^ dm"
      by auto
    have cm_eq: "c\<^sub>m = c\<^sub>1" using chain_ar_delta_advance_func[OF am a\<^sub>1] .
    show "m = n"
    proof (rule ccontr)
      assume "m \<noteq> n"
      hence dm_pos: "0 < dm" using ndecomp by simp
      then obtain dm' where dm_eq: "dm = Suc dm'" using gr0_implies_Suc by blast
      have hsuc: "(c\<^sub>1, c\<^sub>2) \<in> (mttm_step (ar_delta_advance M)) ^^ (Suc dm')"
        using adm cm_eq dm_eq by simp
      obtain c_next where
          first: "(c\<^sub>1, c_next) \<in> mttm_step (ar_delta_advance M)"
        using relpow_Suc_D2[OF hsuc] by blast
      have "(c\<^sub>1, c_next) \<notin> mttm_step (ar_delta_advance M)"
        using anxt by (rule ar_delta_advance_no_step_from_SimNext)
      thus False using first by simp
    qed
  qed
  have mn_eq: "m = n"
  proof (cases "m \<le> n")
    case True
    show ?thesis using aux[OF h\<^sub>1 h\<^sub>2 c\<^sub>1nxt True] .
  next
    case False
    hence nle: "n \<le> m" by simp
    show ?thesis using aux[OF h\<^sub>2 h\<^sub>1 c\<^sub>2nxt nle] by simp
  qed
  have "c\<^sub>1 = c\<^sub>2"
    using chain_ar_delta_advance_func[OF h\<^sub>1 h\<^sub>2[unfolded mn_eq[symmetric]]] .
  thus ?thesis using mn_eq by simp
qed

subsection \<open>Read-phase leaves, sub-relation chain variants\<close>

text \<open>For each single-step read-phase leaf
  (\<open>ar_read_le_step\<close>, \<open>ar_read_le_finish_step\<close>,
  \<open>ar_read_lookback1_step\<close>, \<open>ar_read_lookback2_step\<close>,
  \<open>ar_read_bit_step\<close>, \<open>ar_read_bit_boundary_step\<close>,
  \<open>ar_read_bit_finish_step\<close>), a companion lemma producing the
  step in \<open>mttm_step (ar_delta_read M)\<close> instead of
  \<open>mttm_step (alphabet_reduce_delta M)\<close>.  Each variant uses the
  existing lemma to obtain the step, then lifts via
  \<open>ar_step_read_lift\<close> (the source tag is \<open>AR_SimRead\<close> by
  the leaf's \<open>stg\<close> hypothesis).  No re-derivation of the step's
  effect — the existing leaf's stated post-state, post-tape, post-pos
  conclusions flow through verbatim.\<close>

lemma ar_read_le_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and notlast: "\<not> is_last_k M tk"
      and posk_le: "posk tk = AR_AtLE"
      and aLE: "mt_tape c' tk (mt_pos c' tk) = LE4"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (ar_delta_read M)
              \<and> mt_state c'' = (q, AR_SimRead, k_succ tk, 0,
                                  buf(tk := le_tm M), dvec, posk)
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := Suc (mt_pos c' tk))"
proof -
  have src: "fst (snd (mt_state c')) = AR_SimRead" using stg by simp
  show ?thesis
    using ar_exists_step_in_sub_read
            [OF ar_read_le_step[OF vM stg qQ notlast posk_le aLE vsrc pad_blank src_bounded] src] .
qed

lemma ar_read_le_finish_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and last: "is_last_k M tk"
      and posk_le: "posk tk = AR_AtLE"
      and aLE: "mt_tape c' tk (mt_pos c' tk) = LE4"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (ar_delta_read M)
              \<and> mt_state c'' = (q, AR_SimCompute, k_unidx 0, 0,
                                  buf(tk := le_tm M), dvec, posk)
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := Suc (mt_pos c' tk))"
proof -
  have src: "fst (snd (mt_state c')) = AR_SimRead" using stg by simp
  show ?thesis
    using ar_exists_step_in_sub_read
            [OF ar_read_le_finish_step[OF vM stg qQ last posk_le aLE vsrc pad_blank src_bounded] src] .
qed

lemma ar_read_lookback1_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (ar_delta_read M)
              \<and> mt_state c'' = (q, AR_SimRead, tk, Suc 0, buf, dvec, posk)
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := mt_pos c' tk - 1)"
proof -
  have src: "fst (snd (mt_state c')) = AR_SimRead" using stg by simp
  show ?thesis
    using ar_exists_step_in_sub_read
            [OF ar_read_lookback1_step[OF vM stg qQ posk_proper notLE vsrc pad_blank src_bounded] src] .
qed

lemma ar_read_lookback2_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimRead, tk, Suc 0, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, Suc 0, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimRead, tk, Suc 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (ar_delta_read M)
              \<and> mt_state c'' = (q, AR_SimRead, tk, Suc (Suc 0),
                    buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0), dvec,
                    posk(tk := if mt_tape c' tk (mt_pos c' tk) = LE4
                               then AR_AtFirstProper else AR_AtFurtherProper))
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := Suc (mt_pos c' tk))"
proof -
  have src: "fst (snd (mt_state c')) = AR_SimRead" using stg by simp
  show ?thesis
    using ar_exists_step_in_sub_read
            [OF ar_read_lookback2_step[OF vM stg qQ posk_proper kge2 vsrc pad_blank src_bounded] src] .
qed

lemma ar_read_bit_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimRead, tk, i, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and ilo: "2 \<le> i"
      and ihi: "Suc i \<le> Suc (block_width (\<Gamma>_tm M))"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimRead, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (ar_delta_read M)
              \<and> mt_state c'' = (q, AR_SimRead, tk, Suc i,
                    buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                          (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf tk)
                             + bit_value (mt_tape c' tk (mt_pos c' tk)))),
                    dvec, posk)
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := Suc (mt_pos c' tk))"
proof -
  have src: "fst (snd (mt_state c')) = AR_SimRead" using stg by simp
  show ?thesis
    using ar_exists_step_in_sub_read
            [OF ar_read_bit_step[OF vM stg qQ posk_proper ilo ihi kge2 vsrc pad_blank src_bounded] src] .
qed

lemma ar_read_bit_boundary_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimRead, tk, i, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and notlast: "\<not> is_last_k M tk"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and ieq: "i = Suc (block_width (\<Gamma>_tm M))"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimRead, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (ar_delta_read M)
              \<and> mt_state c'' = (q, AR_SimRead, k_succ tk, 0,
                    buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                          (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf tk)
                             + bit_value (mt_tape c' tk (mt_pos c' tk)))),
                    dvec, posk)
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := Suc (mt_pos c' tk))"
proof -
  have src: "fst (snd (mt_state c')) = AR_SimRead" using stg by simp
  show ?thesis
    using ar_exists_step_in_sub_read
            [OF ar_read_bit_boundary_step[OF vM stg qQ notlast posk_proper ieq vsrc pad_blank src_bounded]
                src] .
qed

lemma ar_read_bit_finish_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimRead, tk, i, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and last: "is_last_k M tk"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and ieq: "i = Suc (block_width (\<Gamma>_tm M))"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimRead, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (ar_delta_read M)
              \<and> mt_state c'' = (q, AR_SimCompute, k_unidx 0, 0,
                    buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                          (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf tk)
                             + bit_value (mt_tape c' tk (mt_pos c' tk)))),
                    dvec, posk)
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := Suc (mt_pos c' tk))"
proof -
  have src: "fst (snd (mt_state c')) = AR_SimRead" using stg by simp
  show ?thesis
    using ar_exists_step_in_sub_read
            [OF ar_read_bit_finish_step[OF vM stg qQ last posk_proper ieq vsrc pad_blank src_bounded]
                src] .
qed

subsection \<open>Read-phase combiners, sub-relation chain variants\<close>

text \<open>Multi-step combiner \<open>_in_sub\<close> variants follow the same
  proof structure as the originals, but obtain their sub-chains from
  the leaf \<open>_in_sub\<close> companions and compose via the generic
  \<open>relpow_Suc_I2\<close>/\<open>relpow_add\<close> combinators (which work over
  any relation, in particular \<open>mttm_step (ar_delta_read M)\<close>).
  All bookkeeping for tape, position, state shape transfers verbatim
  from the originals.\<close>

lemma ar_read_bit_loop_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 2, buf0, dvec, posk)"
      and buf0_valid: "\<forall>k. buf0 k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and pos_base: "mt_pos c' tk = base"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 2, buf0, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (mttm_step (ar_delta_read M))
                              ^^ (block_width (\<Gamma>_tm M) - 1)
              \<and> mt_state c'' = (q, AR_SimRead, tk, Suc (block_width (\<Gamma>_tm M)),
                    buf0(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) (buf0 tk)
                            (map (\<lambda>m. mt_tape c' tk (base + m))
                                 [0..<block_width (\<Gamma>_tm M) - 1])),
                    dvec, posk)
              \<and> mt_pos c'' tk = base + (block_width (\<Gamma>_tm M) - 1)
              \<and> mt_tape c'' = mt_tape c'
              \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_pos c'' k' = mt_pos c' k')"
  by (rule ar_read_bit_loop_gen
        [OF ar_read_bit_step_in_sub vM qQ kge2 posk_proper stg buf0_valid pos_base pad0 src0])

lemma ar_read_proper_prefix_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
      and base_pos: "0 < base"
      and pos_base: "mt_pos c' tk = base"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (mttm_step (ar_delta_read M))
                              ^^ Suc (block_width (\<Gamma>_tm M))
              \<and> mt_state c'' = (q, AR_SimRead, tk, Suc (block_width (\<Gamma>_tm M)),
                    buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M))
                              (gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0)
                              (map (\<lambda>m. mt_tape c' tk (base + m))
                                   [0..<block_width (\<Gamma>_tm M) - 1])),
                    dvec,
                    posk(tk := if mt_tape c' tk (base - 1) = LE4
                               then AR_AtFirstProper else AR_AtFurtherProper))
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := base + (block_width (\<Gamma>_tm M) - 1))"
  by (rule ar_read_proper_prefix_gen
        [OF ar_read_lookback1_step_in_sub ar_read_lookback2_step_in_sub
            ar_read_bit_loop_in_sub
            vM qQ kge2 posk_proper stg notLE base_pos pos_base vsrc pad0 src0])

lemma ar_read_proper_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and notlast: "\<not> is_last_k M tk"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
      and base_pos: "0 < base"
      and pos_base: "mt_pos c' tk = base"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (mttm_step (ar_delta_read M))
                              ^^ (block_width (\<Gamma>_tm M) + 2)
              \<and> mt_state c'' = (q, AR_SimRead, k_succ tk, 0,
                    buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M))
                              (gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0)
                              (map (\<lambda>m. mt_tape c' tk (base + m))
                                   [0..<block_width (\<Gamma>_tm M)])),
                    dvec,
                    posk(tk := if mt_tape c' tk (base - 1) = LE4
                               then AR_AtFirstProper else AR_AtFurtherProper))
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := base + block_width (\<Gamma>_tm M))"
  by (rule ar_read_proper_step_gen
        [OF ar_read_proper_prefix_in_sub ar_read_bit_boundary_step_in_sub
            vM qQ kge2 notlast posk_proper stg notLE base_pos pos_base vsrc pad0 src0])

lemma ar_read_proper_finish_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and last: "is_last_k M tk"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
      and base_pos: "0 < base"
      and pos_base: "mt_pos c' tk = base"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (mttm_step (ar_delta_read M))
                              ^^ (block_width (\<Gamma>_tm M) + 2)
              \<and> mt_state c'' = (q, AR_SimCompute, k_unidx 0, 0,
                    buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M))
                              (gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0)
                              (map (\<lambda>m. mt_tape c' tk (base + m))
                                   [0..<block_width (\<Gamma>_tm M)])),
                    dvec,
                    posk(tk := if mt_tape c' tk (base - 1) = LE4
                               then AR_AtFirstProper else AR_AtFurtherProper))
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := base + block_width (\<Gamma>_tm M))"
  by (rule ar_read_proper_finish_step_gen
        [OF ar_read_proper_prefix_in_sub ar_read_bit_finish_step_in_sub
            vM qQ kge2 last posk_proper stg notLE base_pos pos_base vsrc pad0 src0])

lemma ar_read_tape_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and tM :: "nat \<Rightarrow> 'a"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and notlast: "\<not> is_last_k M tk"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and tcorr: "ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                    tM (mt_tape c' tk)"
      and ppos: "mt_pos c' tk = sim_pos (block_width (\<Gamma>_tm M)) p"
      and pkok: "posk tk = AR_AtLE \<longleftrightarrow> p = 0"
      and proper_mem: "1 \<le> p \<Longrightarrow> tM p \<in> \<Gamma>_tm M"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (mttm_step (ar_delta_read M))
                              ^^ (if p = 0 then 1 else block_width (\<Gamma>_tm M) + 2)
              \<and> mt_state c'' = (q, AR_SimRead, k_succ tk, 0,
                    buf(tk := tM p), dvec,
                    posk(tk := if p = 0 then AR_AtLE
                               else if p = 1 then AR_AtFirstProper
                               else AR_AtFurtherProper))
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk :=
                    if p = 0 then Suc 0
                    else sim_pos (block_width (\<Gamma>_tm M)) p + block_width (\<Gamma>_tm M))"
  by (rule ar_read_tape_step_gen
        [OF ar_read_le_step_in_sub ar_read_proper_step_in_sub
            vM qQ kge2 notlast stg tcorr ppos pkok proper_mem vsrc pad0 src0])

lemma ar_read_tape_finish_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and tM :: "nat \<Rightarrow> 'a"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and last: "is_last_k M tk"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and tcorr: "ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                    tM (mt_tape c' tk)"
      and ppos: "mt_pos c' tk = sim_pos (block_width (\<Gamma>_tm M)) p"
      and pkok: "posk tk = AR_AtLE \<longleftrightarrow> p = 0"
      and proper_mem: "1 \<le> p \<Longrightarrow> tM p \<in> \<Gamma>_tm M"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (mttm_step (ar_delta_read M))
                              ^^ (if p = 0 then 1 else block_width (\<Gamma>_tm M) + 2)
              \<and> mt_state c'' = (q, AR_SimCompute, k_unidx 0, 0,
                    buf(tk := tM p), dvec,
                    posk(tk := if p = 0 then AR_AtLE
                               else if p = 1 then AR_AtFirstProper
                               else AR_AtFurtherProper))
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk :=
                    if p = 0 then Suc 0
                    else sim_pos (block_width (\<Gamma>_tm M)) p + block_width (\<Gamma>_tm M))"
  by (rule ar_read_tape_finish_step_gen
        [OF ar_read_le_finish_step_in_sub ar_read_proper_finish_step_in_sub
            vM qQ kge2 last stg tcorr ppos pkok proper_mem vsrc pad0 src0])

lemma ar_read_prefix_in_sub:
  fixes M :: "('q, 'a) mttm"
    and cM :: "('a, 'q) mt_config"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and stg0: "mt_state c0 = (q, AR_SimRead, 0, 0, buf0, dvec, posk0)"
      and tcorr: "\<forall>k < k_tm M. ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                       (mt_tape cM k) (mt_tape c0 k)"
      and ppos: "\<And>k. mt_pos c0 k = sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k)"
      and pkok: "\<And>k. posk0 k = AR_AtLE \<longleftrightarrow> mt_pos cM k = 0"
      and tapeG: "\<And>k. mt_tape cM k (mt_pos cM k) \<in> \<Gamma>_tm M"
      and bufG: "\<And>k. buf0 k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, 0, 0, buf0, dvec, posk0)"
  shows "j \<le> k_tm M - 1 \<Longrightarrow>
    (\<exists>c m. (c0, c) \<in> (mttm_step (ar_delta_read M)) ^^ m
         \<and> m \<le> j * (block_width (\<Gamma>_tm M) + 2)
         \<and> mt_state c = (q, AR_SimRead, k_unidx j, 0,
              (\<lambda>k. if k_idx k < j then mt_tape cM k (mt_pos cM k) else buf0 k),
              dvec,
              (\<lambda>k. if k_idx k < j
                    then (if mt_pos cM k = 0 then AR_AtLE
                          else if mt_pos cM k = 1 then AR_AtFirstProper
                          else AR_AtFurtherProper)
                    else posk0 k))
         \<and> mt_tape c = mt_tape c0
         \<and> mt_pos c = (\<lambda>k. if k_idx k < j
              then (if mt_pos cM k = 0 then Suc 0
                    else sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k)
                           + block_width (\<Gamma>_tm M))
              else mt_pos c0 k))"
  by (rule ar_read_prefix_gen
        [OF _ vM qQ kge2 stg0 tcorr ppos pkok tapeG bufG pad0 src0])
     (rule ar_read_tape_step_in_sub; assumption)

lemma ar_read_phase_in_sub:
  fixes M :: "('q, 'a) mttm"
    and cM :: "('a, 'q) mt_config"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and stg0: "mt_state c0 = (q, AR_SimRead, 0, 0, buf0, dvec, posk0)"
      and tcorr: "\<forall>k < k_tm M. ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                       (mt_tape cM k) (mt_tape c0 k)"
      and ppos: "\<And>k. mt_pos c0 k = sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k)"
      and pkok: "\<And>k. posk0 k = AR_AtLE \<longleftrightarrow> mt_pos cM k = 0"
      and tapeG: "\<And>k. mt_tape cM k (mt_pos cM k) \<in> \<Gamma>_tm M"
      and bufG: "\<And>k. buf0 k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, 0, 0, buf0, dvec, posk0)"
  shows "\<exists>c m. (c0, c) \<in> (mttm_step (ar_delta_read M)) ^^ m
         \<and> m \<le> k_tm M * (block_width (\<Gamma>_tm M) + 2)
         \<and> mt_state c = (q, AR_SimCompute, k_unidx 0, 0,
              (\<lambda>k. if k < k_tm M then mt_tape cM k (mt_pos cM k) else buf0 k),
              dvec,
              (\<lambda>k. if k < k_tm M
                    then (if mt_pos cM k = 0 then AR_AtLE
                          else if mt_pos cM k = 1 then AR_AtFirstProper
                          else AR_AtFurtherProper)
                    else posk0 k))
         \<and> mt_tape c = mt_tape c0
         \<and> mt_pos c = (\<lambda>k. if k < k_tm M
              then (if mt_pos cM k = 0 then Suc 0
                    else sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k) + block_width (\<Gamma>_tm M))
              else mt_pos c0 k)"
  by (rule ar_read_phase_gen
        [OF _ _ vM qQ kge2 stg0 tcorr ppos pkok tapeG bufG pad0 src0];
      (rule ar_read_prefix_in_sub ar_read_tape_finish_step_in_sub; assumption))

subsection \<open>Write-phase leaves, sub-relation chain variants\<close>

text \<open>Six write-phase leaves mirror to the sub-relation
  \<open>mttm_step (ar_delta_write M)\<close> via \<open>ar_step_write_lift\<close>,
  parallel to the seven read leaves at the earlier subsection.
  Each variant obtains the step from the original leaf, derives the
  \<open>AR_SimWrite\<close> source tag from the \<open>stg\<close> hypothesis,
  and lifts via \<open>ar_step_write_lift\<close>.\<close>

lemma ar_write_le_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimWrite, tk, 0, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and poskLE: "posk tk = AR_AtLE"
      and notlast: "\<not> is_last_k M tk"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimWrite, tk, 0, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimWrite, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (ar_delta_write M)
              \<and> mt_state c'' = (q, AR_SimWrite, k_succ tk, 0, buf, dvec, posk)
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = mt_pos c'"
proof -
  have src: "fst (snd (mt_state c')) = AR_SimWrite" using stg by simp
  show ?thesis
    using ar_exists_step_in_sub_write
            [OF ar_write_le_step[OF vM stg qQ poskLE notlast vsrc pad_blank src_bounded] src] .
qed

lemma ar_write_le_finish_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimWrite, tk, 0, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and poskLE: "posk tk = AR_AtLE"
      and last: "is_last_k M tk"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimWrite, tk, 0, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimWrite, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (ar_delta_write M)
              \<and> mt_state c'' = (q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk)
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = mt_pos c'"
proof -
  have src: "fst (snd (mt_state c')) = AR_SimWrite" using stg by simp
  show ?thesis
    using ar_exists_step_in_sub_write
            [OF ar_write_le_finish_step[OF vM stg qQ poskLE last vsrc pad_blank src_bounded] src] .
qed

lemma ar_write_walk_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimWrite, tk, i, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and poskproper: "posk tk \<noteq> AR_AtLE"
      and notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
      and step_le: "Suc i \<le> block_width (\<Gamma>_tm M)"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimWrite, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimWrite, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (ar_delta_write M)
              \<and> mt_state c'' = (q, AR_SimWrite, tk, Suc i, buf, dvec, posk)
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := mt_pos c' tk - 1)"
proof -
  have src: "fst (snd (mt_state c')) = AR_SimWrite" using stg by simp
  show ?thesis
    using ar_exists_step_in_sub_write
            [OF ar_write_walk_step[OF vM stg qQ poskproper notLE step_le vsrc pad_blank src_bounded] src] .
qed

lemma ar_write_bit_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimWrite, tk, i, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and poskproper: "posk tk \<noteq> AR_AtLE"
      and notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
      and ilo: "block_width (\<Gamma>_tm M) \<le> i"
      and ihi: "Suc i < 2 * block_width (\<Gamma>_tm M)"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimWrite, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimWrite, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (ar_delta_write M)
              \<and> mt_state c'' = (q, AR_SimWrite, tk, Suc i, buf, dvec, posk)
              \<and> mt_tape c'' = (mt_tape c')(tk :=
                    (mt_tape c' tk)(mt_pos c' tk :=
                       write_bit (\<Gamma>_tm M) (bl_tm M) (buf tk)
                                 (i - block_width (\<Gamma>_tm M))))
              \<and> mt_pos c'' = (mt_pos c')(tk := Suc (mt_pos c' tk))"
proof -
  have src: "fst (snd (mt_state c')) = AR_SimWrite" using stg by simp
  show ?thesis
    using ar_exists_step_in_sub_write
            [OF ar_write_bit_step[OF vM stg qQ poskproper notLE ilo ihi vsrc pad_blank src_bounded] src] .
qed

lemma ar_write_bit_boundary_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimWrite, tk, i, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and poskproper: "posk tk \<noteq> AR_AtLE"
      and notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
      and notlast: "\<not> is_last_k M tk"
      and ihi: "Suc i = 2 * block_width (\<Gamma>_tm M)"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimWrite, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimWrite, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (ar_delta_write M)
              \<and> mt_state c'' = (q, AR_SimWrite, k_succ tk, 0, buf, dvec, posk)
              \<and> mt_tape c'' = (mt_tape c')(tk :=
                    (mt_tape c' tk)(mt_pos c' tk :=
                       write_bit (\<Gamma>_tm M) (bl_tm M) (buf tk)
                                 (i - block_width (\<Gamma>_tm M))))
              \<and> mt_pos c'' = (mt_pos c')(tk := Suc (mt_pos c' tk))"
proof -
  have src: "fst (snd (mt_state c')) = AR_SimWrite" using stg by simp
  show ?thesis
    using ar_exists_step_in_sub_write
            [OF ar_write_bit_boundary_step
                  [OF vM stg qQ poskproper notLE notlast ihi vsrc pad_blank src_bounded] src] .
qed

lemma ar_write_bit_finish_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimWrite, tk, i, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and poskproper: "posk tk \<noteq> AR_AtLE"
      and notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
      and last: "is_last_k M tk"
      and ihi: "Suc i = 2 * block_width (\<Gamma>_tm M)"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimWrite, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimWrite, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (ar_delta_write M)
              \<and> mt_state c'' = (q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk)
              \<and> mt_tape c'' = (mt_tape c')(tk :=
                    (mt_tape c' tk)(mt_pos c' tk :=
                       write_bit (\<Gamma>_tm M) (bl_tm M) (buf tk)
                                 (i - block_width (\<Gamma>_tm M))))
              \<and> mt_pos c'' = (mt_pos c')(tk := Suc (mt_pos c' tk))"
proof -
  have src: "fst (snd (mt_state c')) = AR_SimWrite" using stg by simp
  show ?thesis
    using ar_exists_step_in_sub_write
            [OF ar_write_bit_finish_step
                  [OF vM stg qQ poskproper notLE last ihi vsrc pad_blank src_bounded] src] .
qed

subsection \<open>Advance-phase leaves, sub-relation chain variants\<close>

text \<open>Three advance-phase leaves
  (\<open>ar_advance_walk_step\<close>, \<open>ar_advance_boundary_step\<close>,
  \<open>ar_advance_finish_step\<close>) mirror to the sub-relation
  \<open>mttm_step (ar_delta_advance M)\<close> via
  \<open>ar_exists_step_in_sub_advance\<close>, parallel to the write and
  read leaves above.  Each variant derives the
  \<open>AR_SimAdvance\<close> source tag from \<open>stg\<close>, then composes
  the original leaf with the existence lifter.\<close>

lemma ar_advance_walk_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimAdvance, tk, i, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
      and step_lt: "Suc i < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimAdvance, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimAdvance, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (ar_delta_advance M)
              \<and> mt_state c'' = (q, AR_SimAdvance, tk, Suc i, buf, dvec, posk)
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := mt_pos c' tk - 1)"
proof -
  have src: "fst (snd (mt_state c')) = AR_SimAdvance" using stg by simp
  show ?thesis
    using ar_exists_step_in_sub_advance
            [OF ar_advance_walk_step[OF vM stg qQ notLE step_lt vsrc pad_blank src_bounded] src] .
qed

lemma ar_advance_boundary_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimAdvance, tk, i, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and notlast: "\<not> is_last_k M tk"
      and fire: "(dvec tk = dir.R \<and> i = 0)
                 \<or> (dvec tk \<noteq> dir.R
                     \<and> mt_tape c' tk (mt_pos c' tk) \<noteq> LE4
                     \<and> Suc i = ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk))"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimAdvance, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimAdvance, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (ar_delta_advance M)
              \<and> mt_state c'' = (q, AR_SimAdvance, k_succ tk, 0, buf, dvec,
                                  posk(tk := ar_newpos (dvec tk) (posk tk)))
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (if dvec tk = dir.R then mt_pos c'
                              else (mt_pos c')(tk := mt_pos c' tk - 1))"
proof -
  have src: "fst (snd (mt_state c')) = AR_SimAdvance" using stg by simp
  show ?thesis
    using ar_exists_step_in_sub_advance
            [OF ar_advance_boundary_step[OF vM stg qQ notlast fire vsrc pad_blank src_bounded] src] .
qed

lemma ar_advance_finish_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimAdvance, tk, i, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and last: "is_last_k M tk"
      and fire: "(dvec tk = dir.R \<and> i = 0)
                 \<or> (dvec tk \<noteq> dir.R
                     \<and> mt_tape c' tk (mt_pos c' tk) \<noteq> LE4
                     \<and> Suc i = ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk))"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimAdvance, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimAdvance, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (ar_delta_advance M)
              \<and> mt_state c'' = (q, AR_SimNext, k_unidx 0, 0, buf, dvec,
                                  posk(tk := ar_newpos (dvec tk) (posk tk)))
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (if dvec tk = dir.R then mt_pos c'
                              else (mt_pos c')(tk := mt_pos c' tk - 1))"
proof -
  have src: "fst (snd (mt_state c')) = AR_SimAdvance" using stg by simp
  show ?thesis
    using ar_exists_step_in_sub_advance
            [OF ar_advance_finish_step[OF vM stg qQ last fire vsrc pad_blank src_bounded] src] .
qed

subsection \<open>Write-phase combiners, sub-relation chain variants\<close>

text \<open>Write-phase multi-step combiner \<open>_in_sub\<close> variants
  follow the same proof structure as the originals, obtaining
  sub-chains from the write-leaf \<open>_in_sub\<close> companions and
  composing via the generic \<open>relpow_Suc_I2\<close> /
  \<open>relpow_invariant_chain\<close> combinators (which work over any
  relation, in particular \<open>mttm_step (ar_delta_write M)\<close>).\<close>

lemma ar_write_back_loop_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and poskproper: "posk tk \<noteq> AR_AtLE"
      and stg: "mt_state c0 = (q, AR_SimWrite, tk, 0, buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and pos_base: "mt_pos c0 tk = base + block_width (\<Gamma>_tm M)"
      and notLE: "\<And>m. \<lbrakk> 1 \<le> m; m \<le> block_width (\<Gamma>_tm M) \<rbrakk>
                   \<Longrightarrow> mt_tape c0 tk (base + m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimWrite, tk, 0, buf, dvec, posk)"
  shows "\<exists>c'. (c0, c') \<in> (mttm_step (ar_delta_write M))
                            ^^ block_width (\<Gamma>_tm M)
              \<and> mt_state c' = (q, AR_SimWrite, tk, block_width (\<Gamma>_tm M),
                                  buf, dvec, posk)
              \<and> mt_pos c' tk = base
              \<and> mt_tape c' = mt_tape c0
              \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_pos c' k' = mt_pos c0 k')"
  by (rule ar_write_back_loop_gen
        [OF ar_write_walk_step_in_sub vM qQ kge2 poskproper stg buf_valid pos_base notLE pad0 src0])

lemma ar_write_fwd_loop_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and poskproper: "posk tk \<noteq> AR_AtLE"
      and stg: "mt_state c0 = (q, AR_SimWrite, tk, block_width (\<Gamma>_tm M),
                                 buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and pos_base: "mt_pos c0 tk = base"
      and notLE: "\<And>m. m < block_width (\<Gamma>_tm M)
                   \<Longrightarrow> mt_tape c0 tk (base + m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimWrite, tk, block_width (\<Gamma>_tm M), buf, dvec, posk)"
  shows "\<exists>c'. (c0, c') \<in> (mttm_step (ar_delta_write M))
                            ^^ (block_width (\<Gamma>_tm M) - 1)
              \<and> mt_state c' = (q, AR_SimWrite, tk,
                    block_width (\<Gamma>_tm M) + (block_width (\<Gamma>_tm M) - 1),
                    buf, dvec, posk)
              \<and> mt_pos c' tk = base + (block_width (\<Gamma>_tm M) - 1)
              \<and> mt_tape c' tk = (\<lambda>pos.
                    if base \<le> pos \<and> pos < base + (block_width (\<Gamma>_tm M) - 1)
                    then write_bit (\<Gamma>_tm M) (bl_tm M) (buf tk) (pos - base)
                    else mt_tape c0 tk pos)
              \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_tape c' k' = mt_tape c0 k')
              \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_pos c' k' = mt_pos c0 k')"
  by (rule ar_write_fwd_loop_gen
        [OF ar_write_bit_step_in_sub vM qQ kge2 poskproper stg buf_valid pos_base notLE pad0 src0])

text \<open>The proper-cell single-tape write prefix, re-mirrored into
  \<open>mttm_step (ar_delta_write M)\<close>.  Composes the back-walk loop
  (\<open>ar_write_back_loop_in_sub\<close>) and the forward bit-write loop
  (\<open>ar_write_fwd_loop_in_sub\<close>) by \<open>relcompI\<close> +
  \<open>relpow_add\<close>; since both \<open>_in_sub\<close> sub-combiners carry
  field-for-field the same output contract as the originals, the
  composition and the two \<open>ext\<close> reassemblies (tape, pos)
  transfer verbatim with only the relation and the two helper calls
  changed.\<close>

lemma ar_write_proper_prefix_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and poskproper: "posk tk \<noteq> AR_AtLE"
      and stg: "mt_state c' = (q, AR_SimWrite, tk, 0, buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and pos_base: "mt_pos c' tk = base + block_width (\<Gamma>_tm M)"
      and notLE: "\<And>m. m \<le> block_width (\<Gamma>_tm M)
                   \<Longrightarrow> mt_tape c' tk (base + m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimWrite, tk, 0, buf, dvec, posk)"
  shows "\<exists>c2. (c', c2) \<in> (mttm_step (ar_delta_write M))
                            ^^ (block_width (\<Gamma>_tm M) + (block_width (\<Gamma>_tm M) - 1))
              \<and> mt_state c2 = (q, AR_SimWrite, tk,
                    block_width (\<Gamma>_tm M) + (block_width (\<Gamma>_tm M) - 1),
                    buf, dvec, posk)
              \<and> mt_tape c2 = (mt_tape c')(tk := (\<lambda>pos.
                    if base \<le> pos \<and> pos < base + (block_width (\<Gamma>_tm M) - 1)
                    then write_bit (\<Gamma>_tm M) (bl_tm M) (buf tk) (pos - base)
                    else mt_tape c' tk pos))
              \<and> mt_pos c2 = (mt_pos c')(tk := base + (block_width (\<Gamma>_tm M) - 1))"
  by (rule ar_write_proper_prefix_gen
        [OF ar_write_back_loop_in_sub ar_write_fwd_loop_in_sub
            vM qQ kge2 poskproper stg buf_valid pos_base notLE pad0 src0])

text \<open>The proper-cell single-tape write, non-last tape, re-mirrored
  into \<open>mttm_step (ar_delta_write M)\<close>.  As
  \<open>ar_write_proper_prefix_in_sub\<close> followed by one bit-boundary
  step (\<open>ar_write_bit_boundary_step_in_sub\<close>), composing by
  \<open>relpow_Suc_I\<close>.  The shared \<open>write_block_extend\<close> helper is
  relation-agnostic (pure \<open>fun_upd\<close> arithmetic) and reused
  verbatim; the body transfers from the original with only the
  relation and the two helper references changed.\<close>

lemma ar_write_proper_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and notlast: "\<not> is_last_k M tk"
      and poskproper: "posk tk \<noteq> AR_AtLE"
      and stg: "mt_state c' = (q, AR_SimWrite, tk, 0, buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and pos_base: "mt_pos c' tk = base + block_width (\<Gamma>_tm M)"
      and notLE: "\<And>m. m \<le> block_width (\<Gamma>_tm M)
                   \<Longrightarrow> mt_tape c' tk (base + m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimWrite, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (mttm_step (ar_delta_write M))
                              ^^ (2 * block_width (\<Gamma>_tm M))
              \<and> mt_state c'' = (q, AR_SimWrite, k_succ tk, 0, buf, dvec, posk)
              \<and> mt_tape c'' = (mt_tape c')(tk := (\<lambda>pos.
                    if base \<le> pos \<and> pos < base + block_width (\<Gamma>_tm M)
                    then write_bit (\<Gamma>_tm M) (bl_tm M) (buf tk) (pos - base)
                    else mt_tape c' tk pos))
              \<and> mt_pos c'' = (mt_pos c')(tk := base + block_width (\<Gamma>_tm M))"
  by (rule ar_write_proper_step_gen
        [OF ar_write_proper_prefix_in_sub ar_write_bit_boundary_step_in_sub
            vM qQ kge2 notlast poskproper stg buf_valid pos_base notLE pad0 src0])

text \<open>The proper-cell single-tape write, last tape, re-mirrored
  into \<open>mttm_step (ar_delta_write M)\<close>.  As
  \<open>ar_write_proper_step_in_sub\<close> but \<open>tk\<close> is the last tape,
  so the closing step is \<open>ar_write_bit_finish_step_in_sub\<close>:
  after the last-cell write the phase transitions to
  \<open>AR_SimAdvance\<close> with the current-tape field reset to
  \<open>k_unidx 0\<close>.  Same \<open>2b\<close>-step block write and head return
  to \<open>base + b\<close>; body transfers verbatim with only the relation
  and the two helper references changed.\<close>

lemma ar_write_proper_finish_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and last: "is_last_k M tk"
      and poskproper: "posk tk \<noteq> AR_AtLE"
      and stg: "mt_state c' = (q, AR_SimWrite, tk, 0, buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and pos_base: "mt_pos c' tk = base + block_width (\<Gamma>_tm M)"
      and notLE: "\<And>m. m \<le> block_width (\<Gamma>_tm M)
                   \<Longrightarrow> mt_tape c' tk (base + m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimWrite, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (mttm_step (ar_delta_write M))
                              ^^ (2 * block_width (\<Gamma>_tm M))
              \<and> mt_state c'' = (q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk)
              \<and> mt_tape c'' = (mt_tape c')(tk := (\<lambda>pos.
                    if base \<le> pos \<and> pos < base + block_width (\<Gamma>_tm M)
                    then write_bit (\<Gamma>_tm M) (bl_tm M) (buf tk) (pos - base)
                    else mt_tape c' tk pos))
              \<and> mt_pos c'' = (mt_pos c')(tk := base + block_width (\<Gamma>_tm M))"
  by (rule ar_write_proper_finish_step_gen
        [OF ar_write_proper_prefix_in_sub ar_write_bit_finish_step_in_sub
            vM qQ kge2 last poskproper stg buf_valid pos_base notLE pad0 src0])

text \<open>The unified single-tape write, non-last tape, re-mirrored
  into \<open>mttm_step (ar_delta_write M)\<close>: the LE/proper dispatch
  on \<open>posk tk = AR_AtLE\<close> (pinned by \<open>poskle\<close> to \<open>p =
  0\<close>).  The LE arm (\<open>ar_write_le_step_in_sub\<close>, \<open>1\<close>
  step) hands off untouched; the proper arm
  (\<open>ar_write_proper_step_in_sub\<close>, \<open>2b\<close> steps) overwrites
  the \<open>b\<close>-cell block.  Head invariant in both arms.  The
  \<open>\<noteq> LE4\<close> facts come from the input correspondence
  \<open>tcorr\<close>; that derivation is relation-agnostic and transfers
  verbatim along with the relation and two helper references
  changing.\<close>

lemma ar_write_tape_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and tM :: "nat \<Rightarrow> 'a"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and notlast: "\<not> is_last_k M tk"
      and stg: "mt_state c' = (q, AR_SimWrite, tk, 0, buf, dvec, posk)"
      and tcorr: "ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                    tM (mt_tape c' tk)"
      and ppos: "mt_pos c' tk = (if p = 0 then Suc 0
                    else sim_pos (block_width (\<Gamma>_tm M)) p + block_width (\<Gamma>_tm M))"
      and poskle: "posk tk = AR_AtLE \<longleftrightarrow> p = 0"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimWrite, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimWrite, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (mttm_step (ar_delta_write M))
                              ^^ (if p = 0 then 1 else 2 * block_width (\<Gamma>_tm M))
              \<and> mt_state c'' = (q, AR_SimWrite, k_succ tk, 0, buf, dvec, posk)
              \<and> mt_tape c'' = (if p = 0 then mt_tape c'
                    else (mt_tape c')(tk := (\<lambda>pos.
                      if sim_pos (block_width (\<Gamma>_tm M)) p \<le> pos
                         \<and> pos < sim_pos (block_width (\<Gamma>_tm M)) p + block_width (\<Gamma>_tm M)
                      then write_bit (\<Gamma>_tm M) (bl_tm M) (buf tk)
                             (pos - sim_pos (block_width (\<Gamma>_tm M)) p)
                      else mt_tape c' tk pos)))
              \<and> mt_pos c'' = mt_pos c'"
  by (rule ar_write_tape_step_gen
        [OF ar_write_le_step_in_sub ar_write_proper_step_in_sub
            vM qQ kge2 notlast stg tcorr ppos poskle buf_valid vsrc pad0 src0])

text \<open>The unified single-tape write, last tape, re-mirrored into
  \<open>mttm_step (ar_delta_write M)\<close>: as
  \<open>ar_write_tape_step_in_sub\<close> but \<open>tk\<close> is the last tape,
  so both arms transition to \<open>AR_SimAdvance\<close> (current-tape
  field reset to \<open>k_unidx 0\<close>): the LE arm via
  \<open>ar_write_le_finish_step_in_sub\<close>, the proper arm via
  \<open>ar_write_proper_finish_step_in_sub\<close>.  Same tape edit and
  head invariance; body transfers verbatim with only the relation
  and the two helper references changed.\<close>

lemma ar_write_tape_finish_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and tM :: "nat \<Rightarrow> 'a"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and last: "is_last_k M tk"
      and stg: "mt_state c' = (q, AR_SimWrite, tk, 0, buf, dvec, posk)"
      and tcorr: "ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                    tM (mt_tape c' tk)"
      and ppos: "mt_pos c' tk = (if p = 0 then Suc 0
                    else sim_pos (block_width (\<Gamma>_tm M)) p + block_width (\<Gamma>_tm M))"
      and poskle: "posk tk = AR_AtLE \<longleftrightarrow> p = 0"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimWrite, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimWrite, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (mttm_step (ar_delta_write M))
                              ^^ (if p = 0 then 1 else 2 * block_width (\<Gamma>_tm M))
              \<and> mt_state c'' = (q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk)
              \<and> mt_tape c'' = (if p = 0 then mt_tape c'
                    else (mt_tape c')(tk := (\<lambda>pos.
                      if sim_pos (block_width (\<Gamma>_tm M)) p \<le> pos
                         \<and> pos < sim_pos (block_width (\<Gamma>_tm M)) p + block_width (\<Gamma>_tm M)
                      then write_bit (\<Gamma>_tm M) (bl_tm M) (buf tk)
                             (pos - sim_pos (block_width (\<Gamma>_tm M)) p)
                      else mt_tape c' tk pos)))
              \<and> mt_pos c'' = mt_pos c'"
  by (rule ar_write_tape_finish_step_gen
        [OF ar_write_le_finish_step_in_sub ar_write_proper_finish_step_in_sub
            vM qQ kge2 last stg tcorr ppos poskle buf_valid vsrc pad0 src0])

text \<open>The write-phase prefix walk, re-mirrored into
  \<open>mttm_step (ar_delta_write M)\<close>: from the write boundary,
  iterate the unified non-last per-tape write
  \<open>ar_write_tape_step_in_sub\<close> over the first \<open>j\<close> tapes
  (all non-last), landing back at \<open>AR_SimWrite\<close> on tape
  \<open>k_unidx j\<close>.  The induction on \<open>j\<close>, the split tape
  descriptor, and the per-tape \<open>tcorr\<close>/position bookkeeping
  transfer verbatim from the original; only the relation and the
  one helper reference change.  The internal IH is already over
  \<open>ar_delta_write M\<close>.\<close>

lemma ar_write_prefix_in_sub:
  fixes M :: "('q, 'a) mttm"
    and cM :: "('a, 'q) mt_config"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and stg0: "mt_state c0 = (q, AR_SimWrite, 0, 0, buf, dvec, posk)"
      and tcorr: "\<forall>k < k_tm M. ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                       (mt_tape cM k) (mt_tape c0 k)"
      and ppos: "\<forall>k < k_tm M. mt_pos c0 k = (if mt_pos cM k = 0 then Suc 0
                       else sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k)
                              + block_width (\<Gamma>_tm M))"
      and poskle: "\<forall>k < k_tm M. posk k = AR_AtLE \<longleftrightarrow> mt_pos cM k = 0"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimWrite, 0, 0, buf, dvec, posk)"
  shows "j \<le> k_tm M - 1 \<Longrightarrow>
    (\<exists>c m. (c0, c) \<in> (mttm_step (ar_delta_write M)) ^^ m
         \<and> m \<le> j * (2 * block_width (\<Gamma>_tm M))
         \<and> mt_state c = (q, AR_SimWrite, k_unidx j, 0, buf, dvec, posk)
         \<and> mt_tape c = (\<lambda>k. if k_idx k < j
              then (if mt_pos cM k = 0 then mt_tape c0 k
                    else (\<lambda>pos. if sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k) \<le> pos
                                  \<and> pos < sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k)
                                            + block_width (\<Gamma>_tm M)
                               then write_bit (\<Gamma>_tm M) (bl_tm M) (buf k)
                                      (pos - sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k))
                               else mt_tape c0 k pos))
              else mt_tape c0 k)
         \<and> mt_pos c = mt_pos c0)"
  by (rule ar_write_prefix_gen
        [OF ar_write_tape_step_in_sub vM qQ kge2 stg0 tcorr ppos poskle buf_valid pad0 src0])

text \<open>The full write phase, re-mirrored into
  \<open>mttm_step (ar_delta_write M)\<close>: the prefix walk
  (\<open>ar_write_prefix_in_sub\<close>) over the first \<open>k_tm M -
  1\<close> tapes followed by the unified last-tape write
  (\<open>ar_write_tape_finish_step_in_sub\<close>), landing at
  \<open>AR_SimAdvance\<close> with every proper tape's block overwritten by
  \<open>write_bit (buf k)\<close> and every \<open>LE\<close> tape / head
  unchanged.  Aggregate cost \<open>\<le> k_tm M \<cdot> 2b\<close>.  The
  split-to-full descriptor collapse, the cardinality bookkeeping, and
  the cost bound are relation-agnostic and transfer verbatim; only the
  relation and the two helper references change.\<close>

lemma ar_write_phase_in_sub:
  fixes M :: "('q, 'a) mttm"
    and cM :: "('a, 'q) mt_config"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and stg0: "mt_state c0 = (q, AR_SimWrite, 0, 0, buf, dvec, posk)"
      and tcorr: "\<forall>k < k_tm M. ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                       (mt_tape cM k) (mt_tape c0 k)"
      and ppos: "\<forall>k < k_tm M. mt_pos c0 k = (if mt_pos cM k = 0 then Suc 0
                       else sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k)
                              + block_width (\<Gamma>_tm M))"
      and poskle: "\<forall>k < k_tm M. posk k = AR_AtLE \<longleftrightarrow> mt_pos cM k = 0"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimWrite, 0, 0, buf, dvec, posk)"
  shows "\<exists>c m. (c0, c) \<in> (mttm_step (ar_delta_write M)) ^^ m
         \<and> m \<le> k_tm M * (2 * block_width (\<Gamma>_tm M))
         \<and> mt_state c = (q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk)
         \<and> mt_tape c = (\<lambda>k. if k < k_tm M
              then (if mt_pos cM k = 0 then mt_tape c0 k
                    else (\<lambda>pos. if sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k) \<le> pos
                                  \<and> pos < sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k)
                                            + block_width (\<Gamma>_tm M)
                               then write_bit (\<Gamma>_tm M) (bl_tm M) (buf k)
                                      (pos - sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k))
                               else mt_tape c0 k pos))
              else mt_tape c0 k)
         \<and> mt_pos c = mt_pos c0"
  by (rule ar_write_phase_gen
        [OF ar_write_prefix_in_sub ar_write_tape_finish_step_in_sub
            vM qQ kge2 stg0 tcorr ppos poskle buf_valid pad0 src0])

text \<open>The advance left-walk loop, re-mirrored into
  \<open>mttm_step (ar_delta_advance M)\<close>.  From an
  \<open>AR_SimAdvance\<close> stage at bit-counter \<open>0\<close>, \<open>n\<close>
  \<open>M'\<close>-steps walk the head \<open>n\<close> cells \<open>L\<close>
  (counter \<open>0 \<rightarrow> n\<close>), tape and other heads unchanged.
  The \<open>relpow_invariant_chain\<close> loop, the per-step
  \<open>\<noteq> LE4\<close> guard, and the displacement bound
  (\<open>ar_disp_le_2k\<close>) are relation-agnostic and transfer
  verbatim; only the relation and the one helper reference change.\<close>

lemma ar_advance_walk_loop_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and stg: "mt_state c0 = (q, AR_SimAdvance, tk, 0, buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and ndisp: "n < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)"
      and notLE: "\<And>j. j < n \<Longrightarrow> mt_tape c0 tk (mt_pos c0 tk - j) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimAdvance, tk, 0, buf, dvec, posk)"
  shows "\<exists>c'. (c0, c') \<in> (mttm_step (ar_delta_advance M)) ^^ n
              \<and> mt_state c' = (q, AR_SimAdvance, tk, n, buf, dvec, posk)
              \<and> mt_pos c' tk = mt_pos c0 tk - n
              \<and> mt_tape c' = mt_tape c0
              \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_pos c' k' = mt_pos c0 k')"
  by (rule ar_advance_walk_loop_gen
        [OF ar_advance_walk_step_in_sub vM qQ stg buf_valid ndisp notLE pad0 src0])

text \<open>The unified single-tape advance, non-last tape, re-mirrored
  into \<open>mttm_step (ar_delta_advance M)\<close>: the
  \<open>R\<close>/non-\<open>R\<close> dispatch.  An \<open>R\<close>-move needs no
  head motion (single boundary step, cost \<open>1\<close>); a
  non-\<open>R\<close>-move walks the head \<open>D = ar_disp\<close> cells
  \<open>L\<close> (the \<open>D - 1\<close>-step
  \<open>ar_advance_walk_loop_in_sub\<close> then the final boundary
  \<open>L\<close>-move), landing at \<open>start - D\<close>.  The
  walk-then-boundary decomposition and the conditional head
  conclusion transfer verbatim; only the relation and the two helper
  references change.\<close>

lemma ar_advance_tape_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and notlast: "\<not> is_last_k M tk"
      and stg: "mt_state c0 = (q, AR_SimAdvance, tk, 0, buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and dge1: "dvec tk \<noteq> dir.R
                  \<Longrightarrow> 0 < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)"
      and notLE: "\<And>m. m < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)
                    \<Longrightarrow> mt_tape c0 tk (mt_pos c0 tk - m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimAdvance, tk, 0, buf, dvec, posk)"
  shows "\<exists>c'. (c0, c') \<in> (mttm_step (ar_delta_advance M))
                            ^^ (if dvec tk = dir.R then 1
                                else ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk))
              \<and> mt_state c' = (q, AR_SimAdvance, k_succ tk, 0, buf, dvec,
                                  posk(tk := ar_newpos (dvec tk) (posk tk)))
              \<and> mt_tape c' = mt_tape c0
              \<and> mt_pos c' = (if dvec tk = dir.R then mt_pos c0
                            else (mt_pos c0)(tk := mt_pos c0 tk
                                   - ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)))"
  by (rule ar_advance_tape_step_gen
        [OF ar_advance_walk_loop_in_sub ar_advance_boundary_step_in_sub
            vM qQ kge2 notlast stg buf_valid dge1 notLE pad0 src0])

text \<open>The unified single-tape advance, last tape, re-mirrored
  into \<open>mttm_step (ar_delta_advance M)\<close>: as
  \<open>ar_advance_tape_step_in_sub\<close> but \<open>tk\<close> is the last
  tape, so the boundary step (\<open>ar_advance_finish_step_in_sub\<close>)
  transitions to \<open>AR_SimNext\<close> (current-tape field reset to
  \<open>k_unidx 0\<close>) rather than advancing to \<open>k_succ tk\<close>.
  Same R/non-R dispatch and walk-then-boundary decomposition; only
  the relation and the two helper references change.\<close>

lemma ar_advance_tape_finish_step_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and last: "is_last_k M tk"
      and stg: "mt_state c0 = (q, AR_SimAdvance, tk, 0, buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and dge1: "dvec tk \<noteq> dir.R
                  \<Longrightarrow> 0 < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)"
      and notLE: "\<And>m. m < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)
                    \<Longrightarrow> mt_tape c0 tk (mt_pos c0 tk - m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimAdvance, tk, 0, buf, dvec, posk)"
  shows "\<exists>c'. (c0, c') \<in> (mttm_step (ar_delta_advance M))
                            ^^ (if dvec tk = dir.R then 1
                                else ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk))
              \<and> mt_state c' = (q, AR_SimNext, k_unidx 0, 0, buf, dvec,
                                  posk(tk := ar_newpos (dvec tk) (posk tk)))
              \<and> mt_tape c' = mt_tape c0
              \<and> mt_pos c' = (if dvec tk = dir.R then mt_pos c0
                            else (mt_pos c0)(tk := mt_pos c0 tk
                                   - ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)))"
  by (rule ar_advance_tape_finish_step_gen
        [OF ar_advance_walk_loop_in_sub ar_advance_finish_step_in_sub
            vM qQ kge2 last stg buf_valid dge1 notLE pad0 src0])

text \<open>The advance prefix walk, re-mirrored into
  \<open>mttm_step (ar_delta_advance M)\<close>: a custom induction on the
  tape index \<open>j\<close> (\<open>j \<le> k_tm M - 1\<close>, every tape it
  touches non-last), iterating \<open>ar_advance_tape_step_in_sub\<close>
  from the boundary tape \<open>k_unidx 0\<close>.  The tape is
  constant; the carried state is a \<open>k_idx k < j\<close> split over
  the \<open>posk\<close> and position vectors.  The induction, the
  descriptor collapse, and the per-tape \<open>notLE\<close>/\<open>dge1\<close>
  entry facts are relation-agnostic and transfer verbatim; only the
  relation and the one helper reference change.\<close>

lemma ar_advance_prefix_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and stg0: "mt_state c0 = (q, AR_SimAdvance, 0, 0, buf0, dvec, posk0)"
      and buf_valid: "\<forall>k. buf0 k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and dge1: "\<forall>k < k_tm M. dvec k \<noteq> dir.R
                  \<longrightarrow> 0 < ar_disp (block_width (\<Gamma>_tm M)) (dvec k) (posk0 k)"
      and notLE: "\<forall>k < k_tm M. \<forall>m. m < ar_disp (block_width (\<Gamma>_tm M)) (dvec k) (posk0 k)
                    \<longrightarrow> mt_tape c0 k (mt_pos c0 k - m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimAdvance, 0, 0, buf0, dvec, posk0)"
  shows "j \<le> k_tm M - 1 \<Longrightarrow>
    (\<exists>c m. (c0, c) \<in> (mttm_step (ar_delta_advance M)) ^^ m
         \<and> m \<le> j * (2 * block_width (\<Gamma>_tm M))
         \<and> mt_state c = (q, AR_SimAdvance, k_unidx j, 0, buf0, dvec,
              (\<lambda>k. if k_idx k < j then ar_newpos (dvec k) (posk0 k)
                    else posk0 k))
         \<and> mt_tape c = mt_tape c0
         \<and> mt_pos c = (\<lambda>k. if k_idx k < j
              then (if dvec k = dir.R then mt_pos c0 k
                    else mt_pos c0 k
                           - ar_disp (block_width (\<Gamma>_tm M)) (dvec k) (posk0 k))
              else mt_pos c0 k))"
  by (rule ar_advance_prefix_gen
        [OF ar_advance_tape_step_in_sub vM qQ kge2 stg0 buf_valid dge1 notLE pad0 src0])

text \<open>The full advance phase, re-mirrored into
  \<open>mttm_step (ar_delta_advance M)\<close>: the prefix walk
  (\<open>ar_advance_prefix_in_sub\<close>) over the first
  \<open>k_tm M - 1\<close> tapes followed by the unified last-tape
  advance (\<open>ar_advance_tape_finish_step_in_sub\<close>), landing at
  \<open>AR_SimNext\<close> (current-tape field \<open>k_unidx 0\<close>) with
  every head moved to \<open>M\<close>'s new position and every \<open>posk\<close>
  updated by \<open>ar_newpos\<close>.  The tape is unchanged.  Aggregate
  cost \<open>\<le> k_tm M \<cdot> 2b\<close>.  The split-to-full descriptor
  collapse and cost bound are relation-agnostic and transfer
  verbatim; only the relation and the two helper references
  change.\<close>

lemma ar_advance_phase_in_sub:
  fixes M :: "('q, 'a) mttm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and stg0: "mt_state c0 = (q, AR_SimAdvance, 0, 0, buf0, dvec, posk0)"
      and buf_valid: "\<forall>k. buf0 k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and dge1: "\<forall>k < k_tm M. dvec k \<noteq> dir.R
                  \<longrightarrow> 0 < ar_disp (block_width (\<Gamma>_tm M)) (dvec k) (posk0 k)"
      and notLE: "\<forall>k < k_tm M. \<forall>m. m < ar_disp (block_width (\<Gamma>_tm M)) (dvec k) (posk0 k)
                    \<longrightarrow> mt_tape c0 k (mt_pos c0 k - m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimAdvance, 0, 0, buf0, dvec, posk0)"
  shows "\<exists>c m. (c0, c) \<in> (mttm_step (ar_delta_advance M)) ^^ m
         \<and> m \<le> k_tm M * (2 * block_width (\<Gamma>_tm M))
         \<and> mt_state c = (q, AR_SimNext, k_unidx 0, 0, buf0, dvec,
              (\<lambda>k. if k < k_tm M then ar_newpos (dvec k) (posk0 k)
                    else posk0 k))
         \<and> mt_tape c = mt_tape c0
         \<and> mt_pos c = (\<lambda>k. if k < k_tm M
              then (if dvec k = dir.R then mt_pos c0 k
                    else mt_pos c0 k - ar_disp (block_width (\<Gamma>_tm M)) (dvec k) (posk0 k))
              else mt_pos c0 k)"
  by (rule ar_advance_phase_gen
        [OF ar_advance_prefix_in_sub ar_advance_tape_finish_step_in_sub
            vM qQ kge2 stg0 buf_valid dge1 notLE pad0 src0])

subsection \<open>Walker preservation — per-substep M'-step lemmas\<close>

text \<open>One preservation lemma per substep predicate: an
  \<open>M'\<close>-step out of a config satisfying the current invariant
  lands at a config satisfying the next invariant in the cycle (or
  splits the disjunction when the substep's relation has multiple
  destination arms).  Together with the chunked engine, these
  characterise the walker's per-step evolution: the substep idx
  carried in the M'-config is the dispatch discriminator at each
  step, no chain pinning needed.\<close>

lemma ar_walker_step_from_boundary:
  fixes M :: "('q, 'a) mttm"
    and cM :: "('a, 'q) mt_config"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes inv: "ar_walker_at_boundary M cM c'"
      and step: "(c', c'') \<in> mttm_step (alphabet_reduce_delta M)"
  shows "ar_walker_in_read M cM c'' \<or> ar_walker_at_compute M cM c''"
proof -
  have rbnd: "ar_at_read_boundary M c'"
    using inv unfolding ar_walker_at_boundary_def by simp
  obtain qM' stg where st: "mt_state c' = (qM', stg)"
    by (cases "mt_state c'") auto
  obtain idx tk i buf dvec posk where
      sg: "stg = (idx, tk, i, buf, dvec, posk)" by (cases stg) auto
  \<comment> \<open>\<open>ar_at_read_boundary\<close>'s condition is a
     non-trivial implication (\<open>idx = AR_SimRead \<longrightarrow> \<dots>\<close>) — but
     the only way \<open>ar_walker_at_boundary\<close> can hold with
     \<open>idx \<noteq> AR_SimRead\<close> would require \<open>ar_simulates\<close>'s
     halt disjunct to fire, which the \<open>ar_at_read_boundary\<close>
     hypothesis combined with stage shape rules out at the boundary
     of a non-halting cycle.  Discharged via \<open>ar_simulates\<close>'s
     state-shape branches.\<close>
  have src: "fst (snd (mt_state c')) = AR_SimRead"
  proof -
    have sim: "ar_simulates M cM c'"
      using inv unfolding ar_walker_at_boundary_def by simp
    have sim_body:
        "((idx = AR_SimRead \<and> qM' \<notin> {t_tm M, r_tm M})
            \<or> (qM' = t_tm M
                 \<and> (idx, tk, i, buf, dvec, posk) = ar_accept_stage (bl_tm M))
            \<or> (qM' = r_tm M
                 \<and> (idx, tk, i, buf, dvec, posk) = ar_reject_stage (bl_tm M)))
         \<and> mt_state cM = qM'"
      using sim unfolding ar_simulates_def by (simp add: st sg Let_def)
    consider (R) "idx = AR_SimRead"
           | (A) "qM' = t_tm M \<and> (idx, tk, i, buf, dvec, posk) = ar_accept_stage (bl_tm M)"
           | (J) "qM' = r_tm M \<and> (idx, tk, i, buf, dvec, posk) = ar_reject_stage (bl_tm M)"
      using sim_body by blast
    thus ?thesis
    proof cases
      case R thus ?thesis using st sg by simp
    next
      case A
      \<comment> \<open>halt-accept stage has \<open>idx = AR_HaltAccept\<close>,
         which together with \<open>ar_at_read_boundary\<close>'s
         \<open>idx = AR_SimRead \<longrightarrow> \<dots>\<close> is consistent only
         if we are NOT at \<open>AR_SimRead\<close>.  But the step
         out of a halt-coerced config is impossible — \<open>S\<close>
         in \<open>mttm_step.cases\<close> with \<open>fst (snd S) = AR_HaltAccept\<close>
         cannot fire any of the five substep relations
         (constructor-distinctness from
         \<open>alphabet_reduce_delta_src_tag\<close>).\<close>
      have idx_acc: "idx = AR_HaltAccept"
        using A by (simp add: ar_accept_stage_def)
      from step obtain S ts n S' aw dir where
          c'_eq: "c' = Config\<^sub>M S ts n"
        and rel: "(S, (\<lambda>k. ts k (n k)), S', aw, dir)
                    \<in> alphabet_reduce_delta M"
        by (auto elim: mttm_step.cases)
      have src_S: "fst (snd S) = AR_HaltAccept"
        using c'_eq st sg idx_acc by simp
      from alphabet_reduce_delta_src_tag[OF rel]
      have "fst (snd S) \<in> {AR_SimRead, AR_SimCompute, AR_SimWrite,
                            AR_SimAdvance, AR_SimNext}" .
      hence False using src_S by auto
      thus ?thesis ..
    next
      case J
      have idx_rej: "idx = AR_HaltReject"
        using J by (simp add: ar_reject_stage_def)
      from step obtain S ts n S' aw dir where
          c'_eq: "c' = Config\<^sub>M S ts n"
        and rel: "(S, (\<lambda>k. ts k (n k)), S', aw, dir)
                    \<in> alphabet_reduce_delta M"
        by (auto elim: mttm_step.cases)
      have src_S: "fst (snd S) = AR_HaltReject"
        using c'_eq st sg idx_rej by simp
      from alphabet_reduce_delta_src_tag[OF rel]
      have "fst (snd S) \<in> {AR_SimRead, AR_SimCompute, AR_SimWrite,
                            AR_SimAdvance, AR_SimNext}" .
      hence False using src_S by auto
      thus ?thesis ..
    qed
  qed
  \<comment> \<open>The M'-step fires \<open>ar_delta_read\<close> by src-tag
     uniqueness; the lift extends the witness chain by one step.\<close>
  have step_read: "(c', c'') \<in> mttm_step (ar_delta_read M)"
    using ar_step_read_lift[OF src step] .
  hence step_read1: "(c', c'') \<in> (mttm_step (ar_delta_read M)) ^^ Suc 0"
    by simp
  \<comment> \<open>Dispatch on the dest tag\<close>
  from ar_step_from_SimRead_lands[OF step src]
  have dest: "fst (snd (mt_state c'')) = AR_SimRead
            \<or> fst (snd (mt_state c'')) = AR_SimCompute" .
  thus ?thesis
  proof
    assume dr: "fst (snd (mt_state c'')) = AR_SimRead"
    have "ar_walker_in_read M cM c''"
      unfolding ar_walker_in_read_def
      using dr inv step_read1 by blast
    thus ?thesis ..
  next
    assume dc: "fst (snd (mt_state c'')) = AR_SimCompute"
    have "ar_walker_at_compute M cM c''"
      unfolding ar_walker_at_compute_def
      using dc inv step_read1 by blast
    thus ?thesis ..
  qed
qed

lemma ar_walker_step_from_in_read:
  fixes M :: "('q, 'a) mttm"
    and cM :: "('a, 'q) mt_config"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes inv: "ar_walker_in_read M cM c'"
      and step: "(c', c'') \<in> mttm_step (alphabet_reduce_delta M)"
  shows "ar_walker_in_read M cM c'' \<or> ar_walker_at_compute M cM c''"
proof -
  have src: "fst (snd (mt_state c')) = AR_SimRead"
    using inv unfolding ar_walker_in_read_def by simp
  obtain c_b m where
      wb: "ar_walker_at_boundary M cM c_b"
    and chain: "(c_b, c') \<in> (mttm_step (ar_delta_read M)) ^^ m"
    using inv unfolding ar_walker_in_read_def by blast
  have step_read: "(c', c'') \<in> mttm_step (ar_delta_read M)"
    using ar_step_read_lift[OF src step] .
  have chain_ext: "(c_b, c'') \<in> (mttm_step (ar_delta_read M)) ^^ Suc m"
    using chain step_read by (rule relpow_Suc_I)
  from ar_step_from_SimRead_lands[OF step src]
  have dest: "fst (snd (mt_state c'')) = AR_SimRead
            \<or> fst (snd (mt_state c'')) = AR_SimCompute" .
  thus ?thesis
  proof
    assume dr: "fst (snd (mt_state c'')) = AR_SimRead"
    have "ar_walker_in_read M cM c''"
      unfolding ar_walker_in_read_def
      using dr wb chain_ext by blast
    thus ?thesis ..
  next
    assume dc: "fst (snd (mt_state c'')) = AR_SimCompute"
    have "ar_walker_at_compute M cM c''"
      unfolding ar_walker_at_compute_def
      using dc wb chain_ext by blast
    thus ?thesis ..
  qed
qed

lemma ar_walker_step_from_at_compute:
  fixes M :: "('q, 'a) mttm"
    and cM :: "('a, 'q) mt_config"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes inv: "ar_walker_at_compute M cM c'"
      and step: "(c', c'') \<in> mttm_step (alphabet_reduce_delta M)"
      and vM: "valid_mttm M"
      and qQ: "mt_state cM \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and tapeG: "\<And>k. mt_tape cM k (mt_pos cM k) \<in> \<Gamma>_tm M"
  shows "ar_walker_in_write M cM c''"
proof -
  let ?k = "block_width (\<Gamma>_tm M)"
  let ?aM = "\<lambda>k. mt_tape cM k (mt_pos cM k)"
  have c'_compute: "fst (snd (mt_state c')) = AR_SimCompute"
    using inv unfolding ar_walker_at_compute_def by simp
  obtain c_b m_w where
      wb: "ar_walker_at_boundary M cM c_b"
    and chain_w: "(c_b, c') \<in> (mttm_step (ar_delta_read M)) ^^ m_w"
    using inv unfolding ar_walker_at_compute_def by blast
  have sim: "ar_simulates M cM c_b"
    using wb unfolding ar_walker_at_boundary_def by simp
  have pcons: "ar_posk_consistent M cM c_b"
    using wb unfolding ar_walker_at_boundary_def by simp
  have rbnd: "ar_at_read_boundary M c_b"
    using wb unfolding ar_walker_at_boundary_def by simp
  \<comment> \<open>\<open>c_b\<close>'s tag is \<open>AR_SimRead\<close>: from a chain step (when
     \<open>m_w > 0\<close>) by \<open>ar_delta_read_src\<close>, or by ruling out the
     halt branches of \<open>ar_simulates\<close> (when \<open>m_w = 0\<close>).\<close>
  have cb_idx: "fst (snd (mt_state c_b)) = AR_SimRead"
  proof (cases m_w)
    case 0
    have cb_eq: "c_b = c'" using chain_w 0 by simp
    have cb_compute: "fst (snd (mt_state c_b)) = AR_SimCompute"
      using c'_compute cb_eq by simp
    obtain qM' stg where st_b: "mt_state c_b = (qM', stg)"
      by (cases "mt_state c_b") auto
    obtain idx tk i buf dvec posk where
        sg_b: "stg = (idx, tk, i, buf, dvec, posk)" by (cases stg) auto
    have idx_cpu: "idx = AR_SimCompute" using cb_compute st_b sg_b by simp
    have "(idx = AR_SimRead \<and> qM' \<notin> {t_tm M, r_tm M})
            \<or> (qM' = t_tm M \<and> stg = ar_accept_stage (bl_tm M))
            \<or> (qM' = r_tm M \<and> stg = ar_reject_stage (bl_tm M))"
      using sim st_b sg_b unfolding ar_simulates_def by (auto split: prod.splits)
    hence False
      using idx_cpu sg_b
      by (auto simp: ar_accept_stage_def ar_reject_stage_def)
    thus ?thesis ..
  next
    case (Suc m')
    have hsuc: "(c_b, c') \<in> (mttm_step (ar_delta_read M)) ^^ Suc m'"
      using chain_w Suc by simp
    obtain c_1 where
        first: "(c_b, c_1) \<in> mttm_step (ar_delta_read M)"
      using relpow_Suc_D2[OF hsuc] by blast
    from first obtain S ts n S' aw dir where
        ceq: "c_b = Config\<^sub>M S ts n"
      and rel: "(S, (\<lambda>k. ts k (n k)), S', aw, dir) \<in> ar_delta_read M"
      by (auto elim: mttm_step.cases)
    have "fst (snd S) = AR_SimRead" using ar_delta_read_src[OF rel] .
    thus ?thesis using ceq by simp
  qed
  \<comment> \<open>Extract \<open>c_b\<close>'s full state shape and the boundary's
     correspondences.\<close>
  obtain qM' stg where st_b: "mt_state c_b = (qM', stg)"
    by (cases "mt_state c_b") auto
  obtain idx tk i buf dvec posk where
      sg_b: "stg = (idx, tk, i, buf, dvec, posk)" by (cases stg) auto
  have idx_read: "idx = AR_SimRead" using cb_idx st_b sg_b by simp
  have sim_unfold: "(idx = AR_SimRead \<and> qM' \<notin> {t_tm M, r_tm M})
            \<or> (qM' = t_tm M \<and> stg = ar_accept_stage (bl_tm M))
            \<or> (qM' = r_tm M \<and> stg = ar_reject_stage (bl_tm M))"
    using sim st_b sg_b unfolding ar_simulates_def by (auto split: prod.splits)
  have qM'_eq: "qM' = mt_state cM"
    using sim st_b sg_b unfolding ar_simulates_def by (auto split: prod.splits)
  have tcorr: "\<forall>k < k_tm M. ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                       (mt_tape cM k) (mt_tape c_b k)"
    using sim st_b sg_b unfolding ar_simulates_def by (auto split: prod.splits)
  have ppos: "\<And>k. mt_pos c_b k = sim_pos ?k (mt_pos cM k)"
    using sim st_b sg_b idx_read
    unfolding ar_simulates_def by (auto split: prod.splits)
  have pkok: "\<And>k. posk k = AR_AtLE \<longleftrightarrow> mt_pos cM k = 0"
    using pcons st_b sg_b idx_read
    unfolding ar_posk_consistent_def by (auto split: prod.splits)
  have bnd_unfold: "idx = AR_SimRead
        \<longrightarrow> (tk = 0 \<and> i = 0
             \<and> (\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M})
             \<and> ar_stage_bounded (bl_tm M) (k_tm M)
                  (idx, tk, i, buf, dvec, posk))"
    using rbnd st_b sg_b
    unfolding ar_at_read_boundary_def by (auto split: prod.splits)
  have tk0: "tk = 0" and i0: "i = 0"
    and bufG: "\<And>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using bnd_unfold idx_read by simp_all
  have stg0: "mt_state c_b = (mt_state cM, AR_SimRead, 0, 0, buf, dvec, posk)"
    using st_b sg_b qM'_eq idx_read tk0 i0 by simp
  \<comment> \<open>Boundary blank-tail and bounded-stage facts, now produced by the
     strengthened \<open>ar_at_read_boundary\<close>: \<open>src0_b\<close> from its
     bounded-stage conjunct (specialised by \<open>idx = AR_SimRead\<close>,
     \<open>tk = 0\<close>, \<open>i = 0\<close>); \<open>pad0_b\<close> from its config
     padding-blank conjunct.\<close>
  have pad0_b: "\<forall>j \<ge> k_tm M. mt_tape c_b j (mt_pos c_b j) = BLANK4"
    using rbnd unfolding ar_at_read_boundary_def by (auto split: prod.splits)
  have src0_b: "ar_stage_bounded (bl_tm M) (k_tm M)
                  (AR_SimRead, 0, 0, buf, dvec, posk)"
    using bnd_unfold idx_read tk0 i0 by simp
  \<comment> \<open>Apply \<open>ar_read_phase_in_sub\<close> at the boundary.\<close>
  obtain c_r m_phase where
      r_chain: "(c_b, c_r) \<in> (mttm_step (ar_delta_read M)) ^^ m_phase"
    and r_state: "mt_state c_r = (mt_state cM, AR_SimCompute, k_unidx 0, 0,
                    (\<lambda>k. if k < k_tm M then ?aM k else buf k), dvec,
                    (\<lambda>k. if k < k_tm M
                          then (if mt_pos cM k = 0 then AR_AtLE
                                else if mt_pos cM k = 1 then AR_AtFirstProper
                                else AR_AtFurtherProper)
                          else posk k))"
    using ar_read_phase_in_sub[OF vM qQ kge2 stg0 tcorr ppos pkok tapeG bufG
                                  pad0_b src0_b]
    by blast
  have r_cpu: "fst (snd (mt_state c_r)) = AR_SimCompute"
    using r_state by simp
  \<comment> \<open>Pin the walker's witness chain against \<open>ar_read_phase_in_sub\<close>'s.\<close>
  have c'_eq_c_r: "c' = c_r"
    using chain_ar_delta_read_to_SimCompute_uniq[OF chain_w r_chain c'_compute r_cpu]
    by simp
  have c'_state: "mt_state c' = (mt_state cM, AR_SimCompute, k_unidx 0, 0,
                    (\<lambda>k. if k < k_tm M then ?aM k else buf k), dvec,
                    (\<lambda>k. if k < k_tm M
                          then (if mt_pos cM k = 0 then AR_AtLE
                                else if mt_pos cM k = 1 then AR_AtFirstProper
                                else AR_AtFurtherProper)
                          else posk k))"
    using c'_eq_c_r r_state by simp
  \<comment> \<open>Lift the compute step to the sub-relation and invert.\<close>
  have step_compute: "(c', c'') \<in> mttm_step (ar_delta_compute M)"
    using ar_step_compute_lift[OF c'_compute step] .
  obtain q' m_a' m_d where
      mdelta: "(mt_state cM, (\<lambda>k. if k < k_tm M then ?aM k else buf k),
                  q', m_a', m_d) \<in> delta_tm M"
    and c''_state: "mt_state c'' = (q', AR_SimWrite, 0, 0, m_a', m_d,
                      (\<lambda>k. if k < k_tm M
                            then (if mt_pos cM k = 0 then AR_AtLE
                                  else if mt_pos cM k = 1 then AR_AtFirstProper
                                  else AR_AtFurtherProper)
                            else posk k))"
    and c''_tape: "mt_tape c'' = mt_tape c'"
    and c''_pos: "mt_pos c'' = mt_pos c'"
    using ar_compute_step_inv[OF step c'_state] by blast
  \<comment> \<open>Bundle the witness chain into \<open>ar_walker_in_write\<close>.\<close>
  have c''_write: "fst (snd (mt_state c'')) = AR_SimWrite"
    using c''_state by simp
  have empty_w: "(c'', c'') \<in> (mttm_step (ar_delta_write M)) ^^ 0" by simp
  show "ar_walker_in_write M cM c''"
    unfolding ar_walker_in_write_def
  proof (intro conjI)
    show "fst (snd (mt_state c'')) = AR_SimWrite" by (rule c''_write)
    show "\<exists>c_b c_w m_r m_w.
            ar_walker_at_boundary M cM c_b
          \<and> (c_b, c_w) \<in> (mttm_step (ar_delta_read M)) ^^ m_r
          \<and> fst (snd (mt_state c_w)) = AR_SimCompute
          \<and> (\<exists>c_w_post. (c_w, c_w_post) \<in> mttm_step (ar_delta_compute M)
                          \<and> (c_w_post, c'') \<in> (mttm_step (ar_delta_write M)) ^^ m_w)"
      by (intro exI[where x = c_b] exI[where x = c'] exI[where x = m_w]
                exI[where x = 0] conjI wb chain_w c'_compute
                exI[where x = c''] step_compute empty_w)
  qed
qed

lemma ar_walker_step_from_in_write:
  fixes M :: "('q, 'a) mttm"
    and cM :: "('a, 'q) mt_config"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes inv: "ar_walker_in_write M cM c'"
      and step: "(c', c'') \<in> mttm_step (alphabet_reduce_delta M)"
  shows "ar_walker_in_write M cM c'' \<or> ar_walker_in_advance M cM c''"
proof -
  have src: "fst (snd (mt_state c')) = AR_SimWrite"
    using inv unfolding ar_walker_in_write_def by simp
  obtain c_b c_w m_r m_w where
      wb:   "ar_walker_at_boundary M cM c_b"
    and chr:  "(c_b, c_w) \<in> (mttm_step (ar_delta_read M)) ^^ m_r"
    and cwC:  "fst (snd (mt_state c_w)) = AR_SimCompute"
    and rest: "\<exists>c_w_post. (c_w, c_w_post) \<in> mttm_step (ar_delta_compute M)
                          \<and> (c_w_post, c') \<in> (mttm_step (ar_delta_write M)) ^^ m_w"
    using inv unfolding ar_walker_in_write_def by blast
  obtain c_w_post where
      ccs: "(c_w, c_w_post) \<in> mttm_step (ar_delta_compute M)"
    and chw: "(c_w_post, c') \<in> (mttm_step (ar_delta_write M)) ^^ m_w"
    using rest by blast
  have step_write: "(c', c'') \<in> mttm_step (ar_delta_write M)"
    using ar_step_write_lift[OF src step] .
  have chw_ext: "(c_w_post, c'') \<in> (mttm_step (ar_delta_write M)) ^^ Suc m_w"
    using chw step_write by (rule relpow_Suc_I)
  from ar_step_from_SimWrite_lands[OF step src]
  have dest: "fst (snd (mt_state c'')) = AR_SimWrite
            \<or> fst (snd (mt_state c'')) = AR_SimAdvance" .
  thus ?thesis
  proof
    assume dw: "fst (snd (mt_state c'')) = AR_SimWrite"
    have "ar_walker_in_write M cM c''"
      unfolding ar_walker_in_write_def
    proof (intro conjI)
      show "fst (snd (mt_state c'')) = AR_SimWrite" by (rule dw)
      show "\<exists>c_b c_w m_r m_w.
              ar_walker_at_boundary M cM c_b
              \<and> (c_b, c_w) \<in> (mttm_step (ar_delta_read M)) ^^ m_r
              \<and> fst (snd (mt_state c_w)) = AR_SimCompute
              \<and> (\<exists>c_w_post.
                   (c_w, c_w_post) \<in> mttm_step (ar_delta_compute M)
                 \<and> (c_w_post, c'') \<in> (mttm_step (ar_delta_write M)) ^^ m_w)"
        by (intro exI[where x = c_b] exI[where x = c_w] exI[where x = m_r]
                  exI[where x = "Suc m_w"] conjI wb chr cwC
                  exI[where x = c_w_post] ccs chw_ext)
    qed
    thus ?thesis ..
  next
    assume da: "fst (snd (mt_state c'')) = AR_SimAdvance"
    \<comment> \<open>Cycle transition write to advance: \<open>c''\<close> opens the
        advance phase with zero advance-steps elapsed.\<close>
    have empty_a: "(c'', c'') \<in> (mttm_step (ar_delta_advance M)) ^^ 0"
      by simp
    have "ar_walker_in_advance M cM c''"
      unfolding ar_walker_in_advance_def
    proof (intro conjI)
      show "fst (snd (mt_state c'')) = AR_SimAdvance" by (rule da)
      show "\<exists>c_b c_w c_a m_r m_w m_a.
              ar_walker_at_boundary M cM c_b
              \<and> (c_b, c_w) \<in> (mttm_step (ar_delta_read M)) ^^ m_r
              \<and> fst (snd (mt_state c_w)) = AR_SimCompute
              \<and> fst (snd (mt_state c_a)) = AR_SimAdvance
              \<and> (\<exists>c_w_post.
                   (c_w, c_w_post) \<in> mttm_step (ar_delta_compute M)
                 \<and> (c_w_post, c_a) \<in> (mttm_step (ar_delta_write M)) ^^ m_w
                 \<and> (c_a, c'') \<in> (mttm_step (ar_delta_advance M)) ^^ m_a)"
        by (intro exI[where x = c_b] exI[where x = c_w] exI[where x = c'']
                  exI[where x = m_r] exI[where x = "Suc m_w"] exI[where x = 0]
                  conjI wb chr cwC da
                  exI[where x = c_w_post] ccs chw_ext empty_a)
    qed
    thus ?thesis ..
  qed
qed

lemma ar_walker_step_from_in_advance:
  fixes M :: "('q, 'a) mttm"
    and cM :: "('a, 'q) mt_config"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes inv: "ar_walker_in_advance M cM c'"
      and step: "(c', c'') \<in> mttm_step (alphabet_reduce_delta M)"
  shows "ar_walker_in_advance M cM c'' \<or> ar_walker_at_next M cM c''"
proof -
  have src: "fst (snd (mt_state c')) = AR_SimAdvance"
    using inv unfolding ar_walker_in_advance_def by simp
  obtain c_b c_w c_a m_r m_w m_a where
      wb:   "ar_walker_at_boundary M cM c_b"
    and chr:  "(c_b, c_w) \<in> (mttm_step (ar_delta_read M)) ^^ m_r"
    and cwC:  "fst (snd (mt_state c_w)) = AR_SimCompute"
    and caC:  "fst (snd (mt_state c_a)) = AR_SimAdvance"
    and rest: "\<exists>c_w_post.
                  (c_w, c_w_post) \<in> mttm_step (ar_delta_compute M)
                \<and> (c_w_post, c_a) \<in> (mttm_step (ar_delta_write M)) ^^ m_w
                \<and> (c_a, c') \<in> (mttm_step (ar_delta_advance M)) ^^ m_a"
    using inv unfolding ar_walker_in_advance_def by blast
  obtain c_w_post where
      ccs: "(c_w, c_w_post) \<in> mttm_step (ar_delta_compute M)"
    and chw: "(c_w_post, c_a) \<in> (mttm_step (ar_delta_write M)) ^^ m_w"
    and cha: "(c_a, c') \<in> (mttm_step (ar_delta_advance M)) ^^ m_a"
    using rest by blast
  have step_advance: "(c', c'') \<in> mttm_step (ar_delta_advance M)"
    using ar_step_advance_lift[OF src step] .
  have cha_ext: "(c_a, c'') \<in> (mttm_step (ar_delta_advance M)) ^^ Suc m_a"
    using cha step_advance by (rule relpow_Suc_I)
  from ar_step_from_SimAdvance_lands[OF step src]
  have dest: "fst (snd (mt_state c'')) = AR_SimAdvance
            \<or> fst (snd (mt_state c'')) = AR_SimNext" .
  thus ?thesis
  proof
    assume da: "fst (snd (mt_state c'')) = AR_SimAdvance"
    have "ar_walker_in_advance M cM c''"
      unfolding ar_walker_in_advance_def
    proof (intro conjI)
      show "fst (snd (mt_state c'')) = AR_SimAdvance" by (rule da)
      show "\<exists>c_b c_w c_a m_r m_w m_a.
              ar_walker_at_boundary M cM c_b
              \<and> (c_b, c_w) \<in> (mttm_step (ar_delta_read M)) ^^ m_r
              \<and> fst (snd (mt_state c_w)) = AR_SimCompute
              \<and> fst (snd (mt_state c_a)) = AR_SimAdvance
              \<and> (\<exists>c_w_post.
                   (c_w, c_w_post) \<in> mttm_step (ar_delta_compute M)
                 \<and> (c_w_post, c_a) \<in> (mttm_step (ar_delta_write M)) ^^ m_w
                 \<and> (c_a, c'') \<in> (mttm_step (ar_delta_advance M)) ^^ m_a)"
        by (intro exI[where x = c_b] exI[where x = c_w] exI[where x = c_a]
                  exI[where x = m_r] exI[where x = m_w] exI[where x = "Suc m_a"]
                  conjI wb chr cwC caC
                  exI[where x = c_w_post] ccs chw cha_ext)
    qed
    thus ?thesis ..
  next
    assume dn: "fst (snd (mt_state c'')) = AR_SimNext"
    \<comment> \<open>Cycle transition advance to next: extended advance chain
        lands at \<open>c''\<close>, the redundant \<open>c_n = c'\<close> conjunct
        instantiates with \<open>c_n = c''\<close>.\<close>
    have "ar_walker_at_next M cM c''"
      unfolding ar_walker_at_next_def
    proof (intro conjI)
      show "fst (snd (mt_state c'')) = AR_SimNext" by (rule dn)
      show "\<exists>c_b c_w c_a c_n m_r m_w m_a.
              ar_walker_at_boundary M cM c_b
              \<and> (c_b, c_w) \<in> (mttm_step (ar_delta_read M)) ^^ m_r
              \<and> fst (snd (mt_state c_w)) = AR_SimCompute
              \<and> fst (snd (mt_state c_a)) = AR_SimAdvance
              \<and> (\<exists>c_w_post.
                   (c_w, c_w_post) \<in> mttm_step (ar_delta_compute M)
                 \<and> (c_w_post, c_a) \<in> (mttm_step (ar_delta_write M)) ^^ m_w
                 \<and> (c_a, c_n) \<in> (mttm_step (ar_delta_advance M)) ^^ m_a
                 \<and> c_n = c'')"
        by (intro exI[where x = c_b] exI[where x = c_w] exI[where x = c_a]
                  exI[where x = c''] exI[where x = m_r] exI[where x = m_w]
                  exI[where x = "Suc m_a"] conjI wb chr cwC caC
                  exI[where x = c_w_post] ccs chw cha_ext refl)
    qed
    thus ?thesis ..
  qed
qed

text \<open>The sixth and final substep preservation closes the
  walker suite mechanically: an \<open>M'\<close>-step out of
  \<open>AR_SimNext\<close> lands at \<open>AR_SimRead\<close> (cycle close),
  \<open>AR_HaltAccept\<close>, or \<open>AR_HaltReject\<close> by
  \<open>ar_step_from_SimNext_lands\<close>.  This is a pure dispatch
  lemma — establishing the boundary for the reconstructed
  \<open>M\<close>-successor at a cycle close is a separate cycle-level
  concern handled by \<open>ar_walker_cycle_close\<close> and the chunked
  reverse engine.  Keeping the \<open>at_next\<close> walker preservation
  thin keeps the suite uniform — all six are one-substep
  mechanical lemmas.  Itself currently uncalled — the cycle close runs
  through \<open>ar_walker_cycle_close\<close> directly — kept to complete the
  six-member walker-preservation suite.\<close>

lemma ar_walker_step_from_at_next:
  fixes M :: "('q, 'a) mttm"
    and cM :: "('a, 'q) mt_config"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes inv: "ar_walker_at_next M cM c'"
      and step: "(c', c'') \<in> mttm_step (alphabet_reduce_delta M)"
  shows "fst (snd (mt_state c'')) = AR_SimRead
       \<or> fst (snd (mt_state c'')) = AR_HaltAccept
       \<or> fst (snd (mt_state c'')) = AR_HaltReject"
proof -
  have src: "fst (snd (mt_state c')) = AR_SimNext"
    using inv unfolding ar_walker_at_next_def by simp
  show ?thesis using ar_step_from_SimNext_lands[OF step src] .
qed

subsection \<open>Cycle-close bridging lemma\<close>

text \<open>An \<open>AR_SimNext\<close> step closes a simulation cycle: the walker is
  re-established at a boundary for the next \<open>M\<close>-configuration.  The
  successor is \<^emph>\<open>reconstructed\<close> from the pinned compute branch
  (the \<open>\<exists>cM'\<close> in the conclusion): under nondeterministic
  \<open>delta_tm M\<close> the source \<open>cM\<close> may have several successors, so the
  fired branch is recovered from the walker's own witness chain rather
  than assumed.  The forward
  arm is rebuilt entirely over the substep sub-relations and each walker
  witness chain is pinned by a \<open>chain_ar_delta_X_to_Y_uniq\<close> suite.

  The closing next step is inverted by \<open>ar_next_step_inv\<close>, which
  dispatches on the reconstructed \<open>M\<close>-state \<open>q'\<close> into three
  outcomes: continue (\<open>q' \<notin> {t, r}\<close>, landing at \<open>AR_SimRead\<close>),
  accept (\<open>q' = t_tm M\<close>) or reject (\<open>q' = r_tm M\<close>).  All three
  re-establish \<open>ar_walker_at_boundary M cMn c''\<close>: the boundary
  invariant carries the halt cases too — \<open>ar_simulates\<close>'s state
  disjunction has dedicated accept/reject arms, and both
  \<open>ar_posk_consistent\<close> and \<open>ar_at_read_boundary\<close> are
  \<open>AR_SimRead\<close>-guarded, hence vacuous off the read boundary.  The
  three predicates are discharged from the explicit endpoint by the shared
  semantic lemmas (\<open>ar_write_tape_correspondence\<close>,
  \<open>ar_advance_newsimpos\<close>, \<open>ar_newpos_atLE_iff\<close>).  No union chain
  is pinned and \<open>ar_simulates_forward_step\<close> is not invoked.\<close>

lemma ar_walker_cycle_close:
  fixes M :: "('q, 'a) mttm"
    and w :: "'a list"
    and cM :: "('a, 'q) mt_config"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes inv: "ar_walker_at_next M cM c'"
      and step: "(c', c'') \<in> mttm_step (alphabet_reduce_delta M)"
      and vM: "valid_mttm M"
      and qQ: "mt_state cM \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and tapeG: "\<And>k. mt_tape cM k (mt_pos cM k) \<in> \<Gamma>_tm M"
      and w_sub: "set w \<subseteq> Sigma_tm M"
      and reach_M: "(init_config_mttm M w, cM) \<in> (mttm_step (delta_tm M))\<^sup>*"
      and lebl: "le_tm M \<noteq> bl_tm M"
  shows "\<exists>cM'. (cM, cM') \<in> mttm_step (delta_tm M)
               \<and> ar_walker_at_boundary M cM' c''"
proof -
  let ?k = "block_width (\<Gamma>_tm M)"
  let ?aM = "\<lambda>k. mt_tape cM k (mt_pos cM k)"
  have kpos_tm: "0 < k_tm M" using vM by (cases M) auto
  \<comment> \<open>Unpack the \<open>ar_walker_at_next\<close> witness.\<close>
  obtain c_b c_w c_a c_n m_r m_w m_a c_w_post where
      wb: "ar_walker_at_boundary M cM c_b"
    and chain_r: "(c_b, c_w) \<in> (mttm_step (ar_delta_read M)) ^^ m_r"
    and cw_cpu: "fst (snd (mt_state c_w)) = AR_SimCompute"
    and ca_adv: "fst (snd (mt_state c_a)) = AR_SimAdvance"
    and cstep: "(c_w, c_w_post) \<in> mttm_step (ar_delta_compute M)"
    and wchain: "(c_w_post, c_a) \<in> (mttm_step (ar_delta_write M)) ^^ m_w"
    and achain0: "(c_a, c_n) \<in> (mttm_step (ar_delta_advance M)) ^^ m_a"
    and cn_eq: "c_n = c'"
    using inv unfolding ar_walker_at_next_def by blast
  have achain: "(c_a, c') \<in> (mttm_step (ar_delta_advance M)) ^^ m_a"
    using achain0 cn_eq by simp
  have c'_next: "fst (snd (mt_state c')) = AR_SimNext"
    using inv unfolding ar_walker_at_next_def by simp
  have sim: "ar_simulates M cM c_b"
    using wb unfolding ar_walker_at_boundary_def by simp
  have pcons: "ar_posk_consistent M cM c_b"
    using wb unfolding ar_walker_at_boundary_def by simp
  have rbnd: "ar_at_read_boundary M c_b"
    using wb unfolding ar_walker_at_boundary_def by simp
  have cb_idx: "fst (snd (mt_state c_b)) = AR_SimRead"
  proof (cases m_r)
    case 0
    have cb_eq: "c_b = c_w" using chain_r 0 by simp
    have cb_compute: "fst (snd (mt_state c_b)) = AR_SimCompute"
      using cw_cpu cb_eq by simp
    obtain qM' stg where st_b: "mt_state c_b = (qM', stg)"
      by (cases "mt_state c_b") auto
    obtain idx tk i buf dvec posk where
        sg_b: "stg = (idx, tk, i, buf, dvec, posk)" by (cases stg) auto
    have idx_cpu: "idx = AR_SimCompute" using cb_compute st_b sg_b by simp
    have "(idx = AR_SimRead \<and> qM' \<notin> {t_tm M, r_tm M})
            \<or> (qM' = t_tm M \<and> stg = ar_accept_stage (bl_tm M))
            \<or> (qM' = r_tm M \<and> stg = ar_reject_stage (bl_tm M))"
      using sim st_b sg_b unfolding ar_simulates_def by (auto split: prod.splits)
    hence False using idx_cpu sg_b
      by (auto simp: ar_accept_stage_def ar_reject_stage_def)
    thus ?thesis ..
  next
    case (Suc m')
    have hsuc: "(c_b, c_w) \<in> (mttm_step (ar_delta_read M)) ^^ Suc m'"
      using chain_r Suc by simp
    obtain c_1 where first: "(c_b, c_1) \<in> mttm_step (ar_delta_read M)"
      using relpow_Suc_D2[OF hsuc] by blast
    from first obtain S ts n S' aw dir where
        ceq: "c_b = Config\<^sub>M S ts n"
      and rel: "(S, (\<lambda>k. ts k (n k)), S', aw, dir) \<in> ar_delta_read M"
      by (auto elim: mttm_step.cases)
    have "fst (snd S) = AR_SimRead" using ar_delta_read_src[OF rel] .
    thus ?thesis using ceq by simp
  qed
  obtain qM' stg where st_b: "mt_state c_b = (qM', stg)"
    by (cases "mt_state c_b") auto
  obtain idx tk i buf dvec posk where
      sg_b: "stg = (idx, tk, i, buf, dvec, posk)" by (cases stg) auto
  have idx_read: "idx = AR_SimRead" using cb_idx st_b sg_b by simp
  have qM'_eq: "qM' = mt_state cM"
    using sim st_b sg_b unfolding ar_simulates_def by (auto split: prod.splits)
  have tcorr: "\<forall>k < k_tm M. ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                       (mt_tape cM k) (mt_tape c_b k)"
    using sim st_b sg_b unfolding ar_simulates_def by (auto split: prod.splits)
  have ppos: "\<And>k. mt_pos c_b k = sim_pos ?k (mt_pos cM k)"
    using sim st_b sg_b idx_read
    unfolding ar_simulates_def by (auto split: prod.splits)
  have pkok: "\<And>k. posk k = AR_AtLE \<longleftrightarrow> mt_pos cM k = 0"
    using pcons st_b sg_b idx_read
    unfolding ar_posk_consistent_def by (auto split: prod.splits)
  have bnd_unfold: "idx = AR_SimRead
        \<longrightarrow> (tk = 0 \<and> i = 0
             \<and> (\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M})
             \<and> ar_stage_bounded (bl_tm M) (k_tm M)
                  (idx, tk, i, buf, dvec, posk))"
    using rbnd st_b sg_b
    unfolding ar_at_read_boundary_def by (auto split: prod.splits)
  have tk0: "tk = 0" and i0: "i = 0"
    and bufG: "\<And>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using bnd_unfold idx_read by simp_all
  have src_b: "ar_stage_bounded (bl_tm M) (k_tm M)
                 (AR_SimRead, 0, 0, buf, dvec, posk)"
    using bnd_unfold idx_read tk0 i0 by simp
  have pad_b: "\<forall>j \<ge> k_tm M. mt_tape c_b j (mt_pos c_b j) = BLANK4"
    using rbnd unfolding ar_at_read_boundary_def by (auto split: prod.splits)
  have stg0: "mt_state c_b = (mt_state cM, AR_SimRead, 0, 0, buf, dvec, posk)"
    using st_b sg_b qM'_eq idx_read tk0 i0 by simp
  have buf_tail: "\<forall>j \<ge> k_tm M. buf j = bl_tm M"
    using src_b by (simp add: ar_stage_bounded_def)
  have dvec_tail: "\<forall>j \<ge> k_tm M. dvec j = dir.N"
    using src_b by (simp add: ar_stage_bounded_def)
  have posk_tail: "\<forall>j \<ge> k_tm M. posk j = AR_AtLE"
    using src_b by (simp add: ar_stage_bounded_def)
  have valcM: "valid_config_mttm M cM"
    using valid_reach_mttm[OF vM w_sub reach_M] .
  have aM_tail: "\<forall>j \<ge> k_tm M. mt_tape cM j (mt_pos cM j) = bl_tm M"
    using valid_config_mttm_blank_tail[OF valcM] by blast
  \<comment> \<open>Read-pin: reconstruct the canonical compute config (guarded read
     buffer / posk / position), pin the walker's read chain to it.\<close>
  let ?rbuf = "\<lambda>k. if k < k_tm M then ?aM k else buf k"
  let ?rposk = "\<lambda>k. if k < k_tm M
                     then (if mt_pos cM k = 0 then AR_AtLE
                           else if mt_pos cM k = 1 then AR_AtFirstProper
                           else AR_AtFurtherProper)
                     else posk k"
  let ?rpos = "\<lambda>k. if k < k_tm M
                    then (if mt_pos cM k = 0 then Suc 0
                          else sim_pos ?k (mt_pos cM k) + ?k)
                    else mt_pos c_b k"
  obtain c_r m_phase where
      r_chain: "(c_b, c_r) \<in> (mttm_step (ar_delta_read M)) ^^ m_phase"
    and r_state: "mt_state c_r = (mt_state cM, AR_SimCompute, k_unidx 0, 0,
                    ?rbuf, dvec, ?rposk)"
    and r_tape: "mt_tape c_r = mt_tape c_b"
    and r_pos: "mt_pos c_r = ?rpos"
    using ar_read_phase_in_sub[OF vM qQ kge2 stg0 tcorr ppos pkok tapeG bufG
                                  pad_b src_b]
    by blast
  have r_cpu: "fst (snd (mt_state c_r)) = AR_SimCompute" using r_state by simp
  have cw_eq_cr: "c_w = c_r"
    using chain_ar_delta_read_to_SimCompute_uniq[OF chain_r r_chain cw_cpu r_cpu]
    by simp
  have cw_state: "mt_state c_w = (mt_state cM, AR_SimCompute, k_unidx 0, 0,
                    ?rbuf, dvec, ?rposk)"
    using cw_eq_cr r_state by simp
  \<comment> \<open>Invert the compute step: the explicit post-state and the fired
     \<open>delta_tm M\<close> branch (on the guarded read buffer).\<close>
  obtain q' m_a' m_d where
      mdelta: "(mt_state cM, ?rbuf, q', m_a', m_d) \<in> delta_tm M"
    and cwpost_state: "mt_state c_w_post = (q', AR_SimWrite, 0, 0, m_a', m_d, ?rposk)"
    and cwpost_tape: "mt_tape c_w_post = mt_tape c_w"
    and cwpost_pos: "mt_pos c_w_post = mt_pos c_w"
    using ar_compute_step_inv_sub[OF cstep cw_state] by blast
  obtain qM tsM nM where cM_eq: "cM = Config\<^sub>M qM tsM nM" by (cases cM) auto
  have qM_eq: "qM = mt_state cM" using cM_eq by simp
  have aM_eq: "(\<lambda>k. tsM k (nM k)) = ?aM" using cM_eq by simp
  have rbuf_eq: "?rbuf = ?aM"
  proof (rule ext)
    fix k show "?rbuf k = ?aM k"
    proof (cases "k < k_tm M")
      case True thus ?thesis by simp
    next
      case False
      have "?rbuf k = bl_tm M" using buf_tail False by simp
      moreover have "?aM k = bl_tm M" using aM_tail False by simp
      ultimately show ?thesis by simp
    qed
  qed
  have mdelta_aM: "(mt_state cM, ?aM, q', m_a', m_d) \<in> delta_tm M"
    using mdelta rbuf_eq by simp
  define cMn where cMn_def: "cMn = Config\<^sub>M q' (\<lambda>k. (tsM k)(nM k := m_a' k))
                                              (\<lambda>k. go_dir (m_d k) (nM k))"
  have mdelta': "(qM, (\<lambda>k. tsM k (nM k)), q', m_a', m_d) \<in> delta_tm M"
    using mdelta_aM qM_eq aM_eq by simp
  have m_step: "(cM, cMn) \<in> mttm_step (delta_tm M)"
    using mttm_step.step[where ts = tsM and n = nM, OF mdelta'] cM_eq cMn_def by simp
  have q'Q: "q' \<in> Q_tm M" using valid_mttm_delta(3)[OF vM mdelta_aM] .
  have a'G: "m_a' k \<in> \<Gamma>_tm M" for k using valid_mttm_delta(4)[OF vM mdelta_aM] .
  have a'val: "\<forall>k. m_a' k \<in> \<Gamma>_tm M \<union> {bl_tm M}" using a'G by blast
  have dsupp: "\<forall>j \<ge> k_tm M. m_a' j = bl_tm M \<and> m_d j = dir.N"
    using valid_mttm_delta_support[OF vM mdelta_aM] by blast
  \<comment> \<open>Write phase: post-write tape / position setup and pad / src for the
     compute-exit config, then pin the walker's write chain.\<close>
  have pad_cwpost: "\<forall>j \<ge> k_tm M. mt_tape c_w_post j (mt_pos c_w_post j) = BLANK4"
  proof (intro allI impI)
    fix j assume jk: "k_tm M \<le> j"
    have "mt_pos c_w_post j = mt_pos c_b j"
      using cwpost_pos cw_eq_cr r_pos jk by simp
    moreover have "mt_tape c_w_post j = mt_tape c_b j"
      using cwpost_tape cw_eq_cr r_tape by simp
    ultimately show "mt_tape c_w_post j (mt_pos c_w_post j) = BLANK4"
      using pad_b jk by simp
  qed
  have src_cwpost: "ar_stage_bounded (bl_tm M) (k_tm M)
                      (AR_SimWrite, 0, 0, m_a', m_d, ?rposk)"
    using kpos_tm dsupp posk_tail by (simp add: ar_stage_bounded_def)
  have tcorr_w: "\<forall>k < k_tm M. ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                     (mt_tape cM k) (mt_tape c_w_post k)"
  proof (intro allI impI)
    fix k assume kN: "k < k_tm M"
    have "mt_tape c_w_post k = mt_tape c_b k"
      using cwpost_tape cw_eq_cr r_tape by simp
    thus "ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
            (mt_tape cM k) (mt_tape c_w_post k)"
      using tcorr kN by simp
  qed
  have ppos_w: "\<forall>k < k_tm M. mt_pos c_w_post k = (if mt_pos cM k = 0 then Suc 0
                   else sim_pos ?k (mt_pos cM k) + ?k)"
    using cwpost_pos cw_eq_cr r_pos by simp
  have a'le0_w: "\<forall>k < k_tm M. mt_pos cM k = 0 \<longrightarrow> m_a' k = le_tm M"
  proof (intro allI impI)
    fix k assume kN: "k < k_tm M" and p0: "mt_pos cM k = 0"
    have tsk0: "tsM k 0 = le_tm M" using valcM cM_eq kN by (cases M) auto
    have "(\<lambda>j. tsM j (nM j)) k = le_tm M" using tsk0 p0 cM_eq by simp
    thus "m_a' k = le_tm M" using valid_mttm_deltaLE[OF vM mdelta'] by simp
  qed
  have poskle_w: "\<forall>k < k_tm M. ?rposk k = AR_AtLE \<longleftrightarrow> mt_pos cM k = 0"
    by auto
  obtain c_write mw where
      w_chain: "(c_w_post, c_write) \<in> (mttm_step (ar_delta_write M)) ^^ mw"
    and w_state: "mt_state c_write = (q', AR_SimAdvance, k_unidx 0, 0, m_a', m_d,
                    ?rposk)"
    and w_tape: "mt_tape c_write = (\<lambda>k. if k < k_tm M
          then (if mt_pos cM k = 0 then mt_tape c_w_post k
                else (\<lambda>pos. if sim_pos ?k (mt_pos cM k) \<le> pos
                              \<and> pos < sim_pos ?k (mt_pos cM k) + ?k
                           then write_bit (\<Gamma>_tm M) (bl_tm M) (m_a' k)
                                  (pos - sim_pos ?k (mt_pos cM k))
                           else mt_tape c_w_post k pos))
          else mt_tape c_w_post k)"
    and w_pos: "mt_pos c_write = mt_pos c_w_post"
    using ar_write_phase_in_sub[OF vM q'Q kge2 cwpost_state tcorr_w ppos_w
                                   poskle_w a'val pad_cwpost src_cwpost]
    by blast
  have c_write_adv: "fst (snd (mt_state c_write)) = AR_SimAdvance"
    using w_state by simp
  have ca_eq: "c_a = c_write"
    using chain_ar_delta_write_to_SimAdvance_uniq[OF wchain w_chain ca_adv
                                                     c_write_adv]
    by simp
  \<comment> \<open>Advance phase: bridge the tk-field, displacement facts (active
     tapes), pad / src for the write-exit config, then pin.\<close>
  have w_state': "mt_state c_write = (q', AR_SimAdvance, 0, 0, m_a', m_d, ?rposk)"
    using w_state by (simp add: k_unidx_zero)
  have pad_cwrite: "\<forall>j \<ge> k_tm M. mt_tape c_write j (mt_pos c_write j) = BLANK4"
  proof (intro allI impI)
    fix j assume jk: "k_tm M \<le> j"
    have "mt_tape c_write j = mt_tape c_w_post j" using w_tape jk by simp
    moreover have "mt_pos c_write j = mt_pos c_w_post j" using w_pos by simp
    ultimately show "mt_tape c_write j (mt_pos c_write j) = BLANK4"
      using pad_cwpost jk by simp
  qed
  have src_cwrite: "ar_stage_bounded (bl_tm M) (k_tm M)
                      (AR_SimAdvance, 0, 0, m_a', m_d, ?rposk)"
    using kpos_tm dsupp posk_tail by (simp add: ar_stage_bounded_def)
  have dge1: "\<forall>k < k_tm M. m_d k \<noteq> dir.R \<longrightarrow> 0 < ar_disp ?k (m_d k) (?rposk k)"
  proof (intro allI impI)
    fix k assume kN: "k < k_tm M" and dkR: "m_d k \<noteq> dir.R"
    show "0 < ar_disp ?k (m_d k) (?rposk k)"
    proof (cases "mt_pos cM k = 0")
      case True
      have nM0: "nM k = 0" using True cM_eq by simp
      have "tsM k 0 = le_tm M" using valcM cM_eq kN by (cases M) auto
      hence "(\<lambda>j. tsM j (nM j)) k = le_tm M" using nM0 by simp
      hence "m_d k \<in> {dir.N, dir.R}" using valid_mttm_deltaLE[OF vM mdelta'] by simp
      hence "m_d k = dir.N" using dkR by auto
      moreover have "?rposk k = AR_AtLE" using True kN by simp
      ultimately show "0 < ar_disp ?k (m_d k) (?rposk k)" by simp
    next
      case False
      have dN_or_L: "m_d k = dir.N \<or> m_d k = dir.L"
        using dkR by (cases "m_d k") auto
      have rk: "?rposk k = AR_AtFirstProper \<or> ?rposk k = AR_AtFurtherProper"
        using False kN by auto
      from dN_or_L rk kge2 show "0 < ar_disp ?k (m_d k) (?rposk k)" by auto
    qed
  qed
  have notLE: "\<forall>k < k_tm M. \<forall>m. m < ar_disp ?k (m_d k) (?rposk k)
                 \<longrightarrow> mt_tape c_write k (mt_pos c_write k - m) \<noteq> LE4"
  proof (intro allI impI)
    fix k m assume kN: "k < k_tm M"
      and mlt: "m < ar_disp ?k (m_d k) (?rposk k)"
    have tcorr_wk: "ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                      (mt_tape cM k) (mt_tape c_w_post k)"
      using tcorr_w kN by blast
    have wcpos: "mt_pos c_write k = (if mt_pos cM k = 0 then Suc 0
                    else sim_pos ?k (mt_pos cM k) + ?k)"
      using w_pos ppos_w kN by simp
    have wtape_notLE: "mt_tape c_write k pos \<noteq> LE4" if pos1: "1 \<le> pos" for pos
    proof (cases "mt_pos cM k = 0")
      case True
      have "mt_tape c_write k pos = mt_tape c_w_post k pos"
        using w_tape True kN by simp
      thus ?thesis
        using ar_tape_correspondence_not_LE4[OF tcorr_wk pos1] by simp
    next
      case False
      have wexp: "mt_tape c_write k pos
            = (if sim_pos ?k (mt_pos cM k) \<le> pos
                  \<and> pos < sim_pos ?k (mt_pos cM k) + ?k
               then write_bit (\<Gamma>_tm M) (bl_tm M) (m_a' k)
                      (pos - sim_pos ?k (mt_pos cM k))
               else mt_tape c_w_post k pos)"
        using w_tape False kN by simp
      show ?thesis
      proof (cases "sim_pos ?k (mt_pos cM k) \<le> pos
                      \<and> pos < sim_pos ?k (mt_pos cM k) + ?k")
        case True
        have b: "pos - sim_pos ?k (mt_pos cM k) < ?k" using True by linarith
        have "mt_tape c_write k pos
                = write_bit (\<Gamma>_tm M) (bl_tm M) (m_a' k)
                    (pos - sim_pos ?k (mt_pos cM k))"
          using wexp True by simp
        thus ?thesis using write_bit_not_LE4[OF b] by simp
      next
        case False
        have nreg: "\<not> (sim_pos ?k (mt_pos cM k) \<le> pos
                        \<and> pos < sim_pos ?k (mt_pos cM k) + ?k)"
          using False by simp
        have "mt_tape c_write k pos = mt_tape c_w_post k pos"
          using wexp by (simp add: if_not_P[OF nreg])
        thus ?thesis
          using ar_tape_correspondence_not_LE4[OF tcorr_wk pos1] by simp
      qed
    qed
    have rge: "ar_disp ?k (m_d k) (?rposk k) \<le> mt_pos c_write k"
    proof (cases "mt_pos cM k = 0")
      case True
      have "ar_disp ?k (m_d k) (?rposk k) \<le> Suc 0"
        using True kN by (cases "m_d k") auto
      thus ?thesis using wcpos True by simp
    next
      case nz: False
      show ?thesis
      proof (cases "mt_pos cM k = 1")
        case True
        have "ar_disp ?k (m_d k) (?rposk k) \<le> Suc ?k"
          using True kN by (cases "m_d k") auto
        thus ?thesis using wcpos True by (simp add: sim_pos_def)
      next
        case False
        have p2: "2 \<le> mt_pos cM k" using nz False by simp
        have d2: "ar_disp ?k (m_d k) (?rposk k) \<le> 2 * ?k"
          using nz False kN by (cases "m_d k") auto
        have cw_eq2: "mt_pos c_write k = (mt_pos cM k - 1) * ?k + 1 + ?k"
          using wcpos nz by (simp add: sim_pos_def)
        have "(1::nat) \<le> mt_pos cM k - 1" using p2 by simp
        hence "1 * ?k \<le> (mt_pos cM k - 1) * ?k" by (rule mult_le_mono1)
        hence kk: "?k \<le> (mt_pos cM k - 1) * ?k" by (simp only: mult_1_left)
        have "2 * ?k \<le> mt_pos c_write k" using kk cw_eq2 by linarith
        thus ?thesis using d2 by linarith
      qed
    qed
    have "m < mt_pos c_write k" using mlt rge by simp
    hence "1 \<le> mt_pos c_write k - m" by simp
    thus "mt_tape c_write k (mt_pos c_write k - m) \<noteq> LE4" by (rule wtape_notLE)
  qed
  let ?aposk = "\<lambda>k. if k < k_tm M then ar_newpos (m_d k) (?rposk k) else ?rposk k"
  let ?apos = "\<lambda>k. if k < k_tm M
                    then (if m_d k = dir.R then mt_pos c_write k
                          else mt_pos c_write k - ar_disp ?k (m_d k) (?rposk k))
                    else mt_pos c_write k"
  obtain c_adv ma where
      a_chain: "(c_write, c_adv) \<in> (mttm_step (ar_delta_advance M)) ^^ ma"
    and a_state: "mt_state c_adv = (q', AR_SimNext, k_unidx 0, 0, m_a', m_d, ?aposk)"
    and a_tape: "mt_tape c_adv = mt_tape c_write"
    and a_pos: "mt_pos c_adv = ?apos"
    using ar_advance_phase_in_sub[OF vM q'Q kge2 w_state' a'val dge1 notLE
                                     pad_cwrite src_cwrite]
    by blast
  have c_adv_nxt: "fst (snd (mt_state c_adv)) = AR_SimNext" using a_state by simp
  have achain': "(c_write, c') \<in> (mttm_step (ar_delta_advance M)) ^^ m_a"
    using achain ca_eq by simp
  have c'_eq: "c' = c_adv"
    using chain_ar_delta_advance_to_SimNext_uniq[OF achain' a_chain c'_next
                                                    c_adv_nxt]
    by simp
  have c'_state: "mt_state c' = (q', AR_SimNext, k_unidx 0, 0, m_a', m_d, ?aposk)"
    using c'_eq a_state by simp
  \<comment> \<open>Closing next step: invert it; dispatch on the reconstructed
     \<open>M\<close>-state \<open>q'\<close>.\<close>
  have nxt: "mt_tape c'' = mt_tape c' \<and> mt_pos c'' = mt_pos c'
       \<and> ((q' \<notin> {t_tm M, r_tm M}
             \<and> mt_state c'' = (q', AR_SimRead, 0, 0, m_a', m_d, ?aposk))
          \<or> (q' = t_tm M
             \<and> mt_state c'' = (t_tm M, ar_accept_stage (bl_tm M)))
          \<or> (q' = r_tm M
             \<and> mt_state c'' = (r_tm M, ar_reject_stage (bl_tm M))))"
    using ar_next_step_inv[OF step c'_state] .
  have nxt_tape: "mt_tape c'' = mt_tape c'" using nxt by simp
  have nxt_pos: "mt_pos c'' = mt_pos c'" using nxt by simp
  have nxt_disj:
      "(q' \<notin> {t_tm M, r_tm M}
          \<and> mt_state c'' = (q', AR_SimRead, 0, 0, m_a', m_d, ?aposk))
       \<or> (q' = t_tm M
          \<and> mt_state c'' = (t_tm M, ar_accept_stage (bl_tm M)))
       \<or> (q' = r_tm M
          \<and> mt_state c'' = (r_tm M, ar_reject_stage (bl_tm M)))"
    using nxt by simp
  \<comment> \<open>Re-establish the boundary predicates for \<open>cMn\<close> at \<open>c''\<close>.\<close>
  have st_cMn: "mt_state cMn = q'" using cMn_def by simp
  have padpos0: "\<forall>j \<ge> k_tm M. mt_pos cM j = 0" using pkok posk_tail by blast
  have dposL: "m_d k \<noteq> dir.L" if p0: "mt_pos cM k = 0" and kN: "k < k_tm M" for k
  proof -
    have nM0: "nM k = 0" using p0 cM_eq by simp
    have "tsM k 0 = le_tm M" using valcM cM_eq kN by (cases M) auto
    hence "(\<lambda>j. tsM j (nM j)) k = le_tm M" using nM0 by simp
    hence "m_d k \<in> {dir.N, dir.R}" using valid_mttm_deltaLE[OF vM mdelta'] by simp
    thus "m_d k \<noteq> dir.L" by auto
  qed
  have cwpost_b: "mt_tape c_w_post = mt_tape c_b"
    using cwpost_tape cw_eq_cr r_tape by simp
  have cM1tape: "mt_tape cMn k = (mt_tape cM k)(mt_pos cM k := m_a' k)" for k
    using cMn_def cM_eq by simp
  have wt_def: "mt_tape c'' k pos
        = (if mt_pos cM k = 0 then mt_tape c_b k pos
           else if sim_pos ?k (mt_pos cM k) \<le> pos
                   \<and> pos < sim_pos ?k (mt_pos cM k) + ?k
                then write_bit (\<Gamma>_tm M) (bl_tm M) (m_a' k)
                       (pos - sim_pos ?k (mt_pos cM k))
                else mt_tape c_b k pos)" for k pos
  proof (cases "k < k_tm M")
    case True
    thus ?thesis using nxt_tape c'_eq a_tape w_tape cwpost_b by simp
  next
    case False
    hence kge: "k_tm M \<le> k" by simp
    have p0: "mt_pos cM k = 0" using padpos0 kge by blast
    have "mt_tape c'' k = mt_tape c_b k"
      using nxt_tape c'_eq a_tape w_tape cwpost_b kge by simp
    thus ?thesis using p0 by simp
  qed
  have tcorr_1: "\<forall>k < k_tm M. ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                   (mt_tape cMn k) (mt_tape c'' k)"
  proof (intro allI impI)
    fix k assume kN: "k < k_tm M"
    show "ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
            (mt_tape cMn k) (mt_tape c'' k)"
      by (rule ar_write_tape_correspondence
                [OF kge2 kN tcorr cM1tape a'le0_w wt_def])
  qed
  have apos_1: "mt_pos c'' k = sim_pos ?k (mt_pos cMn k)" for k
  proof (cases "k < k_tm M")
    case kN: True
    have posM1: "mt_pos cMn k = go_dir (m_d k) (mt_pos cM k)"
      using cMn_def cM_eq by simp
    have key: "(if m_d k = dir.R
                 then (if mt_pos cM k = 0 then Suc 0
                       else sim_pos ?k (mt_pos cM k) + ?k)
                 else (if mt_pos cM k = 0 then Suc 0
                       else sim_pos ?k (mt_pos cM k) + ?k)
                        - ar_disp ?k (m_d k)
                            (if mt_pos cM k = 0 then AR_AtLE
                             else if mt_pos cM k = 1 then AR_AtFirstProper
                             else AR_AtFurtherProper))
               = sim_pos ?k (go_dir (m_d k) (mt_pos cM k))"
    proof (rule ar_advance_newsimpos)
      show "2 \<le> ?k" by (rule kge2)
      show "mt_pos cM k = 0 \<Longrightarrow> m_d k \<noteq> dir.L" using dposL kN by blast
    qed
    have cadv_pos: "mt_pos c'' k = (if m_d k = dir.R
                 then (if mt_pos cM k = 0 then Suc 0
                       else sim_pos ?k (mt_pos cM k) + ?k)
                 else (if mt_pos cM k = 0 then Suc 0
                       else sim_pos ?k (mt_pos cM k) + ?k)
                        - ar_disp ?k (m_d k)
                            (if mt_pos cM k = 0 then AR_AtLE
                             else if mt_pos cM k = 1 then AR_AtFirstProper
                             else AR_AtFurtherProper))"
      using nxt_pos c'_eq a_pos w_pos ppos_w kN by simp
    show ?thesis by (simp add: cadv_pos key posM1)
  next
    case False
    hence kge: "k_tm M \<le> k" by simp
    have dN: "m_d k = dir.N" using dsupp kge by blast
    have posM1: "mt_pos cMn k = go_dir (m_d k) (mt_pos cM k)"
      using cMn_def cM_eq by simp
    have "mt_pos c'' k = mt_pos c_b k"
      using nxt_pos c'_eq a_pos w_pos cwpost_pos cw_eq_cr r_pos kge by simp
    also have "\<dots> = sim_pos ?k (mt_pos cM k)" using ppos by simp
    also have "\<dots> = sim_pos ?k (mt_pos cMn k)" using posM1 dN by simp
    finally show ?thesis .
  qed
  have aposk_1: "?aposk k = AR_AtLE \<longleftrightarrow> mt_pos cMn k = 0" for k
  proof (cases "k < k_tm M")
    case kN: True
    have posM1: "mt_pos cMn k = go_dir (m_d k) (mt_pos cM k)"
      using cMn_def cM_eq by simp
    have key: "(ar_newpos (m_d k)
                  (if mt_pos cM k = 0 then AR_AtLE
                   else if mt_pos cM k = 1 then AR_AtFirstProper
                   else AR_AtFurtherProper) = AR_AtLE)
                 \<longleftrightarrow> go_dir (m_d k) (mt_pos cM k) = 0"
    proof (rule ar_newpos_atLE_iff)
      show "mt_pos cM k = 0 \<Longrightarrow> m_d k \<noteq> dir.L" using dposL kN by blast
    qed
    have aposk_k: "?aposk k = ar_newpos (m_d k)
                     (if mt_pos cM k = 0 then AR_AtLE
                      else if mt_pos cM k = 1 then AR_AtFirstProper
                      else AR_AtFurtherProper)"
      using kN by simp
    show ?thesis by (simp add: aposk_k key posM1)
  next
    case False
    hence kge: "k_tm M \<le> k" by simp
    have dN: "m_d k = dir.N" using dsupp kge by blast
    have p0: "mt_pos cM k = 0" using padpos0 kge by blast
    have posM1: "mt_pos cMn k = go_dir (m_d k) (mt_pos cM k)"
      using cMn_def cM_eq by simp
    have "mt_pos cMn k = 0" using posM1 dN p0 by simp
    moreover have "posk k = AR_AtLE" using posk_tail kge by blast
    moreover have "?aposk k = posk k" using kge by simp
    ultimately show ?thesis by simp
  qed
  have pad_c'': "\<forall>j \<ge> k_tm M. mt_tape c'' j (mt_pos c'' j) = BLANK4"
  proof (intro allI impI)
    fix j assume jk: "k_tm M \<le> j"
    have "mt_pos c'' j = mt_pos c_write j"
      using nxt_pos c'_eq a_pos jk by simp
    moreover have "mt_tape c'' j = mt_tape c_write j"
      using nxt_tape c'_eq a_tape by simp
    ultimately show "mt_tape c'' j (mt_pos c'' j) = BLANK4"
      using pad_cwrite jk by simp
  qed
  have src_read'': "ar_stage_bounded (bl_tm M) (k_tm M)
                      (AR_SimRead, 0, 0, m_a', m_d, ?aposk)"
    using kpos_tm dsupp posk_tail by (simp add: ar_stage_bounded_def)
  show ?thesis
  proof (intro exI[where x = cMn] conjI)
    show "(cM, cMn) \<in> mttm_step (delta_tm M)" by (rule m_step)
    show "ar_walker_at_boundary M cMn c''"
    proof -
      consider
          (cont) "q' \<notin> {t_tm M, r_tm M}"
                 "mt_state c'' = (q', AR_SimRead, 0, 0, m_a', m_d, ?aposk)"
        | (acc)  "q' = t_tm M"
                 "mt_state c'' = (t_tm M, ar_accept_stage (bl_tm M))"
        | (rej)  "q' = r_tm M"
                 "mt_state c'' = (r_tm M, ar_reject_stage (bl_tm M))"
        using nxt_disj by blast
      thus ?thesis
      proof cases
        case cont
        have notT: "q' \<noteq> t_tm M" using cont(1) by simp
        have notR: "q' \<noteq> r_tm M" using cont(1) by simp
        show ?thesis
          unfolding ar_walker_at_boundary_def
        proof (intro conjI)
          show "ar_simulates M cMn c''"
            by (simp add: ar_simulates_def Let_def cont(2) st_cMn notT notR
                          tcorr_1 apos_1)
          show "ar_posk_consistent M cMn c''"
            by (simp add: ar_posk_consistent_def cont(2) aposk_1)
          show "ar_at_read_boundary M c''"
            by (simp add: ar_at_read_boundary_def cont(2) a'G pad_c'' src_read'')
        qed
      next
        case acc
        show ?thesis
          unfolding ar_walker_at_boundary_def
        proof (intro conjI)
          show "ar_simulates M cMn c''"
            by (simp add: ar_simulates_def Let_def acc(2) st_cMn acc(1)
                          tcorr_1 ar_accept_stage_def)
          show "ar_posk_consistent M cMn c''"
            by (simp add: ar_posk_consistent_def acc(2) ar_accept_stage_def)
          show "ar_at_read_boundary M c''"
            by (simp add: ar_at_read_boundary_def acc(2) ar_accept_stage_def
                          pad_c'')
        qed
      next
        case rej
        show ?thesis
          unfolding ar_walker_at_boundary_def
        proof (intro conjI)
          show "ar_simulates M cMn c''"
            by (simp add: ar_simulates_def Let_def rej(2) st_cMn rej(1)
                          tcorr_1 ar_reject_stage_def)
          show "ar_posk_consistent M cMn c''"
            by (simp add: ar_posk_consistent_def rej(2) ar_reject_stage_def)
          show "ar_at_read_boundary M c''"
            by (simp add: ar_at_read_boundary_def rej(2) ar_reject_stage_def
                          pad_c'')
        qed
      qed
    qed
  qed
qed

subsection \<open>Chunked reverse engine\<close>

text \<open>The reverse-arm loop invariant: the substep-walker is in
  \<^emph>\<open>some\<close> stage of the cycle.  Six disjuncts, one per walker
  predicate.  This is the AR analogue of
  carrying \<open>ae_simulates\<close> across AE's reverse induction, but
  stage-granular: where AE peels a whole fixed-length cycle per
  \<open>ae_backward_stage\<close>, AR peels one \<open>M'\<close>-substep and dispatches on
  the current substep tag (the cycle length is data-dependent here, which
  is why the pivot to the substep walker was needed in the first place).\<close>

definition ar_walker ::
  "('q, 'a) mttm
    \<Rightarrow> ('a, 'q) mt_config
    \<Rightarrow> (sym4, 'q \<times> 'a ar_stage) mt_config \<Rightarrow> bool" where
  "ar_walker M cM c' \<longleftrightarrow>
     ar_walker_at_boundary M cM c'
   \<or> ar_walker_in_read M cM c'
   \<or> ar_walker_at_compute M cM c'
   \<or> ar_walker_in_write M cM c'
   \<or> ar_walker_in_advance M cM c'
   \<or> ar_walker_at_next M cM c'"

text \<open>Chunked-induction engine for the reverse arm, the AR analogue of
  AE's \<open>ae_simulation_phase_chunked_reverse\<close>.  Given a finite
  \<open>M'\<close>-trace \<open>(c', c_acc)\<close> of length \<open>m\<close> ending in the canonical
  accept config \<open>(t_tm M, ar_accept_stage (bl_tm M))\<close> and the walker
  invariant at \<open>c'\<close> relative to a reachable \<open>cM\<close>, deliver an
  accepting \<open>M\<close>-path from \<open>cM\<close>.  Strong induction on \<open>m\<close>; at
  each level dispatch on the walker stage and peel one \<open>M'\<close>-step:

  \<^item> the five active stages (\<open>in_read\<close>, \<open>at_compute\<close>,
    \<open>in_write\<close>, \<open>in_advance\<close>, \<open>at_next\<close>, and an active read
    boundary) all have \<open>c' \<noteq> c_acc\<close>, so \<open>m = Suc m'\<close>; peel
    the step via the matching preservation lemma (\<open>at_compute\<close> emits
    one \<open>M\<close>-step into the \<open>in_write\<close> witness; \<open>at_next\<close> emits
    one via \<open>ar_walker_cycle_close\<close> and advances \<open>cM\<close>), then
    recurse on \<open>m'\<close>;
  \<^item> a boundary at the accept config closes the induction:
    \<open>ar_simulates_accept_iff\<close> forces \<open>mt_state cM = t_tm M\<close>;
  \<^item> a boundary at the reject config is impossible — the trace runs to
    the accept config, but reject is terminal (\<open>ar_reject_terminal\<close>)
    and the reject config is not the accept config.

  The conclusion is in \<open>rtrancl\<close> form for the downstream
  \<open>Lang_mttm\<close>-repacking in \<open>alphabet_reduce_language\<close>.\<close>

lemma ar_simulation_phase_chunked_reverse:
  fixes M :: "('q, 'a) mttm"
    and w :: "'a list"
    and cM :: "('a, 'q) mt_config"
    and c' c_acc :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and m :: nat
  assumes vM:      "valid_mttm M"
      and w_sub:   "set w \<subseteq> Sigma_tm M"
      and card_ge: "card (\<Gamma>_tm M) \<ge> 4"
      and lebl:    "le_tm M \<noteq> bl_tm M"
      and reach_M: "(init_config_mttm M w, cM) \<in> (mttm_step (delta_tm M))\<^sup>*"
      and trace:   "(c', c_acc) \<in> (mttm_step (alphabet_reduce_delta M)) ^^ m"
      and accept:  "mt_state c_acc = (t_tm M, ar_accept_stage (bl_tm M))"
      and walk:    "ar_walker M cM c'"
  shows "\<exists>cM_final. (cM, cM_final) \<in> (mttm_step (delta_tm M))\<^sup>*
                    \<and> mt_state cM_final = t_tm M"
  using reach_M trace walk
proof (induction m arbitrary: cM c' rule: less_induct)
  case (less m)
  let ?R = "mttm_step (alphabet_reduce_delta M)"
  \<comment> \<open>Encoding width \<open>\<ge> 2\<close> from \<open>card \<Gamma>_M \<ge> 4\<close>, and the
     reachable-config invariants \<open>cM\<close> needs for the substep lemmas.\<close>
  have kge2: "2 \<le> block_width (\<Gamma>_tm M)"
  proof -
    have "(2::nat) ^ 2 \<le> 2 ^ block_width (\<Gamma>_tm M)"
      using card_ge card_le_two_pow_block_width[of "\<Gamma>_tm M"] by simp
    thus "2 \<le> block_width (\<Gamma>_tm M)"
      using power_le_imp_le_exp[of "2::nat" 2 "block_width (\<Gamma>_tm M)"] by simp
  qed
  have valcM: "valid_config_mttm M cM"
    by (rule valid_reach_mttm[OF vM w_sub less.prems(1)])
  have qQ: "mt_state cM \<in> Q_tm M" using valcM by (cases M; cases cM) auto
  have tapeG: "mt_tape cM k (mt_pos cM k) \<in> \<Gamma>_tm M" for k
  proof -
    have "range (mt_tape cM k) \<subseteq> \<Gamma>_tm M"
      using valcM by (cases M; cases cM) auto
    thus ?thesis by blast
  qed
  have acc_idx: "fst (snd (mt_state c_acc)) = AR_HaltAccept"
    using accept by (simp add: ar_accept_stage_def)
  \<comment> \<open>An active config (substep tag \<open>\<noteq> AR_HaltAccept\<close>) cannot be
     \<open>c_acc\<close>, so the trace has a first step to peel.\<close>
  have peel: "\<exists>m' c'_1. m = Suc m'
                \<and> (c', c'_1) \<in> ?R \<and> (c'_1, c_acc) \<in> ?R ^^ m'"
    if notHA: "fst (snd (mt_state c')) \<noteq> AR_HaltAccept"
  proof -
    have "m \<noteq> 0"
    proof
      assume "m = 0"
      hence "c' = c_acc" using less.prems(2) by simp
      thus False using notHA acc_idx by simp
    qed
    then obtain m' where mSuc: "m = Suc m'" using not0_implies_Suc by blast
    have "(c', c_acc) \<in> ?R ^^ Suc m'" using less.prems(2) mSuc by simp
    from relpow_Suc_D2[OF this] obtain c'_1 where
        "(c', c'_1) \<in> ?R" and "(c'_1, c_acc) \<in> ?R ^^ m'" by blast
    thus ?thesis using mSuc by blast
  qed
  from less.prems(3)
  consider (bnd) "ar_walker_at_boundary M cM c'"
         | (rd)  "ar_walker_in_read M cM c'"
         | (cmp) "ar_walker_at_compute M cM c'"
         | (wr)  "ar_walker_in_write M cM c'"
         | (adv) "ar_walker_in_advance M cM c'"
         | (nx)  "ar_walker_at_next M cM c'"
    unfolding ar_walker_def by blast
  then show ?case
  proof cases
    case bnd
    have sim: "ar_simulates M cM c'"
      using bnd unfolding ar_walker_at_boundary_def by simp
    obtain qM0 stg where st: "mt_state c' = (qM0, stg)"
      by (cases "mt_state c'") auto
    obtain idx tk i buf dvec posk where
        sg: "stg = (idx, tk, i, buf, dvec, posk)" by (cases stg) auto
    have state_disj:
        "(idx = AR_SimRead \<and> qM0 \<notin> {t_tm M, r_tm M})
           \<or> (qM0 = t_tm M \<and> stg = ar_accept_stage (bl_tm M))
           \<or> (qM0 = r_tm M \<and> stg = ar_reject_stage (bl_tm M))"
      using sim st sg unfolding ar_simulates_def by (auto split: prod.splits)
    consider (active) "idx = AR_SimRead"
           | (acc)    "stg = ar_accept_stage (bl_tm M)" "qM0 = t_tm M"
           | (rej)    "stg = ar_reject_stage (bl_tm M)" "qM0 = r_tm M"
      using state_disj by blast
    thus ?thesis
    proof cases
      case active
      have neq: "fst (snd (mt_state c')) \<noteq> AR_HaltAccept"
        using st sg active by simp
      obtain m' c'_1 where mSuc: "m = Suc m'"
        and fst_step: "(c', c'_1) \<in> ?R"
        and rest: "(c'_1, c_acc) \<in> ?R ^^ m'"
        using peel[OF neq] by blast
      have m'_lt: "m' < m" using mSuc by simp
      have "ar_walker_in_read M cM c'_1 \<or> ar_walker_at_compute M cM c'_1"
        using ar_walker_step_from_boundary[OF bnd fst_step] .
      hence walk_1: "ar_walker M cM c'_1" unfolding ar_walker_def by blast
      show ?thesis using less.IH[OF m'_lt less.prems(1) rest walk_1] .
    next
      case acc
      have c'_acc: "mt_state c' = (t_tm M, ar_accept_stage (bl_tm M))"
        using st sg acc by simp
      have cM_t: "mt_state cM = t_tm M"
        using ar_simulates_accept_iff[OF vM sim] c'_acc by simp
      have "(cM, cM) \<in> (mttm_step (delta_tm M))\<^sup>*" by simp
      thus ?thesis using cM_t by blast
    next
      case rej
      have c'_rej: "mt_state c' = (r_tm M, ar_reject_stage (bl_tm M))"
        using st sg rej by simp
      show ?thesis
      proof (cases m)
        case 0
        have ceq: "c' = c_acc" using less.prems(2) 0 by simp
        have "fst (snd (mt_state c')) = AR_HaltReject"
          using c'_rej by (simp add: ar_reject_stage_def)
        moreover have "fst (snd (mt_state c')) = AR_HaltAccept"
          using ceq accept by (simp add: ar_accept_stage_def)
        ultimately show ?thesis by simp
      next
        case (Suc m')
        have "(c', c_acc) \<in> ?R ^^ Suc m'" using less.prems(2) Suc by simp
        from relpow_Suc_D2[OF this] obtain c'_1 where
            fst_step: "(c', c'_1) \<in> ?R" by blast
        have "mt_state c' \<noteq> (r_tm M, ar_reject_stage (bl_tm M))"
          by (rule ar_reject_terminal[OF vM card_ge fst_step])
        thus ?thesis using c'_rej by simp
      qed
    qed
  next
    case rd
    have neq: "fst (snd (mt_state c')) \<noteq> AR_HaltAccept"
      using rd unfolding ar_walker_in_read_def by simp
    obtain m' c'_1 where mSuc: "m = Suc m'"
      and fst_step: "(c', c'_1) \<in> ?R"
      and rest: "(c'_1, c_acc) \<in> ?R ^^ m'"
      using peel[OF neq] by blast
    have m'_lt: "m' < m" using mSuc by simp
    have "ar_walker_in_read M cM c'_1 \<or> ar_walker_at_compute M cM c'_1"
      using ar_walker_step_from_in_read[OF rd fst_step] .
    hence walk_1: "ar_walker M cM c'_1" unfolding ar_walker_def by blast
    show ?thesis using less.IH[OF m'_lt less.prems(1) rest walk_1] .
  next
    case cmp
    have neq: "fst (snd (mt_state c')) \<noteq> AR_HaltAccept"
      using cmp unfolding ar_walker_at_compute_def by simp
    obtain m' c'_1 where mSuc: "m = Suc m'"
      and fst_step: "(c', c'_1) \<in> ?R"
      and rest: "(c'_1, c_acc) \<in> ?R ^^ m'"
      using peel[OF neq] by blast
    have m'_lt: "m' < m" using mSuc by simp
    have w_1: "ar_walker_in_write M cM c'_1"
      using ar_walker_step_from_at_compute[OF cmp fst_step vM qQ kge2 tapeG] .
    have walk_1: "ar_walker M cM c'_1" using w_1 unfolding ar_walker_def by blast
    show ?thesis using less.IH[OF m'_lt less.prems(1) rest walk_1] .
  next
    case wr
    have neq: "fst (snd (mt_state c')) \<noteq> AR_HaltAccept"
      using wr unfolding ar_walker_in_write_def by simp
    obtain m' c'_1 where mSuc: "m = Suc m'"
      and fst_step: "(c', c'_1) \<in> ?R"
      and rest: "(c'_1, c_acc) \<in> ?R ^^ m'"
      using peel[OF neq] by blast
    have m'_lt: "m' < m" using mSuc by simp
    have "ar_walker_in_write M cM c'_1 \<or> ar_walker_in_advance M cM c'_1"
      using ar_walker_step_from_in_write[OF wr fst_step] .
    hence walk_1: "ar_walker M cM c'_1" unfolding ar_walker_def by blast
    show ?thesis using less.IH[OF m'_lt less.prems(1) rest walk_1] .
  next
    case adv
    have neq: "fst (snd (mt_state c')) \<noteq> AR_HaltAccept"
      using adv unfolding ar_walker_in_advance_def by simp
    obtain m' c'_1 where mSuc: "m = Suc m'"
      and fst_step: "(c', c'_1) \<in> ?R"
      and rest: "(c'_1, c_acc) \<in> ?R ^^ m'"
      using peel[OF neq] by blast
    have m'_lt: "m' < m" using mSuc by simp
    have "ar_walker_in_advance M cM c'_1 \<or> ar_walker_at_next M cM c'_1"
      using ar_walker_step_from_in_advance[OF adv fst_step] .
    hence walk_1: "ar_walker M cM c'_1" unfolding ar_walker_def by blast
    show ?thesis using less.IH[OF m'_lt less.prems(1) rest walk_1] .
  next
    case nx
    have neq: "fst (snd (mt_state c')) \<noteq> AR_HaltAccept"
      using nx unfolding ar_walker_at_next_def by simp
    obtain m' c'_1 where mSuc: "m = Suc m'"
      and fst_step: "(c', c'_1) \<in> ?R"
      and rest: "(c'_1, c_acc) \<in> ?R ^^ m'"
      using peel[OF neq] by blast
    have m'_lt: "m' < m" using mSuc by simp
    obtain cMn where step_cMn: "(cM, cMn) \<in> mttm_step (delta_tm M)"
      and bnd_1: "ar_walker_at_boundary M cMn c'_1"
      using ar_walker_cycle_close[OF nx fst_step vM qQ kge2 tapeG
                                     w_sub less.prems(1) lebl]
      by blast
    have reach_Mn: "(init_config_mttm M w, cMn) \<in> (mttm_step (delta_tm M))\<^sup>*"
      using less.prems(1) step_cMn by (rule rtrancl.rtrancl_into_rtrancl)
    have walk_1: "ar_walker M cMn c'_1"
      using bnd_1 unfolding ar_walker_def by blast
    obtain cM_final where
        run_final: "(cMn, cM_final) \<in> (mttm_step (delta_tm M))\<^sup>*"
      and acc_final: "mt_state cM_final = t_tm M"
      using less.IH[OF m'_lt reach_Mn rest walk_1] by blast
    have "(cM, cM_final) \<in> (mttm_step (delta_tm M))\<^sup>*"
      using step_cMn run_final by (meson r_into_rtrancl rtrancl_trans)
    thus ?thesis using acc_final by blast
  qed
qed

text \<open>Classical language-equivalence (biconditional) for alphabet
  reduction: an \<open>'a\<close>-word \<open>w\<close> over the input alphabet is in
  \<open>M\<close>'s language iff its \<open>sym4\<close>-encoding is in the language
  of the reduced machine \<open>M'\<close>.  Pairs the forward inclusion
  \<open>alphabet_reduce_language_forward\<close> (in
  \<open>AlphabetReduction_Theorems.thy\<close>) with the reverse leg supplied by
  \<open>ar_simulation_phase_chunked_reverse\<close>.

  Unlike AE, the alphabet-reduction construction has no input
  validation prefix (the no-validation design point), so the reverse
  direction needs neither a validation-peel nor a determinism /
  chain-uniqueness argument: the encoded input's accepting \<open>M'\<close>-run
  is handed to the engine directly off the initial read-boundary
  correspondence (\<open>ar_walker_at_boundary\<close>, the conjunction of the
  three \<open>_init\<close> invariants).  No \<open>det_mttm\<close> hypothesis is
  required.

  The \<open>set w \<subseteq> Sigma_tm M\<close> guard is required (and matches
  AE's statement): \<open>Lang_mttm\<close> bakes in the input-alphabet
  restriction, so \<open>w \<in> Lang_mttm M\<close> supplies the guard for
  free in the forward direction, but membership of the encoded word
  in \<open>Lang_mttm M'\<close> says nothing about \<open>w\<close>'s alphabet.  For
  \<open>w\<close> outside the input alphabet the encoded word can still be
  accepted by \<open>M'\<close> while \<open>w \<notin> Lang_mttm M\<close>.\<close>

theorem alphabet_reduce_language:
  fixes M :: "('q, 'a) mttm"
  assumes vM:        "valid_mttm M"
      and s_neq_t:   "s_tm M \<noteq> t_tm M"
      and s_neq_r:   "s_tm M \<noteq> r_tm M"
      and le_neq_bl: "le_tm M \<noteq> bl_tm M"
      and card_ge:   "card (\<Gamma>_tm M) \<ge> 4"
  shows "\<forall>w. set w \<subseteq> Sigma_tm M
              \<longrightarrow> (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w \<in> Lang_mttm
                      (alphabet_reduce M
                         :: ('q \<times> 'a ar_stage, sym4) mttm))
                  = (w \<in> Lang_mttm M)"
proof -
  let ?M' = "alphabet_reduce M :: ('q \<times> 'a ar_stage, sym4) mttm"
  have fwd: "\<forall>w. set w \<subseteq> Sigma_tm M
                  \<longrightarrow> w \<in> Lang_mttm M
                  \<longrightarrow> encode_input_ar (\<Gamma>_tm M) (bl_tm M) w \<in> Lang_mttm ?M'"
    by (rule alphabet_reduce_language_forward[OF vM s_neq_t s_neq_r le_neq_bl card_ge])
  show ?thesis
  proof (intro allI impI)
    fix w :: "'a list"
    assume w_sub: "set w \<subseteq> Sigma_tm M"
    let ?enc = "encode_input_ar (\<Gamma>_tm M) (bl_tm M) w"
    let ?c'  = "init_config_mttm ?M' ?enc"
    show "(?enc \<in> Lang_mttm ?M') = (w \<in> Lang_mttm M)"
    proof
      assume w_in_M: "w \<in> Lang_mttm M"
      from fwd w_sub w_in_M show "?enc \<in> Lang_mttm ?M'" by blast
    next
      \<comment> \<open>Reverse direction: an accepting \<open>M'\<close>-run on the encoded
          input yields an accepting \<open>M\<close>-run on \<open>w\<close>.  No
          validation prefix to peel, so the accepting trace feeds the
          chunked-reverse engine directly off the initial read-boundary
          correspondence.\<close>
      assume enc_in_M': "?enc \<in> Lang_mttm ?M'"
      \<comment> \<open>Step 1: unpack the \<open>M'\<close>-acceptance into a relpow trace.\<close>
      from enc_in_M' obtain wM' nM' where
          acc_path_M':
            "(?c', Config\<^sub>M (t_tm ?M') wM' nM')
                \<in> (mttm_step (delta_tm ?M'))\<^sup>*"
        unfolding Lang_mttm_def by blast
      have acc_path:
          "(?c', Config\<^sub>M (t_tm ?M') wM' nM')
              \<in> (mttm_step (alphabet_reduce_delta M))\<^sup>*"
        using acc_path_M' by simp
      obtain m where trace:
          "(?c', Config\<^sub>M (t_tm ?M') wM' nM')
              \<in> (mttm_step (alphabet_reduce_delta M)) ^^ m"
        using acc_path rtrancl_imp_relpow by metis
      \<comment> \<open>Step 2: the accept state in the engine's canonical form.\<close>
      have accept:
          "mt_state (Config\<^sub>M (t_tm ?M') wM' nM')
              = (t_tm M, ar_accept_stage (bl_tm M))"
        by simp
      \<comment> \<open>Step 3: the initial read-boundary correspondence is the
          walker's boundary disjunct.\<close>
      have sim:  "ar_simulates M (init_config_mttm M w) ?c'"
        by (rule ar_simulates_init[OF vM w_sub s_neq_t s_neq_r])
      have posk: "ar_posk_consistent M (init_config_mttm M w) ?c'"
        by (rule ar_posk_consistent_init)
      have rbnd: "ar_at_read_boundary M ?c'"
        by (rule ar_at_read_boundary_init[OF vM])
      have walk: "ar_walker M (init_config_mttm M w) ?c'"
        unfolding ar_walker_def ar_walker_at_boundary_def
        using sim posk rbnd by blast
      \<comment> \<open>Step 4: seed with the reflexive reach and run the engine.\<close>
      have reach_refl: "(init_config_mttm M w, init_config_mttm M w)
                          \<in> (mttm_step (delta_tm M))\<^sup>*" by simp
      obtain cM_final where
          M_path: "(init_config_mttm M w, cM_final)
                      \<in> (mttm_step (delta_tm M))\<^sup>*"
        and M_acc: "mt_state cM_final = t_tm M"
        using ar_simulation_phase_chunked_reverse
                [OF vM w_sub card_ge le_neq_bl reach_refl trace accept walk]
        by blast
      \<comment> \<open>Step 5: repack as \<open>w \<in> Lang_mttm M\<close>.\<close>
      obtain wM_acc nM_acc where
          cM_final_eq: "cM_final = Config\<^sub>M (t_tm M) wM_acc nM_acc"
        using M_acc by (cases cM_final) simp
      show "w \<in> Lang_mttm M"
        unfolding Lang_mttm_def
        using w_sub M_path cM_final_eq by blast
    qed
  qed
qed

end
