theory AlphabetReduction_Reverse
  imports AlphabetReduction_Theorems
begin

section \<open>Alphabet reduction: reverse language inclusion\<close>

text \<open>The reverse leg of \<open>alphabet_reduce_language\<close>:
  \<open>encode_input_ar (\<Gamma>_ktm M) (bl_ktm M) w \<in> Lang_ktm (alphabet_reduce M)
   \<Longrightarrow> w \<in> Lang_ktm M\<close>, the converse of the proven
  \<open>alphabet_reduce_language_forward\<close>.

  This holds for deterministic and nondeterministic \<open>M\<close> alike, and
  the proof is direct, with no argument about the uniqueness of
  validation chains as in AE's reverse direction, because AR's only
  nondeterministic substep, \<open>ar_delta_compute\<close>, is a direct
  single-step embedding of \<open>delta_ktm M\<close> (one substrate tuple per
  \<open>M\<close>-tuple, no AE-style \<open>m_steps_buffered\<close> slack), so every
  accepting \<open>M'\<close>-path decodes branch-by-branch to a genuine
  accepting \<open>M\<close>-path.

  The proof inverts the simulation directly: a per-cycle
  backward step lemma reads the \<open>M\<close>-transition straight off the
  compute tuple on the given \<open>M'\<close>-path and reuses the forward
  direction's invariants \<open>ar_simulates\<close>, \<open>ar_posk_consistent\<close>,
  \<open>ar_at_read_boundary\<close> read backward; a backward chunked engine
  aggregates the per-cycle steps into an \<open>M\<close>-run.
  Throughout, \<open>b\<close> abbreviates \<open>block_width \<Gamma>\<close> (the per-symbol cell width).\<close>

subsection \<open>Terminal accept configuration\<close>

text \<open>Base case of the backward engine: the accept state
  \<open>t_ktm (alphabet_reduce M)\<close> is terminal.  A valid machine never
  steps from its accept state (substrate \<open>ktm_step_src_neq_t\<close>),
  and \<open>alphabet_reduce M\<close> is valid by \<open>alphabet_reduce_wf\<close>;
  its accept state is \<open>(t_ktm M, ar_accept_stage (bl_ktm M))\<close> by
  \<open>alphabet_reduce_accept\<close>.

  Not used below: the reverse induction needs only the reject case,
  \<open>ar_reject_terminal\<close>, to rule out a rejecting configuration in the
  middle of a path; this lemma is its accepting counterpart.\<close>

lemma ar_accept_terminal:
  fixes M :: "('q, 'a) ktm"
    and c c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM:      "valid_ktm M"
      and card_ge: "card (\<Gamma>_ktm M) \<ge> 4"
      and step:    "(c, c') \<in> ktm_step (alphabet_reduce_delta M)"
  shows "ktc_state c \<noteq> (t_ktm M, ar_accept_stage (bl_ktm M))"
proof -
  let ?M' = "alphabet_reduce M :: ('q \<times> 'a ar_stage, sym4) ktm"
  have valM': "valid_ktm ?M'" by (rule alphabet_reduce_wf[OF vM card_ge])
  have step': "(c, c') \<in> ktm_step (delta_ktm ?M')" using step by simp
  have "ktc_state c \<noteq> t_ktm ?M'" by (rule ktm_step_src_neq_t[OF valM' step'])
  thus ?thesis by simp
qed

text \<open>Reject companion of \<open>ar_accept_terminal\<close>: the reject state
  \<open>r_ktm (alphabet_reduce M) = (r_ktm M, ar_reject_stage (bl_ktm M))\<close>
  (by \<open>alphabet_reduce_reject\<close>) is terminal too (substrate
  \<open>ktm_step_src_neq_r\<close>).  The backward engine uses it to kill a
  reject boundary reached mid-trace: the trace runs to the accept
  config, so a reject config can carry no outgoing step.\<close>

lemma ar_reject_terminal:
  fixes M :: "('q, 'a) ktm"
    and c c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM:      "valid_ktm M"
      and card_ge: "card (\<Gamma>_ktm M) \<ge> 4"
      and step:    "(c, c') \<in> ktm_step (alphabet_reduce_delta M)"
  shows "ktc_state c \<noteq> (r_ktm M, ar_reject_stage (bl_ktm M))"
proof -
  let ?M' = "alphabet_reduce M :: ('q \<times> 'a ar_stage, sym4) ktm"
  have valM': "valid_ktm ?M'" by (rule alphabet_reduce_wf[OF vM card_ge])
  have step': "(c, c') \<in> ktm_step (delta_ktm ?M')" using step by simp
  have "ktc_state c \<noteq> r_ktm ?M'" by (rule ktm_step_src_neq_r[OF valM' step'])
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

subsection \<open>Where each substep can lead\<close>

text \<open>Each substep relation's destination tag is confined to a
  small set: read loops to itself or transitions to compute; compute
  is the unique non-deterministic step and lands at write; write
  loops or advances; advance loops or hands off to next; next closes
  the cycle (back to read) or dispatches to a halt-coerced
  configuration.  These five facts encode the substep transition
  graph, and the reverse direction's arguments about the shape of a
  path rest on them.\<close>

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

text \<open>The central lemma of the reverse direction: a single \<open>M'\<close>-step out of
  an \<open>AR_SimCompute\<close> configuration reads the simulated
  \<open>M\<close>-transition straight off the compute tuple.  Because
  \<open>ar_delta_compute\<close> is a direct single-step embedding of
  \<open>delta_ktm M\<close>, the inversion yields a genuine
  \<open>(q, buf, q', m_a', m_d) \<in> delta_ktm M\<close> with no chain-uniqueness
  or determinism assumption — this is where AR's ND-generality is
  earned.  Compute neither writes nor moves: the tape and head
  positions are unchanged (read symbol equals write symbol, direction
  \<open>N\<close>).\<close>

lemma ar_compute_step_inv_sub:
  fixes M :: "('q, 'a) ktm"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes step: "(c', c'') \<in> ktm_step (ar_delta_compute M)"
      and stg:  "ktc_state c' = (q, AR_SimCompute, tk, i, buf, dvec, posk)"
  obtains q' m_a' m_d where
      "(q, buf, q', m_a', m_d) \<in> delta_ktm M"
    and "ktc_state c'' = (q', AR_SimWrite, 0, 0, m_a', m_d, posk)"
    and "ktc_tape c'' = ktc_tape c'"
    and "ktc_pos c'' = ktc_pos c'"
proof -
  from step obtain S ts n S'' aw move where
      c'_eq:   "c' = KConfig S ts n"
    and c''_eq: "c'' = KConfig S'' (\<lambda>k. (ts k)(n k := aw k))
                        (\<lambda>k. go_move (move k) (n k))"
    and rel:   "(S, (\<lambda>k. ts k (n k)), S'', aw, move)
                   \<in> ar_delta_compute M"
    by (auto elim: ktm_step.cases)
  have S_eq: "S = (q, AR_SimCompute, tk, i, buf, dvec, posk)"
    using stg c'_eq by simp
  have crel: "((q, AR_SimCompute, tk, i, buf, dvec, posk),
                 (\<lambda>k. ts k (n k)), S'', aw, move) \<in> ar_delta_compute M"
    using rel S_eq by simp
  from crel obtain q' m_a' m_d where
      mdelta:  "(q, buf, q', m_a', m_d) \<in> delta_ktm M"
    and S''_eq: "S'' = (q', AR_SimWrite, 0, 0, m_a', m_d, posk)"
    and aw_eq: "aw = (\<lambda>k. ts k (n k))"
    and dir_eq: "move = (\<lambda>_. MoveN)"
    unfolding ar_delta_compute_def by auto
  have state: "ktc_state c'' = (q', AR_SimWrite, 0, 0, m_a', m_d, posk)"
    using c''_eq S''_eq by simp
  have tape: "ktc_tape c'' = ktc_tape c'"
  proof -
    have "ktc_tape c'' = (\<lambda>k. (ts k)(n k := aw k))" using c''_eq by simp
    also have "\<dots> = ts" by (simp add: aw_eq fun_upd_triv)
    finally show ?thesis using c'_eq by simp
  qed
  have pos: "ktc_pos c'' = ktc_pos c'"
  proof -
    have "ktc_pos c'' = (\<lambda>k. go_move (move k) (n k))" using c''_eq by simp
    also have "\<dots> = n" by (simp add: dir_eq)
    finally show ?thesis using c'_eq by simp
  qed
  show ?thesis by (rule that[OF mdelta state tape pos])
qed

text \<open>The union-step face of the inversion: lift the union step into
  the compute sub-relation (\<open>ar_step_compute_lift\<close>) and invert there.
  Used by the preservation lemma \<open>ar_walker_step_from_at_compute\<close>
  below; the lemma that closes a cycle inverts the compute step of the
  sub-relation directly, via \<open>ar_compute_step_inv_sub\<close>.\<close>

lemma ar_compute_step_inv:
  fixes M :: "('q, 'a) ktm"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes step: "(c', c'') \<in> ktm_step (alphabet_reduce_delta M)"
      and stg:  "ktc_state c' = (q, AR_SimCompute, tk, i, buf, dvec, posk)"
  obtains q' m_a' m_d where
      "(q, buf, q', m_a', m_d) \<in> delta_ktm M"
    and "ktc_state c'' = (q', AR_SimWrite, 0, 0, m_a', m_d, posk)"
    and "ktc_tape c'' = ktc_tape c'"
    and "ktc_pos c'' = ktc_pos c'"
proof -
  from step obtain S ts n S'' aw move where
      c'_eq:   "c' = KConfig S ts n"
    and c''_eq: "c'' = KConfig S'' (\<lambda>k. (ts k)(n k := aw k))
                        (\<lambda>k. go_move (move k) (n k))"
    and rel:   "(S, (\<lambda>k. ts k (n k)), S'', aw, move)
                   \<in> alphabet_reduce_delta M"
    by (auto elim: ktm_step.cases)
  have src: "fst (snd S) = AR_SimCompute" using stg c'_eq by simp
  have crel: "(S, (\<lambda>k. ts k (n k)), S'', aw, move) \<in> ar_delta_compute M"
    by (rule ar_delta_compute_from_src[OF rel src])
  have step_explicit:
      "(KConfig S ts n, KConfig S'' (\<lambda>k. (ts k)(n k := aw k))
          (\<lambda>k. go_move (move k) (n k))) \<in> ktm_step (ar_delta_compute M)"
    using crel by (rule ktm_step.step)
  have sub: "(c', c'') \<in> ktm_step (ar_delta_compute M)"
    using step_explicit c'_eq c''_eq by simp
  show thesis
  proof (rule ar_compute_step_inv_sub[OF sub stg])
    fix q' m_a' m_d
    assume "(q, buf, q', m_a', m_d) \<in> delta_ktm M"
       and "ktc_state c'' = (q', AR_SimWrite, 0, 0, m_a', m_d, posk)"
       and "ktc_tape c'' = ktc_tape c'"
       and "ktc_pos c'' = ktc_pos c'"
    thus thesis by (rule that)
  qed
qed

subsection \<open>Inverting the closing substep: next cycle or halt\<close>

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
  \<open>t_ktm (alphabet_reduce M)\<close>.\<close>

lemma ar_next_step_inv:
  fixes M :: "('q, 'a) ktm"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes step: "(c', c'') \<in> ktm_step (alphabet_reduce_delta M)"
      and stg:  "ktc_state c' = (q, AR_SimNext, tk, i, buf, dvec, posk)"
  shows "ktc_tape c'' = ktc_tape c' \<and> ktc_pos c'' = ktc_pos c'
         \<and> ((q \<notin> {t_ktm M, r_ktm M}
               \<and> ktc_state c'' = (q, AR_SimRead, 0, 0, buf, dvec, posk))
            \<or> (q = t_ktm M
               \<and> ktc_state c'' = (t_ktm M, ar_accept_stage (bl_ktm M)))
            \<or> (q = r_ktm M
               \<and> ktc_state c'' = (r_ktm M, ar_reject_stage (bl_ktm M))))"
proof -
  from step obtain S ts n S'' aw move where
      c'_eq:   "c' = KConfig S ts n"
    and c''_eq: "c'' = KConfig S'' (\<lambda>k. (ts k)(n k := aw k))
                        (\<lambda>k. go_move (move k) (n k))"
    and rel:   "(S, (\<lambda>k. ts k (n k)), S'', aw, move)
                   \<in> alphabet_reduce_delta M"
    by (auto elim: ktm_step.cases)
  have S_eq: "S = (q, AR_SimNext, tk, i, buf, dvec, posk)"
    using stg c'_eq by simp
  have src: "fst (snd S) = AR_SimNext" using S_eq by simp
  have nrel: "((q, AR_SimNext, tk, i, buf, dvec, posk),
                 (\<lambda>k. ts k (n k)), S'', aw, move) \<in> ar_delta_next M"
    using ar_delta_next_from_src[OF rel src] S_eq by simp
  have core: "aw = (\<lambda>k. ts k (n k)) \<and> move = (\<lambda>_. MoveN)
       \<and> ((q \<notin> {t_ktm M, r_ktm M}
              \<and> S'' = (q, AR_SimRead, 0, 0, buf, dvec, posk))
          \<or> (q = t_ktm M \<and> S'' = (t_ktm M, ar_accept_stage (bl_ktm M)))
          \<or> (q = r_ktm M \<and> S'' = (r_ktm M, ar_reject_stage (bl_ktm M))))"
    using nrel
    unfolding ar_delta_next_def ar_accept_stage_def ar_reject_stage_def
    by auto
  have tape: "ktc_tape c'' = ktc_tape c'"
  proof -
    have "ktc_tape c'' = (\<lambda>k. (ts k)(n k := aw k))" using c''_eq by simp
    also have "\<dots> = ts" using core by (simp add: fun_upd_triv)
    finally show ?thesis using c'_eq by simp
  qed
  have pos: "ktc_pos c'' = ktc_pos c'"
  proof -
    have "ktc_pos c'' = (\<lambda>k. go_move (move k) (n k))" using c''_eq by simp
    also have "\<dots> = n" using core by simp
    finally show ?thesis using c'_eq by simp
  qed
  have st: "ktc_state c'' = S''" using c''_eq by simp
  show ?thesis using tape pos core st by simp
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

subsection \<open>Where a step of each substep lands\<close>

text \<open>Lift the per-relation destination-tag lemmas
  (\<open>ar_delta_X_dest\<close>) up through \<open>ktm_step\<close>: an
  \<open>M'\<close>-step out of a configuration whose source idx is
  \<open>AR_SimX\<close> lands at a configuration whose idx is in
  \<open>X\<close>'s dest set.  The five lemmas compose the substrate's
  \<open>ktm_step_states\<close> (the firing tuple's two states), the
  \<open>from_src\<close> union-disambiguation helpers, and
  \<open>ar_delta_X_dest\<close>.  Together they encode the cycle's
  substep transition graph at the level of whole \<open>M'\<close>-steps, which is
  what the induction along the path below uses: SimRead-loop-or-compute, compute-to-write,
  write-loop-or-advance, advance-loop-or-next,
  next-to-read-or-halt.\<close>

lemma ar_step_from_SimRead_lands:
  assumes step: "(c, c') \<in> ktm_step (alphabet_reduce_delta M)"
      and src:  "fst (snd (ktc_state c)) = AR_SimRead"
  shows "fst (snd (ktc_state c')) = AR_SimRead
       \<or> fst (snd (ktc_state c')) = AR_SimCompute"
proof -
  from step obtain a a' d
    where "(ktc_state c, a, ktc_state c', a', d) \<in> alphabet_reduce_delta M"
    by (rule ktm_step_states)
  from ar_delta_read_from_src [OF this src] show ?thesis
    by (rule ar_delta_read_dest)
qed

text \<open>The \<open>compute\<close> member of the five lemmas above is not used: the
  compute substep is the nondeterministic branch point, and the proof
  handles it by reading the \<open>M\<close>-transition off the step instead.  It is
  stated so that the substep transition graph is complete.\<close>

lemma ar_step_from_SimCompute_lands:
  assumes step: "(c, c') \<in> ktm_step (alphabet_reduce_delta M)"
      and src:  "fst (snd (ktc_state c)) = AR_SimCompute"
  shows "fst (snd (ktc_state c')) = AR_SimWrite"
proof -
  from step obtain a a' d
    where "(ktc_state c, a, ktc_state c', a', d) \<in> alphabet_reduce_delta M"
    by (rule ktm_step_states)
  from ar_delta_compute_from_src [OF this src] show ?thesis
    by (rule ar_delta_compute_dest)
qed

lemma ar_step_from_SimWrite_lands:
  assumes step: "(c, c') \<in> ktm_step (alphabet_reduce_delta M)"
      and src:  "fst (snd (ktc_state c)) = AR_SimWrite"
  shows "fst (snd (ktc_state c')) = AR_SimWrite
       \<or> fst (snd (ktc_state c')) = AR_SimAdvance"
proof -
  from step obtain a a' d
    where "(ktc_state c, a, ktc_state c', a', d) \<in> alphabet_reduce_delta M"
    by (rule ktm_step_states)
  from ar_delta_write_from_src [OF this src] show ?thesis
    by (rule ar_delta_write_dest)
qed

lemma ar_step_from_SimAdvance_lands:
  assumes step: "(c, c') \<in> ktm_step (alphabet_reduce_delta M)"
      and src:  "fst (snd (ktc_state c)) = AR_SimAdvance"
  shows "fst (snd (ktc_state c')) = AR_SimAdvance
       \<or> fst (snd (ktc_state c')) = AR_SimNext"
proof -
  from step obtain a a' d
    where "(ktc_state c, a, ktc_state c', a', d) \<in> alphabet_reduce_delta M"
    by (rule ktm_step_states)
  from ar_delta_advance_from_src [OF this src] show ?thesis
    by (rule ar_delta_advance_dest)
qed

lemma ar_step_from_SimNext_lands:
  assumes step: "(c, c') \<in> ktm_step (alphabet_reduce_delta M)"
      and src:  "fst (snd (ktc_state c)) = AR_SimNext"
  shows "fst (snd (ktc_state c')) = AR_SimRead
       \<or> fst (snd (ktc_state c')) = AR_HaltAccept
       \<or> fst (snd (ktc_state c')) = AR_HaltReject"
proof -
  from step obtain a a' d
    where "(ktc_state c, a, ktc_state c', a', d) \<in> alphabet_reduce_delta M"
    by (rule ktm_step_states)
  from ar_delta_next_from_src [OF this src] show ?thesis
    by (rule ar_delta_next_dest)
qed

subsection \<open>Invariants for each substep of the cycle\<close>

text \<open>The reverse direction walks along the \<open>M'\<close>-path one step at a time
  (hence the \<^emph>\<open>walker\<close> in the names below): an induction over the path
  that tracks where in the cycle we are by reading
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
  from the witness chain living in the \<^emph>\<open>specific\<close> substep relation
  \<open>ktm_step (ar_delta_T M)\<close>, which by
  \<open>ar_delta_T_src\<close> can only fire from sources at T —
  ruling out the wrap.\<close>

definition ar_walker_at_boundary ::
  "('q, 'a) ktm
    \<Rightarrow> ('a, 'q) ktc_config
    \<Rightarrow> (sym4, 'q \<times> 'a ar_stage) ktc_config \<Rightarrow> bool" where
  "ar_walker_at_boundary M cM c' \<longleftrightarrow>
     ar_simulates M cM c'
   \<and> ar_posk_consistent M cM c'
   \<and> ar_at_read_boundary M c'"

definition ar_walker_in_read ::
  "('q, 'a) ktm
    \<Rightarrow> ('a, 'q) ktc_config
    \<Rightarrow> (sym4, 'q \<times> 'a ar_stage) ktc_config \<Rightarrow> bool" where
  "ar_walker_in_read M cM c' \<longleftrightarrow>
     fst (snd (ktc_state c')) = AR_SimRead
   \<and> (\<exists>c_b m. ar_walker_at_boundary M cM c_b
                \<and> (c_b, c') \<in> (ktm_step (ar_delta_read M)) ^^ m)"

definition ar_walker_at_compute ::
  "('q, 'a) ktm
    \<Rightarrow> ('a, 'q) ktc_config
    \<Rightarrow> (sym4, 'q \<times> 'a ar_stage) ktc_config \<Rightarrow> bool" where
  "ar_walker_at_compute M cM c' \<longleftrightarrow>
     fst (snd (ktc_state c')) = AR_SimCompute
   \<and> (\<exists>c_b m. ar_walker_at_boundary M cM c_b
                \<and> (c_b, c') \<in> (ktm_step (ar_delta_read M)) ^^ m)"

definition ar_walker_in_write ::
  "('q, 'a) ktm
    \<Rightarrow> ('a, 'q) ktc_config
    \<Rightarrow> (sym4, 'q \<times> 'a ar_stage) ktc_config \<Rightarrow> bool" where
  "ar_walker_in_write M cM c' \<longleftrightarrow>
     fst (snd (ktc_state c')) = AR_SimWrite
   \<and> (\<exists>c_b c_w m_r m_w.
        ar_walker_at_boundary M cM c_b
        \<and> (c_b, c_w) \<in> (ktm_step (ar_delta_read M)) ^^ m_r
        \<and> fst (snd (ktc_state c_w)) = AR_SimCompute
        \<and> (\<exists>c_w_post. (c_w, c_w_post) \<in> ktm_step (ar_delta_compute M)
                       \<and> (c_w_post, c') \<in> (ktm_step (ar_delta_write M)) ^^ m_w))"

definition ar_walker_in_advance ::
  "('q, 'a) ktm
    \<Rightarrow> ('a, 'q) ktc_config
    \<Rightarrow> (sym4, 'q \<times> 'a ar_stage) ktc_config \<Rightarrow> bool" where
  "ar_walker_in_advance M cM c' \<longleftrightarrow>
     fst (snd (ktc_state c')) = AR_SimAdvance
   \<and> (\<exists>c_b c_w c_a m_r m_w m_a.
        ar_walker_at_boundary M cM c_b
        \<and> (c_b, c_w) \<in> (ktm_step (ar_delta_read M)) ^^ m_r
        \<and> fst (snd (ktc_state c_w)) = AR_SimCompute
        \<and> fst (snd (ktc_state c_a)) = AR_SimAdvance
        \<and> (\<exists>c_w_post. (c_w, c_w_post) \<in> ktm_step (ar_delta_compute M)
                       \<and> (c_w_post, c_a) \<in> (ktm_step (ar_delta_write M)) ^^ m_w
                       \<and> (c_a, c') \<in> (ktm_step (ar_delta_advance M)) ^^ m_a))"

definition ar_walker_at_next ::
  "('q, 'a) ktm
    \<Rightarrow> ('a, 'q) ktc_config
    \<Rightarrow> (sym4, 'q \<times> 'a ar_stage) ktc_config \<Rightarrow> bool" where
  "ar_walker_at_next M cM c' \<longleftrightarrow>
     fst (snd (ktc_state c')) = AR_SimNext
   \<and> (\<exists>c_b c_w c_a c_n m_r m_w m_a.
        ar_walker_at_boundary M cM c_b
        \<and> (c_b, c_w) \<in> (ktm_step (ar_delta_read M)) ^^ m_r
        \<and> fst (snd (ktc_state c_w)) = AR_SimCompute
        \<and> fst (snd (ktc_state c_a)) = AR_SimAdvance
        \<and> (\<exists>c_w_post. (c_w, c_w_post) \<in> ktm_step (ar_delta_compute M)
                       \<and> (c_w_post, c_a) \<in> (ktm_step (ar_delta_write M)) ^^ m_w
                       \<and> (c_a, c_n) \<in> (ktm_step (ar_delta_advance M)) ^^ m_a
                       \<and> c_n = c'))"

subsection \<open>A step from a given substep is a step of that substep's relation\<close>

text \<open>Four \<open>ktm_step\<close>-to-specific-substep lifts: an
  \<open>M'\<close>-step in \<open>ktm_step (alphabet_reduce_delta M)\<close>
  whose source carries substep tag T is in fact in the smaller
  \<open>ktm_step (ar_delta_T M)\<close>.  Each is the substrate's
  \<open>ktm_step_restrict_src\<close> applied to the matching
  \<open>ar_delta_T_from_src\<close> helper, which narrows the firing tuple by
  src-tag uniqueness.  The preservation lemmas below chain these lifts
  with the destination lemmas (\<open>ar_step_from_SimX_lands\<close>) to extend
  the witness chain by one step.\<close>

lemma ar_step_read_lift:
  fixes M :: "('q, 'a) ktm"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes src:  "fst (snd (ktc_state c')) = AR_SimRead"
      and step: "(c', c'') \<in> ktm_step (alphabet_reduce_delta M)"
  shows "(c', c'') \<in> ktm_step (ar_delta_read M)"
  by (rule ktm_step_restrict_src [OF step])
     (erule ar_delta_read_from_src, assumption, rule src)

lemma ar_step_compute_lift:
  fixes M :: "('q, 'a) ktm"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes src:  "fst (snd (ktc_state c')) = AR_SimCompute"
      and step: "(c', c'') \<in> ktm_step (alphabet_reduce_delta M)"
  shows "(c', c'') \<in> ktm_step (ar_delta_compute M)"
  by (rule ktm_step_restrict_src [OF step])
     (erule ar_delta_compute_from_src, assumption, rule src)

lemma ar_step_write_lift:
  fixes M :: "('q, 'a) ktm"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes src:  "fst (snd (ktc_state c')) = AR_SimWrite"
      and step: "(c', c'') \<in> ktm_step (alphabet_reduce_delta M)"
  shows "(c', c'') \<in> ktm_step (ar_delta_write M)"
  by (rule ktm_step_restrict_src [OF step])
     (erule ar_delta_write_from_src, assumption, rule src)

lemma ar_step_advance_lift:
  fixes M :: "('q, 'a) ktm"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes src:  "fst (snd (ktc_state c')) = AR_SimAdvance"
      and step: "(c', c'') \<in> ktm_step (alphabet_reduce_delta M)"
  shows "(c', c'') \<in> ktm_step (ar_delta_advance M)"
  by (rule ktm_step_restrict_src [OF step])
     (erule ar_delta_advance_from_src, assumption, rule src)

subsection \<open>Runs of the read substep are determined\<close>

text \<open>Two structural facts about chains in the read sub-relation:
  the sub-relation is \<^emph>\<open>functional\<close> (\<open>ar_delta_read_functional\<close>,
  lifted to steps by the substrate's \<open>ktm_step_det_at\<close>); and it
  cannot fire from a source whose substep tag is \<open>AR_SimCompute\<close>
  (by \<open>ar_delta_read_src\<close>).  The substrate's
  \<open>relpow_halted_same_run\<close> turns the two into the pinning: a chain
  ending at \<open>AR_SimCompute\<close> is unique in both its length and its
  endpoint, so if two chains in the sub-relation start at the same seed and both
  end at an \<open>AR_SimCompute\<close>-tagged config, they coincide.  This
  is what bridges the walker's by-construction \<open>R_read\<close> witness
  chain to the existence chain produced by \<open>ar_read_phase\<close>, whose
  steps lie in \<open>ar_delta_read\<close> as well as in the full relation: the
  witness chain inherits the latter's
  stated endpoint state shape, including the load-bearing
  \<open>buf = \<lambda>k. ktc_tape cM k (ktc_pos cM k)\<close>.\<close>

lemma ar_delta_read_no_step_from_SimCompute:
  fixes M :: "('q, 'a) ktm"
    and c c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes "fst (snd (ktc_state c)) = AR_SimCompute"
  shows "(c, c') \<notin> ktm_step (ar_delta_read M)"
proof
  assume h: "(c, c') \<in> ktm_step (ar_delta_read M)"
  from h obtain S ts n S' aw move where
      ceq: "c = KConfig S ts n"
    and rel: "(S, (\<lambda>k. ts k (n k)), S', aw, move) \<in> ar_delta_read M"
    by (auto elim: ktm_step.cases)
  have "fst (snd S) = AR_SimRead" using ar_delta_read_src[OF rel] .
  hence "fst (snd (ktc_state c)) = AR_SimRead" using ceq by simp
  with assms show False by simp
qed

lemma chain_ar_delta_read_to_SimCompute_uniq:
  fixes M :: "('q, 'a) ktm"
    and c c\<^sub>1 c\<^sub>2 :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes h\<^sub>1: "(c, c\<^sub>1) \<in> (ktm_step (ar_delta_read M)) ^^ m"
      and h\<^sub>2: "(c, c\<^sub>2) \<in> (ktm_step (ar_delta_read M)) ^^ n"
      and c\<^sub>1cpu: "fst (snd (ktc_state c\<^sub>1)) = AR_SimCompute"
      and c\<^sub>2cpu: "fst (snd (ktc_state c\<^sub>2)) = AR_SimCompute"
  shows "m = n \<and> c\<^sub>1 = c\<^sub>2"
proof -
  have fn: "y = z"
    if "x \<in> UNIV" "(x, y) \<in> ktm_step (ar_delta_read M)"
       "(x, z) \<in> ktm_step (ar_delta_read M)" for x y z
    by (rule ktm_step_det_at [OF _ that(2,3)])
       (blast dest: ar_delta_read_functional)
  have stuck: False
    if "u \<in> {C. fst (snd (ktc_state C)) = AR_SimCompute}"
       "(u, v) \<in> ktm_step (ar_delta_read M)" for u v
    using that ar_delta_read_no_step_from_SimCompute by blast
  show ?thesis
    by (rule relpow_halted_same_run
          [where R = UNIV and H = "{C. fst (snd (ktc_state C)) = AR_SimCompute}",
           OF _ fn stuck _ h\<^sub>1 _ h\<^sub>2])
       (simp_all add: c\<^sub>1cpu c\<^sub>2cpu)
qed


text \<open>Two parallel chain-pinning suites for the write and advance
  sub-relations, mirroring the read suite verbatim with
  \<open>ar_delta_write\<close> / \<open>ar_delta_advance\<close> in place of
  \<open>ar_delta_read\<close> and \<open>AR_SimAdvance\<close> / \<open>AR_SimNext\<close>
  in place of \<open>AR_SimCompute\<close>.  Functionality
  (\<open>ar_delta_write_functional\<close>, \<open>ar_delta_advance_functional\<close>) and src
  uniqueness (\<open>ar_delta_write_src\<close>, \<open>ar_delta_advance_src\<close>)
  feed the same scaffold.  These suites are used by the cycle-close
  bridging lemma to pin walker write/advance chains against the
  forward \<open>ar_write_phase\<close> / \<open>ar_advance_phase\<close>
  constructions.\<close>

lemma ar_delta_write_no_step_from_SimAdvance:
  fixes M :: "('q, 'a) ktm"
    and c c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes "fst (snd (ktc_state c)) = AR_SimAdvance"
  shows "(c, c') \<notin> ktm_step (ar_delta_write M)"
proof
  assume h: "(c, c') \<in> ktm_step (ar_delta_write M)"
  from h obtain S ts n S' aw move where
      ceq: "c = KConfig S ts n"
    and rel: "(S, (\<lambda>k. ts k (n k)), S', aw, move) \<in> ar_delta_write M"
    by (auto elim: ktm_step.cases)
  have "fst (snd S) = AR_SimWrite" using ar_delta_write_src[OF rel] .
  hence "fst (snd (ktc_state c)) = AR_SimWrite" using ceq by simp
  with assms show False by simp
qed

lemma chain_ar_delta_write_to_SimAdvance_uniq:
  fixes M :: "('q, 'a) ktm"
    and c c\<^sub>1 c\<^sub>2 :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes h\<^sub>1: "(c, c\<^sub>1) \<in> (ktm_step (ar_delta_write M)) ^^ m"
      and h\<^sub>2: "(c, c\<^sub>2) \<in> (ktm_step (ar_delta_write M)) ^^ n"
      and c\<^sub>1adv: "fst (snd (ktc_state c\<^sub>1)) = AR_SimAdvance"
      and c\<^sub>2adv: "fst (snd (ktc_state c\<^sub>2)) = AR_SimAdvance"
  shows "m = n \<and> c\<^sub>1 = c\<^sub>2"
proof -
  have fn: "y = z"
    if "x \<in> UNIV" "(x, y) \<in> ktm_step (ar_delta_write M)"
       "(x, z) \<in> ktm_step (ar_delta_write M)" for x y z
    by (rule ktm_step_det_at [OF _ that(2,3)])
       (blast dest: ar_delta_write_functional)
  have stuck: False
    if "u \<in> {C. fst (snd (ktc_state C)) = AR_SimAdvance}"
       "(u, v) \<in> ktm_step (ar_delta_write M)" for u v
    using that ar_delta_write_no_step_from_SimAdvance by blast
  show ?thesis
    by (rule relpow_halted_same_run
          [where R = UNIV and H = "{C. fst (snd (ktc_state C)) = AR_SimAdvance}",
           OF _ fn stuck _ h\<^sub>1 _ h\<^sub>2])
       (simp_all add: c\<^sub>1adv c\<^sub>2adv)
qed

lemma ar_delta_advance_no_step_from_SimNext:
  fixes M :: "('q, 'a) ktm"
    and c c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes "fst (snd (ktc_state c)) = AR_SimNext"
  shows "(c, c') \<notin> ktm_step (ar_delta_advance M)"
proof
  assume h: "(c, c') \<in> ktm_step (ar_delta_advance M)"
  from h obtain S ts n S' aw move where
      ceq: "c = KConfig S ts n"
    and rel: "(S, (\<lambda>k. ts k (n k)), S', aw, move) \<in> ar_delta_advance M"
    by (auto elim: ktm_step.cases)
  have "fst (snd S) = AR_SimAdvance" using ar_delta_advance_src[OF rel] .
  hence "fst (snd (ktc_state c)) = AR_SimAdvance" using ceq by simp
  with assms show False by simp
qed

lemma chain_ar_delta_advance_to_SimNext_uniq:
  fixes M :: "('q, 'a) ktm"
    and c c\<^sub>1 c\<^sub>2 :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes h\<^sub>1: "(c, c\<^sub>1) \<in> (ktm_step (ar_delta_advance M)) ^^ m"
      and h\<^sub>2: "(c, c\<^sub>2) \<in> (ktm_step (ar_delta_advance M)) ^^ n"
      and c\<^sub>1nxt: "fst (snd (ktc_state c\<^sub>1)) = AR_SimNext"
      and c\<^sub>2nxt: "fst (snd (ktc_state c\<^sub>2)) = AR_SimNext"
  shows "m = n \<and> c\<^sub>1 = c\<^sub>2"
proof -
  have fn: "y = z"
    if "x \<in> UNIV" "(x, y) \<in> ktm_step (ar_delta_advance M)"
       "(x, z) \<in> ktm_step (ar_delta_advance M)" for x y z
    by (rule ktm_step_det_at [OF _ that(2,3)])
       (blast dest: ar_delta_advance_functional)
  have stuck: False
    if "u \<in> {C. fst (snd (ktc_state C)) = AR_SimNext}"
       "(u, v) \<in> ktm_step (ar_delta_advance M)" for u v
    using that ar_delta_advance_no_step_from_SimNext by blast
  show ?thesis
    by (rule relpow_halted_same_run
          [where R = UNIV and H = "{C. fst (snd (ktc_state C)) = AR_SimNext}",
           OF _ fn stuck _ h\<^sub>1 _ h\<^sub>2])
       (simp_all add: c\<^sub>1nxt c\<^sub>2nxt)
qed

subsection \<open>Each step preserves the substep invariants\<close>

text \<open>One preservation lemma per substep predicate: an
  \<open>M'\<close>-step out of a config satisfying the current invariant
  lands at a config satisfying the next invariant in the cycle (or
  splits the disjunction when the substep's relation has multiple
  destination arms).  Together with the chunked engine, these
  describe how the walker's invariant evolves step by step: the substep
  index carried in the \<open>M'\<close>-configuration decides which case applies at
  each step, so no argument about the shape of the whole chain is
  needed.\<close>

lemma ar_walker_step_from_boundary:
  fixes M :: "('q, 'a) ktm"
    and cM :: "('a, 'q) ktc_config"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes inv: "ar_walker_at_boundary M cM c'"
      and step: "(c', c'') \<in> ktm_step (alphabet_reduce_delta M)"
  shows "ar_walker_in_read M cM c'' \<or> ar_walker_at_compute M cM c''"
proof -
  obtain qM' stg where st: "ktc_state c' = (qM', stg)"
    by (cases "ktc_state c'") auto
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
  have src: "fst (snd (ktc_state c')) = AR_SimRead"
  proof -
    have sim: "ar_simulates M cM c'"
      using inv unfolding ar_walker_at_boundary_def by simp
    have sim_body:
        "((idx = AR_SimRead \<and> qM' \<notin> {t_ktm M, r_ktm M})
            \<or> (qM' = t_ktm M
                 \<and> (idx, tk, i, buf, dvec, posk) = ar_accept_stage (bl_ktm M))
            \<or> (qM' = r_ktm M
                 \<and> (idx, tk, i, buf, dvec, posk) = ar_reject_stage (bl_ktm M)))
         \<and> ktc_state cM = qM'"
      using sim unfolding ar_simulates_def by (simp add: st sg Let_def)
    consider (R) "idx = AR_SimRead"
           | (A) "qM' = t_ktm M \<and> (idx, tk, i, buf, dvec, posk) = ar_accept_stage (bl_ktm M)"
           | (J) "qM' = r_ktm M \<and> (idx, tk, i, buf, dvec, posk) = ar_reject_stage (bl_ktm M)"
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
         in \<open>ktm_step.cases\<close> with \<open>fst (snd S) = AR_HaltAccept\<close>
         cannot fire any of the five substep relations
         (constructor-distinctness from
         \<open>alphabet_reduce_delta_src_tag\<close>).\<close>
      have idx_acc: "idx = AR_HaltAccept"
        using A by (simp add: ar_accept_stage_def)
      from step obtain S ts n S' aw move where
          c'_eq: "c' = KConfig S ts n"
        and rel: "(S, (\<lambda>k. ts k (n k)), S', aw, move)
                    \<in> alphabet_reduce_delta M"
        by (auto elim: ktm_step.cases)
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
      from step obtain S ts n S' aw move where
          c'_eq: "c' = KConfig S ts n"
        and rel: "(S, (\<lambda>k. ts k (n k)), S', aw, move)
                    \<in> alphabet_reduce_delta M"
        by (auto elim: ktm_step.cases)
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
  have step_read: "(c', c'') \<in> ktm_step (ar_delta_read M)"
    using ar_step_read_lift[OF src step] .
  hence step_read1: "(c', c'') \<in> (ktm_step (ar_delta_read M)) ^^ Suc 0"
    by simp
  \<comment> \<open>Dispatch on the dest tag\<close>
  from ar_step_from_SimRead_lands[OF step src]
  have dest: "fst (snd (ktc_state c'')) = AR_SimRead
            \<or> fst (snd (ktc_state c'')) = AR_SimCompute" .
  thus ?thesis
  proof
    assume dr: "fst (snd (ktc_state c'')) = AR_SimRead"
    have "ar_walker_in_read M cM c''"
      unfolding ar_walker_in_read_def
      using dr inv step_read1 by blast
    thus ?thesis ..
  next
    assume dc: "fst (snd (ktc_state c'')) = AR_SimCompute"
    have "ar_walker_at_compute M cM c''"
      unfolding ar_walker_at_compute_def
      using dc inv step_read1 by blast
    thus ?thesis ..
  qed
qed

lemma ar_walker_step_from_in_read:
  fixes M :: "('q, 'a) ktm"
    and cM :: "('a, 'q) ktc_config"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes inv: "ar_walker_in_read M cM c'"
      and step: "(c', c'') \<in> ktm_step (alphabet_reduce_delta M)"
  shows "ar_walker_in_read M cM c'' \<or> ar_walker_at_compute M cM c''"
proof -
  have src: "fst (snd (ktc_state c')) = AR_SimRead"
    using inv unfolding ar_walker_in_read_def by simp
  obtain c_b m where
      wb: "ar_walker_at_boundary M cM c_b"
    and chain: "(c_b, c') \<in> (ktm_step (ar_delta_read M)) ^^ m"
    using inv unfolding ar_walker_in_read_def by blast
  have step_read: "(c', c'') \<in> ktm_step (ar_delta_read M)"
    using ar_step_read_lift[OF src step] .
  have chain_ext: "(c_b, c'') \<in> (ktm_step (ar_delta_read M)) ^^ Suc m"
    using chain step_read by (rule relpow_Suc_I)
  from ar_step_from_SimRead_lands[OF step src]
  have dest: "fst (snd (ktc_state c'')) = AR_SimRead
            \<or> fst (snd (ktc_state c'')) = AR_SimCompute" .
  thus ?thesis
  proof
    assume dr: "fst (snd (ktc_state c'')) = AR_SimRead"
    have "ar_walker_in_read M cM c''"
      unfolding ar_walker_in_read_def
      using dr wb chain_ext by blast
    thus ?thesis ..
  next
    assume dc: "fst (snd (ktc_state c'')) = AR_SimCompute"
    have "ar_walker_at_compute M cM c''"
      unfolding ar_walker_at_compute_def
      using dc wb chain_ext by blast
    thus ?thesis ..
  qed
qed

lemma ar_walker_step_from_at_compute:
  fixes M :: "('q, 'a) ktm"
    and cM :: "('a, 'q) ktc_config"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes inv: "ar_walker_at_compute M cM c'"
      and step: "(c', c'') \<in> ktm_step (alphabet_reduce_delta M)"
      and vM: "valid_ktm M"
      and qQ: "ktc_state cM \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and tapeG: "\<And>k. ktc_tape cM k (ktc_pos cM k) \<in> \<Gamma>_ktm M"
  shows "ar_walker_in_write M cM c''"
proof -
  let ?k = "block_width (\<Gamma>_ktm M)"
  let ?aM = "\<lambda>k. ktc_tape cM k (ktc_pos cM k)"
  have c'_compute: "fst (snd (ktc_state c')) = AR_SimCompute"
    using inv unfolding ar_walker_at_compute_def by simp
  obtain c_b m_w where
      wb: "ar_walker_at_boundary M cM c_b"
    and chain_w: "(c_b, c') \<in> (ktm_step (ar_delta_read M)) ^^ m_w"
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
  have cb_idx: "fst (snd (ktc_state c_b)) = AR_SimRead"
  proof (cases m_w)
    case 0
    have cb_eq: "c_b = c'" using chain_w 0 by simp
    have cb_compute: "fst (snd (ktc_state c_b)) = AR_SimCompute"
      using c'_compute cb_eq by simp
    obtain qM' stg where st_b: "ktc_state c_b = (qM', stg)"
      by (cases "ktc_state c_b") auto
    obtain idx tk i buf dvec posk where
        sg_b: "stg = (idx, tk, i, buf, dvec, posk)" by (cases stg) auto
    have idx_cpu: "idx = AR_SimCompute" using cb_compute st_b sg_b by simp
    have "(idx = AR_SimRead \<and> qM' \<notin> {t_ktm M, r_ktm M})
            \<or> (qM' = t_ktm M \<and> stg = ar_accept_stage (bl_ktm M))
            \<or> (qM' = r_ktm M \<and> stg = ar_reject_stage (bl_ktm M))"
      using sim st_b sg_b unfolding ar_simulates_def by (auto split: prod.splits)
    hence False
      using idx_cpu sg_b
      by (auto simp: ar_accept_stage_def ar_reject_stage_def)
    thus ?thesis ..
  next
    case (Suc m')
    have hsuc: "(c_b, c') \<in> (ktm_step (ar_delta_read M)) ^^ Suc m'"
      using chain_w Suc by simp
    obtain c_1 where
        first: "(c_b, c_1) \<in> ktm_step (ar_delta_read M)"
      using relpow_Suc_D2[OF hsuc] by blast
    from first obtain S ts n S' aw move where
        ceq: "c_b = KConfig S ts n"
      and rel: "(S, (\<lambda>k. ts k (n k)), S', aw, move) \<in> ar_delta_read M"
      by (auto elim: ktm_step.cases)
    have "fst (snd S) = AR_SimRead" using ar_delta_read_src[OF rel] .
    thus ?thesis using ceq by simp
  qed
  \<comment> \<open>Extract \<open>c_b\<close>'s full state shape and the boundary's
     correspondences.\<close>
  obtain qM' stg where st_b: "ktc_state c_b = (qM', stg)"
    by (cases "ktc_state c_b") auto
  obtain idx tk i buf dvec posk where
      sg_b: "stg = (idx, tk, i, buf, dvec, posk)" by (cases stg) auto
  have idx_read: "idx = AR_SimRead" using cb_idx st_b sg_b by simp
  have qM'_eq: "qM' = ktc_state cM"
    using sim st_b sg_b unfolding ar_simulates_def by (auto split: prod.splits)
  have tcorr: "\<forall>k < k_ktm M. ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                       (ktc_tape cM k) (ktc_tape c_b k)"
    using sim st_b sg_b unfolding ar_simulates_def by (auto split: prod.splits)
  have ppos: "\<And>k. ktc_pos c_b k = sim_pos ?k (ktc_pos cM k)"
    using sim st_b sg_b idx_read
    unfolding ar_simulates_def by (auto split: prod.splits)
  have pkok: "\<And>k. posk k = AR_AtLE \<longleftrightarrow> ktc_pos cM k = 0"
    using pcons st_b sg_b idx_read
    unfolding ar_posk_consistent_def by (auto split: prod.splits)
  have bnd_unfold: "idx = AR_SimRead
        \<longrightarrow> (tk = 0 \<and> i = 0
             \<and> (\<forall>k. buf k \<in> \<Gamma>_ktm M \<union> {bl_ktm M})
             \<and> ar_stage_bounded (bl_ktm M) (k_ktm M)
                  (idx, tk, i, buf, dvec, posk))"
    using rbnd st_b sg_b
    unfolding ar_at_read_boundary_def by (auto split: prod.splits)
  have tk0: "tk = 0" and i0: "i = 0"
    and bufG: "\<And>k. buf k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
    using bnd_unfold idx_read by simp_all
  have stg0: "ktc_state c_b = (ktc_state cM, AR_SimRead, 0, 0, buf, dvec, posk)"
    using st_b sg_b qM'_eq idx_read tk0 i0 by simp
  \<comment> \<open>Boundary blank-tail and bounded-stage facts, now produced by the
     strengthened \<open>ar_at_read_boundary\<close>: \<open>src0_b\<close> from its
     bounded-stage conjunct (specialised by \<open>idx = AR_SimRead\<close>,
     \<open>tk = 0\<close>, \<open>i = 0\<close>); \<open>pad0_b\<close> from its config
     padding-blank conjunct.\<close>
  have pad0_b: "\<forall>j \<ge> k_ktm M. ktc_tape c_b j (ktc_pos c_b j) = BLANK4"
    using rbnd unfolding ar_at_read_boundary_def by (auto split: prod.splits)
  have src0_b: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                  (AR_SimRead, 0, 0, buf, dvec, posk)"
    using bnd_unfold idx_read tk0 i0 by simp
  \<comment> \<open>Apply \<open>ar_read_phase\<close> at the boundary, keeping the read sub-relation.\<close>
  obtain c_r m_phase where
      r_chain: "(c_b, c_r) \<in> (ktm_step (ar_delta_read M)) ^^ m_phase"
    and r_state: "ktc_state c_r = (ktc_state cM, AR_SimCompute, k_unidx 0, 0,
                    (\<lambda>k. if k < k_ktm M then ?aM k else buf k), dvec,
                    (\<lambda>k. if k < k_ktm M
                          then (if ktc_pos cM k = 0 then AR_AtLE
                                else if ktc_pos cM k = 1 then AR_AtFirstProper
                                else AR_AtFurtherProper)
                          else posk k))"
    using ar_read_phase[OF vM qQ kge2 stg0 tcorr ppos pkok tapeG bufG
                           pad0_b src0_b] ktm_run_mono [OF Int_lower2]
    by blast
  have r_cpu: "fst (snd (ktc_state c_r)) = AR_SimCompute"
    using r_state by simp
  \<comment> \<open>Pin the walker's witness chain against \<open>ar_read_phase\<close>'s.\<close>
  have c'_eq_c_r: "c' = c_r"
    using chain_ar_delta_read_to_SimCompute_uniq[OF chain_w r_chain c'_compute r_cpu]
    by simp
  have c'_state: "ktc_state c' = (ktc_state cM, AR_SimCompute, k_unidx 0, 0,
                    (\<lambda>k. if k < k_ktm M then ?aM k else buf k), dvec,
                    (\<lambda>k. if k < k_ktm M
                          then (if ktc_pos cM k = 0 then AR_AtLE
                                else if ktc_pos cM k = 1 then AR_AtFirstProper
                                else AR_AtFurtherProper)
                          else posk k))"
    using c'_eq_c_r r_state by simp
  \<comment> \<open>Lift the compute step to the sub-relation and invert.\<close>
  have step_compute: "(c', c'') \<in> ktm_step (ar_delta_compute M)"
    using ar_step_compute_lift[OF c'_compute step] .
  obtain q' m_a' m_d where
      mdelta: "(ktc_state cM, (\<lambda>k. if k < k_ktm M then ?aM k else buf k),
                  q', m_a', m_d) \<in> delta_ktm M"
    and c''_state: "ktc_state c'' = (q', AR_SimWrite, 0, 0, m_a', m_d,
                      (\<lambda>k. if k < k_ktm M
                            then (if ktc_pos cM k = 0 then AR_AtLE
                                  else if ktc_pos cM k = 1 then AR_AtFirstProper
                                  else AR_AtFurtherProper)
                            else posk k))"
    and c''_tape: "ktc_tape c'' = ktc_tape c'"
    and c''_pos: "ktc_pos c'' = ktc_pos c'"
    using ar_compute_step_inv[OF step c'_state] by blast
  \<comment> \<open>Bundle the witness chain into \<open>ar_walker_in_write\<close>.\<close>
  have c''_write: "fst (snd (ktc_state c'')) = AR_SimWrite"
    using c''_state by simp
  have empty_w: "(c'', c'') \<in> (ktm_step (ar_delta_write M)) ^^ 0" by simp
  show "ar_walker_in_write M cM c''"
    unfolding ar_walker_in_write_def
  proof (intro conjI)
    show "fst (snd (ktc_state c'')) = AR_SimWrite" by (rule c''_write)
    show "\<exists>c_b c_w m_r m_w.
            ar_walker_at_boundary M cM c_b
          \<and> (c_b, c_w) \<in> (ktm_step (ar_delta_read M)) ^^ m_r
          \<and> fst (snd (ktc_state c_w)) = AR_SimCompute
          \<and> (\<exists>c_w_post. (c_w, c_w_post) \<in> ktm_step (ar_delta_compute M)
                          \<and> (c_w_post, c'') \<in> (ktm_step (ar_delta_write M)) ^^ m_w)"
      by (intro exI[where x = c_b] exI[where x = c'] exI[where x = m_w]
                exI[where x = 0] conjI wb chain_w c'_compute
                exI[where x = c''] step_compute empty_w)
  qed
qed

lemma ar_walker_step_from_in_write:
  fixes M :: "('q, 'a) ktm"
    and cM :: "('a, 'q) ktc_config"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes inv: "ar_walker_in_write M cM c'"
      and step: "(c', c'') \<in> ktm_step (alphabet_reduce_delta M)"
  shows "ar_walker_in_write M cM c'' \<or> ar_walker_in_advance M cM c''"
proof -
  have src: "fst (snd (ktc_state c')) = AR_SimWrite"
    using inv unfolding ar_walker_in_write_def by simp
  obtain c_b c_w m_r m_w where
      wb:   "ar_walker_at_boundary M cM c_b"
    and chr:  "(c_b, c_w) \<in> (ktm_step (ar_delta_read M)) ^^ m_r"
    and cwC:  "fst (snd (ktc_state c_w)) = AR_SimCompute"
    and rest: "\<exists>c_w_post. (c_w, c_w_post) \<in> ktm_step (ar_delta_compute M)
                          \<and> (c_w_post, c') \<in> (ktm_step (ar_delta_write M)) ^^ m_w"
    using inv unfolding ar_walker_in_write_def by blast
  obtain c_w_post where
      ccs: "(c_w, c_w_post) \<in> ktm_step (ar_delta_compute M)"
    and chw: "(c_w_post, c') \<in> (ktm_step (ar_delta_write M)) ^^ m_w"
    using rest by blast
  have step_write: "(c', c'') \<in> ktm_step (ar_delta_write M)"
    using ar_step_write_lift[OF src step] .
  have chw_ext: "(c_w_post, c'') \<in> (ktm_step (ar_delta_write M)) ^^ Suc m_w"
    using chw step_write by (rule relpow_Suc_I)
  from ar_step_from_SimWrite_lands[OF step src]
  have dest: "fst (snd (ktc_state c'')) = AR_SimWrite
            \<or> fst (snd (ktc_state c'')) = AR_SimAdvance" .
  thus ?thesis
  proof
    assume dw: "fst (snd (ktc_state c'')) = AR_SimWrite"
    have "ar_walker_in_write M cM c''"
      unfolding ar_walker_in_write_def
    proof (intro conjI)
      show "fst (snd (ktc_state c'')) = AR_SimWrite" by (rule dw)
      show "\<exists>c_b c_w m_r m_w.
              ar_walker_at_boundary M cM c_b
              \<and> (c_b, c_w) \<in> (ktm_step (ar_delta_read M)) ^^ m_r
              \<and> fst (snd (ktc_state c_w)) = AR_SimCompute
              \<and> (\<exists>c_w_post.
                   (c_w, c_w_post) \<in> ktm_step (ar_delta_compute M)
                 \<and> (c_w_post, c'') \<in> (ktm_step (ar_delta_write M)) ^^ m_w)"
        by (intro exI[where x = c_b] exI[where x = c_w] exI[where x = m_r]
                  exI[where x = "Suc m_w"] conjI wb chr cwC
                  exI[where x = c_w_post] ccs chw_ext)
    qed
    thus ?thesis ..
  next
    assume da: "fst (snd (ktc_state c'')) = AR_SimAdvance"
    \<comment> \<open>Cycle transition write to advance: \<open>c''\<close> opens the
        advance phase with zero advance-steps elapsed.\<close>
    have empty_a: "(c'', c'') \<in> (ktm_step (ar_delta_advance M)) ^^ 0"
      by simp
    have "ar_walker_in_advance M cM c''"
      unfolding ar_walker_in_advance_def
    proof (intro conjI)
      show "fst (snd (ktc_state c'')) = AR_SimAdvance" by (rule da)
      show "\<exists>c_b c_w c_a m_r m_w m_a.
              ar_walker_at_boundary M cM c_b
              \<and> (c_b, c_w) \<in> (ktm_step (ar_delta_read M)) ^^ m_r
              \<and> fst (snd (ktc_state c_w)) = AR_SimCompute
              \<and> fst (snd (ktc_state c_a)) = AR_SimAdvance
              \<and> (\<exists>c_w_post.
                   (c_w, c_w_post) \<in> ktm_step (ar_delta_compute M)
                 \<and> (c_w_post, c_a) \<in> (ktm_step (ar_delta_write M)) ^^ m_w
                 \<and> (c_a, c'') \<in> (ktm_step (ar_delta_advance M)) ^^ m_a)"
        by (intro exI[where x = c_b] exI[where x = c_w] exI[where x = c'']
                  exI[where x = m_r] exI[where x = "Suc m_w"] exI[where x = 0]
                  conjI wb chr cwC da
                  exI[where x = c_w_post] ccs chw_ext empty_a)
    qed
    thus ?thesis ..
  qed
qed

lemma ar_walker_step_from_in_advance:
  fixes M :: "('q, 'a) ktm"
    and cM :: "('a, 'q) ktc_config"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes inv: "ar_walker_in_advance M cM c'"
      and step: "(c', c'') \<in> ktm_step (alphabet_reduce_delta M)"
  shows "ar_walker_in_advance M cM c'' \<or> ar_walker_at_next M cM c''"
proof -
  have src: "fst (snd (ktc_state c')) = AR_SimAdvance"
    using inv unfolding ar_walker_in_advance_def by simp
  obtain c_b c_w c_a m_r m_w m_a where
      wb:   "ar_walker_at_boundary M cM c_b"
    and chr:  "(c_b, c_w) \<in> (ktm_step (ar_delta_read M)) ^^ m_r"
    and cwC:  "fst (snd (ktc_state c_w)) = AR_SimCompute"
    and caC:  "fst (snd (ktc_state c_a)) = AR_SimAdvance"
    and rest: "\<exists>c_w_post.
                  (c_w, c_w_post) \<in> ktm_step (ar_delta_compute M)
                \<and> (c_w_post, c_a) \<in> (ktm_step (ar_delta_write M)) ^^ m_w
                \<and> (c_a, c') \<in> (ktm_step (ar_delta_advance M)) ^^ m_a"
    using inv unfolding ar_walker_in_advance_def by blast
  obtain c_w_post where
      ccs: "(c_w, c_w_post) \<in> ktm_step (ar_delta_compute M)"
    and chw: "(c_w_post, c_a) \<in> (ktm_step (ar_delta_write M)) ^^ m_w"
    and cha: "(c_a, c') \<in> (ktm_step (ar_delta_advance M)) ^^ m_a"
    using rest by blast
  have step_advance: "(c', c'') \<in> ktm_step (ar_delta_advance M)"
    using ar_step_advance_lift[OF src step] .
  have cha_ext: "(c_a, c'') \<in> (ktm_step (ar_delta_advance M)) ^^ Suc m_a"
    using cha step_advance by (rule relpow_Suc_I)
  from ar_step_from_SimAdvance_lands[OF step src]
  have dest: "fst (snd (ktc_state c'')) = AR_SimAdvance
            \<or> fst (snd (ktc_state c'')) = AR_SimNext" .
  thus ?thesis
  proof
    assume da: "fst (snd (ktc_state c'')) = AR_SimAdvance"
    have "ar_walker_in_advance M cM c''"
      unfolding ar_walker_in_advance_def
    proof (intro conjI)
      show "fst (snd (ktc_state c'')) = AR_SimAdvance" by (rule da)
      show "\<exists>c_b c_w c_a m_r m_w m_a.
              ar_walker_at_boundary M cM c_b
              \<and> (c_b, c_w) \<in> (ktm_step (ar_delta_read M)) ^^ m_r
              \<and> fst (snd (ktc_state c_w)) = AR_SimCompute
              \<and> fst (snd (ktc_state c_a)) = AR_SimAdvance
              \<and> (\<exists>c_w_post.
                   (c_w, c_w_post) \<in> ktm_step (ar_delta_compute M)
                 \<and> (c_w_post, c_a) \<in> (ktm_step (ar_delta_write M)) ^^ m_w
                 \<and> (c_a, c'') \<in> (ktm_step (ar_delta_advance M)) ^^ m_a)"
        by (intro exI[where x = c_b] exI[where x = c_w] exI[where x = c_a]
                  exI[where x = m_r] exI[where x = m_w] exI[where x = "Suc m_a"]
                  conjI wb chr cwC caC
                  exI[where x = c_w_post] ccs chw cha_ext)
    qed
    thus ?thesis ..
  next
    assume dn: "fst (snd (ktc_state c'')) = AR_SimNext"
    \<comment> \<open>Cycle transition advance to next: extended advance chain
        lands at \<open>c''\<close>, the redundant \<open>c_n = c'\<close> conjunct
        instantiates with \<open>c_n = c''\<close>.\<close>
    have "ar_walker_at_next M cM c''"
      unfolding ar_walker_at_next_def
    proof (intro conjI)
      show "fst (snd (ktc_state c'')) = AR_SimNext" by (rule dn)
      show "\<exists>c_b c_w c_a c_n m_r m_w m_a.
              ar_walker_at_boundary M cM c_b
              \<and> (c_b, c_w) \<in> (ktm_step (ar_delta_read M)) ^^ m_r
              \<and> fst (snd (ktc_state c_w)) = AR_SimCompute
              \<and> fst (snd (ktc_state c_a)) = AR_SimAdvance
              \<and> (\<exists>c_w_post.
                   (c_w, c_w_post) \<in> ktm_step (ar_delta_compute M)
                 \<and> (c_w_post, c_a) \<in> (ktm_step (ar_delta_write M)) ^^ m_w
                 \<and> (c_a, c_n) \<in> (ktm_step (ar_delta_advance M)) ^^ m_a
                 \<and> c_n = c'')"
        by (intro exI[where x = c_b] exI[where x = c_w] exI[where x = c_a]
                  exI[where x = c''] exI[where x = m_r] exI[where x = m_w]
                  exI[where x = "Suc m_a"] conjI wb chr cwC caC
                  exI[where x = c_w_post] ccs chw cha_ext refl)
    qed
    thus ?thesis ..
  qed
qed

text \<open>The sixth and last of the preservation lemmas: an \<open>M'\<close>-step out
  of \<open>AR_SimNext\<close> leads to \<open>AR_SimRead\<close> (closing the cycle),
  \<open>AR_HaltAccept\<close>, or \<open>AR_HaltReject\<close>, by
  \<open>ar_step_from_SimNext_lands\<close>.  It only sorts the cases.
  Establishing the invariant for the reconstructed \<open>M\<close>-successor when
  a cycle closes is done once per cycle, by \<open>ar_walker_cycle_close\<close>
  and the chunked reverse induction, and the proof goes through that
  lemma directly; this one is not used below, and is stated so that all
  six substeps have their one-step lemma.\<close>

lemma ar_walker_step_from_at_next:
  fixes M :: "('q, 'a) ktm"
    and cM :: "('a, 'q) ktc_config"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes inv: "ar_walker_at_next M cM c'"
      and step: "(c', c'') \<in> ktm_step (alphabet_reduce_delta M)"
  shows "fst (snd (ktc_state c'')) = AR_SimRead
       \<or> fst (snd (ktc_state c'')) = AR_HaltAccept
       \<or> fst (snd (ktc_state c'')) = AR_HaltReject"
proof -
  have src: "fst (snd (ktc_state c')) = AR_SimNext"
    using inv unfolding ar_walker_at_next_def by simp
  show ?thesis using ar_step_from_SimNext_lands[OF step src] .
qed

subsection \<open>Closing a simulation cycle\<close>

text \<open>An \<open>AR_SimNext\<close> step closes a simulation cycle: the walker is
  re-established at a boundary for the next \<open>M\<close>-configuration.  The
  successor is \<^emph>\<open>reconstructed\<close> from the pinned compute branch
  (the \<open>\<exists>cM'\<close> in the conclusion): under nondeterministic
  \<open>delta_ktm M\<close> the source \<open>cM\<close> may have several successors, so the
  fired branch is recovered from the walker's own witness chain rather
  than assumed.  The forward phase lemmas run in the full relation and
  in the substep sub-relation at once, so the forward direction is read in the
  sub-relations and each walker
  witness chain is pinned by a \<open>chain_ar_delta_X_to_Y_uniq\<close> suite.

  The closing next step is inverted by \<open>ar_next_step_inv\<close>, which
  dispatches on the reconstructed \<open>M\<close>-state \<open>q'\<close> into three
  outcomes: continue (\<open>q' \<notin> {t, r}\<close>, landing at \<open>AR_SimRead\<close>),
  accept (\<open>q' = t_ktm M\<close>) or reject (\<open>q' = r_ktm M\<close>).  All three
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
  fixes M :: "('q, 'a) ktm"
    and w :: "'a list"
    and cM :: "('a, 'q) ktc_config"
    and c' c'' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes inv: "ar_walker_at_next M cM c'"
      and step: "(c', c'') \<in> ktm_step (alphabet_reduce_delta M)"
      and vM: "valid_ktm M"
      and qQ: "ktc_state cM \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and tapeG: "\<And>k. ktc_tape cM k (ktc_pos cM k) \<in> \<Gamma>_ktm M"
      and w_sub: "set w \<subseteq> Sigma_ktm M"
      and reach_M: "(init_config_ktm M w, cM) \<in> (ktm_step (delta_ktm M))\<^sup>*"
      and lebl: "le_ktm M \<noteq> bl_ktm M"
  shows "\<exists>cM'. (cM, cM') \<in> ktm_step (delta_ktm M)
               \<and> ar_walker_at_boundary M cM' c''"
proof -
  let ?k = "block_width (\<Gamma>_ktm M)"
  let ?aM = "\<lambda>k. ktc_tape cM k (ktc_pos cM k)"
  have kpos_ktm: "0 < k_ktm M" using vM by (cases M) auto
  \<comment> \<open>Unpack the \<open>ar_walker_at_next\<close> witness.\<close>
  obtain c_b c_w c_a c_n m_r m_w m_a c_w_post where
      wb: "ar_walker_at_boundary M cM c_b"
    and chain_r: "(c_b, c_w) \<in> (ktm_step (ar_delta_read M)) ^^ m_r"
    and cw_cpu: "fst (snd (ktc_state c_w)) = AR_SimCompute"
    and ca_adv: "fst (snd (ktc_state c_a)) = AR_SimAdvance"
    and cstep: "(c_w, c_w_post) \<in> ktm_step (ar_delta_compute M)"
    and wchain: "(c_w_post, c_a) \<in> (ktm_step (ar_delta_write M)) ^^ m_w"
    and achain0: "(c_a, c_n) \<in> (ktm_step (ar_delta_advance M)) ^^ m_a"
    and cn_eq: "c_n = c'"
    using inv unfolding ar_walker_at_next_def by blast
  have achain: "(c_a, c') \<in> (ktm_step (ar_delta_advance M)) ^^ m_a"
    using achain0 cn_eq by simp
  have c'_next: "fst (snd (ktc_state c')) = AR_SimNext"
    using inv unfolding ar_walker_at_next_def by simp
  have sim: "ar_simulates M cM c_b"
    using wb unfolding ar_walker_at_boundary_def by simp
  have pcons: "ar_posk_consistent M cM c_b"
    using wb unfolding ar_walker_at_boundary_def by simp
  have rbnd: "ar_at_read_boundary M c_b"
    using wb unfolding ar_walker_at_boundary_def by simp
  have cb_idx: "fst (snd (ktc_state c_b)) = AR_SimRead"
  proof (cases m_r)
    case 0
    have cb_eq: "c_b = c_w" using chain_r 0 by simp
    have cb_compute: "fst (snd (ktc_state c_b)) = AR_SimCompute"
      using cw_cpu cb_eq by simp
    obtain qM' stg where st_b: "ktc_state c_b = (qM', stg)"
      by (cases "ktc_state c_b") auto
    obtain idx tk i buf dvec posk where
        sg_b: "stg = (idx, tk, i, buf, dvec, posk)" by (cases stg) auto
    have idx_cpu: "idx = AR_SimCompute" using cb_compute st_b sg_b by simp
    have "(idx = AR_SimRead \<and> qM' \<notin> {t_ktm M, r_ktm M})
            \<or> (qM' = t_ktm M \<and> stg = ar_accept_stage (bl_ktm M))
            \<or> (qM' = r_ktm M \<and> stg = ar_reject_stage (bl_ktm M))"
      using sim st_b sg_b unfolding ar_simulates_def by (auto split: prod.splits)
    hence False using idx_cpu sg_b
      by (auto simp: ar_accept_stage_def ar_reject_stage_def)
    thus ?thesis ..
  next
    case (Suc m')
    have hsuc: "(c_b, c_w) \<in> (ktm_step (ar_delta_read M)) ^^ Suc m'"
      using chain_r Suc by simp
    obtain c_1 where first: "(c_b, c_1) \<in> ktm_step (ar_delta_read M)"
      using relpow_Suc_D2[OF hsuc] by blast
    from first obtain S ts n S' aw move where
        ceq: "c_b = KConfig S ts n"
      and rel: "(S, (\<lambda>k. ts k (n k)), S', aw, move) \<in> ar_delta_read M"
      by (auto elim: ktm_step.cases)
    have "fst (snd S) = AR_SimRead" using ar_delta_read_src[OF rel] .
    thus ?thesis using ceq by simp
  qed
  obtain qM' stg where st_b: "ktc_state c_b = (qM', stg)"
    by (cases "ktc_state c_b") auto
  obtain idx tk i buf dvec posk where
      sg_b: "stg = (idx, tk, i, buf, dvec, posk)" by (cases stg) auto
  have idx_read: "idx = AR_SimRead" using cb_idx st_b sg_b by simp
  have qM'_eq: "qM' = ktc_state cM"
    using sim st_b sg_b unfolding ar_simulates_def by (auto split: prod.splits)
  have tcorr: "\<forall>k < k_ktm M. ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                       (ktc_tape cM k) (ktc_tape c_b k)"
    using sim st_b sg_b unfolding ar_simulates_def by (auto split: prod.splits)
  have ppos: "\<And>k. ktc_pos c_b k = sim_pos ?k (ktc_pos cM k)"
    using sim st_b sg_b idx_read
    unfolding ar_simulates_def by (auto split: prod.splits)
  have pkok: "\<And>k. posk k = AR_AtLE \<longleftrightarrow> ktc_pos cM k = 0"
    using pcons st_b sg_b idx_read
    unfolding ar_posk_consistent_def by (auto split: prod.splits)
  have bnd_unfold: "idx = AR_SimRead
        \<longrightarrow> (tk = 0 \<and> i = 0
             \<and> (\<forall>k. buf k \<in> \<Gamma>_ktm M \<union> {bl_ktm M})
             \<and> ar_stage_bounded (bl_ktm M) (k_ktm M)
                  (idx, tk, i, buf, dvec, posk))"
    using rbnd st_b sg_b
    unfolding ar_at_read_boundary_def by (auto split: prod.splits)
  have tk0: "tk = 0" and i0: "i = 0"
    and bufG: "\<And>k. buf k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
    using bnd_unfold idx_read by simp_all
  have src_b: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                 (AR_SimRead, 0, 0, buf, dvec, posk)"
    using bnd_unfold idx_read tk0 i0 by simp
  have pad_b: "\<forall>j \<ge> k_ktm M. ktc_tape c_b j (ktc_pos c_b j) = BLANK4"
    using rbnd unfolding ar_at_read_boundary_def by (auto split: prod.splits)
  have stg0: "ktc_state c_b = (ktc_state cM, AR_SimRead, 0, 0, buf, dvec, posk)"
    using st_b sg_b qM'_eq idx_read tk0 i0 by simp
  have buf_tail: "\<forall>j \<ge> k_ktm M. buf j = bl_ktm M"
    using src_b by (simp add: ar_stage_bounded_def)
  have posk_tail: "\<forall>j \<ge> k_ktm M. posk j = AR_AtLE"
    using src_b by (simp add: ar_stage_bounded_def)
  have valcM: "valid_config_ktm M cM"
    using valid_reach_ktm[OF vM w_sub reach_M] .
  have aM_tail: "\<forall>j \<ge> k_ktm M. ktc_tape cM j (ktc_pos cM j) = bl_ktm M"
    using valid_config_ktm_blank_tail[OF valcM] by blast
  \<comment> \<open>Read-pin: reconstruct the canonical compute config (guarded read
     buffer / posk / position), pin the walker's read chain to it.\<close>
  let ?rbuf = "\<lambda>k. if k < k_ktm M then ?aM k else buf k"
  let ?rposk = "\<lambda>k. if k < k_ktm M
                     then (if ktc_pos cM k = 0 then AR_AtLE
                           else if ktc_pos cM k = 1 then AR_AtFirstProper
                           else AR_AtFurtherProper)
                     else posk k"
  let ?rpos = "\<lambda>k. if k < k_ktm M
                    then (if ktc_pos cM k = 0 then Suc 0
                          else sim_pos ?k (ktc_pos cM k) + ?k)
                    else ktc_pos c_b k"
  obtain c_r m_phase where
      r_chain: "(c_b, c_r) \<in> (ktm_step (ar_delta_read M)) ^^ m_phase"
    and r_state: "ktc_state c_r = (ktc_state cM, AR_SimCompute, k_unidx 0, 0,
                    ?rbuf, dvec, ?rposk)"
    and r_tape: "ktc_tape c_r = ktc_tape c_b"
    and r_pos: "ktc_pos c_r = ?rpos"
    using ar_read_phase[OF vM qQ kge2 stg0 tcorr ppos pkok tapeG bufG
                           pad_b src_b] ktm_run_mono [OF Int_lower2]
    by blast
  have r_cpu: "fst (snd (ktc_state c_r)) = AR_SimCompute" using r_state by simp
  have cw_eq_cr: "c_w = c_r"
    using chain_ar_delta_read_to_SimCompute_uniq[OF chain_r r_chain cw_cpu r_cpu]
    by simp
  have cw_state: "ktc_state c_w = (ktc_state cM, AR_SimCompute, k_unidx 0, 0,
                    ?rbuf, dvec, ?rposk)"
    using cw_eq_cr r_state by simp
  \<comment> \<open>Invert the compute step: the explicit post-state and the fired
     \<open>delta_ktm M\<close> branch (on the guarded read buffer).\<close>
  obtain q' m_a' m_d where
      mdelta: "(ktc_state cM, ?rbuf, q', m_a', m_d) \<in> delta_ktm M"
    and cwpost_state: "ktc_state c_w_post = (q', AR_SimWrite, 0, 0, m_a', m_d, ?rposk)"
    and cwpost_tape: "ktc_tape c_w_post = ktc_tape c_w"
    and cwpost_pos: "ktc_pos c_w_post = ktc_pos c_w"
    using ar_compute_step_inv_sub[OF cstep cw_state] by blast
  obtain qM tsM nM where cM_eq: "cM = KConfig qM tsM nM" by (cases cM) auto
  have qM_eq: "qM = ktc_state cM" using cM_eq by simp
  have aM_eq: "(\<lambda>k. tsM k (nM k)) = ?aM" using cM_eq by simp
  have rbuf_eq: "?rbuf = ?aM"
  proof (rule ext)
    fix k show "?rbuf k = ?aM k"
    proof (cases "k < k_ktm M")
      case True thus ?thesis by simp
    next
      case False
      have "?rbuf k = bl_ktm M" using buf_tail False by simp
      moreover have "?aM k = bl_ktm M" using aM_tail False by simp
      ultimately show ?thesis by simp
    qed
  qed
  have mdelta_aM: "(ktc_state cM, ?aM, q', m_a', m_d) \<in> delta_ktm M"
    using mdelta rbuf_eq by simp
  define cMn where cMn_def: "cMn = KConfig q' (\<lambda>k. (tsM k)(nM k := m_a' k))
                                              (\<lambda>k. go_move (m_d k) (nM k))"
  have mdelta': "(qM, (\<lambda>k. tsM k (nM k)), q', m_a', m_d) \<in> delta_ktm M"
    using mdelta_aM qM_eq aM_eq by simp
  have m_step: "(cM, cMn) \<in> ktm_step (delta_ktm M)"
    using ktm_step.step[where ts = tsM and n = nM, OF mdelta'] cM_eq cMn_def by simp
  have q'Q: "q' \<in> Q_ktm M" using valid_ktm_delta(3)[OF vM mdelta_aM] .
  have a'G: "m_a' k \<in> \<Gamma>_ktm M" for k using valid_ktm_delta(4)[OF vM mdelta_aM] .
  have a'val: "\<forall>k. m_a' k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}" using a'G by blast
  have dsupp: "\<forall>j \<ge> k_ktm M. m_a' j = bl_ktm M \<and> m_d j = MoveN"
    using valid_ktm_delta_support[OF vM mdelta_aM] by blast
  \<comment> \<open>Write phase: post-write tape / position setup and pad / src for the
     compute-exit config, then pin the walker's write chain.\<close>
  have pad_cwpost: "\<forall>j \<ge> k_ktm M. ktc_tape c_w_post j (ktc_pos c_w_post j) = BLANK4"
  proof (intro allI impI)
    fix j assume jk: "k_ktm M \<le> j"
    have "ktc_pos c_w_post j = ktc_pos c_b j"
      using cwpost_pos cw_eq_cr r_pos jk by simp
    moreover have "ktc_tape c_w_post j = ktc_tape c_b j"
      using cwpost_tape cw_eq_cr r_tape by simp
    ultimately show "ktc_tape c_w_post j (ktc_pos c_w_post j) = BLANK4"
      using pad_b jk by simp
  qed
  have src_cwpost: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                      (AR_SimWrite, 0, 0, m_a', m_d, ?rposk)"
    using kpos_ktm dsupp posk_tail by (simp add: ar_stage_bounded_def)
  have tcorr_w: "\<forall>k < k_ktm M. ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                     (ktc_tape cM k) (ktc_tape c_w_post k)"
  proof (intro allI impI)
    fix k assume kN: "k < k_ktm M"
    have "ktc_tape c_w_post k = ktc_tape c_b k"
      using cwpost_tape cw_eq_cr r_tape by simp
    thus "ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
            (ktc_tape cM k) (ktc_tape c_w_post k)"
      using tcorr kN by simp
  qed
  have ppos_w: "\<forall>k < k_ktm M. ktc_pos c_w_post k = (if ktc_pos cM k = 0 then Suc 0
                   else sim_pos ?k (ktc_pos cM k) + ?k)"
    using cwpost_pos cw_eq_cr r_pos by simp
  have a'le0_w: "\<forall>k < k_ktm M. ktc_pos cM k = 0 \<longrightarrow> m_a' k = le_ktm M"
  proof (intro allI impI)
    fix k assume kN: "k < k_ktm M" and p0: "ktc_pos cM k = 0"
    have tsk0: "tsM k 0 = le_ktm M" using valcM cM_eq kN by (cases M) auto
    have "(\<lambda>j. tsM j (nM j)) k = le_ktm M" using tsk0 p0 cM_eq by simp
    thus "m_a' k = le_ktm M" using valid_ktm_deltaLE[OF vM mdelta'] by simp
  qed
  have poskle_w: "\<forall>k < k_ktm M. ?rposk k = AR_AtLE \<longleftrightarrow> ktc_pos cM k = 0"
    by auto
  obtain c_write mw where
      w_chain: "(c_w_post, c_write) \<in> (ktm_step (ar_delta_write M)) ^^ mw"
    and w_state: "ktc_state c_write = (q', AR_SimAdvance, k_unidx 0, 0, m_a', m_d,
                    ?rposk)"
    and w_tape: "ktc_tape c_write = (\<lambda>k. if k < k_ktm M
          then (if ktc_pos cM k = 0 then ktc_tape c_w_post k
                else (\<lambda>pos. if sim_pos ?k (ktc_pos cM k) \<le> pos
                              \<and> pos < sim_pos ?k (ktc_pos cM k) + ?k
                           then write_bit (\<Gamma>_ktm M) (bl_ktm M) (m_a' k)
                                  (pos - sim_pos ?k (ktc_pos cM k))
                           else ktc_tape c_w_post k pos))
          else ktc_tape c_w_post k)"
    and w_pos: "ktc_pos c_write = ktc_pos c_w_post"
    using ar_write_phase[OF vM q'Q kge2 cwpost_state tcorr_w ppos_w
                            poskle_w a'val pad_cwpost src_cwpost]
          ktm_run_mono [OF Int_lower2]
    by blast
  have c_write_adv: "fst (snd (ktc_state c_write)) = AR_SimAdvance"
    using w_state by simp
  have ca_eq: "c_a = c_write"
    using chain_ar_delta_write_to_SimAdvance_uniq[OF wchain w_chain ca_adv
                                                     c_write_adv]
    by simp
  \<comment> \<open>Advance phase: bridge the tk-field, displacement facts (active
     tapes), pad / src for the write-exit config, then pin.\<close>
  have w_state': "ktc_state c_write = (q', AR_SimAdvance, 0, 0, m_a', m_d, ?rposk)"
    using w_state by (simp add: k_unidx_zero)
  have pad_cwrite: "\<forall>j \<ge> k_ktm M. ktc_tape c_write j (ktc_pos c_write j) = BLANK4"
  proof (intro allI impI)
    fix j assume jk: "k_ktm M \<le> j"
    have "ktc_tape c_write j = ktc_tape c_w_post j" using w_tape jk by simp
    moreover have "ktc_pos c_write j = ktc_pos c_w_post j" using w_pos by simp
    ultimately show "ktc_tape c_write j (ktc_pos c_write j) = BLANK4"
      using pad_cwpost jk by simp
  qed
  have src_cwrite: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                      (AR_SimAdvance, 0, 0, m_a', m_d, ?rposk)"
    using kpos_ktm dsupp posk_tail by (simp add: ar_stage_bounded_def)
  have dge1: "\<forall>k < k_ktm M. m_d k \<noteq> MoveR \<longrightarrow> 0 < ar_disp ?k (m_d k) (?rposk k)"
  proof (intro allI impI)
    fix k assume kN: "k < k_ktm M" and dkR: "m_d k \<noteq> MoveR"
    show "0 < ar_disp ?k (m_d k) (?rposk k)"
    proof (cases "ktc_pos cM k = 0")
      case True
      have nM0: "nM k = 0" using True cM_eq by simp
      have "tsM k 0 = le_ktm M" using valcM cM_eq kN by (cases M) auto
      hence "(\<lambda>j. tsM j (nM j)) k = le_ktm M" using nM0 by simp
      hence "m_d k \<in> {MoveN, MoveR}" using valid_ktm_deltaLE[OF vM mdelta'] by simp
      hence "m_d k = MoveN" using dkR by auto
      moreover have "?rposk k = AR_AtLE" using True kN by simp
      ultimately show "0 < ar_disp ?k (m_d k) (?rposk k)" by simp
    next
      case False
      have dN_or_L: "m_d k = MoveN \<or> m_d k = MoveL"
        using dkR by (cases "m_d k") auto
      have rk: "?rposk k = AR_AtFirstProper \<or> ?rposk k = AR_AtFurtherProper"
        using False kN by auto
      from dN_or_L rk kge2 show "0 < ar_disp ?k (m_d k) (?rposk k)" by auto
    qed
  qed
  have notLE: "\<forall>k < k_ktm M. \<forall>m. m < ar_disp ?k (m_d k) (?rposk k)
                 \<longrightarrow> ktc_tape c_write k (ktc_pos c_write k - m) \<noteq> LE4"
  proof (intro allI impI)
    fix k m assume kN: "k < k_ktm M"
      and mlt: "m < ar_disp ?k (m_d k) (?rposk k)"
    have tcorr_wk: "ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                      (ktc_tape cM k) (ktc_tape c_w_post k)"
      using tcorr_w kN by blast
    have wcpos: "ktc_pos c_write k = (if ktc_pos cM k = 0 then Suc 0
                    else sim_pos ?k (ktc_pos cM k) + ?k)"
      using w_pos ppos_w kN by simp
    have wtape_notLE: "ktc_tape c_write k pos \<noteq> LE4" if pos1: "1 \<le> pos" for pos
    proof (cases "ktc_pos cM k = 0")
      case True
      have "ktc_tape c_write k pos = ktc_tape c_w_post k pos"
        using w_tape True kN by simp
      thus ?thesis
        using ar_tape_correspondence_not_LE4[OF tcorr_wk pos1] by simp
    next
      case False
      have wexp: "ktc_tape c_write k pos
            = (if sim_pos ?k (ktc_pos cM k) \<le> pos
                  \<and> pos < sim_pos ?k (ktc_pos cM k) + ?k
               then write_bit (\<Gamma>_ktm M) (bl_ktm M) (m_a' k)
                      (pos - sim_pos ?k (ktc_pos cM k))
               else ktc_tape c_w_post k pos)"
        using w_tape False kN by simp
      show ?thesis
      proof (cases "sim_pos ?k (ktc_pos cM k) \<le> pos
                      \<and> pos < sim_pos ?k (ktc_pos cM k) + ?k")
        case True
        have b: "pos - sim_pos ?k (ktc_pos cM k) < ?k" using True by linarith
        have "ktc_tape c_write k pos
                = write_bit (\<Gamma>_ktm M) (bl_ktm M) (m_a' k)
                    (pos - sim_pos ?k (ktc_pos cM k))"
          using wexp True by simp
        thus ?thesis using write_bit_not_LE4[OF b] by simp
      next
        case False
        have nreg: "\<not> (sim_pos ?k (ktc_pos cM k) \<le> pos
                        \<and> pos < sim_pos ?k (ktc_pos cM k) + ?k)"
          using False by simp
        have "ktc_tape c_write k pos = ktc_tape c_w_post k pos"
          using wexp by (simp add: if_not_P[OF nreg])
        thus ?thesis
          using ar_tape_correspondence_not_LE4[OF tcorr_wk pos1] by simp
      qed
    qed
    have rge: "ar_disp ?k (m_d k) (?rposk k) \<le> ktc_pos c_write k"
    proof (cases "ktc_pos cM k = 0")
      case True
      have "ar_disp ?k (m_d k) (?rposk k) \<le> Suc 0"
        using True kN by (cases "m_d k") auto
      thus ?thesis using wcpos True by simp
    next
      case nz: False
      show ?thesis
      proof (cases "ktc_pos cM k = 1")
        case True
        have "ar_disp ?k (m_d k) (?rposk k) \<le> Suc ?k"
          using True kN by (cases "m_d k") auto
        thus ?thesis using wcpos True by (simp add: sim_pos_def)
      next
        case False
        have p2: "2 \<le> ktc_pos cM k" using nz False by simp
        have d2: "ar_disp ?k (m_d k) (?rposk k) \<le> 2 * ?k"
          using nz False kN by (cases "m_d k") auto
        have cw_eq2: "ktc_pos c_write k = (ktc_pos cM k - 1) * ?k + 1 + ?k"
          using wcpos nz by (simp add: sim_pos_def)
        have "(1::nat) \<le> ktc_pos cM k - 1" using p2 by simp
        hence "1 * ?k \<le> (ktc_pos cM k - 1) * ?k" by (rule mult_le_mono1)
        hence kk: "?k \<le> (ktc_pos cM k - 1) * ?k" by (simp only: mult_1_left)
        have "2 * ?k \<le> ktc_pos c_write k" using kk cw_eq2 by linarith
        thus ?thesis using d2 by linarith
      qed
    qed
    have "m < ktc_pos c_write k" using mlt rge by simp
    hence "1 \<le> ktc_pos c_write k - m" by simp
    thus "ktc_tape c_write k (ktc_pos c_write k - m) \<noteq> LE4" by (rule wtape_notLE)
  qed
  let ?aposk = "\<lambda>k. if k < k_ktm M then ar_newpos (m_d k) (?rposk k) else ?rposk k"
  let ?apos = "\<lambda>k. if k < k_ktm M
                    then (if m_d k = MoveR then ktc_pos c_write k
                          else ktc_pos c_write k - ar_disp ?k (m_d k) (?rposk k))
                    else ktc_pos c_write k"
  obtain c_adv ma where
      a_chain: "(c_write, c_adv) \<in> (ktm_step (ar_delta_advance M)) ^^ ma"
    and a_state: "ktc_state c_adv = (q', AR_SimNext, k_unidx 0, 0, m_a', m_d, ?aposk)"
    and a_tape: "ktc_tape c_adv = ktc_tape c_write"
    and a_pos: "ktc_pos c_adv = ?apos"
    using ar_advance_phase[OF vM q'Q kge2 w_state' a'val dge1 notLE
                              pad_cwrite src_cwrite] ktm_run_mono [OF Int_lower2]
    by blast
  have c_adv_nxt: "fst (snd (ktc_state c_adv)) = AR_SimNext" using a_state by simp
  have achain': "(c_write, c') \<in> (ktm_step (ar_delta_advance M)) ^^ m_a"
    using achain ca_eq by simp
  have c'_eq: "c' = c_adv"
    using chain_ar_delta_advance_to_SimNext_uniq[OF achain' a_chain c'_next
                                                    c_adv_nxt]
    by simp
  have c'_state: "ktc_state c' = (q', AR_SimNext, k_unidx 0, 0, m_a', m_d, ?aposk)"
    using c'_eq a_state by simp
  \<comment> \<open>Closing next step: invert it; dispatch on the reconstructed
     \<open>M\<close>-state \<open>q'\<close>.\<close>
  have nxt: "ktc_tape c'' = ktc_tape c' \<and> ktc_pos c'' = ktc_pos c'
       \<and> ((q' \<notin> {t_ktm M, r_ktm M}
             \<and> ktc_state c'' = (q', AR_SimRead, 0, 0, m_a', m_d, ?aposk))
          \<or> (q' = t_ktm M
             \<and> ktc_state c'' = (t_ktm M, ar_accept_stage (bl_ktm M)))
          \<or> (q' = r_ktm M
             \<and> ktc_state c'' = (r_ktm M, ar_reject_stage (bl_ktm M))))"
    using ar_next_step_inv[OF step c'_state] .
  have nxt_tape: "ktc_tape c'' = ktc_tape c'" using nxt by simp
  have nxt_pos: "ktc_pos c'' = ktc_pos c'" using nxt by simp
  have nxt_disj:
      "(q' \<notin> {t_ktm M, r_ktm M}
          \<and> ktc_state c'' = (q', AR_SimRead, 0, 0, m_a', m_d, ?aposk))
       \<or> (q' = t_ktm M
          \<and> ktc_state c'' = (t_ktm M, ar_accept_stage (bl_ktm M)))
       \<or> (q' = r_ktm M
          \<and> ktc_state c'' = (r_ktm M, ar_reject_stage (bl_ktm M)))"
    using nxt by simp
  \<comment> \<open>Re-establish the boundary predicates for \<open>cMn\<close> at \<open>c''\<close>.\<close>
  have st_cMn: "ktc_state cMn = q'" using cMn_def by simp
  have padpos0: "\<forall>j \<ge> k_ktm M. ktc_pos cM j = 0" using pkok posk_tail by blast
  have dposL: "m_d k \<noteq> MoveL" if p0: "ktc_pos cM k = 0" and kN: "k < k_ktm M" for k
  proof -
    have nM0: "nM k = 0" using p0 cM_eq by simp
    have "tsM k 0 = le_ktm M" using valcM cM_eq kN by (cases M) auto
    hence "(\<lambda>j. tsM j (nM j)) k = le_ktm M" using nM0 by simp
    hence "m_d k \<in> {MoveN, MoveR}" using valid_ktm_deltaLE[OF vM mdelta'] by simp
    thus "m_d k \<noteq> MoveL" by auto
  qed
  have cwpost_b: "ktc_tape c_w_post = ktc_tape c_b"
    using cwpost_tape cw_eq_cr r_tape by simp
  have cM1tape: "ktc_tape cMn k = (ktc_tape cM k)(ktc_pos cM k := m_a' k)" for k
    using cMn_def cM_eq by simp
  have wt_def: "ktc_tape c'' k pos
        = (if ktc_pos cM k = 0 then ktc_tape c_b k pos
           else if sim_pos ?k (ktc_pos cM k) \<le> pos
                   \<and> pos < sim_pos ?k (ktc_pos cM k) + ?k
                then write_bit (\<Gamma>_ktm M) (bl_ktm M) (m_a' k)
                       (pos - sim_pos ?k (ktc_pos cM k))
                else ktc_tape c_b k pos)" for k pos
  proof (cases "k < k_ktm M")
    case True
    thus ?thesis using nxt_tape c'_eq a_tape w_tape cwpost_b by simp
  next
    case False
    hence kge: "k_ktm M \<le> k" by simp
    have p0: "ktc_pos cM k = 0" using padpos0 kge by blast
    have "ktc_tape c'' k = ktc_tape c_b k"
      using nxt_tape c'_eq a_tape w_tape cwpost_b kge by simp
    thus ?thesis using p0 by simp
  qed
  have tcorr_1: "\<forall>k < k_ktm M. ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                   (ktc_tape cMn k) (ktc_tape c'' k)"
  proof (intro allI impI)
    fix k assume kN: "k < k_ktm M"
    show "ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
            (ktc_tape cMn k) (ktc_tape c'' k)"
      by (rule ar_write_tape_correspondence
                [OF kge2 kN tcorr cM1tape a'le0_w wt_def])
  qed
  have apos_1: "ktc_pos c'' k = sim_pos ?k (ktc_pos cMn k)" for k
  proof (cases "k < k_ktm M")
    case kN: True
    have posM1: "ktc_pos cMn k = go_move (m_d k) (ktc_pos cM k)"
      using cMn_def cM_eq by simp
    have key: "(if m_d k = MoveR
                 then (if ktc_pos cM k = 0 then Suc 0
                       else sim_pos ?k (ktc_pos cM k) + ?k)
                 else (if ktc_pos cM k = 0 then Suc 0
                       else sim_pos ?k (ktc_pos cM k) + ?k)
                        - ar_disp ?k (m_d k)
                            (if ktc_pos cM k = 0 then AR_AtLE
                             else if ktc_pos cM k = 1 then AR_AtFirstProper
                             else AR_AtFurtherProper))
               = sim_pos ?k (go_move (m_d k) (ktc_pos cM k))"
    proof (rule ar_advance_newsimpos)
      show "2 \<le> ?k" by (rule kge2)
      show "ktc_pos cM k = 0 \<Longrightarrow> m_d k \<noteq> MoveL" using dposL kN by blast
    qed
    have cadv_pos: "ktc_pos c'' k = (if m_d k = MoveR
                 then (if ktc_pos cM k = 0 then Suc 0
                       else sim_pos ?k (ktc_pos cM k) + ?k)
                 else (if ktc_pos cM k = 0 then Suc 0
                       else sim_pos ?k (ktc_pos cM k) + ?k)
                        - ar_disp ?k (m_d k)
                            (if ktc_pos cM k = 0 then AR_AtLE
                             else if ktc_pos cM k = 1 then AR_AtFirstProper
                             else AR_AtFurtherProper))"
      using nxt_pos c'_eq a_pos w_pos ppos_w kN by simp
    show ?thesis by (simp add: cadv_pos key posM1)
  next
    case False
    hence kge: "k_ktm M \<le> k" by simp
    have dN: "m_d k = MoveN" using dsupp kge by blast
    have posM1: "ktc_pos cMn k = go_move (m_d k) (ktc_pos cM k)"
      using cMn_def cM_eq by simp
    have "ktc_pos c'' k = ktc_pos c_b k"
      using nxt_pos c'_eq a_pos w_pos cwpost_pos cw_eq_cr r_pos kge by simp
    also have "\<dots> = sim_pos ?k (ktc_pos cM k)" using ppos by simp
    also have "\<dots> = sim_pos ?k (ktc_pos cMn k)" using posM1 dN by simp
    finally show ?thesis .
  qed
  have aposk_1: "?aposk k = AR_AtLE \<longleftrightarrow> ktc_pos cMn k = 0" for k
  proof (cases "k < k_ktm M")
    case kN: True
    have posM1: "ktc_pos cMn k = go_move (m_d k) (ktc_pos cM k)"
      using cMn_def cM_eq by simp
    have key: "(ar_newpos (m_d k)
                  (if ktc_pos cM k = 0 then AR_AtLE
                   else if ktc_pos cM k = 1 then AR_AtFirstProper
                   else AR_AtFurtherProper) = AR_AtLE)
                 \<longleftrightarrow> go_move (m_d k) (ktc_pos cM k) = 0"
    proof (rule ar_newpos_atLE_iff)
      show "ktc_pos cM k = 0 \<Longrightarrow> m_d k \<noteq> MoveL" using dposL kN by blast
    qed
    have aposk_k: "?aposk k = ar_newpos (m_d k)
                     (if ktc_pos cM k = 0 then AR_AtLE
                      else if ktc_pos cM k = 1 then AR_AtFirstProper
                      else AR_AtFurtherProper)"
      using kN by simp
    show ?thesis by (simp add: aposk_k key posM1)
  next
    case False
    hence kge: "k_ktm M \<le> k" by simp
    have dN: "m_d k = MoveN" using dsupp kge by blast
    have p0: "ktc_pos cM k = 0" using padpos0 kge by blast
    have posM1: "ktc_pos cMn k = go_move (m_d k) (ktc_pos cM k)"
      using cMn_def cM_eq by simp
    have "ktc_pos cMn k = 0" using posM1 dN p0 by simp
    moreover have "posk k = AR_AtLE" using posk_tail kge by blast
    moreover have "?aposk k = posk k" using kge by simp
    ultimately show ?thesis by simp
  qed
  have pad_c'': "\<forall>j \<ge> k_ktm M. ktc_tape c'' j (ktc_pos c'' j) = BLANK4"
  proof (intro allI impI)
    fix j assume jk: "k_ktm M \<le> j"
    have "ktc_pos c'' j = ktc_pos c_write j"
      using nxt_pos c'_eq a_pos jk by simp
    moreover have "ktc_tape c'' j = ktc_tape c_write j"
      using nxt_tape c'_eq a_tape by simp
    ultimately show "ktc_tape c'' j (ktc_pos c'' j) = BLANK4"
      using pad_cwrite jk by simp
  qed
  have src_read'': "ar_stage_bounded (bl_ktm M) (k_ktm M)
                      (AR_SimRead, 0, 0, m_a', m_d, ?aposk)"
    using kpos_ktm dsupp posk_tail by (simp add: ar_stage_bounded_def)
  show ?thesis
  proof (intro exI[where x = cMn] conjI)
    show "(cM, cMn) \<in> ktm_step (delta_ktm M)" by (rule m_step)
    show "ar_walker_at_boundary M cMn c''"
    proof -
      consider
          (cont) "q' \<notin> {t_ktm M, r_ktm M}"
                 "ktc_state c'' = (q', AR_SimRead, 0, 0, m_a', m_d, ?aposk)"
        | (acc)  "q' = t_ktm M"
                 "ktc_state c'' = (t_ktm M, ar_accept_stage (bl_ktm M))"
        | (rej)  "q' = r_ktm M"
                 "ktc_state c'' = (r_ktm M, ar_reject_stage (bl_ktm M))"
        using nxt_disj by blast
      thus ?thesis
      proof cases
        case cont
        have notT: "q' \<noteq> t_ktm M" using cont(1) by simp
        have notR: "q' \<noteq> r_ktm M" using cont(1) by simp
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

subsection \<open>The reverse simulation, one cycle at a time\<close>

text \<open>The reverse-direction loop invariant: the substep-walker is in
  \<^emph>\<open>some\<close> stage of the cycle.  Six disjuncts, one per walker
  predicate.  This is the AR analogue of
  carrying \<open>ae_simulates\<close> across AE's reverse induction, but
  stage-granular: where AE peels a whole fixed-length cycle per
  \<open>ae_backward_stage\<close>, AR peels one \<open>M'\<close>-substep and dispatches on
  the current substep tag, because here the length of a cycle depends on
  the data.\<close>

definition ar_walker ::
  "('q, 'a) ktm
    \<Rightarrow> ('a, 'q) ktc_config
    \<Rightarrow> (sym4, 'q \<times> 'a ar_stage) ktc_config \<Rightarrow> bool" where
  "ar_walker M cM c' \<longleftrightarrow>
     ar_walker_at_boundary M cM c'
   \<or> ar_walker_in_read M cM c'
   \<or> ar_walker_at_compute M cM c'
   \<or> ar_walker_in_write M cM c'
   \<or> ar_walker_in_advance M cM c'
   \<or> ar_walker_at_next M cM c'"

text \<open>Chunked-induction engine for the reverse direction, the AR analogue of
  AE's \<open>ae_simulation_phase_chunked_reverse\<close>.  Given a finite
  \<open>M'\<close>-trace \<open>(c', c_acc)\<close> of length \<open>m\<close> ending in the canonical
  accept config \<open>(t_ktm M, ar_accept_stage (bl_ktm M))\<close> and the walker
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
    \<open>ar_simulates_accept_iff\<close> forces \<open>ktc_state cM = t_ktm M\<close>;
  \<^item> a boundary at the reject config is impossible — the trace runs to
    the accept config, but reject is terminal (\<open>ar_reject_terminal\<close>)
    and the reject config is not the accept config.

  The conclusion is in \<open>rtrancl\<close> form for the downstream
  \<open>Lang_ktm\<close>-repacking in \<open>alphabet_reduce_language\<close>.\<close>

lemma ar_simulation_phase_chunked_reverse:
  fixes M :: "('q, 'a) ktm"
    and w :: "'a list"
    and cM :: "('a, 'q) ktc_config"
    and c' c_acc :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
    and m :: nat
  assumes vM:      "valid_ktm M"
      and w_sub:   "set w \<subseteq> Sigma_ktm M"
      and card_ge: "card (\<Gamma>_ktm M) \<ge> 4"
      and lebl:    "le_ktm M \<noteq> bl_ktm M"
      and reach_M: "(init_config_ktm M w, cM) \<in> (ktm_step (delta_ktm M))\<^sup>*"
      and trace:   "(c', c_acc) \<in> (ktm_step (alphabet_reduce_delta M)) ^^ m"
      and accept:  "ktc_state c_acc = (t_ktm M, ar_accept_stage (bl_ktm M))"
      and walk:    "ar_walker M cM c'"
  shows "\<exists>cM_final. (cM, cM_final) \<in> (ktm_step (delta_ktm M))\<^sup>*
                    \<and> ktc_state cM_final = t_ktm M"
  using reach_M trace walk
proof (induction m arbitrary: cM c' rule: less_induct)
  case (less m)
  let ?R = "ktm_step (alphabet_reduce_delta M)"
  \<comment> \<open>Encoding width \<open>\<ge> 2\<close> from \<open>card \<Gamma>_M \<ge> 4\<close>, and the
     reachable-config invariants \<open>cM\<close> needs for the substep lemmas.\<close>
  have kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
  proof -
    have "(2::nat) ^ 2 \<le> 2 ^ block_width (\<Gamma>_ktm M)"
      using card_ge card_le_two_pow_block_width[of "\<Gamma>_ktm M"] by simp
    thus "2 \<le> block_width (\<Gamma>_ktm M)"
      using power_le_imp_le_exp[of "2::nat" 2 "block_width (\<Gamma>_ktm M)"] by simp
  qed
  have valcM: "valid_config_ktm M cM"
    by (rule valid_reach_ktm[OF vM w_sub less.prems(1)])
  have qQ: "ktc_state cM \<in> Q_ktm M" using valcM by (cases M; cases cM) auto
  have tapeG: "ktc_tape cM k (ktc_pos cM k) \<in> \<Gamma>_ktm M" for k
  proof -
    have "range (ktc_tape cM k) \<subseteq> \<Gamma>_ktm M"
      using valcM by (cases M; cases cM) auto
    thus ?thesis by blast
  qed
  have acc_idx: "fst (snd (ktc_state c_acc)) = AR_HaltAccept"
    using accept by (simp add: ar_accept_stage_def)
  \<comment> \<open>An active config (substep tag \<open>\<noteq> AR_HaltAccept\<close>) cannot be
     \<open>c_acc\<close>, so the trace has a first step to peel.\<close>
  have peel: "\<exists>m' c'_1. m = Suc m'
                \<and> (c', c'_1) \<in> ?R \<and> (c'_1, c_acc) \<in> ?R ^^ m'"
    if notHA: "fst (snd (ktc_state c')) \<noteq> AR_HaltAccept"
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
    obtain qM0 stg where st: "ktc_state c' = (qM0, stg)"
      by (cases "ktc_state c'") auto
    obtain idx tk i buf dvec posk where
        sg: "stg = (idx, tk, i, buf, dvec, posk)" by (cases stg) auto
    have state_disj:
        "(idx = AR_SimRead \<and> qM0 \<notin> {t_ktm M, r_ktm M})
           \<or> (qM0 = t_ktm M \<and> stg = ar_accept_stage (bl_ktm M))
           \<or> (qM0 = r_ktm M \<and> stg = ar_reject_stage (bl_ktm M))"
      using sim st sg unfolding ar_simulates_def by (auto split: prod.splits)
    consider (active) "idx = AR_SimRead"
           | (acc)    "stg = ar_accept_stage (bl_ktm M)" "qM0 = t_ktm M"
           | (rej)    "stg = ar_reject_stage (bl_ktm M)" "qM0 = r_ktm M"
      using state_disj by blast
    thus ?thesis
    proof cases
      case active
      have neq: "fst (snd (ktc_state c')) \<noteq> AR_HaltAccept"
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
      have c'_acc: "ktc_state c' = (t_ktm M, ar_accept_stage (bl_ktm M))"
        using st sg acc by simp
      have cM_t: "ktc_state cM = t_ktm M"
        using ar_simulates_accept_iff[OF vM sim] c'_acc by simp
      have "(cM, cM) \<in> (ktm_step (delta_ktm M))\<^sup>*" by simp
      thus ?thesis using cM_t by blast
    next
      case rej
      have c'_rej: "ktc_state c' = (r_ktm M, ar_reject_stage (bl_ktm M))"
        using st sg rej by simp
      show ?thesis
      proof (cases m)
        case 0
        have ceq: "c' = c_acc" using less.prems(2) 0 by simp
        have "fst (snd (ktc_state c')) = AR_HaltReject"
          using c'_rej by (simp add: ar_reject_stage_def)
        moreover have "fst (snd (ktc_state c')) = AR_HaltAccept"
          using ceq accept by (simp add: ar_accept_stage_def)
        ultimately show ?thesis by simp
      next
        case (Suc m')
        have "(c', c_acc) \<in> ?R ^^ Suc m'" using less.prems(2) Suc by simp
        from relpow_Suc_D2[OF this] obtain c'_1 where
            fst_step: "(c', c'_1) \<in> ?R" by blast
        have "ktc_state c' \<noteq> (r_ktm M, ar_reject_stage (bl_ktm M))"
          by (rule ar_reject_terminal[OF vM card_ge fst_step])
        thus ?thesis using c'_rej by simp
      qed
    qed
  next
    case rd
    have neq: "fst (snd (ktc_state c')) \<noteq> AR_HaltAccept"
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
    have neq: "fst (snd (ktc_state c')) \<noteq> AR_HaltAccept"
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
    have neq: "fst (snd (ktc_state c')) \<noteq> AR_HaltAccept"
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
    have neq: "fst (snd (ktc_state c')) \<noteq> AR_HaltAccept"
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
    have neq: "fst (snd (ktc_state c')) \<noteq> AR_HaltAccept"
      using nx unfolding ar_walker_at_next_def by simp
    obtain m' c'_1 where mSuc: "m = Suc m'"
      and fst_step: "(c', c'_1) \<in> ?R"
      and rest: "(c'_1, c_acc) \<in> ?R ^^ m'"
      using peel[OF neq] by blast
    have m'_lt: "m' < m" using mSuc by simp
    obtain cMn where step_cMn: "(cM, cMn) \<in> ktm_step (delta_ktm M)"
      and bnd_1: "ar_walker_at_boundary M cMn c'_1"
      using ar_walker_cycle_close[OF nx fst_step vM qQ kge2 tapeG
                                     w_sub less.prems(1) lebl]
      by blast
    have reach_Mn: "(init_config_ktm M w, cMn) \<in> (ktm_step (delta_ktm M))\<^sup>*"
      using less.prems(1) step_cMn by (rule rtrancl.rtrancl_into_rtrancl)
    have walk_1: "ar_walker M cMn c'_1"
      using bnd_1 unfolding ar_walker_def by blast
    obtain cM_final where
        run_final: "(cMn, cM_final) \<in> (ktm_step (delta_ktm M))\<^sup>*"
      and acc_final: "ktc_state cM_final = t_ktm M"
      using less.IH[OF m'_lt reach_Mn rest walk_1] by blast
    have "(cM, cM_final) \<in> (ktm_step (delta_ktm M))\<^sup>*"
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
  three \<open>_init\<close> invariants).  No \<open>det_ktm\<close> hypothesis is
  required.

  The \<open>set w \<subseteq> Sigma_ktm M\<close> guard is required (and matches
  AE's statement): \<open>Lang_ktm\<close> bakes in the input-alphabet
  restriction, so \<open>w \<in> Lang_ktm M\<close> supplies the guard for
  free in the forward direction, but membership of the encoded word
  in \<open>Lang_ktm M'\<close> says nothing about \<open>w\<close>'s alphabet.  For
  \<open>w\<close> outside the input alphabet the encoded word can still be
  accepted by \<open>M'\<close> while \<open>w \<notin> Lang_ktm M\<close>.\<close>

theorem alphabet_reduce_language:
  fixes M :: "('q, 'a) ktm"
  assumes vM:        "valid_ktm M"
      and s_neq_t:   "s_ktm M \<noteq> t_ktm M"
      and s_neq_r:   "s_ktm M \<noteq> r_ktm M"
      and le_neq_bl: "le_ktm M \<noteq> bl_ktm M"
      and card_ge:   "card (\<Gamma>_ktm M) \<ge> 4"
  shows "\<forall>w. set w \<subseteq> Sigma_ktm M
              \<longrightarrow> (encode_input_ar (\<Gamma>_ktm M) (bl_ktm M) w \<in> Lang_ktm
                      (alphabet_reduce M
                         :: ('q \<times> 'a ar_stage, sym4) ktm))
                  = (w \<in> Lang_ktm M)"
proof -
  let ?M' = "alphabet_reduce M :: ('q \<times> 'a ar_stage, sym4) ktm"
  have fwd: "\<forall>w. set w \<subseteq> Sigma_ktm M
                  \<longrightarrow> w \<in> Lang_ktm M
                  \<longrightarrow> encode_input_ar (\<Gamma>_ktm M) (bl_ktm M) w \<in> Lang_ktm ?M'"
    by (rule alphabet_reduce_language_forward[OF vM s_neq_t s_neq_r le_neq_bl card_ge])
  show ?thesis
  proof (intro allI impI)
    fix w :: "'a list"
    assume w_sub: "set w \<subseteq> Sigma_ktm M"
    let ?enc = "encode_input_ar (\<Gamma>_ktm M) (bl_ktm M) w"
    let ?c'  = "init_config_ktm ?M' ?enc"
    show "(?enc \<in> Lang_ktm ?M') = (w \<in> Lang_ktm M)"
    proof
      assume w_in_M: "w \<in> Lang_ktm M"
      from fwd w_sub w_in_M show "?enc \<in> Lang_ktm ?M'" by blast
    next
      \<comment> \<open>Reverse direction: an accepting \<open>M'\<close>-run on the encoded
          input yields an accepting \<open>M\<close>-run on \<open>w\<close>.  No
          validation prefix to peel, so the accepting trace feeds the
          chunked-reverse engine directly off the initial read-boundary
          correspondence.\<close>
      assume enc_in_M': "?enc \<in> Lang_ktm ?M'"
      \<comment> \<open>Step 1: unpack the \<open>M'\<close>-acceptance into a relpow trace.\<close>
      from enc_in_M' obtain wM' nM' where
          acc_path_M':
            "(?c', KConfig (t_ktm ?M') wM' nM')
                \<in> (ktm_step (delta_ktm ?M'))\<^sup>*"
        unfolding Lang_ktm_def by blast
      have acc_path:
          "(?c', KConfig (t_ktm ?M') wM' nM')
              \<in> (ktm_step (alphabet_reduce_delta M))\<^sup>*"
        using acc_path_M' by simp
      obtain m where trace:
          "(?c', KConfig (t_ktm ?M') wM' nM')
              \<in> (ktm_step (alphabet_reduce_delta M)) ^^ m"
        using acc_path rtrancl_imp_relpow by metis
      \<comment> \<open>Step 2: the accept state in the engine's canonical form.\<close>
      have accept:
          "ktc_state (KConfig (t_ktm ?M') wM' nM')
              = (t_ktm M, ar_accept_stage (bl_ktm M))"
        by simp
      \<comment> \<open>Step 3: the initial read-boundary correspondence is the
          walker's boundary disjunct.\<close>
      have sim:  "ar_simulates M (init_config_ktm M w) ?c'"
        by (rule ar_simulates_init[OF vM w_sub s_neq_t s_neq_r])
      have posk: "ar_posk_consistent M (init_config_ktm M w) ?c'"
        by (rule ar_posk_consistent_init)
      have rbnd: "ar_at_read_boundary M ?c'"
        by (rule ar_at_read_boundary_init[OF vM])
      have walk: "ar_walker M (init_config_ktm M w) ?c'"
        unfolding ar_walker_def ar_walker_at_boundary_def
        using sim posk rbnd by blast
      \<comment> \<open>Step 4: seed with the reflexive reach and run the engine.\<close>
      have reach_refl: "(init_config_ktm M w, init_config_ktm M w)
                          \<in> (ktm_step (delta_ktm M))\<^sup>*" by simp
      obtain cM_final where
          M_path: "(init_config_ktm M w, cM_final)
                      \<in> (ktm_step (delta_ktm M))\<^sup>*"
        and M_acc: "ktc_state cM_final = t_ktm M"
        using ar_simulation_phase_chunked_reverse
                [OF vM w_sub card_ge le_neq_bl reach_refl trace accept walk]
        by blast
      \<comment> \<open>Step 5: repack as \<open>w \<in> Lang_ktm M\<close>.\<close>
      obtain wM_acc nM_acc where
          cM_final_eq: "cM_final = KConfig (t_ktm M) wM_acc nM_acc"
        using M_acc by (cases cM_final) simp
      show "w \<in> Lang_ktm M"
        unfolding Lang_ktm_def
        using w_sub M_path cM_final_eq by blast
    qed
  qed
qed

end
