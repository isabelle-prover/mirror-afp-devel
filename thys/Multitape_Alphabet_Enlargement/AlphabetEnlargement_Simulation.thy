theory AlphabetEnlargement_Simulation
  imports AlphabetEnlargement_Delta
begin

subsection \<open>The combinator\<close>

text \<open>The alphabet-enlargement combinator following Hopcroft--Ullman
  \<^cite>\<open>\<open>Theorem 12.3\<close> in "Hopcroft1979:introduction"\<close>.  Takes a
  substrate machine over alphabet \<open>'a\<close>;
  produces a substrate machine over alphabet
  \<open>'c \<Rightarrow> 'a\<close> (blocks) with state set
  \<open>'q \<times> ('a, 'c) ae_stage\<close>.  Tape count \<open>k_ktm M\<close> is preserved.

  The output machine simulates \<open>M\<close> on the externally encoded
  input via a stage-based simulation: each stage consumes 8
  substeps of \<open>M'\<close> to simulate exactly \<open>c\<close> consecutive steps
  of \<open>M\<close> (pre-fetch home + neighbour blocks in 4 substeps;
  compute next \<open>c\<close> \<open>M\<close>-steps internally; write back up to 3
  modified blocks and reposition heads in 4 substeps).

  Pieces:
  \<^item> \<open>Q'\<close>: \<open>Q_M \<times> UNIV\<close> over \<open>ae_stage\<close>.
  \<^item> \<open>\<Sigma>'\<close>: blocks composed of \<open>\<Sigma>_M \<union> {bl_M}\<close> cells (the
    encoder's image), excluding the all-blank and all-LE blocks.
  \<^item> \<open>\<Gamma>'\<close>: blocks composed of \<open>\<Gamma>_M\<close> cells.
  \<^item> blank: \<open>bl_block bl_M\<close> (the constant blank-block).
  \<^item> LE: \<open>LE_block le_M\<close> (the constant LE-block).
  \<^item> \<open>\<delta>'\<close>: \<open>alphabet_enlarge_delta M\<close> (union of 8 per-substep
    relations; bodies partially filled in this pass).
  \<^item> start: \<open>(s_M, init_stage le_M)\<close>.
  \<^item> accept / reject: \<open>(t_M, init_stage le_M)\<close> /
    \<open>(r_M, init_stage le_M)\<close>; distinguished by the \<open>M\<close>-state
    component, which inherits \<open>t_M \<noteq> r_M\<close> from \<open>M\<close>'s wf.\<close>

definition alphabet_enlarge ::
  "('q, 'a) ktm
    \<Rightarrow> ('q \<times> ('a, ('c :: enum)) ae_stage, 'c \<Rightarrow> 'a) ktm"
  where
    "alphabet_enlarge M =
      (case M of KTM Q_M Sigma_M Gamma_M bl_M le_M _ s_M t_M r_M k_M \<Rightarrow>
         KTM (Q_M \<times> {stg. ae_valid_stage Gamma_M le_M k_M stg})
              (gamma_block (Sigma_M \<union> {bl_M})
                  - {bl_block bl_M, LE_block le_M})
              (gamma_block Gamma_M)
              (bl_block bl_M)
              (LE_block le_M)
              (alphabet_enlarge_delta M)
              (s_M, init_stage le_M)
              (t_M, init_stage le_M)
              (r_M, init_stage le_M)
              k_M)"


subsection \<open>Simulation infrastructure\<close>

text \<open>The two top-level theorems below — \<open>alphabet_enlarge_language\<close>
  and \<open>alphabet_enlarge_time\<close> — both route through a shared
  simulation argument relating \<open>M\<close>'s configurations to
  \<open>M' = alphabet_enlarge M\<close>'s configurations at SS1 stage
  boundaries (or at halt configurations reached via
  SS8\<open>\<rightarrow>\<close>SS1's halt-routing).  The relation \<open>ae_simulates\<close>,
  the per-substep mid-stage invariants \<open>ae_inv_ss1\<close>,
  \<open>\<dots>\<close>, \<open>ae_inv_ss8\<close>, and the lemma roster below
  carry the structure of that argument.\<close>

subsubsection \<open>Positions, the tape correspondence, and the initial configuration\<close>

text \<open>The position-decoding map: given \<open>M'\<close>'s block
  position \<open>s\<close> and a within-block offset \<open>i :: 'c\<close>, return
  the corresponding \<open>M\<close>-tape position.  For \<open>s = 0\<close> the result
  is 0 (the LE position is shared between \<open>M\<close> and \<open>M'\<close>).  For
  \<open>s \<ge> 1\<close>, the block at \<open>s\<close> covers \<open>M\<close>'s positions
  \<open>(s - 1) \<cdot> c + 1\<close> through \<open>(s - 1) \<cdot> c + c\<close> in the order
  determined by the canonical \<open>'c\<close>-enumeration via
  \<open>c_idx\<close>.\<close>

definition ae_decode_pos :: "nat \<Rightarrow> ('c :: enum) \<Rightarrow> nat" where
  "ae_decode_pos s i =
     (if s = 0 then 0
      else (s - 1) * card (UNIV :: 'c set) + c_idx i + 1)"

text \<open>Tape-content correspondence under the encoding: for every
  \<open>M\<close>-tape position \<open>p\<close>, the value at \<open>p\<close> equals the value of
  the corresponding \<open>M'\<close>-block at the corresponding offset.
  Position 0 of \<open>M\<close>'s tape is fixed at \<open>le\<close> (the substrate's
  LE invariant); positions \<open>p \<ge> 1\<close> map bijectively to
  block-and-offset pairs \<open>(s, i)\<close> with \<open>s \<ge> 1\<close> via
  \<open>p = (s - 1) \<cdot> c + c_idx i + 1\<close>.\<close>

definition ae_tape_correspondence ::
  "'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> ('c :: enum \<Rightarrow> 'a)) \<Rightarrow> bool" where
  "ae_tape_correspondence le tM tM' \<longleftrightarrow>
     tM 0 = le \<and>
     (\<forall>s i. s \<ge> 1
              \<longrightarrow> tM ((s - 1) * card (UNIV :: 'c set) + c_idx i + 1)
                  = tM' s i)"

text \<open>Initial configuration of \<open>M' = alphabet_enlarge M\<close> on a
  block input \<open>w :: ('c \<Rightarrow> 'a) list\<close>.  Mirrors the
  substrate's top-level \<open>init_config_ktm\<close> shape, re-stated here
  with the explicit block tape layout the downstream
  simulation lemmas need.  Position 0 holds the LE-block; positions
  \<open>1\<close>\<open>\<dots>\<close>\<open>length w\<close> on tape 0 hold \<open>w\<close>'s blocks; all
  other positions hold the blank-block; all heads at position
  0.\<close>

definition ae_init_config ::
  "('q, 'a) ktm
    \<Rightarrow> (('c :: enum) \<Rightarrow> 'a) list
    \<Rightarrow> ('c \<Rightarrow> 'a, 'q \<times> ('a, 'c) ae_stage) ktc_config" where
  "ae_init_config M w =
     KConfig (s_ktm M, init_stage (le_ktm M))
              (\<lambda>i n. if i < k_ktm M
                     then if n = 0 then LE_block (le_ktm M)
                          else if i = 0 \<and> n \<le> length w
                               then w ! (n - 1)
                               else bl_block (bl_ktm M)
                     else bl_block (bl_ktm M))
              (\<lambda>_. 0)"

text \<open>Bridge: the substrate's \<open>init_config_ktm\<close> of
  \<open>alphabet_enlarge M\<close> on a block input \<open>w\<close> coincides
  with the AE-specific \<open>ae_init_config M w\<close>.  The substrate's
  \<open>init_config_ktm\<close> uses \<open>alphabet_enlarge M\<close>'s field
  projections, which inherit from \<open>M\<close> via the construction
  (start state becomes \<open>(s_ktm M, init_stage (le_ktm M))\<close>;
  blank becomes \<open>bl_block (bl_ktm M)\<close>; LE becomes
  \<open>LE_block (le_ktm M)\<close>).  Used by
  \<open>alphabet_enlarge_language\<close> and \<open>alphabet_enlarge_time\<close>
  to translate the substrate-level \<open>accepts_in_time_ktm\<close>
  conclusion into the AE-side \<open>ae_init_config\<close> form on which the
  validation / simulation chains operate.\<close>

lemma init_config_alphabet_enlarge:
  fixes M :: "('q, 'a) ktm"
    and w :: "('c :: enum \<Rightarrow> 'a) list"
  shows "init_config_ktm
            (alphabet_enlarge M
               :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) ktm) w
          = ae_init_config M w"
proof -
  obtain Q \<Sigma> \<Gamma> bl le \<delta> s t r k where
    M_eq: "M = KTM Q \<Sigma> \<Gamma> bl le \<delta> s t r k"
    by (cases M)
  have s_eq:  "s_ktm M = s"   by (simp only: M_eq s_ktm.simps)
  have le_eq: "le_ktm M = le" by (simp only: M_eq le_ktm.simps)
  have bl_eq: "bl_ktm M = bl" by (simp only: M_eq bl_ktm.simps)
  show ?thesis
    unfolding ae_init_config_def
    unfolding s_eq le_eq bl_eq
    unfolding M_eq alphabet_enlarge_def
    by simp
qed

subsubsection \<open>The components of the enlarged machine\<close>

text \<open>Projection bridges for \<open>alphabet_enlarge M\<close>: the field
  accessors \<open>s_ktm\<close>, \<open>t_ktm\<close>, \<open>r_ktm\<close>, \<open>bl_ktm\<close>, \<open>le_ktm\<close>,
  \<open>delta_ktm\<close> are positional pattern-matches on the
  \<open>KTM\<close> constructor.  Used by \<open>alphabet_enlarge_language\<close>
  and \<open>alphabet_enlarge_time\<close> to translate substrate-level
  field references on \<open>alphabet_enlarge M\<close> into the AE-side
  expressions (the construction's start / accept / reject states
  inherit from \<open>M\<close> with an attached \<open>init_stage le\<close>;
  blank and LE become block-encoded; delta is
  \<open>alphabet_enlarge_delta M\<close>).\<close>

lemma s_ktm_alphabet_enlarge:
  fixes M :: "('q, 'a) ktm"
  shows "s_ktm (alphabet_enlarge M
                  :: ('q \<times> ('a, ('c :: enum)) ae_stage,
                      'c \<Rightarrow> 'a) ktm)
          = (s_ktm M, init_stage (le_ktm M))"
  by (cases M) (simp add: alphabet_enlarge_def)

lemma t_ktm_alphabet_enlarge:
  fixes M :: "('q, 'a) ktm"
  shows "t_ktm (alphabet_enlarge M
                  :: ('q \<times> ('a, ('c :: enum)) ae_stage,
                      'c \<Rightarrow> 'a) ktm)
          = (t_ktm M, init_stage (le_ktm M))"
  by (cases M) (simp add: alphabet_enlarge_def)

lemma r_ktm_alphabet_enlarge:
  fixes M :: "('q, 'a) ktm"
  shows "r_ktm (alphabet_enlarge M
                  :: ('q \<times> ('a, ('c :: enum)) ae_stage,
                      'c \<Rightarrow> 'a) ktm)
          = (r_ktm M, init_stage (le_ktm M))"
  by (cases M) (simp add: alphabet_enlarge_def)

lemma bl_ktm_alphabet_enlarge:
  fixes M :: "('q, 'a) ktm"
  shows "bl_ktm (alphabet_enlarge M
                  :: ('q \<times> ('a, ('c :: enum)) ae_stage,
                      'c \<Rightarrow> 'a) ktm)
          = bl_block (bl_ktm M)"
  by (cases M) (simp add: alphabet_enlarge_def)

lemma le_ktm_alphabet_enlarge:
  fixes M :: "('q, 'a) ktm"
  shows "le_ktm (alphabet_enlarge M
                  :: ('q \<times> ('a, ('c :: enum)) ae_stage,
                      'c \<Rightarrow> 'a) ktm)
          = LE_block (le_ktm M)"
  by (cases M) (simp add: alphabet_enlarge_def)

lemma delta_ktm_alphabet_enlarge:
  fixes M :: "('q, 'a) ktm"
  shows "delta_ktm (alphabet_enlarge M
                     :: ('q \<times> ('a, ('c :: enum)) ae_stage,
                         'c \<Rightarrow> 'a) ktm)
          = alphabet_enlarge_delta M"
  by (cases M) (simp add: alphabet_enlarge_def)

lemma Sigma_ktm_alphabet_enlarge:
  fixes M :: "('q, 'a) ktm"
  shows "Sigma_ktm (alphabet_enlarge M
                     :: ('q \<times> ('a, ('c :: enum)) ae_stage,
                         'c \<Rightarrow> 'a) ktm)
          = gamma_block (Sigma_ktm M \<union> {bl_ktm M})
              - {bl_block (bl_ktm M), LE_block (le_ktm M)}"
  by (cases M) (simp add: alphabet_enlarge_def)

subsubsection \<open>Every cell holds a block of tape symbols\<close>

text \<open>Tape well-formedness invariant on an \<open>M'\<close>-configuration:
  every cell of every tape lies in \<open>gamma_block (\<Gamma>_ktm M)\<close>, and
  every cell of every \<^emph>\<open>inactive\<close> tape (index \<open>\<ge> k_ktm M\<close>)
  holds the blank block \<open>bl_block (bl_ktm M)\<close>.  The blank-tail
  conjunct is the value-level analogue of the substrate's config
  support: with the tape count a runtime \<open>nat\<close>, the inactive tapes
  must read blank so that a constructed \<open>\<delta>'\<close>-transition meets the
  substrate \<open>\<delta>\<close>-support's read-side condition \<open>\<forall>j\<ge>k. a j = bl\<close>.
  Carried by the simulation (and by each \<open>ae_inv_ss<N>\<close>) so that
  downstream chain steps in \<open>alphabet_enlarge_delta M\<close> can
  discharge both the intersection guard's read-side membership and
  the support's blank-tail locally.\<close>

definition ae_tape_in_gamma_block ::
  "('q, 'a) ktm
    \<Rightarrow> ('c :: enum \<Rightarrow> 'a,
        'q \<times> ('a, 'c) ae_stage) ktc_config
    \<Rightarrow> bool" where
  "ae_tape_in_gamma_block M cM' \<longleftrightarrow>
     (\<forall>k p. ktc_tape cM' k p \<in> gamma_block (\<Gamma>_ktm M))
     \<and> (\<forall>j\<ge>k_ktm M. \<forall>p. ktc_tape cM' j p = bl_block (bl_ktm M))"

text \<open>Write-side blank-tail of \<open>alphabet_enlarge_delta\<close>: every
  member writes the blank block \<open>bl_block (bl_ktm M)\<close> on every
  inactive tape (index \<open>\<ge> k_ktm M\<close>).  Holds builder-by-builder —
  the validation and buffer-load substeps leave the tape unchanged
  (\<open>a' = a\<close>, so the write-tail is the read-tail conjunct), and the
  write-back substeps guard their write to \<open>bl_block (bl_ktm M)\<close>
  beyond \<open>k_ktm M\<close>.  Discharges the \<open>\<delta>\<close>-support write-side
  obligation when threading \<open>ae_tape_in_gamma_block\<close>'s blank-tail
  across a step.\<close>

lemma alphabet_enlarge_delta_write_tail:
  fixes M :: "('q, 'a) ktm"
  assumes mem: "(s, a, s', a', d) \<in> alphabet_enlarge_delta M"
  shows "\<forall>j\<ge>k_ktm M. a' j = bl_block (bl_ktm M)"
  using mem
  unfolding alphabet_enlarge_delta_def
            ae_delta_val_fwd_advance_def ae_delta_val_fwd_to_padded_def
            ae_delta_val_fwd_reject_def ae_delta_val_fwd_to_ret_def
            ae_delta_val_pad_to_ret_def ae_delta_val_pad_reject_def
            ae_delta_val_ret_step_def ae_delta_val_ret_to_sim_def
            ae_delta_ss1_ss2_def ae_delta_ss2_ss3_def ae_delta_ss3_ss4_def
            ae_delta_ss4_ss5_def ae_delta_ss5_ss6_def ae_delta_ss6_ss7_def
            ae_delta_ss7_ss8_def ae_delta_ss8_ss1_def
  by auto

text \<open>Single-step preservation of the gamma-block invariant
  under \<open>alphabet_enlarge_delta\<close>.  The intersection guard in
  \<open>alphabet_enlarge_delta\<close>'s definition forces the written
  value \<open>a' k\<close> to lie in \<open>gamma_block (\<Gamma>_ktm M)\<close>; untouched
  cells inherit gamma-block-ness from the precondition on
  \<open>c'\<close>.  Iteration to \<open>^^ k\<close>-step chains follows by induction
  on \<open>k\<close> at use sites; not packaged separately here pending
  a concrete use site.\<close>

lemma ae_step_alphabet_enlarge_gamma_preserve:
  fixes M  :: "('q, 'a) ktm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                    'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes pre:  "ae_tape_in_gamma_block M c'"
      and step: "(c', c'') \<in> ktm_step (alphabet_enlarge_delta M)"
    shows "ae_tape_in_gamma_block M c''"
proof -
  from step obtain s ts n s' a' d where
      c'_eq:  "c' = KConfig s ts n"
      and c''_eq: "c'' = KConfig s' (\<lambda>k. (ts k)(n k := a' k))
                                    (\<lambda>k. go_move (d k) (n k))"
      and rel: "(s, (\<lambda>k. ts k (n k)), s', a', d) \<in> alphabet_enlarge_delta M"
    by (auto elim: ktm_step.cases)
  from rel have a'_gamma: "\<forall>k. a' k \<in> gamma_block (\<Gamma>_ktm M)"
    unfolding alphabet_enlarge_delta_def by auto
  from rel have a'_tail: "\<forall>j\<ge>k_ktm M. a' j = bl_block (bl_ktm M)"
    by (rule alphabet_enlarge_delta_write_tail)
  have pre_gamma: "\<forall>k p. ktc_tape c' k p \<in> gamma_block (\<Gamma>_ktm M)"
    using pre unfolding ae_tape_in_gamma_block_def by simp
  have pre_tail: "\<forall>j\<ge>k_ktm M. \<forall>p. ktc_tape c' j p = bl_block (bl_ktm M)"
    using pre unfolding ae_tape_in_gamma_block_def by simp
  have gamma_part: "\<forall>k p. ktc_tape c'' k p \<in> gamma_block (\<Gamma>_ktm M)"
  proof (intro allI)
    fix k p
    show "ktc_tape c'' k p \<in> gamma_block (\<Gamma>_ktm M)"
    proof (cases "p = n k")
      case True
      with c''_eq have "ktc_tape c'' k p = a' k" by simp
      thus ?thesis using a'_gamma by simp
    next
      case False
      with c''_eq have eq_c'': "ktc_tape c'' k p = ts k p" by simp
      from c'_eq have eq_c': "ktc_tape c' k p = ts k p" by simp
      from eq_c'' eq_c' have "ktc_tape c'' k p = ktc_tape c' k p" by simp
      thus ?thesis using pre_gamma by simp
    qed
  qed
  have tail_part: "\<forall>j\<ge>k_ktm M. \<forall>p. ktc_tape c'' j p = bl_block (bl_ktm M)"
  proof (intro allI impI)
    fix j p assume jk: "k_ktm M \<le> j"
    show "ktc_tape c'' j p = bl_block (bl_ktm M)"
    proof (cases "p = n j")
      case True
      with c''_eq have "ktc_tape c'' j p = a' j" by simp
      thus ?thesis using a'_tail jk by simp
    next
      case False
      with c''_eq have eq_c'': "ktc_tape c'' j p = ts j p" by simp
      from c'_eq have "ktc_tape c' j p = ts j p" by simp
      with eq_c'' have "ktc_tape c'' j p = ktc_tape c' j p" by simp
      thus ?thesis using pre_tail jk by simp
    qed
  qed
  show ?thesis
    unfolding ae_tape_in_gamma_block_def
    using gamma_part tail_part by blast
qed

text \<open>Side-band invariant: the \<open>M'\<close>-state's stage is \<^emph>\<open>valid\<close>
  in the sense of \<open>ae_valid_stage\<close> at \<open>\<Gamma>_ktm M\<close>, \<open>le_ktm M\<close>,
  \<open>k_ktm M\<close> — every block stored in the three-block buffer
  lies in \<open>gamma_block (\<Gamma>_ktm M)\<close>, and the per-tape offset,
  buffer and destination fields are all frozen at their initial
  values beyond the tape count \<open>k_ktm M\<close>.  Companion to
  \<open>ae_tape_in_gamma_block\<close>: the gamma conjunct discharges the
  \<open>alphabet_enlarge_delta\<close> intersection's write-side membership
  at the write-back substeps (SS5\<open>\<rightarrow>\<close>SS6, SS6\<open>\<rightarrow>\<close>SS7,
  SS7\<open>\<rightarrow>\<close>SS8), and the frozen-tail conjuncts supply the
  \<open>ae_valid_stage\<close> source obligation the step-existence lemmas
  feed to the \<open>*_dest_valid\<close> preservation lemmas — neither is
  provable from the minimal \<open>ae_inv_ss<N>\<close> bodies alone.  Equal by
  construction to \<open>ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
  (snd (ktc_state cM'))\<close>.\<close>

definition ae_buffer_in_gamma_block ::
  "('q, 'a) ktm
    \<Rightarrow> ('c :: enum \<Rightarrow> 'a,
        'q \<times> ('a, 'c) ae_stage) ktc_config
    \<Rightarrow> bool" where
  "ae_buffer_in_gamma_block M cM' \<longleftrightarrow>
     (case ktc_state cM' of (_, off, buf, dst, _) \<Rightarrow>
        (\<forall>k. fst (buf k) \<in> gamma_block (\<Gamma>_ktm M)
            \<and> fst (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)
            \<and> snd (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M))
      \<and> (\<forall>j\<ge>k_ktm M. off j = init_offset j)
      \<and> (\<forall>j\<ge>k_ktm M. buf j = init_buffer (le_ktm M) j)
      \<and> (\<forall>j\<ge>k_ktm M. dst j = init_dest j))"

text \<open>Preservation of \<open>ae_buffer_in_gamma_block\<close> (stage
  validity) under a single \<open>ktm_step\<close> via
  \<open>alphabet_enlarge_delta\<close>.  Companion to
  \<open>ae_step_alphabet_enlarge_gamma_preserve\<close> (tape-side).  The
  destination stage's \<open>ae_valid_stage\<close> is already an explicit
  conjunct of \<open>alphabet_enlarge_delta\<close>'s intersection, so the
  invariant is preserved by reading it straight off the post-state
  — no case split on the 16 sub-deltas is required.  (The
  per-substep discharge of that conjunct lives in the
  \<open>*_dest_valid\<close> lemmas, which the step-existence lemmas invoke
  when building each \<open>\<delta>'\<close>-membership.)\<close>

lemma ae_step_alphabet_enlarge_buffer_gamma_preserve:
  fixes M  :: "('q, 'a) ktm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                    'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes vM:       "valid_ktm M"
      and pre_buf:  "ae_buffer_in_gamma_block M c'"
      and pre_tape: "ae_tape_in_gamma_block M c'"
      and step:     "(c', c'') \<in> ktm_step (alphabet_enlarge_delta M)"
    shows "ae_buffer_in_gamma_block M c''"
proof -
  obtain s ts n s' a' d where
      rel: "(s, (\<lambda>k. ts k (n k)), s', a', d) \<in> alphabet_enlarge_delta M"
      and c'_eq: "c' = KConfig s ts n"
      and c''_eq: "c'' = KConfig s' (\<lambda>k. (ts k)(n k := a' k))
                                      (\<lambda>k. go_move (d k) (n k))"
    using step by (auto elim: ktm_step.cases)
  \<comment> \<open>The destination stage's validity is already an explicit
      conjunct of \<open>alphabet_enlarge_delta\<close>'s intersection, so the
      step preserves \<open>ae_buffer_in_gamma_block\<close> (stage validity)
      directly — no case split on the 16 sub-deltas is needed.\<close>
  obtain q' off' buf' dst' idx' where s'_eq: "s' = (q', off', buf', dst', idx')"
    by (cases s')
  have vs': "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M) (snd s')"
    using rel unfolding alphabet_enlarge_delta_def by auto
  have ktc_c'': "ktc_state c'' = s'" using c''_eq by simp
  show ?thesis
    using vs' ktc_c'' s'_eq
    unfolding ae_buffer_in_gamma_block_def ae_valid_stage_def by simp
qed

text \<open>Joint preservation of \<open>ae_tape_in_gamma_block\<close> and
  \<open>ae_buffer_in_gamma_block\<close> across an \<open>n\<close>-step chain
  of \<open>ktm_step (alphabet_enlarge_delta M)\<close>.  The per-step
  buffer-side preservation requires both invariants at the
  source, so they must thread jointly across the chain.\<close>

lemma ae_gamma_preserve_relpow:
  fixes M  :: "('q, 'a) ktm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                    'q \<times> ('a, 'c) ae_stage) ktc_config"
    and n :: nat
  assumes vM:       "valid_ktm M"
      and pre_buf:  "ae_buffer_in_gamma_block M c'"
      and pre_tape: "ae_tape_in_gamma_block M c'"
      and chain:    "(c', c'') \<in> ktm_step (alphabet_enlarge_delta M) ^^ n"
    shows "ae_buffer_in_gamma_block M c'' \<and> ae_tape_in_gamma_block M c''"
  using relpow_imp_rtrancl [OF chain]
  by (induction rule: rtrancl_induct)
     (auto intro: pre_buf pre_tape ae_step_alphabet_enlarge_gamma_preserve
                  ae_step_alphabet_enlarge_buffer_gamma_preserve [OF vM])

subsubsection \<open>Simulation relation and mid-stage invariants\<close>

text \<open>The simulation relation, stage-granular.  Holds at SS1
  boundaries (or at halt configurations) between
  \<open>M\<close>-configurations and \<open>M'\<close>-configurations.  Captures five
  invariants: \<open>substep_idx\<close> is SS1 (or the halt branch fires);
  \<open>M\<close>-state matches the projected \<open>'q\<close>-component of \<open>M'\<close>'s
  state; tape contents correspond cell-by-block-and-offset
  per \<open>ae_tape_correspondence\<close>; head positions correspond per
  \<open>ae_decode_pos\<close>; and every \<open>M'\<close>-tape cell lies in
  \<open>gamma_block (\<Gamma>_ktm M)\<close> per \<open>ae_tape_in_gamma_block\<close>.

  Mid-stage configurations (\<open>substep_idx\<close> \<open>\<in>\<close> \<open>{SS2, \<dots>, SS7}\<close>
  or any validation phase) are not in this relation; they're
  handled by the per-substep invariants \<open>ae_inv_ss<N>\<close> below
  that thread through individual substep proofs.\<close>

definition ae_simulates ::
  "('q, 'a) ktm
    \<Rightarrow> ('a, 'q) ktc_config
    \<Rightarrow> ('c :: enum \<Rightarrow> 'a,
        'q \<times> ('a, 'c) ae_stage) ktc_config
    \<Rightarrow> bool" where
  "ae_simulates M cM cM' \<longleftrightarrow>
     (let qM = ktc_state cM; tsM = ktc_tape cM; nM = ktc_pos cM;
          full = ktc_state cM';
          tsM' = ktc_tape cM'; nM' = ktc_pos cM' in
      (case full of (qM', off, buf, dest, idx) \<Rightarrow>
         ((idx = SS1 \<and> qM' \<notin> {t_ktm M, r_ktm M})
            \<or> (qM' \<in> {t_ktm M, r_ktm M}
                 \<and> (off, buf, dest, idx) = init_stage (le_ktm M)))
         \<and> qM = qM'
         \<and> (\<forall>k<k_ktm M. ae_tape_correspondence (le_ktm M) (tsM k) (tsM' k))
         \<and> (idx = SS1
              \<longrightarrow> (\<forall>k<k_ktm M. nM k = ae_decode_pos (nM' k) (off k)))
         \<and> ae_tape_in_gamma_block M cM'))"

text \<open>Mid-stage invariants: one per simulation substep boundary.
  Each \<open>ae_inv_ss<N>\<close> describes \<open>M'\<close>'s configuration shape
  at the substep boundary entering substep \<open>SS<N>\<close>.  The
  bodies are deliberately minimal: they pin only the
  \<open>substep_idx\<close> component and the \<open>M\<close>-state's
  membership in \<open>Q_ktm M\<close>.  The heavier tape- and
  buffer-content properties are tracked separately by the
  companion side-band invariants \<open>ae_tape_in_gamma_block\<close>
  and \<open>ae_buffer_in_gamma_block\<close> below, rather than folded
  into these per-substep bodies.\<close>

definition ae_inv_ss1 ::
  "('q, 'a) ktm
    \<Rightarrow> ('c :: enum \<Rightarrow> 'a,
        'q \<times> ('a, 'c) ae_stage) ktc_config
    \<Rightarrow> bool" where
  "ae_inv_ss1 M cM' \<longleftrightarrow>
     (case ktc_state cM' of (qM', _, _, _, idx) \<Rightarrow>
        idx = SS1 \<and> qM' \<in> Q_ktm M)"

definition ae_inv_ss2 ::
  "('q, 'a) ktm
    \<Rightarrow> ('c :: enum \<Rightarrow> 'a,
        'q \<times> ('a, 'c) ae_stage) ktc_config
    \<Rightarrow> bool" where
  "ae_inv_ss2 M cM' \<longleftrightarrow>
     (case ktc_state cM' of (qM', _, _, _, idx) \<Rightarrow>
        idx = SS2 \<and> qM' \<in> Q_ktm M)"

definition ae_inv_ss3 ::
  "('q, 'a) ktm
    \<Rightarrow> ('c :: enum \<Rightarrow> 'a,
        'q \<times> ('a, 'c) ae_stage) ktc_config
    \<Rightarrow> bool" where
  "ae_inv_ss3 M cM' \<longleftrightarrow>
     (case ktc_state cM' of (qM', _, _, _, idx) \<Rightarrow>
        idx = SS3 \<and> qM' \<in> Q_ktm M)"

definition ae_inv_ss4 ::
  "('q, 'a) ktm
    \<Rightarrow> ('c :: enum \<Rightarrow> 'a,
        'q \<times> ('a, 'c) ae_stage) ktc_config
    \<Rightarrow> bool" where
  "ae_inv_ss4 M cM' \<longleftrightarrow>
     (case ktc_state cM' of (qM', _, _, _, idx) \<Rightarrow>
        idx = SS4 \<and> qM' \<in> Q_ktm M)"

definition ae_inv_ss5 ::
  "('q, 'a) ktm
    \<Rightarrow> ('c :: enum \<Rightarrow> 'a,
        'q \<times> ('a, 'c) ae_stage) ktc_config
    \<Rightarrow> bool" where
  "ae_inv_ss5 M cM' \<longleftrightarrow>
     (case ktc_state cM' of (qM', _, _, _, idx) \<Rightarrow>
        idx = SS5 \<and> qM' \<in> Q_ktm M)"

definition ae_inv_ss6 ::
  "('q, 'a) ktm
    \<Rightarrow> ('c :: enum \<Rightarrow> 'a,
        'q \<times> ('a, 'c) ae_stage) ktc_config
    \<Rightarrow> bool" where
  "ae_inv_ss6 M cM' \<longleftrightarrow>
     (case ktc_state cM' of (qM', _, _, _, idx) \<Rightarrow>
        idx = SS6 \<and> qM' \<in> Q_ktm M)"

definition ae_inv_ss7 ::
  "('q, 'a) ktm
    \<Rightarrow> ('c :: enum \<Rightarrow> 'a,
        'q \<times> ('a, 'c) ae_stage) ktc_config
    \<Rightarrow> bool" where
  "ae_inv_ss7 M cM' \<longleftrightarrow>
     (case ktc_state cM' of (qM', _, _, _, idx) \<Rightarrow>
        idx = SS7 \<and> qM' \<in> Q_ktm M)"

definition ae_inv_ss8 ::
  "('q, 'a) ktm
    \<Rightarrow> ('c :: enum \<Rightarrow> 'a,
        'q \<times> ('a, 'c) ae_stage) ktc_config
    \<Rightarrow> bool" where
  "ae_inv_ss8 M cM' \<longleftrightarrow>
     (case ktc_state cM' of (qM', _, _, _, idx) \<Rightarrow>
        idx = SS8 \<and> qM' \<in> Q_ktm M)"

subsubsection \<open>Endmarker compatibility at substeps 6 to 8\<close>

text \<open>Per-substep LE-compatibility predicates (SS6, SS7, SS8).
  At these substeps, the action returns one of the buffer's side
  slots \<open>l\<close>, \<open>r\<close> (or in SS8's halt case, the home slot) in
  branches the LE-no-write guard cannot discharge structurally
  (gamma-block alone allows \<open>l, r \<in> LE_block\<close>).  Each predicate
  asserts the substrate-level guard exactly: at the current
  configuration, if the substep's action returns \<open>LE_block\<close> on
  tape \<open>k\<close>, then \<open>ts k (n k)\<close> already equals \<open>LE_block\<close>.
  These are contracts the chain proof discharges from a richer
  position-buffer correspondence; the per-substep step-existence
  lemmas consume them as additional hypotheses.\<close>

definition ae_le_compat_ss6 ::
  "('q, 'a) ktm
    \<Rightarrow> ('c :: enum \<Rightarrow> 'a,
        'q \<times> ('a, 'c) ae_stage) ktc_config
    \<Rightarrow> bool" where
  "ae_le_compat_ss6 M cM' \<longleftrightarrow>
     (case cM' of KConfig (_, _, buf, dest, _) ts n \<Rightarrow>
        \<forall>k<k_ktm M. fst (ae_ss6_action (le_ktm M) (ts k (n k)) (buf k) (dest k))
              = LE_block (le_ktm M)
            \<longrightarrow> ts k (n k) = LE_block (le_ktm M))"

definition ae_le_compat_ss7 ::
  "('q, 'a) ktm
    \<Rightarrow> ('c :: enum \<Rightarrow> 'a,
        'q \<times> ('a, 'c) ae_stage) ktc_config
    \<Rightarrow> bool" where
  "ae_le_compat_ss7 M cM' \<longleftrightarrow>
     (case cM' of KConfig (_, _, buf, dest, _) ts n \<Rightarrow>
        \<forall>k<k_ktm M. fst (ae_ss7_action (le_ktm M) (ts k (n k)) (buf k) (dest k))
              = LE_block (le_ktm M)
            \<longrightarrow> ts k (n k) = LE_block (le_ktm M))"

definition ae_le_compat_ss8 ::
  "('q, 'a) ktm
    \<Rightarrow> ('c :: enum \<Rightarrow> 'a,
        'q \<times> ('a, 'c) ae_stage) ktc_config
    \<Rightarrow> bool" where
  "ae_le_compat_ss8 M cM' \<longleftrightarrow>
     (case cM' of KConfig (_, _, buf, dest, _) ts n \<Rightarrow>
        \<forall>k<k_ktm M. fst (ae_ss8_action (le_ktm M) (ts k (n k)) (buf k) (dest k))
              = LE_block (le_ktm M)
            \<longrightarrow> ts k (n k) = LE_block (le_ktm M))"

text \<open>\<^emph>\<open>The LE-guard pre-emption invariant.\<close>  This is the
  load-bearing side-band that makes the writeback chain
  correct across all three regimes (steady-state, le1, le0).

  *Why we need it.*  Each writeback substep's action
  (\<open>ae_ss5_action\<close> through \<open>ae_ss8_action\<close>) has
  an LE-guard prefix branch (\<open>a = LE_block le\<close>: write
  \<open>LE_block\<close> back, idempotent — see the action-helper
  preamble) and a default branch that writes some buffer slot.
  If the buffer slot the default branch \<^emph>\<open>would\<close> write is itself
  \<open>LE_block\<close> and the head is at a non-LE position, the
  default branch would corrupt the tape encoding by writing
  \<open>LE_block\<close> where non-LE data should be.  The construction
  prevents this by \<^emph>\<open>threading the head trajectory through
  block 0 (the LE position) at exactly the moments when a
  buffer-LE-write would otherwise occur\<close> — so the LE-guard
  branch fires first and pre-empts the default branch's
  dangerous write.

  *What the predicate captures.*  The three conjuncts are
  exactly the structural facts needed for this pre-emption to
  hold:

  \<^enum> Post-buffer-load (\<open>idx \<in> {SS5, SS6, SS7, SS8}\<close>): the
    buffer's \<open>r\<close> slot is not \<open>LE_block\<close>.  This rules out
    the dangerous write whenever SS6 (\<open>dest = AE_Left\<close>) or
    SS7/SS8 (various \<open>dest\<close>) would write the r-slot — those
    branches' antecedent (\<open>slot = LE_block\<close>) is vacuously
    false.  Justification: \<open>r\<close> is loaded from \<open>M'\<close>-position
    \<open>p_start + 1 \<ge> 1\<close>; the substrate's \<open>\<delta>\<close>LE
    forbids \<open>LE_block\<close> at any position \<open>\<ge> 1\<close>, and the
    c-step compute (via \<open>ae_m_steps_buffered_correct\<close>)
    preserves this.

  \<^enum> SS6 (\<open>dest \<noteq> AE_Left\<close>): when SS6's default branch
    would write the \<open>l\<close>-slot, and that \<open>l\<close>-slot is
    \<open>LE_block\<close>, then the head IS at a position holding
    \<open>LE_block\<close>.  The LE-guard fires and pre-empts the
    default branch.  In steady-state (\<open>s \<ge> 2\<close>) the
    antecedent \<open>l = LE_block\<close> is vacuously false (l is
    loaded from block \<open>s-1 \<ge> 1\<close>, non-LE).  In le1
    (\<open>s = 1\<close>) the antecedent is true (l is loaded from
    block 0, which IS \<open>LE_block\<close>), and the consequent
    is established by le1's head trajectory: SS5's
    \<open>move L\<close> rule (for \<open>dest \<noteq> AE_Left\<close>) takes the
    head from block 1 (SS5 entry) to block 0 (SS6
    entry) where it reads \<open>LE_block\<close>.

  \<^enum> SS8 (\<open>dest = AE_Left\<close>): symmetric to the SS6 clause.
    When SS8's default branch would write the \<open>l\<close>-slot for
    \<open>dest = AE_Left\<close>, and that slot is \<open>LE_block\<close>,
    the head is at \<open>LE_block\<close>.  Steady-state vacuous;
    in le1 with \<open>dest = AE_Left\<close>, SS5's \<open>move R\<close> +
    SS6's \<open>move L\<close> + SS7's \<open>move L\<close> threads the
    head from block 1 to block 0 by SS8 entry.

  Other substep+dest combinations either write \<open>r\<close>
  (covered by conjunct 1, vacuous antecedent), write \<open>a\<close>
  back idempotently (SS7's default; no \<open>LE_block\<close> ever
  introduced), or fire only on the LE-guard branch (writing
  \<open>LE_block\<close> only when \<open>a = LE_block\<close>, which is
  trivially safe).

  *Why this isn't separate predicates per regime.*  The
  predicate's antecedents (\<open>slot = LE_block\<close>) are
  inherently regime-discriminating: steady-state satisfies
  them vacuously, le1 satisfies them via head-trajectory
  tracing.  A single uniform predicate works because the
  substep actions' direction rules
  (\<open>ae_ss5_action\<close>'s "move L when \<open>dest \<noteq>
  AE_Left\<close>", etc.) deliver the head to block 0 at
  exactly the right substeps in le1, and don't need to in
  steady-state.\<close>

definition ae_position_link ::
  "('q, 'a) ktm
    \<Rightarrow> ('c :: enum \<Rightarrow> 'a,
        'q \<times> ('a, 'c) ae_stage) ktc_config
    \<Rightarrow> bool" where
  "ae_position_link M cM' \<longleftrightarrow>
     (case ktc_state cM' of (_, _, buf, dest, idx) \<Rightarrow>
        (idx \<in> {SS5, SS6, SS7, SS8} \<longrightarrow>
           (\<forall>k<k_ktm M. snd (snd (buf k)) \<noteq> LE_block (le_ktm M)))
        \<and> (idx = SS6 \<longrightarrow>
           (\<forall>k<k_ktm M. dest k \<noteq> AE_Left
                  \<longrightarrow> fst (buf k) = LE_block (le_ktm M)
                  \<longrightarrow> ktc_tape cM' k (ktc_pos cM' k)
                        = LE_block (le_ktm M)))
        \<and> (idx = SS8 \<longrightarrow>
           (\<forall>k<k_ktm M. dest k = AE_Left
                  \<longrightarrow> fst (buf k) = LE_block (le_ktm M)
                  \<longrightarrow> ktc_tape cM' k (ktc_pos cM' k)
                        = LE_block (le_ktm M))))"

subsubsection \<open>Endmarker compatibility from the position invariant\<close>

text \<open>Discharge lemmas: at SS\<open><N>\<close> entry (per
  \<open>ae_inv_ss<N>\<close>), the side-band \<open>ae_position_link\<close> implies the
  per-substep contract \<open>ae_le_compat_ss<N>\<close>.  Each proof
  case-splits on the \<open>ae_ss<N>_action\<close>'s branches: r-write
  branches close via the first conjunct of \<open>ae_position_link\<close>
  (\<open>r \<noteq> LE_block\<close> makes the antecedent vacuous); a-write
  branches close trivially via \<open>a' = a\<close>; the l-write branch
  (SS6 with \<open>dest \<noteq> AE_Left\<close>; SS8 with \<open>dest = AE_Left\<close>)
  closes via the second conjunct (the position-link's
  \<open>l = LE_block \<longrightarrow> ts (n) = LE_block\<close> guard for that
  substep+dest).  Used at the chain proof's call site to
  discharge the \<open>ae_le_compat_ss<N>\<close> hypotheses on the
  \<open>ae_step_ss<N>_ss<N+1>_exists\<close> step-existence helpers.\<close>

lemma ae_position_link_discharges_ss6:
  fixes M :: "('q, 'a) ktm"
    and c' :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes inv: "ae_inv_ss6 M c'"
      and pos: "ae_position_link M c'"
    shows "ae_le_compat_ss6 M c'"
proof -
  obtain q ofs buf dest where
      state_eq: "ktc_state c' = (q, ofs, buf, dest, SS6)"
    using inv unfolding ae_inv_ss6_def
    by (cases "ktc_state c'") auto
  obtain ts n where
      c'_eq: "c' = KConfig (q, ofs, buf, dest, SS6) ts n"
    using state_eq by (cases c') auto
  have r_not_le: "\<forall>k<k_ktm M. snd (snd (buf k)) \<noteq> LE_block (le_ktm M)"
    using pos state_eq unfolding ae_position_link_def by simp
  have l_guard:
      "\<forall>k<k_ktm M. dest k \<noteq> AE_Left
              \<longrightarrow> fst (buf k) = LE_block (le_ktm M)
              \<longrightarrow> ts k (n k) = LE_block (le_ktm M)"
    using pos state_eq c'_eq unfolding ae_position_link_def by simp
  have body:
      "\<forall>k<k_ktm M. fst (ae_ss6_action (le_ktm M) (ts k (n k)) (buf k) (dest k))
              = LE_block (le_ktm M)
            \<longrightarrow> ts k (n k) = LE_block (le_ktm M)"
  proof (intro allI impI)
    fix k
    assume klt: "k < k_ktm M"
    let ?a = "ts k (n k)"
    obtain l h r where buf_k: "buf k = (l, h, r)"
      by (cases "buf k") auto
    assume act_le:
        "fst (ae_ss6_action (le_ktm M) ?a (buf k) (dest k))
            = LE_block (le_ktm M)"
    show "?a = LE_block (le_ktm M)"
    proof (cases "?a = LE_block (le_ktm M)")
      case True thus ?thesis .
    next
      case a_neq: False
      show ?thesis
      proof (cases "h = LE_block (le_ktm M)")
        case h_le: True
        from a_neq h_le buf_k have
            "fst (ae_ss6_action (le_ktm M) ?a (buf k) (dest k)) = ?a"
          by simp
        with act_le show ?thesis by simp
      next
        case h_neq: False
        show ?thesis
        proof (cases "dest k = AE_Left")
          case ds_l: True
          from a_neq h_neq ds_l buf_k have
              "fst (ae_ss6_action (le_ktm M) ?a (buf k) (dest k)) = r"
            by simp
          with act_le have "r = LE_block (le_ktm M)" by simp
          with r_not_le[rule_format, OF klt] buf_k have False by simp
          thus ?thesis ..
        next
          case ds_nl: False
          from a_neq h_neq ds_nl buf_k have
              "fst (ae_ss6_action (le_ktm M) ?a (buf k) (dest k)) = l"
            by simp
          with act_le have l_le: "l = LE_block (le_ktm M)" by simp
          have "fst (buf k) = l" using buf_k by simp
          with l_le ds_nl l_guard[rule_format, OF klt] show ?thesis by simp
        qed
      qed
    qed
  qed
  show ?thesis
    using body unfolding ae_le_compat_ss6_def c'_eq by simp
qed

lemma ae_position_link_discharges_ss7:
  fixes M :: "('q, 'a) ktm"
    and c' :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes inv: "ae_inv_ss7 M c'"
      and pos: "ae_position_link M c'"
    shows "ae_le_compat_ss7 M c'"
proof -
  obtain q ofs buf dest where
      state_eq: "ktc_state c' = (q, ofs, buf, dest, SS7)"
    using inv unfolding ae_inv_ss7_def
    by (cases "ktc_state c'") auto
  obtain ts n where
      c'_eq: "c' = KConfig (q, ofs, buf, dest, SS7) ts n"
    using state_eq by (cases c') auto
  have r_not_le: "\<forall>k<k_ktm M. snd (snd (buf k)) \<noteq> LE_block (le_ktm M)"
    using pos state_eq unfolding ae_position_link_def by simp
  have body:
      "\<forall>k<k_ktm M. fst (ae_ss7_action (le_ktm M) (ts k (n k)) (buf k) (dest k))
              = LE_block (le_ktm M)
            \<longrightarrow> ts k (n k) = LE_block (le_ktm M)"
  proof (intro allI impI)
    fix k
    assume klt: "k < k_ktm M"
    let ?a = "ts k (n k)"
    obtain l h r where buf_k: "buf k = (l, h, r)"
      by (cases "buf k") auto
    assume act_le:
        "fst (ae_ss7_action (le_ktm M) ?a (buf k) (dest k))
            = LE_block (le_ktm M)"
    show "?a = LE_block (le_ktm M)"
    proof (cases "?a = LE_block (le_ktm M)")
      case True thus ?thesis .
    next
      case a_neq: False
      show ?thesis
      proof (cases "h = LE_block (le_ktm M)")
        case h_le: True
        from a_neq h_le buf_k have
            "fst (ae_ss7_action (le_ktm M) ?a (buf k) (dest k)) = r"
          by simp
        with act_le have "r = LE_block (le_ktm M)" by simp
        with r_not_le[rule_format, OF klt] buf_k have False by simp
        thus ?thesis ..
      next
        case h_neq: False
        from a_neq h_neq buf_k have
            "fst (ae_ss7_action (le_ktm M) ?a (buf k) (dest k)) = ?a"
          by simp
        with act_le show ?thesis by simp
      qed
    qed
  qed
  show ?thesis
    using body unfolding ae_le_compat_ss7_def c'_eq by simp
qed

lemma ae_position_link_discharges_ss8:
  fixes M :: "('q, 'a) ktm"
    and c' :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes inv: "ae_inv_ss8 M c'"
      and pos: "ae_position_link M c'"
    shows "ae_le_compat_ss8 M c'"
proof -
  obtain q ofs buf dest where
      state_eq: "ktc_state c' = (q, ofs, buf, dest, SS8)"
    using inv unfolding ae_inv_ss8_def
    by (cases "ktc_state c'") auto
  obtain ts n where
      c'_eq: "c' = KConfig (q, ofs, buf, dest, SS8) ts n"
    using state_eq by (cases c') auto
  have r_not_le: "\<forall>k<k_ktm M. snd (snd (buf k)) \<noteq> LE_block (le_ktm M)"
    using pos state_eq unfolding ae_position_link_def by simp
  have l_guard:
      "\<forall>k<k_ktm M. dest k = AE_Left
              \<longrightarrow> fst (buf k) = LE_block (le_ktm M)
              \<longrightarrow> ts k (n k) = LE_block (le_ktm M)"
    using pos state_eq c'_eq unfolding ae_position_link_def by simp
  have body:
      "\<forall>k<k_ktm M. fst (ae_ss8_action (le_ktm M) (ts k (n k)) (buf k) (dest k))
              = LE_block (le_ktm M)
            \<longrightarrow> ts k (n k) = LE_block (le_ktm M)"
  proof (intro allI impI)
    fix k
    assume klt: "k < k_ktm M"
    let ?a = "ts k (n k)"
    obtain l h r where buf_k: "buf k = (l, h, r)"
      by (cases "buf k") auto
    assume act_le:
        "fst (ae_ss8_action (le_ktm M) ?a (buf k) (dest k))
            = LE_block (le_ktm M)"
    show "?a = LE_block (le_ktm M)"
    proof (cases "?a = LE_block (le_ktm M)")
      case True thus ?thesis .
    next
      case a_neq: False
      show ?thesis
      proof (cases "h = LE_block (le_ktm M)")
        case h_le: True
        show ?thesis
        proof (cases "dest k = AE_Right")
          case ds_r: True
          from a_neq h_le ds_r buf_k have
              "fst (ae_ss8_action (le_ktm M) ?a (buf k) (dest k)) = r"
            by simp
          with act_le have "r = LE_block (le_ktm M)" by simp
          with r_not_le[rule_format, OF klt] buf_k have False by simp
          thus ?thesis ..
        next
          case ds_nr: False
          from a_neq h_le ds_nr buf_k have
              "fst (ae_ss8_action (le_ktm M) ?a (buf k) (dest k)) = ?a"
            by simp
          with act_le show ?thesis by simp
        qed
      next
        case h_neq: False
        show ?thesis
        proof (cases "dest k")
          case AE_Left
          from a_neq h_neq AE_Left buf_k have
              "fst (ae_ss8_action (le_ktm M) ?a (buf k) (dest k)) = l"
            by simp
          with act_le have l_le: "l = LE_block (le_ktm M)" by simp
          have "fst (buf k) = l" using buf_k by simp
          with l_le AE_Left l_guard[rule_format, OF klt] show ?thesis by simp
        next
          case AE_Home
          from a_neq h_neq AE_Home buf_k have
              "fst (ae_ss8_action (le_ktm M) ?a (buf k) (dest k)) = r"
            by simp
          with act_le have "r = LE_block (le_ktm M)" by simp
          with r_not_le[rule_format, OF klt] buf_k have False by simp
          thus ?thesis ..
        next
          case AE_Right
          from a_neq h_neq AE_Right buf_k have
              "fst (ae_ss8_action (le_ktm M) ?a (buf k) (dest k)) = r"
            by simp
          with act_le have "r = LE_block (le_ktm M)" by simp
          with r_not_le[rule_format, OF klt] buf_k have False by simp
          thus ?thesis ..
        qed
      qed
    qed
  qed
  show ?thesis
    using body unfolding ae_le_compat_ss8_def c'_eq by simp
qed

subsubsection \<open>Which substep a step starts from\<close>

text \<open>Pre-state idx determinations for the three substantive
  sub-deltas of \<open>ae_step_alphabet_enlarge_position_link_preserve\<close>'s
  aux hypotheses.  Used by the chain proof to discharge vacuous-aux
  cases of the preservation lemma: when the actual sub-step is e.g.
  \<open>ss1\<rightarrow>ss2\<close>, the pre-state idx is SS1 \<open>\<noteq>\<close> SS4, so
  the \<open>aux_ss4_ss5\<close> antecedent is unsatisfiable.\<close>

lemma ae_delta_ss4_ss5_pre_idx:
  assumes "(s, a, s', a', d) \<in> ae_delta_ss4_ss5 M"
  shows "snd (snd (snd (snd s))) = SS4"
  using assms unfolding ae_delta_ss4_ss5_def by force

lemma ae_delta_ss5_ss6_pre_idx:
  assumes "(s, a, s', a', d) \<in> ae_delta_ss5_ss6 M"
  shows "snd (snd (snd (snd s))) = SS5"
  using assms unfolding ae_delta_ss5_ss6_def by force

lemma ae_delta_ss7_ss8_pre_idx:
  assumes "(s, a, s', a', d) \<in> ae_delta_ss7_ss8 M"
  shows "snd (snd (snd (snd s))) = SS7"
  using assms unfolding ae_delta_ss7_ss8_def by force

text \<open>Vacuous-aux helpers: when the actual sub-step is not
  SS4\<open>\<rightarrow>\<close>SS5 / SS5\<open>\<rightarrow>\<close>SS6 / SS7\<open>\<rightarrow>\<close>SS8
  (per the pre-state idx), the corresponding aux antecedent of
  \<open>ae_step_alphabet_enlarge_position_link_preserve\<close> is
  unsatisfiable, so the aux holds vacuously.  Used in the chain
  proof to discharge the three aux hypotheses at substeps whose
  pre-state idx doesn't match.\<close>

lemma ae_pos_link_aux_void_ss4_ss5:
  fixes M :: "('q, 'a) ktm"
    and c_pre c_post :: "('c :: enum \<Rightarrow> 'a,
                           'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes pre_neq: "snd (snd (snd (snd (ktc_state c_pre)))) \<noteq> SS4"
      and step:    "(c_pre, c_post) \<in> ktm_step (ae_delta_ss4_ss5 M)"
    shows "ae_position_link M c_post"
proof -
  from step obtain s ts n s' a' d where
      eq: "c_pre = KConfig s ts n"
      and rel: "(s, (\<lambda>k. ts k (n k)), s', a', d) \<in> ae_delta_ss4_ss5 M"
    by (auto elim: ktm_step.cases)
  have "snd (snd (snd (snd s))) = SS4"
    using ae_delta_ss4_ss5_pre_idx[OF rel] .
  with eq pre_neq have False by simp
  thus ?thesis ..
qed

lemma ae_pos_link_aux_void_ss5_ss6:
  fixes M :: "('q, 'a) ktm"
    and c_pre c_post :: "('c :: enum \<Rightarrow> 'a,
                           'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes pre_neq: "snd (snd (snd (snd (ktc_state c_pre)))) \<noteq> SS5"
      and step:    "(c_pre, c_post) \<in> ktm_step (ae_delta_ss5_ss6 M)"
    shows "ae_position_link M c_post"
proof -
  from step obtain s ts n s' a' d where
      eq: "c_pre = KConfig s ts n"
      and rel: "(s, (\<lambda>k. ts k (n k)), s', a', d) \<in> ae_delta_ss5_ss6 M"
    by (auto elim: ktm_step.cases)
  have "snd (snd (snd (snd s))) = SS5"
    using ae_delta_ss5_ss6_pre_idx[OF rel] .
  with eq pre_neq have False by simp
  thus ?thesis ..
qed

lemma ae_pos_link_aux_void_ss7_ss8:
  fixes M :: "('q, 'a) ktm"
    and c_pre c_post :: "('c :: enum \<Rightarrow> 'a,
                           'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes pre_neq: "snd (snd (snd (snd (ktc_state c_pre)))) \<noteq> SS7"
      and step:    "(c_pre, c_post) \<in> ktm_step (ae_delta_ss7_ss8 M)"
    shows "ae_position_link M c_post"
proof -
  from step obtain s ts n s' a' d where
      eq: "c_pre = KConfig s ts n"
      and rel: "(s, (\<lambda>k. ts k (n k)), s', a', d) \<in> ae_delta_ss7_ss8 M"
    by (auto elim: ktm_step.cases)
  have "snd (snd (snd (snd s))) = SS7"
    using ae_delta_ss7_ss8_pre_idx[OF rel] .
  with eq pre_neq have False by simp
  thus ?thesis ..
qed

subsubsection \<open>Position-link preservation\<close>

text \<open>Preservation of \<open>ae_position_link\<close> under a single
  \<open>ktm_step\<close> via \<open>alphabet_enlarge_delta\<close>.  The proof
  case-splits on which of the 16 sub-deltas fires.  Validation
  transitions (8) and simulation transitions whose post-idx is
  outside the post-buffer-load regime
  (\<open>ss1\<rightarrow>ss2\<close>, \<open>ss2\<rightarrow>ss3\<close>,
  \<open>ss3\<rightarrow>ss4\<close>, \<open>ss8\<rightarrow>ss1\<close>) close
  vacuously — the predicate's content is conditional on
  \<open>idx \<in>\<close> \<open>{SS5, SS6, SS7, SS8}\<close>.  The buffer-stable
  transition \<open>ss6\<rightarrow>ss7\<close> closes by transferring the
  pre-state's \<open>r \<noteq> LE_block\<close> across the buffer-preserving
  step.  The three substantive transitions \<open>ss4\<rightarrow>ss5\<close>,
  \<open>ss5\<rightarrow>ss6\<close>, \<open>ss7\<rightarrow>ss8\<close> require
  auxiliary hypotheses that the chain proof discharges from the
  broader simulation context (\<open>m_steps_buffered_correct\<close>'s
  \<open>\<delta>\<close>LE preservation, the buffer-load invariants, and
  the cadence at SS5/SS7 entry).\<close>

lemma ae_step_alphabet_enlarge_position_link_preserve:
  fixes M  :: "('q, 'a) ktm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                    'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes pre: "ae_position_link M c'"
      and step: "(c', c'') \<in> ktm_step (alphabet_enlarge_delta M)"
      and aux_ss4_ss5:
          "(c', c'') \<in> ktm_step (ae_delta_ss4_ss5 M)
            \<Longrightarrow> ae_position_link M c''"
      and aux_ss5_ss6:
          "(c', c'') \<in> ktm_step (ae_delta_ss5_ss6 M)
            \<Longrightarrow> ae_position_link M c''"
      and aux_ss7_ss8:
          "(c', c'') \<in> ktm_step (ae_delta_ss7_ss8 M)
            \<Longrightarrow> ae_position_link M c''"
    shows "ae_position_link M c''"
proof -
  obtain s ts n s' a' d where
      rel: "(s, (\<lambda>k. ts k (n k)), s', a', d) \<in> alphabet_enlarge_delta M"
      and c'_eq: "c' = KConfig s ts n"
      and c''_eq: "c'' = KConfig s' (\<lambda>k. (ts k)(n k := a' k))
                                      (\<lambda>k. go_move (d k) (n k))"
    using step by (auto elim: ktm_step.cases)
  let ?rel_tup = "(s, (\<lambda>k. ts k (n k)), s', a', d)"
  consider
      (vfa) "?rel_tup \<in> ae_delta_val_fwd_advance M"
    | (vfp) "?rel_tup \<in> ae_delta_val_fwd_to_padded M"
    | (vfr) "?rel_tup \<in> ae_delta_val_fwd_reject M"
    | (vfr2) "?rel_tup \<in> ae_delta_val_fwd_to_ret M"
    | (vpr) "?rel_tup \<in> ae_delta_val_pad_to_ret M"
    | (vpr2) "?rel_tup \<in> ae_delta_val_pad_reject M"
    | (vrs) "?rel_tup \<in> ae_delta_val_ret_step M"
    | (vrts) "?rel_tup \<in> ae_delta_val_ret_to_sim M"
    | (s12) "?rel_tup \<in> ae_delta_ss1_ss2 M"
    | (s23) "?rel_tup \<in> ae_delta_ss2_ss3 M"
    | (s34) "?rel_tup \<in> ae_delta_ss3_ss4 M"
    | (s45) "?rel_tup \<in> ae_delta_ss4_ss5 M"
    | (s56) "?rel_tup \<in> ae_delta_ss5_ss6 M"
    | (s67) "?rel_tup \<in> ae_delta_ss6_ss7 M"
    | (s78) "?rel_tup \<in> ae_delta_ss7_ss8 M"
    | (s81) "?rel_tup \<in> ae_delta_ss8_ss1 M"
    using rel unfolding alphabet_enlarge_delta_def by blast
  thus ?thesis
  proof cases
    case vfa
    thus ?thesis
      using c''_eq unfolding ae_position_link_def ae_delta_val_fwd_advance_def
      by auto
  next
    case vfp
    thus ?thesis
      using c''_eq unfolding ae_position_link_def ae_delta_val_fwd_to_padded_def
      by auto
  next
    case vfr
    thus ?thesis
      using c''_eq
      unfolding ae_position_link_def ae_delta_val_fwd_reject_def init_stage_def
      by auto
  next
    case vfr2
    thus ?thesis
      using c''_eq unfolding ae_position_link_def ae_delta_val_fwd_to_ret_def
      by auto
  next
    case vpr
    thus ?thesis
      using c''_eq unfolding ae_position_link_def ae_delta_val_pad_to_ret_def
      by auto
  next
    case vpr2
    thus ?thesis
      using c''_eq
      unfolding ae_position_link_def ae_delta_val_pad_reject_def init_stage_def
      by auto
  next
    case vrs
    thus ?thesis
      using c''_eq unfolding ae_position_link_def ae_delta_val_ret_step_def
      by auto
  next
    case vrts
    thus ?thesis
      using c''_eq unfolding ae_position_link_def ae_delta_val_ret_to_sim_def
      by auto
  next
    case s12
    thus ?thesis
      using c''_eq unfolding ae_position_link_def ae_delta_ss1_ss2_def
      by auto
  next
    case s23
    thus ?thesis
      using c''_eq unfolding ae_position_link_def ae_delta_ss2_ss3_def
      by auto
  next
    case s34
    thus ?thesis
      using c''_eq unfolding ae_position_link_def ae_delta_ss3_ss4_def
      by auto
  next
    case s45
    have step_s45: "(c', c'') \<in> ktm_step (ae_delta_ss4_ss5 M)"
      using s45 c'_eq c''_eq by (auto intro: ktm_step.intros)
    thus ?thesis by (rule aux_ss4_ss5)
  next
    case s56
    have step_s56: "(c', c'') \<in> ktm_step (ae_delta_ss5_ss6 M)"
      using s56 c'_eq c''_eq by (auto intro: ktm_step.intros)
    thus ?thesis by (rule aux_ss5_ss6)
  next
    case s67
    \<comment> \<open>Buffer unchanged from SS6 (pre) to SS7 (post).
        Pre's \<open>r \<noteq> LE_block\<close> at SS6 transfers to SS7.\<close>
    obtain q ofs buf dest where
        pre_state: "s = (q, ofs, buf, dest, SS6)"
        and post_state: "s' = (q, ofs, buf, dest, SS7)"
      using s67 unfolding ae_delta_ss6_ss7_def by auto
    have pre_state': "ktc_state c' = (q, ofs, buf, dest, SS6)"
      using c'_eq pre_state by simp
    have post_state': "ktc_state c'' = (q, ofs, buf, dest, SS7)"
      using c''_eq post_state by simp
    have r_not_le:
        "\<forall>k<k_ktm M. snd (snd (buf k)) \<noteq> LE_block (le_ktm M)"
      using pre pre_state' unfolding ae_position_link_def by simp
    show ?thesis
      unfolding ae_position_link_def post_state'
      using r_not_le by simp
  next
    case s78
    have step_s78: "(c', c'') \<in> ktm_step (ae_delta_ss7_ss8 M)"
      using s78 c'_eq c''_eq by (auto intro: ktm_step.intros)
    thus ?thesis by (rule aux_ss7_ss8)
  next
    case s81
    \<comment> \<open>Post-state is SS1 (non-halt branch) or \<open>init_stage le\<close>
        (halt branch); both have idx outside the regime.\<close>
    obtain q ofs buf dest where
        pre_state: "s = (q, ofs, buf, dest, SS8)"
        and post_state:
          "s' = (q, if q \<in> {t_ktm M, r_ktm M}
                      then init_stage (le_ktm M)
                      else (ofs, buf, init_dest, SS1))"
      using s81 unfolding ae_delta_ss8_ss1_def by auto
    show ?thesis
    proof (cases "q \<in> {t_ktm M, r_ktm M}")
      case True
      hence "s' = (q, init_stage (le_ktm M))" using post_state by simp
      thus ?thesis
        using c''_eq
        unfolding ae_position_link_def init_stage_def
        by auto
    next
      case False
      hence "s' = (q, ofs, buf, init_dest, SS1)" using post_state by simp
      thus ?thesis
        using c''_eq
        unfolding ae_position_link_def
        by auto
    qed
  qed
qed

subsubsection \<open>Per-substep step-existence\<close>

text \<open>Per-substep step-existence lemmas (forward simulation,
  buffer phase).  Each lemma, given a configuration \<open>c'\<close>
  satisfying the appropriate \<open>ae_inv_ss<N>\<close> precondition (plus
  whichever side-band invariants the substep requires), produces
  a witness \<open>c''\<close> for which both the per-substep step
  \<open>ktm_step (ae_delta_ss<N>_ss<N+1> M)\<close> and the full-delta
  step \<open>ktm_step (alphabet_enlarge_delta M)\<close> hold.  Per-substep
  delta is forwarded to the existing
  \<open>ae_step_ss<N>_ss<N+1>_invariant\<close> lemma at the chain
  orchestration site (\<open>ae_simulates_forward_stage\<close>);
  full-delta step accumulates into the chain's
  \<open>ktm_step\<^sup>*\<close> closure.

  Hypothesis pattern by substep:

  \<^item> SS1\<open>\<rightarrow>\<close>SS2, SS2\<open>\<rightarrow>\<close>SS3,
    SS3\<open>\<rightarrow>\<close>SS4 (buffer-load): \<open>ae_inv_ss<N>\<close> +
    \<open>ae_tape_in_gamma_block\<close> + non-halt; substrate write is a
    no-op (\<open>a' = a\<close>).
  \<^item> SS4\<open>\<rightarrow>\<close>SS5 (c-fold compute): adds \<open>valid_ktm\<close>,
    \<open>delta_total\<close>, the per-tape \<open>ae_window_invariant\<close>, and a
    no-LE-in-window hypothesis; the substrate witness is obtained
    by invoking \<open>ae_m_steps_buffered_correct\<close>.  Substrate write
    is still a no-op.  Located in
    \<open>AlphabetEnlargement\<close> rather than this theory because
    \<open>ae_m_steps_buffered_correct\<close> lives there.
  \<^item> SS5\<open>\<rightarrow>\<close>SS6 (write-back, first cell):
    \<open>ae_inv_ss5\<close> + \<open>ae_tape_in_gamma_block\<close> +
    \<open>ae_buffer_in_gamma_block\<close>; no non-halt hypothesis (the
    SS5 action is total in its inputs; halt routing kicks in only
    at SS8\<open>\<rightarrow>\<close>SS1).
  \<^item> SS6\<open>\<rightarrow>\<close>SS7 (write-back, side cell):
    \<open>ae_inv_ss6\<close> + \<open>ae_tape_in_gamma_block\<close> +
    \<open>ae_buffer_in_gamma_block\<close> + \<open>ae_le_compat_ss6\<close>.
    The fourth hypothesis is the per-substep LE-no-write
    contract (the action returns the buffer's \<open>l\<close> or \<open>r\<close> slot
    in steady-state, and gamma-block alone does not preclude
    \<open>l, r \<in> LE_block\<close>).
  \<^item> SS7\<open>\<rightarrow>\<close>SS8: same shape as SS6, with
    \<open>ae_le_compat_ss7\<close>.
  \<^item> SS8\<open>\<rightarrow>\<close>SS1: same shape, with
    \<open>ae_le_compat_ss8\<close>; halt-aware destination routing is
    internal to \<open>ae_delta_ss8_ss1\<close>'s \<open>stage'\<close> if-then-else,
    so step-existence is uniform across halt and non-halt.\<close>

lemma ae_step_ss1_ss2_exists:
  fixes M :: "('q, 'a) ktm"
    and c' :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes inv:     "ae_inv_ss1 M c'"
      and gamma:   "ae_tape_in_gamma_block M c'"
      and buf:     "ae_buffer_in_gamma_block M c'"
      and q_neq_t: "fst (ktc_state c') \<noteq> t_ktm M"
      and q_neq_r: "fst (ktc_state c') \<noteq> r_ktm M"
  shows "\<exists>c''. (c', c'') \<in> ktm_step (ae_delta_ss1_ss2 M)
                \<and> (c', c'') \<in> ktm_step (alphabet_enlarge_delta M)"
proof -
  obtain q ofs buf dest where
      state_eq: "ktc_state c' = (q, ofs, buf, dest, SS1)"
      and q_in: "q \<in> Q_ktm M"
    using inv unfolding ae_inv_ss1_def
    by (cases "ktc_state c'") auto
  obtain ts n where c'_eq: "c' = KConfig (q, ofs, buf, dest, SS1) ts n"
    using state_eq by (cases c') auto
  let ?a = "\<lambda>k. ts k (n k)"
  let ?buf' = "\<lambda>k. if k < k_ktm M
                     then (fst (buf k), ?a k, snd (snd (buf k)))
                     else init_buffer (le_ktm M) k"
  let ?d = "\<lambda>k. if k < k_ktm M
                  then (if ?a k = LE_block (le_ktm M) then MoveN else MoveL)
                  else MoveN"
  have q_neq_t': "q \<noteq> t_ktm M" using q_neq_t state_eq by simp
  have q_neq_r': "q \<noteq> r_ktm M" using q_neq_r state_eq by simp
  have a_tail: "\<forall>j\<ge>k_ktm M. ?a j = bl_block (bl_ktm M)"
    using gamma c'_eq unfolding ae_tape_in_gamma_block_def by simp
  have rel_in: "((q, ofs, buf, dest, SS1), ?a,
                  (q, ofs, ?buf', dest, SS2), ?a, ?d)
                  \<in> ae_delta_ss1_ss2 M"
    unfolding ae_delta_ss1_ss2_def
    using q_in q_neq_t' q_neq_r' a_tail by auto
  have gamma_a: "\<forall>k. ?a k \<in> gamma_block (\<Gamma>_ktm M)"
    using gamma c'_eq unfolding ae_tape_in_gamma_block_def by simp
  have src_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, SS1)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using buf state_eq
    unfolding ae_buffer_in_gamma_block_def ae_valid_stage_def by simp
  have dst_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, ?buf', dest, SS2)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    by (rule ae_delta_ss1_ss2_dest_valid[OF rel_in gamma_a src_valid])
  have aed_in: "((q, ofs, buf, dest, SS1), ?a,
                  (q, ofs, ?buf', dest, SS2), ?a, ?d)
                  \<in> alphabet_enlarge_delta M"
    unfolding alphabet_enlarge_delta_def
    using rel_in gamma_a src_valid dst_valid by auto
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts"
    by (rule ext) auto
  let ?c'' = "KConfig (q, ofs, ?buf', dest, SS2) ts
                       (\<lambda>k. go_move (?d k) (n k))"
  have step_sub_raw:
    "(KConfig (q, ofs, buf, dest, SS1) ts n,
       KConfig (q, ofs, ?buf', dest, SS2)
         (\<lambda>k. (ts k)(n k := ?a k))
         (\<lambda>k. go_move (?d k) (n k)))
       \<in> ktm_step (ae_delta_ss1_ss2 M)"
  proof (rule ktm_step.intros)
    show "((q, ofs, buf, dest, SS1), ?a,
            (q, ofs, ?buf', dest, SS2), ?a, ?d)
            \<in> ae_delta_ss1_ss2 M" by (rule rel_in)
  qed
  have step_sub: "(c', ?c'') \<in> ktm_step (ae_delta_ss1_ss2 M)"
    using step_sub_raw c'_eq ts_unchanged by simp
  have step_full_raw:
    "(KConfig (q, ofs, buf, dest, SS1) ts n,
       KConfig (q, ofs, ?buf', dest, SS2)
         (\<lambda>k. (ts k)(n k := ?a k))
         (\<lambda>k. go_move (?d k) (n k)))
       \<in> ktm_step (alphabet_enlarge_delta M)"
  proof (rule ktm_step.intros)
    show "((q, ofs, buf, dest, SS1), ?a,
            (q, ofs, ?buf', dest, SS2), ?a, ?d)
            \<in> alphabet_enlarge_delta M" by (rule aed_in)
  qed
  have step_full: "(c', ?c'') \<in> ktm_step (alphabet_enlarge_delta M)"
    using step_full_raw c'_eq ts_unchanged by simp
  show ?thesis using step_sub step_full by blast
qed

lemma ae_step_ss2_ss3_exists:
  fixes M :: "('q, 'a) ktm"
    and c' :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes vM:      "valid_ktm M"
      and inv:     "ae_inv_ss2 M c'"
      and gamma:   "ae_tape_in_gamma_block M c'"
      and buf:     "ae_buffer_in_gamma_block M c'"
      and q_neq_t: "fst (ktc_state c') \<noteq> t_ktm M"
      and q_neq_r: "fst (ktc_state c') \<noteq> r_ktm M"
  shows "\<exists>c''. (c', c'') \<in> ktm_step (ae_delta_ss2_ss3 M)
                \<and> (c', c'') \<in> ktm_step (alphabet_enlarge_delta M)"
proof -
  obtain q ofs buf dest where
      state_eq: "ktc_state c' = (q, ofs, buf, dest, SS2)"
      and q_in: "q \<in> Q_ktm M"
    using inv unfolding ae_inv_ss2_def
    by (cases "ktc_state c'") auto
  obtain ts n where c'_eq: "c' = KConfig (q, ofs, buf, dest, SS2) ts n"
    using state_eq by (cases c') auto
  let ?a = "\<lambda>k. ts k (n k)"
  let ?buf' = "\<lambda>k. if k < k_ktm M
                     then (let (l, h, r) = buf k in
                            (if h = LE_block (le_ktm M)
                               then bl_block (bl_ktm M)
                               else ?a k,
                             h, r))
                     else init_buffer (le_ktm M) k"
  let ?d = "\<lambda>k. if k < k_ktm M
                  then (if (fst (snd (buf k))) = LE_block (le_ktm M)
                         then MoveN else MoveR)
                  else MoveN"
  have q_neq_t': "q \<noteq> t_ktm M" using q_neq_t state_eq by simp
  have q_neq_r': "q \<noteq> r_ktm M" using q_neq_r state_eq by simp
  have a_tail: "\<forall>j\<ge>k_ktm M. ?a j = bl_block (bl_ktm M)"
    using gamma c'_eq unfolding ae_tape_in_gamma_block_def by simp
  have rel_in: "((q, ofs, buf, dest, SS2), ?a,
                  (q, ofs, ?buf', dest, SS3), ?a, ?d)
                  \<in> ae_delta_ss2_ss3 M"
    unfolding ae_delta_ss2_ss3_def
    using q_in q_neq_t' q_neq_r' a_tail by auto
  have gamma_a: "\<forall>k. ?a k \<in> gamma_block (\<Gamma>_ktm M)"
    using gamma c'_eq unfolding ae_tape_in_gamma_block_def by simp
  have src_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, SS2)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using buf state_eq
    unfolding ae_buffer_in_gamma_block_def ae_valid_stage_def by simp
  have dst_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, ?buf', dest, SS3)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    by (rule ae_delta_ss2_ss3_dest_valid[OF vM rel_in gamma_a src_valid])
  have aed_in: "((q, ofs, buf, dest, SS2), ?a,
                  (q, ofs, ?buf', dest, SS3), ?a, ?d)
                  \<in> alphabet_enlarge_delta M"
    unfolding alphabet_enlarge_delta_def
    using rel_in gamma_a src_valid dst_valid by auto
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts"
    by (rule ext) auto
  let ?c'' = "KConfig (q, ofs, ?buf', dest, SS3) ts
                       (\<lambda>k. go_move (?d k) (n k))"
  have step_sub_raw:
    "(KConfig (q, ofs, buf, dest, SS2) ts n,
       KConfig (q, ofs, ?buf', dest, SS3)
         (\<lambda>k. (ts k)(n k := ?a k))
         (\<lambda>k. go_move (?d k) (n k)))
       \<in> ktm_step (ae_delta_ss2_ss3 M)"
  proof (rule ktm_step.intros)
    show "((q, ofs, buf, dest, SS2), ?a,
            (q, ofs, ?buf', dest, SS3), ?a, ?d)
            \<in> ae_delta_ss2_ss3 M" by (rule rel_in)
  qed
  have step_sub: "(c', ?c'') \<in> ktm_step (ae_delta_ss2_ss3 M)"
    using step_sub_raw c'_eq ts_unchanged by simp
  have step_full_raw:
    "(KConfig (q, ofs, buf, dest, SS2) ts n,
       KConfig (q, ofs, ?buf', dest, SS3)
         (\<lambda>k. (ts k)(n k := ?a k))
         (\<lambda>k. go_move (?d k) (n k)))
       \<in> ktm_step (alphabet_enlarge_delta M)"
  proof (rule ktm_step.intros)
    show "((q, ofs, buf, dest, SS2), ?a,
            (q, ofs, ?buf', dest, SS3), ?a, ?d)
            \<in> alphabet_enlarge_delta M" by (rule aed_in)
  qed
  have step_full: "(c', ?c'') \<in> ktm_step (alphabet_enlarge_delta M)"
    using step_full_raw c'_eq ts_unchanged by simp
  show ?thesis using step_sub step_full by blast
qed

lemma ae_step_ss3_ss4_exists:
  fixes M :: "('q, 'a) ktm"
    and c' :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes inv:     "ae_inv_ss3 M c'"
      and gamma:   "ae_tape_in_gamma_block M c'"
      and buf:     "ae_buffer_in_gamma_block M c'"
      and q_neq_t: "fst (ktc_state c') \<noteq> t_ktm M"
      and q_neq_r: "fst (ktc_state c') \<noteq> r_ktm M"
  shows "\<exists>c''. (c', c'') \<in> ktm_step (ae_delta_ss3_ss4 M)
                \<and> (c', c'') \<in> ktm_step (alphabet_enlarge_delta M)"
proof -
  obtain q ofs buf dest where
      state_eq: "ktc_state c' = (q, ofs, buf, dest, SS3)"
      and q_in: "q \<in> Q_ktm M"
    using inv unfolding ae_inv_ss3_def
    by (cases "ktc_state c'") auto
  obtain ts n where c'_eq: "c' = KConfig (q, ofs, buf, dest, SS3) ts n"
    using state_eq by (cases c') auto
  let ?a = "\<lambda>k. ts k (n k)"
  let ?d = "\<lambda>k. if k < k_ktm M then MoveR else MoveN"
  have q_neq_t': "q \<noteq> t_ktm M" using q_neq_t state_eq by simp
  have q_neq_r': "q \<noteq> r_ktm M" using q_neq_r state_eq by simp
  have a_tail: "\<forall>j\<ge>k_ktm M. ?a j = bl_block (bl_ktm M)"
    using gamma c'_eq unfolding ae_tape_in_gamma_block_def by simp
  have rel_in: "((q, ofs, buf, dest, SS3), ?a,
                  (q, ofs, buf, dest, SS4), ?a, ?d)
                  \<in> ae_delta_ss3_ss4 M"
    unfolding ae_delta_ss3_ss4_def
    using q_in q_neq_t' q_neq_r' a_tail by auto
  have gamma_a: "\<forall>k. ?a k \<in> gamma_block (\<Gamma>_ktm M)"
    using gamma c'_eq unfolding ae_tape_in_gamma_block_def by simp
  have src_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, SS3)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using buf state_eq
    unfolding ae_buffer_in_gamma_block_def ae_valid_stage_def by simp
  have dst_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, SS4)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    by (rule ae_delta_ss3_ss4_dest_valid[OF rel_in src_valid])
  have aed_in: "((q, ofs, buf, dest, SS3), ?a,
                  (q, ofs, buf, dest, SS4), ?a, ?d)
                  \<in> alphabet_enlarge_delta M"
    unfolding alphabet_enlarge_delta_def
    using rel_in gamma_a src_valid dst_valid by auto
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts"
    by (rule ext) auto
  let ?c'' = "KConfig (q, ofs, buf, dest, SS4) ts
                       (\<lambda>k. go_move (?d k) (n k))"
  have step_sub_raw:
    "(KConfig (q, ofs, buf, dest, SS3) ts n,
       KConfig (q, ofs, buf, dest, SS4)
         (\<lambda>k. (ts k)(n k := ?a k))
         (\<lambda>k. go_move (?d k) (n k)))
       \<in> ktm_step (ae_delta_ss3_ss4 M)"
  proof (rule ktm_step.intros)
    show "((q, ofs, buf, dest, SS3), ?a,
            (q, ofs, buf, dest, SS4), ?a, ?d)
            \<in> ae_delta_ss3_ss4 M" by (rule rel_in)
  qed
  have step_sub: "(c', ?c'') \<in> ktm_step (ae_delta_ss3_ss4 M)"
    using step_sub_raw c'_eq ts_unchanged by simp
  have step_full_raw:
    "(KConfig (q, ofs, buf, dest, SS3) ts n,
       KConfig (q, ofs, buf, dest, SS4)
         (\<lambda>k. (ts k)(n k := ?a k))
         (\<lambda>k. go_move (?d k) (n k)))
       \<in> ktm_step (alphabet_enlarge_delta M)"
  proof (rule ktm_step.intros)
    show "((q, ofs, buf, dest, SS3), ?a,
            (q, ofs, buf, dest, SS4), ?a, ?d)
            \<in> alphabet_enlarge_delta M" by (rule aed_in)
  qed
  have step_full: "(c', ?c'') \<in> ktm_step (alphabet_enlarge_delta M)"
    using step_full_raw c'_eq ts_unchanged by simp
  show ?thesis using step_sub step_full by blast
qed

text \<open>SS5\<open>\<rightarrow>\<close>SS6 step-existence.  The first of the write-back
  substeps' step-existence cluster (SS5\<open>\<rightarrow>\<close>SS6, SS6\<open>\<rightarrow>\<close>SS7,
  SS7\<open>\<rightarrow>\<close>SS8) — each writes a buffer cell back to the tape, so
  each needs \<open>ae_buffer_in_gamma_block\<close> to discharge the
  \<open>alphabet_enlarge_delta\<close> intersection guard's
  \<open>a' k \<in> gamma_block\<close> obligation.

  The SS5 action is total in its inputs (no halt-state
  precondition), so unlike the buffer-load substeps (SS1\<open>\<rightarrow>\<close>SS4)
  the lemma does not need \<open>q_neq_t\<close>/\<open>q_neq_r\<close> hypotheses.
  Halt routing kicks in only at SS8\<open>\<rightarrow>\<close>SS1.\<close>

lemma ae_step_ss5_ss6_exists:
  fixes M :: "('q, 'a) ktm"
    and c' :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes inv:   "ae_inv_ss5 M c'"
      and gamma: "ae_tape_in_gamma_block M c'"
      and buf:   "ae_buffer_in_gamma_block M c'"
  shows "\<exists>c''. (c', c'') \<in> ktm_step (ae_delta_ss5_ss6 M)
                \<and> (c', c'') \<in> ktm_step (alphabet_enlarge_delta M)"
proof -
  obtain q ofs buf dest where
      state_eq: "ktc_state c' = (q, ofs, buf, dest, SS5)"
      and q_in: "q \<in> Q_ktm M"
    using inv unfolding ae_inv_ss5_def
    by (cases "ktc_state c'") auto
  obtain ts n where c'_eq: "c' = KConfig (q, ofs, buf, dest, SS5) ts n"
    using state_eq by (cases c') auto
  let ?a  = "\<lambda>k. ts k (n k)"
  let ?a' = "\<lambda>k. if k < k_ktm M
                   then fst (ae_ss5_action (le_ktm M) (?a k) (buf k) (dest k))
                   else bl_block (bl_ktm M)"
  let ?d  = "\<lambda>k. if k < k_ktm M
                   then snd (ae_ss5_action (le_ktm M) (?a k) (buf k) (dest k))
                   else MoveN"
  have a_tail: "\<forall>j\<ge>k_ktm M. ?a j = bl_block (bl_ktm M)"
    using gamma c'_eq unfolding ae_tape_in_gamma_block_def by simp
  have rel_in: "((q, ofs, buf, dest, SS5), ?a,
                  (q, ofs, buf, dest, SS6), ?a', ?d)
                  \<in> ae_delta_ss5_ss6 M"
    unfolding ae_delta_ss5_ss6_def using q_in a_tail by auto
  have gamma_a: "\<forall>k. ?a k \<in> gamma_block (\<Gamma>_ktm M)"
    using gamma c'_eq unfolding ae_tape_in_gamma_block_def by simp
  have h_gamma: "\<forall>k. fst (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)"
    using buf state_eq unfolding ae_buffer_in_gamma_block_def by simp
  have act_gamma: "\<forall>k. fst (ae_ss5_action (le_ktm M) (?a k) (buf k) (dest k))
                        \<in> gamma_block (\<Gamma>_ktm M)"
  proof (intro allI)
    fix k
    obtain l h r where buf_k: "buf k = (l, h, r)"
      by (cases "buf k") auto
    have h_in_gamma: "h \<in> gamma_block (\<Gamma>_ktm M)"
      using spec[OF h_gamma, of k] buf_k by simp
    have a_k_in_gamma: "?a k \<in> gamma_block (\<Gamma>_ktm M)"
      using spec[OF gamma_a, of k] by simp
    show "fst (ae_ss5_action (le_ktm M) (?a k) (buf k) (dest k))
            \<in> gamma_block (\<Gamma>_ktm M)"
    proof (cases "?a k = LE_block (le_ktm M)")
      case True
      thus ?thesis using a_k_in_gamma buf_k by simp
    next
      case a_neq_le: False
      show ?thesis
      proof (cases "h = LE_block (le_ktm M)")
        case True
        thus ?thesis using a_neq_le a_k_in_gamma buf_k by simp
      next
        case False
        thus ?thesis using a_neq_le h_in_gamma buf_k by simp
      qed
    qed
  qed
  have gamma_a': "\<forall>k. ?a' k \<in> gamma_block (\<Gamma>_ktm M)"
  proof (intro allI)
    fix k
    show "?a' k \<in> gamma_block (\<Gamma>_ktm M)"
    proof (cases "k < k_ktm M")
      case True thus ?thesis using spec[OF act_gamma, of k] by simp
    next
      case False
      hence "?a' k = ?a k" using a_tail by simp
      thus ?thesis using spec[OF gamma_a, of k] by simp
    qed
  qed
  have act_le: "\<forall>k. fst (ae_ss5_action (le_ktm M) (?a k) (buf k) (dest k))
                        = LE_block (le_ktm M)
                    \<longrightarrow> ?a k = LE_block (le_ktm M)"
  proof (intro allI impI)
    fix k
    assume a'_le: "fst (ae_ss5_action (le_ktm M) (?a k) (buf k) (dest k))
                     = LE_block (le_ktm M)"
    obtain l h r where buf_k: "buf k = (l, h, r)"
      by (cases "buf k") auto
    show "?a k = LE_block (le_ktm M)"
    proof (cases "?a k = LE_block (le_ktm M)")
      case True thus ?thesis .
    next
      case a_neq_le: False
      show ?thesis
      proof (cases "h = LE_block (le_ktm M)")
        case True
        hence "fst (ae_ss5_action (le_ktm M) (?a k) (buf k) (dest k)) = ?a k"
          using a_neq_le buf_k by simp
        with a'_le a_neq_le show ?thesis by simp
      next
        case h_neq_le: False
        hence "fst (ae_ss5_action (le_ktm M) (?a k) (buf k) (dest k)) = h"
          using a_neq_le buf_k by simp
        with a'_le h_neq_le show ?thesis by simp
      qed
    qed
  qed
  have le_no_write: "\<forall>k. ?a' k = LE_block (le_ktm M)
                            \<longrightarrow> ?a k = LE_block (le_ktm M)"
  proof (intro allI impI)
    fix k
    assume a'_le: "?a' k = LE_block (le_ktm M)"
    show "?a k = LE_block (le_ktm M)"
    proof (cases "k < k_ktm M")
      case True
      hence "fst (ae_ss5_action (le_ktm M) (?a k) (buf k) (dest k))
               = LE_block (le_ktm M)"
        using a'_le by simp
      thus ?thesis using spec[OF act_le, of k] by simp
    next
      case False
      hence "?a k = ?a' k" using a_tail by simp
      thus ?thesis using a'_le by simp
    qed
  qed
  have src_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, SS5)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using buf state_eq
    unfolding ae_buffer_in_gamma_block_def ae_valid_stage_def by simp
  have dst_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, SS6)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    by (rule ae_delta_ss5_ss6_dest_valid[OF rel_in src_valid])
  have aed_in: "((q, ofs, buf, dest, SS5), ?a,
                  (q, ofs, buf, dest, SS6), ?a', ?d)
                  \<in> alphabet_enlarge_delta M"
    unfolding alphabet_enlarge_delta_def
    using rel_in gamma_a gamma_a' le_no_write src_valid dst_valid by auto
  let ?ts'  = "\<lambda>k. (ts k)(n k := ?a' k)"
  let ?n'   = "\<lambda>k. go_move (?d k) (n k)"
  let ?c''  = "KConfig (q, ofs, buf, dest, SS6) ?ts' ?n'"
  have step_sub_raw:
    "(KConfig (q, ofs, buf, dest, SS5) ts n,
       KConfig (q, ofs, buf, dest, SS6) ?ts' ?n')
       \<in> ktm_step (ae_delta_ss5_ss6 M)"
  proof (rule ktm_step.intros)
    show "((q, ofs, buf, dest, SS5), ?a,
            (q, ofs, buf, dest, SS6), ?a', ?d)
            \<in> ae_delta_ss5_ss6 M" by (rule rel_in)
  qed
  have step_sub: "(c', ?c'') \<in> ktm_step (ae_delta_ss5_ss6 M)"
    using step_sub_raw c'_eq by simp
  have step_full_raw:
    "(KConfig (q, ofs, buf, dest, SS5) ts n,
       KConfig (q, ofs, buf, dest, SS6) ?ts' ?n')
       \<in> ktm_step (alphabet_enlarge_delta M)"
  proof (rule ktm_step.intros)
    show "((q, ofs, buf, dest, SS5), ?a,
            (q, ofs, buf, dest, SS6), ?a', ?d)
            \<in> alphabet_enlarge_delta M" by (rule aed_in)
  qed
  have step_full: "(c', ?c'') \<in> ktm_step (alphabet_enlarge_delta M)"
    using step_full_raw c'_eq by simp
  show ?thesis using step_sub step_full by blast
qed

text \<open>Step-existence at SS6: writes the home block's previous
  contents in steady-state (\<open>ds = AE_Left\<close> writes \<open>r\<close>;
  otherwise writes \<open>l\<close>); LE-stage branches return \<open>a\<close> idempotently.
  The \<open>l\<close>/\<open>r\<close> branches force the per-substep
  \<open>ae_le_compat_ss6\<close> hypothesis: \<open>l\<close> may legitimately equal
  \<open>LE_block\<close> when \<open>p_start = 1\<close>, so structural discharge fails
  and the chain proof must thread the position-buffer
  correspondence in.\<close>

lemma ae_step_ss6_ss7_exists:
  fixes M :: "('q, 'a) ktm"
    and c' :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes inv:        "ae_inv_ss6 M c'"
      and gamma:      "ae_tape_in_gamma_block M c'"
      and buf:        "ae_buffer_in_gamma_block M c'"
      and le_compat:  "ae_le_compat_ss6 M c'"
  shows "\<exists>c''. (c', c'') \<in> ktm_step (ae_delta_ss6_ss7 M)
                \<and> (c', c'') \<in> ktm_step (alphabet_enlarge_delta M)"
proof -
  obtain q ofs buf dest where
      state_eq: "ktc_state c' = (q, ofs, buf, dest, SS6)"
      and q_in: "q \<in> Q_ktm M"
    using inv unfolding ae_inv_ss6_def
    by (cases "ktc_state c'") auto
  obtain ts n where c'_eq: "c' = KConfig (q, ofs, buf, dest, SS6) ts n"
    using state_eq by (cases c') auto
  let ?a  = "\<lambda>k. ts k (n k)"
  let ?a' = "\<lambda>k. if k < k_ktm M
                   then fst (ae_ss6_action (le_ktm M) (?a k) (buf k) (dest k))
                   else bl_block (bl_ktm M)"
  let ?d  = "\<lambda>k. if k < k_ktm M
                   then snd (ae_ss6_action (le_ktm M) (?a k) (buf k) (dest k))
                   else MoveN"
  have a_tail: "\<forall>j\<ge>k_ktm M. ?a j = bl_block (bl_ktm M)"
    using gamma c'_eq unfolding ae_tape_in_gamma_block_def by simp
  have rel_in: "((q, ofs, buf, dest, SS6), ?a,
                  (q, ofs, buf, dest, SS7), ?a', ?d)
                  \<in> ae_delta_ss6_ss7 M"
    unfolding ae_delta_ss6_ss7_def using q_in a_tail by auto
  have gamma_a: "\<forall>k. ?a k \<in> gamma_block (\<Gamma>_ktm M)"
    using gamma c'_eq unfolding ae_tape_in_gamma_block_def by simp
  have buf_gamma:
      "\<forall>k. fst (buf k) \<in> gamma_block (\<Gamma>_ktm M)
            \<and> fst (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)
            \<and> snd (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)"
    using buf state_eq unfolding ae_buffer_in_gamma_block_def by simp
  have act_gamma: "\<forall>k. fst (ae_ss6_action (le_ktm M) (?a k) (buf k) (dest k))
                        \<in> gamma_block (\<Gamma>_ktm M)"
  proof (intro allI)
    fix k
    obtain l h r where buf_k: "buf k = (l, h, r)"
      by (cases "buf k") auto
    have l_in: "l \<in> gamma_block (\<Gamma>_ktm M)"
      using spec[OF buf_gamma, of k] buf_k by simp
    have r_in: "r \<in> gamma_block (\<Gamma>_ktm M)"
      using spec[OF buf_gamma, of k] buf_k by simp
    have a_in: "?a k \<in> gamma_block (\<Gamma>_ktm M)"
      using spec[OF gamma_a, of k] by simp
    show "fst (ae_ss6_action (le_ktm M) (?a k) (buf k) (dest k))
            \<in> gamma_block (\<Gamma>_ktm M)"
    proof (cases "?a k = LE_block (le_ktm M)")
      case True thus ?thesis using a_in buf_k by simp
    next
      case a_neq_le: False
      show ?thesis
      proof (cases "h = LE_block (le_ktm M)")
        case True thus ?thesis using a_neq_le a_in buf_k by simp
      next
        case h_neq_le: False
        show ?thesis
        proof (cases "dest k = AE_Left")
          case True
          thus ?thesis using a_neq_le h_neq_le r_in buf_k by simp
        next
          case False
          thus ?thesis using a_neq_le h_neq_le l_in buf_k by simp
        qed
      qed
    qed
  qed
  have gamma_a': "\<forall>k. ?a' k \<in> gamma_block (\<Gamma>_ktm M)"
  proof (intro allI)
    fix k
    show "?a' k \<in> gamma_block (\<Gamma>_ktm M)"
    proof (cases "k < k_ktm M")
      case True thus ?thesis using spec[OF act_gamma, of k] by simp
    next
      case False
      hence "?a' k = ?a k" using a_tail by simp
      thus ?thesis using spec[OF gamma_a, of k] by simp
    qed
  qed
  have act_le: "\<forall>k<k_ktm M. fst (ae_ss6_action (le_ktm M) (?a k) (buf k) (dest k))
                        = LE_block (le_ktm M)
                    \<longrightarrow> ?a k = LE_block (le_ktm M)"
    using le_compat c'_eq unfolding ae_le_compat_ss6_def by simp
  have le_no_write: "\<forall>k. ?a' k = LE_block (le_ktm M)
                            \<longrightarrow> ?a k = LE_block (le_ktm M)"
  proof (intro allI impI)
    fix k
    assume a'_le: "?a' k = LE_block (le_ktm M)"
    show "?a k = LE_block (le_ktm M)"
    proof (cases "k < k_ktm M")
      case True
      hence "fst (ae_ss6_action (le_ktm M) (?a k) (buf k) (dest k))
               = LE_block (le_ktm M)"
        using a'_le by simp
      thus ?thesis using act_le[rule_format, OF True] by simp
    next
      case False
      hence "?a k = ?a' k" using a_tail by simp
      thus ?thesis using a'_le by simp
    qed
  qed
  have src_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, SS6)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using buf state_eq
    unfolding ae_buffer_in_gamma_block_def ae_valid_stage_def by simp
  have dst_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, SS7)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    by (rule ae_delta_ss6_ss7_dest_valid[OF rel_in src_valid])
  have aed_in: "((q, ofs, buf, dest, SS6), ?a,
                  (q, ofs, buf, dest, SS7), ?a', ?d)
                  \<in> alphabet_enlarge_delta M"
    unfolding alphabet_enlarge_delta_def
    using rel_in gamma_a gamma_a' le_no_write src_valid dst_valid by auto
  let ?ts'  = "\<lambda>k. (ts k)(n k := ?a' k)"
  let ?n'   = "\<lambda>k. go_move (?d k) (n k)"
  let ?c''  = "KConfig (q, ofs, buf, dest, SS7) ?ts' ?n'"
  have step_sub_raw:
    "(KConfig (q, ofs, buf, dest, SS6) ts n,
       KConfig (q, ofs, buf, dest, SS7) ?ts' ?n')
       \<in> ktm_step (ae_delta_ss6_ss7 M)"
  proof (rule ktm_step.intros)
    show "((q, ofs, buf, dest, SS6), ?a,
            (q, ofs, buf, dest, SS7), ?a', ?d)
            \<in> ae_delta_ss6_ss7 M" by (rule rel_in)
  qed
  have step_sub: "(c', ?c'') \<in> ktm_step (ae_delta_ss6_ss7 M)"
    using step_sub_raw c'_eq by simp
  have step_full_raw:
    "(KConfig (q, ofs, buf, dest, SS6) ts n,
       KConfig (q, ofs, buf, dest, SS7) ?ts' ?n')
       \<in> ktm_step (alphabet_enlarge_delta M)"
  proof (rule ktm_step.intros)
    show "((q, ofs, buf, dest, SS6), ?a,
            (q, ofs, buf, dest, SS7), ?a', ?d)
            \<in> alphabet_enlarge_delta M" by (rule aed_in)
  qed
  have step_full: "(c', ?c'') \<in> ktm_step (alphabet_enlarge_delta M)"
    using step_full_raw c'_eq by simp
  show ?thesis using step_sub step_full by blast
qed

text \<open>Step-existence at SS7: idempotent home re-write in
  steady-state (returns \<open>a\<close>) or right write in LE-stage
  (returns \<open>r\<close>); the LE-stage branch needs
  \<open>ae_le_compat_ss7\<close>.  Steady-state is structurally safe
  (\<open>a' = a\<close>); the LE-stage branch fires only when \<open>h = LE_block\<close>
  and \<open>a \<noteq> LE_block\<close>, returning \<open>r\<close>, where the chain proof
  must show \<open>r = LE_block\<close> contradicts the position invariant.\<close>

lemma ae_step_ss7_ss8_exists:
  fixes M :: "('q, 'a) ktm"
    and c' :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes inv:        "ae_inv_ss7 M c'"
      and gamma:      "ae_tape_in_gamma_block M c'"
      and buf:        "ae_buffer_in_gamma_block M c'"
      and le_compat:  "ae_le_compat_ss7 M c'"
  shows "\<exists>c''. (c', c'') \<in> ktm_step (ae_delta_ss7_ss8 M)
                \<and> (c', c'') \<in> ktm_step (alphabet_enlarge_delta M)"
proof -
  obtain q ofs buf dest where
      state_eq: "ktc_state c' = (q, ofs, buf, dest, SS7)"
      and q_in: "q \<in> Q_ktm M"
    using inv unfolding ae_inv_ss7_def
    by (cases "ktc_state c'") auto
  obtain ts n where c'_eq: "c' = KConfig (q, ofs, buf, dest, SS7) ts n"
    using state_eq by (cases c') auto
  let ?a  = "\<lambda>k. ts k (n k)"
  let ?a' = "\<lambda>k. if k < k_ktm M
                   then fst (ae_ss7_action (le_ktm M) (?a k) (buf k) (dest k))
                   else bl_block (bl_ktm M)"
  let ?d  = "\<lambda>k. if k < k_ktm M
                   then snd (ae_ss7_action (le_ktm M) (?a k) (buf k) (dest k))
                   else MoveN"
  have a_tail: "\<forall>j\<ge>k_ktm M. ?a j = bl_block (bl_ktm M)"
    using gamma c'_eq unfolding ae_tape_in_gamma_block_def by simp
  have rel_in: "((q, ofs, buf, dest, SS7), ?a,
                  (q, ofs, buf, dest, SS8), ?a', ?d)
                  \<in> ae_delta_ss7_ss8 M"
    unfolding ae_delta_ss7_ss8_def using q_in a_tail by auto
  have gamma_a: "\<forall>k. ?a k \<in> gamma_block (\<Gamma>_ktm M)"
    using gamma c'_eq unfolding ae_tape_in_gamma_block_def by simp
  have buf_gamma:
      "\<forall>k. fst (buf k) \<in> gamma_block (\<Gamma>_ktm M)
            \<and> fst (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)
            \<and> snd (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)"
    using buf state_eq unfolding ae_buffer_in_gamma_block_def by simp
  have act_gamma: "\<forall>k. fst (ae_ss7_action (le_ktm M) (?a k) (buf k) (dest k))
                        \<in> gamma_block (\<Gamma>_ktm M)"
  proof (intro allI)
    fix k
    obtain l h r where buf_k: "buf k = (l, h, r)"
      by (cases "buf k") auto
    have r_in: "r \<in> gamma_block (\<Gamma>_ktm M)"
      using spec[OF buf_gamma, of k] buf_k by simp
    have a_in: "?a k \<in> gamma_block (\<Gamma>_ktm M)"
      using spec[OF gamma_a, of k] by simp
    show "fst (ae_ss7_action (le_ktm M) (?a k) (buf k) (dest k))
            \<in> gamma_block (\<Gamma>_ktm M)"
    proof (cases "?a k = LE_block (le_ktm M)")
      case True thus ?thesis using a_in buf_k by simp
    next
      case a_neq_le: False
      show ?thesis
      proof (cases "h = LE_block (le_ktm M)")
        case True thus ?thesis using a_neq_le r_in buf_k by simp
      next
        case h_neq_le: False
        thus ?thesis using a_neq_le a_in buf_k by simp
      qed
    qed
  qed
  have gamma_a': "\<forall>k. ?a' k \<in> gamma_block (\<Gamma>_ktm M)"
  proof (intro allI)
    fix k
    show "?a' k \<in> gamma_block (\<Gamma>_ktm M)"
    proof (cases "k < k_ktm M")
      case True thus ?thesis using spec[OF act_gamma, of k] by simp
    next
      case False
      hence "?a' k = ?a k" using a_tail by simp
      thus ?thesis using spec[OF gamma_a, of k] by simp
    qed
  qed
  have act_le: "\<forall>k<k_ktm M. fst (ae_ss7_action (le_ktm M) (?a k) (buf k) (dest k))
                        = LE_block (le_ktm M)
                    \<longrightarrow> ?a k = LE_block (le_ktm M)"
    using le_compat c'_eq unfolding ae_le_compat_ss7_def by simp
  have le_no_write: "\<forall>k. ?a' k = LE_block (le_ktm M)
                            \<longrightarrow> ?a k = LE_block (le_ktm M)"
  proof (intro allI impI)
    fix k
    assume a'_le: "?a' k = LE_block (le_ktm M)"
    show "?a k = LE_block (le_ktm M)"
    proof (cases "k < k_ktm M")
      case True
      hence "fst (ae_ss7_action (le_ktm M) (?a k) (buf k) (dest k))
               = LE_block (le_ktm M)"
        using a'_le by simp
      thus ?thesis using act_le[rule_format, OF True] by simp
    next
      case False
      hence "?a k = ?a' k" using a_tail by simp
      thus ?thesis using a'_le by simp
    qed
  qed
  have src_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, SS7)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using buf state_eq
    unfolding ae_buffer_in_gamma_block_def ae_valid_stage_def by simp
  have dst_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, SS8)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    by (rule ae_delta_ss7_ss8_dest_valid[OF rel_in src_valid])
  have aed_in: "((q, ofs, buf, dest, SS7), ?a,
                  (q, ofs, buf, dest, SS8), ?a', ?d)
                  \<in> alphabet_enlarge_delta M"
    unfolding alphabet_enlarge_delta_def
    using rel_in gamma_a gamma_a' le_no_write src_valid dst_valid by auto
  let ?ts'  = "\<lambda>k. (ts k)(n k := ?a' k)"
  let ?n'   = "\<lambda>k. go_move (?d k) (n k)"
  let ?c''  = "KConfig (q, ofs, buf, dest, SS8) ?ts' ?n'"
  have step_sub_raw:
    "(KConfig (q, ofs, buf, dest, SS7) ts n,
       KConfig (q, ofs, buf, dest, SS8) ?ts' ?n')
       \<in> ktm_step (ae_delta_ss7_ss8 M)"
  proof (rule ktm_step.intros)
    show "((q, ofs, buf, dest, SS7), ?a,
            (q, ofs, buf, dest, SS8), ?a', ?d)
            \<in> ae_delta_ss7_ss8 M" by (rule rel_in)
  qed
  have step_sub: "(c', ?c'') \<in> ktm_step (ae_delta_ss7_ss8 M)"
    using step_sub_raw c'_eq by simp
  have step_full_raw:
    "(KConfig (q, ofs, buf, dest, SS7) ts n,
       KConfig (q, ofs, buf, dest, SS8) ?ts' ?n')
       \<in> ktm_step (alphabet_enlarge_delta M)"
  proof (rule ktm_step.intros)
    show "((q, ofs, buf, dest, SS7), ?a,
            (q, ofs, buf, dest, SS8), ?a', ?d)
            \<in> alphabet_enlarge_delta M" by (rule aed_in)
  qed
  have step_full: "(c', ?c'') \<in> ktm_step (alphabet_enlarge_delta M)"
    using step_full_raw c'_eq by simp
  show ?thesis using step_sub step_full by blast
qed

text \<open>Step-existence at SS8: end of the write-back phase.  The
  action selects \<open>l\<close>, \<open>r\<close>, or \<open>a\<close> per stage-kind \<open>\<times>\<close> dest;
  the next stage is determined by halt routing — \<open>q \<in> {t, r}\<close>
  routes to \<open>init_stage le\<close>, otherwise re-enters SS1 with
  buffer + offset preserved and dest reset to \<open>init_dest\<close>.
  Step-existence is uniform across the halt branch: both
  branches are total in the action's input.  The chain-level
  forward-simulation argument splits halt-emission from cycle
  continuation downstream, but step-existence itself does not
  require a non-halting hypothesis.\<close>

lemma ae_step_ss8_ss1_exists:
  fixes M :: "('q, 'a) ktm"
    and c' :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes vM:         "valid_ktm M"
      and inv:        "ae_inv_ss8 M c'"
      and gamma:      "ae_tape_in_gamma_block M c'"
      and buf:        "ae_buffer_in_gamma_block M c'"
      and le_compat:  "ae_le_compat_ss8 M c'"
  shows "\<exists>c''. (c', c'') \<in> ktm_step (ae_delta_ss8_ss1 M)
                \<and> (c', c'') \<in> ktm_step (alphabet_enlarge_delta M)"
proof -
  obtain q ofs buf dest where
      state_eq: "ktc_state c' = (q, ofs, buf, dest, SS8)"
      and q_in: "q \<in> Q_ktm M"
    using inv unfolding ae_inv_ss8_def
    by (cases "ktc_state c'") auto
  obtain ts n where c'_eq: "c' = KConfig (q, ofs, buf, dest, SS8) ts n"
    using state_eq by (cases c') auto
  let ?a  = "\<lambda>k. ts k (n k)"
  let ?a' = "\<lambda>k. if k < k_ktm M
                   then fst (ae_ss8_action (le_ktm M) (?a k) (buf k) (dest k))
                   else bl_block (bl_ktm M)"
  let ?d  = "\<lambda>k. if k < k_ktm M
                   then snd (ae_ss8_action (le_ktm M) (?a k) (buf k) (dest k))
                   else MoveN"
  let ?stage' = "if q \<in> {t_ktm M, r_ktm M}
                 then init_stage (le_ktm M)
                 else (ofs, buf, init_dest, SS1)"
  have a_tail: "\<forall>j\<ge>k_ktm M. ?a j = bl_block (bl_ktm M)"
    using gamma c'_eq unfolding ae_tape_in_gamma_block_def by simp
  have rel_in: "((q, ofs, buf, dest, SS8), ?a,
                  (q, ?stage'), ?a', ?d)
                  \<in> ae_delta_ss8_ss1 M"
    unfolding ae_delta_ss8_ss1_def init_stage_def
    using q_in a_tail by auto
  have gamma_a: "\<forall>k. ?a k \<in> gamma_block (\<Gamma>_ktm M)"
    using gamma c'_eq unfolding ae_tape_in_gamma_block_def by simp
  have buf_gamma:
      "\<forall>k. fst (buf k) \<in> gamma_block (\<Gamma>_ktm M)
            \<and> fst (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)
            \<and> snd (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)"
    using buf state_eq unfolding ae_buffer_in_gamma_block_def by simp
  have act_gamma: "\<forall>k. fst (ae_ss8_action (le_ktm M) (?a k) (buf k) (dest k))
                        \<in> gamma_block (\<Gamma>_ktm M)"
  proof (intro allI)
    fix k
    obtain l h r where buf_k: "buf k = (l, h, r)"
      by (cases "buf k") auto
    have l_in: "l \<in> gamma_block (\<Gamma>_ktm M)"
      using spec[OF buf_gamma, of k] buf_k by simp
    have r_in: "r \<in> gamma_block (\<Gamma>_ktm M)"
      using spec[OF buf_gamma, of k] buf_k by simp
    have a_in: "?a k \<in> gamma_block (\<Gamma>_ktm M)"
      using spec[OF gamma_a, of k] by simp
    show "fst (ae_ss8_action (le_ktm M) (?a k) (buf k) (dest k))
            \<in> gamma_block (\<Gamma>_ktm M)"
    proof (cases "?a k = LE_block (le_ktm M)")
      case True thus ?thesis using a_in buf_k by simp
    next
      case a_neq_le: False
      show ?thesis
      proof (cases "h = LE_block (le_ktm M)")
        case True
        show ?thesis
        proof (cases "dest k = AE_Right")
          case True thus ?thesis
            using a_neq_le \<open>h = LE_block (le_ktm M)\<close> r_in buf_k by simp
        next
          case False thus ?thesis
            using a_neq_le \<open>h = LE_block (le_ktm M)\<close> a_in buf_k by simp
        qed
      next
        case h_neq_le: False
        show ?thesis
        proof (cases "dest k")
          case AE_Left thus ?thesis
            using a_neq_le h_neq_le l_in buf_k by simp
        next
          case AE_Home thus ?thesis
            using a_neq_le h_neq_le r_in buf_k by simp
        next
          case AE_Right thus ?thesis
            using a_neq_le h_neq_le r_in buf_k by simp
        qed
      qed
    qed
  qed
  have gamma_a': "\<forall>k. ?a' k \<in> gamma_block (\<Gamma>_ktm M)"
  proof (intro allI)
    fix k
    show "?a' k \<in> gamma_block (\<Gamma>_ktm M)"
    proof (cases "k < k_ktm M")
      case True thus ?thesis using spec[OF act_gamma, of k] by simp
    next
      case False
      hence "?a' k = ?a k" using a_tail by simp
      thus ?thesis using spec[OF gamma_a, of k] by simp
    qed
  qed
  have act_le: "\<forall>k<k_ktm M. fst (ae_ss8_action (le_ktm M) (?a k) (buf k) (dest k))
                        = LE_block (le_ktm M)
                    \<longrightarrow> ?a k = LE_block (le_ktm M)"
    using le_compat c'_eq unfolding ae_le_compat_ss8_def by simp
  have le_no_write: "\<forall>k. ?a' k = LE_block (le_ktm M)
                            \<longrightarrow> ?a k = LE_block (le_ktm M)"
  proof (intro allI impI)
    fix k
    assume a'_le: "?a' k = LE_block (le_ktm M)"
    show "?a k = LE_block (le_ktm M)"
    proof (cases "k < k_ktm M")
      case True
      hence "fst (ae_ss8_action (le_ktm M) (?a k) (buf k) (dest k))
               = LE_block (le_ktm M)"
        using a'_le by simp
      thus ?thesis using act_le[rule_format, OF True] by simp
    next
      case False
      hence "?a k = ?a' k" using a_tail by simp
      thus ?thesis using a'_le by simp
    qed
  qed
  have src_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, SS8)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using buf state_eq
    unfolding ae_buffer_in_gamma_block_def ae_valid_stage_def by simp
  have dst_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ?stage')
                              :: 'q \<times> ('a, 'c) ae_stage))"
    by (rule ae_delta_ss8_ss1_dest_valid[OF vM rel_in src_valid])
  have aed_in: "((q, ofs, buf, dest, SS8), ?a,
                  (q, ?stage'), ?a', ?d)
                  \<in> alphabet_enlarge_delta M"
    unfolding alphabet_enlarge_delta_def
    using rel_in gamma_a gamma_a' le_no_write src_valid dst_valid by auto
  let ?ts'  = "\<lambda>k. (ts k)(n k := ?a' k)"
  let ?n'   = "\<lambda>k. go_move (?d k) (n k)"
  let ?c''  = "KConfig (q, ?stage') ?ts' ?n'"
  have step_sub_raw:
    "(KConfig (q, ofs, buf, dest, SS8) ts n,
       KConfig (q, ?stage') ?ts' ?n')
       \<in> ktm_step (ae_delta_ss8_ss1 M)"
  proof (rule ktm_step.intros)
    show "((q, ofs, buf, dest, SS8), ?a,
            (q, ?stage'), ?a', ?d)
            \<in> ae_delta_ss8_ss1 M" by (rule rel_in)
  qed
  have step_sub: "(c', ?c'') \<in> ktm_step (ae_delta_ss8_ss1 M)"
    using step_sub_raw c'_eq by simp
  have step_full_raw:
    "(KConfig (q, ofs, buf, dest, SS8) ts n,
       KConfig (q, ?stage') ?ts' ?n')
       \<in> ktm_step (alphabet_enlarge_delta M)"
  proof (rule ktm_step.intros)
    show "((q, ofs, buf, dest, SS8), ?a,
            (q, ?stage'), ?a', ?d)
            \<in> alphabet_enlarge_delta M" by (rule aed_in)
  qed
  have step_full: "(c', ?c'') \<in> ktm_step (alphabet_enlarge_delta M)"
    using step_full_raw c'_eq by simp
  show ?thesis using step_sub step_full by blast
qed

subsubsection \<open>Encoder helpers\<close>

text \<open>Encoder structural helpers.  \<open>length_encode_input\<close> and
  \<open>encode_input_nth\<close> unfold the encoder's definition into the
  shape that downstream proofs about block content cite.\<close>

lemma length_encode_input:
  "length (encode_input bl u :: ('c :: enum \<Rightarrow> 'a) list)
     = (length u + card (UNIV :: 'c set) - 1) div card (UNIV :: 'c set)"
  by (simp add: encode_input_def Let_def)

lemma encode_input_nth:
  fixes u :: "'a list"
    and x :: "'c :: enum"
  assumes "i < length (encode_input bl u :: ('c \<Rightarrow> 'a) list)"
  shows "((encode_input bl u :: ('c \<Rightarrow> 'a) list) ! i) x
           = (let j = i * card (UNIV :: 'c set) + c_idx x
                in if j < length u then u ! j else bl)"
proof -
  let ?c = "card (UNIV :: 'c set)"
  have len_eq: "length (encode_input bl u :: ('c \<Rightarrow> 'a) list)
                  = (length u + ?c - 1) div ?c"
    by (simp add: encode_input_def Let_def)
  hence i_lt: "i < (length u + ?c - 1) div ?c" using assms by simp
  show ?thesis
    unfolding encode_input_def Let_def
    using i_lt by simp
qed

text \<open>Index range for \<open>c_idx\<close>: every element of \<open>'c :: enum\<close>
  has an index strictly less than the length of the canonical
  enumeration, and the enumeration retrieves that element back.\<close>

lemma c_idx_in_range:
  fixes x :: "'c :: enum"
  shows "c_idx x < length (enum_class.enum :: 'c list)"
    and "(enum_class.enum :: 'c list) ! c_idx x = x"
proof -
  have ex_unique: "\<exists>!i. i < length (enum_class.enum :: 'c list)
                         \<and> (enum_class.enum :: 'c list) ! i = x"
  proof -
    have x_in: "x \<in> set (enum_class.enum :: 'c list)"
      using enum_class.UNIV_enum by blast
    then obtain i where
      i_lt: "i < length (enum_class.enum :: 'c list)" and
      i_eq: "(enum_class.enum :: 'c list) ! i = x"
      by (auto simp: in_set_conv_nth)
    moreover have "\<And>j. j < length (enum_class.enum :: 'c list)
                    \<Longrightarrow> (enum_class.enum :: 'c list) ! j = x
                    \<Longrightarrow> j = i"
      using i_lt i_eq enum_class.enum_distinct
      by (metis nth_eq_iff_index_eq)
    ultimately show ?thesis by blast
  qed
  have idx_eq: "c_idx x < length (enum_class.enum :: 'c list)
                \<and> (enum_class.enum :: 'c list) ! c_idx x = x"
    unfolding c_idx_def using theI'[OF ex_unique] .
  show "c_idx x < length (enum_class.enum :: 'c list)" using idx_eq ..
  show "(enum_class.enum :: 'c list) ! c_idx x = x" using idx_eq ..
qed

lemma c_idx_lt_card: "c_idx (x :: 'c :: enum) < card (UNIV :: 'c set)"
proof -
  have "card (UNIV :: 'c set) = length (enum_class.enum :: 'c list)"
    using enum_class.UNIV_enum enum_class.enum_distinct
    by (metis distinct_card length_remdups_card_conv set_remdups)
  thus ?thesis using c_idx_in_range(1) by simp
qed

lemma card_eq_length_enum:
  "card (UNIV :: 'c :: enum set) = length (enum_class.enum :: 'c list)"
  using enum_class.UNIV_enum enum_class.enum_distinct
  by (metis distinct_card length_remdups_card_conv set_remdups)

lemma c_idx_enum_nth:
  fixes i :: nat
  assumes "i < length (enum_class.enum :: 'c :: enum list)"
  shows "c_idx ((enum_class.enum :: 'c list) ! i) = i"
proof -
  let ?xs = "enum_class.enum :: 'c list"
  have nth_eq: "?xs ! c_idx (?xs ! i) = ?xs ! i"
    using c_idx_in_range(2) .
  have lt: "c_idx (?xs ! i) < length ?xs"
    by (rule c_idx_in_range(1))
  show ?thesis
    using nth_eq lt assms enum_class.enum_distinct
    by (metis nth_eq_iff_index_eq)
qed

end
