theory Wrap_Defs
  imports Wrap_Base "Multitape_TM_Substrate.Multitape_Origin_Float"
begin

section \<open>Faithful (k-tape) encoding wrap: plant-\<open>le\<close> variant (HU 12.4)\<close>

text \<open>Reaching faithful \<open>k\<close> tapes for the super-linear speed-up
  \<^cite>\<open>\<open>Theorem 12.3\<close> in "Hopcroft1979:introduction"\<close> by
  \<^emph>\<open>rewinding\<close> the reused input tape costs a \<open>~2n\<close> setup that the
  super-linear growth hypothesis absorbs.  Theorem 12.4's
  tight \<open>(1+\<epsilon>)n\<close> bound cannot absorb it, so this variant avoids the
  rewind of the input tape entirely: it plants a fresh \<open>le\<close> at the input
  head's final position, \<^emph>\<open>floating\<close> the origin (the spent raw input to
  its left becomes unreachable, penned off by clause 1).

  Only the reset phase differs from the transpose wrap.  The storage
  tape (physical @{text 1}, carrying M's tape 0 = the encoded input) is
  still rewound to its \<open>le\<close> --- but that is only \<open>\<lceil>n/c\<rceil>\<close> cells (the
  encoded length), the \<open>\<epsilon>\<cdot>n\<close> term --- via the generic single-tape
  rewind @{const wrap_rewind_loop_delta_gen}.  The input tape (physical
  @{text 0}, becoming M's tape 1) is \<^emph>\<open>not\<close> rewound: the rewind-done
  step plants \<open>le\<close> on it and hands over to @{text W_Disp}.  Everything
  else --- the six transpose encoder families, the transposed run, the
  dispatch --- is reused verbatim.

  The planted \<open>le\<close> makes the wrap \<^emph>\<open>not\<close> @{const le_unique} (it writes
  \<open>le\<close> where it did not read \<open>le\<close>); it remains @{const valid_mttm}, since
  clause 1 constrains only transitions that \<^emph>\<open>read\<close> \<open>le\<close>.  The engine
  is then run from a floated-origin init config, bridged back to the
  proper @{const init_config_mttm} by the origin-float lemmas of
  @{theory Multitape_TM_Substrate.Multitape_Origin_Float}.\<close>

subsection \<open>The plant-\<open>le\<close> reset done step\<close>

text \<open>Rewind-done for the plant variant: fires when the storage tape
  (index @{text "Suc 0"}) reads \<open>le\<close> (its cell 0, reached by the generic
  rewind loop), and in the same transition writes \<open>le\<close> on the input tape
  (index @{text 0}) at its current head --- the plant --- handing over to
  @{text W_Disp}.  No head moves.  This is the sole wrap-B-specific reset
  family; the loop is the generic @{const wrap_rewind_loop_delta_gen}.\<close>

definition wrap_plant_done_delta ::
  "('q, 'b) mttm \<Rightarrow> 'a set
   \<Rightarrow> (('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> ('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> (nat \<Rightarrow> dir)) set"
where
  "wrap_plant_done_delta M \<Sigma>u =
     { (W_Reset, sym, W_Disp,
        (\<lambda>t. if t = 0 then Enc (le_tm M) else sym t),
        \<lambda>_. dir.N)
       | sym.
           sym (Suc 0) = Enc (le_tm M)
           \<and> (\<forall>i\<ge>k_tm M. sym i = Enc (bl_tm M))
           \<and> sym \<in> UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_tm M }"

subsection \<open>The plant-\<open>le\<close> combinator\<close>

text \<open>The plant wrap's transition relation: the six transpose encoder
  families at @{term "K = k_tm M"}, the transposed run and dispatch, and
  --- for the reset --- the generic single-tape storage rewind (loop)
  plus the plant-done step.\<close>

definition wrap_delta ::
  "('q, 'b) mttm \<Rightarrow> ('a list \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a set
   \<Rightarrow> (('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> ('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> (nat \<Rightarrow> dir)) set"
where
  "wrap_delta M pack c \<Sigma>u =
     wrap_init_delta_gen (k_tm M) M
     \<union> wrap_buf_extend_delta_gen (k_tm M) M c \<Sigma>u
     \<union> wrap_buf_close_delta_gen (k_tm M) M pack c \<Sigma>u
     \<union> wrap_buf_empty_end_delta_gen (k_tm M) M \<Sigma>u
     \<union> wrap_buf_nonempty_end_delta_gen (k_tm M) M pack c \<Sigma>u
     \<union> wrap_rewind_loop_delta_gen W_Reset (Suc 0) (k_tm M) M \<Sigma>u
     \<union> wrap_plant_done_delta M \<Sigma>u
     \<union> wrap_disp_delta_gen (k_tm M) M \<Sigma>u
     \<union> wrap_run_delta M \<Sigma>u"

text \<open>The faithful \<open>k\<close>-tape plant-\<open>le\<close> encoding wrap: transition relation
  @{const wrap_delta} at tape count @{term "k_tm M"}, reusing the wrap
  state set (no new state --- the plant folds into the reset-done step).
  Well-formed only when @{term "k_tm M \<ge> 2"}, as for the transpose wrap.\<close>

fun encoding_wrap ::
  "('q, 'b) mttm \<Rightarrow> ('a list \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a set
   \<Rightarrow> (('q, 'a, 'b) wrap_state, ('a, 'b) wrap_alphabet) mttm"
where
  "encoding_wrap M pack c \<Sigma>u =
     MTTM
       (wrap_state_set M c \<Sigma>u)
       (Raw ` \<Sigma>u)
       (Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_tm M)
       (Enc (bl_tm M))
       (Enc (le_tm M))
       (wrap_delta M pack c \<Sigma>u)
       W_Init
       (W_Run (t_tm M))
       W_Rej
       (k_tm M)"


subsection \<open>Well-formedness of the plant-\<open>le\<close> wrap\<close>

text \<open>Phase-family case split for @{const wrap_delta}: a transition
  belongs to exactly one of the nine builders --- the six
  boundary-parameterised encoder families at @{term "k_tm M"}, the generic
  single-tape storage rewind loop, the plant-\<open>le\<close> rewind-done step, and the
  transposed run.\<close>

lemma wrap_delta_cases:
  assumes "(q, a, q', a', d) \<in> wrap_delta M pack c \<Sigma>u"
  obtains
    (init) "(q, a, q', a', d) \<in> wrap_init_delta_gen (k_tm M) M"
  | (ext) "(q, a, q', a', d) \<in> wrap_buf_extend_delta_gen (k_tm M) M c \<Sigma>u"
  | (close) "(q, a, q', a', d) \<in> wrap_buf_close_delta_gen (k_tm M) M pack c \<Sigma>u"
  | (eend) "(q, a, q', a', d) \<in> wrap_buf_empty_end_delta_gen (k_tm M) M \<Sigma>u"
  | (nend) "(q, a, q', a', d) \<in> wrap_buf_nonempty_end_delta_gen (k_tm M) M pack c \<Sigma>u"
  | (rloop) "(q, a, q', a', d)
               \<in> wrap_rewind_loop_delta_gen W_Reset (Suc 0) (k_tm M) M \<Sigma>u"
  | (rdone) "(q, a, q', a', d) \<in> wrap_plant_done_delta M \<Sigma>u"
  | (disp) "(q, a, q', a', d) \<in> wrap_disp_delta_gen (k_tm M) M \<Sigma>u"
  | (run) "(q, a, q', a', d) \<in> wrap_run_delta M \<Sigma>u"
  using assms unfolding wrap_delta_def by blast

text \<open>Obligation 1 --- well-formedness of the faithful @{text k}-tape
  plant-\<open>le\<close> wrap at tape count @{term "k_tm M"}.  Hypotheses:
  @{term "2 \<le> k_tm M"}, @{term "valid_mttm M"}, and
  @{term "le_tm M \<noteq> bl_tm M"} (the storage rewind passes @{text bl}
  through unchanged, and the plant writes @{text le}, so the
  no-spurious-LE obligations need them distinct).  It does \<^emph>\<open>not\<close> require
  @{const le_unique} of the input, and --- crucially --- the resulting wrap
  is itself \<^emph>\<open>not\<close> @{const le_unique}: the plant-done step writes @{text le}
  on physical tape @{text 0} without reading it there.  That is legal for
  @{const valid_mttm}, whose clause 1 (obligation 14 below) constrains only
  transitions that \<^emph>\<open>read\<close> @{text le}; the dropped clause 2 was exactly the
  no-planting rule.\<close>

lemma wrap_wf:
  assumes valM: "valid_mttm M"
      and le_ne_bl: "le_tm M \<noteq> bl_tm M"
      and finSu: "finite \<Sigma>u"
      and c_pos: "0 < c"
      and k2: "2 \<le> k_tm M"
  shows "valid_mttm (encoding_wrap M pack c \<Sigma>u)"
proof -
  have eq:
    "encoding_wrap M pack c \<Sigma>u =
       MTTM (wrap_state_set M c \<Sigma>u)
            (Raw ` \<Sigma>u)
            (Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_tm M)
            (Enc (bl_tm M))
            (Enc (le_tm M))
            (wrap_delta M pack c \<Sigma>u)
            W_Init
            (W_Run (t_tm M))
            W_Rej
            (k_tm M)"
    by simp
  show ?thesis
    unfolding eq valid_mttm.simps
  proof (intro conjI)
    \<comment> \<open>(1) finite Q'\<close>
    show "finite (wrap_state_set M c \<Sigma>u)"
      by (rule finite_wrap_state_set[OF valM finSu])
    \<comment> \<open>(2) finite \<open>\<Gamma>\<close>'\<close>
    show "finite (Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_tm M)"
      using finSu valid_mttm_finite_Gamma[OF valM] by simp
    \<comment> \<open>(3) \<open>\<Sigma>\<close>' \<open>\<subseteq>\<close> \<open>\<Gamma>\<close>'\<close>
    show "Raw ` \<Sigma>u \<subseteq> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_tm M"
      by blast
    \<comment> \<open>(4) start in Q'\<close>
    show "W_Init \<in> wrap_state_set M c \<Sigma>u"
      unfolding wrap_state_set_def by simp
    \<comment> \<open>(5) accept in Q'\<close>
    show "W_Run (t_tm M) \<in> wrap_state_set M c \<Sigma>u"
      using valid_mttm_t_in_Q[OF valM]
      unfolding wrap_state_set_def by simp
    \<comment> \<open>(6) reject in Q'\<close>
    show "W_Rej \<in> wrap_state_set M c \<Sigma>u"
      unfolding wrap_state_set_def by simp
    \<comment> \<open>(7a) bl in \<open>\<Gamma>\<close>'\<close>
    show "Enc (bl_tm M) \<in> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_tm M"
      using valid_mttm_blank_in_Gamma[OF valM] by blast
    \<comment> \<open>(7b) bl not in \<open>\<Sigma>\<close>'\<close>
    show "Enc (bl_tm M) \<notin> Raw ` \<Sigma>u"
      by auto
    \<comment> \<open>(8a) le in \<open>\<Gamma>\<close>'\<close>
    show "Enc (le_tm M) \<in> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_tm M"
      using valid_mttm_LE_in_Gamma[OF valM] by blast
    \<comment> \<open>(8b) le not in \<open>\<Sigma>\<close>'\<close>
    show "Enc (le_tm M) \<notin> Raw ` \<Sigma>u"
      by auto
    \<comment> \<open>(11) accept \<open>\<noteq>\<close> reject\<close>
    show "W_Run (t_tm M) \<noteq> W_Rej"
      by simp
    \<comment> \<open>(12) \<open>0 < k\<close>: the plant wrap keeps M's tape count.\<close>
    show "0 < k_tm M"
      using valid_mttm_k_pos[OF valM] by simp
    \<comment> \<open>(13) \<open>\<delta>\<close>-shape: source / dest / read / write range typing.  The
       plant writes @{text "Enc le"} on tape @{text 0}, which is in range by
       @{thm valid_mttm_LE_in_Gamma}.\<close>
    show "wrap_delta M pack c \<Sigma>u
            \<subseteq> (wrap_state_set M c \<Sigma>u - {W_Run (t_tm M), W_Rej})
              \<times> (UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_tm M)
              \<times> wrap_state_set M c \<Sigma>u
              \<times> (UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_tm M)
              \<times> (UNIV \<rightarrow> UNIV)"
      unfolding wrap_delta_def
                wrap_init_delta_gen_def wrap_buf_extend_delta_gen_def
                wrap_buf_close_delta_gen_def wrap_buf_empty_end_delta_gen_def
                wrap_buf_nonempty_end_delta_gen_def
                wrap_rewind_loop_delta_gen_def
                wrap_plant_done_delta_def
                wrap_disp_delta_gen_def wrap_run_delta_def
                wrap_state_set_def
      using c_pos valid_mttm_t_in_Q[OF valM] valid_mttm_s_in_Q[OF valM]
            valid_mttm_LE_in_Gamma[OF valM] valid_mttm_blank_in_Gamma[OF valM]
            valid_mttm_delta_set[OF valM]
            valid_mttm_Sigma_sub_Gamma[OF valM]
      by (fastforce split: nat.split if_splits)
    \<comment> \<open>(14) \<open>\<delta>\<close>LE-preservation: read LE \<open>\<Longrightarrow>\<close> write LE and dir \<open>\<in>\<close> {N, R}.
       The plant-done step writes LE on tape @{text 0} regardless of what it
       read there --- legal, since this obligation only fires when the read
       cell already \<^emph>\<open>is\<close> LE, and then the plant writes LE anyway.  The
       rewind loop only moves the storage head (@{text "Suc 0"}), whose
       read cannot be LE (its guard), so no LE-read cell moves.\<close>
    show "\<forall>q a q' a' d k.
            (q, a, q', a', d) \<in> wrap_delta M pack c \<Sigma>u \<longrightarrow>
            a k = Enc (le_tm M) \<longrightarrow>
            a' k = Enc (le_tm M) \<and> d k \<in> {dir.N, dir.R}"
    proof (intro allI impI)
      fix q a q' a' d k
      assume in_\<delta>: "(q, a, q', a', d) \<in> wrap_delta M pack c \<Sigma>u"
         and LE: "a k = Enc (le_tm M)"
      from in_\<delta> show "a' k = Enc (le_tm M) \<and> d k \<in> {dir.N, dir.R}"
      proof (cases rule: wrap_delta_cases)
        case init
        thus ?thesis using LE unfolding wrap_init_delta_gen_def
          by (auto split: nat.splits if_splits)
      next
        case ext
        thus ?thesis using LE unfolding wrap_buf_extend_delta_gen_def
          by (auto split: nat.splits)
      next
        case close
        thus ?thesis using LE unfolding wrap_buf_close_delta_gen_def
          by (fastforce split: nat.splits if_splits)
      next
        case eend
        thus ?thesis using LE unfolding wrap_buf_empty_end_delta_gen_def
          by (auto split: nat.splits)
      next
        case nend
        thus ?thesis using LE unfolding wrap_buf_nonempty_end_delta_gen_def
          by (fastforce split: nat.splits if_splits)
      next
        case rloop
        \<comment> \<open>Storage rewind: write = read, so LE is preserved; the only moving
           head is @{text "Suc 0"}, whose guard forbids reading LE, so a
           LE-read cell (necessarily @{text "k \<noteq> Suc 0"}) stays stationary.\<close>
        thus ?thesis using LE unfolding wrap_rewind_loop_delta_gen_def
          by (auto split: if_splits)
      next
        case rdone
        \<comment> \<open>Plant-done: read = write on every tape except @{text 0}, where the
           plant writes LE; either way the write at a LE-read cell is LE, and
           no head moves.\<close>
        thus ?thesis using LE unfolding wrap_plant_done_delta_def
          by (auto split: if_splits)
      next
        case disp
        thus ?thesis using LE unfolding wrap_disp_delta_gen_def
          by (auto split: nat.splits)
      next
        case run
        then obtain qq \<sigma> q'' \<sigma>' dd sym where
            aeq: "a = sym"
            and a'eq: "a' = (\<lambda>p. Enc (\<sigma>' (wrap_tau p)))"
            and deq: "d = (\<lambda>p. dd (wrap_tau p))"
            and trM: "(qq, \<sigma>, q'', \<sigma>', dd) \<in> delta_tm M"
            and symc: "\<forall>p. sym p = Enc (\<sigma> (wrap_tau p))"
          unfolding wrap_run_delta_def by auto
        have "sym k = Enc (le_tm M)" using LE aeq by simp
        moreover have "sym k = Enc (\<sigma> (wrap_tau k))" using symc by simp
        ultimately have "\<sigma> (wrap_tau k) = le_tm M" by simp
        from valid_mttm_deltaLE[OF valM trM this]
        have "\<sigma>' (wrap_tau k) = le_tm M \<and> dd (wrap_tau k) \<in> {dir.N, dir.R}" .
        with a'eq deq show ?thesis by simp
      qed
    qed
    \<comment> \<open>(15) \<open>\<delta>\<close>-support: beyond the tape count each transition reads and
       writes blank and is stationary.  Since \<open>2 \<le> k_tm M \<le> j\<close> we have
       \<open>2 \<le> j\<close>: the storage head @{text "Suc 0"} and the plant tape @{text 0}
       are both \<open>< j\<close>, so both reset families are blank-stationary there, and
       the run inherits @{thm valid_mttm_delta_support}.\<close>
    show "\<forall>q a q' a' d.
            (q, a, q', a', d) \<in> wrap_delta M pack c \<Sigma>u \<longrightarrow>
            (\<forall>j \<ge> k_tm M.
               a j = Enc (bl_tm M) \<and> a' j = Enc (bl_tm M) \<and> d j = dir.N)"
    proof (intro allI impI)
      fix q a q' a' d j
      assume in_\<delta>: "(q, a, q', a', d) \<in> wrap_delta M pack c \<Sigma>u"
         and jge: "k_tm M \<le> j"
      from k2 jge have j2: "2 \<le> j" by simp
      from in_\<delta>
      show "a j = Enc (bl_tm M) \<and> a' j = Enc (bl_tm M) \<and> d j = dir.N"
      proof (cases rule: wrap_delta_cases)
        case init
        thus ?thesis using jge j2 unfolding wrap_init_delta_gen_def
          by (auto split: nat.splits if_splits)
      next
        case ext
        thus ?thesis using jge j2 unfolding wrap_buf_extend_delta_gen_def
          by (auto split: nat.splits)
      next
        case close
        thus ?thesis using jge j2 unfolding wrap_buf_close_delta_gen_def
          by (auto split: nat.splits if_splits)
      next
        case eend
        thus ?thesis using jge j2 unfolding wrap_buf_empty_end_delta_gen_def
          by (auto split: nat.splits)
      next
        case nend
        thus ?thesis using jge j2 unfolding wrap_buf_nonempty_end_delta_gen_def
          by (auto split: nat.splits if_splits)
      next
        case rloop
        thus ?thesis using jge j2 unfolding wrap_rewind_loop_delta_gen_def
          by (auto split: if_splits)
      next
        case rdone
        thus ?thesis using jge j2 unfolding wrap_plant_done_delta_def
          by (auto split: if_splits)
      next
        case disp
        thus ?thesis using jge j2 unfolding wrap_disp_delta_gen_def
          by (auto split: nat.splits)
      next
        case run
        then obtain qq \<sigma> q'' \<sigma>' dd sym where
            aeq: "a = sym"
            and a'eq: "a' = (\<lambda>p. Enc (\<sigma>' (wrap_tau p)))"
            and deq: "d = (\<lambda>p. dd (wrap_tau p))"
            and trM: "(qq, \<sigma>, q'', \<sigma>', dd) \<in> delta_tm M"
            and symc: "\<forall>p. sym p = Enc (\<sigma> (wrap_tau p))"
          unfolding wrap_run_delta_def by auto
        have tauj: "wrap_tau j = j" using j2 by (rule wrap_tau_ge2_id)
        from valid_mttm_delta_support[OF valM trM jge]
        have supp: "\<sigma> j = bl_tm M \<and> \<sigma>' j = bl_tm M \<and> dd j = dir.N" .
        have "a j = Enc (bl_tm M)" using aeq symc tauj supp by simp
        moreover have "a' j = Enc (bl_tm M)" using a'eq tauj supp by simp
        moreover have "d j = dir.N" using deq tauj supp by simp
        ultimately show ?thesis by simp
      qed
    qed
  qed
qed


subsection \<open>Determinism of the plant-\<open>le\<close> wrap\<close>

text \<open>Obligation 4 --- determinism preservation, conditional on
  @{term "det_mttm M"}.  The encoder families and
  dispatch are functional per read pattern, and the transposed run inherits
  M-determinism through @{const wrap_tau}.  Only the @{text W_Reset} case
  differs: instead of the two combined-reset families it disambiguates the
  generic storage rewind loop from the plant-done step by their
  @{text le}-guards on the storage tape (index @{text "Suc 0"}) --- the loop
  reads a non-@{text le} there, the plant-done reads @{text le} --- each
  functional in the read.\<close>

lemma wrap_det:
  assumes valM: "valid_mttm M"
      and detM: "det_mttm M"
      and finSu: "finite \<Sigma>u"
      and c_pos: "0 < c"
  shows "det_mttm (encoding_wrap M pack c \<Sigma>u)"
  unfolding det_mttm_def
proof (intro allI impI)
  fix q a p1 b1 d1 p2 b2 d2
  assume t1: "(q, a, p1, b1, d1) \<in> delta_tm (encoding_wrap M pack c \<Sigma>u)"
     and t2: "(q, a, p2, b2, d2) \<in> delta_tm (encoding_wrap M pack c \<Sigma>u)"
  hence t1w: "(q, a, p1, b1, d1) \<in> wrap_delta M pack c \<Sigma>u"
    and t2w: "(q, a, p2, b2, d2) \<in> wrap_delta M pack c \<Sigma>u"
    by simp_all
  show "(p1, b1, d1) = (p2, b2, d2)"
  proof (cases q)
    case W_Init
    with t1w t2w show ?thesis
      unfolding wrap_delta_def
                wrap_init_delta_gen_def wrap_buf_extend_delta_gen_def
                wrap_buf_close_delta_gen_def wrap_buf_empty_end_delta_gen_def
                wrap_buf_nonempty_end_delta_gen_def
                wrap_rewind_loop_delta_gen_def
                wrap_plant_done_delta_def
                wrap_disp_delta_gen_def wrap_run_delta_def
      by auto
  next
    case (W_Buf ws)
    with t1w t2w show ?thesis
      unfolding wrap_delta_def
                wrap_init_delta_gen_def wrap_buf_extend_delta_gen_def
                wrap_buf_close_delta_gen_def wrap_buf_empty_end_delta_gen_def
                wrap_buf_nonempty_end_delta_gen_def
                wrap_rewind_loop_delta_gen_def
                wrap_plant_done_delta_def
                wrap_disp_delta_gen_def wrap_run_delta_def
      by auto
  next
    case W_Reset
    \<comment> \<open>Both storage-rewind families read @{text "sym (Suc 0)"}; the loop
       fires when it is not @{text le} (looping in @{text W_Reset}, no head
       moves but @{text "Suc 0"} left), the plant-done when it is @{text le}
       (to @{text W_Disp}, planting @{text le} on tape @{text 0}).  Their
       guards are complementary, so at most one fires per read.\<close>
    with t1w t2w show ?thesis
      unfolding wrap_delta_def
                wrap_init_delta_gen_def wrap_buf_extend_delta_gen_def
                wrap_buf_close_delta_gen_def wrap_buf_empty_end_delta_gen_def
                wrap_buf_nonempty_end_delta_gen_def
                wrap_rewind_loop_delta_gen_def
                wrap_plant_done_delta_def
                wrap_disp_delta_gen_def wrap_run_delta_def
      by (auto split: if_splits)
  next
    case W_Disp
    with t1w t2w show ?thesis
      unfolding wrap_delta_def
                wrap_init_delta_gen_def wrap_buf_extend_delta_gen_def
                wrap_buf_close_delta_gen_def wrap_buf_empty_end_delta_gen_def
                wrap_buf_nonempty_end_delta_gen_def
                wrap_rewind_loop_delta_gen_def
                wrap_plant_done_delta_def
                wrap_disp_delta_gen_def wrap_run_delta_def
      by auto
  next
    case (W_Run qM)
    \<comment> \<open>Only \<open>wrap_run_delta\<close> has a \<open>W_Run\<close> source.  Extract the M-side
       \<open>\<delta>\<close>-tuples linked to each wrap-tuple, then use M-determinism.\<close>
    from t1w W_Run obtain sig1 q1' sig1' dd1 where
      m1: "(qM, sig1, q1', sig1', dd1) \<in> delta_tm M"
      and sym1: "\<forall>p. a p = Enc (sig1 (wrap_tau p))"
      and p1_eq: "p1 = W_Run q1'"
      and b1_eq: "b1 = (\<lambda>p. Enc (sig1' (wrap_tau p)))"
      and d1_eq: "d1 = (\<lambda>p. dd1 (wrap_tau p))"
      unfolding wrap_delta_def
                wrap_init_delta_gen_def wrap_buf_extend_delta_gen_def
                wrap_buf_close_delta_gen_def wrap_buf_empty_end_delta_gen_def
                wrap_buf_nonempty_end_delta_gen_def
                wrap_rewind_loop_delta_gen_def
                wrap_plant_done_delta_def
                wrap_disp_delta_gen_def wrap_run_delta_def
      by auto
    from t2w W_Run obtain sig2 q2' sig2' dd2 where
      m2: "(qM, sig2, q2', sig2', dd2) \<in> delta_tm M"
      and sym2: "\<forall>p. a p = Enc (sig2 (wrap_tau p))"
      and p2_eq: "p2 = W_Run q2'"
      and b2_eq: "b2 = (\<lambda>p. Enc (sig2' (wrap_tau p)))"
      and d2_eq: "d2 = (\<lambda>p. dd2 (wrap_tau p))"
      unfolding wrap_delta_def
                wrap_init_delta_gen_def wrap_buf_extend_delta_gen_def
                wrap_buf_close_delta_gen_def wrap_buf_empty_end_delta_gen_def
                wrap_buf_nonempty_end_delta_gen_def
                wrap_rewind_loop_delta_gen_def
                wrap_plant_done_delta_def
                wrap_disp_delta_gen_def wrap_run_delta_def
      by auto
    have sigma_eq: "sig1 = sig2"
    proof (rule ext)
      fix x
      have e1: "a (wrap_tau x) = Enc (sig1 (wrap_tau (wrap_tau x)))"
        using sym1 by blast
      have e2: "a (wrap_tau x) = Enc (sig2 (wrap_tau (wrap_tau x)))"
        using sym2 by blast
      from e1 e2 have "sig1 (wrap_tau (wrap_tau x)) = sig2 (wrap_tau (wrap_tau x))"
        by simp
      thus "sig1 x = sig2 x" by (simp add: wrap_tau_invol)
    qed
    have M_det: "(q1', sig1', dd1) = (q2', sig2', dd2)"
      using m1 m2 sigma_eq detM[unfolded det_mttm_def] by blast
    hence q'_eq: "q1' = q2'" and sig'_eq: "sig1' = sig2'" and dd_eq: "dd1 = dd2"
      by simp_all
    show ?thesis
      using p1_eq p2_eq b1_eq b2_eq d1_eq d2_eq q'_eq sig'_eq dd_eq
      by metis
  next
    case W_Rej
    with t1w show ?thesis
      unfolding wrap_delta_def
                wrap_init_delta_gen_def wrap_buf_extend_delta_gen_def
                wrap_buf_close_delta_gen_def wrap_buf_empty_end_delta_gen_def
                wrap_buf_nonempty_end_delta_gen_def
                wrap_rewind_loop_delta_gen_def
                wrap_plant_done_delta_def
                wrap_disp_delta_gen_def wrap_run_delta_def
      by auto
  qed
qed

end
