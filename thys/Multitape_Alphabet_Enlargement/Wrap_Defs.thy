theory Wrap_Defs
  imports Wrap_Base "Multitape_TM_Substrate.Multitape_Origin_Float"
begin

section \<open>The wrap, ending its reset with a fresh endmarker\<close>

text \<open>Keeping M's \<open>k\<close> tapes means reusing the input tape, and
  \<^emph>\<open>rewinding\<close> it after the encoder has read it costs about \<open>2n\<close> steps.
  Under a super-linear time bound, as in Theorem 12.3
  \<^cite>\<open>\<open>Theorem 12.3\<close> in "Hopcroft1979:introduction"\<close>, that cost is
  absorbed, but Theorem 12.4's \<open>(1+\<epsilon>)n\<close> bound cannot absorb it.  So this
  wrap does not rewind the input tape: it writes a fresh \<open>le\<close> at the input
  head's final position, \<^emph>\<open>floating\<close> the origin (the spent raw input to
  its left becomes unreachable, since a head reading \<open>le\<close> may not move
  left, clause 1 of @{const valid_ktm}).

  The storage tape (physical @{text 1}, carrying M's tape 0, the encoded
  input) is still rewound to its \<open>le\<close>, but that is only \<open>\<lceil>n/c\<rceil>\<close> cells
  (the encoded length), the \<open>\<epsilon>\<cdot>n\<close> term; it uses the generic single-tape
  rewind @{const wrap_rewind_loop_delta_gen}.  The input tape (physical
  @{text 0}, becoming M's tape 1) is \<^emph>\<open>not\<close> rewound: the step that ends
  the rewind writes \<open>le\<close> on it and hands over to @{text W_Disp}.  The
  encoder families, the transposed run and the dispatch are those of
  @{theory Multitape_Alphabet_Enlargement.Wrap_Base}.

  The fresh \<open>le\<close> makes the wrap \<^emph>\<open>not\<close> @{const le_unique} (it writes
  \<open>le\<close> where it did not read \<open>le\<close>); it remains @{const valid_ktm}, since
  clause 1 constrains only transitions that \<^emph>\<open>read\<close> \<open>le\<close>.  The engine
  is then run from a floated-origin init config, bridged back to the
  proper @{const init_config_ktm} by the origin-float lemmas of
  @{theory Multitape_TM_Substrate.Multitape_Origin_Float}.\<close>

subsection \<open>The step that ends the reset\<close>

text \<open>The step that ends the reset (called \<^emph>\<open>plant-done\<close> in the names
  below, for the \<open>le\<close> it plants): it fires when the storage tape
  (index @{text "Suc 0"}) reads \<open>le\<close> (its cell 0, reached by the generic
  rewind loop), and in the same transition writes \<open>le\<close> on the input tape
  (index @{text 0}) under its head, handing over to @{text W_Disp}.  No
  head moves.  This is the only reset family specific to this wrap; the
  loop is the generic @{const wrap_rewind_loop_delta_gen}.\<close>

definition wrap_plant_done_delta ::
  "('q, 'b) ktm \<Rightarrow> 'a set
   \<Rightarrow> (('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> ('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> (nat \<Rightarrow> move)) set"
where
  "wrap_plant_done_delta M \<Sigma>u =
     { (W_Reset, sym, W_Disp,
        (\<lambda>t. if t = 0 then Enc (le_ktm M) else sym t),
        \<lambda>_. MoveN)
       | sym.
           sym (Suc 0) = Enc (le_ktm M)
           \<and> (\<forall>i\<ge>k_ktm M. sym i = Enc (bl_ktm M))
           \<and> sym \<in> UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_ktm M }"

subsection \<open>The combinator\<close>

text \<open>The wrap's transition relation: the six encoder families at
  @{term "K = k_ktm M"}, the transposed run and dispatch, and --- for the
  reset --- the generic single-tape storage rewind (loop) plus the
  plant-done step.\<close>

definition wrap_delta ::
  "('q, 'b) ktm \<Rightarrow> ('a list \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a set
   \<Rightarrow> (('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> ('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> (nat \<Rightarrow> move)) set"
where
  "wrap_delta M pack c \<Sigma>u =
     wrap_init_delta_gen (k_ktm M) M
     \<union> wrap_buf_extend_delta_gen (k_ktm M) M c \<Sigma>u
     \<union> wrap_buf_close_delta_gen (k_ktm M) M pack c \<Sigma>u
     \<union> wrap_buf_empty_end_delta_gen (k_ktm M) M \<Sigma>u
     \<union> wrap_buf_nonempty_end_delta_gen (k_ktm M) M pack c \<Sigma>u
     \<union> wrap_rewind_loop_delta_gen W_Reset (Suc 0) (k_ktm M) M \<Sigma>u
     \<union> wrap_plant_done_delta M \<Sigma>u
     \<union> wrap_disp_delta_gen (k_ktm M) M \<Sigma>u
     \<union> wrap_run_delta M \<Sigma>u"

text \<open>The encoding wrap: transition relation @{const wrap_delta} at M's tape
  count @{term "k_ktm M"}, over the wrap state set (no new state: writing
  the fresh \<open>le\<close> is part of the step that ends the reset).  It is proved
  valid below for @{term "k_ktm M \<ge> 2"}, since the input tape must serve
  as one of M's tapes other than tape @{text 0}.\<close>

fun encoding_wrap ::
  "('q, 'b) ktm \<Rightarrow> ('a list \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a set
   \<Rightarrow> (('q, 'a, 'b) wrap_state, ('a, 'b) wrap_alphabet) ktm"
where
  "encoding_wrap M pack c \<Sigma>u =
     KTM
       (wrap_state_set M c \<Sigma>u)
       (Raw ` \<Sigma>u)
       (Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_ktm M)
       (Enc (bl_ktm M))
       (Enc (le_ktm M))
       (wrap_delta M pack c \<Sigma>u)
       W_Init
       (W_Run (t_ktm M))
       (W_Run (r_ktm M))
       (k_ktm M)"


subsection \<open>Validity of the wrap\<close>

text \<open>Phase-family case split for @{const wrap_delta}: a transition
  belongs to exactly one of the nine builders --- the six
  boundary-parameterised encoder families at @{term "k_ktm M"}, the generic
  single-tape storage rewind loop, the plant-done step, the dispatch, and the
  transposed run.\<close>

lemma wrap_delta_cases:
  assumes "(q, a, q', a', d) \<in> wrap_delta M pack c \<Sigma>u"
  obtains
    (init) "(q, a, q', a', d) \<in> wrap_init_delta_gen (k_ktm M) M"
  | (ext) "(q, a, q', a', d) \<in> wrap_buf_extend_delta_gen (k_ktm M) M c \<Sigma>u"
  | (close) "(q, a, q', a', d) \<in> wrap_buf_close_delta_gen (k_ktm M) M pack c \<Sigma>u"
  | (eend) "(q, a, q', a', d) \<in> wrap_buf_empty_end_delta_gen (k_ktm M) M \<Sigma>u"
  | (nend) "(q, a, q', a', d) \<in> wrap_buf_nonempty_end_delta_gen (k_ktm M) M pack c \<Sigma>u"
  | (rloop) "(q, a, q', a', d)
               \<in> wrap_rewind_loop_delta_gen W_Reset (Suc 0) (k_ktm M) M \<Sigma>u"
  | (rdone) "(q, a, q', a', d) \<in> wrap_plant_done_delta M \<Sigma>u"
  | (disp) "(q, a, q', a', d) \<in> wrap_disp_delta_gen (k_ktm M) M \<Sigma>u"
  | (run) "(q, a, q', a', d) \<in> wrap_run_delta M \<Sigma>u"
  using assms unfolding wrap_delta_def by blast

text \<open>Validity of the wrap at tape count @{term "k_ktm M"}.  Hypotheses:
  @{term "2 \<le> k_ktm M"}, @{term "valid_ktm M"}, and
  @{term "le_ktm M \<noteq> bl_ktm M"} (the storage rewind passes @{text bl}
  through unchanged, and the plant-done step writes @{text le}, so the
  obligations against a spurious @{text le} need them distinct).  It does
  \<^emph>\<open>not\<close> require @{const le_unique} of the input, and the resulting wrap
  is itself \<^emph>\<open>not\<close> @{const le_unique}: the plant-done step writes @{text le}
  on physical tape @{text 0} without reading it there.  That is allowed by
  @{const valid_ktm}, whose endmarker clause (obligation 14 below)
  constrains only transitions that \<^emph>\<open>read\<close> @{text le}; forbidding a fresh
  @{text le} is the separate predicate @{const le_unique}.\<close>

lemma wrap_wf:
  assumes valM: "valid_ktm M"
      and le_ne_bl: "le_ktm M \<noteq> bl_ktm M"
      and finSu: "finite \<Sigma>u"
      and c_pos: "0 < c"
      and k2: "2 \<le> k_ktm M"
  shows "valid_ktm (encoding_wrap M pack c \<Sigma>u)"
proof -
  have eq:
    "encoding_wrap M pack c \<Sigma>u =
       KTM (wrap_state_set M c \<Sigma>u)
            (Raw ` \<Sigma>u)
            (Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_ktm M)
            (Enc (bl_ktm M))
            (Enc (le_ktm M))
            (wrap_delta M pack c \<Sigma>u)
            W_Init
            (W_Run (t_ktm M))
            (W_Run (r_ktm M))
            (k_ktm M)"
    by simp
  show ?thesis
    unfolding eq valid_ktm.simps
  proof (intro conjI)
    \<comment> \<open>(1) finite Q'\<close>
    show "finite (wrap_state_set M c \<Sigma>u)"
      by (rule finite_wrap_state_set[OF valM finSu])
    \<comment> \<open>(2) finite \<open>\<Gamma>\<close>'\<close>
    show "finite (Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_ktm M)"
      using finSu valid_ktm_finite_Gamma[OF valM] by simp
    \<comment> \<open>(3) \<open>\<Sigma>\<close>' \<open>\<subseteq>\<close> \<open>\<Gamma>\<close>'\<close>
    show "Raw ` \<Sigma>u \<subseteq> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_ktm M"
      by blast
    \<comment> \<open>(4) start in Q'\<close>
    show "W_Init \<in> wrap_state_set M c \<Sigma>u"
      unfolding wrap_state_set_def by simp
    \<comment> \<open>(5) accept in Q'\<close>
    show "W_Run (t_ktm M) \<in> wrap_state_set M c \<Sigma>u"
      using valid_ktm_t_in_Q[OF valM]
      unfolding wrap_state_set_def by simp
    \<comment> \<open>(6) reject in Q'\<close>
    show "W_Run (r_ktm M) \<in> wrap_state_set M c \<Sigma>u"
      using valid_ktm_r_in_Q[OF valM]
      unfolding wrap_state_set_def by simp
    \<comment> \<open>(7a) bl in \<open>\<Gamma>\<close>'\<close>
    show "Enc (bl_ktm M) \<in> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_ktm M"
      using valid_ktm_blank_in_Gamma[OF valM] by blast
    \<comment> \<open>(7b) bl not in \<open>\<Sigma>\<close>'\<close>
    show "Enc (bl_ktm M) \<notin> Raw ` \<Sigma>u"
      by auto
    \<comment> \<open>(8a) le in \<open>\<Gamma>\<close>'\<close>
    show "Enc (le_ktm M) \<in> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_ktm M"
      using valid_ktm_LE_in_Gamma[OF valM] by blast
    \<comment> \<open>(8b) le not in \<open>\<Sigma>\<close>'\<close>
    show "Enc (le_ktm M) \<notin> Raw ` \<Sigma>u"
      by auto
    \<comment> \<open>(11) accept \<open>\<noteq>\<close> reject\<close>
    show "W_Run (t_ktm M) \<noteq> W_Run (r_ktm M)"
      using valM by (cases M) simp
    \<comment> \<open>(12) \<open>0 < k\<close>: the wrap keeps M's tape count.\<close>
    show "0 < k_ktm M"
      using valid_ktm_k_pos[OF valM] by simp
    \<comment> \<open>(13) \<open>\<delta>\<close>-shape: source / dest / read / write range typing.  The
       plant-done step writes @{text "Enc le"} on tape @{text 0}, which is in range by
       @{thm valid_ktm_LE_in_Gamma}.\<close>
    show "wrap_delta M pack c \<Sigma>u
            \<subseteq> (wrap_state_set M c \<Sigma>u - {W_Run (t_ktm M), W_Run (r_ktm M)})
              \<times> (UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_ktm M)
              \<times> wrap_state_set M c \<Sigma>u
              \<times> (UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_ktm M)
              \<times> (UNIV \<rightarrow> UNIV)"
      unfolding wrap_delta_def
                wrap_init_delta_gen_def wrap_buf_extend_delta_gen_def
                wrap_buf_close_delta_gen_def wrap_buf_empty_end_delta_gen_def
                wrap_buf_nonempty_end_delta_gen_def
                wrap_rewind_loop_delta_gen_def
                wrap_plant_done_delta_def
                wrap_disp_delta_gen_def wrap_run_delta_def
                wrap_state_set_def
      using c_pos valid_ktm_t_in_Q[OF valM] valid_ktm_s_in_Q[OF valM]
            valid_ktm_LE_in_Gamma[OF valM] valid_ktm_blank_in_Gamma[OF valM]
            valid_ktm_delta_set[OF valM]
            valid_ktm_Sigma_sub_Gamma[OF valM]
      by (fastforce split: nat.split if_splits)
    \<comment> \<open>(14) \<open>\<delta>\<close>LE-preservation: read LE \<open>\<Longrightarrow>\<close> write LE and dir \<open>\<in>\<close> {N, R}.
       The plant-done step writes LE on tape @{text 0} regardless of what it
       read there --- legal, since this obligation only fires when the read
       cell already \<^emph>\<open>is\<close> LE, and then the step writes LE anyway.  The
       rewind loop only moves the storage head (@{text "Suc 0"}), whose
       read cannot be LE (its guard), so no LE-read cell moves.\<close>
    show "\<forall>q a q' a' d k.
            (q, a, q', a', d) \<in> wrap_delta M pack c \<Sigma>u \<longrightarrow>
            a k = Enc (le_ktm M) \<longrightarrow>
            a' k = Enc (le_ktm M) \<and> d k \<in> {MoveN, MoveR}"
    proof (intro allI impI)
      fix q a q' a' d k
      assume in_\<delta>: "(q, a, q', a', d) \<in> wrap_delta M pack c \<Sigma>u"
         and LE: "a k = Enc (le_ktm M)"
      from in_\<delta> show "a' k = Enc (le_ktm M) \<and> d k \<in> {MoveN, MoveR}"
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
           step writes LE; either way the write at a LE-read cell is LE, and
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
            and trM: "(qq, \<sigma>, q'', \<sigma>', dd) \<in> delta_ktm M"
            and symc: "\<forall>p. sym p = Enc (\<sigma> (wrap_tau p))"
          unfolding wrap_run_delta_def by auto
        have "sym k = Enc (le_ktm M)" using LE aeq by simp
        moreover have "sym k = Enc (\<sigma> (wrap_tau k))" using symc by simp
        ultimately have "\<sigma> (wrap_tau k) = le_ktm M" by simp
        from valid_ktm_deltaLE[OF valM trM this]
        have "\<sigma>' (wrap_tau k) = le_ktm M \<and> dd (wrap_tau k) \<in> {MoveN, MoveR}" .
        with a'eq deq show ?thesis by simp
      qed
    qed
    \<comment> \<open>(15) \<open>\<delta>\<close>-support: beyond the tape count each transition reads and
       writes blank and is stationary.  Since \<open>2 \<le> k_ktm M \<le> j\<close> we have
       \<open>2 \<le> j\<close>: the storage head @{text "Suc 0"} and the input tape @{text 0}
       are both \<open>< j\<close>, so both reset families are blank-stationary there, and
       the run inherits @{thm valid_ktm_delta_support}.\<close>
    show "\<forall>q a q' a' d.
            (q, a, q', a', d) \<in> wrap_delta M pack c \<Sigma>u \<longrightarrow>
            (\<forall>j \<ge> k_ktm M.
               a j = Enc (bl_ktm M) \<and> a' j = Enc (bl_ktm M) \<and> d j = MoveN)"
    proof (intro allI impI)
      fix q a q' a' d j
      assume in_\<delta>: "(q, a, q', a', d) \<in> wrap_delta M pack c \<Sigma>u"
         and jge: "k_ktm M \<le> j"
      from k2 jge have j2: "2 \<le> j" by simp
      from in_\<delta>
      show "a j = Enc (bl_ktm M) \<and> a' j = Enc (bl_ktm M) \<and> d j = MoveN"
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
            and trM: "(qq, \<sigma>, q'', \<sigma>', dd) \<in> delta_ktm M"
            and symc: "\<forall>p. sym p = Enc (\<sigma> (wrap_tau p))"
          unfolding wrap_run_delta_def by auto
        have tauj: "wrap_tau j = j" using j2 by (rule wrap_tau_ge2_id)
        from valid_ktm_delta_support[OF valM trM jge]
        have supp: "\<sigma> j = bl_ktm M \<and> \<sigma>' j = bl_ktm M \<and> dd j = MoveN" .
        have "a j = Enc (bl_ktm M)" using aeq symc tauj supp by simp
        moreover have "a' j = Enc (bl_ktm M)" using a'eq tauj supp by simp
        moreover have "d j = MoveN" using deq tauj supp by simp
        ultimately show ?thesis by simp
      qed
    qed
  qed
qed


subsection \<open>Determinism of the wrap\<close>

text \<open>Obligation 4 --- determinism preservation, conditional on
  @{term "det_ktm M"}.  The encoder families and
  dispatch are functional per read pattern, and the transposed run inherits
  M-determinism through @{const wrap_tau}.  In the @{text W_Reset} case two
  families can fire, and they are told apart, the generic storage rewind
  loop from the plant-done step, by their
  @{text le}-guards on the storage tape (index @{text "Suc 0"}) --- the loop
  reads a non-@{text le} there, the plant-done reads @{text le} --- each
  functional in the read.\<close>

lemma wrap_det:
  assumes valM: "valid_ktm M"
      and detM: "det_ktm M"
      and finSu: "finite \<Sigma>u"
      and c_pos: "0 < c"
  shows "det_ktm (encoding_wrap M pack c \<Sigma>u)"
  unfolding det_ktm_def
proof (intro allI impI)
  fix q a p1 b1 d1 p2 b2 d2
  assume t1: "(q, a, p1, b1, d1) \<in> delta_ktm (encoding_wrap M pack c \<Sigma>u)"
     and t2: "(q, a, p2, b2, d2) \<in> delta_ktm (encoding_wrap M pack c \<Sigma>u)"
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
       (to @{text W_Disp}, writing @{text le} on tape @{text 0}).  Their
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
      m1: "(qM, sig1, q1', sig1', dd1) \<in> delta_ktm M"
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
      m2: "(qM, sig2, q2', sig2', dd2) \<in> delta_ktm M"
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
      using m1 m2 sigma_eq detM[unfolded det_ktm_def] by blast
    hence q'_eq: "q1' = q2'" and sig'_eq: "sig1' = sig2'" and dd_eq: "dd1 = dd2"
      by simp_all
    show ?thesis
      using p1_eq p2_eq b1_eq b2_eq d1_eq d2_eq q'_eq sig'_eq dd_eq
      by metis
  qed
qed

end
