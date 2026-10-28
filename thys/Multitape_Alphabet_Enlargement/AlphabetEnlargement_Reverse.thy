theory AlphabetEnlargement_Reverse
  imports AlphabetEnlargement
begin

text \<open>This theory holds the reverse-direction machinery for the
  \<open>alphabet_enlarge\<close> simulation chain, together with the
  biconditional language theorem \<open>alphabet_enlarge_language\<close>
  --- which closes via that machinery for every well-formed
  \<open>M\<close>, with \<^emph>\<open>no determinism hypothesis\<close> --- and the
  nondeterministic corollary \<open>alphabet_enlarge_nae\<close>.

  Contents, in dependency order:

  \<^item> Three reverse-direction lifts of the buffered compute:
    \<open>m_step_buffered_lift_to_tape_general\<close>,
    \<open>m_step_buffered_chain_lift_to_tape\<close>,
    \<open>m_steps_buffered_lift_to_tape\<close>.

  \<^item> \<open>ae_step_ss4_ss5_destruct_to_buffered\<close>:
    reverse-direction SS4\<open>\<rightarrow>\<close>SS5 step destructor.

  \<^item> The four reverse-direction chain peel lemmas
    \<open>ae_backward_stage_load_chain\<close>,
    \<open>ae_backward_stage_compute_extract\<close>,
    \<open>ae_backward_stage_writeback_chain\<close>, and
    \<open>ae_backward_stage_decompose\<close>, and the reverse-direction
    top-level wrapper \<open>ae_backward_stage\<close>.

  \<^item> A chain-uniqueness lemma for
    \<open>alphabet_enlarge_delta\<close> derived from the 16
    per-substep functionality lemmas in
    \<open>AlphabetEnlargement_Delta\<close>.

  \<^item> The biconditional language theorem
    \<open>alphabet_enlarge_language\<close>, for every well-formed
    \<open>M\<close> (no determinism hypothesis).  The forward direction
    delegates to \<open>alphabet_enlarge_language_forward\<close> (in
    \<open>AlphabetEnlargement\<close>); the reverse direction is proved
    here determinism-free, via the validation-phase uniqueness
    and the window-inversion kernel.

  \<^item> The nondeterministic corollary
    \<open>alphabet_enlarge_nae\<close>: the biconditional and the time
    bound packaged for an arbitrary, possibly nondeterministic,
    well-formed \<open>M\<close>.

  The reverse direction does not require \<open>det_ktm M\<close>.  The
  natural route would close by chain uniqueness of
  \<open>alphabet_enlarge_delta\<close>, which a nondeterministic
  \<open>M\<close> does not supply (its compute substep is multi-valued);
  the determinism-bound step is instead discharged by the
  unconditional window-inversion kernel (the \<open>det\<close>-free
  SS5\<open>\<rightarrow>\<close>SS8 subsection below).  The biconditional and the
  corollary \<open>alphabet_enlarge_nae\<close> therefore hold for
  nondeterministic \<open>M\<close> as well.\<close>


subsection \<open>Reverse direction: from the buffer back to the tapes\<close>

subsubsection \<open>Single-step lift to per-tape\<close>

text \<open>Per-tape regime-dispatching single-step lift.  Takes the
  per-tape unified \<open>ae_window_invariant_general\<close> (with the
  regime selector \<open>pos_n :: nat \<Rightarrow> nat\<close> that can differ across
  tapes) and produces a substrate-side \<open>ktm_step\<close> with the
  per-tape unified invariant preserved on the post-step config.

  The proof factors out the regime-independent structure
  (\<open>cM\<close> unpack, \<open>\<delta>\<close>-tuple extraction, per-tape
  read-match via \<open>read_bp_via_window_general\<close>,
  \<open>ktm_step.step\<close> packaging) from the regime-specific
  window-preservation step, which dispatches per tape on
  \<open>pos_n k\<close> into \<open>ae_window_invariant_step\<close> /
  \<open>_le1_step\<close> / \<open>_le0_step\<close>.

  The hypothesis bundle for the regime-specific side conditions
  is the same per-regime form as the forward direction's
  \<open>ae_m_steps_buffered_correct_trace_general\<close> uses, so
  Step 2b can pass these through directly.\<close>

lemma m_step_buffered_lift_to_tape_general:
  fixes M :: "('q, 'a) ktm"
    and cM :: "('a, 'q) ktc_config"
    and q q' :: 'q
    and blocks blocks' ::
          "nat \<Rightarrow> (('c :: enum \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))"
    and pos_bp pos_bp' :: "nat \<Rightarrow> 'c bp"
    and pos_n :: "nat \<Rightarrow> nat"
  assumes vM:        "valid_ktm M"
      and lu:        "le_unique M"
      and cM_valid:  "valid_config_ktm M cM"
      and step:      "((q, blocks, pos_bp), (q', blocks', pos_bp'))
                         \<in> m_step_buffered M"
      and st_eq:     "ktc_state cM = q"
      and window:    "\<forall>k<k_ktm M. ae_window_invariant_general
                            (ktc_tape cM k) (ktc_pos cM k)
                            (pos_bp k) (blocks k) (pos_n k)
                            (le_ktm M)"
      and bp_lt:     "\<forall>k. bp_linear (pos_bp k)
                              < 3 * card (UNIV :: 'c set) - 1"
      and bp_pos:    "\<forall>k. 0 < bp_linear (pos_bp k)"
      and no_le:     "\<forall>k<k_ktm M. (pos_n k = 0
                              \<longrightarrow> (\<forall>i. 0 < i
                                          \<and> i \<le> card (UNIV :: 'c set)
                                       \<longrightarrow> ktc_tape cM k i \<noteq> le_ktm M))
                           \<and> (pos_n k = 1
                                \<longrightarrow> (\<forall>i. 0 < i
                                            \<and> i \<le> 2 * card (UNIV :: 'c set)
                                         \<longrightarrow> ktc_tape cM k i \<noteq> le_ktm M))
                           \<and> (pos_n k \<ge> 2
                                \<longrightarrow> ktc_tape cM k (ktc_pos cM k) \<noteq> le_ktm M)"
  shows "\<exists>cM'.
            (cM, cM') \<in> ktm_step (delta_ktm M)
            \<and> ktc_state cM' = q'
            \<and> (\<forall>k<k_ktm M. ae_window_invariant_general
                      (ktc_tape cM' k) (ktc_pos cM' k)
                      (pos_bp' k) (blocks' k) (pos_n k) (le_ktm M))"
proof -
  obtain ts_pre n_pre where
      cM_eq: "cM = KConfig q ts_pre n_pre"
  proof -
    obtain q0 ts0 n0 where cM_form: "cM = KConfig q0 ts0 n0"
      by (cases cM) auto
    from st_eq cM_form have "q0 = q" by simp
    with cM_form show thesis using that by simp
  qed
  have tp_eq: "ktc_tape cM = ts_pre" using cM_eq by simp
  have ps_eq: "ktc_pos cM = n_pre"   using cM_eq by simp
  from step obtain a a' d where
      delta_mem: "(q, a, q', a', d) \<in> delta_ktm M"
    and read_eq:  "\<forall>k. a k = read_bp (blocks k) (pos_bp k)"
    and write_eq: "\<forall>k. blocks' k = write_bp (blocks k) (pos_bp k) (a' k)"
    and adv_eq:   "\<forall>k. bp_advance_le (le_ktm M) (a k) (pos_bp k) (d k)
                          = Some (pos_bp' k)"
    unfolding m_step_buffered_def by auto
  have read_match: "\<forall>k. a k = ts_pre k (n_pre k)"
  proof (intro allI)
    fix k
    show "a k = ts_pre k (n_pre k)"
    proof (cases "k < k_ktm M")
      case True
      from window True have wi_k:
          "ae_window_invariant_general (ktc_tape cM k) (ktc_pos cM k)
              (pos_bp k) (blocks k) (pos_n k) (le_ktm M)" by blast
      hence wi_k': "ae_window_invariant_general (ts_pre k) (n_pre k)
                       (pos_bp k) (blocks k) (pos_n k) (le_ktm M)"
        using tp_eq ps_eq by simp
      have "read_bp (blocks k) (pos_bp k) = ts_pre k (n_pre k)"
        by (rule read_bp_via_window_general[OF wi_k'])
      thus "a k = ts_pre k (n_pre k)"
        using read_eq by simp
    next
      case False
      hence kge: "k \<ge> k_ktm M" by simp
      \<comment> \<open>Padding tape: no window invariant available; the
          read-match holds because both sides are the substrate
          blank \<open>bl_ktm M\<close> --- \<open>a k\<close> by \<open>\<delta>\<close>-support, the actual
          tape read by \<open>cM\<close>'s blank-tail.\<close>
      have a_bl: "a k = bl_ktm M"
        using valid_ktm_delta_support[OF vM delta_mem kge] by simp
      have ts_bl: "ts_pre k (n_pre k) = bl_ktm M"
        using valid_config_ktm_blank_tail[OF cM_valid kge] tp_eq by simp
      show "a k = ts_pre k (n_pre k)" using a_bl ts_bl by simp
    qed
  qed
  have read_match_fun: "(\<lambda>k. ts_pre k (n_pre k)) = a"
    using read_match by (auto intro!: ext)
  let ?cM' = "KConfig q' (\<lambda>k. (ts_pre k)(n_pre k := a' k))
                           (\<lambda>k. go_move (d k) (n_pre k))"
  have delta_tuple: "(q, \<lambda>k. ts_pre k (n_pre k), q', a', d)
                       \<in> delta_ktm M"
    using delta_mem read_match_fun by simp
  have step_ktm: "(cM, ?cM') \<in> ktm_step (delta_ktm M)"
  proof -
    have "(KConfig q ts_pre n_pre, ?cM') \<in> ktm_step (delta_ktm M)"
      by (rule ktm_step.step
            [where ts=ts_pre and n=n_pre and a=a' and move=d,
             OF delta_tuple])
    thus ?thesis using cM_eq by simp
  qed
  have st_new: "ktc_state ?cM' = q'" by simp
  have new_window:
      "\<forall>k<k_ktm M. ae_window_invariant_general
              (ktc_tape ?cM' k) (ktc_pos ?cM' k)
              (pos_bp' k) (blocks' k) (pos_n k) (le_ktm M)"
  proof (intro allI impI)
    fix k assume klt: "k < k_ktm M"
    let ?c = "card (UNIV :: 'c set)"
    have tape_k: "ktc_tape ?cM' k = (ts_pre k)(n_pre k := a' k)" by simp
    have pos_k:  "ktc_pos ?cM' k  = go_move (d k) (n_pre k)" by simp
    have blocks'_k: "blocks' k = write_bp (blocks k) (pos_bp k) (a' k)"
      using write_eq by blast
    have adv_k_buf: "bp_advance_le (le_ktm M) (a k) (pos_bp k) (d k)
                        = Some (pos_bp' k)"
      using adv_eq by blast
    have read_a_k: "a k = ts_pre k (n_pre k)" using read_match by blast
    have adv_k: "bp_advance_le (le_ktm M) (ts_pre k (n_pre k))
                    (pos_bp k) (d k) = Some (pos_bp' k)"
      using adv_k_buf read_a_k by simp
    have wi_gen_k: "ae_window_invariant_general
        (ts_pre k) (n_pre k) (pos_bp k) (blocks k) (pos_n k) (le_ktm M)"
      using window klt tp_eq ps_eq by simp
    have bp_lt_k:  "bp_linear (pos_bp k) < 3 * ?c - 1" using bp_lt by blast
    have bp_pos_k: "0 < bp_linear (pos_bp k)" using bp_pos by blast
    \<comment> \<open>LE-discipline side conditions, derived from
      \<open>valid_ktm M\<close>; used in \<open>le0\<close> and \<open>le1\<close>
      branches.\<close>
    have a_le_k: "ts_pre k (n_pre k) = le_ktm M
                    \<Longrightarrow> a' k = le_ktm M \<and> d k \<in> {MoveN, MoveR}"
    proof -
      assume LE: "ts_pre k (n_pre k) = le_ktm M"
      have a_LE: "a k = le_ktm M" using read_a_k LE by simp
      show "a' k = le_ktm M \<and> d k \<in> {MoveN, MoveR}"
        by (rule valid_ktm_deltaLE[OF vM delta_mem a_LE])
    qed
    have a_not_le_k: "ts_pre k (n_pre k) \<noteq> le_ktm M \<Longrightarrow> a' k \<noteq> le_ktm M"
    proof
      assume nLE: "ts_pre k (n_pre k) \<noteq> le_ktm M" and LE': "a' k = le_ktm M"
      have a_LE: "a k = le_ktm M"
        by (rule valid_ktm_deltaLE_no_write[OF lu delta_mem LE'])
      from a_LE read_a_k nLE show False by simp
    qed
    \<comment> \<open>Dispatch on \<open>pos_n k\<close> regime.\<close>
    consider (steady) "pos_n k \<ge> 2" | (le1) "pos_n k = 1" | (le0) "pos_n k = 0"
      by linarith
    then show "ae_window_invariant_general
                 (ktc_tape ?cM' k) (ktc_pos ?cM' k)
                 (pos_bp' k) (blocks' k) (pos_n k) (le_ktm M)"
    proof cases
      case steady
      have wi_st: "ae_window_invariant (ts_pre k) (n_pre k)
                      (pos_bp k) (blocks k) ((pos_n k - 2) * ?c + 1)"
        using wi_gen_k steady
        unfolding ae_window_invariant_general_def by simp
      have no_le_k: "ts_pre k (n_pre k) \<noteq> le_ktm M"
        using no_le klt steady tp_eq ps_eq by force
      have wi_post: "ae_window_invariant
                        ((ts_pre k)(n_pre k := a' k))
                        (go_move (d k) (n_pre k))
                        (pos_bp' k)
                        (write_bp (blocks k) (pos_bp k) (a' k))
                        ((pos_n k - 2) * ?c + 1)"
        by (rule ae_window_invariant_step
                [OF wi_st adv_k bp_lt_k bp_pos_k no_le_k])
      have wi_post_gen:
          "ae_window_invariant_general
              ((ts_pre k)(n_pre k := a' k))
              (go_move (d k) (n_pre k))
              (pos_bp' k)
              (write_bp (blocks k) (pos_bp k) (a' k))
              (pos_n k) (le_ktm M)"
        using wi_post steady
        unfolding ae_window_invariant_general_def by simp
      show ?thesis using wi_post_gen tape_k pos_k blocks'_k by simp
    next
      case le1
      have wi_l1: "ae_window_invariant_le1 (ts_pre k) (n_pre k)
                      (pos_bp k) (blocks k) (le_ktm M)"
        using wi_gen_k le1
        unfolding ae_window_invariant_general_def by simp
      have no_le_win_k: "\<forall>i. 0 < i \<and> i \<le> 2 * ?c
                                \<longrightarrow> ts_pre k i \<noteq> le_ktm M"
        using no_le klt le1 tp_eq by simp
      have wi_post: "ae_window_invariant_le1
                        ((ts_pre k)(n_pre k := a' k))
                        (go_move (d k) (n_pre k))
                        (pos_bp' k)
                        (write_bp (blocks k) (pos_bp k) (a' k))
                        (le_ktm M)"
        by (rule ae_window_invariant_le1_step
                [OF wi_l1 adv_k bp_lt_k bp_pos_k
                    a_le_k a_not_le_k no_le_win_k])
      have wi_post_gen:
          "ae_window_invariant_general
              ((ts_pre k)(n_pre k := a' k))
              (go_move (d k) (n_pre k))
              (pos_bp' k)
              (write_bp (blocks k) (pos_bp k) (a' k))
              (pos_n k) (le_ktm M)"
        using wi_post le1
        unfolding ae_window_invariant_general_def by simp
      show ?thesis using wi_post_gen tape_k pos_k blocks'_k by simp
    next
      case le0
      have wi_l0: "ae_window_invariant_le0 (ts_pre k) (n_pre k)
                      (pos_bp k) (blocks k) (le_ktm M)"
        using wi_gen_k le0
        unfolding ae_window_invariant_general_def by simp
      have no_le_win_k: "\<forall>i. 0 < i \<and> i \<le> ?c
                                \<longrightarrow> ts_pre k i \<noteq> le_ktm M"
        using no_le klt le0 tp_eq by simp
      have wi_post: "ae_window_invariant_le0
                        ((ts_pre k)(n_pre k := a' k))
                        (go_move (d k) (n_pre k))
                        (pos_bp' k)
                        (write_bp (blocks k) (pos_bp k) (a' k))
                        (le_ktm M)"
        by (rule ae_window_invariant_le0_step
                [OF wi_l0 adv_k bp_lt_k bp_pos_k
                    a_le_k a_not_le_k no_le_win_k])
      have wi_post_gen:
          "ae_window_invariant_general
              ((ts_pre k)(n_pre k := a' k))
              (go_move (d k) (n_pre k))
              (pos_bp' k)
              (write_bp (blocks k) (pos_bp k) (a' k))
              (pos_n k) (le_ktm M)"
        using wi_post le0
        unfolding ae_window_invariant_general_def by simp
      show ?thesis using wi_post_gen tape_k pos_k blocks'_k by simp
    qed
  qed
  show ?thesis using step_ktm st_new new_window by blast
qed


text \<open>Auxiliary induction for the reverse lift: given an
  \<open>n\<close>-step \<open>m_step_buffered\<close> chain (with \<open>n \<le> c\<close>)
  starting from a canonical SS4-entry buffered state and the
  per-tape \<open>ae_window_invariant_general\<close> + side conditions
  on a substrate-side initial config \<open>cM\<close>, produces an
  \<open>n\<close>-step substrate \<open>ktm_step\<close> trace from \<open>cM\<close> to
  some \<open>cM_n\<close> with matching state, preserved window
  invariant, preserved no-LE windows, preserved
  \<open>left_not_le_pos0\<close>, and the
  \<open>bp_linear\<close>-bound conjunct (\<open>c \<le> bp_linear + n\<close>,
  \<open>bp_linear < 2c + n\<close>).

  Mirror of the forward induction \<open>ae_coupled_run_aux_general\<close>
  with trace \<open>\<longleftrightarrow>\<close> chain flipped.  The single-step lift
  \<open>m_step_buffered_lift_to_tape_general\<close> does the per-step
  substrate-side construction; this lemma threads the invariants
  across the chain.

  Used inside the smaller wrapper
  \<open>m_steps_buffered_lift_to_tape\<close>, which exposes the result
  via \<open>m_steps_buffered\<close>.\<close>

lemma m_step_buffered_chain_lift_to_tape:
  fixes M :: "('q, 'a) ktm"
    and qM :: 'q
    and ofs :: "nat \<Rightarrow> 'c :: enum"
    and buf_full ::
          "nat \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))"
    and pos :: "nat \<Rightarrow> nat"
    and n :: nat
    and qM_n :: 'q
    and buf_n ::
          "nat \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))"
    and end_pos_n :: "nat \<Rightarrow> 'c bp"
    and cM :: "('a, 'q) ktc_config"
  assumes vM:    "valid_ktm M"
      and lu:    "le_unique M"
      and cM_valid: "valid_config_ktm M cM"
      and qM_in: "qM \<in> Q_ktm M"
      and chain: "((qM, buf_full, \<lambda>k. (AE_Home, ofs k)),
                   (qM_n, buf_n, end_pos_n))
                      \<in> (m_step_buffered M) ^^ n"
      and st_eq: "ktc_state cM = qM"
      and window:
            "\<forall>k<k_ktm M. ae_window_invariant_general
                    (ktc_tape cM k) (ktc_pos cM k)
                    (AE_Home, ofs k) (buf_full k) (pos k) (le_ktm M)"
      and n_bound: "n \<le> card (UNIV :: 'c set)"
      and no_le:
            "\<forall>k. (pos k = 0
                    \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                              \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))
                 \<and> (pos k = 1
                      \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                                \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))
                 \<and> (pos k \<ge> 2
                      \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                                \<longrightarrow> ktc_tape cM k
                                      ((pos k - 2) * card (UNIV :: 'c set)
                                        + 1 + i)
                                    \<noteq> le_ktm M))"
      and left_not_le_pos0:
            "\<forall>k<k_ktm M. pos k = 0 \<longrightarrow> fst (buf_full k) \<noteq> LE_block (le_ktm M)"
  shows "\<exists>cM_n.
            (cM, cM_n) \<in> ktm_step (delta_ktm M) ^^ n
            \<and> ktc_state cM_n = qM_n
            \<and> (\<forall>k<k_ktm M. ae_window_invariant_general
                      (ktc_tape cM_n k) (ktc_pos cM_n k)
                      (end_pos_n k) (buf_n k) (pos k) (le_ktm M))
            \<and> (\<forall>k. (pos k = 0
                       \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                                  \<longrightarrow> ktc_tape cM_n k (Suc i) \<noteq> le_ktm M))
                    \<and> (pos k = 1
                          \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                                    \<longrightarrow> ktc_tape cM_n k (Suc i) \<noteq> le_ktm M))
                    \<and> (pos k \<ge> 2
                          \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                                    \<longrightarrow> ktc_tape cM_n k
                                          ((pos k - 2) * card (UNIV :: 'c set)
                                            + 1 + i)
                                        \<noteq> le_ktm M)))
            \<and> (\<forall>k<k_ktm M. pos k = 0
                       \<longrightarrow> fst (buf_n k) \<noteq> LE_block (le_ktm M))
            \<and> (\<forall>k. card (UNIV :: 'c set) \<le> bp_linear (end_pos_n k) + n
                    \<and> bp_linear (end_pos_n k)
                          < 2 * card (UNIV :: 'c set) + n)"
  using chain n_bound
proof (induction n arbitrary: qM_n buf_n end_pos_n)
  case 0
  \<comment> \<open>Base case: zero buffered steps means the chain endpoint
    \<open>(qM_n, buf_n, end_pos_n)\<close> equals the start
    \<open>(qM, buf_full, AE_Home offsets)\<close>; witness \<open>cM_n = cM\<close>
    and the substrate trace of length 0 is trivial.  All six
    output conjuncts lift directly from the lemma's input
    hypotheses.\<close>
  from "0.prems"(1) have eq:
      "(qM_n, buf_n, end_pos_n) = (qM, buf_full, \<lambda>k. (AE_Home, ofs k))"
    by simp
  have qM_n_eq:     "qM_n = qM"             using eq by simp
  have buf_n_eq:    "buf_n = buf_full"      using eq by simp
  have end_pos_eq:  "end_pos_n = (\<lambda>k. (AE_Home, ofs k))" using eq by simp
  show ?case
  proof (intro exI [where x = cM] conjI)
    show "(cM, cM) \<in> ktm_step (delta_ktm M) ^^ 0" by simp
    show "ktc_state cM = qM_n" using st_eq qM_n_eq by simp
    show "\<forall>k<k_ktm M. ae_window_invariant_general
                  (ktc_tape cM k) (ktc_pos cM k)
                  (end_pos_n k) (buf_n k) (pos k) (le_ktm M)"
      using window buf_n_eq end_pos_eq by simp
    show "\<forall>k. (pos k = 0
                 \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                            \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))
              \<and> (pos k = 1
                   \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                             \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))
              \<and> (pos k \<ge> 2
                   \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                             \<longrightarrow> ktc_tape cM k
                                   ((pos k - 2) * card (UNIV :: 'c set)
                                     + 1 + i)
                                 \<noteq> le_ktm M))"
      using no_le by simp
    show "\<forall>k<k_ktm M. pos k = 0 \<longrightarrow> fst (buf_n k) \<noteq> LE_block (le_ktm M)"
      using left_not_le_pos0 buf_n_eq by simp
    show "\<forall>k. card (UNIV :: 'c set) \<le> bp_linear (end_pos_n k) + 0
                \<and> bp_linear (end_pos_n k) < 2 * card (UNIV :: 'c set) + 0"
    proof (intro allI conjI)
      fix k
      have lin_eq: "bp_linear (end_pos_n k)
                       = card (UNIV :: 'c set) + c_idx (ofs k)"
        using end_pos_eq unfolding bp_linear_def by simp
      have idx_lt: "c_idx (ofs k) < card (UNIV :: 'c set)"
        by (rule c_idx_lt_card)
      show "card (UNIV :: 'c set) \<le> bp_linear (end_pos_n k) + 0"
        using lin_eq by simp
      show "bp_linear (end_pos_n k) < 2 * card (UNIV :: 'c set) + 0"
        using lin_eq idx_lt by simp
    qed
  qed
next
  case (Suc n')
  \<comment> \<open>Inductive step.  Peel the LAST \<open>m_step_buffered\<close> step
    via \<open>relpow_Suc_E\<close> to an intermediate
    \<open>(qM_n', buf_n', end_pos_n')\<close>.  Apply the IH at \<open>n'\<close>
    to obtain an intermediate substrate config \<open>cM_n'\<close> with
    \<open>ktc_state cM_n' = qM_n'\<close>, the window invariant, and the
    four threaded conjuncts.  Use Step 2a's
    \<open>m_step_buffered_lift_to_tape_general\<close> to extract one
    substrate \<open>ktm_step\<close> from \<open>cM_n'\<close> to a fresh
    \<open>cM_n\<close>; compose via \<open>relpow_Suc_I\<close>.  Re-derive the
    four threaded conjuncts at length \<open>Suc n'\<close>.\<close>
  have n'_bound: "n' \<le> card (UNIV :: 'c set)"
    using Suc.prems(2) by linarith
  from Suc.prems(1) obtain s_n' where
      chain_n':  "((qM, buf_full, \<lambda>k. (AE_Home, ofs k)), s_n')
                      \<in> (m_step_buffered M) ^^ n'"
    and last_step_raw: "(s_n', (qM_n, buf_n, end_pos_n))
                          \<in> m_step_buffered M"
    by (rule relpow_Suc_E)
  obtain qM_n' buf_n' end_pos_n' where
      s_n'_eq: "s_n' = (qM_n', buf_n', end_pos_n')"
    by (cases s_n') auto
  have chain_n'_unp:
      "((qM, buf_full, \<lambda>k. (AE_Home, ofs k)),
        (qM_n', buf_n', end_pos_n')) \<in> (m_step_buffered M) ^^ n'"
    using chain_n' s_n'_eq by simp
  have last_step:
      "((qM_n', buf_n', end_pos_n'), (qM_n, buf_n, end_pos_n))
          \<in> m_step_buffered M"
    using last_step_raw s_n'_eq by simp
  \<comment> \<open>Invoke the IH at length \<open>n'\<close>.\<close>
  from Suc.IH[OF chain_n'_unp n'_bound]
  obtain cM_n' where
      trace_n': "(cM, cM_n') \<in> ktm_step (delta_ktm M) ^^ n'"
    and st_n':  "ktc_state cM_n' = qM_n'"
    and window_n':
          "\<forall>k<k_ktm M. ae_window_invariant_general
                  (ktc_tape cM_n' k) (ktc_pos cM_n' k)
                  (end_pos_n' k) (buf_n' k) (pos k) (le_ktm M)"
    and no_le_n':
          "\<forall>k. (pos k = 0
                   \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                             \<longrightarrow> ktc_tape cM_n' k (Suc i) \<noteq> le_ktm M))
                \<and> (pos k = 1
                     \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                               \<longrightarrow> ktc_tape cM_n' k (Suc i) \<noteq> le_ktm M))
                \<and> (pos k \<ge> 2
                     \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                               \<longrightarrow> ktc_tape cM_n' k
                                     ((pos k - 2) * card (UNIV :: 'c set)
                                       + 1 + i)
                                   \<noteq> le_ktm M))"
    and left_n':
          "\<forall>k<k_ktm M. pos k = 0
                   \<longrightarrow> fst (buf_n' k) \<noteq> LE_block (le_ktm M)"
    and bp_bound_n':
          "\<forall>k. card (UNIV :: 'c set) \<le> bp_linear (end_pos_n' k) + n'
                \<and> bp_linear (end_pos_n' k)
                       < 2 * card (UNIV :: 'c set) + n'"
    by blast
  \<comment> \<open>Validity of the intermediate config \<open>cM_n'\<close>, threaded
    along the IH's \<open>n'\<close>-step trace; supplies the leaf lift's
    blank-tail read-match on padding tapes.\<close>
  have cM_n'_valid: "valid_config_ktm M cM_n'"
    by (rule valid_reach_relpow_ktm[OF vM cM_valid trace_n'])
  \<comment> \<open>Per-tape strict bounds at \<open>n'\<close>: \<open>n' \<le> c - 1\<close>
    gives \<open>0 < bp_linear < 3c - 1\<close>.\<close>
  have c_pos: "1 \<le> card (UNIV :: 'c set)"
    using Suc.prems(2) by linarith
  have bp_lt_n':
      "\<forall>k. bp_linear (end_pos_n' k) < 3 * card (UNIV :: 'c set) - 1"
  proof (intro allI)
    fix k
    have lin_lt: "bp_linear (end_pos_n' k) < 2 * card (UNIV :: 'c set) + n'"
      using bp_bound_n' by blast
    show "bp_linear (end_pos_n' k) < 3 * card (UNIV :: 'c set) - 1"
      using lin_lt Suc.prems(2) c_pos by linarith
  qed
  have bp_pos_n':
      "\<forall>k. 0 < bp_linear (end_pos_n' k)"
  proof (intro allI)
    fix k
    have low: "card (UNIV :: 'c set) \<le> bp_linear (end_pos_n' k) + n'"
      using bp_bound_n' by blast
    show "0 < bp_linear (end_pos_n' k)"
      using low Suc.prems(2) c_pos by linarith
  qed
  \<comment> \<open>Per-tape no-LE-at-head at \<open>cM_n'\<close>, regime-dispatched
    (steady: read at head is not LE; le0/le1: window-wide no-LE
    on \<open>[1, c]\<close> or \<open>[1, 2c]\<close>).  Derived from the IH's
    \<open>no_le_n'\<close> conjunct.  The steady-regime case requires
    one extra step: \<open>ktc_pos cM_n' k = (pos k - 2)c + 1
    + bp_linear (end_pos_n' k)\<close> (from the window invariant),
    and \<open>bp_linear < 3c\<close> places the head inside the no-LE
    window.\<close>
  \<comment> \<open>Per-tape no-LE-at-head at \<open>cM_n'\<close>, regime-dispatched,
    derived from the IH's \<open>no_le_n'\<close> conjunct.  Split into
    three regime sublemmas, combined via \<open>blast\<close>.\<close>
  have head_le0:
      "\<forall>k. pos k = 0
              \<longrightarrow> (\<forall>i. 0 < i \<and> i \<le> card (UNIV :: 'c set)
                          \<longrightarrow> ktc_tape cM_n' k i \<noteq> le_ktm M)"
  proof (intro allI impI allI impI)
    fix k i
    assume pos_0: "pos k = 0"
       and i_bnd: "0 < i \<and> i \<le> card (UNIV :: 'c set)"
    then obtain j where i_eq: "i = Suc j"
                    and j_lt: "j < card (UNIV :: 'c set)"
      by (metis Suc_le_eq Suc_pred')
    from no_le_n' pos_0 j_lt
    have "ktc_tape cM_n' k (Suc j) \<noteq> le_ktm M" by blast
    thus "ktc_tape cM_n' k i \<noteq> le_ktm M" using i_eq by simp
  qed
  have head_le1:
      "\<forall>k. pos k = 1
              \<longrightarrow> (\<forall>i. 0 < i \<and> i \<le> 2 * card (UNIV :: 'c set)
                          \<longrightarrow> ktc_tape cM_n' k i \<noteq> le_ktm M)"
  proof (intro allI impI allI impI)
    fix k i
    assume pos_1: "pos k = 1"
       and i_bnd: "0 < i \<and> i \<le> 2 * card (UNIV :: 'c set)"
    then obtain j where i_eq: "i = Suc j"
                    and j_lt: "j < 2 * card (UNIV :: 'c set)"
      by (metis Suc_le_eq Suc_pred')
    from no_le_n' pos_1 j_lt
    have "ktc_tape cM_n' k (Suc j) \<noteq> le_ktm M" by blast
    thus "ktc_tape cM_n' k i \<noteq> le_ktm M" using i_eq by simp
  qed
  have head_steady:
      "\<forall>k<k_ktm M. pos k \<ge> 2
              \<longrightarrow> ktc_tape cM_n' k (ktc_pos cM_n' k) \<noteq> le_ktm M"
  proof (intro allI impI impI)
    fix k
    assume klt: "k < k_ktm M" and pos_ge: "pos k \<ge> 2"
    let ?c = "card (UNIV :: 'c set)"
    have wi_k: "ae_window_invariant_general
                    (ktc_tape cM_n' k) (ktc_pos cM_n' k)
                    (end_pos_n' k) (buf_n' k) (pos k) (le_ktm M)"
      using window_n' klt by blast
    have wi_steady: "ae_window_invariant
                        (ktc_tape cM_n' k) (ktc_pos cM_n' k)
                        (end_pos_n' k) (buf_n' k)
                        ((pos k - 2) * ?c + 1)"
      using wi_k pos_ge
      unfolding ae_window_invariant_general_def by simp
    have head_eq: "ktc_pos cM_n' k
                       = (pos k - 2) * ?c + 1
                         + bp_linear (end_pos_n' k)"
      using wi_steady unfolding ae_window_invariant_def by simp
    have lin_lt_3c: "bp_linear (end_pos_n' k) < 3 * ?c"
    proof -
      have step: "bp_linear (end_pos_n' k) < 3 * ?c - 1"
        using bp_lt_n' by blast
      show ?thesis using step c_pos by linarith
    qed
    from no_le_n' pos_ge lin_lt_3c
    have "ktc_tape cM_n' k
              ((pos k - 2) * ?c + 1 + bp_linear (end_pos_n' k))
            \<noteq> le_ktm M" by blast
    thus "ktc_tape cM_n' k (ktc_pos cM_n' k) \<noteq> le_ktm M"
      using head_eq by simp
  qed
  have no_le_step2a:
      "\<forall>k<k_ktm M. (pos k = 0
              \<longrightarrow> (\<forall>i. 0 < i \<and> i \<le> card (UNIV :: 'c set)
                          \<longrightarrow> ktc_tape cM_n' k i \<noteq> le_ktm M))
           \<and> (pos k = 1
                \<longrightarrow> (\<forall>i. 0 < i \<and> i \<le> 2 * card (UNIV :: 'c set)
                            \<longrightarrow> ktc_tape cM_n' k i \<noteq> le_ktm M))
           \<and> (pos k \<ge> 2
                \<longrightarrow> ktc_tape cM_n' k (ktc_pos cM_n' k) \<noteq> le_ktm M)"
    using head_le0 head_le1 head_steady by blast
  \<comment> \<open>Apply Step 2a (single-step lift) to extract the substrate
    step from \<open>last_step\<close>.\<close>
  obtain cM_n where
      step_extracted:
        "(cM_n', cM_n) \<in> ktm_step (delta_ktm M)
         \<and> ktc_state cM_n = qM_n
         \<and> (\<forall>k<k_ktm M. ae_window_invariant_general
                    (ktc_tape cM_n k) (ktc_pos cM_n k)
                    (end_pos_n k) (buf_n k) (pos k) (le_ktm M))"
    using m_step_buffered_lift_to_tape_general
            [OF vM lu cM_n'_valid last_step st_n' window_n' bp_lt_n' bp_pos_n'
                no_le_step2a] by blast
  have step_one:  "(cM_n', cM_n) \<in> ktm_step (delta_ktm M)"
    using step_extracted by simp
  have st_n_eq:   "ktc_state cM_n = qM_n"
    using step_extracted by simp
  have window_n:
      "\<forall>k<k_ktm M. ae_window_invariant_general
              (ktc_tape cM_n k) (ktc_pos cM_n k)
              (end_pos_n k) (buf_n k) (pos k) (le_ktm M)"
    using step_extracted by simp
  have trace_n:
      "(cM, cM_n) \<in> ktm_step (delta_ktm M) ^^ (Suc n')"
    using trace_n' step_one by (rule relpow_Suc_I)
  \<comment> \<open>Re-derive the \<open>cM_n\<close> / \<open>cM_n'\<close> relation in
    \<open>ktm_step\<close>-shape: \<open>ktm_step.cases\<close> on
    \<open>step_one\<close> unpacks the delta tuple and the tape
    update.\<close>
  obtain ts_pre n_pre q_post a_step dir_step where
      cM_n'_eq: "cM_n' = KConfig qM_n' ts_pre n_pre"
    and cM_n_eq:
        "cM_n = KConfig q_post
                  (\<lambda>k. (ts_pre k)(n_pre k := a_step k))
                  (\<lambda>k. go_move (dir_step k) (n_pre k))"
    and delta_mem:
        "(qM_n', \<lambda>k. ts_pre k (n_pre k),
            q_post, a_step, dir_step) \<in> delta_ktm M"
  proof -
    from step_one obtain q_pre' ts_pre' n_pre' q_post' a_step' dir_step'
      where step_unp:
        "cM_n' = KConfig q_pre' ts_pre' n_pre'"
        "cM_n = KConfig q_post'
                  (\<lambda>k. (ts_pre' k)(n_pre' k := a_step' k))
                  (\<lambda>k. go_move (dir_step' k) (n_pre' k))"
        "(q_pre', \<lambda>k. ts_pre' k (n_pre' k),
              q_post', a_step', dir_step') \<in> delta_ktm M"
      by (rule ktm_step.cases)
    have q_pre'_eq: "q_pre' = qM_n'"
      using step_unp(1) st_n' by simp
    show thesis using step_unp q_pre'_eq that by simp
  qed
  have tp_n':  "ktc_tape cM_n' = ts_pre" using cM_n'_eq by simp
  have tp_n:   "\<forall>k. ktc_tape cM_n k
                       = (ts_pre k)(n_pre k := a_step k)"
    using cM_n_eq by auto
  \<comment> \<open>Conjunct 3 threading: new \<open>no_le\<close> at \<open>cM_n\<close>.
    Mirrors the forward direction.  Three regime branches; for
    each cell in the window, case-split on whether the M-step's
    update site \<open>n_pre k\<close> coincides; if it does, use the
    LE-write contrapositive \<open>valid_ktm_deltaLE_no_write\<close>.\<close>
  have no_le_contra:
      "\<forall>k. ts_pre k (n_pre k) \<noteq> le_ktm M
              \<longrightarrow> a_step k \<noteq> le_ktm M"
  proof (intro allI impI)
    fix k
    assume rd_not_le: "ts_pre k (n_pre k) \<noteq> le_ktm M"
    show "a_step k \<noteq> le_ktm M"
    proof
      assume a_le: "a_step k = le_ktm M"
      have "(\<lambda>k. ts_pre k (n_pre k)) k = le_ktm M"
        by (rule valid_ktm_deltaLE_no_write[OF lu delta_mem a_le])
      hence "ts_pre k (n_pre k) = le_ktm M" by simp
      with rd_not_le show False ..
    qed
  qed
  have no_le0_n:
      "\<forall>k. pos k = 0
              \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                        \<longrightarrow> ktc_tape cM_n k (Suc i) \<noteq> le_ktm M)"
  proof (intro allI impI allI impI)
    fix k i
    assume pos_0: "pos k = 0"
       and i_bd: "i < card (UNIV :: 'c set)"
    have ih_at: "ts_pre k (Suc i) \<noteq> le_ktm M"
    proof -
      from no_le_n' pos_0 i_bd
      have "ktc_tape cM_n' k (Suc i) \<noteq> le_ktm M" by blast
      thus ?thesis using tp_n' by simp
    qed
    show "ktc_tape cM_n k (Suc i) \<noteq> le_ktm M"
    proof (cases "Suc i = n_pre k")
      case False
      hence "ktc_tape cM_n k (Suc i) = ts_pre k (Suc i)"
        using tp_n by simp
      thus ?thesis using ih_at by simp
    next
      case True
      hence tape_eq: "ktc_tape cM_n k (Suc i) = a_step k"
        using tp_n by simp
      from True have "ts_pre k (n_pre k) = ts_pre k (Suc i)"
        by simp
      with ih_at have "ts_pre k (n_pre k) \<noteq> le_ktm M" by simp
      hence "a_step k \<noteq> le_ktm M" using no_le_contra by blast
      thus ?thesis using tape_eq by simp
    qed
  qed
  have no_le1_n:
      "\<forall>k. pos k = 1
              \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                        \<longrightarrow> ktc_tape cM_n k (Suc i) \<noteq> le_ktm M)"
  proof (intro allI impI allI impI)
    fix k i
    assume pos_1: "pos k = 1"
       and i_bd: "i < 2 * card (UNIV :: 'c set)"
    have ih_at: "ts_pre k (Suc i) \<noteq> le_ktm M"
    proof -
      from no_le_n' pos_1 i_bd
      have "ktc_tape cM_n' k (Suc i) \<noteq> le_ktm M" by blast
      thus ?thesis using tp_n' by simp
    qed
    show "ktc_tape cM_n k (Suc i) \<noteq> le_ktm M"
    proof (cases "Suc i = n_pre k")
      case False
      hence "ktc_tape cM_n k (Suc i) = ts_pre k (Suc i)"
        using tp_n by simp
      thus ?thesis using ih_at by simp
    next
      case True
      hence tape_eq: "ktc_tape cM_n k (Suc i) = a_step k"
        using tp_n by simp
      from True have "ts_pre k (n_pre k) = ts_pre k (Suc i)"
        by simp
      with ih_at have "ts_pre k (n_pre k) \<noteq> le_ktm M" by simp
      hence "a_step k \<noteq> le_ktm M" using no_le_contra by blast
      thus ?thesis using tape_eq by simp
    qed
  qed
  have no_le2_n:
      "\<forall>k. pos k \<ge> 2
              \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                        \<longrightarrow> ktc_tape cM_n k
                              ((pos k - 2) * card (UNIV :: 'c set) + 1 + i)
                            \<noteq> le_ktm M)"
  proof (intro allI impI allI impI)
    fix k i
    assume pos_ge: "pos k \<ge> 2"
       and i_bd: "i < 3 * card (UNIV :: 'c set)"
    let ?j = "(pos k - 2) * card (UNIV :: 'c set) + 1 + i"
    have ih_at: "ts_pre k ?j \<noteq> le_ktm M"
    proof -
      from no_le_n' pos_ge i_bd
      have "ktc_tape cM_n' k ?j \<noteq> le_ktm M" by blast
      thus ?thesis using tp_n' by simp
    qed
    show "ktc_tape cM_n k ?j \<noteq> le_ktm M"
    proof (cases "?j = n_pre k")
      case False
      hence "ktc_tape cM_n k ?j = ts_pre k ?j"
        using tp_n by simp
      thus ?thesis using ih_at by simp
    next
      case True
      hence tape_eq: "ktc_tape cM_n k ?j = a_step k"
        using tp_n by simp
      from True have "ts_pre k (n_pre k) = ts_pre k ?j"
        by simp
      with ih_at have "ts_pre k (n_pre k) \<noteq> le_ktm M" by simp
      hence "a_step k \<noteq> le_ktm M" using no_le_contra by blast
      thus ?thesis using tape_eq by simp
    qed
  qed
  have no_le_n:
      "\<forall>k. (pos k = 0
              \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                        \<longrightarrow> ktc_tape cM_n k (Suc i) \<noteq> le_ktm M))
           \<and> (pos k = 1
                \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                          \<longrightarrow> ktc_tape cM_n k (Suc i) \<noteq> le_ktm M))
           \<and> (pos k \<ge> 2
                \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                          \<longrightarrow> ktc_tape cM_n k
                                ((pos k - 2) * card (UNIV :: 'c set)
                                  + 1 + i)
                              \<noteq> le_ktm M))"
    using no_le0_n no_le1_n no_le2_n by blast
  \<comment> \<open>Conjunct 4 threading: \<open>left_not_le_pos0\<close> at \<open>buf_n\<close>.
    The buffered write at \<open>end_pos_n' k\<close> changes
    \<open>buf_n' k\<close> at the \<open>AE_Left\<close> / \<open>AE_Home\<close> / \<open>AE_Right\<close> block
    depending on \<open>fst (end_pos_n' k)\<close>.  For \<open>pos k = 0\<close>,
    the regime invariant \<open>ae_window_invariant_le0\<close> forces
    the buffered head to be in the Home block (so the Left
    block is unchanged), giving \<open>fst (buf_n k) = fst (buf_n' k)\<close>;
    apply the IH (\<open>left_n'\<close>).\<close>
  from last_step obtain a_buf a'_buf d_buf where
      delta_buf: "(qM_n', a_buf, qM_n, a'_buf, d_buf) \<in> delta_ktm M"
    and read_buf: "\<forall>k. a_buf k = read_bp (buf_n' k) (end_pos_n' k)"
    and write_buf: "\<forall>k. buf_n k
                            = write_bp (buf_n' k) (end_pos_n' k) (a'_buf k)"
    and adv_buf: "\<forall>k. bp_advance_le (le_ktm M) (a_buf k)
                              (end_pos_n' k) (d_buf k)
                          = Some (end_pos_n k)"
    unfolding m_step_buffered_def by auto
  have left_n:
      "\<forall>k<k_ktm M. pos k = 0 \<longrightarrow> fst (buf_n k) \<noteq> LE_block (le_ktm M)"
  proof (intro allI impI impI)
    fix k
    assume klt: "k < k_ktm M" and pos_0: "pos k = 0"
    have wi_k: "ae_window_invariant_general
                    (ktc_tape cM_n' k) (ktc_pos cM_n' k)
                    (end_pos_n' k) (buf_n' k) (pos k) (le_ktm M)"
      using window_n' klt by blast
    have wi_l0: "ae_window_invariant_le0
                    (ktc_tape cM_n' k) (ktc_pos cM_n' k)
                    (end_pos_n' k) (buf_n' k) (le_ktm M)"
      using wi_k pos_0
      unfolding ae_window_invariant_general_def by simp
    have head_home_or_right:
        "fst (end_pos_n' k) \<in> {AE_Home, AE_Right}"
    proof (cases "fst (end_pos_n' k)")
      case AE_Left
      have "False"
        using wi_l0 AE_Left
        unfolding ae_window_invariant_le0_def by simp
      thus ?thesis ..
    qed auto
    obtain l h r where buf_n'_eq:
        "buf_n' k = (l, h, r)" by (cases "buf_n' k") auto
    obtain b off where end_eq:
        "end_pos_n' k = (b, off)" by (cases "end_pos_n' k") auto
    from head_home_or_right end_eq have b_in: "b \<in> {AE_Home, AE_Right}" by simp
    have fst_buf_n:
        "fst (buf_n k) = fst (buf_n' k)"
    proof -
      have wb_eq: "buf_n k
                    = write_bp (buf_n' k) (end_pos_n' k) (a'_buf k)"
        using write_buf by blast
      consider (home) "b = AE_Home" | (right) "b = AE_Right"
        using b_in by blast
      thus ?thesis
      proof cases
        case home
        have "write_bp (buf_n' k) (end_pos_n' k) (a'_buf k)
                = (l, h(off := a'_buf k), r)"
          using buf_n'_eq end_eq home
          unfolding write_bp_def by simp
        thus ?thesis using wb_eq buf_n'_eq by simp
      next
        case right
        have "write_bp (buf_n' k) (end_pos_n' k) (a'_buf k)
                = (l, h, r(off := a'_buf k))"
          using buf_n'_eq end_eq right
          unfolding write_bp_def by simp
        thus ?thesis using wb_eq buf_n'_eq by simp
      qed
    qed
    show "fst (buf_n k) \<noteq> LE_block (le_ktm M)"
      using fst_buf_n left_n' klt pos_0 by simp
  qed
  \<comment> \<open>Conjunct 5 threading: \<open>bp_bound\<close> at \<open>end_pos_n\<close>.
    One \<open>m_step_buffered\<close> step shifts \<open>bp_linear\<close> by at most 1
    (R: +1, L: -1, N: 0), via \<open>bp_advance_le\<close>.  The new
    bounds follow from the IH bounds and the advance equation.
    Helper: \<open>bp_advance_le_lin_bounded\<close> (in Setup).\<close>
  have bp_bound_n:
      "\<forall>k. card (UNIV :: 'c set) \<le> bp_linear (end_pos_n k) + Suc n'
            \<and> bp_linear (end_pos_n k)
                 < 2 * card (UNIV :: 'c set) + Suc n'"
  proof (intro allI)
    fix k
    have low_n':
        "card (UNIV :: 'c set) \<le> bp_linear (end_pos_n' k) + n'"
      using bp_bound_n' by blast
    have high_n':
        "bp_linear (end_pos_n' k) < 2 * card (UNIV :: 'c set) + n'"
      using bp_bound_n' by blast
    have pos_n': "0 < bp_linear (end_pos_n' k)"
      using bp_pos_n' by blast
    have adv_k: "bp_advance_le (le_ktm M) (a_buf k) (end_pos_n' k) (d_buf k)
                    = Some (end_pos_n k)"
      using adv_buf by blast
    show "card (UNIV :: 'c set) \<le> bp_linear (end_pos_n k) + Suc n'
            \<and> bp_linear (end_pos_n k)
                  < 2 * card (UNIV :: 'c set) + Suc n'"
      by (rule bp_advance_le_lin_bounded
              [OF adv_k pos_n' high_n' low_n'])
  qed
  \<comment> \<open>Assemble the six output conjuncts.\<close>
  show ?case
  proof (intro exI [where x = cM_n] conjI)
    show "(cM, cM_n) \<in> ktm_step (delta_ktm M) ^^ Suc n'"
      using trace_n .
    show "ktc_state cM_n = qM_n" using st_n_eq .
    show "\<forall>k<k_ktm M. ae_window_invariant_general
                  (ktc_tape cM_n k) (ktc_pos cM_n k)
                  (end_pos_n k) (buf_n k) (pos k) (le_ktm M)"
      using window_n .
    show "\<forall>k. (pos k = 0
                 \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                            \<longrightarrow> ktc_tape cM_n k (Suc i) \<noteq> le_ktm M))
              \<and> (pos k = 1
                   \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                             \<longrightarrow> ktc_tape cM_n k (Suc i) \<noteq> le_ktm M))
              \<and> (pos k \<ge> 2
                   \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                             \<longrightarrow> ktc_tape cM_n k
                                   ((pos k - 2) * card (UNIV :: 'c set)
                                     + 1 + i)
                                 \<noteq> le_ktm M))"
      using no_le_n .
    show "\<forall>k<k_ktm M. pos k = 0
                 \<longrightarrow> fst (buf_n k) \<noteq> LE_block (le_ktm M)"
      using left_n .
    show "\<forall>k. card (UNIV :: 'c set) \<le> bp_linear (end_pos_n k) + Suc n'
                \<and> bp_linear (end_pos_n k)
                      < 2 * card (UNIV :: 'c set) + Suc n'"
      using bp_bound_n .
  qed
qed


text \<open>User-facing reverse lift on
  \<open>m_steps_buffered\<close>.  Wraps Step 2b-aux
  (\<open>m_step_buffered_chain_lift_to_tape\<close>) by unfolding
  the existential \<open>n\<close> in \<open>m_steps_buffered M\<close>,
  applying the aux induction, and exposing the result via an
  \<open>obtains\<close>-form interface.  Preserves the halt-exit
  disjunction (\<open>n = c \<or> final state \<in> {t, r}\<close>) on
  the substrate side.

  Consumed by \<open>ae_backward_stage\<close> to extract the substrate
  M-side trace from an SS4\<open>\<rightarrow>\<close>SS5 buffered chunk.\<close>

lemma m_steps_buffered_lift_to_tape:
  fixes M :: "('q, 'a) ktm"
    and qM :: 'q
    and ofs :: "nat \<Rightarrow> 'c :: enum"
    and buf_full ::
          "nat \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))"
    and pos :: "nat \<Rightarrow> nat"
    and qM_end :: 'q
    and buf_end ::
          "nat \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))"
    and end_pos_bp :: "nat \<Rightarrow> 'c bp"
    and cM :: "('a, 'q) ktc_config"
  assumes vM:    "valid_ktm M"
      and lu:    "le_unique M"
      and cM_valid: "valid_config_ktm M cM"
      and qM_in: "qM \<in> Q_ktm M"
      and steps: "((qM, buf_full, \<lambda>k. (AE_Home, ofs k)),
                   (qM_end, buf_end, end_pos_bp))
                      \<in> m_steps_buffered M"
      and st_eq: "ktc_state cM = qM"
      and window:
            "\<forall>k<k_ktm M. ae_window_invariant_general
                    (ktc_tape cM k) (ktc_pos cM k)
                    (AE_Home, ofs k) (buf_full k) (pos k) (le_ktm M)"
      and no_le:
            "\<forall>k. (pos k = 0
                    \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                              \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))
                 \<and> (pos k = 1
                      \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                                \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))
                 \<and> (pos k \<ge> 2
                      \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                                \<longrightarrow> ktc_tape cM k
                                      ((pos k - 2) * card (UNIV :: 'c set)
                                        + 1 + i)
                                    \<noteq> le_ktm M))"
      and left_not_le_pos0:
            "\<forall>k<k_ktm M. pos k = 0 \<longrightarrow> fst (buf_full k) \<noteq> LE_block (le_ktm M)"
  obtains cM_end n where
      "(cM, cM_end) \<in> ktm_step (delta_ktm M) ^^ n"
    and "n \<le> card (UNIV :: 'c set)"
    and "n = card (UNIV :: 'c set) \<or> ktc_state cM_end \<in> {t_ktm M, r_ktm M}"
    and "ktc_state cM_end = qM_end"
    and "\<forall>k<k_ktm M. ae_window_invariant_general
                (ktc_tape cM_end k) (ktc_pos cM_end k)
                (end_pos_bp k) (buf_end k) (pos k) (le_ktm M)"
    and "\<forall>k. (pos k = 0
                 \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                           \<longrightarrow> ktc_tape cM_end k (Suc i) \<noteq> le_ktm M))
              \<and> (pos k = 1
                   \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                             \<longrightarrow> ktc_tape cM_end k (Suc i) \<noteq> le_ktm M))
              \<and> (pos k \<ge> 2
                   \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                             \<longrightarrow> ktc_tape cM_end k
                                   ((pos k - 2) * card (UNIV :: 'c set)
                                     + 1 + i)
                                 \<noteq> le_ktm M))"
    and "\<forall>k<k_ktm M. pos k = 0
                \<longrightarrow> fst (buf_end k) \<noteq> LE_block (le_ktm M)"
proof -
  \<comment> \<open>Unfold \<open>m_steps_buffered\<close>'s existential.\<close>
  from steps obtain n where
      chain_n: "((qM, buf_full, \<lambda>k. (AE_Home, ofs k)),
                 (qM_end, buf_end, end_pos_bp))
                    \<in> (m_step_buffered M) ^^ n"
    and n_bnd: "n \<le> card (UNIV :: 'c set)"
    and halt_or_full:
        "n = card (UNIV :: 'c set) \<or> qM_end \<in> {t_ktm M, r_ktm M}"
    unfolding m_steps_buffered_def by auto
  \<comment> \<open>Invoke Step 2b-aux to obtain the substrate trace plus
    the threaded invariants at \<open>cM_n\<close>.\<close>
  from m_step_buffered_chain_lift_to_tape
        [OF vM lu cM_valid qM_in chain_n st_eq window n_bnd no_le
            left_not_le_pos0]
  obtain cM_end where
      trace_n:  "(cM, cM_end) \<in> ktm_step (delta_ktm M) ^^ n"
    and st_eq_n: "ktc_state cM_end = qM_end"
    and window_n:
        "\<forall>k<k_ktm M. ae_window_invariant_general
                (ktc_tape cM_end k) (ktc_pos cM_end k)
                (end_pos_bp k) (buf_end k) (pos k) (le_ktm M)"
    and no_le_n:
        "\<forall>k. (pos k = 0
                 \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                            \<longrightarrow> ktc_tape cM_end k (Suc i) \<noteq> le_ktm M))
              \<and> (pos k = 1
                   \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                              \<longrightarrow> ktc_tape cM_end k (Suc i) \<noteq> le_ktm M))
              \<and> (pos k \<ge> 2
                   \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                              \<longrightarrow> ktc_tape cM_end k
                                    ((pos k - 2) * card (UNIV :: 'c set)
                                      + 1 + i)
                                  \<noteq> le_ktm M))"
    and left_n:
        "\<forall>k<k_ktm M. pos k = 0 \<longrightarrow> fst (buf_end k) \<noteq> LE_block (le_ktm M)"
    by blast
  have halt_or_full_substrate:
      "n = card (UNIV :: 'c set) \<or> ktc_state cM_end \<in> {t_ktm M, r_ktm M}"
    using halt_or_full st_eq_n by simp
  show ?thesis
    by (rule that[OF trace_n n_bnd halt_or_full_substrate
                       st_eq_n window_n no_le_n left_n])
qed


subsubsection \<open>Taking apart a step from substep 4 to substep 5\<close>

text \<open>Reverse-direction counterpart of
  \<open>ae_step_ss4_ss5_construct_from_buffered\<close>.  Given an
  SS4\<open>\<rightarrow>\<close>SS5 substrate step, destructure it to
  expose the SS4 source structure, the SS5 target structure, and
  the inner buffered chain.  Consumed by
  \<open>ae_backward_stage_compute_extract\<close>.

  No \<open>ae_inv_ss4\<close> hypothesis is required: the relation
  \<open>ae_delta_ss4_ss5\<close> itself pins the source state shape
  (\<open>substep_idx\<close> = SS4, \<open>q \<in> Q_ktm M\<close>,
  \<open>q \<noteq> t_ktm M\<close>, \<open>q \<noteq> r_ktm M\<close>)
  and exposes the buffered chain. The destruct is therefore a
  purely structural elimination of \<open>ktm_step.cases\<close>
  followed by an unfold of \<open>ae_delta_ss4_ss5_def\<close>.\<close>

lemma ae_step_ss4_ss5_destruct_to_buffered:
  fixes M :: "('q, 'a) ktm"
    and c c' :: "('c :: enum \<Rightarrow> 'a,
                  'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes step: "(c, c') \<in> ktm_step (ae_delta_ss4_ss5 M)"
  obtains q ofs buf dest_old ts n q_out buf' bufC end_pos where
      "c = KConfig (q, ofs, buf, dest_old, SS4) ts n"
    and "ktc_state c' = (q_out,
                        \<lambda>k. if k < k_ktm M then snd (end_pos k)
                              else init_offset k,
                        buf',
                        \<lambda>k. if k < k_ktm M then fst (end_pos k)
                              else init_dest k, SS5)"
    and "buf' = (\<lambda>k. if k < k_ktm M then bufC k
                       else init_buffer (le_ktm M) k)"
    and "ktc_tape c' = ts"
    and "ktc_pos c'
           = (\<lambda>k. go_move (if k < k_ktm M
                            then (if ts k (n k) = LE_block (le_ktm M)
                                    then MoveN else MoveL)
                            else MoveN)
                         (n k))"
    and "q \<in> Q_ktm M"
    and "q \<noteq> t_ktm M"
    and "q \<noteq> r_ktm M"
    and "\<forall>j\<ge>k_ktm M. ts j (n j) = bl_block (bl_ktm M)"
    and "((q, \<lambda>k. (fst (buf k),
                    if k < k_ktm M then fst (snd (buf k)) else ts k (n k),
                    ts k (n k)),
            \<lambda>k. (AE_Home, ofs k)),
           (q_out, bufC, end_pos)) \<in> m_steps_buffered M"
proof -
  from step obtain s tsP nP s' aP dP where
      cP_eq: "c = KConfig s tsP nP"
      and c'_eq: "c' = KConfig s' (\<lambda>k. (tsP k)(nP k := aP k))
                                   (\<lambda>k. go_move (dP k) (nP k))"
      and rel: "(s, (\<lambda>k. tsP k (nP k)), s', aP, dP)
                  \<in> ae_delta_ss4_ss5 M"
    by (auto elim: ktm_step.cases)
  from rel obtain q ofs buf dest_old q_out ofs' buf' dest'
                  buf_full end_pos bufC
    where s_eq: "s = (q, ofs, buf, dest_old, SS4)"
      and s'_eq: "s' = (q_out, ofs', buf', dest', SS5)"
      and a_eq: "aP = (\<lambda>k. tsP k (nP k))"
      and q_in_Q: "q \<in> Q_ktm M"
      and q_neq_t_M: "q \<noteq> t_ktm M"
      and q_neq_r_M: "q \<noteq> r_ktm M"
      and supp: "\<forall>j\<ge>k_ktm M. tsP j (nP j) = bl_block (bl_ktm M)"
      and buf_full_eq: "buf_full
                         = (\<lambda>k. (fst (buf k),
                                  if k < k_ktm M then fst (snd (buf k))
                                    else tsP k (nP k),
                                  tsP k (nP k)))"
      and m_steps_raw: "((q, buf_full, \<lambda>k. (AE_Home, ofs k)),
                          (q_out, bufC, end_pos))
                            \<in> m_steps_buffered M"
      and ofs'_eq: "ofs' = (\<lambda>k. if k < k_ktm M then snd (end_pos k)
                                  else init_offset k)"
      and buf'_eq: "buf' = (\<lambda>k. if k < k_ktm M then bufC k
                                  else init_buffer (le_ktm M) k)"
      and dest'_eq: "dest' = (\<lambda>k. if k < k_ktm M then fst (end_pos k)
                                   else init_dest k)"
      and d_eq: "dP = (\<lambda>k. if k < k_ktm M
                             then (if tsP k (nP k) = LE_block (le_ktm M)
                                     then MoveN else MoveL)
                             else MoveN)"
    by (auto simp: ae_delta_ss4_ss5_def)
  have ts_write_unchanged: "(\<lambda>k. (tsP k)(nP k := aP k)) = tsP"
    using a_eq by (auto intro!: ext)
  show thesis
  proof (rule that[where q=q and ofs=ofs and buf=buf
                     and dest_old=dest_old and ts=tsP and n=nP
                     and q_out=q_out and buf'=buf' and bufC=bufC
                     and end_pos=end_pos])
    show "c = KConfig (q, ofs, buf, dest_old, SS4) tsP nP"
      using cP_eq s_eq by simp
    show "ktc_state c' = (q_out,
                         \<lambda>k. if k < k_ktm M then snd (end_pos k)
                               else init_offset k,
                         buf',
                         \<lambda>k. if k < k_ktm M then fst (end_pos k)
                               else init_dest k, SS5)"
      using c'_eq s'_eq ofs'_eq dest'_eq by simp
    show "buf' = (\<lambda>k. if k < k_ktm M then bufC k
                        else init_buffer (le_ktm M) k)"
      by (rule buf'_eq)
    show "ktc_tape c' = tsP"
      using c'_eq ts_write_unchanged by simp
    show "ktc_pos c'
            = (\<lambda>k. go_move (if k < k_ktm M
                             then (if tsP k (nP k) = LE_block (le_ktm M)
                                     then MoveN else MoveL)
                             else MoveN)
                          (nP k))"
      using c'_eq d_eq by simp
    show "q \<in> Q_ktm M" by (rule q_in_Q)
    show "q \<noteq> t_ktm M" by (rule q_neq_t_M)
    show "q \<noteq> r_ktm M" by (rule q_neq_r_M)
    show "\<forall>j\<ge>k_ktm M. tsP j (nP j) = bl_block (bl_ktm M)" by (rule supp)
    show "((q, \<lambda>k. (fst (buf k),
                     if k < k_ktm M then fst (snd (buf k)) else tsP k (nP k),
                     tsP k (nP k)),
              \<lambda>k. (AE_Home, ofs k)),
            (q_out, bufC, end_pos)) \<in> m_steps_buffered M"
      using m_steps_raw buf_full_eq by simp
  qed
qed


subsubsection \<open>Backward stage: load, compute, writeback\<close>

text \<open>\<^emph>\<open>Reverse-direction counterpart of \<open>ae_forward_stage_load_chain\<close>.\<close>
  Given a 3-step \<open>alphabet_enlarge_delta\<close>-chain
  \<open>c' \<rightarrow>^3 c3\<close> with \<open>c'\<close> at SS1 with the
  forward-direction invariants, identifies the three buffer-load
  substeps (SS1\<open>\<rightarrow>\<close>SS2, SS2\<open>\<rightarrow>\<close>SS3,
  SS3\<open>\<rightarrow>\<close>SS4), commits each peeled step to its
  canonical substep relation via
  \<open>ktm_step_ae_delta_ssN_only\<close>, and propagates the
  invariant bundle (\<open>ae_inv_ss4\<close>,
  \<open>ae_tape_in_gamma_block\<close>,
  \<open>ae_buffer_in_gamma_block\<close>, state preservation,
  \<open>ae_position_link\<close>) to \<open>c3\<close>.  Side-band
  preservation reuses the direction-agnostic lemmas
  (\<open>ae_step_alphabet_enlarge_gamma_preserve\<close> etc.) from
  the forward direction.\<close>

lemma ae_backward_stage_load_chain:
  fixes M :: "('q, 'a) ktm"
    and c' c3 :: "('c :: enum \<Rightarrow> 'a,
                   'q \<times> ('a, 'c) ae_stage) ktc_config"
    and qM' :: 'q
    and ofs :: "nat \<Rightarrow> 'c"
    and buf :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest :: "nat \<Rightarrow> ae_dest"
  assumes vM:          "valid_ktm M"
      and c'_state:    "ktc_state c' = (qM', ofs, buf, dest, SS1)"
      and inv_ss1:     "ae_inv_ss1 M c'"
      and gamma_c':    "ae_tape_in_gamma_block M c'"
      and buf_gamma:   "ae_buffer_in_gamma_block M c'"
      and pos_link_c': "ae_position_link M c'"
      and qM'_neq_t:   "qM' \<noteq> t_ktm M"
      and qM'_neq_r:   "qM' \<noteq> r_ktm M"
      and run:         "(c', c3)
                          \<in> ktm_step (alphabet_enlarge_delta M) ^^ 3"
  obtains c1 c2 where
      "(c', c1) \<in> ktm_step (ae_delta_ss1_ss2 M)"
    and "(c', c1) \<in> ktm_step (alphabet_enlarge_delta M)"
    and "(c1, c2) \<in> ktm_step (ae_delta_ss2_ss3 M)"
    and "(c1, c2) \<in> ktm_step (alphabet_enlarge_delta M)"
    and "(c2, c3) \<in> ktm_step (ae_delta_ss3_ss4 M)"
    and "(c2, c3) \<in> ktm_step (alphabet_enlarge_delta M)"
    and "ae_inv_ss4 M c3"
    and "ae_tape_in_gamma_block M c3"
    and "ae_buffer_in_gamma_block M c3"
    and "fst (ktc_state c3) = qM'"
    and "ae_position_link M c3"
proof -
  \<comment> \<open>Peel the 3-step chain into three alphabet-enlarge steps
      through intermediates \<open>c1\<close>, \<open>c2\<close>.\<close>
  from run obtain c1 c2 where
      step1: "(c', c1) \<in> ktm_step (alphabet_enlarge_delta M)"
    and step2: "(c1, c2) \<in> ktm_step (alphabet_enlarge_delta M)"
    and step3: "(c2, c3) \<in> ktm_step (alphabet_enlarge_delta M)"
    by (auto dest!: relpow_Suc_D2 simp: numeral_3_eq_3)

  \<comment> \<open>Substep 1: SS1\<open>\<rightarrow>\<close>SS2.  Commit step1 to
      \<open>ae_delta_ss1_ss2\<close> via \<open>ktm_step_ae_delta_ss1_only\<close>,
      then propagate the per-substep invariant and side-bands.\<close>
  have c'_idx_ss1: "snd (snd (snd (snd (ktc_state c')))) = SS1"
    using c'_state by simp
  have step1_sub: "(c', c1) \<in> ktm_step (ae_delta_ss1_ss2 M)"
    by (rule ktm_step_ae_delta_ss1_only[OF step1 c'_idx_ss1])
  have inv_ss2: "ae_inv_ss2 M c1"
    using ae_step_ss1_ss2_invariant[OF vM inv_ss1 step1_sub] .
  have gamma_c1: "ae_tape_in_gamma_block M c1"
    using ae_step_alphabet_enlarge_gamma_preserve[OF gamma_c' step1] .
  have buf_gamma_c1: "ae_buffer_in_gamma_block M c1"
    using ae_step_alphabet_enlarge_buffer_gamma_preserve[OF vM buf_gamma
                                                            gamma_c' step1] .
  have c1_fst_eq: "fst (ktc_state c1) = qM'"
    using step1_sub c'_state
    by (auto simp: ae_delta_ss1_ss2_def elim: ktm_step.cases)
  have aux_45_at_c': "(c', c1) \<in> ktm_step (ae_delta_ss4_ss5 M)
                        \<Longrightarrow> ae_position_link M c1"
    using ae_pos_link_aux_void_ss4_ss5[where M = M and c_pre = c' and c_post = c1]
          c'_idx_ss1 by simp
  have aux_56_at_c': "(c', c1) \<in> ktm_step (ae_delta_ss5_ss6 M)
                        \<Longrightarrow> ae_position_link M c1"
    using ae_pos_link_aux_void_ss5_ss6[where M = M and c_pre = c' and c_post = c1]
          c'_idx_ss1 by simp
  have aux_78_at_c': "(c', c1) \<in> ktm_step (ae_delta_ss7_ss8 M)
                        \<Longrightarrow> ae_position_link M c1"
    using ae_pos_link_aux_void_ss7_ss8[where M = M and c_pre = c' and c_post = c1]
          c'_idx_ss1 by simp
  have pos_link_c1: "ae_position_link M c1"
    using ae_step_alphabet_enlarge_position_link_preserve[OF pos_link_c'
            step1 aux_45_at_c' aux_56_at_c' aux_78_at_c'] .

  \<comment> \<open>Substep 2: SS2\<open>\<rightarrow>\<close>SS3.\<close>
  have c1_idx_ss2: "snd (snd (snd (snd (ktc_state c1)))) = SS2"
    using inv_ss2 unfolding ae_inv_ss2_def by (cases "ktc_state c1") auto
  have step2_sub: "(c1, c2) \<in> ktm_step (ae_delta_ss2_ss3 M)"
    by (rule ktm_step_ae_delta_ss2_only[OF step2 c1_idx_ss2])
  have inv_ss3: "ae_inv_ss3 M c2"
    using ae_step_ss2_ss3_invariant[OF vM inv_ss2 step2_sub] .
  have gamma_c2: "ae_tape_in_gamma_block M c2"
    using ae_step_alphabet_enlarge_gamma_preserve[OF gamma_c1 step2] .
  have buf_gamma_c2: "ae_buffer_in_gamma_block M c2"
    using ae_step_alphabet_enlarge_buffer_gamma_preserve[OF vM buf_gamma_c1
                                                            gamma_c1 step2] .
  have c2_fst_eq: "fst (ktc_state c2) = qM'"
    using step2_sub c1_fst_eq
    by (cases "ktc_state c1")
       (auto simp: ae_delta_ss2_ss3_def elim: ktm_step.cases)
  have aux_45_at_c1: "(c1, c2) \<in> ktm_step (ae_delta_ss4_ss5 M)
                        \<Longrightarrow> ae_position_link M c2"
    using ae_pos_link_aux_void_ss4_ss5[where M = M and c_pre = c1 and c_post = c2]
          c1_idx_ss2 by simp
  have aux_56_at_c1: "(c1, c2) \<in> ktm_step (ae_delta_ss5_ss6 M)
                        \<Longrightarrow> ae_position_link M c2"
    using ae_pos_link_aux_void_ss5_ss6[where M = M and c_pre = c1 and c_post = c2]
          c1_idx_ss2 by simp
  have aux_78_at_c1: "(c1, c2) \<in> ktm_step (ae_delta_ss7_ss8 M)
                        \<Longrightarrow> ae_position_link M c2"
    using ae_pos_link_aux_void_ss7_ss8[where M = M and c_pre = c1 and c_post = c2]
          c1_idx_ss2 by simp
  have pos_link_c2: "ae_position_link M c2"
    using ae_step_alphabet_enlarge_position_link_preserve[OF pos_link_c1
            step2 aux_45_at_c1 aux_56_at_c1 aux_78_at_c1] .

  \<comment> \<open>Substep 3: SS3\<open>\<rightarrow>\<close>SS4.\<close>
  have c2_idx_ss3: "snd (snd (snd (snd (ktc_state c2)))) = SS3"
    using inv_ss3 unfolding ae_inv_ss3_def by (cases "ktc_state c2") auto
  have step3_sub: "(c2, c3) \<in> ktm_step (ae_delta_ss3_ss4 M)"
    by (rule ktm_step_ae_delta_ss3_only[OF step3 c2_idx_ss3])
  have inv_ss4: "ae_inv_ss4 M c3"
    using ae_step_ss3_ss4_invariant[OF vM inv_ss3 step3_sub] .
  have gamma_c3: "ae_tape_in_gamma_block M c3"
    using ae_step_alphabet_enlarge_gamma_preserve[OF gamma_c2 step3] .
  have buf_gamma_c3: "ae_buffer_in_gamma_block M c3"
    using ae_step_alphabet_enlarge_buffer_gamma_preserve[OF vM buf_gamma_c2
                                                            gamma_c2 step3] .
  have c3_fst_eq: "fst (ktc_state c3) = qM'"
    using step3_sub c2_fst_eq
    by (cases "ktc_state c2")
       (auto simp: ae_delta_ss3_ss4_def elim: ktm_step.cases)
  have aux_45_at_c2: "(c2, c3) \<in> ktm_step (ae_delta_ss4_ss5 M)
                        \<Longrightarrow> ae_position_link M c3"
    using ae_pos_link_aux_void_ss4_ss5[where M = M and c_pre = c2 and c_post = c3]
          c2_idx_ss3 by simp
  have aux_56_at_c2: "(c2, c3) \<in> ktm_step (ae_delta_ss5_ss6 M)
                        \<Longrightarrow> ae_position_link M c3"
    using ae_pos_link_aux_void_ss5_ss6[where M = M and c_pre = c2 and c_post = c3]
          c2_idx_ss3 by simp
  have aux_78_at_c2: "(c2, c3) \<in> ktm_step (ae_delta_ss7_ss8 M)
                        \<Longrightarrow> ae_position_link M c3"
    using ae_pos_link_aux_void_ss7_ss8[where M = M and c_pre = c2 and c_post = c3]
          c2_idx_ss3 by simp
  have pos_link_c3: "ae_position_link M c3"
    using ae_step_alphabet_enlarge_position_link_preserve[OF pos_link_c2
            step3 aux_45_at_c2 aux_56_at_c2 aux_78_at_c2] .

  show ?thesis
    by (rule that[OF step1_sub step1 step2_sub step2 step3_sub step3
                     inv_ss4 gamma_c3 buf_gamma_c3 c3_fst_eq pos_link_c3])
qed


text \<open>\<^emph>\<open>Reverse-direction SS4\<open>\<rightarrow>\<close>SS5 compute extract.\<close>
  Counterpart of the forward direction's SS4\<open>\<rightarrow>\<close>SS5 step
  construction.  Given the load-chain output (the three buffer-load
  steps c'\<open>\<rightarrow>\<close>c3 plus standard SS1-boundary invariants)
  and a substrate step \<open>(c3, c4) \<in> ktm_step
  (alphabet_enlarge_delta M)\<close> issuing from c3 at SS4, this
  lemma produces:

  \<^enum> Step commitment: \<open>(c3, c4)\<close> lies in
    \<open>ae_delta_ss4_ss5\<close> (via
    \<open>ktm_step_ae_delta_ss4_only\<close>).

  \<^enum> Lifted \<open>cM\<close> trace: \<open>(cM, cM_new) \<in> ktm_step
    (delta_ktm M) ^^ n\<close> for some \<open>n \<le> |c|\<close>, with halt-or-full
    termination — produced by \<open>m_steps_buffered_lift_to_tape\<close>
    (Step 2b-wrapper) from the \<open>m_steps_buffered\<close> chain
    exposed by \<open>ae_step_ss4_ss5_destruct_to_buffered\<close>.

  \<^enum> Threaded invariants at \<open>cM_new\<close>/\<open>c4\<close>: window
    invariant carrying through, regime-aware no-LE, and the
    \<open>fst (buf' k) \<noteq> LE_block\<close> guard for pos=0 tapes.

  Composes the direction-agnostic helpers from the forward direction
  (\<open>ae_home_classification\<close>,
  \<open>ae_ss1_to_ss4_buffer_chars_general\<close>,
  \<open>ae_ss4_window_from_correspondence_general\<close>) with the
  reverse-direction helpers
  (\<open>ktm_step_ae_delta_ss4_only\<close>,
  \<open>ae_step_ss4_ss5_destruct_to_buffered\<close>) and Step
  2b-wrapper.  Consumer: \<open>ae_backward_stage\<close>'s body.\<close>

lemma ae_backward_stage_compute_extract:
  fixes M :: "('q, 'a) ktm"
    and cM :: "('a, 'q) ktc_config"
    and c' c1 c2 c3 c4 :: "('c :: enum \<Rightarrow> 'a,
                              'q \<times> ('a, 'c) ae_stage) ktc_config"
    and qM' :: 'q
    and ofs :: "nat \<Rightarrow> 'c"
    and buf :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest :: "nat \<Rightarrow> ae_dest"
  assumes vM:          "valid_ktm M"
      and lu:          "le_unique M"
      and cM_valid:    "valid_config_ktm M cM"
      and sim:         "ae_simulates M cM c'"
      and c'_state:    "ktc_state c' = (qM', ofs, buf, dest, SS1)"
      and le_anchor:   "\<forall>k<k_ktm M. ktc_tape c' k 0 = LE_block (le_ktm M)"
      and le_neq_bl:   "le_ktm M \<noteq> bl_ktm M"
      and no_le_per_tape:
            "\<forall>k. (ktc_pos c' k \<ge> 2
                    \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                              \<longrightarrow> ktc_tape cM k
                                    ((ktc_pos c' k - 2) * card (UNIV :: 'c set)
                                       + 1 + i)
                                  \<noteq> le_ktm M))
                 \<and> (ktc_pos c' k = 1
                      \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                                \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))
                 \<and> (ktc_pos c' k = 0
                      \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                                \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))"
      and step1_sub:   "(c', c1) \<in> ktm_step (ae_delta_ss1_ss2 M)"
      and step2_sub:   "(c1, c2) \<in> ktm_step (ae_delta_ss2_ss3 M)"
      and step3_sub:   "(c2, c3) \<in> ktm_step (ae_delta_ss3_ss4 M)"
      and step4_full:  "(c3, c4) \<in> ktm_step (alphabet_enlarge_delta M)"
      and c3_idx_ss4:  "snd (snd (snd (snd (ktc_state c3)))) = SS4"
  obtains cM_new buf' end_pos n where
      "(c3, c4) \<in> ktm_step (ae_delta_ss4_ss5 M)"
    and "(cM, cM_new) \<in> ktm_step (delta_ktm M) ^^ n"
    and "n \<le> card (UNIV :: 'c set)"
    and "n = card (UNIV :: 'c set)
            \<or> ktc_state cM_new \<in> {t_ktm M, r_ktm M}"
    and "ktc_state c4 = (ktc_state cM_new,
                          \<lambda>k. if k < k_ktm M then snd (end_pos k)
                                else init_offset k,
                          buf',
                          \<lambda>k. if k < k_ktm M then fst (end_pos k)
                                else init_dest k, SS5)"
    and "ktc_tape c4 = ktc_tape c'"
    and "\<forall>k<k_ktm M. ae_window_invariant_general
                (ktc_tape cM_new k) (ktc_pos cM_new k)
                (end_pos k) (buf' k) (ktc_pos c' k) (le_ktm M)"
    and "\<forall>k. (ktc_pos c' k = 0
                  \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                            \<longrightarrow> ktc_tape cM_new k (Suc i) \<noteq> le_ktm M))
              \<and> (ktc_pos c' k = 1
                  \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                            \<longrightarrow> ktc_tape cM_new k (Suc i) \<noteq> le_ktm M))
              \<and> (ktc_pos c' k \<ge> 2
                  \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                            \<longrightarrow> ktc_tape cM_new k
                                  ((ktc_pos c' k - 2) * card (UNIV :: 'c set)
                                     + 1 + i)
                                \<noteq> le_ktm M))"
    and "\<forall>k<k_ktm M. ktc_pos c' k = 0
                \<longrightarrow> fst (buf' k) \<noteq> LE_block (le_ktm M)"
proof -
  \<comment> \<open>Commit step4 to \<open>ae_delta_ss4_ss5\<close> via the
      cross-phase exclusion lift.\<close>
  have step4_sub: "(c3, c4) \<in> ktm_step (ae_delta_ss4_ss5 M)"
    by (rule ktm_step_ae_delta_ss4_only[OF step4_full c3_idx_ss4])

  \<comment> \<open>Extract tape correspondence from the simulation invariant.\<close>
  have tape_corr: "\<forall>k<k_ktm M. ae_tape_correspondence (le_ktm M)
                          (ktc_tape cM k) (ktc_tape c' k)"
    using sim c'_state unfolding ae_simulates_def by auto

  \<comment> \<open>Home-cell LE classification.\<close>
  have home_classification:
      "\<forall>k<k_ktm M. (ktc_pos c' k = 0
              \<longrightarrow> ktc_tape c' k (ktc_pos c' k) = LE_block (le_ktm M))
           \<and> (ktc_pos c' k \<ge> 1
              \<longrightarrow> ktc_tape c' k (ktc_pos c' k) \<noteq> LE_block (le_ktm M))"
    by (rule ae_home_classification[OF le_anchor no_le_per_tape tape_corr])

  \<comment> \<open>SS4-entry buffer / tape / position characterisation
      (direction-agnostic, shared with forward direction).\<close>
  have c3_state:
      "ktc_state c3 = (qM', ofs,
                       (\<lambda>k. if k < k_ktm M
                              then (if ktc_pos c' k = 0
                                     then (bl_block (bl_ktm M),
                                           LE_block (le_ktm M),
                                           snd (snd (buf k)))
                                     else (ktc_tape c' k (ktc_pos c' k - 1),
                                           ktc_tape c' k (ktc_pos c' k),
                                           snd (snd (buf k))))
                              else init_buffer (le_ktm M) k),
                       dest, SS4)"
    using ae_ss1_to_ss4_buffer_chars_general(1)[OF c'_state step1_sub
                                                   step2_sub step3_sub
                                                   home_classification] .
  have c3_tape: "ktc_tape c3 = ktc_tape c'"
    using ae_ss1_to_ss4_buffer_chars_general(2)[OF c'_state step1_sub
                                                   step2_sub step3_sub
                                                   home_classification] .
  have c3_pos: "\<And>k. k < k_ktm M \<Longrightarrow> ktc_pos c3 k = ktc_pos c' k + 1"
    using ae_ss1_to_ss4_buffer_chars_general(3)[OF c'_state step1_sub
                                                   step2_sub step3_sub
                                                   home_classification] .

  \<comment> \<open>Per-tape SS4 window invariant at \<open>cM\<close> via the unified
      from-correspondence helper.\<close>
  have window_at_cM:
      "\<forall>k<k_ktm M. ae_window_invariant_general
              (ktc_tape cM k) (ktc_pos cM k)
              (AE_Home, ofs k)
              (if ktc_pos c' k = 0
                 then (bl_block (bl_ktm M),
                       LE_block (le_ktm M),
                       ktc_tape c' k 1)
               else if ktc_pos c' k = 1
                 then (ktc_tape c' k 0,
                       ktc_tape c' k 1,
                       ktc_tape c' k 2)
               else (ktc_tape c' k (ktc_pos c' k - 1),
                     ktc_tape c' k (ktc_pos c' k),
                     ktc_tape c' k (ktc_pos c' k + 1)))
              (ktc_pos c' k)
              (le_ktm M)"
    using ae_ss4_window_from_correspondence_general[OF sim c'_state
                                                       le_anchor
                                                       no_le_per_tape] .

  \<comment> \<open>Destructure the SS4\<open>\<rightarrow>\<close>SS5 step into its
      \<open>m_steps_buffered\<close> chain.  Bind every obtained variable
      and every shows-conjunct, then discharge by direct
      rule-application to avoid \<open>blast\<close> divergence on the
      large \<open>obtains\<close>.\<close>
  obtain qD ofsD bufD destD tsD nD q_out buf' bufC end_pos where
      c3_eq: "c3 = KConfig (qD, ofsD, bufD, destD, SS4) tsD nD"
    and c4_state_raw:
        "ktc_state c4 = (q_out,
                        \<lambda>k. if k < k_ktm M then snd (end_pos k)
                              else init_offset k,
                        buf',
                        \<lambda>k. if k < k_ktm M then fst (end_pos k)
                              else init_dest k, SS5)"
    and buf'_def: "buf' = (\<lambda>k. if k < k_ktm M then bufC k
                                 else init_buffer (le_ktm M) k)"
    and c4_tape_raw: "ktc_tape c4 = tsD"
    and c4_pos_raw:
        "ktc_pos c4
           = (\<lambda>k. go_move (if k < k_ktm M
                            then (if tsD k (nD k) = LE_block (le_ktm M)
                                    then MoveN else MoveL)
                            else MoveN)
                         (nD k))"
    and qD_in: "qD \<in> Q_ktm M"
    and qD_neq_t: "qD \<noteq> t_ktm M"
    and qD_neq_r: "qD \<noteq> r_ktm M"
    and tsD_supp: "\<forall>j\<ge>k_ktm M. tsD j (nD j) = bl_block (bl_ktm M)"
    and m_steps:
        "((qD, \<lambda>k. (fst (bufD k),
                     if k < k_ktm M then fst (snd (bufD k)) else tsD k (nD k),
                     tsD k (nD k)),
            \<lambda>k. (AE_Home, ofsD k)),
           (q_out, bufC, end_pos)) \<in> m_steps_buffered M"
    by (rule ae_step_ss4_ss5_destruct_to_buffered[OF step4_sub])

  \<comment> \<open>Identify destructed names with our load-chain view.\<close>
  have qD_eq: "qD = qM'"
    using c3_eq c3_state by simp
  have ofsD_eq: "ofsD = ofs"
    using c3_eq c3_state by simp
  have bufD_eq:
      "bufD = (\<lambda>k. if k < k_ktm M
                     then (if ktc_pos c' k = 0
                            then (bl_block (bl_ktm M),
                                  LE_block (le_ktm M),
                                  snd (snd (buf k)))
                            else (ktc_tape c' k (ktc_pos c' k - 1),
                                  ktc_tape c' k (ktc_pos c' k),
                                  snd (snd (buf k))))
                     else init_buffer (le_ktm M) k)"
    using c3_eq c3_state by simp
  have tsD_eq: "tsD = ktc_tape c'"
    using c3_eq c3_tape by simp
  have nD_eq: "\<And>k. k < k_ktm M \<Longrightarrow> nD k = ktc_pos c' k + 1"
    using c3_eq c3_pos by simp

  \<comment> \<open>The destruct's \<open>m_steps\<close> source is the guarded
      \<open>buf_full\<close> home block; name it \<open>buf_full_src\<close> so the
      Step 2b-wrapper unification is first-order.  On active tapes
      (\<open>k < k_ktm M\<close>) it collapses to the window helper's
      regime-aware buffer shape; padding tapes carry the frozen
      empty-tape shadow and never enter the wrapper's
      \<open>\<forall>k<k_ktm M\<close> obligations.\<close>
  define buf_full_src ::
      "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    where "buf_full_src =
             (\<lambda>k. (fst (bufD k),
                   if k < k_ktm M then fst (snd (bufD k)) else tsD k (nD k),
                   tsD k (nD k)))"

  \<comment> \<open>Active-tape alignment: for \<open>k < k_ktm M\<close> the guarded
      source coincides with the window helper's regime shape.\<close>
  have src_align:
      "\<forall>k<k_ktm M. buf_full_src k
              = (if ktc_pos c' k = 0
                   then (bl_block (bl_ktm M), LE_block (le_ktm M),
                         ktc_tape c' k 1)
                 else if ktc_pos c' k = 1
                   then (ktc_tape c' k 0, ktc_tape c' k 1, ktc_tape c' k 2)
                 else (ktc_tape c' k (ktc_pos c' k - 1),
                       ktc_tape c' k (ktc_pos c' k),
                       ktc_tape c' k (ktc_pos c' k + 1)))"
  proof (intro allI impI)
    fix k assume klt: "k < k_ktm M"
    have bufD_k: "bufD k
                    = (if ktc_pos c' k = 0
                         then (bl_block (bl_ktm M), LE_block (le_ktm M),
                               snd (snd (buf k)))
                         else (ktc_tape c' k (ktc_pos c' k - 1),
                               ktc_tape c' k (ktc_pos c' k),
                               snd (snd (buf k))))"
      using bufD_eq klt by simp
    have tsD_k: "tsD k (nD k) = ktc_tape c' k (ktc_pos c' k + 1)"
      using tsD_eq nD_eq[OF klt] by simp
    have src_k: "buf_full_src k
                   = (fst (bufD k), fst (snd (bufD k)), tsD k (nD k))"
      using klt unfolding buf_full_src_def by simp
    show "buf_full_src k
            = (if ktc_pos c' k = 0
                 then (bl_block (bl_ktm M), LE_block (le_ktm M),
                       ktc_tape c' k 1)
               else if ktc_pos c' k = 1
                 then (ktc_tape c' k 0, ktc_tape c' k 1, ktc_tape c' k 2)
               else (ktc_tape c' k (ktc_pos c' k - 1),
                     ktc_tape c' k (ktc_pos c' k),
                     ktc_tape c' k (ktc_pos c' k + 1)))"
    proof (cases "ktc_pos c' k")
      case 0
      thus ?thesis using src_k bufD_k tsD_k by simp
    next
      case (Suc m)
      show ?thesis
      proof (cases m)
        case 0
        with Suc src_k bufD_k tsD_k show ?thesis
          by (simp add: eval_nat_numeral)
      next
        case (Suc mm)
        with \<open>ktc_pos c' k = Suc m\<close> src_k bufD_k tsD_k show ?thesis by simp
      qed
    qed
  qed

  \<comment> \<open>State alignment for \<open>cM\<close>: simulation gives
      \<open>ktc_state cM = qM'\<close>, and destruct gives \<open>qD = qM'\<close>.\<close>
  have st_eq_cM: "ktc_state cM = qD"
    using sim c'_state qD_eq unfolding ae_simulates_def by auto

  \<comment> \<open>\<open>m_steps\<close> chain in the form expected by the
      Step 2b-wrapper, with the guarded source named and \<open>ofs\<close>
      substituted for \<open>ofsD\<close>.\<close>
  have m_steps_src:
      "((qD, buf_full_src, \<lambda>k. (AE_Home, ofs k)),
          (q_out, bufC, end_pos)) \<in> m_steps_buffered M"
    using m_steps ofsD_eq unfolding buf_full_src_def by simp

  \<comment> \<open>Window invariant at \<open>cM\<close> for the guarded source, on
      active tapes, via the regime alignment.\<close>
  have window_at_cM_src:
      "\<forall>k<k_ktm M. ae_window_invariant_general
              (ktc_tape cM k) (ktc_pos cM k)
              (AE_Home, ofs k) (buf_full_src k) (ktc_pos c' k) (le_ktm M)"
  proof (intro allI impI)
    fix k assume klt: "k < k_ktm M"
    show "ae_window_invariant_general (ktc_tape cM k) (ktc_pos cM k)
            (AE_Home, ofs k) (buf_full_src k) (ktc_pos c' k) (le_ktm M)"
      using window_at_cM[rule_format, OF klt] src_align[rule_format, OF klt]
      by simp
  qed

  \<comment> \<open>Invoke Step 2b-wrapper.  The window invariant at \<open>cM\<close>
      and the regime-keyed \<open>no_le\<close> match the wrapper's
      hypotheses by construction.  Left-not-LE for pos=0 tapes
      is the \<open>bl_block \<noteq> LE_block\<close> argument.\<close>
  have bl_neq_le:
      "(bl_block (bl_ktm M) :: 'c \<Rightarrow> 'a) \<noteq> LE_block (le_ktm M)"
  proof
    assume eq: "(bl_block (bl_ktm M) :: 'c \<Rightarrow> 'a) = LE_block (le_ktm M)"
    have "bl_block (bl_ktm M) (SOME x :: 'c. True)
            = LE_block (le_ktm M) (SOME x :: 'c. True)"
      using eq by simp
    hence "bl_ktm M = le_ktm M"
      unfolding bl_block_def LE_block_def by simp
    with le_neq_bl show False by simp
  qed
  have left_not_le_pos0_buf_full:
      "\<forall>k<k_ktm M. ktc_pos c' k = 0
              \<longrightarrow> fst (buf_full_src k) \<noteq> LE_block (le_ktm M)"
  proof (intro allI impI impI)
    fix k assume klt: "k < k_ktm M" and pos0: "ktc_pos c' k = 0"
    have "buf_full_src k
            = (bl_block (bl_ktm M), LE_block (le_ktm M), ktc_tape c' k 1)"
      using src_align[rule_format, OF klt] pos0 by simp
    thus "fst (buf_full_src k) \<noteq> LE_block (le_ktm M)"
      using bl_neq_le by simp
  qed

  \<comment> \<open>Reorder the regime conjunction so it matches the
      Step 2b-wrapper's hypothesis shape (pos=0, pos=1, pos\<open>\<ge>\<close>2).
      The outer \<open>no_le_per_tape\<close> uses the opposite order
      (pos\<open>\<ge>\<close>2, pos=1, pos=0) inherited from the forward-direction
      assumption convention.\<close>
  have no_le_per_tape_reordered:
      "\<forall>k. (ktc_pos c' k = 0
              \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                        \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))
           \<and> (ktc_pos c' k = 1
                \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                          \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))
           \<and> (ktc_pos c' k \<ge> 2
                \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                          \<longrightarrow> ktc_tape cM k
                                ((ktc_pos c' k - 2) * card (UNIV :: 'c set)
                                   + 1 + i)
                              \<noteq> le_ktm M))"
    using no_le_per_tape by blast

  obtain cM_new n where
      cM_trace_n: "(cM, cM_new) \<in> ktm_step (delta_ktm M) ^^ n"
    and n_bnd: "n \<le> card (UNIV :: 'c set)"
    and halt_or_full:
        "n = card (UNIV :: 'c set)
            \<or> ktc_state cM_new \<in> {t_ktm M, r_ktm M}"
    and cM_new_st: "ktc_state cM_new = q_out"
    and new_window_C:
        "\<forall>k<k_ktm M. ae_window_invariant_general
                (ktc_tape cM_new k) (ktc_pos cM_new k)
                (end_pos k) (bufC k) (ktc_pos c' k) (le_ktm M)"
    and new_no_le:
        "\<forall>k. (ktc_pos c' k = 0
                  \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                            \<longrightarrow> ktc_tape cM_new k (Suc i) \<noteq> le_ktm M))
              \<and> (ktc_pos c' k = 1
                  \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                            \<longrightarrow> ktc_tape cM_new k (Suc i) \<noteq> le_ktm M))
              \<and> (ktc_pos c' k \<ge> 2
                  \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                            \<longrightarrow> ktc_tape cM_new k
                                  ((ktc_pos c' k - 2) * card (UNIV :: 'c set)
                                     + 1 + i)
                                \<noteq> le_ktm M))"
    and new_left_C:
        "\<forall>k<k_ktm M. ktc_pos c' k = 0
                \<longrightarrow> fst (bufC k) \<noteq> LE_block (le_ktm M)"
    by (rule m_steps_buffered_lift_to_tape
          [OF vM lu cM_valid qD_in m_steps_src st_eq_cM window_at_cM_src
              no_le_per_tape_reordered left_not_le_pos0_buf_full])
  \<comment> \<open>The SS5 buffer \<open>buf'\<close> agrees with the chain target
      \<open>bufC\<close> on active tapes; transport the per-active-tape
      window and left-not-LE facts.\<close>
  have buf'_active: "\<forall>k<k_ktm M. buf' k = bufC k"
    using buf'_def by simp
  have new_window:
      "\<forall>k<k_ktm M. ae_window_invariant_general
              (ktc_tape cM_new k) (ktc_pos cM_new k)
              (end_pos k) (buf' k) (ktc_pos c' k) (le_ktm M)"
    using new_window_C buf'_active by simp
  have new_left_not_le_pos0:
      "\<forall>k<k_ktm M. ktc_pos c' k = 0
              \<longrightarrow> fst (buf' k) \<noteq> LE_block (le_ktm M)"
    using new_left_C buf'_active by simp

  \<comment> \<open>Tape preservation through SS4\<open>\<rightarrow>\<close>SS5: the substep
      writes the same letter it reads (\<open>a' = a\<close>), so
      \<open>ktc_tape c4 = ktc_tape c3 = ktc_tape c'\<close>.\<close>
  have c4_tape: "ktc_tape c4 = ktc_tape c'"
    using c4_tape_raw tsD_eq by simp

  \<comment> \<open>Rewrite \<open>c4_state_raw\<close> to use \<open>ktc_state cM_new\<close>;
      offset / dest fields are guarded (frozen at \<open>init_*\<close> beyond
      the tape count), mirroring the SS4\<open>\<rightarrow>\<close>SS5 \<open>\<delta>\<close>.\<close>
  have c4_state:
      "ktc_state c4 = (ktc_state cM_new,
                       \<lambda>k. if k < k_ktm M then snd (end_pos k)
                             else init_offset k,
                       buf',
                       \<lambda>k. if k < k_ktm M then fst (end_pos k)
                             else init_dest k, SS5)"
    using c4_state_raw cM_new_st by simp

  show thesis
  proof (rule that[where cM_new = cM_new and buf' = buf'
                     and end_pos = end_pos and n = n])
    show "(c3, c4) \<in> ktm_step (ae_delta_ss4_ss5 M)" by (rule step4_sub)
    show "(cM, cM_new) \<in> ktm_step (delta_ktm M) ^^ n"
      by (rule cM_trace_n)
    show "n \<le> card (UNIV :: 'c set)" by (rule n_bnd)
    show "n = card (UNIV :: 'c set)
            \<or> ktc_state cM_new \<in> {t_ktm M, r_ktm M}"
      by (rule halt_or_full)
    show "ktc_state c4 = (ktc_state cM_new,
                          \<lambda>k. if k < k_ktm M then snd (end_pos k)
                                else init_offset k,
                          buf',
                          \<lambda>k. if k < k_ktm M then fst (end_pos k)
                                else init_dest k, SS5)"
      by (rule c4_state)
    show "ktc_tape c4 = ktc_tape c'" by (rule c4_tape)
    show "\<forall>k<k_ktm M. ae_window_invariant_general
                (ktc_tape cM_new k) (ktc_pos cM_new k)
                (end_pos k) (buf' k) (ktc_pos c' k) (le_ktm M)"
      by (rule new_window)
    show "\<forall>k. (ktc_pos c' k = 0
                  \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                            \<longrightarrow> ktc_tape cM_new k (Suc i) \<noteq> le_ktm M))
              \<and> (ktc_pos c' k = 1
                  \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                            \<longrightarrow> ktc_tape cM_new k (Suc i) \<noteq> le_ktm M))
              \<and> (ktc_pos c' k \<ge> 2
                  \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                            \<longrightarrow> ktc_tape cM_new k
                                  ((ktc_pos c' k - 2) * card (UNIV :: 'c set)
                                     + 1 + i)
                                \<noteq> le_ktm M))"
      by (rule new_no_le)
    show "\<forall>k<k_ktm M. ktc_pos c' k = 0
                \<longrightarrow> fst (buf' k) \<noteq> LE_block (le_ktm M)"
      by (rule new_left_not_le_pos0)
  qed
qed


text \<open>\<^emph>\<open>Reverse-direction SS5\<open>\<rightarrow>\<close>SS1 writeback chain peel.\<close>
  Mirror of \<open>ae_backward_stage_load_chain\<close> for the four
  write-back substeps (SS5\<open>\<rightarrow>\<close>SS6,
  SS6\<open>\<rightarrow>\<close>SS7, SS7\<open>\<rightarrow>\<close>SS8,
  SS8\<open>\<rightarrow>\<close>SS1).

  Given an SS5-boundary config \<open>c4\<close> with the standard SS5
  invariants and a 4-step \<open>alphabet_enlarge_delta\<close> chain
  to \<open>c''\<close>, identifies each substep via the lemmas
  \<open>ktm_step_ae_delta_ssN_only\<close>, propagates the per-substep
  invariants \<open>ae_inv_ss\<close> through the chain, carries
  \<open>ae_tape_in_gamma_block\<close> and
  \<open>ae_buffer_in_gamma_block\<close> via the direction-agnostic
  preserve lemmas, and exposes the halt-aware c'' status:

  \<^item> non-halt branch (\<open>q_out \<notin> {t_ktm M, r_ktm M}\<close>):
    \<open>c''\<close> lands at SS1 with the same q-component as c4 (preserved
    through all 4 substeps).

  \<^item> halt branch (\<open>q_out \<in> {t_ktm M, r_ktm M}\<close>):
    \<open>c''\<close> lands at VFwd with halted q-component and
    \<open>init_stage le\<close>.

  Position-link propagation through writeback substeps is NOT
  performed here — it requires the regime-aware buffer non-LE
  analysis that's better packaged with the final
  \<open>ae_simulates\<close> assembly in the top-level wrapper below.\<close>

lemma ae_backward_stage_writeback_chain:
  fixes M :: "('q, 'a) ktm"
    and c4 c'' :: "('c :: enum \<Rightarrow> 'a,
                     'q \<times> ('a, 'c) ae_stage) ktc_config"
    and q_out :: 'q
  assumes vM:           "valid_ktm M"
      and c4_inv:       "ae_inv_ss5 M c4"
      and c4_q:         "fst (ktc_state c4) = q_out"
      and q_out_in_Q:   "q_out \<in> Q_ktm M"
      and gamma_c4:     "ae_tape_in_gamma_block M c4"
      and buf_gamma_c4: "ae_buffer_in_gamma_block M c4"
      and run:          "(c4, c'')
                           \<in> ktm_step (alphabet_enlarge_delta M) ^^ 4"
  obtains c5 c6 c7 where
      "(c4, c5) \<in> ktm_step (ae_delta_ss5_ss6 M)"
    and "(c4, c5) \<in> ktm_step (alphabet_enlarge_delta M)"
    and "(c5, c6) \<in> ktm_step (ae_delta_ss6_ss7 M)"
    and "(c5, c6) \<in> ktm_step (alphabet_enlarge_delta M)"
    and "(c6, c7) \<in> ktm_step (ae_delta_ss7_ss8 M)"
    and "(c6, c7) \<in> ktm_step (alphabet_enlarge_delta M)"
    and "(c7, c'') \<in> ktm_step (ae_delta_ss8_ss1 M)"
    and "(c7, c'') \<in> ktm_step (alphabet_enlarge_delta M)"
    and "q_out \<notin> {t_ktm M, r_ktm M} \<longrightarrow> ae_inv_ss1 M c''"
    and "q_out \<in> {t_ktm M, r_ktm M}
            \<longrightarrow> (case ktc_state c'' of (qH, _, _, _, idx)
                  \<Rightarrow> qH \<in> {t_ktm M, r_ktm M} \<and> idx = VFwd)"
    and "fst (ktc_state c'') = q_out"
    and "ae_tape_in_gamma_block M c''"
    and "ae_buffer_in_gamma_block M c''"
proof -
  \<comment> \<open>Peel the 4-step chain into four alphabet-enlarge steps
      through intermediates \<open>c5\<close>, \<open>c6\<close>, \<open>c7\<close>.\<close>
  from run obtain c5 c6 c7 where
      step5: "(c4, c5) \<in> ktm_step (alphabet_enlarge_delta M)"
    and step6: "(c5, c6) \<in> ktm_step (alphabet_enlarge_delta M)"
    and step7: "(c6, c7) \<in> ktm_step (alphabet_enlarge_delta M)"
    and step8: "(c7, c'') \<in> ktm_step (alphabet_enlarge_delta M)"
    by (auto dest!: relpow_Suc_D2 simp: numeral_eq_Suc)

  \<comment> \<open>Substep 5: SS5\<open>\<rightarrow>\<close>SS6.\<close>
  have c4_idx_ss5: "snd (snd (snd (snd (ktc_state c4)))) = SS5"
    using c4_inv unfolding ae_inv_ss5_def by (cases "ktc_state c4") auto
  have step5_sub: "(c4, c5) \<in> ktm_step (ae_delta_ss5_ss6 M)"
    by (rule ktm_step_ae_delta_ss5_only[OF step5 c4_idx_ss5])
  have inv_ss6: "ae_inv_ss6 M c5"
    using ae_step_ss5_ss6_invariant[OF vM c4_inv step5_sub] .
  have gamma_c5: "ae_tape_in_gamma_block M c5"
    using ae_step_alphabet_enlarge_gamma_preserve[OF gamma_c4 step5] .
  have buf_gamma_c5: "ae_buffer_in_gamma_block M c5"
    using ae_step_alphabet_enlarge_buffer_gamma_preserve[OF vM buf_gamma_c4
                                                            gamma_c4 step5] .
  have c5_fst_eq: "fst (ktc_state c5) = q_out"
    using step5_sub c4_q
    by (cases "ktc_state c4")
       (auto simp: ae_delta_ss5_ss6_def elim: ktm_step.cases)

  \<comment> \<open>Substep 6: SS6\<open>\<rightarrow>\<close>SS7.\<close>
  have c5_idx_ss6: "snd (snd (snd (snd (ktc_state c5)))) = SS6"
    using inv_ss6 unfolding ae_inv_ss6_def
    by (cases "ktc_state c5") auto
  have step6_sub: "(c5, c6) \<in> ktm_step (ae_delta_ss6_ss7 M)"
    by (rule ktm_step_ae_delta_ss6_only[OF step6 c5_idx_ss6])
  have inv_ss7: "ae_inv_ss7 M c6"
    using ae_step_ss6_ss7_invariant[OF vM inv_ss6 step6_sub] .
  have gamma_c6: "ae_tape_in_gamma_block M c6"
    using ae_step_alphabet_enlarge_gamma_preserve[OF gamma_c5 step6] .
  have buf_gamma_c6: "ae_buffer_in_gamma_block M c6"
    using ae_step_alphabet_enlarge_buffer_gamma_preserve[OF vM buf_gamma_c5
                                                            gamma_c5 step6] .
  have c6_fst_eq: "fst (ktc_state c6) = q_out"
    using step6_sub c5_fst_eq
    by (cases "ktc_state c5")
       (auto simp: ae_delta_ss6_ss7_def elim: ktm_step.cases)

  \<comment> \<open>Substep 7: SS7\<open>\<rightarrow>\<close>SS8.\<close>
  have c6_idx_ss7: "snd (snd (snd (snd (ktc_state c6)))) = SS7"
    using inv_ss7 unfolding ae_inv_ss7_def
    by (cases "ktc_state c6") auto
  have step7_sub: "(c6, c7) \<in> ktm_step (ae_delta_ss7_ss8 M)"
    by (rule ktm_step_ae_delta_ss7_only[OF step7 c6_idx_ss7])
  have inv_ss8: "ae_inv_ss8 M c7"
    using ae_step_ss7_ss8_invariant[OF vM inv_ss7 step7_sub] .
  have gamma_c7: "ae_tape_in_gamma_block M c7"
    using ae_step_alphabet_enlarge_gamma_preserve[OF gamma_c6 step7] .
  have buf_gamma_c7: "ae_buffer_in_gamma_block M c7"
    using ae_step_alphabet_enlarge_buffer_gamma_preserve[OF vM buf_gamma_c6
                                                            gamma_c6 step7] .
  have c7_fst_eq: "fst (ktc_state c7) = q_out"
    using step7_sub c6_fst_eq
    by (cases "ktc_state c6")
       (auto simp: ae_delta_ss7_ss8_def elim: ktm_step.cases)

  \<comment> \<open>Substep 8: SS8\<open>\<rightarrow>\<close>SS1 with halt-aware routing.
      The substep relation pins the q-component; the post-state
      \<open>stage'\<close> is \<open>init_stage le\<close> in the halt branch
      and \<open>(ofs, buf, init_dest, SS1)\<close> in the non-halt
      branch.\<close>
  have c7_idx_ss8: "snd (snd (snd (snd (ktc_state c7)))) = SS8"
    using inv_ss8 unfolding ae_inv_ss8_def
    by (cases "ktc_state c7") auto
  have step8_sub: "(c7, c'') \<in> ktm_step (ae_delta_ss8_ss1 M)"
    by (rule ktm_step_ae_delta_ss8_only[OF step8 c7_idx_ss8])
  have c''_fst_eq: "fst (ktc_state c'') = q_out"
    using step8_sub c7_fst_eq
    by (cases "ktc_state c7")
       (auto simp: ae_delta_ss8_ss1_def elim: ktm_step.cases)
  have gamma_c'': "ae_tape_in_gamma_block M c''"
    using ae_step_alphabet_enlarge_gamma_preserve[OF gamma_c7 step8] .
  have buf_gamma_c'': "ae_buffer_in_gamma_block M c''"
    using ae_step_alphabet_enlarge_buffer_gamma_preserve[OF vM buf_gamma_c7
                                                            gamma_c7 step8] .

  \<comment> \<open>Halt-aware c'' invariant.  In the non-halt branch,
      \<open>ae_step_ss8_ss1_invariant\<close> gives
      \<open>ae_inv_ss1 M c''\<close>.  In the halt branch,
      \<open>ae_step_ss8_ss1_invariant_halt\<close> gives the
      \<open>qH \<in> {t_ktm M, r_ktm M} \<and> idx = VFwd\<close> state shape
      at c''.\<close>
  have non_halt_inv:
      "q_out \<notin> {t_ktm M, r_ktm M} \<longrightarrow> ae_inv_ss1 M c''"
  proof
    assume nh: "q_out \<notin> {t_ktm M, r_ktm M}"
    have non_halt_at_c7:
        "case ktc_state c7 of (qM', _, _, _, _) \<Rightarrow>
           qM' \<noteq> t_ktm M \<and> qM' \<noteq> r_ktm M"
      using c7_fst_eq nh by (cases "ktc_state c7") auto
    show "ae_inv_ss1 M c''"
      using ae_step_ss8_ss1_invariant[OF vM inv_ss8 non_halt_at_c7 step8_sub] .
  qed
  have halt_inv:
      "q_out \<in> {t_ktm M, r_ktm M}
          \<longrightarrow> (case ktc_state c'' of (qH, _, _, _, idx)
                  \<Rightarrow> qH \<in> {t_ktm M, r_ktm M} \<and> idx = VFwd)"
  proof
    assume h: "q_out \<in> {t_ktm M, r_ktm M}"
    have halt_at_c7:
        "case ktc_state c7 of (qM', _, _, _, _) \<Rightarrow>
           qM' \<in> {t_ktm M, r_ktm M}"
      using c7_fst_eq h by (cases "ktc_state c7") auto
    show "case ktc_state c'' of (qH, _, _, _, idx)
            \<Rightarrow> qH \<in> {t_ktm M, r_ktm M} \<and> idx = VFwd"
      using ae_step_ss8_ss1_invariant_halt[OF inv_ss8 halt_at_c7 step8_sub] .
  qed

  show ?thesis
    by (rule that[OF step5_sub step5 step6_sub step6 step7_sub step7
                     step8_sub step8 non_halt_inv halt_inv c''_fst_eq
                     gamma_c'' buf_gamma_c''])
qed

text \<open>Reverse-direction dispatcher: unpack \<open>ae_simulates\<close>
  \<^emph>\<open>without\<close> committing to the SS1-versus-halt disjunction.
  Companion to \<open>ae_forward_stage_unpack_sim\<close> (which
  requires the SS1 branch via the non-halt M-state hypotheses).

  Where \<open>ae_forward_stage_unpack_sim\<close> serves forward-direction
  proofs (M-state is mid-simulation by hypothesis, so SS1 is
  forced), \<open>ae_simulates_state_disjunction\<close> serves
  reverse-direction proofs that walk an M'-chain to a canonical halt
  config: at each step the current paired \<open>c'\<close> might be
  mid-simulation (SS1) or already at halt
  (\<open>init_stage le\<close>), and the proof needs both branches
  exposed for case-analysis.\<close>

lemma ae_simulates_state_disjunction:
  fixes M :: "('q, 'a) ktm"
    and cM :: "('a, 'q) ktc_config"
    and c' :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes sim: "ae_simulates M cM c'"
  obtains qM' ofs buf dest idx where
      "ktc_state c' = (qM', ofs, buf, dest, idx)"
    and "ktc_state cM = qM'"
    and "(idx = SS1 \<and> qM' \<notin> {t_ktm M, r_ktm M})
         \<or> (qM' \<in> {t_ktm M, r_ktm M}
              \<and> (ofs, buf, dest, idx) = init_stage (le_ktm M))"
    and "\<forall>k<k_ktm M. ae_tape_correspondence (le_ktm M)
              (ktc_tape cM k) (ktc_tape c' k)"
    and "ae_tape_in_gamma_block M c'"
proof -
  obtain qM' ofs buf dest idx where
      state_comp: "ktc_state c' = (qM', ofs, buf, dest, idx)"
    by (cases "ktc_state c'")
  have sim_body:
      "((idx = SS1 \<and> qM' \<notin> {t_ktm M, r_ktm M})
          \<or> (qM' \<in> {t_ktm M, r_ktm M}
               \<and> (ofs, buf, dest, idx) = init_stage (le_ktm M)))
       \<and> ktc_state cM = qM'
       \<and> (\<forall>k<k_ktm M. ae_tape_correspondence (le_ktm M)
                 (ktc_tape cM k) (ktc_tape c' k))
       \<and> (idx = SS1
            \<longrightarrow> (\<forall>k<k_ktm M. ktc_pos cM k = ae_decode_pos (ktc_pos c' k) (ofs k)))
       \<and> ae_tape_in_gamma_block M c'"
    using sim state_comp unfolding ae_simulates_def by simp
  have qM_eq: "ktc_state cM = qM'" using sim_body by simp
  have state_disj:
      "(idx = SS1 \<and> qM' \<notin> {t_ktm M, r_ktm M})
        \<or> (qM' \<in> {t_ktm M, r_ktm M}
              \<and> (ofs, buf, dest, idx) = init_stage (le_ktm M))"
    using sim_body by simp
  have tape_corr:
      "\<forall>k<k_ktm M. ae_tape_correspondence (le_ktm M)
              (ktc_tape cM k) (ktc_tape c' k)"
    using sim_body by simp
  have gamma_c': "ae_tape_in_gamma_block M c'"
    using sim_body by simp
  show ?thesis
    by (rule that[OF state_comp qM_eq state_disj tape_corr gamma_c'])
qed


subsubsection \<open>Substeps 5 to 8 are determined by the window, without determinism\<close>

text \<open>The det-free replacement for the SS4\<open>\<rightarrow>\<close>SS5 chain-uniqueness
  used in \<open>ae_backward_stage\<close>.  The \<open>det_ktm M\<close> hypothesis was
  consumed only to identify the given backward chain's SS4\<open>\<rightarrow>\<close>SS5
  target with the forward direction's reconstruction.  Both targets satisfy
  \<open>ae_window_invariant_general\<close> against the \<^emph>\<open>same\<close> extracted
  M-trace endpoint, so the identification is a functional inversion of the
  window invariant, not a use of determinism.  The kernel is two
  unconditional injectivity facts about the linearisation: (A)
  \<open>bp_linear\<close> is injective --- the boundary position \<open>bp\<close> is
  recovered from the head \<open>nM\<close>; (B) the \<open>3\<cdot>card\<close>-cell window
  \<open>buf_lin_at blocks\<close> determines \<open>blocks\<close> --- the buffer triple
  is recovered from the tape.  Combined, they give the full-window
  (\<open>pos \<ge> 2\<close>) inversion below.\<close>

text \<open>\<open>c_idx\<close> is injective: it has \<open>enum_class.enum ! c_idx x = x\<close>
  as a section (\<open>c_idx_in_range\<close>), so equal indices give equal
  elements.\<close>

lemma c_idx_inj:
  fixes x y :: "'c :: enum"
  assumes "c_idx x = c_idx y"
  shows "x = y"
proof -
  have "x = (enum_class.enum :: 'c list) ! c_idx x"
    by (rule c_idx_in_range(2)[symmetric])
  also have "\<dots> = (enum_class.enum :: 'c list) ! c_idx y"
    using assms by simp
  also have "\<dots> = y" by (rule c_idx_in_range(2))
  finally show ?thesis .
qed

text \<open>(A) \<open>bp_linear\<close> injective.  The direction component lands the
  value in one of three disjoint length-\<open>card\<close> intervals, so equal
  values force equal directions; \<open>c_idx\<close>-injectivity then forces equal
  cells.\<close>

lemma bp_linear_inj:
  fixes p q :: "('c :: enum) bp"
  assumes "bp_linear p = bp_linear q"
  shows "p = q"
proof -
  obtain d x where p: "p = (d, x)" by (cases p)
  obtain d' y where q: "q = (d', y)" by (cases q)
  have bx: "c_idx x < card (UNIV :: 'c set)" by (rule c_idx_lt_card)
  have by': "c_idx y < card (UNIV :: 'c set)" by (rule c_idx_lt_card)
  from assms have eq:
    "(case d of AE_Left \<Rightarrow> 0 | AE_Home \<Rightarrow> card (UNIV :: 'c set)
        | AE_Right \<Rightarrow> 2 * card (UNIV :: 'c set)) + c_idx x
     = (case d' of AE_Left \<Rightarrow> 0 | AE_Home \<Rightarrow> card (UNIV :: 'c set)
        | AE_Right \<Rightarrow> 2 * card (UNIV :: 'c set)) + c_idx y"
    by (simp add: p q bp_linear_def)
  have "d = d' \<and> c_idx x = c_idx y"
    using eq bx by' by (cases d; cases d'; simp; linarith)
  hence "d = d'" and "x = y" using c_idx_inj by auto
  thus ?thesis by (simp add: p q)
qed

text \<open>(B) the window \<open>buf_lin_at blocks\<close> determines \<open>blocks\<close>.  Each
  of the three blocks is read at every \<open>'c\<close>-cell as \<open>i\<close> sweeps its
  third of the window, because \<open>enum_class.enum\<close> enumerates the whole
  type.\<close>

lemma buf_window_determines:
  fixes b1 b2 :: "(('c :: enum) \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
  assumes "\<forall>i < 3 * card (UNIV :: 'c set). buf_lin_at b1 i = buf_lin_at b2 i"
  shows "b1 = b2"
proof -
  obtain l1 h1 r1 where b1: "b1 = (l1, h1, r1)" by (cases b1)
  obtain l2 h2 r2 where b2: "b2 = (l2, h2, r2)" by (cases b2)
  let ?c = "card (UNIV :: 'c set)"
  have lE: "l1 = l2"
  proof (rule ext)
    fix x :: 'c
    have idx: "c_idx x < ?c" by (rule c_idx_lt_card)
    hence lt: "c_idx x < 3 * ?c" by simp
    have v1: "buf_lin_at b1 (c_idx x) = l1 x"
      using idx by (simp add: b1 buf_lin_at_def Let_def c_idx_in_range(2))
    have v2: "buf_lin_at b2 (c_idx x) = l2 x"
      using idx by (simp add: b2 buf_lin_at_def Let_def c_idx_in_range(2))
    from assms lt have "buf_lin_at b1 (c_idx x) = buf_lin_at b2 (c_idx x)" by blast
    with v1 v2 show "l1 x = l2 x" by simp
  qed
  have hE: "h1 = h2"
  proof (rule ext)
    fix x :: 'c
    have idx: "c_idx x < ?c" by (rule c_idx_lt_card)
    hence lt: "?c + c_idx x < 3 * ?c" by linarith
    have v1: "buf_lin_at b1 (?c + c_idx x) = h1 x"
      using idx by (simp add: b1 buf_lin_at_def Let_def c_idx_in_range(2))
    have v2: "buf_lin_at b2 (?c + c_idx x) = h2 x"
      using idx by (simp add: b2 buf_lin_at_def Let_def c_idx_in_range(2))
    from assms lt have "buf_lin_at b1 (?c + c_idx x) = buf_lin_at b2 (?c + c_idx x)" by blast
    with v1 v2 show "h1 x = h2 x" by simp
  qed
  have rE: "r1 = r2"
  proof (rule ext)
    fix x :: 'c
    have idx: "c_idx x < ?c" by (rule c_idx_lt_card)
    hence lt: "2 * ?c + c_idx x < 3 * ?c" by linarith
    have v1: "buf_lin_at b1 (2 * ?c + c_idx x) = r1 x"
      using idx by (simp add: b1 buf_lin_at_def Let_def c_idx_in_range(2))
    have v2: "buf_lin_at b2 (2 * ?c + c_idx x) = r2 x"
      using idx by (simp add: b2 buf_lin_at_def Let_def c_idx_in_range(2))
    from assms lt have "buf_lin_at b1 (2 * ?c + c_idx x) = buf_lin_at b2 (2 * ?c + c_idx x)" by blast
    with v1 v2 show "r1 x = r2 x" by simp
  qed
  show ?thesis using b1 b2 lE hE rE by simp
qed

text \<open>Per-block reads of \<open>buf_lin_at\<close>: the three thirds of the
  window read the left / home / right block respectively.\<close>

lemma buf_lin_at_l:
  fixes b :: "(('c :: enum) \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
  assumes "i < card (UNIV :: 'c set)"
  shows "buf_lin_at b i = fst b ((enum_class.enum :: 'c list) ! i)"
  using assms by (simp add: buf_lin_at_def case_prod_beta Let_def)

lemma buf_lin_at_h:
  fixes b :: "(('c :: enum) \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
  assumes "card (UNIV :: 'c set) \<le> i" and "i < 2 * card (UNIV :: 'c set)"
  shows "buf_lin_at b i = fst (snd b) ((enum_class.enum :: 'c list) ! (i - card (UNIV :: 'c set)))"
  using assms by (simp add: buf_lin_at_def case_prod_beta Let_def)

lemma buf_lin_at_r:
  fixes b :: "(('c :: enum) \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
  assumes "2 * card (UNIV :: 'c set) \<le> i" and "i < 3 * card (UNIV :: 'c set)"
  shows "buf_lin_at b i = snd (snd b) ((enum_class.enum :: 'c list) ! (i - 2 * card (UNIV :: 'c set)))"
  using assms by (simp add: buf_lin_at_def case_prod_beta Let_def)

text \<open>Per-block determination from window reads over the block's third.\<close>

lemma buf_left_window:
  fixes b1 b2 :: "(('c :: enum) \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
  assumes "\<forall>i < card (UNIV :: 'c set). buf_lin_at b1 i = buf_lin_at b2 i"
  shows "fst b1 = fst b2"
proof (rule ext)
  fix x :: 'c
  have idx: "c_idx x < card (UNIV :: 'c set)" by (rule c_idx_lt_card)
  have "fst b1 x = buf_lin_at b1 (c_idx x)"
    using idx by (simp add: buf_lin_at_l c_idx_in_range(2))
  also have "\<dots> = buf_lin_at b2 (c_idx x)" using assms idx by blast
  also have "\<dots> = fst b2 x"
    using idx by (simp add: buf_lin_at_l c_idx_in_range(2))
  finally show "fst b1 x = fst b2 x" .
qed

lemma buf_home_window:
  fixes b1 b2 :: "(('c :: enum) \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
  assumes "\<forall>i. card (UNIV :: 'c set) \<le> i \<and> i < 2 * card (UNIV :: 'c set)
                 \<longrightarrow> buf_lin_at b1 i = buf_lin_at b2 i"
  shows "fst (snd b1) = fst (snd b2)"
proof (rule ext)
  fix x :: 'c
  let ?c = "card (UNIV :: 'c set)"
  have idx: "c_idx x < ?c" by (rule c_idx_lt_card)
  have lo: "?c \<le> ?c + c_idx x" by simp
  have hi: "?c + c_idx x < 2 * ?c" using idx by linarith
  have "fst (snd b1) x = buf_lin_at b1 (?c + c_idx x)"
    using lo hi by (simp add: buf_lin_at_h c_idx_in_range(2))
  also have "\<dots> = buf_lin_at b2 (?c + c_idx x)" using assms lo hi by blast
  also have "\<dots> = fst (snd b2) x"
    using lo hi by (simp add: buf_lin_at_h c_idx_in_range(2))
  finally show "fst (snd b1) x = fst (snd b2) x" .
qed

lemma buf_right_window:
  fixes b1 b2 :: "(('c :: enum) \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
  assumes "\<forall>i. 2 * card (UNIV :: 'c set) \<le> i \<and> i < 3 * card (UNIV :: 'c set)
                 \<longrightarrow> buf_lin_at b1 i = buf_lin_at b2 i"
  shows "snd (snd b1) = snd (snd b2)"
proof (rule ext)
  fix x :: 'c
  let ?c = "card (UNIV :: 'c set)"
  have idx: "c_idx x < ?c" by (rule c_idx_lt_card)
  have lo: "2 * ?c \<le> 2 * ?c + c_idx x" by simp
  have hi: "2 * ?c + c_idx x < 3 * ?c" using idx by linarith
  have "snd (snd b1) x = buf_lin_at b1 (2 * ?c + c_idx x)"
    using lo hi by (simp add: buf_lin_at_r c_idx_in_range(2))
  also have "\<dots> = buf_lin_at b2 (2 * ?c + c_idx x)" using assms lo hi by blast
  also have "\<dots> = snd (snd b2) x"
    using lo hi by (simp add: buf_lin_at_r c_idx_in_range(2))
  finally show "snd (snd b1) x = snd (snd b2) x" .
qed

text \<open>Full-window inversion (\<open>pos \<ge> 2\<close>): the head and the window
  together determine both the boundary position and the buffer.\<close>

lemma ae_window_invariant_determines:
  fixes tM :: "nat \<Rightarrow> 'a"
  assumes h1: "ae_window_invariant tM nM bp1 b1 p_start"
      and h2: "ae_window_invariant tM nM bp2 b2 p_start"
  shows "bp1 = (bp2 :: ('c :: enum) bp) \<and> b1 = b2"
proof
  from h1 h2 have "nM = p_start + bp_linear bp1" "nM = p_start + bp_linear bp2"
    unfolding ae_window_invariant_def by simp_all
  hence "bp_linear bp1 = bp_linear bp2" by simp
  thus "bp1 = bp2" by (rule bp_linear_inj)
next
  from h1 h2 have
      "\<forall>i < 3 * card (UNIV :: 'c set). tM (p_start + i) = buf_lin_at b1 i"
      "\<forall>i < 3 * card (UNIV :: 'c set). tM (p_start + i) = buf_lin_at b2 i"
    unfolding ae_window_invariant_def by simp_all
  hence "\<forall>i < 3 * card (UNIV :: 'c set). buf_lin_at b1 i = buf_lin_at b2 i" by simp
  thus "b1 = b2" by (rule buf_window_determines)
qed

text \<open>Boundary-position \<open>bp\<close> inversions: the head \<open>nM\<close> determines
  the position even in the \<open>pos = 1\<close> / \<open>pos = 0\<close> cases, where the
  encoding is a direction-case rather than a single \<open>bp_linear\<close>
  equation.  The three directions still land \<open>nM\<close> in disjoint ranges.\<close>

lemma bp_le1_inj:
  fixes bp1 bp2 :: "('c :: enum) bp" and nM :: nat
  assumes A1: "case fst bp1 of AE_Left \<Rightarrow> snd bp1 = c_last \<and> nM = 0
                 | AE_Home \<Rightarrow> nM = Suc (c_idx (snd bp1))
                 | AE_Right \<Rightarrow> nM = Suc (card (UNIV :: 'c set) + c_idx (snd bp1))"
      and A2: "case fst bp2 of AE_Left \<Rightarrow> snd bp2 = c_last \<and> nM = 0
                 | AE_Home \<Rightarrow> nM = Suc (c_idx (snd bp2))
                 | AE_Right \<Rightarrow> nM = Suc (card (UNIV :: 'c set) + c_idx (snd bp2))"
  shows "bp1 = bp2"
proof -
  obtain d1 x1 where p1: "bp1 = (d1, x1)" by (cases bp1)
  obtain d2 x2 where p2: "bp2 = (d2, x2)" by (cases bp2)
  have b1: "c_idx x1 < card (UNIV :: 'c set)" by (rule c_idx_lt_card)
  have b2: "c_idx x2 < card (UNIV :: 'c set)" by (rule c_idx_lt_card)
  have "d1 = d2 \<and> x1 = x2"
    using A1[unfolded p1] A2[unfolded p2] b1 b2
    by (cases d1; cases d2; simp; (linarith | blast intro: c_idx_inj))
  thus ?thesis using p1 p2 by simp
qed

text \<open>Full inversion at \<open>pos = 1\<close>: every direction constrains the
  cell here, so the head pins \<open>bp\<close>; the window plus the fixed left
  block (\<open>LE_block le\<close>) pin all three blocks.\<close>

lemma ae_window_invariant_le1_determines:
  fixes tM :: "nat \<Rightarrow> 'a"
  assumes h1: "ae_window_invariant_le1 tM nM bp1 b1 le"
      and h2: "ae_window_invariant_le1 tM nM bp2 b2 le"
  shows "bp1 = (bp2 :: ('c :: enum) bp) \<and> b1 = b2"
proof -
  let ?c = "card (UNIV :: 'c set)"
  have a1: "case fst bp1 of AE_Left \<Rightarrow> snd bp1 = c_last \<and> nM = 0
              | AE_Home \<Rightarrow> nM = Suc (c_idx (snd bp1))
              | AE_Right \<Rightarrow> nM = Suc (?c + c_idx (snd bp1))"
    using h1 unfolding ae_window_invariant_le1_def by simp
  have a2: "case fst bp2 of AE_Left \<Rightarrow> snd bp2 = c_last \<and> nM = 0
              | AE_Home \<Rightarrow> nM = Suc (c_idx (snd bp2))
              | AE_Right \<Rightarrow> nM = Suc (?c + c_idx (snd bp2))"
    using h2 unfolding ae_window_invariant_le1_def by simp
  have bp: "bp1 = bp2" by (rule bp_le1_inj[OF a1 a2])
  have lefts: "fst b1 = LE_block le" "fst b2 = LE_block le"
    using h1 h2 unfolding ae_window_invariant_le1_def by simp_all
  have e1: "\<forall>i<2 * ?c. tM (Suc i) = buf_lin_at b1 (?c + i)"
    using h1 unfolding ae_window_invariant_le1_def by simp
  have e2: "\<forall>i<2 * ?c. tM (Suc i) = buf_lin_at b2 (?c + i)"
    using h2 unfolding ae_window_invariant_le1_def by simp
  have home: "fst (snd b1) = fst (snd b2)"
  proof (rule buf_home_window, intro allI impI)
    fix i assume "?c \<le> i \<and> i < 2 * ?c"
    then have i1: "?c \<le> i" and i2: "i < 2 * ?c" by auto
    from i2 have lt: "i - ?c < 2 * ?c" by linarith
    from i1 have eq: "?c + (i - ?c) = i" by linarith
    from e1 lt have "tM (Suc (i - ?c)) = buf_lin_at b1 (?c + (i - ?c))" by blast
    with eq have A: "tM (Suc (i - ?c)) = buf_lin_at b1 i" by simp
    from e2 lt have "tM (Suc (i - ?c)) = buf_lin_at b2 (?c + (i - ?c))" by blast
    with eq have B: "tM (Suc (i - ?c)) = buf_lin_at b2 i" by simp
    from A B show "buf_lin_at b1 i = buf_lin_at b2 i" by simp
  qed
  have right: "snd (snd b1) = snd (snd b2)"
  proof (rule buf_right_window, intro allI impI)
    fix i assume "2 * ?c \<le> i \<and> i < 3 * ?c"
    then have i1: "2 * ?c \<le> i" and i2: "i < 3 * ?c" by auto
    from i2 have lt: "i - ?c < 2 * ?c" by linarith
    from i1 have eq: "?c + (i - ?c) = i" by linarith
    from e1 lt have "tM (Suc (i - ?c)) = buf_lin_at b1 (?c + (i - ?c))" by blast
    with eq have A: "tM (Suc (i - ?c)) = buf_lin_at b1 i" by simp
    from e2 lt have "tM (Suc (i - ?c)) = buf_lin_at b2 (?c + (i - ?c))" by blast
    with eq have B: "tM (Suc (i - ?c)) = buf_lin_at b2 i" by simp
    from A B show "buf_lin_at b1 i = buf_lin_at b2 i" by simp
  qed
  have "b1 = b2" using lefts home right by (cases b1; cases b2) auto
  with bp show ?thesis by simp
qed

text \<open>General window inversion (all \<open>pos\<close>).  The home and right
  blocks are determined by the tape window at every \<open>pos\<close>.  For
  \<open>pos \<noteq> 0\<close> the boundary position \<open>bp\<close> and the whole buffer are
  determined.  At \<open>pos = 0\<close> the left block and the home offset of
  \<open>bp\<close> are off-trace (the absent left neighbour of the endmarker, and
  \<open>AE_Home \<Longrightarrow> nM = 0\<close> says nothing of the cell); they are carried from
  the source by the buffered simulation, not pinned by the window.\<close>

lemma ae_window_invariant_general_determines:
  fixes tM :: "nat \<Rightarrow> 'a"
  assumes h1: "ae_window_invariant_general tM nM bp1 b1 pos le"
      and h2: "ae_window_invariant_general tM nM bp2 b2 pos le"
  shows "fst (snd b1) = fst (snd (b2 :: (('c :: enum) \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)))
         \<and> snd (snd b1) = snd (snd b2)
         \<and> (pos \<noteq> 0 \<longrightarrow> bp1 = bp2 \<and> b1 = b2)"
proof (cases "pos \<ge> 2")
  case True
  have w1: "ae_window_invariant tM nM bp1 b1 ((pos - 2) * card (UNIV :: 'c set) + 1)"
    using h1 True unfolding ae_window_invariant_general_def by simp
  have w2: "ae_window_invariant tM nM bp2 b2 ((pos - 2) * card (UNIV :: 'c set) + 1)"
    using h2 True unfolding ae_window_invariant_general_def by simp
  from ae_window_invariant_determines[OF w1 w2]
  have "bp1 = bp2" and "b1 = b2" by simp_all
  thus ?thesis by simp
next
  case False
  show ?thesis
  proof (cases "pos = 1")
    case True
    have l1: "ae_window_invariant_le1 tM nM bp1 b1 le"
      using h1 True unfolding ae_window_invariant_general_def by simp
    have l2: "ae_window_invariant_le1 tM nM bp2 b2 le"
      using h2 True unfolding ae_window_invariant_general_def by simp
    from ae_window_invariant_le1_determines[OF l1 l2]
    have "bp1 = bp2" and "b1 = b2" by simp_all
    thus ?thesis by simp
  next
    case False
    with \<open>\<not> 2 \<le> pos\<close> have pos0: "pos = 0" by simp
    have l1: "ae_window_invariant_le0 tM nM bp1 b1 le"
      using h1 pos0 unfolding ae_window_invariant_general_def by simp
    have l2: "ae_window_invariant_le0 tM nM bp2 b2 le"
      using h2 pos0 unfolding ae_window_invariant_general_def by simp
    let ?c = "card (UNIV :: 'c set)"
    have homes: "fst (snd b1) = LE_block le" "fst (snd b2) = LE_block le"
      using l1 l2 unfolding ae_window_invariant_le0_def by simp_all
    have f1: "\<forall>i<?c. tM (Suc i) = buf_lin_at b1 (2 * ?c + i)"
      using l1 unfolding ae_window_invariant_le0_def by simp
    have f2: "\<forall>i<?c. tM (Suc i) = buf_lin_at b2 (2 * ?c + i)"
      using l2 unfolding ae_window_invariant_le0_def by simp
    have right: "snd (snd b1) = snd (snd b2)"
    proof (rule buf_right_window, intro allI impI)
      fix i assume "2 * ?c \<le> i \<and> i < 3 * ?c"
      then have i1: "2 * ?c \<le> i" and i2: "i < 3 * ?c" by auto
      from i2 have lt: "i - 2 * ?c < ?c" by linarith
      from i1 have eq: "2 * ?c + (i - 2 * ?c) = i" by linarith
      from f1 lt have "tM (Suc (i - 2 * ?c)) = buf_lin_at b1 (2 * ?c + (i - 2 * ?c))" by blast
      with eq have A: "tM (Suc (i - 2 * ?c)) = buf_lin_at b1 i" by simp
      from f2 lt have "tM (Suc (i - 2 * ?c)) = buf_lin_at b2 (2 * ?c + (i - 2 * ?c))" by blast
      with eq have B: "tM (Suc (i - 2 * ?c)) = buf_lin_at b2 i" by simp
      from A B show "buf_lin_at b1 i = buf_lin_at b2 i" by simp
    qed
    from homes right pos0 show ?thesis by auto
  qed
qed

text \<open>Per-tape lift of the window inversion: across the active tapes
  \<open>k < K\<close>, two buffered outputs that both window-correspond to the
  same per-tape trace endpoint agree on the home + right blocks at
  every \<open>pos\<close>, and fully (boundary position and whole buffer) where
  \<open>pos k \<noteq> 0\<close>.  This is the form consumed by the config-level
  SS4\<open>\<rightarrow>\<close>SS5 inversion: the SS4\<open>\<rightarrow>\<close>SS5 state's per-tape buffer / boundary
  components are exactly such families.\<close>

lemma ae_window_general_indexed_determines:
  fixes tM :: "nat \<Rightarrow> nat \<Rightarrow> 'a" and nM pos :: "nat \<Rightarrow> nat"
    and bp1 bp2 :: "nat \<Rightarrow> ('c :: enum) bp"
    and b1 b2 :: "nat \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))"
    and le :: 'a and K :: nat
  assumes h1: "\<forall>k<K. ae_window_invariant_general (tM k) (nM k)
                          (bp1 k) (b1 k) (pos k) le"
      and h2: "\<forall>k<K. ae_window_invariant_general (tM k) (nM k)
                          (bp2 k) (b2 k) (pos k) le"
  shows "\<forall>k<K. fst (snd (b1 k)) = fst (snd (b2 k))
              \<and> snd (snd (b1 k)) = snd (snd (b2 k))
              \<and> (pos k \<noteq> 0 \<longrightarrow> bp1 k = bp2 k \<and> b1 k = b2 k)"
proof (intro allI impI)
  fix k assume k: "k < K"
  from h1 k have g1: "ae_window_invariant_general (tM k) (nM k)
                          (bp1 k) (b1 k) (pos k) le" by blast
  from h2 k have g2: "ae_window_invariant_general (tM k) (nM k)
                          (bp2 k) (b2 k) (pos k) le" by blast
  show "fst (snd (b1 k)) = fst (snd (b2 k))
          \<and> snd (snd (b1 k)) = snd (snd (b2 k))
          \<and> (pos k \<noteq> 0 \<longrightarrow> bp1 k = bp2 k \<and> b1 k = b2 k)"
    by (rule ae_window_invariant_general_determines[OF g1 g2])
qed

subsubsection \<open>The step from substep 4 to substep 5 is determined by its trace\<close>

text \<open>The det-free replacement for \<open>ae_delta_ss4_ss5_functional\<close>.
  The SS4\<open>\<rightarrow>\<close>SS5 macro-step's nondeterminism is confined to the state's
  buffer / boundary-position components (the \<open>m_steps_buffered\<close>
  witness); the tape and head movements are functions of the source
  alone.  This first lemma isolates that: two SS4\<open>\<rightarrow>\<close>SS5 steps from a
  \<^emph>\<open>common\<close> source have identical tape and identical head positions,
  unconditionally (no trace correspondence needed).

  Reading the \<open>ae_delta_ss4_ss5\<close> definition: the write symbol equals
  the read symbol (the step rewrites nothing, it only moves heads), and
  the per-tape direction \<open>d\<close> is \<open>if a k = LE_block le then N else L\<close>
  on active tapes and \<open>N\<close> beyond the tape count --- a function of the read
  tuple \<open>a = \<lambda>k. ts k (n k)\<close>, which the shared source fixes.\<close>

lemma ae_ss4_ss5_shared_source_tape:
  fixes M :: "('q, 'a) ktm"
    and c4 c5a c5b :: "('c :: enum \<Rightarrow> 'a,
                        'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes stepa: "(c4, c5a) \<in> ktm_step (ae_delta_ss4_ss5 M)"
      and stepb: "(c4, c5b) \<in> ktm_step (ae_delta_ss4_ss5 M)"
  shows "ktc_tape c5a = ktc_tape c5b \<and> ktc_pos c5a = ktc_pos c5b"
proof -
  obtain s ts n where c4_eq: "c4 = KConfig s ts n" by (cases c4)
  from stepa c4_eq obtain s'a a'a da where
      a_eq: "c5a = KConfig s'a (\<lambda>k. (ts k)(n k := a'a k))
                                 (\<lambda>k. go_move (da k) (n k))"
    and rela: "(s, (\<lambda>k. ts k (n k)), s'a, a'a, da) \<in> ae_delta_ss4_ss5 M"
    by (auto elim: ktm_step.cases)
  from stepb c4_eq obtain s'b a'b db where
      b_eq: "c5b = KConfig s'b (\<lambda>k. (ts k)(n k := a'b k))
                                 (\<lambda>k. go_move (db k) (n k))"
    and relb: "(s, (\<lambda>k. ts k (n k)), s'b, a'b, db) \<in> ae_delta_ss4_ss5 M"
    by (auto elim: ktm_step.cases)
  \<comment> \<open>Write equals read and direction is canonical in the read, for
      both steps; hence both match the shared source.\<close>
  have wa: "a'a = (\<lambda>k. ts k (n k))"
   and dda: "da = (\<lambda>k. if k < k_ktm M
                          then (if ts k (n k) = LE_block (le_ktm M)
                                  then MoveN else MoveL)
                          else MoveN)"
    using rela unfolding ae_delta_ss4_ss5_def by auto
  have wb: "a'b = (\<lambda>k. ts k (n k))"
   and ddb: "db = (\<lambda>k. if k < k_ktm M
                          then (if ts k (n k) = LE_block (le_ktm M)
                                  then MoveN else MoveL)
                          else MoveN)"
    using relb unfolding ae_delta_ss4_ss5_def by auto
  show ?thesis using a_eq b_eq wa dda wb ddb by simp
qed

subsubsection \<open>At the left end, substeps 5 to 8 ignore the block to the left\<close>

text \<open>At \<open>pos = 0\<close> the home block is uniformly \<open>LE_block le\<close>
  (\<open>= (\<lambda>_. le)\<close>; window \<open>le0\<close>).  Every SS5\<open>\<rightarrow>\<close>SS8 action then routes
  through its \<open>h = LE_block le\<close> branch, which reads only the current
  cell \<open>a\<close>, the right block \<open>r\<close>, and the boundary direction \<open>ds\<close> ---
  never the left block \<open>l\<close>.  And the actions never take the boundary
  \<^emph>\<open>offset\<close> as an argument at all.  So the two components the window
  inversion leaves free at \<open>pos = 0\<close> (the left block and the
  \<open>AE_Home\<close> offset) are invisible to SS5\<open>\<rightarrow>\<close>SS8: no source-carrying
  induction is needed.\<close>

lemma ae_ss5_action_indep_left:
  "ae_ss5_action le a (l, LE_block le, r) ds
     = ae_ss5_action le a (l', LE_block le, r) ds"
  by simp

lemma ae_ss6_action_indep_left:
  "ae_ss6_action le a (l, LE_block le, r) ds
     = ae_ss6_action le a (l', LE_block le, r) ds"
  by simp

lemma ae_ss7_action_indep_left:
  "ae_ss7_action le a (l, LE_block le, r) ds
     = ae_ss7_action le a (l', LE_block le, r) ds"
  by simp

lemma ae_ss8_action_indep_left:
  "ae_ss8_action le a (l, LE_block le, r) ds
     = ae_ss8_action le a (l', LE_block le, r) ds"
  by simp

text \<open>The boundary \<^emph>\<open>direction\<close> (the \<open>dest\<close> the actions read) does
  agree at \<open>pos = 0\<close>: against a fixed head \<open>nM\<close>, \<open>le0\<close> determines
  \<open>fst bp\<close> (\<open>AE_Home\<close> iff \<open>nM = 0\<close>, else \<open>AE_Right\<close>; never
  \<open>AE_Left\<close>), and the whole \<open>bp\<close> except the \<open>AE_Home\<close> offset (the
  one genuine pos=0 don't-care).\<close>

lemma ae_window_le0_dest_agree:
  fixes bp1 bp2 :: "('c :: enum) bp"
  assumes h1: "ae_window_invariant_le0 tM nM bp1 b1 le"
      and h2: "ae_window_invariant_le0 tM nM bp2 b2 le"
  shows "fst bp1 = fst bp2 \<and> (fst bp1 \<noteq> AE_Home \<longrightarrow> bp1 = bp2)"
proof -
  obtain d1 x1 where p1: "bp1 = (d1, x1)" by (cases bp1)
  obtain d2 x2 where p2: "bp2 = (d2, x2)" by (cases bp2)
  have key1: "(d1 = AE_Home \<longrightarrow> nM = 0)
                \<and> (d1 = AE_Right \<longrightarrow> nM = Suc (c_idx x1)) \<and> d1 \<noteq> AE_Left"
    using h1[unfolded ae_window_invariant_le0_def p1] by (cases d1) auto
  have key2: "(d2 = AE_Home \<longrightarrow> nM = 0)
                \<and> (d2 = AE_Right \<longrightarrow> nM = Suc (c_idx x2)) \<and> d2 \<noteq> AE_Left"
    using h2[unfolded ae_window_invariant_le0_def p2] by (cases d2) auto
  have move: "d1 = d2"
  proof (cases "nM = 0")
    case True
    have "d1 = AE_Home" using key1 True by (cases d1) auto
    moreover have "d2 = AE_Home" using key2 True by (cases d2) auto
    ultimately show ?thesis by simp
  next
    case False
    have "d1 = AE_Right" using key1 False by (cases d1) auto
    moreover have "d2 = AE_Right" using key2 False by (cases d2) auto
    ultimately show ?thesis by simp
  qed
  have full: "d1 \<noteq> AE_Home \<longrightarrow> x1 = x2"
  proof
    assume nh: "d1 \<noteq> AE_Home"
    have r1: "d1 = AE_Right" using key1 nh by (cases d1) auto
    have "nM = Suc (c_idx x1)" using key1 r1 by simp
    moreover have "nM = Suc (c_idx x2)" using key2 move r1 by simp
    ultimately have "c_idx x1 = c_idx x2" by simp
    thus "x1 = x2" by (rule c_idx_inj)
  qed
  show ?thesis using move full p1 p2 by simp
qed

text \<open>The per-block agreement the SS5\<open>\<rightarrow>\<close>SS8 actions are congruent under:
  home and right blocks agree, and the left block agrees \<^emph>\<open>where the
  home block is not\<close> \<open>LE_block le\<close> (at the \<open>LE_block\<close> home --- the
  pos=0 case --- the actions never read the left block, so it may
  differ).  Both clauses are delivered at every tape by the window
  inversion + \<open>le0\<close>.\<close>

definition ae_blk_agree ::
  "'a \<Rightarrow> (('c :: enum \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
       \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)) \<Rightarrow> bool" where
  "ae_blk_agree le b1 b2 \<longleftrightarrow>
     fst (snd b1) = fst (snd b2)
     \<and> snd (snd b1) = snd (snd b2)
     \<and> (fst (snd b1) \<noteq> LE_block le \<longrightarrow> fst b1 = fst b2)"

lemma ae_blk_agree_action_eq:
  assumes "ae_blk_agree le b1 b2"
  shows "b1 = b2 \<or> (fst (snd b1) = LE_block le \<and> fst (snd b2) = LE_block le
                      \<and> snd (snd b1) = snd (snd b2))"
proof (cases "fst (snd b1) = LE_block le")
  case False
  hence "fst b1 = fst b2" using assms unfolding ae_blk_agree_def by simp
  moreover have "fst (snd b1) = fst (snd b2)" "snd (snd b1) = snd (snd b2)"
    using assms unfolding ae_blk_agree_def by simp_all
  ultimately have "b1 = b2" by (cases b1; cases b2) auto
  thus ?thesis by simp
next
  case True
  thus ?thesis using assms unfolding ae_blk_agree_def by simp
qed

lemma ae_ss5_action_cong:
  assumes "ae_blk_agree le b1 b2"
  shows "ae_ss5_action le a b1 ds = ae_ss5_action le a b2 ds"
  using ae_blk_agree_action_eq[OF assms]
proof
  assume "b1 = b2" thus ?thesis by simp
next
  assume "fst (snd b1) = LE_block le \<and> fst (snd b2) = LE_block le
            \<and> snd (snd b1) = snd (snd b2)"
  thus ?thesis
    by (cases b1; cases b2)
       (simp add: ae_ss5_action_indep_left)
qed

lemma ae_ss6_action_cong:
  assumes "ae_blk_agree le b1 b2"
  shows "ae_ss6_action le a b1 ds = ae_ss6_action le a b2 ds"
  using ae_blk_agree_action_eq[OF assms]
proof
  assume "b1 = b2" thus ?thesis by simp
next
  assume "fst (snd b1) = LE_block le \<and> fst (snd b2) = LE_block le
            \<and> snd (snd b1) = snd (snd b2)"
  thus ?thesis
    by (cases b1; cases b2)
       (simp add: ae_ss6_action_indep_left)
qed

lemma ae_ss7_action_cong:
  assumes "ae_blk_agree le b1 b2"
  shows "ae_ss7_action le a b1 ds = ae_ss7_action le a b2 ds"
  using ae_blk_agree_action_eq[OF assms]
proof
  assume "b1 = b2" thus ?thesis by simp
next
  assume "fst (snd b1) = LE_block le \<and> fst (snd b2) = LE_block le
            \<and> snd (snd b1) = snd (snd b2)"
  thus ?thesis
    by (cases b1; cases b2)
       (simp add: ae_ss7_action_indep_left)
qed

lemma ae_ss8_action_cong:
  assumes "ae_blk_agree le b1 b2"
  shows "ae_ss8_action le a b1 ds = ae_ss8_action le a b2 ds"
  using ae_blk_agree_action_eq[OF assms]
proof
  assume "b1 = b2" thus ?thesis by simp
next
  assume "fst (snd b1) = LE_block le \<and> fst (snd b2) = LE_block le
            \<and> snd (snd b1) = snd (snd b2)"
  thus ?thesis
    by (cases b1; cases b2)
       (simp add: ae_ss8_action_indep_left)
qed

text \<open>Config-level SS5\<open>\<rightarrow>\<close>SS6 congruence: two configs that agree on
  tape, head positions, state \<open>q\<close> and \<open>dest\<close>, and whose buffers
  are \<open>ae_blk_agree\<close> per tape (offsets / buffers may otherwise differ),
  take an SS5\<open>\<rightarrow>\<close>SS6 step to configs that again agree on tape and head
  positions, with the state advanced to SS6 and \<open>q\<close> / \<open>buf\<close> / \<open>dest\<close>
  carried unchanged.  The reads coincide (tape + pos equal), so the
  action-congruence makes the writes and moves coincide.\<close>

lemma ae_ss5_ss6_cong:
  fixes M :: "('q, 'a) ktm"
    and c1 c2 c1' c2' :: "('c :: enum \<Rightarrow> 'a,
                           'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes tape: "ktc_tape c1 = ktc_tape c2"
      and pos:  "ktc_pos c1 = ktc_pos c2"
      and st1:  "ktc_state c1 = (q, ofs1, buf1, dest, SS5)"
      and st2:  "ktc_state c2 = (q, ofs2, buf2, dest, SS5)"
      and blk:  "\<forall>k. ae_blk_agree (le_ktm M) (buf1 k) (buf2 k)"
      and s1:   "(c1, c1') \<in> ktm_step (ae_delta_ss5_ss6 M)"
      and s2:   "(c2, c2') \<in> ktm_step (ae_delta_ss5_ss6 M)"
  shows "ktc_tape c1' = ktc_tape c2' \<and> ktc_pos c1' = ktc_pos c2'
         \<and> ktc_state c1' = (q, ofs1, buf1, dest, SS6)
         \<and> ktc_state c2' = (q, ofs2, buf2, dest, SS6)"
proof -
  obtain ts n where c1d: "c1 = KConfig (q, ofs1, buf1, dest, SS5) ts n"
    using st1 by (cases c1) auto
  have c2d: "c2 = KConfig (q, ofs2, buf2, dest, SS5) ts n"
    using st2 tape pos c1d by (cases c2) auto
  from s1[unfolded c1d] obtain s1' a'1 d1 where
      c1'd: "c1' = KConfig s1' (\<lambda>k. (ts k)(n k := a'1 k))
                                 (\<lambda>k. go_move (d1 k) (n k))"
    and rel1: "((q, ofs1, buf1, dest, SS5), (\<lambda>k. ts k (n k)),
                s1', a'1, d1) \<in> ae_delta_ss5_ss6 M"
    by (auto elim: ktm_step.cases)
  from s2[unfolded c2d] obtain s2' a'2 d2 where
      c2'd: "c2' = KConfig s2' (\<lambda>k. (ts k)(n k := a'2 k))
                                 (\<lambda>k. go_move (d2 k) (n k))"
    and rel2: "((q, ofs2, buf2, dest, SS5), (\<lambda>k. ts k (n k)),
                s2', a'2, d2) \<in> ae_delta_ss5_ss6 M"
    by (auto elim: ktm_step.cases)
  have e1: "s1' = (q, ofs1, buf1, dest, SS6)"
    and a1: "a'1 = (\<lambda>k. if k < k_ktm M
                          then fst (ae_ss5_action (le_ktm M) (ts k (n k))
                                      (buf1 k) (dest k))
                          else bl_block (bl_ktm M))"
    and d1: "d1 = (\<lambda>k. if k < k_ktm M
                          then snd (ae_ss5_action (le_ktm M) (ts k (n k))
                                      (buf1 k) (dest k))
                          else MoveN)"
    using rel1 unfolding ae_delta_ss5_ss6_def by auto
  have e2: "s2' = (q, ofs2, buf2, dest, SS6)"
    and a2: "a'2 = (\<lambda>k. if k < k_ktm M
                          then fst (ae_ss5_action (le_ktm M) (ts k (n k))
                                      (buf2 k) (dest k))
                          else bl_block (bl_ktm M))"
    and d2: "d2 = (\<lambda>k. if k < k_ktm M
                          then snd (ae_ss5_action (le_ktm M) (ts k (n k))
                                      (buf2 k) (dest k))
                          else MoveN)"
    using rel2 unfolding ae_delta_ss5_ss6_def by auto
  have act: "\<And>k. ae_ss5_action (le_ktm M) (ts k (n k)) (buf1 k) (dest k)
                  = ae_ss5_action (le_ktm M) (ts k (n k)) (buf2 k) (dest k)"
    by (rule ae_ss5_action_cong[OF blk[rule_format]])
  have "a'1 = a'2"
    by (rule ext) (simp add: a1 a2 act)
  moreover have "d1 = d2"
    by (rule ext) (simp add: d1 d2 act)
  ultimately show ?thesis using c1'd c2'd e1 e2 by simp
qed

lemma ae_ss6_ss7_cong:
  fixes M :: "('q, 'a) ktm"
    and c1 c2 c1' c2' :: "('c :: enum \<Rightarrow> 'a,
                           'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes tape: "ktc_tape c1 = ktc_tape c2"
      and pos:  "ktc_pos c1 = ktc_pos c2"
      and st1:  "ktc_state c1 = (q, ofs1, buf1, dest, SS6)"
      and st2:  "ktc_state c2 = (q, ofs2, buf2, dest, SS6)"
      and blk:  "\<forall>k. ae_blk_agree (le_ktm M) (buf1 k) (buf2 k)"
      and s1:   "(c1, c1') \<in> ktm_step (ae_delta_ss6_ss7 M)"
      and s2:   "(c2, c2') \<in> ktm_step (ae_delta_ss6_ss7 M)"
  shows "ktc_tape c1' = ktc_tape c2' \<and> ktc_pos c1' = ktc_pos c2'
         \<and> ktc_state c1' = (q, ofs1, buf1, dest, SS7)
         \<and> ktc_state c2' = (q, ofs2, buf2, dest, SS7)"
proof -
  obtain ts n where c1d: "c1 = KConfig (q, ofs1, buf1, dest, SS6) ts n"
    using st1 by (cases c1) auto
  have c2d: "c2 = KConfig (q, ofs2, buf2, dest, SS6) ts n"
    using st2 tape pos c1d by (cases c2) auto
  from s1[unfolded c1d] obtain s1' a'1 d1 where
      c1'd: "c1' = KConfig s1' (\<lambda>k. (ts k)(n k := a'1 k))
                                 (\<lambda>k. go_move (d1 k) (n k))"
    and rel1: "((q, ofs1, buf1, dest, SS6), (\<lambda>k. ts k (n k)),
                s1', a'1, d1) \<in> ae_delta_ss6_ss7 M"
    by (auto elim: ktm_step.cases)
  from s2[unfolded c2d] obtain s2' a'2 d2 where
      c2'd: "c2' = KConfig s2' (\<lambda>k. (ts k)(n k := a'2 k))
                                 (\<lambda>k. go_move (d2 k) (n k))"
    and rel2: "((q, ofs2, buf2, dest, SS6), (\<lambda>k. ts k (n k)),
                s2', a'2, d2) \<in> ae_delta_ss6_ss7 M"
    by (auto elim: ktm_step.cases)
  have e1: "s1' = (q, ofs1, buf1, dest, SS7)"
    and a1: "a'1 = (\<lambda>k. if k < k_ktm M
                          then fst (ae_ss6_action (le_ktm M) (ts k (n k))
                                      (buf1 k) (dest k))
                          else bl_block (bl_ktm M))"
    and d1: "d1 = (\<lambda>k. if k < k_ktm M
                          then snd (ae_ss6_action (le_ktm M) (ts k (n k))
                                      (buf1 k) (dest k))
                          else MoveN)"
    using rel1 unfolding ae_delta_ss6_ss7_def by auto
  have e2: "s2' = (q, ofs2, buf2, dest, SS7)"
    and a2: "a'2 = (\<lambda>k. if k < k_ktm M
                          then fst (ae_ss6_action (le_ktm M) (ts k (n k))
                                      (buf2 k) (dest k))
                          else bl_block (bl_ktm M))"
    and d2: "d2 = (\<lambda>k. if k < k_ktm M
                          then snd (ae_ss6_action (le_ktm M) (ts k (n k))
                                      (buf2 k) (dest k))
                          else MoveN)"
    using rel2 unfolding ae_delta_ss6_ss7_def by auto
  have act: "\<And>k. ae_ss6_action (le_ktm M) (ts k (n k)) (buf1 k) (dest k)
                  = ae_ss6_action (le_ktm M) (ts k (n k)) (buf2 k) (dest k)"
    by (rule ae_ss6_action_cong[OF blk[rule_format]])
  have "a'1 = a'2"
    by (rule ext) (simp add: a1 a2 act)
  moreover have "d1 = d2"
    by (rule ext) (simp add: d1 d2 act)
  ultimately show ?thesis using c1'd c2'd e1 e2 by simp
qed

lemma ae_ss7_ss8_cong:
  fixes M :: "('q, 'a) ktm"
    and c1 c2 c1' c2' :: "('c :: enum \<Rightarrow> 'a,
                           'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes tape: "ktc_tape c1 = ktc_tape c2"
      and pos:  "ktc_pos c1 = ktc_pos c2"
      and st1:  "ktc_state c1 = (q, ofs1, buf1, dest, SS7)"
      and st2:  "ktc_state c2 = (q, ofs2, buf2, dest, SS7)"
      and blk:  "\<forall>k. ae_blk_agree (le_ktm M) (buf1 k) (buf2 k)"
      and s1:   "(c1, c1') \<in> ktm_step (ae_delta_ss7_ss8 M)"
      and s2:   "(c2, c2') \<in> ktm_step (ae_delta_ss7_ss8 M)"
  shows "ktc_tape c1' = ktc_tape c2' \<and> ktc_pos c1' = ktc_pos c2'
         \<and> ktc_state c1' = (q, ofs1, buf1, dest, SS8)
         \<and> ktc_state c2' = (q, ofs2, buf2, dest, SS8)"
proof -
  obtain ts n where c1d: "c1 = KConfig (q, ofs1, buf1, dest, SS7) ts n"
    using st1 by (cases c1) auto
  have c2d: "c2 = KConfig (q, ofs2, buf2, dest, SS7) ts n"
    using st2 tape pos c1d by (cases c2) auto
  from s1[unfolded c1d] obtain s1' a'1 d1 where
      c1'd: "c1' = KConfig s1' (\<lambda>k. (ts k)(n k := a'1 k))
                                 (\<lambda>k. go_move (d1 k) (n k))"
    and rel1: "((q, ofs1, buf1, dest, SS7), (\<lambda>k. ts k (n k)),
                s1', a'1, d1) \<in> ae_delta_ss7_ss8 M"
    by (auto elim: ktm_step.cases)
  from s2[unfolded c2d] obtain s2' a'2 d2 where
      c2'd: "c2' = KConfig s2' (\<lambda>k. (ts k)(n k := a'2 k))
                                 (\<lambda>k. go_move (d2 k) (n k))"
    and rel2: "((q, ofs2, buf2, dest, SS7), (\<lambda>k. ts k (n k)),
                s2', a'2, d2) \<in> ae_delta_ss7_ss8 M"
    by (auto elim: ktm_step.cases)
  have e1: "s1' = (q, ofs1, buf1, dest, SS8)"
    and a1: "a'1 = (\<lambda>k. if k < k_ktm M
                          then fst (ae_ss7_action (le_ktm M) (ts k (n k))
                                      (buf1 k) (dest k))
                          else bl_block (bl_ktm M))"
    and d1: "d1 = (\<lambda>k. if k < k_ktm M
                          then snd (ae_ss7_action (le_ktm M) (ts k (n k))
                                      (buf1 k) (dest k))
                          else MoveN)"
    using rel1 unfolding ae_delta_ss7_ss8_def by auto
  have e2: "s2' = (q, ofs2, buf2, dest, SS8)"
    and a2: "a'2 = (\<lambda>k. if k < k_ktm M
                          then fst (ae_ss7_action (le_ktm M) (ts k (n k))
                                      (buf2 k) (dest k))
                          else bl_block (bl_ktm M))"
    and d2: "d2 = (\<lambda>k. if k < k_ktm M
                          then snd (ae_ss7_action (le_ktm M) (ts k (n k))
                                      (buf2 k) (dest k))
                          else MoveN)"
    using rel2 unfolding ae_delta_ss7_ss8_def by auto
  have act: "\<And>k. ae_ss7_action (le_ktm M) (ts k (n k)) (buf1 k) (dest k)
                  = ae_ss7_action (le_ktm M) (ts k (n k)) (buf2 k) (dest k)"
    by (rule ae_ss7_action_cong[OF blk[rule_format]])
  have "a'1 = a'2"
    by (rule ext) (simp add: a1 a2 act)
  moreover have "d1 = d2"
    by (rule ext) (simp add: d1 d2 act)
  ultimately show ?thesis using c1'd c2'd e1 e2 by simp
qed

text \<open>The closing SS8\<open>\<rightarrow>\<close>SS1 step also resets \<open>dest\<close> to \<open>init_dest\<close>
  and the substep index to \<open>SS1\<close> (non-halt branch, \<open>q \<notin> {t, r}\<close> ---
  the case the reverse direction runs in).  Otherwise as before: the action
  is congruent under \<open>ae_blk_agree\<close>, so tape and head positions
  coincide, and \<open>q\<close> / \<open>ofs\<close> / \<open>buf\<close> are carried.\<close>

lemma ae_ss8_ss1_cong:
  fixes M :: "('q, 'a) ktm"
    and c1 c2 c1' c2' :: "('c :: enum \<Rightarrow> 'a,
                           'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes tape: "ktc_tape c1 = ktc_tape c2"
      and pos:  "ktc_pos c1 = ktc_pos c2"
      and st1:  "ktc_state c1 = (q, ofs1, buf1, dest, SS8)"
      and st2:  "ktc_state c2 = (q, ofs2, buf2, dest, SS8)"
      and blk:  "\<forall>k. ae_blk_agree (le_ktm M) (buf1 k) (buf2 k)"
      and qnh:  "q \<notin> {t_ktm M, r_ktm M}"
      and s1:   "(c1, c1') \<in> ktm_step (ae_delta_ss8_ss1 M)"
      and s2:   "(c2, c2') \<in> ktm_step (ae_delta_ss8_ss1 M)"
  shows "ktc_tape c1' = ktc_tape c2' \<and> ktc_pos c1' = ktc_pos c2'
         \<and> ktc_state c1' = (q, ofs1, buf1, init_dest, SS1)
         \<and> ktc_state c2' = (q, ofs2, buf2, init_dest, SS1)"
proof -
  obtain ts n where c1d: "c1 = KConfig (q, ofs1, buf1, dest, SS8) ts n"
    using st1 by (cases c1) auto
  have c2d: "c2 = KConfig (q, ofs2, buf2, dest, SS8) ts n"
    using st2 tape pos c1d by (cases c2) auto
  from s1[unfolded c1d] obtain s1' a'1 d1 where
      c1'd: "c1' = KConfig s1' (\<lambda>k. (ts k)(n k := a'1 k))
                                 (\<lambda>k. go_move (d1 k) (n k))"
    and rel1: "((q, ofs1, buf1, dest, SS8), (\<lambda>k. ts k (n k)),
                s1', a'1, d1) \<in> ae_delta_ss8_ss1 M"
    by (auto elim: ktm_step.cases)
  from s2[unfolded c2d] obtain s2' a'2 d2 where
      c2'd: "c2' = KConfig s2' (\<lambda>k. (ts k)(n k := a'2 k))
                                 (\<lambda>k. go_move (d2 k) (n k))"
    and rel2: "((q, ofs2, buf2, dest, SS8), (\<lambda>k. ts k (n k)),
                s2', a'2, d2) \<in> ae_delta_ss8_ss1 M"
    by (auto elim: ktm_step.cases)
  have e1: "s1' = (q, ofs1, buf1, init_dest, SS1)"
    and a1: "a'1 = (\<lambda>k. if k < k_ktm M
                          then fst (ae_ss8_action (le_ktm M) (ts k (n k))
                                      (buf1 k) (dest k))
                          else bl_block (bl_ktm M))"
    and d1: "d1 = (\<lambda>k. if k < k_ktm M
                          then snd (ae_ss8_action (le_ktm M) (ts k (n k))
                                      (buf1 k) (dest k))
                          else MoveN)"
    using rel1 qnh unfolding ae_delta_ss8_ss1_def by auto
  have e2: "s2' = (q, ofs2, buf2, init_dest, SS1)"
    and a2: "a'2 = (\<lambda>k. if k < k_ktm M
                          then fst (ae_ss8_action (le_ktm M) (ts k (n k))
                                      (buf2 k) (dest k))
                          else bl_block (bl_ktm M))"
    and d2: "d2 = (\<lambda>k. if k < k_ktm M
                          then snd (ae_ss8_action (le_ktm M) (ts k (n k))
                                      (buf2 k) (dest k))
                          else MoveN)"
    using rel2 qnh unfolding ae_delta_ss8_ss1_def by auto
  have act: "\<And>k. ae_ss8_action (le_ktm M) (ts k (n k)) (buf1 k) (dest k)
                  = ae_ss8_action (le_ktm M) (ts k (n k)) (buf2 k) (dest k)"
    by (rule ae_ss8_action_cong[OF blk[rule_format]])
  have "a'1 = a'2"
    by (rule ext) (simp add: a1 a2 act)
  moreover have "d1 = d2"
    by (rule ext) (simp add: d1 d2 act)
  ultimately show ?thesis using c1'd c2'd e1 e2 by simp
qed

text \<open>Chaining the four congruences through the macro-cycle tail
  SS5\<open>\<rightarrow>\<close>SS6\<open>\<rightarrow>\<close>SS7\<open>\<rightarrow>\<close>SS8\<open>\<rightarrow>\<close>SS1: two SS5 configs agreeing on tape, head
  positions, \<open>q\<close>, \<open>dest\<close>, and \<open>ae_blk_agree\<close> buffers reach SS1
  boundary configs that agree on tape and head positions, with \<open>q\<close> and
  the (still \<open>ae_blk_agree\<close>) buffers carried and \<open>dest\<close> reset to
  \<open>init_dest\<close>.  The buffers are carried unchanged, so the per-tape
  \<open>ae_blk_agree\<close> hypothesis is reused verbatim at each step.\<close>

lemma ae_ss5_ss8_segment_cong:
  fixes M :: "('q, 'a) ktm"
    and c5a c5b ca cb :: "('c :: enum \<Rightarrow> 'a,
                           'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes tape: "ktc_tape c5a = ktc_tape c5b"
      and pos:  "ktc_pos c5a = ktc_pos c5b"
      and st1:  "ktc_state c5a = (q, ofs1, buf1, dest, SS5)"
      and st2:  "ktc_state c5b = (q, ofs2, buf2, dest, SS5)"
      and blk:  "\<forall>k. ae_blk_agree (le_ktm M) (buf1 k) (buf2 k)"
      and qnh:  "q \<notin> {t_ktm M, r_ktm M}"
      and a56:  "(c5a, d6a) \<in> ktm_step (ae_delta_ss5_ss6 M)"
      and a67:  "(d6a, d7a) \<in> ktm_step (ae_delta_ss6_ss7 M)"
      and a78:  "(d7a, d8a) \<in> ktm_step (ae_delta_ss7_ss8 M)"
      and a81:  "(d8a, ca)  \<in> ktm_step (ae_delta_ss8_ss1 M)"
      and b56:  "(c5b, d6b) \<in> ktm_step (ae_delta_ss5_ss6 M)"
      and b67:  "(d6b, d7b) \<in> ktm_step (ae_delta_ss6_ss7 M)"
      and b78:  "(d7b, d8b) \<in> ktm_step (ae_delta_ss7_ss8 M)"
      and b81:  "(d8b, cb)  \<in> ktm_step (ae_delta_ss8_ss1 M)"
  shows "ktc_tape ca = ktc_tape cb \<and> ktc_pos ca = ktc_pos cb
         \<and> ktc_state ca = (q, ofs1, buf1, init_dest, SS1)
         \<and> ktc_state cb = (q, ofs2, buf2, init_dest, SS1)"
proof -
  from ae_ss5_ss6_cong[OF tape pos st1 st2 blk a56 b56]
  have t6: "ktc_tape d6a = ktc_tape d6b" and p6: "ktc_pos d6a = ktc_pos d6b"
   and s6a: "ktc_state d6a = (q, ofs1, buf1, dest, SS6)"
   and s6b: "ktc_state d6b = (q, ofs2, buf2, dest, SS6)" by simp_all
  from ae_ss6_ss7_cong[OF t6 p6 s6a s6b blk a67 b67]
  have t7: "ktc_tape d7a = ktc_tape d7b" and p7: "ktc_pos d7a = ktc_pos d7b"
   and s7a: "ktc_state d7a = (q, ofs1, buf1, dest, SS7)"
   and s7b: "ktc_state d7b = (q, ofs2, buf2, dest, SS7)" by simp_all
  from ae_ss7_ss8_cong[OF t7 p7 s7a s7b blk a78 b78]
  have t8: "ktc_tape d8a = ktc_tape d8b" and p8: "ktc_pos d8a = ktc_pos d8b"
   and s8a: "ktc_state d8a = (q, ofs1, buf1, dest, SS8)"
   and s8b: "ktc_state d8b = (q, ofs2, buf2, dest, SS8)" by simp_all
  from ae_ss8_ss1_cong[OF t8 p8 s8a s8b blk qnh a81 b81]
  show ?thesis by simp
qed

text \<open>The \<open>ae_simulates\<close> transfer (the congruence that closes the
  pos=0 don't-care).  A reconstructed boundary config \<open>c'''\<close> with
  \<open>ae_simulates M cM c'''\<close> hands its simulation to a given \<open>c''\<close> that
  agrees on tape, head positions, and state \<^emph>\<open>except\<close> the offset \<open>ofs\<close>,
  which need agree only where the simulated head \<open>ktc_pos cM k\<close> is
  non-zero.  At \<open>ktc_pos cM k = 0\<close> the position decode
  \<open>ae_decode_pos\<close> ignores the offset (it returns \<open>0\<close> exactly when its
  AE-head argument is \<open>0\<close>), so the offset residual is invisible.  Both
  configs are at non-halt SS1, where \<open>ae_simulates\<close> reads neither
  \<open>buf\<close> nor \<open>dest\<close>.\<close>

lemma ae_decode_pos_eq_0:
  "ae_decode_pos s i = 0 \<Longrightarrow> s = 0"
  by (simp add: ae_decode_pos_def split: if_splits)

lemma ae_decode_pos_zero_eq: "ae_decode_pos 0 i = 0"
  by (simp add: ae_decode_pos_def)

lemma ae_simulates_transfer:
  fixes M :: "('q, 'a) ktm" and cM :: "('a, 'q) ktc_config"
    and c'' c''' :: "('c :: enum \<Rightarrow> 'a, 'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes sim':   "ae_simulates M cM c'''"
      and cM_inQ: "ktc_state cM \<in> Q_ktm M"
      and cM_nt:  "ktc_state cM \<noteq> t_ktm M"
      and cM_nr:  "ktc_state cM \<noteq> r_ktm M"
      and tape:   "ktc_tape c'' = ktc_tape c'''"
      and pos:    "ktc_pos c'' = ktc_pos c'''"
      and st2:    "ktc_state c'' = (q, ofs1, buf1, init_dest, SS1)"
      and st3:    "ktc_state c''' = (q, ofs2, buf2, init_dest, SS1)"
      and qnh:    "q \<notin> {t_ktm M, r_ktm M}"
      and ofsh:   "\<forall>k<k_ktm M. ktc_pos cM k = 0 \<or> ofs1 k = ofs2 k"
      and gam:    "ae_tape_in_gamma_block M c''"
  shows "ae_simulates M cM c''"
proof -
  obtain qM' ofs buf dest where
      ust: "ktc_state c''' = (qM', ofs, buf, dest, SS1)"
    and qeq: "ktc_state cM = qM'"
    and corr: "\<forall>k<k_ktm M. ae_tape_correspondence (le_ktm M)
                            (ktc_tape cM k) (ktc_tape c''' k)"
    and dec0: "\<forall>k<k_ktm M. ktc_pos cM k
                            = ae_decode_pos (ktc_pos c''' k) (ofs k)"
    by (rule ae_forward_stage_unpack_sim[OF sim' cM_inQ cM_nt cM_nr])
  from ust st3 have qM'eq: "qM' = q" and ofeq: "ofs = ofs2" by auto
  have dec: "\<forall>k<k_ktm M. ktc_pos cM k
                          = ae_decode_pos (ktc_pos c''' k) (ofs2 k)"
    using dec0 ofeq by simp
  have corr2: "\<forall>k<k_ktm M. ae_tape_correspondence (le_ktm M)
                            (ktc_tape cM k) (ktc_tape c'' k)"
    using corr tape by simp
  have qeq2: "ktc_state cM = q" using qeq qM'eq by simp
  have dec2: "\<forall>k<k_ktm M. ktc_pos cM k
                           = ae_decode_pos (ktc_pos c'' k) (ofs1 k)"
  proof (intro allI impI)
    fix k assume k: "k < k_ktm M"
    have d3: "ktc_pos cM k = ae_decode_pos (ktc_pos c''' k) (ofs2 k)"
      by (rule dec[rule_format, OF k])
    have ppos: "ktc_pos c'' k = ktc_pos c''' k" using pos by simp
    show "ktc_pos cM k = ae_decode_pos (ktc_pos c'' k) (ofs1 k)"
    proof (cases "ktc_pos cM k = 0")
      case True
      have "ae_decode_pos (ktc_pos c''' k) (ofs2 k) = 0"
        using d3[symmetric] True by simp
      from ae_decode_pos_eq_0[OF this] have "ktc_pos c''' k = 0" .
      hence "ae_decode_pos (ktc_pos c'' k) (ofs1 k) = 0"
        using ppos by (simp add: ae_decode_pos_zero_eq)
      thus ?thesis using True by simp
    next
      case False
      from ofsh[rule_format, OF k] False have "ofs1 k = ofs2 k" by simp
      hence "ae_decode_pos (ktc_pos c'' k) (ofs1 k)
               = ae_decode_pos (ktc_pos c''' k) (ofs2 k)"
        using ppos by simp
      thus ?thesis using d3 by simp
    qed
  qed
  show ?thesis
    unfolding ae_simulates_def Let_def st2
    using qeq2 corr2 dec2 gam qnh by simp
qed

text \<open>The bridge from the window inversion to the segment congruence's
  hypotheses.  Two SS5 buffered families window-corresponding (per active
  tape) to the same trace endpoint give: their buffers are
  \<open>ae_blk_agree\<close> (home + right agree at every \<open>pos\<close> from the kernel;
  at \<open>pos = 0\<close> the home is \<open>LE_block le\<close> so the left clause is
  vacuous), and their boundary \<^emph>\<open>directions\<close> agree (full \<open>bp\<close>
  agreement where \<open>pos \<noteq> 0\<close>; \<open>le0\<close> direction agreement at
  \<open>pos = 0\<close>).  These are exactly the \<open>buf\<close> / \<open>dest\<close> congruence
  inputs the SS5\<open>\<rightarrow>\<close>SS8 chain consumes.\<close>

lemma ae_ss5_window_blk_dest_agree:
  fixes tM :: "nat \<Rightarrow> nat \<Rightarrow> 'a" and nM pos :: "nat \<Rightarrow> nat"
    and bp1 bp2 :: "nat \<Rightarrow> ('c :: enum) bp"
    and b1 b2 :: "nat \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))"
    and le :: 'a and K :: nat
  assumes h1: "\<forall>k<K. ae_window_invariant_general (tM k) (nM k)
                          (bp1 k) (b1 k) (pos k) le"
      and h2: "\<forall>k<K. ae_window_invariant_general (tM k) (nM k)
                          (bp2 k) (b2 k) (pos k) le"
  shows "(\<forall>k<K. ae_blk_agree le (b1 k) (b2 k))
         \<and> (\<forall>k<K. fst (bp1 k) = fst (bp2 k))"
proof (intro conjI allI impI)
  fix k assume k: "k < K"
  from h1 k have g1: "ae_window_invariant_general (tM k) (nM k)
                          (bp1 k) (b1 k) (pos k) le" by blast
  from h2 k have g2: "ae_window_invariant_general (tM k) (nM k)
                          (bp2 k) (b2 k) (pos k) le" by blast
  from ae_window_invariant_general_determines[OF g1 g2]
  have hr1: "fst (snd (b1 k)) = fst (snd (b2 k))"
   and hr2: "snd (snd (b1 k)) = snd (snd (b2 k))"
   and full: "pos k \<noteq> 0 \<longrightarrow> bp1 k = bp2 k \<and> b1 k = b2 k" by simp_all
  show "ae_blk_agree le (b1 k) (b2 k)"
  proof (cases "pos k = 0")
    case True
    have le0_1: "ae_window_invariant_le0 (tM k) (nM k) (bp1 k) (b1 k) le"
      using g1 True unfolding ae_window_invariant_general_def by simp
    have "fst (snd (b1 k)) = LE_block le"
      using le0_1 unfolding ae_window_invariant_le0_def by simp
    thus ?thesis using hr1 hr2 unfolding ae_blk_agree_def by simp
  next
    case False
    with full have "b1 k = b2 k" by simp
    thus ?thesis unfolding ae_blk_agree_def by simp
  qed
next
  fix k assume k: "k < K"
  from h1 k have g1: "ae_window_invariant_general (tM k) (nM k)
                          (bp1 k) (b1 k) (pos k) le" by blast
  from h2 k have g2: "ae_window_invariant_general (tM k) (nM k)
                          (bp2 k) (b2 k) (pos k) le" by blast
  show "fst (bp1 k) = fst (bp2 k)"
  proof (cases "pos k = 0")
    case True
    have le0_1: "ae_window_invariant_le0 (tM k) (nM k) (bp1 k) (b1 k) le"
      using g1 True unfolding ae_window_invariant_general_def by simp
    have le0_2: "ae_window_invariant_le0 (tM k) (nM k) (bp2 k) (b2 k) le"
      using g2 True unfolding ae_window_invariant_general_def by simp
    from ae_window_le0_dest_agree[OF le0_1 le0_2] show ?thesis by simp
  next
    case False
    from ae_window_invariant_general_determines[OF g1 g2] False
    show ?thesis by simp
  qed
qed

text \<open>Halt branch of the closing SS8\<open>\<rightarrow>\<close>SS1 step.  When
  \<open>q \<in> {t, r}\<close> the builder resets the stage to the constant
  \<open>init_stage (le_ktm M)\<close>, \<^emph>\<open>independent\<close> of the buffers and
  offset --- so the two destination states are \<^emph>\<open>identical\<close> (not
  merely \<open>ae_blk_agree\<close>), and only the tape write needs the
  action-congruence.  This is the halt-case companion of
  \<open>ae_ss8_ss1_cong\<close>.\<close>

lemma ae_ss8_ss1_cong_halt:
  fixes M :: "('q, 'a) ktm"
    and c1 c2 c1' c2' :: "('c :: enum \<Rightarrow> 'a,
                           'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes tape: "ktc_tape c1 = ktc_tape c2"
      and pos:  "ktc_pos c1 = ktc_pos c2"
      and st1:  "ktc_state c1 = (q, ofs1, buf1, dest, SS8)"
      and st2:  "ktc_state c2 = (q, ofs2, buf2, dest, SS8)"
      and blk:  "\<forall>k. ae_blk_agree (le_ktm M) (buf1 k) (buf2 k)"
      and qh:   "q \<in> {t_ktm M, r_ktm M}"
      and s1:   "(c1, c1') \<in> ktm_step (ae_delta_ss8_ss1 M)"
      and s2:   "(c2, c2') \<in> ktm_step (ae_delta_ss8_ss1 M)"
  shows "ktc_tape c1' = ktc_tape c2' \<and> ktc_pos c1' = ktc_pos c2'
         \<and> ktc_state c1' = (q, init_stage (le_ktm M))
         \<and> ktc_state c2' = (q, init_stage (le_ktm M))"
proof -
  obtain ts n where c1d: "c1 = KConfig (q, ofs1, buf1, dest, SS8) ts n"
    using st1 by (cases c1) auto
  have c2d: "c2 = KConfig (q, ofs2, buf2, dest, SS8) ts n"
    using st2 tape pos c1d by (cases c2) auto
  from s1[unfolded c1d] obtain s1' a'1 d1 where
      c1'd: "c1' = KConfig s1' (\<lambda>k. (ts k)(n k := a'1 k))
                                 (\<lambda>k. go_move (d1 k) (n k))"
    and rel1: "((q, ofs1, buf1, dest, SS8), (\<lambda>k. ts k (n k)),
                s1', a'1, d1) \<in> ae_delta_ss8_ss1 M"
    by (auto elim: ktm_step.cases)
  from s2[unfolded c2d] obtain s2' a'2 d2 where
      c2'd: "c2' = KConfig s2' (\<lambda>k. (ts k)(n k := a'2 k))
                                 (\<lambda>k. go_move (d2 k) (n k))"
    and rel2: "((q, ofs2, buf2, dest, SS8), (\<lambda>k. ts k (n k)),
                s2', a'2, d2) \<in> ae_delta_ss8_ss1 M"
    by (auto elim: ktm_step.cases)
  have e1: "s1' = (q, init_stage (le_ktm M))"
    and a1: "a'1 = (\<lambda>k. if k < k_ktm M
                          then fst (ae_ss8_action (le_ktm M) (ts k (n k))
                                      (buf1 k) (dest k))
                          else bl_block (bl_ktm M))"
    and d1: "d1 = (\<lambda>k. if k < k_ktm M
                          then snd (ae_ss8_action (le_ktm M) (ts k (n k))
                                      (buf1 k) (dest k))
                          else MoveN)"
    using rel1 qh unfolding ae_delta_ss8_ss1_def by auto
  have e2: "s2' = (q, init_stage (le_ktm M))"
    and a2: "a'2 = (\<lambda>k. if k < k_ktm M
                          then fst (ae_ss8_action (le_ktm M) (ts k (n k))
                                      (buf2 k) (dest k))
                          else bl_block (bl_ktm M))"
    and d2: "d2 = (\<lambda>k. if k < k_ktm M
                          then snd (ae_ss8_action (le_ktm M) (ts k (n k))
                                      (buf2 k) (dest k))
                          else MoveN)"
    using rel2 qh unfolding ae_delta_ss8_ss1_def by auto
  have act: "\<And>k. ae_ss8_action (le_ktm M) (ts k (n k)) (buf1 k) (dest k)
                  = ae_ss8_action (le_ktm M) (ts k (n k)) (buf2 k) (dest k)"
    by (rule ae_ss8_action_cong[OF blk[rule_format]])
  have "a'1 = a'2"
    by (rule ext) (simp add: a1 a2 act)
  moreover have "d1 = d2"
    by (rule ext) (simp add: d1 d2 act)
  ultimately show ?thesis using c1'd c2'd e1 e2 by simp
qed

text \<open>Halt-agnostic prefix of the macro-cycle tail: chaining the three
  non-branching congruences SS5\<open>\<rightarrow>\<close>SS6\<open>\<rightarrow>\<close>SS7\<open>\<rightarrow>\<close>SS8.  None of these
  three steps inspects the halt flag, so the conclusion carries
  \<open>q\<close> / \<open>dest\<close> / the \<open>ae_blk_agree\<close> buffers unchanged
  whether or not \<open>q\<close> is halting; the halt split re-enters only at the
  final SS8\<open>\<rightarrow>\<close>SS1 step.\<close>

lemma ae_ss5_ss8_segment_to_ss8:
  fixes M :: "('q, 'a) ktm"
    and c5a c5b c8a c8b :: "('c :: enum \<Rightarrow> 'a,
                            'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes tape: "ktc_tape c5a = ktc_tape c5b"
      and pos:  "ktc_pos c5a = ktc_pos c5b"
      and st1:  "ktc_state c5a = (q, ofs1, buf1, dest, SS5)"
      and st2:  "ktc_state c5b = (q, ofs2, buf2, dest, SS5)"
      and blk:  "\<forall>k. ae_blk_agree (le_ktm M) (buf1 k) (buf2 k)"
      and a56:  "(c5a, d6a) \<in> ktm_step (ae_delta_ss5_ss6 M)"
      and a67:  "(d6a, d7a) \<in> ktm_step (ae_delta_ss6_ss7 M)"
      and a78:  "(d7a, c8a) \<in> ktm_step (ae_delta_ss7_ss8 M)"
      and b56:  "(c5b, d6b) \<in> ktm_step (ae_delta_ss5_ss6 M)"
      and b67:  "(d6b, d7b) \<in> ktm_step (ae_delta_ss6_ss7 M)"
      and b78:  "(d7b, c8b) \<in> ktm_step (ae_delta_ss7_ss8 M)"
  shows "ktc_tape c8a = ktc_tape c8b \<and> ktc_pos c8a = ktc_pos c8b
         \<and> ktc_state c8a = (q, ofs1, buf1, dest, SS8)
         \<and> ktc_state c8b = (q, ofs2, buf2, dest, SS8)"
proof -
  from ae_ss5_ss6_cong[OF tape pos st1 st2 blk a56 b56]
  have t6: "ktc_tape d6a = ktc_tape d6b" and p6: "ktc_pos d6a = ktc_pos d6b"
   and s6a: "ktc_state d6a = (q, ofs1, buf1, dest, SS6)"
   and s6b: "ktc_state d6b = (q, ofs2, buf2, dest, SS6)" by simp_all
  from ae_ss6_ss7_cong[OF t6 p6 s6a s6b blk a67 b67]
  have t7: "ktc_tape d7a = ktc_tape d7b" and p7: "ktc_pos d7a = ktc_pos d7b"
   and s7a: "ktc_state d7a = (q, ofs1, buf1, dest, SS7)"
   and s7b: "ktc_state d7b = (q, ofs2, buf2, dest, SS7)" by simp_all
  from ae_ss7_ss8_cong[OF t7 p7 s7a s7b blk a78 b78]
  show ?thesis by simp
qed

text \<open>Halt-case \<open>ae_simulates\<close> transfer.  When the simulated M-config
  \<open>cM\<close> is halting, \<open>ae_simulates\<close> reads only the M-state, the tape
  correspondence, and (via the halt disjunct) that the stage equals
  \<open>init_stage (le_ktm M)\<close> --- never the pos-decode.  So a given \<open>c''\<close>
  whose stage is exactly \<open>init_stage (le_ktm M)\<close> and whose tape matches a
  reconstructed \<open>c'''\<close> with \<open>ae_simulates M cM c'''\<close> inherits the
  simulation.  Uses the halt-agnostic \<open>ae_simulates_state_disjunction\<close>
  (not \<open>ae_forward_stage_unpack_sim\<close>, which needs non-halt \<open>cM\<close>).\<close>

lemma ae_simulates_transfer_halt:
  fixes M :: "('q, 'a) ktm" and cM :: "('a, 'q) ktc_config"
    and c'' c''' :: "('c :: enum \<Rightarrow> 'a, 'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes sim':    "ae_simulates M cM c'''"
      and cM_halt: "ktc_state cM \<in> {t_ktm M, r_ktm M}"
      and tape:    "ktc_tape c'' = ktc_tape c'''"
      and st2:     "ktc_state c'' = (ktc_state cM, init_stage (le_ktm M))"
      and gam:     "ae_tape_in_gamma_block M c''"
  shows "ae_simulates M cM c''"
proof -
  obtain qM' ofs buf dest idx where
      ust: "ktc_state c''' = (qM', ofs, buf, dest, idx)"
    and qeq: "ktc_state cM = qM'"
    and corr: "\<forall>k<k_ktm M. ae_tape_correspondence (le_ktm M)
                            (ktc_tape cM k) (ktc_tape c''' k)"
    by (rule ae_simulates_state_disjunction[OF sim'])
  have corr2: "\<forall>k<k_ktm M. ae_tape_correspondence (le_ktm M)
                            (ktc_tape cM k) (ktc_tape c'' k)"
    using corr tape by simp
  show ?thesis
    unfolding ae_simulates_def Let_def st2 init_stage_def
    using cM_halt corr2 gam by simp
qed

text \<open>The offset-agreement bridge (the non-halt transfer's \<open>ofsh\<close>).
  Two SS5 window-correspondences to the same trace endpoint agree on the
  boundary \<^emph>\<open>offset\<close> \<open>snd bp\<close> \<^emph>\<open>except\<close> where the simulated head
  \<open>nM\<close> is \<open>0\<close>.  Where \<open>pos \<noteq> 0\<close> the kernel pins the full
  \<open>bp\<close>.  Where \<open>pos = 0\<close> the \<open>le0\<close> dest-agreement splits on the
  direction: at \<open>AE_Home\<close> the invariant forces \<open>nM = 0\<close> (the left
  disjunct); otherwise (\<open>AE_Right\<close>) it pins the full \<open>bp\<close>, so the
  offset agrees.  This is precisely the residual being confined to the
  \<open>pos = 0 / AE_Home\<close> corner, where \<open>ae_decode_pos\<close> ignores the
  offset.\<close>

lemma ae_ss5_window_ofs_agree:
  fixes tM :: "nat \<Rightarrow> nat \<Rightarrow> 'a" and nM pos :: "nat \<Rightarrow> nat"
    and bp1 bp2 :: "nat \<Rightarrow> ('c :: enum) bp"
    and b1 b2 :: "nat \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))"
    and le :: 'a and K :: nat
  assumes h1: "\<forall>k<K. ae_window_invariant_general (tM k) (nM k)
                          (bp1 k) (b1 k) (pos k) le"
      and h2: "\<forall>k<K. ae_window_invariant_general (tM k) (nM k)
                          (bp2 k) (b2 k) (pos k) le"
  shows "\<forall>k<K. nM k = 0 \<or> snd (bp1 k) = snd (bp2 k)"
proof (intro allI impI)
  fix k assume k: "k < K"
  from h1 k have g1: "ae_window_invariant_general (tM k) (nM k)
                          (bp1 k) (b1 k) (pos k) le" by blast
  from h2 k have g2: "ae_window_invariant_general (tM k) (nM k)
                          (bp2 k) (b2 k) (pos k) le" by blast
  show "nM k = 0 \<or> snd (bp1 k) = snd (bp2 k)"
  proof (cases "pos k = 0")
    case False
    from ae_window_invariant_general_determines[OF g1 g2] False
    have "bp1 k = bp2 k" by simp
    thus ?thesis by simp
  next
    case True
    have le0_1: "ae_window_invariant_le0 (tM k) (nM k) (bp1 k) (b1 k) le"
      using g1 True unfolding ae_window_invariant_general_def by simp
    have le0_2: "ae_window_invariant_le0 (tM k) (nM k) (bp2 k) (b2 k) le"
      using g2 True unfolding ae_window_invariant_general_def by simp
    from ae_window_le0_dest_agree[OF le0_1 le0_2]
    have full: "fst (bp1 k) \<noteq> AE_Home \<longrightarrow> bp1 k = bp2 k"
      by (rule conjunct2)
    have home_nM0: "fst (bp1 k) = AE_Home \<longrightarrow> nM k = 0"
      using le0_1[unfolded ae_window_invariant_le0_def]
      by (cases "fst (bp1 k)") auto
    show ?thesis
    proof (cases "fst (bp1 k) = AE_Home")
      case True
      thus ?thesis using home_nM0 by simp
    next
      case False
      with full have "bp1 k = bp2 k" by simp
      thus ?thesis by simp
    qed
  qed
qed

text \<open>Integration prototype (non-halt branch).  This is the
  \<open>ae_sim_c''\<close> derivation of \<open>ae_backward_stage\<close> with the \<open>det\<close>
  chain-uniqueness replaced by the det-free toolkit, stated against the
  hypotheses the strengthened \<open>ae_backward_stage_decompose\<close> (run arm)
  and \<open>ae_simulates_forward_stage_general\<close> (forward direction) will expose.
  Both SS4\<open>\<rightarrow>\<close>SS5 steps leave a \<^emph>\<open>common\<close> SS4 source \<open>c3\<close> (the
  SS1\<open>\<rightarrow>\<close>SS4 builders are functional, matched in the real integration);
  both SS5 configs window-correspond to the same trace endpoint
  \<open>cM_new\<close>.  The shared source pins tape+head; the window bridge pins
  the \<open>buf\<close> (\<open>ae_blk_agree\<close>), the \<open>dest\<close> direction, and the
  offset-except-where-\<open>nM=0\<close>; the inactive-tape tails come from both
  SS5 states being \<open>init\<close> beyond \<open>k_ktm M\<close>.  The SS5\<open>\<rightarrow>\<close>SS1 segment
  congruence then transports the agreement to the SS1 boundary, and
  \<open>ae_simulates_transfer\<close> hands the forward simulation across.\<close>

lemma nae_sim_proto_nonhalt:
  fixes M :: "('q, 'a) ktm" and cM_new :: "('a, 'q) ktc_config"
    and c3 c4 c5 c6 c7 c'' :: "('c :: enum \<Rightarrow> 'a,
                               'q \<times> ('a, 'c) ae_stage) ktc_config"
    and c4f c5f c6f c7f c''' :: "('c :: enum \<Rightarrow> 'a,
                                 'q \<times> ('a, 'c) ae_stage) ktc_config"
    and ofs_r ofs_f :: "nat \<Rightarrow> 'c"
    and buf_r buf_f :: "nat \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))"
    and dest_r dest_f :: "nat \<Rightarrow> ae_dest" and pos :: "nat \<Rightarrow> nat"
  assumes q_in_Q:  "ktc_state cM_new \<in> Q_ktm M"
      and nonhalt: "ktc_state cM_new \<notin> {t_ktm M, r_ktm M}"
      \<comment> \<open>common SS4 source\<close>
      and run45: "(c3, c4)  \<in> ktm_step (ae_delta_ss4_ss5 M)"
      and fwd45: "(c3, c4f) \<in> ktm_step (ae_delta_ss4_ss5 M)"
      \<comment> \<open>SS5 states + window correspondences (run / fwd)\<close>
      and c4_state:  "ktc_state c4  = (ktc_state cM_new, ofs_r, buf_r, dest_r, SS5)"
      and c4f_state: "ktc_state c4f = (ktc_state cM_new, ofs_f, buf_f, dest_f, SS5)"
      and run_window: "\<forall>k<k_ktm M. ae_window_invariant_general
              (ktc_tape cM_new k) (ktc_pos cM_new k)
              (dest_r k, ofs_r k) (buf_r k) (pos k) (le_ktm M)"
      and fwd_window: "\<forall>k<k_ktm M. ae_window_invariant_general
              (ktc_tape cM_new k) (ktc_pos cM_new k)
              (dest_f k, ofs_f k) (buf_f k) (pos k) (le_ktm M)"
      \<comment> \<open>inactive-tape tails (both \<open>init\<close> beyond \<open>k_ktm M\<close>)\<close>
      and buf_tail:  "\<forall>k. \<not> k < k_ktm M
                         \<longrightarrow> ae_blk_agree (le_ktm M) (buf_r k) (buf_f k)"
      and dest_tail: "\<forall>k. \<not> k < k_ktm M \<longrightarrow> dest_r k = dest_f k"
      \<comment> \<open>run / forward SS5\<open>\<rightarrow>\<close>SS1 substep chains\<close>
      and run5: "(c4, c5)  \<in> ktm_step (ae_delta_ss5_ss6 M)"
      and run6: "(c5, c6)  \<in> ktm_step (ae_delta_ss6_ss7 M)"
      and run7: "(c6, c7)  \<in> ktm_step (ae_delta_ss7_ss8 M)"
      and run8: "(c7, c'') \<in> ktm_step (ae_delta_ss8_ss1 M)"
      and fwd5: "(c4f, c5f)  \<in> ktm_step (ae_delta_ss5_ss6 M)"
      and fwd6: "(c5f, c6f)  \<in> ktm_step (ae_delta_ss6_ss7 M)"
      and fwd7: "(c6f, c7f)  \<in> ktm_step (ae_delta_ss7_ss8 M)"
      and fwd8: "(c7f, c''') \<in> ktm_step (ae_delta_ss8_ss1 M)"
      and sim_fwd: "ae_simulates M cM_new c'''"
      and gam:     "ae_tape_in_gamma_block M c''"
  shows "ae_simulates M cM_new c''"
proof -
  \<comment> \<open>Shared SS4 source: tape + head positions agree at SS5.\<close>
  from ae_ss4_ss5_shared_source_tape[OF run45 fwd45]
  have tape45: "ktc_tape c4 = ktc_tape c4f"
   and pos45:  "ktc_pos c4 = ktc_pos c4f" by simp_all
  \<comment> \<open>Window bridge: buffers \<open>ae_blk_agree\<close>, \<open>dest\<close> direction agrees
      (active tapes).\<close>
  from ae_ss5_window_blk_dest_agree[OF run_window fwd_window]
  have blk_act: "\<forall>k<k_ktm M. ae_blk_agree (le_ktm M) (buf_r k) (buf_f k)"
   and dir_act: "\<forall>k<k_ktm M. dest_r k = dest_f k" by simp_all
  \<comment> \<open>Offset bridge: \<open>ofs\<close> agrees except where the simulated head is
      \<open>0\<close> --- this is the transfer's \<open>ofsh\<close>.\<close>
  from ae_ss5_window_ofs_agree[OF run_window fwd_window]
  have ofsh: "\<forall>k<k_ktm M. ktc_pos cM_new k = 0 \<or> ofs_r k = ofs_f k" by simp
  \<comment> \<open>Lift \<open>blk\<close> / \<open>dest\<close> agreement to all tapes via the tails.\<close>
  have blk_all: "\<forall>k. ae_blk_agree (le_ktm M) (buf_r k) (buf_f k)"
  proof
    fix k show "ae_blk_agree (le_ktm M) (buf_r k) (buf_f k)"
      by (cases "k < k_ktm M") (use blk_act buf_tail in blast)+
  qed
  have dest_eq: "dest_r = dest_f"
  proof
    fix k show "dest_r k = dest_f k"
      by (cases "k < k_ktm M") (use dir_act dest_tail in blast)+
  qed
  have c4f_state': "ktc_state c4f = (ktc_state cM_new, ofs_f, buf_f, dest_r, SS5)"
    using c4f_state dest_eq by simp
  \<comment> \<open>Transport agreement SS5\<open>\<rightarrow>\<close>SS1 (non-halt branch).\<close>
  from ae_ss5_ss8_segment_cong[OF tape45 pos45 c4_state c4f_state' blk_all
                                  nonhalt run5 run6 run7 run8
                                  fwd5 fwd6 fwd7 fwd8]
  have tcc: "ktc_tape c'' = ktc_tape c'''"
   and pcc: "ktc_pos c'' = ktc_pos c'''"
   and st_c'':  "ktc_state c'' = (ktc_state cM_new, ofs_r, buf_r, init_dest, SS1)"
   and st_c''': "ktc_state c''' = (ktc_state cM_new, ofs_f, buf_f, init_dest, SS1)"
    by simp_all
  \<comment> \<open>Transfer the forward simulation across the agreement.\<close>
  have cM_nt: "ktc_state cM_new \<noteq> t_ktm M" using nonhalt by simp
  have cM_nr: "ktc_state cM_new \<noteq> r_ktm M" using nonhalt by simp
  show ?thesis
    by (rule ae_simulates_transfer[OF sim_fwd q_in_Q cM_nt cM_nr tcc pcc
                                      st_c'' st_c''' nonhalt ofsh gam])
qed

text \<open>Integration prototype (halt branch).  When the simulated M-config
  halts within the macro-cycle (\<open>ktc_state cM_new \<in> {t, r}\<close>) the
  closing SS8\<open>\<rightarrow>\<close>SS1 step resets the stage to \<open>init_stage\<close> instead of
  looping to SS1, so the non-halt segment congruence does not apply.  The
  shared source + window bridge are unchanged; the SS5\<open>\<rightarrow>\<close>SS8 prefix is
  halt-agnostic; the halt SS8\<open>\<rightarrow>\<close>SS1 congruence lands both boundary
  configs in the identical \<open>init_stage\<close> state with agreeing tapes, and
  \<open>ae_simulates_transfer_halt\<close> hands the (halt-disjunct) simulation
  across.  No offset reasoning: the halt disjunct never reads the
  pos-decode.\<close>

lemma nae_sim_proto_halt:
  fixes M :: "('q, 'a) ktm" and cM_new :: "('a, 'q) ktc_config"
    and c3 c4 c5 c6 c7 c'' :: "('c :: enum \<Rightarrow> 'a,
                               'q \<times> ('a, 'c) ae_stage) ktc_config"
    and c4f c5f c6f c7f c''' :: "('c :: enum \<Rightarrow> 'a,
                                 'q \<times> ('a, 'c) ae_stage) ktc_config"
    and ofs_r ofs_f :: "nat \<Rightarrow> 'c"
    and buf_r buf_f :: "nat \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))"
    and dest_r dest_f :: "nat \<Rightarrow> ae_dest" and pos :: "nat \<Rightarrow> nat"
  assumes halt: "ktc_state cM_new \<in> {t_ktm M, r_ktm M}"
      and run45: "(c3, c4)  \<in> ktm_step (ae_delta_ss4_ss5 M)"
      and fwd45: "(c3, c4f) \<in> ktm_step (ae_delta_ss4_ss5 M)"
      and c4_state:  "ktc_state c4  = (ktc_state cM_new, ofs_r, buf_r, dest_r, SS5)"
      and c4f_state: "ktc_state c4f = (ktc_state cM_new, ofs_f, buf_f, dest_f, SS5)"
      and run_window: "\<forall>k<k_ktm M. ae_window_invariant_general
              (ktc_tape cM_new k) (ktc_pos cM_new k)
              (dest_r k, ofs_r k) (buf_r k) (pos k) (le_ktm M)"
      and fwd_window: "\<forall>k<k_ktm M. ae_window_invariant_general
              (ktc_tape cM_new k) (ktc_pos cM_new k)
              (dest_f k, ofs_f k) (buf_f k) (pos k) (le_ktm M)"
      and buf_tail:  "\<forall>k. \<not> k < k_ktm M
                         \<longrightarrow> ae_blk_agree (le_ktm M) (buf_r k) (buf_f k)"
      and dest_tail: "\<forall>k. \<not> k < k_ktm M \<longrightarrow> dest_r k = dest_f k"
      and run5: "(c4, c5)  \<in> ktm_step (ae_delta_ss5_ss6 M)"
      and run6: "(c5, c6)  \<in> ktm_step (ae_delta_ss6_ss7 M)"
      and run7: "(c6, c7)  \<in> ktm_step (ae_delta_ss7_ss8 M)"
      and run8: "(c7, c'') \<in> ktm_step (ae_delta_ss8_ss1 M)"
      and fwd5: "(c4f, c5f)  \<in> ktm_step (ae_delta_ss5_ss6 M)"
      and fwd6: "(c5f, c6f)  \<in> ktm_step (ae_delta_ss6_ss7 M)"
      and fwd7: "(c6f, c7f)  \<in> ktm_step (ae_delta_ss7_ss8 M)"
      and fwd8: "(c7f, c''') \<in> ktm_step (ae_delta_ss8_ss1 M)"
      and sim_fwd: "ae_simulates M cM_new c'''"
      and gam:     "ae_tape_in_gamma_block M c''"
  shows "ae_simulates M cM_new c''"
proof -
  from ae_ss4_ss5_shared_source_tape[OF run45 fwd45]
  have tape45: "ktc_tape c4 = ktc_tape c4f"
   and pos45:  "ktc_pos c4 = ktc_pos c4f" by simp_all
  from ae_ss5_window_blk_dest_agree[OF run_window fwd_window]
  have blk_act: "\<forall>k<k_ktm M. ae_blk_agree (le_ktm M) (buf_r k) (buf_f k)"
   and dir_act: "\<forall>k<k_ktm M. dest_r k = dest_f k" by simp_all
  have blk_all: "\<forall>k. ae_blk_agree (le_ktm M) (buf_r k) (buf_f k)"
  proof
    fix k show "ae_blk_agree (le_ktm M) (buf_r k) (buf_f k)"
      by (cases "k < k_ktm M") (use blk_act buf_tail in blast)+
  qed
  have dest_eq: "dest_r = dest_f"
  proof
    fix k show "dest_r k = dest_f k"
      by (cases "k < k_ktm M") (use dir_act dest_tail in blast)+
  qed
  have c4f_state': "ktc_state c4f = (ktc_state cM_new, ofs_f, buf_f, dest_r, SS5)"
    using c4f_state dest_eq by simp
  \<comment> \<open>Halt-agnostic SS5\<open>\<rightarrow>\<close>SS8 prefix.\<close>
  from ae_ss5_ss8_segment_to_ss8[OF tape45 pos45 c4_state c4f_state' blk_all
                                    run5 run6 run7 fwd5 fwd6 fwd7]
  have t8: "ktc_tape c7 = ktc_tape c7f" and p8: "ktc_pos c7 = ktc_pos c7f"
   and s8:  "ktc_state c7  = (ktc_state cM_new, ofs_r, buf_r, dest_r, SS8)"
   and s8f: "ktc_state c7f = (ktc_state cM_new, ofs_f, buf_f, dest_r, SS8)"
    by simp_all
  \<comment> \<open>Halt SS8\<open>\<rightarrow>\<close>SS1: both boundary configs reach the identical
      \<open>init_stage\<close>, tapes agree.\<close>
  from ae_ss8_ss1_cong_halt[OF t8 p8 s8 s8f blk_all halt run8 fwd8]
  have tcc: "ktc_tape c'' = ktc_tape c'''"
   and st_c'': "ktc_state c'' = (ktc_state cM_new, init_stage (le_ktm M))"
    by simp_all
  show ?thesis
    by (rule ae_simulates_transfer_halt[OF sim_fwd halt tcc st_c'' gam])
qed

text \<open>Combined integration prototype: the full \<open>ae_sim_c''\<close> of
  \<open>ae_backward_stage\<close>, \<open>det\<close>-free.  Takes the union of the two
  branches' exposure and case-splits on whether \<open>cM_new\<close> halts.  This
  is the literal template for the real rewrite in
  \<open>AlphabetEnlargement_Reverse\<close>: the only remaining integration work is
  to (a) strengthen \<open>ae_backward_stage_decompose\<close> to expose the run
  arm's SS5 state \<open>c4_state\<close> + \<open>run_window\<close> (already derived
  internally as \<open>window_cM_new\<close>) and the inactive tails, (b) strengthen
  \<open>ae_simulates_forward_stage_general\<close> to expose its SS5 config
  \<open>c4f\<close> + \<open>fwd_window\<close> + the SS5\<open>\<rightarrow>\<close>SS1 substeps alongside the
  \<open>c'''\<close> it already returns, and (c) match the two SS4 sources
  \<open>c3 = c3_fwd\<close> via the SS1\<open>\<rightarrow>\<close>SS4 functional builders.  No new
  mathematics in the reverse direction.\<close>

lemma nae_sim_proto:
  fixes M :: "('q, 'a) ktm" and cM_new :: "('a, 'q) ktc_config"
    and c3 c4 c5 c6 c7 c'' :: "('c :: enum \<Rightarrow> 'a,
                               'q \<times> ('a, 'c) ae_stage) ktc_config"
    and c4f c5f c6f c7f c''' :: "('c :: enum \<Rightarrow> 'a,
                                 'q \<times> ('a, 'c) ae_stage) ktc_config"
    and ofs_r ofs_f :: "nat \<Rightarrow> 'c"
    and buf_r buf_f :: "nat \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))"
    and dest_r dest_f :: "nat \<Rightarrow> ae_dest" and pos :: "nat \<Rightarrow> nat"
  assumes q_in_Q:  "ktc_state cM_new \<in> Q_ktm M"
      and run45: "(c3, c4)  \<in> ktm_step (ae_delta_ss4_ss5 M)"
      and fwd45: "(c3, c4f) \<in> ktm_step (ae_delta_ss4_ss5 M)"
      and c4_state:  "ktc_state c4  = (ktc_state cM_new, ofs_r, buf_r, dest_r, SS5)"
      and c4f_state: "ktc_state c4f = (ktc_state cM_new, ofs_f, buf_f, dest_f, SS5)"
      and run_window: "\<forall>k<k_ktm M. ae_window_invariant_general
              (ktc_tape cM_new k) (ktc_pos cM_new k)
              (dest_r k, ofs_r k) (buf_r k) (pos k) (le_ktm M)"
      and fwd_window: "\<forall>k<k_ktm M. ae_window_invariant_general
              (ktc_tape cM_new k) (ktc_pos cM_new k)
              (dest_f k, ofs_f k) (buf_f k) (pos k) (le_ktm M)"
      and buf_tail:  "\<forall>k. \<not> k < k_ktm M
                         \<longrightarrow> ae_blk_agree (le_ktm M) (buf_r k) (buf_f k)"
      and dest_tail: "\<forall>k. \<not> k < k_ktm M \<longrightarrow> dest_r k = dest_f k"
      and run5: "(c4, c5)  \<in> ktm_step (ae_delta_ss5_ss6 M)"
      and run6: "(c5, c6)  \<in> ktm_step (ae_delta_ss6_ss7 M)"
      and run7: "(c6, c7)  \<in> ktm_step (ae_delta_ss7_ss8 M)"
      and run8: "(c7, c'') \<in> ktm_step (ae_delta_ss8_ss1 M)"
      and fwd5: "(c4f, c5f)  \<in> ktm_step (ae_delta_ss5_ss6 M)"
      and fwd6: "(c5f, c6f)  \<in> ktm_step (ae_delta_ss6_ss7 M)"
      and fwd7: "(c6f, c7f)  \<in> ktm_step (ae_delta_ss7_ss8 M)"
      and fwd8: "(c7f, c''') \<in> ktm_step (ae_delta_ss8_ss1 M)"
      and sim_fwd: "ae_simulates M cM_new c'''"
      and gam:     "ae_tape_in_gamma_block M c''"
  shows "ae_simulates M cM_new c''"
proof (cases "ktc_state cM_new \<in> {t_ktm M, r_ktm M}")
  case True
  show ?thesis
    by (rule nae_sim_proto_halt[OF True run45 fwd45 c4_state c4f_state
                                   run_window fwd_window buf_tail dest_tail
                                   run5 run6 run7 run8 fwd5 fwd6 fwd7 fwd8
                                   sim_fwd gam])
next
  case False
  show ?thesis
    by (rule nae_sim_proto_nonhalt[OF q_in_Q False run45 fwd45 c4_state
                                      c4f_state run_window fwd_window
                                      buf_tail dest_tail
                                      run5 run6 run7 run8 fwd5 fwd6 fwd7 fwd8
                                      sim_fwd gam])
qed


subsubsection \<open>Assembling a backward stage\<close>

text \<open>\<^emph>\<open>Reverse-direction chain orchestration.\<close>  Combines
  \<open>ae_backward_stage_load_chain\<close>,
  \<open>ae_backward_stage_compute_extract\<close>, and
  \<open>ae_backward_stage_writeback_chain\<close> into a single
  decomposition of an 8-step \<open>alphabet_enlarge_delta\<close>-chain
  from an SS1 boundary configuration.  Exposes the 8 substep facts,
  the substrate trace, its termination disjunction, and halt-aware
  c'' status.

  Design choice: the outer \<open>obtains\<close> exposes only first-order
  conjuncts — projection-level state shape (\<open>fst (ktc_state c'')
  = ktc_state cM_new\<close>) rather than 5-tuple state equalities — to
  avoid the higher-order pattern unification that defeats an
  \<open>OF\<close>-style discharge.  The c4 state-tuple is internal
  plumbing; the consumer only needs first-order projections.\<close>

lemma ae_backward_stage_decompose:
  fixes M :: "('q, 'a) ktm"
    and cM :: "('a, 'q) ktc_config"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                     'q \<times> ('a, 'c) ae_stage) ktc_config"
    and qM' :: 'q
    and ofs :: "nat \<Rightarrow> 'c"
    and buf :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest :: "nat \<Rightarrow> ae_dest"
  assumes vM:          "valid_ktm M"
      and lu:          "le_unique M"
      and sim:         "ae_simulates M cM c'"
      and val_cM:      "valid_config_ktm M cM"
      and c'_state:    "ktc_state c' = (qM', ofs, buf, dest, SS1)"
      and inv_ss1:     "ae_inv_ss1 M c'"
      and gamma_c':    "ae_tape_in_gamma_block M c'"
      and buf_gamma:   "ae_buffer_in_gamma_block M c'"
      and pos_link_c': "ae_position_link M c'"
      and le_anchor:   "\<forall>k<k_ktm M. ktc_tape c' k 0 = LE_block (le_ktm M)"
      and le_neq_bl:   "le_ktm M \<noteq> bl_ktm M"
      and qM'_neq_t:   "qM' \<noteq> t_ktm M"
      and qM'_neq_r:   "qM' \<noteq> r_ktm M"
      and no_le_per_tape:
            "\<forall>k. (ktc_pos c' k \<ge> 2
                    \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                              \<longrightarrow> ktc_tape cM k
                                    ((ktc_pos c' k - 2) * card (UNIV :: 'c set)
                                       + 1 + i)
                                  \<noteq> le_ktm M))
                 \<and> (ktc_pos c' k = 1
                      \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                                \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))
                 \<and> (ktc_pos c' k = 0
                      \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                                \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))"
      and run:         "(c', c'')
                          \<in> ktm_step (alphabet_enlarge_delta M) ^^ 8"
  obtains c1 c2 c3 c4 c5 c6 c7 cM_new n ofs_r buf_r dest_r where
      "(c', c1) \<in> ktm_step (ae_delta_ss1_ss2 M)"
    and "(c1, c2) \<in> ktm_step (ae_delta_ss2_ss3 M)"
    and "(c2, c3) \<in> ktm_step (ae_delta_ss3_ss4 M)"
    and "(c3, c4) \<in> ktm_step (ae_delta_ss4_ss5 M)"
    and "(c4, c5) \<in> ktm_step (ae_delta_ss5_ss6 M)"
    and "(c5, c6) \<in> ktm_step (ae_delta_ss6_ss7 M)"
    and "(c6, c7) \<in> ktm_step (ae_delta_ss7_ss8 M)"
    and "(c7, c'') \<in> ktm_step (ae_delta_ss8_ss1 M)"
    and "(cM, cM_new) \<in> ktm_step (delta_ktm M) ^^ n"
    and "n \<le> card (UNIV :: 'c set)"
    and "n = card (UNIV :: 'c set)
            \<or> ktc_state cM_new \<in> {t_ktm M, r_ktm M}"
    and "fst (ktc_state c'') = ktc_state cM_new"
    and "ktc_state cM_new \<notin> {t_ktm M, r_ktm M}
            \<longrightarrow> ae_inv_ss1 M c''"
    and "ktc_state cM_new \<in> {t_ktm M, r_ktm M}
            \<longrightarrow> snd (snd (snd (snd (ktc_state c'')))) = VFwd"
    and "ae_tape_in_gamma_block M c''"
    and "ae_buffer_in_gamma_block M c''"
    and "ktc_state c4 = (ktc_state cM_new, ofs_r, buf_r, dest_r, SS5)"
    and "\<forall>k<k_ktm M. ae_window_invariant_general
              (ktc_tape cM_new k) (ktc_pos cM_new k)
              (dest_r k, ofs_r k) (buf_r k) (ktc_pos c' k) (le_ktm M)"
    and "ae_buffer_in_gamma_block M c4"
    and "ktc_state cM_new \<in> Q_ktm M"
proof -
  let ?R = "ktm_step (alphabet_enlarge_delta M)"

  \<comment> \<open>Peel the 8-step chain into 8 individual full steps via
      \<open>numeral_eq_Suc\<close>-driven Suc unfolding.  Then rebuild the
      R^^3 prefix and R^^4 suffix for the helper invocations.\<close>
  from run obtain c1' c2' c3 c4 c5' c6' c7' where
      p1:         "(c', c1') \<in> ?R"
    and p2:         "(c1', c2') \<in> ?R"
    and p3:         "(c2', c3) \<in> ?R"
    and step4_full: "(c3, c4) \<in> ?R"
    and p5:         "(c4, c5') \<in> ?R"
    and p6:         "(c5', c6') \<in> ?R"
    and p7:         "(c6', c7') \<in> ?R"
    and p8:         "(c7', c'') \<in> ?R"
    by (auto dest!: relpow_Suc_D2 simp: numeral_eq_Suc)

  \<comment> \<open>Rebuild \<open>(c', c3) \<in> R^^3\<close> via explicit Suc-form
      chain.\<close>
  have a0: "(c', c1') \<in> ?R ^^ Suc 0" using p1 by simp
  have a1: "(c', c2') \<in> ?R ^^ Suc (Suc 0)"
    using relpow_Suc_I[OF a0 p2] .
  have a2: "(c', c3) \<in> ?R ^^ Suc (Suc (Suc 0))"
    using relpow_Suc_I[OF a1 p3] .
  have eq3: "(3::nat) = Suc (Suc (Suc 0))" by (simp add: eval_nat_numeral)
  have load_run: "(c', c3) \<in> ?R ^^ 3"
    using a2 unfolding eq3 .

  \<comment> \<open>Rebuild \<open>(c4, c'') \<in> R^^4\<close>.\<close>
  have b0: "(c4, c5') \<in> ?R ^^ Suc 0" using p5 by simp
  have b1: "(c4, c6') \<in> ?R ^^ Suc (Suc 0)"
    using relpow_Suc_I[OF b0 p6] .
  have b2: "(c4, c7') \<in> ?R ^^ Suc (Suc (Suc 0))"
    using relpow_Suc_I[OF b1 p7] .
  have b3: "(c4, c'') \<in> ?R ^^ Suc (Suc (Suc (Suc 0)))"
    using relpow_Suc_I[OF b2 p8] .
  have eq4: "(4::nat) = Suc (Suc (Suc (Suc 0)))" by (simp add: eval_nat_numeral)
  have writeback_run: "(c4, c'') \<in> ?R ^^ 4"
    using b3 unfolding eq4 .

  \<comment> \<open>Invoke \<open>load_chain\<close> on
      \<open>(c', c3) \<in> R^^3\<close>.  Returns fresh
      c1, c2 (the substep intermediates) with the substep facts and
      c3 invariants.  These c1, c2 may differ syntactically from
      c1', c2' above, but we propagate forward using only c1, c2.\<close>
  obtain c1 c2 where
      step1_sub: "(c', c1) \<in> ktm_step (ae_delta_ss1_ss2 M)"
    and step1_full: "(c', c1) \<in> ?R"
    and step2_sub: "(c1, c2) \<in> ktm_step (ae_delta_ss2_ss3 M)"
    and step2_full: "(c1, c2) \<in> ?R"
    and step3_sub: "(c2, c3) \<in> ktm_step (ae_delta_ss3_ss4 M)"
    and step3_full: "(c2, c3) \<in> ?R"
    and inv_ss4_c3: "ae_inv_ss4 M c3"
    and gamma_c3: "ae_tape_in_gamma_block M c3"
    and buf_gamma_c3: "ae_buffer_in_gamma_block M c3"
    and c3_q_eq: "fst (ktc_state c3) = qM'"
    and pos_link_c3: "ae_position_link M c3"
    by (rule ae_backward_stage_load_chain
                [OF vM c'_state inv_ss1 gamma_c' buf_gamma pos_link_c'
                    qM'_neq_t qM'_neq_r load_run])

  \<comment> \<open>Recover \<open>c3_idx_ss4\<close> for
      \<open>compute_extract\<close>.\<close>
  have c3_idx_ss4: "snd (snd (snd (snd (ktc_state c3)))) = SS4"
    using inv_ss4_c3 unfolding ae_inv_ss4_def
    by (cases "ktc_state c3") auto

  \<comment> \<open>Invoke \<open>compute_extract\<close>.  Returns the cM
      trace, termination disjunction, c4 5-tuple state shape (used
      internally only), and tape/buffer/window propagation facts.\<close>
  obtain cM_new buf' end_pos n where
      step4_sub: "(c3, c4) \<in> ktm_step (ae_delta_ss4_ss5 M)"
    and cM_trace: "(cM, cM_new) \<in> ktm_step (delta_ktm M) ^^ n"
    and n_bnd: "n \<le> card (UNIV :: 'c set)"
    and halt_or_full:
          "n = card (UNIV :: 'c set)
              \<or> ktc_state cM_new \<in> {t_ktm M, r_ktm M}"
    and c4_state:
          "ktc_state c4 = (ktc_state cM_new,
                            \<lambda>k. if k < k_ktm M then snd (end_pos k)
                                  else init_offset k,
                            buf',
                            \<lambda>k. if k < k_ktm M then fst (end_pos k)
                                  else init_dest k, SS5)"
    and c4_tape: "ktc_tape c4 = ktc_tape c'"
    and window_cM_new:
          "\<forall>k<k_ktm M. ae_window_invariant_general
                  (ktc_tape cM_new k) (ktc_pos cM_new k)
                  (end_pos k) (buf' k) (ktc_pos c' k) (le_ktm M)"
    and no_le_cM_new:
          "\<forall>k. (ktc_pos c' k = 0
                  \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                            \<longrightarrow> ktc_tape cM_new k (Suc i) \<noteq> le_ktm M))
              \<and> (ktc_pos c' k = 1
                  \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                            \<longrightarrow> ktc_tape cM_new k (Suc i) \<noteq> le_ktm M))
              \<and> (ktc_pos c' k \<ge> 2
                  \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                            \<longrightarrow> ktc_tape cM_new k
                                  ((ktc_pos c' k - 2) * card (UNIV :: 'c set)
                                     + 1 + i)
                                \<noteq> le_ktm M))"
    and buf'_le_pos0:
          "\<forall>k<k_ktm M. ktc_pos c' k = 0
                  \<longrightarrow> fst (buf' k) \<noteq> LE_block (le_ktm M)"
    by (rule ae_backward_stage_compute_extract
                [OF vM lu val_cM sim c'_state le_anchor le_neq_bl no_le_per_tape
                    step1_sub step2_sub step3_sub step4_full c3_idx_ss4])

  \<comment> \<open>First-order projections from \<open>c4_state\<close> —
      these are the inputs to \<open>writeback_chain\<close>
      (\<open>q_out = ktc_state cM_new\<close>) and the bridge facts used
      in the final discharge.\<close>
  have c4_q: "fst (ktc_state c4) = ktc_state cM_new"
    using c4_state by simp
  have c4_idx_ss5: "snd (snd (snd (snd (ktc_state c4)))) = SS5"
    using c4_state by simp

  \<comment> \<open>Propagate \<open>valid_config_ktm M\<close> through the
      n-step substrate trace to obtain
      \<open>ktc_state cM_new \<in> Q_ktm M\<close>.  Inline induction since
      no packaged multi-step preservation lemma exists.\<close>
  have val_cM_new: "valid_config_ktm M cM_new"
  proof -
    have preserve: "\<And>c_b n0. (cM, c_b) \<in> ktm_step (delta_ktm M) ^^ n0
                                \<Longrightarrow> valid_config_ktm M c_b"
    proof -
      fix c_b n0
      assume "(cM, c_b) \<in> ktm_step (delta_ktm M) ^^ n0"
      thus "valid_config_ktm M c_b"
      proof (induction n0 arbitrary: c_b)
        case 0 thus ?case using val_cM by simp
      next
        case (Suc n0)
        from Suc.prems obtain c_mid where
            ih: "(cM, c_mid) \<in> ktm_step (delta_ktm M) ^^ n0"
          and step_last: "(c_mid, c_b) \<in> ktm_step (delta_ktm M)"
          by (auto elim: relpow_Suc_E)
        have val_mid: "valid_config_ktm M c_mid"
          using Suc.IH[OF ih] .
        show ?case by (rule valid_step_ktm[OF vM step_last val_mid])
      qed
    qed
    show ?thesis using preserve[OF cM_trace] .
  qed
  have q_in_Q: "ktc_state cM_new \<in> Q_ktm M"
  proof -
    obtain Q Sg Gm bl le dt s t r kM where
        Mr: "M = KTM Q Sg Gm bl le dt s t r kM" by (cases M)
    obtain q ts nn where cr: "cM_new = KConfig q ts nn" by (cases cM_new)
    show ?thesis using val_cM_new Mr cr by simp
  qed

  \<comment> \<open>Push gamma / buffer-gamma through step4 to c4.\<close>
  have gamma_c4: "ae_tape_in_gamma_block M c4"
    using ae_step_alphabet_enlarge_gamma_preserve[OF gamma_c3 step4_full] .
  have buf_gamma_c4: "ae_buffer_in_gamma_block M c4"
    using ae_step_alphabet_enlarge_buffer_gamma_preserve
            [OF vM buf_gamma_c3 gamma_c3 step4_full] .

  \<comment> \<open>Assemble \<open>ae_inv_ss5 M c4\<close> for
      \<open>writeback_chain\<close>.\<close>
  have inv_ss5_c4: "ae_inv_ss5 M c4"
    unfolding ae_inv_ss5_def using c4_q c4_idx_ss5 q_in_Q
    by (cases "ktc_state c4") auto

  \<comment> \<open>Invoke \<open>writeback_chain\<close>.
      \<open>q_out = ktc_state cM_new\<close> (via \<open>c4_q\<close>);
      writeback exposes c5, c6, c7 substep facts and the halt-aware
      c'' status keyed on \<open>q_out\<close>.\<close>
  obtain c5 c6 c7 where
      step5_sub: "(c4, c5) \<in> ktm_step (ae_delta_ss5_ss6 M)"
    and step5_full: "(c4, c5) \<in> ?R"
    and step6_sub: "(c5, c6) \<in> ktm_step (ae_delta_ss6_ss7 M)"
    and step6_full: "(c5, c6) \<in> ?R"
    and step7_sub: "(c6, c7) \<in> ktm_step (ae_delta_ss7_ss8 M)"
    and step7_full: "(c6, c7) \<in> ?R"
    and step8_sub: "(c7, c'') \<in> ktm_step (ae_delta_ss8_ss1 M)"
    and step8_full: "(c7, c'') \<in> ?R"
    and c''_non_halt:
          "ktc_state cM_new \<notin> {t_ktm M, r_ktm M}
              \<longrightarrow> ae_inv_ss1 M c''"
    and c''_halt:
          "ktc_state cM_new \<in> {t_ktm M, r_ktm M}
              \<longrightarrow> (case ktc_state c'' of (qH, _, _, _, idx)
                    \<Rightarrow> qH \<in> {t_ktm M, r_ktm M} \<and> idx = VFwd)"
    and c''_q_eq: "fst (ktc_state c'') = ktc_state cM_new"
    and gamma_c'': "ae_tape_in_gamma_block M c''"
    and buf_gamma_c'': "ae_buffer_in_gamma_block M c''"
    by (rule ae_backward_stage_writeback_chain
                [OF vM inv_ss5_c4 c4_q q_in_Q gamma_c4 buf_gamma_c4
                    writeback_run])

  \<comment> \<open>Refine \<open>c''_halt\<close>'s tuple-case form to a
      first-order projection on \<open>snd^4 (ktc_state c'')\<close>.\<close>
  have halt_inv_idx:
      "ktc_state cM_new \<in> {t_ktm M, r_ktm M}
          \<longrightarrow> snd (snd (snd (snd (ktc_state c'')))) = VFwd"
  proof
    assume h: "ktc_state cM_new \<in> {t_ktm M, r_ktm M}"
    have shape:
        "case ktc_state c'' of (qH, _, _, _, idx)
              \<Rightarrow> qH \<in> {t_ktm M, r_ktm M} \<and> idx = VFwd"
      using mp[OF c''_halt h] .
    show "snd (snd (snd (snd (ktc_state c'')))) = VFwd"
      using shape by (cases "ktc_state c''") auto
  qed

  \<comment> \<open>SS5 exposure in the run phase, for the reverse direction without
      determinism.  Name the
      three SS5 stage fields (offset, buffer, dest) so the consumer can
      feed them to \<open>nae_sim_proto\<close>; re-express the window
      correspondence in \<open>(dest, ofs)\<close> bp form (the proto's shape).
      The inactive-tape tails travel inside \<open>buf_gamma_c4\<close>
      (\<open>ae_buffer_in_gamma_block\<close> \<open>\<equiv>\<close> \<open>ae_valid_stage\<close>:
      \<open>buf\<close> / \<open>dest\<close> frozen to \<open>init\<close> beyond \<open>k_ktm M\<close>).\<close>
  define ofs_r where
    "ofs_r = (\<lambda>k. if k < k_ktm M then snd (end_pos k) else init_offset k)"
  define buf_r where "buf_r = buf'"
  define dest_r where
    "dest_r = (\<lambda>k. if k < k_ktm M then fst (end_pos k) else init_dest k)"
  have R_c4_state: "ktc_state c4 = (ktc_state cM_new, ofs_r, buf_r, dest_r, SS5)"
    using c4_state by (simp add: ofs_r_def buf_r_def dest_r_def)
  have R_run_window:
      "\<forall>k<k_ktm M. ae_window_invariant_general
              (ktc_tape cM_new k) (ktc_pos cM_new k)
              (dest_r k, ofs_r k) (buf_r k) (ktc_pos c' k) (le_ktm M)"
  proof (intro allI impI)
    fix k assume klt: "k < k_ktm M"
    have bp_eq: "(dest_r k, ofs_r k) = end_pos k"
      using klt by (simp add: dest_r_def ofs_r_def)
    show "ae_window_invariant_general (ktc_tape cM_new k) (ktc_pos cM_new k)
            (dest_r k, ofs_r k) (buf_r k) (ktc_pos c' k) (le_ktm M)"
      using window_cM_new[rule_format, OF klt] bp_eq by (simp add: buf_r_def)
  qed

  \<comment> \<open>Final discharge: 19 first-order conjuncts, no HOU patterns.\<close>
  show ?thesis
    by (rule that[OF step1_sub step2_sub step3_sub step4_sub
                     step5_sub step6_sub step7_sub step8_sub
                     cM_trace n_bnd halt_or_full c''_q_eq
                     c''_non_halt halt_inv_idx gamma_c'' buf_gamma_c''
                     R_c4_state R_run_window buf_gamma_c4 q_in_Q])
qed


text \<open>\<^emph>\<open>Reverse-direction top-level wrapper.\<close>  Given the
  simulation invariant at an SS1 boundary configuration
  \<open>c'\<close> and an 8-step
  \<open>alphabet_enlarge_delta\<close>-chain
  \<open>(c', c'') \<in> R^^8\<close>, produces the corresponding
  substrate trace \<open>(cM, cM_new) \<in> step^n\<close> with
  \<open>n \<le> c\<close> and asserts the simulation invariant at the
  new boundary configuration \<open>c''\<close>.

  This is the reverse-direction counterpart to
  \<open>ae_simulates_forward_stage_general\<close>.  The internal
  decomposition is handled by
  \<open>ae_backward_stage_decompose\<close>; this wrapper
  unpacks the simulation invariant via
  \<open>ae_forward_stage_unpack_sim\<close>, invokes the decompose
  lemma, and re-packages the conclusions in terms of the
  \<open>ae_simulates\<close> invariant for the consumer (Step 4
  validation-trace-unique-to-SS1, ultimately
  \<open>alphabet_enlarge_language\<close>'s reverse implication).

  The body has two substantive components beyond the decompose
  invocation:

  \<^item> \<^emph>\<open>\<open>le_anchor\<close> preservation at \<open>c''\<close>\<close>:
    each of the 8 substeps preserves
    \<open>ktc_tape c kk 0 = LE_block (le_ktm M)\<close>.  Discharged
    directly via the substrate's
    \<open>ktm_relpow_LE_pos0_preserve\<close> applied to the
    enlarged machine, in one step, with no derivation per
    substep.

  \<^item> \<^emph>\<open>\<open>ae_simulates M cM_new c''\<close>\<close>: the full
    simulation invariant — tape correspondence, position decoding
    in the non-halt branch, halt-shape in the halt branch.
    Derived using the substep facts from the decomposition plus the same
    regime-aware writeback machinery the forward direction uses
    (\<open>pos_link\<close> propagation, tape preservation across
    writeback writes, per-tape regime case-splits for position
    decoding).

  An earlier draft of this wrapper also exposed a position
  displacement disjunct (\<open>ktc_pos c'' kk \<in> {p, p+1, p-1}\<close>
  per tape).  Audit showed the consuming wrapper
  (\<open>ae_trace_decode\<close>) doesn't need it; the forward direction's
  parallel \<open>disp_c8\<close> was bound at its only call site
  (\<open>ae_simulation_phase_chunked\<close>) but never referenced.
  Dropped as dead code.\<close>

lemma ae_backward_stage:
  fixes M :: "('q, 'a) ktm"
    and cM :: "('a, 'q) ktc_config"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                     'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes vM:           "valid_ktm M"
      and lu:           "le_unique M"
      and sim:          "ae_simulates M cM c'"
      and val_cM:       "valid_config_ktm M cM"
      and q_neq_t:      "ktc_state cM \<noteq> t_ktm M"
      and q_neq_r:      "ktc_state cM \<noteq> r_ktm M"
      and buf_gamma:    "ae_buffer_in_gamma_block M c'"
      and le_anchor:    "\<forall>kk<k_ktm M. ktc_tape c' kk 0 = LE_block (le_ktm M)"
      and le_neq_bl:    "le_ktm M \<noteq> bl_ktm M"
      and no_le_per_tape:
            "\<forall>k. (ktc_pos c' k \<ge> 2
                    \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                              \<longrightarrow> ktc_tape cM k
                                    ((ktc_pos c' k - 2) * card (UNIV :: 'c set)
                                       + 1 + i)
                                  \<noteq> le_ktm M))
                 \<and> (ktc_pos c' k = 1
                      \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                                \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))
                 \<and> (ktc_pos c' k = 0
                      \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                                \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))"
      and run:          "(c', c'') \<in> ktm_step (alphabet_enlarge_delta M) ^^ 8"
  obtains cM_new n where
      "(cM, cM_new) \<in> ktm_step (delta_ktm M) ^^ n"
    and "n \<le> card (UNIV :: 'c set)"
    and "n = card (UNIV :: 'c set)
            \<or> ktc_state cM_new \<in> {t_ktm M, r_ktm M}"
    and "ae_simulates M cM_new c''"
    and "ae_buffer_in_gamma_block M c''"
    and "\<forall>kk<k_ktm M. ktc_tape c'' kk 0 = LE_block (le_ktm M)"
proof -
  \<comment> \<open>Derive \<open>ktc_state cM \<in> Q_ktm M\<close> from
      \<open>val_cM\<close> for the sim-unpack invocation.\<close>
  have qM_in_Q: "ktc_state cM \<in> Q_ktm M"
  proof -
    obtain Q Sg Gm bl le dt s t r kM where
        Mr: "M = KTM Q Sg Gm bl le dt s t r kM" by (cases M)
    obtain q ts nn where cr: "cM = KConfig q ts nn" by (cases cM)
    show ?thesis using val_cM Mr cr by simp
  qed

  \<comment> \<open>Unpack the simulation invariant at \<open>c'\<close>.\<close>
  obtain qM' ofs buf dest where
      c'_state:     "ktc_state c' = (qM', ofs, buf, dest, SS1)"
    and qM_eq:      "ktc_state cM = qM'"
    and qM'_in_Q:   "qM' \<in> Q_ktm M"
    and qM'_neq_t:  "qM' \<noteq> t_ktm M"
    and qM'_neq_r:  "qM' \<noteq> r_ktm M"
    and tape_corr:  "\<forall>k<k_ktm M. ae_tape_correspondence (le_ktm M)
                            (ktc_tape cM k) (ktc_tape c' k)"
    and pos_decode: "\<forall>k<k_ktm M. ktc_pos cM k = ae_decode_pos (ktc_pos c' k) (ofs k)"
    and gamma_c':   "ae_tape_in_gamma_block M c'"
    and inv_ss1:    "ae_inv_ss1 M c'"
    and pos_link_c': "ae_position_link M c'"
    by (rule ae_forward_stage_unpack_sim[OF sim qM_in_Q q_neq_t q_neq_r])

  \<comment> \<open>Decompose the 8-step chain.\<close>
  obtain c1 c2 c3 c4 c5 c6 c7 cM_new n ofs_r buf_r dest_r where
      step1_sub: "(c', c1) \<in> ktm_step (ae_delta_ss1_ss2 M)"
    and step2_sub: "(c1, c2) \<in> ktm_step (ae_delta_ss2_ss3 M)"
    and step3_sub: "(c2, c3) \<in> ktm_step (ae_delta_ss3_ss4 M)"
    and step4_sub: "(c3, c4) \<in> ktm_step (ae_delta_ss4_ss5 M)"
    and step5_sub: "(c4, c5) \<in> ktm_step (ae_delta_ss5_ss6 M)"
    and step6_sub: "(c5, c6) \<in> ktm_step (ae_delta_ss6_ss7 M)"
    and step7_sub: "(c6, c7) \<in> ktm_step (ae_delta_ss7_ss8 M)"
    and step8_sub: "(c7, c'') \<in> ktm_step (ae_delta_ss8_ss1 M)"
    and cM_trace: "(cM, cM_new) \<in> ktm_step (delta_ktm M) ^^ n"
    and n_bnd:    "n \<le> card (UNIV :: 'c set)"
    and halt_or_full:
          "n = card (UNIV :: 'c set)
              \<or> ktc_state cM_new \<in> {t_ktm M, r_ktm M}"
    and c''_fst_eq: "fst (ktc_state c'') = ktc_state cM_new"
    and c''_non_halt:
          "ktc_state cM_new \<notin> {t_ktm M, r_ktm M}
              \<longrightarrow> ae_inv_ss1 M c''"
    and c''_halt_idx:
          "ktc_state cM_new \<in> {t_ktm M, r_ktm M}
              \<longrightarrow> snd (snd (snd (snd (ktc_state c'')))) = VFwd"
    and gamma_c'': "ae_tape_in_gamma_block M c''"
    and buf_gamma_c'': "ae_buffer_in_gamma_block M c''"
    and run_c4_state:
          "ktc_state c4 = (ktc_state cM_new, ofs_r, buf_r, dest_r, SS5)"
    and run_window:
          "\<forall>k<k_ktm M. ae_window_invariant_general
                  (ktc_tape cM_new k) (ktc_pos cM_new k)
                  (dest_r k, ofs_r k) (buf_r k) (ktc_pos c' k) (le_ktm M)"
    and run_buf_gamma_c4: "ae_buffer_in_gamma_block M c4"
    and run_q_in_Q: "ktc_state cM_new \<in> Q_ktm M"
    by (rule ae_backward_stage_decompose
                [OF vM lu sim val_cM c'_state inv_ss1 gamma_c' buf_gamma
                    pos_link_c' le_anchor le_neq_bl qM'_neq_t qM'_neq_r
                    no_le_per_tape run])

  \<comment> \<open>The \<open>le_anchor\<close>-at-\<open>c''\<close> conclusion collapses to a
      direct invocation of the substrate-level
      \<open>ktm_relpow_LE_pos0_preserve\<close> applied to the
      enlarged machine, with the \<open>delta_ktm\<close> /
      \<open>le_ktm\<close> bridges discharging the
      \<open>alphabet_enlarge_delta\<close> \<open>\<leftrightarrow>\<close>
      \<open>delta_ktm (alphabet_enlarge M)\<close> and
      \<open>LE_block (le_ktm M)\<close> \<open>\<leftrightarrow>\<close>
      \<open>le_ktm (alphabet_enlarge M)\<close> identities.\<close>
  have le_anchor_c'': "\<forall>kk<k_ktm M. ktc_tape c'' kk 0 = LE_block (le_ktm M)"
  proof (intro allI impI)
    fix kk
    assume kklt: "kk < k_ktm M"
    let ?M' = "alphabet_enlarge M
                  :: ('q \<times> ('a, 'c) ae_stage,
                      'c \<Rightarrow> 'a) ktm"
    have vM': "valid_ktm ?M'"
      by (rule alphabet_enlarge_wf[OF vM])
    have run': "(c', c'') \<in> ktm_step (delta_ktm ?M') ^^ 8"
      using run by (simp add: delta_ktm_alphabet_enlarge)
    have le_at_c'_kk: "ktc_tape c' kk 0 = le_ktm ?M'"
      using le_anchor[rule_format, OF kklt] by (simp add: le_ktm_alphabet_enlarge)
    have "ktc_tape c'' kk 0 = le_ktm ?M'"
      by (rule ktm_relpow_LE_pos0_preserve[OF vM' run' le_at_c'_kk])
    then show "ktc_tape c'' kk 0 = LE_block (le_ktm M)"
      by (simp add: le_ktm_alphabet_enlarge)
  qed
  \<comment> \<open>Sub-step \<open>ae_sim_c''\<close> (\<open>det\<close>-free): rather than
      identify the backward boundary \<open>c''\<close> with the forward
      witness \<open>c'''\<close> by chain uniqueness (which needs
      \<open>det_ktm M\<close>), apply \<open>nae_sim_proto\<close>.  The forward
      direction rebuilds a \<open>c'''\<close> simulating the \<^emph>\<open>same\<close>
      extracted M-trace endpoint \<open>cM_new\<close>, now exposing its SS5
      config; the two arms share the SS4 source \<open>c3\<close> (the
      functional SS1\<open>\<rightarrow>\<close>SS4 builders force \<open>c1 = c1f\<close>,
      \<open>c2 = c2f\<close>, \<open>c3 = c3f\<close>); the window invariant against
      the common \<open>cM_new\<close> pins the SS5 outputs modulo the
      pos\<open>=\<close>0 offset don't-care; and the inactive-tape tails agree
      because \<open>ae_buffer_in_gamma_block\<close> freezes both arms'
      \<open>buf\<close> / \<open>dest\<close> to \<open>init\<close> beyond \<open>k_ktm M\<close>.
      The forward direction's full \<open>ae_simulates\<close> transports across
      the SS5\<open>\<rightarrow>\<close>SS1 congruence to \<open>c''\<close>.\<close>
  have ae_sim_c'': "ae_simulates M cM_new c''"
  proof -
    \<comment> \<open>Forward direction: a \<open>c'''\<close> simulating the same \<open>cM_new\<close>,
        with its full substep chain + SS5 exposure.\<close>
    obtain c''' c1f c2f c3f c4f c5f c6f c7f ofs_f buf_f dest_f where
        fwd_chain: "(c', c''')
                       \<in> ktm_step (alphabet_enlarge_delta M) ^^ 8"
      and sim_c''': "ae_simulates M cM_new c'''"
      and fwd_bufg_c''': "ae_buffer_in_gamma_block M c'''"
      and fwd_le_c''': "\<forall>kk<k_ktm M. ktc_tape c''' kk 0 = LE_block (le_ktm M)"
      and f_step1: "(c', c1f) \<in> ktm_step (ae_delta_ss1_ss2 M)"
      and f_step2: "(c1f, c2f) \<in> ktm_step (ae_delta_ss2_ss3 M)"
      and f_step3: "(c2f, c3f) \<in> ktm_step (ae_delta_ss3_ss4 M)"
      and f_step4: "(c3f, c4f) \<in> ktm_step (ae_delta_ss4_ss5 M)"
      and f_step5: "(c4f, c5f) \<in> ktm_step (ae_delta_ss5_ss6 M)"
      and f_step6: "(c5f, c6f) \<in> ktm_step (ae_delta_ss6_ss7 M)"
      and f_step7: "(c6f, c7f) \<in> ktm_step (ae_delta_ss7_ss8 M)"
      and f_step8: "(c7f, c''') \<in> ktm_step (ae_delta_ss8_ss1 M)"
      and fwd_c4_state:
            "ktc_state c4f = (ktc_state cM_new, ofs_f, buf_f, dest_f, SS5)"
      and fwd_window:
            "\<forall>kk<k_ktm M. ae_window_invariant_general
                    (ktc_tape cM_new kk) (ktc_pos cM_new kk)
                    (dest_f kk, ofs_f kk) (buf_f kk) (ktc_pos c' kk) (le_ktm M)"
      and fwd_buf_gamma_c4f: "ae_buffer_in_gamma_block M c4f"
      by (rule ae_simulates_forward_stage_general
                  [OF vM lu sim qM_in_Q q_neq_t q_neq_r buf_gamma n_bnd
                      cM_trace halt_or_full le_anchor le_neq_bl
                      no_le_per_tape])

    \<comment> \<open>Shared SS4 source: both arms load SS1\<open>\<rightarrow>\<close>SS4 from \<open>c'\<close>
        through the functional substep builders.\<close>
    have c1_eq: "c1 = c1f"
      by (rule ktm_step_functional [OF _ step1_sub f_step1])
        (use ae_delta_ss1_ss2_functional in blast)
    have f_step2': "(c1, c2f) \<in> ktm_step (ae_delta_ss2_ss3 M)"
      using f_step2 c1_eq by simp
    have c2_eq: "c2 = c2f"
      by (rule ktm_step_functional [OF _ step2_sub f_step2'])
        (use ae_delta_ss2_ss3_functional in blast)
    have f_step3': "(c2, c3f) \<in> ktm_step (ae_delta_ss3_ss4 M)"
      using f_step3 c2_eq by simp
    have c3_eq: "c3 = c3f"
      by (rule ktm_step_functional [OF _ step3_sub f_step3'])
        (use ae_delta_ss3_ss4_functional in blast)
    have fwd45: "(c3, c4f) \<in> ktm_step (ae_delta_ss4_ss5 M)"
      using f_step4 c3_eq by simp

    \<comment> \<open>Inactive-tape tails: \<open>ae_buffer_in_gamma_block\<close> carries
        the \<open>ae_valid_stage\<close> tail, freezing \<open>buf\<close> / \<open>dest\<close>
        to \<open>init\<close> beyond \<open>k_ktm M\<close> on both arms, so they agree
        there.\<close>
    have run_tails:
        "(\<forall>j\<ge>k_ktm M. buf_r j = init_buffer (le_ktm M) j)
          \<and> (\<forall>j\<ge>k_ktm M. dest_r j = init_dest j)"
      using run_buf_gamma_c4[unfolded ae_buffer_in_gamma_block_def run_c4_state]
      by simp
    have fwd_tails:
        "(\<forall>j\<ge>k_ktm M. buf_f j = init_buffer (le_ktm M) j)
          \<and> (\<forall>j\<ge>k_ktm M. dest_f j = init_dest j)"
      using fwd_buf_gamma_c4f[unfolded ae_buffer_in_gamma_block_def fwd_c4_state]
      by simp
    have buf_tail:
        "\<forall>k. \<not> k < k_ktm M
              \<longrightarrow> ae_blk_agree (le_ktm M) (buf_r k) (buf_f k)"
    proof (intro allI impI)
      fix k assume "\<not> k < k_ktm M"
      hence kge: "k_ktm M \<le> k" by simp
      have "buf_r k = buf_f k" using run_tails fwd_tails kge by simp
      thus "ae_blk_agree (le_ktm M) (buf_r k) (buf_f k)"
        by (simp add: ae_blk_agree_def)
    qed
    have dest_tail: "\<forall>k. \<not> k < k_ktm M \<longrightarrow> dest_r k = dest_f k"
    proof (intro allI impI)
      fix k assume "\<not> k < k_ktm M"
      hence kge: "k_ktm M \<le> k" by simp
      show "dest_r k = dest_f k" using run_tails fwd_tails kge by simp
    qed

    show ?thesis
      by (rule nae_sim_proto[OF run_q_in_Q step4_sub fwd45 run_c4_state
                                fwd_c4_state run_window fwd_window
                                buf_tail dest_tail
                                step5_sub step6_sub step7_sub step8_sub
                                f_step5 f_step6 f_step7 f_step8
                                sim_c''' gamma_c''])
  qed

  show ?thesis
    by (rule that[OF cM_trace n_bnd halt_or_full ae_sim_c''
                     buf_gamma_c'' le_anchor_c''])
qed


subsubsection \<open>Substep cycle progression\<close>

text \<open>Substep-cycle progression: a single full-delta step from a
  config whose substep idx is \<open>SS1\<close> lands at \<open>SS2\<close>.

  Mechanism: the full \<open>alphabet_enlarge_delta\<close> is the union
  of 16 per-substep deltas, each of whose source tuple fixes the
  substep idx to its own \<open>SS\<langle>N\<rangle>\<close> / validation marker.
  From an \<open>SS1\<close>-source step, only \<open>ae_delta_ss1_ss2\<close>'s
  source matches, which \<open>ktm_step_ae_delta_ss1_only\<close> says at the
  level of steps; the substrate's \<open>ktm_step_states\<close> then hands over
  the tuple's target state, whose idx \<open>ae_delta_ss1_ss2\<close> fixes to
  \<open>SS2\<close>.

  Foundation for the substep-cycle tracking that
  forces \<open>m \<ge> 8\<close> in the reverse chunked-phase induction;
  without this, \<open>m \<in> \<lbrace>1,...,7\<rbrace>\<close>-paths from
  \<open>SS1\<close> can't be ruled out as candidates for reaching
  \<open>VFwd\<close>-halt.\<close>

lemma ae_step_from_SS1_lands_at_SS2:
  fixes M :: "('q, 'a) ktm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                     'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes idx: "snd (snd (snd (snd (ktc_state c')))) = SS1"
      and step: "(c', c'') \<in> ktm_step (alphabet_enlarge_delta M)"
  shows "snd (snd (snd (snd (ktc_state c'')))) = SS2"
proof -
  from step have "(c', c'') \<in> ktm_step (ae_delta_ss1_ss2 M)"
    by (rule ktm_step_ae_delta_ss1_only [OF _ idx])
  then obtain a a' d
    where "(ktc_state c', a, ktc_state c'', a', d) \<in> ae_delta_ss1_ss2 M"
    by (rule ktm_step_states)
  then show ?thesis by (auto simp: ae_delta_ss1_ss2_def)
qed

lemma ae_step_from_SS2_lands_at_SS3:
  fixes M :: "('q, 'a) ktm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                     'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes idx: "snd (snd (snd (snd (ktc_state c')))) = SS2"
      and step: "(c', c'') \<in> ktm_step (alphabet_enlarge_delta M)"
  shows "snd (snd (snd (snd (ktc_state c'')))) = SS3"
proof -
  from step have "(c', c'') \<in> ktm_step (ae_delta_ss2_ss3 M)"
    by (rule ktm_step_ae_delta_ss2_only [OF _ idx])
  then obtain a a' d
    where "(ktc_state c', a, ktc_state c'', a', d) \<in> ae_delta_ss2_ss3 M"
    by (rule ktm_step_states)
  then show ?thesis by (auto simp: ae_delta_ss2_ss3_def)
qed

lemma ae_step_from_SS3_lands_at_SS4:
  fixes M :: "('q, 'a) ktm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                     'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes idx: "snd (snd (snd (snd (ktc_state c')))) = SS3"
      and step: "(c', c'') \<in> ktm_step (alphabet_enlarge_delta M)"
  shows "snd (snd (snd (snd (ktc_state c'')))) = SS4"
proof -
  from step have "(c', c'') \<in> ktm_step (ae_delta_ss3_ss4 M)"
    by (rule ktm_step_ae_delta_ss3_only [OF _ idx])
  then obtain a a' d
    where "(ktc_state c', a, ktc_state c'', a', d) \<in> ae_delta_ss3_ss4 M"
    by (rule ktm_step_states)
  then show ?thesis by (auto simp: ae_delta_ss3_ss4_def)
qed

lemma ae_step_from_SS4_lands_at_SS5:
  fixes M :: "('q, 'a) ktm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                     'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes idx: "snd (snd (snd (snd (ktc_state c')))) = SS4"
      and step: "(c', c'') \<in> ktm_step (alphabet_enlarge_delta M)"
  shows "snd (snd (snd (snd (ktc_state c'')))) = SS5"
proof -
  from step have "(c', c'') \<in> ktm_step (ae_delta_ss4_ss5 M)"
    by (rule ktm_step_ae_delta_ss4_only [OF _ idx])
  then obtain a a' d
    where "(ktc_state c', a, ktc_state c'', a', d) \<in> ae_delta_ss4_ss5 M"
    by (rule ktm_step_states)
  then show ?thesis by (auto simp: ae_delta_ss4_ss5_def)
qed

lemma ae_step_from_SS5_lands_at_SS6:
  fixes M :: "('q, 'a) ktm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                     'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes idx: "snd (snd (snd (snd (ktc_state c')))) = SS5"
      and step: "(c', c'') \<in> ktm_step (alphabet_enlarge_delta M)"
  shows "snd (snd (snd (snd (ktc_state c'')))) = SS6"
proof -
  from step have "(c', c'') \<in> ktm_step (ae_delta_ss5_ss6 M)"
    by (rule ktm_step_ae_delta_ss5_only [OF _ idx])
  then obtain a a' d
    where "(ktc_state c', a, ktc_state c'', a', d) \<in> ae_delta_ss5_ss6 M"
    by (rule ktm_step_states)
  then show ?thesis by (auto simp: ae_delta_ss5_ss6_def)
qed

lemma ae_step_from_SS6_lands_at_SS7:
  fixes M :: "('q, 'a) ktm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                     'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes idx: "snd (snd (snd (snd (ktc_state c')))) = SS6"
      and step: "(c', c'') \<in> ktm_step (alphabet_enlarge_delta M)"
  shows "snd (snd (snd (snd (ktc_state c'')))) = SS7"
proof -
  from step have "(c', c'') \<in> ktm_step (ae_delta_ss6_ss7 M)"
    by (rule ktm_step_ae_delta_ss6_only [OF _ idx])
  then obtain a a' d
    where "(ktc_state c', a, ktc_state c'', a', d) \<in> ae_delta_ss6_ss7 M"
    by (rule ktm_step_states)
  then show ?thesis by (auto simp: ae_delta_ss6_ss7_def)
qed

lemma ae_step_from_SS7_lands_at_SS8:
  fixes M :: "('q, 'a) ktm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                     'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes idx: "snd (snd (snd (snd (ktc_state c')))) = SS7"
      and step: "(c', c'') \<in> ktm_step (alphabet_enlarge_delta M)"
  shows "snd (snd (snd (snd (ktc_state c'')))) = SS8"
proof -
  from step have "(c', c'') \<in> ktm_step (ae_delta_ss7_ss8 M)"
    by (rule ktm_step_ae_delta_ss7_only [OF _ idx])
  then obtain a a' d
    where "(ktc_state c', a, ktc_state c'', a', d) \<in> ae_delta_ss7_ss8 M"
    by (rule ktm_step_states)
  then show ?thesis by (auto simp: ae_delta_ss7_ss8_def)
qed

text \<open>SS8 is the cycle-closure substep: post-state lands at
  \<open>SS1\<close> (steady-state continuation) or \<open>VFwd\<close>
  (halt-branch, when the simulated \<open>M\<close>-state at SS8 is in
  \<open>\<lbrace>t_ktm M, r_ktm M\<rbrace>\<close>).  The looser
  \<open>SS1 \<or> VFwd\<close> disjunction is what the reverse-direction
  chain-progression argument needs; the precise branch resolution
  is handled by \<open>ae_step_ss8_ss1_invariant\<close> /
  \<open>ae_step_ss8_ss1_invariant_halt\<close>.\<close>

lemma ae_step_from_SS8_lands_at_SS1_or_VFwd:
  fixes M :: "('q, 'a) ktm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                     'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes idx: "snd (snd (snd (snd (ktc_state c')))) = SS8"
      and step: "(c', c'') \<in> ktm_step (alphabet_enlarge_delta M)"
  shows "snd (snd (snd (snd (ktc_state c'')))) \<in> {SS1, VFwd}"
proof -
  from step have "(c', c'') \<in> ktm_step (ae_delta_ss8_ss1 M)"
    by (rule ktm_step_ae_delta_ss8_only [OF _ idx])
  then obtain a a' d
    where rel: "(ktc_state c', a, ktc_state c'', a', d) \<in> ae_delta_ss8_ss1 M"
    by (rule ktm_step_states)
  obtain q ofs buf stage' where
      s'_eq: "ktc_state c'' = (q, stage')"
    and stage'_eq: "stage' = (if q \<in> {t_ktm M, r_ktm M}
                                then init_stage (le_ktm M)
                                else (ofs, buf, init_dest, SS1))"
    using rel unfolding ae_delta_ss8_ss1_def by auto
  have init_stage_substep_VFwd:
      "snd (snd (snd (init_stage (le_ktm M) :: ('a, 'c) ae_stage))) = VFwd"
    unfolding init_stage_def by simp
  show ?thesis
  proof (cases "q \<in> {t_ktm M, r_ktm M}")
    case True
    hence stage'_init: "stage' = init_stage (le_ktm M)"
      using stage'_eq by simp
    have "snd (snd (snd (snd (ktc_state c'')))) = VFwd"
      using s'_eq stage'_init init_stage_substep_VFwd by simp
    thus ?thesis by simp
  next
    case False
    hence stage'_cont: "stage' = (ofs, buf, init_dest, SS1)"
      using stage'_eq by simp
    have "snd (snd (snd (snd (ktc_state c'')))) = SS1"
      using s'_eq stage'_cont by simp
    thus ?thesis by simp
  qed
qed


text \<open>Chain-progression: from a config at substep \<open>SS1\<close>,
  no chain of length \<open>1 \<le> m \<le> 7\<close> reaches a configuration
  at substep \<open>VFwd\<close>.  The substep cycle \<open>SS1
  \<rightarrow> SS2 \<rightarrow> ... \<rightarrow> SS8 \<rightarrow>
  SS1 \<or> VFwd\<close> takes exactly 8 steps from \<open>SS1\<close> to
  reach \<open>VFwd\<close>; shorter chains stay within
  \<open>\<lbrace>SS2,...,SS8\<rbrace>\<close>.

  Used by the reverse chunked-phase argument to force \<open>m \<ge>
  8\<close> when an SS1-paired \<open>c'\<close> has a chain ending in the
  canonical halt config \<open>(t_ktm M, init_stage le)\<close>.\<close>

lemma ae_chain_from_SS1_short_not_VFwd:
  fixes M :: "('q, 'a) ktm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                     'q \<times> ('a, 'c) ae_stage) ktc_config"
    and m :: nat
  assumes idx_SS1: "snd (snd (snd (snd (ktc_state c')))) = SS1"
      and m_lt_8:  "0 < m \<and> m < 8"
      and chain:   "(c', c'') \<in> ktm_step (alphabet_enlarge_delta M) ^^ m"
  shows "snd (snd (snd (snd (ktc_state c'')))) \<noteq> VFwd"
proof -
  let ?R = "ktm_step (alphabet_enlarge_delta M)"
  let ?idx = "\<lambda>c. snd (snd (snd (snd (ktc_state c))))"
  consider (m1) "m = 1" | (m2) "m = 2" | (m3) "m = 3" | (m4) "m = 4"
         | (m5) "m = 5" | (m6) "m = 6" | (m7) "m = 7"
    using m_lt_8 by linarith
  thus ?thesis
  proof cases
    case m1
    have step1: "(c', c'') \<in> ?R" using chain m1 by simp
    have "?idx c'' = SS2"
      by (rule ae_step_from_SS1_lands_at_SS2[OF idx_SS1 step1])
    thus ?thesis by simp
  next
    case m2
    from chain m2 obtain c1 where
        e1: "(c', c1) \<in> ?R" and e2: "(c1, c'') \<in> ?R"
      by (auto dest!: relpow_Suc_D2 simp: numeral_eq_Suc)
    have "?idx c1 = SS2"
      by (rule ae_step_from_SS1_lands_at_SS2[OF idx_SS1 e1])
    hence "?idx c'' = SS3"
      by (rule ae_step_from_SS2_lands_at_SS3[OF _ e2])
    thus ?thesis by simp
  next
    case m3
    from chain m3 obtain c1 c2 where
        e1: "(c', c1) \<in> ?R" and e2: "(c1, c2) \<in> ?R"
        and e3: "(c2, c'') \<in> ?R"
      by (auto dest!: relpow_Suc_D2 simp: numeral_eq_Suc)
    have x1: "?idx c1 = SS2"
      by (rule ae_step_from_SS1_lands_at_SS2[OF idx_SS1 e1])
    have x2: "?idx c2 = SS3"
      by (rule ae_step_from_SS2_lands_at_SS3[OF x1 e2])
    hence "?idx c'' = SS4"
      by (rule ae_step_from_SS3_lands_at_SS4[OF _ e3])
    thus ?thesis by simp
  next
    case m4
    from chain m4 obtain c1 c2 c3 where
        e1: "(c', c1) \<in> ?R" and e2: "(c1, c2) \<in> ?R"
        and e3: "(c2, c3) \<in> ?R" and e4: "(c3, c'') \<in> ?R"
      by (auto dest!: relpow_Suc_D2 simp: numeral_eq_Suc)
    have x1: "?idx c1 = SS2"
      by (rule ae_step_from_SS1_lands_at_SS2[OF idx_SS1 e1])
    have x2: "?idx c2 = SS3"
      by (rule ae_step_from_SS2_lands_at_SS3[OF x1 e2])
    have x3: "?idx c3 = SS4"
      by (rule ae_step_from_SS3_lands_at_SS4[OF x2 e3])
    hence "?idx c'' = SS5"
      by (rule ae_step_from_SS4_lands_at_SS5[OF _ e4])
    thus ?thesis by simp
  next
    case m5
    from chain m5 obtain c1 c2 c3 c4 where
        e1: "(c', c1) \<in> ?R" and e2: "(c1, c2) \<in> ?R"
        and e3: "(c2, c3) \<in> ?R" and e4: "(c3, c4) \<in> ?R"
        and e5: "(c4, c'') \<in> ?R"
      by (auto dest!: relpow_Suc_D2 simp: numeral_eq_Suc)
    have x1: "?idx c1 = SS2"
      by (rule ae_step_from_SS1_lands_at_SS2[OF idx_SS1 e1])
    have x2: "?idx c2 = SS3"
      by (rule ae_step_from_SS2_lands_at_SS3[OF x1 e2])
    have x3: "?idx c3 = SS4"
      by (rule ae_step_from_SS3_lands_at_SS4[OF x2 e3])
    have x4: "?idx c4 = SS5"
      by (rule ae_step_from_SS4_lands_at_SS5[OF x3 e4])
    hence "?idx c'' = SS6"
      by (rule ae_step_from_SS5_lands_at_SS6[OF _ e5])
    thus ?thesis by simp
  next
    case m6
    from chain m6 obtain c1 c2 c3 c4 c5 where
        e1: "(c', c1) \<in> ?R" and e2: "(c1, c2) \<in> ?R"
        and e3: "(c2, c3) \<in> ?R" and e4: "(c3, c4) \<in> ?R"
        and e5: "(c4, c5) \<in> ?R" and e6: "(c5, c'') \<in> ?R"
      by (auto dest!: relpow_Suc_D2 simp: numeral_eq_Suc)
    have x1: "?idx c1 = SS2"
      by (rule ae_step_from_SS1_lands_at_SS2[OF idx_SS1 e1])
    have x2: "?idx c2 = SS3"
      by (rule ae_step_from_SS2_lands_at_SS3[OF x1 e2])
    have x3: "?idx c3 = SS4"
      by (rule ae_step_from_SS3_lands_at_SS4[OF x2 e3])
    have x4: "?idx c4 = SS5"
      by (rule ae_step_from_SS4_lands_at_SS5[OF x3 e4])
    have x5: "?idx c5 = SS6"
      by (rule ae_step_from_SS5_lands_at_SS6[OF x4 e5])
    hence "?idx c'' = SS7"
      by (rule ae_step_from_SS6_lands_at_SS7[OF _ e6])
    thus ?thesis by simp
  next
    case m7
    from chain m7 obtain c1 c2 c3 c4 c5 c6 where
        e1: "(c', c1) \<in> ?R" and e2: "(c1, c2) \<in> ?R"
        and e3: "(c2, c3) \<in> ?R" and e4: "(c3, c4) \<in> ?R"
        and e5: "(c4, c5) \<in> ?R" and e6: "(c5, c6) \<in> ?R"
        and e7: "(c6, c'') \<in> ?R"
      by (auto dest!: relpow_Suc_D2 simp: numeral_eq_Suc)
    have x1: "?idx c1 = SS2"
      by (rule ae_step_from_SS1_lands_at_SS2[OF idx_SS1 e1])
    have x2: "?idx c2 = SS3"
      by (rule ae_step_from_SS2_lands_at_SS3[OF x1 e2])
    have x3: "?idx c3 = SS4"
      by (rule ae_step_from_SS3_lands_at_SS4[OF x2 e3])
    have x4: "?idx c4 = SS5"
      by (rule ae_step_from_SS4_lands_at_SS5[OF x3 e4])
    have x5: "?idx c5 = SS6"
      by (rule ae_step_from_SS5_lands_at_SS6[OF x4 e5])
    have x6: "?idx c6 = SS7"
      by (rule ae_step_from_SS6_lands_at_SS7[OF x5 e6])
    hence "?idx c'' = SS8"
      by (rule ae_step_from_SS7_lands_at_SS8[OF _ e7])
    thus ?thesis by simp
  qed
qed


subsubsection \<open>The reverse simulation: dispatch on the substep\<close>

text \<open>Substrate consequence: from reachability of \<open>cM\<close> from
  \<open>init_config_ktm M w\<close>, every \<open>M\<close>-tape cell at any positive
  index along that trace is not the left-end marker \<open>le_ktm M\<close>.
  Packaged as the \<open>no_le_per_tape\<close> conjunct expected by
  \<open>ae_backward_stage\<close> (forward chunked-phase derivation pattern
  at lines 8688+ of \<open>AlphabetEnlargement.thy\<close>).  Factored out
  so the main chunked-reverse induction body stays under
  elaboration budget.\<close>

lemma ae_no_le_per_tape_from_reach:
  fixes M :: "('q, 'a) ktm"
    and w :: "'a list"
    and cM :: "('a, 'q) ktc_config"
    and c' :: "('c :: enum \<Rightarrow> 'a,
                 'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes vM:        "valid_ktm M"
      and lu:        "le_unique M"
      and w_sub:     "set w \<subseteq> Sigma_ktm M"
      and le_neq_bl: "le_ktm M \<noteq> bl_ktm M"
      and reach_M:   "(init_config_ktm M w, cM)
                        \<in> (ktm_step (delta_ktm M))\<^sup>*"
  shows "\<forall>k. (ktc_pos c' k \<ge> 2
                \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                          \<longrightarrow> ktc_tape cM k
                                ((ktc_pos c' k - 2)
                                    * card (UNIV :: 'c set)
                                   + 1 + i)
                              \<noteq> le_ktm M))
             \<and> (ktc_pos c' k = 1
                  \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                            \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))
             \<and> (ktc_pos c' k = 0
                  \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                            \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))"
proof (intro allI conjI impI allI impI)
  fix k :: nat and i :: nat
  assume "2 \<le> ktc_pos c' k"
     and "i < 3 * card (UNIV :: 'c set)"
  have idx_nz:
      "(ktc_pos c' k - 2) * card (UNIV :: 'c set) + 1 + i \<noteq> 0"
    by simp
  show "ktc_tape cM k
          ((ktc_pos c' k - 2) * card (UNIV :: 'c set)
             + 1 + i) \<noteq> le_ktm M"
    using valid_reach_LE_only_pos0_ktm
            [OF vM lu w_sub reach_M idx_nz le_neq_bl[symmetric]] .
next
  fix k :: nat and i :: nat
  assume "ktc_pos c' k = 1"
     and "i < 2 * card (UNIV :: 'c set)"
  have idx_nz: "Suc i \<noteq> 0" by simp
  show "ktc_tape cM k (Suc i) \<noteq> le_ktm M"
    using valid_reach_LE_only_pos0_ktm
            [OF vM lu w_sub reach_M idx_nz le_neq_bl[symmetric]] .
next
  fix k :: nat and i :: nat
  assume "ktc_pos c' k = 0"
     and "i < card (UNIV :: 'c set)"
  have idx_nz: "Suc i \<noteq> 0" by simp
  show "ktc_tape cM k (Suc i) \<noteq> le_ktm M"
    using valid_reach_LE_only_pos0_ktm
            [OF vM lu w_sub reach_M idx_nz le_neq_bl[symmetric]] .
qed


text \<open>Halt-branch contradiction: when \<open>ktc_state c'\<close> is at a
  halt-coerced state \<open>(qM', init_stage le)\<close> with \<open>qM' \<in>
  {t_ktm M, r_ktm M}\<close>, the alphabet-enlarged accept/reject bridges
  identify the configuration's state with \<open>t_ktm M'\<close> /
  \<open>r_ktm M'\<close>, and \<open>ktm_step_src_neq_t\<close> /
  \<open>ktm_step_src_neq_r\<close> rule out any outgoing step.  Factored
  out so the chunked-reverse induction body's halt-branch
  dispatch is a single \<open>have False ...\<close>.\<close>

lemma ae_halt_c'_no_step:
  fixes M :: "('q, 'a) ktm"
    and qM' :: 'q
    and c' c'' :: "(('c :: enum) \<Rightarrow> 'a,
                     'q \<times> ('a, 'c) ae_stage) ktc_config"
  assumes vM:        "valid_ktm M"
      and qM_in_tr:  "qM' \<in> {t_ktm M, r_ktm M}"
      and state_c':  "ktc_state c' = (qM', init_stage (le_ktm M))"
      and step:      "(c', c'')
                          \<in> ktm_step (alphabet_enlarge_delta M)"
  shows "False"
proof -
  let ?M' = "alphabet_enlarge M
               :: ('q \<times> ('a, 'c) ae_stage,
                   'c \<Rightarrow> 'a) ktm"
  have valM': "valid_ktm ?M'"
    by (rule alphabet_enlarge_wf[OF vM])
  have step_M': "(c', c'') \<in> ktm_step (delta_ktm ?M')"
    using step by (simp add: delta_ktm_alphabet_enlarge)
  from qM_in_tr have qM_cases: "qM' = t_ktm M \<or> qM' = r_ktm M"
    by blast
  thus False
  proof
    assume "qM' = t_ktm M"
    hence "ktc_state c' = t_ktm ?M'"
      using state_c' by (simp add: t_ktm_alphabet_enlarge)
    thus False using ktm_step_src_neq_t[OF valM' step_M']
      by simp
  next
    assume "qM' = r_ktm M"
    hence "ktc_state c' = r_ktm ?M'"
      using state_c' by (simp add: r_ktm_alphabet_enlarge)
    thus False using ktm_step_src_neq_r[OF valM' step_M']
      by simp
  qed
qed


subsubsection \<open>The reverse simulation, one stage at a time, and the language\<close>

text \<open>Chunked-induction engine for the reverse direction.  Given a
  finite \<open>M'\<close>-chain \<open>(c', c_acc)\<close> of length \<open>m\<close> ending in the
  canonical halt configuration \<open>(t_ktm M, init_stage le)\<close>, plus an
  \<open>ae_simulates\<close> invariant at \<open>c'\<close> with the standard side-band
  invariants \<open>buf_gamma\<close> and \<open>le_anchor\<close>, deliver an accepting
  \<open>M\<close>-path from \<open>cM\<close>.  Mirror of \<open>ae_simulation_phase_chunked\<close>
  (forward) but inducting on the \<open>M'\<close>-side chain length rather
  than the \<open>M\<close>-side: at each level we peel 8 \<open>M'\<close>-steps via
  \<open>ae_backward_stage\<close> and recurse.

  Three induction cases:
   \<open>\<bullet>\<close>\<open>m = 0\<close> base: \<open>c' = c_acc\<close>; the simulation's accept
     correspondence forces \<open>ktc_state cM = t_ktm M\<close>.
   \<open>\<bullet>\<close>\<open>0 < m < 8\<close>: contradiction via
     \<open>ae_chain_from_SS1_short_not_VFwd\<close> (or trivial substep
     mismatch when \<open>c' = c_acc\<close>'s sister case applies).
   \<open>\<bullet>\<close>\<open>m \<ge> 8\<close> peel: split \<open>m = 8 + (m - 8)\<close> via \<open>relpow_add\<close>,
     apply \<open>ae_backward_stage\<close> to the first chunk, IH on \<open>m - 8\<close>.

  The conclusion is in \<open>rtrancl\<close> form (the \<open>n_M\<close> step counter
  is forgotten via \<open>relpow_imp_rtrancl\<close>) to ease the downstream
  \<open>Lang_ktm\<close>-repacking in \<open>alphabet_enlarge_language\<close>.\<close>

lemma ae_simulation_phase_chunked_reverse:
  fixes M :: "('q, 'a) ktm"
    and w :: "'a list"
    and cM :: "('a, 'q) ktc_config"
    and c' c_acc :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) ktc_config"
    and m :: nat
  assumes vM:         "valid_ktm M"
      and lu:         "le_unique M"
      and w_sub:      "set w \<subseteq> Sigma_ktm M"
      and le_neq_bl:  "le_ktm M \<noteq> bl_ktm M"
      and reach_M:    "(init_config_ktm M w, cM)
                          \<in> (ktm_step (delta_ktm M))\<^sup>*"
      and trace:      "(c', c_acc)
                          \<in> ktm_step (alphabet_enlarge_delta M) ^^ m"
      and accept:     "ktc_state c_acc
                          = (t_ktm M, init_stage (le_ktm M))"
      and sim:        "ae_simulates M cM c'"
      and buf_gamma:  "ae_buffer_in_gamma_block M c'"
      and le_anchor:  "\<forall>kk<k_ktm M. ktc_tape c' kk 0 = LE_block (le_ktm M)"
  shows "\<exists>cM_final. (cM, cM_final) \<in> (ktm_step (delta_ktm M))\<^sup>*
                    \<and> ktc_state cM_final = t_ktm M"
  using reach_M trace sim buf_gamma le_anchor
proof (induction m arbitrary: cM c' rule: less_induct)
  case (less m)
  obtain qM' ofs buf dest idx where
      state_c': "ktc_state c' = (qM', ofs, buf, dest, idx)"
    and qM_eq:   "ktc_state cM = qM'"
    and state_disj: "(idx = SS1 \<and> qM' \<notin> {t_ktm M, r_ktm M})
                     \<or> (qM' \<in> {t_ktm M, r_ktm M}
                         \<and> (ofs, buf, dest, idx)
                             = init_stage (le_ktm M))"
    and "\<forall>k<k_ktm M. ae_tape_correspondence (le_ktm M)
                (ktc_tape cM k) (ktc_tape c' k)"
    and "ae_tape_in_gamma_block M c'"
    by (rule ae_simulates_state_disjunction[OF less.prems(3)])
  consider (halt) "qM' \<in> {t_ktm M, r_ktm M}
                   \<and> (ofs, buf, dest, idx) = init_stage (le_ktm M)"
         | (ss1)  "idx = SS1 \<and> qM' \<notin> {t_ktm M, r_ktm M}"
    using state_disj by blast
  thus ?case
  proof cases
    case halt
    have state_full: "ktc_state c' = (qM', init_stage (le_ktm M))"
      using state_c' halt by simp
    show ?thesis
    proof (cases m)
      case 0
      from less.prems(2) 0 have c'_eq: "c' = c_acc" by simp
      have "ktc_state c' = (t_ktm M, init_stage (le_ktm M))"
        using accept c'_eq by simp
      hence qM_t: "qM' = t_ktm M" using state_full by simp
      have cM_state: "ktc_state cM = t_ktm M" using qM_eq qM_t by simp
      have refl: "(cM, cM) \<in> (ktm_step (delta_ktm M))\<^sup>*" by simp
      show ?thesis using refl cM_state by blast
    next
      case (Suc m')
      have trace_Suc:
          "(c', c_acc) \<in> ktm_step (alphabet_enlarge_delta M)
                              ^^ Suc m'"
        using less.prems(2) Suc by simp
      obtain c'_1 where
          first_step:
              "(c', c'_1) \<in> ktm_step (alphabet_enlarge_delta M)"
        and rest_trace:
              "(c'_1, c_acc) \<in> ktm_step (alphabet_enlarge_delta M)
                                    ^^ m'"
        using relpow_Suc_D2[OF trace_Suc] by blast
      have qM_in_tr: "qM' \<in> {t_ktm M, r_ktm M}" using halt by simp
      have False
        by (rule ae_halt_c'_no_step
                   [OF vM qM_in_tr state_full first_step])
      thus ?thesis by simp
    qed
  next
    case ss1
    from ss1 have idx_SS1: "idx = SS1" by simp
    have idx_snd4: "snd (snd (snd (snd (ktc_state c')))) = SS1"
      using state_c' idx_SS1 by simp
    have qM_neq_t: "ktc_state cM \<noteq> t_ktm M" using qM_eq ss1 by simp
    have qM_neq_r: "ktc_state cM \<noteq> r_ktm M" using qM_eq ss1 by simp
    consider (m_zero) "m = 0"
           | (m_short) "0 < m \<and> m < 8"
           | (m_long) "8 \<le> m"
      by linarith
    thus ?thesis
    proof cases
      case m_zero
      from less.prems(2) m_zero have c'_eq: "c' = c_acc" by simp
      have "ktc_state c' = (t_ktm M, init_stage (le_ktm M))"
        using accept c'_eq by simp
      hence c'_VFwd: "snd (snd (snd (snd (ktc_state c')))) = VFwd"
        unfolding init_stage_def by simp
      from c'_VFwd idx_snd4 have False by simp
      thus ?thesis by simp
    next
      case m_short
      have c_acc_VFwd:
          "snd (snd (snd (snd (ktc_state c_acc)))) = VFwd"
        using accept by (simp add: init_stage_def)
      have not_VFwd:
          "snd (snd (snd (snd (ktc_state c_acc)))) \<noteq> VFwd"
        by (rule ae_chain_from_SS1_short_not_VFwd
                   [OF idx_snd4 m_short less.prems(2)])
      from c_acc_VFwd not_VFwd have False by simp
      thus ?thesis by simp
    next
      case m_long
      define m_rem where "m_rem \<equiv> m - 8"
      have m_split: "m = 8 + m_rem"
        using m_long m_rem_def by simp
      have rem_lt: "m_rem < m"
        using m_long m_rem_def by simp
      from less.prems(2) m_split have trace_compose:
          "(c', c_acc)
              \<in> (ktm_step (alphabet_enlarge_delta M) ^^ 8)
                  O (ktm_step (alphabet_enlarge_delta M) ^^ m_rem)"
        by (simp add: relpow_add)
      obtain c_8 where
          run_8:    "(c', c_8)
                        \<in> ktm_step (alphabet_enlarge_delta M) ^^ 8"
        and rest_8: "(c_8, c_acc)
                        \<in> ktm_step (alphabet_enlarge_delta M) ^^ m_rem"
        using trace_compose by auto
      have val_cM: "valid_config_ktm M cM"
        by (rule valid_reach_ktm[OF vM w_sub less.prems(1)])
      have no_le_per_tape:
          "\<forall>k. (ktc_pos c' k \<ge> 2
                  \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                            \<longrightarrow> ktc_tape cM k
                                  ((ktc_pos c' k - 2)
                                      * card (UNIV :: 'c set)
                                     + 1 + i)
                                \<noteq> le_ktm M))
               \<and> (ktc_pos c' k = 1
                    \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                              \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))
               \<and> (ktc_pos c' k = 0
                    \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                              \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))"
        by (rule ae_no_le_per_tape_from_reach
                   [OF vM lu w_sub le_neq_bl less.prems(1)])
      obtain cM_new n_M where
          cM_run:    "(cM, cM_new) \<in> ktm_step (delta_ktm M) ^^ n_M"
        and n_M_le:   "n_M \<le> card (UNIV :: 'c set)"
        and end_disj: "n_M = card (UNIV :: 'c set)
                          \<or> ktc_state cM_new \<in> {t_ktm M, r_ktm M}"
        and sim_new:  "ae_simulates M cM_new c_8"
        and buf_new:  "ae_buffer_in_gamma_block M c_8"
        and le_new:   "\<forall>kk<k_ktm M. ktc_tape c_8 kk 0 = LE_block (le_ktm M)"
        by (rule ae_backward_stage[OF vM lu less.prems(3) val_cM
                                       qM_neq_t qM_neq_r
                                       less.prems(4) less.prems(5)
                                       le_neq_bl no_le_per_tape run_8])
      have cM_to_new_star: "(cM, cM_new) \<in> (ktm_step (delta_ktm M))\<^sup>*"
        using cM_run by (rule relpow_imp_rtrancl)
      have reach_cM_new: "(init_config_ktm M w, cM_new)
                            \<in> (ktm_step (delta_ktm M))\<^sup>*"
        using less.prems(1) cM_to_new_star by (rule rtrancl_trans)
      obtain cM_final where
          rest_run:  "(cM_new, cM_final)
                         \<in> (ktm_step (delta_ktm M))\<^sup>*"
        and acc_final: "ktc_state cM_final = t_ktm M"
        using less.IH[OF rem_lt reach_cM_new rest_8 sim_new
                          buf_new le_new]
        by blast
      have cM_to_final:
          "(cM, cM_final) \<in> (ktm_step (delta_ktm M))\<^sup>*"
        using cM_to_new_star rest_run by (rule rtrancl_trans)
      show ?thesis using cM_to_final acc_final by blast
    qed
  qed
qed



text \<open>Language-equivalence statement (biconditional) for every
  well-formed \<open>M\<close> --- \<^emph>\<open>with no determinism hypothesis\<close>.
  Pairs with the forward inclusion
  \<open>alphabet_enlarge_language_forward\<close> in
  \<open>AlphabetEnlargement.thy\<close>: this theorem combines that
  forward leg with a determinism-free reverse leg.

  Both legs assume only \<open>well_formed_ktm M\<close>.  The forward leg
  is unconditional in \<open>M\<close>'s determinism by construction.  The
  reverse leg originally required \<open>det_ktm M\<close>: the natural
  route identifies the post-validation point by chain uniqueness
  of \<open>alphabet_enlarge_delta\<close>
  (\<open>ktm_step_alphabet_enlarge_relpow_functional\<close>), which a
  nondeterministic \<open>M\<close> does not supply --- its compute substep
  is multi-valued, so that full chain is not unique.  The
  refactoring removed the dependency.  The validation prefix is
  pinned instead by the \<^emph>\<open>validation-phase\<close> uniqueness
  \<open>ktm_step_alphabet_enlarge_val_relpow_functional\<close> (the AE
  bookkeeping is deterministic whatever \<open>M\<close> does), and the
  single determinism-supplied step in \<open>ae_backward_stage\<close> ---
  the SS4\<open>\<rightarrow>\<close>SS5 identification --- is replaced by the
  unconditional window-inversion kernel (\<open>bp_linear\<close>
  injectivity plus buffer-window inversion; the \<open>det\<close>-free
  SS5\<open>\<rightarrow>\<close>SS8 kernel above), with the remainder discharged by
  \<open>ae_simulation_phase_chunked_reverse\<close>.  The biconditional
  therefore holds for nondeterministic \<open>M\<close> as well, which is
  what the nondeterministic corollary \<open>alphabet_enlarge_nae\<close>
  packages with the time bound.  The Hopcroft--Ullman
  linear-speedup corollaries
  \<^cite>\<open>\<open>Theorems 12.3, 12.4\<close> in "Hopcroft1979:introduction"\<close>
  reinstate \<open>det_ktm M\<close> only for the same-alphabet wrap, not for this
  biconditional.\<close>

theorem alphabet_enlarge_language:
  fixes M :: "('q, 'a) ktm"
  assumes wf:        "well_formed_ktm M"
  shows "\<forall>w. set w \<subseteq> Sigma_ktm M
              \<longrightarrow> (encode_input (bl_ktm M) w \<in> Lang_ktm
                      (alphabet_enlarge M
                         :: ('q \<times> ('a, ('c :: enum)) ae_stage,
                             'c \<Rightarrow> 'a) ktm))
                  = (w \<in> Lang_ktm M)"
proof -
  from wf have vM:        "valid_ktm M"
           and lu:        "le_unique M"
           and s_neq_t:   "s_ktm M \<noteq> t_ktm M"
           and s_neq_r:   "s_ktm M \<noteq> r_ktm M"
           and le_neq_bl: "le_ktm M \<noteq> bl_ktm M"
    by auto

  let ?M' = "alphabet_enlarge M
               :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) ktm"

  have fwd: "\<forall>w. set w \<subseteq> Sigma_ktm M
                  \<longrightarrow> w \<in> Lang_ktm M
                  \<longrightarrow> encode_input (bl_ktm M) w \<in> Lang_ktm ?M'"
    by (rule alphabet_enlarge_language_forward[OF wf])

  show ?thesis
  proof (intro allI impI)
    fix w :: "'a list"
    assume w_sub: "set w \<subseteq> Sigma_ktm M"
    show "(encode_input (bl_ktm M) w \<in> Lang_ktm ?M')
            = (w \<in> Lang_ktm M)"
    proof
      assume w_in_M: "w \<in> Lang_ktm M"
      from fwd w_sub w_in_M
      show "encode_input (bl_ktm M) w \<in> Lang_ktm ?M'"
        by blast
    next
      \<comment> \<open>Reverse direction: \<open>encode_input w \<in> Lang_ktm M'\<close>
          \<open>\<Longrightarrow>\<close> \<open>w \<in> Lang_ktm M\<close>.

          Strategy: unpack the \<open>M'\<close>-accepting trace; peel
          validation via the strengthened
          \<open>ae_validation_post_state_canonical\<close>; identify
          the post-validation point on the trace via
          validation-phase chain uniqueness
          (\<open>ktm_step_alphabet_enlarge_val_relpow_functional\<close>,
          \<open>det\<close>-free); invoke
          \<open>ae_simulation_phase_chunked_reverse\<close> on the
          remainder; repack the resulting M-trace as
          \<open>Lang_ktm M\<close>.\<close>
      assume enc_in_M':
          "encode_input (bl_ktm M) w \<in> Lang_ktm ?M'"
      \<comment> \<open>Step 1: Unpack the M'-acceptance.\<close>
      from enc_in_M' obtain wM' nM' where
          acc_path_M':
            "(init_config_ktm ?M' (encode_input (bl_ktm M) w),
              KConfig (t_ktm ?M') wM' nM')
                \<in> (ktm_step (delta_ktm ?M'))\<^sup>*"
        unfolding Lang_ktm_def by blast
      define c_acc :: "('c \<Rightarrow> 'a, 'q \<times> ('a, 'c) ae_stage)
                          ktc_config"
        where "c_acc \<equiv> KConfig (t_ktm ?M') wM' nM'"
      \<comment> \<open>Step 2: Bridge \<open>?M'\<close> components to AE-side and
          convert rtrancl to relpow.\<close>
      have c_acc_state:
          "ktc_state c_acc = (t_ktm M, init_stage (le_ktm M))"
        unfolding c_acc_def by (simp add: t_ktm_alphabet_enlarge)
      have acc_path_AE:
          "(ae_init_config M (encode_input (bl_ktm M) w), c_acc)
              \<in> (ktm_step (alphabet_enlarge_delta M))\<^sup>*"
        using acc_path_M'
        by (simp add: init_config_alphabet_enlarge
                      delta_ktm_alphabet_enlarge c_acc_def)
      obtain N where acc_pow:
          "(ae_init_config M (encode_input (bl_ktm M) w), c_acc)
              \<in> ktm_step (alphabet_enlarge_delta M) ^^ N"
        using acc_path_AE rtrancl_imp_relpow by metis
      \<comment> \<open>Step 3: Peel validation.  Explicit type annotation
          on \<open>c'_post\<close> to share \<open>'c\<close> with \<open>c_acc\<close> (the
          validation-peel lemma is polymorphic over \<open>'c\<close>;
          without the annotation Isabelle freshens).\<close>
      obtain n_val and c'_post :: "('c \<Rightarrow> 'a,
                                     'q \<times> ('a, 'c) ae_stage) ktc_config" where
          val_run:    "(ae_init_config M (encode_input (bl_ktm M) w),
                        c'_post)
                          \<in> ktm_step (alphabet_enlarge_delta M)
                                  ^^ n_val"
        and val_sim:  "ae_simulates M (init_config_ktm M w) c'_post"
        and val_buf:  "ae_buffer_in_gamma_block M c'_post"
        and val_le:   "\<forall>kk<k_ktm M. ktc_tape c'_post kk 0 = LE_block (le_ktm M)"
        and val_reach:
              "\<forall>i<n_val. \<forall>d :: ('c \<Rightarrow> 'a,
                                  'q \<times> ('a, 'c) ae_stage) ktc_config.
                  (ae_init_config M (encode_input (bl_ktm M) w), d)
                      \<in> ktm_step (alphabet_enlarge_delta M) ^^ i
                    \<longrightarrow> snd (snd (snd (snd (ktc_state d))))
                          \<in> {VFwd, VFwdPad, VRet}"
        by (rule ae_validation_post_state_canonical
                   [OF vM w_sub le_neq_bl])
      \<comment> \<open>Step 4: Identify chain remainder.  By
          \<open>ktm_step_alphabet_enlarge_val_relpow_functional\<close> the
          validation endpoint sits on the unique chain from
          \<open>ae_init_config\<close> to \<open>c_acc\<close>.  Two cases on
          \<open>n_val\<close> vs \<open>N\<close>:
           \<open>\<bullet>\<close> \<open>n_val \<le> N\<close>: extract remainder
              \<open>(c'_post, c_acc) \<in> step ^^ (N - n_val)\<close>.
           \<open>\<bullet>\<close> \<open>n_val > N\<close>: contradiction — a step from
              \<open>c_acc\<close> is impossible since
              \<open>ktc_state c_acc = t_ktm M'\<close>.\<close>
      have n_val_le_N: "n_val \<le> N"
      proof (rule ccontr)
        assume "\<not> n_val \<le> N"
        hence N_lt: "N < n_val" by simp
        have sum_eq: "N + (n_val - N) = n_val"
          using N_lt by simp
        have val_run_combined:
            "(ae_init_config M (encode_input (bl_ktm M) w), c'_post)
                \<in> ktm_step (alphabet_enlarge_delta M)
                      ^^ (N + (n_val - N))"
          using val_run sum_eq by simp
        hence val_compose:
            "(ae_init_config M (encode_input (bl_ktm M) w), c'_post)
                \<in> (ktm_step (alphabet_enlarge_delta M) ^^ N)
                    O (ktm_step (alphabet_enlarge_delta M)
                          ^^ (n_val - N))"
          by (simp add: relpow_add)
        obtain c_mid where
            step_to_mid:
              "(ae_init_config M (encode_input (bl_ktm M) w), c_mid)
                  \<in> ktm_step (alphabet_enlarge_delta M) ^^ N"
          and step_from_mid:
              "(c_mid, c'_post)
                  \<in> ktm_step (alphabet_enlarge_delta M)
                        ^^ (n_val - N)"
          using val_compose by auto
        have inv_N: "\<forall>i<N. \<forall>d :: ('c \<Rightarrow> 'a,
                                    'q \<times> ('a, 'c) ae_stage) ktc_config.
                        (ae_init_config M (encode_input (bl_ktm M) w), d)
                            \<in> ktm_step (alphabet_enlarge_delta M) ^^ i
                          \<longrightarrow> snd (snd (snd (snd (ktc_state d))))
                                \<in> {VFwd, VFwdPad, VRet}"
          using val_reach N_lt by (meson less_trans)
        have c_mid_eq: "c_mid = c_acc"
          by (rule ktm_step_alphabet_enlarge_val_relpow_functional
                     [OF le_neq_bl step_to_mid acc_pow inv_N])
        have step_from_acc:
            "(c_acc, c'_post)
                \<in> ktm_step (alphabet_enlarge_delta M)
                      ^^ (n_val - N)"
          using step_from_mid c_mid_eq by simp
        have extra_pos: "0 < n_val - N" using N_lt by simp
        obtain m_extra_pred where m_extra_Suc:
            "n_val - N = Suc m_extra_pred"
          using extra_pos by (cases "n_val - N") auto
        have step_from_acc_Suc:
            "(c_acc, c'_post)
                \<in> ktm_step (alphabet_enlarge_delta M)
                      ^^ Suc m_extra_pred"
          using step_from_acc m_extra_Suc by simp
        obtain c_acc_1 where
            first_step:
              "(c_acc, c_acc_1)
                  \<in> ktm_step (alphabet_enlarge_delta M)"
          and rest_step:
              "(c_acc_1, c'_post)
                  \<in> ktm_step (alphabet_enlarge_delta M)
                        ^^ m_extra_pred"
          using relpow_Suc_D2[OF step_from_acc_Suc] by blast
        have valM': "valid_ktm ?M'"
          by (rule alphabet_enlarge_wf[OF vM])
        have first_step_M':
            "(c_acc, c_acc_1) \<in> ktm_step (delta_ktm ?M')"
          using first_step by (simp add: delta_ktm_alphabet_enlarge)
        have c_acc_state_M': "ktc_state c_acc = t_ktm ?M'"
          using c_acc_state by (simp add: t_ktm_alphabet_enlarge)
        from ktm_step_src_neq_t[OF valM' first_step_M']
             c_acc_state_M'
          show False by simp
      qed
      have remainder:
          "(c'_post, c_acc) \<in> ktm_step (alphabet_enlarge_delta M)
                                    ^^ (N - n_val)"
      proof -
        have sum_eq: "n_val + (N - n_val) = N"
          using n_val_le_N by simp
        have "(ae_init_config M (encode_input (bl_ktm M) w), c_acc)
                \<in> ktm_step (alphabet_enlarge_delta M)
                      ^^ (n_val + (N - n_val))"
          using acc_pow sum_eq by simp
        hence acc_compose:
            "(ae_init_config M (encode_input (bl_ktm M) w), c_acc)
                \<in> (ktm_step (alphabet_enlarge_delta M) ^^ n_val)
                    O (ktm_step (alphabet_enlarge_delta M)
                          ^^ (N - n_val))"
          by (simp add: relpow_add)
        obtain c_mid where
            run_to_mid:
              "(ae_init_config M (encode_input (bl_ktm M) w), c_mid)
                  \<in> ktm_step (alphabet_enlarge_delta M) ^^ n_val"
          and run_from_mid:
              "(c_mid, c_acc)
                  \<in> ktm_step (alphabet_enlarge_delta M)
                        ^^ (N - n_val)"
          using acc_compose by auto
        have c_mid_eq: "c_mid = c'_post"
          by (rule ktm_step_alphabet_enlarge_val_relpow_functional
                     [OF le_neq_bl run_to_mid val_run val_reach])
        show ?thesis using run_from_mid c_mid_eq by simp
      qed
      \<comment> \<open>Step 5: Invoke chunked-reverse to extract an M-side
          accepting path.\<close>
      have reach_refl:
          "(init_config_ktm M w, init_config_ktm M w)
              \<in> (ktm_step (delta_ktm M))\<^sup>*"
        by simp
      obtain cM_final where
          M_path:    "(init_config_ktm M w, cM_final)
                          \<in> (ktm_step (delta_ktm M))\<^sup>*"
        and M_acc:    "ktc_state cM_final = t_ktm M"
        using ae_simulation_phase_chunked_reverse
                [OF vM lu w_sub le_neq_bl reach_refl remainder
                    c_acc_state val_sim val_buf val_le]
        by blast
      \<comment> \<open>Step 6: Repack as \<open>w \<in> Lang_ktm M\<close>.\<close>
      obtain wM_acc nM_acc where
          cM_final_eq:
            "cM_final = KConfig (t_ktm M) wM_acc nM_acc"
        using M_acc by (cases cM_final) simp
      show "w \<in> Lang_ktm M"
        unfolding Lang_ktm_def
        using w_sub M_path cM_final_eq by blast
    qed
  qed
qed


subsection \<open>Nondeterministic alphabet enlargement\<close>

text \<open>The determinism-free building block for the nondeterministic
  linear speedup --- the \<^emph>\<open>Form-2\<close> statement (raw, no
  \<open>encoding_wrap\<close>, tape count unchanged, over the enlarged
  alphabet).  For an arbitrary, \<^emph>\<open>possibly nondeterministic\<close>,
  well-formed \<open>M\<close>, the enlargement \<open>alphabet_enlarge M\<close>
  preserves the language (under the \<open>encode_input\<close> block
  map) and the running time, with \<^emph>\<open>no\<close> \<open>det_ktm M\<close>
  hypothesis and \<^emph>\<open>no\<close> \<open>det_ktm\<close>-output conclusion; the
  witness \<open>alphabet_enlarge M\<close> is nondeterministic exactly when
  \<open>M\<close> is.

  Wrapping this in the inline plant-\<open>le\<close> encoder yields the
  same-alphabet nondeterministic speedup corollaries
  \<open>linear_speedup_HU_12_3_nae\<close> / \<open>12_4_nae_B\<close> --- the
  Hopcroft--Ullman page-291 corollary
  \<^cite>\<open>\<open>p.~291\<close> in "Hopcroft1979:introduction"\<close> --- proved in
  \<open>Wrap_Speedup\<close> alongside their deterministic
  counterparts \<open>linear_speedup_HU_12_3_dae\<close> / \<open>12_4_dae_B\<close>,
  which assume \<open>det_ktm M\<close> and additionally conclude output
  determinism via \<open>wrap_det\<close>.\<close>

theorem alphabet_enlarge_nae:
  fixes M :: "('q, 'a) ktm"
    and T :: "nat \<Rightarrow> nat"
  assumes wf: "well_formed_ktm M"
  obtains \<alpha> f :: nat
  where "\<forall>w. set w \<subseteq> Sigma_ktm M
              \<longrightarrow> (encode_input (bl_ktm M) w \<in> Lang_ktm
                      (alphabet_enlarge M
                         :: ('q \<times> ('a, ('c :: enum)) ae_stage,
                             'c \<Rightarrow> 'a) ktm))
                  = (w \<in> Lang_ktm M)"
    and "\<forall>w. set w \<subseteq> Sigma_ktm M
              \<longrightarrow> accepts_in_time_ktm M w (T (length w))
              \<longrightarrow> accepts_in_time_ktm
                    (alphabet_enlarge M
                       :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) ktm)
                    (encode_input (bl_ktm M) w)
                    (\<alpha> * ((length w + card (UNIV :: 'c set) - 1)
                            div card (UNIV :: 'c set))
                     + 8 * ((T (length w) + card (UNIV :: 'c set) - 1)
                             div card (UNIV :: 'c set))
                     + f)"
proof -
  have lang:
    "\<forall>w. set w \<subseteq> Sigma_ktm M
            \<longrightarrow> (encode_input (bl_ktm M) w \<in> Lang_ktm
                    (alphabet_enlarge M
                       :: ('q \<times> ('a, ('c :: enum)) ae_stage,
                           'c \<Rightarrow> 'a) ktm))
                = (w \<in> Lang_ktm M)"
    by (rule alphabet_enlarge_language[OF wf])
  obtain \<alpha> f :: nat where time:
    "\<forall>w. set w \<subseteq> Sigma_ktm M
            \<longrightarrow> accepts_in_time_ktm M w (T (length w))
            \<longrightarrow> accepts_in_time_ktm
                  (alphabet_enlarge M
                     :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) ktm)
                  (encode_input (bl_ktm M) w)
                  (\<alpha> * ((length w + card (UNIV :: 'c set) - 1)
                          div card (UNIV :: 'c set))
                   + 8 * ((T (length w) + card (UNIV :: 'c set) - 1)
                           div card (UNIV :: 'c set))
                   + f)"
    by (rule alphabet_enlarge_time[OF wf])
  show ?thesis by (rule that[OF lang time])
qed


end
