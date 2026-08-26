theory AlphabetEnlargement_Window
  imports AlphabetEnlargement_BufferArith
begin

subsection \<open>Window-invariant single-step preservation\<close>

text \<open>Steady-regime window-invariant preservation under one
  buffered \<open>M\<close>-step.  Takes the IH-side invariant
  \<open>ae_window_invariant tM nM bp blocks p_start\<close>, the buffered
  head advance \<open>bp_advance_le le (tM nM) bp d = Some bp'\<close>, the
  position bounds excluding \<open>bp_advance\<close>'s None cases
  (\<open>bp_linear < 3c - 1\<close> for R, \<open>0 < bp_linear\<close> for L), and
  a no-LE-at-head fact (\<open>tM nM \<noteq> le\<close>) excluding
  \<open>bp_advance_le\<close>'s LE-jump.  Produces the new invariant for
  the parallel tape fun-update and buffer \<open>write_bp\<close>.

  In the steady regime (\<open>pos \<ge> 2\<close>) the no-LE precondition is
  forced by the regime's no-LE window: the buffered head's
  \<open>nM = p_start + bp_linear bp\<close> lies inside the no-LE
  window \<open>[p_start, p_start + 3c - 1]\<close>, so \<open>tM nM \<noteq> le\<close>.

  Used by the Suc case of \<open>ae_coupled_run_aux_general\<close> to
  discharge conjunct 2 in the \<open>pos \<ge> 2\<close> regime.\<close>

lemma ae_window_invariant_step:
  fixes le a' :: 'a
    and tM :: "nat \<Rightarrow> 'a"
    and nM p_start :: nat
    and bp bp' :: "('c :: enum) bp"
    and blocks :: "('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and d :: dir
  assumes wi:     "ae_window_invariant tM nM bp blocks p_start"
      and adv:    "bp_advance_le le (tM nM) bp d = Some bp'"
      and bp_lt:  "bp_linear bp < 3 * card (UNIV :: 'c set) - 1"
      and bp_pos: "0 < bp_linear bp"
      and no_le:  "tM nM \<noteq> le"
  shows "ae_window_invariant
            (tM(nM := a')) (go_dir d nM)
            bp' (write_bp blocks bp a') p_start"
proof -
  let ?c = "card (UNIV :: 'c set)"
  from wi have p_start_ge: "p_start \<ge> 1"
    unfolding ae_window_invariant_def by simp
  from wi have head_corr: "nM = p_start + bp_linear bp"
    unfolding ae_window_invariant_def by simp
  from wi have win_eq:
      "\<forall>i. i < 3 * ?c \<longrightarrow> tM (p_start + i) = buf_lin_at blocks i"
    unfolding ae_window_invariant_def by simp
  \<comment> \<open>The LE-jump in \<open>bp_advance_le\<close> doesn't fire because
    \<open>tM nM \<noteq> le\<close>; so \<open>adv\<close> collapses to a plain
    \<open>bp_advance\<close>.\<close>
  have adv_plain: "bp_advance bp d = Some bp'"
  proof -
    from no_le have "\<not> (tM nM = le \<and> fst bp = AE_Home \<and> d = dir.R)"
      by simp
    hence "bp_advance_le le (tM nM) bp d = bp_advance bp d"
      unfolding bp_advance_le_def by auto
    with adv show ?thesis by simp
  qed
  \<comment> \<open>Head-position correspondence under the step: case-split on
    direction.  N keeps \<open>bp\<close>, R increments \<open>bp_linear\<close>, L
    decrements (needs \<open>nM \<ge> 1\<close>, supplied by
    \<open>p_start_ge\<close>).\<close>
  have head_new: "go_dir d nM = p_start + bp_linear bp'"
  proof (cases d)
    case N
    from adv_plain N have "Some bp' = Some bp"
      using bp_advance_N_some[of bp] by simp
    hence bp'_eq: "bp' = bp" by simp
    show ?thesis using N bp'_eq head_corr by simp
  next
    case R
    from adv_plain R have adv_R: "bp_advance bp dir.R = Some bp'" by simp
    have lin_R: "bp_linear bp' = Suc (bp_linear bp)"
      by (rule bp_advance_R_linear[OF adv_R])
    show ?thesis using R lin_R head_corr by simp
  next
    case L
    from adv_plain L have adv_L: "bp_advance bp dir.L = Some bp'" by simp
    have lin_L: "Suc (bp_linear bp') = bp_linear bp"
      by (rule bp_advance_L_linear[OF adv_L])
    have nM_form: "nM = Suc (p_start + bp_linear bp')"
      using head_corr lin_L by simp
    show ?thesis using L nM_form by simp
  qed
  \<comment> \<open>Window-content alignment: the only changed cell in the
    M-tape (\<open>nM\<close>) corresponds to the only changed buffer cell
    (the linearised \<open>bp_linear bp\<close>), so the alignment is
    preserved by \<open>buf_lin_at_write_bp_match\<close> at the matching
    index and \<open>buf_lin_at_write_bp_other\<close> elsewhere.\<close>
  have win_new:
      "\<forall>i. i < 3 * ?c \<longrightarrow>
              (tM(nM := a')) (p_start + i)
                = buf_lin_at (write_bp blocks bp a') i"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < 3 * ?c"
    show "(tM(nM := a')) (p_start + i)
            = buf_lin_at (write_bp blocks bp a') i"
    proof (cases "i = bp_linear bp")
      case True
      have pos_eq: "p_start + i = nM" using True head_corr by simp
      have "(tM(nM := a')) (p_start + i) = a'" using pos_eq by simp
      moreover have "buf_lin_at (write_bp blocks bp a') i = a'"
        using True buf_lin_at_write_bp_match[of blocks bp a'] by simp
      ultimately show ?thesis by simp
    next
      case False
      hence pos_neq: "p_start + i \<noteq> nM" using head_corr by simp
      have "(tM(nM := a')) (p_start + i) = tM (p_start + i)"
        using pos_neq by simp
      also have "... = buf_lin_at blocks i" using win_eq i_lt by blast
      also have "... = buf_lin_at (write_bp blocks bp a') i"
        by (rule buf_lin_at_write_bp_other[OF False i_lt, symmetric])
      finally show ?thesis .
    qed
  qed
  show ?thesis
    unfolding ae_window_invariant_def
    using p_start_ge head_new win_new by simp
qed

text \<open>Structural-case equivalence for the \<open>le1\<close> regime: the
  case-on-\<open>fst bp\<close> head-position constraint in
  \<open>ae_window_invariant_le1\<close> is equivalent to the single algebraic
  relation \<open>Suc (bp_linear bp) = nM + c\<close>.

  Forward direction (\<open>\<Rightarrow>\<close>): case-split on \<open>fst bp\<close>, compute
  \<open>bp_linear\<close> from the case, conclude the algebraic relation.

  Backward direction (\<open>\<Leftarrow>\<close>): given the algebraic relation,
  case-split on \<open>fst bp\<close> and recover the original case-clause
  from \<open>bp_linear\<close>'s known form per case (using
  \<open>c_idx_last\<close> for the \<open>AE_Left\<close> sub-case where the
  algebraic relation forces \<open>snd bp = c_last\<close>).

  Used by \<open>ae_window_invariant_le1_step\<close> to reduce the
  structural-case preservation goal to a single algebraic check,
  avoiding a per-direction-per-block-boundary nested case analysis.\<close>

lemma bp_linear_le1_struct_iff:
  fixes bp :: "('c :: enum) bp"
    and nM :: nat
  shows "(case fst bp of
            AE_Left  \<Rightarrow> snd bp = c_last \<and> nM = 0
          | AE_Home  \<Rightarrow> nM = Suc (c_idx (snd bp))
          | AE_Right \<Rightarrow> nM = Suc (card (UNIV :: 'c set)
                                  + c_idx (snd bp)))
        \<longleftrightarrow> Suc (bp_linear bp) = nM + card (UNIV :: 'c set)"
proof -
  let ?c = "card (UNIV :: 'c set)"
  have idx_lt: "c_idx (snd bp) < ?c" by (rule c_idx_lt_card)
  show ?thesis
  proof (cases "fst bp")
    case AE_Left
    have lin_eq: "bp_linear bp = c_idx (snd bp)"
      using AE_Left by (cases bp) simp
    show ?thesis
    proof
      assume "case fst bp of
                AE_Left  \<Rightarrow> snd bp = c_last \<and> nM = 0
              | AE_Home  \<Rightarrow> nM = Suc (c_idx (snd bp))
              | AE_Right \<Rightarrow> nM = Suc (?c + c_idx (snd bp))"
      with AE_Left have snd_eq: "snd bp = c_last" and nM_eq: "nM = 0" by auto
      have "c_idx (snd bp) = ?c - 1" using snd_eq c_idx_last by simp
      thus "Suc (bp_linear bp) = nM + ?c"
        using lin_eq nM_eq idx_lt by simp
    next
      assume "Suc (bp_linear bp) = nM + ?c"
      hence "Suc (c_idx (snd bp)) = nM + ?c" using lin_eq by simp
      hence nM_zero: "nM = 0"
        using idx_lt by linarith
      with \<open>Suc (c_idx (snd bp)) = nM + ?c\<close>
      have idx_eq: "c_idx (snd bp) = ?c - 1" using idx_lt by simp
      have c_idx_last_eq: "c_idx (c_last :: 'c) = ?c - 1"
        by (rule c_idx_last)
      have idx_at: "c_idx (snd bp) = c_idx (c_last :: 'c)"
        using idx_eq c_idx_last_eq by simp
      hence snd_eq: "snd bp = c_last"
        by (metis c_idx_in_range(2))
      show "case fst bp of
              AE_Left  \<Rightarrow> snd bp = c_last \<and> nM = 0
            | AE_Home  \<Rightarrow> nM = Suc (c_idx (snd bp))
            | AE_Right \<Rightarrow> nM = Suc (?c + c_idx (snd bp))"
        using AE_Left snd_eq nM_zero by simp
    qed
  next
    case AE_Home
    have lin_eq: "bp_linear bp = ?c + c_idx (snd bp)"
      using AE_Home by (cases bp) simp
    show ?thesis
    proof
      assume "case fst bp of
                AE_Left  \<Rightarrow> snd bp = c_last \<and> nM = 0
              | AE_Home  \<Rightarrow> nM = Suc (c_idx (snd bp))
              | AE_Right \<Rightarrow> nM = Suc (?c + c_idx (snd bp))"
      with AE_Home have nM_eq: "nM = Suc (c_idx (snd bp))" by simp
      thus "Suc (bp_linear bp) = nM + ?c" using lin_eq by simp
    next
      assume "Suc (bp_linear bp) = nM + ?c"
      hence "Suc (?c + c_idx (snd bp)) = nM + ?c" using lin_eq by simp
      hence "nM = Suc (c_idx (snd bp))" by simp
      thus "case fst bp of
              AE_Left  \<Rightarrow> snd bp = c_last \<and> nM = 0
            | AE_Home  \<Rightarrow> nM = Suc (c_idx (snd bp))
            | AE_Right \<Rightarrow> nM = Suc (?c + c_idx (snd bp))"
        using AE_Home by simp
    qed
  next
    case AE_Right
    have lin_eq: "bp_linear bp = 2 * ?c + c_idx (snd bp)"
      using AE_Right by (cases bp) simp
    show ?thesis
    proof
      assume "case fst bp of
                AE_Left  \<Rightarrow> snd bp = c_last \<and> nM = 0
              | AE_Home  \<Rightarrow> nM = Suc (c_idx (snd bp))
              | AE_Right \<Rightarrow> nM = Suc (?c + c_idx (snd bp))"
      with AE_Right have nM_eq: "nM = Suc (?c + c_idx (snd bp))" by simp
      thus "Suc (bp_linear bp) = nM + ?c" using lin_eq by simp
    next
      assume "Suc (bp_linear bp) = nM + ?c"
      hence "Suc (2 * ?c + c_idx (snd bp)) = nM + ?c" using lin_eq by simp
      hence "nM = Suc (?c + c_idx (snd bp))" by simp
      thus "case fst bp of
              AE_Left  \<Rightarrow> snd bp = c_last \<and> nM = 0
            | AE_Home  \<Rightarrow> nM = Suc (c_idx (snd bp))
            | AE_Right \<Rightarrow> nM = Suc (?c + c_idx (snd bp))"
        using AE_Right by simp
    qed
  qed
qed

text \<open>\<open>le1\<close>-regime window-invariant preservation under one
  buffered \<open>M\<close>-step.  Takes the IH-side invariant
  \<open>ae_window_invariant_le1 tM nM bp blocks le\<close>, the buffered
  head advance, the position bounds, and the substrate-derived
  facts on \<open>a'\<close> / \<open>d\<close>'s response to the read symbol's
  LE-status: when reading \<open>le\<close>, M writes \<open>le\<close> and moves
  N or R (from \<open>valid_mttm_deltaLE\<close>); when reading
  non-\<open>le\<close>, M doesn't write \<open>le\<close> (from
  \<open>valid_mttm_deltaLE_no_write\<close>'s contrapositive).  Also takes
  a no-LE-in-window precondition (from the IH-side
  \<open>no_le\<close> invariant restricted to the \<open>le1\<close> regime's
  window cells \<open>1..2c\<close>) which forces the LE-jump in
  \<open>bp_advance_le\<close> to never fire.

  Used by the Suc case of \<open>ae_coupled_run_aux_general\<close> to
  discharge conjunct 2 in the \<open>pos = 1\<close> regime.\<close>

lemma ae_window_invariant_le1_step:
  fixes le a' :: 'a
    and tM :: "nat \<Rightarrow> 'a"
    and nM :: nat
    and bp bp' :: "('c :: enum) bp"
    and blocks :: "('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and d :: dir
  assumes wi:        "ae_window_invariant_le1 tM nM bp blocks le"
      and adv:       "bp_advance_le le (tM nM) bp d = Some bp'"
      and bp_lt:     "bp_linear bp < 3 * card (UNIV :: 'c set) - 1"
      and bp_pos:    "0 < bp_linear bp"
      and a_le:      "tM nM = le \<Longrightarrow> a' = le \<and> d \<in> {dir.N, dir.R}"
      and a_not_le:  "tM nM \<noteq> le \<Longrightarrow> a' \<noteq> le"
      and no_le_win: "\<forall>i. 0 < i \<and> i \<le> 2 * card (UNIV :: 'c set)
                              \<longrightarrow> tM i \<noteq> le"
  shows "ae_window_invariant_le1
            (tM(nM := a')) (go_dir d nM)
            bp' (write_bp blocks bp a') le"
proof -
  let ?c = "card (UNIV :: 'c set)"
  from wi have l_LE: "fst blocks = LE_block le"
    unfolding ae_window_invariant_le1_def by simp
  from wi have tM_0: "tM 0 = le"
    unfolding ae_window_invariant_le1_def by simp
  have struct_lin: "Suc (bp_linear bp) = nM + ?c"
  proof -
    have "(case fst bp of
            AE_Left  \<Rightarrow> snd bp = c_last \<and> nM = 0
          | AE_Home  \<Rightarrow> nM = Suc (c_idx (snd bp))
          | AE_Right \<Rightarrow> nM = Suc (?c + c_idx (snd bp)))"
      using wi unfolding ae_window_invariant_le1_def by simp
    thus ?thesis
      using bp_linear_le1_struct_iff[where bp = bp and nM = nM]
      by blast
  qed
  from wi have align:
      "\<forall>i. i < 2 * ?c \<longrightarrow> tM (Suc i) = buf_lin_at blocks (?c + i)"
    unfolding ae_window_invariant_le1_def by simp
  \<comment> \<open>LE-jump never fires in \<open>le1\<close>: at \<open>fst bp = AE_Home\<close>,
    \<open>nM\<close> lies in \<open>{1..c}\<close>, so \<open>tM nM \<noteq> le\<close> by
    \<open>no_le_win\<close>.\<close>
  have not_le_jump: "\<not> (tM nM = le \<and> fst bp = AE_Home \<and> d = dir.R)"
  proof
    assume "tM nM = le \<and> fst bp = AE_Home \<and> d = dir.R"
    hence le_at: "tM nM = le" and fst_home: "fst bp = AE_Home" by auto
    have lin: "bp_linear bp = ?c + c_idx (snd bp)"
      using fst_home by (cases bp) simp
    from struct_lin lin have nM_eq: "nM = Suc (c_idx (snd bp))" by simp
    have idx_lt: "c_idx (snd bp) < ?c" by (rule c_idx_lt_card)
    have nM_bd: "0 < nM \<and> nM \<le> ?c" using nM_eq idx_lt by simp
    hence "tM nM \<noteq> le" using no_le_win by simp
    with le_at show False by simp
  qed
  have adv_plain: "bp_advance bp d = Some bp'"
  proof -
    have "bp_advance_le le (tM nM) bp d = bp_advance bp d"
      using not_le_jump unfolding bp_advance_le_def by auto
    with adv show ?thesis by simp
  qed
  \<comment> \<open>Algebraic post-step relation: \<open>Suc (bp_linear bp') =
    go_dir d nM + c\<close>.  By the equivalence
    \<open>bp_linear_le1_struct_iff\<close> this implies the structural
    case-on-\<open>fst bp'\<close> at \<open>nM' = go_dir d nM\<close>.\<close>
  have struct_new: "Suc (bp_linear bp') = go_dir d nM + ?c"
  proof (cases d)
    case N
    from adv_plain N have "Some bp' = Some bp"
      using bp_advance_N_some[of bp] by simp
    hence bp'_eq: "bp' = bp" by simp
    show ?thesis using N bp'_eq struct_lin by simp
  next
    case R
    from adv_plain R have adv_R: "bp_advance bp dir.R = Some bp'" by simp
    have lin_R: "bp_linear bp' = Suc (bp_linear bp)"
      by (rule bp_advance_R_linear[OF adv_R])
    show ?thesis using R lin_R struct_lin by simp
  next
    case L
    from adv_plain L have adv_L: "bp_advance bp dir.L = Some bp'" by simp
    have lin_L: "Suc (bp_linear bp') = bp_linear bp"
      by (rule bp_advance_L_linear[OF adv_L])
    have nM_pos: "0 < nM"
    proof (rule ccontr)
      assume "\<not> 0 < nM"
      hence "nM = 0" by simp
      hence "tM nM = le" using tM_0 by simp
      with a_le have d_in: "d \<in> {dir.N, dir.R}" by blast
      with L show False by simp
    qed
    obtain m where m_eq: "nM = Suc m" using nM_pos by (cases nM) auto
    have "Suc (Suc (bp_linear bp')) = Suc (bp_linear bp)"
      using lin_L by simp
    also have "... = nM + ?c" using struct_lin by simp
    also have "... = Suc (m + ?c)" using m_eq by simp
    finally have lhs_eq: "Suc (bp_linear bp') = m + ?c" by simp
    have rhs_eq: "go_dir dir.L nM = m" using m_eq by simp
    show ?thesis using L lhs_eq rhs_eq by simp
  qed
  have struct_post:
      "(case fst bp' of
          AE_Left  \<Rightarrow> snd bp' = c_last \<and> go_dir d nM = 0
        | AE_Home  \<Rightarrow> go_dir d nM = Suc (c_idx (snd bp'))
        | AE_Right \<Rightarrow> go_dir d nM = Suc (?c + c_idx (snd bp')))"
    using struct_new
          bp_linear_le1_struct_iff[where bp = bp' and nM = "go_dir d nM"]
    by blast
  \<comment> \<open>Window-content alignment over \<open>{1..2c} \<leftrightarrow> {c..3c-1}\<close>:
    the write lands at buffer index \<open>bp_linear bp\<close>; if that
    index lies in the alignment range (\<open>?c + i\<close>), the tape
    write at \<open>nM\<close> matches; otherwise both sides unchanged.\<close>
  have align_new:
      "\<forall>i. i < 2 * ?c \<longrightarrow>
              (tM(nM := a')) (Suc i)
                = buf_lin_at (write_bp blocks bp a') (?c + i)"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < 2 * ?c"
    show "(tM(nM := a')) (Suc i)
            = buf_lin_at (write_bp blocks bp a') (?c + i)"
    proof (cases "?c + i = bp_linear bp")
      case True
      hence "Suc (?c + i) = Suc (bp_linear bp)" by simp
      hence "Suc i + ?c = nM + ?c" using struct_lin by simp
      hence Suc_i_eq: "Suc i = nM" by simp
      have lhs: "(tM(nM := a')) (Suc i) = a'" using Suc_i_eq by simp
      have rhs: "buf_lin_at (write_bp blocks bp a') (?c + i) = a'"
        using True buf_lin_at_write_bp_match[of blocks bp a'] by simp
      show ?thesis using lhs rhs by simp
    next
      case False
      hence c_plus_i_neq: "?c + i \<noteq> bp_linear bp" by simp
      have Suc_i_neq: "Suc i \<noteq> nM"
      proof
        assume "Suc i = nM"
        hence "Suc i + ?c = nM + ?c" by simp
        hence "Suc (?c + i) = Suc (bp_linear bp)" using struct_lin by simp
        hence "?c + i = bp_linear bp" by simp
        with c_plus_i_neq show False ..
      qed
      have c_plus_i_lt: "?c + i < 3 * ?c" using i_lt by simp
      have "(tM(nM := a')) (Suc i) = tM (Suc i)" using Suc_i_neq by simp
      also have "... = buf_lin_at blocks (?c + i)" using align i_lt by blast
      also have "... = buf_lin_at (write_bp blocks bp a') (?c + i)"
        by (rule buf_lin_at_write_bp_other
                  [OF c_plus_i_neq c_plus_i_lt, symmetric])
      finally show ?thesis .
    qed
  qed
  \<comment> \<open>First conjunct: \<open>fst (new blocks) = LE_block le\<close>.
    Write site case-split on \<open>fst bp\<close>: in \<open>AE_Left\<close> case
    (forced \<open>snd bp = c_last\<close>, reads \<open>le\<close>, writes \<open>le\<close>)
    the left slot stays \<open>LE_block le\<close>; in \<open>AE_Home\<close> /
    \<open>AE_Right\<close> cases the write doesn't touch the left
    slot.\<close>
  have fst_new: "fst (write_bp blocks bp a') = LE_block le"
  proof (cases "fst bp")
    case AE_Left
    obtain b' off where bp_eq: "bp = (b', off)" by (cases bp)
    have b'_eq: "b' = AE_Left" using AE_Left bp_eq by simp
    have lin_eq: "bp_linear bp = c_idx off" using bp_eq AE_Left by simp
    have idx_lt: "c_idx off < ?c" by (rule c_idx_lt_card)
    from struct_lin lin_eq have suc_eq: "Suc (c_idx off) = nM + ?c" by simp
    have nM_zero: "nM = 0" using suc_eq idx_lt by linarith
    have idx_top: "c_idx off = ?c - 1" using suc_eq nM_zero by linarith
    have c_idx_last_eq: "c_idx (c_last :: 'c) = ?c - 1" by (rule c_idx_last)
    have idx_at: "c_idx off = c_idx (c_last :: 'c)"
      using idx_top c_idx_last_eq by simp
    hence off_eq: "off = c_last" by (metis c_idx_in_range(2))
    have tM_nM_eq: "tM nM = le" using nM_zero tM_0 by simp
    have a'_eq: "a' = le" using a_le tM_nM_eq by blast
    obtain l h r where blocks_eq: "blocks = (l, h, r)"
      by (cases blocks) auto
    have l_eq: "l = LE_block le" using l_LE blocks_eq by simp
    have wb_eq: "write_bp blocks bp a' = (l(off := a'), h, r)"
      using bp_eq b'_eq blocks_eq unfolding write_bp_def by simp
    have "l(off := a') = LE_block le"
    proof -
      have "l(off := a') = (LE_block le)(c_last := le)"
        using l_eq off_eq a'_eq by simp
      also have "... = LE_block le" unfolding LE_block_def by auto
      finally show ?thesis .
    qed
    thus ?thesis using wb_eq by simp
  next
    case AE_Home
    obtain b' off where bp_eq: "bp = (b', off)" by (cases bp)
    have b'_eq: "b' = AE_Home" using AE_Home bp_eq by simp
    obtain l h r where blocks_eq: "blocks = (l, h, r)"
      by (cases blocks) auto
    have wb_eq: "write_bp blocks bp a' = (l, h(off := a'), r)"
      using bp_eq b'_eq blocks_eq unfolding write_bp_def by simp
    show ?thesis using wb_eq l_LE blocks_eq by simp
  next
    case AE_Right
    obtain b' off where bp_eq: "bp = (b', off)" by (cases bp)
    have b'_eq: "b' = AE_Right" using AE_Right bp_eq by simp
    obtain l h r where blocks_eq: "blocks = (l, h, r)"
      by (cases blocks) auto
    have wb_eq: "write_bp blocks bp a' = (l, h, r(off := a'))"
      using bp_eq b'_eq blocks_eq unfolding write_bp_def by simp
    show ?thesis using wb_eq l_LE blocks_eq by simp
  qed
  \<comment> \<open>Second conjunct: \<open>(new tM) 0 = le\<close>.  Either the
    fun-update doesn't touch cell 0 (\<open>nM \<noteq> 0\<close>), or
    \<open>nM = 0\<close> and \<open>a' = le\<close> by the LE-write discipline.\<close>
  have tM_0_new: "(tM(nM := a')) 0 = le"
  proof (cases "nM = 0")
    case True
    have "tM nM = le" using True tM_0 by simp
    hence "a' = le" using a_le by blast
    thus ?thesis using True by simp
  next
    case False
    have "(tM(nM := a')) 0 = tM 0" using False by simp
    thus ?thesis using tM_0 by simp
  qed
  show ?thesis
    unfolding ae_window_invariant_le1_def
    using fst_new tM_0_new struct_post align_new by simp
qed

text \<open>\<open>le0\<close>-regime window-invariant preservation under one
  buffered \<open>M\<close>-step.  Differs from \<open>le1\<close> in that:

  \<open>\<bullet>\<close> the LE block lives in the home slot, not the left slot;
  \<open>\<bullet>\<close> \<open>fst bp = AE_Left\<close> is forbidden by the invariant;
  \<open>\<bullet>\<close> \<open>fst bp = AE_Home\<close> always reads \<open>le\<close> (the whole home
    slot is \<open>LE_block le\<close>) so the LE-jump in
    \<open>bp_advance_le\<close> DOES fire on R from \<open>AE_Home\<close>;
  \<open>\<bullet>\<close> the alignment is only over right-slot cells
    \<open>{1..c} \<leftrightarrow> {2c..3c-1}\<close>.

  Structurally the proof splits on \<open>fst bp\<close>: \<open>AE_Left\<close>
  is closed by contradiction with the invariant; \<open>AE_Home\<close>
  case-splits on \<open>d \<in> {N, R}\<close> (L forbidden by
  \<open>valid_mttm_deltaLE\<close>); \<open>AE_Right\<close> falls through to the
  standard \<open>bp_advance\<close> with displacement \<open>\<pm>1/0\<close> and the
  no-LE precondition rules out the LE-jump.\<close>

lemma ae_window_invariant_le0_step:
  fixes le a' :: 'a
    and tM :: "nat \<Rightarrow> 'a"
    and nM :: nat
    and bp bp' :: "('c :: enum) bp"
    and blocks :: "('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and d :: dir
  assumes wi:        "ae_window_invariant_le0 tM nM bp blocks le"
      and adv:       "bp_advance_le le (tM nM) bp d = Some bp'"
      and bp_lt:     "bp_linear bp < 3 * card (UNIV :: 'c set) - 1"
      and bp_pos:    "0 < bp_linear bp"
      and a_le:      "tM nM = le \<Longrightarrow> a' = le \<and> d \<in> {dir.N, dir.R}"
      and a_not_le:  "tM nM \<noteq> le \<Longrightarrow> a' \<noteq> le"
      and no_le_win: "\<forall>i. 0 < i \<and> i \<le> card (UNIV :: 'c set)
                              \<longrightarrow> tM i \<noteq> le"
  shows "ae_window_invariant_le0
            (tM(nM := a')) (go_dir d nM)
            bp' (write_bp blocks bp a') le"
proof -
  let ?c = "card (UNIV :: 'c set)"
  from wi have h_LE: "fst (snd blocks) = LE_block le"
    unfolding ae_window_invariant_le0_def by simp
  from wi have tM_0: "tM 0 = le"
    unfolding ae_window_invariant_le0_def by simp
  from wi have align:
      "\<forall>i. i < ?c \<longrightarrow> tM (Suc i) = buf_lin_at blocks (2 * ?c + i)"
    unfolding ae_window_invariant_le0_def by simp
  from wi have struct_pre:
      "(case fst bp of
          AE_Home  \<Rightarrow> nM = 0
        | AE_Right \<Rightarrow> nM = Suc (c_idx (snd bp))
        | AE_Left  \<Rightarrow> False)"
    unfolding ae_window_invariant_le0_def by simp
  have not_left: "fst bp \<noteq> AE_Left"
    using struct_pre by (cases "fst bp") auto
  obtain l h r where blocks_eq: "blocks = (l, h, r)"
    by (cases blocks) auto
  have h_eq: "h = LE_block le" using h_LE blocks_eq by simp
  obtain b off where bp_eq: "bp = (b, off)" by (cases bp)
  show ?thesis
  proof (cases b)
    case AE_Left
    with bp_eq not_left show ?thesis by simp
  next
    case AE_Home
    have b_home: "b = AE_Home" using AE_Home .
    from struct_pre bp_eq AE_Home have nM_zero: "nM = 0" by simp
    have tM_nM_le: "tM nM = le" using nM_zero tM_0 by simp
    from a_le tM_nM_le have a'_le: "a' = le"
      and d_in: "d \<in> {dir.N, dir.R}" by auto
    \<comment> \<open>Write-back: \<open>(LE_block le)(off := le) = LE_block le\<close>,
      so the home slot stays \<open>LE_block le\<close>.\<close>
    have wb_eq: "write_bp blocks bp a' = (l, h(off := a'), r)"
      using bp_eq b_home blocks_eq unfolding write_bp_def by simp
    have h_new: "h(off := a') = LE_block le"
      using h_eq a'_le unfolding LE_block_def by auto
    have new_blocks: "write_bp blocks bp a' = (l, LE_block le, r)"
      using wb_eq h_new by simp
    \<comment> \<open>Tape: \<open>tM(0 := le) = tM\<close>.\<close>
    have tM_new: "tM(nM := a') = tM"
      using nM_zero tM_0 a'_le by auto
    show ?thesis
    proof (cases d)
      case N
      from adv N have "bp_advance_le le (tM nM) bp dir.N = Some bp'" by simp
      hence bp'_eq: "bp' = bp"
        unfolding bp_advance_le_def using bp_advance_N_some[of bp] by auto
      have go_dir_N: "go_dir dir.N nM = nM" by simp
      show ?thesis
        unfolding ae_window_invariant_le0_def
      proof (intro conjI)
        show "fst (snd (write_bp blocks bp a')) = LE_block le"
          using new_blocks by simp
        show "(tM(nM := a')) 0 = le" using tM_new tM_0 by simp
        show "(case fst bp' of
                AE_Home  \<Rightarrow> go_dir d nM = 0
              | AE_Right \<Rightarrow> go_dir d nM = Suc (c_idx (snd bp'))
              | AE_Left  \<Rightarrow> False)"
          using bp'_eq bp_eq b_home N nM_zero by simp
        show "\<forall>i. i < ?c \<longrightarrow>
                  (tM(nM := a')) (Suc i)
                    = buf_lin_at (write_bp blocks bp a') (2 * ?c + i)"
        proof (intro allI impI)
          fix i
          assume i_lt: "i < ?c"
          have lhs: "(tM(nM := a')) (Suc i) = tM (Suc i)"
            using tM_new by simp
          also have "... = buf_lin_at blocks (2 * ?c + i)"
            using align i_lt by blast
          also have "... = buf_lin_at (l, LE_block le, r) (2 * ?c + i)"
            using h_eq blocks_eq
            unfolding buf_lin_at_def by simp
          also have "... = buf_lin_at (write_bp blocks bp a') (2 * ?c + i)"
            using new_blocks by simp
          finally show "(tM(nM := a')) (Suc i)
                          = buf_lin_at (write_bp blocks bp a') (2 * ?c + i)" .
        qed
      qed
    next
      case R
      \<comment> \<open>LE-jump fires: \<open>bp' = (AE_Right, c_first)\<close>,
        \<open>go_dir R 0 = 1 = Suc (c_idx c_first)\<close>.\<close>
      from adv R tM_nM_le b_home bp_eq
      have bp'_eq: "bp' = (AE_Right, c_first)"
        unfolding bp_advance_le_def by simp
      have nM'_eq: "go_dir dir.R nM = 1" using nM_zero by simp
      have c_idx_first_eq: "c_idx (c_first :: 'c) = 0"
        by (rule c_idx_first)
      show ?thesis
        unfolding ae_window_invariant_le0_def
      proof (intro conjI)
        show "fst (snd (write_bp blocks bp a')) = LE_block le"
          using new_blocks by simp
        show "(tM(nM := a')) 0 = le" using tM_new tM_0 by simp
        show "(case fst bp' of
                AE_Home  \<Rightarrow> go_dir d nM = 0
              | AE_Right \<Rightarrow> go_dir d nM = Suc (c_idx (snd bp'))
              | AE_Left  \<Rightarrow> False)"
          using bp'_eq R nM'_eq c_idx_first_eq by simp
        show "\<forall>i. i < ?c \<longrightarrow>
                  (tM(nM := a')) (Suc i)
                    = buf_lin_at (write_bp blocks bp a') (2 * ?c + i)"
        proof (intro allI impI)
          fix i
          assume i_lt: "i < ?c"
          have "(tM(nM := a')) (Suc i) = tM (Suc i)" using tM_new by simp
          also have "... = buf_lin_at blocks (2 * ?c + i)"
            using align i_lt by blast
          also have "... = buf_lin_at (l, LE_block le, r) (2 * ?c + i)"
            using h_eq blocks_eq unfolding buf_lin_at_def by simp
          also have "... = buf_lin_at (write_bp blocks bp a') (2 * ?c + i)"
            using new_blocks by simp
          finally show "(tM(nM := a')) (Suc i)
                          = buf_lin_at (write_bp blocks bp a') (2 * ?c + i)" .
        qed
      qed
    next
      case L
      with d_in show ?thesis by simp
    qed
  next
    case AE_Right
    have b_right: "b = AE_Right" using AE_Right .
    from struct_pre bp_eq AE_Right
    have nM_form: "nM = Suc (c_idx off)" by simp
    have idx_lt: "c_idx off < ?c" by (rule c_idx_lt_card)
    have nM_bd: "0 < nM \<and> nM \<le> ?c" using nM_form idx_lt by simp
    have tM_nM_ne: "tM nM \<noteq> le" using nM_bd no_le_win by simp
    have a'_ne: "a' \<noteq> le" using a_not_le tM_nM_ne by blast
    \<comment> \<open>LE-jump doesn't fire (\<open>fst bp = AE_Right \<noteq> AE_Home\<close>).
      So \<open>bp_advance_le = bp_advance\<close>.\<close>
    have adv_plain: "bp_advance bp d = Some bp'"
    proof -
      have "\<not> (tM nM = le \<and> fst bp = AE_Home \<and> d = dir.R)"
        using bp_eq b_right by simp
      hence "bp_advance_le le (tM nM) bp d = bp_advance bp d"
        unfolding bp_advance_le_def by auto
      with adv show ?thesis by simp
    qed
    \<comment> \<open>Write-back: writes to right slot, home and left unchanged.\<close>
    have wb_eq: "write_bp blocks bp a' = (l, h, r(off := a'))"
      using bp_eq b_right blocks_eq unfolding write_bp_def by simp
    have new_h: "fst (snd (write_bp blocks bp a')) = LE_block le"
      using wb_eq h_eq by simp
    \<comment> \<open>Tape: cell 0 unchanged (\<open>nM \<ge> 1\<close>).\<close>
    have tM_0_new: "(tM(nM := a')) 0 = le"
      using nM_bd tM_0 by simp
    \<comment> \<open>Alignment under the parallel write: the only updated buffer cell
      is at index \<open>2c + c_idx off = bp_linear bp\<close>; the tape update
      at \<open>nM = Suc (c_idx off)\<close> corresponds.\<close>
    have bp_lin: "bp_linear bp = 2 * ?c + c_idx off"
      using bp_eq b_right by simp
    show ?thesis
    proof (cases d)
      case N
      from adv_plain N have "Some bp' = Some bp"
        using bp_advance_N_some[of bp] by simp
      hence bp'_eq: "bp' = bp" by simp
      show ?thesis
        unfolding ae_window_invariant_le0_def
      proof (intro conjI)
        show "fst (snd (write_bp blocks bp a')) = LE_block le"
          by (rule new_h)
        show "(tM(nM := a')) 0 = le" by (rule tM_0_new)
        show "(case fst bp' of
                AE_Home  \<Rightarrow> go_dir d nM = 0
              | AE_Right \<Rightarrow> go_dir d nM = Suc (c_idx (snd bp'))
              | AE_Left  \<Rightarrow> False)"
          using bp'_eq bp_eq b_right N nM_form by simp
        show "\<forall>i. i < ?c \<longrightarrow>
                  (tM(nM := a')) (Suc i)
                    = buf_lin_at (write_bp blocks bp a') (2 * ?c + i)"
        proof (intro allI impI)
          fix i
          assume i_lt: "i < ?c"
          show "(tM(nM := a')) (Suc i)
                  = buf_lin_at (write_bp blocks bp a') (2 * ?c + i)"
          proof (cases "i = c_idx off")
            case True
            have "Suc i = nM" using True nM_form by simp
            hence lhs: "(tM(nM := a')) (Suc i) = a'" by simp
            have idx_eq: "2 * ?c + i = bp_linear bp"
              using True bp_lin by simp
            have rhs: "buf_lin_at (write_bp blocks bp a') (2 * ?c + i) = a'"
              using idx_eq buf_lin_at_write_bp_match[of blocks bp a'] by simp
            show ?thesis using lhs rhs by simp
          next
            case False
            have idx_neq: "2 * ?c + i \<noteq> bp_linear bp"
              using False bp_lin by simp
            have idx_2c_lt: "2 * ?c + i < 3 * ?c" using i_lt by simp
            have Suc_i_neq: "Suc i \<noteq> nM"
              using False nM_form by simp
            have "(tM(nM := a')) (Suc i) = tM (Suc i)"
              using Suc_i_neq by simp
            also have "... = buf_lin_at blocks (2 * ?c + i)"
              using align i_lt by blast
            also have "... = buf_lin_at (write_bp blocks bp a') (2 * ?c + i)"
              by (rule buf_lin_at_write_bp_other
                        [OF idx_neq idx_2c_lt, symmetric])
            finally show ?thesis .
          qed
        qed
      qed
    next
      case R
      from adv_plain R have adv_R: "bp_advance bp dir.R = Some bp'" by simp
      have lin_R: "bp_linear bp' = Suc (bp_linear bp)"
        by (rule bp_advance_R_linear[OF adv_R])
      \<comment> \<open>Either \<open>bp' = (AE_Right, ofs')\<close> with
        \<open>c_idx ofs' = Suc (c_idx off)\<close>, or \<open>bp' = None\<close>
        via the \<open>AE_Right\<close> R-boundary (\<open>c_succ off = None\<close>),
        which contradicts \<open>adv\<close>.  Hence
        \<open>c_succ off = Some ofs'\<close>.\<close>
      obtain ofs' where c_succ_off: "c_succ off = Some ofs'"
      proof (cases "c_succ off")
        case None
        have "bp_advance bp dir.R = None"
          using bp_eq b_right None unfolding bp_advance_def by simp
        with adv_R show thesis by simp
      next
        case (Some ofs')
        thus thesis using that by simp
      qed
      have bp'_eq: "bp' = (AE_Right, ofs')"
        using bp_eq b_right c_succ_off adv_R
        unfolding bp_advance_def by simp
      have idx_succ: "c_idx ofs' = Suc (c_idx off)"
        by (rule c_succ_idx_some[OF c_succ_off])
      have nM_succ: "go_dir dir.R nM = Suc (c_idx ofs')"
        using nM_form idx_succ by simp
      show ?thesis
        unfolding ae_window_invariant_le0_def
      proof (intro conjI)
        show "fst (snd (write_bp blocks bp a')) = LE_block le"
          by (rule new_h)
        show "(tM(nM := a')) 0 = le" by (rule tM_0_new)
        show "(case fst bp' of
                AE_Home  \<Rightarrow> go_dir d nM = 0
              | AE_Right \<Rightarrow> go_dir d nM = Suc (c_idx (snd bp'))
              | AE_Left  \<Rightarrow> False)"
          using bp'_eq R nM_succ by simp
        show "\<forall>i. i < ?c \<longrightarrow>
                  (tM(nM := a')) (Suc i)
                    = buf_lin_at (write_bp blocks bp a') (2 * ?c + i)"
        proof (intro allI impI)
          fix i
          assume i_lt: "i < ?c"
          show "(tM(nM := a')) (Suc i)
                  = buf_lin_at (write_bp blocks bp a') (2 * ?c + i)"
          proof (cases "i = c_idx off")
            case True
            have "Suc i = nM" using True nM_form by simp
            hence lhs: "(tM(nM := a')) (Suc i) = a'" by simp
            have idx_eq: "2 * ?c + i = bp_linear bp"
              using True bp_lin by simp
            have rhs: "buf_lin_at (write_bp blocks bp a') (2 * ?c + i) = a'"
              using idx_eq buf_lin_at_write_bp_match[of blocks bp a'] by simp
            show ?thesis using lhs rhs by simp
          next
            case False
            have idx_neq: "2 * ?c + i \<noteq> bp_linear bp"
              using False bp_lin by simp
            have idx_2c_lt: "2 * ?c + i < 3 * ?c" using i_lt by simp
            have Suc_i_neq: "Suc i \<noteq> nM"
              using False nM_form by simp
            have "(tM(nM := a')) (Suc i) = tM (Suc i)"
              using Suc_i_neq by simp
            also have "... = buf_lin_at blocks (2 * ?c + i)"
              using align i_lt by blast
            also have "... = buf_lin_at (write_bp blocks bp a') (2 * ?c + i)"
              by (rule buf_lin_at_write_bp_other
                        [OF idx_neq idx_2c_lt, symmetric])
            finally show ?thesis .
          qed
        qed
      qed
    next
      case L
      from adv_plain L have adv_L: "bp_advance bp dir.L = Some bp'" by simp
      have lin_L: "Suc (bp_linear bp') = bp_linear bp"
        by (rule bp_advance_L_linear[OF adv_L])
      \<comment> \<open>Two sub-cases: \<open>c_pred off = Some ofs'\<close> gives
        \<open>bp' = (AE_Right, ofs')\<close>; \<open>c_pred off = None\<close>
        (\<open>off = c_first\<close>) gives \<open>bp' = (AE_Home, c_last)\<close>.\<close>
      show ?thesis
      proof (cases "c_pred off")
        case (Some ofs')
        have bp'_eq: "bp' = (AE_Right, ofs')"
          using bp_eq b_right Some adv_L
          unfolding bp_advance_def by simp
        have idx_pred: "Suc (c_idx ofs') = c_idx off"
          by (rule c_pred_idx_some[OF Some])
        obtain m where nM_eq: "nM = Suc m"
          using nM_bd by (cases nM) auto
        have m_eq: "m = c_idx off" using nM_form nM_eq by simp
        have nM'_eq: "go_dir dir.L nM = Suc (c_idx ofs')"
          using nM_eq m_eq idx_pred by simp
        show ?thesis
          unfolding ae_window_invariant_le0_def
        proof (intro conjI)
          show "fst (snd (write_bp blocks bp a')) = LE_block le"
            by (rule new_h)
          show "(tM(nM := a')) 0 = le" by (rule tM_0_new)
          show "(case fst bp' of
                  AE_Home  \<Rightarrow> go_dir d nM = 0
                | AE_Right \<Rightarrow> go_dir d nM = Suc (c_idx (snd bp'))
                | AE_Left  \<Rightarrow> False)"
            using bp'_eq L nM'_eq by simp
          show "\<forall>i. i < ?c \<longrightarrow>
                    (tM(nM := a')) (Suc i)
                      = buf_lin_at (write_bp blocks bp a') (2 * ?c + i)"
          proof (intro allI impI)
            fix i
            assume i_lt: "i < ?c"
            show "(tM(nM := a')) (Suc i)
                    = buf_lin_at (write_bp blocks bp a') (2 * ?c + i)"
            proof (cases "i = c_idx off")
              case True
              have "Suc i = nM" using True nM_form by simp
              hence lhs: "(tM(nM := a')) (Suc i) = a'" by simp
              have idx_eq: "2 * ?c + i = bp_linear bp"
                using True bp_lin by simp
              have rhs: "buf_lin_at (write_bp blocks bp a') (2 * ?c + i) = a'"
                using idx_eq buf_lin_at_write_bp_match[of blocks bp a'] by simp
              show ?thesis using lhs rhs by simp
            next
              case False
              have idx_neq: "2 * ?c + i \<noteq> bp_linear bp"
                using False bp_lin by simp
              have idx_2c_lt: "2 * ?c + i < 3 * ?c" using i_lt by simp
              have Suc_i_neq: "Suc i \<noteq> nM"
                using False nM_form by simp
              have "(tM(nM := a')) (Suc i) = tM (Suc i)"
                using Suc_i_neq by simp
              also have "... = buf_lin_at blocks (2 * ?c + i)"
                using align i_lt by blast
              also have "... = buf_lin_at (write_bp blocks bp a') (2 * ?c + i)"
                by (rule buf_lin_at_write_bp_other
                          [OF idx_neq idx_2c_lt, symmetric])
              finally show ?thesis .
            qed
          qed
        qed
      next
        case None
        have idx_zero: "c_idx off = 0"
          using c_pred_idx_none[OF None] by simp
        have bp'_eq: "bp' = (AE_Home, c_last)"
          using bp_eq b_right None adv_L
          unfolding bp_advance_def by simp
        have nM_one: "nM = 1" using nM_form idx_zero by simp
        have nM'_eq: "go_dir dir.L nM = 0" using nM_one by simp
        show ?thesis
          unfolding ae_window_invariant_le0_def
        proof (intro conjI)
          show "fst (snd (write_bp blocks bp a')) = LE_block le"
            by (rule new_h)
          show "(tM(nM := a')) 0 = le" by (rule tM_0_new)
          show "(case fst bp' of
                  AE_Home  \<Rightarrow> go_dir d nM = 0
                | AE_Right \<Rightarrow> go_dir d nM = Suc (c_idx (snd bp'))
                | AE_Left  \<Rightarrow> False)"
            using bp'_eq L nM'_eq by simp
          show "\<forall>i. i < ?c \<longrightarrow>
                    (tM(nM := a')) (Suc i)
                      = buf_lin_at (write_bp blocks bp a') (2 * ?c + i)"
          proof (intro allI impI)
            fix i
            assume i_lt: "i < ?c"
            show "(tM(nM := a')) (Suc i)
                    = buf_lin_at (write_bp blocks bp a') (2 * ?c + i)"
            proof (cases "i = c_idx off")
              case True
              have "Suc i = nM" using True nM_form by simp
              hence lhs: "(tM(nM := a')) (Suc i) = a'" by simp
              have idx_eq: "2 * ?c + i = bp_linear bp"
                using True bp_lin by simp
              have rhs: "buf_lin_at (write_bp blocks bp a') (2 * ?c + i) = a'"
                using idx_eq buf_lin_at_write_bp_match[of blocks bp a'] by simp
              show ?thesis using lhs rhs by simp
            next
              case False
              have idx_neq: "2 * ?c + i \<noteq> bp_linear bp"
                using False bp_lin by simp
              have idx_2c_lt: "2 * ?c + i < 3 * ?c" using i_lt by simp
              have Suc_i_neq: "Suc i \<noteq> nM"
                using False nM_form by simp
              have "(tM(nM := a')) (Suc i) = tM (Suc i)"
                using Suc_i_neq by simp
              also have "... = buf_lin_at blocks (2 * ?c + i)"
                using align i_lt by blast
              also have "... = buf_lin_at (write_bp blocks bp a') (2 * ?c + i)"
                by (rule buf_lin_at_write_bp_other
                          [OF idx_neq idx_2c_lt, symmetric])
              finally show ?thesis .
            qed
          qed
        qed
      qed
    qed
  qed
qed

end
