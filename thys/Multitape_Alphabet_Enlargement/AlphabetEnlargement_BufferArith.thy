theory AlphabetEnlargement_BufferArith
  imports AlphabetEnlargement_Uniqueness
begin

text \<open>Arithmetic lemmas on the 3-block buffer abstraction
  used by the \<open>alphabet_enlarge\<close> simulation chain.
  Definitions of \<open>bp_advance\<close>, \<open>bp_linear\<close>,
  \<open>buf_lin_at\<close>, \<open>write_bp\<close>, \<open>read_bp\<close>,
  and the \<open>ae_window_invariant\<close> family live in
  \<open>AlphabetEnlargement_Substeps\<close>; this theory collects the
  lemmas that relate them and forms a self-contained arithmetic
  layer between the encoder/decoder and the forward simulation
  proof.

  Contents, in dependency order:

  \<^item> Offset and \<open>bp_linear\<close> base arithmetic:
    \<open>c_succ\<close> / \<open>c_pred\<close> on offsets, \<open>bp_linear\<close>
    at the three block-anchor patterns, and the universal
    \<open>< 3c\<close> bound.

  \<^item> \<open>bp_advance\<close>'s commutation with
    \<open>bp_linear\<close>: each successful R-move increments
    \<open>bp_linear\<close>, each successful L-move
    decrements it; failure cases correspond to buffer-edge
    positions.  Head-stays-in-buffer totality lemmas for
    strict-interior R / L moves.  LE-aware totality and
    single-step linear-bound preservation for
    \<open>bp_advance_le\<close>.

  \<^item> Read-from-window lemmas: bridge between buffer-read
    at a buffered head position and the linearised buffer access
    (steady / LE-edge / per-tape unified regimes).

  \<^item> \<open>buf_lin_at\<close> effect of \<open>write_bp\<close>
    at the matched buffered head's linear index and at all other
    indices.

  \<^item> Window-invariant single-step preservation under one
    buffered \<open>M\<close>-step: steady regime,
    \<open>le1\<close> regime, \<open>le0\<close> regime, and the
    per-tape unified companion dispatching on the regime
    selector \<open>pos\<close>.

  These lemmas are the standalone arithmetic underpinning piece
  4 of the AE simulation correctness proof
  (\<open>ae_m_steps_buffered_correct\<close>): the buffered
  compute's head displacement matches the actual head
  displacement step-by-step, and the head stays in the buffer
  for any prefix of \<open>\<le> c\<close> moves starting from
  the home block.\<close>


subsection \<open>Buffered head position arithmetic\<close>

text \<open>Lemmas relating \<open>bp_linear\<close> (linearised buffer index in
  \<open>[0, 3c)\<close>) to \<open>bp_advance\<close>'s case structure and to the
  \<open>c_succ\<close> / \<open>c_pred\<close> partial-step operations on offsets.
  These are the standalone arithmetic underpinning piece 4
  (\<open>ae_m_steps_buffered_correct\<close>): the buffered compute's
  head displacement matches the actual head displacement
  step-by-step, and the head stays in the buffer for any
  prefix of \<open>\<le> c\<close> moves starting from the home block.\<close>

subsubsection \<open>Offset and \<open>bp_linear\<close> arithmetic\<close>

text \<open>\<open>c_succ\<close> and \<open>c_pred\<close> step an offset by one, or
  report that it would leave the block.\<close>

lemma c_succ_Some:
  fixes x y :: "nat"
  assumes "c_succ m x = Some y"
  shows "y = Suc x"
  using assms by (auto simp: c_succ_def split: if_split_asm)

lemma c_succ_None:
  fixes x :: "nat"
  assumes "c_succ m x = None" and "x < m"
  shows "Suc x = m"
  using assms by (auto simp: c_succ_def split: if_split_asm)

lemma c_pred_Some:
  fixes x y :: "nat"
  assumes "c_pred x = Some y"
  shows "Suc y = x"
  using assms by (auto simp: c_pred_def split: if_split_asm)

lemma c_pred_None:
  fixes x :: "nat"
  assumes "c_pred x = None"
  shows "x = 0"
  using assms by (auto simp: c_pred_def split: if_split_asm)

text \<open>\<open>bp_linear\<close>'s value at the three home/left/right
  block patterns, plus the universal \<open>< 3c\<close> bound.\<close>

lemma bp_linear_AE_Left [simp]:
  fixes off :: "nat"
  shows "bp_linear m (AE_Left, off) = off"
  by (simp add: bp_linear_def)

lemma bp_linear_AE_Home [simp]:
  fixes off :: "nat"
  shows "bp_linear m (AE_Home, off) = m + off"
  by (simp add: bp_linear_def)

lemma bp_linear_AE_Right [simp]:
  fixes off :: "nat"
  shows "bp_linear m (AE_Right, off)
           = 2 * m + off"
  by (simp add: bp_linear_def)

lemma bp_linear_lt_3c:
  fixes p :: "bp"
  assumes "snd p < m"
  shows "bp_linear m p < 3 * m"
proof -
  have idx_lt: "snd p < m"
    using assms .
  show ?thesis using idx_lt
    by (cases p; cases "fst p") auto
qed

subsubsection \<open>\<open>bp_advance\<close> commutation, totality, and bounds at the endmarker\<close>

text \<open>\<open>bp_advance\<close>'s commutation with \<open>bp_linear\<close>: each
  successful R-move increments \<open>bp_linear\<close> by 1, each
  successful L-move decrements by 1, N is identity.\<close>

lemma bp_advance_N_some:
  "bp_advance m p MoveN = Some p"
  unfolding bp_advance_def by (cases p) simp

lemma bp_advance_N_linear:
  "bp_advance m p MoveN = Some p \<and> bp_linear m p = bp_linear m p"
  using bp_advance_N_some by simp

lemma bp_advance_R_linear:
  fixes p p' :: "bp"
  assumes "bp_advance m p MoveR = Some p'"
      and lt: "snd p < m"
  shows "bp_linear m p' = Suc (bp_linear m p)"
proof (cases "c_succ m (snd p)")
  case (Some off')
  from Some assms have p'_eq: "p' = (fst p, off')"
    unfolding bp_advance_def by (cases p) simp
  have idx_eq: "off' = Suc (snd p)"
    using c_succ_Some[OF Some] .
  show ?thesis using p'_eq idx_eq
    by (cases p; cases "fst p") auto
next
  case None
  from None have idx_at_last: "Suc (snd p) = m"
    using c_succ_None[OF _ lt] by blast
  show ?thesis
  proof (cases "fst p")
    case AE_Left
    with None assms have p'_eq: "p' = (AE_Home, 0)"
      unfolding bp_advance_def by (cases p) simp
    show ?thesis using p'_eq AE_Left idx_at_last
      by (cases p) auto
  next
    case AE_Home
    with None assms have p'_eq: "p' = (AE_Right, 0)"
      unfolding bp_advance_def by (cases p) simp
    show ?thesis using p'_eq AE_Home idx_at_last
      by (cases p) auto
  next
    case AE_Right
    with None assms show ?thesis
      unfolding bp_advance_def by (cases p) simp
  qed
qed

lemma bp_advance_L_linear:
  fixes p p' :: "bp"
  assumes "bp_advance m p MoveL = Some p'"
      and lt: "snd p < m"
  shows "Suc (bp_linear m p') = bp_linear m p"
proof (cases "c_pred (snd p)")
  case (Some off')
  from Some assms have p'_eq: "p' = (fst p, off')"
    unfolding bp_advance_def by (cases p) simp
  have idx_eq: "Suc off' = snd p"
    using c_pred_Some[OF Some] .
  show ?thesis using p'_eq idx_eq
    by (cases p; cases "fst p") auto
next
  case None
  from None have idx_zero: "snd p = 0"
    using c_pred_None by blast
  have c_pos: "0 < m"
    using lt by linarith
  show ?thesis
  proof (cases "fst p")
    case AE_Left
    with None assms show ?thesis
      unfolding bp_advance_def by (cases p) simp
  next
    case AE_Home
    with None assms have p'_eq: "p' = (AE_Left, c_last m)"
      unfolding bp_advance_def by (cases p) simp
    have lin_p': "bp_linear m p' = m - 1"
      using p'_eq c_last_def by simp
    have lin_p: "bp_linear m p = m"
      using AE_Home idx_zero by (cases p) auto
    show ?thesis using lin_p' lin_p c_pos by linarith
  next
    case AE_Right
    with None assms have p'_eq: "p' = (AE_Home, c_last m)"
      unfolding bp_advance_def by (cases p) simp
    have lin_p': "bp_linear m p' = m + (m - 1)"
      using p'_eq c_last_def by simp
    have lin_p: "bp_linear m p = 2 * m"
      using AE_Right idx_zero by (cases p) auto
    show ?thesis using lin_p' lin_p c_pos by linarith
  qed
qed

text \<open>Head-stays-in-buffer: any \<open>R\<close>-move from a strict-interior
  position succeeds; any \<open>L\<close>-move from a strict-interior
  position succeeds.  These are the standalone arithmetic
  underpinning the inductive proof of
  \<open>ae_m_steps_buffered_correct\<close>'s step case.\<close>

lemma bp_advance_R_some:
  fixes p :: "bp"
  assumes "bp_linear m p < 3 * m - 1"
      and lt: "snd p < m"
  shows "\<exists>p'. bp_advance m p MoveR = Some p'"
proof (cases "c_succ m (snd p)")
  case (Some off')
  thus ?thesis unfolding bp_advance_def by (cases p) simp
next
  case None
  hence idx_at_last: "Suc (snd p) = m"
    using c_succ_None[OF _ lt] by blast
  show ?thesis
  proof (cases "fst p")
    case AE_Left
    with None show ?thesis
      unfolding bp_advance_def by (cases p) simp
  next
    case AE_Home
    with None show ?thesis
      unfolding bp_advance_def by (cases p) simp
  next
    case AE_Right
    \<comment> \<open>Contradicts \<open>bp_linear p < 3c - 1\<close>: at
        \<open>(AE_Right, c_last)\<close>, \<open>bp_linear p = 3c - 1\<close>.\<close>
    have lin_eq: "bp_linear m p = 3 * m - 1"
      using AE_Right idx_at_last
      by (cases p) auto
    with assms show ?thesis by linarith
  qed
qed

lemma bp_advance_L_some:
  fixes p :: "bp"
  assumes "0 < bp_linear m p"
  shows "\<exists>p'. bp_advance m p MoveL = Some p'"
proof (cases "c_pred (snd p)")
  case (Some off')
  thus ?thesis unfolding bp_advance_def by (cases p) simp
next
  case None
  hence idx_zero: "snd p = 0"
    using c_pred_None by blast
  show ?thesis
  proof (cases "fst p")
    case AE_Left
    \<comment> \<open>Contradicts \<open>0 < bp_linear p\<close>: at \<open>(AE_Left, 0)\<close>,
       \<open>bp_linear p = 0\<close>.\<close>
    have lin_eq: "bp_linear m p = 0"
      using AE_Left idx_zero by (cases p) auto
    with assms show ?thesis by linarith
  next
    case AE_Home
    with None show ?thesis
      unfolding bp_advance_def by (cases p) simp
  next
    case AE_Right
    with None show ?thesis
      unfolding bp_advance_def by (cases p) simp
  qed
qed

text \<open>LE-aware totality of \<open>bp_advance_le\<close>: given the same
  position bounds that make \<open>bp_advance\<close> total
  (\<open>bp_linear < 3c - 1\<close> excludes the only None case for R,
  \<open>0 < bp_linear\<close> excludes the only None case for L), the
  LE-aware wrapper is also total — the only "extra" behaviour
  is the LE-jump, which always returns
  \<open>Some (AE_Right, 0)\<close>.

  The two position bounds correspond to "head not at the
  rightmost cell of the right block" and "head not at the
  leftmost cell of the left block".  In
  \<open>ae_coupled_run_aux_general\<close>'s inductive step these
  bounds hold strictly at the precondition step \<open>n'\<close>
  thanks to the fifth output conjunct (\<open>bp_linear bound\<close>)
  and the budget \<open>n' \<le> c - 1\<close>.\<close>

lemma bp_advance_le_total:
  fixes le a :: 'a
    and p :: "bp"
    and d :: move
  assumes bp_lt_max: "bp_linear m p < 3 * m - 1"
      and bp_gt_zero: "0 < bp_linear m p"
      and lt: "snd p < m"
  shows "\<exists>p'. bp_advance_le m le a p d = Some p'"
proof (cases "a = le \<and> fst p = AE_Home \<and> d = MoveR")
  case True
  hence "bp_advance_le m le a p d = Some (AE_Right, 0)"
    unfolding bp_advance_le_def by simp
  thus ?thesis by auto
next
  case False
  hence skip: "bp_advance_le m le a p d = bp_advance m p d"
    unfolding bp_advance_le_def by auto
  show ?thesis
  proof (cases d)
    case MoveN
    have "bp_advance_le m le a p d = Some p"
      using skip MoveN bp_advance_N_some[of _ p] by simp
    thus ?thesis by blast
  next
    case MoveR
    thus ?thesis using skip bp_advance_R_some[OF bp_lt_max lt] by auto
  next
    case MoveL
    thus ?thesis using skip bp_advance_L_some[OF bp_gt_zero] by auto
  qed
qed

text \<open>Single-step \<open>bp_linear\<close> preservation for
  \<open>bp_advance_le\<close>: the \<open>c \<le> bp_linear + n\<close>
  /\ \<open>bp_linear < 2c + n\<close> invariant is preserved when
  \<open>n\<close> increases by one.  Four cases by
  \<open>bp_advance_le\<close>'s outcome:

  - LE-jump fires: \<open>bp_linear p' = 2c\<close>, both bounds hold
    trivially.
  - \<open>bp_advance\<close> N: \<open>bp_linear p' = bp_linear p\<close>;
    bounds widen.
  - \<open>bp_advance\<close> R: \<open>bp_linear p' = Suc (bp_linear p)\<close>
    (\<open>bp_advance_R_linear\<close>); upper bound +1, lower +0.
  - \<open>bp_advance\<close> L: \<open>Suc (bp_linear p') = bp_linear p\<close>
    (\<open>bp_advance_L_linear\<close>); upper -1, lower +1 (needs
    \<open>0 < bp_linear p\<close> to avoid nat truncation).

  Used in \<open>ae_coupled_run_aux_general\<close>'s inductive step
  to discharge the fifth output conjunct at \<open>cM_n\<close>.\<close>

lemma bp_advance_le_lin_bounded:
  fixes le a :: 'a
    and p p' :: "bp"
    and d :: move and n :: nat
  assumes adv: "bp_advance_le m le a p d = Some p'"
      and p_pos: "0 < bp_linear m p"
      and p_upper: "bp_linear m p < 2 * m + n"
      and p_lower: "m \<le> bp_linear m p + n"
      and lt: "snd p < m"
  shows "m \<le> bp_linear m p' + Suc n
        \<and> bp_linear m p' < 2 * m + Suc n"
proof (cases "a = le \<and> fst p = AE_Home \<and> d = MoveR")
  case True
  hence p'_eq: "p' = (AE_Right, 0)"
    using adv unfolding bp_advance_le_def by simp
  hence lin_p': "bp_linear m p' = 2 * m"
    by simp
  show ?thesis using lin_p' by simp
next
  case False
  hence skip: "bp_advance_le m le a p d = bp_advance m p d"
    unfolding bp_advance_le_def by auto
  with adv have adv_bp: "bp_advance m p d = Some p'" by simp
  show ?thesis
  proof (cases d)
    case MoveN
    have "bp_advance m p MoveN = Some p" by (rule bp_advance_N_some)
    with adv_bp MoveN have "p' = p" by simp
    hence "bp_linear m p' = bp_linear m p" by simp
    thus ?thesis using p_upper p_lower by linarith
  next
    case MoveR
    with adv_bp have "bp_linear m p' = Suc (bp_linear m p)"
      using bp_advance_R_linear[OF _ lt] by blast
    thus ?thesis using p_upper p_lower by linarith
  next
    case MoveL
    with adv_bp have "Suc (bp_linear m p') = bp_linear m p"
      using bp_advance_L_linear[OF _ lt] by blast
    thus ?thesis using p_upper p_lower p_pos by linarith
  qed
qed

subsubsection \<open>Read-from-window lemmas\<close>

text \<open>Bridge between buffer-read at a buffered head position
  and the linearised buffer access.  Together with the window
  invariant this gives \<open>read_bp blocks bp = tM nM\<close>, the key
  step that lets a buffered \<open>\<delta>\<close>-tuple be matched against an
  M-step's actual symbol read.\<close>

lemma buf_lin_at_eq_read_bp:
  fixes blocks :: "(nat \<Rightarrow> 'a)
                    \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)"
    and bp :: "bp"
  assumes lt: "snd bp < m"
  shows "buf_lin_at m blocks (bp_linear m bp) = read_bp blocks bp"
proof -
  obtain l h r where blocks_eq: "blocks = (l, h, r)"
    by (cases blocks) auto
  obtain b off where bp_eq: "bp = (b, off)" by (cases bp)
  let ?c = "m"
  let ?xs = "[0..<m] :: nat list"
  have off_lt: "off < m" using lt bp_eq by simp
  have nth_off: "?xs ! off = off" using off_lt by simp
  show ?thesis
  proof (cases b)
    case AE_Left
    have "bp_linear m bp = off"
      using bp_eq AE_Left by simp
    moreover have "off < ?c" using off_lt .
    ultimately show ?thesis
      using bp_eq blocks_eq AE_Left nth_off
      unfolding buf_lin_at_def read_bp_def by simp
  next
    case AE_Home
    have lin_eq: "bp_linear m bp = ?c + off"
      using bp_eq AE_Home by simp
    have not_lt_c: "\<not> ?c + off < ?c" by simp
    have lt_2c: "?c + off < 2 * ?c" using off_lt by simp
    have sub_eq: "?c + off - ?c = off" by simp
    show ?thesis
      using bp_eq blocks_eq AE_Home lin_eq not_lt_c lt_2c sub_eq nth_off
      unfolding buf_lin_at_def read_bp_def by simp
  next
    case AE_Right
    have lin_eq: "bp_linear m bp = 2 * ?c + off"
      using bp_eq AE_Right by simp
    have not_lt_c: "\<not> 2 * ?c + off < ?c" by simp
    have not_lt_2c: "\<not> 2 * ?c + off < 2 * ?c" by simp
    have sub_eq: "2 * ?c + off - 2 * ?c = off" by simp
    show ?thesis
      using bp_eq blocks_eq AE_Right lin_eq not_lt_c not_lt_2c sub_eq nth_off
      unfolding buf_lin_at_def read_bp_def by simp
  qed
qed

lemma read_bp_via_window:
  fixes tM :: "nat \<Rightarrow> 'a"
    and bp :: "bp"
    and blocks :: "(nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)"
  assumes "ae_window_invariant m tM nM bp blocks p_start"
  shows "read_bp blocks bp = tM nM"
proof -
  let ?c = "m"
  from assms have nM_eq: "nM = p_start + bp_linear m bp"
    unfolding ae_window_invariant_def by blast
  from assms have win:
      "\<forall>i. i < 3 * ?c \<longrightarrow> tM (p_start + i) = buf_lin_at m blocks i"
    unfolding ae_window_invariant_def by blast
  from assms have lt: "snd bp < m"
    unfolding ae_window_invariant_def by blast
  have lin_lt: "bp_linear m bp < 3 * ?c" using lt by (rule bp_linear_lt_3c)
  have e1: "tM nM = buf_lin_at m blocks (bp_linear m bp)"
    using win lin_lt nM_eq by simp
  have e2: "buf_lin_at m blocks (bp_linear m bp) = read_bp blocks bp"
    using lt by (rule buf_lin_at_eq_read_bp)
  from e1 e2 show ?thesis by simp
qed

text \<open>LE-edge analogue of \<open>read_bp_via_window\<close> for the
  \<open>le1\<close> regime: the buffered read at the head equals the
  M-tape read at the M-side head position, under
  \<open>ae_window_invariant_le1\<close>.  Three sub-cases on
  \<open>fst bp\<close>:
  - \<open>AE_Left\<close> (head at \<open>(AE_Left, c_last)\<close>):
    \<open>nM = 0\<close>; M reads \<open>le\<close>; buffer reads
    \<open>l c_last = LE_block le c_last = le\<close>.  Match.
  - \<open>AE_Home\<close> (head in home block, offset \<open>off\<close>):
    \<open>nM = Suc off\<close>; routes through the right slot
    of the buf-linearisation \<open>tM (Suc i)
    = buf_lin_at blocks (c + i)\<close> at \<open>i = off\<close>.
  - \<open>AE_Right\<close> (head in right block, offset \<open>off\<close>):
    \<open>nM = Suc (c + off)\<close>; same buf-linearisation at
    \<open>i = c + off\<close>.\<close>

lemma read_bp_via_window_le1:
  fixes tM :: "nat \<Rightarrow> 'a"
    and bp :: "bp"
    and blocks :: "(nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)"
  assumes wi: "ae_window_invariant_le1 m tM nM bp blocks le"
  shows "read_bp blocks bp = tM nM"
proof -
  let ?c = "m"
  obtain b off where bp_eq: "bp = (b, off)" by (cases bp)
  obtain l h r where blocks_eq: "blocks = (l, h, r)"
    by (cases blocks) auto
  from wi have tM_0: "tM 0 = le"
    unfolding ae_window_invariant_le1_def by blast
  from wi have l_eq: "fst blocks = LE_block m le"
    unfolding ae_window_invariant_le1_def by blast
  from wi have win:
      "\<forall>i. i < 2 * ?c
              \<longrightarrow> tM (Suc i) = buf_lin_at m blocks (?c + i)"
    unfolding ae_window_invariant_le1_def by blast
  show ?thesis
  proof (cases b)
    case AE_Left
    have off_c_last: "off = c_last m"
      using wi bp_eq AE_Left
      unfolding ae_window_invariant_le1_def by auto
    have nM_eq: "nM = 0"
      using wi bp_eq AE_Left
      unfolding ae_window_invariant_le1_def by auto
    have rd_l: "read_bp blocks bp = l (c_last m)"
      using bp_eq AE_Left off_c_last blocks_eq
      unfolding read_bp_def by simp
    have last_lt: "c_last m < m"
      using wi bp_eq off_c_last unfolding ae_window_invariant_le1_def by auto
    have l_const: "l (c_last m) = le"
      using l_eq blocks_eq last_lt unfolding LE_block_def by simp
    show ?thesis using rd_l l_const nM_eq tM_0 by simp
  next
    case AE_Home
    have nM_eq: "nM = Suc off"
      using wi bp_eq AE_Home
      unfolding ae_window_invariant_le1_def by auto
    have idx_lt: "off < ?c"
      using wi bp_eq
      unfolding ae_window_invariant_le1_def ae_window_invariant_le0_def
      by auto
    have idx_lt_2c: "off < 2 * ?c" using idx_lt by simp
    have tM_eq:
        "tM (Suc off) = buf_lin_at m blocks (?c + off)"
      using win idx_lt_2c by simp
    have lin_eq: "bp_linear m bp = ?c + off"
      using bp_eq AE_Home unfolding bp_linear_def by simp
    have bp_m: "snd bp < m" using bp_eq idx_lt by simp
    have rd_e: "buf_lin_at m blocks (bp_linear m bp) = read_bp blocks bp"
      by (rule buf_lin_at_eq_read_bp[OF bp_m])
    show ?thesis using nM_eq tM_eq lin_eq rd_e by simp
  next
    case AE_Right
    have nM_eq: "nM = Suc (?c + off)"
      using wi bp_eq AE_Right
      unfolding ae_window_invariant_le1_def by auto
    have idx_lt: "off < ?c"
      using wi bp_eq
      unfolding ae_window_invariant_le1_def ae_window_invariant_le0_def
      by auto
    have lt_2c: "?c + off < 2 * ?c" using idx_lt by simp
    have tM_eq:
        "tM (Suc (?c + off))
            = buf_lin_at m blocks (?c + (?c + off))"
      using win lt_2c by simp
    have lin_eq: "bp_linear m bp = 2 * ?c + off"
      using bp_eq AE_Right unfolding bp_linear_def by simp
    have eq2: "?c + (?c + off) = 2 * ?c + off"
      by simp
    have bp_m: "snd bp < m" using bp_eq idx_lt by simp
    have rd_e: "buf_lin_at m blocks (bp_linear m bp) = read_bp blocks bp"
      by (rule buf_lin_at_eq_read_bp[OF bp_m])
    show ?thesis using nM_eq tM_eq lin_eq rd_e eq2 by simp
  qed
qed

text \<open>LE-edge analogue of \<open>read_bp_via_window\<close> for the
  \<open>le0\<close> regime.  Buffered head can be:
  - \<open>AE_Home\<close>: \<open>nM = 0\<close>; M reads \<open>le\<close>;
    buffer reads \<open>h off = LE_block le off = le\<close>
    (home slot is the \<open>LE_block\<close>).  Match.
  - \<open>AE_Right\<close>: \<open>nM = Suc off\<close>; routes through
    the right slot's buf-linearisation \<open>tM (Suc i)
    = buf_lin_at blocks (2c + i)\<close> at \<open>i = off\<close>.
  - \<open>AE_Left\<close> excluded by the window invariant.\<close>

lemma read_bp_via_window_le0:
  fixes tM :: "nat \<Rightarrow> 'a"
    and bp :: "bp"
    and blocks :: "(nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)"
  assumes wi: "ae_window_invariant_le0 m tM nM bp blocks le"
  shows "read_bp blocks bp = tM nM"
proof -
  let ?c = "m"
  obtain b off where bp_eq: "bp = (b, off)" by (cases bp)
  obtain l h r where blocks_eq: "blocks = (l, h, r)"
    by (cases blocks) auto
  from wi have tM_0: "tM 0 = le"
    unfolding ae_window_invariant_le0_def by blast
  from wi have h_eq: "fst (snd blocks) = LE_block m le"
    unfolding ae_window_invariant_le0_def by blast
  from wi have win:
      "\<forall>i. i < ?c
              \<longrightarrow> tM (Suc i) = buf_lin_at m blocks (2 * ?c + i)"
    unfolding ae_window_invariant_le0_def by blast
  show ?thesis
  proof (cases b)
    case AE_Left
    \<comment> \<open>Excluded by \<open>ae_window_invariant_le0\<close>'s case
      analysis on \<open>fst bp\<close>.\<close>
    from wi bp_eq AE_Left have False
      unfolding ae_window_invariant_le0_def by auto
    thus ?thesis ..
  next
    case AE_Home
    have nM_eq: "nM = 0"
      using wi bp_eq AE_Home
      unfolding ae_window_invariant_le0_def by auto
    have rd_h: "read_bp blocks bp = h off"
      using bp_eq AE_Home blocks_eq
      unfolding read_bp_def by simp
    have off_lt: "off < m"
      using wi bp_eq unfolding ae_window_invariant_le0_def by auto
    have h_const: "h off = le"
      using h_eq blocks_eq off_lt unfolding LE_block_def by simp
    show ?thesis using rd_h h_const nM_eq tM_0 by simp
  next
    case AE_Right
    have nM_eq: "nM = Suc off"
      using wi bp_eq AE_Right
      unfolding ae_window_invariant_le0_def by auto
    have idx_lt: "off < ?c"
      using wi bp_eq
      unfolding ae_window_invariant_le1_def ae_window_invariant_le0_def
      by auto
    have tM_eq:
        "tM (Suc off)
            = buf_lin_at m blocks (2 * ?c + off)"
      using win idx_lt by simp
    have lin_eq: "bp_linear m bp = 2 * ?c + off"
      using bp_eq AE_Right unfolding bp_linear_def by simp
    have bp_m: "snd bp < m" using bp_eq idx_lt by simp
    have rd_e: "buf_lin_at m blocks (bp_linear m bp) = read_bp blocks bp"
      by (rule buf_lin_at_eq_read_bp[OF bp_m])
    show ?thesis using nM_eq tM_eq lin_eq rd_e by simp
  qed
qed

text \<open>Per-tape unified read-from-window companion: dispatches on
  the regime selector \<open>pos\<close> into the three sibling
  read-match lemmas (\<open>read_bp_via_window_le0\<close>,
  \<open>read_bp_via_window_le1\<close>, \<open>read_bp_via_window\<close>).
  This is the load-bearing read-match lemma at the inductive step
  of \<open>ae_coupled_run_aux_general\<close>: \<open>read_bp\<close> at
  the buffered head equals \<open>M\<close>-side read.\<close>

lemma read_bp_via_window_general:
  fixes tM :: "nat \<Rightarrow> 'a"
    and bp :: "bp"
    and blocks :: "(nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)"
  assumes wi: "ae_window_invariant_general m tM nM bp blocks pos le"
  shows "read_bp blocks bp = tM nM"
proof -
  let ?c = "m"
  consider (steady) "pos \<ge> 2" | (le1) "pos = 1" | (le0) "pos = 0"
    by linarith
  then show ?thesis
  proof cases
    case steady
    have wi_st: "ae_window_invariant m tM nM bp blocks
                    ((pos - 2) * ?c + 1)"
      using wi steady
      unfolding ae_window_invariant_general_def by simp
    show ?thesis by (rule read_bp_via_window[OF wi_st])
  next
    case le1
    have wi_l1: "ae_window_invariant_le1 m tM nM bp blocks le"
      using wi le1
      unfolding ae_window_invariant_general_def by simp
    show ?thesis by (rule read_bp_via_window_le1[OF wi_l1])
  next
    case le0
    have wi_l0: "ae_window_invariant_le0 m tM nM bp blocks le"
      using wi le0
      unfolding ae_window_invariant_general_def by simp
    show ?thesis by (rule read_bp_via_window_le0[OF wi_l0])
  qed
qed

subsubsection \<open>\<open>buf_lin_at\<close> preservation under \<open>write_bp\<close>\<close>

text \<open>Effect of \<open>write_bp\<close> on \<open>buf_lin_at\<close>: at the
  buffered head's linearised position, the linearised access
  reads back the freshly written symbol; at any other
  in-window position, the linearised access is unchanged.
  Used in the window-invariant preservation step of the
  Suc case of \<open>ae_coupled_run_aux\<close>.\<close>

lemma buf_lin_at_write_bp_match:
  fixes blocks :: "(nat \<Rightarrow> 'a)
                    \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)"
    and bp :: "bp"
    and x :: 'a
  assumes lt: "snd bp < m"
  shows "buf_lin_at m (write_bp blocks bp x) (bp_linear m bp) = x"
proof -
  obtain l h r where blocks_eq: "blocks = (l, h, r)"
    by (cases blocks) auto
  obtain b off where bp_eq: "bp = (b, off)" by (cases bp)
  let ?c = "m"
  let ?xs = "[0..<m] :: nat list"
  have off_lt: "off < m" using lt bp_eq by simp
  have nth_off: "?xs ! off = off" using off_lt by simp
  show ?thesis
  proof (cases b)
    case AE_Left
    have lin_eq: "bp_linear m bp = off"
      using bp_eq AE_Left by simp
    have wb: "write_bp blocks bp x = (l(off := x), h, r)"
      using bp_eq blocks_eq AE_Left unfolding write_bp_def by simp
    show ?thesis
      using lin_eq off_lt wb nth_off
      unfolding buf_lin_at_def by simp
  next
    case AE_Home
    have lin_eq: "bp_linear m bp = ?c + off"
      using bp_eq AE_Home by simp
    have not_lt_c: "\<not> ?c + off < ?c" by simp
    have lt_2c: "?c + off < 2 * ?c" using off_lt by simp
    have sub_eq: "?c + off - ?c = off" by simp
    have wb: "write_bp blocks bp x = (l, h(off := x), r)"
      using bp_eq blocks_eq AE_Home unfolding write_bp_def by simp
    show ?thesis
      using lin_eq not_lt_c lt_2c sub_eq wb nth_off
      unfolding buf_lin_at_def by simp
  next
    case AE_Right
    have lin_eq: "bp_linear m bp = 2 * ?c + off"
      using bp_eq AE_Right by simp
    have not_lt_c: "\<not> 2 * ?c + off < ?c" by simp
    have not_lt_2c: "\<not> 2 * ?c + off < 2 * ?c" by simp
    have sub_eq: "2 * ?c + off - 2 * ?c = off" by simp
    have wb: "write_bp blocks bp x = (l, h, r(off := x))"
      using bp_eq blocks_eq AE_Right unfolding write_bp_def by simp
    show ?thesis
      using lin_eq not_lt_c not_lt_2c sub_eq wb nth_off
      unfolding buf_lin_at_def by simp
  qed
qed

lemma buf_lin_at_write_bp_other:
  fixes blocks :: "(nat \<Rightarrow> 'a)
                    \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)"
    and bp :: "bp"
    and x :: 'a
    and i :: nat
  assumes neq:    "i \<noteq> bp_linear m bp"
      and i_lt:   "i < 3 * m"
  shows "buf_lin_at m (write_bp blocks bp x) i = buf_lin_at m blocks i"
proof -
  obtain l h r where blocks_eq: "blocks = (l, h, r)"
    by (cases blocks) auto
  obtain b off where bp_eq: "bp = (b, off)" by (cases bp)
  let ?c = "m"
  let ?xs = "[0..<m] :: nat list"
  have len_eq: "length ?xs = ?c" by simp
  have nth_upt_eq:
      "\<And>j. j < ?c \<Longrightarrow> ((?xs :: nat list) ! j) = j"
  proof -
    fix j assume "j < ?c"
    with len_eq have "j < length ?xs" by simp
    thus "((?xs :: nat list) ! j) = j" by simp
  qed
  show ?thesis
  proof (cases b)
    case AE_Left
    have lin_eq: "bp_linear m bp = off"
      using bp_eq AE_Left by simp
    have wb: "write_bp blocks bp x = (l(off := x), h, r)"
      using bp_eq blocks_eq AE_Left unfolding write_bp_def by simp
    show ?thesis
    proof (cases "i < ?c")
      case True
      \<comment> \<open>i lands in the left block; offset is \<open>?xs ! i\<close>.\<close>
      have idx_neq: "?xs ! i \<noteq> off"
      proof
        assume eq: "?xs ! i = off"
        have "(?xs ! i) = i" using nth_upt_eq True by simp
        with eq have "off = i" by simp
        with neq lin_eq show False by simp
      qed
      show ?thesis using True wb idx_neq blocks_eq
        unfolding buf_lin_at_def by simp
    next
      case False
      \<comment> \<open>i lands in home or right block; left-block update doesn't affect.\<close>
      show ?thesis using False wb blocks_eq
        unfolding buf_lin_at_def by simp
    qed
  next
    case AE_Home
    have lin_eq: "bp_linear m bp = ?c + off"
      using bp_eq AE_Home by simp
    have wb: "write_bp blocks bp x = (l, h(off := x), r)"
      using bp_eq blocks_eq AE_Home unfolding write_bp_def by simp
    show ?thesis
    proof (cases "i < ?c")
      case True
      show ?thesis using True wb blocks_eq
        unfolding buf_lin_at_def by simp
    next
      case False
      hence ge_c: "i \<ge> ?c" by simp
      show ?thesis
      proof (cases "i < 2 * ?c")
        case True
        \<comment> \<open>home block; offset is \<open>?xs ! (i - ?c)\<close>.\<close>
        have sub_lt: "i - ?c < ?c" using True ge_c by simp
        have idx_neq: "?xs ! (i - ?c) \<noteq> off"
        proof
          assume eq: "?xs ! (i - ?c) = off"
          have "(?xs ! (i - ?c)) = i - ?c"
            using nth_upt_eq sub_lt by simp
          with eq have "off = i - ?c" by simp
          with neq lin_eq ge_c show False by simp
        qed
        show ?thesis using True ge_c wb idx_neq blocks_eq
          unfolding buf_lin_at_def by simp
      next
        case False
        show ?thesis using False ge_c wb blocks_eq
          unfolding buf_lin_at_def by simp
      qed
    qed
  next
    case AE_Right
    have lin_eq: "bp_linear m bp = 2 * ?c + off"
      using bp_eq AE_Right by simp
    have wb: "write_bp blocks bp x = (l, h, r(off := x))"
      using bp_eq blocks_eq AE_Right unfolding write_bp_def by simp
    show ?thesis
    proof (cases "i < 2 * ?c")
      case True
      show ?thesis using True wb blocks_eq
        unfolding buf_lin_at_def Let_def by simp
    next
      case False
      hence ge_2c: "i \<ge> 2 * ?c" by simp
      \<comment> \<open>right block; offset is \<open>?xs ! (i - 2 * ?c)\<close>.\<close>
      have sub_lt: "i - 2 * ?c < ?c" using ge_2c i_lt by simp
      have idx_neq: "?xs ! (i - 2 * ?c) \<noteq> off"
      proof
        assume eq: "?xs ! (i - 2 * ?c) = off"
        have "(?xs ! (i - 2 * ?c)) = i - 2 * ?c"
          using nth_upt_eq sub_lt by simp
        with eq have "off = i - 2 * ?c" by simp
        with neq lin_eq ge_2c show False by simp
      qed
      show ?thesis using False ge_2c wb idx_neq blocks_eq
        unfolding buf_lin_at_def Let_def by simp
    qed
  qed
qed

end
