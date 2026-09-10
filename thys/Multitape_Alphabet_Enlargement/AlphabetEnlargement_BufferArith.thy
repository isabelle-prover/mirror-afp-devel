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

  \<^item> \<open>c_idx\<close> / \<open>bp_linear\<close> base
    arithmetic: \<open>c_succ\<close> / \<open>c_pred\<close> on
    \<open>c_idx\<close>, \<open>bp_linear\<close> at the three
    block-anchor patterns, the universal \<open>< 3c\<close>
    bound, and the \<open>c_idx\<close> values at the first /
    last enum element.

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
  \<open>c_succ\<close> / \<open>c_pred\<close> partial-step operations on \<open>'c\<close>.
  These are the standalone arithmetic underpinning piece 4
  (\<open>ae_m_steps_buffered_correct\<close>): the buffered compute's
  head displacement matches the actual head displacement
  step-by-step, and the head stays in the buffer for any
  prefix of \<open>\<le> c\<close> moves starting from the home block.\<close>

subsubsection \<open>\<open>c_idx\<close> and \<open>bp_linear\<close> arithmetic\<close>

text \<open>\<open>c_succ\<close> and \<open>c_pred\<close>'s effect on \<open>c_idx\<close>.\<close>

lemma c_succ_idx_some:
  fixes x y :: "'c :: enum"
  assumes "c_succ x = Some y"
  shows "c_idx y = Suc (c_idx x)"
proof -
  let ?xs = "enum_class.enum :: 'c list"
  from assms have suc_lt: "Suc (c_idx x) < length ?xs"
                  and y_eq: "y = ?xs ! Suc (c_idx x)"
    unfolding c_succ_def Let_def
    by (auto split: if_split_asm)
  show ?thesis using c_idx_enum_nth[OF suc_lt] y_eq by simp
qed

lemma c_succ_idx_none:
  fixes x :: "'c :: enum"
  assumes "c_succ x = None"
  shows "Suc (c_idx x) = card (UNIV :: 'c set)"
proof -
  let ?xs = "enum_class.enum :: 'c list"
  from assms have "\<not> Suc (c_idx x) < length ?xs"
    unfolding c_succ_def Let_def by (auto split: if_split_asm)
  hence "Suc (c_idx x) \<ge> length ?xs" by simp
  moreover have "c_idx x < length ?xs" by (rule c_idx_in_range)
  ultimately have "Suc (c_idx x) = length ?xs" by linarith
  thus ?thesis by (simp add: card_eq_length_enum)
qed

lemma c_pred_idx_some:
  fixes x y :: "'c :: enum"
  assumes "c_pred x = Some y"
  shows "Suc (c_idx y) = c_idx x"
proof -
  let ?xs = "enum_class.enum :: 'c list"
  from assms have idx_pos: "c_idx x \<noteq> 0"
                  and y_eq: "y = ?xs ! (c_idx x - 1)"
    unfolding c_pred_def Let_def
    by (auto split: if_split_asm)
  from idx_pos have idx_lt: "c_idx x - 1 < length ?xs"
    using c_idx_in_range(1)[of x] by linarith
  have "c_idx y = c_idx x - 1"
    using c_idx_enum_nth[OF idx_lt] y_eq by simp
  thus ?thesis using idx_pos by simp
qed

lemma c_pred_idx_none:
  fixes x :: "'c :: enum"
  assumes "c_pred x = None"
  shows "c_idx x = 0"
  using assms unfolding c_pred_def Let_def
  by (auto split: if_split_asm)

text \<open>\<open>bp_linear\<close>'s value at the three home/left/right
  block patterns, plus the universal \<open>< 3c\<close> bound.\<close>

lemma bp_linear_AE_Left [simp]:
  fixes off :: "'c :: enum"
  shows "bp_linear (AE_Left, off) = c_idx off"
  by (simp add: bp_linear_def)

lemma bp_linear_AE_Home [simp]:
  fixes off :: "'c :: enum"
  shows "bp_linear (AE_Home, off) = card (UNIV :: 'c set) + c_idx off"
  by (simp add: bp_linear_def)

lemma bp_linear_AE_Right [simp]:
  fixes off :: "'c :: enum"
  shows "bp_linear (AE_Right, off)
           = 2 * card (UNIV :: 'c set) + c_idx off"
  by (simp add: bp_linear_def)

lemma bp_linear_lt_3c:
  fixes p :: "('c :: enum) bp"
  shows "bp_linear p < 3 * card (UNIV :: 'c set)"
proof -
  have idx_lt: "c_idx (snd p) < card (UNIV :: 'c set)"
    by (rule c_idx_lt_card)
  show ?thesis using idx_lt
    by (cases p; cases "fst p") auto
qed

subsubsection \<open>\<open>bp_advance\<close> commutation, totality, and LE-aware bounds\<close>

text \<open>\<open>bp_advance\<close>'s commutation with \<open>bp_linear\<close>: each
  successful R-move increments \<open>bp_linear\<close> by 1, each
  successful L-move decrements by 1, N is identity.\<close>

lemma bp_advance_N_some:
  "bp_advance p dir.N = Some p"
  unfolding bp_advance_def by (cases p) simp

lemma bp_advance_N_linear:
  "bp_advance p dir.N = Some p \<and> bp_linear p = bp_linear p"
  using bp_advance_N_some by simp

text \<open>The first / last enum element decode to indices 0 and
  \<open>c - 1\<close>.\<close>

lemma c_idx_first:
  shows "c_idx (c_first :: 'c :: enum) = 0"
proof -
  have len_pos: "0 < length (enum_class.enum :: 'c list)"
    using c_idx_in_range(1)[of "c_first :: 'c"] by linarith
  have "c_idx ((enum_class.enum :: 'c list) ! 0) = 0"
    using c_idx_enum_nth[OF len_pos] .
  thus ?thesis unfolding c_first_def .
qed

lemma c_idx_last:
  shows "c_idx (c_last :: 'c :: enum) = card (UNIV :: 'c set) - 1"
proof -
  let ?xs = "enum_class.enum :: 'c list"
  have len_pos: "0 < length ?xs"
    using c_idx_in_range(1)[of "c_last :: 'c"] by linarith
  have last_lt: "length ?xs - 1 < length ?xs" using len_pos by simp
  have "c_idx ((?xs :: 'c list) ! (length ?xs - 1)) = length ?xs - 1"
    using c_idx_enum_nth[OF last_lt] .
  thus ?thesis
    by (simp add: c_last_def card_eq_length_enum)
qed

lemma bp_advance_R_linear:
  fixes p p' :: "('c :: enum) bp"
  assumes "bp_advance p dir.R = Some p'"
  shows "bp_linear p' = Suc (bp_linear p)"
proof (cases "c_succ (snd p)")
  case (Some off')
  from Some assms have p'_eq: "p' = (fst p, off')"
    unfolding bp_advance_def by (cases p) simp
  have idx_eq: "c_idx off' = Suc (c_idx (snd p))"
    using c_succ_idx_some[OF Some] .
  show ?thesis using p'_eq idx_eq
    by (cases p; cases "fst p") auto
next
  case None
  from None have idx_at_last: "Suc (c_idx (snd p)) = card (UNIV :: 'c set)"
    using c_succ_idx_none by blast
  show ?thesis
  proof (cases "fst p")
    case AE_Left
    with None assms have p'_eq: "p' = (AE_Home, c_first)"
      unfolding bp_advance_def by (cases p) simp
    show ?thesis using p'_eq AE_Left idx_at_last c_idx_first
      by (cases p) auto
  next
    case AE_Home
    with None assms have p'_eq: "p' = (AE_Right, c_first)"
      unfolding bp_advance_def by (cases p) simp
    show ?thesis using p'_eq AE_Home idx_at_last c_idx_first
      by (cases p) auto
  next
    case AE_Right
    with None assms show ?thesis
      unfolding bp_advance_def by (cases p) simp
  qed
qed

lemma bp_advance_L_linear:
  fixes p p' :: "('c :: enum) bp"
  assumes "bp_advance p dir.L = Some p'"
  shows "Suc (bp_linear p') = bp_linear p"
proof (cases "c_pred (snd p)")
  case (Some off')
  from Some assms have p'_eq: "p' = (fst p, off')"
    unfolding bp_advance_def by (cases p) simp
  have idx_eq: "Suc (c_idx off') = c_idx (snd p)"
    using c_pred_idx_some[OF Some] .
  show ?thesis using p'_eq idx_eq
    by (cases p; cases "fst p") auto
next
  case None
  from None have idx_zero: "c_idx (snd p) = 0"
    using c_pred_idx_none by blast
  have c_pos: "0 < card (UNIV :: 'c set)"
    using c_idx_lt_card[of "snd p"] by linarith
  show ?thesis
  proof (cases "fst p")
    case AE_Left
    with None assms show ?thesis
      unfolding bp_advance_def by (cases p) simp
  next
    case AE_Home
    with None assms have p'_eq: "p' = (AE_Left, c_last)"
      unfolding bp_advance_def by (cases p) simp
    have lin_p': "bp_linear p' = card (UNIV :: 'c set) - 1"
      using p'_eq c_idx_last by simp
    have lin_p: "bp_linear p = card (UNIV :: 'c set)"
      using AE_Home idx_zero by (cases p) auto
    show ?thesis using lin_p' lin_p c_pos by linarith
  next
    case AE_Right
    with None assms have p'_eq: "p' = (AE_Home, c_last)"
      unfolding bp_advance_def by (cases p) simp
    have lin_p': "bp_linear p' = card (UNIV :: 'c set) + (card (UNIV :: 'c set) - 1)"
      using p'_eq c_idx_last by simp
    have lin_p: "bp_linear p = 2 * card (UNIV :: 'c set)"
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
  fixes p :: "('c :: enum) bp"
  assumes "bp_linear p < 3 * card (UNIV :: 'c set) - 1"
  shows "\<exists>p'. bp_advance p dir.R = Some p'"
proof (cases "c_succ (snd p)")
  case (Some off')
  thus ?thesis unfolding bp_advance_def by (cases p) simp
next
  case None
  hence idx_at_last: "Suc (c_idx (snd p)) = card (UNIV :: 'c set)"
    using c_succ_idx_none by blast
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
    have lin_eq: "bp_linear p = 3 * card (UNIV :: 'c set) - 1"
      using AE_Right idx_at_last
      by (cases p) auto
    with assms show ?thesis by linarith
  qed
qed

lemma bp_advance_L_some:
  fixes p :: "('c :: enum) bp"
  assumes "0 < bp_linear p"
  shows "\<exists>p'. bp_advance p dir.L = Some p'"
proof (cases "c_pred (snd p)")
  case (Some off')
  thus ?thesis unfolding bp_advance_def by (cases p) simp
next
  case None
  hence idx_zero: "c_idx (snd p) = 0"
    using c_pred_idx_none by blast
  show ?thesis
  proof (cases "fst p")
    case AE_Left
    \<comment> \<open>Contradicts \<open>0 < bp_linear p\<close>: at \<open>(AE_Left, c_first)\<close>,
       \<open>bp_linear p = 0\<close>.\<close>
    have lin_eq: "bp_linear p = 0"
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
  \<open>Some (AE_Right, c_first)\<close>.

  The two position bounds correspond to "head not at the
  rightmost cell of the right block" and "head not at the
  leftmost cell of the left block".  In
  \<open>ae_coupled_run_aux_general\<close>'s inductive step these
  bounds hold strictly at the precondition step \<open>n'\<close>
  thanks to the fifth output conjunct (\<open>bp_linear bound\<close>)
  and the budget \<open>n' \<le> c - 1\<close>.\<close>

lemma bp_advance_le_total:
  fixes le a :: 'a
    and p :: "('c :: enum) bp"
    and d :: dir
  assumes bp_lt_max: "bp_linear p < 3 * card (UNIV :: 'c set) - 1"
      and bp_gt_zero: "0 < bp_linear p"
  shows "\<exists>p'. bp_advance_le le a p d = Some p'"
proof (cases "a = le \<and> fst p = AE_Home \<and> d = dir.R")
  case True
  hence "bp_advance_le le a p d = Some (AE_Right, c_first)"
    unfolding bp_advance_le_def by simp
  thus ?thesis by auto
next
  case False
  hence skip: "bp_advance_le le a p d = bp_advance p d"
    unfolding bp_advance_le_def by auto
  show ?thesis
  proof (cases d)
    case N
    have "bp_advance_le le a p d = Some p"
      using skip N bp_advance_N_some[of p] by simp
    thus ?thesis by blast
  next
    case R
    thus ?thesis using skip bp_advance_R_some[OF bp_lt_max] by auto
  next
    case L
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
    and p p' :: "('c :: enum) bp"
    and d :: dir and n :: nat
  assumes adv: "bp_advance_le le a p d = Some p'"
      and p_pos: "0 < bp_linear p"
      and p_upper: "bp_linear p < 2 * card (UNIV :: 'c set) + n"
      and p_lower: "card (UNIV :: 'c set) \<le> bp_linear p + n"
  shows "card (UNIV :: 'c set) \<le> bp_linear p' + Suc n
        \<and> bp_linear p' < 2 * card (UNIV :: 'c set) + Suc n"
proof (cases "a = le \<and> fst p = AE_Home \<and> d = dir.R")
  case True
  hence p'_eq: "p' = (AE_Right, c_first)"
    using adv unfolding bp_advance_le_def by simp
  hence lin_p': "bp_linear p' = 2 * card (UNIV :: 'c set)"
    by (simp add: c_idx_first)
  show ?thesis using lin_p' by simp
next
  case False
  hence skip: "bp_advance_le le a p d = bp_advance p d"
    unfolding bp_advance_le_def by auto
  with adv have adv_bp: "bp_advance p d = Some p'" by simp
  show ?thesis
  proof (cases d)
    case N
    have "bp_advance p dir.N = Some p" by (rule bp_advance_N_some)
    with adv_bp N have "p' = p" by simp
    hence "bp_linear p' = bp_linear p" by simp
    thus ?thesis using p_upper p_lower by linarith
  next
    case R
    with adv_bp have "bp_linear p' = Suc (bp_linear p)"
      using bp_advance_R_linear by blast
    thus ?thesis using p_upper p_lower by linarith
  next
    case L
    with adv_bp have "Suc (bp_linear p') = bp_linear p"
      using bp_advance_L_linear by blast
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
  fixes blocks :: "(('c :: enum) \<Rightarrow> 'a)
                    \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and bp :: "'c bp"
  shows "buf_lin_at blocks (bp_linear bp) = read_bp blocks bp"
proof -
  obtain l h r where blocks_eq: "blocks = (l, h, r)"
    by (cases blocks) auto
  obtain b off where bp_eq: "bp = (b, off)" by (cases bp)
  let ?c = "card (UNIV :: 'c set)"
  let ?xs = "enum_class.enum :: 'c list"
  have idx_lt: "c_idx off < ?c" by (rule c_idx_lt_card)
  have len_eq: "?c = length ?xs" by (rule card_eq_length_enum)
  have nth_off: "?xs ! c_idx off = off" by (rule c_idx_in_range(2))
  show ?thesis
  proof (cases b)
    case AE_Left
    have "bp_linear bp = c_idx off"
      using bp_eq AE_Left by simp
    moreover have "c_idx off < ?c" using idx_lt .
    ultimately show ?thesis
      using bp_eq blocks_eq AE_Left nth_off
      unfolding buf_lin_at_def read_bp_def by simp
  next
    case AE_Home
    have lin_eq: "bp_linear bp = ?c + c_idx off"
      using bp_eq AE_Home by simp
    have not_lt_c: "\<not> ?c + c_idx off < ?c" by simp
    have lt_2c: "?c + c_idx off < 2 * ?c" using idx_lt by simp
    have sub_eq: "?c + c_idx off - ?c = c_idx off" by simp
    show ?thesis
      using bp_eq blocks_eq AE_Home lin_eq not_lt_c lt_2c sub_eq nth_off
      unfolding buf_lin_at_def read_bp_def by simp
  next
    case AE_Right
    have lin_eq: "bp_linear bp = 2 * ?c + c_idx off"
      using bp_eq AE_Right by simp
    have not_lt_c: "\<not> 2 * ?c + c_idx off < ?c" by simp
    have not_lt_2c: "\<not> 2 * ?c + c_idx off < 2 * ?c" by simp
    have sub_eq: "2 * ?c + c_idx off - 2 * ?c = c_idx off" by simp
    show ?thesis
      using bp_eq blocks_eq AE_Right lin_eq not_lt_c not_lt_2c sub_eq nth_off
      unfolding buf_lin_at_def read_bp_def by simp
  qed
qed

lemma read_bp_via_window:
  fixes tM :: "nat \<Rightarrow> 'a"
    and bp :: "('c :: enum) bp"
    and blocks :: "('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
  assumes "ae_window_invariant tM nM bp blocks p_start"
  shows "read_bp blocks bp = tM nM"
proof -
  let ?c = "card (UNIV :: 'c set)"
  from assms have nM_eq: "nM = p_start + bp_linear bp"
    unfolding ae_window_invariant_def by blast
  from assms have win:
      "\<forall>i. i < 3 * ?c \<longrightarrow> tM (p_start + i) = buf_lin_at blocks i"
    unfolding ae_window_invariant_def by blast
  have lin_lt: "bp_linear bp < 3 * ?c" by (rule bp_linear_lt_3c)
  have e1: "tM nM = buf_lin_at blocks (bp_linear bp)"
    using win lin_lt nM_eq by simp
  have e2: "buf_lin_at blocks (bp_linear bp) = read_bp blocks bp"
    by (rule buf_lin_at_eq_read_bp)
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
    \<open>nM = Suc (c_idx off)\<close>; routes through the right slot
    of the buf-linearisation \<open>tM (Suc i)
    = buf_lin_at blocks (c + i)\<close> at \<open>i = c_idx off\<close>.
  - \<open>AE_Right\<close> (head in right block, offset \<open>off\<close>):
    \<open>nM = Suc (c + c_idx off)\<close>; same buf-linearisation at
    \<open>i = c + c_idx off\<close>.\<close>

lemma read_bp_via_window_le1:
  fixes tM :: "nat \<Rightarrow> 'a"
    and bp :: "('c :: enum) bp"
    and blocks :: "('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
  assumes wi: "ae_window_invariant_le1 tM nM bp blocks le"
  shows "read_bp blocks bp = tM nM"
proof -
  let ?c = "card (UNIV :: 'c set)"
  obtain b off where bp_eq: "bp = (b, off)" by (cases bp)
  obtain l h r where blocks_eq: "blocks = (l, h, r)"
    by (cases blocks) auto
  from wi have tM_0: "tM 0 = le"
    unfolding ae_window_invariant_le1_def by blast
  from wi have l_eq: "fst blocks = LE_block le"
    unfolding ae_window_invariant_le1_def by blast
  from wi have win:
      "\<forall>i. i < 2 * ?c
              \<longrightarrow> tM (Suc i) = buf_lin_at blocks (?c + i)"
    unfolding ae_window_invariant_le1_def by blast
  show ?thesis
  proof (cases b)
    case AE_Left
    have off_c_last: "off = c_last"
      using wi bp_eq AE_Left
      unfolding ae_window_invariant_le1_def by auto
    have nM_eq: "nM = 0"
      using wi bp_eq AE_Left
      unfolding ae_window_invariant_le1_def by auto
    have rd_l: "read_bp blocks bp = l c_last"
      using bp_eq AE_Left off_c_last blocks_eq
      unfolding read_bp_def by simp
    have l_const: "l c_last = le"
      using l_eq blocks_eq unfolding LE_block_def by simp
    show ?thesis using rd_l l_const nM_eq tM_0 by simp
  next
    case AE_Home
    have nM_eq: "nM = Suc (c_idx off)"
      using wi bp_eq AE_Home
      unfolding ae_window_invariant_le1_def by auto
    have idx_lt: "c_idx off < ?c" by (rule c_idx_lt_card)
    have idx_lt_2c: "c_idx off < 2 * ?c" using idx_lt by simp
    have tM_eq:
        "tM (Suc (c_idx off)) = buf_lin_at blocks (?c + c_idx off)"
      using win idx_lt_2c by simp
    have lin_eq: "bp_linear bp = ?c + c_idx off"
      using bp_eq AE_Home unfolding bp_linear_def by simp
    have rd_e: "buf_lin_at blocks (bp_linear bp) = read_bp blocks bp"
      by (rule buf_lin_at_eq_read_bp)
    show ?thesis using nM_eq tM_eq lin_eq rd_e by simp
  next
    case AE_Right
    have nM_eq: "nM = Suc (?c + c_idx off)"
      using wi bp_eq AE_Right
      unfolding ae_window_invariant_le1_def by auto
    have idx_lt: "c_idx off < ?c" by (rule c_idx_lt_card)
    have lt_2c: "?c + c_idx off < 2 * ?c" using idx_lt by simp
    have tM_eq:
        "tM (Suc (?c + c_idx off))
            = buf_lin_at blocks (?c + (?c + c_idx off))"
      using win lt_2c by simp
    have lin_eq: "bp_linear bp = 2 * ?c + c_idx off"
      using bp_eq AE_Right unfolding bp_linear_def by simp
    have eq2: "?c + (?c + c_idx off) = 2 * ?c + c_idx off"
      by simp
    have rd_e: "buf_lin_at blocks (bp_linear bp) = read_bp blocks bp"
      by (rule buf_lin_at_eq_read_bp)
    show ?thesis using nM_eq tM_eq lin_eq rd_e eq2 by simp
  qed
qed

text \<open>LE-edge analogue of \<open>read_bp_via_window\<close> for the
  \<open>le0\<close> regime.  Buffered head can be:
  - \<open>AE_Home\<close>: \<open>nM = 0\<close>; M reads \<open>le\<close>;
    buffer reads \<open>h off = LE_block le off = le\<close>
    (home slot is the \<open>LE_block\<close>).  Match.
  - \<open>AE_Right\<close>: \<open>nM = Suc (c_idx off)\<close>; routes through
    the right slot's buf-linearisation \<open>tM (Suc i)
    = buf_lin_at blocks (2c + i)\<close> at \<open>i = c_idx off\<close>.
  - \<open>AE_Left\<close> excluded by the window invariant.\<close>

lemma read_bp_via_window_le0:
  fixes tM :: "nat \<Rightarrow> 'a"
    and bp :: "('c :: enum) bp"
    and blocks :: "('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
  assumes wi: "ae_window_invariant_le0 tM nM bp blocks le"
  shows "read_bp blocks bp = tM nM"
proof -
  let ?c = "card (UNIV :: 'c set)"
  obtain b off where bp_eq: "bp = (b, off)" by (cases bp)
  obtain l h r where blocks_eq: "blocks = (l, h, r)"
    by (cases blocks) auto
  from wi have tM_0: "tM 0 = le"
    unfolding ae_window_invariant_le0_def by blast
  from wi have h_eq: "fst (snd blocks) = LE_block le"
    unfolding ae_window_invariant_le0_def by blast
  from wi have win:
      "\<forall>i. i < ?c
              \<longrightarrow> tM (Suc i) = buf_lin_at blocks (2 * ?c + i)"
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
    have h_const: "h off = le"
      using h_eq blocks_eq unfolding LE_block_def by simp
    show ?thesis using rd_h h_const nM_eq tM_0 by simp
  next
    case AE_Right
    have nM_eq: "nM = Suc (c_idx off)"
      using wi bp_eq AE_Right
      unfolding ae_window_invariant_le0_def by auto
    have idx_lt: "c_idx off < ?c" by (rule c_idx_lt_card)
    have tM_eq:
        "tM (Suc (c_idx off))
            = buf_lin_at blocks (2 * ?c + c_idx off)"
      using win idx_lt by simp
    have lin_eq: "bp_linear bp = 2 * ?c + c_idx off"
      using bp_eq AE_Right unfolding bp_linear_def by simp
    have rd_e: "buf_lin_at blocks (bp_linear bp) = read_bp blocks bp"
      by (rule buf_lin_at_eq_read_bp)
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
    and bp :: "('c :: enum) bp"
    and blocks :: "('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
  assumes wi: "ae_window_invariant_general tM nM bp blocks pos le"
  shows "read_bp blocks bp = tM nM"
proof -
  let ?c = "card (UNIV :: 'c set)"
  consider (steady) "pos \<ge> 2" | (le1) "pos = 1" | (le0) "pos = 0"
    by linarith
  then show ?thesis
  proof cases
    case steady
    have wi_st: "ae_window_invariant tM nM bp blocks
                    ((pos - 2) * ?c + 1)"
      using wi steady
      unfolding ae_window_invariant_general_def by simp
    show ?thesis by (rule read_bp_via_window[OF wi_st])
  next
    case le1
    have wi_l1: "ae_window_invariant_le1 tM nM bp blocks le"
      using wi le1
      unfolding ae_window_invariant_general_def by simp
    show ?thesis by (rule read_bp_via_window_le1[OF wi_l1])
  next
    case le0
    have wi_l0: "ae_window_invariant_le0 tM nM bp blocks le"
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
  fixes blocks :: "(('c :: enum) \<Rightarrow> 'a)
                    \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and bp :: "'c bp"
    and x :: 'a
  shows "buf_lin_at (write_bp blocks bp x) (bp_linear bp) = x"
proof -
  obtain l h r where blocks_eq: "blocks = (l, h, r)"
    by (cases blocks) auto
  obtain b off where bp_eq: "bp = (b, off)" by (cases bp)
  let ?c = "card (UNIV :: 'c set)"
  let ?xs = "enum_class.enum :: 'c list"
  have idx_lt: "c_idx off < ?c" by (rule c_idx_lt_card)
  have nth_off: "?xs ! c_idx off = off" by (rule c_idx_in_range(2))
  show ?thesis
  proof (cases b)
    case AE_Left
    have lin_eq: "bp_linear bp = c_idx off"
      using bp_eq AE_Left by simp
    have wb: "write_bp blocks bp x = (l(off := x), h, r)"
      using bp_eq blocks_eq AE_Left unfolding write_bp_def by simp
    show ?thesis
      using lin_eq idx_lt wb nth_off
      unfolding buf_lin_at_def by simp
  next
    case AE_Home
    have lin_eq: "bp_linear bp = ?c + c_idx off"
      using bp_eq AE_Home by simp
    have not_lt_c: "\<not> ?c + c_idx off < ?c" by simp
    have lt_2c: "?c + c_idx off < 2 * ?c" using idx_lt by simp
    have sub_eq: "?c + c_idx off - ?c = c_idx off" by simp
    have wb: "write_bp blocks bp x = (l, h(off := x), r)"
      using bp_eq blocks_eq AE_Home unfolding write_bp_def by simp
    show ?thesis
      using lin_eq not_lt_c lt_2c sub_eq wb nth_off
      unfolding buf_lin_at_def by simp
  next
    case AE_Right
    have lin_eq: "bp_linear bp = 2 * ?c + c_idx off"
      using bp_eq AE_Right by simp
    have not_lt_c: "\<not> 2 * ?c + c_idx off < ?c" by simp
    have not_lt_2c: "\<not> 2 * ?c + c_idx off < 2 * ?c" by simp
    have sub_eq: "2 * ?c + c_idx off - 2 * ?c = c_idx off" by simp
    have wb: "write_bp blocks bp x = (l, h, r(off := x))"
      using bp_eq blocks_eq AE_Right unfolding write_bp_def by simp
    show ?thesis
      using lin_eq not_lt_c not_lt_2c sub_eq wb nth_off
      unfolding buf_lin_at_def by simp
  qed
qed

lemma buf_lin_at_write_bp_other:
  fixes blocks :: "(('c :: enum) \<Rightarrow> 'a)
                    \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and bp :: "'c bp"
    and x :: 'a
    and i :: nat
  assumes neq:    "i \<noteq> bp_linear bp"
      and i_lt:   "i < 3 * card (UNIV :: 'c set)"
  shows "buf_lin_at (write_bp blocks bp x) i = buf_lin_at blocks i"
proof -
  obtain l h r where blocks_eq: "blocks = (l, h, r)"
    by (cases blocks) auto
  obtain b off where bp_eq: "bp = (b, off)" by (cases bp)
  let ?c = "card (UNIV :: 'c set)"
  let ?xs = "enum_class.enum :: 'c list"
  have idx_lt: "c_idx off < ?c" by (rule c_idx_lt_card)
  have len_eq: "length ?xs = ?c" by (rule card_eq_length_enum[symmetric])
  have c_idx_eq:
      "\<And>j. j < ?c \<Longrightarrow> c_idx ((?xs :: 'c list) ! j) = j"
  proof -
    fix j assume "j < ?c"
    with len_eq have "j < length ?xs" by simp
    thus "c_idx ((?xs :: 'c list) ! j) = j" by (rule c_idx_enum_nth)
  qed
  show ?thesis
  proof (cases b)
    case AE_Left
    have lin_eq: "bp_linear bp = c_idx off"
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
        from True len_eq have i_in: "i < length ?xs" by simp
        have "c_idx (?xs ! i) = i" using c_idx_eq True by simp
        with eq have "c_idx off = i" by simp
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
    have lin_eq: "bp_linear bp = ?c + c_idx off"
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
          have "c_idx (?xs ! (i - ?c)) = i - ?c"
            using c_idx_eq sub_lt by simp
          with eq have "c_idx off = i - ?c" by simp
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
    have lin_eq: "bp_linear bp = 2 * ?c + c_idx off"
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
        have "c_idx (?xs ! (i - 2 * ?c)) = i - 2 * ?c"
          using c_idx_eq sub_lt by simp
        with eq have "c_idx off = i - 2 * ?c" by simp
        with neq lin_eq ge_2c show False by simp
      qed
      show ?thesis using False ge_2c wb idx_neq blocks_eq
        unfolding buf_lin_at_def Let_def by simp
    qed
  qed
qed

end
