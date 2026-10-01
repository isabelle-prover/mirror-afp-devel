theory AlphabetReduction_Simulation
  imports AlphabetReduction_Determinism
begin

subsection \<open>Simulation correspondence\<close>

text \<open>Position correspondence \<open>sim_pos b\<close>, the AR analogue of
  AE's \<open>ae_decode_pos\<close> read forwards (M-position to
  M'-position).  \<open>M\<close>-position \<open>0\<close> (the mandatory
  \<open>LE\<close> cell) maps to \<open>M'\<close>-position \<open>0\<close>;
  \<open>M\<close>-position \<open>p \<ge> 1\<close> maps to the start of its
  \<open>b\<close>-cell block at \<open>(p - 1) \<cdot> b + 1\<close>.  The
  \<open>1\<close>-cell \<open>LE\<close> / \<open>b\<close>-cell proper layout
  is intrinsic to the substrate's mandatory single \<open>LE\<close>
  cell at position \<open>0\<close>.
  Throughout, \<open>b\<close> abbreviates \<open>block_width \<Gamma>\<close> (the per-symbol cell width).\<close>

definition sim_pos :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sim_pos k p = (if p = 0 then 0 else (p - 1) * k + 1)"

text \<open>The proper-region tiling fact: the encoded cells are
  \<open>b\<close>-wide, aligned, and disjoint, so a position
  \<open>sim_pos b p + j\<close> (\<open>j < b\<close>) lands in another cell's
  block \<open>[sim_pos b q, sim_pos b q + b)\<close> exactly when
  \<open>p = q\<close>.  This is the bridge the forward-step tape
  re-establishment (\<open>tcorr\<^sub>1\<close>) and the advance back-walk
  (\<open>notLE\<close>) both turn on: a write at \<open>M\<close>-position
  \<open>q\<close> touches the \<open>p\<close>-block iff \<open>p = q\<close>.
  Proved by the alignment argument — a block index off by one shifts
  the position by a full \<open>b\<close>, past the \<open>j < b\<close>
  offset.\<close>
lemma sim_pos_in_block_iff:
  fixes K p q j :: nat
  assumes K1: "1 \<le> K" and p1: "1 \<le> p" and q1: "1 \<le> q" and jK: "j < K"
  shows "(sim_pos K q \<le> sim_pos K p + j \<and> sim_pos K p + j < sim_pos K q + K)
           \<longleftrightarrow> p = q"
proof
  assume "p = q"
  thus "sim_pos K q \<le> sim_pos K p + j \<and> sim_pos K p + j < sim_pos K q + K"
    using jK by (simp add: sim_pos_def)
next
  assume L: "sim_pos K q \<le> sim_pos K p + j
               \<and> sim_pos K p + j < sim_pos K q + K"
  have lo: "(q - 1) * K \<le> (p - 1) * K + j"
    and hi: "(p - 1) * K + j < (q - 1) * K + K"
    using L p1 q1 by (auto simp: sim_pos_def)
  have "p - 1 = q - 1"
  proof (rule ccontr)
    assume "p - 1 \<noteq> q - 1"
    then consider "p - 1 < q - 1" | "q - 1 < p - 1" by linarith
    thus False
    proof cases
      case 1
      hence "(p - 1) + 1 \<le> q - 1" by simp
      hence "((p - 1) + 1) * K \<le> (q - 1) * K" by (rule mult_le_mono1)
      hence "(p - 1) * K + K \<le> (q - 1) * K" by (simp add: algebra_simps)
      thus False using lo jK by linarith
    next
      case 2
      hence "(q - 1) + 1 \<le> p - 1" by simp
      hence "((q - 1) + 1) * K \<le> (p - 1) * K" by (rule mult_le_mono1)
      hence "(q - 1) * K + K \<le> (p - 1) * K" by (simp add: algebra_simps)
      thus False using hi by linarith
    qed
  qed
  thus "p = q" using p1 q1 by linarith
qed

text \<open>Per-cell encoding image \<open>cell_repr \<Gamma> bl x\<close>: the
  \<open>b\<close>-cell \<open>sym4\<close> block that a single
  source cell of value \<open>x\<close> occupies on \<open>M'\<close>'s tape
  (at proper positions \<open>p \<ge> 1\<close>).  The blank
  \<open>bl\<close> maps to \<open>b\<close> consecutive \<open>BLANK4\<close>
  cells; every other source symbol maps to its
  \<open>encode_symbol\<close> bit-block.  Both branches have length
  \<open>b\<close>, so the block is uniformly \<open>b\<close>-wide.
  The endmarker \<open>le\<close> is not a case here: \<open>le\<close>
  occurs only at position \<open>0\<close> (a \<open>1\<close>-cell
  \<open>LE4\<close>), handled directly in
  \<open>ar_tape_correspondence\<close>.\<close>

definition cell_repr :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> sym4 list" where
  "cell_repr \<Gamma> bl x =
     (if x = bl then replicate (block_width \<Gamma>) BLANK4
      else encode_symbol \<Gamma> bl x)"

text \<open>Read-phase decode correctness for a whole cell block: folding
  the accumulator from \<open>gamma_unenum 0\<close> over \<open>cell_repr
  \<Gamma> bl x\<close> recovers \<open>x\<close>, uniformly across the blank and
  proper branches.  The blank branch is \<open>foldl_ar_acc_blank\<close>
  (seed rewritten to \<open>bl\<close> via \<open>gamma_unenum_zero\<close>); the
  proper branch is \<open>foldl_ar_acc_encode_symbol\<close>.  This is the
  fact the single-tape read composition discharges its \<open>buf
  tk\<close>-correctness against.\<close>

lemma foldl_ar_acc_cell_repr:
  assumes "finite \<Gamma>" and "bl \<in> \<Gamma>" and "x \<in> \<Gamma>"
  shows "foldl (ar_acc \<Gamma> bl) (gamma_unenum \<Gamma> bl 0)
                (cell_repr \<Gamma> bl x) = x"
proof (cases "x = bl")
  case True
  have "foldl (ar_acc \<Gamma> bl) (gamma_unenum \<Gamma> bl 0) (cell_repr \<Gamma> bl x)
          = foldl (ar_acc \<Gamma> bl) bl (replicate (block_width \<Gamma>) BLANK4)"
    using True gamma_unenum_zero[OF assms(1,2)] by (simp add: cell_repr_def)
  also have "\<dots> = bl" by (rule foldl_ar_acc_blank[OF assms(1,2)])
  finally show ?thesis using True by simp
next
  case False
  have "foldl (ar_acc \<Gamma> bl) (gamma_unenum \<Gamma> bl 0) (cell_repr \<Gamma> bl x)
          = foldl (ar_acc \<Gamma> bl) (gamma_unenum \<Gamma> bl 0)
                  (encode_symbol \<Gamma> bl x)"
    using False by (simp add: cell_repr_def)
  also have "\<dots> = x" by (rule foldl_ar_acc_encode_symbol[OF assms(1,3)])
  finally show ?thesis .
qed

text \<open>Tape-content correspondence under the encoding, the AR
  analogue of AE's \<open>ae_tape_correspondence\<close>.  \<open>M\<close>'s
  tape cell \<open>0\<close> holds \<open>le\<close> and \<open>M'\<close>'s
  cell \<open>0\<close> holds \<open>LE4\<close>; for every proper position
  \<open>p \<ge> 1\<close>, the \<open>b\<close>-cell block on
  \<open>M'\<close> starting at \<open>sim_pos b p\<close>
  spells out \<open>cell_repr \<Gamma> bl (tM p)\<close>.  Since
  \<open>M'\<close>'s alphabet is the whole of \<open>sym4\<close>, no
  separate gamma-block invariant is carried (AE's
  \<open>ae_tape_in_gamma_block\<close> would be vacuous here): the
  correspondence pins every \<open>M'\<close>-cell.\<close>

definition ar_tape_correspondence ::
  "'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> sym4) \<Rightarrow> bool" where
  "ar_tape_correspondence \<Gamma> le bl tM tM' \<longleftrightarrow>
     tM 0 = le \<and> tM' 0 = LE4 \<and>
     (\<forall>p. 1 \<le> p \<longrightarrow>
        (\<forall>j. j < block_width \<Gamma> \<longrightarrow>
           tM' (sim_pos (block_width \<Gamma>) p + j) = cell_repr \<Gamma> bl (tM p) ! j))"

text \<open>The simulation relation, stage-granular, the AR analogue
  of AE's \<open>ae_simulates\<close>.  Holds at \<open>AR_SimRead\<close>
  boundaries (M-step start, M-state not halted) or at the two
  halt configurations between an \<open>M\<close>-configuration
  \<open>cM\<close> and an \<open>M'\<close>-configuration \<open>cM'\<close>:
  \<^item> the \<open>ar_substep_idx\<close> tag is \<open>AR_SimRead\<close>
    with the embedded M-state not yet in \<open>\<lbrace>t, r\<rbrace>\<close>,
    or the M-state is \<open>t\<close> / \<open>r\<close> and the stage is the
    matching \<open>ar_accept_stage\<close> / \<open>ar_reject_stage\<close>
    (AR's dedicated halt stages, unlike AE's parked
    \<open>init_stage\<close>);
  \<^item> the embedded M-state matches \<open>M\<close>'s state;
  \<^item> every tape corresponds cell-for-cell via
    \<open>ar_tape_correspondence\<close>;
  \<^item> at an \<open>AR_SimRead\<close> boundary, every head sits at
    \<open>sim_pos b\<close> of \<open>M\<close>'s head.\<close>

definition ar_simulates ::
  "('q, 'a) mttm
    \<Rightarrow> ('a, 'q) mt_config
    \<Rightarrow> (sym4, 'q \<times> 'a ar_stage) mt_config
    \<Rightarrow> bool" where
  "ar_simulates M cM cM' \<longleftrightarrow>
     (let qM = mt_state cM; tsM = mt_tape cM; nM = mt_pos cM;
          full = mt_state cM';
          tsM' = mt_tape cM'; nM' = mt_pos cM' in
      (case full of (qM', stg) \<Rightarrow>
         (case stg of (idx, _, _, _, _, _) \<Rightarrow>
            ((idx = AR_SimRead \<and> qM' \<notin> {t_tm M, r_tm M})
               \<or> (qM' = t_tm M \<and> stg = ar_accept_stage (bl_tm M))
               \<or> (qM' = r_tm M \<and> stg = ar_reject_stage (bl_tm M)))
            \<and> qM = qM'
            \<and> (\<forall>k < k_tm M. ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                       (tsM k) (tsM' k))
            \<and> (idx = AR_SimRead
                 \<longrightarrow> (\<forall>k. nM' k = sim_pos (block_width (\<Gamma>_tm M)) (nM k))))))"

text \<open>Companion invariant carried alongside \<open>ar_simulates\<close> (the AR
  analogue of AE's \<open>ae_buffer_in_gamma_block\<close>): at an
  \<open>AR_SimRead\<close> boundary the per-tape position-kind flag
  \<open>posk\<close> agrees with \<open>M\<close>'s head being on the left-end
  marker, \<open>posk k = AR_AtLE \<longleftrightarrow> nM k = 0\<close>.  This is
  the bit the read's LE-vs-proper dispatch consumes; the
  \<open>AR_AtFirstProper\<close>/\<open>AR_AtFurtherProper\<close> split is
  deliberately not pinned (the read re-derives it via look-back).  Kept
  out of \<open>ar_simulates\<close> proper so the reverse-direction language
  proof, which shares \<open>ar_simulates\<close>, carries no \<open>posk\<close>
  reasoning.  Vacuous off the \<open>AR_SimRead\<close> boundary (terminal
  accept/reject configs), where the flag is never read again.  Sound by
  the look-back re-sync argument: established
  at the initial config (all heads at \<open>0\<close>, all flags
  \<open>AR_AtLE\<close>) and preserved each \<open>M\<close>-step by
  \<open>ar_simulates_forward_step\<close>.\<close>

definition ar_posk_consistent ::
  "('q, 'a) mttm
    \<Rightarrow> ('a, 'q) mt_config
    \<Rightarrow> (sym4, 'q \<times> 'a ar_stage) mt_config \<Rightarrow> bool" where
  "ar_posk_consistent M cM cM' \<longleftrightarrow>
     (case mt_state cM' of (qM', stg) \<Rightarrow>
        (case stg of (idx, _, _, _, _, posk) \<Rightarrow>
           idx = AR_SimRead
             \<longrightarrow> (\<forall>k. posk k = AR_AtLE \<longleftrightarrow> mt_pos cM k = 0)))"

text \<open>Second companion invariant, the boundary-shape companion (the
  buffer-in-\<open>\<Gamma>\<close> companion, plus
  the canonical-position pin).  \<open>ar_simulates\<close>'s
  \<open>AR_SimRead\<close> arm pins only \<open>idx = AR_SimRead\<close> — not
  the current-tape / bit-counter fields, nor that \<open>buf\<close> is a
  valid alphabet vector — but the read phase
  (\<open>ar_read_phase\<close>) starts a fresh per-\<open>M\<close>-step scan
  at tape \<open>0\<close>, counter \<open>0\<close>, and
  \<open>ar_valid_stage\<close> requires \<open>buf\<close> in
  \<open>\<Gamma> \<union> {bl}\<close>.  So this companion asserts, at an
  \<open>AR_SimRead\<close> boundary, the canonical entry shape \<open>tk =
  0\<close>, \<open>i = 0\<close>, \<open>\<forall>k. buf k \<in> \<Gamma> \<union>
  {bl}\<close>.  Vacuous off the boundary (the halt configs), where the
  read phase never runs.  Under value-level tape count it carries two
  further invariants the reverse walker's read-phase lift needs: the
  boundary stage is \<open>ar_stage_bounded\<close> (its \<open>buf\<close> /
  \<open>dvec\<close> / \<open>posk\<close> tails freeze beyond \<open>k_tm M\<close>),
  and the whole config is blank-tailed (\<open>\<forall>j \<ge> k_tm M.
  mt_tape cM' j (mt_pos cM' j) = BLANK4\<close>) — the \<open>src0_b\<close> /
  \<open>pad0_b\<close> facts the substrate's \<open>alphabet_reduce_delta\<close>
  support filter forces on every produced step.  Established at the
  initial config
  (\<open>ar_init_stage\<close>: tape \<open>0\<close>, counter \<open>0\<close>,
  \<open>buf = \<lambda>_. bl\<close>) and preserved each \<open>M\<close>-step by
  the next handshake's non-terminal arm (resets tape / counter to
  \<open>0\<close>; \<open>buf\<close> carries the just-written symbols, all in
  \<open>\<Gamma>\<close>).  Kept separate from \<open>ar_simulates\<close> for
  the same reason as \<open>ar_posk_consistent\<close> — the
  reverse-direction language proof shares \<open>ar_simulates\<close> and
  should carry no forward-only boundary bookkeeping.\<close>

definition ar_at_read_boundary ::
  "('q, 'a) mttm
    \<Rightarrow> (sym4, 'q \<times> 'a ar_stage) mt_config \<Rightarrow> bool" where
  "ar_at_read_boundary M cM' \<longleftrightarrow>
     (case mt_state cM' of (qM', stg) \<Rightarrow>
        (case stg of (idx, tk, i, buf, dvec, posk) \<Rightarrow>
           idx = AR_SimRead
             \<longrightarrow> (tk = 0 \<and> i = 0
                  \<and> (\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M})
                  \<and> ar_stage_bounded (bl_tm M) (k_tm M)
                       (idx, tk, i, buf, dvec, posk))))
     \<and> (\<forall>j \<ge> k_tm M. mt_tape cM' j (mt_pos cM' j) = BLANK4)"

end
