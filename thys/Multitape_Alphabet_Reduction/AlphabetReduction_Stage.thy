theory AlphabetReduction_Stage
  imports AlphabetReduction_Codec
begin

subsection \<open>Stage type and validity\<close>

text \<open>Substep counter / phase indicator for the output machine's
  state set, mirroring AE's \<open>substep_idx\<close>.  The five
  simulation sub-tags \<open>AR_SimRead\<close> /
  \<open>AR_SimCompute\<close> / \<open>AR_SimWrite\<close> /
  \<open>AR_SimAdvance\<close> / \<open>AR_SimNext\<close> mark the five
  phases of one M-step simulation; \<open>AR_HaltAccept\<close> and
  \<open>AR_HaltReject\<close> are the AR-specific terminal states
  that map to the substrate's \<open>t_tm M''\<close> and
  \<open>r_tm M''\<close>.  No validation sub-tags: AR's language
  theorem is quantified over encoder-image inputs only, and
  AR's per-tape \<open>buf\<close> field is populated on-the-fly
  during read substeps (no buffer-initialisation prelude to
  motivate a validation phase).
  Throughout, \<open>b\<close> abbreviates \<open>block_width \<Gamma>\<close> (the per-symbol cell width).\<close>

datatype ar_substep_idx =
    AR_SimRead | AR_SimCompute | AR_SimWrite | AR_SimAdvance
  | AR_SimNext
  | AR_HaltAccept | AR_HaltReject

instance ar_substep_idx :: finite
proof (intro_classes)
  have "(UNIV :: ar_substep_idx set) \<subseteq>
          {AR_SimRead, AR_SimCompute, AR_SimWrite, AR_SimAdvance,
           AR_SimNext,
           AR_HaltAccept, AR_HaltReject}"
    using ar_substep_idx.exhaust by blast
  thus "finite (UNIV :: ar_substep_idx set)"
    using finite_subset by auto
qed

text \<open>Per-tape position-kind tag, the AR analogue of AE's
  per-tape regime dispatch (\<open>le0\<close> / \<open>le1\<close> /
  \<open>steady\<close>), generalised to three values because of the
  LE-1-cell / proper-b-cell layout: \<open>AR_AtLE\<close> for the
  head at M-position 0 (the substrate-mandated single
  \<open>LE4\<close> cell), \<open>AR_AtFirstProper\<close> for the head at
  M-position 1 (immediately past the LE cell, where an
  \<open>L\<close>-move lands on the LE cell), and
  \<open>AR_AtFurtherProper\<close> for the head at M-position
  \<open>\<ge>\<close> 2 (where an \<open>L\<close>-move stays in proper
  territory).  Read by \<open>AR_SimRead\<close> / \<open>AR_SimWrite\<close>
  to dispatch between LE-mode and proper-mode handling, by
  \<open>AR_SimAdvance\<close> to compute the per-direction
  displacement, and updated by \<open>AR_SimAdvance\<close> per the
  direction.\<close>

datatype ar_pos_kind =
    AR_AtLE
  | AR_AtFirstProper
  | AR_AtFurtherProper

instance ar_pos_kind :: finite
proof (intro_classes)
  have "(UNIV :: ar_pos_kind set) \<subseteq>
          {AR_AtLE, AR_AtFirstProper, AR_AtFurtherProper}"
    using ar_pos_kind.exhaust by blast
  thus "finite (UNIV :: ar_pos_kind set)"
    using finite_subset by auto
qed

text \<open>Stage bookkeeping carried in the output machine's state
  set: substep tag, current-tape index (\<open>nat\<close>), per-bit
  counter (\<open>nat\<close>), per-tape symbol buf
  (\<open>nat \<Rightarrow> 'a\<close>: holds the decoded value after read, the
  symbol-to-encode during write), direction-vector
  (\<open>nat \<Rightarrow> dir\<close>: emitted by \<open>AR_SimCompute\<close>,
  consumed by \<open>AR_SimAdvance\<close>), and per-tape position-kind
  (\<open>nat \<Rightarrow> ar_pos_kind\<close>: read by SimRead/SimWrite for
  LE/proper dispatch, updated by SimAdvance per the direction).
  The \<open>nat\<close> counter is loose-typed; \<open>ar_valid_stage\<close>
  below imposes the bound \<open>i < 2 * b\<close>
  (accommodating the \<open>2b\<close>-cell L-walks of
  \<open>AR_SimAdvance\<close>) to recover finiteness of the state
  set.\<close>

type_synonym 'a ar_stage =
  "ar_substep_idx
   \<times> nat
   \<times> nat
   \<times> (nat \<Rightarrow> 'a)
   \<times> (nat \<Rightarrow> dir)
   \<times> (nat \<Rightarrow> ar_pos_kind)"

text \<open>State-level stage validity: the \<open>nat \<Rightarrow> 'a\<close> buf
  field stores per-tape symbols in
  \<open>\<Gamma> \<union> {bl}\<close> (so \<open>finite \<Gamma>\<close> bounds it),
  and the \<open>nat\<close> bit-counter is bounded by
  \<open>2 * b\<close> (the factor \<open>2\<close>
  accommodates \<open>AR_SimAdvance\<close>'s L-walks of up to
  \<open>2b\<close> cells; AR's \<open>\<delta>'\<close> keeps the
  counter's substantively-reachable range within this bound,
  so the bound is non-restrictive on runtime states but
  load-bearing for finiteness of the state set).  The
  position-kind field is unconstrained at this level — its
  type is already finite.  Spec-side counterpart used as the
  stage-component restriction in \<open>alphabet_reduce\<close>'s
  output state set \<open>Q'\<close>, making \<open>Q'\<close> finite from
  the set-level premise \<open>finite \<Gamma>\<close> plus the
  value-level tape-count bound (\<open>ar_stage_bounded\<close>, next block)
  — without requiring
  \<open>UNIV(nat \<Rightarrow> 'a)\<close> to be a finite type.  Direct AR
  analogue of \<open>ae_valid_stage\<close>.\<close>

definition ar_valid_stage ::
  "'a set \<Rightarrow> 'a \<Rightarrow> 'a ar_stage \<Rightarrow> bool" where
  "ar_valid_stage \<Gamma> bl stg \<longleftrightarrow>
     (case stg of (_, _, i, buf, _, _) \<Rightarrow>
        i < 2 * block_width \<Gamma> \<and> (\<forall>k. buf k \<in> \<Gamma> \<union> {bl}))"

text \<open>Tape count bound: the value-level isolation of the tape-count fact.
  The per-tape function fields freeze to their initial values beyond the
  active tape count \<open>K\<close> (\<open>buf \<rightarrow> bl\<close>,
  \<open>dvec \<rightarrow> dir.N\<close>,
  \<open>posk \<rightarrow> AR_AtLE\<close>), and the current-tape scalar
  \<open>tk\<close> stays \<open>\<le> K\<close>.  Kept \<^emph>\<open>separate\<close> from
  \<open>ar_valid_stage\<close> (the per-step content invariant threaded through
  the simulation): the bound is needed only by \<open>alphabet_reduce\<close>'s
  \<open>Q'\<close>, \<open>finite_ar_valid_stages\<close>, the three phase combiners,
  and a single substep-union preservation step — not at the ~120 content
  sites — so the tape count fact is localised rather than smeared.  (AE's
  \<open>ae_valid_stage\<close> folds the bound in directly; that ripple is
  slated for de-rippling in AE's pre-AFP defensive review, converging on
  this isolated shape.)\<close>

definition ar_stage_bounded ::
  "'a \<Rightarrow> nat \<Rightarrow> 'a ar_stage \<Rightarrow> bool" where
  "ar_stage_bounded bl K stg \<longleftrightarrow>
     (case stg of (_, tk, _, buf, dvec, posk) \<Rightarrow>
        tk < K
        \<and> (\<forall>j\<ge>K. buf j = bl)
        \<and> (\<forall>j\<ge>K. dvec j = dir.N)
        \<and> (\<forall>j\<ge>K. posk j = AR_AtLE))"

lemma finite_ar_valid_stages:
  fixes \<Gamma> :: "'a set" and bl :: 'a and K :: nat
  assumes finG: "finite \<Gamma>"
  shows "finite {stg :: 'a ar_stage.
                  ar_valid_stage \<Gamma> bl stg \<and> ar_stage_bounded bl K stg}"
proof -
  let ?B = "\<Gamma> \<union> {bl}"
  have fB: "finite ?B" using finG by simp
  \<comment> \<open>Each \<open>nat \<Rightarrow> X\<close> field is finite by
     @{thm[source] finite_tail_const_funcs}: finite codomain, constant
     beyond \<open>K\<close>.\<close>
  let ?bufs = "{buf :: nat \<Rightarrow> 'a.
                  (\<forall>j. buf j \<in> ?B) \<and> (\<forall>j\<ge>K. buf j = bl)}"
  let ?dvecs = "{dvec :: nat \<Rightarrow> dir.
                  (\<forall>j. dvec j \<in> (UNIV :: dir set))
                  \<and> (\<forall>j\<ge>K. dvec j = dir.N)}"
  let ?posks = "{posk :: nat \<Rightarrow> ar_pos_kind.
                  (\<forall>j. posk j \<in> (UNIV :: ar_pos_kind set))
                  \<and> (\<forall>j\<ge>K. posk j = AR_AtLE)}"
  have fbufs: "finite ?bufs"
    using finite_tail_const_funcs[OF fB, of K bl] .
  have fdvecs: "finite ?dvecs"
    using finite_tail_const_funcs[OF finite_UNIV_dir, of K dir.N] .
  have fposks: "finite ?posks"
    using finite_tail_const_funcs[OF finite_UNIV, of K AR_AtLE] .
  let ?ENV = "(UNIV :: ar_substep_idx set) \<times> {..K} \<times> {..<2 * block_width \<Gamma>}
                \<times> ?bufs \<times> ?dvecs \<times> ?posks"
  have "{stg :: 'a ar_stage.
           ar_valid_stage \<Gamma> bl stg \<and> ar_stage_bounded bl K stg} \<subseteq> ?ENV"
    unfolding ar_valid_stage_def ar_stage_bounded_def
    by (auto simp: mem_Times_iff split: prod.splits)
  moreover have "finite ?ENV"
    using fbufs fdvecs fposks by (intro finite_cartesian_product) simp_all
  ultimately show ?thesis by (rule finite_subset)
qed


subsection \<open>Per-tape enumeration helpers\<close>

text \<open>Per-tape walk helpers.  Under value-level tape count a tape index
  is a natural number directly (tape \<open>kk\<close> sits at position
  \<open>kk\<close>, the active tapes being \<open>{..< k_tm M}\<close>), so the abstract
  enumeration of the old \<open>'k\<close> tape-index type collapses: \<open>k_idx\<close>
  and \<open>k_unidx\<close> are the identity and \<open>k_succ\<close> is \<open>Suc\<close>.
  They are retained as thin wrappers through the tape count migration (inlined
  in the cleanup sweep) so the per-phase walk lemmas keep their shape.  The
  per-tape substep relations (\<open>ar_delta_read\<close>, \<open>ar_delta_write\<close>,
  \<open>ar_delta_advance\<close>) walk tapes in order, processing tape
  \<open>kk\<close>, advancing to \<open>k_succ kk\<close>, and leaving the phase when
  \<open>is_last_k M kk\<close> (\<open>Suc kk = k_tm M\<close>) fires.\<close>

definition k_idx :: "nat \<Rightarrow> nat" where
  "k_idx kk = kk"

definition k_unidx :: "nat \<Rightarrow> nat" where
  "k_unidx j = j"

definition k_succ :: "nat \<Rightarrow> nat" where
  "k_succ kk = Suc kk"

definition is_last_k :: "('q, 'a) mttm \<Rightarrow> nat \<Rightarrow> bool" where
  "is_last_k M kk \<longleftrightarrow> Suc kk = k_tm M"

text \<open>Navigation facts the per-phase tape walks consume.  Under the
  identity collapse these are immediate: \<open>k_idx\<close> and \<open>k_unidx\<close>
  fix \<open>0\<close> and \<open>k_idx\<close> is injective, the successor of
  \<open>k_unidx j\<close> is \<open>k_unidx (Suc j)\<close>, and
  \<open>is_last_k M (k_unidx j)\<close> reduces to \<open>Suc j = k_tm M\<close>.
  The bounded hypotheses are retained so existing call sites keep their
  shape across the migration.\<close>

lemma k_idx_zero: "k_idx 0 = 0"
  by (simp add: k_idx_def)

lemma k_unidx_zero: "k_unidx 0 = 0"
  by (simp add: k_unidx_def)

lemma k_idx_inj: "inj_on k_idx UNIV"
  by (simp add: k_idx_def inj_on_def)

lemma k_idx_unidx:
  assumes "j < k_tm M"
  shows "k_idx (k_unidx j) = j"
  by (simp add: k_idx_def k_unidx_def)

lemma k_succ_unidx:
  assumes "Suc j < k_tm M"
  shows "k_succ (k_unidx j) = k_unidx (Suc j)"
  by (simp add: k_succ_def k_unidx_def)

lemma is_last_k_unidx:
  assumes "j < k_tm M"
  shows "is_last_k M (k_unidx j) \<longleftrightarrow> Suc j = k_tm M"
  by (simp add: is_last_k_def k_unidx_def)


subsection \<open>Per-substep dispatch helpers\<close>

text \<open>Displacement of an \<open>AR_SimAdvance\<close> walk on one
  tape, dispatched on the tape's current direction (from
  \<open>dvec\<close>) and position-kind.  Encodes the displacement
  table: zero
  for \<open>R\<close>
  (head already at \<open>sim_pos (p+1)\<close> after the per-tape
  write phase), one for \<open>N\<close> from \<open>AR_AtLE\<close>
  (single \<open>L\<close>-move back to position 0),
  \<open>b\<close> for \<open>N\<close> from proper (back to
  \<open>sim_pos p\<close>), \<open>Suc b\<close> for \<open>L\<close>
  from \<open>AR_AtFirstProper\<close> (back to position 0), and
  \<open>2 \<cdot> b\<close> for \<open>L\<close> from
  \<open>AR_AtFurtherProper\<close> (back to \<open>sim_pos (p-1)\<close>).
  The \<open>L\<close>-from-\<open>AR_AtLE\<close> case is forbidden by
  the substrate's \<open>\<delta>LE\<close> invariant; setting its
  displacement to \<open>0\<close> here makes the advance relation
  exclude that case naturally (no stepping arm is satisfied, no
  boundary condition fires).\<close>

fun ar_disp :: "nat \<Rightarrow> dir \<Rightarrow> ar_pos_kind \<Rightarrow> nat" where
  "ar_disp _ dir.R _                  = 0"
| "ar_disp _ dir.N AR_AtLE            = 1"
| "ar_disp k dir.N AR_AtFirstProper   = k"
| "ar_disp k dir.N AR_AtFurtherProper = k"
| "ar_disp _ dir.L AR_AtLE            = 0"
| "ar_disp k dir.L AR_AtFirstProper   = Suc k"
| "ar_disp k dir.L AR_AtFurtherProper = 2 * k"

text \<open>Per-tape position-kind transition under
  \<open>AR_SimAdvance\<close>, dispatched on (direction,
  pre-advance position-kind).  Encodes the transition table:
  \<open>R\<close>-advance bumps position-kind up the
  ladder (\<open>AR_AtLE\<close> \<open>\<rightarrow>\<close>
  \<open>AR_AtFirstProper\<close> \<open>\<rightarrow>\<close>
  \<open>AR_AtFurtherProper\<close>; the last is a fixed point);
  \<open>N\<close>-advance preserves position-kind;
  \<open>L\<close>-advance from \<open>AR_AtFirstProper\<close>
  drops to \<open>AR_AtLE\<close>; \<open>L\<close>-advance from
  \<open>AR_AtFurtherProper\<close> remains
  \<open>AR_AtFurtherProper\<close> as a defensive default — the
  actual post-advance position can be either
  \<open>AR_AtFirstProper\<close> (if \<open>p - 1 = 1\<close>) or
  \<open>AR_AtFurtherProper\<close> (otherwise), and a one-cell
  look-back substep at the next \<open>AR_SimRead\<close>
  refines this distinction.  The \<open>L\<close>-from-
  \<open>AR_AtLE\<close> case is forbidden by \<open>\<delta>LE\<close>
  and is never substantively reached; the dummy mapping to
  \<open>AR_AtLE\<close> below keeps \<open>ar_newpos\<close>
  total.\<close>

fun ar_newpos :: "dir \<Rightarrow> ar_pos_kind \<Rightarrow> ar_pos_kind" where
  "ar_newpos dir.R AR_AtLE            = AR_AtFirstProper"
| "ar_newpos dir.R AR_AtFirstProper   = AR_AtFurtherProper"
| "ar_newpos dir.R AR_AtFurtherProper = AR_AtFurtherProper"
| "ar_newpos dir.N AR_AtLE            = AR_AtLE"
| "ar_newpos dir.N AR_AtFirstProper   = AR_AtFirstProper"
| "ar_newpos dir.N AR_AtFurtherProper = AR_AtFurtherProper"
| "ar_newpos dir.L AR_AtLE            = AR_AtLE"
| "ar_newpos dir.L AR_AtFirstProper   = AR_AtLE"
| "ar_newpos dir.L AR_AtFurtherProper = AR_AtFurtherProper"

text \<open>The cell-level write image for a per-tape symbol in
  the proper region.  Returns the \<open>j\<close>-th sym4 cell
  of the symbol's image: \<open>BLANK4\<close> for every position
  if the symbol is the blank \<open>bl\<close> (the blank's
  cell-repr is \<open>b\<close> consecutive blanks); the
  \<open>j\<close>-th bit of \<open>encode_symbol \<Gamma> bl x\<close>
  otherwise.  Used by \<open>ar_delta_write\<close>'s proper-arm
  forward-write phase to emit one cell per substep.  The
  \<open>le_tm M\<close> case is excluded — \<open>ar_delta_write\<close>'s
  LE-arm short-circuits writes for that symbol, so the head
  never enters the forward-write phase with
  \<open>buf tk = le_tm M\<close>.\<close>

definition write_bit ::
  "'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> sym4" where
  "write_bit \<Gamma> bl x j =
     (if x = bl then BLANK4 else encode_symbol \<Gamma> bl x ! j)"

end
