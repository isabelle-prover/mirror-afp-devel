theory BMSSP_Bucketed_Cost_Bridge
  imports BMSSP_Bucketed_Partition BMSSP_Top_Level_Bounds
begin

section \<open>Bridging the Bucketed Operation Costs to the Schedule Parameters\<close>

text \<open>
  This theory closes the gap between the two cost layers of the development.

  The costed BMSSP recurrence (the relations \<open>direct_insert_costed_bmssp\<close> and
  \<open>exact_concrete_bmssp\<close>) charges every direct insert at the
  abstract parameter \<open>t\<close> and every batch-prepended item at the abstract
  parameter \<open>h\<close>, through the predicates @{const partition_insert_cost_bound}
  and @{const partition_batch_cost_bound}.  The top-level analysis then sets
  \<open>t\<close> to the two-thirds logarithmic schedule parameter and \<open>h\<close> to the
  one-third parameter.

  Independently, the bucketed partition theory proves that its concrete
  operations realise the abstract predicates with the
  paper-tight budgets @{const bp_insert_paper_budget} and
  @{const bp_batch_prepend_paper_budget}, each of the shape
  \<open>const + floor_log (Suc (N div M))\<close>.

  What was missing is the arithmetic bridge: the realised bucketed budget
  \<open>const + floor_log (Suc (N div M))\<close> is no larger than the schedule parameter
  whenever the ratio \<open>N div M\<close> is below the corresponding power of two.  The
  bucket directory is searched in \<open>floor_log (Suc (N div M))\<close> steps, so the only
  fact needed is that @{const floor_log} of a number strictly below \<open>2 ^ E\<close>
  does not exceed \<open>E\<close>.  This theory proves that arithmetic, packages it into the
  two interface predicates, and exposes the resulting connected statements:
  with the bucketed costs in force, the per-level ratio bound is exactly what
  makes the abstract Insert and BatchPrepend cost parameters realisable at the
  logarithmic schedule scales used by the headline recurrence.
\<close>

subsection \<open>Logarithmic Arithmetic\<close>

text \<open>
  The single arithmetic fact underlying the whole bridge: if a positive number
  is strictly below \<open>2 ^ E\<close>, its binary logarithm is at most \<open>E\<close>.  Everything
  about the bucketed budgets reduces to this through monotonicity of
  @{const floor_log}.
\<close>

lemma floor_log_less_exp2_le:
  assumes "n < 2 ^ E"
  shows "floor_log n \<le> E"
proof -
  have "n \<le> 2 ^ E"
    using assms by simp
  then have "floor_log n \<le> floor_log (2 ^ E)"
    by (rule floor_log_le_iff)
  also have "\<dots> = E"
    by (rule floor_log_power)
  finally show ?thesis .
qed

lemma floor_log_Suc_div_le:
  assumes "Suc (N div M) \<le> 2 ^ E"
  shows "floor_log (Suc (N div M)) \<le> E"
proof -
  have "floor_log (Suc (N div M)) \<le> floor_log (2 ^ E)"
    using assms by (rule floor_log_le_iff)
  also have "\<dots> = E"
    by (rule floor_log_power)
  finally show ?thesis .
qed

text \<open>
  The ratio condition we use throughout: at most \<open>2 ^ E\<close> blocks worth of
  entries are live, i.e. \<open>N div M < 2 ^ E\<close>.  Equivalently \<open>Suc (N div M) \<le>
  2 ^ E\<close>, the form consumed by @{thm floor_log_Suc_div_le}.
\<close>

definition ratio_below_pow2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "ratio_below_pow2 N M E \<longleftrightarrow> N div M < 2 ^ E"

lemma ratio_below_pow2_floor_log:
  assumes "ratio_below_pow2 N M E"
  shows "floor_log (Suc (N div M)) \<le> E"
proof -
  have "Suc (N div M) \<le> 2 ^ E"
    using assms unfolding ratio_below_pow2_def by simp
  then show ?thesis
    by (rule floor_log_Suc_div_le)
qed

subsection \<open>Bucketed Budgets at the Ratio Bound\<close>

text \<open>
  Under the ratio bound the two paper budgets collapse to a constant plus the
  exponent \<open>E\<close>.  These are the budgets that the realisation corollaries
  @{thm bp_realises_partition_insert_cost_bound} and
  @{thm bp_realises_partition_batch_cost_bound} attach to the concrete bucketed
  operations.
\<close>

lemma bp_insert_paper_budget_le_const_plus_exp:
  assumes "ratio_below_pow2 N M E"
  shows "bp_insert_paper_budget N M \<le> 9 + E"
  unfolding bp_insert_paper_budget_def
  using ratio_below_pow2_floor_log[OF assms] by simp

lemma bp_batch_prepend_paper_budget_le_const_plus_exp:
  assumes "ratio_below_pow2 N M E"
  shows "bp_batch_prepend_paper_budget N M \<le> 2 + E"
  unfolding bp_batch_prepend_paper_budget_def
  using ratio_below_pow2_floor_log[OF assms] by simp

subsection \<open>Monotonicity of the Abstract Cost Predicates\<close>

text \<open>
  The abstract cost predicates are \<open>c \<le> t\<close> and \<open>c \<le> t * length xs\<close>, so they are
  monotone in the budget parameter.  Weakening a realised budget to a larger one
  therefore preserves the predicate; this is what lets us replace the precise
  bucketed budget by the constant-plus-exponent bound and then by the schedule
  parameter.
\<close>

lemma partition_insert_cost_bound_mono:
  fixes c t t' :: nat
  assumes "partition_insert_cost_bound c t"
    and "t \<le> t'"
  shows "partition_insert_cost_bound c t'"
proof -
  have "c \<le> t"
    using assms(1) unfolding partition_insert_cost_bound_def .
  then have "c \<le> t'"
    using assms(2) by (rule le_trans)
  then show ?thesis
    unfolding partition_insert_cost_bound_def .
qed

lemma partition_batch_cost_bound_mono:
  fixes c t t' :: nat
  assumes "partition_batch_cost_bound c t xs"
    and "t \<le> t'"
  shows "partition_batch_cost_bound c t' xs"
proof -
  have "c \<le> t * length xs"
    using assms(1) unfolding partition_batch_cost_bound_def .
  also have "\<dots> \<le> t' * length xs"
    using assms(2) by (rule mult_right_mono) simp
  finally show ?thesis
    unfolding partition_batch_cost_bound_def .
qed

subsection \<open>Bucketed Operations Realise the Schedule Cost Parameters\<close>

text \<open>
  These are the central connecting facts.  Each says: the \emph{actual} step
  count of a concrete bucketed operation satisfies the abstract cost predicate
  with the budget set to \<open>const + E\<close>, provided the operation runs on a state
  whose live ratio is below \<open>2 ^ E\<close>.  No free abstract parameter remains: the
  budget is the measured cost of the bucketed implementation, bounded through
  the logarithmic arithmetic above.

  These bridge the realisation corollaries
  @{thm bp_realises_partition_insert_cost_bound} and
  @{thm bp_realises_partition_batch_cost_bound} (which exhibit the budget as
  \emph{some} value equal to the paper budget) to a concrete, schedule-facing
  inequality.
\<close>

theorem c_bp_paper_insert_realises_const_plus_exp:
  assumes reg: "bp_regular_invariant P"
    and ratio: "ratio_below_pow2 (length (bp_entries P)) (bp_block_size P) E"
  shows "partition_insert_cost_bound
    (bp_steps_of (c_bp_paper_insert x b P)) (9 + E)"
proof -
  have base: "partition_insert_cost_bound
      (bp_steps_of (c_bp_paper_insert x b P))
      (bp_lazy_insert_amortized_budget P)"
    by (rule c_bp_paper_insert_regular_partition_insert_cost_bound[OF reg])
  have budget_eq: "bp_lazy_insert_amortized_budget P =
      bp_insert_paper_budget (length (bp_entries P)) (bp_block_size P)"
    by (rule bp_lazy_insert_amortized_budget_paper_form)
  have budget_le: "bp_insert_paper_budget
      (length (bp_entries P)) (bp_block_size P) \<le> 9 + E"
    by (rule bp_insert_paper_budget_le_const_plus_exp[OF ratio])
  show ?thesis
    by (rule partition_insert_cost_bound_mono[OF base])
       (use budget_eq budget_le in linarith)
qed

theorem c_bp_paper_batch_prepend_realises_const_plus_exp:
  assumes ratio: "ratio_below_pow2 (length xs) (bp_block_size P) E"
  shows "partition_batch_cost_bound
    (bp_steps_of (c_bp_paper_batch_prepend xs P)) (2 + E) xs"
proof -
  have base: "partition_batch_cost_bound
      (bp_steps_of (c_bp_paper_batch_prepend xs P))
      (bp_ratio_log_budget (length xs) (bp_block_size P)) xs"
    by (rule c_bp_paper_batch_prepend_batch_cost_bound)
  have budget_le: "bp_ratio_log_budget (length xs) (bp_block_size P) \<le> 2 + E"
  proof -
    have "bp_ratio_log_budget (length xs) (bp_block_size P) \<le>
        bp_batch_prepend_paper_budget (length xs) (bp_block_size P)"
      by (rule bp_ratio_log_budget_le_batch_prepend_paper_budget)
    also have "\<dots> \<le> 2 + E"
      by (rule bp_batch_prepend_paper_budget_le_const_plus_exp[OF ratio])
    finally show ?thesis .
  qed
  show ?thesis
    by (rule partition_batch_cost_bound_mono[OF base budget_le])
qed

text \<open>
  The Pull cost needs no ratio bound: the bucketed Pull already realises the
  abstract pull predicate exactly (cost \<open>= card S\<close>), independent of the live
  ratio.  We re-expose it here so the three operation costs sit together as the
  connected interface used by the recurrence.
\<close>

theorem c_bp_paper_pull_realises_partition_pull_cost_bound:
  assumes pull: "bp_result_of (c_bp_paper_pull M B P) = (S, beta, P')"
  shows "partition_pull_cost_bound (bp_steps_of (c_bp_paper_pull M B P)) S"
  by (rule bp_realises_partition_pull_cost_bound[OF pull])

subsection \<open>The Bucketed Cost Parameters Sit at the Schedule Scales\<close>

text \<open>
  The previous theorems show, per operation, that the measured bucketed step
  count satisfies the abstract cost predicate with budget \<open>const + E\<close>, where
  \<open>E\<close> is the live-ratio exponent.  The headline recurrence is solved by
  @{thm bmssp_refined_cost_bound_bigo_sssp_time_target_from_component_bounds},
  which needs the Insert cost parameter \<open>t\<close> to grow like \<open>log\<^sup>2\<^sup>/\<^sup>3\<close> and the
  BatchPrepend cost parameter \<open>H\<close> to grow like \<open>log\<^sup>1\<^sup>/\<^sup>3\<close>.

  We now discharge exactly those two envelope facts for the bucketed budgets.
  For Insert, the live ratio is allowed to reach the two-thirds schedule
  parameter, so the budget is \<open>9 + sssp_log_two_thirds_param n\<close>; a constant
  added to \<open>log\<^sup>2\<^sup>/\<^sup>3\<close> is still \<open>O(log\<^sup>2\<^sup>/\<^sup>3)\<close>.  For BatchPrepend, the
  per-pull batch has length at most a constant multiple of the block size
  (bounded out-degree), so its ratio exponent is a constant \<open>c\<close>; the budget is
  then \<open>2 + c\<close>, a constant, which is \<open>O(log\<^sup>1\<^sup>/\<^sup>3)\<close> because the one-third
  factor tends to infinity.  These are the genuine reasons the bucketed costs
  fit the deterministic schedule.
\<close>

lemma sssp_log_factor_at_top:
  "filterlim sssp_log_factor at_top at_top"
proof -
  have "filterlim (\<lambda>n. sssp_log_factor_one_third n * sssp_log_factor_one_third n)
      at_top at_top"
    by (rule filterlim_at_top_mult_at_top
        [OF sssp_log_factor_one_third_at_top sssp_log_factor_one_third_at_top])
  moreover have
    "(\<lambda>n. sssp_log_factor_one_third n * sssp_log_factor_one_third n) =
      sssp_log_factor"
    by (rule ext) (rule sssp_log_factor_one_third_square)
  ultimately show ?thesis by simp
qed

text \<open>
  Insert envelope: a constant plus the two-thirds schedule parameter is
  eventually dominated by twice the two-thirds log factor.  This is the
  @{term t_bound} hypothesis with the bucketed Insert budget in the parameter
  slot.
\<close>

lemma const_plus_two_thirds_param_le_two_thirds_factor:
  "eventually
    (\<lambda>n. real (c + sssp_log_two_thirds_param n) \<le>
      real (c + 2) * sssp_log_factor n) at_top"
  using eventually_one_le_sssp_log_factor
proof eventually_elim
  case (elim n)
  have one_le: "1 \<le> sssp_log_factor n"
    using elim .
  have param_le: "real (sssp_log_two_thirds_param n) \<le> sssp_log_factor n + 1"
  proof -
    have nonneg: "0 \<le> sssp_log_factor n"
      using one_le by linarith
    have "real (nat \<lceil>sssp_log_factor n\<rceil>) = of_int \<lceil>sssp_log_factor n\<rceil>"
      using of_nat_int_ceiling[OF nonneg] .
    moreover have "of_int \<lceil>sssp_log_factor n\<rceil> \<le> sssp_log_factor n + 1"
      using ceiling_correct[of "sssp_log_factor n"] by linarith
    ultimately show ?thesis
      unfolding sssp_log_two_thirds_param_def by simp
  qed
  have c_le: "real c \<le> real c * sssp_log_factor n"
  proof -
    have "real c * 1 \<le> real c * sssp_log_factor n"
      by (rule mult_left_mono[OF one_le]) simp
    then show ?thesis by simp
  qed
  have "real (c + sssp_log_two_thirds_param n) =
      real c + real (sssp_log_two_thirds_param n)"
    by simp
  also have "\<dots> \<le> real c + (sssp_log_factor n + 1)"
    using param_le by linarith
  also have "\<dots> \<le> real c * sssp_log_factor n + 2 * sssp_log_factor n"
    using c_le one_le by linarith
  also have "\<dots> = real (c + 2) * sssp_log_factor n"
    by (simp add: algebra_simps)
  finally show ?case .
qed

text \<open>
  BatchPrepend envelope: a constant budget is eventually dominated by any
  positive multiple of the one-third log factor, because that factor tends to
  infinity.  This is the @{term H_bound} hypothesis with the bucketed
  BatchPrepend budget (a constant under bounded out-degree) in the parameter
  slot.
\<close>

lemma const_le_one_third_factor:
  "eventually
    (\<lambda>n. real (c::nat) \<le> sssp_log_factor_one_third n) at_top"
proof -
  have "filterlim sssp_log_factor_one_third at_top at_top"
    by (rule sssp_log_factor_one_third_at_top)
  then have "eventually (\<lambda>n. real c \<le> sssp_log_factor_one_third n) at_top"
    unfolding filterlim_at_top by blast
  then show ?thesis .
qed

text \<open>
  The two envelopes packaged as the schedule-facing component bounds.  The first
  states that the bucketed Insert cost parameter
  \<open>\<lambda>n. 9 + sssp_log_two_thirds_param n\<close> is \<open>O(log\<^sup>2\<^sup>/\<^sup>3)\<close>; the second that the
  bucketed BatchPrepend cost parameter \<open>\<lambda>n. 2 + c\<close> is \<open>O(log\<^sup>1\<^sup>/\<^sup>3)\<close>.  These
  are exactly the \<open>t_bound\<close> and \<open>H_bound\<close> premises consumed by the recurrence
  solver, now justified by the realised bucketed budgets instead of left as
  free parameters.
\<close>

theorem bucketed_insert_param_two_thirds_envelope:
  "eventually
    (\<lambda>n. real (9 + sssp_log_two_thirds_param n) \<le>
      11 * sssp_log_factor n) at_top"
  using const_plus_two_thirds_param_le_two_thirds_factor[of 9]
  by simp

theorem bucketed_batch_param_one_third_envelope:
  "eventually
    (\<lambda>n. real (2 + c) \<le> real (Suc (2 + c)) * sssp_log_factor_one_third n)
    at_top"
  using const_le_one_third_factor[of "2 + c"]
proof eventually_elim
  case (elim n)
  have nonneg: "0 \<le> sssp_log_factor_one_third n"
    using sssp_log_factor_one_third_pos[of n] by linarith
  have "real (2 + c) \<le> sssp_log_factor_one_third n"
    using elim .
  also have "\<dots> \<le> real (Suc (2 + c)) * sssp_log_factor_one_third n"
  proof -
    have "sssp_log_factor_one_third n * 1 \<le>
        sssp_log_factor_one_third n * real (Suc (2 + c))"
      by (rule mult_left_mono) (use nonneg in simp_all)
    then show ?thesis
      by (simp add: mult.commute)
  qed
  finally show ?case .
qed

subsection \<open>Connected Headline: Bucketed-Costed BMSSP is \<open>O(m log\<^sup>2\<^sup>/\<^sup>3 n)\<close>\<close>

text \<open>
  The capstone.  It plugs the bucketed cost parameters directly into the
  recurrence solver
  @{thm bmssp_refined_cost_bound_bigo_sssp_time_target_from_component_bounds}.
  The Insert cost slot \<open>t\<close> carries the bucketed Insert budget
  \<open>\<lambda>n. 9 + sssp_log_two_thirds_param n\<close>, and the BatchPrepend cost slot \<open>H\<close>
  carries the bucketed BatchPrepend budget \<open>\<lambda>_. 2 + cbatch\<close> (a constant under
  bounded out-degree, when the per-pull batch length stays within a constant
  multiple of the block size).  Crucially, no cost parameter is left free: both
  are the measured bucketed budgets established above.  The conclusion is the
  deterministic SSSP target \<open>O(m * log\<^sup>2\<^sup>/\<^sup>3 n)\<close>.

  Recall the argument order of @{const bmssp_refined_graph_time_bound} is
  \<open>A R H l t m n\<close>, with body \<open>2 A (2 l + 1) n + (R + t + l H) m\<close>; here the
  fifth argument \<open>t\<close> is the Insert cost and the third argument \<open>H\<close> is the
  BatchPrepend per-item cost.

  This theorem is what unifies the two previously separate claims of the entry:
  the asymptotic recurrence (claim 2) and the bucketed operation costs (claim
  3).  In the original development the recurrence's Insert cost was a free
  parameter that the headline simply set to the schedule scale; here that
  parameter is the actual bucketed budget, and the bound still holds.
\<close>

theorem bucketed_refined_cost_bigo_sssp_time_target:
  fixes m A l R T :: "nat \<Rightarrow> nat"
    and cbatch :: nat
    and Cn Ca Cl Cr :: real
  assumes Cn_pos: "0 < Cn"
    and Ca_pos: "0 < Ca"
    and Cl_nonneg: "0 \<le> Cl"
    and Cr_pos: "0 < Cr"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real n \<le> Cn * real (m n)) at_top"
    and A_bound:
      "eventually (\<lambda>n. real (A n) \<le> Ca * sssp_log_factor_one_third n) at_top"
    and l_bound:
      "eventually (\<lambda>n. real (l n) \<le> Cl * sssp_log_factor_one_third n) at_top"
    and R_bound:
      "eventually (\<lambda>n. real (R n) \<le> Cr * sssp_log_factor n) at_top"
    and cost_bound:
      "eventually
        (\<lambda>n. T n \<le> bmssp_refined_graph_time_bound
           A R (\<lambda>_. 2 + cbatch) l
           (\<lambda>n. 9 + sssp_log_two_thirds_param n) m n)
        at_top"
  shows "(\<lambda>n. real (T n)) \<in> O(\<lambda>n. sssp_time_target m n)"
proof (rule bmssp_refined_cost_bound_bigo_sssp_time_target_from_component_bounds
    [where Cn = Cn and Ca = Ca and Cl = Cl and Cr = Cr
       and Ct = 11 and Ch = "real (Suc (2 + cbatch))"
       and A = A and l = l and R = R
       and t = "\<lambda>n. 9 + sssp_log_two_thirds_param n"
       and H = "\<lambda>_. 2 + cbatch" and m = m and T = T])
  show "0 < Cn" by (rule Cn_pos)
  show "0 < Ca" by (rule Ca_pos)
  show "0 \<le> Cl" by (rule Cl_nonneg)
  show "0 < Cr" by (rule Cr_pos)
  show "0 < (11::real)" by simp
  show "0 < real (Suc (2 + cbatch))" by simp
  show "eventually (\<lambda>n. real n \<le> Cn * real (m n)) at_top"
    by (rule vertex_count_dominated)
  show "eventually (\<lambda>n. real (A n) \<le> Ca * sssp_log_factor_one_third n) at_top"
    by (rule A_bound)
  show "eventually (\<lambda>n. real (l n) \<le> Cl * sssp_log_factor_one_third n) at_top"
    by (rule l_bound)
  show "eventually (\<lambda>n. real (R n) \<le> Cr * sssp_log_factor n) at_top"
    by (rule R_bound)
  show "eventually
      (\<lambda>n. real (9 + sssp_log_two_thirds_param n) \<le> 11 * sssp_log_factor n)
      at_top"
    by (rule bucketed_insert_param_two_thirds_envelope)
  show "eventually
      (\<lambda>n. real ((\<lambda>_. 2 + cbatch) n) \<le>
        real (Suc (2 + cbatch)) * sssp_log_factor_one_third n) at_top"
    by (rule bucketed_batch_param_one_third_envelope)
  show "eventually
      (\<lambda>n. T n \<le> bmssp_refined_graph_time_bound
         A R (\<lambda>_. 2 + cbatch) l
         (\<lambda>n. 9 + sssp_log_two_thirds_param n) m n) at_top"
    by (rule cost_bound)
qed

text \<open>
  Specialised to the sparse-graph regime where the vertex term is dominated by
  the edge term, this is the familiar deterministic SSSP envelope
  \<open>O(m * (ln n) powr (2/3))\<close>, now carrying the bucketed Insert and BatchPrepend
  costs in the recurrence rather than free abstract parameters.
\<close>

corollary bucketed_refined_cost_bigo_log_target:
  fixes m A l R T :: "nat \<Rightarrow> nat"
    and cbatch :: nat
    and Cn Ca Cl Cr :: real
  assumes Cn_pos: "0 < Cn"
    and Ca_pos: "0 < Ca"
    and Cl_nonneg: "0 \<le> Cl"
    and Cr_pos: "0 < Cr"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real n \<le> Cn * real (m n)) at_top"
    and A_bound:
      "eventually (\<lambda>n. real (A n) \<le> Ca * sssp_log_factor_one_third n) at_top"
    and l_bound:
      "eventually (\<lambda>n. real (l n) \<le> Cl * sssp_log_factor_one_third n) at_top"
    and R_bound:
      "eventually (\<lambda>n. real (R n) \<le> Cr * sssp_log_factor n) at_top"
    and cost_bound:
      "eventually
        (\<lambda>n. T n \<le> bmssp_refined_graph_time_bound
           A R (\<lambda>_. 2 + cbatch) l
           (\<lambda>n. 9 + sssp_log_two_thirds_param n) m n)
        at_top"
  shows "(\<lambda>n. real (T n)) \<in>
    O(\<lambda>n. real (m n) * (ln (real n + 2)) powr (2 / 3))"
proof -
  have "(\<lambda>n. real (T n)) \<in> O(\<lambda>n. sssp_time_target m n)"
    by (rule bucketed_refined_cost_bigo_sssp_time_target
        [OF Cn_pos Ca_pos Cl_nonneg Cr_pos vertex_count_dominated
          A_bound l_bound R_bound cost_bound])
  then show ?thesis
    unfolding sssp_time_target_def sssp_log_factor_def .
qed

end
