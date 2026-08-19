theory BMSSP_Complexity
  imports "HOL-Library.Landau_Symbols" BMSSP_Operational_Pull
begin

section \<open>Core Cost Accounting\<close>

text \<open>
  This theory starts the checked complexity side of the development.  Earlier
  theories prove that the recursive BMSSP algorithm returns the right vertices
  and labels.  Here the same traces are interpreted as cost recurrences.  The
  first part is deliberately arithmetic: logarithmic target functions, level
  widths, level capacities, and the Big-O envelopes that eventually become the
  SSSP headline.

  The file then moves inside the graph locale and introduces the graph-size
  quantities used by the cost bounds.  Vertex counts, edge counts, outgoing
  ranges, and range-tree chains are all finite combinatorial objects.  The
  proofs establish that the lists produced by a partition loop are disjoint
  slices, so their vertex and outgoing-edge costs can be summed without double
  counting.

  The final part defines a costed operational relation for the abstract
  partition interface.  It is intentionally not the bucketed implementation; it
  is the reusable recurrence layer that later theories refine.  The bucketed
  proof plugs concrete local costs into these abstract cost expressions, while
  the top-level bounds instantiate the logarithmic parameter schedule.
\<close>

definition sssp_log_factor where
  "sssp_log_factor n = (ln (real n + 2)) powr (2 / 3)"

definition sssp_log_factor_one_third where
  "sssp_log_factor_one_third n = (ln (real n + 2)) powr (1 / 3)"

definition sssp_time_target where
  "sssp_time_target m n = real (m n) * sssp_log_factor n"

definition bmssp_level_width :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bmssp_level_width t l = 2 ^ (l * t)"

definition bmssp_level_cap :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bmssp_level_cap k t l = k * bmssp_level_width t l"

lemma bmssp_level_width_pos [simp]:
  "0 < bmssp_level_width t l"
  unfolding bmssp_level_width_def by simp

lemma bmssp_level_cap_eq:
  "bmssp_level_cap k t l = k * 2 ^ (l * t)"
  unfolding bmssp_level_cap_def bmssp_level_width_def by simp

lemma bmssp_level_width_mono:
  assumes "l \<le> l'"
  shows "bmssp_level_width t l \<le> bmssp_level_width t l'"
proof -
  have "l * t \<le> l' * t"
    using assms by simp
  then show ?thesis
    unfolding bmssp_level_width_def by (simp add: power_increasing)
qed

lemma bmssp_level_width_Suc:
  "bmssp_level_width t (Suc l) = bmssp_level_width t l * 2 ^ t"
  unfolding bmssp_level_width_def by (simp add: power_add algebra_simps)

lemma bmssp_level_width_prev_times_two_le:
  assumes "0 < t" "0 < l"
  shows "2 * bmssp_level_width t (l - 1) \<le> bmssp_level_width t l"
proof (cases l)
  case 0
  then show ?thesis
    using assms by simp
next
  case (Suc l')
  have two_le: "(2::nat) \<le> 2 ^ t"
  proof -
    have "2 ^ 1 \<le> (2::nat) ^ t"
      by (rule power_increasing) (use assms(1) in simp_all)
    then show ?thesis
      by simp
  qed
  have "2 * bmssp_level_width t (l - 1) \<le>
      (2 ^ t) * bmssp_level_width t (l - 1)"
    by (rule mult_right_mono[OF two_le]) simp
  also have "\<dots> = bmssp_level_width t l"
    unfolding Suc bmssp_level_width_Suc by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma bmssp_level_cap_mono:
  assumes "l \<le> l'"
  shows "bmssp_level_cap k t l \<le> bmssp_level_cap k t l'"
  unfolding bmssp_level_cap_def
  using bmssp_level_width_mono[OF assms, of t] by simp

lemma bmssp_level_cap_ge_level:
  "k \<le> bmssp_level_cap k t l"
  unfolding bmssp_level_cap_def
  using bmssp_level_width_pos[of t l]
  by (cases "bmssp_level_width t l") simp_all

lemma bmssp_level_size_constraint_arithmetic:
  assumes t_pos: "0 < t"
    and l_pos: "0 < l"
    and before: "acc < k * bmssp_level_width t l"
    and child: "child \<le> 4 * k * bmssp_level_width t (l - 1)"
    and extra: "extra \<le> k * bmssp_level_width t l"
    and U_size: "U_size \<le> acc + child + extra"
  shows "U_size \<le> 4 * k * bmssp_level_width t l"
proof -
  have acc_le: "acc \<le> k * bmssp_level_width t l"
    using before by simp
  have child_le: "child \<le> 2 * k * bmssp_level_width t l"
  proof -
    have "4 * k * bmssp_level_width t (l - 1) \<le>
        2 * k * bmssp_level_width t l"
    proof -
      have "2 * bmssp_level_width t (l - 1) \<le> bmssp_level_width t l"
        by (rule bmssp_level_width_prev_times_two_le[OF t_pos l_pos])
      then have "2 * k * (2 * bmssp_level_width t (l - 1)) \<le>
          2 * k * bmssp_level_width t l"
        by simp
      then show ?thesis
        by (simp add: algebra_simps)
    qed
    then show ?thesis
      using child by linarith
  qed
  have "U_size \<le>
      k * bmssp_level_width t l +
      2 * k * bmssp_level_width t l +
      k * bmssp_level_width t l"
    using U_size acc_le child_le extra by linarith
  also have "\<dots> = 4 * k * bmssp_level_width t l"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma sssp_log_factor_pos [simp]:
  "0 < sssp_log_factor n"
proof -
  have "1 < real n + 2"
    by simp
  then have "0 < ln (real n + 2)"
    by (rule ln_gt_zero)
  then show ?thesis
    unfolding sssp_log_factor_def by simp
qed

lemma sssp_log_factor_one_third_pos [simp]:
  "0 < sssp_log_factor_one_third n"
proof -
  have "1 < real n + 2"
    by simp
  then have "0 < ln (real n + 2)"
    by (rule ln_gt_zero)
  then show ?thesis
    unfolding sssp_log_factor_one_third_def by simp
qed

lemma sssp_log_factor_mono:
  assumes "n \<le> m"
  shows "sssp_log_factor n \<le> sssp_log_factor m"
proof -
  have ln_le: "ln (real n + 2) \<le> ln (real m + 2)"
    by (rule ln_mono) (use assms in simp_all)
  have ln_nonneg: "0 \<le> ln (real n + 2)"
    by simp
  show ?thesis
    unfolding sssp_log_factor_def
    by (rule powr_mono2) (use ln_nonneg ln_le in simp_all)
qed

lemma sssp_log_factor_one_third_mono:
  assumes "n \<le> m"
  shows "sssp_log_factor_one_third n \<le> sssp_log_factor_one_third m"
proof -
  have ln_le: "ln (real n + 2) \<le> ln (real m + 2)"
    by (rule ln_mono) (use assms in simp_all)
  have ln_nonneg: "0 \<le> ln (real n + 2)"
    by simp
  show ?thesis
    unfolding sssp_log_factor_one_third_def
    by (rule powr_mono2) (use ln_nonneg ln_le in simp_all)
qed

lemma sssp_log_factor_square_arg_le:
  "sssp_log_factor (n * n) \<le> 2 * sssp_log_factor n"
proof -
  let ?a = "ln (real (n * n) + 2)"
  let ?b = "ln (real n + 2)"
  have arg_le: "real (n * n) + 2 \<le> (real n + 2) ^ 2"
    by (simp add: power2_eq_square algebra_simps)
  have arg_pos: "0 < real (n * n) + 2"
  proof -
    have "0 \<le> real (n * n)"
      by simp
    then show ?thesis
      by linarith
  qed
  have ln_le: "?a \<le> 2 * ?b"
  proof -
    have "?a \<le> ln ((real n + 2) ^ 2)"
      by (rule ln_mono) (use arg_le in simp, rule arg_pos)
    also have "\<dots> = 2 * ?b"
      by (simp add: ln_realpow)
    finally show ?thesis .
  qed
  have a_nonneg: "0 \<le> ?a"
    by simp
  have b_nonneg: "0 \<le> ?b"
    by simp
  have powr_le: "?a powr (2 / 3) \<le> (2 * ?b) powr (2 / 3)"
    by (rule powr_mono2) (use a_nonneg ln_le in simp_all)
  have two_powr_le: "(2::real) powr (2 / 3) \<le> 2"
  proof -
    have "(2::real) powr (2 / 3) \<le> 2 powr 1"
      by (rule powr_mono) simp_all
    then show ?thesis
      by simp
  qed
  have "(2 * ?b) powr (2 / 3) =
      (2::real) powr (2 / 3) * (?b powr (2 / 3))"
    by (simp add: powr_mult)
  also have "\<dots> \<le> 2 * (?b powr (2 / 3))"
    by (rule mult_right_mono[OF two_powr_le]) (use b_nonneg in simp)
  finally have "(2 * ?b) powr (2 / 3) \<le> 2 * (?b powr (2 / 3))" .
  then show ?thesis
    unfolding sssp_log_factor_def using powr_le by linarith
qed

lemma sssp_log_factor_one_third_square_arg_le:
  "sssp_log_factor_one_third (n * n) \<le>
    2 * sssp_log_factor_one_third n"
proof -
  let ?a = "ln (real (n * n) + 2)"
  let ?b = "ln (real n + 2)"
  have arg_le: "real (n * n) + 2 \<le> (real n + 2) ^ 2"
    by (simp add: power2_eq_square algebra_simps)
  have arg_pos: "0 < real (n * n) + 2"
  proof -
    have "0 \<le> real (n * n)"
      by simp
    then show ?thesis
      by linarith
  qed
  have ln_le: "?a \<le> 2 * ?b"
  proof -
    have "?a \<le> ln ((real n + 2) ^ 2)"
      by (rule ln_mono) (use arg_le in simp, rule arg_pos)
    also have "\<dots> = 2 * ?b"
      by (simp add: ln_realpow)
    finally show ?thesis .
  qed
  have a_nonneg: "0 \<le> ?a"
    by simp
  have b_nonneg: "0 \<le> ?b"
    by simp
  have powr_le: "?a powr (1 / 3) \<le> (2 * ?b) powr (1 / 3)"
    by (rule powr_mono2) (use a_nonneg ln_le in simp_all)
  have two_powr_le: "(2::real) powr (1 / 3) \<le> 2"
  proof -
    have "(2::real) powr (1 / 3) \<le> 2 powr 1"
      by (rule powr_mono) simp_all
    then show ?thesis
      by simp
  qed
  have "(2 * ?b) powr (1 / 3) =
      (2::real) powr (1 / 3) * (?b powr (1 / 3))"
    by (simp add: powr_mult)
  also have "\<dots> \<le> 2 * (?b powr (1 / 3))"
    by (rule mult_right_mono[OF two_powr_le]) (use b_nonneg in simp)
  finally have "(2 * ?b) powr (1 / 3) \<le> 2 * (?b powr (1 / 3))" .
  then show ?thesis
    unfolding sssp_log_factor_one_third_def using powr_le by linarith
qed

lemma sssp_log_factor_one_third_square:
  "sssp_log_factor_one_third n * sssp_log_factor_one_third n =
    sssp_log_factor n"
proof -
  have "0 < ln (real n + 2)"
  proof -
    have "1 < real n + 2"
      by simp
    then show ?thesis
      by (rule ln_gt_zero)
  qed
  then show ?thesis
    unfolding sssp_log_factor_one_third_def sssp_log_factor_def
    by (simp add: powr_add [symmetric])
qed

lemma eventually_one_le_sssp_log_factor_one_third:
  "eventually (\<lambda>n. 1 \<le> sssp_log_factor_one_third n) at_top"
proof (rule eventually_at_top_linorderI[of 1])
  fix n :: nat
  assume n_ge: "1 \<le> n"
  have "exp 1 \<le> (3::real)"
    by (rule exp_le)
  also have "\<dots> \<le> real n + 2"
    using n_ge by simp
  finally have exp_le_arg: "exp 1 \<le> real n + 2" .
  have ln_ge: "1 \<le> ln (real n + 2)"
    using exp_le_arg by (simp add: ln_ge_iff)
  show "1 \<le> sssp_log_factor_one_third n"
    unfolding sssp_log_factor_one_third_def
    by (rule ge_one_powr_ge_zero[OF ln_ge]) simp
qed

lemma sssp_time_target_nonneg [simp]:
  "0 \<le> sssp_time_target m n"
proof -
  have "0 \<le> real (m n)"
    by simp
  moreover have "0 \<le> sssp_log_factor n"
    using sssp_log_factor_pos[of n] by linarith
  ultimately show ?thesis
    unfolding sssp_time_target_def by (rule mult_nonneg_nonneg)
qed

theorem sssp_time_target_bigoI_norm:
  assumes C: "0 < C"
    and eventually_bound:
      "eventually
        (\<lambda>n. norm (real (T n)) \<le> C * norm (sssp_time_target m n)) at_top"
  shows "(\<lambda>n. real (T n)) \<in> O(\<lambda>n. sssp_time_target m n)"
  using C eventually_bound unfolding bigo_def by blast

theorem sssp_time_target_bigoI:
  assumes C: "0 < C"
    and eventually_bound:
      "eventually (\<lambda>n. real (T n) \<le> C * sssp_time_target m n) at_top"
  shows "(\<lambda>n. real (T n)) \<in> O(\<lambda>n. sssp_time_target m n)"
proof (rule sssp_time_target_bigoI_norm[OF C])
  show "eventually
      (\<lambda>n. norm (real (T n)) \<le> C * norm (sssp_time_target m n)) at_top"
    using eventually_bound
  proof eventually_elim
    case (elim n)
    then show ?case
      by simp
  qed
qed

definition bmssp_graph_time_bound where
  "bmssp_graph_time_bound A R l t m n =
    2 * A n * (2 * l n + 1) * n + (R n + l n * t n) * m n"

theorem bmssp_graph_time_bound_bigo_sssp_time_target:
  assumes Cn_pos: "0 < Cn"
    and Cv_pos: "0 < Cv"
    and Ce_pos: "0 < Ce"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real n \<le> Cn * real (m n)) at_top"
    and vertex_factor:
      "eventually
        (\<lambda>n. real (2 * A n * (2 * l n + 1)) \<le>
          Cv * sssp_log_factor n) at_top"
    and edge_factor:
      "eventually
        (\<lambda>n. real (R n + l n * t n) \<le>
          Ce * sssp_log_factor n) at_top"
  shows "(\<lambda>n. real (bmssp_graph_time_bound A R l t m n))
    \<in> O(\<lambda>n. sssp_time_target m n)"
proof (rule sssp_time_target_bigoI[where C = "Cv * Cn + Ce"])
  show "0 < Cv * Cn + Ce"
  proof -
    have "0 < Cv * Cn"
      using Cv_pos Cn_pos by (rule mult_pos_pos)
    then show ?thesis
      using Ce_pos by linarith
  qed
next
  show "eventually
      (\<lambda>n. real (bmssp_graph_time_bound A R l t m n) \<le>
        (Cv * Cn + Ce) * sssp_time_target m n) at_top"
    using vertex_count_dominated vertex_factor edge_factor
  proof eventually_elim
    case (elim n)
    let ?vf = "real (2 * A n * (2 * l n + 1))"
    let ?ef = "real (R n + l n * t n)"
    let ?log = "sssp_log_factor n"
    have vertex:
      "?vf * real n \<le> (Cv * ?log) * (Cn * real (m n))"
    proof (rule mult_mono)
      show "?vf \<le> Cv * ?log"
        using elim(2) .
      show "real n \<le> Cn * real (m n)"
        using elim(1) .
      show "0 \<le> real n"
        by simp
      show "0 \<le> Cv * ?log"
      proof -
        have "0 \<le> Cv"
          using Cv_pos by linarith
        moreover have "0 \<le> ?log"
          using sssp_log_factor_pos[of n] by linarith
        ultimately show ?thesis
          by (rule mult_nonneg_nonneg)
      qed
    qed
    also have "\<dots> = (Cv * Cn) * (real (m n) * ?log)"
      by (simp add: algebra_simps)
    finally have vertex':
      "?vf * real n \<le> (Cv * Cn) * (real (m n) * ?log)" .
    have edge:
      "?ef * real (m n) \<le> (Ce * ?log) * real (m n)"
      by (rule mult_right_mono[OF elim(3)]) simp
    also have "\<dots> = Ce * (real (m n) * ?log)"
      by (simp add: algebra_simps)
    finally have edge':
      "?ef * real (m n) \<le> Ce * (real (m n) * ?log)" .
    have "real (bmssp_graph_time_bound A R l t m n) =
        ?vf * real n + ?ef * real (m n)"
      unfolding bmssp_graph_time_bound_def by simp
    also have "\<dots> \<le>
        (Cv * Cn) * (real (m n) * ?log) +
        Ce * (real (m n) * ?log)"
      using vertex' edge' by linarith
    also have "\<dots> = (Cv * Cn + Ce) * sssp_time_target m n"
      unfolding sssp_time_target_def by (simp add: algebra_simps)
    finally show ?case .
  qed
qed

theorem bmssp_cost_bound_bigo_sssp_time_target:
  assumes Cn_pos: "0 < Cn"
    and Cv_pos: "0 < Cv"
    and Ce_pos: "0 < Ce"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real n \<le> Cn * real (m n)) at_top"
    and vertex_factor:
      "eventually
        (\<lambda>n. real (2 * A n * (2 * l n + 1)) \<le>
          Cv * sssp_log_factor n) at_top"
    and edge_factor:
      "eventually
        (\<lambda>n. real (R n + l n * t n) \<le>
          Ce * sssp_log_factor n) at_top"
    and cost_bound:
      "eventually (\<lambda>n. T n \<le> bmssp_graph_time_bound A R l t m n) at_top"
  shows "(\<lambda>n. real (T n)) \<in> O(\<lambda>n. sssp_time_target m n)"
proof -
  have graph:
    "(\<lambda>n. real (bmssp_graph_time_bound A R l t m n))
      \<in> O(\<lambda>n. sssp_time_target m n)"
    by (rule bmssp_graph_time_bound_bigo_sssp_time_target
      [OF Cn_pos Cv_pos Ce_pos vertex_count_dominated vertex_factor
        edge_factor])
  then obtain C where C_pos: "0 < C"
    and eventually_graph:
      "eventually
        (\<lambda>n. norm (real (bmssp_graph_time_bound A R l t m n)) \<le>
          C * norm (sssp_time_target m n)) at_top"
    unfolding bigo_def by blast
  show ?thesis
  proof (rule sssp_time_target_bigoI_norm[OF C_pos])
    show "eventually
        (\<lambda>n. norm (real (T n)) \<le> C * norm (sssp_time_target m n)) at_top"
      using cost_bound eventually_graph
    proof eventually_elim
      case (elim n)
      have "norm (real (T n)) \<le>
          norm (real (bmssp_graph_time_bound A R l t m n))"
        using elim(1) by simp
      also have "\<dots> \<le> C * norm (sssp_time_target m n)"
        using elim(2) .
      finally show ?case .
    qed
  qed
qed

definition bmssp_refined_graph_time_bound where
  "bmssp_refined_graph_time_bound A R H l t m n =
    2 * A n * (2 * l n + 1) * n +
    (R n + t n + l n * H n) * m n"

theorem bmssp_refined_graph_time_bound_bigo_sssp_time_target:
  assumes Cn_pos: "0 < Cn"
    and Cv_pos: "0 < Cv"
    and Ce_pos: "0 < Ce"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real n \<le> Cn * real (m n)) at_top"
    and vertex_factor:
      "eventually
        (\<lambda>n. real (2 * A n * (2 * l n + 1)) \<le>
          Cv * sssp_log_factor n) at_top"
    and edge_factor:
      "eventually
        (\<lambda>n. real (R n + t n + l n * H n) \<le>
          Ce * sssp_log_factor n) at_top"
  shows "(\<lambda>n. real (bmssp_refined_graph_time_bound A R H l t m n))
    \<in> O(\<lambda>n. sssp_time_target m n)"
proof (rule sssp_time_target_bigoI[where C = "Cv * Cn + Ce"])
  show "0 < Cv * Cn + Ce"
  proof -
    have "0 < Cv * Cn"
      using Cv_pos Cn_pos by (rule mult_pos_pos)
    then show ?thesis
      using Ce_pos by linarith
  qed
next
  show "eventually
      (\<lambda>n. real (bmssp_refined_graph_time_bound A R H l t m n) \<le>
        (Cv * Cn + Ce) * sssp_time_target m n) at_top"
    using vertex_count_dominated vertex_factor edge_factor
  proof eventually_elim
    case (elim n)
    let ?vf = "real (2 * A n * (2 * l n + 1))"
    let ?ef = "real (R n + t n + l n * H n)"
    let ?log = "sssp_log_factor n"
    have vertex:
      "?vf * real n \<le> (Cv * ?log) * (Cn * real (m n))"
    proof (rule mult_mono)
      show "?vf \<le> Cv * ?log"
        using elim(2) .
      show "real n \<le> Cn * real (m n)"
        using elim(1) .
      show "0 \<le> real n"
        by simp
      show "0 \<le> Cv * ?log"
      proof -
        have "0 \<le> Cv"
          using Cv_pos by linarith
        moreover have "0 \<le> ?log"
          using sssp_log_factor_pos[of n] by linarith
        ultimately show ?thesis
          by (rule mult_nonneg_nonneg)
      qed
    qed
    also have "\<dots> = (Cv * Cn) * (real (m n) * ?log)"
      by (simp add: algebra_simps)
    finally have vertex':
      "?vf * real n \<le> (Cv * Cn) * (real (m n) * ?log)" .
    have edge:
      "?ef * real (m n) \<le> (Ce * ?log) * real (m n)"
      by (rule mult_right_mono[OF elim(3)]) simp
    also have "\<dots> = Ce * (real (m n) * ?log)"
      by (simp add: algebra_simps)
    finally have edge':
      "?ef * real (m n) \<le> Ce * (real (m n) * ?log)" .
    have "real (bmssp_refined_graph_time_bound A R H l t m n) =
        ?vf * real n + ?ef * real (m n)"
      unfolding bmssp_refined_graph_time_bound_def by simp
    also have "\<dots> \<le>
        (Cv * Cn) * (real (m n) * ?log) +
        Ce * (real (m n) * ?log)"
      using vertex' edge' by linarith
    also have "\<dots> = (Cv * Cn + Ce) * sssp_time_target m n"
      unfolding sssp_time_target_def by (simp add: algebra_simps)
    finally show ?case .
  qed
qed

theorem bmssp_refined_cost_bound_bigo_sssp_time_target:
  assumes Cn_pos: "0 < Cn"
    and Cv_pos: "0 < Cv"
    and Ce_pos: "0 < Ce"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real n \<le> Cn * real (m n)) at_top"
    and vertex_factor:
      "eventually
        (\<lambda>n. real (2 * A n * (2 * l n + 1)) \<le>
          Cv * sssp_log_factor n) at_top"
    and edge_factor:
      "eventually
        (\<lambda>n. real (R n + t n + l n * H n) \<le>
          Ce * sssp_log_factor n) at_top"
    and cost_bound:
      "eventually
        (\<lambda>n. T n \<le> bmssp_refined_graph_time_bound A R H l t m n) at_top"
  shows "(\<lambda>n. real (T n)) \<in> O(\<lambda>n. sssp_time_target m n)"
proof -
  have graph:
    "(\<lambda>n. real (bmssp_refined_graph_time_bound A R H l t m n))
      \<in> O(\<lambda>n. sssp_time_target m n)"
    by (rule bmssp_refined_graph_time_bound_bigo_sssp_time_target
      [OF Cn_pos Cv_pos Ce_pos vertex_count_dominated vertex_factor
        edge_factor])
  then obtain C where C_pos: "0 < C"
    and eventually_graph:
      "eventually
        (\<lambda>n. norm (real (bmssp_refined_graph_time_bound A R H l t m n)) \<le>
          C * norm (sssp_time_target m n)) at_top"
    unfolding bigo_def by blast
  show ?thesis
  proof (rule sssp_time_target_bigoI_norm[OF C_pos])
    show "eventually
        (\<lambda>n. norm (real (T n)) \<le> C * norm (sssp_time_target m n)) at_top"
      using cost_bound eventually_graph
    proof eventually_elim
      case (elim n)
      have "norm (real (T n)) \<le>
          norm (real (bmssp_refined_graph_time_bound A R H l t m n))"
        using elim(1) by simp
      also have "\<dots> \<le> C * norm (sssp_time_target m n)"
        using elim(2) .
      finally show ?case .
    qed
  qed
qed

theorem bmssp_refined_cost_bound_bigo_sssp_time_target_from_component_bounds:
  assumes Cn_pos: "0 < Cn"
    and Ca_pos: "0 < Ca"
    and Cl_nonneg: "0 \<le> Cl"
    and Cr_pos: "0 < Cr"
    and Ct_pos: "0 < Ct"
    and Ch_pos: "0 < Ch"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real n \<le> Cn * real (m n)) at_top"
    and A_bound:
      "eventually
        (\<lambda>n. real (A n) \<le> Ca * sssp_log_factor_one_third n) at_top"
    and l_bound:
      "eventually
        (\<lambda>n. real (l n) \<le> Cl * sssp_log_factor_one_third n) at_top"
    and R_bound:
      "eventually
        (\<lambda>n. real (R n) \<le> Cr * sssp_log_factor n) at_top"
    and t_bound:
      "eventually
        (\<lambda>n. real (t n) \<le> Ct * sssp_log_factor n) at_top"
    and H_bound:
      "eventually
        (\<lambda>n. real (H n) \<le> Ch * sssp_log_factor_one_third n) at_top"
    and cost_bound:
      "eventually
        (\<lambda>n. T n \<le> bmssp_refined_graph_time_bound A R H l t m n) at_top"
  shows "(\<lambda>n. real (T n)) \<in> O(\<lambda>n. sssp_time_target m n)"
proof (rule bmssp_refined_cost_bound_bigo_sssp_time_target
    [where Cn = Cn and Cv = "2 * Ca * (2 * Cl + 1)"
      and Ce = "Cr + Ct + Cl * Ch"])
  show "0 < Cn"
    using Cn_pos .
  show "0 < 2 * Ca * (2 * Cl + 1)"
    using Ca_pos Cl_nonneg by (intro mult_pos_pos) simp_all
  show "0 < Cr + Ct + Cl * Ch"
  proof -
    have "0 \<le> Cl * Ch"
      using Cl_nonneg Ch_pos by simp
    then show ?thesis
      using Cr_pos Ct_pos by linarith
  qed
  show "eventually (\<lambda>n. real n \<le> Cn * real (m n)) at_top"
    using vertex_count_dominated .
  show "eventually
      (\<lambda>n. real (2 * A n * (2 * l n + 1)) \<le>
        2 * Ca * (2 * Cl + 1) * sssp_log_factor n) at_top"
    using A_bound l_bound eventually_one_le_sssp_log_factor_one_third
  proof eventually_elim
    case (elim n)
    let ?L = "sssp_log_factor_one_third n"
    have L_nonneg: "0 \<le> ?L"
      using sssp_log_factor_one_third_pos[of n] by linarith
    have A_le: "real (A n) \<le> Ca * ?L"
      using elim(1) .
    have l_le: "real (2 * l n + 1) \<le> (2 * Cl + 1) * ?L"
    proof -
      have "real (2 * l n + 1) = 2 * real (l n) + 1"
        by simp
      also have "\<dots> \<le> 2 * (Cl * ?L) + 1"
        using elim(2) by linarith
      also have "\<dots> \<le> 2 * (Cl * ?L) + ?L"
        using elim(3) by linarith
      also have "\<dots> = (2 * Cl + 1) * ?L"
        by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    have l_rhs_nonneg: "0 \<le> (2 * Cl + 1) * ?L"
      using Cl_nonneg L_nonneg by (intro mult_nonneg_nonneg) simp_all
    have prod:
      "real (A n) * real (2 * l n + 1) \<le>
        (Ca * ?L) * ((2 * Cl + 1) * ?L)"
      by (rule mult_mono[OF A_le l_le]) (use L_nonneg Ca_pos l_rhs_nonneg in simp_all)
    have "real (2 * A n * (2 * l n + 1)) =
        2 * (real (A n) * real (2 * l n + 1))"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> 2 * ((Ca * ?L) * ((2 * Cl + 1) * ?L))"
      using prod by simp
    also have "\<dots> = 2 * Ca * (2 * Cl + 1) * sssp_log_factor n"
      using sssp_log_factor_one_third_square[of n]
      by (simp add: algebra_simps)
    finally show ?case .
  qed
  show "eventually
      (\<lambda>n. real (R n + t n + l n * H n) \<le>
        (Cr + Ct + Cl * Ch) * sssp_log_factor n) at_top"
    using R_bound t_bound l_bound H_bound
  proof eventually_elim
    case (elim n)
    let ?L = "sssp_log_factor_one_third n"
    have L_nonneg: "0 \<le> ?L"
      using sssp_log_factor_one_third_pos[of n] by linarith
    have lH:
      "real (l n * H n) \<le> (Cl * Ch) * sssp_log_factor n"
    proof -
      have prod:
        "real (l n) * real (H n) \<le> (Cl * ?L) * (Ch * ?L)"
        by (rule mult_mono[OF elim(3) elim(4)])
          (use Cl_nonneg Ch_pos L_nonneg in simp_all)
      have "real (l n * H n) = real (l n) * real (H n)"
        by simp
      also have "\<dots> \<le> (Cl * ?L) * (Ch * ?L)"
        using prod .
      also have "\<dots> = (Cl * Ch) * sssp_log_factor n"
        using sssp_log_factor_one_third_square[of n]
        by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    have "real (R n + t n + l n * H n) =
        real (R n) + real (t n) + real (l n * H n)"
      by simp
    also have "\<dots> \<le>
        Cr * sssp_log_factor n + Ct * sssp_log_factor n +
        (Cl * Ch) * sssp_log_factor n"
      using elim(1) elim(2) lH by linarith
    also have "\<dots> = (Cr + Ct + Cl * Ch) * sssp_log_factor n"
      by (simp add: algebra_simps)
    finally show ?case .
  qed
  show "eventually
      (\<lambda>n. T n \<le> bmssp_refined_graph_time_bound A R H l t m n) at_top"
    using cost_bound .
qed

theorem bmssp_refined_graph_time_bound_bigo_sssp_time_target_slack:
  assumes Cn_pos: "0 < Cn"
    and Cm_pos: "0 < Cm"
    and Cv_pos: "0 < Cv"
    and Ce_pos: "0 < Ce"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real (v n) \<le> Cn * real (m n)) at_top"
    and edge_count_dominated:
      "eventually (\<lambda>n. real (m' n) \<le> Cm * real (m n)) at_top"
    and vertex_factor:
      "eventually
        (\<lambda>n. real (2 * A n * (2 * l n + 1)) \<le>
          Cv * sssp_log_factor n) at_top"
    and edge_factor:
      "eventually
        (\<lambda>n. real (R n + t n + l n * H n) \<le>
          Ce * sssp_log_factor n) at_top"
  shows "(\<lambda>n. real (bmssp_refined_graph_time_bound
      (\<lambda>_. A n) (\<lambda>_. R n) (\<lambda>_. H n) (\<lambda>_. l n) (\<lambda>_. t n)
      (\<lambda>_. m' n) (v n)))
    \<in> O(\<lambda>n. sssp_time_target m n)"
proof (rule sssp_time_target_bigoI[where C = "Cv * Cn + Ce * Cm"])
  show "0 < Cv * Cn + Ce * Cm"
  proof -
    have "0 < Cv * Cn"
      using Cv_pos Cn_pos by (rule mult_pos_pos)
    moreover have "0 < Ce * Cm"
      using Ce_pos Cm_pos by (rule mult_pos_pos)
    ultimately show ?thesis
      by linarith
  qed
next
  show "eventually
      (\<lambda>n. real (bmssp_refined_graph_time_bound
          (\<lambda>_. A n) (\<lambda>_. R n) (\<lambda>_. H n) (\<lambda>_. l n) (\<lambda>_. t n)
          (\<lambda>_. m' n) (v n)) \<le>
        (Cv * Cn + Ce * Cm) * sssp_time_target m n) at_top"
    using vertex_count_dominated edge_count_dominated vertex_factor edge_factor
  proof eventually_elim
    case (elim n)
    let ?vf = "real (2 * A n * (2 * l n + 1))"
    let ?ef = "real (R n + t n + l n * H n)"
    let ?log = "sssp_log_factor n"
    have vertex:
      "?vf * real (v n) \<le> (Cv * ?log) * (Cn * real (m n))"
    proof (rule mult_mono)
      show "?vf \<le> Cv * ?log"
        using elim(3) .
      show "real (v n) \<le> Cn * real (m n)"
        using elim(1) .
      show "0 \<le> real (v n)"
        by simp
      show "0 \<le> Cv * ?log"
      proof -
        have "0 \<le> Cv"
          using Cv_pos by linarith
        moreover have "0 \<le> ?log"
          using sssp_log_factor_pos[of n] by linarith
        ultimately show ?thesis
          by (rule mult_nonneg_nonneg)
      qed
    qed
    also have "\<dots> = (Cv * Cn) * (real (m n) * ?log)"
      by (simp add: algebra_simps)
    finally have vertex':
      "?vf * real (v n) \<le> (Cv * Cn) * (real (m n) * ?log)" .
    have edge:
      "?ef * real (m' n) \<le> (Ce * ?log) * (Cm * real (m n))"
    proof (rule mult_mono)
      show "?ef \<le> Ce * ?log"
        using elim(4) .
      show "real (m' n) \<le> Cm * real (m n)"
        using elim(2) .
      show "0 \<le> real (m' n)"
        by simp
      show "0 \<le> Ce * ?log"
      proof -
        have "0 \<le> Ce"
          using Ce_pos by linarith
        moreover have "0 \<le> ?log"
          using sssp_log_factor_pos[of n] by linarith
        ultimately show ?thesis
          by (rule mult_nonneg_nonneg)
      qed
    qed
    also have "\<dots> = (Ce * Cm) * (real (m n) * ?log)"
      by (simp add: algebra_simps)
    finally have edge':
      "?ef * real (m' n) \<le> (Ce * Cm) * (real (m n) * ?log)" .
    have "real (bmssp_refined_graph_time_bound
          (\<lambda>_. A n) (\<lambda>_. R n) (\<lambda>_. H n) (\<lambda>_. l n) (\<lambda>_. t n)
          (\<lambda>_. m' n) (v n)) =
        ?vf * real (v n) + ?ef * real (m' n)"
      unfolding bmssp_refined_graph_time_bound_def by simp
    also have "\<dots> \<le>
        (Cv * Cn) * (real (m n) * ?log) +
        (Ce * Cm) * (real (m n) * ?log)"
      using vertex' edge' by linarith
    also have "\<dots> = (Cv * Cn + Ce * Cm) * sssp_time_target m n"
      unfolding sssp_time_target_def by (simp add: algebra_simps)
    finally show ?case .
  qed
qed

theorem bmssp_refined_cost_bound_bigo_sssp_time_target_from_component_bounds_slack:
  assumes Cn_pos: "0 < Cn"
    and Cm_pos: "0 < Cm"
    and Ca_pos: "0 < Ca"
    and Cl_nonneg: "0 \<le> Cl"
    and Cr_pos: "0 < Cr"
    and Ct_pos: "0 < Ct"
    and Ch_pos: "0 < Ch"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real (v n) \<le> Cn * real (m n)) at_top"
    and edge_count_dominated:
      "eventually (\<lambda>n. real (m' n) \<le> Cm * real (m n)) at_top"
    and A_bound:
      "eventually
        (\<lambda>n. real (A n) \<le> Ca * sssp_log_factor_one_third n) at_top"
    and l_bound:
      "eventually
        (\<lambda>n. real (l n) \<le> Cl * sssp_log_factor_one_third n) at_top"
    and R_bound:
      "eventually
        (\<lambda>n. real (R n) \<le> Cr * sssp_log_factor n) at_top"
    and t_bound:
      "eventually
        (\<lambda>n. real (t n) \<le> Ct * sssp_log_factor n) at_top"
    and H_bound:
      "eventually
        (\<lambda>n. real (H n) \<le> Ch * sssp_log_factor_one_third n) at_top"
    and cost_bound:
      "eventually
        (\<lambda>n. T n \<le> bmssp_refined_graph_time_bound
          (\<lambda>_. A n) (\<lambda>_. R n) (\<lambda>_. H n) (\<lambda>_. l n) (\<lambda>_. t n)
          (\<lambda>_. m' n) (v n)) at_top"
  shows "(\<lambda>n. real (T n)) \<in> O(\<lambda>n. sssp_time_target m n)"
proof -
  have Cv_pos: "0 < 2 * Ca * (2 * Cl + 1)"
    using Ca_pos Cl_nonneg by (intro mult_pos_pos) simp_all
  have Ce_pos: "0 < Cr + Ct + Cl * Ch"
  proof -
    have "0 \<le> Cl * Ch"
      using Cl_nonneg Ch_pos by simp
    then show ?thesis
      using Cr_pos Ct_pos by linarith
  qed
  have vertex_factor:
    "eventually
      (\<lambda>n. real (2 * A n * (2 * l n + 1)) \<le>
        2 * Ca * (2 * Cl + 1) * sssp_log_factor n) at_top"
    using A_bound l_bound eventually_one_le_sssp_log_factor_one_third
  proof eventually_elim
    case (elim n)
    let ?L = "sssp_log_factor_one_third n"
    have L_nonneg: "0 \<le> ?L"
      using sssp_log_factor_one_third_pos[of n] by linarith
    have A_le: "real (A n) \<le> Ca * ?L"
      using elim(1) .
    have l_le: "real (2 * l n + 1) \<le> (2 * Cl + 1) * ?L"
    proof -
      have "real (2 * l n + 1) = 2 * real (l n) + 1"
        by simp
      also have "\<dots> \<le> 2 * (Cl * ?L) + 1"
        using elim(2) by linarith
      also have "\<dots> \<le> 2 * (Cl * ?L) + ?L"
        using elim(3) by linarith
      also have "\<dots> = (2 * Cl + 1) * ?L"
        by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    have l_rhs_nonneg: "0 \<le> (2 * Cl + 1) * ?L"
      using Cl_nonneg L_nonneg by (intro mult_nonneg_nonneg) simp_all
    have prod:
      "real (A n) * real (2 * l n + 1) \<le>
        (Ca * ?L) * ((2 * Cl + 1) * ?L)"
      by (rule mult_mono[OF A_le l_le])
        (use L_nonneg Ca_pos l_rhs_nonneg in simp_all)
    have "real (2 * A n * (2 * l n + 1)) =
        2 * (real (A n) * real (2 * l n + 1))"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> 2 * ((Ca * ?L) * ((2 * Cl + 1) * ?L))"
      using prod by simp
    also have "\<dots> = 2 * Ca * (2 * Cl + 1) * sssp_log_factor n"
      using sssp_log_factor_one_third_square[of n]
      by (simp add: algebra_simps)
    finally show ?case .
  qed
  have edge_factor:
    "eventually
      (\<lambda>n. real (R n + t n + l n * H n) \<le>
        (Cr + Ct + Cl * Ch) * sssp_log_factor n) at_top"
    using R_bound t_bound l_bound H_bound
  proof eventually_elim
    case (elim n)
    let ?L = "sssp_log_factor_one_third n"
    have L_nonneg: "0 \<le> ?L"
      using sssp_log_factor_one_third_pos[of n] by linarith
    have lH:
      "real (l n * H n) \<le> (Cl * Ch) * sssp_log_factor n"
    proof -
      have prod:
        "real (l n) * real (H n) \<le> (Cl * ?L) * (Ch * ?L)"
        by (rule mult_mono[OF elim(3) elim(4)])
          (use Cl_nonneg Ch_pos L_nonneg in simp_all)
      have "real (l n * H n) = real (l n) * real (H n)"
        by simp
      also have "\<dots> \<le> (Cl * ?L) * (Ch * ?L)"
        using prod .
      also have "\<dots> = (Cl * Ch) * sssp_log_factor n"
        using sssp_log_factor_one_third_square[of n]
        by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    have "real (R n + t n + l n * H n) =
        real (R n) + real (t n) + real (l n * H n)"
      by simp
    also have "\<dots> \<le>
        Cr * sssp_log_factor n + Ct * sssp_log_factor n +
        (Cl * Ch) * sssp_log_factor n"
      using elim(1) elim(2) lH by linarith
    also have "\<dots> = (Cr + Ct + Cl * Ch) * sssp_log_factor n"
      by (simp add: algebra_simps)
    finally show ?case .
  qed
  have graph:
    "(\<lambda>n. real (bmssp_refined_graph_time_bound
        (\<lambda>_. A n) (\<lambda>_. R n) (\<lambda>_. H n) (\<lambda>_. l n) (\<lambda>_. t n)
        (\<lambda>_. m' n) (v n)))
      \<in> O(\<lambda>n. sssp_time_target m n)"
    by (rule bmssp_refined_graph_time_bound_bigo_sssp_time_target_slack
      [OF Cn_pos Cm_pos Cv_pos Ce_pos vertex_count_dominated
        edge_count_dominated vertex_factor edge_factor])
  then obtain C where C_pos: "0 < C"
    and eventually_graph:
      "eventually
        (\<lambda>n. norm (real (bmssp_refined_graph_time_bound
          (\<lambda>_. A n) (\<lambda>_. R n) (\<lambda>_. H n) (\<lambda>_. l n) (\<lambda>_. t n)
          (\<lambda>_. m' n) (v n))) \<le>
          C * norm (sssp_time_target m n)) at_top"
    unfolding bigo_def by blast
  show ?thesis
  proof (rule sssp_time_target_bigoI_norm[OF C_pos])
    show "eventually
        (\<lambda>n. norm (real (T n)) \<le> C * norm (sssp_time_target m n)) at_top"
      using cost_bound eventually_graph
    proof eventually_elim
      case (elim n)
      have "norm (real (T n)) \<le>
          norm (real (bmssp_refined_graph_time_bound
            (\<lambda>_. A n) (\<lambda>_. R n) (\<lambda>_. H n) (\<lambda>_. l n) (\<lambda>_. t n)
            (\<lambda>_. m' n) (v n)))"
        using elim(1) by simp
      also have "\<dots> \<le> C * norm (sssp_time_target m n)"
        using elim(2) .
      finally show ?case .
    qed
  qed
qed

section \<open>Logarithmic Parameter Schedule\<close>

text \<open>
  The paper's schedule balances two logarithmic scales.  The parameter usually
  called \<open>k\<close> is chosen on the order of \<open>log^(1/3) n\<close>, while the recursion
  depth and partition width use the corresponding \<open>log^(2/3) n\<close> scale.  The
  two definitions below use ceilings of the real-valued factors so that the
  executable and inductive parameters remain natural numbers.

  The lemmas in this section are mostly analytic bookkeeping.  They show that
  the ceiling parameters are eventually positive, monotone enough for the
  recurrence, and asymptotically within constant factors of the real logarithmic
  targets.  Those facts are what let the refined graph-time expressions be
  rewritten as \<open>O(m * log^(2/3) n)\<close>.
\<close>

definition sssp_log_one_third_param where
  "sssp_log_one_third_param n = nat \<lceil>sssp_log_factor_one_third n\<rceil>"

definition sssp_log_two_thirds_param where
  "sssp_log_two_thirds_param n = nat \<lceil>sssp_log_factor n\<rceil>"

lemma sssp_log_one_third_param_pos [simp]:
  "0 < sssp_log_one_third_param n"
  unfolding sssp_log_one_third_param_def
  using sssp_log_factor_one_third_pos[of n] by simp

lemma sssp_log_two_thirds_param_pos [simp]:
  "0 < sssp_log_two_thirds_param n"
  unfolding sssp_log_two_thirds_param_def
  using sssp_log_factor_pos[of n] by simp

lemma real_cuberoot_at_top:
  "filterlim (\<lambda>x::real. root 3 x) at_top at_top"
  by (rule filterlim_at_top_at_top
      [where Q = "\<lambda>x. True" and P = "\<lambda>x. True" and g = "\<lambda>x. x ^ 3"])
    (auto intro: real_root_le_mono simp: odd_real_root_power_cancel)

lemma sssp_log_factor_one_third_at_top:
  "filterlim sssp_log_factor_one_third at_top at_top"
proof -
  have ln_at_top':
    "filterlim (\<lambda>n::nat. ln (real (n + 2))) at_top at_top"
    by (intro filterlim_compose[OF ln_at_top]
        filterlim_compose[OF filterlim_real_sequentially]
        filterlim_add_const_nat_at_top)
  have root_ln_at_top:
    "filterlim (\<lambda>n::nat. root 3 (ln (real (n + 2)))) at_top at_top"
    by (rule filterlim_compose[OF real_cuberoot_at_top ln_at_top'])
  have eq:
    "(\<lambda>n::nat. root 3 (ln (real (n + 2)))) = sssp_log_factor_one_third"
  proof
    fix n :: nat
    have ln_nonneg: "0 \<le> ln (real (n + 2))"
      by simp
    have "root 3 (ln (real (n + 2))) =
        ln (real (n + 2)) powr (1 / 3)"
      using root_powr_inverse[of 3 "ln (real (n + 2))"] ln_nonneg
      by simp
    then show "root 3 (ln (real (n + 2))) = sssp_log_factor_one_third n"
      unfolding sssp_log_factor_one_third_def
      by (simp add: add.commute)
  qed
  show ?thesis
    using root_ln_at_top unfolding eq .
qed

lemma nat_ceiling_at_top:
  "filterlim (\<lambda>x::real. nat \<lceil>x\<rceil>) at_top at_top"
proof (rule filterlim_at_top_at_top
    [where Q = "\<lambda>x. 0 \<le> x" and P = "\<lambda>_::nat. True" and g = real])
  fix x y :: real
  assume x_nonneg: "0 \<le> x" and y_nonneg: "0 \<le> y" and xy: "x \<le> y"
  have "\<lceil>x\<rceil> \<le> \<lceil>y\<rceil>"
    by (rule ceiling_mono[OF xy])
  then show "nat \<lceil>x\<rceil> \<le> nat \<lceil>y\<rceil>"
    by (rule nat_mono)
next
  fix n :: nat
  show "nat \<lceil>real n\<rceil> = n"
    by simp
next
  fix n :: nat
  show "0 \<le> real n"
    by simp
next
  show "eventually (\<lambda>x::real. 0 \<le> x) at_top"
    by (rule eventually_ge_at_top)
next
  show "eventually (\<lambda>_::nat. True) at_top"
    by simp
qed

lemma sssp_log_one_third_param_at_top:
  "filterlim sssp_log_one_third_param at_top at_top"
  unfolding sssp_log_one_third_param_def
  by (rule filterlim_compose
    [OF nat_ceiling_at_top sssp_log_factor_one_third_at_top])

lemma eventually_less_sssp_log_one_third_param:
  "eventually (\<lambda>n. K < sssp_log_one_third_param n) at_top"
proof -
  have "eventually (\<lambda>n. Suc K \<le> sssp_log_one_third_param n) at_top"
    using sssp_log_one_third_param_at_top
    unfolding filterlim_at_top by blast
  then show ?thesis
    by eventually_elim simp
qed

lemma sssp_log_two_thirds_param_le_one_third_square:
  "sssp_log_two_thirds_param n \<le>
    sssp_log_one_third_param n * sssp_log_one_third_param n"
proof -
  let ?L = "sssp_log_factor_one_third n"
  let ?p = "sssp_log_one_third_param n"
  have L_nonneg: "0 \<le> ?L"
    using sssp_log_factor_one_third_pos[of n] by linarith
  have L_le_p: "?L \<le> real ?p"
    unfolding sssp_log_one_third_param_def
    using L_nonneg by simp
  have "sssp_log_factor n \<le> real (?p * ?p)"
  proof -
    have "?L * ?L \<le> real ?p * real ?p"
      by (rule mult_mono[OF L_le_p L_le_p])
        (use L_nonneg in simp_all)
    then show ?thesis
      using sssp_log_factor_one_third_square[of n] by simp
  qed
  then show ?thesis
    unfolding sssp_log_two_thirds_param_def by simp
qed

lemma real_nat_ceiling_le_twice:
  fixes x :: real
  assumes "1 \<le> x"
  shows "real (nat \<lceil>x\<rceil>) \<le> 2 * x"
proof -
  have x_nonneg: "0 \<le> x"
    using assms by linarith
  have ceil_nat: "real (nat \<lceil>x\<rceil>) = of_int \<lceil>x\<rceil>"
    using of_nat_int_ceiling[OF x_nonneg] .
  have "of_int \<lceil>x\<rceil> - 1 < x"
    using ceiling_correct[of x] by blast
  then have "of_int \<lceil>x\<rceil> \<le> x + 1"
    by linarith
  also have "\<dots> \<le> 2 * x"
    using assms by linarith
  finally show ?thesis
    unfolding ceil_nat .
qed

lemma eventually_one_le_sssp_log_factor:
  "eventually (\<lambda>n. 1 \<le> sssp_log_factor n) at_top"
  using eventually_one_le_sssp_log_factor_one_third
proof eventually_elim
  case (elim n)
  let ?L = "sssp_log_factor_one_third n"
  have "1 \<le> ?L * ?L"
  proof -
    have L_nonneg: "0 \<le> ?L"
      using elim by linarith
    have "(1::real) * 1 \<le> ?L * ?L"
      by (rule mult_mono[OF elim elim]) (simp_all add: L_nonneg)
    then show ?thesis
      by simp
  qed
  then show ?case
    using sssp_log_factor_one_third_square[of n] by simp
qed

lemma sssp_log_one_third_param_component_bound:
  "eventually
    (\<lambda>n. real (sssp_log_one_third_param n) \<le>
      2 * sssp_log_factor_one_third n) at_top"
  using eventually_one_le_sssp_log_factor_one_third
proof eventually_elim
  case (elim n)
  show ?case
    unfolding sssp_log_one_third_param_def
    by (rule real_nat_ceiling_le_twice[OF elim])
qed

lemma sssp_log_two_thirds_param_component_bound:
  "eventually
    (\<lambda>n. real (sssp_log_two_thirds_param n) \<le>
      2 * sssp_log_factor n) at_top"
  using eventually_one_le_sssp_log_factor
proof eventually_elim
  case (elim n)
  show ?case
    unfolding sssp_log_two_thirds_param_def
    by (rule real_nat_ceiling_le_twice[OF elim])
qed

lemma sssp_log_one_third_param_square_arg_component_bound:
  "eventually
    (\<lambda>n. real (sssp_log_one_third_param (n * n)) \<le>
      4 * sssp_log_factor_one_third n) at_top"
proof (rule eventually_at_top_linorderI[of 1])
  fix n :: nat
  assume n_ge: "1 \<le> n"
  have one_le: "1 \<le> sssp_log_factor_one_third (n * n)"
  proof -
    have "1 \<le> sssp_log_factor_one_third n"
    proof -
      have "exp 1 \<le> (3::real)"
        by (rule exp_le)
      also have "\<dots> \<le> real n + 2"
        using n_ge by simp
      finally have exp_le_arg: "exp 1 \<le> real n + 2" .
      have ln_ge: "1 \<le> ln (real n + 2)"
        using exp_le_arg by (simp add: ln_ge_iff)
      show ?thesis
        unfolding sssp_log_factor_one_third_def
        by (rule ge_one_powr_ge_zero[OF ln_ge]) simp
    qed
    also have "\<dots> \<le> sssp_log_factor_one_third (n * n)"
      by (rule sssp_log_factor_one_third_mono) (use n_ge in simp)
    finally show ?thesis .
  qed
  have "real (sssp_log_one_third_param (n * n)) \<le>
      2 * sssp_log_factor_one_third (n * n)"
    unfolding sssp_log_one_third_param_def
    by (rule real_nat_ceiling_le_twice[OF one_le])
  also have "\<dots> \<le> 2 * (2 * sssp_log_factor_one_third n)"
    using sssp_log_factor_one_third_square_arg_le[of n] by simp
  also have "\<dots> = 4 * sssp_log_factor_one_third n"
    by simp
  finally show "real (sssp_log_one_third_param (n * n)) \<le>
      4 * sssp_log_factor_one_third n" .
qed

lemma sssp_log_two_thirds_param_square_arg_component_bound:
  "eventually
    (\<lambda>n. real (sssp_log_two_thirds_param (n * n)) \<le>
      4 * sssp_log_factor n) at_top"
proof (rule eventually_at_top_linorderI[of 1])
  fix n :: nat
  assume n_ge: "1 \<le> n"
  have one_le: "1 \<le> sssp_log_factor (n * n)"
  proof -
    have "1 \<le> sssp_log_factor n"
    proof -
      have one_third: "1 \<le> sssp_log_factor_one_third n"
      proof -
        have "exp 1 \<le> (3::real)"
          by (rule exp_le)
        also have "\<dots> \<le> real n + 2"
          using n_ge by simp
        finally have exp_le_arg: "exp 1 \<le> real n + 2" .
        have ln_ge: "1 \<le> ln (real n + 2)"
          using exp_le_arg by (simp add: ln_ge_iff)
        show ?thesis
          unfolding sssp_log_factor_one_third_def
          by (rule ge_one_powr_ge_zero[OF ln_ge]) simp
      qed
      let ?L = "sssp_log_factor_one_third n"
      have "1 \<le> ?L * ?L"
      proof -
        have L_nonneg: "0 \<le> ?L"
          using one_third by linarith
        have "(1::real) * 1 \<le> ?L * ?L"
          by (rule mult_mono[OF one_third one_third])
            (simp_all add: L_nonneg)
        then show ?thesis
          by simp
      qed
      then show ?thesis
        using sssp_log_factor_one_third_square[of n] by simp
    qed
    also have "\<dots> \<le> sssp_log_factor (n * n)"
      by (rule sssp_log_factor_mono) (use n_ge in simp)
    finally show ?thesis .
  qed
  have "real (sssp_log_two_thirds_param (n * n)) \<le>
      2 * sssp_log_factor (n * n)"
    unfolding sssp_log_two_thirds_param_def
    by (rule real_nat_ceiling_le_twice[OF one_le])
  also have "\<dots> \<le> 2 * (2 * sssp_log_factor n)"
    using sssp_log_factor_square_arg_le[of n] by simp
  also have "\<dots> = 4 * sssp_log_factor n"
    by simp
  finally show "real (sssp_log_two_thirds_param (n * n)) \<le>
      4 * sssp_log_factor n" .
qed

theorem bmssp_refined_cost_bound_bigo_sssp_time_target_log_params:
  assumes Cn_pos: "0 < Cn"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real n \<le> Cn * real (m n)) at_top"
    and cost_bound:
      "eventually
        (\<lambda>n. T n \<le>
          bmssp_refined_graph_time_bound sssp_log_one_third_param
            sssp_log_two_thirds_param sssp_log_one_third_param
            sssp_log_one_third_param sssp_log_two_thirds_param m n) at_top"
  shows "(\<lambda>n. real (T n)) \<in> O(\<lambda>n. sssp_time_target m n)"
proof (rule bmssp_refined_cost_bound_bigo_sssp_time_target_from_component_bounds
    [where Cn = Cn and Ca = 2 and Cl = 2 and Cr = 2 and Ct = 2 and Ch = 2])
  show "0 < Cn"
    using Cn_pos .
  show "0 < (2::real)"
    by simp
  show "0 \<le> (2::real)"
    by simp
  show "0 < (2::real)"
    by simp
  show "0 < (2::real)"
    by simp
  show "0 < (2::real)"
    by simp
  show "eventually (\<lambda>n. real n \<le> Cn * real (m n)) at_top"
    using vertex_count_dominated .
  show "eventually
      (\<lambda>n. real (sssp_log_one_third_param n) \<le>
        2 * sssp_log_factor_one_third n) at_top"
    by (rule sssp_log_one_third_param_component_bound)
  show "eventually
      (\<lambda>n. real (sssp_log_one_third_param n) \<le>
        2 * sssp_log_factor_one_third n) at_top"
    by (rule sssp_log_one_third_param_component_bound)
  show "eventually
      (\<lambda>n. real (sssp_log_two_thirds_param n) \<le>
        2 * sssp_log_factor n) at_top"
    by (rule sssp_log_two_thirds_param_component_bound)
  show "eventually
      (\<lambda>n. real (sssp_log_two_thirds_param n) \<le>
        2 * sssp_log_factor n) at_top"
    by (rule sssp_log_two_thirds_param_component_bound)
  show "eventually
      (\<lambda>n. real (sssp_log_one_third_param n) \<le>
        2 * sssp_log_factor_one_third n) at_top"
    by (rule sssp_log_one_third_param_component_bound)
  show "eventually
      (\<lambda>n. T n \<le>
        bmssp_refined_graph_time_bound sssp_log_one_third_param
          sssp_log_two_thirds_param sssp_log_one_third_param
          sssp_log_one_third_param sssp_log_two_thirds_param m n) at_top"
    using cost_bound .
qed

theorem bmssp_refined_cost_bound_bigo_sssp_time_target_log_params_bounded_degree:
  fixes D :: nat
  assumes Cn_pos: "0 < Cn"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real n \<le> Cn * real (m n)) at_top"
    and cost_bound:
      "eventually
        (\<lambda>n. T n \<le>
          bmssp_refined_graph_time_bound
            (\<lambda>n. Suc D * sssp_log_one_third_param n)
            sssp_log_two_thirds_param sssp_log_one_third_param
            sssp_log_one_third_param sssp_log_two_thirds_param m n) at_top"
  shows "(\<lambda>n. real (T n)) \<in> O(\<lambda>n. sssp_time_target m n)"
proof (rule bmssp_refined_cost_bound_bigo_sssp_time_target_from_component_bounds
    [where Cn = Cn and Ca = "2 * real (Suc D)"
      and Cl = 2 and Cr = 2 and Ct = 2 and Ch = 2])
  show "0 < Cn"
    using Cn_pos .
  show "0 < 2 * real (Suc D)"
    by simp
  show "0 \<le> (2::real)"
    by simp
  show "0 < (2::real)"
    by simp
  show "0 < (2::real)"
    by simp
  show "0 < (2::real)"
    by simp
  show "eventually (\<lambda>n. real n \<le> Cn * real (m n)) at_top"
    using vertex_count_dominated .
  show "eventually
      (\<lambda>n. real (Suc D * sssp_log_one_third_param n) \<le>
        2 * real (Suc D) * sssp_log_factor_one_third n) at_top"
    using sssp_log_one_third_param_component_bound
  proof eventually_elim
    case (elim n)
    have "real (Suc D * sssp_log_one_third_param n) =
        real (Suc D) * real (sssp_log_one_third_param n)"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> real (Suc D) *
        (2 * sssp_log_factor_one_third n)"
      using elim by simp
    also have "\<dots> = 2 * real (Suc D) * sssp_log_factor_one_third n"
      by (simp add: algebra_simps)
    finally show ?case .
  qed
  show "eventually
      (\<lambda>n. real (sssp_log_one_third_param n) \<le>
        2 * sssp_log_factor_one_third n) at_top"
    by (rule sssp_log_one_third_param_component_bound)
  show "eventually
      (\<lambda>n. real (sssp_log_two_thirds_param n) \<le>
        2 * sssp_log_factor n) at_top"
    by (rule sssp_log_two_thirds_param_component_bound)
  show "eventually
      (\<lambda>n. real (sssp_log_two_thirds_param n) \<le>
        2 * sssp_log_factor n) at_top"
    by (rule sssp_log_two_thirds_param_component_bound)
  show "eventually
      (\<lambda>n. real (sssp_log_one_third_param n) \<le>
        2 * sssp_log_factor_one_third n) at_top"
    by (rule sssp_log_one_third_param_component_bound)
  show "eventually
      (\<lambda>n. T n \<le>
        bmssp_refined_graph_time_bound
          (\<lambda>n. Suc D * sssp_log_one_third_param n)
          sssp_log_two_thirds_param sssp_log_one_third_param
          sssp_log_one_third_param sssp_log_two_thirds_param m n) at_top"
    using cost_bound .
qed

theorem bmssp_refined_cost_bound_bigo_sssp_time_target_log_params_bounded_degree_slack:
  fixes D :: nat
  assumes Cn_pos: "0 < Cn"
    and Cm_pos: "0 < Cm"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real (v n) \<le> Cn * real (m n)) at_top"
    and edge_count_dominated:
      "eventually (\<lambda>n. real (m' n) \<le> Cm * real (m n)) at_top"
    and cost_bound:
      "eventually
        (\<lambda>n. T n \<le>
          bmssp_refined_graph_time_bound
            (\<lambda>_. Suc D * sssp_log_one_third_param n)
            (\<lambda>_. sssp_log_two_thirds_param n)
            (\<lambda>_. sssp_log_one_third_param n)
            (\<lambda>_. sssp_log_one_third_param n)
            (\<lambda>_. sssp_log_two_thirds_param n)
            (\<lambda>_. m' n) (v n)) at_top"
  shows "(\<lambda>n. real (T n)) \<in> O(\<lambda>n. sssp_time_target m n)"
proof (rule bmssp_refined_cost_bound_bigo_sssp_time_target_from_component_bounds_slack
    [where Cn = Cn and Cm = Cm and Ca = "2 * real (Suc D)"
      and Cl = 2 and Cr = 2 and Ct = 2 and Ch = 2])
  show "0 < Cn"
    using Cn_pos .
  show "0 < Cm"
    using Cm_pos .
  show "0 < 2 * real (Suc D)"
    by simp
  show "0 \<le> (2::real)"
    by simp
  show "0 < (2::real)"
    by simp
  show "0 < (2::real)"
    by simp
  show "0 < (2::real)"
    by simp
  show "eventually (\<lambda>n. real (v n) \<le> Cn * real (m n)) at_top"
    using vertex_count_dominated .
  show "eventually (\<lambda>n. real (m' n) \<le> Cm * real (m n)) at_top"
    using edge_count_dominated .
  show "eventually
      (\<lambda>n. real (Suc D * sssp_log_one_third_param n) \<le>
        2 * real (Suc D) * sssp_log_factor_one_third n) at_top"
    using sssp_log_one_third_param_component_bound
  proof eventually_elim
    case (elim n)
    have "real (Suc D * sssp_log_one_third_param n) =
        real (Suc D) * real (sssp_log_one_third_param n)"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> real (Suc D) *
        (2 * sssp_log_factor_one_third n)"
      using elim by simp
    also have "\<dots> = 2 * real (Suc D) * sssp_log_factor_one_third n"
      by (simp add: algebra_simps)
    finally show ?case .
  qed
  show "eventually
      (\<lambda>n. real (sssp_log_one_third_param n) \<le>
        2 * sssp_log_factor_one_third n) at_top"
    by (rule sssp_log_one_third_param_component_bound)
  show "eventually
      (\<lambda>n. real (sssp_log_two_thirds_param n) \<le>
        2 * sssp_log_factor n) at_top"
    by (rule sssp_log_two_thirds_param_component_bound)
  show "eventually
      (\<lambda>n. real (sssp_log_two_thirds_param n) \<le>
        2 * sssp_log_factor n) at_top"
    by (rule sssp_log_two_thirds_param_component_bound)
  show "eventually
      (\<lambda>n. real (sssp_log_one_third_param n) \<le>
        2 * sssp_log_factor_one_third n) at_top"
    by (rule sssp_log_one_third_param_component_bound)
  show "eventually
      (\<lambda>n. T n \<le>
        bmssp_refined_graph_time_bound
          (\<lambda>_. Suc D * sssp_log_one_third_param n)
          (\<lambda>_. sssp_log_two_thirds_param n)
          (\<lambda>_. sssp_log_one_third_param n)
          (\<lambda>_. sssp_log_one_third_param n)
          (\<lambda>_. sssp_log_two_thirds_param n)
          (\<lambda>_. m' n) (v n)) at_top"
    using cost_bound .
qed

theorem bmssp_refined_cost_bound_bigo_sssp_time_target_log_params_bounded_degree_square_arg:
  fixes D :: nat
  assumes Cn_pos: "0 < Cn"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real n \<le> Cn * real (m n)) at_top"
    and cost_bound:
      "eventually
        (\<lambda>n. T n \<le>
          bmssp_refined_graph_time_bound
            (\<lambda>n. Suc D * sssp_log_one_third_param (n * n))
            (\<lambda>n. sssp_log_two_thirds_param (n * n))
            (\<lambda>n. sssp_log_one_third_param (n * n))
            (\<lambda>n. sssp_log_one_third_param (n * n))
            (\<lambda>n. sssp_log_two_thirds_param (n * n)) m n) at_top"
  shows "(\<lambda>n. real (T n)) \<in> O(\<lambda>n. sssp_time_target m n)"
proof (rule bmssp_refined_cost_bound_bigo_sssp_time_target_from_component_bounds
    [where Cn = Cn and Ca = "4 * real (Suc D)"
      and Cl = 4 and Cr = 4 and Ct = 4 and Ch = 4])
  show "0 < Cn"
    using Cn_pos .
  show "0 < 4 * real (Suc D)"
    by simp
  show "0 \<le> (4::real)"
    by simp
  show "0 < (4::real)"
    by simp
  show "0 < (4::real)"
    by simp
  show "0 < (4::real)"
    by simp
  show "eventually (\<lambda>n. real n \<le> Cn * real (m n)) at_top"
    using vertex_count_dominated .
  show "eventually
      (\<lambda>n. real (Suc D * sssp_log_one_third_param (n * n)) \<le>
        4 * real (Suc D) * sssp_log_factor_one_third n) at_top"
    using sssp_log_one_third_param_square_arg_component_bound
  proof eventually_elim
    case (elim n)
    have "real (Suc D * sssp_log_one_third_param (n * n)) =
        real (Suc D) * real (sssp_log_one_third_param (n * n))"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> real (Suc D) *
        (4 * sssp_log_factor_one_third n)"
      using elim by simp
    also have "\<dots> = 4 * real (Suc D) * sssp_log_factor_one_third n"
      by (simp add: algebra_simps)
    finally show ?case .
  qed
  show "eventually
      (\<lambda>n. real (sssp_log_one_third_param (n * n)) \<le>
        4 * sssp_log_factor_one_third n) at_top"
    by (rule sssp_log_one_third_param_square_arg_component_bound)
  show "eventually
      (\<lambda>n. real (sssp_log_two_thirds_param (n * n)) \<le>
        4 * sssp_log_factor n) at_top"
    by (rule sssp_log_two_thirds_param_square_arg_component_bound)
  show "eventually
      (\<lambda>n. real (sssp_log_two_thirds_param (n * n)) \<le>
        4 * sssp_log_factor n) at_top"
    by (rule sssp_log_two_thirds_param_square_arg_component_bound)
  show "eventually
      (\<lambda>n. real (sssp_log_one_third_param (n * n)) \<le>
        4 * sssp_log_factor_one_third n) at_top"
    by (rule sssp_log_one_third_param_square_arg_component_bound)
  show "eventually
      (\<lambda>n. T n \<le>
        bmssp_refined_graph_time_bound
          (\<lambda>n. Suc D * sssp_log_one_third_param (n * n))
          (\<lambda>n. sssp_log_two_thirds_param (n * n))
          (\<lambda>n. sssp_log_one_third_param (n * n))
          (\<lambda>n. sssp_log_one_third_param (n * n))
          (\<lambda>n. sssp_log_two_thirds_param (n * n)) m n) at_top"
    using cost_bound .
qed

theorem bmssp_refined_cost_bound_bigo_sssp_time_target_log_params_bounded_degree_square_arg_slack:
  fixes D :: nat
  assumes Cn_pos: "0 < Cn"
    and Cm_pos: "0 < Cm"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real (v n) \<le> Cn * real (m n)) at_top"
    and edge_count_dominated:
      "eventually (\<lambda>n. real (m' n) \<le> Cm * real (m n)) at_top"
    and cost_bound:
      "eventually
        (\<lambda>n. T n \<le>
          bmssp_refined_graph_time_bound
            (\<lambda>_. Suc D * sssp_log_one_third_param (n * n))
            (\<lambda>_. sssp_log_two_thirds_param (n * n))
            (\<lambda>_. sssp_log_one_third_param (n * n))
            (\<lambda>_. sssp_log_one_third_param (n * n))
            (\<lambda>_. sssp_log_two_thirds_param (n * n))
            (\<lambda>_. m' n) (v n)) at_top"
  shows "(\<lambda>n. real (T n)) \<in> O(\<lambda>n. sssp_time_target m n)"
proof (rule bmssp_refined_cost_bound_bigo_sssp_time_target_from_component_bounds_slack
    [where Cn = Cn and Cm = Cm and Ca = "4 * real (Suc D)"
      and Cl = 4 and Cr = 4 and Ct = 4 and Ch = 4])
  show "0 < Cn"
    using Cn_pos .
  show "0 < Cm"
    using Cm_pos .
  show "0 < 4 * real (Suc D)"
    by simp
  show "0 \<le> (4::real)"
    by simp
  show "0 < (4::real)"
    by simp
  show "0 < (4::real)"
    by simp
  show "0 < (4::real)"
    by simp
  show "eventually (\<lambda>n. real (v n) \<le> Cn * real (m n)) at_top"
    using vertex_count_dominated .
  show "eventually (\<lambda>n. real (m' n) \<le> Cm * real (m n)) at_top"
    using edge_count_dominated .
  show "eventually
      (\<lambda>n. real (Suc D * sssp_log_one_third_param (n * n)) \<le>
        4 * real (Suc D) * sssp_log_factor_one_third n) at_top"
    using sssp_log_one_third_param_square_arg_component_bound
  proof eventually_elim
    case (elim n)
    have "real (Suc D * sssp_log_one_third_param (n * n)) =
        real (Suc D) * real (sssp_log_one_third_param (n * n))"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> real (Suc D) *
        (4 * sssp_log_factor_one_third n)"
      using elim by simp
    also have "\<dots> = 4 * real (Suc D) * sssp_log_factor_one_third n"
      by (simp add: algebra_simps)
    finally show ?case .
  qed
  show "eventually
      (\<lambda>n. real (sssp_log_one_third_param (n * n)) \<le>
        4 * sssp_log_factor_one_third n) at_top"
    by (rule sssp_log_one_third_param_square_arg_component_bound)
  show "eventually
      (\<lambda>n. real (sssp_log_two_thirds_param (n * n)) \<le>
        4 * sssp_log_factor n) at_top"
    by (rule sssp_log_two_thirds_param_square_arg_component_bound)
  show "eventually
      (\<lambda>n. real (sssp_log_two_thirds_param (n * n)) \<le>
        4 * sssp_log_factor n) at_top"
    by (rule sssp_log_two_thirds_param_square_arg_component_bound)
  show "eventually
      (\<lambda>n. real (sssp_log_one_third_param (n * n)) \<le>
        4 * sssp_log_factor_one_third n) at_top"
    by (rule sssp_log_one_third_param_square_arg_component_bound)
  show "eventually
      (\<lambda>n. T n \<le>
        bmssp_refined_graph_time_bound
          (\<lambda>_. Suc D * sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_two_thirds_param (n * n))
          (\<lambda>_. sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_two_thirds_param (n * n))
          (\<lambda>_. m' n) (v n)) at_top"
    using cost_bound .
qed

theorem bmssp_refined_cost_bound_bigo_sssp_time_target_log_params_bounded_degree_square_arg_real_slack:
  fixes D :: nat
  assumes Cn_pos: "0 < Cn"
    and Ccost_pos: "0 < Ccost"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real n \<le> Cn * real (m n)) at_top"
    and cost_bound:
      "eventually
        (\<lambda>n. real (T n) \<le> Ccost *
          real (bmssp_refined_graph_time_bound
            (\<lambda>n. Suc D * sssp_log_one_third_param (n * n))
            (\<lambda>n. sssp_log_two_thirds_param (n * n))
            (\<lambda>n. sssp_log_one_third_param (n * n))
            (\<lambda>n. sssp_log_one_third_param (n * n))
            (\<lambda>n. sssp_log_two_thirds_param (n * n)) m n)) at_top"
  shows "(\<lambda>n. real (T n)) \<in> O(\<lambda>n. sssp_time_target m n)"
proof -
  let ?G = "\<lambda>n. bmssp_refined_graph_time_bound
    (\<lambda>n. Suc D * sssp_log_one_third_param (n * n))
    (\<lambda>n. sssp_log_two_thirds_param (n * n))
    (\<lambda>n. sssp_log_one_third_param (n * n))
    (\<lambda>n. sssp_log_one_third_param (n * n))
    (\<lambda>n. sssp_log_two_thirds_param (n * n)) m n"
  have G_bigo: "(\<lambda>n. real (?G n)) \<in> O(\<lambda>n. sssp_time_target m n)"
    by (rule bmssp_refined_cost_bound_bigo_sssp_time_target_log_params_bounded_degree_square_arg
      [where D = D and T = ?G, OF Cn_pos vertex_count_dominated]) simp
  then obtain C where C_pos: "0 < C"
    and G_bound:
      "eventually
        (\<lambda>n. norm (real (?G n)) \<le>
          C * norm (sssp_time_target m n)) at_top"
    unfolding bigo_def by blast
  have Cprod_pos: "0 < Ccost * C"
    using Ccost_pos C_pos by simp
  show ?thesis
  proof (rule sssp_time_target_bigoI_norm[OF Cprod_pos])
    show "eventually
      (\<lambda>n. norm (real (T n)) \<le>
        Ccost * C * norm (sssp_time_target m n)) at_top"
      using cost_bound G_bound
    proof eventually_elim
      case (elim n)
      have "norm (real (T n)) = real (T n)"
        by simp
      also have "\<dots> \<le> Ccost * real (?G n)"
        using elim(1) .
      also have "\<dots> = Ccost * norm (real (?G n))"
        by simp
      also have "\<dots> \<le> Ccost * (C * norm (sssp_time_target m n))"
        using elim(2) Ccost_pos by simp
      also have "\<dots> = Ccost * C * norm (sssp_time_target m n)"
        by (simp add: algebra_simps)
      finally show ?case .
    qed
  qed
qed

theorem bmssp_refined_cost_bound_bigo_sssp_time_target_log_params_bounded_degree_real_slack:
  fixes D :: nat
  assumes Cn_pos: "0 < Cn"
    and Ccost_pos: "0 < Ccost"
    and vertex_count_dominated:
      "eventually (\<lambda>n. real n \<le> Cn * real (m n)) at_top"
    and cost_bound:
      "eventually
        (\<lambda>n. real (T n) \<le> Ccost *
          real (bmssp_refined_graph_time_bound
            (\<lambda>n. Suc D * sssp_log_one_third_param n)
            sssp_log_two_thirds_param sssp_log_one_third_param
            sssp_log_one_third_param sssp_log_two_thirds_param m n)) at_top"
  shows "(\<lambda>n. real (T n)) \<in> O(\<lambda>n. sssp_time_target m n)"
proof -
  let ?G = "\<lambda>n. bmssp_refined_graph_time_bound
    (\<lambda>n. Suc D * sssp_log_one_third_param n)
    sssp_log_two_thirds_param sssp_log_one_third_param
    sssp_log_one_third_param sssp_log_two_thirds_param m n"
  have G_bigo: "(\<lambda>n. real (?G n)) \<in> O(\<lambda>n. sssp_time_target m n)"
    by (rule bmssp_refined_cost_bound_bigo_sssp_time_target_log_params_bounded_degree
      [where D = D and T = ?G, OF Cn_pos vertex_count_dominated]) simp
  then obtain C where C_pos: "0 < C"
    and G_bound:
      "eventually
        (\<lambda>n. norm (real (?G n)) \<le>
          C * norm (sssp_time_target m n)) at_top"
    unfolding bigo_def by blast
  have Cprod_pos: "0 < Ccost * C"
    using Ccost_pos C_pos by simp
  show ?thesis
  proof (rule sssp_time_target_bigoI_norm[OF Cprod_pos])
    show "eventually
      (\<lambda>n. norm (real (T n)) \<le>
        Ccost * C * norm (sssp_time_target m n)) at_top"
      using cost_bound G_bound
    proof eventually_elim
      case (elim n)
      have "norm (real (T n)) = real (T n)"
        by simp
      also have "\<dots> \<le> Ccost * real (?G n)"
        using elim(1) .
      also have "\<dots> = Ccost * norm (real (?G n))"
        by simp
      also have "\<dots> \<le> Ccost * (C * norm (sssp_time_target m n))"
        using elim(2) Ccost_pos by simp
      also have "\<dots> = Ccost * C * norm (sssp_time_target m n)"
        by (simp add: algebra_simps)
      finally show ?case .
    qed
  qed
qed

context unique_shortest_digraph
begin

text \<open>
  From this point on the arithmetic bounds are tied to a concrete finite graph.
  The definitions \<open>vertex_count\<close> and \<open>edge_count\<close> are simple wrappers around
  the locale's finite vertex and edge sets, but naming them keeps the final
  theorems independent of internal set notation.  The parent-edge construction
  is used to relate reachable vertices to edges, which is the standard sparse
  graph move behind replacing a vertex term by an edge term when all vertices
  are reachable.
\<close>

definition vertex_count where
  "vertex_count = card V"

definition edge_count where
  "edge_count = card E"

definition parent_edge_to where
  "parent_edge_to v = (last (butlast (shortest_path_to v)), v)"

lemma vertex_count_pos [simp]:
  "0 < vertex_count"
proof -
  have "V \<noteq> {}"
    using source_in_V by blast
  then show ?thesis
    unfolding vertex_count_def using finite_V by (simp add: card_gt_0_iff)
qed

lemma edge_count_le_vertex_count_square:
  "edge_count \<le> vertex_count * vertex_count"
proof -
  have E_subset: "E \<subseteq> V \<times> V"
    using edge_in_V by auto
  have "edge_count = card E"
    unfolding edge_count_def by simp
  also have "\<dots> \<le> card (V \<times> V)"
    by (rule card_mono[OF _ E_subset]) (use finite_V in simp)
  also have "\<dots> = vertex_count * vertex_count"
    unfolding vertex_count_def by (simp add: card_cartesian_product)
  finally show ?thesis .
qed

lemma parent_edge_to_in_E:
  assumes reach_v: "reachable s v"
    and v_ne: "v \<noteq> s"
  shows "parent_edge_to v \<in> E"
proof -
  let ?p = "shortest_path_to v"
  have sp: "shortest_walk s ?p v"
    by (rule shortest_path_to_shortest[OF reach_v])
  have walk_p: "walk ?p"
    using sp unfolding shortest_walk_def simple_walk_betw_def walk_betw_def by blast
  have p_ne: "?p \<noteq> []"
    using sp unfolding shortest_walk_def simple_walk_betw_def walk_betw_def by blast
  have hd_p: "hd ?p = s"
    using sp unfolding shortest_walk_def simple_walk_betw_def walk_betw_def by blast
  have last_p: "last ?p = v"
    using sp unfolding shortest_walk_def simple_walk_betw_def walk_betw_def by blast
  have len_ge2: "1 < length ?p"
  proof (rule ccontr)
    assume "\<not> 1 < length ?p"
    then have "length ?p = 1"
      using p_ne by (cases ?p) auto
    then have "hd ?p = last ?p"
      by (cases ?p) auto
    then show False
      using hd_p last_p v_ne by simp
  qed
  have but_ne: "butlast ?p \<noteq> []"
    using len_ge2 by (cases ?p) auto
  obtain q u where but: "butlast ?p = q @ [u]"
    using but_ne by (cases "butlast ?p" rule: rev_cases) auto
  have p_decomp: "?p = q @ [u, v]"
  proof -
    have "?p = butlast ?p @ [last ?p]"
      using p_ne by simp
    then show ?thesis
      using but last_p by simp
  qed
  have i_lt: "Suc (length q) < length ?p"
    using p_decomp by simp
  have edge: "(?p ! length q, ?p ! Suc (length q)) \<in> E"
    by (rule walk_nth_edge[OF walk_p i_lt])
  have "?p ! length q = u"
    using p_decomp by (simp add: nth_append)
  moreover have "?p ! Suc (length q) = v"
    using p_decomp by (simp add: nth_append)
  ultimately have "(u, v) \<in> E"
    using edge by simp
  moreover have "last (butlast ?p) = u"
    using but by simp
  ultimately show ?thesis
    unfolding parent_edge_to_def by simp
qed

theorem vertex_count_le_Suc_edge_count_if_all_reachable:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
  shows "vertex_count \<le> Suc edge_count"
proof -
  have image_subset: "parent_edge_to ` (V - {s}) \<subseteq> E"
  proof
    fix e
    assume "e \<in> parent_edge_to ` (V - {s})"
    then obtain v where v: "v \<in> V" "v \<noteq> s" "e = parent_edge_to v"
      by blast
    have "reachable s v"
      by (rule all_reachable[OF v(1)])
    then show "e \<in> E"
      using parent_edge_to_in_E[OF _ v(2)] v(3) by simp
  qed
  have inj: "inj_on parent_edge_to (V - {s})"
    unfolding parent_edge_to_def inj_on_def by auto
  have card_image:
    "card (V - {s}) = card (parent_edge_to ` (V - {s}))"
    using inj finite_V by (simp add: card_image)
  also have "\<dots> \<le> edge_count"
    unfolding edge_count_def
    by (rule card_mono[OF finite_E image_subset])
  finally have without_s: "card (V - {s}) \<le> edge_count" .
  have V_decomp: "V = insert s (V - {s})"
    using source_in_V by blast
  have "card V = card (insert s (V - {s}))"
    using V_decomp by simp
  also have "\<dots> = Suc (card (V - {s}))"
    by (rule card_insert_disjoint) (use finite_V in auto)
  finally have "card V = Suc (card (V - {s}))" .
  then show ?thesis
    using without_s unfolding vertex_count_def by simp
qed

corollary vertex_count_le_twice_edge_count_if_all_reachable:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and nontrivial: "0 < edge_count"
  shows "vertex_count \<le> 2 * edge_count"
proof -
  have "vertex_count \<le> Suc edge_count"
    by (rule vertex_count_le_Suc_edge_count_if_all_reachable[OF all_reachable])
  also have "\<dots> \<le> 2 * edge_count"
    using nontrivial by simp
  finally show ?thesis .
qed

lemma card_subset_vertex_count:
  assumes "S \<subseteq> V"
  shows "card S \<le> vertex_count"
  unfolding vertex_count_def
  by (rule card_mono[OF finite_V assms])

lemma eventually_top_level_threshold_exceeds_vertex_count:
  "eventually
    (\<lambda>N. vertex_count <
      sssp_log_one_third_param N *
      bmssp_level_cap (sssp_log_one_third_param N)
        (sssp_log_two_thirds_param N) (sssp_log_one_third_param N))
    at_top"
  using eventually_less_sssp_log_one_third_param[of vertex_count]
proof eventually_elim
  case (elim N)
  let ?p = "sssp_log_one_third_param N"
  let ?q = "sssp_log_two_thirds_param N"
  let ?cap = "bmssp_level_cap ?p ?q ?p"
  have cap_pos: "0 < ?cap"
    unfolding bmssp_level_cap_def by simp
  have "?p \<le> ?p * ?cap"
    using cap_pos by (cases ?cap) simp_all
  then show ?case
    using elim by linarith
qed

lemma find_pivots_pivots_capped_singleton_empty_if_params_exceed_vertex_count:
  assumes k_gt: "vertex_count < k"
    and cap_ge: "vertex_count \<le> cap"
  shows "find_pivots_pivots_capped k cap d {s} B = {}"
proof -
  let ?seen = "find_pivots_seen_capped k cap d {s} B"
  have source_subset: "{s} \<subseteq> V"
    using source_in_V by simp
  have seen_subset: "?seen \<subseteq> V"
    unfolding find_pivots_seen_capped_def
    by (rule fp_iter_capped_seen_subset_V[OF source_subset source_subset])
  have card_seen_le: "card ?seen \<le> vertex_count"
    by (rule card_subset_vertex_count[OF seen_subset])
  have no_overflow: "\<not> card ?seen > cap"
    using card_seen_le cap_ge by linarith
  have no_large_tree:
    "{u \<in> {s}. k \<le> card (tree_of u \<inter> ?seen)} = {}"
  proof
    show "{u \<in> {s}. k \<le> card (tree_of u \<inter> ?seen)} \<subseteq> {}"
    proof
      fix u
      assume u_mem: "u \<in> {u \<in> {s}. k \<le> card (tree_of u \<inter> ?seen)}"
      have tree_seen_subset: "tree_of u \<inter> ?seen \<subseteq> V"
        unfolding tree_of_def by blast
      have "card (tree_of u \<inter> ?seen) \<le> vertex_count"
        by (rule card_subset_vertex_count[OF tree_seen_subset])
      moreover have "k \<le> card (tree_of u \<inter> ?seen)"
        using u_mem by blast
      ultimately show "u \<in> {}"
        using k_gt by linarith
    qed
  qed simp
  show ?thesis
    unfolding find_pivots_pivots_capped_def
    using no_overflow no_large_tree by simp
qed

lemma eventually_top_level_pivots_empty:
  "eventually
    (\<lambda>N. find_pivots_pivots_capped (sssp_log_one_third_param N)
      (bmssp_level_cap (sssp_log_one_third_param N)
        (sssp_log_two_thirds_param N) (sssp_log_one_third_param N))
      d {s} B = {})
    at_top"
  using eventually_less_sssp_log_one_third_param[of vertex_count]
proof eventually_elim
  case (elim N)
  let ?p = "sssp_log_one_third_param N"
  let ?q = "sssp_log_two_thirds_param N"
  let ?cap = "bmssp_level_cap ?p ?q ?p"
  have cap_ge_p: "?p \<le> ?cap"
    by (rule bmssp_level_cap_ge_level)
  have cap_ge_vertex: "vertex_count \<le> ?cap"
    using elim cap_ge_p by linarith
  show ?case
    by (rule find_pivots_pivots_capped_singleton_empty_if_params_exceed_vertex_count
      [OF elim cap_ge_vertex])
qed

lemma edge_count_outgoing_bound:
  "card (outgoing_edges X) \<le> edge_count"
proof -
  have "outgoing_edges X \<subseteq> E"
    unfolding outgoing_edges_def by blast
  then show ?thesis
    unfolding edge_count_def by (rule card_mono[OF finite_E])
qed

lemma edge_count_outgoing_bound_tree:
  "card (outgoing_edges (bound_tree S B)) \<le> edge_count"
  by (rule edge_count_outgoing_bound)

text \<open>
  The range-based edge definitions are the combinatorial support for the
  direct-insert and lower-batch split.  An edge is charged to a range according
  to the relaxed value at its source, not merely according to the source
  vertex.  This matches the algorithm: a completed child range may generate
  relaxations that fall below the pull bound, inside the parent output bound, or
  outside the current problem.

  The length lemmas connect executable lists of relaxation pairs to the
  mathematical edge ranges.  The disjointness and split lemmas that follow make
  it possible to sum per-child edge charges and bound them by the outgoing edges
  of the assembled parent range.
\<close>

definition outgoing_edges_range where
  "outgoing_edges_range U a B =
    {(u, v) \<in> E. u \<in> U \<and> a \<le> dist s u + w u v \<and>
      below_bound (dist s u + w u v) B}"

lemma outgoing_edges_range_subset_E:
  "outgoing_edges_range U a B \<subseteq> E"
  unfolding outgoing_edges_range_def by blast

lemma outgoing_edges_range_subset_outgoing_edges:
  "outgoing_edges_range U a B \<subseteq> outgoing_edges U"
  unfolding outgoing_edges_range_def outgoing_edges_def by blast

lemma finite_outgoing_edges_range [simp]:
  "finite (outgoing_edges_range U a B)"
  by (rule finite_subset[OF outgoing_edges_range_subset_E finite_E])

lemma card_outgoing_edges_range_le_edge_count:
  "card (outgoing_edges_range U a B) \<le> edge_count"
  unfolding edge_count_def
  by (rule card_mono[OF finite_E outgoing_edges_range_subset_E])

definition edge_relaxation_pairs_in_bound where
  "edge_relaxation_pairs_in_bound d U L B =
     map (\<lambda>(u, v). (v, d u + w u v))
       (filter (\<lambda>(u, v). L \<le> d u + w u v \<and>
          below_bound (d u + w u v) B)
        (edge_list_of (outgoing_edges U)))"

lemma edge_relaxation_pairs_in_bound_value_ge_low:
  assumes "(x, b) \<in> set (edge_relaxation_pairs_in_bound d U L B)"
  shows "L \<le> b"
  using assms unfolding edge_relaxation_pairs_in_bound_def by auto

lemma edge_relaxation_pairs_in_bound_value_below_bound:
  assumes "(x, b) \<in> set (edge_relaxation_pairs_in_bound d U L B)"
  shows "below_bound b B"
  using assms unfolding edge_relaxation_pairs_in_bound_def by auto

lemma edge_relaxation_pairs_in_bound_length_le_outgoing_edges_range:
  assumes complete: "complete_on d U"
    and reaches: "\<And>u. u \<in> U \<Longrightarrow> reachable s u"
  shows "length (edge_relaxation_pairs_in_bound d U L B) \<le>
    card (outgoing_edges_range U L B)"
proof -
  let ?es = "edge_list_of (outgoing_edges U)"
  let ?fs =
    "filter (\<lambda>(u, v). L \<le> d u + w u v \<and>
      below_bound (d u + w u v) B) ?es"
  have set_es: "set ?es = outgoing_edges U"
    using edge_list_of_properties(1)[OF finite_outgoing_edges] .
  have distinct_fs: "distinct ?fs"
    using edge_list_of_properties(2)[OF finite_outgoing_edges] by simp
  have subset:
    "set ?fs \<subseteq> outgoing_edges_range U L B"
  proof
    fix e
    assume e: "e \<in> set ?fs"
    then obtain u v where ev: "e = (u, v)"
      by (metis surj_pair)
    have edge: "(u, v) \<in> E"
      and uU: "u \<in> U"
      and low: "L \<le> d u + w u v"
      and high: "below_bound (d u + w u v) B"
      using e set_es unfolding ev outgoing_edges_def by auto
    have du: "d u = dist s u"
      using complete reaches[OF uU] uU unfolding complete_on_def by blast
    show "e \<in> outgoing_edges_range U L B"
      using edge uU low high unfolding ev du outgoing_edges_range_def by simp
  qed
  have "length (edge_relaxation_pairs_in_bound d U L B) = length ?fs"
    unfolding edge_relaxation_pairs_in_bound_def by simp
  also have "\<dots> = card (set ?fs)"
    using distinct_card[OF distinct_fs] by simp
  also have "\<dots> \<le> card (outgoing_edges_range U L B)"
    by (rule card_mono[OF finite_outgoing_edges_range subset])
  finally show ?thesis .
qed

lemma partition_batch_cost_bound_edge_relaxation_pairs_in_bound:
  assumes cost:
      "partition_batch_cost_bound c t
        (edge_relaxation_pairs_in_bound d U L B)"
    and complete: "complete_on d U"
    and reaches: "\<And>u. u \<in> U \<Longrightarrow> reachable s u"
  shows "c \<le> t * card (outgoing_edges_range U L B)"
proof -
  have len_le: "length (edge_relaxation_pairs_in_bound d U L B) \<le>
      card (outgoing_edges_range U L B)"
    by (rule edge_relaxation_pairs_in_bound_length_le_outgoing_edges_range
      [OF complete reaches])
  have "c \<le> t * length (edge_relaxation_pairs_in_bound d U L B)"
    using cost unfolding partition_batch_cost_bound_def by simp
  also have "\<dots> \<le> t * card (outgoing_edges_range U L B)"
    using len_le by simp
  finally show ?thesis .
qed

lemma edge_relaxation_pairs_between_length_le_outgoing_edges_range:
  assumes complete: "complete_on d U"
    and reaches: "\<And>u. u \<in> U \<Longrightarrow> reachable s u"
  shows "length (edge_relaxation_pairs_between d U L H) \<le>
    card (outgoing_edges_range U L (Fin H))"
proof -
  let ?es = "edge_list_of (outgoing_edges U)"
  let ?fs =
    "filter (\<lambda>(u, v). L \<le> d u + w u v \<and> d u + w u v < H) ?es"
  have set_es: "set ?es = outgoing_edges U"
    using edge_list_of_properties(1)[OF finite_outgoing_edges] .
  have distinct_fs: "distinct ?fs"
    using edge_list_of_properties(2)[OF finite_outgoing_edges] by simp
  have subset:
    "set ?fs \<subseteq> outgoing_edges_range U L (Fin H)"
  proof
    fix e
    assume e: "e \<in> set ?fs"
    then obtain u v where ev: "e = (u, v)"
      by (metis surj_pair)
    have edge: "(u, v) \<in> E"
      and uU: "u \<in> U"
      and low: "L \<le> d u + w u v"
      and high: "d u + w u v < H"
      using e set_es unfolding ev outgoing_edges_def by auto
    have du: "d u = dist s u"
      using complete reaches[OF uU] uU unfolding complete_on_def by blast
    show "e \<in> outgoing_edges_range U L (Fin H)"
      using edge uU low high unfolding ev du outgoing_edges_range_def by simp
  qed
  have "length (edge_relaxation_pairs_between d U L H) = length ?fs"
    unfolding edge_relaxation_pairs_between_def by simp
  also have "\<dots> = card (set ?fs)"
    using distinct_card[OF distinct_fs] by simp
  also have "\<dots> \<le> card (outgoing_edges_range U L (Fin H))"
    by (rule card_mono[OF finite_outgoing_edges_range subset])
  finally show ?thesis .
qed

lemma edge_relaxation_pairs_between_length_le_range_tree_outgoing_edges_range:
  assumes complete: "complete_on d (range_tree S a B)"
  shows "length (edge_relaxation_pairs_between d (range_tree S a B) L H) \<le>
    card (outgoing_edges_range (range_tree S a B) L (Fin H))"
proof (rule edge_relaxation_pairs_between_length_le_outgoing_edges_range[OF complete])
  fix u
  assume "u \<in> range_tree S a B"
  then show "reachable s u"
    unfolding range_tree_def tree_set_def tree_path_def by blast
qed

lemma outgoing_edges_range_mono_sources:
  assumes "U \<subseteq> W"
  shows "outgoing_edges_range U a B \<subseteq> outgoing_edges_range W a B"
  using assms unfolding outgoing_edges_range_def by blast

lemma outgoing_edges_range_split:
  assumes a_le_b: "a \<le> b"
    and b_le_B: "bound_le (Fin b) B"
  shows "outgoing_edges_range U a B =
    outgoing_edges_range U a (Fin b) \<union> outgoing_edges_range U b B"
  using assms unfolding outgoing_edges_range_def
  by (cases B) auto

lemma outgoing_edges_range_split_disjoint:
  "outgoing_edges_range U a (Fin b) \<inter> outgoing_edges_range U b B = {}"
  unfolding outgoing_edges_range_def by auto

lemma card_outgoing_edges_range_split:
  assumes a_le_b: "a \<le> b"
    and b_le_B: "bound_le (Fin b) B"
  shows "card (outgoing_edges_range U a B) =
    card (outgoing_edges_range U a (Fin b)) +
    card (outgoing_edges_range U b B)"
proof -
  have split:
    "outgoing_edges_range U a B =
      outgoing_edges_range U a (Fin b) \<union> outgoing_edges_range U b B"
    by (rule outgoing_edges_range_split[OF a_le_b b_le_B])
  have disj:
    "outgoing_edges_range U a (Fin b) \<inter> outgoing_edges_range U b B = {}"
    by (rule outgoing_edges_range_split_disjoint)
  show ?thesis
    unfolding split
    by (rule card_Un_disjoint) (use disj in auto)
qed

lemma card_outgoing_edges_range_lower_direct_split:
  assumes b_le_beta: "b \<le> beta"
    and beta_le_B: "bound_le (Fin beta) B"
  shows "card (outgoing_edges_range U b (Fin beta)) +
    card (outgoing_edges_range U beta B) =
    card (outgoing_edges_range U b B)"
  using card_outgoing_edges_range_split[OF b_le_beta beta_le_B, of U]
  by simp

lemma card_outgoing_edges_range_zero_lower_direct_split_le:
  assumes beta_le_B: "bound_le (Fin beta) B"
    and nonneg:
      "\<And>u v. \<lbrakk>(u, v) \<in> E; u \<in> U\<rbrakk> \<Longrightarrow> 0 \<le> dist s u + w u v"
  shows "card (outgoing_edges_range U 0 (Fin beta)) +
    card (outgoing_edges_range U beta B) \<le>
    card (outgoing_edges_range U 0 B)"
proof -
  let ?lower = "outgoing_edges_range U 0 (Fin beta)"
  let ?direct = "outgoing_edges_range U beta B"
  let ?full = "outgoing_edges_range U 0 B"
  have disj: "?lower \<inter> ?direct = {}"
    by (rule outgoing_edges_range_split_disjoint)
  have union_subset: "?lower \<union> ?direct \<subseteq> ?full"
  proof
    fix e
    assume e: "e \<in> ?lower \<union> ?direct"
    show "e \<in> ?full"
    proof (cases "e \<in> ?lower")
      case True
      then show ?thesis
        using beta_le_B unfolding outgoing_edges_range_def
        by (cases B) auto
    next
      case False
      then have direct: "e \<in> ?direct"
        using e by blast
      then obtain u v where e_uv: "e = (u, v)"
        by (metis surj_pair)
      have edge: "(u, v) \<in> E" and uU: "u \<in> U"
        using direct unfolding e_uv outgoing_edges_range_def by auto
      have "0 \<le> dist s u + w u v"
        by (rule nonneg[OF edge uU])
      then show ?thesis
        using direct unfolding e_uv outgoing_edges_range_def by auto
    qed
  qed
  have card_union:
    "card (?lower \<union> ?direct) = card ?lower + card ?direct"
    using disj by (simp add: card_Un_disjoint)
  have "card (?lower \<union> ?direct) \<le> card ?full"
    by (rule card_mono[OF finite_outgoing_edges_range union_subset])
  then show ?thesis
    using card_union by linarith
qed

lemma outgoing_edges_range_disjoint_sources:
  assumes "U \<inter> W = {}"
  shows "outgoing_edges_range U a B \<inter> outgoing_edges_range W c D = {}"
  using assms unfolding outgoing_edges_range_def by blast

fun pairwise_disjoint_list where
  "pairwise_disjoint_list [] \<longleftrightarrow> True"
| "pairwise_disjoint_list (X # Xs) \<longleftrightarrow>
    (\<forall>Y\<in>set Xs. X \<inter> Y = {}) \<and> pairwise_disjoint_list Xs"

lemma pairwise_disjoint_list_outgoing_edges_range:
  assumes "pairwise_disjoint_list Us"
  shows "pairwise_disjoint_list (map (\<lambda>U. outgoing_edges_range U a B) Us)"
  using assms
proof (induction Us)
  case Nil
  then show ?case by simp
next
  case (Cons U Us)
  have disj_head:
    "\<forall>Y\<in>set (map (\<lambda>U. outgoing_edges_range U a B) Us).
      outgoing_edges_range U a B \<inter> Y = {}"
  proof
    fix Y
    assume "Y \<in> set (map (\<lambda>U. outgoing_edges_range U a B) Us)"
    then obtain W where W: "W \<in> set Us" "Y = outgoing_edges_range W a B"
      by auto
    have "U \<inter> W = {}"
      using Cons.prems W(1) by simp
    then show "outgoing_edges_range U a B \<inter> Y = {}"
      unfolding W(2) by (rule outgoing_edges_range_disjoint_sources)
  qed
  have tail: "pairwise_disjoint_list (map (\<lambda>U. outgoing_edges_range U a B) Us)"
    using Cons.IH Cons.prems by simp
  show ?case
    using disj_head tail by simp
qed

lemma edge_outdegree_le_edge_count:
  "edge_outdegree_le edge_count"
  unfolding edge_outdegree_le_def
  using edge_count_outgoing_bound by blast

lemma card_Union_pairwise_disjoint_list:
  assumes disj: "pairwise_disjoint_list Xs"
    and finite_sets: "\<And>X. X \<in> set Xs \<Longrightarrow> finite X"
  shows "card (\<Union>(set Xs)) = sum_list (map card Xs)"
  using assms
proof (induction Xs)
  case Nil
  then show ?case by simp
next
  case (Cons X Xs)
  have finite_X: "finite X"
    using Cons.prems by simp
  have finite_tail: "finite (\<Union>(set Xs))"
    using Cons.prems by auto
  have disjoint_tail: "X \<inter> \<Union>(set Xs) = {}"
    using Cons.prems by auto
  have tail:
    "card (\<Union>(set Xs)) = sum_list (map card Xs)"
    using Cons.IH Cons.prems by auto
  have "card (\<Union>(set (X # Xs))) =
      card X + card (\<Union>(set Xs))"
    by (simp add: card_Un_disjoint finite_X finite_tail disjoint_tail)
  then show ?case
    using tail by simp
qed

lemma sum_card_outgoing_edges_range_disjoint_sources_le_edge_count:
  assumes disj: "pairwise_disjoint_list Us"
  shows "sum_list (map (\<lambda>U. card (outgoing_edges_range U a B)) Us) \<le> edge_count"
proof -
  have disj_ranges:
    "pairwise_disjoint_list (map (\<lambda>U. outgoing_edges_range U a B) Us)"
    by (rule pairwise_disjoint_list_outgoing_edges_range[OF disj])
  have finite_ranges:
    "\<And>X. X \<in> set (map (\<lambda>U. outgoing_edges_range U a B) Us) \<Longrightarrow> finite X"
    by auto
  have card_union:
    "card (\<Union>(set (map (\<lambda>U. outgoing_edges_range U a B) Us))) =
      sum_list (map card (map (\<lambda>U. outgoing_edges_range U a B) Us))"
    by (rule card_Union_pairwise_disjoint_list[OF disj_ranges finite_ranges])
  have union_subset:
    "\<Union>(set (map (\<lambda>U. outgoing_edges_range U a B) Us)) \<subseteq> E"
  proof
    fix e
    assume "e \<in> \<Union>(set (map (\<lambda>U. outgoing_edges_range U a B) Us))"
    then obtain U where "U \<in> set Us" and "e \<in> outgoing_edges_range U a B"
      by auto
    then show "e \<in> E"
      unfolding outgoing_edges_range_def by auto
  qed
  have sum_maps:
    "sum_list (map (\<lambda>U. card (outgoing_edges_range U a B)) Us) =
      sum_list (map card (map (\<lambda>U. outgoing_edges_range U a B) Us))"
    by (induction Us) simp_all
  have "sum_list (map (\<lambda>U. card (outgoing_edges_range U a B)) Us) =
      card (\<Union>(set (map (\<lambda>U. outgoing_edges_range U a B) Us)))"
    using sum_maps card_union by simp
  also have "\<dots> \<le> edge_count"
    unfolding edge_count_def by (rule card_mono[OF finite_E union_subset])
  finally show ?thesis .
qed

lemma outgoing_edges_disjoint_if_sources_disjoint:
  assumes "A \<inter> B = {}"
  shows "outgoing_edges A \<inter> outgoing_edges B = {}"
  using assms unfolding outgoing_edges_def by auto

lemma pairwise_disjoint_list_outgoing_edges:
  assumes "pairwise_disjoint_list Xs"
  shows "pairwise_disjoint_list (map outgoing_edges Xs)"
  using assms
proof (induction Xs)
  case Nil
  then show ?case by simp
next
  case (Cons X Xs)
  have "\<And>Y. Y \<in> set Xs \<Longrightarrow> outgoing_edges X \<inter> outgoing_edges Y = {}"
    using Cons.prems outgoing_edges_disjoint_if_sources_disjoint by auto
  then show ?case
    using Cons by auto
qed

lemma outgoing_edges_Union_list:
  "outgoing_edges (\<Union>(set Xs)) = \<Union>(set (map outgoing_edges Xs))"
  unfolding outgoing_edges_def by auto

lemma outgoing_edges_mono:
  assumes "A \<subseteq> B"
  shows "outgoing_edges A \<subseteq> outgoing_edges B"
  using assms unfolding outgoing_edges_def by blast

fun range_tree_child_list where
  "range_tree_child_list S a [] = []"
| "range_tree_child_list S a (b # bs) =
    range_tree S a (Fin b) # range_tree_child_list S b bs"

lemma length_range_tree_child_list [simp]:
  "length (range_tree_child_list S a bs) = length bs"
  by (induction bs arbitrary: a) simp_all

lemma range_tree_child_list_set_subset_chain_list:
  "set (range_tree_child_list S a bs) \<subseteq> set (range_tree_chain_list S a bs B)"
proof (induction bs arbitrary: a)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  have "set (range_tree_child_list S b bs) \<subseteq>
      set (range_tree_chain_list S b bs B)"
    using Cons.IH .
  then show ?case by auto
qed

lemma Union_range_tree_child_list_subset_chain:
  "\<Union>(set (range_tree_child_list S a bs)) \<subseteq> range_tree_chain S a bs B"
proof (induction bs arbitrary: a)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  have "\<Union>(set (range_tree_child_list S b bs)) \<subseteq>
      range_tree_chain S b bs B"
    using Cons.IH .
  then show ?case by auto
qed

fun range_tree_child_edge_range_list where
  "range_tree_child_edge_range_list S a [] [] = []"
| "range_tree_child_edge_range_list S a [] (b # bs) = []"
| "range_tree_child_edge_range_list S a (beta # betas) [] = []"
| "range_tree_child_edge_range_list S a (beta # betas) (b # bs) =
    outgoing_edges_range (range_tree S a (Fin b)) b (Fin beta) #
    range_tree_child_edge_range_list S b betas bs"

lemma range_tree_child_edge_range_list_subset_outgoing_sources:
  assumes "Y \<in> set (range_tree_child_edge_range_list S a betas bs)"
  shows "\<exists>X\<in>set (range_tree_child_list S a bs). Y \<subseteq> outgoing_edges X"
  using assms
proof (induction betas arbitrary: a bs)
  case Nil
  then show ?case
    by (cases bs) simp_all
next
  case (Cons beta betas)
  show ?case
  proof (cases bs)
    case Nil
    then show ?thesis
      using Cons.prems by simp
  next
    case (Cons b bs')
    let ?head = "outgoing_edges_range (range_tree S a (Fin b)) b (Fin beta)"
    let ?tail = "range_tree_child_edge_range_list S b betas bs'"
    have Y_cases: "Y = ?head \<or> Y \<in> set ?tail"
      using Cons.prems Cons by simp
    then show ?thesis
    proof
      assume Y_head: "Y = ?head"
      have "?head \<subseteq> outgoing_edges (range_tree S a (Fin b))"
        by (rule outgoing_edges_range_subset_outgoing_edges)
      then show ?thesis
        unfolding Cons Y_head by auto
    next
      assume Y_tail: "Y \<in> set ?tail"
      obtain X where X: "X \<in> set (range_tree_child_list S b bs')"
        and YX: "Y \<subseteq> outgoing_edges X"
        using Cons.IH[OF Y_tail] by blast
      show ?thesis
        using X YX unfolding Cons by auto
    qed
  qed
qed

lemma range_tree_child_edge_range_list_member_subset_E:
  assumes "Y \<in> set (range_tree_child_edge_range_list S a betas bs)"
  shows "Y \<subseteq> E"
proof
  fix e
  assume eY: "e \<in> Y"
  obtain X where "X \<in> set (range_tree_child_list S a bs)"
    and Y_subset: "Y \<subseteq> outgoing_edges X"
    using range_tree_child_edge_range_list_subset_outgoing_sources[OF assms]
    by blast
  then have "e \<in> outgoing_edges X"
    using eY by blast
  then show "e \<in> E"
    unfolding outgoing_edges_def by blast
qed

lemma pairwise_disjoint_list_range_tree_child_edge_range_list:
  assumes mono: "nondecreasing_from a bs"
  shows "pairwise_disjoint_list (range_tree_child_edge_range_list S a betas bs)"
  using mono
proof (induction betas arbitrary: a bs)
  case Nil
  then show ?case
    by (cases bs) simp_all
next
  case (Cons beta betas)
  show ?case
  proof (cases bs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons b bs')
    let ?head = "outgoing_edges_range (range_tree S a (Fin b)) b (Fin beta)"
    let ?tail = "range_tree_child_edge_range_list S b betas bs'"
    have a_le_b: "a \<le> b"
      using Cons.prems Cons by simp
    have mono_tail: "nondecreasing_from b bs'"
      using Cons.prems Cons by simp
    have head_tail_disj: "\<forall>Y\<in>set ?tail. ?head \<inter> Y = {}"
    proof
      fix Y
      assume Y: "Y \<in> set ?tail"
      obtain X where X: "X \<in> set (range_tree_child_list S b bs')"
        and YX: "Y \<subseteq> outgoing_edges X"
        using range_tree_child_edge_range_list_subset_outgoing_sources[OF Y]
        by blast
      have X_subset: "X \<subseteq> range_tree_chain S b bs' Infinity"
        using X Union_range_tree_child_list_subset_chain[of S b bs' Infinity]
        by blast
      have source_disj: "range_tree S a (Fin b) \<inter> X = {}"
        using range_tree_disjoint_range_tree_chain_tail
          [OF a_le_b mono_tail, of S Infinity] X_subset by blast
      have out_disj:
        "outgoing_edges (range_tree S a (Fin b)) \<inter> outgoing_edges X = {}"
        by (rule outgoing_edges_disjoint_if_sources_disjoint[OF source_disj])
      have head_subset: "?head \<subseteq> outgoing_edges (range_tree S a (Fin b))"
        by (rule outgoing_edges_range_subset_outgoing_edges)
      show "?head \<inter> Y = {}"
        using head_subset YX out_disj by blast
    qed
    have tail_disj: "pairwise_disjoint_list ?tail"
      by (rule Cons.IH[OF mono_tail])
    show ?thesis
      unfolding Cons by (simp add: head_tail_disj tail_disj)
  qed
qed

lemma sum_card_range_tree_child_edge_range_list_le_edge_count:
  assumes mono: "nondecreasing_from a bs"
  shows "sum_list (map card (range_tree_child_edge_range_list S a betas bs))
    \<le> edge_count"
proof -
  let ?Xs = "range_tree_child_edge_range_list S a betas bs"
  have disj: "pairwise_disjoint_list ?Xs"
    by (rule pairwise_disjoint_list_range_tree_child_edge_range_list[OF mono])
  have finite_sets: "\<And>X. X \<in> set ?Xs \<Longrightarrow> finite X"
    using range_tree_child_edge_range_list_member_subset_E
    by (meson finite_E finite_subset)
  have card_union:
    "card (\<Union>(set ?Xs)) = sum_list (map card ?Xs)"
    by (rule card_Union_pairwise_disjoint_list[OF disj finite_sets])
  have union_subset: "\<Union>(set ?Xs) \<subseteq> E"
  proof
    fix e
    assume "e \<in> \<Union>(set ?Xs)"
    then obtain X where X: "X \<in> set ?Xs" and eX: "e \<in> X"
      by blast
    show "e \<in> E"
      using range_tree_child_edge_range_list_member_subset_E[OF X] eX by blast
  qed
  have "sum_list (map card ?Xs) = card (\<Union>(set ?Xs))"
    using card_union by simp
  also have "\<dots> \<le> edge_count"
    unfolding edge_count_def by (rule card_mono[OF finite_E union_subset])
  finally show ?thesis .
qed

lemma sum_card_range_tree_child_edge_range_list_le_outgoing_edges_chain:
  assumes mono: "nondecreasing_from a bs"
  shows "sum_list (map card (range_tree_child_edge_range_list S a betas bs))
    \<le> card (outgoing_edges (range_tree_chain S a bs B))"
proof -
  let ?Rs = "range_tree_child_edge_range_list S a betas bs"
  let ?Xs = "range_tree_child_list S a bs"
  have disj: "pairwise_disjoint_list ?Rs"
    by (rule pairwise_disjoint_list_range_tree_child_edge_range_list[OF mono])
  have finite_sets: "\<And>R. R \<in> set ?Rs \<Longrightarrow> finite R"
    using range_tree_child_edge_range_list_member_subset_E
    by (meson finite_E finite_subset)
  have card_union:
    "card (\<Union>(set ?Rs)) = sum_list (map card ?Rs)"
    by (rule card_Union_pairwise_disjoint_list[OF disj finite_sets])
  have union_subset_children: "\<Union>(set ?Rs) \<subseteq> outgoing_edges (\<Union>(set ?Xs))"
  proof
    fix e
    assume "e \<in> \<Union>(set ?Rs)"
    then obtain R where R: "R \<in> set ?Rs" and eR: "e \<in> R"
      by blast
    obtain X where X: "X \<in> set ?Xs" and R_subset: "R \<subseteq> outgoing_edges X"
      using range_tree_child_edge_range_list_subset_outgoing_sources[OF R]
      by blast
    show "e \<in> outgoing_edges (\<Union>(set ?Xs))"
      using eR R_subset X unfolding outgoing_edges_def by blast
  qed
  have children_subset: "\<Union>(set ?Xs) \<subseteq> range_tree_chain S a bs B"
    by (rule Union_range_tree_child_list_subset_chain)
  have union_subset:
    "\<Union>(set ?Rs) \<subseteq> outgoing_edges (range_tree_chain S a bs B)"
    using union_subset_children outgoing_edges_mono[OF children_subset] by blast
  have "sum_list (map card ?Rs) = card (\<Union>(set ?Rs))"
    using card_union by simp
  also have "\<dots> \<le> card (outgoing_edges (range_tree_chain S a bs B))"
    by (rule card_mono) (simp_all add: union_subset)
  finally show ?thesis .
qed

fun range_tree_child_direct_edge_range_list where
  "range_tree_child_direct_edge_range_list S B a [] [] = []"
| "range_tree_child_direct_edge_range_list S B a [] (b # bs) = []"
| "range_tree_child_direct_edge_range_list S B a (beta # betas) [] = []"
| "range_tree_child_direct_edge_range_list S B a (beta # betas) (b # bs) =
    outgoing_edges_range (range_tree S a (Fin b)) beta B #
    range_tree_child_direct_edge_range_list S B b betas bs"

fun range_tree_child_zero_edge_range_list where
  "range_tree_child_zero_edge_range_list S a [] [] = []"
| "range_tree_child_zero_edge_range_list S a [] (b # bs) = []"
| "range_tree_child_zero_edge_range_list S a (beta # betas) [] = []"
| "range_tree_child_zero_edge_range_list S a (beta # betas) (b # bs) =
    outgoing_edges_range (range_tree S a (Fin b)) 0 (Fin beta) #
    range_tree_child_zero_edge_range_list S b betas bs"

fun range_tree_child_full_edge_range_list where
  "range_tree_child_full_edge_range_list S B a [] = []"
| "range_tree_child_full_edge_range_list S B a (b # bs) =
    outgoing_edges_range (range_tree S a (Fin b)) 0 B #
    range_tree_child_full_edge_range_list S B b bs"

fun range_tree_child_bound_pair_list where
  "range_tree_child_bound_pair_list S a [] [] = []"
| "range_tree_child_bound_pair_list S a [] (b # bs) = []"
| "range_tree_child_bound_pair_list S a (beta # betas) [] = []"
| "range_tree_child_bound_pair_list S a (beta # betas) (b # bs) =
    (range_tree S a (Fin b), Fin beta) #
    range_tree_child_bound_pair_list S b betas bs"

lemma range_tree_child_direct_edge_range_list_subset_outgoing_sources:
  assumes "Y \<in> set (range_tree_child_direct_edge_range_list S B a betas bs)"
  shows "\<exists>X\<in>set (range_tree_child_list S a bs). Y \<subseteq> outgoing_edges X"
  using assms
proof (induction betas arbitrary: a bs)
  case Nil
  then show ?case
    by (cases bs) simp_all
next
  case (Cons beta betas)
  show ?case
  proof (cases bs)
    case Nil
    then show ?thesis
      using Cons.prems by simp
  next
    case (Cons b bs')
    let ?head = "outgoing_edges_range (range_tree S a (Fin b)) beta B"
    let ?tail = "range_tree_child_direct_edge_range_list S B b betas bs'"
    have Y_cases: "Y = ?head \<or> Y \<in> set ?tail"
      using Cons.prems Cons by simp
    then show ?thesis
    proof
      assume Y_head: "Y = ?head"
      have "?head \<subseteq> outgoing_edges (range_tree S a (Fin b))"
        by (rule outgoing_edges_range_subset_outgoing_edges)
      then show ?thesis
        unfolding Cons Y_head by auto
    next
      assume Y_tail: "Y \<in> set ?tail"
      obtain X where X: "X \<in> set (range_tree_child_list S b bs')"
        and YX: "Y \<subseteq> outgoing_edges X"
        using Cons.IH[OF Y_tail] by blast
      show ?thesis
        using X YX unfolding Cons by auto
    qed
  qed
qed

lemma range_tree_child_direct_edge_range_list_member_subset_E:
  assumes "Y \<in> set (range_tree_child_direct_edge_range_list S B a betas bs)"
  shows "Y \<subseteq> E"
proof
  fix e
  assume eY: "e \<in> Y"
  obtain X where "X \<in> set (range_tree_child_list S a bs)"
    and Y_subset: "Y \<subseteq> outgoing_edges X"
    using range_tree_child_direct_edge_range_list_subset_outgoing_sources[OF assms]
    by blast
  then have "e \<in> outgoing_edges X"
    using eY by blast
  then show "e \<in> E"
    unfolding outgoing_edges_def by blast
qed

lemma pairwise_disjoint_list_range_tree_child_direct_edge_range_list:
  assumes mono: "nondecreasing_from a bs"
  shows "pairwise_disjoint_list
    (range_tree_child_direct_edge_range_list S B a betas bs)"
  using mono
proof (induction betas arbitrary: a bs)
  case Nil
  then show ?case
    by (cases bs) simp_all
next
  case (Cons beta betas)
  show ?case
  proof (cases bs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons b bs')
    let ?head = "outgoing_edges_range (range_tree S a (Fin b)) beta B"
    let ?tail = "range_tree_child_direct_edge_range_list S B b betas bs'"
    have a_le_b: "a \<le> b"
      using Cons.prems Cons by simp
    have mono_tail: "nondecreasing_from b bs'"
      using Cons.prems Cons by simp
    have head_tail_disj: "\<forall>Y\<in>set ?tail. ?head \<inter> Y = {}"
    proof
      fix Y
      assume Y: "Y \<in> set ?tail"
      obtain X where X: "X \<in> set (range_tree_child_list S b bs')"
        and YX: "Y \<subseteq> outgoing_edges X"
        using range_tree_child_direct_edge_range_list_subset_outgoing_sources[OF Y]
        by blast
      have X_subset: "X \<subseteq> range_tree_chain S b bs' Infinity"
        using X Union_range_tree_child_list_subset_chain[of S b bs' Infinity]
        by blast
      have source_disj: "range_tree S a (Fin b) \<inter> X = {}"
        using range_tree_disjoint_range_tree_chain_tail
          [OF a_le_b mono_tail, of S Infinity] X_subset by blast
      have out_disj:
        "outgoing_edges (range_tree S a (Fin b)) \<inter> outgoing_edges X = {}"
        by (rule outgoing_edges_disjoint_if_sources_disjoint[OF source_disj])
      have head_subset: "?head \<subseteq> outgoing_edges (range_tree S a (Fin b))"
        by (rule outgoing_edges_range_subset_outgoing_edges)
      show "?head \<inter> Y = {}"
        using head_subset YX out_disj by blast
    qed
    have tail_disj: "pairwise_disjoint_list ?tail"
      by (rule Cons.IH[OF mono_tail])
    show ?thesis
      unfolding Cons by (simp add: head_tail_disj tail_disj)
  qed
qed

lemma sum_card_range_tree_child_direct_edge_range_list_le_edge_count:
  assumes mono: "nondecreasing_from a bs"
  shows "sum_list
    (map card (range_tree_child_direct_edge_range_list S B a betas bs))
    \<le> edge_count"
proof -
  let ?Xs = "range_tree_child_direct_edge_range_list S B a betas bs"
  have disj: "pairwise_disjoint_list ?Xs"
    by (rule pairwise_disjoint_list_range_tree_child_direct_edge_range_list
      [OF mono])
  have finite_sets: "\<And>X. X \<in> set ?Xs \<Longrightarrow> finite X"
    using range_tree_child_direct_edge_range_list_member_subset_E
    by (meson finite_E finite_subset)
  have card_union:
    "card (\<Union>(set ?Xs)) = sum_list (map card ?Xs)"
    by (rule card_Union_pairwise_disjoint_list[OF disj finite_sets])
  have union_subset: "\<Union>(set ?Xs) \<subseteq> E"
  proof
    fix e
    assume "e \<in> \<Union>(set ?Xs)"
    then obtain X where X: "X \<in> set ?Xs" and eX: "e \<in> X"
      by blast
    show "e \<in> E"
      using range_tree_child_direct_edge_range_list_member_subset_E[OF X] eX
      by blast
  qed
  have "sum_list (map card ?Xs) = card (\<Union>(set ?Xs))"
    using card_union by simp
  also have "\<dots> \<le> edge_count"
    unfolding edge_count_def by (rule card_mono[OF finite_E union_subset])
  finally show ?thesis .
qed

lemma sum_card_range_tree_child_direct_edge_range_list_le_outgoing_edges_chain:
  assumes mono: "nondecreasing_from a bs"
  shows "sum_list
    (map card (range_tree_child_direct_edge_range_list S B' a betas bs))
    \<le> card (outgoing_edges (range_tree_chain S a bs B))"
proof -
  let ?Rs = "range_tree_child_direct_edge_range_list S B' a betas bs"
  let ?Xs = "range_tree_child_list S a bs"
  have disj: "pairwise_disjoint_list ?Rs"
    by (rule pairwise_disjoint_list_range_tree_child_direct_edge_range_list
      [OF mono])
  have finite_sets: "\<And>R. R \<in> set ?Rs \<Longrightarrow> finite R"
    using range_tree_child_direct_edge_range_list_member_subset_E
    by (meson finite_E finite_subset)
  have card_union:
    "card (\<Union>(set ?Rs)) = sum_list (map card ?Rs)"
    by (rule card_Union_pairwise_disjoint_list[OF disj finite_sets])
  have union_subset_children: "\<Union>(set ?Rs) \<subseteq> outgoing_edges (\<Union>(set ?Xs))"
  proof
    fix e
    assume "e \<in> \<Union>(set ?Rs)"
    then obtain R where R: "R \<in> set ?Rs" and eR: "e \<in> R"
      by blast
    obtain X where X: "X \<in> set ?Xs" and R_subset: "R \<subseteq> outgoing_edges X"
      using range_tree_child_direct_edge_range_list_subset_outgoing_sources[OF R]
      by blast
    show "e \<in> outgoing_edges (\<Union>(set ?Xs))"
      using eR R_subset X unfolding outgoing_edges_def by blast
  qed
  have children_subset: "\<Union>(set ?Xs) \<subseteq> range_tree_chain S a bs B"
    by (rule Union_range_tree_child_list_subset_chain)
  have union_subset:
    "\<Union>(set ?Rs) \<subseteq> outgoing_edges (range_tree_chain S a bs B)"
    using union_subset_children outgoing_edges_mono[OF children_subset] by blast
  have "sum_list (map card ?Rs) = card (\<Union>(set ?Rs))"
    using card_union by simp
  also have "\<dots> \<le> card (outgoing_edges (range_tree_chain S a bs B))"
    by (rule card_mono) (simp_all add: union_subset)
  finally show ?thesis .
qed

lemma range_tree_nonneg_edge_value:
  assumes edge: "(u, v) \<in> E"
    and u_range: "u \<in> range_tree S a B"
  shows "0 \<le> dist s u + w u v"
proof -
  have reach_u: "reachable s u"
    using u_range unfolding range_tree_def tree_set_def tree_path_def by blast
  have "0 \<le> dist s u"
    by (rule dist_nonneg[OF reach_u])
  moreover have "0 \<le> w u v"
    by (rule nonneg_weight[OF edge])
  ultimately show ?thesis
    by linarith
qed

lemma sum_card_range_tree_child_zero_direct_edge_ranges_le_full:
  assumes bounds: "bounds_le B betas"
  shows
    "sum_list (map card (range_tree_child_zero_edge_range_list S a betas bs)) +
     sum_list
       (map card (range_tree_child_direct_edge_range_list S B a betas bs))
     \<le> sum_list (map card (range_tree_child_full_edge_range_list S B a bs))"
  using bounds
proof (induction betas arbitrary: a bs)
  case Nil
  then show ?case
    by (cases bs) simp_all
next
  case (Cons beta betas)
  show ?case
  proof (cases bs)
    case Nil
    then show ?thesis
      by simp
  next
    case (Cons b bs')
    have beta_le_B: "bound_le (Fin beta) B"
      using Cons.prems by simp
    have bounds_tail: "bounds_le B betas"
      using Cons.prems by simp
    have head:
      "card (outgoing_edges_range (range_tree S a (Fin b)) 0 (Fin beta)) +
       card (outgoing_edges_range (range_tree S a (Fin b)) beta B)
       \<le> card (outgoing_edges_range (range_tree S a (Fin b)) 0 B)"
      by (rule card_outgoing_edges_range_zero_lower_direct_split_le
        [OF beta_le_B range_tree_nonneg_edge_value])
    have tail:
      "sum_list (map card (range_tree_child_zero_edge_range_list S b betas bs')) +
       sum_list
         (map card (range_tree_child_direct_edge_range_list S B b betas bs'))
       \<le> sum_list (map card
         (range_tree_child_full_edge_range_list S B b bs'))"
      by (rule Cons.IH[OF bounds_tail])
    show ?thesis
      unfolding Cons by simp (use head tail in linarith)
  qed
qed

lemma range_tree_child_full_edge_range_list_eq_map:
  "range_tree_child_full_edge_range_list S B a bs =
    map (\<lambda>U. outgoing_edges_range U 0 B) (range_tree_child_list S a bs)"
  by (induction bs arbitrary: a) simp_all

lemma sum_card_range_tree_child_full_edge_range_list_le_outgoing_edges_range_chain:
  assumes mono: "nondecreasing_from a bs"
  shows "sum_list (map card (range_tree_child_full_edge_range_list S B a bs))
    \<le> card (outgoing_edges_range (range_tree_chain S a bs C) 0 B)"
proof -
  let ?Xs = "range_tree_child_list S a bs"
  let ?Rs = "map (\<lambda>U. outgoing_edges_range U 0 B) ?Xs"
  have disj_children: "pairwise_disjoint_list ?Xs"
    using mono
  proof (induction bs arbitrary: a)
    case Nil
    then show ?case by simp
  next
    case (Cons b bs)
    have a_le_b: "a \<le> b"
      using Cons.prems by simp
    have mono_tail: "nondecreasing_from b bs"
      using Cons.prems by simp
    have head_tail_disj:
      "\<And>Y. Y \<in> set (range_tree_child_list S b bs) \<Longrightarrow>
        range_tree S a (Fin b) \<inter> Y = {}"
    proof -
      fix Y
      assume Y: "Y \<in> set (range_tree_child_list S b bs)"
      have "Y \<subseteq> range_tree_chain S b bs Infinity"
        using Y Union_range_tree_child_list_subset_chain[of S b bs Infinity]
        by blast
      moreover have
        "range_tree S a (Fin b) \<inter> range_tree_chain S b bs Infinity = {}"
        using range_tree_disjoint_range_tree_chain_tail[OF a_le_b mono_tail] .
      ultimately show "range_tree S a (Fin b) \<inter> Y = {}"
        by blast
    qed
    show ?case
      using head_tail_disj Cons.IH[OF mono_tail] by simp
  qed
  have disj: "pairwise_disjoint_list ?Rs"
    by (rule pairwise_disjoint_list_outgoing_edges_range[OF disj_children])
  have finite_sets: "\<And>R. R \<in> set ?Rs \<Longrightarrow> finite R"
    by auto
  have card_union:
    "card (\<Union>(set ?Rs)) = sum_list (map card ?Rs)"
    by (rule card_Union_pairwise_disjoint_list[OF disj finite_sets])
  have children_subset: "\<Union>(set ?Xs) \<subseteq> range_tree_chain S a bs C"
    by (rule Union_range_tree_child_list_subset_chain)
  have union_subset:
    "\<Union>(set ?Rs) \<subseteq> outgoing_edges_range (range_tree_chain S a bs C) 0 B"
  proof
    fix e
    assume "e \<in> \<Union>(set ?Rs)"
    then obtain X where X: "X \<in> set ?Xs"
      and eX: "e \<in> outgoing_edges_range X 0 B"
      by auto
    have X_subset: "X \<subseteq> range_tree_chain S a bs C"
      using X children_subset by blast
    show "e \<in> outgoing_edges_range (range_tree_chain S a bs C) 0 B"
      using outgoing_edges_range_mono_sources[OF X_subset] eX by blast
  qed
  have "sum_list (map card (range_tree_child_full_edge_range_list S B a bs)) =
      sum_list (map card ?Rs)"
    by (simp add: range_tree_child_full_edge_range_list_eq_map)
  also have "\<dots> = card (\<Union>(set ?Rs))"
    using card_union by simp
  also have "\<dots> \<le>
      card (outgoing_edges_range (range_tree_chain S a bs C) 0 B)"
    by (rule card_mono[OF finite_outgoing_edges_range union_subset])
  finally show ?thesis .
qed

lemma sum_card_range_tree_child_zero_direct_edge_ranges_le_outgoing_edges_range_chain:
  assumes mono: "nondecreasing_from a bs"
    and bounds: "bounds_le B betas"
  shows
    "sum_list (map card (range_tree_child_zero_edge_range_list S a betas bs)) +
     sum_list
       (map card (range_tree_child_direct_edge_range_list S B a betas bs))
     \<le> card (outgoing_edges_range (range_tree_chain S a bs C) 0 B)"
proof -
  have split:
    "sum_list (map card (range_tree_child_zero_edge_range_list S a betas bs)) +
     sum_list
       (map card (range_tree_child_direct_edge_range_list S B a betas bs))
     \<le> sum_list (map card (range_tree_child_full_edge_range_list S B a bs))"
    by (rule sum_card_range_tree_child_zero_direct_edge_ranges_le_full
      [OF bounds])
  have full:
    "sum_list (map card (range_tree_child_full_edge_range_list S B a bs))
      \<le> card (outgoing_edges_range (range_tree_chain S a bs C) 0 B)"
    by (rule sum_card_range_tree_child_full_edge_range_list_le_outgoing_edges_range_chain
      [OF mono])
  show ?thesis
    using split full by linarith
qed

lemma weighted_sum_child_lower_direct_edge_ranges_le:
  assumes mono: "nondecreasing_from a bs"
  shows
    "h * sum_list (map card (range_tree_child_edge_range_list S a betas bs)) +
     t * sum_list
       (map card (range_tree_child_direct_edge_range_list S B a betas bs))
     \<le> (h + t) * edge_count"
proof -
  have lower:
    "sum_list (map card (range_tree_child_edge_range_list S a betas bs))
      \<le> edge_count"
    by (rule sum_card_range_tree_child_edge_range_list_le_edge_count[OF mono])
  have direct:
    "sum_list
      (map card (range_tree_child_direct_edge_range_list S B a betas bs))
      \<le> edge_count"
    by (rule sum_card_range_tree_child_direct_edge_range_list_le_edge_count
      [OF mono])
  have lower_w:
    "h * sum_list (map card (range_tree_child_edge_range_list S a betas bs))
      \<le> h * edge_count"
    using lower by simp
  have direct_w:
    "t * sum_list
       (map card (range_tree_child_direct_edge_range_list S B a betas bs))
      \<le> t * edge_count"
    using direct by simp
  have "h * sum_list (map card (range_tree_child_edge_range_list S a betas bs)) +
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list S B a betas bs))
      \<le> h * edge_count + t * edge_count"
    using lower_w direct_w by linarith
  also have "\<dots> = (h + t) * edge_count"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma weighted_sum_child_lower_direct_edge_ranges_le_outgoing_edges_chain:
  assumes mono: "nondecreasing_from a bs"
  shows
    "h * sum_list (map card (range_tree_child_edge_range_list S a betas bs)) +
     t * sum_list
       (map card (range_tree_child_direct_edge_range_list S B' a betas bs))
     \<le> (h + t) * card (outgoing_edges (range_tree_chain S a bs B))"
proof -
  have lower:
    "sum_list (map card (range_tree_child_edge_range_list S a betas bs))
      \<le> card (outgoing_edges (range_tree_chain S a bs B))"
    by (rule sum_card_range_tree_child_edge_range_list_le_outgoing_edges_chain
      [OF mono])
  have direct:
    "sum_list
      (map card (range_tree_child_direct_edge_range_list S B' a betas bs))
      \<le> card (outgoing_edges (range_tree_chain S a bs B))"
    by (rule sum_card_range_tree_child_direct_edge_range_list_le_outgoing_edges_chain
      [OF mono])
  have lower_w:
    "h * sum_list (map card (range_tree_child_edge_range_list S a betas bs))
      \<le> h * card (outgoing_edges (range_tree_chain S a bs B))"
    using lower by simp
  have direct_w:
    "t * sum_list
       (map card (range_tree_child_direct_edge_range_list S B' a betas bs))
      \<le> t * card (outgoing_edges (range_tree_chain S a bs B))"
    using direct by simp
  have "h * sum_list (map card (range_tree_child_edge_range_list S a betas bs)) +
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list S B' a betas bs))
      \<le> h * card (outgoing_edges (range_tree_chain S a bs B)) +
        t * card (outgoing_edges (range_tree_chain S a bs B))"
    using lower_w direct_w by linarith
  also have "\<dots> = (h + t) * card (outgoing_edges (range_tree_chain S a bs B))"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma sum_card_outgoing_edges_le_degree:
  assumes degree: "edge_outdegree_le \<Delta>"
    and sets: "\<And>X. X \<in> set Xs \<Longrightarrow> X \<subseteq> V"
  shows "sum_list (map (\<lambda>X. card (outgoing_edges X)) Xs) \<le>
    \<Delta> * sum_list (map card Xs)"
  using sets
proof (induction Xs)
  case Nil
  then show ?case by simp
next
  case (Cons X Xs)
  have X_subset: "X \<subseteq> V"
    using Cons.prems by simp
  have X_bound: "card (outgoing_edges X) \<le> \<Delta> * card X"
    by (rule card_outgoing_edges_le[OF X_subset degree])
  have tail_bound:
    "sum_list (map (\<lambda>X. card (outgoing_edges X)) Xs) \<le>
      \<Delta> * sum_list (map card Xs)"
    using Cons.IH Cons.prems by simp
  have "card (outgoing_edges X) +
      sum_list (map (\<lambda>X. card (outgoing_edges X)) Xs) \<le>
      \<Delta> * card X + \<Delta> * sum_list (map card Xs)"
    using X_bound tail_bound by simp
  also have "\<dots> = \<Delta> * sum_list (map card (X # Xs))"
    by (simp add: algebra_simps)
  finally show ?case
    by simp
qed

lemma card_outgoing_edges_Union_list_eq_sum:
  assumes disj: "pairwise_disjoint_list Xs"
  shows "card (outgoing_edges (\<Union>(set Xs))) =
    sum_list (map (\<lambda>X. card (outgoing_edges X)) Xs)"
proof -
  have disj_edges: "pairwise_disjoint_list (map outgoing_edges Xs)"
    using pairwise_disjoint_list_outgoing_edges[OF disj] .
  have finite_edges: "\<And>X. X \<in> set (map outgoing_edges Xs) \<Longrightarrow> finite X"
    by auto
  have "card (outgoing_edges (\<Union>(set Xs))) =
      card (\<Union>(set (map outgoing_edges Xs)))"
    using outgoing_edges_Union_list[of Xs] by simp
  also have "\<dots> = sum_list (map (\<lambda>Y. card Y) (map outgoing_edges Xs))"
    by (rule card_Union_pairwise_disjoint_list[OF disj_edges finite_edges])
  also have "\<dots> = sum_list (map (\<lambda>X. card (outgoing_edges X)) Xs)"
    by (induction Xs) simp_all
  finally show ?thesis .
qed

lemma range_tree_chain_list_pairwise_disjoint:
  assumes mono: "nondecreasing_from a bs"
  shows "pairwise_disjoint_list (range_tree_chain_list S a bs B)"
  using assms
proof (induction bs arbitrary: a)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  have a_le_b: "a \<le> b"
    using Cons.prems by simp
  have mono_tail: "nondecreasing_from b bs"
    using Cons.prems by simp
  have head_tail_disj:
    "\<And>Y. Y \<in> set (range_tree_chain_list S b bs B) \<Longrightarrow>
      range_tree S a (Fin b) \<inter> Y = {}"
  proof -
    fix Y
    assume Y: "Y \<in> set (range_tree_chain_list S b bs B)"
    have "Y \<subseteq> range_tree_chain S b bs B"
      using Y Union_range_tree_chain_list[of S b bs B] by blast
    moreover have
      "range_tree S a (Fin b) \<inter> range_tree_chain S b bs B = {}"
      using range_tree_disjoint_range_tree_chain_tail[OF a_le_b mono_tail] .
    ultimately show "range_tree S a (Fin b) \<inter> Y = {}"
      by blast
  qed
  show ?case
    using head_tail_disj Cons.IH[OF mono_tail] by simp
qed

lemma range_tree_child_list_pairwise_disjoint:
  assumes mono: "nondecreasing_from a bs"
  shows "pairwise_disjoint_list (range_tree_child_list S a bs)"
  using assms
proof (induction bs arbitrary: a)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  have a_le_b: "a \<le> b"
    using Cons.prems by simp
  have mono_tail: "nondecreasing_from b bs"
    using Cons.prems by simp
  have head_tail_disj:
    "\<And>Y. Y \<in> set (range_tree_child_list S b bs) \<Longrightarrow>
      range_tree S a (Fin b) \<inter> Y = {}"
  proof -
    fix Y
    assume Y: "Y \<in> set (range_tree_child_list S b bs)"
    have "Y \<subseteq> range_tree_chain S b bs Infinity"
      using Y Union_range_tree_child_list_subset_chain[of S b bs Infinity] by blast
    moreover have
      "range_tree S a (Fin b) \<inter> range_tree_chain S b bs Infinity = {}"
      using range_tree_disjoint_range_tree_chain_tail[OF a_le_b mono_tail] .
    ultimately show "range_tree S a (Fin b) \<inter> Y = {}"
      by blast
  qed
  show ?case
    using head_tail_disj Cons.IH[OF mono_tail] by simp
qed

theorem card_range_tree_child_list_le_chain:
  assumes mono: "nondecreasing_from a bs"
  shows "sum_list (map card (range_tree_child_list S a bs)) \<le>
    card (range_tree_chain S a bs B)"
proof -
  let ?Xs = "range_tree_child_list S a bs"
  have disj: "pairwise_disjoint_list ?Xs"
    by (rule range_tree_child_list_pairwise_disjoint[OF mono])
  have finite_sets: "\<And>X. X \<in> set ?Xs \<Longrightarrow> finite X"
    using range_tree_child_list_set_subset_chain_list
      finite_range_tree_chain_list_sets by blast
  have card_union:
    "card (\<Union>(set ?Xs)) = sum_list (map card ?Xs)"
    by (rule card_Union_pairwise_disjoint_list[OF disj finite_sets])
  have subset: "\<Union>(set ?Xs) \<subseteq> range_tree_chain S a bs B"
    by (rule Union_range_tree_child_list_subset_chain)
  have "sum_list (map card ?Xs) = card (\<Union>(set ?Xs))"
    using card_union by simp
  also have "\<dots> \<le> card (range_tree_chain S a bs B)"
    by (rule card_mono) (simp_all add: subset)
  finally show ?thesis .
qed

lemma sum_card_list_all2_le:
  assumes "list_all2 (\<lambda>X Y. card X \<le> card Y) Xs Ys"
  shows "sum_list (map card Xs) \<le> sum_list (map card Ys)"
  using assms
proof (induction rule: list_all2_induct)
  case Nil
  then show ?case by simp
next
  case (Cons X Y Xs Ys)
  then show ?case by simp
qed

lemma sum_card_dominated_by_disjoint_union:
  assumes disj: "pairwise_disjoint_list Ys"
    and finite_sets: "\<And>Y. Y \<in> set Ys \<Longrightarrow> finite Y"
    and dominated: "list_all2 (\<lambda>X Y. card X \<le> card Y) Xs Ys"
  shows "sum_list (map card Xs) \<le> card (\<Union>(set Ys))"
proof -
  have "sum_list (map card Xs) \<le> sum_list (map card Ys)"
    by (rule sum_card_list_all2_le[OF dominated])
  also have "\<dots> = card (\<Union>(set Ys))"
    using card_Union_pairwise_disjoint_list[OF disj finite_sets] by simp
  finally show ?thesis .
qed

theorem sum_card_dominated_by_range_tree_child_list_le_chain:
  assumes mono: "nondecreasing_from a bs"
    and dominated:
      "list_all2 (\<lambda>X R. card X \<le> card R) Xs
        (range_tree_child_list S a bs)"
  shows "sum_list (map card Xs) \<le> card (range_tree_chain S a bs B)"
proof -
  have "sum_list (map card Xs) \<le>
      sum_list (map card (range_tree_child_list S a bs))"
    by (rule sum_card_list_all2_le[OF dominated])
  also have "\<dots> \<le> card (range_tree_chain S a bs B)"
    by (rule card_range_tree_child_list_le_chain[OF mono])
  finally show ?thesis .
qed

theorem card_outgoing_edges_range_tree_chain_eq_sum_list:
  assumes mono: "nondecreasing_from a bs"
  shows "card (outgoing_edges (range_tree_chain S a bs B)) =
    sum_list
      (map (\<lambda>X. card (outgoing_edges X)) (range_tree_chain_list S a bs B))"
proof -
  have disj: "pairwise_disjoint_list (range_tree_chain_list S a bs B)"
    using range_tree_chain_list_pairwise_disjoint[OF mono] .
  have "card (outgoing_edges (range_tree_chain S a bs B)) =
      card (outgoing_edges (\<Union>(set (range_tree_chain_list S a bs B))))"
    using Union_range_tree_chain_list[of S a bs B] by simp
  also have "\<dots> =
      sum_list
        (map (\<lambda>X. card (outgoing_edges X)) (range_tree_chain_list S a bs B))"
    by (rule card_outgoing_edges_Union_list_eq_sum[OF disj])
  finally show ?thesis .
qed

theorem card_outgoing_edges_range_tree_child_list_le_chain:
  assumes mono: "nondecreasing_from a bs"
  shows "sum_list
      (map (\<lambda>X. card (outgoing_edges X)) (range_tree_child_list S a bs)) \<le>
    card (outgoing_edges (range_tree_chain S a bs B))"
proof -
  let ?Xs = "range_tree_child_list S a bs"
  have disj: "pairwise_disjoint_list ?Xs"
    by (rule range_tree_child_list_pairwise_disjoint[OF mono])
  have card_union:
    "card (outgoing_edges (\<Union>(set ?Xs))) =
      sum_list (map (\<lambda>X. card (outgoing_edges X)) ?Xs)"
    by (rule card_outgoing_edges_Union_list_eq_sum[OF disj])
  have subset: "\<Union>(set ?Xs) \<subseteq> range_tree_chain S a bs B"
    by (rule Union_range_tree_child_list_subset_chain)
  have outgoing_subset:
    "outgoing_edges (\<Union>(set ?Xs)) \<subseteq>
      outgoing_edges (range_tree_chain S a bs B)"
    by (rule outgoing_edges_mono[OF subset])
  have "sum_list (map (\<lambda>X. card (outgoing_edges X)) ?Xs) =
      card (outgoing_edges (\<Union>(set ?Xs)))"
    using card_union by simp
  also have "\<dots> \<le> card (outgoing_edges (range_tree_chain S a bs B))"
    by (rule card_mono) (simp_all add: outgoing_subset)
  finally show ?thesis .
qed

lemma sum_outgoing_card_list_all2_le:
  assumes "list_all2
    (\<lambda>X Y. card (outgoing_edges X) \<le> card (outgoing_edges Y)) Xs Ys"
  shows "sum_list (map (\<lambda>X. card (outgoing_edges X)) Xs) \<le>
    sum_list (map (\<lambda>Y. card (outgoing_edges Y)) Ys)"
  using assms
proof (induction rule: list_all2_induct)
  case Nil
  then show ?case by simp
next
  case (Cons X Y Xs Ys)
  then show ?case by simp
qed

theorem sum_outgoing_dominated_by_range_tree_child_list_le_chain:
  assumes mono: "nondecreasing_from a bs"
    and dominated:
      "list_all2
        (\<lambda>X R. card (outgoing_edges X) \<le> card (outgoing_edges R)) Xs
        (range_tree_child_list S a bs)"
  shows "sum_list (map (\<lambda>X. card (outgoing_edges X)) Xs) \<le>
    card (outgoing_edges (range_tree_chain S a bs B))"
proof -
  have "sum_list (map (\<lambda>X. card (outgoing_edges X)) Xs) \<le>
      sum_list
        (map (\<lambda>R. card (outgoing_edges R)) (range_tree_child_list S a bs))"
    by (rule sum_outgoing_card_list_all2_le[OF dominated])
  also have "\<dots> \<le> card (outgoing_edges (range_tree_chain S a bs B))"
    by (rule card_outgoing_edges_range_tree_child_list_le_chain[OF mono])
  finally show ?thesis .
qed

lemma edge_costs_le_range_tree_chain_outgoing:
  assumes mono: "nondecreasing_from a bs"
    and costs: "list_all2 (\<lambda>c X. c \<le> C * card (outgoing_edges X)) costs
      (range_tree_chain_list S a bs B)"
  shows "sum_list costs \<le> C * card (outgoing_edges (range_tree_chain S a bs B))"
proof -
  have "sum_list costs \<le>
      sum_list
        (map (\<lambda>X. C * card (outgoing_edges X))
          (range_tree_chain_list S a bs B))"
    using costs
  proof (induction rule: list_all2_induct)
    case Nil
    then show ?case by simp
  next
    case (Cons c X costs Xs)
    then show ?case by simp
  qed
  also have "\<dots> =
      C * sum_list
        (map (\<lambda>X. card (outgoing_edges X)) (range_tree_chain_list S a bs B))"
  proof -
    define Xs where "Xs = range_tree_chain_list S a bs B"
    have "sum_list (map (\<lambda>X. C * card (outgoing_edges X)) Xs) =
        C * sum_list (map (\<lambda>X. card (outgoing_edges X)) Xs)"
      by (induction Xs) (simp_all add: algebra_simps)
    then show ?thesis
      unfolding Xs_def .
  qed
  also have "\<dots> = C * card (outgoing_edges (range_tree_chain S a bs B))"
    using card_outgoing_edges_range_tree_chain_eq_sum_list[OF mono, of S B] by simp
  finally show ?thesis .
qed

text \<open>
  These two cost shapes are the local language of the runtime proof.  The level
  bound \<open>level_range_cost_bound\<close> is the simple recurrence form: a vertex term
  scaled by the recursion level and an outgoing-edge term scaled by the range
  coefficient.  The amortised bound \<open>bmssp_amortized_cost_bound\<close> adds the
  extra direct-edge range term used by the bucketed partition, where direct
  inserts have their own cost story.

  The summation lemmas below say that if every recursive child call satisfies
  one of these bounds on its own range slice, then the sum of child costs can be
  rewritten as sums over the corresponding child range lists.  Later theories
  collapse those sums using the disjointness lemmas above.
\<close>

definition level_range_cost_bound where
  "level_range_cost_bound A R l X =
     A * l * card X + R * card (outgoing_edges X)"

definition bmssp_amortized_cost_bound where
  "bmssp_amortized_cost_bound A R h t q L B X =
     A * L * card X + (R + q * h) * card (outgoing_edges X) +
     t * card (outgoing_edges_range X 0 B)"

lemma sum_bmssp_amortized_child_bounds_le:
  assumes bounds:
    "list_all2 (\<lambda>c_child UB. case UB of (U_child, B_child) \<Rightarrow>
      c_child \<le>
        bmssp_amortized_cost_bound A R h t q L B_child U_child)
      child_costs (range_tree_child_bound_pair_list S a betas bs)"
  shows "sum_list child_costs \<le>
    A * L * sum_list (map card (range_tree_child_list S a bs)) +
    (R + q * h) *
      sum_list (map (\<lambda>U. card (outgoing_edges U))
        (range_tree_child_list S a bs)) +
    t * sum_list
      (map card (range_tree_child_zero_edge_range_list S a betas bs))"
  using bounds
proof (induction betas arbitrary: a bs child_costs)
  case Nil
  then have costs_nil: "child_costs = []"
    by (cases bs; cases child_costs) auto
  show ?case
    using costs_nil by simp
next
  case (Cons beta betas)
  note outer_prems = Cons.prems
  note outer_IH = Cons.IH
  show ?case
  proof (cases bs)
    case Nil
    then have costs_nil: "child_costs = []"
      using outer_prems by (cases child_costs) auto
    show ?thesis
      using Nil costs_nil by simp
  next
    case bs_Cons: (Cons b bs')
    show ?thesis
    proof (cases child_costs)
      case Nil
      then show ?thesis
        by simp
    next
      case costs_Cons: (Cons c_child child_costs_tail)
      have head:
        "c_child \<le>
          bmssp_amortized_cost_bound A R h t q L (Fin beta)
            (range_tree S a (Fin b))"
        using outer_prems unfolding bs_Cons costs_Cons by simp
      have tail_bounds:
        "list_all2 (\<lambda>c_child UB. case UB of (U_child, B_child) \<Rightarrow>
          c_child \<le>
            bmssp_amortized_cost_bound A R h t q L B_child U_child)
          child_costs_tail (range_tree_child_bound_pair_list S b betas bs')"
        using outer_prems unfolding bs_Cons costs_Cons by simp
      have tail:
        "sum_list child_costs_tail \<le>
          A * L * sum_list (map card (range_tree_child_list S b bs')) +
          (R + q * h) *
            sum_list (map (\<lambda>U. card (outgoing_edges U))
              (range_tree_child_list S b bs')) +
          t * sum_list
            (map card (range_tree_child_zero_edge_range_list S b betas bs'))"
        by (rule outer_IH[OF tail_bounds])
      have head_unfolded:
        "c_child \<le>
          A * L * card (range_tree S a (Fin b)) +
          (R + q * h) * card (outgoing_edges (range_tree S a (Fin b))) +
          t * card (outgoing_edges_range (range_tree S a (Fin b)) 0
            (Fin beta))"
        using head unfolding bmssp_amortized_cost_bound_def .
      show ?thesis
        unfolding bs_Cons costs_Cons
        using head_unfolded tail by (simp add: algebra_simps)
    qed
  qed
qed

lemma child_costs_le_level_range_chain_bound:
  assumes mono: "nondecreasing_from a bs"
    and costs: "list_all2 (\<lambda>c X. c \<le> level_range_cost_bound A R l X) costs
      (range_tree_chain_list S a bs B)"
  shows "sum_list costs \<le>
    A * l * card (range_tree_chain S a bs B) +
    R * card (outgoing_edges (range_tree_chain S a bs B))"
proof -
  define Xs where "Xs = range_tree_chain_list S a bs B"
  have cost_sum:
    "sum_list costs \<le> sum_list (map (level_range_cost_bound A R l) Xs)"
    using costs unfolding Xs_def
  proof (induction rule: list_all2_induct)
    case Nil
    then show ?case by simp
  next
    case (Cons c X costs Xs)
    then show ?case
      unfolding level_range_cost_bound_def by simp
  qed
  have split_sum:
    "sum_list (map (level_range_cost_bound A R l) Xs) =
      A * l * sum_list (map (\<lambda>X. card X) Xs) +
      R * sum_list (map (\<lambda>X. card (outgoing_edges X)) Xs)"
  proof (induction Xs)
    case Nil
    then show ?case
      unfolding level_range_cost_bound_def by simp
  next
    case (Cons X Xs)
    then show ?case
      unfolding level_range_cost_bound_def by (simp add: algebra_simps)
  qed
  have card_sum:
    "sum_list (map (\<lambda>X. card X) Xs) = card (range_tree_chain S a bs B)"
    using card_range_tree_chain_eq_sum_list[OF mono, of S B]
    unfolding Xs_def by simp
  have edge_sum:
    "sum_list (map (\<lambda>X. card (outgoing_edges X)) Xs) =
      card (outgoing_edges (range_tree_chain S a bs B))"
    using card_outgoing_edges_range_tree_chain_eq_sum_list[OF mono, of S B]
    unfolding Xs_def by simp
  show ?thesis
    using cost_sum split_sum card_sum edge_sum by simp
qed

theorem concrete_partition_loop_trace_card_decomposition:
  assumes trace: "concrete_partition_loop_trace P B a bs d' B' Us U"
  shows "card U =
    card (bound_tree P (Fin a)) + card (range_tree_chain P a bs B')"
proof -
  have mono: "nondecreasing_from a bs"
    and bounds: "bounds_le B' (a # bs)"
    using trace unfolding concrete_partition_loop_trace_def by blast+
  have post: "bmssp_post_full d P B d' B' U"
    using concrete_partition_loop_trace_post[OF trace] .
  then have U_eq: "U = bound_tree P B'"
    unfolding bmssp_post_full_def by blast
  show ?thesis
    using card_bound_tree_range_chain_union[OF mono bounds, of P] U_eq by simp
qed

theorem concrete_partition_loop_trace_range_card_le:
  assumes trace: "concrete_partition_loop_trace P B a bs d' B' Us U"
  shows "card (range_tree_chain P a bs B') \<le> card U"
  using concrete_partition_loop_trace_card_decomposition[OF trace]
  by simp

definition concrete_capped_step_core_cost where
  "concrete_capped_step_core_cost k cap d S B child_costs =
     fp_iter_capped_scan_cost k cap d S S B + sum_list child_costs"

definition base_case_scan_cost where
  "base_case_scan_cost \<Delta> k x B = card (outgoing_edges (base_case_vertices k x B))"

theorem base_case_scan_cost_le:
  assumes degree: "edge_outdegree_le \<Delta>"
  shows "base_case_scan_cost \<Delta> k x B \<le> \<Delta> * k"
proof -
  have order_subset: "set (base_case_order x B) \<subseteq> V"
    using base_case_order_set[of x B]
    unfolding bound_tree_def by auto
  have vertices_subset: "base_case_vertices k x B \<subseteq> V"
  proof (cases "length (base_case_order x B) \<le> k")
    case True
    then show ?thesis
      using order_subset unfolding base_case_vertices_def by (simp add: Let_def)
  next
    case False
    then show ?thesis
      using order_subset unfolding base_case_vertices_def
      by (auto simp: Let_def dest: in_set_takeD)
  qed
  have "base_case_scan_cost \<Delta> k x B \<le>
      \<Delta> * card (base_case_vertices k x B)"
    unfolding base_case_scan_cost_def
    by (rule card_outgoing_edges_le[OF vertices_subset degree])
  also have "\<dots> \<le> \<Delta> * k"
    using card_base_case_vertices_le[of k x B] by simp
  finally show ?thesis .
qed

theorem base_case_scan_cost_le_outgoing_edges:
  "base_case_scan_cost \<Delta> k x B \<le>
    card (outgoing_edges (base_case_vertices k x B))"
  unfolding base_case_scan_cost_def
  by simp

theorem base_case_scan_cost_le_edge_count:
  "base_case_scan_cost edge_count k x B \<le> edge_count * k"
  by (rule base_case_scan_cost_le[OF edge_outdegree_le_edge_count])

definition concrete_capped_step_accounted_cost where
  "concrete_capped_step_accounted_cost k cap d S B child_costs edge_costs =
     fp_iter_capped_scan_cost k cap d S S B +
     sum_list child_costs + sum_list edge_costs"

theorem concrete_capped_step_core_cost_le_range:
  assumes S_subset: "S \<subseteq> V"
    and degree: "edge_outdegree_le \<Delta>"
    and S_cap: "card S \<le> cap"
    and trace: "concrete_partition_loop_trace
      (find_pivots_pivots_capped k cap d S B) B a bs d' B' Us U_loop"
    and child_costs: "list_all2 (\<lambda>c X. c \<le> C * card X) costs
      (range_tree_chain_list (find_pivots_pivots_capped k cap d S B) a bs B')"
  shows "concrete_capped_step_core_cost k cap d S B costs \<le>
    k * \<Delta> * cap +
      C * card (range_tree_chain
        (find_pivots_pivots_capped k cap d S B) a bs B')"
proof -
  let ?P = "find_pivots_pivots_capped k cap d S B"
  have mono: "nondecreasing_from a bs"
    using trace unfolding concrete_partition_loop_trace_def by blast
  have scan:
    "fp_iter_capped_scan_cost k cap d S S B \<le> k * \<Delta> * cap"
    using find_pivots_capped_scan_cost_le[OF S_subset degree S_cap] .
  have child:
    "sum_list costs \<le> C * card (range_tree_chain ?P a bs B')"
    using child_costs_le_range_tree_chain_card[OF mono child_costs] .
  show ?thesis
    unfolding concrete_capped_step_core_cost_def using scan child by linarith
qed

theorem concrete_capped_step_core_cost_le_level_chain:
  assumes S_subset: "S \<subseteq> V"
    and degree: "edge_outdegree_le \<Delta>"
    and S_cap: "card S \<le> cap"
    and trace: "concrete_partition_loop_trace
      (find_pivots_pivots_capped k cap d S B) B a bs d' B' Us U_loop"
    and child_costs: "list_all2 (\<lambda>c X. c \<le> level_range_cost_bound A R l X) costs
      (range_tree_chain_list (find_pivots_pivots_capped k cap d S B) a bs B')"
  shows "concrete_capped_step_core_cost k cap d S B costs \<le>
    k * \<Delta> * cap +
    A * l *
      card (range_tree_chain (find_pivots_pivots_capped k cap d S B) a bs B') +
    R * card (outgoing_edges
      (range_tree_chain (find_pivots_pivots_capped k cap d S B) a bs B'))"
proof -
  let ?P = "find_pivots_pivots_capped k cap d S B"
  have mono: "nondecreasing_from a bs"
    using trace unfolding concrete_partition_loop_trace_def by blast
  have scan:
    "fp_iter_capped_scan_cost k cap d S S B \<le> k * \<Delta> * cap"
    using find_pivots_capped_scan_cost_le[OF S_subset degree S_cap] .
  have child:
    "sum_list costs \<le>
      A * l * card (range_tree_chain ?P a bs B') +
      R * card (outgoing_edges (range_tree_chain ?P a bs B'))"
    using child_costs_le_level_range_chain_bound[OF mono child_costs] .
  show ?thesis
    unfolding concrete_capped_step_core_cost_def using scan child by linarith
qed

theorem concrete_capped_step_core_cost_closes_level_bound:
  assumes S_subset: "S \<subseteq> V"
    and degree: "edge_outdegree_le \<Delta>"
    and S_cap: "card S \<le> cap"
    and trace: "concrete_partition_loop_trace
      (find_pivots_pivots_capped k cap d S B) B a bs d' B' Us U_loop"
    and child_costs: "list_all2 (\<lambda>c X. c \<le> level_range_cost_bound A R l X) costs
      (range_tree_chain_list (find_pivots_pivots_capped k cap d S B) a bs B')"
    and scan_budget: "k * \<Delta> * cap \<le> A * card U_loop"
  shows "concrete_capped_step_core_cost k cap d S B costs \<le>
    level_range_cost_bound A R (Suc l) U_loop"
proof -
  let ?P = "find_pivots_pivots_capped k cap d S B"
  have children:
    "list_all2 (\<lambda>U X. U = X \<and> complete_on d' U) Us
      (range_tree_chain_list ?P a bs B')"
    using trace unfolding concrete_partition_loop_trace_def by blast
  have U_def: "U_loop = bound_tree ?P (Fin a) \<union> \<Union>(set Us)"
    using trace unfolding concrete_partition_loop_trace_def by blast
  have Union_eq:
    "\<Union>(set Us) = \<Union>(set (range_tree_chain_list ?P a bs B'))"
    using children by (induction rule: list_all2_induct) auto
  have U_eq_chain:
    "U_loop = bound_tree ?P (Fin a) \<union> range_tree_chain ?P a bs B'"
    using U_def Union_eq Union_range_tree_chain_list[of ?P a bs B'] by simp
  have finite_U: "finite U_loop"
    using U_eq_chain by simp
  have chain_subset: "range_tree_chain ?P a bs B' \<subseteq> U_loop"
    using U_eq_chain by blast
  have card_chain_le: "card (range_tree_chain ?P a bs B') \<le> card U_loop"
    by (rule card_mono[OF finite_U chain_subset])
  have outgoing_subset:
    "outgoing_edges (range_tree_chain ?P a bs B') \<subseteq> outgoing_edges U_loop"
    using outgoing_edges_mono[OF chain_subset] .
  have finite_out_U: "finite (outgoing_edges U_loop)"
    by simp
  have card_out_le:
    "card (outgoing_edges (range_tree_chain ?P a bs B')) \<le>
      card (outgoing_edges U_loop)"
    by (rule card_mono[OF finite_out_U outgoing_subset])
  have step:
    "concrete_capped_step_core_cost k cap d S B costs \<le>
      k * \<Delta> * cap +
      A * l * card (range_tree_chain ?P a bs B') +
      R * card (outgoing_edges (range_tree_chain ?P a bs B'))"
    by (rule concrete_capped_step_core_cost_le_level_chain
      [OF S_subset degree S_cap trace child_costs])
  also have "\<dots> \<le>
      A * card U_loop + A * l * card U_loop +
      R * card (outgoing_edges U_loop)"
    using scan_budget card_chain_le card_out_le
    by (intro add_mono mult_left_mono) simp_all
  also have "\<dots> = level_range_cost_bound A R (Suc l) U_loop"
    unfolding level_range_cost_bound_def by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma scan_budget_from_loop_card:
  assumes degree_factor: "\<Delta> \<le> A"
    and progress: "k * cap \<le> card U_loop"
  shows "k * \<Delta> * cap \<le> A * card U_loop"
proof -
  have "k * \<Delta> * cap \<le> k * A * cap"
    using degree_factor by (intro mult_left_mono mult_right_mono) simp_all
  also have "\<dots> = A * (k * cap)"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> A * card U_loop"
    using progress by simp
  finally show ?thesis .
qed

lemma scan_insert_budget_from_loop_card:
  assumes degree_factor: "\<Delta> \<le> A"
    and insert_factor: "t \<le> A * k"
    and progress: "k * cap \<le> card U_loop"
  shows "k * \<Delta> * cap + t * cap \<le> 2 * A * card U_loop"
proof -
  have scan: "k * \<Delta> * cap \<le> A * card U_loop"
    by (rule scan_budget_from_loop_card[OF degree_factor progress])
  have insert: "t * cap \<le> A * card U_loop"
  proof -
    have "t * cap \<le> (A * k) * cap"
      using insert_factor by simp
    also have "\<dots> = A * (k * cap)"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> A * card U_loop"
      using progress by simp
    finally show ?thesis .
  qed
  have "k * \<Delta> * cap + t * cap \<le> A * card U_loop + A * card U_loop"
    using scan insert by simp
  also have "\<dots> = 2 * A * card U_loop"
    by simp
  finally show ?thesis .
qed

lemma loop_overhead_budget_from_progress:
  assumes factor: "Suc t \<le> A"
    and progress: "M * q \<le> card U"
  shows "(Suc t) * M * q \<le> A * card U"
proof -
  have "(Suc t) * M * q \<le> A * (M * q)"
  proof -
    have "(Suc t) * (M * q) \<le> A * (M * q)"
      by (rule mult_right_mono[OF factor]) simp
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  also have "\<dots> \<le> A * card U"
    using progress by simp
  finally show ?thesis .
qed

theorem concrete_capped_step_core_cost_closes_level_bound_from_progress:
  assumes S_subset: "S \<subseteq> V"
    and degree: "edge_outdegree_le \<Delta>"
    and S_cap: "card S \<le> cap"
    and trace: "concrete_partition_loop_trace
      (find_pivots_pivots_capped k cap d S B) B a bs d' B' Us U_loop"
    and child_costs: "list_all2 (\<lambda>c X. c \<le> level_range_cost_bound A R l X) costs
      (range_tree_chain_list (find_pivots_pivots_capped k cap d S B) a bs B')"
    and degree_factor: "\<Delta> \<le> A"
    and progress: "k * cap \<le> card U_loop"
  shows "concrete_capped_step_core_cost k cap d S B costs \<le>
    level_range_cost_bound A R (Suc l) U_loop"
proof -
  have scan_budget: "k * \<Delta> * cap \<le> A * card U_loop"
    by (rule scan_budget_from_loop_card[OF degree_factor progress])
  show ?thesis
    by (rule concrete_capped_step_core_cost_closes_level_bound
      [OF S_subset degree S_cap trace child_costs scan_budget])
qed

theorem concrete_capped_step_core_cost_le_loop_vertices:
  assumes S_subset: "S \<subseteq> V"
    and degree: "edge_outdegree_le \<Delta>"
    and S_cap: "card S \<le> cap"
    and trace: "concrete_partition_loop_trace
      (find_pivots_pivots_capped k cap d S B) B a bs d' B' Us U_loop"
    and child_costs: "list_all2 (\<lambda>c X. c \<le> C * card X) costs
      (range_tree_chain_list (find_pivots_pivots_capped k cap d S B) a bs B')"
  shows "concrete_capped_step_core_cost k cap d S B costs \<le>
    k * \<Delta> * cap + C * card U_loop"
proof -
  let ?P = "find_pivots_pivots_capped k cap d S B"
  have children:
    "list_all2 (\<lambda>U X. U = X \<and> complete_on d' U) Us
      (range_tree_chain_list ?P a bs B')"
    using trace unfolding concrete_partition_loop_trace_def by blast
  have U_def: "U_loop = bound_tree ?P (Fin a) \<union> \<Union>(set Us)"
    using trace unfolding concrete_partition_loop_trace_def by blast
  have Union_eq:
    "\<Union>(set Us) = \<Union>(set (range_tree_chain_list ?P a bs B'))"
    using children by (induction rule: list_all2_induct) auto
  have U_eq_chain:
    "U_loop = bound_tree ?P (Fin a) \<union> range_tree_chain ?P a bs B'"
    using U_def Union_eq Union_range_tree_chain_list[of ?P a bs B'] by simp
  have finite_U: "finite U_loop"
    using U_eq_chain by simp
  have chain_subset: "range_tree_chain ?P a bs B' \<subseteq> U_loop"
    using U_eq_chain by blast
  have card_chain_le: "card (range_tree_chain ?P a bs B') \<le> card U_loop"
    by (rule card_mono[OF finite_U chain_subset])
  have "concrete_capped_step_core_cost k cap d S B costs \<le>
      k * \<Delta> * cap + C * card (range_tree_chain ?P a bs B')"
    by (rule concrete_capped_step_core_cost_le_range
      [OF S_subset degree S_cap trace child_costs])
  also have "\<dots> \<le> k * \<Delta> * cap + C * card U_loop"
    using card_chain_le by simp
  finally show ?thesis .
qed

theorem concrete_capped_step_accounted_cost_le:
  assumes S_subset: "S \<subseteq> V"
    and degree: "edge_outdegree_le \<Delta>"
    and S_cap: "card S \<le> cap"
    and trace: "concrete_partition_loop_trace
      (find_pivots_pivots_capped k cap d S B) B a bs d' B' Us U_loop"
    and child_costs: "list_all2 (\<lambda>c X. c \<le> C * card X) child_costs
      (range_tree_chain_list (find_pivots_pivots_capped k cap d S B) a bs B')"
    and edge_costs: "list_all2 (\<lambda>c X. c \<le> R * card (outgoing_edges X)) edge_costs
      (range_tree_chain_list (find_pivots_pivots_capped k cap d S B) a bs B')"
  shows "concrete_capped_step_accounted_cost k cap d S B child_costs edge_costs \<le>
    k * \<Delta> * cap + C * card U_loop +
    R * card (outgoing_edges
      (range_tree_chain (find_pivots_pivots_capped k cap d S B) a bs B'))"
proof -
  let ?P = "find_pivots_pivots_capped k cap d S B"
  have mono: "nondecreasing_from a bs"
    using trace unfolding concrete_partition_loop_trace_def by blast
  have core:
    "concrete_capped_step_core_cost k cap d S B child_costs \<le>
      k * \<Delta> * cap + C * card U_loop"
    by (rule concrete_capped_step_core_cost_le_loop_vertices
      [OF S_subset degree S_cap trace child_costs])
  have core_unfolded:
    "fp_iter_capped_scan_cost k cap d S S B + sum_list child_costs \<le>
      k * \<Delta> * cap + C * card U_loop"
    using core unfolding concrete_capped_step_core_cost_def .
  have edges:
    "sum_list edge_costs \<le> R * card (outgoing_edges (range_tree_chain ?P a bs B'))"
    using edge_costs_le_range_tree_chain_outgoing[OF mono edge_costs] .
  show ?thesis
    unfolding concrete_capped_step_accounted_cost_def
    using core_unfolded edges by linarith
qed

theorem full_operational_partition_loop_state_trace_and_degree_cost:
  assumes run:
    "full_operational_partition_loop_state M t k cap l d P B d' D a betas bs B' Us U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and degree: "edge_outdegree_le \<Delta>"
  obtains child_costs child_sets where
    "concrete_partition_loop_trace P B a bs d' B' Us U"
    "length child_costs = length child_sets"
    "\<And>X. X \<in> set child_sets \<Longrightarrow> X \<subseteq> V"
    "c \<le> sum_list child_costs + M * length child_costs +
      t * (\<Delta> * sum_list (map card child_sets) + M * length child_costs)"
proof -
  obtain child_costs child_sets where trace:
      "concrete_partition_loop_trace P B a bs d' B' Us U"
    and len: "length child_costs = length child_sets"
    and sets: "\<And>X. X \<in> set child_sets \<Longrightarrow> X \<subseteq> V"
    and cost:
      "c \<le> sum_list child_costs + M * length child_costs +
        t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
          M * length child_costs)"
    using full_operational_partition_loop_state_trace_and_complete_edge_cost
      [OF run sound pre P_reaches] by blast
  have edge_sum:
    "sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) \<le>
      \<Delta> * sum_list (map card child_sets)"
    by (rule sum_card_outgoing_edges_le_degree[OF degree sets])
  have cost_degree:
    "c \<le> sum_list child_costs + M * length child_costs +
      t * (\<Delta> * sum_list (map card child_sets) + M * length child_costs)"
  proof -
    have "sum_list child_costs + M * length child_costs +
        t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
          M * length child_costs) \<le>
        sum_list child_costs + M * length child_costs +
        t * (\<Delta> * sum_list (map card child_sets) + M * length child_costs)"
      using edge_sum by simp
    then show ?thesis
      using cost by linarith
  qed
  show thesis
    using that trace len sets cost_degree by blast
qed

definition partition_initial_insert_cost_bound where
  "partition_initial_insert_cost_bound c t P \<longleftrightarrow> c \<le> t * card P"

lemma partition_initial_insert_cost_boundD:
  assumes "partition_initial_insert_cost_bound c t P"
  shows "c \<le> t * card P"
  using assms unfolding partition_initial_insert_cost_bound_def .

lemma partition_initial_insert_cost_bound_le:
  assumes cost: "partition_initial_insert_cost_bound c t P"
    and card_le: "card P \<le> N"
  shows "c \<le> t * N"
proof -
  have "c \<le> t * card P"
    using cost by (rule partition_initial_insert_cost_boundD)
  also have "\<dots> \<le> t * N"
    using card_le by simp
  finally show ?thesis .
qed

lemma find_pivots_pivots_capped_subset:
  "find_pivots_pivots_capped k cap d S B \<subseteq> S"
  unfolding find_pivots_pivots_capped_def by auto

lemma find_pivots_pivots_capped_card_le:
  assumes S_subset: "S \<subseteq> V"
  shows "card (find_pivots_pivots_capped k cap d S B) \<le> card S"
proof -
  have finite_S: "finite S"
    using finite_subset[OF S_subset finite_V] .
  show ?thesis
    by (rule card_mono[OF finite_S find_pivots_pivots_capped_subset])
qed

lemma find_pivots_pivots_capped_scaled_card_le:
  assumes S_subset: "S \<subseteq> V"
    and S_k_cap: "k * card S \<le> cap"
  shows "k * card (find_pivots_pivots_capped k cap d S B) \<le> cap"
proof -
  have "card (find_pivots_pivots_capped k cap d S B) \<le> card S"
    by (rule find_pivots_pivots_capped_card_le[OF S_subset])
  then have "k * card (find_pivots_pivots_capped k cap d S B) \<le>
      k * card S"
    by simp
  then show ?thesis
    using S_k_cap by linarith
qed

lemma find_pivots_pivots_capped_tree_antichain:
  assumes anti: "tree_antichain S"
  shows "tree_antichain (find_pivots_pivots_capped k cap d S B)"
  by (rule tree_antichain_subset[OF anti find_pivots_pivots_capped_subset])

lemma partition_initial_insert_cost_bound_capped_pivots_le:
  assumes cost: "partition_initial_insert_cost_bound c t
      (find_pivots_pivots_capped k cap d S B)"
    and S_subset: "S \<subseteq> V"
    and S_cap: "card S \<le> cap"
  shows "c \<le> t * cap"
proof -
  have pivots_S:
    "card (find_pivots_pivots_capped k cap d S B) \<le> card S"
    by (rule find_pivots_pivots_capped_card_le[OF S_subset])
  have pivots_le: "card (find_pivots_pivots_capped k cap d S B) \<le> cap"
    by (rule order_trans[OF pivots_S S_cap])
  show ?thesis
    by (rule partition_initial_insert_cost_bound_le[OF cost pivots_le])
qed

lemma find_pivots_scan_and_initial_insert_cost_le:
  assumes S_subset: "S \<subseteq> V"
    and degree: "edge_outdegree_le \<Delta>"
    and S_cap: "card S \<le> cap"
    and insert: "partition_initial_insert_cost_bound c_insert t
      (find_pivots_pivots_capped k cap d S B)"
  shows "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
    k * \<Delta> * cap + t * cap"
proof -
  have scan: "fp_iter_capped_scan_cost k cap d S S B \<le> k * \<Delta> * cap"
    by (rule find_pivots_capped_scan_cost_le[OF S_subset degree S_cap])
  have insert_le: "c_insert \<le> t * cap"
    by (rule partition_initial_insert_cost_bound_capped_pivots_le
      [OF insert S_subset S_cap])
  show ?thesis
    using scan insert_le by simp
qed

lemma find_pivots_scan_and_initial_insert_cost_le_edge_count:
  assumes S_subset: "S \<subseteq> V"
    and S_cap: "card S \<le> cap"
    and insert: "partition_initial_insert_cost_bound c_insert t
      (find_pivots_pivots_capped k cap d S B)"
  shows "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
    k * edge_count * cap + t * cap"
  by (rule find_pivots_scan_and_initial_insert_cost_le
    [OF S_subset edge_outdegree_le_edge_count S_cap insert])

lemma find_pivots_scan_and_initial_insert_budget_from_progress:
  assumes S_subset: "S \<subseteq> V"
    and degree: "edge_outdegree_le \<Delta>"
    and S_cap: "card S \<le> cap"
    and insert: "partition_initial_insert_cost_bound c_insert t
      (find_pivots_pivots_capped k cap d S B)"
    and degree_factor: "\<Delta> \<le> A"
    and insert_factor: "t \<le> A * k"
    and progress: "k * cap \<le> card U"
  shows "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
    2 * A * card U"
proof -
  have local:
    "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
      k * \<Delta> * cap + t * cap"
    by (rule find_pivots_scan_and_initial_insert_cost_le
      [OF S_subset degree S_cap insert])
  have budget: "k * \<Delta> * cap + t * cap \<le> 2 * A * card U"
    by (rule scan_insert_budget_from_loop_card
      [OF degree_factor insert_factor progress])
  show ?thesis
    using local budget by linarith
qed

lemma find_pivots_pivots_capped_card_le_seen_if_no_overflow:
  assumes S_subset: "S \<subseteq> V"
    and anti: "tree_antichain S"
    and k_pos: "0 < k"
    and no_overflow:
      "\<not> card (find_pivots_seen_capped k cap d S B) > cap"
  shows "card (find_pivots_pivots_capped k cap d S B) \<le>
    card (find_pivots_seen_capped k cap d S B)"
proof -
  let ?P = "find_pivots_pivots_capped k cap d S B"
  let ?W = "find_pivots_seen_capped k cap d S B"
  have cases:
      "k * card ?P \<le> card ?W \<or> (?P = S \<and> card ?W > cap)"
    by (rule find_pivots_pivots_capped_card_times_le_seen_or_overflow
      [OF S_subset anti])
  then have mult_le: "k * card ?P \<le> card ?W"
    using no_overflow by blast
  have "card ?P \<le> k * card ?P"
    using k_pos by (cases k) simp_all
  then show ?thesis
    using mult_le by linarith
qed

lemma partition_initial_insert_cost_bound_capped_pivots_le_seen_scaled_from_mult:
  assumes insert: "partition_initial_insert_cost_bound c t P"
    and pivot_mult: "k * card P \<le> card W"
    and insert_factor: "t \<le> A * k"
  shows "c \<le> A * card W"
proof -
  have "c \<le> t * card P"
    by (rule partition_initial_insert_cost_boundD[OF insert])
  also have "\<dots> \<le> (A * k) * card P"
    using insert_factor by simp
  also have "\<dots> = A * (k * card P)"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> A * card W"
    using pivot_mult by simp
  finally show ?thesis .
qed

lemma find_pivots_pivots_capped_card_times_le_seen:
  assumes S_subset: "S \<subseteq> V"
    and anti: "tree_antichain S"
    and S_k_cap: "k * card S \<le> cap"
  shows "k * card (find_pivots_pivots_capped k cap d S B) \<le>
    card (find_pivots_seen_capped k cap d S B)"
proof -
  let ?P = "find_pivots_pivots_capped k cap d S B"
  let ?W = "find_pivots_seen_capped k cap d S B"
  have cases: "k * card ?P \<le> card ?W \<or> (?P = S \<and> card ?W > cap)"
    by (rule find_pivots_pivots_capped_card_times_le_seen_or_overflow
      [OF S_subset anti])
  then show ?thesis
  proof
    assume "k * card ?P \<le> card ?W"
    then show ?thesis .
  next
    assume overflow: "?P = S \<and> card ?W > cap"
    then have "k * card ?P \<le> cap"
      using S_k_cap by simp
    also have "\<dots> \<le> card ?W"
      using overflow by simp
    finally show ?thesis .
  qed
qed

lemma partition_initial_insert_cost_bound_capped_pivots_le_seen_scaled:
  assumes insert: "partition_initial_insert_cost_bound c t
      (find_pivots_pivots_capped k cap d S B)"
    and S_subset: "S \<subseteq> V"
    and anti: "tree_antichain S"
    and S_k_cap: "k * card S \<le> cap"
    and insert_factor: "t \<le> A * k"
  shows "c \<le> A * card (find_pivots_seen_capped k cap d S B)"
proof -
  have pivot_mult:
    "k * card (find_pivots_pivots_capped k cap d S B) \<le>
      card (find_pivots_seen_capped k cap d S B)"
    by (rule find_pivots_pivots_capped_card_times_le_seen
      [OF S_subset anti S_k_cap])
  show ?thesis
    by (rule partition_initial_insert_cost_bound_capped_pivots_le_seen_scaled_from_mult
      [OF insert pivot_mult insert_factor])
qed

lemma partition_initial_insert_cost_bound_capped_pivots_le_seen_if_no_overflow:
  assumes insert: "partition_initial_insert_cost_bound c t
      (find_pivots_pivots_capped k cap d S B)"
    and S_subset: "S \<subseteq> V"
    and anti: "tree_antichain S"
    and k_pos: "0 < k"
    and no_overflow:
      "\<not> card (find_pivots_seen_capped k cap d S B) > cap"
  shows "c \<le> t * card (find_pivots_seen_capped k cap d S B)"
proof -
  have pivots_le:
    "card (find_pivots_pivots_capped k cap d S B) \<le>
      card (find_pivots_seen_capped k cap d S B)"
    by (rule find_pivots_pivots_capped_card_le_seen_if_no_overflow
      [OF S_subset anti k_pos no_overflow])
  show ?thesis
    by (rule partition_initial_insert_cost_bound_le[OF insert pivots_le])
qed

lemma partition_initial_insert_cost_bound_capped_pivots_le_seen:
  assumes insert: "partition_initial_insert_cost_bound c t
      (find_pivots_pivots_capped k cap d S B)"
    and S_subset: "S \<subseteq> V"
    and S_cap: "card S \<le> cap"
    and anti: "tree_antichain S"
    and k_pos: "0 < k"
  shows "c \<le> t * card (find_pivots_seen_capped k cap d S B)"
proof (cases "card (find_pivots_seen_capped k cap d S B) > cap")
  case True
  have c_le_cap: "c \<le> t * cap"
    by (rule partition_initial_insert_cost_bound_capped_pivots_le
      [OF insert S_subset S_cap])
  have "t * cap \<le> t * card (find_pivots_seen_capped k cap d S B)"
    using True by simp
  then show ?thesis
    using c_le_cap by linarith
next
  case False
  show ?thesis
    by (rule partition_initial_insert_cost_bound_capped_pivots_le_seen_if_no_overflow
      [OF insert S_subset anti k_pos False])
qed

lemma find_pivots_scan_and_initial_insert_cost_le_seen_if_no_overflow:
  assumes S_subset: "S \<subseteq> V"
    and degree: "edge_outdegree_le \<Delta>"
    and anti: "tree_antichain S"
    and k_pos: "0 < k"
    and no_overflow:
      "\<not> card (find_pivots_seen_capped k cap d S B) > cap"
    and insert: "partition_initial_insert_cost_bound c_insert t
      (find_pivots_pivots_capped k cap d S B)"
  shows "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
    (k * \<Delta> + t) * card (find_pivots_seen_capped k cap d S B)"
proof -
  let ?W = "find_pivots_seen_capped k cap d S B"
  have scan: "fp_iter_capped_scan_cost k cap d S S B \<le>
      k * \<Delta> * card ?W"
    by (rule find_pivots_capped_scan_cost_le_seen[OF S_subset degree])
  have insert_le: "c_insert \<le> t * card ?W"
    by (rule partition_initial_insert_cost_bound_capped_pivots_le_seen_if_no_overflow
      [OF insert S_subset anti k_pos no_overflow])
  have "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
      k * \<Delta> * card ?W + t * card ?W"
    using scan insert_le by simp
  also have "\<dots> = (k * \<Delta> + t) * card ?W"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma find_pivots_scan_and_initial_insert_cost_le_seen:
  assumes S_subset: "S \<subseteq> V"
    and degree: "edge_outdegree_le \<Delta>"
    and S_cap: "card S \<le> cap"
    and anti: "tree_antichain S"
    and k_pos: "0 < k"
    and insert: "partition_initial_insert_cost_bound c_insert t
      (find_pivots_pivots_capped k cap d S B)"
  shows "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
    (k * \<Delta> + t) * card (find_pivots_seen_capped k cap d S B)"
proof -
  let ?W = "find_pivots_seen_capped k cap d S B"
  have scan: "fp_iter_capped_scan_cost k cap d S S B \<le>
      k * \<Delta> * card ?W"
    by (rule find_pivots_capped_scan_cost_le_seen[OF S_subset degree])
  have insert_le: "c_insert \<le> t * card ?W"
    by (rule partition_initial_insert_cost_bound_capped_pivots_le_seen
      [OF insert S_subset S_cap anti k_pos])
  have "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
      k * \<Delta> * card ?W + t * card ?W"
    using scan insert_le by simp
  also have "\<dots> = (k * \<Delta> + t) * card ?W"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma find_pivots_scan_and_initial_insert_cost_le_seen_scaled:
  assumes S_subset: "S \<subseteq> V"
    and degree: "edge_outdegree_le \<Delta>"
    and anti: "tree_antichain S"
    and S_k_cap: "k * card S \<le> cap"
    and insert: "partition_initial_insert_cost_bound c_insert t
      (find_pivots_pivots_capped k cap d S B)"
    and insert_factor: "t \<le> A_insert * k"
  shows "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
    (k * \<Delta> + A_insert) * card (find_pivots_seen_capped k cap d S B)"
proof -
  let ?W = "find_pivots_seen_capped k cap d S B"
  have scan: "fp_iter_capped_scan_cost k cap d S S B \<le>
      k * \<Delta> * card ?W"
    by (rule find_pivots_capped_scan_cost_le_seen[OF S_subset degree])
  have insert_le: "c_insert \<le> A_insert * card ?W"
    by (rule partition_initial_insert_cost_bound_capped_pivots_le_seen_scaled
      [OF insert S_subset anti S_k_cap insert_factor])
  have "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
      k * \<Delta> * card ?W + A_insert * card ?W"
    using scan insert_le by simp
  also have "\<dots> = (k * \<Delta> + A_insert) * card ?W"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma find_pivots_scan_and_initial_insert_budget_from_seen_scaled:
  assumes S_subset: "S \<subseteq> V"
    and degree: "edge_outdegree_le \<Delta>"
    and anti: "tree_antichain S"
    and S_k_cap: "k * card S \<le> cap"
    and insert: "partition_initial_insert_cost_bound c_insert t
      (find_pivots_pivots_capped k cap d S B)"
    and insert_factor: "t \<le> A_insert * k"
    and factor: "k * \<Delta> + A_insert \<le> A"
    and seen_progress:
      "card (find_pivots_seen_capped k cap d S B) \<le> card U"
  shows "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
    A * card U"
proof -
  let ?W = "find_pivots_seen_capped k cap d S B"
  have local:
    "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
      (k * \<Delta> + A_insert) * card ?W"
    by (rule find_pivots_scan_and_initial_insert_cost_le_seen_scaled
      [OF S_subset degree anti S_k_cap insert insert_factor])
  have "(k * \<Delta> + A_insert) * card ?W \<le> A * card U"
    by (rule mult_mono[OF factor seen_progress]) simp_all
  then show ?thesis
    using local by linarith
qed

lemma find_pivots_scan_and_initial_insert_budget_from_seen:
  assumes S_subset: "S \<subseteq> V"
    and degree: "edge_outdegree_le \<Delta>"
    and anti: "tree_antichain S"
    and k_pos: "0 < k"
    and no_overflow:
      "\<not> card (find_pivots_seen_capped k cap d S B) > cap"
    and insert: "partition_initial_insert_cost_bound c_insert t
      (find_pivots_pivots_capped k cap d S B)"
    and factor: "k * \<Delta> + t \<le> A"
    and seen_progress:
      "card (find_pivots_seen_capped k cap d S B) \<le> card U"
  shows "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
    A * card U"
proof -
  let ?W = "find_pivots_seen_capped k cap d S B"
  have local:
    "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
      (k * \<Delta> + t) * card ?W"
    by (rule find_pivots_scan_and_initial_insert_cost_le_seen_if_no_overflow
      [OF S_subset degree anti k_pos no_overflow insert])
  have "(k * \<Delta> + t) * card ?W \<le> A * card U"
    by (rule mult_mono[OF factor seen_progress]) simp_all
  then show ?thesis
    using local by linarith
qed

lemma find_pivots_scan_and_initial_insert_budget_from_seen_total:
  assumes S_subset: "S \<subseteq> V"
    and degree: "edge_outdegree_le \<Delta>"
    and S_cap: "card S \<le> cap"
    and anti: "tree_antichain S"
    and k_pos: "0 < k"
    and insert: "partition_initial_insert_cost_bound c_insert t
      (find_pivots_pivots_capped k cap d S B)"
    and factor: "k * \<Delta> + t \<le> A"
    and seen_progress:
      "card (find_pivots_seen_capped k cap d S B) \<le> card U"
  shows "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
    A * card U"
proof -
  let ?W = "find_pivots_seen_capped k cap d S B"
  have local:
    "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
      (k * \<Delta> + t) * card ?W"
    by (rule find_pivots_scan_and_initial_insert_cost_le_seen
      [OF S_subset degree S_cap anti k_pos insert])
  have "(k * \<Delta> + t) * card ?W \<le> A * card U"
    by (rule mult_mono[OF factor seen_progress]) simp_all
  then show ?thesis
    using local by linarith
qed

text \<open>
  The relation below is the first costed operational run in this file.  It
  refines the full operational relation by adding a natural-number cost to each
  BMSSP call and each partition loop.  The constructors charge base-case scans,
  FindPivots scans and initial inserts, pulls, batch prepends, recursive child
  calls, and the remaining tail of the loop.

  This relation is intentionally generic in the partition-cost predicates.  It
  does not know whether a sorted list, bucketed partition, or another data
  structure implements the primitive operations.  Its job is to expose the exact
  cost skeleton that the later refinement layers and the final headline theorem
  instantiate.
\<close>

inductive costed_full_operational_partition_loop_state
  and costed_full_operational_bmssp where
  Cost_State_Done:
    "keys_of D = {} \<Longrightarrow>
     bound_le (Fin a) B \<Longrightarrow>
     complete_on d' (bound_tree P (Fin a)) \<Longrightarrow>
     costed_full_operational_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
       [] [] (Fin a) [range_tree P a (Fin a)]
       (bound_tree P (Fin a) \<union> \<Union>(set [range_tree P a (Fin a)])) 0"
| Cost_State_Step:
    "pull_separates D (M_of l) Bmax S_pull beta D_pull \<Longrightarrow>
     bound_le (Fin beta) B \<Longrightarrow>
     bmssp_pre_full d (split_below d P beta) (Fin beta) \<Longrightarrow>
     S_pull = split_below d P beta \<Longrightarrow>
     a \<le> b \<Longrightarrow>
     complete_on d' (bound_tree P (Fin a)) \<Longrightarrow>
     costed_full_operational_bmssp \<Delta> M_of t k cap l d S_pull (Fin beta)
       d_child (Fin b) U_child c_child \<Longrightarrow>
     complete_preserved d_child d' U_child \<Longrightarrow>
     batch =
       edge_relaxation_pairs_between d_child U_child b beta @
       label_pairs_between d S_pull b beta \<Longrightarrow>
     D_next = batch_min_update D_pull batch \<Longrightarrow>
     partition_pull_cost_bound c_pull S_pull \<Longrightarrow>
     partition_batch_cost_bound c_batch t batch \<Longrightarrow>
     costed_full_operational_partition_loop_state \<Delta> M_of t k cap l d P B d'
       D_next b betas bs B' Us_tail U_tail c_tail \<Longrightarrow>
     c = c_pull + c_batch + c_child + c_tail \<Longrightarrow>
     costed_full_operational_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
       (beta # betas) (b # bs) B'
       (range_tree P a (Fin b) # Us_tail)
       (bound_tree P (Fin a) \<union>
        \<Union>(set (range_tree P a (Fin b) # Us_tail))) c"
| Cost_Base:
    "S = {x} \<Longrightarrow>
     costed_full_operational_bmssp \<Delta> M_of t k cap 0 d S B
       (\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v)
       (base_case_bound k x B)
       (base_case_vertices k x B)
       (base_case_scan_cost \<Delta> k x B)"
| Cost_Step:
    "D = label_partition_view
       (find_pivots_label_capped k cap d S B)
       (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
     partition_initial_insert_cost_bound c_insert t
       (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
     costed_full_operational_partition_loop_state \<Delta> M_of t k cap l
       (find_pivots_label_capped k cap d S B)
       (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
       Us U_loop c_loop \<Longrightarrow>
     complete_on d'
       {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
     U = U_loop \<union>
       {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
     c = fp_iter_capped_scan_cost k cap d S S B + c_insert + c_loop \<Longrightarrow>
     costed_full_operational_bmssp \<Delta> M_of t k cap (Suc l) d S B d' B' U c"

theorem costed_full_operational_partition_loop_state_refines:
  "costed_full_operational_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
     betas bs B' Us U c \<Longrightarrow>
   full_operational_partition_loop_state (M_of l) t k cap l d P B d' D a
     betas bs B' Us U c"
and costed_full_operational_bmssp_refines:
  "costed_full_operational_bmssp \<Delta> M_of t k cap l d S B d' B' U c \<Longrightarrow>
   full_operational_bmssp k cap l d S B d' B' U"
proof (induction rule:
    costed_full_operational_partition_loop_state_costed_full_operational_bmssp.inducts)
  case (Cost_State_Done D a B d' P \<Delta> M_of t k cap l d)
  show ?case
    by (rule full_operational_partition_loop_state.State_Done
      [OF Cost_State_Done(1) Cost_State_Done(2) Cost_State_Done(3)])
next
  case (Cost_State_Step D M_of l Bmax S_pull beta D_pull B d P a b d'
      \<Delta> t k cap d_child U_child c_child batch D_next c_pull c_batch
      betas bs B' Us_tail U_tail c_tail c)
  have child_run:
    "full_operational_bmssp k cap l d S_pull (Fin beta)
      d_child (Fin b) U_child"
    using Cost_State_Step by blast
  have tail_run:
    "full_operational_partition_loop_state (M_of l) t k cap l d P B d'
      D_next b betas bs B' Us_tail U_tail c_tail"
    using Cost_State_Step by blast
  show ?case
  proof (rule full_operational_partition_loop_state.State_Step)
    show "pull_separates D (M_of l) Bmax S_pull beta D_pull"
      using Cost_State_Step by blast
    show "bound_le (Fin beta) B"
      using Cost_State_Step by blast
    show "bmssp_pre_full d (split_below d P beta) (Fin beta)"
      using Cost_State_Step by blast
    show "S_pull = split_below d P beta"
      using Cost_State_Step by blast
    show "a \<le> b"
      using Cost_State_Step by blast
    show "complete_on d' (bound_tree P (Fin a))"
      using Cost_State_Step by blast
    show "full_operational_bmssp k cap l d S_pull (Fin beta)
        d_child (Fin b) U_child"
      using child_run .
    show "complete_preserved d_child d' U_child"
      using Cost_State_Step by blast
    show "batch =
        edge_relaxation_pairs_between d_child U_child b beta @
        label_pairs_between d S_pull b beta"
      using Cost_State_Step by blast
    show "D_next = batch_min_update D_pull batch"
      using Cost_State_Step by blast
    show "partition_pull_cost_bound c_pull S_pull"
      using Cost_State_Step by blast
    show "partition_batch_cost_bound c_batch t batch"
      using Cost_State_Step by blast
    show "full_operational_partition_loop_state (M_of l) t k cap l d P B d'
        D_next b betas bs B' Us_tail U_tail c_tail"
      using tail_run .
    show "c = c_pull + c_batch + c_child + c_tail"
      using Cost_State_Step by blast
  qed
next
  case (Cost_Base S x \<Delta> M_of t k cap d B)
  show ?case
    by (rule Full_Base[OF Cost_Base.hyps])
next
  case (Cost_Step D k cap d S B c_insert t \<Delta> M_of l d' a betas bs B'
      Us U_loop c_loop U c)
  have state:
    "full_operational_partition_loop_state (M_of l) t k cap l
       (find_pivots_label_capped k cap d S B)
       (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
       Us U_loop c_loop"
    using Cost_Step by blast
  have loop:
    "full_operational_partition_loop k cap l
       (find_pivots_label_capped k cap d S B)
       (find_pivots_pivots_capped k cap d S B) B d' a betas bs B'
       Us U_loop"
    by (rule full_operational_partition_loop_state_refines[OF state])
  show ?case
  proof (rule Full_Step)
    show "full_operational_partition_loop k cap l
        (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B) B d' a betas bs B'
        Us U_loop"
      using loop .
    show "complete_on d'
        {v \<in> bound_tree S B'.
         find_pivots_label_capped k cap d S B v = dist s v}"
      using Cost_Step by blast
    show "U = U_loop \<union>
        {v \<in> bound_tree S B'.
         find_pivots_label_capped k cap d S B v = dist s v}"
      using Cost_Step by blast
  qed
qed

theorem costed_full_operational_bmssp_correct:
  assumes run:
    "costed_full_operational_bmssp \<Delta> M_of t k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "bmssp_post_full d S B d' B' U"
proof -
  have run': "full_operational_bmssp k cap l d S B d' B' U"
    by (rule costed_full_operational_bmssp_refines[OF run])
  show ?thesis
    by (rule full_operational_bmssp_correct[OF run' sound pre S_reaches])
qed

lemma costed_full_operational_partition_loop_state_lengths:
  assumes run:
    "costed_full_operational_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U c"
  shows "length betas = length bs"
    and "length Us = Suc (length bs)"
proof -
  have state:
    "full_operational_partition_loop_state (M_of l) t k cap l d P B d' D a
      betas bs B' Us U c"
    by (rule costed_full_operational_partition_loop_state_refines[OF run])
  show "length betas = length bs"
    by (rule full_operational_partition_loop_state_lengths(1)[OF state])
  show "length Us = Suc (length bs)"
    by (rule full_operational_partition_loop_state_lengths(2)[OF state])
qed

theorem finite_initial_label_costed_full_operational_top_level_correct:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and run:
      "costed_full_operational_bmssp \<Delta> M_of t k cap l finite_initial_label {s}
        Infinity d' Infinity U c"
  shows "sssp_correct d'"
proof -
  have run': "full_operational_bmssp k cap l finite_initial_label {s}
      Infinity d' Infinity U"
    by (rule costed_full_operational_bmssp_refines[OF run])
  show ?thesis
    by (rule finite_initial_label_full_operational_top_level_correct
      [OF all_reachable run'])
qed

theorem costed_full_operational_partition_loop_state_trace_and_degree_cost:
  assumes run:
    "costed_full_operational_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and degree: "edge_outdegree_le \<Delta>"
  obtains child_costs child_sets where
    "concrete_partition_loop_trace P B a bs d' B' Us U"
    "length child_costs = length child_sets"
    "\<And>X. X \<in> set child_sets \<Longrightarrow> X \<subseteq> V"
    "c \<le> sum_list child_costs + (M_of l) * length child_costs +
      t * (\<Delta> * sum_list (map card child_sets) + (M_of l) * length child_costs)"
proof -
  have state:
    "full_operational_partition_loop_state (M_of l) t k cap l d P B d' D a
      betas bs B' Us U c"
    by (rule costed_full_operational_partition_loop_state_refines[OF run])
  show thesis
    by (rule full_operational_partition_loop_state_trace_and_degree_cost
      [OF state sound pre P_reaches degree that])
qed

theorem costed_full_operational_partition_loop_state_child_call_data:
  "costed_full_operational_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U c \<Longrightarrow>
   sound_label d \<Longrightarrow>
   bmssp_pre_full d P B \<Longrightarrow>
   (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
   \<exists>child_costs child_sets.
      length child_costs = length child_sets \<and>
      length child_costs = length bs \<and>
      list_all2
        (\<lambda>c_child U_child. \<exists>S_child B_child d_child B_child'.
          costed_full_operational_bmssp \<Delta> M_of t k cap l d S_child B_child
            d_child B_child' U_child c_child \<and>
          bmssp_pre_full d S_child B_child \<and>
          (\<forall>x\<in>S_child. reachable s x) \<and>
          card S_child \<le> M_of l)
        child_costs child_sets \<and>
      (\<forall>X\<in>set child_sets. X \<subseteq> V) \<and>
      c \<le> sum_list child_costs + (M_of l) * length child_costs +
        t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
          (M_of l) * length child_costs)"
and costed_full_operational_bmssp_child_call_data_trivial:
  "costed_full_operational_bmssp \<Delta> M_of t k cap l d S B d' B' U c \<Longrightarrow> True"
proof (induction rule:
    costed_full_operational_partition_loop_state_costed_full_operational_bmssp.inducts)
  case (Cost_State_Done D a B d' P \<Delta> M_of t k cap l d)
  show ?case
    by (intro exI[of _ "[]"] exI[of _ "[]"]) simp
next
  case (Cost_State_Step D M_of l Bmax S_pull beta D_pull B d P a b d'
      \<Delta> t k cap d_child U_child c_child batch D_next c_pull c_batch
      betas bs B' Us_tail U_tail c_tail c)
  obtain child_costs child_sets where len_tail:
      "length child_costs = length child_sets"
    and child_len_tail: "length child_costs = length bs"
    and calls_tail:
      "list_all2
        (\<lambda>c_child U_child. \<exists>S_child B_child d_child B_child'.
          costed_full_operational_bmssp \<Delta> M_of t k cap l d S_child B_child
            d_child B_child' U_child c_child \<and>
          bmssp_pre_full d S_child B_child \<and>
          (\<forall>x\<in>S_child. reachable s x) \<and>
          card S_child \<le> M_of l)
        child_costs child_sets"
    and sets_tail: "\<forall>X\<in>set child_sets. X \<subseteq> V"
    and tail:
      "c_tail \<le> sum_list child_costs + M_of l * length child_costs +
        t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
          M_of l * length child_costs)"
    using Cost_State_Step.IH(8)
      [OF Cost_State_Step.prems(1) Cost_State_Step.prems(2) Cost_State_Step.prems(3)]
    by blast
  have child_reaches:
    "\<And>x. x \<in> S_pull \<Longrightarrow> reachable s x"
    using Cost_State_Step
    unfolding split_below_def by blast
  have child_pre: "bmssp_pre_full d S_pull (Fin beta)"
    using Cost_State_Step by blast
  have child_run:
    "costed_full_operational_bmssp \<Delta> M_of t k cap l d S_pull (Fin beta)
      d_child (Fin b) U_child c_child"
    using Cost_State_Step by blast
  have child_post:
    "bmssp_post_full d S_pull (Fin beta) d_child (Fin b) U_child"
    by (rule costed_full_operational_bmssp_correct
      [OF child_run Cost_State_Step.prems(1) child_pre child_reaches])
  have child_set: "U_child \<subseteq> V"
    using child_post unfolding bmssp_post_full_def bound_tree_def by blast
  have P_subset: "P \<subseteq> V"
    using Cost_State_Step unfolding bmssp_pre_full_def by blast
  have finite_P: "finite P"
    using finite_subset[OF P_subset finite_V] .
  have S_pull_subset: "S_pull \<subseteq> P"
    using Cost_State_Step unfolding split_below_def by blast
  have finite_S_pull: "finite S_pull"
    using finite_subset[OF S_pull_subset finite_P] .
  have card_pull: "card S_pull \<le> M_of l"
    using Cost_State_Step unfolding pull_separates_def by blast
  have pull_cost: "c_pull \<le> M_of l"
    using Cost_State_Step card_pull
    unfolding partition_pull_cost_bound_def by linarith
  have edge_len:
    "length (edge_relaxation_pairs_between d_child U_child b beta) \<le>
      card (outgoing_edges U_child)"
    by (rule edge_relaxation_pairs_between_length_le_outgoing)
  have label_len:
    "length (label_pairs_between d S_pull b beta) \<le> card S_pull"
    by (rule label_pairs_between_length_le_card[OF finite_S_pull])
  have batch_len:
    "length batch \<le> card (outgoing_edges U_child) + M_of l"
    using Cost_State_Step edge_len label_len card_pull by simp
  have batch_cost:
    "c_batch \<le> t * (card (outgoing_edges U_child) + M_of l)"
  proof -
    have "c_batch \<le> t * length batch"
      using Cost_State_Step
      unfolding partition_batch_cost_bound_def by simp
    also have "\<dots> \<le> t * (card (outgoing_edges U_child) + M_of l)"
      using batch_len by simp
    finally show ?thesis .
  qed
  let ?child_costs = "c_child # child_costs"
  let ?child_sets = "U_child # child_sets"
  have len: "length ?child_costs = length ?child_sets"
    using len_tail by simp
  have child_len: "length ?child_costs = length (b # bs)"
    using child_len_tail by simp
  have call_head:
    "\<exists>S_child B_child d_child' B_child'.
      costed_full_operational_bmssp \<Delta> M_of t k cap l d S_child B_child
        d_child' B_child' U_child c_child \<and>
      bmssp_pre_full d S_child B_child \<and>
      (\<forall>x\<in>S_child. reachable s x) \<and>
      card S_child \<le> M_of l"
    using child_run child_pre child_reaches card_pull by blast
  have calls:
    "list_all2
      (\<lambda>c_child U_child. \<exists>S_child B_child d_child B_child'.
        costed_full_operational_bmssp \<Delta> M_of t k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l)
      ?child_costs ?child_sets"
    using call_head calls_tail by simp
  have sets: "\<forall>X\<in>set ?child_sets. X \<subseteq> V"
    using child_set sets_tail by simp
  have cost:
    "c \<le> sum_list ?child_costs + M_of l * length ?child_costs +
      t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) ?child_sets) +
        M_of l * length ?child_costs)"
  proof -
    have c_eq: "c = c_pull + c_batch + c_child + c_tail"
      using Cost_State_Step by blast
    have "c_pull + c_batch + c_child + c_tail \<le>
        M_of l + t * (card (outgoing_edges U_child) + M_of l) +
        c_child +
        (sum_list child_costs + M_of l * length child_costs +
          t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
            M_of l * length child_costs))"
      using pull_cost batch_cost tail by simp
    also have "\<dots> =
        sum_list ?child_costs + M_of l * length ?child_costs +
        t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) ?child_sets) +
          M_of l * length ?child_costs)"
      by (simp add: algebra_simps)
    finally show ?thesis
      using c_eq by simp
  qed
  show ?case
  proof (intro exI[of _ ?child_costs] exI[of _ ?child_sets] conjI)
    show "length ?child_costs = length ?child_sets"
      using len .
    show "length ?child_costs = length (b # bs)"
      using child_len .
    show "list_all2
      (\<lambda>c_child U_child. \<exists>S_child B_child d_child B_child'.
        costed_full_operational_bmssp \<Delta> M_of t k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l)
      ?child_costs ?child_sets"
      using calls .
    show "\<forall>X\<in>set ?child_sets. X \<subseteq> V"
      using sets .
    show "c \<le> sum_list ?child_costs + M_of l * length ?child_costs +
      t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) ?child_sets) +
        M_of l * length ?child_costs)"
      using cost .
  qed
next
  case (Cost_Base S x \<Delta> M_of t k cap d B)
  show ?case
    by simp
next
  case (Cost_Step D k cap d S B c_insert t \<Delta> M_of l d' a betas bs B'
      Us U_loop c_loop U c)
  show ?case
    by simp
qed

theorem costed_full_operational_partition_loop_state_child_calls_and_cost:
  assumes run:
    "costed_full_operational_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
  obtains child_costs child_sets where
    "concrete_partition_loop_trace P B a bs d' B' Us U"
    "length child_costs = length child_sets"
    "length child_costs = length bs"
    "list_all2
      (\<lambda>c_child U_child. \<exists>S_child B_child d_child B_child'.
        costed_full_operational_bmssp \<Delta> M_of t k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l)
      child_costs child_sets"
    "\<And>X. X \<in> set child_sets \<Longrightarrow> X \<subseteq> V"
    "c \<le> sum_list child_costs + (M_of l) * length child_costs +
      t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
        (M_of l) * length child_costs)"
proof -
  have state:
    "full_operational_partition_loop_state (M_of l) t k cap l d P B d' D a
      betas bs B' Us U c"
    by (rule costed_full_operational_partition_loop_state_refines[OF run])
  have loop:
    "full_operational_partition_loop k cap l d P B d' a betas bs B' Us U"
    by (rule full_operational_partition_loop_state_refines[OF state])
  have trace: "concrete_partition_loop_trace P B a bs d' B' Us U"
    by (rule full_operational_partition_loop_trace[OF loop sound pre P_reaches])
  have data:
    "\<exists>child_costs child_sets.
      length child_costs = length child_sets \<and>
      length child_costs = length bs \<and>
      list_all2
        (\<lambda>c_child U_child. \<exists>S_child B_child d_child B_child'.
          costed_full_operational_bmssp \<Delta> M_of t k cap l d S_child B_child
            d_child B_child' U_child c_child \<and>
          bmssp_pre_full d S_child B_child \<and>
          (\<forall>x\<in>S_child. reachable s x) \<and>
          card S_child \<le> M_of l)
        child_costs child_sets \<and>
      (\<forall>X\<in>set child_sets. X \<subseteq> V) \<and>
      c \<le> sum_list child_costs + (M_of l) * length child_costs +
        t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
          (M_of l) * length child_costs)"
    by (rule costed_full_operational_partition_loop_state_child_call_data
      [OF run sound pre P_reaches])
  obtain child_costs child_sets where len:
      "length child_costs = length child_sets"
    and child_len: "length child_costs = length bs"
    and calls:
      "list_all2
        (\<lambda>c_child U_child. \<exists>S_child B_child d_child B_child'.
          costed_full_operational_bmssp \<Delta> M_of t k cap l d S_child B_child
            d_child B_child' U_child c_child \<and>
          bmssp_pre_full d S_child B_child \<and>
          (\<forall>x\<in>S_child. reachable s x) \<and>
          card S_child \<le> M_of l)
        child_costs child_sets"
    and sets: "\<forall>X\<in>set child_sets. X \<subseteq> V"
    and cost:
      "c \<le> sum_list child_costs + (M_of l) * length child_costs +
        t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
          (M_of l) * length child_costs)"
    using data by blast
  show thesis
  proof (rule that[OF trace len child_len calls _ cost])
    fix X
    assume "X \<in> set child_sets"
    then show "X \<subseteq> V"
      using sets by blast
  qed
qed

theorem costed_full_operational_partition_loop_state_cost_from_child_bound:
  assumes run:
    "costed_full_operational_partition_loop_state \<Delta> M_of t k cap l d P B d' D a
      betas bs B' Us U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and degree: "edge_outdegree_le \<Delta>"
    and child_bound:
      "\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>costed_full_operational_bmssp \<Delta> M_of t k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l\<rbrakk>
        \<Longrightarrow> c_child \<le> C * card U_child"
  obtains child_sets where
    "concrete_partition_loop_trace P B a bs d' B' Us U"
    "\<And>X. X \<in> set child_sets \<Longrightarrow> X \<subseteq> V"
    "length child_sets = length bs"
    "c \<le> (C + t * \<Delta>) * sum_list (map card child_sets) +
      (Suc t) * (M_of l) * length bs"
proof -
  have state:
    "full_operational_partition_loop_state (M_of l) t k cap l d P B d' D a
      betas bs B' Us U c"
    by (rule costed_full_operational_partition_loop_state_refines[OF run])
  have loop:
    "full_operational_partition_loop k cap l d P B d' a betas bs B' Us U"
    by (rule full_operational_partition_loop_state_refines[OF state])
  have trace:
      "concrete_partition_loop_trace P B a bs d' B' Us U"
    by (rule full_operational_partition_loop_trace[OF loop sound pre P_reaches])
  have data:
    "\<exists>child_costs child_sets.
      length child_costs = length child_sets \<and>
      length child_costs = length bs \<and>
      list_all2
        (\<lambda>c_child U_child. \<exists>S_child B_child d_child B_child'.
          costed_full_operational_bmssp \<Delta> M_of t k cap l d S_child B_child
            d_child B_child' U_child c_child \<and>
          bmssp_pre_full d S_child B_child \<and>
          (\<forall>x\<in>S_child. reachable s x) \<and>
          card S_child \<le> M_of l)
        child_costs child_sets \<and>
      (\<forall>X\<in>set child_sets. X \<subseteq> V) \<and>
      c \<le> sum_list child_costs + (M_of l) * length child_costs +
        t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
          (M_of l) * length child_costs)"
    by (rule costed_full_operational_partition_loop_state_child_call_data
      [OF run sound pre P_reaches])
  obtain child_costs child_sets where len: "length child_costs = length child_sets"
    and child_len: "length child_costs = length bs"
    and calls:
      "list_all2
        (\<lambda>c_child U_child. \<exists>S_child B_child d_child B_child'.
          costed_full_operational_bmssp \<Delta> M_of t k cap l d S_child B_child
            d_child B_child' U_child c_child \<and>
          bmssp_pre_full d S_child B_child \<and>
          (\<forall>x\<in>S_child. reachable s x) \<and>
          card S_child \<le> M_of l)
        child_costs child_sets"
    and sets: "\<And>X. X \<in> set child_sets \<Longrightarrow> X \<subseteq> V"
    and cost:
      "c \<le> sum_list child_costs + (M_of l) * length child_costs +
        t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
          (M_of l) * length child_costs)"
    using data by blast
  have child_sets_len: "length child_sets = length bs"
    using len child_len by simp
  have child_cost_bounds:
    "list_all2 (\<lambda>c_child U_child. c_child \<le> C * card U_child)
      child_costs child_sets"
    using calls
  proof (induction rule: list_all2_induct)
    case Nil
    then show ?case by simp
  next
    case (Cons c_child child_costs U_child child_sets)
    obtain S_child B_child d_child B_child' where child:
        "costed_full_operational_bmssp \<Delta> M_of t k cap l d S_child B_child
          d_child B_child' U_child c_child"
      and child_pre: "bmssp_pre_full d S_child B_child"
      and child_reaches: "\<forall>x\<in>S_child. reachable s x"
      and child_card: "card S_child \<le> M_of l"
      using Cons.hyps by blast
    have head: "c_child \<le> C * card U_child"
      by (rule child_bound[OF child child_pre _ child_card])
        (use child_reaches in blast)
    show ?case
      using head Cons.IH Cons.hyps by simp
  qed
  have child_sum:
    "sum_list child_costs \<le> C * sum_list (map card child_sets)"
  proof -
    have "sum_list child_costs \<le>
        sum_list (map (\<lambda>X. C * card X) child_sets)"
      using sum_list_le_if_list_all2[OF child_cost_bounds] .
    also have "\<dots> = C * sum_list (map card child_sets)"
      by (induction child_sets) (simp_all add: algebra_simps)
    finally show ?thesis .
  qed
  have edge_sum:
    "sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) \<le>
      \<Delta> * sum_list (map card child_sets)"
    by (rule sum_card_outgoing_edges_le_degree[OF degree sets])
  have "c \<le>
      C * sum_list (map card child_sets) + (M_of l) * length child_sets +
      t * (\<Delta> * sum_list (map card child_sets) +
        (M_of l) * length child_sets)"
  proof -
    have middle:
      "(M_of l) * length child_costs \<le> (M_of l) * length child_sets"
      using len by simp
    have inside:
      "sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
        (M_of l) * length child_costs \<le>
       \<Delta> * sum_list (map card child_sets) +
        (M_of l) * length child_sets"
      using edge_sum middle by linarith
    have tail_term:
      "t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
          (M_of l) * length child_costs) \<le>
       t * (\<Delta> * sum_list (map card child_sets) +
          (M_of l) * length child_sets)"
      using inside by simp
    have "sum_list child_costs + (M_of l) * length child_costs +
        t * (sum_list (map (\<lambda>X. card (outgoing_edges X)) child_sets) +
          (M_of l) * length child_costs) \<le>
        C * sum_list (map card child_sets) + (M_of l) * length child_sets +
        t * (\<Delta> * sum_list (map card child_sets) +
          (M_of l) * length child_sets)"
      using child_sum middle tail_term by linarith
    then show ?thesis
      using cost by linarith
  qed
  also have "\<dots> =
      (C + t * \<Delta>) * sum_list (map card child_sets) +
      (Suc t) * (M_of l) * length child_sets"
    by (simp add: algebra_simps)
  finally have final:
    "c \<le> (C + t * \<Delta>) * sum_list (map card child_sets) +
      (Suc t) * (M_of l) * length bs"
    using child_sets_len by simp
  show thesis
  proof (rule that[OF trace _ child_sets_len final])
    fix X
    assume "X \<in> set child_sets"
    then show "X \<subseteq> V"
      using sets by blast
  qed
qed

end

end
