theory Mixed_O2H

imports Pure_O2H 
  Estimation 
  Run_Adversary 
  Limit_Process 
  Purification

begin

section \<open>Mixed O2H Setting and Preliminaries\<close>

hide_const (open) Determinants.trace


locale mixed_o2h = o2h_setting "TYPE('x)" "TYPE('y::group_add)" "TYPE('mem)" "TYPE('l)" +
  \<comment> \<open>We fix the distributions on H and S. (They might be correlated.)
    So far, we assume that they are discrete distributions and model them in the following way:\<close>
  (* 
  Future steps for generalisations: 
  Fist make 'x and 'y finite and use UNIV instead of carrier sets, 
  then think about if and how to make the sums infinite
  (or have distr_H >0 only for finitely many Hs)
  For Thm1 also include G into the distribution
*)

(*Need joint distributions H S z G*)
fixes carrier :: "(('x \<Rightarrow> 'y)\<times>('x \<Rightarrow> bool)\<times>_) set" 
fixes distr :: "(('x \<Rightarrow> 'y)\<times>('x \<Rightarrow> bool)\<times>_) \<Rightarrow> real"

assumes distr_pos: "\<forall>(H,S,z)\<in>carrier. distr (H,S,z) \<ge> 0"
  and distr_sum_1: "(\<Sum>(H,S,z)\<in>carrier. distr (H,S,z)) = 1"
  and finite_carrier: "finite carrier" 
  (*Assumption for application of Lemma 1, needs to be eliminated eventually *)

(* fix the adversary! *)
fixes E:: "'mem kraus_adv"
assumes E_norm_id: "\<And>i. i < d+1 \<Longrightarrow> kf_bound (E i) \<le> id_cblinfun"
assumes E_nonzero: "\<And>i. i < d+1 \<Longrightarrow> Rep_kraus_family (E i) \<noteq> {}"

fixes P:: "'mem update"
assumes is_Proj_P: "is_Proj P"


begin

lemma norm_P: 
  "norm P \<le> 1"
  using is_Proj_P by (simp add: norm_is_Proj)

lemma distr_pos':
  assumes "(H,S,z)\<in>carrier" shows "distr (H,S,z) \<ge> 0"
  using distr_pos assms by auto

lemma norm_Fst_P:
  "norm (Fst P:: ('mem \<times> 'a) update) \<le> 1"
  by (simp add: Fst_def norm_P tensor_op_norm)

(*
Notation:
\<rho>left = expectation over H,S of run_A_update H S
\<rho>right = expectation over H,S of run_B_update H S
*)

subsection \<open>Final states\<close>

definition \<rho>left_pure :: "(nat \<Rightarrow> 'mem update) \<Rightarrow> 'mem tc_op" where
  "\<rho>left_pure UA = (\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) *\<^sub>C run_pure_A_tc UA H)"

definition \<rho>left :: "'mem kraus_adv \<Rightarrow> 'mem tc_op" where
  "\<rho>left F = (\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) *\<^sub>C run_mixed_A F H)"


definition \<rho>right_pure :: "(nat \<Rightarrow> 'mem update) \<Rightarrow> ('mem \<times> 'l) tc_op" where
  "\<rho>right_pure UA = (\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) *\<^sub>C run_pure_B_tc UA H S)"

definition \<rho>right :: "'mem kraus_adv \<Rightarrow> ('mem \<times> 'l) tc_op" where
  "\<rho>right F = (\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) *\<^sub>C run_mixed_B F H S)"


definition \<rho>count_pure :: "(nat \<Rightarrow> 'mem update) \<Rightarrow> ('mem \<times> nat) tc_op" where
  "\<rho>count_pure UA = (\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) *\<^sub>C run_pure_B_count_tc UA H S)"

definition \<rho>count :: "'mem kraus_adv \<Rightarrow> ('mem \<times> nat) tc_op" where
  "\<rho>count F = (\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) *\<^sub>C run_mixed_B_count F H S)"



text \<open>Positivity\<close>

lemma \<rho>left_pure_pos: "0 \<le> \<rho>left_pure UA"
  unfolding \<rho>left_pure_def by (intro sum_nonneg) (metis (mono_tags, lifting) complex_of_real_nn_iff 
      distr_pos prod.case_eq_if run_pure_A_tc_pos scaleC_nonneg_nonneg)

lemma \<rho>left_pos: "0 \<le> \<rho>left F"
  unfolding \<rho>left_def by (intro sum_nonneg) (metis (mono_tags, lifting) complex_of_real_nn_iff 
      distr_pos prod.case_eq_if run_mixed_A_pos scaleC_nonneg_nonneg)

lemma \<rho>right_pure_pos: "0 \<le> \<rho>right_pure UA"
  unfolding \<rho>right_pure_def by (intro sum_nonneg) (metis (mono_tags, lifting) complex_of_real_nn_iff 
      distr_pos prod.case_eq_if run_pure_B_tc_pos scaleC_nonneg_nonneg)

lemma \<rho>right_pos: "0 \<le> \<rho>right F"
  unfolding \<rho>right_def by (intro sum_nonneg) (metis (mono_tags, lifting) complex_of_real_nn_iff 
      distr_pos prod.case_eq_if run_mixed_B_pos scaleC_nonneg_nonneg)

lemma \<rho>count_pure_pos: "0 \<le> \<rho>count_pure UA"
  unfolding \<rho>count_pure_def by (intro sum_nonneg)(metis (mono_tags, lifting) complex_of_real_nn_iff 
      distr_pos prod.case_eq_if run_pure_B_count_tc_pos scaleC_nonneg_nonneg)

lemma \<rho>count_pos: "0 \<le> \<rho>count F"
  unfolding \<rho>count_def by (intro sum_nonneg) (metis (mono_tags, lifting) complex_of_real_nn_iff 
      distr_pos prod.case_eq_if run_mixed_B_count_pos scaleC_nonneg_nonneg)


text \<open>Norm leq 1, trace-preserving adversary states have norm 1\<close>


lemma norm_\<rho>left:
  "norm (\<rho>left E) \<le> 1"
proof -
  have "norm (\<rho>left E) \<le> (\<Sum>(H,S,z)\<in>carrier. norm ((distr (H,S,z)) *\<^sub>C run_mixed_A E H))"
    unfolding \<rho>left_def using norm_sum by (simp add: prod.case_eq_if sum_norm_le)
  also have "\<dots> = (\<Sum>(H,S,z)\<in>carrier. (distr (H,S,z)) *\<^sub>C norm (run_mixed_A E H))"
    by (auto intro!: sum.cong simp add: distr_pos')
  also have "\<dots> \<le> (\<Sum>(H,S,z)\<in>carrier. (distr (H,S,z)) *\<^sub>C 1)"
  proof (intro sum_mono, safe, goal_cases)
    case (1 H S z)
    have one: "0 \<le> complex_of_real (distr (H, S, z))" using distr_pos' 1 by auto
    have two: "complex_of_real (norm (run_mixed_A E H)) \<le> (1::complex)" 
      using norm_run_mixed_A[OF E_norm_id] 1 by auto
    then show ?case by (metis complex_scaleC_def one mult_left_mono)
  qed 
  also have "\<dots> = 1" using distr_sum_1 by (auto simp add: of_real_sum[symmetric])
  finally show ?thesis by auto
qed

lemma norm_\<rho>right:
  "norm (\<rho>right E) \<le> 1"
proof -
  have "norm (\<rho>right E) \<le> (\<Sum>(H,S,z)\<in>carrier. norm ((distr (H,S,z)) *\<^sub>C run_mixed_B E H S))"
    unfolding \<rho>right_def using norm_sum by (simp add: prod.case_eq_if sum_norm_le)
  also have "\<dots> = (\<Sum>(H,S,z)\<in>carrier. (distr (H,S,z)) *\<^sub>C norm (run_mixed_B E H S))"
    by (auto intro!: sum.cong simp add: distr_pos')
  also have "\<dots> \<le> (\<Sum>(H,S,z)\<in>carrier. (distr (H,S,z)) *\<^sub>C 1)"
  proof (intro sum_mono, safe, goal_cases)
    case (1 H S z)
    have one: "0 \<le> complex_of_real (distr (H, S, z))" using distr_pos' 1 by auto
    have two: "complex_of_real (norm (run_mixed_B E H S)) \<le> (1::complex)" 
      using norm_run_mixed_B[OF E_norm_id] 1 by auto
    then show ?case by (metis complex_scaleC_def one mult_left_mono)
  qed 
  also have "\<dots> = 1" using distr_sum_1 by (auto simp add: of_real_sum[symmetric])
  finally show ?thesis by auto
qed

lemma norm_\<rho>count:
  "norm (\<rho>count E) \<le> 1"
proof -
  have "norm (\<rho>count E) \<le> (\<Sum>(H,S,z)\<in>carrier. norm ((distr (H,S,z)) *\<^sub>C run_mixed_B_count E H S))"
    unfolding \<rho>count_def using norm_sum by (simp add: prod.case_eq_if sum_norm_le)
  also have "\<dots> = (\<Sum>(H,S,z)\<in>carrier. (distr (H,S,z)) *\<^sub>C norm (run_mixed_B_count E H S))"
    by (auto intro!: sum.cong simp add: distr_pos')
  also have "\<dots> \<le> (\<Sum>(H,S,z)\<in>carrier. (distr (H,S,z)) *\<^sub>C 1)"
  proof (intro sum_mono, safe, goal_cases)
    case (1 H S z)
    have one: "0 \<le> complex_of_real (distr (H, S, z))" using distr_pos' 1 by auto
    have two: "complex_of_real (norm (run_mixed_B_count E H S)) \<le> (1::complex)" 
      using norm_run_mixed_B_count[OF E_norm_id] 1 by auto
    then show ?case by (metis complex_scaleC_def one mult_left_mono)
  qed 
  also have "\<dots> = 1" using distr_sum_1 by (auto simp add: of_real_sum[symmetric])
  finally show ?thesis by auto
qed



lemma trace_preserving_norm_\<rho>right:
  assumes "\<And>i. i < d+1 \<Longrightarrow> km_trace_preserving (kf_apply 
  (kf_Fst (E i)::(('mem \<times> 'l) ell2, ('mem \<times> 'l) ell2, unit) kraus_family))"
  shows "norm (\<rho>right E) = 1"
proof -
  have "norm (\<Sum>(H, S, z)\<in>carrier. (distr (H, S, z)) *\<^sub>C run_mixed_B E H S) = 
    trace_tc (\<Sum>(H, S, z)\<in>carrier. (distr (H, S, z)) *\<^sub>C run_mixed_B E H S)"
    using \<rho>right_def \<rho>right_pos norm_tc_pos by auto
  also have "\<dots> = (\<Sum>(H, S, z)\<in>carrier. (distr (H, S, z)) * trace_tc (run_mixed_B E H S))" 
    by (smt (verit) complex_scaleC_def prod.case_eq_if sum.cong trace_tc_scaleC trace_tc_sum)
  also have "\<dots> = (\<Sum>(H, S, z)\<in>carrier. (distr (H, S, z)) * norm (run_mixed_B E H S))"
    by (subst of_real_sum, intro sum.cong, simp)
      (simp add: norm_tc_pos prod.case_eq_if run_mixed_B_pos)
  also have "\<dots> = (\<Sum>(H, S, z)\<in>carrier. (distr (H, S, z)))" 
    using trace_preserving_norm_run_mixed_B[OF assms] by auto
  also have "\<dots> = 1" using distr_sum_1 by blast
  finally show ?thesis unfolding \<rho>right_def by auto
qed

lemma trace_preserving_norm_\<rho>count:
  assumes "\<And>i. i < d+1 \<Longrightarrow> km_trace_preserving (kf_apply 
  (kf_Fst (E i)::(('mem \<times> nat) ell2, ('mem \<times> nat) ell2, unit) kraus_family))"
  shows "norm (\<rho>count E) = 1"
proof -
  have "norm (\<Sum>(H, S, z)\<in>carrier. (distr (H, S, z)) *\<^sub>C run_mixed_B_count E H S) = 
    trace_tc (\<Sum>(H, S, z)\<in>carrier. (distr (H, S, z)) *\<^sub>C run_mixed_B_count E H S)"
    using \<rho>count_def \<rho>count_pos norm_tc_pos by auto
  also have "\<dots> = (\<Sum>(H, S, z)\<in>carrier. (distr (H, S, z)) * trace_tc (run_mixed_B_count E H S))" 
    by (smt (verit) complex_scaleC_def prod.case_eq_if sum.cong trace_tc_scaleC trace_tc_sum)
  also have "\<dots> = (\<Sum>(H, S, z)\<in>carrier. (distr (H, S, z)) * norm (run_mixed_B_count E H S))"
    by (subst of_real_sum, intro sum.cong, simp)
      (simp add: norm_tc_pos prod.case_eq_if run_mixed_B_count_pos)
  also have "\<dots> = (\<Sum>(H, S, z)\<in>carrier. (distr (H, S, z)))" 
    using trace_preserving_norm_run_mixed_B_count[OF assms] by auto
  also have "\<dots> = 1" using distr_sum_1 by blast
  finally show ?thesis unfolding \<rho>count_def by auto
qed


text \<open>Summability and Infsums\<close>
  (* 
In the case that finite (carrier), the following is easier.

For the case that carrier of distribution on H,S is infinite
infsum_Sigma_positive_tc 
infsum_swap_positive_tc

However, we get problems since the sum is not finite and we cannot use the auxiliary lemma!
 *)

lemma from_trace_class_\<rho>right_pure:
  "from_trace_class (\<rho>right_pure UA) = (\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) *\<^sub>C run_pure_B_update UA H S)"
  by (smt (verit) \<rho>right_pure_def from_trace_class_sum run_pure_B_tc_def prod.case_eq_if 
      run_pure_B_update_def run_pure_adv_update_tc' scaleC_trace_class.rep_eq sum.cong)



lemma has_sum_scaleC_tc:
  fixes x :: "('a::chilbert_space,'a) trace_class"
  assumes "(f has_sum x) A"
  shows "((\<lambda>y. c *\<^sub>C f y) has_sum c *\<^sub>C x) A"
  using assms by (rule has_sum_scaleC_right)


lemma \<rho>left_has_sum:
  "(\<rho>left has_sum \<rho>left E) (finite_kraus_subadv E d)"
proof -
  have "((\<lambda>x. (distr (H,S,z)) *\<^sub>C run_mixed_A x H) has_sum (distr (H,S,z)) *\<^sub>C run_mixed_A E H)
        (finite_kraus_subadv E d)" for H S z
    using has_sum_scaleC_tc[OF run_mixed_A_has_sum[of H E]] by auto
  then show ?thesis unfolding \<rho>left_def by (intro has_sum_finite_sum[OF _ finite_carrier]) 
      (auto simp add: case_prod_beta intro!: has_sum_cmult_right) 
qed


lemma \<rho>right_has_sum:
  "((\<lambda>f. \<rho>right f) has_sum \<rho>right E) (finite_kraus_subadv E d)"
proof -
  have "((\<lambda>x. (distr (H,S,z)) *\<^sub>C run_mixed_B x H S) has_sum (distr (H,S,z)) *\<^sub>C run_mixed_B E H S)
        (finite_kraus_subadv E d)" for H S z
    using has_sum_scaleC_tc[OF run_mixed_B_has_sum'[of H S E]] by auto
  then show ?thesis unfolding \<rho>right_def by (intro has_sum_finite_sum[OF _ finite_carrier]) 
      (auto simp add: case_prod_beta intro!: has_sum_cmult_right) 
qed


lemma \<rho>right_abs_summable:
  "\<rho>right abs_summable_on (finite_kraus_subadv E d)"
  using has_sum_imp_summable[OF \<rho>right_has_sum] \<rho>right_pos summable_abs_summable_tc by blast


lemma \<rho>count_has_sum:
  "(\<rho>count has_sum \<rho>count E) (finite_kraus_subadv E d)"
proof -
  have "((\<lambda>x. (distr (H,S,z)) *\<^sub>C run_mixed_B_count x H S) has_sum (distr (H,S,z)) *\<^sub>C run_mixed_B_count E H S)
        (finite_kraus_subadv E d)" for H S z
    using has_sum_scaleC_tc[OF run_mixed_B_count_has_sum'[of H S E]] by auto
  then show ?thesis unfolding \<rho>count_def by (intro has_sum_finite_sum[OF _ finite_carrier]) 
      (auto simp add: case_prod_beta intro!: has_sum_cmult_right) 
qed


text \<open>Connection pure and mixed states\<close>

lemma \<rho>left_pure_mixed:
  assumes "\<And>i. i < d + 1 \<Longrightarrow> finite (Rep_kraus_family (F i))"
    "\<And>i. i < d + 1 \<Longrightarrow> fst ` Rep_kraus_family (F i) \<noteq> {}"
  shows "\<rho>left F = (\<Sum>UAs \<in> purify_comp_kraus d F. \<rho>left_pure UAs)"
proof -
  have run: "run_mixed_A F H = (\<Sum>UAs\<in>purify_comp_kraus d F. run_pure_A_tc UAs H)" for H
    using purification_run_mixed_A assms by auto
  have "\<rho>left F = (\<Sum>UAs\<in>purify_comp_kraus d F. (\<Sum>(H,S,z)\<in>carrier.
        complex_of_real (distr (H,S,z)) *\<^sub>C run_pure_A_tc UAs H))" 
    unfolding \<rho>left_def run by (subst sum.swap) (auto intro!: sum.cong simp add: scaleC_sum_right)
  then show ?thesis unfolding \<rho>left_pure_def by auto
qed

lemma \<rho>right_pure_mixed:
  assumes "\<And>i. i < d + 1 \<Longrightarrow> finite (Rep_kraus_family (F i))"
    "\<And>i. i < d + 1 \<Longrightarrow> fst ` Rep_kraus_family (F i) \<noteq> {}"
  shows "\<rho>right F = (\<Sum>UAs \<in> purify_comp_kraus d F. \<rho>right_pure UAs)"
proof -
  have run: "run_mixed_B F H S = (\<Sum>UAs\<in>purify_comp_kraus d F. run_pure_B_tc UAs H S)" for H S
    using purification_run_mixed_B assms by blast
  have "\<rho>right F = (\<Sum>UAs\<in>purify_comp_kraus d F. (\<Sum>(H,S,z)\<in>carrier.
        complex_of_real (distr (H,S,z)) *\<^sub>C run_pure_B_tc UAs H S))" 
    unfolding \<rho>right_def run by (subst sum.swap) (auto intro!: sum.cong simp add: scaleC_sum_right)
  then show ?thesis unfolding \<rho>right_pure_def by auto
qed

lemma \<rho>count_pure_mixed:
  assumes "\<And>i. i < d + 1 \<Longrightarrow> finite (Rep_kraus_family (F i))"
    "\<And>i. i < d + 1 \<Longrightarrow> fst ` Rep_kraus_family (F i) \<noteq> {}"
  shows "\<rho>count F = (\<Sum>UAs \<in> purify_comp_kraus d F. \<rho>count_pure UAs)"
proof -
  have run: "run_mixed_B_count F H S = (\<Sum>UAs\<in>purify_comp_kraus d F. run_pure_B_count_tc UAs H S)" for H S
    using purification_run_mixed_B_count assms by blast
  have "\<rho>count F = (\<Sum>UAs\<in>purify_comp_kraus d F. (\<Sum>(H,S,z)\<in>carrier.
        complex_of_real (distr (H,S,z)) *\<^sub>C run_pure_B_count_tc UAs H S))" 
    unfolding \<rho>count_def run by (subst sum.swap) (auto intro!: sum.cong simp add: scaleC_sum_right)
  then show ?thesis unfolding \<rho>count_pure_def by auto
qed


subsection \<open>Measurement at the end\<close>

text \<open>Measurement at the end of the adversary run. 
\<open>end_measure\<close> measures whether there was a find element (event "Find").\<close>


definition end_measure :: "('mem \<times> 'l) update" where
  "end_measure = Snd (id_cblinfun - selfbutter (ket empty))"

lemma is_Proj_Snd:
  assumes "is_Proj f"
  shows "is_Proj (Snd f)"
  by (simp add: assms register_projector)


lemma is_Proj_end_measure:
  "is_Proj end_measure"
  unfolding end_measure_def by (auto intro!: is_Proj_Snd simp add: butterfly_is_Proj)

lemma Proj_end_measure:
  "Proj (end_measure *\<^sub>S \<top>) = end_measure"
  using Proj_on_own_range is_Proj_end_measure by auto

lemma norm_end_measure:
  "norm (end_measure) \<le> 1"
  using norm_is_Proj is_Proj_end_measure by auto

lemma end_measure_butterfly:
  "sandwich end_measure (selfbutter \<Psi>) = selfbutter (end_measure *\<^sub>V \<Psi>)"
  by (rule sandwich_butterfly)

lemma trace_end_measure:
  "trace (end_measure o\<^sub>C\<^sub>L selfbutter \<Psi>) = (complex_of_real (norm (end_measure *\<^sub>V \<Psi>)))\<^sup>2"
  by (metis (no_types, lifting) cblinfun_apply_cblinfun_compose cinner_adj_left 
      is_Proj_algebraic is_Proj_end_measure power2_norm_eq_cinner trace_butterfly_comp')


lemma trace_endmeasure_pos:
  assumes "\<rho> \<ge> 0"
  shows "trace_tc (compose_tcr end_measure \<rho>) \<ge> 0"
  by (metis (no_types, opaque_lifting) assms compose_tcr.rep_eq from_trace_class_pos is_Proj_algebraic 
      is_Proj_end_measure positive_cblinfun_squareI trace_class_from_trace_class trace_comp_pos trace_tc.rep_eq)

lemma trace_class_end_measure:
  assumes "trace_class a"
  shows "trace_class (end_measure o\<^sub>C\<^sub>L a)"
  using assms by (rule trace_class_comp_right)

lemma abs_op_id_cblinfun [simp]:
  "abs_op id_cblinfun = id_cblinfun"
  by (simp add: abs_op_id_on_pos)

section \<open>\<^term>\<open>empty_tc\<close> is the trace-class representative of the $0$.\<close>

definition empty_tc :: "'l tc_op" where 
  "empty_tc = Abs_trace_class (selfbutter (ket empty))"

lemma norm_empty_tc:
  "norm empty_tc = 1" 
  unfolding empty_tc_def by (metis more_arith_simps(6) norm_ket norm_tc_butterfly tc_butterfly.abs_eq)

lemma empty_tc_pos: "0 \<le> empty_tc"
  unfolding empty_tc_def by (simp add: Abs_trace_class_geq0I)


subsection \<open>Projective measurement PM\<close>

text \<open>The projective measurement PM Q at the end\<close>


definition PM_update :: "('mem \<times> 'l) update  \<Rightarrow> ('mem \<times> 'l) update \<Rightarrow> complex" where
  "PM_update Q \<rho> = trace (sandwich Q \<rho>)"

lemma PM_update_linear:
  assumes "trace_class \<rho>" "trace_class \<psi>"
  shows "PM_update Q (\<rho> + \<psi>) = PM_update Q \<rho> + PM_update Q \<psi>"
  unfolding PM_update_def
  by (simp add: assms(1) assms(2) cblinfun.add_right trace_class_sandwich trace_plus)

definition PM :: "('mem \<times> 'l) update \<Rightarrow> ('mem \<times> 'l) tc_op \<Rightarrow> complex" where
  "PM Q = PM_update Q o from_trace_class"

lemma PM_altdef:
  "PM Q \<rho> = trace_tc (sandwich_tc Q \<rho>)"
  unfolding PM_def PM_update_def by (simp add: from_trace_class_sandwich_tc trace_tc.rep_eq)

lemma PM_linear:
  "PM Q (\<rho> + \<psi>) = PM Q \<rho> + PM Q \<psi>"
  unfolding PM_altdef by (simp add: sandwich_tc_plus trace_tc_plus)

lemma PM_sum_distr:
  "PM Q (sum f S) = sum (PM Q o f) S"
  by (metis PM_linear add_cancel_right_right sum_comp_morphism)

lemma PM_scale:
  "PM Q (a *\<^sub>C \<rho>) = a * PM Q \<rho>"
  unfolding PM_altdef by (simp add: sandwich_tc_scaleC_right trace_tc_scaleC)

lemma PM_case:
  "PM Q (case x of (H,S,z) \<Rightarrow> f H S) = (case x of (H,S,z) \<Rightarrow> PM Q (f H S))"
  by (simp add: prod.case_eq_if)

lemma PM_Re:
  assumes "\<rho> \<ge> 0"
  shows "Re (PM Q \<rho>) = PM Q \<rho>"
  unfolding PM_altdef by (simp add: assms complex_is_real_iff_compare0 sandwich_tc_pos trace_tc_pos)

lemma PM_pos:
  assumes "\<rho> \<ge> 0"
  shows "PM Q \<rho> \<ge> 0"
  by (simp add: PM_def PM_update_def assms from_trace_class_pos sandwich_pos trace_pos)

lemma Re_PM_pos:
  assumes "\<rho> \<ge> 0"
  shows "Re (PM Q \<rho>) \<ge> 0" 
  using PM_Re PM_pos[OF assms] by (simp add: less_eq_complex_def)

lemma norm_PM:
  assumes "norm \<rho> \<le> 1" "norm Q \<le> 1"
  shows "norm (PM Q \<rho>) \<le> 1"
proof -
  have "norm (PM Q \<rho>) \<le> norm (sandwich_tc (Q:: ('mem \<times> 'l) update) \<rho>)"
    unfolding PM_altdef using trace_tc_norm by auto
  also have "\<dots> \<le> (norm (Q :: ('mem \<times> 'l) update))^2 * norm \<rho>" by (rule norm_sandwich_tc)
  also have "\<dots> \<le> norm \<rho>" using \<open>norm Q \<le> 1\<close> mult_le_cancel_right2 power_mono by fastforce
  also have "\<dots> \<le> 1" using assms by auto
  finally show ?thesis by auto
qed

lemma PM_bounded_linear:
  shows "bounded_linear (PM Q)"
  unfolding PM_altdef by (simp add: bounded_linear_trace_norm_sandwich_tc)

text \<open>has\_sum property of PM\<close>

lemma PM_has_sum:
  assumes "(f has_sum x) A"
  shows "(PM Q o f has_sum PM Q x) A"
  unfolding o_def by (simp add: has_sum_bounded_linear PM_bounded_linear assms)



subsection \<open>Pright and Pleft'\<close>

definition Pleft' where "Pleft' Q = Re (PM Q (tc_tensor (\<rho>left E) empty_tc))"

definition Pleft where "Pleft Q = Re (trace_tc (sandwich_tc Q (\<rho>left E)))"

lemma trace_tensor_tc:
  "trace_tc (tc_tensor a b) = trace_tc a * trace_tc b"
  by (simp add: tc_tensor.rep_eq trace_tc.rep_eq trace_tensor)


lemma Pleft_Pleft':
  assumes "sandwich_tc A empty_tc = tc_selfbutter (ket empty)"
  shows "Pleft Q = Pleft' (Q \<otimes>\<^sub>o A)"
proof -
  from assms have "trace_tc (sandwich_tc Q (\<rho>left E)) = 
    trace_tc (sandwich_tc (Q \<otimes>\<^sub>o A) (tc_tensor (\<rho>left E) empty_tc))"
    by (metis empty_tc_def empty_tc_pos from_trace_class_inverse mult_cancel_left1 norm_empty_tc 
        norm_tc_pos of_real_1 sandwich_tc_tensor tc_butterfly.rep_eq tc_selfbutter_def trace_tensor_tc)
  then show ?thesis unfolding Pleft_def Pleft'_def PM_altdef by auto
qed



lemma Pleft_Pleft'_empty:
  "Pleft Q = Pleft' (Q \<otimes>\<^sub>o selfbutter (ket empty))"
proof -
  have "sandwich_tc (selfbutter (ket empty)) empty_tc = tc_selfbutter (ket empty)"
    unfolding empty_tc_def tc_selfbutter_def sandwich_tc_def tc_butterfly_def compose_tcl_def 
      compose_tcr_def by (auto simp add: Abs_trace_class_inverse)
  then show ?thesis using Pleft_Pleft' by auto
qed

lemma Pleft_Pleft'_id:
  "Pleft Q = Pleft' (Q \<otimes>\<^sub>o id_cblinfun)"
proof -
  have "sandwich_tc (id_cblinfun) empty_tc = tc_selfbutter (ket empty)"
    unfolding empty_tc_def tc_selfbutter_def sandwich_tc_def tc_butterfly_def compose_tcl_def 
      compose_tcr_def by (auto simp add: Abs_trace_class_inverse)
  then show ?thesis using Pleft_Pleft' by auto
qed

lemma Pleft_Pleft'_case5:
  assumes "is_Proj Q"
  shows "Pleft Q = Pleft' (Q \<otimes>\<^sub>o selfbutter (ket empty) + end_measure)"
proof -
  define Set where "Set = (Q \<otimes>\<^sub>o id_cblinfun) *\<^sub>S \<top> \<squnion> 
    (id_cblinfun \<otimes>\<^sub>o (id_cblinfun - selfbutter (ket empty))) *\<^sub>S \<top>"
  have rew: "Q \<otimes>\<^sub>o selfbutter (ket empty) + end_measure = Proj (Set)" unfolding Set_def
    by (subst splitting_Proj_or) (auto simp add: butterfly_is_Proj assms end_measure_def Snd_def 
        is_Proj_end_measure)
  have "(id_cblinfun - selfbutter (ket empty)) o\<^sub>C\<^sub>L selfbutter (ket empty) = 0"
    by (simp add: cblinfun_compose_minus_left)
  then have zero: "compose_tcr end_measure (tc_tensor (\<rho>left E) empty_tc) = 0"
    unfolding compose_tcr_def empty_tc_def end_measure_def Snd_def 
    by (auto simp add: Abs_trace_class_inverse comp_tensor_op tc_tensor.rep_eq zero_trace_class.abs_eq)
  have "trace_tc (sandwich_tc (Q \<otimes>\<^sub>o selfbutter (ket empty) + end_measure) 
    (tc_tensor (\<rho>left E) empty_tc)) = 
    trace_tc (compose_tcr (Q \<otimes>\<^sub>o selfbutter (ket empty) + end_measure) 
    (tc_tensor (\<rho>left E) empty_tc))" unfolding rew sandwich_tc_def trace_tc.rep_eq 
    compose_tcl.rep_eq compose_tcr.rep_eq
    by (metis (no_types, lifting) Proj_idempotent adj_Proj cblinfun_assoc_left(1) circularity_of_trace 
        compose_tcr.rep_eq trace_class_from_trace_class) 
  also have "\<dots> = trace_tc (compose_tcr (Q \<otimes>\<^sub>o selfbutter (ket empty)) (tc_tensor (\<rho>left E) empty_tc) + 
    compose_tcr end_measure (tc_tensor (\<rho>left E) empty_tc))"
    by (simp add: compose_tcr.add_left)
  also have "\<dots> = trace_tc (compose_tcr (Q \<otimes>\<^sub>o selfbutter (ket empty)) (tc_tensor (\<rho>left E) empty_tc))"
    using zero by auto
  also have "\<dots> = trace_tc (sandwich_tc (Q \<otimes>\<^sub>o selfbutter (ket empty)) (tc_tensor (\<rho>left E) empty_tc))"
    unfolding sandwich_tc_def trace_tc.rep_eq compose_tcl.rep_eq compose_tcr.rep_eq
    by (metis (no_types, lifting) assms butterfly_is_Proj cblinfun_assoc_left(1) circularity_of_trace 
        compose_tcr.rep_eq is_Proj_algebraic is_Proj_tensor_op norm_ket trace_class_from_trace_class)
  finally have "trace_tc (sandwich_tc (Q \<otimes>\<^sub>o selfbutter (ket empty) + end_measure) 
    (tc_tensor (\<rho>left E) empty_tc)) = 
    trace_tc (sandwich_tc (Q \<otimes>\<^sub>o selfbutter (ket empty)) (tc_tensor (\<rho>left E) empty_tc))"
    by auto
  then have "Pleft' (Q \<otimes>\<^sub>o selfbutter (ket empty) + end_measure) = Pleft' (Q \<otimes>\<^sub>o selfbutter (ket empty))"
    unfolding Pleft'_def PM_altdef by auto
  then show ?thesis using Pleft_Pleft'_empty by auto
qed


definition Pright where "Pright Q = Re (PM Q (\<rho>right E))"

lemma Re_PM_left_has_sum:
  "((\<lambda>F. Re (PM Q (tc_tensor (\<rho>left F) empty_tc))) has_sum Pleft' Q) 
  (finite_kraus_subadv E d)"
  unfolding Pleft'_def
  using Re_has_sum[OF PM_has_sum[OF tc_tensor_has_sum [of _ _ _ empty_tc, OF \<rho>left_has_sum]]]
    PM_pos[OF tc_tensor_pos[OF \<rho>left_pos empty_tc_pos]] unfolding comp_def by auto

lemma Re_PM_right_has_sum:
  "((\<lambda>F. Re (PM Q (\<rho>right F))) has_sum Pright Q) (finite_kraus_subadv E d)" 
  unfolding Pright_def
  using Re_has_sum[OF PM_has_sum[OF \<rho>right_has_sum]] PM_pos[OF \<rho>right_pos] by (auto simp add: o_def)






subsection \<open>Pfind\<close>

text \<open>The definition of the find event\<close>
definition Pfind_update ::
  "(nat \<Rightarrow> 'mem update) \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> ('x \<Rightarrow> bool) \<Rightarrow> complex" where
  "Pfind_update UA H S = trace (end_measure o\<^sub>C\<^sub>L (run_pure_B_update UA H S))"

definition Pfind_pure :: "(nat \<Rightarrow> 'mem update) \<Rightarrow> complex" where
  "Pfind_pure UA = trace_tc (compose_tcr end_measure  (\<rho>right_pure UA))" 

definition Pfind :: "'mem kraus_adv \<Rightarrow> complex" where
  "Pfind F = trace_tc (compose_tcr end_measure (\<rho>right F))" 


lemma Pfind_altdef:
  "Pfind E = Pright end_measure"
  unfolding Pfind_def Pright_def PM_altdef
  by (smt (verit) \<rho>right_pos cblinfun_assoc_left(1) circularity_of_trace complex_is_real_iff_compare0 
      compose_tcr.rep_eq from_trace_class_sandwich_tc is_Proj_algebraic is_Proj_end_measure of_real_Re 
      sandwich_apply sandwich_tc_pos trace_class_from_trace_class trace_tc.rep_eq trace_tc_pos)


lemma Pfind_Pright:
  "Re (Pfind E) = Pright end_measure"
  unfolding Pfind_altdef by auto


text \<open>Write mixed in pure states, pure in updates and connect updates to \<^locale>\<open>pure_o2h\<close> version.\<close>


lemma Re_Pfind_update_altdef:
  assumes "\<And>i. i<d+1 \<Longrightarrow> norm (UA i) \<le> 1"
  shows "Re (Pfind_update UA H S) = pure_o2h.Pfind' X Y d init flip empty H S UA"
proof -
  interpret pure: pure_o2h X Y d init flip bit valid empty H S UA
    by unfold_locales (auto simp add: assms)
  have B: "run_pure_B_update UA H S = selfbutter (pure.run_B)"
    unfolding run_pure_B_ell2_update 
    by (simp add: Fst_def o_def pure.run_B_def run_pure_B_ell2_def)
  show ?thesis unfolding Pfind_update_def pure.Pfind'_def B trace_selfbutter_norm trace_end_measure
    by (auto simp add: end_measure_def)    
qed


lemma Pfind_pure_update:
  "Pfind_pure UA = (\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) * Pfind_update UA H S)"
proof -
  have "Pfind_pure UA = trace_tc (\<Sum>x\<in>carrier. compose_tcr end_measure 
         (case x of (H,S,z) \<Rightarrow> complex_of_real (distr (H,S,z)) *\<^sub>C run_pure_B_tc UA H S))"
    unfolding Pfind_pure_def \<rho>right_pure_def 
    by (auto simp add:  compose_tcr.sum_right)
  also have "\<dots> = trace (\<Sum>x\<in>carrier. end_measure o\<^sub>C\<^sub>L from_trace_class
         (case x of (H,S,z) \<Rightarrow> complex_of_real (distr (H,S,z)) *\<^sub>C run_pure_B_tc UA H S))"
    unfolding trace_tc.rep_eq from_trace_class_sum compose_tcr.rep_eq by auto
  also have "\<dots> = (\<Sum>i\<in>carrier. trace (end_measure o\<^sub>C\<^sub>L from_trace_class
          (case i of (H,S,z) \<Rightarrow> complex_of_real (distr (H,S,z)) *\<^sub>C run_pure_B_tc UA H S)))" 
    by (subst trace_sum) (auto simp add: trace_class_end_measure)
  also have "\<dots> = (\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) * Pfind_update UA H S)"
    unfolding Pfind_update_def by (intro sum.cong) (auto simp add: Abs_trace_class_inverse 
        run_pure_B_ell2_update run_pure_B_update_tc scaleC_trace_class.rep_eq trace_scaleC)
  finally show ?thesis by auto
qed

lemma Pfind_pure_mixed:
  assumes "\<And>i. i < d + 1 \<Longrightarrow> finite (Rep_kraus_family (F i))"
    "\<And>i. i < d + 1 \<Longrightarrow> fst ` Rep_kraus_family (F i) \<noteq> {}"
  shows "Pfind F = (\<Sum>UA\<in>purify_comp_kraus d F. Pfind_pure UA)"
proof -
  have run: "\<rho>right F = sum \<rho>right_pure (purify_comp_kraus d F)"
    using \<rho>right_pure_mixed assms by auto
  show ?thesis unfolding Pfind_def Pfind_pure_def run 
    by (auto simp add: compose_tcr.sum_right trace_tc_sum) 
qed



text \<open>Pfind positivity\<close>

lemma Pfind_pure_pos:
  "Pfind_pure UA \<ge> 0"
proof -
  have "Pfind_pure UA = trace_tc (\<Sum>i\<in>carrier. compose_tcr end_measure (case i of (H,S,z) \<Rightarrow>
                (distr (H,S,z)) *\<^sub>C run_pure_B_tc UA H S))"
    unfolding Pfind_pure_def \<rho>right_pure_def by (auto simp add: compose_tcr.sum_right) 
  also have "\<dots> = (\<Sum>i\<in>carrier. trace_tc (compose_tcr end_measure (case i of (H,S,z) \<Rightarrow>
                (distr (H,S,z)) *\<^sub>C run_pure_B_tc UA H S)))"
    by (intro trace_tc_sum)
  also have "\<dots> = (\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) *\<^sub>C trace_tc (compose_tcr end_measure 
    (run_pure_B_tc UA H S)))"
    by (intro sum.cong, auto simp add: compose_tcr.scaleC_right trace_tc_scaleC)
  also have "\<dots> \<ge> 0" by (intro sum_nonneg) 
      (use distr_pos run_pure_B_tc_pos trace_endmeasure_pos in \<open>fastforce\<close>)
  finally show ?thesis by linarith
qed

lemma Pfind_pos: 
  "Pfind F \<ge> 0" by (simp add: Pfind_def \<rho>right_pos trace_endmeasure_pos)


text \<open>Pfind is already real\<close>

lemma Re_Pfind_update:
  "Re (Pfind_update UA H S) = Pfind_update UA H S"
  unfolding Pfind_update_def
  by (simp add: run_pure_B_ell2_update trace_end_measure)

lemma Re_Pfind_pure:
  "Re (Pfind_pure UA) = Pfind_pure UA"
  using Pfind_pure_pos complex_eq_iff less_eq_complex_def by auto

lemma Re_Pfind:
  "Re (Pfind F) = Pfind F"
  unfolding Pfind_def
  using \<rho>right_pos complex_eq_iff less_eq_complex_def trace_endmeasure_pos by force



text \<open>\<^const>\<open>Pfind\<close>, \<^const>\<open>has_sum\<close>, and \<^const>\<open>summable_on\<close> properties\<close>

lemma Pfind_abs_summable_on:
  "Pfind abs_summable_on (finite_kraus_subadv E d)"
proof -
  have "\<rho>right abs_summable_on (finite_kraus_subadv E d)" using \<rho>right_abs_summable by auto
  then obtain M where M: "sum (\<lambda>x. trace_tc (\<rho>right x)) F \<le> complex_of_real M" 
    if "F \<subseteq> finite_kraus_subadv E d" "finite F" for F
    unfolding norm_tc_pos[OF \<rho>right_pos, symmetric] of_real_sum[symmetric] 
      abs_summable_iff_bdd_above bdd_above_def
    by (metis (no_types, lifting) bdd_above_def cSUP_upper complex_of_real_mono mem_Collect_eq)
  show ?thesis 
  proof (unfold Pfind_def abs_summable_iff_bdd_above, intro bdd_aboveI[of _ M])
    fix x assume "x \<in> sum (\<lambda>x. cmod (trace_tc (compose_tcr end_measure (\<rho>right x)))) `
             {F. F \<subseteq> finite_kraus_subadv E d \<and> finite F}"
    then obtain F where assm: "F \<subseteq> finite_kraus_subadv E d" "finite F" 
      and x: "x = sum (\<lambda>x. cmod (trace_tc (compose_tcr end_measure (\<rho>right x)))) F"
      by auto
    have "x \<le> sum (\<lambda>x. norm (end_measure) * (trace_tc (\<rho>right x))) F"  
      unfolding x using cmod_trace_times' by (subst of_real_sum, intro sum_mono)
        (smt (verit, ccfv_threshold) \<rho>right_pos complex_of_real_mono norm_compose_tcr norm_tc_pos 
          of_real_mult trace_tc_norm)
    also have "\<dots> \<le> 1 * sum (\<lambda>x. trace_tc (\<rho>right x)) F" 
      by (subst sum_distrib_left[symmetric]) (meson \<rho>right_pos complex_of_real_leq_1_iff mult_right_mono 
          norm_end_measure sum_nonneg trace_tc_pos)
    also have "\<dots> \<le> M" using M[OF assm] by (simp add: trace_tc.rep_eq)
    finally show "x \<le> M" by auto
  qed
qed

lemma Pfind_summable_on:
  "Pfind summable_on (finite_kraus_subadv E d)"
  using Pfind_abs_summable_on abs_summable_summable by blast


lemma Pfind_has_sum:
  "((\<lambda>F. Pfind F) has_sum Pfind E) (finite_kraus_subadv E d)"
proof -
  have lin: "bounded_linear (\<lambda>x. trace_tc (compose_tcr end_measure x))"
    by (simp add: bounded_clinear.bounded_linear bounded_linear_compose compose_tcr.real.bounded_linear_right)
  show ?thesis unfolding Pfind_def using \<rho>right_has_sum by (auto intro!: has_sum_bounded_linear[OF lin])
qed

subsection \<open>Nontermination Part\<close>

text \<open>This introduces the non-termination part needed for pure o2h with \<^term>\<open>norm UA \<le> 1\<close>.\<close>


definition P_nonterm_update::"('x \<Rightarrow> 'y) \<Rightarrow> ('x \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 'mem update) \<Rightarrow> real" where
  "P_nonterm_update H S UA = 
  Re (trace (run_pure_B_count_update UA H S) - trace (run_pure_B_update UA H S))"

definition P_nonterm_pure::"(nat \<Rightarrow> 'mem ell2 \<Rightarrow>\<^sub>C\<^sub>L 'mem ell2) \<Rightarrow> real" where
  "P_nonterm_pure UA = Re (trace_tc (\<rho>count_pure UA) - trace_tc (\<rho>right_pure UA))"

definition P_nonterm :: "'mem kraus_adv \<Rightarrow> real" where
  "P_nonterm F = Re (trace_tc (\<rho>count F) - trace_tc (\<rho>right F))"


text \<open>Connecting mixed with pure, pure with updates and updates with \<^locale>\<open>pure_o2h\<close> version.\<close>

lemma P_nonterm_update_altdef:
  assumes "\<And>i. i<d+1 \<Longrightarrow> norm (UA i) \<le> 1"
  shows "P_nonterm_update H S UA = pure_o2h.P_nonterm X Y d init flip empty H S UA"
proof -
  interpret pure: pure_o2h X Y d init flip bit valid empty H S UA
    by unfold_locales (auto simp add: assms)
  have Bcount: "run_pure_B_count_update UA H S = selfbutter (pure.run_B_count)"
    unfolding run_pure_B_count_ell2_update 
    by (simp add: Fst_def o_def pure.run_B_count_def run_pure_B_count_ell2_def)
  have B: "run_pure_B_update UA H S = selfbutter (pure.run_B)"
    unfolding run_pure_B_ell2_update 
    by (simp add: Fst_def o_def pure.run_B_def run_pure_B_ell2_def)
  show ?thesis unfolding P_nonterm_update_def pure.P_nonterm_def Bcount B trace_selfbutter_norm
    by auto
qed


lemma P_nonterm_pure_update:
  "P_nonterm_pure UA = (\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) * P_nonterm_update H S UA)"
proof -
  have 1: "trace_tc (run_pure_B_count_tc UA a b) = trace (from_trace_class (run_pure_B_count_tc UA a b))"
    for a b by (simp add: trace_tc.rep_eq)
  have 2: "trace (from_trace_class (run_pure_B_tc UA a b)) = trace_tc (run_pure_B_tc UA a b)"
    for a b by (simp add: trace_tc.rep_eq)
  show ?thesis unfolding P_nonterm_pure_def \<rho>count_pure_def \<rho>right_pure_def P_nonterm_update_def 
    by (subst trace_tc_sum, subst trace_tc_sum) (auto simp add: case_prod_beta 
        sum_subtractf[symmetric] trace_tc_scaleC algebra_simps run_pure_B_update_tc' 
        run_pure_B_count_update_tc' 1 2 intro!: sum.cong) 
qed


lemma P_nonterm_purification:
  assumes "\<And>i. i < d + 1 \<Longrightarrow> finite (Rep_kraus_family (F i))"
    "\<And>i. i < d + 1 \<Longrightarrow> Rep_kraus_family (F i) \<noteq> {}"
  shows "P_nonterm F = (\<Sum>UA\<in>purify_comp_kraus d F. P_nonterm_pure UA)"
proof -
  have r: "\<rho>right F = sum \<rho>right_pure (purify_comp_kraus d F)"
    using \<rho>right_pure_mixed assms by auto
  have c: "\<rho>count F = sum \<rho>count_pure (purify_comp_kraus d F)"
    using \<rho>count_pure_mixed assms by auto
  show ?thesis unfolding P_nonterm_def P_nonterm_pure_def using r[symmetric] c[symmetric]
    by (auto simp add: sum_subtractf Re_sum[symmetric] trace_tc_sum[symmetric] simp del: Re_sum)
qed


text \<open>Positive error term\<close>

lemma error_term_update_pos:
  assumes "\<And>i. i<d+1 \<Longrightarrow> norm (UA i) \<le> 1"
  shows "0 \<le> (d+1) * Re (Pfind_update UA H S) + d * (P_nonterm_update H S UA)"
proof -  
  interpret pure: pure_o2h X Y d init flip bit valid empty H S UA
    by unfold_locales (auto simp add: assms)
  have "(d+1) * Re (Pfind_update UA H S) + d * (P_nonterm_update H S UA) = 
        (d+1) * (pure.Pfind') + d * (pure.P_nonterm)"
    using Re_Pfind_update_altdef P_nonterm_update_altdef assms by auto
  also have "\<dots> \<ge> 0" using pure.error_term_pos by auto
  finally show ?thesis by auto
qed 

lemma error_term_pure_pos:
  assumes "\<And>i. i<d+1 \<Longrightarrow> norm (UA i) \<le> 1"
  shows "0 \<le> (d+1) * Re (Pfind_pure UA) + d * (P_nonterm_pure UA)"
proof -
  have "(d+1) * Re (Pfind_pure UA) + d * (P_nonterm_pure UA) = (\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) * 
    ((d+1) * Re (Pfind_update UA H S) + d * (P_nonterm_update H S UA)))"
    unfolding P_nonterm_pure_update Pfind_pure_update 
    unfolding sum_distrib_left Re_sum sum.distrib[symmetric] 
    by (intro sum.cong)(auto simp add: algebra_simps)
  also have "\<dots> \<ge> 0"  by (intro sum_nonneg, use error_term_update_pos assms distr_pos' in \<open>auto\<close>)
  finally show ?thesis by auto
qed

lemma error_term_pos:
  assumes finite: "\<And>i. i < d+1 \<Longrightarrow> finite (Rep_kraus_family (F i))"
    and F_norm_id:"\<And>i. i < d+1 \<Longrightarrow> kf_bound (F i) \<le> id_cblinfun"
    and F_nonzero: "\<And>i. i < d+1 \<Longrightarrow> Rep_kraus_family (F i) \<noteq> {}"
  shows "0 \<le> (d + 1) * Re (Pfind F) + d * P_nonterm F"
proof -
  have "(d + 1) * Re (Pfind F) + d * P_nonterm F = 
    (\<Sum>UA\<in>purify_comp_kraus d F. (d+1) * Re (Pfind_pure UA)) + d * P_nonterm F"
    using assms by (subst Pfind_pure_mixed) (auto simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>UA\<in>purify_comp_kraus d F. (d+1) * Re (Pfind_pure UA) + d * (P_nonterm_pure UA))"
    using assms by (subst P_nonterm_purification) (auto simp add: sum_distrib_left)
  also have "\<dots> \<ge> 0" by (intro sum_nonneg) 
      (use error_term_pure_pos norm_in_purify_comp_kraus[where n=d] assms in \<open>auto\<close>)
  finally show ?thesis by auto
qed



text \<open>has sum property\<close>

lemma P_nonterm_has_sum:
  "((\<lambda>F. P_nonterm F) has_sum P_nonterm E) (finite_kraus_subadv E d)"
proof -
  have lin: "bounded_linear (\<lambda>x. trace_tc x)"
    by (simp add: bounded_clinear.bounded_linear)
  show ?thesis unfolding P_nonterm_def using \<rho>right_has_sum \<rho>count_has_sum 
    by (auto intro!: has_sum_Re has_sum_diff has_sum_bounded_linear[OF lin])
qed




section \<open>Proof of Mixed O2H\<close>
text \<open>We prove the mixed O2H in several steps.\<close>

text \<open>Step 1: Connect the updates version to the \<open>pure_o2h\<close> lemma\<close>

lemma estimate_Pfind_update_sqrt:
  fixes UA H S
  assumes "\<And>i. i<d+1 \<Longrightarrow> norm (UA i) \<le> 1"
    and norm_Q: "norm Q \<le> 1"
  shows "\<bar>sqrt (Re (PM_update Q ((run_pure_A_update UA H) \<otimes>\<^sub>o (selfbutter (ket empty))))) - 
        sqrt (Re (PM_update Q (run_pure_B_update UA H S)))\<bar> 
     \<le> sqrt ((d+1) * Re (Pfind_update UA H S) + d * P_nonterm_update H S UA)"
proof -
  interpret pure: pure_o2h X Y d init flip bit valid empty H S UA 
    by unfold_locales (auto simp add: assms)
  have pure_A: "run_pure_A_ell2 UA H = pure.run_A" 
    unfolding pure.run_A_def run_pure_A_ell2_def by auto
  have pure_B: "run_pure_B_ell2 UA H S = pure.run_B"
    unfolding pure.run_B_def run_pure_B_ell2_def Fst_def comp_def by auto
  have pure_find: "Pfind_update UA H S = pure.Pfind'"
    unfolding Pfind_update_def pure.Pfind'_def end_measure_def[symmetric] 
    unfolding run_pure_B_ell2_update pure_B using trace_end_measure by auto
  have 1: "\<bar>sqrt (Re (PM_update Q (run_pure_A_update UA H \<otimes>\<^sub>o selfbutter (ket empty)))) - 
      sqrt (Re (PM_update Q (run_pure_B_update UA H S)))\<bar> =
    \<bar>sqrt (Re (trace (sandwich Q (selfbutter (run_pure_A_ell2 UA H \<otimes>\<^sub>s ket empty))))) - 
     sqrt (Re (trace (sandwich Q (selfbutter (run_pure_B_ell2 UA H S)))))\<bar>"
    unfolding PM_update_def by (simp add: run_pure_A_ell2_update run_pure_B_ell2_update 
        tensor_butterfly)
  also have 2: "\<dots> = \<bar>sqrt (Re (trace (selfbutter (Q *\<^sub>V (run_pure_A_ell2 UA H \<otimes>\<^sub>s ket empty))))) - 
     sqrt (Re (trace (selfbutter (Q *\<^sub>V (run_pure_B_ell2 UA H S)))))\<bar>"
    by (simp add: selfbutter_sandwich)
  also have 3: "\<dots> = \<bar>(norm (Q *\<^sub>V (run_pure_A_ell2 UA H \<otimes>\<^sub>s ket empty))) - 
     norm (Q *\<^sub>V (run_pure_B_ell2 UA H S))\<bar>"
    unfolding trace_butterfly power2_norm_eq_cinner[symmetric] by (simp add: norm_power)
  also have 5: "\<dots> \<le> norm (Q *\<^sub>V (run_pure_A_ell2 UA H \<otimes>\<^sub>s ket empty) - 
     Q *\<^sub>V (run_pure_B_ell2 UA H S))" by (simp add: norm_triangle_ineq3) 
  also have "\<dots> = norm (Q *\<^sub>V (run_pure_A_ell2 UA H \<otimes>\<^sub>s ket empty - run_pure_B_ell2 UA H S))" 
    by (subst cblinfun.diff_right) auto
  also have "\<dots> \<le> norm (Q::('mem\<times>'l)update) * 
    norm (run_pure_A_ell2 UA H \<otimes>\<^sub>s ket empty - run_pure_B_ell2 UA H S)" 
    by (rule norm_cblinfun)
  also have "\<dots> \<le> norm (run_pure_A_ell2 UA H \<otimes>\<^sub>s ket empty - run_pure_B_ell2 UA H S)"
    using norm_Q by (metis mult_le_cancel_right2 norm_not_less_zero)
  also have "\<dots> \<le> (sqrt (real (d + 1) * pure.Pfind' + real d * pure.P_nonterm))"
    unfolding pure_A pure_B using pure.pure_o2h_sqrt by auto
  also have "\<dots> \<le> sqrt ((d+1) * Re (Pfind_update UA H S) + d * pure.P_nonterm)" 
    unfolding pure_find by simp
  also have "\<dots> \<le> sqrt ((d + 1) * Re (Pfind_update UA H S) + (d * P_nonterm_update H S UA))"
    by (subst P_nonterm_update_altdef[OF assms(1)], auto)
  finally show ?thesis  using "1" "2" "3" "5" by linarith
qed



lemma estimate_Pfind_tc_sqrt:
  fixes UA H S
  assumes "\<And>i. i<d+1 \<Longrightarrow> norm (UA i) \<le> 1" "norm Q \<le> 1"
  shows "\<bar>sqrt (Re (PM Q (tc_tensor (run_pure_A_tc UA H) empty_tc))) - 
        sqrt (Re (PM Q (run_pure_B_tc UA H S)))\<bar> 
     \<le> sqrt ((d+1) * Re (Pfind_update UA H S) + d * (P_nonterm_update H S UA))"
  using estimate_Pfind_update_sqrt[OF assms] unfolding empty_tc_def
  by (smt (verit) PM_def assms(1) assms(2) from_trace_class_inverse estimate_Pfind_update_sqrt 
      run_pure_B_tc_def run_pure_B_update_def o_def run_pure_A_tc_def run_pure_A_update_def 
      run_pure_adv_update_tc' tc_butterfly.rep_eq tc_tensor.rep_eq)


text \<open>Step 2: Connect the pure version with the update version by summation over 
the distribution of H and S\<close>

lemma estimate_Pfind_pure_sqrt:
  fixes UA
  assumes "\<And>i. i<d+1 \<Longrightarrow> norm (UA i) \<le> 1" "norm Q \<le> 1"
  shows "\<bar>sqrt (Re (PM Q (tc_tensor (\<rho>left_pure UA) empty_tc))) - sqrt (Re (PM Q (\<rho>right_pure UA)))\<bar>
 \<le> sqrt (real (d + 1) * Re (Pfind_pure UA) + d * P_nonterm_pure UA)"
proof -
  let ?PMA = "(\<lambda>H. PM Q (tc_tensor (run_pure_A_tc UA H) empty_tc))"
  let ?PMB = "(\<lambda>H S. PM Q (run_pure_B_tc UA H S))"
  have "\<bar>sqrt (Re (PM Q (tc_tensor (\<rho>left_pure UA) empty_tc))) - sqrt (Re (PM Q (\<rho>right_pure UA)))\<bar> = 
    \<bar>sqrt (\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) * Re (?PMA H)) - 
     sqrt (\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) * Re (?PMB H S))\<bar>"
  proof -
    have zeroA: "0 \<le> tc_tensor (run_pure_A_tc UA H) empty_tc" for H 
      by (intro tc_tensor_pos[OF run_pure_A_tc_pos empty_tc_pos])
    have "Re (PM Q (tc_tensor (\<rho>left_pure UA) empty_tc)) = Re (PM Q (\<Sum>i\<in>carrier.
         (distr i) *\<^sub>C tc_tensor (run_pure_A_tc UA (fst i)) empty_tc))"
      unfolding \<rho>left_pure_def 
      by (auto simp add: tc_tensor_scaleC_left tc_tensor_sum_left case_prod_beta)
    also have "\<dots> = Re (\<Sum>x\<in>carrier. (distr x) * PM Q (tc_tensor (run_pure_A_tc UA (fst x)) empty_tc))"
      by (subst PM_sum_distr)+ (auto simp add: prod.case_distrib comp_def PM_scale algebra_simps)
    also have "\<dots> = (\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) * Re (?PMA H))"
      by (subst Re_sum) 
        (auto simp add: distr_pos' PM_pos[OF zeroA] norm_mult algebra_simps intro!: sum.cong )
    finally have 1: "Re (PM Q (tc_tensor (\<rho>left_pure UA) empty_tc)) = 
      (\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) * Re (?PMA H))" by auto
    have "Re (PM Q (\<rho>right_pure UA)) = Re (PM Q (\<Sum>i\<in>carrier. (distr i) *\<^sub>C run_pure_B_tc UA (fst i) (fst (snd i))))"
      unfolding \<rho>right_pure_def 
      by (auto simp add: tc_tensor_scaleC_left tc_tensor_sum_left case_prod_beta)
    also have "\<dots> = Re (\<Sum>x\<in>carrier. (distr x) * PM Q (run_pure_B_tc UA (fst x) (fst (snd x))))"
      by (subst PM_sum_distr)+ (auto simp add: prod.case_distrib comp_def PM_scale algebra_simps)
    also have "\<dots> = (\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) * Re (?PMB H S))"
      by (subst Re_sum) (auto simp add: distr_pos' PM_pos[OF run_pure_B_tc_pos] 
          norm_mult algebra_simps intro!: sum.cong )
    finally have 2: "Re (PM Q (\<rho>right_pure UA)) = (\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) * Re (?PMB H S))" 
      by auto
    show ?thesis unfolding 1 2 by auto
  qed
  also have "\<dots> \<le> sqrt (\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) * 
    ((d+1) * Re (Pfind_update UA H S) + d * (P_nonterm_update H S UA))) "
  proof -
    have ass1: "\<forall>x\<in>carrier. 0 \<le> (case x of (H,S,z) \<Rightarrow> Re (?PMA H))" 
      by (metis (mono_tags, lifting) PM_pos cmod_Re empty_tc_pos norm_ge_zero prod.case_eq_if 
          run_pure_A_tc_pos tc_tensor_pos)
    have ass2: "\<forall>x\<in>carrier. 0 \<le> (case x of (H,S,z) \<Rightarrow> Re (?PMB H S))" 
      by (metis (mono_tags, lifting) PM_pos cmod_Re norm_ge_zero prod.case_eq_if run_pure_B_tc_pos)
    have ass3: "\<forall>x\<in>carrier. 0 \<le> (case x of (H,S,z) \<Rightarrow> (d + 1) * Re (Pfind_update UA H S) + 
      d * (P_nonterm_update H S UA))"
      using assms(1) error_term_update_pos by auto
    have ass4: "\<forall>x\<in>carrier. 0 \<le> distr x" using distr_pos by fastforce
    have ass5: "\<forall>x\<in>carrier. \<bar>sqrt (case x of (H,S,z) \<Rightarrow> Re (?PMA H)) -
      sqrt (case x of (H,S,z) \<Rightarrow> Re (?PMB H S))\<bar>
     \<le> sqrt (case x of (H,S,z) \<Rightarrow> real (d + 1) * Re (Pfind_update UA H S) + d * (P_nonterm_update H S UA))"
      using estimate_Pfind_tc_sqrt[OF assms] by auto
    have rew_sum1: 
      "(\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) * Re (?PMA H)) = 
       (\<Sum>x\<in>carrier. distr x * (case x of (H,S,z) \<Rightarrow> Re (?PMA H)))"
      by (auto intro: sum.cong)
    have rew_sum2: "(\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) * Re (?PMB H S)) =
       (\<Sum>x\<in>carrier. distr x * (case x of (H,S,z) \<Rightarrow> Re (?PMB H S)))" by (auto intro: sum.cong)
    have rew_sum3: "(\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) * 
        (real (d + 1) * Re (Pfind_update UA H S) + d * (P_nonterm_update H S UA))) = 
      (\<Sum>x\<in>carrier. distr x * (case x of (H,S,z) \<Rightarrow> real (d + 1) * Re (Pfind_update UA H S) +
        real d * (P_nonterm_update H S UA)))" by (auto intro!: sum.cong)
    show ?thesis by (unfold rew_sum1 rew_sum2 rew_sum3)
        (rule sqrt_estimate_real[OF finite_carrier ass1 ass2 ass3 ass4 ass5])
  qed
  also have "\<dots> \<le> sqrt (real (d + 1) * Re (Pfind_pure UA) + d * P_nonterm_pure UA)"
  proof -
    have "(\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) * ((d + 1) * Re (Pfind_update UA H S) +
         d * P_nonterm_update H S UA)) = (\<Sum>(H,S,z)\<in>carrier. 
        (d + 1) * distr (H,S,z) * Re (Pfind_update UA H S)) + (\<Sum>(H,S,z)\<in>carrier. 
         d * distr (H,S,z) * P_nonterm_update H S UA)"
      by (subst sum.distrib[symmetric], intro sum.cong) (auto simp add: algebra_simps)
    also have "\<dots> = (d + 1) * Re ((\<Sum>(H,S,z)\<in>carrier. distr (H,S,z) * Pfind_update UA H S)) + 
      d * (\<Sum>(H,S,z)\<in>carrier.  distr (H,S,z) * P_nonterm_update H S UA)"
    proof (subst Re_sum, goal_cases)
      case 1
      have 1: "(\<Sum>(H,S,z)\<in>carrier. (d + 1) * distr (H,S,z) * Re (Pfind_update UA H S)) = 
        (d + 1) * (\<Sum>(H,S,z)\<in>carrier. Re ((distr (H,S,z)) * Pfind_update UA H S))" 
        by (auto simp add: sum_distrib_left distr_pos' norm_mult intro!: sum.cong)
      then show ?case unfolding 1 by (auto simp add: sum_distrib_left prod.case_eq_if 
            intro!: sum.cong) 
    qed
    also have "\<dots> \<le> (d + 1) * Re (Pfind_pure UA) + d * (P_nonterm_pure UA)"
      unfolding Pfind_pure_update using P_nonterm_pure_update d_gr_0 by auto 
    finally show ?thesis by auto
  qed 
  finally show ?thesis by auto
qed


text \<open>Step 3: prove the mixed O2H only for finite kraus maps using the pure version\<close>


lemma estimate_Pfind_finite_sqrt:
  assumes finite: "\<And>i. i < d+1 \<Longrightarrow> finite (Rep_kraus_family (F i))"
    and F_norm_id:"\<And>i. i < d+1 \<Longrightarrow> kf_bound (F i) \<le> id_cblinfun"
    and F_nonzero: "\<And>i. i < d+1 \<Longrightarrow> Rep_kraus_family (F i) \<noteq> {}"
    and norm_Q: "norm Q \<le> 1"
  shows "\<bar>csqrt (PM Q (tc_tensor (\<rho>left F) empty_tc)) - csqrt (PM Q (\<rho>right F))\<bar> \<le> 
  csqrt ((d+1) * Pfind F + d * P_nonterm F)"
proof -
  let ?PMleft = "(\<lambda>UA. PM Q (tc_tensor (\<rho>left_pure UA) empty_tc))"
  let ?PMright = "(\<lambda>UA. PM Q (\<rho>right_pure UA))"
  define I :: "(nat \<Rightarrow> 'mem update) set" where "I = purify_comp_kraus d F"
  have "finite I" unfolding I_def using comp_kraus_maps_set_finite assms by auto
  have norm_UA: "\<And>i. i<d+1 \<Longrightarrow> norm (UA i) \<le> 1" if "UA\<in>I" for UA 
    by (intro norm_in_purify_comp_kraus) (use that F_norm_id in \<open>auto simp add: I_def\<close>)
  have A: "PM Q (tc_tensor (\<rho>left F) empty_tc) = (\<Sum>UA\<in>I. ?PMleft UA)" unfolding I_def
    by (subst \<rho>left_pure_mixed) (auto simp add: tc_tensor_sum_left PM_sum_distr assms)
  have B: "PM Q (\<rho>right F) = (\<Sum>UA\<in>I. ?PMright UA)" unfolding I_def
    by (subst \<rho>right_pure_mixed) (auto simp add: PM_sum_distr assms)
  have find: "(d + 1) * (Pfind F) = (\<Sum>UA\<in>I. (d + 1) * Pfind_pure UA)" unfolding I_def
    by (subst Pfind_pure_mixed) (auto simp add: sum_distrib_left assms)
  have nonterm: "d * (P_nonterm F) = (\<Sum>UA\<in>I. d * P_nonterm_pure UA)" unfolding I_def
    by (subst P_nonterm_purification) (auto simp add: sum_distrib_left assms)
  have A_pos: "0 \<le> tc_tensor (\<rho>left F) empty_tc" using \<rho>left_pos
    by (simp add: empty_tc_pos tc_tensor_pos)
  have PMleft_pos: "?PMleft UA \<ge> 0" for UA 
    by (auto intro!: PM_pos simp add: empty_tc_pos tc_tensor_pos \<rho>left_pure_pos)
  have PMright_pos: "?PMright UA \<ge> 0" for UA by (auto intro!: PM_pos simp add: \<rho>right_pure_pos)
  have "\<bar>csqrt (PM Q (tc_tensor (\<rho>left F) empty_tc)) - csqrt (PM Q (\<rho>right F))\<bar> = 
        \<bar>csqrt (Re (PM Q (tc_tensor (\<rho>left F) empty_tc))) - csqrt (Re (PM Q (\<rho>right F)))\<bar>"
    by (subst PM_Re[OF A_pos], subst PM_Re[OF \<rho>right_pos]) auto
  also have "\<dots> = \<bar>sqrt (Re (PM Q (tc_tensor (\<rho>left F) empty_tc))) - sqrt (Re (PM Q (\<rho>right F)))\<bar>"
    using complex_of_real_abs A_pos PM_pos \<rho>right_pos less_eq_complex_def by force
  also have "\<dots> = \<bar>sqrt ((\<Sum>UA\<in>I. Re (?PMleft UA))) -  sqrt ((\<Sum>UA\<in>I. Re (?PMright UA)))\<bar>"
    unfolding A B by (subst Re_sum, subst Re_sum) auto
  also have "\<dots> \<le> sqrt (\<Sum>UA\<in>I. (d+1) * Re (Pfind_pure UA) + d * P_nonterm_pure UA)"
  proof -
    have 1: "\<forall>UA\<in>I. 0 \<le> Re (?PMleft UA)" using PMleft_pos by (simp add: less_eq_complex_def)
    have 2: "\<forall>UA\<in>I. 0 \<le> Re (?PMright UA)" using PMright_pos by (metis cmod_Re norm_ge_zero)
    have 3: "\<forall>UA\<in>I. 0 \<le> real (d + 1) * Re (Pfind_pure UA) + d * P_nonterm_pure UA" 
      using error_term_pure_pos norm_UA by auto 
    have 4: "\<forall>UA\<in>I. 0 \<le> (1::real)" by auto
    have 5: "\<forall>UA\<in>I. 
      \<bar>sqrt (Re (PM Q (tc_tensor (\<rho>left_pure UA) empty_tc))) - sqrt (Re (PM Q (\<rho>right_pure UA)))\<bar>
      \<le> sqrt (real (d + 1) * Re (Pfind_pure UA) + d * P_nonterm_pure UA)"
      using estimate_Pfind_pure_sqrt norm_UA norm_Q by auto
    have "\<bar>sqrt ((\<Sum>UA\<in>I. Re (?PMleft UA))) -  sqrt ((\<Sum>UA\<in>I. Re (?PMright UA)))\<bar>
      \<le> sqrt (\<Sum>UA\<in>I. ((d+1) * Re (Pfind_pure UA) + d * P_nonterm_pure UA))"
      using sqrt_estimate_real[OF \<open>finite I\<close> 1 2 3 4 5] by auto
    then show ?thesis by (auto intro!: complex_of_real_mono)
  qed
  also have "\<dots> = csqrt (\<Sum>UA\<in>I. (d+1) * (Pfind_pure UA) + d * P_nonterm_pure UA)"
  proof (subst of_real_sqrt, goal_cases)
    case 1 then show ?case by (intro sum_nonneg) (use error_term_pure_pos norm_UA in \<open>auto\<close>)
  next
    case 2
    have *: "complex_of_real (real (d + 1) * Re (Pfind_pure x) + real d * P_nonterm_pure x) = 
      complex_of_nat (d + 1) * Pfind_pure x + complex_of_real (real d * P_nonterm_pure x)" for x
      by (simp add: Re_Pfind_pure)
    then show ?case by (subst of_real_sum, subst *) auto
  qed
  also have "\<dots> = csqrt ((\<Sum>UA\<in>I. (d+1) * Pfind_pure UA) + (\<Sum>UA\<in>I. d * P_nonterm_pure UA))"
    by (simp)
  finally show ?thesis by (subst find, subst nonterm) auto
qed

lemma estimate_Pfind_finite_sqrt':
  assumes finite: "\<And>i. i < d+1 \<Longrightarrow> finite (Rep_kraus_family (F i))"
    and F_norm_id:"\<And>i. i < d+1 \<Longrightarrow> kf_bound (F i) \<le> id_cblinfun"
    and F_nonzero: "\<And>i. i < d+1 \<Longrightarrow> Rep_kraus_family (F i) \<noteq> {}"
    and norm_Q: "norm Q \<le> 1"
  shows "\<bar>sqrt (Re (PM Q (tc_tensor (\<rho>left F) empty_tc))) - sqrt (Re (PM Q (\<rho>right F)))\<bar> \<le> 
  sqrt ((d+1) * Re (Pfind F) + d * P_nonterm F)"
proof -
  let ?f = "PM Q (tc_tensor (\<rho>left F) empty_tc)"
  have rew1: "sqrt (Re (?f)) = csqrt (?f)" 
    by (metis PM_Re PM_pos \<rho>left_pos complex_of_real_nn_iff empty_tc_pos of_real_sqrt tc_tensor_pos)
  have rew2: "sqrt (Re (PM Q (\<rho>right F))) = csqrt (PM Q (\<rho>right F))"
    using PM_pos \<rho>right_pos less_eq_complex_def by auto
  have pos: "0 \<le> real (d + 1) * Re (Pfind F) + real d * P_nonterm F"
    using error_term_pos assms by auto
  have rew3: "complex_of_real (sqrt (real (d + 1) * Re (Pfind F) + real d * P_nonterm F)) = 
       csqrt (real (d + 1) * (Pfind F) + real d * P_nonterm F)"
    by (subst of_real_sqrt[OF pos]) (auto simp add: error_term_pos Re_Pfind) 
  show ?thesis apply (subst complex_of_real_mono_iff[symmetric], subst complex_of_real_abs)
    apply (subst of_real_diff, subst rew1, subst rew2, subst rew3) 
    by (use estimate_Pfind_finite_sqrt[OF assms] in \<open>auto\<close>)
qed


text \<open>Step 4: Prove the mixed O2H for possibly infinite kraus maps using a limit process from 
  finite to infinite kraus maps\<close>



lemma Re_Pfind_has_sum:
  "((\<lambda>F. (1 + real d) * Re (Pfind F)) has_sum (1 + real d) * Re (Pfind E)) (finite_kraus_subadv E d)"
  using has_sum_cmult_right[OF Re_has_sum[OF Pfind_has_sum]] Pfind_pos
  by (auto simp add: o_def)

lemma scale_P_nonterm_has_sum:
  "((\<lambda>F. real d * P_nonterm F) has_sum real d * P_nonterm E) (finite_kraus_subadv E d)"
  using P_nonterm_has_sum has_sum_cmult_right by blast






lemma estimate_Pfind_sqrt:
  assumes norm_Q: "norm Q \<le> 1"
  shows "\<bar>sqrt (Pleft' Q) - sqrt (Pright Q)\<bar> \<le> 
  sqrt ((d+1) * Re (Pfind E) + d * P_nonterm E)"
    (is "?left \<le> ?right")
proof -
  have not_bot: "finite_subsets_at_top (finite_kraus_subadv E d) \<noteq> \<bottom>" by auto
  let ?f = "(\<lambda>\<FF>. sqrt (sum (\<lambda>F. (d+1) * (Re (Pfind F)) + d * (P_nonterm F)) \<FF>))"
  have tendsto_right: "(?f \<longlongrightarrow> sqrt (real (d + 1) * Re (Pfind E) + real d * P_nonterm E))
     (finite_subsets_at_top (finite_kraus_subadv E d))" 
    using Re_Pfind_has_sum scale_P_nonterm_has_sum unfolding has_sum_def
    by (auto intro!: tendsto_real_sqrt tendsto_add tendsto_mult_left tendsto_Re)
  let ?g = "(\<lambda>\<FF>. \<bar>sqrt (sum (\<lambda>F. Re (PM Q (tc_tensor (\<rho>left F) empty_tc))) \<FF>) - 
    sqrt (sum (\<lambda>F. Re (PM Q (\<rho>right F))) \<FF>)\<bar>)"
  have tendsto_left: 
    "(?g \<longlongrightarrow> \<bar>sqrt (Pleft' Q) - sqrt (Pright Q)\<bar>)
     (finite_subsets_at_top (finite_kraus_subadv E d))"
    using Re_PM_left_has_sum Re_PM_right_has_sum unfolding has_sum_def 
    by (auto intro!: tendsto_rabs tendsto_real_sqrt tendsto_diff)
  have eventually: "\<forall>\<^sub>F x in finite_subsets_at_top (finite_kraus_subadv E d).
       \<bar>sqrt (\<Sum>F\<in>x. Re (PM Q (tc_tensor (\<rho>left F) empty_tc))) - sqrt (\<Sum>F\<in>x. Re (PM Q (\<rho>right F)))\<bar>
       \<le> sqrt (\<Sum>F\<in>x. real (d + 1) * Re (Pfind F) + real d * P_nonterm F)"
  proof (intro eventually_finite_subsets_at_top_weakI, goal_cases)
    case (1 G)
    have fin_case: "\<bar>sqrt (Re (PM Q (tc_tensor (\<rho>left F) empty_tc))) - sqrt (Re (PM Q (\<rho>right F)))\<bar>
         \<le> sqrt (real(d+1) * Re (Pfind F) + real d * P_nonterm F)"
      if "F\<in>G" for F proof (intro estimate_Pfind_finite_sqrt'[OF _ _ _ norm_Q], goal_cases)
      case (1 i)
      have "F \<in> finite_kraus_subadv E d" using \<open>G \<subseteq> finite_kraus_subadv E d\<close> that by auto
      then show ?case using fin_subadv_fin_Rep_kraus_family 1 by auto
    next
      case (2 i)
      have "kf_bound (F i) \<le> kf_bound (E i)" 
        by (meson "1"(2) "2" Set.basic_monos(7) finite_kraus_subadv_I kf_bound_of_elems that)
      also have "kf_bound (E i) \<le> id_cblinfun" using "2" E_norm_id by auto
      finally show ?case by linarith
    next
      case (3 i)
      then show ?case using "1"(2) fin_subadv_nonzero[where n=d] that by auto
    qed 
    then have "\<bar>sqrt (\<Sum>F\<in>G. 1 * (Re (PM Q (tc_tensor (\<rho>left F) empty_tc)))) - 
       sqrt (\<Sum>F\<in>G. 1 * (Re (PM Q (\<rho>right F))))\<bar>
    \<le> sqrt (\<Sum>F\<in>G. 1 * (real (d + 1) * Re (Pfind F) + real d * P_nonterm F))"
    proof (intro sqrt_estimate_real[OF 1(1)], goal_cases)
      case 3
      then show ?case using error_term_pos by (smt (verit, best) real_sqrt_ge_0_iff)
    qed (auto intro!: Re_PM_pos \<rho>right_pos tc_tensor_pos empty_tc_pos \<rho>left_pos)
    then show ?case by auto
  qed
  show ?thesis by (intro tendsto_le[OF not_bot tendsto_right tendsto_left eventually])
qed



lemma estimate_Pfind:
  assumes norm_Q: "norm Q \<le> 1"
  shows
    "\<bar>Pleft' Q - Pright Q\<bar> \<le>  2 * sqrt ((d+1) * Re (Pfind E) + d* P_nonterm E)"
proof - 
  have sqrt: 
    "\<bar>sqrt (Pleft' Q) - sqrt (Pright Q)\<bar> \<le> sqrt ((d+1) * Re (Pfind E) + d* P_nonterm E)"
    using estimate_Pfind_sqrt assms norm_Fst_P by auto
  have "\<bar>(Pleft' Q) - (Pright Q)\<bar> = \<bar>sqrt (Pleft' Q) - sqrt (Pright Q)\<bar> * 
    \<bar>sqrt (Pleft' Q) + sqrt (Pright Q)\<bar>"
    unfolding Pleft'_def Pright_def
    by (auto intro!: sqrt_binom Re_PM_pos \<rho>right_pos tc_tensor_pos \<rho>left_pos empty_tc_pos)
  also have "\<dots> \<le> 2 * \<bar>sqrt (Pleft' Q) - sqrt (Pright Q)\<bar>"
  proof -
    have "norm (PM Q(tc_tensor (\<rho>left E) empty_tc)) \<le> trace_norm (sandwich Q *\<^sub>V
        from_trace_class (tc_tensor (\<rho>left E) empty_tc))"  unfolding PM_def PM_update_def by auto
    also have "\<dots> \<le> (norm (Q :: ('mem \<times> 'l) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('mem \<times> 'l) ell2))^2 * 
      trace_norm (from_trace_class (tc_tensor (\<rho>left E) empty_tc))"
      using trace_norm_sandwich[of "from_trace_class (tc_tensor (\<rho>left E) empty_tc)" "Q",
          OF trace_class_from_trace_class] by auto 
    also have "\<dots> \<le> 1 * norm (tc_tensor (\<rho>left E) empty_tc)" 
      by (smt (verit, ccfv_SIG) norm_Q mult_le_cancel_right2 norm_ge_zero norm_trace_class.rep_eq 
          power2_eq_square)
    also have "\<dots> = norm (\<rho>left E)" unfolding norm_tc_tensor norm_empty_tc by auto
    have "norm (PM Q(tc_tensor (\<rho>left E) empty_tc)) \<le> 1"
      by (intro norm_PM, unfold norm_tc_tensor) (auto simp add: norm_\<rho>left norm_empty_tc norm_Q) 
    then have left: "norm (sqrt (Pleft' Q)) \<le> 1"
      by (simp add: Pleft'_def PM_pos Re_PM_pos \<rho>left_pos cmod_Re empty_tc_pos tc_tensor_pos)
    have "norm (PM Q(\<rho>right E)) \<le> 1" 
      by (intro norm_PM) (auto simp add: norm_\<rho>right norm_Q)
    then have right: "norm (sqrt(Pright Q)) \<le> 1" 
      by (simp add: Pright_def PM_pos Re_PM_pos \<rho>right_pos cmod_Re)
    have "\<bar>sqrt (Pleft' Q) + sqrt (Pright Q)\<bar> \<le> 2"
      using left right by auto
    then show ?thesis by (subst mult.commute[of 2], intro mult_left_mono) auto
  qed
  finally show "\<bar>Pleft' Q - Pright Q\<bar> \<le> 2 * sqrt ((d+1) * Re (Pfind E) + d* P_nonterm E)" 
    using sqrt by auto
qed

end
end