(*
   File:    Incomplete_Gamma_Lemma_Bucket.thy
   Author:  Manuel Eberl, University of Innsbruck
*)
section \<open>Auxiliary material\<close>
theory Incomplete_Gamma_Lemma_Bucket
  imports
  "HOL-Complex_Analysis.Complex_Analysis"
  Safe_Power
  More_Dominated_Convergence
  Derivative_Method
begin

lemma sgn_sqrt [simp]: "sgn (sqrt x) = sgn x"
  by (auto simp: sgn_if)

(* TODO Move *)
lemma countably_generated_imp_convergent_sequence:
  assumes "countably_generated_filter F" "F \<noteq> bot"
  obtains X where "filterlim X F sequentially"
proof -
  obtain B where B: "antimono_on UNIV B" "\<And>P. eventually P F = (\<exists>i::nat. \<forall>x\<in>B i. P x)"
    using countably_generated_filter_iff_decseq[of F] assms by blast
  have "B i \<noteq> {}" for i
    using B(2)[of "\<lambda>_. False"] assms by (auto simp: trivial_limit_def)
  hence "\<forall>i. \<exists>x. x \<in> B i"
    by blast
  then obtain X where X: "X i \<in> B i" for i
    by metis
  have "filterlim X F sequentially"
    unfolding filterlim_def le_filter_def eventually_filtermap
  proof safe
    fix P assume "eventually P F"
    with B obtain i where i: "\<forall>x\<in>B i. P x"
      by blast
    hence "P (X j)" if j: "j \<ge> i" for j
      using monotone_onD[OF B(1) _ _ j] X[of j] by auto
    thus "eventually (\<lambda>j. P (X j)) sequentially"
      by (auto simp: eventually_at_top_linorder)
  qed
  thus ?thesis
    by (rule that)
qed

(* TODO Move *)
lemma (in sequential_filter) dominated_convergence':
  fixes f :: "'a \<Rightarrow> 'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes f: "eventually (\<lambda>k. (f k) integrable_on S) F" and h: "h integrable_on S"
    and le: "eventually (\<lambda>k. \<forall>x\<in>S. norm (f k x) \<le> h x) F"
    and conv: "\<And>x. x \<in> S \<Longrightarrow> ((\<lambda>k. f k x) \<longlongrightarrow> g x) F"
  shows "((\<lambda>k. integral S (f k)) \<longlongrightarrow> integral S g) F"
proof (rule filterlim_sequentially_imp_filterlim)
  fix X assume X: "filterlim X F sequentially"
  have "eventually (\<lambda>k. (\<forall>x\<in>S. norm (f k x) \<le> h x) \<and> f k integrable_on S) F"
    using f le by eventually_elim auto
  hence "eventually (\<lambda>k. (\<forall>x\<in>S. norm (f (X k) x) \<le> h x) \<and> f (X k) integrable_on S) sequentially"
    by (rule eventually_compose_filterlim) fact
  then obtain N where N: "\<And>k. k \<ge> N \<Longrightarrow> (\<forall>x\<in>S. norm (f (X k) x) \<le> h x) \<and> f (X k) integrable_on S"
    by (auto simp: eventually_at_top_linorder)
  define X' where "X' = X \<circ> ((+) N)"
  have X': "\<forall>x\<in>S. norm (f (X' k) x) \<le> h x" "f (X' k) integrable_on S" for k
    using N[of "N + k"] by (simp_all add: X'_def)
  have lim_X': "filterlim X' F sequentially" unfolding X'_def o_def
    by (rule filterlim_compose[OF X]) 
       (use filterlim_add_const_nat_at_top[of N] in \<open>simp_all add: add_ac\<close>)

  have "(\<lambda>n. integral S (f (X' n))) \<longlonglongrightarrow> integral S g"
  proof (rule dominated_convergence)
    show "h integrable_on S"
      by fact
    show "f (X' n) integrable_on S" for n
      by (rule X')
    show "norm (f (X' k) x) \<le> h x" if "x \<in> S" for x k
      using X'[of k] that by auto
    show "(\<lambda>n. f (X' n) x) \<longlonglongrightarrow> g x" if "x \<in> S" for x
      by (rule filterlim_compose[OF conv lim_X']) fact
  qed
  hence "(\<lambda>n. integral S (f (X' (n - N)))) \<longlonglongrightarrow> integral S g"
    by (rule filterlim_compose) (rule filterlim_minus_const_nat_at_top)
  also have "?this \<longleftrightarrow> (\<lambda>n. integral S (f (X n))) \<longlonglongrightarrow> integral S g"
  proof (rule filterlim_cong)
    show "eventually (\<lambda>n. integral S (f (X' (n - N))) = integral S (f (X n))) at_top"
      using eventually_ge_at_top[of N] by eventually_elim (auto simp: X'_def)
  qed auto
  finally show "(\<lambda>n. integral S (f (X n))) \<longlonglongrightarrow> integral S g" .
qed

(* TODO Move *)
lemma dominated_convergence_countably_generated_filter:
  fixes f :: "'a \<Rightarrow> 'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes cg: "countably_generated_filter F"
  assumes f: "eventually (\<lambda>k. (f k) integrable_on S) F" and h: "h integrable_on S"
    and le: "eventually (\<lambda>k. \<forall>x\<in>S. norm (f k x) \<le> h x) F"
    and conv: "\<And>x. x \<in> S \<Longrightarrow> ((\<lambda>k. f k x) \<longlongrightarrow> g x) F"
  shows "F \<noteq> bot \<Longrightarrow> g integrable_on S" "((\<lambda>k. integral S (f k)) \<longlongrightarrow> integral S g) F"
proof -
  interpret sequential_filter F
    by (rule countably_generated_filter_imp_sequential_filter) fact
  show "((\<lambda>k. integral S (f k)) \<longlongrightarrow> integral S g) F"
    using f h le conv by (rule dominated_convergence')

  assume "F \<noteq> bot"
  with cg obtain X where X: "filterlim X F sequentially"
    using countably_generated_imp_convergent_sequence by blast
  have "eventually (\<lambda>k. (\<forall>x\<in>S. norm (f k x) \<le> h x) \<and> f k integrable_on S) F"
    using f le by eventually_elim auto
  hence "eventually (\<lambda>k. (\<forall>x\<in>S. norm (f (X k) x) \<le> h x) \<and> f (X k) integrable_on S) sequentially"
    by (rule eventually_compose_filterlim) fact
  then obtain N where N: "\<And>k. k \<ge> N \<Longrightarrow> (\<forall>x\<in>S. norm (f (X k) x) \<le> h x) \<and> f (X k) integrable_on S"
    by (auto simp: eventually_at_top_linorder)
  define X' where "X' = X \<circ> ((+) N)"
  have X': "\<forall>x\<in>S. norm (f (X' k) x) \<le> h x" "f (X' k) integrable_on S" for k
    using N[of "N + k"] by (simp_all add: X'_def)
  have lim_X': "filterlim X' F sequentially" unfolding X'_def o_def
    by (rule filterlim_compose[OF X]) 
       (use filterlim_add_const_nat_at_top[of N] in \<open>simp_all add: add_ac\<close>)

  show "g integrable_on S"
  proof (rule dominated_convergence)
    show "h integrable_on S"
      by fact
    show "f (X' n) integrable_on S" for n
      by (rule X')
    show "norm (f (X' k) x) \<le> h x" if "x \<in> S" for x k
      using X'[of k] that by auto
    show "(\<lambda>n. f (X' n) x) \<longlonglongrightarrow> g x" if "x \<in> S" for x
      by (rule filterlim_compose[OF conv lim_X']) fact
  qed
qed



(* TODO Move *)
lemma nonpos_Reals_real_eq: "\<real>\<^sub>\<le>\<^sub>0 = {..(0::real)}"
  by (auto simp: nonpos_Reals_def)

(* TODO Move *)
lemma has_integral_complex_of_real_iff:
  "((\<lambda>x. of_real (f x) :: complex) has_integral (of_real I)) A \<longleftrightarrow> (f has_integral I) A"
proof
  assume "((\<lambda>x. of_real (f x) :: complex) has_integral (of_real I)) A"
  thus "(f has_integral I) A"
    by (subst (asm) has_integral_componentwise_iff) (auto simp: Basis_complex_def)
qed (auto intro: has_integral_of_real)

(* TODO Move *)
lemma integrable_on_complex_of_real_iff:
  "(\<lambda>x. of_real (f x) :: complex) integrable_on A \<longleftrightarrow> f integrable_on A"
  using has_integral_complex_of_real_iff[of f _ A]
  by (metis (lifting) ext Re_complex_of_real complex_inner_1_right integrable_component
        integrable_on_def)

(* TODO Move *)
lemma integral_complex_of_real:
  "integral A (\<lambda>x. complex_of_real (f x)) = of_real (integral A f)"
proof (cases "f integrable_on A")
  case True
  thus ?thesis
    using integral_linear[of f A complex_of_real]
    by (auto simp: bounded_linear_of_real o_def)
next
  case False
  hence "\<not>(\<lambda>x. complex_of_real (f x)) integrable_on A"
    by (subst integrable_on_complex_of_real_iff)
  with False show ?thesis
    by (simp add: not_integrable_integral)
qed

(* TODO Move *)
lemma countable_nonpos_Ints [intro]: "countable \<int>\<^sub>\<le>\<^sub>0"
  by (rule countable_subset[of _ "\<int>"]) (auto intro: countable_int)


(* TODO: Move *)
lemma
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes integrable: "\<And>i. set_integrable M A (f i)"
  and summable: "AE x\<in>A in M. summable (\<lambda>i. norm (f i x))"
  and sums: "summable (\<lambda>i. (\<integral>x\<in>A. norm (f i x) \<partial>M))"
  shows set_integrable_suminf: "set_integrable M A (\<lambda>x. (\<Sum>i. f i x))"
    and sums_set_integral: "(\<lambda>i. set_lebesgue_integral M A (f i)) sums (\<integral>x\<in>A. (\<Sum>i. f i x) \<partial>M)"
    and set_integral_suminf: "(\<integral>x\<in>A. (\<Sum>i. f i x) \<partial>M) = (\<Sum>i. set_lebesgue_integral M A (f i))"
    and summable_set_integral: "summable (\<lambda>i. set_lebesgue_integral M A (f i))"
proof -
  have 1: "integrable M (\<lambda>x. indicat_real A x *\<^sub>R f i x)" for i
    using integrable[of i] unfolding set_integrable_def .
  have 2: "AE x in M. summable (\<lambda>i. norm (indicat_real A x *\<^sub>R f i x))"
    using summable by eventually_elim auto
  have 3: "summable (\<lambda>i. lebesgue_integral M (\<lambda>x. norm (indicat_real A x *\<^sub>R f i x)))"
    using sums unfolding set_lebesgue_integral_def by simp

  have "integrable M (\<lambda>x. (\<Sum>i. indicator A x *\<^sub>R f i x))"
    using 1 2 3 by (rule integrable_suminf)
  also have "(\<lambda>x. (\<Sum>i. indicator A x *\<^sub>R f i x)) = (\<lambda>x. indicator A x *\<^sub>R (\<Sum>i. f i x))"
    by (auto simp: indicator_def)
  finally show "set_integrable M A (\<lambda>x. (\<Sum>i. f i x))"
    unfolding set_integrable_def .

  have "(\<lambda>i. set_lebesgue_integral M A (f i)) sums (\<integral>x. (\<Sum>i. indicator A x *\<^sub>R f i x) \<partial>M)"
    unfolding set_lebesgue_integral_def using 1 2 3 by (rule sums_integral)
  also have "(\<integral>x. (\<Sum>i. indicator A x *\<^sub>R f i x) \<partial>M) = (\<integral>x. indicator A x *\<^sub>R (\<Sum>i. f i x) \<partial>M)"
    by (rule Bochner_Integration.integral_cong) (simp_all add: indicator_def)
  finally show "(\<lambda>i. set_lebesgue_integral M A (f i)) sums (\<integral>x\<in>A. (\<Sum>i. f i x) \<partial>M)"
    unfolding set_lebesgue_integral_def .

  have "(\<integral>x\<in>A. \<Sum>i. f i x\<partial>M) = (\<integral>x. (\<Sum>i. indicator A x *\<^sub>R f i x) \<partial>M)"
    unfolding set_lebesgue_integral_def 
    by (rule Bochner_Integration.integral_cong) (auto simp: indicator_def)
  also have "\<dots> = (\<Sum>i. (\<integral>x\<in>A. f i x \<partial>M))"
    unfolding set_lebesgue_integral_def using 1 2 3 by (rule integral_suminf)
  finally show "(\<integral>x\<in>A. (\<Sum>i. f i x) \<partial>M) = (\<Sum>i. set_lebesgue_integral M A (f i))" .

  show "summable (\<lambda>i. set_lebesgue_integral M A (f i))"
    unfolding set_lebesgue_integral_def using 1 2 3 by (rule summable_integral)
qed

(* TODO Move *)
lemma leibniz_rule_field_derivative_real:
  fixes f::"'a::{real_normed_field, banach} \<Rightarrow> real \<Rightarrow> 'a"
  assumes fx: "\<And>x t. x \<in> U \<Longrightarrow> t \<in> {a..b} \<Longrightarrow> ((\<lambda>x. f x t) has_field_derivative fx x t) (at x within U)"
  assumes integrable_f2: "\<And>x. x \<in> U \<Longrightarrow> (f x) integrable_on {a..b}"
  assumes cont_fx: "continuous_on (U \<times> {a..b}) (\<lambda>(x, t). fx x t)"
  assumes U: "x0 \<in> U" "convex U"
  shows "((\<lambda>x. integral {a..b} (f x)) has_field_derivative integral {a..b} (fx x0)) (at x0 within U)"    
  using leibniz_rule_field_derivative[of U a b f fx x0] assms by simp

lemma convex_minkowski_sum_ball:
  fixes A :: "'a :: euclidean_space set"
  assumes "convex A"
  shows   "convex (\<Union>x\<in>A. ball x r)"
proof -
  have "convex (\<Union>x\<in>A. \<Union>y\<in>ball 0 r. {x + y})"
    by (rule convex_sums) (use assms in auto)
  also have "(\<Union>x\<in>A. \<Union>y\<in>ball 0 r. {x + y}) = (\<Union>x\<in>A. ball x r)"
  proof (intro equalityI subsetI)
    fix z assume "z \<in> (\<Union>x\<in>A. \<Union>y\<in>ball 0 r. {x + y})"
    thus "z \<in> (\<Union>x\<in>A. ball x r)"
      by (force simp: dist_norm)
  next
    fix z assume "z \<in> (\<Union>x\<in>A. ball x r)"
    then obtain x where "x \<in> A" "z \<in> ball x r"
      by auto
    hence "z = x + (z - x)" "z - x \<in> ball 0 r"
      by (auto simp: dist_norm)
    thus "z \<in> (\<Union>x\<in>A. \<Union>y\<in>ball 0 r. {x + y})"
      using \<open>x \<in> A\<close> by blast
  qed
  finally show ?thesis .
qed

lemma convex_minkowski_sum_cball:
  fixes A :: "'a :: euclidean_space set"
  assumes "convex A"
  shows   "convex (\<Union>x\<in>A. cball x r)"
proof -
  have "convex (\<Union>x\<in>A. \<Union>y\<in>cball 0 r. {x + y})"
    by (rule convex_sums) (use assms in auto)
  also have "(\<Union>x\<in>A. \<Union>y\<in>cball 0 r. {x + y}) = (\<Union>x\<in>A. cball x r)"
  proof (intro equalityI subsetI)
    fix z assume "z \<in> (\<Union>x\<in>A. \<Union>y\<in>cball 0 r. {x + y})"
    thus "z \<in> (\<Union>x\<in>A. cball x r)"
      by (force simp: dist_norm)
  next
    fix z assume "z \<in> (\<Union>x\<in>A. cball x r)"
    then obtain x where "x \<in> A" "z \<in> cball x r"
      by auto
    hence "z = x + (z - x)" "z - x \<in> cball 0 r"
      by (auto simp: dist_norm)
    thus "z \<in> (\<Union>x\<in>A. \<Union>y\<in>cball 0 r. {x + y})"
      using \<open>x \<in> A\<close> by blast
  qed
  finally show ?thesis .
qed
    
lemma continuous_on_linepath [continuous_intros]:
  assumes "continuous_on A f" "continuous_on A g" "continuous_on A h"
  shows   "continuous_on A (\<lambda>x. linepath (f x) (g x) (h x))"
  unfolding linepath_def by (intro continuous_intros assms)

lemma contour_integral_linepath_has_field_derivative:
  assumes A: "open A" "a \<in> A" "z \<in> A" "closed_segment a z \<subseteq> A"
  assumes holo: "f holomorphic_on A"
  shows   "((\<lambda>z. contour_integral (linepath a z) f) has_field_derivative f z) (at z within B)"
proof -
  define e where "e = (if A = UNIV then 1 else setdist (closed_segment a z) (-A))"
  have "e > 0"
  proof (cases "A = UNIV")
    case False
    hence "setdist (closed_segment a z) (-A) > 0"
      using assms unfolding e_def
      by (subst setdist_gt_0_compact_closed compact_path_image) auto
    thus "e > 0"
      using False by (auto simp: e_def)
  qed (auto simp: e_def)

  have dist_ge_e: "dist x y \<ge> e" if "x \<in> closed_segment a z" "y \<in> -A" for x y
    using setdist_le_dist[OF that] that by (auto simp: e_def)

  define A' where "A' = (\<Union>x\<in>closed_segment a z. ball x e)"
  have "A' \<subseteq> A"
  proof
    fix x assume "x \<in> A'"
    then obtain y where "y \<in> closed_segment a z" "dist y x < e"
      by (auto simp: A'_def)
    thus "x \<in> A"
      using dist_ge_e[of y x] by auto
  qed
  have "closed_segment a z \<subseteq> A'" "open A'"
    using \<open>e > 0\<close> unfolding A'_def by fastforce+
  have "convex A'"
    unfolding A'_def by (intro convex_minkowski_sum_ball) auto
  have "a \<in> A'" "z \<in> A'"
    using \<open>closed_segment a z \<subseteq> A'\<close> by auto
  note A' = \<open>A' \<subseteq> A\<close> \<open>closed_segment a z \<subseteq> A'\<close> \<open>open A'\<close> \<open>convex A'\<close> \<open>a \<in> A'\<close> \<open>z \<in> A'\<close>
  note holo = holomorphic_on_subset[OF holo \<open>A' \<subseteq> A\<close>]

  have "(f has_field_derivative deriv f z) (at z)" if "z \<in> A'" for z
    using that A' A by (auto intro!: holomorphic_derivI holo)
  note [derivative_intros] = DERIV_chain2[OF this]
  note [continuous_intros] = 
    continuous_on_compose2[OF holomorphic_on_imp_continuous_on [OF holo]]
    continuous_on_compose2[OF holomorphic_on_imp_continuous_on [OF holomorphic_deriv[OF holo]]]
  have [derivative_intros]:
      "((\<lambda>x. linepath a x t) has_field_derivative of_real t) (at x within A')" for t x
    by (auto simp: linepath_def scaleR_conv_of_real intro!: derivative_eq_intros)
 
  have *: "linepath a b t \<in> A'" if "a \<in> A'" "b \<in> A'" "t \<in> {0..1}" for a b t
    using that linepath_in_convex_hull[of a A' b t] A' by (simp add: hull_same)
    
  have "((\<lambda>z. integral {0..1} (\<lambda>x. f (linepath a z x)) * (z - a)) has_field_derivative 
      integral {0..1} (\<lambda>t. deriv f (linepath a z t) * of_real t) * (z - a) +
      integral {0..1} (\<lambda>x. f (linepath a z x))) (at z within A')" 
      (is "(_ has_field_derivative ?I) _")
    by (rule derivative_eq_intros leibniz_rule_field_derivative_real * A')+
       (insert assms A' *,
        auto intro!: derivative_eq_intros leibniz_rule_field_derivative_real
                     integrable_continuous_real continuous_intros 
             simp:   split_beta scaleR_conv_of_real)
  also have "(\<lambda>z. integral {0..1} (\<lambda>x. f (linepath a z x)) * (z - a)) = 
               (\<lambda>z. contour_integral (linepath a z) f)"
    by (simp add: contour_integral_integral)
  also have "?I = integral {0..1} (\<lambda>x. deriv f (linepath a z x) * of_real x * (z - a) + 
                     f (linepath a z x))" (is "_ = integral _ ?g")
    by (subst integral_mult_left [symmetric], subst integral_add [symmetric])
       (insert assms A', auto intro!: integrable_continuous_real continuous_intros simp: *)
  also have "(?g has_integral of_real 1 * f (linepath a z 1) - of_real 0 * f (linepath a z 0)) {0..1}"
    using * A A'
    by (intro fundamental_theorem_of_calculus)
       (auto intro!: derivative_eq_intros has_vector_derivative_real_field 
             simp: linepath_def scaleR_conv_of_real)
  hence "integral {0..1} ?g = f (linepath a z 1)" by (simp add: has_integral_iff)
  also have "linepath a z 1 = z" by (simp add: linepath_def)
  also from \<open>z \<in> A'\<close> and \<open>open A'\<close> have "at z within A' = at z" by (rule at_within_open)
  finally show ?thesis by (rule DERIV_subset) simp_all
qed



(* TODO: Move *)
lemma set_integrable_bigo:
  fixes f g :: "real \<Rightarrow> 'a :: {banach, real_normed_field, second_countable_topology}"
  assumes "f \<in> O(\<lambda>x. g x)" and "set_integrable lborel {a..} g"
  assumes "\<And>b. b \<ge> a \<Longrightarrow> set_integrable lborel {a..<b} f"
  assumes [measurable]: "set_borel_measurable borel {a..} f"
  shows   "set_integrable lborel {a..} f"
proof -
  from assms(1) obtain C x0 where C: "C > 0" "\<And>x. x \<ge> x0 \<Longrightarrow> norm (f x) \<le> C * norm (g x)"
    by (fastforce elim!: landau_o.bigE simp: eventually_at_top_linorder)
  define x0' where "x0' = max a x0"

  have "set_integrable lborel {a..<x0'} f"
    by (intro assms) (auto simp: x0'_def)
  moreover have "set_integrable lborel {x0'..} f" unfolding set_integrable_def
  proof (rule Bochner_Integration.integrable_bound)
    from assms(2) have "set_integrable lborel {x0'..} g"
      by (rule set_integrable_subset) (auto simp: x0'_def)
    thus "integrable lborel (\<lambda>x. C *\<^sub>R (indicator {x0'..} x *\<^sub>R g x))" unfolding set_integrable_def
      by (intro integrable_scaleR_right) (simp add: abs_mult norm_mult)
  next
    from assms(4) have "set_borel_measurable borel {x0'..} f"
      by (rule set_borel_measurable_subset) (auto simp: x0'_def)
    thus "(\<lambda>x. indicator {x0'..} x *\<^sub>R f x) \<in> borel_measurable lborel"
      by (simp add: set_borel_measurable_def)
  next
    show "AE x in lborel. norm (indicator {x0'..} x *\<^sub>R f x)
                            \<le> norm (C *\<^sub>R (indicator {x0'..} x *\<^sub>R g x))"
      using C by (intro AE_I2) (auto simp: abs_mult indicator_def x0'_def)
  qed
  ultimately have "set_integrable lborel ({a..<x0'} \<union> {x0'..}) f"
    by (rule set_integrable_Un) auto
  also have "{a..<x0'} \<union> {x0'..} = {a..}" by (auto simp: x0'_def)
  finally show ?thesis .
qed


subsection \<open>Miscellaneous preliminary material\<close>

(* TODO: Move to HOL-Complex_Analysis.Cauchy_Integral_Formula *)
lemma uniform_limit_analytic_at:
  assumes "uniform_limit A f g F"
  assumes "eventually (\<lambda>x. f x holomorphic_on A) F"
  assumes "z \<in> A" "open A" "F \<noteq> bot"
  shows   "g analytic_on {z}"
proof -
  obtain r where r: "r > 0" "cball z r \<subseteq> A"
    using \<open>z \<in> A\<close> \<open>open A\<close> by (meson open_contains_cball)
  show ?thesis
  proof (rule holomorphic_uniform_limit[of z r f F g])
    show "\<forall>\<^sub>F x in F. continuous_on (cball z r) (f x) \<and> f x holomorphic_on ball z r"
      using assms(2)
    proof eventually_elim
      case (elim x)
      have "ball z r \<subseteq> cball z r"
        by auto
      also have "\<dots> \<subseteq> A"
        by fact
      finally have "f x holomorphic_on ball z r"
        using elim holomorphic_on_subset r by blast
      moreover have "continuous_on (cball z r) (f x)"
        using elim r by (auto intro: holomorphic_on_imp_continuous_on)
      ultimately show ?case by blast
    qed
  next
    assume "g holomorphic_on ball z r"
    thus "g analytic_on {z}"
      using \<open>z \<in> A\<close> \<open>open A\<close> analytic_at_ball r(1) by blast
  next
    show "uniform_limit (cball z r) f g F"
      using assms(1) by (rule uniform_limit_on_subset) (use r in auto)
  qed (use assms in auto)
qed

lemma uniform_limit_holomorphic:
  assumes "uniform_limit A f g F"
  assumes "eventually (\<lambda>x. f x holomorphic_on A) F"
  assumes "open A" "F \<noteq> bot"
  shows   "g holomorphic_on A"
proof -
  have "g analytic_on A"
    using uniform_limit_analytic_at[OF assms(1,2) _ assms(3,4)] analytic_on_analytic_at
    by blast
  thus ?thesis
    using \<open>open A\<close> by (simp add: analytic_on_open)
qed

(* TODO: Move to HOL-Analysis.Euler_Mascheroni *)
lemma Re_euler_mascheroni [simp]: "Re euler_mascheroni = euler_mascheroni"
  and Im_euler_mascheroni [simp]: "Im euler_mascheroni = 0"
  by (simp_all add: euler_mascheroni_def)

(* TODO: Move to Deriv. Check if it breaks anything. *)
lemma has_real_derivative_imp_has_vector_derivative [derivative_intros]:
  assumes "(f has_real_derivative f') (at x)"
  shows   "(f has_vector_derivative f') (at x)"
  using assms by (simp add: has_real_derivative_iff_has_vector_derivative)

(* TODO: This version should probably replace the version in the library (without the ') *)
lemma DERIV_real_sqrt_generic':
  assumes "x \<noteq> 0"
  shows "(sqrt has_field_derivative (sgn x * inverse (sqrt x) / 2)) (at x within A)"
  unfolding sqrt_def
  by (rule has_field_derivative_at_within) (use assms in \<open>auto intro!: DERIV_real_root_generic\<close>)

(* TODO: This version should probably replace the version in the library (without the ') *)
lemma DERIV_real_root_generic':
  assumes "x \<noteq> 0"
  shows "(root n has_real_derivative (inverse (real n * (sgn x * root n x) ^ (n - Suc 0)))) (at x within A)"
proof (cases "n = 0")
  case False
  show ?thesis
    by (rule has_field_derivative_at_within)
       (use False assms in \<open>auto intro!: DERIV_real_root_generic simp: field_simps sgn_if\<close>)
next
  case True
  have "root 0 = (\<lambda>x. 0)"
    by (auto simp: root_def fun_eq_iff)
  thus ?thesis
    using True by auto
qed

declare
  DERIV_real_sqrt_generic[THEN DERIV_chain2, derivative_intros del]
  DERIV_real_root_generic[THEN DERIV_chain2, derivative_intros del]
  DERIV_real_sqrt_generic'[THEN DERIV_chain2, derivative_intros] 
  DERIV_real_root_generic'[THEN DERIV_chain2, derivative_intros] 

lemmas [derivative_intros] = has_vector_derivative_real_field


(* TODO: Move to Complex *)
lemma DERIV_complex_norm [derivative_intros]:
  fixes f :: "real \<Rightarrow> complex"
  assumes "f x \<noteq> 0" and [derivative_intros]: "(f has_vector_derivative D') (at x)"
  shows "((\<lambda>x. norm (f x)) has_field_derivative ((D' \<bullet> f x) / norm (f x))) (at x)"
proof -
  have "norm (f x) > 0"
    using assms by simp
  hence *: "(Re (f x))\<^sup>2 + (Im (f x))\<^sup>2 > 0"
    unfolding cmod_def by simp
  hence **: "(Re (f x))\<^sup>2 + (Im (f x))\<^sup>2 \<noteq> 0"
    by auto
  from assms have ***: "Re (f x) \<noteq> 0 \<or> Im (f x) \<noteq> 0"
    by (auto simp: complex_eq_iff)
  show ?thesis unfolding cmod_def
    using * by derivative (auto simp: divide_simps inner_complex_def)
qed


subsection \<open>Preliminary facts about the Gamma and Digamma function\<close>

(* TODO: much of this could be put in the library, to HOL_Analysis.Gamma_Function, or if
   necessary somewhere in HOL-Complex_Analysis (e.g. Complex_Transcendental).
   It is of general interest.
*)

lemma cnj_Digamma:
  assumes [simp]: "s \<noteq> 0"
  shows   "cnj (Digamma s) = Digamma (cnj s)"
proof (rule tendsto_unique)
  have "(\<lambda>x. (complex_of_real (ln (real x)) - (\<Sum>n<x. inverse (cnj s + of_nat n)))) \<longlonglongrightarrow> Digamma (cnj s)"
    (is "?f \<longlonglongrightarrow> _") by (rule tendsto_cnj Digamma_LIMSEQ)+ auto
  also have "?f = (\<lambda>x. cnj (complex_of_real (ln (real x)) - (\<Sum>n<x. inverse (s + of_nat n))))"
    by simp
  finally show "\<dots> \<longlonglongrightarrow> Digamma (cnj s)" .
  show "(\<lambda>x. cnj (complex_of_real (ln (real x)) - (\<Sum>n<x. inverse (s + of_nat n)))) \<longlonglongrightarrow> cnj (Digamma s)"
    by (rule tendsto_cnj Digamma_LIMSEQ)+ auto
qed auto

lemma cnj_Polygamma:
  assumes [simp]: "s \<noteq> 0"
  shows   "cnj (Polygamma n s) = Polygamma n (cnj s)"
proof (cases "n = 0")
  case True
  thus ?thesis using cnj_Digamma[of s] by simp
next
  case False
  have "(\<lambda>k. inverse ((cnj s + of_nat k) ^ Suc n)) sums 
          ((-1) ^ Suc n * Polygamma n (cnj s) / fact n)"
    by (rule Polygamma_LIMSEQ) (use False in auto)
  also have "(\<lambda>k. inverse ((cnj s + of_nat k) ^ Suc n)) = 
             (\<lambda>k. cnj (inverse ((s + of_nat k) ^ Suc n)))"
    by simp
  finally have "(\<lambda>k. cnj (inverse ((s + of_nat k) ^ Suc n))) sums 
                  ((-1) ^ Suc n * Polygamma n (cnj s) / fact n)" .
  moreover have "(\<lambda>k. cnj (inverse ((s + of_nat k) ^ Suc n))) sums 
                   (cnj ((-1) ^ Suc n * Polygamma n s / fact n))"
    unfolding sums_cnj by (intro Polygamma_LIMSEQ) (use False in auto)
  ultimately have "(-1) ^ Suc n * Polygamma n (cnj s) / fact n = 
                   cnj ((-1) ^ Suc n * Polygamma n s / fact n)"
    by (rule sums_unique2)
  thus ?thesis by simp
qed

lemma norm_rGamma_Im_mono:
  assumes "Re z1 = Re z2" "\<bar>Im z1\<bar> \<le> \<bar>Im z2\<bar>"
  shows   "norm (rGamma z1) \<le> norm (rGamma z2)"
proof -
  define a b1 b2 where "a = Re z1" and "b1 = \<bar>Im z1\<bar>" and "b2 = \<bar>Im z2\<bar>"
  from assms have b12: "0 \<le> b1" "b1 \<le> b2"
    by (simp_all add: b1_def b2_def)
  have *: "norm (rGamma_series_Weierstrass (Complex a b1) n) \<le> norm (rGamma_series_Weierstrass (Complex a b2) n)" for n
    unfolding rGamma_series_Weierstrass_def norm_mult prod_norm [symmetric]
  proof (intro mult_mono mult_nonneg_nonneg norm_ge_zero exp_ge_zero prod_nonneg ballI prod_mono conjI)
    from b12 show "norm (Complex a b1) \<le> norm (Complex a b2)"
      by (auto simp: cmod_def simp flip: abs_le_square_iff)
  next
    fix i assume i: "i \<in> {1..n}"
    have *: "norm (1 + z / of_nat i) = norm (of_nat i + z) / real i" for z :: complex
    proof -
      have "norm (of_nat i + z) / real i = norm ((of_nat i + z) / of_nat i)"
        by (subst norm_divide) auto
      also have "(of_nat i + z) / of_nat i = 1 + z / of_nat i"
        using i by (simp add: field_simps)
      finally show ?thesis ..
    qed
    show "cmod (1 + Complex a b1 / of_nat i) \<le> cmod (1 + Complex a b2 / of_nat i)"
      using i b12 unfolding *
      by (intro divide_right_mono) (auto simp: cmod_def simp flip: abs_le_square_iff)
  qed auto
  have "norm (rGamma (Complex a b1)) \<le> norm (rGamma (Complex a b2))"
    by (rule tendsto_le sequentially_bot tendsto_norm tendsto_norm rGamma_Weierstrass_complex)+
       (rule always_eventually allI *)+
  also have "Complex a b1 \<in> {z1, cnj z1}"
    by (auto simp: a_def b1_def complex_eq_iff)
  hence "norm (rGamma (Complex a b1)) = norm (rGamma z1)"
    by (auto simp flip: cnj_rGamma)
  also have "Complex a b2 \<in> {z2, cnj z2}"
    by (auto simp: assms a_def b2_def complex_eq_iff)
  hence "norm (rGamma (Complex a b2)) = norm (rGamma z2)"
    by (auto simp flip: cnj_rGamma)
  finally show ?thesis .
qed

lemma Re_Digamma_Im_mono:
  assumes "Re z1 = Re z2" "Re z1 > 0" "\<bar>Im z1\<bar> \<le> \<bar>Im z2\<bar>"
  shows "Re (Digamma z1) \<le> Re (Digamma z2)"
proof -
  have [simp]: "z1 \<noteq> 0" "z2 \<noteq> 0"
    using assms by (auto simp: complex_eq_iff)
  define a b1 b2 where "a = Re z1" and "b1 = \<bar>Im z1\<bar>" and "b2 = \<bar>Im z2\<bar>"
  have "Re (Digamma (Complex a b1)) \<le> Re (Digamma (Complex a b2))"
  proof (rule tendsto_le[OF _ _ _ always_eventually[OF allI]])
    fix k :: nat
    have "(a + real n) / (b2\<^sup>2 + (a + real n)\<^sup>2) \<le> (a + real n) / (b1\<^sup>2 + (a + real n)\<^sup>2)" for n
      using assms
      by (intro divide_left_mono mult_pos_pos add_nonneg_pos)
         (auto simp: a_def b1_def b2_def abs_le_square_iff)
    hence "(\<Sum>x<k. Re (1 / (of_nat x + Complex a b2))) \<le> (\<Sum>x<k. Re (1 / (of_nat x + Complex a b1)))"
      using assms by (intro sum_mono) (auto simp: Re_divide field_simps)
    thus "Re (complex_of_real (ln (real k)) - (\<Sum>n<k. inverse (Complex a b1 + of_nat n))) \<le>
          Re (complex_of_real (ln (real k)) - (\<Sum>n<k. inverse (Complex a b2 + of_nat n)))"
      by (simp add: field_simps)
  next
    show "sequentially \<noteq> bot" by simp
  qed ((rule Digamma_LIMSEQ tendsto_Re)+; use assms in \<open>simp add: a_def complex_eq_iff\<close>)+
  also have "Complex a b1 \<in> {z1, cnj z1}"
    by (auto simp: complex_eq_iff a_def b1_def b2_def)
  hence "Re (Digamma (Complex a b1)) = Re (Digamma z1)"
    by (auto simp flip: cnj_Digamma)
  also have "Complex a b2 \<in> {z2, cnj z2}"
    by (auto simp: complex_eq_iff a_def b1_def b2_def assms)
  hence "Re (Digamma (Complex a b2)) = Re (Digamma z2)"
    by (auto simp flip: cnj_Digamma)
  finally show ?thesis .
qed
 
lemma Digamma_Re_le_Re_Digamma:
  assumes "Re z > 0"
  shows "Digamma (Re z) \<le> Re (Digamma z)"
proof -
  have "Digamma (Re z) = Re (Digamma (of_real (Re z)))"
    using assms by (subst Polygamma_of_real) auto
  also have "\<dots> \<le> Re (Digamma z)"
    by (rule Re_Digamma_Im_mono) (use assms in auto)
  finally show ?thesis .
qed
    
lemma Re_Digamma_nonneg:
  assumes "Re z > 0" "Digamma (Re z) \<ge> 0"
  shows "Re (Digamma z) \<ge> 0"
proof -
  have "0 \<le> Digamma (Re z)"
    using assms by simp
  also have "\<dots> \<le> Re (Digamma z)"
    by (rule Digamma_Re_le_Re_Digamma) (use assms in auto)
  finally show ?thesis .
qed

lemma norm_Gamma_Re_mono:
  assumes "Im z1 = Im z2" "Re z1 \<le> Re z2" "Re z1 > 0" "Digamma (Re z1) \<ge> 0"
  shows   "norm (Gamma z1) \<le> norm (Gamma z2)"
proof -
  define a1 a2 b where "a1 = Re z1" and "a2 = Re z2" and "b = Im z1"

  have z1: "z1 = complex_of_real a1 + \<i> * complex_of_real b"
   and z2: "z2 = complex_of_real a2 + \<i> * complex_of_real b"
    by (simp_all add: a1_def a2_def b_def complex_eq_iff assms)

  show "norm (Gamma z1) \<le> norm (Gamma z2)"
    unfolding z1 z2
  proof (rule deriv_nonneg_imp_mono[where g = "\<lambda>a. norm (Gamma (complex_of_real a + \<i> * b))"])
    fix x :: real
    assume x: "x \<in> {a1..a2}"
    with assms have "x > 0" by (auto simp: a1_def)
    define z where "z = complex_of_real x + \<i> * complex_of_real b"
    have *: "complex_of_real x + \<i> * complex_of_real b \<notin> \<int>\<^sub>\<le>\<^sub>0"
      using \<open>x > 0\<close> by (auto elim!: nonpos_Ints_cases simp: complex_eq_iff)
    hence **: "Gamma (complex_of_real x + \<i> * complex_of_real b) \<noteq> 0"
      by (subst Gamma_eq_zero_iff) auto
    have "((\<lambda>x. norm (Gamma (of_real x + \<i> * b))) has_field_derivative
            (Gamma z * Digamma z) \<bullet> Gamma z / norm (Gamma z)) (at x)"
      using * ** by derivative (auto simp: z_def)
    also have "(Gamma z * Digamma z) \<bullet> Gamma z = Re (Digamma z) * norm (Gamma z) ^ 2"
      by (simp add: inner_complex_def cmod_def power2_eq_square field_simps)
    also have "\<dots> / norm (Gamma z) = Re (Digamma z) * norm (Gamma z)"
      by (simp add: power2_eq_square)
    finally show "((\<lambda>x. norm (Gamma (of_real x + \<i> * b)))
                    has_field_derivative Re (Digamma z) * norm (Gamma z)) (at x)" .

    from x have "Re z > 0"
      using assms by (auto simp: z_def a1_def)
    moreover {
      have "0 \<le> Digamma a1" using assms by (simp add: a1_def)
      also have "\<dots> \<le> Digamma (Re x)"
        using assms x by (intro Digamma_real_mono) (auto simp: a1_def)
      finally have "Digamma (Re x) \<ge> 0" .
    }
    ultimately have "Re (Digamma z) \<ge> 0"
      by (intro Re_Digamma_nonneg) (auto simp: z_def)
    thus "Re (Digamma z) * norm (Gamma z) \<ge> 0"
      using assms x by (intro mult_nonneg_nonneg) auto
  qed (use assms in \<open>auto simp: a1_def a2_def\<close>)
qed

lemma norm_Gamma_Im_mono:
  assumes "Re z1 = Re z2" "\<bar>Im z1\<bar> \<le> \<bar>Im z2\<bar>" "z1 \<in> \<int>\<^sub>\<le>\<^sub>0 \<longrightarrow> z2 \<in> \<int>\<^sub>\<le>\<^sub>0"
  shows   "norm (Gamma z1) \<ge> norm (Gamma z2)"
proof (cases "z2 \<in> \<int>\<^sub>\<le>\<^sub>0")
  case True
  hence "Gamma z2 = 0" by (auto simp: Gamma_eq_zero_iff)
  thus ?thesis by simp
next
  case False
  with assms have "z1 \<notin> \<int>\<^sub>\<le>\<^sub>0"
    by auto
  with assms False norm_rGamma_Im_mono[of z1 z2] show ?thesis
    by (auto simp: Gamma_def norm_divide field_simps rGamma_eq_zero_iff)
qed

lemma norm_Gamma_bound:
  assumes "Re z \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "norm (Gamma z) \<le> \<bar>Gamma (Re z)\<bar>"
proof -
  from assms have "z \<notin> \<int>\<^sub>\<le>\<^sub>0"
    by (auto simp: nonpos_Ints_def)
  with norm_Gamma_Im_mono[of "of_real (Re z)" z] assms show ?thesis
    by (auto simp: Gamma_complex_of_real of_real_in_nonpos_Ints_iff)
qed

lemma norm_Gamma_bound':
  assumes "Re z > 0"
  shows   "norm (Gamma z) \<le> Gamma (Re z)"
proof -
  from assms have "Re z \<notin> \<int>\<^sub>\<le>\<^sub>0"
    by (auto elim: nonpos_Ints_cases)
  with assms show ?thesis
    using norm_Gamma_bound[of z] by simp
qed

end
