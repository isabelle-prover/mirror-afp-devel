section \<open>Tail Bounds for Expander Walks\<close>

theory Distributed_Distinct_Elements_Tail_Bounds
  imports
    Distributed_Distinct_Elements_Preliminary
    Expander_Graphs.Pseudorandom_Objects_Expander_Walks
    "HOL-Decision_Procs.Approximation"
begin

text \<open>This section introduces tail estimates for random walks in expander graphs, specific to the
verification of this algorithm (in particular to two-stage expander graph sampling and obtained
tail bounds for subgaussian random variables). They follow from the more fundamental results
@{thm [source] regular_graph.kl_chernoff_property} and
@{thm [source] regular_graph.uniform_property} which are verified in the AFP entry for
expander graphs~\cite{Expander_Graphs-AFP}.\<close>

hide_fact Henstock_Kurzweil_Integration.integral_sum

unbundle intro_cong_syntax

lemma x_ln_x_min:
  assumes "x \<ge> (0::real)"
  shows  "x * ln x \<ge> -exp (-1)"
proof -
  define f where "f x = x * ln x" for x :: real
  define f' where "f' x = ln x + 1" for x :: real

  have 0:"(f has_real_derivative (f' x)) (at x)" if "x > 0" for x
    unfolding f_def f'_def using that
    by (auto intro!: derivative_eq_intros)

  have "f' x \<ge> 0" if "exp (-1) \<le> x" for x :: real
  proof -
    have "ln x \<ge> -1"
      using that order_less_le_trans[OF exp_gt_zero]
      by (intro iffD2[OF ln_ge_iff]) auto
    thus ?thesis
      unfolding f'_def by (simp)
  qed

  hence "\<exists>y. (f has_real_derivative y) (at x) \<and> 0 \<le> y" if "x \<ge> exp (-1)" for x :: real
    using that order_less_le_trans[OF exp_gt_zero]
    by (intro exI[where x="f' x"] conjI 0) auto
  hence "f (exp (-1)) \<le> f x" if "exp(-1) \<le> x"
    by (intro DERIV_nonneg_imp_nondecreasing[OF that]) auto
  hence 2:?thesis if  "exp(-1) \<le> x"
    unfolding f_def using that by simp

  have "f' x \<le> 0" if "x > 0" "x \<le> exp (-1)" for x :: real
  proof -
    have "ln x \<le> ln (exp (-1))"
      by (intro iffD2[OF ln_le_cancel_iff] that exp_gt_zero)
    also have "... = -1"
      by simp
    finally have "ln x \<le> -1" by simp
    thus ?thesis unfolding f'_def by simp
  qed

  hence "\<exists>y. (f has_real_derivative y) (at x) \<and> y \<le> 0" if "x > 0 " "x \<le> exp (-1)" for x :: real
    using that by (intro exI[where x="f' x"] conjI 0) auto
  hence "f (exp (-1)) \<le> f x" if "x > 0" "x \<le> exp(-1)"
    using that(1) by (intro DERIV_nonpos_imp_nonincreasing[OF that(2)]) auto
  hence 3:?thesis if "x > 0" "x \<le> exp(-1)"
    unfolding f_def using that by simp

  have ?thesis if "x = 0"
    using that by simp
  thus ?thesis
    using 2 3 assms by fastforce
qed

theorem (in regular_graph) walk_tail_bound:
  assumes "l > 0"
  assumes "S \<subseteq> verts G"
  defines "\<mu> \<equiv> real (card S) / card (verts G)"
  assumes "\<gamma> < 1" "\<mu> + \<Lambda>\<^sub>a \<le> \<gamma>"
  shows "measure (pmf_of_multiset (walks G l)) {w. real (card {i \<in> {..<l}. w ! i \<in> S}) \<ge> \<gamma>*l}
    \<le> exp (- real l * (\<gamma> * ln (1/(\<mu>+\<Lambda>\<^sub>a)) - 2 * exp(-1)))" (is "?L \<le> ?R")
proof (cases "\<mu> > 0")
  case True

  have "0 < \<mu> + \<Lambda>\<^sub>a"
    by (intro add_pos_nonneg \<Lambda>_ge_0 True)
  also have "... \<le> \<gamma>"
    using assms(5) by simp
  finally have \<gamma>_gt_0: "0 < \<gamma>" by simp

  hence \<gamma>_ge_0: "0 \<le> \<gamma>"
    by simp

  have "card S \<le> card (verts G)"
    by (intro card_mono assms(2)) auto
  hence \<mu>_le_1: "\<mu> \<le> 1"
    unfolding \<mu>_def by (simp add:divide_simps)

  have 2: "0 < \<mu> + \<Lambda>\<^sub>a * (1 - \<mu>)"
    using \<mu>_le_1 by (intro add_pos_nonneg True mult_nonneg_nonneg \<Lambda>_ge_0) auto

  have "\<mu> + \<Lambda>\<^sub>a * (1 - \<mu>) \<le> \<mu> +  \<Lambda>\<^sub>a * 1"
    using \<Lambda>_ge_0 True by (intro add_mono mult_left_mono) auto
  also have "... \<le> \<gamma>"
    using assms(5) by simp
  also have "... < 1"
    using assms(4) by simp
  finally have 4:"\<mu> + \<Lambda>\<^sub>a * (1 - \<mu>) < 1" by simp
  hence 3: "1 \<le> 1 / (1 - (\<mu> + \<Lambda>\<^sub>a * (1 - \<mu>)))"
    using 2 by (subst pos_le_divide_eq) simp_all

  have "card S \<le> n"
    unfolding n_def by (intro card_mono assms(2)) auto
  hence 0:"\<mu> \<le> 1"
    unfolding \<mu>_def n_def[symmetric] using n_gt_0 by simp

  have "\<gamma> * ln (1 / (\<mu> + \<Lambda>\<^sub>a)) - 2*exp (- 1) = \<gamma> * ln (1 / (\<mu> + \<Lambda>\<^sub>a*1))+0 -2*exp (- 1)"
    by simp
  also have "... \<le> \<gamma> * ln (1 / (\<mu> + \<Lambda>\<^sub>a*(1-\<mu>)))+0-2*exp(-1)"
    using True \<gamma>_ge_0 \<Lambda>_ge_0 0 2
    by (intro diff_right_mono mult_left_mono iffD2[OF ln_le_cancel_iff] divide_pos_pos
        divide_left_mono add_mono) auto
  also have "... \<le> \<gamma> * ln (1 / (\<mu> + \<Lambda>\<^sub>a*(1-\<mu>)))+(1-\<gamma>)*ln(1/(1-(\<mu>+\<Lambda>\<^sub>a*(1-\<mu>))))-2* exp(-1)"
    using assms(4) 3 by (intro add_mono diff_mono mult_nonneg_nonneg ln_ge_zero) auto
  also have "... = (-exp(-1))+\<gamma>*ln(1/(\<mu>+\<Lambda>\<^sub>a*(1-\<mu>)))+(-exp(-1))+(1-\<gamma>)*ln(1/(1-(\<mu>+\<Lambda>\<^sub>a*(1-\<mu>))))"
    by simp
  also have "... \<le> \<gamma>*ln \<gamma>+\<gamma>*ln(1/(\<mu>+\<Lambda>\<^sub>a*(1-\<mu>)))+(1-\<gamma>)*ln(1-\<gamma>)+(1-\<gamma>)*ln(1/(1-(\<mu>+\<Lambda>\<^sub>a*(1-\<mu>))))"
    using assms(4) \<gamma>_ge_0 by (intro add_mono x_ln_x_min) auto
  also have "... = \<gamma>*(ln \<gamma>+ln(1/(\<mu>+\<Lambda>\<^sub>a*(1-\<mu>))))+(1-\<gamma>)*(ln(1-\<gamma>)+ln(1/(1-(\<mu>+\<Lambda>\<^sub>a*(1-\<mu>)))))"
    by (simp add:algebra_simps)
  also have "... = \<gamma> * ln (\<gamma>*(1/(\<mu>+\<Lambda>\<^sub>a*(1-\<mu>))))+(1-\<gamma>)*ln((1-\<gamma>)*(1/(1-(\<mu>+\<Lambda>\<^sub>a*(1-\<mu>)))))"
    using 2 4 by (simp add: ln_mult ln_div)
  also have "... = KL_div \<gamma> (\<mu>+\<Lambda>\<^sub>a*(1-\<mu>))"
    using assms(4,5) 2 4 \<gamma>_ge_0 by (subst KL_div_eq) simp_all
  finally have 1: "\<gamma> * ln (1 / (\<mu> + \<Lambda>\<^sub>a)) - 2 * exp (- 1) \<le> KL_div \<gamma> (\<mu> + \<Lambda>\<^sub>a * (1 - \<mu>))"
    by simp

  have "\<mu>+\<Lambda>\<^sub>a*(1-\<mu>) \<le> \<mu>+\<Lambda>\<^sub>a*1"
    using True
    by (intro add_mono mult_left_mono \<Lambda>_ge_0) auto
  also have "... \<le> \<gamma>"
    using assms(5) by simp
  finally have "\<mu>+\<Lambda>\<^sub>a*(1-\<mu>) \<le> \<gamma>"  by simp
  moreover have "\<mu>+\<Lambda>\<^sub>a*(1-\<mu>) > 0"
    using 0 by (intro add_pos_nonneg True mult_nonneg_nonneg \<Lambda>_ge_0) auto
  ultimately have "\<mu>+\<Lambda>\<^sub>a*(1-\<mu>) \<in> {0<..\<gamma>}" by simp
  hence "?L \<le> exp (- real l * KL_div \<gamma> (\<mu>+\<Lambda>\<^sub>a*(1-\<mu>)))"
    using assms(4) unfolding \<mu>_def by (intro kl_chernoff_property assms(1,2)) auto
  also have "... \<le> ?R"
    using assms(1) 1 by simp
  finally show ?thesis by simp
next
  case False
  hence "\<mu> \<le> 0" by simp
  hence "card S = 0"
    unfolding \<mu>_def n_def[symmetric] using n_gt_0 by (simp add:divide_simps)
  moreover have "finite S"
    using finite_subset[OF assms(2) finite_verts] by auto
  ultimately have 0:"S = {}" by auto
  have "\<mu> = 0"
    unfolding \<mu>_def 0 by simp
  hence "\<mu> + \<Lambda>\<^sub>a \<ge>0 "
    using \<Lambda>_ge_0 by simp
  hence "\<gamma> \<ge> 0"
    using assms(5) by simp
  hence "\<gamma> * real l \<ge> 0"
    by (intro mult_nonneg_nonneg) auto
  thus ?thesis using 0 by simp
qed

theorem (in regular_graph) walk_tail_bound_2:
  assumes "l > 0" "\<Lambda>\<^sub>a \<le> \<Lambda>" "\<Lambda> > 0"
  assumes "S \<subseteq> verts G"
  defines "\<mu> \<equiv> real (card S) / card (verts G)"
  assumes "\<gamma> < 1" "\<mu> + \<Lambda> \<le> \<gamma>"
  shows "measure (pmf_of_multiset (walks G l)) {w. real (card {i \<in> {..<l}. w ! i \<in> S}) \<ge> \<gamma>*l}
    \<le> exp (- real l * (\<gamma> * ln (1/(\<mu>+\<Lambda>)) - 2 * exp(-1)))" (is "?L \<le> ?R")
proof (cases "\<mu> > 0")
  case True

  have 0: "0 < \<mu> + \<Lambda>\<^sub>a"
    by (intro add_pos_nonneg \<Lambda>_ge_0 True)
  hence "0 < \<mu> + \<Lambda>"
    using assms(2) by simp
  hence 1: "0 < (\<mu> + \<Lambda>) * (\<mu> + \<Lambda>\<^sub>a)"
    using 0 by simp

  have 3:"\<mu> + \<Lambda>\<^sub>a \<le> \<gamma>"
    using assms(2,7) by simp
  have 2: "0 \<le> \<gamma>"
    using 3 True \<Lambda>_ge_0 by simp

  have "?L \<le> exp (- real l * (\<gamma> * ln (1/(\<mu>+\<Lambda>\<^sub>a)) - 2 * exp(-1)))"
    using 3 unfolding \<mu>_def by (intro walk_tail_bound assms(1,4,6))
  also have "... = exp (- (real l * (\<gamma> * ln (1/(\<mu>+\<Lambda>\<^sub>a)) - 2 * exp(-1))))"
    by simp
  also have "... \<le> exp (- (real l * (\<gamma> * ln (1/(\<mu>+\<Lambda>)) - 2 * exp(-1))))"
    using True assms(2,3) using 0 1 2
    by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono diff_mono iffD2[OF ln_le_cancel_iff]
        divide_left_mono le_imp_neg_le) simp_all
  also have "... = ?R"
    by simp
  finally show ?thesis by simp
next
  case False
  hence "\<mu> \<le> 0" by simp
  hence "card S = 0"
    unfolding \<mu>_def n_def[symmetric] using n_gt_0 by (simp add:divide_simps)
  moreover have "finite S"
    using finite_subset[OF assms(4) finite_verts] by auto
  ultimately have 0:"S = {}" by auto
  have "\<mu> = 0"
    unfolding \<mu>_def 0 by simp
  hence "\<mu> + \<Lambda>\<^sub>a \<ge>0 "
    using \<Lambda>_ge_0 by simp
  hence "\<gamma> \<ge> 0"
    using assms by simp
  hence "\<gamma> * real l \<ge> 0"
    by (intro mult_nonneg_nonneg) auto
  thus ?thesis using 0 by simp
qed

lemma disjI_safe: "(\<not>x \<Longrightarrow> y) \<Longrightarrow>  x \<or> y" by auto

lemma walk_tail_bound:
  fixes T
  assumes "l > 0" "\<Lambda> > 0"
  assumes "measure (sample_pro S) {w. T w} \<le> \<mu>"
  assumes "\<gamma> \<le> 1" "\<mu> + \<Lambda> \<le> \<gamma>" "\<mu> \<le> 1"
  shows "measure (sample_pro (\<E> l \<Lambda> S)) {w. real (card {i \<in> {..<l}. T (w i)}) \<ge> \<gamma>*l}
    \<le> exp (- real l * (\<gamma> * ln (1/(\<mu>+\<Lambda>)) - 2 * exp(-1)))" (is "?L \<le> ?R")
proof -
  have \<mu>_ge_0: "\<mu> \<ge> 0" using assms(3) measure_nonneg order.trans by metis
  hence \<gamma>_gt_0: "\<gamma> > 0" using assms(2,5) by auto
  hence \<gamma>_ge_0: "\<gamma> \<ge> 0" by simp

  have "\<mu> + \<Lambda> * (1 - \<mu>) \<le> \<mu> + \<Lambda> * 1" using assms(2,6) \<mu>_ge_0 by auto
  also have "... \<le> \<gamma>" using assms(5) by simp
  finally have 1:"\<mu> + \<Lambda> * (1 - \<mu>) \<le> \<gamma>" by simp

  have 2: "0 < \<mu> + \<Lambda> * (1 - \<mu>)"
  proof (cases "\<mu> = 1")
    case True then show ?thesis by simp
  next
    case False
    then show ?thesis  using assms(2,6)
      by (simp add: \<mu>_ge_0 add_strict_increasing2)
  qed

  have 3: "0 < \<mu> + \<Lambda>" using \<mu>_ge_0 assms(2) by simp

  have "\<gamma> * ln (1 / (\<mu> + \<Lambda>)) - 2*exp (- 1) = \<gamma> * ln (1 / (\<mu> + \<Lambda>*1))+0 -2*exp (-1)" by simp
  also have "... \<le> \<gamma> * ln (1 / (\<mu> + \<Lambda>*(1-\<mu>)))+0-2*exp(-1)"
    using 2 3 \<gamma>_ge_0 \<mu>_ge_0 assms(2) by (intro diff_right_mono add_mono mult_left_mono
        iffD2[OF ln_le_cancel_iff] divide_left_mono divide_pos_pos) simp_all
  also have "... \<le> \<gamma> * ln (1 / (\<mu> + \<Lambda>*(1-\<mu>)))+(1-\<gamma>)*ln(1/(1-(\<mu>+\<Lambda>*(1-\<mu>))))-2* exp(-1)"
  proof (cases "\<gamma> < 1")
    case True
    hence "\<mu> + \<Lambda> * (1 - \<mu>) < 1" using 1 by simp
    thus ?thesis using assms(4) 2
      by (intro diff_right_mono add_mono mult_nonneg_nonneg order.refl ln_ge_zero) auto
  next
    case False
    hence "\<gamma>=1" using assms(4) by simp
    thus ?thesis by simp
  qed
  also have "... = (-exp(-1))+\<gamma>*ln(1/(\<mu>+\<Lambda>*(1-\<mu>)))+(-exp(-1))+(1-\<gamma>)*ln(1/(1-(\<mu>+\<Lambda>*(1-\<mu>))))"
    by simp
  also have "... \<le> \<gamma>*ln \<gamma>+\<gamma>*ln(1/(\<mu>+\<Lambda>*(1-\<mu>)))+(1-\<gamma>)*ln(1-\<gamma>)+(1-\<gamma>)*ln(1/(1-(\<mu>+\<Lambda>*(1-\<mu>))))"
    using assms(4) \<gamma>_ge_0 by (intro add_mono x_ln_x_min) auto
  also have "... = \<gamma>*(ln \<gamma>+ln(1/(\<mu>+\<Lambda>*(1-\<mu>))))+(1-\<gamma>)*(ln(1-\<gamma>)+ln(1/(1-(\<mu>+\<Lambda>*(1-\<mu>)))))"
    by (simp add:algebra_simps)
  also have "... = \<gamma> * ln (\<gamma>*(1/(\<mu>+\<Lambda>*(1-\<mu>))))+(1-\<gamma>)*ln((1-\<gamma>)*(1/(1-(\<mu>+\<Lambda>*(1-\<mu>)))))"
    using 2 1 assms(4)  by (simp add: ln_mult ln_div)
  also have "... = KL_div \<gamma> (\<mu>+\<Lambda>*(1-\<mu>))" using \<gamma>_ge_0 2 assms(4) 1 by (subst KL_div_eq') force+
  finally have 4: "\<gamma> * ln (1 / (\<mu> + \<Lambda>)) - 2 * exp (- 1) \<le> KL_div \<gamma> (\<mu> + \<Lambda> * (1 - \<mu>))"
    by simp

  have "?L \<le> exp (- real l * KL_div \<gamma> (\<mu>+\<Lambda>*(1-\<mu>)))"
    using 1 by (intro expander_kl_chernoff_bound assms)
  also have "... \<le> exp (- real l * (\<gamma> * ln (1 / (\<mu> + \<Lambda>)) - 2 * exp (- 1)))"
    by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono_neg 4) auto
  finally show ?thesis by simp
qed

definition C\<^sub>1 :: real where "C\<^sub>1 = exp 2 + exp 3 + (exp 1 - 1)"

lemma deviation_bound:
  fixes f :: "'a \<Rightarrow> real"
  assumes "l > 0"
  assumes "\<Lambda> \<in> {0<..exp (-real l * ln (real l)^3)}"
  assumes "\<And>x. x \<ge> 20 \<Longrightarrow> measure (sample_pro S) {v. f v \<ge> x} \<le> exp (-x * ln x^3)"
  shows "measure (sample_pro (\<E> l \<Lambda> S)) {\<omega>. (\<Sum>i<l. f (\<omega> i)) \<ge> C\<^sub>1 * l} \<le> exp (- real l)"  (is "?L \<le> ?R")
proof -
  let ?w = "sample_pro (\<E> l \<Lambda> S)"
  let ?p = "sample_pro S"
  let ?a = "real l*(exp 2 + exp 3)"

  define b :: real where "b = exp 1 - 1"
  have b_gt_0: "b > 0" unfolding b_def by (approximation 5)

  define L where
    "L k = measure ?w {w. exp (real k)*card{i\<in>{..<l}.f(w i)\<ge>exp(real k)} \<ge> real l/real k^2}" for k

  define k_max where "k_max = max 4 (MAX v \<in> pro_set S. nat \<lfloor>ln (f v)\<rfloor>+1)"

  have k_max_ge_4: "k_max \<ge> 4" unfolding k_max_def by simp
  have k_max_ge_3: "k_max \<ge> 3" unfolding k_max_def by simp

  have 1:"of_bool(\<lfloor>ln(max x (exp 1))\<rfloor>+1=int k)=(of_bool(x\<ge>exp(real k-1))-of_bool(x \<ge> exp k)::real)"
    (is "?L1 = ?R1") if "k \<ge> 3" for k x
  proof -
    have a1: "real k - 1 \<le> k" by simp
    have "?L1 = of_bool(\<lfloor>ln(max x (exp 1))\<rfloor>=int k-1)" by simp
    also have "... = of_bool(ln(max x (exp 1))\<in>{real k-1..<real k})" unfolding floor_eq_iff by simp
    also have "... = of_bool(exp(ln(max x (exp 1)))\<in>{exp (real k-1)..<exp (real k)})" by simp
    also have "... = of_bool(max x (exp 1) \<in>{exp (real k-1)..<exp (real k)})"
      by (subst exp_ln) (auto intro!:max.strict_coboundedI2)
    also have "... = of_bool(x \<in>{exp (real k-1)..<exp (real k)})"
    proof (cases "x \<ge> exp 1")
      case True
      then show ?thesis by simp
    next
      case False
      have "{exp (real k - 1)..<exp (real k)} \<subseteq> {exp (real k - 1)..}" by auto
      also have "... \<subseteq> {exp 1..}" using that by simp
      finally have "{exp (real k - 1)..<exp (real k)} \<subseteq> {exp 1..}" by simp
      moreover have "x \<notin> {exp 1..}" using False by simp
      ultimately have "x \<notin> {exp (real k - 1)..<exp (real k)}" by blast
      hence "of_bool(x \<in>{exp (real k-1)..<exp (real k)}) = 0" by simp
      also have "... = of_bool(max x (exp 1) \<in>{exp (real k-1)..<exp (real k)})"
        using False that by simp
      finally show ?thesis by metis
    qed
    also have "... = ?R1" using order_trans[OF iffD2[OF exp_le_cancel_iff a1]] by auto
    finally show ?thesis by simp
  qed

  have 0: "{nat \<lfloor>ln (max (f x) (exp 1))\<rfloor>+1} \<subseteq> {2..k_max}" (is "{?L1} \<subseteq> ?R2")
    if "x \<in> pro_set S" for x
  proof (cases "f x \<ge> exp 1")
    case True
    hence "?L1 = nat \<lfloor>ln (f x)\<rfloor>+1" by simp
    also have "... \<le> (MAX v \<in> pro_set S. nat \<lfloor>ln (f v)\<rfloor>+1)"
      by (intro Max_ge finite_imageI imageI that finite_pro_set)
    also have "... \<le> k_max" unfolding k_max_def by simp
    finally have le_0: "?L1 \<le> k_max" by simp
    have "(1::nat) \<le> nat \<lfloor>ln (exp (1::real))\<rfloor>" by simp
    also have "... \<le> nat \<lfloor>ln (f x)\<rfloor>"
      using True order_less_le_trans[OF exp_gt_zero]
      by (intro nat_mono floor_mono iffD2[OF ln_le_cancel_iff]) auto
    finally have "1 \<le> nat \<lfloor>ln (f x)\<rfloor>" by simp
    hence "?L1 \<ge> 2" using True by simp
    hence "?L1 \<in> ?R2" using le_0 by simp
    then show ?thesis by simp
  next
    case False
    hence "{?L1} = {2}" by simp
    also have "... \<subseteq> ?R2" using k_max_ge_3 by simp
    finally show ?thesis by simp
  qed

  have 2:"(\<Sum>i<l. f (w i)) \<le> ?a+b*(\<Sum>k=3..<k_max. exp k * card {i\<in>{..<l}. f (w i)\<ge>exp k})"
    (is "?L1 \<le> ?R1") if "w \<in> pro_set (\<E> l \<Lambda> S)" for w
  proof -
    have s_w: "w i \<in> pro_set S" for i
      using that expander_pro_range[OF assms(1)] assms(2)
      unfolding set_sample_pro[where S="\<E> l \<Lambda> S"] by auto

    have "?L1 \<le> (\<Sum>i<l. exp( ln (max (f (w i)) (exp 1))))"
      by (intro sum_mono) (simp add:less_max_iff_disj)
    also have "... \<le> (\<Sum>i<l. exp (of_nat (nat \<lfloor>ln (max (f (w i)) (exp 1))\<rfloor>+1)))"
      by (intro sum_mono iffD2[OF exp_le_cancel_iff]) linarith
    also have "... = (\<Sum>i<l. (\<Sum>k=2..k_max. exp k * of_bool (k=nat \<lfloor>ln (max (f (w i))(exp 1))\<rfloor>+1)))"
      using Int_absorb1[OF 0] s_w by (intro sum.cong map_cong refl)
       (simp add:of_bool_def if_distrib if_distribR sum.If_cases)
    also have "...=
      (\<Sum>i<l.(\<Sum>k\<in>(insert 2{3..k_max}). exp k* of_bool(k=nat\<lfloor>ln(max(f (w i))(exp 1))\<rfloor>+1)))"
      using k_max_ge_3 by (intro_cong "[\<sigma>\<^sub>1 sum_list]" more:map_cong sum.cong) auto
    also have "... = (\<Sum>i<l. exp 2* of_bool (2=nat \<lfloor>ln (max (f (w i))(exp 1))\<rfloor>+1) +
      (\<Sum>k=3..k_max. exp k * of_bool (k=nat \<lfloor>ln (max (f (w i))(exp 1))\<rfloor>+1)))"
      by (subst sum.insert) auto
    also have "...\<le>(\<Sum>i<l. exp 2*1+(\<Sum>k=3..k_max. exp k* of_bool(k=nat\<lfloor>ln(max(f (w i))(exp 1))\<rfloor>+1)))"
      by (intro sum_mono add_mono mult_left_mono) auto
    also have "...=(\<Sum>i<l. exp 2+(\<Sum>k=3..k_max. exp k* of_bool(\<lfloor>ln(max(f (w i))(exp 1))\<rfloor>+1=int k)))"
      by (intro_cong "[\<sigma>\<^sub>1 sum_list,\<sigma>\<^sub>1 of_bool, \<sigma>\<^sub>2(+),\<sigma>\<^sub>2(*)]" more:map_cong sum.cong) auto
    also have "... =
      (\<Sum>i<l. exp 2+(\<Sum>k=3..k_max. exp k*(of_bool(f (w i)\<ge>exp (real k-1))-of_bool(f (w i)\<ge>exp k))))"
      by (intro_cong "[\<sigma>\<^sub>1 sum_list,\<sigma>\<^sub>1 of_bool, \<sigma>\<^sub>2(+),\<sigma>\<^sub>2(*)]" more:map_cong sum.cong 1) auto
    also have "... = (\<Sum>i<l.
      exp 2+(\<Sum>k=2+1..<k_max+1. exp k*(of_bool(f (w i)\<ge>exp(real k-1))-of_bool(f (w i)\<ge>exp k))))"
      by (intro_cong "[\<sigma>\<^sub>2(+)]" more:map_cong sum.cong) auto
    also have "... = (\<Sum>i<l.
      exp 2+(\<Sum>k=2..<k_max. exp (k+1)*(of_bool(f (w i)\<ge>exp k)-of_bool(f (w i)\<ge>exp (Suc k)))))"
      by (subst sum.shift_bounds_nat_ivl) simp
    also have "... = (\<Sum>i<l. exp 2+ (\<Sum>k=2..<k_max. exp (k+1)* of_bool(f (w i)\<ge>exp k))-
      (\<Sum>k=2..<k_max. exp (k+1)* of_bool(f (w i)\<ge>exp (k+1))))"
      by (simp add:sum_subtractf algebra_simps)
    also have "... = (\<Sum>i<l. exp 2+ (\<Sum>k=2..<k_max. exp (k+1)* of_bool(f (w i)\<ge>exp k))-
      (\<Sum>k=3..<k_max+1. exp k* of_bool(f (w i)\<ge>exp k)))"
      by (subst sum.shift_bounds_nat_ivl[symmetric]) (simp cong:sum.cong)
    also have "... = (\<Sum>i<l. exp 2+ (\<Sum>k\<in> insert 2 {3..<k_max}. exp (k+1)* of_bool(f (w i)\<ge>exp k))-
      (\<Sum>k=3..<k_max+1. exp k* of_bool(f (w i)\<ge>exp k)))"
      using k_max_ge_3 by (intro_cong "[\<sigma>\<^sub>2 (+), \<sigma>\<^sub>2 (-)]" more: map_cong sum.cong) auto
    also have "... = (\<Sum>i<l. exp 2+ exp 3 * of_bool (f (w i) \<ge> exp 2) +
      (\<Sum>k=3..<k_max. exp (k+1)* of_bool(f (w i)\<ge>exp k)) -
      (\<Sum>k=3..<k_max+1. exp k* of_bool(f (w i)\<ge>exp k)))"
      by (subst sum.insert) (simp_all add:algebra_simps)
    also have "... \<le> (\<Sum>i<l. exp 2+exp 3+(\<Sum>k=3..<k_max. exp (k+1)* of_bool(f (w i)\<ge>exp k))-
      (\<Sum>k=3..<k_max+1. exp k* of_bool(f (w i)\<ge>exp k)))"
      by (intro sum_mono add_mono diff_mono) auto
    also have "... = (\<Sum>i<l. exp 2+exp 3+(\<Sum>k=3..<k_max. exp (k+1)* of_bool(f (w i)\<ge>exp k))-
      (\<Sum>k\<in> insert k_max {3..<k_max}. exp k* of_bool(f (w i)\<ge>exp k)))"
      using k_max_ge_3 by (intro_cong "[\<sigma>\<^sub>2 (+), \<sigma>\<^sub>2 (-)]" more: map_cong sum.cong) auto
    also have "... = (\<Sum>i<l. exp 2+exp 3+(\<Sum>k=3..<k_max. (exp (k+1)-exp k)* of_bool(f (w i)\<ge>exp k))-
      (exp k_max * of_bool (f (w i)\<ge> exp k_max)))"
      by (subst sum.insert) (auto simp add:sum_subtractf algebra_simps)
    also have "...\<le>(\<Sum>i<l. exp 2+exp 3+(\<Sum>k=3..<k_max. (exp (k+1)-exp k)* of_bool(f(w i)\<ge>exp k))-0)"
      by (intro sum_mono add_mono diff_mono) auto
    also have "... \<le>(\<Sum>i<l. exp 2+exp 3+ (\<Sum>k=3..<k_max. (exp (k+1)-exp k)* of_bool(f(w i)\<ge>exp k)))"
      by auto
    also have "... = (\<Sum>i<l. exp 2+exp 3+(\<Sum>k=3..<k_max.(exp 1-1)*(exp k* of_bool(f (w i)\<ge>exp k))))"
      by (simp add:exp_add algebra_simps)
    also have "... = (\<Sum>i<l. exp 2+exp 3+b*(\<Sum>k=3..<k_max. exp k* of_bool(f (w i)\<ge>exp k)))"
      unfolding b_def by (subst sum_distrib_left) simp
    also have "... = ?a+b*(\<Sum>i<l. (\<Sum>k=3..<k_max. exp k* of_bool(f (w i)\<ge>exp k)))"
       by (simp add: sum_distrib_left[symmetric])
    also have "... = ?R1"
      by (subst sum.swap) (simp add:ac_simps Int_def)
    finally show ?thesis by simp
  qed

  have 3: "\<exists>k\<in>{3..<k_max}. g k \<ge> l/real k^2" if "(\<Sum>k=3..<k_max. g k) \<ge> real l" for g
  proof (rule ccontr)
    assume a3: "\<not>(\<exists>k\<in>{3..<k_max}. g k \<ge> l/real k^2)"
    hence "g k < l/real k^2" if "k \<in>{3..<k_max}" for k using that by force
    hence "(\<Sum>k=3..<k_max. g k) < (\<Sum>k=3..<k_max. l/real k^2)"
      using k_max_ge_4 by (intro sum_strict_mono) auto
    also have "... \<le> (\<Sum>k=3..<k_max. l/ (real k*(real k-1)))"
      by (intro sum_mono divide_left_mono) (auto simp:power2_eq_square)
    also have "... = l * (\<Sum>k=3..<k_max. 1 / (real k-1) - 1/k)"
      by (simp add:sum_distrib_left field_simps)
    also have "... = l * (\<Sum>k=2+1..<(k_max-1)+1. (-1)/k - (-1) / (real k-1))"
      by (intro sum.cong arg_cong2[where f="(*)"]) auto
    also have "... = l * (\<Sum>k=2..<(k_max-1). (-1)/(Suc k) - (-1) / k)"
      by (subst sum.shift_bounds_nat_ivl) auto
    also have "... = l * (1/2 - 1 / real (k_max - 1))"
      using k_max_ge_3 by (subst sum_Suc_diff') auto
    also have "... \<le> real l * (1 - 0)" by (intro mult_left_mono diff_mono) auto
    also have "... = l" by simp
    finally have "(\<Sum>k=3..<k_max. g k) < l" by simp
    thus "False" using that by simp
  qed

  have 4: "L k \<le> exp(-real l-k+2)" if "k \<ge> 3" for k
  proof (cases "k \<le> ln l")
    case True
    define \<gamma> where "\<gamma> = 1 / (real k)\<^sup>2 / exp (real k)"
    define \<mu> where "\<mu> = exp (-exp(real k) * real k^3)"

    have exp_k_ubound: "exp (real k) \<le> real l" using True assms(1) by (simp add: ln_ge_iff)

    have "20 \<le> exp (3::real)" by (approximation 10)
    also have "... \<le> exp (real k)" using that by simp
    finally have exp_k_lbound: "20 \<le> exp (real k)" by simp

    have "measure (sample_pro S) {v. f v\<ge>exp(real k)} \<le> exp (-exp(real k) * ln (exp (real k)) ^ 3)"
      by (intro assms(3) exp_k_lbound)
    also have "... = exp (-(exp(real k) * real k^3))" by simp
    finally have \<mu>_bound: "measure (sample_pro S) {v. f v \<ge> exp (real k)} \<le> \<mu>" by (simp add:\<mu>_def)

    have "\<mu>+\<Lambda> \<le> exp (-exp(real k) * real k^3) + exp (- real l * ln (real l) ^ 3)"
      unfolding \<mu>_def using assms by (intro add_mono) auto
    also have "... =  exp (-(exp(real k) * real k^3)) + exp (- (real l * ln (real l) ^ 3))" by simp
    also have "... \<le> exp (-(exp(real k) * real k^3)) + exp (-(exp(real k) * ln(exp (real k))^3))"
      using assms(1) exp_k_ubound by (intro add_mono iffD2[OF exp_le_cancel_iff] le_imp_neg_le
          mult_mono power_mono iffD2[OF ln_le_cancel_iff]) simp_all
    also have "... = 2 * exp (-exp(real k) * real k^3)" by simp
    finally have \<mu>_\<Lambda>_bound: "\<mu>+\<Lambda> \<le> 2 * exp (-exp(real k) * real k^3)" by simp

    have "\<mu>+\<Lambda> \<le> 2 * exp (-exp(real k) * real k^3)" by (intro \<mu>_\<Lambda>_bound)
    also have "... = exp (-exp(real k) * real k^3 + ln 2)" unfolding exp_add by simp
    also have "... = exp (-(exp(real k) * real k^3 - ln 2))" by simp
    also have "... \<le> exp (-((1+ real k) * real k^3 - ln 2))"
      using that by (intro iffD2[OF exp_le_cancel_iff] le_imp_neg_le diff_mono mult_right_mono
          exp_ge_add_one_self_aux) auto
    also have "... = exp (-(real k^4 + (real k^3- ln 2)))"
      by (simp add:power4_eq_xxxx power3_eq_cube algebra_simps)
    also have "... \<le> exp (-(real k^4 + (2^3- ln 2)))" using that
      by (intro iffD2[OF exp_le_cancel_iff] le_imp_neg_le add_mono diff_mono power_mono) auto
    also have "... \<le> exp (-(real k^4 + 0))"
      by (intro iffD2[OF exp_le_cancel_iff] le_imp_neg_le add_mono order.refl) (approximation 5)
    also have "... \<le> exp (-(real k^3 * real k))"
      by (simp add:power4_eq_xxxx power3_eq_cube algebra_simps)
    also have "... \<le> exp (-(2^3 * real k))" using that
      by (intro iffD2[OF exp_le_cancel_iff] le_imp_neg_le mult_right_mono power_mono) auto
    also have "... \<le> exp (-3* real k)" by (intro iffD2[OF exp_le_cancel_iff]) auto
    also have "... = exp (-(real k + 2 * real k) )" by simp
    also have "... \<le> exp (-(real k + 2 * ln k) )"
      using that
      by (intro iffD2[OF exp_le_cancel_iff] le_imp_neg_le add_mono mult_left_mono ln_bound) auto
    also have "... = exp (-(real k + ln(k^2)))" using that by (subst ln_powr[symmetric]) auto
    also have "... = \<gamma>"
      using that unfolding \<gamma>_def exp_minus exp_add inverse_eq_divide by (simp add:algebra_simps)
    finally have \<mu>_\<Lambda>_le_\<gamma>: "\<mu>+\<Lambda>\<le>\<gamma>" by simp

    have "\<mu> \<ge> 0" unfolding \<mu>_def by simp
    hence \<mu>_\<Lambda>_gt_0: "\<mu>+\<Lambda>>0" using assms(2) by auto

    have "\<gamma> = 1 / ((real k)\<^sup>2 * exp (real k))" unfolding \<gamma>_def by simp
    also have "... \<le> 1 / (2^2 * exp 2)"
      using that by (intro divide_left_mono mult_mono power_mono) (auto)
    finally have \<gamma>_ubound: "\<gamma> \<le> 1 / (4 * exp 2)" by simp

    have "\<gamma> \<le> 1 / (4 * exp 2)" by (intro \<gamma>_ubound)
    also have "... < 1" by (approximation 5)
    finally have \<gamma>_lt_1: "\<gamma> < 1" by simp

    have \<gamma>_ge_0: "\<gamma> \<ge> 0" using that unfolding \<gamma>_def by (intro divide_nonneg_pos) auto
    have \<mu>_le_1: "\<mu> \<le> 1" unfolding \<mu>_def by simp

    have "L k = measure ?w {w. \<gamma>*l \<le> real (card {i \<in> {..<l}. exp (real k) \<le> f (w i)})}"
      unfolding L_def \<gamma>_def using that
      by (intro_cong "[\<sigma>\<^sub>2 measure]" more:Collect_cong) (simp add:field_simps)
    also have "... \<le> exp (- real l * (\<gamma> * ln (1/(\<mu>+\<Lambda>)) - 2 * exp(-1)))"
      using \<gamma>_lt_1 assms(2) by (intro walk_tail_bound \<mu>_bound assms(1) \<mu>_\<Lambda>_le_\<gamma> \<mu>_le_1) auto
    also have "... = exp ( real l * (\<gamma> * ln (\<mu>+\<Lambda>) + 2 * exp (-1)))"
      using \<mu>_\<Lambda>_gt_0 by (simp_all add:ln_div algebra_simps)
    also have "... \<le> exp ( real l * (\<gamma> * ln (2 * exp (-exp(real k) * real k^3)) + 2 * exp(-1)))"
      using \<mu>_\<Lambda>_gt_0 \<mu>_\<Lambda>_bound \<gamma>_ge_0
      by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono add_mono iffD2[OF ln_le_cancel_iff])
       simp_all
    also have "... = exp (real l * (\<gamma> * (ln 2 - exp (real k) * real k ^ 3) + 2 * exp (- 1)))"
      by (simp add:ln_mult)
    also have "... = exp (real l * (\<gamma> * ln 2 - real k + 2 * exp (- 1)))"
      using that unfolding \<gamma>_def by (simp add:field_simps power2_eq_square power3_eq_cube)
    also have "... \<le> exp (real l * (ln 2 / (4 * exp 2) - real k + 2 * exp (-1)))"
      using \<gamma>_ubound by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono add_mono diff_mono)
        (auto simp:divide_simps)
    also have "... = exp (real l * (ln 2 / (4 * exp 2) + 2 *exp(-1) - real k))"
      by simp
    also have "... \<le> exp (real l * (1 - real k))"
      by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono diff_mono order.refl of_nat_0_le_iff)
       (approximation 12)
    also have "... \<le> exp (-real l - real k + 2)"
    proof (intro iffD2[OF exp_le_cancel_iff])
      have "1 * (real k-2) \<le> real l * (real k-2)"
        using assms(1) that by (intro mult_right_mono) auto
      thus "real l * (1 - real k) \<le> - real l - real k + 2" by argo
    qed
    finally show ?thesis by simp
  next
    case False
    hence k_gt_l: "k \<ge> ln l" by simp
    define \<gamma> where "\<gamma> = 1 / (real k)\<^sup>2 / exp (real k)"

    have "20 \<le> exp (3::real)" by (approximation 10)
    also have "... \<le> exp (real k)" using that by simp
    finally have exp_k_lbound: "20 \<le> exp (real k)" by simp

    have \<gamma>_gt_0: "0 < \<gamma>" using that unfolding \<gamma>_def by (intro divide_pos_pos) auto

    hence \<gamma>_l_gt_0: "0 < \<gamma> * real l" using assms(1) by auto

    have "L k = measure ?w {w. \<gamma>*l \<le> real (card {i \<in> {..<l}. exp (real k) \<le> f (w i)})}"
      unfolding L_def \<gamma>_def using that
      by (intro_cong "[\<sigma>\<^sub>2 measure]" more:Collect_cong) (simp add:field_simps)
    also have "... \<le> (\<integral>w. real (card {i \<in> {..<l}. exp (real k) \<le> f (w i)}) \<partial>?w) / (\<gamma>*l)"
      by (intro pmf_markov \<gamma>_l_gt_0) simp_all
    also have "... = (\<integral>w. (\<Sum>i<l. of_bool (exp(real k) \<le> f (w i)))\<partial>?w) / (\<gamma>*l)"
      by (intro_cong "[\<sigma>\<^sub>2 (/)]" more:integral_cong_AE AE_pmfI) (auto simp add:Int_def)
    also have "... = (\<Sum>i<l. (\<integral>w. of_bool (exp(real k) \<le> f (w i))\<partial>?w)) / (\<gamma>*l)"
      by (intro_cong "[\<sigma>\<^sub>2 (/)]" more:integral_sum integrable_measure_pmf_finite finite_pro_set)
    also have "... = (\<Sum>i<l. (\<integral>v. of_bool (exp(real k) \<le> f v)\<partial>(map_pmf (\<lambda>w. w i) ?w))) / (\<gamma>*l)"
      by simp
    also have "... = (\<Sum>i<l. (\<integral>v. of_bool (exp(real k) \<le> f v)\<partial>?p)) / (\<gamma>*l)" using assms(1,2)
      by (intro_cong "[\<sigma>\<^sub>2(/),\<sigma>\<^sub>2(integral\<^sup>L),\<sigma>\<^sub>1 measure_pmf]" more:sum.cong expander_uniform_property)
        simp_all
    also have "... = (\<Sum>i<l. (\<integral>v. indicat_real {v. (exp(real k) \<le> f v)} v\<partial>?p)) / (\<gamma>*l)"
      by (intro_cong "[\<sigma>\<^sub>2(/),\<sigma>\<^sub>2(integral\<^sup>L)]" more:sum.cong) auto
    also have "... = (\<Sum>i<l. (measure ?p {v. f v \<ge> exp (real k)})) / (\<gamma>*l)" by simp
    also have "... \<le> (\<Sum>i<l. exp (- exp (real k) * ln (exp (real k)) ^ 3)) / (\<gamma>*l)"
      using \<gamma>_l_gt_0 by (intro divide_right_mono sum_mono assms(3) exp_k_lbound) auto
    also have "... = exp (- exp (real k) * real k ^ 3) / \<gamma>" using assms(1) by simp
    also have "... = exp (real k + ln (k^2) - exp (real k) * real k ^ 3)"
      using that unfolding \<gamma>_def
      by (simp add:exp_add exp_diff exp_minus algebra_simps inverse_eq_divide)
    also have "... = exp (real k + 2 * ln k - exp (real k) * real k ^ 3)"
      using that by (subst ln_powr[symmetric]) auto
    also have "... \<le> exp (real k + 2 * real k - exp (ln l) * real k^3)"
      using that k_gt_l ln_bound
      by (intro iffD2[OF exp_le_cancel_iff] add_mono diff_mono mult_left_mono mult_right_mono) auto
    also have "... = exp (3* real k - l * (real k^3-1) -l)"
      using assms(1) by (subst exp_ln) (auto simp add:algebra_simps)
    also have "... \<le> exp (3* real k - 1 * (real k^3-1) -l)"
      using assms(1) that by (intro iffD2[OF exp_le_cancel_iff] diff_mono mult_right_mono) auto
    also have "... = exp (3* real k - real k * real k^2-1 -l+2)"
      by (simp add:power2_eq_square power3_eq_cube)
    also have "... \<le> exp (3* real k - real k * 2^2-0 -l+2)"
      using assms(1) that
      by (intro iffD2[OF exp_le_cancel_iff] add_mono diff_mono mult_left_mono power_mono) auto
    also have "... = exp (- real l - real k + 2)" by simp
    finally show ?thesis by simp
  qed

  have "?L \<le> measure ?w
    {w. ?a+b*(\<Sum>k=3..<k_max. exp (real k) * card {i\<in>{..<l}. f (w i)\<ge>exp (real k)}) \<ge> C\<^sub>1*l}"
    using order_trans[OF _ 2] by (intro pmf_mono) simp
  also have "... = measure ?w
    {w. (\<Sum>k=3..<k_max. exp(real k)*card{i\<in>{..<l}.f(w i)\<ge>exp(real k)})\<ge>l}"
    unfolding C\<^sub>1_def b_def[symmetric] using b_gt_0
    by (intro_cong "[\<sigma>\<^sub>2 measure]" more:Collect_cong) (simp add:algebra_simps)
  also have "... \<le> measure ?w
    {w. (\<exists>k\<in>{3..<k_max}. exp (real k)*card{i\<in>{..<l}.f(w i)\<ge>exp(real k)} \<ge> real l/real k^2)}"
    using 3 by (intro pmf_mono) simp
  also have "... = measure ?w
    (\<Union>k\<in>{3..<k_max}. {w. exp (real k)*card{i\<in>{..<l}.f(w i)\<ge>exp(real k)} \<ge> real l/real k^2})"
    by (intro_cong "[\<sigma>\<^sub>2 measure]") auto
  also have "... \<le> (\<Sum>k=3..<k_max. L k)"
    unfolding L_def by (intro finite_measure.finite_measure_subadditive_finite) auto
  also have "... \<le> (\<Sum>k=3..<k_max. exp (- real l - real k + 2))" by (intro sum_mono 4) auto
  also have "... = (\<Sum>k=0+3..<(k_max-3)+3. exp (- real l - real k + 2))"
    using k_max_ge_3 by (intro sum.cong) auto
  also have "... = (\<Sum>k=0..<k_max-3. exp (-1 - real l - real k))"
    by (subst sum.shift_bounds_nat_ivl) ( simp add:algebra_simps)
  also have "... = exp(-1-real l) * (\<Sum>k<k_max-3. exp (real k*(-1)))"
    using atLeast0LessThan
    by (simp add:exp_diff exp_add sum_distrib_left exp_minus inverse_eq_divide)
  also have "... = exp (-1-real l) * ((exp (- 1) ^ (k_max - 3) - 1) / (exp (- 1) - 1))"
    unfolding exp_of_nat_mult by (subst geometric_sum) auto
  also have "... = exp(-1-real l) * (1-exp (- 1) ^ (k_max - 3)) / (1-exp (- 1))"
    by (simp add:field_simps)
  also have "... \<le> exp(-1-real l) * (1-0) / (1-exp (- 1))"
    using k_max_ge_3 by (intro mult_left_mono divide_right_mono diff_mono) auto
  also have "... = exp (-real l) * (exp (-1) / (1-exp(-1)))"
    by (simp add:exp_diff exp_minus inverse_eq_divide)
  also have "... \<le> exp (-real l) * 1"
    by (intro mult_left_mono exp_ge_zero) (approximation 10)
  finally show ?thesis by simp
qed

unbundle no intro_cong_syntax

end