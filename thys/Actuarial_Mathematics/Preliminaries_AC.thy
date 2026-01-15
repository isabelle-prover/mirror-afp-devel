theory Preliminaries_AC
  imports "HOL-Library.Rewrite" "HOL-Probability.Probability"
begin

notation powr (infixr \<open>.^\<close> 80)

section \<open>Preliminary Lemmas\<close>

lemma Collect_conj_eq2: "{x \<in> A. P x \<and> Q x} = {x \<in> A. P x} \<inter> {x \<in> A. Q x}"
  by blast

lemma vimage_compl_atMost:
  fixes f :: "'a \<Rightarrow> 'b::linorder"
  shows "-(f -` {..y}) = f -` {y<..}"
  by fastforce

context linorder
begin

lemma Icc_minus_Ico:
  fixes a b
  assumes "a \<le> b"
  shows  "{a..b} - {a..<b} = {b}"
  using assms by auto

lemma Icc_minus_Ioc:
  fixes a b
  assumes "a \<le> b"
  shows "{a..b} - {a<..b} = {a}"
  using assms by auto

(* To be included in Lebesgue_Stieltjes_Integral *)
(* subsubsection \<open>Intersection\<close> in Set_Interval.thy *)
lemma Int_atLeastAtMost_Unbounded[simp]: "{a..} Int {..b} = {a..b}"
  by auto

lemma Int_greaterThanAtMost_Unbounded[simp]: "{a<..} Int {..b} = {a<..b}"
  by auto

lemma Int_atLeastLessThan_Unbounded[simp]: "{a..} Int {..<b} = {a..<b}"
  by auto

lemma Int_greaterThanLessThan_Unbounded[simp]: "{a<..} Int {..<b} = {a<..<b}"
  by auto

end

lemma Ico_real_nat_disjoint:
  "disjoint_family (\<lambda>n::nat. {a + real n ..< a + real n + 1})" for a::real
  unfolding disjoint_family_on_def by fastforce

corollary Ico_nat_disjoint: "disjoint_family (\<lambda>n::nat. {real n ..< real n + 1})"
  using Ico_real_nat_disjoint[of 0] by simp

lemma Ico_real_nat_union: "(\<Union>n::nat. {a + real n ..< a + real n + 1}) = {a..}" for a::real
proof
  show "(\<Union>n::nat. {a + real n ..< a + real n + 1}) \<subseteq> {a..}" by auto
next
  show "{a..} \<subseteq> (\<Union>n::nat. {a + real n ..< a + real n + 1})"
  proof
    fix x assume "x \<in> {a..}"
    hence "a \<le> x" by simp
    hence "nat \<lfloor>x-a\<rfloor> \<le> x-a \<and> x-a < nat \<lfloor>x-a\<rfloor> + 1" by linarith
    hence "a + nat \<lfloor>x-a\<rfloor> \<le> x \<and> x < a + nat \<lfloor>x-a\<rfloor> + 1" by auto
    thus "x \<in> (\<Union>n::nat. {a + real n ..< a + real n + 1})" by auto
  qed
qed

corollary Ico_nat_union: "(\<Union>n::nat. {real n ..< real n + 1}) = {0..}"
  using Ico_real_nat_union[of 0] by simp

lemma Ico_nat_union_finite: "(\<Union>(n::nat)<m. {real n ..< real n + 1}) = {0..<m}"
proof
  show "(\<Union>(n::nat)<m. {real n ..< real n + 1}) \<subseteq> {0..<m}" by auto
next
  show "{0..<m} \<subseteq> (\<Union>(n::nat)<m. {real n ..< real n + 1})"
  proof
    fix x::real
    assume \<star>: "x \<in> {0..<m}"
    hence "nat \<lfloor>x\<rfloor> < m" using of_nat_floor by fastforce
    moreover with \<star> have "nat \<lfloor>x\<rfloor> \<le> x \<and> x < nat \<lfloor>x\<rfloor> + 1"
      by (metis Nat.add_0_right atLeastLessThan_iff le_nat_floor
          less_one linorder_not_le nat_add_left_cancel_le of_nat_floor)
    ultimately show "x \<in> (\<Union>(n::nat)<m. {real n ..< real n + 1})"
      unfolding atLeastLessThan_def by force
  qed
qed

lemma seq_part_multiple: fixes m n :: nat assumes "m \<noteq> 0" defines "A \<equiv> \<lambda>i::nat. {i*m ..< (i+1)*m}"
  shows "\<forall>i j. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}" and "(\<Union>i<n. A i) = {..< n*m}"
proof -
  { fix i j :: nat
    have "i \<noteq> j \<Longrightarrow> A i \<inter> A j = {}"
    proof (erule contrapos_np)
      assume "A i \<inter> A j \<noteq> {}"
      then obtain k where "k \<in> A i \<inter> A j" by blast
      hence "i*m < (j+1)*m \<and> j*m < (i+1)*m" unfolding A_def by force
      hence "i < j+1 \<and> j < i+1" using mult_less_cancel2 by blast
      thus "i = j" by force
    qed }
  thus "\<forall>i j. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}" by blast
next
  show "(\<Union>i<n. A i) = {..< n*m}"
  proof
    show "(\<Union>i<n. A i) \<subseteq> {..< n*m}"
    proof
      fix x::nat
      assume "x \<in> (\<Union>i<n. A i)"
      then obtain i where i_n: "i < n" and i_x: "x < (i+1)*m" unfolding A_def by force
      hence "i+1 \<le> n" by linarith
      hence "x < n*m" by (meson less_le_trans mult_le_cancel2 i_x)
      thus "x \<in> {..< n*m}"
        using diff_mult_distrib mult_1 i_n by auto
    qed
  next
    show "{..< n*m} \<subseteq> (\<Union>i<n. A i)"
    proof
      fix x::nat
      let ?i = "x div m"
      assume "x \<in> {..< n*m}"
      hence "?i < n" by (simp add: less_mult_imp_div_less)
      moreover have "?i*m \<le> x \<and> x < (?i+1)*m"
        using assms div_times_less_eq_dividend dividend_less_div_times by auto
      ultimately show "x \<in> (\<Union>i<n. A i)" unfolding A_def by force
    qed
  qed
qed

lemma frontier_Icc_real: "frontier {a..b} = {a, b}" if "a \<le> b" for a b :: real
  unfolding frontier_def using that by force

lemma(in field) divide_mult_cancel[simp]: fixes a b assumes "b \<noteq> 0"
  shows "a / b * b = a"
  by (simp add: assms)

lemma inverse_powr: "(1/a).^b = a.^-b" if "a > 0" for a b :: real
  by (simp add: powr_divide powr_minus_divide)

lemma geometric_increasing_sum_aux: "(1-r)^2 * (\<Sum>k<n. (k+1)*r^k) = 1 - (n+1)*r^n + n*r^(n+1)"
  for n::nat and r::real
proof (induct n)
  case 0
  thus ?case by simp
next
  case (Suc n)
  thus ?case
    apply (simp only: sum.lessThan_Suc)
    apply (subst distrib_left)
    apply (subst Suc.hyps)
    by (subst power2_diff) (simp add: field_simps power2_eq_square)
qed

lemma geometric_increasing_sum: "(\<Sum>k<n. (k+1)*r^k) = (1 - (n+1)*r^n + n*r^(n+1)) / (1-r)^2"
  if "r \<noteq> 1" for n::nat and r::real
  by (subst geometric_increasing_sum_aux[THEN sym]) (simp add: that)

(* Already included in Topologial_Spaces.thy *)
lemma Lim_cong:
  assumes "\<forall>\<^sub>F x in F. f x = g x"
  shows "Lim F f = Lim F g"
  unfolding t2_space_class.Lim_def using tendsto_cong assms by fastforce

lemma LIM_zero_iff': "((\<lambda>x. l - f x) \<longlongrightarrow> 0) F = (f \<longlongrightarrow> l) F"
  for f :: "'a \<Rightarrow> 'b::real_normed_vector"
  unfolding tendsto_iff dist_norm
  by (rewrite minus_diff_eq[THEN sym], rewrite norm_minus_cancel) simp

lemma antimono_onI:
  "(\<And>r s. r \<in> A \<Longrightarrow> s \<in> A \<Longrightarrow> r \<le> s \<Longrightarrow> f r \<ge> f s) \<Longrightarrow> antimono_on A f"
  by (rule monotone_onI)

lemma antimono_onD:
  "\<lbrakk>antimono_on A f; r \<in> A; s \<in> A; r \<le> s\<rbrakk> \<Longrightarrow> f r \<ge> f s"
  by (rule monotone_onD)

lemma antimono_imp_mono_on: "antimono f \<Longrightarrow> antimono_on A f"
  by (simp add: antimonoD antimono_onI)

lemma antimono_on_subset: "antimono_on A f \<Longrightarrow> B \<subseteq> A \<Longrightarrow> antimono_on B f"
  by (rule monotone_on_subset)

lemma mono_on_antimono_on:
  fixes f :: "'a::order \<Rightarrow> 'b::ordered_ab_group_add"
  shows "mono_on A f \<longleftrightarrow> antimono_on A (\<lambda>r. - f r)"
  by (simp add: monotone_on_def)

lemmas mono_antimono = mono_on_antimono_on[where A=UNIV]

lemma mono_on_at_top_le:
  fixes a :: "'a::linorder" and b :: "'b::{order_topology, linordered_ab_group_add}"
    and f :: "'a \<Rightarrow> 'b"
  assumes f_mono: "mono_on {a..} f" and f_to_l: "(f \<longlongrightarrow> l) at_top"
  shows "\<And>x. x \<in> {a..} \<Longrightarrow> f x \<le> l"
proof -
  { fix b assume b_a: "b \<ge> a" and fb_l: "\<not> f b \<le> l"
    let ?eps = "f b - l"
    have lim_top: "\<And>S. open S \<Longrightarrow> l \<in> S \<Longrightarrow> eventually (\<lambda>x. f x \<in> S) at_top"
      using assms tendsto_def by auto
    have "eventually (\<lambda>x. f x \<in> {l - ?eps <..< l + ?eps}) at_top"
      using fb_l by (intro lim_top; force)
    then obtain N where fn_in: "\<And>n. n \<ge> N \<Longrightarrow> f n \<in> {l - ?eps <..< l + ?eps}"
      using eventually_at_top_linorder by metis
    let ?n = "max b N"
    have "f ?n < f b" using fn_in by force
    moreover have "f ?n \<ge> f b" using f_mono b_a by (simp add: le_max_iff_disj mono_on_def)
    ultimately have False by simp }
  thus "\<And>x. x \<in> {a..} \<Longrightarrow> f x \<le> l"
    by blast
qed

corollary mono_at_top_le:
  fixes b :: "'b::{order_topology, linordered_ab_group_add}" and f :: "'a::linorder \<Rightarrow> 'b"
  assumes "mono f" and "(f \<longlongrightarrow> b) at_top"
  shows "f x \<le> b"
  using mono_on_at_top_le assms by (metis atLeast_iff mono_imp_mono_on nle_le)

lemma mono_on_at_bot_ge:
  fixes a :: "'a::linorder" and b :: "'b::{order_topology, linordered_ab_group_add}"
    and f :: "'a \<Rightarrow> 'b"
  assumes f_mono: "mono_on {..a} f" and f_to_l: "(f \<longlongrightarrow> l) at_bot"
  shows "\<And>x. x \<in> {..a} \<Longrightarrow> f x \<ge> l"
proof -
  { fix b assume b_a: "b \<le> a" and fb_l: "\<not> f b \<ge> l"
    let ?eps = "l - f b"
    have lim_bot: "\<And>S. open S \<Longrightarrow> l \<in> S \<Longrightarrow> eventually (\<lambda>x. f x \<in> S) at_bot"
      using assms tendsto_def by auto
    have "eventually (\<lambda>x. f x \<in> {l - ?eps <..< l + ?eps}) at_bot"
      using fb_l by (intro lim_bot; force)
    then obtain N where fn_in: "\<And>n. n \<le> N \<Longrightarrow> f n \<in> {l - ?eps <..< l + ?eps}"
      using eventually_at_bot_linorder by metis
    let ?n = "min b N"
    have "f ?n > f b" using fn_in by force
    moreover have "f ?n \<le> f b" using f_mono b_a by (simp add: min.coboundedI1 mono_onD)
    ultimately have False by simp }
  thus "\<And>x. x \<in> {..a} \<Longrightarrow> f x \<ge> l"
    by blast
qed

corollary mono_at_bot_ge:
  fixes b :: "'b::{order_topology, linordered_ab_group_add}" and f :: "'a::linorder \<Rightarrow> 'b"
  assumes "mono f" and "(f \<longlongrightarrow> b) at_bot"
  shows "\<And>x. f x \<ge> b"
  using mono_on_at_bot_ge assms by (metis atMost_iff mono_imp_mono_on nle_le)

lemma antimono_on_at_top_ge:
  fixes a :: "'a::linorder" and b :: "'b::{order_topology, linordered_ab_group_add}"
    and f :: "'a \<Rightarrow> 'b"
  assumes f_antimono: "antimono_on {a..} f" and f_to_l: "(f \<longlongrightarrow> l) at_top"
  shows "\<And>x. x \<in> {a..} \<Longrightarrow> f x \<ge> l"
proof -
  { fix b assume b_a: "b \<ge> a" and fb_l: "\<not> f b \<ge> l"
    let ?eps = "l - f b"
    have lim_top: "\<And>S. open S \<Longrightarrow> l \<in> S \<Longrightarrow> eventually (\<lambda>x. f x \<in> S) at_top"
      using assms tendsto_def by auto
    have "eventually (\<lambda>x. f x \<in> {l - ?eps <..< l + ?eps}) at_top"
      using fb_l by (intro lim_top; force)
    then obtain N where fn_in: "\<And>n. n \<ge> N \<Longrightarrow> f n \<in> {l - ?eps <..< l + ?eps}"
      using eventually_at_top_linorder by metis
    let ?n = "max b N"
    have "f ?n > f b" using fn_in by force
    moreover have "f ?n \<le> f b" using f_antimono b_a
      by (simp add: antimono_onD le_max_iff_disj)
    ultimately have False by simp }
  thus "\<And>x. x \<in> {a..} \<Longrightarrow> f x \<ge> l"
    by blast
qed

corollary antimono_at_top_le:
  fixes b :: "'b::{order_topology, linordered_ab_group_add}" and f :: "'a::linorder \<Rightarrow> 'b"
  assumes "antimono f" and "(f \<longlongrightarrow> b) at_top"
  shows "\<And>x. f x \<ge> b"
  using antimono_on_at_top_ge assms antimono_imp_mono_on by blast

lemma antimono_on_at_bot_ge:
  fixes a :: "'a::linorder" and b :: "'b::{order_topology, linordered_ab_group_add}"
    and f :: "'a \<Rightarrow> 'b"
  assumes f_antimono: "antimono_on {..a} f" and f_to_l: "(f \<longlongrightarrow> l) at_bot"
  shows "\<And>x. x \<in> {..a} \<Longrightarrow> f x \<le> l"
proof -
  { fix b assume b_a: "b \<le> a" and fb_l: "\<not> f b \<le> l"
    let ?eps = "f b - l"
    have lim_bot: "\<And>S. open S \<Longrightarrow> l \<in> S \<Longrightarrow> eventually (\<lambda>x. f x \<in> S) at_bot"
      using assms tendsto_def by auto
    have "eventually (\<lambda>x. f x \<in> {l - ?eps <..< l + ?eps}) at_bot"
      using fb_l by (intro lim_bot; force)
    then obtain N where fn_in: "\<And>n. n \<le> N \<Longrightarrow> f n \<in> {l - ?eps <..< l + ?eps}"
      using eventually_at_bot_linorder by metis
    let ?n = "min b N"
    have "f ?n < f b" using fn_in by force 
   moreover have "f ?n \<ge> f b" using f_antimono b_a by (simp add: min.coboundedI1 antimono_onD)
    ultimately have False by simp }
  thus "\<And>x. x \<in> {..a} \<Longrightarrow> f x \<le> l"
    using assms by blast
qed

corollary antimono_at_bot_ge:
  fixes b :: "'b::{order_topology, linordered_ab_group_add}" and f :: "'a::linorder \<Rightarrow> 'b"
  assumes "antimono f" and "(f \<longlongrightarrow> b) at_bot"
  shows "\<And>x. f x \<le> b"
  using antimono_on_at_bot_ge assms antimono_imp_mono_on by blast

lemma continuous_cdivide:
  fixes c::"'a::real_normed_field"
  assumes "c \<noteq> 0" "continuous F f"
  shows "continuous F (\<lambda>x. f x / c)"
  using assms continuous_mult_right by (rewrite field_class.field_divide_inverse) auto

lemma continuous_mult_left_iff:
  fixes c::"'a::real_normed_field"
  assumes "c \<noteq> 0"
  shows "continuous F f \<longleftrightarrow> continuous F (\<lambda>x. c * f x)"
  using assms continuous_cmult_left_iff by blast

lemma continuous_mult_right_iff:
  fixes c::"'a::real_normed_field"
  assumes "c \<noteq> 0"
  shows "continuous F f \<longleftrightarrow> continuous F (\<lambda>x. f x * c)"
  using continuous_mult_right continuous_cdivide assms by force

lemma continuous_cdivide_iff:
  fixes c::"'a::real_normed_field"
  assumes "c \<noteq> 0"
  shows "continuous F f \<longleftrightarrow> continuous F (\<lambda>x. f x / c)"
proof
  assume "continuous F f"
  thus "continuous F (\<lambda>x. f x / c)"
    by (intro continuous_cdivide) (simp add: assms)
next
  assume "continuous F (\<lambda>x. f x / c)"
  hence "continuous F (\<lambda>x. f x / c * c)" using continuous_mult_right by fastforce
  thus "continuous F f" using assms by force
qed

lemma continuous_within_shift:
  fixes a x :: "'a :: {topological_ab_group_add, t2_space}"
    and s :: "'a set"
    and f :: "'a \<Rightarrow> 'b::topological_space"
  shows "continuous (at x within s) (\<lambda>x. f (x+a)) \<longleftrightarrow> continuous (at (x+a) within plus a ` s) f"
proof
  assume "continuous (at x within s) (\<lambda>x. f (x+a))"
  moreover have "continuous (at (x+a) within plus a ` s) (plus (-a))"
    by (simp add: continuous_at_imp_continuous_at_within)
  moreover have "plus (-a) ` plus a ` s = s" by force
  ultimately show "continuous (at (x+a) within plus a ` s) f"
    using continuous_within_compose unfolding comp_def by force
next
  assume "continuous (at (x+a) within plus a ` s) f"
  moreover have "continuous (at x within s) (plus a)"
    by (simp add: continuous_at_imp_continuous_at_within)
  ultimately show "continuous (at x within s) (\<lambda>x. f (x+a))"
    using continuous_within_compose unfolding comp_def by (force simp add: add.commute)
qed

lemma isCont_shift:
  fixes a x :: "'a :: {topological_ab_group_add, t2_space}"
    and f :: "'a \<Rightarrow> 'b::topological_space"
  shows "isCont (\<lambda>x. f (x+a)) x \<longleftrightarrow> isCont f (x+a)"
  using continuous_within_shift by force

lemma has_real_derivative_at_split:
  "(f has_real_derivative D) (at x) \<longleftrightarrow>
    (f has_real_derivative D) (at_left x) \<and> (f has_real_derivative D) (at_right x)"
proof -
  have "at x = at x within ({..<x} \<union> {x<..})" by (simp add: at_eq_sup_left_right at_within_union)
  thus "(f has_real_derivative D) (at x) \<longleftrightarrow>
    (f has_real_derivative D) (at_left x) \<and> (f has_real_derivative D) (at_right x)"
    using Lim_within_Un has_field_derivative_iff by fastforce
qed

lemma DERIV_cmult_iff:
  assumes "c \<noteq> 0"
  shows "(f has_field_derivative D) (at x within s) \<longleftrightarrow>
    ((\<lambda>x. c * f x) has_field_derivative c * D) (at x within s)"
proof
  assume "(f has_field_derivative D) (at x within s)"
  thus  "((\<lambda>x. c * f x) has_field_derivative c * D) (at x within s)" using DERIV_cmult by force
next
  assume "((\<lambda>x. c * f x) has_field_derivative c * D) (at x within s)"
  hence "((\<lambda>x. c * f x / c) has_field_derivative c * D / c) (at x within s)"
    using DERIV_cdivide assms by blast
  thus "(f has_field_derivative D) (at x within s)" by (simp add: assms field_simps)
qed

lemma DERIV_cmult_right_iff:
  assumes "c \<noteq> 0"
  shows "(f has_field_derivative D) (at x within s) \<longleftrightarrow>
    ((\<lambda>x. f x * c) has_field_derivative D * c) (at x within s)"
  by (rewrite DERIV_cmult_iff[of c], simp_all add: assms mult_ac)

lemma DERIV_cdivide_iff:
  assumes "c \<noteq> 0"
  shows "(f has_field_derivative D) (at x within s) \<longleftrightarrow>
    ((\<lambda>x. f x / c) has_field_derivative D / c) (at x within s)"
  by (simp add: DERIV_cmult_right_iff assms field_class.field_divide_inverse)

lemma DERIV_ln_divide_chain:
  fixes f :: "real \<Rightarrow> real"
  assumes "f x > 0" and "(f has_real_derivative D) (at x within s)"
  shows "((\<lambda>x. ln (f x)) has_real_derivative (D / f x)) (at x within s)"
proof -
  have "DERIV ln (f x) :> 1 / f x" using assms by (intro DERIV_ln_divide) blast
  thus ?thesis using DERIV_chain2 assms by fastforce
qed

lemma inverse_fun_has_integral_ln:
  fixes f :: "real \<Rightarrow> real" and f' :: "real \<Rightarrow> real"
  assumes "a \<le> b" and
    "\<And>x. x\<in>{a..b} \<Longrightarrow> f x > 0" and
    "continuous_on {a..b} f" and 
    "\<And>x. x\<in>{a<..<b} \<Longrightarrow> (f has_real_derivative f' x) (at x)"
  shows "((\<lambda>x. f' x / f x) has_integral (ln (f b) - ln (f a))) {a..b}"
proof -
  have "continuous_on {a..b} (\<lambda>x. ln (f x))" using assms by (intro continuous_intros; force)
  moreover have "\<And>x. x\<in>{a<..<b} \<Longrightarrow> ((\<lambda>x. ln (f x)) has_vector_derivative f' x / f x) (at x)"
    apply (rewrite has_real_derivative_iff_has_vector_derivative[THEN sym])
    using assms by (intro DERIV_ln_divide_chain; simp)
  ultimately show ?thesis using assms by (intro fundamental_theorem_of_calculus_interior; simp)
qed

lemma powr_at_top:
  fixes a::real
  assumes "a > 1"
  shows "filterlim (\<lambda>x. a.^x) at_top at_top"
proof -
  have [simp]: "ln a > 0" using assms by simp
  have "a \<noteq> 0" using assms by simp
  moreover have "filterlim (\<lambda>x. exp (ln a * x)) at_top at_top"
    using assms
    by(auto intro!: filterlim_compose[OF exp_at_top] filterlim_cmult_at_bot_at_top[OF ln_at_top]
        ln_at_top filterlim_cmult_at_bot_at_top[OF filterlim_ident])
  ultimately show ?thesis unfolding powr_def by(simp add: mult.commute)
qed

lemma powr_0_at_top:
  fixes a::real
  assumes "0 < a" "a < 1"
  shows "((\<lambda>x. a.^x) \<longlongrightarrow> 0) at_top"
proof -
  have "\<And>x. inverse ((1/a).^x) = a.^x"
    using assms by (rewrite inverse_powr; simp add: powr_minus)
  moreover have "((\<lambda>x. inverse ((1/a).^x)) \<longlongrightarrow> 0) at_top"
    by (intro tendsto_inverse_0_at_top powr_at_top) (simp add: assms)
  ultimately show ?thesis by simp
qed

lemma DERIV_fun_powr2:
  fixes a::real
  assumes a_pos: "a > 0"
    and f: "DERIV f x :> r"
  shows "DERIV (\<lambda>x. a.^(f x)) x :> a.^(f x) * r * ln a"
proof -
  let ?g = "(\<lambda>x. a)"
  have g: "DERIV ?g x :> 0" by simp
  have pos: "?g x > 0" by (simp add: a_pos)
  show ?thesis
    using DERIV_powr[OF g pos f] a_pos by (auto simp add: field_simps)
qed

lemma has_real_derivative_powr2:
  assumes a_pos: "a > 0"
  shows "((\<lambda>x. a.^x) has_real_derivative a.^x * ln a) (at x)"
proof -
  let ?f = "(\<lambda>x. x::real)"
  have f: "DERIV ?f x :> 1" by simp
  thus ?thesis using DERIV_fun_powr2[OF a_pos f] by simp
qed

(* corollary to DERIV_shift *)
lemma field_differentiable_shift:
  "(f field_differentiable (at (x + z))) = ((\<lambda>x. f (x + z)) field_differentiable (at x))"
  unfolding field_differentiable_def using DERIV_shift by force

subsection \<open>Lemmas on \<open>indicator\<close> for a Linearly Ordered Type\<close>

lemma indicator_Icc_shift:
  fixes a b t x :: "'a::linordered_ab_group_add"
  shows "indicator {a..b} x = indicator {t+a..t+b} (t+x)"
  by (simp add: indicator_def)

lemma indicator_Icc_shift_inverse:
  fixes a b t x :: "'a::linordered_ab_group_add"
  shows "indicator {a-t..b-t} x = indicator {a..b} (t+x)"
  by (metis add.commute diff_add_cancel indicator_Icc_shift)

lemma indicator_Ici_shift:
  fixes a t x :: "'a::linordered_ab_group_add"
  shows "indicator {a..} x = indicator {t+a..} (t+x)"
  by (simp add: indicator_def)

lemma indicator_Ici_shift_inverse:
  fixes a t x :: "'a::linordered_ab_group_add"
  shows "indicator {a-t..} x = indicator {a..} (t+x)"
  by (metis add.commute diff_add_cancel indicator_Ici_shift)

lemma indicator_Iic_shift:
  fixes b t x :: "'a::linordered_ab_group_add"
  shows "indicator {..b} x = indicator {..t+b} (t+x)"
  by (simp add: indicator_def)

lemma indicator_Iic_shift_inverse:
  fixes b t x :: "'a::linordered_ab_group_add"
  shows "indicator {..b-t} x = indicator {..b} (t+x)"
  by (metis add.commute diff_add_cancel indicator_Iic_shift)

lemma indicator_Icc_reverse:
  fixes a b t x :: "'a::linordered_ab_group_add"
  shows "indicator {a..b} x = indicator {t-b..t-a} (t-x)"
  by (metis add_le_cancel_left atLeastAtMost_iff diff_add_cancel indicator_simps le_diff_eq)

lemma indicator_Icc_reverse_inverse:
  fixes a b t x :: "'a::linordered_ab_group_add"
  shows "indicator {t-b..t-a} x = indicator {a..b} (t-x)"
  by (metis add_diff_cancel_left' diff_add_cancel indicator_Icc_reverse)

lemma indicator_Ici_reverse:
  fixes a t x :: "'a::linordered_ab_group_add"
  shows "indicator {a..} x = indicator {..t-a} (t-x)"
  by (simp add: indicator_def)

lemma indicator_Ici_reverse_inverse:
  fixes b t x :: "'a::linordered_ab_group_add"
  shows "indicator {t-b..} x = indicator {..b} (t-x)" 
  by (metis add_diff_cancel_left' diff_add_cancel indicator_Ici_reverse)

lemma indicator_Iic_reverse:
  fixes b t x :: "'a::linordered_ab_group_add"
  shows "indicator {..b} x = indicator {t-b..} (t-x)"
  by (simp add: indicator_def)

lemma indicator_Iic_reverse_inverse:
  fixes a t x :: "'a::linordered_field"
  shows "indicator {..t-a} x = indicator {a..} (t-x)"
  by (simp add: indicator_def)

lemma indicator_Icc_affine_pos:
  fixes a b c t x :: "'a::linordered_field"
  assumes "c > 0"
  shows "indicator {a..b} x = indicator {t+c*a..t+c*b} (t + c*x)"
  unfolding indicator_def using assms by simp

lemma indicator_Icc_affine_pos_inverse:
  fixes a b c t x :: "'a::linordered_field"
  assumes "c > 0"
  shows "indicator {(a-t)/c..(b-t)/c} x = indicator {a..b} (t + c*x)"
  using indicator_Icc_affine_pos[where a="(a-t)/c" and b="(b-t)/c" and c=c and t=t ] assms by simp

lemma indicator_Ici_affine_pos:
  fixes a c t x :: "'a::linordered_field"
  assumes "c > 0"
  shows "indicator {a..} x = indicator {t+c*a..} (t + c*x)"
  unfolding indicator_def using assms by simp

lemma indicator_Ici_affine_pos_inverse:
  fixes a c t x :: "'a::linordered_field"
  assumes "c > 0"
  shows "indicator {(a-t)/c..} x = indicator {a..} (t + c*x)"
  using indicator_Ici_affine_pos[where a="(a-t)/c" and c=c and t=t] assms by simp

lemma indicator_Iic_affine_pos:
  fixes b c t x :: "'a::linordered_field"
  assumes "c > 0"
  shows "indicator {..b} x = indicator {..t+c*b} (t + c*x)"
  unfolding indicator_def using assms by simp

lemma indicator_Iic_affine_pos_inverse:
  fixes b c t x :: "'a::linordered_field"
  assumes "c > 0"
  shows "indicator {..(b-t)/c} x = indicator {..b} (t + c*x)"
  using indicator_Iic_affine_pos[where b="(b-t)/c" and c=c and t=t] assms by simp

lemma indicator_Icc_affine_neg:
  fixes a b c t x :: "'a::linordered_field"
  assumes "c < 0"
  shows "indicator {a..b} x = indicator {t+c*b..t+c*a} (t + c*x)"
  unfolding indicator_def using assms by auto

lemma indicator_Icc_affine_neg_inverse:
  fixes a b c t x :: "'a::linordered_field"
  assumes "c < 0"
  shows "indicator {(b-t)/c..(a-t)/c} x = indicator {a..b} (t + c*x)"
  using indicator_Icc_affine_neg[where a="(b-t)/c" and b="(a-t)/c" and c=c and t=t] assms by simp

lemma indicator_Ici_affine_neg:
  fixes a c t x :: "'a::linordered_field"
  assumes "c < 0"
  shows "indicator {a..} x = indicator {..t+c*a} (t + c*x)"
  unfolding indicator_def using assms by simp

lemma indicator_Ici_affine_neg_inverse:
  fixes b c t x :: "'a::linordered_field"
  assumes "c < 0"
  shows "indicator {(b-t)/c..} x = indicator {..b} (t + c*x)"
  using indicator_Ici_affine_neg[where a="(b-t)/c" and c=c and t=t] assms by simp

lemma indicator_Iic_affine_neg:
  fixes b c t x :: "'a::linordered_field"
  assumes "c < 0"
  shows "indicator {..b} x = indicator {t+c*b..} (t + c*x)"
  unfolding indicator_def using assms by simp

lemma indicator_Iic_affine_neg_inverse:
  fixes a c t x :: "'a::linordered_field"
  assumes "c < 0"
  shows "indicator {..(a-t)/c} x = indicator {a..} (t + c*x)"
  using indicator_Iic_affine_neg[where b="(a-t)/c" and c=c and t=t] assms by simp

section \<open>Additional Lemmas for the \<open>HOL-Analysis\<close> Library\<close>

(* To be included in Lebesgue_Stieltjes_Integral *)
lemma differentiable_eq_field_differentiable_real:
  fixes f :: "real \<Rightarrow> real"
  shows "f differentiable F \<longleftrightarrow> f field_differentiable F"
  unfolding field_differentiable_def differentiable_def has_real_derivative
  using has_real_derivative_iff by presburger

(* To be included in Lebesgue_Stieltjes_Integral *)
lemma differentiable_on_eq_field_differentiable_real:
  fixes f :: "real \<Rightarrow> real"
  shows "f differentiable_on s \<longleftrightarrow> (\<forall>x\<in>s. f field_differentiable (at x within s))"
  unfolding differentiable_on_def using differentiable_eq_field_differentiable_real by simp

lemma differentiable_on_cong :
  assumes "\<And>x. x\<in>s \<Longrightarrow> f x = g x" and "f differentiable_on s"
  shows "g differentiable_on s"
proof -
  { fix x assume "x\<in>s"
    hence "f differentiable at x within s" using assms unfolding differentiable_on_def by simp
    from this obtain D where "(f has_derivative D) (at x within s)"
      unfolding differentiable_def by blast
    hence "(g has_derivative D) (at x within s)"
      using has_derivative_transform assms \<open>x\<in>s\<close> by metis
    hence "g differentiable at x within s" unfolding differentiable_def by blast }
  hence "\<forall>x\<in>s. g differentiable at x within s" by simp
  thus ?thesis unfolding differentiable_on_def by simp
qed

lemma C1_differentiable_imp_deriv_continuous_on:
  "f C1_differentiable_on S \<Longrightarrow> continuous_on S (deriv f)"
  using C1_differentiable_on_eq field_derivative_eq_vector_derivative by auto

lemma deriv_shift:
  assumes "f field_differentiable at (x+a)"
  shows "deriv f (x+a) = deriv (\<lambda>s. f (x+s)) a"
proof -
  have "(f has_field_derivative deriv f (x+a)) (at (x+a))"
    using DERIV_deriv_iff_field_differentiable assms
    by force
  hence "((\<lambda>s. f (x+s)) has_field_derivative deriv f (x+a)) (at a)"
    using DERIV_at_within_shift has_field_derivative_at_within by blast
  moreover have "((\<lambda>s. f (x+s)) has_field_derivative deriv (\<lambda>s. f (x+s)) a) (at a)"
    using DERIV_imp_deriv calculation by fastforce
  ultimately show ?thesis using DERIV_unique by force
qed

lemma piecewise_differentiable_on_cong:
  assumes "f piecewise_differentiable_on i"
    and "\<And>x. x \<in> i \<Longrightarrow> f x = g x"
  shows "g piecewise_differentiable_on i"
proof -
  have "continuous_on i g"
    using continuous_on_cong_simp assms piecewise_differentiable_on_imp_continuous_on by force
  moreover have "\<exists>S. finite S \<and> (\<forall>x \<in> i - S. g differentiable (at x within i))"
  proof -
    from assms piecewise_differentiable_on_def
    obtain S where fin: "finite S" and "\<forall>x \<in> i - S. f differentiable (at x within i)" by metis
    hence "\<And>x. x \<in> i - S \<Longrightarrow> f differentiable (at x within i)" by simp
    hence "\<And>x. x \<in> i - S \<Longrightarrow> g differentiable (at x within i)"
      using has_derivative_transform assms by (metis DiffD1 differentiable_def)
    with fin show ?thesis by blast
  qed
  ultimately show ?thesis unfolding piecewise_differentiable_on_def by simp
qed

lemma differentiable_piecewise:
  assumes "continuous_on i f"
    and "f differentiable_on i"
  shows "f piecewise_differentiable_on i"
  unfolding piecewise_differentiable_on_def using assms differentiable_onD by auto

lemma piecewise_differentiable_scaleR:
  assumes "f piecewise_differentiable_on S"
  shows "(\<lambda>x. a *\<^sub>R f x) piecewise_differentiable_on S"
proof -
  from assms obtain T where fin: "finite T" "\<And>x. x \<in> S - T \<Longrightarrow> f differentiable at x within S"
    unfolding piecewise_differentiable_on_def by blast
  hence "\<And>x. x \<in> S - T \<Longrightarrow> (\<lambda>x. a *\<^sub>R f x) differentiable at x within S"
    using differentiable_scaleR by simp
  moreover have "continuous_on S (\<lambda>x. a *\<^sub>R f x)"
    using assms continuous_on_scaleR continuous_on_const piecewise_differentiable_on_def by blast
  ultimately show "(\<lambda>x. a *\<^sub>R f x) piecewise_differentiable_on S"
    using fin piecewise_differentiable_on_def by blast
qed

lemma differentiable_on_piecewise_compose:
  assumes "f piecewise_differentiable_on S"
    and "g differentiable_on f ` S"
  shows "g \<circ> f piecewise_differentiable_on S"
proof -
  from assms obtain T where fin: "finite T" "\<And>x. x \<in> S - T \<Longrightarrow> f differentiable at x within S"
    unfolding piecewise_differentiable_on_def by blast
  hence "\<And>x. x \<in> S - T \<Longrightarrow> g \<circ> f differentiable at x within S"
    by (meson DiffD1 assms differentiable_chain_within differentiable_onD image_eqI)
  hence "\<exists>T. finite T \<and> (\<forall>x\<in>S-T. g \<circ> f differentiable at x within S)" using fin by blast
  moreover have "continuous_on S (g \<circ> f)"
    using assms continuous_on_compose differentiable_imp_continuous_on
    unfolding piecewise_differentiable_on_def by blast
  ultimately show ?thesis
    unfolding piecewise_differentiable_on_def by force
qed

lemma MVT_order_free:
  fixes r h :: real
  defines "I \<equiv> {r..r+h} \<union> {r+h..r}"
  assumes "continuous_on I f" and "f differentiable_on interior I"
  obtains t where "t \<in> {0<..<1}" and "f (r+h) - f r = h * deriv f (r + t*h)"
proof -
  consider (h_pos) "h > 0" | (h_0) "h = 0" | (h_neg) "h < 0" by force
  thus ?thesis
  proof cases
    case h_pos
    hence "r < r+h" "I = {r..r+h}" unfolding I_def by simp_all
    moreover hence "interior I = {r<..<r+h}" by simp
    moreover hence "\<And>x. \<lbrakk>r < x; x < r+h\<rbrakk> \<Longrightarrow> f differentiable (at x)"
      using assms by (simp add: differentiable_on_eq_differentiable_at)
    ultimately obtain z where "r < z \<and> z < r+h \<and> f (r+h) - f r = h * deriv f z"
      using MVT assms by (smt (verit) DERIV_imp_deriv)
    moreover hence "(z-r) / h \<in> {0<..<1}" by simp
    moreover have "z = r + (z-r)/h * h" using h_pos by simp
    ultimately show ?thesis using that by presburger
  next
    case h_0
    have "1/2 \<in> {0::real<..<1}" by simp
    moreover have "f (r+h) - f r = 0" using h_0 by simp
    moreover have "h * deriv f (r + (1/2)*h) = 0" using h_0 by simp
    ultimately show ?thesis using that by presburger
  next case h_neg
    hence "r+h < r" "I = {r+h..r}" unfolding I_def by simp_all
    moreover hence "interior I = {r+h<..<r}" by simp
    moreover hence "\<And>x. \<lbrakk>r+h < x; x < r\<rbrakk> \<Longrightarrow> f differentiable (at x)"
      using assms by (simp add: differentiable_on_eq_differentiable_at)
    ultimately obtain z where "r+h < z \<and> z < r \<and> f r - f (r+h) = -h * deriv f z"
      using MVT assms by (smt (verit) DERIV_imp_deriv)
    moreover hence "(z-r) / h \<in> {0<..<1}" by (simp add: neg_less_divide_eq)
    moreover have "z = r + (z-r)/h * h" using h_neg by simp
    ultimately show ?thesis using that mult_minus_left by fastforce
  qed
qed

lemma integral_combine2:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "a \<le> c" "c \<le> b"
    and "f integrable_on {a..c}" "f integrable_on {c..b}"
  shows "integral {a..c} f + integral {c..b} f = integral {a..b} f"
  by (meson Henstock_Kurzweil_Integration.integrable_combine
      Henstock_Kurzweil_Integration.integral_combine assms)

lemma has_integral_null_interval: fixes a b :: real and f::"real \<Rightarrow> real" assumes "a \<ge> b"
  shows "(f has_integral 0) {a..b}"
  using assms content_real_eq_0 by blast

lemma has_integral_interval_reverse: fixes f :: "real \<Rightarrow> real" and a b :: real
  assumes "a \<le> b"
    and "continuous_on {a..b} f"
  shows "((\<lambda>x. f (a+b-x)) has_integral (integral {a..b} f)) {a..b}"
proof -
  let ?g = "\<lambda>x. a + b - x"
  let ?g' = "\<lambda>x. -1"
  have "continuous_on {a..b} ?g" using continuous_on_op_minus by simp
  moreover have "\<And>x. x\<in>{a..b} \<Longrightarrow> (?g has_field_derivative ?g' x) (at x within {a..b})"
    by (auto intro!: derivative_eq_intros)
  ultimately have "((\<lambda>x. -1 * f (a+b-x)) has_integral integral {b..a} f - integral {a..b} f) {a..b}"
    using has_integral_substitution_general[of "{}" a b ?g a b f] assms by force
  thus ?thesis
    by (simp add: has_integral_null_interval[OF \<open>a \<le> b\<close>, THEN integral_unique] has_integral_neg_iff)
qed

lemma FTC_real_deriv_has_integral:
  fixes F :: "real \<Rightarrow> real"
  assumes "a \<le> b"
    and "F piecewise_differentiable_on {a<..<b}"
    and "continuous_on {a..b} F"
  shows "(deriv F has_integral F b - F a) {a..b}"
proof -
  obtain S where fin: "finite S" and
    diff: "\<And>x. x \<in> {a<..<b} - S \<Longrightarrow> F differentiable at x within {a<..<b} - S"
    using assms unfolding piecewise_differentiable_on_def
    by (meson Diff_subset differentiable_within_subset)
  hence "\<And>x. x \<in> {a<..<b} - S \<Longrightarrow> (F has_real_derivative deriv F x) (at x)"
  proof -
    fix x assume x_in: "x \<in> {a<..<b} - S"
    have "open ({a<..<b} - S)"
      using fin finite_imp_closed by (metis open_Diff open_greaterThanLessThan)
    hence "at x within {a<..<b} - S = at x" by (meson x_in at_within_open)
    hence "F differentiable at x" using diff x_in by (smt (verit))
    thus "(F has_real_derivative deriv F x) (at x)"
      using DERIV_deriv_iff_real_differentiable by simp
  qed
  thus ?thesis
    by (intro fundamental_theorem_of_calculus_interior_strong[where S=S];
        simp add: assms fin has_real_derivative_iff_has_vector_derivative)
qed

lemma integrable_spike_cong:
  assumes "negligible S" "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
  shows "f integrable_on T \<longleftrightarrow> g integrable_on T"
  using integrable_spike assms by force

lemma has_integral_powr2_from_0:
  fixes a c :: real
  assumes a_pos: "a > 0" and a_neq_1: "a \<noteq> 1" and c_nneg: "c \<ge> 0"
  shows "((\<lambda>x. a.^x) has_integral ((a.^c - 1) / (ln a))) {0..c}"
proof -
  have "((\<lambda>x. a.^x) has_integral ((a.^c)/(ln a) - (a.^0)/(ln a))) {0..c}"
  proof (rule fundamental_theorem_of_calculus[OF c_nneg])
    fix x::real
    assume "x \<in> {0..c}"
    show "((\<lambda>y. a.^y / ln a) has_vector_derivative a.^x) (at x within {0..c})"
      using has_real_derivative_powr2[OF a_pos, of x]
            DERIV_cdivide[where c = "ln a"]
      by(fastforce simp: assms has_real_derivative_iff_has_vector_derivative
               intro!: has_vector_derivative_within_subset[where S=UNIV and T="{0..c}"])
  qed
  thus ?thesis
    using assms powr_zero_eq_one by (simp add: field_simps)
qed

lemma integrable_on_powr2_from_0:
  fixes a c :: real
  assumes a_pos: "a > 0" and a_neq_1: "a \<noteq> 1" and c_nneg: "c \<ge> 0"
  shows "(\<lambda>x. a.^x) integrable_on {0..c}"
  using has_integral_powr2_from_0[OF assms] unfolding integrable_on_def by blast

lemma integrable_on_powr2_from_0_general:
  fixes a c :: real
  assumes a_pos: "a > 0" and c_nneg: "c \<ge> 0"
  shows "(\<lambda>x. a.^x) integrable_on {0..c}"
proof (cases "a = 1")
  case True
  thus ?thesis
    using has_integral_const_real by auto
next
  case False
  thus ?thesis
    using has_integral_powr2_from_0 False assms by auto
qed

(* Stronger Version of lemma integral_power *)
lemma has_bochner_integral_power:
  fixes a b :: real and k :: nat
  assumes "a \<le> b"
  shows "has_bochner_integral lborel (\<lambda>x. x^k * indicator {a..b} x) ((b^(k+1) - a^(k+1)) / (k+1))"
proof -
  have "\<And>x. ((\<lambda>x. x^(k+1) / (k+1)) has_real_derivative x^k) (at x)"
    using DERIV_pow by (intro derivative_eq_intros) auto
  hence "has_bochner_integral lborel (\<lambda>x. x^k * indicator {a..b} x) (b^(k+1)/(k+1) - a^(k+1)/(k+1))"
    by (intro has_bochner_integral_FTC_Icc_real; simp add: assms)
  thus ?thesis by (simp add: diff_divide_distrib)
qed

corollary integrable_power: "(a::real) \<le> b \<Longrightarrow> integrable lborel (\<lambda>x. x^k * indicator {a..b} x)"
  using has_bochner_integral_power integrable.intros by blast

lemma nn_integral_powr_Icc:
  fixes a b c :: real
  assumes "a \<le> b" "0 < c" "c \<noteq> 1"
  shows "(\<integral>\<^sup>+x\<in>{a..b}. c.^x \<partial>lborel) = (c.^b - c.^a) / ln c"
proof -
  let ?F = "\<lambda>x. c.^x / ln c"
  have "\<And>x. DERIV ?F x :> c.^x"
  proof -
    fix x
    have "DERIV ?F x :> ?F x * ln c"
      using DERIV_fun_powr2 assms by (intro derivative_eq_intros; simp) simp
    thus "DERIV ?F x :> c.^x" using assms by simp
  qed
  thus ?thesis by (rewrite nn_integral_FTC_Icc[where F="?F"]; simp add: assms) argo
qed

lemma nn_integral_powr_Icc_gen:
  fixes a b c :: real
  assumes "0 < c" "c \<noteq> 1"
  shows "(\<integral>\<^sup>+x\<in>{a..b}. c.^x \<partial>lborel) = (if a \<le> b then (c.^b - c.^a) / ln c else 0)"
proof (cases \<open>a \<le> b\<close>)
  case True
  thus ?thesis using nn_integral_powr_Icc assms by simp
next
  case False
  thus ?thesis by simp
qed

lemma nn_integral_powr_Icc_finite:
  fixes a b c :: real
  assumes "0 < c"
  shows "(\<integral>\<^sup>+x\<in>{a..b}. c.^x \<partial>lborel) < \<top>"
proof (cases \<open>c = 1\<close>)
  case True
  hence "(\<integral>\<^sup>+x\<in>{a..b}. c.^x \<partial>lborel) = (\<integral>\<^sup>+x\<in>{a..b}. 1 \<partial>lborel)" by simp
  also have "\<dots> = emeasure lborel {a..b}" using nn_integral_indicator by simp
  also have "\<dots> < \<top>" by (simp add: emeasure_lborel_Icc_eq)
  finally show ?thesis .
next
  case False
  thus ?thesis by (rewrite nn_integral_powr_Icc_gen; simp add: assms)
qed

lemma nn_integral_powr_Ici:
  fixes a c :: real
  assumes "0 < c" "c < 1"
  shows "(\<integral>\<^sup>+x\<in>{a..}. c.^x \<partial>lborel) = - (c.^a / ln c)"
proof -
  let ?F = "\<lambda>x. c.^x / ln c"
  have "\<And>x. DERIV ?F x :> c.^x"
  proof -
    fix x
    have "DERIV ?F x :> ?F x * ln c"
      using DERIV_fun_powr2 assms by (intro derivative_eq_intros; simp) simp
    thus "DERIV ?F x :> c.^x" using assms by simp
  qed
  moreover have "(?F \<longlongrightarrow> 0 / ln c) at_top"
    using assms by (intro tendsto_intros; simp add: powr_0_at_top)
  ultimately show ?thesis by (rewrite nn_integral_FTC_atLeast[where F="?F"]; simp) simp
qed

lemma set_integrable_iff_bounded:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "A \<in> sets M"
  shows "set_integrable M A f \<longleftrightarrow> set_borel_measurable M A f \<and> (\<integral>\<^sup>+x\<in>A. norm (f x) \<partial>M) < \<infinity>"
  unfolding set_integrable_def set_borel_measurable_def using integrable_iff_bounded
  by (smt (verit, ccfv_threshold) indicator_mult_ennreal indicator_pos_le
      mult.commute nn_integral_cong norm_scaleR)

lemma set_integrable_powr_Icc:
  fixes a b c :: real
  assumes "0 < c"
  shows "set_integrable lborel {a..b} (\<lambda>x. c.^x)"
proof -
  have "set_borel_measurable lborel {a..b} (\<lambda>x. c.^x)" unfolding set_borel_measurable_def by simp
  moreover have "(\<integral>\<^sup>+x\<in>{a..b}. c.^x \<partial>lborel) < \<top>" using assms nn_integral_powr_Icc_finite by simp
  ultimately show ?thesis by (rewrite set_integrable_iff_bounded; simp)
qed

lemma set_integrable_powr_Ici:
  fixes a c :: real
  assumes "0 < c" "c < 1"
  shows "set_integrable lborel {a..} (\<lambda>x. c.^x)"
proof -
  have "set_borel_measurable lborel {a..} (\<lambda>x. c.^x)" unfolding set_borel_measurable_def by simp
  moreover have "(\<integral>\<^sup>+x\<in>{a..}. c.^x \<partial>lborel) < \<top>" using assms nn_integral_powr_Ici by simp
  ultimately show ?thesis by (rewrite set_integrable_iff_bounded; simp)
qed

(* Analogue for lemma has_integral_integral_real *)
lemma has_integral_set_integral_real:
  fixes f::"'a::euclidean_space \<Rightarrow> real" and A :: "'a set"
  assumes f: "set_integrable lborel A f"
  shows "(f has_integral (set_lebesgue_integral lborel A f)) A"
  using assms has_integral_integral_real[where f="\<lambda>x. indicat_real A x * f x"]
  by (simp add: has_integral_iff set_borel_integral_eq_integral)

(* To be included in Lebesgue_Stieltjes_Integral *)
lemma set_borel_measurable_UNIV[simp]:
  fixes f :: "'a :: real_vector \<Rightarrow> real"
  shows "set_borel_measurable M UNIV f \<longleftrightarrow> f \<in> borel_measurable M"
  unfolding set_borel_measurable_def by simp

lemma set_borel_measurable_lborel:
  "set_borel_measurable lborel A f \<longleftrightarrow> set_borel_measurable borel A f"
  unfolding set_borel_measurable_def by simp

lemma restrict_space_whole[simp]: "restrict_space M (space M) = M"
  unfolding restrict_space_def by (simp add: measure_of_of_measure)

(* To be included in Lebesgue_Stieltjes_Integral *)
lemma deriv_measurable_real:
  fixes f :: "real \<Rightarrow> real"
  assumes "f differentiable_on S" "open S" "f \<in> borel_measurable borel"
  shows "set_borel_measurable borel S (deriv f)"
proof -
  have "\<And>x. x \<in> S \<Longrightarrow> deriv f x = lim (\<lambda>i. (f (x + 1 / Suc i) - f x) / (1 / Suc i))"
  proof -
    fix x assume x_S: "x \<in> S"
    hence "f field_differentiable (at x within S)"
      using differentiable_on_eq_field_differentiable_real assms by simp
    hence "(f has_field_derivative deriv f x) (at x)"
      using assms DERIV_deriv_iff_field_differentiable x_S at_within_open by force
    hence "(\<lambda>h. (f (x+h) - f x) / h) \<midarrow>0\<rightarrow> deriv f x" using DERIV_def by auto
    hence "\<forall>d. (\<forall>i. d i \<in> UNIV-{0::real}) \<longrightarrow> d \<longlonglongrightarrow> 0 \<longrightarrow>
      ((\<lambda>h. (f (x+h) - f x) / h) \<circ> d) \<longlonglongrightarrow> deriv f x"
      using tendsto_at_iff_sequentially by blast
    moreover have "\<forall>i. 1 / Suc i \<in> UNIV - {0::real}" by simp
    moreover have "(\<lambda>i. 1 / Suc i) \<longlonglongrightarrow> 0" using LIMSEQ_Suc lim_const_over_n by blast
    ultimately have "((\<lambda>h. (f (x+h) - f x) / h) \<circ> (\<lambda>i. 1 / Suc i)) \<longlonglongrightarrow> deriv f x" by auto
    thus "deriv f x = lim (\<lambda>i. (f (x + 1 / Suc i) - f x) / (1 / Suc i))"
      unfolding comp_def by (simp add: limI)
  qed
  moreover have "(\<lambda>x. indicator S x * lim (\<lambda>i. (f (x + 1 / Suc i) - f x) / (1 / Suc i)))
    \<in> borel_measurable borel"
    using assms by (measurable, simp, measurable)
  ultimately show ?thesis
    unfolding set_borel_measurable_def measurable_cong
    by simp (smt (verit) indicator_simps(2) measurable_cong mult_eq_0_iff)
qed

(* To be included in Lebesgue_Stieltjes_Integral *)
corollary deriv_measurabe_real_UNIV:
  fixes f :: "real \<Rightarrow> real"
  assumes "f differentiable_on UNIV" "f \<in> borel_measurable borel"
  shows "deriv f \<in> borel_measurable borel"
  using deriv_measurable_real[where S=UNIV] assms by simp

(* To be included in Lebesgue_Stieltjes_Integral *)
lemma piecewise_differentiable_on_deriv_measurable_real:
  fixes f :: "real \<Rightarrow> real"
  assumes "f piecewise_differentiable_on S" "open S" "f \<in> borel_measurable borel"
  shows "set_borel_measurable borel S (deriv f)"
proof -
  from assms obtain T where fin: "finite T" and
    diff: "\<And>x. x \<in> S - T \<Longrightarrow> f differentiable at x within S"
    unfolding piecewise_differentiable_on_def by blast
  with assms have "open (S - T)" using finite_imp_closed by blast
  moreover hence "f differentiable_on (S - T)"
    unfolding differentiable_on_def using assms by (metis Diff_iff at_within_open diff)
  ultimately have "set_borel_measurable borel (S - T) (deriv f)"
    by (intro deriv_measurable_real; simp add: assms)
  moreover have "x \<notin> T \<Longrightarrow> indicat_real (S - T) x = indicat_real S x" for x
    by(simp add: indicator_diff)
  ultimately show ?thesis
    using fin 
    by(auto intro!: measurable_discrete_difference[where f="\<lambda>x. indicat_real (S - T) x * deriv f x"]
        countable_finite simp: set_borel_measurable_def)
qed

(* To be included in Lebesgue_Stieltjes_Integral *)
corollary piecewise_differentiable_on_deriv_measurable_real_UNIV:
  fixes f :: "real \<Rightarrow> real"
  assumes "f piecewise_differentiable_on UNIV" "f \<in> borel_measurable borel"
  shows "(deriv f) \<in> borel_measurable borel"
  using piecewise_differentiable_on_deriv_measurable_real[where S=UNIV] assms by simp

lemma borel_measurable_antimono:
  fixes f :: "real \<Rightarrow> real"
  shows "antimono f \<Longrightarrow> f \<in> borel_measurable borel"
  using borel_measurable_mono[of "\<lambda>x. - f x"] by (simp add: antimonoD monoI)

lemma set_borel_measurable_restrict_space_iff: 
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes \<Omega>[measurable, simp]: "\<Omega> \<inter> space M \<in> sets M"
  shows "f \<in> borel_measurable (restrict_space M \<Omega>) \<longleftrightarrow> set_borel_measurable M \<Omega> f"
  using assms borel_measurable_restrict_space_iff set_borel_measurable_def by blast

lemma set_integrable_restrict_space_iff:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "A \<in> sets M"
  shows "set_integrable M A f \<longleftrightarrow> integrable (restrict_space M A) f"
  unfolding set_integrable_def using assms
  by (rewrite integrable_restrict_space; simp)

lemma set_lebesgue_integral_restrict_space:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "A \<in> sets M"
  shows "set_lebesgue_integral M A f = integral\<^sup>L (restrict_space M A) f"
  unfolding set_lebesgue_integral_def using assms integral_restrict_space
  by (metis (mono_tags) sets.Int_space_eq2)

lemma distr_borel_lborel: "distr M borel f = distr M lborel f"
  by (metis distr_cong sets_lborel)

lemma AE_translation:
  assumes "AE x in lborel. P x" shows "AE x in lborel. P (a+x)"
proof -
  from assms obtain N where P: "\<And>x. x \<in> space lborel - N \<Longrightarrow> P x" and null: "N \<in> null_sets lborel"
    using AE_E3 by blast
  hence "{y. a+y \<in> N} \<in> null_sets lborel"
    using null_sets_translation[of N "-a", simplified] by (simp add: add.commute)
  moreover have "\<And>y. y \<in> space lborel - {y. a+y \<in> N} \<Longrightarrow> P (a+y)" using P by force
  ultimately show "AE y in lborel. P (a+y)"
    by (metis (no_types, lifting) Collect_mono P UNIV_I eventually_ae_filter
        Diff_iff space_borel space_lborel)
qed

lemma set_AE_translation:
  assumes "AE x\<in>S in lborel. P x" shows "AE x \<in> plus (-a) ` S in lborel. P (a+x)"
proof -
  have "AE x in lborel. a+x \<in> S \<longrightarrow> P (a+x)" using assms by (rule AE_translation)
  moreover have "\<And>x. a+x \<in> S \<longleftrightarrow> x \<in> plus (-a) ` S" by force
  ultimately show ?thesis by simp
qed

lemma AE_scale_measure_iff:
  assumes "r > 0"
  shows "(AE x in (scale_measure r M). P x) \<longleftrightarrow> (AE x in M. P x)"
  unfolding ae_filter_def null_sets_def
  using assms by(auto intro!: arg_cong[where f="\<lambda>A. eventually P (Inf A)"] simp: space_scale_measure)

lemma nn_set_integral_cong2:
  assumes "AE x\<in>A in M. f x = g x"
  shows "(\<integral>\<^sup>+x\<in>A. f x \<partial>M) = (\<integral>\<^sup>+x\<in>A. g x \<partial>M)"
  using assms by(auto intro!: nn_integral_cong_AE)

(* add after Set_Integral.nn_integral_null_delta *)
lemma nn_integral_minus_null:
  assumes "A \<in> sets M" "B \<in> sets M" "B \<in> null_sets M"
  shows "(\<integral>\<^sup>+x \<in> A. f x \<partial>M) = (\<integral>\<^sup>+x \<in> A - B. f x \<partial>M)"
proof -
  have "sym_diff A (A - B) = A \<inter> B" by force
  moreover have "A \<inter> B \<in> null_sets M" using assms null_set_Int1 by blast
  ultimately show ?thesis using assms by (rewrite nn_integral_null_delta; simp)
qed

lemma set_lebesgue_integral_cong_AE2:
  assumes [measurable]: "A \<in> sets M" "set_borel_measurable M A f" "set_borel_measurable M A g"
  assumes "AE x \<in> A in M. f x = g x"
  shows "(LINT x:A|M. f x) = (LINT x:A|M. g x)"
  using assms
  by(auto simp: set_lebesgue_integral_def set_borel_measurable_def
      intro!: Bochner_Integration.integral_cong_AE)

proposition set_nn_integral_eq_set_integral:
  assumes "AE x\<in>A in M. 0 \<le> f x" "set_integrable M A f"
  shows "(\<integral>\<^sup>+x\<in>A. f x \<partial>M) = (\<integral>x\<in>A. f x \<partial>M)"
proof -
  have "(\<integral>\<^sup>+x\<in>A. f x \<partial>M) = \<integral>\<^sup>+x. ennreal (f x * indicator A x) \<partial>M"
    using nn_integral_set_ennreal by blast
  also have "\<dots> = \<integral>x. f x * indicator A x \<partial>M"
    using assms unfolding set_integrable_def
    by (rewrite nn_integral_eq_integral; force simp add: mult.commute)
  also have "\<dots> = (\<integral>x\<in>A. f x \<partial>M)" unfolding set_lebesgue_integral_def by (simp add: mult.commute)
  finally show ?thesis .
qed

proposition nn_integral_disjoint_family_on_finite:
  assumes [measurable]: "f \<in> borel_measurable M" "\<And>(n::nat). n \<in> S \<Longrightarrow> B n \<in> sets M"
    and "disjoint_family_on B S" "finite S"
  shows "(\<integral>\<^sup>+x \<in> (\<Union>n\<in>S. B n). f x \<partial>M) = (\<Sum>n\<in>S. (\<integral>\<^sup>+x \<in> B n. f x \<partial>M))"
proof -
  let ?A = "\<lambda>n::nat. if n \<in> S then B n else {}"
  have "\<And>n::nat. ?A n \<in> sets M" by simp
  moreover have "disjoint_family ?A"
    unfolding disjoint_family_on_def
  proof -
    { fix m n :: nat
      assume "m \<noteq> n"
      hence "(if m \<in> S then B m else {}) \<inter> (if n \<in> S then B n else {}) = {}"
        using assms unfolding disjoint_family_on_def by simp }
    thus "\<forall>m::nat\<in>UNIV. \<forall>n::nat\<in>UNIV. m \<noteq> n \<longrightarrow>
      (if m \<in> S then B m else {}) \<inter> (if n \<in> S then B n else {}) = {}"
      by blast
  qed
  ultimately have "set_nn_integral M (\<Union> (range ?A)) f = (\<Sum>n. set_nn_integral M (?A n) f)"
    by (rewrite nn_integral_disjoint_family; simp)
  moreover have "set_nn_integral M (\<Union> (range ?A)) f = (\<integral>\<^sup>+x \<in> (\<Union>n\<in>S. B n). f x \<partial>M)"
  proof -
    have "\<Union> (range ?A) = (\<Union>n\<in>S. B n)" by simp
    thus ?thesis by simp
  qed
  moreover have "(\<Sum>n. set_nn_integral M (?A n) f) = (\<Sum>n\<in>S. set_nn_integral M (B n) f)"
    by (rewrite suminf_finite[of S]; simp add: assms)
  ultimately show ?thesis by simp
qed

(* set integral version of lemma nn_integral_monotone_convergence_SUP *)
lemma set_nn_integral_monotone_convergence_SUP:
  assumes "incseq f" and "\<And>i. f i \<in> borel_measurable M" and "A \<in> sets M"
  shows "(\<integral>\<^sup>+x\<in>A. (SUP i. f i x) \<partial>M) = (SUP i. (\<integral>\<^sup>+x\<in>A. f i x \<partial>M))"
proof -
  have "\<And>x. (SUP i. f i x) * indicator A x = (SUP i. f i x * indicator A x)"
    using SUP_mult_right_ennreal by blast
  hence "(\<integral>\<^sup>+x\<in>A. (SUP i. f i x) \<partial>M) = (\<integral>\<^sup>+ x. (SUP i. f i x * indicator A x) \<partial>M)" by simp
  moreover have "incseq (\<lambda>i. (\<lambda>x. f i x * indicator A x))"
    using assms unfolding incseq_def le_fun_def by (simp add: mult_right_mono)
  moreover have "\<And>i. (\<lambda>x. f i x * indicator A x) \<in> borel_measurable M" using assms by simp
  ultimately show ?thesis using nn_integral_monotone_convergence_SUP by force
qed

(* set integral version of lemma nn_integral_sum *)
lemma set_nn_integral_sum:
  assumes "\<And>i. i \<in> P \<Longrightarrow> f i \<in> borel_measurable M" and "A \<in> sets M"
  shows "(\<integral>\<^sup>+x\<in>A. (\<Sum>i\<in>P. f i x) \<partial>M) = (\<Sum>i\<in>P. \<integral>\<^sup>+x\<in>A. f i x \<partial>M)" (is "?LHS = ?RHS")
proof -
  have "?LHS = \<integral>\<^sup>+x. (\<Sum>i\<in>P. f i x * indicator A x) \<partial>M" by (simp add: sum_distrib_right)
  also have "\<dots> = ?RHS" using assms by (rewrite nn_integral_sum; simp)
  finally show ?thesis .
qed

(* set integral version of lemma nn_integral_indicator *)
lemma set_nn_integral_indicator:
  assumes "A \<in> sets M" "B \<in> sets M"
  shows "set_nn_integral M A (indicator B) = emeasure M (B \<inter> A)"
  using assms nn_integral_indicator
  by (metis (no_types, lifting) indicator_inter_arith nn_integral_cong sets.Int)

lemma nn_integral_distr_set:
  assumes [measurable]:"T \<in> measurable M M'" and [measurable]:"f \<in> borel_measurable (distr M M' T)"
    and [measurable]:"A \<in> sets M'" and "\<And>x. x \<in> space M \<Longrightarrow> T x \<in> A"
  shows "integral\<^sup>N (distr M M' T) f = set_nn_integral (distr M M' T) A f"
proof -
  have *:"\<And>x. x \<in> space M \<Longrightarrow> f (T x) * indicator (space M') (T x) = f (T x) * indicator A (T x)"
    using assms measurable_space[of T M M'] by(simp add: indicator_def)
  have "integral\<^sup>N (distr M M' T) f = (\<integral>\<^sup>+x\<in>(space M'). f x \<partial>(distr M M' T))"
    by (rewrite nn_set_integral_space[THEN sym], simp)
  also have "\<dots> = (\<integral>\<^sup>+x\<in>A. f x \<partial>(distr M M' T))"
    by(auto simp add: nn_integral_distr * intro!: nn_integral_cong)
  finally show ?thesis .
qed

(* Analogue for "measure_eqI_lessThan" in the "Lebesgue_Measure" Theory *)
lemma measure_eqI_Ioc:
  fixes M N :: "real measure"
  assumes sets: "sets M = sets borel" "sets N = sets borel"
  assumes fin: "\<And>a b. a \<le> b \<Longrightarrow> emeasure M {a<..b} < \<infinity>"
  assumes eq: "\<And>a b. a \<le> b \<Longrightarrow> emeasure M {a<..b} = emeasure N {a<..b}"
  shows "M = N"
proof (rule measure_eqI_generator_eq_countable)
  let ?Ioc = "\<lambda>(a::real,b::real). {a<..b}" let ?E = "range ?Ioc"
  show "Int_stable ?E" using Int_stable_def Int_greaterThanAtMost by force
  show "?E \<subseteq> Pow UNIV" "sets M = sigma_sets UNIV ?E" "sets N = sigma_sets UNIV ?E"
    unfolding sets by (auto simp add: borel_sigma_sets_Ioc)
  show "\<And>I. I \<in> ?E \<Longrightarrow> emeasure M I = emeasure N I"
  proof -
    fix I assume "I \<in> ?E"
    then obtain a b where "I = {a<..b}" by auto
    thus "emeasure M I = emeasure N I" by (smt (verit, best) eq greaterThanAtMost_empty)
  qed
  show "?Ioc ` (Rats \<times> Rats) \<subseteq> ?E" "(\<Union>i\<in>(Rats\<times>Rats). ?Ioc i) = UNIV"
    using Rats_no_bot_less Rats_no_top_le by auto
  show "countable (?Ioc ` (Rats \<times> Rats))" using countable_rat by blast
  show "\<And>I. I \<in> ?Ioc ` (Rats \<times> Rats) \<Longrightarrow> emeasure M I \<noteq> \<infinity>"
  proof -
    fix I assume "I \<in> ?Ioc ` (Rats \<times> Rats)"
    then obtain a b where "(a,b) \<in> (Rats \<times> Rats)" "I = {a<..b}" by blast
    thus "emeasure M I \<noteq> \<infinity>" by (smt (verit, best) Ioc_inj fin order.strict_implies_not_eq)
  qed
qed

lemma (in finite_measure) distributed_measure:
  assumes "distributed M N X f"
    and f_nn: "\<And>x. x \<in> space N \<Longrightarrow>  f x \<ge> 0"
    and [measurable]:"A \<in> sets N"
  shows "measure M (X -` A \<inter> space M) = (\<integral>x. indicator A x * f x \<partial>N)"
proof -
  have [measurable]:"f \<in> borel_measurable N"
    using assms distributed_real_measurable by blast 
  have "emeasure M (X -` A \<inter> space M) = (\<integral>\<^sup>+x\<in>A. ennreal (f x) \<partial>N)"
    by (rule distributed_emeasure; simp add: assms)
  moreover have "enn2real (\<integral>\<^sup>+x\<in>A. ennreal (f x) \<partial>N) = \<integral>x. indicator A x * f x \<partial>N"
    by(subst integral_eq_nn_integral)
      (use f_nn in "auto simp: mult.commute nn_integral_set_ennreal")
  ultimately show ?thesis using measure_def by metis
qed

lemma set_integrable_const[simp]:
  "A \<in> sets M \<Longrightarrow> emeasure M A < \<infinity> \<Longrightarrow> set_integrable M A (\<lambda>_. c)"
  using has_bochner_integral_indicator unfolding set_integrable_def by simp

lemma set_integral_const[simp]:
  "A \<in> sets M \<Longrightarrow> emeasure M A < \<infinity> \<Longrightarrow> set_lebesgue_integral M A (\<lambda>_. c) = measure M A *\<^sub>R c"
  unfolding set_lebesgue_integral_def using has_bochner_integral_indicator by force

lemma set_integral_empty_0[simp]: "set_lebesgue_integral M {} f = 0"
  unfolding set_lebesgue_integral_def by simp

lemma set_integral_nonneg[simp]:
  fixes f :: "'a \<Rightarrow> real" and A :: "'a set"
  shows "(\<And>x. x \<in> A \<Longrightarrow> 0 \<le> f x) \<Longrightarrow> 0 \<le> set_lebesgue_integral M A f"
  unfolding set_lebesgue_integral_def by (simp add: indicator_times_eq_if(1))

(* Set Integral Version of the Lebesgue's Dominated Convergence Theorem *)
lemma
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}" and w :: "'a \<Rightarrow> real"
  assumes "A \<in> sets M" "set_borel_measurable M A f"
    "\<And>i. set_borel_measurable M A (s i)" "set_integrable M A w"
  assumes lim: "AE x\<in>A in M. (\<lambda>i. s i x) \<longlonglongrightarrow> f x"
  assumes bound: "\<And>i::nat. AE x\<in>A in M. norm (s i x) \<le> w x"
  shows set_integrable_dominated_convergence: "set_integrable M A f"
    and set_integrable_dominated_convergence2: "\<And>i. set_integrable M A (s i)"
    and set_integral_dominated_convergence:
    "(\<lambda>i. set_lebesgue_integral M A (s i)) \<longlonglongrightarrow>  set_lebesgue_integral M A f"
proof -
  have "(\<lambda>x. indicator A x *\<^sub>R f x) \<in> borel_measurable M" and
    "\<And>i. (\<lambda>x. indicator A x *\<^sub>R s i x) \<in> borel_measurable M" and
    "integrable M (\<lambda>x. indicator A x *\<^sub>R w x)"
    using assms unfolding set_borel_measurable_def set_integrable_def by simp_all
  moreover have "AE x in M. (\<lambda>i. indicator A x *\<^sub>R s i x) \<longlonglongrightarrow> indicator A x *\<^sub>R f x"
  proof -
    obtain N where N_null: "N \<in> null_sets M" and
      si_f: "\<And>x. x \<in> space M - N \<Longrightarrow> x \<in> A \<longrightarrow> (\<lambda>i. s i x) \<longlonglongrightarrow> f x"
      using lim AE_E3 by (smt (verit))
    hence "\<And>x. x \<in> space M - N \<Longrightarrow> (\<lambda>i. indicator A x *\<^sub>R s i x) \<longlonglongrightarrow> indicator A x *\<^sub>R f x"
    proof -
      fix x assume asm: "x \<in> space M - N"
      thus "(\<lambda>i. indicator A x *\<^sub>R s i x) \<longlonglongrightarrow> indicator A x *\<^sub>R f x"
      proof (cases \<open>x \<in> A\<close>)
        case True
        with si_f asm show ?thesis by simp
      next 
        case False
        thus ?thesis by simp
      qed
    qed
    thus ?thesis
      by(auto intro!: AE_I'[OF N_null])
  qed
  moreover have "\<And>i. AE x in M. norm (indicator A x *\<^sub>R s i x) \<le> indicator A x *\<^sub>R w x"
  proof -
    fix i
    from bound obtain N where N_null: "N \<in> null_sets M" and
      "\<And>x. x \<in> space M - N \<Longrightarrow> x \<in> A \<longrightarrow> norm (s i x) \<le> w x"
      using AE_E3 by (smt (verit))
    hence "\<And>x. x \<in> space M - N \<Longrightarrow> norm (indicator A x *\<^sub>R s i x) \<le> indicator A x *\<^sub>R w x"
      by (simp add: indicator_scaleR_eq_if)
    with N_null show "AE x in M. norm (indicator A x *\<^sub>R s i x) \<le> indicator A x *\<^sub>R w x"
      by (smt (verit) DiffI eventually_ae_filter mem_Collect_eq subsetI)
  qed
  ultimately show "set_integrable M A f" "\<And>i. set_integrable M A (s i)"
    "(\<lambda>i. set_lebesgue_integral M A (s i)) \<longlonglongrightarrow>  set_lebesgue_integral M A f"
    unfolding set_integrable_def set_lebesgue_integral_def
    by (rule integrable_dominated_convergence, rule integrable_dominated_convergence2,
        rule integral_dominated_convergence)
qed

lemma absolutely_integrable_on_iff_set_integrable:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes [measurable]:"f \<in> borel_measurable lborel" "S \<in> sets lborel"
  shows "set_integrable lborel S f \<longleftrightarrow> f absolutely_integrable_on S"
  by(simp add: integrable_completion set_integrable_def)

corollary integrable_on_iff_set_integrable_nonneg:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x \<ge> 0" "f \<in> borel_measurable lborel"
    and  "S \<in> sets lborel"
  shows "set_integrable lborel S f \<longleftrightarrow> f integrable_on S"
  using absolutely_integrable_on_iff_set_integrable assms
  by (metis absolutely_integrable_on_iff_nonneg)

lemma integrable_on_iff_set_integrable_nonneg_AE:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes "AE x\<in>S in lborel. f x \<ge> 0"
    and [measurable]:"f \<in> borel_measurable lborel" "S \<in> sets lborel"
  shows "set_integrable lborel S f \<longleftrightarrow> f integrable_on S"
proof -
  from assms obtain N where nonneg: "\<And>x. x \<in> S - N \<Longrightarrow> f x \<ge> 0" and null: "N \<in> null_sets lborel"
    using AE_E3 by force
  let ?g = "\<lambda>x. if x \<in> N then 0 else f x"
  have [simp]: "negligible N" using null negligible_iff_null_sets null_sets_completionI by blast
  have "N \<in> sets lborel" using null by auto
  hence [simp]: "?g \<in> borel_measurable borel" using assms by force
  have "set_integrable lborel S f \<longleftrightarrow> set_integrable lborel S ?g"
  proof -
    have "AE x\<in>S in lborel. f x = ?g x"
      by(auto intro!: AE_I'[OF null])
    thus ?thesis using assms by (intro set_integrable_cong_AE[of f _ ?g S]; simp)
  qed
  also have "\<dots> \<longleftrightarrow> ?g integrable_on S"
    using assms by (intro integrable_on_iff_set_integrable_nonneg; simp add: nonneg)
  also have "\<dots> \<longleftrightarrow> f integrable_on S" by (rule integrable_spike_cong[of N]; simp)
  finally show ?thesis .
qed

lemma set_borel_integral_eq_integral_nonneg:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x \<ge> 0" "f \<in> borel_measurable borel" "S \<in> sets borel"
  shows "(LINT x : S | lborel. f x) = integral S f"
    \<comment> \<open>Note that \<open>0 = 0\<close> holds when the integral diverges.\<close>
proof (cases \<open>set_integrable lborel S f\<close>)
  case True
  thus ?thesis using set_borel_integral_eq_integral by force
next
  case False
  hence "(LINT x : S | lborel. f x) = 0"
    unfolding set_lebesgue_integral_def set_integrable_def
    by (rewrite not_integrable_integral_eq; simp)
  moreover have "integral S f = 0"
    apply (rule not_integrable_integral)
    using False assms by (rewrite in asm integrable_on_iff_set_integrable_nonneg; simp)
  ultimately show ?thesis ..
qed

lemma set_borel_integral_eq_integral_nonneg_AE:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes "AE x\<in>S in lborel. f x \<ge> 0" "f \<in> borel_measurable borel" "S \<in> sets borel"
  shows "(LINT x : S | lborel. f x) = integral S f"
    \<comment> \<open>Note that \<open>0 = 0\<close> holds when the integral diverges.\<close>
proof (cases \<open>set_integrable lborel S f\<close>)
  case True
  thus ?thesis using set_borel_integral_eq_integral by force
next
  case False
  hence "(LINT x : S | lborel. f x) = 0"
    unfolding set_lebesgue_integral_def set_integrable_def
    by (rewrite not_integrable_integral_eq; simp)
  moreover have "integral S f = 0"
    apply (rule not_integrable_integral)
    using False assms by (rewrite in asm integrable_on_iff_set_integrable_nonneg_AE; simp)
  ultimately show ?thesis ..
qed

subsection \<open>Set Lebesgue Integrability on Affine Transformation\<close>

lemma set_integrable_Icc_affine_pos_iff:
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}" and a b c t :: real
  assumes [arith]:"c > 0"
  shows "set_integrable lborel {(a-t)/c..(b-t)/c} (\<lambda>x. f (t + c*x))
    \<longleftrightarrow> set_integrable lborel {a..b} f"
  unfolding set_integrable_def indicator_Icc_affine_pos_inverse[OF assms]
  by(intro lborel_integrable_real_affine_iff) simp

corollary set_integrable_Icc_shift:
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}" and a b t :: real
  shows "set_integrable lborel {a-t..b-t} (\<lambda>x. f (t+x)) \<longleftrightarrow> set_integrable lborel {a..b} f"
  using set_integrable_Icc_affine_pos_iff[where c=1] by simp

lemma set_integrable_Ici_affine_pos_iff:
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}" and a c t :: real
  assumes [arith]:"c > 0"
  shows "set_integrable lborel {(a-t)/c..} (\<lambda>x. f (t + c*x))
    \<longleftrightarrow> set_integrable lborel {a..} f"
  unfolding set_integrable_def indicator_Ici_affine_pos_inverse[OF assms]
  by (rule lborel_integrable_real_affine_iff) simp

corollary set_integrable_Ici_shift:
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}" and a t :: real
  shows "set_integrable lborel {a-t..} (\<lambda>x. f (t+x)) \<longleftrightarrow> set_integrable lborel {a..} f"
  using set_integrable_Ici_affine_pos_iff[where c=1] by simp

lemma set_integrable_Iic_affine_pos_iff:
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}" and b c t :: real
  assumes [arith]:"c > 0"
  shows "set_integrable lborel {..(b-t)/c} (\<lambda>x. f (t + c*x))
    \<longleftrightarrow> set_integrable lborel {..b} f"
  unfolding set_integrable_def indicator_Iic_affine_pos_inverse[OF assms]
  by (rule lborel_integrable_real_affine_iff) simp

corollary set_integrable_Iic_shift:
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}" and b t :: real
  shows "set_integrable lborel {..b-t} (\<lambda>x. f (t+x)) \<longleftrightarrow> set_integrable lborel {..b} f"
  using set_integrable_Iic_affine_pos_iff[where c=1] by simp

lemma set_integrable_Icc_affine_neg_iff:
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}" and a b c t :: real
  assumes [arith]:"c < 0"
  shows "set_integrable lborel {(b-t)/c..(a-t)/c} (\<lambda>x. f (t + c*x))
    \<longleftrightarrow> set_integrable lborel {a..b} f"
  unfolding set_integrable_def indicator_Icc_affine_neg_inverse[OF assms]
  by (rule lborel_integrable_real_affine_iff) simp

corollary set_integrable_Icc_reverse:
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}" and a b t :: real
  shows "set_integrable lborel {t-b..t-a} (\<lambda>x. f (t-x)) \<longleftrightarrow> set_integrable lborel {a..b} f"
  using set_integrable_Icc_affine_neg_iff[where c="-1"] by simp

lemma set_integrable_Ici_affine_neg_iff:
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}" and b c t :: real
  assumes [arith]:"c < 0"
  shows "set_integrable lborel {(b-t)/c..} (\<lambda>x. f (t + c*x))
    \<longleftrightarrow> set_integrable lborel {..b} f"
  unfolding set_integrable_def indicator_Ici_affine_neg_inverse[OF assms]
  by (rule lborel_integrable_real_affine_iff) simp

corollary set_integrable_Ici_reverse:
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}" and b t :: real
  shows "set_integrable lborel {t-b..} (\<lambda>x. f (t-x)) \<longleftrightarrow> set_integrable lborel {..b} f"
  using set_integrable_Ici_affine_neg_iff[where c="-1"] by simp

lemma set_integrable_Iic_affine_neg_iff:
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}" and a c t :: real
  assumes [arith]:"c < 0"
  shows "set_integrable lborel {..(a-t)/c} (\<lambda>x. f (t + c*x))
    \<longleftrightarrow> set_integrable lborel {a..} f"
  unfolding set_integrable_def indicator_Iic_affine_neg_inverse[OF assms]
  by (rule lborel_integrable_real_affine_iff) simp

corollary set_integrable_Iic_reverse:
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}" and a t :: real
  shows "set_integrable lborel {..t-a} (\<lambda>x. f (t-x)) \<longleftrightarrow> set_integrable lborel {a..} f"
  using set_integrable_Iic_affine_neg_iff[where c="-1"] by simp

subsection \<open>Set Lebesgue Integral on Affine Transformation\<close>

lemma lborel_set_integral_Icc_affine_pos:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}" and a b c :: real
  assumes [arith]:"c > 0"
  shows "(\<integral>x\<in>{a..b}. f x \<partial>lborel) = c *\<^sub>R (\<integral>x\<in>{(a-t)/c..(b-t)/c}. f (t + c*x) \<partial>lborel)"
  unfolding set_lebesgue_integral_def indicator_Icc_affine_pos_inverse[OF assms]
  using lborel_integral_real_affine[where c=c] by force

corollary lborel_set_integral_Icc_shift:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}" and a b :: real
  shows "(\<integral>x\<in>{a..b}. f x \<partial>lborel) = (\<integral>x\<in>{a-t..b-t}. f (t+x) \<partial>lborel)"
  using lborel_set_integral_Icc_affine_pos[where c=1] by simp

lemma lborel_set_integral_Ici_affine_pos:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}" and a c :: real
  assumes [arith]:"c > 0"
  shows "(\<integral>x\<in>{a..}. f x \<partial>lborel) = c *\<^sub>R (\<integral>x\<in>{(a-t)/c..}. f (t + c*x) \<partial>lborel)"
  unfolding set_lebesgue_integral_def indicator_Ici_affine_pos_inverse[OF assms]
  using lborel_integral_real_affine[where c=c] by force

corollary lborel_set_integral_Ici_shift:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}" and a::real
  shows "(\<integral>x\<in>{a..}. f x \<partial>lborel) = (\<integral>x\<in>{a-t..}. f (t+x) \<partial>lborel)"
  using lborel_set_integral_Ici_affine_pos[where c=1] by simp

lemma lborel_set_integral_Iic_affine_pos:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}" and b c :: real
  assumes [arith]:"c > 0"
  shows "(\<integral>x\<in>{..b}. f x \<partial>lborel) = c *\<^sub>R (\<integral>x\<in>{..(b-t)/c}. f (t + c*x) \<partial>lborel)"
  unfolding set_lebesgue_integral_def indicator_Iic_affine_pos_inverse[OF assms]
  using lborel_integral_real_affine[where c=c] by force

corollary lborel_set_integral_Iic_shift:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}" and b::real
  shows "(\<integral>x\<in>{..b}. f x \<partial>lborel) = (\<integral>x\<in>{..b-t}. f (t+x) \<partial>lborel)"
  using lborel_set_integral_Iic_affine_pos[where c=1] by simp

lemma lborel_set_integral_Icc_affine_neg:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}" and a b c :: real
  assumes [arith]:"c < 0"
  shows "(\<integral>x\<in>{a..b}. f x \<partial>lborel) = -c *\<^sub>R (\<integral>x\<in>{(b-t)/c..(a-t)/c}. f (t + c*x) \<partial>lborel)"
  unfolding set_lebesgue_integral_def indicator_Icc_affine_neg_inverse[OF assms]
  using lborel_integral_real_affine[where c=c] by force

corollary lborel_set_integral_Icc_reverse:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}" and a b :: real
  shows "(\<integral>x\<in>{a..b}. f x \<partial>lborel) = (\<integral>x\<in>{t-b..t-a}. f (t-x) \<partial>lborel)"
  using lborel_set_integral_Icc_affine_neg[where c="-1"] by simp

lemma lborel_set_integral_Ici_affine_neg:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}" and b c :: real
  assumes [arith]:"c < 0"
  shows "(\<integral>x\<in>{..b}. f x \<partial>lborel) = -c *\<^sub>R (\<integral>x\<in>{(b-t)/c..}. f (t + c*x) \<partial>lborel)"
  unfolding set_lebesgue_integral_def indicator_Ici_affine_neg_inverse[OF assms]
  using lborel_integral_real_affine[where c=c] by force

corollary lborel_set_integral_Ici_reverse:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}" and b::real
  shows "(\<integral>x\<in>{..b}. f x \<partial>lborel) = (\<integral>x\<in>{t-b..}. f (t-x) \<partial>lborel)"
  using lborel_set_integral_Ici_affine_neg[where c="-1"] by simp

lemma lborel_set_integral_Iic_affine_neg:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}" and a c :: real
  assumes [arith]:"c < 0"
  shows "(\<integral>x\<in>{a..}. f x \<partial>lborel) = -c *\<^sub>R (\<integral>x\<in>{..(a-t)/c}. f (t + c*x) \<partial>lborel)"
  unfolding set_lebesgue_integral_def indicator_Iic_affine_neg_inverse[OF assms]
  using lborel_integral_real_affine[where c=c] by force

corollary lborel_set_integral_Iic_reverse:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}" and a::real
  shows "(\<integral>x\<in>{a..}. f x \<partial>lborel) = (\<integral>x\<in>{..t-a}. f (t-x) \<partial>lborel)"
  using lborel_set_integral_Iic_affine_neg[where c="-1"] by simp

lemma set_integrable_Ici_equiv_aux:
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}" and a b :: real
  assumes "\<And>c d. set_integrable lborel {c..d} f" "a \<le> b"
  shows "set_integrable lborel {a..} f \<longleftrightarrow> set_integrable lborel {b..} f"
proof
  assume "set_integrable lborel {a..} f"
  thus "set_integrable lborel {b..} f" by (rule set_integrable_subset; simp add: assms)
next
  assume "set_integrable lborel {b..} f"
  moreover have "set_integrable lborel {a..b} f" using assms by blast
  moreover have "{a..} = {a..b} \<union> {b..}" using assms by auto
  ultimately show "set_integrable lborel {a..} f" using set_integrable_Un by force
qed

corollary set_integrable_Ici_equiv:
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}" and a b :: real
  assumes "\<And>c d. set_integrable lborel {c..d} f"
  shows "set_integrable lborel {a..} f \<longleftrightarrow> set_integrable lborel {b..} f"
  using set_integrable_Ici_equiv_aux assms by (metis linorder_linear)

lemma set_integrable_Iic_equiv:
  fixes f :: "real \<Rightarrow> real" and a b :: real
  assumes "\<And>c d. set_integrable lborel {c..d} f"
  shows "set_integrable lborel {..a} f \<longleftrightarrow> set_integrable lborel {..b} f" (is "?LHS \<longleftrightarrow> ?RHS")
proof -
  have "?LHS \<longleftrightarrow> set_integrable lborel {-a..} (\<lambda>x. f (-x))"
    using set_integrable_Ici_reverse[where t=0] by force
  also have "\<dots> \<longleftrightarrow> set_integrable lborel {-b..} (\<lambda>x. f (-x))"
  proof -
    have "\<And>c d. set_integrable lborel {c..d} (\<lambda>x. f (-x))"
      apply (rewrite at "{\<hole>.._}" minus_minus[THEN sym])
      apply (rewrite at "{_..\<hole>}" minus_minus[THEN sym])
      using assms set_integrable_Icc_reverse[where t=0] by force
    thus ?thesis by (rule set_integrable_Ici_equiv)
  qed
  also have "\<dots> \<longleftrightarrow> ?RHS" using set_integrable_Ici_reverse[where t=0] by force
  finally show ?thesis .
qed

subsection \<open>Alternative Integral Test\<close>

lemma nn_integral_suminf_Ico_real_nat:
  fixes a::real and f :: "real \<Rightarrow> ennreal"
  assumes "f \<in> borel_measurable lborel"
  shows "(\<integral>\<^sup>+x\<in>{a..}. f x \<partial>lborel) = (\<Sum>k. \<integral>\<^sup>+x\<in>{a+k..<a+k+1}. f x \<partial>lborel)"
  apply (rewrite Ico_real_nat_union[THEN sym])
  using Ico_real_nat_disjoint assms by (intro nn_integral_disjoint_family; simp)

(* Another Version of theorem integral_test *)
theorem set_integrable_iff_summable:
  fixes a::real and f :: "real \<Rightarrow> real"
  assumes "antimono_on {a..} f" and f_nn: "\<And>x. a \<le> x \<Longrightarrow> f x \<ge> 0"
    and [measurable]:"f \<in> borel_measurable lborel"
  shows "set_integrable lborel {a..} f \<longleftrightarrow> summable (\<lambda>k. f (a+k))"
proof
  assume asm: "set_integrable lborel {a..} f"
  have "\<forall>k\<ge>0. norm (f (a+(k+1::nat))) \<le> (\<integral>x\<in>{a+k..<a+k+1}. f x \<partial>lborel)"
  proof -
    { fix k::nat
      have "norm (f (a+(k+1::nat))) = f (a+k+1)"
        using assms by (smt (verit) of_nat_0_le_iff of_nat_1 of_nat_add real_norm_def)
      also have "\<dots> = (\<integral>x\<in>{a+k..<a+k+1}. f (a+k+1) \<partial>lborel)"
        unfolding set_lebesgue_integral_def by simp
      also have "\<dots> \<le> (\<integral>x\<in>{a+k..<a+k+1}. f x \<partial>lborel)"
        using assms(1)
        by(intro set_integral_mono[OF _ set_integrable_restrict_space[of lborel "{a..}"]])
          (auto simp: asm sets_restrict_space monotone_on_def)
      finally have "norm (f (a+(k+1::nat))) \<le> (\<integral>x\<in>{a+k..<a+k+1}. f x \<partial>lborel)" . }
    thus ?thesis by simp
  qed
  moreover have "summable (\<lambda>k. \<integral>x\<in>{a+k..<a+k+1}. f x \<partial>lborel)"
  proof -
    have "(\<integral>\<^sup>+x\<in>{a..}. ennreal (f x) \<partial>lborel) \<noteq> \<infinity>"
      using asm unfolding set_integrable_def
      by (metis (no_types, lifting) ext mult.commute indicator_mult_ennreal
          integrableD(2) real_scaleR_def)
    moreover have "(\<Sum>i. (\<integral>\<^sup>+x\<in>{a + real i..<a + real i + 1}. ennreal (f x) \<partial>lborel))
                 = (\<Sum>i. ennreal (set_lebesgue_integral lborel {a + real i..<a + real i + 1} f))"
      using f_nn by(auto intro!: suminf_cong set_nn_integral_eq_set_integral set_integrable_subset[OF asm])
    ultimately show ?thesis
      by(auto simp: nn_integral_suminf_Ico_real_nat 
          intro!: summable_suminf_not_top set_integral_nonneg f_nn)
  qed
  ultimately have "summable (\<lambda>k. f (a+(k+1::nat)))"
    using summable_comparison_test by (metis (no_types, lifting))
  thus "summable (\<lambda>k. f (a+k))" using summable_iff_shift by blast
next
  assume asm: "summable (\<lambda>k. f (a+k))"
  hence "(\<integral>\<^sup>+x\<in>{a..}. ennreal \<bar>f x\<bar> \<partial>lborel) < \<infinity>"
  proof -
    have "(\<integral>\<^sup>+x\<in>{a..}. ennreal \<bar>f x\<bar> \<partial>lborel) = (\<integral>\<^sup>+x\<in>{a..}. ennreal (f x) \<partial>lborel)"
      using assms by (metis abs_of_nonneg atLeast_iff indicator_simps(2) mult_eq_0_iff)
    also have "\<dots>  = (\<Sum>k. \<integral>\<^sup>+x\<in>{a+k..<a+k+1}. ennreal (f x) \<partial>lborel)"
      using assms by (rewrite nn_integral_suminf_Ico_real_nat; simp)
    also have "\<dots> \<le> (\<Sum>k. \<integral>\<^sup>+x\<in>{a+k..<a+k+1}. ennreal (f (a+k)) \<partial>lborel)"
    proof -
      have "\<And>(k::nat) x. x\<in>{a+k..<a+k+1} \<Longrightarrow> f x \<le> f (a+k)"
        using assms unfolding monotone_on_def by auto
      thus ?thesis
        by(intro suminf_le nn_integral_mono)
          (auto simp: indicator_def intro!: ennreal_leI)
    qed
    also have "\<dots> = (\<Sum>k. ennreal (f (a+k)))"
      apply (rule suminf_cong)
      by (rewrite nn_integral_cmult_indicator; simp)
    also have "\<dots> < \<infinity>"
      unfolding infinity_ennreal_def apply (rewrite less_top[THEN sym])
      using asm assms
      by (metis (mono_tags, lifting) ennreal_suminf_neq_top le_add_same_cancel1
          of_nat_0_le_iff suminf_cong)
    finally show ?thesis .
  qed
  moreover have "set_borel_measurable lborel {a..} f"
    using assms unfolding set_borel_measurable_def by simp
  ultimately show "set_integrable lborel {a..} f" by (rewrite set_integrable_iff_bounded) auto
qed

subsection \<open>Interchange of Differentiation and Lebesgue Integration\<close>

definition measurable_extension :: "'a measure \<Rightarrow> 'b measure \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
  "measurable_extension M N f \<equiv> (SOME g. g \<in> M \<rightarrow>\<^sub>M N \<and> (AE x in M. f x = g x))"
  \<comment> \<open>The term \<open>measurable_extension\<close> is proposed by Reynald Affeldt.\<close>
  \<comment> \<open>This function is used to make an almost-everywhere-defined function measurable.\<close>

lemma measurable_extension_def2:
  "measurable_extension M N f = (SOME g. g \<in> M \<rightarrow>\<^sub>M N \<and> (\<exists>S\<in>(null_sets M). {x \<in> space M. f x \<noteq> g x} \<subseteq> S))"
  by(simp add: measurable_extension_def eventually_ae_filter)

lemma
  fixes f g
  assumes "g \<in> M \<rightarrow>\<^sub>M N" "AE x in M. f x = g x"
  shows measurable_extensionI: "AE x in M. f x = measurable_extension M N f x"
    (is "AE x in M. f x = ?me x")
    and measurable_extensionI2: "AE x in M. g x = measurable_extension M N f x"
    and measurable_extension_measurable: "measurable_extension M N f \<in> measurable M N"
proof -
  have "?me \<in> M \<rightarrow>\<^sub>M N \<and> (AE x in M. f x = ?me x)"
    unfolding measurable_extension_def
    by(rule someI[where P="\<lambda>h. h \<in> M \<rightarrow>\<^sub>M N \<and> (AE x in M. f x = h x)"]) (use assms in auto)
  thus "AE x in M. f x = ?me x" "AE x in M. g x = ?me x" "?me \<in> M \<rightarrow>\<^sub>M N"
    using assms by auto
qed

lemma measurable_extension_measurable'[measurable]:
  assumes "f \<in>  M \<rightarrow>\<^sub>M N"
  shows "measurable_extension M N f \<in> M \<rightarrow>\<^sub>M N"
  using assms by(auto intro!: measurable_extension_measurable)

lemma measurable_extensionI'[simp]:
  assumes "f \<in>  M \<rightarrow>\<^sub>M N"
  shows "AE x in M. f x = measurable_extension M N f x"
  using assms by(auto intro!: measurable_extensionI)

corollary measurable_measurable_extension_AE:
  fixes f
  assumes "f \<in> M \<rightarrow>\<^sub>M N"
  shows "AE x in M. f x = measurable_extension M N f x"
  by (rule measurable_extensionI[where g=f]; simp add: assms)

abbreviation borel_measurable_extension ::
  "'a measure \<Rightarrow> ('a \<Rightarrow> 'b::topological_space) \<Rightarrow> 'a \<Rightarrow> 'b" where
  "borel_measurable_extension M f \<equiv> measurable_extension M borel f"

definition set_borel_measurable_extension ::
  "'a measure \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b::topological_space) \<Rightarrow> 'a \<Rightarrow> 'b"
  where "set_borel_measurable_extension M A f = borel_measurable_extension (restrict_space M A) f"

lemma
  fixes f g :: "'a \<Rightarrow> 'b::real_normed_vector" and A
  assumes [measurable]:"A \<in> sets M" "set_borel_measurable M A g" "AE x\<in>A in M. f x = g x"
  shows set_borel_measurable_extensionI:
    "AE x\<in>A in M. f x = set_borel_measurable_extension M A f x" and
    set_borel_measurable_extensionI2:
    "AE x\<in>A in M. g x = set_borel_measurable_extension M A f x" and
    set_borel_measurable_extension_measurable:
    "set_borel_measurable M A (set_borel_measurable_extension M A f)"
  using assms measurable_extensionI2[where g=g] measurable_extensionI[where g=g]
    measurable_extension_measurable
  by(auto simp: set_borel_measurable_extension_def AE_restrict_space_iff[symmetric]
      set_borel_measurable_restrict_space_iff[symmetric])

corollary set_borel_measurable_measurable_extension_AE:
  fixes f::"'a \<Rightarrow> 'b::real_normed_vector" and A
  assumes "set_borel_measurable M A f" "A \<in> sets M"
  shows "AE x\<in>A in M. f x = set_borel_measurable_extension M A f x"
  by (simp add: assms set_borel_measurable_extensionI2)

proposition interchange_deriv_LINT_general:
  fixes a b :: real and f :: "real \<Rightarrow> 'a \<Rightarrow> real" and g :: "'a \<Rightarrow> real"
  assumes f_integ: "\<And>r. r\<in>{a<..<b} \<Longrightarrow> integrable M (f r)" and
    f_diff: "AE x in M. (\<lambda>r. f r x) differentiable_on {a<..<b}" and
    Df_bound: "AE x in M. \<forall>r\<in>{a<..<b}. \<bar>deriv (\<lambda>r. f r x) r\<bar> \<le> g x" "integrable M g"
  shows "\<And>r. r\<in>{a<..<b} \<Longrightarrow> ((\<lambda>r. \<integral>x. f r x \<partial>M) has_real_derivative
    \<integral>x. borel_measurable_extension M (\<lambda>x. deriv (\<lambda>r. f r x) r) x \<partial>M) (at r)"
proof -
  text \<open>Preparation\<close>
  have f_msr[measurable]: "\<And>r. a < r \<Longrightarrow> r <b \<Longrightarrow> f r \<in> borel_measurable M" using f_integ by auto
  from AE_E3 f_diff obtain N1 where N1_null: "N1 \<in> null_sets M" and
    "\<And>x. x \<in> space M - N1 \<Longrightarrow> (\<lambda>s. f s x) differentiable_on {a<..<b}"
    by metis
  hence f_diffN1: "\<And>x. x \<in> space M - N1 \<Longrightarrow> (\<lambda>s. f s x) differentiable_on {a<..<b}"
    by (meson Diff_iff sets.sets_into_space subset_eq)
  from Df_bound obtain N2 where N2_null: "N2 \<in> null_sets M" and
    "\<And>x. x \<in> space M - N2 \<Longrightarrow> \<forall>r\<in>{a<..<b}. \<bar>deriv (\<lambda>s. f s x) r\<bar> \<le> g x"
    by (auto simp: eventually_ae_filter)
  hence Df_boundN2:"\<And>x. x \<in> space M - N2 \<Longrightarrow> \<forall>r\<in>{a<..<b}. \<bar>deriv (\<lambda>s. f s x) r\<bar> \<le> g x"
    by (meson Diff_iff sets.sets_into_space subset_eq)
  define N where "N \<equiv> N1 \<union> N2"
  let ?CN = "space M - N"
  have N_null: "N \<in> null_sets M" and N_msr[measurable]: "N \<in> sets M"
    unfolding N_def using N1_null N2_null by auto
  have f_diffCN: "\<And>x. x\<in>?CN \<Longrightarrow> (\<lambda>s. f s x) differentiable_on {a<..<b}"
    unfolding N_def using f_diffN1 by simp
  define Df :: "real \<Rightarrow> 'a \<Rightarrow> real" where
    "Df r x \<equiv> indicator ({a<..<b}\<times>?CN) (r,x) * deriv (\<lambda>s. f s x) r" for r x
  have Df_boundCN: "\<And>x. x\<in>?CN \<Longrightarrow> \<forall>r\<in>{a<..<b}. \<bar>Df r x\<bar> \<le> g x"
    unfolding Df_def N_def using Df_boundN2 by simp
  text \<open>Main Part of the Proof\<close>
  fix r assume r_ab: "r\<in>{a<..<b}"
  then obtain e where e_pos: "e > 0" and ball_ab: "ball r e \<subseteq> {a<..<b}"
    by (meson openE open_greaterThanLessThan)
  have "\<And>d::nat\<Rightarrow>real. \<lbrakk>\<forall>i. d i \<in> UNIV-{0}; d \<longlonglongrightarrow> 0\<rbrakk> \<Longrightarrow>
    ((\<lambda>h. ((\<integral>x. f (r+h) x \<partial>M) - \<integral>x. f r x \<partial>M) / h) \<circ> d) \<longlonglongrightarrow>
    \<integral>x. borel_measurable_extension M (\<lambda>y. deriv (\<lambda>s. f s y) r) x \<partial>M"
  proof -
    fix d::"nat\<Rightarrow>real" assume d_neq0: "\<forall>i. d i \<in> UNIV-{0}" and d_to0: "d \<longlonglongrightarrow> 0"
    then obtain m where "\<forall>i\<ge>m. \<bar>d i - 0\<bar> < e" using LIMSEQ_def e_pos dist_real_def by metis
    hence rd_ab: "\<And>n. r + d (n+m) \<in> {a<..<b}" using dist_real_def ball_ab by (simp add: subset_eq)
    have limf_Df: "\<And>x. x\<in>?CN \<Longrightarrow> (\<lambda>n. (f (r + d (n+m)) x - f r x) / d (n+m)) \<longlonglongrightarrow> Df r x"
    proof -
      fix x assume x_CN: "x\<in>?CN"
      hence "(\<lambda>s. f s x) field_differentiable (at r)"
        using f_diffCN r_ab
        by (metis at_within_open differentiable_on_eq_field_differentiable_real
            open_greaterThanLessThan)
      hence "((\<lambda>h. (f (r+h) x - f r x) / h) \<longlongrightarrow> Df r x) (at 0)"
        using r_ab x_CN by (simp add: Df_def DERIV_def DERIV_deriv_iff_field_differentiable[symmetric])
      hence "(\<lambda>i. (f (r + d i) x - f r x) / d i) \<longlonglongrightarrow> Df r x"
        using d_neq0 d_to0 by(simp add: tendsto_at_iff_sequentially comp_def)
      thus "(\<lambda>n. (f (r + d (n+m)) x - f r x) / d (n+m)) \<longlonglongrightarrow> Df r x"
        by (rule LIMSEQ_ignore_initial_segment[where k=m])
    qed
    have Df_eq:
      "Df r = (\<lambda>x. indicator ?CN x * lim (\<lambda>n. (f (r + d (n+m)) x - f r x) / d (n+m)))"
    proof
      fix x
      show "Df r x = indicator ?CN x * lim (\<lambda>n. (f (r + d (n+m)) x - f r x) / d (n+m))"
      proof (cases \<open>x\<in>?CN\<close>)
        case True
        hence "lim (\<lambda>n. (f (r + d (n+m)) x - f r x) / d (n+m)) = Df r x"
          by (intro limI, rule limf_Df)
        thus ?thesis using True by simp
      next
        case False
        thus ?thesis unfolding Df_def by simp
      qed
    qed
    hence Df_msr[measurable]: "Df r \<in> borel_measurable M"
      using r_ab rd_ab by(simp add: Df_eq)
    have "((\<lambda>h. ((\<integral>x. f (r+h) x \<partial>M) - \<integral>x. f r x \<partial>M) / h) \<circ> d) \<longlonglongrightarrow>
      \<integral>x. lim (\<lambda>n. (f (r + d (n+m)) x - f r x) / d (n+m)) \<partial>M"
    proof -
      have "(\<lambda>n. \<integral>x. (f (r + d (n+m)) x - f r x) / d (n+m) \<partial>M) \<longlonglongrightarrow>
        \<integral>x. lim (\<lambda>n. (f (r + d (n+m)) x - f r x) / d (n+m)) \<partial>M"
      proof - \<comment> \<open>by Lebesgue's Dominated Convergence Theorem\<close>
        have "AE x in M. (\<lambda>n. (f (r + d (n+m)) x - f r x) / d (n+m)) \<longlonglongrightarrow>
          lim (\<lambda>n. (f (r + d (n+m)) x - f r x) / d (n+m))"
          using limf_Df Df_eq N_null by (smt (verit) DiffI AE_I' limI mem_Collect_eq subset_eq)
        moreover have "\<And>n. AE x in M. norm ((f (r + d (n+m)) x - f r x) / d (n+m)) \<le> g x"
        proof -
          fix n
          { fix x assume x_CN: "x\<in>?CN"
            let ?I = "{r..(r + d (n+m))} \<union> {(r + d (n+m))..r}"
            have f_diffI: "(\<lambda>s. f s x) differentiable_on ?I"
              apply (rule differentiable_on_subset[where t="{a<..<b}"], rule f_diffCN, rule x_CN)
              using r_ab rd_ab[of n] by (rewrite Un_subset_iff, auto)
            hence "continuous_on ?I (\<lambda>s. f s x)" "(\<lambda>s. f s x) differentiable_on interior ?I"
               apply -
              using differentiable_imp_continuous_on apply blast
              by (metis differentiable_on_subset interior_subset)
            then obtain t where t_01: "t\<in>{0<..<1}" and
              f_MVT: "f (r + d (n+m)) x - f r x = d (n+m) * deriv (\<lambda>s. f s x) (r + t * (d (n+m)))"
              by (rule MVT_order_free)
            hence rtd_ab: "r + t * d (n+m) \<in> {a<..<b}"
              using r_ab rd_ab[of n]
              by simp (smt (verit, ccfv_threshold) mult_less_cancel_left mult_less_cancel_right2)
                (* TODO: fix this proof *)
            have "d (n+m) * deriv (\<lambda>s. f s x) (r + t * (d (n+m))) =
              d (n+m) * Df (r + t * (d (n+m))) x"
            proof -
              have "r + t * (d (n+m)) \<in> {a<..<b}"
                using r_ab rd_ab[of n] t_01 rtd_ab by blast
              thus ?thesis unfolding Df_def using x_CN by simp
            qed
            with f_MVT have "(f (r + d (n+m)) x - f r x) / d (n+m) = Df (r + t * (d (n+m))) x"
              using d_neq0 by simp
            moreover have "\<bar>Df (r + t * (d (n+m))) x\<bar> \<le> g x" using Df_boundCN x_CN rtd_ab by simp
            ultimately have "\<bar>(f (r + d (n+m)) x - f r x) / d (n+m)\<bar> \<le> g x" by simp }
          thus "AE x in M. norm ((f (r + d (n+m)) x - f r x) / d (n+m)) \<le> g x"
            unfolding real_norm_def by(auto intro!: AE_I'[OF N_null])
        qed
        ultimately show "((\<lambda>n. \<integral>x. (f (r + d (n+m)) x - f r x) / d (n+m) \<partial>M) \<longlonglongrightarrow>
          \<integral>x. lim (\<lambda>n. (f (r + d (n+m)) x - f r x) / d (n+m)) \<partial>M)"
          using Df_bound rd_ab r_ab
          by(intro integral_dominated_convergence[where w=g]) simp_all
      qed
      moreover have "\<And>n. ((\<integral>x. f (r + d (n+m)) x \<partial>M) - \<integral>x. f r x \<partial>M) / d (n+m) =
        \<integral>x. (f (r + d (n+m)) x - f r x) / d (n+m) \<partial>M"
        using d_neq0 rd_ab r_ab f_integ by simp
      ultimately show ?thesis
        unfolding comp_def using d_neq0
        by (auto simp: LIMSEQ_offset[where k=m])
    qed
    moreover have "(\<integral>x. lim (\<lambda>n. (f (r + d (n+m)) x - f r x) / d (n+m)) \<partial>M) =
      \<integral>x. borel_measurable_extension M (\<lambda>y. deriv (\<lambda>s. f s y) r) x \<partial>M"
    proof -
      have "(\<integral>x. lim (\<lambda>n. (f (r + d (n+m)) x - f r x) / d (n+m)) \<partial>M) = \<integral>x. Df r x \<partial>M"
      proof -
        have "AE x in M. lim (\<lambda>n. (f (r + d (n+m)) x - f r x) / d (n+m)) = Df r x"
        proof -
          { fix x assume x_CN: "x\<in>?CN"
            hence "lim (\<lambda>n. (f (r + d (n+m)) x - f r x) / d (n+m)) = Df r x" by (simp add: Df_eq) }
          thus ?thesis using AE_I' N_null by (smt (verit, del_insts) DiffI mem_Collect_eq subsetI)
        qed
        thus ?thesis 
          using r_ab rd_ab by (intro integral_cong_AE) auto
      qed
      also have "\<dots> = \<integral>x. borel_measurable_extension M (\<lambda>y. deriv (\<lambda>s. f s y) r) x \<partial>M"
      proof -
        have "AE x in M. Df r x = borel_measurable_extension M (\<lambda>y. deriv (\<lambda>s. f s y) r) x" and
          "borel_measurable_extension M (\<lambda>y. deriv (\<lambda>s. f s y) r) \<in> borel_measurable M"
        proof -
          have "{x \<in> space M. deriv (\<lambda>s. f s x) r \<noteq> Df r x} \<subseteq> N"
          proof -
            { fix x assume "x\<in>?CN"
              hence "deriv (\<lambda>s. f s x) r = Df r x" unfolding Df_def using r_ab by simp }
            thus ?thesis by blast
          qed
          hence *:"AE x in M. deriv (\<lambda>s. f s x) r = Df r x"
            using N_null eventually_ae_filter by blast
          thus "AE x in M. Df r x = borel_measurable_extension M (\<lambda>y. deriv (\<lambda>s. f s y) r) x" and
            "borel_measurable_extension M (\<lambda>y. deriv (\<lambda>s. f s y) r) \<in> borel_measurable M"
            by(auto intro!: measurable_extensionI2[OF _ *] measurable_extension_measurable[OF _ *])
        qed
        thus ?thesis using Df_msr by (intro integral_cong_AE; simp)
      qed
      finally show ?thesis .
    qed
    ultimately show "((\<lambda>h. ((\<integral>x. f (r+h) x \<partial>M) - \<integral>x. f r x \<partial>M) / h) \<circ> d) \<longlonglongrightarrow>
      \<integral>x. borel_measurable_extension M (\<lambda>y. deriv (\<lambda>s. f s y) r) x \<partial>M"
      using tendsto_cong_limit by simp
  qed
  thus "((\<lambda>s. \<integral>x. f s x \<partial>M) has_real_derivative
    \<integral>x. borel_measurable_extension M (\<lambda>y. deriv (\<lambda>s. f s y) r) x \<partial>M) (at r)"
    by (rewrite DERIV_def, rewrite tendsto_at_iff_sequentially) simp
qed

proposition interchange_deriv_LINT:
  fixes a b :: real and f :: "real \<Rightarrow> 'a \<Rightarrow> real" and g :: "'a \<Rightarrow> real"
  assumes "\<And>r. r\<in>{a<..<b} \<Longrightarrow> integrable M (f r)" and
    "AE x in M. (\<lambda>r. f r x) differentiable_on {a<..<b}" and
    "\<And>r. r\<in>{a<..<b} \<Longrightarrow> (\<lambda>x. (deriv (\<lambda>r. f r x) r)) \<in> borel_measurable M" and
    "AE x in M. \<forall>r\<in>{a<..<b}. \<bar>deriv (\<lambda>r. f r x) r\<bar> \<le> g x" "integrable M g"
  shows "\<And>r. r\<in>{a<..<b} \<Longrightarrow> ((\<lambda>r. \<integral>x. f r x \<partial>M) has_real_derivative
    \<integral>x. deriv (\<lambda>r. f r x) r \<partial>M) (at r)"
proof -
  fix r assume r_ab: "r\<in>{a<..<b}"
  hence Df_msr[measurable]: "(\<lambda>x. deriv (\<lambda>s. f s x) r) \<in> borel_measurable M"
    using assms by simp
  have "((\<lambda>s. \<integral>x. f s x \<partial>M) has_real_derivative
    (\<integral>x. borel_measurable_extension M (\<lambda>y. deriv (\<lambda>s. f s y) r) x \<partial>M)) (at r)"
    using assms r_ab by (intro interchange_deriv_LINT_general; simp)
  moreover have "(\<integral>x. deriv (\<lambda>s. f s x) r \<partial>M) =
     (\<integral>x. borel_measurable_extension M (\<lambda>y. deriv (\<lambda>s. f s y) r) x \<partial>M)"
    by(auto intro!: integral_cong_AE)
  ultimately show "((\<lambda>r. \<integral>x. f r x \<partial>M) has_real_derivative \<integral>x. deriv (\<lambda>r. f r x) r \<partial>M) (at r)"
    by simp
qed

proposition interchange_deriv_LINT_set_general:
  fixes a b :: real and f :: "real \<Rightarrow> 'a \<Rightarrow> real" and g :: "'a \<Rightarrow> real" and A :: "'a set"
  assumes A_msr: "A \<in> sets M" and
    f_integ: "\<And>r. r\<in>{a<..<b} \<Longrightarrow> set_integrable M A (f r)" and
    f_diff: "AE x\<in>A in M. (\<lambda>r. f r x) differentiable_on {a<..<b}" and
    Df_bound: "AE x\<in>A in M. \<forall>r\<in>{a<..<b}. \<bar>deriv (\<lambda>r. f r x) r\<bar> \<le> g x" "set_integrable M A g"
  shows "\<And>r. r\<in>{a<..<b} \<Longrightarrow> ((\<lambda>r. \<integral>x\<in>A. f r x \<partial>M) has_real_derivative
    (\<integral>x\<in>A. set_borel_measurable_extension M A (\<lambda>x. deriv (\<lambda>r. f r x) r) x \<partial>M)) (at r)"
proof -
  let ?M_A = "restrict_space M A"
  have "\<And>r. r\<in>{a<..<b} \<Longrightarrow> integrable ?M_A (f r)"
    using A_msr f_integ set_integrable_restrict_space_iff by auto
  moreover have "AE x in ?M_A. (\<lambda>r. f r x) differentiable_on {a<..<b}"
    using AE_restrict_space_iff A_msr f_diff by (metis sets.Int_space_eq2)
  moreover have "AE x in ?M_A. \<forall>r\<in>{a<..<b}. \<bar>deriv (\<lambda>r. f r x) r\<bar> \<le> g x" and
    "integrable ?M_A g"
    using A_msr Df_bound set_integrable_restrict_space_iff
    by (auto simp add: AE_restrict_space_iff)
  ultimately have "\<And>r. r\<in>{a<..<b} \<Longrightarrow> ((\<lambda>r. integral\<^sup>L ?M_A (f r)) has_real_derivative
    integral\<^sup>L ?M_A (borel_measurable_extension ?M_A (\<lambda>x. deriv (\<lambda>r. f r x) r))) (at r)"
    by (rule interchange_deriv_LINT_general[where M="restrict_space M A"]) auto
  thus "\<And>r. r\<in>{a<..<b} \<Longrightarrow> ((\<lambda>r. \<integral>x\<in>A. f r x \<partial>M) has_real_derivative
    (\<integral>x\<in>A. set_borel_measurable_extension M A (\<lambda>x. deriv (\<lambda>r. f r x) r) x \<partial>M)) (at r)"
    unfolding set_borel_measurable_extension_def using assms
    by(simp add: set_lebesgue_integral_restrict_space)
qed

proposition interchange_deriv_LINT_set:
  fixes a b :: real and f :: "real \<Rightarrow> 'a \<Rightarrow> real" and g :: "'a \<Rightarrow> real" and A :: "'a set"
  assumes [measurable]:"A \<in> sets M" and
    "\<And>r. r\<in>{a<..<b} \<Longrightarrow> set_integrable M A (f r)" and
    "AE x\<in>A in M. (\<lambda>r. f r x) differentiable_on {a<..<b}" and
    "\<And>r. r\<in>{a<..<b} \<Longrightarrow> set_borel_measurable M A (\<lambda>x. (deriv (\<lambda>r. f r x) r))" and
    "AE x\<in>A in M. \<forall>r\<in>{a<..<b}. \<bar>deriv (\<lambda>r. f r x) r\<bar> \<le> g x" "set_integrable M A g"
  shows "\<And>r. r\<in>{a<..<b} \<Longrightarrow> ((\<lambda>r. \<integral>x\<in>A. f r x \<partial>M) has_real_derivative
    (\<integral>x\<in>A. deriv (\<lambda>r. f r x) r \<partial>M)) (at r)"
proof -
  fix r assume r_ab: "r\<in>{a<..<b}"
  hence [simp]: "set_borel_measurable M A (\<lambda>x. deriv (\<lambda>s. f s x) r)"
    using assms by simp
  have [measurable]: "\<And>h N L. h \<in> N \<rightarrow>\<^sub>M L \<Longrightarrow> measurable_extension N L h \<in> N \<rightarrow>\<^sub>M L"
    by(rule measurable_extension_measurable) auto
  have "((\<lambda>s. \<integral>x\<in>A. f s x \<partial>M) has_real_derivative
    (\<integral>x\<in>A. set_borel_measurable_extension M A (\<lambda>y. deriv (\<lambda>s. f s y) r) x \<partial>M)) (at r)"
    using assms r_ab by (intro interchange_deriv_LINT_set_general; simp)
  moreover have "(\<integral>x\<in>A. deriv (\<lambda>s. f s x) r \<partial>M) = 
     (\<integral>x\<in>A. set_borel_measurable_extension M A (\<lambda>y. deriv (\<lambda>s. f s y) r) x \<partial>M)"
    by(auto intro!: set_lebesgue_integral_cong_AE2 set_borel_measurable_measurable_extension_AE
        set_borel_measurable_extension_measurable[where g="\<lambda>y. deriv (\<lambda>s. f s y) r"])
  ultimately show
    "((\<lambda>r. \<integral>x\<in>A. f r x \<partial>M) has_real_derivative (\<integral>x\<in>A. deriv (\<lambda>r. f r x) r \<partial>M)) (at r)"
    by simp
qed

section \<open>Additional Lemmas for the \<open>HOL-Probability\<close> Library\<close>

lemma (in finite_borel_measure)
  fixes F :: "real \<Rightarrow> real"
  assumes nondecF : "\<And> x y. x \<le> y \<Longrightarrow> F x \<le> F y" and
    right_cont_F : "\<And>a. continuous (at_right a) F" and
    lim_F_at_bot : "(F \<longlongrightarrow> 0) at_bot" and
    lim_F_at_top : "(F \<longlongrightarrow> m) at_top" and
    m : "0 \<le> m"
  shows emeasure_interval_measure_Ioi: "emeasure (interval_measure F) {x<..} = m - F x"
    and measure_interval_measure_Ioi: "measure (interval_measure F) {x<..} = m - F x"
proof -
  interpret F_FM: finite_measure "interval_measure F"
    using finite_borel_measure.axioms(1) finite_borel_measure_interval_measure lim_F_at_bot
      lim_F_at_top m nondecF right_cont_F by blast
  have "UNIV = {..x} \<union> {x<..}" by auto
  moreover have "{..x} \<inter> {x<..} = {}" by auto
  ultimately have "emeasure (interval_measure F) UNIV =
    emeasure (interval_measure F) {..x} + emeasure (interval_measure F) {x<..}"
    by (simp add: plus_emeasure)
  moreover have "emeasure (interval_measure F) UNIV = m"
    using assms interval_measure_UNIV by presburger
  ultimately show \<star>: "emeasure (interval_measure F) {x<..} = m - F x"
    using assms emeasure_interval_measure_Iic
    by (metis ennreal_add_diff_cancel_left ennreal_minus measure_interval_measure_Iic
        measure_nonneg top_neq_ennreal)
  hence "ennreal (measure (interval_measure F) {x<..}) = m - F x"
    using emeasure_eq_measure by (metis emeasure_eq_ennreal_measure top_neq_ennreal)
  moreover have "\<And>x. F x \<le> m"
    using lim_F_at_top nondecF by (intro mono_at_top_le[where f=F]; simp add: mono_def)
  ultimately show "measure (interval_measure F) {x<..} = m - F x"
    using ennreal_inj F_FM.emeasure_eq_measure by force
qed

lemma (in prob_space) cond_prob_nonneg[simp]: "cond_prob M P Q \<ge> 0"
  by (auto simp: cond_prob_def)

lemma (in prob_space) cond_prob_whole_1: "cond_prob M P P = 1" if "prob {\<omega> \<in> space M. P \<omega>} \<noteq> 0"
  unfolding cond_prob_def using that by simp

lemma (in prob_space) cond_prob_0_null: "cond_prob M P Q = 0" if "prob {\<omega> \<in> space M. Q \<omega>} = 0"
  unfolding cond_prob_def using that by simp

lemma (in prob_space) cond_prob_AE_prob:
  assumes "{\<omega> \<in> space M. P \<omega>} \<in> events" "{\<omega> \<in> space M. Q \<omega>} \<in> events"
    and "AE \<omega> in M. Q \<omega>"
  shows "cond_prob M P Q = prob {\<omega> \<in> space M. P \<omega>}"
proof -
  let ?setP = "{\<omega> \<in> space M. P \<omega>}"
  let ?setQ = "{\<omega> \<in> space M. Q \<omega>}"
  have [simp]: "prob ?setQ = 1" using assms prob_Collect_eq_1 by simp
  hence "cond_prob M P Q = prob (?setP \<inter> ?setQ)"
    unfolding cond_prob_def by (simp add: Collect_conj_eq2)
  also have "\<dots> = prob ?setP"
  proof (rule antisym)
    show "prob (?setP \<inter> ?setQ) \<le> prob ?setP"
      using assms finite_measure_mono inf_sup_ord(1) by blast
  next
    show "prob ?setP \<le> prob (?setP \<inter> ?setQ)"
    proof -
      have "prob (?setP \<inter> ?setQ) = prob ?setP + prob ?setQ - prob (?setP \<union> ?setQ)"
        using assms by (smt (verit) finite_measure_Diff' finite_measure_Union' sup_commute)
      also have "\<dots> = prob ?setP + (1 - prob (?setP \<union> ?setQ))" by simp
      also have "\<dots> \<ge> prob ?setP" by simp
      finally show ?thesis .
    qed
  qed
  finally show ?thesis .
qed

subsection \<open>More Properties of \<open>cdf\<close>'s\<close>

context finite_borel_measure
begin

lemma cdf_diff_eq2:
  assumes "x \<le> y"
  shows "cdf M y - cdf M x = measure M {x<..y}"
proof (cases \<open>x = y\<close>)
  case True
  thus ?thesis by force
next 
  case False
  hence "x < y" using assms by simp
  thus ?thesis by (rule cdf_diff_eq)
qed

end

context prob_space
begin

lemma cdf_distr_measurable [measurable]:
  assumes [measurable]: "random_variable borel X"
  shows "cdf (distr M borel X) \<in> borel_measurable borel"
  by(auto intro!: cdf_distribution.measurable_C simp: cdf_distribution_def)

lemma cdf_distr_P:
  assumes [measurable]:"random_variable borel X"
  shows "cdf (distr M borel X) x = \<P>(\<omega> in M. X \<omega> \<le> x)"
  by(auto simp: measure_distr cdf_def intro!: arg_cong[where f=prob])

lemma cdf_continuous_distr_P_lt:
  assumes [measurable]:"random_variable borel X" "isCont (cdf (distr M borel X)) x"
  shows "cdf (distr M borel X) x = \<P>(\<omega> in M. X \<omega> < x)"
proof -
  have "\<P>(\<omega> in M. X \<omega> < x) = measure (distr M borel X) {..<x}"
    by (auto simp: measure_distr intro!: arg_cong[where f=prob])
  also have "\<dots> = measure (distr M borel X) ({..<x} \<union> {x})"
    by(rule finite_measure.measure_zero_union[symmetric])
      (use assms in
       "auto intro!: finite_measure_distr finite_borel_measure.isCont_cdf[THEN iffD1]
                     real_distribution.finite_borel_measure_M")
  also have "\<dots> = measure (distr M borel X) {..x}" by (metis ivl_disj_un_singleton(2))
  also have "\<dots> = cdf (distr M borel X) x" unfolding cdf_def by simp
  finally show ?thesis by simp
qed

lemma cdf_distr_diff_P:
  assumes "x \<le> y"
    and [measurable]:"random_variable borel X"
  shows "cdf (distr M borel X) y - cdf (distr M borel X) x = \<P>(\<omega> in M. x < X \<omega> \<and> X \<omega> \<le> y)"
proof -
  interpret distrX_FBM: finite_borel_measure "distr M borel X"
    using real_distribution.finite_borel_measure_M real_distribution_distr assms by simp
  have "cdf (distr M borel X) y - cdf (distr M borel X) x = measure (distr M borel X) {x<..y}"
    by (rewrite distrX_FBM.cdf_diff_eq2; simp add: assms)
  also have "\<dots> = \<P>(\<omega> in M. x < X \<omega> \<and> X \<omega> \<le> y)"
    by(auto simp: measure_distr intro!: arg_cong[where f=prob])
  finally show ?thesis .
qed

lemma cdf_distr_max:
  fixes c::real
  assumes [measurable]: "random_variable borel X"
  shows "cdf (distr M borel (\<lambda>x. max (X x) c)) u = cdf (distr M borel X) u * indicator {c..} u"
proof (cases \<open>c \<le> u\<close>)
  case True
  thus ?thesis
    by(auto simp: measure_distr cdf_def intro!: arg_cong[where f=prob])
next
  case h:False
  hence "(\<lambda>x. max (X x) c) -` {..u} \<inter> space M = {}"
    by fastforce
  thus ?thesis
    using h by(auto simp: measure_distr cdf_def)
qed

lemma cdf_distr_min:
  fixes c::real
  assumes [measurable]: "random_variable borel X"
  shows "cdf (distr M borel (\<lambda>x. min (X x) c)) u =
    1 - (1 - cdf (distr M borel X) u) * indicator {..<c} u"
proof (cases \<open>c \<le> u\<close>)
  case h:True
  hence *:"(\<lambda>x. min (X x) c) -` {..u} \<inter> space M = space M"
    by fastforce
  thus ?thesis
    using h by(simp add: cdf_def measure_distr prob_space)
next
  case h:False
  then have "(\<lambda>x. min (X x) c) -` {..u} \<inter> space M = X -` {..u} \<inter> space M"
    by fastforce
  thus ?thesis
    using h by(simp add: cdf_def measure_distr)
qed

lemma cdf_distr_floor_P:
  fixes X :: "'a \<Rightarrow> real"
  assumes [measurable]: "random_variable borel X"
  shows "cdf (distr M borel (\<lambda>x. \<lfloor>X x\<rfloor>)) u = \<P>(x in M. X x < \<lfloor>u\<rfloor> + 1)"
  using floor_le_iff le_floor_iff
  by(auto simp: cdf_def measure_distr vimage_def intro!: arg_cong[where f=prob])

lemma expectation_nonneg_tail:
  assumes [measurable]: "random_variable borel X"
    and X_nonneg: "\<And>x. x \<in> space M \<Longrightarrow> X x \<ge> 0"
  defines "F u \<equiv> cdf (distr M borel X) u"
  shows "(\<integral>\<^sup>+x. ennreal (X x) \<partial>M) = (\<integral>\<^sup>+u\<in>{0..}. ennreal (1 - F u) \<partial>lborel)"
proof -
  let ?distrX = "distr M borel X"
  have "(\<integral>\<^sup>+x. ennreal (X x) \<partial>M) = (\<integral>\<^sup>+u. ennreal u \<partial>?distrX)"
    by (simp add: nn_integral_distr)
  also have "\<dots> = (\<integral>\<^sup>+u\<in>{0..}. ennreal u \<partial>?distrX)"
    by (rule nn_integral_distr_set; simp add: X_nonneg)
  also have "\<dots> = (\<integral>\<^sup>+u\<in>{0..}. (\<integral>\<^sup>+v\<in>{0..}. indicator {..<u} v \<partial>lborel) \<partial>?distrX)"
  proof -
    have "\<And>u::real. u\<in>{0..} \<Longrightarrow> ennreal u = (\<integral>\<^sup>+v\<in>{0..}. indicator {..<u} v \<partial>lborel)"
      by(auto simp: indicator_inter_arith[symmetric] inf.commute)
    thus ?thesis by (metis (no_types, lifting) indicator_eq_0_iff mult_eq_0_iff)
  qed
  also have "\<dots> = (\<integral>\<^sup>+v\<in>{0..}. (\<integral>\<^sup>+u\<in>{0..}. indicator {..<u} v \<partial>?distrX) \<partial>lborel)"
  proof -
    have "(\<integral>\<^sup>+u\<in>{0..}. (\<integral>\<^sup>+v\<in>{0..}. indicator {..<u} v \<partial>lborel) \<partial>?distrX) =
      \<integral>\<^sup>+u. (\<integral>\<^sup>+v. indicator {..<u} v * indicator {0..} v * indicator {0..} u \<partial>lborel) \<partial>?distrX"
      by (rewrite nn_integral_multc; simp)
    also have "\<dots> =
      \<integral>\<^sup>+v. (\<integral>\<^sup>+u. indicator {..<u} v * indicator {0..} v * indicator {0..} u \<partial>?distrX) \<partial>lborel"
    proof -
      have [measurable]: "Measurable.pred (borel \<Otimes>\<^sub>M borel) (\<lambda>x:: real \<times> real. fst x \<in> {..<snd x})"
        by auto
      show ?thesis
        by(auto intro!: pair_sigma_finite.Fubini' pair_sigma_finite.intro
          simp: lborel.sigma_finite_measure_axioms prob_space_imp_sigma_finite[OF prob_space_distr])
    qed
    also have "\<dots> = (\<integral>\<^sup>+v\<in>{0..}. (\<integral>\<^sup>+u\<in>{0..}. indicator {..<u} v \<partial>?distrX) \<partial>lborel)"
    proof -
      have [measurable]:"\<And>x::real. Measurable.pred borel (\<lambda>y. x \<in> {..<y})"
        by simp
      have "\<And>x y. (indicator {..<y} x :: ennreal) * indicator {0..} x * indicator {0..} y
                    = indicator {..<y} x * indicator {0..} y * indicator {0..} x"
        by(auto simp: indicator_def)
      thus ?thesis
        by(subst nn_integral_multc[symmetric]) (auto intro!: nn_integral_cong simp: nn_integral_distr)
    qed
    finally show ?thesis by simp
  qed
  also have "\<dots> = (\<integral>\<^sup>+v\<in>{0..}. (\<integral>\<^sup>+u. indicator {v<..} u \<partial>?distrX) \<partial>lborel)"
  proof -
    have [measurable]:"\<And>x::real. Measurable.pred borel (\<lambda>y. x \<in> {..<y})"
      by simp
    have "\<And>x y::real. indicator {..<y} x * indicator {0..} y * indicator {0..} x
                 = indicator {x<..} y * (indicator {0..} x :: ennreal)"
      by(auto simp: indicator_def)
    thus ?thesis
      by(auto intro!: nn_integral_cong simp del: nn_integral_indicator simp: nn_integral_multc[symmetric])
  qed
  also have "\<dots> = (\<integral>\<^sup>+v\<in>{0..}. ennreal (1 - F v) \<partial>lborel)"
  proof -
    have "space M - X -` {..x} \<inter> space M = X -` {x<..} \<inter> space M" for x
      by auto
    thus ?thesis
      by(auto intro!: nn_integral_cong simp: emeasure_distr F_def cdf_def
          measure_distr prob_compl[symmetric] emeasure_eq_measure[symmetric])
  qed
  finally show ?thesis .
qed

lemma expectation_nonpos_tail:
  assumes [measurable]: "random_variable borel X"
    and X_nonpos: "\<And>x. x \<in> space M \<Longrightarrow> X x \<le> 0"
  defines "F u \<equiv> cdf (distr M borel X) u"
  shows "(\<integral>\<^sup>+x. ennreal (- X x) \<partial>M) = (\<integral>\<^sup>+u\<in>{..0}. ennreal (F u) \<partial>lborel)"
proof -
  let ?distrX = "distr M borel X"
  have "(\<integral>\<^sup>+x. ennreal (- X x) \<partial>M) = (\<integral>\<^sup>+u. ennreal (-u) \<partial>?distrX)"
    by (rewrite nn_integral_distr; simp)
  also have "\<dots> = (\<integral>\<^sup>+u\<in>{..0}. ennreal (-u) \<partial>?distrX)"
  proof -
    have [simp]: "{..0::real} \<union> {0<..} = UNIV" by force
    have "(\<integral>\<^sup>+u. ennreal (-u) \<partial>?distrX) =
      (\<integral>\<^sup>+u\<in>{..0}. ennreal (-u) \<partial>?distrX) + (\<integral>\<^sup>+u\<in>{0<..}. ennreal (-u) \<partial>?distrX)"
      by (rewrite nn_integral_disjoint_pair[symmetric]) auto
    also have "\<dots> = (\<integral>\<^sup>+u\<in>{..0}. ennreal (-u) \<partial>?distrX)"
      apply (rewrite nn_integral_zero'[of "\<lambda>u. ennreal (-u) * indicator {0<..} u"])
      unfolding indicator_def using always_eventually ennreal_lt_0 by fastforce+
    finally show ?thesis .
  qed
  also have "\<dots> = (\<integral>\<^sup>+u\<in>{..0}. (\<integral>\<^sup>+v\<in>{..0}. indicator {u..} v \<partial>lborel) \<partial>?distrX)"
  proof -
    have "\<And>u::real. u\<in>{..0} \<Longrightarrow> ennreal (-u) = (\<integral>\<^sup>+v\<in>{..0}. indicator {u..} v \<partial>lborel)"
      by (rewrite indicator_inter_arith[THEN sym]) simp
    thus ?thesis by (metis (no_types, lifting) indicator_eq_0_iff mult_eq_0_iff)
  qed
  also have "\<dots> = (\<integral>\<^sup>+v\<in>{..0}. (\<integral>\<^sup>+u\<in>{..0}. indicator {u..} v \<partial>?distrX) \<partial>lborel)"
  proof -
    have "(\<integral>\<^sup>+u\<in>{..0}. (\<integral>\<^sup>+v\<in>{..0}. indicator {u..} v \<partial>lborel) \<partial>?distrX) =
      \<integral>\<^sup>+u. (\<integral>\<^sup>+v. indicator {u..} v * indicator {..0} v * indicator {..0} u \<partial>lborel) \<partial>?distrX"
      by (rewrite nn_integral_multc; simp)
    also have "\<dots> =
      \<integral>\<^sup>+v. (\<integral>\<^sup>+u. indicator {u..} v * indicator {..0} v * indicator {..0} u \<partial>?distrX) \<partial>lborel"
      apply (rewrite pair_sigma_finite.Fubini')
      using pair_sigma_finite.intro assms
        prob_space_distr prob_space_imp_sigma_finite sigma_finite_lborel
       apply blast
      by measurable auto (* TODO: fix this proof *)
    also have "\<dots> = (\<integral>\<^sup>+v\<in>{..0}. (\<integral>\<^sup>+u\<in>{..0}. indicator {u..} v \<partial>?distrX) \<partial>lborel)"
      apply (rewrite nn_integral_multc[THEN sym]; measurable; simp?)
      apply (rule nn_integral_cong)+ 
      using mult.assoc mult.commute by metis  (* TODO: fix this proof *)
    finally show ?thesis by simp
  qed
  also have "\<dots> = (\<integral>\<^sup>+v\<in>{..0}. (\<integral>\<^sup>+u. indicator {..v} u \<partial>?distrX) \<partial>lborel)"
    apply (rule nn_integral_cong)
    apply (rewrite nn_integral_multc[THEN sym], measurable; (simp del: nn_integral_indicator)?)+
    apply (rule nn_integral_cong)
    using atMost_iff atLeast_iff indicator_simps by (smt (verit, del_insts) mult_1 mult_eq_0_iff)
     (* TODO: fix this proof *)
  also have "\<dots> = (\<integral>\<^sup>+v\<in>{..0}. ennreal (F v) \<partial>lborel)"
    apply (rule nn_integral_cong, simp)
    apply (rewrite emeasure_distr; simp?)
    unfolding F_def cdf_def
    by (rewrite measure_distr; simp add: emeasure_eq_measure)
     (* TODO: fix this proof *)
  finally show ?thesis .
qed

proposition expectation_tail:
  assumes [measurable]: "integrable M X"
  defines "F u \<equiv> cdf (distr M borel X) u"
  shows "expectation X = (LBINT u:{0..}. 1 - F u) - (LBINT u:{..0}. F u)"
proof -
  have "expectation X = expectation (\<lambda>x. max (X x) 0) + expectation (\<lambda>x. min (X x) 0)"
    using integrable_max integrable_min
    apply (rewrite Bochner_Integration.integral_add[THEN sym], measurable)
    by (rule Bochner_Integration.integral_cong; simp)
     (* TODO: fix this proof *)
  also have "\<dots> = expectation (\<lambda>x. max (X x) 0) - expectation (\<lambda>x. - min (X x) 0)" by force
  also have "\<dots> = (LBINT u:{0..}. 1 - F u) - (LBINT u:{..0}. F u)"
  proof -
    have "expectation (\<lambda>x. max (X x) 0) = (LBINT u:{0..}. 1 - F u)"
    proof -
      have "expectation (\<lambda>x. max (X x) 0) = enn2real (\<integral>\<^sup>+x. ennreal (max (X x) 0) \<partial>M)"
        by (rule integral_eq_nn_integral; simp)
      also have "\<dots> = enn2real (\<integral>\<^sup>+u\<in>{0..}. ennreal (1 - F u) \<partial>lborel)"
        apply (rewrite expectation_nonneg_tail)
          apply simp
         apply simp
        apply (rewrite cdf_distr_max)
         apply simp
        unfolding F_def
        apply (metis (opaque_lifting) indicator_simps mult.commute mult_1 mult_eq_0_iff)
        done
      also have "\<dots> = enn2real (\<integral>\<^sup>+u. ennreal ((1 - F u) * indicator {0..} u) \<partial>lborel)"
        by (simp add: indicator_mult_ennreal mult.commute)
      also have "\<dots> = (LBINT u:{0..}. 1 - F u)"
        apply (rewrite integral_eq_nn_integral[THEN sym])
          apply(simp add: F_def)
        unfolding F_def using real_distribution.cdf_bounded_prob
         apply force
        unfolding set_lebesgue_integral_def
        apply (rule Bochner_Integration.integral_cong)
         apply simp_all
        done
      finally show ?thesis .
    qed
    moreover have "expectation (\<lambda>x. - min (X x) 0) = (LBINT u:{..0}. F u)"
    proof -
      have "expectation (\<lambda>x. - min (X x) 0) = enn2real (\<integral>\<^sup>+x. ennreal (- min (X x) 0) \<partial>M)"
        by (rule integral_eq_nn_integral; simp)
      also have "\<dots> = enn2real (\<integral>\<^sup>+u\<in>{..0}. ennreal (F u) \<partial>lborel)"
      proof -
        let ?distrminX = "distr M borel (\<lambda>x. min (X x) 0)"
        have [simp]: "sym_diff {..0} {..<0} = {0::real}" by force
        have "enn2real (\<integral>\<^sup>+x. ennreal (- min (X x) 0) \<partial>M) =
      enn2real (\<integral>\<^sup>+u\<in>{..0}. ennreal (cdf ?distrminX u) \<partial>lborel)"
          by (rewrite expectation_nonpos_tail; simp)
        also have "\<dots> = enn2real (\<integral>\<^sup>+u\<in>{..<0}. ennreal (cdf ?distrminX u) \<partial>lborel)"
          by (rewrite nn_integral_null_delta, auto)
        also have "\<dots> = enn2real (\<integral>\<^sup>+u\<in>{..<0}. ennreal (F u) \<partial>lborel)"
          apply (rewrite cdf_distr_min)
           apply simp
          apply (intro arg_cong[where f=enn2real] nn_integral_cong)
          unfolding F_def by (smt (verit) indicator_simps mult_cancel_left1 mult_eq_0_iff)
        also have "\<dots> = enn2real (\<integral>\<^sup>+u\<in>{..0}. ennreal (F u) \<partial>lborel)"
          by (rewrite nn_integral_null_delta, auto simp add: sup_commute)
        finally show ?thesis .
      qed
      also have "\<dots> = enn2real (\<integral>\<^sup>+u. ennreal (F u * indicator {..0} u) \<partial>lborel)"
        using mult.commute indicator_mult_ennreal by metis
      also have "\<dots> = (LBINT u:{..0}. F u)"
        apply (rewrite integral_eq_nn_integral[THEN sym])
          apply(simp add: F_def)
        unfolding F_def
        using finite_borel_measure.cdf_nonneg real_distribution.finite_borel_measure_M
         apply simp
        unfolding set_lebesgue_integral_def
        apply (rule Bochner_Integration.integral_cong)
         apply simp_all
        done
      finally show ?thesis .
    qed
    ultimately show ?thesis by simp
  qed
  finally show ?thesis .
qed

proposition distributed_deriv_cdf:
  assumes [measurable]: "random_variable borel X"
  defines "F u \<equiv> cdf (distr M borel X) u"
  assumes "finite S" "\<And>x. x \<notin> S \<Longrightarrow> (F has_real_derivative f x) (at x)"
    and "continuous_on UNIV F" "f \<in> borel_measurable lborel"
  shows "distributed M lborel X f"
proof -
  have FBM: "finite_borel_measure (distr M borel X)"
    using real_distribution.finite_borel_measure_M real_distribution_distr assms by simp
  then interpret distrX_FBM: finite_borel_measure "distr M borel X" .
  have FBMl: "finite_borel_measure (distr M lborel X)" using FBM distr_borel_lborel by metis
  then interpret distrlX_FBM: finite_borel_measure "distr M lborel X" .
  have [simp]: "(\<lambda>x. ennreal (f x)) \<in> borel_measurable borel" using assms by simp
  moreover have "distr M lborel X = density lborel f"
  proof -
    have "\<And>a b. a \<le> b \<Longrightarrow> emeasure (distr M lborel X) {a<..b} < \<top>"
      using distrlX_FBM.emeasure_real less_top_ennreal by blast
    moreover have "\<And>a b. a \<le> b \<Longrightarrow>
      emeasure (distr M lborel X) {a<..b} = emeasure (density lborel f) {a<..b}"
    proof -
      fix a b :: real assume "a \<le> b"
      hence [simp]: "sym_diff {a<..b} {a..b} = {a}" by force
      have "emeasure (density lborel f) {a<..b} = (\<integral>\<^sup>+x\<in>{a<..b}. ennreal (f x) \<partial>lborel)"
        by (rewrite emeasure_density; simp)
      also have "\<dots> = (\<integral>\<^sup>+x\<in>{a..b}. ennreal (f x) \<partial>lborel)"
        by (rewrite nn_integral_null_delta, auto)
      also have "\<dots> = \<integral>\<^sup>+x. ennreal (indicat_real {a..b} x * f x) \<partial>lborel"
        by (metis indicator_mult_ennreal mult.commute)
      also have "\<dots> = ennreal (F b - F a)"
      proof -
        define g where "g x = (if x \<in> S then 0 else f x)" for x :: real
        have [simp]: "\<And>x. g x \<ge> 0"
          unfolding g_def
          apply (split if_split, auto)
          apply (rule mono_on_imp_deriv_nonneg[of UNIV F], auto)
          unfolding F_def mono_on_def using distrX_FBM.cdf_nondecreasing apply blast
          using assms unfolding F_def by force
          (* TODO: fix this proof *)
        have "(\<integral>\<^sup>+x. ennreal (indicat_real {a..b} x * f x) \<partial>lborel)
          = \<integral>\<^sup>+x. ennreal (indicat_real {a..b} x * g x) \<partial>lborel"
          apply (rule nn_integral_cong_AE)
          apply (rule AE_mp[where P= "\<lambda>x. x \<notin> S"])
          using assms finite_imp_null_set_lborel AE_not_in
           apply blast
          unfolding g_def
          apply simp
          done
        also have "\<dots> = ennreal (F b - F a)"
          apply (rewrite nn_integral_has_integral_lebesgue, simp)
           apply (rule fundamental_theorem_of_calculus_strong[of S], auto simp: \<open>a \<le> b\<close> g_def assms)
          using has_real_derivative_iff_has_vector_derivative assms apply presburger
          using assms continuous_on_subset subsetI by fastforce
          (* TODO: fix this proof *)
        finally show ?thesis .
      qed
      also have "\<dots> = emeasure (distr M lborel X) {a <.. b}"
        using \<open>a \<le> b\<close>
        by (rewrite distrlX_FBM.emeasure_Ioc)
           (auto simp: F_def cdf_def ennreal_minus[symmetric] distr_borel_lborel)
      finally show "emeasure (distr M lborel X) {a<..b} = emeasure (density lborel f) {a<..b}"
        by simp
    qed
    ultimately show ?thesis by (intro measure_eqI_Ioc; simp)
  qed
  ultimately show ?thesis unfolding distributed_def by auto
qed

end

text \<open>
  Define the conditional probability space.
  This is obtained by rescaling the restricted space of a probability space.
\<close>

subsection \<open>Conditional Probability Space\<close>

lemma restrict_prob_space:
  assumes "measure_space \<Omega> A \<mu>" "a \<in> A"
    and "0 < \<mu> a" "\<mu> a < \<infinity>"
  shows "prob_space (scale_measure (1 / \<mu> a) (restrict_space (measure_of \<Omega> A \<mu>) a))"
proof
  let ?M = "measure_of \<Omega> A \<mu>"
  let ?Ma = "restrict_space ?M a"
  let ?rMa = "scale_measure (1 / \<mu> a) ?Ma"
  have "emeasure ?rMa (space ?rMa) = 1 / \<mu> a * emeasure ?Ma (space ?rMa)" by simp
  also have "\<dots> = 1 / \<mu> a * emeasure ?M (space ?rMa)"
    using assms
    apply (rewrite emeasure_restrict_space)
    apply (simp add: measure_space_def sigma_algebra.sets_measure_of_eq)
    by (simp add: space_restrict_space space_scale_measure) simp
    (* TODO: fix this proof *)
  also have "\<dots> = 1 / \<mu> a * emeasure ?M (space ?Ma)" by (rewrite space_scale_measure) simp
  also have "\<dots> = 1 / \<mu> a * emeasure ?M a"
    using assms
    by (rewrite space_restrict_space2) (auto simp add: measure_space_closed)
  also have "\<dots> = 1"
    using assms measure_space_def
    by (rewrite emeasure_measure_of_sigma) (auto simp add: ennreal_divide_times)
  finally show "emeasure ?rMa (space ?rMa) = 1" .
qed

definition cond_prob_space :: "'a measure \<Rightarrow> 'a set \<Rightarrow> 'a measure" (infix \<open>\<downharpoonright>\<close> 200)
  where "M\<downharpoonright>A \<equiv> scale_measure (1 / emeasure M A) (restrict_space M A)"

context prob_space
begin

lemma cond_prob_space_whole[simp]: "M \<downharpoonright> space M = M"
  unfolding cond_prob_space_def using emeasure_space_1 by simp

lemma cond_prob_space_correct:
  assumes "A \<in> events" "prob A > 0"
  shows "prob_space (M\<downharpoonright>A)"
  using restrict_prob_space[OF measure_space[of M]] assms
  by(auto simp: cond_prob_space_def emeasure_eq_measure measure_of_of_measure)

lemma space_cond_prob_space:
  assumes "A \<in> events"
  shows "space (M\<downharpoonright>A) = A"
  unfolding cond_prob_space_def using assms by (simp add: space_scale_measure)

lemma sets_cond_prob_space: "sets (M\<downharpoonright>A) = (\<inter>) A ` events"
  unfolding cond_prob_space_def by (metis sets_restrict_space sets_scale_measure)

lemma measure_cond_prob_space:
  assumes "A \<in> events" "B \<in> events"
    and "prob A > 0"
  shows "measure (M\<downharpoonright>A) (B \<inter> A) = prob (B \<inter> A) / prob A"
proof -
  have "1 / emeasure M A = ennreal (1 / prob A)"
    using assms by (smt (verit) divide_ennreal emeasure_eq_measure ennreal_1)
  hence "measure (M\<downharpoonright>A) (B \<inter> A) = (1 / prob A) * measure (restrict_space M A) (B \<inter> A)"
    unfolding cond_prob_space_def using measure_scale_measure by force
  also have "\<dots> = (1 / prob A) * prob (B \<inter> A)"
    using measure_restrict_space assms by (metis inf.cobounded2 sets.Int_space_eq2)
  also have "\<dots> = prob (B \<inter> A) / prob A" by simp
  finally show ?thesis .
qed

corollary measure_cond_prob_space_subset:
  assumes "A \<in> events" "B \<in> events" "B \<subseteq> A"
    and "prob A > 0"
  shows "measure (M\<downharpoonright>A) B = prob B / prob A"
proof -
  have "B = B \<inter> A" using assms by auto
  moreover have "measure (M\<downharpoonright>A) (B \<inter> A) = prob (B \<inter> A) / prob A"
    using assms measure_cond_prob_space by simp
  ultimately show ?thesis by auto
qed

lemma cond_cond_prob_space:
  assumes [measurable]:"A \<in> events" "B \<in> events" "B \<subseteq> A" "prob B > 0"
  shows "(M\<downharpoonright>A)\<downharpoonright>B = M\<downharpoonright>B"
proof (rule measure_eqI)
  have pA_pos[simp]: "prob A > 0" using assms by (smt (verit, ccfv_SIG) finite_measure_mono)
  interpret MA_PS: prob_space "M\<downharpoonright>A" using cond_prob_space_correct assms by simp
  interpret MB_PS: prob_space "M\<downharpoonright>B" using cond_prob_space_correct assms by simp
  have "1 / emeasure M A = ennreal (1 / prob A)"
    using pA_pos by (smt (verit, ccfv_SIG) divide_ennreal emeasure_eq_measure ennreal_1)
  hence [simp]: "0 < MA_PS.prob B"
    using assms pA_pos
    by (metis divide_eq_0_iff measure_cond_prob_space_subset zero_less_measure_iff)
  have [simp]: "B \<in> MA_PS.events"
    using assms by (rewrite sets_cond_prob_space) (auto simp: image_def)
  have [simp]: "finite_measure ((M\<downharpoonright>A)\<downharpoonright>B)"
    by (auto intro!: prob_space.finite_measure prob_space.cond_prob_space_correct
        simp: prob_space_axioms)
  show sets_MAB: "sets ((M\<downharpoonright>A)\<downharpoonright>B) = sets (M\<downharpoonright>B)"
    apply (rewrite prob_space.sets_cond_prob_space)
    using MA_PS.prob_space_axioms
     apply presburger
    apply (rewrite sets_cond_prob_space, unfold image_def)+
    using assms by blast
  show "\<And>C. C \<in> sets ((M\<downharpoonright>A)\<downharpoonright>B) \<Longrightarrow> emeasure ((M\<downharpoonright>A)\<downharpoonright>B) C = emeasure (M\<downharpoonright>B) C"
  proof -
    fix C assume "C \<in> sets ((M\<downharpoonright>A)\<downharpoonright>B)"
    hence "C \<in> sets (M\<downharpoonright>B)" using sets_MAB by simp
    from this obtain D where "D \<in> events" "C = B \<inter> D"
      by (rewrite in asm sets_cond_prob_space, auto)
    hence [simp]: "C \<in> events" and [simp]: "C \<subseteq> B" and [simp]: "C \<subseteq> A" using assms by auto
    hence [simp]: "C \<in> MA_PS.events"
      using assms by (rewrite sets_cond_prob_space, unfold image_def) blast
    show "emeasure ((M\<downharpoonright>A)\<downharpoonright>B) C = emeasure (M\<downharpoonright>B) C"
      apply (rewrite finite_measure.emeasure_eq_measure, simp)+
      apply (rewrite ennreal_inj, simp_all)
      apply (rewrite prob_space.measure_cond_prob_space_subset,
          simp_all add: assms prob_space_axioms MA_PS.prob_space_axioms)+
      using pA_pos by fastforce 
      (* TODO: fix this proof *)
  qed
qed

lemma cond_prob_space_prob:
  assumes[measurable]: "Measurable.pred M P" "Measurable.pred M Q"
    and "\<P>(x in M. Q x) > 0"
  shows "measure (M \<downharpoonright> {x \<in> space M. Q x}) {x \<in> space M. P x \<and> Q x} = \<P>(x in M. P x \<bar> Q x)"
proof -
  let ?SetP = "{x \<in> space M. P x}"
  let ?SetQ = "{x \<in> space M. Q x}"
  have "measure (M\<downharpoonright>?SetQ) {x \<in> space M. P x \<and> Q x} = measure (M\<downharpoonright>?SetQ) (?SetP \<inter> ?SetQ)"
    by (smt (verit, ccfv_SIG) Collect_cong Int_def mem_Collect_eq)
  also have "\<dots> = prob (?SetP \<inter> ?SetQ) / prob ?SetQ"
    using assms by (rewrite measure_cond_prob_space) simp_all
  also have "\<dots> = \<P>(x in M. P x \<bar> Q x)"
    unfolding cond_prob_def assms by (smt (verit) Collect_cong Int_def mem_Collect_eq)
  finally show ?thesis .
qed

lemma cond_prob_space_cond_prob:
  assumes [measurable]: "Measurable.pred M P" "Measurable.pred M Q"
    and "\<P>(x in M. Q x) > 0"
  shows "\<P>(x in M. P x \<bar> Q x) = \<P>(x in (M \<downharpoonright> {x \<in> space M. Q x}). P x)"
proof -
  let ?setQ = "{x \<in> space M. Q x}"
  have "\<P>(x in M. P x \<bar> Q x) = measure (M\<downharpoonright>?setQ) {x \<in> space M. P x \<and> Q x}"
    using cond_prob_space_prob assms by simp
  also have "\<dots> = \<P>(x in (M\<downharpoonright>?setQ). P x)"
  proof -
    have "{x \<in> space M. P x \<and> Q x} = {x \<in> space (M\<downharpoonright>?setQ). P x}"
      using space_cond_prob_space assms by force
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma cond_prob_neg:
  assumes[measurable]: "Measurable.pred M P" "Measurable.pred M Q"
    and "\<P>(x in M. Q x) > 0"
  shows "\<P>(x in M. \<not> P x \<bar> Q x) = 1 - \<P>(x in M. P x \<bar> Q x)"
proof -
  let ?setP = "{x \<in> space M. P x}"
  let ?setQ = "{x \<in> space M. Q x}"
  interpret setQ_PS: prob_space "M\<downharpoonright>?setQ" using cond_prob_space_correct assms by simp
  have [simp]: "{x \<in> space (M\<downharpoonright>?setQ). P x} \<in> setQ_PS.events"
  proof -
    have "{x \<in> space (M\<downharpoonright>?setQ). P x} = ?setQ \<inter> ?setP" using space_cond_prob_space by force
    thus ?thesis using sets_cond_prob_space by simp
  qed
  have "\<P>(x in M. \<not> P x \<bar> Q x) = \<P>(x in M\<downharpoonright>?setQ. \<not> P x)"
    by (rewrite cond_prob_space_cond_prob; simp add: assms)
  also have "\<dots> = 1 - \<P>(x in M\<downharpoonright>?setQ. P x)" by (rewrite setQ_PS.prob_neg) (simp_all add: assms)
  also have "\<dots> = 1 - \<P>(x in M. P x \<bar> Q x)"
    by (rewrite cond_prob_space_cond_prob; simp add: assms)
  finally show ?thesis .
qed

lemma random_variable_cond_prob_space:
  fixes A :: "'a set"
  assumes [measurable]: "random_variable borel X"
  shows "X \<in> borel_measurable (M\<downharpoonright>A)"
  by(auto intro!: measurable_restrict_space1 simp: cond_prob_space_def cong: measurable_cong_sets)

lemma AE_cond_prob_space_iff:
  assumes "A \<in> events" "prob A > 0"
  shows "(AE x in M\<downharpoonright>A. P x) \<longleftrightarrow> (AE x in M. x \<in> A \<longrightarrow> P x)"
proof -
  have [simp]: "1 / emeasure M A > 0"
    using assms divide_ennreal emeasure_eq_measure ennreal_1
    by (simp add: ennreal_zero_less_divide)
  show ?thesis
    unfolding cond_prob_space_def
    apply (rewrite AE_scale_measure_iff)
     apply fact
    by (rewrite AE_restrict_space_iff; simp add: assms)
qed

lemma integral_cond_prob_space_nn:
  assumes [measurable]:"A \<in> events" "prob A > 0"
    and [measurable]: "random_variable borel X"
    and nonneg: "AE x in M. x \<in> A \<longrightarrow> 0 \<le> X x"
  shows "integral\<^sup>L (M\<downharpoonright>A) X = expectation (\<lambda>x. indicator A x * X x) / prob A"
proof -
  have [measurable]: "X \<in> borel_measurable (M\<downharpoonright>A)"
    by (rule random_variable_cond_prob_space; (simp add: assms))
  have [simp]: "AE x in (M\<downharpoonright>A). 0 \<le> X x"
    by (rewrite AE_cond_prob_space_iff; simp add: assms)
  have [measurable]: "random_variable borel (\<lambda>x. indicat_real A x * X x)" 
    using borel_measurable_indicator assms by force
  have [simp]: "AE x in M. 0 \<le> indicat_real A x * X x" using nonneg by fastforce
  have "integral\<^sup>L (M\<downharpoonright>A) X = enn2real (\<integral>\<^sup>+ x. ennreal (X x) \<partial>(M\<downharpoonright>A))"
    by (rewrite integral_eq_nn_integral; simp)
  also have "\<dots> = enn2real (1 / prob A * \<integral>\<^sup>+ x. ennreal (X x) \<partial>(restrict_space M A))"
    using divide_ennreal assms
    by(auto simp: nn_integral_scale_measure cond_prob_space_def measurable_restrict_space1
        emeasure_eq_measure ennreal_1[symmetric] simp del: ennreal_1)
  also have "\<dots> = enn2real (1 / prob A * (\<integral>\<^sup>+ x. ennreal (indicator A x * X x) \<partial>M))"
    by (simp add: assms nn_integral_restrict_space nn_integral_set_ennreal mult.commute)
  also have "\<dots> = integral\<^sup>L M (\<lambda>x. indicator A x * X x) / prob A"
    by (simp add: divide_nonneg_pos enn2real_mult integral_eq_nn_integral)
  finally show ?thesis by simp
qed

end

text \<open>
  Define the complementary cumulative distribution function, also known as tail distribution.
  The theory presented below is a slight modification of the subsection "Properties of cdf's"
  in the theory \<open>Distribution_Functions\<close>.
\<close>

subsection \<open>Complementary Cumulative Distribution Function\<close>

definition ccdf :: "real measure \<Rightarrow> real \<Rightarrow> real"
  where "ccdf M \<equiv> \<lambda>x. measure M {x<..}"
    \<comment> \<open>complementary cumulative distribution function (tail distribution)\<close>

lemma ccdf_def2: "ccdf M x = measure M {x<..}"
  by (simp add: ccdf_def)

context finite_borel_measure
begin

lemma add_cdf_ccdf: "cdf M x + ccdf M x = measure M (space M)"
proof -
  have "{..x} \<union> {x<..} = UNIV" by auto
  moreover have "{..x} \<inter> {x<..} = {}" by auto
  ultimately have "emeasure M {..x} + emeasure M {x<..} = emeasure M UNIV"
    using plus_emeasure M_is_borel atMost_borel greaterThan_borel by metis
  hence "measure M {..x} + measure M {x<..} = measure M UNIV"
    using finite_emeasure_space emeasure_eq_measure ennreal_inj
    by (metis measure_def enn2real_plus ennreal_less_top)
  thus ?thesis unfolding cdf_def ccdf_def using borel_UNIV by simp
qed

lemma ccdf_cdf: "ccdf M = (\<lambda>x. measure M (space M) - cdf M x)"
  by (rule ext) (smt (verit) add_cdf_ccdf)

lemma cdf_ccdf: "cdf M = (\<lambda>x. measure M (space M) - ccdf M x)"
  by (rule ext) (smt (verit) add_cdf_ccdf)

lemma isCont_cdf_ccdf: "isCont (cdf M) x \<longleftrightarrow> isCont (ccdf M) x"
proof
  show "isCont (cdf M) x \<Longrightarrow> isCont (ccdf M) x" by (rewrite ccdf_cdf) auto
next
  show "isCont (ccdf M) x \<Longrightarrow> isCont (cdf M) x" by (rewrite cdf_ccdf) auto
qed

lemma isCont_ccdf: "isCont (ccdf M) x \<longleftrightarrow> measure M {x} = 0"
  using isCont_cdf_ccdf isCont_cdf by simp

lemma continuous_cdf_ccdf:
  shows "continuous F (cdf M) \<longleftrightarrow> continuous F (ccdf M)"
    (is "?LHS \<longleftrightarrow> ?RHS")
proof
  assume ?LHS
  thus ?RHS using continuous_diff continuous_const by (rewrite ccdf_cdf) blast
next
  assume ?RHS
  thus ?LHS using continuous_diff continuous_const by (rewrite cdf_ccdf) blast
qed

lemma has_real_derivative_cdf_ccdf:
  "(cdf M has_real_derivative D) F \<longleftrightarrow> (ccdf M has_real_derivative -D) F"
proof
  assume "(cdf M has_real_derivative D) F"
  thus "(ccdf M has_real_derivative -D) F"
    using ccdf_cdf DERIV_const Deriv.field_differentiable_diff by fastforce
next
  assume "(ccdf M has_real_derivative -D) F"
  thus "(cdf M has_real_derivative D) F"
    using cdf_ccdf DERIV_const Deriv.field_differentiable_diff by fastforce
qed

lemma differentiable_cdf_ccdf: "(cdf M differentiable F) \<longleftrightarrow> (ccdf M differentiable F)"
  by (metis differentiable_def has_real_derivative_cdf_ccdf has_real_derivative_iff
      minus_equation_iff)

lemma deriv_cdf_ccdf:
  assumes "cdf M differentiable at x"
  shows "deriv (cdf M) x = - deriv (ccdf M) x"
  using has_real_derivative_cdf_ccdf differentiable_cdf_ccdf assms
  by (simp add: DERIV_deriv_iff_real_differentiable DERIV_imp_deriv)

lemma ccdf_diff_eq2:
  assumes "x \<le> y"
  shows "ccdf M x - ccdf M y = measure M {x<..y}"
proof -
  have "ccdf M x - ccdf M y = cdf M y - cdf M x"
    using add_cdf_ccdf by (metis add_diff_cancel_left add_diff_cancel_right)
  also have "\<dots> = measure M {x<..y}" using cdf_diff_eq2 assms by simp
  finally show ?thesis .
qed

lemma ccdf_nonincreasing: "x \<le> y \<Longrightarrow> ccdf M x \<ge> ccdf M y"
  using ccdf_cdf cdf_nondecreasing by auto

lemma ccdf_nonneg: "ccdf M x \<ge> 0"
  by (simp add: ccdf_def)

lemma ccdf_bounded: "ccdf M x \<le> measure M (space M)"
  by (simp add: ccdf_def bounded_measure)

lemma ccdf_lim_at_top: "(ccdf M \<longlongrightarrow> 0) at_top"
proof -
  have "((\<lambda>x. measure M (space M) - cdf M x) \<longlongrightarrow> measure M (space M) - measure M (space M)) at_top"
    by (intro tendsto_intros cdf_lim_at_top)
  thus ?thesis
    by (rewrite ccdf_cdf) simp
qed

lemma ccdf_lim_at_bot: "(ccdf M \<longlongrightarrow> measure M (space M)) at_bot"
proof -
  have "((\<lambda>x. measure M (space M) - cdf M x) \<longlongrightarrow> measure M (space M) - 0) at_bot"
    by (intro tendsto_intros cdf_lim_at_bot)
  thus ?thesis
    by (rewrite ccdf_cdf) simp
qed

lemma ccdf_is_right_cont: "continuous (at_right a) (ccdf M)"
proof -
  have "continuous (at_right a) (\<lambda>x. measure M (space M) - cdf M x)"
    by (intro continuous_intros cdf_is_right_cont)
  thus ?thesis by (rewrite ccdf_cdf) simp
qed

end

context prob_space
begin

lemma ccdf_distr_measurable [measurable]:
  assumes [measurable]: "random_variable borel X"
  shows "ccdf (distr M borel X) \<in> borel_measurable borel"
  using real_distribution.finite_borel_measure_M by (rewrite finite_borel_measure.ccdf_cdf; simp)

lemma ccdf_distr_P:
  assumes [measurable]:"random_variable borel X"
  shows "ccdf (distr M borel X) x = \<P>(\<omega> in M. X \<omega> > x)"
  by(auto simp: measure_distr ccdf_def intro!: arg_cong[where f=prob])

lemma ccdf_continuous_distr_P_ge:
  assumes "random_variable borel X" "isCont (ccdf (distr M borel X)) x"
  shows "ccdf (distr M borel X) x = \<P>(\<omega> in M. X \<omega> \<ge> x)"
proof -
  have "ccdf (distr M borel X) x = measure (distr M borel X) {x<..}" unfolding ccdf_def by simp
  also have "\<dots> = measure (distr M borel X) ({x<..} \<union> {x})"
    apply (rewrite finite_measure.measure_zero_union, simp_all add: assms finite_measure_distr)
    using finite_borel_measure.isCont_ccdf real_distribution.finite_borel_measure_M assms by blast
  also have "\<dots> = measure (distr M borel X) {x..}" by (metis Un_commute ivl_disj_un_singleton(1))
  also have "\<dots> = \<P>(\<omega> in M. X \<omega> \<ge> x)" 
    apply (rewrite measure_distr, simp_all add: assms)
    unfolding vimage_def by simp (smt (verit) Collect_cong Int_def mem_Collect_eq)
  finally show ?thesis .
qed

lemma ccdf_distr_diff_P:
  assumes "x \<le> y"
    and [measurable]:"random_variable borel X"
  shows "ccdf (distr M borel X) x - ccdf (distr M borel X) y = \<P>(\<omega> in M. x < X \<omega> \<and> X \<omega> \<le> y)"
proof -
  interpret distrX_FBM: finite_borel_measure "distr M borel X"
    using real_distribution.finite_borel_measure_M real_distribution_distr assms by simp
  have "ccdf (distr M borel X) x - ccdf (distr M borel X) y = measure (distr M borel X) {x<..y}"
    by (rewrite distrX_FBM.ccdf_diff_eq2; simp add: assms)
  also have "\<dots> = \<P>(\<omega> in M. x < X \<omega> \<and> X \<omega> \<le> y)"
    by(auto simp: measure_distr intro!: arg_cong[where f=prob])
  finally show ?thesis .
qed

end

context real_distribution
begin

lemma ccdf_bounded_prob: "\<And>x. ccdf M x \<le> 1"
  by (subst prob_space[THEN sym], rule ccdf_bounded)

lemma ccdf_lim_at_bot_prob: "(ccdf M \<longlongrightarrow> 1) at_bot"
  by (subst prob_space[THEN sym], rule ccdf_lim_at_bot)

end

text \<open>Introduce the hazard rate. This notion will be used to define the force of mortality.\<close>

subsection \<open>Hazard Rate\<close>

context prob_space
begin

definition hazard_rate :: "('a \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real"
  where "hazard_rate X t \<equiv>
    Lim (at_right 0) (\<lambda>dt. \<P>(x in M. t < X x \<and> X x \<le> t + dt \<bar> X x > t) / dt)"
    \<comment> \<open>Here, \<open>X\<close> is supposed to be a random variable.\<close>

lemma hazard_rate_0_ccdf_0:
  assumes [measurable]: "random_variable borel X"
    and "ccdf (distr M borel X) t = 0"
  shows "hazard_rate X t = 0"
  \<comment> \<open>Note that division by \<open>0\<close> is calculated as \<open>0\<close> in Isabelle/HOL.\<close>
proof -
  have "\<And>dt. \<P>(x in M. t < X x \<and> X x \<le> t + dt \<bar> X x > t) = 0"
    unfolding cond_prob_def using ccdf_distr_P assms by simp
  hence "hazard_rate X t = Lim (at_right 0) (\<lambda>dt::real. 0)"
    unfolding hazard_rate_def by (rewrite Lim_cong; simp)
  also have "\<dots> = 0" by (rule tendsto_Lim; simp)
  finally show ?thesis .
qed

lemma hazard_rate_deriv_cdf:
  assumes [measurable]: "random_variable borel X"
    and "(cdf (distr M borel X)) differentiable at t"
  shows "hazard_rate X t = deriv (cdf (distr M borel X)) t / ccdf (distr M borel X) t"
proof (cases \<open>ccdf (distr M borel X) t = 0\<close>)
  case True
  with hazard_rate_0_ccdf_0 show ?thesis by simp
next
  case h:False
  let ?F = "cdf (distr M borel X)"
  have "\<forall>\<^sub>F dt in at_right 0. \<P>(x in M. t < X x \<and> X x \<le> t + dt \<bar> X x > t) / dt =
    (?F (t + dt) - ?F t) / dt / ccdf (distr M borel X) t"
    apply (rule eventually_at_rightI[where b=1]; simp)
    unfolding cond_prob_def
    apply (rewrite cdf_distr_diff_P; simp)
    apply (rewrite ccdf_distr_P[THEN sym], simp)
    by (smt (verit) Collect_cong mult.commute) (* TODO: fix this proof *)
  moreover have "((\<lambda>dt. (?F (t + dt) - ?F t) / dt / ccdf (distr M borel X) t) \<longlongrightarrow>
    deriv ?F t / ccdf (distr M borel X) t) (at_right 0)"
    apply (rule tendsto_intros)
      apply (rule Lim_at_imp_Lim_at_within)
    using DERIV_deriv_iff_real_differentiable assms DERIV_def
      apply blast
     apply (rule Lim_at_imp_Lim_at_within)
    using DERIV_deriv_iff_real_differentiable assms DERIV_def
     apply blast
    apply fact
    done
  ultimately show ?thesis
    unfolding hazard_rate_def using tendsto_cong by (intro tendsto_Lim; fastforce)
qed

lemma deriv_cdf_hazard_rate:
  assumes [measurable]: "random_variable borel X"
    and "(cdf (distr M borel X)) differentiable at t"
  shows "deriv (cdf (distr M borel X)) t = ccdf (distr M borel X) t * hazard_rate X t"
proof -
  interpret distrX_FBM: finite_borel_measure "distr M borel X"
    using real_distribution.finite_borel_measure_M real_distribution_distr assms by simp
  show ?thesis
  proof (cases \<open>ccdf (distr M borel X) t = 0\<close>)
    case True
    hence "cdf (distr M borel X) t = 1"
      using distrX_FBM.cdf_ccdf
      by (metis assms(1) diff_0_right prob_space.prob_space prob_space_distr)
    moreover obtain D where "(cdf (distr M borel X) has_real_derivative D) (at t)"
      using assms real_differentiable_def by blast
    ultimately have "(cdf (distr M borel X) has_real_derivative 0) (at t)"
      using assms
      by (smt (verit) DERIV_local_max real_distribution.cdf_bounded_prob real_distribution_distr)
    thus ?thesis using True by (simp add: DERIV_imp_deriv)
  next
    case False
    thus ?thesis using hazard_rate_deriv_cdf assms by simp
  qed
qed

lemma hazard_rate_deriv_ccdf:
  assumes [measurable]: "random_variable borel X"
    and "(ccdf (distr M borel X)) differentiable at t"
  shows "hazard_rate X t = - deriv (ccdf (distr M borel X)) t / ccdf (distr M borel X) t"
proof -
  interpret distrX_FBM: finite_borel_measure "distr M borel X"
    using real_distribution.finite_borel_measure_M real_distribution_distr assms by simp
  show ?thesis
    using hazard_rate_deriv_cdf distrX_FBM.deriv_cdf_ccdf assms distrX_FBM.differentiable_cdf_ccdf
    by presburger
qed

lemma deriv_ccdf_hazard_rate: 
  assumes [measurable]: "random_variable borel X"
    and "(ccdf (distr M borel X)) differentiable at t"
  shows "deriv (ccdf (distr M borel X)) t = - ccdf (distr M borel X) t * hazard_rate X t"
proof -
  interpret distrX_FBM: finite_borel_measure "distr M borel X"
    using real_distribution.finite_borel_measure_M real_distribution_distr assms by simp
  show ?thesis
    using deriv_cdf_hazard_rate distrX_FBM.deriv_cdf_ccdf assms distrX_FBM.differentiable_cdf_ccdf
    by simp
qed

lemma hazard_rate_deriv_ln_ccdf:
  assumes [measurable]: "random_variable borel X"
    and "(ccdf (distr M borel X)) differentiable at t"
    and "ccdf (distr M borel X) t \<noteq> 0"
  shows "hazard_rate X t = - deriv (\<lambda>t. ln (ccdf (distr M borel X) t)) t"
proof -
  interpret distrX_FBM: finite_borel_measure "distr M borel X"
    using real_distribution.finite_borel_measure_M real_distribution_distr assms by simp
  let ?srvl = "ccdf (distr M borel X)"
  have "?srvl t > 0" using distrX_FBM.ccdf_nonneg assms
    by (meson add_strict_increasing add_strict_increasing2 less_add_same_cancel1
        linorder_neqE_linordered_idom)
  moreover have "(?srvl has_real_derivative (deriv ?srvl t)) (at t)"
    using DERIV_deriv_iff_real_differentiable assms by blast
  ultimately have "((\<lambda>t. ln (?srvl t)) has_real_derivative  1 / ?srvl t * deriv ?srvl t) (at t)"
    by (rule derivative_intros)
  hence "deriv (\<lambda>t. ln (?srvl t)) t = deriv ?srvl t / ?srvl t" by (simp add: DERIV_imp_deriv)
  also have "\<dots> = - hazard_rate X t" using hazard_rate_deriv_ccdf assms by simp
  finally show ?thesis by simp
qed

lemma hazard_rate_has_integral:
  assumes [measurable]: "random_variable borel X"
    and "t \<le> u"
    and "(ccdf (distr M borel X)) piecewise_differentiable_on {t<..<u}"
    and "continuous_on {t..u} (ccdf (distr M borel X))"
    and "\<And>s. s \<in> {t..u} \<Longrightarrow> ccdf (distr M borel X) s \<noteq> 0"
  shows
    "(hazard_rate X has_integral ln (ccdf (distr M borel X) t / ccdf (distr M borel X) u)) {t..u}"
proof -
  interpret distrX_FBM: finite_borel_measure "distr M borel X"
    using real_distribution.finite_borel_measure_M real_distribution_distr assms by simp
  let ?srvl = "ccdf (distr M borel X)"
  have [simp]: "\<And>s. t \<le> s \<and> s \<le> u \<Longrightarrow> ?srvl s > 0"
    using distrX_FBM.ccdf_nonneg assms by (smt (verit) atLeastAtMost_iff)
  have "(deriv (\<lambda>s. - ln (?srvl s)) has_integral - ln (?srvl u) - - ln (?srvl t)) {t..u}"
  proof -
    have "continuous_on {t..u} (\<lambda>s. - ln (?srvl s))"
      by (intro continuous_intros continuous_on_ln) (auto simp add: assms)
    moreover hence "(\<lambda>s. - ln (?srvl s)) piecewise_differentiable_on {t<..<u}"
    proof -
      have "?srvl ` {t<..<u} \<subseteq> {0<..}"
      proof -
        { fix s assume "s \<in> {t<..<u}"
          hence "?srvl s \<noteq> 0" using assms by simp
          moreover have "?srvl s \<ge> 0" using distrX_FBM.ccdf_nonneg by simp
          ultimately have "?srvl s > 0" by simp }
        thus ?thesis by auto
      qed
      hence "(\<lambda>r. - ln r) \<circ> ?srvl piecewise_differentiable_on {t<..<u}"
        apply (intro differentiable_on_piecewise_compose)
         apply(simp add: assms)
        apply (rule derivative_intros)
        apply (rule differentiable_on_subset[of ln "{0<..}"])
         apply (rewrite differentiable_on_eq_field_differentiable_real)
        unfolding field_differentiable_def using DERIV_ln
        by (meson greaterThan_iff has_field_derivative_at_within) simp
      thus ?thesis unfolding comp_def by simp
    qed
    ultimately show ?thesis by (intro FTC_real_deriv_has_integral; simp add: assms)
  qed
  hence ln: "(deriv (\<lambda>s. - ln (?srvl s)) has_integral ln (?srvl t / ?srvl u)) {t..u}"
    by (rewrite ln_div; force simp: assms)
  thus "((hazard_rate X) has_integral ln (?srvl t / ?srvl u)) {t..u}"
  proof -
    from assms obtain S0 where finS0: "finite S0" and
      diffS0: "\<And>s. s \<in> {t<..<u} - S0 \<Longrightarrow> ?srvl differentiable at s within {t<..<u}"
      unfolding piecewise_differentiable_on_def by blast
    from this obtain S where "finite S" and "\<And>s. s \<in> {t..u} - S \<Longrightarrow> ?srvl differentiable at s"
    proof (atomize_elim)
      let ?S = "S0 \<union> {t, u}"
      have "finite ?S" using finS0 by simp
      moreover have "\<forall>s. s \<in> {t..u} - ?S \<longrightarrow> ccdf (distr M borel X) differentiable at s"
      proof -
        { fix s assume s_in: "s \<in> {t..u} - ?S"
          hence "?srvl differentiable at s within {t<..<u}" using diffS0 by simp
          hence "?srvl differentiable at s"
            using s_in by (rewrite at_within_open[THEN sym], simp_all) }
        thus ?thesis by blast
      qed
      ultimately show
        "\<exists>S. finite S \<and> (\<forall>s. s \<in> {t..u} - S \<longrightarrow> ccdf (distr M borel X) differentiable at s)"
        by blast
    qed
    thus ?thesis
      apply (rewrite has_integral_spike_finite_eq [of S _ "deriv (\<lambda>s. - ln (?srvl s))"])
        apply simp
       apply (rewrite hazard_rate_deriv_ln_ccdf)
          apply simp
         apply(simp add: assms)
        apply(simp add: assms)
       apply (rewrite deriv_minus)
        apply (rewrite in asm differentiable_eq_field_differentiable_real)
        apply (rewrite comp_def[THEN sym])
        apply(rule field_differentiable_compose[of "?srvl"])
         apply simp
      unfolding field_differentiable_def
        apply (rule exI)
        apply(rule DERIV_ln)
        apply simp
       apply simp
      using ln
      apply simp
      done
  qed
qed

corollary hazard_rate_integrable:
  assumes [measurable]: "random_variable borel X"
    and "t \<le> u"
    and "(ccdf (distr M borel X)) piecewise_differentiable_on {t<..<u}"
    and "continuous_on {t..u} (ccdf (distr M borel X))"
    and "\<And>s. s \<in> {t..u} \<Longrightarrow> ccdf (distr M borel X) s \<noteq> 0"
  shows "hazard_rate X integrable_on {t..u}"
  using has_integral_integrable hazard_rate_has_integral assms by blast

lemma ccdf_exp_cumulative_hazard:
  assumes [measurable]: "random_variable borel X"
    and "t \<le> u"
    and "(ccdf (distr M borel X)) piecewise_differentiable_on {t<..<u}"
    and "continuous_on {t..u} (ccdf (distr M borel X))"
    and "\<And>s. s \<in> {t..u} \<Longrightarrow> ccdf (distr M borel X) s \<noteq> 0"
  shows "ccdf (distr M borel X) u / ccdf (distr M borel X) t =
    exp (- integral {t..u} (hazard_rate X))"
proof -
  interpret distrX_FBM: finite_borel_measure "distr M borel X"
    using real_distribution.finite_borel_measure_M real_distribution_distr assms by simp
  let ?srvl = "ccdf (distr M borel X)"
  have [simp]: "\<And>s. t \<le> s \<and> s \<le> u \<Longrightarrow> ?srvl s > 0"
    using distrX_FBM.ccdf_nonneg assms
    by (metis atLeastAtMost_iff less_eq_real_def)
  have "integral {t..u} (hazard_rate X) = ln (?srvl t / ?srvl u)"
    using hazard_rate_has_integral has_integral_integrable_integral assms by auto
  also have "\<dots> = - ln (?srvl u / ?srvl t)" using ln_div assms by simp
  finally have "- integral {t..u} (hazard_rate X) = ln (?srvl u / ?srvl t)" by simp
  thus ?thesis using assms by simp
qed

lemma hazard_rate_density_ccdf:
  assumes "distributed M lborel X f"
    and "\<And>s. f s \<ge> 0" "t < u" "continuous_on {t..u} f"
  shows "hazard_rate X t = f t / ccdf (distr M borel X) t"
proof (cases \<open>ccdf (distr M borel X) t = 0\<close>)
  case True
  thus ?thesis
    using assms
    by (rewrite hazard_rate_0_ccdf_0)
       (auto dest: distributed_measurable)
next
  case False
  have [simp]: "t \<le> u" using assms by simp
  have [measurable]: "random_variable borel X"
    using assms distributed_measurable measurable_lborel1 by blast
  have [measurable]: "f \<in> borel_measurable lborel"
    using assms distributed_real_measurable by metis
  have [simp]: "integrable lborel f"
  proof -
    have "prob (X -` UNIV \<inter> space M) = LINT x|lborel. indicat_real UNIV x * f x"
      by (rule distributed_measure; simp add: assms)
    thus ?thesis
      using prob_space not_integrable_integral_eq by fastforce
  qed
  have "((\<lambda>dt. (LBINT s:{t..t+dt}. f s) / dt) \<longlongrightarrow> f t) (at_right 0)"
  proof -
    have "\<And>dt. (\<integral>\<^sup>+ x. ennreal (indicat_real {t..t+dt} x * f x) \<partial>lborel) < \<infinity>"
    proof -
      fix dt :: real
      have "(\<integral>\<^sup>+ x. ennreal (indicat_real {t..t+dt} x * f x) \<partial>lborel) =
        set_nn_integral lborel {t..t+dt} f"
        by (metis indicator_mult_ennreal mult.commute)
      moreover have "emeasure M (X -` {t..t+dt} \<inter> space M) = set_nn_integral lborel {t..t+dt} f"
        by (rule distributed_emeasure; simp add: assms)
      moreover have "emeasure M (X -` {t..t+dt} \<inter> space M) < \<infinity>"
        using emeasure_eq_measure ennreal_less_top infinity_ennreal_def by presburger
      ultimately show "(\<integral>\<^sup>+ x. ennreal (indicat_real {t..t+dt} x * f x) \<partial>lborel) < \<infinity>" by simp
    qed
    hence "\<And>dt. (LBINT s:{t..t+dt}. f s) = integral {t..t+dt} f"
      by (auto intro!: set_borel_integral_eq_integral integrableI_nonneg
          simp: set_integrable_def assms)
    moreover have "((\<lambda>dt. (integral {t..t+dt} f) / dt) \<longlongrightarrow> f t) (at_right 0)"
    proof -
      have "((\<lambda>x. integral {t..x} f) has_real_derivative f t) (at t within {t..u})"
        by (rule integral_has_real_derivative; simp add: assms)
      moreover have "(at t within {t..u}) = (at (t+0) within (+)t ` {0..u-t})" by simp
      ultimately have
        "((\<lambda>x. integral {t..x} f) \<circ> (+)t has_real_derivative f t) (at 0 within {0..u-t})"
        by (metis DERIV_at_within_shift_lemma)
      hence "((\<lambda>dt. (integral {t..t+dt} f) / dt) \<longlongrightarrow> f t) (at 0 within {0..u-t})"
        using has_field_derivative_iff by force
      thus ?thesis using at_within_Icc_at_right assms
        by (metis (lifting) diff_gt_0_iff_gt)
    qed
    ultimately show ?thesis by simp
  qed
  moreover have "\<And>dt. dt > 0 \<Longrightarrow> \<P>(x in M. X x \<in> {t <.. t+dt}) = (LBINT s:{t..t+dt}. f s)"
  proof -
    fix dt :: real assume "dt > 0"
    hence [simp]: "sym_diff {t<..t + dt} {t..t + dt} = {t}" by force
    have "(\<integral>s. indicator {t<..t+dt} s * f s \<partial>lborel) = prob (X -` {t<..t+dt} \<inter> space M)"
      by (rule distributed_measure[THEN sym]; simp add: assms)
    hence "\<P>(x in M. X x \<in> {t <.. t+dt}) = (LBINT s:{t<..t+dt}. f s)"
      by(auto intro!: arg_cong[where f=prob] simp: set_lebesgue_integral_def)
    moreover have "(LBINT s:{t<..t+dt}. f s) = (LBINT s:{t..t+dt}. f s)"
      by (rule set_integral_null_delta; force)
    ultimately show "\<P>(x in M. X x \<in> {t <.. t+dt}) = (LBINT s:{t..t+dt}. f s)" by simp
  qed
  ultimately have "((\<lambda>dt. \<P>(x in M. t < X x \<and> X x \<le> t + dt) / dt) \<longlongrightarrow> f t) (at_right 0)"
    by(auto intro!: Lim_cong_within
       [where f="\<lambda>dt. \<P>(x in M. t < X x \<and> X x \<le> t + dt) / dt"
          and g="\<lambda>dt. (LBINT s:{t..t+dt}. f s) / dt",THEN iffD2])
  hence "((\<lambda>dt. \<P>(x in M. t < X x \<and> X x \<le> t + dt \<bar> X x > t) / dt) \<longlongrightarrow>
    f t / ccdf (distr M borel X) t) (at_right 0)"
    unfolding cond_prob_def
    apply (rewrite ccdf_distr_P[THEN sym])
     apply simp
    unfolding conj.assoc divide_divide_eq_left
    apply (rewrite mult.commute)
    apply(rewrite divide_divide_eq_left[THEN sym])
    apply(rule tendsto_intros)
    by(auto intro!: Lim_cong_within
        [where f="\<lambda>x. prob {\<omega> \<in> space M. t < X \<omega> \<and> X \<omega> \<le> t + x \<and> t < X \<omega>} / x"
          and g="\<lambda>dt. prob {x \<in> space M. t < X x \<and> X x \<le> t + dt} / dt", THEN iffD2]
        arg_cong[where f=prob] False)
  thus ?thesis unfolding hazard_rate_def by (intro tendsto_Lim; simp)
qed

end

end