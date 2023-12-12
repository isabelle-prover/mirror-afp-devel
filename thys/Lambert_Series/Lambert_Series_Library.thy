section \<open>Missing Library Material\<close>
theory Lambert_Series_Library
imports 
  "HOL-Complex_Analysis.Complex_Analysis"
  "HOL-Library.Landau_Symbols"
  "HOL-Real_Asymp.Real_Asymp"
begin

subsection \<open>Miscellaneous\<close>

lemma power_less_1_iff: "x \<ge> 0 \<Longrightarrow> (x :: real) ^ n < 1 \<longleftrightarrow> x < 1 \<and> n > 0"
  by (metis not_gr_zero not_less_iff_gr_or_eq power_0 real_root_lt_1_iff real_root_pos2)

lemma fls_nth_sum: "fls_nth (\<Sum>x\<in>A. f x) n = (\<Sum>x\<in>A. fls_nth (f x) n)"
  by (induction A rule: infinite_finite_induct) auto

lemma two_times_choose_two: "2 * (n choose 2) = n * (n - 1)"
  unfolding choose_two by (simp add: algebra_simps)

lemma Nats_not_empty [simp]: "\<nat> \<noteq> {}"
  using Nats_1 by blast


subsection \<open>Infinite sums\<close>

lemma has_sum_iff: "(f has_sum S) A \<longleftrightarrow> f summable_on A \<and> infsum f A = S"
  using infsumI summable_iff_has_sum_infsum by blast
  
lemma summable_on_reindex_bij_witness:
  assumes "\<And>a. a \<in> S \<Longrightarrow> i (j a) = a"
  assumes "\<And>a. a \<in> S \<Longrightarrow> j a \<in> T"
  assumes "\<And>b. b \<in> T \<Longrightarrow> j (i b) = b"
  assumes "\<And>b. b \<in> T \<Longrightarrow> i b \<in> S"
  assumes "\<And>a. a \<in> S \<Longrightarrow> h (j a) = g a"
  shows   "g summable_on S \<longleftrightarrow> h summable_on T"
  using has_sum_reindex_bij_witness[of S i j T h g, OF assms refl]
  by (simp add: summable_on_def)

lemma has_sum_diff:
  fixes f g :: "'a \<Rightarrow> 'b::{topological_ab_group_add}"
  assumes \<open>(f has_sum a) A\<close>
  assumes \<open>(g has_sum b) A\<close>
  shows \<open>((\<lambda>x. f x - g x) has_sum (a - b)) A\<close>
  using has_sum_add[of f A a "\<lambda>x. -g x" "-b"] assms by (simp add: has_sum_uminus)

lemma summable_on_diff:
  fixes f g :: "'a \<Rightarrow> 'b::{topological_ab_group_add}"
  assumes \<open>f summable_on A\<close>
  assumes \<open>g summable_on A\<close>
  shows \<open>(\<lambda>x. f x - g x) summable_on A\<close>
  by (metis (full_types) assms summable_on_def has_sum_diff)

lemma infsum_diff:
  fixes f g :: "'a \<Rightarrow> 'b::{topological_ab_group_add, t2_space}"
  assumes \<open>f summable_on A\<close>
  assumes \<open>g summable_on A\<close>
  shows \<open>infsum (\<lambda>x. f x - g x) A = infsum f A - infsum g A\<close>
proof -
  have \<open>((\<lambda>x. f x - g x) has_sum (infsum f A - infsum g A)) A\<close>
    by (simp add: assms has_sum_diff)
  then show ?thesis
    using infsumI by blast
qed

lemma summable_norm_add:
  assumes "summable (\<lambda>n. norm (f n))" "summable (\<lambda>n. norm (g n))"
  shows   "summable (\<lambda>n. norm (f n + g n))"
proof (rule summable_comparison_test)
  show "summable (\<lambda>n. norm (f n) + norm (g n))"
    by (intro summable_add assms)
  show "\<exists>N. \<forall>n\<ge>N. norm (norm (f n + g n)) \<le> norm (f n) + norm (g n)"
    by (intro exI[of _ 0] allI impI) (auto simp: norm_triangle_ineq)
qed

lemma summable_norm_diff:
  assumes "summable (\<lambda>n. norm (f n))" "summable (\<lambda>n. norm (g n))"
  shows   "summable (\<lambda>n. norm (f n - g n))"
  using summable_norm_add[of f "\<lambda>n. -g n"] assms by simp

lemma sums_imp_has_prod_exp:
  fixes f :: "_ \<Rightarrow>'a::{real_normed_field,banach}"
  assumes "f sums F"
  shows   "(\<lambda>n. exp (f n)) has_prod exp F"
proof -
  have "(\<lambda>n. exp (\<Sum>i\<le>n. f i)) \<longlonglongrightarrow> exp F"
    by (intro tendsto_intros) (use assms in \<open>auto simp: sums_def' atLeast0AtMost\<close>)
  also have "(\<lambda>n. exp (\<Sum>i\<le>n. f i)) = (\<lambda>n. \<Prod>i\<le>n. exp (f i))"
    by (simp add: exp_sum)
  finally have "raw_has_prod (\<lambda>n. exp (f n)) 0 (exp F)"
    unfolding raw_has_prod_def by auto
  thus ?thesis
    unfolding has_prod_def by blast
qed

lemma telescope_summable_iff:
  fixes f :: "nat \<Rightarrow> 'a::{real_normed_vector}"
  shows "summable (\<lambda>n. f (Suc n) - f n) \<longleftrightarrow> convergent f"
proof
  assume "convergent f"
  thus "summable (\<lambda>n. f (Suc n) - f n)"
    using telescope_summable[of f] by (auto simp: convergent_def)
next
  assume "summable (\<lambda>n. f (Suc n) - f n)"
  hence "convergent (\<lambda>n. \<Sum>i<n. f (Suc i) - f i)"
    by (simp add: summable_iff_convergent)
  also have "(\<lambda>n. \<Sum>i<n. f (Suc i) - f i) = (\<lambda>n. f n - f 0)"
    by (subst sum_lessThan_telescope) auto
  also have "convergent \<dots> \<longleftrightarrow> convergent f"
    by (rule convergent_diff_const_right_iff)
  finally show "convergent f" .
qed

lemma telescope_summable_iff':
  fixes f :: "nat \<Rightarrow> 'a::{real_normed_vector}"
  shows "summable (\<lambda>n. f n - f (Suc n)) \<longleftrightarrow> convergent f"
  using telescope_summable_iff[of "\<lambda>n. -f n"] by (simp flip: convergent_minus_iff)

lemma norm_summable_mult_bounded:
  assumes "summable (\<lambda>n. norm (f n))"
  assumes "g \<in> O(\<lambda>_. 1)"
  shows   "summable (\<lambda>n. norm (f n * g n))"
proof -
  from assms(2) obtain C where C: "C > 0" "eventually (\<lambda>n. norm (g n) \<le> C) at_top"
    by (auto elim!: landau_o.bigE)
  show ?thesis
  proof (rule summable_comparison_test_ev)
    show "summable (\<lambda>n. norm (f n) * C)"
      by (subst mult.commute) (intro summable_mult assms)
    show "eventually (\<lambda>n. norm (norm (f n * g n)) \<le> norm (f n) * C) at_top"
      using C(2) by eventually_elim (use C(1) in \<open>auto intro!: mult_mono simp: norm_mult\<close>)
  qed
qed

lemma summable_powser_comparison_test_bigo:
  fixes f g :: "nat \<Rightarrow> 'a :: {real_normed_field, banach}"
  assumes "summable f" "g \<in> O(\<lambda>n. f n * c ^ n)" "norm c < 1"
  shows   "summable (\<lambda>n. norm (g n))"
proof (rule summable_comparison_test_bigo)
  have "summable (\<lambda>n. norm (f n * c ^ n))"
    by (rule powser_insidea[of _ 1]) (use assms in auto)
  thus "summable (\<lambda>n. norm (norm (f n * c ^ n)))"
    by simp
  show "(\<lambda>n. norm (g n)) \<in> O(\<lambda>n. norm (f n * c ^ n))"
    using assms(2) by simp
qed
  
lemma geometric_sums_gen:
  assumes "norm (x :: 'a :: real_normed_field) < 1"
  shows   "(\<lambda>n. x ^ (n + k)) sums (x ^ k / (1 - x))"
proof -
  have "(\<lambda>n. x ^ k * x ^ n) sums (x ^ k * (1 / (1 - x)))"
    by (intro sums_mult geometric_sums assms)
  thus ?thesis
    by (simp add: power_add mult_ac)
qed

lemma has_sum_geometric:
  fixes x :: "'a :: {real_normed_field, banach}"
  assumes "norm x < 1"
  shows   "((\<lambda>n. x ^ n) has_sum (x ^ m / (1 - x))) {m..}"
proof -
  have "((\<lambda>n. x ^ n) has_sum (1 / (1 - x))) UNIV"
    using assms
    by (intro norm_summable_imp_has_sum)
       (auto intro: geometric_sums summable_geometric simp: norm_power)
  hence "((\<lambda>n. x ^ m * x ^ n) has_sum (x ^ m * (1 / (1 - x)))) UNIV"
    by (rule has_sum_cmult_right)
  also have "?this \<longleftrightarrow> ?thesis"
    by (rule has_sum_reindex_bij_witness[of _ "\<lambda>n. n - m" "\<lambda>n. n + m"]) (auto simp: power_add)
  finally show ?thesis .
qed

lemma n_powser_sums:
  fixes q :: "'a :: {real_normed_field,banach}"
  assumes q: "norm q < 1"
  shows   "(\<lambda>n. of_nat n * q ^ n) sums (q / (1 - q) ^ 2)"
proof -
  have "(\<lambda>n. q * (of_nat (Suc n) * q ^ n)) sums (q * (1 / (1 - q)\<^sup>2))"
    using q by (intro sums_mult geometric_deriv_sums)
  also have "(\<lambda>n. q * (of_nat (Suc n) * q ^ n)) = (\<lambda>n. of_nat (Suc n) * q ^ Suc n)"
    by (simp add: algebra_simps)
  finally have "(\<lambda>n. of_nat n * q ^ n) sums (q * (1 / (1 - q)\<^sup>2) + of_nat 0 * q ^ 0)"
    by (rule sums_Suc)
  thus "(\<lambda>n. of_nat n * q ^ n) sums (q / (1 - q) ^ 2)"
    by simp
qed


subsection \<open>Convergence radius\<close>

lemma tendsto_imp_conv_radius_eq:
  assumes "(\<lambda>n. ereal (norm (f n) powr (1 / real n))) \<longlonglongrightarrow> c'" "c = inverse c'"
  shows   "conv_radius f = c"
proof -
  have "(\<lambda>n. ereal (root n (norm (f n)))) \<longlonglongrightarrow> c'"
  proof (rule Lim_transform_eventually)
    show "(\<lambda>n. ereal (norm (f n) powr (1 / real n))) \<longlonglongrightarrow> c'"
      using assms by simp
    show "\<forall>\<^sub>F x in sequentially. ereal (norm (f x) powr (1 / real x)) = 
                                ereal (root x (norm (f x)))"
      using eventually_gt_at_top[of 0] 
    proof eventually_elim
      case (elim n)
      show ?case using elim
        by (cases "f n = 0") (simp_all add: root_powr_inverse)
    qed
  qed
  thus ?thesis
    unfolding conv_radius_def using assms by (simp add: limsup_root_limit)
qed

lemma conv_radius_powr_real: "conv_radius (\<lambda>n. real n powr a) = 1"
proof (rule tendsto_imp_conv_radius_eq)
  have "(\<lambda>n. ereal ((real n powr a) powr (1 / real n))) \<longlonglongrightarrow> ereal 1"
    by (rule tendsto_ereal) real_asymp
  thus "(\<lambda>n. ereal (norm (real n powr a) powr (1 / real n))) \<longlonglongrightarrow> ereal 1"
    by simp
qed (simp_all add: one_ereal_def)

lemma conv_radius_one_over: "conv_radius (\<lambda>n. 1 / of_nat n :: 'a :: {real_normed_field, banach}) = 1"
proof (rule tendsto_imp_conv_radius_eq)
  have "(\<lambda>n. ereal ((1 / n) powr (1 / real n))) \<longlonglongrightarrow> ereal 1"
    by (rule tendsto_ereal) real_asymp
  thus "(\<lambda>n. ereal (norm (1 / of_nat n :: 'a) powr (1 / real n))) \<longlonglongrightarrow> ereal 1"
    by (simp add: norm_divide)
qed (simp_all add: one_ereal_def)

lemma conv_radius_mono:
  assumes "eventually (\<lambda>n. norm (f n) \<ge> norm (g n)) sequentially"
  shows   "conv_radius f \<le> conv_radius g"
  unfolding conv_radius_def
proof (rule ereal_inverse_antimono[OF _ Limsup_mono])
  have "limsup (\<lambda>n. 0) \<le> limsup (\<lambda>n. ereal (root n (norm (g n))))"
    by (rule Limsup_mono) (auto intro!: eventually_mono[OF eventually_gt_at_top[of 0]])
  thus "limsup (\<lambda>n. ereal (root n (norm (g n)))) \<ge> 0"
    by (simp add: Limsup_const)
next
  show "\<forall>\<^sub>F x in sequentially. ereal (root x (norm (g x))) \<le> ereal (root x (norm (f x)))"
    using assms eventually_gt_at_top[of 0] by eventually_elim auto
qed

lemma conv_radius_const [simp]:
  assumes "c \<noteq> 0"
  shows   "conv_radius (\<lambda>_. c) = 1"
proof (rule tendsto_imp_conv_radius_eq)
  show "(\<lambda>n. ereal (norm c powr (1 / real n))) \<longlonglongrightarrow> ereal 1"
    by (rule tendsto_ereal) (use assms in real_asymp)
qed auto

lemma conv_radius_bigo_polynomial:
  assumes "f \<in> O(\<lambda>n. of_nat n ^ k)"
  shows   "conv_radius f \<ge> 1"
proof -
  from assms obtain C where ev: "C > 0" "eventually (\<lambda>n. norm (f n) \<le> C * real n ^ k) at_top"
    by (elim landau_o.bigE) (auto simp: norm_power)
  have "(\<lambda>x. (C * real x ^ k) powr (1 / real x)) \<longlonglongrightarrow> 1"
    using ev(1) by real_asymp
  hence "conv_radius (\<lambda>n. C * real n ^ k) = inverse (ereal 1)" using ev(1)
    by (intro tendsto_imp_conv_radius_eq[OF _ refl] tendsto_ereal)
       (simp add: norm_mult norm_power abs_mult)
  moreover have "conv_radius (\<lambda>n. C * real n ^ k) \<le> conv_radius f"
    by (intro conv_radius_mono eventually_mono[OF ev(2)]) auto
  ultimately show ?thesis
    by (simp add: one_ereal_def)
qed


subsection \<open>Limits\<close>

lemma oscillation_imp_not_tendsto:
  assumes "eventually (\<lambda>n. f (g n) \<in> A) sequentially" "filterlim g F sequentially"
  assumes "eventually (\<lambda>n. f (h n) \<in> B) sequentially" "filterlim h F sequentially"
  assumes "closed A" "closed B" "A \<inter> B = {}"
  shows   "\<not>filterlim f (nhds c) F"
proof
  assume *: "filterlim f (nhds c) F"
  have "filterlim (\<lambda>n. f (g n)) (nhds c) sequentially"
    using * assms(2) by (rule filterlim_compose)
  with assms(1,5) have "c \<in> A"
    by (metis Lim_in_closed_set sequentially_bot)
  have "filterlim (\<lambda>n. f (h n)) (nhds c) sequentially"
    using * assms(4) by (rule filterlim_compose)
  with assms(3,6) have "c \<in> B"
    by (metis Lim_in_closed_set sequentially_bot)
  with \<open>c \<in> A\<close> and \<open>A \<inter> B = {}\<close> show False
    by blast
qed

lemma oscillation_imp_not_convergent:
  assumes "frequently (\<lambda>n. f n \<in> A) sequentially"
  assumes "frequently (\<lambda>n. f n \<in> B) sequentially"
  assumes "closed A" "closed B" "A \<inter> B = {}"
  shows   "\<not>convergent f"
proof -
  obtain g :: "nat \<Rightarrow> nat" where g: "strict_mono g" "\<And>n. f (g n) \<in> A"
    using assms(1) infinite_enumerate
    unfolding cofinite_eq_sequentially [symmetric] INFM_iff_infinite
    by blast
  obtain h :: "nat \<Rightarrow> nat" where h: "strict_mono h" "\<And>n. f (h n) \<in> B"
    using assms(2) infinite_enumerate
    unfolding cofinite_eq_sequentially [symmetric] INFM_iff_infinite
    by blast
  have "\<not>f \<longlonglongrightarrow> L" for L
  proof (rule oscillation_imp_not_tendsto)
    show "\<forall>\<^sub>F n in sequentially. f (g n) \<in> A" "\<forall>\<^sub>F n in sequentially. f (h n) \<in> B"
      using g h by auto
  qed (use g h assms in \<open>auto intro: filterlim_subseq\<close>)
  thus ?thesis
    unfolding convergent_def by blast
qed

lemma seq_bigo_1_iff:
  "g \<in> O(\<lambda>_::nat. 1) \<longleftrightarrow> bounded (range g)"
proof
  assume "g \<in> O(\<lambda>_. 1)"
  then obtain C where"eventually (\<lambda>n. norm (g n) \<le> C) at_top"
    by (elim landau_o.bigE) auto
  then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> norm (g n) \<le> C" 
    by (auto simp: eventually_at_top_linorder)
  hence "norm (g n) \<le> Max (insert C (norm ` g ` {..<N}))" for n
    by (cases "n < N") (auto simp: Max_ge_iff)
  thus "bounded (range g)"
    by (auto simp: bounded_iff)
next
  assume "bounded (range g)"
  then obtain C where "norm (g n) \<le> C" for n
    by (auto simp: bounded_iff)
  thus "g \<in> O(\<lambda>_. 1)"
    by (intro bigoI[where c = C]) auto
qed

lemma incseq_convergent':
  assumes "incseq (g :: nat \<Rightarrow> real)" "g \<in> O(\<lambda>_. 1)"
  shows   "convergent g"
proof -
  from assms(2) have "bounded (range g)"
    by (simp add: seq_bigo_1_iff)
  then obtain C where C: "\<bar>g n\<bar> \<le> C" for n
    unfolding bounded_iff by auto
  show ?thesis
  proof (rule incseq_convergent)
    show "incseq g"
      by fact
  next
    have "g i \<le> C" for i :: nat
      using C[of i] by auto
    thus "\<forall>i. g i \<le> C"
      by blast
  qed (auto simp: convergent_def)
qed

lemma decseq_convergent':
  assumes "decseq (g :: nat \<Rightarrow> real)" "g \<in> O(\<lambda>_. 1)"
  shows   "convergent g"
  using incseq_convergent'[of "\<lambda>n. -g n "] assms
  by (simp flip: convergent_minus_iff add: decseq_eq_incseq)

lemma filterlim_of_int_iff:
  fixes c :: "'a :: real_normed_algebra_1"
  assumes "F \<noteq> bot"
  shows "filterlim (\<lambda>x. of_int (f x)) (nhds c) F \<longleftrightarrow>
           (\<exists>c'. c = of_int c' \<and> eventually (\<lambda>x. f x = c') F)"
proof
  assume "\<exists>c'. c = of_int c' \<and> eventually (\<lambda>x. f x = c') F"
  then obtain c' where c': "c = of_int c'" "eventually (\<lambda>x. f x = c') F"
    by blast
  from c'(2) have "eventually (\<lambda>x. of_int (f x) = c) F"
    by eventually_elim (auto simp: c'(1))
  thus "filterlim (\<lambda>x. of_int (f x)) (nhds c) F"
    by (rule tendsto_eventually)    
next
  assume *: "filterlim (\<lambda>x. of_int (f x)) (nhds c) F"
  show "(\<exists>c'. c = of_int c' \<and> eventually (\<lambda>x. f x = c') F)"
  proof (cases "c \<in> \<int>")
    case False
    hence "setdist {c} \<int> > 0"
      by (subst setdist_gt_0_compact_closed) auto
    with * have "eventually (\<lambda>x. dist (of_int (f x)) c < setdist {c} \<int>) F"
      unfolding tendsto_iff by blast
    then obtain x where "dist (of_int (f x)) c < setdist {c} \<int>"
      using \<open>F \<noteq> bot\<close> eventually_happens by blast
    moreover have "dist c (of_int (f x)) \<ge> setdist {c} \<int>"
      by (rule setdist_le_dist) auto
    ultimately show ?thesis
      by (simp add: dist_commute)
  next
    case True
    then obtain c' where c: "c = of_int c'"
      by (elim Ints_cases)
    have "eventually (\<lambda>x. dist (of_int (f x)) c < 1) F"
      using * unfolding tendsto_iff by auto
    hence "eventually (\<lambda>x. f x = c') F"
      by eventually_elim (auto simp: c dist_of_int)
    with c show ?thesis
      by auto
  qed
qed

lemma filterlim_of_nat_iff:
  fixes c :: "'a :: real_normed_algebra_1"
  assumes "F \<noteq> bot"
  shows "filterlim (\<lambda>x. of_nat (f x)) (nhds c) F \<longleftrightarrow>
           (\<exists>c'. c = of_nat c' \<and> eventually (\<lambda>x. f x = c') F)"
proof
  assume "\<exists>c'. c = of_nat c' \<and> eventually (\<lambda>x. f x = c') F"
  then obtain c' where c': "c = of_nat c'" "eventually (\<lambda>x. f x = c') F"
    by blast
  from c'(2) have "eventually (\<lambda>x. of_nat (f x) = c) F"
    by eventually_elim (auto simp: c'(1))
  thus "filterlim (\<lambda>x. of_nat (f x)) (nhds c) F"
    by (rule tendsto_eventually)    
next
  assume *: "filterlim (\<lambda>x. of_nat (f x)) (nhds c) F"
  show "(\<exists>c'. c = of_nat c' \<and> eventually (\<lambda>x. f x = c') F)"
  proof (cases "c \<in> \<nat>")
    case False
    hence "setdist {c} \<nat> > 0"
      by (subst setdist_gt_0_compact_closed) auto
    with * have "eventually (\<lambda>x. dist (of_nat (f x)) c < setdist {c} \<nat>) F"
      unfolding tendsto_iff by blast
    then obtain x where "dist (of_nat (f x)) c < setdist {c} \<nat>"
      using \<open>F \<noteq> bot\<close> eventually_happens by blast
    moreover have "dist c (of_nat (f x)) \<ge> setdist {c} \<nat>"
      by (rule setdist_le_dist) auto
    ultimately show ?thesis
      by (simp add: dist_commute)
  next
    case True
    then obtain c' where c: "c = of_nat c'"
      by (elim Nats_cases)
    have "eventually (\<lambda>x. dist (of_nat (f x)) c < 1) F"
      using * unfolding tendsto_iff by auto
    hence "eventually (\<lambda>x. f x = c') F"
      by eventually_elim (auto simp: c dist_of_nat)
    with c show ?thesis
      by auto
  qed
qed

lemma uniform_limit_compose:
  assumes "uniform_limit B (\<lambda>x y. f x y) (\<lambda>y. f' y) F" "\<And>y. y \<in> A \<Longrightarrow> g y \<in> B"
  shows   "uniform_limit A (\<lambda>x y. f x (g y)) (\<lambda>y. f' (g y)) F"
proof -
  have "uniform_limit (g ` A) (\<lambda>x y. f x y) (\<lambda>y. f' y) F"
    using assms(1) by (rule uniform_limit_on_subset) (use assms(2) in blast)
  thus "uniform_limit A (\<lambda>x y. f x (g y)) (\<lambda>y. f' (g y)) F"
    unfolding uniform_limit_iff by auto
qed

lemma uniform_limit_const':
  assumes "filterlim f (nhds c) F"
  shows   "uniform_limit A (\<lambda>x y. f x) (\<lambda>y. c) F"
proof -
  have "\<forall>\<^sub>F n in F. \<forall>x\<in>A. dist (f n) c < \<epsilon>" if \<epsilon>: "\<epsilon> > 0" for \<epsilon> :: real
  proof -
    from assms and \<epsilon> have "\<forall>\<^sub>F n in F. dist (f n) c < \<epsilon>"
      unfolding tendsto_iff by blast
    thus ?thesis
      by eventually_elim auto
  qed
  thus ?thesis
    unfolding uniform_limit_iff by blast
qed

lemma uniform_limit_singleton_iff [simp]:
  "uniform_limit {x} f g F \<longleftrightarrow> filterlim (\<lambda>y. f y x) (nhds (g x)) F"
  by (simp add: uniform_limit_iff tendsto_iff)

end