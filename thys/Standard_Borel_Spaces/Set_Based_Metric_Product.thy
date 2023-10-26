(*  Title:   Set_Based_Metric_Product.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

subsubsection \<open> Product Metric Spaces \<close>

theory Set_Based_Metric_Product
  imports Set_Based_Metric_Space
begin

lemma nsum_of_r':
  fixes r :: real
  assumes r:"0 < r" "r < 1"
  shows "(\<Sum>n. r^(n + k) * K) = r^k / (1 - r) * K"
 (is "?lhs = _")
proof -
  have "?lhs = (\<Sum>n. r^n * K) - (\<Sum>n\<in>{..<k}. r^n * K)"
    using r by(auto intro!: suminf_minus_initial_segment summable_mult2)
  also have "... = 1 / (1 - r) * K - (1 - r^k) / (1 - r) * K"
  proof -
    have "(\<Sum>n\<in>{..<k}. r^n * K) = (1 - r^k) / (1 - r) * K"
      using one_diff_power_eq[of r k] r scale_sum_left[of "\<lambda>n. r^n" "{..<k}" K,symmetric]
      by auto
    thus ?thesis
      using r by(auto simp add: suminf_geometric[of "r"] suminf_mult2[where c=K,symmetric])
  qed
  finally show ?thesis
    using r by (simp add: diff_divide_distrib left_diff_distrib)
qed

lemma nsum_of_r_leq:
  fixes r :: real and a :: "nat \<Rightarrow> real"
  assumes r:"0 < r" "r < 1"
      and a:"\<And>n. 0 \<le> a n" "\<And>n. a n \<le> K"
    shows "0 \<le> (\<Sum>n. r^(n + k) * a (n + l))" "(\<Sum>n. r^(n + k) * a (n + l)) \<le> r^k / (1 - r) * K"
proof -
  have [simp]: "summable (\<lambda>n. r ^ (n + k) * a (n + l))"
    apply(rule summable_comparison_test'[of "\<lambda>n. r^(n+k) * K"])
    using r a by(auto intro!: summable_mult2)
  show "0 \<le> (\<Sum>n. r^(n + k) * a (n + l))"
    using r a by(auto intro!: suminf_nonneg)
  have "(\<Sum>n. r^(n + k) * a (n + l)) \<le> (\<Sum>n. r^(n + k) * K)"
    using a r by(auto intro!: suminf_le summable_mult2)
  also have "... = r^k / (1 - r) * K"
    by(rule nsum_of_r'[OF r])
  finally show "(\<Sum>n. r^(n + k) * a (n + l)) \<le> r^k / (1 - r) * K" .
qed

lemma nsum_of_r_le:
  fixes r :: real and a :: "nat \<Rightarrow> real"
  assumes r:"0 < r" "r < 1"
      and a:"\<And>n. 0 \<le> a n" "\<And>n. a n \<le> K" "\<exists>n'\<ge> l. a n' < K"
    shows "(\<Sum>n. r^(n + k) * a (n + l)) < r^k / (1 - r) * K"
proof -
  obtain n' where hn': "a (n' + l) < K"
    using a(3) by (metis add.commute le_iff_add)
  define a' where "a' = (\<lambda>n. if n = n' + l then K else a n)"
  have a': "\<And>n. 0 \<le> a' n" "\<And>n. a' n \<le> K"
    using a(1,2) le_trans order.trans[OF a(1,2)[of 0]] by(auto simp: a'_def)
  have [simp]: "summable (\<lambda>n. r ^ (n + k) * a (n + l))"
    apply(rule summable_comparison_test'[of "\<lambda>n. r^(n+k) * K"])
    using r a by(auto intro!: summable_mult2)
  have [simp]: "summable (\<lambda>n. r^(n + k) * a' (n + l))"
    apply(rule summable_comparison_test'[of "\<lambda>n. r^(n+k) * K"])
    using r a' by(auto intro!: summable_mult2)
  have "(\<Sum>n. r^(n + k) * a (n + l)) = (\<Sum>n. r^(n + Suc n' + k) * a (n + Suc n'+ l)) + (\<Sum>i<Suc n'. r^(i + k) * a (i + l))"
    by(rule suminf_split_initial_segment) simp
  also have "... = (\<Sum>n. r^(n + Suc n' + k) * a (n + Suc n'+ l)) + (\<Sum>i<n'. r^(i + k) * a (i + l)) + r^(n' + k) * a (n' + l)"
    by simp
  also have "... < (\<Sum>n. r^(n + Suc n' + k) * a (n + Suc n'+ l)) + (\<Sum>i<n'. r^(i + k) * a (i + l)) + r^(n' + k) * K"
    using r hn' by auto
  also have "... = (\<Sum>n. r^(n + Suc n' + k) * a' (n + Suc n'+ l)) + (\<Sum>i<Suc n'. r^(i + k) * a' (i + l))"
    by(auto simp: a'_def)
  also have "... = (\<Sum>n. r^(n + k) * a' (n + l))"
    by(rule suminf_split_initial_segment[symmetric]) simp
  also have "... \<le> r^k / (1 - r) * K"
    by(rule nsum_of_r_leq[OF r a'])
  finally show ?thesis .
qed

definition product_dist' :: "[real, 'i set, nat \<Rightarrow> 'i, 'i \<Rightarrow> 'a set, 'i \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real] \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> real" where
product_dist_def: "product_dist' r I g Mi di \<equiv> (\<lambda>x y. if x \<in> (\<Pi>\<^sub>E i\<in>I. Mi i) \<and> y \<in> (\<Pi>\<^sub>E i\<in>I. Mi i) then (\<Sum>n. if g n \<in> I then r^n * di (g n) (x (g n)) (y (g n)) else 0) else 0)"

text \<open> $d(x,y) = \sum_{n\in \mathbb{N}} r^n * d_{g_I(i)}(x_{g_I(i)},y_{g_I(i)})$.\<close>
locale Product_metric = 
  fixes r :: real
    and I :: "'i set"
    and f :: "'i \<Rightarrow> nat"
    and g :: "nat \<Rightarrow> 'i"
    and Mi :: "'i \<Rightarrow> 'a set"
    and di :: "'i \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real"
    and K :: real
  assumes r: "0 < r" "r < 1"
      and I: "countable I"
      and gf_comp_id : "\<And>i. i \<in> I \<Longrightarrow> g (f i) = i"
      and gf_if_finite: "finite I \<Longrightarrow> bij_betw f I {..< card I}"
                        "finite I \<Longrightarrow> bij_betw g {..< card I} I"
      and gf_if_infinite: "infinite I \<Longrightarrow> bij_betw f I UNIV"
                          "infinite I \<Longrightarrow> bij_betw g UNIV I"
                          "\<And>n. infinite I \<Longrightarrow> f (g n) = n"
      and Md_metric: "\<And>i. i \<in> I \<Longrightarrow> Metric_space (Mi i) (di i)"
      and di_nonneg: "\<And>i x y. 0 \<le> di i x y"
      and di_bounded: "\<And>i x y. di i x y \<le> K"
      and K_pos : "0 < K"

lemma from_nat_into_to_nat_on_product_metric_pair:
  assumes "countable I"
  shows "\<And>i. i \<in> I \<Longrightarrow> from_nat_into I (to_nat_on I i) = i"
    and "finite I \<Longrightarrow> bij_betw (to_nat_on I) I {..< card I}"
    and "finite I \<Longrightarrow> bij_betw (from_nat_into I) {..< card I} I"
    and "infinite I \<Longrightarrow> bij_betw (to_nat_on I) I UNIV"
    and "infinite I \<Longrightarrow> bij_betw (from_nat_into I) UNIV I"
    and "\<And>n. infinite I \<Longrightarrow> to_nat_on I (from_nat_into I n) = n"
  by(simp_all add: assms to_nat_on_finite bij_betw_from_nat_into_finite to_nat_on_infinite bij_betw_from_nat_into)

lemma product_metric_pair_finite_nat:
 "bij_betw id {..n} {..< card {..n}}" "bij_betw id {..< card {..n}} {..n}"
  by(auto simp: bij_betw_def)

lemma product_metric_pair_finite_nat':
 "bij_betw id {..<n} {..< card {..<n}}" "bij_betw id {..< card {..<n}} {..<n}"
  by(auto simp: bij_betw_def)

context Product_metric
begin

abbreviation "product_dist \<equiv> product_dist' r I g Mi di"

lemma nsum_of_rK: "(\<Sum>n. r^(n + k)*K) = r^k / (1 - r) * K"
  by(rule nsum_of_r'[OF r])

lemma i_min:
  assumes "i \<in> I" "g n = i"
  shows "f i \<le> n"
proof(cases "finite I")
  case h:True
  show ?thesis
  proof(rule ccontr)
    assume "\<not> f i \<le> n"
    then have h0:"n < f i" by simp
    have "f i \<in> {..<card I}"
      using  bij_betwE[OF gf_if_finite(1)[OF h]] assms(1) by simp
    moreover have "n \<in> {..<card I}" "n \<noteq> f i"
      using h0 \<open>f i \<in> {..<card I}\<close> by auto
    ultimately have "g n \<noteq> g (f i)"
      using bij_betw_imp_inj_on[OF gf_if_finite(2)[OF h]]
      by (simp add: inj_on_contraD)
    thus False
      by(simp add: gf_comp_id[OF assms(1)] assms(2))
  qed
next
  show "infinite I \<Longrightarrow> f i \<le> n"
    using assms(2) gf_if_infinite(3)[of n] by simp
qed

lemma g_surj:
  assumes "i \<in> I"
  shows "\<exists>n. g n = i"
  using gf_comp_id[of i] assms by auto

lemma product_dist_summable'[simp]:
  "summable (\<lambda>n. r^n * di (g n) (x (g n)) (y (g n)))"
  apply(rule summable_comparison_test'[of "\<lambda>n. r^n * K"])
  using r di_nonneg di_bounded K_pos by(auto intro!: summable_mult2)

lemma product_dist_summable[simp]:
  "summable (\<lambda>n. if g n \<in> I then r^n * di (g n) (x (g n)) (y (g n)) else 0)"
  by(rule summable_comparison_test'[of "\<lambda>n. r^n * di (g n) (x (g n)) (y (g n))"]) (use r di_nonneg di_bounded K_pos in auto)

lemma summable_rK[simp]: "summable (\<lambda>n. r^n * K)"
  using r by(auto intro!: summable_mult2)

lemma Product_metric: "Metric_space (\<Pi>\<^sub>E i\<in>I. Mi i) product_dist"
proof -
  have h': "\<And>i xi yi. i \<in> I \<Longrightarrow> xi \<in> Mi i \<Longrightarrow> yi \<in> Mi i \<Longrightarrow> xi = yi \<longleftrightarrow> di i xi yi = 0"
           "\<And>i xi yi. i \<in> I \<Longrightarrow> di i xi yi = di i yi xi"
           "\<And>i xi yi zi. i \<in> I \<Longrightarrow> xi \<in> Mi i \<Longrightarrow> yi \<in> Mi i \<Longrightarrow> zi \<in> Mi i \<Longrightarrow> di i xi zi \<le> di i xi yi + di i yi zi"
    using Md_metric by(auto simp: Metric_space_def)
  show ?thesis
  proof
    show "\<And>x y. 0 \<le> product_dist x y"
      using di_nonneg r by(auto simp: product_dist_def intro!: suminf_nonneg product_dist_summable)
  next
    fix x y
    assume hxy:"x \<in> (\<Pi>\<^sub>E i\<in>I. Mi i)" "y \<in> (\<Pi>\<^sub>E i\<in>I. Mi i)"
    show "(product_dist x y = 0) \<longleftrightarrow> (x = y)"
    proof
      assume heq:"x = y"
      then have "(if g n \<in> I then r ^ n * di (g n) (x (g n)) (y (g n)) else 0) = 0" for n
        using hxy h'(1)[of "g n" "x (g n)" "y (g n)"] by(auto simp: product_dist_def)
      thus "product_dist x y = 0"
        by(auto simp: product_dist_def)
    next
      assume h0:"product_dist x y = 0"
      have "(\<Sum>n. if g n \<in> I then r ^ n * di (g n) (x (g n)) (y (g n)) else 0) = 0
                     \<longleftrightarrow> (\<forall>n. (if g n \<in> I then r^n * di (g n) (x (g n)) (y (g n)) else 0) = 0)"
        apply(rule suminf_eq_zero_iff)
        using di_nonneg r by(auto simp: product_dist_def intro!: product_dist_summable)
      hence hn0:"\<And>n. (if g n \<in> I then r^n * di (g n) (x (g n)) (y (g n)) else 0) = 0"
        using h0 hxy by(auto simp: product_dist_def)
      show "x = y"
      proof
        fix i
        consider "i \<in> I" | "i \<notin> I" by auto
        thus "x i = y i"
        proof cases
          case 1
          from g_surj[OF this] obtain n where 
           hn: "g n = i" by auto
          have "di (g n) (x (g n)) (y (g n)) = 0"
            using hn h'(1)[OF 1,of "x i" "y i"] hxy hn0[of n] 1 r by simp
          thus ?thesis
            using hn h'(1)[OF 1,of "x i" "y i"] hxy 1 by auto
        next
          case 2
          then show ?thesis
           by(simp add: PiE_arb[OF hxy(1) 2] hxy PiE_arb[OF hxy(2) 2])
        qed
      qed
    qed
  next
    show "product_dist x y = product_dist y x" for x y
      using h'(2) by(auto simp: product_dist_def) (metis (no_types, opaque_lifting))
  next
    fix x y z
    assume hxyz:"x \<in> (\<Pi>\<^sub>E i\<in>I. Mi i)" "y \<in> (\<Pi>\<^sub>E i\<in>I. Mi i)" "z \<in> (\<Pi>\<^sub>E i\<in>I. Mi i)"
    have "(if g n \<in> I then r ^ n * di (g n) (x (g n)) (z (g n)) else 0) 
           \<le> (if g n \<in> I then r ^ n * di (g n) (x (g n)) (y (g n)) else 0) + (if g n \<in> I then r ^ n * di (g n) (y (g n)) (z (g n)) else 0)" for n
      using h'(3)[of "g n" "x (g n)" "y (g n)" "z (g n)"] hxyz r
      by(auto simp: distrib_left[of "r ^ n",symmetric])
    thus "product_dist x z \<le> product_dist x y + product_dist y z"
    by(auto simp add: product_dist_def suminf_add[OF product_dist_summable[of x y] product_dist_summable[of y z]] hxyz intro!: suminf_le summable_add)
  qed
qed

sublocale Product_metric: Metric_space "\<Pi>\<^sub>E i\<in>I. Mi i" "product_dist"
  by(rule Product_metric)

lemma product_dist_leqr: "product_dist x y \<le> 1 / (1 - r) * K"
proof -
  have "product_dist x y \<le> (\<Sum>n. if g n \<in> I then r^n * di (g n) (x (g n)) (y (g n)) else 0)"
  proof -
    consider "x \<in> (\<Pi>\<^sub>E i\<in>I. Mi i) \<and> y \<in> (\<Pi>\<^sub>E i\<in>I. Mi i)" | "\<not> (x \<in> (\<Pi>\<^sub>E i\<in>I. Mi i) \<and> y \<in> (\<Pi>\<^sub>E i\<in>I. Mi i))" by auto
    then show ?thesis
    proof cases
      case 1
      then show ?thesis by(auto simp: product_dist_def)
    next
      case 2
      then have "product_dist x y = 0"
        by(auto simp: product_dist_def)
      also have "... \<le> (\<Sum>n. if g n \<in> I then r^n * di (g n) (x (g n)) (y (g n)) else 0)"
        using di_nonneg r by(auto intro!: suminf_nonneg product_dist_summable)
      finally show ?thesis .
    qed
  qed
  also have "... \<le> (\<Sum>n. r^n * di (g n) (x (g n)) (y (g n)))"
   using r di_nonneg di_bounded by(auto intro!: suminf_le)
  also have "... \<le> (\<Sum>n. r^n * K)"
    using r di_bounded di_nonneg by(auto intro!: suminf_le)
  also have "... = 1 / (1 - r) * K"
    using r nsum_of_rK[of 0] by simp
  finally show ?thesis .
qed

lemma product_dist_geq:
  assumes "i \<in> I" and "g n = i" "x \<in> (\<Pi>\<^sub>E i\<in>I. Mi i)" "y \<in> (\<Pi>\<^sub>E i\<in>I. Mi i)"
    shows "di i (x i) (y i) \<le> (1/r)^n * product_dist x y"
          (is "?lhs \<le> ?rhs")
proof -
  interpret mi: Metric_space "Mi i" "di i"
    by(rule Md_metric[OF assms(1)])
  have "(\<lambda>m. if m = f i then di (g m) (x (g m)) (y (g m)) else 0) sums di (g (f i)) (x (g (f i))) (y (g (f i)))"
    by(rule sums_single)
  also have "... = ?lhs"
    by(simp add: gf_comp_id[OF assms(1)])
  finally have 1:"summable (\<lambda>m. if m = f i then di (g m) (x (g m)) (y (g m)) else 0)"
                 "?lhs = (\<Sum>m. (if m = f i then di (g m) (x (g m)) (y (g m)) else 0))"
    by(auto simp: sums_iff)
  note 1(2)
  also have "... \<le> (\<Sum>m. (1/r)^n * (if g m \<in> I then r^m * di (g m) (x (g m)) (y (g m)) else 0))"
  proof(rule suminf_le)
    show "summable (\<lambda>m. (1/r)^n * (if g m \<in> I then r^m * di (g m) (x (g m)) (y (g m)) else 0))"
      by(auto intro!: product_dist_summable)
  next
    fix k
    have **:"1 \<le> (1/r) ^ n * r ^ f i"
    proof -
      have "(1/r) ^ n * (r ^ f i) = (1/r)^(n-f i) * (1/r)^(f i) * r ^ f i"
        using r by(simp add: power_diff[OF _ i_min[OF assms(1,2)],of "1/r",simplified])
      also have "... = (1/r) ^ (n-f i)"
        using r by (simp add: power_one_over)
      finally show ?thesis
        using r by auto
    qed
    have *:"g k \<in> I" if "k = f i"
      using gf_comp_id[OF assms(1)] assms(1) that by auto
    show "(if k = f i then di (g k) (x (g k)) (y (g k)) else 0) \<le> (1/r) ^ n * (if g k \<in> I then r ^ k * di (g k) (x (g k)) (y (g k)) else 0)"
      using * di_nonneg r ** mult_right_mono[OF **] by(auto simp: vector_space_over_itself.scale_scale[of "(1 / r) ^ n"])
  qed(simp add: 1)
  also have "... = ?rhs"
    unfolding product_dist_def
    using assms by(auto intro!: suminf_mult product_dist_summable)
  finally show ?thesis .
qed

lemma limitin_M_iff_limitin_Mi:
  shows "limitin Product_metric.mtopology xn x sequentially \<longleftrightarrow> (\<exists>N. \<forall>n\<ge>N. (\<forall>i\<in>I.  xn n i \<in> Mi i) \<and> (\<forall>i. i\<notin>I \<longrightarrow> xn n i = undefined)) \<and> (\<forall>i\<in>I. limitin (Metric_space.mtopology (Mi i) (di i)) (\<lambda>n. xn n i) (x i) sequentially) \<and> x \<in> (\<Pi>\<^sub>E i\<in>I. Mi i)"
proof safe
  fix i
  assume h:"limitin Product_metric.mtopology xn x sequentially"
  then show "\<exists>N. \<forall>n\<ge>N. (\<forall>i\<in>I.  xn n i \<in> Mi i) \<and> (\<forall>i. i\<notin>I \<longrightarrow> xn n i = undefined)"
    by(simp only: Product_metric.limit_metric_sequentially) (metis PiE_E r(1))
  then obtain N' where N': "\<And>i n. i \<in> I \<Longrightarrow> n \<ge> N' \<Longrightarrow> xn n i \<in> Mi i" "\<And>i n. i \<notin> I \<Longrightarrow> n \<ge> N' \<Longrightarrow> xn n i = undefined"
    by blast
  assume i:"i \<in> I"
  then interpret m: Metric_space "Mi i" "di i"
    using Md_metric by blast
  show "limitin m.mtopology (\<lambda>n. xn n i) (x i) sequentially"
    unfolding m.limitin_metric eventually_sequentially
  proof safe
    show "x i \<in> Mi i"
      using h i by(auto simp: Product_metric.limitin_metric)
  next
    fix \<epsilon> :: real
    assume "0 < \<epsilon>"
    then obtain "r^ f i * \<epsilon> > 0" using r by auto
    then obtain N where N:"\<And>n. n \<ge> N \<Longrightarrow> product_dist (xn n) x < r^ f i * \<epsilon>"
      using h(1) by(fastforce simp: Product_metric.limitin_metric eventually_sequentially)
    show "\<exists>N. \<forall>n\<ge>N. xn n i \<in> Mi i \<and> di i (xn n i) (x i) < \<epsilon>"
    proof(safe intro!: exI[where x="max N N'"])
      fix n
      assume "max N N' \<le> n"
      then have "N \<le> n" "N' \<le> n"
        by auto
      have "di i (xn n i) (x i) \<le> (1 / r) ^ f i * product_dist (xn n) x"
        thm product_dist_geq[OF i gf_comp_id[OF i] ]
        using h i N'[OF _ \<open>N' \<le> n\<close>] by(auto intro!: product_dist_geq[OF i gf_comp_id[OF i] ] dest: Product_metric.limitin_mspace)
      also have "... < (1 / r) ^ f i * r^ f i * \<epsilon>"
        using N[OF \<open>N \<le> n\<close>] r by auto
      also have "... \<le> \<epsilon>"
        by (simp add: \<open>0 < \<epsilon>\<close> power_one_over)
      finally show "di i (xn n i) (x i) < \<epsilon>" .
    qed(use N' h i in auto)
  qed
next
  fix N'
  assume N': "\<forall>n\<ge>N'. (\<forall>i\<in>I. xn n i \<in> Mi i) \<and> (\<forall>i. i \<notin> I \<longrightarrow> xn n i = undefined)"
  assume h:"\<forall>i\<in>I. limitin (Metric_space.mtopology (Mi i) (di i)) (\<lambda>n. xn n i) (x i) sequentially" "x \<in> (\<Pi>\<^sub>E i\<in>I. Mi i)"
  show "limitin Product_metric.mtopology xn x sequentially"
    unfolding Product_metric.limitin_metric eventually_sequentially
  proof safe
    fix \<epsilon>
    assume he:"(0::real) < \<epsilon>"
    then have "0 < \<epsilon>*((1-r)/K)" using r K_pos by auto
    hence "\<exists>k. r^k < \<epsilon>*((1-r)/K)"
      using r(2) real_arch_pow_inv by blast
    then obtain l where "r^l < \<epsilon>*((1-r)/K)" by auto
    hence hk:"r^l/(1-r)*K < \<epsilon>"
      using mult_imp_div_pos_less[OF divide_pos_pos[OF _ K_pos,of "1-r"]] r(2) by simp
    hence hke: "0 < \<epsilon> - r^l/(1-r)*K" by auto
    consider "l = 0" | "0 < l" by auto
    then show "\<exists>N. \<forall>n\<ge>N. xn n \<in> (\<Pi>\<^sub>E i\<in>I. Mi i) \<and> product_dist (xn n) x < \<epsilon>"
    proof cases
      case 1
      then have he2:"1 / (1 - r)*K < \<epsilon>" using hk by auto
      show ?thesis
        using order.strict_trans1[OF product_dist_leqr he2] N'
        by(auto intro!: exI[where x=N'])
    next
      case 2
      with hke have "0 < 1 / real l * (\<epsilon> - r^l/(1-r)*K)" by auto
      hence "\<forall>i\<in>I. \<exists>N. \<forall>n\<ge>N. di i (xn n i) (x i) < 1 / real l * (\<epsilon> - r^l/(1-r)*K)"
        using h by (meson Md_metric Metric_space.limit_metric_sequentially)
      then obtain N where hn:
      "\<And>i n. i \<in> I \<Longrightarrow> n \<ge> N i \<Longrightarrow> di i (xn n i) (x i) < 1 / real l * (\<epsilon> - r^l/(1-r)*K)"
        by metis
      show ?thesis
      proof(safe intro!: exI[where x="max (Sup {N (g n) | n. n < l}) N'"])
        fix n
        assume "max (\<Squnion> {N (g n) |n. n < l}) N' \<le> n"
        then have hsup:"\<Squnion> {N (g n) |n. n < l} \<le> n" and N'n: "N' \<le> n"
          by auto
        have "product_dist (xn n) x = (\<Sum>m. if g m \<in> I then r ^ m * di (g m) (xn n (g m)) (x (g m)) else 0)"
          using N' N'n h by(auto simp: product_dist_def)
        also have "... = (\<Sum>m. if g (m + l) \<in> I then r ^ (m + l)* di (g (m + l)) (xn n (g (m + l))) (x (g (m + l))) else 0) + (\<Sum>m<l. if g m \<in> I then r ^ m * di (g m) (xn n (g m)) (x (g m)) else 0)"
          by(auto intro!: suminf_split_initial_segment)
        also have "... \<le> r^l/(1-r)*K + (\<Sum>m<l. if g m \<in> I then r ^ m * di (g m) (xn n (g m)) (x(g m)) else 0)"
        proof -
          have "(\<Sum>m. if g (m + l) \<in> I then r ^ (m + l)* di (g (m + l)) (xn n (g (m + l))) (x (g (m + l))) else 0) \<le> (\<Sum>m. r^(m + l)*K)"
            using di_bounded N' r K_pos by(auto intro!: suminf_le summable_ignore_initial_segment)
          also have "... = r^l/(1-r)*K"
            by(rule nsum_of_rK)
          finally show ?thesis by auto
        qed
        also have "... \<le> r^l / (1 - r)*K + (\<Sum>m<l. if g m \<in> I then di (g m) (xn n (g m)) (x (g m)) else 0)"
        proof -
          have " (\<Sum>m<l. if g m \<in> I then r ^ m * di (g m) (xn n (g m)) (x (g m))  else 0) \<le> (\<Sum>m<l. if g m \<in> I then di (g m) (xn n (g m)) (x (g m)) else 0)"
            using di_bounded di_nonneg r by(auto intro!: sum_mono simp: mult_left_le_one_le power_le_one)
          thus ?thesis by simp
        qed
        also have "... < r^l / (1 - r)*K + (\<Sum>m<l. 1 / real l * (\<epsilon> - r^l/(1-r)*K))"
        proof -
          have "(\<Sum>m<l. if g m \<in> I then di (g m) (xn n (g m)) (x (g m)) else 0) < (\<Sum>m<l. 1 / real l * (\<epsilon> - r^l/(1-r)*K))"
          proof(rule sum_strict_mono_ex1)
            show "\<forall>p\<in>{..<l}. (if g p \<in> I then di (g p) (xn n (g p)) (x (g p)) else 0) \<le> 1 / real l * (\<epsilon> - r ^ l / (1 - r)*K)"
            proof -
              have "0 \<le> (\<epsilon> - r ^ l * K / (1 - r)) / real l"
                using hke by auto
              moreover {
                fix p
                assume "p < l" "g p \<in> I"
                then have "N (g p) \<in> {N (g n) |n. n < l}"
                  by auto
                from le_cSup_finite[OF _ this] hsup have "N (g p) \<le> n"
                  by auto
                hence "di (g p) (xn n (g p)) (x (g p)) \<le> (\<epsilon> - r ^ l *K/ (1 - r)) / real l"
                  using hn[OF \<open>g p \<in> I\<close>,of n] by simp
              }
              ultimately show ?thesis
                by auto
            qed
          next
            show "\<exists>a\<in>{..<l}. (if g a \<in> I then di (g a) (xn n (g a)) (x (g a)) else 0) < 1 / real l * (\<epsilon> - r ^ l  / (1 - r)*K)"
            proof -
              have "0 < (\<epsilon> - r ^ l * K / (1 - r)) / real l"
                using hke 2 by auto
              moreover {
                assume "g 0 \<in> I"
                have "N (g 0) \<in> {N (g n) |n. n < l}"
                  using 2 by auto
                from le_cSup_finite[OF _ this] hsup have "N (g 0) \<le> n"
                  by auto
                hence "di (g 0) (xn n (g 0)) (x (g 0)) < (\<epsilon> - r ^ l * K/ (1 - r)) / real l"
                  using hn[OF \<open>g 0 \<in> I\<close>,of n] by simp
              }
              ultimately show ?thesis
                by(auto intro!: bexI[where x=0] simp: 2)
            qed
          qed simp
          thus ?thesis by simp
        qed
        also have "... = \<epsilon>"
          using 2 by auto
        finally show  "product_dist (xn n) x < \<epsilon>" .
      qed(use N' in auto)
    qed
  qed (use N' h in auto)
qed(auto simp: Product_metric.limitin_metric)

lemma Product_metric_mtopology_eq: "product_topology (\<lambda>i. Metric_space.mtopology (Mi i) (di i)) I = Product_metric.mtopology" 
proof -
  have htopspace:"\<And>i. i \<in> I \<Longrightarrow> topspace (Metric_space.mtopology (Mi i) (di i)) = Mi i"
    by (simp add: Md_metric Metric_space.topspace_mtopology)
  hence htopspace':"(\<Pi>\<^sub>E i\<in>I. topspace (Metric_space.mtopology (Mi i) (di i))) = (\<Pi>\<^sub>E i\<in>I. Mi i)" by auto
  consider "I = {}" | "I \<noteq> {}" by auto
  then show ?thesis
  proof cases
    case 1
    interpret d: discrete_metric "{\<lambda>x. undefined}" .
    have "product_dist  = (\<lambda>x y. 0)"
      by standard+ (auto simp: product_dist_def 1)
    hence 2:"Product_metric.mtopology = d.disc.mtopology"
      by (metis "1" PiE_empty_domain Product_metric.open_in_mspace Product_metric.topspace_mtopology d.mtopology_discrete_metric discrete_topology_unique singleton_iff)
    show ?thesis
      unfolding 2 by(simp add: product_topology_empty_discrete 1 d.mtopology_discrete_metric)
  next
    case I':2
    show ?thesis
      unfolding base_is_subbase[OF Product_metric.mtopology_base_in_balls,simplified subbase_in_def] product_topology_def
    proof(rule topology_generated_by_eq)
      fix U
      assume "U \<in> {Product_metric.mball a \<epsilon> |a \<epsilon>. a \<in> (\<Pi>\<^sub>E i\<in>I. Mi i) \<and> 0 < \<epsilon>}"
      then obtain a \<epsilon> where hu:
        "U = Product_metric.mball a \<epsilon>" "a \<in> (\<Pi>\<^sub>E i\<in>I. Mi i)" "0 < \<epsilon>" by auto
      have "\<exists>X. x \<in> (\<Pi>\<^sub>E i\<in>I. X i) \<and> (\<Pi>\<^sub>E i\<in>I. X i) \<subseteq> U \<and> (\<forall>i. openin (Metric_space.mtopology (Mi i) (di i)) (X i)) \<and> finite {i. X i \<noteq> topspace (Metric_space.mtopology (Mi i) (di i))}" if "x \<in> U" for x
      proof -
        consider "\<epsilon> \<le> 1 / (1 - r) * K" | "1 / (1 - r) * K < \<epsilon>" by fastforce
        then show "\<exists>X. x \<in> (\<Pi>\<^sub>E i\<in>I. X i) \<and> (\<Pi>\<^sub>E i\<in>I. X i) \<subseteq> U \<and>  (\<forall>i. openin (Metric_space.mtopology (Mi i) (di i)) (X i)) \<and>  finite {i. X i \<noteq> topspace (Metric_space.mtopology (Mi i) (di i))}"
        proof cases
          case he2:1
          have "0 < (\<epsilon> - product_dist a x)*((1-r)/ K)" using r hu K_pos that hu by auto
          hence "\<exists>k. r^k < (\<epsilon> - product_dist a x)*((1-r)/ K)"
            using r(2) real_arch_pow_inv by blast
          then obtain k where "r^k < (\<epsilon> - product_dist a x)*((1-r)/ K)" by auto
          hence hk:"r^k / (1-r) * K < (\<epsilon> - product_dist a x)"
            using mult_imp_div_pos_less[OF divide_pos_pos[OF _ K_pos,of "1-r"]] r(2) by auto
          have hk': "0 < k" apply(rule ccontr) using hk he2 Product_metric.nonneg[of a x] by auto
          define \<epsilon>' where "\<epsilon>' \<equiv> (1/(real k))*(\<epsilon> - product_dist a x - r^k / (1-r) * K)"
          have h\<epsilon>' : "0 < \<epsilon>'" using hk by(auto simp: \<epsilon>'_def hk')
          define X where "X \<equiv> (if finite I then (\<lambda>i. if i \<in> I then Metric_space.mball (Mi i) (di i) (x i) \<epsilon>' else topspace (Metric_space.mtopology (Mi i) (di i))) else (\<lambda>i. if i \<in> I \<and> f i < k then Metric_space.mball (Mi i) (di i) (x i) \<epsilon>' else topspace (Metric_space.mtopology (Mi i) (di i))))"
          show ?thesis
          proof(intro exI[where x=X] conjI)
            have "x i \<in> Metric_space.mball (Mi i) (di i) (x i) \<epsilon>'" if "i \<in> I" for i
              using hu \<open>x \<in> U\<close> by (auto simp add: PiE_mem h\<epsilon>' Md_metric Metric_space.centre_in_mball_iff that)
            thus "x \<in> (\<Pi>\<^sub>E i\<in>I. X i)"
              using hu that htopspace by(auto simp: X_def)
          next
            show "(\<Pi>\<^sub>E i\<in>I. X i) \<subseteq> U"
            proof
              fix y
              assume "y \<in> (\<Pi>\<^sub>E i\<in>I. X i)"
              have "\<And>i. X i \<subseteq> topspace (Metric_space.mtopology (Mi i) (di i))"
                by (simp add: Md_metric Metric_space.mball_subset_mspace X_def htopspace)
              hence "y \<in> (\<Pi>\<^sub>E i\<in>I. Mi i)"
                using htopspace' \<open>y \<in> (\<Pi>\<^sub>E i\<in>I. X i)\<close> by blast
              have "product_dist a y < \<epsilon>"
              proof -
                have "product_dist a y \<le> product_dist a x + product_dist x y"
                  using Product_metric.triangle \<open>y \<in> Pi\<^sub>E I Mi\<close> hu(1) that by auto
                also have "... < product_dist a x + (\<epsilon> - product_dist a x)"
                proof -
                  have "product_dist x y < (\<epsilon> - product_dist a x)"
                  proof -
                    have "product_dist x y = (\<Sum>n. if g n \<in> I then r ^ n * di (g n) (x (g n)) (y (g n)) else 0)"
                      by (metis (no_types, lifting) hu(1) that \<open>y \<in> (\<Pi>\<^sub>E i\<in>I. Mi i)\<close> Product_metric.in_mball product_dist_def suminf_cong)
                    also have "... = (\<Sum>n. if g (n + k) \<in> I then r ^ (n + k)* di (g (n + k)) (x (g (n + k))) (y (g (n + k))) else 0) + (\<Sum>n<k. if g n \<in> I then r ^ n * di (g n) (x (g n)) (y (g n)) else 0)"
                      by(rule suminf_split_initial_segment) simp
                    also have "... \<le> r^k / (1 - r) * K + (\<Sum>n<k. if g n \<in> I then r ^ n * di (g n) (x (g n)) (y (g n)) else 0)"
                    proof -
                      have "(\<Sum>n. if g (n + k) \<in> I then r ^ (n + k)* di (g (n + k)) (x (g (n + k))) (y (g (n + k))) else 0) \<le> (\<Sum>n. r ^ (n + k) * K)"
                        using di_bounded di_nonneg r K_pos by(auto intro!: suminf_le summable_ignore_initial_segment) 
                      also have "... = r^k / (1 - r) * K"
                        by(rule nsum_of_rK)
                      finally show ?thesis by simp
                    qed
                    also have "... < r^k / (1 - r) * K + (\<epsilon> - product_dist a x - r^k / (1 - r) * K)"
                    proof -
                      have "(\<Sum>n<k. if g n \<in> I then r ^ n * di (g n) (x (g n)) (y (g n)) else 0) < (\<Sum>n<k. \<epsilon>')"
                      proof(rule sum_strict_mono_ex1)
                        show "\<forall>l\<in>{..<k}. (if g l \<in> I then r ^ l * di (g l) (x (g l)) (y (g l)) else 0) \<le> \<epsilon>'"
                        proof -
                          {
                            fix l
                            assume "g l \<in> I" "l < k"
                            then interpret mbd: Metric_space "Mi (g l)" "di (g l)"
                              by(auto intro!: Md_metric)
                            have "r ^ l * di (g l) (x (g l)) (y (g l)) \<le> di (g l) (x (g l)) (y (g l))"
                              using r by(auto intro!: mult_right_mono[of "r ^ l" 1,OF _ mbd.nonneg[of "x (g l)" "y (g l)"],simplified] simp: power_le_one)
                            also have "... < \<epsilon>'"
                            proof -
                              have "y (g l) \<in> mbd.mball (x (g l)) \<epsilon>'"
                              proof(cases "finite I")
                                case True
                                then show ?thesis
                                  using PiE_mem[OF \<open>y \<in> (\<Pi>\<^sub>E i\<in>I. X i)\<close> \<open>g l \<in> I\<close>]
                                  by(simp add: X_def \<open>g l \<in> I\<close>)
                              next
                                case False
                                then show ?thesis
                                  using PiE_mem[OF \<open>y \<in> (\<Pi>\<^sub>E i\<in>I. X i)\<close> \<open>g l \<in> I\<close>] gf_if_infinite(3)
                                  by(simp add: X_def \<open>g l \<in> I\<close> \<open>l < k\<close>)
                              qed
                              thus ?thesis
                                by auto
                            qed
                            finally have "r ^ l * di (g l) (x (g l)) (y (g l)) \<le> \<epsilon>'" by simp
                          }
                          thus ?thesis
                            by(auto simp: order.strict_implies_order[OF h\<epsilon>'])
                        qed
                      next
                        show "\<exists>a\<in>{..<k}. (if g a \<in> I then r ^ a * di (g a) (x (g a)) (y (g a)) else 0) < \<epsilon>'"
                        proof(rule bexI[where x=0])
                          {
                            assume "g 0 \<in> I"
                            then interpret mbd: Metric_space "Mi (g 0)" "di (g 0)"
                              by(auto intro!: Md_metric)
                            have "y (g 0) \<in> mbd.mball (x (g 0)) \<epsilon>'"
                            proof(cases "finite I")
                              case True
                              then show ?thesis
                                using PiE_mem[OF \<open>y \<in> (\<Pi>\<^sub>E i\<in>I. X i)\<close> \<open>g 0 \<in> I\<close>]
                                by(simp add: X_def \<open>g 0 \<in> I\<close>)
                            next
                              case False
                              then show ?thesis
                                using PiE_mem[OF \<open>y \<in> (\<Pi>\<^sub>E i\<in>I. X i)\<close> \<open>g 0 \<in> I\<close>] gf_if_infinite(3)
                                by(simp add: X_def \<open>g 0 \<in> I\<close> \<open>0 < k\<close>)
                            qed
                            hence "r ^ 0 * di (g 0) (x (g 0)) (y (g 0))  < \<epsilon>'"
                              by auto
                          }
                          thus "(if g 0 \<in> I then r ^ 0 * di (g 0) (x (g 0)) (y (g 0)) else 0) < \<epsilon>'"
                            using  h\<epsilon>' by auto
                        qed(use hk' in auto)
                      qed simp
                      also have "... = (\<epsilon> - product_dist a x - r ^ k / (1 - r) * K)"
                        by(simp add: \<epsilon>'_def hk')
                      finally show ?thesis by simp
                    qed
                    finally show ?thesis by simp
                  qed
                  thus ?thesis by simp
                qed
                finally show ?thesis by auto
              qed
              thus "y \<in> U"
                by(simp add: hu(1) hu(2) \<open>y \<in> (\<Pi>\<^sub>E i\<in>I. Mi i)\<close>)
            qed
          next
            have "openin (Metric_space.mtopology (Mi i) (di i)) (Metric_space.mball (Mi i) (di i) (x i) \<epsilon>')" if "i \<in> I" for i
              by (simp add: Md_metric Metric_space.openin_mball that)
            moreover have "openin (Metric_space.mtopology (Mi i) (di i)) (topspace (Metric_space.mtopology (Mi i) (di i)))" for i
              by auto
            ultimately show "\<forall>i. openin (Metric_space.mtopology (Mi i) (di i)) (X i)"
              by(auto simp: X_def)
          next
            show "finite {i. X i \<noteq> topspace (Metric_space.mtopology (Mi i) (di i))}"
            proof(cases "finite I")
              case True
              then show ?thesis
                by(simp add: X_def)
            next
              case Iinf:False
              have "finite {i \<in> I. f i < k}"
              proof -
                have "{i \<in> I. f i < k} = inv_into I f ` {..<k}"
                proof -
                  have *:"\<And>i. i \<in> I \<Longrightarrow> inv_into I f (f i) = i"
                         "\<And>n. f (inv_into I f n) = n"
                    using bij_betw_inv_into_left[OF gf_if_infinite(1)[OF Iinf]]
                          bij_betw_inv_into_right[OF gf_if_infinite(1)[OF Iinf]]
                    by auto
                  show ?thesis
                  proof
                    show "{i \<in> I. f i < k} \<subseteq> inv_into I f ` {..<k}"
                    proof
                    show "p \<in> {i \<in> I. f i < k} \<Longrightarrow> p \<in> inv_into I f ` {..<k}" for p
                      using *(1)[of p] by (auto simp: rev_image_eqI)
                  qed
                  next
                    show " inv_into I f ` {..<k} \<subseteq> {i \<in> I. f i < k} "
                      using *(2) bij_betw_inv_into[OF  gf_if_infinite(1)[OF Iinf]]
                      by (auto simp: bij_betw_def)
                  qed
                qed
                also have "finite ..." by auto
                finally show ?thesis .
              qed
              thus ?thesis
                by(simp add: X_def Iinf)
            qed
          qed
        next
          case 2
          then have "U = (\<Pi>\<^sub>E i\<in>I. Mi i)"
            unfolding hu(1) using order.strict_trans1[OF product_dist_leqr,of \<epsilon>] hu(2)
            by auto
          also have "... = (\<Pi>\<^sub>E i\<in>I. topspace (Metric_space.mtopology (Mi i) (di i)))"
            using htopspace by auto
          finally have "U = (\<Pi>\<^sub>E i\<in>I. topspace (Metric_space.mtopology (Mi i) (di i)))" .
          thus ?thesis
            using that hu htopspace by(auto intro!: exI[where x="\<lambda>i. topspace (Metric_space.mtopology (Mi i) (di i))"])
        qed
      qed
      hence "\<exists>X. \<forall>x\<in>U. x \<in> (\<Pi>\<^sub>E i\<in>I. X x i) \<and> (\<Pi>\<^sub>E i\<in>I. X x i) \<subseteq> U \<and> (\<forall>i. openin (Metric_space.mtopology (Mi i) (di i)) (X x i)) \<and> finite {i. X x i \<noteq> topspace (Metric_space.mtopology (Mi i) (di i))}"
        by(auto intro!: bchoice)
      then obtain X where "\<forall>x\<in>U. x \<in> (\<Pi>\<^sub>E i\<in>I. X x i) \<and> (\<Pi>\<^sub>E i\<in>I. X x i) \<subseteq> U \<and> (\<forall>i. openin (Metric_space.mtopology (Mi i) (di i)) (X x i)) \<and> finite {i. X x i \<noteq> topspace (Metric_space.mtopology (Mi i) (di i))}"
        by auto
      hence hX: "\<And>x. x \<in> U \<Longrightarrow> x \<in> (\<Pi>\<^sub>E i\<in>I. X x i)" "\<And>x. x \<in> U \<Longrightarrow> (\<Pi>\<^sub>E i\<in>I. X x i) \<subseteq> U"  "\<And>x. x \<in> U \<Longrightarrow> (\<forall>i. openin (Metric_space.mtopology (Mi i) (di i)) (X x i))" "\<And>x. x \<in> U \<Longrightarrow> finite {i. X x i \<noteq> topspace (Metric_space.mtopology (Mi i) (di i))}"
        by auto
      hence hXopen: "\<And>x. x \<in> U \<Longrightarrow> (\<Pi>\<^sub>E i\<in>I. X x i) \<in> {\<Pi>\<^sub>E i\<in>I. X i |X. (\<forall>i. openin (Metric_space.mtopology (Mi i) (di i)) (X i)) \<and> finite {i. X i \<noteq> topspace (Metric_space.mtopology (Mi i) (di i))}}"
        by blast
      have "U = (\<Union> {(\<Pi>\<^sub>E i\<in>I. X x i) | x. x \<in> U})"
        using hX(1,2) by blast
      have "openin (topology_generated_by {\<Pi>\<^sub>E i\<in>I. X i |X. (\<forall>i. openin (Metric_space.mtopology (Mi i) (di i)) (X i)) \<and> finite {i. X i \<noteq> topspace (Metric_space.mtopology (Mi i) (di i))}}) (\<Union> {(\<Pi>\<^sub>E i\<in>I. X x i) | x. x \<in> U})"
        apply(rule openin_Union)
        using hXopen by(auto simp: openin_topology_generated_by_iff intro!: generate_topology_on.Basis)
      thus "openin (topology_generated_by {\<Pi>\<^sub>E i\<in>I. X i |X. (\<forall>i. openin (Metric_space.mtopology (Mi i) (di i)) (X i)) \<and> finite {i. X i \<noteq> topspace (Metric_space.mtopology (Mi i) (di i))}}) U"
        using \<open>U = (\<Union> {(\<Pi>\<^sub>E i\<in>I. X x i) | x. x \<in> U})\<close> by simp
    next
      fix U
      assume "U \<in> {\<Pi>\<^sub>E i\<in>I. X i |X. (\<forall>i. openin (Metric_space.mtopology (Mi i) (di i)) (X i)) \<and> finite {i. X i \<noteq> topspace (Metric_space.mtopology (Mi i) (di i))}}"
      then obtain X where hX:
       "U = (\<Pi>\<^sub>E i\<in>I. X i)" "\<And>i. openin (Metric_space.mtopology (Mi i) (di i)) (X i)" "finite {i. X i \<noteq> topspace (Metric_space.mtopology (Mi i) (di i))}"
        by auto
      have "\<exists>a \<epsilon>. x \<in> Product_metric.mball a \<epsilon> \<and> Product_metric.mball a \<epsilon> \<subseteq> U" if "x \<in> U" for x
      proof -
        have x_intop:"x \<in> (\<Pi>\<^sub>E i\<in>I. Mi i)"
          unfolding htopspace'[symmetric] using that hX(1) openin_subset[OF hX(2)] by auto
        define I' where "I' \<equiv> {i. X i \<noteq> topspace (Metric_space.mtopology (Mi i) (di i))} \<inter> I"
        then have I':"finite I'" "I' \<subseteq> I" using hX(3) by auto
        consider "I' = {}" | "I' \<noteq> {}" by auto
        then show ?thesis
        proof cases
          case 1
          then have "\<And>i. i \<in> I \<Longrightarrow> X i = topspace (Metric_space.mtopology (Mi i) (di i))"
            by(auto simp: I'_def)
          then have "U = (\<Pi>\<^sub>E i\<in>I. Mi i)"
            by (simp add: PiE_eq hX(1) htopspace)
          thus ?thesis
            using 1 that by(auto intro!: exI[where x=x] exI[where x=1])
        next
          case I'_nonempty:2
          hence "\<And>i. i \<in> I' \<Longrightarrow> openin (Metric_space.mtopology (Mi i) (di i)) (X i)"
            using hX(2) by(simp add: I'_def)
          hence "\<exists>\<epsilon>>0. Metric_space.mball (Mi i) (di i) (x i) \<epsilon> \<subseteq> (X i)" if "i \<in> I'" for i
            using I'(2) Md_metric Metric_space.openin_mtopology PiE_mem \<open>x \<in> U\<close> hX(1) subset_eq that by blast
          then obtain \<epsilon>i' where hei:"\<And>i. i \<in> I' \<Longrightarrow> \<epsilon>i' i > 0" "\<And>i. i \<in> I' \<Longrightarrow> Metric_space.mball (Mi i) (di i) (x i) (\<epsilon>i' i) \<subseteq> (X i)"
            by metis
          define \<epsilon> where "\<epsilon> \<equiv> Min {\<epsilon>i' i |i. i \<in> I'}"
          have \<epsilon>min: "\<And>i. i \<in> I' \<Longrightarrow> \<epsilon> \<le> \<epsilon>i' i"
            using I' by(auto simp: \<epsilon>_def intro!: Min.coboundedI)
          have h\<epsilon>: "\<epsilon> > 0"
            using I' I'_nonempty Min_gr_iff[of "{\<epsilon>i' i |i. i \<in> I'}" 0] hei(1)
            by(auto simp: \<epsilon>_def)
          define n where "n \<equiv> Max {f i | i. i \<in> I'}"
          have "\<And>i. i \<in> I' \<Longrightarrow>f i \<le> n"
            using I' by(auto intro!: Max.coboundedI[of "{f i | i. i \<in> I'}"] simp: n_def)
          hence hn2:"\<And>i. i \<in> I' \<Longrightarrow> (1 / r) ^ f i \<le> (1 / r)^n"
            using r by auto
          have h\<epsilon>' : "0 < \<epsilon>*(r^n)" using h\<epsilon> r by auto
          show ?thesis
          proof(safe intro!: exI[where x=x] exI[where x="\<epsilon>*(r^n)"])
            fix y
            assume "y \<in> Product_metric.mball x (\<epsilon> * r ^ n)"
            have "y i \<in> X i" if "i \<in> I'" for i
            proof -
              interpret mi: Metric_space "Mi i" "di i"
                using Md_metric that by(simp add: I'_def)
              have "di i (x i) (y i) < \<epsilon>i' i"
              proof -
                have "di i (x i) (y i) \<le> (1 / r) ^ f i * product_dist x y"
                  using that \<open>y \<in> Product_metric.mball x (\<epsilon> * r ^ n)\<close> by(auto intro!: product_dist_geq[of i,OF  _ gf_comp_id x_intop] simp: I'_def)
                also have "... \<le> (1 / r)^n * product_dist x y"
                  by(rule mult_right_mono[OF hn2[OF that] Product_metric.nonneg])
                also have "... <  \<epsilon>"
                  using \<open>y \<in> Product_metric.mball x (\<epsilon> * r ^ n)\<close> r
                  by (simp add: pos_divide_less_eq power_one_over)
                also have "... \<le> \<epsilon>i' i"
                  by(rule \<epsilon>min[OF that])
                finally show ?thesis .
              qed
              hence "(y i) \<in> mi.mball (x i) (\<epsilon>i' i)"
                using \<open>y \<in> Product_metric.mball x (\<epsilon> * r ^ n)\<close> x_intop that
                by(auto simp: I'_def)
              thus ?thesis
                using hei[OF that] by auto
            qed
            moreover have "y i \<in> X i" if "i \<in> I - I'" for i
              using that htopspace \<open>y \<in> Product_metric.mball x (\<epsilon> * r ^ n)\<close>
              by(auto simp: I'_def)
            ultimately show "y \<in> U"
              using \<open>y \<in> Product_metric.mball x (\<epsilon> * r ^ n)\<close>
              by(auto simp: hX(1))
          qed(use x_intop h\<epsilon>' in auto)
        qed
      qed
      then obtain a where "\<forall>x\<in>U. \<exists>\<epsilon>. x \<in> Product_metric.mball (a x) \<epsilon> \<and> Product_metric.mball (a x) \<epsilon> \<subseteq> U"
        by metis
      then obtain \<epsilon> where hae: "\<And>x. x \<in> U \<Longrightarrow> x \<in> Product_metric.mball (a x) (\<epsilon> x)" "\<And>x. x \<in> U \<Longrightarrow> Product_metric.mball (a x) (\<epsilon> x) \<subseteq> U"
        by metis
      hence hae': "\<And>x. x \<in> U \<Longrightarrow> a x \<in> (\<Pi>\<^sub>E i\<in>I. Mi i)" "\<And>x. x \<in> U \<Longrightarrow> 0 < \<epsilon> x"
        by auto[1] (metis Product_metric.mball_eq_empty empty_iff hae(1) linorder_not_less)
      have "openin (topology_generated_by {Product_metric.mball a \<epsilon> |a \<epsilon>. a \<in> (\<Pi>\<^sub>E i\<in>I. Mi i) \<and> 0 < \<epsilon>}) (\<Union> { Product_metric.mball (a x) (\<epsilon> x) |x. x \<in> U})"
        using Product_metric.openin_mball \<open>Product_metric.mtopology = topology_generated_by {Product_metric.mball a \<epsilon> |a \<epsilon>. a \<in> Pi\<^sub>E I Mi \<and> 0 < \<epsilon>}\<close> by auto
      moreover have "U = (\<Union> {Product_metric.mball (a x) (\<epsilon> x) |x. x \<in> U})"
        using hae by (auto simp del: Product_metric.in_mball)
      ultimately show "openin (topology_generated_by {Product_metric.mball a \<epsilon> |a \<epsilon>. a \<in> (\<Pi>\<^sub>E i\<in>I. Mi i) \<and> 0 < \<epsilon>}) U"
        by simp
    qed
  qed
qed

corollary separable_Mi_separable_M:
  assumes "\<And>i. i \<in> I \<Longrightarrow> separable_space (Metric_space.mtopology (Mi i) (di i))"
  shows "separable_space Product_metric.mtopology"
  by(simp add: Product_metric_mtopology_eq[symmetric] separable_countable_product assms I)

lemma mcomplete_Mi_mcomplete_M:
  assumes "\<And>i. i \<in> I \<Longrightarrow> Metric_space.mcomplete (Mi i) (di i)"
  shows Product_metric.mcomplete
proof(cases "I = {}")
  case 1:True
  interpret d: discrete_metric "{\<lambda>x. undefined}" .
  have 2:"product_dist  = (\<lambda>x y. 0)"
    by standard+ (auto simp: product_dist_def 1)
  show ?thesis
    apply(simp add: Product_metric.mcomplete_def Product_metric.limitin_metric eventually_sequentially Product_metric.MCauchy_def)
    apply(simp add: 2)
    by(auto simp: 1 intro!: exI[where x="(\<lambda>i. undefined)"])
next
  assume 2: "I \<noteq> {}"
  show ?thesis
    unfolding Product_metric.mcomplete_def
  proof safe
    fix xn
    assume h: "Product_metric.MCauchy xn"
    have *:"Metric_space.MCauchy (Mi i) (di i) (\<lambda>n. xn n i)" if hi:"i \<in> I" for i
    proof -
      interpret mi: Metric_space "Mi i" "di i"
        by(simp add: Md_metric hi)
      show "mi.MCauchy (\<lambda>n. xn n i)"
        unfolding mi.MCauchy_def
      proof safe
        show "xn n i \<in> Mi i" for n
          using h hi by(auto simp: Product_metric.MCauchy_def)
      next
        fix \<epsilon>
        assume he:"(0::real) < \<epsilon>"
        then have "0 < \<epsilon> * r^(f i)" using r by auto
        then obtain N where N:
          "\<And>n m. n\<ge>N \<Longrightarrow> m\<ge>N \<Longrightarrow> product_dist (xn n) (xn m) < \<epsilon> * r^(f i)"
          using h Product_metric.MCauchy_def by fastforce 
        show "\<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> di i (xn n i) (xn n' i) < \<epsilon>"
        proof(safe intro!: exI[where x=N])
          fix n m
          assume n:"n \<ge> N" "m \<ge> N"
          have "di i (xn n i) (xn m i) \<le> (1 / r) ^ (f i) * product_dist (xn n) (xn m)"
            by(rule product_dist_geq) (use h[simplified Product_metric.MCauchy_def] hi gf_comp_id[of i] in auto)
          also have "... < \<epsilon>"
            using N[OF n] by (simp add: mult_imp_div_pos_less power_one_over r(1))
          finally show "di i (xn n i) (xn m i) < \<epsilon>" .
        qed
      qed
    qed
    hence "\<forall>i\<in>I. \<exists>x. limitin (Metric_space.mtopology (Mi i) (di i)) (\<lambda>n. xn n i) x sequentially"
      using Md_metric Metric_space.mcomplete_alt assms by blast
    then obtain x where hx:"\<And>i. i \<in> I \<Longrightarrow> limitin (Metric_space.mtopology (Mi i) (di i)) (\<lambda>n. xn n i) (x i) sequentially"
      by metis
    hence hx':"(\<lambda>i\<in>I. x i) \<in> (\<Pi>\<^sub>E i\<in>I. Mi i)"
      by (simp add: Md_metric Metric_space.limit_metric_sequentially)
    thus "\<exists>x. limitin Product_metric.mtopology xn x sequentially"
      using h by(auto intro!: exI[where x="\<lambda>i\<in>I. x i"] limitin_M_iff_limitin_Mi[THEN iffD2,of xn] simp: Product_metric.MCauchy_def hx) blast
  qed
qed

end (* Product_metric *)

lemma product_metricI:
  assumes "0 < r" "r < 1" "countable I" "\<And>i. i \<in> I \<Longrightarrow> Metric_space (Mi i) (di i)"
      and "\<And>i x y. 0 \<le> di i x y" "\<And>i x y. di i x y \<le> K" "0 < K"
    shows "Product_metric r I (to_nat_on I) (from_nat_into I) Mi di K"
  using from_nat_into_to_nat_on_product_metric_pair[OF assms(3)] assms
  by(simp add: Product_metric_def  Metric_space_def)

lemma product_metric_natI:
  assumes "0 < r" "r < 1" "\<And>n. Metric_space (Mi n) (di n)"
      and "\<And>i x y. 0 \<le> di i x y" "\<And>i x y. di i x y \<le> K" "0 < K"
    shows "Product_metric r UNIV id id Mi di K"
  using assms by(auto simp: Product_metric_def)

end