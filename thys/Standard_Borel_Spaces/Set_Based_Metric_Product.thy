(*  Title:   Set_Based_Metric_Product.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

subsection \<open> Product Metric Spaces \<close>

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
product_dist_def: "product_dist' r I g S d \<equiv> (\<lambda>x y. if x \<in> (\<Pi>\<^sub>E i\<in>I. S i) \<and> y \<in> (\<Pi>\<^sub>E i\<in>I. S i) then (\<Sum>n. if g n \<in> I then r^n * d (g n) (x (g n)) (y (g n)) else 0) else 0)"

text \<open> $d(x,y) = \sum_{n\in \mathbb{N}} r^n * d_{g_I(i)}(x_{g_I(i)},y_{g_I(i)})$.\<close>
locale product_metric = 
  fixes r :: real
    and I :: "'i set"
    and f :: "'i \<Rightarrow> nat"
    and g :: "nat \<Rightarrow> 'i"
    and S :: "'i \<Rightarrow> 'a set"
    and d :: "'i \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real"
    and K :: real
  assumes r: "0 < r" "r < 1"
      and I: "countable I"
      and gf_comp_id : "\<And>i. i \<in> I \<Longrightarrow> g (f i) = i"
      and gf_if_finite: "finite I \<Longrightarrow> bij_betw f I {..< card I}"
                        "finite I \<Longrightarrow> bij_betw g {..< card I} I"
      and gf_if_infinite: "infinite I \<Longrightarrow> bij_betw f I UNIV"
                          "infinite I \<Longrightarrow> bij_betw g UNIV I"
                          "\<And>n. infinite I \<Longrightarrow> f (g n) = n"
      and sd_metric: "\<And>i. i \<in> I \<Longrightarrow> metric_set (S i) (d i)"
      and d_nonneg: "\<And>i x y. 0 \<le> d i x y"
      and d_bound: "\<And>i x y. d i x y \<le> K"
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

context product_metric
begin

abbreviation "product_dist \<equiv> product_dist' r I g S d"

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
  "summable (\<lambda>n. r^n * d (g n) (x (g n)) (y (g n)))"
  apply(rule summable_comparison_test'[of "\<lambda>n. r^n * K"])
  using r d_nonneg d_bound K_pos by(auto intro!: summable_mult2)

lemma product_dist_summable[simp]:
  "summable (\<lambda>n. if g n \<in> I then r^n * d (g n) (x (g n)) (y (g n)) else 0)"
  by(rule summable_comparison_test'[of "\<lambda>n. r^n * d (g n) (x (g n)) (y (g n))"]) (use r d_nonneg d_bound K_pos in auto)

lemma summable_rK[simp]: "summable (\<lambda>n. r^n * K)"
  using r by(auto intro!: summable_mult2)

lemma product_dist_distance: "metric_set (\<Pi>\<^sub>E i\<in>I. S i) product_dist"
proof -
  have h': "\<And>i xi yi. i \<in> I \<Longrightarrow> xi \<in> S i \<Longrightarrow> yi \<in> S i \<Longrightarrow> xi = yi \<longleftrightarrow> d i xi yi = 0"
           "\<And>i xi yi. i \<in> I \<Longrightarrow> d i xi yi = d i yi xi"
           "\<And>i xi yi zi. i \<in> I \<Longrightarrow> xi \<in> S i \<Longrightarrow> yi \<in> S i \<Longrightarrow> zi \<in> S i \<Longrightarrow> d i xi zi \<le> d i xi yi + d i yi zi"
    using sd_metric by(auto simp: metric_set_def)
  show ?thesis
  proof
    show "\<And>x y. 0 \<le> product_dist x y"
      using d_nonneg r by(auto simp: product_dist_def intro!: suminf_nonneg product_dist_summable)
  next
    show "\<And>x y. x \<notin> (\<Pi>\<^sub>E i\<in>I. S i) \<Longrightarrow> product_dist x y = 0"
      by(auto simp: product_dist_def)
  next
    fix x y
    assume hxy:"x \<in> (\<Pi>\<^sub>E i\<in>I. S i)" "y \<in> (\<Pi>\<^sub>E i\<in>I. S i)"
    show "(x = y) \<longleftrightarrow> (product_dist x y = 0)"
    proof
      assume heq:"x = y"
      then have "(if g n \<in> I then r ^ n * d (g n) (x (g n)) (y (g n)) else 0) = 0" for n
        using hxy h'(1)[of "g n" "x (g n)" "y (g n)"] by(auto simp: product_dist_def)
      thus "product_dist x y = 0"
        by(auto simp: product_dist_def)
    next
      assume h0:"product_dist x y = 0"
      have "(\<Sum>n. if g n \<in> I then r ^ n * d (g n) (x (g n)) (y (g n)) else 0) = 0
                     \<longleftrightarrow> (\<forall>n. (if g n \<in> I then r^n * d (g n) (x (g n)) (y (g n)) else 0) = 0)"
        apply(rule suminf_eq_zero_iff)
        using d_nonneg r by(auto simp: product_dist_def intro!: product_dist_summable)
      hence hn0:"\<And>n. (if g n \<in> I then r^n * d (g n) (x (g n)) (y (g n)) else 0) = 0"
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
          have "d (g n) (x (g n)) (y (g n)) = 0"
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
    assume hxyz:"x \<in> (\<Pi>\<^sub>E i\<in>I. S i)" "y \<in> (\<Pi>\<^sub>E i\<in>I. S i)" "z \<in> (\<Pi>\<^sub>E i\<in>I. S i)"
    have "(if g n \<in> I then r ^ n * d (g n) (x (g n)) (z (g n)) else 0) 
           \<le> (if g n \<in> I then r ^ n * d (g n) (x (g n)) (y (g n)) else 0) + (if g n \<in> I then r ^ n * d (g n) (y (g n)) (z (g n)) else 0)" for n
      using h'(3)[of "g n" "x (g n)" "y (g n)" "z (g n)"] hxyz r
      by(auto simp: distrib_left[of "r ^ n",symmetric])
    thus "product_dist x z \<le> product_dist x y + product_dist y z"
    by(auto simp add: product_dist_def suminf_add[OF product_dist_summable[of x y] product_dist_summable[of y z]] hxyz intro!: suminf_le summable_add)
  qed
qed

sublocale metric_set "\<Pi>\<^sub>E i\<in>I. S i" "product_dist"
  by(rule product_dist_distance)

lemma product_dist_leqr: "product_dist x y \<le> 1 / (1 - r) * K"
proof -
  have "product_dist x y \<le> (\<Sum>n. if g n \<in> I then r^n * d (g n) (x (g n)) (y (g n)) else 0)"
  proof -
    consider "x \<in> (\<Pi>\<^sub>E i\<in>I. S i) \<and> y \<in> (\<Pi>\<^sub>E i\<in>I. S i)" | "\<not> (x \<in> (\<Pi>\<^sub>E i\<in>I. S i) \<and> y \<in> (\<Pi>\<^sub>E i\<in>I. S i))" by auto
    then show ?thesis
    proof cases
      case 1
      then show ?thesis by(auto simp: product_dist_def)
    next
      case 2
      then have "product_dist x y = 0"
        by(auto simp: product_dist_def)
      also have "... \<le> (\<Sum>n. if g n \<in> I then r^n * d (g n) (x (g n)) (y (g n)) else 0)"
        using d_nonneg r by(auto intro!: suminf_nonneg product_dist_summable)
      finally show ?thesis .
    qed
  qed
  also have "... \<le> (\<Sum>n. r^n * d (g n) (x (g n)) (y (g n)))"
   using r d_nonneg d_bound by(auto intro!: suminf_le)
  also have "... \<le> (\<Sum>n. r^n * K)"
    using r d_bound d_nonneg by(auto intro!: suminf_le)
  also have "... = 1 / (1 - r) * K"
    using r nsum_of_rK[of 0] by simp
  finally show ?thesis .
qed

lemma product_dist_geq:
  assumes "i \<in> I" and "g n = i" "x \<in> (\<Pi>\<^sub>E i\<in>I. S i)" "y \<in> (\<Pi>\<^sub>E i\<in>I. S i)"
    shows "d i (x i) (y i) \<le> (1/r)^n * product_dist x y"
          (is "?lhs \<le> ?rhs")
proof -
  interpret mi: metric_set "S i" "d i"
    by(rule sd_metric[OF assms(1)])
  have "(\<lambda>m. if m = f i then d (g m) (x (g m)) (y (g m)) else 0) sums d (g (f i)) (x (g (f i))) (y (g (f i)))"
    by(rule sums_single)
  also have "... = ?lhs"
    by(simp add: gf_comp_id[OF assms(1)])
  finally have 1:"summable (\<lambda>m. if m = f i then d (g m) (x (g m)) (y (g m)) else 0)"
                 "?lhs = (\<Sum>m. (if m = f i then d (g m) (x (g m)) (y (g m)) else 0))"
    by(auto simp: sums_iff)
  note 1(2)
  also have "... \<le> (\<Sum>m. (1/r)^n * (if g m \<in> I then r^m * d (g m) (x (g m)) (y (g m)) else 0))"
  proof(rule suminf_le)
    show "summable (\<lambda>m. (1/r)^n * (if g m \<in> I then r^m * d (g m) (x (g m)) (y (g m)) else 0))"
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
    show "(if k = f i then d (g k) (x (g k)) (y (g k)) else 0) \<le> (1/r) ^ n * (if g k \<in> I then r ^ k * d (g k) (x (g k)) (y (g k)) else 0)"
      using * d_nonneg r ** mult_right_mono[OF **] by(auto simp: vector_space_over_itself.scale_scale[of "(1 / r) ^ n"])
  qed(simp add: 1)
  also have "... = ?rhs"
    unfolding product_dist_def
    using assms by(auto intro!: suminf_mult product_dist_summable)
  finally show ?thesis .
qed

lemma converge_to_iff:
  assumes "xn \<in> sequence" "x \<in> (\<Pi>\<^sub>E i\<in>I. S i)"
  shows "converge_to_inS xn x \<longleftrightarrow> (\<forall>i\<in>I. metric_set.converge_to_inS (S i) (d i) (\<lambda>n. xn n i) (x i))"
proof safe
  fix i
  assume h:"converge_to_inS xn x" "i \<in> I"
  then interpret m: metric_set "S i" "d i"
    using sd_metric by blast
  show "m.converge_to_inS (\<lambda>n. xn n i) (x i)"
    unfolding m.converge_to_inS_def2
  proof safe
    show 1:"\<And>x. xn x i \<in> S i" "x i \<in> S i"
      using h by(auto simp: converge_to_inS_def)
  next
    fix \<epsilon> :: real
    assume "0 < \<epsilon>"
    then obtain "r^ f i * \<epsilon> > 0" using r by auto
    then obtain N where N:"\<And>n. n \<ge> N \<Longrightarrow> product_dist (xn n) x < r^ f i * \<epsilon>"
      using h(1) by(auto simp: converge_to_inS_def2) metis
    show "\<exists>N. \<forall>n\<ge>N. d i (xn n i) (x i) < \<epsilon>"
    proof(safe intro!: exI[where x=N])
      fix n
      assume "N \<le> n"
      have "d i (xn n i) (x i) \<le> (1 / r) ^ f i * product_dist (xn n) x"
        using h by(auto intro!: product_dist_geq[OF h(2) gf_comp_id[OF h(2)]] simp: converge_to_inS_def)
      also have "... < (1 / r) ^ f i * r^ f i * \<epsilon>"
        using N[OF \<open>N \<le> n\<close>] r by auto
      also have "... \<le> \<epsilon>"
        by (simp add: \<open>0 < \<epsilon>\<close> power_one_over)
      finally show " d i (xn n i) (x i) < \<epsilon>" .
    qed
  qed
next
  assume h:"\<forall>i\<in>I. metric_set.converge_to_inS (S i) (d i) (\<lambda>n. xn n i) (x i)"
  show "converge_to_inS xn x"
    unfolding converge_to_inS_def2
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
    then show "\<exists>N. \<forall>n\<ge>N. product_dist (xn n) x < \<epsilon>"
    proof cases
      case 1
      then have he2:"1 / (1 - r)*K < \<epsilon>" using hk by auto
      show ?thesis
        using order.strict_trans1[OF product_dist_leqr he2]
        by(auto simp: complete_metric_set_def intro!: exI[where x=0])
    next
      case 2
      with hke have "0 < 1 / real l * (\<epsilon> - r^l/(1-r)*K)" by auto
      hence "\<forall>i\<in>I. \<exists>N. \<forall>n\<ge>N. d i (xn n i) (x i) < 1 / real l * (\<epsilon> - r^l/(1-r)*K)"
        using h metric_set.converge_to_inS_def2[OF sd_metric] by auto
      then obtain N where hn:
      "\<And>i n. i \<in> I \<Longrightarrow> n \<ge> N i \<Longrightarrow> d i (xn n i) (x i) < 1 / real l * (\<epsilon> - r^l/(1-r)*K)"
        by metis
      show ?thesis
      proof(safe intro!: exI[where x="Sup {N (g n) | n. n < l}"])
        fix n
        assume hsup:"\<Squnion> {N (g n) |n. n < l} \<le> n"
        have "product_dist (xn n) x = (\<Sum>m. if g m \<in> I then r ^ m * d (g m) (xn n (g m)) (x (g m)) else 0)"
          using assms by(auto simp: product_dist_def)
        also have "... = (\<Sum>m. if g (m + l) \<in> I then r ^ (m + l)* d (g (m + l)) (xn n (g (m + l))) (x (g (m + l))) else 0) + (\<Sum>m<l. if g m \<in> I then r ^ m * d (g m) (xn n (g m)) (x (g m)) else 0)"
          by(auto intro!: suminf_split_initial_segment)
        also have "... \<le> r^l/(1-r)*K + (\<Sum>m<l. if g m \<in> I then r ^ m * d (g m) (xn n (g m)) (x(g m)) else 0)"
        proof -
          have "(\<Sum>m. if g (m + l) \<in> I then r ^ (m + l)* d (g (m + l)) (xn n (g (m + l))) (x (g (m + l))) else 0) \<le> (\<Sum>m. r^(m + l)*K)"
            using d_bound assms r K_pos by(auto intro!: suminf_le summable_ignore_initial_segment)
          also have "... = r^l/(1-r)*K"
            by(rule nsum_of_rK)
          finally show ?thesis by auto
        qed
        also have "... \<le> r^l / (1 - r)*K + (\<Sum>m<l. if g m \<in> I then d (g m) (xn n (g m)) (x (g m)) else 0)"
        proof -
          have " (\<Sum>m<l. if g m \<in> I then r ^ m * d (g m) (xn n (g m)) (x (g m))  else 0) \<le> (\<Sum>m<l. if g m \<in> I then d (g m) (xn n (g m)) (x (g m)) else 0)"
            using d_bound d_nonneg r by(auto intro!: sum_mono simp: mult_left_le_one_le power_le_one)
          thus ?thesis by simp
        qed
        also have "... < r^l / (1 - r)*K + (\<Sum>m<l. 1 / real l * (\<epsilon> - r^l/(1-r)*K))"
        proof -
          have "(\<Sum>m<l. if g m \<in> I then d (g m) (xn n (g m)) (x (g m)) else 0) < (\<Sum>m<l. 1 / real l * (\<epsilon> - r^l/(1-r)*K))"
          proof(rule sum_strict_mono_ex1)
            show "\<forall>p\<in>{..<l}. (if g p \<in> I then d (g p) (xn n (g p)) (x (g p)) else 0) \<le> 1 / real l * (\<epsilon> - r ^ l / (1 - r)*K)"
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
                hence "d (g p) (xn n (g p)) (x (g p)) \<le> (\<epsilon> - r ^ l *K/ (1 - r)) / real l"
                  using hn[OF \<open>g p \<in> I\<close>,of n] by simp
              }
              ultimately show ?thesis
                by auto
            qed
          next
            show "\<exists>a\<in>{..<l}. (if g a \<in> I then d (g a) (xn n (g a)) (x (g a)) else 0) < 1 / real l * (\<epsilon> - r ^ l  / (1 - r)*K)"
            proof -
              have "0 < (\<epsilon> - r ^ l * K / (1 - r)) / real l"
                using hke 2 by auto
              moreover {
                assume "g 0 \<in> I"
                have "N (g 0) \<in> {N (g n) |n. n < l}"
                  using 2 by auto
                from le_cSup_finite[OF _ this] hsup have "N (g 0) \<le> n"
                  by auto
                hence "d (g 0) (xn n (g 0)) (x (g 0)) < (\<epsilon> - r ^ l * K/ (1 - r)) / real l"
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
      qed
    qed
  qed (use assms in auto)
qed

lemma product_dist_mtopology: "product_topology (\<lambda>i. metric_set.mtopology (S i) (d i)) I = mtopology" 
proof -
  have htopspace:"\<And>i. i \<in> I \<Longrightarrow> topspace (metric_set.mtopology (S i) (d i)) = S i"
    by (simp add: sd_metric metric_set.mtopology_topspace)
  hence htopspace':"(\<Pi>\<^sub>E i\<in>I. topspace (metric_set.mtopology (S i) (d i))) = (\<Pi>\<^sub>E i\<in>I. S i)" by auto
  consider "I = {}" | "I \<noteq> {}" by auto
  then show ?thesis
  proof cases
    case 1
    then have "product_dist  = (\<lambda>x y. 0)"
      using metric_set_axioms by(simp add: singleton_metric_unique)
    thus ?thesis
      by(simp add: product_topology_empty_discrete 1 singleton_metric_mtopology)
  next
    case I':2
    show ?thesis
      unfolding mtopology_def2 product_topology_def
    proof(rule topology_generated_by_eq)
      fix U
      assume "U \<in> {open_ball a \<epsilon> |a \<epsilon>. a \<in> (\<Pi>\<^sub>E i\<in>I. S i) \<and> 0 < \<epsilon>}"
      then obtain a \<epsilon> where hu:
        "U = open_ball a \<epsilon>" "a \<in> (\<Pi>\<^sub>E i\<in>I. S i)" "0 < \<epsilon>" by auto
      have "\<exists>X. x \<in> (\<Pi>\<^sub>E i\<in>I. X i) \<and> (\<Pi>\<^sub>E i\<in>I. X i) \<subseteq> U \<and> (\<forall>i. openin (metric_set.mtopology (S i) (d i)) (X i)) \<and> finite {i. X i \<noteq> topspace (metric_set.mtopology (S i) (d i))}" if "x \<in> U" for x
      proof -
        consider "\<epsilon> \<le> 1 / (1 - r) * K" | "1 / (1 - r) * K < \<epsilon>" by fastforce
        then show "\<exists>X. x \<in> (\<Pi>\<^sub>E i\<in>I. X i) \<and> (\<Pi>\<^sub>E i\<in>I. X i) \<subseteq> U \<and>  (\<forall>i. openin (metric_set.mtopology (S i) (d i)) (X i)) \<and>  finite {i. X i \<noteq> topspace (metric_set.mtopology (S i) (d i))}"
        proof cases
          case he2:1
          note hx = open_ballD[OF that[simplified hu(1)]] open_ballD'(1)[OF that[simplified hu(1)]]

          then have "0 < (\<epsilon> - product_dist a x)*((1-r)/ K)" using r hu K_pos by auto
          hence "\<exists>k. r^k < (\<epsilon> - product_dist a x)*((1-r)/ K)"
            using r(2) real_arch_pow_inv by blast
          then obtain k where "r^k < (\<epsilon> - product_dist a x)*((1-r)/ K)" by auto
          hence hk:"r^k / (1-r) * K < (\<epsilon> - product_dist a x)"
            using mult_imp_div_pos_less[OF divide_pos_pos[OF _ K_pos,of "1-r"]] r(2) by auto
          have hk': "0 < k" apply(rule ccontr) using hk he2 dist_geq0[of a x] by auto
          define \<epsilon>' where "\<epsilon>' \<equiv> (1/(real k))*(\<epsilon> - product_dist a x - r^k / (1-r) * K)"
          have h\<epsilon>' : "0 < \<epsilon>'" using hk by(auto simp: \<epsilon>'_def hk')
          define X where "X \<equiv> (if finite I then (\<lambda>i. if i \<in> I then metric_set.open_ball (S i) (d i) (x i) \<epsilon>' else topspace (metric_set.mtopology (S i) (d i))) else (\<lambda>i. if i \<in> I \<and> f i < k then metric_set.open_ball (S i) (d i) (x i) \<epsilon>' else topspace (metric_set.mtopology (S i) (d i))))"
          show ?thesis
          proof(intro exI[where x=X] conjI)
            have "x i \<in> metric_set.open_ball (S i) (d i) (x i) \<epsilon>'" if "i \<in> I" for i
              using hx(2) by (simp add: PiE_mem h\<epsilon>' metric_set.open_ball_ina sd_metric that)
            thus "x \<in> (\<Pi>\<^sub>E i\<in>I. X i)"
              using hx(2) htopspace by(auto simp: X_def)
          next
            show "(\<Pi>\<^sub>E i\<in>I. X i) \<subseteq> U"
            proof
              fix y
              assume "y \<in> (\<Pi>\<^sub>E i\<in>I. X i)"
              have "\<And>i. X i \<subseteq> topspace (metric_set.mtopology (S i) (d i))"
                by (simp add: X_def sd_metric htopspace metric_set.open_ball_subset_ofS)
              hence "y \<in> (\<Pi>\<^sub>E i\<in>I. S i)"
                using htopspace' \<open>y \<in> (\<Pi>\<^sub>E i\<in>I. X i)\<close> by blast
              have "product_dist a y < \<epsilon>"
              proof -
                have "product_dist a y \<le> product_dist a x + product_dist x y"
                  by(rule dist_tr[OF hu(2) hx(2) \<open>y \<in> (\<Pi>\<^sub>E i\<in>I. S i)\<close>])
                also have "... < product_dist a x + (\<epsilon> - product_dist a x)"
                proof -
                  have "product_dist x y < (\<epsilon> - product_dist a x)"
                  proof -
                    have "product_dist x y = (\<Sum>n. if g n \<in> I then r ^ n * d (g n) (x (g n)) (y (g n)) else 0)"
                      by(simp add: product_dist_def hx \<open>y \<in> (\<Pi>\<^sub>E i\<in>I. S i)\<close>)
                    also have "... = (\<Sum>n. if g (n + k) \<in> I then r ^ (n + k)* d (g (n + k)) (x (g (n + k))) (y (g (n + k))) else 0) + (\<Sum>n<k. if g n \<in> I then r ^ n * d (g n) (x (g n)) (y (g n)) else 0)"
                      by(rule suminf_split_initial_segment) simp
                    also have "... \<le> r^k / (1 - r) * K + (\<Sum>n<k. if g n \<in> I then r ^ n * d (g n) (x (g n)) (y (g n)) else 0)"
                    proof -
                      have "(\<Sum>n. if g (n + k) \<in> I then r ^ (n + k)* d (g (n + k)) (x (g (n + k))) (y (g (n + k))) else 0) \<le> (\<Sum>n. r ^ (n + k) * K)"
                        using d_bound d_nonneg r K_pos by(auto intro!: suminf_le summable_ignore_initial_segment) 
                      also have "... = r^k / (1 - r) * K"
                        by(rule nsum_of_rK)
                      finally show ?thesis by simp
                    qed
                    also have "... < r^k / (1 - r) * K + (\<epsilon> - product_dist a x - r^k / (1 - r) * K)"
                    proof -
                      have "(\<Sum>n<k. if g n \<in> I then r ^ n * d (g n) (x (g n)) (y (g n)) else 0) < (\<Sum>n<k. \<epsilon>')"
                      proof(rule sum_strict_mono_ex1)
                        show "\<forall>l\<in>{..<k}. (if g l \<in> I then r ^ l * d (g l) (x (g l)) (y (g l)) else 0) \<le> \<epsilon>'"
                        proof -
                          {
                            fix l
                            assume "g l \<in> I" "l < k"
                            then interpret mbd: metric_set "S (g l)" "d (g l)"
                              by(auto intro!: sd_metric)
                            have "r ^ l * d (g l) (x (g l)) (y (g l)) \<le> d (g l) (x (g l)) (y (g l))"
                              using r by(auto intro!: mult_right_mono[of "r ^ l" 1,OF _ mbd.dist_geq0[of "x (g l)" "y (g l)"],simplified] simp: power_le_one)
                            also have "... < \<epsilon>'"
                            proof -
                              have "y (g l) \<in> mbd.open_ball (x (g l)) \<epsilon>'"
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
                                by(auto dest: mbd.open_ballD)
                            qed
                            finally have "r ^ l * d (g l) (x (g l)) (y (g l)) \<le> \<epsilon>'" by simp
                          }
                          thus ?thesis
                            by(auto simp: order.strict_implies_order[OF h\<epsilon>'])
                        qed
                      next
                        show "\<exists>a\<in>{..<k}. (if g a \<in> I then r ^ a * d (g a) (x (g a)) (y (g a)) else 0) < \<epsilon>'"
                        proof(rule bexI[where x=0])
                          {
                            assume "g 0 \<in> I"
                            then interpret mbd: metric_set "S (g 0)" "d (g 0)"
                              by(auto intro!: sd_metric)
                            have "y (g 0) \<in> mbd.open_ball (x (g 0)) \<epsilon>'"
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
                            hence "r ^ 0 * d (g 0) (x (g 0)) (y (g 0))  < \<epsilon>'"
                              by(auto dest: mbd.open_ballD)
                          }
                          thus "(if g 0 \<in> I then r ^ 0 * d (g 0) (x (g 0)) (y (g 0)) else 0) < \<epsilon>'"
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
                by(simp add: hu(1) open_ball_def hu(2) \<open>y \<in> (\<Pi>\<^sub>E i\<in>I. S i)\<close>)
            qed
          next
            have "openin (metric_set.mtopology (S i) (d i)) (metric_set.open_ball (S i) (d i) (x i) \<epsilon>')" if "i \<in> I" for i
              by (meson PiE_E h\<epsilon>' hx(2) metric_set.mtopology_open_ball_in sd_metric that)
            moreover have "openin (metric_set.mtopology (S i) (d i)) (topspace (metric_set.mtopology (S i) (d i)))" for i
              by auto
            ultimately show "\<forall>i. openin (metric_set.mtopology (S i) (d i)) (X i)"
              by(auto simp: X_def)
          next
            show "finite {i. X i \<noteq> topspace (metric_set.mtopology (S i) (d i))}"
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
          then have "U = (\<Pi>\<^sub>E i\<in>I. S i)"
            unfolding hu(1) using order.strict_trans1[OF product_dist_leqr,of \<epsilon>] hu(2)
            by(simp add: open_ball_def)
          also have "... = (\<Pi>\<^sub>E i\<in>I. topspace (metric_set.mtopology (S i) (d i)))"
            using htopspace by auto
          finally have "U = (\<Pi>\<^sub>E i\<in>I. topspace (metric_set.mtopology (S i) (d i)))" .
          thus ?thesis
            using open_ballD'(1)[OF that[simplified hu(1)]] htopspace by(auto intro!: exI[where x="\<lambda>i. topspace (metric_set.mtopology (S i) (d i))"])
        qed
      qed
      hence "\<exists>X. \<forall>x\<in>U. x \<in> (\<Pi>\<^sub>E i\<in>I. X x i) \<and> (\<Pi>\<^sub>E i\<in>I. X x i) \<subseteq> U \<and> (\<forall>i. openin (metric_set.mtopology (S i) (d i)) (X x i)) \<and> finite {i. X x i \<noteq> topspace (metric_set.mtopology (S i) (d i))}"
        by(auto intro!: bchoice)
      then obtain X where "\<forall>x\<in>U. x \<in> (\<Pi>\<^sub>E i\<in>I. X x i) \<and> (\<Pi>\<^sub>E i\<in>I. X x i) \<subseteq> U \<and> (\<forall>i. openin (metric_set.mtopology (S i) (d i)) (X x i)) \<and> finite {i. X x i \<noteq> topspace (metric_set.mtopology (S i) (d i))}"
        by auto
      hence hX: "\<And>x. x \<in> U \<Longrightarrow> x \<in> (\<Pi>\<^sub>E i\<in>I. X x i)" "\<And>x. x \<in> U \<Longrightarrow> (\<Pi>\<^sub>E i\<in>I. X x i) \<subseteq> U"  "\<And>x. x \<in> U \<Longrightarrow> (\<forall>i. openin (metric_set.mtopology (S i) (d i)) (X x i))" "\<And>x. x \<in> U \<Longrightarrow> finite {i. X x i \<noteq> topspace (metric_set.mtopology (S i) (d i))}"
        by auto
      hence hXopen: "\<And>x. x \<in> U \<Longrightarrow> (\<Pi>\<^sub>E i\<in>I. X x i) \<in> {\<Pi>\<^sub>E i\<in>I. X i |X. (\<forall>i. openin (metric_set.mtopology (S i) (d i)) (X i)) \<and> finite {i. X i \<noteq> topspace (metric_set.mtopology (S i) (d i))}}"
        by blast
      have "U = (\<Union> {(\<Pi>\<^sub>E i\<in>I. X x i) | x. x \<in> U})"
        using hX(1,2) by blast
      have "openin (topology_generated_by {\<Pi>\<^sub>E i\<in>I. X i |X. (\<forall>i. openin (metric_set.mtopology (S i) (d i)) (X i)) \<and> finite {i. X i \<noteq> topspace (metric_set.mtopology (S i) (d i))}}) (\<Union> {(\<Pi>\<^sub>E i\<in>I. X x i) | x. x \<in> U})"
        apply(rule openin_Union)
        using hXopen by(auto simp: openin_topology_generated_by_iff intro!: generate_topology_on.Basis)
      thus "openin (topology_generated_by {\<Pi>\<^sub>E i\<in>I. X i |X. (\<forall>i. openin (metric_set.mtopology (S i) (d i)) (X i)) \<and> finite {i. X i \<noteq> topspace (metric_set.mtopology (S i) (d i))}}) U"
        using \<open>U = (\<Union> {(\<Pi>\<^sub>E i\<in>I. X x i) | x. x \<in> U})\<close> by simp
    next
      fix U
      assume "U \<in> {\<Pi>\<^sub>E i\<in>I. X i |X. (\<forall>i. openin (metric_set.mtopology (S i) (d i)) (X i)) \<and> finite {i. X i \<noteq> topspace (metric_set.mtopology (S i) (d i))}}"
      then obtain X where hX:
       "U = (\<Pi>\<^sub>E i\<in>I. X i)" "\<And>i. openin (metric_set.mtopology (S i) (d i)) (X i)" "finite {i. X i \<noteq> topspace (metric_set.mtopology (S i) (d i))}"
        by auto
      have "\<exists>a \<epsilon>. x \<in> open_ball a \<epsilon> \<and> open_ball a \<epsilon> \<subseteq> U" if "x \<in> U" for x
      proof -
        have x_intop:"x \<in> (\<Pi>\<^sub>E i\<in>I. S i)"
          unfolding htopspace'[symmetric] using that hX(1) openin_subset[OF hX(2)] by auto
        define I' where "I' \<equiv> {i. X i \<noteq> topspace (metric_set.mtopology (S i) (d i))} \<inter> I"
        then have I':"finite I'" "I' \<subseteq> I" using hX(3) by auto
        consider "I' = {}" | "I' \<noteq> {}" by auto
        then show ?thesis
        proof cases
          case 1
          then have "\<And>i. i \<in> I \<Longrightarrow> X i = topspace (metric_set.mtopology (S i) (d i))"
            by(auto simp: I'_def)
          then have "U = (\<Pi>\<^sub>E i\<in>I. S i)"
            by (simp add: PiE_eq hX(1) htopspace)
          thus ?thesis
            using open_ball_subset_ofS[of x 1] that
            by(auto intro!: exI[where x=x] exI[where x=1])
        next
          case I'_nonempty:2
          hence "\<And>i. i \<in> I' \<Longrightarrow> openin (metric_set.mtopology (S i) (d i)) (X i)"
            using hX(2) by(simp add: I'_def)
          hence "\<exists>\<epsilon>>0. metric_set.open_ball (S i) (d i) (x i) \<epsilon> \<subseteq> (X i)" if "i \<in> I'" for i
            using metric_set.mtopology_openin_iff[of "S i" "d i" "X i"] sd_metric[of i] hX(1,2) \<open>x \<in> U\<close> that
            using I'_def by blast
          then obtain \<epsilon>i' where hei:"\<And>i. i \<in> I' \<Longrightarrow> \<epsilon>i' i > 0" "\<And>i. i \<in> I' \<Longrightarrow> metric_set.open_ball (S i) (d i) (x i) (\<epsilon>i' i) \<subseteq> (X i)"
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
            assume "y \<in> open_ball x (\<epsilon> * r ^ n)"
            have "y i \<in> X i" if "i \<in> I'" for i
            proof -
              interpret mi: metric_set "S i" "d i"
                using sd_metric that by(simp add: I'_def)
              have "d i (x i) (y i) < \<epsilon>i' i"
              proof -
                have "d i (x i) (y i) \<le> (1 / r) ^ f i * product_dist x y"
                  using that by(auto intro!: product_dist_geq[of i,OF  _ gf_comp_id x_intop open_ballD'(1)[OF \<open>y \<in> open_ball x (\<epsilon> * r ^ n)\<close>]] simp: I'_def)
                also have "... \<le> (1 / r)^n * product_dist x y"
                  by(rule mult_right_mono[OF hn2[OF that] dist_geq0])
                also have "... <  \<epsilon>"
                  using open_ballD[OF \<open>y \<in> open_ball x (\<epsilon> * r ^ n)\<close>] r
                  by (simp add: pos_divide_less_eq power_one_over)
                also have "... \<le> \<epsilon>i' i"
                  by(rule \<epsilon>min[OF that])
                finally show ?thesis .
              qed
              hence "(y i) \<in> mi.open_ball (x i) (\<epsilon>i' i)"
                using open_ballD'(1)[OF \<open>y \<in> open_ball x (\<epsilon> * r ^ n)\<close>] x_intop that
                by(auto simp: mi.open_ball_def I'_def)
              thus ?thesis
                using hei[OF that] by auto
            qed
            moreover have "y i \<in> X i" if "i \<in> I - I'" for i
              using that htopspace open_ballD'(1)[OF \<open>y \<in> open_ball x (\<epsilon> * r ^ n)\<close>]
              by(auto simp: I'_def)
            ultimately show "y \<in> U"
              using open_ballD'(1)[OF \<open>y \<in> open_ball x (\<epsilon> * r ^ n)\<close>]
              by(auto simp: hX(1))
          qed(use open_ball_ina[OF x_intop h\<epsilon>'] in auto)
        qed
      qed
      then obtain a where "\<forall>x\<in>U. \<exists>\<epsilon>. x \<in> open_ball (a x) \<epsilon> \<and> open_ball (a x) \<epsilon> \<subseteq> U"
        by metis
      then obtain \<epsilon> where hae: "\<And>x. x \<in> U \<Longrightarrow> x \<in> open_ball (a x) (\<epsilon> x)" "\<And>x. x \<in> U \<Longrightarrow> open_ball (a x) (\<epsilon> x) \<subseteq> U"
        by metis
      hence hae': "\<And>x. x \<in> U \<Longrightarrow> a x \<in> (\<Pi>\<^sub>E i\<in>I. S i)" "\<And>x. x \<in> U \<Longrightarrow> 0 < \<epsilon> x"
        using open_ballD'(2) by meson (use open_ballD'(2,3) hae in meson)
      have "openin (topology_generated_by {open_ball a \<epsilon> |a \<epsilon>. a \<in> (\<Pi>\<^sub>E i\<in>I. S i) \<and> 0 < \<epsilon>}) (\<Union> { open_ball (a x) (\<epsilon> x) |x. x \<in> U})"
        by(auto intro!: openin_Union[of _ mtopology] simp: mtopology_def2[symmetric] hae' metric_set_axioms metric_set.mtopology_open_ball_in)
      moreover have "U = (\<Union> {open_ball (a x) (\<epsilon> x) |x. x \<in> U})"
        using hae by auto
      ultimately show "openin (topology_generated_by {open_ball a \<epsilon> |a \<epsilon>. a \<in> (\<Pi>\<^sub>E i\<in>I. S i) \<and> 0 < \<epsilon>}) U"
        by simp
    qed
  qed
qed

end

lemma product_metricI:
  assumes "0 < r" "r < 1" "countable I" "\<And>i. i \<in> I \<Longrightarrow> metric_set (S i) (d i)"
      and "\<And>i x y. 0 \<le> d i x y" "\<And>i x y. d i x y \<le> K" "0 < K"
    shows "product_metric r I (to_nat_on I) (from_nat_into I) S d K"
  using from_nat_into_to_nat_on_product_metric_pair[OF assms(3)] assms
  by(simp add:  product_metric_def  metric_set_def)

(* TODO add lemmas for above metric *)

text \<open> Case: all $(S_i,d_i)$ are separable metric spaces.\<close>
locale product_separable_metric = product_metric +
  assumes sd_separable_metric: "\<And>i. i \<in> I \<Longrightarrow> separable_metric_set (S i) (d i)"
begin

sublocale separable_metric_set "\<Pi>\<^sub>E i\<in>I. S i" product_dist
proof -
  have "\<And>i. i \<in> I \<Longrightarrow> second_countable (metric_set.mtopology (S i) (d i))"
    by (simp add: sd_separable_metric separable_metric_set.second_countable)
  hence "second_countable (product_topology (\<lambda>i. metric_set.mtopology (S i) (d i)) I)"
    by(rule product_topology_second_countable[OF I])
  hence "second_countable (metric_set.mtopology (Pi\<^sub>E I S) product_dist)"
    using product_dist_mtopology sd_metric
    by(simp add: separable_metric_set_def)
  thus "separable_metric_set (\<Pi>\<^sub>E i\<in>I. S i) product_dist"
    by (meson I d_bound d_nonneg metric_set.separable_if_second_countable product_dist_distance r(1) r(2) sd_metric second_countable_def separable_metric_set.axioms(1))
qed

end

text \<open> Case: all $(S_i,d_i)$ are complete metric spaces.\<close>
locale product_complete_metric = product_metric +
  assumes sd_complete_metric: "\<And>i. i \<in> I \<Longrightarrow> complete_metric_set (S i) (d i)"
begin

lemma product_dist_complete':
  assumes "I \<noteq> {}"
  shows "complete_metric_set (\<Pi>\<^sub>E i\<in>I. S i) product_dist"
proof -
  show ?thesis
  proof
    fix k
    assume h:"Cauchy_inS k"
    have *:"i \<in> I \<Longrightarrow> metric_set.Cauchy_inS (S i) (d i) (\<lambda>n. k n i)" for i
    proof -
      assume hi:"i \<in> I"
      then interpret mi: complete_metric_set "S i" "d i"
        by(simp add: sd_complete_metric)
      show "mi.Cauchy_inS (\<lambda>n. k n i)"
        unfolding mi.Cauchy_inS_def2''
      proof
        show "(\<lambda>n. k n i) \<in> mi.sequence"
          using h hi by(auto simp: Cauchy_inS_def)
      next
        show "\<forall>\<epsilon>>0. \<exists>x\<in>S i. \<exists>N. \<forall>n\<ge>N. d i x (k n i) < \<epsilon>"
        proof safe
          fix \<epsilon>
          assume he:"(0::real) < \<epsilon>"
          then have "0 < \<epsilon> * r^(f i)" using r by auto
          then obtain x N where hxn:
           "x\<in>(\<Pi>\<^sub>E i\<in>I. S i)" "\<And>n. n\<ge>N \<Longrightarrow> product_dist x (k n) < \<epsilon> * r^(f i)"
            using h[simplified Cauchy_inS_def2''] by blast
          hence hxn':"\<And>n. n\<ge>N \<Longrightarrow> (1/r)^(f i) * product_dist x (k n) < \<epsilon>"
            by (simp add: pos_divide_less_eq power_divide r(1))
          show "\<exists>x\<in>S i. \<exists>N. \<forall>n\<ge>N. d i x (k n i) < \<epsilon>"
          proof(safe intro!: bexI[where x="x i"] exI[where x=N])
            show "x i \<in> S i"
              using hi hxn by auto
          next
            fix n
            assume hnn:"N \<le> n"
            have hf:"k n \<in> (\<Pi>\<^sub>E i\<in>I. S i)"
              using h by(auto simp: Cauchy_inS_def)
            have "d i (x i) (k n i) \<le> (1/r)^(f i) * product_dist x (k n)"
              using product_dist_geq[OF hi gf_comp_id[OF hi] hxn(1) hf]
              by simp
            also have "... < \<epsilon>"
              using hxn'[OF hnn] .
            finally show "d i (x i) (k n i) < \<epsilon>" .
          qed
        qed
      qed
    qed
    have "\<exists>x. metric_set.converge_to_inS (S i) (d i) (\<lambda>n. k n i) x" if "i \<in> I" for i
      using complete_metric_set.convergence[OF sd_complete_metric[OF that] *[OF that]] metric_set.convergent_inS_def[OF sd_metric[OF that]]
      by auto
    then obtain x where hx:"\<And>i. i \<in> I \<Longrightarrow> metric_set.converge_to_inS (S i) (d i) (\<lambda>n. k n i) (x i)"
      by metis
    have hx':"(\<lambda>i\<in>I. x i) \<in> (\<Pi>\<^sub>E i\<in>I. S i)"
      using hx metric_set.converge_to_inS_def[OF sd_metric] by auto
    show "convergent_inS k"
      using converge_to_iff[OF _ hx',of k]
      by(auto intro!: exI[where x="\<lambda>i\<in>I. x i"] simp: h[simplified Cauchy_inS_def] hx convergent_inS_def)
  qed
qed

sublocale complete_metric_set "\<Pi>\<^sub>E i\<in>I. S i" product_dist
proof -
  consider "I = {}" | "I \<noteq> {}" by auto
  then show "complete_metric_set (\<Pi>\<^sub>E i\<in>I. S i) product_dist"
  proof cases
    case 1
    then have "product_dist = (\<lambda>x y. 0)"
      using metric_set_axioms singleton_metric_unique[of "\<lambda>x. undefined"] by auto
    with 1 singleton_metric_polish[of "\<lambda>x. undefined"]
    show ?thesis by(auto simp: polish_metric_set_def)
  next
    case 2
    with product_dist_complete' show ?thesis by simp
  qed
qed

end

lemma product_complete_metricI:
  assumes "0 < r" "r < 1" "countable I" "\<And>i. i \<in> I \<Longrightarrow> complete_metric_set (S i) (d i)"
      and "\<And>i x y. 0 \<le> d i x y" "\<And>i x y. d i x y \<le> K" "0 < K"
    shows "product_complete_metric r I (to_nat_on I) (from_nat_into I) S d K"
  using from_nat_into_to_nat_on_product_metric_pair[OF assms(3)] assms
  by(simp add: product_complete_metric_def product_metric_def product_complete_metric_axioms_def complete_metric_set_def)

lemma product_complete_metric_natI:
  assumes "0 < r" "r < 1" "\<And>n. complete_metric_set (S n) (d n)"
      and "\<And>i x y. 0 \<le> d i x y" "\<And>i x y. d i x y \<le> K" "0 < K"
    shows "product_complete_metric r UNIV id id S d K"
  using assms by(simp add: product_complete_metric_def product_metric_def product_complete_metric_axioms_def polish_metric_set_def complete_metric_set_def)

locale product_polish_metric = product_complete_metric + product_separable_metric
begin

sublocale polish_metric_set "\<Pi>\<^sub>E i\<in>I. S i" product_dist
  by (simp add: complete_metric_set_axioms polish_metric_set_def separable_metric_set_axioms)

end

lemma product_polish_metricI:
  assumes "0 < r" "r < 1" "countable I" "\<And>i. i \<in> I \<Longrightarrow> polish_metric_set (S i) (d i)"
      and "\<And>i x y. 0 \<le> d i x y" "\<And>i x y. d i x y \<le> K" "0 < K"
    shows "product_polish_metric r I (to_nat_on I) (from_nat_into I) S d K"
  using from_nat_into_to_nat_on_product_metric_pair[OF assms(3)] assms
  by(simp add: product_polish_metric_def product_complete_metric_def product_separable_metric_def product_metric_def product_complete_metric_axioms_def product_separable_metric_axioms_def polish_metric_set_def complete_metric_set_def)

lemma product_polish_metric_natI:
  assumes "0 < r" "r < 1" "\<And>n. polish_metric_set (S n) (d n)"
      and "\<And>i x y. 0 \<le> d i x y" "\<And>i x y. d i x y \<le> K" "0 < K"
    shows "product_polish_metric r UNIV id id S d K"
  using assms by(simp add: product_polish_metric_def product_complete_metric_def product_separable_metric_def product_metric_def product_complete_metric_axioms_def product_separable_metric_axioms_def polish_metric_set_def complete_metric_set_def)

text \<open> Define a bounded distance function from a distance function \<close>
definition bounded_dist :: "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real" where
"bounded_dist d \<equiv> (\<lambda>a b. d a b / (1 + d a b))"

lemma bounded_dist_mono:
  fixes r l :: real
  assumes "0 \<le> r" "0 \<le> l" and "r \<le> l"
  shows "r / (1 + r) \<le> l / (1 + l)"
proof -
  have "(1 + l) * r \<le> l* (1 + r)"
    using assms by (simp add: distrib_left distrib_right)
  hence "((1 + l) * r) * (1 / (1 + r)) \<le> (l * (1 + r))  * (1 / (1 + r))"
    using linordered_ring_strict_class.mult_le_cancel_right[of "(1 + l) * r" "1 / (1 + r)" "l * (1 + r)"] assms(1)
    by auto
  hence "(1 / (1 + l)) * (((1 + l) * r) * (1 / (1 + r))) \<le> (1 / (1 + l)) * ((l * (1 + r))  * (1 / (1 + r)))"
    using linordered_ring_strict_class.mult_le_cancel_left[of "1 / (1 + l)" "((1 + l) * r) * (1 / (1 + r))" "(l * (1 + r))  * (1 / (1 + r))"] assms(2)
    by auto
  thus ?thesis
    using assms by auto
qed

lemma bounded_dist_mono_strict:
  fixes r l :: real
  assumes "0 \<le> r" "0 \<le> l" and "r < l"
  shows "r / (1 + r) < l / (1 + l)"
proof -
  have "(1 + l) * r < l* (1 + r)"
    using assms by (simp add: distrib_left distrib_right)
  hence "((1 + l) * r) * (1 / (1 + r)) < (l * (1 + r))  * (1 / (1 + r))"
    using linordered_ring_strict_class.mult_less_cancel_right[of "(1 + l) * r" "1 / (1 + r)" "l * (1 + r)"] assms(1)
    by auto
  hence "(1 / (1 + l)) * (((1 + l) * r) * (1 / (1 + r))) < (1 / (1 + l)) * ((l * (1 + r))  * (1 / (1 + r)))"
    using linordered_ring_strict_class.mult_less_cancel_left[of "1 / (1 + l)" "((1 + l) * r) * (1 / (1 + r))" "(l * (1 + r))  * (1 / (1 + r))"] assms(2)
    by auto
  thus ?thesis
    using assms by auto
qed

lemma bounded_dist_mono_inverse:
  fixes r l :: real
  assumes "0 \<le> r" "0 \<le> l" and "r / (1 + r) \<le> l / (1 + l)"
  shows "r \<le> l"
proof -
  have "(1 / (1 + l)) * (((1 + l) * r) * (1 / (1 + r))) \<le> (1 / (1 + l)) * ((l * (1 + r))  * (1 / (1 + r)))"
    using assms by auto
  hence "((1 + l) * r) * (1 / (1 + r)) \<le> (l * (1 + r))  * (1 / (1 + r))"
    using linordered_ring_strict_class.mult_le_cancel_left[of "1 / (1 + l)" "((1 + l) * r) * (1 / (1 + r))" "(l * (1 + r))  * (1 / (1 + r))"] assms(2)
    by auto
  hence "(1 + l) * r \<le> l* (1 + r)"
    using linordered_ring_strict_class.mult_le_cancel_right[of "(1 + l) * r" "1 / (1 + r)" "l * (1 + r)"] assms(1)
    by auto
  thus ?thesis
    using assms by (simp add: distrib_left distrib_right)
qed

lemma bounded_dist_mono_strict_inverse:
  fixes r l :: real
  assumes "0 \<le> r" "0 \<le> l" and "r / (1 + r) < l / (1 + l)"
  shows "r < l"
proof -
  have "(1 / (1 + l)) * (((1 + l) * r) * (1 / (1 + r))) < (1 / (1 + l)) * ((l * (1 + r))  * (1 / (1 + r)))"
    using assms by auto
  hence "((1 + l) * r) * (1 / (1 + r)) < (l * (1 + r))  * (1 / (1 + r))"
    using linordered_ring_strict_class.mult_less_cancel_left[of "1 / (1 + l)" "((1 + l) * r) * (1 / (1 + r))" "(l * (1 + r))  * (1 / (1 + r))"] assms(2)
    by auto
  hence "(1 + l) * r < l* (1 + r)"
    using linordered_ring_strict_class.mult_less_cancel_right[of "(1 + l) * r" "1 / (1 + r)" "l * (1 + r)"] assms(1)
    by auto
  thus ?thesis
    using assms by (simp add: distrib_left distrib_right)
qed

lemma bounded_dist_inverse_comp:
  fixes \<epsilon> :: real
  assumes "0 < \<epsilon>" and "\<epsilon> < 1"
  shows "\<epsilon> = (\<epsilon> / (1 - \<epsilon>)) / (1 + (\<epsilon> / (1 - \<epsilon>)))"
        (is "_ = ?\<epsilon>' / (1 + ?\<epsilon>')")
proof -
  have "1 + \<epsilon> / (1 - \<epsilon>) = (1 - \<epsilon>) / (1 - \<epsilon>) + \<epsilon> / (1 - \<epsilon>)"
    using assms by auto
  also have "... = 1 / (1 - \<epsilon>)"
    by(simp only: division_ring_class.add_divide_distrib[symmetric], simp)
  finally show "\<epsilon> = ?\<epsilon>' / (1 + ?\<epsilon>')"
    using assms by simp
qed

lemma(in metric_set) bounded_dist_dist:
  shows "metric_set S (bounded_dist dist)"
    and "bounded_dist dist a b < 1"
proof -
  show "metric_set S (bounded_dist dist)"
  proof
    show "\<And>x y. 0 \<le> bounded_dist dist x y"
         "\<And>x y. x \<notin> S \<Longrightarrow> bounded_dist dist x y = 0"
         "\<And>x y. bounded_dist dist x y = bounded_dist dist y x"
      using dist_geq0 dist_notin dist_sym
      by(auto simp: bounded_dist_def)
  next
    fix x y
    assume hxy:"x \<in> S" "y \<in> S"
    show "x = y \<longleftrightarrow> (bounded_dist dist x y = 0)"
    proof
      assume "bounded_dist dist x y = 0"
      then have "dist x y / (1 + dist x y) = 0"
        by(simp add: bounded_dist_def)
      hence "dist x y = 0"
        using field_class.divide_eq_0_iff[of "d x y"] dist_geq0
        by (simp add: add_nonneg_eq_0_iff)
      thus "x = y"
        using dist_0[OF hxy] by simp
    qed (simp add: bounded_dist_def dist_0[OF hxy])
  next
    fix x y z
    assume hxyz:"x \<in> S" "y \<in> S" "z \<in> S"
    have "bounded_dist dist x z \<le> (dist x y + dist y z) / (1 + dist x y + dist y z)"
      using bounded_dist_mono[OF _ _ dist_tr[OF hxyz],simplified semigroup_add_class.add.assoc[symmetric]] dist_geq0
      by(simp add: bounded_dist_def)
    also have "... = dist x y / (1 + dist x y + dist y z) + dist y z / (1 + dist x y + dist y z)"
      using add_divide_distrib by auto
    also have "... \<le> bounded_dist dist x y + bounded_dist dist y z"
      apply(rule add_mono_thms_linordered_semiring(1))
      unfolding bounded_dist_def
      using dist_geq0
      by(auto intro!: linordered_field_class.divide_left_mono linordered_semiring_strict_class.mult_pos_pos add_pos_nonneg )
    finally show "bounded_dist dist x z \<le> bounded_dist dist x y + bounded_dist dist y z" .
  qed
  show "bounded_dist dist a b < 1"
    using dist_geq0[of a b] by(auto simp: bounded_dist_def)
qed

lemma(in metric_set) bounded_dist_ball_eq:
  assumes "x \<in> S" and "\<epsilon> > 0"
  shows "open_ball x \<epsilon> = metric_set.open_ball S (bounded_dist dist) x (\<epsilon> / (1 + \<epsilon>))"
proof(rule set_eqI)
  interpret m2: metric_set S "bounded_dist dist"
    by(rule bounded_dist_dist)
  fix y
  have "y \<in> open_ball x \<epsilon> \<longleftrightarrow> y \<in> S \<and> dist x y < \<epsilon>"
    using assms by(simp add: open_ball_def)
  also have "... \<longleftrightarrow> y \<in> S \<and> dist x y / (1 + dist x y) < \<epsilon> / (1 + \<epsilon>)"
    using bounded_dist_mono_strict[of "dist x y" \<epsilon>] bounded_dist_mono_strict_inverse[of "dist x y" \<epsilon>] dist_geq0 assms(2)
    by auto
  also have "... \<longleftrightarrow> y \<in> m2.open_ball x (\<epsilon> / (1 + \<epsilon>))"
    using assms by(simp add: m2.open_ball_def,simp add: bounded_dist_def)
  finally show "y \<in> open_ball x \<epsilon> \<longleftrightarrow> y \<in> m2.open_ball x (\<epsilon> / (1 + \<epsilon>))" .
qed

lemma(in metric_set) bounded_dist_ball_ge1:
  assumes "x \<in> S" and "1 \<le> \<epsilon>"
  shows "metric_set.open_ball S (bounded_dist dist) x \<epsilon> = S"
proof -
  interpret m2: metric_set S "bounded_dist dist"
    by(rule bounded_dist_dist)
  show ?thesis
    using order.strict_trans2[OF bounded_dist_dist(2)[of x] assms(2)] assms(1)
    by(auto simp: m2.open_ball_def)
qed

lemma(in metric_set) bounded_dist_generate_same_topology:
  "mtopology = metric_set.mtopology S (bounded_dist dist)"
proof -
  interpret m2: metric_set S "bounded_dist dist"
    by(rule bounded_dist_dist)
  show ?thesis
  proof(rule metric_generates_same_topology[OF metric_set_axioms bounded_dist_dist(1)])
    fix x U
    assume h: "U \<subseteq> S" "\<forall>x\<in>U. \<exists>\<epsilon>>0. open_ball x \<epsilon> \<subseteq> U" "x \<in> U"
    then obtain \<epsilon> where he:
       "\<epsilon> > 0" "open_ball x \<epsilon> \<subseteq> U" by auto
    show "\<exists>\<epsilon>>0. m2.open_ball x \<epsilon> \<subseteq> U"
      using he bounded_dist_ball_eq[of x \<epsilon>] h
      by(auto intro!: exI[where x="\<epsilon> / (1 + \<epsilon>)"])
  next
    fix x U
    assume h: "U \<subseteq> S" "\<forall>x\<in>U. \<exists>\<epsilon>>0. m2.open_ball x \<epsilon> \<subseteq> U" "x \<in> U"
    then obtain \<epsilon> where he:
       "\<epsilon> > 0" "m2.open_ball x \<epsilon> \<subseteq> U" by auto
    consider "\<epsilon> < 1" | "1 \<le> \<epsilon>" by fastforce
    then show "\<exists>\<epsilon>>0. open_ball x \<epsilon> \<subseteq> U"
    proof cases
      case 1
      let ?\<epsilon>' = "\<epsilon> / (1 - \<epsilon>)"
      note 2 = bounded_dist_inverse_comp[OF he(1) 1]
      have 3:"0 < ?\<epsilon>'"
        using he 1 by auto
      show ?thesis
        using h(1,3) he(2) 3 bounded_dist_ball_eq[of x ?\<epsilon>',simplified 2[symmetric]]
        by(auto intro!: exI[where x="?\<epsilon>'"])
    next
      case 2
      have "U = S"
        using bounded_dist_ball_ge1[of x,OF _ 2] h(1,3) he(2)
        by auto
      thus ?thesis
        using open_ball_subset_ofS
        by(auto intro!: exI[where x=1])
    qed
  qed
qed

lemma(in metric_set) bounded_dist_converge_to_inS_iff:
 "converge_to_inS xn x \<longleftrightarrow> metric_set.converge_to_inS S (bounded_dist dist) xn x"
  by(simp add: metric_generates_same_topology_converges[OF metric_set_axioms bounded_dist_dist(1) bounded_dist_generate_same_topology])

lemma(in metric_set) bounded_dist_Cauchy_eq:
 "Cauchy_inS f \<longleftrightarrow> metric_set.Cauchy_inS S (bounded_dist dist) f"
proof -
  interpret m2: metric_set S "bounded_dist dist"
    by(rule bounded_dist_dist)
  show ?thesis
  proof
    assume h:"Cauchy_inS f"
    show "m2.Cauchy_inS f"
      unfolding m2.Cauchy_inS_def2'
    proof safe
      fix \<epsilon> :: real
      assume he: "0 < \<epsilon>"
      consider "\<epsilon> < 1" | "1 \<le> \<epsilon>" by fastforce
      then show "\<exists>x\<in>S. \<exists>N. \<forall>n\<ge>N. f n \<in> m2.open_ball x \<epsilon>"
      proof cases
        case 1
        let ?\<epsilon> = "\<epsilon> / (1 - \<epsilon>)"
        note 2 = bounded_dist_inverse_comp[OF he(1) 1]
        have 3:"0 < ?\<epsilon>"
          using he 1 by auto
        then obtain x N where hxn:
         "x \<in> S" "\<And>n. n\<ge>N \<Longrightarrow> f n \<in> open_ball x ?\<epsilon>"
          using Cauchy_inS_def2'[of f] h by blast
        show ?thesis
          using hxn bounded_dist_ball_eq[OF hxn(1) 3,simplified 2[symmetric]]
          by(auto intro!: bexI[where x=x] exI[where x=N])
      next
        case 2
        then show ?thesis
          using bounded_dist_ball_ge1[of "f 0" \<epsilon>] Cauchy_inS_def2'[of f] h
          by(auto intro!: bexI[where x="f 0"] exI[where x=0])
      qed
    qed(rule Cauchy_inS_dest1[OF h])
  next
    assume h:"m2.Cauchy_inS f"
    show "Cauchy_inS f"
      unfolding Cauchy_inS_def2'
    proof safe
      fix \<epsilon> :: real
      assume he:"0 < \<epsilon>"
      then have "0 < \<epsilon> / (1 + \<epsilon>)" by simp
      then obtain x N where
       "x \<in> S" "\<And>n. n \<ge>N \<Longrightarrow> f n \<in> m2.open_ball x (\<epsilon> / (1 + \<epsilon>))"
        using h[simplified m2.Cauchy_inS_def2'] by blast
      thus "\<exists>x\<in>S. \<exists>N. \<forall>n\<ge>N. f n \<in> open_ball x \<epsilon>"
        using he bounded_dist_ball_eq[of x \<epsilon>]
        by(auto intro!: bexI[where x=x] exI[where x=N])
    qed(rule m2.Cauchy_inS_dest1[OF h])
  qed
qed

lemma(in complete_metric_set) bounded_dist_complete:
 "complete_metric_set S (bounded_dist dist)"
  unfolding complete_metric_set_def complete_metric_set_axioms_def
  by(auto intro!: bounded_dist_dist convergence simp: bounded_dist_Cauchy_eq[symmetric] metric_generates_same_topology_convergent[OF metric_set_axioms bounded_dist_dist(1) bounded_dist_generate_same_topology,symmetric])

lemma(in polish_metric_set) bounded_dist_polish:
 "polish_metric_set S (bounded_dist dist)"
  unfolding polish_metric_set_def
  using metric_generates_same_topology_separable[OF metric_set_axioms bounded_dist_dist(1) bounded_dist_generate_same_topology]
  by(auto intro!: bounded_dist_complete separable_metric_set_axioms)

lemma(in metric_set) uniform_continuous_map_bounded_dist_equiv:
  assumes "metric_set T f"
  shows "uniform_continuous_map S dist T f = uniform_continuous_map S (bounded_dist dist) T f"
proof
  fix g
  interpret bS: metric_set S "bounded_dist dist"
    by (rule bounded_dist_dist(1))
  interpret T: metric_set T f by fact
  show "uniform_continuous_map S dist T f g = uniform_continuous_map S (bounded_dist dist) T f g"
    unfolding uniform_continuous_map_def[OF metric_set_axioms T.metric_set_axioms] uniform_continuous_map_def[OF bS.metric_set_axioms T.metric_set_axioms]
  proof safe
    fix e :: real
    assume h: "e > 0" "g \<in> S \<rightarrow> T" "\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>x\<in>S. \<forall>y\<in>S. dist x y < \<delta> \<longrightarrow> f (g x) (g y) < \<epsilon>"
    with h(3) obtain d where d: "d > 0" "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> dist x y < d \<Longrightarrow> f (g x) (g y) < e"
      by metis
    consider "d \<ge> 1" | "d < 1" by fastforce
    show "\<exists>\<delta>>0. \<forall>x\<in>S. \<forall>y\<in>S. bounded_dist dist x y < \<delta> \<longrightarrow> f (g x) (g y) < e"
    proof(safe intro!: exI[where x="d / (1 + d)"])
      fix x y
      assume xy:"x \<in> S" "y \<in> S" " bounded_dist dist x y < d / (1 + d)"
      then have "dist x y < d"
        using d(1) dist_geq0 bounded_dist_mono_strict_inverse[of "dist x y" d] by(auto simp: bounded_dist_def)
      thus "f (g x) (g y) < e"
        by(auto intro!: d xy)
    qed(use d in auto)
  next
    fix e :: real
    assume h: "e > 0" "g \<in> S \<rightarrow> T" "\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>x\<in>S. \<forall>y\<in>S. bounded_dist dist x y < \<delta> \<longrightarrow> f (g x) (g y) < \<epsilon>"
    with h(3) obtain d where d: "d > 0" "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> bounded_dist dist x y < d \<Longrightarrow> f (g x) (g y) < e"
      by metis
    show "\<exists>\<delta>>0. \<forall>x\<in>S. \<forall>y\<in>S. dist x y < \<delta> \<longrightarrow> f (g x) (g y) < e"
    proof(safe intro!: exI[where x=d])
      fix x y
      assume xy: "x \<in> S" "y \<in> S" "dist x y < d"
      then have "bounded_dist dist x y < d"
        using dist_geq0[of x y] by(auto intro!: order.strict_trans1[OF divide_left_mono[OF le_add_same_cancel1[THEN iffD2,OF dist_geq0,of 1] dist_geq0],simplified] simp: bounded_dist_def)
      from d(2)[OF xy(1,2) this] show "f (g x) (g y) < e" .
    qed(use d in auto)
  qed
qed

lemma(in metric_set) uniform_continuous_map_bounded_dist_equiv':
  assumes "metric_set T f"
  shows "uniform_continuous_map S dist T f = uniform_continuous_map S (bounded_dist dist) T (bounded_dist f)"
proof
  fix g
  interpret bS: metric_set S "bounded_dist dist"
    by (rule bounded_dist_dist(1))
  interpret T: metric_set T f by fact
  interpret bT: metric_set T "bounded_dist f"
    by(rule T.bounded_dist_dist(1))
  show "uniform_continuous_map S dist T f g = uniform_continuous_map S (bounded_dist dist) T (bounded_dist f) g"
    unfolding uniform_continuous_map_def[OF metric_set_axioms T.metric_set_axioms] uniform_continuous_map_def[OF bS.metric_set_axioms bT.metric_set_axioms]
  proof safe
    fix e :: real
    assume h: "e > 0" "g \<in> S \<rightarrow> T" "\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>x\<in>S. \<forall>y\<in>S. dist x y < \<delta> \<longrightarrow> f (g x) (g y) < \<epsilon>"
    with h(3) obtain d where d: "d > 0" "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> dist x y < d \<Longrightarrow> f (g x) (g y) < e"
      by metis
    consider "d \<ge> 1" | "d < 1" by fastforce
    show "\<exists>\<delta>>0. \<forall>x\<in>S. \<forall>y\<in>S. bounded_dist dist x y < \<delta> \<longrightarrow> bounded_dist f (g x) (g y) < e"
    proof(safe intro!: exI[where x="d / (1 + d)"])
      fix x y
      assume xy:"x \<in> S" "y \<in> S" " bounded_dist dist x y < d / (1 + d)"
      then have "dist x y < d"
        using d(1) dist_geq0 bounded_dist_mono_strict_inverse[of "dist x y" d] by(auto simp: bounded_dist_def)
      then have "f (g x) (g y) < e"
        by(auto intro!: d xy)
      thus "bounded_dist f (g x) (g y) < e"
        using T.dist_geq0[of "g x" "g y"] by(auto intro!: order.strict_trans1[OF divide_left_mono[OF le_add_same_cancel1[THEN iffD2,OF T.dist_geq0,of 1] T.dist_geq0],simplified] simp: bounded_dist_def )
    qed(use d in auto)
  next
    fix e :: real
    assume h: "e > 0" "g \<in> S \<rightarrow> T" "\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>x\<in>S. \<forall>y\<in>S. bounded_dist dist x y < \<delta> \<longrightarrow> bounded_dist f (g x) (g y) < \<epsilon>"
    then have "e / (1 + e) > 0" by auto
    with h(3) obtain d where d: "d > 0" "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> bounded_dist dist x y < d \<Longrightarrow> bounded_dist f (g x) (g y) < e / (1 + e)"
      by metis
    show "\<exists>\<delta>>0. \<forall>x\<in>S. \<forall>y\<in>S. dist x y < \<delta> \<longrightarrow> f (g x) (g y) < e"
    proof(safe intro!: exI[where x=d])
      fix x y
      assume xy: "x \<in> S" "y \<in> S" "dist x y < d"
      then have "bounded_dist dist x y < d"
        using dist_geq0[of x y] by(auto intro!: order.strict_trans1[OF divide_left_mono[OF le_add_same_cancel1[THEN iffD2,OF dist_geq0,of 1] dist_geq0],simplified] simp: bounded_dist_def)
      from d(2)[OF xy(1,2) this] show "f (g x) (g y) < e"
        using h(1) T.dist_geq0 by(auto intro!: bounded_dist_mono_strict_inverse[of "f (g x) (g y)" e] simp: bounded_dist_def)
    qed(use d in auto)
  qed
qed

lemma(in metric_set) Urysohn_uniform:
  assumes "closedin mtopology T" "closedin mtopology U" "T \<inter> U = {}" "\<And>x y. x \<in> T \<Longrightarrow> y \<in> U \<Longrightarrow> dist x y \<ge> e" "e > 0"
  obtains f :: "'a \<Rightarrow> real"
  where "uniform_continuous_map S dist UNIV dist_typeclass f"
        "\<And>x. f x \<ge> 0" "\<And>x. f x \<le> 1" "\<And>x. x \<in> T \<Longrightarrow> f x = 1" "\<And>x. x \<in> U \<Longrightarrow> f x = 0"
proof -
  consider "T = {}" | "U = {}" | "T \<noteq> {}" "U \<noteq> {}" by auto
  then show ?thesis
  proof cases
    case 1
    define f where "f \<equiv> (\<lambda>x::'a. 0::real)"
    with 1 have "uniform_continuous_map S dist UNIV dist_typeclass f" "\<And>x. f x \<in>{0..1}" "\<And>x. x \<in> T \<Longrightarrow> f x = 1" "\<And>x. x \<in> U \<Longrightarrow> f x = 0"
      by(auto intro!: uniform_continuous_map_const[OF metric_set_axioms metric_class_metric_set] simp: f_def)
    then show ?thesis
      using that by auto
  next
    case 2
    define f where "f \<equiv> (\<lambda>x::'a. 1::real)"
    with 2 have "uniform_continuous_map S dist UNIV dist_typeclass f" "\<And>x. f x \<in>{0..1}" "\<And>x. x \<in> T \<Longrightarrow> f x = 1" "\<And>x. x \<in> U \<Longrightarrow> f x = 0"
      by(auto intro!: uniform_continuous_map_const[OF metric_set_axioms metric_class_metric_set] simp: f_def)
    then show ?thesis
      using that by auto
  next
    case TU:3
    then have STU:"S \<noteq> {}" "T \<subseteq> S" "U \<subseteq> S"
      using assms(1,2) closedin_topspace_empty mtopology_topspace closedin_subset by fastforce+
    interpret bd: metric_set S "bounded_dist dist"
      by (rule bounded_dist_dist(1))
    have e:"\<And>x y. x \<in> T \<Longrightarrow> y \<in> U \<Longrightarrow> bounded_dist dist x y \<ge> e / (1 + e)"
      using assms by(auto intro!: bounded_dist_mono simp: bounded_dist_def dist_geq0)
    define f where "f \<equiv> (\<lambda>x. bd.dist_set U x / (bd.dist_set U x + bd.dist_set T x))"
    have "uniform_continuous_map S dist UNIV dist_typeclass f"
      unfolding f_def
    proof(rule uniform_continuous_map_real_devide[where Kf=1 and Kg=2])
      show "uniform_continuous_map S dist UNIV dist_typeclass (bd.dist_set U)"
           "uniform_continuous_map S dist UNIV dist_typeclass (\<lambda>x. bd.dist_set U x + bd.dist_set T x)"
        by(auto simp: uniform_continuous_map_bounded_dist_equiv[OF metric_class_metric_set] bd.dist_set_uniform_continuous intro!: bd.uniform_continuous_map_add)
    next
      fix x
      assume x:"x \<in> S"
      consider "x \<in> (\<Union>a\<in>U. bd.open_ball a ((e / (1 + e)) / 2))" | "x \<notin> (\<Union>a\<in>U. bd.open_ball a ((e / (1 + e)) / 2))" by auto
      then show "(e / (1 + e)) / 2 \<le> \<bar>bd.dist_set U x + bd.dist_set T x\<bar>"
      proof cases
        case 1
        have "bd.open_ball x ((e / (1 + e)) / 2) \<inter> T = {}"
        proof(rule ccontr)
          assume "bd.open_ball x ((e / (1 + e)) / 2) \<inter> T \<noteq> {}"
          then obtain y where y:"y \<in> bd.open_ball x ((e / (1 + e)) / 2)" "y \<in> T"
            by auto
          obtain u where u:"u \<in> U" "x \<in> bd.open_ball u ((e / (1 + e)) / 2)"
            using 1 by auto
          have "bounded_dist dist y u \<le> bounded_dist dist y x + bounded_dist dist x u"
            using STU u y x by(auto intro!: bd.dist_tr)
          also have "... < (e / (1 + e)) / 2 + (e / (1 + e)) / 2"
            using bd.open_ballD[OF u(2)] bd.open_ballD[OF y(1)] by(simp add: bd.dist_sym)
          also have "... = e / (1 + e)" using assms(5) by linarith
          finally show False
            using  e[OF y(2) u(1)] by simp
        qed
        from bd.dist_set_ball_empty[OF TU(1) STU(2) _ x this] assms
        have "e / (1 + e) / 2 \<le> bd.dist_set T x" by auto
        also have "... \<le> \<bar>bd.dist_set U x + bd.dist_set T x\<bar>"
          using bd.dist_set_geq0 by auto
        finally show ?thesis .
      next
        case 2
        then have "bd.open_ball x ((e / (1 + e)) / 2) \<inter> U = {}"
          by(auto simp: bd.open_ball_inverse[of x])
        from bd.dist_set_ball_empty[OF TU(2) STU(3) _ x this] assms
        have "e / (1 + e) / 2 \<le> bd.dist_set U x" by auto
        also have "... \<le> \<bar>bd.dist_set U x + bd.dist_set T x\<bar>"
          using bd.dist_set_geq0 by auto
        finally show ?thesis .
      qed
      thus "bd.dist_set U x + bd.dist_set T x \<noteq> 0"
        using bd.dist_set_geq0 assms(5) order_antisym_conv by fastforce
    next
      show "0 < e / (1 + e) / 2"
        using assms by auto
    next
      fix x
      have "\<bar>bd.dist_set U x + bd.dist_set T x\<bar> = bd.dist_set U x + bd.dist_set T x"
        using bd.dist_set_geq0 by auto
      also have "... < 2"
        by (metis add_mono_thms_linordered_field(5) one_add_one bd.dist_set_bounded[OF bounded_dist_dist(2),simplified])
      finally show "\<bar>bd.dist_set U x + bd.dist_set T x\<bar> < 2" .
      show "\<bar>bd.dist_set U x\<bar> < 1"
        using bd.dist_set_geq0 bd.dist_set_bounded[OF bounded_dist_dist(2)] by auto
    qed
    moreover have "\<And>x. f x \<in>{0..1}"
      unfolding f_def
    proof -
      fix x
      have "bd.dist_set U x / (bd.dist_set U x + bd.dist_set T x) \<le> bd.dist_set U x / bd.dist_set U x"
      proof -
        consider "bd.dist_set U x = 0" | "bd.dist_set U x > 0"
          using bd.dist_set_geq0 by (auto simp: less_eq_real_def)
        thus ?thesis
        proof cases
          case 2
          show ?thesis
            by(rule divide_left_mono[OF _ _ mult_pos_pos]) (insert 2 bd.dist_set_geq0,simp_all add: add.commute add_nonneg_pos)
        qed simp
      qed
      also have "... \<le> 1" by simp
      finally show "bd.dist_set U x / (bd.dist_set U x + bd.dist_set T x) \<in> {0..1}"
        using bd.dist_set_geq0 by auto  
    qed      
    moreover have "f x = 1" if x:"x \<in> T" for x
    proof -
      { assume h:"bd.dist_set U x = 0"
        then have "x \<notin> U" using assms STU x by blast
        hence False
          using bd.dist_set_closed_ge0[simplified bounded_dist_generate_same_topology[symmetric],OF assms(2) TU(2),of x] STU h x
          by auto
      }
      thus ?thesis
        by(auto simp: f_def bd.dist_set_inA x)
    qed
    moreover have "\<And>x. x \<in> U \<Longrightarrow> f x = 0"
      by (auto simp: f_def bd.dist_set_inA)
    ultimately show ?thesis
      using that by auto
  qed
qed

lemma product_metricI':
  assumes "0 < r" "r < 1" "countable I" "\<And>i. i \<in> I \<Longrightarrow> metric_set (S i) (d i)"
  shows "product_metric r I (to_nat_on I) (from_nat_into I) S (\<lambda>i x y. if i \<in> I then bounded_dist (d i) x y else 0) 1"
proof -
  have "\<And>i. i \<in> I \<Longrightarrow> metric_set (S i) (bounded_dist (d i))"
       "\<And>i x y. i \<in> I \<Longrightarrow> bounded_dist (d i) x y \<le> 1"
    using assms(4) by(auto intro!: metric_set.bounded_dist_dist(1) less_imp_le[OF metric_set.bounded_dist_dist(2)])
  thus ?thesis
    by(auto intro!: product_metricI[OF assms(1-3)] simp: metric_set_def)
qed

lemma product_complete_metricI':
  assumes "0 < r" "r < 1" "countable I" "\<And>i. i \<in> I \<Longrightarrow> complete_metric_set (S i) (d i)"
  shows "product_complete_metric r I (to_nat_on I) (from_nat_into I) S (\<lambda>i x y. if i \<in> I then bounded_dist (d i) x y else 0) 1"
proof -
  have "\<And>i. i \<in> I \<Longrightarrow> complete_metric_set (S i) (bounded_dist (d i))"
       "\<And>i x y. i \<in> I \<Longrightarrow> bounded_dist (d i) x y \<le> 1"
    using assms(4) by(auto intro!: metric_set.bounded_dist_dist(1) less_imp_le[OF metric_set.bounded_dist_dist(2)] simp: complete_metric_set_def) (simp add: assms(4) complete_metric_set.axioms(2) complete_metric_set.bounded_dist_complete)
  thus ?thesis
    by(auto intro!: product_complete_metricI[OF assms(1-3)] simp: complete_metric_set_def) (metis metric_set.dist_geq0)
qed

lemma product_complete_metric_natI':
  assumes "0 < r" "r < 1" "\<And>n. complete_metric_set (S n) (d n)"
  shows "product_complete_metric r UNIV id id S (\<lambda>n. bounded_dist (d n)) 1"
proof -
  have "\<And>n. complete_metric_set (S n) (bounded_dist (d n))"
       "\<And>n x y. bounded_dist (d n) x y \<le> 1"
    using assms(3) by(auto intro!: metric_set.bounded_dist_dist(1) less_imp_le[OF metric_set.bounded_dist_dist(2)] simp: complete_metric_set_def) (simp add: assms(3) complete_metric_set.axioms(2) complete_metric_set.bounded_dist_complete)
  thus ?thesis
    by(auto intro!: product_complete_metric_natI[OF assms(1,2)]) (meson complete_metric_set_def metric_set.dist_geq0)
qed

lemma product_polish_metricI':
  assumes "0 < r" "r < 1" "countable I" "\<And>i. i \<in> I \<Longrightarrow> polish_metric_set (S i) (d i)"
  shows "product_polish_metric r I (to_nat_on I) (from_nat_into I) S (\<lambda>i x y. if i \<in> I then bounded_dist (d i) x y else 0) 1"
proof -
  have "\<And>i. i \<in> I \<Longrightarrow> metric_set (S i) (bounded_dist (d i))"
       "\<And>i x y. i \<in> I \<Longrightarrow> bounded_dist (d i) x y \<le> 1"
    using assms(4) by(auto intro!: metric_set.bounded_dist_dist(1) less_imp_le[OF metric_set.bounded_dist_dist(2)] simp: polish_metric_set_def complete_metric_set_def)
  thus ?thesis
    using assms(4) by(auto intro!: product_polish_metricI[OF assms(1-3)] polish_metric_set.bounded_dist_polish simp: metric_set_def)
qed

end