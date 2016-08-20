(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

theory Banach_Density
imports SG_Library_Complement

begin

section {*Banach densities*}

text {*The upper Banach density of a subset $A$ of the integers is
$\limsup Card(A \cap [0,n)) / n \in [0,1]$. It measures how big a set of integers is,
at some times. In this paragraph, we establish the basic properties of this notion.

There is a corresponding notion of lower Banach density, with a liminf instead
of a limsup, measuring how big a set is at all times. The corresponding properties
are proved exactly in the same way.
*}

subsection {*Upper Banach densities*}

definition upper_Banach_density::"nat set \<Rightarrow> real"
  where "upper_Banach_density A = real_of_ereal(limsup (\<lambda>n. card(A \<inter> {..<n})/n))"

lemma upper_Banach_density_in_01:
  "ereal(upper_Banach_density A) = limsup (\<lambda>n. card(A \<inter> {..<n})/n)"
  "upper_Banach_density A \<le> 1"
  "upper_Banach_density A \<ge> 0"
proof -
  {
    fix n::nat assume "n>0"
    have "card(A \<inter> {..<n}) \<le> n" by (metis card_lessThan Int_lower2 card_mono finite_lessThan)
    then have "card(A \<inter> {..<n}) / n \<le> ereal 1" using `n>0` by auto
  }
  then have "eventually (\<lambda>n. card(A \<inter> {..<n}) / n \<le> ereal 1) sequentially"
    by (simp add: eventually_at_top_dense)
  then have a: "limsup (\<lambda>n. card(A \<inter> {..<n})/n) \<le> 1" by (simp add: Limsup_const Limsup_eventually_bounded)

  have "card(A \<inter> {..<n}) / n \<ge> ereal 0" for n by auto
  then have "liminf (\<lambda>n. card(A \<inter> {..<n})/n) \<ge> 0" by (simp add: le_Liminf_iff less_le_trans)
  then have b: "limsup (\<lambda>n. card(A \<inter> {..<n})/n) \<ge> 0" by (meson Liminf_le_Limsup order_trans sequentially_bot)

  have "abs(limsup (\<lambda>n. card(A \<inter> {..<n})/n)) \<noteq> \<infinity>" using a b by auto
  then show "ereal(upper_Banach_density A) = limsup (\<lambda>n. card(A \<inter> {..<n})/n)"
    unfolding upper_Banach_density_def by auto
  show "upper_Banach_density A \<le> 1" "upper_Banach_density A \<ge> 0" unfolding upper_Banach_density_def
    using a b by (auto simp add: real_of_ereal_le_1 real_of_ereal_pos)
qed

lemma upper_Banach_density_event1:
  fixes l::real
  assumes "upper_Banach_density A < l"
  shows "eventually (\<lambda>n. card(A \<inter> {..<n}) < l * n) sequentially"
proof -
  have "limsup (\<lambda>n. card(A \<inter> {..<n})/n) < l"
    using assms upper_Banach_density_in_01(1) ereal_less_ereal_Ex by auto
  then have "eventually (\<lambda>n. card(A \<inter> {..<n})/n < ereal l) sequentially"
    using Limsup_lessD by blast
  then have "eventually (\<lambda>n. card(A \<inter> {..<n})/n < ereal l \<and> n > 0) sequentially"
    using eventually_gt_at_top eventually_conj by blast
  moreover have "card(A \<inter> {..<n}) < l * n" if "card(A \<inter> {..<n})/n < ereal l \<and> n > 0" for n
    using that by (simp add: divide_less_eq)
  ultimately show "eventually (\<lambda>n. card(A \<inter> {..<n}) < l * n) sequentially"
    by (simp add: eventually_mono)
qed

lemma upper_Banach_density_event2:
  fixes l::real
  assumes "eventually (\<lambda>n. card(A \<inter> {..<n}) \<le> l * n) sequentially"
  shows "upper_Banach_density A \<le> l"
proof -
  have "eventually (\<lambda>n. card(A \<inter> {..<n}) \<le> l * n \<and> n > 0) sequentially"
    using assms eventually_gt_at_top eventually_conj by blast
  moreover have "card(A \<inter> {..<n})/n \<le> ereal l" if "card(A \<inter> {..<n}) \<le> l * n \<and> n > 0" for n
    using that by (simp add: divide_le_eq)
  ultimately have "eventually (\<lambda>n. card(A \<inter> {..<n})/n \<le> ereal l) sequentially"
    by (simp add: eventually_mono)
  then have "limsup (\<lambda>n. card(A \<inter> {..<n})/n) \<le> ereal l"
    by (simp add: Limsup_eventually_bounded)
  then have "ereal(upper_Banach_density A) \<le> ereal l"
    using upper_Banach_density_in_01(1) by auto
  then show ?thesis by auto
qed

lemma lem_ge_sum:
  fixes l x y::real
  assumes "l>x+y"
  shows "\<exists>lx ly. l = lx + ly \<and> lx > x \<and> ly > y"
proof -
  define lx ly where "lx = x + (l-(x+y))/2" and "ly = y + (l-(x+y))/2"
  have "l = lx + ly \<and> lx > x \<and> ly > y" unfolding lx_def ly_def using assms by auto
  then show ?thesis by auto
qed

lemma upper_Banach_density_union:
  shows "upper_Banach_density (A \<union> B) \<le> upper_Banach_density A + upper_Banach_density B"
proof -
  {
    fix l assume "l > upper_Banach_density A + upper_Banach_density B"
    then obtain lA lB where l: "l = lA+lB" and lA: "lA > upper_Banach_density A" and lB: "lB > upper_Banach_density B"
      using lem_ge_sum by blast
    {
      fix n assume H: "card (A \<inter> {..<n}) < lA * n \<and> card (B \<inter> {..<n}) < lB * n"
      have "card((A\<union>B) \<inter> {..<n}) \<le> card(A \<inter> {..<n}) + card(B \<inter> {..<n})"
        by (simp add: card_Un_le inf_sup_distrib2)
      also have "... \<le> l * n" using l H by (simp add: ring_class.ring_distribs(2))
      finally have "card ((A\<union>B) \<inter> {..<n}) \<le> l * n" by simp
    }
    moreover have "eventually (\<lambda>n. card (A \<inter> {..<n}) < lA * n \<and> card (B \<inter> {..<n}) < lB * n) sequentially"
      using upper_Banach_density_event1[OF lA] upper_Banach_density_event1[OF lB] eventually_conj by blast
    ultimately have "eventually (\<lambda>n. card((A\<union>B) \<inter> {..<n}) \<le> l * n) sequentially"
      by (simp add: eventually_mono)
    then have "upper_Banach_density (A \<union> B) \<le> l" using upper_Banach_density_event2 by auto
  }
  then show ?thesis by (meson dense not_le)
qed

lemma upper_Banach_density_subset:
  assumes "A \<subseteq> B"
  shows "upper_Banach_density A \<le> upper_Banach_density B"
proof -
  {
    fix l::real assume l: "l > upper_Banach_density B"
    have "card(A \<inter> {..<n}) \<le> card(B \<inter> {..<n})" for n
      using assms by (metis Int_lower2 Int_mono card_mono finite_lessThan finite_subset inf.left_idem)
    then have "card(A \<inter> {..<n}) \<le> l * n" if "card(B \<inter> {..<n}) < l * n" for n
      using that by (meson lessThan_def less_imp_le of_nat_le_iff order_trans)
    moreover have "eventually (\<lambda>n. card(B \<inter> {..<n}) < l * n) sequentially"
      using upper_Banach_density_event1 l by simp
    ultimately have "eventually (\<lambda>n. card(A \<inter> {..<n}) \<le> l * n) sequentially"
      by (simp add: eventually_mono)
    then have "upper_Banach_density A \<le> l" using upper_Banach_density_event2 by auto
  }
  then show ?thesis by (meson dense not_le)
qed

lemma upper_Banach_density_lim:
  assumes "(\<lambda>n. card(A \<inter> {..<n})/n) \<longlonglongrightarrow> l"
  shows "upper_Banach_density A = l"
proof -
  have "(\<lambda>n. ereal(card(A \<inter> {..<n})/n)) \<longlonglongrightarrow> l" using assms by auto
  then have "limsup (\<lambda>n. card(A \<inter> {..<n})/n) = l"
    using sequentially_bot tendsto_iff_Liminf_eq_Limsup by blast
  then show ?thesis unfolding upper_Banach_density_def by auto
qed

lemma upper_Banach_density_0_diff:
  assumes "A \<subseteq> B" "upper_Banach_density (B-A) = 0"
  shows "upper_Banach_density A = upper_Banach_density B"
proof -
  have "upper_Banach_density B \<le> upper_Banach_density A + upper_Banach_density (B-A)"
    using upper_Banach_density_union[of A "B-A"] by (simp add: assms(1) sup.absorb2)
  then have "upper_Banach_density B \<le> upper_Banach_density A"
    using assms(2) by simp
  then show ?thesis using upper_Banach_density_subset[OF assms(1)] by simp
qed

lemma
  assumes "upper_Banach_density (A \<Delta> B) = 0"
  shows "upper_Banach_density A = upper_Banach_density B"
proof -
  have "A- (A\<inter>B) \<subseteq> A \<Delta> B" "B- (A\<inter>B) \<subseteq> A \<Delta> B"
    using assms(1) by (auto simp add: Diff_Int Un_infinite)
  then have "upper_Banach_density (A - (A\<inter>B)) = 0"
            "upper_Banach_density (B - (A\<inter>B)) = 0"
    using upper_Banach_density_subset assms(1) upper_Banach_density_in_01(3)
    by (metis inf.absorb_iff2 inf.orderE)+
  then have "upper_Banach_density (A\<inter>B) = upper_Banach_density A"
            "upper_Banach_density (A\<inter>B) = upper_Banach_density B"
    using upper_Banach_density_0_diff by auto
  then show ?thesis by simp
qed

lemma upper_Banach_density_finite:
  assumes "finite A"
  shows "upper_Banach_density A = 0"
proof -
  have "(\<lambda>n. card(A \<inter> {..<n})/n) \<longlonglongrightarrow> 0"
  proof (rule tendsto_sandwich[where ?f= "\<lambda>n. 0" and ?h = "\<lambda>(n::nat). card A / n"])
    have "card(A \<inter> {..<n})/n \<le> card A / n" if "n>0" for n
      using that `finite A` by (simp add: card_mono divide_right_mono)
    then show "eventually (\<lambda>n. card(A \<inter> {..<n})/n \<le> card A / n) sequentially"
      by (simp add: eventually_at_top_dense)
    have "(\<lambda>n. real (card A)* (1 / real n)) \<longlonglongrightarrow> real(card A) * 0"
      by (rule tendsto_mult, simp, simp add: lim_1_over_n)
    then show "(\<lambda>n. real (card A) / real n) \<longlonglongrightarrow> 0" by auto
  qed (auto)
  then show "upper_Banach_density A = 0" using upper_Banach_density_lim by auto
qed

lemma upper_Banach_density_shift:
  fixes k::nat and l::int
  shows "ereal(upper_Banach_density A) = limsup (\<lambda>n. card(A \<inter> {k..nat(n+l)}) / n)"
proof -
  define C where "C = k+2*nat(abs(l))+1"
  have *: "(\<lambda>n. C*(1/n)) \<longlonglongrightarrow> real C * 0"
    by (rule tendsto_mult, auto simp add: lim_1_over_n)
  have l0: "limsup (\<lambda>n. C/n) = 0"
    apply (rule lim_imp_Limsup, simp) using * by (simp add: zero_ereal_def)

  {
    fix n
    have "card(A \<inter> {k..nat(n+l)}) \<le> card (A \<inter> {..<n} \<union> {n..n + nat(abs(l))})"
      by (rule card_mono, auto)
    also have "... \<le> card (A \<inter> {..<n}) + card {n..n + nat(abs(l))}"
      by (rule card_Un_le)
    also have "... \<le> card (A \<inter> {..<n}) + real C"
      unfolding C_def by auto
    finally have "card(A \<inter> {k..nat(n+l)}) / n \<le> (card (A \<inter> {..<n}) + real C) /n"
      by (simp add: divide_right_mono)
    also have "... = card (A \<inter> {..<n})/n + C/n"
      using add_divide_distrib by auto
    finally have "card(A \<inter> {k..nat(n+l)}) / n \<le> card (A \<inter> {..<n})/n + C/n"
      by auto
  }
  then have "limsup (\<lambda>n. card(A \<inter> {k..nat(n+l)}) / n) \<le> limsup (\<lambda>n. card (A \<inter> {..<n})/n + ereal(C/n))"
    by (simp add: Limsup_mono)
  also have "... \<le> limsup (\<lambda>n. card (A \<inter> {..<n})/n) + limsup (\<lambda>n. C/n)"
    by (rule ereal_limsup_add_mono)
  finally have a: "limsup (\<lambda>n. card(A \<inter> {k..nat(n+l)}) / n) \<le> limsup (\<lambda>n. card (A \<inter> {..<n})/n)"
    using l0 by simp

  {
    fix n::nat
    have "card ({..<k} \<union> {n-nat(abs(l))..n + nat(abs(l))}) \<le> card {..<k} + card {n-nat(abs(l))..n + nat(abs(l))}"
      by (rule card_Un_le)
    also have "... \<le> k + 2*nat(abs(l)) + 1" by auto
    finally have *: "card ({..<k} \<union> {n-nat(abs(l))..n + nat(abs(l))}) \<le> C" unfolding C_def by blast

    have "card(A \<inter> {..<n}) \<le> card (A \<inter> {k..nat(n+l)} \<union> ({..<k} \<union> {n-nat(abs(l))..n + nat(abs(l))}))"
      by (rule card_mono, auto)
    also have "... \<le> card (A \<inter> {k..nat(n+l)}) + card ({..<k} \<union> {n-nat(abs(l))..n + nat(abs(l))})"
      by (rule card_Un_le)
    also have "... \<le> card (A \<inter> {k..nat(n+l)}) + C"
      using * by auto
    finally have "card (A \<inter> {..<n}) / n \<le> (card (A \<inter> {k..nat(n+l)}) + real C)/n"
      by (simp add: divide_right_mono)
    also have "... = card (A \<inter> {k..nat(n+l)})/n + C/n"
      using add_divide_distrib by auto
    finally have "card (A \<inter> {..<n}) / n \<le> card (A \<inter> {k..nat(n+l)})/n + C/n"
      by auto
  }
  then have "limsup (\<lambda>n. card(A \<inter> {..<n}) / n) \<le> limsup (\<lambda>n. card (A \<inter> {k..nat(n+l)})/n + ereal(C/n))"
    by (simp add: Limsup_mono)
  also have "... \<le> limsup (\<lambda>n. card (A \<inter> {k..nat(n+l)})/n) + limsup (\<lambda>n. C/n)"
    by (rule ereal_limsup_add_mono)
  finally have "limsup (\<lambda>n. card(A \<inter> {..<n}) / n) \<le> limsup (\<lambda>n. card (A \<inter> {k..nat(n+l)})/n)"
    using l0 by simp
  then have "limsup (\<lambda>n. card(A \<inter> {..<n}) / n) = limsup (\<lambda>n. card (A \<inter> {k..nat(n+l)})/n)"
    using a by auto
  then show ?thesis using upper_Banach_density_in_01(1) by auto
qed

lemma upper_Banach_density_meas [measurable]:
  assumes [measurable]: "\<And>(n::nat). Measurable.pred M (P n)"
  shows "(\<lambda>x. upper_Banach_density {n. P n x}) \<in> borel_measurable M"
unfolding upper_Banach_density_def by auto


subsection {*Lower Banach densities*}

definition lower_Banach_density::"nat set \<Rightarrow> real"
  where "lower_Banach_density A = real_of_ereal(liminf (\<lambda>n. card(A \<inter> {..<n})/n))"

lemma lower_Banach_density_in_01:
  "ereal(lower_Banach_density A) = liminf (\<lambda>n. card(A \<inter> {..<n})/n)"
  "lower_Banach_density A \<le> 1"
  "lower_Banach_density A \<ge> 0"
proof -
  {
    fix n::nat assume "n>0"
    have "card(A \<inter> {..<n}) \<le> n" by (metis card_lessThan Int_lower2 card_mono finite_lessThan)
    then have "card(A \<inter> {..<n}) / n \<le> ereal 1" using `n>0` by auto
  }
  then have "eventually (\<lambda>n. card(A \<inter> {..<n}) / n \<le> ereal 1) sequentially"
    by (simp add: eventually_at_top_dense)
  then have "limsup (\<lambda>n. card(A \<inter> {..<n})/n) \<le> 1" by (simp add: Limsup_const Limsup_eventually_bounded)
  then have a: "liminf (\<lambda>n. card(A \<inter> {..<n})/n) \<le> 1"
    by (meson Liminf_le_Limsup less_le_trans not_le sequentially_bot)

  have "card(A \<inter> {..<n}) / n \<ge> ereal 0" for n by auto
  then have b: "liminf (\<lambda>n. card(A \<inter> {..<n})/n) \<ge> 0" by (simp add: le_Liminf_iff less_le_trans)

  have "abs(liminf (\<lambda>n. card(A \<inter> {..<n})/n)) \<noteq> \<infinity>" using a b by auto
  then show "ereal(lower_Banach_density A) = liminf (\<lambda>n. card(A \<inter> {..<n})/n)"
    unfolding lower_Banach_density_def by auto
  show "lower_Banach_density A \<le> 1" "lower_Banach_density A \<ge> 0" unfolding lower_Banach_density_def
    using a b by (auto simp add: real_of_ereal_le_1 real_of_ereal_pos)
qed

lemma lower_Banach_density_le_upper:
  "lower_Banach_density A \<le> upper_Banach_density A"
using lower_Banach_density_in_01(1) upper_Banach_density_in_01(1)
by (metis (mono_tags, lifting) Liminf_le_Limsup ereal_less_eq(3) sequentially_bot)

text {*The lower Banach density of a set is $1$ minus the upper Banach density of its complement.
Hence, most statements about one of them follow from statements about the other one,
although we will rather give direct proofs as they are not more complicated.*}

lemma lower_upper_Banach_density_complement:
  "lower_Banach_density A = 1 - upper_Banach_density (UNIV - A)"
proof -
  {
    fix n assume "n>(0::nat)"
    have "{..<n} \<inter> UNIV - (UNIV - ({..<n} - (UNIV - A))) = {..<n} \<inter> A"
      by blast
    moreover have "{..<n} \<inter> UNIV \<inter> (UNIV - ({..<n} - (UNIV - A))) = (UNIV - A) \<inter> {..<n}"
      by blast
    ultimately have "card (A \<inter> {..<n}) = n - card((UNIV-A) \<inter> {..<n})"
      by (metis (no_types) Int_commute card_Diff_subset_Int card_lessThan finite_Int finite_lessThan inf_top_right)
    then have "card (A \<inter> {..<n})/n = (real n - card((UNIV-A) \<inter> {..<n})) / n"
      by (metis Int_lower2 card_lessThan card_mono finite_lessThan of_nat_diff)
    then have "card (A \<inter> {..<n})/n = ereal 1 - card((UNIV-A) \<inter> {..<n})/n"
      using `n>0` by (simp add: diff_divide_distrib)
  }
  then have "eventually (\<lambda>n. card (A \<inter> {..<n})/n = ereal 1 - card((UNIV-A) \<inter> {..<n})/n) sequentially"
    by (simp add: eventually_at_top_dense)
  then have "liminf (\<lambda>n. card (A \<inter> {..<n})/n) = liminf (\<lambda>n. ereal 1 - card((UNIV-A) \<inter> {..<n})/n)"
    by (rule Liminf_eq)
  also have "... = ereal 1 - limsup (\<lambda>n. card((UNIV-A) \<inter> {..<n})/n)"
    by (rule liminf_ereal_cminus, simp)
  finally show ?thesis unfolding lower_Banach_density_def
    by (metis ereal_minus(1) real_of_ereal.simps(1) upper_Banach_density_in_01(1))
qed

lemma lower_Banach_density_event1:
  fixes l::real
  assumes "lower_Banach_density A > l"
  shows "eventually (\<lambda>n. card(A \<inter> {..<n}) > l * n) sequentially"
proof -
  have "ereal(lower_Banach_density A) > l" using assms by auto
  then have "liminf (\<lambda>n. card(A \<inter> {..<n})/n) > l"
    using lower_Banach_density_in_01(1) by auto
  then have "eventually (\<lambda>n. card(A \<inter> {..<n})/n > ereal l) sequentially"
    using less_LiminfD by blast
  then have "eventually (\<lambda>n. card(A \<inter> {..<n})/n > ereal l \<and> n > 0) sequentially"
    using eventually_gt_at_top eventually_conj by blast
  moreover have "card(A \<inter> {..<n}) > l * n" if "card(A \<inter> {..<n})/n > ereal l \<and> n > 0" for n
    using that divide_le_eq ereal_less_eq(3) less_imp_of_nat_less not_less of_nat_eq_0_iff by fastforce
  ultimately show "eventually (\<lambda>n. card(A \<inter> {..<n}) > l * n) sequentially"
    by (simp add: eventually_mono)
qed

lemma lower_Banach_density_event2:
  fixes l::real
  assumes "eventually (\<lambda>n. card(A \<inter> {..<n}) \<ge> l * n) sequentially"
  shows "lower_Banach_density A \<ge> l"
proof -
  have "eventually (\<lambda>n. card(A \<inter> {..<n}) \<ge> l * n \<and> n > 0) sequentially"
    using assms eventually_gt_at_top eventually_conj by blast
  moreover have "card(A \<inter> {..<n})/n \<ge> ereal l" if "card(A \<inter> {..<n}) \<ge> l * n \<and> n > 0" for n
    using that by (meson ereal_less_eq(3) not_less of_nat_0_less_iff pos_divide_less_eq)
  ultimately have "eventually (\<lambda>n. card(A \<inter> {..<n})/n \<ge> ereal l) sequentially"
    by (simp add: eventually_mono)
  then have "liminf (\<lambda>n. card(A \<inter> {..<n})/n) \<ge> ereal l"
    by (simp add: Liminf_eventually_bounded)
  then have "ereal(lower_Banach_density A) \<ge> ereal l"
    using lower_Banach_density_in_01(1) by auto
  then show ?thesis by auto
qed

lemma lower_Banach_density_subset:
  assumes "A \<subseteq> B"
  shows "lower_Banach_density A \<le> lower_Banach_density B"
proof -
  {
    fix l::real assume l: "l < lower_Banach_density A"
    have "card(A \<inter> {..<n}) \<le> card(B \<inter> {..<n})" for n
      using assms by (metis Int_lower2 Int_mono card_mono finite_lessThan finite_subset inf.left_idem)
    then have "card(B \<inter> {..<n}) \<ge> l * n" if "card(A \<inter> {..<n}) > l * n" for n
      using that by (meson lessThan_def less_imp_le of_nat_le_iff order_trans)
    moreover have "eventually (\<lambda>n. card(A \<inter> {..<n}) > l * n) sequentially"
      using lower_Banach_density_event1 l by simp
    ultimately have "eventually (\<lambda>n. card(B \<inter> {..<n}) \<ge> l * n) sequentially"
      by (simp add: eventually_mono)
    then have "lower_Banach_density B \<ge> l" using lower_Banach_density_event2 by auto
  }
  then show ?thesis by (meson dense not_le)
qed

lemma lower_Banach_density_lim:
  assumes "(\<lambda>n. card(A \<inter> {..<n})/n) \<longlonglongrightarrow> l"
  shows "lower_Banach_density A = l"
proof -
  have "(\<lambda>n. ereal(card(A \<inter> {..<n})/n)) \<longlonglongrightarrow> l" using assms by auto
  then have "liminf (\<lambda>n. card(A \<inter> {..<n})/n) = l"
    using sequentially_bot tendsto_iff_Liminf_eq_Limsup by blast
  then show ?thesis unfolding lower_Banach_density_def by auto
qed

lemma lower_Banach_density_finite:
  assumes "finite A"
  shows "lower_Banach_density A = 0"
using lower_Banach_density_in_01(3) upper_Banach_density_finite[OF assms] lower_Banach_density_le_upper
by (metis antisym_conv)

end
