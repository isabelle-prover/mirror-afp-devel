section\<open>Miscellaneous technical lemmas\<close>

(*
  Title:   Miscellaneous_Lemmas.thy
  Authors: Angeliki Koutsoukou-Argyraki, Mantas Bakšys, and Chelsea Edmonds
  Affiliation: University of Cambridge
  Date: August 2022.
*)

theory Miscellaneous_Lemmas
  imports 
    "HOL-Library.Indicator_Function"
    "HOL-Analysis.Convex"
begin

lemma set_pairs_filter_subset: "A \<subseteq> B \<Longrightarrow> {p . p \<in> A \<times> A \<and> P p} \<subseteq> {p. p \<in> B \<times> B \<and> P p}"
  by (intro subsetI) blast

lemma card_set_ss_indicator: 
  assumes "A \<subseteq> B"
  assumes "finite B"
  shows "card A = (\<Sum> p \<in> B. indicator A p)"
proof -
  obtain C where ceq: "C = B - A" by blast
  then have beq: "B = A \<union> C" using assms by blast
  have bint: "A \<inter> C = {}" using ceq by blast
  have finite: "finite A" using assms finite_subset by auto 
  have zero: "\<And> p. p \<in> C \<Longrightarrow> indicator (A) p = 0"
    by (simp add: ceq) 
  then have "card A = (\<Sum> p \<in> A . indicator (A) p)"
    by simp 
  also have "... = (\<Sum> p \<in> A . indicator A p) + (\<Sum> p \<in> C . indicator A p)" 
    using zero by (metis add_cancel_left_right sum.neutral) 
  finally show "card A = (\<Sum> p \<in> B. indicator A p)" using beq bint assms
    by (metis add.commute ceq sum.subset_diff) 
qed

lemma card_cartesian_prod_square: "finite X \<Longrightarrow> card (X \<times> X) = (card X)^2" 
  using card_cartesian_product by (simp add: power2_eq_square) 

lemma (in ordered_ab_group_add) diff_strict1_mono: 
  assumes "a > a'" "b \<le> b'"
  shows "a - b > a' - b'"
  using diff_strict_mono assms
  by (metis local.diff_strict_right_mono local.dual_order.not_eq_order_implies_strict) 

lemma card_cartesian_product_6: "card (A \<times> A \<times> A \<times> A \<times> A \<times> A) = (card A) ^ 6"
proof-
  have "card (A \<times> A \<times> A \<times> A \<times> A \<times> A) = 
    card A * card A * card A * card A * card A * card A" 
    using card_cartesian_product mult.commute by metis
  then show ?thesis by algebra
qed

lemma card_cartesian_product3: "card (X \<times> Y \<times> Z) = card X * card Y * card Z"
  using card_cartesian_product  by (metis mult.commute mult.left_commute)  


lemma card_le_image_div:
  fixes A:: "'a set" and B:: "'b set" and f:: "'a \<Rightarrow> 'b set" and r:: real
  assumes "finite B" and "pairwise (\<lambda> s t. disjnt (f s) (f t)) A" and "\<forall> d \<in> A. (card (f d)) \<ge> r" 
  and "\<forall> d \<in> A. f d \<subseteq> B" and "r > 0"
  shows "card A \<le> card B / r"

proof (cases "finite A")
  assume hA: "finite A"
  have hpair_disj: "pairwise disjnt (f ` A)" using assms by (metis pairwiseD pairwise_imageI)
  have "r * card A = (\<Sum> d \<in> A. r)" by simp
  also have "... \<le> (\<Sum> d \<in> A. card (f d))" using assms sum_mono by fastforce
  also have "... = sum card (f ` A)" using assms hA by (simp add: sum_card_image)
  also have "... = card (\<Union> d \<in> A. f d)" using assms hA hpair_disj
    by (metis Sup_upper card_Union_disjoint finite_UN_I rev_finite_subset)
  also have "... \<le> card B" using assms card_mono
    by (metis UN_subset_iff of_nat_le_iff)
  finally have "r * card A \<le> card B" by linarith
  thus ?thesis using divide_le_eq assms by (simp add: mult_imp_le_div_pos mult_of_nat_commute)
next
  assume "\<not> finite A"
  thus ?thesis using assms by auto
qed

lemma list_middle_eq: 
  "length xs = length ys \<Longrightarrow> hd xs = hd ys \<Longrightarrow> last xs = last ys 
    \<Longrightarrow> butlast (tl xs) = butlast (tl ys) \<Longrightarrow> xs = ys"
  apply (induct xs ys rule: list_induct2, simp)
  by (metis append_butlast_last_id butlast.simps(1) butlast.simps(2) butlast_tl hd_Cons_tl 
      impossible_Cons le_refl list.sel(3) neq_Nil_conv)

lemma list2_middle_singleton: 
  assumes "length xs = 3"
  shows "butlast (tl xs) = [xs ! 1]"
proof (simp add: list_eq_iff_nth_eq assms)
  have l: "length (butlast (tl xs)) = 1" using length_butlast length_tl assms by simp 
  then have " butlast (tl xs) ! 0 = (tl xs) ! 0" using nth_butlast[of 0 "tl xs"] by simp
  then show "butlast (tl xs) ! 0 = xs ! Suc 0" using nth_tl[of 0 xs]  l by simp
qed


lemma le_powr_half_mult:
  fixes x y z:: real
  assumes "x ^ 2 \<le> y * z" and "0 \<le> y" and "0 \<le> z"
  shows "x \<le> y powr(1/2) * z powr (1/2)"
  using assms power2_eq_square
  by (metis dual_order.trans linorder_linear powr_ge_pzero powr_half_sqrt powr_mult real_le_rsqrt 
    real_sqrt_le_0_iff)

lemma Cauchy_Schwarz_ineq_sum2:
  fixes f g:: "'a \<Rightarrow> real" and A:: "'a set"
  shows "(\<Sum> d \<in> A. f d * g d) \<le> 
    (\<Sum> d \<in> A. (f d)^2) powr (1/2) * (\<Sum> d \<in> A. (g d)^2) powr (1/2)"
  using Convex.Cauchy_Schwarz_ineq_sum[of "f" "g" "A"] le_powr_half_mult sum_nonneg zero_le_power2
  by (metis (mono_tags, lifting))

end