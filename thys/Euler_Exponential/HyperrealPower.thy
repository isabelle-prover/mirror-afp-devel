(*  Title:  HyperrealPower.thy
    Author: Jacques D. Fleuriot, University of Edinburgh, 2026
*)

section\<open>Hyperreal powers\<close>

theory HyperrealPower
  imports "Real_Power.Log" "HOL-Nonstandard_Analysis.NatStar" HyperBinomial
begin                                                             

definition
  hpow  :: "[hypreal,hypreal] \<Rightarrow> hypreal"     (infixr "hpow" 80) where
  [transfer_unfold]: "x hpow a = starfun2 (pow\<^sub>\<real>) x a"

lemma "(hpow) \<in> InternalFuns2"
  unfolding InternalFuns_def hpow_def
  by (simp add: starfun2_eq_starfun2n)

lemma hpow: "(star_n X) hpow (star_n Y) = star_n (\<lambda>n. (X n) pow\<^sub>\<real> (Y n))"
  by (metis hpow_def starfun2_star_n)

subsection\<open>Tranferred properties\<close>

lemma hpow_one_eq_one [simp]: "\<And>a. 1 hpow a = 1"
by transfer simp

lemma hpow_zero_eq_one [simp]: "\<And>a. a > 0 \<Longrightarrow> a hpow 0 = 1"
by transfer simp

lemma hpow_minus_one: "\<And>a. 0 < a \<Longrightarrow> a hpow -1 = inverse a"
  by transfer (simp add: powreal_minus_one)

lemma hpow_one [simp]: "\<And>a. a > 0 \<Longrightarrow> a hpow 1 = a"
by transfer simp

lemma hpow_gt_zero: "\<And>a x. a > 0 \<Longrightarrow> a hpow x > 0"
by (transfer, rule powreal_gt_zero)

lemma hpow_not_zero: "\<And>a x. a > 0 \<Longrightarrow> a hpow x \<noteq> 0"
by (transfer, rule powreal_not_zero)

lemma hpow_minus: "\<And>a x. a > 0 \<Longrightarrow> a hpow (-x) = inverse (a hpow x)"
by (transfer, rule powreal_minus)

lemma hpow_inverse:
     "\<And>a x. a > 0 \<Longrightarrow> inverse (a hpow x) = (inverse a) hpow x"
by (transfer, rule powreal_inverse)

lemma hpow_mult_base: 
      "\<And>a b x. \<lbrakk> 0 < a; 0 < b \<rbrakk> \<Longrightarrow> (a * b) hpow x = (a hpow x) * (b hpow x)"
  by transfer (simp add: powreal_mult_base)

lemma hpow_mult: 
  "\<And>a x y. 0 < a \<Longrightarrow> (a hpow x) hpow y = a hpow (x * y)"
by (transfer, rule powreal_mult)

lemma hpow_divide:
  "\<And>a b x. \<lbrakk> 0 < a; 0 < b \<rbrakk> \<Longrightarrow> (a/b) hpow x = (a hpow x) / (b hpow x)"
by transfer (simp add: powreal_divide)

lemma hpow_divide2: "\<And>a x y. a > 0 \<Longrightarrow> a hpow (x - y) = (a hpow x)/(a hpow y)"
by transfer (simp add: powreal_divide2)

lemma hpow_ge_one: "\<And>a x. a \<ge> 1 \<Longrightarrow> x \<ge> 0 \<Longrightarrow> a hpow x \<ge> 1"
by (transfer, rule powreal_ge_one)

lemma hpow_ge_one2:  
   "\<And>a x. \<lbrakk> 0 < a; a < 1; x \<le> 0 \<rbrakk> \<Longrightarrow> a hpow x \<ge> 1"
by (transfer, rule powreal_ge_one2)

lemma hpow_le_mono:
   "\<And>r s a. \<lbrakk> r \<le> s; a \<ge> 1 \<rbrakk> \<Longrightarrow> a hpow r \<le> a hpow s"
by (transfer, rule powreal_le_mono)

lemma hpow_le_anti_mono:
   "\<And>r s a. \<lbrakk> r \<le> s; 0 < a; a < 1 \<rbrakk> \<Longrightarrow> a hpow r \<ge> a hpow s"
by (transfer, rule powreal_le_anti_mono)

lemma hpow_less_cancel:
   "\<And>r s a. \<lbrakk> a hpow r < a hpow s; a \<ge> 1 \<rbrakk> \<Longrightarrow> r < s"
by (transfer, rule powreal_less_cancel)

lemma hpow_less_anti_mono:
  "\<And>r s a. \<lbrakk> r < s; 0 < a; a < 1 \<rbrakk> \<Longrightarrow> a hpow r > a hpow s"
by (transfer, rule powreal_less_anti_mono)

lemma hpow_less_mono:
   "\<And>r s a. \<lbrakk> r < s; a > 1 \<rbrakk> \<Longrightarrow> a hpow r < a hpow s"
by (transfer, rule powreal_less_mono)

lemma hpow_le_cancel:
   "\<And>r s a. \<lbrakk> a hpow r \<le> a hpow s; a > 1 \<rbrakk> \<Longrightarrow> r \<le> s"
by (transfer, rule powreal_le_cancel)

lemma hpow_less_cancel_iff [simp]: 
   "\<And>r s a. 1 < a \<Longrightarrow> (a hpow r < a hpow s) = (r < s)"
by (transfer, rule powreal_less_cancel_iff)

lemma hpow_le_cancel_iff [simp]: 
   "\<And>r s a. 1 < a \<Longrightarrow> (a hpow r \<le> a hpow s) = (r \<le> s)"
by (transfer, rule powreal_le_cancel_iff)

lemma hpow_inject_exp1 [simp]: 
   "\<And>r s a. 1 < a  \<Longrightarrow> (a hpow r = a hpow s) = (s = r)"
by (transfer, rule powreal_inject_exp1)

lemma hpow_inject_exp2 [simp]: 
   "\<And>r s a. 0 < a \<Longrightarrow> a < 1 \<Longrightarrow> (a hpow r = a hpow s) = (s = r)"
by transfer simp 

lemma hpow_inject [simp]: 
   "\<And>r s a. 0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> (a hpow r = a hpow s) = (s = r)"
by (transfer, rule powreal_inject)

lemma hpow_gt_one: "\<And>a x. a > 1 \<Longrightarrow> x > 0 \<Longrightarrow> a hpow x > 1"
by (transfer, rule powreal_gt_one)

lemma hpow_less_mono_base:
  "\<And>a b r. \<lbrakk> r > 0; 0 < a; a < b \<rbrakk> \<Longrightarrow> a hpow r < b hpow r"
by (transfer, rule powreal_less_mono_base)

lemma hpow_less_antimono_base:
  "\<And>a b r. \<lbrakk> r < 0; 0 < a; a < b \<rbrakk> \<Longrightarrow> a hpow r > b hpow r"
by (transfer, rule powreal_less_antimono_base)

lemma hpow_hyperpow_eq:
  "\<And>a n. a > 0 \<Longrightarrow> a hpow (of_hypnat n) = a pow n"
by (transfer, rule powreal_power_eq)

lemma hpow_hyperpow_eq2: 
   "\<And>a n. 0 \<le> a \<Longrightarrow> 0 < n \<Longrightarrow> a pow n = (if (a = 0) then 0 else a hpow (of_hypnat n))"
by transfer (simp add: powreal_power_eq2 )

lemma hpow_hypint:
  "\<And>x i. x > 0 \<Longrightarrow> x hpow (of_hypint i) = (if i \<ge> 0 then x pow hypnat i else 1 / x pow hypnat (-i))"
by transfer (metis powreal_int)

lemma hpow_power_eq:
  "\<And>a. a> 0 \<Longrightarrow> a hpow hypreal_of_nat n = a ^ n"
by transfer (simp add: powreal_power_eq)

lemma hpow_inverse_of_hypnat_gt_one: 
   "\<And>a N. \<lbrakk> a > 1; N \<noteq> 0 \<rbrakk> \<Longrightarrow> a hpow (inverse(of_hypnat N)) > 1"
by transfer (auto intro: powreal_inverse_of_nat_gt_one)

lemma hpow_inverse_of_nat_gt_one: 
   "\<And>a. \<lbrakk> a > 1; N \<noteq> 0 \<rbrakk> \<Longrightarrow> a hpow (inverse(of_nat N)) > 1"
by transfer (auto intro: powreal_inverse_of_nat_gt_one)

lemma Infinitesimal_hyperpow_less_one_lemma:
  "\<And>x r. \<lbrakk>hnorm (x::'a::real_normed_algebra_1 star) < 1; 0 < r \<rbrakk> 
        \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. hnorm (x pow n) <  r"
  using LIMSEQ_iff LIMSEQ_power_zero 
  by transfer force

lemma hpow_add: "\<And>a x y. 0 < a \<Longrightarrow> a hpow (x + y) = a hpow x * a hpow y"
by transfer (metis powreal_add)

lemma hpow_eq_square: "\<And>x. 0 < x \<Longrightarrow> x hpow 2 = x * x"
by (metis hpow_add hpow_one one_add_one)

lemma hpow_minus_eq_hpow:
  "\<lbrakk> 0 < a; 0 < b; a hpow -x = b hpow y \<rbrakk> \<Longrightarrow> a hpow x = b hpow - y"
by (metis hpow_minus inverse_inverse_eq)


lemma hpow_half_divide_eq:
  "0 < y \<Longrightarrow> y hpow (1/2) / y = inverse(y hpow (1/2))"
proof -
  assume a1: "0 < y"
  then have "y = y hpow 1"
    by simp
  then have "y = y hpow (1/2) * y hpow (1/2)"
    by (metis a1 field_sum_of_halves hpow_add)
  moreover have "y hpow (1/2) > 0"
    by (simp add: a1 hpow_gt_zero)
  ultimately show ?thesis
    by (metis divide_eq_0_iff inverse_eq_divide nonzero_divide_mult_cancel_right) 
qed

lemma less_hpow_half_lemma:
  "\<lbrakk> 0 < x; 0 < y; x < y hpow (1/2) \<rbrakk> \<Longrightarrow> x/y < inverse(y hpow (1/2))"
by (metis divide_strict_right_mono hpow_half_divide_eq)

lemma le_hpow_half_lemma:
  "\<lbrakk> 0 < x; 0 < y; x \<le> y hpow (1/2) \<rbrakk> \<Longrightarrow> x/y \<le> inverse(y hpow (1/2))"
by (metis divide_le_cancel hpow_half_divide_eq less_asym)


subsection\<open>Relating pow and hpow\<close>

lemma hpow_hyperpow_eq_hpow: "0 < a \<Longrightarrow> (a hpow x) pow n = a hpow (x * of_hypnat n)"
by (metis hpow_gt_zero hpow_hyperpow_eq hpow_mult)

lemma hpow_divide_pow_cancel:
  assumes "a > 1" "j \<noteq> 0"
  shows "(a hpow (z/of_hypnat j)) pow j = a hpow z"
using assms hpow_hyperpow_eq_hpow by simp

lemma hpow_inverse_of_hypnat_cancel:
     "\<lbrakk> 0 < a; 0 < N \<rbrakk> \<Longrightarrow> a = (a hpow (inverse(of_hypnat N))) hpow (of_hypnat  N)"
by (simp add: hpow_mult)

lemma hpow_inverse_of_hypnat_pow_cancel:
   "\<lbrakk> 0 < a; 0 < N \<rbrakk> \<Longrightarrow> (a hpow (inverse(of_hypnat N))) pow N = a"
by (metis hpow_gt_zero hpow_hyperpow_eq hpow_inverse_of_hypnat_cancel)

lemma hpow_inverse_of_hypnat_pow_cancel2:
   "\<lbrakk> a > 1; N \<in> HNatInfinite \<rbrakk> \<Longrightarrow> a = (a hpow (inverse(of_hypnat N))) pow N"
by (metis hpow_inverse_of_hypnat_pow_cancel order_less_trans zero_less_HNatInfinite zero_less_one)

lemma HNatInfinite_hpow_inverse_gt_one: 
   "\<lbrakk> a > 1; N \<in> HNatInfinite \<rbrakk> \<Longrightarrow> a hpow (inverse(of_hypnat N)) > 1"
by (metis HNatInfinite_of_hypnat_gt_zero hpow_gt_one inverse_positive_iff_positive)

lemma HNatInfinite_hpow_eq_Ex: 
  assumes "a > 1" and "N \<in> HNatInfinite"
  shows "\<exists>u>0. a hpow (inverse(of_hypnat N)) = 1 + u"
proof -
  have "a hpow inverse (hypreal_of_hypnat N) > 1"
    by (simp add: HNatInfinite_hpow_inverse_gt_one assms)
  then have "a hpow inverse (hypreal_of_hypnat N) - 1 > 0"
    by simp
  then show ?thesis by fastforce
qed

subsection\<open>Some nonstandardard theorems \<close>

lemma hpow_inverse_hypreal_of_nat_approx_one_cancel:
  assumes "a > 0" 
      and "m > 0" 
      and "a hpow inverse (hypreal_of_nat m) \<approx> 1" 
    shows "a \<approx> 1"
proof -
  have "(a hpow inverse (hypreal_of_nat m)) ^ m \<approx> 1" 
    using hrealpow_approx_one assms(3) by blast 
  moreover have "(a hpow inverse (hypreal_of_hypnat (of_nat m))) pow of_nat m = a"
    using assms(1) assms(2) hpow_inverse_of_hypnat_pow_cancel of_nat_0_less_iff by blast
  ultimately show ?thesis
    by (simp add: hyperpow_hypnat_of_nat) 
qed

lemma HNatInfinite_hpow_inverse_approx_one_cancel:
  "\<lbrakk> a > 0; \<not>(a \<approx> 1); (a hpow (inverse(of_hypnat N))) \<approx> 1; N \<noteq> 0 \<rbrakk> \<Longrightarrow> N \<in> HNatInfinite"
  using HNatInfinite_not_Nats_iff Nats_def hpow_inverse_hypreal_of_nat_approx_one_cancel 
  by (auto simp add: Nats_def)

lemma HFinite_hpow1:
  assumes "a \<in> HFinite"
      and "x \<in> HFinite"
      and "1 \<le> a" 
  shows "a hpow x \<in> HFinite"
proof (cases "a = 1")
  case True
  then show ?thesis by simp
next
  case False
  then have a_gt_1: "a > 1"
    using assms(3) le_less by simp
  obtain n where "x < hypreal_of_nat n"
    using HFinite_less_Nat_Ex Nats_cases assms(2) by blast
  then have "a hpow x < a hpow hypreal_of_nat n"
    using hpow_less_mono a_gt_1
    by blast
  then have "a hpow x < a ^ n"
    using assms(3) hpow_power_eq by auto
  moreover have "a ^ n \<in> HFinite"
    by (simp add: assms(1) hrealpow_HFinite)
  ultimately show ?thesis
    by (meson HFinite_bounded assms(3) hpow_gt_zero less_imp_le less_le_trans zero_less_one)
qed


lemma HFinite_hpow2:
  assumes "a \<in> HFinite - Infinitesimal"
      and "x \<in> HFinite"
      and "0 < a"
      and "a < 1"
  shows "a hpow x \<in> HFinite"
proof -
  have "1 < 1/a"
    by (simp add: assms(3) assms(4))
  moreover have "-x \<in> HFinite"
    by (simp add: HFinite_minus_iff assms(2))
  ultimately have "(1/a) hpow -x \<in> HFinite"
    by (metis HFinite_hpow1 HFinite_inverse2 assms(1) inverse_eq_divide less_le)
  then show ?thesis
    by (simp add: assms(3) hpow_divide hpow_minus)
qed
    
lemma HFinite_hpow3:
   "\<lbrakk> a \<in> HFinite - Infinitesimal; x \<in> HFinite; 0 < a \<rbrakk> \<Longrightarrow> a hpow x \<in> HFinite"
by (metis DiffE HFinite_hpow1 HFinite_hpow2 linorder_not_less)

lemma HFinite_hpow_not_Infinitesimal: 
  assumes "a \<in> HFinite"
  and "x \<in> HFinite"
  and "1 \<le> a" 
shows "a hpow x \<notin> Infinitesimal"
proof 
  have "a hpow x \<noteq> 0"
    using assms(3) hpow_not_zero by auto
  moreover assume "a hpow x \<in> Infinitesimal"
  then have "inverse (a hpow x) \<in> HInfinite"
    using Infinitesimal_inverse_HInfinite calculation by blast
  then have "a hpow - x \<notin> HFinite"
    using HFinite_not_HInfinite assms(3) hpow_minus by auto
  then show False
    using HFinite_hpow1 HFinite_minus_iff assms by blast 
qed

lemma HFinite_hpow_HFinite_Diff_Infinitesimal:
  "\<lbrakk> a \<in> HFinite; x \<in> HFinite; a \<ge> 1 \<rbrakk> \<Longrightarrow> a hpow x \<in> HFinite - Infinitesimal"
by (metis Diff_iff HFinite_hpow1 HFinite_hpow_not_Infinitesimal)

lemma approx_hpow_minus_hpow:
  "\<lbrakk> 0 < a; 0 < b; a hpow -x \<approx> b hpow y; a hpow x \<in> HFinite - Infinitesimal \<rbrakk> \<Longrightarrow> a hpow x \<approx> b hpow - y"
  by (metis HFinite_not_Infinitesimal_inverse approx_inverse approx_reorient hpow_minus inverse_inverse_eq)

lemma HNatInfinite_hpow_inverse_approx_one:
  assumes "a \<in> HFinite" 
  and "a > 1"
  and "N \<in> HNatInfinite"
  shows "(a hpow (inverse(of_hypnat N))) \<approx> 1"
proof -
  obtain u where u0: "u > 0" and lhs: "a hpow inverse (hypreal_of_hypnat N) = 1 + u"
    using HNatInfinite_hpow_eq_Ex assms(2) assms(3) by blast 
  then have "(a hpow inverse (hypreal_of_hypnat N)) pow N = (1 + u) pow N"
    by simp
  also obtain x where "\<dots> = 1 + hypreal_of_hypnat N * u + x" and x0: "x \<ge> 0"
    by (metis add.commute hyperbinomial_expand_first_two_terms' less_imp_le u0)
    then have "a = 1 + hypreal_of_hypnat N * u + x"
    using assms(2) assms(3) calculation hpow_inverse_of_hypnat_pow_cancel2 by auto
  then have "u \<le> (a - 1) / hypreal_of_hypnat N"
    using assms(2) assms(3)  u0 x0 
    by (auto simp add: le_divide_eq zero_less_HNatInfinite)
  moreover have "(a - 1) / hypreal_of_hypnat N \<in> Infinitesimal"
    by (simp add: HFinite_diff Infinitesimal_HFinite_mult2 assms(1) assms(3) divide_inverse) 
  ultimately have "u \<in> Infinitesimal"
    using u0 Infinitesimal_interval2 Infinitesimal_zero
    by (metis less_imp_le)
  then show ?thesis
    using bex_Infinitesimal_iff2 lhs by blast 
qed

lemma HNatInfinite_hpow_inverse_diff_one_Infinitesimal:
  "\<lbrakk> a \<in> HFinite; a > 1; N \<in> HNatInfinite \<rbrakk> \<Longrightarrow> (a hpow (inverse(of_hypnat N))) - 1 \<in> Infinitesimal"
by (metis HNatInfinite_hpow_inverse_approx_one bex_Infinitesimal_iff)

lemma HNatInfinite_hpow_inverse_approx_one2:
  "\<lbrakk> a \<in> HFinite; a > 1; N \<in> HNatInfinite \<rbrakk> \<Longrightarrow> (a hpow (1/of_hypnat N)) \<approx> 1"
by (simp add: divide_inverse HNatInfinite_hpow_inverse_approx_one)

text\<open>One of the results that we want on our way to derive the exponential series a la Euler\<close>
lemma Infinitesimal_pos_hpow_approx_one:
  assumes HFinite_a: "a \<in> HFinite"
  and a_gt1: "a > 1"
  and e_gt0: "e > 0"
  and Infinitesimal_e: "e \<in> Infinitesimal"
  shows "a hpow e \<approx> 1"
proof -
  have gt0: "0 < hypnat (hfloor (1 / e))"
    using e_gt0 Infinitesimal_e hypreal_HNatInfinite_hfloor_inverse_Infinitesimal zero_less_HNatInfinite 
    by blast
  have ele: "e \<le> 1/(of_hypint (hfloor(1/e)))"
    by (metis (no_types, lifting) div_by_1 divide_pos_pos e_gt0 gt0 hfloor_correct inverse_divide 
        inverse_le_iff_le of_hypint_0_less_iff zero_less_hypnat_eq zero_less_one)
  have "inverse(of_hypint (hfloor(1/e)) + 1) < e"
    by (simp add: e_gt0 hfloor_less_cancel inverse_eq_divide inverse_less_imp_less) 
   then have "a hpow inverse (hypreal_of_hypnat (hypnat (hfloor (1 / e)) + 1)) - 1 \<le> a hpow e - 1"
     by (simp add: a_gt1 e_gt0 less_imp_le)
   moreover have "a hpow e - 1 \<le> a hpow inverse (hypreal_of_hypnat (hypnat (hfloor (1 / e)))) - 1"
     using assms gt0 ele
     by (simp add: inverse_eq_divide)
  moreover have "a hpow inverse (hypreal_of_hypnat (hypnat (hfloor (1 / e)))) - 1 \<in> Infinitesimal"
    using HNatInfinite_hpow_inverse_diff_one_Infinitesimal assms 
          hypreal_HNatInfinite_hfloor_inverse_Infinitesimal 
    by blast
  ultimately have "a hpow e - 1 \<in> Infinitesimal"
    by (meson Infinitesimal_interval2 Infinitesimal_zero a_gt1 e_gt0 diff_ge_0_iff_ge 
        hpow_ge_one less_imp_le)
  then show ?thesis
    using bex_Infinitesimal_iff 
    by blast
qed

lemma Infinitesimal_neg_hpow_approx_one:
   "\<lbrakk> a \<in> HFinite; a > 1; e > 0; e \<in> Infinitesimal\<rbrakk> \<Longrightarrow> a hpow -e \<approx> 1"
  using Infinitesimal_pos_hpow_approx_one approx_inverse hpow_minus by fastforce

text\<open>And the next result, without e>0 restriction!\<close>

lemma Infinitesimal_hpow_approx_one:
  assumes "a \<in> HFinite" 
      and "a > 1"
      and " e \<in> Infinitesimal"
    shows "a hpow e \<approx> 1"
proof -
  have "e < 0 \<or> e = 0 \<or> 0 < e"
    by (simp add: less_linear)
  then show ?thesis 
  proof (safe)
    assume "e < 0" 
    then show ?thesis
      using Infinitesimal_neg_hpow_approx_one assms 
      by force 
  next
    show "a hpow 0 \<approx> 1"
      using assms(2) by auto
  next 
    assume "e > 0" 
    then show ?thesis
      using Infinitesimal_pos_hpow_approx_one assms 
      by force
  qed
qed

lemma hpow_HFinite_approx_1_lemma1:
  assumes x_finite: "x \<in> HFinite" 
      and a_infclose_1: "a \<approx> 1" 
      and a_ge_1: "a \<ge> 1"  and x_gt_0: "x > 0" 
  shows "a hpow x \<approx> 1"
proof (cases "a = 1")
  assume "a = 1" 
  then show ?thesis 
     by simp
next
  assume "a \<noteq> 1" 
  then have a_gt_1: "a > 1" 
    using a_ge_1 by simp
  obtain n where xn: "of_nat n \<le> x" and  xn1: "x < of_nat (n + 1)"
    using HFinite_between_Nats x_finite x_gt_0 
    by (metis (no_types, lifting) Nats_cases of_nat_1 of_nat_add)  
  then have "a ^ n \<le> a hpow x"
    by (metis a_ge_1 a_gt_1 hpow_le_mono hpow_power_eq less_trans zero_less_one)
  moreover have "a hpow x < a ^ (n + 1)"
    by (metis a_ge_1 a_gt_1 hpow_less_mono hpow_power_eq less_le_trans xn1 zero_less_one)
  moreover have "a ^ n \<approx> 1"
    by (simp add: a_infclose_1 hrealpow_approx_one) 
  moreover have "a ^ (n + 1) \<approx> 1"
    using a_infclose_1 hrealpow_approx_one by blast
  ultimately show ?thesis
    by (meson approx_le_bound approx_sym approx_trans less_imp_le) 
qed

lemma approx_hpow:
  assumes "y \<in> HFinite" and "a \<in> HFinite"
      and "a > 1" and "x \<approx> y"
    shows "a hpow x \<approx> a hpow y"
proof -
  have "x - y \<in> Infinitesimal"
    using approx_def assms(4) by auto
  then have "a hpow (x - y) \<approx> 1"
    using Infinitesimal_hpow_approx_one assms(2) assms(3) by blast
  then have axy_approx_1: "a hpow x / a hpow y \<approx> 1"
    using assms(3) hpow_divide2 by auto
   have "a hpow y \<in> HFinite"
    by (simp add: HFinite_hpow1 assms(1,2,3) less_imp_le) 
  then show ?thesis 
    using approx_mult2 [OF axy_approx_1] hpow_not_zero assms(3)
    by fastforce
qed

end