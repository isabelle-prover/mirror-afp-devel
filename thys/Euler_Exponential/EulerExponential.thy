(*  Title:  Euler_Exponential.thy
    Author: Jacques D. Fleuriot, University of Edinburgh, 2026
*)

section\<open>Deriving the exponential series Euler-style\<close>

theory  EulerExponential
imports  HyperBinomial HyperLog 
begin

subsection\<open>Euler's witness: Introductio, paragraph 114\<close>

text\<open>We show explicitly that Euler's witness (that he denotes by k) 
     is a finite quantity. The existence is merely stated by Euler 
     and finiteness is only argued using an example, with Euler merely 
     stating that: 

     "We see that k is a finite number which depends on the value of the base a".
\<close>

lemma Introductio_114_HFinite_witness:
      assumes infinitesimal_exponent: "e \<in> Infinitesimal"
      and exponent_gt_zero: "e > 0"
      and base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1" 
      shows "(a hpow e - 1)/e \<in> HFinite"
proof -
  have agt0: "a > 0"
    using base_greater_1 less_trans zero_less_one by blast 
  let ?k = "(a hpow e - 1)/e" 
  have "(a hpow e) pow hypnat(hfloor(1/e)) = (1 + ?k * e) pow hypnat(hfloor(1/e))"
    by (simp add: exponent_gt_zero neq_iff)
  then
  obtain x 
    where xprops: "x \<ge> 0"
                  "a hpow (e * of_hypnat(hypnat(hfloor(1/e)))) = 
                   1 + of_hypnat(hypnat(hfloor(1/e))) * (?k * e) + x" 
    using hyperbinomial_expand_first_two_terms hpow_hyperpow_eq_hpow 
          [symmetric] base_greater_1 exponent_gt_zero agt0 
    by (metis diff_ge_0_iff_ge divide_nonneg_pos hpow_ge_one mult_nonneg_nonneg 
        order.strict_implies_order)
  then have "a \<approx> 1 + of_hypnat(hypnat(hfloor(1/e))) * (?k * e) + x" 
    using approx_hpow base_finite base_greater_1 exponent_gt_zero 
          Infinitesimal_hfloor_inverse_mult_self_pos
    by (metis HFinite_1 agt0 approx_sym divide_pos_pos hpow_one infinitesimal_exponent 
        of_hypnat_hypnat_of_hypint zero_less_one less_le)
  then have "1 + of_hypnat(hypnat(hfloor(1/e))) * (?k * e) + x \<in> HFinite"
    using approx_HFinite base_finite 
    by blast 
  moreover have "of_hypnat(hypnat(hfloor(1/e))) * ?k * e \<ge> 0"
    by (simp add: base_greater_1 exponent_gt_zero hpow_ge_one less_imp_le)
  ultimately have "of_hypnat(hypnat(hfloor(1/e))) * (?k * e) \<in> HFinite" 
    using HFinite_add_imp_HFinite xprops(1) zero_le_one
    by (metis (no_types, lifting) add.commute add_nonneg_nonneg mult.assoc) 
  then show "?k \<in> HFinite"
    using Infinitesimal_hfloor_inverse_mult_self_pos approx_1_mult_HFinite_HFinite 
          infinitesimal_exponent exponent_gt_zero
          of_hypnat_hypnat_of_hypint
    by (metis (no_types, lifting) divide_pos_pos mult.assoc mult.commute zero_less_one less_le) 
qed


text\<open>Proposition 114, with some finite k.\<close>

lemma Introductio_114_pos:
      assumes infinitesimal_exponent: "e \<in> Infinitesimal"
      and exponent_gt_zero: "e > 0"
      and base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1" 
    shows "\<exists>k\<in>HFinite. k > 0 \<and> a hpow e = 1 + k * e"
proof -
  have "(a hpow e - 1)/e \<in> HFinite" and "(a hpow e - 1)/e > 0"
    using Introductio_114_HFinite_witness assms hpow_gt_one 
    by auto
  then show ?thesis
    using exponent_gt_zero le_add_diff_inverse 
    by auto 
qed


text\<open>This case, not discussed explicitly by Euler, is also needed to eventually 
     deal with finite, negative exponents.\<close>

lemma Introductio_114_neg:
      assumes infinitesimal_exponent: "e \<in> Infinitesimal"
      and exponent_less_zero: "e < 0"
      and base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1" 
      shows "\<exists>k\<in>HFinite. k > 0 \<and> a hpow e = 1 + k * e"
proof - 
  obtain k where ks: "k \<in> HFinite" "k > 0" "a hpow -e = 1 + k * -e"
    using Introductio_114_pos assms
    by (meson Infinitesimal_minus_iff neg_0_less_iff_less) 
  then have "(a hpow e) * (a hpow -e) = (1 + k * -e) * (a hpow e)"  
    by simp
  then have "1 = a hpow e + (k * a hpow e) * -e"
    using base_greater_1 hpow_add[symmetric] hpow_zero_eq_one 
    by (simp add: algebra_simps ) 
  then have a_hpow_e: "a hpow e = 1 + (k * (a hpow e)) * e" 
    by linarith
  have HFinite_k_mult: "k * (a hpow e) \<in> HFinite"
    by (meson HFinite_0 HFinite_hpow1 HFinite_mult Infinitesimal_approx 
        approx_HFinite base_finite base_greater_1 infinitesimal_exponent ks(1) 
        le_less not_Infinitesimal_not_zero) 
  have "k * (a hpow e) > 0" using base_greater_1 hpow_gt_zero ks(2) 
    by auto 
  thus ?thesis using a_hpow_e HFinite_k_mult 
    by blast
qed

lemma Introductio_114_HFinite_witness2:
      assumes infinitesimal_exponent: "e \<in> Infinitesimal"
      and exponent_less_zero: "e < 0"
      and base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1" 
    shows "(a hpow e - 1)/e \<in> HFinite"
proof -
  have e_ne_0: "e \<noteq> 0" 
    using exponent_less_zero 
    by simp
  obtain k where ks: "k \<in> HFinite" "k > 0" "a hpow e = 1 + k * e"
    using Introductio_114_neg assms 
    by blast
  from ks(3) have "a hpow e - 1 = k * e" 
    by simp
  then have "(a hpow e - 1)/e = k * e / e" 
    by simp
  also have "\<dots> = k" using e_ne_0 
    by simp
  finally show ?thesis using ks(1) 
    by simp
qed

lemma Introductio_114_HFinite_witness_full:
      assumes "x \<in> Infinitesimal"
      and "a \<in> HFinite"
      and "a > 1" 
    shows "(a hpow x - 1)/x \<in> HFinite"
  by (metis assms HFinite_0 Introductio_114_HFinite_witness Introductio_114_HFinite_witness2  
      divide_eq_0_iff linorder_neqE_linordered_idom)

subsection\<open>Defining Euleur's finite witness\<close>

text\<open>In fact, let us introduce a definition that will enable us to characterize  Euler's k, 
     (called the scaling factor by McKinzie and Tuckey but also left undefined by them).\<close>

definition eulerK :: "hypreal \<Rightarrow> hypreal \<Rightarrow> hypreal" where
  "eulerK a x \<equiv> (a hpow x - 1)/ x"

lemma eulerK_neg_exponent:
  assumes "a > 0" and "e \<noteq> 0"
  shows "eulerK a (-e) = eulerK a e / (a hpow e)"
proof -
  have ane0: "a hpow e \<noteq> 0"
    using assms(1) hpow_not_zero by blast
  have "eulerK a (-e) = (inverse (a hpow e) - 1) / (-e)"
    using assms(1) hpow_minus by (simp add: eulerK_def)
  also have "\<dots> = ((1 - a hpow e) / (a hpow e)) / (-e)"
    using ane0 by (simp add: inverse_eq_divide diff_divide_distrib)
  also have "\<dots> = (a hpow e - 1) / (a hpow e * e)"
    by (simp add: diff_divide_distrib)
  also have "\<dots> = ((a hpow e - 1) / e) / (a hpow e)"
    using ane0 by (simp add: field_simps)
  finally show ?thesis by (simp add: eulerK_def)
qed


text\<open>Equivalent multiplicative form.\<close>

corollary eulerK_neg_exponent_mult:
  assumes "a > 0" and "e \<noteq> 0"
  shows "eulerK a (-e) * (a hpow e) = eulerK a e"
  using eulerK_neg_exponent assms hpow_not_zero by auto

lemma eulerK_neg_approx:
  assumes "a \<in> HFinite" and "a > 1" and "x \<in> Infinitesimal" 
  shows "eulerK a (-x) \<approx> eulerK a x"
proof -
  have "a > 0" using assms(2) by auto
  moreover have "eulerK a (-x) = eulerK a x / (a hpow x)"
    by (metis calculation add.inverse_neutral div_by_1 eulerK_neg_exponent hpow_zero_eq_one)
  moreover have "a hpow x \<approx> 1"
    using Infinitesimal_hpow_approx_one assms by blast
  moreover have "eulerK a x \<in> HFinite"
    by (simp add: Introductio_114_HFinite_witness_full assms eulerK_def)
  moreover have "a hpow x \<in> HFinite - Infinitesimal"
    by (meson HFinite_hpow_HFinite_Diff_Infinitesimal Infinitesimal_subset_HFinite assms order_less_le
        subsetD)
  ultimately show ?thesis
    by (metis DiffE HFinite_divide Infinitesimal_zero approx_mult2 approx_reorient 
        divide_eq_0_iff eulerK_def eulerK_neg_exponent_mult mem_infmal_iff 
        mult.right_neutral)
qed

corollary eulerK_epsilon_neg_approx:
  assumes "a \<in> HFinite" and "a > 1" 
  shows "eulerK a (-\<epsilon>) \<approx> eulerK a \<epsilon>"
  by (simp add: assms  epsilon_not_zero eulerK_neg_approx)

lemma Introductio_114_eulerK_witness:
  assumes "x \<in> Infinitesimal"
  and "a \<in> HFinite"
  and "a > 1" 
  shows "eulerK a x \<in> HFinite"
  using assms Introductio_114_HFinite_witness_full eulerK_def 
  by auto

lemma HFinite_eulerK_inverse_whn:
  assumes "a \<in> HFinite"
  and "a > 1" 
  shows "eulerK a (1/of_hypnat whn) \<in> HFinite"
  by (metis assms HNatInfinite_inverse_Infinitesimal HNatInfinite_whn Introductio_114_HFinite_witness_full
      eulerK_def inverse_eq_divide)

lemma Introductio_114_eulerK_epsilon_witness:
      assumes "a \<in> HFinite"
      and     "a > 1" 
      shows "eulerK a \<epsilon> \<in> HFinite"
  using assms Introductio_114_HFinite_witness_full
  by (simp add: eulerK_def)

lemma eulerK_neg_e_HFinite:
  assumes "e \<in> Infinitesimal" "e > 0" "a \<in> HFinite" "a > 1"
  shows "eulerK a (-e) \<in> HFinite"
  by (metis Infinitesimal_minus_iff Introductio_114_HFinite_witness_full assms(1,3,4) eulerK_def)

lemma Introductio_114_neg_eulerK_epsilon_witness:
  assumes "a \<in> HFinite" "a > 1"
  shows "eulerK a (-\<epsilon>) \<in> HFinite"
  by (simp add: assms  epsilon_gt_zero eulerK_neg_e_HFinite)

lemma eulerK_neg_e_gt_zero:
  assumes "e \<in> Infinitesimal" "e > 0" "a \<in> HFinite" "a > 1"
  shows "eulerK a (-e) > 0"
proof -
  have a_gt_0: "a > 0" using assms(4) by auto
  have "a hpow e > 1" using assms(4) assms(2) hpow_gt_one by blast
  then have "a hpow (-e) < 1"
    using a_gt_0 hpow_minus by (simp add: inverse_less_1_iff hpow_gt_zero)
  then have "a hpow (-e) - 1 < 0" by simp
  moreover have "-e < 0" using assms(2) by simp
  ultimately show ?thesis
    by (metis eulerK_def zero_less_divide_iff)
qed

lemma eulerK_neg_epsilon_gt_zero:
  assumes "a \<in> HFinite" "a > 1"
  shows "eulerK a (-\<epsilon>) > 0"
  by (simp add: assms epsilon_gt_zero eulerK_neg_e_gt_zero)

lemma Introductio_114_eulerK:
  shows "a > 0 \<Longrightarrow> a hpow e = 1 + eulerK a e * e"
  by (simp add: eulerK_def)

lemma Introductio_114_eulerK':
  shows "e \<noteq> 0 \<Longrightarrow> a hpow e = 1 + eulerK a e * e"
  by (simp add: eulerK_def)

lemma Introductio_114_eulerK_epsilon:
  shows "a hpow \<epsilon> = 1 + eulerK a \<epsilon> * \<epsilon>"
  by (simp add: epsilon_not_zero eulerK_def)

lemma Introductio_114_epsilon:
  "a > 1 \<Longrightarrow> \<epsilon> = hLog a (1 + eulerK a \<epsilon> * \<epsilon>)"
  using Introductio_114_eulerK_epsilon eulerK_def by fastforce

lemma eulerK_product_neg_e:
  assumes "a > 0" and "e \<noteq> 0"
  shows "eulerK a (-e) * (-e) = eulerK a e * (-e) / (a hpow e)"
proof -
  have "eulerK a (-e) = eulerK a e / (a hpow e)"
    using eulerK_neg_exponent assms by blast
  then show ?thesis by (simp add: field_simps)
qed

lemma eulerK_pow_neg_e:
  assumes "a > 0" and "e \<noteq> 0"
  shows "(eulerK a (-e) * (-e)) pow of_nat n = (eulerK a e * (-e)) pow of_nat n / (a hpow e) ^ n"
proof -
  have "(eulerK a (-e) * (-e)) pow of_nat n = (eulerK a e * (-e) / (a hpow e)) pow of_nat n"
    using eulerK_product_neg_e assms by simp
  also have "\<dots> = (eulerK a e * (-e)) pow of_nat n / (a hpow e) pow of_nat n"
    using hyperpow_divide by blast
  also have "\<dots> = (eulerK a e * (-e)) pow of_nat n / (a hpow e) ^ n"
    using hyperpow_of_nat by auto
  finally show ?thesis .
qed

subsection\<open>Euler's Introductio, Paragraph 115: first expansion\<close>

text\<open>This expansion is given by Euler who implicitly uses the Binomial theorem.\<close>

lemma Introductio_115_expansion_hchoose:
  "a > 0 \<Longrightarrow> (a hpow x) pow j = hypersum (\<lambda>i. of_hypnat (j hchoose i) * (eulerK a x * x) pow i) {0..j}"
  using Introductio_114_eulerK hyperbinomial_simple by auto

lemma Introductio_115_expansion_hffp:
  "a > 0 \<Longrightarrow> 
   (a hpow x) pow j = 
   hypersum (\<lambda>i. (hfallfactpow (of_hypnat j) i)/ hfact i * (eulerK a x * x) pow i) {0..j}"
  by (simp add: Introductio_114_eulerK hyperbinomial_hfallfactpow hyperbinomial_simple)

lemma Introductio_115_expansion_hchoose':
  "e \<noteq> 0 \<Longrightarrow> (a hpow e) pow j = hypersum (\<lambda>i. of_hypnat (j hchoose i) * (eulerK a e * e) pow i) {0..j}"
  using Introductio_114_eulerK' hyperbinomial_simple by auto

lemma Introductio_115_expansion_hchoose_epsilon:
  "(a hpow \<epsilon>) pow j = hypersum (\<lambda>i. of_hypnat (j hchoose i) * (eulerK a \<epsilon> * \<epsilon>) pow i) {0..j}"
  using Introductio_114_eulerK_epsilon hyperbinomial_simple by auto

(* Not used in the end *)
lemma HFinite_Infinitesimal_hpow_cancel_approx:
      assumes infinitesimal_exponent: "e \<in> Infinitesimal"
      and exponent_not_zero: "e \<noteq> 0"
      and base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1" 
      and exponentz_HFinite: "z \<in> HFinite"
    shows "(a hpow e) hpow of_hypint(hfloor(z/e)) \<approx> a hpow z"
proof -
  have hpow_pow: "(a hpow e) hpow of_hypint(hfloor(z/e)) = a hpow (e * of_hypint (hfloor(z/e)))"
    using base_greater_1 hpow_hyperpow_eq_hpow less_trans zero_less_one hpow_mult 
    by auto  
  have "(e * of_hypint (hfloor(z/e))) \<approx> z"
    using  Infinitesimal_hfloor_divide_mult exponent_not_zero 
           infinitesimal_exponent  by simp
  then have "a hpow (e * of_hypint (hfloor(z/e))) \<approx> a hpow z"
    using approx_hpow base_finite base_greater_1 exponentz_HFinite by blast
  thus ?thesis by (simp add: hpow_pow) 
qed 

lemma hpow_hypersum_pos_hchoose:
  assumes "e \<in> Infinitesimal" and "e > 0"
    and "a \<in> HFinite" and "a > 1" 
    and "z \<in> HFinite" and "z > 0"
    defines "N \<equiv> hypnat (hfloor (z / e))"
    shows "a hpow z \<approx> (\<Sum>\<^sub>h i\<in>{0..N}. hypreal_of_hypnat (N hchoose i) * (eulerK a e * e) pow i)"
proof -
  have "(a hpow e) pow N =  
           (\<Sum>\<^sub>h i\<in>{0..N}. of_hypnat (N hchoose i) * (eulerK a e * e) pow i)"
  using Introductio_115_expansion_hchoose assms(4) by fastforce 
  then show ?thesis 
    using assms Infinitesimal_hfloor_divide_mult hpow_hyperpow_eq_hpow approx_hpow 
    unfolding N_def 
    by (metis (lifting) approx_sym divide_pos_pos dual_order.strict_trans of_hypnat_hypnat_of_hypint order_less_le
        zero_less_one)
qed

lemma hpow_hypersum_pos_hffp:
  assumes "e \<in> Infinitesimal" and "e > 0"
      and "a \<in> HFinite" and "a > 1" 
      and "z \<in> HFinite" and "z > 0"
    defines "N \<equiv> hypnat (hfloor (z / e))"
    shows "a hpow z \<approx> 
           (\<Sum>\<^sub>h i\<in>{0..N}. hfallfactpow (of_hypnat N) i / hfact i * (eulerK a e * e) pow i)"
  by (metis (lifting) hpow_hypersum_pos_hchoose assms ext hyperbinomial_hfallfactpow)

lemma HFinite_Infinitesimal_hpow_hypersum_pos_eulerK_epsilon:
    assumes "a \<in> HFinite" and "a > 1" 
    and "z \<in> HFinite" and "z > 0"
    defines "N \<equiv> hypnat (hfloor (z/\<epsilon>))"
    shows "a hpow z \<approx>
              (\<Sum>\<^sub>h i\<in>{0..N}. hypreal_of_hypnat (N hchoose i) * (eulerK a \<epsilon> * \<epsilon>) pow i)"
  using hpow_hypersum_pos_hchoose Infinitesimal_epsilon assms epsilon_gt_zero
  by blast

lemma Infinitesimal_pow_hfallfactpow_le_pow:
      assumes infinitesimal_e: "e \<in> Infinitesimal"
      and e_gt_zero: "e > (0::hypreal)"
      and exponentz_HFinite: "z \<in> HFinite - Infinitesimal"
      and exponentz_gt_zero: "z > 0"
      defines "N \<equiv> hypnat (hfloor (z / e))"
      shows "e pow n * hfallfactpow (of_hypnat N) n \<le> z pow n"
proof - 
    have "hfallfactpow (hypreal_of_hypnat N) n \<le> (of_hypnat N) pow n" 
      by (metis hfallfactpow_le_hyperpow hfallfactpow_of_nat_eq_0_lemma 
          hyperpow_ge_zero not_le_imp_less of_hypnat_0_le_iff of_hypnat_less_iff)
    then have le1: 
          "e pow n * hfallfactpow (of_hypnat N) n \<le> e pow n *  (of_hypnat N) pow n"
      by (simp add: e_gt_zero hyperpow_gt_zero)
    have hfloor_gt_0: "of_hypnat N > (0::hypreal)" 
       by (simp add: field_simps N_def e_gt_zero, 
           meson DiffD2 Infinitesimal_interval Infinitesimal_zero 
           exponentz_HFinite exponentz_gt_zero infinitesimal_e not_le_imp_less) 
     have "e * of_hypnat N \<le> z"
       unfolding N_def
      by (metis  divide_nonneg_nonneg  e_gt_zero exponentz_gt_zero 
          leD less_imp_le mult.commute mult_imp_div_pos_less 
          not_less of_hypint_floor_le of_hypnat_hypnat zero_le_hfloor)  
     then have  "(e * of_hypnat N) pow n \<le> z pow n"
      using e_gt_zero hfloor_gt_0 hyperpow_le mult_pos_pos by blast
    thus ?thesis 
      using le1 unfolding N_def 
      by (metis (no_types, lifting) hyperpow_mult order_trans) 
qed

lemma HyperSummable_exp_terms:
      assumes infinitesimal_e: "e \<in> Infinitesimal"
      and e_gt_zero: "e > (0::hypreal)"
      and exponentz_HFinite: "z \<in> HFinite - Infinitesimal"
      and exponentz_gt_zero: "z > 0"
      and k_HFinite: "k \<in> HFinite" 
      and k_gt_zero: "k > 0"
      defines "N \<equiv> hypnat (hfloor (z / e))"
      shows "HyperSummable
             (\<lambda>i. hfallfactpow (of_hypnat N) i / hfact i * (k * e) pow i)"
proof -
  have internalf_summand: 
           "(\<lambda>i. hfallfactpow (of_hypnat N) i  / hfact i * (k * e) pow i) \<in> InternalFuns"
    by (simp add: InternalFuns_divide  InternalFuns_mult InternalFuns_of_hypnat)
  have internalf_compare: "(\<lambda>i. (k * z) pow i / hfact i) \<in> InternalFuns"
    by (simp add: InternalFuns_divide)
  {fix n :: "nat star" have 
             "0 \<le> hfallfactpow (of_hypnat N) n / hfact n * (k * e) pow n"
       by (meson divide_nonneg_pos e_gt_zero hfact_gt_zero hfallfactpow_ge_zero 
           hyperpow_ge_zero k_gt_zero mult_nonneg_nonneg order_less_le)
   }
   then have summand_ge_0: 
             "\<forall>n. 0 \<le> hfallfactpow (of_hypnat N) n / hfact n * (k * e) pow n" 
     by blast
   have hypersummable_compare: "HyperSummable (\<lambda>i. (k * z) pow i / hfact i)"
     using HFinite_mult HyperSummable_exp exponentz_HFinite k_HFinite by auto
     
   have  "\<exists>k'\<in>\<nat>. \<forall>n\<ge>k'. 
              hfallfactpow (of_hypnat N) n / hfact n * (k * e) pow n
              \<le> (k * z) pow n / hfact n"
   proof -
     {fix n :: "nat star" assume n_gt_0: "n \<ge> 0" 
       then have  "hfallfactpow (hypreal_of_hypnat N) n * e pow n \<le> z pow n"
         by (metis N_def Infinitesimal_pow_hfallfactpow_le_pow e_gt_zero exponentz_HFinite 
             exponentz_gt_zero infinitesimal_e mult.commute)
       then have  "hfallfactpow (hypreal_of_hypnat N) n * (k * e) pow n  \<le> (k * z) pow n"
          by (simp add: hyperpow_gt_zero hyperpow_mult k_gt_zero)
       }
       thus ?thesis using N_def Nats_0 divide_right_mono 
         by (metis hfact_gt_zero order_less_le times_divide_eq_left) 
   qed
   thus ?thesis using internalf_compare internalf_summand hypersummable_compare summand_ge_0
                      HyperSummable_hypreal_comparison_test
     by (metis (no_types, lifting) times_divide_eq_left) 
qed

text\<open>We compare against the previous series this time to show hypersum for negative exponent 
     is also summable\<close>

lemma HyperSummable_exp_terms2:
      assumes infinitesimal_e: "e \<in> Infinitesimal"
      and e_gt_zero: "e > (0::hypreal)"
      and exponentz_HFinite: "z \<in> HFinite - Infinitesimal"
      and exponentz_less_zero: "z < 0"
      and k_HFinite: "k \<in> HFinite" 
      and k_gt_zero: "k > 0"
      defines "N \<equiv> hypnat (hfloor (-z / e))"
      shows "HyperSummable (\<lambda>i. hfallfactpow (of_hypnat N) i / hfact i * (k * -e) pow i)"
proof - 
  have internalf_summand: 
          "(\<lambda>i. hfallfactpow (of_hypnat N) i / hfact i * (k * -e) pow i) \<in> InternalFuns"
    by (simp add: InternalFuns_divide  InternalFuns_mult InternalFuns_of_hypnat)
  have internalf_compare: 
          "(\<lambda>i. hfallfactpow (of_hypnat N) i / hfact i * (k * e) pow i) \<in> InternalFuns"
    by (simp add: InternalFuns_divide  InternalFuns_mult InternalFuns_of_hypnat)
  have zs: "- z \<in> HFinite - Infinitesimal" "-z > 0"
    using HFinite_minus_iff  Diff_iff Infinitesimal_minus_iff exponentz_HFinite exponentz_less_zero 
    by auto 
    have le_terms: 
          "\<exists>ka\<in>\<nat>. \<forall>n\<ge>ka. 
               hnorm (hfallfactpow (of_hypnat N) n / hfact n * (k * - e) pow n)
               \<le> hfallfactpow (of_hypnat N) n / hfact n * (k * e) pow n"
    proof -
    {fix n :: "nat star" assume n_gt_0: "n \<ge> 0" 
     then have "\<bar>hfallfactpow (of_hypnat N) n *  (k * - e) pow n\<bar>
                \<le>  hfallfactpow (of_hypnat N) n * (k * e) pow n"
     proof (cases "hfallfactpow (of_hypnat N) n = (0::hypreal)")
       assume "hfallfactpow (of_hypnat N) n = (0::hypreal)"
       then show ?thesis by (simp add: N_def)
     next 
       assume "hfallfactpow (of_hypnat N) n \<noteq> (0::hypreal)"
       then have "hfallfactpow (of_hypnat N) n > (0::hypreal)"
         by (simp add: order.not_eq_order_implies_strict N_def)
       then show ?thesis
         by (metis (no_types, lifting) abs_mult abs_of_nonneg e_gt_zero 
             hrabs_hyperpow_minus hyperpow_ge_zero k_gt_zero le_less mult_minus_right 
             mult_nonneg_nonneg)    
     qed            
     then have "hnorm(hfallfactpow (of_hypnat N) n *  (k * - e) pow n)
                \<le>  hfallfactpow (of_hypnat N) n * (k * e) pow n"
       by simp         
   }
   thus ?thesis 
     using Nats_0 divide_right_mono of_hypnat_0_le_iff
     by (metis (no_types, lifting) hnorm_divide hnorm_hypreal_of_hypnat 
         of_hypnat_hfact times_divide_eq_left) 
   qed
   then show ?thesis 
     using HyperSummable_comparison_test [OF internalf_summand internalf_compare] 
           HyperSummable_exp_terms zs infinitesimal_e e_gt_zero k_HFinite k_gt_zero 
     unfolding N_def 
     by blast
qed

lemma HyperSummable_binomial_neg_hchoose:
  assumes infinitesimal_e: "e \<in> Infinitesimal"
      and infitesimal_e_gt_zero: "e > 0"
      and base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1"
      and exponentz_HFinite: "z \<in> HFinite - Infinitesimal"
      and exponentz_less_zero: "z < 0"
    defines "N \<equiv> hypnat (hfloor(-z/e))"
  shows "HyperSummable (\<lambda>i. of_hypnat (N hchoose i) * (eulerK a e * -e) pow i)"
proof -
  let ?k = "eulerK a e"
  have eq: "(\<lambda>i. hypreal_of_hypnat (N hchoose i) * (?k * -e) pow i) =
            (\<lambda>i. hfallfactpow (hypreal_of_hypnat N) i / hfact i * 
                 (?k * -e) pow i)"
    by (simp add: hyperbinomial_hfallfactpow)
  moreover have "eulerK a e \<in> HFinite"
    by (simp add: Introductio_114_eulerK_witness base_finite base_greater_1 infinitesimal_e)
  moreover have "eulerK a e > 0"
    by (simp add: base_greater_1 eulerK_def hpow_gt_one infitesimal_e_gt_zero)
  ultimately show ?thesis
    unfolding N_def
    by (metis (no_types, lifting) ext HyperSummable_exp_terms2 exponentz_HFinite exponentz_less_zero 
        hyperbinomial_hfallfactpow infinitesimal_e infitesimal_e_gt_zero)
qed

lemma HyperSummable_binomial_neg_hchoose':
  assumes infinitesimal_e: "e \<in> Infinitesimal"
      and infitesima_e_gt_zero: "e > 0"
      and base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1"
      and exponentz_HFinite: "z \<in> HFinite - Infinitesimal"
      and exponentz_less_zero: "z < 0"
    defines "N \<equiv> hypnat (hfloor(-z/e))"
    shows "HyperSummable (\<lambda>i. of_hypnat (N hchoose i) * (eulerK a (-e) * -e) pow i)"
proof -
  let ?k = "eulerK a (-e)"
  have k_HFinite: "?k \<in> HFinite"
    by (simp add: Introductio_114_eulerK_witness base_finite base_greater_1 infinitesimal_e)
  moreover have k_gt_zero: "?k > 0"
    by (simp add: base_finite base_greater_1 eulerK_neg_e_gt_zero infinitesimal_e infitesima_e_gt_zero)
  moreover have eq: 
           "(\<lambda>i. of_hypnat (N hchoose i) * (?k * -e) pow i) =
            (\<lambda>i. hfallfactpow (of_hypnat N) i / hfact i * (?k * -e) pow i)"
    by (rule ext, simp add: hyperbinomial_hfallfactpow)
  ultimately show ?thesis
    using HyperSummable_exp_terms2 exponentz_HFinite exponentz_less_zero infinitesimal_e 
          infitesima_e_gt_zero 
    unfolding N_def
    by presburger
qed

lemma hpow_hypersum_neg_hchoose:
  assumes infinitesimal_e: "e \<in> Infinitesimal"
      and infinitesimal_e_gt_zero: "e > 0"
      and base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1" 
      and exponentz_HFinite: "z \<in> HFinite"
      and exponentz_less_zero: "z < 0"
      defines "N \<equiv> hypnat (hfloor (- z/e))"
      shows "a hpow z \<approx>
             (\<Sum>\<^sub>h i\<in>{0..N}. of_hypnat (N hchoose i) * (eulerK a (- e) * - e) pow i)"
proof -
  have ze_pos: "- z/e \<ge> 0"
    by (simp add: divide_nonpos_pos exponentz_less_zero infinitesimal_e_gt_zero order_less_imp_le)
   have "(a hpow -e) pow N =  
        hypersum (\<lambda>i. of_hypnat (N hchoose i) * (eulerK a (-e) * -e) pow i) {0..N}"
     using Introductio_115_expansion_hchoose' infinitesimal_e_gt_zero 
     by force
   moreover have "a hpow (-e * of_hypnat N) \<approx> a hpow z"
     unfolding N_def
     by (metis Infinitesimal_hfloor_divide_mult approx_hpow approx_minus_cancel base_finite 
         base_greater_1 exponentz_HFinite infinitesimal_e infinitesimal_e_gt_zero mult_minus_left 
         of_hypnat_hypnat_of_hypint order_less_le verit_minus_simplify(4) ze_pos)
    ultimately show ?thesis
      by (metis approx_sym base_greater_1 dual_order.strict_trans hpow_hyperpow_eq_hpow zero_less_one)
  qed

lemma hyperpow_nat_approx:
      assumes infinitesimal_e: "e \<in> Infinitesimal"
      and e_gt_0: "e > (0::hypreal)"
      and z_HFinite_not_Infinitesimal: "z \<in> HFinite - Infinitesimal"
      and z_gt_0: "z > 0"
      shows "z pow of_nat i \<approx> (hfallfactpow (of_hypnat(hypnat(hfloor(z/e)))) (of_nat i)) * (e pow of_nat i)"
proof -
  have "z/e \<in> HInfinite" 
      using infinitesimal_e z_HFinite_not_Infinitesimal e_gt_0
        by (metis DiffD2 HInfinite_HFinite_disj Infinitesimal_ratio less_numeral_extra(3))   
      then have HNatInfinite_ze: "hypnat(hfloor(z/e)) \<in> HNatInfinite" 
        using divide_pos_pos e_gt_0 hypreal_HNatInfinite_hfloor z_gt_0
        by blast  
      then have hfall_div_pow_1: "(hfallfactpow (of_hypnat(hypnat(hfloor(z/e)))) (of_nat i)) /
                (hypreal_of_hypnat(hypnat(hfloor(z/e))) pow of_nat i) \<approx> 1"
        using HNatInfinite_hfallfactpow_divide_hyperpow_of_nat 
        by blast
      have z_pow_HFinite: "z pow of_nat i \<in> HFinite"
          by (metis DiffE hrealpow_HFinite hyperpow_of_nat z_HFinite_not_Infinitesimal) 
      have "(e * of_hypnat(hypnat(hfloor(z/e)))) pow of_nat i \<approx> z pow of_nat i"
        by (metis DiffE HNatInfinite_of_hypnat_gt_zero HNatInfinite_ze Infinitesimal_hfloor_divide_mult 
            division_ring_divide_zero hfloor_zero hrealpow_approx hyperpow_of_nat hypint_hypnat_eq 
            infinitesimal_e less_numeral_extra(3) of_hypnat_hypnat z_HFinite_not_Infinitesimal)
      then have  "(hfallfactpow (of_hypnat(hypnat(hfloor(z/e)))) (of_nat i)) /
                (hypreal_of_hypnat(hypnat(hfloor(z/e))) pow of_nat i) * 
             (e * of_hypnat(hypnat(hfloor(z/e)))) pow of_nat i \<approx> z pow of_nat i"
        by (metis HFinite_1 approx_mult_HFinite hfall_div_pow_1 mult.left_neutral z_pow_HFinite)
      thus ?thesis 
        using HNatInfinite_ze
        by (metis (no_types, lifting) hyperpow_divide nonzero_mult_div_cancel_right 
            of_hypnat_eq_0_iff of_nat_0 of_nat_eq_star_of star_of_neq_HNatInfinite 
            times_divide_eq_left times_divide_eq_right approx_sym)
qed

lemma hyperpow_nat_approx':
      assumes infinitesimal_e: "e \<in> Infinitesimal"
      and e_gt_0: "e > (0::hypreal)"
      and z_HFinite_not_Infinitesimal: "z \<in> HFinite - Infinitesimal"
      and z_gt_0: "z > 0"
      and Nats_i: "i \<in> \<nat>"
    shows "z pow i \<approx> (hfallfactpow (of_hypnat(hypnat(hfloor(z/e)))) i) * (e pow i)"
  using assms hyperpow_nat_approx Nats_hypnat_of_nat_iff by auto

lemma HFinite_not_Infinitesimal_pow_of_nat_eq_hfallfactpow_neg:
      assumes infinitesimal_e: "e \<in> Infinitesimal"
      and e_gt_0: "e > (0::hypreal)"
      and z_HFinite_not_Infinitesimal: "z \<in> HFinite - Infinitesimal"
      and z_less_0: "z < 0"
      shows "z pow of_nat i \<approx> (hfallfactpow (of_hypnat(hypnat(hfloor(-z/e)))) (of_nat i)) * ((-e) pow of_nat i)"
proof -
  have "z/e \<in> HInfinite" 
    using infinitesimal_e z_HFinite_not_Infinitesimal e_gt_0
    by (metis DiffD2 HInfinite_HFinite_disj Infinitesimal_ratio less_numeral_extra(3))   
      then have HNatInfinite_ze: "hypnat(hfloor(-z/e)) \<in> HNatInfinite"
        by (simp add: HInfinite_minus_iff divide_neg_pos e_gt_0 hypreal_HNatInfinite_hfloor z_less_0)
      then have hfall_div_pow_1: "(hfallfactpow (of_hypnat(hypnat(hfloor(-z/e)))) (of_nat i)) /
                (hypreal_of_hypnat(hypnat(hfloor(-z/e))) pow of_nat i) \<approx> 1"
        using HNatInfinite_hfallfactpow_divide_hyperpow_of_nat 
        by blast
      have z_pow_HFinite: "z pow of_nat i \<in> HFinite"
        by (metis DiffE hrealpow_HFinite hyperpow_of_nat z_HFinite_not_Infinitesimal) 
      have "- e * hypreal_of_hypnat (hypnat (hfloor(-z/e))) \<approx> z"
        using Infinitesimal_hfloor_divide_mult z_less_0 infinitesimal_e e_gt_0
        by (metis HNatInfinite_of_hypnat_gt_zero HNatInfinite_ze add.inverse_inverse approx_minus 
              hypint_hypnat_eq linorder_neq_iff mult_minus_left of_hypint_of_hypnat)
      then have "(-e * of_hypnat(hypnat(hfloor(-z/e)))) pow of_nat i \<approx> z pow of_nat i"
        by (meson DiffD1 approx_sym hyperpow_approx z_HFinite_not_Infinitesimal)
      then have  "(hfallfactpow (of_hypnat(hypnat(hfloor(-z/e)))) (of_nat i)) /
                (hypreal_of_hypnat(hypnat(hfloor(-z/e))) pow of_nat i) * 
             (-e * of_hypnat(hypnat(hfloor(-z/e)))) pow of_nat i \<approx> z pow of_nat i"
        by (metis HFinite_1 approx_mult_HFinite hfall_div_pow_1 mult.left_neutral z_pow_HFinite)
      thus ?thesis using HNatInfinite_ze
        by (metis (no_types, lifting) hyperpow_divide nonzero_mult_div_cancel_right 
            of_hypnat_eq_0_iff of_nat_0 of_nat_eq_star_of star_of_neq_HNatInfinite 
            times_divide_eq_left times_divide_eq_right approx_sym)
qed

lemma HFinite_not_Infinitesimal_pow_of_nat_eq_hfallfactpow2:
      assumes infinitesimal_e: "e \<in> Infinitesimal"
      and e_gt_0: "e > (0::hypreal)"
      and z_HFinite_not_Infinitesimal: "z \<in> HFinite - Infinitesimal"
      and z_gt_0: "z > 0"
      and HFinite_k: "k \<in> HFinite"
      shows "(k * z) pow of_nat i \<approx> 
             (hfallfactpow (of_hypnat(hypnat(hfloor(z/e)))) (of_nat i)) * ((k * e) pow of_nat i)"
       using hyperpow_nat_approx HFinite_k
proof -
  have "k pow of_nat i \<in> HFinite"
    by (metis (no_types) HFinite_k hrealpow_HFinite hyperpow_of_nat)
  then have "k pow of_nat i * z pow of_nat i \<approx> 
             k pow of_nat i * (hfallfactpow (hypreal_of_hypnat (hypnat (hfloor(z / e)))) (of_nat i) * e pow of_nat i)"
    by (meson hyperpow_nat_approx approx_mult_subst approx_refl e_gt_0 infinitesimal_e z_HFinite_not_Infinitesimal z_gt_0)
  then show ?thesis
    by (simp add: hyperpow_mult mult.left_commute)
qed

lemma HFinite_not_Infinitesimal_pow_of_nat_eq_hfallfactpow2_neg:
      assumes infinitesimal_e: "e \<in> Infinitesimal"
      and e_gt_0: "e > (0::hypreal)"
      and z_HFinite_not_Infinitesimal: "z \<in> HFinite - Infinitesimal"
      and z_less_0: "z < 0"
      and HFinite_k: "k \<in> HFinite"
      shows "(k * z) pow of_nat i \<approx> 
             (hfallfactpow (of_hypnat(hypnat(hfloor(-z/e)))) (of_nat i)) * ((k * -e) pow of_nat i)"
       using hyperpow_nat_approx HFinite_k
proof -
  have "k pow of_nat i \<in> HFinite"
    by (metis (no_types) HFinite_k hrealpow_HFinite hyperpow_of_nat)
  then have "k pow of_nat i * z pow of_nat i \<approx> 
             k pow of_nat i * (hfallfactpow (hypreal_of_hypnat (hypnat (hfloor(-z / e)))) (of_nat i) * (-e) pow of_nat i)"
    using HFinite_not_Infinitesimal_pow_of_nat_eq_hfallfactpow_neg approx_mult2 e_gt_0 infinitesimal_e z_HFinite_not_Infinitesimal z_less_0 by blast
  then show ?thesis
    by (metis hyperpow_mult mult.left_commute)
qed            

lemma HFinite_not_Infinitesimal_pow_of_nat_eq_hfallfactpow_divide:
      assumes infinitesimal_e: "e \<in> Infinitesimal"
      and e_gt_0: "e > (0::hypreal)"
      and z_HFinite_not_Infinitesimal: "z \<in> HFinite - Infinitesimal"
      and z_gt_0: "z > 0"
      and HFinite_k: "k \<in> HFinite"
      shows "(k * z) pow of_nat i/fact i \<approx> 
             (hfallfactpow (of_hypnat(hypnat(hfloor(z/e)))) (of_nat i))/fact i * ((k * e) pow of_nat i)"
      using HFinite_not_Infinitesimal_pow_of_nat_eq_hfallfactpow2 HFinite_k
         by (metis HInfinite_diff_HFinite_Infinitesimal_disj Reals_of_nat 
              SReal_Infinitesimal_zero approx_divide_HFinite_diff_Infinitesimal 
              approx_divide_HInfinite e_gt_0 fact_nonzero infinitesimal_e of_nat_fact 
              times_divide_eq_left z_HFinite_not_Infinitesimal z_gt_0)


lemma HFinite_not_Infinitesimal_pow_of_nat_eq_hfallfactpow_divide_neg:
      assumes infinitesimal_e: "e \<in> Infinitesimal"
      and e_gt_0: "e > (0::hypreal)"
      and z_HFinite_not_Infinitesimal: "z \<in> HFinite - Infinitesimal"
      and z_less_0: "z < 0"
      and HFinite_k: "k \<in> HFinite"
      shows "(k * z) pow of_nat i/fact i \<approx> 
             (hfallfactpow (of_hypnat(hypnat(hfloor(-z/e)))) (of_nat i))/fact i * ((k * -e) pow of_nat i)"
      using HFinite_not_Infinitesimal_pow_of_nat_eq_hfallfactpow2_neg HFinite_k
         by (metis HInfinite_diff_HFinite_Infinitesimal_disj Reals_of_nat 
              SReal_Infinitesimal_zero approx_divide_HFinite_diff_Infinitesimal 
              approx_divide_HInfinite e_gt_0 fact_nonzero infinitesimal_e of_nat_fact 
              times_divide_eq_left z_HFinite_not_Infinitesimal z_less_0)

lemma binomial_summand_HFinite_neg:
  assumes "e \<in> Infinitesimal" "e > 0"
          "z \<in> HFinite - Infinitesimal" "z < 0"
          "k \<in> HFinite" "k > 0"
          "n = of_nat m"
  shows "hypreal_of_hypnat (hypnat (hfloor(-z/e)) hchoose n) * (k * -e) pow n \<in> HFinite"
proof -
  let ?N = "hypnat (hfloor(-z/e))"
  have "hypreal_of_hypnat (?N hchoose n) * (k * -e) pow n = 
        hfallfactpow (hypreal_of_hypnat ?N) n / hfact n * (k * -e) pow n"
    by (simp add: hyperbinomial_hfallfactpow)
  also have "\<dots> \<approx> (k * z) pow n / fact m"
    using HFinite_not_Infinitesimal_pow_of_nat_eq_hfallfactpow_divide_neg assms
    by (metis approx_sym hfact_of_nat of_nat_eq_star_of of_nat_fact)
  finally have approx_standard: "hypreal_of_hypnat (?N hchoose n) * (k * -e) pow n \<approx> 
                                  (k * z) pow n / fact m" .
  have "(k * z) pow n / fact m \<in> HFinite"
  proof -
    have "k * z \<in> HFinite" using assms(3,5) by (metis DiffD1 HFinite_mult)
    then have "(k * z) pow n \<in> HFinite"
      by (metis assms(7) hrealpow_HFinite hyperpow_of_nat)
    moreover have "(fact m :: hypreal) \<noteq> 0" by simp
    moreover have "(fact m :: hypreal) \<in> HFinite"
      by (metis HFinite_of_nat of_nat_fact)
    ultimately show ?thesis
      using HFinite_divide SReal_Infinitesimal_zero fact_in_Reals by blast
  qed
  then show ?thesis using approx_standard approx_HFinite
    using approx_sym by blast
qed

text\<open>These two binomial summands are infinitely close for standard n.\<close>

lemma hchoose_approx_for_Nats:
  assumes Infinitesimal_e: "e \<in> Infinitesimal"
      and Infinitesima_e_gt0: "e > 0"
      and base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1"
      and exponentz_HFinite: "z \<in> HFinite - Infinitesimal"
      and exponentz_less_zero: "z < 0"
  shows "\<forall>n\<in>\<nat>. hypreal_of_hypnat (hypnat (hfloor(-z/e)) hchoose n) * (eulerK a e * -e) pow n \<approx>
                hypreal_of_hypnat (hypnat (hfloor(-z/e)) hchoose n) * (eulerK a (-e) * -e) pow n"
proof 
  fix n :: hypnat assume n_Nat: "n \<in> \<nat>"
  then obtain m where n_eq: "n = of_nat m"
    using Nats_cases by blast

  let ?N = "hypnat (hfloor(-z/e))"
  let ?k1 = "eulerK a e"
  let ?k2 = "eulerK a (-e)"

  have a_gt_0: "a > 0" using base_greater_1 by auto

  \<comment> \<open>Both eulerK values are HFinite and positive, trivially\<close>
  have k1_HFinite: "?k1 \<in> HFinite"
    by (simp add: Infinitesimal_e Introductio_114_eulerK_witness base_finite base_greater_1)
  have k1_gt_0: "?k1 > 0"
    by (simp add: Infinitesima_e_gt0 base_greater_1 eulerK_def hpow_gt_one)
  have k2_HFinite: "?k2 \<in> HFinite"
    by (simp add: Infinitesima_e_gt0 Infinitesimal_e base_finite base_greater_1 eulerK_neg_e_HFinite)
  have k2_gt_0: "?k2 > 0"
    by (simp add: Infinitesima_e_gt0 Infinitesimal_e base_finite base_greater_1 eulerK_neg_e_gt_zero)

  \<comment> \<open>Both sides approximate the same middle term via the falling factorial\<close>
  let ?mid1 = "(?k1 * z) pow n / fact m"
  let ?mid2 = "(?k2 * z) pow n / fact m"

  have lhs_approx: "hypreal_of_hypnat (?N hchoose n) * (?k1 * -e) pow n \<approx> ?mid1"
  proof -
    have "hypreal_of_hypnat (?N hchoose n) * (?k1 * -e) pow n = 
          hfallfactpow (hypreal_of_hypnat ?N) n / hfact n * (?k1 * -e) pow n"
      by (simp add: hyperbinomial_hfallfactpow)
    also have "\<dots> \<approx> ?mid1"
      by (metis HFinite_not_Infinitesimal_pow_of_nat_eq_hfallfactpow_divide_neg Infinitesima_e_gt0 
          Infinitesimal_e approx_reorient exponentz_HFinite exponentz_less_zero hfact_of_nat 
          k1_HFinite n_eq of_nat_eq_star_of of_nat_fact)
     finally show ?thesis .
  qed

  have rhs_approx: "hypreal_of_hypnat (?N hchoose n) * (?k2 * -e) pow n \<approx> ?mid2"
  proof -
    have "hypreal_of_hypnat (?N hchoose n) * (?k2 * -e) pow n = 
          hfallfactpow (hypreal_of_hypnat ?N) n / hfact n * (?k2 * -e) pow n"
      by (simp add: hyperbinomial_hfallfactpow)
    also have "\<dots> \<approx> ?mid2"
      by (metis HFinite_not_Infinitesimal_pow_of_nat_eq_hfallfactpow_divide_neg Infinitesima_e_gt0 
          Infinitesimal_e approx_reorient exponentz_HFinite exponentz_less_zero hfact_of_nat 
          k2_HFinite n_eq  of_nat_eq_star_of of_nat_fact)
    finally show ?thesis .
  qed

  \<comment> \<open>The two middle terms are infinitely close because for infinitesimal e, 
      eulerK a e is infinitely close to eulerK a (-e)\<close>
  have k1_approx_k2: "?k1 \<approx> ?k2"
    using Infinitesimal_e approx_sym base_finite base_greater_1 eulerK_neg_approx 
    by auto

  have k1z_approx_k2z: "?k1 * z \<approx> ?k2 * z"
  proof -
    have "z \<in> HFinite" using exponentz_HFinite 
      by blast
    then show ?thesis using k1_approx_k2 approx_mult1 
      by blast
  qed

  have k1z_HFinite: "?k1 * z \<in> HFinite"
    using k1_HFinite exponentz_HFinite 
    by (metis DiffD1 HFinite_mult)

  have mid_approx: "?mid1 \<approx> ?mid2"
  proof -
    have "(?k1 * z) pow n \<approx> (?k2 * z) pow n"
      using k1z_approx_k2z k1z_HFinite n_eq 
      by (metis approx_HFinite hrealpow_approx hyperpow_of_nat)
    then show ?thesis
      by (metis approx_divide_HFinite_diff_Infinitesimal fact_nonzero 
          hypreal_of_real_HFinite_diff_Infinitesimal of_nat_fact star_of_of_nat)
  qed

  \<comment> \<open>Conclude by transitivity of infinitely close relation\<close>
  show "hypreal_of_hypnat (?N hchoose n) * (?k1 * -e) pow n \<approx>
        hypreal_of_hypnat (?N hchoose n) * (?k2 * -e) pow n"
    using approx_trans2 lhs_approx mid_approx rhs_approx 
    by blast
qed

lemma hypersetsetsum_neg_approx:
  assumes infinitesimal_e: "e \<in> Infinitesimal"
      and infinitesimal_e_gt_zero: "e > 0"
      and base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1" 
      and exponentz_HFinite: "z \<in> HFinite - Infinitesimal"
      and exponentz_less_zero: "z < 0"
      shows "hypersum
              (\<lambda>i. of_hypnat (hypnat (hfloor (- z/e)) hchoose i) *
                   (eulerK a e * -e) pow i)
              {0..hypnat (hfloor (- z/e))} \<approx>
              hypersum
              (\<lambda>i. of_hypnat (hypnat (hfloor (- z/e)) hchoose i) *
                   (eulerK a (-e) * -e) pow i)
              {0..hypnat (hfloor (- z/e))}"
proof (rule Hypersum_Comparison_Theorem')
  show "(\<lambda>i. hypreal_of_hypnat (hypnat (hfloor (- z / e)) hchoose i) * (eulerK a e * - e) pow i)
        \<in> InternalFuns"
    using InternalFuns_hyperpow_simple InternalFuns_mult InternalFuns_of_hypnat InternalFuns_star_choose 
    by blast
next
  show "(\<lambda>i. hypreal_of_hypnat (hypnat (hfloor (- z / e)) hchoose i) * (eulerK a (- e) * - e) pow i)
        \<in> InternalFuns"
    using InternalFuns_hyperpow_simple InternalFuns_mult InternalFuns_of_hypnat InternalFuns_star_choose by blast
next
  show "HyperSummable
        (\<lambda>i. hypreal_of_hypnat (hypnat (hfloor (- z / e)) hchoose i) * (eulerK a e * - e) pow i)"
    using HyperSummable_binomial_neg_hchoose assms  
    by blast
next 
  show "HyperSummable
        (\<lambda>i. hypreal_of_hypnat (hypnat (hfloor (- z / e)) hchoose i) * (eulerK a (- e) * - e) pow i)"
    using HyperSummable_binomial_neg_hchoose' assms 
    by blast
next 
  show "\<forall>n\<in>\<nat>. hypreal_of_hypnat (hypnat (hfloor (- z / e)) hchoose n) * (eulerK a e * - e) pow n \<approx>
               hypreal_of_hypnat (hypnat (hfloor (- z / e)) hchoose n) * (eulerK a (- e) * - e) pow n"
    using hchoose_approx_for_Nats assms  
    by blast
qed

lemma hpow_hypersum_neg_hchoose':
  assumes "e \<in> Infinitesimal"
      and infinitesimal_e_gt_zero: "e > 0"
      and base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1" 
      and exponentz_HFinite: "z \<in> HFinite - Infinitesimal"
      and exponentz_less_zero: "z < 0"
      shows "a hpow z \<approx>
              hypersum (\<lambda>i. of_hypnat (hypnat (hfloor (- z/e)) hchoose i) * (eulerK a e * -e) pow i)
              {0..hypnat (hfloor (- z/e))}"
proof - 
  have "hypersum
     (\<lambda>i. hypreal_of_hypnat (hypnat (hfloor (- z / e)) hchoose i) *
           (eulerK a (- e) * - e) pow i) {0..hypnat (hfloor (- z / e))} \<approx>
          hypersum (\<lambda>i. hypreal_of_hypnat (hypnat (hfloor (- z / e)) hchoose i) *
           (eulerK a e * - e) pow i) {0..hypnat (hfloor (- z / e))}"
    using approx_sym assms hypersetsetsum_neg_approx 
    by blast
  then show ?thesis
    using hpow_hypersum_neg_hchoose [where e=e] assms
    by (meson DiffE approx_trans)
qed

text\<open>Euler's series in Paragraph 115, with finite, non-infinitesimal z > 0:\<close>
lemma hpow_approx_series_pos:
      assumes infinitesimal_e: "e \<in> Infinitesimal"
      and e_gt_zero: "e > 0"
      and base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1" 
      and exponentz_HFinite: "z \<in> HFinite - Infinitesimal"
      and exponentz_gt_zero: "z > 0"
    defines "N \<equiv> hypnat(hfloor(z/e))"
      shows "a hpow z \<approx> hypersum (\<lambda>i. (eulerK a e * z) pow i/ hfact i) {0..N}"   
proof -
     have internalf_rhs_terms: "(\<lambda>i. (eulerK a e * z) pow i / hfact i) \<in> InternalFuns"
       by (simp add: InternalFuns_divide)
     have hyperSummable_rhs: "HyperSummable (\<lambda>i. (eulerK a e * z) pow i / hfact i)"
       by (metis Diff_iff HFinite_mult HyperSummable_exp 
           Introductio_114_eulerK_witness base_finite base_greater_1
           exponentz_HFinite infinitesimal_e)
     have "(\<lambda>i. hypreal_of_hypnat (N hchoose i) * (eulerK a e * e) pow i) \<in> InternalFuns"
       using InternalFuns_hyperpow_simple InternalFuns_mult InternalFuns_of_hypnat InternalFuns_star_choose 
       by blast
     then have internalf_lhs_terms: "(\<lambda>i. hfallfactpow (hypreal_of_hypnat N) i / 
                                          hfact i * (eulerK a e * e) pow i) \<in> InternalFuns"
        by (simp add: hyperbinomial_hfallfactpow [symmetric])
 
    {
      fix n :: "nat star" assume "n \<in> Nats" 
      then obtain K where "n = hypnat_of_nat K"
        using Nats_hypnat_of_nat_iff by blast
      moreover have "hfallfactpow (hypreal_of_hypnat N) (hypnat_of_nat K) *
                     (eulerK a e * e) pow hypnat_of_nat K \<approx>
                     (eulerK a e * z) pow hypnat_of_nat K"
        by (metis HFinite_not_Infinitesimal_pow_of_nat_eq_hfallfactpow2 Introductio_114_eulerK_witness 
            N_def approx_reorient base_finite base_greater_1 e_gt_zero exponentz_HFinite 
            exponentz_gt_zero infinitesimal_e of_nat_eq_star_of)
      ultimately have "hfallfactpow (hypreal_of_hypnat (hypnat (hfloor(z/e)))) n / hfact n * 
                       (eulerK a e * e) pow n \<approx>
                       (eulerK a e * z) pow n / hfact n"
        by (metis N_def Reals_of_nat SReal_HFinite_diff_Infinitesimal approx_divide_HFinite_diff_Infinitesimal 
            hfact_nonzero hfact_of_nat times_divide_eq_left)
     }
     then have approx_lhs_rhs: 
               "\<forall>n\<in>\<nat>. hfallfactpow (hypreal_of_hypnat N) n /
                       hfact n * (eulerK a e * e) pow n \<approx>
                       (eulerK a e * z) pow n / hfact n" 
        unfolding N_def by blast
     have "HyperSummable
             (\<lambda>i. hfallfactpow (hypreal_of_hypnat N) i / 
                  hfact i * (eulerK a e * e) pow i)"
       using HyperSummable_exp_terms Introductio_114_eulerK_witness N_def
       by (metis (no_types, lifting) ext base_finite base_greater_1 diff_gt_0_iff_gt divide_pos_pos 
           e_gt_zero eulerK_def exponentz_HFinite exponentz_gt_zero hpow_gt_one infinitesimal_e)

     then have "hypersum (\<lambda>i. hfallfactpow (of_hypnat N) i / hfact i * (eulerK a e * e) pow i) {0..N} \<approx>
                hypersum (\<lambda>i. (eulerK a e * z) pow i / hfact i) {0..N}"
         using Hypersum_Comparison_Theorem' approx_lhs_rhs hyperSummable_rhs internalf_lhs_terms 
               internalf_rhs_terms by blast
       then show ?thesis using approx_trans assms
         using hpow_hypersum_pos_hffp[of e a z] by blast
qed

lemma hpow_approx_series_pos_epsilon:
  assumes base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1" 
      and exponentz_HFinite: "z \<in> HFinite - Infinitesimal"
      and exponentz_gt_zero: "z > 0"
      shows "a hpow z \<approx> 
             hypersum (\<lambda>i. (eulerK a \<epsilon> * z) pow i/ hfact i) {0..hypnat(hfloor(z/\<epsilon>))}"
  using Infinitesimal_epsilon base_finite base_greater_1 epsilon_gt_zero exponentz_HFinite 
        exponentz_gt_zero hpow_approx_series_pos 
  by blast 

text\<open>Euler's series in Paragraph 115, with finite, non-infinitesimal z < 0:\<close>
lemma hpow_approx_series_neg:
      assumes infinitesimal_e: "e \<in> Infinitesimal"
      and e_gt_zero: "e > 0"
      and base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1" 
      and exponentz_HFinite: "z \<in> HFinite - Infinitesimal"
      and exponentz_less_zero: "z < 0"
      shows "a hpow z \<approx> 
             hypersum (\<lambda>i. (eulerK a e * z) pow i/ hfact i) {0..hypnat(hfloor(-z/e))}"   
proof -
     have internalf_rhs_terms: "(\<lambda>i. (eulerK a e * z) pow i / hfact i) \<in> InternalFuns"
       by (simp add: InternalFuns_divide) 
     have hyperSummable_rhs: "HyperSummable (\<lambda>i. (eulerK a e * z) pow i / hfact i)"
       by (metis (lifting) ext Diff_iff HFinite_mult HyperSummable_exp Introductio_114_eulerK_witness base_finite
           base_greater_1 exponentz_HFinite infinitesimal_e)
     have "(\<lambda>i. hypreal_of_hypnat (hypnat  (hfloor(-z/e)) hchoose i) * (eulerK a e * -e) pow i) \<in> InternalFuns"
       using InternalFuns_hyperpow_simple InternalFuns_mult InternalFuns_of_hypnat InternalFuns_star_choose 
       by blast
     then have internalf_lhs_terms: 
          "(\<lambda>i. hfallfactpow (hypreal_of_hypnat (hypnat (hfloor(-z/e)))) i / hfact i * 
                (eulerK a e * -e) pow i) \<in> InternalFuns"
       by (simp add: InternalFuns_divide InternalFuns_mult)
     {
       fix n :: "nat star" assume "n \<in> Nats" 
       then obtain N where n: "n = hypnat_of_nat N"
         using Nats_hypnat_of_nat_iff by blast
       moreover have "hfallfactpow (hypreal_of_hypnat (hypnat (hfloor (- (z / e))))) (hypnat_of_nat N) *
                 (- (eulerK a e * e)) pow hypnat_of_nat N \<approx>
                 (eulerK a e * z) pow hypnat_of_nat N"
         by (metis (no_types, lifting) HFinite_not_Infinitesimal_pow_of_nat_eq_hfallfactpow2_neg 
             Introductio_114_eulerK_witness approx_reorient base_finite base_greater_1 e_gt_zero 
             exponentz_HFinite exponentz_less_zero infinitesimal_e minus_divide_left mult_minus_right
             of_nat_eq_star_of)
       ultimately have "hfallfactpow (hypreal_of_hypnat (hypnat (hfloor(-z/e)))) n / hfact n * 
                       (eulerK a e * -e) pow n \<approx>
                       (eulerK a e * z) pow n / hfact n"
        by (metis HFinite_not_Infinitesimal_pow_of_nat_eq_hfallfactpow_divide_neg Introductio_114_eulerK_witness 
            approx_sym base_finite base_greater_1 e_gt_zero exponentz_HFinite exponentz_less_zero hfact_of_nat 
            infinitesimal_e of_nat_eq_star_of of_nat_fact)
      }
      then have approx_lhs_rhs: 
               "\<forall>n\<in>\<nat>. hfallfactpow (hypreal_of_hypnat (hypnat (hfloor(-z/e)))) n / hfact n * 
                       (eulerK a e * -e) pow n \<approx>
                       (eulerK a e * z) pow n / hfact n" 
        by blast
      have "- z \<in> HFinite - Infinitesimal" "-z > 0"
        using HFinite_minus_iff  Diff_iff Infinitesimal_minus_iff exponentz_HFinite exponentz_less_zero 
        by auto 
      then have hs: "HyperSummable
             (\<lambda>i. hfallfactpow (hypreal_of_hypnat (hypnat (hfloor(-z/e)))) i / hfact i  * (eulerK a e * -e) pow i)"
       using HyperSummable_exp_terms2 [where z=z and e=e and k="eulerK a e"]
              Introductio_114_eulerK_witness base_finite base_greater_1 e_gt_zero eulerK_def 
             exponentz_HFinite hpow_gt_one infinitesimal_e 
        by auto
      then have x: "hypersum (\<lambda>i. hfallfactpow (of_hypnat(hypnat(hfloor(-z/e)))) i / hfact i *
                                 (eulerK a e * -e) pow i) {0..hypnat(hfloor(-z/e))} \<approx>
                   hypersum (\<lambda>i. (eulerK a e * z) pow i / hfact i) {0..hypnat(hfloor(-z/e))}"
        using Hypersum_Comparison_Theorem' approx_lhs_rhs hyperSummable_rhs internalf_lhs_terms 
               internalf_rhs_terms 
        by blast
      then show ?thesis
        using assms approx_trans [OF hpow_hypersum_neg_hchoose'] hyperbinomial_hfallfactpow
        by (metis (no_types, lifting) ext) 
qed

text\<open>Euler's series in Paragraph 115, with infinitesimal z:\<close>
lemma hpow_approx_series_infinitesimal':
    assumes infinitesimal_e: "e \<in> Infinitesimal"
      and base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1" 
      and exponentz_Infinitesimal: "z \<approx> 0"
      shows "a hpow z \<approx> 
             hypersum (\<lambda>i. (eulerK a e * z) pow i/ hfact i) {0..< hSuc n}" 
proof -
  have hsum_approx_0: "hypersum (\<lambda>i. (eulerK a e * z) pow hSuc i / hfact (hSuc i)) {0..< n} \<approx> 0"
  proof -
    have internalf_shift_exp: 
          "(\<lambda>i. (eulerK a e * z) pow hSuc i / hfact (hSuc i)) \<in> InternalFuns"
      by (simp add: InternalFuns_divide InternalFuns_of_hypnat)
    have " HyperSummable (\<lambda>i. (eulerK a e * z) pow i / hfact i)"
      by (metis HFinite_0 HFinite_mult HyperSummable_exp Introductio_114_eulerK_witness 
          approx_HFinite approx_sym base_finite base_greater_1 exponentz_Infinitesimal infinitesimal_e)
    then have hypersummable_shift_exp: "HyperSummable (\<lambda>i. (eulerK a e * z) pow hSuc i / hfact (hSuc i))"
      using HyperSummable_shift_hSuc InternalFuns_expf_term 
      by blast
    {
      fix n :: "nat star" 
      assume nat_n: "n \<in> \<nat>" 
      then have Infinitesimal_exponentz_pow: "(eulerK a e * z) pow hSuc n \<in> Infinitesimal"
        by (metis Infinitesimal_HFinite_mult Infinitesimal_hyperpow Introductio_114_eulerK_witness 
            base_finite base_greater_1 exponentz_Infinitesimal infinitesimal_e mem_infmal_iff 
            mult.commute zero_less_hSuc)
        have hfinite_hfact_suc_n: "hypreal_of_hypnat (hfact (hSuc n)) \<in> HFinite"
          by (simp add: hfact_nat_in_Nats Nats_hypreal_of_hypnat_HFinite nat_n hSuc_eq_add_one)
        have "hypreal_of_hypnat (hfact (hSuc n)) \<notin> Infinitesimal"
          by (metis Infinitesimal_interval2 Infinitesimal_zero hfact_gt_zero hypnat_gt_zero_iff 
                    of_hypnat_1 of_hypnat_le_iff one_not_Infinitesimal zero_le_one)
        then have "(eulerK a e * z) pow hSuc n / hypreal_of_hypnat (hfact (hSuc n)) \<in> Infinitesimal"
          using hfinite_hfact_suc_n Infinitesimal_exponentz_pow Infinitesimal_divide_HFinite by blast
    } 
    then have "\<forall>n\<in>\<nat>. (eulerK a e * z) pow hSuc n / hfact (hSuc n) \<approx> 0"
       using Infinitesimal_approx
       by (simp add: mem_infmal_iff of_hypnat_hfact)     
     thus ?thesis 
       using Hypersum_Comparison_Theorem [where g="\<lambda>n. 0", simplified]
              HyperSummable_def2 hypersummable_shift_exp internalf_shift_exp 
       by fastforce
  qed
  have "hypersum (\<lambda>i. (eulerK a e * z) pow i / hfact i) {0..<hSuc n} =
           (eulerK a e * z) pow 0 / hfact 0 + 
              hypersum (\<lambda>i. (eulerK a e * z) pow i / hfact i) {hSuc 0..<hSuc n}"
    using InternalFuns_divide InternalFuns_hfact InternalFuns_hyperpow_simple hypersum_head_upt_hSuc 
    by blast
  moreover have hsum: "\<dots> = 1 + hypersum (\<lambda>i. (eulerK a e * z) pow hSuc i / hfact (hSuc i)) {0..<n}"
     by (subst hypersum_shift_bounds_hSuc_ivl, auto intro: InternalFuns_expf_term')
  then have hsum_approx_1: 
       "hypersum (\<lambda>i. (eulerK a e * z) pow i / hfact i) {0..<hSuc n} \<approx> 1"
    using approx_minus_iff calculation hsum_approx_0 
    by fastforce
  have "a hpow z \<approx> 1"
     using Infinitesimal_hpow_approx_one base_finite base_greater_1 exponentz_Infinitesimal 
              lemma_approx_gt_zero by (simp add: mem_infmal_iff) 
  then have "a hpow z \<approx> hypersum (\<lambda>i. (eulerK a e * z) pow i / hfact i) {0..<hSuc n}"
    using hsum_approx_1 approx_trans2 
    by blast 
  thus ?thesis
    by blast
qed

lemma hpow_approx_series_infinitesimal:
  assumes "e \<in> Infinitesimal"
      and base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1" 
      and exponentz_Infinitesimal: "z \<approx> 0"
      shows "a hpow z \<approx> 
             hypersum (\<lambda>i. (eulerK a e * z) pow i / hfact i) {0..n}"
  using assms(1) atLeastLessThanhSuc_atLeastAtMost base_finite base_greater_1 exponentz_Infinitesimal
    hpow_approx_series_infinitesimal' 
  by presburger

lemma hpow_approx_series_infinitesimal_epsilon:
      assumes base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1" 
      and exponentz_Infinitesimal: "z \<approx> 0"
      shows "a hpow z \<approx> 
             hypersum (\<lambda>i. (eulerK a \<epsilon> * z) pow i / hfact i) {0..n}"
  using Infinitesimal_epsilon atLeastLessThanhSuc_atLeastAtMost base_finite base_greater_1 
        exponentz_Infinitesimal hpow_approx_series_infinitesimal 
  by presburger

text\<open>Euler's power series in Paragraph 115:\<close>
lemma hpow_approx_powseries:
      assumes infinitesimal_e: "e \<in> Infinitesimal"
      and e_gt_zero: "e > 0"
      and base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1" 
      and exponentz_HFinite: "z \<in> HFinite"      
      shows "a hpow z \<approx> 
             hypersum (\<lambda>i. (eulerK a e * z) pow i / hfact i) {0..hypnat(hfloor(\<bar>z\<bar>/e))}"    
proof (cases "z \<approx> 0")
  assume "z \<approx> 0" 
  then show ?thesis
    using base_finite base_greater_1 hpow_approx_series_infinitesimal infinitesimal_e 
    by blast
next 
   assume exponentz_not_approx_0: "\<not> (z \<approx> 0)"
    then have exponentz_not_zero: "z \<noteq> 0" by blast 
    have z_not_Infinitesimal: "z \<notin> Infinitesimal" 
      by (simp add: mem_infmal_iff exponentz_not_approx_0) 
    then show ?thesis 
    proof (cases "z > 0")
      assume "z > 0" then show ?thesis
        by (simp add: base_finite base_greater_1 e_gt_zero exponentz_HFinite 
                      hpow_approx_series_pos infinitesimal_e
                      z_not_Infinitesimal)
    next    
      assume "\<not> (z > 0)" then have "z < 0"
        using exponentz_not_zero 
        by auto
      then show ?thesis
        using assms hpow_approx_series_neg
        by (simp add: z_not_Infinitesimal)  
    qed
qed

subsection\<open>Euler's Introductio, Paragraph 116: exponential function.\<close>

text\<open>First version of main theorem, with Euler's k explicit:\<close>
lemma Euler_hpow_approx_powseries':
  assumes base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1" 
      and exponentz_HFinite: "z \<in> HFinite"    
      and index_infinite: "n \<in> HNatInfinite"  
      shows "a hpow z \<approx> 
             hypersum (\<lambda>i. (eulerK a (1 / of_hypnat n) * z) pow i / hfact i) {0..n}" 
proof - 
    have inv_n_gt_zero: "1/hypreal_of_hypnat n > 0" (is "?epsilon > 0")
      using index_infinite HNatInfinite_of_hypnat_gt_zero zero_less_divide_1_iff 
      by blast
    have infinitesimal_inv_n: "1/hypreal_of_hypnat n \<in> Infinitesimal" 
      using index_infinite 
      by (metis HNatInfinite_inverse_Infinitesimal inverse_eq_divide)

     show ?thesis
     proof (cases "z \<approx> 0")
       assume "z \<approx> 0" then show ?thesis
         by (metis (full_types) HNatInfinite_inverse_Infinitesimal base_finite base_greater_1 
             hpow_approx_series_infinitesimal index_infinite inverse_eq_divide)
     next 
       assume exponentz_not_approx_0: "\<not> (z \<approx> 0)" 
       have index2_infinite: "hypnat (hfloor (\<bar>z\<bar> / ?epsilon)) \<in> HNatInfinite" 
         using  hypreal_HNatInfinite_hfloor
         by (metis HInfinite_HFinite_disj Infinitesimal_approx Infinitesimal_hrabs_iff 
                   Infinitesimal_ratio Infinitesimal_zero divide_less_eq_1 divide_less_eq_1_pos 
                   divide_pos_pos exponentz_not_approx_0 infinitesimal_inv_n inv_n_gt_zero 
                    not_one_less_zero zero_less_abs_iff) 
       then have x: "a hpow z \<approx>
               hypersum (\<lambda>i. (eulerK a (1 / hypreal_of_hypnat n) * z) pow i / hfact i) 
                {0..hypnat(hfloor(\<bar>z\<bar>/?epsilon))}"
         using assms(1-3) hpow_approx_powseries infinitesimal_inv_n inv_n_gt_zero 
         by blast    
       moreover have "hypersum (\<lambda>i. (eulerK a (1 / hypreal_of_hypnat n) * z) pow i / hfact i) 
                      {0..hypnat(hfloor(\<bar>z\<bar>/?epsilon))} \<approx> 
                      hypersum (\<lambda>i. (eulerK a (1 / hypreal_of_hypnat n) * z) pow i/ hfact i) {0..n}"
         by (metis (lifting) ext HFinite_mult HyperSummable_exp HyperSummable_hypersum_approx 
             Introductio_114_eulerK_witness assms(1-3)  index2_infinite index_infinite infinitesimal_inv_n)
       ultimately have "a hpow z \<approx> hypersum (\<lambda>i. (eulerK a (1 / hypreal_of_hypnat n) * z) pow i/ hfact i) {0..n}"
       using approx_trans
       by blast 
    then show ?thesis .
  qed
qed

text\<open>We can remove the dependency between the infinite sum and the scaling factor as the 
     hypersequence is hypersummable (hyper Cauchy) and so infinitely close for any infinite 
     m and n, giving us Euler's result for power series.\<close>

lemma Euler_hpow_approx_powseries:
  assumes base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1" 
      and exponentz_HFinite: "z \<in> HFinite"    
      and pow_infinite: "n \<in> HNatInfinite" 
      and index_infinite: "m \<in> HNatInfinite" 
      shows "a hpow z \<approx> 
             hypersum (\<lambda>i. (eulerK a (1 / of_hypnat n) * z) pow i / hfact i) {0..m}" 
proof - 
  have "HyperSummable (\<lambda>i. (eulerK a (1 / hypreal_of_hypnat n) * z) pow i / hfact i)"
    by (metis (no_types, lifting) ext HFinite_mult HNatInfinite_inverse_Infinitesimal HyperSummable_exp
        Introductio_114_eulerK_witness base_finite base_greater_1 divide_inverse exponentz_HFinite 
        lambda_one pow_infinite)
  then have "hypersum (\<lambda>i. (eulerK a (1 / hypreal_of_hypnat n) * z) pow i / hfact i) {0..m} \<approx>
             hypersum (\<lambda>i. (eulerK a (1 / hypreal_of_hypnat n) * z) pow i / hfact i) {0..n}"
    using HyperSummable_hypersum_approx index_infinite pow_infinite by blast
  then show ?thesis
    using approx_trans2 base_finite base_greater_1 exponentz_HFinite Euler_hpow_approx_powseries' pow_infinite
    by blast 
qed

lemma epsilon_inverse_hSuc_whn:
  "\<epsilon> = 1/hypreal_of_hypnat(hSuc whn)"
  by (simp add: epsilon_inverse_omega hSuc_eq_add_one inverse_eq_divide whn_eq_\<omega>m1)

text\<open>We derive another simpler version of Euler's result by fixing our positive infinitesimal.\<close>
lemma Euler_hpow_approx_powseries_epsilon:
  assumes base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1" 
      and exponentz_HFinite: "z \<in> HFinite"    
      shows "a hpow z \<approx> 
             hypersum (\<lambda>i. (eulerK a \<epsilon> * z) pow i/ hfact i) {0..whn}"
  unfolding epsilon_inverse_hSuc_whn
  using assms Euler_hpow_approx_powseries
         HNatInfinite_add HNatInfinite_whn hSuc_eq_add_one 
  by presburger 

text\<open>Theorem as stated by McKinzie and Tucker, 2001:\<close>
lemma Euler_hpow_approx_powseries_MT:
  assumes base_finite: "a \<in> HFinite"
      and base_greater_1: "a > 1" 
    shows "\<exists>k\<in>HFinite. 
              \<forall>z\<in>HFinite.
                \<forall>n\<in>HNatInfinite. 
                    a hpow z \<approx> hypersum (\<lambda>i. (k * z) pow i/ hfact i) {0..n}" 
proof (rule bexI [where x="eulerK a (1 / hypreal_of_hypnat whn)"], safe)
  fix z :: "real star" and n :: "nat star"
  assume "z \<in> HFinite" "n \<in> HNatInfinite"
  then show "a hpow z \<approx>
               hypersum
                (\<lambda>i. (eulerK a (1 / hypreal_of_hypnat whn) * z) pow i / hfact i) {0..n}"
    using HNatInfinite_whn base_finite base_greater_1 Euler_hpow_approx_powseries 
    by blast
next
  show "eulerK a (1 / hypreal_of_hypnat whn) \<in> HFinite"
    by (metis HNatInfinite_inverse_Infinitesimal HNatInfinite_whn Introductio_114_eulerK_witness base_finite
        base_greater_1 inverse_eq_divide)
qed

lemma binomial_term_le_inv_fact:
  assumes "k \<le> N" and "(0::hypreal) < of_hypnat N"
  shows "hypreal_of_hypnat (N hchoose k) * (1 / of_hypnat N) pow k
         \<le> 1 / hfact k"
proof -
  (* Rewrite binomial coefficient via falling factorial *)
  have 
    "hypreal_of_hypnat (N hchoose k) * (1 / of_hypnat N) pow k =
     hfallfactpow (of_hypnat N) k / (hfact k * of_hypnat N pow k)"
  proof -
    have "hypreal_of_hypnat (N hchoose k) =
          hfallfactpow (of_hypnat N) k / hfact k"
      using hyperbinomial_hfallfactpow by auto
      thus ?thesis
        by (simp add: hyperpow_divide)
  qed
  (* Apply the bound hfallfactpow N k \<le> N^k *)
  moreover have "hfallfactpow (of_hypnat N) k \<le> hypreal_of_hypnat N pow k"
    by (simp add: assms(1) hfallfactpow_le_hyperpow)
  moreover have "(0 :: hypreal) < of_hypnat N pow k"
    using assms(2) hyperpow_gt_zero by blast
  moreover have "(0 :: hypreal) < hfact k"
    using hfact_gt_zero of_hypnat_0_less_iff by blast
  ultimately show ?thesis
    by (metis (no_types, lifting) divide_le_cancel linorder_not_less mult_less_0_iff
        nonzero_divide_mult_cancel_right order_less_le)
qed

lemma geometric_half_sum_lt_two:
  "\<Sum>\<^sub>h ((pow) (1 / 2)) {0..M} < (2::hypreal)"
proof -
  have sum_eq: "\<Sum>\<^sub>h ((pow) (1 / 2)) {0..<M + 1} = ((1 / (2::hypreal)) pow (M + 1) - 1) / (1 / 2 - 1)"
     by (simp add: hypersum_geometric)
  moreover have sum_eq2: "\<Sum>\<^sub>h ((pow) (1 / (2::hypreal))) {0..M} = \<Sum>\<^sub>h ((pow) (1 / 2)) {0..<M + 1}"
    using atLeastLessThanhSuc_atLeastAtMost hSuc_eq_add_one by auto
  moreover have pow_pos: "(1/2 :: hypreal) pow (M + 1) > 0"
    by (simp add: hyperpow_gt_zero)
  moreover have denom: "(1/2 :: hypreal) - 1 = -1/2" by simp
  ultimately show ?thesis by simp
qed

lemma inv_fact_sum_le_three:
  "hypersum (\<lambda>k. 1 /  (hfact k)) {0..N} \<le> (3 ::hypreal)"
proof -
  have zero_term: "1 / hfact 0 = (1::hypreal)"
    by simp
  have term_bound: "\<forall>j. (1 :: hypreal) / hfact (j + 1) \<le> (1/2) pow j"
  proof
    fix j :: hypnat
    have hf_pos: "(0::hypreal) <  hfact (j+1)"
      using hfact_gt_zero of_hypnat_0_less_iff by blast
    moreover have "hfact (j+1) \<ge> (2::hypreal) pow j"
      by (simp add: hfact_hSuc_ge_two_pow of_hypnat_hfact)
    ultimately show "(1::hypreal) / hfact (j + 1) \<le> (1/2) pow j"
      by (simp add: frac_le hyperpow_divide hyperpow_gt_zero)
  qed
  have internal_f: "(\<lambda>a. (1::hypreal) / hfact a) \<in> InternalFuns"
      by (simp add: InternalFuns_divide InternalFuns_of_hypnat)
  have split: "(\<Sum>\<^sub>h k\<in>{0..N}. (1::hypreal) / hfact k) = 1 + (\<Sum>\<^sub>h k\<in>{0..<N}. 1 / hfact (hSuc k))"
  proof (subst hypersum_shift_bounds_hSuc_ivl [symmetric])
    show "(\<lambda>a. (1::hypreal) / hfact a) \<in> InternalFuns"
      by (rule internal_f)
  next 
    show "(\<Sum>\<^sub>h k\<in>{0..N}. (1::hypreal) / hfact k) = 1 + (\<Sum>\<^sub>h a\<in>{hSuc 0..<hSuc N}. 1 / hfact a)"
    proof(subst hypersum_head_hSuc)
      show "(\<lambda>k. (1::hypreal) / hfact k) \<in> InternalFuns" "N \<ge> 0"
        by (auto simp add: internal_f)
    next
      show "(1::hypreal) / hfact 0 + (\<Sum>\<^sub>h k\<in>{hSuc 0..N}. 1 / hfact k) =
            1 + (\<Sum>\<^sub>h a\<in>{hSuc 0..<hSuc N}. 1 / hfact a)"
        by (simp add: atLeastLessThanhSuc_atLeastAtMost)
    qed
  qed
  have tail_bound:
    "(\<Sum>\<^sub>h k\<in>{0..<N}. (1::hypreal) / hfact (k + 1)) \<le> 
      \<Sum>\<^sub>h ((pow) (1 / 2)) {0..<N}"
  proof (rule hypersum_mono)
    show "(\<lambda>k. (1::hypreal) / hfact (k + 1)) \<in> InternalFuns"
      by (simp add: InternalFuns_add InternalFuns_divide InternalFuns_of_hypnat)
  next
    show "(pow) (1 / 2) \<in> InternalFuns" "{0..<N} \<in> InternalSets"
      by auto
  next
    fix i
    assume "i \<in> {0..<N}"
    show "(1::hypreal) / hfact (i + 1) \<le> (1 / 2) pow i"
      by (rule term_bound [THEN spec])
  qed
  have geo_bound: "\<Sum>\<^sub>h ((pow) (1 / 2)) {0..<N} < (2::hypreal)"
    using geometric_half_sum_lt_two [of "N - 1"]
    by (metis atLeastLessThanhSuc_atLeastAtMost diff_numeral_special(9) divide_eq_0_iff divide_eq_eq_1
        hSuc_eq_add_one hyperpow_zero hypersum_geometric hypnat_le_add_diff_inverse2 hypnat_less_one not_less
        numeral_eq_one_iff verit_eq_simplify(10) zero_less_numeral)
  show ?thesis
    using split geo_bound hSuc_eq_add_one tail_bound by force
qed

lemma HNatInfinite_one_plus_inv_pow_HFinite:
  assumes "n \<in> HNatInfinite"
  shows "(1 + 1 / hypreal_of_hypnat n) pow n \<in> HFinite"
proof -
  have n_pos: "(0::hypreal) < of_hypnat n"
    using assms HNatInfinite_of_hypnat_gt_zero of_hypnat_0_less_iff by blast
  (* Step 1: Binomial expansion *)
  have expand:
    "(1 + 1 / hypreal_of_hypnat n) pow n =
     hypersum (\<lambda>k. of_hypnat (n hchoose k) * (1 / of_hypnat n) pow k) {0..n}"
    using hyperbinomial_simple [of "1 / of_hypnat n" n] by simp
  (* Step 2: Bound each term by 1/k! *)
  have term_le:
    "\<forall>k \<in> {0..n}. hypreal_of_hypnat (n hchoose k) * (1 / of_hypnat n) pow k
                  \<le> 1 /  (hfact k)"
    using binomial_term_le_inv_fact n_pos by auto
  (* Step 3: Sum bound via hypersum_mono *)
  have sum_le:
    "(1 + 1 / hypreal_of_hypnat n) pow n \<le>
     hypersum (\<lambda>k. 1 / hfact k) {0..n}"
  proof (unfold expand, rule hypersum_mono)
    show "(\<lambda>k. hypreal_of_hypnat (n hchoose k) * (1 / hypreal_of_hypnat n) pow k) \<in> InternalFuns"
      by  (simp add: InternalFuns_mult InternalFuns_of_hypnat InternalFuns_star_choose)
  next
    show "(\<lambda>k. 1 / hfact k) \<in> InternalFuns"
      by (simp add: InternalFuns_o2 star_divide_def)
  next
    show "{0..n} \<in> InternalSets"
      by simp
  next
    fix i
    assume "i \<in> {0..n}"
    then show "hypreal_of_hypnat (n hchoose i) * (1 / hypreal_of_hypnat n) pow i \<le> 
          1 /  hfact i"
      using term_le by blast
  qed
  (* Step 4: Hypersum \<le> 3 *)
  have sum_bound:
    "hypersum (\<lambda>k. 1 / hfact k) {0..n} \<le> (3::hypreal)"
    using inv_fact_sum_le_three by blast
  (* Step 5: Lower bound *)
  have pos: "(1 + 1 / hypreal_of_hypnat n) pow n > 0"
    by (meson add_pos_pos hyperpow_gt_zero n_pos zero_less_divide_1_iff zero_less_one)
  (* Step 6: Upper bound and then conclude HFinite *)
  have le_three: "(1 + 1 / hypreal_of_hypnat n) pow n \<le> 3"
    using sum_le sum_bound by linarith
  then show ?thesis
    using HFinite_bounded HFinite_numeral order_less_imp_le pos by blast
qed

lemma hpow_approx_powseries_exp_lemma:
  assumes exponentz_HFinite: "z \<in> HFinite"    
      and index_infinite: "m \<in> HNatInfinite"  
      and pow_infinite: "n \<in> HNatInfinite"  
    shows "((1 + 1/of_hypnat n) pow n) hpow z \<approx> 
             hypersum (\<lambda>i. z pow i/ hfact i) {0..m}" 
proof - 
  have "n \<noteq> 0"
    by (metis pow_infinite zero_not_mem_HNatInfinite)
  then have eulerK_1: "eulerK ((1 + 1/of_hypnat n) pow  n) (1/of_hypnat n) = 1"
    using hpow_hyperpow_eq [symmetric]
    by (simp add: eulerK_def  add_pos_pos hpow_mult field_simps)
  moreover have "(1 + 1 / hypreal_of_hypnat n) pow n \<in> HFinite"
    by (simp add: HNatInfinite_one_plus_inv_pow_HFinite pow_infinite)
  moreover have "1 < (1 + 1 / hypreal_of_hypnat n) pow n"
    by (metis HNatInfinite_of_hypnat_gt_zero add_pos_pos hpow_gt_one hpow_hyperpow_eq pow_infinite
        less_add_same_cancel1 zero_less_divide_iff zero_less_one)
   ultimately show ?thesis
     using assms Euler_hpow_approx_powseries
     by force  
 qed 

lemma hpow_approx_powseries_exp_lemma2:
    assumes  "z \<in> HFinite"    
      shows "((1 + 1/of_hypnat whn) pow whn) hpow z \<approx> hypersum (\<lambda>i. z pow i/ hfact i) {0..whn}"
  by (simp add: assms hpow_approx_powseries_exp_lemma)

text\<open>Setting the exponent z=1, gives us the series to evaluate the base, which in Introductio 122, 
     Euler denotes by the symbol e. We do the same below.\<close>

lemma hpow_approx_powseries_exp_lemma3:
       "(1 + (1::hypreal)/of_hypnat whn) pow whn \<approx>  hypersum (\<lambda>i. 1/ hfact i) {0..whn}"
  using hpow_approx_powseries_exp_lemma2 [where z=1,  simplified]
  by (simp add: add_pos_pos hyperpow_gt_zero)

subsection\<open>Euler's Introductio, Paragraph 122: exponential series expansion for the base @{term \<ee>}\<close>

text\<open>We can define a Euler's @{term \<ee>} as follows although to pin it down to a 
     unique real number, we should use the standard part function.
\<close>

definition euler_e (\<open>\<ee>\<close>) where  
  "\<ee> = (1 + 1/of_hypnat whn) pow whn"

text \<open>Basic properties of @{term \<ee>}.\<close>

lemma euler_e_pos [simp]: "(\<ee>::hypreal) > 0"
  by (simp add: add_pos_pos euler_e_def hyperpow_gt_zero)

text\<open>The (infinitely close) series for @{term \<ee>}\<close>
lemma Euler_e:
   "\<ee> \<approx> hypersum (\<lambda>i. (1::hypreal)/ hfact i) {0..whn}"
  by (simp add: euler_e_def hpow_approx_powseries_exp_lemma3)

text\<open>Euler's Exponential series as a hyperfinite hypersum i.e. an infinite polynomial:\<close>
lemma Euler_exp_powseries:
    assumes "z \<in> HFinite"    
      shows "\<ee> hpow z \<approx> 
             hypersum (\<lambda>i. z pow i/ hfact i) {0..whn}"
  by (simp add: assms euler_e_def hpow_approx_powseries_exp_lemma2) 

lemma euler_e_hpow_zero [simp]: "\<ee> hpow 0 = 1"
  by simp

lemma euler_e_hpow_one [simp]: "\<ee> hpow 1 = \<ee>"
  by simp

lemma hexp_gt_one: "0 < x \<Longrightarrow> 1 < \<ee> hpow x"
  by (metis add_pos_pos divide_pos_pos euler_e_def hpow_gt_one hpow_hyperpow_eq hypnat_zero_less_hypnat_omega
      less_add_same_cancel1 of_hypnat_0_less_iff zero_less_one)

lemma HFinite_euler_e [simp]:
    "(\<ee>::real star) \<in> HFinite"
  by (simp add: HNatInfinite_one_plus_inv_pow_HFinite euler_e_def)

lemma euler_e_gt_one [simp]:
    "(\<ee>::real star) > 1"
  using hexp_gt_one [of 1]
  by (simp add: euler_e_def hyperpow_gt_zero hypreal_add_zero_less_le_mono)

lemma euler_e_ne_one: "(\<ee>::hypreal) \<noteq> 1"
  using euler_e_gt_one
  by linarith

lemma "eulerK \<ee> (1 / hypreal_of_hypnat whn) = 1"
    using hpow_hyperpow_eq [symmetric] 
    by (simp add: eulerK_def euler_e_def add_pos_pos hpow_mult field_simps)

lemma euler_e_ge_two: "(\<ee>::hypreal) \<ge> 2"
proof -
  have whn_pos: "(0::hypreal) < of_hypnat whn"
    using HNatInfinite_of_hypnat_gt_zero HNatInfinite_whn by blast
  then have inv_pos: "(0::hypreal) \<le> 1 / of_hypnat whn"
    by auto
  obtain x :: hypreal where x_ge: "x \<ge> 0" and
    expand: "(1 + 1 / of_hypnat whn) pow whn = 1 + of_hypnat whn * (1 / of_hypnat whn) + x"
    using hyperbinomial_expand_first_two_terms [OF inv_pos, of whn] by auto
  have "of_hypnat whn * (1 / of_hypnat whn) = (1::hypreal)"
    using whn_pos by auto
  then have "(1 + 1 / of_hypnat whn) pow whn = 2 + x"
    using expand by auto
  then show ?thesis 
    using x_ge euler_e_def
    by (metis add.commute le_add_same_cancel2) 
qed

lemma euler_e_power_ge_two_power: "(\<ee>::hypreal) ^ n \<ge> 2 ^ n"
  by (simp add: euler_e_ge_two power_mono)

lemma euler_e_power_bound:
  assumes "a \<in> HFinite" "a \<ge> 1"
  shows "\<exists>n. (\<ee>::hypreal) ^ n \<ge> a"
proof -
  obtain m where "a \<le> of_nat m"
    using HFinite_less_Nat_Ex assms(1) Nats_cases
    by (metis order_less_imp_le)
  moreover have "\<exists>n. of_nat m \<le> (2::hypreal) ^ n"
    using self_le_ge2_pow by fastforce
  then obtain n where "of_nat m \<le> (2::hypreal) ^ n" by auto
  moreover have "(2::hypreal) ^ n \<le> \<ee> ^ n" 
    using euler_e_power_ge_two_power by auto
  ultimately show ?thesis by (metis order_trans)
qed

lemma hpow_euler_e_eulerK_approx:
  assumes "a \<in> HFinite"
      and "a > 1" 
    shows "\<ee> hpow (eulerK a (1/of_hypnat whn)) \<approx> a"
  using assms Euler_hpow_approx_powseries [where a=a and z=1 and n=whn and m=whn, simplified]
        Euler_exp_powseries HFinite_eulerK_inverse_whn approx_trans2  
  by blast

lemma euler_e_hpow_not_approx_one_pos:
  assumes "d \<in> HFinite" "d > 0" "d \<notin> Infinitesimal"
  shows "\<not> (\<ee> hpow d \<approx> 1)"
proof -
  have d_HF_not_Inf: "d \<in> HFinite - Infinitesimal"
    using assms(1,3) 
    by blast
  then have inv_d_HF: "inverse d \<in> HFinite"
    using HFinite_inverse2 
    by blast
  then obtain m where m_bound: "inverse d < of_nat m" 
    using HFinite_less_Nat_Ex Nats_cases 
    by blast
  have m_pos: "m > 0"
  proof (rule ccontr)
    assume "\<not> m > 0" then have "m = 0" by simp
    then have "inverse d < 0" 
      using m_bound 
      by simp
    then show False
      using assms(2) 
      by fastforce
  qed
  have d_lower: "d > inverse (of_nat m)"
    by (simp add: assms(2) inverse_less_imp_less m_bound)
  have "\<ee> hpow d > \<ee> hpow (inverse (of_nat m))"
    using d_lower euler_e_gt_one hpow_less_mono 
    by blast
  moreover have "\<ee> hpow (inverse (of_nat m)) \<ge> star_of 2 hpow (inverse (of_nat m))"
  proof -
    have "inverse (of_nat m) > (0::hypreal)"
      using m_pos 
      by simp
    moreover have "(star_of 2 :: hypreal) \<le> \<ee>" 
      using euler_e_ge_two 
      by simp
    moreover have "(0::hypreal) < star_of 2" 
      by simp
    ultimately show ?thesis
      by (metis hpow_less_mono_base le_less less_imp_le)
  qed
  moreover have "star_of 2 hpow (inverse (of_nat m)) = star_of (2 pow\<^sub>\<real> (inverse (real m)))"
    by transfer simp
  moreover have "2 pow\<^sub>\<real> (inverse (real m)) > 1"
    using m_pos 
    by (simp add: powreal_gt_one)
  ultimately have lower: "\<ee> hpow d > star_of (2 pow\<^sub>\<real> (inverse (real m)))" 
    by linarith
  show "\<not> (\<ee> hpow d \<approx> 1)"
  proof
    assume "\<ee> hpow d \<approx> 1"
    then have "\<ee> hpow d - 1 \<in> Infinitesimal"
      by (simp add: Infinitesimal_approx_minus)
    moreover have "\<ee> hpow d - 1 > star_of (2 pow\<^sub>\<real> (inverse (real m))) - 1"
      using lower by simp
    moreover have "star_of (2 pow\<^sub>\<real> (inverse (real m))) - 1 > 0"
      using \<open>2 pow\<^sub>\<real> (inverse (real m)) > 1\<close> 
      by simp
    ultimately have "star_of (2 pow\<^sub>\<real> (inverse (real m))) - 1 \<in> Infinitesimal"
      using Infinitesimal_interval 
      by blast
    moreover have "2 pow\<^sub>\<real> (inverse (real m)) - 1 \<noteq> 0" 
      using \<open>2 pow\<^sub>\<real> (inverse (real m)) > 1\<close> 
      by force
    then have "star_of (2 pow\<^sub>\<real> (inverse (real m)) - 1) \<notin> Infinitesimal"
      by blast
    ultimately show False 
      by simp
  qed
qed

lemma euler_e_hpow_not_approx_one_neg:
  assumes "d \<in> HFinite" "d < 0" "d \<notin> Infinitesimal"
  shows "\<not> (\<ee> hpow d \<approx> 1)"
proof -
  have "-d > 0" "-d \<notin> Infinitesimal" "-d \<in> HFinite" 
    using assms by (auto simp: HFinite_minus_iff)
  then have neg_not_approx: "\<not> (\<ee> hpow (-d) \<approx> 1)"
    by (simp add: euler_e_hpow_not_approx_one_pos)
  show "\<not> (\<ee> hpow d \<approx> 1)"
  proof
    assume "\<ee> hpow d \<approx> 1"
    have e_hpow_d_HF_not_Inf: "\<ee> hpow d \<in> HFinite - Infinitesimal"
      using HFinite_hpow_HFinite_Diff_Infinitesimal HFinite_euler_e euler_e_gt_one 
            assms(1) less_imp_le 
      by blast
    then have "inverse (\<ee> hpow d) \<approx> inverse 1"
      using \<open>\<ee> hpow d \<approx> 1\<close> approx_inverse approx_sym 
      by blast
    then have "inverse (\<ee> hpow d) \<approx> 1" 
      by simp
    moreover have "\<ee> hpow (-d) = inverse (\<ee> hpow d)"
      using euler_e_pos hpow_minus 
      by blast
    ultimately have "\<ee> hpow (-d) \<approx> 1" 
      by simp
    then show False
      by (simp add: neg_not_approx)
  qed
qed

lemma euler_e_hpow_not_approx_one:
  assumes "d \<in> HFinite" "d \<noteq> 0" "d \<notin> Infinitesimal"
  shows "\<not> (\<ee> hpow d \<approx> 1)"
  by (meson assms euler_e_hpow_not_approx_one_neg euler_e_hpow_not_approx_one_pos
      linorder_neqE_linordered_idom)

corollary euler_e_hpow_approx_one_iff_Infinitesimal:
  assumes "d \<in> HFinite"
  shows "(\<ee> hpow d \<approx> 1) \<longleftrightarrow> (d \<in> Infinitesimal)"
  using HFinite_euler_e Infinitesimal_hpow_approx_one assms euler_e_gt_one euler_e_hpow_not_approx_one
  by blast

lemma euler_e_hpow_approx_inject:
  assumes "\<ee> hpow x \<approx> \<ee> hpow y" 
      and "x \<in> HFinite"
      and "y \<in> HFinite" 
  shows "x \<approx> y"
proof -
  have "\<ee> hpow (x - y) = \<ee> hpow x / \<ee> hpow y"
    using euler_e_pos hpow_divide2 
    by blast
  moreover have "\<ee> hpow x / \<ee> hpow y \<approx> 1"
  proof -
    have ey_HF: "\<ee> hpow y \<in> HFinite - Infinitesimal"
      using HFinite_hpow_HFinite_Diff_Infinitesimal HFinite_euler_e euler_e_gt_one 
            assms(3) less_imp_le 
      by blast
    then have "\<ee> hpow x / \<ee> hpow y \<approx> \<ee> hpow y / \<ee> hpow y"
      using assms(1) approx_divide_HFinite_diff_Infinitesimal by blast
    then show ?thesis
      by (simp add: hpow_not_zero) 
  qed
  ultimately have hpow_diff: "\<ee> hpow (x - y) \<approx> 1" by simp
  then show "x \<approx> y"
    by (meson HFinite_diff assms(2,3) bex_Infinitesimal_iff euler_e_hpow_approx_one_iff_Infinitesimal)
qed

subsection\<open>Hypernatural logarithm\<close>

text\<open>Let us define the hypernatural logarithm of a hyperreal x\<close>

definition Ln where
  "Ln x \<equiv> hLog \<ee> x"

lemma Ln_euler_e [simp]: "Ln \<ee> = 1"
  by (metis Ln_def add_pos_pos divide_pos_pos euler_e_def hLog_eq_one hexp_gt_one hpow_one hyperpow_gt_zero
      hypnat_zero_less_hypnat_omega less_numeral_extra(1) of_hypnat_0_less_iff order_less_irrefl)

lemma hpow_e_Ln [simp]:
  assumes "a > 0"
    shows "\<ee> hpow (Ln a) = a"
  by (metis Ln_def add_pos_pos assms euler_e_def hexp_gt_one hpow_hLog_cancel hpow_one hyperpow_gt_zero
      hypnat_zero_less_hypnat_omega less_numeral_extra(1,4) of_hypnat_0_less_iff zero_less_divide_1_iff)

lemma Ln_ge_zero: "a \<ge> 1 \<Longrightarrow> Ln a \<ge> 0"
  using Ln_def by fastforce

lemma Ln_inverse: "x > 0 \<Longrightarrow> Ln (inverse x) = - Ln x"
  by (simp add: Ln_def euler_e_ne_one hLog_inverse)

lemma Ln_less_zero: "a > 0 \<Longrightarrow> a < 1 \<Longrightarrow> Ln a < 0"
  by (simp add: Ln_def)

lemma Ln_HFinite:
  assumes "a \<in> HFinite - Infinitesimal" "a > 0"
  shows "Ln a \<in> HFinite"
proof (cases "a \<ge> 1")
  case True
  obtain n where n_bound: "\<ee> ^ n \<ge> a"
    using euler_e_power_bound assms(1) True 
    by (metis DiffD1)
  then have "\<ee> hpow (of_nat n) \<ge> a"
    by (simp add: hpow_power_eq)
  then have "hLog \<ee> (\<ee> hpow (of_nat n)) \<ge> hLog \<ee> a"
    using assms(2) 
    by auto
  then have "of_nat n \<ge> hLog \<ee> a"
    by (simp add: euler_e_ne_one)
  then have "Ln a \<le> of_nat n" 
    by (simp add: Ln_def)
  then show ?thesis
    using HFinite_bounded HFinite_of_nat Ln_ge_zero True 
    by blast
next
  case False
  then have a_lt_1: "a < 1" 
    by simp
  then have inv_a_ge_1: "inverse a \<ge> 1"
    using assms(2) one_le_inverse_iff 
    by fastforce
  have inv_a_HFinite: "inverse a \<in> HFinite"
    using assms(1) HFinite_inverse2 
    by blast
  have inv_a_HFinite_diff: "inverse a \<in> HFinite - Infinitesimal"
    using HFinite_not_Infinitesimal_inverse assms(1) 
    by blast
  have inv_a_pos: "inverse a > 0" 
    using assms(2) by simp
  have "Ln (inverse a) \<in> HFinite"
  proof -
    have "Ln (inverse a) \<ge> 0"
      by (simp add: Ln_ge_zero inv_a_ge_1)
    moreover obtain n where "\<ee> ^ n \<ge> inverse a"
      using euler_e_power_bound inv_a_HFinite inv_a_ge_1 by blast
    then have "\<ee> hpow (of_nat n) \<ge> inverse a"
      using euler_e_pos hpow_power_eq 
      by simp
    then have "hLog \<ee> (\<ee> hpow (of_nat n)) \<ge> hLog \<ee> (inverse a)"
      using euler_e_pos hpow_gt_zero inv_a_pos 
      by simp
    then have "of_nat n \<ge> hLog \<ee> (inverse a)"
      using euler_e_pos euler_e_ne_one 
      by simp
    then have "Ln (inverse a) \<le> of_nat n" 
      by (simp add: Ln_def)
    ultimately show ?thesis
      using HFinite_bounded HFinite_of_nat 
      by blast
  qed
  moreover have "Ln a = - Ln (inverse a)"
    using euler_e_pos euler_e_ne_one assms(2)
    by (simp add: Ln_def hLog_inverse)
  ultimately show ?thesis
    by (simp add: HFinite_minus_iff)
qed


lemma Ln_eulerK_approx:
  assumes "a \<in> HFinite" "a > 1"
  shows "Ln a \<approx> eulerK a (1 / hypreal_of_hypnat whn)"
  using assms euler_e_hpow_approx_inject hpow_euler_e_eulerK_approx hpow_e_Ln Ln_HFinite
        HFinite_eulerK_inverse_whn
  by (metis Diff_iff Infinitesimal_interval Infinitesimal_zero approx_sym dual_order.strict_trans
      one_not_Infinitesimal zero_less_one) 

text\<open>This is just to show that natural logarithm would have the expected definition (if we take
     the standard part of the RHS)\<close>

lemma Ln_approx_def:
  assumes "a \<in> HFinite" "a > 1"
  shows "Ln a \<approx> (a hpow (1 / hypreal_of_hypnat whn) - 1) * of_hypnat whn"
  using Ln_eulerK_approx assms eulerK_def by auto

text\<open>Euler's power series in terms of hypernatural logarithm.\<close>
lemma hpow_powseries_Ln:
  assumes "a \<in> HFinite"
      and "a > 1" 
      and "z \<in> HFinite"    
      shows "a hpow z \<approx> (\<Sum>\<^sub>h i\<in>{0..whn}. (Ln a * z) pow i / hfact i)"
proof -
  have "(\<Sum>\<^sub>h i\<in>{0..whn}. (eulerK a (1 / hypreal_of_hypnat whn) * z) pow i / hfact i) \<approx>
        (\<Sum>\<^sub>h i\<in>{0..whn}. (Ln a * z) pow i / hfact i)"
  proof (rule Hypersum_Comparison_Theorem')
    show "(\<lambda>i. (eulerK a (1 / hypreal_of_hypnat whn) * z) pow i / hfact i) \<in> InternalFuns"
      by simp
  next
    show "(\<lambda>i. (Ln a * z) pow i / hfact i) \<in> InternalFuns"
      by simp
  next
    show "HyperSummable
            (\<lambda>i. (eulerK a (1 / hypreal_of_hypnat whn) * z) pow i / hfact i)"
      by (simp add: assms HFinite_eulerK_inverse_whn HFinite_mult HyperSummable_exp)
  next
    show "HyperSummable (\<lambda>i. (Ln a * z) pow i / hfact i)"
      using assms 
      by (metis HFinite_eulerK_inverse_whn HFinite_mult HyperSummable_exp Ln_eulerK_approx
          approx_HFinite approx_reorient)
  next 
    show "\<forall>n\<in>\<nat>. (eulerK a (1 / hypreal_of_hypnat whn) * z) pow n / hfact n \<approx>
           (Ln a * z) pow n / hfact n"
    proof 
      fix n :: hypnat
      assume Nat_n: "n \<in> \<nat>"
      then have "(z * eulerK a (1 / hypreal_of_hypnat whn)) pow n \<approx> (z * Ln a) pow n"
        by (metis assms HFinite_eulerK_inverse_whn HFinite_mult Ln_eulerK_approx Nats_hypnat_of_nat_iff approx_mult1
            approx_reorient hyperpow_approx mult.commute
            of_nat_eq_star_of)
      moreover have "(hfact n :: hypreal) \<in> HFinite - Infinitesimal"
        by (metis Nats_hypnat_of_nat_iff Reals_of_nat SReal_HFinite_diff_Infinitesimal Nat_n hfact_nonzero
            hfact_of_nat )
      ultimately 
      show "(eulerK a (1 / hypreal_of_hypnat whn) * z) pow n / hfact n \<approx>
            (Ln a * z) pow n / hfact n"
        by (simp add: approx_divide_HFinite_diff_Infinitesimal mult.commute)
    qed
  qed
  then show ?thesis 
    using Euler_hpow_approx_powseries [where n=whn and m=whn] assms HNatInfinite_whn approx_trans 
    by blast
qed

subsection\<open>Linking the Euler and Isabelle library exponential functions.\<close>

text\<open>Just for the sake of it: we link our current derivation of the exponential series 
     to the Isabelle library one.\<close>

lemma exp_NSsums: "(\<lambda>n. z ^ n / fact n) NSsums (exp z)"
proof -
  have "(\<lambda>n. z ^ n / fact n) sums (exp z)"
    using exp_converges [of z]
    by (simp add: inverse_eq_divide nonzero_divide_eq_eq)
  then show ?thesis
    by (simp add: sums_NSsums_iff)
qed

lemma hypersum_exp_approx:
  assumes "N \<in> HNatInfinite"
  shows "hypersum (*f* (\<lambda>n. z ^ n / fact n)) {0..<N} \<approx> of_real (exp z)"
  using exp_NSsums NSsums_hypersum_HNatInfinite_approx_iff assms 
  by blast

lemma starfun_exp_of_real: "(*f* exp) (of_real z) = of_real (exp z)"
  by (metis exp_of_real star_of_real_def starfun_star_of)

lemma starfun_exp_term_eq:
  "(*f* (\<lambda>n. z ^ n / fact n)) n = (of_real z) pow n / hfact n"
  by (simp add: hfact_def starfun_power)

lemma HyperSummable_starfun_real_exp:
  "HyperSummable (*f* (\<lambda>n. (z::real) ^ n / fact n))"
proof -
  have "summable (\<lambda>n. z ^ n / fact n)"
    using exp_NSsums sums_NSsums_iff sums_summable 
    by blast
  then show ?thesis
    using HyperSummable_starfun_summable_iff 
    by blast
qed

lemma hypersum_starfun_exp_approx_euler_sum:
  "hypersum (*f* (\<lambda>n. z ^ n / fact n)) {0..N} \<approx> 
   hypersum (\<lambda>i. (of_real z) pow i / hfact i) {0..N}"
  by (metis (no_types, lifting) ext approx_refl starfun_exp_term_eq)

text\<open>Theorem linking the two representations of the exponential series. \<close>

theorem euler_e_hpow_approx_starfun_exp:
  "\<ee> hpow (of_real z) \<approx> (*f* exp) (of_real z)"
proof -
  let ?z = "of_real z :: hypreal"

  have hypsum_std_exp: "hypersum (*f* (\<lambda>n. z ^ n / fact n)) {0..<hSuc whn} \<approx> of_real (exp z)"
    using hypersum_exp_approx [OF HNatInfinite_add [OF HNatInfinite_whn]] 
    by (simp add: hSuc_eq_add_one)
  moreover have sums_approx:
    "hypersum (*f* (\<lambda>n. z ^ n / fact n)) {0..<hSuc whn} \<approx>
     hypersum (\<lambda>i. ?z pow i / hfact i) {0..whn}"
    using atLeastLessThanhSuc_atLeastAtMost hypersum_starfun_exp_approx_euler_sum 
    by presburger
  ultimately have "of_real (exp z) \<approx> hypersum (\<lambda>i. ?z pow i / hfact i) {0..whn}"
    using  sums_approx approx_sym approx_trans 
    by blast
  then have "\<ee> hpow ?z \<approx> of_real (exp z)"
    by (metis Euler_exp_powseries HFinite_star_of approx_trans2 of_real_eq_star_of)
  then show ?thesis
    using starfun_exp_of_real
    by simp
qed

corollary euler_e_hpow_approx_exp:
  "\<ee> hpow (hypreal_of_real z) \<approx> hypreal_of_real (exp z)"
  using euler_e_hpow_approx_starfun_exp starfun_exp_of_real by simp

text \<open>The standard part of our Euler exponential is (the hyperreak embedding of) 
Isabelle's exponential funtion \<close>

corollary st_euler_e_hpow_eq_exp:
  "st(\<ee> hpow (hypreal_of_real z)) = hypreal_of_real (exp z)"
  by (simp add: approx_sym euler_e_hpow_approx_exp st_unique)

text \<open>We can show that the standard part of our Euler @{term \<ee>} is (literally!) the real e.\<close>

corollary euler_e_approx_exp1: "(\<ee>::hypreal) \<approx> of_real (exp 1)"
  using euler_e_hpow_approx_exp [of 1] by simp

corollary st_euler_e_approx_exp1: "st (\<ee>::hypreal) = of_real (exp 1)"
  using euler_e_approx_exp1 st_eq_approx_iff by force

subsection\<open>Derivative of Euler's exponential function.\<close>

text\<open>We can also show that our Euler exponential function is its own derivative.\<close>

lemma euler_e_hpow_eulerK_approx_base:
  assumes inf_e: "e \<in> Infinitesimal" 
      and e_pos: "e > 0"
      and a_HF: "a \<in> HFinite" 
      and a_gt1: "a > 1"
  shows "\<ee> hpow (eulerK a e) \<approx> a"
proof -
  let ?k = "eulerK a e"
  let ?N = "hypnat(hfloor(1/e))"

  have k_HF: "?k \<in> HFinite"
    using Introductio_114_eulerK_witness inf_e a_HF a_gt1
    by blast
  have N_inf: "?N \<in> HNatInfinite"
    using e_pos hypreal_HNatInfinite_hfloor_inverse_Infinitesimal inf_e 
    by blast
  have "a hpow 1 \<approx> 
        hypersum (\<lambda>i. (?k * 1) pow i / hfact i) {0..?N}"
    using hpow_approx_powseries [OF inf_e e_pos a_HF a_gt1 HFinite_1]
    by simp
  then have sum_approx_a: 
    "a \<approx> hypersum (\<lambda>i. ?k pow i / hfact i) {0..?N}"
    using a_gt1
    by simp
  have sum_approx_exp: 
    "\<ee> hpow ?k \<approx> hypersum (\<lambda>i. ?k pow i / hfact i) {0..whn}"
    using Euler_exp_powseries k_HF 
    by blast
  have summable: "HyperSummable (\<lambda>i. ?k pow i / hfact i)"
    using HyperSummable_exp k_HF 
    by blast
  then have sums_approx: 
    "hypersum (\<lambda>i. ?k pow i / hfact i) {0..?N} \<approx>
     hypersum (\<lambda>i. ?k pow i / hfact i) {0..whn}"
    using HyperSummable_hypersum_approx N_inf HNatInfinite_whn 
    by blast
  have "a \<approx> hypersum (\<lambda>i. ?k pow i / hfact i) {0..whn}"
    using sum_approx_a sums_approx approx_trans 
    by blast
  then have "a \<approx> \<ee> hpow ?k"
    using sum_approx_exp approx_trans2 
    by blast
  then show ?thesis
    using approx_sym 
    by blast
qed

lemma eulerK_approx_Ln_pos:
  assumes "e \<in> Infinitesimal" "e > 0" "a \<in> HFinite" "a > 1"
  shows "eulerK a e \<approx> Ln a"
proof -
  have k_HF: "eulerK a e \<in> HFinite"
    using Introductio_114_eulerK_witness assms 
    by blast
  have a_pos: "a > 0"
    using assms(4) by (simp add: less_trans)
  have Ln_HF: "Ln a \<in> HFinite"
    using Ln_HFinite assms(3,4)
    by (metis Diff_iff Infinitesimal_interval Infinitesimal_zero 
        dual_order.strict_trans one_not_Infinitesimal zero_less_one)
  have "\<ee> hpow (eulerK a e) \<approx> a"
    using euler_e_hpow_eulerK_approx_base assms 
    by blast
  moreover have "a = \<ee> hpow (Ln a)"
    using hpow_e_Ln a_pos 
    by simp
  ultimately have "\<ee> hpow (eulerK a e) \<approx> \<ee> hpow (Ln a)"
    by simp
  then show ?thesis
    using euler_e_hpow_approx_inject k_HF Ln_HF 
    by blast
qed

text \<open>Extend the previous lemma to deal with negative infinitesimals.\<close>

lemma eulerK_approx_Ln_neg:
  assumes "e \<in> Infinitesimal" "e < 0" "a \<in> HFinite" "a > 1"
  shows "eulerK a e \<approx> Ln a"
proof -
  have neg_e_inf: "-e \<in> Infinitesimal"
    using assms(1) Infinitesimal_minus_iff 
    by blast
  have "eulerK a (-(-e)) \<approx> eulerK a (-e)"
    using eulerK_neg_approx [OF assms(3,4) neg_e_inf] 
    by blast
  then have "eulerK a e \<approx> eulerK a (-e)"
    by simp
  moreover have "eulerK a (-e) \<approx> Ln a"
    using eulerK_approx_Ln_pos neg_e_inf assms
    by force
  ultimately show ?thesis
    using approx_trans 
    by blast
qed

text \<open>The combined result for any nonzero infinitesimal.\<close>

theorem eulerK_approx_Ln:
  assumes "e \<in> Infinitesimal" "e \<noteq> 0" "a \<in> HFinite" "a > 1"
  shows "eulerK a e \<approx> Ln a"
  using assms eulerK_approx_Ln_neg eulerK_approx_Ln_pos 
  by fastforce

lemma hpow_difference_quotient:
  assumes "a > 0" 
  shows "(a hpow (x + e) - a hpow x) / e = a hpow x * eulerK a e"
proof -
  have "a hpow (x + e) = a hpow x * a hpow e"
    using hpow_add assms(1) 
    by blast
  then have "a hpow (x + e) - a hpow x = a hpow x * (a hpow e - 1)"
    by (simp add: algebra_simps)
  then have "(a hpow (x + e) - a hpow x) / e = a hpow x * ((a hpow e - 1) / e)"
    by simp
  then show ?thesis
    by (simp add: eulerK_def)
qed

text \<open>Nonstandard derivative of the general exponential\<close>

theorem NSderivative_hpow:
  assumes a_HF: "a \<in> HFinite"
      and a_gt1: "a > 1" 
      and x_HF: "x \<in> HFinite"
      and e_inf: "e \<in> Infinitesimal"
      and e_ne0: "e \<noteq> 0"
  shows "(a hpow (x + e) - a hpow x) / e \<approx> Ln a * (a hpow x)"
proof -
  have "a > 0"
    using a_gt1 by (simp add: less_trans)
  then have factor: "(a hpow (x + e) - a hpow x) / e = a hpow x * eulerK a e"
    using hpow_difference_quotient  
    by blast
  have eulerK_Ln: "eulerK a e \<approx> Ln a"
    by (simp add: a_HF a_gt1 e_inf e_ne0 eulerK_approx_Ln)
  have hpow_HF: "a hpow x \<in> HFinite"
    using HFinite_hpow1 a_HF x_HF a_gt1 less_imp_le
    by blast
  then have "a hpow x * eulerK a e \<approx> a hpow x * Ln a"
    by (simp add: approx_mult2 eulerK_Ln)
  then show ?thesis
    by (simp add: factor mult.commute)
qed

text \<open>Euler's exponential function is its own (nonstandardly-expressed) derivative (as expected).\<close>

theorem NSderivative_euler_e:
  assumes "x \<in> HFinite" "e \<in> Infinitesimal" "e \<noteq> 0"
  shows "(\<ee> hpow (x + e) - \<ee> hpow x) / e \<approx> \<ee> hpow x"
proof -
  have "(\<ee> hpow (x + e) - \<ee> hpow x) / e \<approx> Ln \<ee> * (\<ee> hpow x)"
    using NSderivative_hpow [OF HFinite_euler_e euler_e_gt_one assms] 
    by blast
  then show ?thesis
    by simp
qed

lemma NSderivative_hpow_at_zero:
  assumes "a \<in> HFinite" "a > 1" "e \<in> Infinitesimal" "e \<noteq> 0"
  shows "(a hpow e - 1) / e \<approx> Ln a"
proof -
  have "(a hpow (0 + e) - a hpow 0) / e \<approx> Ln a * (a hpow 0)"
    using HFinite_0 NSderivative_hpow assms 
    by blast
  then show ?thesis
    using assms(2) 
    by (simp add: less_trans)
qed 

text \<open>The derivative of @{term \<ee>} hpow x at x=0 is 1.\<close>

lemma NSderivative_euler_e_at_zero:
  assumes "e \<in> Infinitesimal" "e \<noteq> 0"
  shows "(\<ee> hpow e - 1) / e \<approx> 1"
  using NSderivative_hpow_at_zero [OF HFinite_euler_e euler_e_gt_one assms]
  by simp

lemma "(\<ee> hpow \<epsilon> - 1) / \<epsilon> \<approx> 1"
  by (simp add: NSderivative_euler_e_at_zero epsilon_not_zero)

end