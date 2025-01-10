section \<open>\<open>Positive_Operators\<close> -- Positive bounded operators\<close>

theory Positive_Operators
  imports
    Ordinary_Differential_Equations.Cones
    Misc_Tensor_Product_BO
    Strong_Operator_Topology
begin

no_notation Infinite_Set_Sum.abs_summable_on (infix "abs'_summable'_on" 50)
hide_const (open) Infinite_Set_Sum.abs_summable_on
hide_fact (open) Infinite_Set_Sum.abs_summable_on_Sigma_iff

unbundle cblinfun_notation

lemma cinner_pos_if_pos: \<open>f \<bullet>\<^sub>C (A *\<^sub>V f) \<ge> 0\<close> if \<open>A \<ge> 0\<close>
  using less_eq_cblinfun_def that by force

definition sqrt_op :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close> where
  \<open>sqrt_op a = (if (\<exists>b :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a. b \<ge> 0 \<and> b* o\<^sub>C\<^sub>L b = a) then (SOME b. b \<ge> 0 \<and> b* o\<^sub>C\<^sub>L b = a) else 0)\<close>

lemma sqrt_op_nonpos: \<open>sqrt_op a = 0\<close> if \<open>\<not> a \<ge> 0\<close>
proof -
  have \<open>\<not> (\<exists>b. b \<ge> 0 \<and> b* o\<^sub>C\<^sub>L b = a)\<close>
    using positive_cblinfun_squareI that by blast
  then show ?thesis
    by (auto simp add: sqrt_op_def)
qed

lemma generalized_Cauchy_Schwarz:
  fixes inner A
  assumes Apos: \<open>A \<ge> 0\<close>
  defines "inner x y \<equiv> x \<bullet>\<^sub>C (A *\<^sub>V y)"
  shows \<open>complex_of_real ((norm (inner x y))\<^sup>2) \<le> inner x x * inner y y\<close>
proof (cases \<open>inner y y = 0\<close>)
  case True
  have [simp]: \<open>inner (s *\<^sub>C x) y = cnj s * inner x y\<close> for s x y
    by (simp add: assms(2))
  have [simp]: \<open>inner x (s *\<^sub>C y) = s * inner x y\<close> for s x y
    by (simp add: assms(2) cblinfun.scaleC_right)
  have [simp]: \<open>inner (x - x') y = inner x y - inner x' y\<close> for x x' y
    by (simp add: cinner_diff_left inner_def)
  have [simp]: \<open>inner x (y - y') = inner x y - inner x y'\<close> for x y y'
    by (simp add: cblinfun.diff_right cinner_diff_right inner_def)
  have Re0: \<open>Re (inner x y) = 0\<close> for x
  proof -
    have *: \<open>Re (inner x y) = (inner x y + inner y x) / 2\<close>
      by (smt (verit, del_insts) assms(1) assms(2) cinner_adj_left cinner_commute complex_Re_numeral complex_add_cnj field_sum_of_halves numeral_One numeral_plus_numeral of_real_divide of_real_numeral one_complex.simps(1) positive_hermitianI semiring_norm(2))
    have \<open>0 \<le> Re (inner (x - s *\<^sub>C y) (x - s *\<^sub>C y))\<close> for s
      by (metis Re_mono assms(1) assms(2) cinner_pos_if_pos zero_complex.simps(1))
    also have \<open>\<dots> s = Re (inner x x) - s * 2 * Re (inner x y)\<close> for s
      apply (auto simp: True)
      by (smt (verit, ccfv_threshold) Re_complex_of_real assms(1) assms(2) cinner_adj_right cinner_commute complex_add_cnj diff_minus_eq_add minus_complex.simps(1) positive_hermitianI uminus_complex.sel(1))
    finally show \<open>Re (inner x y) = 0\<close>
      by (metis add_le_same_cancel1 ge_iff_diff_ge_0 nonzero_eq_divide_eq not_numeral_le_zero zero_neq_numeral)
  qed
  have \<open>Im (inner x y) = Re (inner (imaginary_unit *\<^sub>C x) y)\<close>
    by simp
  also have \<open>\<dots> = 0\<close>
    by (rule Re0)
  finally have \<open>inner x y = 0\<close>
    using Re0[of x]
    using complex_eq_iff zero_complex.simps(1) zero_complex.simps(2) by presburger
  then show ?thesis
    by (auto simp: True)
next
  case False
  have inner_commute: \<open>inner x y = cnj (inner y x)\<close>
    by (metis Apos cinner_adj_left cinner_commute' inner_def positive_hermitianI)
  have [simp]: "cnj (inner y y) = inner y y" for y
    by (metis assms(1) cinner_adj_right cinner_commute' inner_def positive_hermitianI)
  define r where "r = cnj (inner x y) / inner y y"
  have "0 \<le> inner (x - scaleC r y) (x - scaleC r y)"
    by (simp add: Apos inner_def cinner_pos_if_pos)
  also have "\<dots> = inner x x - r * inner x y - cnj r * inner y x + r * cnj r * inner y y"
    unfolding cinner_diff_left cinner_diff_right cinner_scaleC_left cinner_scaleC_right inner_def
    by (smt (verit, ccfv_threshold) cblinfun.diff_right cblinfun.scaleC_right cblinfun_cinner_right.rep_eq cinner_scaleC_left cinner_scaleC_right diff_add_eq diff_diff_eq2 mult.assoc)
  also have "\<dots> = inner x x - inner y x * cnj r"
    unfolding r_def by auto
  also have "\<dots> = inner x x - inner x y * cnj (inner x y) / inner y y"
    unfolding r_def
    by (metis assms(1) assms(2) cinner_adj_right cinner_commute complex_cnj_divide mult.commute positive_hermitianI times_divide_eq_left)
  finally have "0 \<le> inner x x - inner x y * cnj (inner x y) / inner y y" .
  hence "inner x y * cnj (inner x y) / inner y y \<le> inner x x"
    by (simp add: le_diff_eq)
  hence \<open>(norm (inner x y)) ^ 2 / inner y y \<le> inner x x\<close>
    using complex_norm_square by presburger
  then show ?thesis
    by (metis False assms(1) assms(2) cinner_pos_if_pos mult_right_mono nonzero_eq_divide_eq)
qed

lemma sandwich_pos[intro]: \<open>sandwich b a \<ge> 0\<close> if \<open>a \<ge> 0\<close>
  by (metis (no_types, opaque_lifting) positive_cblinfunI cblinfun_apply_cblinfun_compose cinner_adj_left cinner_pos_if_pos sandwich_apply that)

lemma cblinfun_power_pos: \<open>cblinfun_power a n \<ge> 0\<close> if \<open>a \<ge> 0\<close>
proof (cases \<open>even n\<close>)
  case True
  have \<open>0 \<le> (cblinfun_power a (n div 2))* o\<^sub>C\<^sub>L (cblinfun_power a (n div 2))\<close>
    using positive_cblinfun_squareI by blast
  also have \<open>\<dots> = cblinfun_power a (n div 2 + n div 2)\<close>
    by (metis cblinfun_power_adj cblinfun_power_compose positive_hermitianI that)
  also from True have \<open>\<dots> = cblinfun_power a n\<close>
    by (metis add_self_div_2 div_plus_div_distrib_dvd_right) 
  finally show ?thesis
    by -
next
  case False
  have \<open>0 \<le> sandwich (cblinfun_power a (n div 2)) a\<close>
    using \<open>a \<ge> 0\<close> by (rule sandwich_pos)
  also have \<open>\<dots> = cblinfun_power a (n div 2 + 1 + n div 2)\<close>
    unfolding sandwich_apply
    by (metis (no_types, lifting) One_nat_def cblinfun_compose_id_right cblinfun_power_0 cblinfun_power_Suc' cblinfun_power_adj cblinfun_power_compose positive_hermitianI that)
  also from False have \<open>\<dots> = cblinfun_power a n\<close>
    by (smt (verit, del_insts) Suc_1 add.commute add.left_commute add_mult_distrib2 add_self_div_2 nat.simps(3) nonzero_mult_div_cancel_left odd_two_times_div_two_succ)
  finally show ?thesis
    by -
qed



(* Proof follows https://link.springer.com/article/10.1007%2FBF01448052,
      @{cite wecken35linearer} *)
lemma sqrt_op_existence:
  fixes A :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space\<close>
  assumes Apos: \<open>A \<ge> 0\<close>
  shows \<open>\<exists>B. B \<ge> 0 \<and> B o\<^sub>C\<^sub>L B = A \<and> (\<forall>F. A o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L A \<longrightarrow> B o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L B)
          \<and> B \<in> closure (cspan (range (cblinfun_power A)))\<close>
proof -
  define k S where \<open>k = norm A\<close> and \<open>S = A /\<^sub>R k - id_cblinfun\<close>
  have \<open>S \<le> 0\<close>
  proof (rule cblinfun_leI)
    fix x :: 'a assume [simp]: \<open>norm x = 1\<close>
    with assms have aux1: \<open>complex_of_real (inverse (norm A)) * (x \<bullet>\<^sub>C (A *\<^sub>V x)) \<le> 1\<close>
      by (smt (verit, del_insts) Reals_cnj_iff cinner_adj_left cinner_commute cinner_scaleR_left cinner_scaleR_right cmod_Re complex_inner_class.Cauchy_Schwarz_ineq2 left_inverse less_eq_complex_def linordered_field_class.inverse_nonnegative_iff_nonnegative mult_cancel_left2 mult_left_mono norm_cblinfun norm_ge_zero norm_mult norm_of_real norm_one positive_hermitianI reals_zero_comparable zero_less_one_class.zero_le_one)
    show \<open>x \<bullet>\<^sub>C (S *\<^sub>V x) \<le> x \<bullet>\<^sub>C (0 *\<^sub>V x)\<close>
      by (auto simp: S_def cinner_diff_right cblinfun.diff_left scaleR_scaleC cdot_square_norm k_def complex_of_real_mono_iff[where y=1, simplified]
          simp flip: assms of_real_inverse of_real_power of_real_mult power_mult_distrib power_inverse
          intro!: power_le_one aux1)
  qed
  have [simp]: \<open>S* = S\<close>
    using \<open>S \<le> 0\<close> adj_0 comparable_hermitean' selfadjoint_def by blast
  have \<open>- id_cblinfun \<le> S\<close>
    by (simp add: S_def assms k_def scaleR_nonneg_nonneg)
  then have \<open>norm (S *\<^sub>V f) \<le> norm f\<close> for f
  proof -
    have 1: \<open>- S \<ge> 0\<close>
      by (simp add: \<open>S \<le> 0\<close>)
    have 2: \<open>f \<bullet>\<^sub>C (- S *\<^sub>V f) \<le> f \<bullet>\<^sub>C f\<close>
      by (metis \<open>- id_cblinfun \<le> S\<close> id_cblinfun_apply less_eq_cblinfun_def minus_le_iff)

    have \<open>(norm (S *\<^sub>V f))^4 = complex_of_real ((cmod ((- S *\<^sub>V f) \<bullet>\<^sub>C (- S *\<^sub>V f)))\<^sup>2)\<close>
      apply (auto simp: power4_eq_xxxx cblinfun.minus_left complex_of_real_cmod power2_eq_square simp flip: power2_norm_eq_cinner)
      by (smt (verit, ccfv_SIG) complex_of_real_cmod mult.assoc norm_ge_zero norm_mult norm_of_real of_real_mult)
    also have \<open>\<dots> \<le> (- S *\<^sub>V f) \<bullet>\<^sub>C (- S *\<^sub>V - S *\<^sub>V f) * (f \<bullet>\<^sub>C (- S *\<^sub>V f))\<close>
      apply (rule generalized_Cauchy_Schwarz[where A=\<open>-S\<close> and x = \<open>-S *\<^sub>V f\<close> and y = f])
      by (fact 1)
    also have \<open>\<dots> \<le> (- S *\<^sub>V f) \<bullet>\<^sub>C (- S *\<^sub>V - S *\<^sub>V f) * (f \<bullet>\<^sub>C f)\<close>
      using 2 apply (rule mult_left_mono)
      using "1" cinner_pos_if_pos by blast
    also have \<open>\<dots> \<le> (- S *\<^sub>V f) \<bullet>\<^sub>C (- S *\<^sub>V f) * (f \<bullet>\<^sub>C f)\<close>
      apply (rule mult_right_mono)
      apply (metis \<open>- id_cblinfun \<le> S\<close> id_cblinfun_apply less_eq_cblinfun_def neg_le_iff_le verit_minus_simplify(4))
      by simp
    also have \<open>\<dots> = (norm (-S *\<^sub>V f))\<^sup>2 * (norm f)\<^sup>2\<close>
      by (simp add: cdot_square_norm)
    also have \<open>\<dots> = (norm (S *\<^sub>V f))\<^sup>2 * (norm f)\<^sup>2\<close>
      by (simp add: cblinfun.minus_left)
    finally have \<open>norm (S *\<^sub>V f) ^ 4 \<le> (norm (S *\<^sub>V f))\<^sup>2 * (norm f)\<^sup>2\<close>
      using complex_of_real_mono_iff by blast
    then have \<open>(norm (S *\<^sub>V f))\<^sup>2 \<le> (norm f)\<^sup>2\<close>
      by (smt (verit, best) \<open>complex_of_real (norm (S *\<^sub>V f) ^ 4) = complex_of_real ((cmod ((- S *\<^sub>V f) \<bullet>\<^sub>C (- S *\<^sub>V f)))\<^sup>2)\<close> cblinfun.real.minus_left cinner_ge_zero cmod_Re mult_cancel_left mult_left_mono norm_minus_cancel of_real_eq_iff power2_eq_square power2_norm_eq_cinner' zero_less_norm_iff)
    then show \<open>norm (S *\<^sub>V f) \<le> norm f\<close>
      by auto
  qed
  then have norm_Snf: \<open>norm (cblinfun_power S n *\<^sub>V f) \<le> norm f\<close> for f n
    by (induction n, auto simp: cblinfun_power_Suc' intro: order.trans)
  have fSnf: \<open>cmod (f \<bullet>\<^sub>C (cblinfun_power S n *\<^sub>V f)) \<le> cmod (f \<bullet>\<^sub>C f)\<close> for f n
    by (smt (z3) One_nat_def Re_complex_of_real Suc_1 cdot_square_norm cinner_ge_zero cmod_Re complex_inner_class.Cauchy_Schwarz_ineq2 mult.commute mult_cancel_right1 mult_left_mono norm_Snf norm_ge_zero power_0 power_Suc)
  from norm_Snf have norm_Sn: \<open>norm (cblinfun_power S n) \<le> 1\<close> for n
    apply (rule_tac norm_cblinfun_bound)
    by auto
  define b where \<open>b = (\<lambda>n. (1/2 gchoose n) *\<^sub>R cblinfun_power S n)\<close>
  define B0 B where \<open>B0 = infsum b UNIV\<close> and \<open>B = sqrt k *\<^sub>R B0\<close>

  have sum_norm_b: \<open>(\<Sum>n\<in>F. norm (b n)) \<le> 3\<close> (is \<open>?lhs \<le> ?rhs\<close>) if \<open>finite F\<close> for F
  proof -
    have [simp]: \<open>\<lceil>1 / 2 :: real\<rceil> = 1\<close>
      by (simp add: ceiling_eq_iff)
    from \<open>finite F\<close> obtain d where \<open>F \<subseteq> {..d}\<close> and [simp]: \<open>d > 0\<close>
      by (metis Icc_subset_Iic_iff atLeast0AtMost bot_nat_0.extremum bot_nat_0.not_eq_extremum dual_order.trans finite_nat_iff_bounded_le less_one)

    have \<open>?lhs = (\<Sum>n\<in>F. norm ((1 / 2 gchoose n) *\<^sub>R (cblinfun_power S n)))\<close>
      by (simp add: b_def scaleR_cblinfun.rep_eq)
    also have \<open>\<dots> \<le> (\<Sum>n\<in>F. abs ((1 / 2 gchoose n)))\<close>
      apply (auto intro!: sum_mono)
      using norm_Sn
      by (metis norm_cmul_rule_thm norm_scaleR verit_prod_simplify(2))
    also have \<open>\<dots> \<le> (\<Sum>n\<le>d. abs (1/2 gchoose n))\<close>
      using \<open>F \<subseteq> {..d}\<close> by (auto intro!: mult_right_mono sum_mono2)
    also have \<open>\<dots> = (2 - (- 1) ^ d * (- (1 / 2) gchoose d))\<close>
      apply (subst gbinomial_sum_lower_abs)
      by auto
    also have \<open>\<dots> \<le> (2 + norm (- (1/2) gchoose d :: real))\<close>
      apply (auto intro!: mult_right_mono)
      by (smt (verit) left_minus_one_mult_self mult.assoc mult_minus_left power2_eq_iff power2_eq_square)
    also have \<open>\<dots> \<le> 3\<close>
      apply (subgoal_tac \<open>abs (- (1/2) gchoose d :: real) \<le> 1\<close>)
      apply (metis add_le_cancel_left is_num_normalize(1) mult.commute mult_left_mono norm_ge_zero numeral_Bit0 numeral_Bit1 one_add_one real_norm_def)
      apply (rule abs_gbinomial_leq1)
      by auto
    finally show ?thesis
      by -
  qed

  have has_sum_b: \<open>(b has_sum B0) UNIV\<close>
    apply (auto intro!: has_sum_infsum abs_summable_summable[where f=b] bdd_aboveI[where M=3] simp: B0_def abs_summable_iff_bdd_above)
    using sum_norm_b
    by simp

  have \<open>B0 \<ge> 0\<close>
  proof (rule positive_cblinfunI)
    fix f :: 'a assume [simp]: \<open>norm f = 1\<close>
    from has_sum_b
    have sum1: \<open>(\<lambda>n. f \<bullet>\<^sub>C (b n *\<^sub>V f)) summable_on UNIV\<close>
      apply (intro summable_on_cinner_left summable_on_cblinfun_apply_left)
      by (simp add: has_sum_imp_summable)
    have sum2: \<open>(\<lambda>x. - (complex_of_real \<bar>1 / 2 gchoose x\<bar> * (f \<bullet>\<^sub>C f))) summable_on UNIV - {0}\<close>
      apply (rule abs_summable_summable)
      using gbinomial_abs_summable_1[of \<open>1/2\<close>]
      by (auto simp add: cnorm_eq_1[THEN iffD1])
    from sum1 have sum3: \<open>(\<lambda>n. complex_of_real (1 / 2 gchoose n) * (f \<bullet>\<^sub>C (cblinfun_power S n *\<^sub>V f))) summable_on UNIV - {0}\<close>
      unfolding b_def
      by (metis (no_types, lifting) cinner_scaleR_right finite.emptyI finite_insert 
          scaleR_cblinfun.rep_eq summable_on_cofin_subset summable_on_cong)

    have aux: \<open>a \<ge> - b\<close> if \<open>norm a \<le> norm b\<close> and \<open>a \<in> \<real>\<close> and \<open>b \<ge> 0\<close> for a b :: complex
      using cmod_eq_Re complex_is_Real_iff less_eq_complex_def that(1) that(2) that(3) by force

    from has_sum_b
    have \<open>f \<bullet>\<^sub>C (B0 *\<^sub>V f) = (\<Sum>\<^sub>\<infinity>n. f \<bullet>\<^sub>C (b n *\<^sub>V f))\<close>
      by (metis B0_def infsum_cblinfun_apply_left infsum_cinner_left summable_on_cblinfun_apply_left summable_on_def)
    moreover have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>n\<in>UNIV-{0}. f \<bullet>\<^sub>C (b n *\<^sub>V f)) + f \<bullet>\<^sub>C (b 0 *\<^sub>V f)\<close>
      apply (subst infsum_Diff)
      using sum1 by auto
    moreover have \<open>\<dots> = f \<bullet>\<^sub>C (b 0 *\<^sub>V f) + (\<Sum>\<^sub>\<infinity>n\<in>UNIV-{0}. f \<bullet>\<^sub>C ((1/2 gchoose n) *\<^sub>R cblinfun_power S n *\<^sub>V f))\<close>
      unfolding b_def by simp
    moreover have \<open>\<dots> = f \<bullet>\<^sub>C (b 0 *\<^sub>V f) + (\<Sum>\<^sub>\<infinity>n\<in>UNIV-{0}. of_real (1/2 gchoose n) * (f \<bullet>\<^sub>C (cblinfun_power S n *\<^sub>V f)))\<close>
      by (simp add: scaleR_cblinfun.rep_eq)
    moreover have \<open>\<dots> \<ge> f \<bullet>\<^sub>C (b 0 *\<^sub>V f) - (\<Sum>\<^sub>\<infinity>n\<in>UNIV-{0}. of_real (abs (1/2 gchoose n)) * (f \<bullet>\<^sub>C f))\<close> (is \<open>_ \<ge> \<dots>\<close>)
    proof -
      have *: \<open>- (complex_of_real (abs (1 / 2 gchoose x)) * (f \<bullet>\<^sub>C f))
         \<le> complex_of_real (1 / 2 gchoose x) * (f \<bullet>\<^sub>C (cblinfun_power S x *\<^sub>V f))\<close> for x
        apply (rule aux)
        by (auto simp: cblinfun_power_adj norm_mult fSnf selfadjoint_def
            intro!: cinner_real cinner_hermitian_real mult_left_mono Reals_mult mult_nonneg_nonneg)
      show ?thesis
        apply (subst diff_conv_add_uminus) apply (rule add_left_mono)
        apply (subst infsum_uminus[symmetric]) apply (rule infsum_mono_complex)
        apply (rule sum2)
        apply (rule sum3)
        by (rule *)
    qed
    moreover have \<open>\<dots> = f \<bullet>\<^sub>C (b 0 *\<^sub>V f) - (\<Sum>\<^sub>\<infinity>n\<in>UNIV-{0}. of_real (abs (1/2 gchoose n))) * (f \<bullet>\<^sub>C f)\<close>
      by (simp add: infsum_cmult_left')
    moreover have \<open>\<dots> = of_real (1 - (\<Sum>\<^sub>\<infinity>n\<in>UNIV-{0}. (abs (1/2 gchoose n)))) * (f \<bullet>\<^sub>C f)\<close>
      by (simp add: b_def left_diff_distrib infsum_of_real)
    moreover have \<open>\<dots> \<ge> 0 * (f \<bullet>\<^sub>C f)\<close> (is \<open>_ \<ge> \<dots>\<close>)
      apply (auto intro!: mult_nonneg_nonneg)
      using gbinomial_abs_has_sum_1[where a=\<open>1/2\<close>]
      by (auto simp add: infsumI)
    moreover have \<open>\<dots> = 0\<close>
      by simp
    ultimately show \<open>f \<bullet>\<^sub>C (B0 *\<^sub>V f) \<ge> 0\<close>
      by force
  qed
  then have \<open>B \<ge> 0\<close>
    by (simp add: B_def k_def scaleR_nonneg_nonneg)
  then have \<open>B = B*\<close>
    by (simp add: positive_hermitianI)
  have \<open>B0 o\<^sub>C\<^sub>L B0 = id_cblinfun + S\<close>
  proof (rule cblinfun_cinner_eqI)
    fix \<psi>
    define s bb where \<open>s = \<psi> \<bullet>\<^sub>C ((B0 o\<^sub>C\<^sub>L B0) *\<^sub>V \<psi>)\<close> and \<open>bb k = (\<Sum>n\<le>k. (b n *\<^sub>V \<psi>) \<bullet>\<^sub>C (b (k - n) *\<^sub>V \<psi>))\<close> for k

    have \<open>bb k = (\<Sum>n\<le>k. of_real ((1 / 2 gchoose (k - n)) * (1 / 2 gchoose n)) * (\<psi> \<bullet>\<^sub>C (cblinfun_power S k *\<^sub>V \<psi>)))\<close> for k
      by (simp add: bb_def[abs_def] b_def cblinfun.scaleR_left cblinfun_power_adj mult.assoc
          flip: cinner_adj_right cblinfun_apply_cblinfun_compose)
    also have \<open>\<dots>k = of_real (\<Sum>n\<le>k. ((1 / 2 gchoose n) * (1 / 2 gchoose (k - n)))) * (\<psi> \<bullet>\<^sub>C (cblinfun_power S k *\<^sub>V \<psi>))\<close> for k
      apply (subst mult.commute) by (simp add: sum_distrib_right)
    also have \<open>\<dots>k = of_real (1 gchoose k) * (\<psi> \<bullet>\<^sub>C (cblinfun_power S k *\<^sub>V \<psi>))\<close> for k
      apply (simp only: atMost_atLeast0 gbinomial_Vandermonde)
      by simp
    also have \<open>\<dots>k = of_bool (k \<le> 1) * (\<psi> \<bullet>\<^sub>C (cblinfun_power S k *\<^sub>V \<psi>))\<close> for k
      by (simp add: gbinomial_1)
    finally have bb_simp: \<open>bb k = of_bool (k \<le> 1) * (\<psi> \<bullet>\<^sub>C (cblinfun_power S k *\<^sub>V \<psi>))\<close> for k
      by -

    have bb_sum: \<open>bb summable_on UNIV\<close>
      apply (rule summable_on_cong_neutral[where T=\<open>{..1}\<close> and g=bb, THEN iffD2])
      by (auto simp: bb_simp)

    from has_sum_b have b\<psi>_sum: \<open>(\<lambda>n. b n *\<^sub>V \<psi>) summable_on UNIV\<close>
      by (simp add: has_sum_imp_summable summable_on_cblinfun_apply_left)

    have b2_pos: \<open>(b i *\<^sub>V \<psi>) \<bullet>\<^sub>C (b j *\<^sub>V \<psi>) \<ge> 0\<close> if \<open>i\<noteq>0\<close> \<open>j\<noteq>0\<close> for i j
    proof -
      have gchoose_sign: \<open>(-1) ^ (i+1) * ((1/2 :: real) gchoose i) \<ge> 0\<close> if \<open>i\<noteq>0\<close> for i
      proof -
        obtain j where j: \<open>Suc j = i\<close>
          using \<open>i \<noteq> 0\<close> not0_implies_Suc by blast
        show ?thesis
        proof (unfold j[symmetric], induction j)
          case 0
          then show ?case
            by simp
        next
          case (Suc j)
          have \<open>(- 1) ^ (Suc (Suc j) + 1) * (1 / 2 gchoose Suc (Suc j))
               = ((- 1) ^ (Suc j + 1) * (1 / 2 gchoose Suc j)) * ((-1) * (1/2-Suc j) / (Suc (Suc j)))\<close>
            apply (simp add: gbinomial_a_Suc_n)
            by (smt (verit, ccfv_threshold) divide_divide_eq_left' divide_divide_eq_right minus_divide_right)
          also have \<open>\<dots> \<ge> 0\<close>
            apply (rule mult_nonneg_nonneg)
             apply (rule Suc.IH)
            apply (rule divide_nonneg_pos)
             apply (rule mult_nonpos_nonpos)
            by auto
          finally show ?case
            by -
        qed
      qed
      from \<open>S \<le> 0\<close>
      have Sn_sign: \<open>\<psi> \<bullet>\<^sub>C (cblinfun_power (- S) (i + j) *\<^sub>V \<psi>) \<ge> 0\<close>
        by (auto intro!: cinner_pos_if_pos cblinfun_power_pos)
      have *: \<open>(- 1) ^ (i + (j + (i + j))) = (1::complex)\<close>
        by (metis Parity.ring_1_class.power_minus_even even_add power_one)

      have \<open>(b i *\<^sub>V \<psi>) \<bullet>\<^sub>C (b j *\<^sub>V \<psi>)
          = complex_of_real (1 / 2 gchoose i) * complex_of_real (1 / 2 gchoose j)
             * (\<psi> \<bullet>\<^sub>C (cblinfun_power S (i + j) *\<^sub>V \<psi>))\<close>
        by (simp add: b_def cblinfun.scaleR_right cblinfun.scaleR_left cblinfun_power_adj
            flip: cinner_adj_right cblinfun_apply_cblinfun_compose)
      also have \<open>\<dots> = complex_of_real ((-1)^(i+1) * (1 / 2 gchoose i)) * complex_of_real ((-1)^(j+1) * (1 / 2 gchoose j))
             * (\<psi> \<bullet>\<^sub>C (cblinfun_power (-S) (i + j) *\<^sub>V \<psi>))\<close>
        by (simp add: cblinfun.scaleR_left cblinfun_power_uminus * flip: power_add)
      also have \<open>\<dots> \<ge> 0\<close>
        apply (rule mult_nonneg_nonneg)
        apply (rule mult_nonneg_nonneg)
        using complex_of_real_nn_iff gchoose_sign that(1) apply blast
        using complex_of_real_nn_iff gchoose_sign that(2) apply blast
        by (fact Sn_sign)
      finally show ?thesis
        by -
    qed

    have \<open>s = (B0 *\<^sub>V \<psi>) \<bullet>\<^sub>C (B0 *\<^sub>V \<psi>)\<close>
      by (metis \<open>0 \<le> B0\<close> cblinfun_apply_cblinfun_compose cinner_adj_left positive_hermitianI s_def)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>n. b n *\<^sub>V \<psi>) \<bullet>\<^sub>C (\<Sum>\<^sub>\<infinity>n. b n *\<^sub>V \<psi>)\<close>
      by (metis B0_def has_sum_b infsum_cblinfun_apply_left has_sum_imp_summable)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>n. bb n)\<close>
      using b\<psi>_sum b\<psi>_sum unfolding bb_def
      apply (rule Cauchy_cinner_product_infsum[symmetric])
      using b\<psi>_sum b\<psi>_sum
      apply (rule Cauchy_cinner_product_summable[where X=\<open>{0}\<close> and Y=\<open>{0}\<close>])
      using b2_pos by auto
    also have \<open>\<dots> = bb 0 + bb 1\<close>
      apply (subst infsum_cong_neutral[where T=\<open>{..1}\<close> and g=bb])
      by (auto simp: bb_simp)
    also have \<open>\<dots> = \<psi> \<bullet>\<^sub>C ((id_cblinfun + S) *\<^sub>V \<psi>)\<close>
      by (simp add: cblinfun_power_Suc cblinfun.add_left cinner_add_right bb_simp)
    finally show \<open>s = \<psi> \<bullet>\<^sub>C ((id_cblinfun + S) *\<^sub>V \<psi>)\<close>
      by -
  qed
  then have \<open>B o\<^sub>C\<^sub>L B = norm A *\<^sub>C (id_cblinfun + S)\<close>
    apply (simp add: k_def B_def power2_eq_square scaleR_scaleC)
    by (metis norm_imp_pos_and_ge of_real_power power2_eq_square real_sqrt_pow2)
  also have \<open>\<dots> = A\<close>
    by (metis (no_types, lifting) k_def S_def add.commute cancel_comm_monoid_add_class.diff_cancel diff_add_cancel norm_eq_zero of_real_1 of_real_mult right_inverse scaleC_diff_right scaleC_one scaleC_scaleC scaleR_scaleC)
  finally have B2A: \<open>B o\<^sub>C\<^sub>L B = A\<close>
    by -
  have BF_comm: \<open>B o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L B\<close> if \<open>A o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L A\<close> for F
  proof -
    have \<open>S o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L S\<close>
      by (simp add: S_def that[symmetric] cblinfun_compose_minus_right cblinfun_compose_minus_left 
          flip: cblinfun_compose_assoc)
    then have \<open>cblinfun_power S n o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L cblinfun_power S n\<close> for n
      apply (induction n)
       apply (simp_all add: cblinfun_power_Suc' cblinfun_compose_assoc)
      by (simp flip: cblinfun_compose_assoc)
    then have *: \<open>b n o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L b n\<close> for n
      by (simp add: b_def)
    have \<open>(\<Sum>\<^sub>\<infinity>n. b n) o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L (\<Sum>\<^sub>\<infinity>n. b n)\<close>
    proof -
      have [simp]: \<open>b summable_on UNIV\<close>
        using has_sum_b by (auto simp add: summable_on_def)
      have \<open>(\<Sum>\<^sub>\<infinity>n. b n) o\<^sub>C\<^sub>L F = (\<Sum>\<^sub>\<infinity>n. (b n) o\<^sub>C\<^sub>L F)\<close>
        apply (subst infsum_comm_additive[where f=\<open>\<lambda>x. x o\<^sub>C\<^sub>L F\<close>, symmetric])
        by (auto simp: o_def isCont_cblinfun_compose_left)
      also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>n. F o\<^sub>C\<^sub>L (b n))\<close>
        by (simp add: * )
      also have \<open>\<dots> = F o\<^sub>C\<^sub>L (\<Sum>\<^sub>\<infinity>n. b n)\<close>
        apply (subst infsum_comm_additive[where f=\<open>\<lambda>x. F o\<^sub>C\<^sub>L x\<close>, symmetric])
        by (auto simp: o_def isCont_cblinfun_compose_right)
      finally show ?thesis
        by -
    qed
    then have \<open>B0 o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L B0\<close>
      unfolding B0_def
      unfolding infsum_euclidean_eq[abs_def, symmetric]
      apply (transfer fixing: b F)
      by simp
    then show ?thesis
      by (auto simp: B_def)
  qed
  have B_closure: \<open>B \<in> closure (cspan (range (cblinfun_power A)))\<close>
  proof (cases \<open>k = 0\<close>)
    case True
    then show ?thesis 
      unfolding B_def using closure_subset complex_vector.span_zero by auto
  next
    case False
    then have \<open>k \<noteq> 0\<close>
      by -
    from has_sum_b
    have limit: \<open>(sum b \<longlongrightarrow> B0) (finite_subsets_at_top UNIV)\<close>
      by (simp add: has_sum_def)
    have \<open>cblinfun_power (A /\<^sub>R k - id_cblinfun) n \<in> cspan (range (cblinfun_power A))\<close> for n
    proof (induction n)
      case 0
      then show ?case 
        by (auto intro!: complex_vector.span_base range_eqI[where x=0])
    next
      case (Suc n)
      define pow_n where \<open>pow_n = cblinfun_power (A /\<^sub>R k - id_cblinfun) n\<close>
      have pow_n_span: \<open>pow_n \<in> cspan (range (cblinfun_power A))\<close>
        using Suc by (simp add: pow_n_def)
      have A_pow_n_span: \<open>A o\<^sub>C\<^sub>L pow_n \<in> cspan (range (cblinfun_power A))\<close>
      proof -
        from pow_n_span
        obtain F r where \<open>finite F\<close> and F_A: \<open>F \<subseteq> range (cblinfun_power A)\<close>
          and pow_n_sum: \<open>pow_n = (\<Sum>a\<in>F. r a *\<^sub>C a)\<close>
          by (auto simp add: complex_vector.span_explicit)
        have \<open>A o\<^sub>C\<^sub>L a \<in> range (cblinfun_power A)\<close> if \<open>a \<in> F\<close> for a
        proof -
          from that obtain m where \<open>a = cblinfun_power A m\<close>
            using F_A by auto
          then have \<open>A o\<^sub>C\<^sub>L a = cblinfun_power A (Suc m)\<close>
            by (simp add: cblinfun_power_Suc')
          then show ?thesis
            by auto
        qed
        then have \<open>(\<Sum>a\<in>F. r a *\<^sub>C (A o\<^sub>C\<^sub>L a)) \<in> cspan (range (cblinfun_power A))\<close>
          by (meson basic_trans_rules(31) complex_vector.span_scale complex_vector.span_sum complex_vector.span_superset)
        moreover have \<open>A o\<^sub>C\<^sub>L pow_n = (\<Sum>a\<in>F. r a *\<^sub>C (A o\<^sub>C\<^sub>L a))\<close>
          by (simp add: pow_n_sum cblinfun_compose_sum_right flip: cblinfun.scaleC_left)
        ultimately show ?thesis
          by simp
      qed
      have \<open>cblinfun_power (A /\<^sub>R k - id_cblinfun) (Suc n) = (A o\<^sub>C\<^sub>L pow_n) /\<^sub>R k - pow_n\<close>
        by (simp add: cblinfun_power_Suc' cblinfun_compose_minus_left flip: pow_n_def)
      also from pow_n_span A_pow_n_span 
      have \<open>\<dots> \<in> cspan (range (cblinfun_power A))\<close>
        by (auto intro!: complex_vector.span_diff complex_vector.span_scale 
            simp: scaleR_scaleC)
      finally show ?case
        by -
    qed
    then have b_range: \<open>b n \<in> cspan (range (cblinfun_power A))\<close> for n
      by (simp add: b_def S_def scaleR_scaleC complex_vector.span_scale)
    have sum_bF: \<open>sum b F \<in> cspan (range (cblinfun_power A))\<close> if \<open>finite F\<close> for F
      using that apply induction
      using b_range complex_vector.span_add complex_vector.span_zero by auto
    have \<open>B0 \<in> closure (cspan (range (cblinfun_power A)))\<close>
      using limit apply (rule limit_in_closure)
      using sum_bF by (simp_all add: eventually_finite_subsets_at_top_weakI)
    also have \<open>\<dots> = closure ((\<lambda>x. inverse (sqrt k) *\<^sub>R x) ` cspan (range (cblinfun_power A)))\<close>
      using \<open>k \<noteq> 0\<close> by (simp add: scaleR_scaleC csubspace_scaleC_invariant)
    also have \<open>\<dots> = (\<lambda>x. inverse (sqrt k) *\<^sub>R x) ` closure (cspan (range (cblinfun_power A)))\<close>
      by (simp add: closure_scaleR)
    finally show ?thesis
      apply (simp add: B_def image_def)
      using \<open>k \<noteq> 0\<close> by force
  qed
  from \<open>B \<ge> 0\<close> B2A BF_comm B_closure
  show ?thesis
    by metis
qed


lemma wecken35hilfssatz:
  \<comment> \<open>Auxiliary lemma from \<^cite>\<open>wecken35linearer\<close>\<close>
  \<open>\<exists>P. is_Proj P \<and> (\<forall>F. F o\<^sub>C\<^sub>L (W - T) = (W - T) o\<^sub>C\<^sub>L F \<longrightarrow> F o\<^sub>C\<^sub>L P = P o\<^sub>C\<^sub>L F)
     \<and> (\<forall>f. W f = 0 \<longrightarrow> P f = f)
     \<and> (W = (2 *\<^sub>C P - id_cblinfun) o\<^sub>C\<^sub>L T)\<close>
  if WT_comm: \<open>W o\<^sub>C\<^sub>L T = T o\<^sub>C\<^sub>L W\<close> and \<open>W = W*\<close> and \<open>T = T*\<close> 
    and WW_TT: \<open>W o\<^sub>C\<^sub>L W = T o\<^sub>C\<^sub>L T\<close>
  for W T :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
proof (rule exI, intro conjI allI impI)
  define P where \<open>P = Proj (kernel (W-T))\<close>
  show \<open>is_Proj P\<close>
    by (simp add: P_def)
  show thesis1: \<open>F o\<^sub>C\<^sub>L P = P o\<^sub>C\<^sub>L F\<close> if \<open>F o\<^sub>C\<^sub>L (W - T) = (W - T) o\<^sub>C\<^sub>L F\<close> for F
  proof -
    have 1: \<open>F o\<^sub>C\<^sub>L P = P o\<^sub>C\<^sub>L F o\<^sub>C\<^sub>L P\<close> if \<open>F o\<^sub>C\<^sub>L (W - T) = (W - T) o\<^sub>C\<^sub>L F\<close> for F
    proof (rule cblinfun_eqI)
      fix \<psi>
      have \<open>P *\<^sub>V \<psi> \<in> space_as_set (kernel (W - T))\<close>
        by (metis P_def Proj_range cblinfun_apply_in_image)
      then have \<open>(W - T) *\<^sub>V P *\<^sub>V \<psi> = 0\<close>
        using kernel_memberD by blast
      then have \<open>(W - T) *\<^sub>V F *\<^sub>V P *\<^sub>V \<psi> = 0\<close>
        by (metis cblinfun.zero_right cblinfun_apply_cblinfun_compose that)
      then have \<open>F *\<^sub>V P *\<^sub>V \<psi> \<in> space_as_set (kernel (W - T))\<close>
        using kernel_memberI by blast
      then have \<open>P *\<^sub>V (F *\<^sub>V P *\<^sub>V \<psi>) = F *\<^sub>V P *\<^sub>V \<psi>\<close>
        using P_def Proj_fixes_image by blast
      then show \<open>(F o\<^sub>C\<^sub>L P) *\<^sub>V \<psi> = (P o\<^sub>C\<^sub>L F o\<^sub>C\<^sub>L P) *\<^sub>V \<psi>\<close>
        by simp
    qed
    have 2: \<open>F* o\<^sub>C\<^sub>L (W - T) = (W - T) o\<^sub>C\<^sub>L F*\<close>
      by (metis \<open>T = T*\<close> \<open>W = W*\<close> adj_cblinfun_compose adj_minus that)
    have \<open>F o\<^sub>C\<^sub>L P = P o\<^sub>C\<^sub>L F o\<^sub>C\<^sub>L P\<close> and \<open>F* o\<^sub>C\<^sub>L P = P o\<^sub>C\<^sub>L F* o\<^sub>C\<^sub>L P\<close>
      using 1[OF that] 1[OF 2] by auto
    then show \<open>F o\<^sub>C\<^sub>L P = P o\<^sub>C\<^sub>L F\<close>
      by (metis P_def adj_Proj adj_cblinfun_compose cblinfun_assoc_left(1) double_adj)
  qed
  show thesis2: \<open>P *\<^sub>V f = f\<close> if \<open>W *\<^sub>V f = 0\<close> for f
  proof -
    from that
    have \<open>0 = (W *\<^sub>V f) \<bullet>\<^sub>C (W *\<^sub>V f)\<close>
      by simp
    also from \<open>W = W*\<close> have \<open>\<dots> = f \<bullet>\<^sub>C ((W o\<^sub>C\<^sub>L W) *\<^sub>V f)\<close>
      by (simp add: that)
    also from WW_TT have \<open>\<dots> = f \<bullet>\<^sub>C ((T o\<^sub>C\<^sub>L T) *\<^sub>V f)\<close>
      by simp
    also from \<open>T = T*\<close> have \<open>\<dots> = (T *\<^sub>V f) \<bullet>\<^sub>C (T *\<^sub>V f)\<close>
      by (metis cblinfun_apply_cblinfun_compose cinner_adj_left)
    finally have \<open>T *\<^sub>V f = 0\<close>
      by simp
    then have \<open>(W - T) *\<^sub>V f = 0\<close>
      by (simp add: cblinfun.diff_left that)
    then show \<open>P *\<^sub>V f = f\<close>
      using P_def Proj_fixes_image kernel_memberI by blast
  qed
  show thesis3: \<open>W = (2 *\<^sub>C P - id_cblinfun) o\<^sub>C\<^sub>L T\<close>
  proof -
    from WW_TT WT_comm have WT_binomial: \<open>(W - T) o\<^sub>C\<^sub>L (W + T) = 0\<close>
      by (simp add: cblinfun_compose_add_right cblinfun_compose_minus_left)
    have PWT: \<open>P o\<^sub>C\<^sub>L (W + T) = W + T\<close>
    proof (rule cblinfun_eqI)
      fix \<psi>
      from WT_binomial have \<open>(W + T) *\<^sub>V \<psi> \<in> space_as_set (kernel (W-T))\<close>
        by (metis cblinfun_apply_cblinfun_compose kernel_memberI zero_cblinfun.rep_eq)
      then show \<open>(P o\<^sub>C\<^sub>L (W + T)) *\<^sub>V \<psi> = (W + T) *\<^sub>V \<psi>\<close>
        by (metis P_def Proj_idempotent Proj_range cblinfun_apply_cblinfun_compose cblinfun_fixes_range)
    qed
    from P_def have \<open>(W - T) o\<^sub>C\<^sub>L P = 0\<close>
      by (metis Proj_range thesis1 cblinfun_apply_cblinfun_compose cblinfun_apply_in_image
          cblinfun_eqI kernel_memberD zero_cblinfun.rep_eq)
    with PWT WT_comm thesis1 have \<open>2 *\<^sub>C T o\<^sub>C\<^sub>L P = W + T\<close>
      by (metis (no_types, lifting) bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose cblinfun_compose_add_right cblinfun_compose_minus_left cblinfun_compose_minus_right eq_iff_diff_eq_0 scaleC_2)
    with  that(2) that(3) show ?thesis
      by (smt (verit, ccfv_threshold) P_def add_diff_cancel adj_Proj adj_cblinfun_compose adj_plus cblinfun_compose_id_right cblinfun_compose_minus_left cblinfun_compose_scaleC_left id_cblinfun_adjoint scaleC_2)
  qed
qed

lemma sqrt_op_pos[simp]: \<open>sqrt_op a \<ge> 0\<close>
proof (cases \<open>a \<ge> 0\<close>)
  case True
  from sqrt_op_existence[OF True]
  have *: \<open>\<exists>b::'a \<Rightarrow>\<^sub>C\<^sub>L 'a. b \<ge> 0 \<and> b* o\<^sub>C\<^sub>L b = a\<close>
    by (metis positive_hermitianI)
  then show ?thesis
    using * by (smt (verit, ccfv_threshold) someI_ex sqrt_op_def)
next
  case False
  then show ?thesis
    by (simp add: sqrt_op_nonpos)
qed

lemma sqrt_op_square[simp]: 
  assumes \<open>a \<ge> 0\<close>
  shows \<open>sqrt_op a o\<^sub>C\<^sub>L sqrt_op a = a\<close>
proof -
  from sqrt_op_existence[OF assms]
  have *: \<open>\<exists>b::'a \<Rightarrow>\<^sub>C\<^sub>L 'a. b \<ge> 0 \<and> b* o\<^sub>C\<^sub>L b = a\<close>
    by (metis positive_hermitianI)
  have \<open>sqrt_op a o\<^sub>C\<^sub>L sqrt_op a = (sqrt_op a)* o\<^sub>C\<^sub>L sqrt_op a\<close>
    by (metis positive_hermitianI sqrt_op_pos)
  also have \<open>(sqrt_op a)* o\<^sub>C\<^sub>L sqrt_op a = a\<close>
    using * by (metis (mono_tags, lifting) someI_ex sqrt_op_def)
  finally show ?thesis
    by -
qed

lemma sqrt_op_unique:
  \<comment> \<open>Proof follows \<^cite>\<open>wecken35linearer\<close>\<close>
  assumes \<open>b \<ge> 0\<close> and \<open>b* o\<^sub>C\<^sub>L b = a\<close>
  shows \<open>b = sqrt_op a\<close>
proof -
  have \<open>a \<ge> 0\<close>
    using assms(2) positive_cblinfun_squareI by blast 
  from sqrt_op_existence[OF \<open>a \<ge> 0\<close>]
  obtain sq where \<open>sq \<ge> 0\<close> and \<open>sq o\<^sub>C\<^sub>L sq = a\<close> and a_comm: \<open>a o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L a \<Longrightarrow> sq o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L sq\<close> for F
    by metis
  have eq_sq: \<open>b = sq\<close> if \<open>b \<ge> 0\<close> and \<open>b* o\<^sub>C\<^sub>L b = a\<close> for b
  proof -
    have \<open>b o\<^sub>C\<^sub>L a = a o\<^sub>C\<^sub>L b\<close>
      by (metis cblinfun_assoc_left(1) positive_hermitianI that(1) that(2))
    then have b_sqrt_comm: \<open>b o\<^sub>C\<^sub>L sq = sq o\<^sub>C\<^sub>L b\<close>
      using a_comm by force
    from \<open>b \<ge> 0\<close> have \<open>b = b*\<close>
      by (simp add: assms(1) positive_hermitianI)
    have sqrt_adj: \<open>sq = sq*\<close>
      by (simp add: \<open>0 \<le> sq\<close> positive_hermitianI)
    have bb_sqrt: \<open>b o\<^sub>C\<^sub>L b = sq o\<^sub>C\<^sub>L sq\<close>
      using \<open>b = b*\<close> \<open>sq o\<^sub>C\<^sub>L sq = a\<close> that(2) by fastforce

    from wecken35hilfssatz[OF b_sqrt_comm \<open>b = b*\<close> sqrt_adj bb_sqrt]
    obtain P where \<open>is_Proj P\<close> and b_P_sq: \<open>b = (2 *\<^sub>C P - id_cblinfun) o\<^sub>C\<^sub>L sq\<close>
      and Pcomm: \<open>F o\<^sub>C\<^sub>L (b - sq) = (b - sq) o\<^sub>C\<^sub>L F \<Longrightarrow> F o\<^sub>C\<^sub>L P = P o\<^sub>C\<^sub>L F\<close> for F
      by metis

    have 1: \<open>sandwich (id_cblinfun - P) b = (id_cblinfun - P) o\<^sub>C\<^sub>L b\<close>
      by (smt (verit, del_insts) Pcomm \<open>is_Proj P\<close> b_sqrt_comm cblinfun_assoc_left(1) cblinfun_compose_id_left cblinfun_compose_id_right cblinfun_compose_minus_left cblinfun_compose_minus_right cblinfun_compose_zero_left diff_0_right is_Proj_algebraic is_Proj_complement is_Proj_idempotent sandwich_apply)
    also have 2: \<open>\<dots> = - (id_cblinfun - P) o\<^sub>C\<^sub>L sq\<close>
      apply (simp add: b_P_sq)
      by (smt (verit, del_insts) \<open>0 \<le> sq\<close> \<open>is_Proj P\<close> add_diff_cancel_left' cancel_comm_monoid_add_class.diff_cancel cblinfun_compose_assoc cblinfun_compose_id_right cblinfun_compose_minus_right diff_diff_eq2 is_Proj_algebraic is_Proj_complement minus_diff_eq scaleC_2)
    also have \<open>\<dots> = - sandwich (id_cblinfun - P) sq\<close>
      by (metis \<open>(id_cblinfun - P) o\<^sub>C\<^sub>L b = - (id_cblinfun - P) o\<^sub>C\<^sub>L sq\<close> calculation cblinfun_compose_uminus_left sandwich_apply)
    also have \<open>\<dots> \<le> 0\<close>
      by (simp add: \<open>0 \<le> sq\<close> sandwich_pos)
    finally have \<open>sandwich (id_cblinfun - P) b \<le> 0\<close>
      by -
    moreover from \<open>b \<ge> 0\<close> have \<open>sandwich (id_cblinfun - P) b \<ge> 0\<close>
      by (simp add: sandwich_pos)
    ultimately have \<open>sandwich (id_cblinfun - P) b = 0\<close>
      by auto
    with 1 2 have \<open>(id_cblinfun - P) o\<^sub>C\<^sub>L sq = 0\<close>
      by (metis add.inverse_neutral cblinfun_compose_uminus_left minus_diff_eq)
    with b_P_sq show \<open>b = sq\<close>
      by (metis (no_types, lifting) add.inverse_neutral add_diff_cancel_right' adj_cblinfun_compose cblinfun_compose_id_right cblinfun_compose_minus_left diff_0 diff_eq_diff_eq id_cblinfun_adjoint scaleC_2 sqrt_adj)
  qed
  
  from eq_sq have \<open>sqrt_op a = sq\<close>
    by (simp add: \<open>0 \<le> a\<close> comparable_hermitean[unfolded selfadjoint_def])
  moreover from eq_sq have \<open>b = sq\<close>
    by (simp add: assms(1) assms(2))
  ultimately show \<open>b = sqrt_op a\<close>
    by simp
qed

lemma sqrt_op_in_closure: \<open>sqrt_op a \<in> closure (cspan (range (cblinfun_power a)))\<close>
proof (cases \<open>a \<ge> 0\<close>)
  case True
  from sqrt_op_existence[OF True]
  obtain B :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> where \<open>B \<ge> 0\<close> and \<open>B o\<^sub>C\<^sub>L B = a\<close>
    and B_closure: \<open>B \<in> closure (cspan (range (cblinfun_power a)))\<close>
    by metis
  then have \<open>sqrt_op a = B\<close>
    by (metis positive_hermitianI sqrt_op_unique)
  with B_closure show ?thesis
    by simp
next
  case False
  then have \<open>sqrt_op a = 0\<close>
    by (simp add: sqrt_op_nonpos)
  also have \<open>0 \<in> closure (cspan (range (cblinfun_power a)))\<close>
    using closure_subset complex_vector.span_zero by blast
  finally show ?thesis
    by -
qed


lemma sqrt_op_commute:
  assumes \<open>A \<ge> 0\<close>
  assumes \<open>A o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L A\<close>
  shows \<open>sqrt_op A o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L sqrt_op A\<close>
  by (metis assms(1) assms(2) positive_hermitianI sqrt_op_existence sqrt_op_unique)

lemma sqrt_op_0[simp]: \<open>sqrt_op 0 = 0\<close>
  apply (rule sqrt_op_unique[symmetric])
  by auto

lemma sqrt_op_scaleC: 
  assumes \<open>c \<ge> 0\<close> and \<open>a \<ge> 0\<close>
  shows \<open>sqrt_op (c *\<^sub>C a) = sqrt c *\<^sub>C sqrt_op a\<close>
  apply (rule sqrt_op_unique[symmetric])
  using assms apply (auto simp: split_scaleC_pos_le positive_hermitianI)
  by (metis of_real_power power2_eq_square real_sqrt_pow2)

definition abs_op :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> where \<open>abs_op a = sqrt_op (a* o\<^sub>C\<^sub>L a)\<close>

lemma abs_op_pos[simp]: \<open>abs_op a \<ge> 0\<close>
  by (simp add: abs_op_def positive_cblinfun_squareI sqrt_op_pos)

lemma abs_op_0[simp]: \<open>abs_op 0 = 0\<close>
  unfolding abs_op_def by auto

lemma abs_op_idem[simp]: \<open>abs_op (abs_op a) = abs_op a\<close>
  by (metis abs_op_def abs_op_pos sqrt_op_unique)

lemma abs_op_uminus[simp]: \<open>abs_op (- a) = abs_op a\<close>
  by (simp add: abs_op_def adj_uminus bounded_cbilinear.minus_left 
      bounded_cbilinear.minus_right bounded_cbilinear_cblinfun_compose)

lemma selfbutter_pos[simp]: \<open>selfbutter x \<ge> 0\<close>
  by (metis butterfly_def double_adj positive_cblinfun_squareI)


lemma abs_op_butterfly[simp]: \<open>abs_op (butterfly x y) = (norm x / norm y) *\<^sub>R selfbutter y\<close> for x :: \<open>'a::chilbert_space\<close> and y :: \<open>'b::chilbert_space\<close>
proof (cases \<open>y=0\<close>)
  case False
  have \<open>abs_op (butterfly x y) = sqrt_op (cinner x x *\<^sub>C selfbutter y)\<close>
    unfolding abs_op_def by simp
  also have \<open>\<dots> = (norm x / norm y) *\<^sub>R selfbutter y\<close>
    apply (rule sqrt_op_unique[symmetric])
    using False by (auto intro!: scaleC_nonneg_nonneg simp: scaleR_scaleC power2_eq_square simp flip: power2_norm_eq_cinner)
  finally show ?thesis
    by -
next
  case True
  then show ?thesis
    by simp
qed

lemma abs_op_nondegenerate: \<open>a = 0\<close> if \<open>abs_op a = 0\<close>
proof -
  from that
  have \<open>sqrt_op (a* o\<^sub>C\<^sub>L a) = 0\<close>
    by (simp add: abs_op_def)
  then have \<open>0* o\<^sub>C\<^sub>L 0 = (a* o\<^sub>C\<^sub>L a)\<close>
    by (metis cblinfun_compose_zero_right positive_cblinfun_squareI sqrt_op_square)
  then show \<open>a = 0\<close>
    apply (rule_tac op_square_nondegenerate)
    by simp
qed

lemma abs_op_scaleC: \<open>abs_op (c *\<^sub>C a) = \<bar>c\<bar> *\<^sub>C abs_op a\<close>
proof -
  define aa where \<open>aa = a* o\<^sub>C\<^sub>L a\<close>
  have \<open>abs_op (c *\<^sub>C a) = sqrt_op (\<bar>c\<bar>\<^sup>2 *\<^sub>C aa)\<close>
    by (simp add: abs_op_def x_cnj_x aa_def)
  also have \<open>\<dots> = \<bar>c\<bar> *\<^sub>C sqrt_op aa\<close>
    by (smt (verit, best) aa_def abs_complex_def abs_nn cblinfun_compose_scaleC_left cblinfun_compose_scaleC_right complex_cnj_complex_of_real o_apply positive_cblinfun_squareI power2_eq_square scaleC_adj scaleC_nonneg_nonneg scaleC_scaleC sqrt_op_pos sqrt_op_square sqrt_op_unique)
  also have \<open>\<dots> = \<bar>c\<bar> *\<^sub>C abs_op a\<close>
    by (simp add: aa_def abs_op_def)
  finally show ?thesis
    by -
qed


lemma kernel_abs_op[simp]: \<open>kernel (abs_op a) = kernel a\<close>
proof (rule ccsubspace_eqI)
  fix x
  have \<open>x \<in> space_as_set (kernel (abs_op a)) \<longleftrightarrow> abs_op a x = 0\<close>
    using kernel_memberD kernel_memberI by blast
  also have \<open>\<dots> \<longleftrightarrow> abs_op a x \<bullet>\<^sub>C abs_op a x = 0\<close>
    by simp
  also have \<open>\<dots> \<longleftrightarrow> x \<bullet>\<^sub>C ((abs_op a)* o\<^sub>C\<^sub>L abs_op a) x = 0\<close>
    by (simp add: cinner_adj_right)
  also have \<open>\<dots> \<longleftrightarrow> x \<bullet>\<^sub>C (a* o\<^sub>C\<^sub>L a) x = 0\<close>
    by (simp add: abs_op_def positive_cblinfun_squareI positive_hermitianI)
  also have \<open>\<dots> \<longleftrightarrow> a x \<bullet>\<^sub>C a x = 0\<close>
    by (simp add: cinner_adj_right)
  also have \<open>\<dots> \<longleftrightarrow> a x = 0\<close>
    by simp
  also have \<open>\<dots> \<longleftrightarrow> x \<in> space_as_set (kernel a)\<close>
    using kernel_memberD kernel_memberI by auto
  finally show \<open>x \<in> space_as_set (kernel (abs_op a)) \<longleftrightarrow> x \<in> space_as_set (kernel a)\<close>
    by -
qed

definition polar_decomposition where
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, 3.9 Polar Decomposition\<close>
  \<open>polar_decomposition A = cblinfun_extension (range (abs_op A)) (\<lambda>\<psi>. A *\<^sub>V inv (abs_op A) \<psi>) o\<^sub>C\<^sub>L Proj (abs_op A *\<^sub>S top)\<close>
    for A :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner\<close>

lemma 
  fixes A :: \<open>'a :: chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b :: chilbert_space\<close>
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, 3.9 Polar Decomposition\<close>
  shows polar_decomposition_correct: \<open>polar_decomposition A o\<^sub>C\<^sub>L abs_op A = A\<close>
    and polar_decomposition_final_space: \<open>polar_decomposition A *\<^sub>S top = A *\<^sub>S top\<close> (* Should be more precise: range (polar_decomposition A) = closure (range A) *)
    and polar_decomposition_initial_space[simp]: \<open>kernel (polar_decomposition A) = kernel A\<close>
    and polar_decomposition_partial_isometry[simp]: \<open>partial_isometry (polar_decomposition A)\<close>
proof -
  have abs_A_norm: \<open>norm (abs_op A h) = norm (A h)\<close> for h
  proof -
    have \<open>complex_of_real ((norm (A h))\<^sup>2) = A h \<bullet>\<^sub>C A h\<close>
      by (simp add: cdot_square_norm)
    also have \<open>\<dots> = (A* o\<^sub>C\<^sub>L A) h \<bullet>\<^sub>C h\<close>
      by (simp add: cinner_adj_left)
    also have \<open>\<dots> = ((abs_op A)* o\<^sub>C\<^sub>L abs_op A) h \<bullet>\<^sub>C h\<close>
      by (simp add: abs_op_def positive_cblinfun_squareI positive_hermitianI)
    also have \<open>\<dots> = abs_op A h \<bullet>\<^sub>C abs_op A h\<close>
      by (simp add: cinner_adj_left)
    also have \<open>\<dots> = complex_of_real ((norm (abs_op A h))\<^sup>2)\<close>
      using cnorm_eq_square by blast
    finally show ?thesis
      by (simp add: cdot_square_norm cnorm_eq)
  qed

  define W W' P
    where \<open>W = (\<lambda>\<psi>. A *\<^sub>V inv (abs_op A) \<psi>)\<close> 
    and \<open>W' = cblinfun_extension (range (abs_op A)) W\<close>
    and \<open>P = Proj (abs_op A *\<^sub>S top)\<close>

  have pdA: \<open>polar_decomposition A = W' o\<^sub>C\<^sub>L P\<close>
    by (auto simp: polar_decomposition_def W'_def W_def P_def) 

  have AA_norm: \<open>norm (W \<psi>) = norm \<psi>\<close> if \<open>\<psi> \<in> range (abs_op A)\<close> for \<psi>
  proof -
    define h where \<open>h = inv (abs_op A) \<psi>\<close>
    from that have absA_h: \<open>abs_op A h = \<psi>\<close>
      by (simp add: f_inv_into_f h_def)
    have \<open>complex_of_real ((norm (W \<psi>))\<^sup>2) = complex_of_real ((norm (A h))\<^sup>2)\<close>
      using W_def h_def by blast 
    also have \<open>\<dots> = A h \<bullet>\<^sub>C A h\<close>
      by (simp add: cdot_square_norm)
    also have \<open>\<dots> = (A* o\<^sub>C\<^sub>L A) h \<bullet>\<^sub>C h\<close>
      by (simp add: cinner_adj_left)
    also have \<open>\<dots> = ((abs_op A)* o\<^sub>C\<^sub>L abs_op A) h \<bullet>\<^sub>C h\<close>
      by (simp add: abs_op_def positive_cblinfun_squareI positive_hermitianI)
    also have \<open>\<dots> = abs_op A h \<bullet>\<^sub>C abs_op A h\<close>
      by (simp add: cinner_adj_left)
    also have \<open>\<dots> = complex_of_real ((norm (abs_op A h))\<^sup>2)\<close>
      using cnorm_eq_square by blast
    also have \<open>\<dots> = complex_of_real ((norm \<psi>)\<^sup>2)\<close>
      using absA_h by fastforce
    finally show \<open>norm (W \<psi>) = norm \<psi>\<close>
      by (simp add: cdot_square_norm cnorm_eq)
  qed
  then have AA_norm': \<open>norm (W \<psi>) \<le> 1 * norm \<psi>\<close> if \<open>\<psi> \<in> range (abs_op A)\<close> for \<psi>
    using that by simp

  have W_absA: \<open>W (abs_op A h) = A h\<close> for h
  proof -
    have \<open>A h = A h'\<close> if \<open>abs_op A h = abs_op A h'\<close> for h h'
    proof -
      from that have \<open>norm (abs_op A (h - h')) = 0\<close>
        by (simp add: cblinfun.diff_right)
      with AA_norm have \<open>norm (A (h - h')) = 0\<close>
        by (simp add: abs_A_norm)
      then show \<open>A h = A h'\<close>
        by (simp add: cblinfun.diff_right)
    qed
    then show ?thesis
      by (metis W_def f_inv_into_f rangeI)
  qed

  have range_subspace: \<open>csubspace (range (abs_op A))\<close>
    by (auto intro!: range_is_csubspace)

  have exP: \<open>\<exists>P. is_Proj P \<and> range ((*\<^sub>V) P) = closure (range ((*\<^sub>V) (abs_op A)))\<close>
    apply (rule exI[of _ \<open>Proj (abs_op A *\<^sub>S \<top>)\<close>])
    by (metis (no_types, opaque_lifting) Proj_is_Proj Proj_range Proj_range_closed cblinfun_image.rep_eq closure_closed space_as_set_top)

  have add: \<open>W (x + y) = W x + W y\<close> if x_in: \<open>x \<in> range (abs_op A)\<close> and y_in: \<open>y \<in> range (abs_op A)\<close> for x y
  proof -
    obtain x' y' where \<open>x = abs_op A x'\<close> and \<open>y = abs_op A y'\<close>
      using x_in y_in by blast
    then show ?thesis
      by (simp flip: cblinfun.add_right add: W_absA)
  qed

  have scale: \<open>W (c *\<^sub>C x) = c *\<^sub>C W x\<close> if x_in: \<open>x \<in> range (abs_op A)\<close> for c x
  proof -
    obtain x' where \<open>x = abs_op A x'\<close>
      using x_in by blast
    then show ?thesis
      by (simp flip: cblinfun.scaleC_right add: W_absA)
  qed

  have \<open>cblinfun_extension_exists (range (abs_op A)) W\<close>
    using range_subspace exP add scale AA_norm'
    by (rule cblinfun_extension_exists_proj)

  then have W'_apply: \<open>W' *\<^sub>V \<psi> = W \<psi>\<close> if \<open>\<psi> \<in> range (abs_op A)\<close> for \<psi>
    by (simp add: W'_def cblinfun_extension_apply that)

   have \<open>norm (W' \<psi>) - norm \<psi> = 0\<close> if \<open>\<psi> \<in> range (abs_op A)\<close> for \<psi>
    by (simp add: W'_apply AA_norm that)
  then have \<open>norm (W' \<psi>) - norm \<psi> = 0\<close> if \<open>\<psi> \<in> closure (range (abs_op A))\<close> for \<psi>
    apply (rule_tac continuous_constant_on_closure[where S=\<open>range (abs_op A)\<close>])
    using that by (auto intro!: continuous_at_imp_continuous_on)
  then have norm_W': \<open>norm (W' \<psi>) = norm \<psi>\<close> if \<open>\<psi> \<in> space_as_set (abs_op A *\<^sub>S top)\<close> for \<psi>
    using cblinfun_image.rep_eq that by force

  show correct: \<open>polar_decomposition A o\<^sub>C\<^sub>L abs_op A = A\<close>
  proof (rule cblinfun_eqI)
    fix \<psi> :: 'a
    have \<open>(polar_decomposition A o\<^sub>C\<^sub>L abs_op A) *\<^sub>V \<psi> = W (P (abs_op A \<psi>))\<close>
      by (simp add: W'_apply P_def pdA Proj_fixes_image) 
    also have \<open>\<dots> = W (abs_op A \<psi>)\<close>
      by (auto simp: P_def Proj_fixes_image)
    also have \<open>\<dots> = A \<psi>\<close>
      by (simp add: W_absA)
(*     also have \<open>\<dots> = A (inv (abs_op A) (abs_op A \<psi>))\<close>
      using W_def by fastforce
    also have \<open>\<dots> = A \<psi>\<close>
       *)
    finally show \<open>(polar_decomposition A o\<^sub>C\<^sub>L abs_op A) *\<^sub>V \<psi> = A *\<^sub>V \<psi>\<close>
      by -
  qed

  show \<open>polar_decomposition A *\<^sub>S top = A *\<^sub>S top\<close>
  proof (rule antisym)
    have *: \<open>A *\<^sub>S top = polar_decomposition A *\<^sub>S abs_op A *\<^sub>S top\<close>
      by (simp add: cblinfun_assoc_left(2) correct)
    also have \<open>\<dots> \<le> polar_decomposition A *\<^sub>S top\<close>
      by (simp add: cblinfun_image_mono)
    finally show \<open>A *\<^sub>S top \<le> polar_decomposition A *\<^sub>S top\<close>
      by -

    have \<open>W' \<psi> \<in> range A\<close> if \<open>\<psi> \<in> range (abs_op A)\<close> for \<psi>
      using W'_apply W_def that by blast
    then have \<open>W' \<psi> \<in> closure (range A)\<close> if \<open>\<psi> \<in> closure (range (abs_op A))\<close> for \<psi>
      using * 
      by (metis (mono_tags, lifting) P_def Proj_range Proj_fixes_image cblinfun_apply_cblinfun_compose cblinfun_apply_in_image cblinfun_compose_image cblinfun_image.rep_eq pdA that top_ccsubspace.rep_eq)
    then have \<open>W' \<psi> \<in> space_as_set (A *\<^sub>S top)\<close> if \<open>\<psi> \<in> space_as_set (abs_op A *\<^sub>S top)\<close> for \<psi>
      by (metis cblinfun_image.rep_eq that top_ccsubspace.rep_eq)
    then have \<open>polar_decomposition A \<psi> \<in> space_as_set (A *\<^sub>S top)\<close> for \<psi>
      by (metis P_def Proj_range cblinfun_apply_cblinfun_compose cblinfun_apply_in_image pdA)
    then show \<open>polar_decomposition A *\<^sub>S top \<le> A *\<^sub>S top\<close>
      using * 
      by (metis (no_types, lifting) Proj_idempotent Proj_range cblinfun_compose_image dual_order.eq_iff polar_decomposition_def)
  qed

  show \<open>partial_isometry (polar_decomposition A)\<close>
    apply (rule partial_isometryI'[where V=\<open>abs_op A *\<^sub>S top\<close>])
    by (auto simp add: P_def Proj_fixes_image norm_W' pdA kernel_memberD)

  have \<open>kernel (polar_decomposition A) = - (abs_op A *\<^sub>S top)\<close>
    apply (rule partial_isometry_initial[where V=\<open>abs_op A *\<^sub>S top\<close>])
    by (auto simp add: P_def Proj_fixes_image norm_W' pdA kernel_memberD)
  also have \<open>\<dots> = kernel (abs_op A)\<close>
    by (metis abs_op_pos kernel_compl_adj_range positive_hermitianI)
  also have \<open>\<dots> = kernel A\<close>
    by (simp add: kernel_abs_op)
  finally show \<open>kernel (polar_decomposition A) = kernel A\<close>
    by -
qed

lemma polar_decomposition_correct': \<open>(polar_decomposition A)* o\<^sub>C\<^sub>L A = abs_op A\<close>
  for A :: \<open>'a :: chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b :: chilbert_space\<close>
proof -
  have \<open>polar_decomposition A* o\<^sub>C\<^sub>L A = (polar_decomposition A* o\<^sub>C\<^sub>L polar_decomposition A) o\<^sub>C\<^sub>L abs_op A\<close>
    by (simp add: cblinfun_compose_assoc polar_decomposition_correct)
  also have \<open>\<dots> = Proj (- kernel (polar_decomposition A)) o\<^sub>C\<^sub>L abs_op A\<close>
    by (simp add: partial_isometry_adj_a_o_a polar_decomposition_partial_isometry)
  also have \<open>\<dots> = Proj (- kernel A) o\<^sub>C\<^sub>L abs_op A\<close>
    by (simp add: polar_decomposition_initial_space)
  also have \<open>\<dots> = Proj (- kernel (abs_op A)) o\<^sub>C\<^sub>L abs_op A\<close>
    by simp
  also have \<open>\<dots> = Proj (abs_op A *\<^sub>S top) o\<^sub>C\<^sub>L abs_op A\<close>
    by (metis abs_op_pos kernel_compl_adj_range ortho_involution positive_hermitianI)
  also have \<open>\<dots> = abs_op A\<close>
    by (simp add: Proj_fixes_image cblinfun_eqI)
  finally show ?thesis
    by -
qed

lemma abs_op_adj: \<open>abs_op (a*) = sandwich (polar_decomposition a) (abs_op a)\<close>
proof -
  have pos: \<open>sandwich (polar_decomposition a) (abs_op a) \<ge> 0\<close>
    by (simp add: sandwich_pos)
  have \<open>(sandwich (polar_decomposition a) (abs_op a))* o\<^sub>C\<^sub>L (sandwich (polar_decomposition a) (abs_op a))
     = polar_decomposition a o\<^sub>C\<^sub>L (abs_op a)* o\<^sub>C\<^sub>L abs_op a o\<^sub>C\<^sub>L (polar_decomposition a)*\<close>
    apply (simp add: sandwich_apply)
    by (metis (no_types, lifting) cblinfun_assoc_left(1) polar_decomposition_correct polar_decomposition_correct')
  also have \<open>\<dots> = a o\<^sub>C\<^sub>L a*\<close>
    by (metis abs_op_pos adj_cblinfun_compose cblinfun_assoc_left(1) polar_decomposition_correct positive_hermitianI)
  finally have \<open>sandwich (polar_decomposition a) (abs_op a) = sqrt_op (a o\<^sub>C\<^sub>L a*)\<close>
    using pos by (simp add: sqrt_op_unique)
  also have \<open>\<dots> = abs_op (a*)\<close>
    by (simp add: abs_op_def)
  finally show ?thesis
    by simp
qed

lemma abs_opI: 
  assumes \<open>a* o\<^sub>C\<^sub>L a = b* o\<^sub>C\<^sub>L b\<close>
  assumes \<open>a \<ge> 0\<close>
  shows \<open>a = abs_op b\<close>
  by (simp add: abs_op_def assms(1) assms(2) sqrt_op_unique)

lemma abs_op_id_on_pos: \<open>a \<ge> 0 \<Longrightarrow> abs_op a = a\<close>
  using abs_opI by force

lemma norm_abs_op[simp]: \<open>norm (abs_op a) = norm a\<close> 
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
proof -
  have \<open>(norm (abs_op a))\<^sup>2 = norm (abs_op a* o\<^sub>C\<^sub>L abs_op a)\<close>
    by simp
  also have \<open>\<dots> = norm (a* o\<^sub>C\<^sub>L a)\<close>
    by (simp add: abs_op_def positive_cblinfun_squareI positive_hermitianI)
  also have \<open>\<dots> = (norm a)\<^sup>2\<close>
    by simp
  finally show ?thesis
    by simp
qed


(* TODO Potentially move to Complex_Bounded_Linear_Functions and replace partial_isometry_square_proj by this.
        But the proof uses facts from this theory. *)
lemma partial_isometry_iff_square_proj:
  \<comment> \<open>@{cite conway2013course}, Exercise VIII.3.15\<close>
  fixes A :: \<open>'a :: chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b :: chilbert_space\<close>
  shows \<open>partial_isometry A \<longleftrightarrow> is_Proj (A* o\<^sub>C\<^sub>L A)\<close>
proof (rule iffI)
  show \<open>is_Proj (A* o\<^sub>C\<^sub>L A)\<close> if \<open>partial_isometry A\<close>
    by (simp add: partial_isometry_square_proj that)
next
  show \<open>partial_isometry A\<close> if \<open>is_Proj (A* o\<^sub>C\<^sub>L A)\<close>
  proof (rule partial_isometryI)
    fix h
    from that have \<open>norm (A* o\<^sub>C\<^sub>L A) \<le> 1\<close>
      using norm_is_Proj by blast
    then have normA: \<open>norm A \<le> 1\<close> and normAadj: \<open>norm (A*) \<le> 1\<close>
      by (simp_all add: norm_AadjA abs_square_le_1)
    assume \<open>h \<in> space_as_set (- kernel A)\<close>
    also have \<open>\<dots> = space_as_set (- kernel (A* o\<^sub>C\<^sub>L A))\<close>
      by (metis (no_types, lifting) abs_opI is_Proj_algebraic kernel_abs_op positive_cblinfun_squareI that)
    also have \<open>\<dots> = space_as_set ((A* o\<^sub>C\<^sub>L A) *\<^sub>S \<top>)\<close>
      by (simp add: kernel_compl_adj_range)
    finally have \<open>A* *\<^sub>V A *\<^sub>V h = h\<close>
      by (metis Proj_fixes_image Proj_on_own_range that cblinfun_apply_cblinfun_compose)
    then have \<open>norm h = norm (A* *\<^sub>V A *\<^sub>V h)\<close>
      by simp
    also have \<open>\<dots> \<le> norm (A *\<^sub>V h)\<close>
      by (smt (verit) normAadj mult_left_le_one_le norm_cblinfun norm_ge_zero)
    also have \<open>\<dots> \<le> norm h\<close>
      by (smt (verit) normA mult_left_le_one_le norm_cblinfun norm_ge_zero)
    ultimately show \<open>norm (A *\<^sub>V h) = norm h\<close>
      by simp
  qed
qed

lemma abs_op_square: \<open>(abs_op A)* o\<^sub>C\<^sub>L abs_op A = A* o\<^sub>C\<^sub>L A\<close>
  by (simp add: abs_op_def positive_cblinfun_squareI positive_hermitianI)

lemma polar_decomposition_0[simp]: \<open>polar_decomposition 0 = (0 :: 'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space)\<close>
proof -
  have \<open>polar_decomposition (0 :: 'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) *\<^sub>S \<top> = 0 *\<^sub>S \<top>\<close>
    by (simp add: polar_decomposition_final_space)
  then show ?thesis
    by simp
qed

lemma polar_decomposition_unique:
  fixes A :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes ker: \<open>kernel X = kernel A\<close>
  assumes comp: \<open>X o\<^sub>C\<^sub>L abs_op A = A\<close>
  shows \<open>X = polar_decomposition A\<close>
proof -
  have \<open>X \<psi> = polar_decomposition A \<psi>\<close> if \<open>\<psi> \<in> space_as_set (kernel A)\<close> for \<psi>
  proof -
    have \<open>\<psi> \<in> space_as_set (kernel X)\<close>
      by (simp add: ker that)
    then have \<open>X \<psi> = 0\<close>
      by (simp add: kernel.rep_eq)
    moreover
    have \<open>\<psi> \<in> space_as_set (kernel (polar_decomposition A))\<close>
      by (simp add: polar_decomposition_initial_space that)
    then have \<open>polar_decomposition A \<psi> = 0\<close>
      by (simp add: kernel.rep_eq del: polar_decomposition_initial_space)
    ultimately show ?thesis
      by simp
  qed
  then have 1: \<open>X o\<^sub>C\<^sub>L Proj (kernel A) = polar_decomposition A o\<^sub>C\<^sub>L Proj (kernel A)\<close>
    by (metis assms(1) cblinfun_compose_Proj_kernel polar_decomposition_initial_space)
  have *: \<open>abs_op A *\<^sub>S \<top> = - kernel A\<close>
    by (metis (mono_tags, opaque_lifting) abs_op_pos kernel_abs_op kernel_compl_adj_range ortho_involution positive_hermitianI)
  
  have \<open>X o\<^sub>C\<^sub>L abs_op A = polar_decomposition A o\<^sub>C\<^sub>L abs_op A\<close>
    by (simp add: comp polar_decomposition_correct)
  then have \<open>X \<psi> = polar_decomposition A \<psi>\<close> if \<open>\<psi> \<in> space_as_set (abs_op A *\<^sub>S \<top>)\<close> for \<psi>
    by (simp add: cblinfun_same_on_image that)
  then have 2: \<open>X o\<^sub>C\<^sub>L Proj (- kernel A) = polar_decomposition A o\<^sub>C\<^sub>L Proj (- kernel A)\<close>
    using *
    by (metis (no_types, opaque_lifting) Proj_idempotent cblinfun_eqI lift_cblinfun_comp(4) norm_Proj_apply)
  from 1 2 have \<open>X o\<^sub>C\<^sub>L Proj (- kernel A) + X o\<^sub>C\<^sub>L Proj (kernel A)
           = polar_decomposition A o\<^sub>C\<^sub>L Proj (- kernel A) + polar_decomposition A o\<^sub>C\<^sub>L Proj (kernel A)\<close>
    by simp
  then show ?thesis
    by (simp add: Proj_ortho_compl flip: cblinfun_compose_add_right)
qed

lemma norm_cblinfun_mono:
\<comment> \<open>Would logically belong in \<^theory>\<open>Complex_Bounded_Operators.Complex_Bounded_Linear_Function\<close>
      but uses \<^const>\<open>sqrt_op\<close> from this theory in the proof.\<close>
  fixes A B :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>A \<ge> 0\<close>
  assumes \<open>A \<le> B\<close>
  shows \<open>norm A \<le> norm B\<close>
proof -
  have \<open>B \<ge> 0\<close>
    using assms by force
  have sqrtA: \<open>(sqrt_op A)* o\<^sub>C\<^sub>L sqrt_op A = A\<close>
    by (simp add: \<open>A \<ge> 0\<close> positive_hermitianI)
  have sqrtB: \<open>(sqrt_op B)* o\<^sub>C\<^sub>L sqrt_op B = B\<close>
    by (simp add: \<open>B \<ge> 0\<close> positive_hermitianI)
  have \<open>norm (sqrt_op A \<psi>) \<le> norm (sqrt_op B \<psi>)\<close> for \<psi>
    apply (auto intro!: cnorm_le[THEN iffD2]
        simp: sqrtA sqrtB
        simp flip: cinner_adj_right cblinfun_apply_cblinfun_compose)
    using assms less_eq_cblinfun_def by auto
  then have \<open>norm (sqrt_op A) \<le> norm (sqrt_op B)\<close>
    by (meson dual_order.trans norm_cblinfun norm_cblinfun_bound norm_ge_zero)
  moreover have \<open>norm A = (norm (sqrt_op A))\<^sup>2\<close>
    by (metis norm_AadjA sqrtA)
  moreover have \<open>norm B = (norm (sqrt_op B))\<^sup>2\<close>
    by (metis norm_AadjA sqrtB)
  ultimately show \<open>norm A \<le> norm B\<close>
    by force
qed

lemma sandwich_mono: \<open>sandwich A B \<le> sandwich A C\<close> if \<open>B \<le> C\<close>
  by (metis cblinfun.real.diff_right diff_ge_0_iff_ge sandwich_pos that)

lemma sums_pos_cblinfun:
  fixes f :: "nat \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes \<open>f sums a\<close>
  assumes \<open>\<And>n. f n \<ge> 0\<close>
  shows "a \<ge> 0"
  apply (rule sums_mono_cblinfun[where f=\<open>\<lambda>_. 0\<close> and g=f])
  using assms by auto

lemma has_sum_mono_cblinfun:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes "(f has_sum x) A" and "(g has_sum y) A"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows "x \<le> y"
  using assms has_sum_mono_neutral_cblinfun by force

lemma infsum_mono_cblinfun:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes "f summable_on A" and "g summable_on A"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows "infsum f A \<le> infsum g A"
  by (meson assms has_sum_infsum has_sum_mono_cblinfun)

lemma suminf_mono_cblinfun:
  fixes f :: "nat \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes "summable f" and "summable g"
  assumes \<open>\<And>x. f x \<le> g x\<close>
  shows "suminf f \<le> suminf g"
  using assms sums_mono_cblinfun by blast 

lemma suminf_pos_cblinfun:
  fixes f :: "nat \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes \<open>summable f\<close>
  assumes \<open>\<And>x. f x \<ge> 0\<close>
  shows "suminf f \<ge> 0"
  using assms sums_mono_cblinfun by blast 


lemma infsum_mono_neutral_cblinfun:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes "f summable_on A" and "g summable_on B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "infsum f A \<le> infsum g B"
  by (smt (verit, del_insts) assms(1) assms(2) assms(3) assms(4) assms(5) has_sum_infsum has_sum_mono_neutral_cblinfun)

lemma abs_op_geq: \<open>abs_op a \<ge> a\<close> if \<open>selfadjoint a\<close>
proof -
  define A P where \<open>A = abs_op a\<close> and \<open>P = Proj (kernel (A + a))\<close>
  from that have [simp]: \<open>a* = a\<close>
    by (simp add: selfadjoint_def)
  have [simp]: \<open>A \<ge> 0\<close>
    by (simp add: A_def)
  then have [simp]: \<open>A* = A\<close>
    using positive_hermitianI by fastforce
  have aa_AA: \<open>a o\<^sub>C\<^sub>L a = A o\<^sub>C\<^sub>L A\<close>
    by (metis A_def \<open>A* = A\<close> abs_op_square that selfadjoint_def)
  have [simp]: \<open>P* = P\<close>
    by (simp add: P_def adj_Proj)
  have Aa_aA: \<open>A o\<^sub>C\<^sub>L a = a o\<^sub>C\<^sub>L A\<close>
    by (metis (full_types) A_def lift_cblinfun_comp(2) abs_op_def positive_cblinfun_squareI sqrt_op_commute that selfadjoint_def)

  have \<open>(A-a) \<psi> \<bullet>\<^sub>C (A+a) \<phi> = 0\<close> for \<phi> \<psi>
    by (simp add: adj_minus that \<open>A* = A\<close> aa_AA Aa_aA cblinfun_compose_add_right cblinfun_compose_minus_left
        flip: cinner_adj_right cblinfun_apply_cblinfun_compose)
  then have \<open>(A-a) \<psi> \<in> space_as_set (kernel (A+a))\<close> for \<psi>
    by (metis \<open>A* = A\<close> adj_plus call_zero_iff cinner_adj_left kernel_memberI that selfadjoint_def)
  then have P_fix: \<open>P o\<^sub>C\<^sub>L (A-a) = (A-a)\<close>
    by (simp add: P_def Proj_fixes_image cblinfun_eqI)
  then have \<open>P o\<^sub>C\<^sub>L (A-a) o\<^sub>C\<^sub>L P = (A-a) o\<^sub>C\<^sub>L P\<close>
    by simp
  also have \<open>\<dots> = (P o\<^sub>C\<^sub>L (A-a))*\<close>
    by (simp add: adj_minus \<open>A* = A\<close> that \<open>P* = P\<close>)
  also have \<open>\<dots> = (A-a)*\<close>
    by (simp add: P_fix)
  also have \<open>\<dots> = A-a\<close>
    by (simp add: \<open>A* = A\<close> that adj_minus)
  finally have 1: \<open>P o\<^sub>C\<^sub>L (A - a) o\<^sub>C\<^sub>L P = A - a\<close>
    by -
  have 2: \<open>P o\<^sub>C\<^sub>L (A + a) o\<^sub>C\<^sub>L P = 0\<close>
    by (simp add: P_def cblinfun_compose_assoc)
  have \<open>A - a = P o\<^sub>C\<^sub>L (A - a) o\<^sub>C\<^sub>L P + P o\<^sub>C\<^sub>L (A + a) o\<^sub>C\<^sub>L P\<close>
    by (simp add: 1 2)
  also have \<open>\<dots> = sandwich P (2 *\<^sub>C A)\<close>
    by (simp add: sandwich_apply cblinfun_compose_minus_left cblinfun_compose_minus_right
        cblinfun_compose_add_left cblinfun_compose_add_right scaleC_2 \<open>P* = P\<close>) 
  also have \<open>\<dots> \<ge> 0\<close>
    by (auto intro!: sandwich_pos scaleC_nonneg_nonneg simp: less_eq_complex_def)
  finally show \<open>A \<ge> a\<close>
    by auto
qed

lemma abs_op_geq_neq: \<open>abs_op a \<ge> - a\<close> if \<open>selfadjoint a\<close>
  by (metis abs_op_geq abs_op_uminus adj_uminus that selfadjoint_def)

lemma infsum_nonneg_cblinfun:
  fixes f :: "'a \<Rightarrow> 'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b"
  assumes "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsum f M \<ge> 0"
  apply (cases \<open>f summable_on M\<close>)
   apply (subst infsum_0_simp[symmetric])
   apply (rule infsum_mono_cblinfun)
  using assms by (auto simp: infsum_not_exists)

lemma adj_abs_op[simp]: \<open>(abs_op a)* = abs_op a\<close>
  by (simp add: positive_hermitianI) 

lemma cblinfun_image_less_eqI:
  fixes A :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>\<And>h. h \<in> space_as_set S \<Longrightarrow> A h \<in> space_as_set T\<close>
  shows \<open>A *\<^sub>S S \<le> T\<close>
proof -
  from assms have \<open>A ` space_as_set S \<subseteq> space_as_set T\<close>
    by blast
  then have \<open>closure (A ` space_as_set S) \<subseteq> closure (space_as_set T)\<close>
    by (rule closure_mono)
  also have \<open>\<dots> = space_as_set T\<close>
    by force
  finally show ?thesis
    apply (transfer fixing: A)
    by (simp add: cblinfun_image.rep_eq ccsubspace_leI)
qed



lemma abs_op_plus_orthogonal:
  assumes \<open>a* o\<^sub>C\<^sub>L b = 0\<close> and \<open>a o\<^sub>C\<^sub>L b* = 0\<close>
  shows \<open>abs_op (a + b) = abs_op a + abs_op b\<close>
proof (rule abs_opI[symmetric])
  have ba: \<open>b* o\<^sub>C\<^sub>L a = 0\<close>
    apply (rule cblinfun_eqI, rule cinner_extensionality)
    apply (simp add: cinner_adj_right flip: cinner_adj_left)
    by (simp add: assms simp_a_oCL_b') 
  have abs_ab: \<open>abs_op a o\<^sub>C\<^sub>L abs_op b = 0\<close>
  proof -
    have \<open>abs_op b *\<^sub>S \<top> = - kernel (abs_op b)\<close>
      by (simp add: kernel_compl_adj_range positive_hermitianI) 
    also have \<open>\<dots> = - kernel b\<close>
      by simp
    also have \<open>\<dots> = (b*) *\<^sub>S \<top>\<close>
      by (simp add: kernel_compl_adj_range) 
    also have \<open>\<dots> \<le> kernel a\<close>
      apply (auto intro!: cblinfun_image_less_eqI kernel_memberI simp: )
      by (simp add: assms flip: cblinfun_apply_cblinfun_compose)
    also have \<open>\<dots> = kernel (abs_op a)\<close>
      by simp 
    finally show \<open>abs_op a o\<^sub>C\<^sub>L abs_op b = 0\<close>
      by (metis Proj_compose_cancelI cblinfun_compose_Proj_kernel cblinfun_compose_assoc cblinfun_compose_zero_left) 
  qed
  then have abs_ba: \<open>abs_op b o\<^sub>C\<^sub>L abs_op a = 0\<close>
    by (metis abs_op_pos adj_0 adj_cblinfun_compose positive_hermitianI) 
  have \<open>(a + b)* o\<^sub>C\<^sub>L (a + b) = (a*) o\<^sub>C\<^sub>L a + (b*) o\<^sub>C\<^sub>L b\<close>
    by (simp add: cblinfun_compose_add_left cblinfun_compose_add_right adj_plus assms ba)
  also have \<open>\<dots> = (abs_op a + abs_op b)* o\<^sub>C\<^sub>L (abs_op a + abs_op b)\<close>
    by (simp add: cblinfun_compose_add_left cblinfun_compose_add_right adj_plus abs_ab abs_ba flip: abs_op_square)
  finally show \<open>(abs_op a + abs_op b)* o\<^sub>C\<^sub>L (abs_op a + abs_op b) = (a + b)* o\<^sub>C\<^sub>L (a + b)\<close>
    by simp
  show \<open>0 \<le> abs_op a + abs_op b\<close>
    by simp 
qed


definition pos_op :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> where
  \<open>pos_op a = (abs_op a + a) /\<^sub>R 2\<close>

definition neg_op :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> where
  \<open>neg_op a = (abs_op a - a) /\<^sub>R 2\<close>

lemma pos_op_pos: 
  assumes \<open>selfadjoint a\<close>
  shows \<open>pos_op a \<ge> 0\<close>
  using abs_op_geq_neq[OF assms]
  apply (simp add: pos_op_def)
  by (smt (verit, best) add_le_cancel_right more_arith_simps(3) scaleR_nonneg_nonneg zero_le_divide_iff) 

lemma neg_op_pos:
  assumes \<open>selfadjoint a\<close>
  shows \<open>neg_op a \<ge> 0\<close>
  using abs_op_geq[OF assms]
  by (simp add: neg_op_def scaleR_nonneg_nonneg)

lemma pos_op_neg_op_ortho:
  assumes \<open>selfadjoint a\<close>
  shows \<open>pos_op a o\<^sub>C\<^sub>L neg_op a = 0\<close>
  apply (auto intro!: simp: pos_op_def neg_op_def cblinfun_compose_add_left cblinfun_compose_minus_right)
  by (metis (no_types, opaque_lifting) Groups.add_ac(2) abs_op_def abs_op_pos abs_op_square assms cblinfun_assoc_left(1) positive_cblinfun_squareI positive_hermitianI selfadjoint_def sqrt_op_commute) 


lemma pos_op_plus_neg_op: \<open>pos_op a + neg_op a = abs_op a\<close>
  by (simp add: pos_op_def neg_op_def scaleR_diff_right scaleR_add_right pth_8)

lemma pos_op_minus_neg_op: \<open>pos_op a - neg_op a = a\<close>
  by (simp add: pos_op_def neg_op_def scaleR_diff_right scaleR_add_right pth_8)

lemma pos_op_neg_op_unique:
  assumes bca: \<open>b - c = a\<close>
  assumes \<open>b \<ge> 0\<close> and \<open>c \<ge> 0\<close>
  assumes bc: \<open>b o\<^sub>C\<^sub>L c = 0\<close>
  shows \<open>b = pos_op a\<close> and \<open>c = neg_op a\<close>
proof -
  from bc have cb: \<open>c o\<^sub>C\<^sub>L b = 0\<close>
    by (metis adj_0 adj_cblinfun_compose assms(2) assms(3) positive_hermitianI) 
  from \<open>b \<ge> 0\<close> have [simp]: \<open>b* = b\<close>
    by (simp add: positive_hermitianI) 
  from \<open>c \<ge> 0\<close> have [simp]: \<open>c* = c\<close>
    by (simp add: positive_hermitianI) 
  have bc_abs: \<open>b + c = abs_op a\<close>
  proof -
    have \<open>(b + c)* o\<^sub>C\<^sub>L (b + c) = b o\<^sub>C\<^sub>L b + c o\<^sub>C\<^sub>L c\<close>
      by (simp add: cblinfun_compose_add_left cblinfun_compose_add_right bc cb adj_plus)
    also have \<open>\<dots> = (b - c)* o\<^sub>C\<^sub>L (b - c)\<close>
      by (simp add: cblinfun_compose_minus_left cblinfun_compose_minus_right bc cb adj_minus)
    also from bca have \<open>\<dots> = a* o\<^sub>C\<^sub>L a\<close>
      by blast
    finally show ?thesis
      apply (rule abs_opI)
      by (simp add: \<open>b \<ge> 0\<close> \<open>c \<ge> 0\<close>) 
  qed
  from arg_cong2[OF bca bc_abs, of plus]
    arg_cong2[OF pos_op_minus_neg_op[of a] pos_op_plus_neg_op[of a], of plus, symmetric]
  show \<open>b = pos_op a\<close>
    by (simp flip: scaleR_2)
  from arg_cong2[OF bc_abs bca, of minus]
    arg_cong2[OF pos_op_plus_neg_op[of a] pos_op_minus_neg_op[of a], of minus, symmetric]
  show \<open>c = neg_op a\<close>
    by (simp flip: scaleR_2)
qed


lemma pos_imp_selfadjoint: \<open>a \<ge> 0 \<Longrightarrow> selfadjoint a\<close>
  using positive_hermitianI selfadjoint_def by blast

lemma abs_op_one_dim: \<open>abs_op x = one_dim_iso (abs (one_dim_iso x :: complex))\<close>
  by (metis (mono_tags, lifting) abs_opI abs_op_scaleC of_complex_def one_cblinfun_adj one_comp_one_cblinfun one_dim_iso_is_of_complex one_dim_iso_of_one one_dim_iso_of_zero one_dim_loewner_order one_dim_scaleC_1 zero_less_one_class.zero_le_one)


lemma pos_selfadjoint: \<open>selfadjoint a\<close> if \<open>a \<ge> 0\<close>
  using adj_0 comparable_hermitean selfadjoint_def that by blast

lemma one_dim_loewner_order_strict: \<open>A > B \<longleftrightarrow> one_dim_iso A > (one_dim_iso B :: complex)\<close> for A B :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a::{chilbert_space, one_dim}\<close>
  by (auto simp: less_cblinfun_def one_dim_loewner_order)

lemma one_dim_cblinfun_zero_le_one: \<open>0 < (1 :: 'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close>
  by (simp add: one_dim_loewner_order_strict)
lemma one_dim_cblinfun_one_pos: \<open>0 \<le> (1 :: 'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close>
  by (simp add: one_dim_loewner_order)

lemma Proj_pos[iff]: \<open>Proj S \<ge> 0\<close>
  apply (rule positive_cblinfun_squareI[where B=\<open>Proj S\<close>])
  by (simp add: adj_Proj)

lemma abs_op_Proj[simp]: \<open>abs_op (Proj S) = Proj S\<close>
  by (simp add: abs_op_id_on_pos)



lemma diagonal_operator_pos:
  assumes \<open>\<And>x. f x \<ge> 0\<close>
  shows \<open>diagonal_operator f \<ge> 0\<close>
proof (cases \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>)
  case True
  have [simp]: \<open>csqrt (f x) = sqrt (cmod (f x))\<close> for x
    by (simp add: Extra_Ordered_Fields.complex_of_real_cmod assms abs_pos of_real_sqrt)
  have bdd: \<open>bdd_above (range (\<lambda>x. sqrt (cmod (f x))))\<close>
  proof -
    from True obtain B where \<open>cmod (f x) \<le> B\<close> for x
      by (auto simp: bdd_above_def)
    then show ?thesis
      by (auto intro!: bdd_aboveI[where M=\<open>sqrt B\<close>] simp: )
  qed
  show ?thesis
    apply (rule positive_cblinfun_squareI[where B=\<open>diagonal_operator (\<lambda>x. csqrt (f x))\<close>])
    by (simp add: assms diagonal_operator_adj diagonal_operator_comp bdd complex_of_real_cmod abs_pos
        flip: of_real_mult)
next
  case False
  then show ?thesis
    by (simp add: diagonal_operator_invalid)
qed

lemma abs_op_diagonal_operator: 
  \<open>abs_op (diagonal_operator f) = diagonal_operator (\<lambda>x. abs (f x))\<close>
proof (cases \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>)
  case True
  show ?thesis
    apply (rule abs_opI[symmetric])
    by (auto intro!: diagonal_operator_pos abs_nn simp: True diagonal_operator_adj diagonal_operator_comp cnj_x_x)
next
  case False
  then show ?thesis
    by (simp add: diagonal_operator_invalid)
qed



end
