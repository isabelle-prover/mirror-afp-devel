theory MobiusGyroVectorSpace
imports Main MobiusGyroGroup  GyroVectorSpace  Gyrotrigonometry GammaFactor HyperbolicFunctions
begin

(* --------------------------------------------------------- *)

lemma norms:
  shows "{x. \<exists>a. x = cmod (to_complex a)} \<union> {x. \<exists>a. x = - cmod (to_complex a)} = {x. \<bar>x\<bar> < 1}"
proof-
  { 
    fix x :: real
    assume "\<bar>x\<bar> < 1" 
    then have "cmod (Complex x 0) < 1"
      by (simp add: complex_norm)
    then have "to_complex (PoincareDisc.of_complex (Complex x 0)) = x"
      by (simp add: complex_of_real_def of_complex_inverse)
    then have "\<exists>a. x = cmod (to_complex a) \<or> (\<exists> a. x = - cmod (to_complex a))"
      by (metis abs_eq_iff' norm_of_real)
  }
  moreover
  have "\<And> a. cmod (to_complex a) < 1"
    using to_complex by force
  ultimately show ?thesis
    by auto
qed

global_interpretation Mobius_gyrocarrier': gyrocarrier'
  where to_carrier = to_complex 
rewrites
  "Mobius_gyrocarrier'.gyroinner = inner_p" and
  "Mobius_gyrocarrier'.gyronorm = norm_p" and
  "Mobius_gyrocarrier'.carrier = {z. cmod z < 1}" and
  "Mobius_gyrocarrier'.norms = {x. abs x < 1}"
defines
  of_complex = "gyrocarrier'.of_carrier to_complex"
proof-
  show *: "gyrocarrier' to_complex"
  proof
    show "inj to_complex"
      by (simp add: inj_on_def to_complex_inject)
  next
    show "to_complex 0\<^sub>g = 0"
      by (simp add: gyrozero_PoincareDisc_def ozero_m'_def ozero_m.rep_eq)
  qed

  show "gyrocarrier'.gyroinner to_complex = (\<cdot>)"
    apply rule
    apply rule
    unfolding gyrocarrier'.gyroinner_def[OF *]
    apply transfer
    by (simp add: inner_complex_def)

  show "gyrocarrier'.gyronorm to_complex = norm_p"
    apply rule
    unfolding gyrocarrier'.gyronorm_def[OF *]
    apply transfer
    by simp

  show "gyrocarrier'.carrier to_complex = {z. cmod z < 1}"
    unfolding gyrocarrier'.carrier_def[OF *]
    using type_definition.Rep_range type_definition_PoincareDisc
    by blast

  show "gyrocarrier'.norms to_complex = {x. \<bar>x\<bar> < 1}"
    using norms
    unfolding gyrocarrier'.norms_def[OF *]
    unfolding gyrocarrier'.gyronorm_def[OF *]
    by auto
qed

lemma Mobius_gyrocarrier'_norms [simp]: 
  shows "gyrocarrier'.norms to_complex = {x. abs x < 1}"
  using Mobius_gyrocarrier'.norms_def
  unfolding gyrocarrier'.norms_def[OF Mobius_gyrocarrier'.gyrocarrier'_axioms]
            gyrocarrier'.gyronorm_def[OF Mobius_gyrocarrier'.gyrocarrier'_axioms]
  using norm_p.rep_eq 
  by presburger

lemma Mobius_gyrocarrier'_carrier [simp]: 
  shows "gyrocarrier'.carrier to_complex = {z. cmod z < 1}"
  unfolding gyrocarrier'.carrier_def[OF Mobius_gyrocarrier'.gyrocarrier'_axioms]
  using type_definition.Rep_range type_definition_PoincareDisc
  by blast

(* --------------------------------------------------------- *)

lemma moebius_gyroauto:
  shows "gyr\<^sub>m u v a \<cdot> gyr\<^sub>m u v b = a \<cdot> b"
proof-
  have "gyr\<^sub>m u v a \<cdot> gyr\<^sub>m u v b = Re((cnj (to_complex (gyr\<^sub>m u v a))) * (to_complex (gyr\<^sub>m u v b)))"
    using inner_p.rep_eq
    by (simp add: inner_complex_def)
  moreover have "gyr\<^sub>m u v a = of_complex(((1 + (to_complex u) * cnj (to_complex v)) / (1 + (cnj (to_complex u)) * to_complex v)) *
    (to_complex a))"
    by (metis Mobius_gyrocarrier'.of_carrier gyr_m'_def gyr\<^sub>m.rep_eq)
  moreover have "gyr\<^sub>m u v b = of_complex(((1 + (to_complex u) * cnj (to_complex v)) / (1 + (cnj (to_complex u)) * to_complex v)) *
    (to_complex b))"
    by (metis Mobius_gyrocarrier'.of_carrier gyr_m'_def gyr\<^sub>m.rep_eq)
  moreover have "(cnj (to_complex (gyr\<^sub>m u v a))) = cnj ((1 + (to_complex u) * cnj (to_complex v)) / (1 + (cnj (to_complex u)) * to_complex v)) *
    cnj (to_complex a)"
    by (simp add: gyr_m'_def gyr\<^sub>m.rep_eq)
  moreover have " (cnj ((1 + (to_complex u) * cnj (to_complex v)) / (1 + (to_complex v)*(cnj (to_complex u))) ))*  ((1 + (to_complex u) * cnj (to_complex v)) / (1 + (to_complex v)*(cnj (to_complex u)))) = 1"
  proof-
    have *: "cmod (to_complex u) < 1"
      using to_complex by blast
    moreover have **:"cmod (to_complex v) < 1"
      using to_complex by blast
    moreover have "cmod (((1 + (to_complex u) * cnj (to_complex v)) / (1 +  (to_complex v)*(cnj (to_complex u))))) =1"
      using  cmod_mix_cnj[OF * **] 
      by force
    ultimately show ?thesis using cnj_cmod_1
      by (metis mult.commute)
  qed
  moreover have "gyr\<^sub>m u v a \<cdot> gyr\<^sub>m u v b = Re((cnj (to_complex a))*(to_complex b))"
    using calculation(1) calculation(5) gyr_m'_def gyr\<^sub>m.rep_eq by force
  moreover have "a \<cdot> b = Re((cnj (to_complex a))*(to_complex b))"
    by (simp add: inner_complex_def inner_p.rep_eq)
  ultimately show ?thesis
    by presburger
qed

interpretation Mobius_gyrocarrier: gyrocarrier 
  where to_carrier = to_complex
proof
  fix u v a b
  have "gyr u v a \<cdot> gyr u v b = a \<cdot> b"
    by (simp add: gyr_PoincareDisc_def moebius_gyroauto)
  then show "gyrocarrier'.gyroinner to_complex (gyr u v a) (gyr u v b) =
             gyrocarrier'.gyroinner to_complex a b"  
    using gyrocarrier'.gyroinner_def[OF Mobius_gyrocarrier'.gyrocarrier'_axioms] Mobius_gyrocarrier'.gyroinner_def 
    by fastforce
qed


global_interpretation Mobius_gyrocarrier_norms_embed': gyrocarrier_norms_embed'
  where to_carrier = to_complex
rewrites
  "Mobius_gyrocarrier_norms_embed'.reals = of_complex ` cor ` {x. abs x < 1}"
proof-
  show *: "gyrocarrier_norms_embed' to_complex"
    by unfold_locales auto

  show "gyrocarrier_norms_embed'.reals to_complex = of_complex ` cor ` {x. \<bar>x\<bar> < 1}"
    unfolding gyrocarrier_norms_embed'.reals_def[OF *]
    using Mobius_gyrocarrier'_norms of_complex_def
    by presburger
qed

lemma Mobius_gyrocarrier_norms_embed'_to_real':
  assumes "x \<in> Mobius_gyrocarrier_norms_embed'.reals"
  shows "Mobius_gyrocarrier_norms_embed'.to_real' x = Re (to_complex x)"
  using assms
  using Mobius_gyrocarrier_norms_embed'.to_real'_def of_complex_inverse
  by fastforce

lemma Mobius_gyrocarrier_norms_embed'_of_real':
  assumes "x \<in> Mobius_gyrocarrier'.norms"
  shows "Mobius_gyrocarrier_norms_embed'.of_real' x = PoincareDisc.of_complex (cor x)"
  using assms
  by (metis Mobius_gyrocarrier'.of_carrier Mobius_gyrocarrier_norms_embed'.of_real'_def comp_apply mem_Collect_eq norm_of_real of_complex_inverse)

lemma gyronorm_Re:
  assumes "Re (to_complex x) \<ge> 0" "Im (to_complex x) = 0"
  shows "\<llangle>x\<rrangle> = Re (to_complex x)"
  using assms
  by (simp add: Mobius_gyrocarrier'.gyronorm_def cmod_eq_Re)

lemma Mobius_gyrocarrier_norms_embed'_reals [simp]: 
  shows "gyrocarrier_norms_embed'.reals to_complex = of_complex ` cor ` {x. \<bar>x\<bar> < 1}"
  by (simp add: Mobius_gyrocarrier_norms_embed'.gyrocarrier_norms_embed'_axioms gyrocarrier_norms_embed'.reals_def of_complex_def)

(* --------------------------------------------------------- *)
definition otimes'_k :: "real \<Rightarrow> complex \<Rightarrow> real" where
  "otimes'_k r z = ((1 + cmod z) powr r - (1 - cmod z) powr r) /
                   ((1 + cmod z) powr r + (1 - cmod z) powr r)" 

lemma otimes'_k_tanh: 
  assumes "cmod z < 1"
  shows "otimes'_k r z = tanh (r * artanh (cmod z))"
proof-
  have "0 < 1 + cmod z"
    by (smt norm_not_less_zero)
  hence "(1 + cmod z) powr r \<noteq> 0"
    by auto

  have "1 - (1 - cmod z) powr r / (1 + cmod z) powr r = 
        ((1 + cmod z) powr r - (1 - cmod z) powr r) / (1 + cmod z) powr r"
    by (smt \<open>(1 + cmod z) powr r \<noteq> 0\<close> add_divide_distrib divide_self)
  moreover
  have "1 + (1 - cmod z) powr r / (1 + cmod z) powr r =
       ((1 + cmod z) powr r + (1 - cmod z) powr r) / (1 + cmod z) powr r"
    by (smt add_divide_distrib calculation)
  moreover
  have "exp (- (r * ln ((1 + cmod z) / (1 - cmod z)))) =
         ((1 + cmod z) / (1 - cmod z)) powr (-r)" 
    using `0 < 1 + cmod z` ln_powr[symmetric, of "(1 + cmod z) / (1 - cmod z)" "-r"]
    using assms by (simp add: powr_def)
  ultimately
  show ?thesis
    using assms powr_divide[of "1 + cmod z" "1 - cmod z" r]
    using `0 < 1 + cmod z` `(1 + cmod z) powr r \<noteq> 0`
    unfolding otimes'_k_def tanh_real_altdef artanh_def
    by (simp add: powr_minus_divide)
qed

lemma cmod_otimes'_k: 
  assumes "cmod z < 1"
  shows "cmod (otimes'_k r z) < 1"
  by (smt assms divide_less_eq_1_pos divide_minus_left otimes'_k_def norm_of_real powr_gt_zero zero_less_norm_iff)

definition otimes' :: "real \<Rightarrow> complex \<Rightarrow> complex" where
  "otimes' r z = (if z = 0 then 0 else cor (otimes'_k r z) * (z / cmod z))"

lemma cmod_otimes':
  assumes "cmod z < 1"
  shows "cmod (otimes' r z) = abs (otimes'_k r z)"
proof (cases "z = 0")
  case True
  thus ?thesis
    by (simp add: otimes'_def otimes'_k_def)
next
  case False
  hence "cmod (cor (otimes'_k r z)) = abs (otimes'_k r z)"
    by simp
  then show ?thesis
    using False
    unfolding otimes'_def
    by (simp add: norm_divide norm_mult)
qed

lift_definition otimes :: "real \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" (infixl "\<otimes>" 105) is otimes'
  using cmod_otimes' cmod_otimes'_k by auto

lemma otimes_distrib_lemma':
  fixes "ax" "bx" "ay" "by" :: real
  assumes "ax + bx \<noteq> 0" "ay + by \<noteq> 0"
  shows "(ax * ay - bx * by) / (ax * ay + bx * by) = 
         ((ax - bx)/(ax + bx) + (ay - by)/(ay + by)) / 
          (1 + ((ax - bx)/(ax + bx))*((ay - by)/(ay + by)))" (is "?lhs = ?rhs")
proof-
  have "(ax - bx)/(ax + bx) + (ay - by)/(ay + by) = ((ax - bx)*(ay + by) + (ay - by)*(ax + bx)) / ((ax + bx)*(ay + by))"
    by (simp add: \<open>ax + bx \<noteq> 0\<close> \<open>ay + by \<noteq> 0\<close> add_frac_eq)
  hence 1: "(ax - bx)/(ax + bx) + (ay - by)/(ay + by) = 2 * (ax * ay - bx * by) / ((ax + bx)*(ay + by))"
    by (simp add: field_simps)

  have "1 + ((ax - bx)/(ax + bx))*((ay - by)/(ay + by)) = 
        (((ax + bx)*(ay + by)) + (ax - bx)*(ay - by))/((ax + bx)*(ay + by))"
    by (simp add: \<open>ax + bx \<noteq> 0\<close> \<open>ay + by \<noteq> 0\<close> add_divide_distrib)
  hence 2: "1 + ((ax - bx)/(ax + bx))*((ay - by)/(ay + by)) = 2 * (ax * ay + bx * by) / ((ax + bx)*(ay + by))"
    by (simp add: field_simps)

  have "?rhs = 2 * (ax * ay - bx * by) / ((ax + bx) * (ay + by)) /
              (2 * (ax * ay + bx * by) / ((ax + bx) * (ay + by)))"
    by (subst 1, subst 2, simp)
  also have "\<dots> = (2 * (ax * ay - bx * by) * ((ax + bx) * (ay + by))) /
                  (2 * ((ax + bx) * (ay + by)) * (ax * ay + bx * by))"
    by auto
  also have "\<dots> = ((2 * ((ax + bx) * (ay + by))) * (ax * ay - bx * by)) / 
                  ((2 * ((ax + bx) * (ay + by))) * (ax * ay + bx * by))"
    by (simp add: field_simps)
  also have "\<dots> = (ax * ay - bx * by) / (ax * ay + bx * by)"
    using \<open>ax + bx \<noteq> 0\<close> \<open>ay + by \<noteq> 0\<close> by auto
  finally
  show ?thesis
    by simp                                                                                 
qed

lemma otimes_distrib_lemma:
  assumes "cmod a < 1"
  shows "otimes'_k (r1 + r2) a = oplus_m' (otimes'_k r1 a) (otimes'_k r2 a)"
  unfolding otimes'_k_def oplus_m'_def
  unfolding powr_add
  apply (subst otimes_distrib_lemma')
  apply (smt powr_gt_zero powr_non_neg)
  apply (smt powr_gt_zero powr_non_neg)
  apply simp
  done

lemma otimes_oplus_m_distrib:
  shows "(r1 + r2) \<otimes> a = r1 \<otimes> a \<oplus>\<^sub>m r2 \<otimes> a" 
proof transfer
  fix r1 r2 a
  assume "cmod a < 1"
  show "otimes' (r1 + r2) a = oplus_m' (otimes' r1 a) (otimes' r2 a)"
  proof (cases "a = 0")
    case True
    then show ?thesis
      by (simp add: otimes'_def oplus_m'_def)
  next
    case False
    let ?p = "1 + cmod a" and ?m = "1 - cmod a"
    have "cor (otimes'_k (r1 + r2) a) * a / cor (cmod a) = 
          oplus_m' (otimes'_k r1 a) (otimes'_k r2 a) * a / cor (cmod a)"
      by (simp add: \<open>cmod a < 1\<close> otimes_distrib_lemma)
    moreover
    have "cor (otimes'_k r1 a) * cnj a * (cor (otimes'_k r2 a) * a) / (cor (cmod a) * cor (cmod a)) = 
          cor (otimes'_k r1 a) * cor (otimes'_k r2 a)"
      by (smt False complex_mod_cnj complex_mod_mult_cnj complex_norm_square mult.commute nonzero_mult_div_cancel_left norm_mult of_real_mult times_divide_times_eq zero_less_norm_iff)
    ultimately
     show ?thesis
      using False
      unfolding otimes'_def oplus_m'_def
      by (smt complex_cnj_complex_of_real complex_cnj_divide complex_cnj_mult distrib_right times_divide_eq_left times_divide_eq_right times_divide_times_eq)
  qed      
qed

lemma otimes_assoc:
  shows "(r1 * r2) \<otimes> a = r1 \<otimes> (r2 \<otimes> a)"
proof transfer
  fix r1 r2 a
  assume "cmod a < 1"
  show "otimes' (r1 * r2) a = otimes' r1 (otimes' r2 a)"
  proof (cases "a = 0")
    case True
    then show ?thesis
      by (simp add: otimes'_def)
  next
    case False
    show ?thesis
    proof (cases "r2 = 0")
      case True
      thus ?thesis
        by (simp add: \<open>cmod a < 1\<close> otimes'_def otimes'_k_tanh)
    next
      case False
      let ?a2 = "otimes' r2 a"
      let ?k2 = "otimes'_k r2 a"
      have "cmod ?a2 = abs ?k2"
        using \<open>cmod a < 1\<close> cmod_otimes'
        by blast
      hence "cmod ?a2 < 1"
        using \<open>cmod a < 1\<close> cmod_otimes'_k
        by auto
      have "(1 + cmod a) / (1 - cmod a) > 1"
        using `a \<noteq> 0`
        by (simp add: \<open>cmod a < 1\<close>)
      hence "artanh (cmod a) > 0"
        by (simp add: artanh_def)
      hence "?k2 \<noteq> 0"
        using `cmod a < 1` `a \<noteq> 0` otimes'_k_tanh[of a r2] `r2 \<noteq> 0`
        by auto
      hence "?a2 \<noteq> 0"
        using `a \<noteq> 0`
        unfolding otimes'_def
        by simp
      have "sgn ?k2 = sgn r2"
        using otimes'_k_tanh[OF `cmod a < 1`, of r2]
        by (smt \<open>0 < artanh (cmod a)\<close> \<open>cmod ?a2 = \<bar>?k2\<bar>\<close> \<open>?a2 \<noteq> 0\<close> mult_nonneg_nonneg mult_nonpos_nonneg sgn_neg sgn_pos tanh_0 tanh_real_neg_iff zero_less_norm_iff)
      have "otimes' r1 (otimes' r2 a) = 
             cor (otimes'_k r1 (cor ?k2 * a / cor (cmod a))) *
             (cor ?k2 * a) / (cor (cmod a) * abs ?k2)"
        using False `?a2 \<noteq> 0`
        using \<open>cmod ?a2 = \<bar>?k2\<bar>\<close> 
        unfolding otimes'_def
        by auto
      also have "... = cor (tanh (r1 * \<bar>r2 * artanh (cmod a)\<bar>)) *  
                 (cor ?k2 * a) / (cor (cmod a) * abs ?k2)"
        using cmod_otimes'[of a r2] `cmod a < 1` `a \<noteq> 0`
        unfolding otimes'_def
        using \<open>cmod ?a2 < 1\<close> \<open>cmod ?a2 = \<bar>?k2\<bar>\<close> otimes'_k_tanh 
        using \<open>cmod a < 1\<close> otimes'_k_tanh[of a r2]
        by (simp add: artanh_abs_tanh)
      also have "... = cor (tanh (r1 * \<bar>r2\<bar> * artanh (cmod a))) *  
                 (cor ?k2 * a) / (cor (cmod a) * abs ?k2)"
        using `artanh (cmod a) > 0`
        by (smt ab_semigroup_mult_class.mult_ac(1) mult_minus_left mult_nonneg_nonneg)
      also have "... = cor (tanh (r1 * \<bar>r2\<bar> * artanh (cmod a))) * sgn ?k2 * (a / cor (cmod a))"
        by (simp add: mult.commute real_sgn_eq)
      also have "... = cor (tanh (r1 * \<bar>r2\<bar> * artanh (cmod a))) * sgn r2 * (a / cor (cmod a))"
        using `sgn ?k2 = sgn r2`
        by simp
      also have "... = cor (tanh (r1 * r2 * artanh (cmod a))) * (a / cor (cmod a))"
        by (cases "r2 \<ge> 0") auto
      finally show ?thesis
        by (simp add: \<open>cmod a < 1\<close> otimes'_def otimes'_k_tanh)
    qed
  qed
qed

lemma otimes_scale_prop:
  fixes r :: real
  assumes "r \<noteq> 0"
  shows "to_complex (\<bar>r\<bar> \<otimes> a) / \<llangle>r \<otimes> a\<rrangle>  = to_complex a / \<llangle>a\<rrangle>"
proof-
  let ?f = "\<lambda> r a. tanh (r * artanh (cmod (to_complex a)))"

  have *: "to_complex (\<bar>r\<bar> \<otimes> a) = ?f \<bar>r\<bar> a * (to_complex a / \<llangle>a\<rrangle>)"
    using Mobius_gyrocarrier'.gyronorm_def to_complex otimes'_def otimes'_k_tanh otimes.rep_eq
    by force
  then have "\<llangle>r \<otimes> a\<rrangle> = cmod (?f r a * (to_complex a / \<llangle>a\<rrangle>))"
    by (metis (no_types, lifting) Mobius_gyrocarrier'.gyronorm_def to_complex cmod_otimes' otimes'_def otimes'_k_tanh otimes.rep_eq mem_Collect_eq norm_mult norm_of_real)
  then have "\<llangle>r \<otimes> a\<rrangle> = \<bar>?f r a / \<llangle>a\<rrangle>\<bar> * cmod (to_complex a)"
    by (metis (no_types, opaque_lifting) norm_mult norm_of_real of_real_divide times_divide_eq_left times_divide_eq_right)

  have "?f \<bar>r\<bar> a = tanh(\<bar>r\<bar> * \<bar>artanh (cmod (to_complex a))\<bar>)"
    by (smt (verit) to_complex artanh_nonneg mem_Collect_eq norm_ge_zero)
  then have "?f \<bar>r\<bar> a = \<bar>?f r a\<bar>"
    by (metis abs_mult tanh_real_abs)

  have "\<bar>?f r a / \<llangle>a\<rrangle>\<bar> = ?f \<bar>r\<bar> a / \<llangle>a\<rrangle>"
    by (metis Mobius_gyrocarrier'.gyronorm_def to_complex abs_divide abs_le_self_iff abs_mult_pos abs_norm_cancel artanh_nonneg dual_order.refl mem_Collect_eq  tanh_real_abs)
  then have **:"?f \<bar>r\<bar> a / \<llangle>a\<rrangle> = \<bar>?f r a / \<llangle>a\<rrangle>\<bar>"
    by simp

  show ?thesis
  proof (cases "to_complex a = 0")
    case True
    then show ?thesis
      using assms
      by (simp add: otimes'_def otimes.rep_eq)
  next
    case False
    then have "\<bar>?f r a / \<llangle>a\<rrangle>\<bar> \<noteq>0"
      using assms
      by (metis artanh_0 Mobius_gyrocarrier'.gyronorm_def to_complex abs_norm_cancel artanh_not_0 artanh_tanh_real divide_eq_0_iff linorder_not_less mem_Collect_eq mult_eq_0_iff norm_eq_zero not_less_iff_gr_or_eq zero_less_abs_iff)
    then show ?thesis
      using * ** Mobius_gyrocarrier'.gyronorm_def 
            \<open>\<llangle>r \<otimes> a\<rrangle> = \<bar>?f r a / \<llangle>a\<rrangle>\<bar> * cmod (to_complex a)\<close> 
      by fastforce
  qed
qed

lemma gamma_factor_eq1_lemma1:
  shows "cmod(1 + cnj a * b)*cmod(1 + cnj a * b) - cmod(a+b)*cmod(a+b) =
         (1 - cmod a * cmod a) * (1 - cmod b * cmod b)"
proof-
  have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) = (1+(cnj a)*b) * cnj(1+(cnj a)*b)"
    by (metis complex_norm_square power2_eq_square)
  then have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) = (1+(cnj a)*b)*(1+(cnj(cnj a))* (cnj b))"
    using complex_cnj_add complex_cnj_mult complex_cnj_one by presburger
  then have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b)= 1+a*(cnj b)+(cnj a)*b + (cnj a)*b*a*(cnj b)"
    by (simp add: field_simps)
  moreover 
  have "cmod(a+b)*cmod(a+b) = (a+b)*cnj(a+b)"
    by (metis complex_norm_square power2_eq_square)
  then have "cmod(a+b)*cmod(a+b) = a*(cnj a) + a*(cnj b) + b*(cnj a) + b*(cnj b)"
    by (simp add: field_simps)
  then have "cmod(a+b)*cmod(a+b) = cmod(a)*cmod(a) + a*(cnj b) + b*(cnj a) + cmod(b)*cmod(b)"
    by (metis complex_norm_square power2_eq_square)
  ultimately have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) - cmod(a+b)*cmod(a+b) = 
    (1+a*(cnj b)+(cnj a)*b + (cnj a)*b*a*(cnj b))-( cmod(a)*cmod(a) + a*(cnj b) + b*(cnj a) + cmod(b)*cmod(b))"
    by auto
  then have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) - cmod(a+b)*cmod(a+b) = (1+(cnj a)*a*(b*(cnj b)) - cmod(a)*cmod(a) - cmod(b)*cmod(b))"
    by fastforce
  then have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) - cmod(a+b)*cmod(a+b) = (1+(cmod(a)*cmod(a))*(b*(cnj b))-cmod(a)*cmod(a) - cmod(b)*cmod(b))"
    by (metis (mono_tags, opaque_lifting) complex_norm_square mult.assoc mult.left_commute power2_eq_square)
  then have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) - cmod(a+b)*cmod(a+b) = (1+(cmod(a)*cmod(a))*(cmod(b)*cmod(b))-cmod(a)*cmod(a) - cmod(b)*cmod(b))"
    by (smt (verit) Re_complex_of_real cmod_power2 complex_In_mult_cnj_zero complex_mod_cnj complex_mod_mult_cnj diff_add_cancel cnj_cmod norm_mult norm_zero of_real_1 plus_complex.sel(1) times_complex.sel(1))
  moreover
  have "(1-cmod(a)*cmod(a))*(1-cmod(b)*cmod(b)) = 1+(cmod(a)*cmod(a))*(cmod(b)*cmod(b))-cmod(a)*cmod(a)-cmod(b)*cmod(b)"
    by (simp add: field_simps)
  ultimately
  show ?thesis 
    by presburger
qed

lemma gamma_factor_eq1_lemma2:
  fixes x y::real
  assumes "y > 0"  
  shows "1 / sqrt(1 - (x*x)/(y*y)) = abs y / sqrt(y*y - x*x)"
proof-
  have "1 - ((x*x)/(y*y)) = (y*y-x*x) / (y*y)"
    using assms
    by (metis diff_divide_distrib div_0 divide_less_cancel divide_self no_zero_divisors)
  then have "sqrt (1 - (x*x)/(y*y)) = sqrt(y*y-x*x)/sqrt(y*y)"
    using real_sqrt_divide by presburger
  then have "sqrt(1 - (x*x)/(y*y)) = sqrt(y*y-x*x)/abs(y)"
    using real_sqrt_abs2 by presburger
  then show ?thesis
    by auto
qed

lemma gamma_factor_norm_oplus_m:
  shows "\<gamma> (\<llangle>a \<oplus>\<^sub>m b\<rrangle>) = 
         \<gamma> (to_complex a) *  
         \<gamma> (to_complex b) * 
         cmod (1 + cnj (to_complex a) * (to_complex b))"
proof-
  let ?a = "to_complex a" and ?b = "to_complex b"
  have "norm (\<llangle>a \<oplus>\<^sub>m b\<rrangle>) < 1"
    using Mobius_gyrocarrier'.gyronorm_def to_complex abs_square_less_1
    by fastforce
  then have *: "\<gamma> (\<llangle>a \<oplus>\<^sub>m b\<rrangle>) = 
                1 / sqrt(1 - cmod (?a+?b) / cmod (1 + cnj ?a *?b) * cmod (?a+?b) / cmod (1 + cnj ?a *?b))"
    using Mobius_gyrocarrier'.gyronorm_def gamma_factor_def oplus_m'_def oplus_m.rep_eq norm_divide norm_eq_zero norm_le_zero_iff norm_of_real real_norm_def 
    by (smt (verit, del_insts) power2_eq_square times_divide_eq_right)
  also have "\<dots> =  
           cmod(1 + cnj ?a * ?b) /
           sqrt(cmod (1 + cnj ?a * ?b) * cmod (1 + cnj ?a * ?b) -
                cmod (?a+?b) * cmod (?a+?b))"
  proof-
    let ?iz1 = "cmod (?a+?b) * cmod (?a+?b)"
    let ?iz2 = "cmod (1 + cnj ?a * ?b) * cmod (1 + cnj ?a * ?b)"
    have "?iz1 \<ge> 0"
      by force
    moreover
    have "?iz2 > 0"
      using den_not_zero to_complex
      by auto
    ultimately show ?thesis
      using zero_less_mult_iff
      by (smt (verit, best) divide_divide_eq_left gamma_factor_eq1_lemma2 norm_not_less_zero times_divide_eq_left)
  qed
  also have "\<dots> = cmod(1 + cnj ?a * ?b) / sqrt((1 - cmod ?a * cmod ?a) * (1 - cmod ?b * cmod ?b))"    
    using gamma_factor_eq1_lemma1
    by presburger
  also have "\<dots> =
         \<gamma> (to_complex a) *  
         \<gamma> (to_complex b) * 
         cmod (1 + cnj (to_complex a) * (to_complex b))"
  proof-
    have "cmod (to_complex a) < 1" "cmod (to_complex b) < 1"
      using to_complex
      by auto
    then show ?thesis
      unfolding gamma_factor_def
      by (simp add: power2_eq_square real_sqrt_mult)
  qed
  finally show ?thesis
    .
qed


lemma gamma_factor_norm_oplus_m':
  shows "\<gamma>\<^sub>p (of_complex (cor (\<llangle>a \<oplus>\<^sub>m b\<rrangle>))) = 
         \<gamma>\<^sub>p (a) *  
         \<gamma>\<^sub>p (b) * 
         cmod (1 + cnj (to_complex a) * (to_complex b))"
proof-
  have "norm ((cor (\<llangle>a \<oplus>\<^sub>m b\<rrangle>))) <1"
    using norm_lt_one norm_p.rep_eq by auto
  moreover have "\<gamma>\<^sub>p (of_complex (cor (\<llangle>a \<oplus>\<^sub>m b\<rrangle>))) = \<gamma>  (\<llangle>a \<oplus>\<^sub>m b\<rrangle>)"
    by (metis Mobius_gyrocarrier'.gyronorm_def Mobius_gyrocarrier'.norm_in_norms Mobius_gyrocarrier_norms_embed'.gyronorm_of_real' Mobius_gyrocarrier_norms_embed'.of_real'_def gamma_factor_def gammma_factor_p.rep_eq o_apply real_norm_def)
  ultimately show ?thesis 
    by (simp add: gamma_factor_norm_oplus_m gammma_factor_p.rep_eq)
qed


lemma gamma_factor_oplus_m_triangle_lemma:
  fixes x y ::real
  assumes "x \<ge> 0" "x < 1" "y \<ge> 0" "y < 1"
  shows "1 / sqrt (1 - ((x+y)*(x+y))/((1+x*y)*(1+x*y))) = 
         (1+x*y) / (sqrt (1-x*x) * sqrt (1-y*y))"
proof-
  have "1 - ((x+y)*(x+y))/((1+x*y)*(1+x*y)) = ((1+x*y)*(1+x*y) - (x+y)*(x+y)) / ((1+x*y)*(1+x*y))"
    by (smt (verit, ccfv_threshold) add_divide_distrib assms div_self mult_eq_0_iff mult_nonneg_nonneg)
  then have "1 - ((x+y)*(x+y))/((1+x*y)*(1+x*y)) = ((1-x*x)*(1-y*y)) / ((1+x*y)*(1+x*y))"
    by (simp add: field_simps)
  then have "sqrt(1 - ((x+y)*(x+y))/((1+x*y)*(1+x*y))) = 
             (sqrt(1-x*x)*sqrt(1-y*y)) / (sqrt((1+x*y)*(1+x*y)))"
    using assms real_sqrt_divide real_sqrt_mult
    by presburger
  then show ?thesis
    using assms
    by simp
qed

lemma gamma_factor_oplus_m_triangle:
  shows "\<gamma> (\<llangle>a \<oplus>\<^sub>m b\<rrangle>) \<le> \<gamma> (to_complex ((of_complex (\<llangle>a\<rrangle>)) \<oplus>\<^sub>m (of_complex (\<llangle>b\<rrangle>))))"
proof-
  have "\<gamma> (to_complex ((of_complex (\<llangle>a\<rrangle>)) \<oplus>\<^sub>m (of_complex (\<llangle>b\<rrangle>)))) =
        \<gamma> (\<llangle>a\<rrangle>) * \<gamma> (\<llangle>b\<rrangle>) * (1 + \<llangle>a\<rrangle> * \<llangle>b\<rrangle>)"
  proof-
    let ?expr1 =  "((\<llangle>a\<rrangle>) + (\<llangle>b\<rrangle>)) / (1 + (\<llangle>a\<rrangle>)*(\<llangle>b\<rrangle>))"
    let ?expr2 = "to_complex (of_complex (\<llangle>a\<rrangle>) \<oplus>\<^sub>m of_complex (\<llangle>b\<rrangle>))"
    have *: "?expr1 = ?expr2"
      using Mobius_gyrocarrier'.gyronorm_def Mobius_gyrocarrier'.to_carrier to_complex oplus_m'_def oplus_m.rep_eq
      by auto

    have **: "norm (\<llangle>a\<rrangle>) < 1" "norm (\<llangle>b\<rrangle>) < 1"
      using to_complex abs_square_less_1 norm_p.rep_eq 
      by fastforce+
    then have ***: "\<gamma> (\<llangle>a\<rrangle>) = 1 / sqrt(1 - (\<llangle>a\<rrangle>) * (\<llangle>a\<rrangle>))"
                   "\<gamma> (\<llangle>b\<rrangle>) = 1 / sqrt(1 - (\<llangle>b\<rrangle>) * (\<llangle>b\<rrangle>))"
      unfolding gamma_factor_def
      by (auto simp add: power2_eq_square) 

    have "\<gamma> ?expr1 = 1 / sqrt(1 - ((cmod (?expr1)) * cmod(?expr1)))"
      using * **
      unfolding gamma_factor_def power2_eq_square
      by (metis norm_lt_one norm_of_real norm_p.rep_eq real_norm_def)
    moreover
    have "cmod ?expr1 = ?expr1"
      by (smt (verit, ccfv_threshold) Mobius_gyrocarrier'.gyronorm_def mult_less_0_iff norm_divide norm_not_less_zero norm_of_real of_real_1 of_real_add of_real_divide of_real_mult)
    ultimately
    have "\<gamma> ?expr1 = 1 / sqrt (1 - (Re ?expr1 * Re ?expr1))"
       by (metis Re_complex_of_real)
    then have "\<gamma> ?expr1 = (1 + \<llangle>a\<rrangle>*\<llangle>b\<rrangle>) / (sqrt (1-\<llangle>a\<rrangle>*\<llangle>a\<rrangle>) * sqrt (1-\<llangle>b\<rrangle>*\<llangle>b\<rrangle>))"
       using Mobius_gyrocarrier'.gyronorm_def to_complex gamma_factor_oplus_m_triangle_lemma
       using \<open>cmod ?expr1 = ?expr1\<close> 
       by force
     then have "\<gamma> (cor ?expr1) = (1 + \<llangle>a\<rrangle>*\<llangle>b\<rrangle>) / (sqrt (1-\<llangle>a\<rrangle>*\<llangle>a\<rrangle>) * sqrt (1-\<llangle>b\<rrangle>*\<llangle>b\<rrangle>))"
       unfolding gamma_factor_def
       by (metis norm_of_real real_norm_def)       
    then show ?thesis
      using \<open>?expr1 = ?expr2\<close>[symmetric]
      using  ***
      by simp
  qed

  moreover

  have "\<gamma> (\<llangle>a\<rrangle>) * \<gamma> (\<llangle>b\<rrangle>) * (1 + \<llangle>a\<rrangle>*\<llangle>b\<rrangle>) \<ge> 
        \<gamma> (to_complex a) * \<gamma> (to_complex b) * cmod (1  + cnj (to_complex a) * (to_complex b))"
  proof-
    have *: "\<gamma> (\<llangle>a\<rrangle>) = \<gamma> (to_complex a)"
            "\<gamma> (\<llangle>b\<rrangle>) = \<gamma> (to_complex b)"
       by (auto simp add: Mobius_gyrocarrier'.gyronorm_def gamma_factor_def)
     
     have "cmod (1 + cnj (to_complex a) * (to_complex b)) \<le> 
           cmod 1 + cmod (cnj (to_complex a) * (to_complex b))"
       using norm_triangle_ineq
       by blast
     also have "\<dots> = 1 + cmod (to_complex a) * cmod (to_complex b)"
       by (simp add: norm_mult)
     also have "\<dots> = 1 + \<llangle>a\<rrangle>*\<llangle>b\<rrangle>"
       using Mobius_gyrocarrier'.gyronorm_def
       by force
     finally show ?thesis
       using *[symmetric]
       using Mobius_gyrocarrier'.gyronorm_def gamma_factor_positive norm_lt_one
       by (simp add: gamma_factor_positive)
   qed

   ultimately show ?thesis 
     using gamma_factor_norm_oplus_m
     by presburger
qed

lemma mobius_triangle:
  shows "\<llangle>a \<oplus>\<^sub>m b\<rrangle> \<le> \<llangle>of_complex (\<llangle>a\<rrangle>) \<oplus>\<^sub>m of_complex (\<llangle>b\<rrangle>)\<rrangle>"
proof (cases "to_complex a = - to_complex b")
  case True
  then show ?thesis
   by (simp add: Mobius_gyrocarrier'.gyronorm_def oplus_m'_def oplus_m.rep_eq)
next
  case False
  let ?e1 = "(\<llangle>a \<oplus>\<^sub>m b\<rrangle>)"
  let ?e2 = "cmod (to_complex (of_complex (\<llangle>a\<rrangle>) \<oplus>\<^sub>m of_complex (\<llangle>b\<rrangle>)))"
  have "?e1 > 0"
    by (smt (verit, best) Mobius_gyrocarrier'.gyronorm_def \<open>to_complex a \<noteq> - to_complex b\<close> ab_left_minus add_right_cancel divide_eq_0_iff gamma_factor_norm_oplus_m gamma_factor_positive oplus_m'_def oplus_m.rep_eq norm_eq_zero norm_le_zero_iff of_real_0 zero_less_mult_iff)
  moreover
  have "?e2 > 0"
    by (smt (verit, best) calculation gamma_factor_def gamma_factor_increasing gamma_factor_oplus_m_triangle norm_lt_one norm_zero zero_less_norm_iff)
  moreover
  have "?e1 < 1" "?e2 < 1"
    using Mobius_gyrocarrier'.gyronorm_def to_complex 
    by auto
  ultimately 
  show ?thesis
    using gamma_factor_increase_reverse[of ?e1 ?e2]
    by (smt (verit, del_insts) gamma_factor_def gamma_factor_increasing gamma_factor_oplus_m_triangle norm_p.rep_eq real_norm_def)
qed

lemma mobius_triangle':
  shows "\<llangle>a \<oplus>\<^sub>m b\<rrangle> \<le> Re (to_complex (of_complex (\<llangle>a\<rrangle>) \<oplus>\<^sub>m of_complex (\<llangle>b\<rrangle>)))"
proof-
  have "\<llangle>of_complex (\<llangle>a\<rrangle>) \<oplus>\<^sub>m of_complex (\<llangle>b\<rrangle>)\<rrangle> = Re (to_complex (of_complex (\<llangle>a\<rrangle>) \<oplus>\<^sub>m of_complex (\<llangle>b\<rrangle>)))" (is "\<llangle>?x\<rrangle> = ?y")
  proof (rule gyronorm_Re)
    show "Re (to_complex ?x) \<ge> 0"
      by (rule oplusM_pos_reals, simp_all add: norm_geq_zero norm_lt_one)
  next
    show "Im (to_complex ?x) = 0"
      by (rule oplusM_reals, simp_all add: norm_geq_zero norm_lt_one)
  qed
  then show ?thesis
    using mobius_triangle[of a b]
    by simp
qed

lemma mobius_gyroauto_norm:
  shows "\<llangle>gyr\<^sub>m a b v\<rrangle> = \<llangle>v\<rrangle>"
  using Mobius_gyrocarrier.norm_gyr gyr_PoincareDisc_def
  by auto

lemma otimes_homogenity:
  shows "\<llangle>r \<otimes> a\<rrangle> = cmod (to_complex (\<bar>r\<bar> \<otimes> of_complex (\<llangle>a\<rrangle>)))"
proof (cases "a = 0\<^sub>m")
  case True
  then show ?thesis
    using Mobius_gyrocarrier'.gyronorm_def otimes'_def otimes.rep_eq ozero_m'_def ozero_m.rep_eq ozero_m_def
    by force
next
  case False
  have "\<llangle>r \<otimes> a\<rrangle> = \<bar>tanh (r * artanh (\<llangle>a\<rrangle>))\<bar>"
    using Mobius_gyrocarrier'.gyronorm_def to_complex cmod_otimes' otimes'_k_tanh otimes.rep_eq
    by force
  moreover
  have "to_complex (\<bar>r\<bar> \<otimes> of_complex (\<llangle>a\<rrangle>)) = tanh (\<bar>r\<bar> * artanh (\<llangle>a\<rrangle>))"
  proof-
    have "to_complex (\<bar>r\<bar> \<otimes> of_complex (\<llangle>a\<rrangle>)) = 
          otimes'_k \<bar>r\<bar> (\<llangle>a\<rrangle>) * ((\<llangle>a\<rrangle>) / cmod (\<llangle>a\<rrangle>))" 
      using otimes_def otimes'_def
      using Mobius_gyrocarrier'.gyronorm_def Mobius_gyrocarrier'.to_carrier to_complex otimes.rep_eq
      by (smt (verit, del_insts) False mem_Collect_eq norm_eq_zero norm_geq_zero norm_of_real of_real_divide of_real_mult to_complex_0_iff)
    
    moreover
    have "cmod (cmod (to_complex a)) = cmod (to_complex a)"
      by simp
    then have "(\<llangle>a\<rrangle>) / cmod (\<llangle>a\<rrangle>) = 1"
      using \<open>a \<noteq> 0\<^sub>m\<close>
      by (metis Mobius_gyrocarrier'.gyronorm_def Mobius_gyrocarrier'.of_carrier div_self norm_eq_zero ozero_m'_def ozero_m.rep_eq)
    ultimately
    have "to_complex (\<bar>r\<bar> \<otimes> ( of_complex (cor(\<llangle>a\<rrangle>)))) = cor (otimes'_k \<bar>r\<bar> (cor (\<llangle>a\<rrangle>)))"
      by auto
    then show ?thesis
      using Mobius_gyrocarrier'.gyronorm_def to_complex otimes'_k_tanh
      by auto
  qed
  moreover 
  have "\<bar>tanh(r * artanh (cmod (to_complex a))) / \<llangle>a\<rrangle>\<bar> = 
         tanh (\<bar>r\<bar> * artanh (cmod (to_complex a))) / \<llangle>a\<rrangle>"
    by (metis Mobius_gyrocarrier'.gyronorm_def to_complex abs_divide abs_le_self_iff abs_mult_pos abs_norm_cancel artanh_nonneg dual_order.refl mem_Collect_eq  tanh_real_abs)
  ultimately 
  show ?thesis
    by (smt (verit, best) norm_of_real real_compex_cmod tanh_real_abs)
qed

lemma otimes_homogenity':
  shows "\<llangle>r \<otimes> a\<rrangle> = Re (to_complex (\<bar>r\<bar> \<otimes> of_complex (\<llangle>a\<rrangle>)))"
proof-
  have *: "cor (\<llangle>a\<rrangle>) \<in> {z. cmod z < 1}"
    by (simp add: norm_geq_zero norm_lt_one)
  have **: "cmod (otimes' \<bar>r\<bar> (cor (\<llangle>a\<rrangle>))) < 1"
    using cmod_otimes' cmod_otimes'_k norm_lt_one norm_p.rep_eq 
    by force

  have "Re (to_complex (\<bar>r\<bar> \<otimes> of_complex (\<llangle>a\<rrangle>))) \<ge> 0"
    unfolding otimes_def
    using of_complex_inverse Mobius_gyrocarrier'.to_carrier[OF *] ** *
    by (simp add: artanh_nonneg norm_geq_zero otimes'_def otimes'_k_tanh)
    
  moreover

  have "Im (to_complex (\<bar>r\<bar> \<otimes> of_complex (\<llangle>a\<rrangle>))) = 0"
    unfolding otimes_def
    using of_complex_inverse Mobius_gyrocarrier'.to_carrier[OF *] ** *
    by (simp add: otimes'_def)

  ultimately

  have "Re (to_complex (\<bar>r\<bar> \<otimes> of_complex (\<llangle>a\<rrangle>))) = cmod (to_complex (\<bar>r\<bar> \<otimes> of_complex (\<llangle>a\<rrangle>)))"
    using cmod_eq_Re 
    by force

  then show ?thesis
    using otimes_homogenity[of r a]
    by simp
qed

lemma gyr_m_gyrospace:
  shows "gyr\<^sub>m (r1 \<otimes> v) (r2 \<otimes> v) = id"
proof-
  have "gyr_m' (to_complex (r1 \<otimes> v)) (to_complex (r2 \<otimes> v)) = id"
  proof-
    let ?v = "to_complex v"
    let ?e1 = "?v * tanh (r1 * artanh (cmod ?v)) /cmod(to_complex v)"
    let ?e2 = "?v * tanh (r2 * artanh (cmod ?v)) /cmod(to_complex v)"

    have "to_complex (r1 \<otimes> v) = ?e1"
         "to_complex (r2 \<otimes> v) = ?e2"
      using to_complex otimes'_def otimes'_k_tanh otimes.rep_eq
      by auto

    moreover

    have "cnj ?e1 = cnj ?v * cnj (tanh (r1 * artanh (cmod ?v))) / cmod ?v"
         "cnj ?e2 = cnj ?v * cnj (tanh (r2 * artanh (cmod ?v))) / cmod ?v"
        by auto

    moreover

    have "(1 + ?e1 * (cnj ?e2)) / (1 + ?e2 * (cnj ?e1)) = 1"
    proof-
      have "1 + ?e1 * (cnj ?e2) = 1 + ?e2 * (cnj ?e1)"
        by simp
      moreover
      have "1 + ?e2 * (cnj ?e1) \<noteq> 0"
        using \<open>to_complex (r1 \<otimes> v) = ?e1\<close> \<open>to_complex (r2 \<otimes> v) = ?e2\<close>
        by (metis to_complex  div_by_0 divide_eq_1_iff mem_Collect_eq cmod_mix_cnj norm_zero)
      ultimately
      show ?thesis
        by simp
    qed

    ultimately show ?thesis 
       using gyr\<^sub>m_def gyr_m'_def
       by (metis eq_id_iff mult.commute mult_1)
   qed

   then show ?thesis 
     by (metis (no_types, opaque_lifting) add_0_left add_0_right complex_cnj_zero div_by_1 eq_id_iff gyr\<^sub>m_def m_left_id oplus_m'_def oplus_m_def ozero_m'_def ozero_m.rep_eq map_fun_apply mult_zero_left)
qed

lemma gyr_m_gyrospace2:
  shows "gyr\<^sub>m u v (r \<otimes> a) = r \<otimes> (gyr\<^sub>m u v a)"
proof-
  let ?u = "to_complex u" and ?v = "to_complex v" and ?a = "to_complex a"
  let ?e1 = "gyr\<^sub>m u v a"
  let ?e2 = "cmod (to_complex ?e1)"

  have "?e1 = of_complex ((1 + ?u * cnj ?v) / (1 + cnj ?u *?v) * ?a)"
    by (metis Mobius_gyrocarrier'.of_carrier gyr_m'_def gyr\<^sub>m.rep_eq)
  then have "?e2 = cmod ((1 + ?u * cnj ?v) / (1 + cnj ?u *?v)) * cmod ?a"
    by (metis gyr_m'_def gyr\<^sub>m.rep_eq norm_mult)
  then have "?e2 = cmod ?a"
    using Mobius_gyrocarrier'.gyronorm_def mobius_gyroauto_norm 
    by presburger
  then have "r \<otimes> ?e1 = of_complex (((1+cmod ?a) powr r - (1-cmod ?a) powr r) /
                                    ((1+cmod ?a) powr r + (1-cmod ?a) powr r) * to_complex ?e1 / ?e2)"
    using otimes_def 
    by (metis (no_types, lifting) Mobius_gyrocarrier'.of_carrier otimes'_def otimes'_k_def otimes.rep_eq mult_eq_0_iff times_divide_eq_right)
  then have "r \<otimes> ?e1 = of_complex (to_complex (r \<otimes> a) * ((1 + ?u * cnj ?v) / (1 + cnj ?u * ?v)))"
    using otimes_def
    using \<open>?e2 = cmod ?a\<close>
    by (smt (verit, ccfv_threshold) Mobius_gyrocarrier'.of_carrier  ab_semigroup_mult_class.mult_ac(1) gyr_m'_def gyr\<^sub>m.rep_eq otimes'_def otimes'_k_def otimes.rep_eq mult.commute mult_eq_0_iff times_divide_eq_right)
  then show ?thesis 
    by (metis Mobius_gyrocarrier'.of_carrier gyr_m'_def gyr\<^sub>m.rep_eq mult.commute)
qed


lemma reals':
  shows "cor ` {x. abs x < 1} = {z. cmod z < 1 \<and> Im z = 0}"
  by (auto, simp add: complex_eq_iff norm_complex_def)

lemma zero_times_m [simp]:
  shows "0 \<otimes> x = 0\<^sub>m"
  by transfer (simp add: otimes'_def otimes'_k_tanh ozero_m'_def)

interpretation Mobius_gyrocarrier_norms_embed: gyrocarrier_norms_embed to_complex otimes
proof
  fix a b
  assume "a \<in> gyrocarrier_norms_embed'.reals to_complex" "b \<in> gyrocarrier_norms_embed'.reals to_complex"
  then obtain x y where "a = of_complex (cor x)" "b = of_complex (cor y)" "abs x < 1" "abs y < 1"
    by auto
  then show "a \<oplus> b \<in> gyrocarrier_norms_embed'.reals to_complex"
    by (metis (mono_tags, lifting) Mobius_gyrocarrier'.of_carrier Mobius_gyrocarrier'.to_carrier Mobius_gyrocarrier_norms_embed'_reals gyroplus_PoincareDisc_def image_eqI mem_Collect_eq oplusM_reals reals' to_complex)
next
  fix a
  assume "a \<in> gyrocarrier_norms_embed'.reals to_complex"
  then obtain x where "a = of_complex (cor x)" "abs x < 1"
    by auto
  then have "\<ominus> a = of_complex (cor (-x))" "abs (-x) < 1"
    unfolding gyroinv_PoincareDisc_def 
    unfolding ominus_m_def
    by (metis Mobius_gyrocarrier'.of_carrier Mobius_gyrocarrier'.to_carrier map_fun_apply mem_Collect_eq norm_of_real of_real_minus ominus_m'_def ominus_m.rep_eq to_complex_inverse, simp)
  then show "\<ominus> a \<in> gyrocarrier_norms_embed'.reals to_complex"
    by auto
next
  fix r a
  assume "a \<in> gyrocarrier_norms_embed'.reals to_complex"
  then obtain x where "a = of_complex (cor x)" "abs x < 1"
    by auto
  then have "a = PoincareDisc.of_complex (cor x)"  "abs x < 1"
    using Mobius_gyrocarrier_norms_embed'.of_real'_def Mobius_gyrocarrier_norms_embed'_of_real' by auto
  have "Im (to_complex (r \<otimes> a)) = 0"
    by (simp add: \<open>\<bar>x\<bar> < 1\<close> \<open>a = MobiusGyroVectorSpace.of_complex (cor x)\<close> otimes'_def otimes.rep_eq)
  moreover
  have "abs (Re (to_complex (r \<otimes> a))) < 1"
    by (metis Mobius_gyrocarrier'.gyronorm_def calculation cmod_eq_Re norm_lt_one)
  ultimately
  show "r \<otimes> a \<in> gyrocarrier_norms_embed'.reals to_complex"
    unfolding Mobius_gyrocarrier_norms_embed'_of_real'
    by (metis (mono_tags, lifting) Mobius_gyrocarrier'.of_carrier Mobius_gyrocarrier_norms_embed'_reals image_eqI mem_Collect_eq reals' to_complex)
qed

interpretation Mobius_pre_gyrovector_space: pre_gyrovector_space to_complex otimes
proof
  fix a :: PoincareDisc
  show "1 \<otimes> a = a"
    by transfer (auto simp add: otimes'_def otimes'_k_def)
next
  fix r1 r2 a
  show "(r1 + r2) \<otimes> a = r1 \<otimes> a \<oplus> r2 \<otimes> a"
    using gyroplus_PoincareDisc_def otimes_oplus_m_distrib by auto
next
  fix r1 r2 a
  show "(r1 * r2) \<otimes> a = r1 \<otimes> (r2 \<otimes> a)"
    by (simp add: otimes_assoc)
next
  fix r :: real and a
  assume "r \<noteq> 0" 
  then show "to_complex (abs r \<otimes> a) /\<^sub>R gyrocarrier'.gyronorm to_complex (r \<otimes> a) =
             to_complex a /\<^sub>R  gyrocarrier'.gyronorm to_complex a"
    using otimes_scale_prop[of r a]
    by (metis Mobius_gyrocarrier'.gyrocarrier'_axioms divide_inverse gyrocarrier'.gyronorm_def mult.commute norm_p.rep_eq of_real_inverse scaleR_conv_of_real)
next
  fix u v r a
  have "gyr\<^sub>m u v (r \<otimes> a) = r \<otimes> gyr\<^sub>m u v a"
    using gyr_m_gyrospace2 
    by auto
  then show "gyr u v (r \<otimes> a) = r \<otimes> gyr u v a"
    using gyr_PoincareDisc_def by auto
next
  fix r1 r2 v
  have "gyr\<^sub>m (r1 \<otimes> v) (r2 \<otimes> v) = id"
    using gyr_m_gyrospace
    by simp
  then show "gyr (r1 \<otimes> v) (r2 \<otimes> v) = id"
    by (simp add: gyr_PoincareDisc_def)
qed

interpretation Mobius_gyrovector_space: gyrovector_space_norms_embed otimes to_complex 
proof
  fix r a
  show "gyrocarrier'.gyronorm to_complex (r \<otimes> a) =
        Mobius_gyrocarrier_norms_embed.otimesR \<bar>r\<bar> (gyrocarrier'.gyronorm to_complex a)"
    using otimes_homogenity'[of r a]
    by (smt (verit, best) Im_eq_0 Mobius_gyrocarrier'.gyrocarrier'_axioms Mobius_gyrocarrier'.gyronorm_def Mobius_gyrocarrier'.of_carrier Mobius_gyrocarrier_norms_embed'.of_real'_def Mobius_gyrocarrier_norms_embed'.to_real'_norm Mobius_gyrocarrier_norms_embed.otimesR_def abs_Re_le_cmod add.right_neutral comp_apply complex_eq gyrocarrier'.gyronorm_def mult_zero_right of_real_0 otimes_homogenity)
next
  fix a b
  show "gyrocarrier'.gyronorm to_complex (a \<oplus> b)
           \<le> Mobius_gyrocarrier_norms_embed'.oplusR (gyrocarrier'.gyronorm to_complex a) (gyrocarrier'.gyronorm to_complex b)"
  proof-
    have "Re (to_complex (of_complex (cmod (to_complex a)) \<oplus>\<^sub>m of_complex (cmod (to_complex b)))) = 
          Mobius_gyrocarrier_norms_embed'.to_real' (Mobius_gyrocarrier_norms_embed'.of_real' (cmod (to_complex a)) \<oplus> Mobius_gyrocarrier_norms_embed'.of_real' (cmod (to_complex b)))"
      by (smt (verit, ccfv_threshold) Mobius_gyrocarrier'.of_carrier Mobius_gyrocarrier_norms_embed'_of_real' Mobius_gyrocarrier_norms_embed'_to_real' complex_mod_minus_le_complex_mod gyroplus_PoincareDisc_def image_eqI mem_Collect_eq of_complex_inverse oplusM_reals reals' to_complex)
    then show ?thesis
      using mobius_triangle'[of a b]
      by (simp add: Mobius_gyrocarrier'.gyrocarrier'_axioms Mobius_gyrocarrier'.gyronorm_def Mobius_gyrocarrier_norms_embed'.gyrocarrier_norms_embed'_axioms gyrocarrier'.gyronorm_def gyrocarrier_norms_embed'.oplusR_def gyroplus_PoincareDisc_def)
  qed
qed


(* ---------------------------------------------------------------------------- *)

lemma norm_scale_tanh: 
  shows "\<llangle>r \<otimes> z\<rrangle> = \<bar>tanh (r * artanh (\<llangle>z\<rrangle>))\<bar>"
proof transfer
  fix r z
  assume "cmod z < 1"
  have "cmod ((otimes'_k r z) * z / cor (cmod z)) = cmod (otimes'_k r z)"
    by (smt (verit) artanh_0 div_by_0 mult_cancel_right1 nonzero_eq_divide_eq norm_divide norm_not_less_zero norm_of_real of_real_0 otimes'_k_tanh tanh_0)
  then show "cmod (otimes' r z) = \<bar>tanh (r * artanh (cmod z))\<bar>"
    unfolding otimes'_def
    using \<open>cmod z < 1\<close> otimes'_k_tanh 
    by auto
qed

lemma ominus_m_scale:
  shows "k \<otimes> (\<ominus>\<^sub>m u) = \<ominus>\<^sub>m (k \<otimes> u)"
  using Mobius_pre_gyrovector_space.scale_minus' gyroinv_PoincareDisc_def 
  by auto

lemma otimes_2_oplus_m: "2 \<otimes> u = u \<oplus>\<^sub>m u"
  using Mobius_pre_gyrovector_space.times2 gyroplus_PoincareDisc_def
  by simp

definition half' :: "complex \<Rightarrow> complex" where
  "half' v = (\<gamma> v / (1 + \<gamma> v)) *\<^sub>R v"

lift_definition half :: "PoincareDisc \<Rightarrow> PoincareDisc" is half'
  unfolding half'_def
proof-
  fix v
  assume "cmod v < 1"
  let ?k = "\<gamma> v / (1 + \<gamma> v)"
  have "abs ?k < 1"
    using \<open>cmod v < 1\<close> gamma_factor_positive by fastforce
  then show "cmod (?k *\<^sub>R v) < 1"
    using \<open>cmod v < 1\<close>
    by (metis mult_closed_for_unit_disc norm_of_real scaleR_conv_of_real)
qed

lemma otimes_2_half:
  shows "2 \<otimes> (half v) = v"
proof-
  have "2 \<otimes> (half v) = half v \<oplus>\<^sub>m half v"
    using otimes_2_oplus_m
    by simp
  also have "\<dots> = v"
  proof transfer
    fix v :: complex 
    assume assms: "cmod v < 1"
    have *: "\<gamma> v \<noteq> 0" "1 + \<gamma> v \<noteq> 0"
      using assms gamma_factor_positive 
      by fastforce+
    let ?k = "\<gamma> v / (1 + \<gamma> v)"
    have "1 + cnj (?k * v) * (?k * v) = 1 + ?k^2 * (cmod v)\<^sup>2"
      by (simp add: cnj_cmod mult.commute power2_eq_square)
    also have "\<dots> = 1 + (\<gamma> v)\<^sup>2 / (1 + \<gamma> v)\<^sup>2 * (1 - 1 / (\<gamma> v)\<^sup>2)"
      using norm_square_gamma_factor[OF assms]
      by (simp add: power_divide)
    also have "\<dots> = 1 + ((\<gamma> v)\<^sup>2 * ((\<gamma> v)\<^sup>2 - 1)) / ((\<gamma> v)\<^sup>2 * (1 + \<gamma> v)\<^sup>2)"
      using *
      by (simp add: field_simps)
    also have "\<dots> = 1 + ((\<gamma> v)\<^sup>2 - 1) / (1 + \<gamma> v)\<^sup>2"
      using *
      by simp
    also have "\<dots> = 1 + ((\<gamma> v - 1) * (\<gamma> v + 1)) / ((\<gamma> v + 1) * (\<gamma> v + 1))"
      by (simp add: power2_eq_square field_simps)
    also have "\<dots> = 1 + (\<gamma> v - 1) / (\<gamma> v + 1)"
      using *
      by simp
    also have "\<dots> = 2 * ?k"
      using *
      by (simp add: field_simps)
    finally show "oplus_m' (half' v) (half' v) = v"
      unfolding oplus_m'_def half'_def
      using * \<open>1 + cnj (?k * v) * (?k * v) = 1 + ?k\<^sup>2 * (cmod v)\<^sup>2\<close>
      by (smt (verit)  mult_eq_0_iff nonzero_mult_div_cancel_left of_real_eq_0_iff power2_eq_square scaleR_conv_of_real scaleR_left_distrib)
  qed
  finally show ?thesis
    .
qed

lemma half:
  shows "half v = (1/2) \<otimes> v"
  by (metis Mobius_pre_gyrovector_space.scale_assoc mult_2 real_scaleR_def scaleR_half_double otimes_2_half)

lemma half':
  assumes "cmod u < 1"
  shows "otimes' (1/2) u = half' u"
  using assms half half.rep_eq[of "of_complex u"] otimes.rep_eq
  by simp

lemma half_gamma':
  shows "to_complex ((1 / 2) \<otimes> u) = 
         (\<gamma> (to_complex u)) / (1 + \<gamma> (to_complex u)) * to_complex u"
  using half half.rep_eq half'_def
  by (simp add: scaleR_conv_of_real)

definition double' :: "complex \<Rightarrow> complex" where
  "double' v = (2 * (\<gamma> v)\<^sup>2 / (2 * (\<gamma> v)\<^sup>2 - 1)) *\<^sub>R v"

lemma double'_cmod:
  assumes "cmod v < 1"
  shows "2 * (\<gamma> v)\<^sup>2 / (2 * (\<gamma> v)\<^sup>2 - 1) = 2 / (1 + (cmod v)\<^sup>2)" (is "?lhs = ?rhs")
proof-
  have **: "1 - (cmod v)\<^sup>2 > 0"
    using assms
    using real_sqrt_lt_1_iff by fastforce

  have "?lhs = 2 * (1 / (1 - (cmod v)\<^sup>2)) / (2 * (1 / (1 - (cmod v)\<^sup>2)) - 1)"
    using gamma_factor_square_norm[OF assms]
    by simp
  also have "\<dots> = 2 / (1 + (cmod v)\<^sup>2)"
  proof-
    have "2 * (1 / (1 - (cmod v)\<^sup>2)) = 2 / (1 - (cmod v)\<^sup>2)"
      by simp
    moreover
    have "2 * (1 / (1 - (cmod v)\<^sup>2)) - 1 = 2 / (1 - (cmod v)\<^sup>2) -  (1 - (cmod v)\<^sup>2) / (1 - (cmod v)\<^sup>2)"
      using **
      by simp
    then have "2 * (1 / (1 - (cmod v)\<^sup>2)) - 1 = (1 + (cmod v)\<^sup>2) / (1 - (cmod v)\<^sup>2)"
      using **
      by (simp add: field_simps)
    ultimately
    show ?thesis
      using **
      by (smt (verit, del_insts) divide_divide_eq_left nonzero_mult_div_cancel_left power2_eq_square times_divide_eq_right)
  qed
  finally show ?thesis
    .
qed

lemma cmod_double':
  assumes "cmod v < 1"
  shows "cmod (double' v) = 2*cmod v / (1 + (cmod v)\<^sup>2)"
proof-
  have "cmod (double' v) = 
        abs(2 * (\<gamma> v)\<^sup>2 / (2 * (\<gamma> v)\<^sup>2 - 1)) * cmod v"
    unfolding double'_def
    by simp
  also have "\<dots> = abs (2 / (1 + (cmod v)\<^sup>2)) * cmod v"
    using assms double'_cmod 
    by presburger
  also have "\<dots> = 2*cmod v / (1 + (cmod v)\<^sup>2)"
  proof-
    have "2 / (1 + (cmod v)\<^sup>2) > 0"
      by (metis half_gt_zero_iff power_one sum_power2_gt_zero_iff zero_less_divide_iff zero_neq_one)
    then show ?thesis
      by simp
  qed
  finally show ?thesis
    .
qed

lift_definition double :: "PoincareDisc \<Rightarrow> PoincareDisc" is double'
proof-
  fix v
  assume *: "cmod v < 1"

  have "cmod (double' v) = 2 * cmod v / (1 + (cmod v)\<^sup>2)"
    using * cmod_double'
    by simp
  also have "\<dots> < 1"
  proof-
    have "(1 - cmod v)\<^sup>2 > 0"
      using *
      by simp
    then have "1 - 2* cmod v + (cmod v)\<^sup>2 > 0"
      by (simp add: field_simps power2_eq_square)
    then have "2*cmod v < 1 + (cmod v)\<^sup>2"
      by simp
    moreover
    have "1 + (cmod v)\<^sup>2 > 0"
      by (smt (verit) not_sum_power2_lt_zero)
    ultimately
    show ?thesis
      using divide_less_eq_1 by blast
  qed
  finally
  show "cmod (double' v) < 1"
    by simp
qed

lemma double'_otimes'_2:
  assumes "cmod v < 1"
  shows "double' v = otimes' 2 v"
proof-
  have "v * 2 / (1 + cor (cmod v) * cor (cmod v)) =
        v * 4 / (2 + 2 * (cor (cmod v) * cor (cmod v)))"

    by (metis (no_types, lifting) distrib_left_numeral mult_2 nonzero_mult_divide_mult_cancel_left numeral_Bit0 one_add_one times_divide_eq_right zero_neq_numeral)

  then show ?thesis
    using assms
    unfolding double'_def otimes'_def otimes'_k_def double'_cmod[OF assms] scaleR_conv_of_real
    by (auto simp add: field_simps power2_eq_square)
qed

lemma double: 
  shows "double u = 2 \<otimes> u"
  by transfer (simp add: double'_otimes'_2)


end
