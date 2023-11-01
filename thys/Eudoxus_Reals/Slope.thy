(*  Author: Ata Keskin, TU München 
*)

theory Slope
imports "HOL.Archimedean_Field"
begin

section \<open>Slopes\<close>

subsection \<open>Bounded Functions\<close>

definition bounded :: "('a \<Rightarrow> int) \<Rightarrow> bool" where
  "bounded f \<longleftrightarrow> bdd_above ((\<lambda>z. \<bar>f z\<bar>) ` UNIV)"

lemma boundedI:
  assumes "\<And>z. \<bar>f z\<bar> \<le> C"
  shows "bounded f"
  unfolding bounded_def by (rule bdd_aboveI2, force intro: assms)

lemma boundedE[elim]:
  assumes "bounded f" "\<exists>C. (\<forall>z. \<bar>f z\<bar> \<le> C) \<and> 0 \<le> C \<Longrightarrow> P"
  shows P
  using assms unfolding bounded_def bdd_above_def by fastforce

lemma boundedE_strict:
  assumes "bounded f" "\<exists>C. (\<forall>z. \<bar>f z\<bar> < C) \<and> 0 < C \<Longrightarrow> P"
  shows P
  by (meson bounded_def bdd_above_def assms boundedE gt_ex order.strict_trans1)

lemma bounded_alt_def: "bounded f \<longleftrightarrow> (\<exists>C. \<forall>z. \<bar>f z\<bar> \<le> C)" using boundedI boundedE by meson

lemma bounded_iff_finite_range: "bounded f \<longleftrightarrow> finite (range f)"
proof
  assume "bounded f"
  then obtain C where bound: "\<bar>z\<bar> \<le> C" if "z \<in> range f" for z by blast
  have "range f \<subseteq> {z. z \<le> C \<and> -z \<le> C}" using abs_le_D1[OF bound] abs_le_D2[OF bound] by blast
  also have "... = {(-C)..C}" by force
  finally show "finite (range f)" using finite_subset finite_atLeastAtMost_int by blast
next
  assume "finite (range f)"
  hence "\<bar>f z\<bar> \<le> max (abs (Sup (range f))) (abs (Inf (range f)))" for z 
    using cInf_lower[OF _ bdd_below_finite, of "f z" "range f"] cSup_upper[OF _ bdd_above_finite, of "f z" "range f"] by force
  thus "bounded f" by (rule boundedI)
qed

lemma bounded_constant:
  shows "bounded (\<lambda>_. c)"
  by (rule boundedI[of _ "\<bar>c\<bar>"], blast)

lemma bounded_add:
  assumes "bounded f" "bounded g"
  shows "bounded (\<lambda>z. f z + g z)"
proof -
  obtain C_f C_g where "\<bar>f z\<bar> \<le> C_f" "\<bar>g z\<bar> \<le> C_g" for z using assms by blast
  hence "\<bar>f z + g z\<bar> \<le> C_f + C_g" for z by (meson abs_triangle_ineq add_mono dual_order.trans)
  thus ?thesis by (blast intro: boundedI)
qed

lemma bounded_mult:
  assumes "bounded f" "bounded g"
  shows "bounded (\<lambda>z. f z * g z)"
proof -
  obtain C where bound: "\<bar>f z\<bar> \<le> C" and C_nonneg: "0 \<le> C" for z using assms by blast
  obtain C' where bound': "\<bar>g z\<bar> \<le> C'" for z using assms by blast
  show ?thesis using mult_mono[OF bound bound' C_nonneg abs_ge_zero] by (simp only: boundedI[of "\<lambda>z. f z * g z" "C * C'"] abs_mult)
qed

lemma bounded_mult_const:
  assumes "bounded f"
  shows "bounded (\<lambda>z. c * f z)"
  by (rule bounded_mult[OF bounded_constant[of c] assms])

lemma bounded_uminus:
  assumes "bounded f"
  shows "bounded (\<lambda>x. - f x)"
  using bounded_mult_const[OF assms, of "- 1"] by simp

lemma bounded_comp:
  assumes "bounded f"
  shows "bounded (f o g)" and "bounded (g o f)"
proof -
  show "bounded (f o g)" using assms boundedI comp_def boundedE by metis
next
  have "range (g o f) = g ` range f" by fastforce
  thus "bounded (g o f)" using assms by (fastforce simp: bounded_iff_finite_range)
qed

subsection \<open>Properties of Slopes\<close>

definition slope :: "(int \<Rightarrow> int) \<Rightarrow> bool" where
  "slope f \<longleftrightarrow> bounded (\<lambda>(m, n). f (m + n) - (f m + f n))"

lemma bounded_slopeI:
  assumes "bounded f"
  shows "slope f"
proof -
  obtain C where "\<bar>f x\<bar> \<le> C" for x using assms by blast
  hence "\<bar>f (m + n) - (f m + f n)\<bar> \<le> C + (C + C)" for m n
    using abs_triangle_ineq4[of "f (m + n)" "f m + f n"] abs_triangle_ineq[of "f m" "f n"] by (meson add_mono order_trans)
  thus ?thesis unfolding slope_def by (fast intro: boundedI)
qed

lemma slopeE[elim]:
  assumes "slope f"
  obtains C where "\<And>m n. \<bar>f (m + n) - (f m + f n)\<bar> \<le> C" "0 \<le> C" using assms unfolding slope_def by fastforce

lemma slope_add:
  assumes "slope f" "slope g"
  shows "slope (\<lambda>z. f z + g z)"
proof -
  obtain C where bound: "\<bar>f (m + n) - (f m + f n)\<bar> \<le> C" for m n using assms by fast
  obtain C' where bound': "\<bar>g (m + n) - (g m + g n)\<bar> \<le> C'" for m n using assms by fast
  have "\<bar>f (m + n) - (f m + f n)\<bar> + \<bar>g (m + n) - (g m + g n)\<bar> \<le> C + C'" for m n using add_mono_thms_linordered_semiring(1) bound bound' by fast
  moreover have "\<bar>(\<lambda>z. f z + g z) (m + n) - ((\<lambda>z. f z + g z) m + (\<lambda>z. f z + g z) n)\<bar> \<le> \<bar>f (m + n) - (f m + f n)\<bar> + \<bar>g (m + n) - (g m + g n)\<bar>" for m n by linarith
  ultimately have "\<bar>(\<lambda>z. f z + g z) (m + n) - ((\<lambda>z. f z + g z) m + (\<lambda>z. f z + g z) n)\<bar> \<le> C + C'" for m n using order_trans by fast
  thus "slope (\<lambda>z. f z + g z)" unfolding slope_def by (fast intro: boundedI)
qed

lemma slope_symmetric_bound:
  assumes "slope f"
  obtains C where "\<And>p q. \<bar>p * f q - q * f p\<bar> \<le> (\<bar>p\<bar> + \<bar>q\<bar> + 2) * C" "0 \<le> C"
proof -
  obtain C where bound: "\<bar>f (m + n) - (f m + f n)\<bar> \<le> C" and C_nonneg: "0 \<le> C" for m n using assms by fast
  
  have *: "\<bar>f (p * q) - p * f q\<bar> \<le> (\<bar>p\<bar> + 1) * C" for p q
  proof (induction p rule: int_induct[where ?k=0])
    case base
    then show ?case using bound[of 0 0] by force
  next
    case (step1 p)
    have "\<bar>f ((p + 1) * q) - f (p * q) - f q\<bar> \<le> C" using bound[of "p * q" q]  by (auto simp: distrib_left mult.commute)
    hence "\<bar>f ((p + 1) * q) - f q - p * f q\<bar> \<le> C + (\<bar>p\<bar> + 1) * C" using step1 by fastforce
    thus ?case using step1 by (auto simp add: distrib_left mult.commute)
  next
    case (step2 p)
    have "\<bar>f ((p - 1) * q) + f q - f (p * q)\<bar> \<le> C" using bound[of "p * q - q" "q"] by (auto simp: mult.commute right_diff_distrib')
    hence "\<bar>f ((p - 1) * q) + f q - p * f q\<bar> \<le> C + (\<bar>p\<bar> + 1) * C" using step2 by force
    hence "\<bar>f ((p - 1) * q) - (p - 1) * f q\<bar> \<le> C + (\<bar>p - 1\<bar>) * C" using step2 by (auto simp: mult.commute right_diff_distrib')
    thus ?case by (auto simp add: distrib_left mult.commute)
  qed

  have "\<bar>p * f q - q * f p\<bar> \<le> (\<bar>p\<bar> + \<bar>q\<bar> + 2) * C" for p q
  proof -
    have "\<bar>p * f q - q * f p\<bar> \<le> \<bar>f (p * q) - p * f q\<bar> + \<bar>f (q * p) - q * f p\<bar>" by (fastforce simp: mult.commute)
    also have "... \<le> (\<bar>p\<bar> + 1) * C + (\<bar>q\<bar> + 1) * C" using *[of p q] *[of q p] by fastforce
    also have "... = (\<bar>p\<bar> + \<bar>q\<bar> + 2) * C" by algebra
    finally show ?thesis .
  qed
  thus ?thesis using that C_nonneg by blast
qed

lemma slope_linear_bound:
  assumes "slope f"
  obtains A B where "\<forall>n. \<bar>f n\<bar> \<le> A * \<bar>n\<bar> + B" "0 \<le> A" "0 \<le> B"
proof -
  obtain C where bound: "\<bar>p * f q - q * f p\<bar> \<le> (\<bar>p\<bar> + \<bar>q\<bar> + 2) * C" "0 \<le> C" for p q using assms slope_symmetric_bound by blast

  have "\<bar>f p\<bar> \<le> (C + \<bar>f 1\<bar>) * \<bar>p\<bar> + 3 * C" for p
  proof -
    have "\<bar>p * f 1 - f p\<bar> \<le> (\<bar>p\<bar> + 3) * C" using bound(1)[of _ 1] by (simp add: add.commute)
    hence "\<bar>f p - p * f 1\<bar> \<le> (\<bar>p\<bar> + 3) * C" by (subst abs_minus[of "f p - p * f 1", symmetric], simp)
    hence "\<bar>f p\<bar> \<le> (\<bar>p\<bar> + 3) * C + \<bar>p * f 1\<bar>" using dual_order.trans abs_triangle_ineq2 diff_le_eq by fast
    hence "\<bar>f p\<bar> \<le> \<bar>p\<bar> * C + 3 * C + \<bar>p\<bar> * \<bar>f 1\<bar>" by (simp add: abs_mult int_distrib(2) mult.commute)
    hence "\<bar>f p\<bar> \<le> \<bar>p\<bar> * (C + \<bar>f 1\<bar>) + 3 * C" by (simp add: ring_class.ring_distribs(1))
    thus ?thesis using mult.commute by metis
  qed
  thus ?thesis using that bound(2) by fastforce
qed

lemma slope_comp:
  assumes "slope f" "slope g"
  shows "slope (f o g)"
proof-
  obtain C where bound: "\<bar>f (m + n) - (f m + f n)\<bar> \<le> C" for m n using assms by fast
  obtain C' where bound': "\<bar>g (m + n) - (g m + g n)\<bar> \<le> C'" for m n using assms by fast
  obtain A B where f_linear_bound: "\<bar>f n\<bar> \<le> A * \<bar>n\<bar> + B" "0 \<le> A" "0 \<le> B" for n using slope_linear_bound[OF assms(1)] by blast
  {
    fix m n
    have "\<bar>f (g (m + n)) - (f (g m) + f (g n))\<bar> \<le> (\<bar>f (g (m + n)) - f (g m + g n)\<bar> + \<bar>f (g m + g n) - (f (g m) + f (g n))\<bar> :: int)" by linarith
    also have "... \<le> \<bar>f (g (m + n)) - f (g m + g n)\<bar> + C" using bound[of "g m" "g n"] by auto
    also have "... \<le> \<bar>f (g (m + n)) - f (g m + g n) - f(g (m + n) - (g m + g n))\<bar> + \<bar>f (g (m + n) - (g m + g n))\<bar> + C" by fastforce
    also have "... \<le> \<bar>f (g (m + n) - (g m + g n))\<bar> + 2 * C" using bound[of "g (m + n) - (g m + g n)" "(g m + g n)"] by fastforce
    also have "... \<le> A * \<bar>g (m + n) - (g m + g n)\<bar> + B + 2 * C" using f_linear_bound(1)[of "g (m + n) - (g m + g n)"] by linarith
    also have "... \<le> A * C' + B + 2 * C" using mult_left_mono[OF bound'[of m n], OF f_linear_bound(2)] by presburger
    finally have "\<bar>f (g (m + n)) - (f (g m) + f (g n))\<bar> \<le> A * C' + B + 2 * C" by blast
  }
  thus "slope (f o g)" unfolding comp_def slope_def by (fast intro: boundedI)
qed

lemma slope_scale: "slope ((*) a)" by (auto simp add: slope_def distrib_left intro: boundedI)

lemma slope_zero: "slope (\<lambda>_. 0)" using slope_scale[of 0] by (simp add: lambda_zero)

lemma slope_one: "slope id" using slope_scale[of 1] by (simp add: slope_def)

lemma slope_uminus: "slope uminus" using slope_scale[of "-1"] by (simp add: slope_def)

lemma slope_uminus':
  assumes "slope f"
  shows "slope (\<lambda>x. - f x)"
  using slope_comp[OF slope_uminus assms] by (simp add: slope_def)

lemma slope_minus:
  assumes "slope f" "slope g"
  shows "slope (\<lambda>x. f x - g x)"
  using slope_add[OF assms(1) slope_uminus', OF assms(2)] by simp

lemma slope_comp_commute:
  assumes "slope f" "slope g"
  shows "bounded (\<lambda>z. (f o g) z - (g o f) z)"
proof -
  obtain C where bound: "\<bar>z * f (g z) - (g z) * (f z)\<bar> \<le> (\<bar>z\<bar> + \<bar>g z\<bar> + 2) * C" "0 \<le> C" for z using slope_symmetric_bound[OF assms(1)] by metis
  obtain C' where bound': "\<bar>(f z) * (g z) - z * g (f z)\<bar> \<le> (\<bar>f z\<bar> + \<bar>z\<bar> + 2) * C'" "0 \<le> C'" for z using slope_symmetric_bound[OF assms(2)] by metis

  obtain A B where f_lbound: "\<bar>f z\<bar> \<le> A * \<bar>z\<bar> + B" "0 \<le> A" "0 \<le> B" for z using slope_linear_bound[OF assms(1)] by blast
  obtain A' B' where g_lbound: "\<bar>g z\<bar> \<le> A' * \<bar>z\<bar> + B'" "0 \<le> A'" "0 \<le> B'" for z using slope_linear_bound[OF assms(2)] by blast

  have combined_bound: "\<bar>z * f (g z) - z * g (f z)\<bar> \<le> (\<bar>z\<bar> + \<bar>g z\<bar> + 2) * C + (\<bar>f z\<bar> + \<bar>z\<bar> + 2) * C'" for z 
    by (intro order_trans[OF _ add_mono[OF bound(1) bound'(1)]]) (fastforce simp add: mult.commute[of "f z" "g z"])

  {
    fix z
    define D E where "D = (C + C' + A' * C + A * C')" and "E = (2 + B') * C + (2 + B) * C'"
    have E_nonneg: "0 \<le> E" unfolding E_def using g_lbound bound f_lbound bound' by simp
    have D_nonneg: "0 \<le> D" unfolding D_def using g_lbound bound f_lbound bound' by simp

    have "(\<bar>z\<bar> + \<bar>g z\<bar> + 2) * C + (\<bar>f z\<bar> + \<bar>z\<bar> + 2) * C' = \<bar>z\<bar> * (C + C') + \<bar>g z\<bar> * C + \<bar>f z\<bar> * C' + 2 * C + 2 * C'" by algebra
    hence "\<bar>z\<bar> * \<bar>f (g z) - g (f z)\<bar> \<le> \<bar>z\<bar> * (C + C') + \<bar>g z\<bar> * C + \<bar>f z\<bar> * C' + 2 * C + 2 * C'" using combined_bound right_diff_distrib abs_mult by metis
    also have "... \<le> \<bar>z\<bar> * (C + C') + (A' * \<bar>z\<bar> + B') * C + \<bar>f z\<bar> * C' + 2 * C + 2 * C'" using mult_right_mono[OF g_lbound(1)[of z] bound(2)] by presburger
    also have "... \<le> \<bar>z\<bar> * (C + C') + (A' * \<bar>z\<bar> + B') * C + (A * \<bar>z\<bar> + B) * C' + 2 * C + 2 * C'" using mult_right_mono[OF f_lbound(1)[of z] bound'(2)] by presburger
    also have "... = \<bar>z\<bar> * (C + C' + A' * C + A * C') + (2 + B') * C + (2 + B) * C'" by algebra
    finally have *: "\<bar>z\<bar> * \<bar>f (g z) - g (f z)\<bar> \<le> \<bar>z\<bar> * D + E" unfolding D_def E_def by presburger
    have "\<bar>f (g z) - g (f z)\<bar> \<le> D + E + \<bar>f (g 0) - g (f 0)\<bar>"
    proof (cases "z = 0")
      case True
      then show ?thesis using D_nonneg E_nonneg by fastforce
    next
      case False
      have "\<bar>z\<bar> * \<bar>f (g z) - g (f z)\<bar> \<le> \<bar>z\<bar> * (D + E)" 
        using mult_right_mono[OF Ints_nonzero_abs_ge1[OF _ False] E_nonneg] distrib_left[of "\<bar>z\<bar>" D E] *
        by (simp add: Ints_def)
      hence "\<bar>f (g z) - g (f z)\<bar> \<le> D + E" using False by simp
      thus ?thesis by linarith
    qed
  }
  thus ?thesis by (fastforce intro: boundedI)
qed

lemma int_set_infiniteI:
  assumes "\<And>C. C \<ge> 0 \<Longrightarrow> \<exists>N\<ge>C. N \<in> (A :: int set)" 
  shows "infinite A"
  by (meson assms abs_ge_zero abs_le_iff gt_ex le_cSup_finite linorder_not_less order_less_le_trans)

lemma int_set_infiniteD:
  assumes "infinite (A :: int set)" "C \<ge> 0"
  obtains z where "z \<in> A" "C \<le> \<bar>z\<bar>"
proof -
  {
    assume asm: "\<forall>z \<in> A. C > \<bar>z\<bar>"
    let ?f = "\<lambda>z. (if z \<in> A then z else (0::int))"
    have bounded: "\<forall>z \<in> A. \<bar>?f z\<bar> \<le> C" using asm by fastforce
    moreover have "\<forall>z \<in> UNIV - A. \<bar>?f z\<bar> \<le> C" using assms by fastforce
    ultimately have "bounded ?f" by (blast intro: boundedI)
    hence False using bounded_iff_finite_range assms by force
  }
  thus ?thesis using that by fastforce
qed

lemma bounded_odd:
  fixes f :: "int \<Rightarrow> int"
  assumes "\<And>z. z < 0 \<Longrightarrow> f z = -f (-z)" "\<And>n. n > 0 \<Longrightarrow> \<bar>f n\<bar> \<le> C"
  shows "bounded f"
proof -
  have "\<bar>f n\<bar> \<le> C + \<bar>f 0\<bar>" if "n \<ge> 0" for n using assms by (metis abs_ge_zero abs_of_nonneg add_increasing2 le_add_same_cancel2 that zero_less_abs_iff)
  hence "\<bar>f n\<bar> \<le> C + \<bar>f 0\<bar>" for n using assms by (cases "0 \<le> n") fastforce+
  thus ?thesis by (rule boundedI)
qed

lemma slope_odd: 
  assumes "\<And>z. z < 0 \<Longrightarrow> f z = - f (- z)" 
          "\<And>m n. \<lbrakk>m > 0; n > 0\<rbrakk> \<Longrightarrow> \<bar>f (m + n) - (f m + f n)\<bar> \<le> C"
  shows "slope f"
proof -
  define C' where "C' = C + \<bar>f 0\<bar>"
  have "C \<ge> 0" using assms(2)[of 1 1] by simp
  hence bound: "\<bar>f (m + n) - (f m + f n)\<bar> \<le> C'" if "m \<ge> 0" "n \<ge> 0" for m n 
    unfolding C'_def using assms(2) that 
    by (cases "m = 0 \<or> n = 0") (force, metis abs_ge_zero add_increasing2 order_le_less)
  {
    fix m n
    have "\<bar>f (m + n) - (f m + f n)\<bar> \<le> C'"
    proof (cases "m \<ge> 0")
      case m_nonneg: True
      show ?thesis
      proof (cases "n \<ge> 0")
        case True
        thus ?thesis using bound m_nonneg by fast
      next
        case False
        hence f_n: "f n = - f (- n)" using assms by simp
        show ?thesis
        proof (cases "m + n \<ge> 0")
          case True
          have "\<bar>f (m + n) - (f m + f n)\<bar> = \<bar>f (m + n + -n) - (f (m + n) + f (-n))\<bar>" using f_n by auto
          thus ?thesis using bound[OF True] by (metis False neg_0_le_iff_le nle_le)
        next
          case False
          hence "f (m + n) = - f (- (m + n))" using assms by force
          hence "\<bar>f (m + n) - (f m + f n)\<bar> = \<bar>f (- (m + n) + m) - (f (- (m + n)) + f m)\<bar>" using f_n by force
          thus ?thesis using m_nonneg bound[of "- (m + n)" m] False by simp
        qed
      qed
    next
      case m_neg: False
      hence f_m: "f m = - f (- m)" using assms by simp
      show ?thesis
      proof (cases "n \<ge> 0")
        case True
        show ?thesis
        proof (cases "m + n \<ge> 0")
          case True
          have "\<bar>f (m + n) - (f m + f n)\<bar> = \<bar>f (m + n + -m) - (f (m + n) + f (-m))\<bar>" using f_m by force
          thus ?thesis using bound[OF True, of "- m"] m_neg by simp
        next
          case False
          hence "f (m + n) = - f (- (m + n))" using assms by force
          hence"\<bar>f (m + n) - (f m + f n)\<bar> = \<bar>f (- (m + n) + n) - (f (- (m + n)) + f n)\<bar>" using f_m by force
          thus ?thesis using bound[of "- (m + n)" n] True False by simp
        qed
      next
        case False
        hence f_n: "f n = - f (- n)" using assms by simp
        have "f (m + n) = - f (- m + - n)" using m_neg False assms by fastforce
        hence "\<bar>f (m + n) - (f m + f n)\<bar> = \<bar>- f (- m + -n) - (- f (-m) + - f(- n))\<bar>" using f_m f_n by argo
        also have "... = \<bar>f (-m + -n) - (f (-m) + f(-n))\<bar>" by linarith
        finally show ?thesis using bound[of "- m" "- n"] False m_neg by simp
      qed
    qed
  }
  thus ?thesis unfolding slope_def by (fast intro: boundedI)
qed

lemma slope_bounded_comp_right_abs:
  assumes "slope f" "bounded (f o abs)"
  shows "bounded f"
proof -
  obtain B where "\<forall>z. \<bar>f \<bar>z\<bar>\<bar> \<le> B" and B_nonneg: "0 \<le> B" using assms by fastforce
  hence B_bound: "\<forall>z \<ge> 0. \<bar>f z\<bar> \<le> B" by (metis abs_of_nonneg)

  obtain D where D_bound: "\<bar>f (m + n) - (f m + f n)\<bar> \<le> D" and D_nonneg: "0 \<le> D" for m n using assms by fast

  have bound: "\<bar>f (-m)\<bar> \<le> \<bar>f 0\<bar> + B + D" if "m \<ge> 0" for m using D_bound[of "-m" m] B_bound that by auto

  have "\<bar>f z\<bar> \<le> \<bar>f 0\<bar> + B + D" for z using B_bound B_nonneg D_nonneg bound[of "-z"] by (cases "z \<ge> 0") fastforce+
  thus "bounded f" by (rule boundedI)
qed

corollary slope_finite_range_iff:
  assumes "slope f"
  shows "finite (range f) \<longleftrightarrow> finite (f ` {0..})" (is "?lhs \<longleftrightarrow> ?rhs")
proof (rule iffI)
  assume asm: ?rhs
  have "range (f o abs) = f ` {0..}" unfolding comp_def atLeast_def image_def by (metis UNIV_I abs_ge_zero abs_of_nonneg mem_Collect_eq)
  thus ?lhs using slope_bounded_comp_right_abs[OF assms] asm by (fastforce simp add: bounded_iff_finite_range)
qed (metis image_subsetI rangeI finite_subset)

lemma slope_positive_lower_bound:
  assumes "slope f" "infinite (f ` {0..} \<inter> {0<..})" "D > 0"
  obtains M where "M > 0" "\<And>m. m > 0 \<Longrightarrow> (m + 1) * D \<le> f (m * M)"
proof -
  {
    have D_nonneg: "D \<ge> 0" using assms by force
    obtain C where C_bound: "\<bar>f (m + n) - (f m + f n)\<bar> \<le> C" and C_nonneg: "0 \<le> C" for m n using assms by fast

    obtain f_M where "2 * (C + D) \<le> \<bar>f_M\<bar>" "f_M \<in> (f ` {0..} \<inter> {0<..})" using mult_left_mono[of "C + D" _ 2] D_nonneg by (metis assms(2) abs_ge_zero abs_le_D1 int_set_infiniteD)
    then obtain M where M_bound: "2 * (C + D) \<le> \<bar>f M\<bar>" "0 < f M" and M_nonneg: "0 \<le> M" by blast
  
    have neg_bound: "(f (m * M + M) - (f (m * M) + f M)) \<ge> -C" for m by (metis C_bound abs_diff_le_iff minus_int_code(1,2))
    hence neg_bound': "(f (m * M + M) - (f (m * M) + f M)) \<ge> -(C + D)" for m by (meson D_nonneg add_increasing2 minus_le_iff)
  
    have *: "m > 0 \<Longrightarrow> f (m * M) \<ge> (m + 1) * (C + D)" for m
    proof (induction m rule: int_induct[where ?k=1])
      case base
      show ?case using M_bound by fastforce
    next
      case (step1 m)
      have "(m + 1 + 1) * (C + D) = (m + 1) * (C + D) + 2 * (C + D) - (C + D)" by algebra
      also have "... \<le> (m + 1) * (C + D) + f M + - (C + D)" using M_bound by fastforce
      also have "... \<le> f (m * M) + f M + - (C + D)" using step1 by simp
      also have "... \<le> (f (m * M) + f M) + (f (m * M + M) - (f (m * M) + f M))" using add_left_mono[OF neg_bound'] by blast
      also have "... = f ((m + 1) * M)" by (simp add: distrib_right)
      finally show ?case by blast
    next
      case (step2 i)
      then show ?case by linarith
    qed
  
    have *: "f (m * M) \<ge> (m + 1) * D" if "m > 0" for m using *[OF that] mult_left_mono[of D "C + D" "m + 1"] that C_nonneg D_nonneg by linarith
    moreover have "M \<noteq> 0" using M_bound add1_zle_eq assms neg_bound by force
    ultimately have "\<exists>M>0. \<forall>m>0. (m + 1) * D \<le> f (m * M) " using M_nonneg by force
  }
  thus ?thesis using that by blast
qed

subsection \<open>Set Membership of \<^term>\<open>Inf\<close> and \<^term>\<open>Sup\<close> on Integers\<close>

lemma int_Inf_mem:
  fixes S :: "int set"
  assumes "S \<noteq> {}" "bdd_below S"
  shows "Inf S \<in> S"
proof -
  have nonneg: "Inf ({0..} \<inter> A) \<in> ({0..} \<inter> A)" if asm: "({(0::int)..} \<inter> A) \<noteq> {}" for A
  proof -
    have "nat ` ({0..} \<inter> A) \<noteq> {}" using asm by blast
    hence "int (Inf (nat ` ({0..} \<inter> A))) \<in> int ` nat ` ({0..} \<inter> A)" using wellorder_InfI[of _ "nat ` ({0..} \<inter> A)"] by fast
    moreover have "int ` nat ` ({0..} \<inter> A) = {0..} \<inter> A" by force
    moreover have "Inf ({0..} \<inter> A) = int (Inf (nat ` ({0..} \<inter> A)))" 
      using calculation by (intro cInf_eq_minimum) (argo, metis IntD2 Int_commute atLeast_iff imageI le_nat_iff wellorder_Inf_le1)
    ultimately show ?thesis by argo
  qed
  have **: "Inf ({b..} \<inter> A) \<in> ({b..} \<inter> A)" if asm: "({(b::int)..} \<inter> A) \<noteq> {}" for A b
  proof (cases "b \<ge> 0")
    case True
    hence "({b..} \<inter> A) = {0..} \<inter> ({b..} \<inter> A)" by fastforce
    thus ?thesis using asm nonneg by metis
  next
    case False
    hence partition: "({b..} \<inter> A) = ({0..} \<inter> A) \<union> ({b..<0} \<inter> A)" by fastforce
    have bdd_below: "bdd_below ({0..} \<inter> A)" "bdd_below ({b..<0} \<inter> A)" by simp+
    thus ?thesis 
    proof (cases "({0..} \<inter> A) \<noteq> {} \<and> ({b..<0} \<inter> A) \<noteq> {}")
      case True
      have finite: "finite ({b..<0} \<inter> A)" by blast
      have "(x :: int) \<le> y \<Longrightarrow> inf x y = x" for x y by (simp add: inf.order_iff)
      have "Inf ({b..} \<inter> A) = inf (Inf ({0..} \<inter> A)) (Inf ({b..<0} \<inter> A))" by (metis cInf_union_distrib True bdd_below partition)
      moreover have "Inf ({b..<0} \<inter> A) \<in> ({b..} \<inter> A)" using Min_in[OF finite] cInf_eq_Min[OF finite] True partition by simp
      moreover have "Inf ({0..} \<inter> A) \<in> ({b..} \<inter> A)" using nonneg True partition by blast
      moreover have "inf (Inf ({0..} \<inter> A)) (Inf ({b..<0} \<inter> A)) \<in> {Inf ({0..} \<inter> A), Inf ({b..<0} \<inter> A)}" by (metis inf.commute inf.order_iff insertI1 insertI2 nle_le)
      ultimately show ?thesis by force
    next
      case False
      hence "({b..} \<inter> A) = ({0..} \<inter> A) \<or> ({b..} \<inter> A) = ({b..<0} \<inter> A)" using partition by auto
      thus ?thesis using Min_in[of "{b..} \<inter> A"] cInf_eq_Min[of "{b..} \<inter> A"] by (metis asm nonneg finite_Int finite_atLeastLessThan_int)
    qed
  qed
  obtain b where "S = {b..} \<inter> S" using assms unfolding bdd_below_def by blast
  thus ?thesis using ** assms by metis
qed

lemma int_Sup_mem:
  fixes S :: "int set"
  assumes "S \<noteq> {}" "bdd_above S"
  shows "Sup S \<in> S"
proof -
  have "Sup S = (- Inf (uminus ` S))" unfolding Inf_int_def image_comp by simp
  moreover have "bdd_below (uminus ` S)" using assms unfolding bdd_below_def bdd_above_def by (metis imageE neg_le_iff_le)
  moreover have "Inf (uminus ` S) \<in> (uminus ` S)" using int_Inf_mem assms by simp
  ultimately show ?thesis by force
qed

end