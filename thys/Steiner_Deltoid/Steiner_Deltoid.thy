(*  Title:      Steiner_Deltoid.thy
    Author:     Arthur Freitas Ramos, David Barros Hulak,
                Ruy Jose Guerra Barretto de Queiroz, 2026
    Maintainer: Arthur Freitas Ramos

The Steiner deltoid as the envelope of the Wallace--Simson lines.
*)

theory Steiner_Deltoid
  imports "Simson.Simson" "HOL-Analysis.Derivative"
begin

hide_const (open) Linear_Algebra.collinear

section \<open>The deltoid parametrisation\<close>

text \<open>We use circumcentre coordinates with the circumcircle as the unit
circle.  In these coordinates the classical parametrisation of the Steiner
deltoid is
\[
  d(m) = (a+b+c)/2 + m + abc\,\overline m^2/2.
\]
The unit-circle hypothesis turns the last term into the more familiar
\(abc/(2m^2)\).\<close>

definition steiner_deltoid_point ::
    "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex"
  where "steiner_deltoid_point a b c m =
    (a + b + c) / 2 + m + a * b * c * (cnj m)\<^sup>2 / 2"

definition steiner_deltoid ::
    "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex set"
  where "steiner_deltoid a b c =
    {steiner_deltoid_point a b c m | m. oncircle 0 1 m}"

definition steiner_deltoid_normal ::
    "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex"
  where "steiner_deltoid_normal a b c m = m - a * b * c * (cnj m)\<^sup>2"

text \<open>For the differential-geometric statements we use the standard real
parameter on the unit circle.  Written without conjugation, the curve is
\[
  \gamma(t)=(a+b+c)/2+e^{it}+abc\,e^{-2it}/2.
\]
At a regular parameter the tangent direction is \(iN(m)\).  At a stationary
parameter we use the first nonzero direction, namely the second derivative
\(-3m\).\<close>

definition unit_circle_param :: "real \<Rightarrow> complex"
  where "unit_circle_param t = exp (t *\<^sub>R \<i>)"

definition steiner_deltoid_curve ::
    "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> real \<Rightarrow> complex"
  where "steiner_deltoid_curve a b c t =
    (a + b + c) / 2 + exp (t *\<^sub>R \<i>) +
      a * b * c * (cnj (exp (t *\<^sub>R \<i>)))\<^sup>2 / 2"

definition steiner_deltoid_tangent_direction_at ::
    "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex"
  where "steiner_deltoid_tangent_direction_at a b c m =
    (if steiner_deltoid_normal a b c m = 0 then m
     else \<i> * steiner_deltoid_normal a b c m)"

definition steiner_deltoid_tangent ::
    "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> real \<Rightarrow> complex set"
  where "steiner_deltoid_tangent a b c t =
    {z. on_line (steiner_deltoid_curve a b c t)
      (steiner_deltoid_curve a b c t +
        steiner_deltoid_tangent_direction_at a b c
          (unit_circle_param t)) z}"

definition steiner_deltoid_tangent_at ::
    "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex set"
  where "steiner_deltoid_tangent_at a b c m =
    {z. on_line (steiner_deltoid_point a b c m)
      (steiner_deltoid_point a b c m +
        steiner_deltoid_tangent_direction_at a b c m) z}"

lemma unit_circle_param_oncircle:
  shows "oncircle 0 1 (unit_circle_param t)"
  unfolding unit_circle_param_def oncircle_def
  by simp

lemma steiner_deltoid_curve_eq_point:
  shows "steiner_deltoid_curve a b c t =
      steiner_deltoid_point a b c (unit_circle_param t)"
  unfolding steiner_deltoid_curve_def steiner_deltoid_point_def
    unit_circle_param_def
  by simp

lemma steiner_deltoid_tangent_eq_tangent_at:
  shows "steiner_deltoid_tangent a b c t =
      steiner_deltoid_tangent_at a b c (unit_circle_param t)"
  unfolding steiner_deltoid_tangent_def steiner_deltoid_tangent_at_def
  by (simp add: steiner_deltoid_curve_eq_point)

lemma steiner_deltoid_curve_has_vector_derivative:
  shows "((\<lambda>t. steiner_deltoid_curve a b c t)
      has_vector_derivative
        \<i> * steiner_deltoid_normal a b c (unit_circle_param t)) (at t)"
proof -
  have h1:
      "((\<lambda>t. exp (t *\<^sub>R \<i>))
        has_vector_derivative exp (t *\<^sub>R \<i>) * \<i>) (at t)"
    by (rule exp_scaleR_has_vector_derivative_right)
  have hconj:
      "((\<lambda>t. cnj (exp (t *\<^sub>R \<i>)))
        has_vector_derivative cnj (exp (t *\<^sub>R \<i>) * \<i>)) (at t)"
    by (rule has_vector_derivative_cnj[OF h1])
  have hsquare:
      "((\<lambda>t. cnj (exp (t *\<^sub>R \<i>)) * cnj (exp (t *\<^sub>R \<i>)))
        has_vector_derivative
          cnj (exp (t *\<^sub>R \<i>)) * cnj (exp (t *\<^sub>R \<i>) * \<i>) +
          cnj (exp (t *\<^sub>R \<i>) * \<i>) * cnj (exp (t *\<^sub>R \<i>))) (at t)"
    by (rule has_vector_derivative_mult[OF hconj hconj])
  have hmul:
      "((\<lambda>t. a * b * c *
          (cnj (exp (t *\<^sub>R \<i>)) * cnj (exp (t *\<^sub>R \<i>))))
        has_vector_derivative
          a * b * c *
            (cnj (exp (t *\<^sub>R \<i>)) * cnj (exp (t *\<^sub>R \<i>) * \<i>) +
              cnj (exp (t *\<^sub>R \<i>) * \<i>) * cnj (exp (t *\<^sub>R \<i>)))) (at t)"
    by (rule has_vector_derivative_mult_right[OF hsquare])
  have hsecond:
      "((\<lambda>t. a * b * c * (cnj (exp (t *\<^sub>R \<i>)))\<^sup>2 / 2)
        has_vector_derivative
          (a * b * c *
            (cnj (exp (t *\<^sub>R \<i>)) * cnj (exp (t *\<^sub>R \<i>) * \<i>) +
              cnj (exp (t *\<^sub>R \<i>) * \<i>) * cnj (exp (t *\<^sub>R \<i>)))) / 2) (at t)"
    using has_vector_derivative_divide[where a = "2::complex", OF hmul]
    by (simp add: power2_eq_square)
  have hadd:
      "((\<lambda>t. (a + b + c) / 2 + exp (t *\<^sub>R \<i>))
        has_vector_derivative
          0 + exp (t *\<^sub>R \<i>) * \<i>) (at t)"
    by (rule has_vector_derivative_add[OF has_vector_derivative_const h1])
  have hsum0:
      "((\<lambda>t. ((a + b + c) / 2 + exp (t *\<^sub>R \<i>)) +
          a * b * c * (cnj (exp (t *\<^sub>R \<i>)))\<^sup>2 / 2)
        has_vector_derivative
          (0 + exp (t *\<^sub>R \<i>) * \<i>) +
            (a * b * c *
              (cnj (exp (t *\<^sub>R \<i>)) * cnj (exp (t *\<^sub>R \<i>) * \<i>) +
                cnj (exp (t *\<^sub>R \<i>) * \<i>) * cnj (exp (t *\<^sub>R \<i>)))) / 2) (at t)"
    by (rule has_vector_derivative_add[OF hadd hsecond])
  have hsum:
      "((\<lambda>t. (a + b + c) / 2 + exp (t *\<^sub>R \<i>) +
          a * b * c * (cnj (exp (t *\<^sub>R \<i>)))\<^sup>2 / 2)
        has_vector_derivative
          exp (t *\<^sub>R \<i>) * \<i> +
            (a * b * c *
              (cnj (exp (t *\<^sub>R \<i>)) * cnj (exp (t *\<^sub>R \<i>) * \<i>) +
                cnj (exp (t *\<^sub>R \<i>) * \<i>) * cnj (exp (t *\<^sub>R \<i>)))) / 2) (at t)"
    using hsum0 by (simp add: algebra_simps)
  show ?thesis
    using hsum
    by (simp add: steiner_deltoid_curve_def steiner_deltoid_normal_def
        unit_circle_param_def power2_eq_square
        algebra_simps)
qed

definition steiner_deltoid_curve_second_derivative ::
    "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> real \<Rightarrow> complex"
  where "steiner_deltoid_curve_second_derivative a b c t =
    - unit_circle_param t -
      2 * a * b * c * (cnj (unit_circle_param t))\<^sup>2"

definition steiner_deltoid_curve_third_derivative ::
    "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> real \<Rightarrow> complex"
  where "steiner_deltoid_curve_third_derivative a b c t =
    - \<i> * unit_circle_param t +
      4 * \<i> * a * b * c * (cnj (unit_circle_param t))\<^sup>2"

definition complex_real_linearly_independent ::
    "complex \<Rightarrow> complex \<Rightarrow> bool"
  where "complex_real_linearly_independent u v \<longleftrightarrow>
    \<not> collinear 0 u v"

definition ordinary_cusp_parameter ::
    "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> real \<Rightarrow> bool"
  where "ordinary_cusp_parameter a b c t \<longleftrightarrow>
    vector_derivative (\<lambda>u. steiner_deltoid_curve a b c u) (at t) = 0
    \<and> steiner_deltoid_curve_second_derivative a b c t \<noteq> 0
    \<and> steiner_deltoid_curve_third_derivative a b c t \<noteq> 0
    \<and> complex_real_linearly_independent
      (steiner_deltoid_curve_second_derivative a b c t)
      (steiner_deltoid_curve_third_derivative a b c t)"

lemma steiner_deltoid_curve_first_derivative_has_vector_derivative:
  shows "((\<lambda>t. \<i> *
      steiner_deltoid_normal a b c (unit_circle_param t))
      has_vector_derivative
        steiner_deltoid_curve_second_derivative a b c t) (at t)"
proof -
  have h1:
      "((\<lambda>t. exp (t *\<^sub>R \<i>))
        has_vector_derivative exp (t *\<^sub>R \<i>) * \<i>) (at t)"
    by (rule exp_scaleR_has_vector_derivative_right)
  have hconj:
      "((\<lambda>t. cnj (exp (t *\<^sub>R \<i>)))
        has_vector_derivative cnj (exp (t *\<^sub>R \<i>) * \<i>)) (at t)"
    by (rule has_vector_derivative_cnj[OF h1])
  have hsquare:
      "((\<lambda>t. cnj (exp (t *\<^sub>R \<i>)) *
          cnj (exp (t *\<^sub>R \<i>)))
        has_vector_derivative
          cnj (exp (t *\<^sub>R \<i>)) * cnj (exp (t *\<^sub>R \<i>) * \<i>) +
          cnj (exp (t *\<^sub>R \<i>) * \<i>) *
            cnj (exp (t *\<^sub>R \<i>))) (at t)"
    by (rule has_vector_derivative_mult[OF hconj hconj])
  have hmul:
      "((\<lambda>t. a * b * c *
          (cnj (exp (t *\<^sub>R \<i>)) * cnj (exp (t *\<^sub>R \<i>))))
        has_vector_derivative
          a * b * c *
            (cnj (exp (t *\<^sub>R \<i>)) * cnj (exp (t *\<^sub>R \<i>) * \<i>) +
              cnj (exp (t *\<^sub>R \<i>) * \<i>) *
                cnj (exp (t *\<^sub>R \<i>)))) (at t)"
    by (rule has_vector_derivative_mult_right[OF hsquare])
  have hnormal:
      "((\<lambda>t. exp (t *\<^sub>R \<i>) - a * b * c *
          (cnj (exp (t *\<^sub>R \<i>)) * cnj (exp (t *\<^sub>R \<i>))))
        has_vector_derivative
          exp (t *\<^sub>R \<i>) * \<i> -
            a * b * c *
              (cnj (exp (t *\<^sub>R \<i>)) * cnj (exp (t *\<^sub>R \<i>) * \<i>) +
                cnj (exp (t *\<^sub>R \<i>) * \<i>) *
                  cnj (exp (t *\<^sub>R \<i>)))) (at t)"
    by (rule has_vector_derivative_diff[OF h1 hmul])
  have hi:
      "((\<lambda>t. \<i> *
          (exp (t *\<^sub>R \<i>) - a * b * c *
            (cnj (exp (t *\<^sub>R \<i>)) * cnj (exp (t *\<^sub>R \<i>)))))
        has_vector_derivative
          \<i> *
            (exp (t *\<^sub>R \<i>) * \<i> -
              a * b * c *
                (cnj (exp (t *\<^sub>R \<i>)) * cnj (exp (t *\<^sub>R \<i>) * \<i>) +
                  cnj (exp (t *\<^sub>R \<i>) * \<i>) *
                    cnj (exp (t *\<^sub>R \<i>))))) (at t)"
    by (rule has_vector_derivative_mult_right[OF hnormal])
  show ?thesis
    using hi
    by (simp add: steiner_deltoid_normal_def
        steiner_deltoid_curve_second_derivative_def
        unit_circle_param_def power2_eq_square algebra_simps)
qed

lemma steiner_deltoid_curve_second_derivative_has_vector_derivative:
  shows "((\<lambda>t. steiner_deltoid_curve_second_derivative a b c t)
      has_vector_derivative
        steiner_deltoid_curve_third_derivative a b c t) (at t)"
proof -
  have h1:
      "((\<lambda>t. exp (t *\<^sub>R \<i>))
        has_vector_derivative exp (t *\<^sub>R \<i>) * \<i>) (at t)"
    by (rule exp_scaleR_has_vector_derivative_right)
  have hconj:
      "((\<lambda>t. cnj (exp (t *\<^sub>R \<i>)))
        has_vector_derivative cnj (exp (t *\<^sub>R \<i>) * \<i>)) (at t)"
    by (rule has_vector_derivative_cnj[OF h1])
  have hsquare:
      "((\<lambda>t. cnj (exp (t *\<^sub>R \<i>)) *
          cnj (exp (t *\<^sub>R \<i>)))
        has_vector_derivative
          cnj (exp (t *\<^sub>R \<i>)) * cnj (exp (t *\<^sub>R \<i>) * \<i>) +
          cnj (exp (t *\<^sub>R \<i>) * \<i>) *
            cnj (exp (t *\<^sub>R \<i>))) (at t)"
    by (rule has_vector_derivative_mult[OF hconj hconj])
  have hmul:
      "((\<lambda>t. 2 * a * b * c *
          (cnj (exp (t *\<^sub>R \<i>)) * cnj (exp (t *\<^sub>R \<i>))))
        has_vector_derivative
          2 * a * b * c *
            (cnj (exp (t *\<^sub>R \<i>)) * cnj (exp (t *\<^sub>R \<i>) * \<i>) +
              cnj (exp (t *\<^sub>R \<i>) * \<i>) *
                cnj (exp (t *\<^sub>R \<i>)))) (at t)"
    by (rule has_vector_derivative_mult_right[OF hsquare])
  have hneg:
      "((\<lambda>t. - exp (t *\<^sub>R \<i>))
        has_vector_derivative -(exp (t *\<^sub>R \<i>) * \<i>)) (at t)"
    by (rule has_vector_derivative_minus[OF h1])
  have hsum:
      "((\<lambda>t. - exp (t *\<^sub>R \<i>) - 2 * a * b * c *
          (cnj (exp (t *\<^sub>R \<i>)) * cnj (exp (t *\<^sub>R \<i>))))
        has_vector_derivative
          -(exp (t *\<^sub>R \<i>) * \<i>) -
            2 * a * b * c *
              (cnj (exp (t *\<^sub>R \<i>)) * cnj (exp (t *\<^sub>R \<i>) * \<i>) +
                cnj (exp (t *\<^sub>R \<i>) * \<i>) *
                  cnj (exp (t *\<^sub>R \<i>)))) (at t)"
    by (rule has_vector_derivative_diff[OF hneg hmul])
  show ?thesis
    using hsum
    by (simp add: steiner_deltoid_curve_second_derivative_def
        steiner_deltoid_curve_third_derivative_def
        unit_circle_param_def power2_eq_square algebra_simps)
qed

lemma steiner_deltoid_point_mem:
  assumes "oncircle 0 1 m"
  shows "steiner_deltoid_point a b c m \<in> steiner_deltoid a b c"
  using assms by (auto simp add: steiner_deltoid_def)

lemma unit_cnj:
  assumes "oncircle 0 1 z"
  shows "cnj z = 1 / z"
  using cnj_diff_on_circle[OF assms zero_less_one] by simp

lemma unit_nonzero:
  assumes "oncircle 0 1 z"
  shows "z \<noteq> 0"
  using oncircle_ne_centre[OF assms zero_less_one] by simp

lemma steiner_deltoid_normal_eq_zero_iff_cube:
  assumes hm: "oncircle 0 1 m"
  shows "steiner_deltoid_normal a b c m = 0 \<longleftrightarrow>
    m ^ 3 = a * b * c"
proof -
  have hcm: "cnj m = 1 / m" using unit_cnj[OF hm] .
  have hm0: "m \<noteq> 0" using unit_nonzero[OF hm] .
  show ?thesis
    unfolding steiner_deltoid_normal_def
    using hm0
    by (simp add: hcm field_simps; algebra)
qed

lemma steiner_deltoid_normal_nonzero_iff_cube_neq:
  assumes hm: "oncircle 0 1 m"
  shows "steiner_deltoid_normal a b c m \<noteq> 0 \<longleftrightarrow>
    m ^ 3 \<noteq> a * b * c"
  using steiner_deltoid_normal_eq_zero_iff_cube[OF hm] by blast

theorem steiner_deltoid_curve_derivative_zero_iff:
  shows "vector_derivative (\<lambda>t. steiner_deltoid_curve a b c t) (at t) = 0
    \<longleftrightarrow> (unit_circle_param t) ^ 3 = a * b * c"
proof -
  have hderiv:
      "vector_derivative (\<lambda>t. steiner_deltoid_curve a b c t) (at t) =
        \<i> * steiner_deltoid_normal a b c (unit_circle_param t)"
    by (rule vector_derivative_at
        [OF steiner_deltoid_curve_has_vector_derivative])
  have hnormal:
      "steiner_deltoid_normal a b c (unit_circle_param t) = 0
        \<longleftrightarrow> (unit_circle_param t) ^ 3 = a * b * c"
    by (rule steiner_deltoid_normal_eq_zero_iff_cube
        [OF unit_circle_param_oncircle])
  show ?thesis
    using hderiv hnormal by simp
qed

lemma steiner_deltoid_curve_second_derivative_stationary:
  fixes a b c :: complex and t :: real
  assumes hcube: "(unit_circle_param t) ^ 3 = a * b * c"
  shows "steiner_deltoid_curve_second_derivative a b c t =
      -3 * unit_circle_param t"
proof -
  have hm: "oncircle 0 1 (unit_circle_param t)"
    by (rule unit_circle_param_oncircle)
  have hnormal:
      "steiner_deltoid_normal a b c (unit_circle_param t) = 0"
    using steiner_deltoid_normal_eq_zero_iff_cube[OF hm] hcube by blast
  have hprod:
      "a * (b * (c * (cnj (unit_circle_param t))\<^sup>2)) =
        unit_circle_param t"
    using hnormal by (simp add: steiner_deltoid_normal_def; algebra)
  show ?thesis
    unfolding steiner_deltoid_curve_second_derivative_def
    using hprod by (simp add: hprod; algebra)
qed

lemma steiner_deltoid_curve_third_derivative_stationary:
  fixes a b c :: complex and t :: real
  assumes hcube: "(unit_circle_param t) ^ 3 = a * b * c"
  shows "steiner_deltoid_curve_third_derivative a b c t =
      3 * \<i> * unit_circle_param t"
proof -
  have hm: "oncircle 0 1 (unit_circle_param t)"
    by (rule unit_circle_param_oncircle)
  have hnormal:
      "steiner_deltoid_normal a b c (unit_circle_param t) = 0"
    using steiner_deltoid_normal_eq_zero_iff_cube[OF hm] hcube by blast
  have hprod:
      "a * (b * (c * (cnj (unit_circle_param t))\<^sup>2)) =
        unit_circle_param t"
    using hnormal by (simp add: steiner_deltoid_normal_def; algebra)
  show ?thesis
    unfolding steiner_deltoid_curve_third_derivative_def
    using hprod by (simp add: hprod algebra_simps; algebra)
qed

lemma complex_perpendicular_cusp_directions:
  assumes hm: "oncircle 0 1 m"
  shows "complex_perpendicular (-3 * m) (3 * \<i> * m)"
proof -
  have hnorm: "m * cnj m = 1"
    using oncircle_norm_sq[OF hm] by simp
  show ?thesis
    unfolding complex_perpendicular_def
    using hnorm by (simp add: algebra_simps)
qed

lemma complex_perpendicular_imp_real_linearly_independent:
  fixes u v :: complex
  assumes hperp: "complex_perpendicular u v"
    and hu: "u \<noteq> 0" and hv: "v \<noteq> 0"
  shows "complex_real_linearly_independent u v"
proof -
  show ?thesis
    unfolding complex_real_linearly_independent_def
  proof
    assume hcol: "collinear 0 u v"
    have him:
        "Im (cnj u * v) = 0"
      using collinear_iff_cross[of 0 u v] hcol by simp
    have hRe: "Re (cnj u * v) = 0"
      using hperp unfolding complex_perpendicular_def .
    have "cnj u * v = 0"
      using hRe him by (simp add: complex_eq_iff)
    then show False using hu hv by simp
  qed
qed

theorem steiner_deltoid_stationary_parameter_is_ordinary_cusp:
  fixes a b c :: complex and t :: real
  assumes hcube: "(unit_circle_param t) ^ 3 = a * b * c"
  shows "ordinary_cusp_parameter a b c t"
proof -
  have hm: "oncircle 0 1 (unit_circle_param t)"
    by (rule unit_circle_param_oncircle)
  have hm0: "unit_circle_param t \<noteq> 0"
    using unit_nonzero[OF hm] .
  have hzero:
      "vector_derivative (\<lambda>u. steiner_deltoid_curve a b c u)
          (at t) = 0"
    using steiner_deltoid_curve_derivative_zero_iff[of a b c t]
      hcube by blast
  have hsecond:
      "steiner_deltoid_curve_second_derivative a b c t \<noteq> 0"
    using steiner_deltoid_curve_second_derivative_stationary[OF hcube] hm0
    by simp
  have hthird:
      "steiner_deltoid_curve_third_derivative a b c t \<noteq> 0"
    using steiner_deltoid_curve_third_derivative_stationary[OF hcube] hm0
    by simp
  have hperp:
      "complex_perpendicular
        (steiner_deltoid_curve_second_derivative a b c t)
        (steiner_deltoid_curve_third_derivative a b c t)"
    using complex_perpendicular_cusp_directions[OF hm]
      steiner_deltoid_curve_second_derivative_stationary[OF hcube]
      steiner_deltoid_curve_third_derivative_stationary[OF hcube]
    by simp
  have hind:
      "complex_real_linearly_independent
        (steiner_deltoid_curve_second_derivative a b c t)
        (steiner_deltoid_curve_third_derivative a b c t)"
    by (rule complex_perpendicular_imp_real_linearly_independent
      [OF hperp hsecond hthird])
  show ?thesis
    unfolding ordinary_cusp_parameter_def
    using hzero hsecond hthird hind by blast
qed

lemma foot_unit:
  fixes a b m :: complex
  assumes ha: "oncircle 0 1 a" and hb: "oncircle 0 1 b"
    and ab: "a \<noteq> b"
  shows "foot a b m = (a + b + m - a * b * cnj m) / 2"
proof -
  have h:
      "foot a b m =
        0 + (a - 0 + (m - 0)) / 2 +
          (b - 0) * (complex_of_real (1\<^sup>2) -
            cnj (m - 0) * (a - 0)) /
            (2 * complex_of_real (1\<^sup>2))"
    by (rule foot_general[OF ha hb zero_less_one ab])
  have "foot a b m =
      0 + (a - 0 + (m - 0)) / 2 +
        (b - 0) * (complex_of_real (1\<^sup>2) -
          cnj (m - 0) * (a - 0)) /
          (2 * complex_of_real (1\<^sup>2))"
    using h .
  also have "... = (a + b + m - a * b * cnj m) / 2"
    by (simp add: algebra_simps; algebra)
  finally show ?thesis .
qed

lemma deltoid_point_minus_foot:
  fixes a b c m :: complex
  assumes ha: "oncircle 0 1 a" and hb: "oncircle 0 1 b"
    and hc: "oncircle 0 1 c" and hm: "oncircle 0 1 m"
    and ab: "a \<noteq> b"
  shows "steiner_deltoid_point a b c m - foot a b m =
      (c + m + a * b * cnj m + a * b * c * (cnj m)\<^sup>2) / 2"
  using foot_unit[OF ha hb ab]
  by (simp add: steiner_deltoid_point_def algebra_simps)

lemma feet_difference_unit:
  fixes a b c m :: complex
  assumes ha: "oncircle 0 1 a" and hb: "oncircle 0 1 b"
    and hc: "oncircle 0 1 c" and hm: "oncircle 0 1 m"
    and ab: "a \<noteq> b" and bc: "b \<noteq> c"
  shows "foot b c m - foot a b m =
      (c - a) * (1 - b * cnj m) / 2"
proof -
  have hd:
      "foot b c m - foot a b m =
        (c - a) * (m - b) / (2 * (m - 0))"
    by (rule foot_diff_PR_circ[OF ha hb hc hm zero_less_one ab bc])
  have hp:
      "foot b c m = (b + c + m - b * c * cnj m) / 2"
    by (rule foot_unit[OF hb hc bc])
  have hq:
      "foot a b m = (a + b + m - a * b * cnj m) / 2"
    by (rule foot_unit[OF ha hb ab])
  show ?thesis using hd hp hq by (simp add: algebra_simps)
qed

lemma cusp_feet_difference_ratio_real:
  fixes a b c m :: complex
  assumes ha: "oncircle 0 1 a" and hb: "oncircle 0 1 b"
    and hc: "oncircle 0 1 c" and hm: "oncircle 0 1 m"
    and ab: "a \<noteq> b" and bc: "b \<noteq> c"
    and hcube: "m ^ 3 = a * b * c"
  shows "(foot b c m - foot a b m) / m \<in> \<real>"
proof -
  have hca: "cnj a = 1 / a" using unit_cnj[OF ha] .
  have hcb: "cnj b = 1 / b" using unit_cnj[OF hb] .
  have hcc: "cnj c = 1 / c" using unit_cnj[OF hc] .
  have hcm: "cnj m = 1 / m" using unit_cnj[OF hm] .
  have ha0: "a \<noteq> 0" using unit_nonzero[OF ha] .
  have hb0: "b \<noteq> 0" using unit_nonzero[OF hb] .
  have hc0: "c \<noteq> 0" using unit_nonzero[OF hc] .
  have hm0: "m \<noteq> 0" using unit_nonzero[OF hm] .
  have hfeet:
      "foot b c m - foot a b m =
        (c - a) * (m - b) / (2 * (m - 0))"
    by (rule foot_diff_PR_circ[OF ha hb hc hm zero_less_one ab bc])
  have hratio:
      "(foot b c m - foot a b m) / m =
        (c - a) * (m - b) / (2 * (m * m))"
    using hfeet hm0
    by (simp add: power2_eq_square field_simps; algebra)
  have hconj_num:
      "cnj ((c - a) * (m - b)) =
        (c - a) * (m - b) / (a * b * c * m)"
    using hca hcb hcc hcm ha0 hb0 hc0 hm0
    by (simp add: complex_cnj_mult field_simps; algebra)
  have hconj_ratio:
      "cnj ((c - a) * (m - b) / (2 * (m * m))) =
        (c - a) * (m - b) / (2 * (m * m))"
    using hconj_num hcm ha0 hb0 hc0 hm0 hcube
    by (simp add: complex_cnj_divide complex_cnj_mult field_simps; algebra)
  have hreal:
      "cnj ((foot b c m - foot a b m) / m) =
        (foot b c m - foot a b m) / m"
    using hratio hconj_ratio by simp
  show ?thesis using hreal by (simp add: Reals_cnj_iff)
qed

lemma deltoid_cross_identity:
  fixes a b c m :: complex
  assumes ha: "oncircle 0 1 a" and hb: "oncircle 0 1 b"
    and hc: "oncircle 0 1 c" and hm: "oncircle 0 1 m"
  shows
    "cnj ((c + m + a * b * cnj m +
          a * b * c * (cnj m)\<^sup>2) / 2) *
        ((c - a) * (1 - b * cnj m) / 2) =
      ((c + m + a * b * cnj m +
          a * b * c * (cnj m)\<^sup>2) / 2) *
        cnj ((c - a) * (1 - b * cnj m) / 2)"
proof -
  have hca: "cnj a = 1 / a" using unit_cnj[OF ha] .
  have hcb: "cnj b = 1 / b" using unit_cnj[OF hb] .
  have hcc: "cnj c = 1 / c" using unit_cnj[OF hc] .
  have hcm: "cnj m = 1 / m" using unit_cnj[OF hm] .
  have ha0: "a \<noteq> 0" using unit_nonzero[OF ha] .
  have hb0: "b \<noteq> 0" using unit_nonzero[OF hb] .
  have hc0: "c \<noteq> 0" using unit_nonzero[OF hc] .
  have hm0: "m \<noteq> 0" using unit_nonzero[OF hm] .
  show ?thesis
    by (simp add: hca hcb hcc hcm ha0 hb0 hc0 hm0 field_simps; algebra)
qed

lemma deltoid_point_collinear:
  fixes a b c m :: complex
  assumes hncol: "\<not> collinear a b c"
    and ha: "oncircle 0 1 a" and hb: "oncircle 0 1 b"
    and hc: "oncircle 0 1 c" and hm: "oncircle 0 1 m"
  shows "collinear (foot a b m)
      (steiner_deltoid_point a b c m) (foot b c m)"
proof -
  obtain ab: "a \<noteq> b" and ac: "a \<noteq> c" and bc: "b \<noteq> c"
    using ncol_distinct[OF hncol] by blast
  have hX:
      "steiner_deltoid_point a b c m - foot a b m =
        (c + m + a * b * cnj m +
          a * b * c * (cnj m)\<^sup>2) / 2"
    by (rule deltoid_point_minus_foot[OF ha hb hc hm ab])
  have hY:
      "foot b c m - foot a b m =
        (c - a) * (1 - b * cnj m) / 2"
    by (rule feet_difference_unit[OF ha hb hc hm ab bc])
  have hlineeq:
      "cnj (steiner_deltoid_point a b c m - foot a b m) *
          (foot b c m - foot a b m) =
        (steiner_deltoid_point a b c m - foot a b m) *
          cnj (foot b c m - foot a b m)"
  proof -
    show ?thesis
      using deltoid_cross_identity[OF ha hb hc hm] by (simp add: hX hY)
  qed
  have hself:
      "cnj (cnj (steiner_deltoid_point a b c m - foot a b m) *
          (foot b c m - foot a b m)) =
        cnj (steiner_deltoid_point a b c m - foot a b m) *
          (foot b c m - foot a b m)"
    using hlineeq by (simp add: complex_cnj_mult)
  have him:
      "Im (cnj (steiner_deltoid_point a b c m - foot a b m) *
          (foot b c m - foot a b m)) = 0"
    using hself by (metis Reals_cnj_iff complex_is_Real_iff)
  have hiff:
      "collinear (foot a b m)
          (steiner_deltoid_point a b c m) (foot b c m) \<longleftrightarrow>
        Im (cnj (steiner_deltoid_point a b c m - foot a b m) *
          (foot b c m - foot a b m)) = 0"
    by (rule collinear_iff_cross)
  show ?thesis using hiff him by simp
qed

theorem simson_line_contains_steiner_deltoid_point_pair:
  fixes a b c m :: complex
  assumes hncol: "\<not> collinear a b c"
    and ha: "oncircle 0 1 a" and hb: "oncircle 0 1 b"
    and hc: "oncircle 0 1 c" and hm: "oncircle 0 1 m"
    and mb: "m \<noteq> b"
  shows "on_line (foot a b m) (foot b c m)
      (steiner_deltoid_point a b c m)"
proof -
  obtain ab: "a \<noteq> b" and ac: "a \<noteq> c" and bc: "b \<noteq> c"
    using ncol_distinct[OF hncol] by blast
  have hm0: "m \<noteq> 0" using unit_nonzero[OF hm] .
  have hfeet:
      "foot b c m - foot a b m =
        (c - a) * (m - b) / (2 * (m - 0))"
    by (rule foot_diff_PR_circ[OF ha hb hc hm zero_less_one ab bc])
  have hne: "foot b c m \<noteq> foot a b m"
  proof
    assume "foot b c m = foot a b m"
    then have "foot b c m - foot a b m = 0" by simp
    with hfeet have "(c - a) * (m - b) / (2 * (m - 0)) = 0"
      by simp
    then show False using ac mb hm0 by simp
  qed
  have hne': "foot a b m \<noteq> foot b c m" using hne by auto
  have hcol:
      "collinear (foot a b m)
        (steiner_deltoid_point a b c m) (foot b c m)"
    by (rule deltoid_point_collinear[OF hncol ha hb hc hm])
  have hratio_eq:
      "collinear (foot a b m)
        (steiner_deltoid_point a b c m) (foot b c m) =
      ((steiner_deltoid_point a b c m - foot a b m) /
        (foot b c m - foot a b m) \<in> \<real>)"
    by (rule collinear_iff_real_ratio[OF hne'])
  have hratio:
      "((steiner_deltoid_point a b c m - foot a b m) /
        (foot b c m - foot a b m) \<in> \<real>)"
    using hratio_eq hcol by simp
  have hlineiff:
      "on_line (foot a b m) (foot b c m)
        (steiner_deltoid_point a b c m) =
      ((steiner_deltoid_point a b c m - foot a b m) /
        (foot b c m - foot a b m) \<in> \<real>)"
    by (rule on_line_iff[OF hne'])
  show ?thesis using hlineiff hratio by simp
qed

theorem simson_line_contains_steiner_deltoid_point:
  fixes a b c m :: complex
  assumes hncol: "\<not> collinear a b c"
    and ha: "oncircle 0 1 a" and hb: "oncircle 0 1 b"
    and hc: "oncircle 0 1 c" and hm: "oncircle 0 1 m"
  shows "(m \<noteq> b \<longrightarrow>
      on_line (foot a b m) (foot b c m)
        (steiner_deltoid_point a b c m)) \<and>
    (m \<noteq> c \<longrightarrow>
      on_line (foot b c m) (foot c a m)
        (steiner_deltoid_point a b c m)) \<and>
    (m \<noteq> a \<longrightarrow>
      on_line (foot c a m) (foot a b m)
        (steiner_deltoid_point a b c m))"
proof -
  have hfirst:
      "m \<noteq> b \<longrightarrow>
        on_line (foot a b m) (foot b c m)
          (steiner_deltoid_point a b c m)"
  proof (rule impI)
    assume mb: "m \<noteq> b"
    show "on_line (foot a b m) (foot b c m)
        (steiner_deltoid_point a b c m)"
      by (rule simson_line_contains_steiner_deltoid_point_pair
          [OF hncol ha hb hc hm mb])
  qed
  have hncol_bca: "\<not> collinear b c a"
    using hncol by (metis collinear_cycle)
  have hsecond:
      "m \<noteq> c \<longrightarrow>
        on_line (foot b c m) (foot c a m)
          (steiner_deltoid_point a b c m)"
  proof (rule impI)
    assume mc: "m \<noteq> c"
    have hrot:
        "on_line (foot b c m) (foot c a m)
          (steiner_deltoid_point b c a m)"
      by (rule simson_line_contains_steiner_deltoid_point_pair
          [OF hncol_bca hb hc ha hm mc])
    show "on_line (foot b c m) (foot c a m)
        (steiner_deltoid_point a b c m)"
      using hrot
      by (simp add: steiner_deltoid_point_def ac_simps)
  qed
  have hncol_cab: "\<not> collinear c a b"
    using hncol by (metis collinear_cycle)
  have hthird:
      "m \<noteq> a \<longrightarrow>
        on_line (foot c a m) (foot a b m)
          (steiner_deltoid_point a b c m)"
  proof (rule impI)
    assume ma: "m \<noteq> a"
    have hrot:
        "on_line (foot c a m) (foot a b m)
          (steiner_deltoid_point c a b m)"
      by (rule simson_line_contains_steiner_deltoid_point_pair
          [OF hncol_cab hc ha hb hm ma])
    show "on_line (foot c a m) (foot a b m)
        (steiner_deltoid_point a b c m)"
      using hrot
      by (simp add: steiner_deltoid_point_def ac_simps)
  qed
  show ?thesis using hfirst hsecond hthird by blast
qed

lemma deltoid_normal_cross_identity:
  fixes a b c m :: complex
  assumes ha: "oncircle 0 1 a" and hb: "oncircle 0 1 b"
    and hc: "oncircle 0 1 c" and hm: "oncircle 0 1 m"
  shows
    "cnj (cnj ((c - a) * (1 - b * cnj m) / 2) *
        (m - a * b * c * (cnj m)\<^sup>2)) =
      -(cnj ((c - a) * (1 - b * cnj m) / 2) *
        (m - a * b * c * (cnj m)\<^sup>2))"
proof -
  have hca: "cnj a = 1 / a" using unit_cnj[OF ha] .
  have hcb: "cnj b = 1 / b" using unit_cnj[OF hb] .
  have hcc: "cnj c = 1 / c" using unit_cnj[OF hc] .
  have hcm: "cnj m = 1 / m" using unit_cnj[OF hm] .
  have ha0: "a \<noteq> 0" using unit_nonzero[OF ha] .
  have hb0: "b \<noteq> 0" using unit_nonzero[OF hb] .
  have hc0: "c \<noteq> 0" using unit_nonzero[OF hc] .
  have hm0: "m \<noteq> 0" using unit_nonzero[OF hm] .
  show ?thesis
    by (simp add: hca hcb hcc hcm ha0 hb0 hc0 hm0 field_simps; algebra)
qed

lemma real_complex_mult:
  fixes p q :: complex
  assumes "p \<in> \<real>" and "q \<in> \<real>"
  shows "p * q \<in> \<real>"
proof -
  have hp: "cnj p = p" by (metis Reals_cnj_iff assms(1))
  have hq: "cnj q = q" by (metis Reals_cnj_iff assms(2))
  show ?thesis
    using hp hq by (simp add: Reals_cnj_iff)
qed

lemma real_ratio_of_perpendicular:
  fixes u n :: complex
  assumes hperp: "complex_perpendicular u n" and hn: "n \<noteq> 0"
  shows "u / (\<i> * n) \<in> \<real>"
proof -
  have hRe: "Re (cnj u * n) = 0"
    using hperp unfolding complex_perpendicular_def .
  have hsum:
      "cnj u * n + u * cnj n = 0"
  proof -
    have h:
        "cnj u * n + u * cnj n = 2 * Re (cnj u * n)"
      using cnj_add_mult_eq_Re[of "cnj u" "cnj n"]
      by (simp only: complex_cnj_cnj)
    have hzero: "complex_of_real (2 * Re (cnj u * n)) = 0"
      using hRe by simp
    show ?thesis
      by (rule trans[OF h hzero])
  qed
  have hrat:
      "cnj (u / (\<i> * n)) = u / (\<i> * n)"
    using hsum hn
    by (simp add: complex_cnj_divide field_simps; algebra)
  show ?thesis using hrat by (simp add: Reals_cnj_iff)
qed

lemma on_line_of_collinear_perpendicular:
  fixes x y z n :: complex
  assumes hcol: "collinear x z y"
    and hxy: "x \<noteq> y"
    and hperp: "complex_perpendicular (y - x) n"
    and hn: "n \<noteq> 0"
  shows "on_line x (x + \<i> * n) z"
proof -
  have hyx: "y - x \<noteq> 0" using hxy by simp
  have hratio1:
      "(z - x) / (y - x) \<in> \<real>"
    using collinear_iff_real_ratio[OF hxy] hcol by simp
  have hratio2:
      "(y - x) / (\<i> * n) \<in> \<real>"
    by (rule real_ratio_of_perpendicular[OF hperp hn])
  have hprod:
      "((z - x) / (y - x)) * ((y - x) / (\<i> * n)) \<in> \<real>"
    by (rule real_complex_mult[OF hratio1 hratio2])
  have hratio:
      "(z - x) / (\<i> * n) =
        ((z - x) / (y - x)) * ((y - x) / (\<i> * n))"
    using hyx hn by (simp add: field_simps hyx hn; algebra)
  have hreal: "(z - x) / (\<i> * n) \<in> \<real>"
    by (metis hratio hprod)
  have hbase: "x \<noteq> x + \<i> * n" using hn by simp
  show ?thesis
    using on_line_iff[OF hbase] hreal by simp
qed

lemma on_line_of_collinear_real_direction:
  fixes x y z d :: complex
  assumes hcol: "collinear x z y"
    and hxy: "x \<noteq> y"
    and hratio2: "(y - x) / d \<in> \<real>"
    and hd: "d \<noteq> 0"
  shows "on_line x (x + d) z"
proof -
  have hyx: "y - x \<noteq> 0" using hxy by simp
  have hratio1:
      "(z - x) / (y - x) \<in> \<real>"
    using collinear_iff_real_ratio[OF hxy] hcol by simp
  have hprod:
      "((z - x) / (y - x)) * ((y - x) / d) \<in> \<real>"
    by (rule real_complex_mult[OF hratio1 hratio2])
  have hratio:
      "(z - x) / d =
        ((z - x) / (y - x)) * ((y - x) / d)"
    using hyx hd by (simp add: field_simps hyx hd; algebra)
  have hreal: "(z - x) / d \<in> \<real>"
    by (metis hratio hprod)
  have hbase: "x \<noteq> x + d" using hd by simp
  show ?thesis
    using on_line_iff[OF hbase] hreal by simp
qed

lemma on_line_change_base:
  fixes x y z d :: complex
  assumes hy: "on_line x (x + d) y"
    and hz: "on_line x (x + d) z"
  shows "on_line z (z + d) y"
proof -
  obtain r :: real where
      yr: "y = x + complex_of_real r * d"
    using hy unfolding on_line_def by (auto simp add: algebra_simps)
  obtain s :: real where
      zs: "z = x + complex_of_real s * d"
    using hz unfolding on_line_def by (auto simp add: algebra_simps)
  have hyz: "y = z + complex_of_real (r - s) * d"
    using yr zs by (simp add: algebra_simps)
  show ?thesis
    unfolding on_line_def
    apply (rule exI[of _ "r - s"])
    using hyz by (simp add: algebra_simps)
qed

lemma on_line_set_eq_of_distinct:
  fixes a b c d :: complex
  assumes hab: "a \<noteq> b" and hcd: "c \<noteq> d"
    and hc: "on_line a b c" and hd: "on_line a b d"
  shows "{z. on_line a b z} = {z. on_line c d z}"
proof -
  obtain r s :: real where
      hcr: "c = a + complex_of_real r * (b - a)"
    and hds: "d = a + complex_of_real s * (b - a)"
    using hc hd unfolding on_line_def by blast
  have hrs: "r \<noteq> s"
  proof
    assume "r = s"
    with hcr hds have "c = d" by simp
    with hcd show False by simp
  qed
  have hsr: "s - r \<noteq> 0" using hrs by simp
  have hdc: "d - c = complex_of_real (s - r) * (b - a)"
    using hcr hds by (simp add: algebra_simps; algebra)
  show "{z. on_line a b z} = {z. on_line c d z}"
  proof (rule set_eqI)
    fix z
    show "z \<in> {z. on_line a b z} \<longleftrightarrow>
        z \<in> {z. on_line c d z}"
  proof
    assume hz: "z \<in> {z. on_line a b z}"
    then obtain t :: real where
        hzt: "z = a + complex_of_real t * (b - a)"
      unfolding on_line_def by blast
    have hztc: "z - c = complex_of_real (t - r) * (b - a)"
      using hzt hcr by (simp add: algebra_simps; algebra)
    have hscale:
        "complex_of_real ((t - r) / (s - r)) * (d - c) =
          complex_of_real (t - r) * (b - a)"
    proof -
      have hsr0: "complex_of_real (s - r) \<noteq> 0" using hsr by simp
      have hrewrite:
          "complex_of_real ((t - r) / (s - r)) * (d - c) =
            (complex_of_real (t - r) / complex_of_real (s - r)) *
              (complex_of_real (s - r) * (b - a))"
        using hdc by (simp add: of_real_divide)
      show ?thesis using hrewrite hsr0
        by (simp add: field_simps; algebra)
    qed
    have hzd:
        "z = c + complex_of_real ((t - r) / (s - r)) * (d - c)"
      using hztc hscale by (simp add: algebra_simps; algebra)
    show "z \<in> {z. on_line c d z}"
      unfolding on_line_def using hzd by blast
  next
    assume hz: "z \<in> {z. on_line c d z}"
    then obtain t :: real where
        hzt: "z = c + complex_of_real t * (d - c)"
      unfolding on_line_def by blast
    have hzb:
      "z = a + complex_of_real (r + t * (s - r)) * (b - a)"
      using hzt hcr hdc
      by (simp add: algebra_simps of_real_mult; algebra)
    show "z \<in> {z. on_line a b z}"
      unfolding on_line_def using hzb by blast
  qed
qed
qed

lemma on_line_eq_of_real_scaled_direction:
  fixes x d :: complex and r :: real
  assumes hd: "d \<noteq> 0" and hr: "r \<noteq> 0"
  shows "{z. on_line x (x + d) z} =
      {z. on_line x (x + complex_of_real r * d) z}"
proof -
  have hbase: "x \<noteq> x + d" using hd by simp
  have hscaled: "x \<noteq> x + complex_of_real r * d"
    using hd hr by simp
  have hx: "on_line x (x + d) x"
    unfolding on_line_def
    by (rule exI[of _ 0]) simp
  have hxr: "on_line x (x + d) (x + complex_of_real r * d)"
    unfolding on_line_def
    by (rule exI[of _ r]) simp
  show ?thesis
    by (rule on_line_set_eq_of_distinct[OF hbase hscaled hx hxr])
qed

theorem steiner_deltoid_cusp_tangent_is_second_derivative:
  fixes a b c :: complex and t :: real
  assumes hcube: "(unit_circle_param t) ^ 3 = a * b * c"
  shows "steiner_deltoid_tangent_at a b c (unit_circle_param t) =
      {z. on_line (steiner_deltoid_point a b c (unit_circle_param t))
        (steiner_deltoid_point a b c (unit_circle_param t) +
          steiner_deltoid_curve_second_derivative a b c t) z}"
proof -
  have hm: "oncircle 0 1 (unit_circle_param t)"
    by (rule unit_circle_param_oncircle)
  have hm0: "unit_circle_param t \<noteq> 0"
    using unit_nonzero[OF hm] .
  have hminus: "(-3::real) \<noteq> 0" by simp
  have hnormal0:
      "steiner_deltoid_normal a b c (unit_circle_param t) = 0"
    using steiner_deltoid_normal_eq_zero_iff_cube[OF hm] hcube by blast
  have hdirection:
      "{z. on_line (steiner_deltoid_point a b c (unit_circle_param t))
          (steiner_deltoid_point a b c (unit_circle_param t) +
            unit_circle_param t) z} =
        {z. on_line (steiner_deltoid_point a b c (unit_circle_param t))
          (steiner_deltoid_point a b c (unit_circle_param t) +
            complex_of_real (-3) * unit_circle_param t) z}"
    by (rule on_line_eq_of_real_scaled_direction[OF hm0 hminus])
  have htangent:
      "steiner_deltoid_tangent_at a b c (unit_circle_param t) =
        {z. on_line (steiner_deltoid_point a b c (unit_circle_param t))
          (steiner_deltoid_point a b c (unit_circle_param t) +
            unit_circle_param t) z}"
    unfolding steiner_deltoid_tangent_at_def
      steiner_deltoid_tangent_direction_at_def
    using hnormal0 by simp
  show ?thesis
    using htangent hdirection
      steiner_deltoid_curve_second_derivative_stationary[OF hcube]
    by (simp add: algebra_simps)
qed

theorem simson_line_perpendicular_to_steiner_deltoid_normal:
  fixes a b c m :: complex
  assumes hncol: "\<not> collinear a b c"
    and ha: "oncircle 0 1 a" and hb: "oncircle 0 1 b"
    and hc: "oncircle 0 1 c" and hm: "oncircle 0 1 m"
  shows "complex_perpendicular
      (foot b c m - foot a b m)
      (steiner_deltoid_normal a b c m)"
proof -
  obtain ab: "a \<noteq> b" and bc: "b \<noteq> c"
    using ncol_distinct[OF hncol] by blast
  have hfeet:
      "foot b c m - foot a b m =
        (c - a) * (1 - b * cnj m) / 2"
    by (rule feet_difference_unit[OF ha hb hc hm ab bc])
  have hnormal:
      "steiner_deltoid_normal a b c m =
        m - a * b * c * (cnj m)\<^sup>2"
    by (simp add: steiner_deltoid_normal_def)
  have hcnj:
      "cnj (cnj (foot b c m - foot a b m) *
          steiner_deltoid_normal a b c m) =
        -(cnj (foot b c m - foot a b m) *
          steiner_deltoid_normal a b c m)"
  proof -
    show ?thesis
      using deltoid_normal_cross_identity[OF ha hb hc hm]
      by (simp add: hfeet hnormal)
  qed
  show ?thesis
    unfolding complex_perpendicular_def
    using hcnj by (metis eq_minus_cnj_iff_imag)
qed

theorem simson_line_is_tangent_to_steiner_deltoid_at_regular:
  fixes a b c m :: complex
  assumes hncol: "\<not> collinear a b c"
    and ha: "oncircle 0 1 a" and hb: "oncircle 0 1 b"
    and hc: "oncircle 0 1 c" and hm: "oncircle 0 1 m"
    and hnormal: "steiner_deltoid_normal a b c m \<noteq> 0"
  shows "(m \<noteq> b \<longrightarrow>
      foot a b m \<in> steiner_deltoid_tangent_at a b c m \<and>
      foot b c m \<in> steiner_deltoid_tangent_at a b c m \<and>
      foot a b m \<noteq> foot b c m) \<and>
    (m = b \<longrightarrow>
      foot b c m \<in> steiner_deltoid_tangent_at a b c m \<and>
      foot c a m \<in> steiner_deltoid_tangent_at a b c m \<and>
      foot b c m \<noteq> foot c a m)"
proof -
  obtain ab: "a \<noteq> b" and ac: "a \<noteq> c" and bc: "b \<noteq> c"
    using ncol_distinct[OF hncol] by blast
  have ca: "c \<noteq> a" using ac by simp
  have hm0: "m \<noteq> 0" using unit_nonzero[OF hm] .
  have hcol:
      "collinear (foot a b m)
        (steiner_deltoid_point a b c m) (foot b c m)"
    by (rule deltoid_point_collinear[OF hncol ha hb hc hm])
  have hperp:
      "complex_perpendicular
        (foot b c m - foot a b m)
        (steiner_deltoid_normal a b c m)"
    by (rule simson_line_perpendicular_to_steiner_deltoid_normal
      [OF hncol ha hb hc hm])
  have hfirst:
      "m \<noteq> b \<longrightarrow>
        foot a b m \<in> steiner_deltoid_tangent_at a b c m \<and>
        foot b c m \<in> steiner_deltoid_tangent_at a b c m \<and>
        foot a b m \<noteq> foot b c m"
  proof (rule impI)
    assume mb: "m \<noteq> b"
    have hne_rev: "foot b c m \<noteq> foot a b m"
    proof
      assume "foot b c m = foot a b m"
      then have hdiff: "foot b c m - foot a b m = 0" by simp
      have hfeet:
          "foot b c m - foot a b m =
            (c - a) * (m - b) / (2 * (m - 0))"
        by (rule foot_diff_PR_circ[OF ha hb hc hm zero_less_one ab bc])
      have hz: "(c - a) * (m - b) / (2 * (m - 0)) = 0"
        using hdiff hfeet by (metis)
      then show False using ac mb hm0 by (simp add: ac mb hm0)
    qed
    have hne: "foot a b m \<noteq> foot b c m" using hne_rev by auto
    have hline_d:
        "on_line (foot a b m)
          (foot a b m + \<i> * steiner_deltoid_normal a b c m)
          (steiner_deltoid_point a b c m)"
      by (rule on_line_of_collinear_perpendicular
        [OF hcol hne hperp hnormal])
    have hline_ab:
        "on_line (foot a b m)
          (foot a b m + \<i> * steiner_deltoid_normal a b c m)
          (foot a b m)"
      by (rule on_line_of_collinear_perpendicular
        [OF collinear_aac hne hperp hnormal])
    have hline_bc:
        "on_line (foot a b m)
          (foot a b m + \<i> * steiner_deltoid_normal a b c m)
          (foot b c m)"
      by (rule on_line_of_collinear_perpendicular
        [OF collinear_refl hne hperp hnormal])
    have htan_ab:
        "on_line (steiner_deltoid_point a b c m)
          (steiner_deltoid_point a b c m +
            \<i> * steiner_deltoid_normal a b c m)
          (foot a b m)"
      by (rule on_line_change_base[OF hline_ab hline_d])
    have htan_bc:
        "on_line (steiner_deltoid_point a b c m)
          (steiner_deltoid_point a b c m +
            \<i> * steiner_deltoid_normal a b c m)
          (foot b c m)"
      by (rule on_line_change_base[OF hline_bc hline_d])
    have hab_mem:
        "foot a b m \<in> steiner_deltoid_tangent_at a b c m"
      using htan_ab
      by (simp add: steiner_deltoid_tangent_at_def
          steiner_deltoid_tangent_direction_at_def hnormal)
    have hbc_mem:
        "foot b c m \<in> steiner_deltoid_tangent_at a b c m"
      using htan_bc
      by (simp add: steiner_deltoid_tangent_at_def
          steiner_deltoid_tangent_direction_at_def hnormal)
    show "foot a b m \<in> steiner_deltoid_tangent_at a b c m \<and>
        foot b c m \<in> steiner_deltoid_tangent_at a b c m \<and>
        foot a b m \<noteq> foot b c m"
      using hab_mem hbc_mem hne by blast
  qed
  have hncol_bca: "\<not> collinear b c a"
    using hncol by (metis collinear_cycle)
  have hsecond:
      "m = b \<longrightarrow>
        foot b c m \<in> steiner_deltoid_tangent_at a b c m \<and>
        foot c a m \<in> steiner_deltoid_tangent_at a b c m \<and>
        foot b c m \<noteq> foot c a m"
  proof (rule impI)
    assume mb: "m = b"
    have hcol_rot:
        "collinear (foot b c m)
          (steiner_deltoid_point a b c m) (foot c a m)"
    proof -
      have hrot:
          "collinear (foot b c m)
            (steiner_deltoid_point b c a m) (foot c a m)"
        by (rule deltoid_point_collinear[OF hncol_bca hb hc ha hm])
      show ?thesis using hrot
        by (simp add: steiner_deltoid_point_def ac_simps)
    qed
    have hnormal_rot:
        "steiner_deltoid_normal b c a m =
          steiner_deltoid_normal a b c m"
      by (simp add: steiner_deltoid_normal_def ac_simps)
    have hperp_rot:
        "complex_perpendicular
          (foot c a m - foot b c m)
          (steiner_deltoid_normal b c a m)"
      by (rule simson_line_perpendicular_to_steiner_deltoid_normal
        [OF hncol_bca hb hc ha hm])
    have hperp2:
        "complex_perpendicular
          (foot c a m - foot b c m)
          (steiner_deltoid_normal a b c m)"
      using hperp_rot hnormal_rot by simp
    have hfeet:
        "foot c a m - foot b c m =
          (a - b) * (m - c) / (2 * (m - 0))"
      by (rule foot_diff_PR_circ[OF hb hc ha hm zero_less_one bc ca])
    have hne_rev: "foot c a m \<noteq> foot b c m"
    proof
      assume "foot c a m = foot b c m"
      then have hdiff: "foot c a m - foot b c m = 0" by simp
      have hz: "(a - b) * (m - c) / (2 * (m - 0)) = 0"
        using hdiff hfeet by (metis)
      then show False using ab bc hm0 mb by (simp add: ab bc hm0 mb)
    qed
    have hne: "foot b c m \<noteq> foot c a m" using hne_rev by auto
    have hline_d:
        "on_line (foot b c m)
          (foot b c m + \<i> * steiner_deltoid_normal a b c m)
          (steiner_deltoid_point a b c m)"
      by (rule on_line_of_collinear_perpendicular
        [OF hcol_rot hne hperp2 hnormal])
    have hline_bc:
        "on_line (foot b c m)
          (foot b c m + \<i> * steiner_deltoid_normal a b c m)
          (foot b c m)"
      by (rule on_line_of_collinear_perpendicular
        [OF collinear_aac hne hperp2 hnormal])
    have hline_ca:
        "on_line (foot b c m)
          (foot b c m + \<i> * steiner_deltoid_normal a b c m)
          (foot c a m)"
      by (rule on_line_of_collinear_perpendicular
        [OF collinear_refl hne hperp2 hnormal])
    have htan_bc:
        "on_line (steiner_deltoid_point a b c m)
          (steiner_deltoid_point a b c m +
            \<i> * steiner_deltoid_normal a b c m)
          (foot b c m)"
      by (rule on_line_change_base[OF hline_bc hline_d])
    have htan_ca:
        "on_line (steiner_deltoid_point a b c m)
          (steiner_deltoid_point a b c m +
            \<i> * steiner_deltoid_normal a b c m)
          (foot c a m)"
      by (rule on_line_change_base[OF hline_ca hline_d])
    have hbc_mem:
        "foot b c m \<in> steiner_deltoid_tangent_at a b c m"
      using htan_bc
      by (simp add: steiner_deltoid_tangent_at_def
          steiner_deltoid_tangent_direction_at_def hnormal)
    have hca_mem:
        "foot c a m \<in> steiner_deltoid_tangent_at a b c m"
      using htan_ca
      by (simp add: steiner_deltoid_tangent_at_def
          steiner_deltoid_tangent_direction_at_def hnormal)
    show "foot b c m \<in> steiner_deltoid_tangent_at a b c m \<and>
        foot c a m \<in> steiner_deltoid_tangent_at a b c m \<and>
        foot b c m \<noteq> foot c a m"
      using hbc_mem hca_mem hne by blast
  qed
  show ?thesis using hfirst hsecond by blast
qed

theorem simson_line_eq_steiner_deltoid_tangent_at:
  fixes a b c m :: complex
  assumes hncol: "\<not> collinear a b c"
    and ha: "oncircle 0 1 a" and hb: "oncircle 0 1 b"
    and hc: "oncircle 0 1 c" and hm: "oncircle 0 1 m"
    and hnormal: "steiner_deltoid_normal a b c m \<noteq> 0"
  shows "(m \<noteq> b \<longrightarrow>
      {z. on_line (foot a b m) (foot b c m) z} =
        steiner_deltoid_tangent_at a b c m) \<and>
    (m = b \<longrightarrow>
      {z. on_line (foot b c m) (foot c a m) z} =
        steiner_deltoid_tangent_at a b c m)"
proof -
  have hAt:
      "(m \<noteq> b \<longrightarrow>
          foot a b m \<in> steiner_deltoid_tangent_at a b c m \<and>
          foot b c m \<in> steiner_deltoid_tangent_at a b c m \<and>
          foot a b m \<noteq> foot b c m) \<and>
        (m = b \<longrightarrow>
          foot b c m \<in> steiner_deltoid_tangent_at a b c m \<and>
          foot c a m \<in> steiner_deltoid_tangent_at a b c m \<and>
          foot b c m \<noteq> foot c a m)"
    by (rule simson_line_is_tangent_to_steiner_deltoid_at_regular
      [OF hncol ha hb hc hm hnormal])
  have hdir:
      "steiner_deltoid_point a b c m \<noteq>
        steiner_deltoid_point a b c m +
          steiner_deltoid_tangent_direction_at a b c m"
    using hnormal
    by (simp add: steiner_deltoid_tangent_direction_at_def hnormal)
  have hfirst:
      "m \<noteq> b \<longrightarrow>
        {z. on_line (foot a b m) (foot b c m) z} =
          steiner_deltoid_tangent_at a b c m"
  proof (rule impI)
    assume mb: "m \<noteq> b"
    have hne: "foot a b m \<noteq> foot b c m"
      using hAt mb by blast
    have hab_mem: "foot a b m \<in> steiner_deltoid_tangent_at a b c m"
      using hAt mb by blast
    have hbc_mem: "foot b c m \<in> steiner_deltoid_tangent_at a b c m"
      using hAt mb by blast
    have hset:
        "{z. on_line (steiner_deltoid_point a b c m)
            (steiner_deltoid_point a b c m +
              steiner_deltoid_tangent_direction_at a b c m) z} =
          {z. on_line (foot a b m) (foot b c m) z}"
    proof (rule on_line_set_eq_of_distinct[OF hdir hne])
      show "on_line (steiner_deltoid_point a b c m)
          (steiner_deltoid_point a b c m +
            steiner_deltoid_tangent_direction_at a b c m)
          (foot a b m)"
        using hab_mem by (simp add: steiner_deltoid_tangent_at_def)
      show "on_line (steiner_deltoid_point a b c m)
          (steiner_deltoid_point a b c m +
            steiner_deltoid_tangent_direction_at a b c m)
          (foot b c m)"
        using hbc_mem by (simp add: steiner_deltoid_tangent_at_def)
    qed
    have hset_rev:
        "{z. on_line (foot a b m) (foot b c m) z} =
          {z. on_line (steiner_deltoid_point a b c m)
            (steiner_deltoid_point a b c m +
              steiner_deltoid_tangent_direction_at a b c m) z}"
      using hset by (rule sym)
    show "{z. on_line (foot a b m) (foot b c m) z} =
        steiner_deltoid_tangent_at a b c m"
      using hset_rev
      by (simp add: steiner_deltoid_tangent_at_def)
  qed
  have hsecond:
      "m = b \<longrightarrow>
        {z. on_line (foot b c m) (foot c a m) z} =
          steiner_deltoid_tangent_at a b c m"
  proof (rule impI)
    assume mb: "m = b"
    have hne: "foot b c m \<noteq> foot c a m"
      using hAt mb by blast
    have hbc_mem: "foot b c m \<in> steiner_deltoid_tangent_at a b c m"
      using hAt mb by blast
    have hca_mem: "foot c a m \<in> steiner_deltoid_tangent_at a b c m"
      using hAt mb by blast
    have hset:
        "{z. on_line (steiner_deltoid_point a b c m)
            (steiner_deltoid_point a b c m +
              steiner_deltoid_tangent_direction_at a b c m) z} =
          {z. on_line (foot b c m) (foot c a m) z}"
    proof (rule on_line_set_eq_of_distinct[OF hdir hne])
      show "on_line (steiner_deltoid_point a b c m)
          (steiner_deltoid_point a b c m +
            steiner_deltoid_tangent_direction_at a b c m)
          (foot b c m)"
        using hbc_mem by (simp add: steiner_deltoid_tangent_at_def)
      show "on_line (steiner_deltoid_point a b c m)
          (steiner_deltoid_point a b c m +
            steiner_deltoid_tangent_direction_at a b c m)
          (foot c a m)"
        using hca_mem by (simp add: steiner_deltoid_tangent_at_def)
    qed
    have hset_rev:
        "{z. on_line (foot b c m) (foot c a m) z} =
          {z. on_line (steiner_deltoid_point a b c m)
            (steiner_deltoid_point a b c m +
              steiner_deltoid_tangent_direction_at a b c m) z}"
      using hset by (rule sym)
    show "{z. on_line (foot b c m) (foot c a m) z} =
        steiner_deltoid_tangent_at a b c m"
      using hset_rev
      by (simp add: steiner_deltoid_tangent_at_def)
  qed
  show ?thesis using hfirst hsecond by blast
qed

theorem simson_line_eq_steiner_deltoid_tangent_at_all:
  fixes a b c m :: complex
  assumes hncol: "\<not> collinear a b c"
    and ha: "oncircle 0 1 a" and hb: "oncircle 0 1 b"
    and hc: "oncircle 0 1 c" and hm: "oncircle 0 1 m"
  shows "(m \<noteq> b \<longrightarrow>
      {z. on_line (foot a b m) (foot b c m) z} =
        steiner_deltoid_tangent_at a b c m) \<and>
    (m = b \<longrightarrow>
      {z. on_line (foot b c m) (foot c a m) z} =
        steiner_deltoid_tangent_at a b c m)"
proof -
  obtain ab: "a \<noteq> b" and ac: "a \<noteq> c" and bc: "b \<noteq> c"
    using ncol_distinct[OF hncol] by blast
  have ca: "c \<noteq> a" using ac by simp
  have hm0: "m \<noteq> 0" using unit_nonzero[OF hm] .
  show ?thesis
  proof (cases "m ^ 3 = a * b * c")
    case True
    have hcube: "m ^ 3 = a * b * c" using True .
    have hnormal0:
        "steiner_deltoid_normal a b c m = 0"
      using steiner_deltoid_normal_eq_zero_iff_cube[OF hm] hcube by blast
    have hdir:
        "steiner_deltoid_point a b c m \<noteq>
          steiner_deltoid_point a b c m + m"
      using hm0 by simp
    have hfirst:
        "m \<noteq> b \<longrightarrow>
          {z. on_line (foot a b m) (foot b c m) z} =
            steiner_deltoid_tangent_at a b c m"
    proof (rule impI)
      assume mb: "m \<noteq> b"
      have hfeet:
          "foot b c m - foot a b m =
            (c - a) * (m - b) / (2 * (m - 0))"
        by (rule foot_diff_PR_circ[OF ha hb hc hm zero_less_one ab bc])
      have hne_rev: "foot b c m \<noteq> foot a b m"
      proof
        assume "foot b c m = foot a b m"
        then have hdiff: "foot b c m - foot a b m = 0" by simp
        have hz: "(c - a) * (m - b) / (2 * (m - 0)) = 0"
          using hdiff hfeet by (metis)
        then show False using ac mb hm0 by (simp add: ac mb hm0)
      qed
      have hne: "foot a b m \<noteq> foot b c m" using hne_rev by auto
      have hcol:
          "collinear (foot a b m)
            (steiner_deltoid_point a b c m) (foot b c m)"
        by (rule deltoid_point_collinear[OF hncol ha hb hc hm])
      have hratio:
          "(foot b c m - foot a b m) / m \<in> \<real>"
        by (rule cusp_feet_difference_ratio_real
          [OF ha hb hc hm ab bc hcube])
      have hline_d:
          "on_line (foot a b m) (foot a b m + m)
            (steiner_deltoid_point a b c m)"
        by (rule on_line_of_collinear_real_direction
          [OF hcol hne hratio hm0])
      have hline_ab:
          "on_line (foot a b m) (foot a b m + m) (foot a b m)"
        by (rule on_line_of_collinear_real_direction
          [OF collinear_aac hne hratio hm0])
      have hline_bc:
          "on_line (foot a b m) (foot a b m + m) (foot b c m)"
        by (rule on_line_of_collinear_real_direction
          [OF collinear_refl hne hratio hm0])
      have htan_ab:
          "on_line (steiner_deltoid_point a b c m)
            (steiner_deltoid_point a b c m + m) (foot a b m)"
        by (rule on_line_change_base[OF hline_ab hline_d])
      have htan_bc:
          "on_line (steiner_deltoid_point a b c m)
            (steiner_deltoid_point a b c m + m) (foot b c m)"
        by (rule on_line_change_base[OF hline_bc hline_d])
      have hset:
          "{z. on_line (steiner_deltoid_point a b c m)
              (steiner_deltoid_point a b c m + m) z} =
            {z. on_line (foot a b m) (foot b c m) z}"
      proof (rule on_line_set_eq_of_distinct[OF hdir hne])
        show "on_line (steiner_deltoid_point a b c m)
            (steiner_deltoid_point a b c m + m) (foot a b m)"
          using htan_ab .
        show "on_line (steiner_deltoid_point a b c m)
            (steiner_deltoid_point a b c m + m) (foot b c m)"
          using htan_bc .
      qed
      have hset_rev:
          "{z. on_line (foot a b m) (foot b c m) z} =
            {z. on_line (steiner_deltoid_point a b c m)
              (steiner_deltoid_point a b c m + m) z}"
        using hset by (rule sym)
      show "{z. on_line (foot a b m) (foot b c m) z} =
          steiner_deltoid_tangent_at a b c m"
        using hset_rev
        by (simp add: steiner_deltoid_tangent_at_def
            steiner_deltoid_tangent_direction_at_def hnormal0)
    qed
    have hncol_bca: "\<not> collinear b c a"
      using hncol by (metis collinear_cycle)
    have hsecond:
        "m = b \<longrightarrow>
          {z. on_line (foot b c m) (foot c a m) z} =
            steiner_deltoid_tangent_at a b c m"
    proof (rule impI)
      assume mb: "m = b"
      have hfeet:
          "foot c a m - foot b c m =
            (a - b) * (m - c) / (2 * (m - 0))"
        by (rule foot_diff_PR_circ[OF hb hc ha hm zero_less_one bc ca])
      have hne_rev: "foot c a m \<noteq> foot b c m"
      proof
        assume "foot c a m = foot b c m"
        then have hdiff: "foot c a m - foot b c m = 0" by simp
        have hz: "(a - b) * (m - c) / (2 * (m - 0)) = 0"
          using hdiff hfeet by (metis)
        then show False using ab bc hm0 mb by (simp add: ab bc hm0 mb)
      qed
      have hne: "foot b c m \<noteq> foot c a m" using hne_rev by auto
      have hcol:
          "collinear (foot b c m)
            (steiner_deltoid_point a b c m) (foot c a m)"
      proof -
        have hrot:
            "collinear (foot b c m)
              (steiner_deltoid_point b c a m) (foot c a m)"
          by (rule deltoid_point_collinear[OF hncol_bca hb hc ha hm])
        show ?thesis using hrot
          by (simp add: steiner_deltoid_point_def ac_simps)
      qed
      have hcube_rot: "m ^ 3 = b * c * a"
        using hcube by (simp add: ac_simps)
      have hratio:
          "(foot c a m - foot b c m) / m \<in> \<real>"
        by (rule cusp_feet_difference_ratio_real
          [OF hb hc ha hm bc ca hcube_rot])
      have hline_d:
          "on_line (foot b c m) (foot b c m + m)
            (steiner_deltoid_point a b c m)"
        by (rule on_line_of_collinear_real_direction
          [OF hcol hne hratio hm0])
      have hline_bc:
          "on_line (foot b c m) (foot b c m + m) (foot b c m)"
        by (rule on_line_of_collinear_real_direction
          [OF collinear_aac hne hratio hm0])
      have hline_ca:
          "on_line (foot b c m) (foot b c m + m) (foot c a m)"
        by (rule on_line_of_collinear_real_direction
          [OF collinear_refl hne hratio hm0])
      have htan_bc:
          "on_line (steiner_deltoid_point a b c m)
            (steiner_deltoid_point a b c m + m) (foot b c m)"
        by (rule on_line_change_base[OF hline_bc hline_d])
      have htan_ca:
          "on_line (steiner_deltoid_point a b c m)
            (steiner_deltoid_point a b c m + m) (foot c a m)"
        by (rule on_line_change_base[OF hline_ca hline_d])
      have hset:
          "{z. on_line (steiner_deltoid_point a b c m)
              (steiner_deltoid_point a b c m + m) z} =
            {z. on_line (foot b c m) (foot c a m) z}"
      proof (rule on_line_set_eq_of_distinct[OF hdir hne])
        show "on_line (steiner_deltoid_point a b c m)
            (steiner_deltoid_point a b c m + m) (foot b c m)"
          using htan_bc .
        show "on_line (steiner_deltoid_point a b c m)
            (steiner_deltoid_point a b c m + m) (foot c a m)"
          using htan_ca .
      qed
      have hset_rev:
          "{z. on_line (foot b c m) (foot c a m) z} =
            {z. on_line (steiner_deltoid_point a b c m)
              (steiner_deltoid_point a b c m + m) z}"
        using hset by (rule sym)
      show "{z. on_line (foot b c m) (foot c a m) z} =
          steiner_deltoid_tangent_at a b c m"
        using hset_rev
        by (simp add: steiner_deltoid_tangent_at_def
            steiner_deltoid_tangent_direction_at_def hnormal0)
    qed
    show ?thesis using hfirst hsecond by blast
  next
    case False
    have hnormal:
        "steiner_deltoid_normal a b c m \<noteq> 0"
      using steiner_deltoid_normal_nonzero_iff_cube_neq[OF hm]
        False by blast
    show ?thesis
      by (rule simson_line_eq_steiner_deltoid_tangent_at
        [OF hncol ha hb hc hm hnormal])
  qed
qed

theorem simson_line_eq_steiner_deltoid_tangent_all:
  fixes a b c :: complex and t :: real
  assumes hncol: "\<not> collinear a b c"
    and ha: "oncircle 0 1 a" and hb: "oncircle 0 1 b"
    and hc: "oncircle 0 1 c"
  shows "(unit_circle_param t \<noteq> b \<longrightarrow>
      {z. on_line (foot a b (unit_circle_param t))
        (foot b c (unit_circle_param t)) z} =
        steiner_deltoid_tangent a b c t) \<and>
    (unit_circle_param t = b \<longrightarrow>
      {z. on_line (foot b c (unit_circle_param t))
        (foot c a (unit_circle_param t)) z} =
        steiner_deltoid_tangent a b c t)"
proof -
  have hm: "oncircle 0 1 (unit_circle_param t)"
    by (rule unit_circle_param_oncircle)
  have hAt:
      "(unit_circle_param t \<noteq> b \<longrightarrow>
          {z. on_line (foot a b (unit_circle_param t))
            (foot b c (unit_circle_param t)) z} =
              steiner_deltoid_tangent_at a b c (unit_circle_param t)) \<and>
        (unit_circle_param t = b \<longrightarrow>
          {z. on_line (foot b c (unit_circle_param t))
            (foot c a (unit_circle_param t)) z} =
              steiner_deltoid_tangent_at a b c (unit_circle_param t))"
    by (rule simson_line_eq_steiner_deltoid_tangent_at_all
      [OF hncol ha hb hc hm])
  have heq:
      "steiner_deltoid_tangent a b c t =
        steiner_deltoid_tangent_at a b c (unit_circle_param t)"
    by (rule steiner_deltoid_tangent_eq_tangent_at)
  show ?thesis using hAt heq by blast
qed

theorem simson_line_is_tangent_to_steiner_deltoid_regular:
  fixes a b c :: complex and t :: real
  assumes hncol: "\<not> collinear a b c"
    and ha: "oncircle 0 1 a" and hb: "oncircle 0 1 b"
    and hc: "oncircle 0 1 c"
    and hregular: "(unit_circle_param t) ^ 3 \<noteq> a * b * c"
  shows "(unit_circle_param t \<noteq> b \<longrightarrow>
      foot a b (unit_circle_param t) \<in> steiner_deltoid_tangent a b c t \<and>
      foot b c (unit_circle_param t) \<in> steiner_deltoid_tangent a b c t \<and>
      foot a b (unit_circle_param t) \<noteq> foot b c (unit_circle_param t)) \<and>
    (unit_circle_param t = b \<longrightarrow>
      foot b c (unit_circle_param t) \<in> steiner_deltoid_tangent a b c t \<and>
      foot c a (unit_circle_param t) \<in> steiner_deltoid_tangent a b c t \<and>
      foot b c (unit_circle_param t) \<noteq> foot c a (unit_circle_param t))"
proof -
  have hm: "oncircle 0 1 (unit_circle_param t)"
    by (rule unit_circle_param_oncircle)
  have hnormal:
      "steiner_deltoid_normal a b c (unit_circle_param t) \<noteq> 0"
    using steiner_deltoid_normal_nonzero_iff_cube_neq[OF hm]
      hregular by blast
  have hAt:
      "(unit_circle_param t \<noteq> b \<longrightarrow>
          foot a b (unit_circle_param t) \<in>
            steiner_deltoid_tangent_at a b c (unit_circle_param t) \<and>
          foot b c (unit_circle_param t) \<in>
            steiner_deltoid_tangent_at a b c (unit_circle_param t) \<and>
          foot a b (unit_circle_param t) \<noteq>
            foot b c (unit_circle_param t)) \<and>
        (unit_circle_param t = b \<longrightarrow>
          foot b c (unit_circle_param t) \<in>
            steiner_deltoid_tangent_at a b c (unit_circle_param t) \<and>
          foot c a (unit_circle_param t) \<in>
            steiner_deltoid_tangent_at a b c (unit_circle_param t) \<and>
          foot b c (unit_circle_param t) \<noteq>
            foot c a (unit_circle_param t))"
    by (rule simson_line_is_tangent_to_steiner_deltoid_at_regular
      [OF hncol ha hb hc hm hnormal])
  have heq:
      "steiner_deltoid_tangent a b c t =
        steiner_deltoid_tangent_at a b c (unit_circle_param t)"
    by (rule steiner_deltoid_tangent_eq_tangent_at)
  show ?thesis using hAt heq by blast
qed

theorem simson_line_meets_steiner_deltoid:
  fixes a b c m :: complex
  assumes hncol: "\<not> collinear a b c"
    and ha: "oncircle 0 1 a" and hb: "oncircle 0 1 b"
    and hc: "oncircle 0 1 c" and hm: "oncircle 0 1 m"
  shows "steiner_deltoid_point a b c m \<in> steiner_deltoid a b c \<and>
    ((m \<noteq> b \<longrightarrow>
        on_line (foot a b m) (foot b c m)
          (steiner_deltoid_point a b c m)) \<and>
      (m \<noteq> c \<longrightarrow>
        on_line (foot b c m) (foot c a m)
          (steiner_deltoid_point a b c m)) \<and>
      (m \<noteq> a \<longrightarrow>
        on_line (foot c a m) (foot a b m)
          (steiner_deltoid_point a b c m)))"
  using steiner_deltoid_point_mem[OF hm]
    simson_line_contains_steiner_deltoid_point[OF hncol ha hb hc hm]
  by blast

end
