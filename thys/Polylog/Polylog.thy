(*
  File:     Polylog/Polylog.thy
  Authors:  Manuel Eberl (University of Innsbruck)
*)
section \<open>The Polylogarithm Function\<close>
theory Polylog
imports
  "HOL-Complex_Analysis.Complex_Analysis"
  "Linear_Recurrences.Eulerian_Polynomials"
  "HOL-Real_Asymp.Real_Asymp"
  Polylog_Library
begin

subsection \<open>Definition and basic properties\<close>

text \<open>
  The principal branch of the Polylogarithm function $\text{Li}_s(z)$ is defined as
    \[\text{Li}_s(z) = \sum_{k=1}^\infty \frac{z^k}{k^s}\]
  for $|z|<1$ and elsewhere by analytic continuation. For integer $s \leq 0$ it is holomorphic
  except for a pole at $z = 1$. For other values of $s$ it is holomorphic except for a branch
  cut along the line $[1, \infty)$.

  Special values include $\text{Li}_0(z) = \frac{z}{1-z}$ and $\text{Li}_1(z) = -\log (1-z)$.

  One could potentially generalise this to arbitrary \<open>s \<in> \<complex>\<close>, but this makes the analytic
  continuation somewhat more complicated, so we chosed not to do this at this point.

  In the following, we define the principal branch of $\text{Li}_s(z)$ for integer $s$.
\<close>

definition polylog :: "int \<Rightarrow> complex \<Rightarrow> complex" where
  "polylog k z =
     (if k \<le> 0 then z * poly (eulerian_poly (nat (-k))) z * (1 - z) powi (k - 1)
      else if z \<in> of_real ` {1..} then 0
           else (SOME f. f holomorphic_on -of_real`{1..} \<and>
                    (\<forall>z\<in>ball 0 1. f z = (\<Sum>n. of_nat (Suc n) powi (-k) * z ^ Suc n))) z)"

lemma conv_radius_polylog: "conv_radius (\<lambda>r. of_nat r powi k :: complex) = 1"
proof (rule conv_radius_ratio_limit_ereal_nonzero)
  have "(\<lambda>n. ereal (real n powi k / real (Suc n) powi k)) \<longlonglongrightarrow> ereal 1"
  proof (cases "k \<ge> 0")
    case True
    have "(\<lambda>n. ereal (real n ^ nat k / real (Suc n) ^ nat k)) \<longlonglongrightarrow> ereal 1"
      by (intro tendsto_ereal) real_asymp
    thus ?thesis
      using True by (simp add: power_int_def)
  next
    case False
    have "(\<lambda>n. ereal (inverse (real n) ^ nat (-k) / inverse (real (Suc n)) ^ nat (-k))) \<longlonglongrightarrow> ereal 1"
      by (intro tendsto_ereal) real_asymp
    thus ?thesis
      using False by (simp add: power_int_def)
  qed
  thus "(\<lambda>n. ereal (norm (of_nat n powi k :: complex) / norm (of_nat (Suc n) powi k :: complex))) \<longlonglongrightarrow> 1"
    unfolding one_ereal_def [symmetric] by (simp add: norm_power_int del: of_nat_Suc)
qed auto

lemma abs_summable_polylog:
  "norm z < 1 \<Longrightarrow> summable (\<lambda>r. norm (of_nat r powi k * z ^ r :: complex))"
  by (rule abs_summable_in_conv_radius) (use conv_radius_polylog[of k] in auto)

text \<open>
  Two very central results that characterise the polylogarithm:
  \[\text{Li}_s'(z) = \frac{1}{z}\text{Li}_{s-1}(z)\quad\quad\text{and}\quad\quad
    \text{Li}_s(z) = \sum_{n=1}^\infty \frac{z^n}{n^s}\quad\text{for}\ |z|<1\]
\<close>
theorem has_field_derivative_polylog [derivative_intros]:
        "\<And>z. z \<in> (if k \<le> 0 then -{1} else -(of_real ` {1..})) \<Longrightarrow>
               (polylog k has_field_derivative (if z = 0 then 1 else polylog (k - 1) z / z)) (at z within A)"
  and sums_polylog: "norm z < 1 \<Longrightarrow> (\<lambda>n. of_nat (Suc n) powi (-k) * z ^ Suc n) sums polylog k z"
proof -
  let ?S = "-(complex_of_real ` {1..})"
  have "open ?S"
    by (intro open_Compl closed_slot_right) 
  define S where "S = (\<lambda>k::int. if k \<le> 0 then -{1} else ?S)"
  have [simp]: "open (S k)" for k
    using \<open>open ?S\<close> by (auto simp: S_def)

  have *: "(\<forall>z\<in>S k. (polylog k has_field_derivative (if z = 0 then 1 else polylog (k - 1) z / z)) (at z)) \<and>
           (\<forall>z\<in>ball 0 1. (\<lambda>n. of_nat (Suc n) powi (-k) * z ^ Suc n) sums polylog k z)"
  proof (induction "nat k" arbitrary: k)
    case 0
    define k' where "k' = nat (-k)"
    have k_eq: "k = -int k'"
      using 0 by (simp add: k'_def)

    have "(polylog k has_field_derivative (if z = 0 then 1 else polylog (k - 1) z / z)) (at z)"
      if z: "z \<in> S k" for z
    proof -
      have [simp]: "z \<noteq> 1"
        using z 0 by (auto simp: S_def)
      write eulerian_poly ("E")
      have "polylog (k - 1) z = z * (poly (E (Suc k')) z * (1 - z) powi (k - 2))"
        using 0 by (simp add: polylog_def k_eq nat_add_distrib algebra_simps)
      also have "\<dots> = z * poly (E (Suc k')) z / (1 - z) ^ (k' + 2)"
        by (simp add: k_eq power_int_def nat_add_distrib field_simps)
      finally have eq1: "polylog (k - 1) z = \<dots>" .

      have "polylog k = (\<lambda>z. z * poly (E k') z * (1 - z) powi (k - 1))"
        using 0 by (simp add: polylog_def [abs_def] k_eq)
      also have "\<dots> = (\<lambda>z. z * poly (E k') z / (1 - z) ^ Suc k')"
        by (simp add: k_eq power_int_def field_simps nat_add_distrib)
      finally have eq2: "polylog k = (\<lambda>z. z * poly (E k') z / (1 - z) ^ Suc k')" .

      have "((\<lambda>z. z * poly (E k') z / (1 - z) ^ Suc k') has_field_derivative
                   (poly (E (Suc k')) z / (1 - z) ^ (k' + 2))) (at z)"
        apply (rule derivative_eq_intros refl poly_DERIV)+
         apply (simp)
        apply (simp add: eulerian_poly.simps(2) Let_def divide_simps)
        apply (simp add: algebra_simps)
        done
      also note eq2 [symmetric]
      also have "poly (E (Suc k')) z / (1 - z) ^ (k' + 2) =
                   (if z = 0 then 1 else polylog (k - 1) z / z)"
        by (subst eq1) (auto)
      finally show ?thesis .
    qed

    moreover have "(\<lambda>n. of_nat (Suc n) powi (-k) * z ^ Suc n) sums polylog k z"
      if z: "norm z < 1" for z
    proof (cases "k = 0")
      case True
      thus ?thesis using z geometric_sums[of z]
        by (auto simp: polylog_def divide_inverse intro!: sums_mult)
    next
      case False
      with 0 have k: "k < 0"
        by simp
      define F where "F = Abs_fps (\<lambda>n. of_nat n ^ nat (-k) :: complex)"
      have "fps_conv_radius (1 - fps_X :: complex fps) \<ge> \<infinity>"
        by (intro order.trans[OF _ fps_conv_radius_diff]) auto
      hence [simp]: "fps_conv_radius (1 - fps_X :: complex fps) = \<infinity>"
        by simp
      have *: "fps_conv_radius ((1 - fps_X) ^ (nat (-k) + 1) :: complex fps) \<ge> \<infinity>"
        by (intro order.trans[OF _ fps_conv_radius_power]) auto

      have "ereal (norm z) < 1"
        using that by simp
      also have "1 \<le> fps_conv_radius F"
        unfolding F_def fps_conv_radius_def using conv_radius_polylog[of "-k"] 0
        by (simp add: power_int_def)
      finally have "(\<lambda>n. fps_nth F n * z ^ n) sums eval_fps F z"
        by (rule sums_eval_fps)
      also have "(\<lambda>n. fps_nth F n * z ^ n) = (\<lambda>n. of_nat n powi (-k) * z ^ n)"
        using 0 by (simp add: F_def power_int_def)
      also have "eval_fps F z = poly (fps_monom_poly 1 (nat (- k))) z /
                                eval_fps ((1 - fps_X) ^ (nat (- k) + 1)) z"
        unfolding F_def fps_monom_aux
      proof (subst eval_fps_divide')
        show "fps_conv_radius (fps_of_poly (fps_monom_poly 1 (nat (- k)))) > 0"
          by simp
        show "fps_conv_radius ((1 - fps_X :: complex fps) ^ (nat (- k) + 1)) > 0"
          by (intro less_le_trans[OF _ fps_conv_radius_power]) auto
        show "1 > (0 :: ereal)"
          by simp
        show "eval_fps ((1 - fps_X) ^ (nat (-k) + 1)) z \<noteq> 0"
          if "z \<in> eball 0 1" for z :: complex
          using that by (subst eval_fps_power) (auto simp: eval_fps_diff)
        show "ereal (norm z) < Min {1, fps_conv_radius (fps_of_poly (fps_monom_poly 1 (nat (- k)))),
                fps_conv_radius ((1 - fps_X :: complex fps) ^ (nat (- k) + 1))}" using * z
          by auto
      qed auto
      also have "eval_fps ((1 - fps_X) ^ (nat (- k) + 1)) z = (1 - z) ^ (nat (-k) + 1)"
        by (subst eval_fps_power) (auto simp: eval_fps_diff)
      also have "\<dots> = (1 - z) powi int (nat (-k) + 1)"
        by (rule power_int_of_nat [symmetric])
      also have "int (nat (-k) + 1) = -(k-1)"
        using 0 by simp
      also have "(poly (fps_monom_poly 1 (nat (- k))) z / (1 - z) powi - (k - 1)) = polylog k z"
        using k
        by (auto simp add: fps_monom_poly_def polylog_def power_int_diff)
      finally show "(\<lambda>n. of_nat (Suc n) powi - k * z ^ (Suc n)) sums polylog k z"
        by (subst sums_Suc_iff) (use k in auto)
    qed
    ultimately show ?case
      using 0 by (auto simp: polylog_def [abs_def])
  next
    case (Suc k' k)
    have [simp]: "nat k = Suc k'" "nat (k - 1) = k'"
      using Suc(2) by auto
    from Suc(2) have k: "k > 0"
      by linarith
    have deriv: "(polylog (k - 1) has_field_derivative
            (if z = 0 then 1 else polylog (k - 2) z / z)) (at z)" if "z \<in> S (k - 1)" for z
      using Suc(1)[of "k-1"] that by auto
    hence holo: "polylog (k - 1) holomorphic_on S (k - 1)"
      by (subst holomorphic_on_open) auto

    have sums: "(\<lambda>n. of_nat (Suc n) powi -(k-1) * z ^ Suc n) sums polylog (k-1) z"
      if "norm z < 1" for z
      using that Suc(1)[of "k - 1"] by auto

    define g where "g = (\<lambda>z. if z = 0 then 1 else polylog (k - 1) z / z)"
    have "g holomorphic_on S (k - 1)"
      unfolding g_def
    proof (rule removable_singularity)
      show "(\<lambda>z. polylog (k - 1) z / z) holomorphic_on S (k - 1) - {0}"
        using Suc by (intro holomorphic_intros holomorphic_on_subset[OF holo]) auto

      define F where "F = Abs_fps (\<lambda>n. of_nat (Suc n) powi (1-k) :: complex)"
      have radius: "fls_conv_radius (fps_to_fls F) = 1"
      proof -
        have "F = fps_shift 1 (Abs_fps (\<lambda>n. of_int n powi (1 - k)))"
          using k by (simp add: F_def fps_eq_iff power_int_def)
        also have "fps_conv_radius \<dots> = 1"
          using conv_radius_polylog[of "1 - k"] unfolding fps_conv_radius_shift
          by (simp add: fps_conv_radius_def)
        finally show ?thesis by simp
      qed

      have "eventually (\<lambda>z::complex. z \<in> ball 0 1) (nhds 0)"
        by (intro eventually_nhds_in_open) auto
      hence "eventually (\<lambda>z::complex. z \<in> ball 0 1 - {0}) (at 0)"
        unfolding eventually_at_filter by eventually_elim auto
      hence "eventually (\<lambda>z. eval_fls (fps_to_fls F) z = polylog (k - 1) z / z) (at 0)"
      proof eventually_elim
        case (elim z)
        have "(\<lambda>n. of_nat (Suc n) powi - (k - 1) * z ^ Suc n / z) sums (polylog (k - 1) z / z)"
          by (intro sums_divide sums) (use elim in auto)
        also have "(\<lambda>n. of_nat (Suc n) powi - (k - 1) * z ^ Suc n / z) =
                   (\<lambda>n. of_nat (Suc n) powi - (k - 1) * z ^ n)"
          using elim by auto
        finally have "polylog (k - 1) z / z = (\<Sum>n. of_nat (Suc n) powi - (k - 1) * z ^ n)"
          by (simp add: sums_iff)
        also have "\<dots> = eval_fps F z"
          unfolding eval_fps_def F_def by simp
        finally show ?case
          using radius elim by (simp add: eval_fps_to_fls)
      qed
      hence "(\<lambda>z. polylog (k - 1) z / z) has_laurent_expansion fps_to_fls F"
        unfolding has_laurent_expansion_def using radius by auto
      hence "(\<lambda>z. polylog (k - 1) z / z) \<midarrow>0\<rightarrow> fls_nth (fps_to_fls F) 0"
        by (intro has_laurent_expansion_imp_tendsto_0 fls_subdegree_fls_to_fps_gt0) auto
      thus "(\<lambda>y. polylog (k - 1) y / y) \<midarrow>0\<rightarrow> 1"
        by (simp add: F_def)
    qed auto
    hence holo: "g holomorphic_on ?S"
      by (rule holomorphic_on_subset) (auto simp: S_def)
    have "simply_connected ?S"
      by (rule simply_connected_slotted_complex_plane_right)
    then obtain f where f: "\<And>z. z \<in> ?S \<Longrightarrow> (f has_field_derivative g z) (at z)"
      using simply_connected_eq_global_primitive holo \<open>open ?S\<close> by blast

    define h where "h = (\<lambda>z. f z - f 0)"
    have deriv_h [derivative_intros]: "(h has_field_derivative g z) (at z)" if "z \<in> ?S" for z
      unfolding h_def using that by (auto intro!: derivative_eq_intros f)
    hence holo_h: "h holomorphic_on S k" (is "?P1 h")
      by (subst holomorphic_on_open) (use k \<open>open ?S\<close> in \<open>auto simp: S_def\<close>)

    have summable: "summable (\<lambda>n. of_nat n powi (-k) * z ^ n)"
      if "norm z < 1" for z :: complex
      by (rule summable_in_conv_radius)
         (use that conv_radius_polylog[of "-k"] in auto)

    define F where "F = Abs_fps (\<lambda>n. of_nat n powi (-k) :: complex)"
    have radius: "fps_conv_radius F = 1"
      using conv_radius_polylog[of "-k"] by (simp add: fps_conv_radius_def F_def)

    have F_deriv [derivative_intros]:
      "(eval_fps F has_field_derivative g z) (at z)" if "z \<in> ball 0 1" for z
    proof -
      have "(eval_fps F has_field_derivative eval_fps (fps_deriv F) z) (at z)"
        using that radius by (auto intro!: derivative_eq_intros)
      also have "eval_fps (fps_deriv F) z = g z"
      proof (cases "z = 0")
        case False
        have "(\<lambda>n. of_nat (Suc n) powi - (k - 1) * z ^ Suc n / z) sums (polylog (k - 1) z / z)"
          by (intro sums_divide sums) (use that in auto)
        also have "\<dots> = g z"
          using False by (simp add: g_def)
        also have "(\<lambda>n. of_nat (Suc n) powi - (k - 1) * z ^ Suc n / z) =
                   (\<lambda>n. of_nat (Suc n) powi - (k - 1) * z ^ n)"
          using False by simp
        finally show ?thesis
          by (auto simp add: eval_fps_def F_def sums_iff power_int_diff power_int_minus field_simps
                   simp del: of_nat_Suc)
      qed (auto simp: F_def g_def eval_fps_at_0)
      finally show ?thesis .
    qed

    hence h_eq_sum: "h z = eval_fps F z" if "z \<in> ball 0 1" for z
    proof -
      have "\<exists>c. \<forall>z\<in>ball 0 1. h z - eval_fps F z = c"
      proof (rule has_field_derivative_zero_constant)
        fix z :: complex assume z: "z \<in> ball 0 1"
        have "((\<lambda>x. h x - eval_fps F x) has_field_derivative 0) (at z)"
          using z by (auto intro!: derivative_eq_intros)
        thus "((\<lambda>x. h x - eval_fps F x) has_field_derivative 0) (at z within ball 0 1)"
          using z by (subst at_within_open) auto
      qed auto
      then obtain c where c: "\<And>z. norm z < 1 \<Longrightarrow> h z - eval_fps F z = c"
        by force
      from c[of 0] and k have "c = 0"
        by (simp add: h_def F_def eval_fps_at_0)
      thus ?thesis
        using c[of z] that by auto
    qed

    have h_eq_sum': "(\<forall>z\<in>ball 0 1. h z = (\<Sum>n. of_nat (Suc n) powi - k * z ^ Suc n))" (is "?P2 h")
    proof safe
      fix z :: complex assume z: "z \<in> ball 0 1"
      have "summable (\<lambda>n. of_nat (Suc n) powi - k * z ^ Suc n)"
        using z summable[of z] by (subst summable_Suc_iff) auto
      also have "?this \<longleftrightarrow> summable (\<lambda>n. of_nat n powi - k * z ^ n)"
        by (rule summable_Suc_iff)
      finally have "(\<lambda>n. of_nat (Suc n) powi -k * z ^ Suc n) sums h z"
        using h_eq_sum[of z] k unfolding summable_Suc_iff
        by (subst sums_Suc_iff) (use z in \<open>auto simp: eval_fps_def F_def\<close>)
      thus "h z = (\<Sum>n. of_nat (Suc n) powi - k * z ^ Suc n)"
        by (simp add: sums_iff)
    qed

    define h' where "h' = (SOME h. ?P1 h \<and> ?P2 h)"
    have "\<exists>h. ?P1 h \<and> ?P2 h"
      using h_eq_sum' holo_h by blast
    from someI_ex[OF this] have h'_props: "?P1 h'" "?P2 h'"
      unfolding h'_def by blast+
    have h'_eq: "h' z = polylog k z" if "z \<in> S k" for z
      using that k by (auto simp: polylog_def h'_def S_def)

    have polylog_sums: "(\<lambda>n. of_nat (Suc n) powi (-k) * z ^ Suc n) sums polylog k z"
      if "norm z < 1" for z
    proof -
      have "summable (\<lambda>n. of_nat (Suc n) powi (-k) * z ^ Suc n)"
        using summable[of z] that by (subst summable_Suc_iff)
      moreover from that have "z \<in> S k"
        by (auto simp: S_def)
      ultimately show ?thesis
        using h'_props using that by (force simp: sums_iff h'_eq)
    qed

    have eq': "polylog k z = h z" if "z \<in> S k" for z
    proof -
      have "h' z = h z"
      proof (rule analytic_continuation_open[where g = h])
        show "h' holomorphic_on S k" "h holomorphic_on S k"
          by fact+
        show "ball 0 1 \<noteq> ({} :: complex set)" "open (ball 0 1 :: complex set)"
          by auto
        show "open (S k)" "connected (S k)" "ball 0 1 \<subseteq> S k"
          using k \<open>open ?S\<close> simply_connected_slotted_complex_plane_right[of 1]
          by (auto simp: S_def simply_connected_imp_connected)
        show "z \<in> S k"
          by fact
        show "h' z = h z" if "z \<in> ball 0 1" for z
          using h'_props(2) h_eq_sum' that by simp
      qed
      with that show ?thesis
        by (simp add: h'_eq)
    qed

    have deriv_polylog: "(polylog k has_field_derivative g z) (at z)" if "z \<in> S k" for z
    proof -
      have "(h has_field_derivative g z) (at z)"
        by (intro deriv_h) (use that k in \<open>auto simp: S_def\<close>)
      also have "?this \<longleftrightarrow> ?thesis"
      proof (rule DERIV_cong_ev)
        have "eventually (\<lambda>w. w \<in> S k) (nhds z)"
          by (intro eventually_nhds_in_open) (use that in auto)
        thus "eventually (\<lambda>w. h w = polylog k w) (nhds z)"
          by eventually_elim (auto simp: eq')
      qed auto
      finally show ?thesis .
    qed

    show ?case
      using deriv_polylog polylog_sums unfolding g_def by simp
  qed

  show "(polylog k has_field_derivative (if z = 0 then 1 else polylog (k - 1) z / z)) (at z within A)"
    if "z \<in> (if k \<le> 0 then -{1} else -(of_real ` {1..}))" for z
    using * that unfolding S_def by (blast intro: has_field_derivative_at_within)
  show "(\<lambda>n. of_nat (Suc n) powi (-k) * z ^ Suc n) sums polylog k z" if "norm z < 1" for z
    using * that by force
qed

lemma has_field_derivative_polylog' [derivative_intros]:
  assumes "(f has_field_derivative f') (at z within A)"
  assumes "if k \<le> 0 then f z \<noteq> 1 else Im (f z) \<noteq> 0 \<or> Re (f z) < 1"
  shows   "((\<lambda>z. polylog k (f z)) has_field_derivative
             (if f z = 0 then 1 else polylog (k-1) (f z) / f z) * f') (at z within A)"
proof -
  have "(polylog k \<circ> f has_field_derivative
          (if f z = 0 then 1 else polylog (k-1) (f z) / f z) * f') (at z within A)"
    using assms(2) by (intro DERIV_chain assms has_field_derivative_polylog) auto
  thus ?thesis
    by (simp add: o_def)
qed

lemma polylog_0 [simp]: "polylog k 0 = 0"
proof -
  have "(\<lambda>_. 0) sums polylog k 0"
    using sums_polylog[of 0 k] by simp
  moreover have "(\<lambda>_. 0 :: complex) sums 0"
    by simp
  ultimately show ?thesis
    using sums_unique2 by blast
qed

text \<open>
  A simple consequence of the derivative formula is the following recurrence for $\text{Li}_s$
  via a contour integral:
  \[\text{Li}_s(z) = \int_0^z \frac{1}{w}\text{Li}_{s-1}(w)\,\text{d}w\]
\<close>
theorem polylog_has_contour_integral:
  assumes "z \<notin> complex_of_real ` ({..-1} \<union> {1..})"
  shows   "((\<lambda>w. polylog s w / w) has_contour_integral polylog (s + 1) z) (linepath 0 z)"
proof -
  let ?l = "linepath 0 z"
  define A where "A = -complex_of_real ` ({..-1} \<union> {1..})"
  have "((\<lambda>w. if w = 0 then 1 else polylog s w / w) has_contour_integral
           (polylog (s + 1) (pathfinish ?l) - polylog (s + 1) (pathstart ?l))) (linepath 0 z)"
  proof (rule contour_integral_primitive)
    have [simp]: "complex_of_real x = -1 \<longleftrightarrow> x = -1" for x
      by (simp add: Complex_eq_neg_1 complex_of_real_def)
    show "(polylog (s + 1) has_field_derivative (if z = 0 then 1 else polylog s z / z)) 
            (at z within A)" if "z \<in> A" for z
      using that by (intro derivative_eq_intros) (auto simp: A_def split: if_splits)
  next
    show "valid_path (linepath 0 z)"
      by (rule valid_path_linepath)
  next
    show "path_image (linepath 0 z) \<subseteq> A"
      using assms starlike_doubly_slotted_complex_plane_aux[of z "-1" 1 0]
      by (auto simp: A_def)
  qed
  hence "((\<lambda>w. if w = 0 then 1 else polylog s w / w) has_contour_integral
           (polylog (s + 1) z)) (linepath 0 z)"
    by simp
  thus ?thesis
    unfolding has_contour_integral_def
  proof (rule has_integral_spike[rotated 2])
    show "negligible {0 :: real}"
      by simp
  qed (auto simp: vector_derivative_linepath_within)
qed

lemma sums_polylog':
  "norm z < 1 \<Longrightarrow> k \<noteq> 0 \<Longrightarrow> (\<lambda>n. of_nat n powi - k * z ^ n) sums polylog k z"
  using sums_polylog[of z k] by (subst (asm) sums_Suc_iff) auto

lemma polylog_altdef1:
  "norm z < 1 \<Longrightarrow> polylog k z = (\<Sum>n. of_nat (Suc n) powi -k * z ^ Suc n)"
  using sums_polylog[of z k] by (simp add: sums_iff)

lemma polylog_altdef2:
  "norm z < 1 \<Longrightarrow> k \<noteq> 0 \<Longrightarrow> polylog k z = (\<Sum>n. of_nat n powi -k * z ^ n)"
  using sums_polylog'[of z k] by (simp add: sums_iff)

lemma polylog_at_pole: "polylog k 1 = 0"
  by (auto simp: polylog_def)

lemma polylog_at_branch_cut: "x \<ge> 1 \<Longrightarrow> k > 0 \<Longrightarrow> polylog k (of_real x) = 0"
  by (auto simp: polylog_def)

lemma holomorphic_on_polylog [holomorphic_intros]:
  assumes "A \<subseteq> (if k \<le> 0 then -{1} else -of_real ` {1..})"
  shows   "polylog k holomorphic_on A"
proof -
  let ?S = "-(complex_of_real ` {1..})"
  have *: "open ?S"
    by (intro open_Compl closed_slot_right) 
  have "polylog k holomorphic_on (if k \<le> 0 then -{1} else ?S)"
    by (subst holomorphic_on_open) (use * in \<open>auto intro!: derivative_eq_intros exI\<close>)
  thus ?thesis
    by (rule holomorphic_on_subset) (use assms in \<open>auto split: if_splits\<close>)
qed

lemmas holomorphic_on_polylog' [holomorphic_intros] =
  holomorphic_on_compose_gen [OF _ holomorphic_on_polylog[OF order.refl], unfolded o_def]

lemma analytic_on_polylog [analytic_intros]:
  assumes "A \<subseteq> (if k \<le> 0 then -{1} else -of_real ` {1..})"
  shows   "polylog k analytic_on A"
proof -
  let ?S = "-(complex_of_real ` {1..})"
  have *: "open ?S"
    by (intro open_Compl closed_slot_right) 
  have "polylog k analytic_on (if k \<le> 0 then -{1} else ?S)"
    by (subst analytic_on_open) (use * in \<open>auto intro!: holomorphic_intros\<close>)
  thus ?thesis
    by (rule analytic_on_subset) (use assms in \<open>auto split: if_splits\<close>)
qed

lemmas analytic_on_polylog' [analytic_intros] =
  analytic_on_compose_gen [OF _ analytic_on_polylog[OF order.refl], unfolded o_def]

lemma continuous_on_polylog [analytic_intros]:
  assumes "A \<subseteq> (if k \<le> 0 then -{1} else -of_real ` {1..})"
  shows   "continuous_on A (polylog k)"
proof -
  let ?S = "-(complex_of_real ` {1..})"
  have *: "open ?S"
    by (intro open_Compl closed_slot_right) 
  have "continuous_on (if k \<le> 0 then -{1} else ?S) (polylog k)"
    by (intro holomorphic_on_imp_continuous_on holomorphic_intros) auto
  thus ?thesis
    by (rule continuous_on_subset) (use assms in auto)
qed

lemmas continuous_on_polylog' [continuous_intros] =
  continuous_on_compose2 [OF continuous_on_polylog [OF order.refl]]


subsection \<open>Special values\<close>

lemma polylog_neg_int_left:
  "k < 0 \<Longrightarrow> polylog k z = z * poly (eulerian_poly (nat (-k))) z * (1 - z) powi (k - 1)"
  by (auto simp: polylog_def)

lemma polylog_0_left: "polylog 0 z = z / (1 - z)"
  by (simp add: polylog_def field_simps)

lemma polylog_neg1_left: "polylog (-1) x = x / (1 - x) ^ 2"
  by (simp add: polylog_neg_int_left eval_nat_numeral eulerian_poly.simps
                power_int_minus field_simps)

lemma polylog_neg2_left: "polylog (-2) x = x * (1 + x) / (1 - x) ^ 3"
  by (simp add: polylog_neg_int_left eval_nat_numeral eulerian_poly.simps
                power_int_minus field_simps)

lemma polylog_neg3_left: "polylog (-3) x = x * (1 + 4 * x + x\<^sup>2) / (1 - x) ^ 4"
  by (simp add: polylog_neg_int_left eval_nat_numeral eulerian_poly.simps Let_def pderiv_add
                pderiv_pCons power_int_minus field_simps numeral_poly)

lemma polylog_1: 
  assumes "z \<notin> of_real ` {1..}"
  shows   "polylog 1 z = -ln (1 - z)"
proof -
  have "(\<lambda>z. polylog 1 z + ln (1 - z)) constant_on -of_real ` {1..}"
  proof (rule has_field_derivative_0_imp_constant_on)
    show "connected (-complex_of_real ` {1..})"
      using starlike_slotted_complex_plane_right[of 1] starlike_imp_connected by blast
    show "open (- complex_of_real ` {1..})"
      using closed_slot_right by blast
    show "((\<lambda>z. polylog 1 z + ln (1 - z)) has_field_derivative 0) (at z)"
      if "z \<in> -of_real ` {1..}" for z
      using that
      by (auto intro!: derivative_eq_intros simp: complex_nonpos_Reals_iff
                       complex_slot_right_eq polylog_0_left divide_simps)
  qed
  then obtain c where c: "\<And>z. z \<in> -of_real`{1..} \<Longrightarrow> polylog 1 z + ln (1 - z) = c"
    unfolding constant_on_def by blast
  from c[of 0] have "c = 0"
    by (auto simp: complex_slot_right_eq)
  with c[of z] show ?thesis
    using assms by (auto simp: add_eq_0_iff)
qed

lemma is_pole_polylog_1:
  assumes "k \<le> 0"
  shows   "is_pole (polylog k) 1"
proof (cases "k = 0")
  case True
  have "filtermap (\<lambda>z. -z) (filtermap (\<lambda>z. z - 1) (at 1)) = filtermap (\<lambda>z. -z) (at (0 :: complex))"
    by (simp add: at_to_0' filtermap_filtermap)
  also have "\<dots> = at 0"
    by (subst filtermap_at_minus) auto
  finally have "filtermap ((\<lambda>z. -z) \<circ> (\<lambda>z. z - 1)) (at 1) = at (0 :: complex)"
    unfolding filtermap_compose .
  hence *: "filtermap (\<lambda>z. 1 - z) (at 1) = at (0 :: complex)"
    by (simp add: o_def)

  have "is_pole (\<lambda>z::complex. z / (1 - z)) 1"
    unfolding is_pole_def
    by (rule filterlim_divide_at_infinity tendsto_intros)+
       (use * in \<open>auto simp: filterlim_def\<close>)
  also have "(\<lambda>z. z / (1 - z)) = polylog k"
    using True by (auto simp: fun_eq_iff polylog_0_left)
  finally show ?thesis .
next
  case False
  have "\<forall>\<^sub>F x in at 1. x \<noteq> (1 :: complex)"
    using eventually_at zero_less_one by blast
  hence ev: "\<forall>\<^sub>F x in at 1. 1 - x \<noteq> (0 :: complex)"
    by eventually_elim auto    
  have "is_pole (\<lambda>z::complex. z * poly (eulerian_poly (nat (- k))) z * (1 - z) powi (k - 1)) 1"
    unfolding is_pole_def
    by (rule tendsto_mult_filterlim_at_infinity tendsto_eq_intros refl ev
             filterlim_power_int_neg_at_infinity | (use assms in simp; fail))+
  also have "(\<lambda>z::complex. z * poly (eulerian_poly (nat (- k))) z * (1 - z) powi (k - 1)) =
             polylog k"
    using assms False by (intro ext) (simp add: polylog_neg_int_left)
  finally show ?thesis .
qed

lemma zorder_polylog_1:
  assumes "k \<le> 0"
  shows   "zorder (polylog k) 1 = k - 1"
proof (cases "k = 0")
  case True
  have "filtermap (\<lambda>z. -z) (filtermap (\<lambda>z. z - 1) (at 1)) = filtermap (\<lambda>z. -z) (at (0 :: complex))"
    by (simp add: at_to_0' filtermap_filtermap)
  also have "\<dots> = at 0"
    by (subst filtermap_at_minus) auto
  finally have "filtermap ((\<lambda>z. -z) \<circ> (\<lambda>z. z - 1)) (at 1) = at (0 :: complex)"
    unfolding filtermap_compose .
  hence *: "filtermap (\<lambda>z. 1 - z) (at 1) = at (0 :: complex)"
    by (simp add: o_def)

  have "zorder (\<lambda>z::complex. (-z) / (z - 1) ^ 1) 1 = -int 1"
    by (rule zorder_nonzero_div_power [of UNIV]) (auto intro!: holomorphic_intros)
  also have "(\<lambda>z. (-z) / (z - 1) ^ 1) = polylog k"
    using True by (auto simp: fun_eq_iff polylog_0_left divide_simps) (auto simp: algebra_simps)?
  finally show ?thesis
    using True by simp
next
  case False
  have "zorder (\<lambda>z::complex. (-1) ^ nat (1 - k) * z * poly (eulerian_poly (nat (- k))) z /
                  (z - 1) ^ nat (1 - k)) 1 = -int (nat (1 - k))" (is "zorder ?f _ = _")
    using False assms
    by (intro zorder_nonzero_div_power [of UNIV]) (auto intro!: holomorphic_intros)
  also have "?f = polylog k"
  proof
    fix z :: complex
    have "(z - 1) ^ nat (1 - k) = (-1) ^ nat (1 - k) * (1 - z) ^ nat (1 - k)"
      by (subst power_mult_distrib [symmetric]) auto
    thus "?f z = polylog k z"
      using False assms by (auto simp: polylog_neg_int_left power_int_def field_simps)
  qed
  finally show ?thesis 
    using False assms by simp
qed

lemma isolated_singularity_polylog_1:
  assumes "k \<le> 0"       
  shows   "isolated_singularity_at (polylog k) 1"
  unfolding isolated_singularity_at_def using assms
  by (intro exI[of _ 1]) (auto intro!: analytic_intros)

lemma not_essential_polylog_1:
  assumes "k \<le> 0"       
  shows   "not_essential (polylog k) 1"
  unfolding not_essential_def using is_pole_polylog_1[of k] assms by auto

lemma polylog_meromorphic_on [meromorphic_intros]:
  assumes "k \<le> 0"
  shows   "polylog k meromorphic_on UNIV {1}"
  using assms
  by (intro meromorphic_onI)
     (auto intro!: holomorphic_intros isolated_singularity_polylog_1 not_essential_polylog_1
           simp: islimpt_finite)


subsection \<open>Duplication formula\<close>

text \<open>
  Lastly, we prove the following duplication formula that the polylogarithm satisfies:
  \[\text{Li}_s(z) + \text{Li}_s(-z) = 2^{1-s} \text{Li}_s(z^2)\]
  The proof is a relatively simple manipulation of infinite sum that defines $\text{Li}_s(z)$
  for $|z|<1$, followed by analytic continuation to its full domain.
\<close>
theorem polylog_duplication:
  assumes "if s \<le> 0 then z \<notin> {-1, 1} else z \<notin> complex_of_real ` ({..-1} \<union> {1..})"
  shows   "polylog s z + polylog s (-z) = 2 powi (1 - s) * polylog s (z\<^sup>2)"
proof -
  define A where "A = -(if s \<le> 0 then {-1, 1} else complex_of_real ` ({..-1} \<union> {1..}))"
  show ?thesis
  proof (rule analytic_continuation_open[where f = "\<lambda>z. polylog s z + polylog s (-z)"])
    show "ball 0 1 \<subseteq> A"
      by (auto simp: A_def)
  next
    have "closed (complex_of_real ` ({..-1} \<union> {1..}))"
      unfolding image_Un by (intro open_Compl closed_Un closed_slot_right closed_slot_left)
    thus "open A"
      unfolding A_def by auto
  next
    have "connected (-complex_of_real ` ({..-1} \<union> {1..}))"
      by (intro simply_connected_imp_connected simply_connected_doubly_slotted_complex_plane) auto
    moreover have "connected (-{-1, 1 :: complex})"
      by (intro path_connected_imp_connected path_connected_complement_countable) auto
    ultimately show "connected A"
      unfolding A_def by auto
  next
    show "(\<lambda>z. polylog s z + polylog s (- z)) holomorphic_on A"
      by (intro holomorphic_intros) (auto simp: complex_eq_iff A_def)
  next
    show "(\<lambda>z. 2 powi (1 - s) * polylog s (z\<^sup>2)) holomorphic_on A"
    proof (intro holomorphic_intros; safe)
      fix z assume z: "z \<in> A"
      show "z^2 \<in> (if s \<le> 0 then - {1} else - complex_of_real ` {1..})"
      proof (cases "s \<le> 0")
        case True
        thus ?thesis using z by (auto simp: A_def power2_eq_1_iff)
      next
        case False
        {
          fix x :: real
          assume x: "x \<ge> 1" "z ^ 2 = of_real x"
          have "Im (z ^ 2) = 0"
            by (simp add: x)
          hence "Im z = 0 \<or> Re z = 0"
            by (simp add: power2_eq_square)
          moreover have "Im z ^ 2 \<ge> 0"
            by auto
          hence "Im z ^ 2 > -1"
            by linarith
          ultimately have "x = Re z ^ 2" "Im z = 0"
            using x unfolding power2_eq_square by (auto simp: complex_eq_iff)
          with x have "\<bar>Re z\<bar> \<ge> 1"
            by (auto simp: power2_ge_1_iff)
          with \<open>Im z = 0\<close> have "z \<notin> A"
            using False by (auto simp: A_def complex_double_slot_eq)
        }
        with False show ?thesis using z
          by (auto simp: A_def)
      qed
    qed
  next
    show "polylog s z + polylog s (-z) = 2 powi (1 - s) * polylog s (z\<^sup>2)"
      if z: "z \<in> ball 0 1" for z
    proof -
      have ran: "range (\<lambda>n::nat. Suc (2 * n)) = {n. odd n}"
        by (auto simp: image_def elim!: oddE)
      have "(\<lambda>n. of_nat (Suc n) powi -s * (z ^ Suc n + (-z) ^ Suc n)) sums
               (polylog s z + polylog s (-z))" (is "?f sums _")
        unfolding ring_distribs using z 
        by (intro sums_add sums_mult sums_polylog) (simp_all add: norm_power)
      also have "?this \<longleftrightarrow> (\<lambda>n. ?f (2 * n + 1)) sums (polylog s z + polylog s (-z))"
        by (rule sym, intro sums_mono_reindex) (auto simp: ran strict_mono_def)
      also have "(\<lambda>n. ?f (2 * n + 1)) = (\<lambda>n. 2 * (2 * of_nat (Suc n)) powi -s * (z\<^sup>2) ^ Suc n)"
        by (intro ext) (simp_all add: algebra_simps power_mult power2_eq_square power_minus')
      also have "\<dots> = (\<lambda>n. 2 powi (1 - s) * (of_nat (Suc n) powi -s * (z\<^sup>2) ^ Suc n))" (is "_ = ?g")
        by (simp add: power_int_diff power_int_minus fun_eq_iff field_simps
                 flip: power_int_mult_distrib)
      finally have "?g sums (polylog s z + polylog s (-z))" .
      moreover have "?g sums (2 powi (1 - s) * polylog s (z\<^sup>2))"
        using z by (intro sums_mult sums_polylog) (simp_all add: norm_power abs_square_less_1)
      ultimately show ?thesis
        using sums_unique2 by blast
    qed
  qed (use assms in \<open>auto simp: A_def\<close>)
qed

end