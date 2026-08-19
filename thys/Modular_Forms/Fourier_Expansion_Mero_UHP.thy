section \<open>$q$-expansions of periodic functions\<close>
theory Fourier_Expansion_Mero_UHP
imports
  "HOL-Complex_Analysis.Complex_Analysis"
  "HOL-Real_Asymp.Real_Asymp"
  Meromorphic_Upper_Half_Plane
  Elliptic_Functions.Z_Plane_Q_Disc
  Elliptic_Functions.FPS_Homomorphism
  Modular_Forms_Library
begin

subsection \<open>The zero order at the cusp\<close>

definition eval_mero_uhp_at_ii_inf :: "mero_uhp \<Rightarrow> complex" where
  "eval_mero_uhp_at_ii_inf f = (if \<exists>L. (f \<longlongrightarrow> L) at_\<i>\<infinity> then Lim at_\<i>\<infinity> f else 0)"

lemma eval_mero_uhp_at_ii_inf_eqI:
  "(eval_mero_uhp f \<longlongrightarrow> c) at_\<i>\<infinity> \<Longrightarrow> eval_mero_uhp_at_ii_inf f = c"
  unfolding eval_mero_uhp_at_ii_inf_def by (auto intro: tendsto_Lim)

definition zorder_at_ii_inf :: "nat \<Rightarrow> mero_uhp \<Rightarrow> int" where
  "zorder_at_ii_inf period f =
     (if period = 0 \<or> f = 0 then 0 else (THE n. eval_mero_uhp f \<in> \<Theta>[at_\<i>\<infinity>](\<lambda>z. to_q period z powi n)))"

definition is_pole_ii_inf where "is_pole_ii_inf f \<longleftrightarrow> filterlim (eval_mero_uhp f) at_infinity at_\<i>\<infinity>"

lemma zorder_at_ii_inf_0 [simp]: "zorder_at_ii_inf period 0 = 0"
  by (auto simp: zorder_at_ii_inf_def)

lemma zorder_at_ii_inf_unique:
  assumes "k > 0"
  shows   "\<exists>\<^sub>\<le>\<^sub>1 n. f \<in> \<Theta>[at_\<i>\<infinity>](\<lambda>x. to_q k x powi n)" (is "Uniq ?P")
proof
  fix m n assume mn: "?P m" "?P n"
  have lim: "filterlim (\<lambda>x. of_real x * \<i>) at_ii_inf at_top"
    by (simp add: at_ii_inf_def filterlim_filtercomap_iff o_def filterlim_ident)
  from mn have "(\<lambda>z. to_q k z powi m) \<in> \<Theta>[at_ii_inf](\<lambda>z. to_q k z powi n)"
    using landau_theta.trans bigtheta_sym by metis
  hence "(\<lambda>x. to_q k (of_real x * \<i>) powi m) \<in> \<Theta>(\<lambda>x. to_q k (of_real x * \<i>) powi n)"
    using lim by (rule landau_theta.compose)
  hence "(\<lambda>x. exp (- (2 * pi * x * m / k))) \<in> \<Theta>(\<lambda>x. exp (- (2 * pi * x * n / k)))"
    by (subst (asm) landau_theta.norm_iff [symmetric], simp only: norm_power_int)
       (simp_all add: exp_power_int mult.commute)
  thus "m = n"
  proof (induction m n rule: linorder_wlog)
    case (le m n)
    let ?f = "\<lambda>n z. exp ((2 * pi * z * n / k))"
    show "m = n"
    proof (rule ccontr)
      assume "m \<noteq> n"
      with le.hyps have "m < n"
        by auto
      have "(\<lambda>_. 1) \<in> o(\<lambda>x. exp (2 * pi * x / real k * real_of_int (n - m)))"
        using \<open>k > 0\<close> \<open>m < n\<close> by real_asymp
      also {
        have "(\<lambda>x. exp ((2 * pi * x * n / k) - (2 * pi * x * m / k))) \<in> \<Theta>(\<lambda>x. 1)"
          using landau_theta.mult[OF le.prems bigtheta_refl[of "?f n"]]
          by (simp add: exp_minus exp_diff field_simps)
        also have "(\<lambda>x. (2 * pi * x * n / k) - (2 * pi * x * m / k)) =
                   (\<lambda>x. 2 * pi * x / k * (n - m))"
          using \<open>k > 0\<close> by (auto simp: field_simps fun_eq_iff)
        finally have "(\<lambda>x. exp (2 * pi * x / real k * real_of_int (n - m))) \<in> \<Theta>(\<lambda>x. 1)" .
      }
      finally show False
        by (simp add: landau_o.small_refl_iff)
    qed
  qed (simp add: bigtheta_sym eq_commute)
qed 

lemma zorder_at_ii_inf_eqI:
  assumes "eval_mero_uhp f \<in> \<Theta>[at_\<i>\<infinity>](\<lambda>x. to_q k x powi n)" "k > 0"
  shows   "zorder_at_ii_inf k f = n"
proof -
  have [simp]: "f \<noteq> 0"
    using assms by auto
  have "zorder_at_ii_inf k f = (THE n. eval_mero_uhp f \<in> \<Theta>[at_ii_inf](\<lambda>z. to_q k z powi n))"
    using assms by (simp add: zorder_at_ii_inf_def)
  also have "(THE n. eval_mero_uhp f \<in> \<Theta>[at_ii_inf](\<lambda>z. to_q k z powi n)) = n"
    using zorder_at_ii_inf_unique assms(1) by (rule the1_equality') fact
  finally show ?thesis .
qed

abbreviation "zorder_mero_uhp f \<equiv> zorder (eval_mero_uhp f)"



subsection \<open>Expansion in terms of \<open>q\<close>\<close>

text \<open>
  Let \<open>f(\<tau>)\<close> be a meromorphic function on the halfplane $\{\tau \mid \text{Im}(\tau) > c\}$
  with period $n$. The variable change $q = 2i\pi\tau/n$ gives us a function $f(q)$ that is 
  meromorphic on a punctured disc of radius $e^{-2\pi c}$ around 0. The point $q = 0$ corresponds 
  to $\tau = i\infty$. Thus, this function $f(q)$ can be viewed as the expansion of $f(\tau)$ at 
  the point $\tau = i\infty$.
\<close>

definition fourier_expansion :: "nat \<Rightarrow> mero_uhp \<Rightarrow> complex \<Rightarrow> complex" where
  "fourier_expansion period f =
     (\<lambda>z. if z = 0 then remove_sings (eval_mero_uhp f \<circ> of_q period) 0 
          else eval_mero_uhp f (of_q period z))"

lemma fourier_expansion_0 [simp]: "fourier_expansion period 0 z = 0"
  by (auto simp: fourier_expansion_def)

definition laurent_expansion_at_ii_inf :: "nat \<Rightarrow> mero_uhp \<Rightarrow> complex fls" ("laurent'_expansion'_at'_\<i>\<infinity>") where
  "laurent_expansion_at_ii_inf period f = laurent_expansion (fourier_expansion period f) 0"

definition fps_expansion_at_ii_inf :: "nat \<Rightarrow> mero_uhp \<Rightarrow> complex fps" ("fps'_expansion'_at'_\<i>\<infinity>") where
  "fps_expansion_at_ii_inf period f = fps_expansion (fourier_expansion period f) 0"

definition meromorphic_at_infinity :: "modgrp set \<Rightarrow> mero_uhp \<Rightarrow> bool" where
  "meromorphic_at_infinity G f \<longleftrightarrow>
     fourier_expansion (cusp_width\<^sub>\<infinity> G) f meromorphic_on {0}"

definition holomorphic_at_infinity :: "mero_uhp \<Rightarrow> bool" where
  "holomorphic_at_infinity f \<longleftrightarrow> (\<exists>c. (f \<longlongrightarrow> c) at_\<i>\<infinity>)"

lemma holomorphic_at_infinity_const [simp, intro]: "holomorphic_at_infinity (const_mero_uhp c)"
proof -
  have "((\<lambda>z. eval_mero_uhp (const_mero_uhp c) z) \<longlongrightarrow> c) at_\<i>\<infinity>"
  proof (rule Lim_transform_eventually)
    show "eventually (\<lambda>z. c = eval_mero_uhp (const_mero_uhp c) z) at_\<i>\<infinity>"
      using eventually_at_ii_inf[of 0] by eventually_elim auto
  qed auto
  thus ?thesis
    unfolding holomorphic_at_infinity_def by blast
qed

lemma holomorphic_at_infinity_0 [simp, intro]: "holomorphic_at_infinity 0"
  using holomorphic_at_infinity_const[of 0]
  by (simp del: holomorphic_at_infinity_const)

lemma holomorphic_at_infinity_1 [simp, intro]: "holomorphic_at_infinity 1"
  using holomorphic_at_infinity_const[of 1]
  by (simp del: holomorphic_at_infinity_const)



locale fourier_expansion_context =
  fixes period :: nat
  assumes period_pos: "period > 0"
begin

abbreviation (input) fourier_expansion' (\<open>(\<open>notation=\<open>postfix q\<close>\<close>_\<^sup>q)\<close> [1000] 1000) where
  "fourier_expansion' \<equiv> fourier_expansion period"

end


locale fourier_expansion_locale =
  fixes period :: nat and f :: mero_uhp
  assumes period_pos: "period > 0"
  assumes invariant_compose_shift_period: "compose_modgrp_mero_uhp f (shift_modgrp period) = f"
begin

sublocale periodic_fun_simple "eval_mero_uhp f" "of_nat period"
proof
  fix z :: complex
  show "eval_mero_uhp f (z + of_nat period) = eval_mero_uhp f z"
  proof (cases "Im z > 0")
    case True
    have "eval_mero_uhp f (z + of_nat period) =
          eval_mero_uhp (compose_modgrp_mero_uhp f (shift_modgrp period)) z"
      using True by simp
    also have "compose_modgrp_mero_uhp f (shift_modgrp period) = f"
      by (rule invariant_compose_shift_period)
    finally show ?thesis .
  qed (auto simp: eval_mero_uhp_outside)
qed

lemma fourier_expansion_locale_mono:
  assumes "period dvd period'" "period' > 0"
  shows   "fourier_expansion_locale period' f"
proof
  obtain k where k: "period' = period * k"
    using assms(1) by (elim dvdE)
  have "compose_modgrp_mero_uhp f (shift_modgrp (int period) ^ k) = f"
    by (induction k)
       (simp_all add: compose_modgrp_mero_uhp_mult_right invariant_compose_shift_period)
  also have "shift_modgrp (int period) ^ k = shift_modgrp (int period')"
    by (simp add: k shift_modgrp_power)
  finally show "compose_modgrp_mero_uhp f (shift_modgrp (int period')) = f" .
qed (use assms in auto)

lemma invariant_compose_shift [simp]:
  assumes "period dvd n"
  shows   "compose_modgrp_mero_uhp f (shift_modgrp n) = f"
proof (rule mero_uhp_eqI)
  from assms obtain k where k: "n = period * k"
    by (elim dvdE)
  have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (cosparse \<H>)"
    by (intro eventually_in_cosparse open_halfspace_Im_gt) auto
  thus "eventually (\<lambda>z. compose_modgrp_mero_uhp f (shift_modgrp n) z = f z) (cosparse \<H>)"
    by eventually_elim (auto simp: k plus_of_nat mult.commute)
qed

interpretation ctxt: fourier_expansion_context period
  by standard (rule period_pos)

lemma fourier_nz_eq:
  assumes q: "q \<noteq> 0"
  shows "f\<^sup>q q = f (of_q period q)"
  using assms by (auto simp: fourier_expansion_def)

lemma fourier_0_aux:
  assumes "(f \<longlongrightarrow> y) at_\<i>\<infinity>"
  shows   "f\<^sup>q 0 = y"
proof -
  have "f\<^sup>q 0 = remove_sings (eval_mero_uhp f \<circ> of_q period) 0"
    by (simp add: fourier_expansion_def)
  also have "\<dots> = y" unfolding o_def
    by (rule remove_sings_eqI filterlim_compose[OF _ filterlim_of_q_at_0] assms period_pos)+
  finally show ?thesis .
qed

lemma isCont_0_aux:
  assumes "(f \<longlongrightarrow> y) at_\<i>\<infinity>"
  shows   "isCont f\<^sup>q 0"
proof -
  have "((\<lambda>q. f (of_q period q)) \<longlongrightarrow> y) (at 0)"
    by (rule filterlim_compose[OF assms filterlim_of_q_at_0]) (use period_pos in auto)
  also have "eventually (\<lambda>q::complex. q \<noteq> 0) (at 0)"
    by (auto simp: eventually_at intro: exI[of _ 1])
  hence "eventually (\<lambda>q. f (of_q period q) = f\<^sup>q q) (at 0)"
    by eventually_elim (auto simp: fourier_nz_eq)
  hence "((\<lambda>q. f (of_q period q)) \<longlongrightarrow> y) (at 0) \<longleftrightarrow> (f\<^sup>q \<longlongrightarrow> y) (at 0)"
    by (intro filterlim_cong) auto
  finally show ?thesis
    using assms by (simp add: isCont_def fourier_0_aux)
qed

lemma fourier_to_q [simp]: "f\<^sup>q (to_q period \<tau>) = f \<tau>"
proof -
  obtain n where n: "of_q period (to_q period \<tau>) = \<tau> + of_int n * of_nat period"
    using of_q_to_q period_pos by blast
  show ?thesis
    by (simp add: fourier_expansion_def n plus_of_int)
qed

lemma fourier_expansion_mult_period:
  assumes k: "k > 0"
  shows "fourier_expansion (period * k) f q = fourier_expansion period f (q ^ k)"
proof -
  have *: "fourier_expansion (period * k) f q = fourier_expansion period f (q ^ k)"
    if q: "q \<noteq> 0" for q
  proof -
    define z where "z = of_q (period * k) q"
    have "fourier_expansion (period * k) f q = f z"
      using q by (auto simp: fourier_expansion_def z_def)
    also have "f z = fourier_expansion period f (to_q period z)"
      by simp
    also have "to_q period z = q powr of_nat k"
      using period_pos q unfolding powr_def by (simp add: to_q_def of_q_def z_def mult_ac)
    also have "\<dots> = q ^ k"
      using q by (subst powr_nat) auto
    finally show ?thesis .
  qed

  show ?thesis
  proof (cases "q = 0")
    case [simp]: True
    have "remove_sings (eval_mero_uhp f \<circ> of_q (period * k)) 0 =
          remove_sings (eval_mero_uhp f \<circ> of_q period \<circ> (\<lambda>q. q ^ k)) 0"
    proof (intro remove_sings_cong)
      have "eventually (\<lambda>q. q \<noteq> 0) (at (0::complex))"
        by (rule eventually_neq_at_within)
      thus "eventually (\<lambda>q. (eval_mero_uhp f \<circ> of_q (period * k)) q = 
                            (eval_mero_uhp f \<circ> of_q period \<circ> (\<lambda>q. q ^ k)) q) (at 0)"
      proof eventually_elim
        case (elim q)
        thus ?case
          using *[of q] by (simp add: fourier_expansion_def)
      qed
    qed auto
    also have "\<dots> = remove_sings (eval_mero_uhp f \<circ> of_q period) 0"
      by (rule remove_sings_compose[OF filtermap_power_at_0_complex]) fact+
    finally show ?thesis using k
      by (simp add: fourier_expansion_def)
  qed (use *[of q] in auto)
qed

lemma has_laurent_expansion_fourier_mult_period:
  assumes "f\<^sup>q has_laurent_expansion F" "k > 0"
  shows   "fourier_expansion (period * k) f has_laurent_expansion fls_compose_fps F (fps_X ^ k)"
proof -
  have "(fourier_expansion period f \<circ> (\<lambda>q. q ^ k)) has_laurent_expansion fls_compose_fps F (fps_X ^ k)"
    by (intro laurent_expansion_intros assms has_laurent_expansion_fps fps_expansion_intros)
       (use \<open>k > 0\<close> in auto)
  also have "fourier_expansion period f \<circ> (\<lambda>q. q ^ k) = fourier_expansion (period * k) f"
    by (rule ext, subst fourier_expansion_mult_period) (use \<open>k > 0\<close> in auto)
  finally show ?thesis .
qed

lemma has_fps_expansion_fourier_mult_period:
  assumes "f\<^sup>q has_fps_expansion F" "k > 0"
  shows   "fourier_expansion (period * k) f has_fps_expansion fps_compose F (fps_X ^ k)"
proof -
  have "(fourier_expansion period f \<circ> (\<lambda>q. q ^ k)) has_fps_expansion fps_compose F (fps_X ^ k)"
    by (intro laurent_expansion_intros assms has_laurent_expansion_fps fps_expansion_intros)
       (use \<open>k > 0\<close> in auto)
  also have "fourier_expansion period f \<circ> (\<lambda>q. q ^ k) = fourier_expansion (period * k) f"
    by (rule ext, subst fourier_expansion_mult_period) (use \<open>k > 0\<close> in auto)
  finally show ?thesis .
qed

lemma filtermap_fourier_expansion_at_0: "filtermap f\<^sup>q (at 0) = filtermap f at_\<i>\<infinity>"
  by (simp add: period_pos filtermap_filtermap flip: at_ii_inf_filtermap[of period])

lemma fourier_tendsto_0_iff: "f\<^sup>q \<midarrow>0\<rightarrow> y \<longleftrightarrow> (f \<longlongrightarrow> y) at_\<i>\<infinity>"
proof
  assume "(f \<longlongrightarrow> y) at_\<i>\<infinity>"
  thus "f\<^sup>q \<midarrow>0\<rightarrow> y"
    using continuous_within isCont_0_aux fourier_0_aux by blast
next
  assume *: "f\<^sup>q \<midarrow>0\<rightarrow> y"
  have "((\<lambda>z. f\<^sup>q (to_q period z)) \<longlongrightarrow> y) at_\<i>\<infinity>"
    by (rule filterlim_compose[OF * filterlim_to_q_at_ii_inf]) (use period_pos in auto)
  also have "(\<lambda>z. f\<^sup>q (to_q period z)) = f"
    by simp
  finally show "(f \<longlongrightarrow> y) at_\<i>\<infinity>" .
qed

lemma fourier_is_pole_0_iff:
  "is_pole f\<^sup>q 0 \<longleftrightarrow> filterlim f at_infinity at_\<i>\<infinity>" 
proof -
  have "is_pole f\<^sup>q 0 \<longleftrightarrow> (LIM q at 0. f (of_q period q) :> at_infinity)"
    unfolding is_pole_def fourier_expansion_def
    by (rule filterlim_cong) (auto simp add: linordered_field_no_ub eventually_at)
  also have "... \<longleftrightarrow> (LIM x at_\<i>\<infinity>. f x :> at_infinity)"
  proof
    assume "LIM q at 0. f (of_q period q) :> at_infinity"
    from filterlim_compose[OF this filterlim_to_q_at_ii_inf, of period] 
    have "LIM x at_\<i>\<infinity>. f (of_q period (to_q period x)) :> at_infinity"
      using period_pos by simp
    then show "filterlim f at_infinity at_\<i>\<infinity>"
    proof (elim filterlim_mono_eventually)
      show "\<forall>\<^sub>F x in at_\<i>\<infinity>. f (of_q period (to_q period x)) = f x" using period_pos
        by (smt (verit, ccfv_SIG) to_q_nonzero eventuallyI fourier_to_q fourier_nz_eq)
    qed auto
  next
    assume "filterlim f at_infinity at_\<i>\<infinity> "
    from filterlim_compose[OF this filterlim_of_q_at_0, of period]
    show "LIM x at 0. f (of_q period x) :> at_infinity"
      using period_pos by simp
  qed
  finally show ?thesis .
qed

lemma fourier_is_pole_to_q_iff: "is_pole f\<^sup>q (to_q period z) \<longleftrightarrow> is_pole f z"
proof -
  have "is_pole f z \<longleftrightarrow> is_pole (f\<^sup>q \<circ> to_q period) z"
    by (rule is_pole_cong) simp_all
  also have "\<dots> \<longleftrightarrow> is_pole f\<^sup>q (to_q period z)"
    by (rule is_pole_compose_iff) (simp_all add: filtermap_to_q_at period_pos)
  finally show ?thesis ..
qed

lemma has_field_derivative_fourier:
  assumes "\<not>is_pole (eval_mero_uhp f) z" "Im z > 0"
  assumes q: "q = to_q period z"
  defines "f' \<equiv> eval_mero_uhp (deriv_mero_uhp f) z"
  shows   "(f\<^sup>q has_field_derivative
              f' * period / (of_real (2 * pi) * \<i> * q)) (at q within A)"
proof -
  have [simp]: "q \<noteq> 0"
    using q by auto
  have "open (-{0 :: complex})"
    by (auto intro: open_halfspace_Im_gt)
  then obtain r where r: "r > 0" "ball q r \<subseteq> -{0 :: complex}"
    unfolding open_contains_ball using \<open>q \<noteq> 0\<close> by blast
  have "simply_connected (ball q r)"
    by (auto intro!: convex_imp_simply_connected)
  moreover have "(\<lambda>q. q) holomorphic_on ball q r" "\<forall>q\<in>ball q r. q \<noteq> 0"
    using r by (auto intro!: holomorphic_intros)
  ultimately obtain myln :: "complex \<Rightarrow> complex"
      where myln_holo: "myln holomorphic_on ball q r" and "\<And>q'. q' \<in> ball q r \<Longrightarrow> q' = exp (myln q')"
    unfolding simply_connected_eq_holomorphic_log[OF open_ball] by blast
  from this(2) have exp_myln: "exp (myln q') = q'" if "q' \<in> ball q r" for q'
    using that by metis

  have [derivative_intros]: "(myln has_field_derivative 1 / q) (at q)"
    by (rule has_field_derivative_complex_logarithm[where A = "ball q r"])
       (use myln_holo exp_myln \<open>r > 0\<close> in auto)

  have "((f \<circ> (\<lambda>q. of_nat period * myln q / (of_real (2 * pi) * \<i>))) has_field_derivative 
           f' * (of_nat period / (of_real (2 * pi) * \<i> * q))) (at q)"
  proof (rule DERIV_chain)
    define z' where "z' = of_nat period * myln q / (complex_of_real (2 * pi) * \<i>)"
    have "to_q period z = to_q period z'"
      using exp_myln[of q] q r(1) by (simp add: z'_def to_q_def)
    then obtain n where n: "z' = z + of_int n * of_nat period"
      using to_q_eq_to_qE period_pos by blast

    have "((f \<circ> (\<lambda>w. w + z - z')) has_field_derivative f' * 1) (at z')"
      unfolding f'_def using assms by (intro DERIV_chain) (auto intro!: derivative_eq_intros)
    also have "(\<lambda>w. w + z - z') = (\<lambda>w. w - of_int n * of_nat period)"
      using n by (auto simp: fun_eq_iff)
    also have "(f \<circ> (\<lambda>w. w - of_int n * of_nat period) has_field_derivative f' * 1) (at z') \<longleftrightarrow>
               (f has_field_derivative f') (at z')"
      by (intro DERIV_cong_ev always_eventually) (auto simp: minus_of_int)
    finally show "(f has_field_derivative f') (at z')"
      by simp
  next
    show "((\<lambda>q. of_nat period * myln q / (complex_of_real (2 * pi) * \<i>)) 
            has_field_derivative (of_nat period / (2 * pi * \<i> * q))) (at q)"
      by (auto intro!: derivative_eq_intros)
  qed

  also have "?this \<longleftrightarrow> (f\<^sup>q has_field_derivative f' * period / (of_real (2 * pi) * \<i> * q)) (at q)"
  proof (intro DERIV_cong_ev)
    have "eventually (\<lambda>w. w \<in> ball q r - {0}) (nhds q)"
      using assms \<open>r > 0\<close> by (intro eventually_nhds_in_open) auto
    thus "\<forall>\<^sub>F x in nhds q. (eval_mero_uhp f \<circ> (\<lambda>q. of_nat period * myln q / (of_real (2 * pi) * \<i>))) x =
                          f\<^sup>q x"
    proof eventually_elim
      case (elim q')
      define z' where "z' = period * myln q' / (2 * complex_of_real pi * \<i>)"
      have "to_q period z' = q'"
        using elim r period_pos by (simp add: z'_def exp_myln to_q_def)
      hence "to_q period (of_q period q') = to_q period z'"
        using elim period_pos by simp
      then obtain n where n: "z' = of_q period q' + of_int n * of_nat period"
        using to_q_eq_to_qE[of period "of_q period q'" z'] period_pos by blast

      have "(f \<circ> (\<lambda>q. of_nat period * myln q / (complex_of_real (2 * pi) * \<i>))) q' = f z'"
        using n by (simp add: z'_def of_q_def)
      also have "\<dots> = f\<^sup>q q'"
        using elim by (simp add: plus_of_int n fourier_nz_eq)
      finally show ?case .
    qed
  qed auto
  finally show ?thesis 
    using has_field_derivative_at_within by blast
qed


definition fourier_poles :: "complex set"
  where "fourier_poles = to_q period ` {z. 0 < Im z \<and> is_pole (eval_mero_uhp f) z}"

lemma zero_not_in_fourier_poles [simp]: "0 \<notin> fourier_poles"
  by (auto simp: fourier_poles_def)
  
lemma is_pole_of_q_iff:
  assumes "q \<in> ball 0 1 - {0}"
  shows   "is_pole f (of_q period q) \<longleftrightarrow> q \<in> fourier_poles"
proof
  assume "is_pole f (of_q period q)"
  thus "q \<in> fourier_poles"
    using assms period_pos unfolding fourier_poles_def 
    by (auto simp: image_def intro!: exI[of _ "of_q period q"] Im_of_q_gt)
next
  assume "q \<in> fourier_poles"
  then obtain z where "Im z > 0" "is_pole f z" "q = to_q period z"
    by (auto simp: fourier_poles_def)
  thus "is_pole f (of_q period q)"
    by (metis to_q_of_q to_q_nonzero fourier_is_pole_to_q_iff period_pos)
qed

lemma to_q_in_fourier_poles_iff [simp]:
  "to_q period z \<in> fourier_poles \<longleftrightarrow> is_pole f z"
proof
  assume "to_q period z \<in> fourier_poles"
  then obtain z' where z': "to_q period z = to_q period z'" "is_pole f z'"
    by (auto simp: fourier_poles_def)
  from z'(1) obtain n where "z = z' + of_int n * of_nat period"
    using period_pos by (metis to_q_eq_to_qE)
  with z'(2) show "is_pole f z"
    by (metis fourier_is_pole_to_q_iff z'(1))
qed (use not_is_pole_eval_mero_uhp_outside[of z f]
     in  \<open>cases "Im z > 0"; auto simp: fourier_poles_def period_pos intro!: imageI\<close>)

lemma not_islimpt_fourier_poles:
  assumes "z \<in> ball 0 1 - {0}"
  shows   "\<not>z islimpt fourier_poles"
proof
  assume "z islimpt fourier_poles"
  then obtain g where g: "\<And>n. g n \<in> fourier_poles - {z}" "g \<longlonglongrightarrow> z"
    unfolding islimpt_sequential by metis
  have [simp]: "g n \<noteq> 0" for n
    using g(1)[of n] by (auto simp: fourier_poles_def)

  from assms have "z \<noteq> 0"
    by auto
  have "open (-{0::complex})"
    by auto
  then obtain r where r: "r > 0" "ball z r \<subseteq> -{0 :: complex}"
    unfolding open_contains_ball using \<open>z \<noteq> 0\<close> by blast
  have "simply_connected (ball z r)"
    by (auto intro!: convex_imp_simply_connected)
  moreover have "(\<lambda>q. q) holomorphic_on ball z r" "\<forall>q\<in>ball z r. q \<noteq> 0"
    using r by (auto intro!: holomorphic_intros)
  ultimately obtain myln :: "complex \<Rightarrow> complex"
    where myln_holo: "myln holomorphic_on ball z r" 
    and "\<And>q'. q' \<in> ball z r \<Longrightarrow> q' = exp (myln q')"
    unfolding simply_connected_eq_holomorphic_log[OF open_ball] by blast
  from this(2) have exp_myln: "exp (myln q') = q'" if "q' \<in> ball z r" for q'
    using that by metis

  define of_q' :: "complex \<Rightarrow> complex"
    where "of_q' = (\<lambda>z. period * myln z / (complex_of_real (2 * pi) * \<i>))"
  have of_q': "to_q period (of_q' w) = w" if "w \<in> ball z r" for w
    using that period_pos by (simp add: to_q_def of_q'_def exp_myln)
  define g' where "g' = (\<lambda>n. of_q' (g n))"      

  have "continuous_on (ball z r) myln"
    by (intro holomorphic_on_imp_continuous_on myln_holo)
  hence cont: "continuous_on (ball z r) of_q'"
    unfolding of_q'_def by (intro continuous_intros) auto

  have "eventually (\<lambda>x. x \<in> ball z r) (nhds z)"
    using r by (intro eventually_nhds_in_open) auto
  hence ev: "eventually (\<lambda>n. g n \<in> ball z r) sequentially"
    by (rule eventually_compose_filterlim [OF _ g(2)])
  hence "g' \<longlonglongrightarrow> of_q' z"
    using r(1) unfolding g'_def by (intro continuous_on_tendsto_compose [OF cont g(2)]) auto

  from ev obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> g n \<in> ball z r"
    by (auto simp: eventually_at_top_linorder)

  have *: "g' n \<in> {z. is_pole f z} - {of_q' z}" if n: "n \<ge> N" for n
  proof -
    have "g n \<in> fourier_poles"
      using g(1)[of n] by auto
    then obtain x where x: "x \<in> {z. is_pole f z}" "g n = to_q period x"
      by (auto simp: fourier_poles_def)
    have *: "to_q period x = to_q period (of_q' (g n))"
      using x N[OF n] by (subst of_q') auto
    obtain m where m: "of_q' (g n) = x + of_int m * of_nat period"
      using to_q_eq_to_qE[OF * period_pos] .
    hence "of_q' (g n) \<in> {z. is_pole f z}"
      by (metis * \<open>g n \<in> fourier_poles\<close> to_q_in_fourier_poles_iff mem_Collect_eq x(2))
    hence "g' n \<in> {z. is_pole f z}"
      by (auto simp: g'_def)
    moreover have "g' n \<noteq> of_q' z"
    proof
      assume "g' n = of_q' z"
      hence "to_q period (g' n) = to_q period (of_q' z)"
        by (simp only: )
      hence "g n = z"
        using N[OF n] \<open>r > 0\<close> by (simp add: of_q' g'_def)
      with g(1)[of n] show False
        by auto
    qed
    ultimately show ?thesis
      by blast
  qed

  define g'' where "g'' = g' \<circ> (\<lambda>n. n + N)"
  have "g'' \<longlonglongrightarrow> of_q' z"
    unfolding g''_def using \<open>g' \<longlonglongrightarrow> _\<close>
    by (rule LIMSEQ_subseq_LIMSEQ) (auto simp: strict_mono_def)
  moreover have "g'' n \<in> {z. is_pole f z} - {of_q' z}" for n
    using *[of "n + N"] by (auto simp: g''_def)
  ultimately have "of_q' z islimpt {z. is_pole f z}"
    unfolding islimpt_sequential by metis
  moreover have "Im (of_q' z) > 0"
  proof -
    have *: "to_q period (of_q period z) = to_q period (of_q' z)"
      using r \<open>z \<noteq> 0\<close> period_pos by (subst of_q') auto
    obtain m where m: "of_q' z = of_q period z + of_int m * of_nat period"
      using to_q_eq_to_qE[OF * period_pos] .
    hence "Im (of_q' z) = Im (of_q period z)"
      by simp
    also from assms have "norm z < 1"
      by simp
    hence "Im (of_q period z) > 0"
      using \<open>z \<noteq> 0\<close> period_pos by (intro Im_of_q_gt) auto
    finally show ?thesis .
  qed
  moreover have "{z. is_pole (eval_mero_uhp f) z} sparse_in \<H>"
    by (intro meromorphic_on_imp_sparse_poles meromorphic_intros) auto
  ultimately show False
    by (subst (asm) sparse_in_open) (auto simp: open_halfspace_Im_gt)
qed

lemma open_Diff_fourier_poles':
  assumes "fourier_poles' \<subseteq> fourier_poles"
  shows   "open (ball 0 1 - {0} - fourier_poles')"
proof - 
  define D where "D = ball (0 :: complex) 1 - {0}"
  have "open (D - closure fourier_poles')"
    by (intro open_Diff) (auto simp: D_def)
  also have "D - closure fourier_poles' = D - fourier_poles'"
  proof safe
    fix x assume x: "x \<in> D" "x \<in> closure fourier_poles'" "x \<notin> fourier_poles'"
    hence "x islimpt fourier_poles'"
      by (subst islimpt_in_closure) auto
    hence "x islimpt fourier_poles"
      by (rule islimpt_subset) fact
    with assms x show False
      using not_islimpt_fourier_poles[of x] by (auto simp: D_def)
  qed (use closure_subset in auto)
  finally show ?thesis 
    by (simp add: D_def)
qed

lemma open_Diff_fourier_poles: "open (ball 0 1 - {0} - fourier_poles)"
  by (rule open_Diff_fourier_poles') auto

lemma analytic_fourier:
  assumes "A \<subseteq> ball 0 1 - fourier_poles - {0}"
  shows "f\<^sup>q analytic_on A"
proof -
  define B where "B = ball 0 1 - fourier_poles"
  have "f\<^sup>q holomorphic_on B - {0}"
    unfolding holomorphic_on_def
  proof
    fix q assume q: "q \<in> B - {0}"
    define z where "z = of_q period q"
    have z: "Im z > 0"
      using q period_pos by (auto simp: B_def z_def intro!: Im_of_q_gt)
    have z_conv_q: "to_q period z = q"
      using q period_pos by (auto simp: B_def z_def)
    have not_pole: "\<not>is_pole (eval_mero_uhp f) z"
    proof
      assume "is_pole (eval_mero_uhp f) z"
      hence "to_q period z \<notin> B"
        using z by (auto simp: B_def)
      with z_conv_q and q show False
        by simp
    qed
    have "\<exists>c. (f\<^sup>q has_field_derivative c) (at q within B - {0})"
      by (rule exI, rule has_field_derivative_fourier[of z]) (use z not_pole z_conv_q in auto)
    thus "f\<^sup>q field_differentiable at q within B - {0}"
      using field_differentiable_def by blast
  qed
  moreover have "open (B - {0})"
    using open_Diff_fourier_poles unfolding B_def by (metis Diff_insert Diff_insert2)
  ultimately have "f\<^sup>q analytic_on B - {0}"
    by (simp add: analytic_on_open)
  thus ?thesis
    by (rule analytic_on_subset) (use assms in \<open>auto simp: B_def\<close>)
qed

lemma fourier_poles_altdef:
  "fourier_poles = {q\<in>ball 0 1-{0}. is_pole f\<^sup>q q}"
proof (intro equalityI subsetI)
  fix q assume q: "q \<in> fourier_poles"
  have "q \<in> ball 0 1 - {0}"
    using q period_pos by (auto simp: fourier_poles_def)
  moreover have "is_pole f\<^sup>q q"
    using q unfolding fourier_poles_def by (auto simp: fourier_is_pole_to_q_iff)
  ultimately show "q \<in> {q\<in>ball 0 1-{0}. is_pole f\<^sup>q q}"
    by auto
next
  fix q assume q: "q \<in> {q\<in>ball 0 1-{0}. is_pole f\<^sup>q q}"
  define z where "z = of_q period q"
  have q_eq: "q = to_q period z"
    using q period_pos by (auto simp: z_def)
  have "Im z > 0"
    using q period_pos by (auto simp: z_def intro!: Im_of_q_gt)
  thus "q \<in> fourier_poles"
    using q by (auto simp: fourier_poles_def q_eq fourier_is_pole_to_q_iff intro!: imageI)
qed

lemma fourier_meromorphic_weak:
  assumes "A \<subseteq> ball 0 1 - {0}"
  shows   "f\<^sup>q meromorphic_on A"
proof (rule meromorphic_on_subset)
  show "f\<^sup>q meromorphic_on (ball 0 1 - {0})"
  proof (rule meromorphic_onI_open[where pts = "fourier_poles"])
    fix q assume "q \<in> fourier_poles"
    thus "not_essential f\<^sup>q q"
      by (auto simp: fourier_poles_altdef)
  next
    fix q :: complex assume q: "q \<in> ball 0 1 - {0}"
    hence "\<not>q islimpt fourier_poles"
      using not_islimpt_fourier_poles[of q] q by blast
    thus "\<not>q islimpt fourier_poles \<inter> (ball 0 1 - {0})"
      using islimpt_subset by blast
  qed (auto intro!: analytic_fourier)
qed (use assms in auto)

lemma tendsto_fourier_to_q:
  assumes "f \<midarrow>z\<rightarrow> c" "q = to_q period z"
  shows   "f\<^sup>q \<midarrow>q\<rightarrow> c"
proof -
  from assms have "q \<noteq> 0"
    by auto
  have "open (-{0::complex})"
    by auto
  then obtain r where r: "r > 0" "ball q r \<subseteq> -{0 :: complex}"
    unfolding open_contains_ball using \<open>q \<noteq> 0\<close> by blast
  have "simply_connected (ball q r)"
    by (auto intro!: convex_imp_simply_connected)
  moreover have "(\<lambda>q. q) holomorphic_on ball q r" "\<forall>q\<in>ball q r. q \<noteq> 0"
    using r by (auto intro!: holomorphic_intros)
  ultimately obtain myln :: "complex \<Rightarrow> complex"
    where myln_holo: "myln holomorphic_on ball q r" 
    and "\<And>q'. q' \<in> ball q r \<Longrightarrow> q' = exp (myln q')"
    unfolding simply_connected_eq_holomorphic_log[OF open_ball] by blast
  from this(2) have exp_myln: "exp (myln q') = q'" if "q' \<in> ball q r" for q'
    using that by metis

  define of_q' :: "complex \<Rightarrow> complex"
    where "of_q' = (\<lambda>z. period * myln z / (complex_of_real (2 * pi) * \<i>))"
  have of_q': "to_q period (of_q' w) = w" if "w \<in> ball q r" for w
    using that by (simp add: to_q_def of_q'_def exp_myln period_pos)

  obtain m where m: "of_q' q = z + of_int m * of_nat period"
  proof -
    have "to_q period z = to_q period (of_q' q)"
      using r(1) by (simp add: of_q' assms)
    from to_q_eq_to_qE[OF this] period_pos and that show ?thesis
      by blast
  qed
  define of_q'' :: "complex \<Rightarrow> complex"
    where "of_q'' = (\<lambda>q. of_q' q - of_int m * of_nat period)"
  have of_q'': "to_q period (of_q'' w) = w" if "w \<in> ball q r" for w
    using that by (auto simp: of_q''_def to_q.minus_of_int of_q')
  have [simp]: "of_q'' (to_q period z) = z"
    using m by (simp add: of_q''_def assms)

  have "continuous_on (ball q r) myln"
    by (intro holomorphic_on_imp_continuous_on myln_holo)
  hence cont: "continuous_on (ball q r) of_q''"
    unfolding of_q''_def of_q'_def by (intro continuous_intros) auto
  moreover have "q \<in> ball q r"
    using r(1) by auto
  ultimately have "isCont of_q'' q"
    by (simp add: continuous_on_eq_continuous_at)
  hence "of_q'' \<midarrow>q\<rightarrow> of_q'' q"
    by (simp add: isCont_def)
  moreover have "\<forall>\<^sub>F x in at q. of_q'' x \<noteq> z"
  proof -
    have "eventually (\<lambda>x. x \<in> ball q r - {q}) (at q)"
      using r(1) by (intro eventually_at_in_open) auto
    thus ?thesis
    proof eventually_elim
      case (elim x)
      hence "to_q period (of_q'' x) \<noteq> to_q period z"
        by (subst of_q'') (auto simp: assms)
      thus ?case
        by blast
    qed
  qed
  ultimately have "filterlim of_q'' (at z) (at q)"
    using assms by (auto simp: filterlim_at)
  hence "(f \<circ> of_q'') \<midarrow>q\<rightarrow> c"
    unfolding o_def by (rule filterlim_compose[OF assms(1)])
  also have "?this \<longleftrightarrow> f\<^sup>q \<midarrow>q\<rightarrow> c"
  proof (intro filterlim_cong refl)
    have "eventually (\<lambda>x. x \<in> ball q r - {q}) (at q)"
      using r(1) by (intro eventually_at_in_open) auto
    moreover have "eventually (\<lambda>x. x \<in> -{0}) (at q)"
      by (intro eventually_at_in_open') (auto simp: assms)
    ultimately show "\<forall>\<^sub>F x in at q. (f \<circ> of_q'') x = f\<^sup>q x"
    proof eventually_elim
      case (elim x)
      have "to_q period (of_q period x) = to_q period (of_q'' x)"
        using elim period_pos by (auto simp: of_q'')
      then obtain m where *: "of_q'' x = of_q period x + of_int m * of_nat period"
        by (elim to_q_eq_to_qE) (use period_pos in auto)
      show ?case using elim Im_of_q_gt[of x]
        by (auto simp: fourier_nz_eq * plus_of_int)
    qed
  qed
  finally show ?thesis .
qed

lemma deriv_fourier:
  assumes "Im z > 0" "\<not>is_pole f z" "q = to_q period z"
  shows   "deriv f\<^sup>q q = eval_mero_uhp (deriv_mero_uhp f) z * of_nat period / (of_real (2 * pi) * \<i> * q)"
  by (rule DERIV_imp_deriv)
     (use has_field_derivative_fourier[OF assms(2,1)]
      in  \<open>auto intro!: derivative_eq_intros simp: assms(3)\<close>)

lemma eval_fourier_outside: 
  assumes "norm q > 1"
  shows   "f\<^sup>q q = 0"
proof (subst fourier_nz_eq)
  show [simp]: "q \<noteq> 0"
    using assms by auto
  show "eval_mero_uhp f (of_q period q) = 0"
    by (subst eval_mero_uhp_outside) (use assms in \<open>auto simp: Im_of_q period_pos\<close>)
qed

lemma not_pole_eval_fourier_outside: "norm q \<ge> 1 \<Longrightarrow> \<not>is_pole f\<^sup>q q"
  by (smt (verit, del_insts) Diff_iff to_q_of_q to_q_in_fourier_poles_iff dist_0_norm 
       fourier_is_pole_to_q_iff fourier_poles_altdef mem_Collect_eq mem_ball norm_zero period_pos)

lemma fourier_expansion_locale_deriv:
  "fourier_expansion_locale period (deriv_mero_uhp f)"
proof
  show "period > 0"
    by (rule period_pos)
next
  have "compose_modgrp_mero_uhp (deriv_mero_uhp f) (shift_modgrp (int period)) =
        deriv_mero_uhp (compose_modgrp_mero_uhp f (shift_modgrp (int period)))"
    by (subst deriv_mero_uhp_compose_modgrp) auto
  also have "compose_modgrp_mero_uhp f (shift_modgrp (int period)) = f"
    by simp
  finally show "compose_modgrp_mero_uhp (deriv_mero_uhp f) (shift_modgrp (int period)) =
                  deriv_mero_uhp f" .
qed

lemma deriv_conv_deriv_fourier_expansion:
  assumes z: "Im z > 0" "\<not>is_pole f z"
  defines "q \<equiv> to_q period z"
  shows   "deriv f z = 2 * \<i> * pi / period * q * deriv f\<^sup>q q"
proof -
  have q: "norm q < 1" "\<not>is_pole f\<^sup>q q"
    using z by (auto simp: q_def period_pos fourier_is_pole_to_q_iff)
  have ana: "f\<^sup>q analytic_on {to_q period z}"
    by (rule analytic_fourier) (use q in \<open>auto simp: fourier_poles_altdef q_def\<close>)
  have "((f\<^sup>q \<circ> (to_q period)) has_field_derivative 
          (deriv f\<^sup>q (to_q period z) * (2 * \<i> * pi / period * to_q period z))) (at z)"
    by (rule derivative_eq_intros DERIV_chain analytic_derivI ana refl period_pos)+ simp_all
  also have "?this \<longleftrightarrow> (f has_field_derivative (2 * \<i> * pi / period * q * deriv f\<^sup>q q)) (at z)"
    by (rule DERIV_cong_ev) (auto simp: q_def)
  finally have "(f has_field_derivative (2 * \<i> * pi / period * q * deriv f\<^sup>q q)) (at z)" .
  thus "deriv f z = 2 * \<i> * pi / period * q * deriv f\<^sup>q q"
    by (rule DERIV_imp_deriv)
qed

end


subsection \<open>Meromorphicity at infinity\<close>


definition has_laurent_expansion_at_ii_inf :: "mero_uhp \<Rightarrow> nat \<Rightarrow> complex fls \<Rightarrow> bool"
  (\<open>(\<open>notation=\<open>infix has_laurent_expansion_at_ii_inf\<close>\<close>(_) has'_laurent'_expansion'_at'_\<i>\<infinity>[(_)] (_))\<close> [60, 0, 60] 60) where
  "f has_laurent_expansion_at_\<i>\<infinity>[period] F \<longleftrightarrow> 
     fourier_expansion_locale period f \<and> fourier_expansion period f has_laurent_expansion F"

definition has_fps_expansion_at_ii_inf :: "mero_uhp \<Rightarrow> nat \<Rightarrow> complex fps \<Rightarrow> bool"
  (\<open>(\<open>notation=\<open>infix has_fps_expansion_at_ii_inf\<close>\<close>(_) has'_fps'_expansion'_at'_\<i>\<infinity>[(_)] (_))\<close> [60, 0, 60] 60) where
  "f has_fps_expansion_at_\<i>\<infinity>[period] F \<longleftrightarrow>
     fourier_expansion_locale period f \<and> fourier_expansion period f has_fps_expansion F"

abbreviation has_laurent_expansion_at_ii_inf_1 :: "mero_uhp \<Rightarrow> complex fls \<Rightarrow> bool"
  (\<open>(\<open>notation=\<open>infix has_laurent_expansion_at_ii_inf_1\<close>\<close>(_) has'_laurent'_expansion'_at'_\<i>\<infinity> (_))\<close> [60, 60] 60) where
  "f has_laurent_expansion_at_\<i>\<infinity> F \<equiv> f has_laurent_expansion_at_\<i>\<infinity>[Suc 0] F"

abbreviation has_fps_expansion_at_ii_inf_1 :: "mero_uhp \<Rightarrow> complex fps \<Rightarrow> bool"
  (\<open>(\<open>notation=\<open>infix has_fps_expansion_at_ii_inf_1\<close>\<close>(_) has'_fps'_expansion'_at'_\<i>\<infinity> (_))\<close> [60, 60] 60) where
  "f has_fps_expansion_at_\<i>\<infinity> F \<equiv> f has_fps_expansion_at_\<i>\<infinity>[Suc 0] F"


locale fourier_expansion_meromorphic = fourier_expansion_locale +
  assumes fourier_meromorphic_at_0: "fourier_expansion period f meromorphic_on {0}"
begin

interpretation ctxt: fourier_expansion_context period
  by standard (rule period_pos)

lemma fourier_meromorphic [meromorphic_intros]:
  assumes "A \<subseteq> ball 0 1"
  shows   "f\<^sup>q meromorphic_on A"
proof (rule meromorphic_on_subset)
  show "f\<^sup>q meromorphic_on (ball 0 1 - {0} \<union> {0})"
    by (intro meromorphic_on_Un fourier_meromorphic_weak fourier_meromorphic_at_0 order.refl)
qed (use assms in auto)

lemma fourier_meromorphic' [meromorphic_intros]:
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> norm (f z) < 1"
  shows   "(\<lambda>z. f\<^sup>q (f z)) meromorphic_on A"
  by (rule meromorphic_on_compose[OF fourier_meromorphic assms(1) order.refl]) (use assms(2) in auto)

lemma fourier_nicely_meromorphic: "f\<^sup>q nicely_meromorphic_on ball 0 1"
  unfolding nicely_meromorphic_on_def
proof (intro ballI conjI)
  fix q :: complex assume q: "q \<in> ball 0 1"
  show "is_pole f\<^sup>q q \<and> f\<^sup>q q = 0 \<or> f\<^sup>q \<midarrow>q\<rightarrow> f\<^sup>q q"
  proof (cases "is_pole f\<^sup>q q")
    case pole: True
    have "f\<^sup>q q = 0"
    proof (cases "q = 0")
      case [simp]: True
      have "is_pole f\<^sup>q 0"
        using pole by simp
      also have "?this \<longleftrightarrow> is_pole (eval_mero_uhp f \<circ> of_q period) 0"
      proof (rule is_pole_cong)
        have "eventually (\<lambda>q. q \<noteq> 0) (at (0::complex))"
          by (rule eventually_neq_at_within)
        thus "eventually (\<lambda>q. f\<^sup>q q = (eval_mero_uhp f \<circ> of_q period) q) (at 0)"
          by eventually_elim (auto simp: fourier_nz_eq)
      qed auto
      finally have "remove_sings (eval_mero_uhp f \<circ> of_q period) 0 = 0"
        by (rule remove_sings_at_pole)
      thus ?thesis
        by (simp add: fourier_expansion_def)
    next
      case False
      hence "q \<in> fourier_poles"
        using q pole by (auto simp: fourier_poles_altdef)
      hence "is_pole f (of_q period q)"
        using q by (subst is_pole_of_q_iff) auto
      hence "f (of_q period q) = 0"
        by (rule eval_mero_uhp_pole)
      thus ?thesis
        using False by (auto simp: fourier_nz_eq)
    qed
    thus ?thesis
      using pole by blast
  next
    case no_pole: False
    have "f\<^sup>q \<midarrow>q\<rightarrow> f\<^sup>q q"
    proof (cases "q = 0")
      case [simp]: True
      have "not_essential f\<^sup>q 0"
        using fourier_meromorphic_at_0 by (simp add: meromorphic_on_not_essential)
      with q no_pole obtain c where "f\<^sup>q \<midarrow>0\<rightarrow> c"
        by (auto simp: not_essential_def)
      thus ?thesis
        using fourier_0_aux[of c] by (simp add: fourier_tendsto_0_iff)
    next
      case False
      define z where "z = of_q period q"
      have q_eq: "q = to_q period z"
        using False q period_pos by (auto simp: z_def)
      show ?thesis
      proof (rule tendsto_fourier_to_q)
        have "\<not>is_pole f z"
          using fourier_is_pole_to_q_iff[of z] q q_eq no_pole by auto
        hence "eval_mero_uhp f \<midarrow>z\<rightarrow> eval_mero_uhp f z"
          unfolding z_def using q False period_pos
          by (intro isContD analytic_at_imp_isCont analytic_intros) (auto intro!: Im_of_q_gt)
        also have "eval_mero_uhp f z = f\<^sup>q q"
          using False q by (simp add: q_eq)
        finally show "eval_mero_uhp f \<midarrow>z\<rightarrow> f\<^sup>q q" .
      qed fact+
    qed
    thus ?thesis ..
  qed
qed (auto intro!: meromorphic_intros)

lemma frequently_fourier_eq0_imp_const:
  assumes "frequently (\<lambda>q. f\<^sup>q q = c) (at q)" "norm q < 1"
  shows   "f = const_mero_uhp c"
proof -
  have "(\<forall>q\<in>ball 0 1. f\<^sup>q q = c) \<or> (\<forall>\<^sub>\<approx>q\<in>ball 0 1. f\<^sup>q q \<noteq> c)"
    by (intro nicely_meromorphic_imp_constant_or_avoid fourier_nicely_meromorphic) auto
  with assms have *: "f\<^sup>q q = c" if "norm q < 1" for q
    using that by (auto simp: eventually_cosparse_open_eq frequently_def)
  have **: "eval_mero_uhp f z = c" if z: "Im z > 0" for z
  proof -
    have "eval_mero_uhp f z = f\<^sup>q (to_q period z)"
      by simp
    also have "\<dots> = c"
      using z by (intro *) (use period_pos in auto)
    finally show ?thesis .
  qed
  have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (cosparse \<H>)"
    by (intro eventually_in_cosparse open_halfspace_Im_gt order.refl)
  hence "eventually (\<lambda>z. eval_mero_uhp f z = eval_mero_uhp (const_mero_uhp c) z) (cosparse \<H>)"
    by eventually_elim (auto simp: **)
  thus ?thesis
    by (rule mero_uhp_eqI)
qed

lemma laurent_expansion_fourier_eq_0_iff:
  assumes "(\<lambda>w. f\<^sup>q (z + w)) has_laurent_expansion F" "norm z < 1"
  shows   "F = 0 \<longleftrightarrow> f = 0"
proof
  assume "f = 0"
  thus "F = 0" using assms
    by (auto dest: zero_has_laurent_expansion_imp_eq_0)
next
  assume [simp]: "F = 0"

  have "eventually (\<lambda>w. f\<^sup>q w = 0) (at z)"
    using assms by (auto simp: has_laurent_expansion_def at_to_0' eventually_filtermap add_ac)
  hence *: "frequently (\<lambda>w. f\<^sup>q w = 0) (at z)"
    by (intro eventually_frequently) auto
  have "f = const_mero_uhp 0"
    using frequently_fourier_eq0_imp_const[OF * \<open>norm z < 1\<close>] by simp
  thus "f = 0"
    by simp
qed

lemma laurent_expansion_fourier_eq_0_iff0:
  assumes "f\<^sup>q has_laurent_expansion F"
  shows   "F = 0 \<longleftrightarrow> f = 0"
  using laurent_expansion_fourier_eq_0_iff[of 0 F] assms by simp

lemma has_laurent_expansion_at_ii_inf_conv_fourier:
  "f has_laurent_expansion_at_\<i>\<infinity>[period] F \<longleftrightarrow> f\<^sup>q has_laurent_expansion F"
  by (simp add: has_laurent_expansion_at_ii_inf_def fourier_expansion_locale_axioms)

lemma has_fps_expansion_at_ii_inf_conv_fourier:
  "f has_fps_expansion_at_\<i>\<infinity>[period] F \<longleftrightarrow> f\<^sup>q has_fps_expansion F"
  by (simp add: has_fps_expansion_at_ii_inf_def fourier_expansion_locale_axioms)

lemma has_laurent_expansion_at_ii_inf:
  "f has_laurent_expansion_at_\<i>\<infinity>[period] laurent_expansion_at_\<i>\<infinity> period f"
  unfolding has_laurent_expansion_at_ii_inf_conv_fourier laurent_expansion_at_ii_inf_def
  using meromorphic_on_imp_has_laurent_expansion[of "f\<^sup>q" "ball 0 1" 0] fourier_meromorphic by simp

lemma zorder_at_ii_inf_conv_fourier:
  assumes "f \<noteq> 0"
  shows   "zorder_at_ii_inf period f = zorder f\<^sup>q 0"
proof (rule zorder_at_ii_inf_eqI)
  define F where "F = laurent_expansion f\<^sup>q 0"
  have "f\<^sup>q meromorphic_on {0}"
    by (intro meromorphic_intros) auto
  hence F: "f\<^sup>q has_laurent_expansion F"
    unfolding F_def by (auto simp: meromorphic_on_def')
  have "F \<noteq> 0"
  proof
    assume "F = 0"
    hence "eventually (\<lambda>q. f\<^sup>q q = 0) (at 0)"
      using F has_laurent_expansion_def by force
    hence "frequently (\<lambda>q. f\<^sup>q q = 0) (at 0)"
      using eventually_frequently trivial_limit_at by blast
    hence "f = const_mero_uhp 0"
      by (intro frequently_fourier_eq0_imp_const) auto
    with assms show False
      by simp
  qed
  define n where "n = zorder f\<^sup>q 0"

  have "(\<lambda>z. f\<^sup>q (to_q period z)) \<in> \<Theta>[at_\<i>\<infinity>](\<lambda>z. to_q period z powi n)"
  proof (rule landau_theta.compose[OF _ filterlim_to_q_at_ii_inf])
    have "f\<^sup>q \<in> \<Theta>[at 0](\<lambda>q. q powi fls_subdegree F)"
      by (rule has_laurent_expansion_imp_bigtheta) fact+
    also have "fls_subdegree F = n"
      unfolding n_def using F \<open>F \<noteq> 0\<close> has_laurent_expansion_zorder_0 by auto
    finally show "f\<^sup>q \<in> \<Theta>[at 0](\<lambda>q. q powi n)" .
  qed (fact period_pos)
  thus "eval_mero_uhp f \<in> \<Theta>[at_\<i>\<infinity>](\<lambda>z. to_q period z powi n)" (is "?P n")
    by simp
qed (fact period_pos)

lemma eventually_neq_at_ii_inf:
  assumes "f \<noteq> const_mero_uhp c"
  shows   "eventually (\<lambda>z. f z \<noteq> c) at_\<i>\<infinity>"
proof (rule ccontr)
  assume "\<not>eventually (\<lambda>z. f z \<noteq> c) at_\<i>\<infinity>"
  hence "\<exists>\<^sub>F x in at_\<i>\<infinity>. eval_mero_uhp f x = c"
    by (simp add: not_eventually)
  hence *: "frequently (\<lambda>q. f\<^sup>q q = c) (at 0)" using period_pos
    by (simp flip: at_ii_inf_filtermap[of period] 
             add: frequently_filtermap not_eventually del: One_nat_def)

  have "(\<forall>q\<in>ball 0 1. f\<^sup>q q = c) \<or> (\<forall>\<^sub>\<approx>q\<in>ball 0 1. f\<^sup>q q \<noteq> c)"
    by (intro nicely_meromorphic_imp_constant_or_avoid fourier_nicely_meromorphic) auto
  thus False
  proof
    assume *: "\<forall>q\<in>ball 0 1. f\<^sup>q q = c"
    have **: "eval_mero_uhp f z = c" if z: "Im z > 0" for z
    proof -
      have "eval_mero_uhp f z = f\<^sup>q (to_q period z)"
        by simp
      also have "to_q period z \<in> ball 0 1"
        using z period_pos by auto
      hence "f\<^sup>q (to_q period z) = c"
        using * by blast
      finally show ?thesis .
    qed
    have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (cosparse \<H>)"
      by (intro eventually_in_cosparse open_halfspace_Im_gt order.refl)
    hence "eventually (\<lambda>z. eval_mero_uhp f z = eval_mero_uhp (const_mero_uhp c) z) (cosparse \<H>)"
      by eventually_elim (use ** in auto)
    hence "f = const_mero_uhp c"
      by (rule mero_uhp_eqI)
    thus False
      using assms by contradiction
  next
    assume "\<forall>\<^sub>\<approx>q\<in>ball 0 1. f\<^sup>q q \<noteq> c"
    hence "eventually (\<lambda>q. f\<^sup>q q \<noteq> c) (at 0)"
      by (auto simp: eventually_cosparse_open_eq)
    with * show False
      by (simp add: frequently_def)
  qed
qed

lemma eventually_neq_fourier:
  assumes "f \<noteq> const_mero_uhp c" "norm q < 1"
  shows   "eventually (\<lambda>q. f\<^sup>q q \<noteq> c) (at q)"
  using assms frequently_fourier_eq0_imp_const unfolding frequently_def by blast

lemma eventually_no_isolated_zero: "eventually (\<lambda>z. \<not>isolated_zero f z) at_\<i>\<infinity>"
proof (cases "f = 0")
  case False
  have "eventually (\<lambda>z. Im z > 0) at_\<i>\<infinity>"
    by (rule eventually_at_ii_inf)
  moreover have "eventually (\<lambda>q. f q \<noteq> 0) at_\<i>\<infinity>"
    using eventually_neq_at_ii_inf[of 0] False by simp
  ultimately show ?thesis
  proof eventually_elim
    case (elim z)
    have "f nicely_meromorphic_on {z}"
      by (rule eval_mero_uhp_nicely_meromorphic) (use elim in auto)
    thus "\<not>isolated_zero f z"
      using elim by (metis zero_isolated_zero_nicely_meromorphic)
  qed
qed auto

lemma eventually_no_poles: "eventually (\<lambda>z. \<not>is_pole f z) at_\<i>\<infinity>"
proof -
  have "\<forall>\<^sub>\<approx>q\<in>ball 0 1. \<not>is_pole (f\<^sup>q) q"
    by (intro meromorphic_on_imp_not_pole_cosparse fourier_meromorphic) auto
  hence "\<forall>\<^sub>F q in at 0. \<not>is_pole (f\<^sup>q) q"
    by (rule eventually_cosparse_imp_eventually_at) auto
  hence "\<forall>\<^sub>F z in at_\<i>\<infinity>. \<not>is_pole (f\<^sup>q) (to_q period z)"
    by (subst (asm) eventually_at_ii_inf_to_q) (rule period_pos)
  thus ?thesis
    by (simp add: fourier_is_pole_to_q_iff)
qed

lemma eval_at_ii_inf_conv_fourier: "eval_mero_uhp_at_ii_inf f = f\<^sup>q 0"
proof (cases "is_pole f\<^sup>q 0")
  case True
  have "fourier_expansion period f 0 = 0"
    using True fourier_nicely_meromorphic by (simp add: is_pole_zero_at_nicely_mero)
  moreover from True have "\<not>(\<exists>L. (f \<longlongrightarrow> L) at_\<i>\<infinity>)"
    using at_ii_inf_neq_bot fourier_is_pole_0_iff not_tendsto_and_filterlim_at_infinity by blast
  ultimately show ?thesis
    unfolding eval_mero_uhp_at_ii_inf_def by auto
next
  case False
  have "f\<^sup>q nicely_meromorphic_on {0}"
    by (rule nicely_meromorphic_on_subset[OF fourier_nicely_meromorphic]) auto
  with False have "isCont f\<^sup>q 0"
    by (auto simp: nicely_meromorphic_on_def isCont_def)
  hence "(f \<longlongrightarrow> f\<^sup>q 0) at_\<i>\<infinity>"
    by (auto simp: isCont_def fourier_tendsto_0_iff)
  thus ?thesis
    by (rule eval_mero_uhp_at_ii_inf_eqI)
qed

lemma is_pole_ii_inf_conv_fourier: "is_pole_ii_inf f \<longleftrightarrow> is_pole f\<^sup>q 0"
  by (simp add: is_pole_def filtermap_fourier_expansion_at_0 is_pole_ii_inf_def filterlim_def)

lemma analytic_fourier' [analytic_intros]:
  assumes "g analytic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1 \<and> \<not>is_pole f\<^sup>q (g z)"
  shows   "(\<lambda>z. f\<^sup>q (g z)) analytic_on A"
proof (rule analytic_on_compose_gen[OF assms(1), unfolded o_def])
  have "f\<^sup>q analytic_on (ball 0 1 - fourier_poles - {0})"
    by (intro analytic_fourier order.refl)
  have "f\<^sup>q analytic_on {0}" if "\<not>is_pole f\<^sup>q 0" 
    using that fourier_nicely_meromorphic nicely_meromorphic_on_imp_analytic_at by auto
  thus "f\<^sup>q analytic_on (ball 0 1 - fourier_poles - {0} \<union> (if is_pole f\<^sup>q 0 then {} else {0}))"
    unfolding analytic_on_Un by (auto intro!: analytic_fourier)
  show "g z \<in> ball 0 1 - fourier_poles - {0} \<union> (if is_pole f\<^sup>q 0 then {} else {0})" if "z \<in> A" for z
    using that assms(2)[of z] by (cases "g z = 0") (auto simp: fourier_poles_altdef)
qed

lemma holomorphic_fourier' [holomorphic_intros]:
  assumes "g holomorphic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1 \<and> \<not>is_pole f\<^sup>q (g z)"
  shows   "(\<lambda>z. f\<^sup>q (g z)) holomorphic_on A"
proof (rule holomorphic_on_compose_gen[OF assms(1), unfolded o_def])
  show "f\<^sup>q holomorphic_on (ball 0 1 - {z. is_pole f\<^sup>q z})"
    by (intro analytic_imp_holomorphic analytic_intros) auto
qed (use assms(2) in auto)

lemma continuous_on_fourier [continuous_intros]:
  assumes "continuous_on A g"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1 \<and> \<not>is_pole f\<^sup>q (g z)"
  shows   "continuous_on A (\<lambda>z. f\<^sup>q (g z))"
  by (rule continuous_on_compose[OF assms(1), unfolded o_def] holomorphic_on_imp_continuous_on holomorphic_intros)+
     (use assms(2) in auto)

lemma continuous_fourier [continuous_intros]:
  assumes "continuous (at z within A) g" assumes "norm (g z) < 1" "\<not>is_pole f\<^sup>q (g z)"
  shows   "continuous (at z within A) (\<lambda>z. f\<^sup>q (g z))"
  by (rule continuous_within_compose[OF assms(1), unfolded o_def]
           continuous_at_imp_continuous_within[OF analytic_at_imp_isCont] analytic_intros)+
     (use assms(2,3) in auto)

lemma tendsto_fourier [tendsto_intros]:
  assumes "(g \<longlongrightarrow> q) F" assumes "norm q < 1" "\<not>is_pole f\<^sup>q q"
  shows   "((\<lambda>z. f\<^sup>q (g z)) \<longlongrightarrow> f\<^sup>q q) F"
  by (rule isCont_tendsto_compose[OF _ assms(1)]) (use assms in \<open>auto intro!: continuous_intros\<close>)

lemma zorder_fourier_neg_iff [simp]:
  assumes "f \<noteq> 0" "norm q < 1"
  shows   "zorder f\<^sup>q q < 0 \<longleftrightarrow> is_pole f\<^sup>q q"
proof (cases "is_pole f\<^sup>q q")
  case True
  thus ?thesis using assms
    by (auto intro!: isolated_pole_imp_neg_zorder meromorphic_on_isolated_singularity meromorphic_intros)
next
  case False
  have "\<exists>\<^sub>F q in at q. f\<^sup>q q \<noteq> 0"
    using assms False by (intro eventually_frequently eventually_neq_fourier) auto
  hence "zorder f\<^sup>q q \<ge> 0"
    using False assms by (intro zorder_ge_0 analytic_intros) auto
  thus ?thesis
    using False by auto
qed

lemma zorder_fourier_nonneg_iff [simp]:
  assumes "f \<noteq> 0" "norm q < 1"
  shows   "zorder f\<^sup>q q \<ge> 0 \<longleftrightarrow> \<not>is_pole f\<^sup>q q"
  using zorder_fourier_neg_iff[OF assms] by linarith

lemma zorder_fourier_pos_iff [simp]:
  assumes "f \<noteq> 0" "norm q < 1"
  shows   "zorder f\<^sup>q q > 0 \<longleftrightarrow> \<not>is_pole f\<^sup>q q \<and> f\<^sup>q q = 0"
proof (cases "is_pole f\<^sup>q q")
  case False
  thus ?thesis
  proof (subst zorder_pos_iff')
    show "\<exists>\<^sub>F q in at q. f\<^sup>q q \<noteq> 0"
      using assms False by (intro eventually_frequently eventually_neq_fourier) auto
  qed (use assms in \<open>auto intro!: analytic_intros\<close>)
next
  case True
  hence "zorder f\<^sup>q q < 0"
    using assms by simp
  with True show ?thesis
    by auto
qed

lemma zorder_fourier_nonpos_iff [simp]:
  assumes "f \<noteq> 0" "norm q < 1"
  shows   "zorder f\<^sup>q q \<le> 0 \<longleftrightarrow> is_pole f\<^sup>q q \<or> f\<^sup>q q \<noteq> 0"
  using zorder_fourier_pos_iff[OF assms] by linarith

lemma zorder_fourier_eq_0_iff [simp]:
  assumes "f \<noteq> 0" "norm q < 1"
  shows   "zorder f\<^sup>q q = 0 \<longleftrightarrow> \<not>is_pole f\<^sup>q q \<and> f\<^sup>q q \<noteq> 0"
  using assms by (metis linorder_neqE_linordered_idom zorder_fourier_neg_iff zorder_fourier_pos_iff)

lemma laurent_expansion_eq_0_iff:
  "laurent_expansion_at_\<i>\<infinity> period f = 0 \<longleftrightarrow> f = 0"
proof -
  define F where "F = laurent_expansion_at_\<i>\<infinity> period f"
  have "f\<^sup>q has_laurent_expansion F"
    using has_laurent_expansion_at_ii_inf
    unfolding F_def has_laurent_expansion_at_ii_inf_def by auto
  thus ?thesis unfolding F_def
    using laurent_expansion_fourier_eq_0_iff0 by blast
qed

lemma zorder_at_ii_inf_conv_subdegree:
  assumes "f \<noteq> 0"
  shows   "zorder_at_ii_inf period f = fls_subdegree (laurent_expansion_at_\<i>\<infinity> period f)"
proof -
  have "zorder_at_ii_inf period f = zorder f\<^sup>q 0"
    using assms by (simp add: zorder_at_ii_inf_conv_fourier)
  also have "\<dots> = fls_subdegree (laurent_expansion_at_\<i>\<infinity> period f)"
    using has_laurent_expansion_at_ii_inf laurent_expansion_eq_0_iff assms
    by (intro has_laurent_expansion_zorder_0) (auto simp: has_laurent_expansion_at_ii_inf_def)
  finally show ?thesis .
qed

text \<open>
  The following are some alternative, equivalent ways of showing that a function is
  holomorphic at infinity.
\<close>
lemma holomorphic_at_infinity_via_fourier_isCont:
  assumes "isCont (fourier_expansion period f) 0"
  shows   "holomorphic_at_infinity f"
proof -
  define f' where "f' = fourier_expansion period f"
  have "f' \<midarrow>0\<rightarrow> f' 0"
    by (rule isContD) (use assms in \<open>auto simp: f'_def\<close>)
  hence "(eval_mero_uhp f \<longlongrightarrow> f' 0) at_\<i>\<infinity>"
    by (simp add: f'_def fourier_tendsto_0_iff)
  thus ?thesis
    unfolding holomorphic_at_infinity_def by blast
qed

lemma holomorphic_at_infinity_via_not_is_pole_ii_inf:
  assumes "\<not>is_pole_ii_inf f"
  shows   "holomorphic_at_infinity f"
proof -
  define f' where "f' = fourier_expansion period f"
  have "f' analytic_on {0}"
  proof (rule nicely_meromorphic_on_imp_analytic_at)
    show "f' nicely_meromorphic_on ball 0 1"
      using fourier_nicely_meromorphic by (simp add: f'_def)
  qed (use assms in \<open>auto simp: f'_def is_pole_ii_inf_conv_fourier\<close>)
  hence "isCont f' 0"
    by (rule analytic_at_imp_isCont)
  thus ?thesis
    by (intro holomorphic_at_infinity_via_fourier_isCont) (simp_all add: f'_def)
qed

lemma holomorphic_at_infinity_via_zorder:
  assumes "zorder_at_ii_inf period f \<ge> 0"
  shows   "holomorphic_at_infinity f"
proof (cases "f = 0")
  case [simp]: False
  define f' where "f' = fourier_expansion period f"

  have "zorder f' 0 = zorder_at_ii_inf period f"
    by (subst zorder_at_ii_inf_conv_fourier) (auto simp: f'_def)
  also have "\<dots> \<ge> 0"
    using assms by simp
  finally have "\<not>is_pole_ii_inf f"
    using zorder_fourier_neg_iff[of 0] by (auto simp: f'_def is_pole_ii_inf_conv_fourier)
  thus ?thesis
    by (intro holomorphic_at_infinity_via_not_is_pole_ii_inf) (simp_all add: f'_def)
qed auto

lemma holomorphic_at_infinity_via_laurent_expansion:
  assumes "f has_laurent_expansion_at_\<i>\<infinity>[period] F" "fls_subdegree F \<ge> 0"
  shows   "holomorphic_at_infinity f"
proof (cases "f = 0")
  case False
  thus ?thesis using assms
    using fourier_tendsto_0_iff has_laurent_expansion_at_ii_inf_def
          has_laurent_expansion_imp_tendsto_0 holomorphic_at_infinity_via_fourier_isCont
          isCont_0_aux by blast
qed auto

lemma holomorphic_at_infinity_via_fps_expansion:
  assumes "f has_fps_expansion_at_\<i>\<infinity>[period] F"
  shows   "holomorphic_at_infinity f"
  using holomorphic_at_infinity_via_laurent_expansion[of "fps_to_fls F"] assms
  by (simp add: fls_subdegree_fls_to_fps_gt0 has_laurent_expansion_fps
                has_fps_expansion_at_ii_inf_conv_fourier
                has_laurent_expansion_at_ii_inf_conv_fourier)

lemma holomorphic_at_infinity_via_bounded_sequence:
  assumes "frequently (\<lambda>z. norm (f z) \<le> c) at_\<i>\<infinity>"
  shows   "holomorphic_at_infinity f"
proof -
  define f' where "f' = fourier_expansion period f"
  from assms have "frequently (\<lambda>z. norm z \<le> c) (filtermap f at_\<i>\<infinity>)"
    by (simp add: frequently_filtermap)
  also have "filtermap f at_\<i>\<infinity> = filtermap f' (at 0)"
    by (simp add: f'_def filtermap_fourier_expansion_at_0)
  finally have bounded_seq: "frequently (\<lambda>z. norm (f' z) \<le> c) (at 0)"
    by (simp add: frequently_filtermap)

  have "\<not>is_pole f' 0"
  proof
    assume "is_pole f' 0"
    hence "eventually (\<lambda>z. norm (f' z) > c) (at 0)"
      unfolding is_pole_def filterlim_at_infinity_iff_eventually_norm_gt by blast
    from bounded_seq and this have "frequently (\<lambda>z. norm (f' z) \<le> c \<and> norm (f' z) > c) (at 0)"
      by (rule frequently_eventually_frequently)
    hence "frequently (\<lambda>z::complex. False) (at 0)"
      by (rule frequently_elim1) auto
    thus False
      by simp
  qed
  thus ?thesis
    by (intro holomorphic_at_infinity_via_not_is_pole_ii_inf)
       (auto simp: f'_def is_pole_ii_inf_conv_fourier)
qed

lemma has_laurent_expansion_deriv:
  assumes "f\<^sup>q has_laurent_expansion F"
  defines "f' \<equiv> fourier_expansion period (deriv_mero_uhp f)"
  defines "c \<equiv> 2 * \<i> * pi / period"
  shows   "f' has_laurent_expansion fls_const c * fls_X * fls_deriv F"
proof -
  interpret deriv: fourier_expansion_locale period "deriv_mero_uhp f"
    by (rule fourier_expansion_locale_deriv)

  have "(\<lambda>q. c * q * deriv f\<^sup>q q) has_laurent_expansion (fls_const c * fls_X * fls_deriv F)"
    by (intro laurent_expansion_intros assms)
  also have "?this \<longleftrightarrow> ?thesis"
  proof (rule has_laurent_expansion_cong)
    have "eventually (\<lambda>q. q \<in> ball 0 1 - {0}) (at 0 :: complex filter)"
      by (rule eventually_at_in_open) auto
    moreover have mero: "f\<^sup>q meromorphic_on {0}"
      by (auto intro!: meromorphic_intros)
    have "eventually (\<lambda>q. \<not>is_pole f\<^sup>q q) (at 0)"
      using meromorphic_on_imp_not_pole_cosparse[OF mero]
      by (auto dest: eventually_cosparse_imp_eventually_at)
    ultimately show "eventually (\<lambda>q. c * q * deriv f\<^sup>q q = f' q) (at 0)"
    proof eventually_elim
      case (elim q)
      define z where "z = of_q period q"
      have q_eq: "q = to_q period z"
        using period_pos elim by (simp add: z_def)
      have z: "Im z > 0" "\<not>is_pole f z"
        using elim period_pos
        by (auto simp: q_eq zero_less_divide_iff zero_less_mult_iff fourier_is_pole_to_q_iff)
      have "c * q * deriv f\<^sup>q q = deriv f z"
        by (subst deriv_conv_deriv_fourier_expansion) 
           (use z period_pos in \<open>auto simp: field_simps q_eq c_def\<close>)
      also have "deriv f z = f' q"
        using elim period_pos z unfolding f'_def
        by (auto simp: z_def eval_deriv_mero_uhp deriv.fourier_nz_eq)
      finally show ?case .
    qed
  qed auto
  finally show ?thesis .
qed

lemma fourier_expansion_meromorphic_deriv:
  "fourier_expansion_meromorphic period (deriv_mero_uhp f)"
proof -
  interpret deriv: fourier_expansion_locale period "deriv_mero_uhp f"
    by (rule fourier_expansion_locale_deriv)
  show ?thesis
  proof
    define f' where "f' = fourier_expansion period (deriv_mero_uhp f)"
    define c where "c = 2 * \<i> * pi / period"
    define F where "F = laurent_expansion_at_\<i>\<infinity> period f"
    have "f' has_laurent_expansion fls_const c * fls_X * fls_deriv F"
      unfolding c_def F_def f'_def
      by (intro has_laurent_expansion_deriv)
         (use has_laurent_expansion_at_ii_inf has_laurent_expansion_at_ii_inf_def in blast)
    thus "f' meromorphic_on {0}"
      by (auto simp: meromorphic_on_def)
  qed
qed

end


locale fourier_expansion_meromorphic_explicit = fourier_expansion_locale +
  fixes fls_fourier :: "complex fls"
  assumes has_laurent_expansion_at_ii_inf_explicit:
    "f has_laurent_expansion_at_\<i>\<infinity>[period] fls_fourier"
begin

sublocale fourier_expansion_meromorphic
proof
  show "fourier_expansion period f meromorphic_on {0}"
    using has_laurent_expansion_at_ii_inf_explicit unfolding has_laurent_expansion_at_ii_inf_def
    by (auto simp: meromorphic_on_def)
qed

lemma fourier_expansion_meromorphic_explicit_mono:
  assumes "period dvd period'" "period' > 0"
  defines "k \<equiv> period' div period"
  shows   "fourier_expansion_meromorphic_explicit period' f (fls_compose_fps fls_fourier (fps_X ^ k))"
proof -
  interpret new: fourier_expansion_locale period' f
    by (rule fourier_expansion_locale_mono) fact+
  have k: "k > 0" and period'_eq: "period' = period * k"
    using assms by (auto simp: k_def)

  show ?thesis
  proof
    have "fourier_expansion period' f has_laurent_expansion fls_compose_fps fls_fourier (fps_X ^ k)"
      using has_laurent_expansion_at_ii_inf_explicit
      unfolding period'_eq has_laurent_expansion_at_ii_inf_def
      by (intro has_laurent_expansion_fourier_mult_period k) auto
    thus "f has_laurent_expansion_at_\<i>\<infinity>[period'] (fls_compose_fps fls_fourier (fps_X ^ k))"
      using new.fourier_expansion_locale_axioms
      unfolding has_laurent_expansion_at_ii_inf_def by auto
  qed
qed

lemma laurent_expansion_eq [simp]: "laurent_expansion_at_\<i>\<infinity> period f = fls_fourier"
  using has_laurent_expansion_at_ii_inf has_laurent_expansion_at_ii_inf_explicit
  unfolding has_laurent_expansion_at_ii_inf_def
  using has_laurent_expansion_unique by blast

lemma fourier_expansion_meromorphic_explicit_deriv:
  defines "F \<equiv> fls_const (2*\<i>*pi/period) * fls_X * fls_deriv fls_fourier"
  shows   "fourier_expansion_meromorphic_explicit period (deriv_mero_uhp f) F"
proof -
  interpret f': fourier_expansion_meromorphic period "deriv_mero_uhp f"
    by (rule fourier_expansion_meromorphic_deriv)
  show ?thesis
  proof
    show "deriv_mero_uhp f has_laurent_expansion_at_\<i>\<infinity>[period] F"
      using has_laurent_expansion_at_ii_inf_explicit
      unfolding F_def has_laurent_expansion_at_ii_inf_def
      by (intro conjI f'.fourier_expansion_locale_axioms has_laurent_expansion_deriv) auto
  qed
qed

end

lemma (in fourier_expansion_meromorphic) fourier_expansion_meromorphic_mono:
  assumes "period' > 0" "period dvd period'"
  shows   "fourier_expansion_meromorphic period' f"
proof -
  define F where "F = laurent_expansion_at_\<i>\<infinity> period f"
  interpret fourier_expansion_meromorphic_explicit period f F
    by unfold_locales (use has_laurent_expansion_at_ii_inf in \<open>simp add: F_def\<close>)
  interpret new: fourier_expansion_meromorphic_explicit period' f 
    "fls_compose_fps F (fps_X ^ (period' div period))"
    by (rule fourier_expansion_meromorphic_explicit_mono) (use assms in auto)
  show ?thesis ..
qed
    


subsection \<open>Holomorphicity at infinity\<close>

locale fourier_expansion_holomorphic = fourier_expansion_locale +
  assumes holo_uhp: "holo_uhp f"
  assumes holomorphic_at_infinity_explicit: "holomorphic_at_infinity f"
begin

interpretation ctxt: fourier_expansion_context period
  by standard (rule period_pos)

lemma fourier_analytic_at_0: "f\<^sup>q analytic_on {0}"
proof -
  from holomorphic_at_infinity_explicit obtain c where lim: "(f \<longlongrightarrow> c) at_\<i>\<infinity>"
    by (auto simp: holomorphic_at_infinity_def)
  define B where "B = norm c + 1"
  have "isCont f\<^sup>q 0"
    using lim by (rule isCont_0_aux)
  hence lim': "(f\<^sup>q \<longlongrightarrow> f\<^sup>q 0) (at 0)"
    by (auto simp: isCont_def intro: Lim_at_imp_Lim_at_within)

  from lim have "eventually (\<lambda>z. f z \<in> ball 0 B) at_\<i>\<infinity>"
    by (rule topological_tendstoD) (auto simp: B_def)
  moreover have "eventually (\<lambda>z. Im z > 0) at_\<i>\<infinity>"
    by (rule eventually_at_ii_inf)
  ultimately obtain y where y: "\<And>z. Im z > y \<Longrightarrow> norm (f z) < B"
    by (auto simp: eventually_at_ii_inf_iff)

  have no_poles_above: "\<not>is_pole f z" if z: "Im z > y" for z
  proof -
    have "eventually (\<lambda>w. w \<in> {w. Im w > y}) (at z)"
      by (rule eventually_at_in_open') (use z in \<open>auto simp: open_halfspace_Im_gt\<close>)
    hence ev: "eventually (\<lambda>w. norm (f w) < B) (at z)"
      by eventually_elim (use y in auto)
    show "\<not>is_pole f z"
    proof
      assume "is_pole f z"
      hence "eventually (\<lambda>z. norm (f z) > B) (at z)"
        unfolding is_pole_def using filterlim_at_infinity_iff_eventually_norm_gt by blast
      hence "eventually (\<lambda>_. False) (at z)"
        using ev by eventually_elim auto
      thus False
        by simp
    qed
  qed

  define r where "r = exp (-y / real period * (2 * pi))"
  have "r > 0"
    by (auto simp: r_def)
  have no_poles_inside: "\<not>is_pole f\<^sup>q q" if q: "norm q < min 1 r" for q
  proof (cases "q = 0")
    case True
    with lim' show ?thesis unfolding is_pole_def
      using at_neq_bot not_tendsto_and_filterlim_at_infinity by blast
  next
    case False
    have "q \<notin> fourier_poles" using q period_pos no_poles_above
      by (auto simp: fourier_poles_def r_def field_simps)
    thus ?thesis using False q
      by (auto simp: fourier_poles_altdef)
  qed

  have "f\<^sup>q holomorphic_on ball 0 (min 1 r)"
  proof (rule no_isolated_singularity')
    show "f\<^sup>q holomorphic_on ball 0 (min 1 r) - {0}"
      using \<open>r > 0\<close> no_poles_inside
      by (intro analytic_imp_holomorphic analytic_fourier) (auto simp: fourier_poles_altdef)
  next
    show "(f\<^sup>q \<longlongrightarrow> f\<^sup>q z) (at z within ball 0 (min 1 r))" if "z \<in> {0}" for z
      using that \<open>isCont f\<^sup>q 0\<close>
      by (auto simp: isCont_def intro: Lim_at_imp_Lim_at_within)
  qed (use \<open>isCont f\<^sup>q 0\<close> \<open>r > 0\<close> in \<open>auto simp: isCont_def\<close>)
  moreover have "0 \<in> ball 0 (min 1 r)" "open (ball 0 (min 1 r) :: complex set)"
    using \<open>r > 0\<close> by auto
  ultimately show ?thesis
    using holomorphic_on_imp_analytic_at by blast
qed

sublocale fourier_expansion_meromorphic
proof
  show "fourier_expansion period f meromorphic_on {0}"
    using fourier_analytic_at_0 by (rule analytic_on_imp_meromorphic_on)
qed

lemma has_fps_expansion_at_ii_inf:
  "f has_fps_expansion_at_\<i>\<infinity>[period] fps_expansion_at_\<i>\<infinity> period f"
  unfolding has_fps_expansion_at_ii_inf_def fps_expansion_at_ii_inf_def
  by (intro conjI fourier_expansion_locale_axioms analytic_at_imp_has_fps_expansion_0 
                  fourier_analytic_at_0)

lemma no_poles [simp]: "\<not>is_pole (eval_mero_uhp f) z"
  using holo_uhp by (auto simp: holo_uhp_def)

lemma tendsto_at_ii_inf: "(f \<longlongrightarrow> eval_mero_uhp_at_ii_inf f) at_\<i>\<infinity>"
  using holomorphic_at_infinity_explicit eval_mero_uhp_at_ii_inf_eqI[of f]
  by (auto simp: holomorphic_at_infinity_def)

lemma no_poles_fourier' [simp]: "fourier_poles = {}"
  by (auto simp: fourier_poles_def)

lemma no_poles_fourier [simp]: "\<not>is_pole (fourier_expansion period f) q"
proof -
  consider "q = 0" | "norm q < 1" "q \<noteq> 0" | "norm q \<ge> 1"
    by linarith
  thus ?thesis
  proof cases
    assume [simp]: "q = 0"
    have "\<not>filterlim (eval_mero_uhp f) at_infinity at_\<i>\<infinity>"
      using tendsto_at_ii_inf at_ii_inf_neq_bot not_tendsto_and_filterlim_at_infinity by blast
    thus ?thesis
      by (auto simp: fourier_is_pole_0_iff)
  next
    assume q: "norm q < 1" "q \<noteq> 0"
    have "is_pole (fourier_expansion period f) q \<longleftrightarrow> q \<in> fourier_poles"
      using q unfolding fourier_poles_altdef by auto
    thus ?thesis
      by auto
  next
    assume q: "norm q \<ge> 1"
    thus ?thesis
      using not_pole_eval_fourier_outside[of q] by auto
  qed
qed

lemma not_is_pole_ii_inf [simp]: "\<not>is_pole_ii_inf f"
  by (simp add: is_pole_ii_inf_conv_fourier)

lemma analytic [analytic_intros]:
  "g analytic_on A \<Longrightarrow> (\<And>z. z \<in> A \<Longrightarrow> Im z > 0) \<Longrightarrow> eval_mero_uhp f analytic_on A"
  by (intro analytic_intros) auto

lemmas [analytic_intros del] = analytic_fourier'
lemmas [holomorphic_intros del] = holomorphic_fourier'

lemma fourier_analytic_full [analytic_intros]:
  assumes "g analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1"
  shows   "(\<lambda>z. fourier_expansion period f (g z)) analytic_on A"
proof (rule analytic_on_compose_gen[OF assms(1), unfolded o_def])
  have "fourier_expansion period f analytic_on ball 0 1 - {0}"
    by (intro analytic_fourier) auto
  moreover have "fourier_expansion period f analytic_on {0}"
    using fourier_nicely_meromorphic nicely_meromorphic_on_imp_analytic_at by auto
  ultimately show "fourier_expansion period f analytic_on (ball 0 1 - {0} \<union> {0})"
    by (subst analytic_on_Un) auto
qed (use assms(2) in auto)

lemma fourier_holomorphic_full [holomorphic_intros]:
  assumes "g holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1"
  shows   "(\<lambda>z. fourier_expansion period f (g z)) holomorphic_on A"
proof (rule holomorphic_on_compose_gen[OF assms(1), unfolded o_def])
  show "fourier_expansion period f holomorphic_on ball 0 1"
    by (intro analytic_imp_holomorphic analytic_intros) auto
qed (use assms in auto)

lemma zorder_at_ii_inf_ge_0 [simp, intro]: "zorder_at_ii_inf period f \<ge> 0"
proof (cases "f = 0")
  case False
  thus ?thesis
    by (auto simp: zorder_at_ii_inf_conv_fourier)
qed auto

end


locale fourier_unop_meromorphic = fourier_expansion_meromorphic +
  fixes g :: "mero_uhp \<Rightarrow> mero_uhp" and g' :: "complex \<Rightarrow> complex" and g'' :: "complex fls \<Rightarrow> complex fls"
  assumes mero_uhp_rel_map [mero_uhp_rel_intros]:
    "mero_uhp_rel (eval_mero_uhp (g f)) (\<lambda>z. g' (eval_mero_uhp f z))"
  assumes compose_modgrp_mero_uhp_map_distrib [simp]:
    "compose_modgrp_mero_uhp (g f) h = g (compose_modgrp_mero_uhp f h)"
  assumes map_laurent_expansion:
    "\<And>f F. f has_laurent_expansion F \<Longrightarrow> (\<lambda>z. g' (f z)) has_laurent_expansion g'' F"
begin

interpretation ctxt: fourier_expansion_context period
  by standard (rule period_pos)

sublocale map: fourier_expansion_locale period "g f"
  by standard (simp_all add: period_pos)

lemma map_fourier_eq_aux:
  assumes q: "q \<in> ball 0 1 - {0}" "\<not>is_pole f\<^sup>q q" "(\<lambda>q. g' (f\<^sup>q q)) analytic_on {q}"
  shows   "fourier_expansion period (g f) q = g' (fourier_expansion period f q)"
proof -
  define z where "z = of_q period q"
  have "(\<lambda>z. g' (f\<^sup>q (to_q period z))) analytic_on {z}" using period_pos q
    by (intro analytic_on_compose_gen[OF _ assms(3), unfolded o_def] analytic_intros)
       (auto simp: z_def)
  hence *: "(\<lambda>z. g' (f z)) analytic_on {z}"
    by simp

  have "fourier_expansion period (g f) q = eval_mero_uhp (g f) z"
    using assms by (auto simp: map.fourier_nz_eq z_def)
  also have "\<dots> = g' (eval_mero_uhp f z)" using period_pos q *
    by (subst mero_uhp_rel_imp_eval_mero_uhp_eq[OF mero_uhp_rel_map])
       (auto intro!: simp: z_def intro!: Im_of_q_gt)
  also have "\<dots> = g' (f\<^sup>q q)"
    using q by (simp add: fourier_nz_eq z_def)
  finally show ?thesis .
qed

lemma meromorphic_map [meromorphic_intros]:
  assumes "A \<subseteq> ball 0 1"
  shows   "(\<lambda>w. g' (f\<^sup>q w)) meromorphic_on A"
  unfolding meromorphic_on_def
proof safe
  fix q assume "q \<in> A"
  hence [simp]: "norm q < 1"
    using assms by auto
  have "(\<lambda>w. g' (f\<^sup>q (q + w))) has_laurent_expansion g'' (laurent_expansion f\<^sup>q q)"
    by (intro map_laurent_expansion meromorphic_on_imp_has_laurent_expansion[of _ "{q}"])
       (auto intro!: meromorphic_intros)
  thus "\<exists>L. (\<lambda>w. g' (f\<^sup>q (q + w))) has_laurent_expansion L" ..
qed

lemma eventually_map_fourier_eq:
  "eventually (\<lambda>q. fourier_expansion period (g f) q = g' (f\<^sup>q q)) (cosparse (ball 0 1))"
  unfolding eventually_cosparse_open_eq[OF open_ball]
proof safe
  fix q :: complex assume q: "q \<in> ball 0 1"
  have "eventually (\<lambda>q. q \<in> ball 0 1) (at q)"
    using q by (intro eventually_at_in_open') auto
  moreover have "eventually (\<lambda>q. q \<noteq> 0) (at q)"
    by (intro eventually_neq_at_within)
  moreover have "eventually (\<lambda>q. \<not>is_pole f\<^sup>q q) (at q)"
  proof -
    have "f\<^sup>q meromorphic_on {q}"
      by (intro meromorphic_intros) (use q in auto)
    thus ?thesis
      by (simp add: eventually_not_pole meromorphic_on_isolated_singularity)
  qed
  moreover have "eventually (\<lambda>q. (\<lambda>q. g' (f\<^sup>q q)) analytic_on {q}) (at q)"
  proof -
    have "(\<lambda>q. g' (f\<^sup>q q)) meromorphic_on {q}"
      by (intro meromorphic_intros) (use q in auto)
    thus ?thesis
      using isolated_singularity_at_altdef meromorphic_on_isolated_singularity by blast
  qed
  ultimately show "eventually (\<lambda>q. fourier_expansion period (g f) q = g' (f\<^sup>q q)) (at q)"
    by eventually_elim (use map_fourier_eq_aux in auto)
qed

sublocale fourier_expansion_meromorphic period "g f"
proof
  have "(\<lambda>q. g' (f\<^sup>q q)) meromorphic_on {0}"
    by (intro meromorphic_intros) auto
  also have "?this \<longleftrightarrow> fourier_expansion period (g f) meromorphic_on {0}"
    by (intro meromorphic_on_cong)
       (use eventually_map_fourier_eq in \<open>simp_all add: eq_commute eventually_cosparse_open_eq\<close>)
  finally show \<dots> .
qed

lemma map_fourier_eq:
  assumes q: "q \<in> ball 0 1" "\<not>is_pole f\<^sup>q q" "(\<lambda>q. g' (f\<^sup>q q)) analytic_on {q}"
  shows   "fourier_expansion period (g f) q = g' (f\<^sup>q q)"
proof (cases "q = 0")
  case True
  have "is_pole (fourier_expansion period (g f)) 0 \<longleftrightarrow> is_pole (\<lambda>q. g' (f\<^sup>q q)) 0"
    using eventually_map_fourier_eq by (intro is_pole_cong) (auto simp: eventually_cosparse_open_eq)
  also have "\<not>is_pole (\<lambda>q. g' (f\<^sup>q q)) 0"
    using q(3) True by (simp add: analytic_at_imp_no_pole)
  finally have "(fourier_expansion period (g f)) \<midarrow>0\<rightarrow> fourier_expansion period (g f) 0"
    unfolding True by (intro isContD analytic_at_imp_isCont analytic_intros) auto
  also have "?this \<longleftrightarrow> (\<lambda>q. g' (f\<^sup>q q)) \<midarrow>0\<rightarrow> fourier_expansion period (g f) 0"
    using eventually_map_fourier_eq by (intro tendsto_cong) (auto simp: eventually_cosparse_open_eq)
  finally have "(\<lambda>q. g' (f\<^sup>q q)) \<midarrow>0\<rightarrow> fourier_expansion period (g f) 0" .
  moreover have "(\<lambda>q. g' (f\<^sup>q q)) \<midarrow>0\<rightarrow> g' (f\<^sup>q 0)"
    by (intro isContD analytic_at_imp_isCont) (use True q(3) in auto)
  ultimately show ?thesis
    using LIM_unique True by blast
qed (use map_fourier_eq_aux q in auto)

lemma map_has_laurent_expansion_at_ii_inf:
  assumes "f\<^sup>q has_laurent_expansion F"
  shows   "(fourier_expansion period (g f)) has_laurent_expansion g'' F"
proof (subst has_laurent_expansion_cong)
  show "eventually (\<lambda>q. fourier_expansion period (g f) q = g' (f\<^sup>q q)) (at 0)"
    using eventually_map_fourier_eq unfolding eventually_cosparse_open_eq[OF open_ball] by auto
  show "(\<lambda>q. g' (f\<^sup>q q)) has_laurent_expansion g'' F"
    by (intro map_laurent_expansion assms)
qed auto

end


locale fourier_expansion_holomorphic_explicit = fourier_expansion_locale +
  fixes fps_fourier :: "complex fps"
  assumes holo_uhp': "holo_uhp f"
  assumes has_laurent_expansion_at_ii_inf_fps_explicit:
    "f has_laurent_expansion_at_\<i>\<infinity>[period] fps_to_fls fps_fourier"
begin

sublocale fourier_expansion_meromorphic_explicit period f "fps_to_fls fps_fourier"
  by unfold_locales (intro has_fps_expansion_fps_to_fls has_laurent_expansion_at_ii_inf_fps_explicit)

sublocale fourier_expansion_holomorphic
proof
  show "holo_uhp f"
    by (fact holo_uhp')
next
  have *: "fourier_expansion period f has_laurent_expansion fps_to_fls fps_fourier"
    using has_laurent_expansion_at_ii_inf_fps_explicit 
    by (simp add: has_laurent_expansion_at_ii_inf_def)
  have "(eval_mero_uhp f \<longlongrightarrow> fps_nth fps_fourier 0) at_\<i>\<infinity>"
    unfolding fourier_tendsto_0_iff [symmetric]
    using has_laurent_expansion_imp_tendsto_0[OF *]
    by (auto simp: tendsto_nhds_iff fls_subdegree_fls_to_fps_gt0)
  thus "holomorphic_at_infinity f"
    unfolding holomorphic_at_infinity_def by blast
qed

lemma has_fps_expansion_at_ii_inf_explicit: "f has_fps_expansion_at_\<i>\<infinity>[period] fps_fourier"
proof -
  have *: "fourier_expansion period f has_laurent_expansion fps_to_fls fps_fourier"
    using has_laurent_expansion_at_ii_inf_fps_explicit 
    by (simp add: has_laurent_expansion_at_ii_inf_def)
  have "(fourier_expansion period f \<longlongrightarrow> fps_nth fps_fourier 0) (at 0)"
    using has_laurent_expansion_imp_tendsto_0[OF *]
    by (auto simp: tendsto_nhds_iff fls_subdegree_fls_to_fps_gt0)
  hence "fourier_expansion period f 0 = fps_nth fps_fourier 0"
    using eval_at_ii_inf_conv_fourier eval_mero_uhp_at_ii_inf_eqI
    by (simp add: fourier_tendsto_0_iff)
  thus ?thesis using * 
    by (auto simp: has_fps_expansion_at_ii_inf_def fourier_expansion_locale_axioms
                   has_fps_expansion_to_laurent)
qed  

lemma fps_expansion_eq [simp]: "fps_expansion_at_\<i>\<infinity> period f = fps_fourier"
  using has_fps_expansion_at_ii_inf has_fps_expansion_at_ii_inf_explicit
  unfolding has_fps_expansion_at_ii_inf_def
  using fps_expansion_unique_complex by blast

lemma eval_mero_uhp_at_ii_inf_eq: "eval_mero_uhp_at_ii_inf f = fps_nth fps_fourier 0"
proof -
  have "fourier_expansion period f has_fps_expansion fps_fourier"
    using has_fps_expansion_at_ii_inf_explicit by (simp add: has_fps_expansion_at_ii_inf_def)
  thus ?thesis
    by (simp add: eval_at_ii_inf_conv_fourier has_fps_expansion_imp_0_eq_fps_nth_0)
qed

end


subsection \<open>Closure properties\<close>

locale fourier_binop_meromorphic = fourier_expansion_context period +
  f: fourier_expansion_meromorphic period f + g: fourier_expansion_meromorphic period g
  for period f g +
  fixes h :: "mero_uhp \<Rightarrow> mero_uhp \<Rightarrow> mero_uhp" and h' :: "complex \<Rightarrow> complex \<Rightarrow> complex" 
    and h'' :: "complex fls \<Rightarrow> complex fls \<Rightarrow> complex fls"
  assumes mero_uhp_rel_map [mero_uhp_rel_intros]:
    "mero_uhp_rel (eval_mero_uhp (h f g)) (\<lambda>z. h' (eval_mero_uhp f z) (eval_mero_uhp g z))"
  assumes compose_modgrp_mero_uhp_map_distrib [simp]:
    "compose_modgrp_mero_uhp (h f g) j = h (compose_modgrp_mero_uhp f j) (compose_modgrp_mero_uhp g j)"
  assumes map_laurent_expansion:
    "\<And>f g F G. f has_laurent_expansion F \<Longrightarrow> g has_laurent_expansion G \<Longrightarrow>
       (\<lambda>z. h' (f z) (g z)) has_laurent_expansion h'' F G"
begin

sublocale map: fourier_expansion_locale period "h f g"
  by standard (simp_all add: period_pos)

lemma map_fourier_eq_aux:
  assumes q: "q \<in> ball 0 1 - {0}" "\<not>is_pole f\<^sup>q q" "\<not>is_pole g\<^sup>q q"
  assumes  "(\<lambda>q. h' (f\<^sup>q q) (g\<^sup>q q)) analytic_on {q}"
  shows   "(fourier_expansion period (h f g)) q = h' (f\<^sup>q q) (g\<^sup>q q)"
proof -
  define z where "z = of_q period q"
  have "(\<lambda>z. h' (f\<^sup>q (to_q period z)) (g\<^sup>q (to_q period z))) analytic_on {z}"
    using period_pos q
    by (intro analytic_on_compose_gen[OF _ assms(4), unfolded o_def] analytic_intros)
       (auto simp: z_def)
  hence *: "(\<lambda>z. h' (f z) (g z)) analytic_on {z}"
    by simp

  have "fourier_expansion period (h f g) q = eval_mero_uhp (h f g) z"
    using assms by (auto simp: map.fourier_nz_eq z_def)
  also have "\<dots> = h' (eval_mero_uhp f z) (eval_mero_uhp g z)" using period_pos q *
    by (subst mero_uhp_rel_imp_eval_mero_uhp_eq[OF mero_uhp_rel_map])
       (auto simp: z_def intro!: Im_of_q_gt)
  also have "\<dots> = h' (f\<^sup>q q) (g\<^sup>q q)"
    using q by (simp add: f.fourier_nz_eq g.fourier_nz_eq z_def)
  finally show ?thesis .
qed

lemma meromorphic_map [meromorphic_intros]:
  assumes "A \<subseteq> ball 0 1"
  shows   "(\<lambda>w. h' (f\<^sup>q w) (g\<^sup>q w)) meromorphic_on A"
  unfolding meromorphic_on_def
proof safe
  fix q assume "q \<in> A"
  hence [simp]: "norm q < 1"
    using assms by auto
  have "(\<lambda>w. h' (f\<^sup>q (q + w)) (g\<^sup>q (q + w))) has_laurent_expansion
          h'' (laurent_expansion f\<^sup>q q) (laurent_expansion g\<^sup>q q)"
    by (intro map_laurent_expansion meromorphic_on_imp_has_laurent_expansion[of _ "{q}"])
       (auto intro!: meromorphic_intros)
  thus "\<exists>L. (\<lambda>w. h' (f\<^sup>q (q + w)) (g\<^sup>q (q + w))) has_laurent_expansion L" ..
qed

lemma eventually_map_fourier_eq:
  "eventually (\<lambda>q. fourier_expansion period (h f g) q = h' (f\<^sup>q q) (g\<^sup>q q)) (cosparse (ball 0 1))"
  unfolding eventually_cosparse_open_eq[OF open_ball]
proof safe
  fix q :: complex assume q: "q \<in> ball 0 1"
  have "eventually (\<lambda>q. q \<in> ball 0 1) (at q)"
    using q by (intro eventually_at_in_open') auto
  moreover have "eventually (\<lambda>q. q \<noteq> 0) (at q)"
    by (intro eventually_neq_at_within)
  moreover have "eventually (\<lambda>q. \<not>is_pole f\<^sup>q q) (at q)"
  proof -
    have "f\<^sup>q meromorphic_on {q}"
      by (intro meromorphic_intros) (use q in auto)
    thus ?thesis
      by (simp add: eventually_not_pole meromorphic_on_isolated_singularity)
  qed
  moreover have "eventually (\<lambda>q. \<not>is_pole g\<^sup>q q) (at q)"
  proof -
    have "g\<^sup>q meromorphic_on {q}"
      by (intro meromorphic_intros) (use q in auto)
    thus ?thesis
      by (simp add: eventually_not_pole meromorphic_on_isolated_singularity)
  qed
  moreover have "eventually (\<lambda>q. (\<lambda>q. h' (f\<^sup>q q) (g\<^sup>q q)) analytic_on {q}) (at q)"
  proof -
    have "(\<lambda>q. h' (f\<^sup>q q) (g\<^sup>q q)) meromorphic_on {q}"
      using q by (auto intro!: meromorphic_intros)
    thus ?thesis
      using isolated_singularity_at_altdef meromorphic_on_isolated_singularity by blast
  qed
  ultimately show "eventually (\<lambda>q. fourier_expansion period (h f g) q = h' (f\<^sup>q q) (g\<^sup>q q)) (at q)"
    by eventually_elim (use map_fourier_eq_aux in auto)
qed

sublocale fourier_expansion_meromorphic period "h f g"
proof
  have "(\<lambda>q. h' (f\<^sup>q q) (g\<^sup>q q)) meromorphic_on {0}"
    by (intro meromorphic_intros) auto
  also have "?this \<longleftrightarrow> fourier_expansion period (h f g) meromorphic_on {0}"
    by (intro meromorphic_on_cong)
       (use eventually_map_fourier_eq in \<open>simp_all add: eq_commute eventually_cosparse_open_eq\<close>)
  finally show \<dots> .
qed

lemma map_fourier_eq:
  assumes q: "q \<in> ball 0 1" "\<not>is_pole f\<^sup>q q" "\<not>is_pole g\<^sup>q q"
  assumes "(\<lambda>q. h' (f\<^sup>q q) (g\<^sup>q q)) analytic_on {q}"
  shows   "fourier_expansion period (h f g) q = h' (f\<^sup>q q) (g\<^sup>q q)"
proof (cases "q = 0")
  case True
  have "is_pole (fourier_expansion period (h f g)) 0 \<longleftrightarrow> is_pole (\<lambda>q. h' (f\<^sup>q q) (g\<^sup>q q)) 0"
    using eventually_map_fourier_eq by (intro is_pole_cong) (auto simp: eventually_cosparse_open_eq)
  also have "\<not>is_pole (\<lambda>q. h' (f\<^sup>q q) (g\<^sup>q q)) 0"
    using assms(4) True by (simp add: analytic_at_imp_no_pole)
  finally have "fourier_expansion period (h f g) \<midarrow>0\<rightarrow> fourier_expansion period (h f g) 0"
    unfolding True by (intro isContD analytic_at_imp_isCont analytic_intros) auto
  also have "?this \<longleftrightarrow> (\<lambda>q. h' (f\<^sup>q q) (g\<^sup>q q)) \<midarrow>0\<rightarrow> fourier_expansion period (h f g) 0"
    using eventually_map_fourier_eq by (intro tendsto_cong) (auto simp: eventually_cosparse_open_eq)
  finally have "(\<lambda>q. h' (f\<^sup>q q) (g\<^sup>q q)) \<midarrow>0\<rightarrow> fourier_expansion period (h f g) 0" .
  moreover have "(\<lambda>q. h' (f\<^sup>q q) (g\<^sup>q q)) \<midarrow>0\<rightarrow> h' (f\<^sup>q 0) (g\<^sup>q 0)"
    by (intro isContD analytic_at_imp_isCont) (use True assms(4) in auto)
  ultimately show ?thesis
    using LIM_unique True by blast
qed (use map_fourier_eq_aux assms in auto)

lemma map_has_laurent_expansion_at_ii_inf:
  assumes "f\<^sup>q has_laurent_expansion F" "g\<^sup>q has_laurent_expansion G"
  shows   "fourier_expansion period (h f g) has_laurent_expansion h'' F G"
proof (subst has_laurent_expansion_cong)
  show "eventually (\<lambda>q. fourier_expansion period (h f g) q = h' (f\<^sup>q q) (g\<^sup>q q)) (at 0)"
    using eventually_map_fourier_eq unfolding eventually_cosparse_open_eq[OF open_ball] by auto
  show "(\<lambda>q. h' (f\<^sup>q q) (g\<^sup>q q)) has_laurent_expansion h'' F G"
    by (intro map_laurent_expansion assms)
qed auto

end
  



context fourier_expansion_context
begin

sublocale const: fourier_expansion_locale period "const_mero_uhp c"
  by standard (auto intro: period_pos)

lemma fourier_const [simp]: 
  assumes "norm q < 1"
  shows   "fourier_expansion period (const_mero_uhp c) q = c"
proof -
  have *: "fourier_expansion period (const_mero_uhp c) q = c" if q: "q \<in> ball 0 1 - {0}" for q
  proof -
    have "Im (of_q period q) > 0"
      using assms q period_pos by (intro Im_of_q_gt) auto
    thus ?thesis using assms period_pos q
      by (auto simp: const.fourier_nz_eq)
  qed
  show ?thesis
  proof (cases "q = 0")
    case True
    have "eventually (\<lambda>q. q \<in> ball 0 1 - {0}) (at 0)"
      by (intro eventually_at_in_open) auto
    hence "eventually (\<lambda>q. fourier_expansion period (const_mero_uhp c) q = c) (at 0)"
      by eventually_elim (simp_all add: *)
    hence "fourier_expansion period (const_mero_uhp c) \<midarrow>0\<rightarrow> c"
      using tendsto_eventually by blast
    thus ?thesis
      using True const.fourier_0_aux const.fourier_tendsto_0_iff by blast
  qed (use *[of q] assms in auto)
qed

lemma not_is_pole_const_fourier [simp]: "\<not>is_pole (fourier_expansion period (const_mero_uhp c)) q"
proof (cases "q \<in> ball 0 1")
  case True
  have "eventually (\<lambda>q::complex. q \<in> ball 0 1) (at q)"
    using True by (intro eventually_at_in_open') auto
  hence "eventually (\<lambda>q. fourier_expansion period (const_mero_uhp c) q = c) (at q)"
    by eventually_elim auto
  hence "is_pole (fourier_expansion period (const_mero_uhp c)) q \<longleftrightarrow> is_pole (\<lambda>_. c) q"
    by (intro is_pole_cong refl) auto
  thus ?thesis by auto
next
  case False
  thus ?thesis
    by (simp add: const.not_pole_eval_fourier_outside)
qed

sublocale const: fourier_expansion_meromorphic period "const_mero_uhp c"
proof
  have "(\<lambda>_. c) holomorphic_on ball 0 1"
    by auto
  also have "?this \<longleftrightarrow> fourier_expansion period (const_mero_uhp c) holomorphic_on ball 0 1"
    by (intro holomorphic_cong) auto
  finally have "fourier_expansion period (const_mero_uhp c) analytic_on {0}"
    by (rule holomorphic_on_imp_analytic_at) auto
  thus "fourier_expansion period (const_mero_uhp c) meromorphic_on {0}"
    by (rule analytic_on_imp_meromorphic_on)
qed

lemma zorder_fourier_0_const [simp]:
  assumes "c \<noteq> 0"
  shows   "zorder (fourier_expansion period (const_mero_uhp c)) 0 = 0"
proof (rule zorder_eq_0I)
  show "fourier_expansion period (const_mero_uhp c) analytic_on {0}"
    by (auto intro!: analytic_intros)
qed (use assms in auto)

lemma const_fourier_has_fps_expansion [fps_expansion_intros]:
  "fourier_expansion period (const_mero_uhp c) has_fps_expansion fps_const c"
proof (subst has_fps_expansion_cong)
  have "eventually (\<lambda>q. q \<in> ball 0 1) (nhds (0 :: complex))"
    by (rule eventually_nhds_in_open) auto
  thus "eventually (\<lambda>q. fourier_expansion period (const_mero_uhp c) q = c) (nhds 0)"
    by eventually_elim auto
  show "(\<lambda>_ :: complex. c) has_fps_expansion fps_const c"
    by (intro fps_expansion_intros)
qed auto

lemma const_fourier_has_laurent_expansion [fps_expansion_intros]:
  "fourier_expansion period (const_mero_uhp c) has_laurent_expansion fls_const c"
proof (subst has_laurent_expansion_cong)
  have "eventually (\<lambda>q. q \<in> ball 0 1) (at (0 :: complex))"
    by (rule eventually_at_in_open') auto
  thus "eventually (\<lambda>q. fourier_expansion period (const_mero_uhp c) q = c) (at 0)"
    by eventually_elim auto
  show "(\<lambda>_ :: complex. c) has_laurent_expansion fls_const c"
    by (intro laurent_expansion_intros)
qed auto

end


lemma zorder_at_ii_inf_const [simp]: "zorder_at_ii_inf n (const_mero_uhp c) = 0"
proof (cases "n > 0")
  case True
  interpret fourier_expansion_context n
    by standard fact
  show ?thesis 
  proof (cases "c = 0")
    case [simp]: False
    show ?thesis
    proof (rule zorder_at_ii_inf_eqI)
      have ev: "eventually (\<lambda>z. Im z > 0) at_ii_inf"
        by (simp add: eventually_at_ii_inf)
      have "eval_mero_uhp (const_mero_uhp c) \<in> \<Theta>[at_\<i>\<infinity>](\<lambda>z. c)"
        by (intro bigthetaI_cong eventually_mono[OF ev]) auto
      also have "(\<lambda>z. c) \<in> \<Theta>[at_\<i>\<infinity>](\<lambda>z. to_q 1 z powi 0)"
        by simp
      finally show "eval_mero_uhp (const_mero_uhp c) \<in> \<Theta>[at_\<i>\<infinity>](\<lambda>x. to_q n x powi 0)"
        by simp
    qed fact
  qed auto
qed (auto simp: zorder_at_ii_inf_def)


context fourier_expansion_locale
begin

lemma fourier_expansion_inverse: "fourier_expansion_locale period (inverse f)"
  and fourier_expansion_uminus: "fourier_expansion_locale period (-f)"
  and fourier_expansion_power: "fourier_expansion_locale period (f ^ n)"
  and fourier_expansion_power_int: "fourier_expansion_locale period (f ^ n)"
  by unfold_locales (auto intro: period_pos simp: hom_distribs)

end


locale fourier_expansion_pair = fourier_expansion_context period +
   f: fourier_expansion_locale period f + g: fourier_expansion_locale period g
   for period f g
begin

lemma fourier_expansion_add: "fourier_expansion_locale period (f + g)"
  and fourier_expansion_diff: "fourier_expansion_locale period (f - g)"
  and fourier_expansion_mult: "fourier_expansion_locale period (f * g)"
  and fourier_expansion_divide: "fourier_expansion_locale period (f / g)"
  by unfold_locales (auto intro: period_pos simp: hom_distribs)

end



context fourier_expansion_meromorphic
begin

interpretation minus: fourier_unop_meromorphic period f "\<lambda>x. -x" "\<lambda>x. -x" "\<lambda>x. -x"
  by standard (mero_uhp_rel, auto intro!: meromorphic_intros laurent_expansion_intros simp: hom_distribs)
lemma fourier_expansion_meromorphic_minus: "fourier_expansion_meromorphic period (-f)" ..
lemmas fourier_minus_eventually_eq = minus.eventually_map_fourier_eq
lemmas has_laurent_expansion_at_ii_inf_minus = minus.map_has_laurent_expansion_at_ii_inf

interpretation ctxt: fourier_expansion_context period
  by standard (rule period_pos)

lemma fourier_minus_eq:
  assumes "q \<in> ball 0 1" "\<not>is_pole f\<^sup>q q"
  shows   "(-f)\<^sup>q q = -f\<^sup>q q"
  by (rule minus.map_fourier_eq[OF assms]) (use assms in \<open>auto intro!: analytic_intros\<close>)

lemma zorder_fourier_minus_eq:
  assumes "q \<in> ball 0 1 - {0}"
  shows   "zorder (-f)\<^sup>q q = zorder f\<^sup>q q"
proof -
  have "zorder (-f)\<^sup>q q = zorder (\<lambda>q. -1 * f\<^sup>q q) q"
    using fourier_minus_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = zorder f\<^sup>q q"
    by (intro zorder_cmult) auto
  finally show ?thesis .
qed



interpretation cmult_left: fourier_unop_meromorphic period f "\<lambda>x. const_mero_uhp c * x" "\<lambda>x. c * x" "\<lambda>x. fls_const c * x"
  by standard (mero_uhp_rel, auto intro!: meromorphic_intros laurent_expansion_intros simp: hom_distribs)
lemma fourier_expansion_meromorphic_cmult_left: "fourier_expansion_meromorphic period (const_mero_uhp c * f)" ..
lemmas fourier_cmult_left_eventually_eq = cmult_left.eventually_map_fourier_eq
lemmas has_laurent_expansion_at_ii_inf_cmult_left = cmult_left.map_has_laurent_expansion_at_ii_inf

lemma fourier_cmult_left_eq:
  assumes "q \<in> ball 0 1" "\<not>is_pole f\<^sup>q q"
  shows   "(const_mero_uhp c * f)\<^sup>q q = c * f\<^sup>q q"
  by (rule cmult_left.map_fourier_eq[OF assms]) (use assms in \<open>auto intro!: analytic_intros\<close>)

lemma zorder_fourier_cmult_left_eq:
  assumes "q \<in> ball 0 1 - {0}" "c \<noteq> 0"
  shows   "zorder (const_mero_uhp c * f)\<^sup>q q = zorder f\<^sup>q q"
proof -
  have "zorder (const_mero_uhp c * f)\<^sup>q q = zorder (\<lambda>q. c * f\<^sup>q q) q"
    using fourier_cmult_left_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = zorder f\<^sup>q q"
    using assms by (intro zorder_cmult) auto
  finally show ?thesis .
qed



interpretation cmult_right: fourier_unop_meromorphic period f "\<lambda>x. x * const_mero_uhp c" "\<lambda>x. x * c" "\<lambda>x. x * fls_const c"
  by standard (mero_uhp_rel, auto intro!: meromorphic_intros laurent_expansion_intros simp: hom_distribs)
lemma fourier_expansion_meromorphic_cmult_right: "fourier_expansion_meromorphic period (const_mero_uhp c * f)" ..
lemmas fourier_cmult_right_eventually_eq = cmult_right.eventually_map_fourier_eq
lemmas has_laurent_expansion_at_ii_inf_cmult_right = cmult_right.map_has_laurent_expansion_at_ii_inf

lemma fourier_cmult_right_eq:
  assumes "q \<in> ball 0 1" "\<not>is_pole f\<^sup>q q"
  shows   "(f * const_mero_uhp c)\<^sup>q q = f\<^sup>q q * c"
  by (rule cmult_right.map_fourier_eq[OF assms]) (use assms in \<open>auto intro!: analytic_intros\<close>)

lemma zorder_fourier_cmult_right_eq:
  assumes "q \<in> ball 0 1 - {0}" "c \<noteq> 0"
  shows   "zorder (f * const_mero_uhp c)\<^sup>q q = zorder f\<^sup>q q"
proof -
  have "zorder (f * const_mero_uhp c)\<^sup>q q = zorder (\<lambda>q. f\<^sup>q q * c) q"
    using fourier_cmult_right_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = zorder f\<^sup>q q"
    by (subst mult.commute, intro zorder_cmult) (use assms in auto)
  finally show ?thesis .
qed


interpretation inverse: fourier_unop_meromorphic period f inverse inverse inverse
  by standard (mero_uhp_rel, auto intro!: meromorphic_intros laurent_expansion_intros simp: hom_distribs)
lemma fourier_expansion_meromorphic_inverse: "fourier_expansion_meromorphic period (inverse f)" ..
lemmas fourier_inverse = inverse.map_fourier_eq
lemmas fourier_inverse_eventually_eq = inverse.eventually_map_fourier_eq
lemmas has_laurent_expansion_at_ii_inf_inverse = inverse.map_has_laurent_expansion_at_ii_inf

lemma fourier_inverse_eq:
  assumes "q \<in> ball 0 1" "\<not>is_pole f\<^sup>q q" "f\<^sup>q q \<noteq> 0"
  shows   "(inverse f)\<^sup>q q = inverse (f\<^sup>q q)"
  by (rule inverse.map_fourier_eq[OF assms(1-2)]) (use assms in \<open>auto intro!: analytic_intros\<close>)

lemma zorder_fourier_inverse_eq:
  assumes "q \<in> ball 0 1" "f \<noteq> 0"
  shows   "zorder (inverse f)\<^sup>q q = -zorder f\<^sup>q q"
proof -
  have "zorder (inverse f)\<^sup>q q = zorder (\<lambda>q. inverse (f\<^sup>q q)) q"
    using fourier_inverse_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = -zorder f\<^sup>q q"
  proof (rule zorder_inverse) 
    show "\<exists>\<^sub>F q in at q. f\<^sup>q q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
  qed (use assms in \<open>auto intro!: meromorphic_on_isolated_singularity 
                       meromorphic_on_not_essential meromorphic_intros\<close>)
  finally show ?thesis .
qed


interpretation power: fourier_unop_meromorphic period f "\<lambda>x. x ^ n" "\<lambda>x. x ^ n" "\<lambda>x. x ^ n"
  by standard (mero_uhp_rel, auto intro!: meromorphic_intros laurent_expansion_intros simp: hom_distribs)
lemma fourier_expansion_meromorphic_power: "fourier_expansion_meromorphic period (f ^ n)" ..
lemmas fourier_power_eventually_eq = power.eventually_map_fourier_eq
lemmas has_laurent_expansion_at_ii_inf_power = power.map_has_laurent_expansion_at_ii_inf

lemma fourier_power_eq:
  assumes "q \<in> ball 0 1" "\<not>is_pole f\<^sup>q q"
  shows   "(f ^ n)\<^sup>q q = f\<^sup>q q ^ n"
  by (rule power.map_fourier_eq[OF assms]) (use assms in \<open>auto intro!: analytic_intros\<close>)


interpretation power_int: fourier_unop_meromorphic period f "\<lambda>x. x powi n" "\<lambda>x. x powi n" "\<lambda>x. x powi n"
  by standard (mero_uhp_rel, auto intro!: meromorphic_intros laurent_expansion_intros simp: hom_distribs)
lemma fourier_expansion_meromorphic_power_int: "fourier_expansion_meromorphic period (f powi n)" ..
lemmas fourier_power_int_eventually_eq = power_int.eventually_map_fourier_eq
lemmas has_laurent_expansion_at_ii_inf_power_int = power_int.map_has_laurent_expansion_at_ii_inf

lemma zorder_fourier_power_int_eq:
  assumes "q \<in> ball 0 1" "f \<noteq> 0"
  shows   "zorder (f powi n)\<^sup>q q = n * zorder f\<^sup>q q"
proof -
  have "zorder (f powi n)\<^sup>q q = zorder (\<lambda>q. f\<^sup>q q powi n) q"
    using fourier_power_int_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = n * zorder f\<^sup>q q"
  proof (rule zorder_power_int) 
    show "\<exists>\<^sub>F q in at q. f\<^sup>q q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
  qed (use assms in \<open>auto intro!: meromorphic_intros\<close>)
  finally show ?thesis .
qed

lemma zorder_fourier_power_eq:
  assumes "q \<in> ball 0 1" "f \<noteq> 0"
  shows   "zorder (f ^ n)\<^sup>q q = n * zorder f\<^sup>q q"
  using zorder_fourier_power_int_eq[OF assms, of "int n"] by simp

end



locale fourier_expansion_meromorphic_pair = fourier_expansion_context period +
   f: fourier_expansion_meromorphic period f + g: fourier_expansion_meromorphic period g
   for period f g
begin

sublocale add: fourier_binop_meromorphic period f g "(+)" "(+)" "(+)"
  by standard (mero_uhp_rel, auto intro!: meromorphic_intros laurent_expansion_intros simp: hom_distribs)
lemma fourier_expansion_meromorphic_add: "fourier_expansion_meromorphic period (f + g)" ..
lemmas fourier_add_eventually_eq = add.eventually_map_fourier_eq
lemmas has_laurent_expansion_at_ii_inf_add = add.map_has_laurent_expansion_at_ii_inf

lemma fourier_add_eq:
  assumes "q \<in> ball 0 1" "\<not>is_pole f\<^sup>q q" "\<not>is_pole g\<^sup>q q"
  shows   "(f + g)\<^sup>q q = f\<^sup>q q + g\<^sup>q q"
  by (rule add.map_fourier_eq[OF assms(1-2)]) (use assms in \<open>auto intro!: analytic_intros\<close>)

lemma zorder_fourier_add_eq1:
  assumes "q \<in> ball 0 1" "f \<noteq> 0" "g \<noteq> 0" "zorder f\<^sup>q q < zorder g\<^sup>q q"
  shows   "zorder (f + g)\<^sup>q q = zorder f\<^sup>q q"
proof -
  have "zorder (f + g)\<^sup>q q = zorder (\<lambda>q. f\<^sup>q q + g\<^sup>q q) q"
    using fourier_add_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = zorder f\<^sup>q q"
  proof (rule zorder_add1) 
    show "\<exists>\<^sub>F q in at q. f\<^sup>q q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently f.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
    show "\<exists>\<^sub>F q in at q. g\<^sup>q q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently g.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
  qed (use assms in \<open>auto intro!: meromorphic_intros\<close>)
  finally show ?thesis .
qed

lemma zorder_fourier_add_eq2:
  assumes "q \<in> ball 0 1" "f \<noteq> 0" "g \<noteq> 0" "zorder f\<^sup>q q > zorder g\<^sup>q q"
  shows   "zorder (f + g)\<^sup>q q = zorder g\<^sup>q q"
proof -
  have "zorder (f + g)\<^sup>q q = zorder (\<lambda>q. f\<^sup>q q + g\<^sup>q q) q"
    using fourier_add_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = zorder g\<^sup>q q"
  proof (rule zorder_add2) 
    show "\<exists>\<^sub>F q in at q. f\<^sup>q q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently f.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
    show "\<exists>\<^sub>F q in at q. g\<^sup>q q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently g.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
  qed (use assms in \<open>auto intro!: meromorphic_intros\<close>)
  finally show ?thesis .
qed


sublocale diff: fourier_binop_meromorphic period f g "(-)" "(-)" "(-)"
  by standard (mero_uhp_rel, auto intro!: meromorphic_intros laurent_expansion_intros simp: hom_distribs)
lemma fourier_expansion_meromorphic_diff: "fourier_expansion_meromorphic period (f - g)" ..
lemmas fourier_diff_eventually_eq = diff.eventually_map_fourier_eq
lemmas has_laurent_expansion_at_ii_inf_diff = diff.map_has_laurent_expansion_at_ii_inf

lemma fourier_diff_eq:
  assumes "q \<in> ball 0 1" "\<not>is_pole f\<^sup>q q" "\<not>is_pole g\<^sup>q q"
  shows   "(f - g)\<^sup>q q = f\<^sup>q q - g\<^sup>q q"
  by (rule diff.map_fourier_eq[OF assms(1-2)]) (use assms in \<open>auto intro!: analytic_intros\<close>)

lemma zorder_fourier_diff_eq1:
  assumes "q \<in> ball 0 1" "f \<noteq> 0" "g \<noteq> 0" "zorder f\<^sup>q q < zorder g\<^sup>q q"
  shows   "zorder (f - g)\<^sup>q q = zorder f\<^sup>q q"
proof -
  have "zorder (f - g)\<^sup>q q = zorder (\<lambda>q. f\<^sup>q q - g\<^sup>q q) q"
    using fourier_diff_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = zorder f\<^sup>q q"
  proof (rule zorder_diff1) 
    show "\<exists>\<^sub>F q in at q. f\<^sup>q q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently f.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
    show "\<exists>\<^sub>F q in at q. g\<^sup>q q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently g.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
  qed (use assms in \<open>auto intro!: meromorphic_intros\<close>)
  finally show ?thesis .
qed

lemma zorder_fourier_diff_eq2:
  assumes "q \<in> ball 0 1" "f \<noteq> 0" "g \<noteq> 0" "zorder f\<^sup>q q > zorder g\<^sup>q q"
  shows   "zorder (f - g)\<^sup>q q = zorder g\<^sup>q q"
proof -
  have "zorder (f - g)\<^sup>q q = zorder (\<lambda>q. f\<^sup>q q - g\<^sup>q q) q"
    using fourier_diff_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = zorder g\<^sup>q q"
  proof (rule zorder_diff2) 
    show "\<exists>\<^sub>F q in at q. f\<^sup>q q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently f.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
    show "\<exists>\<^sub>F q in at q. g\<^sup>q q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently g.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
  qed (use assms in \<open>auto intro!: meromorphic_intros\<close>)
  finally show ?thesis .
qed


sublocale mult: fourier_binop_meromorphic period f g "(*)" "(*)" "(*)"
  by standard (mero_uhp_rel, auto intro!: meromorphic_intros laurent_expansion_intros simp: hom_distribs)
lemma fourier_expansion_meromorphic_mult: "fourier_expansion_meromorphic period (f * g)" ..
lemmas fourier_mult_eventually_eq = mult.eventually_map_fourier_eq
lemmas has_laurent_expansion_at_ii_inf_mult = mult.map_has_laurent_expansion_at_ii_inf

lemma fourier_mult_eq:
  assumes "q \<in> ball 0 1" "\<not>is_pole f\<^sup>q q" "\<not>is_pole g\<^sup>q q"
  shows   "(f * g)\<^sup>q q = f\<^sup>q q * g\<^sup>q q"
  by (rule mult.map_fourier_eq[OF assms(1-2)]) (use assms in \<open>auto intro!: analytic_intros\<close>)

lemma zorder_fourier_mult_eq:
  assumes "q \<in> ball 0 1" "f \<noteq> 0" "g \<noteq> 0"
  shows   "zorder (f * g)\<^sup>q q = zorder f\<^sup>q q + zorder g\<^sup>q q"
proof -
  have "zorder (f * g)\<^sup>q q = zorder (\<lambda>q. f\<^sup>q q * g\<^sup>q q) q"
    using fourier_mult_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = zorder f\<^sup>q q + zorder g\<^sup>q q"
  proof (rule zorder_mult) 
    show "\<exists>\<^sub>F q in at q. f\<^sup>q q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently f.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
    show "\<exists>\<^sub>F q in at q. g\<^sup>q q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently g.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
  qed (use assms in \<open>auto intro!: meromorphic_intros\<close>)
  finally show ?thesis .
qed


sublocale divide: fourier_binop_meromorphic period f g "(/)" "(/)" "(/)"
  by standard (mero_uhp_rel, auto intro!: meromorphic_intros laurent_expansion_intros simp: hom_distribs)
lemma fourier_expansion_meromorphic_divide: "fourier_expansion_meromorphic period (f / g)" ..
lemmas fourier_divide_eventually_eq = divide.eventually_map_fourier_eq
lemmas has_laurent_expansion_at_ii_inf_divide = divide.map_has_laurent_expansion_at_ii_inf

lemma fourier_divide_eq:
  assumes "q \<in> ball 0 1" "\<not>is_pole f\<^sup>q q" "\<not>is_pole g\<^sup>q q" "g\<^sup>q q \<noteq> 0"
  shows   "(f / g)\<^sup>q q = f\<^sup>q q / g\<^sup>q q"
  by (rule divide.map_fourier_eq[OF assms(1-2)]) (use assms in \<open>auto intro!: analytic_intros\<close>) 

lemma zorder_fourier_divide_eq:
  assumes "q \<in> ball 0 1" "f \<noteq> 0" "g \<noteq> 0"
  shows   "zorder (f / g)\<^sup>q q = zorder f\<^sup>q q - zorder g\<^sup>q q"
proof -
  have "zorder (f / g)\<^sup>q q = zorder (\<lambda>q. f\<^sup>q q / g\<^sup>q q) q"
    using fourier_divide_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = zorder f\<^sup>q q - zorder g\<^sup>q q"
  proof (rule zorder_divide)
    show "\<exists>\<^sub>F q in at q. f\<^sup>q q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently f.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
    show "\<exists>\<^sub>F q in at q. g\<^sup>q q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently g.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
  qed (use assms in \<open>auto intro!: meromorphic_intros\<close>)
  finally show ?thesis .
qed

end


lemma compose_modgrp_mero_uhp_compose: 
  "compose_modgrp_mero_uhp (compose_modgrp_mero_uhp f g) h =
     compose_modgrp_mero_uhp f (g * h)"
  by (rule mero_uhp_rel_imp_eq_mero_uhp, mero_uhp_rel,
      rule mero_uhp_relI_weak,subst apply_modgrp_mult) auto

lemma slash_mero_uhp_shift: 
  "slash_mero_uhp k (shift_modgrp n) f = compose_modgrp_mero_uhp f (shift_modgrp n)"
  by (simp add: slash_mero_uhp_def)



lemma holomorphic_at_infinity_via_laurent:
  assumes "f has_laurent_expansion_at_\<i>\<infinity>[period] F" "fls_subdegree F \<ge> 0"
  shows   "holomorphic_at_infinity f"
  using assms unfolding holomorphic_at_infinity_def
  using fourier_expansion_locale.fourier_tendsto_0_iff
    has_laurent_expansion_at_ii_inf_def
    has_laurent_expansion_imp_tendsto_0 by blast

lemma has_laurent_expansion_at_ii_inf_altdef:
  "f has_laurent_expansion_at_\<i>\<infinity>[period] F \<longleftrightarrow> 
     fourier_expansion_meromorphic_explicit period f F"
  unfolding fourier_expansion_meromorphic_explicit_def 
    fourier_expansion_meromorphic_explicit_axioms_def has_laurent_expansion_at_ii_inf_def
  by blast

lemma has_laurent_expansion_at_ii_inf_0_imp_0:
  assumes "f has_laurent_expansion_at_\<i>\<infinity>[period] 0"
  shows   "f = 0"
proof -
  interpret fourier_expansion_meromorphic_explicit period f 0
    using assms unfolding has_laurent_expansion_at_ii_inf_altdef .
  show ?thesis
    using laurent_expansion_eq laurent_expansion_eq_0_iff by blast
qed

lemma has_laurent_expansion_at_ii_inf_unique:
  assumes "f has_laurent_expansion_at_\<i>\<infinity>[period] F"
          "f has_laurent_expansion_at_\<i>\<infinity>[period] G"
  shows   "F = G"
  using assms fourier_expansion_meromorphic_explicit.laurent_expansion_eq
        has_laurent_expansion_at_ii_inf_altdef by blast

lemma has_laurent_expansion_at_ii_inf_mult_period:
  assumes "f has_laurent_expansion_at_\<i>\<infinity>[period] F" "period' = period * k" "k > 0"
  shows   "f has_laurent_expansion_at_\<i>\<infinity>[period'] (fls_compose_fps F (fps_X ^ k))"
proof -
  interpret fourier_expansion_meromorphic_explicit period f F
    using assms(1) unfolding has_laurent_expansion_at_ii_inf_altdef .
  show ?thesis
    using fourier_expansion_meromorphic_explicit_mono[of period'] period_pos assms(3) 
    unfolding assms(2) by (auto simp: has_laurent_expansion_at_ii_inf_altdef)
qed  

lemma has_laurent_expansion_at_ii_inf_at_0:
  assumes "f has_laurent_expansion_at_\<i>\<infinity>[period] F" "fls_subdegree F \<ge> 0"
  shows   "eval_mero_uhp_at_ii_inf f = fls_nth F 0"
proof -
  interpret fourier_expansion_meromorphic_explicit period f F
    using assms(1) unfolding has_laurent_expansion_at_ii_inf_altdef .
  have "fourier_expansion period f \<midarrow>0\<rightarrow> fls_nth F 0"
    by (intro has_laurent_expansion_imp_tendsto_0)
       (use assms in \<open>auto simp: has_laurent_expansion_at_ii_inf_def\<close>)
  thus ?thesis
    by (simp add: eval_at_ii_inf_conv_fourier fourier_0_aux fourier_tendsto_0_iff)
qed

lemma has_laurent_expansion_at_ii_inf_const [laurent_expansion_intros]:
  "period > 0 \<Longrightarrow> const_mero_uhp c has_laurent_expansion_at_\<i>\<infinity>[period] fls_const c"
  by (simp add: fourier_expansion_context.const_fourier_has_laurent_expansion
      fourier_expansion_context.intro fourier_expansion_locale_def
      has_laurent_expansion_at_ii_inf_def)

lemma has_laurent_expansion_at_ii_inf_0 [laurent_expansion_intros]:
  "period > 0 \<Longrightarrow> 0 has_laurent_expansion_at_\<i>\<infinity>[period] 0"
  using has_laurent_expansion_at_ii_inf_const[of period 0] by simp

lemma has_laurent_expansion_at_ii_inf_1 [laurent_expansion_intros]:
  "period > 0 \<Longrightarrow> 1 has_laurent_expansion_at_\<i>\<infinity>[period] 1"
  using has_laurent_expansion_at_ii_inf_const[of period 1] by simp

lemma has_laurent_expansion_at_ii_inf_of_nat [laurent_expansion_intros]:
  "period > 0 \<Longrightarrow> of_nat n has_laurent_expansion_at_\<i>\<infinity>[period] of_nat n"
  using has_laurent_expansion_at_ii_inf_const[of period "of_nat n"] 
  by (simp add: fls_of_nat of_nat_mero_uhp)

lemma has_laurent_expansion_at_ii_inf_of_int [laurent_expansion_intros]:
  "period > 0 \<Longrightarrow> of_int n has_laurent_expansion_at_\<i>\<infinity>[period] of_int n"
  using has_laurent_expansion_at_ii_inf_const[of period "of_int n"] 
  by (simp add: fls_of_int of_int_mero_uhp)

lemma has_laurent_expansion_at_ii_inf_add [laurent_expansion_intros]:
  assumes "f has_laurent_expansion_at_\<i>\<infinity>[period] F"
  assumes "g has_laurent_expansion_at_\<i>\<infinity>[period] G"
  shows   "f + g has_laurent_expansion_at_\<i>\<infinity>[period] F + G"
proof -
  interpret f: fourier_expansion_meromorphic_explicit period f F
    using assms(1) unfolding has_laurent_expansion_at_ii_inf_altdef .
  interpret g: fourier_expansion_meromorphic_explicit period g G
    using assms(2) unfolding has_laurent_expansion_at_ii_inf_altdef .
  interpret pair: fourier_expansion_meromorphic_pair period f g
    by standard (use f.period_pos in auto)
  show ?thesis
    using f.has_laurent_expansion_at_ii_inf
      fourier_binop_meromorphic.map_has_laurent_expansion_at_ii_inf
      g.has_laurent_expansion_at_ii_inf has_laurent_expansion_at_ii_inf_def
      pair.add.fourier_binop_meromorphic_axioms pair.add.has_laurent_expansion_at_ii_inf by auto
qed

lemma has_laurent_expansion_at_ii_inf_mult [laurent_expansion_intros]:
  assumes "f has_laurent_expansion_at_\<i>\<infinity>[period] F"
  assumes "g has_laurent_expansion_at_\<i>\<infinity>[period] G"
  shows   "f * g has_laurent_expansion_at_\<i>\<infinity>[period] F * G"
proof -
  interpret f: fourier_expansion_meromorphic_explicit period f F
    using assms(1) unfolding has_laurent_expansion_at_ii_inf_altdef .
  interpret g: fourier_expansion_meromorphic_explicit period g G
    using assms(2) unfolding has_laurent_expansion_at_ii_inf_altdef .
  interpret pair: fourier_expansion_meromorphic_pair period f g
    by standard (use f.period_pos in auto)
  show ?thesis
    using f.has_laurent_expansion_at_ii_inf
      fourier_binop_meromorphic.map_has_laurent_expansion_at_ii_inf
      g.has_laurent_expansion_at_ii_inf has_laurent_expansion_at_ii_inf_def
      pair.mult.fourier_binop_meromorphic_axioms pair.mult.has_laurent_expansion_at_ii_inf by auto
qed

lemma has_laurent_expansion_at_ii_inf_power_int [laurent_expansion_intros]:
  assumes "f has_laurent_expansion_at_\<i>\<infinity>[period] F"
  shows   "f powi n has_laurent_expansion_at_\<i>\<infinity>[period] F powi n"
proof -
  interpret f: fourier_expansion_meromorphic_explicit period f F
    using assms(1) unfolding has_laurent_expansion_at_ii_inf_altdef .
  show ?thesis
    using f.fourier_expansion_meromorphic_power_int
      f.has_laurent_expansion_at_ii_inf f.has_laurent_expansion_at_ii_inf_power_int f.laurent_expansion_eq
      fourier_expansion_meromorphic.has_laurent_expansion_at_ii_inf_conv_fourier
      has_laurent_expansion_at_ii_inf_def by blast
qed

lemma has_laurent_expansion_at_ii_inf_power [laurent_expansion_intros]:
  assumes "f has_laurent_expansion_at_\<i>\<infinity>[period] F"
  shows   "f ^ n has_laurent_expansion_at_\<i>\<infinity>[period] F ^ n"
  using has_laurent_expansion_at_ii_inf_power_int[OF assms, of "int n"] by simp

lemma has_laurent_expansion_at_ii_inf_inverse [laurent_expansion_intros]:
  assumes "f has_laurent_expansion_at_\<i>\<infinity>[period] F"
  shows   "inverse f has_laurent_expansion_at_\<i>\<infinity>[period] inverse F"
  using has_laurent_expansion_at_ii_inf_power_int[OF assms, of "-1"] by simp

lemma has_laurent_expansion_at_ii_inf_divide [laurent_expansion_intros]:
  assumes "f has_laurent_expansion_at_\<i>\<infinity>[period] F"
  assumes "g has_laurent_expansion_at_\<i>\<infinity>[period] G"
  shows   "f / g has_laurent_expansion_at_\<i>\<infinity>[period] F / G"
  using has_laurent_expansion_at_ii_inf_mult[OF assms(1) 
          has_laurent_expansion_at_ii_inf_inverse[OF assms(2)]]
  by (simp add: field_simps)

lemma has_laurent_expansion_at_ii_inf_minus [laurent_expansion_intros]:
  assumes "f has_laurent_expansion_at_\<i>\<infinity>[period] F"
  shows   "-f has_laurent_expansion_at_\<i>\<infinity>[period] (-F)"
proof -
  interpret f: fourier_expansion_meromorphic_explicit period f F
    using assms(1) unfolding has_laurent_expansion_at_ii_inf_altdef .
  show ?thesis
    using has_laurent_expansion_at_ii_inf_mult[OF 
            assms has_laurent_expansion_at_ii_inf_const[of _ "-1"]] f.period_pos
    by (simp add: hom_distribs)
qed

lemma has_laurent_expansion_at_ii_inf_diff [laurent_expansion_intros]:
  assumes "f has_laurent_expansion_at_\<i>\<infinity>[period] F"
  assumes "g has_laurent_expansion_at_\<i>\<infinity>[period] G"
  shows   "f - g has_laurent_expansion_at_\<i>\<infinity>[period] F - G"
  using has_laurent_expansion_at_ii_inf_add[OF assms(1) 
          has_laurent_expansion_at_ii_inf_minus[OF assms(2)]]
  by simp

lemma has_laurent_expansion_at_ii_inf_deriv [laurent_expansion_intros]:
  assumes "f has_laurent_expansion_at_\<i>\<infinity>[period] F"
  defines "F' \<equiv> fls_const (2*\<i>*pi/period) * fls_X * fls_deriv F"
  shows   "deriv_mero_uhp f has_laurent_expansion_at_\<i>\<infinity>[period] F'"
proof -
  interpret f: fourier_expansion_meromorphic_explicit period f F
    using assms(1) unfolding has_laurent_expansion_at_ii_inf_altdef .
  interpret f': fourier_expansion_meromorphic_explicit period "deriv_mero_uhp f" F'
    unfolding F'_def by (rule f.fourier_expansion_meromorphic_explicit_deriv)
  show ?thesis
    by (rule f'.has_laurent_expansion_at_ii_inf_explicit)
qed

lemma has_laurent_expansion_at_ii_inf_poly [laurent_expansion_intros]:
  assumes "f has_laurent_expansion_at_\<i>\<infinity>[period] F"
  assumes "period > 0"
  shows   "poly (map_poly const_mero_uhp P) f has_laurent_expansion_at_\<i>\<infinity>[period]
             poly (map_poly fls_const P) F"
  using assms by (induction P) (auto intro!: laurent_expansion_intros simp: map_poly_pCons)

lemma has_laurent_expansion_at_ii_inf_poly2 [laurent_expansion_intros]:
  assumes "f has_laurent_expansion_at_\<i>\<infinity>[period] F" "g has_laurent_expansion_at_\<i>\<infinity>[period] G"
  assumes "period > 0"
  shows   "poly2 (map_poly2 const_mero_uhp P) f g has_laurent_expansion_at_\<i>\<infinity>[period]
             poly2 (map_poly2 fls_const P) F G"
  using assms by (induction P) (auto intro!: laurent_expansion_intros)


lemma has_fps_expansion_at_ii_inf_conv_laurent:
  "f has_fps_expansion_at_\<i>\<infinity>[period] F \<longleftrightarrow> f has_laurent_expansion_at_\<i>\<infinity>[period] fps_to_fls F"
proof
  assume "f has_fps_expansion_at_\<i>\<infinity>[period] F"
  thus "f has_laurent_expansion_at_\<i>\<infinity>[period] fps_to_fls F"
    by (simp add: has_fps_expansion_at_ii_inf_def has_fps_expansion_to_laurent
        has_laurent_expansion_at_ii_inf_def)
next
  assume *: "f has_laurent_expansion_at_\<i>\<infinity>[period] fps_to_fls F"
  then interpret fourier_expansion_meromorphic_explicit period f "fps_to_fls F"
    unfolding has_laurent_expansion_at_ii_inf_altdef .
  have "fourier_expansion period f \<midarrow>0\<rightarrow> fls_nth (fps_to_fls F) 0" using * 
    by (intro has_laurent_expansion_imp_tendsto_0)
       (auto simp: has_laurent_expansion_at_ii_inf_def fls_subdegree_fls_to_fps_gt0)
  hence "fourier_expansion period f 0 = fps_nth F 0"
    using eval_at_ii_inf_conv_fourier eval_mero_uhp_at_ii_inf_eqI fourier_tendsto_0_iff by simp
  thus "f has_fps_expansion_at_\<i>\<infinity>[period] F"
    using * has_fps_expansion_to_laurent[of "fourier_expansion period f" F]
    by (simp add: has_fps_expansion_at_ii_inf_def fourier_expansion_locale_axioms
                  has_laurent_expansion_at_ii_inf_def) 
qed

lemma holomorphic_at_infinity_via_fps:
  assumes "f has_fps_expansion_at_\<i>\<infinity>[period] F"
  shows   "holomorphic_at_infinity f"
  using assms
  by (meson fls_subdegree_fls_to_fps_gt0 fourier_expansion_locale.fourier_tendsto_0_iff
        has_fps_expansion_at_ii_inf_conv_laurent has_laurent_expansion_at_ii_inf_def
        has_laurent_expansion_imp_tendsto_0 holomorphic_at_infinity_def)

lemma has_fps_expansion_at_ii_inf_imp_laurent:
  "f has_fps_expansion_at_\<i>\<infinity>[period] F \<Longrightarrow> f has_laurent_expansion_at_\<i>\<infinity>[period] fps_to_fls F"
  using has_fps_expansion_at_ii_inf_conv_laurent by blast

lemma has_fps_expansion_at_ii_inf_mult_period:
  assumes "f has_fps_expansion_at_\<i>\<infinity>[period] F" "period' = period * k" "k > 0"
  shows   "f has_fps_expansion_at_\<i>\<infinity>[period'] (fps_compose F (fps_X ^ k))"
proof -
  have "f has_laurent_expansion_at_\<i>\<infinity>[period] fps_to_fls F"
    using assms(1) by (rule has_fps_expansion_at_ii_inf_imp_laurent)
  hence "f has_laurent_expansion_at_\<i>\<infinity>[period'] fls_compose_fps (fps_to_fls F) (fps_X ^ k)"
    by (rule has_laurent_expansion_at_ii_inf_mult_period) fact+
  also have "fls_compose_fps (fps_to_fls F) (fps_X ^ k) = fps_to_fls (fps_compose F (fps_X ^ k))"
    by (rule fls_compose_fps_to_fls) (use \<open>k > 0\<close> in auto)
  finally show ?thesis
    by (simp add: has_fps_expansion_at_ii_inf_conv_laurent)
qed

lemma has_fps_expansion_at_ii_inf_0_imp_0:
  assumes "f has_fps_expansion_at_\<i>\<infinity>[period] 0"
  shows   "f = 0"
  using assms
  by (metis fps_zero_to_fls has_fps_expansion_at_ii_inf_imp_laurent 
            has_laurent_expansion_at_ii_inf_0_imp_0)

lemma has_fps_expansion_at_ii_inf_unique:
  assumes "f has_fps_expansion_at_\<i>\<infinity>[period] F"
          "f has_fps_expansion_at_\<i>\<infinity>[period] G"
  shows   "F = G"
  using assms fps_expansion_unique_complex has_fps_expansion_at_ii_inf_def by auto

lemma has_fps_expansion_at_ii_inf_at_0:
  assumes "f has_fps_expansion_at_\<i>\<infinity>[period] F"
  shows   "eval_mero_uhp_at_ii_inf f = fps_nth F 0"
  using has_laurent_expansion_at_ii_inf_at_0[OF has_fps_expansion_at_ii_inf_imp_laurent[OF assms]]
  by (simp add: fls_subdegree_fls_to_fps_gt0)

lemma has_fps_expansion_at_ii_inf_const [fps_expansion_intros]:
  "period > 0 \<Longrightarrow> const_mero_uhp c has_fps_expansion_at_\<i>\<infinity>[period] fps_const c"
  unfolding has_fps_expansion_at_ii_inf_conv_laurent fps_const_to_fls
  by (intro laurent_expansion_intros)

lemma has_fps_expansion_at_ii_inf_0 [fps_expansion_intros]:
  "period > 0 \<Longrightarrow> 0 has_fps_expansion_at_\<i>\<infinity>[period] 0"
  using has_fps_expansion_at_ii_inf_const[of period 0] by simp

lemma has_fps_expansion_at_ii_inf_1 [fps_expansion_intros]:
  "period > 0 \<Longrightarrow> 1 has_fps_expansion_at_\<i>\<infinity>[period] 1"
  using has_fps_expansion_at_ii_inf_const[of period 1] by simp

lemma has_fps_expansion_at_ii_inf_of_nat [fps_expansion_intros]:
  "period > 0 \<Longrightarrow> of_nat n has_fps_expansion_at_\<i>\<infinity>[period] of_nat n"
  using has_fps_expansion_at_ii_inf_const[of period "of_nat n"] 
  by (simp add: fps_of_nat of_nat_mero_uhp)

lemma has_fps_expansion_at_ii_inf_of_int [fps_expansion_intros]:
  "period > 0 \<Longrightarrow> of_int n has_fps_expansion_at_\<i>\<infinity>[period] of_int n"
  using has_fps_expansion_at_ii_inf_const[of period "of_int n"] 
  by (simp add: fps_of_int of_int_mero_uhp)

lemma has_fps_expansion_at_ii_inf_add [fps_expansion_intros]:
  assumes "f has_fps_expansion_at_\<i>\<infinity>[period] F"
  assumes "g has_fps_expansion_at_\<i>\<infinity>[period] G"
  shows   "f + g has_fps_expansion_at_\<i>\<infinity>[period] F + G"
  using assms unfolding has_fps_expansion_at_ii_inf_conv_laurent hom_distribs
  by (intro laurent_expansion_intros)

lemma has_fps_expansion_at_ii_inf_mult [fps_expansion_intros]:
  assumes "f has_fps_expansion_at_\<i>\<infinity>[period] F"
  assumes "g has_fps_expansion_at_\<i>\<infinity>[period] G"
  shows   "f * g has_fps_expansion_at_\<i>\<infinity>[period] F * G"
  using assms unfolding has_fps_expansion_at_ii_inf_conv_laurent hom_distribs
  by (intro laurent_expansion_intros)

lemma has_fps_expansion_at_ii_inf_power [fps_expansion_intros]:
  assumes "f has_fps_expansion_at_\<i>\<infinity>[period] F"
  shows   "f ^ n has_fps_expansion_at_\<i>\<infinity>[period] F ^ n"
  using assms unfolding has_fps_expansion_at_ii_inf_conv_laurent hom_distribs
  by (intro laurent_expansion_intros)

lemma has_fps_expansion_at_ii_inf_minus [fps_expansion_intros]:
  assumes "f has_fps_expansion_at_\<i>\<infinity>[period] F"
  shows   "-f has_fps_expansion_at_\<i>\<infinity>[period] (-F)"
  using assms unfolding has_fps_expansion_at_ii_inf_conv_laurent hom_distribs
  by (intro laurent_expansion_intros)

lemma has_fps_expansion_at_ii_inf_diff [fps_expansion_intros]:
  assumes "f has_fps_expansion_at_\<i>\<infinity>[period] F"
  assumes "g has_fps_expansion_at_\<i>\<infinity>[period] G"
  shows   "f - g has_fps_expansion_at_\<i>\<infinity>[period] F - G"
  using assms unfolding has_fps_expansion_at_ii_inf_conv_laurent hom_distribs
  by (intro laurent_expansion_intros)

lemma has_fps_expansion_at_ii_inf_deriv [fps_expansion_intros]:
  assumes "f has_fps_expansion_at_\<i>\<infinity>[period] F"
  defines "F' \<equiv> fps_const (2*\<i>*pi/period) * fps_X * fps_deriv F"
  shows   "deriv_mero_uhp f has_fps_expansion_at_\<i>\<infinity>[period] F'"
proof -
  have "deriv_mero_uhp f has_laurent_expansion_at_\<i>\<infinity>[period] fps_to_fls F'"
    using has_laurent_expansion_at_ii_inf_deriv[of f period "fps_to_fls F"]
    using assms(1) unfolding has_fps_expansion_at_ii_inf_conv_laurent
    by (simp add: F'_def hom_distribs fls_deriv_fps_to_fls)
  thus ?thesis
    by (simp add: has_fps_expansion_at_ii_inf_conv_laurent)
qed

lemma has_fps_expansion_at_ii_inf_deriv_1 [fps_expansion_intros]:
  assumes "f has_fps_expansion_at_\<i>\<infinity> F"
  defines "F' \<equiv> fps_const (2*\<i>*pi) * fps_X * fps_deriv F"
  shows   "deriv_mero_uhp f has_fps_expansion_at_\<i>\<infinity> F'"
  using has_fps_expansion_at_ii_inf_deriv[OF assms(1)] by (simp add: assms(2))

lemma has_fps_expansion_at_ii_inf_sum [fps_expansion_intros]:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x has_fps_expansion_at_\<i>\<infinity>[period] F x"
  assumes "period > 0"
  shows   "(\<Sum>x\<in>A. f x) has_fps_expansion_at_\<i>\<infinity>[period] (\<Sum>x\<in>A. F x)"
  using assms by (induction A rule: infinite_finite_induct) (auto intro!: fps_expansion_intros)

lemma has_fps_expansion_at_ii_inf_poly [fps_expansion_intros]:
  assumes "f has_fps_expansion_at_\<i>\<infinity>[period] F"
  assumes "period > 0"
  shows   "poly (map_poly const_mero_uhp P) f has_fps_expansion_at_\<i>\<infinity>[period]
             poly (map_poly fps_const P) F"
  using assms by (induction P) (auto intro!: fps_expansion_intros simp: map_poly_pCons)

lemma has_fps_expansion_at_ii_inf_poly2 [fps_expansion_intros]:
  assumes "f has_fps_expansion_at_\<i>\<infinity>[period] F" "g has_fps_expansion_at_\<i>\<infinity>[period] G"
  assumes "period > 0"
  shows   "poly2 (map_poly2 const_mero_uhp P) f g has_fps_expansion_at_\<i>\<infinity>[period]
             poly2 (map_poly2 fps_const P) F G"
  using assms by (induction P) (auto intro!: fps_expansion_intros)

lemma zero_has_fps_expansion_at_ii_inf_iff:
  "0 has_fps_expansion_at_\<i>\<infinity>[period] F \<longleftrightarrow> F = 0 \<and> period > 0"
proof safe
  assume *: "0 has_fps_expansion_at_\<i>\<infinity>[period] F"
  then interpret fourier_expansion_meromorphic_explicit period 0 "fps_to_fls F"
    by (simp add: has_fps_expansion_at_ii_inf_conv_laurent has_laurent_expansion_at_ii_inf_altdef)
  show "period > 0"
    by (rule period_pos)
  have "0 has_laurent_expansion_at_\<i>\<infinity>[period] fps_to_fls F"
    using * has_laurent_expansion_at_ii_inf_explicit by force
  moreover have "0 has_laurent_expansion_at_\<i>\<infinity>[period] 0"
    by (rule laurent_expansion_intros) (rule period_pos)
  ultimately show "F = 0"
    unfolding has_laurent_expansion_at_ii_inf_def using has_laurent_expansion_unique by blast
qed (auto intro: fps_expansion_intros)

(* TODO: sum etc. *)
(* TODO: inverse, divide, etc. *)

(* TODO: cleanup? *)

end
