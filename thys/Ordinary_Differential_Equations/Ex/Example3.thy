theory Example3
imports
  "~~/src/HOL/Decision_Procs/Approximation"
  "../IVP/Upper_Lower_Solution"
  Example_Utilities
begin

subsection \<open>Example 3\<close>

abbreviation "e3_real \<equiv> \<lambda>(t, x). (1::real, x*x + t*t::real)"
approximate_affine e3 e3_real
print_theorems
definition "e3_euclarith \<equiv> \<lambda>n.
  (AddE (ScaleR
                (realarith.Add
                  (realarith.Mult (realarith.Var n (real_of_float 0, real_of_float 1))
                    (realarith.Var n (real_of_float 0, real_of_float 1)))
                  (realarith.Mult (realarith.Var n (real_of_float 1, real_of_float 0))
                    (realarith.Var n (real_of_float 1, real_of_float 0))))
                (real_of_float 0, real_of_float 1))
          (ScaleR (realarith.Num (real_of_float 1)) (real_of_float 1, real_of_float 0)))"

setup Locale_Code.open_block
interpretation e3: aform_approximate_ivp e3_real "\<lambda>_. True" e3_euclarith true_euclarithform
  by unfold_locales
    (auto simp add: e3_euclarith_def plusE_def numeral_eq_Suc
      intro!: ext eq_reflection)
setup Locale_Code.close_block

definition "e3_optns = default_optns
    \<lparr> precision := 30,
      tolerance := FloatR 1 (- 4),
      stepsize  := FloatR 1 (- 8),
      printing_fun := (\<lambda>_ _. ())\<rparr>"

definition "solve_e3 = e3.one_step_until_time_ivl_listres (e3_optns)"
schematic_goal solve_ivl_e3:
  "solve_e3 (aform_of_point (0, 1)) True (FloatR 32 (- 8)) = ?X"
  by guess_rhs eval
concrete_definition e3_result uses solve_ivl_e3 is "_ = dRETURN ?X"
definition "e3_reach = map aform_of_list_aform (the (snd (e3_result)))"

lemma e3_flow_mem:
  "0.125 \<in> e3.existence_ivl0 (0, 1) \<and>
    e3.flow0 (0, 1) 0.125 \<in> {0.125} \<times> {1.143552 .. 1.143564} \<and>
    (\<forall>s \<in> {0 .. 0.125}. e3.flow0 (0, 1) s \<in> \<Union>(Affine ` set e3_reach))"
  apply (rule e3.one_step_until_time_ivl_listres_reachable[OF e3_result.refine[unfolded solve_e3_def]])
  apply (auto simp: powr_neg_numeral e3_reach_def)
  apply (auto simp: e3_result_def)
  done

subsubsection \<open>Bounds analytically obtained by Walter~\cite{walter} in section 9, Example V.\<close>

experiment begin

text \<open>Example V in Walter's textbook\<close>

lemma cos_neq_zeroI:
  assumes "-pi / 2 < x" "x < pi / 2"
  shows "cos x \<noteq> 0"
  using assms div2_less_self
  by (fastforce simp: cos_zero_iff)

lemma quadratic_real_max_eq:
  fixes a b c x::real
  defines "xm \<equiv> -b / (2 * a)"
  shows "a < 0 \<Longrightarrow> a * x\<^sup>2 + b * x + c \<le> a * xm\<^sup>2 + b * xm + c"
  unfolding xm_def
  by (sos "(((((A<0 * (A<1 * A<2)) * R<1) + ((A<2 * R<1) * (R<1 * [a^2]^2)))) &
    ((((A<0 * (A<1 * A<2)) * R<1) + ((R<1 * (R<1/2 * [2*a^4*x + a^3*b]^2)) +
    ((A<0 * (A<1 * R<1)) * (R<1/2 * [2*a^2*x + a*b]^2))))))")

definition "f = (\<lambda>t x. t\<^sup>2 + x\<^sup>2::real)"

lemma ll: "local_lipschitz UNIV UNIV f"
  by (rule c1_implies_local_lipschitz[where f'="\<lambda>(t, x). blinfun_scaleR_left (blinfun_scaleR_left id_blinfun 2) x"])
    (auto intro!: continuous_intros derivative_eq_intros ext simp: f_def split_beta' blinfun.bilinear_simps)

lemma cont: "continuous_on UNIV (\<lambda>t. f t x)"
  by (auto intro!: continuous_intros simp: f_def)

interpretation ll_on_open_real UNIV f UNIV by unfold_locales (auto intro!: ll cont)

definition f1::"real \<Rightarrow> real \<Rightarrow> real" where "f1 t x \<equiv> x\<^sup>2"
definition v::"real \<Rightarrow> real" where "v t = 1 / (1 - t)"

lemma v: "(v solves_ode f1) {0..<1} UNIV" and "v 0 = 1"
  by (auto intro!: solves_odeI derivative_eq_intros ext
    simp: v_def has_vderiv_on_def f1_def has_vector_derivative_def divide_simps power2_eq_square)

lemma
  lower_bound:
  assumes y: "(y solves_ode f) {0 ..< t1} UNIV"
    and iv: "y 0 = 1"
    and t: "t1 < 1" "t \<in> {0 ..< t1}"
  shows "v t \<le> y t"
  using y[THEN solves_ode_on_subset] solves_odeD(1)[OF v, THEN has_vderiv_on_subset]
  apply (rule lower_solution[where ?t0.0 = 0])
  using t
  by (auto simp: f1_def f_def v_def iv)

definition f2::"real \<Rightarrow> real \<Rightarrow> real" where "f2 t x \<equiv> 1 + x\<^sup>2"
definition w::"real \<Rightarrow> real" where "w t = tan (t + pi / 4)"

lemma w: "(w solves_ode f2) {0..<pi/4} UNIV" and "w 0 = 1"
  by (auto intro!: solves_odeI derivative_eq_intros ext
    simp: w_def has_vderiv_on_def f2_def has_vector_derivative_def cos_neq_zeroI
      tan_45 tan_sec divide_simps)

lemma upper_bound:
  assumes y: "(y solves_ode f) {0 ..< t1} UNIV"
    and iv: "y 0 = 1"
    and t: "t1 < pi / 4" "t \<in> {0 ..< t1}"
  shows "y t \<le> w t"
  using y[THEN solves_ode_on_subset] solves_odeD(1)[OF w,THEN has_vderiv_on_subset]
  apply (rule upper_solution[where ?t0.0 = 0])
  using t pi_less_4
  by (auto simp: f2_def f_def w_def iv abs_square_less_1 tan_45)

context
  fixes a::real
  assumes a: "a > 1"
  assumes cond: "1 < 16 * a\<^sup>2 * (a - 1)"
begin

definition w1::"real \<Rightarrow> real" where "w1 t = 1 / (1 - a * t)"
definition w1'::"real \<Rightarrow> real" where "w1' t = a / ((1 - a * t)\<^sup>2)"

lemma w1_lower:
  assumes s: "s < 1 / a" "0 < s"
  shows "f s (w1 s) < w1' s"
proof -
  define smax where "smax \<equiv> 1 / (2 * a)"
  have "a - 1 > (1 - a * s)\<^sup>2 * s\<^sup>2"
  proof -
    have "sqrt ((1 - a * s)\<^sup>2 * s\<^sup>2) = (1 - a * s) * s"
      using a s
      by (auto simp: power_mult_distrib[symmetric] algebra_simps divide_simps
        split: if_split_asm)
    also have "\<dots> = (- a) * s\<^sup>2 + 1 * s + 0" by (simp add: algebra_simps power2_eq_square)
    also have "\<dots> \<le> (1 - a * smax) * smax"
      apply (rule order_trans[OF quadratic_real_max_eq])
      using a s
      by (auto simp: smax_def divide_simps algebra_simps power2_eq_square)
    finally have "((1 - a * s)\<^sup>2 * s\<^sup>2) \<le> (1 - a * smax)\<^sup>2 * smax\<^sup>2"
      unfolding power_mult_distrib[symmetric]
      by (simp add: sqrt_le_D)
    also have "\<dots> < a - 1"
      using a s cond
      by (auto simp add: smax_def power2_eq_square algebra_simps  divide_simps split: if_splits)
    finally show ?thesis .
  qed
  then have "s\<^sup>2 < (a - 1) / (1 - a * s)\<^sup>2"
    using a s
    by (auto simp: divide_simps algebra_simps)
  then have "s\<^sup>2 + (1 / (1 - a * s))\<^sup>2 < a / (1 - a * s)\<^sup>2"
    by (simp add: diff_divide_distrib algebra_simps power_one_over)
  then show ?thesis by (simp add: w1_def w1'_def f_def)
qed

lemma w1: "(w1 has_vderiv_on w1') {0..<1/a}"
  by (auto intro!: derivative_eq_intros split: if_splits
    simp: w1_def w1'_def has_vderiv_on_def has_vector_derivative_def
      algebra_simps divide_simps power2_eq_square)

lemma upper_bound1:
  assumes y: "(y solves_ode f) {0 ..< t1} UNIV"
    and iv: "y 0 = 1"
    and t: "t1 < 1 / a" "t \<in> {0 ..< t1}"
  shows "y t \<le> w1 t"
proof -
  have less_one: "s * a < 1" if a1: "s < t1" and a2: "t1 * a < 1" for s
  proof -
    have "0 < a"
      using a by linarith
    then have "a * s \<le> t1 * a"
      using a1 by (metis (no_types) less_eq_real_def mult.commute real_mult_le_cancel_iff2)
    then have "a * s < 1"
      using a2 by linarith
    then show ?thesis
      by (metis mult.commute)
  qed
  show ?thesis
    using y[THEN solves_ode_on_subset] w1[THEN has_vderiv_on_subset] w1_lower
    apply (rule upper_solution[where ?t0.0 = 0 and S = "{0 ..< t1}"])
    using t a
    by (auto simp: less_one w1_def f_def w1'_def iv divide_simps)
qed

end

definition w16::"real \<Rightarrow> real" where "w16 t = 16 / (16 - 17 * t)"

lemma upper_bound16:
  assumes y: "(y solves_ode f) {0 ..< t1} UNIV"
    and iv: "y 0 = 1"
    and t: "t1 < 16 / 17" "t \<in> {0 ..< t1}"
  shows "y t \<le> w16 t"
  using upper_bound1[of "17/16" y t1 t] assms
  by (simp add: divide_simps w1_def w16_def)

lemma approx_lower_bound:
  "1.142857139 \<le> v 0.125"
  unfolding v_def
  by (approximation 40)

lemma approx_upper_bound:
  "w 0.125 \<le> 1.287426955"
  unfolding w_def
  by (approximation 40)

lemma approx_upper_bound16:
  "w16 0.125 \<le> 1.153153155"
  unfolding w16_def
  by (approximation 40)

end

end
