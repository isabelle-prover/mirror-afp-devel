theory Affine_Arithmetic_Auxiliarities
imports "HOL-Analysis.Analysis"
begin

subsection \<open>derivatives\<close>


lemma DERIV_compose_FDERIV:
  fixes f::"real\<Rightarrow>real"
  assumes "DERIV f (g x) :> f'"
  assumes "(g has_derivative g') (at x within s)"
  shows "((\<lambda>x. f (g x)) has_derivative (\<lambda>x. g' x * f')) (at x within s)"
  using assms has_derivative_compose[of g g' x s f "( * ) f'"]
  by (auto simp: has_field_derivative_def ac_simps)

lemmas has_derivative_sin[derivative_intros] = DERIV_sin[THEN DERIV_compose_FDERIV]
  and  has_derivative_cos[derivative_intros] = DERIV_cos[THEN DERIV_compose_FDERIV]
  and  has_derivative_exp[derivative_intros] = DERIV_exp[THEN DERIV_compose_FDERIV]
  and  has_derivative_ln[derivative_intros] = DERIV_ln[THEN DERIV_compose_FDERIV]
  and  has_derivative_tan[derivative_intros] = DERIV_tan[THEN DERIV_compose_FDERIV]

lemmas [derivative_intros] =
  DERIV_compose_FDERIV[OF DERIV_arctan]
  DERIV_compose_FDERIV[OF DERIV_real_sqrt]
  DERIV_compose_FDERIV[OF floor_has_real_derivative]

lemma has_derivative_powr[derivative_intros]:\<comment> \<open>TODO: generalize @{thm DERIV_powr}?\<close>
  assumes g[derivative_intros]: "(g has_derivative g') (at x within X)"
    and f[derivative_intros]:"(f has_derivative f') (at x within X)"
  assumes pos: "0 < g x" and "x \<in> X"
  shows "((\<lambda>x. g x powr f x::real) has_derivative (\<lambda>h. (g x powr f x) * (f' h * ln (g x) + g' h * f x / g x))) (at x within X)"
proof -
  have "\<forall>\<^sub>F x in at x within X. g x > 0"
    by (rule order_tendstoD[OF _ pos])
      (rule has_derivative_continuous[OF g, unfolded continuous_within])
  then obtain d where "d > 0" and pos': "\<And>x'. x' \<in> X \<Longrightarrow> dist x' x < d \<Longrightarrow> 0 < g x'"
    using pos unfolding eventually_at by force

  have "((\<lambda>x. exp (f x * ln (g x))) has_derivative
    (\<lambda>h. (g x powr f x) * (f' h * ln (g x) + g' h * f x / g x))) (at x within X)"
    using pos
    by (auto intro!: derivative_eq_intros simp: divide_simps powr_def)
  then show ?thesis
    by (rule has_derivative_transform_within[OF _ \<open>d > 0\<close> \<open>x \<in> X\<close>]) (auto simp: powr_def dest: pos')
qed


subsection \<open>@{term sum_list}\<close>

lemma sum_list_nth_eqI:
  fixes xs ys::"'a::monoid_add list"
  shows
    "length xs = length ys \<Longrightarrow> (\<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> x = y) \<Longrightarrow>
      sum_list xs = sum_list ys"
  by (induct xs ys rule: list_induct2) auto

lemma fst_sum_list: "fst (sum_list xs) = sum_list (map fst xs)"
  by (induct xs) auto

lemma snd_sum_list: "snd (sum_list xs) = sum_list (map snd xs)"
  by (induct xs) auto

lemma take_greater_eqI: "take c xs = take c ys \<Longrightarrow> c \<ge> a \<Longrightarrow> take a xs = take a ys"
proof (induct xs arbitrary: a c ys)
  case (Cons x xs) note ICons = Cons
  thus ?case
  proof (cases a)
    case (Suc b)
    thus ?thesis using Cons(2,3)
    proof (cases ys)
      case (Cons z zs)
      from ICons obtain d where c: "c = Suc d"
        by (auto simp: Cons Suc dest!: Suc_le_D)
      show ?thesis
        using ICons(2,3)
        by (auto simp: Suc Cons c intro: ICons(1))
    qed simp
  qed simp
qed (metis le_0_eq take_eq_Nil)

lemma take_max_eqD:
  "take (max a b) xs = take (max a b) ys \<Longrightarrow> take a xs = take a ys \<and> take b xs = take b ys"
  by (metis max.cobounded1 max.cobounded2 take_greater_eqI)

lemma take_Suc_eq: "take (Suc n) xs = (if n < length xs then take n xs @ [xs ! n] else xs)"
  by (auto simp: take_Suc_conv_app_nth)

definition "rad_of w = w * pi / 180"
definition "deg_of w = 180 * w / pi"

lemma deg_rad_of_inverse[simp]: "deg_of (rad_of w) = w" "rad_of (deg_of w) = w"
  by (auto simp: deg_of_def rad_of_def)

lemma deg_of_monoI: "x \<le> y \<Longrightarrow> deg_of x \<le> deg_of y"
  by (auto simp: deg_of_def intro!: divide_right_mono)
lemma rad_of_monoI: "x \<le> y \<Longrightarrow> rad_of x \<le> rad_of y"
  by (auto simp: rad_of_def)
lemma deg_of_strict_monoI: "x < y \<Longrightarrow> deg_of x < deg_of y"
  by (auto simp: deg_of_def intro!: divide_strict_right_mono)
lemma rad_of_strict_monoI: "x < y \<Longrightarrow> rad_of x < rad_of y"
  by (auto simp: rad_of_def)

lemma deg_of_mono[simp]: "deg_of x \<le> deg_of y \<longleftrightarrow> x \<le> y"
  apply (auto intro!: deg_of_monoI)
  using rad_of_monoI by fastforce

lemma rad_of_mono[simp]: "rad_of x \<le> rad_of y \<longleftrightarrow> x \<le> y"
  apply (auto intro!: rad_of_monoI)
  using deg_of_monoI by fastforce

lemma deg_of_strict_mono[simp]: "deg_of x < deg_of y \<longleftrightarrow> x < y"
  apply (auto intro!: deg_of_strict_monoI)
  using rad_of_strict_monoI by fastforce

lemma rad_of_strict_mono[simp]: "rad_of x < rad_of y \<longleftrightarrow> x < y"
  apply (auto intro!: rad_of_strict_monoI)
  using deg_of_strict_monoI by fastforce

lemma rad_of_less_pi_half[simp]: "rad_of L < (pi / 2) \<longleftrightarrow> L < 90"
  apply rule
  subgoal by (simp add: rad_of_def)
  subgoal
    apply (rule less_le_trans[OF rad_of_strict_monoI])
    apply assumption
    apply (simp add: rad_of_def; fail)
    done
  done

lemma rad_of_times_2_less_pi[simp]: "rad_of L * 2 < pi  \<longleftrightarrow> L < 90"
  using rad_of_less_pi_half[of L]
  by (simp )

lemma pi_half_less_rad_of[simp]: "- (pi / 2) < rad_of L \<longleftrightarrow> -90 < L"
  apply auto
  subgoal
    apply (simp add: rad_of_def)
    by (metis Groups.mult_ac(2) more_arith_simps(8) mult_less_cancel_left_disj pi_not_less_zero)
  subgoal
    apply (rule le_less_trans[OF _ rad_of_strict_monoI])
     prefer 2 apply assumption
    apply (simp add: rad_of_def; fail)
    done
  done

lemma le_deg_of_arctan_divideI:
  "L \<le> deg_of (arctan (y / x))"
  if "tan (rad_of L) * x \<le> y" "-90 < L" "0 < x" "L < 90"
  apply (rule order_trans[OF _ deg_of_monoI])
   prefer 2
   apply (rule arctan_monotone')
   apply (subst pos_le_divide_eq)
    apply fact
   apply fact
  by (simp_all add: arctan_tan that)

lemma ge_deg_of_arctan_divideI:
  "deg_of (arctan (y / x)) \<le> G"
  if "y \<le> tan (rad_of G) * x" "-90 < G" "0 < x" "G < 90"
  apply (rule order_trans[OF deg_of_monoI])
   apply (rule arctan_monotone')
   apply (subst pos_divide_le_eq)
    apply fact
   apply fact
  by (simp_all add: arctan_tan that)

lemma le_deg_of_arctan_divideD:
  "tan (rad_of L) * x \<le> y"
  if "L \<le> deg_of (arctan (y / x))" "-90 < L" "0 < x" "L < 90"
  apply (rule order_trans[OF mult_right_mono])
    apply (rule tan_mono_le)
      apply (simp add: that)
     apply (rule rad_of_monoI)
     apply fact
  subgoal
    using arctan_ubound
    by simp
  subgoal using that by simp
  using that
  by (auto simp: tan_arctan)

lemma ge_deg_of_arctan_divideD:
  "y \<le> tan (rad_of L) * x"
  if "deg_of (arctan (y / x)) \<le> L" "-90 < L" "0 < x" "L < 90"
  apply (rule order_trans[OF _ mult_right_mono])
    prefer 2
    apply (rule tan_mono_le)
    prefer 2
     apply (rule rad_of_monoI)
     apply fact
  subgoal by (simp add: arctan_lbound)
  subgoal using that by simp
  using that
  by (auto simp: tan_arctan)

end
