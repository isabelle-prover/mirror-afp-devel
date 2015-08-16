theory Lemmas_log
imports Complex_Main
begin

lemma ld_ld_1_less:
  assumes "x > 0" "y > 0" shows "1 + log 2 x + log 2 y < 2 * log 2 (x+y)"
proof -
  have 1: "2*x*y < (x+y)^2" using assms
    by(simp add: numeral_eq_Suc algebra_simps add_pos_pos)
  show ?thesis
    apply(rule powr_less_cancel_iff[of 2, THEN iffD1])
     apply simp
    using assms 1 by(simp add: powr_add log_powr[symmetric] powr_numeral)
qed

lemma ld_ld_less2: assumes "x \<ge> 2" "y \<ge> 2"
  shows "1 + log 2 x + log 2 y \<le> 2 * log 2 (x + y - 1)"
proof-
  from assms have "2*x \<le> x*x" "2*y \<le> y*y" by simp_all
  hence 1: "2 * x * y \<le> (x + y - 1)^2"
    by(simp add: numeral_eq_Suc algebra_simps)
  show ?thesis
    apply(rule powr_le_cancel_iff[of 2, THEN iffD1])
     apply simp
    using assms 1 by(simp add: powr_add log_powr[symmetric] powr_numeral)
qed

lemma log_sum_inequality:
  assumes "x > 0" "y > 0" "b > 1"
  shows   "2*log b 2 + log b x + log b y \<le> 2 * log b (x + y)"
proof-
  {
    fix x y :: real assume x_pos: "x > 0" and x_less_y: "x < y"
    let ?f = "\<lambda>t. log b t - 2 * log b (x + t)"
    and ?f' = "\<lambda>t. 1/(t * ln b) - 2/((x + t)*ln b)"
    from x_pos have "\<forall>t\<ge>x. (?f has_real_derivative ?f' t) (at t)"
      by (auto intro!: derivative_eq_intros simp: field_simps)
    with taylor_up[of 1 "\<lambda>i. if i = 0 then ?f else ?f'" ?f x y x] x_less_y
    obtain t where t: "t > x" "t < y"
      "log b y - 2*log b (x + y) = log b x - 2*log b (2*x) + (y - x) * ?f' t"
      by force
    note t(3)
    also from assms have "log b x - 2*log b (2*x) = -log b x - 2*log b 2"
      by (simp_all add: x_pos log_mult)
    also from x_pos t assms have "1/(t * ln b) \<le> 2/((x + t) * ln b)"
      by (simp add: pos_divide_le_eq)
    with x_less_y have "(y - x) * ?f' t \<le> 0"
      by (intro mult_nonneg_nonpos) simp_all
    finally have "2*log b 2 + log b x + log b y \<le> 2 * log b (x + y)"
      by(simp add: algebra_simps)
  }
  from this[of x y] and this[of y x] show ?thesis using assms
    by (cases x y rule: linorder_cases) (simp_all add: add.commute log_mult)
qed

lemma ld_sum_inequality:
  assumes "x > 0" "y > 0"
  shows   "2 + log 2 x + log 2 y \<le> 2 * log 2 (x + y)"
using log_sum_inequality[OF assms, of 2] by simp

end