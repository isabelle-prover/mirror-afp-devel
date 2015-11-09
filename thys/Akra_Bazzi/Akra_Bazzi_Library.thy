(*
  File:   Akra_Bazzi_Library.thy
  Author: Manuel Eberl <eberlm@in.tum.de>

  Lemma bucket for the Akra–Bazzi theorem.
*)

section {* Auxiliary lemmas *}
theory Akra_Bazzi_Library
imports 
  Complex_Main
  "~~/src/HOL/Multivariate_Analysis/Integration"
  "../Landau_Symbols/Landau_Library"
begin

declare DERIV_powr[THEN DERIV_chain2, derivative_intros]

lemma setsum_pos':
  assumes "finite I"
  assumes "\<exists>x\<in>I. f x > (0 :: _ :: linordered_ab_group_add)"
  assumes "\<And>x. x \<in> I \<Longrightarrow> f x \<ge> 0"
  shows   "setsum f I > 0"
proof-
  from assms(2) guess x by (elim bexE) note x = this
  from x have "I = insert x I" by blast
  also from assms(1) have "setsum f ... = f x + setsum f (I - {x})" by (rule setsum.insert_remove)
  also from x assms have "... > 0" by (intro add_pos_nonneg setsum_nonneg) simp_all
  finally show ?thesis .
qed


lemma min_mult_left:
  assumes "(x::real) > 0"
  shows   "x * min y z = min (x*y) (x*z)"
  using assms by (auto simp add: min_def algebra_simps)

lemma max_mult_left:
  assumes "(x::real) > 0"
  shows   "x * max y z = max (x*y) (x*z)"
  using assms by (auto simp add: max_def algebra_simps)

lemma DERIV_nonneg_imp_mono:
  assumes "\<And>t. t\<in>{x..y} \<Longrightarrow> (f has_field_derivative f' t) (at t)"
  assumes "\<And>t. t\<in>{x..y} \<Longrightarrow> f' t \<ge> 0"
  assumes "(x::real) \<le> y"
  shows   "(f x :: real) \<le> f y"
proof (cases x y rule: linorder_cases)
  assume xy: "x < y"
  hence "\<exists>z. x < z \<and> z < y \<and> f y - f x = (y - x) * f' z"
    by (rule MVT2) (insert assms(1), simp)
  then guess z by (elim exE conjE) note z = this
  from z(1,2) assms(2) xy have "0 \<le> (y - x) * f' z" by (intro mult_nonneg_nonneg) simp_all
  also note z(3)[symmetric]
  finally show "f x \<le> f y" by simp
qed (insert assms(3), simp_all)

lemma eventually_conjE: "eventually (\<lambda>x. P x \<and> Q x) F \<Longrightarrow> (eventually P F \<Longrightarrow> eventually Q F \<Longrightarrow> R) \<Longrightarrow> R"
  apply (frule eventually_rev_mp[of _ _ P], simp)
  apply (drule eventually_rev_mp[of _ _ Q], simp)
  apply assumption
  done

lemma real_natfloor_nat: "x \<in> \<nat> \<Longrightarrow> real (nat \<lfloor>x\<rfloor>) = x" by (elim Nats_cases) simp

lemma eventually_natfloor:
  assumes "eventually P (at_top :: nat filter)"
  shows   "eventually (\<lambda>x. P (nat \<lfloor>x\<rfloor>)) (at_top :: real filter)"
proof-
  from assms obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> P n" using eventually_at_top_linorder by blast
  have "\<forall>n\<ge>real N. P (nat \<lfloor>n\<rfloor>)" by (intro allI impI N le_nat_floor) simp_all
  thus ?thesis using eventually_at_top_linorder by blast
qed


lemma tendsto_ln_over_ln:
  assumes "(a::real) > 0" "c > 0"
  shows   "((\<lambda>x. ln (a*x) / ln (c*x)) ---> 1) at_top"
proof (rule lhospital_at_top_at_top)
  show "LIM x at_top. ln (c*x) :> at_top"
    by (intro filterlim_compose[OF ln_at_top] filterlim_tendsto_pos_mult_at_top[OF tendsto_const] 
              filterlim_ident assms(2))
  show "eventually (\<lambda>x. ((\<lambda>x. ln (a*x)) has_real_derivative (inverse x)) (at x)) at_top"
    using eventually_gt_at_top[of "inverse a"] assms
    by (auto elim!: eventually_elim1 intro!: derivative_eq_intros simp: field_simps)
  show "eventually (\<lambda>x. ((\<lambda>x. ln (c*x)) has_real_derivative (inverse x)) (at x)) at_top"
    using eventually_gt_at_top[of "inverse c"] assms
    by (auto elim!: eventually_elim1 intro!: derivative_eq_intros simp: field_simps)
  show "((\<lambda>x::real. inverse x / inverse x) ---> 1) at_top"
    by (subst tendsto_cong[of _ "\<lambda>_. 1"]) (simp_all add: eventually_not_equal)
qed (simp_all add: eventually_not_equal)


lemma taylor_up2:
  assumes "\<forall>t. c \<le> t \<and> t \<le> b \<longrightarrow> (f has_real_derivative f' t) (at t)"
  assumes "\<forall>t. c \<le> t \<and> t \<le> b \<longrightarrow> (f' has_real_derivative f'' t) (at t)"
  assumes  "c < b"
  shows    "\<exists>t. t > c \<and> t < b \<and> f b = f c + f' c * (b - c) + f'' t * (b - c)^2 / 2"
  using taylor_up[of 2 "op! [f,f',f'']" f c b c] assms
  by (force simp: eval_nat_numeral less_Suc_eq)

lemma one_plus_x_approx_ex:
  assumes x: "(x::real) \<ge> -0.5" "x \<le> 0.5"
  obtains t where "t > -0.5" "t < 0.5" "(1 + x) powr p = 
    1 + p * x + p * (p - 1) * (1 + t) powr (p - 2) / 2 * x ^ 2"
proof (cases "x = 0")
  assume x': "x \<noteq> 0"
  let ?f = "\<lambda>x. (1 + x) powr p"
  let ?f' = "\<lambda>x. p * (1 + x) powr (p - 1)"
  let ?f'' = "\<lambda>x. p * (p - 1) * (1 + x) powr (p - 2)"
  let ?fs = "op! [?f, ?f', ?f'']"
 
  have A: "\<forall>m t. m < 2 \<and> t \<ge> -0.5 \<and> t \<le> 0.5 \<longrightarrow> (?fs m has_real_derivative ?fs (Suc m) t) (at t)"
  proof (clarify)
    fix m :: nat and t :: real assume m: "m < 2" and t: "t \<ge> -0.5" "t \<le> 0.5"
    thus "(?fs m has_real_derivative ?fs (Suc m) t) (at t)"
      using m by (cases m) (force intro: derivative_eq_intros algebra_simps)+
  qed
  have "\<exists>t. (if x < 0 then x < t \<and> t < 0 else 0 < t \<and> t < x) \<and>
              (1 + x) powr p = (\<Sum>m<2. ?fs m 0 / (fact m) * (x - 0)^m) + 
              ?fs 2 t / (fact 2) * (x - 0)\<^sup>2"
    using assms x' by (intro taylor[OF _ _ A]) simp_all
  then guess t by (elim exE conjE)
  note t = this
  with assms have "t > -0.5" "t < 0.5" by (auto split: split_if_asm)
  moreover from t(2) have "(1 + x) powr p = 1 + p * x + p * (p - 1) * (1 + t) powr (p - 2) / 2 * x ^ 2"
    by (simp add: numeral_2_eq_2 real_of_nat_Suc)
  ultimately show ?thesis by (rule that)
next
  assume "x = 0"
  with that[of 0] show ?thesis by simp
qed

lemma tendsto_ln_over_powr: 
  assumes "(a::real) > 0"
  shows   "((\<lambda>x. ln x / x powr a) ---> 0) at_top"
proof (rule lhospital_at_top_at_top)
  from assms show "LIM x at_top. x powr a :> at_top" by (rule powr_at_top)
  show "eventually (\<lambda>x. a * x powr (a - 1) \<noteq> 0) at_top"
    using eventually_gt_at_top[of "0::real"] by eventually_elim (insert assms, simp)
  show "eventually (\<lambda>x::real. (ln has_real_derivative (inverse x)) (at x)) at_top"
    using eventually_gt_at_top[of "0::real"] DERIV_ln by (elim eventually_elim1) simp
  show "eventually (\<lambda>x. ((\<lambda>x. x powr a) has_real_derivative a * x powr (a - 1)) (at x)) at_top"
    using eventually_gt_at_top[of "0::real"] DERIV_powr by (elim eventually_elim1) simp
  have "eventually (\<lambda>x. inverse a * x powr -a = inverse x / (a*x powr (a-1))) at_top"
    using eventually_gt_at_top[of "0::real"] 
    by (elim eventually_elim1) (simp add: field_simps powr_divide2[symmetric] powr_minus)
  moreover from assms have "((\<lambda>x. inverse a * x powr -a) ---> 0) at_top"
    by (intro tendsto_mult_right_zero tendsto_neg_powr filterlim_ident) simp_all
  ultimately show "((\<lambda>x. inverse x / (a * x powr (a - 1))) ---> 0) at_top"
    by (subst (asm) tendsto_cong) simp_all
qed


lemma integrable_const_real: "(\<lambda>x :: real. c) integrable_on {a..b}"
  using integrable_const[of c a b] by simp

lemma fundamental_theorem_of_calculus_real:
  "a \<le> b \<Longrightarrow> \<forall>x\<in>{a..b}. (f has_real_derivative f' x) (at x within {a..b}) \<Longrightarrow>
      (f' has_integral (f b - f a)) {a..b}"
  by (intro fundamental_theorem_of_calculus ballI)
     (simp_all add: has_field_derivative_iff_has_vector_derivative[symmetric])

lemma integral_powr:
  "y \<noteq> -1 \<Longrightarrow> a \<le> b \<Longrightarrow> a > 0 \<Longrightarrow> integral {a..b} (\<lambda>x. x powr y :: real) = 
     inverse (y + 1) * (b powr (y + 1) - a powr (y + 1))"
  by (subst right_diff_distrib, intro integral_unique fundamental_theorem_of_calculus_real)
     (auto intro!: derivative_eq_intros)

lemma integral_ln_powr_over_x:
  "y \<noteq> -1 \<Longrightarrow> a \<le> b \<Longrightarrow> a > 1 \<Longrightarrow> integral {a..b} (\<lambda>x. ln x powr y / x :: real) = 
     inverse (y + 1) * (ln b powr (y + 1) - ln a powr (y + 1))"
  by (subst right_diff_distrib, intro integral_unique fundamental_theorem_of_calculus_real)
     (auto intro!: derivative_eq_intros)     

lemma integral_one_over_x_ln_x:
  "a \<le> b \<Longrightarrow> a > 1 \<Longrightarrow> integral {a..b} (\<lambda>x. inverse (x * ln x) :: real) = ln (ln b) - ln (ln a)"
  by (intro integral_unique fundamental_theorem_of_calculus_real)
     (auto intro!: derivative_eq_intros simp: field_simps)

lemma one_plus_x_approx:
  assumes x: "(x::real) > 0"
  obtains t where "t > 0" "t < x" "(1 + x) powr p = 
    1 + p * x + p * (p - 1) * (1 + t) powr (p - 2) / 2 * x ^ 2"
  using taylor_up2[of 0 x "\<lambda>x. (1+x) powr p" "\<lambda>x. p*(1+x) powr (p - 1)"]
proof-
  let ?f = "\<lambda>x. (1 + x) powr p"
  let ?f' = "\<lambda>x. p * (1 + x) powr (p - 1)"
  let ?f'' = "\<lambda>x. p * (p - 1) * (1 + x) powr (p - 2)"
  have "\<forall>t. t \<ge> 0 \<and> t \<le> x \<longrightarrow> (?f has_real_derivative ?f' t) (at t)"
       "\<forall>t. t \<ge> 0 \<and> t \<le> x \<longrightarrow> (?f' has_real_derivative ?f'' t) (at t)"
    by (force intro!: derivative_eq_intros)+
  from taylor_up2[OF this x] that show ?thesis by force
qed

lemma one_plus_x_approx':
  assumes x: "(x::real) > 0" "x < 1"
  obtains t where "t > 0" "t < x" "(1 + x) powr p = 1 + p * (1 + t) powr (p - 1) * x"
proof-
  let ?f = "\<lambda>x. (1 + x) powr p"
  let ?f' = "\<lambda>x. p * (1 + x) powr (p - 1)"
  let ?fs = "op! [?f, ?f']"
  from x have "\<forall>m t. m < 1 \<and> t \<ge> 0 \<and> t \<le> x \<longrightarrow> (?fs m has_real_derivative ?fs (Suc m) t) (at t)"
    by (force intro: derivative_eq_intros simp: field_simps)
  from taylor_up[OF _ _ this, where f = ?f and c = 0] x that show ?thesis 
    by (auto simp: numeral_2_eq_2 field_simps)
qed

lemma one_plus_x_upper_bound:
  obtains k where "k \<ge> 0" "\<And>x. (x::real) > 0 \<Longrightarrow> x < 1 \<Longrightarrow> (1 + x) powr p \<le> 1 + k * x"
proof-
  {
    fix x :: real assume x: "x > 0" "x < 1"
    let ?k = "\<bar>p\<bar> * max 1 (2 powr (p - 1))"
    from x have "x > 0" "x < 1" by simp_all
    from one_plus_x_approx'[OF this, of p] guess t .
    note t = this
      
    have "p*(1 + t) powr (p-1) \<le> \<bar>p * (1+t) powr (p-1)\<bar>" by simp
    also have "... \<le> \<bar>p\<bar> * (1 + t) powr (p - 1)"
      by (subst abs_mult, subst (2) abs_of_nonneg) simp_all
    also from x t have A: "(1 + t) powr (p - 1) \<le> max (1 powr (p - 1)) (2 powr (p - 1))" 
      by (intro powr_upper_bound) simp_all 
    hence "\<bar>p\<bar> * (1 + t) powr (p - 1) \<le> ?k" 
      by (intro divide_right_mono mult_left_mono) simp_all
    finally have "p*(1+t) powr (p-1) * x \<le> ?k * x" using x
      by (intro mult_right_mono) (simp_all add: algebra_simps)
    hence "1 + p*(1+t) powr (p-1) * x \<le> 1 + ?k * x" by simp
    hence "(1 + x) powr p \<le> 1 + ?k*x" by (subst t) simp_all
  }
  note A = that[OF _ this]
  show ?thesis by (intro A mult_nonneg_nonneg) simp_all
qed


lemma one_minus_x_approx:
  assumes x: "(x::real) > 0" "x < 1"
  obtains t where "t > 0" "t < x" "(1 - x) powr p = 1 - p * x + p * (p - 1) * (1 - t) powr (p - 2) / 2 * x ^ 2"
proof-
  let ?f = "\<lambda>x. (1 - x) powr p"
  let ?f' = "\<lambda>x. -p * (1 - x) powr (p - 1)"
  let ?f'' = "\<lambda>x. p * (p - 1) * (1 - x) powr (p - 2)"
  let ?fs = "op! [?f, ?f', ?f'']"
  
  have "\<forall>m t. m < 2 \<and> t \<ge> 0 \<and> t \<le> x \<longrightarrow> (?fs m has_real_derivative ?fs (Suc m) t) (at t)"
  proof (clarify)
    fix m :: nat and t :: real assume m: "m < 2" and t: "t \<ge> 0" "t \<le> x"
    with x show "(?fs m has_real_derivative ?fs (Suc m) t) (at t)"
      by (cases m) (force intro: derivative_eq_intros simp: algebra_simps)+
  qed
  from taylor_up[OF _ _ this, where f = ?f and c = 0] x that show ?thesis 
    by (auto simp: numeral_2_eq_2 field_simps)
qed

lemma one_minus_x_lower_bound:
  obtains k where "k \<ge> 0" "\<And>x. (x::real) > 0 \<Longrightarrow> x < 0.5 \<Longrightarrow> (1 - x) powr p \<le> 1 - p*x + k*x^2"
proof-
  {
    fix x :: real assume x: "x > 0" "x < 0.5"
    let ?k = "\<bar>p*(p-1)\<bar> * max (0.5 powr (p - 2)) 1 / 2"
    from x have "x > 0" "x < 1" by simp_all
    from one_minus_x_approx[OF this, of p] guess t .
    note t = this
    have "max (0.5 powr (p - 2)) 1 = max (0.5 powr (p - 2)) (1 powr (p - 2))" by simp
    also from x t have "(1 - t) powr (p - 2) \<le> max (0.5 powr (p - 2)) (1 powr (p - 2))" 
      by (intro powr_upper_bound) simp_all
    hence "-\<bar>p*(p-1)\<bar> * max (0.5 powr (p - 2)) (1 powr (p - 2)) / 2 \<le> 
           -\<bar>p*(p-1)\<bar> * (1 - t) powr (p - 2) / 2"
      by (intro divide_right_mono mult_left_mono_neg) simp_all
    also have "... = -\<bar>p * (p - 1) * (1 - t) powr (p - 2)\<bar> / 2" 
      by (subst abs_mult, subst (3) abs_of_nonneg) simp_all
    also have "... \<le> -p * (p - 1) * (1 - t) powr (p - 2) / 2" by simp
    finally have "?k * x^2 \<ge> p * (p - 1) * (1 - t) powr (p - 2) / 2 * x^2" using x
      by (intro mult_right_mono) (simp_all add: algebra_simps)
    hence "1 - p * x + ?k * x^2 \<ge> 1 - p * x + p * (p - 1) * (1 - t) powr (p - 2) / 2 * x^2" by simp
    hence "1 - p * x + ?k * x^2 \<ge> (1 - x) powr p" by (subst t) (simp_all)
  }
  note A = that[OF _ this]
  show ?thesis by (intro A mult_nonneg_nonneg) simp_all
qed

lemma one_minus_x_approx':
  assumes x: "(x::real) > 0" "x < 1"
  obtains t where "t > 0" "t < x" "(1 - x) powr p = 1 - p * (1 - t) powr (p - 1) * x"
proof-
  let ?f = "\<lambda>x. (1 - x) powr p"
  let ?f' = "\<lambda>x. -p * (1 - x) powr (p - 1)"
  let ?fs = "op! [?f, ?f']"
  from x have "\<forall>m t. m < 1 \<and> t \<ge> 0 \<and> t \<le> x \<longrightarrow> (?fs m has_real_derivative ?fs (Suc m) t) (at t)"
    by (force intro: derivative_eq_intros simp: field_simps)
  from taylor_up[OF _ _ this, where f = ?f and c = 0] x that show ?thesis 
    by (auto simp: numeral_2_eq_2 field_simps)
qed


lemma one_minus_x_lower_bound':
  obtains k where "k \<ge> 0" "\<And>x. (x::real) > 0 \<Longrightarrow> x < 0.5 \<Longrightarrow> (1 - x) powr p \<ge> 1 - k * x"
proof-
  {
    fix x :: real assume x: "x > 0" "x < 0.5"
    let ?k = "\<bar>p\<bar> * max (0.5 powr (p - 1)) 1"
    from x have "x > 0" "x < 1" by simp_all
    from one_minus_x_approx'[OF this, of p] guess t .
    note t = this
    have "max (0.5 powr (p - 1)) 1 = max (0.5 powr (p - 1)) (1 powr (p - 1))" by simp
    also from x t have "(1 - t) powr (p - 1) \<le> max (0.5 powr (p - 1)) (1 powr (p - 1))" 
      by (intro powr_upper_bound) simp_all
    hence "-\<bar>p\<bar> * max (0.5 powr (p - 1)) (1 powr (p - 1)) \<le> -\<bar>p\<bar> * (1 - t) powr (p - 1)"
      by (intro mult_left_mono_neg) simp_all
    also have "... = -\<bar>p * (1 - t) powr (p - 1)\<bar>" 
      by (subst abs_mult, subst (3) abs_of_nonneg) simp_all
    also have "... \<le> -p * (1 - t) powr (p - 1)" by simp
    finally have "-?k * x \<le> -p * (1 - t) powr (p - 1) * x" using x
      by (intro mult_right_mono) (simp_all add: algebra_simps)
    hence "1 - ?k * x \<le> 1 - p * (1 - t) powr (p - 1) * x" by simp
    also from t have "... = (1 - x) powr p" by simp
    finally have "(1 - x) powr p \<ge> 1 - \<bar>p\<bar> * max ((5 / 10) powr (p - 1)) 1 * x" .
  }
  note A = that[OF _ this]
  show ?thesis by (intro A mult_nonneg_nonneg) simp_all
qed

lemma one_plus_x_lower_bound':
  obtains k where "\<And>x. (x::real) > 0 \<Longrightarrow> x < 1 \<Longrightarrow> (1 + x) powr p \<ge> 1 + k * x"
proof-
  {
    fix x :: real assume x: "x > 0" "x < 1"
    let ?k = "min p 0 * max 1 (2 powr (p - 1))"
    from one_plus_x_approx'[OF x, of p] guess t . note t = this
    from t x have "(1 + t) powr (p - 1) \<le> max (1 powr (p - 1)) (2 powr (p - 1))"
      by (intro powr_upper_bound) simp_all
    hence "p * (1 + t) powr (p - 1) \<ge> ?k" 
      by (cases "p \<le> 0") (simp_all add: min_def mult_left_mono_neg)
    hence "?k * x \<le> p * (1 + t) powr (p - 1) * x" using x
      by (intro mult_right_mono) simp_all
    with t(3) have "1 + ?k * x \<le> (1 + x) powr p" by simp
  }
  from this and that show ?thesis by blast
qed

lemma one_minus_x_upper_bound':
  obtains k where "\<And>x. (x::real) > 0 \<Longrightarrow> x < 0.5 \<Longrightarrow> (1 - x) powr p \<le> 1 + k * x"
proof-
  {
    fix x :: real assume x: "x > 0" "x < 0.5"
    let ?k = "-(if p \<ge> 0 then 0 else p) * max (0.5 powr (p - 1)) 1"
    from x have "x < 1" by simp
    from one_minus_x_approx'[OF x(1) this, of p] guess t . note t = this

    from t x have "(1 - t) powr (p - 1) \<le> max (0.5 powr (p - 1)) (1 powr (p - 1))"
      by (intro powr_upper_bound) simp_all
    hence "-p * (1 - t) powr (p - 1) \<le> ?k" by (cases "p \<ge> 0") simp_all
    hence "-p * (1 - t) powr (p - 1) * x \<le> ?k * x" by (rule mult_right_mono) (insert x, simp_all)
    with t(3) have "1 + ?k * x \<ge> (1 - x) powr p" by simp
  }
  from this and that show ?thesis by blast
qed

lemma x_times_x_minus_1_nonneg: "x \<le> 0 \<or> x \<ge> 1 \<Longrightarrow> (x::_::linordered_idom) * (x - 1) \<ge> 0"
proof (elim disjE)
  assume x: "x \<le> 0"
  also have "0 \<le> x^2" by simp
  finally show "x * (x - 1) \<ge> 0" by (simp add: power2_eq_square algebra_simps)
qed simp

lemma x_times_x_minus_1_nonpos: "x \<ge> 0 \<Longrightarrow> x \<le> 1 \<Longrightarrow> (x::_::linordered_idom) * (x - 1) \<le> 0"
  by (intro mult_nonneg_nonpos) simp_all

lemma one_plus_powr_ge:
  assumes "p \<le> 0 \<or> p \<ge> 1" "(x::real) > -0.5"
  shows   "(1 + x) powr p \<ge> 1 + p * x"
proof (cases "x > 0")
  assume "x > 0"
  from one_plus_x_approx[OF this, of p] guess t .
  note t = this
  have "(p*(p - 1)) * (1+t) powr (p - 2) / 2 * x^2 \<ge> 0"
    by (rule mult_nonneg_nonneg, rule divide_nonneg_pos, rule mult_nonneg_nonneg)
       (simp_all add: x_times_x_minus_1_nonneg assms)
  with t(3) show ?thesis by simp
next
  assume "\<not>(x > 0)"
  with assms have "x \<ge> -0.5" "x \<le> 0.5" by simp_all
  from one_plus_x_approx_ex[OF this, of p] guess t .
  note t = this
  have "(p*(p - 1)) * (1+t) powr (p - 2) / 2 * x^2 \<ge> 0"
    by (rule mult_nonneg_nonneg, rule divide_nonneg_pos, rule mult_nonneg_nonneg)
       (simp_all add: x_times_x_minus_1_nonneg assms)
  with t(3) show ?thesis by simp
qed

end