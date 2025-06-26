section \<open>Asymptotic and Qualitative Properties\<close>

theory Asymptotic_Qualitative_Properties
  imports Derivative_Identities_Smoothness
begin

subsection \<open>Limits at Infinity of Sigmoid and its Derivative\<close>

text \<open>
  --- Asymptotic Behaviour ---
  We have
  \[
    \lim_{x\to+\infty} \sigma(x) = 1,
    \quad
    \lim_{x\to-\infty} \sigma(x) = 0.
  \]
\<close>

lemma lim_sigmoid_infinity: "((\<lambda>x. sigmoid x) \<longlongrightarrow> 1) at_top"
  unfolding sigmoid_def by real_asymp

lemma lim_sigmoid_minus_infinity: "(sigmoid \<longlongrightarrow> 0) at_bot"
  unfolding sigmoid_def by real_asymp

lemma sig_deriv_lim_at_top: "(deriv sigmoid \<longlongrightarrow> 0) at_top"
proof (subst tendsto_at_top_epsilon_def, clarify)
  fix \<epsilon> :: real
  assume \<epsilon>_pos: "0 < \<epsilon>"

  text \<open>Using the fact that \(\sigma(x) \to 1\) as \(x \to +\infty\).\<close>

  obtain N where N_def: "\<forall>x \<ge> N. \<bar>sigmoid x - 1\<bar> < \<epsilon> / 2"
    using lim_sigmoid_infinity[unfolded tendsto_at_top_epsilon_def] \<epsilon>_pos
    by (metis  half_gt_zero)

  have deriv_bound: "\<forall>x \<ge> N. \<bar>deriv sigmoid x\<bar> \<le> \<bar>sigmoid x - 1\<bar>"
  proof (clarify)
    fix x
    assume "x \<ge> N"
    hence "\<bar>deriv sigmoid x\<bar> = \<bar>sigmoid x - 1 + 1\<bar> * \<bar>1 - sigmoid x\<bar>"
      by (simp add: abs_mult sigmoid_derivative)

    also have "... \<le> \<bar>sigmoid x - 1\<bar>"
      by (smt (verit) mult_cancel_right1 mult_right_mono sigmoid_range)
    finally show "\<bar>deriv sigmoid x\<bar> \<le> \<bar>sigmoid x - 1\<bar>".      
  qed

  have "\<forall>x \<ge> N. \<bar>deriv sigmoid x\<bar> < \<epsilon>"
  proof (clarify)
    fix x
    assume "x \<ge> N"
    hence "\<bar>deriv sigmoid x\<bar> \<le> \<bar>sigmoid x - 1\<bar>"
      using deriv_bound by simp
    also have "... < \<epsilon> / 2"
      using `x \<ge> N` N_def by simp
    also have "... < \<epsilon>"
      using \<epsilon>_pos by simp
    finally show "\<bar>deriv sigmoid x\<bar> < \<epsilon>" .
  qed

  then show "\<exists>N::real. \<forall>x\<ge>N. \<bar>deriv sigmoid x - (0::real)\<bar> < \<epsilon>"
    by (metis diff_zero)
qed

lemma sig_deriv_lim_at_bot: "(deriv sigmoid \<longlongrightarrow> 0) at_bot"
proof (subst tendsto_at_bot_epsilon_def, clarify)
  fix \<epsilon> :: real
  assume \<epsilon>_pos: "0 < \<epsilon>"

  text \<open>Using the fact that \(\sigma(x) \to 0\) as \(x \to -\infty\).\<close>

  obtain N where N_def: "\<forall>x \<le> N. \<bar>sigmoid x - 0\<bar> < \<epsilon> / 2"
    using lim_sigmoid_minus_infinity[unfolded tendsto_at_bot_epsilon_def] \<epsilon>_pos
    by (meson half_gt_zero)

  have deriv_bound: "\<forall>x \<le> N. \<bar>deriv sigmoid x\<bar> \<le> \<bar>sigmoid x - 0\<bar>"
  proof (clarify)
    fix x
    assume "x \<le> N"
    hence "\<bar>deriv sigmoid x\<bar> = \<bar>sigmoid x - 0 + 0\<bar> * \<bar>1 - sigmoid x\<bar>"
      by (simp add: abs_mult sigmoid_derivative)
    also have "... \<le> \<bar>sigmoid x - 0\<bar>"
      by (smt (verit, del_insts) mult_cancel_left2 mult_left_mono sigmoid_range)
    finally show "\<bar>deriv sigmoid x\<bar> \<le> \<bar>sigmoid x - 0\<bar>".
  qed

  have "\<forall>x \<le> N. \<bar>deriv sigmoid x\<bar> < \<epsilon>"
  proof (clarify)
    fix x
    assume "x \<le> N"
    hence "\<bar>deriv sigmoid x\<bar> \<le> \<bar>sigmoid x - 0\<bar>"
      using deriv_bound by simp
    also have "... < \<epsilon> / 2"
      using `x \<le> N` N_def by simp
    also have "... < \<epsilon>"
      using \<epsilon>_pos by simp
    finally show "\<bar>deriv sigmoid x\<bar> < \<epsilon>".
  qed

  then show "\<exists>N::real. \<forall>x \<le> N. \<bar>deriv sigmoid x - (0::real)\<bar> < \<epsilon>"
    by (metis diff_zero)
qed

subsection \<open>Curvature and Inflection\<close>

lemma second_derivative_sigmoid_positive_on:
  assumes "x < 0"
  shows "Nth_derivative 2 sigmoid x > 0"
proof -
  have "1 - 2 * sigmoid x > 0"
    using assms sigmoid_left_dom_range by force
  then show "Nth_derivative 2 sigmoid x > 0"
    by (simp add: sigmoid_range sigmoid_second_derivative)
qed

lemma second_derivative_sigmoid_negative_on:
  assumes "x > 0"
  shows "Nth_derivative 2 sigmoid x < 0"
proof -
  have "1 - 2 * sigmoid x < 0"
    by (smt (verit) assms sigmoid_strictly_increasing sigmoid_symmetry)
  then show "Nth_derivative 2 sigmoid x < 0"
    by (simp add: mult_pos_neg sigmoid_range sigmoid_second_derivative)
qed

lemma sigmoid_inflection_point:
  "Nth_derivative 2 sigmoid 0 = 0"
  by (simp add: sigmoid_alt_def sigmoid_second_derivative)

subsection \<open>Monotonicity and Bounds of the First Derivative\<close>

lemma sigmoid_positive_derivative:
"deriv sigmoid x > 0"
  by (simp add: sigmoid_derivative sigmoid_range)

lemma sigmoid_deriv_0:
"deriv sigmoid 0 = 1/4"
proof -
  have f1: "1 / (1 + 1) = sigmoid 0"
    by (simp add: sigmoid_def)
  then have f2: "\<forall>r. sigmoid 0 * (r + r) = r"
    by simp
  then have f3: "\<forall>n. sigmoid 0 * numeral (num.Bit0 n) = numeral n"
    by (metis (no_types) numeral_Bit0)
  have f4: "\<forall>r. sigmoid r * sigmoid (- r) = deriv sigmoid r"
    using sigmoid_derivative sigmoid_symmetry by presburger
  have "sigmoid 0 = 0 \<longrightarrow> deriv sigmoid 0 = 1 / 4"
    using f1 by force
  then show ?thesis
    using f4 f3 f2 by (metis (no_types) add.inverse_neutral divide_divide_eq_right nonzero_mult_div_cancel_left one_add_one zero_neq_numeral)
qed

lemma deriv_sigmoid_increase_on_negatives:
  assumes "x2 < 0"
  assumes "x1 < x2" 
  shows "deriv sigmoid x1 < deriv sigmoid x2"
  by(rule DERIV_pos_imp_increasing, simp add: assms(2), metis assms(1) deriv_sigmoid_has_deriv 
          dual_order.strict_trans linorder_not_le nle_le second_derivative_alt_def second_derivative_sigmoid_positive_on)
  
lemma deriv_sigmoid_decreases_on_positives:
  assumes "0 < x1"
  assumes "x1 < x2" 
  shows "deriv sigmoid x2 < deriv sigmoid x1"
  by(rule DERIV_neg_imp_decreasing, simp add: assms(2), metis assms(1) deriv_sigmoid_has_deriv 
          dual_order.strict_trans linorder_not_le nle_le second_derivative_alt_def second_derivative_sigmoid_negative_on)

lemma sigmoid_derivative_upper_bound:
  assumes "x\<noteq> 0"
  shows "deriv sigmoid x < 1/4"
proof(cases "x \<le> 0")
  assume "x\<le>0"
  then have neg_case: "x < 0"
    using assms by linarith
  then have "deriv sigmoid x < deriv sigmoid 0"
  proof(rule DERIV_pos_imp_increasing_open)
    show "\<And>xa::real. x < xa \<Longrightarrow> xa < 0 \<Longrightarrow> \<exists>y::real. (deriv sigmoid has_real_derivative y) (at xa) \<and> 0 < y"
      by (metis (no_types) deriv_sigmoid_has_deriv second_derivative_alt_def second_derivative_sigmoid_positive_on)
    show "continuous_on {x..0::real} (deriv sigmoid)"
      by (meson DERIV_atLeastAtMost_imp_continuous_on deriv_sigmoid_has_deriv)
  qed
  then show "deriv sigmoid x < 1/4"
    by (simp add: sigmoid_deriv_0)
next
  assume "\<not> x \<le> 0"
  then have "0 < x"
    by linarith
  then have "deriv sigmoid x < deriv sigmoid 0"
  proof(rule DERIV_neg_imp_decreasing_open)
    show "\<And>xa::real. 0 < xa \<Longrightarrow> xa < x \<Longrightarrow> \<exists>y::real. (deriv sigmoid has_real_derivative y) (at xa) \<and> y < 0"
      by (metis (no_types) deriv_sigmoid_has_deriv second_derivative_alt_def second_derivative_sigmoid_negative_on)
    show "continuous_on {0..x::real} (deriv sigmoid)"
      by (meson DERIV_atLeastAtMost_imp_continuous_on deriv_sigmoid_has_deriv)
  qed
  then show "deriv sigmoid x < 1/4"
    by (simp add: sigmoid_deriv_0)
qed

corollary sigmoid_derivative_range:
  "0 < deriv sigmoid x \<and> deriv sigmoid x \<le> 1/4"
  by (smt (verit, best) sigmoid_deriv_0 sigmoid_derivative_upper_bound sigmoid_positive_derivative)

subsection \<open>Sigmoidal and Heaviside Step Functions\<close>

definition sigmoidal :: "(real \<Rightarrow> real) \<Rightarrow> bool" where
  "sigmoidal f \<equiv> (f \<longlongrightarrow> 1) at_top \<and> (f \<longlongrightarrow> 0) at_bot"

lemma sigmoid_is_sigmoidal: "sigmoidal sigmoid"
  unfolding sigmoidal_def
  by (simp add: lim_sigmoid_infinity lim_sigmoid_minus_infinity)

definition heaviside :: "real \<Rightarrow> real" where
  "heaviside x = (if x < 0 then 0 else 1)"

lemma heaviside_right: "x \<ge> 0 \<Longrightarrow> heaviside x = 1"
  by (simp add: heaviside_def)

lemma heaviside_left: "x < 0 \<Longrightarrow> heaviside x = 0"
  by (simp add: heaviside_def)

lemma heaviside_mono: "x < y \<Longrightarrow> heaviside x \<le> heaviside y"
  by (simp add: heaviside_def)

lemma heaviside_limit_neg_infinity:
  "(heaviside \<longlongrightarrow> 0) at_bot"
  by(rule tendsto_eventually, subst eventually_at_bot_dense, meson heaviside_def)

lemma heaviside_limit_pos_infinity:
  "(heaviside \<longlongrightarrow> 1) at_top"
  by(rule tendsto_eventually, subst eventually_at_top_dense, meson heaviside_def order.asym) 

lemma heaviside_is_sigmoidal: "sigmoidal heaviside"
  by (simp add: heaviside_limit_neg_infinity heaviside_limit_pos_infinity sigmoidal_def)

subsection \<open>Uniform Approximation by Sigmoids\<close>
lemma sigmoidal_uniform_approximation:  
  assumes "sigmoidal \<sigma>"
  assumes "(\<epsilon> :: real) > 0" and "(h :: real) > 0"    
  shows "\<exists>(\<omega>::real)>0. \<forall>w\<ge>\<omega>. \<forall>k<length (xs :: real list).
           (\<forall>x. x - xs!k \<ge> h   \<longrightarrow> \<bar>\<sigma> (w * (x - xs!k)) - 1\<bar> < \<epsilon>) \<and>
           (\<forall>x. x - xs!k \<le> -h  \<longrightarrow> \<bar>\<sigma> (w * (x - xs!k))\<bar> < \<epsilon>)"
proof -
  text \<open>By the sigmoidal assumption, we extract the limits
    \[
      \lim_{x\to +\infty} \sigma(x) = 1
      \quad\text{(limit at\_top)}
      \quad\text{and}\quad
      \lim_{x\to -\infty} \sigma(x) = 0
      \quad\text{(limit at\_bot)}.
    \]\<close>

  have lim_at_top: "(\<sigma> \<longlongrightarrow> 1) at_top"
    using assms(1) unfolding sigmoidal_def by simp
  then obtain Ntop where Ntop_def: "\<forall>x \<ge> Ntop. \<bar>\<sigma> x - 1\<bar> < \<epsilon>"
    using assms(2) tendsto_at_top_epsilon_def by blast

  have lim_at_bot: "(\<sigma> \<longlongrightarrow> 0) at_bot"
    using assms(1) unfolding sigmoidal_def by simp
  then obtain Nbot where Nbot_def: "\<forall>x \<le> Nbot. \<bar>\<sigma> x\<bar> < \<epsilon>"
    using assms(2) tendsto_at_bot_epsilon_def by fastforce

  text \<open> Define \(\omega\) to control the approximation.\<close>

  obtain  \<omega> where \<omega>_def: "\<omega> = max (max 1 (Ntop / h)) (-Nbot / h)"
    by blast
  then have \<omega>_pos: "0 < \<omega>" using assms(2) by simp

  text \<open> Show that \(\omega\) satisfies the required property.\<close>
  show ?thesis
  proof (intro exI[where x = \<omega>] allI impI conjI insert \<omega>_pos)
    fix w :: real and k :: nat and x :: real
    assume w_ge_\<omega>: "\<omega> \<le> w"
    assume k_bound: "k < length xs"

    text \<open> Case 1: \(x - xs!k \ge h\).\<close>

    have "w * h \<ge> Ntop"
      using \<omega>_def assms(3) pos_divide_le_eq w_ge_\<omega> by auto

    then show "x - xs!k \<ge> h \<Longrightarrow> \<bar>\<sigma> (w * (x - xs!k)) - 1\<bar> < \<epsilon>"
      using Ntop_def
      by (smt (verit) \<omega>_pos mult_less_cancel_left w_ge_\<omega>)

    text \<open> Case 2: \(x - xs!k \le -\,h\).\<close>

    have "-w * h \<le> Nbot"
      using \<omega>_def assms(3) pos_divide_le_eq w_ge_\<omega>
      by (smt (verit, ccfv_SIG) mult_minus_left) 
    then show "x - xs!k \<le> -h \<Longrightarrow> \<bar>\<sigma> (w * (x - xs!k))\<bar> < \<epsilon>"
      using Nbot_def
      by (smt (verit, best) \<omega>_pos minus_mult_minus mult_less_cancel_left w_ge_\<omega>)
  qed
qed

end