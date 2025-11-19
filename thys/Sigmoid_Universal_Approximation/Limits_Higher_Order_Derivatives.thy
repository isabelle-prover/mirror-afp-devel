section \<open>Limits and Higher Order Derivatives\<close>

theory Limits_Higher_Order_Derivatives
  imports "HOL-Analysis.Analysis" 
begin


subsection \<open>\(\varepsilon\)--\(\delta\) Characterizations of Limits and Continuity\<close>

lemma tendsto_at_top_epsilon_def:
  "(f \<longlongrightarrow> L) at_top = (\<forall> \<epsilon> > 0. \<exists>N. \<forall>x \<ge> N. \<bar>(f (x::real)::real) - L\<bar> < \<epsilon>)"
    by (simp add: Zfun_def tendsto_Zfun_iff eventually_at_top_linorder)

lemma tendsto_at_bot_epsilon_def:
  "(f \<longlongrightarrow> L) at_bot = (\<forall> \<epsilon> > 0. \<exists>N. \<forall>x \<le> N. \<bar>(f (x::real)::real) - L\<bar> < \<epsilon>)"
    by (simp add: Zfun_def tendsto_Zfun_iff eventually_at_bot_linorder)

lemma tendsto_inf_at_top_epsilon_def:
  "(g \<longlongrightarrow> \<infinity>) at_top = (\<forall> \<epsilon> > 0. \<exists>N. \<forall>x \<ge> N. (g (x::real)::real) > \<epsilon>)"
  by (subst tendsto_PInfty', subst Filter.eventually_at_top_linorder, simp)
  
lemma tendsto_inf_at_bot_epsilon_def:
  "(g \<longlongrightarrow> \<infinity>) at_bot = (\<forall> \<epsilon> > 0. \<exists>N. \<forall>x \<le> N. (g (x::real)::real) > \<epsilon>)"
  by (subst tendsto_PInfty', subst Filter.eventually_at_bot_linorder, simp)

lemma tendsto_minus_inf_at_top_epsilon_def:
  "(g \<longlongrightarrow> -\<infinity>) at_top = (\<forall> \<epsilon> < 0. \<exists>N. \<forall>x \<ge> N. (g (x::real)::real) < \<epsilon>)"
  by(subst tendsto_MInfty', subst Filter.eventually_at_top_linorder, simp)

lemma tendsto_minus_inf_at_bot_epsilon_def:
  "(g \<longlongrightarrow> -\<infinity>) at_bot = (\<forall> \<epsilon> < 0. \<exists>N. \<forall>x \<le> N. (g (x::real)::real) < \<epsilon>)"
  by (subst tendsto_MInfty', subst Filter.eventually_at_bot_linorder, simp)

lemma tendsto_at_x_epsilon_def:
  fixes f :: "real \<Rightarrow> real" and L :: real and x :: real
  shows "(f \<longlongrightarrow> L) (at x) = (\<forall>\<epsilon> > 0. \<exists>\<delta> > 0. \<forall>y. (y \<noteq> x \<and> \<bar>y - x\<bar> < \<delta>) \<longrightarrow> \<bar>f y - L\<bar> < \<epsilon>)"
  unfolding tendsto_def
proof (subst eventually_at, safe)
  text \<open> --- First Direction ---
  We show that the filter definition implies the \(\varepsilon\)--\(\delta\) formulation.\<close>
  fix \<epsilon> :: real
  assume lim_neigh: "\<forall>S. open S \<longrightarrow> L \<in> S \<longrightarrow> (\<exists>d>0. \<forall>xa\<in>UNIV. xa \<noteq> x \<and> dist xa x < d \<longrightarrow> f xa \<in> S)"
  assume \<epsilon>_pos: "0 < \<epsilon>"
  show "\<exists>\<delta>>0. \<forall>y. y \<noteq> x \<and> \<bar>y - x\<bar> < \<delta> \<longrightarrow> \<bar>f y - L\<bar> < \<epsilon>"
  proof -
    text \<open>Choose \(S\) as the open ball around \(L\) with radius \(\varepsilon\).\<close>

    have "open (ball L \<epsilon>)" 
      by simp 
    text \<open>Confirm that \(L\) lies in the ball.\<close>
    moreover have "L \<in> ball L \<epsilon>"
      unfolding ball_def by (simp add: \<epsilon>_pos)
    text \<open>By applying lim\_neigh to the ball, we obtain a suitable \(\delta\).\<close>
    ultimately obtain \<delta> where d_pos: "\<delta> > 0" 
      and \<delta>_prop: "\<forall>y. y \<noteq> x \<and> dist y x < \<delta> \<longrightarrow> f y \<in> ball L \<epsilon>"
      by (meson UNIV_I lim_neigh)
    text \<open>Since \(f(y)\in \mathrm{ball}(L,\varepsilon)\) means \(\lvert f(y)-L\rvert<\varepsilon\), 
          we deduce the \(\varepsilon\)–\(\delta\) condition.\<close>
    hence "\<forall>y. y \<noteq> x \<and> \<bar>y - x\<bar> < \<delta> \<longrightarrow> \<bar>f y - L\<bar> < \<epsilon>"
      by (auto simp: ball_def dist_norm)
    thus ?thesis
      using d_pos by blast
  qed
next
  text \<open>--- Second Direction ---
     We show that the \(\varepsilon\)--\(\delta\) formulation implies the filter definition.\<close>
  fix S :: "real set"
  assume eps_delta: "\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>y. (y \<noteq> x \<and> \<bar>y - x\<bar> < \<delta>) \<longrightarrow> \<bar>f y - L\<bar> < \<epsilon>"
  and S_open: "open S"
  and L_in_S: "L \<in> S"
  text \<open> Since \(S\) is open and contains \(L\), there exists an \(\varepsilon\)-ball
  around \(L\) contained in \(S\).\<close>

  from S_open L_in_S obtain \<epsilon> where \<epsilon>_pos: "\<epsilon> > 0" and ball_sub: "ball L \<epsilon> \<subseteq> S"
    by (meson openE)
  text \<open>Applying the \(\varepsilon\)--\(\delta\) assumption for this particular \(\varepsilon\)
  yields a \(\delta > 0\) such that for all \(y\), if \(y \neq x\) and
  \(\lvert y - x\rvert < \delta\) then \(\lvert f(y) - L\rvert < \varepsilon\).\<close>

  from eps_delta obtain \<delta> where \<delta>_pos: "\<delta> > 0" 
    and \<delta>_prop: "\<forall>y. (y \<noteq> x \<and> \<bar>y - x\<bar> < \<delta>) \<longrightarrow> \<bar>f y - L\<bar> < \<epsilon>"
    using \<epsilon>_pos by blast
  text \<open> Notice that \(\lvert f(y) - L\rvert < \varepsilon\) is equivalent to
  \(f(y) \in \mathrm{ball}\,L\,\varepsilon\).\<close>

  have "\<forall>y. (y \<noteq> x \<and> dist y x < \<delta>) \<longrightarrow> f y \<in> ball L \<epsilon>"
    using \<delta>_prop dist_real_def by fastforce
  text \<open>Since \(\mathrm{ball}(L,\varepsilon) \subseteq S\),
  for all \(y\) with \(y \neq x\) and \(\mathrm{dist}\,y\,x < \delta\), we have \(f\,y \in S\).\<close>
  hence "\<forall>y. (y \<noteq> x \<and> dist y x < \<delta>) \<longrightarrow> f y \<in> S"
    using ball_sub by blast
  text \<open>This gives exactly the existence of some \(d\) (namely \(\delta\)) satisfying the filter condition.\<close>

  thus "\<exists>d>0. \<forall>y\<in>UNIV. (y \<noteq> x \<and> dist y x < d) \<longrightarrow> f y \<in> S"
    using \<delta>_pos by blast
qed

lemma continuous_at_eps_delta:
  fixes g :: "real \<Rightarrow> real" and y :: real
  shows "continuous (at y) g = (\<forall>\<epsilon> > 0. \<exists>\<delta> > 0. \<forall>x. \<bar>x - y\<bar> < \<delta> \<longrightarrow> \<bar>g x - g y\<bar> < \<epsilon>)"
proof -
  have "continuous (at y) g = (\<forall>\<epsilon> > 0. \<exists>\<delta> > 0. \<forall>x. (x \<noteq> y \<and> \<bar>x - y\<bar> < \<delta>) \<longrightarrow> \<bar>g x - g y\<bar> < \<epsilon>)"
    by (simp add: isCont_def tendsto_at_x_epsilon_def)
  also have "... = (\<forall>\<epsilon> > 0. \<exists>\<delta> > 0. \<forall>x. \<bar>x - y\<bar> < \<delta> \<longrightarrow> \<bar>g x - g y\<bar> < \<epsilon>)"
    by (metis abs_eq_0 diff_self)
  finally show ?thesis.
qed

lemma tendsto_divide_approaches_const:
  fixes f g :: "real \<Rightarrow> real"
  assumes f_lim:"((\<lambda>x. f (x::real)) \<longlongrightarrow> c) at_top"
      and g_lim: "((\<lambda>x. g (x::real)) \<longlongrightarrow> \<infinity>) at_top"
    shows "((\<lambda>x. f (x::real) / g x) \<longlongrightarrow> 0) at_top"
proof(subst tendsto_at_top_epsilon_def, clarify)
  fix \<epsilon> :: real
  assume \<epsilon>_pos: "0 < \<epsilon>"

  obtain M where M_def: "M = abs c + 1" and M_gt_0: "M > 0"
    by simp

  obtain N1 where N1_def: "\<forall>x\<ge>N1. abs (f x - c) < 1"
    using f_lim tendsto_at_top_epsilon_def zero_less_one by blast 

  have f_bound: "\<forall>x\<ge>N1. abs (f x) < M"
    using M_def N1_def by fastforce

  have M_over_\<epsilon>_gt_0: "M / \<epsilon> > 0"
    by (simp add: M_gt_0 \<epsilon>_pos)

  then obtain N2 where N2_def: "\<forall>x\<ge>N2. g x > M / \<epsilon>"
    using g_lim tendsto_inf_at_top_epsilon_def by blast

  obtain N where "N = max N1 N2" and N_ge_N1: "N \<ge> N1" and N_ge_N2: "N \<ge> N2"
    by auto 

  show "\<exists>N::real. \<forall>x\<ge>N. \<bar>f x / g x - 0\<bar> < \<epsilon>"
  proof(intro exI [where x=N], clarify)
    fix x :: real
    assume x_ge_N: " N \<le> x"

    have f_bound_x: "\<bar>f x\<bar> < M"
      using N_ge_N1 f_bound x_ge_N by auto

    have g_bound_x: "g x > M / \<epsilon>"
      using N2_def N_ge_N2 x_ge_N by auto 

    have "\<bar>f x / g x\<bar> = \<bar>f x\<bar> / \<bar>g x\<bar>"
      using abs_divide by blast
    also have "... < M /  \<bar>g x\<bar>"
      using M_over_\<epsilon>_gt_0 divide_strict_right_mono f_bound_x g_bound_x by force
    also have  "... < \<epsilon>"
      by (metis  M_over_\<epsilon>_gt_0 \<epsilon>_pos abs_real_def g_bound_x mult.commute order_less_irrefl order_less_trans pos_divide_less_eq)
    finally show "\<bar>f x / g x - 0\<bar> < \<epsilon>"
      by linarith
  qed      
qed

lemma tendsto_divide_approaches_const_at_bot:
  fixes f g :: "real \<Rightarrow> real"
  assumes f_lim: "((\<lambda>x. f (x::real)) \<longlongrightarrow> c) at_bot"
      and g_lim: "((\<lambda>x. g (x::real)) \<longlongrightarrow> \<infinity>) at_bot"
    shows "((\<lambda>x. f (x::real) / g x) \<longlongrightarrow> 0) at_bot"
proof(subst tendsto_at_bot_epsilon_def, clarify)
  fix \<epsilon> :: real
  assume \<epsilon>_pos: "0 < \<epsilon>"

  obtain M where M_def: "M = abs c + 1" and M_gt_0: "M > 0"
    by simp

  obtain N1 where N1_def: "\<forall>x\<le>N1. abs (f x - c) < 1"
    using f_lim tendsto_at_bot_epsilon_def zero_less_one by blast 

  have f_bound: "\<forall>x\<le>N1. abs (f x) < M"
    using M_def N1_def by fastforce

  have M_over_\<epsilon>_gt_0: "M / \<epsilon> > 0"
    by (simp add: M_gt_0 \<epsilon>_pos)

  then obtain N2 where N2_def: "\<forall>x\<le>N2. g x > M / \<epsilon>"
    using g_lim tendsto_inf_at_bot_epsilon_def by blast

  obtain N where "N = min N1 N2" and N_le_N1: "N \<le> N1" and N_le_N2: "N \<le> N2"
    by auto 
    
  show "\<exists>N::real. \<forall>x\<le>N. \<bar>f x / g x - 0\<bar> < \<epsilon>"
  proof(intro exI [where x=N], clarify)
    fix x :: real
    assume x_le_N: "x \<le> N"

    have f_bound_x: "\<bar>f x\<bar> < M"
      using N_le_N1 f_bound x_le_N by auto

    have g_bound_x: "g x > M / \<epsilon>"
      using N2_def N_le_N2 x_le_N by auto 

    have "\<bar>f x / g x\<bar> = \<bar>f x\<bar> / \<bar>g x\<bar>"
      using abs_divide by blast
    also have "... < M /  \<bar>g x\<bar>"
      using M_over_\<epsilon>_gt_0 divide_strict_right_mono f_bound_x g_bound_x by force
    also have  "... < \<epsilon>"
      by (metis  M_over_\<epsilon>_gt_0 \<epsilon>_pos abs_real_def g_bound_x mult.commute order_less_irrefl order_less_trans pos_divide_less_eq)
    finally show "\<bar>f x / g x - 0\<bar> < \<epsilon>"
      by linarith
  qed      
qed

lemma equal_limits_diff_zero_at_top:
  assumes f_lim: "(f \<longlongrightarrow> (L1::real)) at_top"
  assumes g_lim: "(g \<longlongrightarrow> (L2::real)) at_top"
  shows "((f - g) \<longlongrightarrow> (L1 - L2)) at_top"
proof -
  have "((\<lambda>x. f x - g x) \<longlongrightarrow> L1 - L2) at_top"
    by (rule tendsto_diff, rule f_lim, rule g_lim)
  then show ?thesis 
    by (simp add: fun_diff_def)
qed

lemma equal_limits_diff_zero_at_bot:
  assumes f_lim: "(f \<longlongrightarrow> (L1::real)) at_bot"
  assumes g_lim: "(g \<longlongrightarrow> (L2::real)) at_bot"
  shows "((f - g) \<longlongrightarrow> (L1 - L2)) at_bot"
proof -
  have "((\<lambda>x. f x - g x) \<longlongrightarrow> L1 - L2) at_bot"
    by (rule tendsto_diff, rule f_lim, rule g_lim)
  then show ?thesis 
    by (simp add: fun_diff_def)
qed


subsection \<open>Nth Order Derivatives and $C^k(U)$ Smoothness\<close>
fun Nth_derivative :: "nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> real)" where
  "Nth_derivative 0 f = f " |
  "Nth_derivative (Suc n) f  = deriv (Nth_derivative n f)"

lemma first_derivative_alt_def:
  "Nth_derivative 1 f = deriv f"
  by simp

lemma second_derivative_alt_def:
  "Nth_derivative 2 f  = deriv (deriv f)"
  by (simp add: numeral_2_eq_2)

lemma limit_def_nth_deriv:
  fixes f :: "real \<Rightarrow> real" and a :: real and n :: nat
  assumes n_pos: "n > 0"
      and D_last: "DERIV (Nth_derivative (n - 1) f) a :> Nth_derivative n f a"
  shows
    "((\<lambda>x. (Nth_derivative (n - 1) f x - Nth_derivative (n - 1) f a) / (x - a))
       \<longlongrightarrow> Nth_derivative n f a) (at a)"
  using D_last has_field_derivativeD by blast

definition C_k_on :: "nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real set \<Rightarrow> bool" where
  "C_k_on k f U \<equiv> 
     (if k = 0 then (open U \<and> continuous_on U f)
      else (open U \<and> (\<forall>n < k. (Nth_derivative n f) differentiable_on U 
                         \<and> continuous_on U (Nth_derivative (Suc n) f))))"

lemma C0_on_def:
  "C_k_on 0 f U \<longleftrightarrow> (open U \<and> continuous_on U f)"
  by (simp add: C_k_on_def)

lemma C1_cont_diff:
  assumes "C_k_on 1 f U"
  shows "f differentiable_on U \<and> continuous_on U (deriv f) \<and> 
         (\<forall> y  \<in> U. (f has_real_derivative (deriv f) y) (at y))"
  using C_k_on_def DERIV_deriv_iff_real_differentiable assms at_within_open differentiable_on_def by fastforce

lemma C2_cont_diff:
  fixes f :: "real \<Rightarrow> real" and U :: "real set"
  assumes "C_k_on 2 f U"
  shows "f differentiable_on U \<and> continuous_on U (deriv f) \<and> 
         (\<forall>y \<in> U. (f has_real_derivative (deriv f) y) (at y)) \<and>
         deriv f differentiable_on U \<and> continuous_on U (deriv (deriv f)) \<and>
         (\<forall>y \<in> U. (deriv f has_real_derivative (deriv (deriv f)) y) (at y))"
  by (smt (verit, best) C1_cont_diff C_k_on_def Nth_derivative.simps(1,2) One_nat_def assms less_2_cases_iff less_numeral_extra(1) nat_1_add_1 order.asym pos_add_strict)

lemma C2_on_open_U_def2:
  fixes f :: "real \<Rightarrow> real"
  assumes openU : "open U"
      and diff_f : "f differentiable_on U"
      and diff_df: "deriv f differentiable_on U"
      and cont_d2f: "continuous_on U (deriv (deriv f))"
  shows "C_k_on 2 f U"
  by (simp add: C_k_on_def cont_d2f diff_df diff_f differentiable_imp_continuous_on less_2_cases_iff openU)

lemma C_k_on_subset:
  assumes "C_k_on k f U"
  assumes open_subset: "open S \<and> S \<subset> U"  
  shows "C_k_on k f S"
  using assms
  by (smt (verit) C_k_on_def continuous_on_subset differentiable_on_eq_differentiable_at dual_order.strict_implies_order subset_eq)


definition smooth_on :: "(real \<Rightarrow> real) \<Rightarrow> real set \<Rightarrow> bool" where
  "smooth_on f U \<equiv> \<forall>k. C_k_on k f U"

end