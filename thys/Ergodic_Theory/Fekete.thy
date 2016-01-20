(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

theory Fekete
imports Complex_Main Topological_Spaces "~~/src/HOL/Multivariate_Analysis/Operator_Norm" "~~/src/HOL/Multivariate_Analysis/Extended_Real_Limits"
   SG_Library_Complement

begin

section {*Subadditive and submultiplicative sequences*}

text {*A real sequence is subadditive if $u_{n+m} \leq u_n+u_m$. This implies the
convergence of $u_n/n$ to $Inf\{u_n/n\} \in [-\infty, +\infty)$, a useful result known
as Fekete lemma. We prove it below.

Taking logarithms, the same result applies to submultiplicative sequences. We illustrate
it with the definition of the spectral radius as the limit of $\|x^n\|^{1/n}$, the
convergence following from Fekete lemma.*}


subsection {*Subadditive sequences*}

definition subadditive::"(nat\<Rightarrow>real) \<Rightarrow> bool"
  where "subadditive u= (\<forall>m n. u (m+n) \<le> u m + u n)"

definition eventually_subadditive::"(nat\<Rightarrow>real) \<Rightarrow> nat \<Rightarrow> bool"
  where "eventually_subadditive u N0 = (\<forall>m>N0. \<forall>n>N0. u (m+n) \<le> u m + u n)"

lemma subadditive_imp_eventually_subadditive:
  assumes "subadditive u"
  shows "eventually_subadditive u 0"
using assms unfolding subadditive_def eventually_subadditive_def by auto

lemma eventually_subadditive_epsilon:
  assumes "eventually_subadditive u N0"
  shows "\<forall>\<epsilon>>0. \<forall>n>N0. \<exists>N>N0. \<forall>m\<ge>N. u m/m < u n/n + \<epsilon>"
proof (intro allI impI)
  have ineq_rec: "u(a*n+r) \<le> a * u n + u r"  if "n>N0" "r>N0" for a n r
  proof (induct a)
    case (Suc a)
    have "a*n+r>N0" using `r>N0` by simp
    have "u((Suc a)*n+r) = u(a*n+r+n)" by (simp add: add.commute add.left_commute)
    also have "... \<le> u(a*n+r)+u n" using assms `n>N0` `a*n+r>N0` eventually_subadditive_def by blast
    also have "... \<le> a*u n + u r + u n" by (simp add: Suc.hyps)
    also have "... = (Suc a) * u n + u r" by (simp add: distrib_left mult.commute)
    finally show ?case by simp
  qed (simp)

  fix \<epsilon>::real and n::nat
  assume "\<epsilon>>0" "n>N0"
  have "n>0" using `n>N0` by simp
  then have "real n>0" by simp

  let ?V="{abs(u i) |i. i\<le>2*n}"
  have "bdd_above ?V" by simp
  then obtain C where C_def: "\<And>t. t\<in>?V \<Longrightarrow> t\<le>C" by (meson bdd_above_def)

  have ineq_all_m: "u m/m \<le> u n/n + 3*C/m" if "m\<ge>n" for m
  proof -
    have "real m>0" using `m\<ge>n` `real n>0` by auto

    obtain a0 r0 where "r0<n" "m=a0*n+r0"
      by (metis `0 < n` add.commute mod_eqD mod_less_divisor)
    def a \<equiv> "a0-1"
    def r \<equiv> "r0+n"
    have "r<2*n" unfolding r_def by (simp add:`r0<n`)
    have "r\<ge>n" unfolding r_def by simp
    have "a0>0" using `m = a0*n + r0` `n \<le> m` `r0 < n` not_le by fastforce
    hence "m=a*n+r" using a_def r_def `m=a0*n+r0` mult_eq_if by auto
    hence real_eq:"real n*a - m = -r" by simp

    have "r>N0" using `r\<ge>n` `n>N0` by simp
    hence "u m \<le> a*u n + u r" using ineq_rec `m=a*n+r` `n>N0`  by simp
    hence "n*u m \<le> n*(a*u n + u r)" using `real n>0` by simp
    hence "n*u m \<le>  n*a*u n + n*u r" by (simp add: distrib_left)
    hence "n*u m - m*u n \<le> (n*a-real m)*u n + n*u r"by (simp add: left_diff_distrib)
    hence *: "n*u m - m*u n \<le> -r*u n + n*u r" using real_eq by auto

    have "-r*u n \<le> abs(r*u n)" by linarith
    also have "... \<le> r*abs(u n)" by (simp add: abs_mult)
    also have "... \<le> n*2*abs(u n)" using `r < 2 * n`  less_eq_real_def by auto
    finally have "-r*u n \<le> n*2*abs(u n)".
    moreover have "n*u r \<le> n*abs(u r)" by (simp add: ordered_comm_semiring_class.comm_mult_left_mono)
    hence **: "-r*u n + n*u r \<le> n*2*abs(u n) + n*abs(u r)" using add_mono calculation by blast

    have "n \<le> 2*n" by auto
    hence "abs(u n) \<le> C" using C_def by blast
    moreover have "abs(u r) \<le> C" using `r<2*n` C_def less_imp_le by auto
    ultimately have "2*abs(u n) + abs(u r) \<le> 3*C" by linarith
    hence "n*(2*abs(u n) + abs(u r)) \<le> 3*C*n" using `real n>0` by simp
    hence "n*2*abs(u n) + n*abs(u r) \<le> 3*C*n" by (simp add: distrib_left)

    then have "n*u m - m*u n \<le> 3*C*n" using * ** by linarith
    thus "u m/m \<le> u n/n + 3*C/m" using `0 < real n` `0 < real m` by (simp add: divide_simps mult.commute)
  qed

  obtain M::nat where "M \<ge> 3*C/\<epsilon>" using real_nat_ceiling_ge by auto
  def N \<equiv> "M+n+N0+1"
  hence "N>M" by simp
  hence "N>3*C/ \<epsilon>" using `3 * C / \<epsilon> \<le> real M` by linarith
  have "N\<ge>n" using N_def by simp
  have "N>N0" using N_def by simp
  {
    fix m::nat
    assume "m\<ge>N"
    have "3*C < \<epsilon>*N" by (metis `0 < \<epsilon>` `3 * C / \<epsilon> < real N` linordered_field_class.sign_simps(24) pos_divide_less_eq)
    moreover have "\<epsilon>*N \<le> \<epsilon>*m" using `0 < \<epsilon>` `N \<le> m` by auto
    ultimately have "3*C < \<epsilon>*m" by simp
    then have "3*C/m < \<epsilon>" by (simp add: `0 < \<epsilon>` divide_simps)
    moreover have "u m/m \<le> u n/n + 3*C/m" using ineq_all_m `n \<le> N` `N \<le> m` by auto
    ultimately have "u m/m < u n/n + \<epsilon>" by simp
  }
  then show "\<exists>N>N0. \<forall>m\<ge>N. u m/m < u n/n + \<epsilon>" using `N0 < N` by blast
qed

lemma subadditive_converges_ereal':
  assumes "eventually_subadditive u N0"
  shows "(\<lambda>m. ereal(u m/m)) \<longlonglongrightarrow> Inf {ereal(u n/n) | n. n>N0}"
proof -
  have main_ineq: "\<forall>e>0. \<forall>n>N0. \<exists>N>N0. \<forall>m\<ge>N. u m/m < u n/n + e"
    using assms(1) eventually_subadditive_epsilon by simp

  def v \<equiv> "(\<lambda>m. ereal(u m/m))"
  def V \<equiv> "{v n | n. n>N0}"
  def l \<equiv> "Inf V"

  have "\<And>t. t\<in>V \<Longrightarrow> t\<ge>l" by (simp add: Inf_lower l_def)
  then have "\<And>n. n>N0 \<Longrightarrow> v n \<ge> l" using V_def by blast
  then have lower: "eventually (\<lambda>n. a<v n) sequentially" if "a<l" for a
    by (meson that dual_order.strict_trans1 eventually_at_top_dense)

  have upper: "eventually (\<lambda>n. a > v n) sequentially" if "a>l" for a
  proof -
    obtain t where "t\<in>V" "t<a" by (metis `a>l` Inf_greatest l_def not_le)
    then obtain e::real where "e>0" "t+e < a" by (meson ereal_le_epsilon2 leD le_less_linear)
    obtain n where "n>N0" "t=u n/n" using V_def v_def `t \<in> V` by blast
    then have "u n/n + e < a" using `t+e < a` by simp
    obtain N where "\<forall>m\<ge>N.  u m/m < u n/n + e" using main_ineq `0 < e` `N0 < n` by blast
    then have "\<forall>m\<ge>N. u m/m < a" using `u n/n + e < a` less_ereal.simps(1) less_trans by blast
    then have "\<forall>m\<ge>N. v m<a" using v_def by blast
    then show ?thesis using eventually_at_top_linorder by auto
  qed
  from lower and upper show ?thesis unfolding V_def l_def v_def by (simp add: order_tendsto_iff)
qed

lemma subadditive_converges_ereal:
  assumes "subadditive u"
  shows "(\<lambda>m. ereal(u m/m)) \<longlonglongrightarrow> Inf {ereal(u n/n) | n. n>0}"
by (rule subadditive_converges_ereal'[OF subadditive_imp_eventually_subadditive[OF assms]])

lemma subadditive_converges_bounded':
  assumes "eventually_subadditive u N0"
          "bdd_below {u n/n | n. n>N0}"
  shows "(\<lambda>n. u n/n) \<longlonglongrightarrow> Inf {u n/n | n. n>N0}"
proof-
  have *: "(\<lambda>n. ereal(u n /n)) \<longlonglongrightarrow> Inf {ereal(u n/n)|n. n > N0}"
    by (simp add: assms(1) subadditive_converges_ereal')
  def V \<equiv> "{u n/n | n. n>N0}"
  have a: "bdd_below V" "V\<noteq>{}" by (auto simp add: V_def assms(2))
  have "Inf {ereal(t)| t. t\<in>V} = ereal(Inf V)" by (subst ereal_Inf'[OF a], simp add: Setcompr_eq_image)
  moreover have "{ereal(t)| t. t\<in>V} =  {ereal(u n/n)|n. n > N0}" using V_def by blast
  ultimately have "Inf {ereal(u n/n)|n. n > N0} = ereal(Inf {u n/n |n. n > N0})" using V_def by auto
  then have "(\<lambda>n. ereal(u n /n)) \<longlonglongrightarrow> ereal(Inf  {u n/n | n. n>N0})" using * by auto
  then show ?thesis by simp
qed

lemma subadditive_converges_bounded:
  assumes "subadditive u"
          "bdd_below {u n/n | n. n>0}"
  shows "(\<lambda>n. u n/n) \<longlonglongrightarrow> Inf {u n/n | n. n>0}"
by (rule subadditive_converges_bounded'[OF subadditive_imp_eventually_subadditive[OF assms(1)] assms(2)])

lemma subadditive_converges_unbounded':
  assumes "eventually_subadditive u N0"
          "\<not> (bdd_below {u n/n | n. n>N0})"
  shows "(\<lambda>n. ereal(u n/n)) \<longlonglongrightarrow> -\<infinity>"
proof -
  have *: "(\<lambda>n. ereal(u n /n)) \<longlonglongrightarrow> Inf {ereal(u n/n)|n. n > N0}"
    by (simp add: assms(1) subadditive_converges_ereal')
  def V \<equiv> "{u n/n | n. n>N0}"
  hence "\<not> bdd_below V" using assms by simp
  have "Inf {ereal(t) | t. t\<in>V} = -\<infinity>"
    by (rule ereal_bot, metis (mono_tags, lifting) `\<not> bdd_below V` bdd_below_def
    leI Inf_lower2 ereal_less_eq(3) le_less mem_Collect_eq)
  moreover have "{ereal(t)| t. t\<in>V} =  {ereal(u n/n)|n. n > N0}" using V_def by blast
  ultimately have "Inf {ereal(u n/n)|n. n > N0} = -\<infinity>" by auto
  then show ?thesis using * by simp
qed

lemma subadditive_converges_unbounded:
  assumes "subadditive u"
          "\<not> (bdd_below {u n/n | n. n>0})"
  shows "(\<lambda>n. ereal(u n/n)) \<longlonglongrightarrow> -\<infinity>"
by (rule subadditive_converges_unbounded'[OF subadditive_imp_eventually_subadditive[OF assms(1)] assms(2)])

subsection {*Submultiplicative sequences, application to the spectral radius*}

lemma submultiplicative_converges:
  fixes u::"nat\<Rightarrow>real"
  assumes "\<And>n. u n \<ge> 0"
          "\<And>m n. u (m+n) \<le> u m * u n"
  shows "(\<lambda>n. root n (u n))\<longlonglongrightarrow> Inf {root n (u n) | n. n>0}"
proof -
  def v \<equiv> "\<lambda> n. root n (u n)"
  def V \<equiv> "{v n | n. n>0}"
  then have "V \<noteq> {}" by blast
  have "\<And>t. t\<in>V \<Longrightarrow> t \<ge> 0" using V_def v_def assms(1) by auto
  then have "Inf V \<ge> 0" by (simp add: `V \<noteq> {}` cInf_greatest)
  then have "bdd_below V" by (meson `\<And>t. t \<in> V \<Longrightarrow> 0 \<le> t` bdd_below_def)

  show ?thesis
  proof cases
    assume "\<exists>n. u n = 0"
    then obtain n where "u n = 0" by auto
    then have "\<And>m. m\<ge>n \<Longrightarrow> u m = 0" by (metis antisym_conv assms(1) assms(2) le_Suc_ex mult_zero_left)
    then have "\<And>m. m\<ge>n \<Longrightarrow> v m = 0" using v_def by simp
    then have "v \<longlonglongrightarrow> 0" using tendsto_explicit by force

    obtain m where "m>0" "v m=0" using `\<And>m. n \<le> m \<Longrightarrow> v m = 0` le_less_linear by blast
    have "v m \<in> V" using V_def `0 < m` by blast
    then have "Inf V \<le> 0" by (simp add: `bdd_below V` `v m = 0` cInf_lower)
    then have "Inf V = 0" using `0 \<le> Inf V` by auto

    then show ?thesis using V_def v_def `v \<longlonglongrightarrow> 0` by auto
  next
    assume "\<not> (\<exists>n. u n = 0)"
    then have "\<And>n. u n > 0" by (metis assms(1) less_eq_real_def)
    def w \<equiv> "(\<lambda>n. ln (u n))"
    have express_vn: "v n = exp(w n/n)" if "n>0" for n
    proof -
      have "(exp(w n/n))^n = exp(n*(w n/n))" using exp_real_of_nat_mult by presburger
      also have "... = exp(w n)" by (simp add: `0 < n`)
      also have "... = u n" by (simp add: `\<And>n. 0 < u n` w_def)
      finally have "exp(w n/n) = root n (u n)" by (metis `0 < n` exp_ge_zero real_root_power_cancel)
      then show ?thesis unfolding v_def by simp
    qed

    have "eventually_subadditive w 0" unfolding eventually_subadditive_def
    proof (auto)
      fix m n
      have "w (m+n) = ln (u (m+n))" by (simp add: w_def)
      also have "... \<le> ln(u m * u n)" by (simp add: `\<And>n. 0 < u n` assms(2))
      also have "... = ln(u m) + ln(u n)" by (simp add: `\<And>n. 0 < u n` ln_mult)
      also have "... = w m + w n" by (simp add: w_def)
      finally show "w (m+n) \<le> w m + w n".
    qed
    then have main_ineq: "\<forall>e>0. \<forall>n>0. \<exists>N>0. \<forall>m\<ge>N. w m/m < w n/n + e"
      using eventually_subadditive_epsilon by blast

    def l \<equiv> "Inf V"
    then have "\<And>n. n>0 \<Longrightarrow> v n\<ge>l" using V_def by (metis (mono_tags, lifting) `bdd_below V` cInf_lower mem_Collect_eq)
    then have lower: "\<And>a. a < l \<Longrightarrow> eventually (\<lambda>n. a < v n) sequentially" by (meson dual_order.strict_trans1 eventually_at_top_dense)

    have upper: "eventually (\<lambda>n. a > v n) sequentially" if "a>l" for a
    proof -
      obtain t where "t\<in>V" "t<a" using `V \<noteq> {}` cInf_lessD l_def `a>l` by blast
      then have "t>0" using V_def `\<And>n. 0 < u n` v_def by auto
      then have "a/t > 1" using `t<a` by simp
      def e \<equiv> "ln(a/t)/2"
      then have "e>0" by (simp add: `1 < a / t` ln_gt_zero)
      have "e < ln(a/t)" by (simp add: `1 < a / t` e_def ln_gt_zero)
      then have "exp(e) < a/t" by (metis `1 < a / t` exp_less_cancel_iff exp_ln less_trans zero_less_one)

      obtain n where "n>0" "t=v n" using V_def v_def `t \<in> V` by blast
      then have "v n * exp(e) < a" using `exp(e) < a/t` by (metis `0 < t` linordered_field_class.sign_simps(24) pos_less_divide_eq)

      obtain N where *: "N>0" "\<forall>m\<ge>N.  w m/m < w n/n + e" using main_ineq  `0 < n` `e>0` by blast
      {
        fix m
        assume "m\<ge>N"
        then have "m>0" using `N>0` by simp
        have "w m/m < w n/n + e" by (simp add: `N \<le> m` *)
        then have "exp(w m/m) < exp(w n/n + e)" by simp
        also have "... =  exp(w n/n) * exp(e)" by (simp add: mult_exp_exp)
        finally have "v m < v n * exp(e)" using express_vn `m>0` `n>0` by simp
        then have "v m < a" using `v n * exp(e) < a` by simp
      }
      then show ?thesis using eventually_at_top_linorder by auto
    qed

    from lower and upper show ?thesis unfolding v_def l_def V_def by (simp add: order_tendsto_iff)
  qed
qed

definition
  spectral_radius::"'a::real_normed_algebra_1 \<Rightarrow> real"
  where "spectral_radius x = Inf {root n (norm(x^n))| n. n>0}"

lemma spectral_radius_inclusions:
  fixes x::"'a::real_normed_algebra_1"
  defines "V \<equiv> {root n (norm(x^n))| n. n>0}"
  shows "\<And>t. t\<in>V \<Longrightarrow> t \<ge> spectral_radius x"
        "\<And>t. t\<in>V \<Longrightarrow> t \<ge> 0"
        "bdd_below V"
        "V \<noteq> {}"
        "Inf V \<ge> 0"
proof -
  show "V\<noteq>{}" using V_def by blast
  show *: "t \<ge> 0" if "t \<in> V" for t using that unfolding V_def using real_root_pos_pos_le by auto
  then show "bdd_below V" by (meson bdd_below_def)
  then show  "Inf V \<ge> 0" by (simp add: `V \<noteq> {}` * cInf_greatest)
  show "\<And>t. t\<in>V \<Longrightarrow> t \<ge> spectral_radius x" by (metis (mono_tags, lifting) `bdd_below V` assms cInf_lower spectral_radius_def)
qed

lemma spectral_radius_nonneg:
  "spectral_radius x \<ge> 0"
by (simp add: spectral_radius_inclusions(5) spectral_radius_def)

lemma spectral_radius_upper_bound:
  "(spectral_radius x)^n \<le> norm(x^n)"
proof (cases)
  assume "\<not>(n=0)"
  have "root n (norm(x^n)) \<ge> spectral_radius x" using spectral_radius_inclusions `n \<noteq> 0` by auto
  then show ?thesis by (metis `n \<noteq> 0` spectral_radius_nonneg norm_ge_zero not_gr0 power_mono real_root_pow_pos2)
qed (simp)

lemma spectral_radius_limit:
  "(\<lambda>n. root n (norm(x^n))) \<longlonglongrightarrow> spectral_radius x"
proof -
  have "norm(x^(m+n)) \<le> norm(x^m) * norm(x^n)" for m n by (simp add: power_add norm_mult_ineq)
  then show ?thesis unfolding spectral_radius_def using submultiplicative_converges by auto
qed

end