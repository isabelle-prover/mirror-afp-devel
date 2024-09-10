section \<open>An exponential improvement far from the diagonal\<close>

theory Far_From_Diagonal 
  imports Zigzag "Stirling_Formula.Stirling_Formula"

begin
                               

subsection \<open>An asymptotic form for binomial coefficients via Stirling's formula\<close>

text \<open>From Appendix D.3, page 56\<close>

lemma const_smallo_real: "(\<lambda>n. x) \<in> o(real)"
  by real_asymp

lemma o_real_shift:
  assumes "f \<in> o(real)"
  shows "(\<lambda>i. f(i+j)) \<in> o(real)"
  unfolding smallo_def
proof clarify
  fix c :: real
  assume "(0::real) < c"
  then have *: "\<forall>\<^sub>F i in sequentially. norm (f i) \<le> c/2 * norm i"
    using assms half_gt_zero landau_o.smallD by blast
  have "\<forall>\<^sub>F i in sequentially. norm (f (i + j)) \<le> c/2 * norm (i + j)"
    using eventually_all_ge_at_top [OF *]
    by (metis (mono_tags, lifting) eventually_sequentially le_add1)
  then have "\<forall>\<^sub>F i in sequentially. i\<ge>j \<longrightarrow> norm (f (i + j)) \<le> c * norm i"
    apply eventually_elim
    apply clarsimp
    by (smt (verit, best) \<open>0 < c\<close> mult_left_mono nat_distrib(2) of_nat_mono)
  then show "\<forall>\<^sub>F i in sequentially. norm (f (i + j)) \<le> c * norm i"
    using eventually_mp by fastforce
qed

lemma tendsto_zero_imp_o1:
  fixes a :: "nat \<Rightarrow> real"
  assumes "a \<longlonglongrightarrow> 0"
  shows "a \<in> o(1)"
proof -
  have "\<forall>\<^sub>F n in sequentially. \<bar>a n\<bar> \<le> c" if "c>0" for c
    using assms order_tendstoD(2) tendsto_rabs_zero_iff eventually_sequentially less_eq_real_def that
      by metis
  then show ?thesis
    by (auto simp: smallo_def)
qed

subsection \<open>Fact D.3 from the Appendix\<close>

text \<open>And hence, Fact 9.4\<close>

definition "stir \<equiv> \<lambda>n. fact n / (sqrt (2*pi*n) * (n / exp 1) ^ n) - 1"

text \<open>Generalised to the reals to allow derivatives\<close>
definition "stirG \<equiv> \<lambda>n. Gamma (n+1) / (sqrt (2*pi*n) * (n / exp 1) powr n) - 1"

lemma stir_eq_stirG: "n>0 \<Longrightarrow> stir n = stirG (real n)"
  by (simp add: stirG_def stir_def add.commute powr_realpow Gamma_fact)

lemma stir_ge0: "n>0 \<Longrightarrow> stir n \<ge> 0"
  using fact_bounds[of n] by (simp add: stir_def)

lemma stir_to_0: "stir \<longlonglongrightarrow> 0"
  using fact_asymp_equiv by (simp add: asymp_equiv_def stir_def LIM_zero)

lemma stir_o1: "stir \<in> o(1)"
  using stir_to_0 tendsto_zero_imp_o1 by presburger

lemma fact_eq_stir_times: "n \<noteq> 0 \<Longrightarrow> fact n = (1 + stir n) * (sqrt (2*pi*n) * (n / exp 1) ^ n)"
  by (simp add: stir_def)

definition "logstir \<equiv> \<lambda>n. if n=0 then 0 else log 2 ((1 + stir n) * sqrt (2*pi*n))"

lemma logstir_o_real: "logstir \<in> o(real)"
proof -
  have "\<forall>\<^sup>\<infinity>n. 0 < n \<longrightarrow> \<bar>log 2 ((1 + stir n) * sqrt (2*pi*n))\<bar> \<le> c * real n" if "c>0" for c
  proof -
    have "\<forall>\<^sup>\<infinity>n. 2 powr (c*n) / sqrt (2*pi*n) \<ge> c+1"
      using that by real_asymp
    moreover have "\<forall>\<^sup>\<infinity>n. \<bar>stir n\<bar> \<le> c"
      using stir_o1 that by (auto simp: smallo_def)
    ultimately have "\<forall>\<^sup>\<infinity>n. ((1 + stir n) * sqrt (2*pi*n)) \<le> 2 powr (c * n)"
    proof eventually_elim
      fix n
      assume c1: "c+1 \<le> 2 powr (c * n) / sqrt (2*pi*n)" and lec: "\<bar>stir n\<bar> \<le> c"
      then have "stir n \<le> c"
        by auto
      then show "(1 + stir n) * sqrt (2*pi*n) \<le> 2 powr (c*n)"
        using mult_right_mono [OF c1, of "sqrt (2*pi*n)"] lec
        by (smt (verit, ccfv_SIG) c1 mult_right_mono nonzero_eq_divide_eq pos_prod_le powr_gt_zero)
    qed
    then show ?thesis
    proof (eventually_elim, clarify)
      fix n
      assume n: "(1 + stir n) * sqrt (2 * pi * n) \<le> 2 powr (c * n)"
        and "n>0"
      have "(1 + stir n) * sqrt (2 * pi * real n) \<ge> 1"
        using stir_ge0 \<open>0 < n\<close> mult_ge1_I pi_ge_two by auto
      with n show "\<bar>log 2 ((1 + stir n) * sqrt (2 * pi * n))\<bar> \<le> c * n"
        by (simp add: abs_if le_powr_iff)
    qed
  qed
  then show ?thesis
    by (auto simp: smallo_def logstir_def)
qed

lemma logfact_eq_stir_times:
   "fact n = 2 powr (logstir n) * (n / exp 1) ^ n"
proof-
  have "1 + stir n > 0" if "n\<noteq>0"
    using that by (simp add: stir_def)
  then show ?thesis
    by (simp add: logstir_def fact_eq_stir_times)
qed

lemma mono_G:
  defines "G \<equiv> (\<lambda>x::real. Gamma (x + 1) / (x / exp 1) powr x)"
  shows "mono_on {0<..} G"
  unfolding monotone_on_def
proof (intro strip)
  fix x y::real
  assume x: "x \<in> {0<..}" "x \<le> y"
  define GD where "GD \<equiv> \<lambda>u::real. Gamma(u+1) * (Digamma(u+1) - ln(u)) / (u / exp 1) powr u"
  have *: "\<exists>D. (G has_real_derivative D) (at u) \<and> D > 0" if "0 < u" for u 
  proof (intro exI conjI)
    show "(G has_real_derivative GD u) (at u)"
      unfolding G_def GD_def
      using that
      by (force intro!: derivative_eq_intros has_real_derivative_powr' simp: ln_div pos_prod_lt field_simps)
    show "GD u > 0"
      using that by (auto simp: GD_def Digamma_plus_1_gt_ln) \<comment>\<open>Thank you, Manuel!\<close>
  qed
  show "G x \<le> G y"
    using x DERIV_pos_imp_increasing [OF _ *] by (force simp: less_eq_real_def)
qed

lemma mono_logstir: "mono logstir"
  unfolding monotone_on_def
proof (intro strip)
  fix i j::nat
  assume "i\<le>j"
  show "logstir i \<le> logstir j"
  proof (cases "j=0")
    case True
    with \<open>i\<le>j\<close> show ?thesis
      by auto
  next
    case False
    with pi_ge_two have "1 * 1 \<le> 2 * pi * j"
      by (intro mult_mono) auto
    with False stir_ge0 [of j] have *: "1 * 1 \<le> (1 + stir j) * sqrt (2 * pi * real j)"
      by (intro mult_mono) auto
    with \<open>i \<le> j\<close> mono_G show ?thesis
      by (auto simp: logstir_def stir_eq_stirG stirG_def monotone_on_def)
  qed
qed

definition "ok_fun_94 \<equiv> \<lambda>k. - logstir k"

lemma ok_fun_94: "ok_fun_94 \<in> o(real)"
  unfolding ok_fun_94_def
  using logstir_o_real by simp 

lemma fact_9_4:
  assumes l: "0 < l" "l \<le> k"
  defines "\<gamma> \<equiv> l / (real k + real l)"
  shows "k+l choose l \<ge> 2 powr ok_fun_94 k * \<gamma> powr (-l) * (1-\<gamma>) powr (-k)" 
proof -
  have *: "ok_fun_94 k \<le> logstir (k+l) - (logstir k + logstir l)"
    using mono_logstir by (auto simp: ok_fun_94_def monotone_def)
  have "2 powr ok_fun_94 k * \<gamma> powr (- real l) * (1-\<gamma>) powr (- real k)
      = (2 powr ok_fun_94 k) * (k+l) powr(k+l) / (k powr k * l powr l)"
    by (simp add: \<gamma>_def powr_minus powr_add powr_divide divide_simps)
  also have "\<dots> \<le> (2 powr (logstir (k+l)) / (2 powr (logstir k)  * 2 powr (logstir l)))
                 * (k+l) powr (k+l) / (k powr k * l powr l)"
    by (smt (verit, del_insts) * divide_right_mono mult_less_0_iff mult_right_mono powr_add powr_diff powr_ge_zero powr_mono)
  also have "\<dots> = fact(k+l) / (fact k * fact l)"
    using l by (simp add: logfact_eq_stir_times powr_add divide_simps flip: powr_realpow)
  also have "\<dots> = real (k+l choose l)"
    by (simp add: binomial_fact)
  finally show ?thesis .
qed

subsection \<open>Fact D.2\<close>

text \<open>For Fact 9.6\<close>

lemma D2:
  fixes k l
  assumes t: "0<t" "t \<le> k"
  defines "\<gamma> \<equiv> l / (real k + real l)"
  shows "(k+l-t choose l) \<le> exp (- \<gamma> * (t-1)^2 / (2*k)) * (k / (k+l))^t * (k+l choose l)"
proof -
  have "(k+l-t choose l) * inverse (k+l choose l) = (\<Prod>i<t. (k-i) / (k+l-i))"
    using \<open>t \<le> k\<close>
  proof (induction t)
    case (Suc t)
    then have "t \<le> k"
      by simp
    have "(k + l - t) * (k + l - Suc t choose l) = (k - t) * (k + l - t choose l)"
      by (metis binomial_absorb_comp diff_Suc_eq_diff_pred diff_add_inverse2 diff_commute)
    with Suc.IH [symmetric] Suc(2) show ?case 
      by (simp add: field_simps flip: of_nat_mult of_nat_diff)
  qed auto
  also have "\<dots> = (real k / (k+l))^t * (\<Prod>i<t. 1 - real i * real l / (real k * (k+l-i)))"
  proof -
    have "1 - i * real l / (real k * (k+l-i)) = ((k-i)/(k+l-i)) * ((k+l) / k)" 
      if "i<t" for i
      using that \<open>t \<le> k\<close> by (simp add: divide_simps) argo
    then have *: "(\<Prod>i<t. 1 - real i * real l / (real k * (k+l-i))) = (\<Prod>i<t. ((k-i)/(k+l-i)) * ((k+l) / k))"
      by auto
    show ?thesis
      unfolding * prod.distrib by (simp add: power_divide)
  qed
  also have "\<dots> \<le> (real k / (k+l))^t * exp (- (\<Sum>i<t. real i * real l / (real k * (k+l))))"
  proof (intro mult_left_mono)
    have "real i * real l / (real k * real (k+l-i)) \<le> 1"
      if "i < t" for i
      using that \<open>t \<le> k\<close> by (simp add: divide_simps mult_mono)
    moreover have "1 - i * l / (k * real (k+l-i)) \<le> exp (- (i * real l / (k * (k + real l))))" (is "_ \<le> ?R")
      if "i < t" for i 
    proof -
      have "exp (- (i*l / (k * real (k+l-i)))) \<le> ?R"
        using that \<open>t \<le> k\<close> by (simp add: frac_le_eq divide_le_0_iff mult_mono)
      with exp_minus_ge show ?thesis
        by (smt (verit, best)) 
    qed
    ultimately show "(\<Prod>i<t. 1 - i * real l / (k * real (k+l-i))) \<le> exp (- (\<Sum>i<t. i * real l / (k * real (k+l))))"
      by (force simp: exp_sum simp flip: sum_negf intro!: prod_mono)
  qed auto
  finally have 1: "(k+l-t choose l) * inverse (k+l choose l) 
                 \<le> (real k / (k+l))^t * exp (- (\<Sum>i<t. i * \<gamma> / k))"
    by (simp add: \<gamma>_def mult.commute)
  have **: "\<gamma> * (t - 1)^2 / (2*k) \<le> (\<Sum>i<t. i * \<gamma> / k)"
  proof -
    have g: "(\<Sum>i<t. real i) = real (t*(t-1)) / 2"
      by (induction t) (auto simp: algebra_simps eval_nat_numeral)
    have "\<gamma> * (t-1)^2 / (2*k) \<le> real(t*(t-1)) / 2 * \<gamma>/k"
      by (simp add: field_simps eval_nat_numeral divide_right_mono mult_mono \<gamma>_def)
    also have "\<dots> = (\<Sum>i<t. i * \<gamma> / k)" 
      unfolding g [symmetric] by (simp add: sum_distrib_right sum_divide_distrib)
    finally show ?thesis .
  qed
  have 0: "0 \<le> real (k + l choose l)"
    by simp
  have *: "(k+l-t choose l) \<le> (k / (k+l))^t * exp (- (\<Sum>i<t. i * \<gamma> / k)) * (k+l choose l)"
    using order_trans [OF _  mult_right_mono [OF 1 0]]
    by (simp add: less_eq_real_def)
  also have "\<dots> \<le> (k / (k+l))^t * exp (- \<gamma> * (t-1)^2 / (2*k)) *(k+l choose l)"
    using ** by (intro mult_mono) auto
  also have "\<dots> \<le> exp (- \<gamma> * (t-1)^2 / (2 * real k)) * (k / (k+l))^t * (k+l choose l)"
    by (simp add: mult_ac)
  finally show ?thesis 
    using t by simp
qed

text \<open>Statement borrowed from Bhavik; no o(k) function\<close>
corollary Far_9_6:
  fixes k l
  assumes t: "0<t" "t \<le> k"
  defines "\<gamma> \<equiv> l / (k + real l)"
  shows "exp (-1) * (1-\<gamma>) powr (- real t) * exp (\<gamma> * (real t)\<^sup>2 / real(2*k)) * (k-t+l choose l) \<le> (k+l choose l)"
proof -
  have kkl: "k / (k + real l) = 1 - \<gamma>" "k+l-t = k-t+l"
    using t by (auto simp: \<gamma>_def divide_simps)
  have [simp]: "t + t \<le> Suc (t * t)"
    using t
    by (metis One_nat_def Suc_leI mult_2 mult_right_mono nle_le not_less_eq_eq numeral_2_eq_2 mult_1_right)
  have "0 \<le> \<gamma>" "\<gamma> < 1"
    using t by (auto simp: \<gamma>_def)
  then have "\<gamma> * (real t * 2) \<le> \<gamma> + real k * 2"
    using t by (smt (verit, best) mult_less_cancel_right2 of_nat_0_less_iff of_nat_mono)
  then have *: "\<gamma> * t^2 / (2*k) - 1 \<le> \<gamma> * (t-1)^2 / (2*k)"
    using t 
    apply (simp add: power2_eq_square pos_divide_le_eq divide_simps)
    apply (simp add: algebra_simps)
    done
  then have *: "exp (-1) * exp (\<gamma> * t^2 / (2*k)) \<le> exp (\<gamma> * (t-1)^2 / (2*k))"
    by (metis exp_add exp_le_cancel_iff uminus_add_conv_diff)
  have 1: "exp (\<gamma> * (t-1)^2 / (2*k)) * (k+l-t choose l) \<le> (k / (k+l))^t * (k+l choose l)"
    using mult_right_mono [OF D2 [OF t], of "exp (\<gamma> * (t-1)^2 / (2*k))" l] t
    by (simp add: \<gamma>_def exp_minus field_simps)
  have 2: "(k / (k+l)) powr (- real t) * exp (\<gamma> * (t-1)^2 / (2*k)) * (k+l-t choose l) \<le> (k+l choose l)"
    using mult_right_mono [OF 1, of "(1-\<gamma>) powr (- real t)"] t
    by (simp add: powr_minus \<gamma>_def powr_realpow mult_ac divide_simps)
  then have 3: "(1-\<gamma>) powr (- real t) * exp (\<gamma> * (t-1)^2 / (2*k)) * (k-t+l choose l) \<le> (k+l choose l)"
    by (simp add: kkl)
  show ?thesis
    apply (rule order_trans [OF _ 3])
    using "*" less_eq_real_def by fastforce
qed


subsection \<open>Lemma 9.3\<close>

definition "ok_fun_93g \<equiv> \<lambda>\<gamma> k. (nat \<lceil>k powr (3/4)\<rceil>) * log 2 k - (ok_fun_71 \<gamma> k + ok_fun_94 k) + 1"

lemma ok_fun_93g: 
  assumes "0 < \<gamma>" "\<gamma> < 1"
  shows "ok_fun_93g \<gamma> \<in> o(real)"
proof -
  have "(\<lambda>k. (nat \<lceil>k powr (3/4)\<rceil>) * log 2 k) \<in> o(real)"
    by real_asymp
  then show ?thesis
    unfolding ok_fun_93g_def
    by (intro ok_fun_71 [OF assms] ok_fun_94 sum_in_smallo const_smallo_real)
qed

definition "ok_fun_93h \<equiv> \<lambda>\<gamma> k. (2 / (1-\<gamma>)) * k powr (19/20) * (ln \<gamma> + 2 * ln k)
                                 + ok_fun_93g \<gamma> k * ln 2"

lemma ok_fun_93h:
  assumes "0 < \<gamma>" "\<gamma> < 1"
  shows  "ok_fun_93h \<gamma> \<in> o(real)"
proof -
  have "(\<lambda>k. (2 / (1-\<gamma>)) * k powr (19/20) * (ln \<gamma> + 2 * ln k)) \<in> o(real)"
    by real_asymp
  then show ?thesis
    unfolding ok_fun_93h_def by (metis (mono_tags) ok_fun_93g assms sum_in_smallo(1) cmult_in_smallo_iff')
qed

lemma ok_fun_93h_uniform:
  assumes \<mu>01: "0<\<mu>0" "\<mu>1<1" 
  assumes "e>0" 
  shows  "\<forall>\<^sup>\<infinity>k. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> \<bar>ok_fun_93h \<mu> k\<bar> / k \<le> e"
proof -
  define f where "f \<equiv> \<lambda>k. ok_fun_73 k + ok_fun_74 k + ok_fun_76 k + ok_fun_94 k"
  define g where "g \<equiv> \<lambda>\<mu> k. 2 * real k powr (19/20) * (ln \<mu> + 2 * ln k) / (1-\<mu>)"
  have g: "\<forall>\<^sup>\<infinity>k. \<forall>\<mu>. \<mu>0 \<le> \<mu> \<and> \<mu> \<le> \<mu>1 \<longrightarrow> \<bar>g \<mu> k\<bar> / k \<le> e" if "e>0" for e
  proof (intro eventually_all_geI1 [where L = "nat\<lceil>1 / \<mu>0\<rceil>"])
    show "\<forall>\<^sup>\<infinity>k. \<bar>g \<mu>1 k\<bar> / real k \<le> e"
      using assms that unfolding g_def by real_asymp
  next
    fix k \<mu> 
    assume le_e: "\<bar>g \<mu>1 k\<bar> / k \<le> e" and \<mu>: "\<mu>0 \<le> \<mu>" "\<mu> \<le> \<mu>1" and k: "nat \<lceil>1/\<mu>0\<rceil> \<le> k"
    then have "k>0"
      using assms gr0I by force
    have ln_k: "ln k \<ge> ln (1/\<mu>0)"
      using k \<open>0<\<mu>0\<close> ln_mono by fastforce
    with \<mu> \<mu>01 
    have "\<bar>ln \<mu> + 2 * ln (real k)\<bar> \<le> \<bar>ln \<mu>1 + 2 * ln (real k)\<bar>"
      by (smt (verit) ln_div ln_mono ln_one)
    with \<mu> k \<open>\<mu>1 < 1\<close>
    have "\<bar>g \<mu> k\<bar> \<le> \<bar>g \<mu>1 k\<bar>"       
      by (simp add: g_def abs_mult frac_le mult_mono)
    then show "\<bar>g \<mu> k\<bar> / real k \<le> e"
      by (smt (verit, best) divide_right_mono le_e of_nat_less_0_iff)
  qed
  have eq93: "ok_fun_93h \<mu> k = g \<mu> k +
         \<lceil>k powr (3/4)\<rceil> * ln k - ((ok_fun_72 \<mu> k + f k) - 1) * ln 2" for \<mu> k
    by (simp add: ok_fun_93h_def g_def ok_fun_71_def ok_fun_93g_def f_def log_def field_simps)

  have ln2: "ln 2 \<ge> (0::real)"
    by simp
  have le93: "\<bar>ok_fun_93h \<mu> k\<bar> 
     \<le> \<bar>g \<mu> k\<bar> + \<bar>\<lceil>k powr (3/4)\<rceil> * ln k\<bar> + (\<bar>ok_fun_72 \<mu> k\<bar> + \<bar>f k\<bar> + 1) * ln 2" for \<mu> k
    unfolding eq93
    by (smt (verit, best) mult.commute ln_gt_zero_iff mult_le_cancel_left_pos mult_minus_left)
  define e5 where "e5 \<equiv> e/5"
  have "e5 > 0"
    by (simp add: \<open>e>0\<close> e5_def)
  then have A: "\<forall>\<^sup>\<infinity>k. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> \<bar>g \<mu> k\<bar> / k \<le> e5" 
    using g by simp
  have B: "\<forall>\<^sup>\<infinity>k. \<bar>\<lceil>k powr (3/4)\<rceil> * ln k\<bar> / k \<le> e5" 
    using \<open>0 < e5\<close> by real_asymp
  have C: "\<forall>\<^sup>\<infinity>k. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> \<bar>ok_fun_72 \<mu> k\<bar> * ln 2 / k \<le> e5"
    using ln2 assms ok_fun_72_uniform[OF \<mu>01, of "e5 / ln 2"] \<open>e5 > 0\<close>
    by (simp add: divide_simps)
  have "f \<in> o(real)"
    by (simp add: f_def ok_fun_73 ok_fun_74 ok_fun_76 ok_fun_94 sum_in_smallo(1))
  then have D: "\<forall>\<^sup>\<infinity>k. \<bar>f k\<bar> * ln 2 / k \<le> e5"
    using \<open>e5 > 0\<close> ln2
    by (force simp: smallo_def field_simps eventually_at_top_dense dest!: spec [where x="e5 / ln 2"])
  have E: "\<forall>\<^sup>\<infinity>k.  ln 2 / k \<le> e5"
    using \<open>e5 > 0\<close> ln2 by real_asymp
  have "\<forall>\<^sup>\<infinity>k. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> \<bar>ok_fun_93h \<mu> k\<bar> / real k \<le> e5+e5+e5+e5+e5"
    using A B C D E
    apply eventually_elim
    by (fastforce simp: add_divide_distrib distrib_right
          intro!: order_trans [OF  divide_right_mono [OF le93]])
  then show ?thesis
    by (simp add: e5_def)
qed

context P0_min
begin

definition "Big_Far_9_3 \<equiv>     
   \<lambda>\<mu> l. Big_ZZ_8_5 \<mu> l \<and> Big_X_7_1 \<mu> l \<and> Big_Y_6_2 \<mu> l \<and> Big_Red_5_3 \<mu> l
      \<and> (\<forall>k\<ge>l. p0_min - 3 * eps k > 1/k \<and> k\<ge>2
             \<and> \<bar>ok_fun_93h \<mu> k / (\<mu> * (1 + 1 / (exp 1 * (1-\<mu>))))\<bar> / k \<le> 0.667 - 2/3)"

lemma Big_Far_9_3:
  assumes "0<\<mu>0" "\<mu>0\<le>\<mu>1" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> Big_Far_9_3 \<mu> l"
proof -
  define d where "d \<equiv> \<lambda>\<mu>::real. \<mu> * (1 + 1 / (exp 1 * (1-\<mu>)))"
  have "d \<mu>0 > 0" 
    using assms by (auto simp: d_def divide_simps add_pos_pos)
  then have dgt: "d \<mu> \<ge> d \<mu>0" if "\<mu> \<in> {\<mu>0..\<mu>1}" for \<mu>
    using that assms by (auto simp: d_def frac_le mult_mono)

  define e::real where "e \<equiv> 0.667 - 2/3"
  have "e>0"
    by (simp add: e_def)
  have *: "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> (\<forall>k\<ge>l. \<bar>ok_fun_93h \<mu> k / d \<mu>\<bar> / k \<le> e)" 
  proof -
    have "\<forall>\<^sup>\<infinity>l. \<forall>k\<ge>l. (\<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> \<bar>ok_fun_93h \<mu> k\<bar> / k \<le> d \<mu>0 * e)" 
      using mult_pos_pos[OF \<open>d \<mu>0 > 0\<close> \<open>e>0\<close>] assms
      using ok_fun_93h_uniform eventually_all_ge_at_top
      by blast  
    then show ?thesis
      apply eventually_elim 
      using dgt \<open>0 < d \<mu>0\<close> \<open>0 < e\<close>
      by (auto simp: mult_ac divide_simps mult_less_0_iff zero_less_mult_iff split: if_split_asm)
        (smt (verit) mult_less_cancel_left nat_neq_iff of_nat_0_le_iff)
  qed
  with p0_min show ?thesis
    unfolding Big_Far_9_3_def eps_def d_def e_def
    using assms Big_ZZ_8_5 Big_X_7_1 Big_Y_6_2 Big_Red_5_3
    apply (simp add: eventually_conj_iff all_imp_conj_distrib)  
    apply (intro conjI strip eventually_all_ge_at_top; real_asymp)
    done
qed

end (*context P0_Min*)

lemma "(\<lambda>k. (nat \<lceil>real k powr (3/4)\<rceil>) * log 2 k) \<in> o(real)"
  by real_asymp

lemma RN34_le_2powr_ok:
  fixes l k::nat
  assumes "l \<le> k" "0<k"
  defines "l34 \<equiv> nat \<lceil>real l powr (3/4)\<rceil>"
  shows "RN k l34 \<le> 2 powr (\<lceil>k powr (3/4)\<rceil> * log 2 k)"
proof -
  have \<section>: "\<lceil>l powr (3/4)\<rceil> \<le> \<lceil>k powr (3/4)\<rceil>"
    by (simp add: assms(1) ceiling_mono powr_mono2)
  have "RN k l34 \<le> k powr (l34-1)"
    \<comment>\<open>Bhavik's off-diagonal Ramsey upper bound; can't use @{term "2^(k+l34)"}\<close>
    using RN_le_argpower' \<open>k>0\<close> powr_realpow by auto
  also have "\<dots> \<le> k powr l34"
    using \<open>k>0\<close> powr_mono by force
  also have "\<dots> \<le> 2 powr (l34 * log 2 k)"
    by (smt (verit, best) mult.commute \<open>k>0\<close> of_nat_0_less_iff powr_log_cancel powr_powr)
  also have "\<dots> \<le> 2 powr (\<lceil>real k powr (3/4)\<rceil> * log 2 k)"
    unfolding l34_def 
  proof (intro powr_mono powr_mono2 mult_mono ceiling_mono of_nat_mono nat_mono \<open>l \<le> k\<close>)
    show "0 \<le> real_of_int \<lceil>k powr (3/4)\<rceil>"
      by (meson le_of_int_ceiling order.trans powr_ge_zero)
  qed (use assms \<section> in auto)
  finally show ?thesis .
qed

text \<open>Here @{term n} really refers to the cardinality of @{term V}, 
   so actually @{term nV}\<close>
lemma (in Book') Far_9_3:
  defines "\<delta> \<equiv> min (1/200) (\<gamma>/20)"
  defines "\<R> \<equiv> Step_class {red_step}"
  defines "t \<equiv> card \<R>"
  assumes \<gamma>15: "\<gamma> \<le> 1/5" and p0: "p0 \<ge> 1/4" 
    and nge: "n \<ge> exp (-\<delta> * real k) * (k+l choose l)" 
    and X0ge: "card X0 \<ge> n/2" 
           \<comment>\<open>Because @{term"card X0 \<ge> n div 2"} makes the proof harder\<close>
  assumes big: "Big_Far_9_3 \<gamma> l"
  shows "t \<ge> 2*k / 3"
proof -
  define \<S> where "\<S> \<equiv> Step_class {dboost_step}"
  have "k\<ge>2" and big85: "Big_ZZ_8_5 \<gamma> l" and big71: "Big_X_7_1 \<gamma> l" 
    and big62: "Big_Y_6_2 \<gamma> l"  and big53: "Big_Red_5_3 \<gamma> l"
    using big l_le_k by (auto simp: Big_Far_9_3_def)
  define l34 where "l34 \<equiv> nat \<lceil>real l powr (3/4)\<rceil>"
  have "l34 > 0"
    using l34_def ln0 by fastforce
  have \<gamma>01: "0 < \<gamma>" "\<gamma> < 1"
    using ln0 l_le_k by (auto simp: \<gamma>_def)
  then have bigbeta01: "0 < bigbeta" "bigbeta < 1"
    using big53 assms bigbeta_gt0 bigbeta_less1 by (auto simp: bigbeta_def)
  have one_minus: "1-\<gamma> = real k / (real k + real l)"
    using ln0 by (simp add: \<gamma>_def divide_simps)
  have "t < k"
    using red_step_limit by (auto simp: \<R>_def t_def)
  have f: "2 powr ok_fun_94 k * \<gamma> powr (- real l) * (1-\<gamma>) powr (- real k)
          \<le> k+l choose l" 
    unfolding \<gamma>_def using fact_9_4 l_le_k ln0 by blast
  have powr_combine_right: "x powr a * (x powr b * y) = x powr (a+b) * y" for x y a b::real
    by (simp add: powr_add)
  have "(2 powr ok_fun_71 \<gamma> k * 2 powr ok_fun_94 k) * (bigbeta/\<gamma>) ^ card \<S> * (exp (-\<delta>*k) * (1-\<gamma>) powr (- real k + t) / 2)
      \<le> 2 powr ok_fun_71 \<gamma> k * \<gamma>^l * (1-\<gamma>) ^ t * (bigbeta/\<gamma>) ^ card \<S> * (exp (-\<delta>*k) * (k+l choose l) / 2)"
    using \<gamma>01 \<open>0<bigbeta\<close> mult_right_mono [OF f, of "2 powr ok_fun_71 \<gamma> k * \<gamma>^l * (1-\<gamma>) ^ t * (bigbeta/\<gamma>) ^ card \<S> * (exp (-\<delta>*k)) / 2"]
    by (simp add: mult_ac zero_le_mult_iff powr_minus powr_diff divide_simps powr_realpow)
  also have "\<dots> \<le> 2 powr ok_fun_71 \<gamma> k * \<gamma>^l * (1-\<gamma>) ^ t * (bigbeta/\<gamma>) ^ card \<S> * card X0"
  proof (intro mult_left_mono order_refl)
    show "exp (-\<delta> * k) * real (k+l choose l) / 2 \<le> real (card X0)"
      using X0ge nge by force
    show "0 \<le> 2 powr ok_fun_71 \<gamma> k * \<gamma> ^ l * (1-\<gamma>) ^ t * (bigbeta/\<gamma>) ^ card \<S>"
      using \<gamma>01 bigbeta_ge0 by (force simp: bigbeta_def)
  qed
  also have "\<dots> \<le> card (Xseq halted_point)"
    unfolding \<R>_def \<S>_def t_def using big 
    by (intro X_7_1) (auto simp: Big_Far_9_3_def)
  also have "\<dots> \<le> RN k l34"
  proof -
    have "p0 - 3 * eps k > 1/k" and "pee halted_point \<ge> p0 - 3 * eps k"
      using l_le_k big p0_ge Y_6_2_halted by (auto simp: Big_Far_9_3_def \<gamma>_def)
    then show ?thesis
      using halted_point_halted \<gamma>01
      by (fastforce simp: step_terminating_iff termination_condition_def pee_def l34_def)
  qed
  also have "\<dots> \<le> 2 powr (\<lceil>k powr (3/4)\<rceil> * log 2 k)"
    using RN34_le_2powr_ok l34_def l_le_k ln0 by blast
  finally have "2 powr (ok_fun_71 \<gamma> k + ok_fun_94 k) * (bigbeta/\<gamma>) ^ card \<S>
               * exp (-\<delta>*k) * (1-\<gamma>) powr (- real k + t) / 2
              \<le> 2 powr (\<lceil>k powr (3/4)\<rceil> * log 2 k)"
    by (simp add: powr_add)
  then have le_2_powr_g: "exp (-\<delta>*k) * (1-\<gamma>) powr (- real k + t) * (bigbeta/\<gamma>) ^ card \<S>
             \<le> 2 powr ok_fun_93g \<gamma> k"
    using \<open>k\<ge>2\<close> by (simp add: ok_fun_93g_def field_simps powr_add powr_diff flip: powr_realpow)

  let ?\<xi> = "bigbeta * t / (1-\<gamma>) + (2 / (1-\<gamma>)) * k powr (19/20)"
  have bigbeta_le: "bigbeta \<le> \<gamma>" and bigbeta_ge: "bigbeta \<ge> 1 / (real k)\<^sup>2"
    using bigbeta_def \<gamma>01 big53 bigbeta_le bigbeta_ge_square by blast+
  
  define \<phi> where "\<phi> \<equiv> \<lambda>u. (u / (1-\<gamma>)) * ln (\<gamma>/u)"  \<comment>\<open>finding the maximum via derivatives\<close>
  have ln_eq: "ln (\<gamma> / (\<gamma> / exp 1)) / (1-\<gamma>) = 1/(1-\<gamma>)"
    using \<gamma>01 by simp
  have \<phi>: "\<phi> (\<gamma> / exp 1) \<ge> \<phi> bigbeta"
  proof (cases "\<gamma> / exp 1 \<le> bigbeta")    \<comment>\<open>Could perhaps avoid case analysis via 2nd derivatives\<close>
    case True
    show ?thesis 
    proof (intro DERIV_nonpos_imp_nonincreasing [where f = \<phi>])
      fix x
      assume x: "\<gamma> / exp 1 \<le> x" "x \<le> bigbeta"
      with \<gamma>01 have "x>0"
        by (smt (verit, best) divide_pos_pos exp_gt_zero)
      with \<gamma>01 x have "ln (\<gamma>/x) / (1-\<gamma>) - 1 / (1-\<gamma>) \<le> 0"
        by (smt (verit, ccfv_SIG) divide_pos_pos exp_gt_zero frac_le ln_eq ln_mono)
      with x \<open>x>0\<close> \<gamma>01 show "\<exists>D. (\<phi> has_real_derivative D) (at x) \<and> D \<le> 0"
        unfolding \<phi>_def by (intro exI conjI derivative_eq_intros | force)+
    qed (simp add: True)
  next
    case False
    show ?thesis
    proof (intro DERIV_nonneg_imp_nondecreasing [where f = \<phi>])
      fix x
      assume x: "bigbeta \<le> x" "x \<le> \<gamma> / exp 1"
      with bigbeta01 \<gamma>01 have "x>0" by linarith
      with \<gamma>01 x have "ln (\<gamma>/x) / (1-\<gamma>) - 1 / (1-\<gamma>) \<ge> 0"
        by (smt (verit, best) frac_le ln_eq ln_mono zero_less_divide_iff)
      with x \<open>x>0\<close> \<gamma>01 show "\<exists>D. (\<phi> has_real_derivative D) (at x) \<and> D \<ge> 0"
        unfolding \<phi>_def
        by (intro exI conjI derivative_eq_intros | force)+
    qed (use False in force)
  qed

  define c where "c \<equiv> \<lambda>x::real. 1 + 1 / (exp 1 * (1-x))" 
  have mono_c: "mono_on {0<..<1} c"
    by (auto simp: monotone_on_def c_def field_simps)
  have cgt0: "c x > 0" if "x<1" for x
    using that by (simp add: add_pos_nonneg c_def)

  have "card \<S> \<le> bigbeta * t / (1-bigbeta) + (2 / (1-\<gamma>)) * k powr (19/20)" 
    using ZZ_8_5 [OF big85] by (auto simp: \<R>_def \<S>_def t_def)
  also have "\<dots> \<le> ?\<xi>" 
    using bigbeta_le by (simp add: \<gamma>01 bigbeta_ge0 frac_le)
  finally have "card \<S> \<le> ?\<xi>" .
  with bigbeta_le bigbeta01 have "?\<xi> * ln (bigbeta/\<gamma>) \<le> card \<S> * ln (bigbeta/\<gamma>)"
    by (simp add: mult_right_mono_neg)
  then have "-?\<xi> * ln (\<gamma>/bigbeta) \<le> card \<S> * ln (bigbeta/\<gamma>)"
    using bigbeta01 \<gamma>01 by (smt (verit) ln_div minus_mult_minus)
  then have "\<gamma> * (real k - t) - \<delta>*k - ?\<xi> * ln (\<gamma>/bigbeta) \<le> \<gamma> * (real k - t) - \<delta>*k + card \<S> * ln (bigbeta/\<gamma>)"
    by linarith
  also have "\<dots> \<le> (t - real k) * ln (1-\<gamma>) - \<delta>*k + card \<S> * ln (bigbeta/\<gamma>)"
    using \<open>t < k\<close> \<gamma>01 mult_right_mono [OF ln_add_one_self_le_self2 [of "-\<gamma>"], of "real k - t"] 
    by (simp add: algebra_simps)
  also have "\<dots> = ln (exp (-\<delta>*k) * (1-\<gamma>) powr (- real k + t) * (bigbeta/\<gamma>) ^ card \<S>)"
    using \<gamma>01 bigbeta01 by (simp add: ln_mult ln_div ln_realpow)
  also have "\<dots> \<le> ln (2 powr ok_fun_93g \<gamma> k)"
    using le_2_powr_g \<gamma>01 bigbeta01 by (simp del: ln_powr)
  also have "\<dots> = ok_fun_93g \<gamma> k * ln 2"
    by auto
  finally have "\<gamma> * (real k - t) - \<delta>*k - ?\<xi> * ln (\<gamma>/bigbeta) \<le> ok_fun_93g \<gamma> k * ln 2" .
  then have "\<gamma> * (real k - t) \<le> ?\<xi> * ln (\<gamma>/bigbeta) + \<delta>*k + ok_fun_93g \<gamma> k * ln 2"
    by simp
  also have "\<dots> \<le> (bigbeta * t / (1-\<gamma>)) * ln (\<gamma>/bigbeta) + \<delta>*k + ok_fun_93h \<gamma> k"
  proof -
    have "\<gamma>/bigbeta \<le> \<gamma> * (real k)\<^sup>2"
      using kn0 bigbeta_le bigbeta_ge \<open>bigbeta>0\<close> by (simp add: field_simps)
    then have X: "ln (\<gamma>/bigbeta) \<le> ln \<gamma> + 2 * ln k"
      using \<open>bigbeta>0\<close> \<open>\<gamma>>0\<close> kn0 
      by (metis ln_mult_pos ln_realpow of_nat_numeral of_nat_zero_less_power_iff divide_pos_pos ln_mono)
    show ?thesis
      using mult_right_mono [OF X, of "2 * k powr (19/20) / (1-\<gamma>)"] \<open>\<gamma><1\<close>
      by (simp add: ok_fun_93h_def algebra_simps)
  qed
  also have "\<dots> \<le> ((\<gamma> / exp 1) * t / (1-\<gamma>)) + \<delta>*k + ok_fun_93h \<gamma> k"
    using \<gamma>01 mult_right_mono [OF \<phi>, of t] by (simp add: \<phi>_def mult_ac)
  finally have "\<gamma> * (real k - t) \<le> ((\<gamma> / exp 1) * t / (1-\<gamma>)) + \<delta>*k + ok_fun_93h \<gamma> k" .
  then have "(\<gamma>-\<delta>) * k - ok_fun_93h \<gamma> k \<le> t * \<gamma> * c \<gamma>"
    by (simp add: c_def algebra_simps)
  then have "((\<gamma>-\<delta>) * k - ok_fun_93h \<gamma> k) / (\<gamma> * c \<gamma>) \<le> t"
    using \<gamma>01 cgt0 by (simp add: pos_divide_le_eq)
  then have *: "t \<ge> (1-\<delta> / \<gamma>) * inverse (c \<gamma>) * k - ok_fun_93h \<gamma> k / (\<gamma> * c \<gamma>)"  
    using \<gamma>01 cgt0[of \<gamma>] by (simp add: divide_simps)
  define f47 where "f47 \<equiv> \<lambda>x. (1 - 1/(200*x)) * inverse (c x)"
  have "concave_on {1/10..1/5} f47"
    unfolding f47_def
  proof (intro concave_on_mul)
    show "concave_on {1/10..1/5} (\<lambda>x. 1 - 1/(200*x))"
    proof (intro f''_le0_imp_concave)
      fix x::real
      assume "x \<in> {1/10..1/5}"
      then have x01: "0<x" "x<1" by auto
      show "((\<lambda>x. (1 - 1/(200*x))) has_real_derivative 1/(200*x^2)) (at x)"
        using x01 by (intro derivative_eq_intros | force simp: eval_nat_numeral)+
      show "((\<lambda>x. 1/(200*x^2)) has_real_derivative -1/(100*x^3)) (at x)"
        using x01 by (intro derivative_eq_intros | force simp: eval_nat_numeral)+
      show "-1/(100*x^3) \<le> 0"
        using x01 by (simp add: divide_simps)
    qed auto
    show "concave_on {1/10..1/5} (\<lambda>x. inverse (c x))"
    proof (intro f''_le0_imp_concave)
      fix x::real
      assume "x \<in> {1/10..1/5}"
      then have x01: "0<x" "x<1" by auto
      have swap: "u * (x-1) = (-u) * (1-x)" for u
        by (metis minus_diff_eq minus_mult_commute)
      have \<section>: "exp 1 * (x - 1) < 0"
        using x01 by (meson exp_gt_zero less_iff_diff_less_0 mult_less_0_iff)
      then have non0: "1 + 1 / (exp 1 * (1-x)) \<noteq> 0"
        using x01 by (smt (verit) exp_gt_zero mult_pos_pos zero_less_divide_iff)
      let ?f1 = "\<lambda>x. -exp 1 /(- 1 + exp 1 * (- 1 + x))\<^sup>2"
      let ?f2 = "\<lambda>x. 2*exp(1)^2/(-1 + exp(1)*(-1 + x))^3"
      show "((\<lambda>x. inverse (c x)) has_real_derivative ?f1 x) (at x)"
        unfolding c_def power2_eq_square
        using x01 \<section> non0
        apply (intro exI conjI derivative_eq_intros | force)+
        apply (simp add: divide_simps square_eq_iff swap)
        done
      show "(?f1 has_real_derivative ?f2 x) (at x)"
        using x01 \<section>
        by (intro derivative_eq_intros | force simp: divide_simps eval_nat_numeral)+
      show "?f2 (x::real) \<le> 0"
        using x01 \<section> by (simp add: divide_simps)
    qed auto
    show "mono_on {(1::real)/10..1/5} (\<lambda>x. 1 - 1 / (200 * x))"
      by (auto simp: monotone_on_def frac_le)
    show "monotone_on {1/10..1/5} (\<le>) (\<lambda>x y. y \<le> x) (\<lambda>x. inverse (c x))"
      using mono_c cgt0 by (auto simp: monotone_on_def divide_simps)
  qed (auto simp: c_def)
  moreover have "f47(1/10) > 0.667"
    unfolding f47_def c_def by (approximation 15)
  moreover have "f47(1/5) > 0.667"
    unfolding f47_def c_def by (approximation 15)
  ultimately have 47: "f47 x > 0.667" if "x \<in> {1/10..1/5}" for x
    using concave_on_ge_min that by fastforce

  define f48 where "f48 \<equiv> \<lambda>x. (1 - 1/20) * inverse (c x)"
  have 48: "f48 x > 0.667" if "x \<in> {0<..<1/10}" for x
  proof -
    have "(0.667::real) < (1 - 1/20) * inverse(c(1/10))"
      unfolding c_def by (approximation 15)
    also have "\<dots> \<le> f48 x"
      using that unfolding f48_def c_def
      by (intro mult_mono le_imp_inverse_le add_mono divide_left_mono) (auto simp: add_pos_pos)
    finally show ?thesis .
  qed
  define e::real where "e \<equiv> 0.667 - 2/3"
  have BIGH: "abs (ok_fun_93h \<gamma> k / (\<gamma> * c \<gamma>)) / k \<le> e"
    using big l_le_k unfolding Big_Far_9_3_def all_imp_conj_distrib e_def [symmetric] c_def 
    by auto
  consider "\<gamma> \<in> {0<..<1/10}" | "\<gamma> \<in> {1/10..1/5}"
    using \<delta>_def \<open>\<gamma> \<le> 1/5\<close> \<gamma>01 by fastforce
  then show ?thesis
  proof cases
    case 1
    then have \<delta>\<gamma>: "\<delta> / \<gamma> = 1/20"
      by (auto simp: \<delta>_def)
    have "(2/3::real) \<le> f48 \<gamma> - e"
      using 48[OF 1] e_def by force
    also have "\<dots> \<le> (1-\<delta> / \<gamma>) * inverse (c \<gamma>) - ok_fun_93h \<gamma> k / (\<gamma> * c \<gamma>) / k"
      unfolding f48_def \<delta>\<gamma> using BIGH
      by (smt (verit, best) divide_nonneg_nonneg of_nat_0_le_iff zero_less_divide_iff)
    finally
    have A: "2/3 \<le> (1-\<delta> / \<gamma>) * inverse (c \<gamma>) - ok_fun_93h \<gamma> k / (\<gamma> * c \<gamma>) / k" .
    have "real (2 * k) / 3 \<le> (1 - \<delta> / \<gamma>) * inverse (c \<gamma>) * k - ok_fun_93h \<gamma> k / (\<gamma> * c \<gamma>)"
      using mult_left_mono [OF A, of k] cgt0 [of \<gamma>] \<gamma>01 kn0
      by (simp add: divide_simps mult_ac)
    with * show ?thesis
      by linarith
  next
    case 2
    then have \<delta>\<gamma>: "\<delta> / \<gamma> = 1/(200*\<gamma>)"
      by (auto simp: \<delta>_def)
    have "(2/3::real) \<le> f47 \<gamma> - e"
      using 47[OF 2] e_def by force
    also have "\<dots> \<le> (1 - \<delta> / \<gamma>) * inverse (c \<gamma>) - ok_fun_93h \<gamma> k / (\<gamma> * c \<gamma>) / k"
      unfolding f47_def \<delta>\<gamma> using BIGH
      by (smt (verit, best) divide_right_mono of_nat_0_le_iff)
    finally
    have "2/3 \<le> (1 - \<delta> / \<gamma>) * inverse (c \<gamma>) - ok_fun_93h \<gamma> k / (\<gamma> * c \<gamma>) / k" .
    from mult_left_mono [OF this, of k] cgt0 [of \<gamma>] \<gamma>01 kn0
    have "real (2 * k) / 3 \<le> (1 - \<delta> / \<gamma>) * inverse (c \<gamma>) * k - ok_fun_93h \<gamma> k / (\<gamma> * c \<gamma>)"
      by (simp add: divide_simps mult_ac)
    with * show ?thesis
      by linarith
  qed
qed

subsection \<open>Lemma 9.5\<close>

context P0_min
begin

text \<open>Again stolen from Bhavik: cannot allow a dependence on @{term \<gamma>}\<close>
definition "ok_fun_95a \<equiv> \<lambda>k. ok_fun_61 k - (2 + 4 * k powr (19/20))"

definition "ok_fun_95b \<equiv> \<lambda>k. ln 2 * ok_fun_95a k - 1"

lemma ok_fun_95a: "ok_fun_95a \<in> o(real)"
proof -
  have "(\<lambda>k. 2 + 4 * k powr (19/20)) \<in> o(real)"
    by real_asymp
  then show ?thesis
    unfolding ok_fun_95a_def using ok_fun_61 sum_in_smallo by blast
qed

lemma ok_fun_95b: "ok_fun_95b \<in> o(real)"
  using ok_fun_95a by (auto simp: ok_fun_95b_def sum_in_smallo const_smallo_real)

definition "Big_Far_9_5 \<equiv> \<lambda>\<mu> l. Big_Red_5_3 \<mu> l \<and> Big_Y_6_1 \<mu> l \<and> Big_ZZ_8_5 \<mu> l"

lemma Big_Far_9_5:
  assumes "0<\<mu>0" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. \<mu>0 \<le> \<mu> \<and> \<mu> \<le> \<mu>1 \<longrightarrow> Big_Far_9_5 \<mu> l"
  using assms Big_Red_5_3 Big_Y_6_1 Big_ZZ_8_5
  unfolding Big_Far_9_5_def  eps_def
  by (simp add: eventually_conj_iff all_imp_conj_distrib)  

end

text \<open>Y0 is an additional assumption found in Bhavik's version. (He had a couple of others).
 The first $o(k)$ function adjusts for the error in $n/2$\<close>
lemma (in Book') Far_9_5:
  fixes \<delta> \<eta>::real
  defines "\<R> \<equiv> Step_class {red_step}"
  defines "t \<equiv> card \<R>"
  assumes nV: "real nV \<ge> exp (-\<delta> * k) * (k+l choose l)" and Y0: "card Y0 \<ge> nV div 2"
  assumes p0: "1/2 \<le> 1-\<gamma>-\<eta>" "1-\<gamma>-\<eta> \<le> p0" and "0\<le>\<eta>"
  assumes big: "Big_Far_9_5 \<gamma> l"
  shows "card (Yseq halted_point) \<ge> 
     exp (-\<delta> * k + ok_fun_95b k) * (1-\<gamma>-\<eta>) powr (\<gamma>*t / (1-\<gamma>)) * ((1-\<gamma>-\<eta>)/(1-\<gamma>))^t 
   * exp (\<gamma> * (real t)\<^sup>2 / (2*k)) * (k-t+l choose l)"   (is "_ \<ge> ?rhs")
proof -
  define \<S> where "\<S> \<equiv> Step_class {dboost_step}"
  define s where "s \<equiv> card \<S>"
  have \<gamma>01: "0 < \<gamma>" "\<gamma> < 1"
    using ln0 l_le_k by (auto simp: \<gamma>_def)
  have big85: "Big_ZZ_8_5 \<gamma> l" and big61: "Big_Y_6_1 \<gamma> l" and big53: "Big_Red_5_3 \<gamma> l"
    using big by (auto simp: Big_Far_9_5_def)
  have "bigbeta \<le> \<gamma>" 
    using bigbeta_def \<gamma>01 big53 bigbeta_le by blast 
  have 85: "s \<le> (bigbeta / (1-bigbeta)) * t + (2 / (1-\<gamma>)) * k powr (19/20)"
    unfolding s_def t_def \<R>_def \<S>_def using ZZ_8_5 \<gamma>01 big85 by blast
  also have "\<dots> \<le> (\<gamma> / (1-\<gamma>)) * t + (2 / (1-\<gamma>)) * k powr (19/20)"
    using \<gamma>01 \<open>bigbeta \<le> \<gamma>\<close> by (intro add_mono mult_right_mono frac_le) auto
  finally have D85: "s \<le> \<gamma>*t / (1-\<gamma>) + (2 / (1-\<gamma>)) * k powr (19/20)"
    by auto
  have "t<k"
    unfolding t_def \<R>_def using \<gamma>01 red_step_limit by blast
  have st: "card (Step_class {red_step,dboost_step}) = t + s"
    using \<gamma>01
    by (simp add: s_def t_def \<R>_def \<S>_def Step_class_insert_NO_MATCH card_Un_disjnt disjnt_Step_class)
  then have 61: "2 powr (ok_fun_61 k) * p0 ^ (t+s) * card Y0 \<le> card (Yseq halted_point)"
    using Y_6_1[OF big61] card_XY0 \<gamma>01 by (simp add: divide_simps)
  have "(1-\<gamma>-\<eta>) powr (t + \<gamma>*t / (1-\<gamma>)) * nV \<le> (1-\<gamma>-\<eta>) powr (t+s - 4 * k powr (19/20)) * (4 * card Y0)"
  proof (intro mult_mono)
    show "(1-\<gamma>-\<eta>) powr (t + \<gamma>*t / (1-\<gamma>)) \<le> (1-\<gamma>-\<eta>) powr (t+s - 4 * k powr (19/20))"
    proof (intro powr_mono')
      have "\<gamma> \<le> 1/2"
        using \<open>0\<le>\<eta>\<close> p0 by linarith
      then have 22: "1 / (1 - \<gamma>) \<le> 2"
        using divide_le_eq_1 by fastforce
      show "real (t + s) - 4 * real k powr (19 / 20) \<le> real t + \<gamma> * real t / (1 - \<gamma>)"
        using mult_left_mono [OF 22, of "2 * real k powr (19 / 20)"] D85
        by (simp add: algebra_simps)
    next
      show "0 \<le> 1 - \<gamma> - \<eta>" "1 - \<gamma> - \<eta> \<le> 1"
        using assms \<gamma>01 by linarith+
    qed
    have "nV \<ge> 2"
      by (metis nontriv wellformed two_edges card_mono ex_in_conv finV)
    then have "nV \<le> 4 * (nV div 2)" by linarith
    also have "\<dots> \<le> 4 * card Y0"
      using Y0 mult_le_mono2 by presburger 
    finally show "real nV \<le> real (4 * card Y0)"      
      by force
  qed (use Y0 in auto)
  also have "\<dots> \<le> (1-\<gamma>-\<eta>) powr (t+s) / (1-\<gamma>-\<eta>) powr (4 * k powr (19/20)) * (4 * card Y0)"
    by (simp add: divide_powr_uminus powr_diff)
  also have "\<dots> \<le> (1-\<gamma>-\<eta>) powr (t+s) / (1/2) powr (4 * k powr (19/20)) * (4 * card Y0)"
  proof (intro mult_mono divide_left_mono)
    show "(1/2) powr (4 * k powr (19/20)) \<le> (1-\<gamma>-\<eta>) powr (4 * k powr (19/20))"
      using \<gamma>01 p0 \<open>0\<le>\<eta>\<close> by (intro powr_mono_both') auto
  qed (use p0 in auto)
  also have "\<dots> \<le> p0 powr (t+s) / (1/2) powr (4 * k powr (19/20)) * (4 * card Y0)"
    using p0 powr_mono2 by (intro mult_mono divide_right_mono) auto
  also have "\<dots> = (2 powr (2 + 4 * k powr (19/20))) * p0 ^ (t+s) * card Y0"
    using p0_01 by (simp add: powr_divide powr_add power_add powr_realpow)
  finally have "2 powr (ok_fun_95a k) * (1-\<gamma>-\<eta>) powr (t + \<gamma>*t / (1-\<gamma>)) * nV \<le> 2 powr (ok_fun_61 k) * p0 ^ (t+s) * card Y0"
    by (simp add: ok_fun_95a_def powr_diff field_simps)
  with 61 have *: "card (Yseq halted_point) \<ge> 2 powr (ok_fun_95a k) * (1-\<gamma>-\<eta>) powr (t + \<gamma>*t / (1-\<gamma>)) * nV"
    by linarith

  have F: "exp (ok_fun_95b k) = 2 powr ok_fun_95a k * exp (- 1)"
    by (simp add: ok_fun_95b_def exp_diff exp_minus powr_def field_simps)
  have "?rhs
   \<le> exp (-\<delta> * k) * 2 powr (ok_fun_95a k) * exp (-1) * (1-\<gamma>-\<eta>) powr (\<gamma>*t / (1-\<gamma>))
         * (((1-\<gamma>-\<eta>)/(1-\<gamma>)) ^t * exp (\<gamma> * (real t)\<^sup>2 / real(2*k)) * (k-t+l choose l))"
    unfolding exp_add F by simp
  also have "\<dots> \<le>  exp (-\<delta> * k) * 2 powr (ok_fun_95a k) * (1-\<gamma>-\<eta>) powr (\<gamma>*t / (1-\<gamma>))
         * (exp (-1) * ((1-\<gamma>-\<eta>)/(1-\<gamma>)) ^t * exp (\<gamma> * (real t)\<^sup>2 / real(2*k)) * (k-t+l choose l))"
    by (simp add: mult.assoc)
  also have "\<dots> \<le> 2 powr (ok_fun_95a k) * (1-\<gamma>-\<eta>) powr (t + \<gamma>*t / (1-\<gamma>)) * exp (-\<delta> * k)
                * (exp (-1) * (1-\<gamma>) powr (- real t) * exp (\<gamma> * (real t)\<^sup>2 / real(2*k)) * (k-t+l choose l))"
    using p0 \<gamma>01
    unfolding powr_add powr_minus by (simp add: mult_ac divide_simps flip: powr_realpow)
  also have "\<dots> \<le> 2 powr (ok_fun_95a k) * (1-\<gamma>-\<eta>) powr (t + \<gamma>*t / (1-\<gamma>)) * exp (-\<delta> * k) * (k+l choose l)"
  proof (cases "t=0")
    case False
    then show ?thesis
      unfolding \<gamma>_def using \<open>t<k\<close> by (intro mult_mono order_refl Far_9_6) auto
  qed auto
  also have "\<dots> \<le> 2 powr (ok_fun_95a k) * (1-\<gamma>-\<eta>) powr (t + \<gamma>*t / (1-\<gamma>)) * nV"
    using nV mult_left_mono by fastforce
  also have "\<dots> \<le> card (Yseq halted_point)"
    by (rule *)
  finally show ?thesis .
qed

subsection \<open>Lemma 9.2 actual proof\<close>

context P0_min
begin

lemma error_9_2:
  assumes "\<mu>>0" "d > 0"
  shows "\<forall>\<^sup>\<infinity>k. ok_fun_95b k + \<mu> * real k / d \<ge> 0"
proof -
  have "\<forall>\<^sup>\<infinity>k. \<bar>ok_fun_95b k\<bar> \<le> (\<mu>/d) * k"
    using ok_fun_95b assms unfolding smallo_def
    by (auto dest!: spec [where x = "\<mu>/d"])
  then show ?thesis
    by eventually_elim force
qed

definition "Big_Far_9_2 \<equiv> \<lambda>\<mu> l. Big_Far_9_3 \<mu> l \<and> Big_Far_9_5 \<mu> l \<and> (\<forall>k\<ge>l. ok_fun_95b k + \<mu>*k/60 \<ge> 0)"

lemma Big_Far_9_2:
  assumes "0<\<mu>0" "\<mu>0\<le>\<mu>1" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. \<mu>0 \<le> \<mu> \<and> \<mu> \<le> \<mu>1 \<longrightarrow> Big_Far_9_2 \<mu> l"
proof -
  have "\<forall>\<^sup>\<infinity>l. \<forall>k\<ge>l. (\<forall>\<mu>. \<mu>0 \<le> \<mu> \<and> \<mu> \<le> \<mu>1 \<longrightarrow> 0 \<le> ok_fun_95b k + \<mu> * k / 60)"
    using assms 
    apply (intro eventually_all_ge_at_top eventually_all_geI0 error_9_2)
     apply (auto simp: divide_right_mono mult_right_mono elim!: order_trans)
    done
  then show ?thesis
    using assms Big_Far_9_3 Big_Far_9_5
    unfolding Big_Far_9_2_def
    apply (simp add: eventually_conj_iff all_imp_conj_distrib)  
    by (smt (verit, ccfv_threshold) eventually_sequentially)
qed

end

lemma (in Book') Far_9_2_conclusion:
  defines "\<R> \<equiv> Step_class {red_step}"
  defines "t \<equiv> card \<R>"
  assumes Y: "(k-t+l choose l) \<le> card (Yseq halted_point)"
  shows False
proof -
  have "t<k"
    unfolding t_def \<R>_def using red_step_limit by blast
  have "RN (k-t) l \<le> card (Yseq halted_point)"
    by (metis Y add.commute RN_commute RN_le_choose le_trans)
  then obtain K 
    where Ksub: "K \<subseteq> Yseq halted_point" 
      and K: "card K = k-t \<and> clique K Red \<or> card K = l \<and> clique K Blue"
    by (meson Red_Blue_RN Yseq_subset_V size_clique_def)
  show False
    using K
  proof
    assume K: "card K = k - t \<and> clique K Red"
    have "clique (K \<union> Aseq halted_point) Red"
    proof (intro clique_Un)
      show "clique (Aseq halted_point) Red"
        by (meson A_Red_clique valid_state_seq)
      have "all_edges_betw_un (Aseq halted_point) (Yseq halted_point) \<subseteq> Red"
        using valid_state_seq Ksub
        by (auto simp: valid_state_def RB_state_def all_edges_betw_un_Un2)
      then show "all_edges_betw_un K (Aseq halted_point) \<subseteq> Red"
        using Ksub all_edges_betw_un_commute all_edges_betw_un_mono2 by blast
      show "K \<subseteq> V"
        using Ksub Yseq_subset_V by blast
    qed (use K Aseq_subset_V in auto)
    moreover have "card (K \<union> Aseq halted_point) = k"
    proof -
      have eqt: "card (Aseq halted_point) = t"
        using red_step_eq_Aseq \<R>_def t_def by simp
      have "card (K \<union> Aseq halted_point) = card K + card (Aseq halted_point) "
      proof (intro card_Un_disjoint)
        show "finite K"
          by (meson Ksub Yseq_subset_V finV finite_subset)
        have "disjnt (Yseq halted_point) (Aseq halted_point)"
          using valid_state_seq by (auto simp: valid_state_def disjoint_state_def)
        with Ksub show "K \<inter> Aseq halted_point = {}"
          by (auto simp: disjnt_def)
      qed (simp add: finite_Aseq)
      also have "\<dots> = k"
        using eqt K \<open>t < k\<close> by simp
      finally show ?thesis .
    qed
    moreover have "K \<union> Aseq halted_point \<subseteq> V"
      using Aseq_subset_V Ksub Yseq_subset_V by blast
    ultimately show False
      using no_Red_clique size_clique_def by blast
  next
    assume "card K = l \<and> clique K Blue"
    then show False
      using Ksub Yseq_subset_V no_Blue_clique size_clique_def by blast
  qed
qed


text \<open>A little tricky to express since the Book locale assumes that 
      there are no cliques in the original graph (page 9). So it's a contrapositive\<close>
lemma (in Book') Far_9_2_aux:
  fixes \<delta> \<eta>::real
  defines "\<delta> \<equiv> \<gamma>/20"
  assumes 0: "real (card X0) \<ge> nV/2" "card Y0 \<ge> nV div 2" "p0 \<ge> 1-\<gamma>-\<eta>"
     \<comment>\<open>These are the assumptions about the red density of the graph\<close>
  assumes \<gamma>: "\<gamma> \<le> 1/10" and \<eta>: "0\<le>\<eta>" "\<eta> \<le> \<gamma>/15"
  assumes nV: "real nV \<ge> exp (-\<delta> * k) * (k+l choose l)" 
  assumes big: "Big_Far_9_2 \<gamma> l"
  shows False
proof -
  define \<R> where "\<R> \<equiv> Step_class {red_step}"
  define t where "t \<equiv> card \<R>"
  have \<gamma>01: "0 < \<gamma>" "\<gamma> < 1"
    using ln0 l_le_k by (auto simp: \<gamma>_def)
  have big93: "Big_Far_9_3 \<gamma> l" 
    using big by (auto simp: Big_Far_9_2_def)
  have t23: "t \<ge> 2*k / 3"
    unfolding t_def \<R>_def
  proof (rule Far_9_3)
    show "\<gamma> \<le> 1/5"
      using \<gamma> unfolding \<gamma>_def by linarith
    have "min (1/200) (\<gamma> / 20) \<ge> \<delta>"
      unfolding \<delta>_def using \<gamma> ln0 by (simp add: \<gamma>_def)
    then show "exp (- min (1/200) (\<gamma> / 20) * k) * (k+l choose l) \<le> nV"
      using \<delta>_def \<gamma>_def nV by force
    show "1/4 \<le> p0"
      using \<eta> \<gamma> 0 by linarith
    show "Big_Far_9_3 (\<gamma>) l"
      using \<gamma>_def big93 by blast
  qed (use assms in auto)
  have "t<k"
    unfolding t_def \<R>_def using \<gamma>01 red_step_limit by blast

  have ge_half: "1/2 \<le> 1-\<gamma>-\<eta>"
    using \<gamma> \<eta> by linarith
  have "exp (-1/3 + (1/5::real)) \<le> exp (10/9 * ln (134/150))"
    by (approximation 9)
  also have "\<dots> \<le> exp (1 / (1-\<gamma>) * ln (134/150))"
    using \<gamma> by (auto simp: divide_simps)
  also have "\<dots> \<le> exp (1 / (1-\<gamma>) * ln (1-\<gamma>-\<eta>))"
    using \<gamma> \<eta> by (auto simp: divide_simps)
  also have "\<dots> = (1-\<gamma>-\<eta>) powr (1 / (1-\<gamma>))"
    using ge_half by (simp add: powr_def)
  finally have A: "exp (-1/3 + 1/5) \<le> (1-\<gamma>-\<eta>) powr (1 / (1-\<gamma>))" .

  have "3*t / (10*k) \<le> (-1/3 + 1/5) + t/(2*k)"
    using t23 kn0 by (simp add: divide_simps)
  from mult_right_mono [OF this, of "\<gamma>*t"] \<gamma>01
  have "3*\<gamma>*t\<^sup>2 / (10*k) \<le> \<gamma>*t*(-1/3 + 1/5) + \<gamma>*t\<^sup>2/(2*k)"
    by (simp add: eval_nat_numeral algebra_simps) 
  then have "exp (3*\<gamma>*t\<^sup>2 / (10*k)) \<le> exp (-1/3 + 1/5) powr (\<gamma>*t) * exp (\<gamma>*t\<^sup>2/(2*k))"
    by (simp add: mult_exp_exp exp_powr_real)
  also have "\<dots> \<le> (1-\<gamma>-\<eta>) powr ((\<gamma>*t) / (1-\<gamma>)) * exp (\<gamma>*t\<^sup>2/(2*k))"
    using \<gamma>01 powr_powr powr_mono2 [of "\<gamma>*t" "exp (-1/3 + 1/5)", OF _ _ A]
    by (intro mult_right_mono) auto
  finally have B: "exp (3*\<gamma>*t\<^sup>2 / (10*k)) \<le> (1-\<gamma>-\<eta>) powr ((\<gamma>*t) / (1-\<gamma>)) * exp (\<gamma>*t\<^sup>2/(2*k))" .

  have "(2*k / 3)^2 \<le> t\<^sup>2"
    using t23 by auto
  from kn0 \<gamma>01 mult_right_mono [OF this, of "\<gamma>/(80*k)"]
  have C: "\<delta>*k + \<gamma>*k/60 \<le> 3*\<gamma>*t\<^sup>2 / (20*k)"
    by (simp add: field_simps \<delta>_def eval_nat_numeral)

  have "exp (- 3*\<gamma>*t / (20*k)) \<le> exp (-3 * \<eta>/2)"
  proof -
    have "1 \<le> 3/2 * t/k"
      using t23 kn0 by (auto simp: divide_simps)
    from mult_right_mono [OF this, of "\<gamma>/15"] \<gamma>01 \<eta> 
    show ?thesis
      by simp
  qed
  also have "\<dots> \<le> 1 - \<eta> / (1-\<gamma>)"
  proof -
    have \<section>: "2/3 \<le> (1 - \<gamma> - \<eta>)"
      using \<gamma> \<eta> by linarith
    have "1 / (1-\<eta> / (1-\<gamma>)) = 1 + \<eta> / (1-\<gamma>-\<eta>)"
      using ge_half \<eta> by (simp add: divide_simps split: if_split_asm)
    also have "\<dots> \<le> 1 + 3 * \<eta> / 2"
      using mult_right_mono [OF \<section>, of \<eta>] \<eta> ge_half by (simp add: field_simps)
    also have "\<dots> \<le> exp (3 * \<eta> / 2)"
      using exp_minus_ge [of "-3*\<eta>/2"] by simp
    finally show ?thesis
      using \<gamma>01 ge_half 
      by (simp add: exp_minus divide_simps mult.commute split: if_split_asm)
  qed
  also have "\<dots> = (1-\<gamma>-\<eta>) / (1-\<gamma>)"
    using \<gamma>01 by (simp add: divide_simps)
  finally have "exp (- 3*\<gamma>*t / (20*k)) \<le> (1-\<gamma>-\<eta>) / (1-\<gamma>)" .
  from powr_mono2 [of t, OF _ _ this] ge_half \<gamma>01
  have D: "exp (- 3*\<gamma>*t\<^sup>2 / (20*k)) \<le> ((1-\<gamma>-\<eta>) / (1-\<gamma>))^t"
    by (simp add: eval_nat_numeral powr_powr exp_powr_real mult_ac flip: powr_realpow)

  have "(k-t+l choose l) \<le> card (Yseq halted_point)"
  proof -
    have "1 * real(k-t+l choose l) 
            \<le> exp (ok_fun_95b k + \<gamma>*k/60) * (k-t+l choose l)"
      using big l_le_k unfolding Big_Far_9_2_def
      by (intro mult_right_mono mult_ge1_I) auto
    also have "\<dots> \<le> exp (3*\<gamma>*t\<^sup>2 / (20*k) + -\<delta> * k + ok_fun_95b k) * (k-t+l choose l)"
      using C by simp
    also have "\<dots> = exp (3*\<gamma>*t\<^sup>2 / (10*k)) * exp (-\<delta> * k + ok_fun_95b k) * exp (- 3*\<gamma>*t\<^sup>2 / (20*k))
            * (k-t+l choose l)"
      by (simp flip: exp_add)
    also have "\<dots> \<le> exp (3*\<gamma>*t\<^sup>2 / (10*k)) * exp (-\<delta> * k + ok_fun_95b k) * ((1-\<gamma>-\<eta>)/(1-\<gamma>))^t 
            * (k-t+l choose l)"
      using \<gamma>01 ge_half D by (intro mult_right_mono) auto
    also have "\<dots> \<le> (1-\<gamma>-\<eta>) powr (\<gamma>*t / (1-\<gamma>)) * exp (\<gamma> * t\<^sup>2 / (2*k)) * exp (-\<delta> * k + ok_fun_95b k) 
                  * ((1-\<gamma>-\<eta>)/(1-\<gamma>))^t * (k-t+l choose l)"
      using \<gamma>01 ge_half by (intro mult_right_mono B) auto
    also have "\<dots> = exp (-\<delta> * k + ok_fun_95b k) * (1-\<gamma>-\<eta>) powr (\<gamma>*t / (1-\<gamma>)) * ((1-\<gamma>-\<eta>)/(1-\<gamma>))^t 
                  * exp (\<gamma> * (real t)\<^sup>2 / (2*k)) * (k-t+l choose l)"
      by (simp add: mult_ac)
    also have 95: "\<dots> \<le> real (card (Yseq halted_point))"
      unfolding t_def \<R>_def
    proof (rule Far_9_5)
      show "1/2 \<le> 1 - \<gamma> - \<eta>"
        using ge_half \<gamma>_def by blast
      show "Big_Far_9_5 (\<gamma>) l"
        using Big_Far_9_2_def big unfolding \<gamma>_def by presburger
    qed (use assms in auto)
    finally show ?thesis by simp
  qed
  then show False
    using Far_9_2_conclusion by (simp flip: \<R>_def t_def)
qed

text \<open>Mediation of 9.2 (and 10.2) from locale @{term Book_Basis} to the book locales
   with the starting sets of equal size\<close>
lemma (in No_Cliques) Basis_imp_Book:
  assumes gd: "p0_min \<le> graph_density Red"
  assumes \<mu>01: "0 < \<mu>" "\<mu> < 1"
  obtains X0 Y0 where "l\<ge>2" "card X0 \<ge> real nV / 2" "card Y0 = gorder div 2" 
    and "X0 = V \<setminus> Y0" "Y0\<subseteq>V" 
    and "graph_density Red \<le> gen_density Red X0 Y0"
    and "Book V E p0_min Red Blue l k \<mu> X0 Y0" 
proof -
  have "Red \<noteq> {}"
    using gd p0_min by (auto simp: graph_density_def)
  then have "gorder \<ge> 2"
    by (metis Red_E card_mono equals0I finV subset_empty two_edges wellformed)
  then have div2: "0 < gorder div 2" "gorder div 2 < gorder"
    by auto
  then obtain Y0 where Y0: "card Y0 = gorder div 2" "Y0\<subseteq>V" 
    "graph_density Red \<le> gen_density Red (V\<setminus>Y0) Y0"
    by (metis complete Red_E exists_density_edge_density gen_density_commute)
  define X0 where "X0 \<equiv> V \<setminus> Y0" 
  interpret Book V E p0_min Red Blue l k \<mu> X0 Y0
  proof
    show "X0\<subseteq>V" "disjnt X0 Y0"
      by (auto simp: X0_def disjnt_iff)
    show "p0_min \<le> gen_density Red X0 Y0"
      using X0_def Y0 gd gen_density_commute p0_min by auto
  qed (use assms \<open>Y0\<subseteq>V\<close> in auto)
  have False if "l<2"
    using that unfolding less_2_cases_iff
  proof
    assume "l = Suc 0" 
    with Y0 div2 show False
      by (metis RN_1' no_Red_clique no_Blue_clique Red_Blue_RN Suc_leI kn0)
  qed (use ln0 in auto)
  with l_le_k have "l\<ge>2"
    by force
  have card_X0: "card X0 \<ge> nV/2"
    using Y0 \<open>Y0\<subseteq>V\<close> unfolding X0_def
    by (simp add: card_Diff_subset finite_Y0)
  then show thesis
    using Book_axioms X0_def Y0 \<open>2 \<le> l\<close> that by blast
qed

text \<open>Material that needs to be proved \textbf{outside} the book locales\<close>

text \<open>As above, for @{term Book'}\<close>
lemma (in No_Cliques) Basis_imp_Book':
  assumes gd: "p0_min \<le> graph_density Red"
  assumes l: "0<l" "l\<le>k"
  obtains X0 Y0 where "l\<ge>2" "card X0 \<ge> real nV / 2" "card Y0 = gorder div 2" and "X0 = V \<setminus> Y0" "Y0\<subseteq>V" 
    and "graph_density Red \<le> gen_density Red X0 Y0"
    and "Book' V E p0_min Red Blue l k (real l / (real k + real l)) X0 Y0" 
proof -
  define \<gamma> where "\<gamma> \<equiv> real l / (real k + real l)"
  have "0 < \<gamma>" "\<gamma> < 1"
    using l by (auto simp: \<gamma>_def)
  with assms Basis_imp_Book [of  \<gamma>]
  obtain X0 Y0 where *: "l\<ge>2" "card X0 \<ge> real nV / 2" "card Y0 = gorder div 2" "X0 = V \<setminus> Y0" "Y0\<subseteq>V" 
    "graph_density Red \<le> gen_density Red X0 Y0" "Book V E p0_min Red Blue l k \<gamma> X0 Y0"
    by blast
  then interpret Book V E p0_min Red Blue l k \<gamma> X0 Y0
    by blast
  have "Book' V E p0_min Red Blue l k \<gamma> X0 Y0"
    using Book' \<gamma>_def by auto
  with * assms show ?thesis
    using \<gamma>_def  that by blast
qed

lemma (in No_Cliques) Far_9_2:
  fixes \<delta> \<gamma> \<eta>::real
  defines "\<gamma> \<equiv> l / (real k + real l)"
  defines "\<delta> \<equiv> \<gamma>/20"
  assumes nV: "real nV \<ge> exp (-\<delta> * k) * (k+l choose l)" 
  assumes gd: "graph_density Red \<ge> 1-\<gamma>-\<eta>" and p0_min_OK: "p0_min \<le> 1-\<gamma>-\<eta>"  
  assumes big: "Big_Far_9_2 \<gamma> l" 
  assumes "\<gamma> \<le> 1/10" and \<eta>: "0\<le>\<eta>" "\<eta> \<le> \<gamma>/15"
  shows False
proof -
  obtain X0 Y0 where "l\<ge>2" and card_X0: "card X0 \<ge> real nV / 2" 
    and card_Y0: "card Y0 = gorder div 2" 
    and X0_def: "X0 = V \<setminus> Y0" and "Y0\<subseteq>V" 
    and gd_le: "graph_density Red \<le> gen_density Red X0 Y0"
    and "Book' V E p0_min Red Blue l k \<gamma> X0 Y0" 
    using Basis_imp_Book' assms p0_min no_Red_clique no_Blue_clique ln0 by auto
  then interpret Book' V E p0_min Red Blue l k \<gamma> X0 Y0
    by blast 
  show False
  proof (intro Far_9_2_aux [of \<eta>])
    show "1 - \<gamma> - \<eta> \<le> p0"
      using X0_def \<gamma>_def gd gd_le gen_density_commute p0_def by auto
  qed (use assms card_X0 card_Y0 in auto)
qed

subsection \<open>Theorem 9.1\<close>

text \<open>An arithmetical lemma proved outside of the locales\<close>
lemma kl_choose: 
  fixes l k::nat
  assumes "m<l" "k>0"
  defines "PM \<equiv> \<Prod>i<m. (l - real i) / (k+l-real i)"
  shows "(k+l choose l) = (k+l-m choose (l-m)) / PM"
proof -
  have inj: "inj_on (\<lambda>i. i-m) {m..<l}" \<comment>\<open>relating the power and binomials; maybe easier using factorials\<close>
    by (auto simp: inj_on_def)
  have "(\<Prod>i<l. (k+l-i) / (l-i)) / (\<Prod>i<m. (k+l-i) / (l-i))
      = (\<Prod>i = m..<l. (k+l-i) / (l-i))"
    using prod_divide_nat_ivl [of 0 m l "\<lambda>i. (k+l-i) / (l-i)"] \<open>m < l\<close>
    by (simp add: atLeast0LessThan)
  also have "\<dots> = (\<Prod>i<l - m. (k+l-m - i) / (l-m-i))"
    apply (intro prod.reindex_cong [OF inj, symmetric])
    by (auto simp: image_minus_const_atLeastLessThan_nat)
  finally
  have "(\<Prod>i < l-m. (k+l-m - i) / (l-m-i)) 
      = (\<Prod>i < l. (k+l-i) / (l-i)) / (\<Prod>i<m. (k+l-i) / (l-i))" 
    by linarith
  also have "\<dots> = (k+l choose l) * inverse (\<Prod>i<m. (k+l-i) / (l-i))"
    by (simp add: field_simps atLeast0LessThan binomial_altdef_of_nat) 
  also have "\<dots> = (k+l choose l) * PM"
    unfolding PM_def using \<open>m < l\<close> \<open>k>0\<close>
    by (simp add: atLeast0LessThan flip: prod_inversef)
  finally have "(k+l-m choose (l-m)) = (k+l choose l) * PM"
    by (simp add: atLeast0LessThan binomial_altdef_of_nat)
  then show "real(k+l choose l) = (k+l-m choose (l-m)) / PM"
    by auto
qed


context P0_min
begin

text \<open>The proof considers a smaller graph, so @{term l} needs to be so big
   that the smaller @{term l'} will be big enough.\<close>
definition Big_Far_9_1 :: "real \<Rightarrow> nat \<Rightarrow> bool" where
  "Big_Far_9_1 \<equiv> \<lambda>\<mu> l. l\<ge>3 \<and> (\<forall>l' \<gamma>. real l' \<ge> (10/11) * \<mu> * real l \<longrightarrow> \<mu>\<^sup>2 \<le> \<gamma> \<and> \<gamma> \<le> 1/10 \<longrightarrow> Big_Far_9_2 \<gamma> l')"

text \<open>The proof of theorem 10.1 requires a range of values\<close>
lemma Big_Far_9_1:
  assumes "0<\<mu>0" "\<mu>0\<le>1/10"
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. \<mu>0 \<le> \<mu> \<and> \<mu> \<le> 1/10 \<longrightarrow> Big_Far_9_1 \<mu> l"
proof -
  have "\<mu>0\<^sup>2 \<le> 1/10"
    using assms by (smt (verit, ccfv_threshold) le_divide_eq_1 mult_left_le power2_eq_square)
  then have "\<forall>\<^sup>\<infinity>l. \<forall>\<gamma>. \<mu>0\<^sup>2 \<le> \<gamma> \<and> \<gamma> \<le> 1/10 \<longrightarrow> Big_Far_9_2 \<gamma> l"
    using assms by (intro Big_Far_9_2) auto
  then obtain N where N: "\<forall>l\<ge>N. \<forall>\<gamma>. \<mu>0\<^sup>2 \<le> \<gamma> \<and> \<gamma> \<le> 1/10 \<longrightarrow> Big_Far_9_2 \<gamma> l"
    using eventually_sequentially by auto
  define M where "M \<equiv> nat\<lceil>11*N / (10*\<mu>0)\<rceil>"
  have "(10/11) * \<mu>0 * l \<ge> N" if "l \<ge> M" for l
    using that by (simp add: M_def \<open>\<mu>0>0\<close> mult_of_nat_commute pos_divide_le_eq)
  with N have "\<forall>l\<ge>M. \<forall>l' \<gamma>. (10/11) * \<mu>0 * l \<le> l' \<longrightarrow> \<mu>0\<^sup>2 \<le> \<gamma> \<and> \<gamma> \<le> 1 / 10 \<longrightarrow> Big_Far_9_2 \<gamma> l'"
    by (smt (verit, ccfv_SIG) of_nat_le_iff)
  then have "\<forall>\<^sup>\<infinity>l. \<forall>l' \<gamma>. (10/11) * \<mu>0 * l \<le> l' \<longrightarrow> \<mu>0\<^sup>2 \<le> \<gamma> \<and> \<gamma> \<le> 1 / 10 \<longrightarrow> Big_Far_9_2 \<gamma> l'"
    by (auto simp: eventually_sequentially)
  moreover have "\<forall>\<^sup>\<infinity>l. l\<ge>3"
    by simp
  ultimately show ?thesis
    unfolding Big_Far_9_1_def 
    apply eventually_elim
    by (smt (verit) \<open>0<\<mu>0\<close> mult_left_mono mult_right_mono of_nat_less_0_iff power_mono zero_less_mult_iff)
qed

text \<open>The text claims the result for all @{term k} and @{term l}, not just those sufficiently large,
  but the $o(k)$ function allowed in the exponent provides a fudge factor\<close>
theorem Far_9_1:
  fixes l k::nat
  fixes \<delta> \<gamma>::real
  defines "\<gamma> \<equiv> real l / (real k + real l)"
  defines "\<delta> \<equiv> \<gamma>/20"
  assumes \<gamma>: "\<gamma> \<le> 1/10" 
  assumes big: "Big_Far_9_1 \<gamma> l"
  assumes p0_min_91: "p0_min \<le> 1 - (1/10) * (1 + 1/15)"
  shows "RN k l \<le> exp (-\<delta>*k + 1) * (k+l choose l)"
proof (rule ccontr)
  assume non: "\<not> RN k l \<le> exp (-\<delta> * k + 1) * (k+l choose l)"
  with RN_eq_0_iff have "l>0" by force
  with \<gamma> have l9k: "9*l \<le> k"
    by (auto simp: \<gamma>_def divide_simps)
  have "l\<le>k"
    using \<gamma>_def \<gamma> nat_le_real_less by fastforce
  with \<open>l>0\<close> have "k>0" by linarith
  define \<xi>::real where "\<xi> \<equiv> 1/15"
  define U_lower_bound_ratio where \<comment>\<open>Bhavik's name\<close>
    "U_lower_bound_ratio \<equiv> \<lambda>m. (1+\<xi>)^m * (\<Prod>i<m. (l - real i) / (k+l - real i))"

  define n where "n \<equiv> RN k l - 1"
  have "l\<ge>3"
    using big by (auto simp: Big_Far_9_1_def)
  have "k\<ge>27"
    using l9k \<open>l\<ge>3\<close> by linarith
  have "exp 1 / (exp 1 - 2) < (27::real)"
    by (approximation 5)
  also have RN27: "\<dots> \<le> RN k l"
    by (meson RN_3plus' \<open>l\<ge>3\<close> \<open>k\<ge>27\<close> le_trans numeral_le_real_of_nat_iff)
  finally have "exp 1 / (exp 1 - 2) < RN k l" .
  moreover have "n < RN k l"
    using RN27 by (simp add: n_def)
  moreover have "2 < exp (1::real)"
    by (approximation 5)
  ultimately have nRNe: "n/2 > RN k l / exp 1"
    by (simp add: n_def field_split_simps)

  have "(k+l choose l) / exp (-1 + \<delta>*k) < RN k l"
    by (smt (verit) divide_inverse exp_minus mult_minus_left mult_of_nat_commute non)
  then have "(RN k l / exp 1) * exp (\<delta>*k) > (k+l choose l)"
    unfolding exp_add exp_minus by (simp add: field_simps)
  with nRNe have n2exp_gt: "(n/2) * exp (\<delta>*k) > (k+l choose l)"
    by (smt (verit, best) exp_gt_zero mult_le_cancel_right_pos)
  then have nexp_gt: "n * exp (\<delta>*k) > (k+l choose l)"
    by simp

  define V where "V \<equiv> {..<n}"
  define E where "E \<equiv> all_edges V" 
  interpret Book_Basis V E
  proof qed (auto simp: V_def E_def comp_sgraph.wellformed comp_sgraph.two_edges)
  have [simp]: "nV = n"
    by (simp add: V_def)
  then obtain Red Blue
    where Red_E: "Red \<subseteq> E" and Blue_def: "Blue = E-Red" 
      and no_Red_K: "\<not> (\<exists>K. size_clique k K Red)"
      and no_Blue_K: "\<not> (\<exists>K. size_clique l K Blue)"
    by (metis \<open>n < RN k l\<close> less_RN_Red_Blue)
  have Blue_E: "Blue \<subseteq> E" and disjnt_Red_Blue: "disjnt Red Blue" 
  and  Blue_eq: "Blue = all_edges V - Red"
    using complete by (auto simp: Blue_def disjnt_iff E_def) 
  define is_good_clique where
    "is_good_clique \<equiv> \<lambda>i K. clique K Blue \<and> K \<subseteq> V \<and>
                                 card (V \<inter> (\<Inter>w\<in>K. Neighbours Blue w))
                                 \<ge> real i * U_lower_bound_ratio (card K) - card K"
  have is_good_card: "card K < l" if "is_good_clique i K" for i K
    using no_Blue_K that unfolding is_good_clique_def 
    by (metis nat_neq_iff size_clique_def size_clique_smaller)
  define GC where "GC \<equiv> {C. is_good_clique n C}"
  have "GC \<noteq> {}"
    by (auto simp: GC_def is_good_clique_def U_lower_bound_ratio_def E_def V_def)
  have "GC \<subseteq> Pow V"
    by (auto simp: is_good_clique_def GC_def)
  then have "finite GC"
    by (simp add: finV finite_subset)
  then obtain W where "W \<in> GC" and MaxW: "Max (card ` GC) = card W"
    using \<open>GC \<noteq> {}\<close> obtains_MAX by blast
  then have 49: "is_good_clique n W"
    using GC_def by blast
  have max49: "\<not> is_good_clique n (insert x W)" if "x\<in>V\<setminus>W" for x
  proof 
    assume x: "is_good_clique n (insert x W)"
    then have "card (insert x W) = Suc (card W)"
      using finV is_good_clique_def finite_subset that by fastforce
    with x \<open>finite GC\<close> have "Max (card ` GC) \<ge> Suc (card W)"
      by (simp add: GC_def rev_image_eqI)
    then show False
      by (simp add: MaxW)
  qed

  have "W\<subseteq>V"
    using 49 by (auto simp: is_good_clique_def)
  define m where "m \<equiv> card W"
  define \<gamma>' where "\<gamma>' \<equiv> (l - real m) / (k+l-real m)"
  define \<eta> where "\<eta> \<equiv> \<xi> * \<gamma>'"

  have Red_Blue_RN: "\<exists>K \<subseteq> X. size_clique m K Red \<or> size_clique n K Blue"
    if "card X \<ge> RN m n" "X\<subseteq>V" for m n and X 
    using partn_lst_imp_is_clique_RN [OF is_Ramsey_number_RN [of m n]] finV that  
    unfolding is_clique_RN_def size_clique_def clique_indep_def Blue_eq 
    by (metis clique_iff_indep finite_subset subset_trans)
  define U where "U \<equiv> V \<inter> (\<Inter>w\<in>W. Neighbours Blue w)"
  define EU where "EU \<equiv> E \<inter> Pow U"
  define RedU where "RedU \<equiv> Red \<inter> Pow U"
  define BlueU where "BlueU \<equiv> Blue \<inter> Pow U"

  have "RN k l > 0"
    using \<open>n < RN k l\<close> by auto
  have "\<gamma>' > 0"
    using is_good_card [OF 49] by (simp add: \<gamma>'_def m_def)
  then have "\<eta> > 0"
    by (simp add: \<eta>_def \<xi>_def)
  have "finite W"
    using \<open>W \<subseteq> V\<close> finV finite_subset by (auto simp: V_def)
  have "U \<subseteq> V" and VUU: "V \<inter> U = U"
    by (force simp: U_def)+
  have "disjnt U W"
    using Blue_E not_own_Neighbour unfolding E_def V_def U_def disjnt_iff by blast
  have "m<l"
    using 49 is_good_card m_def by blast
  then have \<gamma>1516: "\<gamma>' \<le> 15/16"
    using \<gamma>_def \<gamma> by (simp add: \<gamma>'_def divide_simps)
  then have \<gamma>'_le1: "(1+\<xi>) * \<gamma>' \<le> 1"
    by (simp add: \<xi>_def)

  have cardU: "n * U_lower_bound_ratio m \<le> m + card U"
    using 49 VUU unfolding is_good_clique_def U_def m_def by force
  obtain [iff]: "finite RedU" "finite BlueU" "RedU \<subseteq> EU"
    using BlueU_def EU_def RedU_def E_def V_def Red_E Blue_E fin_edges finite_subset by blast 
  have card_RedU_le: "card RedU \<le> card EU"
    by (metis EU_def E_def \<open>RedU \<subseteq> EU\<close> card_mono fin_all_edges finite_Int)
  interpret UBB: Book_Basis U "E \<inter> Pow U" p0_min 
  proof
    fix e 
    assume "e \<in> E \<inter> Pow U"
    with two_edges show "e \<subseteq> U" "card e = 2" by auto
  next
    show "finite U"
      using \<open>U \<subseteq> V\<close> by (simp add: V_def finite_subset)
    have "x \<in> E" if "x \<in> all_edges U" for x 
      using \<open>U \<subseteq> V\<close> all_edges_mono that complete E_def by blast
    then show "E \<inter> Pow U = all_edges U"
      using comp_sgraph.wellformed \<open>U \<subseteq> V\<close> by (auto intro: e_in_all_edges_ss)
  qed auto

  have clique_W: "size_clique m W Blue"
    using 49 is_good_clique_def size_clique_def V_def m_def by blast

  define PM where "PM \<equiv> \<Prod>i<m. (l - real i) / (k+l-real i)"
  then have U_lower_m: "U_lower_bound_ratio m = (1+\<xi>)^m * PM"
    using U_lower_bound_ratio_def by blast
  have prod_gt0: "PM > 0"
    unfolding PM_def using \<open>m<l\<close> by (intro prod_pos) auto

  have kl_choose: "real(k+l choose l) = (k+l-m choose (l-m)) / PM"
    unfolding PM_def using kl_choose \<open>0 < k\<close> \<open>m < l\<close> by blast
  \<comment>\<open>Now a huge effort just to show that @{term U} is nontrivial.
     Proof probably shows its cardinality exceeds a multiple of @{term l}\<close>
  define ekl20 where "ekl20 \<equiv> exp (k / (20*(k+l)))"
  have ekl20_eq: "exp (\<delta>*k) = ekl20^l"
      by (simp add: \<delta>_def \<gamma>_def ekl20_def field_simps flip: exp_of_nat2_mult)
  have "ekl20 \<le> exp(1/20)"
    unfolding ekl20_def using \<open>m < l\<close> by fastforce
  also have "\<dots> \<le> (1+\<xi>)"
    unfolding \<xi>_def by (approximation 10)
  finally have exp120: "ekl20 \<le> 1 + \<xi>" .
  have ekl20_gt0: "0 < ekl20"
    by (simp add: ekl20_def)

  have "3*l + Suc l - q \<le> (k+q choose q) / exp(\<delta>*k) * (1+\<xi>) ^ (l - q)"
    if "1\<le>q" "q\<le>l" for q
    using that
  proof (induction q rule: nat_induct_at_least)
    case base
    have "ekl20^l = ekl20^(l-1) * ekl20"
      by (metis \<open>0 < l\<close> power_minus_mult)
    also have "\<dots> \<le> (1+\<xi>) ^ (l-1) * ekl20"
      using ekl20_def exp120 power_mono by fastforce
    also have "\<dots> \<le> 2 * (1+\<xi>) ^ (l-1)"
    proof -
      have \<section>: "ekl20 \<le> 2"
        using \<xi>_def exp120 by linarith
      from mult_right_mono [OF this, of "(1+\<xi>) ^ (l-1)"] 
      show ?thesis by (simp add: mult_ac \<xi>_def)
    qed
    finally have "ekl20^l \<le> 2 * (1+\<xi>) ^ (l-1)"
      by argo 
    then have "1/2 \<le> (1+\<xi>) ^ (l-1) / ekl20^l"
      using ekl20_def by auto
    moreover have "4 * real l / (1 + real k) \<le> 1/2"
      using l9k by (simp add: divide_simps)
    ultimately have "4 * real l / (1 + real k) \<le> (1+\<xi>) ^ (l-1) / ekl20^l"
      by linarith
    then show ?case
      by (simp add: field_simps ekl20_eq)
  next
    case (Suc q)
    then have \<ddagger>: "(1+\<xi>) ^ (l - q) = (1+\<xi>) * (1+\<xi>) ^ (l - Suc q)"
      by (metis Suc_diff_le diff_Suc_Suc power.simps(2))
    have "real(k + q choose q) \<le> real(k + q choose Suc q)" "0 \<le> (1+\<xi>) ^ (l - Suc q)"
      using \<open>Suc q \<le> l\<close> l9k by (auto simp: \<xi>_def binomial_mono) 
    from mult_right_mono [OF this]
    have "(k + q choose q) * (1+\<xi>) ^ (l - q) / exp (\<delta> * k) - 1 
        \<le> (real (k + q choose q) + (k + q choose Suc q)) * (1+\<xi>) ^ (l - Suc q) / exp (\<delta> * k)"
      unfolding \<ddagger> by (simp add: \<xi>_def field_simps add_increasing)
    with Suc show ?case by force      
  qed
  from \<open>m<l\<close> this [of "l-m"] 
  have "1 + 3*l + real m \<le> (k+l-m choose (l-m)) / exp \<delta> ^ k * (1+\<xi>) ^ m"
    by (simp add: Suc_leI exp_of_nat2_mult)
  also have "\<dots> \<le> (k+l-m choose (l-m)) / exp (\<delta> * k) * (1+\<xi>) ^ m"
    by (simp add: exp_of_nat2_mult)
  also have "\<dots> < PM * (real n * (1+\<xi>) ^ m)"
  proof -
    have \<section>: "(k+l choose l) / exp (\<delta> * k) < n"
      by (simp add: less_eq_real_def nexp_gt pos_divide_less_eq)
    show ?thesis
      using mult_strict_left_mono [OF \<section>, of "PM * (1+\<xi>) ^ m"] kl_choose prod_gt0
      by (auto simp: field_simps \<xi>_def)
  qed
  also have "\<dots> = real n * U_lower_bound_ratio m"
    by (simp add: U_lower_m)
  finally have U_MINUS_M: "3*l + 1 < real n * U_lower_bound_ratio m - m"
    by linarith
  then have cardU_gt: "card U > 3*l + 1"
    using cardU by linarith
  with UBB.complete have "card EU > 0" "card U > 1"
    by (simp_all add: EU_def UBB.finV card_all_edges)
  have BlueU_eq: "BlueU = EU \<setminus> RedU" 
    using Blue_eq complete by (fastforce simp: BlueU_def RedU_def EU_def V_def E_def)
  have [simp]: "UBB.graph_size = card EU"
    using EU_def by blast
  have "\<gamma>' \<le> \<gamma>"
    using \<open>m<l\<close> \<open>k>0\<close> by (simp add: \<gamma>_def \<gamma>'_def field_simps)
  have False if "UBB.graph_density RedU < 1 - \<gamma>' - \<eta>"
  proof -    \<comment>\<open>by maximality, etc.\<close>
    have \<section>: "UBB.graph_density BlueU \<ge> \<gamma>' + \<eta>" 
      using that \<open>card EU > 0\<close> card_RedU_le 
      by (simp add: BlueU_eq UBB.graph_density_def diff_divide_distrib card_Diff_subset)
    have Nx: "Neighbours BlueU x \<inter> (U \<setminus> {x}) = Neighbours BlueU x" for x 
      using that by (auto simp: BlueU_eq EU_def Neighbours_def)
    have "BlueU \<subseteq> E \<inter> Pow U"
      using BlueU_eq EU_def by blast
    with UBB.exists_density_edge_density [of 1 BlueU]
    obtain x where "x\<in>U" and x: "UBB.graph_density BlueU \<le> UBB.gen_density BlueU {x} (U\<setminus>{x})"
      by (metis UBB.complete \<open>1 < UBB.gorder\<close> card_1_singletonE insertI1 zero_less_one subsetD)
    with \<section> have "\<gamma>' + \<eta> \<le> UBB.gen_density BlueU (U\<setminus>{x}) {x}"
      using UBB.gen_density_commute by auto
    then have *: "(\<gamma>' + \<eta>) * (card U - 1) \<le> card (Neighbours BlueU x)"
      using \<open>BlueU \<subseteq> E \<inter> Pow U\<close> \<open>card U > 1\<close> \<open>x \<in> U\<close>
      by (simp add: UBB.gen_density_def UBB.edge_card_eq_sum_Neighbours UBB.finV divide_simps Nx)

    have x: "x \<in> V\<setminus>W"
      using \<open>x \<in> U\<close> \<open>U \<subseteq> V\<close> \<open>disjnt U W\<close> by (auto simp: U_def disjnt_iff)
    moreover
    have "is_good_clique n (insert x W)"
      unfolding is_good_clique_def
    proof (intro conjI)
      show "clique (insert x W) Blue"
      proof (intro clique_insert)
        show "clique W Blue"
          using 49 is_good_clique_def by blast
        show "all_edges_betw_un {x} W \<subseteq> Blue"
          using \<open>x\<in>U\<close> by (auto simp: U_def all_edges_betw_un_def insert_commute in_Neighbours_iff)
      qed (use \<open>W \<subseteq> V\<close> \<open>x \<in> V\<setminus>W\<close> in auto)
    next
      show "insert x W \<subseteq> V"
        using \<open>W \<subseteq> V\<close> \<open>x \<in> V\<setminus>W\<close> by auto
    next
      have NB_Int_U: "Neighbours Blue x \<inter> U = Neighbours BlueU x"
        using \<open>x \<in> U\<close> by (auto simp: BlueU_def U_def Neighbours_def)
      have ulb_ins: "U_lower_bound_ratio (card (insert x W)) = U_lower_bound_ratio m * (1+\<xi>) * \<gamma>'"
        using \<open>x \<in> V\<setminus>W\<close> \<open>finite W\<close> by (simp add: U_lower_bound_ratio_def \<gamma>'_def m_def)
      have "n * U_lower_bound_ratio (card (insert x W))  = n * U_lower_bound_ratio m * (1+\<xi>) * \<gamma>'"
        by (simp add: ulb_ins)
      also have "\<dots> \<le> real (m + card U) * (1+\<xi>) * \<gamma>'"
        using mult_right_mono [OF cardU, of "(1+\<xi>) * \<gamma>'"] \<open>0 < \<eta>\<close> \<open>0 < \<gamma>'\<close> \<eta>_def by argo
      also have "\<dots> \<le> m + card U * (1+\<xi>) * \<gamma>'"
        using mult_left_mono [OF \<gamma>'_le1, of m] by (simp add: algebra_simps)
      also have "\<dots> \<le> Suc m + (\<gamma>' + \<eta>) * (UBB.gorder - Suc 0)"
        using * \<open>x \<in> V\<setminus>W\<close> \<open>finite W\<close> cardU_gt \<gamma>1516
        apply (simp add: U_lower_bound_ratio_def \<xi>_def \<eta>_def)
        by (simp add: algebra_simps)
      also have "\<dots> \<le> Suc m + card (V \<inter> \<Inter> (Neighbours Blue ` insert x W))"
        using * NB_Int_U finV by (simp add: U_def Int_ac)
      also have "\<dots> = real (card (insert x W) + card (V \<inter> \<Inter> (Neighbours Blue ` insert x W)))"
        using x \<open>finite W\<close> VUU by (auto simp: U_def m_def)
      finally show "n * U_lower_bound_ratio (card(insert x W)) - card(insert x W)
                   \<le> card (V \<inter> \<Inter> (Neighbours Blue ` insert x W))" 
        by simp
    qed
    ultimately show False
      using max49 by blast
  qed
  then have gd_RedU_ge: "UBB.graph_density RedU \<ge> 1 - \<gamma>' - \<eta>" by force

  \<comment>\<open>Bhavik's gamma'\_le\_gamma\_iff\<close>
  have \<gamma>'\<gamma>2: "\<gamma>' < \<gamma>\<^sup>2 \<longleftrightarrow> (real k * real l) + (real l * real l) < (real k * real m) + (real l * (real m * 2))"
    using \<open>m < l\<close>
    apply (simp add: \<gamma>'_def \<gamma>_def eval_nat_numeral divide_simps; simp add: algebra_simps)
    by (metis \<open>k>0\<close> mult_less_cancel_left_pos of_nat_0_less_iff distrib_left)
  also have "\<dots>  \<longleftrightarrow> (l * (k+l)) / (k + 2 * l) < m"
    using \<open>m < l\<close> by (simp add: field_simps)
  finally have \<gamma>'\<gamma>2_iff: "\<gamma>' < \<gamma>\<^sup>2 \<longleftrightarrow> (l * (k+l)) / (k + 2 * l) < m" .
  \<comment>\<open>in both cases below, we find a blue clique of size @{term"l-m"}\<close>
  have extend_Blue_clique: "\<exists>K'. size_clique l K' Blue" 
    if "K \<subseteq> U" "size_clique (l-m) K Blue" for K
  proof -
    have K: "card K = l-m" "clique K Blue"
      using that by (auto simp: size_clique_def)
    define K' where "K' \<equiv> K \<union> W"
    have "card K' = l"
      unfolding K'_def
    proof (subst card_Un_disjnt)
      show "finite K" "finite W"
        using UBB.finV \<open>K \<subseteq> U\<close> finite_subset \<open>finite W\<close> by blast+
      show "disjnt K W"
        using \<open>disjnt U W\<close> \<open>K \<subseteq> U\<close> disjnt_subset1 by blast
      show "card K + card W = l"
        using K \<open>m < l\<close> m_def by auto
    qed
    moreover have "clique K' Blue"
      using \<open>clique K Blue\<close> clique_W \<open>K \<subseteq> U\<close>
      unfolding K'_def size_clique_def U_def 
      by (force simp: in_Neighbours_iff insert_commute intro: Ramsey.clique_Un)
    ultimately show ?thesis
      unfolding K'_def size_clique_def using \<open>K \<subseteq> U\<close> \<open>U \<subseteq> V\<close> \<open>W \<subseteq> V\<close> by auto
  qed

  show False
  proof (cases "\<gamma>' < \<gamma>\<^sup>2")
    case True
    with \<gamma>'\<gamma>2 have YKK: "\<gamma>*k \<le> m" 
      using \<open>0<k\<close> \<open>m < l\<close> 
      apply (simp add: \<gamma>_def field_simps)
      by (smt (verit, best) distrib_left mult_left_mono of_nat_0_le_iff)
    have ln1\<xi>: "ln (1+\<xi>) * 20 \<ge> 1"
      unfolding \<xi>_def by (approximation 10)
    with YKK have \<section>: "m * ln (1+\<xi>) \<ge> \<delta> * k"
      unfolding \<delta>_def using zero_le_one mult_mono by fastforce
    have powerm: "(1+\<xi>)^m \<ge> exp (\<delta> * k)"
      using exp_mono [OF \<section>]
      by (smt (verit) \<eta>_def \<open>0 < \<eta>\<close> \<open>0 < \<gamma>'\<close> exp_ln_iff exp_of_nat_mult zero_le_mult_iff)
    have "n * (1+\<xi>)^m \<ge> (k+l choose l)"
      by (smt (verit, best) mult_left_mono nexp_gt of_nat_0_le_iff powerm)
    then have **: "n * U_lower_bound_ratio m \<ge> (k+l-m choose (l-m))"
      using \<open>m<l\<close> prod_gt0 kl_choose by (auto simp: U_lower_m field_simps)

    have m_le_choose: "m \<le> (k+l-m-1 choose (l-m))"
    proof (cases "m=0")
      case False
      have "m \<le> (k+l-m-1 choose 1)"
        using \<open>l\<le>k\<close> \<open>m<l\<close> by simp
      also have "\<dots> \<le> (k+l-m-1 choose (l-m))"
        using False \<open>l\<le>k\<close> \<open>m<l\<close> by (intro binomial_mono) auto
      finally have m_le_choose: "m \<le> (k+l-m-1 choose (l-m))" .
      then show ?thesis .
    qed auto
    have "RN k (l-m) \<le> k + (l-m) - 2 choose (k - 1)"
      by (rule RN_le_choose_strong)
    also have "\<dots> \<le> (k+l-m-1 choose k)"
      using \<open>l\<le>k\<close> \<open>m<l\<close> choose_reduce_nat by simp
    also have "\<dots> = (k+l-m-1 choose (l-m-1))"
      using \<open>m<l\<close> by (simp add: binomial_symmetric [of k])
    also have "\<dots> = (k+l-m choose (l-m)) - (k+l-m-1 choose (l-m))"
      using \<open>l\<le>k\<close> \<open>m<l\<close> choose_reduce_nat by simp
    also have "\<dots> \<le> (k+l-m choose (l-m)) - m"
      using m_le_choose by linarith
    finally have "RN k (l-m) \<le> (k+l-m choose (l-m)) - m" .
    then have "card U \<ge> RN k (l-m)"
      using 49 ** VUU by (force simp: is_good_clique_def U_def m_def)
    with Red_Blue_RN no_Red_K \<open>U \<subseteq> V\<close>
    obtain K where "K \<subseteq> U" "size_clique (l-m) K Blue" by meson
    then show False
      using no_Blue_K extend_Blue_clique by blast
  next
    case False 
    have YMK: "\<gamma>-\<gamma>' \<le> m/k"
      using \<open>m<l\<close> 
      apply (simp add: \<gamma>_def \<gamma>'_def divide_simps)
      apply (simp add: algebra_simps)
      by (smt (verit) mult_left_mono mult_right_mono nat_less_real_le of_nat_0_le_iff)

    define \<delta>' where "\<delta>' \<equiv> \<gamma>'/20"
    have no_RedU_K: "\<not> (\<exists>K. UBB.size_clique k K RedU)"
      unfolding UBB.size_clique_def RedU_def
      by (metis Int_subset_iff VUU all_edges_subset_iff_clique no_Red_K size_clique_def)
    have "(\<exists>K. UBB.size_clique k K RedU) \<or> (\<exists>K. UBB.size_clique (l-m) K BlueU)"
    proof (rule ccontr)
      assume neg: "\<not> ((\<exists>K. UBB.size_clique k K RedU) \<or> (\<exists>K. UBB.size_clique (l-m) K BlueU))"
      interpret UBB_NC: No_Cliques U "E \<inter> Pow U" p0_min RedU BlueU "l-m" k
      proof
        show "BlueU = E \<inter> Pow U \<setminus> RedU"
          using BlueU_eq EU_def by fastforce
      qed (use neg EU_def \<open>RedU \<subseteq> EU\<close> no_RedU_K \<open>l\<le>k\<close> in auto)
      show False
      proof (intro UBB_NC.Far_9_2)
        have "exp (\<delta>*k) * exp (-\<delta>'*k) = exp (\<gamma>*k/20 - \<gamma>'*k/20)"
          unfolding \<delta>_def \<delta>'_def by (simp add: mult_exp_exp) 
        also have "\<dots> \<le> exp (m/20)"
          using YMK \<open>0 < k\<close> by (simp add: left_diff_distrib divide_simps)
        also have "\<dots> \<le> (1+\<xi>)^m"
        proof -
          have "ln (16 / 15) * 20 \<ge> (1::real)"
            by (approximation 5)
          from mult_left_mono [OF this] 
          show ?thesis
            by (simp add: \<xi>_def powr_def mult_ac flip: powr_realpow)
        qed
        finally have expexp: "exp (\<delta>*k) * exp (-\<delta>'*k) \<le> (1+\<xi>) ^ m" .

        have "exp (-\<delta>'*k) * (k + (l-m) choose (l-m)) = exp (-\<delta>'*k) * PM * (k+l choose l)"
          using \<open>m < l\<close> kl_choose by force
        also have "\<dots> < (n/2) * exp (\<delta>*k) * exp (-\<delta>'*k) * PM"
          using n2exp_gt prod_gt0 by auto 
        also have "\<dots> \<le> (n/2) * (1+\<xi>) ^ m * PM"
          using expexp less_eq_real_def prod_gt0 by fastforce
        also have "\<dots> \<le> n * U_lower_bound_ratio m - m"  \<comment>\<open>where I was stuck: the "minus m"\<close>
          using PM_def U_MINUS_M U_lower_bound_ratio_def \<open>m < l\<close> by fastforce
        finally have "exp (-\<delta>'*k) * (k + (l-m) choose (l-m)) \<le> n * U_lower_bound_ratio m - m"
          by linarith 
        also have "\<dots> \<le> UBB.nV"
          using cardU by linarith
        finally have "exp (-\<delta>'*k) * (k + (l-m) choose (l-m)) \<le> UBB.nV" .
        then show "exp (- ((l-m) / (k + real (l-m)) / 20) * k) * (k + (l-m) choose (l-m)) \<le> UBB.nV"
          using \<open>m < l\<close> by (simp add: \<delta>'_def \<gamma>'_def) argo
      next
        show "1 - real (l-m) / (real k + real (l-m)) - \<eta> \<le> UBB.graph_density RedU"
          using gd_RedU_ge \<open>\<gamma>' \<le> \<gamma>\<close> \<open>m < l\<close> unfolding \<gamma>_def \<gamma>'_def
          by (smt (verit) less_or_eq_imp_le of_nat_add of_nat_diff)
        have "p0_min \<le> 1 - \<gamma> - \<eta>"
          using \<open>\<gamma>' \<le> \<gamma>\<close> \<gamma> p0_min_91 by (auto simp: \<eta>_def \<xi>_def)
        also have "\<dots> \<le> 1 - (l-m) / (real k + real (l-m)) - \<eta>"
          using \<open>\<gamma>' \<le> \<gamma>\<close> \<open>m<l\<close> by (simp add: \<gamma>_def \<gamma>'_def algebra_simps)
        finally show "p0_min \<le> 1 - (l-m) / (real k + real (l-m)) - \<eta>" .
      next
        have "m \<le> l * (k + real l) / (k + 2 * real l)"
          using False \<gamma>'\<gamma>2_iff by auto 
        also have "\<dots> \<le> l * (1 - (10/11)*\<gamma>)"
          using \<gamma> \<open>l>0\<close> by (simp add: \<gamma>_def field_split_simps)
        finally have "m \<le> real l * (1 - (10/11)*\<gamma>)" 
          by force
        then have "real l - real m \<ge> (10/11) * \<gamma> * l"
          by (simp add: algebra_simps)
        then have "Big_Far_9_2 \<gamma>' (l-m)"
          using False big \<open>\<gamma>' \<le> \<gamma>\<close> \<gamma> \<open>m<l\<close>
          by (simp add: Big_Far_9_1_def)
        then show "Big_Far_9_2 ((l-m) / (real k + real (l-m))) (l-m)"
          by (simp add: \<gamma>'_def \<open>m < l\<close> add_diff_eq less_or_eq_imp_le)
        show "(l-m) / (real k + real (l-m)) \<le> 1/10"
          using \<gamma> \<gamma>_def \<open>m < l\<close> by fastforce
        show "0 \<le> \<eta>"
          using \<open>0 < \<eta>\<close> by linarith
        show "\<eta> \<le> (l-m) / (real k + real (l-m)) / 15"
          using mult_right_mono [OF \<open>\<gamma>' \<le> \<gamma>\<close>, of \<xi>]
          by (simp add: \<eta>_def \<gamma>'_def \<open>m < l\<close> \<xi>_def add_diff_eq less_or_eq_imp_le mult.commute)
      qed
    qed
    with no_RedU_K obtain K where "K \<subseteq> U" "UBB.size_clique (l-m) K BlueU"
      by (meson UBB.size_clique_def)
    then show False
      using no_Blue_K extend_Blue_clique VUU
      unfolding UBB.size_clique_def size_clique_def BlueU_def
      by (metis Int_subset_iff all_edges_subset_iff_clique) 
  qed
qed

end (*context P0_min*)

end
