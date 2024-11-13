section \<open>The Proof of Theorem 1.1\<close>

theory The_Proof
  imports From_Diagonal

begin

subsection \<open>The bounding functions\<close>

definition "H \<equiv> \<lambda>p. -p * log 2 p - (1-p) * log 2 (1-p)"

definition dH where "dH \<equiv> \<lambda>x::real. -ln(x)/ln(2) + ln(1 - x)/ln(2)"

lemma dH [derivative_intros]: 
  assumes "0<x" "x<1"
  shows "(H has_real_derivative dH x) (at x)"
  unfolding H_def dH_def log_def
  by (rule derivative_eq_intros | use assms in force)+

lemma H0 [simp]: "H 0 = 0" and H1 [simp]: "H 1 = 0"
  by (auto simp: H_def)

lemma H_reflect: "H (1-p) = H p"
  by (simp add: H_def)

lemma H_ge0:
  assumes "0 \<le> p" "p \<le> 1"
  shows "0 \<le> H p"
  unfolding H_def
  by (smt (verit, best) assms mult_minus_left mult_le_0_iff zero_less_log_cancel_iff)

text \<open>Going up, from 0 to 1/2\<close>
lemma H_half_mono:
  assumes "0\<le>p'" "p'\<le>p" "p \<le> 1/2"
  shows "H p' \<le> H p"
proof (cases "p'=0")
  case True
  then have "H p' = 0"
    by (auto simp: H_def)
  then show ?thesis
    by (smt (verit) H_ge0 True assms(2) assms(3) divide_le_eq_1_pos)
next
  case False
  with assms have "p'>0" by simp
  have "dH(1/2) = 0"
    by (simp add: dH_def)
  moreover
  have "dH x \<ge> 0" if "0<x" "x\<le>1/2" for x
    using that by (simp add: dH_def divide_right_mono)
  ultimately show ?thesis
    by (smt (verit) dH DERIV_nonneg_imp_nondecreasing \<open>p'>0\<close> assms le_divide_eq_1_pos)
qed

text \<open>Going down, from 1/2 to 1\<close>
lemma H_half_mono':
  assumes "1/2 \<le> p'" "p'\<le>p" "p \<le> 1"
  shows "H p' \<ge> H p"
  using H_half_mono [of "1-p" "1-p'"] H_reflect assms by auto

lemma H_half: "H(1/2) = 1"
  by (simp add: H_def log_divide)

lemma H_le1:
  assumes "0 \<le> p" "p \<le> 1"
  shows "H p \<le> 1"
  by (smt (verit, best) H0 H1 H_ge0 H_half_mono H_half_mono' H_half assms)

text \<open>Many thanks to Fedor Petrov on mathoverflow\<close>
lemma H_12_1:
  fixes a b::nat
  assumes "a \<ge> b"
  shows "log 2 (a choose b) \<le> a * H(b/a)"
proof (cases "a=b \<or> b=0")
  case True
  with assms show ?thesis
    by (auto simp: H_def)
next
  let ?p = "b/a"
  case False
  then have p01: "0 < ?p" "?p < 1"
    using assms by auto
  then have "(a choose b) * ?p ^ b * (1-?p) ^ (a-b) \<le> (?p + (1-?p)) ^ a"
    by (subst binomial_ring) (force intro!: member_le_sum assms)
  also have "\<dots> = 1"
    by simp
  finally have \<section>: "(a choose b) * ?p ^ b * (1-?p) ^ (a-b) \<le> 1" .
  have "log 2 (a choose b) + b * log 2 ?p + (a-b) * log 2 (1-?p) \<le> 0"
    using Transcendental.log_mono [OF _ _ \<section>] False assms 
    by (force simp add: p01 log_mult log_nat_power)
  then show ?thesis
    using p01 False assms unfolding H_def by (simp add: divide_simps)
qed 

definition "gg \<equiv> GG (2/5)"

lemma gg_eq: "gg x y = log 2 (5/2) + x * log 2 (5/3) + y * log 2 ((2 * (x+y)) / (5*y))"
  by (simp add: gg_def GG_def)

definition "f1 \<equiv> \<lambda>x y. x + y + (2-x) * H(1/(2-x))"

definition "f2 \<equiv> \<lambda>x y. f1 x y - (1 / (40 * ln 2)) * ((1-x) / (2-x))"

definition "ff \<equiv> \<lambda>x y. if x < 3/4 then f1 x y else f2 x y"

text \<open>Incorporating Bhavik‘s idea, which gives us a lower bound for @{term \<gamma>} of 1/101\<close>
definition ffGG :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "ffGG \<equiv> \<lambda>\<mu> x y. max 1.9 (min (ff x y) (GG \<mu> x y))"

text \<open>The proofs involving @{term Sup} are needlessly difficult because ultimately 
the sets involved are finite, eliminating the need to demonstrate boundedness.
Simpler might be to use the extended reals.\<close>

lemma f1_le:
  assumes "x\<le>1" 
  shows "f1 x y \<le> y+2"
  unfolding f1_def
  using H_le1 [of "1/(2-x)"] assms
  by (smt (verit) divide_le_eq_1_pos divide_nonneg_nonneg mult_left_le)

lemma ff_le4:
  assumes "x\<le>1" "y\<le>1"
  shows "ff x y \<le> 4"
proof -
  have "ff x y \<le> f1 x y"
    using assms by (simp add: ff_def f2_def)
  also have "\<dots> \<le> 4"
    using assms by (smt (verit) f1_le)
  finally show ?thesis .
qed

lemma ff_GG_bound:
  assumes "x\<le>1" "y\<le>1"
  shows "ffGG \<mu> x y \<le> 4"
  using ff_le4 [OF assms] by (auto simp: ffGG_def)

lemma bdd_above_ff_GG:
  assumes "x\<le>1" "u\<le>1"
  shows "bdd_above ((\<lambda>y. ffGG \<mu> x y + \<eta>) ` {0..u})"
  using ff_GG_bound assms
  by (intro bdd_above.I2 [where M = "4+\<eta>"]) force

lemma bdd_above_SUP_ff_GG:
  assumes "0\<le>u" "u\<le>1"
  shows "bdd_above ((\<lambda>x. \<Squnion>y\<in>{0..u}. ffGG \<mu> x y + \<eta>) ` {0..1})"
  using bdd_above_ff_GG assms
  by (intro bdd_aboveI [where M = "4 + \<eta>"]) (auto simp: cSup_le_iff ff_GG_bound Pi_iff)

text \<open>Claim (62). A singularity if $x=1$. Okay if we put $\ln(0) = 0$\<close>
lemma FF_le_f1:
  fixes k::nat and x y::real
  assumes x: "0 \<le> x" "x \<le> 1" and y: "0 \<le> y" "y \<le> 1"
  shows "FF k x y \<le> f1 x y"
proof (cases "nat\<lfloor>k - x*k\<rfloor> = 0")
  case True
  with x show ?thesis
    by (simp add: FF_def f1_def H_ge0 log_def)
next
  case False
  let ?kl = "k + k - nat \<lceil>x*k\<rceil>"
  have kk_less_1: "k / ?kl < 1"
    using x False by (simp add: field_split_simps, linarith)
  have le: "nat\<lfloor>k - x*k\<rfloor> \<le> k - nat\<lceil>x*k\<rceil>"
    using floor_ceiling_diff_le x
    by (meson mult_left_le_one_le mult_nonneg_nonneg of_nat_0_le_iff)
  have "k>0"
    using False zero_less_iff_neq_zero by fastforce
  have RN_gt0: "RN k (nat\<lfloor>k - x*k\<rfloor>) > 0"
    by (metis False RN_eq_0_iff \<open>k>0\<close> gr0I)
  then have \<section>: "RN k (nat\<lfloor>k - x*k\<rfloor>) \<le> k + nat\<lfloor>k - x*k\<rfloor> choose k"
    using RN_le_choose by force
  also have "\<dots> \<le> k + k - nat\<lceil>x*k\<rceil> choose k"
    using False Nat.le_diff_conv2 binomial_right_mono le by fastforce
  finally have "RN k (nat \<lfloor>real k - x*k\<rfloor>) \<le> ?kl choose k" .
  with RN_gt0 have "FF k x y \<le> log 2 (?kl choose k) / k + x + y"
    by (simp add: FF_def divide_right_mono nat_less_real_le)
  also have "\<dots> \<le> (?kl * H(k/?kl)) / k + x + y"
  proof -
    have "k \<le> k + k - nat\<lceil>x*k\<rceil>"
      using False by linarith
    then show ?thesis
      by (simp add: H_12_1 divide_right_mono)
  qed
  also have "\<dots> \<le> f1 x y"
  proof -
    have 1: "?kl / k \<le> 2-x"
        using x by (simp add: field_split_simps)
    have 2: "H (k / ?kl) \<le> H (1 / (2-x))"
    proof (intro H_half_mono')
      show "1 / (2-x) \<le> k / ?kl"
        using x False by (simp add: field_split_simps, linarith)
    qed (use x kk_less_1 in auto)
    have "?kl / k * H (k / ?kl) \<le> (2-x) * H (1 / (2-x))"
      using x mult_mono [OF 1 2 _ H_ge0] kk_less_1 by fastforce
    then show ?thesis
      by (simp add: f1_def)
  qed
  finally show ?thesis .
qed

text \<open>Bhavik's @{text "eleven_one_large_end"}\<close>
lemma f1_le_19:
  fixes k::nat and x y::real
  assumes x: "0.99 \<le> x" "x \<le> 1" and y: "0 \<le> y" "y \<le> 3/4"
  shows "f1 x y \<le> 1.9"
proof -
  have A: "2-x \<le> 1.01"
    using x by simp
  have "H (1 / (2-x)) \<le> H (1 / (2-0.99))"
    using x by (intro H_half_mono') (auto simp: divide_simps)
  also have "\<dots> \<le> 0.081"
    unfolding H_def by (approximation 15)
  finally have B: "H (1 / (2-x)) \<le> 0.081" .
  have "(2-x) * H (1 / (2-x)) \<le> 1.01 * 0.081"
    using mult_mono [OF A B] x
    by (smt (verit) A H_ge0 divide_le_eq_1_pos divide_nonneg_nonneg)
  with assms show ?thesis by (auto simp: f1_def)
qed

text \<open>Claim (63) in weakened form; we get rid of the extra bit later\<close>
lemma (in P0_min) FF_le_f2:
  fixes k::nat and x y::real
  assumes x: "3/4 \<le> x" "x \<le> 1" and y: "0 \<le> y" "y \<le> 1"
  and l: "real l = k - x*k"
  assumes p0_min_101: "p0_min \<le> 1 - 1/5"
  defines "\<gamma> \<equiv> real l / (real k + real l)"
  defines "\<gamma>0 \<equiv> min \<gamma> (0.07)" 
  assumes "\<gamma> > 0"
  shows "FF k x y \<le> f2 x y + ok_fun_10_1 \<gamma> k / (k * ln 2)"
proof -
  have "l>0"
    using \<open>\<gamma>>0\<close> \<gamma>_def less_irrefl by fastforce
  have "x>0"
    using x by linarith
  with l have "k\<ge>l"
    by (smt (verit, del_insts) of_nat_0_le_iff of_nat_le_iff pos_prod_lt)
  with \<open>0 < l\<close> have "k>0" by force
  have RN_gt0: "RN k l > 0"
    by (metis RN_eq_0_iff \<open>0 < k\<close> \<open>0 < l\<close> gr0I)
  define \<delta> where "\<delta> \<equiv> \<gamma>/40"
  have A: "l / real(k+l) = (1-x)/(2-x)"
    using x \<open>k>0\<close> by (simp add: l field_simps)
  have B: "real(k+l) / k = 2-x"
    using \<open>0 < k\<close> l by (auto simp: divide_simps left_diff_distrib)
  have \<gamma>: "\<gamma> \<le> 1/5" 
    using x A by (simp add: \<gamma>_def)
  have "1 - 1 / (2-x) = (1-x) / (2-x)"
    using x by (simp add: divide_simps)
  then have Heq: "H (1 / (2-x)) = H ((1-x) / (2-x))"
    by (metis H_reflect)
  have "RN k l \<le> exp (-\<delta>*k + ok_fun_10_1 \<gamma> k) * (k+l choose l)"
    unfolding \<delta>_def \<gamma>_def
  proof (rule Closer_10_1_unconditional)
    show "0 < l / (real k + real l)" "l / (real k + real l) \<le> 1/5"
      using \<gamma> \<open>\<gamma> > 0\<close> by (auto simp: \<gamma>_def)
    have "min (l / (k + real l)) 0.07 > 0"
      using \<open>l>0\<close> by force 
  qed (use p0_min_101 in auto)
  with RN_gt0 have "FF k x y \<le> log 2 (exp (-\<delta>*k + ok_fun_10_1 \<gamma> k) * (k+l choose l)) / k + x + y"
    unfolding FF_def
    by (intro add_mono divide_right_mono Transcendental.log_mono; simp flip: l)
  also have "\<dots> = (log 2 (exp (-\<delta>*k + ok_fun_10_1 \<gamma> k)) + log 2 (k+l choose l)) / k + x + y"
    by (simp add: log_mult)
  also have "\<dots> \<le> ((-\<delta>*k + ok_fun_10_1 \<gamma> k) / ln 2 + (k+l) * H(l/(k+l))) / k + x + y"
    using H_12_1
    by (smt (verit, ccfv_SIG) log_exp divide_right_mono le_add2 of_nat_0_le_iff)
  also have "\<dots> = (-\<delta>*k + ok_fun_10_1 \<gamma> k) / k / ln 2 + (k+l) / k * H(l/(k+l)) + x + y"
    by argo
  also have "\<dots> = -\<delta> / ln 2 + ok_fun_10_1 \<gamma> k / (k * ln 2) + (2-x) * H((1-x)/(2-x)) + x + y"
  proof -
    have "(-\<delta>*k + ok_fun_10_1 \<gamma> k) / k / ln 2 = -\<delta> / ln 2 + ok_fun_10_1 \<gamma> k / (k * ln 2)"
      using \<open>0 < k\<close> by (simp add: divide_simps)
    with A B show ?thesis
      by presburger
  qed
  also have "\<dots> = - (log 2 (exp 1) / 40) * (1-x) / (2-x) + ok_fun_10_1 \<gamma> k / (k * ln 2) + (2-x) * H((1-x)/(2-x)) + x + y"
    using A by (force simp: \<delta>_def \<gamma>_def field_simps)
  also have "\<dots> \<le> f2 x y + ok_fun_10_1 \<gamma> k / (real k * ln 2)"
    by (simp add: Heq f1_def f2_def mult_ac)
  finally show ?thesis .
qed


text \<open>The body of the proof has been extracted to allow the symmetry argument.
  And 1/12 is 3/4-2/3, the latter number corresponding to @{term "\<mu>=2/5"}\<close>
lemma (in Book_Basis) From_11_1_Body:
  fixes V :: "'a set"
  assumes \<mu>: "0 < \<mu>" "\<mu> \<le> 2/5" and \<eta>: "0 < \<eta>" "\<eta> \<le> 1/12"
    and ge_RN: "Suc nV \<ge> RN k k"
    and Red: "graph_density Red \<ge> 1/2" 
    and p0_min12: "p0_min \<le> 1/2"
    and Red_E: "Red \<subseteq> E" and Blue_def: "Blue = E\<setminus>Red" 
    and no_Red_K: "\<not> (\<exists>K. size_clique k K Red)"
    and no_Blue_K: "\<not> (\<exists>K. size_clique k K Blue)"
    and big: "Big_From_11_1 \<eta> \<mu> k"
  shows "log 2 (RN k k) / k \<le> (SUP x \<in> {0..1}. SUP y \<in> {0..3/4}. ffGG \<mu> x y + \<eta>)"
proof -  
  have 12: "3/4 - 2/3 = (1/12::real)"
    by simp
  define \<eta>' where "\<eta>' \<equiv> \<eta>/2"
  have \<eta>': "0 < \<eta>'" "\<eta>' \<le> 1/12"
    using \<eta> by (auto simp: \<eta>'_def)
  have "k>0" and big101: "Big_Closer_10_1 (1/101) (nat\<lceil>k/100\<rceil>)" and ok_fun_10_1_le: "3 / (k * ln 2) \<le> \<eta>'"
    using big by (auto simp: Big_From_11_1_def \<eta>'_def)
  interpret No_Cliques where l=k
    using assms unfolding No_Cliques_def No_Cliques_axioms_def
    using Book_Basis_axioms P0_min_axioms by blast
  obtain X0 Y0 where card_X0: "card X0 \<ge> nV/2" and card_Y0: "card Y0 = gorder div 2"
    and "X0 = V \<setminus> Y0" "Y0\<subseteq>V"
    and p0_half: "1/2 \<le> gen_density Red X0 Y0"
    and "Book V E p0_min Red Blue k k \<mu> X0 Y0" 
  proof (rule Basis_imp_Book)
    show "p0_min \<le> graph_density Red"
      using p0_min12 Red by linarith
    show "0 < \<mu>" "\<mu> < 1"
      using \<mu> by auto
  qed (use infinite_UNIV p0_min Blue_def Red \<mu> in auto)
  then interpret Book V E p0_min Red Blue k k \<mu> X0 Y0
    by meson
  define \<R> where "\<R> \<equiv> Step_class {red_step}"
  define \<S> where "\<S> \<equiv> Step_class {dboost_step}"
  define t where "t \<equiv> card \<R>" 
  define s where "s \<equiv> card \<S>"
  define x where "x \<equiv> t/k"
  define y where "y \<equiv> s/k"
  have sts: "(s + real t) / s = (x+y) / y"
    using \<open>k>0\<close> by (simp add: x_def y_def divide_simps)
  have "t<k"
    by (simp add: \<R>_def \<mu> t_def red_step_limit)
  then obtain x01: "0\<le>x" "x<1"
    by (auto simp: x_def)

  have big41: "Big_Blue_4_1 \<mu> k" and big61: "Big_Y_6_1 \<mu> k" 
    and big85: "Big_ZZ_8_5 \<mu> k" and big11_2: "Big_From_11_2 \<mu> k"
    and ok111_le: "ok_fun_11_1 \<mu> k / k \<le> \<eta>'"
    and powr_le: "(2 / (1-\<mu>)) * k powr (-1/20) \<le> \<eta>'" and "k>0"
    using big by (auto simp: Big_From_11_1_def Big_Y_6_1_def Big_Y_6_2_def \<eta>'_def)
  then have big53: "Big_Red_5_3 \<mu> k"
    by (meson Big_From_11_2_def)
  have "\<mu> < 1"
    using \<mu> by auto
  
  have "s<k"
    unfolding s_def \<S>_def
    by (meson \<mu> le_less_trans bblue_dboost_step_limit big41 le_add2)
  then obtain y01: "0\<le>y" "y<1"
    by (auto simp: y_def)

  text \<open>Now that @{term x} and @{term y} are fixed, here's the body of the outer supremum\<close>
  define w where "w \<equiv> (\<Squnion>y\<in>{0..3/4}. ffGG \<mu> x y + \<eta>)"
  show ?thesis
  proof (intro cSup_upper2 imageI)
    show "w \<in> (\<lambda>x. \<Squnion>y\<in>{0..3/4}. ffGG \<mu> x y + \<eta>) ` {0..1}"
      using x01 by (force simp: w_def intro!: image_eqI [where x=x])
  next
    have \<mu>23: "\<mu> / (1-\<mu>) \<le> 2/3"
      using \<mu> by (simp add: divide_simps)
    have beta_le: "bigbeta \<le> \<mu>"
      using \<open>\<mu><1\<close> \<mu> big53 bigbeta_le by blast
    have "s \<le> (bigbeta / (1 - bigbeta)) * t + (2 / (1-\<mu>)) * k powr (19/20)"
      using ZZ_8_5 [OF big85] \<mu> by (auto simp: \<R>_def \<S>_def s_def t_def)
    also have "\<dots> \<le> (\<mu> / (1-\<mu>)) * t + (2 / (1-\<mu>)) * k powr (19/20)"
      by (smt (verit, ccfv_SIG) \<open>\<mu><1\<close> \<mu> beta_le frac_le mult_right_mono of_nat_0_le_iff)
    also have "\<dots> \<le> (\<mu> / (1-\<mu>)) * t + (2 / (1-\<mu>)) * (k powr (-1/20) * k powr 1)"
      unfolding powr_add [symmetric] by simp
    also have "\<dots> \<le> (2/3) * t + (2 / (1-\<mu>)) * (k powr (-1/20)) * k"
      using mult_right_mono [OF \<mu>23, of t] by (simp add: mult_ac)
    also have "\<dots> \<le> (3/4 - \<eta>') * k + (2 / (1-\<mu>)) * (k powr (-1/20)) * k"
    proof -
      have "(2/3) * t \<le> (2/3) * k"
        using \<open>t < k\<close> by simp
      then show ?thesis
        using 12 \<eta>' by (smt (verit) mult_right_mono of_nat_0_le_iff)
    qed
    finally have "s \<le> (3/4 - \<eta>') * k + (2 / (1-\<mu>)) * k powr (-1/20) * k" 
      by simp
    with mult_right_mono [OF powr_le, of k] 
    have \<dagger>: "s \<le> 3/4 * k"
      by (simp add: mult.commute right_diff_distrib')
    then have "y \<le> 3/4"
        by (metis \<dagger> \<open>0 < k\<close> of_nat_0_less_iff pos_divide_le_eq y_def)

    have k_minus_t: "nat \<lfloor>real k - real t\<rfloor> = k-t"
      by linarith
    have "nV div 2 \<le> card Y0"
      by (simp add: card_Y0)
    then have \<section>: "log 2 (Suc nV) \<le> log 2 (RN k (k-t)) + s + t + 2 - ok_fun_61 k"
      using From_11_3 [OF _ big61] p0_half \<mu> by (auto simp: \<R>_def \<S>_def p0_def s_def t_def)

    define l where "l \<equiv> k-t"
    define \<gamma> where "\<gamma> \<equiv> real l / (real k + real l)"
    have "\<gamma> < 1"
      using \<open>t < k\<close> by (simp add: \<gamma>_def)
    have "nV div 2 \<le> card X0"
      using card_X0 by linarith
    then have 112: "log 2 (Suc nV) \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + s * log 2 (ratio \<mu> s t)
                + ok_fun_11_2 \<mu> k"
      using From_11_2 [OF _ big11_2] p0_half \<mu>
      unfolding s_def t_def p0_def \<R>_def \<S>_def by force
    have "log 2 (Suc nV) / k \<le> log 2 (1/\<mu>) + x * log 2 (1 / (1-\<mu>)) + y * log 2 (ratio \<mu> s t)
                          + ok_fun_11_2 \<mu> k / k"
      using \<open>k>0\<close> divide_right_mono [OF 112, of k]
      by (simp add: add_divide_distrib x_def y_def)
    also have "\<dots> = GG \<mu> x y + ok_fun_11_2 \<mu> k / k"
      by (metis GG_def sts times_divide_eq_right)
    also have "\<dots> \<le> GG \<mu> x y + ok_fun_11_1 \<mu> k / k"
      by (simp add: ok_fun_11_1_def divide_right_mono)
    finally have le_GG: "log 2 (Suc nV) / k \<le> GG \<mu> x y + ok_fun_11_1 \<mu> k / k" .

    have "log 2 (Suc nV) / k \<le> log 2 (RN k (k-t)) / k + x + y + (2 - ok_fun_61 k) / k"
      using \<open>k>0\<close> divide_right_mono [OF \<section>, of k] add_divide_distrib x_def y_def
      by (smt (verit) add_uminus_conv_diff of_nat_0_le_iff)
    also have "\<dots> = FF k x y + (2 - ok_fun_61 k) / k"
      by (simp add: FF_def x_def k_minus_t)
    finally have DD: "log 2 (Suc nV) / k \<le> FF k x y + (2 - ok_fun_61 k) / k" .

    have "RN k k > 0"
      by (metis RN_eq_0_iff \<open>k>0\<close> gr0I)
    moreover have "log 2 (Suc nV) / k \<le> ffGG \<mu> x y + \<eta>"
    proof (cases "x < 0.99")  \<comment> \<open>a further case split that gives a lower bound for gamma\<close>
      case True
      have \<ddagger>: "Big_Closer_10_1 (min \<gamma> 0.07) (nat \<lceil>\<gamma> * real k / (1 - \<gamma>)\<rceil>)"
      proof (intro Big_Closer_10_1_upward [OF big101])
        show "1/101 \<le> min \<gamma> 0.07"
          using \<open>k>0\<close> \<open>t<k\<close> True by (simp add: \<gamma>_def l_def x_def divide_simps)
        with \<open>\<gamma> < 1\<close> less_eq_real_def have "k/100 \<le> \<gamma> * k / (1 - \<gamma>)"
          by (fastforce simp: field_simps)
        then show "nat \<lceil>k/100\<rceil> \<le> nat \<lceil>\<gamma> * k / (1 - \<gamma>)\<rceil>"
          using ceiling_mono nat_mono by blast
      qed
      have 122: "FF k x y \<le> ff x y + \<eta>'"
      proof -
        have "FF k x y \<le> f1 x y"
          using x01 y01
          by (intro FF_le_f1) auto
        moreover
        have "FF k x y \<le> f2 x y + ok_fun_10_1 \<gamma> k / (k * ln 2)" if "x \<ge> 3/4"
          unfolding \<gamma>_def
        proof (intro FF_le_f2 that)
          have "\<gamma> = (1-x) / (2-x)"
            using \<open>0 < k\<close> \<open>t < k\<close> by (simp add: l_def \<gamma>_def x_def divide_simps)
          then have "\<gamma> \<le> 1/5"
            using that \<open>x<1\<close> by simp
          show "real l = real k - x * real k"
            using \<open>t < k\<close> by (simp add: l_def x_def)
          show "0 < l / (k + real l)"
            using \<open>t < k\<close> l_def by auto
        qed (use x01 y01 p0_min12 in auto)
        moreover have "ok_fun_10_1 \<gamma> k / (k * ln 2) \<le> \<eta>'"
          using \<ddagger> ok_fun_10_1_le by (simp add: ok_fun_10_1_def)
        ultimately show ?thesis
          using \<eta>' by (auto simp: ff_def)
      qed
      have "log 2 (Suc nV) / k \<le> ff x y + \<eta>' + (2 - ok_fun_61 k) / k"
        using "122" DD by linarith
      also have "\<dots> \<le> ff x y + \<eta>' + ok_fun_11_1 \<mu> k / k"
        by (simp add: ok_fun_11_1_def divide_right_mono)
      finally have le_ff: "log 2 (Suc nV) / k \<le> ff x y + \<eta>' + ok_fun_11_1 \<mu> k / k" .
      then show ?thesis
        using \<eta> ok111_le le_ff le_GG unfolding \<eta>'_def ffGG_def by linarith
    next
      case False  \<comment> \<open>in this case, we can use the existing bound involving @{term f1}\<close>
      have "log 2 (Suc nV) / k \<le> FF k x y + (2 - ok_fun_61 k) / k"
        by (metis DD)
      also have "\<dots> \<le> f1 x y + (2 - ok_fun_61 k) / k"
        using x01 y01 FF_le_f1 [of x y] by simp
      also have "\<dots> \<le> 1.9 + (2 - ok_fun_61 k) / k"
        using x01 y01 by (smt (verit) False \<open>y \<le> 3/4\<close> f1_le_19)
      also have "\<dots> \<le> ffGG \<mu> x y + \<eta>"
        by (smt (verit) P0_min.intro P0_min.ok_fun_11_1_def \<eta>'(1) \<eta>'_def divide_right_mono ffGG_def field_sum_of_halves of_nat_0_le_iff ok111_le p0_min(1) p0_min(2))
      finally show ?thesis .
    qed
    ultimately have "log 2 (RN k k) / k \<le> ffGG \<mu> x y + \<eta>"
      using ge_RN \<open>k>0\<close>
      by (smt (verit, best) Transcendental.log_mono divide_right_mono of_nat_0_less_iff of_nat_mono)
    also have "\<dots> \<le> w"
      unfolding w_def 
    proof (intro cSup_upper2)
      have "y \<in> {0..3/4}"
        using divide_right_mono [OF \<dagger>, of k] \<open>k>0\<close> by (simp add: x_def y_def) 
      then show "ffGG \<mu> x y + \<eta> \<in> (\<lambda>y. ffGG \<mu> x y + \<eta>) ` {0..3/4}"
        by blast
    next
      show "bdd_above ((\<lambda>y. ffGG \<mu> x y + \<eta>) ` {0..3/4})"
        by (simp add: bdd_above_ff_GG less_imp_le x01)
    qed auto
    finally show "log 2 (real (RN k k)) / k \<le> w" .
  next
    show "bdd_above ((\<lambda>x. \<Squnion>y\<in>{0..3/4}. ffGG \<mu> x y + \<eta>) ` {0..1})"
      by (auto intro: bdd_above_SUP_ff_GG)
  qed
qed 

theorem (in P0_min) From_11_1:
  assumes \<mu>: "0 < \<mu>" "\<mu> \<le> 2/5" and "0 < \<eta>" "\<eta> \<le> 1/12"
    and p0_min12: "p0_min \<le> 1/2" and big: "Big_From_11_1 \<eta> \<mu> k"
  shows "log 2 (RN k k) / k \<le> (SUP x \<in> {0..1}. SUP y \<in> {0..3/4}. ffGG \<mu> x y + \<eta>)"
proof -
  have "k\<ge>3"
    using big by (auto simp: Big_From_11_1_def)
  define n where "n \<equiv> RN k k - 1"
  define V where "V \<equiv> {..<n}"
  define E where "E \<equiv> all_edges V" 
  interpret Book_Basis V E
  proof qed (auto simp: V_def E_def comp_sgraph.wellformed comp_sgraph.two_edges)

  have "RN k k \<ge> 3"
    using \<open>k\<ge>3\<close> RN_3plus le_trans by blast 
  then have "n < RN k k"
    by (simp add: n_def)
  moreover have [simp]: "nV = n"
    by (simp add: V_def)
  ultimately obtain Red Blue
    where Red_E: "Red \<subseteq> E" and Blue_def: "Blue = E\<setminus>Red" 
      and no_Red_K: "\<not> (\<exists>K. size_clique k K Red)"
      and no_Blue_K: "\<not> (\<exists>K. size_clique k K Blue)"
    by (metis \<open>n < RN k k\<close> less_RN_Red_Blue)
  have Blue_E: "Blue \<subseteq> E" and disjnt_Red_Blue: "disjnt Red Blue" and Blue_eq: "Blue = all_edges V \<setminus> Red"
    using complete by (auto simp: Blue_def disjnt_iff E_def) 
  have "nV > 1"
    using \<open>RN k k \<ge> 3\<close> \<open>nV=n\<close> n_def by linarith
  with graph_size have "graph_size > 0"
    by simp
  then have "graph_density E = 1"
    by (simp add: graph_density_def)
  then have "graph_density Red + graph_density Blue = 1"
    using graph_density_Un [OF disjnt_Red_Blue] by (simp add: Blue_def Red_E Un_absorb1)
  then consider (Red) "graph_density Red \<ge> 1/2" | (Blue) "graph_density Blue \<ge> 1/2"
    by force
  then show ?thesis
  proof cases
    case Red
    show ?thesis
    proof (intro From_11_1_Body)
    next
      show "RN k k \<le> Suc nV"
        by (simp add: n_def)
      show "\<nexists>K. size_clique k K Red"
        using no_Red_K by blast
      show "\<nexists>K. size_clique k K Blue"
        using no_Blue_K by blast
    qed (use Red Red_E Blue_def assms in auto)
  next
    case Blue
    show ?thesis
    proof (intro From_11_1_Body)
      show "RN k k \<le> Suc nV"
        by (simp add: n_def)
      show "Blue \<subseteq> E"
        by (simp add: Blue_E)
      show "Red = E \<setminus> Blue"
        by (simp add: Blue_def Red_E double_diff)
      show "\<nexists>K. size_clique k K Red"
        using no_Red_K by blast
      show "\<nexists>K. size_clique k K Blue"
        using no_Blue_K by blast
    qed (use Blue Red_E Blue_def assms in auto)
  qed
qed

subsection \<open>The monster calculation from appendix A\<close>

subsubsection \<open>Observation A.1\<close>

lemma gg_increasing:
  assumes "x \<le> x'" "0 \<le> x" "0 \<le> y" 
  shows "gg x y \<le> gg x' y"
proof (cases "y=0")
  case False
  with assms show ?thesis
    unfolding gg_eq by (intro add_mono mult_left_mono divide_right_mono Transcendental.log_mono) auto    
qed (auto simp: gg_eq assms)


text \<open>Thanks to Manuel Eberl\<close>
lemma continuous_on_x_ln: "continuous_on {0..} (\<lambda>x::real. x * ln x)"
proof -
  have "continuous (at x within {0..}) (\<lambda>x. x * ln x)"
    if "x \<ge> 0" for x :: real
  proof (cases "x = 0")
    case True
    have "continuous (at_right 0) (\<lambda>x::real. x * ln x)"
      unfolding continuous_within by real_asymp
    thus ?thesis
      using True by (simp add: at_within_Ici_at_right)
  qed (auto intro!: continuous_intros)
  thus ?thesis
    by (simp add: continuous_on_eq_continuous_within)
qed

lemma continuous_on_f1: "continuous_on {..1} (\<lambda>x. f1 x y)"
proof -
  have \<section>: "(\<lambda>x::real. (1 - 1/(2-x)) * ln (1 - 1/(2-x))) = (\<lambda>x. x * ln x) o (\<lambda>x. 1 - 1/(2-x))"
    by (simp add: o_def)
  have cont_xln: "continuous_on {..1} (\<lambda>x::real. (1 - 1/(2-x)) * ln (1 - 1/(2-x)))"
    unfolding \<section>
  proof (rule continuous_intros)
    show "continuous_on {..1::real} (\<lambda>x. 1 - 1/(2-x))"
      by (intro continuous_intros) auto
  next
    show "continuous_on ((\<lambda>x::real. 1 - 1/(2-x)) ` {..1}) (\<lambda>x. x * ln x)"
      by (rule continuous_on_subset [OF continuous_on_x_ln]) auto
  qed
  show ?thesis
    apply (simp add: f1_def H_def log_def)
    by (intro continuous_on_subset [OF cont_xln] continuous_intros) auto
qed

definition df1 where "df1 \<equiv> \<lambda>x. log 2 (2 * ((1-x) / (2-x)))"

lemma Df1 [derivative_intros]: 
  assumes "x<1"
  shows "((\<lambda>x. f1 x y) has_real_derivative df1 x) (at x)"
proof -
  have "(2 - x * 2) = 2 * (1-x)"
    by simp
  then have [simp]: "log 2 (2 - x * 2) = log 2 (1-x) + 1"
    using log_mult [of 2 "1-x" 2] assms by (smt (verit, best) log_eq_one)
  show ?thesis
    using assms 
    unfolding f1_def H_def df1_def
    apply -
    apply (rule derivative_eq_intros | simp)+
    apply (simp add: log_divide divide_simps)
    apply (simp add: algebra_simps)
    done
qed

definition delta where "delta \<equiv> \<lambda>u::real. 1 / (ln 2 * 40 * (2 - u)\<^sup>2)"

lemma Df2: 
  assumes "1/2\<le>x" "x<1" 
  shows "((\<lambda>x. f2 x y) has_real_derivative df1 x + delta x) (at x)" 
  using assms unfolding f2_def delta_def
  apply -
  apply (rule derivative_eq_intros Df1 | simp)+
  apply (simp add: divide_simps power2_eq_square)
  done

lemma antimono_on_ff:
  assumes "0 \<le> y" "y < 1"
  shows "antimono_on {1/2..1} (\<lambda>x. ff x y)"
proof -
  have \<section>: "1 - 1 / (2-x) = (1-x) / (2-x)" if "x<2" for x::real
    using that by (simp add: divide_simps)
  have f1: "f1 x' y \<le> f1 x y"
    if "x \<in> {1/2..1}" "x' \<in> {1/2..1}" "x \<le> x'" "x' \<le> 1" for x x'::real
  proof (rule DERIV_nonpos_imp_decreasing_open [OF \<open>x \<le> x'\<close>, where f = "\<lambda>x. f1 x y"])
    fix u :: real
    assume "x < u" "u < x'"
    with that show "\<exists>D. ((\<lambda>x. f1 x y) has_real_derivative D) (at u) \<and> D \<le> 0"
      by - (rule exI conjI Df1 [unfolded df1_def] | simp)+
  next
    show "continuous_on {x..x'} (\<lambda>x. f1 x y)"
      using that by (intro continuous_on_subset [OF continuous_on_f1]) auto
  qed
  have f1f2: "f2 x' y \<le> f1 x y"
    if "x \<in> {1/2..1}" "x' \<in> {1/2..1}" "x \<le> x'" "x < 3/4" "\<not> x' < 3/4" for x x'::real
    using that
    apply (simp add: f2_def)
    by (smt (verit, best) divide_nonneg_nonneg f1 ln_le_zero_iff pos_prod_lt that)

  have f2: "f2 x' y \<le> f2 x y"
    if A: "x \<in> {1/2..1}" "x' \<in> {1/2..1}" "x \<le> x'" and B: "\<not> x < 3/4" for x x'::real
  proof (rule DERIV_nonpos_imp_decreasing_open [OF \<open>x \<le> x'\<close> , where f = "\<lambda>x. f2 x y"])
    fix u :: real
    assume u: "x < u" "u < x'"
    have "((\<lambda>x. f2 x y) has_real_derivative df1 u + delta u) (at u)"
      using u that by (intro Df2) auto
    moreover have "df1 u + delta u \<le> 0"
    proof -
      have "df1 (1/2) \<le> -1/2"
        unfolding df1_def by (approximation 20)
      moreover have "df1 u \<le> df1 (1/2)"
        using u that unfolding df1_def
        by (intro Transcendental.log_mono) (auto simp: divide_simps)
      moreover have "delta 1 \<le> 0.04"
        unfolding delta_def by (approximation 4)
      moreover have "delta u \<le> delta 1"
        using u that by (auto simp: delta_def divide_simps)
      ultimately show ?thesis
        by auto
    qed
    ultimately show "\<exists>D. ((\<lambda>x. f2 x y) has_real_derivative D) (at u) \<and> D \<le> 0"
      by blast
  next
    show "continuous_on {x..x'} (\<lambda>x. f2 x y)"
      unfolding f2_def
      using that by (intro continuous_on_subset [OF continuous_on_f1] continuous_intros) auto
  qed
  show ?thesis
    using f1 f1f2 f2 by (simp add: monotone_on_def ff_def)
qed

subsubsection \<open>Claims A.2--A.4\<close>

text \<open>Called simply @{term x} in the paper, but are you kidding me?\<close>
definition "x_of \<equiv> \<lambda>y::real. 3*y/5 + 0.5454"

lemma x_of: "x_of \<in> {0..3/4} \<rightarrow> {1/2..1}"
  by (simp add: x_of_def)

definition "y_of \<equiv> \<lambda>x::real. 5 * x/3 - 0.909"

lemma y_of_x_of [simp]: "y_of (x_of y) = y"
  by (simp add: x_of_def y_of_def add_divide_distrib)

lemma x_of_y_of [simp]: "x_of (y_of x) = x"
  by (simp add: x_of_def y_of_def divide_simps)

lemma Df1_y [derivative_intros]: 
  assumes "x<1"
  shows "((\<lambda>x. f1 x (y_of x)) has_real_derivative 5/3 + df1 x) (at x)"
proof -
  have "(2 - x * 2) = 2 * (1-x)"
    by simp
  then have [simp]: "log 2 (2 - x * 2) = log 2 (1-x) + 1"
    using log_mult [of 2 "1-x" 2] assms by (smt (verit, best) log_eq_one)
  show ?thesis
    using assms 
    unfolding f1_def y_of_def H_def df1_def
    apply -
    apply (rule derivative_eq_intros refl | simp)+
    apply (simp add: log_divide divide_simps)
    apply (simp add: algebra_simps)
    done
qed

lemma Df2_y [derivative_intros]: 
  assumes "1/2\<le>x" "x<1" 
  shows "((\<lambda>x. f2 x (y_of x)) has_real_derivative 5/3 + df1 x + delta x) (at x)"
  using assms unfolding f2_def delta_def
  apply -
  apply (rule derivative_eq_intros Df1 | simp)+
  apply (simp add: divide_simps power2_eq_square)
  done

definition "Dg_x \<equiv> \<lambda>y. 3 * log 2 (5/3) / 5 + log 2 ((2727 + y * 8000) / (y * 12500)) 
                     - 2727 / (ln 2 * (2727 + y * 8000))"

lemma Dg_x [derivative_intros]: 
  assumes "y \<in> {0<..<3/4}"
  shows "((\<lambda>y. gg (x_of y) y) has_real_derivative Dg_x y) (at y)"
  using assms 
  unfolding x_of_def gg_def GG_def Dg_x_def
  apply -
  apply (rule derivative_eq_intros refl | simp)+
  apply (simp add: field_simps)
  done

text \<open>Claim A2 is difficult because it comes *real close*: max value = 1.999281, when y = 0.4339.
There is no simple closed form for the maximum point
  (where the derivative goes to 0).
\<close>

text \<open>Due to the singularity at zero, we need to cover the zero case analytically, 
but at least interval arithmetic covers the maximum point\<close>
lemma A2: 
  assumes "y \<in> {0..3/4}"
  shows "gg (x_of y) y \<le> 2 - 1/2^11"
proof -
  have ?thesis if "y \<in> {0..1/10}"
  proof -
    have "gg (x_of y) y \<le> gg (x_of (1/10)) (1/10)"
    proof (rule DERIV_nonneg_imp_increasing_open [of y "1/10"])
      fix y' :: real
      assume y': "y < y'" "y' < 1/10"
      then have "y'>0"
        using that by auto
      show "\<exists>D. ((\<lambda>u. gg (x_of u) u) has_real_derivative D) (at y') \<and> 0 \<le> D"
      proof (intro exI conjI)
        show "((\<lambda>u. gg (x_of u) u) has_real_derivative Dg_x y') (at y')"
          using y' that by (intro derivative_eq_intros) auto
      next
        define Num where "Num \<equiv> 3 * log 2 (5/3) / 5 * (ln 2 * (2727 + y' * 8000)) + log 2 ((2727 + y' * 8000) / (y' * 12500)) * (ln 2 * (2727 + y' * 8000)) - 2727"
        have A: "835.81 \<le> 3 * log 2 (5/3) / 5 * ln 2 * 2727"
          by (approximation 25)
        have B: "2451.9 \<le> 3 * log 2 (5/3) / 5 * ln 2 * 8000"
          by (approximation 25)
        have C: "Dg_x y' = Num / (ln 2 * (2727 + y' * 8000))"
          using \<open>y'>0\<close> by (simp add: Dg_x_def Num_def add_divide_distrib diff_divide_distrib)
        have "0 \<le> -1891.19 + log 2 (2727 / 1250) * (ln 2 * (2727))"
          by (approximation 6)
        also have "\<dots> \<le> -1891.19 + 2451.9 * y' + log 2 ((2727 + y' * 8000) / (y' * 12500)) * (ln 2 * (2727 + y' * 8000)) "
          using y' \<open>0 < y'\<close>
          by (intro add_mono mult_mono Transcendental.log_mono frac_le order.refl) auto
        also have "\<dots> = 835.81 + 2451.9 * y' + log 2 ((2727 + y' * 8000) / (y' * 12500)) * (ln 2 * (2727 + y' * 8000)) 
              - 2727"
          by simp 
        also have "\<dots> \<le> Num"
          using A mult_right_mono [OF B, of y'] \<open>y'>0\<close>
          unfolding Num_def ring_distribs
          by (intro add_mono diff_mono order.refl) (auto simp: mult_ac)
        finally have "Num \<ge> 0" .
        with C show "0 \<le> Dg_x y'"
          using \<open>0 < y'\<close> by auto
      qed
    next
      let ?f = "\<lambda>x. x * log 2 ((16*x/5 + 2727/2500) / (5*x))"
      have \<dagger>: "continuous_on {0..} ?f"
      proof -
        have "continuous (at x within {0..}) ?f"
          if "x \<ge> 0" for x :: real
        proof (cases "x = 0")
          case True
          have "continuous (at_right 0) ?f"
            unfolding continuous_within by real_asymp
          thus ?thesis
            using True by (simp add: at_within_Ici_at_right)
        qed (use that in \<open>auto intro!: continuous_intros\<close>)
        thus ?thesis
          by (simp add: continuous_on_eq_continuous_within)
      qed
      show "continuous_on {y..1/10} (\<lambda>y. gg (x_of y) y)"
        unfolding gg_eq x_of_def using that
        by (force intro: continuous_on_subset [OF \<dagger>] continuous_intros)
    qed (use that in auto)
    also have "\<dots> \<le> 2 - 1/2^11"
      unfolding gg_eq x_of_def by (approximation 10)
    finally show ?thesis .
  qed
  moreover
  have ?thesis if "y \<in> {1/10 .. 3/4}"
    using that unfolding gg_eq x_of_def 
    by (approximation 24 splitting: y = 12)   \<comment>\<open>many thanks to Fabian Immler\<close>
  ultimately show ?thesis
    by (meson assms atLeastAtMost_iff linear)
qed

lemma A3: 
  assumes "y \<in> {0..0.341}"
  shows "f1 (x_of y) y \<le> 2 - 1/2^11"
proof -
  define D where "D \<equiv> \<lambda>x. 5/3 + df1 x"
  define I where "I \<equiv> {0.5454 .. 3/4::real}"
  define x where "x \<equiv> x_of y"
  then have yeq: "y = y_of x"
    by (metis y_of_x_of)
  have "x \<in> {x_of 0 .. x_of 0.341}"
    using assms by (simp add: x_def x_of_def)
  then have x: "x \<in> I"
    by (simp add: x_of_def I_def)
  have D: "((\<lambda>x. f1 x (y_of x)) has_real_derivative D x) (at x)" if "x \<in> I" for x
    using that Df1_y by (force simp: D_def I_def)
  have Dgt0: "D x \<ge> 0" if "x \<in> I" for x
    using that unfolding D_def df1_def I_def by (approximation 10)
  have "f1 x y = f1 x (y_of x)"
    by (simp add: yeq)
  also have "\<dots> \<le> f1 (3/4) (y_of (3/4))"
    using x Dgt0
    by (force simp: I_def intro!: D DERIV_nonneg_imp_nondecreasing [where f = "\<lambda>x. f1 x (y_of x)"])
  also have "\<dots> < 1.994"
    by (simp add: f1_def H_def y_of_def) (approximation 50)
  also have "\<dots> < 2 - 1/2^11"
    by (approximation 50)
  finally show ?thesis
    using x_def by auto
qed

text \<open>This one also comes close: max value = 1.999271, when y = 0.4526. 
The specified upper bound is 1.99951\<close>
lemma A4: 
  assumes "y \<in> {0.341..3/4}"
  shows "f2 (x_of y) y \<le> 2 - 1/2^11"
  unfolding f2_def f1_def x_of_def H_def
  using assms by (approximation 18 splitting: y = 13)


context P0_min
begin 

text \<open>The truly horrible Lemma 12.3\<close>
lemma 123:
  assumes "\<delta> \<le> 1 / 2^11"
  shows "(SUP x \<in> {0..1}. SUP y \<in> {0..3/4}. ffGG (2/5) x y) \<le> 2-\<delta>"
proof -
  have "min (ff x y) (gg x y) \<le> 2 - 1/2^11" if "x \<in> {0..1}" "y \<in> {0..3/4}" for x y
  proof (cases "x \<le> x_of y")
    case True
    with that have "gg x y \<le> gg (x_of y) y"
      by (intro gg_increasing) auto
    with A2 that show ?thesis
      by fastforce
  next
    case False
    with that have "ff x y \<le> ff (x_of y) y"
      by (intro monotone_onD [OF antimono_on_ff]) (auto simp: x_of_def)
    also have "\<dots> \<le> 2 - 1/2^11"
    proof (cases "x_of y < 3/4")
      case True
      with that have "f1 (x_of y) y \<le> 2 - 1/2^11"
        by (intro A3) (auto simp: x_of_def)
      then show ?thesis
        using True ff_def by presburger
    next
      case False
      with that have "f2 (x_of y) y \<le> 2 - 1/2^11"
        by (intro A4) (auto simp: x_of_def)
      then show ?thesis
        using False ff_def by presburger
    qed
    finally show ?thesis
      by linarith 
  qed
  moreover have "2 - 1/2^11 \<le> 2-\<delta>"
    using assms by auto
  ultimately show ?thesis
    by (fastforce simp: ffGG_def gg_def intro!: cSUP_least)
qed

end (*P0_min*)

subsection \<open>Concluding the proof\<close>

text \<open>we subtract a tiny bit, as we seem to need this gap\<close>
definition delta'::real where "delta' \<equiv> 1 / 2^11 - 1 / 2^18"

lemma Aux_1_1:
  assumes p0_min12: "p0_min \<le> 1/2"
  shows "\<forall>\<^sup>\<infinity>k. log 2 (RN k k) / k \<le> 2 - delta'"
proof -
  define p0_min::real where "p0_min \<equiv> 1/2"
  interpret P0_min p0_min
  proof qed (auto simp: p0_min_def)
  define \<delta>::real where "\<delta> \<equiv> 1 / 2^11"
  define \<eta>::real where "\<eta> \<equiv> 1 / 2^18"
  have \<eta>: "0 < \<eta>" "\<eta> \<le> 1/12"
    by (auto simp: \<eta>_def)
  define \<mu>::real where "\<mu> \<equiv> 2/5"
  have "\<forall>\<^sup>\<infinity>k. Big_From_11_1 \<eta> \<mu> k"
    unfolding \<mu>_def using \<eta> by (intro Big_From_11_1) auto
  moreover have "log 2 (real (RN k k)) / k \<le> 2-\<delta> + \<eta>" if "Big_From_11_1 \<eta> \<mu> k" for k
  proof -
    have *: "(\<Squnion>y\<in>{0..3/4}. ffGG \<mu> x y + \<eta>) = (\<Squnion>y\<in>{0..3/4}. ffGG \<mu> x y) + \<eta>"
      if "x\<le>1" for x
      using bdd_above_ff_GG [OF that, of "3/4" \<mu> 0]
      by (simp add: add.commute [of _ \<eta>] Sup_add_eq)
    have "log 2 (RN k k) / k \<le> (SUP x \<in> {0..1}. SUP y \<in> {0..3/4}. ffGG \<mu> x y + \<eta>)"
      using that p0_min12 \<eta> \<mu>_def
      by (intro From_11_1) (auto simp: p0_min_def)
    also have "\<dots> \<le> (SUP x \<in> {0..1}. (SUP y \<in> {0..3/4}. ffGG \<mu> x y) + \<eta>)"
    proof (intro cSUP_subset_mono bdd_above.I2 [where M = "4+\<eta>"])
      fix x :: real
      assume x: "x \<in> {0..1}"
      have "(\<Squnion>y\<in>{0..3/4}. ffGG \<mu> x y + \<eta>) \<le> 4 + \<eta>"
        using bdd_above_ff_GG ff_GG_bound x by (simp add: cSup_le_iff)
      with * x show "(\<Squnion>y\<in>{0..3/4}. ffGG \<mu> x y) + \<eta> \<le> 4 + \<eta>" 
        by simp
    qed (use * in auto)
    also have "\<dots> = (SUP x \<in> {0..1}. SUP y \<in> {0..3/4}. ffGG \<mu> x y) + \<eta>"
      using bdd_above_SUP_ff_GG [of "3/4"  \<mu> 0]
      by (simp add: add.commute [of _ \<eta>] Sup_add_eq)
    also have "\<dots> \<le> 2-\<delta> + \<eta>"
      using 123 [of "1 / 2^11"]
      unfolding \<delta>_def ffGG_def by (auto simp: \<delta>_def ffGG_def \<mu>_def)
    finally show ?thesis .
  qed
  ultimately have "\<forall>\<^sup>\<infinity>k. log 2 (RN k k) / k \<le> 2-\<delta> + \<eta>"
    by (metis (lifting) eventually_mono)
  then show ?thesis
    by (simp add: \<delta>_def \<eta>_def delta'_def)
qed

text \<open>Main theorem 1.1: the exponent is approximately 3.9987\<close>
theorem Main_1_1:
  obtains \<epsilon>::real where "\<epsilon>>0" "\<forall>\<^sup>\<infinity>k. RN k k \<le> (4-\<epsilon>)^k"
proof
  let ?\<epsilon> = "0.00134::real"
  have "\<forall>\<^sup>\<infinity>k. k>0 \<and> log 2 (RN k k) / k \<le> 2 - delta'"
    unfolding eventually_conj_iff using Aux_1_1 eventually_gt_at_top by blast 
  then have "\<forall>\<^sup>\<infinity>k. RN k k \<le> (2 powr (2-delta')) ^ k"
  proof (eventually_elim)
    case (elim k)
    then have "log 2 (RN k k) \<le> (2-delta') * k"
      by (meson of_nat_0_less_iff pos_divide_le_eq)
    then have "RN k k \<le> 2 powr ((2-delta') * k)"
      by (smt (verit, best) Transcendental.log_le_iff powr_ge_zero)
    then show "RN k k \<le> (2 powr (2-delta')) ^ k"
      by (simp add: mult.commute powr_power)
  qed
  moreover have "2 powr (2-delta') \<le> 4 - ?\<epsilon>"
    unfolding delta'_def by (approximation 25)
  ultimately show "\<forall>\<^sup>\<infinity>k. real (RN k k) \<le> (4-?\<epsilon>) ^ k"
    by (smt (verit) power_mono powr_ge_zero eventually_mono)
qed auto

end
