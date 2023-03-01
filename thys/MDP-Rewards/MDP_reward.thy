(* Author: Maximilian Schäffeler *)

theory MDP_reward
  imports
    Bounded_Functions
    MDP_reward_Util
    Blinfun_Util
    MDP_disc
begin

section \<open>Markov Decision Processes with Rewards\<close>

locale MDP_reward = discrete_MDP A K
  for
    A and 
    K :: "'s ::countable \<times> 'a ::countable \<Rightarrow> 's pmf" +
  fixes
    r :: "('s \<times> 'a) \<Rightarrow> real" and
    l :: real
  assumes
    zero_le_disc [simp]: "0 \<le> l" and
    r_bounded: "bounded (range r)"
begin

text \<open>
This extension to the basic MDPs is formalized with another locale.
It assumes the existence of a reward function @{term r} which takes a state-action pair to a real 
number. We assume that the function is bounded @{prop r_bounded}.

Furthermore, we fix a discounting factor @{term l}, where @{term "0 \<le> l \<and> l < 1"}.
\<close>

subsection \<open>Util\<close>
subsubsection \<open>Basic Properties of rewards\<close>
lemma r_bfun: "r \<in> bfun"
  using r_bounded
  by auto

lemma r_bounded': "bounded (r ` X)"
  by (auto intro: r_bounded bounded_subset)

definition "r\<^sub>M = (\<Squnion>sa. \<bar>r sa\<bar>)"

lemma abs_r_le_r\<^sub>M: "\<bar>r sa\<bar> \<le> r\<^sub>M"
  using bounded_norm_le_SUP_norm r_bounded r\<^sub>M_def by fastforce

lemma abs_r\<^sub>M_eq_r\<^sub>M [simp]: "\<bar>r\<^sub>M\<bar> = r\<^sub>M"
  using abs_r_le_r\<^sub>M by fastforce

lemma r\<^sub>M_nonneg: "0 \<le> r\<^sub>M"
  using abs_r\<^sub>M_eq_r\<^sub>M by linarith

lemma measurable_r_nth [measurable]: "(\<lambda>t. r (t !! i)) \<in> borel_measurable S"
  by measurable

lemma integrable_r_nth [simp]: "integrable (\<T> p s) (\<lambda>t. r (t !! i))"
  by (fastforce simp: bounded_iff intro: abs_r_le_r\<^sub>M)

lemma expectation_abs_r_le: "measure_pmf.expectation d (\<lambda>a. \<bar>r (s, a)\<bar>) \<le> r\<^sub>M"
  using abs_r_le_r\<^sub>M
  by (fastforce intro!: measure_pmf.integral_le_const measure_pmf.integrable_const_bound)

lemma abs_exp_r_le: "\<bar>measure_pmf.expectation d r\<bar> \<le> r\<^sub>M"
  using abs_r_le_r\<^sub>M
  by (fastforce intro!: measure_pmf.integral_le_const order.trans[OF integral_abs_bound] measure_pmf.integrable_const_bound)

subsubsection \<open>Infinite disounted sums\<close>
lemma abs_disc_eq[simp]: "\<bar>l ^ i * x\<bar> = l ^ i * \<bar>x\<bar>"
  by (auto simp: abs_mult)

lemma norm_l_pow_eq[simp]: "norm (l^t *\<^sub>R F) = l^t * norm F"
  by auto

subsection \<open>Total Reward for Single Traces\<close>

abbreviation "\<nu>_trace_fin t N \<equiv> \<Sum>i < N. l ^ i * r (t !! i)"
abbreviation "\<nu>_trace t \<equiv> \<Sum>i. l ^ i * r (t !! i)"

lemma abs_\<nu>_trace_fin_le: "\<bar>\<nu>_trace_fin t N\<bar> \<le> (\<Sum>i < N. l^i * r\<^sub>M)"
  by (auto intro!: sum_mono order.trans[OF sum_abs] mult_left_mono abs_r_le_r\<^sub>M)

lemma measurable_suminf_reward[measurable]: "\<nu>_trace \<in> borel_measurable S"
  by measurable

lemma integrable_\<nu>_trace_fin: "integrable (\<T> p s) (\<lambda>t. \<nu>_trace_fin t N)"
  by (fastforce simp: bounded_iff intro: abs_\<nu>_trace_fin_le)


context 
  fixes p :: "('s, 'a) pol"
begin

subsection \<open>Expected Finite-Horizon Discounted Reward\<close>
definition "\<nu>_fin n s = \<integral>t. \<nu>_trace_fin t n \<partial>\<T> p s"

lemma abs_\<nu>_fin_le: "\<bar>\<nu>_fin N s\<bar> \<le> (\<Sum>i<N. l^i * r\<^sub>M)"
  unfolding \<nu>_fin_def
  using abs_\<nu>_trace_fin_le
  by (fastforce intro!: prob_space.integral_le_const order_trans[OF integral_abs_bound])

lemma \<nu>_fin_bfun: "(\<lambda>s. \<nu>_fin N s) \<in> bfun"
  by (auto intro!: abs_\<nu>_fin_le)

lift_definition \<nu>\<^sub>b_fin :: "nat \<Rightarrow> 's \<Rightarrow>\<^sub>b real" is \<nu>_fin
  using \<nu>_fin_bfun .

lemma \<nu>_fin_Suc[simp]: "\<nu>_fin (Suc n) s = \<nu>_fin n s + l ^ n * \<integral>t.  r (t !! n) \<partial>\<T> p s"
  by (simp add: \<nu>_fin_def)

lemma \<nu>_fin_zero[simp]: "\<nu>_fin 0 s = 0"
  by (simp add: \<nu>_fin_def)

lemma \<nu>_fin_eq_Pn: "\<nu>_fin n s = (\<Sum>i<n. l^i * measure_pmf.expectation (Pn' p s i) r)"
  by (induction n) (auto simp: Pn'_eq_\<T> integral_distr)
end

subsection \<open>Expected Total Discounted Reward\<close>

definition "\<nu> p s = lim (\<lambda>n. \<nu>_fin p n s)"

lemmas \<nu>_eq_lim = \<nu>_def

lemma \<nu>_eq_Pn: "\<nu> p s = (\<Sum>i. l^i * measure_pmf.expectation (Pn' p s i) r)"
  by (simp add: \<nu>_fin_eq_Pn \<nu>_eq_lim suminf_eq_lim)


subsection \<open>Reward of a Decision Rule\<close>
context 
  fixes d :: "('s, 'a) dec"
begin
abbreviation "r_dec s \<equiv> \<integral>a. r (s, a) \<partial>d s"

lemma abs_r_dec_le: "\<bar>r_dec s\<bar> \<le> r\<^sub>M"
  using expectation_abs_r_le integral_abs_bound order_trans by fast

lemma r_dec_eq_r_K0: "r_dec s = measure_pmf.expectation (K0' d s) r"
  by (simp add: K0'_def)

lemma r_dec_bfun: "r_dec \<in> bfun"
  using abs_r_dec_le by (auto intro!: bfun_normI)

lift_definition r_dec\<^sub>b :: "'s \<Rightarrow>\<^sub>b real" is "r_dec"
  using r_dec_bfun .

declare r_dec\<^sub>b.rep_eq[simp] bfun.Bfun_inverse[simp]

lemma norm_r_dec_le: "norm r_dec\<^sub>b \<le> r\<^sub>M"
  by (simp add: abs_r_dec_le norm_bound)
end

lemma r_dec_det [simp]: "r_dec (mk_dec_det d) s = r (s, d s)"
  unfolding mk_dec_det_def by auto

subsection \<open>Transition Probability Matrix for MDPs\<close>

context
  fixes p :: "nat \<Rightarrow> ('s, 'a) dec"
begin
definition "\<P>\<^sub>X n = push_exp (\<lambda>s. Xn' (mk_markovian p) s n)"

lemma \<P>\<^sub>X_0[simp]: "\<P>\<^sub>X 0 = id"
  by (simp add: \<P>\<^sub>X_def)

lemma \<P>\<^sub>X_bounded_linear[simp]: "bounded_linear (\<P>\<^sub>X t)"
  unfolding \<P>\<^sub>X_def by simp

lemma norm_\<P>\<^sub>X [simp]: "onorm (\<P>\<^sub>X t) = 1"
  unfolding \<P>\<^sub>X_def by simp

lemma norm_\<P>\<^sub>X_apply[simp]: "norm (\<P>\<^sub>X n x) \<le> norm x"
  using onorm[OF \<P>\<^sub>X_bounded_linear] by simp

lemma \<P>\<^sub>X_bound_r: "norm (\<P>\<^sub>X t (r_dec\<^sub>b (p t))) \<le> r\<^sub>M"
  using norm_\<P>\<^sub>X_apply norm_r_dec_le order.trans by blast

lemma \<P>\<^sub>X_bounded_r: "bounded (range (\<lambda>t. (\<P>\<^sub>X t (r_dec\<^sub>b (p t)))))"
  using \<P>\<^sub>X_bound_r by (auto intro!: boundedI)

end

lemma \<nu>_fin_elem: "\<nu>_fin (mk_markovian p) n s = (\<Sum>i<n. l^i * \<P>\<^sub>X p i (r_dec\<^sub>b (p i)) s)"
  unfolding \<P>\<^sub>X_def \<nu>_fin_eq_Pn Pn'_markovian_eq_Xn'_bind measure_pmf_bind
  using measure_pmf_in_subprob_algebra abs_r_le_r\<^sub>M
  by (subst integral_bind) (auto simp: r_dec_eq_r_K0)

lemma \<nu>\<^sub>b_fin_eq_\<P>\<^sub>X: "\<nu>\<^sub>b_fin (mk_markovian p) n = (\<Sum>i<n. l^i *\<^sub>R \<P>\<^sub>X p i (r_dec\<^sub>b (p i)))"
  by (auto simp: \<nu>_fin_elem sum_apply_bfun \<nu>\<^sub>b_fin.rep_eq)

lemma \<nu>_fin_eq_\<P>\<^sub>X: "\<nu>_fin (mk_markovian p) n = (\<Sum>i<n. l^i *\<^sub>R \<P>\<^sub>X p i (r_dec\<^sub>b (p i)))"
  by (metis \<nu>\<^sub>b_fin.rep_eq \<nu>\<^sub>b_fin_eq_\<P>\<^sub>X)


text \<open>
@{term "\<P>\<^sub>1 d v"} defines for each state the expected value of @{term v} 
after taking a single step in the MDP according to the decision rule @{term d}.  
\<close>

context
  fixes d :: "('s, 'a) dec"
begin
lift_definition \<P>\<^sub>1 :: "('s \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('s \<Rightarrow>\<^sub>b real)" is "push_exp (K_st d)"
  using push_exp_bounded_linear .

lemma \<P>\<^sub>1_bfun_one [simp]:"\<P>\<^sub>1 1 = 1"
  by (auto simp: \<P>\<^sub>1.rep_eq)

lemma \<P>\<^sub>1_pow_bfun_one [simp]: "(\<P>\<^sub>1^^t) 1 = 1"
  by (induction t) auto

lemma \<P>\<^sub>1_pow: "blinfun_apply (\<P>\<^sub>1 ^^ n) = blinfun_apply \<P>\<^sub>1 ^^ n"
  by (induction n) auto

lemma norm_\<P>\<^sub>1 [simp]: "norm \<P>\<^sub>1 = 1"
  by (simp add: norm_blinfun.rep_eq \<P>\<^sub>1.rep_eq)
end

lemma \<P>\<^sub>X_Suc: "\<P>\<^sub>X p (Suc n) v = \<P>\<^sub>1 (p 0) ((\<P>\<^sub>X (\<lambda>n. p (Suc n)) n) v)"
  unfolding \<P>\<^sub>X_def \<P>\<^sub>1.rep_eq
  by (fastforce intro!: abs_le_norm_bfun integral_bind[where K = "count_space UNIV"]
      simp: measure_pmf_in_subprob_algebra measure_pmf_bind Suc_Xn'_markovian)

lemma \<P>\<^sub>X_Suc': "\<P>\<^sub>X p (Suc n) v = \<P>\<^sub>X p n (\<P>\<^sub>1 (p n) v)"
proof (induction n arbitrary: p)
  case 0
  thus ?case
    by (simp add: \<P>\<^sub>X_Suc)
next
  case (Suc n)
  thus ?case 
    by (metis \<P>\<^sub>X_Suc)
qed

lemma \<P>\<^sub>X_const: "\<P>\<^sub>X (\<lambda>_. d) n = \<P>\<^sub>1 d ^^ n"
  by (induction n) (auto simp add: \<P>\<^sub>1_pow \<P>\<^sub>X_Suc)

lemma \<P>\<^sub>X_sconst: "\<P>\<^sub>X (\<lambda>_. p) n = \<P>\<^sub>1 p ^^n"
  using \<P>\<^sub>X_const.

lemma norm_P_n[simp]: "onorm (\<P>\<^sub>1 d ^^ n) = 1"
  using norm_\<P>\<^sub>X[of "\<lambda>_. d"] by (auto simp: \<P>\<^sub>X_sconst)

lemma norm_\<P>\<^sub>1_pow [simp]: "norm (\<P>\<^sub>1 d ^^ t) = 1"
  by (simp add: norm_blinfun.rep_eq)

lemma \<P>\<^sub>X_Suc_n_elem: "\<P>\<^sub>X p n (\<P>\<^sub>1 (p n) v) = \<P>\<^sub>X p (Suc n) v"
  using \<P>\<^sub>X_Suc' \<P>\<^sub>1.rep_eq by auto

lemma \<P>\<^sub>1_eq_\<P>\<^sub>X_one: "blinfun_apply (\<P>\<^sub>1 (p 0)) = \<P>\<^sub>X p 1"
  by (auto simp: \<P>\<^sub>X_Suc' \<P>\<^sub>1.rep_eq)


lemma \<P>\<^sub>1_pos: "0 \<le> u \<Longrightarrow> 0 \<le> \<P>\<^sub>1 d u"
  by (auto simp: \<P>\<^sub>1.rep_eq less_eq_bfun_def)

lemma \<P>\<^sub>1_nonneg: "nonneg_blinfun (\<P>\<^sub>1 d)"
  by (simp add: \<P>\<^sub>1_pos nonneg_blinfun_def)

lemma \<P>\<^sub>1_n_pos: "0 \<le> u \<Longrightarrow> 0 \<le> (\<P>\<^sub>1 d ^^ n) u"
  by (induction n) (auto simp: \<P>\<^sub>1.rep_eq less_eq_bfun_def)

lemma \<P>\<^sub>1_n_nonneg: "nonneg_blinfun (\<P>\<^sub>1 d ^^ n)"
  by (simp add: \<P>\<^sub>1_n_pos nonneg_blinfun_def)

lemma \<P>\<^sub>1_n_disc_pos: "0 \<le> u \<Longrightarrow> 0 \<le> (l^n *\<^sub>R \<P>\<^sub>1 d ^^n) u"
  by (auto simp: \<P>\<^sub>1_n_pos scaleR_nonneg_nonneg blinfun.scaleR_left)

lemma \<P>\<^sub>1_sum_pos: "0 \<le> u \<Longrightarrow> 0 \<le> (\<Sum>t\<le>n. l^t *\<^sub>R (\<P>\<^sub>1 d ^^ t)) u"
  using \<P>\<^sub>1_n_pos \<P>\<^sub>1_pos
  by (induction n) (auto simp: blinfun.add_left blinfun.scaleR_left scaleR_nonneg_nonneg)

lemma \<P>\<^sub>1_sum_ge: 
  assumes "0 \<le> u" 
  shows "u \<le> (\<Sum>t\<le>n. l^t *\<^sub>R \<P>\<^sub>1 d ^^t) u"
  using \<P>\<^sub>1_n_disc_pos[OF assms, of "Suc _"]
  by (induction n) (auto intro: add_increasing2 simp add: blinfun.add_left)


subsection \<open>The Bellman Operator\<close>
definition "L d v \<equiv> r_dec\<^sub>b d + l *\<^sub>R \<P>\<^sub>1 d v"

lemma norm_L_le: "norm (L d v) \<le> r\<^sub>M + l * norm v"
  using norm_blinfun[of "\<P>\<^sub>1 d"] norm_\<P>\<^sub>1 norm_r_dec_le
  by (auto intro!: norm_add_rule_thm mult_left_mono simp: L_def)

lemma abs_L_le: "\<bar>L d v s\<bar> \<le> r\<^sub>M + l * norm v"
  using order.trans[OF norm_le_norm_bfun norm_L_le] by auto

subsubsection \<open>Bellman Operator for Single Actions\<close>
abbreviation "L\<^sub>a a v s \<equiv> r (s, a) + l * measure_pmf.expectation (K (s,a)) v"

lemma L\<^sub>a_le:
  fixes v :: "'s \<Rightarrow>\<^sub>b real"
  shows "\<bar>L\<^sub>a a v s\<bar> \<le> r\<^sub>M + l * norm v"
  using abs_r_le_r\<^sub>M
  by (fastforce intro: order_trans[OF abs_triangle_ineq] order_trans[OF integral_abs_bound]  
      add_mono mult_mono measure_pmf.integral_le_const abs_le_norm_bfun 
      simp: abs_mult)

lemma L\<^sub>a_bounded:
  "bounded (range (\<lambda>a. L\<^sub>a a (apply_bfun v) s))"
  using L\<^sub>a_le by (auto intro!: boundedI)

lemma L\<^sub>a_int: 
  fixes d :: "'a pmf" and v :: "'s \<Rightarrow>\<^sub>b real"
  shows "(\<integral>a. L\<^sub>a a v s \<partial>d) = (\<integral>a. r (s, a) \<partial>d) + l * \<integral>a. \<integral>s'. v s' \<partial>K (s, a) \<partial>d"
proof (subst Bochner_Integration.integral_add)
  show "integrable d (\<lambda>a. r (s, a))"
    using abs_r_le_r\<^sub>M by (fastforce intro!: bounded_integrable simp: bounded_iff)
  show "integrable d (\<lambda>a. l * \<integral>s'. v s' \<partial>K (s, a))"
    by (intro bounded_integrable) 
      (auto intro!: mult_mono order_trans[OF integral_abs_bound] boundedI[of _ "l * norm v"]
        measure_pmf.integral_le_const simp: abs_le_norm_bfun abs_mult)
qed auto

lemma L_eq_L\<^sub>a: "L d v s = measure_pmf.expectation (d s) (\<lambda>a. L\<^sub>a a v s)"
  unfolding L\<^sub>a_int L_def K_st_def \<P>\<^sub>1.rep_eq
  by (auto simp: measure_pmf_bind integral_measure_pmf_bind[where B = "norm v"] abs_le_norm_bfun)

lemma L_eq_L\<^sub>a_det: "L (mk_dec_det d) v s = L\<^sub>a (d s) v s"
  by (auto simp: L_eq_L\<^sub>a mk_dec_det_def)

lemma L\<^sub>a_eq_L: "measure_pmf.expectation p (\<lambda>a. L\<^sub>a a (apply_bfun v) s) = 
  L (\<lambda>t. if t = s then p else return_pmf (SOME a. a \<in> A t)) v s"
  unfolding L_eq_L\<^sub>a by auto

lemma L_le: "L d v s \<le> r\<^sub>M + l * norm v"
  unfolding L_def
  using norm_\<P>\<^sub>1 norm_blinfun[of "(\<P>\<^sub>1 d)"] abs_r_dec_le
  by (fastforce intro: order_trans[OF le_norm_bfun] add_mono mult_left_mono dest: abs_le_D1)

lemma L\<^sub>a_le': "L\<^sub>a a (apply_bfun v) s \<le> r\<^sub>M + l * norm v"
  using L\<^sub>a_le abs_le_D1 by blast


subsection \<open>Optimality Equations\<close>

definition "\<L> (v :: 's \<Rightarrow>\<^sub>b real) s = (\<Squnion>d \<in> D\<^sub>R. L d v s)"

lemma \<L>_bfun: "\<L> v \<in> bfun"
  unfolding \<L>_def using abs_L_le ex_dec by (fastforce intro!: cSup_abs_le bfun_normI)

lift_definition \<L>\<^sub>b :: "('s \<Rightarrow>\<^sub>b real) \<Rightarrow> 's \<Rightarrow>\<^sub>b real" is \<L>
  using \<L>_bfun .

lemma L_bounded[simp, intro]: "bounded (range (\<lambda>p. L p v s))"
  using abs_L_le by (auto intro!: boundedI)

lemma L_bounded'[simp, intro]: "bounded ((\<lambda>p. L p v s) ` X)"
  by (auto intro: bounded_subset)

lemma L_bdd_above[simp, intro]: "bdd_above ((\<lambda>p. L p v s) ` X)"
  by (auto intro: bounded_imp_bdd_above)

lemma L_le_\<L>\<^sub>b: "is_dec d \<Longrightarrow> L d v \<le> \<L>\<^sub>b v"
  by (fastforce simp: \<L>\<^sub>b.rep_eq \<L>_def intro!: cSUP_upper)

subsubsection \<open>Equivalences involving @{const \<L>\<^sub>b}\<close>

lemma SUP_step_MR_eq:
  "\<L> v s = (\<Squnion>pa \<in> {pa. set_pmf pa \<subseteq> A s}. (\<integral>a. L\<^sub>a a v s \<partial>measure_pmf pa))"
  unfolding \<L>_def
proof (intro antisym)
  show "(\<Squnion>d\<in>D\<^sub>R. L d v s) \<le> (\<Squnion>pa \<in> {pa. set_pmf pa \<subseteq> A s}. \<integral>a. L\<^sub>a a v s \<partial>measure_pmf pa)"
  proof (rule cSUP_mono)
    show "D\<^sub>R \<noteq> {}"
      using D\<^sub>R_ne .
  next show "bdd_above ((\<lambda>pa. \<integral>a. L\<^sub>a a v s \<partial>measure_pmf pa) ` {pa. set_pmf pa \<subseteq> A s})"
      using L\<^sub>a_bounded L\<^sub>a_le
      by (auto intro!: order_trans[OF integral_abs_bound] 
          bounded_imp_bdd_above boundedI[where B = "r\<^sub>M + l * norm v"] 
          measure_pmf.integral_le_const bounded_integrable)
  next show "\<exists>m\<in>{pa. set_pmf pa \<subseteq> A s}. L n v s \<le> \<integral>a. L\<^sub>a a v s \<partial>measure_pmf m" if "n \<in> D\<^sub>R" for n
      using that
      by (fastforce simp: L_eq_L\<^sub>a L\<^sub>a_int is_dec_def)
  qed
next
  have aux: "{pa. set_pmf pa \<subseteq> A s} \<noteq> {}"
    using D\<^sub>R_ne is_dec_def by auto
  show "(\<Squnion>pa\<in>{pa. set_pmf pa \<subseteq> A s}. \<integral>a. L\<^sub>a a v s \<partial>measure_pmf pa) \<le> (\<Squnion>d\<in>D\<^sub>R. L d v s)"
  proof (intro cSUP_least[OF aux] cSUP_upper2)
    fix n 
    assume h: "n \<in> {pa. set_pmf pa \<subseteq> A s}"
    let ?p = "(\<lambda>s'. if s = s' then n else SOME a. set_pmf a \<subseteq> A s')"
    have aux: "\<exists>a. set_pmf a \<subseteq> A sa" for sa
      using ex_dec is_dec_def by blast
    show "?p \<in> D\<^sub>R"
      unfolding is_dec_def using h someI_ex[OF aux] by auto
    thus "(\<integral>a. L\<^sub>a a v s \<partial>n) \<le> L ?p v s"
      by (auto simp: L_eq_L\<^sub>a)
    show "bdd_above ((\<lambda>d. L d v s) ` D\<^sub>R)"
      by (fastforce intro!: bounded_imp_bdd_above simp: bounded_def)
  next
  qed
qed

lemma \<L>\<^sub>b_eq_SUP_L\<^sub>a: "\<L>\<^sub>b v s = (\<Squnion>p \<in> {p. set_pmf p \<subseteq> A s}. \<integral>a. L\<^sub>a a v s \<partial>measure_pmf p)"
  using SUP_step_MR_eq \<L>\<^sub>b.rep_eq by presburger

lemma SUP_step_det_eq: "(\<Squnion>d \<in> D\<^sub>D. L (mk_dec_det d) v s) = (\<Squnion>a \<in> A s. L\<^sub>a a v s)"
proof (intro antisym cSUP_mono)
  show "bdd_above ((\<lambda>a. L\<^sub>a a v s) ` A s)"
    using L\<^sub>a_bounded by (fastforce intro!: bounded_imp_bdd_above simp: bounded_def)
  show "bdd_above ((\<lambda>d. L (mk_dec_det d) v s) ` D\<^sub>D)"
    by (auto intro!: bounded_imp_bdd_above boundedI abs_L_le)
  show "\<exists>m\<in>A s. L (mk_dec_det n) v s \<le> L\<^sub>a m v s" if "n \<in> D\<^sub>D" for n
    using that is_dec_det_def by (auto simp: L_eq_L\<^sub>a_det intro: bexI[of _ "n s"])
  show "\<exists>m\<in>D\<^sub>D. L\<^sub>a n v s \<le> L (mk_dec_det m) v s" if "n \<in> A s" for n
    using that A_ne
    by (fastforce simp: L_eq_L\<^sub>a_det is_dec_det_def some_in_eq
        intro!: bexI[of _ "\<lambda>s'. if s = s' then _ else SOME a. a \<in> A s'"])
qed (auto simp: A_ne)

lemma integrable_L\<^sub>a: "integrable (measure_pmf x) (\<lambda>a. L\<^sub>a a (apply_bfun v) s)"
proof (intro Bochner_Integration.integrable_add integrable_mult_right)
  show "integrable (measure_pmf x) (\<lambda>x. r (s, x))"
    using abs_r_le_r\<^sub>M 
    by (auto intro: measure_pmf.integrable_const_bound[of _ "r\<^sub>M"])
next
  show "integrable (measure_pmf x) (\<lambda>x. measure_pmf.expectation (K (s, x)) v)"
    by (auto intro!: bounded_integrable boundedI order.trans[OF integral_abs_bound] 
        measure_pmf.integral_le_const abs_le_norm_bfun)
qed

lemma SUP_L\<^sub>a_eq_det:
  fixes v :: "'s \<Rightarrow>\<^sub>b real"
  shows "(\<Squnion>p\<in>{p. set_pmf p \<subseteq> A s}. \<integral>a. L\<^sub>a a v s \<partial>measure_pmf p) = (\<Squnion>a\<in>A s. L\<^sub>a a v s)"
proof (intro antisym)
  show "(\<Squnion>pa\<in>{pa. set_pmf pa \<subseteq> A s}. measure_pmf.expectation pa (\<lambda>a. L\<^sub>a a v s))
    \<le> (\<Squnion>a\<in>A s. L\<^sub>a a v s)"
    using ex_dec is_dec_def integrable_L\<^sub>a A_ne L\<^sub>a_bounded
    by (fastforce intro: bounded_range_subset intro!: cSUP_least lemma_4_3_1)
  show "(\<Squnion>a\<in>A s. L\<^sub>a a v s) \<le> (\<Squnion>p\<in>{p. set_pmf p \<subseteq> A s}. \<integral>a. L\<^sub>a a v s \<partial>measure_pmf p)"
    unfolding SUP_step_MR_eq[symmetric] SUP_step_det_eq[symmetric] \<L>_def
    using ex_dec_det by (fastforce intro!: cSUP_mono)
qed

lemma \<L>_eq_SUP_det: "\<L> v s = (\<Squnion>d \<in> D\<^sub>D. L (mk_dec_det d) v s)"
  using SUP_step_MR_eq SUP_step_det_eq SUP_L\<^sub>a_eq_det by auto

lemma \<L>\<^sub>b_eq_SUP_det: "\<L>\<^sub>b v s = (\<Squnion>d \<in> D\<^sub>D. L (mk_dec_det d) v s)"
  using \<L>_eq_SUP_det unfolding \<L>\<^sub>b.rep_eq by auto


subsection \<open>Monotonicity\<close>

lemma \<P>\<^sub>X_mono[intro]: "a \<le> b \<Longrightarrow> \<P>\<^sub>X p n a \<le> \<P>\<^sub>X p n b"
  by (fastforce simp: \<P>\<^sub>X_def intro: integral_mono)

lemma \<P>\<^sub>1_mono[intro]: "a \<le> b \<Longrightarrow> \<P>\<^sub>1 p a \<le> \<P>\<^sub>1 p b"
  using \<P>\<^sub>1_nonneg by auto

lemma L_mono[intro]: "u \<le> v \<Longrightarrow> L d u \<le> L d v"
  unfolding L_def by (auto intro: scaleR_left_mono)

lemma \<L>\<^sub>b_mono[intro]: "u \<le> v \<Longrightarrow> \<L>\<^sub>b u \<le> \<L>\<^sub>b v"
  using  ex_dec L_mono[of u v] 
  by (fastforce intro!: cSUP_mono simp: \<L>\<^sub>b.rep_eq \<L>_def)

lemma step_mono:
  assumes "\<L>\<^sub>b v \<le> v" "d \<in> D\<^sub>R"
  shows "L d v \<le> v"
  using assms L_le_\<L>\<^sub>b order.trans by blast

lemma step_mono_elem_det:
  assumes "v \<le> \<L>\<^sub>b v" "e > 0"
  shows "\<exists>d\<in>D\<^sub>D. v \<le> L (mk_dec_det d) v + e *\<^sub>R 1"
proof -
  have "v s \<le> (\<Squnion>a\<in>A s. L\<^sub>a a v s)" for s
    using SUP_step_det_eq \<L>\<^sub>b_eq_SUP_det assms(1) by fastforce
  hence "\<exists>a\<in>A s. v s - e < L\<^sub>a a v s" for s
    using A_ne L\<^sub>a_le'
    by (subst less_cSUP_iff[symmetric]) (fastforce simp: assms add_strict_increasing algebra_simps intro!: bdd_above.I2)+
  hence aux: "\<exists>a\<in>A s. v s \<le> L\<^sub>a a v s + e" for s
    by (auto simp: diff_less_eq intro: less_imp_le)
  then obtain d where "is_dec_det d" "v s \<le> L (mk_dec_det d) v s + e" for s
    by (metis L_eq_L\<^sub>a_det is_dec_det_def)
  thus ?thesis
    by fastforce
qed

lemma step_mono_elem:
  assumes "v \<le> \<L>\<^sub>b v" "e > 0"
  shows "\<exists>d\<in>D\<^sub>R. v \<le> L d v + e *\<^sub>R 1"
  using assms step_mono_elem_det by blast

lemma \<P>\<^sub>X_L_le:
  assumes "\<L>\<^sub>b v \<le> v" "p \<in> \<Pi>\<^sub>M\<^sub>R"
  shows "\<P>\<^sub>X p n (L (p n) v) \<le> \<P>\<^sub>X p n v"
  using assms step_mono by auto

end

locale MDP_reward_disc = MDP_reward A K r l
  for
    A and 
    K :: "'s ::countable \<times> 'a ::countable \<Rightarrow> 's pmf" and
    r l +
  assumes
    disc_lt_one [simp]: "l < 1"
begin

definition "is_opt_act v s = is_arg_max (\<lambda>a. L\<^sub>a a v s) (\<lambda>a. a \<in> A s)"
abbreviation "opt_acts v s \<equiv> {a. is_opt_act v s a}"

lemma summable_disc [intro, simp]: "summable (\<lambda>i. l ^ i * x)"
  by (simp add: mult.commute)

lemma summable_r_disc[intro, simp]:
  "summable (\<lambda>i. \<bar>l ^ i * r (sa i)\<bar>)"
  "summable (\<lambda>i. l ^ i * \<bar>r (sa i)\<bar>)"
  "summable (\<lambda>i. l ^ i * r (sa i))"
proof -
  show "summable (\<lambda>i. \<bar>l ^ i * r (sa i)\<bar>)"
    using abs_r_le_r\<^sub>M
    by (fastforce intro!: mult_left_mono summable_comparison_test'[OF summable_disc])
  thus "summable (\<lambda>i. l ^ i * r (sa i))" "summable (\<lambda>i. l ^ i * \<bar>r (sa i)\<bar>)"
    by (auto intro: summable_rabs_cancel)
qed

lemma summable_norm_disc_I[intro]:
  assumes "summable (\<lambda>t. (l^t * norm F))"
  shows "summable (\<lambda>t. norm (l^t *\<^sub>R F))"
  using assms by auto

lemma summable_norm_disc_I'[intro]:
  assumes "summable (\<lambda>t. (l^t * norm (F t)))"
  shows "summable (\<lambda>t. norm (l^t *\<^sub>R F t))"
  using assms by auto

lemma summable_discI [intro]:
  assumes "bounded (range F)"
  shows "summable (\<lambda>t. l^t * norm (F t))"
proof -
  obtain b where "norm (F x) \<le> b" for x
    using assms by (auto simp: bounded_iff)
  thus ?thesis
    using Abel_lemma[of l 1 F b] by (auto simp: mult.commute)
qed

lemma summable_disc_reward [intro]:
  assumes "bounded (range (F :: nat \<Rightarrow> 'b :: banach))"
  shows "summable (\<lambda>t. l^t *\<^sub>R (F t))"
  using assms by (auto intro: summable_norm_cancel)

lemma summable_norm_bfun_disc: "summable (\<lambda>t. l^t * norm (apply_bfun f t))"
  using norm_le_norm_bfun
  by (auto simp: mult.commute[of "l^_"] intro!: Abel_lemma[of _ 1 _ "norm f"])

lemma summable_bfun_disc [simp]: "summable (\<lambda>t. l^t * (apply_bfun f t))"
proof -
  have "norm (l^t * apply_bfun f t) = l^t * norm (apply_bfun f t)" for t
    by (auto simp: abs_mult)
  hence "summable (\<lambda>t. norm (l^t * (apply_bfun f t)))"
    by (auto simp only: abs_mult)
  thus ?thesis
    by (auto intro: summable_norm_cancel)
qed

lemma norm_bfun_disc_le: "norm f \<le> B \<Longrightarrow> (\<Sum>x. l^x * norm (apply_bfun f x)) \<le> (\<Sum>x. l^x * B)"
  by (fastforce intro!: suminf_le mult_left_mono norm_le_norm_bfun intro: order.trans)

lemma norm_bfun_disc_le': "norm f \<le> B \<Longrightarrow> (\<Sum>x. l^x * (apply_bfun f x)) \<le> (\<Sum>x. l^x * B)"
  by (auto simp: mult_left_mono intro!: suminf_le order.trans[OF _ norm_bfun_disc_le])

lemma sum_disc_lim_l: "(\<Sum>x. l^x * B) = B /(1-l)"
  by (simp add: suminf_mult2[symmetric] summable_geometric suminf_geometric[of l])

lemma sum_disc_bound: "(\<Sum>x. l^x * apply_bfun f x) \<le> (norm f) /(1-l)"
  using norm_bfun_disc_le' sum_disc_lim  by auto

lemma sum_disc_bound':
  fixes f :: "nat \<Rightarrow> 'b \<Rightarrow>\<^sub>b real"
  assumes h: "\<forall>n. norm (f n) \<le> B"
  shows "norm (\<Sum>x. l^x *\<^sub>R f x) \<le> B /(1-l)"
proof -
  have "norm (\<Sum>x. l^x *\<^sub>R f x) \<le>  (\<Sum>x. norm (l^x *\<^sub>R f x))"
    using h
    by (fastforce intro!: boundedI summable_norm)
  also have "\<dots> \<le> (\<Sum>x. l^x * B)"
    using h
    by (auto intro!: suminf_le boundedI simp: mult_mono')
  also have "\<dots> = B /(1-l)"
    by (simp add: sum_disc_lim)
  finally show "norm (\<Sum>x. l^x *\<^sub>R f x) \<le> B /(1-l)" .
qed


lemma abs_\<nu>_trace_le: "\<bar>\<nu>_trace t\<bar> \<le> (\<Sum>i. l ^ i * r\<^sub>M)"
  by (auto intro!: abs_r_le_r\<^sub>M mult_left_mono order_trans[OF summable_rabs] suminf_le)

lemma integrable_\<nu>_trace: "integrable (\<T> p s) \<nu>_trace"
  by (fastforce simp: bounded_iff intro: abs_\<nu>_trace_le)

context 
  fixes p :: "('s, 'a) pol"
begin

lemma \<nu>_eq_\<nu>_trace: "\<nu> p s = \<integral>t. \<nu>_trace t \<partial>\<T> p s"
proof -
  have "(\<lambda>n. \<nu>_fin p n s) \<longlonglongrightarrow> \<integral>t. \<nu>_trace t \<partial>\<T> p s"
    unfolding \<nu>_fin_def
  proof(intro integral_dominated_convergence)
    show "AE x in \<T> p s. \<nu>_trace_fin x \<longlonglongrightarrow> \<nu>_trace x"
      using summable_LIMSEQ by blast
  next
    have "(\<Sum>i<N. l ^ i * r\<^sub>M) \<le> (\<Sum>N. l ^ N * r\<^sub>M)" for N
      by (auto intro: sum_le_suminf simp: r\<^sub>M_nonneg)
    thus "AE x in \<T> p s. norm (\<nu>_trace_fin x N) \<le> (\<Sum>N. l ^ N * r\<^sub>M)" for N
      using order_trans[OF abs_\<nu>_trace_fin_le] by fastforce
  qed auto
  thus ?thesis
    using \<nu>_eq_lim limI by fastforce
qed

lemma abs_\<nu>_le: "\<bar>\<nu> p s\<bar> \<le> (\<Sum>i. l^i * r\<^sub>M)"
  unfolding \<nu>_eq_Pn
  using abs_exp_r_le
  by (fastforce intro!: order.trans[OF summable_rabs] suminf_le summable_comparison_test'[OF summable_disc] mult_left_mono)

lemma \<nu>_le: "\<nu> p s \<le> (\<Sum>i. l^i * r\<^sub>M)"
  by (auto intro: abs_\<nu>_le abs_le_D1)

(* 6.1.2 in Puterman *)
lemma \<nu>_bfun: "\<nu> p \<in> bfun"
  by (auto intro!: abs_\<nu>_le)

lift_definition \<nu>\<^sub>b :: "'s \<Rightarrow>\<^sub>b real" is "\<nu> p"
  using \<nu>_bfun by blast

lemma norm_\<nu>_le: "norm \<nu>\<^sub>b \<le> r\<^sub>M / (1-l)"
  using abs_\<nu>_le sum_disc_lim
  by (auto simp: \<nu>\<^sub>b.rep_eq norm_bfun_def' intro: cSUP_least)
end

lemma \<nu>_as_markovian: "\<nu> (mk_markovian (as_markovian p (return_pmf s))) s = \<nu> p s"
  by (auto simp: \<nu>_eq_Pn Pn_as_markovian_eq Pn'_def)

lemma \<nu>\<^sub>b_as_markovian: "\<nu>\<^sub>b (mk_markovian (as_markovian p (return_pmf s))) s = \<nu>\<^sub>b p s"
  using \<nu>_as_markovian by (auto simp: \<nu>\<^sub>b.rep_eq)

subsection \<open>Optimal Reward\<close>

definition "\<nu>_MD s \<equiv> \<Squnion>p \<in> \<Pi>\<^sub>M\<^sub>D. \<nu> (mk_markovian_det p) s"
definition "\<nu>_opt s \<equiv> \<Squnion>p \<in> \<Pi>\<^sub>H\<^sub>R. \<nu> p s"

lemma \<nu>_opt_bfun: "\<nu>_opt \<in> bfun"
  using abs_\<nu>_le policies_ne 
  by (fastforce simp: \<nu>_opt_def intro!: order_trans[OF cSup_abs_le] bfun_normI)

lift_definition \<nu>\<^sub>b_opt :: "'s \<Rightarrow>\<^sub>b real" is \<nu>_opt
  using \<nu>_opt_bfun .

lemma \<nu>\<^sub>b_opt_eq: "\<nu>\<^sub>b_opt s = (\<Squnion>p \<in> \<Pi>\<^sub>H\<^sub>R. \<nu>\<^sub>b p s)"
  using \<nu>\<^sub>b.rep_eq \<nu>\<^sub>b_opt.rep_eq \<nu>_opt_def by presburger

lemma \<nu>_le_\<nu>_opt [intro]:
  assumes "is_policy p"
  shows "\<nu> p s \<le> \<nu>_opt s"
  unfolding \<nu>_opt_def using abs_\<nu>_le assms
  by (force intro: cSUP_upper intro!: bounded_imp_bdd_above boundedI)

lemma \<nu>\<^sub>b_le_opt [intro]: "p \<in> \<Pi>\<^sub>H\<^sub>R \<Longrightarrow> \<nu>\<^sub>b p \<le> \<nu>\<^sub>b_opt"
  using \<nu>_le by (fastforce simp: \<nu>\<^sub>b.rep_eq \<nu>\<^sub>b_opt.rep_eq)

lemma \<nu>\<^sub>b_le_opt_MD [intro]: "p \<in> \<Pi>\<^sub>M\<^sub>D \<Longrightarrow> \<nu>\<^sub>b (mk_markovian_det p) \<le> \<nu>\<^sub>b_opt"
  by (auto simp: mk_markovian_det_def is_dec_det_def is_dec_def is_policy_def)

lemma \<nu>\<^sub>b_le_opt_DD [intro]: "is_dec_det d \<Longrightarrow> \<nu>\<^sub>b (mk_stationary_det d) \<le> \<nu>\<^sub>b_opt"
  by (auto simp add: is_policy_def mk_markovian_def)

lemma \<nu>\<^sub>b_le_opt_DR [intro]: "is_dec d \<Longrightarrow> \<nu>\<^sub>b (mk_stationary d) \<le> \<nu>\<^sub>b_opt"
  by (auto simp add: is_policy_def mk_markovian_def)

lemma \<nu>\<^sub>b_opt_eq_MR: "\<nu>\<^sub>b_opt s = (\<Squnion>p \<in> \<Pi>\<^sub>M\<^sub>R. \<nu>\<^sub>b (mk_markovian p) s)"
proof (rule antisym)
  show "\<nu>\<^sub>b_opt s \<le> (\<Squnion>p\<in>\<Pi>\<^sub>M\<^sub>R. \<nu>\<^sub>b (mk_markovian p) s)"
    unfolding \<nu>\<^sub>b_opt_eq
  proof (rule cSUP_mono)
    show "\<Pi>\<^sub>H\<^sub>R \<noteq> {}"
      using policies_ne by simp
    show "bdd_above ((\<lambda>p. \<nu>\<^sub>b (mk_markovian p) s) ` \<Pi>\<^sub>M\<^sub>R)"
      by (auto intro!: boundedI bounded_imp_bdd_above abs_\<nu>_le simp: \<nu>\<^sub>b.rep_eq) 
    show "n \<in> \<Pi>\<^sub>H\<^sub>R \<Longrightarrow> \<exists>m\<in>\<Pi>\<^sub>M\<^sub>R. \<nu>\<^sub>b n s \<le> \<nu>\<^sub>b (mk_markovian m) s" for n
      using is_\<Pi>\<^sub>M\<^sub>R_as_markovian by (subst \<nu>\<^sub>b_as_markovian[symmetric]) fastforce     
  qed
  show "(\<Squnion>p\<in>\<Pi>\<^sub>M\<^sub>R. \<nu>\<^sub>b (mk_markovian p) s) \<le> \<nu>\<^sub>b_opt s"
    using \<Pi>\<^sub>M\<^sub>R_ne \<Pi>\<^sub>M\<^sub>R_imp_policies 
    by (auto intro!: cSUP_mono bounded_imp_bdd_above boundedI abs_\<nu>_le simp: \<nu>\<^sub>b_opt_eq  \<nu>\<^sub>b.rep_eq)
qed

lemma summable_norm_disc_reward'[simp]: "summable (\<lambda>t. l^t * norm (\<P>\<^sub>X p t (r_dec\<^sub>b (p t))))"
  using \<P>\<^sub>X_bounded_r by auto

lemma summable_disc_reward_\<P>\<^sub>X [simp]: "summable (\<lambda>t. l^t *\<^sub>R \<P>\<^sub>X p t (r_dec\<^sub>b (p t)))"
  using summable_disc_reward \<P>\<^sub>X_bounded_r by blast

lemma disc_reward_tendsto:
  "(\<lambda>n. \<Sum>t<n. l^t *\<^sub>R \<P>\<^sub>X p t (r_dec\<^sub>b (p t))) \<longlonglongrightarrow> (\<Sum>t. l^t *\<^sub>R \<P>\<^sub>X p t (r_dec\<^sub>b (p t)))"
  by (simp add: summable_LIMSEQ)

lemma \<nu>_eq_\<P>\<^sub>X: "\<nu> (mk_markovian p) = (\<Sum>i. l^i *\<^sub>R \<P>\<^sub>X p i (r_dec\<^sub>b (p i)))"
proof -
  have "\<nu> (mk_markovian p) s = (\<Sum>i. l^i * \<P>\<^sub>X p i (r_dec\<^sub>b (p i)) s)" for s
    unfolding \<nu>\<^sub>b.rep_eq \<P>\<^sub>X_def \<nu>_eq_Pn Pn'_markovian_eq_Xn'_bind measure_pmf_bind
    using measure_pmf_in_subprob_algebra abs_r_le_r\<^sub>M
    by (subst integral_bind) (auto simp: r_dec_eq_r_K0)
  thus ?thesis
    by (auto simp: suminf_apply_bfun)
qed

lemma \<nu>\<^sub>b_eq_\<P>\<^sub>X: "\<nu>\<^sub>b (mk_markovian p) = (\<Sum>i. l^i *\<^sub>R \<P>\<^sub>X p i (r_dec\<^sub>b (p i)))"
  by (auto simp: \<nu>_eq_\<P>\<^sub>X \<nu>\<^sub>b.rep_eq)

lemma \<nu>\<^sub>b_fin_tendsto_\<nu>\<^sub>b: "(\<nu>\<^sub>b_fin (mk_markovian p)) \<longlonglongrightarrow> \<nu>\<^sub>b (mk_markovian p)"
  using disc_reward_tendsto \<nu>\<^sub>b_eq_\<P>\<^sub>X \<nu>\<^sub>b_fin_eq_\<P>\<^sub>X
  by presburger

lemma norm_\<P>\<^sub>1_l_less: "norm (l *\<^sub>R \<P>\<^sub>1 d) < 1"
  by auto
lemma disc_\<P>\<^sub>1_tendsto: "(\<lambda>n. (\<Sum>t\<le>n. l^t *\<^sub>R \<P>\<^sub>1 d ^^t)) \<longlonglongrightarrow> (\<Sum>t. l^t *\<^sub>R \<P>\<^sub>1 d ^^t)"
  by (fastforce simp: bounded_iff intro: summable_LIMSEQ')

lemma disc_\<P>\<^sub>1_lim: "lim (\<lambda>n. (\<Sum>t\<le>n. l^t *\<^sub>R \<P>\<^sub>1 d ^^ t)) = (\<Sum>t. l^t *\<^sub>R \<P>\<^sub>1 d ^^t)"
  using limI disc_\<P>\<^sub>1_tendsto
  by blast

lemma convergent_disc_\<P>\<^sub>1: "convergent (\<lambda>n. (\<Sum>t\<le>n. l^t *\<^sub>R \<P>\<^sub>1 d ^^t))"
  using convergentI disc_\<P>\<^sub>1_tendsto 
  by blast

lemma \<P>\<^sub>1_suminf_ge: 
  assumes "0 \<le> u" shows "u \<le> (\<Sum>t. l^t *\<^sub>R \<P>\<^sub>1 d ^^t) u"
proof -
  have aux: "\<And>x. (\<lambda>n. (\<Sum>t\<le>n. l^t *\<^sub>R \<P>\<^sub>1 d ^^t) u x) \<longlonglongrightarrow> (\<Sum>t. l^t *\<^sub>R \<P>\<^sub>1 d ^^t) u x"
    using bfun_tendsto_apply_bfun disc_\<P>\<^sub>1_lim lim_blinfun_apply[OF convergent_disc_\<P>\<^sub>1] 
    by fastforce
  have "\<And>n. u \<le> (\<Sum>t\<le>n. l^t *\<^sub>R \<P>\<^sub>1 d ^^t) u"
    using \<P>\<^sub>1_sum_ge[OF assms] by auto
  thus ?thesis
    by (auto intro!: LIMSEQ_le_const[OF aux])
qed

lemma \<P>\<^sub>1_suminf_pos: 
  assumes "0 \<le> u" 
  shows "0 \<le> (\<Sum>t. l^t *\<^sub>R \<P>\<^sub>1 d ^^t) u"
  using \<P>\<^sub>1_suminf_ge[of u] assms order.trans by auto

lemma lemma_6_1_2_b:
  assumes "v \<le> u"
  shows "(\<Sum>t. l^t *\<^sub>R \<P>\<^sub>1 d ^^t) v \<le> (\<Sum>t. l^t *\<^sub>R \<P>\<^sub>1 d ^^t) u"
proof -
  have "0 \<le> (\<Sum>n. l ^ n *\<^sub>R \<P>\<^sub>1 d ^^ n) (u - v)"
    using \<P>\<^sub>1_suminf_pos assms by simp
  thus ?thesis
    by (simp add: blinfun.diff_right)
qed

lemma \<nu>_stationary: "\<nu>\<^sub>b (mk_stationary d) = (\<Sum>t. l^t *\<^sub>R (\<P>\<^sub>1 d ^^ t)) (r_dec\<^sub>b d)"
proof -
  have "\<nu>\<^sub>b (mk_stationary d) = (\<Sum>t. (l ^ t *\<^sub>R (\<P>\<^sub>1 d ^^ t)) (r_dec\<^sub>b d))"
    by (simp add: \<nu>\<^sub>b_eq_\<P>\<^sub>X scaleR_blinfun.rep_eq \<P>\<^sub>X_sconst)
  also have "...  = (\<Sum>t. (l ^ t *\<^sub>R (\<P>\<^sub>1 d ^^ t))) (r_dec\<^sub>b d)"
    by (subst bounded_linear.suminf[where f = "\<lambda>x. blinfun_apply x (r_dec\<^sub>b d)"]) 
      (auto intro!: bounded_linear.suminf boundedI)
  finally show ?thesis .
qed

lemma \<nu>_stationary_inv: "\<nu>\<^sub>b (mk_stationary d) = inv\<^sub>L (id_blinfun - l *\<^sub>R \<P>\<^sub>1 d) (r_dec\<^sub>b d)"
  by (auto simp: \<nu>_stationary inv\<^sub>L_inf_sum blincomp_scaleR_right)


text \<open>The value of a markovian policy can be expressed in terms of @{const L}.\<close>

lemma \<nu>_step: "\<nu>\<^sub>b (mk_markovian p) = L (p 0) (\<nu>\<^sub>b (mk_markovian (\<lambda>n. p (Suc n))))"
proof -
  have s: "summable (\<lambda>t. l^t *\<^sub>R (\<P>\<^sub>X p (Suc t) (r_dec\<^sub>b (p (Suc t)))))"
    using \<P>\<^sub>X_bound_r by (auto intro!: boundedI[of _ r\<^sub>M])
  have 
    "\<nu>\<^sub>b (mk_markovian p) = r_dec\<^sub>b (p 0) + (\<Sum>t. l ^ (Suc t) *\<^sub>R \<P>\<^sub>X p (Suc t) (r_dec\<^sub>b (p (Suc t))))"
    by (subst suminf_split_head) (auto simp: \<nu>\<^sub>b_eq_\<P>\<^sub>X)
  also have 
    "\<dots> = r_dec\<^sub>b (p 0) + l *\<^sub>R (\<Sum>t. \<P>\<^sub>1 (p 0) (l^t *\<^sub>R \<P>\<^sub>X (\<lambda>n. p (Suc n)) t (r_dec\<^sub>b (p (Suc t)))))"
    using suminf_scaleR_right[OF s] by (auto simp: \<P>\<^sub>X_Suc blinfun.scaleR_right)
  also have 
    "\<dots> = L (p 0) (\<nu>\<^sub>b (mk_markovian (\<lambda>n. p (Suc n))))"
    using blinfun.bounded_linear_right bounded_linear.suminf[of "blinfun_apply (\<P>\<^sub>1 (p 0))"]
    by (fastforce simp add: \<nu>\<^sub>b_eq_\<P>\<^sub>X L_def)
  finally show ?thesis .
qed

lemma L_\<nu>_fix: "\<nu>\<^sub>b (mk_stationary d) = L d (\<nu>\<^sub>b (mk_stationary d))"
  using \<nu>_step .

lemma L_fix_\<nu>:
  assumes "L p v = v"
  shows "v = \<nu>\<^sub>b (mk_stationary p)"
proof -
  have "r_dec\<^sub>b p = (id_blinfun - l *\<^sub>R \<P>\<^sub>1 p) v"
    using assms by (auto simp: eq_diff_eq L_def blinfun.diff_left blinfun.scaleR_left)
  hence "v = (\<Sum>t. (l *\<^sub>R \<P>\<^sub>1 p)^^t) (r_dec\<^sub>b p)"
    using inv_norm_le'(2)[OF norm_\<P>\<^sub>1_l_less] by auto
  thus "v = \<nu>\<^sub>b (mk_stationary p)"
    by (auto simp: \<nu>_stationary blincomp_scaleR_right)
qed

lemma L_\<nu>_fix_iff: "L d v = v \<longleftrightarrow> v = \<nu>\<^sub>b (mk_stationary d)"
  using L_fix_\<nu> L_\<nu>_fix by auto

subsection \<open>Properties of Solutions of the Optimality Equations\<close>

abbreviation "\<P>\<^sub>d p n v \<equiv> l^n *\<^sub>R \<P>\<^sub>X p n v"

lemma \<P>\<^sub>d_lim: "(\<lambda>n. (\<P>\<^sub>d p n v)) \<longlonglongrightarrow> 0"
proof -
  have "(\<lambda>n. l^n * norm v) \<longlonglongrightarrow> 0"
    by (auto intro!: tendsto_eq_intros)
  moreover have "norm (\<P>\<^sub>d p n v) \<le> l^n * norm v" for p n
    by (simp add: mult_mono')
  ultimately have "(\<lambda>n. norm (\<P>\<^sub>d p n v)) \<longlonglongrightarrow> 0" for p
    by (auto simp: Lim_transform_bound[where g = "\<lambda>n. (l^n * norm v)"])
  thus "(\<lambda>n. (\<P>\<^sub>d p n v)) \<longlonglongrightarrow> 0" for p
    using tendsto_norm_zero_cancel by fast
qed



(* 6.2.2 a) in Puterman *)

lemma \<L>_dec_ge_opt:
  assumes "\<L>\<^sub>b v \<le> v"
  shows "\<nu>\<^sub>b_opt \<le> v"
proof -
  have "\<nu>\<^sub>b (mk_markovian p) \<le> v" if "p \<in> \<Pi>\<^sub>M\<^sub>R" for p
  proof -
    let ?p = "mk_markovian p"
    have aux: "\<nu>\<^sub>b_fin ?p n + l^n *\<^sub>R \<P>\<^sub>X p n v \<le> v" for n
    proof (induction n)
      case (Suc n)
      have "\<P>\<^sub>X p n (r_dec\<^sub>b (p n)) + l *\<^sub>R (\<P>\<^sub>X p (Suc n) v) \<le> \<P>\<^sub>X p n v"
        using \<P>\<^sub>X_L_le assms that by (simp add: \<P>\<^sub>X_Suc_n_elem L_def linear_simps)
      hence "\<nu>\<^sub>b_fin ?p (n + 1) + l^(n + 1) *\<^sub>R (\<P>\<^sub>X p (n + 1) v) \<le> \<nu>\<^sub>b_fin ?p n + l^n *\<^sub>R (\<P>\<^sub>X p n v)"
        by (auto simp del: scaleR_scaleR intro: scaleR_left_mono simp: \<nu>\<^sub>b_fin_eq_\<P>\<^sub>X 
            mult.commute[of l] scaleR_add_right[symmetric] scaleR_scaleR[symmetric])
      also have "\<dots> \<le> v"
        using Suc.IH by (auto simp: \<nu>\<^sub>b_fin_eq_\<P>\<^sub>X)
      finally show ?case
        by auto
    qed (auto simp: \<nu>\<^sub>b_fin_eq_\<P>\<^sub>X)
    have 1: "(\<lambda>n. (\<nu>\<^sub>b_fin ?p n + \<P>\<^sub>d p n v) s) \<longlonglongrightarrow> \<nu>\<^sub>b ?p s" for s
      using bfun_tendsto_apply_bfun Limits.tendsto_add[OF \<nu>\<^sub>b_fin_tendsto_\<nu>\<^sub>b \<P>\<^sub>d_lim] by fastforce
    have "\<nu>\<^sub>b ?p s \<le> v s" for s
      using that aux assms by (fastforce intro!: lim_mono[OF _ 1, of  _ _ "\<lambda>n. v s"])
    thus ?thesis
      using that by blast
  qed
  thus ?thesis
    using policies_ne by (fastforce simp: is_policy_def \<nu>\<^sub>b_opt_eq_MR intro!: cSUP_least)
qed

lemma \<L>_inc_le_opt:
  assumes "v \<le> \<L>\<^sub>b v"
  shows "v \<le> \<nu>\<^sub>b_opt"
proof -
  have le_elem: "v s \<le> \<nu>\<^sub>b_opt s + (e/(1-l))" if "e > 0" for s e
  proof -
    obtain d where "d \<in> D\<^sub>R" and hd: "v \<le> L d v + e *\<^sub>R 1"
      using assms step_mono_elem \<open>e > 0\<close> by blast
    let ?Pinf = "(\<Sum>i. l^i *\<^sub>R \<P>\<^sub>1 d^^i)"
    have "v \<le> r_dec\<^sub>b d + l *\<^sub>R (\<P>\<^sub>1 d) v + e *\<^sub>R 1"
      using hd L_def by fastforce
    hence "(id_blinfun - l *\<^sub>R \<P>\<^sub>1 d) v \<le> r_dec\<^sub>b d + e *\<^sub>R 1"
      by (auto simp: blinfun.diff_left blinfun.scaleR_left algebra_simps)
    hence "?Pinf ((id_blinfun - l *\<^sub>R \<P>\<^sub>1 d) v) \<le> ?Pinf (r_dec\<^sub>b d + e *\<^sub>R 1)"
      using lemma_6_1_2_b \<P>\<^sub>1_def hd by auto
    hence "v \<le> ?Pinf (r_dec\<^sub>b d + e *\<^sub>R 1)"
      using inv_norm_le'(2)[of "l *\<^sub>R \<P>\<^sub>1 d"] by (auto simp: blincomp_scaleR_right)
    also have "\<dots> = \<nu>\<^sub>b (mk_stationary d) + e *\<^sub>R ?Pinf 1"
      by (simp add: \<nu>_stationary blinfun.add_right blinfun.scaleR_right)
    also have "\<dots> = \<nu>\<^sub>b (mk_stationary d) + e *\<^sub>R (\<Sum>i. (l^i *\<^sub>R ((\<P>\<^sub>1 d^^i))) 1)"
      using convergent_disc_\<P>\<^sub>1 
      by (auto simp: summable_iff_convergent' bounded_linear.suminf[of "\<lambda>x. blinfun_apply x 1"])
    also have "\<dots> = \<nu>\<^sub>b (mk_stationary d) + e *\<^sub>R (\<Sum>i. (l^i *\<^sub>R 1))"
      by (auto simp: scaleR_blinfun.rep_eq)
    also have "\<dots> \<le> (\<nu>\<^sub>b (mk_stationary d) + (e / (1-l)) *\<^sub>R  1)"
      by (auto simp: bounded_linear.suminf[symmetric, where f = "\<lambda>x. x *\<^sub>R 1"] 
          suminf_geometric bounded_linear_scaleR_left summable_geometric)
    finally have "v s \<le> (\<nu>\<^sub>b (mk_stationary d) + (e/(1-l)) *\<^sub>R  1) s"
      by auto
    thus "v s \<le> \<nu>\<^sub>b_opt s + (e/(1-l))"
      using \<open>d \<in> D\<^sub>R\<close> \<nu>\<^sub>b_le_opt
      by (auto simp: is_policy_def mk_markovian_def less_eq_bfun_def intro: order_trans)
  qed
  have "v s \<le> \<nu>\<^sub>b_opt s + e" if "e > 0" for s e
  proof -
    have "e * (1 - l) > 0"
      by (simp add: \<open>0 < e\<close>)
    thus "v s \<le> \<nu>\<^sub>b_opt s + e"
      using disc_lt_one that le_elem by (fastforce split: if_splits)
  qed
  thus ?thesis
    by (fastforce intro: field_le_epsilon)
qed    
lemma \<L>_fix_imp_opt:
  assumes "v = \<L>\<^sub>b v"
  shows "v = \<nu>\<^sub>b_opt"
  using assms dual_order.antisym[OF \<L>_dec_ge_opt \<L>_inc_le_opt] by auto

lemma bounded_P: "bounded (\<P>\<^sub>1 ` X)"
  by (auto simp: bounded_iff)

subsection \<open>Solutions to the Optimality Equation\<close>
subsubsection \<open>@{const \<L>\<^sub>b} and @{const L} are Contraction Mappings\<close>
declare bounded_apply_blinfun[intro] bounded_apply_bfun'[intro]

lemma contraction_\<L>: "dist (\<L>\<^sub>b v) (\<L>\<^sub>b u) \<le> l * dist v u"
proof -
  have "dist (\<L>\<^sub>b v s) (\<L>\<^sub>b u s) \<le> l * dist v u" if "\<L>\<^sub>b u s \<le> \<L>\<^sub>b v s" for s v u
  proof -
    have "dist (\<L>\<^sub>b v s) (\<L>\<^sub>b u s) \<le> (\<Squnion>d \<in> D\<^sub>R. L d v s - L d u s)"
      using ex_dec that by (fastforce intro!: le_SUP_diff' simp: dist_real_def \<L>\<^sub>b.rep_eq \<L>_def)
    also have "\<dots> = (\<Squnion>d \<in> D\<^sub>R. l * (\<P>\<^sub>1 d (v - u) s))"
      by (auto simp: L_def right_diff_distrib blinfun.diff_right)
    also have "\<dots> = l * (\<Squnion>d \<in> D\<^sub>R. \<P>\<^sub>1 d (v - u) s)"
      using D\<^sub>R_ne bounded_P by (fastforce intro: bounded_SUP_mul)
    also have "\<dots> \<le> l * norm (\<Squnion>d \<in> D\<^sub>R. \<P>\<^sub>1 d (v - u) s)"
      by (simp add: mult_left_mono)
    also have "\<dots> \<le> l * (\<Squnion>d \<in> D\<^sub>R. norm ((\<P>\<^sub>1 d (v - u)) s))"
    proof -
      have "bounded ((\<lambda>x. norm ((\<P>\<^sub>1 x (v - u)) s)) ` D\<^sub>R)"
        using bounded_apply_bfun' bounded_P bounded_apply_blinfun bounded_norm_comp by metis
      thus ?thesis
        using D\<^sub>R_ne ex_dec bounded_norm_comp by (fastforce intro!: mult_left_mono)
    qed
    also have "\<dots> \<le> l * (\<Squnion>p \<in> D\<^sub>R. norm (\<P>\<^sub>1 p ((v - u))))"
      using D\<^sub>R_ne abs_le_norm_bfun bounded_P
      by (fastforce simp: bounded_norm_comp intro!: bounded_imp_bdd_above mult_left_mono cSUP_mono)
    also have "\<dots> \<le> l * (\<Squnion>p \<in> D\<^sub>R. norm ((v - u)))"
      using norm_push_exp_le_norm D\<^sub>R_ne
      by (fastforce simp: \<P>\<^sub>1.rep_eq intro!: mult_left_mono cSUP_mono)
    also have "\<dots> = l * dist v u"
      by (auto simp: dist_norm)
    finally show ?thesis .
  qed
  hence "\<L>\<^sub>b u s \<le> \<L>\<^sub>b v s \<Longrightarrow> dist (\<L>\<^sub>b v s) (\<L>\<^sub>b u s) \<le> l * dist v u" 
    "\<L>\<^sub>b v s \<le> \<L>\<^sub>b u s \<Longrightarrow> dist (\<L>\<^sub>b v s) (\<L>\<^sub>b u s) \<le> l * dist v u" for u v s
    by (fastforce simp: dist_commute)+
  thus ?thesis
    using linear[of "\<L>\<^sub>b u _"] by (fastforce intro: dist_bound)
qed

lemma is_contraction_\<L>: "is_contraction \<L>\<^sub>b"
  using contraction_\<L> zero_le_disc disc_lt_one unfolding is_contraction_def by blast

lemma contraction_L: "dist (L p v) (L p u) \<le> l * dist v u"
proof -
  have aux: "L p v s - L p u s \<le> l * dist v u" if lea: "L p v s \<ge> L p u s" for v s u
  proof -
    have "L p v s - L p u s = (l *\<^sub>R  (\<P>\<^sub>1 p v - \<P>\<^sub>1 p u)) s"
      by (simp add: L_def scale_right_diff_distrib)
    also have "\<dots> \<le> l * norm (\<P>\<^sub>1 p (v - u) s)"
      by (auto simp: blinfun.diff_right intro!: mult_left_mono)
    also have "\<dots> \<le> l * norm (\<P>\<^sub>1 p (v - u))"
      using abs_le_norm_bfun by (auto intro!: mult_left_mono)
    also have "\<dots> \<le> l * dist v u"
      by (simp add: \<P>\<^sub>1.rep_eq mult_left_mono norm_push_exp_le_norm dist_norm)
    finally show ?thesis
      by auto
  qed
  have "dist (L p v s) (L p u s) \<le> l * dist v u" for v s u
    using aux[of v _ u] aux[of u _ v]
    by (cases "L p v s \<ge> L p u s") (auto simp: dist_real_def dist_commute)
  thus "dist (L p v) (L p u) \<le> l * dist v u"
    by (simp add: dist_bound)
qed

lemma is_contraction_L: "is_contraction (L p)"
  unfolding is_contraction_def using contraction_L disc_lt_one zero_le_disc by blast

subsubsection \<open>Existence of a Fixpoint of @{const \<L>\<^sub>b}\<close>
lemma \<L>\<^sub>b_conv:
  "\<exists>!v. \<L>\<^sub>b v = v" "(\<lambda>n. (\<L>\<^sub>b ^^ n) v) \<longlonglongrightarrow> (THE v. \<L>\<^sub>b v = v)"
  using banach'[OF is_contraction_\<L>] by auto

lemma \<L>\<^sub>b_fix_iff_opt [simp]: "\<L>\<^sub>b v = v \<longleftrightarrow> v = \<nu>\<^sub>b_opt"
  using banach'(1) is_contraction_\<L> \<L>_fix_imp_opt by metis

lemma \<nu>\<^sub>b_opt_fix: "\<nu>\<^sub>b_opt = (THE v. \<L>\<^sub>b v = v)"
  by auto

lemma \<L>\<^sub>b_opt [simp]: "\<L>\<^sub>b \<nu>\<^sub>b_opt = \<nu>\<^sub>b_opt"
  by auto

lemma \<L>\<^sub>b_lim: "(\<lambda>n. (\<L>\<^sub>b ^^ n) v) \<longlonglongrightarrow> \<nu>\<^sub>b_opt"
  using \<L>\<^sub>b_conv(2) \<nu>\<^sub>b_opt_fix by presburger

lemma thm_6_2_6: "\<nu>\<^sub>b p = \<nu>\<^sub>b_opt \<longleftrightarrow> \<L>\<^sub>b (\<nu>\<^sub>b p) = \<nu>\<^sub>b p"
  by force

lemma thm_6_2_6': "\<nu> p = \<nu>_opt \<longleftrightarrow> \<L>\<^sub>b (\<nu>\<^sub>b p) = \<nu>\<^sub>b p"
  using thm_6_2_6 \<nu>\<^sub>b.rep_eq \<nu>\<^sub>b_opt.rep_eq by fastforce

subsection \<open>Existence of Optimal Policies\<close>

definition "\<nu>_improving v d \<longleftrightarrow> (\<forall>s. is_arg_max (\<lambda>d. (L d v) s) (\<lambda>d. d \<in> D\<^sub>R) d)"

lemma \<nu>_improving_iff: "\<nu>_improving v d \<longleftrightarrow> d \<in> D\<^sub>R \<and> (\<forall>d' \<in> D\<^sub>R. \<forall>s. L d' v s \<le> L d v s)"
  by (auto simp: \<nu>_improving_def is_arg_max_linorder)

lemma \<nu>_improving_D_MR[dest]: "\<nu>_improving v d \<Longrightarrow> d \<in> D\<^sub>R"
  by (auto simp add: \<nu>_improving_iff)

lemma \<nu>_improving_ge: "\<nu>_improving v d \<Longrightarrow> d' \<in> D\<^sub>R \<Longrightarrow> L d' v s \<le> L d v s"
  by (auto simp: \<nu>_improving_iff)

lemma \<nu>_improving_imp_\<L>\<^sub>b: "\<nu>_improving v d \<Longrightarrow> \<L>\<^sub>b v = L d v"
  by (fastforce intro!: cSup_eq_maximum simp: \<nu>_improving_iff \<L>\<^sub>b.rep_eq \<L>_def)

lemma \<L>\<^sub>b_imp_\<nu>_improving: 
  assumes "d \<in> D\<^sub>R" "\<L>\<^sub>b v = L d v"
  shows "\<nu>_improving v d"
  using assms L_le_\<L>\<^sub>b by (auto simp: \<nu>_improving_iff assms(2)[symmetric])

lemma \<nu>_improving_alt:
  assumes "d \<in> D\<^sub>R"
  shows "\<nu>_improving v d \<longleftrightarrow> \<L>\<^sub>b v = L d v"
  using \<L>\<^sub>b_imp_\<nu>_improving \<nu>_improving_imp_\<L>\<^sub>b assms by blast

definition "\<nu>_conserving d = \<nu>_improving (\<nu>\<^sub>b_opt) d"

lemma \<nu>_conserving_iff: "\<nu>_conserving d \<longleftrightarrow> d \<in> D\<^sub>R \<and> (\<forall>d' \<in> D\<^sub>R. \<forall>s. L d' \<nu>\<^sub>b_opt s \<le> L d \<nu>\<^sub>b_opt s)"
  by (auto simp: \<nu>_conserving_def \<nu>_improving_iff)

lemma \<nu>_conserving_ge: "\<nu>_conserving d \<Longrightarrow> d' \<in> D\<^sub>R \<Longrightarrow> L d' \<nu>\<^sub>b_opt s \<le> L d \<nu>\<^sub>b_opt s"
  by (auto simp: \<nu>_conserving_iff intro: \<nu>_improving_ge)

lemma \<nu>_conserving_imp_\<L>\<^sub>b [simp]: "\<nu>_conserving d \<Longrightarrow> L d \<nu>\<^sub>b_opt = \<nu>\<^sub>b_opt"
  using \<nu>_improving_imp_\<L>\<^sub>b by (fastforce simp: \<nu>_conserving_def)

lemma \<L>\<^sub>b_imp_\<nu>_conserving:
  assumes "d \<in> D\<^sub>R" "\<L>\<^sub>b \<nu>\<^sub>b_opt = L d \<nu>\<^sub>b_opt"
  shows "\<nu>_conserving d"
  using \<L>\<^sub>b_imp_\<nu>_improving assms by (auto simp: \<nu>_conserving_def)

lemma \<nu>_conserving_alt: 
  assumes "d \<in> D\<^sub>R"
  shows "\<nu>_conserving d \<longleftrightarrow> \<L>\<^sub>b \<nu>\<^sub>b_opt = L d \<nu>\<^sub>b_opt"
  unfolding \<nu>_conserving_def using \<nu>_improving_alt assms by auto

lemma \<nu>_conserving_alt':
  assumes "d \<in> D\<^sub>R"
  shows "\<nu>_conserving d \<longleftrightarrow> L d \<nu>\<^sub>b_opt = \<nu>\<^sub>b_opt"
  using assms \<nu>_conserving_alt by auto

subsubsection \<open>Conserving Decision Rules are Optimal\<close>

theorem ex_improving_imp_conserving:
  assumes "\<And>v. \<exists>d. \<nu>_improving v (mk_dec_det d)"
  shows "\<exists>d. \<nu>_conserving (mk_dec_det d)"
  by (simp add: assms \<nu>_conserving_def)

theorem conserving_imp_opt[simp]:
  assumes "\<nu>_conserving (mk_dec_det d)"
  shows "\<nu>\<^sub>b (mk_stationary_det d) = \<nu>\<^sub>b_opt"
  using L_\<nu>_fix_iff \<nu>_conserving_imp_\<L>\<^sub>b[OF assms] by simp

lemma conserving_imp_opt':
  assumes "\<exists>d. \<nu>_conserving (mk_dec_det d)"
  shows "\<exists>d \<in> D\<^sub>D. (\<nu>\<^sub>b (mk_stationary_det d)) = \<nu>\<^sub>b_opt"
  using assms by (fastforce simp: \<nu>_conserving_def)

theorem improving_att_imp_det_opt:
  assumes "\<And>v. \<exists>d. \<nu>_improving v (mk_dec_det d)"
  shows "\<nu>\<^sub>b_opt s = (\<Squnion>d \<in> D\<^sub>D. \<nu>\<^sub>b (mk_stationary_det d) s)"
proof -
  obtain d where d: "\<nu>_conserving (mk_dec_det d)"
    using assms ex_improving_imp_conserving by auto
  hence "d \<in> D\<^sub>D"
    using \<nu>_conserving_iff is_dec_mk_dec_det_iff by blast
  thus ?thesis
    using \<Pi>\<^sub>M\<^sub>R_imp_policies \<nu>\<^sub>b_le_opt
    by (fastforce intro!: cSup_eq_maximum[where z = "\<nu>\<^sub>b_opt s", symmetric]
        simp: conserving_imp_opt[OF d] image_iff)
qed


lemma \<L>\<^sub>b_sup_att_dec:
  assumes "d \<in> D\<^sub>R" "\<L>\<^sub>b v = L d v"
  shows "\<exists>d' \<in> D\<^sub>D. \<L>\<^sub>b v = L (mk_dec_det d') v"
proof -
  have "\<exists>a\<in> A s. L d v s = L\<^sub>a a v s" for s
    unfolding L_eq_L\<^sub>a
    using assms is_dec_def L\<^sub>a_bounded A_ne \<L>\<^sub>b.rep_eq \<L>_def
    by (intro lemma_4_3_1') 
      (auto intro: bounded_range_subset simp: assms(2)[symmetric] L_eq_L\<^sub>a[symmetric] SUP_step_MR_eq)
  then obtain d' where d: "d' s \<in> A s" "L d v s = L\<^sub>a (d' s) v s" for s
    by metis
  thus ?thesis
    using assms d
    by (fastforce simp: is_dec_det_def mk_dec_det_def L_eq_L\<^sub>a)
qed

lemma \<L>\<^sub>b_sup_att_dec':
  assumes "d \<in> D\<^sub>R" "\<L>\<^sub>b v = L d v"
  shows "\<exists>d' \<in> D\<^sub>D. \<nu>_improving v (mk_dec_det d')"
  using \<L>\<^sub>b_sup_att_dec \<nu>_improving_alt assms by force

subsubsection \<open>Deterministic Decision Rules are Optimal\<close>

lemma opt_imp_opt_dec_det:
  assumes "p \<in> \<Pi>\<^sub>H\<^sub>R" "\<nu>\<^sub>b p = \<nu>\<^sub>b_opt" 
  shows "\<exists>d \<in> D\<^sub>D. \<nu>\<^sub>b (mk_stationary_det d) = \<nu>\<^sub>b_opt"
proof -
  have aux: "L (as_markovian p (return_pmf s) 0) \<nu>\<^sub>b_opt s = \<nu>\<^sub>b_opt s" for s
  proof -
    let ?ps = "as_markovian p (return_pmf s)"
    have markovian_suc_le: "\<nu>\<^sub>b (mk_markovian (\<lambda>n. as_markovian p (return_pmf s) (Suc n))) \<le> \<nu>\<^sub>b_opt"
      using is_\<Pi>\<^sub>M\<^sub>R_as_markovian assms by (auto simp: is_policy_def mk_markovian_def)
    have aux_le: "\<And>x f g. f \<le> g \<Longrightarrow> apply_bfun f x \<le> apply_bfun g x"
      unfolding less_eq_bfun_def by auto
    have "\<nu>\<^sub>b_opt s = \<nu>\<^sub>b (mk_markovian ?ps) s"
      using assms \<nu>\<^sub>b_as_markovian by metis
    also have "\<dots> = L (?ps 0) (\<nu>\<^sub>b (mk_markovian (\<lambda>n. ?ps (Suc n)))) s"
      using \<nu>_step by blast
    also have "\<dots> \<le> L (?ps 0) (\<nu>\<^sub>b_opt) s"
      unfolding L_def using markovian_suc_le \<P>\<^sub>1_mono by (auto intro!: mult_left_mono)
    finally have "\<nu>\<^sub>b_opt s \<le> L (?ps 0) (\<nu>\<^sub>b_opt) s" .
    have "as_markovian p (return_pmf s) 0 \<in> D\<^sub>R"
      using is_\<Pi>\<^sub>M\<^sub>R_as_markovian assms by fast
    have "L (?ps 0) \<nu>\<^sub>b_opt \<le> \<nu>\<^sub>b_opt"
      using \<open>?ps 0 \<in> D\<^sub>R\<close> L_le_\<L>\<^sub>b[of "?ps 0" "\<nu>\<^sub>b_opt"] by simp
    thus "L (?ps 0) \<nu>\<^sub>b_opt s = \<nu>\<^sub>b_opt s"
      using \<open>\<nu>\<^sub>b_opt s \<le> (L (?ps 0) \<nu>\<^sub>b_opt) s\<close> by (auto intro!: antisym)
  qed
  have "L (p []) v s = L (as_markovian p (return_pmf s) 0) v s" for v s
    by (auto simp: L_def \<P>\<^sub>1.rep_eq K_st_def)
  hence "L (p []) \<nu>\<^sub>b_opt = \<nu>\<^sub>b_opt"
    using aux by auto
  hence "\<exists>d \<in> D\<^sub>D. L (mk_dec_det d) \<nu>\<^sub>b_opt = \<nu>\<^sub>b_opt"
    using \<L>\<^sub>b_sup_att_dec assms(1) \<L>\<^sub>b_opt is_policy_def mem_Collect_eq by metis
  thus ?thesis
    using conserving_imp_opt' \<nu>_conserving_alt' by blast
qed

subsubsection \<open>Optimal Decision Rules for Finite Action Spaces\<close>

(* 6.2.10 *)
lemma ex_opt_act: 
assumes "\<And>s. finite (A s)"
shows "\<exists>a \<in> A s. L\<^sub>a a (v :: _ \<Rightarrow>\<^sub>b _) s = \<L>\<^sub>b v s"
      unfolding \<L>\<^sub>b.rep_eq \<L>_eq_SUP_det SUP_step_det_eq
      using arg_max_on_in[OF assms A_ne]
      by (auto simp: cSup_eq_Sup_fin Sup_fin_Max assms A_ne finite_arg_max_eq_Max[symmetric])

lemma ex_opt_dec_det:
assumes "\<And>s. finite (A s)"
shows "\<exists>d \<in> D\<^sub>D. L (mk_dec_det d) (v :: _ \<Rightarrow>\<^sub>b _) = \<L>\<^sub>b v"
  unfolding is_dec_det_def mk_dec_det_def
  using ex_opt_act[OF assms]  someI_ex
  apply (auto intro!: exI[of _ \<open>\<lambda>s. SOME a. a \<in> A s \<and> L\<^sub>a a v s = \<L>\<^sub>b v s\<close>] bfun_eqI)
   apply (smt (verit, best) someI_ex)
  apply (subst L_eq_L\<^sub>a)
  apply (subst expectation_return_pmf)
  by (smt (verit, best) someI_ex)

lemma thm_6_2_10:
  assumes "\<And>s. finite (A s)"
  shows "\<exists>d \<in> D\<^sub>D. \<nu>\<^sub>b_opt = \<nu>\<^sub>b (mk_stationary_det d)"
  using assms conserving_imp_opt' \<L>\<^sub>b_opt L_\<nu>_fix_iff ex_opt_dec_det 
  by metis

subsubsection \<open>Existence of Epsilon-Optimal Policies\<close>

lemma ex_det_eps:
  assumes "0 < e"
  shows "\<exists>d \<in> D\<^sub>D. \<L>\<^sub>b v \<le> L (mk_dec_det d) v + e *\<^sub>R 1"
proof -
  have "\<exists>a \<in> A s. \<L>\<^sub>b v s \<le> L\<^sub>a a v s + e" for s
  proof -
    have "bdd_above ((\<lambda>a. L\<^sub>a a v s) ` A s)"
      using L\<^sub>a_le by (auto intro!: boundedI bounded_imp_bdd_above)
    hence "\<exists>a \<in> A s. \<L>\<^sub>b v s - e < L\<^sub>a a v s"
      unfolding \<L>\<^sub>b.rep_eq \<L>_eq_SUP_det SUP_step_det_eq
      by (auto simp: less_cSUP_iff[OF A_ne, symmetric] \<open>0 < e\<close>)
    thus "\<exists>a \<in> A s. \<L>\<^sub>b v s \<le> L\<^sub>a a v s + e"
      by force
  qed
  thus ?thesis
    unfolding mk_dec_det_def is_dec_det_def
    by (auto simp: L_def \<P>\<^sub>1.rep_eq bind_return_pmf K_st_def less_eq_bfun_def) metis
qed

lemma thm_6_2_11:
  assumes "eps > 0"
  shows "\<exists>d \<in> D\<^sub>D. \<nu>\<^sub>b_opt \<le> \<nu>\<^sub>b (mk_stationary_det d) + eps *\<^sub>R 1"
proof -
  have "(1-l) * eps > 0"
    by (simp add: assms)
  then obtain d where "d \<in> D\<^sub>D" and d: "\<L>\<^sub>b \<nu>\<^sub>b_opt \<le> L (mk_dec_det d) \<nu>\<^sub>b_opt + ((1-l)*eps) *\<^sub>R 1"
    using ex_det_eps[of _ \<nu>\<^sub>b_opt] by auto
  let ?d = "mk_dec_det d"
  let ?lK = "l *\<^sub>R \<P>\<^sub>1 ?d"
  let ?lK_opt = "l *\<^sub>R \<P>\<^sub>1 ?d \<nu>\<^sub>b_opt"
  have "\<nu>\<^sub>b_opt  \<le> r_dec\<^sub>b ?d + ?lK_opt + ((1-l)*eps) *\<^sub>R 1"
    using L_def \<L>_fix_imp_opt d by simp
  hence "\<nu>\<^sub>b_opt - ?lK_opt - ((1-l)*eps) *\<^sub>R 1 \<le> r_dec\<^sub>b ?d"
    by (simp add: cancel_ab_semigroup_add_class.diff_right_commute diff_le_eq)
  hence "(\<Sum>i. ?lK ^^ i) (\<nu>\<^sub>b_opt - ?lK_opt - ((1-l)*eps) *\<^sub>R 1) \<le> \<nu>\<^sub>b (mk_stationary ?d)"
    using lemma_6_1_2_b suminf_cong by (simp add: blincomp_scaleR_right \<nu>_stationary)
  hence "((\<Sum>i. ?lK ^^ i) o\<^sub>L (id_blinfun - ?lK)) \<nu>\<^sub>b_opt - (\<Sum>i. ?lK ^^ i) (((1-l)*eps) *\<^sub>R 1) 
    \<le> (\<nu>\<^sub>b (mk_stationary ?d))"
    by (simp add: blinfun.diff_right blinfun.diff_left blinfun.scaleR_left)
  hence le: "\<nu>\<^sub>b_opt - (\<Sum>i. ?lK ^^ i) (((1-l)*eps) *\<^sub>R 1) \<le> \<nu>\<^sub>b (mk_stationary ?d)"
    by (auto simp: inv_norm_le')
  have s: "summable (\<lambda>i. (l *\<^sub>R \<P>\<^sub>1 ?d)^^i)"
    using convergent_disc_\<P>\<^sub>1 summable_iff_convergent'
    by (simp add: blincomp_scaleR_right summable_iff_convergent')
  have "(\<Sum>i. ?lK ^^ i) (((1-l)*eps) *\<^sub>R 1) = eps *\<^sub>R 1"
  proof -
    have "(\<Sum>i. ?lK ^^ i) (((1-l)*eps) *\<^sub>R 1) = ((1-l)*eps) *\<^sub>R (\<Sum>i. ?lK^^i) 1"
      using blinfun.scaleR_right by blast
    also have "\<dots> = ((1-l)*eps) *\<^sub>R (\<Sum>i. (?lK^^i) 1) "
      using s by (auto simp: bounded_linear.suminf[of "\<lambda>x. blinfun_apply x 1"])
    also have "\<dots> = ((1-l)*eps) *\<^sub>R (\<Sum>i. (l ^ i)) *\<^sub>R 1"
      by (auto simp: blinfun.scaleR_left blincomp_scaleR_right bounded_linear_scaleR_left 
          bounded_linear.suminf[of "\<lambda>x. x *\<^sub>R 1"])
    also have "\<dots> = ((1-l)*eps) *\<^sub>R (1 / (1-l)) *\<^sub>R 1"
      by (simp add: suminf_geometric)
    also have "\<dots> = eps *\<^sub>R 1"
      using disc_lt_one \<open>0 < (1 - l) * eps\<close> by auto
    finally show ?thesis .
  qed
  thus ?thesis
    using \<open>d \<in> D\<^sub>D\<close> diff_le_eq le
    by auto
qed

lemma ex_det_dist_eps:
  assumes "0 < (e :: real)"
  shows "\<exists>d \<in> D\<^sub>D. dist (\<L>\<^sub>b v) (L (mk_dec_det d) v) \<le> e"
proof -
  obtain d where "d \<in> D\<^sub>D" "L (mk_dec_det d) v \<le> (\<L>\<^sub>b v)" 
    and h2: "\<L>\<^sub>b v \<le> L (mk_dec_det d) v + e *\<^sub>R 1"
    using assms ex_det_eps L_le_\<L>\<^sub>b by blast
  hence "0 \<le> \<L>\<^sub>b v -  L (mk_dec_det d) v"
    by simp
  moreover have "\<L>\<^sub>b v - L (mk_dec_det d) v \<le> e *\<^sub>R 1"
    using h2 by (simp add: add.commute diff_le_eq)
  ultimately have "\<forall>s. \<bar>(\<L>\<^sub>b v) s -  L (mk_dec_det d) v s\<bar> \<le> e"
    unfolding less_eq_bfun_def by auto
  hence "dist (\<L>\<^sub>b v) (L (mk_dec_det d) v) \<le> e"
    unfolding dist_bfun.rep_eq by (auto intro!: cSUP_least simp: dist_real_def)
  thus ?thesis
    using \<open>d \<in> D\<^sub>D\<close> 
    by auto
qed

lemma less_imp_ex_add_le: "(x :: real) < y \<Longrightarrow> \<exists>eps>0. x + eps \<le> y"
  by (meson field_le_epsilon less_le_not_le nle_le)

lemma \<nu>\<^sub>b_opt_le_det: "\<nu>\<^sub>b_opt s \<le> (\<Squnion>d \<in> D\<^sub>D. \<nu>\<^sub>b (mk_stationary_det d) s)"
proof (subst le_cSUP_iff, safe)
  fix y
  assume "y < \<nu>\<^sub>b_opt s"
  then obtain eps where 1: "y \<le> \<nu>\<^sub>b_opt s - eps" and "eps > 0"
    using less_imp_ex_add_le by force
  hence "eps / 2 > 0" by auto
  obtain d where "d \<in> D\<^sub>D" and "\<nu>\<^sub>b_opt s \<le> \<nu>\<^sub>b (mk_stationary_det d) s + eps / 2"
    using thm_6_2_11[OF \<open>eps / 2 > 0\<close>] by fastforce
  hence "y < \<nu>\<^sub>b (mk_stationary_det d) s"
    using \<open>eps > 0\<close> by (auto simp: diff_less_eq intro: le_less_trans[OF 1])
  thus "\<exists>i\<in>D\<^sub>D. y < \<nu>\<^sub>b (mk_stationary_det i) s"
    using \<open>d \<in> D\<^sub>D\<close> by blast
next
  show "D\<^sub>D = {} \<Longrightarrow> False"
    using D_det_ne by blast
  show "bdd_above ((\<lambda>d. \<nu>\<^sub>b (mk_stationary_det d) s) ` D\<^sub>D)"
    by (auto intro!: bounded_imp_bdd_above boundedI abs_\<nu>_le simp: \<nu>\<^sub>b.rep_eq)
qed

lemma \<nu>\<^sub>b_opt_eq_det: "\<nu>\<^sub>b_opt s = (\<Squnion>d \<in> D\<^sub>D. \<nu>\<^sub>b (mk_stationary_det d) s)"
  using \<nu>\<^sub>b_le_opt_DD D_det_ne
  by (fastforce intro!: antisym[OF \<nu>\<^sub>b_opt_le_det] cSUP_least)

(* unused, delete? *)
lemma lemma_6_3_1_a:
  assumes "v0 \<in> bfun"
  shows "uniform_limit UNIV (\<lambda>n. ((\<lambda>v. \<L> (Bfun v)) ^^ n) v0) \<nu>_opt sequentially"
proof -
  have \<L>_Bfun_eq: "v0 \<in> bfun \<Longrightarrow> ((\<lambda>v. \<L> (Bfun v))^^n) v0 = (\<L>\<^sub>b ^^n) (Bfun v0)" for n
    by (induction n) (auto simp: \<L>\<^sub>b.rep_eq apply_bfun_inverse)
  have "uniform_limit UNIV (\<lambda>n. (\<L>\<^sub>b ^^ n) (Bfun v0)) \<nu>\<^sub>b_opt sequentially"
    by (intro tendsto_bfun_uniform_limit[OF \<L>\<^sub>b_lim])
  hence "uniform_limit UNIV (\<lambda>n. (\<L>\<^sub>b ^^ n) (Bfun v0)) \<nu>_opt sequentially"
    by (simp add: \<nu>_opt_bfun \<nu>\<^sub>b_opt.rep_eq)
  thus ?thesis
    by (auto simp: assms \<L>_Bfun_eq)
qed

lemma dist_Suc_tendsto_zero:
  assumes "(\<lambda>n. f n) \<longlonglongrightarrow> (y::_::real_normed_vector)"
  shows "(\<lambda>n. dist (f n) (f (Suc n))) \<longlonglongrightarrow> 0"
  using assms tendsto_diff tendsto_norm LIMSEQ_Suc by (fastforce simp: dist_norm)

lemma dist_\<L>\<^sub>b_tendsto: "(\<lambda>n. dist ((\<L>\<^sub>b^^n) v) ((\<L>\<^sub>b^^(Suc n)) v)) \<longlonglongrightarrow> 0"
  using \<L>\<^sub>b_lim by (fast intro!: dist_Suc_tendsto_zero)

definition "max_L_ex s v \<equiv> has_arg_max (\<lambda>a. L\<^sub>a a v s) (A s)"

lemma \<nu>\<^sub>b_fin_zero[simp]: "\<nu>\<^sub>b_fin p 0 = 0"
  by (auto simp: \<nu>\<^sub>b_fin.rep_eq)

lemma \<nu>\<^sub>b_fin_Suc[simp]: 
  "\<nu>\<^sub>b_fin (mk_stationary d) (Suc n) = \<nu>\<^sub>b_fin (mk_stationary d) n + ((l *\<^sub>R \<P>\<^sub>1 d)^^ n) (r_dec\<^sub>b d)"
  by (auto simp: \<P>\<^sub>X_sconst \<nu>\<^sub>b_fin.rep_eq \<nu>_fin_eq_\<P>\<^sub>X blincomp_scaleR_right blinfun.scaleR_left)

lemma \<nu>\<^sub>b_fin_eq: "\<nu>\<^sub>b_fin (mk_stationary d) n = (\<Sum>i < n. ((l *\<^sub>R \<P>\<^sub>1 d)^^ i)) (r_dec\<^sub>b d)"
  by (induction n) (auto simp add: plus_blinfun.rep_eq)

lemma L_iter: "(L d ^^ m) v = \<nu>\<^sub>b_fin (mk_stationary d) m + ((l *\<^sub>R \<P>\<^sub>1 d)^^ m) v"
proof (induction m arbitrary: v)
  case (Suc m)
  have "(L d ^^ Suc m) v = (L d ^^ m) (L d v)"
    by (simp add: funpow_Suc_right del: funpow.simps)
  also have "\<dots> = \<nu>\<^sub>b_fin (mk_stationary d) m + ((l *\<^sub>R \<P>\<^sub>1 d) ^^ m) (L d v)"
    using Suc by simp
  also have "\<dots> = \<nu>\<^sub>b_fin (mk_stationary d) (Suc m) + ((l *\<^sub>R \<P>\<^sub>1 d) ^^ Suc m) v"
    unfolding L_def 
    by (auto simp: \<P>\<^sub>1_pow blinfun.bilinear_simps blincomp_scaleR_right funpow_swap1) 
  finally show ?case .
qed simp

lemma bounded_stationary_\<nu>\<^sub>b_fin: "bounded ((\<lambda>x. (\<nu>\<^sub>b_fin (mk_stationary x) N) s) ` X)"
  using \<nu>\<^sub>b_fin.rep_eq abs_\<nu>_fin_le by (auto intro!: boundedI)

lemma bounded_disc_\<P>\<^sub>1: "bounded ((\<lambda>x. (((l *\<^sub>R \<P>\<^sub>1 x) ^^ m) v) s) ` X)"
  by (auto simp: \<P>\<^sub>X_const[symmetric] blinfun.bilinear_simps blincomp_scaleR_right 
      intro!: boundedI[of _  "l ^ m * norm v"] mult_left_mono order.trans[OF abs_le_norm_bfun])

lemma bounded_disc_\<P>\<^sub>1': "bounded ((\<lambda>x. ((\<P>\<^sub>1 x ^^ m) v) s) ` X)"
  by (auto simp: \<P>\<^sub>X_const[symmetric] intro!: boundedI[of _  "norm v"] order.trans[OF abs_le_norm_bfun])

lemma L_iter_le_\<L>\<^sub>b: "is_dec d \<Longrightarrow> (L d ^^ n) v \<le> (\<L>\<^sub>b ^^ n) v"
  using order_trans[OF L_mono L_le_\<L>\<^sub>b] by (induction n) auto

end

subsection \<open>More Restrictive MDP Locales\<close>
locale MDP_fin_acts = discrete_MDP +
  assumes "\<And>s. finite (A s)"

locale MDP_att_\<L> = MDP_reward_disc A K r l
  for
    A and 
    K :: "'s ::countable \<times> 'a ::countable \<Rightarrow> 's pmf" and
    r and l +
  assumes Sup_att: "max_L_ex (s :: 's) v"
begin
theorem \<L>\<^sub>b_eq_argmax_L\<^sub>a:
  fixes v :: "'s \<Rightarrow>\<^sub>b real"
  assumes "is_arg_max (\<lambda>a. L\<^sub>a a v s) (\<lambda>a. a \<in> A s) a"
  shows "\<L>\<^sub>b v s = L\<^sub>a a v s"
  using L\<^sub>a_le assms A_ne \<L>\<^sub>b.rep_eq \<L>_eq_SUP_det SUP_step_det_eq
  by (auto intro!: cSUP_upper2 antisym cSUP_least simp: is_arg_max_linorder)

lemma L\<^sub>a_le_arg_max: "a \<in> A s \<Longrightarrow> L\<^sub>a a v s \<le> L\<^sub>a (arg_max_on (\<lambda>a. L\<^sub>a a v s) (A s)) v s"
  using Sup_att app_arg_max_ge[OF Sup_att[unfolded max_L_ex_def]]
  by (simp add: arg_max_on_def)

lemma arg_max_on_in: "has_arg_max f Q \<Longrightarrow> arg_max_on f Q \<in> Q"
  using has_arg_max_arg_max by (auto simp: arg_max_on_def)

lemma \<L>\<^sub>b_eq_L\<^sub>a_max: "\<L>\<^sub>b v s = L\<^sub>a (arg_max_on (\<lambda>a. L\<^sub>a a v s) (A s)) v s"
  using app_arg_max_eq_SUP[symmetric] Sup_att max_L_ex_def 
  by (auto simp: \<L>\<^sub>b_eq_SUP_det SUP_step_det_eq)

lemma ex_opt_det: "\<exists>d \<in> D\<^sub>D. \<L>\<^sub>b v = L (mk_dec_det d) v"
proof -
  define d where "d = (\<lambda>s. arg_max_on (\<lambda>a. L\<^sub>a a v s) (A s))"
  have "\<L>\<^sub>b v s = L (mk_dec_det d) v s" for s
    by (auto simp: d_def \<L>\<^sub>b_eq_L\<^sub>a_max L_eq_L\<^sub>a_det)
  moreover have "d \<in> D\<^sub>D"
    using Sup_att arg_max_on_in by (auto simp: d_def is_dec_det_def max_L_ex_def)
  ultimately show ?thesis
    by auto
qed

lemma ex_improving_det: "\<exists>d \<in> D\<^sub>D. \<nu>_improving v (mk_dec_det d)"
  using \<nu>_improving_alt ex_opt_det by auto
end

locale MDP_act = discrete_MDP A K for A :: "'s::countable \<Rightarrow> 'a::countable set" and K +
  fixes arb_act ::  "'a set \<Rightarrow> 'a"
  assumes arb_act_in[simp]: "X \<noteq> {} \<Longrightarrow> arb_act X \<in> X" 

locale MDP_act_disc = MDP_act A K + MDP_att_\<L> A K r l
  for A :: "'s::countable \<Rightarrow> 'a::countable set" and K r l
begin


lemma is_opt_act_some: "is_opt_act v s (arb_act (opt_acts v s))"
  using arb_act_in[of "{a. is_arg_max (\<lambda>a. L\<^sub>a a v s) (\<lambda>a. a \<in> A s) a}"] Sup_att has_arg_max_def
  unfolding max_L_ex_def is_opt_act_def by auto

lemma some_opt_acts_in_A: "arb_act (opt_acts v s) \<in> A s"
  using is_opt_act_some unfolding is_opt_act_def is_arg_max_def by auto

lemma \<nu>_improving_opt_acts: "\<nu>_improving v0 (mk_dec_det (\<lambda>s. arb_act (opt_acts (apply_bfun v0) s)))"
  using is_opt_act_def is_opt_act_some some_opt_acts_in_A
  by (subst \<nu>_improving_alt) (fastforce simp: L_eq_L\<^sub>a_det \<L>\<^sub>b_eq_argmax_L\<^sub>a is_dec_det_def)+

end

locale MDP_finite_type = MDP_reward_disc A K r l
  for A and K :: "'s :: finite \<times> 'a :: finite \<Rightarrow> 's pmf" and r l

end
