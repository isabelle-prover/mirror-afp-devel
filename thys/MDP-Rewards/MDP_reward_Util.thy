theory MDP_reward_Util
  imports Blinfun_Util
begin
section \<open>Auxiliary Lemmas\<close>

subsection \<open>Summability\<close>

lemma summable_powser_const:
  fixes c :: real 
  assumes "\<bar>c\<bar> < 1"
  shows "summable (\<lambda>n. c^n * x)"
  using assms
  by (auto simp: mult.commute)

subsection \<open>Infinite sums\<close>

lemma suminf_split_head': 
  "summable (f :: nat \<Rightarrow> 'x :: real_normed_vector) \<Longrightarrow> suminf f = f 0 + (\<Sum>n. f (Suc n))"
  by (auto simp: suminf_split_head)

lemma sum_disc_lim: 
  assumes "\<bar>c :: real\<bar> < 1" 
  shows "(\<Sum>x. c^x * B) = B /(1-c)"
  by (simp add: assms suminf_geometric summable_geometric suminf_mult2[symmetric])

subsection \<open>Bounded Functions\<close>

lemma suminf_apply_bfun:
  fixes f :: "nat \<Rightarrow> 'c \<Rightarrow>\<^sub>b real"  
  assumes "summable f"
  shows "(\<Sum>i. f i) x = (\<Sum>i. f i x)"
  by (auto intro!: bounded_linear.suminf assms bounded_linear_intro[where K = 1] abs_le_norm_bfun)

lemma sum_apply_bfun:
  fixes f :: "nat \<Rightarrow> 'c \<Rightarrow>\<^sub>b real"  
  shows "(\<Sum>i<n. f i) x = (\<Sum>i<n. apply_bfun (f i) x)"
  by (induction n) auto  

subsection \<open>Push-Forward of a Bounded Function\<close>

lemma integrable_bfun_prob_space [simp]: 
  "integrable (measure_pmf P) (\<lambda>t. apply_bfun f (F t) :: real)"
proof -
  obtain b where "\<forall>t. \<bar>f (F t)\<bar> \<le> b"
    by (metis norm_le_norm_bfun real_norm_def)
  hence "(\<integral>\<^sup>+ x. ennreal \<bar>f (F x)\<bar> \<partial>P) \<le> b"
    using nn_integral_mono ennreal_leI
    by (auto intro: measure_pmf.nn_integral_le_const)
  then show ?thesis
    using ennreal_less_top le_less_trans 
    by (fastforce simp: integrable_iff_bounded)
qed

lift_definition push_exp :: "('b \<Rightarrow> 'c pmf) \<Rightarrow> ('c \<Rightarrow>\<^sub>b real) \<Rightarrow> ('b \<Rightarrow>\<^sub>b real)" is
  "\<lambda>c f s. measure_pmf.expectation (c s) f"
  using bfun_integral_bound' .

declare push_exp.rep_eq[simp]

lemma norm_push_exp_le_norm: "norm (push_exp d x) \<le> norm x"
proof -
  have "\<And>s. (\<integral>s'. norm (x s') \<partial>d s) \<le> norm x"
    using measure_pmf.prob_space_axioms norm_le_norm_bfun[of x]
    by (auto intro!: prob_space.integral_le_const)
  hence aux: "\<And>s. norm (\<integral>s'. x s' \<partial>d s) \<le> norm x"
    using integral_norm_bound order_trans by blast
  have "norm (push_exp d x) = (\<Squnion>s. norm (\<integral>s'. x s' \<partial>d s))"
    unfolding norm_bfun_def'
    by auto
  also have "\<dots> \<le> norm x"
    using aux by (fastforce intro!: cSUP_least)
  finally show ?thesis .
qed

lemma push_exp_bounded_linear [simp]: "bounded_linear (push_exp d)"
  using norm_push_exp_le_norm
  by (auto intro!: bounded_linear_intro[where K = 1])

lemma onorm_push_exp [simp]: "onorm (push_exp d) = 1"
proof (intro antisym)
  show "onorm (push_exp d) \<le> 1"
    using norm_push_exp_le_norm 
    by (auto intro!: onorm_bound)
next
  show "1 \<le> onorm (push_exp d)"
    using onorm[of _ 1, OF push_exp_bounded_linear] 
    by (auto simp: norm_bfun_def')
qed

lemma push_exp_return[simp]: "push_exp return_pmf = id"
  by (auto simp: eq_id_iff[symmetric])

subsection \<open>Boundedness\<close>

lemma bounded_abs[intro]: 
  "bounded (X' :: real set) \<Longrightarrow> bounded (abs ` X')"
  by (auto simp: bounded_iff)

lemma bounded_abs_range[intro]: 
  "bounded (range f :: real set) \<Longrightarrow> bounded (range (\<lambda>x. abs (f x)))"
  by (auto simp: bounded_iff)

subsection \<open>Probability Theory\<close>

lemma integral_measure_pmf_bind: 
  assumes "(\<And>x. \<bar>(f :: 'b \<Rightarrow> real) x\<bar> \<le> B)"
  shows "(\<integral>x. f x \<partial>((measure_pmf M) \<bind> (\<lambda>x. measure_pmf (N x)))) = (\<integral>x. \<integral>y. f y \<partial>N x \<partial>M)"
  using assms
  by (subst integral_bind[of _ "count_space UNIV" B]) (auto simp: measure_pmf_in_subprob_space)

lemma lemma_4_3_1': 
  assumes "set_pmf p \<subseteq> W" 
    and "bounded ((w :: 'c \<Rightarrow> real) ` W)" 
    and "W \<noteq> {}"
    and "measure_pmf.expectation p w = (\<Squnion>p \<in> {p. set_pmf p \<subseteq> W}. measure_pmf.expectation p w)" 
  shows "\<exists>x \<in> W. measure_pmf.expectation p w = w x"
proof -
  have abs_w_le_sup: "y \<in> W \<Longrightarrow> \<bar>w y\<bar> \<le> (\<Squnion>x \<in> W. \<bar>w x\<bar>)" for y
    using assms bounded_abs[OF assms(2)]
    by (auto intro!: cSUP_upper bounded_imp_bdd_above simp: image_image)
  have "False" if "x \<in> set_pmf p" "w x < \<Squnion>(w ` W)" for x
  proof -
    have ex_gr: "\<exists>x'. x' \<in> W \<and> w x < w x'"
      using cSUP_least[of W w "w x"] that assms
      by fastforce
    let ?s = "\<lambda>s. (if x = s then SOME x'. x' \<in> W \<and> w x < w x' else s)"
    have "measure_pmf.expectation p w < measure_pmf.expectation p (\<lambda>xa. w (?s xa))"
    proof (intro measure_pmf.integral_less_AE[where A = "{x}"])
      show "integrable (measure_pmf p) w"
        using assms abs_w_le_sup 
        by (fastforce simp: AE_measure_pmf_iff 
            intro!: measure_pmf.integrable_const_bound)
      show "integrable (measure_pmf p) (\<lambda>xa. w (?s xa))"
        using assms(1) ex_gr someI[where P = "\<lambda>x'. (x' \<in> W) \<and> (w x < w x')"]
        by (fastforce simp: AE_measure_pmf_iff 
            intro!: abs_w_le_sup measure_pmf.integrable_const_bound)
      show "emeasure (measure_pmf p) {x} \<noteq> 0"
        by (simp add: emeasure_pmf_single_eq_zero_iff \<open>x \<in> p\<close>)
      show "{x} \<in> measure_pmf.events p"
        by auto
      show "AE xa\<in>{x} in p. w xa \<noteq> w (?s xa)" "AE xa in p. w xa \<le> w (?s xa)"
        using someI[where P = "\<lambda>x'. (x' \<in> W) \<and> (w x < w x')"] ex_gr
        by (fastforce intro!: AE_pmfI)+
    qed
    hence "measure_pmf.expectation p w < \<Squnion>((\<lambda>p. measure_pmf.expectation p w) ` {p. set_pmf p \<subseteq> W})"
    proof (subst less_cSUP_iff, goal_cases)
      case 1
      then show ?case 
        using assms(1) 
        by blast
    next
      case 2
      then show ?case 
        using abs_w_le_sup
        by (fastforce 
            simp: AE_measure_pmf_iff 
            intro: cSUP_upper2 bdd_aboveI[where M = "(\<Squnion>x\<in>W. \<bar>w x\<bar>)"]
            intro!: measure_pmf.integral_le_const measure_pmf.integrable_const_bound)
    next
      case 3
      then show ?case 
        using ex_gr someI[where P = "\<lambda>x'. (x' \<in> W) \<and> (w x < w x')"] assms(1) 
        by (auto intro!: exI[of _ "map_pmf ?s p"])
    qed
    thus False
      using assms by auto
  qed
  hence 1: "x \<in> set_pmf p \<Longrightarrow> w x = \<Squnion> (w ` W)" for x
    using assms
    by (fastforce intro: antisym simp: bounded_imp_bdd_above cSUP_upper)
  hence "w (SOME x. x \<in> set_pmf p) =  \<Squnion> (w ` W)"
    by (simp add: set_pmf_not_empty some_in_eq)
  thus ?thesis
    using 1 assms(1) set_pmf_not_empty some_in_eq 
    by (fastforce intro!: bexI[of _ "SOME x. x \<in> set_pmf p"]
        simp: AE_measure_pmf_iff Bochner_Integration.integral_cong_AE[where ?g = "\<lambda>_. \<Squnion> (w ` W)"])
qed

lemma lemma_4_3_1: 
  assumes "set_pmf p \<subseteq> W" "integrable (measure_pmf p) w" "bounded ((w :: 'c \<Rightarrow> real) ` W)"
  shows "measure_pmf.expectation p w \<le> \<Squnion>(w ` W)"
  using assms bounded_has_Sup(1) prob_space_measure_pmf
  by (fastforce simp: AE_measure_pmf_iff intro!: prob_space.integral_le_const)

lemma bounded_integrable: 
  assumes "bounded (range v)" "v \<in> borel_measurable (measure_pmf p)" 
  shows "integrable (measure_pmf p) (v :: 'c \<Rightarrow> real)"
  using assms
  by (auto simp: bounded_iff AE_measure_pmf_iff intro!: measure_pmf.integrable_const_bound)

subsection \<open>Argmax\<close>
lemma finite_is_arg_max: "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>x. is_arg_max (f :: 'c \<Rightarrow> real) (\<lambda>x. x \<in> X) x"
  unfolding is_arg_max_def
proof (induction rule: finite_induct)
  case (insert x F)
  then show ?case
  proof (cases "\<forall>y \<in> F. f y \<le> f x")
    case True
    then show ?thesis
      by (auto intro!: exI[of _ x])
  next
    case False
    then show ?thesis
      using insert by force
  qed
qed simp

lemma finite_arg_max_le:
  assumes "finite (X :: 'c set)" "X \<noteq> {}"
  shows "s \<in> X \<Longrightarrow> (f :: 'c \<Rightarrow> real) s \<le> f (arg_max_on (f :: 'c \<Rightarrow> real) X)"
  unfolding arg_max_def arg_max_on_def
  by (metis assms(1) assms(2) finite_is_arg_max is_arg_max_linorder someI_ex)

lemma arg_max_on_in:
  assumes "finite (X :: 'c set)" "X \<noteq> {}"
  shows "(arg_max_on (f :: 'c \<Rightarrow> real)  X) \<in> X"
  unfolding arg_max_on_def arg_max_def
  by (metis assms(1) assms(2) finite_is_arg_max is_arg_max_def someI)

lemma finite_arg_max_eq_Max:
  assumes "finite (X :: 'c set)" "X \<noteq> {}"
  shows "(f :: 'c \<Rightarrow> real) (arg_max_on f X) = Max (f ` X)"
  using assms
  by (auto intro!: Max_eqI[symmetric] finite_arg_max_le arg_max_on_in)


lemma arg_max_SUP: "is_arg_max (f :: 'b \<Rightarrow> real) (\<lambda>x. x \<in> X) m \<Longrightarrow> f m = (\<Squnion>(f ` X))"
  unfolding is_arg_max_def
  by (auto intro!: antisym cSUP_upper bdd_aboveI[of _ "f m"] cSUP_least)

definition "has_max X \<equiv> \<exists>x \<in> X. \<forall>x' \<in> X. x' \<le> x"
definition "has_arg_max f X \<equiv> \<exists>x. is_arg_max f (\<lambda>x. x \<in> X) x"

lemma "has_max ((f :: 'b \<Rightarrow> real) ` X) \<longleftrightarrow> has_arg_max f X"
  unfolding has_max_def has_arg_max_def is_arg_max_def
  using not_less by (auto dest!: leD simp: not_less)

lemma has_arg_max_is_arg_max: "has_arg_max f X \<Longrightarrow> is_arg_max f (\<lambda>x. x \<in> X) (arg_max f (\<lambda>x. x \<in> X))"
  unfolding has_arg_max_def arg_max_def
  by (auto intro: someI)

lemma has_arg_max_arg_max: "has_arg_max f X \<Longrightarrow> (arg_max f (\<lambda>x. x \<in> X)) \<in> X"
  unfolding has_arg_max_def arg_max_def is_arg_max_def by (auto intro: someI2_ex)
  

lemma app_arg_max_ge: "has_arg_max (f :: 'b \<Rightarrow> real) X \<Longrightarrow> x \<in> X \<Longrightarrow> f x \<le> f (arg_max_on f X)"
  unfolding has_arg_max_def arg_max_on_def arg_max_def is_arg_max_def
  using someI[where ?P = "\<lambda>x. x \<in> X \<and> (\<nexists>y. y \<in> X \<and> f x < f y)"] le_less_linear
  by auto

lemma app_arg_max_eq_SUP: "has_arg_max (f :: 'b \<Rightarrow> real) X \<Longrightarrow> f (arg_max_on f X) = \<Squnion>(f ` X)"
  by (simp add: arg_max_SUP arg_max_on_def has_arg_max_is_arg_max)

lemma SUP_is_arg_max: 
  assumes "x \<in> X" "bdd_above (f ` X)" "(f :: 'c \<Rightarrow> real) x = \<Squnion>(f ` X)" 
  shows "is_arg_max f (\<lambda>x. x \<in> X) x"
  unfolding is_arg_max_def
  using not_less assms cSUP_upper[of _ X f] 
  by auto

lemma is_arg_max_linorderI[intro]: fixes f :: "'c \<Rightarrow> 'b :: linorder"
  assumes "P x" "\<And>y. (P y \<Longrightarrow> f x \<ge> f y)"
  shows "is_arg_max f P x"
  using assms by (auto simp: is_arg_max_linorder)

lemma is_arg_max_linorderD[dest]: fixes f :: "'c \<Rightarrow> 'b :: linorder"
  assumes "is_arg_max f P x"
  shows "P x" "(P y \<Longrightarrow> f x \<ge> f y)"
  using assms by (auto simp: is_arg_max_linorder)

lemma is_arg_max_cong: 
  assumes "\<And>x. P x \<Longrightarrow> f x = g x"
  shows "is_arg_max f P x \<longleftrightarrow> is_arg_max g P x"
  unfolding is_arg_max_def using assms by auto

lemma is_arg_max_cong':
  assumes "\<And>x. P x \<Longrightarrow> f x = g x"
  shows "is_arg_max f P = is_arg_max g P"
  using assms by (auto cong: is_arg_max_cong)

lemma is_arg_max_congI: 
  assumes "is_arg_max f P x" "\<And>x. P x \<Longrightarrow> f x = g x" 
  shows "is_arg_max g P x" 
  using is_arg_max_cong assms by force

subsection \<open>Contraction Mappings\<close>

definition "is_contraction C \<equiv> \<exists>l. 0 \<le> l \<and> l < 1 \<and> (\<forall>v u. dist (C v) (C u) \<le> l * dist v u)"

lemma banach':
  fixes C :: "'b :: complete_space \<Rightarrow> 'b"
  assumes "is_contraction C"
  shows "\<exists>!v. C v = v" "\<And>v. (\<lambda>n. (C ^^ n) v) \<longlonglongrightarrow> (THE v. C v = v)"
proof -
  obtain v where C: "C v = v" "\<forall>v'. C v' = v' \<longrightarrow> v' = v" 
    by (metis assms is_contraction_def banach_fix_type)
  obtain l where cont: "dist (C v) (C u) \<le> l * dist v u" "0 \<le> l" "l < 1" for v u
    using assms is_contraction_def by blast
  have *: "\<And>n v0. dist ((C ^^ n) v0) v \<le> l ^ n * dist v0 v"
  proof -
    fix n v0
    show "dist ((C ^^ n) v0) v \<le> l ^ n * dist v0 v"
    proof (induction n)
      case (Suc n)
      thus "dist ((C ^^ Suc n) v0) v \<le> l ^ Suc n * dist v0 v"
        using \<open>0 \<le> l\<close>
        by (subst C(1)[symmetric]) (auto simp: algebra_simps intro!: order_trans[OF cont(1)] mult_left_mono)
    qed simp
  qed
  have "(\<lambda>n. l ^ n) \<longlonglongrightarrow> 0"
    by (simp add: LIMSEQ_realpow_zero \<open>0 \<le> l\<close> \<open>l < 1\<close>)
  hence "\<And>v0. (\<lambda>n. l ^ n * dist v0 v) \<longlonglongrightarrow> 0"
    by (simp add: tendsto_mult_left_zero)
  hence "(\<lambda>n. dist ((C ^^ n) v0) v) \<longlonglongrightarrow> 0" for v0
      using * order_trans abs_ge_self
      by (subst Limits.tendsto_0_le[of "(\<lambda>n. l ^ n * dist v0 v)" _ _ 1]) 
        (fastforce intro!: eventuallyI)+
  hence "\<And>v0. (\<lambda>n. (C ^^ n) v0) \<longlonglongrightarrow> v"
    using tendsto_dist_iff by blast
  thus "\<And>v0. (\<lambda>n. (C ^^ n) v0) \<longlonglongrightarrow> (THE v. C v = v)"
    by (metis (mono_tags, lifting) C theI')
next
  show "\<exists>!v. C v = v"
    using assms banach_fix_type unfolding is_contraction_def by blast
qed

lemma contraction_dist:
  fixes C :: "'b :: complete_space \<Rightarrow> 'b"
  assumes "\<And>v u. dist (C v) (C u) \<le> c  * dist v u"
  assumes "0 \<le> c" "c < 1"
  shows "(1 - c) * dist v (THE v. C v = v) \<le> dist v (C v)"
proof -
  have "is_contraction C"
    unfolding is_contraction_def using assms by auto
  then obtain v_fix where v_fix: "v_fix = (THE v. C v = v)"
    using the1_equality by blast
  hence "(\<lambda>n. (C ^^ n) v) \<longlonglongrightarrow> v_fix"
    using banach'[OF \<open>is_contraction C\<close>] by simp
  have dist_contr_le_pow: "\<And>n. dist ((C ^^ n) v) ((C ^^ Suc n) v) \<le> c ^ n * dist v (C v)"
  proof -
    fix n 
    show "dist ((C ^^ n) v) ((C ^^ Suc n) v) \<le> c ^ n * dist v (C v)"
      using assms
      by (induction n) (auto simp: algebra_simps intro!: order.trans[OF assms(1)] mult_left_mono)
  qed
  have summable_C: "summable (\<lambda>i. dist ((C ^^ i) v) ((C ^^ Suc i) v))"
        using dist_contr_le_pow assms summable_powser_const
        by (intro summable_comparison_test[of "(\<lambda>i. dist ((C ^^ i) v) ((C ^^ Suc i) v))" "\<lambda>i. c^i * dist v (C v)"]) 
          auto
  have "\<forall>e > 0. dist v v_fix \<le> (\<Sum>i. dist ((C ^^ i) v) ((C ^^ (Suc i)) v)) + e"
  proof safe
    fix e ::real assume "0 < e"
    have "\<forall>\<^sub>F n in sequentially. dist ((C^^n) v) v_fix < e"
      using \<open>(\<lambda>n. (C ^^ n) v) \<longlonglongrightarrow> v_fix\<close> \<open>0 < e\<close> tendsto_iff by force
    then obtain N where "dist ((C^^N) v) v_fix < e"
      by fastforce
    hence *: "dist v v_fix \<le> dist v ((C^^N) v) + e"
      by (metis add_le_cancel_left dist_commute dist_triangle_le less_eq_real_def)
    have "dist v ((C^^N) v) \<le> (\<Sum>i\<le>N. dist ((C ^^ i) v) ((C ^^ (Suc i)) v))"
    proof (induction N arbitrary: v)
      case 0
      then show ?case by simp
    next
      case (Suc N)      
      have "dist v ((C ^^ Suc N) v) \<le> dist v (C v) + dist (C v) ((C^^(Suc N)) v)"
        by metric
      also have "\<dots> =  dist v (C v) + dist (C v) ((C^^N) (C v))"
        by (metis funpow_simps_right(2) o_def)
      also have "\<dots> \<le> dist v (C v) + (\<Sum>i\<le>N. dist ((C ^^ i) (C v)) ((C ^^ Suc i) (C v)))"
        using Suc.IH add_le_cancel_left by blast
      also have "\<dots> \<le> dist v (C v) + (\<Sum>i\<le>N. dist ((C ^^Suc i) v) ((C ^^ (Suc (Suc i))) v))"
        by (simp only: funpow_simps_right(2) o_def)
      also have "\<dots> \<le> (\<Sum>i\<le>Suc N. dist ((C ^^ i) v) ((C ^^ (Suc i)) v))"
        by (subst sum.atMost_Suc_shift) simp
      finally show "dist v ((C ^^ Suc N) v) \<le> (\<Sum>i\<le>Suc N. dist ((C ^^ i) v) ((C ^^ Suc i) v))" .
    qed
    moreover have 
      "(\<Sum>i\<le>N. dist ((C ^^ i) v) ((C ^^ Suc i) v)) \<le> (\<Sum>i. dist ((C ^^ i) v) ((C ^^ (Suc i)) v))"
      using summable_C 
      by (auto intro: sum_le_suminf)
    ultimately have "dist v ((C^^N) v) \<le> (\<Sum>i. dist ((C ^^ i) v) ((C ^^ (Suc i)) v))"
      by linarith
    thus "dist v v_fix \<le> (\<Sum>i. dist ((C ^^ i) v) ((C ^^ Suc i) v)) + e"
      using * by fastforce
  qed
  hence le_suminf: "dist v v_fix \<le> (\<Sum>i. dist ((C ^^ i) v) ((C ^^ Suc i) v))"
    using field_le_epsilon by blast
  have "dist v v_fix \<le> (\<Sum>i. c ^ i * dist v (C v))"
    using dist_contr_le_pow summable_C assms summable_powser_const
    by (auto intro!: order_trans[OF le_suminf] suminf_le)
  hence "dist v v_fix \<le> dist v (C v) / (1 - c)"
    using sum_disc_lim
    by (metis sum_disc_lim abs_of_nonneg assms(2) assms(3))
  hence "(1 - c) * dist v v_fix \<le> dist v (C v)"
    using assms(3) mult.commute pos_le_divide_eq 
    by (metis diff_gt_0_iff_gt)
  thus ?thesis
    using v_fix by blast
qed

subsection \<open>Limits\<close>
lemma tendsto_bfun_sandwich:
  assumes 
    "(f :: nat \<Rightarrow> 'b \<Rightarrow>\<^sub>b real) \<longlonglongrightarrow> x" "(g :: nat \<Rightarrow> 'b \<Rightarrow>\<^sub>b real) \<longlonglongrightarrow> x" 
    "eventually (\<lambda>n. f n \<le> h n) sequentially" "eventually (\<lambda>n. h n \<le> g n) sequentially"
  shows "(h :: nat \<Rightarrow> 'b \<Rightarrow>\<^sub>b real) \<longlonglongrightarrow> x"
proof -
  have 1: "(\<lambda>n.  dist (f n) (g n) + dist (g n) x) \<longlonglongrightarrow> 0"
    using tendsto_dist[OF assms(1) assms(2)] tendsto_dist_iff assms
    by (auto intro!: tendsto_add_zero)
  have "eventually (\<lambda>n. dist (h n) (g n) \<le> dist (f n) (g n)) sequentially"    
    using assms(3) assms(4)
  proof eventually_elim
    case (elim n)
    hence "dist (h n a) (g n a) \<le> dist (f n a) (g n a)" for a
    proof - 
      have "f n a \<le> h n a" "h n a \<le> g n a"
        using elim unfolding less_eq_bfun_def by auto
      thus ?thesis
        using dist_real_def by fastforce
    qed
    thus ?case
      unfolding dist_bfun.rep_eq
      by (auto intro!: cSUP_mono bounded_imp_bdd_above simp: dist_real_def bounded_minus_comp bounded_abs_range)
  qed
  moreover have "eventually (\<lambda>n. dist (h n) x \<le> dist (h n) (g n) + dist (g n) x) sequentially"
    by (simp add: dist_triangle)
  ultimately have 2: "eventually (\<lambda>n. dist (h n) x \<le> dist (f n) (g n) + dist (g n) x) sequentially"
    using eventually_elim2 by fastforce
  have "(\<lambda>n. dist (h n) x) \<longlonglongrightarrow> 0"
  proof (subst tendsto_iff, safe)
    fix e ::real
    assume "e > 0"
    hence 3: "\<forall>\<^sub>F xa in sequentially. dist (f xa) (g xa) + dist (g xa) x < e"
      using 1 
      by (auto simp: tendsto_iff)
    show "\<forall>\<^sub>F xa in sequentially. dist (dist (h xa) x) 0 < e"
      by (rule eventually_mp[OF _ 3]) (fastforce intro: 2 eventually_mono)
  qed
  thus ?thesis
    using tendsto_dist_iff
    by auto
qed

subsection \<open>Supremum\<close>

lemma SUP_add_le: 
  assumes "X \<noteq> {}" "bounded (B ` X)" "bounded (A' ` X)" 
  shows "(\<Squnion>c \<in> X. (B :: 'a \<Rightarrow> real) c + A' c) \<le> (\<Squnion>b \<in> X. B b) + (\<Squnion>a \<in> X. A' a)"
  using assms 
  by (auto simp: add_mono bounded_has_Sup(1) intro!: cSUP_least)+

lemma le_SUP_diff':
  assumes ne: "X \<noteq> {}"
    and bdd: "bounded (B ` X)" "bounded (A' ` X)" 
    and sup_le: "(\<Squnion>a \<in> X. (A' :: 'a \<Rightarrow> real) a) \<le> (\<Squnion>b \<in> X. B b)"
  shows  "(\<Squnion>b \<in> X. B b) - (\<Squnion>a \<in> X. (A' :: 'a \<Rightarrow> real) a) \<le> (\<Squnion>c \<in> X. B c - A' c)"
proof -
  have "bounded ((\<lambda>x. (B x - A' x)) ` X)"
    using bdd bounded_minus_comp by blast
  have "(\<Squnion>b \<in> X. B b) - (\<Squnion>a \<in> X. A' a) - e \<le> (\<Squnion>c \<in> X. B c - A' c)" if e: "e > 0" for e
  proof -
    obtain z where z: "(\<Squnion>b \<in> X. B b) - e\<le> B z" "z \<in> X"
       using e ne
       by (subst less_cSupE[where ?y = "\<Squnion> (B ` X) - e", where ?X = "B`X"]) fastforce+
    hence " ((\<Squnion>a \<in> X. A' a) \<le> B z + e)"
      using sup_le
      by force
    hence "A' z \<le> B z + e"
      using \<open>z \<in> X\<close> bdd bounded_has_Sup(1) by fastforce
    thus "(\<Squnion>b \<in> X. B b) - (\<Squnion>a \<in> X. A' a) -e \<le> (\<Squnion>c \<in> X. B c - A' c)"
      using \<open>bounded ((\<lambda>x. B x - A' x) ` X)\<close> z bounded_has_Sup(1)[OF bdd(2)]
      by (subst cSUP_upper2[where x = z]) (fastforce intro!: bounded_imp_bdd_above)+
  qed
  thus ?thesis
    by (subst field_le_epsilon) fastforce+
qed

lemma le_SUP_diff:
  fixes A' :: "'a \<Rightarrow> real"
  assumes "X \<noteq> {}" "bounded (B ` X)" "bounded (A' ` X)" "(\<Squnion>a \<in> X. A' a) \<le> (\<Squnion>b \<in> X. B b)"
  shows  "0 \<le> (\<Squnion>c \<in> X. B c - A' c)"
  using assms
  by (auto intro!: order.trans[OF _ le_SUP_diff'])

lemma bounded_SUP_mul[simp]: 
  "X \<noteq> {} \<Longrightarrow> 0 \<le> l \<Longrightarrow> bounded (f ` X) \<Longrightarrow> (\<Squnion>x \<in> X. (l :: real) * f x) = (l * (\<Squnion>x \<in> X. f x))" 
proof -
  assume "X \<noteq> {} "" bounded (f ` X)" "0 \<le> l"
  have "(\<Squnion>x \<in> X. ereal l * ereal (f x)) = (l * (\<Squnion>x \<in> X. ereal (f x)))"
    by (simp add: Sup_ereal_mult_left' \<open>0 \<le> l\<close> \<open>X \<noteq> {}\<close>)
  obtain b where "\<forall>a \<in>X. \<bar>f a\<bar> \<le> b"
    using \<open>bounded (f ` X)\<close> bounded_real by auto
  have "\<forall>a \<in>X. \<bar>ereal (f a)\<bar> \<le> b"
    by (simp add: \<open>\<forall>a\<in>X. \<bar>f a\<bar> \<le> b\<close>)
  hence sup_leb: "(\<Squnion>a\<in>X. \<bar>ereal (f a)\<bar>)\<le> b"
    by (simp add: SUP_least)
  have "(\<Squnion>a\<in>X. ereal (f a)) \<le> (\<Squnion>a\<in>X. \<bar>ereal (f a)\<bar>)"
    by (auto intro: Complete_Lattices.SUP_mono')
  moreover have "-(\<Squnion>a\<in>X. ereal (f a)) \<le> (\<Squnion>a\<in>X. \<bar>ereal (f a)\<bar>)"
    using \<open>X \<noteq> {}\<close>
    by (auto intro!: Inf_less_eq cSUP_upper2 simp add: ereal_INF_uminus_eq[symmetric])
  ultimately have "\<bar>(\<Squnion>a\<in>X. ereal (f a))\<bar> \<le> (\<Squnion>a\<in>X. \<bar>ereal (f a)\<bar>)"
    by (auto intro: ereal_abs_leI)
  hence "\<bar>\<Squnion>a\<in>X. ereal (f a)\<bar> \<le> b"
    using sup_leb by auto
  hence "\<bar>\<Squnion>a\<in>X. ereal (f a)\<bar> \<noteq> \<infinity>"
    by auto
  hence "(\<Squnion>x \<in> X. ereal (f x)) = ereal (\<Squnion>x \<in> X. (f x))"
    using ereal_SUP by metis
  hence "(\<Squnion>x \<in> X. ereal (l * f x)) = ereal (l * (\<Squnion>x \<in> X. f x))"
    using \<open>(\<Squnion>x\<in>X. ereal l * ereal (f x)) = ereal l * (\<Squnion>x\<in>X. ereal (f x))\<close> by auto
  hence "ereal (\<Squnion>x \<in> X. l * f x) = ereal (l * (\<Squnion>x \<in> X. f x))"
    by (simp add: ereal_SUP)
  thus ?thesis
    by auto
qed

lemma abs_cSUP_le[intro]: 
  "X \<noteq> {} \<Longrightarrow> bounded (F ` X) \<Longrightarrow> \<bar>\<Squnion>x \<in> X. (F x) :: real\<bar> \<le> (\<Squnion>x \<in> X. \<bar>F x\<bar>)"
  by (auto intro!: cSup_abs_le cSUP_upper2 bounded_imp_bdd_above simp: image_image[symmetric])

section \<open>Least argmax\<close>
definition "least_arg_max f P = (LEAST x. is_arg_max f P x)"

lemma least_arg_max_prop: "\<exists>x::'a::wellorder. P x \<Longrightarrow> finite {x. P x} \<Longrightarrow> P (least_arg_max (f :: _ \<Rightarrow> real) P)"
  unfolding least_arg_max_def
  apply (rule LeastI2_ex)
  using finite_is_arg_max[of "{x. P x}", where f = f]
  by auto

lemma is_arg_max_apply_eq: "is_arg_max (f :: _ \<Rightarrow> _ :: linorder)  P x \<Longrightarrow> is_arg_max f P y \<Longrightarrow> f x = f y"
  by (auto simp: is_arg_max_def not_less dual_order.eq_iff)
  
lemma least_arg_max_apply:
  assumes "is_arg_max (f :: _ \<Rightarrow> _ :: linorder) P (x::_::wellorder)" 
  shows "f (least_arg_max f P) = f x"
proof -
  have "is_arg_max f P (least_arg_max f P)"
    by (metis LeastI_ex assms least_arg_max_def)
  thus ?thesis
    using is_arg_max_apply_eq assms by metis
qed

lemma apply_arg_max_eq_max: "finite {x . P x} \<Longrightarrow> is_arg_max (f :: _ \<Rightarrow> _ :: linorder) P x \<Longrightarrow> f x = Max (f ` {x. P x})"
  by (auto simp: is_arg_max_def intro!: Max_eqI[symmetric])

lemma apply_arg_max_eq_max': "finite X\<Longrightarrow> is_arg_max (f :: _ \<Rightarrow> _ :: linorder) (\<lambda>x. x \<in> X) x \<Longrightarrow> (MAX x \<in> X. f x) = f x"
  by (auto simp: is_arg_max_linorder intro!: Max_eqI)

lemma least_arg_max_is_arg_max: "P \<noteq> {} \<Longrightarrow> finite P \<Longrightarrow> is_arg_max f (\<lambda>x::_::wellorder. x \<in> P) (least_arg_max (f :: _ \<Rightarrow> real) (\<lambda>x. x \<in> P))"
  unfolding least_arg_max_def
  apply (rule LeastI_ex)
  using finite_is_arg_max 
  by auto

lemma is_arg_max_const: "is_arg_max (f :: _ \<Rightarrow> _ :: linorder) (\<lambda>y. y = c) x \<longleftrightarrow> x = c"
  unfolding is_arg_max_def
  by auto

lemma least_arg_max_cong': 
  assumes "\<And>x. is_arg_max f P x = is_arg_max g P x"
  shows "least_arg_max f P = least_arg_max g P"
  unfolding least_arg_max_def using assms by metis

end
