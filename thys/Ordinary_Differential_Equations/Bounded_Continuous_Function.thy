header {* Bounded Continuous Functions *}
theory Bounded_Continuous_Function
imports Auxiliarities
begin

text{*\label{sec:bcontfun}*}

subsection{* Definition *}

definition "bcontfun = {f :: 'a::topological_space \<Rightarrow> 'b::real_normed_vector.
  continuous_on UNIV f \<and> (\<exists>y. \<forall>x. norm (f x) \<le> y)}"

typedef ('a, 'b) bcontfun =
    "bcontfun :: ('a::topological_space \<Rightarrow> 'b::real_normed_vector) set"
  by (auto simp: bcontfun_def intro: continuous_on_intros)

lemma bcontfunE:
  assumes "f \<in> bcontfun"
  obtains y where "continuous_on UNIV f" "\<And>x. norm (f x) \<le> y"
  using assms unfolding bcontfun_def by blast

lemma bcontfunI:
  "continuous_on UNIV f \<Longrightarrow> (\<And>x. norm (f x) \<le> y) \<Longrightarrow> f \<in> bcontfun"
  unfolding bcontfun_def by auto


subsection{* Supremum norm for a normed vector space *}

instantiation bcontfun :: (topological_space, real_normed_vector) sgn_div_norm
begin

definition "norm f = Sup (range (\<lambda>x. norm (Rep_bcontfun f x)))"

definition "scaleR r f = Abs_bcontfun (\<lambda>x. r *\<^sub>R Rep_bcontfun f x)"

definition "sgn (f::('a,'b) bcontfun) = f /\<^sub>R norm f"

instance proof qed (simp add: sgn_bcontfun_def)
end

instantiation bcontfun :: (topological_space, real_normed_vector) real_vector
begin

definition "-f = Abs_bcontfun (\<lambda>x. -(Rep_bcontfun f x))"

definition "f + g = Abs_bcontfun (\<lambda>x. Rep_bcontfun f x + Rep_bcontfun g x)"

definition "f - g = Abs_bcontfun (\<lambda>x. Rep_bcontfun f x - Rep_bcontfun g x)"

definition "0 = Abs_bcontfun (\<lambda>x. 0)"


lemma plus_cont:
  fixes f g ::"'a \<Rightarrow> 'b"
  assumes f: "f \<in> bcontfun" and g: "g \<in> bcontfun"
  shows "(\<lambda>x. f x + g x) \<in> bcontfun"
proof -
  from bcontfunE[OF f] guess y .
  moreover from bcontfunE[OF g] guess z .
  ultimately show ?thesis
    by (auto intro!: exI[where x="y + z"] continuous_on_add norm_add_rule_thm bcontfunI)
qed

lemma Rep_bcontfun_plus[simp]: "Rep_bcontfun (f + g) x = Rep_bcontfun f x + Rep_bcontfun g x"
  by (simp add: plus_bcontfun_def Abs_bcontfun_inverse plus_cont Rep_bcontfun)

lemma minus_cont:
  fixes f g ::"'a \<Rightarrow> 'b"
  assumes f: "f \<in> bcontfun" and g: "g \<in> bcontfun"
  shows "(\<lambda>x. f x - g x) \<in> bcontfun"
proof -
  from bcontfunE[OF f] guess y .
  moreover from bcontfunE[OF g] guess z .
  ultimately show ?thesis
  proof (intro bcontfunI)
    fix x
    assume "\<And>x. norm (f x) \<le> y" "\<And>x. norm (g x) \<le> z"
    from this[of x] norm_triangle_ineq4[of "f x" "g x"]
    show "norm (f x - g x) \<le> y + z" by simp
  qed (simp add:continuous_on_diff)
qed

lemma Rep_bcontfun_minus[simp]:
  "Rep_bcontfun (f - g) x = Rep_bcontfun f x - Rep_bcontfun g x"
  by (simp add: minus_bcontfun_def Abs_bcontfun_inverse minus_cont Rep_bcontfun)

lemma zero_cont: "(\<lambda>x. 0) \<in> bcontfun"
  by (intro bcontfunI[where y=0] continuous_on_const) auto

lemma uminus_cont:
  fixes f ::"'a \<Rightarrow> 'b"
  assumes "f \<in> bcontfun"
  shows "(\<lambda>x. - f x) \<in> bcontfun"
proof -
  from bcontfunE[OF assms] guess y .
  thus ?thesis
  proof (intro bcontfunI)
    fix x
    assume "\<And>x. norm (f x) \<le> y"
    thus "norm (- f x) \<le> y" by simp
  qed (simp add: continuous_on_minus)
qed

lemma Rep_bcontfun_uminus[simp]:
  "Rep_bcontfun (- f) x = - Rep_bcontfun f x"
  by (simp add: uminus_bcontfun_def Abs_bcontfun_inverse uminus_cont Rep_bcontfun)

lemma scaleR_cont:
  fixes a and f
  assumes "f \<in> bcontfun"
  shows " (\<lambda>x. a *\<^sub>R f x) \<in> bcontfun"
proof -
  from bcontfunE[OF assms] guess y .
  thus ?thesis
  proof (intro bcontfunI)
    fix x assume "\<And>x. norm (f x) \<le> y"
    thus "norm (a *\<^sub>R f x) \<le> abs a * y"
      by (simp add: mult_left_mono)
  qed (simp add: continuous_on_intros)
qed

lemma Rep_bcontfun_scaleR[simp]:
   "Rep_bcontfun (a *\<^sub>R g) x = a *\<^sub>R Rep_bcontfun g x"
  by (simp add: scaleR_bcontfun_def Abs_bcontfun_inverse scaleR_cont Rep_bcontfun)

instance
proof
qed (simp_all add: plus_bcontfun_def zero_bcontfun_def minus_bcontfun_def scaleR_bcontfun_def
    Abs_bcontfun_inverse Rep_bcontfun_inverse Rep_bcontfun algebra_simps
    plus_cont zero_cont minus_cont scaleR_cont)
end

instantiation bcontfun :: (topological_space, real_normed_vector) real_normed_vector
begin

definition "dist (f::('a, 'b) bcontfun) g = norm (f - g)"

definition "open S =
       (\<forall>x\<Colon>('a, 'b) bcontfun\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"

lemma norm_bounded:
  fixes f ::"('a, 'b) bcontfun"
  shows "norm (Rep_bcontfun f x) \<le> norm f"
proof -
  have "Rep_bcontfun f \<in> bcontfun" using Rep_bcontfun .
  from bcontfunE[OF this] guess y . note y = this
  show ?thesis unfolding norm_bcontfun_def
  proof (intro Sup_upper)
    fix x assume "x \<in> range (\<lambda>x. norm (Rep_bcontfun f x))"
    with y(2) show "x \<le> y" by auto
  qed simp
qed

lemma norm_bound:
  fixes f ::"('a, 'b) bcontfun"
  assumes "\<And>x. norm (Rep_bcontfun f x) \<le> b"
  shows "norm f \<le> b"
unfolding norm_bcontfun_def
proof (intro Sup_least)
  fix x
  assume "x \<in> range (\<lambda>x. norm (Rep_bcontfun f x))"
  then guess a ..
  thus "x \<le> b" using assms by simp
qed simp

lemma norm_zero_eq_zero:
  fixes f :: "('a, 'b) bcontfun"
  shows "(norm f = 0) = (f = 0)"
proof
  assume norm0: "norm f = 0"
  show "f = 0"
    unfolding Rep_bcontfun_inject[symmetric] zero_bcontfun_def
      Abs_bcontfun_inverse[OF zero_cont]
  proof
    fix a
    have "norm (Rep_bcontfun f a) \<le> norm f" by (rule norm_bounded[of f a])
    hence "norm (Rep_bcontfun f a) = 0" unfolding norm0 by simp
    thus "Rep_bcontfun f a = 0" by simp
  qed
qed (simp add: zero_bcontfun_def norm_bcontfun_def Abs_bcontfun_inverse[OF zero_cont]
    image_constant)

instance
proof
  fix f :: "('a, 'b) bcontfun"
  have "0 \<le> norm (Rep_bcontfun f a)" by (rule norm_ge_zero)
  from order_trans[OF this norm_bounded[of f a]] show "0 \<le> norm f" .
next
  fix f g :: "('a, 'b) bcontfun"
  from bcontfunE[OF Rep_bcontfun[of f]] guess y . note y = this
  from bcontfunE[OF Rep_bcontfun[of g]] guess z . note z = this
  show "norm (f + g) \<le> norm f + norm g"
  proof (subst norm_bcontfun_def, safe intro!: Sup_least)
    fix x
    have "norm (Rep_bcontfun (f + g) x) \<le> norm (Rep_bcontfun f x) + norm (Rep_bcontfun g x)"
      by (simp add: norm_triangle_ineq)
    also have "norm (Rep_bcontfun f x) \<le> norm f" by (rule norm_bounded)
    also have "norm (Rep_bcontfun g x) \<le> norm g" by (rule norm_bounded)
    finally show "norm (Rep_bcontfun (f + g) x) \<le> norm f + norm g" by simp
  qed
next
  fix a and f :: "('a, 'b) bcontfun"
  show "norm (a *\<^sub>R f) = \<bar>a\<bar> * norm f"
  proof (cases "a = 0")
    case False
    from bcontfunE[OF Rep_bcontfun[of f]] guess y . note y = this
    have "Sup (op * \<bar>a\<bar> ` range (\<lambda>x. norm (Rep_bcontfun f x))) =
      \<bar>a\<bar> * Sup (range (\<lambda>x. norm (Rep_bcontfun f x)))"
    proof (intro Sup_real_mult[symmetric])
      fix x
      assume "x \<in> range (\<lambda>x. norm (Rep_bcontfun f x))"
      then guess b .. from this
      show "0 \<le> x \<and> x \<le> norm f"
        by (simp add: norm_bounded)
    qed (simp_all add: False)
    moreover
    have "range (\<lambda>x. norm (Rep_bcontfun (a *\<^sub>R f) x)) =
      (\<lambda>x. \<bar>a\<bar> * x) ` (range (\<lambda>x. norm (Rep_bcontfun f x)))" by auto
    ultimately
    show "norm (a *\<^sub>R f) = \<bar>a\<bar> * norm f" by (simp add: norm_bcontfun_def)
  qed (simp add: norm_zero_eq_zero)
qed (simp_all add: dist_bcontfun_def open_bcontfun_def norm_zero_eq_zero)
end

lemma dist_fun_lt_imp_dist_val_lt:
  assumes "dist f g < e"
  shows "dist (Rep_bcontfun f x) (Rep_bcontfun g x) < e"
  using assms norm_bounded[of "f - g" x] by (simp add: dist_norm)

lemma dist_val_lt_imp_dist_fun_le:
  assumes "\<forall>x. dist (Rep_bcontfun f x) (Rep_bcontfun g x) < e"
  shows "dist f g \<le> e"
unfolding dist_norm norm_bcontfun_def
proof (intro Sup_least)
  fix x
  assume "x \<in> range (\<lambda>x. norm (Rep_bcontfun (f - g) x))"
  then guess a ..
  thus "x \<le> e" using assms[THEN spec[where x=a]] by (simp add: dist_norm)
qed (simp)

subsection {* Complete Space *}

lemma bcontfun_complete:
  shows "complete (UNIV::
    ('a::metric_space, 'b::{real_normed_vector, heine_borel}) bcontfun set)"
  unfolding complete_def LIMSEQ_def
proof (safe)
  fix f::"nat \<Rightarrow> ('a,'b) bcontfun"
  assume "Cauchy f" --{* Cauchy equals uniform convergence *}
  then obtain g where limit_function: 
    "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x. dist (Rep_bcontfun (f n) x) (g x) < e"
    using uniformly_convergent_eq_cauchy[of "\<lambda>_. True"
      "\<lambda>n. Rep_bcontfun (f n)"]
    unfolding Cauchy_def by (metis dist_fun_lt_imp_dist_val_lt)

  then obtain N where fg_dist: --{* for an upper bound on g *}
    "\<forall>n\<ge>N. \<forall>x. norm (g x - Rep_bcontfun (f n) x) < 1"
    by (force simp add: dist_norm norm_minus_commute)
  from bcontfunE[OF Rep_bcontfun, of "f N"] obtain b where
    f_bound: "\<forall>x. norm (Rep_bcontfun (f N) x) \<le> b" by force

  have "g \<in> bcontfun" --{* The limit function is bounded and continuous *}
  proof (intro bcontfunI)
    show "continuous_on UNIV g"
      using bcontfunE[OF Rep_bcontfun] limit_function
      by (intro continuous_uniform_limit[where
        f="%n. Rep_bcontfun (f n)" and F="sequentially"]) (auto
        simp add: eventually_sequentially trivial_limit_def dist_norm)
  next
    fix x
    from fg_dist have "norm (g x - Rep_bcontfun (f N) x) < 1"
      by (simp add: dist_norm norm_minus_commute)
    with norm_triangle_ineq2[of "g x" "Rep_bcontfun (f N) x"]
    show "norm (g x) \<le> 1 + b" using f_bound[THEN spec, of x]
      by (simp add: dist_norm norm_minus_commute)
  qed
  show "\<exists>l\<in>UNIV. \<forall>e>0. \<exists>N. \<forall>n\<ge>N. dist (f n) l < e"
    --{* The limit function converges according to its norm *}
  proof (rule, rule, rule)
    fix e::real
    assume "e > 0" hence "e/2 > 0" by simp
    with limit_function[THEN spec, of"e/2"]
    have "\<exists>N. \<forall>n\<ge>N. \<forall>x. dist (Rep_bcontfun (f n) x) (g x) < e/2"
      by simp
    then guess N .. note N=this
    show "\<exists>N. \<forall>n\<ge>N. dist (f n) (Abs_bcontfun g) < e"
    proof (rule+)
      fix n
      assume "N \<le> n"
      with N show "dist (f n) (Abs_bcontfun g) < e"
        using dist_val_lt_imp_dist_fun_le[of
          "f n" "Abs_bcontfun g" "e/2"]
          Abs_bcontfun_inverse[OF `g \<in> bcontfun`] `e > 0` by simp
    qed
  qed simp
qed

subsection{* Continuously Extended Functions *}

definition clamp::"'a::ordered_euclidean_space \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "clamp a b x = (\<Sum>i\<in>Basis.
    (if x\<bullet>i < a\<bullet>i then a\<bullet>i else if x\<bullet>i \<le> b\<bullet>i then x\<bullet>i else b\<bullet>i) *\<^sub>R i)"

definition ext_cont::
  "('a::ordered_euclidean_space \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a, 'b) bcontfun"
  where "ext_cont f a b = Abs_bcontfun ((\<lambda>x. f (clamp a b x)))"

lemma ext_cont_def':
  "ext_cont f a b =
  Abs_bcontfun (\<lambda>x. f (\<Sum>i\<in>Basis. (if x\<bullet>i < a\<bullet>i then a\<bullet>i else if x\<bullet>i \<le> b\<bullet>i then x\<bullet>i else b\<bullet>i) *\<^sub>R i))"
unfolding ext_cont_def clamp_def ..

lemma clamp_in_interval:
  assumes "{a..b} \<noteq> {}"
  shows "clamp a b x \<in> {a..b}"
  unfolding clamp_def
  using interval_ne_empty(1)[of a b] assms
  by (auto simp add: eucl_le[of a] eucl_le[where y=b])

lemma dist_clamps_le_dist_args:
  fixes x::"'a::ordered_euclidean_space"
  assumes "{a..b} \<noteq> {}"
  shows "dist (clamp a b y) (clamp a b x) \<le> dist y x"
proof -
    from interval_ne_empty(1)[of a b] assms have "(\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i)" ..
    hence "(\<Sum>i\<in>Basis. (dist (clamp a b y \<bullet> i) (clamp a b x \<bullet> i))\<twosuperior>)
    \<le> (\<Sum>i\<in>Basis. (dist (y \<bullet> i) (x \<bullet> i))\<twosuperior>)"
      by (auto intro!: setsum_mono
        simp add: clamp_def dist_real_def real_abs_le_square_iff[symmetric])
    thus ?thesis
      by (auto intro: real_sqrt_le_mono
        simp add: euclidean_dist_l2[where y=x] euclidean_dist_l2[where y="clamp a b x"] setL2_def)
qed

lemma clamp_continuous_at:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::metric_space"
  fixes x
  assumes "{a..b} \<noteq> {}"
  assumes f_cont: "continuous_on {a..b} f"
  shows "continuous (at x) (\<lambda>x. f (clamp a b x))"
unfolding continuous_at_eps_delta
proof (safe)
  fix x::'a and e::real
  assume "0 < e"
  moreover
  have "clamp a b x \<in> {a..b}" using clamp_in_interval assms by simp
  moreover
  note f_cont[simplified continuous_on_iff]
  ultimately
  have
    "\<exists>d>0. \<forall>x'\<in>{a..b}. dist x' (clamp a b x) < d \<longrightarrow> dist (f x') (f (clamp a b x)) < e" by fast
  then guess d .. note d=this
  show "\<exists>d>0. \<forall>x'. dist x' x < d \<longrightarrow>
    dist (f (clamp a b x')) (f (clamp a b x)) < e"
  proof (rule+)
    show "\<forall>x'. dist x' x < d \<longrightarrow>
      dist (f (clamp a b x')) (f (clamp a b x)) < e"
    proof (safe)
      fix x'
      assume "dist x' x < d"
      with dist_clamps_le_dist_args[OF assms(1), of x' x] d
      show "dist (f (clamp a b x')) (f (clamp a b x)) < e"
        using clamp_in_interval[OF assms(1), of x']
        by (simp add: ext_cont_def)
    qed
  qed (simp add: d)
qed

lemma clamp_continuous_on:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::metric_space"
  assumes "{a..b} \<noteq> {}"
  assumes f_cont: "continuous_on {a..b} f"
  shows "continuous_on UNIV (\<lambda>x. f (clamp a b x))"
  using assms
  by (auto intro: continuous_at_imp_continuous_on clamp_continuous_at)

lemma clamp_bcontfun:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "{a..b} \<noteq> {}"
  assumes continuous: "continuous_on {a..b} f"
  shows "(\<lambda>x. f (clamp a b x)) \<in> bcontfun"
proof -
  from compact_continuous_image[OF continuous compact_interval[of a b], THEN compact_imp_bounded]
  have "bounded (f ` {a..b})" .
  then obtain c where f_bound: "\<forall>x\<in>f ` {a..b}. norm x \<le> c" by (auto simp add: bounded_pos)
  show "(\<lambda>x. f (clamp a b x)) \<in> bcontfun"
  proof (intro bcontfunI)
    fix x
    from clamp_in_interval[OF assms(1), of x] f_bound
    show "norm (f (clamp a b x)) \<le> c" by (simp add: ext_cont_def)
  qed (simp add: clamp_continuous_on assms)
qed

declare [[coercion Rep_bcontfun]]

lemma ext_cont_cancel[simp]:
  fixes x a b::"'a::ordered_euclidean_space"
  assumes x: "x \<in> {a..b}"
  assumes "continuous_on {a..b} f"
  shows "ext_cont f a b x = f x"
  using assms
  unfolding ext_cont_def
proof (subst Abs_bcontfun_inverse[OF clamp_bcontfun])
  show "f (clamp a b x) = f x"
    using x unfolding clamp_def mem_interval
    by (intro arg_cong[where f=f] euclidean_eqI[where 'a='a]) (simp add: not_less)
qed auto

end