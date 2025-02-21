theory Q_Library
  imports "HOL-Analysis.Analysis" "HOL-Computational_Algebra.Computational_Algebra"
begin

subsection \<open>Miscellanea\<close>

(* simple generic stuff about finite products *)
lemma prod_uminus: "(\<Prod>x\<in>A. -f x :: 'a :: comm_ring_1) = (-1) ^ card A * (\<Prod>x\<in>A. f x)"
  by (induction A rule: infinite_finite_induct) (auto simp: algebra_simps)

lemma prod_diff_swap:
  fixes f :: "'a \<Rightarrow> 'b :: comm_ring_1"
  shows "prod (\<lambda>x. f x - g x) A = (-1) ^ card A * prod (\<lambda>x. g x - f x) A"
  using prod.distrib[of "\<lambda>_. -1" "\<lambda>x. f x - g x" A] by simp

lemma prod_diff:
  fixes f :: "'a \<Rightarrow> 'b :: field"
  assumes "finite A" "B \<subseteq> A" "\<And>x. x \<in> B \<Longrightarrow> f x \<noteq> 0"
  shows   "prod f (A - B) = prod f A / prod f B"
proof -
  from assms have [intro, simp]: "finite B"
    using finite_subset by blast
  have "prod f A = prod f ((A - B) \<union> B)"
    using assms by (intro prod.cong) auto
  also have "\<dots> = prod f (A - B) * prod f B"
    using assms by (subst prod.union_disjoint) (auto intro: finite_subset)
  also have "\<dots> / prod f B = prod f (A - B)"
    using assms by simp
  finally show ?thesis ..
qed


lemma power_inject_exp':
  assumes "a \<noteq> 1" "a > (0 :: 'a :: linordered_semidom)"
  shows   "a ^ m = a ^ n \<longleftrightarrow> m = n"
proof (cases "a > 1")
  case True
  thus ?thesis by simp
next
  case False
  have "a ^ m > a ^ n" if "m < n" for m n
    by (rule power_strict_decreasing) (use that assms False in auto)
  from this[of m n] this[of n m] show ?thesis
    by (cases m n rule: linorder_cases) auto
qed

lemma q_power_neq_1:
  assumes "norm (q :: 'a :: real_normed_div_algebra) < 1" "n > 0"
  shows   "q ^ n \<noteq> 1"
proof (cases "q = 0")
  case False
  thus ?thesis
    using power_inject_exp'[of "norm q" n 0] assms
    by (auto simp flip: norm_power)
qed (use assms in \<open>auto simp: power_0_left\<close>)  


lemma fls_nth_sum: "fls_nth (\<Sum>x\<in>A. f x) n = (\<Sum>x\<in>A. fls_nth (f x) n)"
  by (induction A rule: infinite_finite_induct) auto

lemma one_plus_fls_X_powi_eq:
  "(1 + fls_X) powi n = fps_to_fls (fps_binomial (of_int n :: 'a :: field_char_0))"
proof (cases "n \<ge> 0")
  case True
  thus ?thesis
    using fps_binomial_of_nat[of "nat n", where ?'a = 'a]
    by (simp add: power_int_def fps_to_fls_power)
next
  case False
  thus ?thesis
    using fps_binomial_minus_of_nat[of "nat (-n)", where ?'a = 'a]
    by (simp add: power_int_def fps_to_fls_power fps_inverse_power flip: fls_inverse_fps_to_fls)
qed



lemma bij_betw_imp_empty_iff: "bij_betw f A B \<Longrightarrow> A = {} \<longleftrightarrow> B = {}"
  unfolding bij_betw_def by blast

lemma bij_betw_imp_Ex_iff: "bij_betw f {x. P x} {x. Q x} \<Longrightarrow> (\<exists>x. P x) \<longleftrightarrow> (\<exists>x. Q x)"
  unfolding bij_betw_def by blast

lemma bij_betw_imp_Bex_iff: "bij_betw f {x\<in>A. P x} {x\<in>B. Q x} \<Longrightarrow> (\<exists>x\<in>A. P x) \<longleftrightarrow> (\<exists>x\<in>B. Q x)"
  unfolding bij_betw_def by blast


(* TODO: needlessly weak version in library; should be replaced *)
lemmas [derivative_intros del] = Deriv.DERIV_power_int
lemma DERIV_power_int [derivative_intros]:
  assumes [derivative_intros]: "(f has_field_derivative d) (at x within s)"
  and "n \<ge> 0 \<or> f x \<noteq> 0"
  shows   "((\<lambda>x. power_int (f x) n) has_field_derivative
             (of_int n * power_int (f x) (n - 1) * d)) (at x within s)"
proof (cases n rule: int_cases4)
  case (nonneg n)
  thus ?thesis 
    by (cases "n = 0"; cases "f x = 0")
       (auto intro!: derivative_eq_intros simp: field_simps power_int_diff 
                     power_diff power_int_0_left_if)
next
  case (neg n)
  thus ?thesis using assms(2)
    by (auto intro!: derivative_eq_intros simp: field_simps power_int_diff power_int_minus
             simp flip: power_Suc power_Suc2 power_add)
qed


(* stuff about uniform limits, swapping limits, etc. *)
lemma uniform_limit_compose':
  assumes "uniform_limit B (\<lambda>x y. f x y) (\<lambda>y. f' y) F" "\<And>y. y \<in> A \<Longrightarrow> g y \<in> B"
  shows   "uniform_limit A (\<lambda>x y. f x (g y)) (\<lambda>y. f' (g y)) F"
proof -
  have "uniform_limit (g ` A) (\<lambda>x y. f x y) (\<lambda>y. f' y) F"
    using assms(1) by (rule uniform_limit_on_subset) (use assms(2) in blast)
  thus "uniform_limit A (\<lambda>x y. f x (g y)) (\<lambda>y. f' (g y)) F"
    unfolding uniform_limit_iff by auto
qed

lemma eventually_eventually_prod_filter1:
  assumes "eventually P (F \<times>\<^sub>F G)"
  shows   "eventually (\<lambda>x. eventually (\<lambda>y. P (x, y)) G) F"
proof -
  from assms obtain Pf Pg where
    *: "eventually Pf F" "eventually Pg G" "\<And>x y. Pf x \<Longrightarrow> Pg y \<Longrightarrow> P (x, y)"
    unfolding eventually_prod_filter by auto
  show ?thesis
    using *(1)
  proof eventually_elim
    case x: (elim x)
    show ?case
      using *(2) by eventually_elim (use x *(3) in auto)
  qed
qed

lemma eventually_eventually_prod_filter2:
  assumes "eventually P (F \<times>\<^sub>F G)"
  shows   "eventually (\<lambda>y. eventually (\<lambda>x. P (x, y)) F) G"
proof -
  from assms obtain Pf Pg where
    *: "eventually Pf F" "eventually Pg G" "\<And>x y. Pf x \<Longrightarrow> Pg y \<Longrightarrow> P (x, y)"
    unfolding eventually_prod_filter by auto
  show ?thesis
    using *(2)
  proof eventually_elim
    case y: (elim y)
    show ?case
      using *(1) by eventually_elim (use y *(3) in auto)
  qed
qed

(* TODO: this is more general than the version in the library *)
proposition swap_uniform_limit':
  assumes f: "\<forall>\<^sub>F n in F. (f n \<longlongrightarrow> g n) G"
  assumes g: "(g \<longlongrightarrow> l) F"
  assumes uc: "uniform_limit S f h F"
  assumes ev: "\<forall>\<^sub>F x in G. x \<in> S"
  assumes "\<not>trivial_limit F"
  shows "(h \<longlongrightarrow> l) G"
proof (rule tendstoI)
  fix e :: real
  define e' where "e' = e/3"
  assume "0 < e"
  then have "0 < e'" by (simp add: e'_def)
  from uniform_limitD[OF uc \<open>0 < e'\<close>]
  have "\<forall>\<^sub>F n in F. \<forall>x\<in>S. dist (h x) (f n x) < e'"
    by (simp add: dist_commute)
  moreover
  from f
  have "\<forall>\<^sub>F n in F. \<forall>\<^sub>F x in G. dist (g n) (f n x) < e'"
    by eventually_elim (auto dest!: tendstoD[OF _ \<open>0 < e'\<close>] simp: dist_commute)
  moreover
  from tendstoD[OF g \<open>0 < e'\<close>] have "\<forall>\<^sub>F x in F. dist l (g x) < e'"
    by (simp add: dist_commute)
  ultimately
  have "\<forall>\<^sub>F _ in F. \<forall>\<^sub>F x in G. dist (h x) l < e"
  proof eventually_elim
    case (elim n)
    note fh = elim(1)
    note gl = elim(3)
    show ?case
      using elim(2) ev
    proof eventually_elim
      case (elim x)
      from fh[rule_format, OF \<open>x \<in> S\<close>] elim(1)
      have "dist (h x) (g n) < e' + e'"
        by (rule dist_triangle_lt[OF add_strict_mono])
      from dist_triangle_lt[OF add_strict_mono, OF this gl]
      show ?case by (simp add: e'_def)
    qed
  qed
  thus "\<forall>\<^sub>F x in G. dist (h x) l < e"
    using eventually_happens by (metis \<open>\<not>trivial_limit F\<close>)
qed

(* TODO: reproved theorem in the library using the more general one above *)
proposition swap_uniform_limit:
  assumes f: "\<forall>\<^sub>F n in F. (f n \<longlongrightarrow> g n) (at x within S)"
  assumes g: "(g \<longlongrightarrow> l) F"
  assumes uc: "uniform_limit S f h F"
  assumes nt: "\<not>trivial_limit F"
  shows "(h \<longlongrightarrow> l) (at x within S)"
proof -
  have ev: "eventually (\<lambda>x. x \<in> S) (at x within S)"
    using eventually_at_topological by blast
  show ?thesis
    by (rule swap_uniform_limit'[OF f g uc ev nt])
qed

text \<open>
  Tannery's Theorem proves that, under certain boundedness conditions:
  \[ \lim_{x\to\bar x} \sum_{k=0}^\infty f(k,n) = \sum_{k=0}^\infty \lim_{x\to\bar x} f(k,n) \]
\<close>
lemma tannerys_theorem:
  fixes a :: "nat \<Rightarrow> _ \<Rightarrow> 'a :: {real_normed_algebra, banach}"
  assumes limit: "\<And>k. ((\<lambda>n. a k n) \<longlongrightarrow> b k) F"
  assumes bound: "eventually (\<lambda>(k,n). norm (a k n) \<le> M k) (at_top \<times>\<^sub>F F)"
  assumes "summable M"
  assumes [simp]: "F \<noteq> bot"
  shows   "eventually (\<lambda>n. summable (\<lambda>k. norm (a k n))) F \<and>
           summable (\<lambda>n. norm (b n)) \<and>
           ((\<lambda>n. suminf (\<lambda>k. a k n)) \<longlongrightarrow> suminf b) F"
proof (intro conjI allI)
  show "eventually (\<lambda>n. summable (\<lambda>k. norm (a k n))) F"
  proof -
    have "eventually (\<lambda>n. eventually (\<lambda>k. norm (a k n) \<le> M k) at_top) F"
      using eventually_eventually_prod_filter2[OF bound] by simp
    thus ?thesis
    proof eventually_elim
      case (elim n)
      show "summable (\<lambda>k. norm (a k n))"
      proof (rule summable_comparison_test_ev)
        show "eventually (\<lambda>k. norm (norm (a k n)) \<le> M k) at_top"
          using elim by auto
      qed fact
    qed
  qed

  have bound': "eventually (\<lambda>k. norm (b k) \<le> M k) at_top"
  proof -
    have "eventually (\<lambda>k. eventually (\<lambda>n. norm (a k n) \<le> M k) F) at_top"
      using eventually_eventually_prod_filter1[OF bound] by simp
    thus ?thesis
    proof eventually_elim
      case (elim k)
      show "norm (b k) \<le> M k"
      proof (rule tendsto_upperbound)
        show "((\<lambda>n. norm (a k n)) \<longlongrightarrow> norm (b k)) F"
          by (intro tendsto_intros limit)
      qed (use elim in auto)
    qed
  qed
  show "summable (\<lambda>n. norm (b n))"
    by (rule summable_comparison_test_ev[OF _ \<open>summable M\<close>]) (use bound' in auto)

  from bound obtain Pf Pg where
    *: "eventually Pf at_top" "eventually Pg F" "\<And>k n. Pf k \<Longrightarrow> Pg n \<Longrightarrow> norm (a k n) \<le> M k"
    unfolding eventually_prod_filter by auto

  show "((\<lambda>n. \<Sum>k. a k n) \<longlongrightarrow> (\<Sum>k. b k)) F"
  proof (rule swap_uniform_limit')
    show "(\<lambda>K. (\<Sum>k<K. b k)) \<longlonglongrightarrow> (\<Sum>k. b k)"
      using \<open>summable (\<lambda>n. norm (b n))\<close>
      by (intro summable_LIMSEQ) (auto dest: summable_norm_cancel)
    show "\<forall>\<^sub>F K in sequentially. ((\<lambda>n. \<Sum>k<K. a k n) \<longlongrightarrow> (\<Sum>k<K. b k)) F"
      by (intro tendsto_intros always_eventually allI limit)
    show "\<forall>\<^sub>F x in F. x \<in> {n. Pg n}"
      using *(2) by simp
    show "uniform_limit {n. Pg n} (\<lambda>K n. \<Sum>k<K. a k n) (\<lambda>n. \<Sum>k. a k n) sequentially"
    proof (rule Weierstrass_m_test_ev)
      show "\<forall>\<^sub>F k in at_top. \<forall>n\<in>{n. Pg n}. norm (a k n) \<le> M k"
        using *(1) by eventually_elim (use *(3) in auto)
      show "summable M"
        by fact
    qed
  qed auto
qed

end