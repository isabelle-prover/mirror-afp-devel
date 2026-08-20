section \<open>Auxiliary material\<close>
theory Perron_Prerequisites
  imports "Dirichlet_Series.Dirichlet_Series_Analysis"
begin

subsection \<open>General analysis\<close>

lemma at_infinity_conv_filtercomap_norm_at_top: "at_infinity = filtercomap norm at_top"
  by (rule filter_eqI) (auto simp: eventually_at_infinity eventually_filtercomap_at_top_linorder)

lemma at_infinity_conv_filtercomap_abs_at_top:
  "at_infinity = filtercomap (abs :: real \<Rightarrow> real) at_top"
  unfolding at_infinity_conv_filtercomap_norm_at_top
  using real_norm_def by metis

lemma tendsto_dist_sandwich:
  assumes "eventually (\<lambda>n. dist (f n) c \<le> g n) F"
  assumes "(g \<longlongrightarrow> 0) F"
  shows   "(f \<longlongrightarrow> c) F"
proof -
  have "((\<lambda>n. dist (f n) c) \<longlongrightarrow> 0) F"
  proof (rule tendsto_sandwich)
    show "\<forall>\<^sub>F n in F. dist (f n) c \<ge> 0"
      by simp
    show "\<forall>\<^sub>F n in F. dist (f n) c \<le> g n"
      by fact
  qed (use assms(2) in auto)
  thus ?thesis
    using tendsto_dist_iff by blast
qed

lemma summation_by_parts:
  fixes f g :: "nat \<Rightarrow> 'a :: comm_ring_1"
  assumes "m \<le> n"
  shows "(\<Sum>k=m..n. f k * (g (Suc k) - g k)) =
           f (Suc n) * g (Suc n) - f m * g m - (\<Sum>k=m..n. g (Suc k) * (f (Suc k) - f k))"
proof -
  have "f (Suc n) * g (Suc n) - f m * g m - (\<Sum>k=m..n. g (Suc k) * (f (Suc k) - f k)) -
           (\<Sum>k=m..n. f k * (g (Suc k) - g k)) =
        (\<Sum>k=m..n. f k * g k) - f m * g m - ((\<Sum>k=m..n. f (Suc k) * g (Suc k)) - 
           f (Suc n) * g (Suc n))"
    by (simp add: sum_subtractf algebra_simps)
  also have "(\<Sum>k=m..n. f k * g k) = (\<Sum>k\<in>insert m {m<..n}. f k * g k)"
    using assms by (intro sum.cong) auto
  also have "\<dots> - f m * g m = (\<Sum>k\<in>{m<..n}. f k * g k)"
    by (subst sum.insert) auto
  also have "(\<Sum>k=m..n. f (Suc k) * g (Suc k)) = (\<Sum>k\<in>insert n {m..<n}. f (Suc k) * g (Suc k))"
    using assms by (intro sum.cong) auto
  also have "\<dots> - f (Suc n) * g (Suc n) = (\<Sum>k=m..<n. f (Suc k) * g (Suc k))"
    by (subst sum.insert) auto
  also have "\<dots> = (\<Sum>k\<in>{m<..n}. f k * g k)"
    by (rule sum.reindex_bij_witness[of _ "\<lambda>i. i - 1" "\<lambda>i. i + 1"]) auto
  finally show ?thesis
    by simp
qed

lemma bounded_normE:
  assumes "bounded A"
  obtains C where "C > c" "\<And>x. x \<in> A \<Longrightarrow> norm x < C"
proof -
  from assms obtain C' where C': "\<And>x. x \<in> A \<Longrightarrow> norm x \<le> C'"
    by (auto simp: bounded_iff)
  show ?thesis
    by (intro that[of "max C' c + 1"]) (auto simp: max_def dest: C')
qed

lemma norm_suminf_le':
  fixes f :: "nat \<Rightarrow> 'a :: banach"
  assumes "\<And>n. norm (f n) \<le> g n" "g sums A"
  shows   "norm (suminf f) \<le> A"
proof -
  have "norm (suminf f) \<le> suminf g"
    by (rule norm_suminf_le) (use assms in \<open>auto simp: sums_iff\<close>)
  thus ?thesis
    using assms by (simp add: sums_iff)
qed

lemma uniform_limit_compose':
  assumes "uniform_limit A f g F" and "h ` B \<subseteq> A"
  shows   "uniform_limit B (\<lambda>n x. f n (h x)) (\<lambda>x. g (h x)) F"
  unfolding uniform_limit_iff
proof safe
  fix e :: real
  assume e: "e > 0"
  from e and assms(1) have "\<forall>\<^sub>F n in F. \<forall>x\<in>A. dist (f n x) (g x) < e"
    by (auto simp: uniform_limit_iff)
  thus "\<forall>\<^sub>F n in F. \<forall>x\<in>B. dist (f n (h x)) (g (h x)) < e"
    by eventually_elim (use assms(2) in blast)
qed

subsection \<open>Complex analysis\<close>

lemma analytic_imp_contour_integrable:
  "f analytic_on path_image g \<Longrightarrow> valid_path g \<Longrightarrow> f contour_integrable_on g"
  using contour_integrable_holomorphic_simple[of f _ g]
  by (metis analytic_on_holomorphic)

lemma contour_integral_rectpath:
  assumes "f analytic_on path_image (rectpath a b)"
  shows   "contour_integral (rectpath a b) f =
             contour_integral (linepath a (Complex (Re b) (Im a))) f +
             contour_integral (linepath (Complex (Re b) (Im a)) b) f +
             contour_integral (linepath b (Complex (Re a) (Im b))) f +
             contour_integral (linepath (Complex (Re a) (Im b)) a) f"
proof -
  have *: "A \<subseteq> B \<union> C" if "(A :: complex set) \<subseteq> B \<or> A \<subseteq> C" for A B C
    using that by blast
  show ?thesis
  unfolding rectpath_def Let_def
  by (simp add: analytic_imp_contour_integrable[OF analytic_on_subset[OF assms]]
                rectpath_def Let_def path_image_join *)
qed

lemma contour_integral_bound_linepath':
    "\<lbrakk>f contour_integrable_on (linepath a b);
      0 \<le> B; \<And>x. x \<in> closed_segment a b \<Longrightarrow> norm(f x) \<le> B; c = norm (b - a)\<rbrakk>
     \<Longrightarrow> norm(contour_integral (linepath a b) f) \<le> B * c"
  using contour_integral_bound_linepath by metis

lemma contour_integral_linepath_same_Im:
  assumes "Im z = T" "Im z' = T" "Re z = a" "Re z' = b" "a < b"
  shows   "contour_integral (linepath z z') f =
           integral {a..b} (\<lambda>x. f (Complex x T))"
proof -
  have "contour_integral (((+) (\<i> * of_real T)) \<circ> linepath (of_real a) (of_real b)) f =
         contour_integral (linepath (of_real a) (of_real b)) (\<lambda>x. f (x + \<i> * of_real T))"
    by (subst contour_integral_translate) auto
  also have "\<dots> = integral {a..b} (\<lambda>x. f (complex_of_real x + \<i> * complex_of_real T))"
    by (subst contour_integral_linepath_Reals_eq) (use \<open>a < b\<close> in auto)
  also have "(\<lambda>x. complex_of_real x + \<i> * complex_of_real T) = (\<lambda>x. Complex x T)"
    by (auto simp: complex_eq_iff)
  also have "((+) (\<i> * of_real T)) \<circ> linepath (of_real a) (of_real b) = linepath z z'"
    using assms by (auto simp: fun_eq_iff complex_eq_iff algebra_simps linepath_def)
  finally show ?thesis .
qed

lemma contour_integral_linepath_same_Re:
  assumes "Re z = c" "Re z' = c" "Im z = a" "Im z' = b" "a < b"
  shows   "contour_integral (linepath z z') f =
           \<i> * integral {a..b} (\<lambda>x. f (Complex c x))"
proof -
  have zz': "z = Complex c a" "z' = Complex c b"
    using assms by (auto simp: complex_eq_iff)
  have "contour_integral (linepath z z') f =
         (z' - z) * integral {0..1} (\<lambda>x. f (linepath z z' x))"
    by (simp add: contour_integral_integral)
  also have "z' - z = \<i> * of_real (b - a)"
    by (simp add: zz' Complex_eq algebra_simps)
  also have "integral {0..1} (\<lambda>x. f (linepath z z' x)) =
             integral {0..1} (\<lambda>x. f (Complex c (linepath a b x)))"
    by (simp add: linepath_def Complex_eq scaleR_conv_of_real algebra_simps zz')
  also have "\<dots> = integral {0..(b - a) / (b - a)} (\<lambda>x. f (Complex c (a + (b - a) * x)))"
    using \<open>a < b\<close> by (simp add: algebra_simps linepath_def)
  also have "{0..(b - a) / (b - a)} = (\<lambda>x. x / (b - a)) ` {0..b - a}"
    using \<open>a < b\<close> by simp
  also have "integral \<dots> (\<lambda>x. f (Complex c (a + (b - a) * x))) =
             integral {a-a..b-a} (\<lambda>x. f (Complex c (x + a))) / of_real (b - a)"
    using \<open>a < b\<close> by (subst integral_stretch_real) (auto simp: scaleR_conv_of_real add_ac)
  also have "\<dots> = integral {a..b} (\<lambda>x. f (Complex c x)) / of_real (b - a)"
    by (subst integral_shift_real_ivl) (rule refl)
  finally show ?thesis
    using \<open>a < b\<close> by simp
qed

lemma continuous_on_Complex [continuous_intros]:
  assumes "continuous_on A f" "continuous_on A g"
  shows   "continuous_on A (\<lambda>x. Complex (f x) (g x))"
  unfolding Complex_eq by (intro continuous_intros assms)

lemma contour_integral_primitive':
  assumes "\<And>x. x \<in> S \<Longrightarrow> (f has_field_derivative f' x) (at x within S)"
      and "valid_path g" "path_image g \<subseteq> S" "pathfinish g = b" "pathstart g = a"
    shows "(f' has_contour_integral (f b - f a)) g"
  using contour_integral_primitive[OF assms(1-3)] assms(4,5) by simp

lemma fds_converges_0_imp_summable_fds_nth:
  assumes "fds_converges f 0"
  shows   "summable (fds_nth f)"
proof -
  from assms have "summable (\<lambda>n. fds_nth f n / nat_power n 0)"
    by (simp add: fds_converges_def)
  also have "eventually (\<lambda>n. fds_nth f n / nat_power n 0 = fds_nth f n) at_top"
    using eventually_gt_at_top[of 0] by eventually_elim auto
  hence "summable (\<lambda>n. fds_nth f n / nat_power n 0) \<longleftrightarrow> summable (\<lambda>n. fds_nth f n)"
    by (intro summable_cong)
  finally show ?thesis .
qed

lemma contour_integral_rmul: "contour_integral g (\<lambda>x. f x * c) = contour_integral g f * c"
proof (cases "c = 0")
  case [simp]: False
  show ?thesis
  proof (cases "f contour_integrable_on g")
    case True
    thus ?thesis
      by (simp add: contour_integral_unique has_contour_integral_integral has_contour_integral_rmul)
  next
    case False
    thus ?thesis
      using contour_integrable_rmul_iff not_integrable_contour_integral by force
  qed
qed auto

lemma contour_integral_lmul: "contour_integral g (\<lambda>x. c * f x) = c * contour_integral g f"
  by (subst (1 2) mult.commute) (rule contour_integral_rmul)

lemma contour_integral_divide: "contour_integral g (\<lambda>x. f x / c) = contour_integral g f / c"
  using contour_integral_rmul[of g f "inverse c"] by (simp add: field_simps)

(* TODO: generalise to any path *)
lemma uniform_limit_contour_integral_linepath:
  assumes u: "uniform_limit (path_image (linepath a b)) f g F"
  assumes c: "\<And>n. continuous_on (path_image (linepath a b)) (f n)"
  assumes [simp]: "F \<noteq> bot"
  obtains I J where
    "\<And>n. (f n has_contour_integral I n) (linepath a b)"
    "(g has_contour_integral J) (linepath a b)"
    "(I \<longlongrightarrow> J) F"
proof (rule uniform_limit_integral)
  note [continuous_intros] = continuous_on_compose2[OF c]

  show "uniform_limit {0..1} (\<lambda>x t. f x (linepath a b t) * (b - a))
          (\<lambda>t. g (linepath a b t) * (b - a)) F"
  proof (rule uniform_limit_intros)
    show "uniform_limit {0..1} (\<lambda>x t. f x (linepath a b t))
            (\<lambda>t. g (linepath a b t)) F"
      using u unfolding path_image_def by (rule uniform_limit_compose') auto
  qed

  show "continuous_on {0..1} (\<lambda>t. f n (linepath a b t) * (b - a))" for n
    by (intro continuous_intros; unfold path_image_def) auto

  fix I J
  assume I: "\<And>n. ((\<lambda>t. f n (linepath a b t) * (b - a)) has_integral I n) {0..1}"
     and J: "((\<lambda>t. g (linepath a b t) * (b - a)) has_integral J) {0..1}"
     and lim: "(I \<longlongrightarrow> J) F"
  show ?thesis
   by (rule that[of I J]) (use I J lim in \<open>auto simp: has_contour_integral\<close>)
qed auto

(* TODO: generalise to any path *)
lemma contour_integral_sums_linepath:
  assumes u: "uniform_limit (closed_segment a b) (\<lambda>N w. \<Sum>n<N. f n w) g sequentially"
  assumes c: "\<And>n. continuous_on (closed_segment a b) (f n)"
  obtains J where
    "(g has_contour_integral J) (linepath a b)"
    "(\<lambda>n. contour_integral (linepath a b) (f n)) sums J"
proof (rule uniform_limit_contour_integral_linepath)
  show "uniform_limit (path_image (linepath a b)) (\<lambda>N w. \<Sum>n<N. f n w) g sequentially"
    using u by simp
next
  show "continuous_on (path_image (linepath a b)) (\<lambda>w. \<Sum>n<N. f n w)" for N
    by (intro continuous_intros continuous_on_subset[OF c]) simp_all
next
  fix I J
  assume 1: "\<And>N. ((\<lambda>w. \<Sum>n<N. f n w) has_contour_integral I N) (linepath a b)"
  assume 2: "(g has_contour_integral J) (linepath a b)" and 3: "(I \<longlongrightarrow> J) sequentially"
  have 4: "I = (\<lambda>N. (\<Sum>n<N. contour_integral (linepath a b) (f n)))"
  proof
    fix N :: nat
    have "f n contour_integrable_on (linepath a b)" for n
      by (intro contour_integrable_continuous_linepath assms)
    hence "((\<lambda>w. \<Sum>n<N. f n w) has_contour_integral
             (\<Sum>n<N. contour_integral (linepath a b) (f n))) (linepath a b)"
      using c by (intro has_contour_integral_sum) (simp_all add: has_contour_integral_integral)
    with 1[of N] show "I N = (\<Sum>n<N. contour_integral (linepath a b) (f n))"
      using contour_integral_unique by metis
  qed
  have 5: "(\<lambda>n. contour_integral (linepath a b) (f n)) sums J"
    using 1 2 3 4 unfolding sums_def by blast
  from that[OF 2 5] show ?thesis .
qed auto


subsection \<open>Dirichlet series\<close>

lemma uniform_limit_eval_fds:
  fixes f :: "'a :: dirichlet_series fds"
  assumes "compact B" "\<And>z. z \<in> B \<Longrightarrow> conv_abscissa f < ereal (z \<bullet> 1)"
  shows   "uniform_limit B (\<lambda>N z. \<Sum>n\<le>N. fds_nth f n / nat_power n z) (eval_fds f) sequentially"
proof -
  define g where "g = (\<lambda>N z. \<Sum>n\<le>N. fds_nth f n / nat_power n z)"
  from assms have "uniformly_convergent_on B g"
    unfolding g_def by (rule uniformly_convergent_eval_fds)
  then obtain l where l: "uniform_limit B g l sequentially"
    unfolding uniformly_convergent_on_def by blast
  also have "?this \<longleftrightarrow> uniform_limit B g (eval_fds f) sequentially"
  proof (intro uniform_limit_cong)
    fix z assume z: "z \<in> B"
    from tendsto_uniform_limitI[OF l z] have "(\<lambda>y. g y z) \<longlonglongrightarrow> l z" .
    hence "(\<lambda>n. fds_nth f n / nat_power n z) sums l z"
      by (simp add: g_def sums_def_le)
    thus "l z = eval_fds f z"
      by (simp add: eval_fds_def sums_iff)
  qed auto
  finally show ?thesis
    by (simp add: g_def)
qed

lemma uniform_limit_eval_fds':
  fixes f :: "'a :: dirichlet_series fds"
  assumes "compact B" "\<And>z. z \<in> B \<Longrightarrow> conv_abscissa f < ereal (z \<bullet> 1)"
  shows   "uniform_limit B (\<lambda>N z. \<Sum>n<N. fds_nth f n / nat_power n z) (eval_fds f) sequentially"
proof -
  have "uniform_limit B (\<lambda>N z. \<Sum>n\<le>N. fds_nth f n / nat_power n z) (eval_fds f) sequentially"
    by (rule uniform_limit_eval_fds) (use assms in auto)
  also have "(\<lambda>N z. \<Sum>n\<le>N. fds_nth f n / nat_power n z) =
               (\<lambda>N z. \<Sum>n<Suc N. fds_nth f n / nat_power n z)"
    by (intro ext sum.cong) auto
  finally have "uniform_limit B (\<lambda>N z. \<Sum>n<N. fds_nth f n / nat_power n z) 
                  (eval_fds f) (filtermap Suc sequentially)"
    by (simp add: uniform_limit_iff eventually_filtermap)
  also have "filtermap Suc sequentially = sequentially"
    by (simp add: eventually_filtermap filter_eq_iff)
  finally show ?thesis .
qed

lemma conv_abscissa_shift [simp]:
  "conv_abscissa (fds_shift c f) = conv_abscissa (f :: 'a :: dirichlet_series fds) + c \<bullet> 1"
proof -
  have "conv_abscissa (fds_shift c f) \<le> conv_abscissa f + c \<bullet> 1" for c :: 'a and f
  proof (rule conv_abscissa_leI)
    fix d assume "conv_abscissa f + c \<bullet> 1 < ereal d"
    hence "conv_abscissa f < ereal (d - c \<bullet> 1)" by (cases "conv_abscissa f") auto
    hence "fds_converges (fds_shift c f) (of_real d)"
      by (auto intro!: fds_converges_shift fds_converges simp: algebra_simps)
    thus "\<exists>s. s \<bullet> 1 = d \<and> fds_converges (fds_shift c f) s"
      by (auto intro!: exI[of _ "of_real d"])
  qed
  note * = this[of c f] this[of "-c" "fds_shift c f"]
  show ?thesis by (cases "conv_abscissa (fds_shift c f)"; cases "conv_abscissa f")
                  (insert *, auto intro!: antisym)
qed

(* TODO Move *)
lemma abs_conv_abscissa_fds_zeta [simp]:
  "abs_conv_abscissa (fds_zeta :: 'a :: dirichlet_series fds) = 1"
proof -
  have "abs_conv_abscissa (fds_zeta :: 'a fds) = Inf (ereal ` (\<lambda>x. x \<bullet> 1) ` {s::'a. 1 < s \<bullet> 1})"
    by (simp add: abs_conv_abscissa_def image_image o_def)
  also have "(\<lambda>x. x \<bullet> 1) ` {s::'a. 1 < s \<bullet> 1} = {1<..}"
  proof safe
    fix x :: real
    assume "x > 1"
    show "x \<in> (\<lambda>x. x \<bullet> 1) ` {s::'a. 1 < s \<bullet> 1}"
      by (rule image_eqI[of _ _ "of_real x"]) (use \<open>x > 1\<close> in auto)
  qed
  also have "ereal ` {1<..} = {1<..<\<infinity>}"
  proof safe
    fix x :: ereal assume x: "x \<in> {1<..<\<infinity>}"
    show "x \<in> ereal ` {1<..}"
      using x by (cases x) (auto simp: image_def)
  qed auto
  also have "Inf \<dots> = 1"
    by simp
  finally show ?thesis .
qed

end