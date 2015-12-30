theory Higher_Derivative
imports "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis" "../ODE_Auxiliarities"
begin

subsection {* Approachability (for differentiability) *}

text {* TODO: move to @{thm frechet_derivative_unique_within} *}
definition approachable_at::"('a::euclidean_space) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "approachable_at x G = (\<forall>i\<in>Basis. \<forall>e>0. \<exists>d. 0 < abs(d) \<and> abs(d) < e \<and> (x + d *\<^sub>R i) \<in> G)"

lemma frechet_derivative_unique_within_approach:
  assumes "approachable_at x s"
  assumes "(f has_derivative f') (at x within s)"
  assumes "(f has_derivative f'') (at x within s)"
  shows "f' = f''"
  using frechet_derivative_unique_within[OF assms(2,3)] assms(1)
  by (simp add: approachable_at_def)

lemma frechet_derivative_within:
  shows "approachable_at x G \<Longrightarrow> (f has_derivative f') (at x within G) \<Longrightarrow>
    (f' = frechet_derivative f (at x within G))"
  by (rule frechet_derivative_unique_within)
    (auto simp: frechet_derivative_works[THEN sym] approachable_at_def intro: differentiableI)

lemma approachableI:
  assumes "\<And>i e. i \<in> Basis \<Longrightarrow> e > 0 \<Longrightarrow> \<exists>d. 0 < abs(d) \<and> abs(d) < e \<and> (x + d *\<^sub>R i) \<in> G"
  shows "approachable_at x G"
  using assms by (auto simp: approachable_at_def)

lemma approachableE:
  assumes "approachable_at x G"
  assumes "i \<in> Basis" "e > 0"
  obtains d where "0 < abs d" "abs d < e" "x + d *\<^sub>R i \<in> G"
  using assms by (auto simp: approachable_at_def)

lemma open_approachable[intro, simp]:
  assumes "open G" "x \<in> G"
  shows "approachable_at x G"
proof (rule approachableI)
  fix i::'a and e::real
  assume "i \<in> Basis" "e > 0"
  from assms `x \<in> G`
  obtain d' where d': "d' > 0" "\<And>y. dist y x < d' \<Longrightarrow> y \<in> G" using open_dist by blast
  def d \<equiv> "(min (d'/(norm i+1)) e)/2"
  have "d \<ge> 0" using `e > 0` `d' > 0`
    by (auto simp: d_def)
  have "dist (x + d *\<^sub>R i) x = norm (d *\<^sub>R i)" by (simp add: dist_norm)
  also have "\<dots> \<le> d * (norm i + 1)" using `d \<ge> 0` by (auto intro!: mult_left_mono)
  also have "\<dots> < d'" using `0 < d'` `0 < e`
    by (auto simp add: pos_divide_less_eq pos_less_divide_eq[symmetric] add_nonneg_pos d_def
      add_nonneg_eq_0_iff intro: min.strict_coboundedI1)
  finally have "x + d *\<^sub>R i \<in> G" by (rule d')
  moreover have "0 < abs d" using `d \<ge> 0` `d' > 0` `e > 0`
    by (auto simp add: d_def intro!: divide_pos_pos add_nonneg_pos)
  moreover have "abs d < e" using `0 < d'` `0 < e` `0 \<le> d`
    by (auto simp: d_def)
  ultimately show "\<exists>d. 0 < \<bar>d\<bar> \<and> \<bar>d\<bar> < e \<and> x + d *\<^sub>R i \<in> G" by blast
qed

lemma approachable_at_cball:
  assumes "e > 0"
  shows "approachable_at x (cball x e)"
  using assms
  apply (intro approachableI)
  apply (rule_tac x = "(min (ea/2) e)" in exI)
  apply (auto simp: dist_norm)
  done

text {* TODO: this is @{thm frechet_derivative_unique_within_closed_interval} *}
lemma closed_ivl_approachable[intro, simp]:
  fixes a b::"'a::ordered_euclidean_space"
  assumes lt: "\<And>i. i \<in> Basis \<Longrightarrow> a\<bullet>i < b\<bullet>i" and x: "x \<in> {a .. b}"
  shows "approachable_at x {a .. b}"
proof (rule approachableI)
  fix e::real and i :: 'a assume "e>0" and i:"i\<in>Basis"
  thus "\<exists>d. 0 < \<bar>d\<bar> \<and> \<bar>d\<bar> < e \<and> x + d *\<^sub>R i \<in> {a .. b}"
  proof(cases "x\<bullet>i=a\<bullet>i")
    case True thus ?thesis
      apply(rule_tac x="(min (b\<bullet>i - a\<bullet>i)  e) / 2" in exI)
      using lt[OF i] and `e>0` and x
      unfolding interval_cbox mem_box
      using i by (auto simp add: field_simps inner_simps inner_Basis)
  next
    note * = x[unfolded interval_cbox mem_box, THEN bspec, OF i]
    case False moreover have "a \<bullet> i < x \<bullet> i" using False * by auto
    moreover {
      have "a \<bullet> i * 2 + min (x \<bullet> i - a \<bullet> i) e \<le> a\<bullet>i *2 + x\<bullet>i - a\<bullet>i"
        by auto
      also have "\<dots> = a\<bullet>i + x\<bullet>i" by auto
      also have "\<dots> \<le> 2 * (x\<bullet>i)" using * by auto
      finally have "a \<bullet> i * 2 + min (x \<bullet> i - a \<bullet> i) e \<le> x \<bullet> i * 2" by auto
    }
    moreover have "min (x \<bullet> i - a \<bullet> i) e \<ge> 0" using * and `e>0` by auto
    hence "x \<bullet> i * 2 \<le> b \<bullet> i * 2 + min (x \<bullet> i - a \<bullet> i) e" using * by auto
    ultimately show ?thesis
      apply(rule_tac x="- (min (x\<bullet>i - a\<bullet>i) e) / 2" in exI)
      using lt[OF i] and `e>0` and x
      unfolding interval_cbox mem_box
      using i by (auto simp add: field_simps inner_simps inner_Basis)
  qed
qed

lemma approachable_product[intro]:
  "x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> approachable_at x X \<Longrightarrow> approachable_at y Y \<Longrightarrow>
    approachable_at (x, y) (X \<times> Y)"
  by (auto simp: Basis_prod_def approachable_at_def)


subsection {* Higher directional derivatives *}

lemmas norm_triangle_sub_le = order_trans[OF norm_triangle_ineq4]

locale approachable_on = fixes G
  assumes approachable: "\<And>a. a \<in> G \<Longrightarrow> approachable_at a G"

locale higher_derivative = approachable_on G for G::"'a::euclidean_space set" +
  fixes f::"'a\<Rightarrow>'b::real_normed_vector" and n
  fixes Ds::"'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes Ds_0[derivative_intros]: "a \<in> G \<Longrightarrow> (f has_derivative Ds [] a) (at a within G)"
  assumes Ds_Suc[derivative_intros]:
    "a \<in> G \<Longrightarrow> length ds < n \<Longrightarrow> ((\<lambda>a. Ds ds a d) has_derivative (\<lambda>i. Ds (d#ds) a i)) (at a within G)"
begin

lemma linear_Ds: "\<And>a. n \<ge> length ds \<Longrightarrow> a \<in> G \<Longrightarrow> linear (Ds ds a)"
  by (cases ds) (auto intro!: has_derivative_linear derivative_intros)

end

lemma continuous_imp_tendsto_compose:
  assumes "continuous (at x0) f"
    and "(g \<longlongrightarrow> x0) F"
  shows "((\<lambda>x. f (g x)) \<longlongrightarrow> (f x0)) F"
  using tendsto_compose assms
  by (auto simp: continuous_at)

lemma convex_left_scaling:
  assumes "convex s"
  shows"convex ((\<lambda>x. x *\<^sub>R a) ` s)"
proof (rule convexI, safe)
  fix u v x y::real
  assume "u + v = 1" "0 \<le> u" "0 \<le> v" "x \<in> s" "y \<in> s"
  with assms show "u *\<^sub>R (x *\<^sub>R a) + v *\<^sub>R (y *\<^sub>R a) \<in> ((\<lambda>x. x *\<^sub>R a) ` s)"
    by (auto dest!: mem_convex_alt[of s x y u v] intro!: image_eqI[where x="u * x + v * y"]
      convex_bound_le simp: algebra_simps)
qed

lemma
  differentiable_bound_line:
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "\<And>t. t \<in> {0..1} \<Longrightarrow> x0 + t *\<^sub>R a \<in> G"
  assumes f': "\<And>x. x \<in> G \<Longrightarrow> (f has_derivative f' x) (at x within G)"
  assumes B: "\<forall>x\<in>{0..1}. onorm (f' (x0 + x *\<^sub>R a)) \<le> B"
  shows "norm (f (x0 + a) - f x0) \<le> norm a * B"
proof -
  let ?G = "(\<lambda>x. x0 + x *\<^sub>R a) ` {0..1}"
  have "?G = op + x0 ` (\<lambda>x. x *\<^sub>R a) ` {0..1}" by auto
  also have "convex \<dots>" by (intro convex_translation convex_left_scaling convex_closed_interval)
  finally have "convex ?G" .
  moreover have "?G \<subseteq> G" "x0 \<in> ?G" "x0 + a \<in> ?G" using assms by (auto intro: image_eqI[where x=1])
  ultimately show ?thesis
    using has_derivative_subset[OF f' `?G \<subseteq> G`] B
      differentiable_bound[of "(\<lambda>x. x0 + x *\<^sub>R a) ` {0..1}" f f' B "x0 + a" x0]
    by (auto simp: ac_simps)
qed

lemma differentiable_bound_derivative:
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "\<And>t. t \<in> {0..1} \<Longrightarrow> a + t *\<^sub>R (b - a) \<in> S"
  assumes f'[derivative_intros]: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  assumes B: "\<forall>x\<in>S. onorm (f' x - f' x0) \<le> B"
  assumes "x0 \<in> S"
  shows "norm (f b - f a - f' x0 (b - a)) \<le> norm (b - a) * B"
proof -
  def g \<equiv> "\<lambda>x. f x - f' x0 x"
  have g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative (\<lambda>i. f' x i - f' x0 i)) (at x within S)"
    unfolding g_def using assms
    by (auto intro!: derivative_eq_intros bounded_linear.has_derivative[OF has_derivative_bounded_linear, OF f'])
  from B have B: "\<forall>x\<in>{0..1}. onorm (\<lambda>i. f' (a + x *\<^sub>R (b - a)) i - f' x0 i) \<le> B"
     using assms by (auto simp: fun_diff_def)
  from differentiable_bound_line[OF assms(1) g B] `x0 \<in> S`
  show ?thesis by (simp add: g_def field_simps linear_sub[OF has_derivative_linear[OF f']])
qed

locale higher_continuous_derivative = higher_derivative +
  assumes continuous_Ds:
    "a \<in> G \<Longrightarrow> length ds \<le> n \<Longrightarrow> continuous (at a within G) (\<lambda>a. Ds ds a y)"

locale second_derivative =
  approachable_on G for G +
  fixes f::"'a::euclidean_space\<Rightarrow>'b::euclidean_space" and f' f''
  assumes first_fderiv[derivative_intros]: "\<And>a. a \<in> G \<Longrightarrow> (f has_derivative f' a) (at a within G)"
  assumes second_fderiv[derivative_intros]: "\<And>a i. a \<in> G \<Longrightarrow> ((\<lambda>a. f' a i) has_derivative f'' a i) (at a within G)"
begin

lemma continuous_on_first: "\<And>i. continuous_on G (\<lambda>a. f' a i)"
  by (metis (full_types) Derivative.differentiableI differentiable_imp_continuous_on
    differentiable_on_def second_fderiv)

lemmas linear_first = has_derivative_linear[OF first_fderiv]

lemmas first_linear_simps [simp] =
  linear_add[OF linear_first]
  linear_sub[OF linear_first]
  linear_neg[OF linear_first]
  linear_cmul[OF linear_first]
  linear_0[OF linear_first]
  linear_setsum[OF linear_first]

lemma second_unique:
  "((\<lambda>a. f' a i) has_derivative F'') (at a within G) \<Longrightarrow> a \<in> G \<Longrightarrow> f'' a i = F''"
  using frechet_derivative_unique_within_approach[OF approachable _ second_fderiv] by simp

lemma bilinear_second: assumes "a \<in> G" shows "bilinear (f'' a)"
  unfolding bilinear_def
proof safe
  fix j
  show "linear (f'' a j)" by (rule has_derivative_linear[OF second_fderiv, OF `a \<in> G`])
  have "\<And>i1 i2. (\<lambda>j. f'' a (i1 + i2) j) = (\<lambda>j. f'' a i1 j + f'' a i2 j)"
    using `a \<in> G`  by (intro second_unique[OF has_derivative_transform]) (auto intro!: derivative_intros)
  moreover have "\<And>c i1. f'' a (c *\<^sub>R i1) = (\<lambda>j. c *\<^sub>R f'' a i1 j)"
    using `a \<in> G`  by (intro second_unique[OF has_derivative_transform]) (auto intro!: derivative_intros)
  ultimately show "linear (\<lambda>i. f'' a i j)" by (intro linearI) simp_all
qed

lemmas second_bilinear_simps[simp] =
  bilinear_ladd[OF bilinear_second]
  bilinear_radd[OF bilinear_second]
  bilinear_lsub[OF bilinear_second]
  bilinear_rsub[OF bilinear_second]
  bilinear_lneg[OF bilinear_second]
  bilinear_rneg[OF bilinear_second]
  bilinear_lmul[OF bilinear_second]
  bilinear_rmul[OF bilinear_second]
  bilinear_rzero[OF bilinear_second]
  bilinear_lzero[OF bilinear_second]
  bilinear_setsum[OF bilinear_second]

lemma symmetric_second_derivative_aux:
  fixes i j::"'a::euclidean_space"
  assumes "i \<noteq> j" "i \<noteq> 0" "j \<noteq> 0"
  assumes "a \<in> G"
  assumes "\<And>s t. s \<in> {0..1} \<Longrightarrow> t \<in> {0..1} \<Longrightarrow> a + s *\<^sub>R i + t *\<^sub>R j \<in> G"
  shows "f'' a i j = f'' a j i"
proof -
  let ?F = "at_right (0::real)"
  def B \<equiv> "\<lambda>i j. {a + s *\<^sub>R i + t *\<^sub>R j |s t. s \<in> {0..1} \<and> t \<in> {0..1}}"
  have "B i j \<subseteq> G" using assms by (auto simp: B_def)
  {
    fix e::real and i j::'a
    assume "e > 0"
    assume "i \<noteq> j" "i \<noteq> 0" "j \<noteq> 0"
    assume "B i j \<subseteq> G"
    let ?ij' = "\<lambda>s t. \<lambda>u. a + (s * u) *\<^sub>R i + (t * u) *\<^sub>R j"
    let ?ij = "\<lambda>t. \<lambda>u. a + (t * u) *\<^sub>R i + u *\<^sub>R j"
    let ?i = "\<lambda>t. \<lambda>u. a + (t * u) *\<^sub>R i"
    let ?g = "\<lambda>u t. f (?ij t u) - f (?i t u)"
    have filter_ij'I: "\<And>P. P a \<Longrightarrow> eventually P (at a within G) \<Longrightarrow>
      eventually (\<lambda>x. \<forall>s\<in>{0..1}. \<forall>t\<in>{0..1}. P (?ij' s t x)) ?F"
    proof -
      fix P
      assume "P a"
      assume "eventually P (at a within G)"
      hence "eventually P (at a within B i j)" by (rule filter_leD[OF at_le[OF `B i j \<subseteq> G`]])
      then obtain d where d: "d > 0" and "\<And>x d2. x \<in> B i j \<Longrightarrow> x \<noteq> a \<Longrightarrow> dist x a < d \<Longrightarrow> P x"
        by (auto simp: eventually_at)
      with `P a` have P: "\<And>x d2. x \<in> B i j \<Longrightarrow> dist x a < d \<Longrightarrow> P x" by (case_tac "x = a") auto
      let ?d = "min (min (d/norm i) (d/norm j) / 2) 1"
      show "eventually (\<lambda>x. \<forall>s\<in>{0..1}. \<forall>t\<in>{0..1}. P (?ij' s t x)) (at_right 0)"
        unfolding eventually_at
      proof (rule exI[where x="?d"], safe)
        show "0 < ?d" using `0 < d` `i \<noteq> 0` `j \<noteq> 0` by simp
        fix x s t :: real assume *: "s \<in> {0..1}" "t \<in> {0..1}" "0 < x" "dist x 0 < ?d"
        show "P (?ij' s t x)"
        proof (rule P)
          have "\<And>x y::real. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> x * y \<in> {0..1}"
            by (auto intro!: order_trans[OF mult_left_le_one_le])
          hence "s * x \<in> {0..1}" "t * x \<in> {0..1}" using * by (auto simp: dist_norm)
          thus "?ij' s t x \<in> B i j" by (auto simp: B_def)
          have "norm (s *\<^sub>R x *\<^sub>R i + t *\<^sub>R x *\<^sub>R j) \<le> norm (s *\<^sub>R x *\<^sub>R i) + norm (t *\<^sub>R x *\<^sub>R j)"
            by (rule norm_triangle_ineq)
          also have "\<dots> < d / 2 + d / 2" using * `i \<noteq> 0` `j \<noteq> 0`
            by (intro add_strict_mono) (auto simp: ac_simps dist_norm
              pos_less_divide_eq le_less_trans[OF mult_left_le_one_le])
          finally show "dist (?ij' s t x) a < d" by (simp add: dist_norm)
        qed
      qed
    qed
    {
      fix P
      assume "P a" "eventually P (at a within G)"
      from filter_ij'I[OF this] have "eventually (\<lambda>x. \<forall>t\<in>{0..1}. P (?ij t x)) ?F"
        by eventually_elim (force dest: bspec[where x=1])
    } note filter_ijI = this
    {
      fix P assume "P a" "eventually P (at a within G)"
      from filter_ij'I[OF this] have "eventually (\<lambda>x. \<forall>t\<in>{0..1}. P (?i t x)) ?F"
        by eventually_elim force
    } note filter_iI = this
    {
      from second_fderiv[OF `a \<in> G`, of i, simplified has_derivative_iff_norm, THEN conjunct2,
        THEN tendstoD, OF `0 < e`]
      have "eventually (\<lambda>x. norm (f' x i - f' a i - f'' a i (x - a)) / norm (x - a) \<le> e)
          (at a within G)"
        by eventually_elim (simp add: dist_norm)
      from filter_ijI[OF _ this] filter_iI[OF _ this] `0 < e`
      have
        "eventually (\<lambda>ij. \<forall>t\<in>{0..1}. norm (f' (?ij t ij) i - f' a i - f'' a i (?ij t ij - a)) /
          norm (?ij t ij - a) \<le> e) ?F"
        "eventually (\<lambda>ij. \<forall>t\<in>{0..1}. norm (f' (?i t ij) i - f' a i - f'' a i (?i t ij - a)) /
          norm (?i t ij - a) \<le> e) ?F"
        by auto
      moreover
      have "eventually (\<lambda>x. x \<in> G) (at a within G)" unfolding eventually_at_filter by simp
      hence eventually_in_ij: "eventually (\<lambda>x. \<forall>t\<in>{0..1}. ?ij t x \<in> G) ?F" and
        eventually_in_i: "eventually (\<lambda>x. \<forall>t\<in>{0..1}. ?i t x \<in> G) ?F"
        using `a \<in> G` by (auto dest: filter_ijI filter_iI)
      ultimately
      have "eventually (\<lambda>u. norm (?g u 1 - ?g u 0 - (u * u) *\<^sub>R f'' a i j) \<le>
          u * u * e * (2 * norm i + 3 * norm j)) ?F"
      proof eventually_elim
        case (elim u)
        hence ijsub: "(\<lambda>t. ?ij t u) ` {0..1} \<subseteq> G" and isub: "(\<lambda>t. ?i t u) ` {0..1} \<subseteq> G" by auto
        note has_derivative_subset[OF _ ijsub, derivative_intros]
        note has_derivative_subset[OF _ isub, derivative_intros]
        let ?g' = "\<lambda>t. (\<lambda>ua. u *\<^sub>R ua *\<^sub>R (f' (?ij t u) i - (f' (?i t u) i)))"
        {
          fix t::real assume "t \<in> {0..1}"
          with elim have linear_f': "\<And>c x. f' (?ij t u) (c *\<^sub>R x) = c *\<^sub>R f' (?ij t u) x"
              "\<And>c x. f' (?i t u) (c *\<^sub>R x) = c *\<^sub>R f' (?i t u) x"
            using linear_cmul[OF has_derivative_linear, OF first_fderiv] by auto
          have "((?g u) has_derivative ?g' t) (at t within {0..1})"
            using elim `t \<in> {0..1}`
            by (auto intro!: derivative_eq_intros has_derivative_in_compose[of  "\<lambda>t. ?ij t u" _ _ _ f]
                has_derivative_in_compose[of  "\<lambda>t. ?i t u" _ _ _ f]
              simp: linear_f' scaleR_diff_right mult.commute)
        } note g' = this
        from elim(1) `i \<noteq> 0` `j \<noteq> 0` `0 < e` have f'ij: "\<And>t. t \<in> {0..1} \<Longrightarrow>
            norm (f' (a + (t * u) *\<^sub>R i + u *\<^sub>R j) i - f' a i - f'' a i ((t * u) *\<^sub>R i + u *\<^sub>R j)) \<le>
            e * norm ((t * u) *\<^sub>R i + u *\<^sub>R j)"
          using  linear_0[OF has_derivative_linear, OF second_fderiv, OF `a \<in> G`]
          by (case_tac "u *\<^sub>R j + (t * u) *\<^sub>R i = 0") (auto simp: field_simps
            simp del: pos_divide_le_eq simp add: pos_divide_le_eq[symmetric])
        from elim(2) have f'i: "\<And>t. t \<in> {0..1} \<Longrightarrow> norm (f' (a + (t * u) *\<^sub>R i) i - f' a i -
          f'' a i ((t * u) *\<^sub>R i)) \<le> e * abs (t * u) * norm i"
          using `i \<noteq> 0` `j \<noteq> 0` linear_0[OF has_derivative_linear, OF second_fderiv, OF `a \<in> G`]
          by (case_tac "t * u = 0") (auto simp: field_simps simp del: pos_divide_le_eq
            simp add: pos_divide_le_eq[symmetric])
        have "norm (?g u 1 - ?g u 0 - (u * u) *\<^sub>R f'' a i j) =
          norm ((?g u 1 - ?g u 0 - u *\<^sub>R (f' (a + u *\<^sub>R j) i - (f' a i)))
            + u *\<^sub>R (f' (a + u *\<^sub>R j) i - f' a i - u *\<^sub>R f'' a i j))"
            (is "_ = norm (?g10 + ?f'i)")
          by (simp add: algebra_simps linear_cmul[OF has_derivative_linear, OF second_fderiv,
              OF `a \<in> G`]
            linear_add[OF has_derivative_linear, OF second_fderiv, OF `a \<in> G`])
        also have "\<dots> \<le> norm ?g10 + norm ?f'i"
          by (blast intro: order_trans add_mono norm_triangle_le)
        also
        have "0 \<in> {0..1::real}" by simp
        have "\<forall>t \<in> {0..1}. onorm ((\<lambda>ua. (u * ua) *\<^sub>R (f' (?ij t u) i - f' (?i t u) i)) -
              (\<lambda>ua. (u * ua) *\<^sub>R (f' (a + u *\<^sub>R j) i - f' a i)))
            \<le> 2 * u * u * e * (norm i + norm j)" (is "\<forall>t \<in> _. onorm (?d t) \<le> _")
        proof
          fix t::real assume "t \<in> {0..1}"
          show "onorm (?d t) \<le> 2 * u * u * e * (norm i + norm j)"
          proof (rule onorm_le)
            fix x
            have "norm (?d t x) =
                norm ((u * x) *\<^sub>R (f' (?ij t u) i - f' (?i t u) i - f' (a + u *\<^sub>R j) i + f' a i))"
              by (simp add: algebra_simps)
            also have "\<dots> =
                abs (u * x) * norm (f' (?ij t u) i - f' (?i t u) i - f' (a + u *\<^sub>R j) i + f' a i)"
              by simp
            also have "\<dots> = abs (u * x) * norm (
                 f' (?ij t u) i - f' a i - f'' a i ((t * u) *\<^sub>R i + u *\<^sub>R j)
               - (f' (?i t u) i - f' a i - f'' a i ((t * u) *\<^sub>R i))
               - (f' (a + u *\<^sub>R j) i - f' a i - f'' a i (u *\<^sub>R j)))"
               (is "_ = _ * norm (?dij - ?di - ?dj)")
              using `a \<in> G` by (simp add: algebra_simps)
            also have "\<dots> \<le> abs (u * x) * (norm ?dij + norm ?di + norm ?dj)"
              by (rule mult_left_mono[OF _ abs_ge_zero]) norm
            also have "\<dots> \<le> abs (u * x) *
              (e * norm ((t * u) *\<^sub>R i + u *\<^sub>R j) + e * abs (t * u) * norm i + e * (\<bar>u\<bar> * norm j))"
              using f'ij f'i f'ij[OF `0 \<in> {0..1}`] `t \<in> {0..1}`
              by (auto intro!: add_mono mult_left_mono)
            also have "\<dots> = abs u * abs x * abs u *
              (e * norm (t *\<^sub>R i + j) + e * norm (t *\<^sub>R i) + e * (norm j))"
              by (simp add: algebra_simps norm_scaleR[symmetric] abs_mult del: norm_scaleR)
            also have "\<dots> =
                u * u * abs x * (e * norm (t *\<^sub>R i + j) + e * norm (t *\<^sub>R i) + e * (norm j))"
              by (simp add: ac_simps)
            also have "\<dots> = u * u * e * abs x * (norm (t *\<^sub>R i + j) + norm (t *\<^sub>R i) + norm j)"
              by (simp add: algebra_simps)
            also have "\<dots> \<le> u * u * e * abs x * ((norm (1 *\<^sub>R i) + norm j) + norm (1 *\<^sub>R i) + norm j)"
              using `t \<in> {0..1}` `0 < e`
              by (intro mult_left_mono add_mono) (auto intro!: norm_triangle_le add_right_mono
                mult_left_le_one_le zero_le_square)
            finally show "norm (?d t x) \<le> 2 * u * u * e * (norm i + norm j) * norm x"
              by (simp add: ac_simps)
          qed
        qed
        with differentiable_bound_derivative[where f="?g u" and f'="?g'", of 0 1 _ 0, OF _ g']
        have "norm ?g10 \<le> 2 * u * u * e * (norm i + norm j)" by simp
        also have "norm ?f'i \<le> abs u *
          norm ((f' (a + (u) *\<^sub>R j) i - f' a i - f'' a i ((u) *\<^sub>R j)))"
          using linear_cmul[OF has_derivative_linear, OF second_fderiv, OF `a \<in> G`]
          by simp
        also have "\<dots> \<le> abs u * (e * norm ((u) *\<^sub>R j))"
          using f'ij[OF `0 \<in> {0..1}`] by (auto intro: mult_left_mono)
        also have "\<dots> = u * u * e * norm j" by (simp add: algebra_simps abs_mult)
        finally show ?case by (simp add: algebra_simps)
      qed
    }
  } note wlog = this
  {
    fix e t::real
    assume "0 < e"
    have "B i j = B j i" using `i \<noteq> j` by (force simp: B_def)+
    with assms `B i j \<subseteq> G` have "j \<noteq> i" "B j i \<subseteq> G" by (auto simp:)
    from wlog[OF `0 < e` `i \<noteq> j` `i \<noteq> 0` `j \<noteq> 0` `B i j \<subseteq> G`]
         wlog[OF `0 < e` `j \<noteq> i` `j \<noteq> 0` `i \<noteq> 0` `B j i \<subseteq> G`]
    have "eventually (\<lambda>u. norm ((u * u) *\<^sub>R f'' a i j - (u * u) *\<^sub>R f'' a j i)
         \<le> u * u * e * (5 * norm j + 5 * norm i)) ?F"
    proof eventually_elim
      case (elim u)
      have "norm ((u * u) *\<^sub>R f'' a i j - (u * u) *\<^sub>R f'' a j i) =
        norm (f (a + u *\<^sub>R j + u *\<^sub>R i) - f (a + u *\<^sub>R j) -
         (f (a + u *\<^sub>R i) - f a) - (u * u) *\<^sub>R f'' a j i
         - (f (a + u *\<^sub>R i + u *\<^sub>R j) - f (a + u *\<^sub>R i) -
         (f (a + u *\<^sub>R j) - f a) -
         (u * u) *\<^sub>R f'' a i j))" by (simp add: field_simps)
      also have "\<dots> \<le> u * u * e * (2 * norm j + 3 * norm i) + u * u * e * (3 * norm j + 2 * norm i)"
        using elim by (intro norm_triangle_sub_le) (auto simp: ac_simps intro: add_mono)
      finally show ?case by (simp add: algebra_simps)
    qed
    hence "eventually (\<lambda>u. norm ((u * u) *\<^sub>R (f'' a i j - f'' a j i)) \<le>
        u * u * e * (5 * norm j + 5 * norm i)) ?F"
      by (simp add: algebra_simps)
    hence "eventually (\<lambda>u. (u * u) * norm ((f'' a i j - f'' a j i)) \<le>
        (u * u) * (e * (5 * norm j + 5 * norm i))) ?F"
      by (simp add: ac_simps)
    hence "eventually (\<lambda>u. norm ((f'' a i j - f'' a j i)) \<le> e * (5 * norm j + 5 * norm i)) ?F"
      unfolding mult_le_cancel_left eventually_at_filter
      by eventually_elim auto
    hence "norm (f'' a i j - f'' a j i) \<le> e * (5 * norm j + 5 * norm i)"
      unfolding eventually_at
      apply safe
      apply (drule_tac x="d/2" in bspec)
      apply (auto simp add: dist_norm)
      done
  } note e' = this
  {
    fix e::real assume "0 < e"
    let ?e = "e/2/(5 * norm j + 5 * norm i)"
    have "?e > 0" using `0 < e` `i \<noteq> 0` `j \<noteq> 0` by (auto intro!: divide_pos_pos add_pos_pos)
    from e'[OF this] have "norm (f'' a i j - f'' a j i) \<le> ?e * (5 * norm j + 5 * norm i)" .
    also have "\<dots> = e / 2" using `i \<noteq> 0` `j \<noteq> 0` by (auto simp: ac_simps add_nonneg_eq_0_iff)
    also have "\<dots> < e" using `0 < e` by simp
    finally have "norm (f'' a i j - f'' a j i) < e" .
  } note e = this
  have "norm (f'' a i j - f'' a j i) = 0"
  proof (rule ccontr)
    assume "norm (f'' a i j - f'' a j i) \<noteq> 0"
    hence "norm (f'' a i j - f'' a j i) > 0" by simp
    from e[OF this] show False by simp
  qed
  thus ?thesis by simp
qed

end

locale local_rect = fixes G
  assumes ex_local_rect: "\<And>a. a \<in> G \<Longrightarrow> \<exists>s\<in>Basis\<rightarrow>{x. x \<noteq> 0}. \<forall>x.
    (\<forall>i \<in> Basis. min (a \<bullet> i) (a \<bullet> i + s i) \<le> x \<bullet> i \<and> x \<bullet> i \<le> max (a \<bullet> i) (a \<bullet> i + s i)) \<longrightarrow> x \<in> G"
begin

lemma local_rectE:
  assumes "a \<in> G"
  obtains s where "\<And>i. i \<in> Basis \<Longrightarrow> s i \<noteq> 0"
    "\<And>x. (\<And>i. i \<in> Basis \<Longrightarrow>
      a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> a \<bullet> i + s i \<or> a \<bullet> i + s i \<le> x \<bullet> i \<and> x \<bullet> i \<le> a \<bullet> i) \<Longrightarrow> x \<in> G"
proof atomize_elim
  from ex_local_rect[OF `a \<in> G`] guess s .. note in_GI = this
  then show "\<exists>s. (\<forall>i. i \<in> Basis \<longrightarrow> s i \<noteq> 0) \<and> (\<forall>x. (\<forall>i. i \<in> Basis \<longrightarrow>
      a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> a \<bullet> i + s i \<or> a \<bullet> i + s i \<le> x \<bullet> i \<and> x \<bullet> i \<le> a \<bullet> i) \<longrightarrow> x \<in> G)"
    by (force intro!: exI[where x=s])
qed

lemma
  local_rect_BasisE:
  assumes "a \<in> G"
  obtains s where "\<And>i. i \<in> Basis \<Longrightarrow> s i \<noteq> 0"
    "\<And>t. t \<in> Basis\<rightarrow>{0..1} \<Longrightarrow> a + (\<Sum>i\<in>Basis. (t i * s i) *\<^sub>R i) \<in> G"
proof atomize_elim
  from local_rectE[OF `a \<in> G`] guess s . note GI = this
  show "\<exists>s. (\<forall>i. i \<in> Basis \<longrightarrow> s i \<noteq> 0) \<and>
        (\<forall>t. t \<in> Basis \<rightarrow> {0..1} \<longrightarrow> a + (\<Sum>i\<in>Basis. (t i * s i) *\<^sub>R i) \<in> G)"
    by (rule exI[where x=s]) (force intro!: GI
      simp: algebra_simps inner_Basis mult_less_cancel_right2 zero_less_mult_iff Pi_iff not_le)
qed

end

sublocale local_rect < approachable_on
proof (unfold_locales, rule approachableI)
  fix a i::'a and e::real assume "a \<in> G" "i \<in> Basis" "0 < e"
  from local_rect_BasisE[OF `a \<in> G`] guess s . note nz=this(1) and in_GI = this(2)
  let ?i = "min (e / abs (s i) / 2) 1"
  have "a + (?i * s i) *\<^sub>R i = a + (\<Sum>ia\<in>Basis. ((if ia = i then ?i else 0) * s ia) *\<^sub>R ia)"
    using `i \<in> Basis`
    by (auto simp add: Pi_iff setsum.mono_neutral_cong_right[of Basis "{i}"] min_def)
  also have "\<dots> \<in> G"
    using `0 < e` by (intro in_GI[of "\<lambda>k. if k = i then ?i else 0"])
      (auto simp: Pi_iff)
  finally have "a + (?i * s i) *\<^sub>R i \<in> G" .
  moreover have "0 < abs (?i * s i)" using `e > 0` nz `i \<in> Basis` by (simp add: min_def)
  moreover have "abs (?i * s i) < e" using `e > 0` by (simp add: min_def abs_mult)
  ultimately show "\<exists>d. 0 < \<bar>d\<bar> \<and> \<bar>d\<bar> < e \<and> a + d *\<^sub>R i \<in> G" by blast
qed

lemma sqrt_le_rsquare:
  assumes "\<bar>x\<bar> \<le> sqrt y"
  shows "x\<^sup>2 \<le> y"
  using assms real_sqrt_le_iff[of "x\<^sup>2"] by simp

lemma cube_in_cball:
  fixes x y :: "'a::euclidean_space"
  assumes "r > 0"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> dist (x \<bullet> i) (y \<bullet> i) \<le> r / sqrt(DIM('a))"
  shows "y \<in> cball x r"
  unfolding mem_cball euclidean_dist_l2[of x] setL2_def
proof -
  have "(\<Sum>i\<in>Basis. (dist (x \<bullet> i) (y \<bullet> i))\<^sup>2) \<le> (\<Sum>(i::'a)\<in>Basis. (r / sqrt(DIM('a)))\<^sup>2)"
    using assms by (intro setsum_mono) (auto intro: sqrt_le_rsquare)
  moreover have "... \<le> r\<^sup>2" by (simp add: power_divide)
  ultimately show "sqrt (\<Sum>i\<in>Basis. (dist (x \<bullet> i) (y \<bullet> i))\<^sup>2) \<le> r"
    using `r > 0` by (auto intro!: real_le_lsqrt setsum_nonneg)
qed

lemma local_rect_openI:
  assumes "open G"
  shows "local_rect G"
proof
  fix a
  assume "a \<in> G"
  with `open G` open_contains_cball
  obtain e where e: "e > 0" and in_GI: "\<And>x. x \<in> cball a e \<Longrightarrow> x \<in> G" by force
  show "\<exists>s\<in>Basis \<rightarrow> {x. x \<noteq> 0}. \<forall>x.
    (\<forall>i\<in>Basis. min (a \<bullet> i) (a \<bullet> i + s i) \<le> x \<bullet> i \<and> x \<bullet> i \<le> max (a \<bullet> i) (a \<bullet> i + s i)) \<longrightarrow> x \<in> G"
    using e
    apply (intro bexI[where x="\<lambda>_. e/sqrt(DIM('a))"])
    apply (simp add: min_def max_def)
    apply (auto simp add: dist_real_def min_def max_def field_simps simp del: mem_cball
      intro!: cube_in_cball in_GI)
    done
qed

lemma local_rect_intervalI:
  fixes a b::"'a::ordered_euclidean_space"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> b \<bullet> i < c \<bullet> i"
  shows "local_rect {b..c}"
proof
  fix a
  assume "a \<in> {b..c}"
  show "\<exists>s\<in>Basis \<rightarrow> {x. x \<noteq> 0}.
      \<forall>x. (\<forall>i\<in>Basis. min (a \<bullet> i) (a \<bullet> i + s i) \<le> x \<bullet> i \<and> x \<bullet> i \<le> max (a \<bullet> i) (a \<bullet> i + s i)) \<longrightarrow>
      x \<in> {b..c}"
    using assms `a \<in> {b..c}`
    apply (intro bexI[where x="\<lambda>i. if c \<bullet> i = a \<bullet> i then b \<bullet> i - a \<bullet> i else c \<bullet> i - a \<bullet> i"])
    apply (auto simp: algebra_simps min_def max_def eucl_le[of b] eucl_le[of _ c] not_le
        split: split_if_asm)
    apply (metis le_less_trans not_le)
    apply metis
    by (metis less_irrefl)
qed

locale second_derivative_lrect = second_derivative G f f' f'' + local_rect G for G f f' f''
begin

lemma symmetric_second_derivative:
  fixes i j::"'a::euclidean_space"
  assumes "a \<in> G"
  shows "f'' a i j = f'' a j i"
proof -
  from local_rect_BasisE[OF `a \<in> G`] guess s . note nonzero = this(1) and GI = this(2)
  {
    fix i j::'a assume ij: "i \<noteq> j" "i \<in> Basis" "j \<in> Basis" hence "i \<noteq> 0" "j \<noteq> 0" by auto
    have nz: "s i *\<^sub>R i \<noteq> 0" "s j *\<^sub>R j \<noteq> 0" using nonzero ij by auto
    have ne: "s i *\<^sub>R i \<noteq> s j *\<^sub>R j"  using nonzero ij
      by (metis inner_Basis inner_scaleR_right mult_eq_0_iff zero_neq_one)
    {
      fix t u::real
      assume "0 \<le> t" "t \<le> 1" "0 \<le> u" "u \<le> 1"
      hence "a + (t * s i) *\<^sub>R i + (u * s j) *\<^sub>R j \<in> G"
        using GI[of "((\<lambda>_. 0)(i:=t))(j:=u)"] `i \<in> Basis` `j \<in> Basis` `i \<noteq> j`
        by (simp add: ac_simps setsum.mono_neutral_cong_right[of Basis "{i, j}"])
    }
    hence "f'' a (s i *\<^sub>R i) (s j *\<^sub>R j) = f'' a (s j *\<^sub>R j) (s i *\<^sub>R i)" using ij ne
      by (auto intro!: symmetric_second_derivative_aux[OF ne nz `a \<in> G`])
    hence "f'' a i j = f'' a j i" using `a \<in> G` nz by (simp add: ac_simps)
  }
  hence f''_eq: "\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> f'' a i j = f'' a j i"
    by (case_tac "i = j") auto
  have "f'' a (\<Sum>b\<in>Basis. (i \<bullet> b) *\<^sub>R b) (\<Sum>b\<in>Basis. (j \<bullet> b) *\<^sub>R b) =
    f'' a (\<Sum>b\<in>Basis. (j \<bullet> b) *\<^sub>R b) (\<Sum>b\<in>Basis. (i \<bullet> b) *\<^sub>R b)"
    using `a \<in> G`
    by (auto simp: ac_simps f''_eq swap_inj_on intro:
      setsum.reindex_cong [of "\<lambda>(i, j). (j, i)"])
  thus ?thesis by (simp add: euclidean_representation)
qed

end

locale higher_derivative_lrect = higher_derivative G f n Ds + local_rect G
  for G and f::"'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and n Ds
begin

lemma
  symmetric_higher_derivative:
  assumes "length ds < n"
  assumes "a \<in> G"
  shows "Ds (i#ds) a j = Ds (j#ds) a i"
  using assms(1)
proof (induct ds arbitrary: i j)
  case Nil
  interpret second_derivative_lrect G f "Ds []" "\<lambda>x i. Ds [i] x"
    by unfold_locales (auto intro!: derivative_intros Nil)
  show ?case by (rule symmetric_second_derivative[OF `a \<in> G`])
next
  case (Cons e es k j)
  then interpret second_derivative_lrect G "\<lambda>x. Ds es x i" "Ds (i#es)" "\<lambda>x j.  Ds (j # i # es) x" for i
    by unfold_locales (auto intro!: derivative_eq_intros Cons approachable)
  show ?case by (rule symmetric_second_derivative[OF `a \<in> G`])
qed

end

locale traj_with_higher_derivatives = higher_derivative _ _ _ Ds
  for Ds :: "(real*'a::euclidean_space) list \<Rightarrow> (real*'a) \<Rightarrow> (real*'a) \<Rightarrow> 'a::euclidean_space" +
  fixes x::"real \<Rightarrow> ('a::euclidean_space)"
  assumes domain_notempty: "G \<noteq> {}"
  assumes x': "\<And>s. s \<in> {t..u} \<Longrightarrow> (x has_vector_derivative f (s, x s)) (at s within {t..u})"
begin

lemma has_derivativex[derivative_intros]: "\<And>s. s \<in> {t..u} \<Longrightarrow> (x has_derivative (\<lambda>xa. xa *\<^sub>R f (s, x s))) (at s within {t..u})"
  using x'
  by (auto intro!: derivative_eq_intros simp: has_vector_derivative_def)

lemma
  assumes x_in: "\<And>s. s \<in> {t..u} \<Longrightarrow> (s, x s) \<in> G"
  shows "\<And>s. s \<in> {t..u} \<Longrightarrow> ((\<lambda>s. f (s, x s)) has_vector_derivative
    Ds [] (s, x s) (1, f (s, x s))) (at s within {t..u})"
  apply (auto intro!: derivative_eq_intros simp: has_vector_derivative_def)
  apply (rule has_derivative_eq_rhs)
  apply (rule has_derivative_in_compose[where g=f])
  apply (rule derivative_eq_intros refl)+
  apply simp
  apply (rule refl)+
  apply (rule has_derivative_subset)
  apply (rule Ds_0)
  apply (rule x_in)
  apply simp
  apply rule
  apply (auto intro!: x_in)
  apply rule
  using linear.scaleR[OF linear_Ds[OF _ x_in], of "[]", symmetric, simplified]
  apply simp
  done

end

end

