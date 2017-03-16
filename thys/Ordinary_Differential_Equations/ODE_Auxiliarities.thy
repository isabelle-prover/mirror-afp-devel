section \<open>Auxiliary Lemmas\<close>
theory ODE_Auxiliarities
imports
  "~~/src/HOL/Analysis/Analysis"
  "~~/src/HOL/Library/Float"
begin

sledgehammer_params [fact_filter=mepo]

instantiation prod :: (zero_neq_one, zero_neq_one) zero_neq_one
begin

definition "1 = (1, 1)"

instance by standard (simp add: zero_prod_def one_prod_def)
end

subsection \<open>there is no inner product for type @{typ "'a \<Rightarrow>\<^sub>L 'b"}\<close>

lemma (in real_inner) parallelogram_law: "(norm (x + y))\<^sup>2 + (norm (x - y))\<^sup>2 = 2 * (norm x)\<^sup>2 + 2 * (norm y)\<^sup>2"
proof -
  have "(norm (x + y))\<^sup>2 + (norm (x - y))\<^sup>2 = inner (x + y) (x + y) + inner (x - y) (x - y)"
    by (simp add: norm_eq_sqrt_inner)
  also have "\<dots> = 2 * (norm x)\<^sup>2 + 2 * (norm y)\<^sup>2"
    by (simp add: algebra_simps norm_eq_sqrt_inner)
  finally show ?thesis .
qed

locale no_real_inner
begin

lift_definition fstzero::"(real*real) \<Rightarrow>\<^sub>L (real*real)" is "\<lambda>(x, y). (x, 0)"
  by (auto intro!: bounded_linearI')

lemma [simp]: "fstzero (a, b) = (a, 0)"
  by transfer simp

lift_definition zerosnd::"(real*real) \<Rightarrow>\<^sub>L (real*real)" is "\<lambda>(x, y). (0, y)"
  by (auto intro!: bounded_linearI')

lemma [simp]: "zerosnd (a, b) = (0, b)"
  by transfer simp

lemma fstzero_add_zerosnd: "fstzero + zerosnd = id_blinfun"
  by transfer auto

lemma norm_fstzero_zerosnd: "norm fstzero = 1" "norm zerosnd = 1" "norm (fstzero - zerosnd) = 1"
  by (rule norm_blinfun_eqI[where x="(1, 0)"]) (auto simp: norm_Pair blinfun.bilinear_simps
    intro: norm_blinfun_eqI[where x="(0, 1)"] norm_blinfun_eqI[where x="(1, 0)"])

text \<open>compare with @{thm parallelogram_law}\<close>

lemma "(norm (fstzero + zerosnd))\<^sup>2 + (norm (fstzero - zerosnd))\<^sup>2 \<noteq>
    2 * (norm fstzero)\<^sup>2 + 2 * (norm zerosnd)\<^sup>2"
  by (simp add: fstzero_add_zerosnd norm_fstzero_zerosnd)

end

subsection \<open>bounded linear functions\<close>

locale blinfun_syntax
begin
no_notation vec_nth (infixl "$" 90)
notation blinfun_apply (infixl "$" 999)
end

lemma bounded_linear_via_derivative:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::euclidean_space \<Rightarrow>\<^sub>L 'c::real_normed_vector" \<comment>\<open>TODO: generalize?\<close>
  assumes "\<And>i. ((\<lambda>x. blinfun_apply (f x) i) has_derivative (\<lambda>x. f' y x i)) (at y)"
  shows "bounded_linear (f' y x)"
proof -
  interpret linear "f' y x"
  proof (unfold_locales, goal_cases)
    case (1 v w)
    from has_derivative_unique[OF assms[of "v + w", unfolded blinfun.bilinear_simps]
      has_derivative_add[OF assms[of v] assms[of w]], THEN fun_cong, of x]
    show ?case .
  next
    case (2 r v)
    from has_derivative_unique[OF assms[of "r *\<^sub>R v", unfolded blinfun.bilinear_simps]
      has_derivative_scaleR_right[OF assms[of v], of r], THEN fun_cong, of x]
    show ?case .
  qed
  let ?bnd = "\<Sum>i\<in>Basis. norm (f' y x i)"
  {
    fix v
    have "f' y x v = (\<Sum>i\<in>Basis. (v \<bullet> i) *\<^sub>R f' y x i)"
      by (subst euclidean_representation[symmetric]) (simp add: sum scaleR)
    also have "norm \<dots> \<le> norm v * ?bnd"
      by (auto intro!: order.trans[OF norm_sum] sum_mono mult_right_mono
        simp: sum_distrib_left Basis_le_norm)
    finally have "norm (f' y x v) \<le> norm v * ?bnd" .
  }
  then show ?thesis by unfold_locales auto
qed

definition blinfun_scaleR::"('a::real_normed_vector \<Rightarrow>\<^sub>L real) \<Rightarrow> 'b::real_normed_vector \<Rightarrow> ('a \<Rightarrow>\<^sub>L 'b)"
  where "blinfun_scaleR a b = blinfun_scaleR_left b o\<^sub>L a"

lemma blinfun_scaleR_transfer[transfer_rule]:
  "rel_fun (pcr_blinfun op = op =) (rel_fun op = (pcr_blinfun op = op =))
    (\<lambda>a b c. a c *\<^sub>R b) blinfun_scaleR"
  by (auto simp: blinfun_scaleR_def rel_fun_def pcr_blinfun_def cr_blinfun_def OO_def)

lemma blinfun_scaleR_rep_eq[simp]:
  "blinfun_scaleR a b c = a c *\<^sub>R b"
  by (simp add: blinfun_scaleR_def)

lemma bounded_linear_blinfun_scaleR: "bounded_linear (blinfun_scaleR a)"
  unfolding blinfun_scaleR_def[abs_def]
  by (auto intro!: bounded_linear_intros)

lemma blinfun_scaleR_has_derivative[derivative_intros]:
  assumes "(f has_derivative f') (at x within s)"
  shows "((\<lambda>x. blinfun_scaleR a (f x)) has_derivative (\<lambda>x. blinfun_scaleR a (f' x))) (at x within s)"
  using bounded_linear_blinfun_scaleR assms
  by (rule bounded_linear.has_derivative)

lemma blinfun_componentwise:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::euclidean_space \<Rightarrow>\<^sub>L 'c::real_normed_vector"
  shows "f = (\<lambda>x. \<Sum>i\<in>Basis. blinfun_scaleR (blinfun_inner_left i) (f x i))"
  by (auto intro!: blinfun_eqI
    simp: blinfun.sum_left euclidean_representation blinfun.scaleR_right[symmetric]
      blinfun.sum_right[symmetric])

lemma
  blinfun_has_derivative_componentwiseI:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::euclidean_space \<Rightarrow>\<^sub>L 'c::real_normed_vector"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> ((\<lambda>x. f x i) has_derivative blinfun_apply (f' i)) (at x)"
  shows "(f has_derivative (\<lambda>x. \<Sum>i\<in>Basis. blinfun_scaleR (blinfun_inner_left i) (f' i x))) (at x)"
  by (subst blinfun_componentwise) (force intro: derivative_eq_intros assms simp: blinfun.bilinear_simps)

lemma
  has_derivative_BlinfunI:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::euclidean_space \<Rightarrow>\<^sub>L 'c::real_normed_vector"
  assumes "\<And>i. ((\<lambda>x. f x i) has_derivative (\<lambda>x. f' y x i)) (at y)"
  shows "(f has_derivative (\<lambda>x. Blinfun (f' y x))) (at y)"
proof -
  have 1: "f = (\<lambda>x. \<Sum>i\<in>Basis. blinfun_scaleR (blinfun_inner_left i) (f x i))"
    by (rule blinfun_componentwise)
  moreover have 2: "(\<dots> has_derivative (\<lambda>x. \<Sum>i\<in>Basis. blinfun_scaleR (blinfun_inner_left i) (f' y x i))) (at y)"
    by (force intro: assms derivative_eq_intros)
  moreover
  interpret f': bounded_linear "f' y x" for x
    by (rule bounded_linear_via_derivative) (rule assms)
  have 3: "(\<Sum>i\<in>Basis. blinfun_scaleR (blinfun_inner_left i) (f' y x i)) i = f' y x i" for x i
    by (auto simp: if_distrib cond_application_beta blinfun.bilinear_simps
      f'.scaleR[symmetric] f'.sum[symmetric] euclidean_representation
      intro!: blinfun_euclidean_eqI)
  have 4: "blinfun_apply (Blinfun (f' y x)) = f' y x" for x
    apply (subst bounded_linear_Blinfun_apply)
    subgoal by unfold_locales
    subgoal by simp
    done
  show ?thesis
    apply (subst 1)
    apply (rule 2[THEN has_derivative_eq_rhs])
    apply (rule ext)
    apply (rule blinfun_eqI)
    apply (subst 3)
    apply (subst 4)
    apply (rule refl)
    done
qed

lemma
  has_derivative_Blinfun:
  assumes "(f has_derivative f') F"
  shows "(f has_derivative Blinfun f') F"
  using assms
  by (subst bounded_linear_Blinfun_apply) auto

lift_definition flip_blinfun::
  "('a::real_normed_vector \<Rightarrow>\<^sub>L 'b::real_normed_vector \<Rightarrow>\<^sub>L 'c::real_normed_vector) \<Rightarrow> 'b \<Rightarrow>\<^sub>L 'a \<Rightarrow>\<^sub>L 'c" is
  "\<lambda>f x y. f y x"
  using bounded_bilinear.bounded_linear_left bounded_bilinear.bounded_linear_right bounded_bilinear.flip
  by auto

lemma flip_blinfun_apply[simp]: "flip_blinfun f a b = f b a"
  by transfer simp

lemma le_norm_blinfun:
  shows "norm (blinfun_apply f x) / norm x \<le> norm f"
  by transfer (rule le_onorm)

lemma norm_flip_blinfun[simp]: "norm (flip_blinfun x) = norm x" (is "?l = ?r")
proof (rule antisym)
  from order_trans[OF norm_blinfun, OF mult_right_mono, OF norm_blinfun, OF norm_ge_zero, of x]
  show "?l \<le> ?r"
    by (auto intro!: norm_blinfun_bound simp: ac_simps)
  have "norm (x a b) \<le> norm (flip_blinfun x) * norm a * norm b" for a b
  proof -
    have "norm (x a b) / norm a \<le> norm (flip_blinfun x b)"
      by (rule order_trans[OF _ le_norm_blinfun]) auto
    also have "\<dots> \<le> norm (flip_blinfun x) * norm b"
      by (rule norm_blinfun)
    finally show ?thesis
      by (auto simp add: divide_simps blinfun.bilinear_simps sign_simps  split: if_split_asm)
  qed
  then show "?r \<le> ?l"
    by (auto intro!: norm_blinfun_bound)
qed

lemma bounded_linear_flip_blinfun[bounded_linear]: "bounded_linear flip_blinfun"
  by unfold_locales (auto simp: blinfun.bilinear_simps intro!: blinfun_eqI exI[where x=1])

lemma dist_swap2_swap2[simp]: "dist (flip_blinfun f) (flip_blinfun g) = dist f g"
  by (metis (no_types) bounded_linear_flip_blinfun dist_blinfun_def linear_simps(2)
    norm_flip_blinfun)


subsection \<open>Topology\<close>

lemma at_within_ball: "e > 0 \<Longrightarrow> dist x y < e \<Longrightarrow> at y within ball x e = at y"
  by (subst at_within_open) auto

lemma
  infdist_attains_inf:
  fixes X::"'a::heine_borel set"
  assumes "closed X"
  assumes "X \<noteq> {}"
  obtains x where "x \<in> X" "infdist y X = dist y x"
proof -
  have "bdd_below (dist y ` X)"
    by auto
  from distance_attains_inf[OF assms, of y]
  obtain x where INF: "x \<in> X" "\<And>z. z \<in> X \<Longrightarrow> dist y x \<le> dist y z" by auto
  have "infdist y X = dist y x"
    by (auto simp: infdist_def assms
      intro!: antisym cINF_lower[OF _ \<open>x \<in> X\<close>] cINF_greatest[OF assms(2) INF(2)])
  with \<open>x \<in> X\<close> show ?thesis ..
qed

lemma compact_infdist_le:
  fixes A::"'a::heine_borel set"
  assumes "A \<noteq> {}"
  assumes "compact A"
  assumes "e > 0"
  shows "compact {x. infdist x A \<le> e}"
proof -
  from continuous_closed_vimage[of "{0..e}" "\<lambda>x. infdist x A"]
    continuous_infdist[OF continuous_ident, of _ UNIV A]
  have "closed {x. infdist x A \<le> e}" by (auto simp: vimage_def infdist_nonneg)
  moreover
  from assms obtain x0 b where b: "\<And>x. x \<in> A \<Longrightarrow> dist x0 x \<le> b" "closed A"
    by (auto simp: compact_eq_bounded_closed bounded_def)
  {
    fix y
    assume le: "infdist y A \<le> e"
    from infdist_attains_inf[OF \<open>closed A\<close> \<open>A \<noteq> {}\<close>, of y]
    obtain z where z: "z \<in> A" "infdist y A = dist y z" by blast
    have "dist x0 y \<le> dist y z + dist x0 z"
      by (metis dist_commute dist_triangle)
    also have "dist y z \<le> e" using le z by simp
    also have "dist x0 z \<le> b" using b z by simp
    finally have "dist x0 y \<le> b + e" by arith
  } then
  have "bounded {x. infdist x A \<le> e}"
    by (auto simp: bounded_any_center[where a=x0] intro!: exI[where x="b + e"])
  ultimately show "compact {x. infdist x A \<le> e}"
    by (simp add: compact_eq_bounded_closed)
qed

lemma compact_in_open_separated:
  fixes A::"'a::heine_borel set"
  assumes "A \<noteq> {}"
  assumes "compact A"
  assumes "open B"
  assumes "A \<subseteq> B"
  obtains e where "e > 0" "{x. infdist x A \<le> e} \<subseteq> B"
proof atomize_elim
  have "closed (- B)" "compact A" "- B \<inter> A = {}"
    using assms by (auto simp: open_Diff compact_eq_bounded_closed)
  from separate_closed_compact[OF this]
  obtain d'::real where d': "d'>0" "\<And>x y. x \<notin> B \<Longrightarrow> y \<in> A \<Longrightarrow> d' \<le> dist x y"
    by auto
  define d where "d = d' / 2"
  hence "d>0" "d < d'" using d' by auto
  with d' have d: "\<And>x y. x \<notin> B \<Longrightarrow> y \<in> A \<Longrightarrow> d < dist x y"
    by force
  show "\<exists>e>0. {x. infdist x A \<le> e} \<subseteq> B"
  proof (rule ccontr)
    assume "\<nexists>e. 0 < e \<and> {x. infdist x A \<le> e} \<subseteq> B"
    with \<open>d > 0\<close> obtain x where x: "infdist x A \<le> d" "x \<notin> B"
      by auto
    from assms have "closed A" "A \<noteq> {}" by (auto simp: compact_eq_bounded_closed)
    from infdist_attains_inf[OF this]
    obtain y where y: "y \<in> A" "infdist x A = dist x y"
      by auto
    have "dist x y \<le> d" using x y by simp
    also have "\<dots> < dist x y" using y d x by auto
    finally show False by simp
  qed
qed


subsection \<open>Linorder\<close>

context linordered_idom
begin

lemma mult_left_le_one_le:
  "0 \<le> x \<Longrightarrow> y \<le> 1 \<Longrightarrow> y * x \<le> x"
  by (auto simp add: mult_le_cancel_right2)

lemma mult_le_oneI: "0 \<le> a \<and> a \<le> 1 \<and> b \<le> 1 \<Longrightarrow> a * b \<le> 1"
  using local.dual_order.trans local.mult_left_le by blast

end


subsection \<open>Reals\<close>


subsection \<open>Vector Spaces\<close>

lemma scaleR_dist_distrib_left:
  fixes b c::"'a::real_normed_vector"
  shows "abs a * dist b c = dist (scaleR a b) (scaleR a c)"
  unfolding dist_norm scaleR_diff_right[symmetric] norm_scaleR ..

lemma scaleR_dist_distrib_right:
  fixes a::"'a::real_normed_vector"
  shows "norm a * dist b c = dist (scaleR b a) (scaleR c a)"
  unfolding dist_norm scaleR_diff_left[symmetric] norm_scaleR
  by simp

lemma ex_norm_eq_1: "\<exists>x. norm (x::'a::euclidean_space) = 1"
  by (metis vector_choose_size zero_le_one)


lemma open_neg_translation:
  fixes s :: "'a::real_normed_vector set"
  assumes "open s"
  shows "open((\<lambda>x. a - x) ` s)"
  using open_translation[OF open_negations[OF assms], of a]
  by (auto simp: image_image)

subsection \<open>Balls\<close>

text \<open>I think that @{thm mem_ball} etc. are not \<open>[simp]\<close> rules:
  not sure that inequalities are ``simpler'' than set membership (distorts automatic reasoning
  when only sets are involved)\<close>
lemmas [simp del] = mem_ball mem_cball mem_sphere mem_ball_0 mem_cball_0

lemma ball_subset_cball: "x \<in> ball y e \<Longrightarrow> x \<in> cball y e"
  by (auto simp: mem_ball mem_cball)

lemma ball_subset_ball: "x \<in> ball y e \<Longrightarrow> e < f \<Longrightarrow> x \<in> ball y f"
  by (auto simp: mem_ball mem_cball)

lemma cball_subset_cball: "x \<in> cball y e \<Longrightarrow> e < f \<Longrightarrow> x \<in> cball y f"
  by (auto simp: mem_ball mem_cball)


subsection \<open>Intervals\<close>

notation closed_segment ("(1{_--_})")

lemma open_closed_segment_subset: "open_segment a b \<subseteq> closed_segment a b"
  by (simp add: open_closed_segment subsetI)

lemma is_interval_real_cball[intro, simp]:
  fixes a b::real
  shows "is_interval (cball a b)"
  by (auto simp: is_interval_convex_1 convex_cball)

lemma is_interval_closed_segment_1[intro, simp]:
  fixes a b::real
  shows "is_interval {a -- b}"
  by (auto simp: is_interval_convex_1)

lemma atLeastAtMost_eq_cball:
  fixes a b::real
  shows "{a .. b} = cball ((a + b)/2) ((b - a)/2)"
  by (auto simp: dist_real_def field_simps mem_cball)

lemma greaterThanLessThan_eq_ball:
  fixes a b::real
  shows "{a <..< b} = ball ((a + b)/2) ((b - a)/2)"
  by (auto simp: dist_real_def field_simps mem_ball)

lemma image_mult_atLeastAtMost:
  "(\<lambda>x. x * c::real) ` {x..y} =
    (if x \<le> y then if c > 0 then {x * c .. y * c} else {y * c .. x * c} else {})"
  apply (cases "c = 0")
  subgoal by force
  subgoal by (auto simp: field_simps not_less intro!: image_eqI[where x="inverse c * xa" for xa])
  done

lemma image_add_atLeastAtMost:
  "op + c ` {x..y::real} = {c + x .. c + y}"
  by (auto intro: image_eqI[where x="xa - c" for xa])

lemma min_zero_mult_nonneg_le: "0 \<le> h' \<Longrightarrow> h' \<le> h \<Longrightarrow> min 0 (h * k::real) \<le> h' * k"
  by (metis dual_order.antisym le_cases min_le_iff_disj mult_eq_0_iff mult_le_0_iff
      mult_right_mono_neg)

lemma max_zero_mult_nonneg_le: "0 \<le> h' \<Longrightarrow> h' \<le> h \<Longrightarrow> h' * k \<le> max 0 (h * k::real)"
  by (metis dual_order.antisym le_cases le_max_iff_disj mult_eq_0_iff mult_right_mono
      zero_le_mult_iff)

lemmas closed_segment_real = closed_segment_eq_real_ivl

lemma open_segment_real_le:
  fixes a b::real
  assumes "a \<le> b"
  shows "open_segment a b = {a <..< b}"
  using assms
  unfolding open_segment_def closed_segment_real
  by auto

lemma open_segment_real:
  fixes a b::real
  shows "open_segment a b = (if a \<le> b then {a <..< b} else {b <..< a})"
  using open_segment_real_le[of a b]
    open_segment_real_le[of b a]
    open_segment_commute[of b a]
  by simp

lemma linear_compose: "(\<lambda>xa. a + xa * b) = (\<lambda>x. a + x) o (\<lambda>x. x * b)"
  by auto

lemma image_linear_atLeastAtMost:
  "(\<lambda>xa. a + xa * b) ` {c..d::real} =
  (if c \<le> d then
    if b > 0 then {a + c * b .. a + d * b}
    else {a + d * b .. a + c * b}
  else {})"
  by (simp add: linear_compose image_comp [symmetric] image_mult_atLeastAtMost
    image_add_atLeastAtMost)

lemma insert_atMost[simp]: "insert t {..t::'a::preorder} = {..t}" by auto

lemma insert_atLeastAtMost[simp]:
  "s \<ge> 0 \<Longrightarrow> insert t {t..s + t::'a::ordered_ab_group_add} = {t .. s + t}" by auto

lemma uminus_uminus_image[simp]:
  fixes x::"'a::group_add set"
  shows "uminus ` uminus ` x = x"
  by force

lemma Ball_singleton: "Ball {x} f = f x"
  by simp

lemma is_real_interval_union:
  fixes X Y::"real set"
  shows "is_interval X \<Longrightarrow>
    is_interval Y \<Longrightarrow>
    (X \<noteq> {} \<Longrightarrow> Y \<noteq> {} \<Longrightarrow> X \<inter> Y \<noteq> {}) \<Longrightarrow>
    is_interval (X \<union> Y)"
  unfolding is_interval_def Basis_real_def Ball_singleton real_inner_1_right
  by (safe; metis (mono_tags) all_not_in_conv disjoint_iff_not_equal le_cases)

lemma is_interval_translationI:
  assumes "is_interval X"
  shows "is_interval (op + x ` X)"
  unfolding is_interval_def
proof safe
  fix b d e
  assume "b \<in> X" "d \<in> X"
    "\<forall>i\<in>Basis. (x + b) \<bullet> i \<le> e \<bullet> i \<and> e \<bullet> i \<le> (x + d) \<bullet> i \<or>
       (x + d) \<bullet> i \<le> e \<bullet> i \<and> e \<bullet> i \<le> (x + b) \<bullet> i"
  hence "e - x \<in> X"
    by (intro mem_is_intervalI[OF assms \<open>b \<in> X\<close> \<open>d \<in> X\<close>, of "e - x"])
      (auto simp: algebra_simps)
  thus "e \<in> op + x ` X" by force
qed

lemma is_interval_uminusI:
  assumes "is_interval X"
  shows "is_interval (uminus ` X)"
  unfolding is_interval_def
proof safe
  fix b d e
  assume "b \<in> X" "d \<in> X"
    "\<forall>i\<in>Basis. (- b) \<bullet> i \<le> e \<bullet> i \<and> e \<bullet> i \<le> (- d) \<bullet> i \<or>
       (- d) \<bullet> i \<le> e \<bullet> i \<and> e \<bullet> i \<le> (- b) \<bullet> i"
  hence "- e \<in> X"
    by (intro mem_is_intervalI[OF assms \<open>b \<in> X\<close> \<open>d \<in> X\<close>, of "- e"])
      (auto simp: algebra_simps)
  thus "e \<in> uminus ` X" by force
qed

lemma is_interval_uminus[simp]: "is_interval (uminus ` x) = is_interval x"
  using is_interval_uminusI[of x] is_interval_uminusI[of "uminus ` x"]
  by auto

lemma is_interval_neg_translationI:
  assumes "is_interval X"
  shows "is_interval (op - x ` X)"
proof -
  have "op - x ` X = op + x ` uminus ` X"
    by (force simp: algebra_simps)
  also have "is_interval \<dots>"
    by (metis is_interval_uminusI is_interval_translationI assms)
  finally show ?thesis .
qed

lemma is_interval_translation[simp]:
  "is_interval (op + x ` X) = is_interval X"
  using is_interval_neg_translationI[of "op + x ` X" x]
  by (auto intro!: is_interval_translationI simp: image_image)

lemma is_interval_minus_translation[simp]:
  shows "is_interval (op - x ` X) = is_interval X"
proof -
  have "op - x ` X = op + x ` uminus ` X"
    by (force simp: algebra_simps)
  also have "is_interval \<dots> = is_interval X"
    by simp
  finally show ?thesis .
qed

lemma is_interval_minus_translation'[simp]:
  shows "is_interval ((\<lambda>x. x - c) ` X) = is_interval X"
  using is_interval_translation[of "-c" X]
  by (metis image_cong uminus_add_conv_diff)

lemma [simp]:
  fixes a::"'a::ordered_euclidean_space"
  shows is_interval_ci: "is_interval {a..}"
    and is_interval_ic: "is_interval {..a}"
  by (force simp: is_interval_def eucl_le[where 'a='a])+

lemma [simp]:
  fixes a b::real
  shows is_interval_1_io: "is_interval {..<a}"
    and is_interval_1_oi: "is_interval {a<..}"
    and is_interval_1_co: "is_interval {b..<a}"
    and is_interval_1_oc: "is_interval {a<..b}"
    and is_interval_1_cc: "is_interval {b..a}"
    and is_interval_1_oo: "is_interval {b..a}"
  by (force simp: is_interval_def)+

lemma image_add_atLeast_real[simp]:
  fixes a b c::"'a::ordered_real_vector"
  shows "op + c ` {a..} = {c + a..}"
  by (auto intro!: image_eqI[where x="x - c" for x] simp: algebra_simps)

lemma image_add_atMost_real[simp]:
  fixes a b c::"'a::ordered_real_vector"
  shows "op + c ` {..a} = {..c + a}"
  by (auto intro!: image_eqI[where x="x - c" for x] simp: algebra_simps)

lemma image_add_atLeastLessThan_real[simp]:
  fixes a b c::"'a::ordered_real_vector"
  shows "op + c ` {a..<b} = {c + a..<c + b}"
  by (auto intro!: image_eqI[where x="x - c" for x] simp: algebra_simps)

lemma image_add_greaterThanAtMost_real[simp]:
  fixes a b c::"'a::ordered_real_vector"
  shows "op + c ` {a<..b} = {c + a<..c + b}"
  by (auto intro!: image_eqI[where x="x - c" for x] simp: algebra_simps)


lemma image_minus_const_atLeastLessThan_real[simp]:
  fixes a b c::"'a::ordered_real_vector"
  shows "op - c ` {a..<b} = {c - b<..c - a}"
proof -
  have "op - c ` {a..<b} = op + c ` uminus ` {a ..<b}"
    unfolding image_image by simp
  also have "\<dots> = {c - b<..c - a}" by simp
  finally show ?thesis by simp
qed

lemma image_minus_const_greaterThanAtMost_real[simp]:
  fixes a b c::"'a::ordered_real_vector"
  shows "op - c ` {a<..b} = {c - b..<c - a}"
proof -
  have "op - c ` {a<..b} = op + c ` uminus ` {a<..b}"
    unfolding image_image by simp
  also have "\<dots> = {c - b..<c - a}" by simp
  finally show ?thesis by simp
qed

lemma image_minus_const_atLeast_real[simp]:
  fixes a c::"'a::ordered_real_vector"
  shows "op - c ` {a..} = {..c - a}"
proof -
  have "op - c ` {a..} = op + c ` uminus ` {a ..}"
    unfolding image_image by simp
  also have "\<dots> = {..c - a}" by simp
  finally show ?thesis by simp
qed

lemma image_minus_const_AtMost_real[simp]:
  fixes b c::"'a::ordered_real_vector"
  shows "op - c ` {..b} = {c - b..}"
proof -
  have "op - c ` {..b} = op + c ` uminus ` {..b}"
    unfolding image_image by simp
  also have "\<dots> = {c - b..}" by simp
  finally show ?thesis by simp
qed

lemma interior_atLeastAtMost:
  fixes a b::real
  assumes "a < b"
  shows "interior {a .. b} = {a <..< b}"
  by (metis assms closure_greaterThanLessThan convex_interior_closure
    convex_real_interval(8) interior_open open_greaterThanLessThan)

lemma is_interval_Ioo:
  fixes x::real shows "is_interval {x<..<y}"
  by (metis connected_Ioo is_interval_connected_1)

lemma is_interval_Ioi:
  fixes x::real shows "is_interval {x<..}"
  by (metis connected_Ioi is_interval_connected_1)

lemma is_interval_Iio:
  fixes x::real shows "is_interval {..<x}"
  by (metis connected_Iio is_interval_connected_1)

lemma is_interval_inter: "is_interval X \<Longrightarrow> is_interval Y \<Longrightarrow> is_interval (X \<inter> Y)"
  unfolding is_interval_def
  by blast

lemma cball_trans: "y \<in> cball z b \<Longrightarrow> x \<in> cball y a \<Longrightarrow> x \<in> cball z (b + a)"
  unfolding mem_cball
proof -
  have "dist z x \<le> dist z y + dist y x"
    by (rule dist_triangle)
  also assume "dist z y \<le> b"
  also assume "dist y x \<le> a"
  finally show "dist z x \<le> b + a" by arith
qed

lemma (in linorder_topology) unbounded_connected_above_memI:
  assumes conn: "connected S"
  assumes nbdd: "\<not> bdd_above S"
  assumes "t0 \<in> S"
  assumes "t0 \<le> t"
  shows "t \<in> S"
proof -
  from nbdd obtain s where "s \<in> S" "s \<ge> t" by (metis not_le less_imp_le bdd_above_def)
  from connectedD_interval[OF conn \<open>t0 \<in> S\<close> \<open>s \<in> S\<close> \<open>t0 \<le> t\<close> \<open>t \<le> s\<close>]
  show "t \<in> S" .
qed

lemma (in linorder_topology) unbounded_connected_below_memI:
  assumes conn: "connected S"
  assumes nbdd: "\<not> bdd_below S"
  assumes "t0 \<in> S"
  assumes "t \<le> t0"
  shows "t \<in> S"
proof -
  from nbdd obtain s where "s \<in> S" "t \<ge> s" by (metis not_le less_imp_le bdd_below_def)
  from connectedD_interval[OF conn \<open>s \<in> S\<close> \<open>t0 \<in> S\<close> \<open>s \<le> t\<close> \<open>t \<le> t0\<close>]
  show "t \<in> S" .
qed

lemma (in linorder_topology) not_in_connected_cases:
  assumes conn: "connected S"
  assumes nbdd: "x \<notin> S"
  assumes ne: "S \<noteq> {}"
  obtains "bdd_above S" "\<And>y. y \<in> S \<Longrightarrow> x \<ge> y" | "bdd_below S" "\<And>y. y \<in> S \<Longrightarrow> x \<le> y"
proof -
  obtain s where "s \<in> S" using ne by blast
  {
    assume "s \<le> x"
    have "False" if "x \<le> y" "y \<in> S" for y
      using connectedD_interval[OF conn \<open>s \<in> S\<close> \<open>y \<in> S\<close> \<open>s \<le> x\<close> \<open>x \<le> y\<close>] \<open>x \<notin> S\<close>
      by simp
    then have wit: "y \<in> S \<Longrightarrow> x \<ge> y" for y
      using le_cases by blast
    then have "bdd_above S"
      by (rule local.bdd_aboveI)
    note this wit
  } moreover {
    assume "x \<le> s"
    have "False" if "x \<ge> y" "y \<in> S" for y
      using connectedD_interval[OF conn \<open>y \<in> S\<close> \<open>s \<in> S\<close> \<open>x \<ge> y\<close> \<open>s \<ge> x\<close> ] \<open>x \<notin> S\<close>
      by simp
    then have wit: "y \<in> S \<Longrightarrow> x \<le> y" for y
      using le_cases by blast
    then have "bdd_below S"
      by (rule local.bdd_belowI)
    note this wit
  } ultimately show ?thesis
    by (meson local.le_cases that)
qed

lemma mem_is_interval_1_I:
  fixes a b c::real
  assumes "is_interval S"
  assumes "a \<in> S" "c \<in> S"
  assumes "a \<le> b" "b \<le> c"
  shows "b \<in> S"
  using assms is_interval_1 by blast


subsection \<open>Extended Real Intervals\<close>

lemma open_real_image:
  fixes X::"ereal set"
  assumes "open X"
  assumes "\<infinity> \<notin> X"
  assumes "-\<infinity> \<notin> X"
  shows "open (real_of_ereal ` X)"
proof -
  have "real_of_ereal ` X = ereal -` X"
    apply safe
    subgoal by (metis assms(2) assms(3) real_of_ereal.elims vimageI)
    subgoal using image_iff by fastforce
    done
  thus ?thesis
    by (auto intro!: open_ereal_vimage assms)
qed

lemma real_greaterThanLessThan_infinity_eq:
  "real_of_ereal ` {N::ereal<..<\<infinity>} =
    (if N = \<infinity> then {} else if N = -\<infinity> then UNIV else {real_of_ereal N<..})"
proof -
  {
    fix x::real
    have "x \<in> real_of_ereal ` {- \<infinity><..<\<infinity>::ereal}"
      by (auto intro!: image_eqI[where x="ereal x"])
  } moreover {
    fix x::ereal
    assume "N \<noteq> - \<infinity>" "N < x" "x \<noteq> \<infinity>"
    then have "real_of_ereal N < real_of_ereal x"
      by (cases N; cases x; simp)
  } moreover {
    fix x::real
    assume "N \<noteq> \<infinity>" "real_of_ereal N < x"
    then have "x \<in> real_of_ereal ` {N<..<\<infinity>}"
      by (cases N) (auto intro!: image_eqI[where x="ereal x"])
  } ultimately show ?thesis by auto
qed

lemma real_greaterThanLessThan_minus_infinity_eq:
  "real_of_ereal ` {-\<infinity><..<N::ereal} =
    (if N = \<infinity> then UNIV else if N = -\<infinity> then {} else {..<real_of_ereal N})"
proof -
  have "real_of_ereal ` {-\<infinity><..<N::ereal} = uminus ` real_of_ereal ` {-N<..<\<infinity>}"
    by (auto simp: ereal_uminus_less_reorder intro!: image_eqI[where x="-x" for x])
  also note real_greaterThanLessThan_infinity_eq
  finally show ?thesis by (auto intro!: image_eqI[where x="-x" for x])
qed

lemma real_greaterThanLessThan_inter:
  "real_of_ereal ` {N<..<M::ereal} = real_of_ereal ` {-\<infinity><..<M} \<inter> real_of_ereal ` {N<..<\<infinity>}"
  apply safe
  subgoal by force
  subgoal by force
  subgoal for x y z
    by (cases y; cases z) (auto intro!: image_eqI[where x=z] simp: )
  done

lemma real_atLeastGreaterThan_eq: "real_of_ereal ` {N<..<M::ereal} =
   (if N = \<infinity> then {} else
   if N = -\<infinity> then
    (if M = \<infinity> then UNIV
    else if M = -\<infinity> then {}
    else {..< real_of_ereal M})
  else if M = - \<infinity> then {}
  else if M = \<infinity> then {real_of_ereal N<..}
  else {real_of_ereal N <..< real_of_ereal M})"
  apply (subst real_greaterThanLessThan_inter)
  apply (subst real_greaterThanLessThan_minus_infinity_eq)
  apply (subst real_greaterThanLessThan_infinity_eq)
  apply auto
  done

lemma is_interval_real_ereal_oo: "is_interval (real_of_ereal ` {N<..<M::ereal})"
  by (auto simp: real_atLeastGreaterThan_eq is_interval_empty is_interval_univ
    is_interval_Ioo is_interval_Iio is_interval_Ioi)

lemma is_interval_ball_real: fixes a b::real shows "is_interval (ball a b)"
  by (metis connected_ball is_interval_connected_1)

lemma real_image_ereal_ivl:
  fixes a b::ereal
  shows
  "real_of_ereal ` {a<..<b} =
  (if a < b then (if a = - \<infinity> then if b = \<infinity> then UNIV else {..<real_of_ereal b}
  else if b = \<infinity> then {real_of_ereal a<..} else {real_of_ereal a <..< real_of_ereal b}) else {})"
  by (cases a; cases b; simp add: real_atLeastGreaterThan_eq not_less)


lemma fixes a b c::ereal
  shows not_inftyI: "a < b \<Longrightarrow> b < c \<Longrightarrow> abs b \<noteq> \<infinity>"
  by force

lemma
  interval_neqs:
  fixes r s t::real
  shows "{r<..<s} \<noteq> {t<..}"
    and "{r<..<s} \<noteq> {..<t}"
    and "{r<..<ra} \<noteq> UNIV"
    and "{r<..} \<noteq> {..<s}"
    and "{r<..} \<noteq> UNIV"
    and "{..<r} \<noteq> UNIV"
    and "{} \<noteq> {r<..}"
    and "{} \<noteq> {..<r}"
  subgoal
    by (metis dual_order.strict_trans greaterThanLessThan_iff greaterThan_iff gt_ex not_le order_refl)
  subgoal
    by (metis (no_types, hide_lams) greaterThanLessThan_empty_iff greaterThanLessThan_iff gt_ex
        lessThan_iff minus_minus neg_less_iff_less not_less order_less_irrefl)
  subgoal by force
  subgoal
    by (metis greaterThanLessThan_empty_iff greaterThanLessThan_eq greaterThan_iff inf.idem
        lessThan_iff lessThan_non_empty less_irrefl not_le)
  subgoal by force
  subgoal by force
  subgoal using greaterThan_non_empty by blast
  subgoal using lessThan_non_empty by blast
  done

lemma greaterThanLessThan_eq_iff:
  fixes r s t u::real
  shows "({r<..<s} = {t<..<u}) = (r \<ge> s \<and> u \<le> t \<or> r = t \<and> s = u)"
  by (metis cInf_greaterThanLessThan cSup_greaterThanLessThan greaterThanLessThan_empty_iff not_le)

lemma real_of_ereal_image_greaterThanLessThan_iff:
  "real_of_ereal ` {a <..< b} = real_of_ereal ` {c <..< d} \<longleftrightarrow> (a \<ge> b \<and> c \<ge> d \<or> a = c \<and> b = d)"
  unfolding real_atLeastGreaterThan_eq
  by (cases a; cases b; cases c; cases d;
    simp add: greaterThanLessThan_eq_iff interval_neqs interval_neqs[symmetric])

lemma uminus_image_real_of_ereal_image_greaterThanLessThan:
  "uminus ` real_of_ereal ` {l <..< u} = real_of_ereal ` {-u <..< -l}"
  by (force simp: algebra_simps ereal_less_uminus_reorder
    ereal_uminus_less_reorder intro: image_eqI[where x="-x" for x])

lemma add_image_real_of_ereal_image_greaterThanLessThan:
  "op + c ` real_of_ereal ` {l <..< u} = real_of_ereal ` {c + l <..< c + u}"
  apply safe
  subgoal for x
    using ereal_less_add[of c]
    by (force simp: real_of_ereal_add add.commute)
  subgoal for _ x
    by (force simp: add.commute real_of_ereal_minus ereal_minus_less ereal_less_minus
      intro: image_eqI[where x="x - c"])
  done

lemma add2_image_real_of_ereal_image_greaterThanLessThan:
  "(\<lambda>x. x + c) ` real_of_ereal ` {l <..< u} = real_of_ereal ` {l + c <..< u + c}"
  using add_image_real_of_ereal_image_greaterThanLessThan[of c l u]
  by (metis add.commute image_cong)

lemma minus_image_real_of_ereal_image_greaterThanLessThan:
  "op - c ` real_of_ereal ` {l <..< u} = real_of_ereal ` {c - u <..< c - l}"
  (is "?l = ?r")
proof -
  have "?l = op + c ` uminus ` real_of_ereal ` {l <..< u}" by auto
  also note uminus_image_real_of_ereal_image_greaterThanLessThan
  also note add_image_real_of_ereal_image_greaterThanLessThan
  finally show ?thesis by (simp add: minus_ereal_def)
qed

lemma real_ereal_bound_lemma_up:
  assumes "s \<in> real_of_ereal ` {a<..<b}"
  assumes "t \<notin> real_of_ereal ` {a<..<b}"
  assumes "s \<le> t"
  shows "b \<noteq> \<infinity>"
  using assms
  apply (cases b)
  subgoal by force
  subgoal by (metis PInfty_neq_ereal(2) assms dual_order.strict_trans1 ereal_infty_less(1)
    ereal_less_ereal_Ex greaterThanLessThan_empty_iff greaterThanLessThan_iff greaterThan_iff
    image_eqI less_imp_le linordered_field_no_ub not_less order_trans
    real_greaterThanLessThan_infinity_eq real_image_ereal_ivl real_of_ereal.simps(1))
  subgoal by force
  done

lemma real_ereal_bound_lemma_down:
  assumes "s \<in> real_of_ereal ` {a<..<b}"
  assumes "t \<notin> real_of_ereal ` {a<..<b}"
  assumes "t \<le> s"
  shows "a \<noteq> - \<infinity>"
  using assms
  apply (cases b)
  subgoal
    apply safe
    using assms(1)
    apply (auto simp: real_greaterThanLessThan_minus_infinity_eq)
    done
  subgoal by (auto simp: real_greaterThanLessThan_minus_infinity_eq)
  subgoal by auto
  done


subsection \<open>Euclidean Components\<close>

lemma sqrt_le_rsquare:
  assumes "\<bar>x\<bar> \<le> sqrt y"
  shows "x\<^sup>2 \<le> y"
  using assms real_sqrt_le_iff[of "x\<^sup>2"] by simp

lemma sum_ge_element:
  fixes f::"'a \<Rightarrow> ('b::ordered_comm_monoid_add)"
  assumes "finite s"
  assumes "i \<in> s"
  assumes "\<And>i. i \<in> s \<Longrightarrow> f i \<ge> 0"
  assumes "el = f i"
  shows "el \<le> sum f s"
proof -
  have "el = sum f {i}" by (simp add: assms)
  also have "... \<le> sum f s" using assms by (intro sum_mono2) auto
  finally show ?thesis .
qed

lemma norm_nth_le:
  fixes x::"'a::euclidean_space"
  assumes "i \<in> Basis"
  shows "norm (x \<bullet> i) \<le> norm x"
  unfolding norm_conv_dist euclidean_dist_l2[of x] setL2_def
  by (auto intro!: real_le_rsqrt sum_ge_element assms)

lemma norm_Pair_le:
  shows "norm (x, y) \<le> norm x + norm y"
  unfolding norm_Pair
  by (metis norm_ge_zero sqrt_sum_squares_le_sum)

lemma norm_Pair_ge1:
  shows "norm x \<le> norm (x, y)"
  unfolding norm_Pair
  by (metis real_sqrt_sum_squares_ge1)

lemma norm_Pair_ge2:
  shows "norm y \<le> norm (x, y)"
  unfolding norm_Pair
  by (metis real_sqrt_sum_squares_ge2)

subsection \<open>Operator Norm\<close>

lemma onorm_sum_le:
  assumes "finite S"
  assumes "\<And>s. s \<in> S \<Longrightarrow> bounded_linear (f s)"
  shows "onorm (\<lambda>x. sum (\<lambda>s. f s x) S) \<le> sum (\<lambda>s. onorm (f s)) S"
  using assms
  by (induction) (auto simp: onorm_zero intro!: onorm_triangle_le bounded_linear_sum)

lemma onorm_componentwise:
  assumes "bounded_linear f"
  shows "onorm f \<le> (\<Sum>i\<in>Basis. norm (f i))"
proof -
  {
    fix i::'a
    assume "i \<in> Basis"
    hence "onorm (\<lambda>x. (x \<bullet> i) *\<^sub>R f i) \<le> onorm (\<lambda>x. (x \<bullet> i)) * norm (f i)"
      by (auto intro!: onorm_scaleR_left_lemma)
    also have "\<dots> \<le>  norm i * norm (f i)"
      by (rule mult_right_mono)
        (auto simp: ac_simps Cauchy_Schwarz_ineq2 intro!: onorm_le)
    finally have "onorm (\<lambda>x. (x \<bullet> i) *\<^sub>R f i) \<le> norm (f i)" using \<open>i \<in> Basis\<close>
      by simp
  } hence "onorm (\<lambda>x. \<Sum>i\<in>Basis. (x \<bullet> i) *\<^sub>R f i) \<le> (\<Sum>i\<in>Basis. norm (f i))"
    by (auto intro!: order_trans[OF onorm_sum_le] bounded_linear_scaleR_const
      sum_mono)
  also have "(\<lambda>x. \<Sum>i\<in>Basis. (x \<bullet> i) *\<^sub>R f i) = (\<lambda>x. f (\<Sum>i\<in>Basis. (x \<bullet> i) *\<^sub>R i))"
    by (simp add: linear_sum bounded_linear.linear assms linear_simps)
  also have "\<dots> = f"
    by (simp add: euclidean_representation)
  finally show ?thesis .
qed

lemmas onorm_componentwise_le = order_trans[OF onorm_componentwise]


subsection \<open>Limits\<close>

lemma Zfun_ident: "Zfun (\<lambda>x::'a::real_normed_vector. x) (at 0)"
  using tendsto_ident_at[of "0::'a" UNIV, simplified tendsto_Zfun_iff]
  by simp

lemma not_in_closure_trivial_limitI:
  "x \<notin> closure s \<Longrightarrow> trivial_limit (at x within s)"
  using not_trivial_limit_within[of x s]
  by safe (metis Diff_empty Diff_insert0 closure_subset contra_subsetD)

lemma tendsto_If:
  assumes tendsto:
    "x \<in> s \<union> (closure s \<inter> closure t) \<Longrightarrow>
      (f \<longlongrightarrow> l x) (at x within s \<union> (closure s \<inter> closure t))"
    "x \<in> t \<union> (closure s \<inter> closure t) \<Longrightarrow>
      (g \<longlongrightarrow> l x) (at x within t \<union> (closure s \<inter> closure t))"
  assumes "x \<in> s \<union> t"
  shows "((\<lambda>x. if x \<in> s then f x else g x) \<longlongrightarrow> l x) (at x within s \<union> t)"
proof (rule Lim_Un, safe intro!: topological_tendstoI)
  fix S::"'b set"
  assume S: "open S"
  assume l: "l x \<in> S"
  let ?thesis =
    "\<lambda>t. eventually (\<lambda>x. (if x \<in> s then f x else g x) \<in> S) (at x within t)"
  {
    assume x: "x \<in> s" hence "x \<in> s \<union> (closure s \<inter> closure t)" by auto
    from topological_tendstoD[OF tendsto(1)[OF this] S l]
    have "?thesis s" unfolding eventually_at_filter
      by eventually_elim auto
  } moreover {
    assume "x \<notin> closure s"
    then have "?thesis s"
      by (metis (no_types) not_in_closure_trivial_limitI trivial_limit_eventually)
  } moreover {
    assume s: "x \<in> closure s" "x \<notin> s"
    hence t: "x \<in> t" "x \<in> closure t"
      using assms closure_subset[of t] by auto
    from s t have c1: "x \<in> s \<union> (closure s \<inter> closure t)"
      and c2: "x \<in> t \<union> (closure s \<inter> closure t)"by auto
    from topological_tendstoD[OF tendsto(1)[OF c1] S l]
      topological_tendstoD[OF tendsto(2)[OF c2] S l]
    have "?thesis s"
      unfolding eventually_at_filter
      by eventually_elim auto
  } ultimately show "?thesis s" by blast
  {
    assume x: "x \<in> closure s" "x \<in> closure t"
    hence c1: "x \<in> s \<union> (closure s \<inter> closure t)"
      and c2: "x \<in> t \<union> (closure s \<inter> closure t)"
      by auto
    from topological_tendstoD[OF tendsto(1)[OF c1] S l]
      topological_tendstoD[OF tendsto(2)[OF c2] S l]
    have "?thesis t" unfolding eventually_at_filter
      by eventually_elim auto
  } moreover {
    assume "x \<notin> closure t"
    then have "?thesis t"
      by (metis (no_types) not_in_closure_trivial_limitI trivial_limit_eventually)
  } moreover {
    assume c: "x \<notin> closure s"
    hence c': "x \<in> t \<union> (closure s \<inter> closure t)"
      using assms closure_subset[of s]
      by auto
    from c have "eventually (\<lambda>x. x \<in> - closure s) (at x within t)"
      by (intro topological_tendstoD) (auto intro: tendsto_ident_at)
    hence "?thesis t"
      using topological_tendstoD[OF tendsto(2)[OF c'] S l] closure_subset[of s]
      unfolding eventually_at_filter
      by eventually_elim (auto; metis closure_subset contra_subsetD)
  } ultimately show "?thesis t" by blast
qed

lemma
  tendsto_within_nhd:
  assumes tendsto: "(f \<longlongrightarrow> l) (at x within Y)"
  assumes nhd: "x \<in> T" "open T" "T \<inter> X \<subseteq> Y"
  shows "(f \<longlongrightarrow> l) (at x within X)"
proof (rule topological_tendstoI)
  fix S assume S: "open S" "l \<in> S"
  have "\<forall>\<^sub>F x in at x within X. x \<in> T"
    by (auto intro!: topological_tendstoD nhd)
  moreover
  have "\<forall>\<^sub>F x in at x within X. x \<in> X"
    by (simp add: eventually_at_filter)
  ultimately
  have "\<forall>\<^sub>F x in at x within X. x \<in> Y"
    by eventually_elim (insert nhd, auto)
  moreover
  from topological_tendstoD[OF tendsto S]
  have "\<forall>\<^sub>F x in at x within Y. f x \<in> S" .
  ultimately
  show "\<forall>\<^sub>F x in at x within X. f x \<in> S"
    unfolding eventually_at_filter
    by eventually_elim blast
qed

lemma eventually_open_cball:
  assumes "open X"
  assumes "x \<in> X"
  shows "eventually (\<lambda>e. cball x e \<subseteq> X) (at_right 0)"
proof -
  from open_contains_cball_eq[OF assms(1)] assms(2)
  obtain e where "e > 0" "cball x e \<subseteq> X" by auto
  thus ?thesis
    by (auto simp: eventually_at dist_real_def mem_cball intro!: exI[where x=e])
qed

lemma filterlim_times_real_le:
  fixes c::real
  assumes "c > 0"
  shows "filtermap (op * c) (at_right 0) \<le> at_right 0"
  unfolding filterlim_def
proof (rule filter_leI)
  fix P::"real\<Rightarrow>bool"
  assume "eventually P (at_right 0)"
  then obtain d where d: "d > 0" "\<And>x. x > 0 \<Longrightarrow> x < d \<Longrightarrow> P x"
    by (auto simp: eventually_at dist_real_def)
  then show "eventually P (filtermap (op * c) (at_right 0))"
    by (auto simp: eventually_filtermap eventually_at intro!: exI[where x="d / c"]
      simp: \<open>0 < c\<close> dist_real_def field_simps)
qed

lemma filtermap_times_real:
  assumes "(c::real) > 0"
  shows "filtermap (op * c) (at_right 0) = at_right 0"
proof (rule antisym)
  have "filtermap (op * (inverse c)) (at_right 0) \<le> at_right 0"
    by (rule filterlim_times_real_le) (auto simp: assms)
  also have "\<dots> = filtermap (op * (inverse c)) (filtermap (op * c) (at_right 0))"
    using \<open>c > 0\<close>
    by (simp add: filtermap_filtermap field_simps)
  finally
  show "at_right 0 \<le> filtermap (op * c) (at_right 0)"
    using assms
    by (subst (asm) filtermap_mono_strong) (auto intro!: inj_onI)
qed (intro filterlim_times_real_le assms)


lemma eventually_at_shift_zero:
  fixes x::"'b::real_normed_vector"
  shows "eventually (\<lambda>h. P (x + h)) (at 0) \<longleftrightarrow> eventually P (at x)"
proof -
  have "eventually (\<lambda>h. P (x + h)) (at 0) \<longleftrightarrow>
    eventually P (filtermap (op + x) (at 0))"
    by (simp add: eventually_filtermap)
  also have "filtermap (op + x) (at 0) = at x"
    using filtermap_at_shift[of "-x" 0]
    by (subst add.commute[abs_def]) (simp add: )
  finally show ?thesis .
qed

lemma eventually_at_fst:
  assumes "eventually P (at (fst x))"
  assumes "P (fst x)"
  shows "eventually (\<lambda>h. P (fst h)) (at x)"
  using assms
  unfolding eventually_at_topological
  by (metis open_vimage_fst rangeI range_fst vimageE vimageI)

lemma eventually_at_snd:
  assumes "eventually P (at (snd x))"
  assumes "P (snd x)"
  shows "eventually (\<lambda>h. P (snd h)) (at x)"
  using assms
  unfolding eventually_at_topological
  by (metis open_vimage_snd rangeI range_snd vimageE vimageI)

lemma eventually_at_in_ball: "d > 0 \<Longrightarrow> eventually (\<lambda>y. y \<in> ball x0 d) (at x0)"
  by (auto simp: eventually_at dist_commute mem_ball intro!: exI[where x=d])

lemma seq_harmonic': "((\<lambda>n. 1 / n) \<longlongrightarrow> 0) sequentially"
  using seq_harmonic
  by (simp add: inverse_eq_divide)

lemma filterlim_real_at_infinity_sequentially[tendsto_intros]:
     "filterlim real at_infinity sequentially"
  by (simp add: filterlim_at_top_imp_at_infinity filterlim_real_sequentially)


subsection \<open>Continuity\<close>

lemma continuous_on_fst[continuous_intros]: "continuous_on X fst"
  unfolding continuous_on_def
  by (intro ballI tendsto_intros)

lemma continuous_on_snd[continuous_intros]: "continuous_on X snd"
  unfolding continuous_on_def
  by (intro ballI tendsto_intros)

lemma continuous_at_fst[continuous_intros]:
  fixes x::"'a::euclidean_space \<times> 'b::euclidean_space"
  shows "continuous (at x) fst"
  unfolding continuous_def netlimit_at
  by (intro tendsto_intros)

lemma continuous_at_snd[continuous_intros]:
  fixes x::"'a::euclidean_space \<times> 'b::euclidean_space"
  shows "continuous (at x) snd"
  unfolding continuous_def netlimit_at
  by (intro tendsto_intros)

lemma continuous_at_Pair[continuous_intros]:
  fixes x::"'a::euclidean_space \<times> 'b::euclidean_space"
  assumes "continuous (at x) f"
  assumes "continuous (at x) g"
  shows "continuous (at x) (\<lambda>x. (f x, g x))"
  using assms unfolding continuous_def
  by (intro tendsto_intros)

lemma continuous_on_Pair[continuous_intros]:
  assumes "continuous_on S f"
  assumes "continuous_on S g"
  shows "continuous_on S (\<lambda>x. (f x, g x))"
  using assms unfolding continuous_on_def
  by (auto intro: tendsto_intros)

lemma continuous_Sigma:
  assumes defined: "y \<in> Pi T X"
  assumes f_cont: "continuous_on (Sigma T X) (\<lambda>(t, x). f t x)"
  assumes y_cont: "continuous_on T y"
  shows "continuous_on T (\<lambda>x. f x (y x))"
  using
    defined
    continuous_on_compose2[OF
      continuous_on_subset[where t="(\<lambda>x. (x, y x)) ` T", OF f_cont]
      continuous_on_Pair[OF continuous_on_id y_cont]]
  by auto

lemma IVT'_closed_segment_real:
  fixes f :: "real \<Rightarrow> real"
  assumes y: "y \<in> closed_segment (f a) (f b)"
  assumes *: "continuous_on (closed_segment a b) f"
  shows "\<exists>x \<in> closed_segment a b. f x = y"
proof -
  {
    assume "a \<le> b"
    {
      assume "f a \<le> f b"
      hence ?thesis
        using IVT'[of f a y b] \<open>a \<le> b\<close> assms by (auto simp: closed_segment_real)
    } moreover {
      assume "f b < f a"
      hence ?thesis
        using IVT'[of "-f" a "-y" b] \<open>a \<le> b\<close> assms
        by (force simp: closed_segment_real intro!: continuous_on_minus)
    } ultimately have ?thesis by arith
  } moreover {
    assume "b < a"
    {
      assume "f b < f a"
      hence ?thesis
        using IVT'[of f b y a] \<open>b < a\<close> assms by (auto simp: closed_segment_real)
    } moreover {
      assume "f b \<ge> f a"
      hence ?thesis
        using IVT'[of "-f" b "-y" a] \<open>b < a\<close> assms
        by (force simp: closed_segment_real intro!: continuous_on_minus)
    } ultimately have ?thesis by arith
  } ultimately show ?thesis by arith
qed

lemma continuous_on_subset_comp:
  "continuous_on s f \<Longrightarrow> continuous_on t g \<Longrightarrow> g ` t \<subseteq> s \<Longrightarrow> continuous_on t (\<lambda>x. f (g x))"
  by (rule continuous_on_compose2)

lemma
  continuous_on_blinfun_componentwise:
  fixes f:: "'d::t2_space \<Rightarrow> 'e::euclidean_space \<Rightarrow>\<^sub>L 'f::real_normed_vector"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> continuous_on s (\<lambda>x. f x i)"
  shows "continuous_on s f"
  using assms
  by (auto intro!: continuous_at_imp_continuous_on intro!: tendsto_componentwise1
    simp: continuous_on_eq_continuous_within continuous_def)

lemma continuous_on_compose_Pair:
assumes f: "continuous_on (Sigma A B) (\<lambda>(a, b). f a b)"
assumes g: "continuous_on C g"
assumes h: "continuous_on C h"
assumes subset: "\<And>c. c \<in> C \<Longrightarrow> g c \<in> A" "\<And>c. c \<in> C \<Longrightarrow> h c \<in> B (g c)"
shows "continuous_on C (\<lambda>c. f (g c) (h c))"
using continuous_on_compose2[OF f continuous_on_Pair[OF g h]] subset
by auto

lemma continuous_on_compact_product_lemma:\<comment>\<open>TODO is this useful? it is just explicit uniform continuity!\<close>
  fixes A::"'a::metric_space set" and B::"'b::metric_space set"
  assumes "continuous_on (A \<times> X) (\<lambda>(a, x). f a x)"
  assumes "compact A" "compact X"
  assumes "e > 0"
  shows "\<exists>d>0. \<forall>a \<in> A. \<forall>x \<in> X. \<forall>y \<in> X. dist x y < d \<longrightarrow> dist (f a x) (f a y) < e"
proof -
  have "uniformly_continuous_on (A \<times> X) (\<lambda>(a, x). f a x)"
    by (intro compact_uniformly_continuous compact_Times assms)
  then have "\<forall>e>0. \<exists>d>0. \<forall>a\<in>A. \<forall>x\<in>X. \<forall>b\<in>A. \<forall>y\<in>X. dist (b, y) (a, x) < d \<longrightarrow> dist (f b y) (f a x) < e"
    by (auto simp: uniformly_continuous_on_def)

  from this[rule_format, OF \<open>0 < e\<close>]
  obtain d where d: "0 < d" "\<And>a b x y. a\<in>A \<Longrightarrow> x\<in>X \<Longrightarrow> b\<in>A \<Longrightarrow> y\<in>X \<Longrightarrow> dist (b, y) (a, x) < d \<Longrightarrow> dist (f b y) (f a x) < e"
    by blast
  show ?thesis
    by (rule exI[where x=d]) (auto intro!: d simp: dist_prod_def)
qed

lemma has_derivative_in_compose2:\<comment>\<open>TODO: should there be sth like \<open>op has_derivative_on\<close>?\<close>
  assumes "\<And>x. x \<in> t \<Longrightarrow> (g has_derivative g' x) (at x within t)"
  assumes "f ` s \<subseteq> t" "x \<in> s"
  assumes "(f has_derivative f') (at x within s)"
  shows "((\<lambda>x. g (f x)) has_derivative (\<lambda>y. g' (f x) (f' y))) (at x within s)"
  using assms
  by (auto intro: has_derivative_within_subset intro!: has_derivative_in_compose[of f f' x s g])

lemma has_derivative_singletonI:
  "bounded_linear g \<Longrightarrow> (f has_derivative g) (at x within {x})"
  by (rule has_derivativeI_sandwich[where e=1])
    (auto intro!: bounded_linear_scaleR_left)

lemma vector_derivative_eq_rhs:
  "(f has_vector_derivative f') F \<Longrightarrow> f' = g' \<Longrightarrow> (f has_vector_derivative g') F"
  by simp

lemma has_derivative_transform:
  assumes "x \<in> s" "\<And>x. x \<in> s \<Longrightarrow> g x = f x"
  assumes "(f has_derivative f') (at x within s)"
  shows "(g has_derivative f') (at x within s)"
  using assms
  by (intro has_derivative_transform_within[OF _ zero_less_one, where g=g]) auto

lemma has_derivative_within_If_eq:
  "((\<lambda>x. if P x then f x else g x) has_derivative f') (at x within s) =
    (bounded_linear f' \<and>
     ((\<lambda>y.(if P y then (f y - ((if P x then f x else g x) + f' (y - x)))/\<^sub>R norm (y - x)
           else (g y - ((if P x then f x else g x) + f' (y - x)))/\<^sub>R norm (y - x)))
      \<longlongrightarrow> 0) (at x within s))"
  (is "_ = (_ \<and> (?if \<longlongrightarrow> 0) _)")
proof -
  have "(\<lambda>y. (1 / norm (y - x)) *\<^sub>R
           ((if P y then f y else g y) -
            ((if P x then f x else g x) + f' (y - x)))) = ?if"
    by (auto simp: inverse_eq_divide)
  thus ?thesis by (auto simp: has_derivative_within)
qed

lemma has_derivative_If:
  assumes f': "x \<in> s \<union> (closure s \<inter> closure t) \<Longrightarrow>
    (f has_derivative f' x) (at x within s \<union> (closure s \<inter> closure t))"
  assumes g': "x \<in> t \<union> (closure s \<inter> closure t) \<Longrightarrow>
    (g has_derivative g' x) (at x within t \<union> (closure s \<inter> closure t))"
  assumes connect: "x \<in> closure s \<Longrightarrow> x \<in> closure t \<Longrightarrow> f x = g x"
  assumes connect': "x \<in> closure s \<Longrightarrow> x \<in> closure t \<Longrightarrow> f' x = g' x"
  assumes x_in: "x \<in> s \<union> t"
  shows "((\<lambda>x. if x \<in> s then f x else g x) has_derivative
      (if x \<in> s then f' x else g' x)) (at x within (s \<union> t))"
proof -
  from f' x_in interpret f': bounded_linear "if x \<in> s then f' x else (\<lambda>x. 0)"
    by (auto simp add: has_derivative_within)
  from g' interpret g': bounded_linear "if x \<in> t then g' x else (\<lambda>x. 0)"
    by (auto simp add: has_derivative_within)
  have bl: "bounded_linear (if x \<in> s then f' x else g' x)"
    using f'.scaleR f'.bounded f'.add g'.scaleR g'.bounded g'.add x_in
    by (unfold_locales; force)
  show ?thesis
    using f' g' closure_subset[of t] closure_subset[of s]
    unfolding has_derivative_within_If_eq
    by (intro conjI bl tendsto_If x_in)
      (auto simp: has_derivative_within inverse_eq_divide connect connect' set_mp)
qed

lemma has_vector_derivative_If:
  assumes x_in: "x \<in> s \<union> t"
  assumes "u = s \<union> t"
  assumes f': "x \<in> s \<union> (closure s \<inter> closure t) \<Longrightarrow>
    (f has_vector_derivative f' x) (at x within s \<union> (closure s \<inter> closure t))"
  assumes g': "x \<in> t \<union> (closure s \<inter> closure t) \<Longrightarrow>
    (g has_vector_derivative g' x) (at x within t \<union> (closure s \<inter> closure t))"
  assumes connect: "x \<in> closure s \<Longrightarrow> x \<in> closure t \<Longrightarrow> f x = g x"
  assumes connect': "x \<in> closure s \<Longrightarrow> x \<in> closure t \<Longrightarrow> f' x = g' x"
  shows "((\<lambda>x. if x \<in> s then f x else g x) has_vector_derivative
    (if x \<in> s then f' x else g' x)) (at x within u)"
  unfolding has_vector_derivative_def assms
  using x_in
  apply (intro has_derivative_If[where ?f' = "\<lambda>x a. a *\<^sub>R f' x" and ?g' = "\<lambda>x a. a *\<^sub>R g' x",
        THEN has_derivative_eq_rhs])
  subgoal by (rule f'[unfolded has_vector_derivative_def]; assumption)
  subgoal by (rule g'[unfolded has_vector_derivative_def]; assumption)
  by (auto simp: assms)


subsection \<open>Derivatives\<close>

text \<open>TODO: include this into the attribute \<open>derivative_intros\<close>?\<close>

lemma DERIV_compose_FDERIV:
  fixes f::"real\<Rightarrow>real"
  assumes "DERIV f (g x) :> f'"
  assumes "(g has_derivative g') (at x within s)"
  shows "((\<lambda>x. f (g x)) has_derivative (\<lambda>x. g' x * f')) (at x within s)"
  using assms has_derivative_compose[of g g' x s f "op * f'"]
  by (auto simp: has_field_derivative_def ac_simps)

lemmas has_derivative_sin[derivative_intros] = DERIV_sin[THEN DERIV_compose_FDERIV]
  and  has_derivative_cos[derivative_intros] = DERIV_cos[THEN DERIV_compose_FDERIV]
  and  has_derivative_exp[derivative_intros] = DERIV_exp[THEN DERIV_compose_FDERIV]
  and  has_derivative_ln[derivative_intros] = DERIV_ln[THEN DERIV_compose_FDERIV]
  and  has_derivative_tan[derivative_intros] = DERIV_tan[THEN DERIV_compose_FDERIV]

lemma has_derivative_continuous_on:
  "(\<And>x. x \<in> s \<Longrightarrow> (f has_derivative f' x) (at x within s)) \<Longrightarrow> continuous_on s f"
  by (auto intro!: differentiable_imp_continuous_on differentiableI simp: differentiable_on_def)

lemma has_vector_derivative_continuous_on:
  "(\<And>x. x \<in> s \<Longrightarrow> (f has_vector_derivative f' x) (at x within s)) \<Longrightarrow> continuous_on s f"
  by (auto intro!: differentiable_imp_continuous_on differentiableI simp: has_vector_derivative_def
    differentiable_on_def)

lemma has_vector_derivative_imp:
  assumes "x \<in> s"
  assumes "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  assumes f'g':"f' = g'"
  assumes "x = y" "s = t"
  assumes f': "(f has_vector_derivative f') (at x within s)"
  shows "(g has_vector_derivative g') (at y within t)"
  unfolding has_vector_derivative_def has_derivative_within'
proof (safe)
  fix e::real
  assume "0 < e"
  with assms f' have "\<exists>d>0. \<forall>x'\<in>s.
    0 < norm (x' - x) \<and> norm (x' - x) < d \<longrightarrow>
    norm (g x' - g y - (x' - y) *\<^sub>R g') / norm (x' - x) < e"
    by (auto simp add: has_vector_derivative_def has_derivative_within')
  with assms show "\<exists>d>0. \<forall>x'\<in>t. 0 < norm (x' - y) \<and> norm (x' - y) < d \<longrightarrow>
    norm (g x' - g y - (x' - y) *\<^sub>R g') / norm (x' - y) < e"
    by auto
next
  show "bounded_linear (\<lambda>x. x *\<^sub>R g')"
    using
      has_derivative_bounded_linear[OF f'[simplified has_vector_derivative_def],
        simplified f'g']
    .
qed

lemma has_vector_derivative_cong:
  assumes "x \<in> s"
  assumes "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  assumes f'g':"f' = g'"
  assumes "x = y" "s = t"
  shows "(f has_vector_derivative f') (at x within s) =
    (g has_vector_derivative g') (at y within t)"
  using has_vector_derivative_imp assms by metis

lemma has_derivative_within_union:
  assumes "(f has_derivative g) (at x within s)"
  assumes "(f has_derivative g) (at x within t)"
  shows  "(f has_derivative g) (at x within (s \<union> t))"
proof cases
  assume "at x within (s \<union> t) = bot"
  thus ?thesis using assms by (simp_all add: has_derivative_def)
next
  assume st: "at x within (s \<union> t) \<noteq> bot"
  thus ?thesis
    using assms
    by (cases "at x within s = bot";
      cases "at x within t = bot";
      auto simp: Lim_within_union has_derivative_def netlimit_within)
qed

lemma has_vector_derivative_within_union:
  assumes "(f has_vector_derivative g) (at x within s)"
  assumes "(f has_vector_derivative g) (at x within t)"
  shows  "(f has_vector_derivative g) (at x within (s \<union> t))"
using assms
by (auto simp: has_vector_derivative_def intro: has_derivative_within_union)

lemma vector_derivative_within_closed_interval:
  fixes f::"real \<Rightarrow> 'a::euclidean_space"
  assumes "a < b" and "x \<in> {a .. b}"
  assumes "(f has_vector_derivative f') (at x within {a .. b})"
  shows "vector_derivative f (at x within {a .. b}) = f'"
  using assms vector_derivative_within_closed_interval
  by fastforce

lemma has_vector_derivative_singletonI:
  "(y has_vector_derivative y') (at t0 within {t0})"
  by (auto simp: has_vector_derivative_def intro!: has_derivative_singletonI bounded_linear_intros)

lemma has_derivative_If_in_closed:
  assumes f':"x \<in> s \<Longrightarrow> (f has_derivative f' x) (at x within s)"
  assumes g':"x \<in> t \<Longrightarrow> (g has_derivative g' x) (at x within t)"
  assumes connect: "x \<in> s \<Longrightarrow> x \<in> t \<Longrightarrow> f x = g x" "x \<in> s \<Longrightarrow> x \<in> t \<Longrightarrow> f' x = g' x"
  assumes "closed t" "closed s" "x \<in> s \<union> t"
  shows "((\<lambda>x. if x \<in> s then f x else g x) has_derivative (if x \<in> s then f' x else g' x)) (at x within (s \<union> t))"
  (is "(?if has_derivative ?if') _")
  unfolding has_derivative_within
proof (safe intro!: tendstoI)
  fix e::real assume "0 < e"
  let ?D = "\<lambda>x f f' y. (1 / norm (y - x)) *\<^sub>R (f y - (f x + f' (y - x)))"
  have f': "x \<in> s \<Longrightarrow> ((?D x f (f' x)) \<longlongrightarrow> 0) (at x within s)"
    and g': "x \<in> t \<Longrightarrow> ((?D x g (g' x)) \<longlongrightarrow> 0) (at x within t)"
    using f' g' by (auto simp: has_vector_derivative_def has_derivative_within)
  let ?thesis = "eventually (\<lambda>y. dist (?D x ?if ?if' y) 0 < e) (at x within s \<union> t)"
  {
    assume "x \<in> s" "x \<in> t"
    from tendstoD[OF f'[OF \<open>x \<in> s\<close>] \<open>0 < e\<close>] tendstoD[OF g'[OF \<open>x \<in> t\<close>] \<open>0 < e\<close>]
    have ?thesis unfolding eventually_at_filter
      by eventually_elim (insert \<open>x \<in> s\<close> \<open>x \<in> t\<close>, auto simp: connect)
  } moreover {
    assume "x \<in> s" "x \<notin> t"
    hence "eventually (\<lambda>x. x \<in> - t) (at x within s \<union> t)" using \<open>closed t\<close>
      by (intro topological_tendstoD) (auto intro: tendsto_ident_at)
    with tendstoD[OF f'[OF \<open>x \<in> s\<close>] \<open>0 < e\<close>] have ?thesis unfolding eventually_at_filter
      by eventually_elim (insert \<open>x \<in> s\<close> \<open>x \<notin> t\<close>, auto simp: connect)
  } moreover {
    assume "x \<notin> s" hence "x \<in> t" using assms by auto
    have "eventually (\<lambda>x. x \<in> - s) (at x within s \<union> t)" using \<open>closed s\<close> \<open>x \<notin> s\<close>
      by (intro topological_tendstoD) (auto intro: tendsto_ident_at)
    with tendstoD[OF g'[OF \<open>x \<in> t\<close>] \<open>0 < e\<close>] have ?thesis unfolding eventually_at_filter
      by eventually_elim (insert \<open>x \<in> t\<close> \<open>x \<notin> s\<close>, auto simp: connect)
  } ultimately show ?thesis by blast
qed (insert assms, auto intro!: has_derivative_bounded_linear f' g')

lemma linear_continuation:
  assumes f':"x \<in> {a .. b} \<Longrightarrow> (f has_vector_derivative f' x) (at x within {a .. b})"
  assumes g':"x \<in> {b .. c} \<Longrightarrow> (g has_vector_derivative g' x) (at x within {b .. c})"
  assumes connect: "f b = g b" "f' b = g' b"
  assumes x: "x \<in> {a .. c}"
  assumes abc:"a \<le> b" "b \<le> c"
  shows "((\<lambda>x. if x \<le> b then f x else g x) has_vector_derivative
  (\<lambda>x. if x \<le> b then f' x else g' x) x) (at x within {a .. c})"
  (is "(?h has_vector_derivative ?h' x) _")
proof -
  have un: "{a .. b} \<union> {b .. c} = {a .. c}" using assms by auto
  note has_derivative_If_in_closed[derivative_intros]
  note f'[simplified has_vector_derivative_def, derivative_intros]
  note g'[simplified has_vector_derivative_def, derivative_intros]
  have if': "((\<lambda>x. if x \<in> {a .. b} then f x else g x) has_vector_derivative
    (\<lambda>x. if x \<le> b then f' x else g' x) x) (at x within {a .. b}\<union>{b .. c})"
    unfolding has_vector_derivative_def
    using assms
    apply -
    apply (rule derivative_eq_intros refl | assumption)+
    by auto
  show ?thesis
    unfolding has_vector_derivative_def
    by (rule has_derivative_transform[OF
        x _ if'[simplified un has_vector_derivative_def]])
      simp
qed

lemma Pair_has_vector_derivative:
  assumes "(f has_vector_derivative f') (at x within s)"
    "(g has_vector_derivative g') (at x within s)"
  shows "((\<lambda>x. (f x, g x)) has_vector_derivative (f', g')) (at x within s)"
  using assms
  by (auto simp: has_vector_derivative_def intro!: derivative_eq_intros)

lemma
  has_vector_derivative_at_within_open_subset:
  assumes "x \<in> T \<Longrightarrow> (f has_vector_derivative f' x) (at x within T)"
  assumes "x \<in> S" "open S" "S \<subseteq> T"
  shows "(f has_vector_derivative f' x) (at x)"
proof -
  from at_within_open[OF assms(2,3), symmetric]
  show "(f has_vector_derivative f' x) (at x)"
    using \<open>S \<subseteq> T\<close>
    by (auto intro!: has_vector_derivative_within_subset[OF _ \<open>S \<subseteq> T\<close>] assms)
qed

lemma
  has_vector_derivative_zero_constant:
  assumes "convex s"
  assumes "\<And>x. x \<in> s \<Longrightarrow> (f has_vector_derivative 0) (at x within s)"
  obtains c where "\<And>x. x \<in> s \<Longrightarrow> f x = c"
  using has_derivative_zero_constant[of s f] assms
  by (auto simp: has_vector_derivative_def)


subsection \<open>Differentiability\<close>

lemma differentiable_Pair [simp]:
  "f differentiable at x within s \<Longrightarrow> g differentiable at x within s \<Longrightarrow>
    (\<lambda>x. (f x, g x)) differentiable at x within s"
  unfolding differentiable_def by (blast intro: has_derivative_Pair)

lemma (in bounded_linear)
  differentiable:
  assumes "g differentiable (at x within s)"
  shows " (\<lambda>x. f (g x)) differentiable (at x within s)"
  using assms[simplified frechet_derivative_works]
  by (intro differentiableI) (rule has_derivative)

context begin
private lemmas diff = bounded_linear.differentiable
lemmas differentiable_mult_right[intro] = diff[OF bounded_linear_mult_right]
  and differentiable_mult_left[intro]   = diff[OF bounded_linear_mult_left]
  and differentiable_inner_right[intro] = diff[OF bounded_linear_inner_right]
  and differentiable_inner_left[intro]  = diff[OF bounded_linear_inner_left]
end

lemma (in bounded_bilinear)
  differentiable:
  assumes f: "f differentiable at x within s" and g: "g differentiable at x within s"
  shows "(\<lambda>x. prod (f x) (g x)) differentiable at x within s"
  using assms[simplified frechet_derivative_works]
  by (intro differentiableI) (rule FDERIV)

context begin
private lemmas bdiff = bounded_bilinear.differentiable
lemmas differentiable_mult[intro] = bdiff[OF bounded_bilinear_mult]
  and differentiable_scaleR[intro] = bdiff[OF bounded_bilinear_scaleR]
end

lemma differentiable_transform_within_weak:
  assumes "x \<in> s" "\<And>x'. x'\<in>s \<Longrightarrow> g x' = f x'" "f differentiable at x within s"
  shows "g differentiable at x within s"
  using assms by (intro differentiable_transform_within[OF _ zero_less_one, where g=g]) auto

lemma differentiable_compose_at:
  "f differentiable (at x) \<Longrightarrow> g differentiable (at (f x)) \<Longrightarrow>
  (\<lambda>x. g (f x)) differentiable (at x)"
  unfolding o_def[symmetric]
  by (rule differentiable_chain_at)

lemma differentiable_compose_within:
  "f differentiable (at x within s) \<Longrightarrow>
  g differentiable (at(f x) within (f ` s)) \<Longrightarrow>
  (\<lambda>x. g (f x)) differentiable (at x within s)"
  unfolding o_def[symmetric]
  by (rule differentiable_chain_within)

lemma differentiable_sum[intro, simp]:
  assumes "finite s" "\<forall>a\<in>s. (f a) differentiable net"
  shows "(\<lambda>x. sum (\<lambda>a. f a x) s) differentiable net"
proof -
  from bchoice[OF assms(2)[unfolded differentiable_def]]
  show ?thesis
    by (auto intro!: has_derivative_sum simp: differentiable_def)
qed


subsection \<open>Vector derivative on a set\<close>
  \<comment>\<open>TODO: also for the other derivatives?!\<close>
  \<comment>\<open>TODO: move to repository and rewrite assumptions of common lemmas\<close>

definition
  has_vderiv_on :: "(real \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> real set \<Rightarrow> bool"
  (infix "(has'_vderiv'_on)" 50)
where
  "(f has_vderiv_on f') S \<longleftrightarrow> (\<forall>x \<in> S. (f has_vector_derivative f' x) (at x within S))"

lemma has_vderiv_on_empty[intro, simp]: "(f has_vderiv_on f') {}"
  by (auto simp: has_vderiv_on_def)

lemma vderiv_on_continuous_on: "(f has_vderiv_on f') S \<Longrightarrow> continuous_on S f"
  by (auto intro!: has_vector_derivative_continuous_on simp: has_vderiv_on_def)

lemma has_vderiv_on_cong[cong]:
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x = g x"
  assumes "\<And>x. x \<in> S \<Longrightarrow> f' x = g' x"
  assumes "S = T"
  shows "(f has_vderiv_on f') S = (g has_vderiv_on g') T"
  using assms
  by (auto simp: has_vderiv_on_def cong: has_vector_derivative_cong)

lemma has_vderiv_eq:
  assumes "(f has_vderiv_on f') S"
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x = g x"
  assumes "\<And>x. x \<in> S \<Longrightarrow> f' x = g' x"
  assumes "S = T"
  shows "(g has_vderiv_on g') T"
  using assms by simp

lemma has_vderiv_on_subset:
  assumes "(f has_vderiv_on f') S"
  assumes "T \<subseteq> S"
  shows "(f has_vderiv_on f') T"
  by (meson assms(1) assms(2) contra_subsetD has_vderiv_on_def has_vector_derivative_within_subset)

lemma has_vderiv_on_compose:
  assumes "(f has_vderiv_on f') (g ` T)"
  assumes "(g has_vderiv_on g') T"
  shows "(f o g has_vderiv_on (\<lambda>x. g' x *\<^sub>R f' (g x))) T"
  using assms
  unfolding has_vderiv_on_def
  by (auto intro!: vector_diff_chain_within)

lemma has_vderiv_on_compose':
  assumes "(f has_vderiv_on f') (g ` T)"
  assumes "(g has_vderiv_on g') T"
  shows "((\<lambda>x. f (g x)) has_vderiv_on (\<lambda>x. g' x *\<^sub>R f' (g x))) T"
  using has_vderiv_on_compose[OF assms]
  by simp

lemma has_vderiv_on_compose2:
  assumes "(f has_vderiv_on f') S"
  assumes "(g has_vderiv_on g') T"
  assumes "\<And>t. t \<in> T \<Longrightarrow> g t \<in> S"
  shows "((\<lambda>x. f (g x)) has_vderiv_on (\<lambda>x. g' x *\<^sub>R f' (g x))) T"
  using has_vderiv_on_compose[OF has_vderiv_on_subset[OF assms(1)] assms(2)] assms(3)
  by force

lemma has_vderiv_on_eq_rhs:\<comment>\<open>TODO: integrate intro \<open>derivative_eq_intros\<close>\<close>
  "(f has_vderiv_on g') T \<Longrightarrow> (\<And>x. x \<in> T \<Longrightarrow> g' x = f' x) \<Longrightarrow> (f has_vderiv_on f') T"
  by (auto simp: has_vderiv_on_def)

lemma [THEN has_vderiv_on_eq_rhs, derivative_intros]:
  shows has_vderiv_on_id: "((\<lambda>x. x) has_vderiv_on (\<lambda>x. 1)) T"
    and has_vderiv_on_const: "((\<lambda>x. c) has_vderiv_on (\<lambda>x. 0)) T"
  by (auto simp: has_vderiv_on_def intro!: derivative_eq_intros)

lemma [THEN has_vderiv_on_eq_rhs, derivative_intros]:
  fixes f::"real \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_vderiv_on f') T"
  shows has_vderiv_on_uminus: "((\<lambda>x. - f x) has_vderiv_on (\<lambda>x. - f' x)) T"
  using assms
  by (auto simp: has_vderiv_on_def intro!: derivative_eq_intros)

lemma [THEN has_vderiv_on_eq_rhs, derivative_intros]:
  fixes f g::"real \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_vderiv_on f') T"
  assumes "(g has_vderiv_on g') T"
  shows has_vderiv_on_add: "((\<lambda>x. f x + g x) has_vderiv_on (\<lambda>x. f' x + g' x)) T"
   and has_vderiv_on_diff: "((\<lambda>x. f x - g x) has_vderiv_on (\<lambda>x. f' x - g' x)) T"
  using assms
  by (auto simp: has_vderiv_on_def intro!: derivative_eq_intros)

lemma [THEN has_vderiv_on_eq_rhs, derivative_intros]:
  fixes f::"real \<Rightarrow> real" and g::"real \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_vderiv_on f') T"
  assumes "(g has_vderiv_on g') T"
  shows has_vderiv_on_scaleR: "((\<lambda>x. f x *\<^sub>R g x) has_vderiv_on (\<lambda>x. f x *\<^sub>R g' x + f' x *\<^sub>R g x)) T"
  using assms
  by (auto simp: has_vderiv_on_def has_field_derivative_iff_has_vector_derivative
    intro!: derivative_eq_intros)

lemma [THEN has_vderiv_on_eq_rhs, derivative_intros]:
  fixes f g::"real \<Rightarrow> 'a::real_normed_algebra"
  assumes "(f has_vderiv_on f') T"
  assumes "(g has_vderiv_on g') T"
  shows has_vderiv_on_mult: "((\<lambda>x. f x * g x) has_vderiv_on (\<lambda>x. f x * g' x + f' x * g x)) T"
  using assms
  by (auto simp: has_vderiv_on_def intro!: derivative_eq_intros)

lemma has_vderiv_on_ln[THEN has_vderiv_on_eq_rhs, derivative_intros]:
  fixes g::"real \<Rightarrow> real"
  assumes "\<And>x. x \<in> s \<Longrightarrow> 0 < g x"
  assumes "(g has_vderiv_on g') s"
  shows "((\<lambda>x. ln (g x)) has_vderiv_on (\<lambda>x. g' x / g x)) s"
  using assms
  unfolding has_vderiv_on_def
  by (auto simp: has_vderiv_on_def has_field_derivative_iff_has_vector_derivative[symmetric]
    intro!: derivative_eq_intros)


lemma fundamental_theorem_of_calculus':
  fixes f :: "real \<Rightarrow> 'a::banach"
  shows "a \<le> b \<Longrightarrow> (f has_vderiv_on f') {a .. b} \<Longrightarrow> (f' has_integral (f b - f a)) {a .. b}"
  by (auto intro!: fundamental_theorem_of_calculus simp: has_vderiv_on_def)

lemma has_vderiv_on_If:
  assumes "U = S \<union> T"
  assumes "(f has_vderiv_on f') (S \<union> (closure T \<inter> closure S))"
  assumes "(g has_vderiv_on g') (T \<union> (closure T \<inter> closure S))"
  assumes "\<And>x. x \<in> closure T \<Longrightarrow> x \<in> closure S \<Longrightarrow> f x = g x"
  assumes "\<And>x. x \<in> closure T \<Longrightarrow> x \<in> closure S \<Longrightarrow> f' x = g' x"
  shows "((\<lambda>t. if t \<in> S then f t else g t) has_vderiv_on (\<lambda>t. if t \<in> S then f' t else g' t)) U"
  using assms
  by (auto simp: has_vderiv_on_def ac_simps intro!: has_vector_derivative_If split del: if_split)

lemma has_vderiv_on_singleton: "(y has_vderiv_on y') {t0}"
  by (auto simp: has_vderiv_on_def has_vector_derivative_singletonI)

lemma exists_linear_continuation:
  assumes f':"(f has_vderiv_on f') ({a .. b})"
  shows "\<exists>fc. (\<forall>x. x \<in> {a .. b} \<longrightarrow> (fc has_vector_derivative f' x) (at x)) \<and>
    (\<forall>x. x \<in> {a .. b} \<longrightarrow> fc x = f x)"
proof (rule, safe)
  fix x assume "x \<in> {a .. b}" hence "a \<le> b" by simp
  let ?line = "\<lambda>a x. f a + (x - a) *\<^sub>R f' a"
  let ?fc = "(\<lambda>x. if x \<in> {a .. b} then f x else if x \<in> {..a} then ?line a x else ?line b x)"
  have [simp]:
    "\<And>x. x \<in> {a .. b} \<Longrightarrow> (b \<le> x \<longleftrightarrow> x = b)" "\<And>x. x \<in> {a .. b} \<Longrightarrow> (x \<le> a \<longleftrightarrow> x = a)"
    "\<And>x. x \<le> a \<Longrightarrow> (b \<le> x \<longleftrightarrow> x = b)" using \<open>a \<le> b\<close> by auto
  note [derivative_intros] =
    has_derivative_If_in_closed
    f'[simplified has_vderiv_on_def has_vector_derivative_def, rule_format]
  have "(?fc has_vector_derivative f' x) (at x within {a .. b} \<union> ({..a} \<union> {b..}))"
    using \<open>x \<in> {a .. b}\<close> \<open>a \<le> b\<close>
    by (force intro!: derivative_eq_intros simp: has_vector_derivative_def
      simp del: atMost_iff atLeastAtMost_iff)
  moreover have "{a .. b} \<union> ({..a} \<union> {b..}) = UNIV" by auto
  ultimately show "(?fc has_vector_derivative f' x) (at x)" by simp
  show "?fc x = f x" using \<open>x \<in> {a .. b}\<close> by simp
qed

lemma taylor_up_within:
  assumes INIT: "n>0" "\<And>t. t \<in> {a .. b} \<Longrightarrow> diff 0 t = f t"
  and DERIV: "\<And>m t. m < n \<Longrightarrow> (diff m has_vderiv_on diff (Suc m)) {a .. b}"
  and INTERV: "a \<le> c" "c < b"
  shows "\<exists>t. c < t & t < b &
             f b = (\<Sum>m<n. (diff m c / (fact m)) * (b - c)^m) +
                   (diff n t / (fact n)) * (b - c)^n"
               (is "?taylor f diff")
proof -
  from exists_linear_continuation[OF DERIV]
  have "\<forall>m. \<exists>d'. m < n \<longrightarrow>
    (\<forall>x \<in> {a .. b}. (d' has_vector_derivative diff (Suc m) x) (at x) \<and> d' x = diff m x)"
    by (metis atLeastAtMost_iff)
  then obtain d' where d':
    "\<And>m x. m<n \<Longrightarrow> a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> (d' m has_vector_derivative diff (Suc m) x) (at x)"
    "\<And>m x. m<n \<Longrightarrow> a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> d' m x = diff m x"
    by (metis atLeastAtMost_iff)
  let ?diff = "\<lambda>m. if m = n then diff m else d' m"
  have "?taylor (?diff 0) ?diff" using d'
    by (intro taylor_up[OF _ _ _ \<open>a \<le> c\<close>])
       (auto simp: has_field_derivative_def has_vector_derivative_def
          INIT INTERV mult_commute_abs)
  thus "?taylor f diff" using d' INTERV INIT by auto
qed

lemma taylor_up_within_vector:
  fixes f::"real \<Rightarrow> 'a::euclidean_space"
  assumes INIT: "n>0" "\<And>t. t \<in> {a .. b} \<Longrightarrow> diff 0 t = f t"
  and DERIV: "\<And>m t. m < n \<Longrightarrow> (diff m has_vderiv_on diff (Suc m)) {a .. b}"
  and INTERV: "a \<le> c" "c < b"
  shows "\<exists>t. (\<forall>i\<in>Basis::'a set. c < t i & t i < b) \<and>
    f b = sum (%m. (b - c)^m *\<^sub>R (diff m c /\<^sub>R (fact m))) {..<n} +
      sum (\<lambda>x. (((b - c) ^ n *\<^sub>R diff n (t x) /\<^sub>R (fact n)) \<bullet> x) *\<^sub>R x) Basis"
proof -
  obtain t where t: "\<forall>i\<in>Basis::'a set. t i > c \<and> t i < b \<and>
    f b \<bullet> i =
      (\<Sum>m<n. diff m c \<bullet> i / (fact m) * (b - c) ^ m) +
      diff n (t i) \<bullet> i / (fact n) * (b - c) ^ n"
  proof (atomize_elim, rule bchoice, safe)
    fix i::'a
    assume "i \<in> Basis"
    have DERIV_0: "\<And>t. t \<in> {a .. b} \<Longrightarrow> (diff 0) t \<bullet> i = f t \<bullet> i" using INIT by simp
    have DERIV_Suc: "\<And>m t. m < n \<Longrightarrow> ((\<lambda>t. (diff m) t \<bullet> i) has_vderiv_on (\<lambda>t. diff (Suc m) t \<bullet> i)) {a .. b}"
      using DERIV by (auto intro!: derivative_eq_intros simp: has_vector_derivative_def has_vderiv_on_def)
    from taylor_up_within[OF INIT(1) DERIV_0 DERIV_Suc INTERV]
    show "\<exists>t>c. t < b \<and> f b \<bullet> i =
      (\<Sum>m<n. diff m c \<bullet> i / (fact m) * (b - c) ^ m) +
      diff n t \<bullet> i / (fact n) * (b - c) ^ n" by simp
  qed
  have "f b = (\<Sum>i\<in>Basis. (f b \<bullet> i) *\<^sub>R i)" by (rule euclidean_representation[symmetric])
  also have "\<dots> =
      (\<Sum>i\<in>Basis. ((\<Sum>m<n. (b - c) ^ m *\<^sub>R (diff m c /\<^sub>R (fact m))) \<bullet> i) *\<^sub>R i) +
      (\<Sum>x\<in>Basis. (((b - c) ^ n *\<^sub>R diff n (t x) /\<^sub>R (fact n)) \<bullet> x) *\<^sub>R x)"
    using t
    by (simp add: sum.distrib inner_sum_left inverse_eq_divide algebra_simps)
  finally show ?thesis using t by (auto simp: euclidean_representation)
qed

lemma mvt_very_simple_closed_segmentE:
  fixes f::"real\<Rightarrow>real"
  assumes "(f has_vderiv_on f') (closed_segment a b)"
  obtains y where "y \<in> closed_segment a b"  "f b - f a = (b - a) * f' y"
proof cases
  assume "a \<le> b"
  with mvt_very_simple[of a b f "\<lambda>x i. i *\<^sub>R f' x"] assms
  obtain y where "y \<in> closed_segment a b"  "f b - f a = (b - a) * f' y"
    by (auto simp: has_vector_derivative_def closed_segment_real has_vderiv_on_def)
  thus ?thesis ..
next
  assume "\<not> a \<le> b"
  with mvt_very_simple[of b a f "\<lambda>x i. i *\<^sub>R f' x"] assms
  obtain y where "y \<in> closed_segment a b"  "f b - f a = (b - a) * f' y"
    by (force simp: has_vector_derivative_def has_vderiv_on_def closed_segment_real algebra_simps)
  thus ?thesis ..
qed


lemma mvt_simple_closed_segmentE:
  fixes f::"real\<Rightarrow>real"
  assumes "(f has_vderiv_on f') (closed_segment a b)"
  assumes "a \<noteq> b"
  obtains y where "y \<in> open_segment a b"  "f b - f a = (b - a) * f' y"
proof cases
  assume "a \<le> b"
  with assms have "a < b" by simp
  with mvt_simple[of a b f "\<lambda>x i. i *\<^sub>R f' x"] assms
  obtain y where "y \<in> open_segment a b"  "f b - f a = (b - a) * f' y"
    by (auto simp: has_vector_derivative_def closed_segment_real has_vderiv_on_def open_segment_real)
  thus ?thesis ..
next
  assume "\<not> a \<le> b"
  then have "b < a" by simp
  with mvt_simple[of b a f "\<lambda>x i. i *\<^sub>R f' x"] assms
  obtain y where "y \<in> open_segment a b"  "f b - f a = (b - a) * f' y"
    by (force simp: has_vector_derivative_def has_vderiv_on_def closed_segment_real algebra_simps
      open_segment_real)
  thus ?thesis ..
qed

lemma differentiable_bound_general_open_segment:
  fixes a :: "real"
    and b :: "real"
    and f :: "real \<Rightarrow> 'a::real_normed_vector"
    and f' :: "real \<Rightarrow> 'a"
  assumes "continuous_on (closed_segment a b) f"
  assumes "continuous_on (closed_segment a b) g"
    and "(f has_vderiv_on f') (open_segment a b)"
    and "(g has_vderiv_on g') (open_segment a b)"
    and "\<And>x. x \<in> open_segment a b \<Longrightarrow> norm (f' x) \<le> g' x"
  shows "norm (f b - f a) \<le> abs (g b - g a)"
proof -
  {
    assume "a = b"
    hence ?thesis by simp
  } moreover {
    assume "a < b"
    with assms
    have "continuous_on {a .. b} f"
      and "continuous_on {a .. b} g"
      and "\<And>x. x\<in>{a<..<b} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
      and "\<And>x. x\<in>{a<..<b} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
      and "\<And>x. x\<in>{a<..<b} \<Longrightarrow> norm (f' x) \<le> g' x"
      by (auto simp: open_segment_real closed_segment_real has_vderiv_on_def
        at_within_open[where S="{a<..<b}"])
    from differentiable_bound_general[OF \<open>a < b\<close> this]
    have ?thesis by auto
  } moreover {
    assume "b < a"
    with assms
    have "continuous_on {b .. a} f"
      and "continuous_on {b .. a} g"
      and "\<And>x. x\<in>{b<..<a} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
      and "\<And>x. x\<in>{b<..<a} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
      and "\<And>x. x\<in>{b<..<a} \<Longrightarrow> norm (f' x) \<le> g' x"
      by (auto simp: open_segment_real closed_segment_real has_vderiv_on_def
        at_within_open[where S="{b<..<a}"])
    from differentiable_bound_general[OF \<open>b < a\<close> this]
    have "norm (f a - f b) \<le> g a - g b" by simp
    also have "\<dots> \<le> abs (g b - g a)" by simp
    finally have ?thesis by (simp add: norm_minus_commute)
  } ultimately show ?thesis by arith
qed

lemma has_vderiv_on_union:
  assumes "(f has_vderiv_on g) (s \<union> closure s \<inter> closure t)"
  assumes "(f has_vderiv_on g) (t \<union> closure s \<inter> closure t)"
  shows "(f has_vderiv_on g) (s \<union> t)"
  unfolding has_vderiv_on_def
proof
  fix x assume "x \<in> s \<union> t"
  with has_vector_derivative_If[of x s t "s \<union> t" f g f g] assms
  show "(f has_vector_derivative g x) (at x within s \<union> t)"
    by (auto simp: has_vderiv_on_def)
qed

lemma has_vderiv_on_union_closed:
  assumes "(f has_vderiv_on g) s"
  assumes "(f has_vderiv_on g) t"
  assumes "closed s" "closed t"
  shows "(f has_vderiv_on g) (s \<union> t)"
  using assms
  by (auto simp: Un_absorb2 intro: has_vderiv_on_union)

lemma
  has_vderiv_on_zero_constant:
  assumes "convex s"
  assumes "(f has_vderiv_on (\<lambda>h. 0)) s"
  obtains c where "\<And>x. x \<in> s \<Longrightarrow> f x = c"
  using has_vector_derivative_zero_constant[of s f] assms
  by (auto simp: has_vderiv_on_def)


subsection \<open>Integration\<close>

lemma has_integral_eq_rhs:
  assumes "(f has_integral J) s"
  assumes "I = J"
  shows "(f has_integral I) s"
  using assms
  by metis

lemma has_integral_id:
  "((\<lambda>x. x) has_integral (if a \<le> b then b\<^sup>2/2 - a\<^sup>2/2 else 0)) {a .. b::real}"
  by (auto intro!: fundamental_theorem_of_calculus derivative_eq_intros
    simp: has_vector_derivative_def )

lemma integrable_antiderivative:
  fixes F::"real \<Rightarrow> 'a::banach"
  assumes F: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow>
    (F has_vector_derivative f x) (at x within {a .. b})"
  shows "f integrable_on {a .. b}"
  apply (cases "a \<le> b")
   apply (rule has_integral_integrable)
   apply (rule fundamental_theorem_of_calculus)
  by (auto intro!: F fundamental_theorem_of_calculus)

lemmas content_real[simp]

lemma integral_real_singleton[simp]:
  "integral {a::real} f = 0"
  using integral_refl[of a f] by simp

lemmas integrable_continuous[intro, simp]
  and integrable_continuous_real[intro, simp]

lemma mvt_integral:
  fixes f::"'a::real_normed_vector\<Rightarrow>'b::banach"
  assumes f'[derivative_intros]:
    "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  assumes line_in: "\<And>t. t \<in> {0..1} \<Longrightarrow> x + t *\<^sub>R y \<in> S"
  shows "f (x + y) - f x = integral {0..1} (\<lambda>t. f' (x + t *\<^sub>R y) y)" (is ?th1)
proof -
  from assms have subset: "(\<lambda>xa. x + xa *\<^sub>R y) ` {0..1} \<subseteq> S" by auto
  note [derivative_intros] =
    has_derivative_subset[OF _ subset]
    has_derivative_in_compose[where f="(\<lambda>xa. x + xa *\<^sub>R y)" and g = f]
  note [continuous_intros] =
    continuous_on_compose2[where f="(\<lambda>xa. x + xa *\<^sub>R y)"]
    continuous_on_subset[OF _ subset]
  have "\<And>t. t \<in> {0..1} \<Longrightarrow>
    ((\<lambda>t. f (x + t *\<^sub>R y)) has_vector_derivative f' (x + t *\<^sub>R y) y)
    (at t within {0..1})"
    using assms
    by (auto simp: has_vector_derivative_def
        linear_cmul[OF has_derivative_linear[OF f'], symmetric]
      intro!: derivative_eq_intros)
  from fundamental_theorem_of_calculus[rule_format, OF _ this]
  show ?th1
    by (auto intro!: integral_unique[symmetric])
qed

lemma integral_mult:
  fixes K::real
  shows "f integrable_on X \<Longrightarrow> K * integral X f = integral X (\<lambda>x. K * f x)"
  unfolding real_scaleR_def[symmetric]
  apply (subst integral_cmul)
  by auto

lemma integrable_mult:
  fixes K::real
  shows "f integrable_on X \<Longrightarrow> (\<lambda>x. K * f x) integrable_on X "
  unfolding real_scaleR_def[symmetric]
  apply (subst integrable_cmul)
  by auto

lemma integrable_continuous_closed_segment:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on (closed_segment a b) f"
  shows "f integrable_on (closed_segment a b)"
  using assms closed_segment_eq_real_ivl
  by auto

lemma continuous_on_imp_absolutely_integrable_on:
  fixes f::"real \<Rightarrow> 'a::banach"
  shows "continuous_on {a..b} f \<Longrightarrow>
    norm (integral {a..b} f) \<le> integral {a..b} (\<lambda>x. norm (f x))"
  by (intro integral_norm_bound_integral integrable_continuous_real continuous_on_norm) auto

lemma integral_bound:
  fixes f::"real \<Rightarrow> 'a::banach"
  assumes "a \<le> b"
  assumes "continuous_on {a .. b} f"
  assumes "\<And>t. t \<in> {a .. b} \<Longrightarrow> norm (f t) \<le> B"
  shows "norm (integral {a .. b} f) \<le> B * (b - a)"
proof -
  note continuous_on_imp_absolutely_integrable_on[OF assms(2)]
  also have "integral {a..b} (\<lambda>x. norm (f x)) \<le> integral {a..b} (\<lambda>_. B)"
    by (rule integral_le)
      (auto intro!: integrable_continuous_real continuous_intros assms)
  also have "\<dots> = B * (b - a)" using assms by simp
  finally show ?thesis .
qed

lemma integral_minus_sets:
  fixes f::"real \<Rightarrow> 'a::banach"
  shows "c \<le> a \<Longrightarrow> c \<le> b \<Longrightarrow> f integrable_on {c .. max a b} \<Longrightarrow>
    integral {c .. a} f - integral {c .. b} f =
    (if a \<le> b then - integral {a .. b} f else integral {b .. a} f)"
  using integral_combine[of c a b f]  integral_combine[of c b a f]
  by (auto simp: algebra_simps max_def)

lemma integral_minus_sets':
  fixes f::"real \<Rightarrow> 'a::banach"
  shows "c \<ge> a \<Longrightarrow> c \<ge> b \<Longrightarrow> f integrable_on {min a b .. c} \<Longrightarrow>
    integral {a .. c} f - integral {b .. c} f =
    (if a \<le> b then integral {a .. b} f else - integral {b .. a} f)"
  using integral_combine[of b a c f] integral_combine[of a b c f]
  by (auto simp: algebra_simps min_def)

lemma integral_has_real_derivative:
  assumes "continuous_on {a..b} g"
  assumes "t \<in> {a..b}"
  shows "((\<lambda>x. integral {a..x} g) has_real_derivative g t) (at t within {a..b})"
  using integral_has_vector_derivative[of a b g t] assms
  by (auto simp: has_field_derivative_iff_has_vector_derivative)

lemma indefinite_integral2_continuous:
  fixes f::"real \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a..b}"
  shows "continuous_on {a..b} (\<lambda>x. integral {x..b} f)"
proof -
  have *: "integral {x..b} f = integral {a .. b} f - integral {a .. x} f" if "a \<le> x" "x \<le> b" for x
    using integral_combine[of a x b for x, OF that assms]
    by (simp add: algebra_simps)
  show ?thesis
    by (subst continuous_on_cong[OF refl *])
      (auto intro!: continuous_intros indefinite_integral_continuous assms)
qed

theorem integral2_has_vector_derivative:
  fixes f :: "real \<Rightarrow> 'b::banach"
  assumes "continuous_on {a..b} f"
    and "x \<in> {a..b}"
  shows "((\<lambda>u. integral {u..b} f) has_vector_derivative - f x) (at x within {a..b})"
proof -
  have *: "integral {x..b} f = integral {a .. b} f - integral {a .. x} f" if "a \<le> x" "x \<le> b" for x
    using integral_combine[of a x b for x, OF that integrable_continuous_real[OF assms(1)]]
    by (simp add: algebra_simps)
  show ?thesis
    using \<open>x \<in> _\<close>
    by (subst has_vector_derivative_cong[OF _ * refl refl refl])
      (auto intro!: derivative_eq_intros indefinite_integral_continuous assms
        integral_has_vector_derivative)
qed

lemma integral_has_real_derivative_left:
  assumes "continuous_on {a..b} g"
  assumes "t \<in> {a..b}"
  shows "((\<lambda>x. integral {x..b} g) has_real_derivative -g t) (at t within {a..b})"
  using integral2_has_vector_derivative[OF assms]
  by (auto simp: has_field_derivative_iff_has_vector_derivative)

lemma integral_eucl_le:
  fixes f g::"'a::euclidean_space \<Rightarrow> 'b::ordered_euclidean_space"
  assumes "f integrable_on s"
    and "g integrable_on s"
    and "\<And>x. x \<in> s \<Longrightarrow> f x \<le> g x"
  shows "integral s f \<le> integral s g"
  using assms
  by (auto intro!: integral_component_le simp: eucl_le[where 'a='b])

lemma
  integral_ivl_bound:
  fixes l u::"'a::ordered_euclidean_space"
  assumes "\<And>x h'. h' \<in> {t0 .. h} \<Longrightarrow> x \<in> {t0 .. h} \<Longrightarrow> (h' - t0) *\<^sub>R f x \<in> {l .. u}"
  assumes "t0 \<le> h"
  assumes f_int: "f integrable_on {t0 .. h}"
  shows "integral {t0 .. h} f \<in> {l .. u}"
proof -
  from assms(1)[of t0 t0] assms(2) have "0 \<in> {l .. u}" by auto
  have "integral {t0 .. h} f = integral {t0 .. h} (\<lambda>t. if t \<in> {t0, h} then 0 else f t)"
    by (rule integral_spike[where s="{t0, h}"]) auto
  also
  {
    fix x
    assume 1: "x \<in> {t0 <..< h}"
    with assms have "(h - t0) *\<^sub>R f x \<in> {l .. u}" by auto
    then have "(if x \<in> {t0, h} then 0 else f x) \<in> {l /\<^sub>R (h - t0) .. u /\<^sub>R (h - t0)}"
      using \<open>x \<in> _\<close>
      by (auto simp: inverse_eq_divide
        simp: eucl_le[where 'a='a] field_simps algebra_simps)
  }
  then have "\<dots> \<in> {integral {t0..h} (\<lambda>_. l /\<^sub>R (h - t0)) .. integral {t0..h} (\<lambda>_. u /\<^sub>R (h - t0))}"
    unfolding atLeastAtMost_iff
    apply (safe intro!: integral_eucl_le)
    using \<open>0 \<in> {l .. u}\<close>
    apply (auto intro!: assms
      intro: integrable_continuous_real  integrable_spike[where s="{t0, h}", OF _ _ f_int]
      simp: eucl_le[where 'a='a] divide_simps
      split: if_split_asm)
    done
  also have "\<dots> \<subseteq> {l .. u}"
    using assms \<open>0 \<in> {l .. u}\<close>
    by (auto simp: inverse_eq_divide)
  finally show ?thesis .
qed

lemma
  add_integral_ivl_bound:
  fixes l u::"'a::ordered_euclidean_space"
  assumes "\<And>x h'. h' \<in> {t0 .. h} \<Longrightarrow> x \<in> {t0 .. h} \<Longrightarrow> (h' - t0) *\<^sub>R f x \<in> {l - x0 .. u - x0}"
  assumes "t0 \<le> h"
  assumes f_int: "f integrable_on {t0 .. h}"
  shows "x0 + integral {t0 .. h} f \<in> {l .. u}"
  using integral_ivl_bound[OF assms]
  by (auto simp: algebra_simps)


subsection \<open>interval integral\<close>
  \<comment>\<open>TODO: move to repo ?!\<close>
  \<comment>\<open>TODO: replace with Bochner Integral?!
           But FTC for Bochner requires continuity and euclidean space!\<close>

definition has_ivl_integral ::
    "(real \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'b \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool"\<comment>\<open>TODO: generalize?\<close>
  (infixr "has'_ivl'_integral" 46)
  where "(f has_ivl_integral y) a b \<longleftrightarrow> (if a \<le> b then (f has_integral y) {a .. b} else (f has_integral - y) {b .. a})"

definition ivl_integral::"real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> 'a::real_normed_vector"
  where "ivl_integral a b f = integral {a .. b} f - integral {b .. a} f"

lemma integral_emptyI[simp]:
  fixes a b::real
  shows  "a \<ge> b \<Longrightarrow> integral {a..b} f = 0" "a > b \<Longrightarrow> integral {a..b} f = 0"
  by (cases "a = b") auto

lemma ivl_integral_unique: "(f has_ivl_integral y) a b \<Longrightarrow> ivl_integral a b f = y"
  using integral_unique[of f y "{a .. b}"] integral_unique[of f "- y" "{b .. a}"]
  unfolding ivl_integral_def has_ivl_integral_def
  by (auto split: if_split_asm)

lemma fundamental_theorem_of_calculus_ivl_integral:
  fixes f :: "real \<Rightarrow> 'a::banach"
  shows "(f has_vderiv_on f') (closed_segment a b) \<Longrightarrow> (f' has_ivl_integral f b - f a) a b"
  by (auto simp: has_ivl_integral_def closed_segment_real intro!: fundamental_theorem_of_calculus')

lemma
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on (closed_segment a b)"
  shows indefinite_ivl_integral_continuous:
    "continuous_on (closed_segment a b) (\<lambda>x. ivl_integral a x f)"
    "continuous_on (closed_segment b a) (\<lambda>x. ivl_integral a x f)"
  using assms
  by (auto simp: ivl_integral_def closed_segment_real split: if_split_asm
    intro!: indefinite_integral_continuous indefinite_integral2_continuous
      continuous_intros intro: continuous_on_eq)

lemma
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on (closed_segment a b)"
  assumes "c \<in> closed_segment a b"
  shows indefinite_ivl_integral_continuous_subset:
    "continuous_on (closed_segment a b) (\<lambda>x. ivl_integral c x f)"
proof -
  from assms have "f integrable_on {c--a}" "f integrable_on {c--b}"
    by (auto simp: closed_segment_real integrable_on_subinterval split: if_splits)
  then have "continuous_on (closed_segment a c \<union> closed_segment c b) (\<lambda>x. ivl_integral c x f)"
    by (auto intro!: indefinite_ivl_integral_continuous continuous_on_closed_Un)
  also have "closed_segment a c \<union> closed_segment c b = closed_segment a b"
    using assms by (auto simp: closed_segment_real)
  finally show ?thesis .
qed

lemma real_Icc_closed_segment: fixes a b::real shows "a \<le> b \<Longrightarrow> {a .. b} = closed_segment a b"
  by (auto simp: closed_segment_real)

lemma ivl_integral_zero[simp]: "ivl_integral a a f = 0"
  by (auto simp: ivl_integral_def)

lemma ivl_integral_cong:
  assumes "\<And>x. x \<in> closed_segment a b \<Longrightarrow> g x = f x"
  assumes "a = c" "b = d"
  shows "ivl_integral a b f = ivl_integral c d g"
  using assms integral_spike[of "{}" "closed_segment a b" f g]
  by (auto simp: ivl_integral_def closed_segment_real split: if_split_asm)

lemma ivl_integral_diff:
  "f integrable_on (closed_segment s t) \<Longrightarrow> g integrable_on (closed_segment s t) \<Longrightarrow>
    ivl_integral s t (\<lambda>x. f x - g x) = ivl_integral s t f - ivl_integral s t g"
  using Henstock_Kurzweil_Integration.integral_diff[of f "closed_segment s t" g]
  by (auto simp: ivl_integral_def closed_segment_real split: if_split_asm)

lemma ivl_integral_norm_bound_ivl_integral:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on (closed_segment a b)"
    and "g integrable_on (closed_segment a b)"
    and "\<forall>x\<in>closed_segment a b. norm (f x) \<le> g x"
  shows "norm (ivl_integral a b f) \<le> abs (ivl_integral a b g)"
  using integral_norm_bound_integral[OF assms]
  by (auto simp: ivl_integral_def closed_segment_real split: if_split_asm)

lemma ivl_integral_norm_bound_integral:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on (closed_segment a b)"
    and "g integrable_on (closed_segment a b)"
    and "\<forall>x\<in>closed_segment a b. norm (f x) \<le> g x"
  shows "norm (ivl_integral a b f) \<le> integral {a -- b} g"
  using integral_norm_bound_integral[OF assms]
  by (auto simp: ivl_integral_def closed_segment_real split: if_split_asm)

lemma norm_ivl_integral_le:
  fixes f :: "real \<Rightarrow> real"
  assumes "f integrable_on (closed_segment a b)"
    and "g integrable_on (closed_segment a b)"
    and "\<forall>x\<in>closed_segment a b. f x \<le> g x"
    and "\<forall>x\<in>closed_segment a b. 0 \<le> f x"
  shows "abs (ivl_integral a b f) \<le> abs (ivl_integral a b g)"
  using integral_le[OF assms(1-3)]
  unfolding ivl_integral_def closed_segment_real
  apply (split if_split_asm)
  subgoal by (simp add: assms(1) assms(4) Henstock_Kurzweil_Integration.integral_nonneg real_Icc_closed_segment)
  subgoal using assms
    by (cases "a = b") (auto simp: Henstock_Kurzweil_Integration.integral_nonneg simp: closed_segment_real)
  done

lemma ivl_integral_const [simp]:
  shows "ivl_integral a b (\<lambda>x. c) = (b - a) *\<^sub>R c"
  by (auto simp: ivl_integral_def algebra_simps)

lemma ivl_integral_has_vector_derivative:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on (closed_segment a b) f"
    and "x \<in> closed_segment a b"
  shows "((\<lambda>u. ivl_integral a u f) has_vector_derivative f x) (at x within closed_segment a b)"
proof -
  have "((\<lambda>x. integral {x..a} f) has_vector_derivative 0) (at x within {a..b})" if "a \<le> x" "x \<le> b"
    using assms that
    by (subst has_vector_derivative_cong) auto
  moreover
  have "((\<lambda>x. integral {a..x} f) has_vector_derivative 0) (at x within {b..a})" if "b \<le> x" "x \<le> a"
    using assms that
    by (subst has_vector_derivative_cong) auto
  ultimately
  show ?thesis
    using assms
    by (auto simp: ivl_integral_def closed_segment_real
        intro!: derivative_eq_intros
        integral_has_vector_derivative[of a b f] integral_has_vector_derivative[of b a "-f"]
        integral2_has_vector_derivative[of b a f])
qed

lemma ivl_integral_has_vderiv_on:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on {a -- b} f"
  shows "((\<lambda>u. ivl_integral a u f) has_vderiv_on f) {a -- b}"
  using ivl_integral_has_vector_derivative[OF assms]
  by (auto simp: has_vderiv_on_def)

lemma ivl_integral_has_vderiv_on_subset:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on (closed_segment a b) f"
    and "c \<in> closed_segment a b"
  shows "((\<lambda>u. ivl_integral c u f) has_vderiv_on f) {a -- b}"
proof -
  have "{c--a} \<subseteq> {a -- b}" "{c--b} \<subseteq> {a -- b}"
    using assms by (auto simp: closed_segment_real split: if_splits)
  then have "((\<lambda>u. ivl_integral c u f) has_vderiv_on f) ({c -- a} \<union> {c -- b})"
    by (auto intro!: has_vderiv_on_union_closed ivl_integral_has_vderiv_on assms
      intro: continuous_on_subset)
  also have "{c -- a} \<union> {c -- b} = {a -- b}"
    using assms by (auto simp: closed_segment_real split: if_splits)
  finally show ?thesis .
qed

lemma ivl_integral_has_vector_derivative_subset:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on (closed_segment a b) f"
    and "x \<in> closed_segment a b"
    and "c \<in> closed_segment a b"
  shows "((\<lambda>u. ivl_integral c u f) has_vector_derivative f x) (at x within closed_segment a b)"
  using ivl_integral_has_vderiv_on_subset[OF assms(1)] assms(2-)
  by (auto simp: has_vderiv_on_def)

lemma
  compact_interval_eq_Inf_Sup:
  fixes A::"real set"
  assumes "is_interval A" "compact A" "A \<noteq> {}"
  shows "A = {Inf A .. Sup A}"
  apply (auto simp: closed_segment_real
      intro!: cInf_lower cSup_upper bounded_imp_bdd_below bounded_imp_bdd_above
      compact_imp_bounded assms)
  by (metis assms(1) assms(2) assms(3) cInf_eq_minimum cSup_eq_maximum compact_attains_inf
      compact_attains_sup mem_is_interval_1_I)

lemma ivl_integral_has_vderiv_on_compact_interval:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on A f"
    and "c \<in> A" "is_interval A" "compact A"
  shows "((\<lambda>u. ivl_integral c u f) has_vderiv_on f) A"
proof -
  have "A = {Inf A .. Sup A}"
    by (rule compact_interval_eq_Inf_Sup) (use assms in auto)
  also have "\<dots> = {Inf A -- Sup A}" using assms
    by (auto simp add: closed_segment_real
        intro!: cInf_le_cSup bounded_imp_bdd_below bounded_imp_bdd_above compact_imp_bounded)
  finally have *: "A = {Inf A -- Sup A}" .
  show ?thesis
    apply (subst *)
    apply (rule ivl_integral_has_vderiv_on_subset)
    unfolding *[symmetric]
    by fact+
qed

lemma ivl_integral_has_vector_derivative_compact_interval:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on A f"
    and "is_interval A" "compact A" "x \<in> A" "c \<in> A"
  shows "((\<lambda>u. ivl_integral c u f) has_vector_derivative f x) (at x within A)"
  using ivl_integral_has_vderiv_on_compact_interval[OF assms(1)] assms(2-)
  by (auto simp: has_vderiv_on_def)

lemma ivl_integral_combine:
  fixes f::"real \<Rightarrow> 'a::banach"
  assumes "f integrable_on (closed_segment a b)"
  assumes "f integrable_on (closed_segment b c)"
  assumes "f integrable_on (closed_segment a c)"
  shows "ivl_integral a b f + ivl_integral b c f = ivl_integral a c f"
proof -
  show ?thesis
    using assms
      integral_combine[of a b c f]
      integral_combine[of a c b f]
      integral_combine[of b a c f]
      integral_combine[of b c a f]
      integral_combine[of c a b f]
      integral_combine[of c b a f]
    by (cases "a \<le> b"; cases "b \<le> c"; cases "a \<le> c")
       (auto simp: algebra_simps ivl_integral_def closed_segment_real)
qed

lemma integral_equation_swap_initial_value:
  fixes x::"real\<Rightarrow>'a::banach"
  assumes "\<And>t. t \<in> closed_segment t0 t1 \<Longrightarrow> x t = x t0 + ivl_integral t0 t (\<lambda>t. f t (x t))"
  assumes t: "t \<in> closed_segment t0 t1"
  assumes int: "(\<lambda>t. f t (x t)) integrable_on closed_segment t0 t1"
  shows "x t = x t1 + ivl_integral t1 t (\<lambda>t. f t (x t))"
proof -
  from t int have "(\<lambda>t. f t (x t)) integrable_on closed_segment t0 t"
    "(\<lambda>t. f t (x t)) integrable_on closed_segment t t1"
    by (auto intro: integrable_on_subinterval simp: closed_segment_real split: if_split_asm)
  with assms(1)[of t] assms(2-)
  have "x t - x t0 = ivl_integral t0 t1 (\<lambda>t. f t (x t)) + ivl_integral t1 t (\<lambda>t. f t (x t))"
    by (subst ivl_integral_combine) (auto simp: closed_segment_commute)
  then have "x t + x t1 - (x t0 + ivl_integral t0 t1 (\<lambda>t. f t (x t))) =
    x t1 + ivl_integral t1 t (\<lambda>t. f t (x t))"
    by (simp add: algebra_simps)
  also have "x t0 + ivl_integral t0 t1 (\<lambda>t. f t (x t)) = x t1"
    by (auto simp: assms(1)[symmetric])
  finally show ?thesis  by simp
qed

lemma has_integral_nonpos:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "(f has_integral i) s"
    and "\<forall>x\<in>s. f x \<le> 0"
  shows "i \<le> 0"
  by (rule has_integral_nonneg[of "-f" "-i" s, simplified])
    (auto intro!: has_integral_neg simp: fun_Compl_def assms)

lemma has_ivl_integral_nonneg:
  fixes f :: "real \<Rightarrow> real"
  assumes "(f has_ivl_integral i) a b"
    and "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> 0 \<le> f x"
    and "\<And>x. b \<le> x \<Longrightarrow> x \<le> a \<Longrightarrow> f x \<le> 0"
  shows "0 \<le> i"
  using assms has_integral_nonneg[of f i "{a .. b}"] has_integral_nonpos[of f "-i" "{b .. a}"]
  by (auto simp: has_ivl_integral_def Ball_def not_le split: if_split_asm)

lemma has_ivl_integral_ivl_integral:
  "f integrable_on {a -- b} \<longleftrightarrow> (f has_ivl_integral (ivl_integral a b f)) a b"
  using has_integral_integral[of f "{a -- b}"]
  by (auto simp: closed_segment_real has_ivl_integral_def ivl_integral_def)

lemma ivl_integral_nonneg:
  fixes f :: "real \<Rightarrow> real"
  assumes "f integrable_on {a -- b}"
    and "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> 0 \<le> f x"
    and "\<And>x. b \<le> x \<Longrightarrow> x \<le> a \<Longrightarrow> f x \<le> 0"
  shows "0 \<le> ivl_integral a b f"
  by (rule has_ivl_integral_nonneg[OF assms(1)[unfolded has_ivl_integral_ivl_integral] assms(2-3)])

lemma ivl_integral_bound:
  fixes f::"real \<Rightarrow> 'a::banach"
  assumes "continuous_on {a -- b} f"
  assumes "\<And>t. t \<in> {a -- b} \<Longrightarrow> norm (f t) \<le> B"
  shows "norm (ivl_integral a b f) \<le> B * abs (b - a)"
  using integral_bound[of a b f B]
    integral_bound[of b a f B]
    assms
  by (auto simp: closed_segment_real has_ivl_integral_def ivl_integral_def split: if_splits)

lemma ivl_integral_minus_sets:
  fixes f::"real \<Rightarrow> 'a::banach"
  shows "f integrable_on {c -- a} \<Longrightarrow> f integrable_on {c -- b} \<Longrightarrow> f integrable_on {a -- b} \<Longrightarrow>
    ivl_integral c a f - ivl_integral c b f = ivl_integral b a f"
  using ivl_integral_combine[of f c b a]
  by (auto simp: algebra_simps closed_segment_commute)

lemma ivl_integral_minus_sets':
  fixes f::"real \<Rightarrow> 'a::banach"
  shows "f integrable_on {a -- c} \<Longrightarrow> f integrable_on {b -- c} \<Longrightarrow> f integrable_on {a -- b} \<Longrightarrow>
    ivl_integral a c f - ivl_integral b c f = ivl_integral a b f"
  using ivl_integral_combine[of f a b c]
  by (auto simp: algebra_simps closed_segment_commute)


subsection \<open>Gronwall\<close>

lemma derivative_quotient_bound:
  assumes g_deriv_on: "(g has_vderiv_on g') {a .. b}"
  assumes frac_le: "\<And>t. t \<in> {a .. b} \<Longrightarrow> g' t / g t \<le> K"
  assumes g'_cont: "continuous_on {a .. b} g'"
  assumes g_pos: "\<And>t. t \<in> {a .. b} \<Longrightarrow> g t > 0"
  assumes t_in: "t \<in> {a .. b}"
  shows "g t \<le> g a * exp (K * (t - a))"
proof -
  have g_deriv: "\<And>t. t \<in> {a .. b} \<Longrightarrow> (g has_real_derivative g' t) (at t within {a .. b})"
    using g_deriv_on
    by (auto simp: has_vderiv_on_def has_field_derivative_iff_has_vector_derivative[symmetric])
  from assms have g_nonzero: "\<And>t. t \<in> {a .. b} \<Longrightarrow> g t \<noteq> 0"
    by fastforce
  have frac_integrable: "\<And>t. t \<in> {a .. b} \<Longrightarrow> (\<lambda>t. g' t / g t) integrable_on {a..t}"
    by (force simp: g_nonzero intro: assms has_field_derivative_subset[OF g_deriv]
      continuous_on_subset[OF g'_cont] continuous_intros
      continuous_on_subset[OF vderiv_on_continuous_on[OF g_deriv_on]])
  have "\<And>t. t \<in> {a..b} \<Longrightarrow> ((\<lambda>t. g' t / g t) has_integral ln (g t) - ln (g a)) {a .. t}"
    by (rule fundamental_theorem_of_calculus)
      (auto intro!: derivative_eq_intros assms has_field_derivative_subset[OF g_deriv]
        simp: has_field_derivative_iff_has_vector_derivative[symmetric])
  hence *: "\<And>t. t \<in> {a .. b} \<Longrightarrow> ln (g t) - ln (g a) = integral {a .. t} (\<lambda>t. g' t / g t)"
    using integrable_integral[OF frac_integrable]
    by (rule has_integral_unique[where f = "\<lambda>t. g' t / g t"])
  from * t_in have "ln (g t) - ln (g a) = integral {a .. t} (\<lambda>t. g' t / g t)" .
  also have "\<dots> \<le> integral {a .. t} (\<lambda>_. K)"
    using \<open>t \<in> {a .. b}\<close>
    by (intro integral_le) (auto intro!: frac_integrable frac_le integral_le)
  also have "\<dots> = K * (t - a)" using \<open>t \<in> {a .. b}\<close>
    by simp
  finally have "ln (g t) \<le> K * (t - a) + ln (g a)" (is "?lhs \<le> ?rhs")
    by simp
  hence "exp ?lhs \<le> exp ?rhs"
    by simp
  thus ?thesis
    using \<open>t \<in> {a .. b}\<close> g_pos
    by (simp add: ac_simps exp_add del: exp_le_cancel_iff)
qed

lemma derivative_quotient_bound_left:
  assumes g_deriv_on: "(g has_vderiv_on g') {a .. b}"
  assumes frac_ge: "\<And>t. t \<in> {a .. b} \<Longrightarrow> K \<le> g' t / g t"
  assumes g'_cont: "continuous_on {a .. b} g'"
  assumes g_pos: "\<And>t. t \<in> {a .. b} \<Longrightarrow> g t > 0"
  assumes t_in: "t \<in> {a..b}"
  shows "g t \<le> g b * exp (K * (t - b))"
proof -
  have g_deriv: "\<And>t. t \<in> {a .. b} \<Longrightarrow> (g has_real_derivative g' t) (at t within {a .. b})"
    using g_deriv_on
    by (auto simp: has_vderiv_on_def has_field_derivative_iff_has_vector_derivative[symmetric])
  from assms have g_nonzero: "\<And>t. t \<in> {a..b} \<Longrightarrow> g t \<noteq> 0"
    by fastforce
  have frac_integrable: "\<And>t. t \<in> {a .. b} \<Longrightarrow> (\<lambda>t. g' t / g t) integrable_on {t..b}"
    by (force simp: g_nonzero intro: assms has_field_derivative_subset[OF g_deriv]
      continuous_on_subset[OF g'_cont] continuous_intros
      continuous_on_subset[OF vderiv_on_continuous_on[OF g_deriv_on]])
  have "\<And>t. t \<in> {a..b} \<Longrightarrow> ((\<lambda>t. g' t / g t) has_integral ln (g b) - ln (g t)) {t..b}"
    by (rule fundamental_theorem_of_calculus)
      (auto intro!: derivative_eq_intros assms has_field_derivative_subset[OF g_deriv]
        simp: has_field_derivative_iff_has_vector_derivative[symmetric])
  hence *: "\<And>t. t \<in> {a..b} \<Longrightarrow> ln (g b) - ln (g t) = integral {t..b} (\<lambda>t. g' t / g t)"
    using integrable_integral[OF frac_integrable]
    by (rule has_integral_unique[where f = "\<lambda>t. g' t / g t"])
  have "K * (b - t) = integral {t..b} (\<lambda>_. K)"
    using \<open>t \<in> {a..b}\<close>
    by simp
  also have "... \<le> integral {t..b} (\<lambda>t. g' t / g t)"
    using \<open>t \<in> {a..b}\<close>
    by (intro integral_le) (auto intro!: frac_integrable frac_ge integral_le)
  also have "... = ln (g b) - ln (g t)"
    using * t_in by simp
  finally have "K * (b - t) + ln (g t) \<le> ln (g b)" (is "?lhs \<le> ?rhs")
    by simp
  hence "exp ?lhs \<le> exp ?rhs"
    by simp
  hence "g t * exp (K * (b - t)) \<le> g b"
    using \<open>t \<in> {a..b}\<close> g_pos
    by (simp add: ac_simps exp_add del: exp_le_cancel_iff)
  hence "g t / exp (K * (t - b)) \<le> g b"
    by (simp add: algebra_simps exp_diff)
  thus ?thesis
    by (simp add: field_simps)
qed

lemma gronwall_general:
  fixes g K C a b and t::real
  defines "G \<equiv> \<lambda>t. C + K * integral {a..t} (\<lambda>s. g s)"
  assumes g_le_G: "\<And>t. t \<in> {a..b} \<Longrightarrow> g t \<le> G t"
  assumes g_cont: "continuous_on {a..b} g"
  assumes g_nonneg: "\<And>t. t \<in> {a..b} \<Longrightarrow> 0 \<le> g t"
  assumes pos: "0 < C" "K > 0"
  assumes "t \<in> {a..b}"
  shows "g t \<le> C * exp (K * (t - a))"
proof -
  have G_pos: "\<And>t. t \<in> {a..b} \<Longrightarrow> 0 < G t"
    by (auto simp: G_def intro!: add_pos_nonneg mult_nonneg_nonneg Henstock_Kurzweil_Integration.integral_nonneg
      integrable_continuous_real assms intro: less_imp_le continuous_on_subset)
  have "g t \<le> G t" using assms by auto
  also
  {
    have "(G has_vderiv_on (\<lambda>t. K * g t)) {a..b}"
      by (auto intro!: derivative_eq_intros integral_has_vector_derivative g_cont
        simp add: G_def has_vderiv_on_def)
    moreover
    {
      fix t assume "t \<in> {a..b}"
      hence "K * g t / G t \<le> K * G t / G t"
        using pos g_le_G G_pos
        by (intro divide_right_mono mult_left_mono) (auto intro!: less_imp_le)
      also have "\<dots> = K"
        using G_pos[of t] \<open>t \<in> {a .. b}\<close> by simp
      finally have "K * g t / G t \<le> K" .
    }
    ultimately have "G t \<le> G a * exp (K * (t - a))"
      apply (rule derivative_quotient_bound)
      using \<open>t \<in> {a..b}\<close>
      by (auto intro!: continuous_intros g_cont G_pos simp: field_simps pos)
  }
  also have "G a = C"
    by (simp add: G_def)
  finally show ?thesis
    by simp
qed

lemma gronwall_general_left:
  fixes g K C a b and t::real
  defines "G \<equiv> \<lambda>t. C + K * integral {t..b} (\<lambda>s. g s)"
  assumes g_le_G: "\<And>t. t \<in> {a..b} \<Longrightarrow> g t \<le> G t"
  assumes g_cont: "continuous_on {a..b} g"
  assumes g_nonneg: "\<And>t. t \<in> {a..b} \<Longrightarrow> 0 \<le> g t"
  assumes pos: "0 < C" "K > 0"
  assumes "t \<in> {a..b}"
  shows "g t \<le> C * exp (-K * (t - b))"
proof -
  have G_pos: "\<And>t. t \<in> {a..b} \<Longrightarrow> 0 < G t"
    by (auto simp: G_def intro!: add_pos_nonneg mult_nonneg_nonneg Henstock_Kurzweil_Integration.integral_nonneg
      integrable_continuous_real assms intro: less_imp_le continuous_on_subset)
  have "g t \<le> G t" using assms by auto
  also
  {
    have "(G has_vderiv_on (\<lambda>t. -K * g t)) {a..b}"
      by (auto intro!: derivative_eq_intros integral2_has_vector_derivative g_cont
        simp add: G_def has_vderiv_on_def)
    moreover
    {
      fix t assume "t \<in> {a..b}"
      hence "K * g t / G t \<le> K * G t / G t"
        using pos g_le_G G_pos
        by (intro divide_right_mono mult_left_mono) (auto intro!: less_imp_le)
      also have "\<dots> = K"
        using G_pos[of t] \<open>t \<in> {a .. b}\<close> by simp
      finally have "K * g t / G t \<le> K" .
      hence "-K \<le> -K * g t / G t"
        by simp
    }
    ultimately
    have "G t \<le> G b * exp (-K * (t - b))"
      apply (rule derivative_quotient_bound_left)
      using \<open>t \<in> {a..b}\<close>
      by (auto intro!: continuous_intros g_cont G_pos simp: field_simps pos)
  }
  also have "G b = C"
    by (simp add: G_def)
  finally show ?thesis
    by simp
qed

lemma gronwall_general_segment:
  fixes a b::real
  assumes "\<And>t. t \<in> closed_segment a b \<Longrightarrow> g t \<le> C + K * integral (closed_segment a t) g"
    and "continuous_on (closed_segment a b) g"
    and "\<And>t. t \<in> closed_segment a b \<Longrightarrow> 0 \<le> g t"
    and "0 < C"
    and "0 < K"
    and "t \<in> closed_segment a b"
  shows "g t \<le> C * exp (K * abs (t - a))"
proof cases
  assume "a \<le> b"
  then have *: "abs (t - a) = t -a" using assms by (auto simp: closed_segment_real)
  show ?thesis
    unfolding *
    using assms
    by (intro gronwall_general[where b=b]) (auto intro!: simp: closed_segment_real \<open>a \<le> b\<close>)
next
  assume "\<not>a \<le> b"
  then have *: "K * abs (t - a) = - K * (t - a)" using assms by (auto simp: closed_segment_real algebra_simps)
  {
    fix s :: real
    assume a1: "b \<le> s"
    assume a2: "s \<le> a"
    assume a3: "\<And>t. b \<le> t \<and> t \<le> a \<Longrightarrow> g t \<le> C + K * integral (if a \<le> t then {a..t} else {t..a}) g"
    have "s = a \<or> s < a"
      using a2 by (meson less_eq_real_def)
    then have "g s \<le> C + K * integral {s..a} g"
      using a3 a1 by fastforce
  } then show ?thesis
    unfolding *
    using assms  \<open>\<not>a \<le> b\<close>
    by (intro gronwall_general_left)
      (auto intro!: simp: closed_segment_real)
qed

lemma gronwall_more_general_segment:
  fixes a b c::real
  assumes "\<And>t. t \<in> closed_segment a b \<Longrightarrow> g t \<le> C + K * integral (closed_segment c t) g"
    and cont: "continuous_on (closed_segment a b) g"
    and "\<And>t. t \<in> closed_segment a b \<Longrightarrow> 0 \<le> g t"
    and "0 < C"
    and "0 < K"
    and t: "t \<in> closed_segment a b"
    and c: "c \<in> closed_segment a b"
  shows "g t \<le> C * exp (K * abs (t - c))"
proof -
  from t c have "t \<in> closed_segment c a \<or> t \<in> closed_segment c b"
    by (auto simp: closed_segment_real split_ifs)
  then show ?thesis
  proof
    assume "t \<in> closed_segment c a"
    moreover
    have subs: "closed_segment c a \<subseteq> closed_segment a b" using t c
      by (auto simp: closed_segment_real split_ifs)
    ultimately show ?thesis
      by (intro gronwall_general_segment[where b=a])
        (auto intro!: assms intro: continuous_on_subset)
  next
    assume "t \<in> closed_segment c b"
    moreover
    have subs: "closed_segment c b \<subseteq> closed_segment a b" using t c
      by (auto simp: closed_segment_real)
    ultimately show ?thesis
      by (intro gronwall_general_segment[where b=b])
        (auto intro!: assms intro: continuous_on_subset)
  qed
qed

lemma gronwall:
  fixes g K C and t::real
  defines "G \<equiv> \<lambda>t. C + K * integral {0..t} (\<lambda>s. g s)"
  assumes g_le_G: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> a \<Longrightarrow> g t \<le> G t"
  assumes g_cont: "continuous_on {0..a} g"
  assumes g_nonneg: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> a \<Longrightarrow> 0 \<le> g t"
  assumes pos: "0 < C" "0 < K"
  assumes "0 \<le> t" "t \<le> a"
  shows "g t \<le> C * exp (K * t)"
  apply(rule gronwall_general[where a=0, simplified, OF assms(2-6)[unfolded G_def]])
  using assms(7,8)
  by simp_all

lemma gronwall_left:
  fixes g K C and t::real
  defines "G \<equiv> \<lambda>t. C + K * integral {t..0} (\<lambda>s. g s)"
  assumes g_le_G: "\<And>t. a \<le> t \<Longrightarrow> t \<le> 0 \<Longrightarrow> g t \<le> G t"
  assumes g_cont: "continuous_on {a..0} g"
  assumes g_nonneg: "\<And>t. a \<le> t \<Longrightarrow> t \<le> 0 \<Longrightarrow> 0 \<le> g t"
  assumes pos: "0 < C" "0 < K"
  assumes "a \<le> t" "t \<le> 0"
  shows "g t \<le> C * exp (-K * t)"
  apply(simp, rule gronwall_general_left[where b=0, simplified, OF assms(2-6)[unfolded G_def]])
  using assms(7,8)
  by simp_all

lemma
  fixes g::"real \<Rightarrow> 'a::banach"
  assumes "a \<le> b"
  assumes cf[continuous_intros]: "continuous_on {a .. b} f"
  assumes cg[continuous_intros]: "continuous_on {a .. b} g"
  assumes f: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow>
    (F has_real_derivative f x) (at x within {a .. b})"
  assumes g: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow>
    (G has_vector_derivative g x) (at x within {a .. b})"
  shows integral_by_parts: "integral {a .. b} (\<lambda>x. F x *\<^sub>R g x) =
      F b *\<^sub>R G b - F a *\<^sub>R G a - integral {a .. b} (\<lambda>x. f x *\<^sub>R G x)" (is ?th1)
  and has_integral_by_parts: "((\<lambda>x. F x *\<^sub>R g x) has_integral
      F b *\<^sub>R G b - F a *\<^sub>R G a - integral {a .. b} (\<lambda>x. f x *\<^sub>R G x)) {a .. b}"
    (is ?th2)
proof -
  have [continuous_intros]: "continuous_on {a..b} F" "continuous_on {a..b} G"
    by (auto intro!: has_vector_derivative_continuous_on f g
      simp: has_field_derivative_iff_has_vector_derivative[symmetric])
  have integrable:
    "(\<lambda>x. F x *\<^sub>R g x) integrable_on {a .. b}"
    "(\<lambda>x. f x *\<^sub>R G x) integrable_on {a .. b}"
    by (auto intro!: integrable_continuous_real continuous_intros)
  hence "integral {a..b} (\<lambda>x. F x *\<^sub>R g x) + integral {a..b} (\<lambda>x. f x *\<^sub>R G x) =
      integral {a..b} (\<lambda>x. F x *\<^sub>R g x + f x *\<^sub>R G x)"
    by (rule Henstock_Kurzweil_Integration.integral_add[symmetric])
  also
  note prod = has_vector_derivative_scaleR[OF f g, rule_format]
  have "((\<lambda>x. F x *\<^sub>R g x + f x *\<^sub>R G x) has_integral F b *\<^sub>R G b - F a *\<^sub>R G a) {a..b}"
    by (rule fundamental_theorem_of_calculus[rule_format, OF \<open>a \<le> b\<close> prod]) auto
  from integral_unique[OF this]
  have "integral {a..b} (\<lambda>x. F x *\<^sub>R g x + f x *\<^sub>R G x) = F b *\<^sub>R G b - F a *\<^sub>R G a" .
  finally
  show th1: ?th1
    by (simp add: algebra_simps)
  show ?th2
    unfolding th1[symmetric]
    by (auto intro!: integrable_integral integrable_continuous_real continuous_intros)
qed


subsection \<open>conditionally complete lattice\<close>

lemma bdd_above_cmult:
  "0 \<le> (a :: 'a :: ordered_semiring) \<Longrightarrow> bdd_above S \<Longrightarrow>
    bdd_above ((\<lambda>x. a * x) ` S)"
  by (metis bdd_above_def bdd_aboveI2 mult_left_mono)

lemma Sup_real_mult:
  fixes a::real
  assumes "0 \<le> a"
  assumes "S \<noteq> {}" "bdd_above S"
  shows "a * Sup S = Sup ((\<lambda>x. a * x) ` S)"
  using assms
proof cases
  assume "a = 0" with \<open>S \<noteq> {}\<close> show ?thesis
    by (simp add: cSUP_const)
next
  assume "a \<noteq> 0"
  with \<open>0 \<le> a\<close> have "0 < a"
    by simp
  show ?thesis
  proof (intro antisym)
    have "Sup S \<le> Sup (op * a ` S) / a" using assms
      by (intro cSup_least mult_imp_le_div_pos cSup_upper)
         (auto simp: bdd_above_cmult assms \<open>0 < a\<close> less_imp_le)
    thus "a * Sup S \<le> Sup (op * a ` S)"
      by (simp add: ac_simps pos_le_divide_eq[OF \<open>0<a\<close>])
  qed (insert assms \<open>0 < a\<close>, auto intro!: cSUP_least cSup_upper)
qed

lemma (in conditionally_complete_lattice) cInf_insert2:
  "X \<noteq> {} \<Longrightarrow> bdd_below X \<Longrightarrow> Inf (insert a (insert b X)) = inf (inf a b) (Inf X)"
  by (simp add: local.cInf_insert local.inf_assoc)

lemma (in conditionally_complete_lattice) cSup_insert2:
  "X \<noteq> {} \<Longrightarrow> bdd_above X \<Longrightarrow> Sup (insert a (insert b X)) = sup (sup a b) (Sup X)"
  by (simp add: local.cSup_insert_If local.sup_assoc)

lemma (in conditionally_complete_lattice) Inf_set_fold_inf:
  shows "Inf (set (x#xs)) = fold inf xs x"
  using local.Inf_fin.set_eq_fold local.cInf_eq_Inf_fin by auto

lemma (in conditionally_complete_lattice) Sup_set_fold_sup:
  shows "Sup (set (x#xs)) = fold sup xs x"
  using local.Sup_fin.set_eq_fold local.cSup_eq_Sup_fin by auto

lemma closure_contains_Sup:\<comment>\<open>TODO: reduce to @{thm closure_contains_Inf}, move!\<close>
  fixes S :: "real set"
  assumes "S \<noteq> {}" "bdd_above S"
  shows "Sup S \<in> closure S"
proof -
  have *: "\<forall>x\<in>S. x \<le> Sup S"
    using cSup_upper[of _ S] assms by metis
  {
    fix e :: real
    assume "e > 0"
    then have "Sup S - e < Sup S" by simp
    from less_cSupE[OF this \<open>S \<noteq> {}\<close>] obtain x where "x \<in> S" "Sup S - e < x" .
    with * have "\<exists>x\<in>S. dist x (Sup S) < e"
      by (intro bexI[of _ x]) (auto simp add: dist_real_def)
  }
  then show ?thesis unfolding closure_approachable by auto
qed

lemma closed_contains_Sup:
  fixes S :: "real set"
  shows "S \<noteq> {} \<Longrightarrow> bdd_above S \<Longrightarrow> closed S \<Longrightarrow> Sup S \<in> S"
  by (metis closure_contains_Sup closure_closed)

lemma closed_subset_contains_Sup:
  fixes A C :: "real set"
  shows "closed C \<Longrightarrow> A \<subseteq> C \<Longrightarrow> A \<noteq> {} \<Longrightarrow> bdd_above A \<Longrightarrow> Sup A \<in> C"
  by (metis closure_contains_Sup closure_minimal subset_eq)


subsection \<open>Banach on type class\<close>

lemma banach_fix_type:
  fixes f::"'a::complete_space\<Rightarrow>'a"
  assumes c:"0 \<le> c" "c < 1"
      and lipschitz:"\<forall>x. \<forall>y. dist (f x) (f y) \<le> c * dist x y"
  shows "\<exists>!x. (f x = x)"
  using assms banach_fix[OF complete_UNIV UNIV_not_empty assms(1,2) subset_UNIV, of f]
  by auto

subsection \<open>Float\<close>

definition "trunc p s =
  (let d = truncate_down p s in
  let u = truncate_up p s in
  let ed = abs (s - d) in
  let eu = abs (u - s) in
  if abs (s - d) < abs (u - s) then (d, truncate_up p ed) else (u, truncate_up p eu))"

lemma trunc_nonneg: "0 \<le> s \<Longrightarrow> 0 \<le> trunc p s"
  by (auto simp: trunc_def Let_def zero_prod_def truncate_down_def round_down_nonneg
    intro!: truncate_up_le)

definition "trunc_err p f = f - (fst (trunc p f))"

lemma trunc_err_eq:
  "fst (trunc p f) + (trunc_err p f) = f"
  by (auto simp: trunc_err_def)

lemma trunc_err_le:
  "abs (trunc_err p f) \<le> snd (trunc p f)"
  by (auto simp: trunc_err_def trunc_def Let_def abs_minus_commute
      intro: truncate_up abs_minus_commute)

lemma truncate_down_err_eq_0I: "truncate_up p \<bar>f - truncate_down p f\<bar> = 0 \<Longrightarrow> truncate_down p f = f"
  by (metis abs_le_zero_iff eq_iff_diff_eq_0 truncate_up)

lemma truncate_up_err_eq_0I: "truncate_up p \<bar>truncate_up p f - f\<bar> = 0 \<Longrightarrow> truncate_up p f = f"
  by (metis abs_le_zero_iff eq_iff_diff_eq_0 truncate_up)

lemma trunc_err_eq_zero_iff:
  "trunc_err p f = 0 \<longleftrightarrow> snd (trunc p f) = 0"
  unfolding trunc_err_def trunc_def Let_def
  using truncate_down_err_eq_0I[of p f] truncate_up_err_eq_0I[of p f]
  by auto

lemma mantissa_Float_0[simp]: "mantissa (Float 0 e) = 0"
  by (metis real_of_float_inverse float_zero mantissa_eq_zero_iff zero_float_def)


subsection \<open>Lists\<close>

lemma sum_list_nonneg:
  assumes nn:
    "(\<And>x. x \<in> set xs \<Longrightarrow> f x \<ge> (0::'a::{monoid_add, ordered_ab_semigroup_add}))"
  shows "0 \<le> sum_list (map f xs)"
proof -
  have "0 = sum_list (map (\<lambda>_. 0) xs)"
    by (induct xs) auto
  also have "\<dots> \<le> sum_list (map f xs)"
    by (rule sum_list_mono) (rule assms)
  finally show ?thesis .
qed

lemma
  Ball_set_Cons[simp]: "(\<forall>a\<in>set_Cons x y. P a) \<longleftrightarrow> (\<forall>a\<in>x. \<forall>b\<in>y. P (a#b))"
  by (auto simp: set_Cons_def)

lemma set_cons_eq_empty[iff]: "set_Cons a b = {} \<longleftrightarrow> a = {} \<or> b = {}"
  by (auto simp: set_Cons_def)

lemma listset_eq_empty_iff[iff]: "listset XS = {} \<longleftrightarrow> {} \<in> set XS"
  by (induction XS) auto

lemma sing_in_sings[simp]: "[x] \<in> (\<lambda>x. [x]) ` xd \<longleftrightarrow> x \<in> xd"
  by auto

lemma those_eq_None_set_iff: "those xs = None \<longleftrightarrow> None \<in> set xs"
  by (induction xs) (auto split: option.split)

lemma those_eq_Some_lengthD: "those xs = Some ys \<Longrightarrow> length xs = length ys"
  by (induction xs arbitrary: ys) (auto split: option.splits)

lemma those_eq_Some_map_Some_iff: "those xs = Some ys \<longleftrightarrow> (xs = map Some ys)" (is "?l \<longleftrightarrow> ?r")
proof safe
  assume ?l
  then have "length xs = length ys"
    by (rule those_eq_Some_lengthD)
  then show ?r using \<open>?l\<close>
    by (induction xs ys rule: list_induct2) (auto split: option.splits)
next
  assume ?r
  then have "length xs = length ys"
    by simp
  then show "those (map Some ys) = Some ys" using \<open>?r\<close>
    by (induction xs ys rule: list_induct2) (auto split: option.splits)
qed


subsection \<open>Set(sum)\<close>

lemma sum_eq_nonzero: "finite A \<Longrightarrow> (\<Sum>a\<in>A. f a) = (\<Sum>a\<in>{a\<in>A. f a \<noteq> 0}. f a)"
  by (subst sum.mono_neutral_cong_right) auto

lemma singleton_subsetI:"i \<in> B \<Longrightarrow> {i} \<subseteq> B"
  by auto


subsection \<open>Max\<close>

lemma max_transfer[transfer_rule]:
  assumes [transfer_rule]: "(rel_fun A (rel_fun A (op =))) (op \<le>) (op \<le>)"
  shows "(rel_fun A (rel_fun A A)) max max"
  unfolding max_def[abs_def]
  by transfer_prover

lemma max_power2: fixes a b::real shows "(max (abs a) (abs b))\<^sup>2 = max (a\<^sup>2) (b\<^sup>2)"
  by (auto simp: max_def abs_le_square_iff)

subsection \<open>Uniform Limit\<close>

lemmas bounded_linear_uniform_limit_intros[uniform_limit_intros] =
  bounded_linear.uniform_limit[OF bounded_linear_blinfun_apply]
  bounded_linear.uniform_limit[OF blinfun.bounded_linear_right]
  bounded_linear.uniform_limit[OF bounded_linear_vec_nth]
  bounded_linear.uniform_limit[OF bounded_linear_component_cart]
  bounded_linear.uniform_limit[OF bounded_linear_apply_blinfun]
  bounded_linear.uniform_limit[OF bounded_linear_blinfun_matrix]

lemmas uniform_limit_subset_union = uniform_limit_on_subset[OF uniform_limit_on_Union]

subsection \<open>Bounded Linear Functions\<close>

lift_definition comp3::\<comment>\<open>TODO: name?\<close>
  "('c::real_normed_vector \<Rightarrow>\<^sub>L 'd::real_normed_vector) \<Rightarrow> ('b::real_normed_vector \<Rightarrow>\<^sub>L 'c) \<Rightarrow>\<^sub>L 'b \<Rightarrow>\<^sub>L 'd" is
  "\<lambda>(cd::('c \<Rightarrow>\<^sub>L 'd)) (bc::'b \<Rightarrow>\<^sub>L 'c). (cd o\<^sub>L bc)"
  by (rule bounded_bilinear.bounded_linear_right[OF bounded_bilinear_blinfun_compose])

lemma blinfun_apply_comp3[simp]: "blinfun_apply (comp3 a) b = (a o\<^sub>L b)"
  by (simp add: comp3.rep_eq)

lemma bounded_linear_comp3[bounded_linear]: "bounded_linear comp3"
  by transfer (rule bounded_bilinear_blinfun_compose)

lift_definition comp12::\<comment>\<open>TODO: name?\<close>
  "('a::real_normed_vector \<Rightarrow>\<^sub>L 'c::real_normed_vector) \<Rightarrow> ('b::real_normed_vector \<Rightarrow>\<^sub>L 'c) \<Rightarrow> ('a \<times> 'b) \<Rightarrow>\<^sub>L 'c"
  is "\<lambda>f g (a, b). f a + g b"
  by (auto intro!: bounded_linear_intros
    intro: bounded_linear_compose
    simp: split_beta')

lemma blinfun_apply_comp12[simp]: "blinfun_apply (comp12 f g) b = f (fst b) + g (snd b)"
  by (simp add: comp12.rep_eq split_beta)


subsection \<open>point reflection\<close>

definition preflect::"'a::real_vector \<Rightarrow> 'a \<Rightarrow> 'a" where "preflect \<equiv> \<lambda>t0 t. 2 *\<^sub>R t0 - t"

lemma preflect_preflect[simp]: "preflect t0 (preflect t0 t) = t"
  by (simp add: preflect_def algebra_simps)

lemma preflect_preflect_image[simp]: "preflect t0 ` preflect t0 ` S = S"
  by (simp add: image_image)

lemma is_interval_preflect[simp]: "is_interval (preflect t0 ` S) \<longleftrightarrow> is_interval S"
  by (auto simp: preflect_def[abs_def])

lemma iv_in_preflect_image[intro, simp]: "t0 \<in> T \<Longrightarrow> t0 \<in> preflect t0 ` T"
  by (auto intro!: image_eqI simp: preflect_def algebra_simps scaleR_2)

lemma preflect_tendsto[tendsto_intros]:
  fixes l::"'a::real_normed_vector"
  shows "(g \<longlongrightarrow> l) F \<Longrightarrow> (h \<longlongrightarrow> m) F \<Longrightarrow> ((\<lambda>x. preflect (g x) (h x)) \<longlongrightarrow> preflect l m) F"
  by (auto intro!: tendsto_eq_intros simp: preflect_def)

lemma continuous_preflect[continuous_intros]:
  fixes a::"'a::real_normed_vector"
  shows "continuous (at a within A) (preflect t0)"
  by (auto simp: continuous_within intro!: tendsto_intros)

lemma
  fixes t0::"'a::ordered_real_vector"
  shows preflect_le[simp]: "t0 \<le> preflect t0 b \<longleftrightarrow> b \<le> t0"
    and le_preflect[simp]: "preflect t0 b \<le> t0 \<longleftrightarrow> t0 \<le> b"
    and antimono_preflect: "antimono (preflect t0)"
    and preflect_le_preflect[simp]: "preflect t0 a \<le> preflect t0 b \<longleftrightarrow> b \<le> a"
    and preflect_eq_cancel[simp]: "preflect t0 a = preflect t0 b \<longleftrightarrow> a = b"
  by (auto intro!: antimonoI simp: preflect_def scaleR_2)

lemma preflect_eq_point_iff[simp]: "t0 = preflect t0 s \<longleftrightarrow> t0 = s" "preflect t0 s = t0 \<longleftrightarrow> t0 = s"
  by (auto simp: preflect_def algebra_simps scaleR_2)

lemma preflect_minus_self[simp]: "preflect t0 s - t0 = t0 - s"
  by (simp add: preflect_def scaleR_2)

end
