header {* Auxiliary Lemmas *}
theory ODE_Auxiliarities
imports
  "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
  "~~/src/HOL/Library/Float"
begin

subsection {* Reals *}

lemma image_mult_atLeastAtMost:
  "(\<lambda>x. x * c::real) ` {x..y} = (if x \<le> y then if c > 0 then {x * c .. y * c} else {y * c .. x * c} else {})"
  apply (cases "c = 0")
   apply force
  apply (auto simp: field_simps inverse_eq_divide not_less intro!:
    image_eqI[where x="inverse c * xa" for xa])
  done

lemma image_add_atLeastAtMost:
  "op + c ` {x..y::real} = {c + x .. c + y}"
  by (auto intro: image_eqI[where x="xa - c" for xa])

lemma linear_compose: "(\<lambda>xa. a + xa * b) = (\<lambda>x. a + x) o (\<lambda>x. x * b)"
  by auto

lemma image_linear_atLeastAtMost: "(\<lambda>xa. a + xa * b) ` {c..d::real} =
  (if c \<le> d then if b > 0 then {a + c * b .. a + d * b} else {a + d * b .. a + c * b} else {})"
  by (simp add: linear_compose image_comp [symmetric] image_mult_atLeastAtMost image_add_atLeastAtMost)

lemma min_zero_mult_nonneg_le: "0 \<le> h' \<Longrightarrow> h' \<le> h \<Longrightarrow> min 0 (h * k::real) \<le> h' * k"
  by (metis dual_order.antisym le_cases min_le_iff_disj mult_eq_0_iff mult_le_0_iff mult_right_mono_neg)

lemma max_zero_mult_nonneg_le: "0 \<le> h' \<Longrightarrow> h' \<le> h \<Longrightarrow> h' * k \<le> max 0 (h * k::real)"
  by (metis dual_order.antisym le_cases le_max_iff_disj mult_eq_0_iff mult_right_mono zero_le_mult_iff)

subsection {* Vector Spaces *}

lemma scaleR_dist_distrib_left:
  fixes b c::"'a::real_normed_vector"
  shows "abs a * dist b c = dist (scaleR a b) (scaleR a c)"
  unfolding dist_norm scaleR_diff_right[symmetric] norm_scaleR ..

lemma ex_norm_eq_1: "\<exists>x. norm (x::'a::euclidean_space) = 1"
  by (metis vector_choose_size zero_le_one)

lemma onorm_norm1:
  fixes f::"'a::euclidean_space\<Rightarrow>'b::euclidean_space"
  assumes linear: "linear f"
  assumes n1: "\<And>x. norm x = 1 \<Longrightarrow> norm (f x) \<le> b"
  shows "onorm f \<le> b"
proof (rule onorm[OF linear], safe, cases)
  fix x::'a
  assume "x \<noteq> 0"
  have "norm (f x) = norm (f ((norm x *\<^sub>R inverse (norm x) *\<^sub>R x)))"
    by (simp add: inverse_eq_divide)
  also have "\<dots> = norm x * norm (f (inverse (norm x) *\<^sub>R x))"
    by (subst linear_cmul[OF linear]) simp
  also have "\<dots> \<le> norm x * b"
    by (auto intro!: mult_left_mono n1 simp: inverse_eq_divide `x \<noteq> 0`)
  finally show "norm (f x) \<le> b * norm x" by (simp add: ac_simps)
qed (simp add: linear_0[OF linear])


subsection {* Euclidean Components *}

lemma sqrt_le_rsquare:
  assumes "\<bar>x\<bar> \<le> sqrt y"
  shows "x\<^sup>2 \<le> y"
  using assms real_sqrt_le_iff[of "x\<^sup>2"] by simp

lemma setsum_ge_element:
  fixes f::"'a \<Rightarrow> ('b::ordered_comm_monoid_add)"
  assumes "finite s"
  assumes "i \<in> s"
  assumes "\<And>i. i \<in> s \<Longrightarrow> f i \<ge> 0"
  assumes "el = f i"
  shows "el \<le> setsum f s"
proof -
  have "el = setsum f {i}" by (simp add: assms)
  also have "... \<le> setsum f s" using assms by (intro setsum_mono2) auto
  finally show ?thesis .
qed

lemma norm_nth_le:
  fixes x::"'a::euclidean_space"
  assumes "i \<in> Basis"
  shows "norm (x \<bullet> i) \<le> norm x"
  unfolding norm_conv_dist euclidean_dist_l2[of x] setL2_def
  by (auto intro!: real_le_rsqrt setsum_ge_element assms)

lemma norm_Pair_le:
  shows "norm (x, y) \<le> norm x + norm y"
  unfolding norm_Pair
  by (metis norm_ge_zero sqrt_sum_squares_le_sum)

subsection {* Continuity *}

lemma continuous_on_fst[continuous_on_intros]: "continuous_on X fst"
  unfolding continuous_on_def
  by (intro ballI tendsto_intros)

lemma continuous_on_snd[continuous_on_intros]: "continuous_on X snd"
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

lemma continuous_on_Pair[continuous_on_intros]:
  assumes "continuous_on S f"
  assumes "continuous_on S g"
  shows "continuous_on S (\<lambda>x. (f x, g x))"
  using assms unfolding continuous_on_def
  by (auto intro: tendsto_intros)

lemma continuous_Sigma:
  assumes defined: "y \<in> Pi T X"
  assumes f_cont: "continuous_on (Sigma T X) f"
  assumes y_cont: "continuous_on T y"
  shows "continuous_on T (\<lambda>x. f (x, y x))"
  using continuous_on_compose2[OF continuous_on_subset[where t="(\<lambda>x. (x, y x)) ` T", OF f_cont]
                                  continuous_on_Pair[OF continuous_on_id y_cont]] defined
  by auto

subsection {* Differentiability *}

lemma differentiable_Pair [simp]:
  "f differentiable x in s \<Longrightarrow> g differentiable x in s \<Longrightarrow> (\<lambda>x. (f x, g x)) differentiable x in s"
  unfolding isDiff_def by (blast intro: FDERIV_Pair)

lemma (in bounded_linear)
  differentiable:
  assumes "isDiff (at x within s) g"
  shows "isDiff (at x within s) (\<lambda>x. f (g x))"
  using assms[simplified frechet_derivative_works]
  by (intro differentiableI) (rule FDERIV)

lemmas
  differentiable_mult_right[intro] = bounded_linear.differentiable[OF bounded_linear_mult_right] and
  differentiable_mult_left[intro] = bounded_linear.differentiable[OF bounded_linear_mult_left] and
  differentiable_inner_right[intro] = bounded_linear.differentiable[OF bounded_linear_inner_right] and
  differentiable_inner_left[intro] = bounded_linear.differentiable[OF bounded_linear_inner_left]

lemma (in bounded_bilinear)
  differentiable:
  assumes f: "isDiff (at x within s) f" and g: "isDiff (at x within s) g"
  shows "isDiff (at x within s) (\<lambda>x. prod (f x) (g x))"
  using assms[simplified frechet_derivative_works]
  by (intro differentiableI) (rule FDERIV)

lemmas
  differentiable_mult[intro] = bounded_bilinear.differentiable[OF bounded_bilinear_mult] and
  differentiable_scaleR[intro] = bounded_bilinear.differentiable[OF bounded_bilinear_scaleR]

lemma differentiable_transform_within_weak:
  assumes "x \<in> s" "\<And>x'. x'\<in>s \<Longrightarrow> g x' = f x'" "f differentiable at x within s"
  shows "isDiff (at x within s) g"
  using assms by (intro differentiable_transform_within[OF zero_less_one, where g=g]) auto

lemma differentiable_compose_at:
  "isDiff (at x) f \<Longrightarrow> isDiff (at (f x)) g \<Longrightarrow> isDiff (at x) (\<lambda>x. g (f x))"
  unfolding o_def[symmetric]
  by (rule differentiable_chain_at)

lemma differentiable_compose_within:
  "isDiff (at x within s) f \<Longrightarrow> isDiff (at(f x) within (f ` s)) g \<Longrightarrow>
  isDiff (at x within s) (\<lambda>x. g (f x))"
  unfolding o_def[symmetric]
  by (rule differentiable_chain_within)

lemma differentiable_setsum[intro, simp]:
  assumes "finite s" "\<forall>a\<in>s. Derivative.differentiable (f a) net"
  shows "Derivative.differentiable (\<lambda>x. setsum (\<lambda>a. f a x) s) net"
proof-
 guess f' using bchoice[OF assms(2)[unfolded differentiable_def]] ..
 thus ?thesis unfolding differentiable_def apply-
   apply(rule,rule has_derivative_setsum[where f'=f'])
   by auto
qed

subsection {* Derivatives *}

lemma FDERIV_singletonI: "bounded_linear g \<Longrightarrow> FDERIV f x : {x} :> g"
  by (rule FDERIV_I_sandwich[where e=1]) (auto intro!: bounded_linear_scaleR_left)

lemma vector_derivative_eq_rhs: "(f has_vector_derivative f') F \<Longrightarrow> f' = g' \<Longrightarrow> (f has_vector_derivative g') F"
  by simp

lemma FDERIV_transform:
  assumes "x \<in> s" "\<And>x. x \<in> s \<Longrightarrow> g x = f x"
  assumes "FDERIV f x : s :> f'"
  shows "FDERIV g x : s :> f'"
  using assms by (intro has_derivative_transform_within[OF zero_less_one, where g=g]) auto

lemma FDERIV_If_in_closed:
  assumes f':"\<And>x. x \<in> s \<Longrightarrow> FDERIV f x : s :> f' x"
  assumes g':"\<And>x. x \<in> t \<Longrightarrow> FDERIV g x : t :> g' x"
  assumes connect: "\<And>x. x \<in> s \<inter> t \<Longrightarrow> f x = g x" "\<And>x. x \<in> s \<inter> t \<Longrightarrow> f' x = g' x"
  assumes "closed t" "closed s" "x \<in> s \<union> t"
  shows "FDERIV (\<lambda>x. if x \<in> s then f x else g x) x : (s \<union> t) :> (if x \<in> s then f' x else g' x)"
  (is "(?if has_derivative ?if') _")
  unfolding has_derivative_within
proof (safe intro!: tendstoI)
  fix e::real assume "0 < e"
  let ?D = "\<lambda>x f f' y. (1 / norm (y - x)) *\<^sub>R (f y - (f x + f' (y - x)))"
  have f': "x \<in> s \<Longrightarrow> ((?D x f (f' x)) ---> 0) (at x within s)"
    and g': "x \<in> t \<Longrightarrow> ((?D x g (g' x)) ---> 0) (at x within t)"
    using f' g' by (auto simp: has_vector_derivative_def has_derivative_within)
  let ?thesis = "eventually (\<lambda>y. dist (?D x ?if ?if' y) 0 < e) (at x within s \<union> t)"
  {
    assume "x \<in> s" "x \<in> t"
    from tendstoD[OF f'[OF `x \<in> s`] `0 < e`] tendstoD[OF g'[OF `x \<in> t`] `0 < e`]
    have ?thesis unfolding eventually_at_filter
      by eventually_elim (insert `x \<in> s` `x \<in> t`, auto simp: connect)
  } moreover {
    assume "x \<in> s" "x \<notin> t"
    hence "eventually (\<lambda>x. x \<in> - t) (at x within s \<union> t)" using `closed t`
      by (intro topological_tendstoD) (auto intro: tendsto_ident_at)
    with tendstoD[OF f'[OF `x \<in> s`] `0 < e`] have ?thesis unfolding eventually_at_filter
      by eventually_elim (insert `x \<in> s` `x \<notin> t`, auto simp: connect)
  } moreover {
    assume "x \<notin> s" hence "x \<in> t" using assms by auto
    have "eventually (\<lambda>x. x \<in> - s) (at x within s \<union> t)" using `closed s` `x \<notin> s`
      by (intro topological_tendstoD) (auto intro: tendsto_ident_at)
    with tendstoD[OF g'[OF `x \<in> t`] `0 < e`] have ?thesis unfolding eventually_at_filter 
      by eventually_elim (insert `x \<in> t` `x \<notin> s`, auto simp: connect)
  } ultimately show ?thesis by blast
qed (insert assms, auto intro!: FDERIV_bounded_linear f' g')

lemma linear_continuation:
  assumes f':"\<And>x. x \<in> {a .. b} \<Longrightarrow> (f has_vector_derivative f' x) (at x within {a .. b})"
  assumes g':"\<And>x. x \<in> {b .. c} \<Longrightarrow> (g has_vector_derivative g' x) (at x within {b .. c})"
  assumes connect: "f b = g b" "f' b = g' b"
  assumes x: "x \<in> {a .. c}"
  assumes abc:"a \<le> b" "b \<le> c"
  shows "((\<lambda>x. if x \<le> b then f x else g x) has_vector_derivative
  (\<lambda>x. if x \<le> b then f' x else g' x) x) (at x within {a .. c})"
  (is "(?h has_vector_derivative ?h' x) _")
proof -
  have un: "{a .. b} \<union> {b .. c} = {a .. c}" using assms by auto
  note FDERIV_If_in_closed[FDERIV_intros]
  note f'[simplified has_vector_derivative_def, FDERIV_intros]
  note g'[simplified has_vector_derivative_def, FDERIV_intros]
  have if': "((\<lambda>x. if x \<in> {a .. b} then f x else g x) has_vector_derivative
    (\<lambda>x. if x \<le> b then f' x else g' x) x) (at x within {a .. b}\<union>{b .. c})"
    unfolding has_vector_derivative_def
    using assms
    apply -
    apply (rule FDERIV_eq_intros refl | assumption)+
    apply auto
    done
  show ?thesis
    unfolding has_vector_derivative_def
    by (rule FDERIV_transform[OF x _ if'[simplified un has_vector_derivative_def]]) simp
qed

lemma exists_linear_continuation:
  assumes f':"\<And>x. x \<in> {a .. b} \<Longrightarrow> (f has_vector_derivative f' x) (at x within {a .. b})"
  shows "\<exists>fc. (\<forall>x. x \<in> {a .. b} \<longrightarrow> (fc has_vector_derivative f' x) (at x)) \<and>
    (\<forall>x. x \<in> {a .. b} \<longrightarrow> fc x = f x)"
proof (rule, safe)
  fix x assume "x \<in> {a .. b}" hence "a \<le> b" by simp
  let ?line = "\<lambda>a x. f a + (x - a) *\<^sub>R f' a"
  let ?fc = "(\<lambda>x. if x \<in> {a .. b} then f x else if x \<in> {..a} then ?line a x else ?line b x)"
  have [simp]:
    "\<And>x. x \<in> {a .. b} \<Longrightarrow> (b \<le> x \<longleftrightarrow> x = b)" "\<And>x. x \<in> {a .. b} \<Longrightarrow> (x \<le> a \<longleftrightarrow> x = a)"
    "\<And>x. x \<le> a \<Longrightarrow> (b \<le> x \<longleftrightarrow> x = b)" using `a \<le> b` by auto
  note FDERIV_If_in_closed[FDERIV_intros] f'[simplified has_vector_derivative_def, FDERIV_intros]
  have "(?fc has_vector_derivative f' x) (at x within {a .. b} \<union> ({..a} \<union> {b..}))"
    using `x \<in> {a .. b}` `a \<le> b`
    by (auto intro!: FDERIV_eq_intros simp: has_vector_derivative_def
      simp del: atMost_iff atLeastAtMost_iff)
  moreover have "{a .. b} \<union> ({..a} \<union> {b..}) = UNIV" by auto
  ultimately show "(?fc has_vector_derivative f' x) (at x)" by simp
  show "?fc x = f x" using `x \<in> {a .. b}` by simp
qed


lemma Pair_has_vector_derivative:
  assumes f: "(f has_vector_derivative f') (at x within s)"
      and g: "(g has_vector_derivative g') (at x within s)"
  shows "((\<lambda>x. (f x, g x)) has_vector_derivative (f', g')) (at x within s)"
  using assms by (auto simp: has_vector_derivative_def intro!: FDERIV_eq_intros)

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
  then guess d ..
  with assms show "\<exists>d>0. \<forall>x'\<in>t. 0 < norm (x' - y) \<and> norm (x' - y) < d \<longrightarrow>
    norm (g x' - g y - (x' - y) *\<^sub>R g') / norm (x' - y) < e"
    by auto
next
  show "bounded_linear (\<lambda>x. x *\<^sub>R g')"
    using derivative_linear[OF f'[simplified has_vector_derivative_def], simplified f'g'] assms
    by simp
qed

lemma has_vector_derivative_cong:
  assumes "x \<in> s"
  assumes "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  assumes f'g':"f' = g'"
  assumes "x = y" "s = t"
  shows "(g has_vector_derivative g') (at y within t) =
  (f has_vector_derivative f') (at x within s)"
proof
  assume "(f has_vector_derivative f') (at x within s)"
  from has_vector_derivative_imp this assms
  show "(g has_vector_derivative g') (at y within t)"
    by blast
next
  assume g': "(g has_vector_derivative g') (at y within t)"
  show "(f has_vector_derivative f') (at x within s)"
    using assms g'
    by (intro has_vector_derivative_imp[where f=g and g=f and f'=g' and g'=f'])
      auto
qed

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
    apply (auto simp: Lim_within_union has_derivative_def)
    apply (cases "at x within s = bot", simp_all add: netlimit_within)
    apply (cases "at x within t = bot", simp_all add: netlimit_within)
    done
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
  apply(rule vector_derivative_unique_within_closed_interval)
  using vector_derivative_works[unfolded differentiable_def]
  using assms by (auto simp add: has_vector_derivative_def)

text {* TODO: include this into the attribute DERIV-intros?! *}

lemma DERIV_compose_FDERIV:
  fixes f::"real\<Rightarrow>real"
  assumes "DERIV f (g x) :> f'"
  assumes "FDERIV g x : s :> g'"
  shows "FDERIV (\<lambda>x. f (g x)) x : s :> (\<lambda>x. g' x * f')"
  using assms FDERIV_compose[of g g' x s f "\<lambda>x. x * f'"]
  by (auto simp: deriv_fderiv)

lemmas FDERIV_sin[FDERIV_intros] = DERIV_sin[THEN DERIV_compose_FDERIV]
  and  FDERIV_cos[FDERIV_intros] = DERIV_cos[THEN DERIV_compose_FDERIV]
  and  FDERIV_exp[FDERIV_intros] = DERIV_exp[THEN DERIV_compose_FDERIV]
  and  FDERIV_ln[FDERIV_intros] = DERIV_ln[THEN DERIV_compose_FDERIV]

lemma FDERIV_continuous_on:
  "(\<And>x. x \<in> s \<Longrightarrow> FDERIV f x : s :> f' x) \<Longrightarrow> continuous_on s f"
  by (auto intro!: differentiable_imp_continuous_on differentiableI simp: differentiable_on_def)

lemma taylor_up_within:
  assumes INIT: "n>0" "\<And>t. t \<in> {a .. b} \<Longrightarrow> diff 0 t = f t"
  and DERIV: "\<And>m t. m < n \<Longrightarrow> a \<le> t \<Longrightarrow> t \<le> b \<Longrightarrow>
    ((diff m) has_vector_derivative (diff (Suc m) t)) (at t within {a .. b})"
  and INTERV: "a \<le> c" "c < b"
  shows "\<exists>t. c < t & t < b &
    f b = setsum (%m. (diff m c / real (fact m)) * (b - c)^m) {0..<n} +
      (diff n t / real (fact n)) * (b - c)^n" (is "?taylor f diff")
proof -
  from exists_linear_continuation[of a b, OF DERIV]
  have "\<forall>m. \<exists>d'. m < n \<longrightarrow>
    (\<forall>x \<in> {a .. b}. (d' has_vector_derivative diff (Suc m) x) (at x) \<and> d' x = diff m x)"
    by (metis atLeastAtMost_iff)
  then guess d' unfolding choice_iff .. note d' = this
  let ?diff = "\<lambda>m. if m = n then diff m else d' m"
  have "?taylor (?diff 0) ?diff" using d' by (intro taylor_up[OF _ _ _ `a \<le> c`])
    (auto simp: deriv_fderiv has_vector_derivative_def INIT INTERV)
  thus "?taylor f diff" using d' INTERV INIT by auto
qed

lemma taylor_up_within_vector:
  fixes f::"real \<Rightarrow> 'a::euclidean_space"
  assumes INIT: "n>0" "\<And>t. t \<in> {a .. b} \<Longrightarrow> diff 0 t = f t"
  and DERIV: "\<And>m t. m < n \<Longrightarrow> a \<le> t \<Longrightarrow> t \<le> b \<Longrightarrow>
    ((diff m) has_vector_derivative (diff (Suc m) t)) (at t within {a .. b})"
  and INTERV: "a \<le> c" "c < b"
  shows "\<exists>t. (\<forall>i\<in>Basis::'a set. c < t i & t i < b) \<and>
    f b = setsum (%m. (b - c)^m *\<^sub>R (diff m c /\<^sub>R real (fact m))) {0..<n} +
      setsum (\<lambda>x. (((b - c) ^ n *\<^sub>R diff n (t x) /\<^sub>R real (fact n)) \<bullet> x) *\<^sub>R x) Basis"
proof -
  obtain t where t: "\<forall>i\<in>Basis::'a set. t i > c \<and> t i < b \<and>
    f b \<bullet> i =
      (\<Sum>m = 0..<n. diff m c \<bullet> i / real (fact m) * (b - c) ^ m) +
      diff n (t i) \<bullet> i / real (fact n) * (b - c) ^ n"
  proof (atomize_elim, rule bchoice, safe)
    fix i::'a
    assume "i \<in> Basis"
    have DERIV_0: "\<And>t. t \<in> {a .. b} \<Longrightarrow> (diff 0) t \<bullet> i = f t \<bullet> i" using INIT by simp
    have DERIV_Suc: "\<And>m t. m < n \<Longrightarrow> a \<le> t \<Longrightarrow> t \<le> b \<Longrightarrow>
      ((\<lambda>t. (diff m) t \<bullet> i) has_vector_derivative (diff (Suc m) t \<bullet> i)) (at t within {a .. b})"
      using DERIV by (auto intro!: FDERIV_eq_intros simp: has_vector_derivative_def)
    from taylor_up_within[OF INIT(1) DERIV_0 DERIV_Suc INTERV]
    show "\<exists>t>c. t < b \<and> f b \<bullet> i =
      (\<Sum>m = 0..<n. diff m c \<bullet> i / real (fact m) * (b - c) ^ m) +
      diff n t \<bullet> i / real (fact n) * (b - c) ^ n" by simp
  qed
  have "f b = (\<Sum>i\<in>Basis. (f b \<bullet> i) *\<^sub>R i)" by (rule euclidean_representation[symmetric])
  also have "\<dots> =
      (\<Sum>i\<in>Basis. ((\<Sum>m = 0..<n. (b - c) ^ m *\<^sub>R (diff m c /\<^sub>R real (fact m))) \<bullet> i) *\<^sub>R i) +
      (\<Sum>x\<in>Basis. (((b - c) ^ n *\<^sub>R diff n (t x) /\<^sub>R real (fact n)) \<bullet> x) *\<^sub>R x)"
    using t by (simp add: setsum.distrib inner_setsum_left inverse_eq_divide algebra_simps)
  finally show ?thesis using t by (auto simp: euclidean_representation)
qed

subsection {* Integration *}

lemmas content_real[simp]

lemma integral_atLeastAtMost[simp]:
  "integral {a .. b} (\<lambda>x. c) = content {a .. b} *\<^sub>R c"
  by auto

lemma integral_real_singleton[simp]:
  "integral {a::real} f = 0"
  using integral_refl[of a f] by simp
lemmas integrable_continuous[intro, simp]

lemma mvt_integral:
  fixes f::"'a::euclidean_space\<Rightarrow>'b::euclidean_space"
  assumes f'[FDERIV_intros]: "\<And>x. x \<in> S \<Longrightarrow> FDERIV f x : S :> f' x"
  assumes f'_cont: "\<And>i. i \<in> Basis \<Longrightarrow> continuous_on S (\<lambda>t. f' t i)"
  assumes line_in: "\<And>t. t \<in> {0..1} \<Longrightarrow> x + t *\<^sub>R y \<in> S"
  shows "f (x + y) - f x = integral {0..1} (\<lambda>t. f' (x + t *\<^sub>R y) y)" (is ?th1)
   and  "f (x + y) - f x = (\<Sum>a\<in>Basis. (y \<bullet> a) *\<^sub>R integral {0..1} (\<lambda>t. f' (x + t *\<^sub>R y) a))" (is ?th2)
proof -
  from assms have subset: "(\<lambda>xa. x + xa *\<^sub>R y) ` {0..1} \<subseteq> S" by auto
  note FDERIV_subset[OF _ subset, FDERIV_intros]
  note FDERIV_in_compose[where f="(\<lambda>xa. x + xa *\<^sub>R y)" and g = f, FDERIV_intros]
  note continuous_on_compose2[where f="(\<lambda>xa. x + xa *\<^sub>R y)", continuous_on_intros]
  note continuous_on_subset[OF _ subset, continuous_on_intros]
  have "\<And>t. t \<in> {0..1} \<Longrightarrow>
    ((\<lambda>t. f (x + t *\<^sub>R y)) has_vector_derivative f' (x + t *\<^sub>R y) y) (at t within {0..1})"
    using assms
    by (auto simp: has_vector_derivative_def linear_cmul[OF derivative_is_linear[OF f'], symmetric]
      intro!: FDERIV_eq_intros)
  from fundamental_theorem_of_calculus[rule_format, OF _ this]
  show ?th1
    by (auto intro!: integral_unique[symmetric])

  also have "integral {0..1} (\<lambda>t. f' (x + t *\<^sub>R y) y) =
    integral {0..1} (\<lambda>t. (\<Sum>i\<in>Basis. (f' (x + t *\<^sub>R y) y \<bullet> i) *\<^sub>R i))"
    by (simp add: euclidean_representation)
  also have "\<dots> = integral {0..1}
     (\<lambda>t. \<Sum>i\<in>Basis. (y \<bullet> i) *\<^sub>R (f' (x + t *\<^sub>R y) i))"
  proof (rule integral_spike[OF negligible_empty], safe)
    fix t::real assume t: "t \<in> {0 .. 1}"
    have "(\<Sum>i\<in>Basis. (y \<bullet> i) *\<^sub>R f' (x + t *\<^sub>R y) i) =
      (\<Sum>i\<in>Basis. \<Sum>a\<in>Basis. (y \<bullet> a) *\<^sub>R (f' (x + t *\<^sub>R y) a \<bullet> i) *\<^sub>R i)"
      by (subst setsum_commute[symmetric])
        (simp only: scaleR_setsum_right[symmetric] euclidean_representation)
    also have "\<dots> = (\<Sum>i\<in>Basis. (f' (x + t *\<^sub>R y) y \<bullet> i) *\<^sub>R i)"
      by (subst Derivative.linear_componentwise[OF derivative_is_linear[OF f'], OF line_in[OF t]])
        (simp add: scaleR_setsum_left)
    finally
    show "(\<Sum>i\<in>Basis. (y \<bullet> i) *\<^sub>R f' (x + t *\<^sub>R y) i) = (\<Sum>i\<in>Basis. (f' (x + t *\<^sub>R y) y \<bullet> i) *\<^sub>R i)" .
  qed
  also have "\<dots> = (\<Sum>a\<in>Basis. integral {0..1} (\<lambda>t. (y \<bullet> a) *\<^sub>R f' (x + t *\<^sub>R y) a))"
    by (subst integral_setsum) (auto intro!: continuous_on_intros f'_cont)
  also have "\<dots> = (\<Sum>a\<in>Basis. (y \<bullet> a) *\<^sub>R integral {0..1} (\<lambda>t. f' (x + t *\<^sub>R y) a))"
    using assms
    by (intro setsum_cong[OF refl], subst integral_cmul)
      (auto intro!: continuous_on_intros f'_cont simp: integral_cmul)
  finally show ?th2 .
qed

subsection {* conditionally complete lattice *}

lemma bounded_imp_bdd_above: "bounded S \<Longrightarrow> bdd_above (S :: 'a::ordered_euclidean_space set)"
  by (auto intro: bdd_above_mono dest!: bounded_subset_closed_interval)

lemma bounded_imp_bdd_below: "bounded S \<Longrightarrow> bdd_below (S :: 'a::ordered_euclidean_space set)"
  by (auto intro: bdd_below_mono dest!: bounded_subset_closed_interval)

lemma bdd_above_cmult:
  "0 \<le> (a :: 'a :: ordered_semiring) \<Longrightarrow> bdd_above S \<Longrightarrow> bdd_above ((\<lambda>x. a * x) ` S)"
  by (metis bdd_above_def bdd_aboveI2 mult_left_mono)

lemma Sup_real_mult:
  fixes a::real
  assumes "0 \<le> a"
  assumes "S \<noteq> {}" "bdd_above S"
  shows "a * Sup S = Sup ((\<lambda>x. a * x) ` S)"
  using assms
proof cases
  assume "a = 0" with `S \<noteq> {}` show ?thesis
    by (simp add: SUP_def[symmetric] cSUP_const)
next
  assume "a \<noteq> 0"
  with `0 \<le> a` have "0 < a"
    by simp
  show ?thesis
  proof (intro antisym)
    have "Sup S \<le> Sup (op * a ` S) / a" using assms
      by (intro cSup_least mult_imp_le_div_pos cSup_upper)
         (auto simp: bdd_above_cmult assms `0 < a` less_imp_le)
    thus "a * Sup S \<le> Sup (op * a ` S)"
      by (simp add: ac_simps pos_le_divide_eq[OF `0<a`])
  qed (insert assms `0 < a`, auto intro!: cSup_least cSup_upper)
qed

subsection {* Linorder *}

context linordered_idom
begin

lemma mult_right_le_one_le:
  "0 \<le> x \<Longrightarrow> y \<le> 1 \<Longrightarrow> x * y \<le> x"
  by (auto simp add: mult_le_cancel_left2)

lemma mult_left_le_one_le:
  "0 \<le> x \<Longrightarrow> y \<le> 1 \<Longrightarrow> y * x \<le> x"
  by (auto simp add: mult_le_cancel_right2)

end

subsection {* Banach on type class *}

lemma banach_fix_type:
  fixes f::"'a::complete_space\<Rightarrow>'a"
  assumes c:"0 \<le> c" "c < 1"
      and lipschitz:"\<forall>x. \<forall>y. dist (f x) (f y) \<le> c * dist x y"
  shows "\<exists>!x. (f x = x)"
  using assms banach_fix[OF complete_UNIV UNIV_not_empty assms(1,2) subset_UNIV, of f]
  by auto

subsection {* Float *}

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
  apply (auto simp: trunc_err_def trunc_def Let_def)
  apply (metis truncate_up)
  by (metis abs_minus_commute truncate_up)

lemma trunc_err_eq_zero_iff:
  "trunc_err p f = 0 \<longleftrightarrow> snd (trunc p f) = 0"
  apply (auto simp: trunc_err_def trunc_def Let_def)
  apply (metis abs_le_zero_iff eq_iff_diff_eq_0 truncate_up)
  apply (metis abs_le_zero_iff eq_iff_diff_eq_0 truncate_up)
  done

lemma mantissa_Float_0[simp]: "mantissa (Float 0 e) = 0"
  by (metis float_of_real float_zero mantissa_eq_zero_iff zero_float_def)

subsection {* Lists *}

lemma listsum_nonneg:
  assumes nn: "(\<And>x. x \<in> set xs \<Longrightarrow> f x \<ge> (0::'a::{monoid_add, ordered_ab_semigroup_add}))"
  shows "0 \<le> listsum (map f xs)"
proof -
  have "0 = listsum (map (\<lambda>_. 0) xs)"
    by (induct xs) auto
  also have "\<dots> \<le> listsum (map f xs)"
    by (rule listsum_mono) (rule assms)
  finally show ?thesis .
qed

subsection {* Set(sum) *}

lemma setsum_eq_nonzero: "finite A \<Longrightarrow> (\<Sum>a\<in>A. f a) = (\<Sum>a\<in>{a\<in>A. f a \<noteq> 0}. f a)"
  by (subst setsum_mono_zero_cong_right) auto

lemma singleton_subsetI:"i \<in> B \<Longrightarrow> {i} \<subseteq> B"
  by auto

subsection {* Operator norm *}

lemma onorm_eqI:
  assumes "norm (f y) = x" "norm y = 1"
  assumes "\<And>y. norm y = 1 \<Longrightarrow> norm (f y) \<le> x"
  shows "onorm f = x"
  using assms
  by (auto intro!: cSup_eq_maximum simp: onorm_def SUP_def)

lemma onorm_snd:
  "onorm (snd::('a::euclidean_space*'b::euclidean_space \<Rightarrow> 'b)) = 1"
proof -
  obtain b::'b where "b \<in> Basis" by (metis all_not_in_conv nonempty_Basis)
  hence "norm (snd (0, b)) = 1" "norm (0, b) = 1" by (auto simp: norm_prod_def)
  thus ?thesis
    by (rule onorm_eqI) (metis norm_prod_def real_sqrt_sum_squares_ge2)
qed

lemma onorm_fst:
  "onorm (fst::('a::euclidean_space*'b::euclidean_space \<Rightarrow> 'a)) = 1"
proof -
  obtain b::'a where "b \<in> Basis" by (metis all_not_in_conv nonempty_Basis)
  hence "norm (fst (b, 0)) = 1" "norm (b, 0) = 1" by (auto simp: norm_prod_def)
  thus ?thesis
    by (rule onorm_eqI) (metis norm_prod_def real_sqrt_sum_squares_ge1)
qed

lemma onorm_cmul:
  assumes "bounded_linear f"
  shows "onorm (\<lambda>x::'a::euclidean_space. c *\<^sub>R x) = abs c"
proof -
  from vector_choose_size[of 1] obtain x::'a where "norm (c *\<^sub>R x) = abs c" "norm x = 1" by auto
  thus ?thesis
    by (rule onorm_eqI) simp
qed

subsection {* Max *}

lemma max_transfer[transfer_rule]:
  assumes [transfer_rule]: "(rel_fun A (rel_fun A (op =))) (op \<le>) (op \<le>)"
  shows "(rel_fun A (rel_fun A A)) max max"
  unfolding max_def[abs_def]
  by transfer_prover

lemma max_power2: fixes a b::real shows "(max (abs a) (abs b))\<^sup>2 = max (a\<^sup>2) (b\<^sup>2)"
  by (auto simp: max_def real_abs_le_square_iff)

end
