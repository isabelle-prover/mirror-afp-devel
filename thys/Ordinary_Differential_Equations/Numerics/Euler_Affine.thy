section {* Euler method on Affine Forms *}
theory Euler_Affine
imports
  "~~/src/HOL/Decision_Procs/Dense_Linear_Order"
  "../IVP/Picard_Lindeloef_Qualitative"
  Euler_Affine_Code
begin

text{*\label{sec:euleraform}*}

lemma inf_le_sup_same1: "inf a (b::'a::ordered_euclidean_space) \<le> sup a d"
  by (metis inf.coboundedI1 sup.cobounded1)

lemma fixes a::"'a option"
  shows split_option_bind: "P (a \<bind> f) \<longleftrightarrow> ((a = None \<longrightarrow> P None) \<and> (\<forall>x. a = Some x \<longrightarrow> P (f x)))"
  and split_option_bind_asm:  "P (a \<bind> f) \<longleftrightarrow> (\<not> (a = None \<and> \<not> P None \<or> (\<exists>x. a = Some x \<and> \<not> P (f x))))"
  unfolding atomize_conj
  by (cases a) (auto split: option.split)

lemma msum_subsetI:
  assumes "X \<subseteq> X'" "Y \<subseteq> Y'"
  shows "{(x::'a::group_add) + y |x y. x \<in> X \<and> y \<in> Y} \<subseteq> {x + y |x y. x \<in> X' \<and> y \<in> Y'}"
proof safe
  fix x y
  assume xy: "x \<in> X" "y \<in> Y"
  show "\<exists>x' y'. x + y = x' + y' \<and> x' \<in> X' \<and> y' \<in> Y'"
    apply (rule exI[where x=x])
    apply (rule exI[where x=y])
    using xy assms by auto
qed

subsection {* operations on intervals *}

text {* include separate type of intervals in @{text approximate_sets0} *}

type_synonym 'a ivl = "'a*'a"

definition set_of_ivl::"'a ivl \<Rightarrow> 'a::executable_euclidean_space set"
  where "set_of_ivl x = {fst x .. snd x}"

definition split_ivl::"'a ivl \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> 'a ivl * 'a::executable_euclidean_space ivl"
  where "split_ivl x s i = ((fst x, snd x + (s - snd x \<bullet> i)*\<^sub>Ri), (fst x + (s - fst x \<bullet> i)*\<^sub>Ri, snd x))"

lemma split_ivl:
  assumes "i \<in> Basis"
  assumes "s \<in> {fst X \<bullet> i .. snd X \<bullet> i}"
  shows "x \<in> set_of_ivl X \<longleftrightarrow> x \<in> (set_of_ivl (fst (split_ivl X s i)) \<union> set_of_ivl (snd (split_ivl X s i)))"
  using assms
  by (auto simp: set_of_ivl_def split_ivl_def eucl_le[where 'a='a] not_le algebra_simps inner_Basis)


fun Pair_of_list::"'a list \<Rightarrow> 'a*'a" where
  "Pair_of_list [a, b] = (a, b)"

locale approximate_sets = approximate_sets0 +
  assumes msum_appr_eq: "set_of_appr (msum_appr X Y) = {x + y |x y. x \<in> set_of_appr X \<and> y \<in> set_of_appr Y}"
  assumes inf_of_appr_msum_appr: "inf_of_appr (msum_appr X Y) = inf_of_appr X + inf_of_appr Y"
  assumes sup_of_appr_msum_appr: "sup_of_appr (msum_appr X Y) = sup_of_appr X + sup_of_appr Y"
  assumes inf_of_appr_Inf: "inf_of_appr X \<le> Inf (set_of_appr X)"
  assumes sup_of_appr_Sup: "sup_of_appr X \<ge> Sup (set_of_appr X)"
  assumes sup_of_appr_of_ivl: "l \<le> u \<Longrightarrow> sup_of_appr (appr_of_ivl l u) = u"
  assumes inf_of_appr_of_ivl: "l \<le> u \<Longrightarrow> inf_of_appr (appr_of_ivl l u) = l"
  assumes set_of_appr_of_ivl: "l \<le> u \<Longrightarrow> set_of_appr (appr_of_ivl l u) = {l .. u}"
  assumes set_of_appr_nonempty: "set_of_appr X \<noteq> {}"
  assumes set_of_appr_compact: "compact (set_of_appr X)"
  assumes set_of_appr_convex: "convex (set_of_appr X)"
  assumes set_of_apprs_set_of_appr: "[x] \<in> set_of_apprs [X] \<longleftrightarrow> x \<in> set_of_appr X"
  assumes set_of_apprs_switch: "x#y#xs \<in> set_of_apprs (X#Y#XS) \<Longrightarrow> y#x#xs \<in> set_of_apprs (Y#X#XS)"
  assumes set_of_apprs_rotate: "x#y#xs \<in> set_of_apprs (X#Y#XS) \<Longrightarrow> y#xs@[x] \<in> set_of_apprs (Y#XS@[X])" --"TODO: better use the set (zip ...) property?"
  assumes set_of_apprs_Nil: "xs \<in> set_of_apprs [] \<Longrightarrow> xs = []"
  assumes length_set_of_apprs: "xs \<in> set_of_apprs XS \<Longrightarrow> length xs = length XS"
  assumes set_of_apprs_Cons_ex: "xs \<in> set_of_apprs (X#XS) \<Longrightarrow> (\<exists>y ys. xs = y#ys \<and> y \<in> set_of_appr X \<and> ys \<in> set_of_apprs XS)"
  assumes in_image_Pair_of_listI[simp, intro]:
    "[x, y] \<in> set_of_apprs [X, Y] \<Longrightarrow> (x, y) \<in> Pair_of_list ` set_of_apprs [X, Y]"
  assumes add_appr: "(x # y # ys) \<in> set_of_apprs (X # Y # YS) \<Longrightarrow> (add_appr optns X Y YS) = Some S \<Longrightarrow> (x + y)#x#y#ys \<in> set_of_apprs (S#X#Y#YS)"
  assumes scale_appr: "(x#xs) \<in> set_of_apprs (X#XS) \<Longrightarrow> (scale_appr optns r s X XS) = Some S \<Longrightarrow> ((r/s) *\<^sub>R x # x # xs) \<in> set_of_apprs (S#X#XS)"
  assumes scale_appr_ivl: "s \<in> {r..t} \<Longrightarrow> (x#xs) \<in> set_of_apprs (X#XS) \<Longrightarrow> (scale_appr_ivl optns r t X XS) = Some S \<Longrightarrow> (s *\<^sub>R x # x # xs) \<in> set_of_apprs (S#X#XS)"
  assumes split_appr: "x \<in> set_of_appr X \<Longrightarrow> list_ex (\<lambda>X. x \<in> set_of_appr X) (split_appr optns X)"
  assumes disjoint_apprs: "disjoint_apprs X Y \<Longrightarrow> set_of_appr X \<inter> set_of_appr Y = {}"
begin

lemma set_of_appr_bounded[intro]: "bounded (set_of_appr X)"
  by (rule compact_imp_bounded) (rule set_of_appr_compact)

lemma inf_of_appr[simp]: "x \<in> set_of_appr X \<Longrightarrow> inf_of_appr X \<le> x"
  by (auto intro!: order_trans[OF inf_of_appr_Inf] cInf_lower bounded_imp_bdd_below)

lemma sup_of_appr[simp]: "x \<in> set_of_appr X \<Longrightarrow> x \<le> sup_of_appr X"
  by (auto intro!: order_trans[OF _ sup_of_appr_Sup] cSup_upper bounded_imp_bdd_above)

lemma inf_of_appr_le_sup_of_appr[simp]:
  "inf_of_appr a \<le> sup_of_appr a"
  using set_of_appr_nonempty[of a] order_trans[OF inf_of_appr sup_of_appr]
  by auto

lemma set_of_apprs_Cons: "x#xs \<in> set_of_apprs (X#XS) \<Longrightarrow> xs \<in> set_of_apprs XS"
  by (auto dest: set_of_apprs_Cons_ex)

lemma set_of_apprsE:
  assumes "xs \<in> set_of_apprs (X#XS)"
  obtains y ys where "xs = y # ys" "y \<in> set_of_appr X" "ys \<in> set_of_apprs XS"
  using set_of_apprs_Cons_ex assms by blast

lemma set_of_apprs_rotate3:
  "[x,y, z] \<in> set_of_apprs [X, Y, Z] \<Longrightarrow> [y, z, x] \<in> set_of_apprs [Y,Z,X]"
  by (metis Cons_eq_appendI eq_Nil_appendI set_of_apprs_rotate)

end

lemma tendsto_singleton[tendsto_intros]: "(f \<longlongrightarrow> f x) (at x within {x})"
  by (auto simp: tendsto_def eventually_at_filter)

lemma continuous_on_singleton[continuous_intros]: "continuous_on {x} f"
  unfolding continuous_on_def
  by (auto intro!: tendsto_singleton)

locale approximate_ivp = approximate_ivp0 + approximate_sets +
  fixes ode::"'a  \<Rightarrow> 'a"
  fixes ode_d::"'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes ode_approx:
    "x#xs \<in> set_of_apprs (X'#XS) \<Longrightarrow>
    ode_approx optns (X'#XS) = Some A \<Longrightarrow>
    (ode x # x # xs) \<in> set_of_apprs (A # X' # XS)"
  assumes fderiv[derivative_intros]: "x \<in> X \<Longrightarrow> (ode has_derivative ode_d x) (at x within X)"
  assumes ode_d_approx:
    "x#dx#xs \<in> set_of_apprs (X'#DX'#XS) \<Longrightarrow>
     ode_d_approx optns (X'#DX'#XS) = (Some D') \<Longrightarrow>
     (ode_d x dx # x # dx # xs) \<in> set_of_apprs (D' # X' # DX' # XS)"
  assumes cont_fderiv: "continuous_on UNIV (\<lambda>((t::real, x), (dt::real, y)). ode_d x y)"
    --{* TODO: get rid of the reals *}
    --{* TODO: NOTE: if UNIV is too strong, then also a bound on
      @{term "(\<lambda>(x, y). ode_d x y) ` (X \<times> cball 0 1)"} suffices for every step
      (cf. @{thm compact_continuously_diff.ex_onorm_bound}) -- but this would need to be computed
      in every step *}
begin

lemma fderiv'[derivative_intros]: "((\<lambda>(t, y). ode y) has_derivative (\<lambda>(t, x) (dt, dx). ode_d x dx) (t, x)) (at (t, x) within X)"
  by (auto intro!: derivative_eq_intros has_derivative_compose[of snd])

lemma picard_approx:
  assumes appr: "ode_approx optns [X] = Some Y"
  assumes bb: "inf_of_appr Y = l" "sup_of_appr Y = u"
  assumes x_in: "(\<And>t. t \<in> {t0 .. t1} \<Longrightarrow> x t \<in> set_of_appr X)"
  assumes cont: "continuous_on {t0 .. t1} x"
  assumes ivl: "t0 \<le> t1"
  shows "x0 + integral {t0..t1} (\<lambda>t. ode (x t)) \<in> {x0 + (t1 - t0) *\<^sub>R l .. x0 + (t1 - t0) *\<^sub>R u}"
proof -
  {
    fix t::real
    assume "0 \<le> t" "t \<le> 1"
    hence "t * (t1 - t0) \<le> t1 - t0" using ivl
      by (auto intro!: mult_left_le_one_le )
    hence "t0 + t * (t1 - t0) \<le> t1"
      by (simp add: algebra_simps)
  } note segment[simp] = this
  {
    fix t::real
    assume t: "t \<in> {0 .. 1}"
    have "ode (x (t0 + t * (t1 - t0))) \<in> set_of_appr Y"
      unfolding set_of_apprs_set_of_appr[symmetric]
      apply (rule set_of_apprs_Cons)
      apply (rule set_of_apprs_switch)
      apply (rule ode_approx[OF _ appr])
      using t ivl
      by (auto intro!: x_in ode_approx simp: set_of_apprs_set_of_appr)
    also from bb inf_of_appr sup_of_appr have "set_of_appr Y \<subseteq> {l..u}" by auto
    finally have "ode (x (t0 + t * (t1 - t0))) \<in> {l..u}" .
  } note ode_lu = this
  have cont_ode_x: "continuous_on {t0..t1} (\<lambda>xa. ode (x xa))"
    using ivl
    by (auto intro!: has_derivative_continuous_on[OF fderiv] continuous_on_compose2[of _ ode _ x] cont)
  have cmp: "(\<lambda>t. ode (x (t0 + t * (t1 - t0)))) = (\<lambda>t. ode (x t)) o (\<lambda>t. (t0 + t * (t1 - t0)))"
    by auto
  have cnt: "continuous_on {0 .. 1}(\<lambda>t. ode (x (t0 + t * (t1 - t0))))"
    unfolding cmp using ivl
    by (intro continuous_on_compose)
      (auto intro!: continuous_intros simp: image_linear_atLeastAtMost cont_ode_x not_less)
  have "integral {t0..t1} (\<lambda>t. ode (x t)) =
    (t1 - t0) *\<^sub>R integral {0..1} (\<lambda>t. ode (x (t0 + t * (t1 - t0))))"
    using ivl
    by (intro mvt_integral(2)[of _ "\<lambda>t1. integral {t0..t1} (\<lambda>t. ode (x t))" "\<lambda>t u. u *\<^sub>R ode (x t)"
        t0 "t1 - t0", simplified, OF _ cont_ode_x])
      (auto intro!: integral_has_vector_derivative[OF cont_ode_x]
      simp: has_vector_derivative_def[symmetric])
  also
  {
    have "integral {0..1} (\<lambda>t. ode (x (t0 + t * (t1 - t0)))) \<le> integral {0..1} (\<lambda>t::real . u)"
      using ode_lu
      by (auto simp: eucl_le[where 'a='a] intro!: order_trans[OF integral_component_ubound_real] cnt)
    moreover have "integral {0..1} (\<lambda>t::real . l) \<le> integral {0..1} (\<lambda>t. ode (x (t0 + t * (t1 - t0))))"
      using ode_lu
      by (auto simp: eucl_le[where 'a='a] intro!: order_trans[OF _ integral_component_lbound_real] cnt)
    ultimately have "integral {0..1} (\<lambda>t. ode (x (t0 + t * (t1 - t0)))) \<in> {l .. u}"
      by simp
    hence "(t1 - t0) *\<^sub>R integral {0..1} (\<lambda>t. ode (x (t0 + t * (t1 - t0)))) \<in> {(t1 - t0) *\<^sub>R l .. (t1 - t0) *\<^sub>R u}"
      using ivl
      by (auto intro!: scaleR_left_mono)
  }
  finally show ?thesis by auto
qed

lemma picard_approx_ivl:
  assumes appr: "ode_approx optns [X] = Some Y"
  assumes bb: "inf_of_appr Y = l" "sup_of_appr Y = u"
  assumes x_in: "(\<And>t. t \<in> {t0 .. t1} \<Longrightarrow> x t \<in> set_of_appr X)"
  assumes cont: "continuous_on {t0 .. t1} x"
  assumes ivl: "t0 \<le> t" "t \<le> t1"
  shows "x0 + integral {t0..t} (\<lambda>t. ode (x t)) \<in> {x0 + inf 0 ((t1 - t0) *\<^sub>R l) .. x0 + sup 0 ((t1 - t0) *\<^sub>R u)}"
  using ivl inf_of_appr_le_sup_of_appr[of Y]
  by (intro set_rev_mp[OF picard_approx[OF appr bb x_in continuous_on_subset[OF cont]]])
    (auto simp: eucl_le[where 'a='a] inner_Basis_inf_left inner_Basis_sup_left inf_real_def
      sup_real_def min_def max_def zero_le_mult_iff not_le inner_add_left not_less bb
      intro: mult_right_mono mult_nonneg_nonpos mult_right_mono_neg)

text {* automatic Picard operator *}

lemma P_appr_Some_ode_approxE:
  assumes "P_appr optns X0 h X = Some R"
  obtains Y where "ode_approx optns [X] = Some Y" "R = extend_appr X0 (inf 0 (h *\<^sub>R inf_of_appr Y)) (sup 0 (h *\<^sub>R sup_of_appr Y))"
  using assms
  unfolding P_appr_def
  using assms by (auto simp: P_appr_def)

lemma P_appr:
  assumes x0: "x0 \<in> set_of_appr X0"
  assumes x: "\<And>t. t \<in> {t0..t1} \<Longrightarrow> x t \<in> set_of_appr X"
  assumes cont: "continuous_on {t0..t1} x"
  assumes h': "0 \<le> t1 - t0" "t1 - t0 \<le> h"
  assumes P_res: "P_appr optns X0 h X = Some R"
  shows "x0 + integral {t0..t1} (\<lambda>t. ode (x t)) \<in> set_of_appr R"
proof -
  from P_res obtain Y where Y: "ode_approx optns [X] = Some Y"
    "R = extend_appr X0 (inf 0 (h *\<^sub>R inf_of_appr Y)) (sup 0 (h *\<^sub>R sup_of_appr Y))"
    by (rule P_appr_Some_ode_approxE)
  have "x0 + integral {t0 .. t1} (\<lambda>t. ode (x t)) \<in>
    {x0 + inf 0 ((t1 - t0) *\<^sub>R inf_of_appr Y) .. x0 + sup 0 ((t1 - t0) *\<^sub>R sup_of_appr Y)}"
    using assms
    by (intro picard_approx_ivl[OF Y(1) refl refl x cont]) auto
  also have "\<dots> \<subseteq> {x + y |x y. x \<in> set_of_appr X0 \<and>
      y \<in> {inf 0 ((t1 - t0) *\<^sub>R inf_of_appr Y) .. sup 0 ((t1 - t0) *\<^sub>R sup_of_appr Y)}}"
    apply safe
    subgoal for x
      apply (rule exI[where x=x0])
      apply (rule exI[where x="x - x0"])
      using assms
      apply (simp add: algebra_simps)
      done
    done
  also have "\<dots> \<subseteq> {x + y |x y. x \<in> set_of_appr X0 \<and> y \<in> {inf 0 (h *\<^sub>R inf_of_appr Y) .. sup 0 (h *\<^sub>R sup_of_appr Y)}}"
    using assms
    by (intro msum_subsetI) (auto simp: eucl_le[where 'a='a] inner_Basis_inf_left inf_real_def
      inner_Basis_sup_left sup_real_def not_le not_less min_zero_mult_nonneg_le max_zero_mult_nonneg_le)
  also have "\<dots> = set_of_appr R"
    using assms
    by (simp add: inf_le_sup_same1 scaleR_left_mono set_of_appr_of_ivl Y msum_appr_eq)
  finally show ?thesis .
qed

lemma P_iterE:
assumes "P_iter optns X0 h i X = Some X'"
obtains
  X'' where "P_appr optns X0 h X' = Some X''"
    "{inf_of_appr X'' .. sup_of_appr X''} \<subseteq> {inf_of_appr X' .. sup_of_appr X'}"
  using assms
proof (induct i arbitrary: X)
  case (Suc i) thus ?case
    by (cases "P_appr optns X0 h X") (auto simp: split: split_if_asm )
qed simp

lemma extend_appr_ivl:
  assumes "set_of_appr X = {inf_of_appr X .. sup_of_appr X}"
  assumes le2: "a \<le> 0" "0 \<le> b"
  assumes set_of_apprI: "\<And>x. inf_of_appr X \<le> x \<Longrightarrow> x \<le> sup_of_appr X \<Longrightarrow> x \<in> set_of_appr X"
  shows "set_of_appr (extend_appr X a b) = {inf_of_appr X + a .. sup_of_appr X + b}"
proof -
  have "{inf_of_appr X + a..sup_of_appr X + b} = {x + y|x y. x \<in> {inf_of_appr X ..sup_of_appr X} \<and> y \<in> {a .. b}}"
  proof safe
    fix x assume x: "x \<in> {inf_of_appr X + a..sup_of_appr X + b}"
    let ?x' = "\<Sum>i\<in>Basis. (if (x \<bullet> i) \<le> inf_of_appr X \<bullet> i then inf_of_appr X \<bullet> i
      else if (x \<bullet> i) \<le> sup_of_appr X \<bullet> i then x \<bullet> i else sup_of_appr X \<bullet> i)*\<^sub>R i"
    show "\<exists>x' y. x = x' + y \<and> x' \<in> {inf_of_appr X..sup_of_appr X} \<and> y \<in> {a..b}"
      apply (rule exI[where x = ?x'])
      apply (rule exI[where x = "x - ?x'"])
      unfolding assms
      using le2 x inf_of_appr_le_sup_of_appr
      by (auto simp: eucl_le[where 'a='a] algebra_simps intro!: set_of_apprI)
  qed (auto intro!: add_mono)
  also have "\<dots> = set_of_appr (extend_appr X a b)"
    unfolding msum_appr_eq using le2
    by (intro antisym msum_subsetI) (auto simp: set_of_appr_of_ivl assms(1))
  finally show ?thesis by simp
qed

lemma P_appr_ivl:
  assumes "P_appr optns X0 h X = Some X'"
  assumes "h \<ge> 0"
  assumes ivl_0: "{inf_of_appr X0..sup_of_appr X0} = set_of_appr X0"
  shows "{inf_of_appr X'..sup_of_appr X'} = set_of_appr X'"
proof -
  from assms obtain z where z: "ode_approx optns [X] = Some z"
    and X': "extend_appr X0 (inf 0 (h *\<^sub>R inf_of_appr z)) (sup 0 (h *\<^sub>R sup_of_appr z)) = X'"
    by (auto simp: P_appr_def)
  have [simp]: "inf 0 (h *\<^sub>R inf_of_appr z) \<le> sup 0 (h *\<^sub>R sup_of_appr z)"
    by (metis inf.coboundedI1 sup.cobounded1)
  show ?thesis
    unfolding X'[symmetric]
    by (auto simp: ivl_0[symmetric] extend_appr_ivl inf_of_appr_msum_appr sup_of_appr_msum_appr
      inf_of_appr_of_ivl sup_of_appr_of_ivl)
qed

lemma P_iter_ivl:
  assumes "P_iter optns X0 h i X = Some X'"
  assumes "h \<ge> 0"
  assumes "{inf_of_appr X0..sup_of_appr X0} = set_of_appr X0"
  assumes "{inf_of_appr X..sup_of_appr X} = set_of_appr X"
  shows "{inf_of_appr X'..sup_of_appr X'} = set_of_appr X'"
  using assms
proof (induct i arbitrary: X X')
  case (Suc i)
  thus ?case
  proof (cases "P_appr optns X0 h X")
    fix a
    assume *: "P_appr optns X0 h X = Some a"
    show ?thesis
    proof (cases "inf_of_appr X \<le> inf_of_appr a \<and> sup_of_appr a \<le> sup_of_appr X")
      case True
      with * Suc(2) have "X' = X" by simp
      with Suc show ?thesis by simp
    next
      case False
      with * Suc(2) have ind_step: "P_iter optns X0 h i
         (appr_of_ivl
           (inf (inf_of_appr a) (inf_of_appr X) -
            (if i mod widening_mod optns = 0 then \<bar>inf_of_appr a - inf_of_appr X\<bar> else 0))
           (sup (sup_of_appr a) (sup_of_appr X) +
            (if i mod widening_mod optns = 0 then \<bar>sup_of_appr a - sup_of_appr X\<bar> else 0))) =
              Some X'"
        by (simp add: *)
      have inf_le_sup: "inf (inf_of_appr a) (inf_of_appr X) \<le> sup (sup_of_appr a) (sup_of_appr X)"
        by (metis inf_of_appr_le_sup_of_appr le_infI2 le_supI2)
      hence min_le_max: "inf (inf_of_appr a) (inf_of_appr X) - \<bar>inf_of_appr a - inf_of_appr X\<bar>
           \<le> sup (sup_of_appr a) (sup_of_appr X) + \<bar>sup_of_appr a - sup_of_appr X\<bar>"
        unfolding diff_conv_add_uminus
        by (rule add_mono) (metis abs_ge_zero dual_order.trans neg_le_0_iff_le)
      show "{inf_of_appr X'..sup_of_appr X'} = set_of_appr X'"
        by (rule Suc(1)[OF ind_step])
         (auto simp add: Suc inf_of_appr_of_ivl sup_of_appr_of_ivl min_le_max set_of_appr_of_ivl inf_le_sup)
    qed
  qed simp
qed simp

lemma P_iter_mono:
  assumes "P_iter optns X0 h i X = Some X'"
  shows "set_of_appr X0 \<subseteq> {inf_of_appr X'..sup_of_appr X'}"
proof -
  from P_iterE[OF assms(1)] obtain X'' where X'':
    "P_appr optns X0 h X' = Some X''"
    "{inf_of_appr X''..sup_of_appr X''} \<subseteq> {inf_of_appr X'..sup_of_appr X'}" .
  from X''(1) have "set_of_appr X0 \<subseteq> set_of_appr X''"
    by (force simp: P_appr_def msum_appr_eq set_of_appr_of_ivl inf_le_sup_same1)
  also have "\<dots> \<subseteq> {inf_of_appr X''..sup_of_appr X''}"
    by auto
  also note X''(2)
  finally show ?thesis .
qed

lemma P_iter_eq:
  assumes "P_iter optns X0 h i X = Some X'"
  assumes "h \<ge> 0"
  assumes "{inf_of_appr X0..sup_of_appr X0} = set_of_appr X0"
  assumes "{inf_of_appr X..sup_of_appr X} = set_of_appr X"
  shows "set_of_appr X' = {inf_of_appr X'..sup_of_appr X'}"
  using assms
  by (simp add: P_iter_ivl[OF assms])

lemma P_iter_cert_stepsize:
  assumes "cert_stepsize optns X0 h n i = Some (h', X')"
  shows "P_iter optns (ivl_appr_of_appr X0) h' n (ivl_appr_of_appr X0) = Some X'"
  using assms
  by (induct i arbitrary: h) (auto split: option.split_asm)

definition step_ivp::"real \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'b \<Rightarrow> 'a ivp" where
"step_ivp t0 x0 t1 CX =
  \<lparr>ivp_f = (\<lambda>(t, x). ode x),
  ivp_t0 = t0, ivp_x0 = x0,
  ivp_T = {t0 .. t1},
  ivp_X = set_of_appr CX\<rparr>"

lemma step_ivp_simps[simp]:
  "ivp_f (step_ivp t0 x0 t1 CX) = (\<lambda>(t, x). ode x)"
  "ivp_t0 (step_ivp t0 x0 t1 CX) = t0"
  "ivp_x0 (step_ivp t0 x0 t1 CX) = x0"
  "ivp_T (step_ivp t0 x0 t1 CX) = {t0 .. t1}"
  "ivp_X (step_ivp t0 x0 t1 CX) = set_of_appr CX"
  by (simp_all add: step_ivp_def)

definition euler_ivp::"real \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a ivp"
where
"euler_ivp t0 x0 t1 =
  \<lparr>ivp_f = (\<lambda>(t, x). ode x),
  ivp_t0 = t0, ivp_x0 = x0,
  ivp_T = {t0 .. t1},
  ivp_X = UNIV\<rparr>"

lemma euler_ivp_simps[simp]:
  "ivp_f (euler_ivp t0 x0 t1) = (\<lambda>(t, x). ode x)"
  "ivp_t0 (euler_ivp t0 x0 t1) = t0"
  "ivp_x0 (euler_ivp t0 x0 t1) = x0"
  "ivp_T (euler_ivp t0 x0 t1) = {t0 .. t1}"
  "ivp_X (euler_ivp t0 x0 t1) = UNIV"
  by (simp_all add: euler_ivp_def)

definition global_ivp::"real \<Rightarrow> 'a \<Rightarrow> 'a ivp" where
"global_ivp t0 x0 =
  \<lparr>ivp_f = (\<lambda>(t, x). ode x),
  ivp_t0 = t0, ivp_x0 = x0,
  ivp_T = UNIV,
  ivp_X = UNIV\<rparr>"

lemma global_ivp_simps[simp]:
  "ivp_f (global_ivp t0 x0) = (\<lambda>(t, x). ode x)"
  "ivp_t0 (global_ivp t0 x0) = t0"
  "ivp_x0 (global_ivp t0 x0) = x0"
  "ivp_T (global_ivp t0 x0) = UNIV"
  "ivp_X (global_ivp t0 x0) = UNIV"
  by (simp_all add: global_ivp_def)

text {* execution of @{term euler_step} *}
context
  fixes optns x0 X0 h RES_ivl RES
  assumes x0: "x0 \<in> set_of_appr X0"
  assumes pos_prestep: "0 < stepsize optns"
  assumes euler_step_returns: "euler_step optns X0 = Some (h, RES_ivl, RES)"
begin

text {* intermediate results *}
context
  fixes n i CX X0' F D ERR S S' X1 CX1 t0 t1
  assumes pos_step: "0 < h"
  assumes step_eq: "t0 + h = t1"
  assumes certified_stepsize: "cert_stepsize optns X0 (stepsize optns) n i = Some (h, CX)"
  assumes bounded_ode: "ode_approx optns [X0] = Some X0'"
  assumes bounded_total_ode: "ode_approx optns [CX] = Some F"
  assumes bounded_ode_d: "ode_d_approx optns [CX, F] = Some D"
  assumes bounded_err: "scale_appr optns (h*h) 2 (ivl_appr_of_appr D) [] = Some ERR"
  assumes bounded_scale_euler: "scale_appr optns h 1 X0' [X0] = Some S"
  assumes bounded_scale_ivl_euler: "scale_appr_ivl optns 0 h X0' [X0] = Some S'"
  assumes bounded_add_euler: "add_appr optns X0 S [] = Some X1"
  assumes bounded_add_euler_ivl: "add_appr optns X0 S' [] = Some CX1"
  assumes RES_ivl: "RES_ivl = msum_appr CX1 (appr_of_ivl (inf 0 (inf_of_appr ERR)) (sup 0 (sup_of_appr ERR)))"
  assumes RES: "RES = msum_appr X1 (ivl_appr_of_appr ERR)"
begin

lemma nonneg_step: "0 \<le> h" using pos_step by auto
lemma step_less: "t0 < t1" using step_eq pos_step by auto

lemma set_of_appr_eq: "set_of_appr CX = {inf_of_appr CX .. sup_of_appr CX}"
  by (subst P_iter_eq[OF P_iter_cert_stepsize[OF certified_stepsize]])
    (auto simp: ivl_appr_of_appr_def sup_of_appr_of_ivl inf_of_appr_of_ivl set_of_appr_of_ivl nonneg_step)

lemma x0_in_CX1: "x0 \<in> set_of_appr CX1"
proof -
  from nonneg_step have "0 \<in> {0 .. h}" by auto
  from scale_appr_ivl[OF this ode_approx[OF x0[simplified set_of_apprs_set_of_appr[symmetric]] bounded_ode] bounded_scale_ivl_euler]
  have "[x0, 0] \<in> set_of_apprs [X0, S']"
    by (metis pth_4(1) set_of_apprs_Cons set_of_apprs_rotate3)
  from add_appr[OF this bounded_add_euler_ivl]
  show "x0 \<in> set_of_appr CX1"
    by (metis monoid_add_class.add.right_neutral set_of_apprs_Cons set_of_apprs_rotate3
      set_of_apprs_set_of_appr)
qed

interpretation ivp_on_interval "step_ivp t0 x0 t1 CX" t1
  using nonneg_step step_eq
proof (unfold_locales, simp_all add: step_ivp_def)
  have "x0 \<in> set_of_appr (ivl_appr_of_appr X0)"
     by (auto simp: ivl_appr_of_appr_def set_of_appr_of_ivl x0)
  also have "\<dots> \<subseteq> {inf_of_appr CX..sup_of_appr CX}"
    by (metis P_iter_mono P_iter_cert_stepsize certified_stepsize)
  also have "\<dots> = set_of_appr CX"
    by (rule set_of_appr_eq[symmetric])
  finally show "x0 \<in> set_of_appr CX" .
qed

interpretation continuous T X f
  using iv_defined
  by unfold_locales (auto simp add: step_ivp_def split_beta
    intro!: continuous_on_compose2[of _ ode _ snd] has_derivative_continuous_on[OF fderiv] continuous_intros)

interpretation compact_domain X
  by standard (auto simp: step_ivp_def set_of_appr_eq compact_interval)

interpretation derivative_on_convex T X f "\<lambda>(t, x) (dt, dx). ode_d x dx"
  by standard
    (auto simp: step_ivp_def step_less set_of_appr_eq  nonneg_step less_imp_le convex_real_interval
      convex_closed_interval
      simp del: inf_of_appr sup_of_appr
      intro!: derivative_eq_intros has_derivative_eq_rhs[OF has_derivative_compose, of snd])

interpretation unique_on_closed_cont_diff "step_ivp t0 x0 t1 CX" t1 "\<lambda>(t, x) (dt, dx). ode_d x dx"
proof unfold_locales
  let ?step = "step_ivp t0 x0 t1 CX"
  fix t x
  assume xt0: "x (ivp_t0 ?step) = ivp_x0 ?step"
  from this have "x t0 \<in> set_of_appr (ivl_appr_of_appr X0)" using x0
    by (auto simp: ivl_appr_of_appr_def set_of_appr_of_ivl)
  moreover
  assume "x \<in> {ivp_t0 ?step..t} \<rightarrow> ivp_X ?step"
  from this have "\<And>ta. ta \<in> {t0..t0 + (t - t0)} \<Longrightarrow> x ta \<in> set_of_appr CX" by auto
  moreover
  assume "continuous_on {ivp_t0 ?step..t} x"
  from this have "continuous_on {t0..t0 + (t - t0)} x" by simp
  moreover
  assume "t \<in> ivp_T ?step"
  from this step_eq have "0 \<le> t0 + (t - t0) - t0" "t0 + (t - t0) - t0 \<le> h"
    by simp_all
  moreover
  from P_iter_cert_stepsize[OF certified_stepsize, THEN P_iterE]
  obtain X'' where "P_appr optns (ivl_appr_of_appr X0) h CX = Some X''"
    and subset: "{inf_of_appr X''..sup_of_appr X''} \<subseteq> {inf_of_appr CX..sup_of_appr CX}" .
  note this(1)
  ultimately have "x t0 + integral {t0..t0 + (t - t0)} (\<lambda>t. ode (x t)) \<in> set_of_appr X''"
    by (rule P_appr)
  also have "\<dots> \<subseteq> {inf_of_appr X''..sup_of_appr X''}" by auto
  also note subset
  also note set_of_appr_eq[symmetric]
  finally show "ivp_x0 ?step + integral {ivp_t0 ?step..t} (\<lambda>t. ivp_f ?step (t, x t)) \<in> ivp_X ?step"
    using xt0 by simp
qed (rule continuous_on_subset[where s=UNIV ], simp_all add: step_ivp_def cont_fderiv)

interpretation derivative_set_bounded T X f "\<lambda>(t, x) (dt, dx). ode_d x dx" "Pair_of_list ` set_of_apprs [CX, F]"
  "{inf_of_appr D .. sup_of_appr D}"
proof
  have "Pair_of_list ` set_of_apprs [CX, F] \<subseteq> set_of_appr CX \<times> set_of_appr F"
    by (auto elim!: set_of_apprsE dest!: set_of_apprs_Nil)
  moreover have "bounded (\<dots>)"
    by (rule set_of_appr_compact compact_imp_bounded bounded_Times)+
  ultimately show "bounded (Pair_of_list ` set_of_apprs [CX, F])"
    by (blast intro: bounded_subset)
  show "bounded {inf_of_appr D .. sup_of_appr D}"
    by (simp add: bounded_closed_interval)
  fix t x
  assume "t \<in> T" "x \<in> X"
  hence x: "[x] \<in> set_of_apprs [CX]" by (auto simp: step_ivp_def set_of_apprs_set_of_appr)
  with ode_approx
  have "[x, ode x] \<in> set_of_apprs [CX, F]"
    by (auto intro!: ode_approx bounded_total_ode intro: set_of_apprs_switch)
  thus "(x, ivp_f (step_ivp t0 x0 t1 CX) (t, x)) \<in> Pair_of_list ` set_of_apprs [CX, F]"
    by (auto simp: step_ivp_def)
next
  fix t x d
  assume "t \<in> T"
  assume "(x, d) \<in> Pair_of_list ` set_of_apprs [CX, F]"
  then obtain xs where xs: "Pair_of_list xs = (x, d)" "xs \<in> set_of_apprs [CX, F]" by auto
  hence "xs = [x, d]"
    by (auto elim!: set_of_apprsE dest!: set_of_apprs_Nil)
  with xs have "[x, d] \<in> set_of_apprs [CX, F]" by simp
  hence "[x, d, ode_d x d] \<in> set_of_apprs [CX, F, D]"
    by (auto intro!: ode_d_approx bounded_ode_d intro: set_of_apprs_switch set_of_apprs_rotate3)
  hence "ode_d x d \<in> set_of_appr D"
    unfolding set_of_apprs_set_of_appr[symmetric]
    by (blast intro: set_of_apprs_Cons)
  thus "(case (t, x) of (t, x) \<Rightarrow> \<lambda>(dt, dx). ode_d x dx) (1, d) \<in> {inf_of_appr D .. sup_of_appr D}"
    by auto
qed (simp add: is_interval_closed_interval)

lemma solution_t0': "solution t0 = x0"
  using solution_t0 by (simp add: step_ivp_def)

lemma t0': "ivp_t0 (step_ivp t0 x0 t1 CX) = t0"
  by (simp add: step_ivp_def)

lemma interval': "T = {t0..t1}"
  by (auto simp: step_ivp_def)

lemma euler_consistent_solution':
  assumes "t1' \<in> {t0 .. t1}"
  shows "solution (t0 + (t1' - t0)) - discrete_evolution (euler_increment f) (t0 + (t1' - t0)) t0 (solution t0) \<in>
    op *\<^sub>R ((t1' - t0)\<^sup>2 / 2) ` {inf_of_appr D..sup_of_appr D}"
  using pos_step step_less assms solution_in_D solution_has_deriv
  by (intro euler_consistent_traj_set[where u=t1]) (auto intro!:  solution_has_deriv simp: )

lemma euler_consistent_solution:
  assumes "t1' \<in> {t0 .. t1}"
  shows "solution (t0 + (t1' - t0)) - discrete_evolution (euler_increment f) (t0 + (t1' - t0)) t0 x0 \<in>
    op *\<^sub>R ((t1' - t0)\<^sup>2 / 2) ` {inf_of_appr D..sup_of_appr D}"
  using euler_consistent_solution'[simplified solution_t0', OF assms] .

lemma error_overapproximation:
  shows  "solution (t0 + h) \<in> set_of_appr RES"
proof -
  def euler_res \<equiv> "discrete_evolution (euler_increment f) (t0 + h) t0 x0"
  have step_ok: "t0 + h \<in> {t0 .. t1}" using step_eq pos_step by auto
  from this have "solution (t0 + h) \<in> {euler_res + (h^2 / 2) *\<^sub>R inf_of_appr D .. euler_res + (h^2 / 2) *\<^sub>R sup_of_appr D}"
    using euler_consistent_solution[OF step_ok] step_eq
    by (auto simp: euler_res_def algebra_simps intro!: scaleR_left_mono)
  also have "\<dots> = {x + y |x y. x \<in> {euler_res} \<and> y \<in> {(h * h / 2) *\<^sub>R inf_of_appr D .. (h * h / 2) *\<^sub>R sup_of_appr D}}"
    by (auto intro!: exI[where x="x - euler_res" for x] simp: algebra_simps power2_eq_square)
  also have "\<dots> \<subseteq> set_of_appr (msum_appr X1 (ivl_appr_of_appr ERR))"
    unfolding msum_appr_eq
  proof (rule msum_subsetI)
    have ode_x0: "[ode x0, x0] \<in> set_of_apprs [X0', X0]"
      by (metis bounded_ode ode_approx x0 set_of_apprs_set_of_appr)
    note scale_appr[where r=h and s = 1 and X = "X0'" and XS = "[X0]" and x = "ode x0"
      and xs = "[x0]" and optns = optns,
      THEN set_of_apprs_rotate, simplified append_Cons append_Nil,
      THEN set_of_apprs_Cons]
    from add_appr[OF this , of _ optns , THEN set_of_apprs_switch, THEN set_of_apprs_Cons,
      THEN set_of_apprs_switch, THEN set_of_apprs_Cons,
      simplified set_of_apprs_set_of_appr, OF ode_x0 bounded_scale_euler bounded_add_euler]
    show "{euler_res} \<subseteq> set_of_appr X1"
      using x0
      unfolding euler_res_def discrete_evolution_def euler_increment
      by (simp add: step_ivp_def)
  next
    from
      scale_appr[where r="h * h" and s = 2 and X = "ivl_appr_of_appr D" and XS="[]" and xs="[]"
        and x="inf_of_appr D" and optns=optns,
        THEN set_of_apprs_switch, THEN set_of_apprs_Cons, OF _ bounded_err]
      scale_appr[where r="h * h" and s = 2 and X = "ivl_appr_of_appr D" and XS="[]" and xs="[]"
        and x="sup_of_appr D" and optns=optns,
        THEN set_of_apprs_switch, THEN set_of_apprs_Cons, OF _ bounded_err]
    show "{(h * h / 2) *\<^sub>R inf_of_appr D..(h * h / 2) *\<^sub>R sup_of_appr D} \<subseteq> set_of_appr (ivl_appr_of_appr ERR)"
      by (simp_all add: set_of_apprs_set_of_appr ivl_appr_of_appr_def set_of_appr_of_ivl)
  qed
  finally show ?thesis unfolding RES .
qed

lemma unique_solution_step_ivp: "unique_solution (step_ivp t0 x0 t1 CX)" ..

lemma error_overapproximation_ivl:
  assumes h': "h' \<in> {0..h}"
  shows "solution (t0 + h') \<in> set_of_appr RES_ivl"
proof -
  def euler_res \<equiv> "discrete_evolution (euler_increment f) (t0 + h') t0 x0"
  have step_ok: "t0 + h' \<in> {t0 .. t1}" using step_eq pos_step assms by auto

  have "solution (t0 + h') \<in> {euler_res + (h'^2 / 2) *\<^sub>R inf_of_appr D .. euler_res + (h'^2 / 2) *\<^sub>R sup_of_appr D}"
    using euler_consistent_solution[OF step_ok] step_eq
    by (auto simp: euler_res_def algebra_simps intro!: scaleR_left_mono)
  also have "\<dots> = {x + y |x y. x \<in> {euler_res} \<and> y \<in> {(h' * h' / 2) *\<^sub>R inf_of_appr D .. (h' * h' / 2) *\<^sub>R sup_of_appr D}}"
    by (auto intro!: exI[where x="x - euler_res" for x] simp: algebra_simps power2_eq_square)
  also have "\<dots> \<subseteq> set_of_appr (msum_appr CX1 (appr_of_ivl (inf 0 (inf_of_appr ERR)) (sup 0 (sup_of_appr ERR))))"
    unfolding msum_appr_eq
  proof (rule msum_subsetI)
    have ode_x0: "[ode x0, x0] \<in> set_of_apprs [X0', X0]"
      by (metis bounded_ode ode_approx x0 set_of_apprs_set_of_appr)
    note scale_appr[where r=h and X = "X0'" and XS = "[X0]" and x = "ode x0" and xs = "[x0]" and optns = optns,
      THEN set_of_apprs_rotate, simplified append_Cons append_Nil,
      THEN set_of_apprs_Cons]
    note scale_appr_ivl[OF h', where X = "X0'" and XS = "[X0]" and x = "ode x0" and xs = "[x0]" and optns = optns,
      THEN set_of_apprs_rotate, simplified append_Cons append_Nil,
      THEN set_of_apprs_Cons]
    from add_appr[OF this , of _ optns , THEN set_of_apprs_switch, THEN set_of_apprs_Cons,
      THEN set_of_apprs_switch, THEN set_of_apprs_Cons,
      simplified set_of_apprs_set_of_appr, OF ode_x0 bounded_scale_ivl_euler bounded_add_euler_ivl]
    show "{euler_res} \<subseteq> set_of_appr CX1"
      using x0
      unfolding euler_res_def discrete_evolution_def euler_increment
      by (simp add: step_ivp_def)
  next
    have infsup[simp]: "inf 0 (inf_of_appr ERR) \<le> (sup 0 (sup_of_appr ERR))"
      by (metis inf_sup_ord(1) le_supI1)
    have "{(h' * h' / 2) *\<^sub>R inf_of_appr D .. (h' * h' / 2) *\<^sub>R sup_of_appr D} \<subseteq>
        {inf 0 ((h * h / 2) *\<^sub>R inf_of_appr D) .. sup 0 ((h * h / 2) *\<^sub>R sup_of_appr D)}"
      unfolding interval_cbox
    proof (rule subset_box_imp, safe)
      fix i::'a assume "i \<in> Basis"
      show "inf 0 ((h * h / 2) *\<^sub>R inf_of_appr D) \<bullet> i \<le> (h' * h' / 2) *\<^sub>R inf_of_appr D \<bullet> i"
        using assms
        unfolding inner_Basis_inf_left[OF `i \<in> Basis`] inner_zero_left inf_real_def inner_scaleR_left
        by (intro min_zero_mult_nonneg_le) (auto intro!: mult_mono)
      show "(h' * h' / 2) *\<^sub>R sup_of_appr D \<bullet> i \<le> sup 0 ((h * h / 2) *\<^sub>R sup_of_appr D) \<bullet> i"
        using assms
        unfolding inner_Basis_sup_left[OF `i \<in> Basis`] inner_zero_left sup_real_def inner_scaleR_left
        by (intro max_zero_mult_nonneg_le) (auto intro!: mult_mono)
    qed
    also
    from
      scale_appr[where r="h * h" and s = 2 and X = "ivl_appr_of_appr D" and XS="[]" and xs="[]"
        and x="inf_of_appr D" and optns=optns,
        THEN set_of_apprs_switch, THEN set_of_apprs_Cons, OF _ bounded_err]
      scale_appr[where r="h * h" and s = 2 and X = "ivl_appr_of_appr D" and XS="[]" and xs="[]"
        and x="sup_of_appr D" and optns=optns,
        THEN set_of_apprs_switch, THEN set_of_apprs_Cons, OF _ bounded_err]
    have "\<dots> \<subseteq> set_of_appr (appr_of_ivl (inf 0 (inf_of_appr ERR)) (sup 0 (sup_of_appr ERR)))"
      by (auto simp add: set_of_apprs_set_of_appr ivl_appr_of_appr_def set_of_appr_of_ivl
        intro!: le_infI2 le_supI2)
    finally show "{(h' * h' / 2) *\<^sub>R inf_of_appr D..(h' * h' / 2) *\<^sub>R sup_of_appr D} \<subseteq>
        set_of_appr ((appr_of_ivl (inf 0 (inf_of_appr ERR)) (sup 0 (sup_of_appr ERR))))"
      by (auto simp add: ivl_appr_of_appr_def set_of_appr_of_ivl)
  qed
  finally show ?thesis unfolding RES_ivl .
qed

lemma unique_on_open_global: "unique_on_open (global_ivp t0 x0)"
proof (unfold_locales, safe)
  let ?ivp = "(global_ivp t0 x0)"
  show "ivp_t0 ?ivp \<in> ivp_T ?ivp" "ivp_x0 ?ivp \<in> ivp_X ?ivp"
    by (simp_all add: global_ivp_def)
  show "open (ivp_T ?ivp)" "open (ivp_X ?ivp)"
    by (auto simp: global_ivp_def)
  show "continuous_on (ivp_T ?ivp \<times> ivp_X ?ivp) (ivp_f ?ivp)"
    by (auto simp: global_ivp_def intro!: continuous_intros fderiv' has_derivative_continuous_on)
  fix I t x
  assume "t \<in> (ivp_T ?ivp)" "x \<in> (ivp_X ?ivp)"
  --{* TODO: make local lipschitz based on open sets *}
  with open_contains_cball[of "(ivp_T ?ivp)"] `open (ivp_T ?ivp)`
    open_contains_cball[of "(ivp_X ?ivp)"] `open (ivp_X ?ivp)`
  obtain u v where uv: "cball t u \<subseteq> (ivp_T ?ivp)" "cball x v \<subseteq> (ivp_X ?ivp)" "u > 0" "v > 0"
    by blast
  def w \<equiv> "min u v"
  have "cball t w \<subseteq> (ivp_T ?ivp)" "cball x w \<subseteq> (ivp_X ?ivp)" "w > 0" using uv by (auto simp: w_def)
  have "cball t w = {t - w .. t + w}" by (auto simp: dist_real_def)
  from cube_in_cball'[OF `w > 0`] obtain w' where w':
    "w'>0" "w' \<le> w" "\<And>y. y\<in>{x - setsum (op *\<^sub>R w') Basis..x + setsum (op *\<^sub>R w') Basis} \<Longrightarrow> y \<in> cball x w"
    by metis
  interpret ccd:compact_continuously_diff
      "{t - w' .. t + w'}" "{x - setsum (op *\<^sub>R w') Basis..x + setsum (op *\<^sub>R w') Basis}"
      "\<lambda>(t, x). ode x" "\<lambda>(t, x) (dt, dx). ode_d x dx"
    using `w > 0`
    using fderiv' cont_fderiv w'
    by unfold_locales
      (auto intro!: convex_closed_interval compact_interval split_beta'
        continuous_intros add_nonneg_nonneg
        intro: continuous_on_subset
        simp: algebra_simps eucl_le[where 'a='a])
  let ?u = w' and ?L = ccd.onorm_bound
  have subset: "cball x w' \<subseteq> {x - setsum (op *\<^sub>R w') Basis..x + setsum (op *\<^sub>R w') Basis}"
    unfolding scaleR_setsum_right[symmetric]
    by (rule cball_in_cube)
  have "\<forall>t'\<in>cball t ?u \<inter> I. lipschitz (cball x ?u \<inter> ivp_X (global_ivp t0 x0))
    (\<lambda>y. ivp_f (global_ivp t0 x0) (t', y)) ?L"
    using ccd.lipschitz(1) w'
    by (force intro!: lipschitz_subset[OF _ subset])
  thus "\<exists>u>0. \<exists>L\<ge>0. \<forall>t'\<in>cball t u \<inter> I. lipschitz (cball x u \<inter> (ivp_X ?ivp))
    (\<lambda>y. (ivp_f ?ivp) (t', y)) L"
    using `?u > 0` ccd.lipschitz by blast
qed

lemma unique_on_intermediate_euler_step:
  shows
    "unique_solution (euler_ivp t0 x0 t1)" and
    "\<And>t. t \<in> {t0 .. t1} \<Longrightarrow> ivp.solution (euler_ivp t0 x0 t1) t \<in> set_of_appr RES_ivl" and
    "ivp.solution (euler_ivp t0 x0 t1) t1 \<in> set_of_appr RES"
proof -
  from unique_solution_step_ivp
  interpret step: unique_solution "(step_ivp t0 x0 t1 CX)" .
  from iv_defined have "t0 \<le> t1" by (auto simp: step_ivp_def)
  interpret euler: ivp "(euler_ivp t0 x0 t1)"
    using `t0 \<le> t1`
    by unfold_locales auto
  have euler_ivp_step_ivp: "euler_ivp t0 x0 t1 = step_ivp t0 x0 t1 CX\<lparr>ivp_X := UNIV\<rparr>"
    by (simp add: step_ivp_def)
  have step_solves_euler: "euler.is_solution solution"
    unfolding euler_ivp_step_ivp
    by (auto intro!: is_solution_on_superset_domain)
  interpret euler: has_solution "(euler_ivp t0 x0 t1)"
    by unfold_locales (rule exI step_solves_euler)+
  from unique_on_open_global
  interpret uo: unique_on_open "global_ivp t0 x0" .
  from uo.global_solution guess J . note J=this
  def max_ivp \<equiv> "
    \<lparr>ivp_f = (\<lambda>(t, x). ode x),
    ivp_t0 = t0, ivp_x0 = x0,
    ivp_T = J,
    ivp_X = UNIV\<rparr>"
  from J(4) interpret max_ivp: unique_solution max_ivp
    by (auto simp: global_ivp_def max_ivp_def)
  {
    fix t1 x
    assume "ivp.is_solution (euler_ivp t0 x0 t1) x"
    hence "\<And>t. t\<in>{t0 .. t1} \<Longrightarrow> x t = ivp.solution max_ivp t"
      using J(5)[where K2="{t0 .. t1}"]
      by (auto simp: euler_ivp_def global_ivp_def max_ivp_def is_interval_closed_interval)
  } note solution_eqI = this
  interpret euler: unique_solution "(euler_ivp t0 x0 t1)"
  proof
    fix y t
    assume y: "euler.is_solution y" and "t \<in> euler.T"
    hence "t \<in> {t0 .. t1}" by (simp add: euler_ivp_def)
    thus "y t = ivp.solution (euler_ivp t0 x0 t1) t"
      by (simp add: solution_eqI[OF y] solution_eqI[OF euler.is_solution_solution])
  qed
  show "unique_solution (euler_ivp t0 x0 t1)" proof qed
  have step_eq_euler: "\<And>t. t \<in> {t0 .. t1} \<Longrightarrow> solution t = euler.solution t"
    by (auto intro!: euler.unique_solution step_solves_euler)
  {
    fix t assume "t \<in> {t0 .. t1}"
    thus "euler.solution t \<in> set_of_appr RES_ivl"
      using error_overapproximation_ivl[of "t - t0"] `t0 \<le> t1` step_eq step_eq_euler
      by auto
  }
  show "euler.solution t1 \<in> set_of_appr RES"
    using error_overapproximation `t0 \<le> t1` step_eq step_eq_euler
    by (auto simp add:  step_ivp_def)
qed

end

lemma unique_on_euler_step:
  assumes "t0 + h = t1"
  shows
    "unique_solution (euler_ivp t0 x0 t1)" (is ?th1) and
    "\<And>t. t \<in> {t0 .. t1} \<Longrightarrow> ivp.solution (euler_ivp t0 x0 t1) t \<in> set_of_appr RES_ivl" (is "\<And>t. ?ass2 t \<Longrightarrow> ?th2 t") and
    "ivp.solution (euler_ivp t0 x0 t1) t1 \<in> set_of_appr RES" (is ?th3)
proof -
  from euler_step_returns
  obtain X0' CX F D ERR S S' X1' X1'' where intermediate_results:
    "cert_stepsize optns X0 (stepsize optns) (iterations optns) (halve_stepsizes optns) = Some (h, CX)"
    "ode_approx optns [X0] = Some X0'"
    "ode_approx optns [CX] = Some F"
    "ode_d_approx optns [CX, F] = Some D"
    "scale_appr optns (h * h) 2 (ivl_appr_of_appr D) [] = Some ERR"
    "scale_appr optns h 1 X0' [X0] = Some S"
    "scale_appr_ivl optns 0 h X0' [X0] = Some S'"
    "add_appr optns X0 S [] = Some X1'"
    "add_appr optns X0 S' [] = Some X1''"
    "RES_ivl = extend_appr X1'' (inf 0 (inf_of_appr ERR)) (sup 0 (sup_of_appr ERR))"
    "RES = msum_appr X1' (ivl_appr_of_appr ERR)"
    using pos_prestep euler_step_returns
    by (auto simp: euler_step_def split: split_option_bind_asm)
  from cert_stepsize_pos[OF intermediate_results(1) pos_prestep] have "0 < h" .
  from unique_on_intermediate_euler_step[OF `0 < h` assms intermediate_results(1-11)]
  show ?th1 "\<And>t. ?ass2 t \<Longrightarrow> ?th2 t" ?th3 by -
qed

end

fun set_res_of_appr_res
  where "set_res_of_appr_res (t0', CX, t1', X) = (t0', set_of_appr CX, t1', set_of_appr X)"

definition
  "enclosure f t0 t1 xs = list_all (\<lambda>(t0', CX, t1', X).
    f t1' \<in> X \<and> (\<forall>t \<in> {t0'::real .. t1'}. f t \<in> CX) \<and>
      t0 \<le> t0' \<and> t0' \<le> t1' \<and> t1' \<le> t1) xs"

lemma enclosure_ConsI:
  assumes "enclosure f t0 t1 ress0"
  assumes "f (fst (snd (snd r))) \<in> snd (snd (snd r))"
  assumes "\<And>t. t \<in> {fst r .. fst (snd (snd r))} \<Longrightarrow> f t \<in> fst (snd r)"
  assumes "t0 \<le> fst r" "fst r \<le> fst (snd (snd r))" "fst (snd (snd r)) \<le> t1"
  shows "enclosure f t0 t1 (r # ress0)"
  using assms by (auto simp: enclosure_def)

lemma enclosure_Nil_iff[simp]: "enclosure f t0 t1 [] \<longleftrightarrow> True" by (auto simp: enclosure_def)

lemma enclosure_Cons_iff:
  shows "enclosure f t0 t1 ((t0', CX, t1', X1) # ress0) \<longleftrightarrow>
    (f t1' \<in> X1 \<and> (\<forall>t\<in>{t0' .. t1'}. f t \<in> CX) \<and>
      t0 \<le> t0' \<and> t0' \<le> t1' \<and> t1' \<le> t1 \<and> enclosure f t0 t1 ress0)"
  using assms by (auto simp: enclosure_def)

lemma enclosure_subst:
  assumes "enclosure f t0 t1 ress"
  assumes "\<And>t. t \<in> {t0 .. t1} \<Longrightarrow> f t = g t"
  shows "enclosure g t0 t1 ress"
  using assms
  by (induct ress) (auto simp: enclosure_Cons_iff)

lemma enclosure_mono:
  assumes "t1 \<le> t2"
  assumes "enclosure f t0 t1 ress"
  shows "enclosure f t0 t2 ress"
  using assms
  by (induct ress) (auto simp: enclosure_Cons_iff)

text {* execution of @{term advance_euler} *}

lemma advance_euler_enclosure:
  assumes pos_prestep: "0 < stepsize optns"
  assumes encl: "enclosure (ivp.solution (euler_ivp t0 x0 t1)) t0 t1 (map set_res_of_appr_res xs)"
  assumes u1: "unique_solution (euler_ivp t0 x0 t1)"
  assumes sol: "ivp.solution (euler_ivp t0 x0 t1) t1 \<in> set_of_appr X1"
  assumes adv: "advance_euler optns (Some (i, t1, X1, xs)) = Some (j, t2, X2, ys)"
  shows "enclosure (ivp.solution (euler_ivp t0 x0 t2)) t0 t2 (map set_res_of_appr_res ys)" (is ?encl)
    and "unique_solution (euler_ivp t0 x0 t2)" (is ?unique)
    and "ivp.solution (euler_ivp t0 x0 t2) t2 \<in> set_of_appr X2" (is ?sol)
proof -
  from adv obtain CX where step: "euler_step optns X1 = Some (t2 - t1, CX, X2)"
    and ys: "ys = (t1, CX, t2, X2)#xs"
    by (auto simp: split: option.split_asm)
  from u1 interpret u1: unique_solution "euler_ivp t0 x0 t1"
    by simp
  have "t0 \<le> t1" using u1.iv_defined by simp
  have "t1 + (t2 - t1) = t2" by simp
  note sol_step = unique_on_euler_step[OF sol pos_prestep step this]
  from sol_step(1)
  interpret u2: unique_solution "euler_ivp t1 (ivp.solution (euler_ivp t0 x0 t1) t1) t2" by simp
  have "t1 \<le> t2" using u2.iv_defined by simp
  from `t0 \<le> t1` `t1 \<le> t2`
  interpret connected_unique_solutions
    "euler_ivp t0 x0 t2"
    "euler_ivp t0 x0 t1"
    "euler_ivp t1 (ivp.solution (euler_ivp t0 x0 t1) t1) t2"
     t1 t2
    by unfold_locales auto
  have "enclosure (ivp.solution (euler_ivp t0 x0 t2)) t0 t2 (map set_res_of_appr_res xs)"
    by (auto intro!: enclosure_mono[OF `t1 \<le> t2`] enclosure_subst[OF encl]
      simp: solution1_eq_solution)
  thus ?encl ?sol
    using sol_step `t0 \<le> t1` `t1 \<le> t2` encl
    by (auto simp: ys enclosure_Cons_iff solution2_eq_solution)
  show ?unique by unfold_locales
qed

lemma euler_series_enclosure:
  assumes pos_prestep: "0 < stepsize optns"
  assumes x0: "x0 \<in> set_of_appr X0"
  assumes euler_series_returns: "euler_series optns t0 X0 i = Some (j, t2, X2, ress)"
  shows
    "unique_solution (euler_ivp t0 x0 t2)"
    "enclosure (ivp.solution (euler_ivp t0 x0 t2)) t0 t2 (map set_res_of_appr_res ress)"
    "ivp.solution (euler_ivp t0 x0 t2) t2 \<in> set_of_appr X2"
  unfolding atomize_conj
  using x0 euler_series_returns
proof (induct i arbitrary: t0 ress t2 X2 j)
  case 0
  let ?triv = "euler_ivp t2 x0 t2"
  interpret triv: ivp ?triv
    by standard auto
  have triv: "unique_solution ?triv"
    by (rule triv.singleton_unique_solutionI) auto
  then interpret triv: unique_solution ?triv .
  have "triv.solution t2 = x0"
    using triv.solution_t0 by auto
  with 0 show ?case
    by (auto intro!: triv enclosure_ConsI)
next
  case (Suc i)
  then obtain t1 X1 r1 j' where ser: "euler_series optns t0 X0 i = Some (j', t1, X1, r1)"
    by (cases "euler_series optns t0 X0 i") auto
  with Suc have adv: "advance_euler optns (Some (j', t1, X1, r1)) = Some (j, t2, X2, ress)"
    by simp
  from Suc.hyps[OF Suc.prems(1) ser]
  have IH: "enclosure (ivp.solution (euler_ivp t0 x0 t1)) t0 t1 (map set_res_of_appr_res r1)"
      "unique_solution (euler_ivp t0 x0 t1)"
      "ivp.solution (euler_ivp t0 x0 t1) t1 \<in> set_of_appr X1"
    by simp_all
  from advance_euler_enclosure[OF pos_prestep IH adv]
  show ?case by auto
qed

end

sublocale aform_approximate_ivp0 \<subseteq>
  approximate_sets
    aform_of_ivl msum_aform' Affine Joints
    Inf_aform Sup_aform
    "uncurry_options add_aform_componentwise::('a, 'a::executable_euclidean_space aform, (real \<times> ((real \<times> 'a \<times> 'a \<times> real \<times> 'a \<times> 'a) list))) options \<Rightarrow> _"
    "uncurry_options scaleQ_aform_componentwise"
    "uncurry_options scaleR_aform_ivl"
    "\<lambda>optns. split_aform_largest (precision optns) (presplit_summary_tolerance optns)"
    disjoint_aforms
    inter_aform_plane
proof
  fix x y::'a and X Y and xs ys::"'a list" and XS YS and r s S
    and optns::"('a, 'a aform, (real \<times> ((real \<times> 'a \<times> 'a \<times> real \<times> 'a \<times> 'a) list))) options"
  show "([x] \<in> Joints [X]) = (x \<in> Affine X)"
    by (auto simp: Affine_def valuate_def Joints_def)
  show "Affine X \<noteq> {}" by (rule Affine_notempty)
  show "compact (Affine X)" by (rule compact_Affine)
  {
    assume "x # y # xs \<in> Joints (X # Y # XS)"
    thus "y # x # xs \<in> Joints (Y # X # XS)" "y # xs @ [x] \<in> Joints (Y # XS @ [X])"
      by (auto simp: Joints_def valuate_def)
  }
  {
    assume "xs \<in> Joints []"
    thus "xs = []" by (auto simp: Joints_def valuate_def)
  }
  {
    assume "xs \<in> Joints (X # XS)"
    thus "\<exists>y ys. xs = y # ys \<and> y \<in> Affine X \<and> ys \<in> Joints XS"
      by (auto simp: Joints_def Affine_def valuate_def)
  }
  {
    assume "[x, y] \<in> Joints [X, Y]"
    thus "(x, y) \<in> Pair_of_list ` Joints [X, Y]"
      by (auto simp: Joints_def valuate_def intro!: image_eqI[where x="[aform_val e X, aform_val e Y]" for e])
  }
  {
    assume "uncurry_options add_aform_componentwise optns X Y YS = Some S" "x # y # ys \<in> Joints (X # Y # YS)"
    from add_aform_componentwise[OF this]
    show "(x + y) # x # y # ys \<in> Joints (S # X # Y # YS)" .
  }
  {
    assume "uncurry_options scaleQ_aform_componentwise optns r s X XS = Some S" "x # xs \<in> Joints (X # XS)"
    from scaleQ_aform_componentwise[OF this]
    show "(r/s) *\<^sub>R x # x # xs \<in> Joints (S # X # XS)" by simp
  }
  {
    fix s t::real
    assume "uncurry_options scaleR_aform_ivl optns r t X XS = Some S" "x # xs \<in> Joints (X # XS)"
      "s \<in> {r .. t}"
    from scaleR_aform_ivl[OF this]
    show "s *\<^sub>R x # x # xs \<in> Joints (S # X # XS)" .
  }
  {
    assume "x \<in> Affine X"
    then obtain e where e: "e \<in> UNIV \<rightarrow> {-1 .. 1}" "x = aform_val e X"
      by (auto simp: Affine_def valuate_def)
    let ?sum = "summarize_threshold (precision optns) (presplit_summary_tolerance optns) (degree_aform X) (snd X)"
    obtain e' where e': "e' \<in> funcset UNIV {-1 .. 1}"
      "aform_val e' (fst X, ?sum) = aform_val e X"
      by (rule summarize_pdevsE[OF e(1) order_refl, of "snd X" "precision optns"
          "(\<lambda>i y. presplit_summary_tolerance optns * infnorm (eucl_truncate_up (precision optns) (Radius' (precision optns) X)) \<le> infnorm y)"])
        (auto simp: summarize_threshold_def aform_val_def)
    from e e' have x: "x = aform_val e' (fst X, ?sum)"
      by simp
    show "list_ex (\<lambda>X. x \<in> Affine X) (split_aform_largest (precision optns) (presplit_summary_tolerance optns) X)"
    proof (rule split_aformE[OF e'(1) x, where i="fst (max_pdev ?sum)"])
      fix err::real
      assume "err \<in> {-1 .. 1}" "x = aform_val (e'(fst (max_pdev ?sum) := err))
          (fst (split_aform (fst X, ?sum) (fst (max_pdev ?sum))))"
      thus "list_ex (\<lambda>X. x \<in> Affine X) (split_aform_largest (precision optns) (presplit_summary_tolerance optns) X)"
        using e'(1)
        by (force simp: split_aform_largest_def split_aform_largest_uncond_def Affine_def valuate_def
          intro!: image_eqI[where x="e' (a := err)" for a] split: prod.split)
    next
      fix err::real
      assume "err \<in> {-1 .. 1}" "x = aform_val (e'(fst (max_pdev ?sum) := err))
          (snd (split_aform (fst X, ?sum) (fst (max_pdev ?sum))))"
      thus "list_ex (\<lambda>X. x \<in> Affine X) (split_aform_largest (precision optns) (presplit_summary_tolerance optns) X)"
        using e'(1)
        by (force simp: split_aform_largest_def split_aform_largest_uncond_def Affine_def valuate_def
          intro: image_eqI[where x="e' (a := err)" for a err]
          split: prod.split)
    qed
  }
  show "disjoint_aforms X Y \<Longrightarrow> Affine X \<inter> Affine Y = {}"
    by (rule disjoint_aforms)
  show "Affine (msum_aform' X Y) = {x + y |x y. x \<in> Affine X \<and> y \<in> Affine Y}"
    by (rule Affine_msum_aform) simp
  show "Inf_aform (msum_aform' X Y) = Inf_aform X + Inf_aform Y"
    "Sup_aform (msum_aform' X Y) = Sup_aform X + Sup_aform Y"
    by (auto simp: Inf_aform_msum_aform Sup_aform_msum_aform)
  show "Inf_aform X \<le> Inf (Affine X)" "Sup (Affine X) \<le> Sup_aform X"
    by (auto simp: Affine_def valuate_def Inf_aform Sup_aform intro!: cINF_greatest cSUP_least)
  {
    fix l u::'a assume le: "l \<le> u"
    show "Sup_aform (aform_of_ivl l u) = u"
     "Inf_aform (aform_of_ivl l u) = l"
     "Affine (aform_of_ivl l u) = {l..u}"
     using Inf_aform_aform_of_ivl[OF le] Sup_aform_aform_of_ivl[OF le]
       Affine_aform_of_ivl[OF le]
     by auto
  }
  show "convex (Affine X)"
    by (rule convex_Affine)
  show "xs \<in> Joints XS \<Longrightarrow> length xs = length XS" by (auto simp: Joints_def valuate_def)
qed

locale aform_approximate_ivp = aform_approximate_ivp0 +
  approximate_ivp
    aform_of_ivl msum_aform' Affine Joints
    Inf_aform Sup_aform
    "uncurry_options add_aform_componentwise::('a, 'a::executable_euclidean_space aform, (real \<times> ((real \<times> 'a \<times> 'a \<times> real \<times> 'a \<times> 'a) list))) options \<Rightarrow> _"
    "uncurry_options scaleQ_aform_componentwise"
    "uncurry_options scaleR_aform_ivl"
    "\<lambda>optns. split_aform_largest (precision optns) (presplit_summary_tolerance optns)"
    disjoint_aforms
    inter_aform_plane
begin

text {* TODO: prove these lemmas generically *}

lemma ivls_of_aforms:
  assumes "enclosure f t0 t1 (map set_res_of_appr_res xs)"
  shows "enclosure f t0 t1 (map set_res_of_ivl_res (ivls_of_aforms p xs))"
  using assms
proof (induct xs)
  case (Cons x xs)
  thus ?case
    by (cases x) (auto simp: ivls_of_aforms_def o_def enclosure_Cons_iff
      intro: inf_of_appr eucl_truncate_down_le sup_of_appr eucl_truncate_up_le)
qed (simp add: ivls_of_aforms_def)

lemma summarize_ivls:
  fixes f::"real \<Rightarrow> 'a"
  assumes "enclosure f t0 t1 (map set_res_of_ivl_res xs)"
  shows "enclosure f t0 t1 (case summarize_ivls xs of Some x \<Rightarrow> [set_res_of_ivl_res x] | None \<Rightarrow> [])"
  using assms
proof (induct xs)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  have inf_cases: "\<And>t t0 t1 t2 a b.
    \<forall>t\<in>{t1..t2}. a \<le> f t \<Longrightarrow>
    \<forall>t\<in>{t0..t1}. b \<le> f t \<Longrightarrow>
    t0 \<le> t \<Longrightarrow> t \<le> t2 \<Longrightarrow>
    inf a b \<le> f t"
    by (metis atLeastAtMost_iff le_cases le_infI1 le_infI2)
  have sup_cases: "\<And>t t0 t1 t2 a b.
       \<forall>t\<in>{t1..t2}. f t \<le> a \<Longrightarrow>
       \<forall>t\<in>{t0..t1}. f t \<le> b \<Longrightarrow>
       t0 \<le> t \<Longrightarrow> t \<le> t2 \<Longrightarrow>
       f t \<le> sup a b"
    by (metis atLeastAtMost_iff le_cases le_supI1 le_supI2)
  show ?case
    using Cons
    by (cases x) (fastforce simp: min_def max_def enclosure_Cons_iff
      split: split_if_asm option.split
      intro: inf_cases sup_cases inf.coboundedI1 inf.coboundedI2 le_infI2 le_supI1 le_supI2
        sup.coboundedI1 sup.coboundedI2)
qed

lemma enclosure_takeD:
  assumes "enclosure f t0 t1 (map set_res_of_ivl_res xs)"
  shows "enclosure f t0 t1 (map set_res_of_ivl_res (take m xs))"
using assms
proof (induct xs arbitrary: m)
  case (Cons x xs)
  thus ?case
    by (cases m) (auto simp: enclosure_def)
qed simp

lemma enclosure_dropD:
  assumes "enclosure f t0 t1 (map set_res_of_ivl_res xs)"
  shows "enclosure f t0 t1 (map set_res_of_ivl_res (drop m xs))"
using assms
proof (induct xs arbitrary: m)
  case (Cons x xs)
  thus ?case
    by (cases m) (auto simp: enclosure_def)
qed simp

lemma summarize_option_map_filter_aux: "(case f xs of None \<Rightarrow> [] | Some x \<Rightarrow> [set_res_of_ivl_res x]) =
     (map set_res_of_ivl_res (map the (filter (- Option.is_none) (map f [xs]))))"
   by (auto split: option.split simp: Option.is_none_def)

lemma enclosure_Cons_splitI:
  "enclosure f t0 t1 (map set_res_of_ivl_res (map the (filter (- Option.is_none) ([X])))) \<Longrightarrow>
  enclosure f t0 t1 (map set_res_of_ivl_res (map the (filter (- Option.is_none) ((Xs))))) \<Longrightarrow>
  enclosure f t0 t1 (map set_res_of_ivl_res (map the (filter (- Option.is_none) ((X # Xs)))))"
  by (case_tac "set_res_of_ivl_res (the X)") (auto simp: enclosure_Cons_iff)

lemma summarize_enclosure_aux:
  fixes f::"real \<Rightarrow> 'a"
  assumes "enclosure f t0 t1 (map set_res_of_ivl_res xs)"
  shows "enclosure f t0 t1 (map set_res_of_ivl_res (map the (filter (-Option.is_none) (map summarize_ivls (parts m xs)))))"
  using assms
proof (induct m xs rule: parts.induct)
  case 1 thus ?case by simp
next
  case (2 x xs)
  from summarize_ivls[OF 2]
  show ?case unfolding parts.simps summarize_option_map_filter_aux .
next
  case (3 m x xs)
  have "enclosure f t0 t1 (map set_res_of_ivl_res (map the (filter (- Option.is_none) [summarize_ivls (take (Suc m) (x # xs))])))"
    using summarize_ivls summarize_option_map_filter_aux[symmetric,
        of summarize_ivls "(take (Suc m) (x # xs))", simplified list.map]
    by (metis "3.prems" enclosure_takeD)
  moreover
  from 3 have "enclosure f t0 t1
     (map set_res_of_ivl_res (map the (filter (- Option.is_none) (map summarize_ivls (parts (Suc m) (drop (Suc m) (x # xs)))))))"
     by (metis enclosure_dropD)
  ultimately
  show ?case
    unfolding parts.simps list.map
    by (rule enclosure_Cons_splitI)
qed

lemma
  summarize_enclosure:
  "enclosure f t0 t1 (map set_res_of_appr_res xs) \<Longrightarrow>
    enclosure f t0 t1 (map set_res_of_ivl_res (summarize_enclosure p m xs))"
  unfolding summarize_enclosure_def
  by (intro summarize_enclosure_aux ivls_of_aforms)

lemma euler_series_ivls_result:
  assumes pos_prestep: "0 < stepsize optns"
  assumes x0: "x0 \<in> Affine X0"
  assumes ivls_result: "result_fun optns = ivls_result p m"
  assumes euler_series_returns: "euler_series_result optns t0 X0 i = Some (t1, xs)"
  shows "unique_solution (euler_ivp t0 x0 t1)" (is ?th1)
  and "enclosure (ivp.solution (euler_ivp t0 x0 t1)) t0 t1 (map set_res_of_ivl_res xs)" (is ?th2)
proof -
  from euler_series_returns obtain j X1 ress
    where ress: "euler_series optns t0 X0 i = Some (j, t1, X1, ress)"
    and xs: "xs = summarize_enclosure p m ress"
    by (auto simp: ivls_result ivls_result_def)
  from euler_series_enclosure[OF assms(1-2) ress]
  show ?th1 ?th2
    by (auto intro!: summarize_enclosure simp: xs)
qed

end

end

