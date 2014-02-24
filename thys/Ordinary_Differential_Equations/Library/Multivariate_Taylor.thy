theory Multivariate_Taylor
imports
  Higher_Derivative
begin

subsection {* Multivariate Taylor Series Expansion *}

text {* TODO: move to PiE *}
lemma setsum_insert_PiE[symmetric]:
  assumes "a \<notin> A"
  shows "setsum (\<lambda>x. f (restrict x A) A (x a)) ((insert a A) \<rightarrow>\<^sub>E Basis) =
    setsum (\<lambda>x. setsum (f x A) Basis) (A \<rightarrow>\<^sub>E Basis)"
proof -
  let ?f = "(\<lambda>(x, i). (restrict x A) (a:=i))"
  let ?p = "((A \<rightarrow>\<^sub>E Basis) \<times> Basis)"
  show ?thesis
  proof (subst setsum_cartesian_product, rule setsum_reindex_cong)
    show "insert a A \<rightarrow>\<^sub>E Basis = ?f ` ?p"
    proof safe
      fix x::"'a\<Rightarrow>'d" assume "x \<in> insert a A \<rightarrow>\<^sub>E Basis"
      thus "x \<in> ?f ` ?p"
        by (intro image_eqI[where x="(restrict x A, x a)"])
          (auto simp: restrict_def extensional_def PiE_iff)
    qed (auto simp: PiE_iff extensional_def split: split_if_asm)
  next
    show "inj_on ?f ?p" by (rule inj_onI, clarsimp)
      (metis Int_iff PiE_def assms extensional_restrict restrict_fupd fun_upd_same)
  qed (auto simp: assms)
qed

lemma (in approachable_on) diff_chain_componentwise:
  fixes f::"'a::euclidean_space\<Rightarrow>'b::euclidean_space"
  assumes f_deriv: "FDERIV f (g t) : G :> Df"
  assumes g_deriv: "FDERIV g t : J :> Dg"
  assumes "g ` J \<subseteq> G"
  assumes "t \<in> J"
  defines "\<phi> \<equiv> (\<lambda>t. f (g t))"
  shows "FDERIV \<phi> t : J :> (\<lambda>x. (\<Sum>i\<in>Basis. (Dg x \<bullet> i) *\<^sub>R (Df i)))"
proof -
  have "g t \<in> G" using assms by auto
  from f_deriv have f_diff: "f differentiable (g t) in G"
    by (rule differentiableI)
  have frechet_Df: "frechet_derivative f (at (g t) within G) = Df"
    using f_deriv f_diff approachable `t \<in> J` `g t \<in> G`
    by (auto intro!: frechet_derivative_unique_within
      simp: frechet_derivative_works approachable_at_def)
  have f_jacobian:
    "FDERIV f (g t) : G :> (\<lambda>h. \<Sum>i\<in>Basis. (\<Sum>b\<in>Basis. (Df b \<bullet> i) *\<^sub>R (h \<bullet> b)) *\<^sub>R i)"
    using Derivative.jacobian_works[of _ f] f_diff by (simp add: frechet_Df)
  have "Df = (\<lambda>h. \<Sum>i\<in>Basis. (\<Sum>b\<in>Basis. (Df b \<bullet> i) *\<^sub>R (h \<bullet> b)) *\<^sub>R i)"
    using f_deriv f_jacobian
    by (auto intro: frechet_derivative_unique_within_approach[OF approachable, OF `g t \<in> G`])
  also have "\<dots> = (\<lambda>h. (\<Sum>i\<in>Basis. ((\<Sum>b\<in>Basis. (h \<bullet> b) *\<^sub>R (Df b)) \<bullet> i) *\<^sub>R i))"
    by (simp add: field_simps inner_setsum_left)
  also have "\<dots> = (\<lambda>h. (\<Sum>b\<in>Basis. (h \<bullet> b) *\<^sub>R (Df b)))"
    by (simp add: euclidean_representation)
  finally have Df: "Df = (\<lambda>h. \<Sum>b\<in>Basis. (h \<bullet> b) *\<^sub>R Df b)" .
  have "\<phi> = f o g" by (auto simp add: \<phi>_def)
  hence "FDERIV \<phi> t : J :> (Df \<circ> Dg)"
    using `t \<in> J` `g \` J \<subseteq> G`
    by (auto intro: has_derivative_at_within
        intro!: diff_chain_within has_derivative_within_subset[OF f_deriv]
        g_deriv[simplified has_vector_derivative_def])
  hence "FDERIV \<phi> t : J :> (\<lambda>x. (\<Sum>b\<in>Basis. (Dg x \<bullet> b) *\<^sub>R (Df b)))"
    using `t \<in> J` by (subst (asm) Df) (auto simp: o_def)
  thus ?thesis by (simp add: ac_simps)
qed

lemma setsum_nonneg_eq_0_iff [simp]:
  "finite F ==> (\<And>a. a \<in> F \<Longrightarrow> f a \<ge> 0) \<Longrightarrow> (setsum f F = 0) = (ALL a:F. f a = (0::real))"
  by (induct set: finite) (auto simp: add_nonneg_eq_0_iff setsum_nonneg)

definition "listsN n A = {xs \<in> lists A. length xs = n}"

lemma listsN_0[simp]: "listsN 0 A = {[]}"
  by (auto simp: listsN_def)

lemma listsN_Suc[simp]: "listsN (Suc n) A = (\<lambda>(xs, x). Cons x xs) ` (listsN n A \<times> A)"
  unfolding listsN_def
  apply safe
  apply (case_tac x)
  apply (auto simp: listsN_def)
  done

lemma listsN_length[intro, simp]: "x \<in> listsN n Basis \<Longrightarrow> length x = n"
  by (auto simp: listsN_def)

context higher_derivative_lrect
begin

lemma
  multivariate_taylor:
  fixes X H
  defines "line \<equiv> (\<lambda>t. X + t *\<^sub>R H)"
  defines "sumH \<equiv> (\<Sum>k\<in>Basis. (H \<bullet> k))"
  defines "sumDs \<equiv> (\<lambda>k x. \<Sum>d\<in>Basis. (\<Sum>ds\<in>listsN k Basis.
    (fold (\<lambda>d p. (H \<bullet> d) * p) (d#ds) 1) *\<^sub>R Ds ds x d))"
  defines "diff \<equiv> \<lambda>k. case k of 0 \<Rightarrow> f | Suc k \<Rightarrow> sumDs k"
  assumes H_nonneg: "\<And>i. i \<in> Basis \<Longrightarrow> H \<bullet> i \<ge> 0"
  assumes "H \<noteq> 0"
  assumes line_in_G: "line ` {0..1} \<subseteq> G"
  shows "\<exists>tt\<in>Basis\<rightarrow>{0<..<1}.
    f (X + H) = (\<Sum>m = 0..<Suc n. (diff m X /\<^sub>R real (fact m))) +
      (\<Sum>x\<in>Basis. ((diff (Suc n) (line (tt x)) /\<^sub>R real (fact (Suc n))) \<bullet> x) *\<^sub>R x)"
proof -
  from H_nonneg have "sumH \<ge> 0" by (auto simp: sumH_def intro!: setsum_nonneg)
  moreover from `H \<noteq> 0` H_nonneg have "sumH \<noteq> 0"
    by (subst (asm) euclidean_all_zero_iff[symmetric]) (auto simp: sumH_def)
  ultimately have "sumH > 0" by simp
  have line_fderiv[FDERIV_intros]: "\<And>t. FDERIV line t : {0..1} :> (\<lambda>t. t *\<^sub>R H)"
    unfolding line_def by (subst add_commute)
      (intro has_derivative_add_const scaleR_left_has_derivative has_derivative_id)
  hence line_deriv: "\<And>t. (line has_vector_derivative H) (at t within {0..1})"
    by (auto simp: has_vector_derivative_def has_derivative_at_within)
  hence line_diff: "\<And>t. line differentiable at t within {0..1}"
    unfolding has_vector_derivative_def
    by (rule differentiableI)
  {
    fix d::'a and k::nat and t::real
    assume "t \<in> {0..1}" "k < n" hence "line t \<in> G" using line_in_G by auto
    have FDERIV_Ds_line: "\<And>ds d. length ds < n \<Longrightarrow> d \<in> Basis \<Longrightarrow>
        FDERIV (\<lambda>x. Ds ds (line x) d) t : {0..1} :>
        (\<lambda>x. \<Sum>i\<in>Basis. (x *\<^sub>R H \<bullet> i) *\<^sub>R Ds (i#ds) (line t) d)"
      using line_in_G `t \<in> {0..1}` `line t \<in> G`
      by (intro diff_chain_componentwise)
        (auto intro!: FDERIV_eq_intros simp: symmetric_higher_derivative)
    have "((\<lambda>t. sumDs k (line t)) has_vector_derivative
        (\<Sum>d\<in>Basis. \<Sum>ds\<in>listsN k Basis. \<Sum>i\<in>Basis.
          ((H \<bullet> i) *\<^sub>R (fold (\<lambda>d p. (H \<bullet> d) * p) (d#ds) 1) *\<^sub>R Ds (i # ds) (line t) d)))
        (at t within {0..1})"
        (is "(_ has_vector_derivative ?sumsum) _")
      unfolding has_vector_derivative_def sumDs_def
      using zero_less_Suc[of n] `k < n`
      by (auto intro!: FDERIV_eq_intros FDERIV_Ds_line
        simp: field_simps inverse_eq_divide scaleR_setsum_right)
    also
    have "?sumsum = sumDs (Suc k) (line t)"
      unfolding sumDs_def
      apply (subst setsum_cartesian_product)
      apply simp
      apply (subst setsum_reindex)
      apply (metis inj_split_Cons)
      apply (simp add: field_simps scaleR_setsum_right)
      apply (rule setsum_cong)
      apply simp
      apply (rule setsum_cong) apply simp
      apply (auto simp: ac_simps)
      apply (subst fold_commute_apply[where f="(\<lambda>d. op * (H \<bullet> d))" and g="(\<lambda>d. op * (H \<bullet> d))"
        and h="\<lambda>x. (H \<bullet> b) * x" for b])
      apply (auto simp: mult_commute)
      done
    finally have "((\<lambda>t. sumDs k (line t)) has_vector_derivative sumDs (Suc k) (line t))
      (at t within {0..1})" .
  } hence diff_Suc: "\<And>t ds k. t \<in> {0..1} \<Longrightarrow>  k \<le> n \<Longrightarrow>
    ((\<lambda>t. diff k (line t)) has_vector_derivative diff (Suc k) (line t)) (at t within {0..1})"
    unfolding diff_def
    apply (case_tac k)
    apply (auto intro!: Ds_0)
    apply (simp add: sumDs_def sumH_def scaleR_setsum_left[symmetric])
    unfolding has_vector_derivative_def
    apply (rule diff_chain_componentwise[THEN FDERIV_eq_rhs])
    apply (rule Ds_0)
    using line_in_G apply force
    apply (rule line_fderiv)
    apply (rule line_in_G)
    apply simp
    apply (auto simp: field_simps scaleR_setsum_right)
    done
  have diff_0: "\<And>t. diff 0 (line t) = f (line t)" by (simp add: diff_def)
  from taylor_up_within_vector[of _ 0 1 "\<lambda>k t. diff k (line t)",
    OF zero_less_Suc[of n] diff_0 diff_Suc order_refl zero_less_one]
  obtain tt where "(\<forall>i\<in>Basis. 0 < tt i \<and> tt i < 1)"
    "f (X + H) =
      (\<Sum>m = 0..<Suc n. (diff m X /\<^sub>R real (fact m))) +
      (\<Sum>x\<in>Basis. ((diff (Suc n) (line (tt x)) /\<^sub>R real (fact (Suc n))) \<bullet> x) *\<^sub>R x)"
    by (auto simp: line_def)
  thus ?thesis by auto
qed

end

end
