section \<open>\<open>Complex_Vector_Spaces\<close> -- Complex Vector Spaces\<close>

(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee
*)

theory Complex_Vector_Spaces
  imports
    "HOL-Analysis.Elementary_Topology"
    "HOL-Analysis.Operator_Norm"
    "HOL-Analysis.Elementary_Normed_Spaces"
    "HOL-Library.Set_Algebras"
    "HOL-Analysis.Starlike"
    "HOL-Types_To_Sets.Types_To_Sets"
    "HOL-Library.Complemented_Lattices"
    "HOL-Library.Function_Algebras"

    Extra_Vector_Spaces
    Extra_Ordered_Fields
    Extra_Operator_Norm
    Extra_General

    Complex_Vector_Spaces0
begin

bundle norm_syntax begin
notation norm (\<open>\<parallel>_\<parallel>\<close>)
end

unbundle lattice_syntax

subsection \<open>Misc\<close>


(* Should rather be in Extra_Vector_Spaces but then complex_vector.span_image_scale' does not exist for some reason.
   Ideally this would replace Vector_Spaces.vector_space.span_image_scale. *)
lemma (in vector_space) span_image_scale':
  \<comment> \<open>Strengthening of @{thm [source] vector_space.span_image_scale} without the condition \<open>finite S\<close>\<close>
  assumes nz: "\<And>x. x \<in> S \<Longrightarrow> c x \<noteq> 0"
  shows "span ((\<lambda>x. c x *s x) ` S) = span S"
proof
  have \<open>((\<lambda>x. c x *s x) ` S) \<subseteq> span S\<close>
    by (metis (mono_tags, lifting) image_subsetI in_mono local.span_superset local.subspace_scale local.subspace_span)
  then show \<open>span ((\<lambda>x. c x *s x) ` S) \<subseteq> span S\<close>
    by (simp add: local.span_minimal)
next
  have \<open>x \<in> span ((\<lambda>x. c x *s x) ` S)\<close> if \<open>x \<in> S\<close> for x
  proof -
    have \<open>x = inverse (c x) *s c x *s x\<close>
      by (simp add: nz that)
    moreover have \<open>c x *s x \<in> (\<lambda>x. c x *s x) ` S\<close>
      using that by blast
    ultimately show ?thesis
      by (metis local.span_base local.span_scale)
  qed
  then show \<open>span S \<subseteq> span ((\<lambda>x. c x *s x) ` S)\<close>
    by (simp add: local.span_minimal subsetI)
qed

lemma (in scaleC) scaleC_real: assumes "r\<in>\<real>" shows "r *\<^sub>C x = Re r *\<^sub>R x"
  unfolding scaleR_scaleC using assms by simp

lemma of_complex_of_real_eq [simp]: "of_complex (of_real n) = of_real n"
  unfolding of_complex_def of_real_def unfolding scaleR_scaleC by simp

lemma Complexs_of_real [simp]: "of_real r \<in> \<complex>"
  unfolding Complexs_def of_real_def of_complex_def
  apply (subst scaleR_scaleC) by simp

lemma Reals_in_Complexs: "\<real> \<subseteq> \<complex>"
  unfolding Reals_def by auto

lemma (in bounded_clinear) bounded_linear: "bounded_linear f"
  by standard

lemma clinear_times: "clinear (\<lambda>x. c * x)"
  for c :: "'a::complex_algebra"
  by (auto simp: clinearI distrib_left)

lemma (in clinear) linear: \<open>linear f\<close>
  by standard

lemma bounded_clinearI:
  assumes \<open>\<And>b1 b2. f (b1 + b2) = f b1 + f b2\<close>
  assumes \<open>\<And>r b. f (r *\<^sub>C b) = r *\<^sub>C f b\<close>
  assumes \<open>\<And>x. norm (f x) \<le> norm x * K\<close>
  shows "bounded_clinear f"
  using assms by (auto intro!: exI bounded_clinear.intro clinearI simp: bounded_clinear_axioms_def)

lemma bounded_clinear_id[simp]: \<open>bounded_clinear id\<close>
  by (simp add: id_def)

lemma bounded_clinear_0[simp]: \<open>bounded_clinear 0\<close>
  by (auto intro!: bounded_clinearI[where K=0])

definition cbilinear :: \<open>('a::complex_vector \<Rightarrow> 'b::complex_vector \<Rightarrow> 'c::complex_vector) \<Rightarrow> bool\<close>
  where \<open>cbilinear = (\<lambda> f. (\<forall> y. clinear (\<lambda> x. f x y)) \<and> (\<forall> x. clinear (\<lambda> y. f x y)) )\<close>

lemma cbilinear_add_left:
  assumes \<open>cbilinear f\<close>
  shows \<open>f (a + b) c = f a c + f b c\<close>
  by (smt (verit, del_insts) assms cbilinear_def complex_vector.linear_add)

lemma cbilinear_add_right:
  assumes \<open>cbilinear f\<close>
  shows \<open>f a (b + c) = f a b + f a c\<close>
  by (smt (verit, del_insts) assms cbilinear_def complex_vector.linear_add)

lemma cbilinear_times:
  fixes g' :: \<open>'a::complex_vector \<Rightarrow> complex\<close> and g :: \<open>'b::complex_vector \<Rightarrow> complex\<close>
  assumes \<open>\<And> x y. h x y = (g' x)*(g y)\<close> and \<open>clinear g\<close> and \<open>clinear g'\<close>
  shows \<open>cbilinear h\<close>
proof -
  have w1: "h (b1 + b2) y = h b1 y + h b2 y"
    for b1 :: 'a
      and b2 :: 'a
      and y
  proof-
    have \<open>h (b1 + b2) y = g' (b1 + b2) * g y\<close>
      using \<open>\<And> x y. h x y = (g' x)*(g y)\<close>
      by auto
    also have \<open>\<dots> = (g' b1 + g' b2) * g y\<close>
      using \<open>clinear g'\<close>
      unfolding clinear_def
      by (simp add: assms(3) complex_vector.linear_add)
    also have \<open>\<dots> = g' b1 * g y + g' b2 * g y\<close>
      by (simp add: ring_class.ring_distribs(2))
    also have \<open>\<dots> = h b1 y + h b2 y\<close>
      using assms(1) by auto
    finally show ?thesis by blast
  qed
  have w2: "h (r *\<^sub>C b) y = r *\<^sub>C h b y"
    for r :: complex
      and b :: 'a
      and y
  proof-
    have \<open>h (r *\<^sub>C b) y = g' (r *\<^sub>C b) * g y\<close>
      by (simp add: assms(1))
    also have \<open>\<dots> = r *\<^sub>C (g' b * g y)\<close>
      by (simp add: assms(3) complex_vector.linear_scale)
    also have \<open>\<dots> = r *\<^sub>C (h b y)\<close>
      by (simp add: assms(1))
    finally show ?thesis by blast
  qed
  have "clinear (\<lambda>x. h x y)"
    for y :: 'b
    unfolding clinear_def
    by (meson clinearI clinear_def w1 w2)
  hence t2: "\<forall>y. clinear (\<lambda>x. h x y)"
    by simp
  have v1: "h x (b1 + b2) = h x b1 + h x b2"
    for b1 :: 'b
      and b2 :: 'b
      and x
  proof-
    have \<open>h x (b1 + b2)  = g' x * g (b1 + b2)\<close>
      using \<open>\<And> x y. h x y = (g' x)*(g y)\<close>
      by auto
    also have \<open>\<dots> = g' x * (g b1 + g b2)\<close>
      using \<open>clinear g'\<close>
      unfolding clinear_def
      by (simp add: assms(2) complex_vector.linear_add)
    also have \<open>\<dots> = g' x * g b1 + g' x * g b2\<close>
      by (simp add: ring_class.ring_distribs(1))
    also have \<open>\<dots> = h x b1 + h x b2\<close>
      using assms(1) by auto
    finally show ?thesis by blast
  qed

  have v2:  "h x (r *\<^sub>C b) = r *\<^sub>C h x b"
    for r :: complex
      and b :: 'b
      and x
  proof-
    have \<open>h x (r *\<^sub>C b) =  g' x * g (r *\<^sub>C b)\<close>
      by (simp add: assms(1))
    also have \<open>\<dots> = r *\<^sub>C (g' x * g b)\<close>
      by (simp add: assms(2) complex_vector.linear_scale)
    also have \<open>\<dots> = r *\<^sub>C (h x b)\<close>
      by (simp add: assms(1))
    finally show ?thesis by blast
  qed
  have "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) (h x)"
    for x :: 'a
    using v1 v2
    by (meson clinearI clinear_def)
  hence t1: "\<forall>x. clinear (h x)"
    unfolding clinear_def
    by simp
  show ?thesis
    unfolding cbilinear_def
    by (simp add: t1 t2)
qed

lemma csubspace_is_subspace: "csubspace A \<Longrightarrow> subspace A"
  apply (rule subspaceI)
  by (auto simp: complex_vector.subspace_def scaleR_scaleC)

lemma span_subset_cspan: "span A \<subseteq> cspan A"
  unfolding span_def complex_vector.span_def
  by (simp add: csubspace_is_subspace hull_antimono)


lemma cindependent_implies_independent:
  assumes "cindependent (S::'a::complex_vector set)"
  shows "independent S"
  using assms unfolding dependent_def complex_vector.dependent_def
  using span_subset_cspan by blast

lemma cspan_singleton: "cspan {x} = {\<alpha> *\<^sub>C x| \<alpha>. True}"
proof -
  have \<open>cspan {x} = {y. y\<in>cspan {x}}\<close>
    by auto
  also have \<open>\<dots> = {\<alpha> *\<^sub>C x| \<alpha>. True}\<close>
    apply (subst complex_vector.span_breakdown_eq)
    by auto
  finally show ?thesis
    by -
qed


lemma cspan_as_span:
  "cspan (B::'a::complex_vector set) = span (B \<union> scaleC \<i> ` B)"
proof (intro set_eqI iffI)
  let ?cspan = complex_vector.span
  let ?rspan = real_vector.span
  fix \<psi>
  assume cspan: "\<psi> \<in> ?cspan B"
  have "\<exists>B' r. finite B' \<and> B' \<subseteq> B \<and> \<psi> = (\<Sum>b\<in>B'. r b *\<^sub>C b)"
    using complex_vector.span_explicit[of B] cspan
    by auto
  then obtain B' r where "finite B'" and "B' \<subseteq> B" and \<psi>_explicit: "\<psi> = (\<Sum>b\<in>B'. r b *\<^sub>C b)"
    by atomize_elim
  define R where "R = B \<union> scaleC \<i> ` B"

  have x2: "(case x of (b, i) \<Rightarrow> if i
            then Im (r b) *\<^sub>R \<i> *\<^sub>C b
            else Re (r b) *\<^sub>R b) \<in> span (B \<union> (*\<^sub>C) \<i> ` B)"
    if "x \<in> B' \<times> (UNIV::bool set)"
    for x :: "'a \<times> bool"
    using that \<open>B' \<subseteq> B\<close> by (auto simp add: real_vector.span_base real_vector.span_scale subset_iff)
  have x1: "\<psi> = (\<Sum>x\<in>B'. \<Sum>i\<in>UNIV. if i then Im (r x) *\<^sub>R \<i> *\<^sub>C x else Re (r x) *\<^sub>R x)"
    if "\<And>b. r b *\<^sub>C b = Re (r b) *\<^sub>R b + Im (r b) *\<^sub>R \<i> *\<^sub>C b"
    using that by (simp add: UNIV_bool \<psi>_explicit)
  moreover have "r b *\<^sub>C b = Re (r b) *\<^sub>R b + Im (r b) *\<^sub>R \<i> *\<^sub>C b" for b
    using complex_eq scaleC_add_left scaleC_scaleC scaleR_scaleC
    by (metis (no_types, lifting) complex_of_real_i i_complex_of_real)
  ultimately have "\<psi> = (\<Sum>(b,i)\<in>(B'\<times>UNIV). if i then Im (r b) *\<^sub>R (\<i> *\<^sub>C b) else Re (r b) *\<^sub>R b)"
    by (simp add: sum.cartesian_product)
  also have "\<dots> \<in> ?rspan R"
    unfolding R_def
    using x2
    by (rule real_vector.span_sum)
  finally show "\<psi> \<in> ?rspan R" by -
next
  let ?cspan = complex_vector.span
  let ?rspan = real_vector.span
  define R where "R = B \<union> scaleC \<i> ` B"
  fix \<psi>
  assume rspan: "\<psi> \<in> ?rspan R"
  have "subspace {a. a \<in> cspan B}"
    by (rule real_vector.subspaceI, auto simp add: complex_vector.span_zero
        complex_vector.span_add_eq2 complex_vector.span_scale scaleR_scaleC)
  moreover have "x \<in> cspan B"
    if "x \<in> R"
    for x :: 'a
    using that R_def complex_vector.span_base complex_vector.span_scale by fastforce
  ultimately show "\<psi> \<in> ?cspan B"
    using real_vector.span_induct rspan by blast
qed


lemma isomorphic_equal_cdim:
  assumes lin_f: \<open>clinear f\<close>
  assumes inj_f: \<open>inj_on f (cspan S)\<close>
  assumes im_S: \<open>f ` S = T\<close>
  shows \<open>cdim S = cdim T\<close>
proof -
  obtain SB where SB_span: "cspan SB = cspan S" and indep_SB: \<open>cindependent SB\<close>
    by (metis complex_vector.basis_exists complex_vector.span_mono complex_vector.span_span subset_antisym)
  with lin_f inj_f have indep_fSB: \<open>cindependent (f ` SB)\<close>
    apply (rule_tac complex_vector.linear_independent_injective_image)
    by auto
  from lin_f have \<open>cspan (f ` SB) = f ` cspan SB\<close>
    by (meson complex_vector.linear_span_image)
  also from SB_span lin_f have \<open>\<dots> = cspan T\<close>
    by (metis complex_vector.linear_span_image im_S)
  finally have \<open>cdim T = card (f ` SB)\<close>
    using indep_fSB complex_vector.dim_eq_card by blast
  also have \<open>\<dots> = card SB\<close>
    apply (rule card_image) using inj_f
    by (metis SB_span complex_vector.linear_inj_on_span_iff_independent_image indep_fSB lin_f)
  also have \<open>\<dots> = cdim S\<close>
    using indep_SB SB_span
    by (metis complex_vector.dim_eq_card)
  finally show ?thesis by simp
qed


lemma cindependent_inter_scaleC_cindependent:
  assumes a1: "cindependent (B::'a::complex_vector set)" and a3: "c \<noteq> 1"
  shows "B \<inter> (*\<^sub>C) c ` B = {}"
proof (rule classical, cases \<open>c = 0\<close>)
  case True
  then show ?thesis
    using a1 by (auto simp add: complex_vector.dependent_zero)
next
  case False
  assume "\<not>(B \<inter> (*\<^sub>C) c ` B = {})"
  hence "B \<inter> (*\<^sub>C) c ` B \<noteq> {}"
    by blast
  then obtain x where u1: "x \<in> B \<inter> (*\<^sub>C) c ` B"
    by blast
  then obtain b where u2: "x = b" and u3: "b\<in>B"
    by blast
  then  obtain b' where u2': "x = c *\<^sub>C b'" and u3': "b'\<in>B"
    using u1
    by blast
  have g1: "b = c *\<^sub>C b'"
    using u2 and u2' by simp
  hence "b \<in> complex_vector.span {b'}"
    using False
    by (simp add: complex_vector.span_base complex_vector.span_scale)
  hence "b = b'"
    by (metis  u3' a1 complex_vector.dependent_def complex_vector.span_base
        complex_vector.span_scale insertE insert_Diff u2 u2' u3)
  hence "b' = c *\<^sub>C b'"
    using g1 by blast
  thus ?thesis
    by (metis a1 a3 complex_vector.dependent_zero complex_vector.scale_right_imp_eq
        mult_cancel_right2 scaleC_scaleC u3')
qed

lemma real_independent_from_complex_independent:
  assumes "cindependent (B::'a::complex_vector set)"
  defines "B' == ((*\<^sub>C) \<i> ` B)"
  shows "independent (B \<union> B')"
proof (rule notI)
  assume \<open>dependent (B \<union> B')\<close>
  then obtain T f0 x where [simp]: \<open>finite T\<close> and \<open>T \<subseteq> B \<union> B'\<close> and f0_sum: \<open>(\<Sum>v\<in>T. f0 v *\<^sub>R v) = 0\<close>
    and x: \<open>x \<in> T\<close> and f0_x: \<open>f0 x \<noteq> 0\<close>
    by (auto simp: real_vector.dependent_explicit)
  define f T1 T2 T' f' x' where \<open>f v = (if v \<in> T then f0 v else 0)\<close>
    and \<open>T1 = T \<inter> B\<close> and \<open>T2 = scaleC (-\<i>) ` (T \<inter> B')\<close>
    and \<open>T' = T1 \<union> T2\<close> and \<open>f' v = f v + \<i> * f (\<i> *\<^sub>C v)\<close>
    and \<open>x' = (if x \<in> T1 then x else -\<i> *\<^sub>C x)\<close> for v
  have \<open>B \<inter> B' = {}\<close>
    by (simp add: assms cindependent_inter_scaleC_cindependent)
  have \<open>T' \<subseteq> B\<close>
    by (auto simp: T'_def T1_def T2_def B'_def)
  have [simp]: \<open>finite T'\<close> \<open>finite T1\<close> \<open>finite T2\<close>
    by (auto simp add: T'_def T1_def T2_def)
  have f_sum: \<open>(\<Sum>v\<in>T. f v *\<^sub>R v) = 0\<close>
    unfolding f_def using f0_sum by auto
  have f_x: \<open>f x \<noteq> 0\<close>
    using f0_x x by (auto simp: f_def)
  have f'_sum: \<open>(\<Sum>v\<in>T'. f' v *\<^sub>C v) = 0\<close>
  proof -
    have \<open>(\<Sum>v\<in>T'. f' v *\<^sub>C v) = (\<Sum>v\<in>T'. complex_of_real (f v) *\<^sub>C v) + (\<Sum>v\<in>T'. (\<i> * complex_of_real (f (\<i> *\<^sub>C v))) *\<^sub>C v)\<close>
      by (auto simp: f'_def sum.distrib scaleC_add_left)
    also have \<open>(\<Sum>v\<in>T'. complex_of_real (f v) *\<^sub>C v) = (\<Sum>v\<in>T1. f v *\<^sub>R v)\<close> (is \<open>_ = ?left\<close>)
      apply (auto simp: T'_def scaleR_scaleC intro!: sum.mono_neutral_cong_right)
      using T'_def T1_def \<open>T' \<subseteq> B\<close> f_def by auto
    also have \<open>(\<Sum>v\<in>T'. (\<i> * complex_of_real (f (\<i> *\<^sub>C v))) *\<^sub>C v) = (\<Sum>v\<in>T2. (\<i> * complex_of_real (f (\<i> *\<^sub>C v))) *\<^sub>C v)\<close> (is \<open>_ = ?right\<close>)
      apply (auto simp: T'_def intro!: sum.mono_neutral_cong_right)
      by (smt (z3) B'_def IntE IntI T1_def T2_def \<open>f \<equiv> \<lambda>v. if v \<in> T then f0 v else 0\<close> add.inverse_inverse complex_vector.vector_space_axioms i_squared imageI mult_minus_left vector_space.vector_space_assms(3) vector_space.vector_space_assms(4))
    also have \<open>?right = (\<Sum>v\<in>T\<inter>B'. f v *\<^sub>R v)\<close> (is \<open>_ = ?right\<close>)
      apply (rule sum.reindex_cong[symmetric, where l=\<open>scaleC \<i>\<close>])
        apply (auto simp: T2_def image_image scaleR_scaleC)
      using inj_on_def by fastforce
    also have \<open>?left + ?right = (\<Sum>v\<in>T. f v *\<^sub>R v)\<close>
      apply (subst sum.union_disjoint[symmetric])
      using \<open>B \<inter> B' = {}\<close> \<open>T \<subseteq> B \<union> B'\<close> apply (auto simp: T1_def)
      by (metis Int_Un_distrib Un_Int_eq(4) sup.absorb_iff1)
    also have \<open>\<dots> = 0\<close>
      by (rule f_sum)
    finally show ?thesis
      by -
  qed

  have x': \<open>x' \<in> T'\<close>
    using \<open>T \<subseteq> B \<union> B'\<close> x by (auto simp: x'_def T'_def T1_def T2_def)

  have f'_x': \<open>f' x' \<noteq> 0\<close>
    using Complex_eq Complex_eq_0 f'_def f_x x'_def by auto

  from \<open>finite T'\<close> \<open>T' \<subseteq> B\<close> f'_sum x' f'_x'
  have \<open>cdependent B\<close>
    using complex_vector.independent_explicit_module by blast
  with assms show False
    by auto
qed

lemma crepresentation_from_representation:
  assumes a1: "cindependent B" and a2: "b \<in> B" and a3: "finite B"
  shows "crepresentation B \<psi> b = (representation (B \<union> (*\<^sub>C) \<i> ` B) \<psi> b)
                           + \<i> *\<^sub>C (representation (B \<union> (*\<^sub>C) \<i> ` B) \<psi> (\<i> *\<^sub>C b))"
proof (cases "\<psi> \<in> cspan B")
  define B' where "B' = B \<union> (*\<^sub>C) \<i> ` B"
  case True
  define r  where "r v = real_vector.representation B' \<psi> v" for v
  define r' where "r' v = real_vector.representation B' \<psi> (\<i> *\<^sub>C v)" for v
  define f  where "f v = r v + \<i> *\<^sub>C r' v" for v
  define g  where "g v = crepresentation B \<psi> v" for v
  have "(\<Sum>v | g v \<noteq> 0. g v *\<^sub>C v) = \<psi>"
    unfolding g_def
    using Collect_cong Collect_mono_iff DiffD1 DiffD2 True a1
      complex_vector.finite_representation
      complex_vector.sum_nonzero_representation_eq sum.mono_neutral_cong_left
    by fastforce
  moreover have "finite {v. g v \<noteq> 0}"
    unfolding g_def
    by (simp add: complex_vector.finite_representation)
  moreover have "v \<in> B"
    if "g v \<noteq> 0" for v
    using that unfolding g_def
    by (simp add: complex_vector.representation_ne_zero)
  ultimately have rep1: "(\<Sum>v\<in>B. g v *\<^sub>C v) = \<psi>"
    unfolding g_def
    using a3 True a1 complex_vector.sum_representation_eq by blast
  have l0': "inj ((*\<^sub>C) \<i>::'a \<Rightarrow>'a)"
    unfolding inj_def
    by simp
  have l0: "inj ((*\<^sub>C) (- \<i>)::'a \<Rightarrow>'a)"
    unfolding inj_def
    by simp
  have l1: "(*\<^sub>C) (- \<i>) ` B \<inter> B = {}"
    using cindependent_inter_scaleC_cindependent[where B=B and c = "- \<i>"]
    by (metis Int_commute a1 add.inverse_inverse complex_i_not_one i_squared mult_cancel_left1
        neg_equal_0_iff_equal)
  have l2: "B \<inter> (*\<^sub>C) \<i> ` B = {}"
    by (simp add: a1 cindependent_inter_scaleC_cindependent)
  have rr1: "r (\<i> *\<^sub>C v) = r' v" for v
    unfolding r_def r'_def
    by simp
  have k1: "independent B'"
    unfolding B'_def using a1 real_independent_from_complex_independent by simp
  have "\<psi> \<in> span B'"
    using B'_def True cspan_as_span by blast
  have "v \<in> B'"
    if "r v \<noteq> 0"
    for v
    unfolding r_def
    using r_def real_vector.representation_ne_zero that by auto
  have "finite B'"
    unfolding B'_def using a3
    by simp
  have "(\<Sum>v\<in>B'. r v *\<^sub>R v) = \<psi>"
    unfolding r_def
    using True  Real_Vector_Spaces.real_vector.sum_representation_eq[where B = B' and basis = B'
        and v = \<psi>]
    by (smt Real_Vector_Spaces.dependent_raw_def \<open>\<psi> \<in> Real_Vector_Spaces.span B'\<close> \<open>finite B'\<close>
        equalityD2 k1)
  have d1: "(\<Sum>v\<in>B. r (\<i> *\<^sub>C v) *\<^sub>R (\<i> *\<^sub>C v)) = (\<Sum>v\<in>(*\<^sub>C) \<i> ` B. r v *\<^sub>R v)"
    using l0'
    by (metis (mono_tags, lifting) inj_eq inj_on_def sum.reindex_cong)
  have "(\<Sum>v\<in>B. (r v + \<i> * (r' v)) *\<^sub>C v) = (\<Sum>v\<in>B. r v *\<^sub>C v + (\<i> * r' v) *\<^sub>C v)"
    by (meson scaleC_left.add)
  also have "\<dots> = (\<Sum>v\<in>B. r v *\<^sub>C v) + (\<Sum>v\<in>B. (\<i> * r' v) *\<^sub>C v)"
    using sum.distrib by fastforce
  also have "\<dots> = (\<Sum>v\<in>B. r v *\<^sub>C v) + (\<Sum>v\<in>B. \<i> *\<^sub>C (r' v *\<^sub>C v))"
    by auto
  also have "\<dots> = (\<Sum>v\<in>B. r v *\<^sub>R v) + (\<Sum>v\<in>B. \<i> *\<^sub>C (r (\<i> *\<^sub>C v) *\<^sub>R v))"
    unfolding r'_def r_def
    by (metis (mono_tags, lifting) scaleR_scaleC sum.cong)
  also have "\<dots> = (\<Sum>v\<in>B. r v *\<^sub>R v) + (\<Sum>v\<in>B. r (\<i> *\<^sub>C v) *\<^sub>R (\<i> *\<^sub>C v))"
    by (metis (no_types, lifting) complex_vector.scale_left_commute scaleR_scaleC)
  also have "\<dots> = (\<Sum>v\<in>B. r v *\<^sub>R v) + (\<Sum>v\<in>(*\<^sub>C) \<i> ` B. r v *\<^sub>R v)"
    using d1
    by simp
  also have "\<dots> = \<psi>"
    using l2 \<open>(\<Sum>v\<in>B'. r v *\<^sub>R v) = \<psi>\<close>
    unfolding B'_def
    by (simp add: a3 sum.union_disjoint)
  finally have "(\<Sum>v\<in>B. f v *\<^sub>C v) = \<psi>" unfolding r'_def r_def f_def by simp
  hence "0 = (\<Sum>v\<in>B. f v *\<^sub>C v) - (\<Sum>v\<in>B. crepresentation B \<psi> v *\<^sub>C v)"
    using rep1
    unfolding g_def
    by simp
  also have "\<dots> = (\<Sum>v\<in>B. f v *\<^sub>C v - crepresentation B \<psi> v *\<^sub>C v)"
    by (simp add: sum_subtractf)
  also have "\<dots> = (\<Sum>v\<in>B. (f v - crepresentation B \<psi> v) *\<^sub>C v)"
    by (metis scaleC_left.diff)
  finally have "0 = (\<Sum>v\<in>B. (f v - crepresentation B \<psi> v) *\<^sub>C v)".
  hence "(\<Sum>v\<in>B. (f v - crepresentation B \<psi> v) *\<^sub>C v) = 0"
    by simp
  hence "f b - crepresentation B \<psi> b = 0"
    using a1 a2 a3 complex_vector.independentD[where s = B and t = B
        and u = "\<lambda>v. f v - crepresentation B \<psi> v" and v = b]
      order_refl  by smt
  hence "crepresentation B \<psi> b = f b"
    by simp
  thus ?thesis unfolding f_def r_def r'_def B'_def by auto
next
  define B' where "B' = B \<union> (*\<^sub>C) \<i> ` B"
  case False
  have b2: "\<psi> \<notin> real_vector.span B'"
    unfolding B'_def
    using False cspan_as_span by auto
  have "\<psi> \<notin> complex_vector.span B"
    using False by blast
  have "crepresentation B \<psi> b = 0"
    unfolding complex_vector.representation_def
    by (simp add: False)
  moreover have "real_vector.representation B' \<psi> b = 0"
    unfolding real_vector.representation_def
    by (simp add: b2)
  moreover have "real_vector.representation B' \<psi> ((*\<^sub>C) \<i> b) = 0"
    unfolding real_vector.representation_def
    by (simp add: b2)
  ultimately show ?thesis unfolding B'_def by simp
qed


lemma CARD_1_vec_0[simp]: \<open>(\<psi> :: _ ::{complex_vector,CARD_1}) = 0\<close>
  by auto


lemma scaleC_cindependent:
  assumes a1: "cindependent (B::'a::complex_vector set)" and a3: "c \<noteq> 0"
  shows "cindependent ((*\<^sub>C) c ` B)"
proof-
  have "u y = 0"
    if g1: "y\<in>S" and g2: "(\<Sum>x\<in>S. u x *\<^sub>C x) = 0" and g3: "finite S" and g4: "S\<subseteq>(*\<^sub>C) c ` B"
    for u y S
  proof-
    define v where "v x = u (c *\<^sub>C x)" for x
    obtain S' where "S'\<subseteq>B" and S_S': "S = (*\<^sub>C) c ` S'"
      by (meson g4 subset_imageE)
    have "inj ((*\<^sub>C) c::'a\<Rightarrow>_)"
      unfolding inj_def
      using a3 by auto
    hence "finite S'"
      using S_S' finite_imageD g3 inj_on_subset by blast
    have "t \<in> (*\<^sub>C) (inverse c) ` S"
      if "t \<in> S'" for t
    proof-
      have "c *\<^sub>C t \<in> S"
        using \<open>S = (*\<^sub>C) c ` S'\<close> that by blast
      hence "(inverse c) *\<^sub>C (c *\<^sub>C t) \<in> (*\<^sub>C) (inverse c) ` S"
        by blast
      moreover have "(inverse c) *\<^sub>C (c *\<^sub>C t) = t"
        by (simp add: a3)
      ultimately show ?thesis by simp
    qed
    moreover have "t \<in> S'"
      if "t \<in> (*\<^sub>C) (inverse c) ` S" for t
    proof-
      obtain t' where "t = (inverse c) *\<^sub>C t'" and "t' \<in> S"
        using \<open>t \<in> (*\<^sub>C) (inverse c) ` S\<close> by auto
      have "c *\<^sub>C t = c *\<^sub>C ((inverse c) *\<^sub>C t')"
        using \<open>t = (inverse c) *\<^sub>C t'\<close> by simp
      also have "\<dots> = (c * (inverse c)) *\<^sub>C t'"
        by simp
      also have "\<dots> = t'"
        by (simp add: a3)
      finally have "c *\<^sub>C t = t'".
      thus ?thesis using \<open>t' \<in> S\<close>
        using \<open>S = (*\<^sub>C) c ` S'\<close> a3 complex_vector.scale_left_imp_eq by blast
    qed
    ultimately have "S' = (*\<^sub>C) (inverse c) ` S"
      by blast
    hence "inverse c *\<^sub>C y \<in> S'"
      using that(1) by blast
    have t: "inj (((*\<^sub>C) c)::'a \<Rightarrow> _)"
      using a3 complex_vector.injective_scale[where c = c]
      by blast
    have "0 = (\<Sum>x\<in>(*\<^sub>C) c ` S'. u x *\<^sub>C x)"
      using \<open>S = (*\<^sub>C) c ` S'\<close> that(2) by auto
    also have "\<dots> = (\<Sum>x\<in>S'. v x *\<^sub>C (c *\<^sub>C x))"
      unfolding v_def
      using t Groups_Big.comm_monoid_add_class.sum.reindex[where h = "((*\<^sub>C) c)" and A = S'
          and g = "\<lambda>x. u x *\<^sub>C x"] inj_on_subset by auto
    also have "\<dots> = c *\<^sub>C (\<Sum>x\<in>S'. v x *\<^sub>C x)"
      by (metis (mono_tags, lifting) complex_vector.scale_left_commute scaleC_right.sum sum.cong)
    finally have "0 = c *\<^sub>C (\<Sum>x\<in>S'. v x *\<^sub>C x)".
    hence "(\<Sum>x\<in>S'. v x *\<^sub>C x) = 0"
      using a3 by auto
    hence "v (inverse c *\<^sub>C y) = 0"
      using \<open>inverse c *\<^sub>C y \<in> S'\<close> \<open>finite S'\<close> \<open>S' \<subseteq> B\<close> a1
        complex_vector.independentD
      by blast
    thus "u y = 0"
      unfolding v_def
      by (simp add: a3)
  qed
  thus ?thesis
    using complex_vector.dependent_explicit
    by (simp add: complex_vector.dependent_explicit )
qed

lemma cspan_eqI:
  assumes \<open>\<And>a. a\<in>A \<Longrightarrow> a\<in>cspan B\<close>
  assumes \<open>\<And>b. b\<in>B \<Longrightarrow> b\<in>cspan A\<close>
  shows \<open>cspan A = cspan B\<close>
  apply (rule complex_vector.span_subspace[rotated])
    apply (rule complex_vector.span_minimal)
  using assms by auto

lemma (in bounded_cbilinear) bounded_bilinear[simp]: "bounded_bilinear prod"
  by standard

lemma norm_scaleC_sgn[simp]: \<open>complex_of_real (norm \<psi>) *\<^sub>C sgn \<psi> = \<psi>\<close> for \<psi> :: "'a::complex_normed_vector"
  apply (cases \<open>\<psi> = 0\<close>)
  by (auto simp: sgn_div_norm scaleR_scaleC)

lemma scaleC_of_complex[simp]: \<open>scaleC x (of_complex y) = of_complex (x * y)\<close>
  unfolding of_complex_def using scaleC_scaleC by blast

lemma bounded_clinear_inv:
  assumes [simp]: \<open>bounded_clinear f\<close>
  assumes b: \<open>b > 0\<close>
  assumes bound: \<open>\<And>x. norm (f x) \<ge> b * norm x\<close>
  assumes \<open>surj f\<close>
  shows \<open>bounded_clinear (inv f)\<close>
proof (rule bounded_clinear_intro)
  fix x y :: 'b and r :: complex
  define x' y' where \<open>x' = inv f x\<close> and \<open>y' = inv f y\<close>
  have [simp]: \<open>clinear f\<close>
    by (simp add: bounded_clinear.clinear)
  have [simp]: \<open>inj f\<close>
  proof (rule injI)
    fix x y assume \<open>f x = f y\<close>
    then have \<open>norm (f (x - y)) = 0\<close>
      by (simp add: complex_vector.linear_diff)
    with bound b have \<open>norm (x - y) = 0\<close>
      by (metis linorder_not_le mult_le_0_iff nle_le norm_ge_zero)
    then show \<open>x = y\<close>
      by simp
  qed

  from \<open>surj f\<close>
  have [simp]: \<open>x = f x'\<close> \<open>y = f y'\<close>
    by (simp_all add: surj_f_inv_f x'_def y'_def)
  show "inv f (x + y) = inv f x + inv f y"
    by (simp flip: complex_vector.linear_add)
  show "inv f (r *\<^sub>C x) = r *\<^sub>C inv f x"
    by (simp flip: clinear.scaleC)
  from bound have "b * norm (inv f x) \<le> norm x" 
    by (simp flip: clinear.scaleC)
  with b show "norm (inv f x) \<le> norm x * inverse b" 
    by (smt (verit, ccfv_threshold) left_inverse mult.commute mult_cancel_right1 mult_le_cancel_left_pos vector_space_over_itself.scale_scale)
qed

lemma range_is_csubspace[simp]:
  assumes a1: "clinear f"
  shows "csubspace (range f)"
  using assms complex_vector.linear_subspace_image complex_vector.subspace_UNIV by blast

lemma csubspace_is_convex[simp]:
  assumes a1: "csubspace M"
  shows "convex M"
proof-
  have \<open>\<forall>x\<in>M. \<forall>y\<in> M. \<forall>u. \<forall>v. u *\<^sub>C x + v *\<^sub>C y \<in>  M\<close>
    using a1
    by (simp add:  complex_vector.subspace_def)
  hence \<open>\<forall>x\<in>M. \<forall>y\<in>M. \<forall>u::real. \<forall>v::real. u *\<^sub>R x + v *\<^sub>R y \<in> M\<close>
    by (simp add: scaleR_scaleC)
  hence \<open>\<forall>x\<in>M. \<forall>y\<in>M. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in>M\<close>
    by blast
  thus ?thesis using convex_def by blast
qed

lemma kernel_is_csubspace[simp]:
  assumes a1: "clinear f"
  shows "csubspace  (f -` {0})"
  by (simp add: assms complex_vector.linear_subspace_vimage)

lemma bounded_cbilinear_0[simp]: \<open>bounded_cbilinear (\<lambda>_ _. 0)\<close>
  by (auto intro!: bounded_cbilinear.intro exI[where x=0])
lemma bounded_cbilinear_0'[simp]: \<open>bounded_cbilinear 0\<close>
  by (auto intro!: bounded_cbilinear.intro exI[where x=0])

lemma bounded_cbilinear_apply_bounded_clinear: \<open>bounded_clinear (f x)\<close> if \<open>bounded_cbilinear f\<close>
proof -
  interpret f: bounded_cbilinear f
    by (fact that)
  from f.bounded obtain K where \<open>norm (f a b) \<le> norm a * norm b * K\<close> for a b
    by auto
  then show ?thesis
    by (auto intro!: bounded_clinearI[where K=\<open>norm x * K\<close>] 
        simp add: f.add_right f.scaleC_right mult.commute mult.left_commute)
qed

lemma clinear_scaleR[simp]: \<open>clinear (scaleR x)\<close>
  by (simp add: complex_vector.linear_scale_self scaleR_scaleC)


lemma abs_summable_on_scaleC_left [intro]:
  fixes c :: \<open>'a :: complex_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "(\<lambda>x. f x *\<^sub>C c) abs_summable_on A"
  apply (cases \<open>c = 0\<close>)
   apply simp
  by (auto intro!: summable_on_cmult_left assms simp: norm_scaleC)

lemma abs_summable_on_scaleC_right [intro]:
  fixes f :: \<open>'a \<Rightarrow> 'b :: complex_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "(\<lambda>x. c *\<^sub>C f x) abs_summable_on A"
  apply (cases \<open>c = 0\<close>)
   apply simp
  by (auto intro!: summable_on_cmult_right assms simp: norm_scaleC)

lemma clinear_of_complex[iff]: \<open>clinear of_complex\<close>
  by (simp add: clinearI)

lemma infsum_of_bool_scaleC: \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. of_bool (x=y) *\<^sub>C f x) = of_bool (y\<in>X) *\<^sub>C f y\<close> for f :: \<open>_ \<Rightarrow> _::complex_vector\<close>
  apply (cases \<open>y\<in>X\<close>)
   apply (subst infsum_cong_neutral[where T=\<open>{y}\<close> and g=f])
      apply auto[4]
  apply (subst infsum_cong_neutral[where T=\<open>{}\<close> and g=f])
  by auto

lemma has_sum_bounded_clinear:
  assumes "bounded_clinear h" and "(f has_sum S) A"
  shows "((\<lambda>x. h (f x)) has_sum h S) A"
  apply (rule has_sum_bounded_linear[where h=h])
  by (auto intro!: bounded_clinear.bounded_linear assms)

lemma scaleC_scaleR_commute: \<open>a *\<^sub>C b *\<^sub>R x = b *\<^sub>R a *\<^sub>C x\<close> for x :: \<open>_::complex_normed_vector\<close>
  by (simp add: scaleR_scaleC scaleC_left_commute)

lemma csubspace_has_basis:
  assumes \<open>csubspace S\<close>
  shows \<open>\<exists>B. cindependent B \<and> cspan B = S\<close>
proof -
  obtain B where \<open>cindependent B\<close> and \<open>cspan B = S\<close>
    by (rule complex_vector.maximal_independent_subset[where V=S])
       (use assms complex_vector.span_subspace in blast)
  then show ?thesis
    by auto
qed

lemma inj_scaleC:
  fixes A :: \<open>'a::complex_vector set\<close>
  assumes \<open>c \<noteq> 0\<close>
  shows \<open>inj_on (scaleC c) A\<close>
  by (meson assms inj_onI scaleC_left_imp_eq)

subsection \<open>Antilinear maps and friends\<close>

locale antilinear = additive f for f :: "'a::complex_vector \<Rightarrow> 'b::complex_vector" +
  assumes scaleC: "f (scaleC r x) = cnj r *\<^sub>C f x"

sublocale antilinear \<subseteq> linear
proof (rule linearI)
  show "f (b1 + b2) = f b1 + f b2"
    for b1 :: 'a
      and b2 :: 'a
    by (simp add: add)
  show "f (r *\<^sub>R b) = r *\<^sub>R f b"
    for r :: real
      and b :: 'a
    unfolding scaleR_scaleC by (subst scaleC, simp)
qed

lemma antilinear_imp_scaleC:
  fixes D :: "complex \<Rightarrow> 'a::complex_vector"
  assumes "antilinear D"
  obtains d where "D = (\<lambda>x. cnj x *\<^sub>C d)"
proof -
  interpret clinear "D o cnj"
    apply standard apply auto
     apply (simp add: additive.add assms antilinear.axioms(1))
    using assms antilinear.scaleC by fastforce
  obtain d where "D o cnj = (\<lambda>x. x *\<^sub>C d)"
    using clinear_axioms complex_vector.linear_imp_scale by blast
  then have \<open>D = (\<lambda>x. cnj x *\<^sub>C d)\<close>
    by (metis comp_apply complex_cnj_cnj)
  then show ?thesis
    by (rule that)
qed

corollary complex_antilinearD:
  fixes f :: "complex \<Rightarrow> complex"
  assumes "antilinear f" obtains c where "f = (\<lambda>x. c * cnj x)"
  by (rule antilinear_imp_scaleC [OF assms]) (force simp: scaleC_conv_of_complex)

lemma antilinearI:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>c x. f (c *\<^sub>C x) = cnj c *\<^sub>C f x"
  shows "antilinear f"
  by standard (rule assms)+

lemma antilinear_o_antilinear: "antilinear f \<Longrightarrow> antilinear g \<Longrightarrow> clinear (g o f)"
  apply (rule clinearI)
   apply (simp add: additive.add antilinear_def)
  by (simp add: antilinear.scaleC)

lemma clinear_o_antilinear: "antilinear f \<Longrightarrow> clinear g \<Longrightarrow> antilinear (g o f)"
  apply (rule antilinearI)
   apply (simp add: additive.add complex_vector.linear_add antilinear_def)
  by (simp add: complex_vector.linear_scale antilinear.scaleC)

lemma antilinear_o_clinear: "clinear f \<Longrightarrow> antilinear g \<Longrightarrow> antilinear (g o f)"
  apply (rule antilinearI)
   apply (simp add: additive.add complex_vector.linear_add antilinear_def)
  by (simp add: complex_vector.linear_scale antilinear.scaleC)

locale bounded_antilinear = antilinear f for f :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector" +
  assumes bounded: "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"

lemma bounded_antilinearI:
  assumes \<open>\<And>b1 b2. f (b1 + b2) = f b1 + f b2\<close>
  assumes \<open>\<And>r b. f (r *\<^sub>C b) = cnj r *\<^sub>C f b\<close>
  assumes \<open>\<forall>x. norm (f x) \<le> norm x * K\<close>
  shows "bounded_antilinear f"
  using assms by (auto intro!: exI bounded_antilinear.intro antilinearI simp: bounded_antilinear_axioms_def)

sublocale bounded_antilinear \<subseteq> real: bounded_linear
  \<comment> \<open>Gives access to all lemmas from \<^locale>\<open>linear\<close> using prefix \<open>real.\<close>\<close>
  apply standard by (fact bounded)

lemma (in bounded_antilinear) bounded_linear: "bounded_linear f"
  by (fact real.bounded_linear)

lemma (in bounded_antilinear) antilinear: "antilinear f"
  by (fact antilinear_axioms)

lemma bounded_antilinear_intro:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>r x. f (scaleC r x) = scaleC (cnj r) (f x)"
    and "\<And>x. norm (f x) \<le> norm x * K"
  shows "bounded_antilinear f"
  by standard (blast intro: assms)+

lemma bounded_antilinear_0[simp]: \<open>bounded_antilinear (\<lambda>_. 0)\<close>
  by (auto intro!: bounded_antilinearI[where K=0])

lemma bounded_antilinear_0'[simp]: \<open>bounded_antilinear 0\<close>
  by (auto intro!: bounded_antilinearI[where K=0])

lemma cnj_bounded_antilinear[simp]: "bounded_antilinear cnj"
  apply (rule bounded_antilinear_intro [where K = 1])
  by auto

lemma bounded_antilinear_o_bounded_antilinear:
  assumes "bounded_antilinear f"
    and "bounded_antilinear g"
  shows "bounded_clinear (\<lambda>x. f (g x))"
proof
  interpret f: bounded_antilinear f by fact
  interpret g: bounded_antilinear g by fact
  fix b1 b2 b r
  show "f (g (b1 + b2)) = f (g b1) + f (g b2)"
    by (simp add: f.add g.add)
  show "f (g (r *\<^sub>C b)) = r *\<^sub>C f (g b)"
    by (simp add: f.scaleC g.scaleC)
  have "bounded_linear (\<lambda>x. f (g x))"
    using f.bounded_linear g.bounded_linear by (rule bounded_linear_compose)
  then show "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
    by (rule bounded_linear.bounded)
qed

lemma bounded_antilinear_o_bounded_antilinear':
  assumes "bounded_antilinear f"
    and "bounded_antilinear g"
  shows "bounded_clinear (g o f)"
  using assms by (simp add: o_def bounded_antilinear_o_bounded_antilinear)

lemma bounded_antilinear_o_bounded_clinear:
  assumes "bounded_antilinear f"
    and "bounded_clinear g"
  shows "bounded_antilinear (\<lambda>x. f (g x))"
proof
  interpret f: bounded_antilinear f by fact
  interpret g: bounded_clinear g by fact
  show "f (g (x + y)) = f (g x) + f (g y)" for x y
    by (simp only: f.add g.add)
  show "f (g (scaleC r x)) = scaleC (cnj r) (f (g x))" for r x
    by (simp add: f.scaleC g.scaleC)
  have "bounded_linear (\<lambda>x. f (g x))"
    using f.bounded_linear g.bounded_linear by (rule bounded_linear_compose)
  then show "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
    by (rule bounded_linear.bounded)
qed

lemma bounded_antilinear_o_bounded_clinear':
  assumes "bounded_clinear f"
    and "bounded_antilinear g"
  shows "bounded_antilinear (g o f)"
  using assms by (simp add: o_def bounded_antilinear_o_bounded_clinear)

lemma bounded_clinear_o_bounded_antilinear:
  assumes "bounded_clinear f"
    and "bounded_antilinear g"
  shows "bounded_antilinear (\<lambda>x. f (g x))"
proof
  interpret f: bounded_clinear f by fact
  interpret g: bounded_antilinear g by fact
  show "f (g (x + y)) = f (g x) + f (g y)" for x y
    by (simp only: f.add g.add)
  show "f (g (scaleC r x)) = scaleC (cnj r) (f (g x))" for r x
    using f.scaleC g.scaleC by fastforce
  have "bounded_linear (\<lambda>x. f (g x))"
    using f.bounded_linear g.bounded_linear by (rule bounded_linear_compose)
  then show "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
    by (rule bounded_linear.bounded)
qed

lemma bounded_clinear_o_bounded_antilinear':
  assumes "bounded_antilinear f"
    and "bounded_clinear g"
  shows "bounded_antilinear (g o f)"
  using assms by (simp add: o_def bounded_clinear_o_bounded_antilinear)

lemma bij_clinear_imp_inv_clinear: "clinear (inv f)"
  if a1: "clinear f" and a2: "bij f"
proof
  fix b1 b2 r b
  show "inv f (b1 + b2) = inv f b1 + inv f b2"
    by (simp add: a1 a2 bij_is_inj bij_is_surj complex_vector.linear_add inv_f_eq surj_f_inv_f)
  show "inv f (r *\<^sub>C b) = r *\<^sub>C inv f b"
    using that
    by (smt bij_inv_eq_iff clinear_def complex_vector.linear_scale)
qed


locale bounded_sesquilinear =
  fixes
    prod :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector \<Rightarrow> 'c::complex_normed_vector"
      (infixl \<open>**\<close> 70)
  assumes add_left: "prod (a + a') b = prod a b + prod a' b"
    and add_right: "prod a (b + b') = prod a b + prod a b'"
    and scaleC_left: "prod (r *\<^sub>C a) b = (cnj r) *\<^sub>C (prod a b)"
    and scaleC_right: "prod a (r *\<^sub>C b) = r *\<^sub>C (prod a b)"
    and bounded: "\<exists>K. \<forall>a b. norm (prod a b) \<le> norm a * norm b * K"

sublocale bounded_sesquilinear \<subseteq> real: bounded_bilinear
  \<comment> \<open>Gives access to all lemmas from \<^locale>\<open>linear\<close> using prefix \<open>real.\<close>\<close>
  apply standard
  by (auto simp: add_left add_right scaleC_left scaleC_right bounded scaleR_scaleC)

lemma (in bounded_sesquilinear) bounded_bilinear[simp]: "bounded_bilinear prod"
  by intro_locales

lemma (in bounded_sesquilinear) bounded_antilinear_left: "bounded_antilinear (\<lambda>a. prod a b)"
  apply standard
    apply (auto simp add: scaleC_left add_left)
  by (metis ab_semigroup_mult_class.mult_ac(1) bounded)

lemma (in bounded_sesquilinear) bounded_clinear_right: "bounded_clinear (\<lambda>b. prod a b)"
  apply standard
    apply (auto simp add: scaleC_right add_right)
  by (metis bounded mult.assoc mult.left_commute)

lemma (in bounded_sesquilinear) comp1:
  assumes \<open>bounded_clinear g\<close>
  shows \<open>bounded_sesquilinear (\<lambda>x. prod (g x))\<close>
proof
  interpret bounded_clinear g by fact
  fix a a' b b' r
  show "prod (g (a + a')) b = prod (g a) b + prod (g a') b"
    by (simp add: add add_left)
  show "prod (g a) (b + b') = prod (g a) b + prod (g a) b'"
    by (simp add: add add_right)
  show "prod (g (r *\<^sub>C a)) b = cnj r *\<^sub>C prod (g a) b"
    by (simp add: scaleC scaleC_left)
  show "prod (g a) (r *\<^sub>C b) = r *\<^sub>C prod (g a) b"
    by (simp add: scaleC_right)
  interpret bi: bounded_bilinear \<open>(\<lambda>x. prod (g x))\<close>
    by (simp add: bounded_linear real.comp1)
  show "\<exists>K. \<forall>a b. norm (prod (g a) b) \<le> norm a * norm b * K"
    using bi.bounded by blast
qed

lemma (in bounded_sesquilinear) comp2:
  assumes \<open>bounded_clinear g\<close>
  shows \<open>bounded_sesquilinear (\<lambda>x y. prod x (g y))\<close>
proof
  interpret bounded_clinear g by fact
  fix a a' b b' r
  show "prod (a + a') (g b) = prod a (g b) + prod a' (g b)"
    by (simp add: add add_left)
  show "prod a (g (b + b')) = prod a (g b) + prod a (g b')"
    by (simp add: add add_right)
  show "prod (r *\<^sub>C a) (g b) = cnj r *\<^sub>C prod a (g b)"
    by (simp add: scaleC scaleC_left)
  show "prod a (g (r *\<^sub>C b)) = r *\<^sub>C prod a (g b)"
    by (simp add: scaleC scaleC_right)
  interpret bi: bounded_bilinear \<open>(\<lambda>x y. prod x (g y))\<close>
    apply (rule bounded_bilinear.flip)
    using _ bounded_linear apply (rule bounded_bilinear.comp1)
    using bounded_bilinear by (rule bounded_bilinear.flip)
  show "\<exists>K. \<forall>a b. norm (prod a (g b)) \<le> norm a * norm b * K"
    using bi.bounded by blast
qed

lemma (in bounded_sesquilinear) comp: "bounded_clinear f \<Longrightarrow> bounded_clinear g \<Longrightarrow> bounded_sesquilinear (\<lambda>x y. prod (f x) (g y))"
  using comp1 bounded_sesquilinear.comp2 by auto

lemma bounded_clinear_const_scaleR:
  fixes c :: real
  assumes \<open>bounded_clinear f\<close>
  shows \<open>bounded_clinear (\<lambda> x. c *\<^sub>R f x )\<close>
proof-
  have  \<open>bounded_clinear (\<lambda> x. (complex_of_real c) *\<^sub>C f x )\<close>
    by (simp add: assms bounded_clinear_const_scaleC)
  thus ?thesis
    by (simp add: scaleR_scaleC)
qed

lemma bounded_linear_bounded_clinear:
  \<open>bounded_linear A \<Longrightarrow> \<forall>c x. A (c *\<^sub>C x) = c *\<^sub>C A x \<Longrightarrow> bounded_clinear A\<close>
  apply standard
  by (simp_all add: linear_simps bounded_linear.bounded)

lemma comp_bounded_clinear:
  fixes  A :: \<open>'b::complex_normed_vector \<Rightarrow> 'c::complex_normed_vector\<close>
    and B :: \<open>'a::complex_normed_vector \<Rightarrow> 'b\<close>
  assumes \<open>bounded_clinear A\<close> and \<open>bounded_clinear B\<close>
  shows \<open>bounded_clinear (A \<circ> B)\<close>
  by (metis clinear_compose assms(1) assms(2) bounded_clinear_axioms_def bounded_clinear_compose bounded_clinear_def o_def)


lemma bounded_sesquilinear_add:
  \<open>bounded_sesquilinear (\<lambda> x y. A x y + B x y)\<close> if \<open>bounded_sesquilinear A\<close> and \<open>bounded_sesquilinear B\<close>
proof
  fix a a' :: 'a and b b' :: 'b and r :: complex
  show "A (a + a') b + B (a + a') b = (A a b + B a b) + (A a' b + B a' b)"
    by (simp add: bounded_sesquilinear.add_left that(1) that(2))
  show \<open>A a (b + b') + B a (b + b') = (A a b + B a b) + (A a b' + B a b')\<close>
    by (simp add: bounded_sesquilinear.add_right that(1) that(2))
  show \<open>A (r *\<^sub>C a) b + B (r *\<^sub>C a) b = cnj r *\<^sub>C (A a b + B a b)\<close>
    by (simp add: bounded_sesquilinear.scaleC_left scaleC_add_right that(1) that(2))
  show \<open>A a (r *\<^sub>C b) + B a (r *\<^sub>C b) = r *\<^sub>C (A a b + B a b)\<close>
    by (simp add: bounded_sesquilinear.scaleC_right scaleC_add_right that(1) that(2))
  show \<open>\<exists>K. \<forall>a b. norm (A a b + B a b) \<le> norm a * norm b * K\<close>
  proof-
    have \<open>\<exists> KA. \<forall> a b. norm (A a b) \<le> norm a * norm b * KA\<close>
      by (simp add: bounded_sesquilinear.bounded that(1))
    then obtain KA where \<open>\<forall> a b. norm (A a b) \<le> norm a * norm b * KA\<close>
      by blast
    have \<open>\<exists> KB. \<forall> a b. norm (B a b) \<le> norm a * norm b * KB\<close>
      by (simp add: bounded_sesquilinear.bounded that(2))
    then obtain KB where \<open>\<forall> a b. norm (B a b) \<le> norm a * norm b * KB\<close>
      by blast
    have \<open>norm (A a b + B a b) \<le> norm a * norm b * (KA + KB)\<close>
      for a b
    proof-
      have \<open>norm (A a b + B a b) \<le> norm (A a b) +  norm (B a b)\<close>
        using norm_triangle_ineq by blast
      also have \<open>\<dots> \<le> norm a * norm b * KA + norm a * norm b * KB\<close>
        using  \<open>\<forall> a b. norm (A a b) \<le> norm a * norm b * KA\<close>
          \<open>\<forall> a b. norm (B a b) \<le> norm a * norm b * KB\<close>
        using add_mono by blast
      also have \<open>\<dots>=  norm a * norm b * (KA + KB)\<close>
        by (simp add: mult.commute ring_class.ring_distribs(2))
      finally show ?thesis
        by blast
    qed
    thus ?thesis by blast
  qed
qed

lemma bounded_sesquilinear_uminus:
  \<open>bounded_sesquilinear (\<lambda> x y. - A x y)\<close> if \<open>bounded_sesquilinear A\<close>
proof
  fix a a' :: 'a and b b' :: 'b and r :: complex
  show "- A (a + a') b = (- A a b) + (- A a' b)"
    by (simp add: bounded_sesquilinear.add_left that)
  show \<open>- A a (b + b') = (- A a b) + (- A a b')\<close>
    by (simp add: bounded_sesquilinear.add_right that)
  show \<open>- A (r *\<^sub>C a) b = cnj r *\<^sub>C (- A a b)\<close>
    by (simp add: bounded_sesquilinear.scaleC_left that)
  show \<open>- A a (r *\<^sub>C b) = r *\<^sub>C (- A a b)\<close>
    by (simp add: bounded_sesquilinear.scaleC_right that)
  show \<open>\<exists>K. \<forall>a b. norm (- A a b) \<le> norm a * norm b * K\<close>
  proof-
    have \<open>\<exists> KA. \<forall> a b. norm (A a b) \<le> norm a * norm b * KA\<close>
      by (simp add: bounded_sesquilinear.bounded that(1))
    then obtain KA where \<open>\<forall> a b. norm (A a b) \<le> norm a * norm b * KA\<close>
      by blast
    have \<open>norm (- A a b) \<le> norm a * norm b * KA\<close>
      for a b
      by (simp add: \<open>\<forall>a b. norm (A a b) \<le> norm a * norm b * KA\<close>)
    thus ?thesis by blast
  qed
qed

lemma bounded_sesquilinear_diff:
  \<open>bounded_sesquilinear (\<lambda> x y. A x y - B x y)\<close> if \<open>bounded_sesquilinear A\<close> and \<open>bounded_sesquilinear B\<close>
proof -
  have \<open>bounded_sesquilinear (\<lambda> x y. - B x y)\<close>
    using that(2) by (rule bounded_sesquilinear_uminus)
  then have \<open>bounded_sesquilinear (\<lambda> x y. A x y + (- B x y))\<close>
    using that(1) by (rule bounded_sesquilinear_add[rotated])
  then show ?thesis
    by auto
qed

lemmas isCont_scaleC [simp] =
  bounded_bilinear.isCont [OF bounded_cbilinear_scaleC[THEN bounded_cbilinear.bounded_bilinear]]

lemma bounded_sesquilinear_0[simp]: \<open>bounded_sesquilinear (\<lambda>_ _.0)\<close>
  by (auto intro!: bounded_sesquilinear.intro exI[where x=0])

lemma bounded_sesquilinear_0'[simp]: \<open>bounded_sesquilinear 0\<close>
  by (auto intro!: bounded_sesquilinear.intro exI[where x=0])

lemma bounded_sesquilinear_apply_bounded_clinear: \<open>bounded_clinear (f x)\<close> if \<open>bounded_sesquilinear f\<close>
proof -
  interpret f: bounded_sesquilinear f
    by (fact that)
  from f.bounded obtain K where \<open>norm (f a b) \<le> norm a * norm b * K\<close> for a b
    by auto
  then show ?thesis
    by (auto intro!: bounded_clinearI[where K=\<open>norm x * K\<close>] 
        simp add: f.add_right f.scaleC_right mult.commute mult.left_commute)
qed

lemma antilinear_diff:
  assumes \<open>antilinear f\<close> and \<open>antilinear g\<close>
  shows \<open>antilinear (\<lambda>x. f x - g x)\<close>
  apply (rule antilinearI)
   apply (metis add_diff_add additive.add antilinear_def assms(1,2))
  by (simp add: antilinear.scaleC assms(1,2) scaleC_right.diff)

subsection \<open>Misc 2\<close>

lemma summable_on_scaleC_left [intro]:
  fixes c :: \<open>'a :: complex_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f summable_on A"
  shows   "(\<lambda>x. f x *\<^sub>C c) summable_on A"
  apply (cases \<open>c \<noteq> 0\<close>)
   apply (subst asm_rl[of \<open>(\<lambda>x. f x *\<^sub>C c) = (\<lambda>y. y *\<^sub>C c) o f\<close>], simp add: o_def)
   apply (rule summable_on_comm_additive)
  using assms by (auto simp add: scaleC_left.additive_axioms)

lemma summable_on_scaleC_right [intro]:
  fixes f :: \<open>'a \<Rightarrow> 'b :: complex_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f summable_on A"
  shows   "(\<lambda>x. c *\<^sub>C f x) summable_on A"
  apply (cases \<open>c \<noteq> 0\<close>)
   apply (subst asm_rl[of \<open>(\<lambda>x. c *\<^sub>C f x) = (\<lambda>y. c *\<^sub>C y) o f\<close>], simp add: o_def)
   apply (rule summable_on_comm_additive)
  using assms by (auto simp add: scaleC_right.additive_axioms)

lemma infsum_scaleC_left:
  fixes c :: \<open>'a :: complex_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f summable_on A"
  shows   "infsum (\<lambda>x. f x *\<^sub>C c) A = infsum f A *\<^sub>C c"
  apply (cases \<open>c \<noteq> 0\<close>)
   apply (subst asm_rl[of \<open>(\<lambda>x. f x *\<^sub>C c) = (\<lambda>y. y *\<^sub>C c) o f\<close>], simp add: o_def)
   apply (rule infsum_comm_additive)
  using assms by (auto simp add: scaleC_left.additive_axioms)

lemma infsum_scaleC_right:
  fixes f :: \<open>'a \<Rightarrow> 'b :: complex_normed_vector\<close>
  shows   "infsum (\<lambda>x. c *\<^sub>C f x) A = c *\<^sub>C infsum f A"
proof -
  consider (summable) \<open>f summable_on A\<close> | (c0) \<open>c = 0\<close> | (not_summable) \<open>\<not> f summable_on A\<close> \<open>c \<noteq> 0\<close>
    by auto
  then show ?thesis
  proof cases
    case summable
    then show ?thesis
      apply (subst asm_rl[of \<open>(\<lambda>x. c *\<^sub>C f x) = (\<lambda>y. c *\<^sub>C y) o f\<close>], simp add: o_def)
      apply (rule infsum_comm_additive)
      using summable by (auto simp add: scaleC_right.additive_axioms)
  next
    case c0
    then show ?thesis by auto
  next
    case not_summable
    have \<open>\<not> (\<lambda>x. c *\<^sub>C f x) summable_on A\<close>
    proof (rule notI)
      assume \<open>(\<lambda>x. c *\<^sub>C f x) summable_on A\<close>
      then have \<open>(\<lambda>x. inverse c *\<^sub>C c *\<^sub>C f x) summable_on A\<close>
        using summable_on_scaleC_right by blast
      then have \<open>f summable_on A\<close>
        using not_summable by auto
      with not_summable show False
        by simp
    qed
    then show ?thesis
      by (simp add: infsum_not_exists not_summable(1)) 
  qed
qed

lemma has_sum_scaleC_right:
  fixes f :: \<open>'a \<Rightarrow> 'b :: complex_normed_vector\<close>
  assumes \<open>(f has_sum s) A\<close>
  shows \<open>((\<lambda>x. c *\<^sub>C f x) has_sum c *\<^sub>C s) A\<close>
  apply (rule has_sum_bounded_clinear[where h=\<open>(*\<^sub>C) c\<close>])
  using bounded_clinear_scaleC_right assms by auto


lemmas sums_of_complex = bounded_linear.sums [OF bounded_clinear_of_complex[THEN bounded_clinear.bounded_linear]]
lemmas summable_of_complex = bounded_linear.summable [OF bounded_clinear_of_complex[THEN bounded_clinear.bounded_linear]]
lemmas suminf_of_complex = bounded_linear.suminf [OF bounded_clinear_of_complex[THEN bounded_clinear.bounded_linear]]

lemmas sums_scaleC_left = bounded_linear.sums[OF bounded_clinear_scaleC_left[THEN bounded_clinear.bounded_linear]]
lemmas summable_scaleC_left = bounded_linear.summable[OF bounded_clinear_scaleC_left[THEN bounded_clinear.bounded_linear]]
lemmas suminf_scaleC_left = bounded_linear.suminf[OF bounded_clinear_scaleC_left[THEN bounded_clinear.bounded_linear]]

lemmas sums_scaleC_right = bounded_linear.sums[OF bounded_clinear_scaleC_right[THEN bounded_clinear.bounded_linear]]
lemmas summable_scaleC_right = bounded_linear.summable[OF bounded_clinear_scaleC_right[THEN bounded_clinear.bounded_linear]]
lemmas suminf_scaleC_right = bounded_linear.suminf[OF bounded_clinear_scaleC_right[THEN bounded_clinear.bounded_linear]]

lemma closed_scaleC:
  fixes S::\<open>'a::complex_normed_vector set\<close> and a :: complex
  assumes \<open>closed S\<close>
  shows \<open>closed ((*\<^sub>C) a ` S)\<close>
proof (cases \<open>a = 0\<close>)
  case True
  then show ?thesis
    apply (cases \<open>S = {}\<close>)
    by (auto simp: image_constant)
next
  case False
  then have \<open>(*\<^sub>C) a ` S = (*\<^sub>C) (inverse a) -` S\<close>
    by (auto simp add: rev_image_eqI)
  moreover have \<open>closed ((*\<^sub>C) (inverse a) -` S)\<close>
    by (simp add: assms continuous_closed_vimage)
  ultimately show ?thesis
    by simp
qed

lemma closure_scaleC:
  fixes S::\<open>'a::complex_normed_vector set\<close>
  shows \<open>closure ((*\<^sub>C) a ` S) = (*\<^sub>C) a ` closure S\<close>
proof
  have \<open>closed (closure S)\<close>
    by simp
  show "closure ((*\<^sub>C) a ` S) \<subseteq> (*\<^sub>C) a ` closure S"
    by (simp add: closed_scaleC closure_minimal closure_subset image_mono)

  have "x \<in> closure ((*\<^sub>C) a ` S)"
    if "x \<in> (*\<^sub>C) a ` closure S"
    for x :: 'a
  proof-
    obtain t where \<open>x = ((*\<^sub>C) a) t\<close> and \<open>t \<in> closure S\<close>
      using \<open>x \<in> (*\<^sub>C) a ` closure S\<close> by auto
    have \<open>\<exists>s. (\<forall>n. s n \<in> S) \<and> s \<longlonglongrightarrow> t\<close>
      using \<open>t \<in> closure S\<close> Elementary_Topology.closure_sequential
      by blast
    then obtain s where \<open>\<forall>n. s n \<in> S\<close> and \<open>s \<longlonglongrightarrow> t\<close>
      by blast
    have \<open>(\<forall> n. scaleC a (s n) \<in> ((*\<^sub>C) a ` S))\<close>
      using \<open>\<forall>n. s n \<in> S\<close> by blast
    moreover have \<open>(\<lambda> n. scaleC a (s n)) \<longlonglongrightarrow> x\<close>
    proof-
      have \<open>isCont (scaleC a) t\<close>
        by simp
      thus ?thesis
        using  \<open>s \<longlonglongrightarrow> t\<close>  \<open>x = ((*\<^sub>C) a) t\<close>
        by (simp add: isCont_tendsto_compose)
    qed
    ultimately show ?thesis using Elementary_Topology.closure_sequential
      by metis
  qed
  thus "(*\<^sub>C) a ` closure S \<subseteq> closure ((*\<^sub>C) a ` S)" by blast
qed

lemma onorm_scalarC:
  fixes f :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector\<close>
  assumes a1: \<open>bounded_clinear f\<close>
  shows  \<open>onorm (\<lambda> x. r *\<^sub>C (f x)) = (cmod r) * onorm f\<close>
proof-
  have \<open>(norm (f x)) / norm x \<le> onorm f\<close>
    for x
    using a1
    by (simp add: bounded_clinear.bounded_linear le_onorm)
  hence t2: \<open>bdd_above {(norm (f x)) / norm x | x. True}\<close>
    by fastforce
  have \<open>continuous_on UNIV ( (*) w ) \<close>
    for w::real
    by simp
  hence \<open>isCont ( ((*) (cmod r)) ) x\<close>
    for x
    by simp
  hence t3: \<open>continuous (at_left (Sup {(norm (f x)) / norm x | x. True})) ((*) (cmod r))\<close>
    using Elementary_Topology.continuous_at_imp_continuous_within
    by blast
  have \<open>{(norm (f x)) / norm x | x. True} \<noteq> {}\<close>
    by blast
  moreover have \<open>mono ((*) (cmod r))\<close>
    by (simp add: monoI ordered_comm_semiring_class.comm_mult_left_mono)
  ultimately have \<open>Sup {((*) (cmod r)) ((norm (f x)) / norm x) | x. True}
         = ((*) (cmod r)) (Sup {(norm (f x)) / norm x | x. True})\<close>
    using t2 t3
    by (simp add:  continuous_at_Sup_mono full_SetCompr_eq image_image)
  hence  \<open>Sup {(cmod r) * ((norm (f x)) / norm x) | x. True}
         = (cmod r) * (Sup {(norm (f x)) / norm x | x. True})\<close>
    by blast
  moreover have \<open>Sup {(cmod r) * ((norm (f x)) / norm x) | x. True}
                = (SUP x. cmod r * norm (f x) / norm x)\<close>
    by (simp add: full_SetCompr_eq)
  moreover have \<open>(Sup {(norm (f x)) / norm x | x. True})
                = (SUP x. norm (f x) / norm x)\<close>
    by (simp add: full_SetCompr_eq)
  ultimately have t1: "(SUP x. cmod r * norm (f x) / norm x)
      = cmod r * (SUP x. norm (f x) / norm x)"
    by simp
  have \<open>onorm (\<lambda> x. r *\<^sub>C (f x)) = (SUP x. norm ( (\<lambda> t. r *\<^sub>C (f t)) x) / norm x)\<close>
    by (simp add: onorm_def)
  hence \<open>onorm (\<lambda> x. r *\<^sub>C (f x)) = (SUP x. (cmod r) * (norm (f x)) / norm x)\<close>
    by simp
  also have \<open>... = (cmod r) * (SUP x. (norm (f x)) / norm x)\<close>
    using t1.
  finally show ?thesis
    by (simp add: onorm_def)
qed

lemma onorm_scaleC_left_lemma:
  fixes f :: "'a::complex_normed_vector"
  assumes r: "bounded_clinear r"
  shows "onorm (\<lambda>x. r x *\<^sub>C f) \<le> onorm r * norm f"
proof (rule onorm_bound)
  fix x
  have "norm (r x *\<^sub>C f) = norm (r x) * norm f"
    by simp
  also have "\<dots> \<le> onorm r * norm x * norm f"
    by (simp add: bounded_clinear.bounded_linear mult.commute mult_left_mono onorm r)
  finally show "norm (r x *\<^sub>C f) \<le> onorm r * norm f * norm x"
    by (simp add: ac_simps)
  show "0 \<le> onorm r * norm f"
    by (simp add: bounded_clinear.bounded_linear onorm_pos_le r)
qed

lemma onorm_scaleC_left:
  fixes f :: "'a::complex_normed_vector"
  assumes f: "bounded_clinear r"
  shows "onorm (\<lambda>x. r x *\<^sub>C f) = onorm r * norm f"
proof (cases "f = 0")
  assume "f \<noteq> 0"
  show ?thesis
  proof (rule order_antisym)
    show "onorm (\<lambda>x. r x *\<^sub>C f) \<le> onorm r * norm f"
      using f by (rule onorm_scaleC_left_lemma)
  next
    have bl1: "bounded_clinear (\<lambda>x. r x *\<^sub>C f)"
      by (metis bounded_clinear_scaleC_const f)
    have x1:"bounded_clinear (\<lambda>x. r x * norm f)"
      by (metis bounded_clinear_mult_const f)

    have "onorm r \<le> onorm (\<lambda>x. r x * complex_of_real (norm f)) / norm f"
      if "onorm r \<le> onorm (\<lambda>x. r x * complex_of_real (norm f)) * cmod (1 / complex_of_real (norm f))"
        and "f \<noteq> 0"
      using that
      by (smt (verit) divide_inverse mult_1 norm_divide norm_ge_zero norm_of_real of_real_1 of_real_eq_iff of_real_mult)
    hence "onorm r \<le> onorm (\<lambda>x. r x * norm f) * inverse (norm f)"
      using \<open>f \<noteq> 0\<close> onorm_scaleC_left_lemma[OF x1, of "inverse (norm f)"]
      by (simp add: inverse_eq_divide)
    also have "onorm (\<lambda>x. r x * norm f) \<le> onorm (\<lambda>x. r x *\<^sub>C f)"
    proof (rule onorm_bound)
      have "bounded_linear (\<lambda>x. r x *\<^sub>C f)"
        using bl1 bounded_clinear.bounded_linear by auto
      thus "0 \<le> onorm (\<lambda>x. r x *\<^sub>C f)"
        by (rule Operator_Norm.onorm_pos_le)
      show "cmod (r x * complex_of_real (norm f)) \<le> onorm (\<lambda>x. r x *\<^sub>C f) * norm x"
        for x :: 'b
        by (smt (verit) \<open>bounded_linear (\<lambda>x. r x *\<^sub>C f)\<close> norm_ge_zero norm_mult norm_of_real norm_scaleC onorm)
    qed
    finally show "onorm r * norm f \<le> onorm (\<lambda>x. r x *\<^sub>C f)"
      using \<open>f \<noteq> 0\<close>
      by (simp add: inverse_eq_divide pos_le_divide_eq mult.commute)
  qed
qed (simp add: onorm_zero)

lemma compact_scaleC:
  fixes s :: "'a::complex_normed_vector set"
  assumes "compact s"
  shows "compact (scaleC c ` s)"
  by (auto intro!: compact_continuous_image assms continuous_at_imp_continuous_on)

subsection \<open>Finite dimension and canonical basis\<close>

lemma vector_finitely_spanned:
  assumes \<open>z \<in> cspan T\<close>
  shows \<open>\<exists> S. finite S \<and> S \<subseteq> T \<and> z \<in> cspan S\<close>
proof-
  have \<open>\<exists> S r. finite S \<and> S \<subseteq> T \<and> z = (\<Sum>a\<in>S. r a *\<^sub>C a)\<close>
    using complex_vector.span_explicit[where b = "T"]
      assms by auto
  then obtain S r where \<open>finite S\<close> and \<open>S \<subseteq> T\<close> and \<open>z = (\<Sum>a\<in>S. r a *\<^sub>C a)\<close>
    by blast
  thus ?thesis
    by (meson complex_vector.span_scale complex_vector.span_sum complex_vector.span_superset subset_iff)
qed

setup \<open>Sign.add_const_constraint ("Complex_Vector_Spaces0.cindependent", SOME \<^typ>\<open>'a set \<Rightarrow> bool\<close>)\<close>
setup \<open>Sign.add_const_constraint (\<^const_name>\<open>cdependent\<close>, SOME \<^typ>\<open>'a set \<Rightarrow> bool\<close>)\<close>
setup \<open>Sign.add_const_constraint (\<^const_name>\<open>cspan\<close>, SOME \<^typ>\<open>'a set \<Rightarrow> 'a set\<close>)\<close>

class cfinite_dim = complex_vector +
  assumes cfinitely_spanned: "\<exists>S::'a set. finite S \<and> cspan S = UNIV"

class basis_enum = complex_vector +
  fixes canonical_basis :: \<open>'a list\<close>
    and canonical_basis_length :: \<open>'a itself \<Rightarrow> nat\<close>
  assumes distinct_canonical_basis[simp]:
    "distinct canonical_basis"
    and is_cindependent_set[simp]:
    "cindependent (set canonical_basis)"
    and is_generator_set[simp]:
    "cspan (set canonical_basis) = UNIV"
    and canonical_basis_length:
    \<open>canonical_basis_length TYPE('a) = length canonical_basis\<close>

setup \<open>Sign.add_const_constraint ("Complex_Vector_Spaces0.cindependent", SOME \<^typ>\<open>'a::complex_vector set \<Rightarrow> bool\<close>)\<close>
setup \<open>Sign.add_const_constraint (\<^const_name>\<open>cdependent\<close>, SOME \<^typ>\<open>'a::complex_vector set \<Rightarrow> bool\<close>)\<close>
setup \<open>Sign.add_const_constraint (\<^const_name>\<open>cspan\<close>, SOME \<^typ>\<open>'a::complex_vector set \<Rightarrow> 'a set\<close>)\<close>


instantiation complex :: basis_enum begin
definition "canonical_basis = [1::complex]"
definition \<open>canonical_basis_length (_::complex itself) = 1\<close>
instance
proof
  show "distinct (canonical_basis::complex list)"
    by (simp add: canonical_basis_complex_def)
  show "cindependent (set (canonical_basis::complex list))"
    unfolding canonical_basis_complex_def
    by auto
  show "cspan (set (canonical_basis::complex list)) = UNIV"
    unfolding canonical_basis_complex_def
    apply (auto simp add: cspan_raw_def vector_space_over_itself.span_Basis)
    by (metis complex_scaleC_def complex_vector.span_base complex_vector.span_scale cspan_raw_def insertI1 mult.right_neutral)
  show \<open>canonical_basis_length TYPE(complex) = length (canonical_basis :: complex list)\<close>
    by (simp add: canonical_basis_length_complex_def canonical_basis_complex_def)
qed
end

lemma cdim_UNIV_basis_enum[simp]: \<open>cdim (UNIV::'a::basis_enum set) = length (canonical_basis::'a list)\<close>
  apply (subst is_generator_set[symmetric])
  apply (subst complex_vector.dim_span_eq_card_independent)
   apply (rule is_cindependent_set)
  using distinct_canonical_basis distinct_card by blast

lemma finite_basis: "\<exists>basis::'a::cfinite_dim set. finite basis \<and> cindependent basis \<and> cspan basis = UNIV"
proof -
  from cfinitely_spanned
  obtain S :: \<open>'a set\<close> where \<open>finite S\<close> and \<open>cspan S = UNIV\<close>
    by auto
  from complex_vector.maximal_independent_subset
  obtain B :: \<open>'a set\<close> where \<open>B \<subseteq> S\<close> and \<open>cindependent B\<close> and \<open>S \<subseteq> cspan B\<close>
    by metis
  moreover have \<open>finite B\<close>
    using \<open>B \<subseteq> S\<close> \<open>finite S\<close>
    by (meson finite_subset)
  moreover have \<open>cspan B = UNIV\<close>
    using \<open>cspan S = UNIV\<close> \<open>S \<subseteq> cspan B\<close>
    by (metis complex_vector.span_eq top_greatest)
  ultimately show ?thesis
    by auto
qed

instance basis_enum \<subseteq> cfinite_dim
  apply intro_classes
  apply (rule exI[of _ \<open>set canonical_basis\<close>])
  using is_cindependent_set is_generator_set by auto

lemma cindependent_cfinite_dim_finite:
  assumes \<open>cindependent (S::'a::cfinite_dim set)\<close>
  shows \<open>finite S\<close>
  by (metis assms cfinitely_spanned complex_vector.independent_span_bound top_greatest)

lemma cfinite_dim_finite_subspace_basis:
  assumes \<open>csubspace X\<close>
  shows "\<exists>basis::'a::cfinite_dim set. finite basis \<and> cindependent basis \<and> cspan basis = X"
  by (meson assms cindependent_cfinite_dim_finite complex_vector.basis_exists complex_vector.span_subspace)


text \<open>The following auxiliary lemma (\<open>finite_span_complete_aux\<close>) shows more or less the same as \<open>finite_span_representation_bounded\<close>,
   \<open>finite_span_complete\<close> below (see there for an intuition about the mathematical
   content of the lemmas). However, there is one difference: Here we additionally assume here
   that there is a bijection rep/abs between a finite type \<^typ>\<open>'basis\<close> and the set $B$.
   This is needed to be able to use results about euclidean spaces that are formulated w.r.t.
   the type class \<^class>\<open>finite\<close>

   Since we anyway assume that $B$ is finite, this added assumption does not make the lemma
   weaker. However, we cannot derive the existence of \<^typ>\<open>'basis\<close> inside the proof
   (HOL does not support such reasoning). Therefore we have the type \<^typ>\<open>'basis\<close> as
   an explicit assumption and remove it using @{attribute internalize_sort} after the proof.\<close>

lemma finite_span_complete_aux:
  fixes b :: "'b::real_normed_vector" and B :: "'b set"
    and  rep :: "'basis::finite \<Rightarrow> 'b" and abs :: "'b \<Rightarrow> 'basis"
  assumes t: "type_definition rep abs B"
    and t1: "finite B" and t2: "b\<in>B" and t3: "independent B"
  shows "\<exists>D>0. \<forall>\<psi>. norm (representation B \<psi> b) \<le> norm \<psi> * D"
    and "complete (span B)"
proof -
  define repr  where "repr = real_vector.representation B"
  define repr' where "repr' \<psi> = Abs_euclidean_space (repr \<psi> o rep)" for \<psi>
  define comb  where "comb l = (\<Sum>b\<in>B. l b *\<^sub>R b)" for l
  define comb' where "comb' l = comb (Rep_euclidean_space l o abs)" for l

  have comb_cong: "comb x = comb y" if "\<And>z. z\<in>B \<Longrightarrow> x z = y z" for x y
    unfolding comb_def using that by auto
  have comb_repr[simp]: "comb (repr \<psi>) = \<psi>" if "\<psi> \<in> real_vector.span B" for \<psi>
    using \<open>comb \<equiv> \<lambda>l. \<Sum>b\<in>B. l b *\<^sub>R b\<close> local.repr_def real_vector.sum_representation_eq t1 t3 that
    by fastforce

  have w5:"(\<Sum>b | (b \<in> B \<longrightarrow> x b \<noteq> 0) \<and> b \<in> B. x b *\<^sub>R b) =
    (\<Sum>b\<in>B. x b *\<^sub>R b)" for x
    using \<open>finite B\<close>
    by (smt DiffD1 DiffD2 mem_Collect_eq real_vector.scale_eq_0_iff subset_eq sum.mono_neutral_left)
  have "representation B (\<Sum>b\<in>B. x b *\<^sub>R b) =  (\<lambda>b. if b \<in> B then x b else 0)"
    for x
  proof (rule real_vector.representation_eqI)
    show "independent B"
      by (simp add: t3)
    show "(\<Sum>b\<in>B. x b *\<^sub>R b) \<in> span B"
      by (meson real_vector.span_scale real_vector.span_sum real_vector.span_superset subset_iff)
    show "b \<in> B"
      if "(if b \<in> B then x b else 0) \<noteq> 0"
      for b :: 'b
      using that
      by meson
    show "finite {b. (if b \<in> B then x b else 0) \<noteq> 0}"
      using t1 by auto
    show "(\<Sum>b | (if b \<in> B then x b else 0) \<noteq> 0. (if b \<in> B then x b else 0) *\<^sub>R b) = (\<Sum>b\<in>B. x b *\<^sub>R b)"
      using w5
      by simp
  qed
  hence repr_comb[simp]: "repr (comb x) = (\<lambda>b. if b\<in>B then x b else 0)" for x
    unfolding repr_def comb_def.
  have repr_bad[simp]: "repr \<psi> = (\<lambda>_. 0)" if "\<psi> \<notin> real_vector.span B" for \<psi>
    unfolding repr_def using that
    by (simp add: real_vector.representation_def)
  have [simp]: "repr' \<psi> = 0" if "\<psi> \<notin> real_vector.span B" for \<psi>
    unfolding repr'_def repr_bad[OF that]
    apply transfer
    by auto
  have comb'_repr'[simp]: "comb' (repr' \<psi>) = \<psi>"
    if "\<psi> \<in> real_vector.span B" for \<psi>
  proof -
    have x1: "(repr \<psi> \<circ> rep \<circ> abs) z = repr \<psi> z"
      if "z \<in> B"
      for z
      unfolding o_def
      using t that type_definition.Abs_inverse by fastforce
    have "comb' (repr' \<psi>) = comb ((repr \<psi> \<circ> rep) \<circ> abs)"
      unfolding comb'_def repr'_def
      by (subst Abs_euclidean_space_inverse; simp)
    also have "\<dots> = comb (repr \<psi>)"
      using x1 comb_cong by blast
    also have "\<dots> = \<psi>"
      using that by simp
    finally show ?thesis by -
  qed

  have t1: "Abs_euclidean_space (Rep_euclidean_space t) = t"
    if "\<And>x. rep x \<in> B"
    for t::"'a euclidean_space"
    apply (subst Rep_euclidean_space_inverse)
    by simp
  have "Abs_euclidean_space
     (\<lambda>y. if rep y \<in> B
           then Rep_euclidean_space x y
           else 0) = x"
    for x
    using type_definition.Rep[OF t] apply simp
    using t1 by blast
  hence "Abs_euclidean_space
     (\<lambda>y. if rep y \<in> B
           then Rep_euclidean_space x (abs (rep y))
           else 0) = x"
    for x
    apply (subst type_definition.Rep_inverse[OF t])
    by simp
  hence repr'_comb'[simp]: "repr' (comb' x) = x" for x
    unfolding comb'_def repr'_def o_def
    by simp
  have sphere: "compact (sphere 0 d :: 'basis euclidean_space set)" for d
    using compact_sphere by blast
  have "complete (UNIV :: 'basis euclidean_space set)"
    by (simp add: complete_UNIV)


  have "(\<Sum>b\<in>B. (Rep_euclidean_space (x + y) \<circ> abs) b *\<^sub>R b) = (\<Sum>b\<in>B. (Rep_euclidean_space x \<circ> abs) b *\<^sub>R b) + (\<Sum>b\<in>B. (Rep_euclidean_space y \<circ> abs) b *\<^sub>R b)"
    for x :: "'basis euclidean_space"
      and y :: "'basis euclidean_space"
    apply (transfer fixing: abs)
    by (simp add: scaleR_add_left sum.distrib)
  moreover have "(\<Sum>b\<in>B. (Rep_euclidean_space (c *\<^sub>R x) \<circ> abs) b *\<^sub>R b) = c *\<^sub>R (\<Sum>b\<in>B. (Rep_euclidean_space x \<circ> abs) b *\<^sub>R b)"
    for c :: real
      and x :: "'basis euclidean_space"
    apply (transfer fixing: abs)
    by (simp add: real_vector.scale_sum_right)
  ultimately have blin_comb': "bounded_linear comb'"
    unfolding comb_def comb'_def
    by (rule bounded_linearI')
  hence "continuous_on X comb'" for X
    by (simp add: linear_continuous_on)
  hence "compact (comb' ` sphere 0 d)" for d
    using sphere
    by (rule compact_continuous_image)
  hence compact_norm_comb': "compact (norm ` comb' ` sphere 0 1)"
    using compact_continuous_image continuous_on_norm_id by blast
  have not0: "0 \<notin> norm ` comb' ` sphere 0 1"
  proof (rule ccontr, simp)
    assume "0 \<in> norm ` comb' ` sphere 0 1"
    then obtain x where nc0: "norm (comb' x) = 0" and x: "x \<in> sphere 0 1"
      by auto
    hence "comb' x = 0"
      by simp
    hence "repr' (comb' x) = 0"
      unfolding repr'_def o_def repr_def apply simp
      by (smt repr'_comb' blin_comb' dist_0_norm linear_simps(3) mem_sphere norm_zero x)
    hence "x = 0"
      by auto
    with x show False
      by simp
  qed

  have "closed (norm ` comb' ` sphere 0 1)"
    using compact_imp_closed compact_norm_comb' by blast
  moreover have "0 \<notin> norm ` comb' ` sphere 0 1"
    by (simp add: not0)
  ultimately have "\<exists>d>0. \<forall>x\<in>norm ` comb' ` sphere 0 1. d \<le> dist 0 x"
    by (meson separate_point_closed)

  then obtain d where d: "x\<in>norm ` comb' ` sphere 0 1 \<Longrightarrow> d \<le> dist 0 x"
    and "d > 0" for x
    by metis
  define D where "D = 1/d"
  hence "D > 0"
    using \<open>d>0\<close> unfolding D_def by auto
  have "x \<ge> d"
    if "x\<in>norm ` comb' ` sphere 0 1"
    for x
    using d that
    apply auto
    by fastforce
  hence *: "norm (comb' x) \<ge> d" if "norm x = 1" for x
    using that by auto
  have norm_comb': "norm (comb' x) \<ge> d * norm x" for x
  proof (cases "x=0")
    show "d * norm x \<le> norm (comb' x)"
      if "x = 0"
      using that
      by simp
    show "d * norm x \<le> norm (comb' x)"
      if "x \<noteq> 0"
      using that
      using *[of "(1/norm x) *\<^sub>R x"]
      unfolding linear_simps(5)[OF blin_comb']
      apply auto
      by (simp add: le_divide_eq)
  qed

  have *:  "norm (repr' \<psi>) \<le> norm \<psi> * D" for \<psi>
  proof (cases "\<psi> \<in> real_vector.span B")
    show "norm (repr' \<psi>) \<le> norm \<psi> * D"
      if "\<psi> \<in> span B"
      using that     unfolding D_def
      using norm_comb'[of "repr' \<psi>"] \<open>d>0\<close>
      by (simp_all add: linordered_field_class.mult_imp_le_div_pos mult.commute)

    show "norm (repr' \<psi>) \<le> norm \<psi> * D"
      if "\<psi> \<notin> span B"
      using that \<open>0 < D\<close> by auto
  qed

  hence "norm (Rep_euclidean_space (repr' \<psi>) (abs b)) \<le> norm \<psi> * D" for \<psi>
  proof -
    have "(Rep_euclidean_space (repr' \<psi>) (abs b)) = repr' \<psi> \<bullet> euclidean_space_basis_vector (abs b)"
      apply (transfer fixing: abs b)
      by auto
    also have "\<bar>\<dots>\<bar> \<le> norm (repr' \<psi>)"
      apply (rule Basis_le_norm)
      unfolding Basis_euclidean_space_def by simp
    also have "\<dots> \<le> norm \<psi> * D"
      using * by auto
    finally show ?thesis by simp
  qed
  hence "norm (repr \<psi> b) \<le> norm \<psi> * D" for \<psi>
    unfolding repr'_def
    by (smt \<open>comb' \<equiv> \<lambda>l. comb (Rep_euclidean_space l \<circ> abs)\<close>
        \<open>repr' \<equiv> \<lambda>\<psi>. Abs_euclidean_space (repr \<psi> \<circ> rep)\<close> comb'_repr' comp_apply norm_le_zero_iff
        repr_bad repr_comb)
  thus "\<exists>D>0. \<forall>\<psi>. norm (repr \<psi> b) \<le> norm \<psi> * D"
    using \<open>D>0\<close> by auto
  from \<open>d>0\<close>
  have complete_comb': "complete (comb' ` UNIV)"
  proof (rule complete_isometric_image)
    show "subspace (UNIV::'basis euclidean_space set)"
      by simp
    show "bounded_linear comb'"
      by (simp add: blin_comb')
    show "\<forall>x\<in>UNIV. d * norm x \<le> norm (comb' x)"
      by (simp add: norm_comb')
    show "complete (UNIV::'basis euclidean_space set)"
      by (simp add: \<open>complete UNIV\<close>)
  qed

  have range_comb': "comb' ` UNIV = real_vector.span B"
  proof (auto simp: image_def)
    show "comb' x \<in> real_vector.span B" for x
      by (metis comb'_def comb_cong comb_repr local.repr_def repr_bad repr_comb real_vector.representation_zero real_vector.span_zero)
  next
    fix \<psi> assume "\<psi> \<in> real_vector.span B"
    then obtain f where f: "comb f = \<psi>"
      apply atomize_elim
      unfolding span_finite[OF \<open>finite B\<close>] comb_def
      by auto
    define f' where "f' b = (if b\<in>B then f b else 0)" for b :: 'b
    have f': "comb f' = \<psi>"
      unfolding f[symmetric]
      apply (rule comb_cong)
      unfolding f'_def by simp
    define x :: "'basis euclidean_space" where "x = Abs_euclidean_space (f' o rep)"
    have "\<psi> = comb' x"
      by (metis (no_types, lifting) \<open>\<psi> \<in> span B\<close> \<open>repr' \<equiv> \<lambda>\<psi>. Abs_euclidean_space (repr \<psi> \<circ> rep)\<close>
          comb'_repr' f' fun.map_cong repr_comb t type_definition.Rep_range x_def)
    thus "\<exists>x. \<psi> = comb' x"
      by auto
  qed

  from range_comb' complete_comb'
  show "complete (real_vector.span B)"
    by simp
qed

lemma finite_span_complete[simp]:
  fixes A :: "'a::real_normed_vector set"
  assumes "finite A"
  shows "complete (span A)"
  text \<open>The span of a finite set is complete.\<close>
proof (cases "A \<noteq> {} \<and> A \<noteq> {0}")
  case True
  obtain B where
    BT: "real_vector.span B = real_vector.span A"
    and "independent B"
    and "finite B"
    by (meson True assms finite_subset real_vector.maximal_independent_subset real_vector.span_eq
        real_vector.span_superset subset_trans)

  have "B\<noteq>{}"
    apply (rule ccontr, simp)
    using BT True
    by (metis real_vector.span_superset real_vector.span_empty subset_singletonD)

(* The following generalizes finite_span_complete_aux to hold without the assumption
     that 'basis has type class finite *)
  {
    (* The type variable 'basisT must not be the same as the one used in finite_span_complete_aux,
       otherwise "internalize_sort" below fails *)
    assume "\<exists>(Rep :: 'basisT\<Rightarrow>'a) Abs. type_definition Rep Abs B"
    then obtain rep :: "'basisT \<Rightarrow> 'a" and abs :: "'a \<Rightarrow> 'basisT" where t: "type_definition rep abs B"
      by auto
    have basisT_finite: "class.finite TYPE('basisT)"
      apply intro_classes
      using \<open>finite B\<close> t
      by (metis (mono_tags, opaque_lifting) ex_new_if_finite finite_imageI image_eqI type_definition_def)
    note finite_span_complete_aux(2)[internalize_sort "'basis::finite"]
    note this[OF basisT_finite t]
  }
  note this[cancel_type_definition, OF \<open>B\<noteq>{}\<close> \<open>finite B\<close> _ \<open>independent B\<close>]
  hence "complete (real_vector.span B)"
    using \<open>B\<noteq>{}\<close> by auto
  thus "complete (real_vector.span A)"
    unfolding BT by simp
next
  case False
  thus ?thesis
    using complete_singleton by auto
qed

lemma finite_span_representation_bounded:
  fixes B :: "'a::real_normed_vector set"
  assumes "finite B" and "independent B"
  shows "\<exists>D>0. \<forall>\<psi> b. abs (representation B \<psi> b) \<le> norm \<psi> * D"

  text \<open>
  Assume $B$ is a finite linear independent set of vectors (in a real normed vector space).
  Let $\alpha^\psi_b$ be the coefficients of $\psi$ expressed as a linear combination over $B$.
  Then $\alpha$ is is uniformly cblinfun (i.e., $\lvert\alpha^\psi_b \leq D \lVert\psi\rVert\psi$
  for some $D$ independent of $\psi,b$).

  (This also holds when $b$ is not in the span of $B$ because of the way \<open>real_vector.representation\<close>
  is defined in this corner case.)\<close>

proof (cases "B\<noteq>{}")
  case True

(* The following generalizes finite_span_complete_aux to hold without the assumption
     that 'basis has type class finite *)
  define repr  where "repr = real_vector.representation B"
  {
    (* Step 1: Create a fake type definition by introducing a new type variable 'basis
               and then assuming the existence of the morphisms Rep/Abs to B
               This is then roughly equivalent to "typedef 'basis = B" *)
    (* The type variable 'basisT must not be the same as the one used in finite_span_complete_aux
       (I.e., we cannot call it 'basis) *)
    assume "\<exists>(Rep :: 'basisT\<Rightarrow>'a) Abs. type_definition Rep Abs B"
    then obtain rep :: "'basisT \<Rightarrow> 'a" and abs :: "'a \<Rightarrow> 'basisT" where t: "type_definition rep abs B"
      by auto
        (* Step 2: We show that our fake typedef 'basisT could be instantiated as type class finite *)
    have basisT_finite: "class.finite TYPE('basisT)"
      apply intro_classes
      using \<open>finite B\<close> t
      by (metis (mono_tags, opaque_lifting) ex_new_if_finite finite_imageI image_eqI type_definition_def)
        (* Step 3: We take the finite_span_complete_aux and remove the requirement that 'basis::finite
               (instead, a precondition "class.finite TYPE('basisT)" is introduced) *)
    note finite_span_complete_aux(1)[internalize_sort "'basis::finite"]
      (* Step 4: We instantiate the premises *)
    note this[OF basisT_finite t]
  }
    (* Now we have the desired fact, except that it still assumes that B is isomorphic to some type 'basis
     together with the assumption that there are morphisms between 'basis and B. 'basis and that premise
     are removed using cancel_type_definition
  *)
  note this[cancel_type_definition, OF True \<open>finite B\<close> _ \<open>independent B\<close>]

  hence d2:"\<exists>D. \<forall>\<psi>. D>0 \<and> norm (repr \<psi> b) \<le> norm \<psi> * D" if \<open>b\<in>B\<close> for b
    by (simp add: repr_def that True)
  have d1: " (\<And>b. b \<in> B \<Longrightarrow>
          \<exists>D. \<forall>\<psi>. 0 < D \<and> norm (repr \<psi> b) \<le> norm \<psi> * D) \<Longrightarrow>
    \<exists>D. \<forall>b \<psi>. b \<in> B \<longrightarrow>
               0 < D b \<and> norm (repr \<psi> b) \<le> norm \<psi> * D b"
    apply (rule choice) by auto
  then obtain D where D: "D b > 0 \<and> norm (repr \<psi> b) \<le> norm \<psi> * D b" if "b\<in>B" for b \<psi>
    apply atomize_elim
    using d2 by blast

  hence Dpos: "D b > 0" and Dbound: "norm (repr \<psi> b) \<le> norm \<psi> * D b"
    if "b\<in>B" for b \<psi>
    using that by auto
  define Dall where "Dall = Max (D`B)"
  have "Dall > 0"
    unfolding Dall_def using \<open>finite B\<close> \<open>B\<noteq>{}\<close> Dpos
    by (metis (mono_tags, lifting) Max_in finite_imageI image_iff image_is_empty)
  have "Dall \<ge> D b" if "b\<in>B" for b
    unfolding Dall_def using \<open>finite B\<close> that by auto
  with Dbound
  have "norm (repr \<psi> b) \<le> norm \<psi> * Dall" if "b\<in>B" for b \<psi>
    using that
    by (smt mult_left_mono norm_not_less_zero)
  moreover have "norm (repr \<psi> b) \<le> norm \<psi> * Dall" if "b\<notin>B" for b \<psi>
    unfolding repr_def using real_vector.representation_ne_zero True
    by (metis calculation empty_subsetI less_le_trans local.repr_def norm_ge_zero norm_zero not_less
        subsetI subset_antisym)
  ultimately show "\<exists>D>0. \<forall>\<psi> b. abs (repr \<psi> b) \<le> norm \<psi> * D"
    using \<open>Dall > 0\<close> real_norm_def by metis
next
  case False
  thus ?thesis
    unfolding repr_def using real_vector.representation_ne_zero[of B]
    using nice_ordered_field_class.linordered_field_no_ub by fastforce
qed

hide_fact finite_span_complete_aux


lemma finite_cspan_complete[simp]:
  fixes B :: "'a::complex_normed_vector set"
  assumes "finite B"
  shows "complete (cspan B)"
  by (simp add: assms cspan_as_span)

lemma finite_span_closed[simp]:
  fixes B :: "'a::real_normed_vector set"
  assumes "finite B"
  shows "closed (real_vector.span B)"
  by (simp add: assms complete_imp_closed)


lemma finite_cspan_closed[simp]:
  fixes S::\<open>'a::complex_normed_vector set\<close>
  assumes a1: \<open>finite S\<close>
  shows \<open>closed (cspan S)\<close>
  by (simp add: assms complete_imp_closed)

lemma closure_finite_cspan:
  fixes T::\<open>'a::complex_normed_vector set\<close>
  assumes \<open>finite T\<close>
  shows \<open>closure (cspan T) = cspan T\<close>
  by (simp add: assms)


lemma finite_cspan_crepresentation_bounded:
  fixes B :: "'a::complex_normed_vector set"
  assumes a1: "finite B" and a2: "cindependent B"
  shows "\<exists>D>0. \<forall>\<psi> b. cmod (crepresentation B \<psi> b) \<le> norm \<psi> * D"
proof -
  define B' where "B' = (B \<union> scaleC \<i> ` B)"
  have independent_B': "independent B'"
    using B'_def \<open>cindependent B\<close>
    by (simp add: real_independent_from_complex_independent a1)
  have "finite B'"
    unfolding B'_def using \<open>finite B\<close> by simp
  obtain D' where "D' > 0" and D': "norm (real_vector.representation B' \<psi> b) \<le> norm \<psi> * D'"
    for \<psi> b
    apply atomize_elim
    using independent_B' \<open>finite B'\<close>
    by (simp add: finite_span_representation_bounded)

  define D where "D = 2*D'"
  from \<open>D' > 0\<close> have \<open>D > 0\<close>
    unfolding D_def by simp
  have "norm (crepresentation B \<psi> b) \<le> norm \<psi> * D" for \<psi> b
  proof (cases "b\<in>B")
    case True
    have d3: "norm \<i> = 1"
      by simp

    have "norm (\<i> *\<^sub>C complex_of_real (real_vector.representation B' \<psi> (\<i> *\<^sub>C b)))
          = norm \<i> * norm (complex_of_real (real_vector.representation B' \<psi> (\<i> *\<^sub>C b)))"
      using norm_scaleC by blast
    also have "\<dots> = norm (complex_of_real (real_vector.representation B' \<psi> (\<i> *\<^sub>C b)))"
      using d3 by simp
    finally have d2:"norm (\<i> *\<^sub>C complex_of_real (real_vector.representation B' \<psi> (\<i> *\<^sub>C b)))
          = norm (complex_of_real (real_vector.representation B' \<psi> (\<i> *\<^sub>C b)))".
    have "norm (crepresentation B \<psi> b)
        = norm (complex_of_real (real_vector.representation B' \<psi> b)
            + \<i> *\<^sub>C complex_of_real (real_vector.representation B' \<psi> (\<i> *\<^sub>C b)))"
      by (simp add: B'_def True a1 a2 crepresentation_from_representation)
    also have "\<dots> \<le> norm (complex_of_real (real_vector.representation B' \<psi> b))
             + norm (\<i> *\<^sub>C complex_of_real (real_vector.representation B' \<psi> (\<i> *\<^sub>C b)))"
      using norm_triangle_ineq by blast
    also have "\<dots> = norm (complex_of_real (real_vector.representation B' \<psi> b))
                  + norm (complex_of_real (real_vector.representation B' \<psi> (\<i> *\<^sub>C b)))"
      using d2 by simp
    also have "\<dots> = norm (real_vector.representation B' \<psi> b)
                  + norm (real_vector.representation B' \<psi> (\<i> *\<^sub>C b))"
      by simp
    also have "\<dots> \<le> norm \<psi> * D' + norm \<psi> * D'"
      by (rule add_mono; rule D')
    also have "\<dots> \<le> norm \<psi> * D"
      unfolding D_def by linarith
    finally show ?thesis
      by auto
  next
    case False
    hence "crepresentation B \<psi> b = 0"
      using complex_vector.representation_ne_zero by blast
    thus ?thesis
      by (smt \<open>0 < D\<close> norm_ge_zero norm_zero split_mult_pos_le)
  qed
  with \<open>D > 0\<close>
  show ?thesis
    by auto
qed

lemma bounded_clinear_finite_dim[simp]:
  fixes f :: \<open>'a::{cfinite_dim,complex_normed_vector} \<Rightarrow> 'b::complex_normed_vector\<close>
  assumes \<open>clinear f\<close>
  shows \<open>bounded_clinear f\<close>
proof -
  include norm_syntax
  obtain basis :: \<open>'a set\<close> where b1: "complex_vector.span basis = UNIV"
    and b2: "cindependent basis"
    and b3:"finite basis"
    using finite_basis by auto
  have "\<exists>C>0. \<forall>\<psi> b. cmod (crepresentation basis \<psi> b) \<le> \<parallel>\<psi>\<parallel> * C"
    using finite_cspan_crepresentation_bounded[where B = basis] b2 b3 by blast
  then obtain C where s1: "cmod (crepresentation basis \<psi> b) \<le> \<parallel>\<psi>\<parallel> * C"
    and s2: "C > 0"
  for \<psi> b by blast
  define M where "M = C * (\<Sum>a\<in>basis. \<parallel>f a\<parallel>)"
  have "\<parallel>f x\<parallel> \<le> \<parallel>x\<parallel> * M"
    for x
  proof-
    define r where "r b = crepresentation basis x b" for b
    have x_span: "x \<in> complex_vector.span basis"
      by (simp add: b1)
    have f0: "v \<in> basis"
      if "r v \<noteq> 0" for v
      using complex_vector.representation_ne_zero r_def that by auto
    have w:"{a|a. r a \<noteq> 0} \<subseteq> basis"
      using f0 by blast
    hence f1: "finite {a|a. r a \<noteq> 0}"
      using b3 rev_finite_subset by auto
    have f2: "(\<Sum>a| r a \<noteq> 0. r a *\<^sub>C a) = x"
      unfolding r_def
      using b2 complex_vector.sum_nonzero_representation_eq x_span
        Collect_cong  by fastforce
    have g1: "(\<Sum>a\<in>basis. crepresentation basis x a *\<^sub>C a) = x"
      by (simp add: b2 b3 complex_vector.sum_representation_eq x_span)
    have f3: "(\<Sum>a\<in>basis. r a *\<^sub>C a) = x"
      unfolding r_def
      by (simp add: g1)
    hence "f x = f (\<Sum>a\<in>basis. r a *\<^sub>C a)"
      by simp
    also have "\<dots> = (\<Sum>a\<in>basis. r a *\<^sub>C f a)"
      by (smt (verit, ccfv_SIG) assms complex_vector.linear_scale complex_vector.linear_sum sum.cong)
    finally have "f x = (\<Sum>a\<in>basis. r a *\<^sub>C f a)".
    hence "\<parallel>f x\<parallel> = \<parallel>(\<Sum>a\<in>basis. r a *\<^sub>C f a)\<parallel>"
      by simp
    also have "\<dots> \<le> (\<Sum>a\<in>basis. \<parallel>r a *\<^sub>C f a\<parallel>)"
      by (simp add: sum_norm_le)
    also have "\<dots> \<le> (\<Sum>a\<in>basis. \<parallel>r a\<parallel> * \<parallel>f a\<parallel>)"
      by simp
    also have "\<dots> \<le> (\<Sum>a\<in>basis. \<parallel>x\<parallel> * C * \<parallel>f a\<parallel>)"
      using sum_mono s1 unfolding r_def
      by (simp add: sum_mono mult_right_mono)
    also have "\<dots> \<le> \<parallel>x\<parallel> * C * (\<Sum>a\<in>basis. \<parallel>f a\<parallel>)"
      using sum_distrib_left
      by (smt sum.cong)
    also have "\<dots> = \<parallel>x\<parallel> * M"
      unfolding M_def
      by linarith
    finally show ?thesis .
  qed
  thus ?thesis
    using assms bounded_clinear_def bounded_clinear_axioms_def by blast
qed

lemma summable_on_scaleR_left_converse:
  \<comment> \<open>This result has nothing to do with the bounded operator library but it
      uses @{thm [source] finite_span_closed} so it is proven here.\<close>
  fixes f :: \<open>'b \<Rightarrow> real\<close>
    and c :: \<open>'a :: real_normed_vector\<close>
  assumes \<open>c \<noteq> 0\<close>
  assumes \<open>(\<lambda>x. f x *\<^sub>R c) summable_on A\<close>
  shows \<open>f summable_on A\<close>
proof -
  define fromR toR T where \<open>fromR x = x *\<^sub>R c\<close> and \<open>toR = inv fromR\<close> and \<open>T = range fromR\<close> for x :: real
  have \<open>additive fromR\<close>
    by (simp add: fromR_def additive.intro scaleR_left_distrib)
  have \<open>inj fromR\<close>
    by (simp add: fromR_def \<open>c \<noteq> 0\<close> inj_def)
  have toR_fromR: \<open>toR (fromR x) = x\<close> for x
    by (simp add: \<open>inj fromR\<close> toR_def)
  have fromR_toR: \<open>fromR (toR x) = x\<close> if \<open>x \<in> T\<close> for x
    by (metis T_def f_inv_into_f that toR_def)

  have 1: \<open>sum (toR \<circ> (fromR \<circ> f)) F = toR (sum (fromR \<circ> f) F)\<close> if \<open>finite F\<close> for F
    by (simp add: o_def additive.sum[OF \<open>additive fromR\<close>, symmetric] toR_fromR)
  have 2: \<open>sum (fromR \<circ> f) F \<in> T\<close> if \<open>finite F\<close> for F
    by (simp add: o_def additive.sum[OF \<open>additive fromR\<close>, symmetric] T_def)
  have 3: \<open>(toR \<longlongrightarrow> toR x) (at x within T)\<close> for x
  proof (cases \<open>x \<in> T\<close>)
    case True
    have \<open>dist (toR y) (toR x) < e\<close> if \<open>y\<in>T\<close> \<open>e>0\<close> \<open>dist y x < e * norm c\<close> for e y
    proof -
      obtain x' y' where x: \<open>x = fromR x'\<close> and y: \<open>y = fromR y'\<close>
        using T_def True \<open>y \<in> T\<close> by blast
      have \<open>dist (toR y) (toR x) = dist (fromR (toR y)) (fromR (toR x)) / norm c\<close>
        by (auto simp: dist_real_def fromR_def \<open>c \<noteq> 0\<close>)
      also have \<open>\<dots> = dist y x / norm c\<close>
        using \<open>x\<in>T\<close> \<open>y\<in>T\<close> by (simp add: fromR_toR)
      also have \<open>\<dots> < e\<close>
        using \<open>dist y x < e * norm c\<close>
        by (simp add: divide_less_eq that(2))
      finally show ?thesis
        by (simp add: x y toR_fromR)
    qed
    then show ?thesis
      apply (auto simp: tendsto_iff at_within_def eventually_inf_principal eventually_nhds_metric)
      by (metis assms(1) div_0 divide_less_eq zero_less_norm_iff)
  next
    case False
    have \<open>T = span {c}\<close>
      by (simp add: T_def fromR_def span_singleton)
    then have \<open>closed T\<close>
      by simp
    with False have \<open>x \<notin> closure T\<close>
      by simp
    then have \<open>(at x within T) = bot\<close>
      by (rule not_in_closure_trivial_limitI)
    then show ?thesis
      by simp
  qed
  have 4: \<open>(fromR \<circ> f) summable_on A\<close>
    by (simp add: assms(2) fromR_def summable_on_cong)

  have \<open>(toR o (fromR o f)) summable_on A\<close>
    using 1 2 3 4 
    by (rule summable_on_comm_additive_general[where T=T])
  with toR_fromR
  show ?thesis
    by (auto simp: o_def)
qed

lemma infsum_scaleR_left:
  \<comment> \<open>This result has nothing to do with the bounded operator library but it
      uses @{thm [source] finite_span_closed} so it is proven here.

      It is a strengthening of @{thm [source] infsum_scaleR_left}.\<close>
  fixes c :: \<open>'a :: real_normed_vector\<close>
  shows "infsum (\<lambda>x. f x *\<^sub>R c) A = infsum f A *\<^sub>R c"
proof (cases \<open>f summable_on A\<close>)
  case True
  then show ?thesis 
   apply (subst asm_rl[of \<open>(\<lambda>x. f x *\<^sub>R c) = (\<lambda>y. y *\<^sub>R c) o f\<close>], simp add: o_def)
   apply (rule infsum_comm_additive)
  using True by (auto simp add: scaleR_left.additive_axioms)
next
  case False
  then have \<open>\<not> (\<lambda>x. f x *\<^sub>R c) summable_on A\<close> if \<open>c \<noteq> 0\<close>
    using summable_on_scaleR_left_converse[where A=A and f=f and c=c]
    using that by auto
  with False show ?thesis
    apply (cases \<open>c = 0\<close>)
    by (auto simp add: infsum_not_exists)
qed

lemma infsum_of_real: 
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>A. of_real (f x) :: 'b::{real_normed_vector, real_algebra_1}) = of_real (\<Sum>\<^sub>\<infinity>x\<in>A. f x)\<close>
  \<comment> \<open>This result has nothing to do with the bounded operator library but it
      uses @{thm [source] finite_span_closed} so it is proven here.\<close>
  unfolding of_real_def
  by (rule infsum_scaleR_left)


definition \<open>cfinite_dim S \<longleftrightarrow> (\<exists>B. finite B \<and> S \<subseteq> cspan B)\<close>

lemma cspan_finite_dim[intro]: \<open>cfinite_dim (cspan B)\<close> if \<open>finite B\<close>
  using cfinite_dim_def that by auto

lemma cfinite_dim_subspace_has_basis:
  assumes \<open>cfinite_dim S\<close> and \<open>csubspace S\<close>
  shows \<open>\<exists>B. finite B \<and> cindependent B \<and> cspan B = S\<close>
proof -
  obtain B where \<open>cindependent B\<close> and \<open>cspan B = S\<close>
    by (rule complex_vector.maximal_independent_subset[where V=S])
       (use \<open>csubspace S\<close> complex_vector.span_subspace in blast)
  from \<open>cfinite_dim S\<close>
  obtain C where \<open>finite C\<close> and \<open>S \<subseteq> cspan C\<close>
    using cfinite_dim_def by auto
  from \<open>cspan B = S\<close> and \<open>S \<subseteq> cspan C\<close>
  have \<open>B \<subseteq> cspan C\<close>
    using complex_vector.span_superset by force
  from \<open>finite C\<close> \<open>cindependent B\<close> this
  have \<open>finite B\<close>
    by (rule complex_vector.independent_span_bound[THEN conjunct1])
  from this and \<open>cindependent B\<close> and \<open>cspan B = S\<close>
  show ?thesis
    by auto
qed


subsection \<open>Closed subspaces\<close>

lemma csubspace_INF[simp]: "(\<And>x. x \<in> A \<Longrightarrow> csubspace x) \<Longrightarrow> csubspace (\<Inter>A)"
  by (simp add: complex_vector.subspace_Inter)

locale closed_csubspace =
  fixes A::"('a::{complex_vector,topological_space}) set"
  assumes subspace: "csubspace A"
  assumes closed: "closed A"

declare closed_csubspace.subspace[simp]

lemma closure_is_csubspace[simp]:
  fixes A::"('a::complex_normed_vector) set"
  assumes \<open>csubspace A\<close>
  shows \<open>csubspace (closure A)\<close>
proof-
  have "x \<in> closure A \<Longrightarrow> y \<in> closure A \<Longrightarrow> x+y \<in> closure A" for x y
  proof-
    assume \<open>x\<in>(closure A)\<close>
    then obtain xx where \<open>\<forall> n::nat. xx n \<in> A\<close> and \<open>xx \<longlonglongrightarrow> x\<close>
      using closure_sequential by blast
    assume \<open>y\<in>(closure A)\<close>
    then obtain yy where \<open>\<forall> n::nat. yy n \<in> A\<close> and \<open>yy \<longlonglongrightarrow> y\<close>
      using closure_sequential by blast
    have \<open>\<forall> n::nat. (xx n) + (yy n) \<in> A\<close>
      using \<open>\<forall>n. xx n \<in> A\<close> \<open>\<forall>n. yy n \<in> A\<close> assms complex_vector.subspace_def
      by (simp add: complex_vector.subspace_def)
    hence  \<open>(\<lambda> n. (xx n) + (yy n)) \<longlonglongrightarrow> x + y\<close> using  \<open>xx \<longlonglongrightarrow> x\<close> \<open>yy \<longlonglongrightarrow> y\<close>
      by (simp add: tendsto_add)
    thus ?thesis using  \<open>\<forall> n::nat. (xx n) + (yy n) \<in> A\<close>
      by (meson closure_sequential)
  qed
  moreover have "x\<in>(closure A) \<Longrightarrow> c *\<^sub>C x \<in> (closure A)" for x c
  proof-
    assume \<open>x\<in>(closure A)\<close>
    then obtain xx where \<open>\<forall> n::nat. xx n \<in> A\<close> and \<open>xx \<longlonglongrightarrow> x\<close>
      using closure_sequential by blast
    have \<open>\<forall> n::nat. c *\<^sub>C (xx n) \<in> A\<close>
      using \<open>\<forall>n. xx n \<in> A\<close> assms complex_vector.subspace_def
      by (simp add: complex_vector.subspace_def)
    have \<open>isCont (\<lambda> t. c *\<^sub>C t) x\<close>
      using bounded_clinear.bounded_linear bounded_clinear_scaleC_right linear_continuous_at by auto
    hence  \<open>(\<lambda> n. c *\<^sub>C (xx n)) \<longlonglongrightarrow> c *\<^sub>C x\<close> using  \<open>xx \<longlonglongrightarrow> x\<close>
      by (simp add: isCont_tendsto_compose)
    thus ?thesis using  \<open>\<forall> n::nat. c *\<^sub>C (xx n) \<in> A\<close>
      by (meson closure_sequential)
  qed
  moreover have "0 \<in> (closure A)"
    using assms closure_subset complex_vector.subspace_def
    by (metis in_mono)
  ultimately show ?thesis
    by (simp add: complex_vector.subspaceI)
qed

lemma csubspace_set_plus:
  assumes \<open>csubspace A\<close> and \<open>csubspace B\<close>
  shows \<open>csubspace (A + B)\<close>
proof -
  define C where \<open>C = {\<psi>+\<phi>| \<psi> \<phi>. \<psi>\<in>A \<and> \<phi>\<in>B}\<close>
  have  "x\<in>C \<Longrightarrow> y\<in>C \<Longrightarrow> x+y\<in>C" for x y
    using C_def assms(1) assms(2) complex_vector.subspace_add complex_vector.subspace_sums by blast
  moreover have "c *\<^sub>C x \<in> C" if \<open>x\<in>C\<close> for x c
  proof -
    have "csubspace C"
      by (simp add: C_def assms(1) assms(2) complex_vector.subspace_sums)
    then show ?thesis
      using that by (simp add: complex_vector.subspace_def)
  qed
  moreover have  "0 \<in> C"
    using  \<open>C = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close> add.inverse_neutral add_uminus_conv_diff assms(1) assms(2) diff_0  mem_Collect_eq
      add.right_inverse
    by (metis (mono_tags, lifting) complex_vector.subspace_0)
  ultimately show ?thesis
    unfolding C_def complex_vector.subspace_def
    by (smt mem_Collect_eq set_plus_elim set_plus_intro)
qed

lemma closed_csubspace_0[simp]:
  "closed_csubspace ({0} :: ('a::{complex_vector,t1_space}) set)"
proof-
  have \<open>csubspace {0}\<close>
    using add.right_neutral complex_vector.subspace_def scaleC_right.zero
    by blast
  moreover have "closed ({0} :: 'a set)"
    by simp
  ultimately show ?thesis
    by (simp add: closed_csubspace_def)
qed

lemma closed_csubspace_UNIV[simp]: "closed_csubspace (UNIV::('a::{complex_vector,topological_space}) set)"
proof-
  have \<open>csubspace UNIV\<close>
    by simp
  moreover have \<open>closed UNIV\<close>
    by simp
  ultimately show ?thesis
    unfolding closed_csubspace_def by auto
qed

lemma closed_csubspace_inter[simp]:
  assumes "closed_csubspace A" and "closed_csubspace B"
  shows "closed_csubspace (A\<inter>B)"
proof-
  obtain C where \<open>C = A \<inter> B\<close> by blast
  have \<open>csubspace C\<close>
  proof-
    have "x\<in>C \<Longrightarrow> y\<in>C \<Longrightarrow> x+y\<in>C" for x y
      by (metis IntD1 IntD2 IntI \<open>C = A \<inter> B\<close> assms(1) assms(2) complex_vector.subspace_def closed_csubspace_def)
    moreover have "x\<in>C \<Longrightarrow> c *\<^sub>C x \<in> C" for x c
      by (metis IntD1 IntD2 IntI \<open>C = A \<inter> B\<close> assms(1) assms(2) complex_vector.subspace_def closed_csubspace_def)
    moreover have "0 \<in> C"
      using  \<open>C = A \<inter> B\<close> assms(1) assms(2) complex_vector.subspace_def closed_csubspace_def by fastforce
    ultimately show ?thesis
      by (simp add: complex_vector.subspace_def)
  qed
  moreover have \<open>closed C\<close>
    using  \<open>C = A \<inter> B\<close>
    by (simp add: assms(1) assms(2) closed_Int closed_csubspace.closed)
  ultimately show ?thesis
    using  \<open>C = A \<inter> B\<close>
    by (simp add: closed_csubspace_def)
qed


lemma closed_csubspace_INF[simp]:
  assumes a1: "\<forall>A\<in>\<A>. closed_csubspace A"
  shows "closed_csubspace (\<Inter>\<A>)"
proof-
  have \<open>csubspace (\<Inter>\<A>)\<close>
    by (simp add: assms closed_csubspace.subspace complex_vector.subspace_Inter)
  moreover have \<open>closed (\<Inter>\<A>)\<close>
    by (simp add: assms closed_Inter closed_csubspace.closed)
  ultimately show ?thesis
    by (simp add: closed_csubspace.intro)
qed

typedef (overloaded) ('a::"{complex_vector,topological_space}")
  ccsubspace = \<open>{S::'a set. closed_csubspace S}\<close>
  morphisms space_as_set Abs_ccsubspace
  using Complex_Vector_Spaces.closed_csubspace_UNIV by blast

setup_lifting type_definition_ccsubspace

lemma csubspace_space_as_set[simp]: \<open>csubspace (space_as_set S)\<close>
  by (metis closed_csubspace_def mem_Collect_eq space_as_set)

lemma closed_space_as_set[simp]: \<open>closed (space_as_set S)\<close>
  apply transfer by (simp add: closed_csubspace.closed)

lemma zero_space_as_set[simp]: \<open>0 \<in> space_as_set A\<close>
  by (simp add: complex_vector.subspace_0)

instantiation ccsubspace :: (complex_normed_vector) scaleC begin
lift_definition scaleC_ccsubspace :: "complex \<Rightarrow> 'a ccsubspace \<Rightarrow> 'a ccsubspace" is
  "\<lambda>c S. (*\<^sub>C) c ` S"
proof
  show "csubspace ((*\<^sub>C) c ` S)" if "closed_csubspace S" for c :: complex and S :: "'a set"
    using that
    by (simp add: complex_vector.linear_subspace_image)
  show "closed ((*\<^sub>C) c ` S)" if "closed_csubspace S" for c :: complex and S :: "'a set"
    using that
    by (simp add: closed_scaleC closed_csubspace.closed)
qed

lift_definition scaleR_ccsubspace :: "real \<Rightarrow> 'a ccsubspace \<Rightarrow> 'a ccsubspace" is
  "\<lambda>c S. (*\<^sub>R) c ` S"
proof
  show "csubspace ((*\<^sub>R) r ` S)"
    if "closed_csubspace S"
    for r :: real
      and S :: "'a set"
    using that   using bounded_clinear_def bounded_clinear_scaleC_right scaleR_scaleC
    by (simp add: scaleR_scaleC complex_vector.linear_subspace_image)
  show "closed ((*\<^sub>R) r ` S)"
    if "closed_csubspace S"
    for r :: real
      and S :: "'a set"
    using that
    by (simp add: closed_scaling closed_csubspace.closed)
qed

instance
proof
  show "((*\<^sub>R) r::'a ccsubspace \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)" for r :: real
    by (simp add: scaleR_scaleC scaleC_ccsubspace_def scaleR_ccsubspace_def)
qed
end

instantiation ccsubspace :: ("{complex_vector,t1_space}") bot begin
lift_definition bot_ccsubspace :: \<open>'a ccsubspace\<close> is \<open>{0}\<close>
  by simp
instance..
end

lemma zero_cblinfun_image[simp]: "0 *\<^sub>C S = bot" for S :: "_ ccsubspace"
proof transfer
  have "(0::'b) \<in> (\<lambda>x. 0) ` S"
    if "closed_csubspace S"
    for S::"'b set"
    using that unfolding closed_csubspace_def
    by (simp add: complex_vector.linear_subspace_image complex_vector.module_hom_zero
        complex_vector.subspace_0)
  thus "(*\<^sub>C) 0 ` S = {0::'b}"
    if "closed_csubspace (S::'b set)"
    for S :: "'b set"
    using that
    by (auto intro !: exI [of _ 0])
qed

lemma csubspace_scaleC_invariant:
  fixes a S
  assumes \<open>a \<noteq> 0\<close> and \<open>csubspace S\<close>
  shows \<open>(*\<^sub>C) a ` S = S\<close>
proof-
  have  \<open>x \<in> (*\<^sub>C) a ` S \<Longrightarrow> x \<in> S\<close>
    for x
    using assms(2) complex_vector.subspace_scale by blast
  moreover have  \<open>x \<in> S \<Longrightarrow> x \<in> (*\<^sub>C) a ` S\<close>
    for x
  proof -
    assume "x \<in> S"
    hence "\<exists>c aa. (c / a) *\<^sub>C aa \<in> S \<and> c *\<^sub>C aa = x"
      using assms(2) complex_vector.subspace_def scaleC_one by metis
    hence "\<exists>aa. aa \<in> S \<and> a *\<^sub>C aa = x"
      using assms(1) by auto
    thus ?thesis
      by (meson image_iff)
  qed
  ultimately show ?thesis by blast
qed


lemma ccsubspace_scaleC_invariant[simp]: "a \<noteq> 0 \<Longrightarrow> a *\<^sub>C S = S" for S :: "_ ccsubspace"
  apply transfer
  by (simp add: closed_csubspace.subspace csubspace_scaleC_invariant)


instantiation ccsubspace :: ("{complex_vector,topological_space}") "top"
begin
lift_definition top_ccsubspace :: \<open>'a ccsubspace\<close> is \<open>UNIV\<close>
  by simp

instance ..
end

lemma space_as_set_bot[simp]: \<open>space_as_set bot = {0}\<close>
  by (rule bot_ccsubspace.rep_eq)

lemma ccsubspace_top_not_bot[simp]:
  "(top::'a::{complex_vector,t1_space,not_singleton} ccsubspace) \<noteq> bot"
  (* The type class t1_space is needed because the definition of bot in ccsubspace needs it *)
  by (metis UNIV_not_singleton bot_ccsubspace.rep_eq top_ccsubspace.rep_eq)

lemma ccsubspace_bot_not_top[simp]:
  "(bot::'a::{complex_vector,t1_space,not_singleton} ccsubspace) \<noteq> top"
  using ccsubspace_top_not_bot by metis

instantiation ccsubspace :: ("{complex_vector,topological_space}") "Inf"
begin
lift_definition Inf_ccsubspace::\<open>'a ccsubspace set \<Rightarrow> 'a ccsubspace\<close>
  is \<open>\<lambda> S. \<Inter> S\<close>
proof
  fix S :: "'a set set"
  assume closed: "closed_csubspace x" if \<open>x \<in> S\<close> for x
  show "csubspace (\<Inter> S::'a set)"
    by (simp add: closed closed_csubspace.subspace)
  show "closed (\<Inter> S::'a set)"
    by (simp add: closed closed_csubspace.closed)
qed

instance ..
end

lift_definition ccspan :: "'a::complex_normed_vector set \<Rightarrow> 'a ccsubspace"
  is "\<lambda>G. closure (cspan G)"
proof (rule closed_csubspace.intro)
  fix S :: "'a set"
  show "csubspace (closure (cspan S))"
    by (simp add: closure_is_csubspace)
  show "closed (closure (cspan S))"
    by simp
qed

lemma ccspan_superset:
  \<open>A \<subseteq> space_as_set (ccspan A)\<close>
  for A :: \<open>'a::complex_normed_vector set\<close>
  apply transfer
  by (meson closure_subset complex_vector.span_superset subset_trans)

lemma ccspan_superset': \<open>x \<in> X \<Longrightarrow> x \<in> space_as_set (ccspan X)\<close>
  using ccspan_superset by auto

lemma ccspan_canonical_basis[simp]: "ccspan (set canonical_basis) = top"
  using ccspan.rep_eq space_as_set_inject top_ccsubspace.rep_eq
    closure_UNIV is_generator_set
  by metis

lemma ccspan_Inf_def: \<open>ccspan A = Inf {S. A \<subseteq> space_as_set S}\<close>
  for A::\<open>('a::cbanach) set\<close>
proof -
  have \<open>x \<in> space_as_set (ccspan A)
    \<Longrightarrow> x \<in> space_as_set (Inf {S. A \<subseteq> space_as_set S})\<close>
    for x::'a
  proof-
    assume \<open>x \<in> space_as_set (ccspan A)\<close>
    hence "x \<in> closure (cspan A)"
      by (simp add: ccspan.rep_eq)
    hence \<open>x \<in> closure (complex_vector.span A)\<close>
      unfolding ccspan_def
      by simp
    hence \<open>\<exists> y::nat \<Rightarrow> 'a. (\<forall> n. y n \<in> (complex_vector.span A)) \<and> y \<longlonglongrightarrow> x\<close>
      by (simp add: closure_sequential)
    then obtain y where \<open>\<forall> n. y n \<in> (complex_vector.span A)\<close> and \<open>y \<longlonglongrightarrow> x\<close>
      by blast
    have \<open>y n \<in> \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> closed_csubspace S}\<close>
      for n
      using  \<open>\<forall> n. y n \<in> (complex_vector.span A)\<close>
      by auto

    have \<open>closed_csubspace S \<Longrightarrow> closed S\<close>
      for S::\<open>'a set\<close>
      by (simp add: closed_csubspace.closed)
    hence \<open>closed ( \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> closed_csubspace S})\<close>
      by simp
    hence \<open>x \<in> \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> closed_csubspace S}\<close> using \<open>y \<longlonglongrightarrow> x\<close>
      using \<open>\<And>n. y n \<in> \<Inter> {S. complex_vector.span A \<subseteq> S \<and> closed_csubspace S}\<close> closed_sequentially
      by blast
    moreover have \<open>{S. A \<subseteq> S \<and> closed_csubspace S} \<subseteq> {S. (complex_vector.span A) \<subseteq> S \<and> closed_csubspace S}\<close>
      using Collect_mono_iff
      by (simp add: Collect_mono_iff closed_csubspace.subspace complex_vector.span_minimal)
    ultimately have \<open>x \<in> \<Inter> {S. A \<subseteq> S \<and> closed_csubspace S}\<close>
      by blast
    moreover have "(x::'a) \<in> \<Inter> {x. A \<subseteq> x \<and> closed_csubspace x}"
      if "(x::'a) \<in> \<Inter> {S. A \<subseteq> S \<and> closed_csubspace S}"
      for x :: 'a
        and A :: "'a set"
      using that
      by simp
    ultimately show \<open>x \<in> space_as_set (Inf {S. A \<subseteq> space_as_set S})\<close>
      apply transfer.
  qed
  moreover have \<open>x \<in> space_as_set (Inf {S. A \<subseteq> space_as_set S})
             \<Longrightarrow> x \<in> space_as_set (ccspan A)\<close>
    for x::'a
  proof-
    assume \<open>x \<in> space_as_set (Inf {S. A \<subseteq> space_as_set S})\<close>
    hence \<open>x \<in> \<Inter> {S. A \<subseteq> S \<and> closed_csubspace S}\<close>
      apply transfer
      by blast
    moreover have \<open>{S. (complex_vector.span A) \<subseteq> S \<and> closed_csubspace S} \<subseteq> {S. A \<subseteq> S \<and> closed_csubspace S}\<close>
      using Collect_mono_iff complex_vector.span_superset by fastforce
    ultimately have \<open>x \<in> \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> closed_csubspace S}\<close>
      by blast
    thus \<open>x \<in> space_as_set (ccspan A)\<close>
      by (metis (no_types, lifting) Inter_iff space_as_set closure_subset mem_Collect_eq ccspan.rep_eq)
  qed
  ultimately have \<open>space_as_set (ccspan A) = space_as_set (Inf {S. A \<subseteq> space_as_set S})\<close>
    by blast
  thus ?thesis
    using space_as_set_inject by auto
qed

lemma cspan_singleton_scaleC[simp]: "(a::complex)\<noteq>0 \<Longrightarrow> cspan { a *\<^sub>C \<psi> } = cspan {\<psi>}"
  for \<psi>::"'a::complex_vector"
  by (smt complex_vector.dependent_single complex_vector.independent_insert
      complex_vector.scale_eq_0_iff complex_vector.span_base complex_vector.span_redundant
      complex_vector.span_scale doubleton_eq_iff insert_absorb insert_absorb2 insert_commute
      singletonI)

lemma closure_is_closed_csubspace[simp]:
  fixes S::\<open>'a::complex_normed_vector set\<close>
  assumes \<open>csubspace S\<close>
  shows \<open>closed_csubspace (closure S)\<close>
  using assms closed_csubspace.intro closure_is_csubspace by blast

lemma ccspan_singleton_scaleC[simp]: "(a::complex)\<noteq>0 \<Longrightarrow> ccspan {a *\<^sub>C \<psi>} = ccspan {\<psi>}"
  apply transfer by simp

lemma clinear_continuous_at:
  assumes \<open>bounded_clinear f\<close>
  shows \<open>isCont f x\<close>
  by (simp add: assms bounded_clinear.bounded_linear linear_continuous_at)

lemma clinear_continuous_within:
  assumes \<open>bounded_clinear f\<close>
  shows \<open>continuous (at x within s) f\<close>
  by (simp add: assms bounded_clinear.bounded_linear linear_continuous_within)

lemma antilinear_continuous_at:
  assumes \<open>bounded_antilinear f\<close>
  shows \<open>isCont f x\<close>
  by (simp add: assms bounded_antilinear.bounded_linear linear_continuous_at)

lemma antilinear_continuous_within:
  assumes \<open>bounded_antilinear f\<close>
  shows \<open>continuous (at x within s) f\<close>
  by (simp add: assms bounded_antilinear.bounded_linear linear_continuous_within)

lemma bounded_clinear_eq_on_closure:
  fixes A B :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector"
  assumes \<open>bounded_clinear A\<close> and \<open>bounded_clinear B\<close> and
    eq: \<open>\<And>x. x \<in> G \<Longrightarrow> A x = B x\<close> and t: \<open>t \<in> closure (cspan G)\<close>
  shows \<open>A t = B t\<close>
proof -
  have eq': \<open>A t = B t\<close> if \<open>t \<in> cspan G\<close> for t
    using _ _ that eq apply (rule complex_vector.linear_eq_on)
    by (auto simp: assms bounded_clinear.clinear)
  have \<open>A t - B t = 0\<close>
    using _ _ t apply (rule continuous_constant_on_closure)
    by (auto simp add: eq' assms(1) assms(2) clinear_continuous_at continuous_at_imp_continuous_on)
  then show ?thesis
    by auto
qed

instantiation ccsubspace :: ("{complex_vector,topological_space}") "order"
begin
lift_definition less_eq_ccsubspace :: \<open>'a ccsubspace \<Rightarrow> 'a ccsubspace \<Rightarrow> bool\<close>
  is  \<open>(\<subseteq>)\<close>.
declare less_eq_ccsubspace_def[code del]
lift_definition less_ccsubspace :: \<open>'a ccsubspace \<Rightarrow> 'a ccsubspace \<Rightarrow> bool\<close>
  is \<open>(\<subset>)\<close>.
declare less_ccsubspace_def[code del]
instance
proof
  fix x y z :: "'a ccsubspace"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_eq_ccsubspace.rep_eq less_le_not_le less_ccsubspace.rep_eq)
  show "x \<le> x"
    by (simp add: less_eq_ccsubspace.rep_eq)
  show "x \<le> z" if "x \<le> y" and "y \<le> z"
    using that less_eq_ccsubspace.rep_eq by auto
  show "x = y" if "x \<le> y" and "y \<le> x"
    using that by (simp add: space_as_set_inject less_eq_ccsubspace.rep_eq)
qed
end

lemma ccspan_leqI:
  assumes \<open>M \<subseteq> space_as_set S\<close>
  shows \<open>ccspan M \<le> S\<close>
  using assms apply transfer
  by (simp add: closed_csubspace.closed closure_minimal complex_vector.span_minimal)

lemma ccspan_mono:
  assumes \<open>A \<subseteq> B\<close>
  shows \<open>ccspan A \<le> ccspan B\<close>
  apply (transfer fixing: A B)
  by (simp add: assms closure_mono complex_vector.span_mono)

lemma ccsubspace_leI:
  assumes t1: "space_as_set A \<subseteq> space_as_set B"
  shows "A \<le> B"
  using t1 apply transfer by -

lemma ccspan_of_empty[simp]: "ccspan {} = bot"
proof transfer
  show "closure (cspan {}) = {0::'a}"
    by simp
qed


instantiation ccsubspace :: ("{complex_vector,topological_space}") inf begin
lift_definition inf_ccsubspace :: "'a ccsubspace \<Rightarrow> 'a ccsubspace \<Rightarrow> 'a ccsubspace"
  is "(\<inter>)" by simp
instance .. end

lemma space_as_set_inf[simp]: "space_as_set (A \<sqinter> B) = space_as_set A \<inter> space_as_set B"
  by (rule inf_ccsubspace.rep_eq)

instantiation ccsubspace :: ("{complex_vector,topological_space}") order_top begin
instance
proof
  show "a \<le> \<top>"
    for a :: "'a ccsubspace"
    apply transfer
    by simp
qed
end


instantiation ccsubspace :: ("{complex_vector,t1_space}") order_bot begin
instance
proof
  show "(\<bottom>::'a ccsubspace) \<le> a"
    for a :: "'a ccsubspace"
    apply transfer
    apply auto
    using closed_csubspace.subspace complex_vector.subspace_0 by blast
qed
end


instantiation ccsubspace :: ("{complex_vector,topological_space}") semilattice_inf begin
instance
proof
  fix x y z :: \<open>'a ccsubspace\<close>
  show "x \<sqinter> y \<le> x"
    apply transfer by simp
  show "x \<sqinter> y \<le> y"
    apply transfer by simp
  show "x \<le> y \<sqinter> z" if "x \<le> y" and "x \<le> z"
    using that apply transfer by simp
qed
end


instantiation ccsubspace :: ("{complex_vector,t1_space}") zero begin
definition zero_ccsubspace :: "'a ccsubspace" where [simp]: "zero_ccsubspace = bot"
lemma zero_ccsubspace_transfer[transfer_rule]: \<open>pcr_ccsubspace (=) {0} 0\<close>
  unfolding zero_ccsubspace_def by transfer_prover
instance ..
end

lemma ccspan_0[simp]: \<open>ccspan {0} = 0\<close>
  apply transfer
  by simp

definition \<open>rel_ccsubspace R x y = rel_set R (space_as_set x) (space_as_set y)\<close>


lemma left_unique_rel_ccsubspace[transfer_rule]: \<open>left_unique (rel_ccsubspace R)\<close> if \<open>left_unique R\<close>
proof (rule left_uniqueI)
  fix S T :: \<open>'a ccsubspace\<close> and U
  assume assms: \<open>rel_ccsubspace R S U\<close> \<open>rel_ccsubspace R T U\<close>
  have \<open>space_as_set S = space_as_set T\<close>
    apply (rule left_uniqueD)
      using that apply (rule left_unique_rel_set)
    using assms unfolding rel_ccsubspace_def by auto
  then show \<open>S = T\<close>
    by (simp add: space_as_set_inject)
qed

lemma right_unique_rel_ccsubspace[transfer_rule]: \<open>right_unique (rel_ccsubspace R)\<close> if \<open>right_unique R\<close>
  by (metis rel_ccsubspace_def right_unique_def right_unique_rel_set space_as_set_inject that)

lemma bi_unique_rel_ccsubspace[transfer_rule]: \<open>bi_unique (rel_ccsubspace R)\<close> if \<open>bi_unique R\<close>
  by (metis (no_types, lifting) bi_unique_def bi_unique_rel_set rel_ccsubspace_def space_as_set_inject that)

lemma converse_rel_ccsubspace: \<open>conversep (rel_ccsubspace R) = rel_ccsubspace (conversep R)\<close>
  by (auto simp: rel_ccsubspace_def[abs_def])

lemma space_as_set_top[simp]: \<open>space_as_set top = UNIV\<close>
  by (rule top_ccsubspace.rep_eq)

lemma ccsubspace_eqI:
  assumes \<open>\<And>x. x \<in> space_as_set S \<longleftrightarrow> x \<in> space_as_set T\<close>
  shows \<open>S = T\<close>
  by (metis Abs_ccsubspace_cases Abs_ccsubspace_inverse antisym assms subsetI)

lemma ccspan_remove_0: \<open>ccspan (A - {0}) = ccspan A\<close>
  apply transfer
  by auto

lemma sgn_in_spaceD: \<open>\<psi> \<in> space_as_set A\<close> if \<open>sgn \<psi> \<in> space_as_set A\<close> and \<open>\<psi> \<noteq> 0\<close>
  for \<psi> :: \<open>_ :: complex_normed_vector\<close>
  using that
  apply (transfer fixing: \<psi>)
  by (metis closed_csubspace.subspace complex_vector.subspace_scale divideC_field_simps(1) scaleR_eq_0_iff scaleR_scaleC sgn_div_norm sgn_zero_iff)

lemma sgn_in_spaceI: \<open>sgn \<psi> \<in> space_as_set A\<close> if \<open>\<psi> \<in> space_as_set A\<close> 
  for \<psi> :: \<open>_ :: complex_normed_vector\<close>
  using that by (auto simp: sgn_div_norm scaleR_scaleC complex_vector.subspace_scale)

lemma ccsubspace_leI_unit:
  fixes A B :: \<open>_ :: complex_normed_vector ccsubspace\<close>
  assumes "\<And>\<psi>. norm \<psi> = 1 \<Longrightarrow> \<psi> \<in> space_as_set A \<Longrightarrow> \<psi> \<in> space_as_set B"
  shows "A \<le> B"
proof (rule ccsubspace_leI, rule subsetI)
  fix \<psi> assume \<psi>A: \<open>\<psi> \<in> space_as_set A\<close>
  show \<open>\<psi> \<in> space_as_set B\<close>
    apply (cases \<open>\<psi> = 0\<close>)
    apply simp
    using assms[of \<open>sgn \<psi>\<close>] \<psi>A sgn_in_spaceD sgn_in_spaceI 
    by (auto simp: norm_sgn)
qed

lemma kernel_is_closed_csubspace[simp]:
  assumes a1: "bounded_clinear f"
  shows "closed_csubspace (f -` {0})"
proof-
  have \<open>csubspace (f -` {0})\<close>
    using assms bounded_clinear.clinear complex_vector.linear_subspace_vimage complex_vector.subspace_single_0 by blast
  have "L \<in> {x. f x = 0}"
    if "r \<longlonglongrightarrow> L" and "\<forall> n. r n \<in> {x. f x = 0}"
    for r and  L
  proof-
    have d1: \<open>\<forall> n. f (r n) = 0\<close>
      using that(2) by auto
    have \<open>(\<lambda> n. f (r n)) \<longlonglongrightarrow> f L\<close>
      using assms clinear_continuous_at continuous_within_tendsto_compose' that(1)
      by fastforce
    hence \<open>(\<lambda> n. 0) \<longlonglongrightarrow> f L\<close>
      using d1 by simp
    hence \<open>f L = 0\<close>
      using limI by fastforce
    thus ?thesis by blast
  qed
  then have s3: \<open>closed (f -` {0})\<close>
    using closed_sequential_limits by force
  with \<open>csubspace (f -` {0})\<close>
  show ?thesis
    using closed_csubspace.intro by blast
qed

lemma ccspan_closure[simp]: \<open>ccspan (closure X) = ccspan X\<close>
  by (simp add: basic_trans_rules(24) ccspan.rep_eq ccspan_leqI ccspan_mono closure_mono closure_subset complex_vector.span_superset)

lemma ccspan_finite: \<open>space_as_set (ccspan X) = cspan X\<close> if \<open>finite X\<close>
  by (simp add: ccspan.rep_eq that)

lemma ccspan_UNIV[simp]: \<open>ccspan UNIV = \<top>\<close>
  by (simp add: ccspan.abs_eq top_ccsubspace_def)

lemma infsum_in_closed_csubspaceI:
  assumes \<open>\<And>x. x\<in>X \<Longrightarrow> f x \<in> A\<close>
  assumes \<open>closed_csubspace A\<close>
  shows \<open>infsum f X \<in> A\<close>
proof (cases \<open>f summable_on X\<close>)
  case True
  then have lim: \<open>(sum f \<longlongrightarrow> infsum f X) (finite_subsets_at_top X)\<close>
    by (simp add: infsum_tendsto)
  have sumA: \<open>sum f F \<in> A\<close> if \<open>finite F\<close> and \<open>F \<subseteq> X\<close> for F
    apply (rule complex_vector.subspace_sum)
    using that assms by auto
  from lim show \<open>infsum f X \<in> A\<close>
    apply (rule Lim_in_closed_set[rotated -1])
    using assms sumA by (auto intro!: closed_csubspace.closed eventually_finite_subsets_at_top_weakI)
next
  case False
  then show ?thesis
    using assms by (auto intro!: closed_csubspace.closed complex_vector.subspace_0 simp add: infsum_not_exists)
qed

lemma closed_csubspace_space_as_set[simp]: \<open>closed_csubspace (space_as_set X)\<close>
  using space_as_set by simp

lift_definition finite_dim_ccsubspace :: \<open>'a::complex_normed_vector ccsubspace \<Rightarrow> bool\<close> is cfinite_dim.

lemma ccspan_finite_dim[intro]: \<open>finite_dim_ccsubspace (ccspan B)\<close> if \<open>finite B\<close>
  using ccspan_finite finite_dim_ccsubspace.rep_eq that by fastforce

lemma finite_dim_ccsubspace_zero[iff]: \<open>finite_dim_ccsubspace 0\<close>
proof -
  have *: \<open>cfinite_dim (cspan {0})\<close>
    by blast
  show ?thesis
    apply transfer
    using * by simp
qed

lemma finite_dim_ccsubspace_bot[iff]: \<open>finite_dim_ccsubspace \<bottom>\<close>
  using finite_dim_ccsubspace_zero by auto


lemma ccsubspace_contains_unit:
  assumes \<open>E \<noteq> \<bottom>\<close>
  shows \<open>\<exists>h\<in>space_as_set E. norm h = 1\<close>
proof -
  from assms have \<open>space_as_set E \<noteq> {0}\<close>
    by (metis bot_ccsubspace.rep_eq space_as_set_inject)
  then obtain h\<^sub>0 where \<open>h\<^sub>0 \<in> space_as_set E\<close> and \<open>h\<^sub>0 \<noteq> 0\<close>
    by auto
  then have \<open>sgn h\<^sub>0 \<in> space_as_set E\<close>
    using csubspace_space_as_set
    by (auto intro!: complex_vector.subspace_scale
        simp add: sgn_div_norm scaleR_scaleC)
  moreover from \<open>h\<^sub>0 \<noteq> 0\<close> have \<open>norm (sgn h\<^sub>0) = 1\<close>
    by (simp add: norm_sgn)
  ultimately show ?thesis
    by auto
qed


subsection \<open>Closed sums\<close>

definition closed_sum:: \<open>'a::{semigroup_add,topological_space} set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> where
  \<open>closed_sum A B = closure (A + B)\<close>

notation closed_sum (infixl \<open>+\<^sub>M\<close> 65)

lemma closed_sum_comm: \<open>A +\<^sub>M B = B +\<^sub>M A\<close> for A B :: "_::ab_semigroup_add"
  by (simp add: add.commute closed_sum_def)

lemma closed_sum_left_subset: \<open>0 \<in> B \<Longrightarrow> A \<subseteq> A +\<^sub>M B\<close> for A B :: "_::monoid_add"
  by (metis add.right_neutral closed_sum_def closure_subset in_mono set_plus_intro subsetI)

lemma closed_sum_right_subset: \<open>0 \<in> A \<Longrightarrow> B \<subseteq> A +\<^sub>M B\<close> for A B :: "_::monoid_add"
  by (metis add.left_neutral closed_sum_def closure_subset set_plus_intro subset_iff)

lemma finite_cspan_closed_csubspace:
  assumes "finite (S::'a::complex_normed_vector set)"
  shows "closed_csubspace (cspan S)"
  by (simp add: assms closed_csubspace.intro)

lemma closed_sum_is_sup:
  fixes A B C:: \<open>('a::{complex_vector,topological_space}) set\<close>
  assumes \<open>closed_csubspace C\<close>
  assumes \<open>A \<subseteq> C\<close> and \<open>B \<subseteq> C\<close>
  shows \<open>(A +\<^sub>M B) \<subseteq> C\<close>
proof -
  have \<open>A + B \<subseteq> C\<close>
    using assms unfolding set_plus_def
    using closed_csubspace.subspace complex_vector.subspace_add by blast
  then show \<open>(A +\<^sub>M B) \<subseteq> C\<close>
    unfolding closed_sum_def
    using \<open>closed_csubspace C\<close>
    by (simp add: closed_csubspace.closed closure_minimal)
qed

lemma closed_subspace_closed_sum:
  fixes A B::"('a::complex_normed_vector) set"
  assumes a1: \<open>csubspace A\<close> and a2: \<open>csubspace B\<close>
  shows \<open>closed_csubspace (A +\<^sub>M B)\<close>
  using a1 a2 closed_sum_def
  by (metis closure_is_closed_csubspace csubspace_set_plus)


lemma closed_sum_assoc:
  fixes A B C::"'a::real_normed_vector set"
  shows \<open>A +\<^sub>M (B +\<^sub>M C) = (A +\<^sub>M B) +\<^sub>M C\<close>
proof -
  have \<open>A + closure B \<subseteq> closure (A + B)\<close> for A B :: "'a set"
    by (meson closure_subset closure_sum dual_order.trans order_refl set_plus_mono2)
  then have \<open>A +\<^sub>M (B +\<^sub>M C) = closure (A + (B + C))\<close>
    unfolding closed_sum_def
    by (meson antisym_conv closed_closure closure_minimal closure_mono closure_subset equalityD1 set_plus_mono2)
  moreover
  have \<open>closure A + B \<subseteq> closure (A + B)\<close> for A B :: "'a set"
    by (meson closure_subset closure_sum dual_order.trans order_refl set_plus_mono2)
  then have \<open>(A +\<^sub>M B) +\<^sub>M C = closure ((A + B) + C)\<close>
    unfolding closed_sum_def
    by (meson closed_closure closure_minimal closure_mono closure_subset eq_iff set_plus_mono2)
  ultimately show ?thesis
    by (simp add: ab_semigroup_add_class.add_ac(1))
qed


lemma closed_sum_zero_left[simp]:
  fixes A :: \<open>('a::{monoid_add, topological_space}) set\<close>
  shows \<open>{0} +\<^sub>M A = closure A\<close>
  unfolding closed_sum_def
  by (metis add.left_neutral set_zero)

lemma closed_sum_zero_right[simp]:
  fixes A :: \<open>('a::{monoid_add, topological_space}) set\<close>
  shows \<open>A +\<^sub>M {0} = closure A\<close>
  unfolding closed_sum_def
  by (metis add.right_neutral set_zero)

lemma closed_sum_closure_right[simp]:
  fixes A B :: \<open>'a::real_normed_vector set\<close>
  shows \<open>A +\<^sub>M closure B = A +\<^sub>M B\<close>
  by (metis closed_sum_assoc closed_sum_def closed_sum_zero_right closure_closure)

lemma closed_sum_closure_left[simp]:
  fixes A B :: \<open>'a::real_normed_vector set\<close>
  shows \<open>closure A +\<^sub>M B = A +\<^sub>M B\<close>
  by (simp add: closed_sum_comm)

lemma closed_sum_mono_left:
  assumes \<open>A \<subseteq> B\<close>
  shows \<open>A +\<^sub>M C \<subseteq> B +\<^sub>M C\<close>
  by (simp add: assms closed_sum_def closure_mono set_plus_mono2)

lemma closed_sum_mono_right:
  assumes \<open>A \<subseteq> B\<close>
  shows \<open>C +\<^sub>M A \<subseteq> C +\<^sub>M B\<close>
  by (simp add: assms closed_sum_def closure_mono set_plus_mono2)

instantiation ccsubspace :: (complex_normed_vector) sup begin
lift_definition sup_ccsubspace :: "'a ccsubspace \<Rightarrow> 'a ccsubspace \<Rightarrow> 'a ccsubspace"
  \<comment> \<open>Note that \<^term>\<open>A+B\<close> would not be a closed subspace, we need the closure. See, e.g., \<^url>\<open>https://math.stackexchange.com/a/1786792/403528\<close>.\<close>
  is "\<lambda>A B::'a set. A +\<^sub>M B"
  by (simp add: closed_subspace_closed_sum)
instance ..
end

lemma closed_sum_cspan[simp]:
  shows \<open>cspan X +\<^sub>M cspan Y = closure (cspan (X \<union> Y))\<close>
  by (smt (verit, best) Collect_cong closed_sum_def complex_vector.span_Un set_plus_def)

lemma closure_image_closed_sum:
  assumes \<open>bounded_linear U\<close>
  shows \<open>closure (U ` (A +\<^sub>M B)) = closure (U ` A) +\<^sub>M closure (U ` B)\<close>
proof -
  have \<open>closure (U ` (A +\<^sub>M B)) = closure (U ` closure (closure A + closure B))\<close>
    unfolding closed_sum_def
    by (smt (verit, best) closed_closure closure_minimal closure_mono closure_subset closure_sum set_plus_mono2 subset_antisym)
  also have \<open>\<dots> = closure (U ` (closure A + closure B))\<close>
    using assms closure_bounded_linear_image_subset_eq by blast
  also have \<open>\<dots> = closure (U ` closure A + U ` closure B)\<close>
    apply (subst image_set_plus)
    by (simp_all add: assms bounded_linear.linear)
  also have \<open>\<dots> = closure (closure (U ` A) + closure (U ` B))\<close>
    by (smt (verit, ccfv_SIG) assms closed_closure closure_bounded_linear_image_subset closure_bounded_linear_image_subset_eq closure_minimal closure_mono closure_sum dual_order.eq_iff set_plus_mono2)
  also have \<open>\<dots> = closure (U ` A) +\<^sub>M closure (U ` B)\<close>
    using closed_sum_def by blast
  finally show ?thesis
    by -
qed



lemma ccspan_union: "ccspan A \<squnion> ccspan B = ccspan (A \<union> B)"
  apply transfer by simp

instantiation ccsubspace :: (complex_normed_vector) "Sup"
begin
lift_definition Sup_ccsubspace::\<open>'a ccsubspace set \<Rightarrow> 'a ccsubspace\<close>
  is \<open>\<lambda>S. closure (complex_vector.span (Union S))\<close>
proof
  show "csubspace (closure (complex_vector.span (\<Union> S::'a set)))"
    if "\<And>x::'a set. x \<in> S \<Longrightarrow> closed_csubspace x"
    for S :: "'a set set"
    using that
    by (simp add: closure_is_closed_csubspace)
  show "closed (closure (complex_vector.span (\<Union> S::'a set)))"
    if "\<And>x. (x::'a set) \<in> S \<Longrightarrow> closed_csubspace x"
    for S :: "'a set set"
    using that
    by simp
qed

instance..
end


instance ccsubspace :: ("{complex_normed_vector}") semilattice_sup
proof
  fix x y z :: \<open>'a ccsubspace\<close>
  show \<open>x \<le> sup x y\<close>
    apply transfer
    by (simp add: closed_csubspace_def closed_sum_left_subset complex_vector.subspace_0)

  show "y \<le> sup x y"
    apply transfer
    by (simp add: closed_csubspace_def closed_sum_right_subset complex_vector.subspace_0)

  show "sup x y \<le> z" if "x \<le> z" and "y \<le> z"
    using that apply transfer
    apply (rule closed_sum_is_sup) by auto
qed

instance ccsubspace :: (complex_normed_vector) complete_lattice
proof
  show "Inf A \<le> x" if "x \<in> A"
    for x :: "'a ccsubspace" and A :: "'a ccsubspace set"
    using that
    apply transfer
    by auto

  have b1: "z \<subseteq> \<Inter> A"
    if "Ball A closed_csubspace" and
      "closed_csubspace z" and
      "(\<And>x. closed_csubspace x \<Longrightarrow> x \<in> A \<Longrightarrow> z \<subseteq> x)"
    for z::"'a set" and A
    using that
    by auto
  show "z \<le> Inf A"
    if "\<And>x::'a ccsubspace. x \<in> A \<Longrightarrow> z \<le> x"
    for A :: "'a ccsubspace set"
      and z :: "'a ccsubspace"
    using that
    apply transfer
    using b1 by blast

  show "x \<le> Sup A"
    if "x \<in> A"
    for x :: "'a ccsubspace"
      and A :: "'a ccsubspace set"
    using that
    apply transfer
    by (meson Union_upper closure_subset complex_vector.span_superset dual_order.trans)

  show "Sup A \<le> z"
    if "\<And>x::'a ccsubspace. x \<in> A \<Longrightarrow> x \<le> z"
    for A :: "'a ccsubspace set"
      and z :: "'a ccsubspace"
    using that apply transfer
  proof -
    fix A :: "'a set set" and z :: "'a set"
    assume A_closed: "Ball A closed_csubspace"
    assume "closed_csubspace z"
    assume in_z: "\<And>x. closed_csubspace x \<Longrightarrow> x \<in> A \<Longrightarrow> x \<subseteq> z"
    from A_closed in_z
    have \<open>V \<subseteq> z\<close> if \<open>V \<in> A\<close> for V
      by (simp add: that)
    then have \<open>\<Union> A \<subseteq> z\<close>
      by (simp add: Sup_le_iff)
    with \<open>closed_csubspace z\<close>
    show "closure (cspan (\<Union> A)) \<subseteq> z"
      by (simp add: closed_csubspace_def closure_minimal complex_vector.span_def subset_hull)
  qed

  show "Inf {} = (top::'a ccsubspace)"
    using \<open>\<And>z A. (\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A\<close> top.extremum_uniqueI by auto

  show "Sup {} = (bot::'a ccsubspace)"
    using \<open>\<And>z A. (\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup A \<le> z\<close> bot.extremum_uniqueI by auto
qed

instantiation ccsubspace :: (complex_normed_vector) comm_monoid_add begin
definition plus_ccsubspace :: "'a ccsubspace \<Rightarrow> _ \<Rightarrow> _"
  where [simp]: "plus_ccsubspace = sup"
instance
proof
  fix a b c :: \<open>'a ccsubspace\<close>
  show "a + b + c = a + (b + c)"
    using sup.assoc by auto
  show "a + b = b + a"
    by (simp add: sup.commute)
  show "0 + a = a"
    by (simp add: zero_ccsubspace_def)
qed
end

lemma SUP_ccspan: \<open>(SUP x\<in>X. ccspan (S x)) = ccspan (\<Union>x\<in>X. S x)\<close>
proof (rule SUP_eqI)
  show \<open>ccspan (S x) \<le> ccspan (\<Union>x\<in>X. S x)\<close> if \<open>x \<in> X\<close> for x
    apply (rule ccspan_mono)
    using that by auto
  show \<open>ccspan (\<Union>x\<in>X. S x) \<le> y\<close> if \<open>\<And>x. x \<in> X \<Longrightarrow> ccspan (S x) \<le> y\<close> for y
    apply (intro ccspan_leqI UN_least)
    using that ccspan_superset by (auto simp: less_eq_ccsubspace.rep_eq)
qed

lemma ccsubspace_plus_sup: "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y + z \<le> x"
  for x y z :: "'a::complex_normed_vector ccsubspace"
  unfolding plus_ccsubspace_def by auto

lemma ccsubspace_Sup_empty: "Sup {} = (0::_ ccsubspace)"
  unfolding zero_ccsubspace_def by auto

lemma ccsubspace_add_right_incr[simp]: "a \<le> a + c" for a::"_ ccsubspace"
  by (simp add: add_increasing2)

lemma ccsubspace_add_left_incr[simp]: "a \<le> c + a" for a::"_ ccsubspace"
  by (simp add: add_increasing)

lemma sum_bot_ccsubspace[simp]: \<open>(\<Sum>x\<in>X. \<bottom>) = (\<bottom> :: _ ccsubspace)\<close>
  by (simp flip: zero_ccsubspace_def)

subsection \<open>Conjugate space\<close>

typedef 'a conjugate_space = "UNIV :: 'a set"
  morphisms from_conjugate_space to_conjugate_space ..
setup_lifting type_definition_conjugate_space

instantiation conjugate_space :: (complex_vector) complex_vector begin
lift_definition scaleC_conjugate_space :: \<open>complex \<Rightarrow> 'a conjugate_space \<Rightarrow> 'a conjugate_space\<close> is \<open>\<lambda>c x. cnj c *\<^sub>C x\<close>.
lift_definition scaleR_conjugate_space :: \<open>real \<Rightarrow> 'a conjugate_space \<Rightarrow> 'a conjugate_space\<close> is \<open>\<lambda>r x. r *\<^sub>R x\<close>.
lift_definition plus_conjugate_space :: "'a conjugate_space \<Rightarrow> 'a conjugate_space \<Rightarrow> 'a conjugate_space" is "(+)".
lift_definition uminus_conjugate_space :: "'a conjugate_space \<Rightarrow> 'a conjugate_space" is \<open>\<lambda>x. -x\<close>.
lift_definition zero_conjugate_space :: "'a conjugate_space" is 0.
lift_definition minus_conjugate_space :: "'a conjugate_space \<Rightarrow> 'a conjugate_space \<Rightarrow> 'a conjugate_space" is "(-)".
instance
  apply (intro_classes; transfer)
  by (simp_all add: scaleR_scaleC scaleC_add_right scaleC_left.add)
end

instantiation conjugate_space :: (complex_normed_vector) complex_normed_vector begin
lift_definition sgn_conjugate_space :: "'a conjugate_space \<Rightarrow> 'a conjugate_space" is "sgn".
lift_definition norm_conjugate_space :: "'a conjugate_space \<Rightarrow> real" is norm.
lift_definition dist_conjugate_space :: "'a conjugate_space \<Rightarrow> 'a conjugate_space \<Rightarrow> real" is dist.
lift_definition uniformity_conjugate_space :: "('a conjugate_space \<times> 'a conjugate_space) filter" is uniformity.
lift_definition  open_conjugate_space :: "'a conjugate_space set \<Rightarrow> bool" is "open".
instance
  apply (intro_classes; transfer)
  by (simp_all add: dist_norm sgn_div_norm open_uniformity uniformity_dist norm_triangle_ineq)
end

instantiation conjugate_space :: (cbanach) cbanach begin
instance
  apply intro_classes
  unfolding Cauchy_def convergent_def LIMSEQ_def apply transfer
  using Cauchy_convergent unfolding Cauchy_def convergent_def LIMSEQ_def by metis
end

lemma bounded_antilinear_to_conjugate_space[simp]: \<open>bounded_antilinear to_conjugate_space\<close>
  by (rule bounded_antilinear_intro[where K=1]; transfer; auto)

lemma bounded_antilinear_from_conjugate_space[simp]: \<open>bounded_antilinear from_conjugate_space\<close>
  by (rule bounded_antilinear_intro[where K=1]; transfer; auto)

lemma antilinear_to_conjugate_space[simp]: \<open>antilinear to_conjugate_space\<close>
  by (rule antilinearI; transfer, auto)

lemma antilinear_from_conjugate_space[simp]: \<open>antilinear from_conjugate_space\<close>
  by (rule antilinearI; transfer, auto)

lemma cspan_to_conjugate_space[simp]: "cspan (to_conjugate_space ` X) = to_conjugate_space ` cspan X"
  unfolding complex_vector.span_def complex_vector.subspace_def hull_def
  apply transfer
  apply simp
  by (metis (no_types, opaque_lifting) complex_cnj_cnj)

lemma surj_to_conjugate_space[simp]: "surj to_conjugate_space"
  by (meson surj_def to_conjugate_space_cases)

lemmas has_derivative_scaleC[simp, derivative_intros] =
  bounded_bilinear.FDERIV[OF bounded_cbilinear_scaleC[THEN bounded_cbilinear.bounded_bilinear]]

lemma norm_to_conjugate_space[simp]: \<open>norm (to_conjugate_space x) = norm x\<close>
  by (fact norm_conjugate_space.abs_eq)

lemma norm_from_conjugate_space[simp]: \<open>norm (from_conjugate_space x) = norm x\<close>
  by (simp add: norm_conjugate_space.rep_eq)

lemma closure_to_conjugate_space: \<open>closure (to_conjugate_space ` X) = to_conjugate_space ` closure X\<close>
proof -
  have 1: \<open>to_conjugate_space ` closure X \<subseteq> closure (to_conjugate_space ` X)\<close>
    apply (rule closure_bounded_linear_image_subset)
    by (simp add: bounded_antilinear.bounded_linear)
  have \<open>\<dots> = to_conjugate_space ` from_conjugate_space ` closure (to_conjugate_space ` X)\<close>
    by (simp add: from_conjugate_space_inverse image_image)
  also have \<open>\<dots> \<subseteq> to_conjugate_space ` closure (from_conjugate_space ` to_conjugate_space ` X)\<close>
    apply (rule image_mono)
    apply (rule closure_bounded_linear_image_subset)
    by (simp add: bounded_antilinear.bounded_linear)
  also have \<open>\<dots> = to_conjugate_space ` closure X\<close>
    by (simp add: to_conjugate_space_inverse image_image)
  finally show ?thesis
    using 1 by simp
qed

lemma closure_from_conjugate_space: \<open>closure (from_conjugate_space ` X) = from_conjugate_space ` closure X\<close>
proof -
  have 1: \<open>from_conjugate_space ` closure X \<subseteq> closure (from_conjugate_space ` X)\<close>
    apply (rule closure_bounded_linear_image_subset)
    by (simp add: bounded_antilinear.bounded_linear)
  have \<open>\<dots> = from_conjugate_space ` to_conjugate_space ` closure (from_conjugate_space ` X)\<close>
    by (simp add: to_conjugate_space_inverse image_image)
  also have \<open>\<dots> \<subseteq> from_conjugate_space ` closure (to_conjugate_space ` from_conjugate_space ` X)\<close>
    apply (rule image_mono)
    apply (rule closure_bounded_linear_image_subset)
    by (simp add: bounded_antilinear.bounded_linear)
  also have \<open>\<dots> = from_conjugate_space ` closure X\<close>
    by (simp add: from_conjugate_space_inverse image_image)
  finally show ?thesis
    using 1 by simp
qed

lemma bounded_antilinear_eq_on:
  fixes A B :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector"
  assumes \<open>bounded_antilinear A\<close> and \<open>bounded_antilinear B\<close> and
    eq: \<open>\<And>x. x \<in> G \<Longrightarrow> A x = B x\<close> and t: \<open>t \<in> closure (cspan G)\<close>
  shows \<open>A t = B t\<close>
proof -
  let ?A = \<open>\<lambda>x. A (from_conjugate_space x)\<close> and ?B = \<open>\<lambda>x. B (from_conjugate_space x)\<close>
    and ?G = \<open>to_conjugate_space ` G\<close> and ?t = \<open>to_conjugate_space t\<close>
  have \<open>bounded_clinear ?A\<close> and \<open>bounded_clinear ?B\<close>
    by (auto intro!: bounded_antilinear_o_bounded_antilinear[OF \<open>bounded_antilinear A\<close>]
        bounded_antilinear_o_bounded_antilinear[OF \<open>bounded_antilinear B\<close>])
  moreover from eq have \<open>\<And>x. x \<in> ?G \<Longrightarrow> ?A x = ?B x\<close>
    by (metis image_iff iso_tuple_UNIV_I to_conjugate_space_inverse)
  moreover from t have \<open>?t \<in> closure (cspan ?G)\<close>
    by (metis bounded_antilinear.bounded_linear bounded_antilinear_to_conjugate_space closure_bounded_linear_image_subset cspan_to_conjugate_space imageI subsetD)
  ultimately have \<open>?A ?t = ?B ?t\<close>
    by (rule bounded_clinear_eq_on_closure)
  then show \<open>A t = B t\<close>
    by (simp add: to_conjugate_space_inverse)
qed

lemma to_conjugate_space_0[simp]: \<open>to_conjugate_space 0 = 0\<close>
  by (simp add: zero_conjugate_space.abs_eq)

lemma from_conjugate_space_0[simp]: \<open>from_conjugate_space 0 = 0\<close>
  using zero_conjugate_space.rep_eq by blast

lemma antilinear_eq_0_on_span:
  assumes \<open>antilinear f\<close>
    and \<open>\<And>x. x \<in> b \<Longrightarrow> f x = 0\<close>
    and \<open>x \<in> cspan b\<close>
  shows \<open>f x = 0\<close>
proof -
  from assms(1)
  have \<open>clinear (\<lambda>x. to_conjugate_space (f x))\<close>
    apply (rule antilinear_o_antilinear[unfolded o_def])
    by simp
  then have \<open>to_conjugate_space (f x) = 0\<close>
    apply (rule complex_vector.linear_eq_0_on_span)
    using assms by auto
  then have \<open>from_conjugate_space (to_conjugate_space (f x)) = 0\<close>
    by simp
  then show ?thesis
    by (simp add: to_conjugate_space_inverse)
qed

subsection \<open>Separating sets\<close>

lemma separating_set_bounded_clinear_dense:
  assumes \<open>ccspan S = \<top>\<close>
  shows \<open>separating_set bounded_clinear S\<close>
  unfolding separating_set_def
  apply (intro allI impI ext, rule bounded_clinear_eq_on_closure[where G=S])
  by (use assms ccspan.rep_eq top_ccsubspace.rep_eq in force)+

lemma separating_set_bounded_cbilinear_nested:
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector) \<Rightarrow> _) ((\<lambda>(x, y). h x y) ` (UNIV \<times> UNIV))\<close>
  assumes \<open>bounded_cbilinear h\<close>
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) A\<close>
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) B\<close>
  shows \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) ((\<lambda>(x,y). h x y) ` (A \<times> B))\<close>
proof (rule separating_setI)
  fix f g :: \<open>'a \<Rightarrow> 'e\<close>
  assume [simp]: \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  have [simp]: \<open>bounded_clinear (\<lambda>x. f (h x y))\<close> for y
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear f\<close>])
    using assms(2) by (rule bounded_cbilinear.bounded_clinear_left)
  have [simp]: \<open>bounded_clinear (\<lambda>x. g (h x y))\<close> for y
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear g\<close>])
    using assms(2) by (rule bounded_cbilinear.bounded_clinear_left)
  have [simp]: \<open>bounded_clinear (\<lambda>y. f (h x y))\<close> for x
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear f\<close>])
    using assms(2) by (rule bounded_cbilinear.bounded_clinear_right)
  have [simp]: \<open>bounded_clinear (\<lambda>y. g (h x y))\<close> for x
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear g\<close>])
    using assms(2) by (rule bounded_cbilinear.bounded_clinear_right)

  assume \<open>z \<in> (\<lambda>(x, y). h x y) ` (A \<times> B) \<Longrightarrow> f z = g z\<close> for z
  then have \<open>f (h x y) = g (h x y)\<close> if \<open>x \<in> A\<close> and \<open>y \<in> B\<close> for x y
    using that by auto
  then have \<open>(\<lambda>x. f (h x y)) = (\<lambda>x. g (h x y))\<close> if \<open>y \<in> B\<close> for y
    by (intro eq_from_separatingI[OF assms(3)]) (use that in auto)
  then have \<open>(\<lambda>y. f (h x y)) = (\<lambda>y. g (h x y))\<close> for x
    apply (intro eq_from_separatingI[OF assms(4)])
    subgoal by simp
    subgoal by simp
    subgoal by meson
    done
  then have \<open>f (h x y) = g (h x y)\<close> for x y
    by meson
  with \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  show \<open>f = g\<close>
    by (rule eq_from_separatingI2[where f=f and g=g and P=bounded_clinear and S=UNIV and T=UNIV, rotated 1])
       (fact assms(1))
qed


lemma separating_set_bounded_clinear_antilinear:
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector conjugate_space) \<Rightarrow> _) A\<close>
  shows \<open>separating_set (bounded_antilinear :: (_ => 'e) \<Rightarrow> _) A\<close>
proof (rule separating_setI)
  fix f g :: \<open>'a \<Rightarrow> 'e\<close>
  assume \<open>bounded_antilinear f\<close>
  then have lin_f: \<open>bounded_clinear (to_conjugate_space o f)\<close>
    by (simp add: bounded_antilinear_o_bounded_antilinear')
  assume \<open>bounded_antilinear g\<close>
  then have lin_g: \<open>bounded_clinear (to_conjugate_space o g)\<close>
    by (simp add: bounded_antilinear_o_bounded_antilinear')
  assume \<open>f x = g x\<close> if \<open>x \<in> A\<close> for x
  then have \<open>(to_conjugate_space o f) x = (to_conjugate_space o g) x\<close> if \<open>x \<in> A\<close> for x
    by (simp add: that)
  with lin_f lin_g
  have \<open>to_conjugate_space o f = to_conjugate_space o g\<close>
    by (rule eq_from_separatingI[OF assms])
  then show \<open>f = g\<close>
    by (metis UNIV_I fun.inj_map_strong to_conjugate_space_inverse)
qed

lemma separating_set_bounded_sesquilinear_nested:
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector) \<Rightarrow> _) ((\<lambda>(x, y). h x y) ` (UNIV \<times> UNIV))\<close>
  assumes \<open>bounded_sesquilinear h\<close>
  assumes sep_A: \<open>separating_set (bounded_clinear :: (_ => 'e conjugate_space) \<Rightarrow> _) A\<close>
  assumes sep_B: \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) B\<close>
  shows \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) ((\<lambda>(x,y). h x y) ` (A \<times> B))\<close>
proof (rule separating_setI)
  fix f g :: \<open>'a \<Rightarrow> 'e\<close>
  assume [simp]: \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  have [simp]: \<open>bounded_antilinear (\<lambda>x. f (h x y))\<close> for y
    apply (rule bounded_clinear_o_bounded_antilinear[OF \<open>bounded_clinear f\<close>])
    using assms(2) by (rule bounded_sesquilinear.bounded_antilinear_left)
  have [simp]: \<open>bounded_antilinear (\<lambda>x. g (h x y))\<close> for y
    apply (rule bounded_clinear_o_bounded_antilinear[OF \<open>bounded_clinear g\<close>])
    using assms(2) by (rule bounded_sesquilinear.bounded_antilinear_left)
  have [simp]: \<open>bounded_clinear (\<lambda>y. f (h x y))\<close> for x
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear f\<close>])
    using assms(2) by (rule bounded_sesquilinear.bounded_clinear_right)
  have [simp]: \<open>bounded_clinear (\<lambda>y. g (h x y))\<close> for x
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear g\<close>])
    using assms(2) by (rule bounded_sesquilinear.bounded_clinear_right)

  from sep_A have sep_A': \<open>separating_set (bounded_antilinear :: (_ => 'e) \<Rightarrow> _) A\<close>
    by (rule separating_set_bounded_clinear_antilinear)
  assume \<open>z \<in> (\<lambda>(x, y). h x y) ` (A \<times> B) \<Longrightarrow> f z = g z\<close> for z
  then have \<open>f (h x y) = g (h x y)\<close> if \<open>x \<in> A\<close> and \<open>y \<in> B\<close> for x y
    using that by auto
  then have \<open>(\<lambda>x. f (h x y)) = (\<lambda>x. g (h x y))\<close> if \<open>y \<in> B\<close> for y
    by (intro eq_from_separatingI[OF sep_A']) (use that in auto)
  then have \<open>(\<lambda>y. f (h x y)) = (\<lambda>y. g (h x y))\<close> for x
    apply (intro eq_from_separatingI[OF sep_B])
    subgoal by simp
    subgoal by simp
    subgoal by meson
    done
  then have \<open>f (h x y) = g (h x y)\<close> for x y
    by meson
  with \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  show \<open>f = g\<close>
    by (rule eq_from_separatingI2[where f=f and g=g and P=bounded_clinear and S=UNIV and T=UNIV, rotated 1])
       (fact assms(1))
qed


lemma separating_set_clinear_cspan:
  assumes \<open>cspan S = UNIV\<close>
  shows \<open>separating_set clinear S\<close>
  using assms
  by (auto intro: complex_vector.linear_eq_on simp: separating_set_def)


subsection \<open>Product is a Complex Vector Space\<close>

(* Follows closely Product_Vector.thy *)

instantiation prod :: (complex_vector, complex_vector) complex_vector
begin

definition scaleC_prod_def:
  "scaleC r A = (scaleC r (fst A), scaleC r (snd A))"

lemma fst_scaleC [simp]: "fst (scaleC r A) = scaleC r (fst A)"
  unfolding scaleC_prod_def by simp

lemma snd_scaleC [simp]: "snd (scaleC r A) = scaleC r (snd A)"
  unfolding scaleC_prod_def by simp

proposition scaleC_Pair [simp]: "scaleC r (a, b) = (scaleC r a, scaleC r b)"
  unfolding scaleC_prod_def by simp

instance
proof
  fix a b :: complex and x y :: "'a \<times> 'b"
  show "scaleC a (x + y) = scaleC a x + scaleC a y"
    by (simp add: scaleC_add_right scaleC_prod_def)
  show "scaleC (a + b) x = scaleC a x + scaleC b x"
    by (simp add: Complex_Vector_Spaces.scaleC_prod_def scaleC_left.add)
  show "scaleC a (scaleC b x) = scaleC (a * b) x"
    by (simp add: prod_eq_iff)
  show "scaleC 1 x = x"
    by (simp add: prod_eq_iff)
  show \<open>(scaleR :: _ \<Rightarrow> _ \<Rightarrow> 'a*'b) r = (*\<^sub>C) (complex_of_real r)\<close> for r
    by (auto intro!: ext simp: scaleR_scaleC scaleC_prod_def scaleR_prod_def)
qed

end

lemma module_prod_scale_eq_scaleC: "module_prod.scale (*\<^sub>C) (*\<^sub>C) = scaleC"
  apply (rule ext) apply (rule ext)
  apply (subst module_prod.scale_def)
  subgoal by unfold_locales
  by (simp add: scaleC_prod_def)

interpretation complex_vector?: vector_space_prod "scaleC::_\<Rightarrow>_\<Rightarrow>'a::complex_vector" "scaleC::_\<Rightarrow>_\<Rightarrow>'b::complex_vector"
  rewrites "scale = ((*\<^sub>C)::_\<Rightarrow>_\<Rightarrow>('a \<times> 'b))"
    and "module.dependent (*\<^sub>C) = cdependent"
    and "module.representation (*\<^sub>C) = crepresentation"
    and "module.subspace (*\<^sub>C) = csubspace"
    and "module.span (*\<^sub>C) = cspan"
    and "vector_space.extend_basis (*\<^sub>C) = cextend_basis"
    and "vector_space.dim (*\<^sub>C) = cdim"
    and "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) = clinear"
  subgoal by unfold_locales
  subgoal by (fact module_prod_scale_eq_scaleC)
  unfolding cdependent_raw_def crepresentation_raw_def csubspace_raw_def cspan_raw_def
    cextend_basis_raw_def cdim_raw_def clinear_def
  by (rule refl)+

instance prod :: (complex_normed_vector, complex_normed_vector) complex_normed_vector 
proof
  fix c :: complex and x y :: "'a \<times> 'b"
  show "norm (c *\<^sub>C x) = cmod c * norm x"
    unfolding norm_prod_def
    apply (simp add: power_mult_distrib)
    apply (simp add: distrib_left [symmetric])
    by (simp add: real_sqrt_mult)
qed


lemma cspan_Times: \<open>cspan (S \<times> T) = cspan S \<times> cspan T\<close> if \<open>0 \<in> S\<close> and \<open>0 \<in> T\<close>
proof 
  have \<open>fst ` cspan (S \<times> T) \<subseteq> cspan S\<close>
    apply (subst complex_vector.linear_span_image[symmetric])
    using that complex_vector.module_hom_fst by auto
  moreover have \<open>snd ` cspan (S \<times> T) \<subseteq> cspan T\<close>
    apply (subst complex_vector.linear_span_image[symmetric])
    using that complex_vector.module_hom_snd by auto
  ultimately show \<open>cspan (S \<times> T) \<subseteq> cspan S \<times> cspan T\<close>
    by auto

  show \<open>cspan S \<times> cspan T \<subseteq> cspan (S \<times> T)\<close>
  proof
    fix x assume assm: \<open>x \<in> cspan S \<times> cspan T\<close>
    then have \<open>fst x \<in> cspan S\<close>
      by auto
    then obtain t1 r1 where fst_x: \<open>fst x = (\<Sum>a\<in>t1. r1 a *\<^sub>C a)\<close> and [simp]: \<open>finite t1\<close> and \<open>t1 \<subseteq> S\<close>
      by (auto simp add: complex_vector.span_explicit)
    from assm
    have \<open>snd x \<in> cspan T\<close>
      by auto
    then obtain t2 r2 where snd_x: \<open>snd x = (\<Sum>a\<in>t2. r2 a *\<^sub>C a)\<close> and [simp]: \<open>finite t2\<close> and \<open>t2 \<subseteq> T\<close>
      by (auto simp add: complex_vector.span_explicit)
    define t :: \<open>('a+'b) set\<close> and r :: \<open>('a+'b) \<Rightarrow> complex\<close> and f :: \<open>('a+'b) \<Rightarrow> ('a\<times>'b)\<close>
      where \<open>t = t1 <+> t2\<close>
      and \<open>r a = (case a of Inl a1 \<Rightarrow> r1 a1 | Inr a2 \<Rightarrow> r2 a2)\<close>
      and \<open>f a = (case a of Inl a1 \<Rightarrow> (a1,0) | Inr a2 \<Rightarrow> (0,a2))\<close>
    for a
    have \<open>finite t\<close>
      by (simp add: t_def)
    moreover have \<open>f ` t \<subseteq> S \<times> T\<close>
      using  \<open>t1 \<subseteq> S\<close> \<open>t2 \<subseteq> T\<close> that
      by (auto simp: f_def t_def)
    moreover have \<open>(fst x, snd x) = (\<Sum>a\<in>t. r a *\<^sub>C f a)\<close>
      apply (simp only: fst_x snd_x)
      by (auto simp: t_def sum.Plus r_def f_def sum_prod)
    ultimately show \<open>x \<in> cspan (S \<times> T)\<close>
      apply auto
      by (smt (verit, best) complex_vector.span_scale complex_vector.span_sum complex_vector.span_superset image_subset_iff subset_iff)
  qed
qed

lemma onorm_case_prod_plus: \<open>onorm (case_prod plus :: _ \<Rightarrow> 'a::{real_normed_vector, not_singleton}) = sqrt 2\<close>
proof -
  obtain x :: 'a where \<open>x \<noteq> 0\<close>
    apply atomize_elim by auto
  show ?thesis
    apply (rule onormI[where x=\<open>(x,x)\<close>])
    using norm_plus_leq_norm_prod apply force
    using  \<open>x \<noteq> 0\<close>
    by (auto simp add: zero_prod_def norm_prod_def real_sqrt_mult
        simp flip: scaleR_2)
qed


subsection \<open>Copying existing theorems into sublocales\<close>

context bounded_clinear begin
interpretation bounded_linear f by (rule bounded_linear)
lemmas continuous = real.continuous
lemmas uniform_limit = real.uniform_limit
lemmas Cauchy = real.Cauchy
end

context bounded_antilinear begin
interpretation bounded_linear f by (rule bounded_linear)
lemmas continuous = real.continuous
lemmas uniform_limit = real.uniform_limit
end


context bounded_cbilinear begin
interpretation bounded_bilinear prod by simp
lemmas tendsto = real.tendsto
lemmas isCont = real.isCont
lemmas scaleR_right = real.scaleR_right
lemmas scaleR_left = real.scaleR_left
end

context bounded_sesquilinear begin
interpretation bounded_bilinear prod by simp
lemmas tendsto = real.tendsto
lemmas isCont = real.isCont
lemmas scaleR_right = real.scaleR_right
lemmas scaleR_left = real.scaleR_left
end

lemmas tendsto_scaleC [tendsto_intros] =
  bounded_cbilinear.tendsto [OF bounded_cbilinear_scaleC]

unbundle no lattice_syntax

end
