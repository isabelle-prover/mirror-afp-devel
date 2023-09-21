section \<open>Library Extras\<close>
text \<open>For adding to the repository\<close>

theory Library_Extras imports
  "HOL-Analysis.Polytope" 

begin

section \<open>Preliminaries\<close>

lemma Inter_over_Union:
  "\<Inter> {\<Union> (\<F> x) |x. x \<in> S} = \<Union> {\<Inter> (G ` S) |G. \<forall>x\<in>S. G x \<in> \<F> x}" 
proof -
  have "\<And>x. \<forall>s\<in>S. \<exists>X \<in> \<F> s. x \<in> X \<Longrightarrow> \<exists>G. (\<forall>x\<in>S. G x \<in> \<F> x) \<and> (\<forall>s\<in>S. x \<in> G s)"
    by metis
  then show ?thesis
    by (auto simp flip: all_simps ex_simps)
qed

lemmas closure_Int_convex = convex_closure_inter_two

lemmas span_not_UNIV_orthogonal = span_not_univ_orthogonal

lemma convex_closure_rel_interior_Int:
  assumes "\<And>S. S\<in>\<F> \<Longrightarrow> convex (S :: 'n::euclidean_space set)"
    and "\<Inter>(rel_interior ` \<F>) \<noteq> {}"
  shows "\<Inter>(closure ` \<F>) \<subseteq> closure (\<Inter>(rel_interior ` \<F>))"
proof -
  obtain x where x: "\<forall>S\<in>\<F>. x \<in> rel_interior S"
    using assms by auto
  show ?thesis
  proof
    fix y
    assume y: "y \<in> \<Inter> (closure ` \<F>)"
    show "y \<in> closure (\<Inter>(rel_interior ` \<F>))"
    proof (cases "y=x")
      case True
      with closure_subset x show ?thesis 
        by fastforce
    next
      case False
      {         fix \<epsilon> :: real
        assume e: "\<epsilon> > 0"
        define e1 where "e1 = min 1 (\<epsilon>/norm (y - x))"
        then have e1: "e1 > 0" "e1 \<le> 1" "e1 * norm (y - x) \<le> \<epsilon>"
          using \<open>y \<noteq> x\<close> \<open>\<epsilon> > 0\<close> le_divide_eq[of e1 \<epsilon> "norm (y - x)"]
          by simp_all
        define z where "z = y - e1 *\<^sub>R (y - x)"
        {
          fix S
          assume "S \<in> \<F>"
          then have "z \<in> rel_interior S"
            using rel_interior_closure_convex_shrink[of S x y e1] assms x y e1 z_def
            by auto
        }
        then have *: "z \<in> \<Inter>(rel_interior ` \<F>)"
          by auto
        have "\<exists>x\<in>\<Inter> (rel_interior ` \<F>). dist x y \<le> \<epsilon>"
          using \<open>y \<noteq> x\<close> z_def * e1 e dist_norm[of z y]
          by force
      } then
      show ?thesis
        by (auto simp: closure_approachable_le)
    qed
  qed
qed


lemma closure_Inter_convex:
  fixes \<F> :: "'n::euclidean_space set set"
  assumes  "\<And>S. S \<in> \<F> \<Longrightarrow> convex S" and "\<Inter>(rel_interior ` \<F>) \<noteq> {}"
  shows "closure(\<Inter>\<F>) = \<Inter>(closure ` \<F>)"
proof -
  have "\<Inter>(closure ` \<F>) \<le> closure (\<Inter>(rel_interior ` \<F>))"
    by (meson assms convex_closure_rel_interior_Int)
  moreover
  have "closure (\<Inter>(rel_interior ` \<F>)) \<subseteq> closure (\<Inter>\<F>)"
    using rel_interior_inter_aux closure_mono[of "\<Inter>(rel_interior ` \<F>)" "\<Inter>\<F>"]
    by auto
  ultimately show ?thesis
    using closure_Int[of \<F>] by blast
qed

lemma closure_Inter_convex_open:
  "(\<And>S::'n::euclidean_space set. S \<in> \<F> \<Longrightarrow> convex S \<and> open S)
            \<Longrightarrow> closure(\<Inter>\<F>) = (if \<Inter>\<F> = {} then {} else \<Inter>(closure ` \<F>))"
  by (simp add: closure_Inter_convex rel_interior_open)

lemma empty_interior_subset_hyperplane_aux:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "0 \<in> S" and empty_int: "interior S = {}"
  shows "\<exists>a b. a\<noteq>0 \<and> S \<subseteq> {x. a \<bullet> x = b}"
proof -
  have False if "\<And>a. a = 0 \<or> (\<forall>b. \<exists>T \<in> S. a \<bullet> T \<noteq> b)"
  proof -
    have rel_int: "rel_interior S \<noteq> {}"
      using assms rel_interior_eq_empty by auto
    moreover 
    have "dim S \<noteq> dim (UNIV::'a set)"
      by (metis aff_dim_zero affine_hull_UNIV \<open>0 \<in> S\<close> dim_UNIV empty_int hull_inc rel_int rel_interior_interior)
    then obtain a where "a \<noteq> 0" and a: "span S \<subseteq> {x. a \<bullet> x = 0}"
      using lowdim_subset_hyperplane
      by (metis dim_UNIV dim_subset_UNIV order_less_le)
    have "span UNIV = span S"
      by (metis span_base span_not_UNIV_orthogonal that)
    then have "UNIV \<subseteq> affine hull S"
      by (simp add: \<open>0 \<in> S\<close> hull_inc affine_hull_span_0)
    ultimately show False
      using \<open>rel_interior S \<noteq> {}\<close> empty_int rel_interior_interior by blast
  qed
  then show ?thesis
    by blast
qed

lemma empty_interior_subset_hyperplane:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" and int: "interior S = {}"
  obtains a b where "a \<noteq> 0" "S \<subseteq> {x. a \<bullet> x = b}"
proof (cases "S = {}")
  case True
  then show ?thesis
    using that by blast
next
  case False
  then obtain u where "u \<in> S"
    by blast
  have "\<exists>a b. a \<noteq> 0 \<and> (\<lambda>x. x - u) ` S \<subseteq> {x. a \<bullet> x = b}"
  proof (rule empty_interior_subset_hyperplane_aux)
    show "convex ((\<lambda>x. x - u) ` S)"
      using \<open>convex S\<close> by force
    show "0 \<in> (\<lambda>x. x - u) ` S"
      by (simp add: \<open>u \<in> S\<close>)
    show "interior ((\<lambda>x. x - u) ` S) = {}"
      by (simp add: int interior_translation_subtract)
  qed
  then obtain a b where "a \<noteq> 0" and ab: "(\<lambda>x. x - u) ` S \<subseteq> {x. a \<bullet> x = b}"
    by metis
  then have "S \<subseteq> {x. a \<bullet> x = b + (a \<bullet> u)}"
    using ab by (auto simp: algebra_simps)
  then show ?thesis
    using \<open>a \<noteq> 0\<close> that by auto
qed

lemma aff_dim_psubset:
  "(affine hull S) \<subset> (affine hull T) \<Longrightarrow> aff_dim S < aff_dim T"
  by (metis aff_dim_affine_hull aff_dim_empty aff_dim_subset affine_affine_hull affine_dim_equal order_less_le)

lemma aff_dim_eq_full_gen:
  "S \<subseteq> T \<Longrightarrow> (aff_dim S = aff_dim T \<longleftrightarrow> affine hull S = affine hull T)"
  by (smt (verit, del_insts) aff_dim_affine_hull2 aff_dim_psubset hull_mono psubsetI)

lemma aff_dim_eq_full:
  fixes S :: "'n::euclidean_space set"
  shows "aff_dim S = (DIM('n)) \<longleftrightarrow> affine hull S = UNIV"
  by (metis aff_dim_UNIV aff_dim_affine_hull affine_hull_UNIV)


section \<open>Conic sets and conic hull\<close>

definition conic :: "'a::real_vector set \<Rightarrow> bool"
  where "conic S \<equiv> \<forall>x c. x \<in> S \<longrightarrow> 0 \<le> c \<longrightarrow> (c *\<^sub>R x) \<in> S"

lemma conicD: "\<lbrakk>conic S; x \<in> S; 0 \<le> c\<rbrakk> \<Longrightarrow> (c *\<^sub>R x) \<in> S"
  by (meson conic_def)

lemma subspace_imp_conic: "subspace S \<Longrightarrow> conic S"
  by (simp add: conic_def subspace_def)

lemma conic_empty [simp]: "conic {}"
  using conic_def by blast

lemma conic_UNIV: "conic UNIV"
  by (simp add: conic_def)

lemma conic_Inter: "(\<And>S. S \<in> \<F> \<Longrightarrow> conic S) \<Longrightarrow> conic(\<Inter>\<F>)"
  by (simp add: conic_def)

lemma conic_linear_image:
  "\<lbrakk>conic S; linear f\<rbrakk> \<Longrightarrow> conic(f ` S)"
  by (smt (verit) conic_def image_iff linear.scaleR)

lemma conic_linear_image_eq:
  "\<lbrakk>linear f; inj f\<rbrakk> \<Longrightarrow> conic (f ` S) \<longleftrightarrow> conic S"
  by (smt (verit) conic_def conic_linear_image inj_image_mem_iff linear_cmul)

lemma conic_mul: "\<lbrakk>conic S; x \<in> S; 0 \<le> c\<rbrakk> \<Longrightarrow> (c *\<^sub>R x) \<in> S"
  using conic_def by blast

lemma conic_conic_hull: "conic(conic hull S)"
  by (metis (no_types, lifting) conic_Inter hull_def mem_Collect_eq)

lemma conic_hull_eq: "(conic hull S = S) \<longleftrightarrow> conic S"
  by (metis conic_conic_hull hull_same)

lemma conic_hull_UNIV [simp]: "conic hull UNIV = UNIV"
  by simp

lemma conic_negations: "conic S \<Longrightarrow> conic (image uminus S)"
  by (auto simp: conic_def image_iff)

lemma conic_span [iff]: "conic(span S)"
  by (simp add: subspace_imp_conic)

lemma conic_hull_explicit:
  "conic hull S = {c *\<^sub>R x| c x. 0 \<le> c \<and> x \<in> S}"
proof (rule hull_unique)
  show "S \<subseteq> {c *\<^sub>R x |c x. 0 \<le> c \<and> x \<in> S}"
    by (metis (no_types) cone_hull_expl hull_subset)
  show "conic {c *\<^sub>R x |c x. 0 \<le> c \<and> x \<in> S}"
    using mult_nonneg_nonneg by (force simp: conic_def)
qed (auto simp: conic_def)

lemma conic_hull_as_image:
  "conic hull S = (\<lambda>z. fst z *\<^sub>R snd z) ` ({0..} \<times> S)"
  by (force simp: conic_hull_explicit)

lemma conic_hull_linear_image:
  "linear f \<Longrightarrow> conic hull f ` S = f ` (conic hull S)"
  by (force simp: conic_hull_explicit image_iff set_eq_iff linear_scale) 

lemma conic_hull_image_scale:
  assumes "\<And>x. x \<in> S \<Longrightarrow> 0 < c x"
  shows   "conic hull (\<lambda>x. c x *\<^sub>R x) ` S = conic hull S"
proof
  show "conic hull (\<lambda>x. c x *\<^sub>R x) ` S \<subseteq> conic hull S"
  proof (rule hull_minimal)
    show "(\<lambda>x. c x *\<^sub>R x) ` S \<subseteq> conic hull S"
      using assms conic_hull_explicit by fastforce
  qed (simp add: conic_conic_hull)
  show "conic hull S \<subseteq> conic hull (\<lambda>x. c x *\<^sub>R x) ` S"
  proof (rule hull_minimal)
    { fix x
      assume "x \<in> S"
      then have "x = inverse(c x) *\<^sub>R c x *\<^sub>R x"
        using assms by fastforce
      then have "x \<in> conic hull (\<lambda>x. c x *\<^sub>R x) ` S"
        by (smt (verit, best) \<open>x \<in> S\<close> assms conic_conic_hull conic_mul hull_inc image_eqI inverse_nonpositive_iff_nonpositive)
    }
    then show "S \<subseteq> conic hull (\<lambda>x. c x *\<^sub>R x) ` S" by auto
  qed (simp add: conic_conic_hull)
qed

lemma convex_conic_hull:
  assumes "convex S"
  shows "convex (conic hull S)"
proof -
  { fix c x d y and u :: real
    assume \<section>: "(0::real) \<le> c" "x \<in> S" "(0::real) \<le> d" "y \<in> S" "0 \<le> u" "u \<le> 1"
    have "\<exists>c'' x''. ((1 - u) * c) *\<^sub>R x + (u * d) *\<^sub>R y = c'' *\<^sub>R x'' \<and> 0 \<le> c'' \<and> x'' \<in> S"
    proof (cases "(1 - u) * c = 0")
      case True
      with \<open>0 \<le> d\<close> \<open>y \<in> S\<close>\<open>0 \<le> u\<close>  
      show ?thesis by force
    next
      case False
      define \<xi> where "\<xi> \<equiv> (1 - u) * c + u * d"
      have *: "c * u \<le> c"
        by (simp add: "\<section>" mult_left_le)
      have "\<xi> > 0"
        using False \<section> by (smt (verit, best) \<xi>_def split_mult_pos_le)
      then have **: "c + d * u = \<xi> + c * u"
        by (simp add: \<xi>_def mult.commute right_diff_distrib')
      show ?thesis
      proof (intro exI conjI)
        show "0 \<le> \<xi>"
          using \<open>0 < \<xi>\<close> by auto
        show "((1 - u) * c) *\<^sub>R x + (u * d) *\<^sub>R y = \<xi> *\<^sub>R (((1 - u) * c / \<xi>) *\<^sub>R x + (u * d / \<xi>) *\<^sub>R y)"
          using \<open>\<xi> > 0\<close> by (simp add: algebra_simps diff_divide_distrib)
        show "((1 - u) * c / \<xi>) *\<^sub>R x + (u * d / \<xi>) *\<^sub>R y \<in> S"
          using \<open>0 < \<xi>\<close> 
          by (intro convexD [OF assms]) (auto simp: \<section> field_split_simps * **)
      qed
    qed
  }
  then show ?thesis
    by (auto simp add: conic_hull_explicit convex_alt)
qed

lemma conic_halfspace_le: "conic {x. a \<bullet> x \<le> 0}"
  by (auto simp: conic_def mult_le_0_iff)

lemma conic_halfspace_ge: "conic {x. a \<bullet> x \<ge> 0}"
  by (auto simp: conic_def mult_le_0_iff)

lemma conic_hull_empty [simp]: "conic hull {} = {}"
  by (simp add: conic_hull_eq)

lemma conic_contains_0: "conic S \<Longrightarrow> (0 \<in> S \<longleftrightarrow> S \<noteq> {})"
  by (simp add: Convex.cone_def cone_contains_0 conic_def)

lemma conic_hull_eq_empty: "conic hull S = {} \<longleftrightarrow> (S = {})"
  using conic_hull_explicit by fastforce

lemma conic_sums: "\<lbrakk>conic S; conic T\<rbrakk> \<Longrightarrow> conic (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
  by (simp add: conic_def) (metis scaleR_right_distrib)

lemma conic_Times: "\<lbrakk>conic S; conic T\<rbrakk> \<Longrightarrow> conic(S \<times> T)"
  by (auto simp: conic_def)

lemma conic_Times_eq:
  "conic(S \<times> T) \<longleftrightarrow> S = {} \<or> T = {} \<or> conic S \<and> conic T" (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    by (force simp: conic_def)
  show "?rhs \<Longrightarrow> ?lhs"
    by (force simp: conic_Times)
qed

lemma conic_hull_0 [simp]: "conic hull {0} = {0}"
  by (simp add: conic_hull_eq subspace_imp_conic)

lemma conic_hull_contains_0 [simp]: "0 \<in> conic hull S \<longleftrightarrow> (S \<noteq> {})"
  by (simp add: conic_conic_hull conic_contains_0 conic_hull_eq_empty)

lemma conic_hull_eq_sing:
  "conic hull S = {x} \<longleftrightarrow> S = {0} \<and> x = 0"
proof
  show "conic hull S = {x} \<Longrightarrow> S = {0} \<and> x = 0"
    by (metis conic_conic_hull conic_contains_0 conic_def conic_hull_eq hull_inc insert_not_empty singleton_iff)
qed simp

lemma conic_hull_Int_affine_hull:
  assumes "T \<subseteq> S" "0 \<notin> affine hull S"
  shows "(conic hull T) \<inter> (affine hull S) = T"
proof -
  have TaffS: "T \<subseteq> affine hull S"
    using \<open>T \<subseteq> S\<close> hull_subset by fastforce
  moreover
  { fix c x
    assume "c *\<^sub>R x \<in> affine hull S"
      and "0 \<le> c"
      and "x \<in> T"
    have "c *\<^sub>R x \<in> T"
    proof (cases "c=1")
      case True
      then show ?thesis
        by (simp add: \<open>x \<in> T\<close>)
    next
      case False
      then have "x /\<^sub>R (1 - c) = x + (c * inverse (1 - c)) *\<^sub>R x"
        by (smt (verit, ccfv_SIG) diff_add_cancel mult.commute real_vector_affinity_eq scaleR_collapse scaleR_scaleR)
      then have "0 = inverse(1 - c) *\<^sub>R c *\<^sub>R x + (1 - inverse(1 - c)) *\<^sub>R x"
        by (simp add: algebra_simps)
      then have "0 \<in> affine hull S"
        by (smt (verit) \<open>c *\<^sub>R x \<in> affine hull S\<close> \<open>x \<in> T\<close> affine_affine_hull TaffS in_mono mem_affine)
      then show ?thesis
        using assms by auto        
    qed }
  then have "conic hull T \<inter> affine hull S \<subseteq> T"
    by (auto simp: conic_hull_explicit)
  ultimately show ?thesis
    by (auto simp: hull_inc)
qed


lemma open_in_subset_relative_interior:
  fixes S :: "'a::euclidean_space set"
  shows "openin (top_of_set (affine hull T)) S \<Longrightarrow> (S \<subseteq> rel_interior T) = (S \<subseteq> T)"
  by (meson order.trans rel_interior_maximal rel_interior_subset)


lemma conic_hull_eq_span_affine_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "0 \<in> rel_interior S"
  shows "conic hull S = span S \<and> conic hull S = affine hull S"
proof -
  obtain \<epsilon> where "\<epsilon>>0" and \<epsilon>: "cball 0 \<epsilon> \<inter> affine hull S \<subseteq> S"
    using assms mem_rel_interior_cball by blast
  have *: "affine hull S = span S"
    by (meson affine_hull_span_0 assms hull_inc mem_rel_interior_cball)
  moreover
  have "conic hull S \<subseteq> span S"
    by (simp add: hull_minimal span_superset)
  moreover
    { fix x
    assume "x \<in> affine hull S"
    have "x \<in> conic hull S"
    proof (cases "x=0")
      case True
      then show ?thesis
        using \<open>x \<in> affine hull S\<close> by auto
    next
      case False
      then have "(\<epsilon> / norm x) *\<^sub>R x \<in> cball 0 \<epsilon> \<inter> affine hull S"
        using \<open>0 < \<epsilon>\<close> \<open>x \<in> affine hull S\<close> * span_mul by fastforce
      then have "(\<epsilon> / norm x) *\<^sub>R x \<in> S"
        by (meson \<epsilon> subsetD)
      then have "\<exists>c xa. x = c *\<^sub>R xa \<and> 0 \<le> c \<and> xa \<in> S"
        by (smt (verit, del_insts) \<open>0 < \<epsilon>\<close> divide_nonneg_nonneg eq_vector_fraction_iff norm_eq_zero norm_ge_zero)
      then show ?thesis
        by (simp add: conic_hull_explicit)
    qed
  }
  then have "affine hull S \<subseteq> conic hull S"
    by auto
  ultimately show ?thesis
    by blast
qed

lemma conic_hull_eq_span:
  fixes S :: "'a::euclidean_space set"
  assumes "0 \<in> rel_interior S"
  shows "conic hull S = span S"
  by (simp add: assms conic_hull_eq_span_affine_hull)

lemma conic_hull_eq_affine_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "0 \<in> rel_interior S"
  shows "conic hull S = affine hull S"
  using assms conic_hull_eq_span_affine_hull by blast

lemma conic_hull_eq_span_eq:
  fixes S :: "'a::euclidean_space set"
  shows "0 \<in> rel_interior(conic hull S) \<longleftrightarrow> conic hull S = span S" (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    by (metis conic_hull_eq_span conic_span hull_hull hull_minimal hull_subset span_eq)
  show "?rhs \<Longrightarrow> ?lhs"
    by (metis rel_interior_affine subspace_affine subspace_span)
qed

section\<open>Closure of conic hulls\<close>

proposition closedin_conic_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "compact T" "0 \<notin> T" "T \<subseteq> S"
  shows   "closedin (top_of_set (conic hull S)) (conic hull T)"
proof -
  have **: "compact ({0..} \<times> T \<inter> (\<lambda>z. fst z *\<^sub>R snd z) -` K)" (is "compact ?L")
    if "K \<subseteq> (\<lambda>z. (fst z) *\<^sub>R snd z) ` ({0..} \<times> S)" "compact K" for K
  proof -
    obtain r where "r > 0" and r: "\<And>x. x \<in> K \<Longrightarrow> norm x \<le> r"
      by (metis \<open>compact K\<close> bounded_normE compact_imp_bounded)
    show ?thesis
      unfolding compact_eq_bounded_closed
    proof
      have "bounded ({0..r / setdist{0}T} \<times> T)"
        by (simp add: assms(1) bounded_Times compact_imp_bounded)
      moreover 
      { fix a b
        assume "a *\<^sub>R b \<in> K" and "b \<in> T" and "0 \<le> a"
        have "setdist {0} T \<noteq> 0"
          using \<open>b \<in> T\<close> assms compact_imp_closed setdist_eq_0_closed by auto
        then have T0: "setdist {0} T > 0"
          using less_eq_real_def by fastforce
        then have "a * setdist {0} T \<le> r"
          by (smt (verit, ccfv_SIG) \<open>0 \<le> a\<close> \<open>a *\<^sub>R b \<in> K\<close> \<open>b \<in> T\<close> dist_0_norm mult_mono' norm_scaleR r setdist_le_dist singletonI)
        with T0 \<open>r>0\<close> have "a \<le> r / setdist {0} T"
          by (simp add: divide_simps)
      }
      then have "?L \<subseteq> ({0..r / setdist{0}T} \<times> T)" by auto
      ultimately show "bounded ?L"
        by (meson bounded_subset)
      show "closed ?L"
      proof (rule continuous_closed_preimage)
        show "continuous_on ({0..} \<times> T) (\<lambda>z. fst z *\<^sub>R snd z)"
          by (intro continuous_intros)
        show "closed ({0::real..} \<times> T)"
          by (simp add: assms(1) closed_Times compact_imp_closed)
        show "closed K"
          by (simp add: compact_imp_closed that(2))
      qed
    qed
  qed
  show ?thesis
    unfolding conic_hull_as_image
  proof (rule proper_map)
    show  "compact ({0..} \<times> T \<inter> (\<lambda>z. fst z *\<^sub>R snd z) -` K)" (is "compact ?L")
      if "K \<subseteq> (\<lambda>z. (fst z) *\<^sub>R snd z) ` ({0..} \<times> S)" "compact K" for K
    proof -
      obtain r where "r > 0" and r: "\<And>x. x \<in> K \<Longrightarrow> norm x \<le> r"
        by (metis \<open>compact K\<close> bounded_normE compact_imp_bounded)
      show ?thesis
        unfolding compact_eq_bounded_closed
      proof
        have "bounded ({0..r / setdist{0}T} \<times> T)"
          by (simp add: assms(1) bounded_Times compact_imp_bounded)
        moreover 
        { fix a b
          assume "a *\<^sub>R b \<in> K" and "b \<in> T" and "0 \<le> a"
          have "setdist {0} T \<noteq> 0"
            using \<open>b \<in> T\<close> assms compact_imp_closed setdist_eq_0_closed by auto
          then have T0: "setdist {0} T > 0"
            using less_eq_real_def by fastforce
          then have "a * setdist {0} T \<le> r"
            by (smt (verit, ccfv_SIG) \<open>0 \<le> a\<close> \<open>a *\<^sub>R b \<in> K\<close> \<open>b \<in> T\<close> dist_0_norm mult_mono' norm_scaleR r setdist_le_dist singletonI)
          with T0 \<open>r>0\<close> have "a \<le> r / setdist {0} T"
            by (simp add: divide_simps)
        }
        then have "?L \<subseteq> ({0..r / setdist{0}T} \<times> T)" by auto
        ultimately show "bounded ?L"
          by (meson bounded_subset)
        show "closed ?L"
        proof (rule continuous_closed_preimage)
          show "continuous_on ({0..} \<times> T) (\<lambda>z. fst z *\<^sub>R snd z)"
            by (intro continuous_intros)
          show "closed ({0::real..} \<times> T)"
            by (simp add: assms(1) closed_Times compact_imp_closed)
          show "closed K"
            by (simp add: compact_imp_closed that(2))
        qed
      qed
    qed
    show "(\<lambda>z. fst z *\<^sub>R snd z) ` ({0::real..} \<times> T) \<subseteq> (\<lambda>z. fst z *\<^sub>R snd z) ` ({0..} \<times> S)"
      using \<open>T \<subseteq> S\<close> by force
  qed auto
qed

lemma closed_conic_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "0 \<in> rel_interior S \<or> compact S \<and> 0 \<notin> S"
  shows   "closed(conic hull S)"
  using assms
proof
  assume "0 \<in> rel_interior S"
  then show "closed (conic hull S)"
    by (simp add: conic_hull_eq_span)
next
  assume "compact S \<and> 0 \<notin> S"
  then have "closedin (top_of_set UNIV) (conic hull S)"
    using closedin_conic_hull by force
  then show "closed (conic hull S)"
    by simp
qed 

lemma conic_closure:
  fixes S :: "'a::euclidean_space set"
  shows "conic S \<Longrightarrow> conic(closure S)"
  by (meson Convex.cone_def cone_closure conic_def)

lemma closure_conic_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "0 \<in> rel_interior S \<or> bounded S \<and> ~(0 \<in> closure S)"
  shows   "closure(conic hull S) = conic hull (closure S)"
  using assms
proof
  assume "0 \<in> rel_interior S"
  then show "closure (conic hull S) = conic hull closure S"
    by (metis closed_affine_hull closure_closed closure_same_affine_hull closure_subset conic_hull_eq_affine_hull subsetD subset_rel_interior)
next
  have "\<And>x. x \<in> conic hull closure S \<Longrightarrow> x \<in> closure (conic hull S)"
    by (metis (no_types, opaque_lifting) closure_mono conic_closure conic_conic_hull subset_eq subset_hull)
  moreover 
  assume "bounded S \<and> 0 \<notin> closure S"
  then have "\<And>x. x \<in> closure (conic hull S) \<Longrightarrow> x \<in> conic hull closure S"
    by (metis closed_conic_hull closure_Un_frontier closure_closed closure_mono compact_closure hull_Un_subset le_sup_iff subsetD)
  ultimately show "closure (conic hull S) = conic hull closure S"
    by blast
qed


lemma faces_of_linear_image:
  "\<lbrakk>linear f; inj f\<rbrakk> \<Longrightarrow> {T. T face_of (f ` S)} = (image f) ` {T. T face_of S}"
  by (smt (verit) Collect_cong face_of_def face_of_linear_image setcompr_eq_image subset_imageE)

lemma face_of_conic:
  assumes "conic S" "f face_of S"
  shows "conic f"
  unfolding conic_def
proof (intro strip)
  fix x and c::real
  assume "x \<in> f" and "0 \<le> c"
  have f: "\<And>a b x. \<lbrakk>a \<in> S; b \<in> S; x \<in> f; x \<in> open_segment a b\<rbrakk> \<Longrightarrow> a \<in> f \<and> b \<in> f"
    using \<open>f face_of S\<close> face_ofD by blast
  show "c *\<^sub>R x \<in> f"
  proof (cases "x=0 \<or> c=1")
    case True
    then show ?thesis
      using \<open>x \<in> f\<close> by auto
  next
    case False
    with \<open>0 \<le> c\<close> obtain d e where de: "0 \<le> d" "0 \<le> e" "d < 1" "1 < e" "d < e" "(d = c \<or> e = c)"
      apply (simp add: neq_iff)
      by (metis gt_ex less_eq_real_def order_less_le_trans zero_less_one)
    then obtain [simp]: "c *\<^sub>R x \<in> S" "e *\<^sub>R x \<in> S" \<open>x \<in> S\<close>
      using \<open>x \<in> f\<close> assms conic_mul face_of_imp_subset by blast
    have "x \<in> open_segment (d *\<^sub>R x) (e *\<^sub>R x)" if "c *\<^sub>R x \<notin> f"
      using de False that
      apply (simp add: in_segment)
      apply (rule exI [where x="(1 - d) / (e - d)"])
      apply (simp add: field_simps)
      by (smt (verit, del_insts) add_divide_distrib divide_self scaleR_collapse)
    then show ?thesis
      using \<open>conic S\<close> f [of "d *\<^sub>R x" "e *\<^sub>R x" x] de \<open>x \<in> f\<close>
      by (force simp: conic_def in_segment)
  qed
qed

lemma extreme_point_of_conic:
  assumes "conic S" and x: "x extreme_point_of S"
  shows "x = 0"
proof -
  have "{x} face_of S"
    by (simp add: face_of_singleton x)
  then have "conic{x}"
    using assms(1) face_of_conic by blast
  then show ?thesis
    by (force simp: conic_def)
qed

section \<open>Convex cones and corresponding hulls\<close>

definition convex_cone :: "'a::real_vector set \<Rightarrow> bool"
  where "convex_cone \<equiv> \<lambda>S. S \<noteq> {} \<and> convex S \<and> conic S"

lemma convex_cone_iff:
  "convex_cone S \<longleftrightarrow>
              0 \<in> S \<and> (\<forall>x \<in> S. \<forall>y \<in> S. x + y \<in> S) \<and> (\<forall>x \<in> S. \<forall>c\<ge>0. c *\<^sub>R x \<in> S)"
  by (metis cone_def conic_contains_0 conic_def convex_cone convex_cone_def)

lemma convex_cone_add: "\<lbrakk>convex_cone S; x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> x+y \<in> S"
  by (simp add: convex_cone_iff)

lemma convex_cone_scaleR: "\<lbrakk>convex_cone S; 0 \<le> c; x \<in> S\<rbrakk> \<Longrightarrow> c *\<^sub>R x \<in> S"
  by (simp add: convex_cone_iff)

lemma convex_cone_nonempty: "convex_cone S \<Longrightarrow> S \<noteq> {}"
  by (simp add: convex_cone_def)

lemma convex_cone_linear_image:
  "convex_cone S \<and> linear f \<Longrightarrow> convex_cone(f ` S)"
  by (simp add: conic_linear_image convex_cone_def convex_linear_image)

lemma convex_cone_linear_image_eq:
  "\<lbrakk>linear f; inj f\<rbrakk> \<Longrightarrow> (convex_cone(f ` S) \<longleftrightarrow> convex_cone S)"
  by (simp add: conic_linear_image_eq convex_cone_def)

lemma convex_cone_halfspace_ge: "convex_cone {x. a \<bullet> x \<ge> 0}"
  by (simp add: convex_cone_iff inner_simps(2))

lemma convex_cone_halfspace_le: "convex_cone {x. a \<bullet> x \<le> 0}"
  by (simp add: convex_cone_iff inner_right_distrib mult_nonneg_nonpos)

lemma convex_cone_contains_0: "convex_cone S \<Longrightarrow> 0 \<in> S"
  using convex_cone_iff by blast

lemma convex_cone_Inter:
  "(\<And>S. S \<in> f \<Longrightarrow> convex_cone S) \<Longrightarrow> convex_cone(\<Inter> f)"
  by (simp add: convex_cone_iff)

lemma convex_cone_convex_cone_hull: "convex_cone(convex_cone hull S)"
  by (metis (no_types, lifting) convex_cone_Inter hull_def mem_Collect_eq)

lemma convex_convex_cone_hull: "convex(convex_cone hull S)"
  by (meson convex_cone_convex_cone_hull convex_cone_def)

lemma conic_convex_cone_hull: "conic(convex_cone hull S)"
  by (metis convex_cone_convex_cone_hull convex_cone_def)

lemma convex_cone_hull_nonempty: "convex_cone hull S \<noteq> {}"
  by (simp add: convex_cone_convex_cone_hull convex_cone_nonempty)

lemma convex_cone_hull_contains_0: "0 \<in> convex_cone hull S"
  by (simp add: convex_cone_contains_0 convex_cone_convex_cone_hull)

lemma convex_cone_hull_add:
  "\<lbrakk>x \<in> convex_cone hull S; y \<in> convex_cone hull S\<rbrakk> \<Longrightarrow> x + y \<in> convex_cone hull S"
  by (simp add: convex_cone_add convex_cone_convex_cone_hull)

lemma convex_cone_hull_mul:
  "\<lbrakk>x \<in> convex_cone hull S; 0 \<le> c\<rbrakk> \<Longrightarrow> (c *\<^sub>R x) \<in> convex_cone hull S"
  by (simp add: conic_convex_cone_hull conic_mul)

lemma convex_cone_sums:
  "\<lbrakk>convex_cone S; convex_cone T\<rbrakk> \<Longrightarrow> convex_cone (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
  by (simp add: convex_cone_def conic_sums convex_sums)

lemma convex_cone_Times:
  "\<lbrakk>convex_cone S; convex_cone T\<rbrakk> \<Longrightarrow> convex_cone(S \<times> T)"
  by (simp add: conic_Times convex_Times convex_cone_def)

lemma convex_cone_Times_D1: "convex_cone (S \<times> T) \<Longrightarrow> convex_cone S"
  by (metis Times_empty conic_Times_eq convex_cone_def convex_convex_hull convex_hull_Times hull_same times_eq_iff)

lemma convex_cone_Times_eq:
  "convex_cone(S \<times> T) \<longleftrightarrow> convex_cone S \<and> convex_cone T" 
proof (cases "S={} \<or> T={}")
  case True
  then show ?thesis 
    by (auto dest: convex_cone_nonempty)
next
  case False
  then have "convex_cone (S \<times> T) \<Longrightarrow> convex_cone T"
    by (metis conic_Times_eq convex_cone_def convex_convex_hull convex_hull_Times hull_same times_eq_iff)
  then show ?thesis
    using convex_cone_Times convex_cone_Times_D1 by blast 
qed


lemma convex_cone_hull_Un:
  "convex_cone hull(S \<union> T) = (\<Union>x \<in> convex_cone hull S. \<Union>y \<in> convex_cone hull T. {x + y})"
  (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof (rule hull_minimal)
    show "S \<union> T \<subseteq> (\<Union>x\<in>convex_cone hull S. \<Union>y\<in>convex_cone hull T. {x + y})"
      apply (clarsimp simp: subset_iff)
      by (metis add_0 convex_cone_hull_contains_0 group_cancel.rule0 hull_inc)
    show "convex_cone (\<Union>x\<in>convex_cone hull S. \<Union>y\<in>convex_cone hull T. {x + y})"
      by (simp add: convex_cone_convex_cone_hull convex_cone_sums)
  qed
next
  show "?rhs \<subseteq> ?lhs"
    by clarify (metis convex_cone_hull_add hull_mono le_sup_iff subsetD subsetI)
qed

lemma convex_cone_singleton [iff]: "convex_cone {0}"
  by (simp add: convex_cone_iff)

lemma convex_hull_subset_convex_cone_hull:
  "convex hull S \<subseteq> convex_cone hull S"
  by (simp add: convex_convex_cone_hull hull_minimal hull_subset)


lemma conic_hull_subset_convex_cone_hull:
  "conic hull S \<subseteq> convex_cone hull S"
  by (simp add: conic_convex_cone_hull hull_minimal hull_subset)

lemma subspace_imp_convex_cone: "subspace S \<Longrightarrow> convex_cone S"
  by (simp add: convex_cone_iff subspace_def)

lemma convex_cone_span: "convex_cone(span S)"
  by (simp add: subspace_imp_convex_cone)

lemma convex_cone_negations:
  "convex_cone S \<Longrightarrow> convex_cone (image uminus S)"
  by (simp add: convex_cone_linear_image module_hom_uminus)

lemma subspace_convex_cone_symmetric:
  "subspace S \<longleftrightarrow> convex_cone S \<and> (\<forall>x \<in> S. -x \<in> S)"
  by (smt (verit) convex_cone_iff scaleR_left.minus subspace_def subspace_neg)



lemma convex_cone_hull_separate_nonempty:
  assumes "S \<noteq> {}"
  shows "convex_cone hull S = conic hull (convex hull S)"   (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    by (simp add: assms conic_conic_hull conic_hull_eq_empty convex_cone_def convex_conic_hull hull_inc hull_minimal subsetI)
  show "?rhs \<subseteq> ?lhs"
    by (simp add: conic_convex_cone_hull convex_hull_subset_convex_cone_hull subset_hull)
qed

lemma convex_cone_hull_empty [simp]: "convex_cone hull {} = {0}"
  by (metis convex_cone_hull_contains_0 convex_cone_singleton hull_redundant hull_same)

lemma convex_cone_hull_separate:
  "convex_cone hull S = insert 0 (conic hull (convex hull S))"
  by (cases "S={}") (simp_all add: convex_cone_hull_separate_nonempty insert_absorb)

lemma convex_cone_hull_convex_hull_nonempty:
  "S \<noteq> {} \<Longrightarrow> convex_cone hull S = (\<Union>x \<in> convex hull S. \<Union>c\<in>{0..}. {c *\<^sub>R x})"
  by (force simp: convex_cone_hull_separate_nonempty conic_hull_as_image)


lemma convex_cone_hull_convex_hull:
  "convex_cone hull S = insert 0 (\<Union>x \<in> convex hull S. \<Union>c\<in>{0..}. {c *\<^sub>R x})"
  by (force simp: convex_cone_hull_separate conic_hull_as_image)

lemma convex_cone_hull_linear_image:
  "linear f \<Longrightarrow> convex_cone hull (f ` S) = image f (convex_cone hull S)"
  by (metis (no_types, lifting) conic_hull_linear_image convex_cone_hull_separate convex_hull_linear_image image_insert linear_0)

subsection \<open>Finitely generated cone is polyhedral, and hence closed\<close>

proposition polyhedron_convex_cone_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "finite S"
  shows "polyhedron(convex_cone hull S)"
proof (cases "S = {}")
  case True
  then show ?thesis
    by (simp add: affine_imp_polyhedron)
next
  case False
  then have "polyhedron(convex hull (insert 0 S))"
    by (simp add: assms polyhedron_convex_hull)
  then obtain F a b where "finite F" 
    and F: "convex hull (insert 0 S) = \<Inter> F" 
    and ab: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
    unfolding polyhedron_def by metis
  then have "F \<noteq> {}"
    by (metis bounded_convex_hull finite_imp_bounded Inf_empty assms finite_insert not_bounded_UNIV)
  show ?thesis
    unfolding polyhedron_def
  proof (intro exI conjI)
    show "convex_cone hull S = \<Inter> {h \<in> F. b h = 0}" (is "?lhs = ?rhs")
    proof
      show "?lhs \<subseteq> ?rhs"
      proof (rule hull_minimal)
        show "S \<subseteq> \<Inter> {h \<in> F. b h = 0}"
          by (smt (verit, best) F InterE InterI hull_subset insert_subset mem_Collect_eq subset_eq)
        have "\<And>S. \<lbrakk>S \<in> F; b S = 0\<rbrakk> \<Longrightarrow> convex_cone S"
          by (metis ab convex_cone_halfspace_le)
        then show "convex_cone (\<Inter> {h \<in> F. b h = 0})"
          by (force intro: convex_cone_Inter)
      qed
      have "x \<in> convex_cone hull S"
        if x: "\<And>h. \<lbrakk>h \<in> F; b h = 0\<rbrakk> \<Longrightarrow> x \<in> h" for x
      proof -
        have "\<exists>t. 0 < t \<and> (t *\<^sub>R x) \<in> h" if "h \<in> F" for h
        proof (cases "b h = 0")
          case True
          then show ?thesis
            by (metis x linordered_field_no_ub mult_1 scaleR_one that zero_less_mult_iff)
        next
          case False
          then have "b h > 0"
            by (smt (verit, del_insts) F InterE ab hull_subset inner_zero_right insert_subset mem_Collect_eq that)
          then have "0 \<in> interior {x. a h \<bullet> x \<le> b h}"
            by (simp add: ab that)
          then have "0 \<in> interior h"
            using ab that by auto
          then obtain \<epsilon> where "0 < \<epsilon>" and \<epsilon>: "ball 0 \<epsilon> \<subseteq> h"
            using mem_interior by blast
          show ?thesis
          proof (cases "x=0")
            case True
            then show ?thesis
              using \<epsilon> \<open>0 < \<epsilon>\<close> by auto
          next
            case False
            with \<epsilon> \<open>0 < \<epsilon>\<close> show ?thesis
              by (intro exI [where x="\<epsilon> / (2 * norm x)"]) (auto simp: divide_simps)
          qed
        qed
        then obtain t where t: "\<And>h. h \<in> F \<Longrightarrow> 0 < t h \<and> (t h *\<^sub>R x) \<in> h" 
          by metis
        then have "Inf (t ` F) *\<^sub>R x /\<^sub>R Inf (t ` F) = x"
          by (smt (verit) \<open>F \<noteq> {}\<close> \<open>finite F\<close> field_simps(58) finite_imageI finite_less_Inf_iff image_iff image_is_empty)
        moreover have "Inf (t ` F) *\<^sub>R x /\<^sub>R Inf (t ` F) \<in> convex_cone hull S"
        proof (rule conicD [OF conic_convex_cone_hull])
          have "Inf (t ` F) *\<^sub>R x \<in> \<Inter> F"
          proof clarify
            fix h
            assume  "h \<in> F"
            have eq: "Inf (t ` F) *\<^sub>R x = (1 - Inf(t ` F) / t h) *\<^sub>R 0 + (Inf(t ` F) / t h) *\<^sub>R t h *\<^sub>R x"
              using \<open>h \<in> F\<close> t by force
            show "Inf (t ` F) *\<^sub>R x \<in> h"
              unfolding eq
            proof (rule convexD_alt)
              have "h = {x. a h \<bullet> x \<le> b h}"
                by (simp add: \<open>h \<in> F\<close> ab)
              then show "convex h"
                by (metis convex_halfspace_le)
              show "0 \<in> h"
                by (metis F InterE \<open>h \<in> F\<close> hull_subset insertCI subsetD)
              show "t h *\<^sub>R x \<in> h"
                by (simp add: \<open>h \<in> F\<close> t)
              show "0 \<le> Inf (t ` F) / t h"
                by (metis \<open>F \<noteq> {}\<close> \<open>h \<in> F\<close> cINF_greatest divide_nonneg_pos less_eq_real_def t)
              show "Inf (t ` F) / t h \<le> 1"
                by (simp add: \<open>finite F\<close> \<open>h \<in> F\<close> cInf_le_finite t)
            qed
          qed
          moreover have "convex hull (insert 0 S) \<subseteq> convex_cone hull S"
            by (simp add: convex_cone_hull_contains_0 convex_convex_cone_hull hull_minimal hull_subset)
          ultimately show "Inf (t ` F) *\<^sub>R x \<in> convex_cone hull S"
            using F by blast
          show "0 \<le> inverse (Inf (t ` F))"
            using t by (simp add: \<open>F \<noteq> {}\<close> \<open>finite F\<close> finite_less_Inf_iff less_eq_real_def)
        qed
        ultimately show ?thesis
          by auto
      qed
      then show "?rhs \<subseteq> ?lhs"
        by auto
    qed
    show "\<forall>h\<in>{h \<in> F. b h = 0}. \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b}"
      using ab by blast
  qed (auto simp: \<open>finite F\<close>)
qed


lemma closed_convex_cone_hull:
  fixes S :: "'a::euclidean_space set"
  shows "finite S \<Longrightarrow> closed(convex_cone hull S)"
  by (simp add: polyhedron_convex_cone_hull polyhedron_imp_closed)

lemma polyhedron_convex_cone_hull_polytope:
  fixes S :: "'a::euclidean_space set"
  shows "polytope S \<Longrightarrow> polyhedron(convex_cone hull S)"
  by (metis convex_cone_hull_separate hull_hull polyhedron_convex_cone_hull polytope_def)

lemma polyhedron_conic_hull_polytope:
  fixes S :: "'a::euclidean_space set"
  shows "polytope S \<Longrightarrow> polyhedron(conic hull S)"
  by (metis conic_hull_eq_empty convex_cone_hull_separate_nonempty hull_hull polyhedron_convex_cone_hull_polytope polyhedron_empty polytope_def)

lemma closed_conic_hull_strong:
  fixes S :: "'a::euclidean_space set"
  shows "0 \<in> rel_interior S \<or> polytope S \<or> compact S \<and> ~(0 \<in> S) \<Longrightarrow> closed(conic hull S)"
  using closed_conic_hull polyhedron_conic_hull_polytope polyhedron_imp_closed by blast

end