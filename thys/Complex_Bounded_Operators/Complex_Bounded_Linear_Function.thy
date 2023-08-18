section \<open>\<open>Complex_Bounded_Linear_Function\<close> -- Complex bounded linear functions (bounded operators)\<close>

(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)

theory Complex_Bounded_Linear_Function
  imports
    "HOL-Types_To_Sets.Types_To_Sets"
    Banach_Steinhaus.Banach_Steinhaus
    Complex_Inner_Product
    One_Dimensional_Spaces
    Complex_Bounded_Linear_Function0
    "HOL-Library.Function_Algebras"
begin

unbundle lattice_syntax

subsection \<open>Misc basic facts and declarations\<close>

notation cblinfun_apply (infixr "*\<^sub>V" 70)

lemma id_cblinfun_apply[simp]: "id_cblinfun *\<^sub>V \<psi> = \<psi>"
  by simp

lemma apply_id_cblinfun[simp]: \<open>(*\<^sub>V) id_cblinfun = id\<close>
  by auto

lemma isCont_cblinfun_apply[simp]: "isCont ((*\<^sub>V) A) \<psi>"
  by transfer (simp add: clinear_continuous_at)

declare cblinfun.scaleC_left[simp]

lemma cblinfun_apply_clinear[simp]: \<open>clinear (cblinfun_apply A)\<close>
  using bounded_clinear.axioms(1) cblinfun_apply by blast

lemma cblinfun_cinner_eqI:
  fixes A B :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>\<And>\<psi>. cinner \<psi> (A *\<^sub>V \<psi>) = cinner \<psi> (B *\<^sub>V \<psi>)\<close>
  shows \<open>A = B\<close>
proof -
  define C where \<open>C = A - B\<close>
  have C0[simp]: \<open>cinner \<psi> (C \<psi>) = 0\<close> for \<psi>
    by (simp add: C_def assms cblinfun.diff_left cinner_diff_right)
  { fix f g \<alpha>
    have \<open>0 = cinner (f + \<alpha> *\<^sub>C g) (C *\<^sub>V (f + \<alpha> *\<^sub>C g))\<close>
      by (simp add: cinner_diff_right minus_cblinfun.rep_eq)
    also have \<open>\<dots> = \<alpha> *\<^sub>C cinner f (C g) + cnj \<alpha> *\<^sub>C cinner g (C f)\<close>
      by (smt (z3) C0 add.commute add.right_neutral cblinfun.add_right cblinfun.scaleC_right cblinfun_cinner_right.rep_eq cinner_add_left cinner_scaleC_left complex_scaleC_def)
    finally have \<open>\<alpha> *\<^sub>C cinner f (C g) = - cnj \<alpha> *\<^sub>C cinner g (C f)\<close>
      by (simp add: eq_neg_iff_add_eq_0)
  }
  then have \<open>cinner f (C g) = 0\<close> for f g
    by (metis complex_cnj_i complex_cnj_one complex_vector.scale_cancel_right complex_vector.scale_left_imp_eq equation_minus_iff i_squared mult_eq_0_iff one_neq_neg_one)
  then have \<open>C g = 0\<close> for g
    using cinner_eq_zero_iff by blast
  then have \<open>C = 0\<close>
    by (simp add: cblinfun_eqI)
  then show \<open>A = B\<close>
    using C_def by auto
qed

lemma id_cblinfun_not_0[simp]: \<open>(id_cblinfun :: 'a::{complex_normed_vector, not_singleton} \<Rightarrow>\<^sub>C\<^sub>L _) \<noteq> 0\<close>
  by (metis (full_types) Extra_General.UNIV_not_singleton cblinfun.zero_left cblinfun_id_cblinfun_apply ex_norm1 norm_zero one_neq_zero)

lemma cblinfun_norm_geqI:
  assumes \<open>norm (f *\<^sub>V x) / norm x \<ge> K\<close>
  shows \<open>norm f \<ge> K\<close>
  using assms by transfer (smt (z3) bounded_clinear.bounded_linear le_onorm)

(* This lemma is proven in Complex_Bounded_Linear_Function0 but we add the [simp]
   only here because we try to keep Complex_Bounded_Linear_Function0 as close to
   Bounded_Linear_Function as possible. *)
declare scaleC_conv_of_complex[simp]

lemma cblinfun_eq_0_on_span:
  fixes S::\<open>'a::complex_normed_vector set\<close>
  assumes "x \<in> cspan S"
    and "\<And>s. s\<in>S \<Longrightarrow> F *\<^sub>V s = 0"
  shows \<open>F *\<^sub>V x = 0\<close>
  using bounded_clinear.axioms(1) cblinfun_apply assms complex_vector.linear_eq_0_on_span
  by blast

lemma cblinfun_eq_on_span:
  fixes S::\<open>'a::complex_normed_vector set\<close>
  assumes "x \<in> cspan S"
    and "\<And>s. s\<in>S \<Longrightarrow> F *\<^sub>V s = G *\<^sub>V s"
  shows \<open>F *\<^sub>V x = G *\<^sub>V x\<close>
  using bounded_clinear.axioms(1) cblinfun_apply assms complex_vector.linear_eq_on_span
  by blast

lemma cblinfun_eq_0_on_UNIV_span:
  fixes basis::\<open>'a::complex_normed_vector set\<close>
  assumes "cspan basis = UNIV"
    and "\<And>s. s\<in>basis \<Longrightarrow> F *\<^sub>V s = 0"
  shows \<open>F = 0\<close>
  by (metis cblinfun_eq_0_on_span UNIV_I assms cblinfun.zero_left cblinfun_eqI)

lemma cblinfun_eq_on_UNIV_span:
  fixes basis::"'a::complex_normed_vector set" and \<phi>::"'a \<Rightarrow> 'b::complex_normed_vector"
  assumes "cspan basis = UNIV"
    and "\<And>s. s\<in>basis \<Longrightarrow> F *\<^sub>V s = G *\<^sub>V s"
  shows \<open>F = G\<close>
  by (metis (no_types) assms cblinfun_eqI cblinfun_eq_on_span iso_tuple_UNIV_I)

lemma cblinfun_eq_on_canonical_basis:
  fixes f g::"'a::{basis_enum,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector"
  defines "basis == set (canonical_basis::'a list)"
  assumes "\<And>u. u \<in> basis \<Longrightarrow> f *\<^sub>V u = g *\<^sub>V u"
  shows  "f = g"
  using assms cblinfun_eq_on_UNIV_span is_generator_set by blast

lemma cblinfun_eq_0_on_canonical_basis:
  fixes f ::"'a::{basis_enum,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector"
  defines "basis == set (canonical_basis::'a list)"
  assumes "\<And>u. u \<in> basis \<Longrightarrow> f *\<^sub>V u = 0"
  shows  "f = 0"
  by (simp add: assms cblinfun_eq_on_canonical_basis)

lemma cinner_canonical_basis_eq_0:
  defines "basisA == set (canonical_basis::'a::onb_enum list)"
    and   "basisB == set (canonical_basis::'b::onb_enum list)"
  assumes "\<And>u v. u\<in>basisA \<Longrightarrow> v\<in>basisB \<Longrightarrow> is_orthogonal v (F *\<^sub>V u)"
  shows "F = 0"
proof-
  have "F *\<^sub>V u = 0"
    if "u\<in>basisA" for u
  proof-
    have "\<And>v. v\<in>basisB \<Longrightarrow> is_orthogonal v (F *\<^sub>V u)"
      by (simp add: assms(3) that)
    moreover have "(\<And>v. v\<in>basisB \<Longrightarrow> is_orthogonal v x) \<Longrightarrow> x = 0"
      for x
    proof-
      assume r1: "\<And>v. v\<in>basisB \<Longrightarrow> is_orthogonal v x"
      have "is_orthogonal v x" for v
      proof-
        have "cspan basisB = UNIV"
          using basisB_def is_generator_set  by auto
        hence "v \<in> cspan basisB"
          by (smt iso_tuple_UNIV_I)
        hence "\<exists>t s. v = (\<Sum>a\<in>t. s a *\<^sub>C a) \<and> finite t \<and> t \<subseteq> basisB"
          using complex_vector.span_explicit
          by (smt mem_Collect_eq)
        then obtain t s where b1: "v = (\<Sum>a\<in>t. s a *\<^sub>C a)" and b2: "finite t" and b3: "t \<subseteq> basisB"
          by blast
        have "v \<bullet>\<^sub>C x = (\<Sum>a\<in>t. s a *\<^sub>C a) \<bullet>\<^sub>C x"
          by (simp add: b1)
        also have "\<dots> = (\<Sum>a\<in>t. (s a *\<^sub>C a) \<bullet>\<^sub>C x)"
          using cinner_sum_left by blast
        also have "\<dots> = (\<Sum>a\<in>t. cnj (s a) * (a \<bullet>\<^sub>C x))"
          by auto
        also have "\<dots> = 0"
          using b3 r1 subsetD by force
        finally show ?thesis by simp
      qed
      thus ?thesis
        by (simp add: \<open>\<And>v. (v \<bullet>\<^sub>C x) = 0\<close> cinner_extensionality)
    qed
    ultimately show ?thesis by simp
  qed
  thus ?thesis
    using basisA_def cblinfun_eq_0_on_canonical_basis by auto
qed

lemma cinner_canonical_basis_eq:
  defines "basisA == set (canonical_basis::'a::onb_enum list)"
    and   "basisB == set (canonical_basis::'b::onb_enum list)"
  assumes "\<And>u v. u\<in>basisA \<Longrightarrow> v\<in>basisB \<Longrightarrow> v \<bullet>\<^sub>C (F *\<^sub>V u) = v \<bullet>\<^sub>C (G *\<^sub>V u)"
  shows "F = G"
proof-
  define H where "H = F - G"
  have "\<And>u v. u\<in>basisA \<Longrightarrow> v\<in>basisB \<Longrightarrow> is_orthogonal v (H *\<^sub>V u)"
    unfolding H_def
    by (simp add: assms(3) cinner_diff_right minus_cblinfun.rep_eq)
  hence "H = 0"
    by (simp add: basisA_def basisB_def cinner_canonical_basis_eq_0)
  thus ?thesis unfolding H_def by simp
qed

lemma cinner_canonical_basis_eq':
  defines "basisA == set (canonical_basis::'a::onb_enum list)"
    and   "basisB == set (canonical_basis::'b::onb_enum list)"
  assumes "\<And>u v. u\<in>basisA \<Longrightarrow> v\<in>basisB \<Longrightarrow> (F *\<^sub>V u) \<bullet>\<^sub>C v = (G *\<^sub>V u) \<bullet>\<^sub>C v"
  shows "F = G"
  using cinner_canonical_basis_eq assms
  by (metis cinner_commute')

lemma not_not_singleton_cblinfun_zero: 
  \<open>x = 0\<close> if \<open>\<not> class.not_singleton TYPE('a)\<close> for x :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  apply (rule cblinfun_eqI)
  apply (subst not_not_singleton_zero[OF that])
  by simp

lemma cblinfun_norm_approx_witness:
  fixes A :: \<open>'a::{not_singleton,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>\<epsilon> > 0\<close>
  shows \<open>\<exists>\<psi>. norm (A *\<^sub>V \<psi>) \<ge> norm A - \<epsilon> \<and> norm \<psi> = 1\<close>
proof (transfer fixing: \<epsilon>)
  fix A :: \<open>'a \<Rightarrow> 'b\<close> assume [simp]: \<open>bounded_clinear A\<close>
  have \<open>\<exists>y\<in>{norm (A x) |x. norm x = 1}. y > \<Squnion> {norm (A x) |x. norm x = 1} - \<epsilon>\<close>
    apply (rule Sup_real_close)
    using assms by (auto simp: ex_norm1 bounded_clinear.bounded_linear bdd_above_norm_f)
  also have \<open>\<Squnion> {norm (A x) |x. norm x = 1} = onorm A\<close>
    by (simp add: bounded_clinear.bounded_linear onorm_sphere)
  finally
  show \<open>\<exists>\<psi>. onorm A - \<epsilon> \<le> norm (A \<psi>) \<and> norm \<psi> = 1\<close>
    by force
qed

lemma cblinfun_norm_approx_witness_mult:
  fixes A :: \<open>'a::{not_singleton,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>\<epsilon> < 1\<close>
  shows \<open>\<exists>\<psi>. norm (A *\<^sub>V \<psi>) \<ge> norm A * \<epsilon> \<and> norm \<psi> = 1\<close>
proof (cases \<open>norm A = 0\<close>)
  case True
  then show ?thesis
    by auto (simp add: ex_norm1)
next
  case False
  then have \<open>(1 - \<epsilon>) * norm A > 0\<close>
    using assms by fastforce
  then obtain \<psi> where geq: \<open>norm (A *\<^sub>V \<psi>) \<ge> norm A - ((1 - \<epsilon>) * norm A)\<close> and \<open>norm \<psi> = 1\<close>
    using cblinfun_norm_approx_witness by blast
  have \<open>norm A * \<epsilon> = norm A - (1 - \<epsilon>) * norm A\<close>
    by (simp add: mult.commute right_diff_distrib')
  also have \<open>\<dots> \<le> norm (A *\<^sub>V \<psi>)\<close>
    by (rule geq)
  finally show ?thesis
    using \<open>norm \<psi> = 1\<close> by auto
qed


lemma cblinfun_norm_approx_witness':
  fixes A :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>\<epsilon> > 0\<close>
  shows \<open>\<exists>\<psi>. norm (A *\<^sub>V \<psi>) / norm \<psi> \<ge> norm A - \<epsilon>\<close>
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  obtain \<psi> where \<open>norm (A *\<^sub>V \<psi>) \<ge> norm A - \<epsilon>\<close> and \<open>norm \<psi> = 1\<close>
    apply atomize_elim
    using complex_normed_vector_axioms True assms
    by (rule cblinfun_norm_approx_witness[internalize_sort' 'a])
  then have \<open>norm (A *\<^sub>V \<psi>) / norm \<psi> \<ge> norm A - \<epsilon>\<close>
    by simp
  then show ?thesis 
    by auto
next
  case False
  show ?thesis
    apply (subst not_not_singleton_cblinfun_zero[OF False])
     apply simp
    apply (subst not_not_singleton_cblinfun_zero[OF False])
    using \<open>\<epsilon> > 0\<close> by simp
qed

lemma cblinfun_to_CARD_1_0[simp]: \<open>(A :: _ \<Rightarrow>\<^sub>C\<^sub>L _::CARD_1) = 0\<close>
  by (simp add: cblinfun_eqI)

lemma cblinfun_from_CARD_1_0[simp]: \<open>(A :: _::CARD_1 \<Rightarrow>\<^sub>C\<^sub>L _) = 0\<close>
  using cblinfun_eq_on_UNIV_span by force


lemma cblinfun_cspan_UNIV:
  fixes basis :: \<open>('a::{complex_normed_vector,cfinite_dim} \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector) set\<close>
    and basisA :: \<open>'a set\<close> and basisB :: \<open>'b set\<close>
  assumes \<open>cspan basisA = UNIV\<close> and \<open>cspan basisB = UNIV\<close>
  assumes basis: \<open>\<And>a b. a\<in>basisA \<Longrightarrow> b\<in>basisB \<Longrightarrow> \<exists>F\<in>basis. \<forall>a'\<in>basisA. F *\<^sub>V a' = (if a'=a then b else 0)\<close>
  shows \<open>cspan basis = UNIV\<close>
proof -
  obtain basisA' where \<open>basisA' \<subseteq> basisA\<close> and \<open>cindependent basisA'\<close> and \<open>cspan basisA' = UNIV\<close>
    by (metis assms(1) complex_vector.maximal_independent_subset complex_vector.span_eq top_greatest)
  then have [simp]: \<open>finite basisA'\<close>
    by (simp add: cindependent_cfinite_dim_finite)
  have basis': \<open>\<And>a b. a\<in>basisA' \<Longrightarrow> b\<in>basisB \<Longrightarrow> \<exists>F\<in>basis. \<forall>a'\<in>basisA'. F *\<^sub>V a' = (if a'=a then b else 0)\<close>
    using basis \<open>basisA' \<subseteq> basisA\<close> by fastforce

  obtain F where F: \<open>F a b \<in> basis \<and> F a b *\<^sub>V a' = (if a'=a then b else 0)\<close>
    if \<open>a\<in>basisA'\<close> \<open>b\<in>basisB\<close> \<open>a'\<in>basisA'\<close> for a b a'
    apply atomize_elim apply (intro choice allI)
    using basis' by metis
  then have F_apply: \<open>F a b *\<^sub>V a' = (if a'=a then b else 0)\<close>
    if \<open>a\<in>basisA'\<close> \<open>b\<in>basisB\<close> \<open>a'\<in>basisA'\<close> for a b a'
    using that by auto
  have F_basis: \<open>F a b \<in> basis\<close>
    if \<open>a\<in>basisA'\<close> \<open>b\<in>basisB\<close> for a b
    using that F by auto
  have b_span: \<open>\<exists>G\<in>cspan {F a b|b. b\<in>basisB}. \<forall>a'\<in>basisA'. G *\<^sub>V a' = (if a'=a then b else 0)\<close> if \<open>a\<in>basisA'\<close> for a b
  proof -
    from \<open>cspan basisB = UNIV\<close>
    obtain r t where \<open>finite t\<close> and \<open>t \<subseteq> basisB\<close> and b_lincom: \<open>b = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
      unfolding complex_vector.span_alt by atomize_elim blast
    define G where \<open>G = (\<Sum>i\<in>t. r i *\<^sub>C F a i)\<close>
    have \<open>G \<in> cspan {F a b|b. b\<in>basisB}\<close>
      using \<open>finite t\<close> \<open>t \<subseteq> basisB\<close> unfolding G_def
      by (smt (verit) complex_vector.span_scale complex_vector.span_sum complex_vector.span_superset mem_Collect_eq subsetD)
    moreover have \<open>G *\<^sub>V a' = (if a'=a then b else 0)\<close> if \<open>a'\<in>basisA'\<close> for a'
      using \<open>t \<subseteq> basisB\<close> \<open>a\<in>basisA'\<close> \<open>a'\<in>basisA'\<close>
      by (auto simp: b_lincom G_def cblinfun.sum_left F_apply intro!: sum.neutral sum.cong)
    ultimately show ?thesis
      by blast
  qed

  have a_span: \<open>cspan (\<Union>a\<in>basisA'. cspan {F a b|b. b\<in>basisB}) = UNIV\<close>
  proof (intro equalityI subset_UNIV subsetI, rename_tac H)
    fix H
    obtain G where G: \<open>G a b \<in> cspan {F a b|b. b\<in>basisB} \<and> G a b *\<^sub>V a' = (if a'=a then b else 0)\<close> 
      if \<open>a\<in>basisA'\<close> and \<open>a'\<in>basisA'\<close> for a b a'
      apply atomize_elim apply (intro choice allI)
      using b_span by blast
    then have G_cspan: \<open>G a b \<in> cspan {F a b|b. b\<in>basisB}\<close> if \<open>a\<in>basisA'\<close> for a b
      using that by auto
    from G have G: \<open>G a b *\<^sub>V a' = (if a'=a then b else 0)\<close> if \<open>a\<in>basisA'\<close> and \<open>a'\<in>basisA'\<close> for a b a'
      using that by auto
    define H' where \<open>H' = (\<Sum>a\<in>basisA'. G a (H *\<^sub>V a))\<close>
    have \<open>H' \<in> cspan (\<Union>a\<in>basisA'. cspan {F a b|b. b\<in>basisB})\<close>
      unfolding H'_def using G_cspan
      by (smt (verit, del_insts) UN_iff complex_vector.span_clauses(1) complex_vector.span_sum)
    moreover have \<open>H' = H\<close>
      using \<open>cspan basisA' = UNIV\<close> 
      by (auto simp: H'_def cblinfun_eq_on_UNIV_span cblinfun.sum_left G)
    ultimately show \<open>H \<in> cspan (\<Union>a\<in>basisA'. cspan {F a b |b. b \<in> basisB})\<close>
      by simp
  qed

  moreover have \<open>cspan basis \<supseteq> cspan (\<Union>a\<in>basisA'. cspan {F a b|b. b\<in>basisB})\<close>
    by (smt (verit) F_basis UN_subset_iff complex_vector.span_base complex_vector.span_minimal complex_vector.subspace_span mem_Collect_eq subsetI)

  ultimately show \<open>cspan basis = UNIV\<close>
    by auto
qed


instance cblinfun :: (\<open>{cfinite_dim,complex_normed_vector}\<close>, \<open>{cfinite_dim,complex_normed_vector}\<close>) cfinite_dim
proof intro_classes
  obtain basisA :: \<open>'a set\<close> where [simp]: \<open>cspan basisA = UNIV\<close> \<open>cindependent basisA\<close> \<open>finite basisA\<close>
    using finite_basis by blast
  obtain basisB :: \<open>'b set\<close> where [simp]: \<open>cspan basisB = UNIV\<close> \<open>cindependent basisB\<close> \<open>finite basisB\<close>
    using finite_basis by blast
  define f where \<open>f a b = cconstruct basisA (\<lambda>x. if x=a then b else 0)\<close> for a :: 'a and b :: 'b
  have f_a: \<open>f a b a = b\<close> if \<open>a : basisA\<close> for a b
    by (simp add: complex_vector.construct_basis f_def that)
  have f_not_a: \<open>f a b c = 0\<close> if \<open>a : basisA\<close> and \<open>c : basisA\<close> and \<open>a \<noteq> c\<close>for a b c
    using that by (simp add: complex_vector.construct_basis f_def)
  define F where \<open>F a b = CBlinfun (f a b)\<close> for a b
  have \<open>clinear (f a b)\<close> for a b
    by (auto intro: complex_vector.linear_construct simp: f_def)
  then have \<open>bounded_clinear (f a b)\<close> for a b
    by auto
  then have F_apply: \<open>cblinfun_apply (F a b) = f a b\<close> for a b
    by (simp add: F_def bounded_clinear_CBlinfun_apply)
  define basis where \<open>basis = {F a b| a b. a\<in>basisA \<and> b\<in>basisB}\<close>
  have "\<And>a b. \<lbrakk>a \<in> basisA; b \<in> basisB\<rbrakk> \<Longrightarrow> \<exists>F\<in>basis. \<forall>a'\<in>basisA. F *\<^sub>V a' = (if a' = a then b else 0)"
    by (smt (verit, del_insts) F_apply basis_def f_a f_not_a mem_Collect_eq)
  then have \<open>cspan basis = UNIV\<close>
    by (metis \<open>cspan basisA = UNIV\<close> \<open>cspan basisB = UNIV\<close> cblinfun_cspan_UNIV)

  moreover have \<open>finite basis\<close>
    unfolding basis_def by (auto intro: finite_image_set2) 
  ultimately show \<open>\<exists>S :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set. finite S \<and> cspan S = UNIV\<close>
    by auto
qed

lemma norm_cblinfun_bound_dense:
  assumes \<open>0 \<le> b\<close>
  assumes S: \<open>closure S = UNIV\<close>
  assumes bound: \<open>\<And>x. x\<in>S \<Longrightarrow> norm (cblinfun_apply f x) \<le> b * norm x\<close>
  shows \<open>norm f \<le> b\<close>
proof -
  have 1: \<open>continuous_on UNIV (\<lambda>a. norm (f *\<^sub>V a))\<close>
    by (simp add: continuous_on_eq_continuous_within)
  have 2: \<open>continuous_on UNIV (\<lambda>a. b * norm a)\<close>
    using continuous_on_mult_left continuous_on_norm_id by blast
  have \<open>norm (cblinfun_apply f x) \<le> b * norm x\<close> for x
    by (metis (mono_tags, lifting) UNIV_I S bound 1 2 on_closure_leI)
  then show \<open>norm f \<le> b\<close>
    using \<open>0 \<le> b\<close> norm_cblinfun_bound by blast
qed

lemma infsum_cblinfun_apply:
  assumes \<open>g summable_on S\<close>
  shows \<open>infsum (\<lambda>x. A *\<^sub>V g x) S = A *\<^sub>V (infsum g S)\<close>
  using infsum_bounded_linear[unfolded o_def] assms cblinfun.real.bounded_linear_right by blast

lemma has_sum_cblinfun_apply:
  assumes \<open>(g has_sum x) S\<close>
  shows \<open>((\<lambda>x. A *\<^sub>V g x) has_sum (A *\<^sub>V x)) S\<close>
  using assms has_sum_bounded_linear[unfolded o_def] using cblinfun.real.bounded_linear_right by blast

lemma abs_summable_on_cblinfun_apply:
  assumes \<open>g abs_summable_on S\<close>
  shows \<open>(\<lambda>x. A *\<^sub>V g x) abs_summable_on S\<close>
  using bounded_clinear.bounded_linear[OF cblinfun.bounded_clinear_right] assms
  by (rule abs_summable_on_bounded_linear[unfolded o_def])

lemma summable_on_cblinfun_apply:
  assumes \<open>g summable_on S\<close>
  shows \<open>(\<lambda>x. A *\<^sub>V g x) summable_on S\<close>
  using bounded_clinear.bounded_linear[OF cblinfun.bounded_clinear_right] assms
  by (rule summable_on_bounded_linear[unfolded o_def])

lemma summable_on_cblinfun_apply_left:
  assumes \<open>A summable_on S\<close>
  shows \<open>(\<lambda>x. A x *\<^sub>V g) summable_on S\<close>
  using bounded_clinear.bounded_linear[OF cblinfun.bounded_clinear_left] assms
  by (rule summable_on_bounded_linear[unfolded o_def])

lemma abs_summable_on_cblinfun_apply_left:
  assumes \<open>A abs_summable_on S\<close>
  shows \<open>(\<lambda>x. A x *\<^sub>V g) abs_summable_on S\<close>
  using bounded_clinear.bounded_linear[OF cblinfun.bounded_clinear_left] assms
  by (rule abs_summable_on_bounded_linear[unfolded o_def])
lemma infsum_cblinfun_apply_left:
  assumes \<open>A summable_on S\<close>
  shows \<open>infsum (\<lambda>x. A x *\<^sub>V g) S = (infsum A S) *\<^sub>V g\<close>
  apply (rule infsum_bounded_linear[unfolded o_def, of \<open>\<lambda>A. cblinfun_apply A g\<close>])
  using assms 
  by (auto simp add: bounded_clinear.bounded_linear bounded_cbilinear_cblinfun_apply)
lemma has_sum_cblinfun_apply_left:
  assumes \<open>(A has_sum x) S\<close>
  shows \<open>((\<lambda>x. A x *\<^sub>V g) has_sum (x *\<^sub>V g)) S\<close>
  apply (rule has_sum_bounded_linear[unfolded o_def, of \<open>\<lambda>A. cblinfun_apply A g\<close>])
  using assms by (auto simp add: bounded_clinear.bounded_linear cblinfun.bounded_clinear_left)

text \<open>The next eight lemmas logically belong in \<^theory>\<open>Complex_Bounded_Operators.Complex_Inner_Product\<close>
  but the proofs use facts from this theory.\<close>
lemma has_sum_cinner_left:
  assumes \<open>(f has_sum x) I\<close>
  shows \<open>((\<lambda>i. cinner a (f i)) has_sum cinner a x) I\<close>
  by (metis assms cblinfun_cinner_right.rep_eq has_sum_cblinfun_apply)

lemma summable_on_cinner_left:
  assumes \<open>f summable_on I\<close>
  shows \<open>(\<lambda>i. cinner a (f i)) summable_on I\<close>
  by (metis assms has_sum_cinner_left summable_on_def)

lemma infsum_cinner_left:
  assumes \<open>\<phi> summable_on I\<close>
  shows \<open>cinner \<psi> (\<Sum>\<^sub>\<infinity>i\<in>I. \<phi> i) = (\<Sum>\<^sub>\<infinity>i\<in>I. cinner \<psi> (\<phi> i))\<close>
  by (metis assms has_sum_cinner_left has_sum_infsum infsumI)

lemma has_sum_cinner_right:
  assumes \<open>(f has_sum x) I\<close>
  shows \<open>((\<lambda>i. f i \<bullet>\<^sub>C a) has_sum (x \<bullet>\<^sub>C a)) I\<close>
  using assms has_sum_bounded_linear[unfolded o_def] bounded_antilinear.bounded_linear 
    bounded_antilinear_cinner_left by blast


lemma summable_on_cinner_right:
  assumes \<open>f summable_on I\<close>
  shows \<open>(\<lambda>i. f i \<bullet>\<^sub>C a) summable_on I\<close>
  by (metis assms has_sum_cinner_right summable_on_def)

lemma infsum_cinner_right:
  assumes \<open>\<phi> summable_on I\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>i\<in>I. \<phi> i) \<bullet>\<^sub>C \<psi> = (\<Sum>\<^sub>\<infinity>i\<in>I. \<phi> i \<bullet>\<^sub>C \<psi>)\<close>
  by (metis assms has_sum_cinner_right has_sum_infsum infsumI)

lemma Cauchy_cinner_product_summable:
  assumes asum: \<open>a summable_on UNIV\<close>
  assumes bsum: \<open>b summable_on UNIV\<close>
  assumes \<open>finite X\<close> \<open>finite Y\<close>
  assumes pos: \<open>\<And>x y. x \<notin> X \<Longrightarrow> y \<notin> Y \<Longrightarrow> cinner (a x) (b y) \<ge> 0\<close>
  shows absum: \<open>(\<lambda>(x, y). cinner (a x) (b y)) summable_on UNIV\<close>
proof -
  have \<open>(\<Sum>(x,y)\<in>F. norm (cinner (a x) (b y))) \<le> norm (cinner (infsum a (-X)) (infsum b (-Y))) + norm (infsum a (-X)) + norm (infsum b (-Y)) + 1\<close> 
    if \<open>finite F\<close> and \<open>F \<subseteq> (-X)\<times>(-Y)\<close> for F
  proof -
    from asum \<open>finite X\<close>
    have \<open>a summable_on (-X)\<close>
      by (simp add: Compl_eq_Diff_UNIV summable_on_cofin_subset)
    then obtain MA where \<open>finite MA\<close> and \<open>MA \<subseteq> -X\<close>
      and MA: \<open>G \<supseteq> MA \<Longrightarrow> G \<subseteq> -X \<Longrightarrow> finite G \<Longrightarrow> norm (sum a G - infsum a (-X)) \<le> 1\<close> for G
      apply (simp add: summable_iff_has_sum_infsum has_sum_metric dist_norm)
      by (meson less_eq_real_def zero_less_one)
    
    from bsum \<open>finite Y\<close>
    have \<open>b summable_on (-Y)\<close>
      by (simp add: Compl_eq_Diff_UNIV summable_on_cofin_subset)
    then obtain MB where \<open>finite MB\<close> and \<open>MB \<subseteq> -Y\<close>
      and MB: \<open>G \<supseteq> MB \<Longrightarrow> G \<subseteq> -Y \<Longrightarrow> finite G \<Longrightarrow> norm (sum b G - infsum b (-Y)) \<le> 1\<close> for G
      apply (simp add: summable_iff_has_sum_infsum has_sum_metric dist_norm)
      by (meson less_eq_real_def zero_less_one)

    define F1 F2 where \<open>F1 = fst ` F \<union> MA\<close> and \<open>F2 = snd ` F \<union> MB\<close>
    define t1 t2 where \<open>t1 = sum a F1 - infsum a (-X)\<close> and \<open>t2 = sum b F2 - infsum b (-Y)\<close>
  
    have [simp]: \<open>finite F1\<close> \<open>finite F2\<close>
      using F1_def F2_def \<open>finite MA\<close> \<open>finite MB\<close> that by auto
    have [simp]: \<open>F1 \<subseteq> -X\<close> \<open>F2 \<subseteq> -Y\<close>
      using \<open>F \<subseteq> (-X)\<times>(-Y)\<close> \<open>MA \<subseteq> -X\<close> \<open>MB \<subseteq> -Y\<close>
      by (auto simp: F1_def F2_def)
    from MA[OF _ \<open>F1 \<subseteq> -X\<close> \<open>finite F1\<close>] have \<open>norm t1 \<le> 1\<close> 
      by (auto simp: t1_def F1_def)
    from MB[OF _ \<open>F2 \<subseteq> -Y\<close> \<open>finite F2\<close>] have \<open>norm t2 \<le> 1\<close> 
      by (auto simp: t2_def F2_def)
    have [simp]: \<open>F \<subseteq> F1 \<times> F2\<close>
      by (force simp: F1_def F2_def image_def)
    have \<open>(\<Sum>(x,y)\<in>F. norm (cinner (a x) (b y))) \<le> (\<Sum>(x,y)\<in>F1\<times>F2. norm (cinner (a x) (b y)))\<close>
      by (intro sum_mono2) auto
    also have "... = (\<Sum>x\<in>F1 \<times> F2. norm (a (fst x) \<bullet>\<^sub>C b (snd x)))"
      by (auto  simp: case_prod_beta)
    also have "... =  norm (\<Sum>x\<in>F1 \<times> F2. a (fst x) \<bullet>\<^sub>C b (snd x))"
    proof -
      have "(\<Sum>x\<in>F1 \<times> F2. \<bar>a (fst x) \<bullet>\<^sub>C b (snd x)\<bar>) = \<bar>\<Sum>x\<in>F1 \<times> F2. a (fst x) \<bullet>\<^sub>C b (snd x)\<bar>"
        by (smt (verit, best) pos sum.cong sum_nonneg ComplD SigmaE \<open>F1 \<subseteq> - X\<close> \<open>F2 \<subseteq> - Y\<close> abs_pos prod.sel subset_iff)
      then show ?thesis
        by (smt (verit) abs_complex_def norm_ge_zero norm_of_real o_def of_real_sum sum.cong sum_norm_le)
    qed
    also from pos have \<open>\<dots> = norm (\<Sum>(x,y)\<in>F1\<times>F2. cinner (a x) (b y))\<close>
      by (auto simp: case_prod_beta)
    also have \<open>\<dots> = norm (cinner (sum a F1) (sum b F2))\<close>
      by (simp add: sum.cartesian_product sum_cinner)
    also have \<open>\<dots> = norm (cinner (infsum a (-X) + t1) (infsum b (-Y) + t2))\<close>
      by (simp add: t1_def t2_def)
    also have \<open>\<dots> \<le> norm (cinner (infsum a (-X)) (infsum b (-Y))) + norm (infsum a (-X)) * norm t2 + norm t1 * norm (infsum b (-Y)) + norm t1 * norm t2\<close>
      apply (simp add: cinner_add_right cinner_add_left)
      by (smt (verit, del_insts) complex_inner_class.Cauchy_Schwarz_ineq2 norm_triangle_ineq)
    also from \<open>norm t1 \<le> 1\<close> \<open>norm t2 \<le> 1\<close>
    have \<open>\<dots> \<le> norm (cinner (infsum a (-X)) (infsum b (-Y))) + norm (infsum a (-X)) + norm (infsum b (-Y)) + 1\<close>
      by (auto intro!: add_mono mult_left_le mult_left_le_one_le mult_le_one)
    finally show ?thesis
      by -
  qed

  then have \<open>(\<lambda>(x, y). cinner (a x) (b y)) abs_summable_on (-X)\<times>(-Y)\<close>
    apply (rule_tac nonneg_bdd_above_summable_on)
    by (auto intro!: bdd_aboveI2 simp: case_prod_unfold)
  then have 1: \<open>(\<lambda>(x, y). cinner (a x) (b y)) summable_on (-X)\<times>(-Y)\<close>
    using abs_summable_summable by blast

  from bsum
  have \<open>(\<lambda>y. b y) summable_on (-Y)\<close>
    by (simp add: Compl_eq_Diff_UNIV assms(4) summable_on_cofin_subset)
  then have \<open>(\<lambda>y. cinner (a x) (b y)) summable_on (-Y)\<close> for x
    using summable_on_cinner_left by blast
  with \<open>finite X\<close> have 2: \<open>(\<lambda>(x, y). cinner (a x) (b y)) summable_on X\<times>(-Y)\<close>
    by (force intro: summable_on_product_finite_left)

  from asum
  have \<open>(\<lambda>x. a x) summable_on (-X)\<close>
    by (simp add: Compl_eq_Diff_UNIV assms(3) summable_on_cofin_subset)
  then have \<open>(\<lambda>x. cinner (a x) (b y)) summable_on (-X)\<close> for y
    using summable_on_cinner_right by blast
  with \<open>finite Y\<close> have 3: \<open>(\<lambda>(x, y). cinner (a x) (b y)) summable_on (-X)\<times>Y\<close>
    by (force intro: summable_on_product_finite_right)

  have 4: \<open>(\<lambda>(x, y). cinner (a x) (b y)) summable_on X\<times>Y\<close>
    by (simp add: \<open>finite X\<close> \<open>finite Y\<close>)

  have \<section>: "UNIV = ((-X) \<times> -Y) \<union> (X \<times> -Y) \<union> ((-X) \<times> Y) \<union> (X \<times> Y)"
    by auto
  show ?thesis
    using 1 2 3 4 by (force simp: \<section> intro!: summable_on_Un_disjoint) 
qed


text \<open>A variant of @{thm [source] Series.Cauchy_product_sums} with \<^term>\<open>(*)\<close> replaced by \<^term>\<open>cinner\<close>.
   Differently from @{thm [source] Series.Cauchy_product_sums}, we do not require absolute summability
   of \<^term>\<open>a\<close> and \<^term>\<open>b\<close> individually but only unconditional summability of \<^term>\<open>a\<close>, \<^term>\<open>b\<close>, and their product.
   While on, e.g., reals, unconditional summability is equivalent to absolute summability, in
   general unconditional summability is a weaker requirement.

  Logically belong in \<^theory>\<open>Complex_Bounded_Operators.Complex_Inner_Product\<close>
  but the proof uses facts from this theory.\<close>
lemma 
  fixes a b :: "nat \<Rightarrow> 'a::complex_inner"
  assumes asum: \<open>a summable_on UNIV\<close>
  assumes bsum: \<open>b summable_on UNIV\<close>
  assumes absum: \<open>(\<lambda>(x, y). cinner (a x) (b y)) summable_on UNIV\<close>
    (* \<comment> \<open>See @{thm [source] Cauchy_cinner_product_summable} or @{thm [source] Cauchy_cinner_product_summable'} for a way to rewrite this premise.\<close> *)
  shows Cauchy_cinner_product_infsum: \<open>(\<Sum>\<^sub>\<infinity>k. \<Sum>i\<le>k. cinner (a i) (b (k - i))) = cinner (\<Sum>\<^sub>\<infinity>k. a k) (\<Sum>\<^sub>\<infinity>k. b k)\<close>
    and Cauchy_cinner_product_infsum_exists: \<open>(\<lambda>k. \<Sum>i\<le>k. cinner (a i) (b (k - i))) summable_on UNIV\<close>
proof -
  have img: \<open>(\<lambda>(k::nat, i). (i, k - i)) ` {(k, i). i \<le> k} = UNIV\<close>
    apply (auto simp: image_def)
    by (metis add.commute add_diff_cancel_right' diff_le_self)
  have inj: \<open>inj_on (\<lambda>(k::nat, i). (i, k - i)) {(k, i). i \<le> k}\<close>
    by (smt (verit, del_insts) Pair_inject case_prodE case_prod_conv eq_diff_iff inj_onI mem_Collect_eq)
  have sigma: \<open>(SIGMA k:UNIV. {i. i \<le> k}) = {(k, i). i \<le> k}\<close>
    by auto

  from absum
  have \<section>: \<open>(\<lambda>(x, y). cinner (a y) (b (x - y))) summable_on {(k, i). i \<le> k}\<close>
    by (rule Cauchy_cinner_product_summable'[THEN iffD1])
  then have \<open>(\<lambda>k. \<Sum>\<^sub>\<infinity>i|i\<le>k. cinner (a i) (b (k-i))) summable_on UNIV\<close>
    by (metis (mono_tags, lifting) sigma summable_on_Sigma_banach summable_on_cong)
  then show \<open>(\<lambda>k. \<Sum>i\<le>k. cinner (a i) (b (k - i))) summable_on UNIV\<close>
    by (metis (mono_tags, lifting) atMost_def finite_Collect_le_nat infsum_finite summable_on_cong)

  have \<open>cinner (\<Sum>\<^sub>\<infinity>k. a k) (\<Sum>\<^sub>\<infinity>k. b k) = (\<Sum>\<^sub>\<infinity>k. \<Sum>\<^sub>\<infinity>l. cinner (a k) (b l))\<close>
    by (smt (verit, best) asum bsum infsum_cinner_left infsum_cinner_right infsum_cong)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(k,l). cinner (a k) (b l))\<close>
    by (smt (verit) UNIV_Times_UNIV infsum_Sigma'_banach infsum_cong local.absum)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(k, l)\<in>(\<lambda>(k, i). (i, k - i)) ` {(k, i). i \<le> k}. cinner (a k) (b l))\<close>
    by (simp only: img)
  also have \<open>\<dots> = infsum ((\<lambda>(k, l). a k \<bullet>\<^sub>C b l) \<circ> (\<lambda>(k, i). (i, k - i))) {(k, i). i \<le> k}\<close>
    using inj by (rule infsum_reindex)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(k,i)|i\<le>k. a i \<bullet>\<^sub>C b (k-i))\<close>
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>k. \<Sum>\<^sub>\<infinity>i|i\<le>k. a i \<bullet>\<^sub>C b (k-i))\<close>
    by (metis (no_types) \<section> infsum_Sigma'_banach sigma)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>k. \<Sum>i\<le>k. a i \<bullet>\<^sub>C b (k-i))\<close>
    by (simp add: atMost_def)
  finally show \<open>(\<Sum>\<^sub>\<infinity>k. \<Sum>i\<le>k. a i \<bullet>\<^sub>C b (k - i)) = (\<Sum>\<^sub>\<infinity>k. a k) \<bullet>\<^sub>C (\<Sum>\<^sub>\<infinity>k. b k)\<close>
    by simp
qed


lemma CBlinfun_plus: 
  assumes [simp]: \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  shows \<open>CBlinfun (f + g) = CBlinfun f + CBlinfun g\<close>
  by (auto intro!: cblinfun_eqI simp: plus_fun_def bounded_clinear_add CBlinfun_inverse cblinfun.add_left)

lemma CBlinfun_scaleC:
  assumes \<open>bounded_clinear f\<close>
  shows \<open>CBlinfun (\<lambda>y. c *\<^sub>C f y) = c *\<^sub>C CBlinfun f\<close>
  by (simp add: assms eq_onp_same_args scaleC_cblinfun.abs_eq)


lemma cinner_sup_norm_cblinfun:
  fixes A :: \<open>'a::{complex_normed_vector,not_singleton} \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner\<close>
  shows \<open>norm A = (SUP (\<psi>,\<phi>). cmod (cinner \<psi> (A *\<^sub>V \<phi>)) / (norm \<psi> * norm \<phi>))\<close>
  apply transfer
  apply (rule cinner_sup_onorm)
  by (simp add: bounded_clinear.bounded_linear)


lemma norm_cblinfun_Sup: \<open>norm A = (SUP \<psi>. norm (A *\<^sub>V \<psi>) / norm \<psi>)\<close>
  by (simp add: norm_cblinfun.rep_eq onorm_def)

lemma cblinfun_eq_on:
  fixes A B :: "'a::cbanach \<Rightarrow>\<^sub>C\<^sub>L'b::complex_normed_vector"
  assumes "\<And>x. x \<in> G \<Longrightarrow> A *\<^sub>V x = B *\<^sub>V x" and \<open>t \<in> closure (cspan G)\<close>
  shows "A *\<^sub>V t = B *\<^sub>V t"
  using assms
  apply transfer
  using bounded_clinear_eq_on_closure by blast

lemma cblinfun_eq_gen_eqI:
  fixes A B :: "'a::cbanach \<Rightarrow>\<^sub>C\<^sub>L'b::complex_normed_vector"
  assumes "\<And>x. x \<in> G \<Longrightarrow> A *\<^sub>V x = B *\<^sub>V x" and \<open>ccspan G = \<top>\<close>
  shows "A = B"
  by (metis assms cblinfun_eqI cblinfun_eq_on ccspan.rep_eq iso_tuple_UNIV_I top_ccsubspace.rep_eq)

declare cnj_bounded_antilinear[bounded_antilinear]

lemma Cblinfun_comp_bounded_cbilinear: \<open>bounded_clinear (CBlinfun o p)\<close> if \<open>bounded_cbilinear p\<close>
  by (metis bounded_cbilinear.bounded_clinear_prod_right bounded_cbilinear.prod_right_def comp_id map_fun_def that)

lemma Cblinfun_comp_bounded_sesquilinear: \<open>bounded_antilinear (CBlinfun o p)\<close> if \<open>bounded_sesquilinear p\<close>
  by (metis (mono_tags, opaque_lifting) bounded_clinear_CBlinfun_apply bounded_sesquilinear.bounded_clinear_right comp_apply that transfer_bounded_sesquilinear_bounded_antilinearI)

subsection \<open>Relationship to real bounded operators (\<^typ>\<open>_ \<Rightarrow>\<^sub>L _\<close>)\<close>

instantiation blinfun :: (real_normed_vector, complex_normed_vector) "complex_normed_vector"
begin
lift_definition scaleC_blinfun :: \<open>complex \<Rightarrow>
 ('a::real_normed_vector, 'b::complex_normed_vector) blinfun \<Rightarrow>
 ('a, 'b) blinfun\<close>
  is \<open>\<lambda> c::complex. \<lambda> f::'a\<Rightarrow>'b. (\<lambda> x. c *\<^sub>C (f x) )\<close>
proof
  fix c::complex and f :: \<open>'a\<Rightarrow>'b\<close> and b1::'a and b2::'a
  assume \<open>bounded_linear f\<close>
  show \<open>c *\<^sub>C f (b1 + b2) = c *\<^sub>C f b1 + c *\<^sub>C f b2\<close>
    by (simp add: \<open>bounded_linear f\<close> linear_simps scaleC_add_right)

  fix c::complex and f :: \<open>'a\<Rightarrow>'b\<close> and b::'a and r::real
  assume \<open>bounded_linear f\<close>
  show \<open>c *\<^sub>C f (r *\<^sub>R b) = r *\<^sub>R (c *\<^sub>C f b)\<close>
    by (simp add: \<open>bounded_linear f\<close> linear_simps(5) scaleR_scaleC)

  fix c::complex and f :: \<open>'a\<Rightarrow>'b\<close>
  assume \<open>bounded_linear f\<close>

  have \<open>\<exists> K. \<forall> x. norm (f x) \<le> norm x * K\<close>
    using \<open>bounded_linear f\<close>
    by (simp add: bounded_linear.bounded)
  then obtain K where \<open>\<forall> x. norm (f x) \<le> norm x * K\<close>
    by blast
  have \<open>cmod c \<ge> 0\<close>
    by simp
  hence \<open>\<forall> x. (cmod c) * norm (f x) \<le> (cmod c) * norm x * K\<close>
    using  \<open>\<forall> x. norm (f x) \<le> norm x * K\<close>
    by (metis ordered_comm_semiring_class.comm_mult_left_mono vector_space_over_itself.scale_scale)
  moreover have \<open>norm (c *\<^sub>C f x) = (cmod c) * norm (f x)\<close>
    for x
    by simp
  ultimately show \<open>\<exists>K. \<forall>x. norm (c *\<^sub>C f x) \<le> norm x * K\<close>
    by (metis ab_semigroup_mult_class.mult_ac(1) mult.commute)
qed

instance
proof
  have "r *\<^sub>R x = complex_of_real r *\<^sub>C x"
    for x :: "('a, 'b) blinfun" and r
    by transfer (simp add: scaleR_scaleC)
  thus "((*\<^sub>R) r::'a \<Rightarrow>\<^sub>L 'b \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)" for r
    by auto
  show "a *\<^sub>C (x + y) = a *\<^sub>C x + a *\<^sub>C y"
    for a :: complex and x y :: "'a \<Rightarrow>\<^sub>L 'b"
    by transfer (simp add: scaleC_add_right)

  show "(a + b) *\<^sub>C x = a *\<^sub>C x + b *\<^sub>C x"
    for a b :: complex and x :: "'a \<Rightarrow>\<^sub>L 'b"
    by transfer (simp add: scaleC_add_left)

  show "a *\<^sub>C b *\<^sub>C x = (a * b) *\<^sub>C x"
    for a b :: complex and x :: "'a \<Rightarrow>\<^sub>L 'b"
    by transfer simp

  have \<open>1 *\<^sub>C f x = f x\<close>
    for f :: \<open>'a\<Rightarrow>'b\<close> and x
    by auto
  thus "1 *\<^sub>C x = x"
    for x :: "'a \<Rightarrow>\<^sub>L 'b"
    by (simp add: scaleC_blinfun.rep_eq blinfun_eqI)

  have \<open>onorm (\<lambda>x. a *\<^sub>C f x) = cmod a * onorm f\<close>
    if \<open>bounded_linear f\<close>
    for f :: \<open>'a \<Rightarrow> 'b\<close> and a :: complex
  proof-
    have \<open>cmod a \<ge> 0\<close>
      by simp
    have \<open>\<exists> K::real. \<forall> x. (\<bar> ereal ((norm (f x)) / (norm x)) \<bar>) \<le> K\<close>
      using \<open>bounded_linear f\<close> le_onorm by fastforce
    then obtain K::real where \<open>\<forall> x. (\<bar> ereal ((norm (f x)) / (norm x)) \<bar>) \<le> K\<close>
      by blast
    hence  \<open>\<forall> x. (cmod a) *(\<bar> ereal ((norm (f x)) / (norm x)) \<bar>) \<le> (cmod a) * K\<close>
      using \<open>cmod a \<ge> 0\<close>
      by (metis abs_ereal.simps(1) abs_ereal_pos   abs_pos ereal_mult_left_mono  times_ereal.simps(1))
    hence  \<open>\<forall> x.  (\<bar> ereal ((cmod a) * (norm (f x)) / (norm x)) \<bar>) \<le> (cmod a) * K\<close>
      by simp
    hence \<open>bdd_above {ereal (cmod a * (norm (f x)) / (norm x)) | x. True}\<close>
      by simp
    moreover have \<open>{ereal (cmod a * (norm (f x)) / (norm x)) | x. True} \<noteq> {}\<close>
      by auto
    ultimately have p1: \<open>(SUP x. \<bar>ereal (cmod a * (norm (f x)) / (norm x))\<bar>) \<le> cmod a * K\<close>
      using \<open>\<forall> x. \<bar> ereal (cmod a * (norm (f x)) / (norm x)) \<bar> \<le> cmod a * K\<close>
        Sup_least mem_Collect_eq
      by (simp add: SUP_le_iff)
    have  p2: \<open>\<And>i. i \<in> UNIV \<Longrightarrow> 0 \<le> ereal (cmod a * norm (f i) / norm i)\<close>
      by simp
    hence \<open>\<bar>SUP x. ereal (cmod a * (norm (f x)) / (norm x))\<bar>
              \<le> (SUP x. \<bar>ereal (cmod a * (norm (f x)) / (norm x))\<bar>)\<close>
      using  \<open>bdd_above {ereal (cmod a * (norm (f x)) / (norm x)) | x. True}\<close>
        \<open>{ereal (cmod a * (norm (f x)) / (norm x)) | x. True} \<noteq> {}\<close>
      by (metis (mono_tags, lifting) SUP_upper2 Sup.SUP_cong UNIV_I
          p2 abs_ereal_ge0 ereal_le_real)
    hence \<open>\<bar>SUP x. ereal (cmod a * (norm (f x)) / (norm x))\<bar> \<le> cmod a * K\<close>
      using  \<open>(SUP x. \<bar>ereal (cmod a * (norm (f x)) / (norm x))\<bar>) \<le> cmod a * K\<close>
      by simp
    hence \<open>\<bar> ( SUP i\<in>UNIV::'a set. ereal ((\<lambda> x. (cmod a) * (norm (f x)) / norm x) i)) \<bar> \<noteq> \<infinity>\<close>
      by auto
    hence w2: \<open>( SUP i\<in>UNIV::'a set. ereal ((\<lambda> x. cmod a * (norm (f x)) / norm x) i))
             = ereal ( Sup ((\<lambda> x. cmod a * (norm (f x)) / norm x) ` (UNIV::'a set) ))\<close>
      by (simp add: ereal_SUP)
    have \<open>(UNIV::('a set)) \<noteq> {}\<close>
      by simp
    moreover have \<open>\<And> i. i \<in> (UNIV::('a set)) \<Longrightarrow> (\<lambda> x. (norm (f x)) / norm x :: ereal) i \<ge> 0\<close>
      by simp
    moreover have \<open>cmod a \<ge> 0\<close>
      by simp
    ultimately have \<open>(SUP i\<in>(UNIV::('a set)). ((cmod a)::ereal) * (\<lambda> x. (norm (f x)) / norm x :: ereal) i )
        = ((cmod a)::ereal) * ( SUP i\<in>(UNIV::('a set)). (\<lambda> x. (norm (f x)) / norm x :: ereal) i )\<close>
      by (simp add: Sup_ereal_mult_left')
    hence \<open>(SUP x. ((cmod a)::ereal) * ( (norm (f x)) / norm x :: ereal) )
        = ((cmod a)::ereal) * ( SUP x. ( (norm (f x)) / norm x :: ereal) )\<close>
      by simp
    hence z1: \<open>real_of_ereal ( (SUP x. ((cmod a)::ereal) * ( (norm (f x)) / norm x :: ereal) ) )
        = real_of_ereal ( ((cmod a)::ereal) * ( SUP x. ( (norm (f x)) / norm x :: ereal) ) )\<close>
      by simp
    have z2: \<open>real_of_ereal (SUP x. ((cmod a)::ereal) * ( (norm (f x)) / norm x :: ereal) )
                  = (SUP x. cmod a * (norm (f x) / norm x))\<close>
      using w2
      by auto
    have \<open>real_of_ereal ( ((cmod a)::ereal) * ( SUP x. ( (norm (f x)) / norm x :: ereal) ) )
                =  (cmod a) * real_of_ereal ( SUP x. ( (norm (f x)) / norm x :: ereal) )\<close>
      by simp
    moreover have \<open>real_of_ereal ( SUP x. ( (norm (f x)) / norm x :: ereal) )
                  = ( SUP x. ((norm (f x)) / norm x) )\<close>
    proof-
      have \<open>\<bar> ( SUP i\<in>UNIV::'a set. ereal ((\<lambda> x. (norm (f x)) / norm x) i)) \<bar> \<noteq> \<infinity>\<close>
      proof-
        have \<open>\<exists> K::real. \<forall> x. (\<bar> ereal ((norm (f x)) / (norm x)) \<bar>) \<le> K\<close>
          using \<open>bounded_linear f\<close> le_onorm by fastforce
        then obtain K::real where \<open>\<forall> x. (\<bar> ereal ((norm (f x)) / (norm x)) \<bar>) \<le> K\<close>
          by blast
        hence \<open>bdd_above {ereal ((norm (f x)) / (norm x)) | x. True}\<close>
          by simp
        moreover have \<open>{ereal ((norm (f x)) / (norm x)) | x. True} \<noteq> {}\<close>
          by auto
        ultimately have \<open>(SUP x. \<bar>ereal ((norm (f x)) / (norm x))\<bar>) \<le> K\<close>
          using \<open>\<forall> x. \<bar> ereal ((norm (f x)) / (norm x)) \<bar> \<le> K\<close>
            Sup_least mem_Collect_eq
          by (simp add: SUP_le_iff)
        hence \<open>\<bar>SUP x. ereal ((norm (f x)) / (norm x))\<bar>
              \<le> (SUP x. \<bar>ereal ((norm (f x)) / (norm x))\<bar>)\<close>
          using  \<open>bdd_above {ereal ((norm (f x)) / (norm x)) | x. True}\<close>
            \<open>{ereal ((norm (f x)) / (norm x)) | x. True} \<noteq> {}\<close>
          by (metis (mono_tags, lifting) SUP_upper2 Sup.SUP_cong UNIV_I \<open>\<And>i. i \<in> UNIV \<Longrightarrow> 0 \<le> ereal (norm (f i) / norm i)\<close> abs_ereal_ge0 ereal_le_real)
        hence \<open>\<bar>SUP x. ereal ((norm (f x)) / (norm x))\<bar> \<le> K\<close>
          using  \<open>(SUP x. \<bar>ereal ((norm (f x)) / (norm x))\<bar>) \<le> K\<close>
          by simp
        thus ?thesis
          by auto
      qed
      hence \<open> ( SUP i\<in>UNIV::'a set. ereal ((\<lambda> x. (norm (f x)) / norm x) i))
             = ereal ( Sup ((\<lambda> x. (norm (f x)) / norm x) ` (UNIV::'a set) ))\<close>
        by (simp add: ereal_SUP)
      thus ?thesis
        by simp
    qed
    have z3: \<open>real_of_ereal ( ((cmod a)::ereal) * ( SUP x. ( (norm (f x)) / norm x :: ereal) ) )
                = cmod a * (SUP x. norm (f x) / norm x)\<close>
      by (simp add: \<open>real_of_ereal (SUP x. ereal (norm (f x) / norm x)) = (SUP x. norm (f x) / norm x)\<close>)
    hence w1: \<open>(SUP x. cmod a * (norm (f x) / norm x)) =
          cmod a * (SUP x. norm (f x) / norm x)\<close>
      using z1 z2 by linarith
    have v1: \<open>onorm (\<lambda>x. a *\<^sub>C f x) = (SUP x. norm (a *\<^sub>C f x) / norm x)\<close>
      by (simp add: onorm_def)
    have v2: \<open>(SUP x. norm (a *\<^sub>C f x) / norm x) = (SUP x. ((cmod a) * norm (f x)) / norm x)\<close>
      by simp
    have v3: \<open>(SUP x. ((cmod a) * norm (f x)) / norm x) =  (SUP x. (cmod a) * ((norm (f x)) / norm x))\<close>
      by simp
    have v4: \<open>(SUP x. (cmod a) * ((norm (f x)) / norm x)) = (cmod a) *  (SUP x. ((norm (f x)) / norm x))\<close>
      using w1
      by blast
    show \<open>onorm (\<lambda>x. a *\<^sub>C f x) = cmod a * onorm f\<close>
      using v1 v2 v3 v4
      by (metis (mono_tags, lifting) onorm_def)
  qed
  thus \<open>norm (a *\<^sub>C x) = cmod a * norm x\<close>
    for a::complex and x::\<open>('a, 'b) blinfun\<close>
    by transfer blast
qed
end

(* We do not have clinear_blinfun_compose_right *)
lemma clinear_blinfun_compose_left: \<open>clinear (\<lambda>x. blinfun_compose x y)\<close>
  by (auto intro!: clinearI simp: blinfun_eqI scaleC_blinfun.rep_eq bounded_bilinear.add_left
                                  bounded_bilinear_blinfun_compose)

instance blinfun :: (real_normed_vector, cbanach) cbanach..

lemma blinfun_compose_assoc: "(A o\<^sub>L B) o\<^sub>L C = A o\<^sub>L (B  o\<^sub>L C)"
  by (simp add: blinfun_eqI)

lift_definition blinfun_of_cblinfun::\<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector
  \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'b\<close> is "id"
  by transfer (simp add: bounded_clinear.bounded_linear)

lift_definition blinfun_cblinfun_eq ::
  \<open>'a \<Rightarrow>\<^sub>L 'b \<Rightarrow> 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector \<Rightarrow> bool\<close> is "(=)" .

lemma blinfun_cblinfun_eq_bi_unique[transfer_rule]: \<open>bi_unique blinfun_cblinfun_eq\<close>
  unfolding bi_unique_def by transfer auto

lemma blinfun_cblinfun_eq_right_total[transfer_rule]: \<open>right_total blinfun_cblinfun_eq\<close>
  unfolding right_total_def by transfer (simp add: bounded_clinear.bounded_linear)

named_theorems cblinfun_blinfun_transfer

lemma cblinfun_blinfun_transfer_0[cblinfun_blinfun_transfer]:
  "blinfun_cblinfun_eq (0::(_,_) blinfun) (0::(_,_) cblinfun)"
  by transfer simp

lemma cblinfun_blinfun_transfer_plus[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(blinfun_cblinfun_eq ===> blinfun_cblinfun_eq ===> blinfun_cblinfun_eq) (+) (+)"
  unfolding rel_fun_def by transfer auto

lemma cblinfun_blinfun_transfer_minus[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(blinfun_cblinfun_eq ===> blinfun_cblinfun_eq ===> blinfun_cblinfun_eq) (-) (-)"
  unfolding rel_fun_def by transfer auto

lemma cblinfun_blinfun_transfer_uminus[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(blinfun_cblinfun_eq ===> blinfun_cblinfun_eq) (uminus) (uminus)"
  unfolding rel_fun_def by transfer auto

definition "real_complex_eq r c \<longleftrightarrow> complex_of_real r = c"

lemma bi_unique_real_complex_eq[transfer_rule]: \<open>bi_unique real_complex_eq\<close>
  unfolding real_complex_eq_def bi_unique_def by auto

lemma left_total_real_complex_eq[transfer_rule]: \<open>left_total real_complex_eq\<close>
  unfolding real_complex_eq_def left_total_def by auto

lemma cblinfun_blinfun_transfer_scaleC[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(real_complex_eq ===> blinfun_cblinfun_eq ===> blinfun_cblinfun_eq) (scaleR) (scaleC)"
  unfolding rel_fun_def by transfer (simp add: real_complex_eq_def scaleR_scaleC)

lemma cblinfun_blinfun_transfer_CBlinfun[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(eq_onp bounded_clinear ===> blinfun_cblinfun_eq) Blinfun CBlinfun"
  unfolding rel_fun_def blinfun_cblinfun_eq.rep_eq eq_onp_def
  by (auto simp: CBlinfun_inverse Blinfun_inverse bounded_clinear.bounded_linear)

lemma cblinfun_blinfun_transfer_norm[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(blinfun_cblinfun_eq ===> (=)) norm norm"
  unfolding rel_fun_def by transfer auto

lemma cblinfun_blinfun_transfer_dist[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(blinfun_cblinfun_eq ===> blinfun_cblinfun_eq ===> (=)) dist dist"
  unfolding rel_fun_def dist_norm by transfer auto

lemma cblinfun_blinfun_transfer_sgn[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(blinfun_cblinfun_eq ===> blinfun_cblinfun_eq) sgn sgn"
  unfolding rel_fun_def sgn_blinfun_def sgn_cblinfun_def by transfer (auto simp: scaleR_scaleC)

lemma cblinfun_blinfun_transfer_Cauchy[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(((=) ===> blinfun_cblinfun_eq) ===> (=)) Cauchy Cauchy"
proof -
  note cblinfun_blinfun_transfer[transfer_rule]
  show ?thesis
    unfolding Cauchy_def
    by transfer_prover
qed

lemma cblinfun_blinfun_transfer_tendsto[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(((=) ===> blinfun_cblinfun_eq) ===> blinfun_cblinfun_eq ===> (=) ===> (=)) tendsto tendsto"
proof -
  note cblinfun_blinfun_transfer[transfer_rule]
  show ?thesis
    unfolding tendsto_iff
    by transfer_prover
qed

lemma cblinfun_blinfun_transfer_compose[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(blinfun_cblinfun_eq ===> blinfun_cblinfun_eq ===> blinfun_cblinfun_eq) (o\<^sub>L) (o\<^sub>C\<^sub>L)"
  unfolding rel_fun_def by transfer auto

lemma cblinfun_blinfun_transfer_apply[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(blinfun_cblinfun_eq ===> (=) ===> (=)) blinfun_apply cblinfun_apply"
  unfolding rel_fun_def by transfer auto

lemma blinfun_of_cblinfun_inj:
  \<open>blinfun_of_cblinfun f = blinfun_of_cblinfun g \<Longrightarrow> f = g\<close>
  by (metis cblinfun_apply_inject blinfun_of_cblinfun.rep_eq)

lemma blinfun_of_cblinfun_inv:
  assumes "\<And>c. \<And>x. f *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (f *\<^sub>v x)"
  shows "\<exists>g. blinfun_of_cblinfun g = f"
  using assms
proof transfer
  show "\<exists>g\<in>Collect bounded_clinear. id g = f"
    if "bounded_linear f"
      and "\<And>c x. f (c *\<^sub>C x) = c *\<^sub>C f x"
    for f :: "'a \<Rightarrow> 'b"
    using that bounded_linear_bounded_clinear by auto
qed

lemma blinfun_of_cblinfun_zero:
  \<open>blinfun_of_cblinfun 0 = 0\<close>
  by transfer simp

lemma blinfun_of_cblinfun_uminus:
  \<open>blinfun_of_cblinfun (- f) = - (blinfun_of_cblinfun f)\<close>
  by transfer auto

lemma blinfun_of_cblinfun_minus:
  \<open>blinfun_of_cblinfun (f - g) = blinfun_of_cblinfun f - blinfun_of_cblinfun g\<close>
  by transfer auto

lemma blinfun_of_cblinfun_scaleC:
  \<open>blinfun_of_cblinfun (c *\<^sub>C f) = c *\<^sub>C (blinfun_of_cblinfun f)\<close>
  by transfer auto

lemma blinfun_of_cblinfun_scaleR:
  \<open>blinfun_of_cblinfun (c *\<^sub>R f) = c *\<^sub>R (blinfun_of_cblinfun f)\<close>
  by transfer auto

lemma blinfun_of_cblinfun_norm:
  fixes f::\<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  shows \<open>norm f = norm (blinfun_of_cblinfun f)\<close>
  by transfer auto

lemma blinfun_of_cblinfun_cblinfun_compose:
  fixes f::\<open>'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector\<close>
    and g::\<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  shows \<open>blinfun_of_cblinfun (f  o\<^sub>C\<^sub>L g) = (blinfun_of_cblinfun f) o\<^sub>L (blinfun_of_cblinfun g)\<close>
  by transfer auto

subsection \<open>Composition\<close>

lemma cblinfun_compose_assoc:
  shows "(A o\<^sub>C\<^sub>L B) o\<^sub>C\<^sub>L C = A o\<^sub>C\<^sub>L (B o\<^sub>C\<^sub>L C)"
  by (metis (no_types, lifting) cblinfun_apply_inject fun.map_comp cblinfun_compose.rep_eq)

lemma cblinfun_compose_zero_right[simp]: "U o\<^sub>C\<^sub>L 0 = 0"
  using bounded_cbilinear.zero_right bounded_cbilinear_cblinfun_compose by blast

lemma cblinfun_compose_zero_left[simp]: "0 o\<^sub>C\<^sub>L U = 0"
  using bounded_cbilinear.zero_left bounded_cbilinear_cblinfun_compose by blast

lemma cblinfun_compose_scaleC_left[simp]:
  fixes A::"'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector"
    and B::"'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b"
  shows \<open>(a *\<^sub>C A) o\<^sub>C\<^sub>L B = a *\<^sub>C (A o\<^sub>C\<^sub>L B)\<close>
  by (simp add: bounded_cbilinear.scaleC_left bounded_cbilinear_cblinfun_compose)

lemma cblinfun_compose_scaleR_left[simp]:
  fixes A::"'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector"
    and B::"'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b"
  shows \<open>(a *\<^sub>R A) o\<^sub>C\<^sub>L B = a *\<^sub>R (A o\<^sub>C\<^sub>L B)\<close>
  by (simp add: scaleR_scaleC)

lemma cblinfun_compose_scaleC_right[simp]:
  fixes A::"'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector"
    and B::"'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b"
  shows \<open>A o\<^sub>C\<^sub>L (a *\<^sub>C B) = a *\<^sub>C (A o\<^sub>C\<^sub>L B)\<close>
  by transfer (auto intro!: ext bounded_clinear.clinear complex_vector.linear_scale)

lemma cblinfun_compose_scaleR_right[simp]:
  fixes A::"'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector"
    and B::"'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b"
  shows \<open>A o\<^sub>C\<^sub>L (a *\<^sub>R B) = a *\<^sub>R (A o\<^sub>C\<^sub>L B)\<close>
  by (simp add: scaleR_scaleC)

lemma cblinfun_compose_id_right[simp]:
  shows "U o\<^sub>C\<^sub>L id_cblinfun = U"
  by transfer auto

lemma cblinfun_compose_id_left[simp]:
  shows "id_cblinfun o\<^sub>C\<^sub>L U  = U"
  by transfer auto

lemma cblinfun_compose_add_left: \<open>(a + b) o\<^sub>C\<^sub>L c = (a o\<^sub>C\<^sub>L c) + (b o\<^sub>C\<^sub>L c)\<close>
  by (simp add: bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose)

lemma cblinfun_compose_add_right: \<open>a o\<^sub>C\<^sub>L (b + c) = (a o\<^sub>C\<^sub>L b) + (a o\<^sub>C\<^sub>L c)\<close>
  by (simp add: bounded_cbilinear.add_right bounded_cbilinear_cblinfun_compose)

lemma cbilinear_cblinfun_compose[simp]: "cbilinear cblinfun_compose"
  by (auto intro!: clinearI simp add: cbilinear_def bounded_cbilinear.add_left bounded_cbilinear.add_right bounded_cbilinear_cblinfun_compose)

lemma cblinfun_compose_sum_left: \<open>(\<Sum>i\<in>S. g i) o\<^sub>C\<^sub>L x = (\<Sum>i\<in>S. g i o\<^sub>C\<^sub>L x)\<close>
  by (induction S rule:infinite_finite_induct) (auto simp: cblinfun_compose_add_left)

lemma cblinfun_compose_sum_right: \<open>x o\<^sub>C\<^sub>L (\<Sum>i\<in>S. g i) = (\<Sum>i\<in>S. x o\<^sub>C\<^sub>L g i)\<close>
  by (induction S rule:infinite_finite_induct) (auto simp: cblinfun_compose_add_right)

lemma cblinfun_compose_minus_right: \<open>a o\<^sub>C\<^sub>L (b - c) = (a o\<^sub>C\<^sub>L b) - (a o\<^sub>C\<^sub>L c)\<close>
  by (simp add: bounded_cbilinear.diff_right bounded_cbilinear_cblinfun_compose)
lemma cblinfun_compose_minus_left: \<open>(a - b) o\<^sub>C\<^sub>L c = (a o\<^sub>C\<^sub>L c) - (b o\<^sub>C\<^sub>L c)\<close>
  by (simp add: bounded_cbilinear.diff_left bounded_cbilinear_cblinfun_compose)


lemma simp_a_oCL_b: \<open>a o\<^sub>C\<^sub>L b = c \<Longrightarrow> a o\<^sub>C\<^sub>L (b o\<^sub>C\<^sub>L d) = c o\<^sub>C\<^sub>L d\<close>
  \<comment> \<open>A convenience lemma to transform simplification rules of the form \<^term>\<open>a o\<^sub>C\<^sub>L b = c\<close>.
     E.g., \<open>simp_a_oCL_b[OF isometryD, simp]\<close> declares a simp-rule for simplifying \<^term>\<open>adj x o\<^sub>C\<^sub>L (x o\<^sub>C\<^sub>L y) = id_cblinfun o\<^sub>C\<^sub>L y\<close>.\<close>
  by (auto simp: cblinfun_compose_assoc)

lemma simp_a_oCL_b': \<open>a o\<^sub>C\<^sub>L b = c \<Longrightarrow> a *\<^sub>V (b *\<^sub>V d) = c *\<^sub>V d\<close>
  \<comment> \<open>A convenience lemma to transform simplification rules of the form \<^term>\<open>a o\<^sub>C\<^sub>L b = c\<close>.
     E.g., \<open>simp_a_oCL_b'[OF isometryD, simp]\<close> declares a simp-rule for simplifying \<^term>\<open>adj x *\<^sub>V x *\<^sub>V y = id_cblinfun *\<^sub>V y\<close>.\<close>
  by auto

lemma cblinfun_compose_uminus_left: \<open>(- a) o\<^sub>C\<^sub>L b = - (a o\<^sub>C\<^sub>L b)\<close>
  by (simp add: bounded_cbilinear.minus_left bounded_cbilinear_cblinfun_compose)

lemma cblinfun_compose_uminus_right: \<open>a o\<^sub>C\<^sub>L (- b) = - (a o\<^sub>C\<^sub>L b)\<close>
  by (simp add: bounded_cbilinear.minus_right bounded_cbilinear_cblinfun_compose)

lemma bounded_clinear_cblinfun_compose_left: \<open>bounded_clinear (\<lambda>x. x o\<^sub>C\<^sub>L y)\<close>
  by (simp add: bounded_cbilinear.bounded_clinear_left bounded_cbilinear_cblinfun_compose)
lemma bounded_clinear_cblinfun_compose_right: \<open>bounded_clinear (\<lambda>y. x o\<^sub>C\<^sub>L y)\<close>
  by (simp add: bounded_cbilinear.bounded_clinear_right bounded_cbilinear_cblinfun_compose)
lemma clinear_cblinfun_compose_left: \<open>clinear (\<lambda>x. x o\<^sub>C\<^sub>L y)\<close>
  by (simp add: bounded_cbilinear.bounded_clinear_left bounded_cbilinear_cblinfun_compose bounded_clinear.clinear)
lemma clinear_cblinfun_compose_right: \<open>clinear (\<lambda>y. x o\<^sub>C\<^sub>L y)\<close>
  by (simp add: bounded_clinear.clinear bounded_clinear_cblinfun_compose_right)

lemma additive_cblinfun_compose_left[simp]: \<open>Modules.additive (\<lambda>x. x o\<^sub>C\<^sub>L a)\<close>
  by (simp add: Modules.additive_def cblinfun_compose_add_left)
lemma additive_cblinfun_compose_right[simp]: \<open>Modules.additive (\<lambda>x. a o\<^sub>C\<^sub>L x)\<close>
  by (simp add: Modules.additive_def cblinfun_compose_add_right)
lemma isCont_cblinfun_compose_left: \<open>isCont (\<lambda>x. x o\<^sub>C\<^sub>L a) y\<close>
  apply (rule clinear_continuous_at)
  by (rule bounded_clinear_cblinfun_compose_left)
lemma isCont_cblinfun_compose_right: \<open>isCont (\<lambda>x. a o\<^sub>C\<^sub>L x) y\<close>
  apply (rule clinear_continuous_at)
  by (rule bounded_clinear_cblinfun_compose_right)

lemma cspan_compose_closed:
  assumes \<open>\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L b \<in> A\<close>
  assumes \<open>a \<in> cspan A\<close> and \<open>b \<in> cspan A\<close>
  shows \<open>a o\<^sub>C\<^sub>L b \<in> cspan A\<close>
proof -
  from \<open>a \<in> cspan A\<close>
  obtain F f where \<open>finite F\<close> and \<open>F \<subseteq> A\<close> and a_def: \<open>a = (\<Sum>x\<in>F. f x *\<^sub>C x)\<close>
    by (smt (verit, del_insts) complex_vector.span_explicit mem_Collect_eq)
  from \<open>b \<in> cspan A\<close>
  obtain G g where \<open>finite G\<close> and \<open>G \<subseteq> A\<close> and b_def: \<open>b = (\<Sum>x\<in>G. g x *\<^sub>C x)\<close>
    by (smt (verit, del_insts) complex_vector.span_explicit mem_Collect_eq)
  have \<open>a o\<^sub>C\<^sub>L b = (\<Sum>(x,y)\<in>F\<times>G. (f x *\<^sub>C x) o\<^sub>C\<^sub>L (g y *\<^sub>C y))\<close>
    apply (simp add: a_def b_def cblinfun_compose_sum_left)
    by (auto intro!: sum.cong simp add: cblinfun_compose_sum_right scaleC_sum_right sum.cartesian_product case_prod_beta)
  also have \<open>\<dots> = (\<Sum>(x,y)\<in>F\<times>G. (f x * g y) *\<^sub>C (x o\<^sub>C\<^sub>L y))\<close>
    by (metis (no_types, opaque_lifting) cblinfun_compose_scaleC_left cblinfun_compose_scaleC_right scaleC_scaleC)
  also have \<open>\<dots> \<in> cspan A\<close>
    using assms \<open>G \<subseteq> A\<close> \<open>F \<subseteq> A\<close>
    apply (auto intro!: complex_vector.span_sum complex_vector.span_scale 
        simp: complex_vector.span_clauses)
    using complex_vector.span_clauses(1) by blast
  finally show ?thesis
    by -
qed

subsection \<open>Adjoint\<close>

lift_definition
  adj :: "'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner \<Rightarrow> 'b \<Rightarrow>\<^sub>C\<^sub>L 'a" ("_*" [99] 100)
  is cadjoint by (fact cadjoint_bounded_clinear)

lemma id_cblinfun_adjoint[simp]: "id_cblinfun* = id_cblinfun"
  by (metis adj.rep_eq apply_id_cblinfun cadjoint_id cblinfun_apply_inject)

lemma double_adj[simp]: "(A*)* = A"
  apply transfer using double_cadjoint by blast

lemma adj_cblinfun_compose[simp]:
  fixes B::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
    and A::\<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_inner\<close>
  shows "(A o\<^sub>C\<^sub>L B)* =  (B*) o\<^sub>C\<^sub>L (A*)"
proof transfer
  fix  A :: \<open>'b \<Rightarrow> 'c\<close> and B :: \<open>'a \<Rightarrow> 'b\<close>
  assume \<open>bounded_clinear A\<close> and \<open>bounded_clinear B\<close>
  hence \<open>bounded_clinear (A \<circ> B)\<close>
    by (simp add: comp_bounded_clinear)
  have \<open>((A \<circ> B) u \<bullet>\<^sub>C v) = (u \<bullet>\<^sub>C (B\<^sup>\<dagger> \<circ> A\<^sup>\<dagger>) v)\<close>
    for u v
    by (metis (no_types, lifting) cadjoint_univ_prop \<open>bounded_clinear A\<close> \<open>bounded_clinear B\<close> cinner_commute' comp_def)
  thus \<open>(A \<circ> B)\<^sup>\<dagger> = B\<^sup>\<dagger> \<circ> A\<^sup>\<dagger>\<close>
    using \<open>bounded_clinear (A \<circ> B)\<close>
    by (metis cadjoint_eqI cinner_commute')
qed

lemma scaleC_adj[simp]: "(a *\<^sub>C A)* = (cnj a) *\<^sub>C (A*)"
  by transfer (simp add: bounded_clinear.bounded_linear bounded_clinear_def complex_vector.linear_scale scaleC_cadjoint)

lemma scaleR_adj[simp]: "(a *\<^sub>R A)* = a *\<^sub>R (A*)"
  by (simp add: scaleR_scaleC)

lemma adj_plus: \<open>(A + B)* = (A*) + (B*)\<close>
proof transfer
  fix A B::\<open>'b \<Rightarrow> 'a\<close>
  assume a1: \<open>bounded_clinear A\<close> and a2: \<open>bounded_clinear B\<close>
  define F where \<open>F = (\<lambda>x. (A\<^sup>\<dagger>) x + (B\<^sup>\<dagger>) x)\<close>
  define G where \<open>G = (\<lambda>x. A x + B x)\<close>
  have \<open>bounded_clinear G\<close>
    unfolding G_def
    by (simp add: a1 a2 bounded_clinear_add)
  moreover have \<open>(F u \<bullet>\<^sub>C v) = (u \<bullet>\<^sub>C G v)\<close> for u v
    unfolding F_def G_def
    using cadjoint_univ_prop a1 a2 cinner_add_left
    by (simp add: cadjoint_univ_prop cinner_add_left cinner_add_right)
  ultimately have \<open>F = G\<^sup>\<dagger> \<close>
    using cadjoint_eqI by blast
  thus \<open>(\<lambda>x. A x + B x)\<^sup>\<dagger> = (\<lambda>x. (A\<^sup>\<dagger>) x + (B\<^sup>\<dagger>) x)\<close>
    unfolding F_def G_def
    by auto
qed

lemma cinner_adj_left:
  fixes G :: "'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a::complex_inner"
  shows \<open>(G* *\<^sub>V x) \<bullet>\<^sub>C y = x \<bullet>\<^sub>C (G *\<^sub>V y)\<close>
  apply transfer using cadjoint_univ_prop by blast

lemma cinner_adj_right:
  fixes G :: "'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a::complex_inner"
  shows \<open>x \<bullet>\<^sub>C (G* *\<^sub>V y) = (G *\<^sub>V x) \<bullet>\<^sub>C y\<close>
  apply transfer using cadjoint_univ_prop' by blast

lemma adj_0[simp]: \<open>0* = 0\<close>
  by (metis add_cancel_right_left adj_plus)

lemma norm_adj[simp]: \<open>norm (A*) = norm A\<close>
  for A :: \<open>'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_inner\<close>
proof (cases \<open>(\<exists>x y :: 'b. x \<noteq> y) \<and> (\<exists>x y :: 'c. x \<noteq> y)\<close>)
  case True
  then have c1: \<open>class.not_singleton TYPE('b)\<close>
    by intro_classes simp
  from True have c2: \<open>class.not_singleton TYPE('c)\<close>
    by intro_classes simp
  have normA: \<open>norm A = (SUP (\<psi>, \<phi>). cmod (\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<phi>)) / (norm \<psi> * norm \<phi>))\<close>
    apply (rule cinner_sup_norm_cblinfun[internalize_sort \<open>'a::{complex_normed_vector,not_singleton}\<close>])
     apply (rule complex_normed_vector_axioms)
    by (rule c1)
  have normAadj: \<open>norm (A*) = (SUP (\<psi>, \<phi>). cmod (\<psi> \<bullet>\<^sub>C (A* *\<^sub>V \<phi>)) / (norm \<psi> * norm \<phi>))\<close>
    apply (rule cinner_sup_norm_cblinfun[internalize_sort \<open>'a::{complex_normed_vector,not_singleton}\<close>])
     apply (rule complex_normed_vector_axioms)
    by (rule c2)

  have \<open>norm (A*) = (SUP (\<psi>, \<phi>). cmod (\<phi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>)) / (norm \<psi> * norm \<phi>))\<close>
    unfolding normAadj
    apply (subst cinner_adj_right)
    apply (subst cinner_commute)
    apply (subst complex_mod_cnj)
    by rule
  also have \<open>\<dots> = Sup ((\<lambda>(\<psi>, \<phi>). cmod (\<phi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>)) / (norm \<psi> * norm \<phi>)) ` prod.swap ` UNIV)\<close>
    by auto
  also have \<open>\<dots> = (SUP (\<phi>, \<psi>). cmod (\<phi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>)) / (norm \<psi> * norm \<phi>))\<close>
    apply (subst image_image)
    by auto
  also have \<open>\<dots> = norm A\<close>
    unfolding normA
    by (simp add: mult.commute)
  finally show ?thesis
    by -
next
  case False
  then consider (b) \<open>\<And>x::'b. x = 0\<close> | (c) \<open>\<And>x::'c. x = 0\<close>
    by auto
  then have \<open>A = 0\<close>
    apply (cases; transfer)
     apply (metis (full_types) bounded_clinear_def complex_vector.linear_0)
    by auto
  then show \<open>norm (A*) = norm A\<close>
    by simp
qed


lemma antilinear_adj[simp]: \<open>antilinear adj\<close>
  by (simp add: adj_plus antilinearI)

lemma bounded_antilinear_adj[bounded_antilinear, simp]: \<open>bounded_antilinear adj\<close>
  by (auto intro!: antilinearI exI[of _ 1] simp: bounded_antilinear_def bounded_antilinear_axioms_def adj_plus)

lemma adjoint_eqI:
  fixes G:: \<open>'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a::complex_inner\<close>
    and F:: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  assumes \<open>\<And>x y. ((cblinfun_apply F) x \<bullet>\<^sub>C y) = (x \<bullet>\<^sub>C (cblinfun_apply G) y)\<close>
  shows \<open>F = G*\<close>
  using assms apply transfer using cadjoint_eqI by auto

lemma adj_uminus: \<open>(-A)* = - (A*)\<close>
  by (metis scaleR_adj scaleR_minus1_left scaleR_minus1_left)

lemma cinner_real_hermiteanI:
  \<comment> \<open>Prop. II.2.12 in \<^cite>\<open>conway2013course\<close>\<close>
  assumes \<open>\<And>\<psi>. \<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>) \<in> \<real>\<close>
  shows \<open>A* = A\<close>
proof -
  { fix g h :: 'a
    {
      fix \<alpha> :: complex
      have \<open>cinner h (A h) + cnj \<alpha> *\<^sub>C cinner g (A h) + \<alpha> *\<^sub>C cinner h (A g) + (abs \<alpha>)\<^sup>2 * cinner g (A g)
        = cinner (h + \<alpha> *\<^sub>C g) (A *\<^sub>V (h + \<alpha> *\<^sub>C g))\<close> (is \<open>?sum4 = _\<close>)
        apply (auto simp: cinner_add_right cinner_add_left cblinfun.add_right cblinfun.scaleC_right ring_class.ring_distribs)
        by (metis cnj_x_x mult.commute)
      also have \<open>\<dots> \<in> \<real>\<close>
        using assms by auto
      finally have \<open>?sum4 = cnj ?sum4\<close>
        using Reals_cnj_iff by fastforce
      then have \<open>cnj \<alpha> *\<^sub>C cinner g (A h) + \<alpha> *\<^sub>C cinner h (A g)
            = \<alpha> *\<^sub>C cinner (A h) g + cnj \<alpha> *\<^sub>C cinner (A g) h\<close>
        using Reals_cnj_iff abs_complex_real assms by force
      also have \<open>\<dots> = \<alpha> *\<^sub>C cinner h (A* *\<^sub>V g) + cnj \<alpha> *\<^sub>C cinner g (A* *\<^sub>V h)\<close>
        by (simp add: cinner_adj_right)
      finally have \<open>cnj \<alpha> *\<^sub>C cinner g (A h) + \<alpha> *\<^sub>C cinner h (A g) = \<alpha> *\<^sub>C cinner h (A* *\<^sub>V g) + cnj \<alpha> *\<^sub>C cinner g (A* *\<^sub>V h)\<close>
        by -
    }
    from this[where \<alpha>2=1] this[where \<alpha>2=\<i>]
    have 1: \<open>cinner g (A h) + cinner h (A g) = cinner h (A* *\<^sub>V g) + cinner g (A* *\<^sub>V h)\<close>
      and i: \<open>- \<i> * cinner g (A h) + \<i> *\<^sub>C cinner h (A g) =  \<i> *\<^sub>C cinner h (A* *\<^sub>V g) - \<i> *\<^sub>C cinner g (A* *\<^sub>V h)\<close>
      by auto
    from arg_cong2[OF 1 arg_cong[OF i, where f=\<open>(*) (-\<i>)\<close>], where f=plus]
    have \<open>cinner h (A g) = cinner h (A* *\<^sub>V g)\<close>
      by (auto simp: ring_class.ring_distribs)
  }
  then show "A* = A"
    apply (rule_tac sym)
    by (simp add: adjoint_eqI cinner_adj_right)
qed


lemma norm_AAadj[simp]: \<open>norm (A o\<^sub>C\<^sub>L A*) = (norm A)\<^sup>2\<close> for A :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::{complex_inner}\<close>
proof (cases \<open>class.not_singleton TYPE('b)\<close>)
  case True
  then have [simp]: \<open>class.not_singleton TYPE('b)\<close>
    by -
  have 1: \<open>(norm A)\<^sup>2 * \<epsilon> \<le> norm (A o\<^sub>C\<^sub>L A*)\<close> if \<open>\<epsilon> < 1\<close> and \<open>\<epsilon> \<ge> 0\<close> for \<epsilon>
  proof -
    obtain \<psi> where \<psi>: \<open>norm ((A*) *\<^sub>V \<psi>) \<ge> norm (A*) * sqrt \<epsilon>\<close> and [simp]: \<open>norm \<psi> = 1\<close>
      apply atomize_elim
      apply (rule cblinfun_norm_approx_witness_mult[internalize_sort' 'a])
      using \<open>\<epsilon> < 1\<close> by (auto intro: complex_normed_vector_class.complex_normed_vector_axioms)
    have \<open>complex_of_real ((norm A)\<^sup>2 * \<epsilon>) = (norm (A*) * sqrt \<epsilon>)\<^sup>2\<close>
      by (simp add: ordered_field_class.sign_simps(23) that(2))
    also have \<open>\<dots> \<le> (norm ((A* *\<^sub>V \<psi>)))\<^sup>2\<close>
      by (meson \<psi> complex_of_real_mono mult_nonneg_nonneg norm_ge_zero power_mono real_sqrt_ge_zero \<open>\<epsilon> \<ge> 0\<close>)
    also have \<open>\<dots> \<le> cinner (A* *\<^sub>V \<psi>) (A* *\<^sub>V \<psi>)\<close>
      by (auto simp flip: power2_norm_eq_cinner)
    also have \<section>: \<open>\<dots> = cinner \<psi> ((A o\<^sub>C\<^sub>L A*) *\<^sub>V \<psi>)\<close>
      by (auto simp: cinner_adj_left)
    also have \<open>\<dots> \<le> norm (A o\<^sub>C\<^sub>L A*)\<close>
      using \<open>norm \<psi> = 1\<close>
      by (smt (verit) Re_complex_of_real \<section> cdot_square_norm cinner_ge_zero cmod_Re complex_inner_class.Cauchy_Schwarz_ineq2 complex_of_real_mono mult_cancel_left1 mult_cancel_right1 norm_cblinfun)
    finally show ?thesis
      by (auto simp: less_eq_complex_def)
  qed
  then have 1: \<open>(norm A)\<^sup>2 \<le> norm (A o\<^sub>C\<^sub>L A*)\<close>
    by (metis field_le_mult_one_interval less_eq_real_def ordered_field_class.sign_simps(5))

  have 2: \<open>norm (A o\<^sub>C\<^sub>L A*) \<le> (norm A)\<^sup>2\<close>
  proof (rule norm_cblinfun_bound)
    show \<open>0 \<le> (norm A)\<^sup>2\<close> by simp
    fix \<psi>
    have \<open>norm ((A o\<^sub>C\<^sub>L A*) *\<^sub>V \<psi>) = norm (A *\<^sub>V A* *\<^sub>V \<psi>)\<close>
      by auto
    also have \<open>\<dots> \<le> norm A * norm (A* *\<^sub>V \<psi>)\<close>
      by (simp add: norm_cblinfun)
    also have \<open>\<dots> \<le> norm A * norm (A*) * norm \<psi>\<close>
      by (metis mult.assoc norm_cblinfun norm_imp_pos_and_ge ordered_comm_semiring_class.comm_mult_left_mono)
    also have \<open>\<dots> = (norm A)\<^sup>2 * norm \<psi>\<close>
      by (simp add: power2_eq_square)
    finally show \<open>norm ((A o\<^sub>C\<^sub>L A*) *\<^sub>V \<psi>) \<le> (norm A)\<^sup>2 * norm \<psi>\<close>
      by -
  qed

  from 1 2 show ?thesis by simp
next
  case False
  then have [simp]: \<open>class.CARD_1 TYPE('b)\<close>
    by (rule not_singleton_vs_CARD_1)
  have \<open>A = 0\<close>
    apply (rule cblinfun_to_CARD_1_0[internalize_sort' 'b])
    by (auto intro: complex_normed_vector_class.complex_normed_vector_axioms)
  then show ?thesis
    by auto
qed

lemma sum_adj: \<open>(sum a F)* = sum (\<lambda>i. (a i)*) F\<close>
  by (induction rule:infinite_finite_induct) (auto simp add: adj_plus)

lemma has_sum_adj:
  assumes \<open>(f has_sum x) I\<close>
  shows \<open>((\<lambda>x. adj (f x)) has_sum adj x) I\<close>

  apply (rule has_sum_comm_additive[where f=adj, unfolded o_def])
  apply (simp add: antilinear.axioms(1))
  apply (metis (no_types, lifting) LIM_eq adj_plus adj_uminus norm_adj uminus_add_conv_diff)
  by (simp add: assms)

lemma adj_minus: \<open>(A - B)* = (A*) - (B*)\<close>
  by (metis add_implies_diff adj_plus diff_add_cancel)

lemma cinner_hermitian_real: \<open>x \<bullet>\<^sub>C (A *\<^sub>V x) \<in> \<real>\<close> if \<open>A* = A\<close>
  by (metis Reals_cnj_iff cinner_adj_right cinner_commute' that)

lemma adj_inject: \<open>adj a = adj b \<longleftrightarrow> a = b\<close>
  by (metis (no_types, opaque_lifting) adj_minus eq_iff_diff_eq_0 norm_adj norm_eq_zero)

lemma norm_AadjA[simp]: \<open>norm (A* o\<^sub>C\<^sub>L A) = (norm A)\<^sup>2\<close> for A :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  by (metis double_adj norm_AAadj norm_adj)

lemma cspan_adj_closed:
  assumes \<open>\<And>a. a \<in> A \<Longrightarrow> a* \<in> A\<close>
  assumes \<open>a \<in> cspan A\<close>
  shows \<open>a* \<in> cspan A\<close>
proof -
  from \<open>a \<in> cspan A\<close>
  obtain F f where \<open>finite F\<close> and \<open>F \<subseteq> A\<close> and \<open>a = (\<Sum>x\<in>F. f x *\<^sub>C x)\<close>
    by (smt (verit, del_insts) complex_vector.span_explicit mem_Collect_eq)
  then have \<open>a* = (\<Sum>x\<in>F. cnj (f x) *\<^sub>C x*)\<close>
    by (auto simp: sum_adj)
  also have \<open>\<dots> \<in> cspan A\<close>
    using assms \<open>F \<subseteq> A\<close>
    by (auto intro!: complex_vector.span_sum complex_vector.span_scale simp: complex_vector.span_clauses)
  finally show ?thesis
    by -
qed

subsection \<open>Powers of operators\<close>

lift_definition cblinfun_power :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> is
  \<open>\<lambda>(a::'a\<Rightarrow>'a) n. a ^^ n\<close>
  apply (rename_tac f n, induct_tac n, auto simp: Nat.funpow_code_def)
  by (simp add: bounded_clinear_compose)

lemma cblinfun_power_0[simp]: \<open>cblinfun_power A 0 = id_cblinfun\<close> 
  by transfer auto

lemma cblinfun_power_Suc': \<open>cblinfun_power A (Suc n) = A o\<^sub>C\<^sub>L cblinfun_power A n\<close> 
  by transfer auto

lemma cblinfun_power_Suc: \<open>cblinfun_power A (Suc n) = cblinfun_power A n o\<^sub>C\<^sub>L A\<close>
  apply (induction n)
  by (auto simp: cblinfun_power_Suc' simp flip:  cblinfun_compose_assoc)

lemma cblinfun_power_compose[simp]: \<open>cblinfun_power A n o\<^sub>C\<^sub>L cblinfun_power A m = cblinfun_power A (n+m)\<close>
  apply (induction n)
  by (auto simp: cblinfun_power_Suc' cblinfun_compose_assoc)

lemma cblinfun_power_scaleC: \<open>cblinfun_power (c *\<^sub>C a) n = c^n *\<^sub>C cblinfun_power a n\<close>
  apply (induction n)
  by (auto simp: cblinfun_power_Suc)

lemma cblinfun_power_scaleR: \<open>cblinfun_power (c *\<^sub>R a) n = c^n *\<^sub>R cblinfun_power a n\<close>
  apply (induction n)
  by (auto simp: cblinfun_power_Suc)

lemma cblinfun_power_uminus: \<open>cblinfun_power (-a) n = (-1)^n *\<^sub>R cblinfun_power a n\<close>
  apply (subst asm_rl[of \<open>-a = (-1) *\<^sub>R a\<close>])
   by simp (rule cblinfun_power_scaleR)

lemma cblinfun_power_adj: \<open>(cblinfun_power S n)* = cblinfun_power (S*) n\<close>
  apply (induction n)
   apply simp
  apply (subst cblinfun_power_Suc)
  apply (subst cblinfun_power_Suc')
  by auto

subsection \<open>Unitaries / isometries\<close>


definition isometry::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner \<Rightarrow> bool\<close> where
  \<open>isometry U \<longleftrightarrow> U* o\<^sub>C\<^sub>L U = id_cblinfun\<close>

definition unitary::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner \<Rightarrow> bool\<close> where
  \<open>unitary U \<longleftrightarrow> (U* o\<^sub>C\<^sub>L U  = id_cblinfun) \<and> (U o\<^sub>C\<^sub>L U* = id_cblinfun)\<close>

lemma unitaryI: \<open>unitary a\<close> if \<open>a* o\<^sub>C\<^sub>L a = id_cblinfun\<close> and \<open>a o\<^sub>C\<^sub>L a* = id_cblinfun\<close>
  unfolding unitary_def using that by simp

lemma unitary_twosided_isometry: "unitary U \<longleftrightarrow> isometry U \<and> isometry (U*)"
  unfolding unitary_def isometry_def by simp

lemma isometryD[simp]: "isometry U \<Longrightarrow> U* o\<^sub>C\<^sub>L U = id_cblinfun"
  unfolding isometry_def by simp

(* Not [simp] because isometryD[simp] + unitary_isometry[simp] already have the same effect *)
lemma unitaryD1: "unitary U \<Longrightarrow> U* o\<^sub>C\<^sub>L U = id_cblinfun"
  unfolding unitary_def by simp

lemma unitaryD2[simp]: "unitary U \<Longrightarrow> U o\<^sub>C\<^sub>L U* = id_cblinfun"
  unfolding unitary_def by simp

lemma unitary_isometry[simp]: "unitary U \<Longrightarrow> isometry U"
  unfolding unitary_def isometry_def by simp

lemma unitary_adj[simp]: "unitary (U*) = unitary U"
  unfolding unitary_def by auto

lemma isometry_cblinfun_compose[simp]:
  assumes "isometry A" and "isometry B"
  shows "isometry (A o\<^sub>C\<^sub>L B)"
proof-
  have "B* o\<^sub>C\<^sub>L A* o\<^sub>C\<^sub>L (A o\<^sub>C\<^sub>L B) = id_cblinfun" if "A* o\<^sub>C\<^sub>L A = id_cblinfun" and "B* o\<^sub>C\<^sub>L B = id_cblinfun"
    using that
    by (smt (verit, del_insts) adjoint_eqI cblinfun_apply_cblinfun_compose cblinfun_id_cblinfun_apply)
  thus ?thesis
    using assms unfolding isometry_def by simp
qed

lemma unitary_cblinfun_compose[simp]: "unitary (A o\<^sub>C\<^sub>L B)"
  if "unitary A" and "unitary B"
  using that
  by (smt (z3) adj_cblinfun_compose cblinfun_compose_assoc cblinfun_compose_id_right double_adj isometryD isometry_cblinfun_compose unitary_def unitary_isometry)

lemma unitary_surj:
  assumes "unitary U"
  shows "surj (cblinfun_apply U)"
  apply (rule surjI[where f=\<open>cblinfun_apply (U*)\<close>])
  using assms unfolding unitary_def apply transfer
  using comp_eq_dest_lhs by force

lemma unitary_id[simp]: "unitary id_cblinfun"
  by (simp add: unitary_def)

lemma orthogonal_on_basis_is_isometry:
  assumes spanB: \<open>ccspan B = \<top>\<close>
  assumes orthoU: \<open>\<And>b c. b\<in>B \<Longrightarrow> c\<in>B \<Longrightarrow> cinner (U *\<^sub>V b) (U *\<^sub>V c) = cinner b c\<close>
  shows \<open>isometry U\<close>
proof -
  have [simp]: \<open>b \<in> closure (cspan B)\<close> for b
    using spanB by transfer simp
  have *: \<open>cinner (U* *\<^sub>V U *\<^sub>V \<psi>) \<phi> = cinner \<psi> \<phi>\<close> if \<open>\<psi>\<in>B\<close> and \<open>\<phi>\<in>B\<close> for \<psi> \<phi>
    by (simp add: cinner_adj_left orthoU that(1) that(2))
  have *: \<open>cinner (U* *\<^sub>V U *\<^sub>V \<psi>) \<phi> = cinner \<psi> \<phi>\<close> if \<open>\<psi>\<in>B\<close> for \<psi> \<phi>
    apply (rule bounded_clinear_eq_on_closure[where t=\<phi> and G=B])
    using bounded_clinear_cinner_right *[OF that]
    by auto
  have \<open>U* *\<^sub>V U *\<^sub>V \<phi> = \<phi>\<close> if \<open>\<phi>\<in>B\<close> for \<phi>
    apply (rule cinner_extensionality)
    apply (subst cinner_eq_flip)
    by (simp add: * that)
  then have \<open>U* o\<^sub>C\<^sub>L U = id_cblinfun\<close>
    by (metis cblinfun_apply_cblinfun_compose cblinfun_eq_gen_eqI cblinfun_id_cblinfun_apply spanB)
  then show \<open>isometry U\<close>
    using isometry_def by blast
qed

lemma isometry_preserves_norm: \<open>isometry U \<Longrightarrow> norm (U *\<^sub>V \<psi>) = norm \<psi>\<close>
  by (metis (no_types, lifting) cblinfun_apply_cblinfun_compose cblinfun_id_cblinfun_apply cinner_adj_right cnorm_eq isometryD)

lemma norm_isometry_compose: 
  assumes \<open>isometry U\<close>
  shows \<open>norm (U o\<^sub>C\<^sub>L A) = norm A\<close>
proof -
  have *: \<open>norm (U *\<^sub>V A *\<^sub>V \<psi>) = norm (A *\<^sub>V \<psi>)\<close> for \<psi>
    by (smt (verit, ccfv_threshold) assms cblinfun_apply_cblinfun_compose cinner_adj_right cnorm_eq id_cblinfun_apply isometryD)

  have \<open>norm (U o\<^sub>C\<^sub>L A) = (SUP \<psi>. norm (U *\<^sub>V A *\<^sub>V \<psi>) / norm \<psi>)\<close>
    unfolding norm_cblinfun_Sup by auto
  also have \<open>\<dots> = (SUP \<psi>. norm (A *\<^sub>V \<psi>) / norm \<psi>)\<close>
    using * by auto
  also have \<open>\<dots> = norm A\<close>
    unfolding norm_cblinfun_Sup by auto
  finally show ?thesis
    by simp
qed

lemma norm_isometry:
  fixes U :: \<open>'a::{chilbert_space,not_singleton} \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner\<close>
  assumes \<open>isometry U\<close>
  shows \<open>norm U = 1\<close>
  apply (subst asm_rl[of \<open>U = U o\<^sub>C\<^sub>L id_cblinfun\<close>], simp)
  apply (subst norm_isometry_compose, simp add: assms)
  by simp

lemma norm_preserving_isometry: \<open>isometry U\<close> if \<open>\<And>\<psi>. norm (U *\<^sub>V \<psi>) = norm \<psi>\<close>
  by (smt (verit, ccfv_SIG) cblinfun_cinner_eqI cblinfun_id_cblinfun_apply cinner_adj_right cnorm_eq isometry_def simp_a_oCL_b' that)

lemma norm_isometry_compose': \<open>norm (A o\<^sub>C\<^sub>L U) = norm A\<close> if \<open>isometry (U*)\<close>
  by (smt (verit) cblinfun_compose_assoc cblinfun_compose_id_right double_adj isometryD mult_cancel_left2 norm_AadjA norm_cblinfun_compose norm_isometry_compose norm_zero power2_eq_square right_diff_distrib that zero_less_norm_iff)

lemma unitary_nonzero[simp]: \<open>\<not> unitary (0 :: 'a::{chilbert_space, not_singleton} \<Rightarrow>\<^sub>C\<^sub>L _)\<close>
  by (simp add: unitary_def)

lemma isometry_inj:
  assumes \<open>isometry U\<close>
  shows \<open>inj_on U X\<close>
  apply (rule inj_on_inverseI[where g=\<open>U*\<close>])
  using assms by (simp flip: cblinfun_apply_cblinfun_compose)

lemma unitary_inj:
  assumes \<open>unitary U\<close>
  shows \<open>inj_on U X\<close>
  apply (rule isometry_inj)
  using assms by simp

lemma unitary_adj_inv: \<open>unitary U \<Longrightarrow> cblinfun_apply (U*) = inv (cblinfun_apply U)\<close>
  apply (rule inj_imp_inv_eq[symmetric])
   apply (simp add: unitary_inj)
  unfolding unitary_def
  by (simp flip: cblinfun_apply_cblinfun_compose)

lemma isometry_cinner_both_sides:
  assumes \<open>isometry U\<close>
  shows \<open>cinner (U x) (U y) = cinner x y\<close>
  using assms by (simp add: flip: cinner_adj_right cblinfun_apply_cblinfun_compose)

lemma isometry_image_is_ortho_set:
  assumes \<open>is_ortho_set A\<close>
  assumes \<open>isometry U\<close>
  shows \<open>is_ortho_set (U ` A)\<close>
  using assms apply (auto simp add: is_ortho_set_def isometry_cinner_both_sides)
  by (metis cinner_eq_zero_iff isometry_cinner_both_sides)

subsection \<open>Product spaces\<close>

lift_definition cblinfun_left :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'b::complex_normed_vector)\<close> is \<open>(\<lambda>x. (x,0))\<close>
  by (auto intro!: bounded_clinearI[where K=1])
lift_definition cblinfun_right :: \<open>'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L ('a::complex_normed_vector\<times>'b)\<close> is \<open>(\<lambda>x. (0,x))\<close>
  by (auto intro!: bounded_clinearI[where K=1])

lemma isometry_cblinfun_left[simp]: \<open>isometry cblinfun_left\<close>
  apply (rule orthogonal_on_basis_is_isometry[of some_chilbert_basis])
   apply simp
  by transfer simp

lemma isometry_cblinfun_right[simp]: \<open>isometry cblinfun_right\<close>
  apply (rule orthogonal_on_basis_is_isometry[of some_chilbert_basis])
   apply simp
  by transfer simp

lemma cblinfun_left_right_ortho[simp]: \<open>cblinfun_left* o\<^sub>C\<^sub>L cblinfun_right = 0\<close>
proof -
  have \<open>x \<bullet>\<^sub>C ((cblinfun_left* o\<^sub>C\<^sub>L cblinfun_right) *\<^sub>V y) = 0\<close> for x :: 'b and y :: 'a
    apply (simp add: cinner_adj_right)
    by transfer auto
  then show ?thesis
    by (metis cblinfun.zero_left cblinfun_eqI cinner_eq_zero_iff)
qed

lemma cblinfun_right_left_ortho[simp]: \<open>cblinfun_right* o\<^sub>C\<^sub>L cblinfun_left = 0\<close>
proof -
  have \<open>x \<bullet>\<^sub>C ((cblinfun_right* o\<^sub>C\<^sub>L cblinfun_left) *\<^sub>V y) = 0\<close> for x :: 'b and y :: 'a
    apply (simp add: cinner_adj_right)
    by transfer auto
  then show ?thesis
    by (metis cblinfun.zero_left cblinfun_eqI cinner_eq_zero_iff)
qed

lemma cblinfun_left_apply[simp]: \<open>cblinfun_left *\<^sub>V \<psi> = (\<psi>,0)\<close>
  by transfer simp

lemma cblinfun_left_adj_apply[simp]: \<open>cblinfun_left* *\<^sub>V \<psi> = fst \<psi>\<close>
  apply (cases \<psi>)
  by (auto intro!: cinner_extensionality[of \<open>_ *\<^sub>V _\<close>] simp: cinner_adj_right)

lemma cblinfun_right_apply[simp]: \<open>cblinfun_right *\<^sub>V \<psi> = (0,\<psi>)\<close>
  by transfer simp

lemma cblinfun_right_adj_apply[simp]: \<open>cblinfun_right* *\<^sub>V \<psi> = snd \<psi>\<close>
  apply (cases \<psi>)
  by (auto intro!: cinner_extensionality[of \<open>_ *\<^sub>V _\<close>] simp: cinner_adj_right)

lift_definition ccsubspace_Times :: \<open>'a::complex_normed_vector ccsubspace \<Rightarrow> 'b::complex_normed_vector ccsubspace \<Rightarrow> ('a\<times>'b) ccsubspace\<close> is
  Product_Type.Times
proof -
  fix S :: \<open>'a set\<close> and T :: \<open>'b set\<close>
  assume [simp]: \<open>closed_csubspace S\<close> \<open>closed_csubspace T\<close>
  have \<open>csubspace (S \<times> T)\<close>
    by (simp add: complex_vector.subspace_Times)
  moreover have \<open>closed (S \<times> T)\<close>
    by (simp add: closed_Times closed_csubspace.closed)
  ultimately show \<open>closed_csubspace (S \<times> T)\<close>
    by (rule closed_csubspace.intro)
qed


lemma ccspan_Times: \<open>ccspan (S \<times> T) = ccsubspace_Times (ccspan S) (ccspan T)\<close> if \<open>0 \<in> S\<close> and \<open>0 \<in> T\<close>
proof (transfer fixing: S T)
  from that have \<open>closure (cspan (S \<times> T)) = closure (cspan S \<times> cspan T)\<close>
    by (simp add: cspan_Times)
  also have \<open>\<dots> = closure (cspan S) \<times> closure (cspan T)\<close>
    using closure_Times by blast
  finally   show \<open>closure (cspan (S \<times> T)) = closure (cspan S) \<times> closure (cspan T)\<close>
    by -
qed

lemma ccspan_Times_sing1: \<open>ccspan ({0::'a::complex_normed_vector} \<times> B) = ccsubspace_Times 0 (ccspan B)\<close>
proof (transfer fixing: B)
  have \<open>closure (cspan ({0::'a} \<times> B)) = closure ({0} \<times> cspan B)\<close>
    by (simp add: complex_vector.span_Times_sing1)
  also have \<open>\<dots> = closure {0} \<times> closure (cspan B)\<close>
    using closure_Times by blast
  also have \<open>\<dots> = {0} \<times> closure (cspan B)\<close>
    by simp
  finally show \<open>closure (cspan ({0::'a} \<times> B)) = {0} \<times> closure (cspan B)\<close>
    by -
qed

lemma ccspan_Times_sing2: \<open>ccspan (B \<times> {0::'a::complex_normed_vector}) = ccsubspace_Times (ccspan B) 0\<close>
proof (transfer fixing: B)
  have \<open>closure (cspan (B \<times> {0::'a})) = closure (cspan B \<times> {0})\<close>
    by (simp add: complex_vector.span_Times_sing2)
  also have \<open>\<dots> = closure (cspan B) \<times> closure {0}\<close>
    using closure_Times by blast
  also have \<open>\<dots> = closure (cspan B) \<times> {0}\<close>
    by simp
  finally show \<open>closure (cspan (B \<times> {0::'a})) = closure (cspan B) \<times> {0}\<close>
    by -
qed

lemma ccsubspace_Times_sup: \<open>sup (ccsubspace_Times A B) (ccsubspace_Times C D) = ccsubspace_Times (sup A C) (sup B D)\<close>
proof transfer
  fix A C :: \<open>'a set\<close> and B D :: \<open>'b set\<close>
  have \<open>A \<times> B +\<^sub>M C \<times> D = closure ((A \<times> B) + (C \<times> D))\<close>
    using closed_sum_def by blast
  also have \<open>\<dots> = closure ((A + C) \<times> (B + D))\<close>
    by (simp add: set_Times_plus_distrib)
  also have \<open>\<dots> = closure (A + C) \<times> closure (B + D)\<close>
    by (simp add: closure_Times)
  also have \<open>\<dots> = (A +\<^sub>M C) \<times> (B +\<^sub>M D)\<close>
    by (simp add: closed_sum_def)
  finally show \<open>A \<times> B +\<^sub>M C \<times> D = (A +\<^sub>M C) \<times> (B +\<^sub>M D)\<close>
    by -
qed

lemma ccsubspace_Times_top_top[simp]: \<open>ccsubspace_Times top top = top\<close>
  by transfer simp

lemma is_ortho_set_prod:
  assumes \<open>is_ortho_set B\<close> \<open>is_ortho_set B'\<close>
  shows \<open>is_ortho_set ((B \<times> {0}) \<union> ({0} \<times> B'))\<close>
  using assms unfolding is_ortho_set_def
  apply (auto simp: is_onb_def is_ortho_set_def zero_prod_def)
  by (meson is_onb_def is_ortho_set_def)+

lemma ccsubspace_Times_ccspan:
  assumes \<open>ccspan B = S\<close> and \<open>ccspan B' = S'\<close>
  shows \<open>ccspan ((B \<times> {0}) \<union> ({0} \<times> B')) = ccsubspace_Times S S'\<close>
  by (smt (z3) Diff_eq_empty_iff Sigma_cong assms(1) assms(2) ccspan.rep_eq ccspan_0 ccspan_Times_sing1 ccspan_Times_sing2 ccspan_of_empty ccspan_remove_0 ccspan_superset ccspan_union ccsubspace_Times_sup complex_vector.span_insert_0 space_as_set_bot sup_bot_left sup_bot_right)

lemma is_onb_prod:
  assumes \<open>is_onb B\<close> \<open>is_onb B'\<close>
  shows \<open>is_onb ((B \<times> {0}) \<union> ({0} \<times> B'))\<close>
  using assms by (auto intro!: is_ortho_set_prod simp add: is_onb_def ccsubspace_Times_ccspan)

subsection \<open>Images\<close>

text \<open>The following definition defines the image of a closed subspace \<^term>\<open>S\<close> under a bounded operator \<^term>\<open>A\<close>.
We do not define that image as the image of \<^term>\<open>A\<close> seen as a function (\<^term>\<open>A ` S\<close>) but as the topological closure of that image.
This is because \<^term>\<open>A ` S\<close> might in general not be closed.

For example, if $e_i$ ($i\in\mathbb N$) form an orthonormal basis, and $A$ maps $e_i$ to $e_i/i$, 
then all $e_i$ are in \<^term>\<open>A ` S\<close>, so the closure of \<^term>\<open>A ` S\<close> is the whole space.
However, $\sum_i e_i/i$ is not in \<^term>\<open>A ` S\<close> because its preimage would have to be $\sum_i e_i$ which does not converge.
So \<^term>\<open>A ` S\<close> does not contain the whole space, hence it is not closed.\<close>

lift_definition cblinfun_image :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector
\<Rightarrow> 'a ccsubspace \<Rightarrow> 'b ccsubspace\<close>  (infixr "*\<^sub>S" 70)
  is "\<lambda>A S. closure (A ` S)"
  using  bounded_clinear_def closed_closure  closed_csubspace.intro
  by (simp add: bounded_clinear_def complex_vector.linear_subspace_image closure_is_closed_csubspace)

lemma cblinfun_image_mono:
  assumes a1: "S \<le> T"
  shows "A *\<^sub>S S \<le> A *\<^sub>S T"
  using a1
  by (simp add: cblinfun_image.rep_eq closure_mono image_mono less_eq_ccsubspace.rep_eq)

lemma cblinfun_image_0[simp]:
  shows "U *\<^sub>S 0 = 0"
  thm zero_ccsubspace_def
  by transfer (simp add: bounded_clinear_def complex_vector.linear_0)

lemma cblinfun_image_bot[simp]: "U *\<^sub>S bot = bot"
  using cblinfun_image_0 by auto

lemma cblinfun_image_sup[simp]:
  fixes A B :: \<open>'a::chilbert_space ccsubspace\<close> and U :: "'a \<Rightarrow>\<^sub>C\<^sub>L'b::chilbert_space"
  shows \<open>U *\<^sub>S (sup A B) = sup (U *\<^sub>S A) (U *\<^sub>S B)\<close>
  apply transfer using bounded_clinear.bounded_linear closure_image_closed_sum by blast

lemma scaleC_cblinfun_image[simp]:
  fixes A :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b :: chilbert_space\<close>
    and S :: \<open>'a ccsubspace\<close> and \<alpha> :: complex
  shows \<open>(\<alpha> *\<^sub>C A) *\<^sub>S S  = \<alpha> *\<^sub>C (A *\<^sub>S S)\<close>
proof-
  have \<open>closure ( ( ((*\<^sub>C) \<alpha>) \<circ> (cblinfun_apply A) ) ` space_as_set S) =
   ((*\<^sub>C) \<alpha>) ` (closure (cblinfun_apply A ` space_as_set S))\<close>
    by (metis closure_scaleC image_comp)
  hence \<open>(closure (cblinfun_apply (\<alpha> *\<^sub>C A) ` space_as_set S)) =
   ((*\<^sub>C) \<alpha>) ` (closure (cblinfun_apply A ` space_as_set S))\<close>
    by (metis (mono_tags, lifting) comp_apply image_cong scaleC_cblinfun.rep_eq)
  hence \<open>Abs_ccsubspace (closure (cblinfun_apply (\<alpha> *\<^sub>C A) ` space_as_set S)) =
            \<alpha> *\<^sub>C Abs_ccsubspace (closure (cblinfun_apply A ` space_as_set S))\<close>
    by (metis space_as_set_inverse cblinfun_image.rep_eq scaleC_ccsubspace.rep_eq)
  have x1: "Abs_ccsubspace (closure ((*\<^sub>V) (\<alpha> *\<^sub>C A) ` space_as_set S)) =
            \<alpha> *\<^sub>C Abs_ccsubspace (closure ((*\<^sub>V) A ` space_as_set S))"
    using \<open>Abs_ccsubspace (closure (cblinfun_apply (\<alpha> *\<^sub>C A) ` space_as_set S)) =
            \<alpha> *\<^sub>C Abs_ccsubspace (closure (cblinfun_apply A ` space_as_set S))\<close>
    by blast
  show ?thesis
    unfolding cblinfun_image_def using x1 by force
qed

lemma cblinfun_image_id[simp]:
  "id_cblinfun *\<^sub>S \<psi> = \<psi>"
  by transfer (simp add: closed_csubspace.closed)

lemma cblinfun_compose_image:
  \<open>(A o\<^sub>C\<^sub>L B) *\<^sub>S S =  A *\<^sub>S (B *\<^sub>S S)\<close>
  apply transfer unfolding image_comp[symmetric]
  apply (rule closure_bounded_linear_image_subset_eq[symmetric])
  by (simp add: bounded_clinear.bounded_linear)

lemmas cblinfun_assoc_left = cblinfun_compose_assoc[symmetric] cblinfun_compose_image[symmetric]
  add.assoc[where ?'a="'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space", symmetric]
lemmas cblinfun_assoc_right = cblinfun_compose_assoc cblinfun_compose_image
  add.assoc[where ?'a="'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space"]

lemma cblinfun_image_INF_leq[simp]:
  fixes U :: "'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::cbanach"
    and V :: "'a \<Rightarrow> 'b ccsubspace"
  shows \<open>U *\<^sub>S (INF i\<in>X. V i) \<le> (INF i\<in>X. U *\<^sub>S (V i))\<close>
  apply transfer
  by (simp add: INT_greatest Inter_lower closure_mono image_mono)

lemma isometry_cblinfun_image_inf_distrib':
  fixes U::\<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::cbanach\<close> and B C::"'a ccsubspace"
  shows "U *\<^sub>S (inf B C) \<le> inf (U *\<^sub>S B) (U *\<^sub>S C)"
proof -
  define V where \<open>V b = (if b then B else C)\<close> for b
  have \<open>U *\<^sub>S (INF i. V i) \<le> (INF i. U *\<^sub>S (V i))\<close>
    by auto
  then show ?thesis
    unfolding V_def
    by (metis (mono_tags, lifting) INF_UNIV_bool_expand)
qed

lemma cblinfun_image_eq:
  fixes S :: "'a::cbanach ccsubspace"
    and A B :: "'a::cbanach \<Rightarrow>\<^sub>C\<^sub>L'b::cbanach"
  assumes "\<And>x. x \<in> G \<Longrightarrow> A *\<^sub>V x = B *\<^sub>V x" and "ccspan G \<ge> S"
  shows "A *\<^sub>S S = B *\<^sub>S S"
proof (use assms in transfer)
  fix G :: "'a set" and A :: "'a \<Rightarrow> 'b" and B :: "'a \<Rightarrow> 'b" and S :: "'a set"
  assume a1: "bounded_clinear A"
  assume a2: "bounded_clinear B"
  assume a3: "\<And>x. x \<in> G \<Longrightarrow> A x = B x"
  assume a4: "S \<subseteq> closure (cspan G)"

  have "A ` closure S = B ` closure S"
    by (smt (verit, best) UnCI a1 a2 a3 a4 bounded_clinear_eq_on_closure closure_Un closure_closure image_cong sup.absorb_iff1)
  then show "closure (A ` S) = closure (B ` S)"
    by (metis bounded_clinear.bounded_linear a1 a2 closure_bounded_linear_image_subset_eq)
qed

lemma cblinfun_fixes_range:
  assumes "A o\<^sub>C\<^sub>L B = B" and "\<psi> \<in> space_as_set (B *\<^sub>S top)"
  shows "A *\<^sub>V \<psi> = \<psi>"
proof-
  define rangeB rangeB' where "rangeB = space_as_set (B *\<^sub>S top)"
    and "rangeB' = range (cblinfun_apply B)"
  from assms have "\<psi> \<in> closure rangeB'"
    by (simp add: cblinfun_image.rep_eq rangeB'_def top_ccsubspace.rep_eq)

  then obtain \<psi>i where \<psi>i_lim: "\<psi>i \<longlonglongrightarrow> \<psi>" and \<psi>i_B: "\<psi>i i \<in> rangeB'" for i
    using closure_sequential by blast
  have A_invariant: "A *\<^sub>V \<psi>i i = \<psi>i i"
    for i
  proof-
    from \<psi>i_B obtain \<phi> where \<phi>: "\<psi>i i = B *\<^sub>V \<phi>"
      using rangeB'_def by blast
    hence "A *\<^sub>V \<psi>i i = (A o\<^sub>C\<^sub>L B) *\<^sub>V \<phi>"
      by (simp add: cblinfun_compose.rep_eq)
    also have "\<dots> = B *\<^sub>V \<phi>"
      by (simp add: assms)
    also have "\<dots> = \<psi>i i"
      by (simp add: \<phi>)
    finally show ?thesis.
  qed
  from \<psi>i_lim have "(\<lambda>i. A *\<^sub>V (\<psi>i i)) \<longlonglongrightarrow> A *\<^sub>V \<psi>"
    by (rule isCont_tendsto_compose[rotated], simp)
  with A_invariant have "(\<lambda>i. \<psi>i i) \<longlonglongrightarrow> A *\<^sub>V \<psi>"
    by auto
  with \<psi>i_lim show "A *\<^sub>V \<psi> = \<psi>"
    using LIMSEQ_unique by blast
qed

lemma zero_cblinfun_image[simp]: "0 *\<^sub>S S = (0::_ ccsubspace)"
  by transfer (simp add: complex_vector.subspace_0 image_constant[where x=0])

lemma cblinfun_image_INF_eq_general:
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space ccsubspace"
    and U :: "'b \<Rightarrow>\<^sub>C\<^sub>L'c::chilbert_space"
    and Uinv :: "'c \<Rightarrow>\<^sub>C\<^sub>L'b"
  assumes UinvUUinv: "Uinv o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Uinv = Uinv" and UUinvU: "U o\<^sub>C\<^sub>L Uinv o\<^sub>C\<^sub>L U = U"
    \<comment> \<open>Meaning: \<^term>\<open>Uinv\<close> is a Pseudoinverse of \<^term>\<open>U\<close>\<close>
    and V: "\<And>i. V i \<le> Uinv *\<^sub>S top"
    and \<open>X \<noteq> {}\<close>
  shows "U *\<^sub>S (INF i\<in>X. V i) = (INF i\<in>X. U *\<^sub>S V i)"
proof (rule antisym)
  show "U *\<^sub>S (INF i\<in>X. V i) \<le> (INF i\<in>X. U *\<^sub>S V i)"
    by (rule cblinfun_image_INF_leq)
next
  define rangeU rangeUinv where "rangeU = U *\<^sub>S top" and "rangeUinv = Uinv *\<^sub>S top"
  define INFUV INFV where INFUV_def: "INFUV = (INF i\<in>X. U *\<^sub>S V i)" and INFV_def: "INFV = (INF i\<in>X. V i)"
  from assms have "V i \<le> rangeUinv"
    for i
    unfolding rangeUinv_def by simp
  moreover have "(Uinv o\<^sub>C\<^sub>L U) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set rangeUinv"
    for \<psi>
    using UinvUUinv cblinfun_fixes_range rangeUinv_def that by fastforce
  ultimately have "(Uinv o\<^sub>C\<^sub>L U) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set (V i)"
    for \<psi> i
    using less_eq_ccsubspace.rep_eq that by blast
  hence d1: "(Uinv o\<^sub>C\<^sub>L U) *\<^sub>S (V i) = (V i)" for i
  proof (transfer fixing: i)
    fix V :: "'a \<Rightarrow> 'b set"
      and Uinv :: "'c \<Rightarrow> 'b"
      and U :: "'b \<Rightarrow> 'c"
    assume "pred_fun \<top> closed_csubspace V"
      and "bounded_clinear Uinv"
      and "bounded_clinear U"
      and "\<And>\<psi> i. \<psi> \<in> V i \<Longrightarrow> (Uinv \<circ> U) \<psi> = \<psi>"
    then show "closure ((Uinv \<circ> U) ` V i) = V i"
    proof auto
      fix x
      from \<open>pred_fun \<top> closed_csubspace V\<close>
      show "x \<in> V i"
        if "x \<in> closure (V i)" 
        using that apply simp
        by (metis orthogonal_complement_of_closure closed_csubspace.subspace double_orthogonal_complement_id closure_is_closed_csubspace)
      with \<open>pred_fun \<top> closed_csubspace V\<close>
      show "x \<in> closure (V i)"
        if "x \<in> V i"
        using that
        using setdist_eq_0_sing_1 setdist_sing_in_set
        by blast
    qed
  qed
  have "U *\<^sub>S V i \<le> rangeU" for i
    by (simp add: cblinfun_image_mono rangeU_def)
  hence "INFUV \<le> rangeU"
    unfolding INFUV_def using \<open>X \<noteq> {}\<close>
    by (metis INF_eq_const INF_lower2)
  moreover have "(U o\<^sub>C\<^sub>L Uinv) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set rangeU" for \<psi>
    using UUinvU cblinfun_fixes_range rangeU_def that by fastforce
  ultimately have x: "(U o\<^sub>C\<^sub>L Uinv) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set INFUV" for \<psi>
    by (simp add: in_mono less_eq_ccsubspace.rep_eq that)

  have "closure ((U \<circ> Uinv) ` INFUV) = INFUV"
    if "closed_csubspace INFUV"
      and "bounded_clinear U"
      and "bounded_clinear Uinv"
      and "\<And>\<psi>. \<psi> \<in> INFUV \<Longrightarrow> (U \<circ> Uinv) \<psi> = \<psi>"
    for INFUV :: "'c set"
    using that
  proof auto
    fix x
    show "x \<in> INFUV" if "x \<in> closure INFUV"
      using that \<open>closed_csubspace INFUV\<close>
      by (metis orthogonal_complement_of_closure closed_csubspace.subspace double_orthogonal_complement_id closure_is_closed_csubspace)
    show "x \<in> closure INFUV"
      if "x \<in> INFUV"
      using that \<open>closed_csubspace INFUV\<close>
      using setdist_eq_0_sing_1 setdist_sing_in_set
      by (simp add: closed_csubspace.closed)
  qed
  hence "(U o\<^sub>C\<^sub>L Uinv) *\<^sub>S INFUV = INFUV"
    by (metis (mono_tags, opaque_lifting) x cblinfun_image.rep_eq cblinfun_image_id id_cblinfun_apply image_cong
        space_as_set_inject)
  hence "INFUV = U *\<^sub>S Uinv *\<^sub>S INFUV"
    by (simp add: cblinfun_compose_image)
  also have "\<dots> \<le> U *\<^sub>S (INF i\<in>X. Uinv *\<^sub>S U *\<^sub>S V i)"
    unfolding INFUV_def
    by (metis cblinfun_image_mono cblinfun_image_INF_leq)
  also have "\<dots> = U *\<^sub>S INFV"
    using d1
    by (metis (no_types, lifting) INFV_def cblinfun_assoc_left(2) image_cong)
  finally show "INFUV \<le> U *\<^sub>S INFV".
qed

lemma unitary_range[simp]:
  assumes "unitary U"
  shows "U *\<^sub>S top = top"
  using assms unfolding unitary_def by transfer (metis closure_UNIV comp_apply surj_def)

lemma range_adjoint_isometry:
  assumes "isometry U"
  shows "U* *\<^sub>S top = top"
proof-
  from assms have "top = U* *\<^sub>S U *\<^sub>S top"
    by (simp add: cblinfun_assoc_left(2))
  also have "\<dots> \<le> U* *\<^sub>S top"
    by (simp add: cblinfun_image_mono)
  finally show ?thesis
    using top.extremum_unique by blast
qed

lemma cblinfun_image_INF_eq[simp]:
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space ccsubspace"
    and U :: "'b \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space"
  assumes \<open>isometry U\<close> \<open>X \<noteq> {}\<close>
  shows "U *\<^sub>S (INF i\<in>X. V i) = (INF i\<in>X. U *\<^sub>S V i)"
proof -
  from \<open>isometry U\<close> have "U* o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L U* = U*"
    unfolding isometry_def by simp
  moreover from \<open>isometry U\<close> have "U o\<^sub>C\<^sub>L U* o\<^sub>C\<^sub>L U = U"
    unfolding isometry_def
    by (simp add: cblinfun_compose_assoc)
  moreover have "V i \<le> U* *\<^sub>S top" for i
    by (simp add: range_adjoint_isometry assms)
  ultimately show ?thesis
    using \<open>X \<noteq> {}\<close> by (rule cblinfun_image_INF_eq_general)
qed

lemma isometry_cblinfun_image_inf_distrib[simp]:
  fixes U::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
    and X Y::"'a ccsubspace"
  assumes "isometry U"
  shows "U *\<^sub>S (inf X Y) = inf (U *\<^sub>S X) (U *\<^sub>S Y)"
  using cblinfun_image_INF_eq[where V="\<lambda>b. if b then X else Y" and U=U and X=UNIV]
  unfolding INF_UNIV_bool_expand
  using assms by auto

lemma cblinfun_image_ccspan:
  shows "A *\<^sub>S ccspan G = ccspan ((*\<^sub>V) A ` G)"
  by transfer (simp add: bounded_clinear.bounded_linear bounded_clinear_def closure_bounded_linear_image_subset_eq complex_vector.linear_span_image)

lemma cblinfun_apply_in_image[simp]: "A *\<^sub>V \<psi> \<in> space_as_set (A *\<^sub>S \<top>)"
  by (metis cblinfun_image.rep_eq closure_subset in_mono range_eqI top_ccsubspace.rep_eq)


lemma cblinfun_plus_image_distr:
  \<open>(A + B) *\<^sub>S S \<le> A *\<^sub>S S \<squnion> B *\<^sub>S S\<close>
  by transfer (smt (verit, ccfv_threshold) closed_closure closed_sum_def closure_minimal closure_subset image_subset_iff set_plus_intro subset_eq)

lemma cblinfun_sum_image_distr:
  \<open>(\<Sum>i\<in>I. A i) *\<^sub>S S \<le> (SUP i\<in>I. A i *\<^sub>S S)\<close>
proof (cases \<open>finite I\<close>)
  case True
  then show ?thesis
  proof induction
    case empty
    then show ?case
      by auto
  next
    case (insert x F)
    then show ?case
      by auto (smt (z3) cblinfun_plus_image_distr inf_sup_aci(6) le_iff_sup)
  qed
next
  case False
  then show ?thesis
    by auto
qed

lemma space_as_set_image_commute:
  assumes UV: \<open>U o\<^sub>C\<^sub>L V = id_cblinfun\<close> and VU: \<open>V o\<^sub>C\<^sub>L U = id_cblinfun\<close>
    (* I think only one of them is needed, can the lemma be strengthened? *)
  shows \<open>(*\<^sub>V) U ` space_as_set T = space_as_set (U *\<^sub>S T)\<close>
proof -
  have \<open>space_as_set (U *\<^sub>S T) = U ` V ` space_as_set (U *\<^sub>S T)\<close>
    by (simp add: image_image UV flip: cblinfun_apply_cblinfun_compose)
  also have \<open>\<dots> \<subseteq> U ` space_as_set (V *\<^sub>S U *\<^sub>S T)\<close>
    by (metis cblinfun_image.rep_eq closure_subset image_mono)
  also have \<open>\<dots> = U ` space_as_set T\<close>
    by (simp add: VU cblinfun_assoc_left(2))
  finally have 1: \<open>space_as_set (U *\<^sub>S T) \<subseteq> U ` space_as_set T\<close>
    by -
  have 2: \<open>U ` space_as_set T \<subseteq> space_as_set (U *\<^sub>S T)\<close>
    by (simp add: cblinfun_image.rep_eq closure_subset)
  from 1 2 show ?thesis
    by simp
qed

lemma right_total_rel_ccsubspace:
  fixes R :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector \<Rightarrow> bool\<close>
  assumes UV: \<open>U o\<^sub>C\<^sub>L V = id_cblinfun\<close>
  assumes VU: \<open>V o\<^sub>C\<^sub>L U = id_cblinfun\<close>
  assumes R_def: \<open>\<And>x y. R x y \<longleftrightarrow> x = U *\<^sub>V y\<close>
  shows \<open>right_total (rel_ccsubspace R)\<close>
proof (rule right_totalI)
  fix T :: \<open>'b ccsubspace\<close>
  show \<open>\<exists>S. rel_ccsubspace R S T\<close>
    apply (rule exI[of _ \<open>U *\<^sub>S T\<close>])
    using UV VU by (auto simp add: rel_ccsubspace_def R_def rel_set_def simp flip: space_as_set_image_commute)
qed

lemma left_total_rel_ccsubspace:
  fixes R :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector \<Rightarrow> bool\<close>
  assumes UV: \<open>U o\<^sub>C\<^sub>L V = id_cblinfun\<close>
  assumes VU: \<open>V o\<^sub>C\<^sub>L U = id_cblinfun\<close>
  assumes R_def: \<open>\<And>x y. R x y \<longleftrightarrow> y = U *\<^sub>V x\<close>
  shows \<open>left_total (rel_ccsubspace R)\<close>
proof -
  have \<open>right_total (rel_ccsubspace (conversep R))\<close>
    apply (rule right_total_rel_ccsubspace)
    using assms by auto
  then show ?thesis
    by (auto intro!: right_total_conversep[THEN iffD1] simp: converse_rel_ccsubspace)
qed

lemma cblinfun_image_bot_zero[simp]: \<open>A *\<^sub>S top = bot \<longleftrightarrow> A = 0\<close>
  by (metis Complex_Bounded_Linear_Function.zero_cblinfun_image bot_ccsubspace.rep_eq cblinfun_apply_in_image cblinfun_eqI empty_iff insert_iff zero_ccsubspace_def)

lemma surj_isometry_is_unitary:
  \<comment> \<open>This lemma is a bit stronger than its name suggests:
      We actually only require that the image of U is dense.

      The converse is @{thm [source] unitary_surj}\<close>
  fixes U :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes \<open>isometry U\<close>
  assumes \<open>U *\<^sub>S \<top> = \<top>\<close>
  shows \<open>unitary U\<close>
  by (metis UNIV_I assms(1) assms(2) cblinfun_assoc_left(1) cblinfun_compose_id_right cblinfun_eqI cblinfun_fixes_range id_cblinfun_apply isometry_def space_as_set_top unitary_def)

lemma cblinfun_apply_in_image': "A *\<^sub>V \<psi> \<in> space_as_set (A *\<^sub>S S)" if \<open>\<psi> \<in> space_as_set S\<close>
  by (metis cblinfun_image.rep_eq closure_subset image_subset_iff that)

lemma cblinfun_image_ccspan_leqI:
  assumes \<open>\<And>v. v \<in> M \<Longrightarrow> A *\<^sub>V v \<in> space_as_set T\<close>
  shows \<open>A *\<^sub>S ccspan M \<le> T\<close>
  by (simp add: assms cblinfun_image_ccspan ccspan_leqI image_subsetI)


lemma cblinfun_same_on_image: \<open>A \<psi> = B \<psi>\<close> if eq: \<open>A o\<^sub>C\<^sub>L C = B o\<^sub>C\<^sub>L C\<close> and mem: \<open>\<psi> \<in> space_as_set (C *\<^sub>S \<top>)\<close>
proof -
  have \<open>A \<psi> = B \<psi>\<close> if \<open>\<psi> \<in> range C\<close> for \<psi>
    by (metis (no_types, lifting) eq cblinfun_apply_cblinfun_compose image_iff that)
  moreover have \<open>\<psi> \<in> closure (range C)\<close>
    by (metis cblinfun_image.rep_eq mem top_ccsubspace.rep_eq)
  ultimately show ?thesis
    apply (rule on_closure_eqI)
    by (auto simp: continuous_on_eq_continuous_at)
qed

lemma lift_cblinfun_comp:
\<comment> \<open>Utility lemma to lift a lemma of the form \<^term>\<open>a o\<^sub>C\<^sub>L b = c\<close>
   to become a more general rewrite rule.\<close>
  assumes \<open>a o\<^sub>C\<^sub>L b = c\<close>
  shows \<open>a o\<^sub>C\<^sub>L b = c\<close>
    and \<open>a o\<^sub>C\<^sub>L (b o\<^sub>C\<^sub>L d) = c o\<^sub>C\<^sub>L d\<close>
    and \<open>a *\<^sub>S (b *\<^sub>S S) = c *\<^sub>S S\<close>
    and \<open>a *\<^sub>V (b *\<^sub>V x) = c *\<^sub>V x\<close>
     apply (fact assms)
    apply (simp add: assms cblinfun_assoc_left(1))
  using assms cblinfun_assoc_left(2) apply force
  using assms by force

lemma cblinfun_image_def2: \<open>A *\<^sub>S S = ccspan ((*\<^sub>V) A ` space_as_set S)\<close>
  apply (simp add: flip: cblinfun_image_ccspan)
  by (metis ccspan_leqI ccspan_superset less_eq_ccsubspace.rep_eq order_class.order_eq_iff)

lemma unitary_image_onb:
  \<comment> \<open>Logically belongs in an earlier section but the proof uses results from this section.\<close>
  assumes \<open>is_onb A\<close>
  assumes \<open>unitary U\<close>
  shows \<open>is_onb (U ` A)\<close>
  using assms
  by (auto simp add: is_onb_def isometry_image_is_ortho_set isometry_preserves_norm
      simp flip: cblinfun_image_ccspan)

subsection \<open>Sandwiches\<close>

lift_definition sandwich :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner) \<Rightarrow> (('a \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow>\<^sub>C\<^sub>L ('b \<Rightarrow>\<^sub>C\<^sub>L 'b))\<close> is
  \<open>\<lambda>(A::'a\<Rightarrow>\<^sub>C\<^sub>L'b) B. A o\<^sub>C\<^sub>L B o\<^sub>C\<^sub>L A*\<close>
proof
  fix A :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> and B B1 B2 :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> and c :: complex
  show \<open>A o\<^sub>C\<^sub>L (B1 + B2) o\<^sub>C\<^sub>L A* = (A o\<^sub>C\<^sub>L B1 o\<^sub>C\<^sub>L A*) + (A o\<^sub>C\<^sub>L B2 o\<^sub>C\<^sub>L A*)\<close>
    by (simp add: cblinfun_compose_add_left cblinfun_compose_add_right)
  show \<open>A o\<^sub>C\<^sub>L (c *\<^sub>C B) o\<^sub>C\<^sub>L A* = c *\<^sub>C (A o\<^sub>C\<^sub>L B o\<^sub>C\<^sub>L A*)\<close>
    by auto
  show \<open>\<exists>K. \<forall>B. norm (A o\<^sub>C\<^sub>L B o\<^sub>C\<^sub>L A*) \<le> norm B * K\<close>
  proof (rule exI[of _ \<open>norm A * norm (A*)\<close>], rule allI)
    fix B
    have \<open>norm (A o\<^sub>C\<^sub>L B o\<^sub>C\<^sub>L A*) \<le> norm (A o\<^sub>C\<^sub>L B) * norm (A*)\<close>
      using norm_cblinfun_compose by blast
    also have \<open>\<dots> \<le> (norm A * norm B) * norm (A*)\<close>
      by (simp add: mult_right_mono norm_cblinfun_compose)
    finally show \<open>norm (A o\<^sub>C\<^sub>L B o\<^sub>C\<^sub>L A*) \<le> norm B * (norm A * norm (A*))\<close>
      by (simp add: mult.assoc vector_space_over_itself.scale_left_commute)
  qed
qed

lemma sandwich_0[simp]: \<open>sandwich 0 = 0\<close>
  by (simp add: cblinfun_eqI sandwich.rep_eq)

lemma sandwich_apply: \<open>sandwich A *\<^sub>V B = A o\<^sub>C\<^sub>L B o\<^sub>C\<^sub>L A*\<close>
  apply (transfer fixing: A B) by auto

lemma sandwich_arg_compose:
  assumes \<open>isometry U\<close>
  shows \<open>sandwich U x o\<^sub>C\<^sub>L sandwich U y = sandwich U (x o\<^sub>C\<^sub>L y)\<close>
  apply (simp add: sandwich_apply)
  by (metis (no_types, lifting) lift_cblinfun_comp(2) assms cblinfun_compose_id_right isometryD)

lemma norm_sandwich: \<open>norm (sandwich A) = (norm A)\<^sup>2\<close> for A :: \<open>'a::{chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'b::{complex_inner}\<close>
proof -
  have main: \<open>norm (sandwich A) = (norm A)\<^sup>2\<close> for A :: \<open>'c::{chilbert_space,not_singleton} \<Rightarrow>\<^sub>C\<^sub>L 'd::{complex_inner}\<close>
  proof (rule norm_cblinfun_eqI)
    show \<open>(norm A)\<^sup>2 \<le> norm (sandwich A *\<^sub>V id_cblinfun) / norm (id_cblinfun :: 'c \<Rightarrow>\<^sub>C\<^sub>L _)\<close>
      apply (auto simp: sandwich_apply)
      by -
    fix B
    have \<open>norm (sandwich A *\<^sub>V B) \<le> norm (A o\<^sub>C\<^sub>L B) * norm (A*)\<close>
      using norm_cblinfun_compose by (auto simp: sandwich_apply simp del: norm_adj)
    also have \<open>\<dots> \<le> (norm A * norm B) * norm (A*)\<close>
      by (simp add: mult_right_mono norm_cblinfun_compose)
    also have \<open>\<dots> \<le> (norm A)\<^sup>2 * norm B\<close>
      by (simp add: power2_eq_square mult.assoc vector_space_over_itself.scale_left_commute)
    finally show \<open>norm (sandwich A *\<^sub>V B) \<le> (norm A)\<^sup>2 * norm B\<close>
      by -
    show \<open>0 \<le> (norm A)\<^sup>2\<close>
      by auto
  qed

  show ?thesis
  proof (cases \<open>class.not_singleton TYPE('a)\<close>)
    case True
    show ?thesis
      apply (rule main[internalize_sort' 'c2])
       apply standard[1]
      using True by simp
  next
    case False
    have \<open>A = 0\<close>
      apply (rule cblinfun_from_CARD_1_0[internalize_sort' 'a])
       apply (rule not_singleton_vs_CARD_1)
       apply (rule False)
      by standard
    then show ?thesis
      by simp
  qed
qed

lemma sandwich_apply_adj: \<open>sandwich A (B*) = (sandwich A B)*\<close>
  by (simp add: cblinfun_assoc_left(1) sandwich_apply)

lemma sandwich_id[simp]: "sandwich id_cblinfun = id_cblinfun"
  apply (rule cblinfun_eqI)
  by (auto simp: sandwich_apply)

lemma sandwich_compose: \<open>sandwich (A o\<^sub>C\<^sub>L B) = sandwich A o\<^sub>C\<^sub>L sandwich B\<close>
  by (auto intro!: cblinfun_eqI simp: sandwich_apply)

lemma inj_sandwich_isometry: \<open>inj (sandwich U)\<close> if [simp]: \<open>isometry U\<close> for U :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  apply (rule inj_on_inverseI[where g=\<open>(*\<^sub>V) (sandwich (U*))\<close>])
  by (auto simp flip: cblinfun_apply_cblinfun_compose sandwich_compose)

lemma sandwich_isometry_id: \<open>isometry (U*) \<Longrightarrow> sandwich U id_cblinfun = id_cblinfun\<close>
  by (simp add: sandwich_apply isometry_def)


subsection \<open>Projectors\<close>

lift_definition Proj :: "('a::chilbert_space) ccsubspace \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L'a"
  is \<open>projection\<close>
  by (rule projection_bounded_clinear)

lemma Proj_range[simp]: "Proj S *\<^sub>S top = S"
proof transfer
  fix S :: \<open>'a set\<close> assume \<open>closed_csubspace S\<close>
  then have "closure (range (projection S)) \<subseteq> S"
    by (metis closed_csubspace.closed closed_csubspace.subspace closure_closed complex_vector.subspace_0 csubspace_is_convex dual_order.eq_iff insert_absorb insert_not_empty projection_image)
  moreover have "S \<subseteq> closure (range (projection S))"
    using \<open>closed_csubspace S\<close>
    by (metis closed_csubspace_def closure_subset csubspace_is_convex equals0D projection_image subset_iff)
  ultimately show \<open>closure (range (projection S)) = S\<close>
    by auto
qed

lemma adj_Proj: \<open>(Proj M)* = Proj M\<close>
  by transfer (simp add: projection_cadjoint)

lemma Proj_idempotent[simp]: \<open>Proj M o\<^sub>C\<^sub>L Proj M = Proj M\<close>
proof -
  have u1: \<open>(cblinfun_apply (Proj M)) = projection (space_as_set M)\<close>
    by transfer blast
  have \<open>closed_csubspace (space_as_set M)\<close>
    using space_as_set by auto
  hence u2: \<open>(projection (space_as_set M))\<circ>(projection (space_as_set M))
                = (projection (space_as_set M))\<close>
    using projection_idem by fastforce
  have \<open>(cblinfun_apply (Proj M)) \<circ> (cblinfun_apply (Proj M)) = cblinfun_apply (Proj M)\<close>
    using u1 u2
    by simp
  hence \<open>cblinfun_apply ((Proj M) o\<^sub>C\<^sub>L (Proj M)) = cblinfun_apply (Proj M)\<close>
    by (simp add: cblinfun_compose.rep_eq)
  thus ?thesis using cblinfun_apply_inject
    by auto
qed

lift_definition is_Proj :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> bool\<close> is
  \<open>\<lambda>P. \<exists>M. is_projection_on P M\<close> .

lemma is_Proj_id[simp]: \<open>is_Proj id_cblinfun\<close>
  apply transfer
  by (auto intro!: exI[of _ UNIV] simp: is_projection_on_def is_arg_min_def)

lemma Proj_top[simp]: \<open>Proj \<top> = id_cblinfun\<close>
  by (metis Proj_idempotent Proj_range cblinfun_eqI cblinfun_fixes_range id_cblinfun_apply iso_tuple_UNIV_I space_as_set_top)

lemma Proj_on_own_range':
  fixes P :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L'a\<close>
  assumes \<open>P o\<^sub>C\<^sub>L P = P\<close> and \<open>P = P*\<close>
  shows \<open>Proj (P *\<^sub>S top) = P\<close>
proof -
  define M where "M = P *\<^sub>S top"
  have v3: "x \<in> (\<lambda>x. x - P *\<^sub>V x) -` {0}"
    if "x \<in> range (cblinfun_apply P)"
    for x :: 'a
  proof-
    have v3_1: \<open>cblinfun_apply P \<circ> cblinfun_apply P = cblinfun_apply P\<close>
      by (metis \<open>P o\<^sub>C\<^sub>L P = P\<close> cblinfun_compose.rep_eq)
    have \<open>\<exists>t. P *\<^sub>V t = x\<close>
      using that by blast
    then obtain t where t_def: \<open>P *\<^sub>V t = x\<close>
      by blast
    hence \<open>x - P *\<^sub>V x = x - P *\<^sub>V (P *\<^sub>V t)\<close>
      by simp
    also have \<open>\<dots> = x - (P *\<^sub>V t)\<close>
      using v3_1
      by (metis comp_apply)
    also have \<open>\<dots> = 0\<close>
      by (simp add: t_def)
    finally have \<open>x - P *\<^sub>V x = 0\<close>
      by blast
    thus ?thesis
      by simp
  qed

  have v1: "range (cblinfun_apply P) \<subseteq> (\<lambda>x. x - cblinfun_apply P x) -` {0}"
    using v3
    by blast

  have "x \<in> range (cblinfun_apply P)"
    if "x \<in> (\<lambda>x. x - P *\<^sub>V x) -` {0}"
    for x :: 'a
  proof-
    have x1:\<open>x - P *\<^sub>V x = 0\<close>
      using that by blast
    have \<open>x = P *\<^sub>V x\<close>
      by (simp add: x1 eq_iff_diff_eq_0)
    thus ?thesis
      by blast
  qed
  hence v2: "(\<lambda>x. x - cblinfun_apply P x) -` {0} \<subseteq> range (cblinfun_apply P)"
    by blast
  have i1: \<open>range (cblinfun_apply P) = (\<lambda> x. x - cblinfun_apply P x) -` {0}\<close>
    using v1 v2
    by (simp add: v1 dual_order.antisym)
  have p1: \<open>closed {(0::'a)}\<close>
    by simp
  have p2: \<open>continuous (at x) (\<lambda> x. x - P *\<^sub>V x)\<close>
    for x
  proof-
    have \<open>cblinfun_apply (id_cblinfun - P) = (\<lambda> x. x - P *\<^sub>V x)\<close>
      by (simp add: id_cblinfun.rep_eq minus_cblinfun.rep_eq)
    hence \<open>bounded_clinear (cblinfun_apply (id_cblinfun - P))\<close>
      using cblinfun_apply
      by blast
    hence \<open>continuous (at x) (cblinfun_apply (id_cblinfun - P))\<close>
      by (simp add: clinear_continuous_at)
    thus ?thesis
      using \<open>cblinfun_apply (id_cblinfun - P) = (\<lambda> x. x - P *\<^sub>V x)\<close>
      by simp
  qed

  have i2: \<open>closed ( (\<lambda> x. x - P *\<^sub>V x) -` {0} )\<close>
    using p1 p2
    by (rule Abstract_Topology.continuous_closed_vimage)

  have \<open>closed (range (cblinfun_apply P))\<close>
    using i1 i2
    by simp
  have u2: \<open>cblinfun_apply P x \<in> space_as_set M\<close>
    for x
    by (simp add: M_def \<open>closed (range ((*\<^sub>V) P))\<close> cblinfun_image.rep_eq top_ccsubspace.rep_eq)

  have xy: \<open>is_orthogonal (x - P *\<^sub>V x) y\<close>
    if y1: \<open>y \<in> space_as_set M\<close>
    for x y
  proof-
    have \<open>\<exists>t. y = P *\<^sub>V t\<close>
      using y1
      by (simp add:  M_def \<open>closed (range ((*\<^sub>V) P))\<close> cblinfun_image.rep_eq image_iff
          top_ccsubspace.rep_eq)
    then obtain t where t_def: \<open>y = P *\<^sub>V t\<close>
      by blast
    have \<open>(x - P *\<^sub>V x) \<bullet>\<^sub>C y = (x - P *\<^sub>V x) \<bullet>\<^sub>C (P *\<^sub>V t)\<close>
      by (simp add: t_def)
    also have \<open>\<dots> = (P *\<^sub>V (x - P *\<^sub>V x)) \<bullet>\<^sub>C t\<close>
      by (metis \<open>P = P*\<close> cinner_adj_left)
    also have \<open>\<dots> = (P *\<^sub>V x - P *\<^sub>V (P *\<^sub>V x)) \<bullet>\<^sub>C t\<close>
      by (simp add: cblinfun.diff_right)
    also have \<open>\<dots> = (P *\<^sub>V x - P *\<^sub>V x) \<bullet>\<^sub>C t\<close>
      by (metis assms(1) comp_apply cblinfun_compose.rep_eq)
    also have \<open>\<dots> = (0 \<bullet>\<^sub>C t)\<close>
      by simp
    also have \<open>\<dots> = 0\<close>
      by simp
    finally show ?thesis by blast
  qed
  hence u1: \<open>x - P *\<^sub>V x \<in> orthogonal_complement (space_as_set M)\<close>
    for x
    by (simp add: orthogonal_complementI)
  have "closed_csubspace (space_as_set M)"
    using space_as_set by auto
  hence f1: "(Proj M) *\<^sub>V a = P *\<^sub>V a" for a
    by (simp add: Proj.rep_eq projection_eqI u1 u2)
  have "(+) ((P - Proj M) *\<^sub>V a) = id" for a
    using f1
    by (auto intro!: ext simp add: minus_cblinfun.rep_eq)
  hence "b - b = cblinfun_apply (P - Proj M) a"
    for a b
    by (metis (no_types) add_diff_cancel_right' id_apply)
  hence "cblinfun_apply (id_cblinfun - (P - Proj M)) a = a"
    for a
    by (simp add: minus_cblinfun.rep_eq)
  thus ?thesis
    using u1 u2 cblinfun_apply_inject diff_diff_eq2 diff_eq_diff_eq eq_id_iff id_cblinfun.rep_eq
    by (metis (no_types, opaque_lifting) M_def)
qed

lemma Proj_range_closed:
  assumes "is_Proj P"
  shows "closed (range (cblinfun_apply P))"
  apply (rule is_projection_on_closed[where f=\<open>cblinfun_apply P\<close>])
  using assms is_Proj.rep_eq is_projection_on_image by auto

lemma Proj_is_Proj[simp]:
  fixes M::\<open>'a::chilbert_space ccsubspace\<close>
  shows \<open>is_Proj (Proj M)\<close>
proof-
  have u1: "closed_csubspace (space_as_set M)"
    using space_as_set by blast
  have v1: "h - Proj M *\<^sub>V h
         \<in> orthogonal_complement (space_as_set M)" for h
    by (simp add: Proj.rep_eq orthogonal_complementI projection_orthogonal u1)
  have v2: "Proj M *\<^sub>V h \<in> space_as_set M" for h
    by (metis Proj.rep_eq mem_Collect_eq orthog_proj_exists projection_eqI space_as_set)
  have u2: "is_projection_on ((*\<^sub>V) (Proj M)) (space_as_set M)"
    unfolding is_projection_on_def
    by (simp add: smallest_dist_is_ortho u1 v1 v2)
  show ?thesis
    using u1 u2 is_Proj.rep_eq by blast
qed

lemma is_Proj_algebraic:
  fixes P::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  shows \<open>is_Proj P \<longleftrightarrow> P o\<^sub>C\<^sub>L P = P \<and> P = P*\<close>
proof
  have "P o\<^sub>C\<^sub>L P = P"
    if "is_Proj P"
    using that apply transfer
    using is_projection_on_idem
    by fastforce
  moreover have "P = P*"
    if "is_Proj P"
    using that Proj_range_closed[OF that] is_projection_on_cadjoint[where \<pi>=P and M=\<open>range P\<close>]
    by transfer (metis bounded_clinear.axioms(1) closed_csubspace_UNIV closed_csubspace_def complex_vector.linear_subspace_image is_projection_on_image)
  ultimately show "P o\<^sub>C\<^sub>L P = P \<and> P = P*"
    if "is_Proj P"
    using that
    by blast
  show "is_Proj P"
    if "P o\<^sub>C\<^sub>L P = P \<and> P = P*"
    using that Proj_on_own_range' Proj_is_Proj by metis
qed

lemma Proj_on_own_range:
  fixes P :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L'a\<close>
  assumes \<open>is_Proj P\<close>
  shows \<open>Proj (P *\<^sub>S top) = P\<close>
  using Proj_on_own_range' assms is_Proj_algebraic by blast

lemma Proj_image_leq: "(Proj S) *\<^sub>S A \<le> S"
  by (metis Proj_range inf_top_left le_inf_iff isometry_cblinfun_image_inf_distrib')

lemma Proj_sandwich:
  fixes A::"'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space"
  assumes "isometry A"
  shows "sandwich A *\<^sub>V Proj S = Proj (A *\<^sub>S S)"
proof -
  define P where \<open>P = A o\<^sub>C\<^sub>L Proj S o\<^sub>C\<^sub>L (A*)\<close>
  have \<open>P o\<^sub>C\<^sub>L P = P\<close>
    using assms
    unfolding P_def isometry_def
    by (metis (no_types, lifting) Proj_idempotent cblinfun_assoc_left(1) cblinfun_compose_id_left)
  moreover have \<open>P = P*\<close>
    unfolding P_def
    by (metis adj_Proj adj_cblinfun_compose cblinfun_assoc_left(1) double_adj)
  ultimately have
    \<open>\<exists>M. P = Proj M \<and> space_as_set M = range (cblinfun_apply (A o\<^sub>C\<^sub>L (Proj S) o\<^sub>C\<^sub>L (A*)))\<close>
    using P_def Proj_on_own_range'
    by (metis Proj_is_Proj Proj_range_closed cblinfun_image.rep_eq closure_closed top_ccsubspace.rep_eq)
  then obtain M where \<open>P = Proj M\<close>
    and \<open>space_as_set M = range (cblinfun_apply (A o\<^sub>C\<^sub>L (Proj S) o\<^sub>C\<^sub>L (A*)))\<close>
    by blast

  have f1: "A o\<^sub>C\<^sub>L Proj S = P o\<^sub>C\<^sub>L A"
    by (simp add: P_def assms cblinfun_compose_assoc)
  hence "P o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L A* = P"
    using P_def by presburger
  hence "(P o\<^sub>C\<^sub>L A) *\<^sub>S (c \<squnion> A* *\<^sub>S d) = P *\<^sub>S (A *\<^sub>S c \<squnion> d)"
    for c d

    by (simp add: cblinfun_assoc_left(2))
  hence "P *\<^sub>S (A *\<^sub>S \<top> \<squnion> c) = (P o\<^sub>C\<^sub>L A) *\<^sub>S \<top>"
    for c
    by (metis sup_top_left)
  hence \<open>M = A *\<^sub>S S\<close>
    using f1
    by (metis \<open>P = Proj M\<close> cblinfun_assoc_left(2) Proj_range sup_top_right)
  thus ?thesis
    using \<open>P = Proj M\<close>
    unfolding P_def sandwich_apply by blast
qed

lemma Proj_orthog_ccspan_union:
  assumes "\<And>x y. x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> is_orthogonal x y"
  shows \<open>Proj (ccspan (X \<union> Y)) = Proj (ccspan X) + Proj (ccspan Y)\<close>
proof -
  have \<open>x \<in> cspan X \<Longrightarrow> y \<in> cspan Y \<Longrightarrow> is_orthogonal x y\<close> for x y
    apply (rule is_orthogonal_closure_cspan[where X=X and Y=Y])
    using closure_subset assms by auto
  then have \<open>x \<in> closure (cspan X) \<Longrightarrow> y \<in> closure (cspan Y) \<Longrightarrow> is_orthogonal x y\<close> for x y
    by (metis orthogonal_complementI orthogonal_complement_of_closure orthogonal_complement_orthoI')
  then show ?thesis
    apply (transfer fixing: X Y)
    apply (subst projection_plus[symmetric])
    by auto
qed

abbreviation proj :: "'a::chilbert_space \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'a" where "proj \<psi> \<equiv> Proj (ccspan {\<psi>})"

lemma proj_0[simp]: \<open>proj 0 = 0\<close>
  by transfer auto

lemma ccsubspace_supI_via_Proj:
  fixes A B C::"'a::chilbert_space ccsubspace"
  assumes a1: \<open>Proj (- C) *\<^sub>S A \<le> B\<close>
  shows  "A \<le> B \<squnion> C"
proof-
  have x2: \<open>x \<in> space_as_set B\<close>
    if "x \<in>  closure ( (projection (orthogonal_complement (space_as_set C))) ` space_as_set A)" for x
    using that
    by (metis Proj.rep_eq cblinfun_image.rep_eq assms less_eq_ccsubspace.rep_eq subsetD
        uminus_ccsubspace.rep_eq)
  have q1: \<open>x \<in> closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> space_as_set B \<and> \<phi> \<in> space_as_set C}\<close>
    if \<open>x \<in> space_as_set A\<close>
    for x
  proof-
    have p1: \<open>closed_csubspace (space_as_set C)\<close>
      using space_as_set by auto
    hence \<open>x = (projection (space_as_set C)) x
       + (projection (orthogonal_complement (space_as_set C))) x\<close>
      by simp
    hence \<open>x = (projection (orthogonal_complement (space_as_set C))) x
              + (projection (space_as_set C)) x\<close>
      by (metis ordered_field_class.sign_simps(2))
    moreover have \<open>(projection (orthogonal_complement (space_as_set C))) x \<in> space_as_set B\<close>
      using x2
      by (meson closure_subset image_subset_iff that)
    moreover have \<open>(projection (space_as_set C)) x \<in> space_as_set C\<close>
      by (metis mem_Collect_eq orthog_proj_exists projection_eqI space_as_set)
    ultimately show ?thesis
      using closure_subset by force
  qed
  have x1: \<open>x \<in> (space_as_set B +\<^sub>M space_as_set C)\<close>
    if "x \<in> space_as_set A" for x
  proof -
    have f1: "x \<in> closure {a + b |a b. a \<in> space_as_set B \<and> b \<in> space_as_set C}"
      by (simp add: q1 that)
    have "{a + b |a b. a \<in> space_as_set B \<and> b \<in> space_as_set C} = {a. \<exists>p. p \<in> space_as_set B
      \<and> (\<exists>q. q \<in> space_as_set C \<and> a = p + q)}"
      by blast
    hence "x \<in> closure {a. \<exists>b\<in>space_as_set B. \<exists>c\<in>space_as_set C. a = b + c}"
      using f1 by (simp add: Bex_def_raw)
    thus ?thesis
      using that
      unfolding closed_sum_def set_plus_def
      by blast
  qed

  hence \<open>x \<in> space_as_set (Abs_ccsubspace (space_as_set B +\<^sub>M space_as_set C))\<close>
    if "x \<in> space_as_set A" for x
    using that
    by (metis space_as_set_inverse sup_ccsubspace.rep_eq)
  thus ?thesis
    by (simp add: x1 less_eq_ccsubspace.rep_eq subset_eq sup_ccsubspace.rep_eq)
qed

lemma is_Proj_idempotent:
  assumes "is_Proj P"
  shows "P o\<^sub>C\<^sub>L P = P"
  using assms apply transfer
  using is_projection_on_fixes_image is_projection_on_in_image by fastforce

lemma is_proj_selfadj:
  assumes "is_Proj P"
  shows "P* = P"
  using assms
  unfolding is_Proj_def
  by (metis is_Proj_algebraic is_Proj_def)

lemma is_Proj_I:
  assumes "P o\<^sub>C\<^sub>L P = P" and "P* = P"
  shows "is_Proj P"
  using assms is_Proj_algebraic by metis

lemma is_Proj_0[simp]: "is_Proj 0"
  apply transfer apply (rule exI[of _ 0])
  by (simp add: is_projection_on_zero)

lemma is_Proj_complement[simp]:
  fixes P :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes a1: "is_Proj P"
  shows "is_Proj (id_cblinfun - P)"
  by (smt (z3) add_diff_cancel_left add_diff_cancel_left' adj_cblinfun_compose adj_plus assms bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose diff_add_cancel id_cblinfun_adjoint is_Proj_algebraic cblinfun_compose_id_left)

lemma Proj_bot[simp]: "Proj bot = 0"
  by (metis zero_cblinfun_image Proj_on_own_range' is_Proj_0 is_Proj_algebraic
      zero_ccsubspace_def)

lemma Proj_ortho_compl:
  "Proj (- X) = id_cblinfun - Proj X"
  by (transfer, auto)

lemma Proj_inj:
  assumes "Proj X = Proj Y"
  shows "X = Y"
  by (metis assms Proj_range)

lemma norm_Proj_leq1: \<open>norm (Proj M) \<le> 1\<close> for M :: \<open>'a :: chilbert_space ccsubspace\<close>
  by transfer (metis (no_types, opaque_lifting) mult.left_neutral onorm_bound projection_reduces_norm zero_less_one_class.zero_le_one)

lemma Proj_orthog_ccspan_insert:
  assumes "\<And>y. y \<in> Y \<Longrightarrow> is_orthogonal x y"
  shows \<open>Proj (ccspan (insert x Y)) = proj x + Proj (ccspan Y)\<close>
  apply (subst asm_rl[of \<open>insert x Y = {x} \<union> Y\<close>], simp)
  apply (rule Proj_orthog_ccspan_union)
  using assms by auto

lemma Proj_fixes_image: \<open>Proj S *\<^sub>V \<psi> = \<psi>\<close> if \<open>\<psi> \<in> space_as_set S\<close>
  by (metis Proj_idempotent Proj_range that cblinfun_fixes_range)

lemma norm_is_Proj: \<open>norm P \<le> 1\<close> if \<open>is_Proj P\<close> for P :: \<open>'a :: chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  by (metis Proj_on_own_range norm_Proj_leq1 that)

lemma Proj_sup: \<open>orthogonal_spaces S T \<Longrightarrow> Proj (sup S T) = Proj S + Proj T\<close>
  unfolding orthogonal_spaces_def
  by transfer (simp add: projection_plus)

lemma Proj_sum_spaces:
  assumes \<open>finite X\<close>
  assumes \<open>\<And>x y. x\<in>X \<Longrightarrow> y\<in>X \<Longrightarrow> x\<noteq>y \<Longrightarrow> orthogonal_spaces (J x) (J y)\<close>
  shows \<open>Proj (\<Sum>x\<in>X. J x) = (\<Sum>x\<in>X. Proj (J x))\<close>
  using assms
proof induction
  case empty
  show ?case 
    by auto
next
  case (insert x F)
  have \<open>Proj (sum J (insert x F)) = Proj (J x \<squnion> sum J F)\<close>
    by (simp add: insert)
  also have \<open>\<dots> = Proj (J x) + Proj (sum J F)\<close>
    apply (rule Proj_sup)
    apply (rule orthogonal_sum)
    using insert by auto
  also have \<open>\<dots> = (\<Sum>x\<in>insert x F. Proj (J x))\<close>
    by (simp add: insert.IH insert.hyps(1) insert.hyps(2) insert.prems)
  finally show ?case
    by -
qed

lemma is_Proj_reduces_norm:
  fixes P :: \<open>'a::complex_inner \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>is_Proj P\<close>
  shows \<open>norm (P *\<^sub>V \<psi>) \<le> norm \<psi>\<close>
  apply (rule is_projection_on_reduces_norm[where M=\<open>range P\<close>])
  using assms is_Proj.rep_eq is_projection_on_image by blast (simp add: Proj_range_closed assms closed_csubspace.intro)

lemma norm_Proj_apply: \<open>norm (Proj T *\<^sub>V \<psi>) = norm \<psi> \<longleftrightarrow> \<psi> \<in> space_as_set T\<close>
proof (rule iffI)
  show \<open>norm (Proj T *\<^sub>V \<psi>) = norm \<psi>\<close> if \<open>\<psi> \<in> space_as_set T\<close>
    by (simp add: Proj_fixes_image that)
  assume assm: \<open>norm (Proj T *\<^sub>V \<psi>) = norm \<psi>\<close>
  have \<psi>_decomp: \<open>\<psi> = Proj T \<psi> + Proj (-T) \<psi>\<close>
    by (simp add: Proj_ortho_compl cblinfun.real.diff_left)
  have \<open>(norm (Proj (-T) \<psi>))\<^sup>2 = (norm (Proj T \<psi>))\<^sup>2 + (norm (Proj (-T) \<psi>))\<^sup>2 - (norm (Proj T \<psi>))\<^sup>2\<close>
    by auto
  also have \<open>\<dots> = (norm (Proj T \<psi> + Proj (-T) \<psi>))\<^sup>2 - (norm (Proj T \<psi>))\<^sup>2\<close>
    apply (subst pythagorean_theorem)
     apply (metis (no_types, lifting) Proj_idempotent \<psi>_decomp add_cancel_right_left adj_Proj cblinfun.real.add_right cblinfun_apply_cblinfun_compose cinner_adj_left cinner_zero_left)
    by simp
  also with \<psi>_decomp have \<open>\<dots> = (norm \<psi>)\<^sup>2 - (norm (Proj T \<psi>))\<^sup>2\<close>
    by metis
  also with assm have \<open>\<dots> = 0\<close>
    by simp
  finally have \<open>norm (Proj (-T) \<psi>) = 0\<close>
    by auto
  with \<psi>_decomp have \<open>\<psi> = Proj T \<psi>\<close>
    by auto
  then show \<open>\<psi> \<in> space_as_set T\<close>
    by (metis Proj_range cblinfun_apply_in_image)
qed

lemma norm_Proj_apply_1: \<open>norm \<psi> = 1 \<Longrightarrow> norm (Proj T *\<^sub>V \<psi>) = 1 \<longleftrightarrow> \<psi> \<in> space_as_set T\<close>
  using norm_Proj_apply by metis

lemma norm_is_Proj_nonzero: \<open>norm P = 1\<close> if \<open>is_Proj P\<close> and \<open>P \<noteq> 0\<close> for P :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
proof (rule antisym)
  show \<open>norm P \<le> 1\<close>
    by (simp add: norm_is_Proj that(1))
  from \<open>P \<noteq> 0\<close>
  have \<open>range P \<noteq> 0\<close>
    by (metis cblinfun_eq_0_on_UNIV_span complex_vector.span_UNIV rangeI set_zero singletonD)
  then obtain \<psi> where \<open>\<psi> \<in> range P\<close> and \<open>\<psi> \<noteq> 0\<close>
    by force
  then have \<open>P \<psi> = \<psi>\<close>
    using is_Proj.rep_eq is_projection_on_fixes_image is_projection_on_image that(1) by blast
  then show \<open>norm P \<ge> 1\<close>
    apply (rule_tac cblinfun_norm_geqI[of _ _ \<psi>])
    using \<open>\<psi> \<noteq> 0\<close> by simp
qed


lemma Proj_compose_cancelI:
  assumes \<open>A *\<^sub>S \<top> \<le> S\<close>
  shows \<open>Proj S o\<^sub>C\<^sub>L A = A\<close>
  apply (rule cblinfun_eqI)
proof -
  fix x
  have \<open>(Proj S o\<^sub>C\<^sub>L A) *\<^sub>V x = Proj S *\<^sub>V (A *\<^sub>V x)\<close>
  by simp
  also have \<open>\<dots> = A *\<^sub>V x\<close>
    apply (rule Proj_fixes_image)
    using assms cblinfun_apply_in_image less_eq_ccsubspace.rep_eq by blast
  finally show \<open>(Proj S o\<^sub>C\<^sub>L A) *\<^sub>V x = A *\<^sub>V x\<close>
    by -
qed

lemma space_as_setI_via_Proj:
  assumes \<open>Proj M *\<^sub>V x = x\<close>
  shows \<open>x \<in> space_as_set M\<close>
  using assms norm_Proj_apply by fastforce

lemma unitary_image_ortho_compl: 
  \<comment> \<open>Logically, this lemma belongs in an earlier section but its proof uses projectors.\<close>
  fixes U :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes [simp]: \<open>unitary U\<close>
  shows \<open>U *\<^sub>S (- A) = - (U *\<^sub>S A)\<close>
proof -
  have \<open>Proj (U *\<^sub>S (- A)) = sandwich U (Proj (- A))\<close>
    by (simp add: Proj_sandwich)
  also have \<open>\<dots> = sandwich U (id_cblinfun - Proj A)\<close>
    by (simp add: Proj_ortho_compl)
  also have \<open>\<dots> = id_cblinfun - sandwich U (Proj A)\<close>
    by (metis assms cblinfun.diff_right sandwich_isometry_id unitary_twosided_isometry)
  also have \<open>\<dots> = id_cblinfun - Proj (U *\<^sub>S A)\<close>
    by (simp add: Proj_sandwich)
  also have \<open>\<dots> = Proj (- (U *\<^sub>S A))\<close>
    by (simp add: Proj_ortho_compl)
  finally show ?thesis
    by (simp add: Proj_inj)
qed


lemma Proj_on_image [simp]: \<open>Proj S *\<^sub>S S = S\<close>
  by (metis Proj_idempotent Proj_range cblinfun_compose_image)

subsection \<open>Kernel / eigenspaces\<close>

lift_definition kernel :: "'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector
   \<Rightarrow> 'a ccsubspace"
  is "\<lambda>f. f -` {0}"
  by (metis kernel_is_closed_csubspace)

definition eigenspace :: "complex \<Rightarrow> 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L'a \<Rightarrow> 'a ccsubspace" where
  "eigenspace a A = kernel (A - a *\<^sub>C id_cblinfun)"

lemma kernel_scaleC[simp]: "a\<noteq>0 \<Longrightarrow> kernel (a *\<^sub>C A) = kernel A"
  for a :: complex and A :: "(_,_) cblinfun"
  apply transfer
  using complex_vector.scale_eq_0_iff by blast

lemma kernel_0[simp]: "kernel 0 = top"
  by transfer auto

lemma kernel_id[simp]: "kernel id_cblinfun = 0"
  by transfer simp

lemma eigenspace_scaleC[simp]:
  assumes a1: "a \<noteq> 0"
  shows "eigenspace b (a *\<^sub>C A) = eigenspace (b/a) A"
proof -
  have "b *\<^sub>C (id_cblinfun::('a, _) cblinfun) = a *\<^sub>C (b / a) *\<^sub>C id_cblinfun"
    using a1
    by (metis ceq_vector_fraction_iff)
  hence "kernel (a *\<^sub>C A - b *\<^sub>C id_cblinfun) = kernel (A - (b / a) *\<^sub>C id_cblinfun)"
    using a1 by (metis (no_types) complex_vector.scale_right_diff_distrib kernel_scaleC)
  thus ?thesis
    unfolding eigenspace_def
    by blast
qed

lemma eigenspace_memberD:
  assumes "x \<in> space_as_set (eigenspace e A)"
  shows "A *\<^sub>V x = e *\<^sub>C x"
  using assms unfolding eigenspace_def by transfer auto

lemma kernel_memberD:
  assumes "x \<in> space_as_set (kernel A)"
  shows "A *\<^sub>V x = 0"
  using assms by transfer auto

lemma eigenspace_memberI:
  assumes "A *\<^sub>V x = e *\<^sub>C x"
  shows "x \<in> space_as_set (eigenspace e A)"
  using assms unfolding eigenspace_def by transfer auto

lemma kernel_memberI:
  assumes "A *\<^sub>V x = 0"
  shows "x \<in> space_as_set (kernel A)"
  using assms by transfer auto

lemma kernel_Proj[simp]: \<open>kernel (Proj S) = - S\<close>
  apply transfer
  apply auto
  apply (metis diff_0_right is_projection_on_iff_orthog projection_is_projection_on')
  by (simp add: complex_vector.subspace_0 projection_eqI)

lemma orthogonal_projectors_orthogonal_spaces:
  \<comment> \<open>Logically belongs in section "Projectors".\<close>
  fixes S T :: \<open>'a::chilbert_space ccsubspace\<close>
  shows \<open>orthogonal_spaces S T \<longleftrightarrow> Proj S o\<^sub>C\<^sub>L Proj T = 0\<close>
proof (intro ballI iffI)
  assume \<open>Proj S o\<^sub>C\<^sub>L Proj T = 0\<close> 
  then have \<open>is_orthogonal x y\<close> if \<open>x \<in> space_as_set S\<close> \<open>y \<in> space_as_set T\<close> for x y
    by (metis (no_types, opaque_lifting) Proj_fixes_image adj_Proj cblinfun.zero_left cblinfun_apply_cblinfun_compose cinner_adj_right cinner_zero_right that(1) that(2))
  then show \<open>orthogonal_spaces S T\<close>
    by (simp add: orthogonal_spaces_def)
next 
  assume \<open>orthogonal_spaces S T\<close>
  then have \<open>S \<le> - T\<close>
    by (simp add: orthogonal_spaces_leq_compl)
  then show \<open>Proj S o\<^sub>C\<^sub>L Proj T = 0\<close>
    by (metis (no_types, opaque_lifting) Proj_range adj_Proj adj_cblinfun_compose basic_trans_rules(31) cblinfun.zero_left cblinfun_apply_cblinfun_compose cblinfun_apply_in_image cblinfun_eqI kernel_Proj kernel_memberD less_eq_ccsubspace.rep_eq)
qed


lemma cblinfun_compose_Proj_kernel[simp]: \<open>a o\<^sub>C\<^sub>L Proj (kernel a) = 0\<close>
  apply (rule cblinfun_eqI)
  by simp (metis Proj_range cblinfun_apply_in_image kernel_memberD)

lemma kernel_compl_adj_range:
  shows \<open>kernel a = - (a* *\<^sub>S top)\<close>
proof (rule ccsubspace_eqI)
  fix x
  have \<open>x \<in> space_as_set (kernel a) \<longleftrightarrow> a x = 0\<close>
    by transfer simp
  also have \<open>a x = 0 \<longleftrightarrow> (\<forall>y. is_orthogonal y (a x))\<close>
    by (metis cinner_gt_zero_iff cinner_zero_right)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>y. is_orthogonal (a* *\<^sub>V y) x)\<close>
    by (simp add: cinner_adj_left)
  also have \<open>\<dots> \<longleftrightarrow> x \<in> space_as_set (- (a* *\<^sub>S top))\<close>
    by transfer (metis (mono_tags, opaque_lifting) UNIV_I image_iff is_orthogonal_sym orthogonal_complementI orthogonal_complement_of_closure orthogonal_complement_orthoI')
  finally show \<open>x \<in> space_as_set (kernel a) \<longleftrightarrow> x \<in> space_as_set (- (a* *\<^sub>S top))\<close>
    by -
qed

lemma kernel_apply_self: \<open>A *\<^sub>S kernel A = 0\<close>
proof transfer
  fix A :: \<open>'b \<Rightarrow> 'a\<close>
  assume \<open>bounded_clinear A\<close>
  then have \<open>A 0 = 0\<close>
    by (simp add: bounded_clinear_def complex_vector.linear_0)
  then have \<open>A ` A -` {0} = {0}\<close>
    by fastforce
  then show \<open>closure (A ` A -` {0}) = {0}\<close>
    by auto
qed

lemma leq_kernel_iff: 
  shows \<open>A \<le> kernel B \<longleftrightarrow> B *\<^sub>S A = 0\<close>
proof (rule iffI)
  assume \<open>A \<le> kernel B\<close>
  then have \<open>B *\<^sub>S A \<le> B *\<^sub>S kernel B\<close>
    by (simp add: cblinfun_image_mono)
  also have \<open>\<dots> = 0\<close>
    by (simp add: kernel_apply_self)
  finally show \<open>B *\<^sub>S A = 0\<close>
    by (simp add: bot.extremum_unique)
next
  assume \<open>B *\<^sub>S A = 0\<close>
  then show \<open>A \<le> kernel B\<close>
    apply transfer
    by (metis closure_subset image_subset_iff_subset_vimage)
qed

lemma cblinfun_image_kernel:
  assumes \<open>C *\<^sub>S A *\<^sub>S kernel B \<le> kernel B\<close>
  assumes \<open>A o\<^sub>C\<^sub>L C = id_cblinfun\<close>
  shows \<open>A *\<^sub>S kernel B = kernel (B o\<^sub>C\<^sub>L C)\<close>
proof (rule antisym)
  show \<open>A *\<^sub>S kernel B \<le> kernel (B o\<^sub>C\<^sub>L C)\<close>
    using assms(1) by (simp add: leq_kernel_iff cblinfun_compose_image)
  show \<open>kernel (B o\<^sub>C\<^sub>L C) \<le> A *\<^sub>S kernel B\<close>
  proof (insert assms(2), transfer, intro subsetI)
    fix A :: \<open>'a \<Rightarrow> 'b\<close> and B :: \<open>'a \<Rightarrow> 'c\<close> and C :: \<open>'b \<Rightarrow> 'a\<close> and x
    assume \<open>x \<in> (B \<circ> C) -` {0}\<close>
    then have BCx: \<open>B (C x) = 0\<close>
      by simp
    assume \<open>A \<circ> C = (\<lambda>x. x)\<close>
    then have \<open>x = A (C x)\<close>
      apply (simp add: o_def)
      by metis
    then show \<open>x \<in> closure (A ` B -` {0})\<close>
      using \<open>B (C x) = 0\<close> closure_subset by fastforce
  qed
qed

lemma cblinfun_image_kernel_unitary:
  assumes \<open>unitary U\<close>
  shows \<open>U *\<^sub>S kernel B = kernel (B o\<^sub>C\<^sub>L U*)\<close>
  apply (rule cblinfun_image_kernel)
  using assms by (auto simp flip: cblinfun_compose_image)

lemma kernel_cblinfun_compose:
  assumes \<open>kernel B = 0\<close>
  shows \<open>kernel A = kernel (B o\<^sub>C\<^sub>L A)\<close>
  using assms apply transfer by auto


lemma eigenspace_0[simp]: \<open>eigenspace 0 A = kernel A\<close>
  by (simp add: eigenspace_def)

lemma kernel_isometry: \<open>kernel U = 0\<close> if \<open>isometry U\<close>
  by (simp add: kernel_compl_adj_range range_adjoint_isometry that)

lemma cblinfun_image_eigenspace_isometry:
  assumes [simp]: \<open>isometry A\<close> and \<open>c \<noteq> 0\<close>
  shows \<open>A *\<^sub>S eigenspace c B = eigenspace c (sandwich A B)\<close>
proof (rule antisym)
  show \<open>A *\<^sub>S eigenspace c B \<le> eigenspace c (sandwich A B)\<close>
  proof (unfold cblinfun_image_def2, rule ccspan_leqI, rule subsetI)
    fix x assume \<open>x \<in> (*\<^sub>V) A ` space_as_set (eigenspace c B)\<close>
    then obtain y where x_def: \<open>x = A y\<close> and \<open>y \<in> space_as_set (eigenspace c B)\<close>
      by auto
    then have \<open>B y = c *\<^sub>C y\<close>
      by (simp add: eigenspace_memberD)
    then have \<open>sandwich A B x = c *\<^sub>C x\<close>
      apply (simp add: sandwich_apply x_def cblinfun_compose_assoc 
          flip: cblinfun_apply_cblinfun_compose)
      by (simp add: cblinfun.scaleC_right)
    then show \<open>x \<in> space_as_set (eigenspace c (sandwich A B))\<close>
      by (simp add: eigenspace_memberI)
  qed
  show \<open>eigenspace c (sandwich A *\<^sub>V B) \<le> A *\<^sub>S eigenspace c B\<close>
  proof (rule ccsubspace_leI_unit)
    fix x
    assume \<open>x \<in> space_as_set (eigenspace c (sandwich A B))\<close>
    then have *: \<open>sandwich A B x = c *\<^sub>C x\<close>
      by (simp add: eigenspace_memberD)
    then have \<open>c *\<^sub>C x \<in> range A\<close>
      apply (simp add: sandwich_apply)
      by (metis rangeI)
    then have \<open>(inverse c * c) *\<^sub>C x \<in> range A\<close>
      apply (simp flip: scaleC_scaleC)
      by (metis (no_types, lifting) cblinfun.scaleC_right rangeE rangeI)
    with \<open>c \<noteq> 0\<close> have \<open>x \<in> range A\<close>
      by simp
    then obtain y where x_def: \<open>x = A y\<close>
      by auto
    have \<open>B *\<^sub>V y = A* *\<^sub>V sandwich A B x\<close>
      apply (simp add: sandwich_apply x_def)
      by (metis assms cblinfun_apply_cblinfun_compose id_cblinfun.rep_eq isometryD)
    also have \<open>\<dots> = c *\<^sub>C y\<close>
      apply (simp add: * cblinfun.scaleC_right)
      apply (simp add: x_def)
      by (metis assms(1) cblinfun_apply_cblinfun_compose id_cblinfun_apply isometry_def)
    finally have \<open>y \<in> space_as_set (eigenspace c B)\<close>
      by (simp add: eigenspace_memberI)
    then show \<open>x \<in> space_as_set (A *\<^sub>S eigenspace c B) \<close>
      by (simp add: x_def cblinfun_apply_in_image')
  qed
qed

lemma cblinfun_image_eigenspace_unitary:
  assumes [simp]: \<open>unitary A\<close>
  shows \<open>A *\<^sub>S eigenspace c B = eigenspace c (sandwich A B)\<close>
  apply (cases \<open>c = 0\<close>)
   apply (simp add: sandwich_apply cblinfun_image_kernel_unitary kernel_isometry cblinfun_compose_assoc
    flip: kernel_cblinfun_compose)
  by (simp add: cblinfun_image_eigenspace_isometry)

lemma kernel_member_iff: \<open>x \<in> space_as_set (kernel A) \<longleftrightarrow> A *\<^sub>V x = 0\<close>
  using kernel_memberD kernel_memberI by blast

lemma kernel_square[simp]: \<open>kernel (A* o\<^sub>C\<^sub>L A) = kernel A\<close>
proof (intro ccsubspace_eqI iffI)
  fix x
  assume \<open>x \<in> space_as_set (kernel A)\<close>
  then show \<open>x \<in> space_as_set (kernel (A* o\<^sub>C\<^sub>L A))\<close>
    by (simp add: kernel.rep_eq)
next
  fix x
  assume \<open>x \<in> space_as_set (kernel (A* o\<^sub>C\<^sub>L A))\<close>
  then have \<open>A* *\<^sub>V A *\<^sub>V x = 0\<close>
    by (simp add: kernel.rep_eq)
  then have \<open>(A *\<^sub>V x) \<bullet>\<^sub>C (A *\<^sub>V x) = 0\<close>
    by (metis cinner_adj_right cinner_zero_right)
  then have \<open>A *\<^sub>V x = 0\<close>
    by auto
  then show \<open>x \<in> space_as_set (kernel A)\<close>
    by (simp add: kernel.rep_eq)
qed

subsection \<open>Partial isometries\<close>

definition partial_isometry where
  \<open>partial_isometry A \<longleftrightarrow> (\<forall>h \<in> space_as_set (- kernel A). norm (A h) = norm h)\<close>

lemma partial_isometryI: 
  assumes \<open>\<And>h. h \<in> space_as_set (- kernel A) \<Longrightarrow> norm (A h) = norm h\<close>
  shows \<open>partial_isometry A\<close>
  using assms partial_isometry_def by blast

lemma
  fixes A :: \<open>'a :: chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b :: complex_normed_vector\<close>
  assumes iso: \<open>\<And>\<psi>. \<psi> \<in> space_as_set V \<Longrightarrow> norm (A *\<^sub>V \<psi>) = norm \<psi>\<close>
  assumes zero: \<open>\<And>\<psi>. \<psi> \<in> space_as_set (- V) \<Longrightarrow> A *\<^sub>V \<psi> = 0\<close>
  shows partial_isometryI': \<open>partial_isometry A\<close>
    and partial_isometry_initial: \<open>kernel A = - V\<close>
proof -
  from zero
  have \<open>- V \<le> kernel A\<close>
    by (simp add: kernel_memberI less_eq_ccsubspace.rep_eq subsetI)
  moreover have \<open>kernel A \<le> -V\<close>
    by (smt (verit, ccfv_threshold) Proj_ortho_compl Proj_range assms(1) cblinfun.diff_left cblinfun.diff_right cblinfun_apply_in_image cblinfun_id_cblinfun_apply ccsubspace_leI kernel_Proj kernel_memberD kernel_memberI norm_eq_zero ortho_involution subsetI zero)
  ultimately show kerA: \<open>kernel A = -V\<close>
    by simp

  show \<open>partial_isometry A\<close>
    apply (rule partial_isometryI)
    by (simp add: kerA iso)
qed

lemma Proj_partial_isometry[simp]: \<open>partial_isometry (Proj S)\<close>
  apply (rule partial_isometryI)
  by (simp add: Proj_fixes_image)

lemma is_Proj_partial_isometry: \<open>is_Proj P \<Longrightarrow> partial_isometry P\<close> for P :: \<open>_ :: chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _\<close>
  by (metis Proj_on_own_range Proj_partial_isometry)

lemma isometry_partial_isometry: \<open>isometry P \<Longrightarrow> partial_isometry P\<close>
  by (simp add: isometry_preserves_norm partial_isometry_def)

lemma unitary_partial_isometry: \<open>unitary P \<Longrightarrow> partial_isometry P\<close>
  using isometry_partial_isometry unitary_isometry by blast

lemma norm_partial_isometry:
  fixes A :: \<open>'a :: chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>partial_isometry A\<close> and \<open>A \<noteq> 0\<close>
  shows \<open>norm A = 1\<close> 
proof -
  from \<open>A \<noteq> 0\<close>
  have \<open>- (kernel A) \<noteq> 0\<close>
    by (metis cblinfun_eqI diff_zero id_cblinfun_apply kernel_id kernel_memberD ortho_involution orthog_proj_exists orthogonal_complement_closed_subspace uminus_ccsubspace.rep_eq zero_cblinfun.rep_eq)
  then obtain h where \<open>h \<in> space_as_set (- kernel A)\<close> and \<open>h \<noteq> 0\<close>
    by (metis cblinfun_id_cblinfun_apply ccsubspace_eqI closed_csubspace.subspace complex_vector.subspace_0 kernel_id kernel_memberD kernel_memberI orthogonal_complement_closed_subspace uminus_ccsubspace.rep_eq)
  with \<open>partial_isometry A\<close>
  have \<open>norm (A h) = norm h\<close>
    using partial_isometry_def by blast
  then have \<open>norm A \<ge> 1\<close>
    by (smt (verit) \<open>h \<noteq> 0\<close> mult_cancel_right1 mult_left_le_one_le norm_cblinfun norm_eq_zero norm_ge_zero)

  have \<open>norm A \<le> 1\<close>
  proof (rule norm_cblinfun_bound)
    show \<open>0 \<le> (1::real)\<close>
      by simp
    fix \<psi> :: 'a
    define g h where \<open>g = Proj (kernel A) \<psi>\<close> and \<open>h = Proj (- kernel A) \<psi>\<close>
    have \<open>A g = 0\<close>
      by (metis Proj_range cblinfun_apply_in_image g_def kernel_memberD)
    moreover from \<open>partial_isometry A\<close>
    have \<open>norm (A h) = norm h\<close>
      by (metis Proj_range cblinfun_apply_in_image h_def partial_isometry_def)
    ultimately have \<open>norm (A \<psi>) = norm h\<close>
      by (simp add: Proj_ortho_compl cblinfun.diff_left cblinfun.diff_right g_def h_def)
    also have \<open>norm h \<le> norm \<psi>\<close>
      by (smt (verit, del_insts) h_def mult_left_le_one_le norm_Proj_leq1 norm_cblinfun norm_ge_zero)
    finally show \<open>norm (A *\<^sub>V \<psi>) \<le> 1 * norm \<psi>\<close>
      by simp
  qed

  from \<open>norm A \<le> 1\<close> and \<open>norm A \<ge> 1\<close>
  show \<open>norm A = 1\<close>
    by auto
qed

lemma partial_isometry_adj_a_o_a:
  assumes \<open>partial_isometry a\<close>
  shows \<open>a* o\<^sub>C\<^sub>L a = Proj (- kernel a)\<close>
proof (rule cblinfun_cinner_eqI)
  define P where \<open>P = Proj (- kernel a)\<close>
  have aP: \<open>a o\<^sub>C\<^sub>L P = a\<close>
    by (auto intro!: simp: cblinfun_compose_minus_right P_def Proj_ortho_compl)
  have is_Proj_P[simp]: \<open>is_Proj P\<close>
    by (simp add: P_def)

  fix \<psi> :: 'a
  have \<open>\<psi> \<bullet>\<^sub>C ((a* o\<^sub>C\<^sub>L a) *\<^sub>V \<psi>) = a \<psi> \<bullet>\<^sub>C a \<psi>\<close>
    by (simp add: cinner_adj_right)
  also have \<open>\<dots> = a (P \<psi>) \<bullet>\<^sub>C a (P \<psi>)\<close>
    by (metis aP cblinfun_apply_cblinfun_compose)
  also have \<open>\<dots> = P \<psi> \<bullet>\<^sub>C P \<psi>\<close>
    by (metis P_def Proj_range assms cblinfun_apply_in_image cdot_square_norm partial_isometry_def)
  also have \<open>\<dots> = \<psi> \<bullet>\<^sub>C P \<psi>\<close>
    by (simp flip: cinner_adj_right add: is_proj_selfadj is_Proj_idempotent[THEN simp_a_oCL_b'])
  finally show \<open>\<psi> \<bullet>\<^sub>C ((a* o\<^sub>C\<^sub>L a) *\<^sub>V \<psi>) = \<psi> \<bullet>\<^sub>C P \<psi>\<close>
    by -
qed

lemma partial_isometry_square_proj: \<open>is_Proj (a* o\<^sub>C\<^sub>L a)\<close> if \<open>partial_isometry a\<close>
  by (simp add: partial_isometry_adj_a_o_a that)

lemma partial_isometry_adj[simp]: \<open>partial_isometry (a*)\<close> if \<open>partial_isometry a\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
proof -
  have ran_ker: \<open>a *\<^sub>S top = - kernel (a*)\<close>
    by (simp add: kernel_compl_adj_range)

  have \<open>norm (a* *\<^sub>V h) = norm h\<close> if \<open>h \<in> range a\<close> for h
  proof -
    from that obtain x where h: \<open>h = a x\<close>
      by auto
    have \<open>norm (a* *\<^sub>V h) = norm (a* *\<^sub>V a *\<^sub>V x)\<close>
      by (simp add: h)
    also have \<open>\<dots> = norm (Proj (- kernel a) *\<^sub>V x)\<close>
      by (simp add: \<open>partial_isometry a\<close> partial_isometry_adj_a_o_a simp_a_oCL_b')
    also have \<open>\<dots> = norm (a *\<^sub>V Proj (- kernel a) *\<^sub>V x)\<close>
      by (metis Proj_range \<open>partial_isometry a\<close> cblinfun_apply_in_image partial_isometry_def)
    also have \<open>\<dots> = norm (a *\<^sub>V x)\<close>
      by (smt (verit, best) Proj_idempotent \<open>partial_isometry a\<close> adj_Proj cblinfun_apply_cblinfun_compose cinner_adj_right cnorm_eq partial_isometry_adj_a_o_a)
    also have \<open>\<dots> = norm h\<close>
      using h by auto
    finally show ?thesis
      by -
  qed

  then have norm_pres: \<open>norm (a* *\<^sub>V h) = norm h\<close> if \<open>h \<in> closure (range a)\<close> for h
    using that apply (rule on_closure_eqI)
      by assumption (intro continuous_intros)+

  show ?thesis
    apply (rule partial_isometryI)
    by (auto simp: cblinfun_image.rep_eq norm_pres simp flip: ran_ker)
qed

subsection \<open>Isomorphisms and inverses\<close>

definition iso_cblinfun :: \<open>('a::complex_normed_vector, 'b::complex_normed_vector) cblinfun \<Rightarrow> bool\<close> where
  \<open>iso_cblinfun A = (\<exists> B. A o\<^sub>C\<^sub>L B = id_cblinfun \<and> B o\<^sub>C\<^sub>L A = id_cblinfun)\<close>

definition \<open>invertible_cblinfun A \<longleftrightarrow> (\<exists>B. B o\<^sub>C\<^sub>L A = id_cblinfun)\<close>

definition cblinfun_inv :: \<open>('a::complex_normed_vector, 'b::complex_normed_vector) cblinfun \<Rightarrow> ('b,'a) cblinfun\<close> where
  \<open>cblinfun_inv A = (if invertible_cblinfun A then SOME B. B o\<^sub>C\<^sub>L A = id_cblinfun else 0)\<close>

lemma cblinfun_inv_left:
  assumes \<open>invertible_cblinfun A\<close>
  shows \<open>cblinfun_inv A o\<^sub>C\<^sub>L A = id_cblinfun\<close>
  apply (simp add: assms cblinfun_inv_def)
  apply (rule someI_ex)
  using assms by (simp add: invertible_cblinfun_def)

lemma inv_cblinfun_invertible:  \<open>iso_cblinfun A \<Longrightarrow> invertible_cblinfun A\<close>
  by (auto simp: iso_cblinfun_def invertible_cblinfun_def)

lemma cblinfun_inv_right:
  assumes \<open>iso_cblinfun A\<close>
  shows \<open>A o\<^sub>C\<^sub>L cblinfun_inv A = id_cblinfun\<close>
proof -
  from assms
  obtain B where AB: \<open>A o\<^sub>C\<^sub>L B = id_cblinfun\<close> and BA: \<open>B o\<^sub>C\<^sub>L A = id_cblinfun\<close>
    using iso_cblinfun_def by blast
  from BA have \<open>cblinfun_inv A o\<^sub>C\<^sub>L A = id_cblinfun\<close>
    by (simp add: assms cblinfun_inv_left inv_cblinfun_invertible)
  with AB BA have \<open>cblinfun_inv A = B\<close>
    by (metis cblinfun_assoc_left(1) cblinfun_compose_id_right)
  with AB show \<open>A o\<^sub>C\<^sub>L cblinfun_inv A = id_cblinfun\<close>
    by auto
qed

lemma cblinfun_inv_uniq:
  assumes "A o\<^sub>C\<^sub>L B = id_cblinfun" and "B o\<^sub>C\<^sub>L A = id_cblinfun"
  shows "cblinfun_inv A = B"
  using assms by (metis inv_cblinfun_invertible cblinfun_compose_assoc cblinfun_compose_id_right cblinfun_inv_left iso_cblinfun_def)

lemma iso_cblinfun_unitary: \<open>unitary A \<Longrightarrow> iso_cblinfun A\<close>
  using iso_cblinfun_def unitary_def by blast

lemma invertible_cblinfun_isometry: \<open>isometry A \<Longrightarrow> invertible_cblinfun A\<close>
  using invertible_cblinfun_def isometryD by blast

lemma summable_cblinfun_apply_invertible:
  assumes \<open>invertible_cblinfun A\<close>
  shows \<open>(\<lambda>x. A *\<^sub>V g x) summable_on S \<longleftrightarrow> g summable_on S\<close>
proof (rule iffI)
  assume \<open>g summable_on S\<close>
  then show \<open>(\<lambda>x. A *\<^sub>V g x) summable_on S\<close>
    by (rule summable_on_cblinfun_apply)
next
  assume \<open>(\<lambda>x. A *\<^sub>V g x) summable_on S\<close>
  then have \<open>(\<lambda>x. cblinfun_inv A *\<^sub>V A *\<^sub>V g x) summable_on S\<close>
    by (rule summable_on_cblinfun_apply)
  then show \<open>g summable_on S\<close>
    by (simp add: cblinfun_inv_left assms flip: cblinfun_apply_cblinfun_compose)
qed

lemma infsum_cblinfun_apply_invertible:
  assumes \<open>invertible_cblinfun A\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>S. A *\<^sub>V g x) = A *\<^sub>V (\<Sum>\<^sub>\<infinity>x\<in>S. g x)\<close>
proof (cases \<open>g summable_on S\<close>)
  case True
  then show ?thesis
    by (rule infsum_cblinfun_apply)
next
  case False
  then have \<open>\<not> (\<lambda>x. A *\<^sub>V g x) summable_on S\<close>
  using assms by (simp add: summable_cblinfun_apply_invertible)
  with False show ?thesis 
    by (simp add: infsum_not_exists)
qed

subsection \<open>One-dimensional spaces\<close>


instantiation cblinfun :: (one_dim, one_dim) complex_inner begin
text \<open>Once we have a theory for the trace, we could instead define the Hilbert-Schmidt inner product
  and relax the \<^class>\<open>one_dim\<close>-sort constraint to (\<^class>\<open>cfinite_dim\<close>,\<^class>\<open>complex_normed_vector\<close>) or similar\<close>
definition "cinner_cblinfun (A::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) (B::'a \<Rightarrow>\<^sub>C\<^sub>L 'b)
             = cnj (one_dim_iso (A *\<^sub>V 1)) * one_dim_iso (B *\<^sub>V 1)"
instance
proof intro_classes
  fix A B C :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
    and c c' :: complex
  show "(A \<bullet>\<^sub>C B) = cnj (B \<bullet>\<^sub>C A)"
    unfolding cinner_cblinfun_def by auto
  show "(A + B) \<bullet>\<^sub>C C = (A \<bullet>\<^sub>C C) + (B \<bullet>\<^sub>C C)"
    by (simp add: cinner_cblinfun_def algebra_simps plus_cblinfun.rep_eq)
  show "(c *\<^sub>C A \<bullet>\<^sub>C B) = cnj c * (A \<bullet>\<^sub>C B)"
    by (simp add: cblinfun.scaleC_left cinner_cblinfun_def)
  show "0 \<le> (A \<bullet>\<^sub>C A)"
    unfolding cinner_cblinfun_def by auto
  have "bounded_clinear A \<Longrightarrow> A 1 = 0 \<Longrightarrow> A = (\<lambda>_. 0)"
    for A::"'a \<Rightarrow> 'b"
  proof (rule one_dim_clinear_eqI [where x = 1] , auto)
    show "clinear A"
      if "bounded_clinear A"
        and "A 1 = 0"
      for A :: "'a \<Rightarrow> 'b"
      using that
      by (simp add: bounded_clinear.clinear)
    show "clinear ((\<lambda>_. 0)::'a \<Rightarrow> 'b)"
      if "bounded_clinear A"
        and "A 1 = 0"
      for A :: "'a \<Rightarrow> 'b"
      using that
      by (simp add: complex_vector.module_hom_zero)
  qed
  hence "A *\<^sub>V 1 = 0 \<Longrightarrow> A = 0"
    by transfer
  hence "one_dim_iso (A *\<^sub>V 1) = 0 \<Longrightarrow> A = 0"
    by (metis one_dim_iso_of_zero one_dim_iso_inj)
  thus "((A \<bullet>\<^sub>C A) = 0) = (A = 0)"
    by (auto simp: cinner_cblinfun_def)

  show "norm A = sqrt (cmod (A \<bullet>\<^sub>C A))"
    unfolding cinner_cblinfun_def
    by transfer (simp add: norm_mult abs_complex_def one_dim_onorm' cnj_x_x power2_eq_square bounded_clinear.clinear)
qed
end

instantiation cblinfun :: (one_dim, one_dim) one_dim begin
lift_definition one_cblinfun :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b" is "one_dim_iso"
  by (rule bounded_clinear_one_dim_iso)
lift_definition times_cblinfun :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
  is "\<lambda>f g. f o one_dim_iso o g"
  by (simp add: comp_bounded_clinear)
lift_definition inverse_cblinfun :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b" is
  "\<lambda>f. ((*) (one_dim_iso (inverse (f 1)))) o one_dim_iso"
  by (auto intro!: comp_bounded_clinear bounded_clinear_mult_right)
definition divide_cblinfun :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b" where
  "divide_cblinfun A B = A * inverse B"
definition "canonical_basis_cblinfun = [1 :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b]"
definition \<open>canonical_basis_length_cblinfun (_ :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) itself) = (1::nat)\<close>
instance
proof intro_classes
  let ?basis = "canonical_basis :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) list"
  fix A B C :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
    and c c' :: complex
  show "distinct ?basis"
    unfolding canonical_basis_cblinfun_def by simp
  have "(1::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<noteq> (0::'a \<Rightarrow>\<^sub>C\<^sub>L 'b)"
    by (metis cblinfun.zero_left one_cblinfun.rep_eq one_dim_iso_of_one zero_neq_one)
  thus "cindependent (set ?basis)"
    unfolding canonical_basis_cblinfun_def by simp

  have "A \<in> cspan (set ?basis)" for A
  proof -
    define c :: complex where "c = one_dim_iso (A *\<^sub>V 1)"
    have "A x = one_dim_iso (A 1) *\<^sub>C one_dim_iso x" for x
      by (smt (z3) cblinfun.scaleC_right complex_vector.scale_left_commute one_dim_iso_idem one_dim_scaleC_1)
    hence "A = one_dim_iso (A *\<^sub>V 1) *\<^sub>C 1"
      by transfer metis
    thus "A \<in> cspan (set ?basis)"
      unfolding canonical_basis_cblinfun_def
      by (smt complex_vector.span_base complex_vector.span_scale list.set_intros(1))
  qed
  thus "cspan (set ?basis) = UNIV" by auto

  have "A = (1::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<Longrightarrow>
    norm (1::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) = (1::real)"
    by transfer simp
  thus "A \<in> set ?basis \<Longrightarrow> norm A = 1"
    unfolding canonical_basis_cblinfun_def
    by simp

  show "?basis = [1]"
    unfolding canonical_basis_cblinfun_def by simp
  show "c *\<^sub>C 1 * c' *\<^sub>C 1 = (c * c') *\<^sub>C (1::'a\<Rightarrow>\<^sub>C\<^sub>L'b)"
    by transfer auto
  have "(1::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) = (0::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<Longrightarrow> False"
    by (metis cblinfun.zero_left one_cblinfun.rep_eq one_dim_iso_of_zero' zero_neq_neg_one)
  thus "is_ortho_set (set ?basis)"
    unfolding is_ortho_set_def canonical_basis_cblinfun_def by auto
  show "A div B = A * inverse B"
    by (simp add: divide_cblinfun_def)
  show "inverse (c *\<^sub>C 1) = (1::'a\<Rightarrow>\<^sub>C\<^sub>L'b) /\<^sub>C c"
    by transfer (simp add: o_def one_dim_inverse)
  show \<open>canonical_basis_length TYPE('a \<Rightarrow>\<^sub>C\<^sub>L 'b) = length (canonical_basis :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) list)\<close>
    by (simp add: canonical_basis_length_cblinfun_def canonical_basis_cblinfun_def)
qed
end

lemma id_cblinfun_eq_1[simp]: \<open>id_cblinfun = 1\<close>
  by transfer auto

lemma one_dim_apply_is_times[simp]:
  fixes A :: "'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L 'a" and B :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'a"
  shows "A o\<^sub>C\<^sub>L B = A * B"
  by transfer simp

lemma one_comp_one_cblinfun[simp]: "1 o\<^sub>C\<^sub>L 1 = 1"
  apply transfer unfolding o_def by simp

lemma one_cblinfun_adj[simp]: "1* = 1"
  by transfer simp

lemma scaleC_1_apply[simp]: \<open>(x *\<^sub>C 1) *\<^sub>V y = x *\<^sub>C y\<close>
  by (metis cblinfun.scaleC_left cblinfun_id_cblinfun_apply id_cblinfun_eq_1)

lemma cblinfun_apply_1_left[simp]: \<open>1 *\<^sub>V y = y\<close>
  by (metis cblinfun_id_cblinfun_apply id_cblinfun_eq_1)

lemma of_complex_cblinfun_apply[simp]: \<open>of_complex x *\<^sub>V y = one_dim_iso (x *\<^sub>C y)\<close>
  by (metis of_complex_def cblinfun.scaleC_right one_cblinfun.rep_eq scaleC_cblinfun.rep_eq)

lemma cblinfun_compose_1_left[simp]: \<open>1 o\<^sub>C\<^sub>L x = x\<close>
  by transfer auto

lemma cblinfun_compose_1_right[simp]: \<open>x o\<^sub>C\<^sub>L 1 = x\<close>
  by transfer auto

lemma one_dim_iso_id_cblinfun: \<open>one_dim_iso id_cblinfun = id_cblinfun\<close>
  by simp

lemma one_dim_iso_id_cblinfun_eq_1: \<open>one_dim_iso id_cblinfun = 1\<close>
  by simp

lemma one_dim_iso_comp_distr[simp]: \<open>one_dim_iso (a o\<^sub>C\<^sub>L b) = one_dim_iso a o\<^sub>C\<^sub>L one_dim_iso b\<close>
  by (smt (z3) cblinfun_compose_scaleC_left cblinfun_compose_scaleC_right one_cinner_a_scaleC_one one_comp_one_cblinfun one_dim_iso_of_one one_dim_iso_scaleC)

lemma one_dim_iso_comp_distr_times[simp]: \<open>one_dim_iso (a o\<^sub>C\<^sub>L b) = one_dim_iso a * one_dim_iso b\<close>
  by (smt (verit, del_insts) mult.left_neutral mult_scaleC_left one_cinner_a_scaleC_one one_comp_one_cblinfun one_dim_iso_of_one one_dim_iso_scaleC cblinfun_compose_scaleC_right cblinfun_compose_scaleC_left)

lemma one_dim_iso_adjoint[simp]: \<open>one_dim_iso (A*) = (one_dim_iso A)*\<close>
  by (smt (z3) one_cblinfun_adj one_cinner_a_scaleC_one one_dim_iso_of_one one_dim_iso_scaleC scaleC_adj)

lemma one_dim_iso_adjoint_complex[simp]: \<open>one_dim_iso (A*) = cnj (one_dim_iso A)\<close>
  by (metis (mono_tags, lifting) one_cblinfun_adj one_dim_iso_idem one_dim_scaleC_1 scaleC_adj)

lemma one_dim_cblinfun_compose_commute: \<open>a o\<^sub>C\<^sub>L b = b o\<^sub>C\<^sub>L a\<close> for a b :: \<open>('a::one_dim,'a) cblinfun\<close>
  by (simp add: one_dim_iso_inj)

lemma one_cblinfun_apply_one[simp]: \<open>1 *\<^sub>V 1 = 1\<close>
  by (simp add: one_cblinfun.rep_eq)

lemma is_onb_one_dim[simp]: \<open>norm x = 1 \<Longrightarrow> is_onb {x}\<close> for x :: \<open>_ :: one_dim\<close>
  by (auto simp: is_onb_def intro!: ccspan_one_dim)

lemma one_dim_iso_cblinfun_comp: \<open>one_dim_iso (a o\<^sub>C\<^sub>L b) = of_complex (cinner (a* *\<^sub>V 1) (b *\<^sub>V 1))\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::one_dim\<close> and b :: \<open>'c::one_dim \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  by (simp add: cinner_adj_left cinner_cblinfun_def one_dim_iso_def)

lemma one_dim_iso_cblinfun_apply[simp]: \<open>one_dim_iso \<psi> *\<^sub>V \<phi> = one_dim_iso (one_dim_iso \<psi> *\<^sub>C \<phi>)\<close>
  by (smt (verit) cblinfun.scaleC_left one_cblinfun.rep_eq one_dim_iso_of_one one_dim_iso_scaleC one_dim_scaleC_1)

subsection \<open>Loewner order\<close>

lift_definition heterogenous_cblinfun_id :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  is \<open>if bounded_clinear (heterogenous_identity :: 'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector) then heterogenous_identity else (\<lambda>_. 0)\<close>
  by auto

lemma heterogenous_cblinfun_id_def'[simp]: "heterogenous_cblinfun_id = id_cblinfun"
  by transfer auto

definition "heterogenous_same_type_cblinfun (x::'a::chilbert_space itself) (y::'b::chilbert_space itself) \<longleftrightarrow>
  unitary (heterogenous_cblinfun_id :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<and> unitary (heterogenous_cblinfun_id :: 'b \<Rightarrow>\<^sub>C\<^sub>L 'a)"

lemma heterogenous_same_type_cblinfun[simp]: \<open>heterogenous_same_type_cblinfun (x::'a::chilbert_space itself) (y::'a::chilbert_space itself)\<close>
  unfolding heterogenous_same_type_cblinfun_def by auto

instantiation cblinfun :: (chilbert_space, chilbert_space) ord begin
definition less_eq_cblinfun_def_heterogenous: \<open>A \<le> B \<longleftrightarrow>
  (if heterogenous_same_type_cblinfun TYPE('a) TYPE('b) then
    \<forall>\<psi>::'b. cinner \<psi> ((B-A) *\<^sub>V heterogenous_cblinfun_id *\<^sub>V \<psi>) \<ge> 0 else (A=B))\<close>
definition \<open>(A :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) < B \<longleftrightarrow> A \<le> B \<and> \<not> B \<le> A\<close>
instance..
end

lemma less_eq_cblinfun_def: \<open>A \<le> B \<longleftrightarrow>
    (\<forall>\<psi>. cinner \<psi> (A *\<^sub>V \<psi>) \<le> cinner \<psi> (B *\<^sub>V \<psi>))\<close>
  unfolding less_eq_cblinfun_def_heterogenous
  by (auto simp del: less_eq_complex_def simp: cblinfun.diff_left cinner_diff_right)

instantiation cblinfun :: (chilbert_space, chilbert_space) ordered_complex_vector begin
instance
proof intro_classes
  fix x y z :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  fix a b :: complex

  define pos where \<open>pos X \<longleftrightarrow> (\<forall>\<psi>. cinner \<psi> (X *\<^sub>V \<psi>) \<ge> 0)\<close> for X :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  consider (unitary) \<open>heterogenous_same_type_cblinfun TYPE('a) TYPE('b)\<close>
      \<open>\<And>A B :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b. A \<le> B = pos ((B-A) o\<^sub>C\<^sub>L (heterogenous_cblinfun_id :: 'b\<Rightarrow>\<^sub>C\<^sub>L'a))\<close>
    | (trivial) \<open>\<And>A B :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b. A \<le> B \<longleftrightarrow> A = B\<close>
    by atomize_elim (auto simp: pos_def less_eq_cblinfun_def_heterogenous)
  note cases = this

  have [simp]: \<open>pos 0\<close>
    unfolding pos_def by auto

  have pos_nondeg: \<open>X = 0\<close> if \<open>pos X\<close> and \<open>pos (-X)\<close> for X
    apply (rule cblinfun_cinner_eqI, simp)
    using that by (metis (no_types, lifting) cblinfun.minus_left cinner_minus_right dual_order.antisym equation_minus_iff neg_le_0_iff_le pos_def)

  have pos_add: \<open>pos (X+Y)\<close> if \<open>pos X\<close> and \<open>pos Y\<close> for X Y
    by (smt (z3) pos_def cblinfun.diff_left cinner_minus_right cinner_simps(3) diff_ge_0_iff_ge diff_minus_eq_add neg_le_0_iff_le order_trans that(1) that(2) uminus_cblinfun.rep_eq)

  have pos_scaleC: \<open>pos (a *\<^sub>C X)\<close> if \<open>a\<ge>0\<close> and \<open>pos X\<close> for X a
    using that unfolding pos_def by (auto simp: cblinfun.scaleC_left)

  let ?id = \<open>heterogenous_cblinfun_id :: 'b \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>

  show \<open>x \<le> x\<close>
    apply (cases rule:cases) by auto
  show \<open>(x < y) \<longleftrightarrow> (x \<le> y \<and> \<not> y \<le> x)\<close>
    unfolding less_cblinfun_def by simp
  show \<open>x \<le> z\<close> if \<open>x \<le> y\<close> and \<open>y \<le> z\<close>
  proof (cases rule:cases)
    case unitary
    define a b :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> where \<open>a = (y-x) o\<^sub>C\<^sub>L heterogenous_cblinfun_id\<close>
      and \<open>b = (z-y) o\<^sub>C\<^sub>L heterogenous_cblinfun_id\<close>
    with unitary that have \<open>pos a\<close> and \<open>pos b\<close>
      by auto
    then have \<open>pos (a + b)\<close>
      by (rule pos_add)
    moreover have \<open>a + b = (z - x) o\<^sub>C\<^sub>L heterogenous_cblinfun_id\<close>
      unfolding a_def b_def
      by (metis (no_types, lifting) bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose diff_add_cancel ordered_field_class.sign_simps(2) ordered_field_class.sign_simps(8))
    ultimately show ?thesis
      using unitary by auto
  next
    case trivial
    with that show ?thesis by auto
  qed
  show \<open>x = y\<close> if \<open>x \<le> y\<close> and \<open>y \<le> x\<close>
  proof (cases rule:cases)
    case unitary
    then have \<open>unitary ?id\<close>
      by (auto simp: heterogenous_same_type_cblinfun_def)
    define a b :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> where \<open>a = (y-x) o\<^sub>C\<^sub>L ?id\<close>
      and \<open>b = (x-y) o\<^sub>C\<^sub>L ?id\<close>
    with unitary that have \<open>pos a\<close> and \<open>pos b\<close>
      by auto
    then have \<open>a = 0\<close>
      apply (rule_tac pos_nondeg)
       apply (auto simp: a_def b_def)
      by (smt (verit, best) add.commute bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose cblinfun_compose_zero_left diff_0 diff_add_cancel group_cancel.rule0 group_cancel.sub1)
    then show ?thesis
      unfolding a_def using \<open>unitary ?id\<close>
      by (metis cblinfun_compose_assoc cblinfun_compose_id_right cblinfun_compose_zero_left eq_iff_diff_eq_0 unitaryD2)
  next
    case trivial
    with that show ?thesis by simp
  qed
  show \<open>x + y \<le> x + z\<close> if \<open>y \<le> z\<close>
  proof (cases rule:cases)
    case unitary
    with that show ?thesis
      by auto
  next
    case trivial
    with that show ?thesis
      by auto
  qed

  show \<open>a *\<^sub>C x \<le> a *\<^sub>C y\<close> if \<open>x \<le> y\<close> and \<open>0 \<le> a\<close>
  proof (cases rule:cases)
    case unitary
    with that pos_scaleC show ?thesis
      by (metis cblinfun_compose_scaleC_left complex_vector.scale_right_diff_distrib)
  next
    case trivial
    with that show ?thesis
      by auto
  qed

  show \<open>a *\<^sub>C x \<le> b *\<^sub>C x\<close> if \<open>a \<le> b\<close> and \<open>0 \<le> x\<close>
  proof (cases rule:cases)
    case unitary
    with that show ?thesis
      by (auto intro!: pos_scaleC simp flip: scaleC_diff_left)
  next
    case trivial
    with that show ?thesis
      by auto
  qed
qed
end



lemma positive_id_cblinfun[simp]: "id_cblinfun \<ge> 0"
  unfolding less_eq_cblinfun_def using cinner_ge_zero by auto

lemma positive_hermitianI: \<open>A* = A\<close> if \<open>A \<ge> 0\<close>
  apply (rule cinner_real_hermiteanI)
  using that by (auto simp: complex_is_real_iff_compare0 less_eq_cblinfun_def)

lemma cblinfun_leI:
  assumes \<open>\<And>x. norm x = 1 \<Longrightarrow> x \<bullet>\<^sub>C (A *\<^sub>V x) \<le> x \<bullet>\<^sub>C (B *\<^sub>V x)\<close>
  shows \<open>A \<le> B\<close>
proof (unfold less_eq_cblinfun_def, intro allI, case_tac \<open>\<psi> = 0\<close>)
  fix \<psi> :: 'a assume \<open>\<psi> = 0\<close>
  then show \<open>\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>) \<le> \<psi> \<bullet>\<^sub>C (B *\<^sub>V \<psi>)\<close>
    by simp
next
  fix \<psi> :: 'a assume \<open>\<psi> \<noteq> 0\<close>
  define \<phi> where \<open>\<phi> = \<psi> /\<^sub>R norm \<psi>\<close>
  have \<open>\<phi> \<bullet>\<^sub>C (A *\<^sub>V \<phi>) \<le> \<phi> \<bullet>\<^sub>C (B *\<^sub>V \<phi>)\<close>
    apply (rule assms)
    unfolding \<phi>_def
    by (simp add: \<open>\<psi> \<noteq> 0\<close>)
  with \<open>\<psi> \<noteq> 0\<close> show \<open>\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>) \<le> \<psi> \<bullet>\<^sub>C (B *\<^sub>V \<psi>)\<close>
    unfolding \<phi>_def
    by (smt (verit) cinner_adj_left cinner_scaleR_left cinner_simps(6) complex_of_real_nn_iff mult_cancel_right1 mult_left_mono norm_eq_zero norm_ge_zero of_real_1 right_inverse scaleR_scaleC scaleR_scaleR)
qed

lemma positive_cblinfunI: \<open>A \<ge> 0\<close> if \<open>\<And>x. norm x = 1 \<Longrightarrow> cinner x (A *\<^sub>V x) \<ge> 0\<close>
  apply (rule cblinfun_leI)
  using that by simp

lemma less_eq_scaled_id_norm: 
  assumes \<open>norm A \<le> c\<close> and \<open>A = A*\<close>
  shows \<open>A \<le> complex_of_real c *\<^sub>C id_cblinfun\<close>
proof -
  have \<open>x \<bullet>\<^sub>C (A *\<^sub>V x) \<le> complex_of_real c\<close> if \<open>norm x = 1\<close> for x
  proof -
    have \<open>norm (x \<bullet>\<^sub>C (A *\<^sub>V x)) \<le> norm (A *\<^sub>V x)\<close>
      by (metis complex_inner_class.Cauchy_Schwarz_ineq2 mult_cancel_right1 that)
    also have \<open>\<dots> \<le> norm A\<close>
      by (metis more_arith_simps(6) norm_cblinfun that)
    also have \<open>\<dots> \<le> c\<close>
      by (rule assms)
    finally have \<open>norm (x \<bullet>\<^sub>C (A *\<^sub>V x)) \<le> c\<close>
      by -
    moreover have \<open>x \<bullet>\<^sub>C (A *\<^sub>V x) \<in> \<real>\<close>
      by (metis assms(2) cinner_hermitian_real)
    ultimately show ?thesis
      by (metis cnorm_le_square complex_of_real_cmod complex_of_real_mono complex_of_real_nn_iff dual_order.trans reals_zero_comparable)
  qed
  then show ?thesis
    by (smt (verit) cblinfun.scaleC_left cblinfun_id_cblinfun_apply cblinfun_leI cinner_scaleC_right cnorm_eq_1 mult_cancel_left2)
qed

(* Note: this does not require B to be a square operator *)
lemma positive_cblinfun_squareI: \<open>A = B* o\<^sub>C\<^sub>L B \<Longrightarrow> A \<ge> 0\<close>
  apply (rule positive_cblinfunI)
  by (metis cblinfun_apply_cblinfun_compose cinner_adj_right cinner_ge_zero)

lemma one_dim_loewner_order: \<open>A \<ge> B \<longleftrightarrow> one_dim_iso A \<ge> (one_dim_iso B :: complex)\<close> for A B :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a::{chilbert_space, one_dim}\<close>
proof -
  have A: \<open>A = one_dim_iso A *\<^sub>C id_cblinfun\<close>
    by simp
  have B: \<open>B = one_dim_iso B *\<^sub>C id_cblinfun\<close>
    by simp
  have \<open>A \<ge> B \<longleftrightarrow> (\<forall>\<psi>. cinner \<psi> (A \<psi>) \<ge> cinner \<psi> (B \<psi>))\<close>
    by (simp add: less_eq_cblinfun_def)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>\<psi>::'a. one_dim_iso B * (\<psi> \<bullet>\<^sub>C \<psi>) \<le> one_dim_iso A * (\<psi> \<bullet>\<^sub>C \<psi>))\<close>
    apply (subst A, subst B)
    by (metis (no_types, opaque_lifting) cinner_scaleC_right id_cblinfun_apply scaleC_cblinfun.rep_eq)
  also have \<open>\<dots> \<longleftrightarrow> one_dim_iso A \<ge> (one_dim_iso B :: complex)\<close>
    by (auto intro!: mult_right_mono elim!: allE[where x=1])
  finally show ?thesis
    by -
qed

lemma one_dim_positive: \<open>A \<ge> 0 \<longleftrightarrow> one_dim_iso A \<ge> (0::complex)\<close> for A :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a::{chilbert_space, one_dim}\<close>
  using one_dim_loewner_order[where B=0] by auto

lemma op_square_nondegenerate: \<open>a = 0\<close> if \<open>a* o\<^sub>C\<^sub>L a = 0\<close>
proof (rule cblinfun_eq_0_on_UNIV_span[where basis=UNIV]; simp)
  fix s
  from that have \<open>s \<bullet>\<^sub>C ((a* o\<^sub>C\<^sub>L a) *\<^sub>V s) = 0\<close>
    by simp
  then have \<open>(a *\<^sub>V s) \<bullet>\<^sub>C (a *\<^sub>V s) = 0\<close>
    by (simp add: cinner_adj_right)
  then show \<open>a *\<^sub>V s = 0\<close>
    by simp
qed

lemma comparable_hermitean:
  assumes \<open>a \<le> b\<close>
  assumes \<open>a* = a\<close>
  shows \<open>b* = b\<close>
  by (smt (verit, best) assms(1) assms(2) cinner_hermitian_real cinner_real_hermiteanI comparable complex_is_real_iff_compare0 less_eq_cblinfun_def)

lemma comparable_hermitean':
  assumes \<open>a \<le> b\<close>
  assumes \<open>b* = b\<close>
  shows \<open>a* = a\<close>
  by (smt (verit, best) assms(1) assms(2) cinner_hermitian_real cinner_real_hermiteanI comparable complex_is_real_iff_compare0 less_eq_cblinfun_def)

lemma Proj_mono: \<open>Proj S \<le> Proj T \<longleftrightarrow> S \<le> T\<close>
proof (rule iffI)
  assume \<open>S \<le> T\<close>
  define D where \<open>D = Proj T - Proj S\<close>
  from \<open>S \<le> T\<close> have TS_S[simp]: \<open>Proj T o\<^sub>C\<^sub>L Proj S = Proj S\<close>
    by (smt (verit, ccfv_threshold) Proj_idempotent Proj_range cblinfun_apply_cblinfun_compose cblinfun_apply_in_image cblinfun_eqI cblinfun_fixes_range less_eq_ccsubspace.rep_eq subset_iff)
  then have ST_S[simp]: \<open>Proj S o\<^sub>C\<^sub>L Proj T = Proj S\<close>
    by (metis adj_Proj adj_cblinfun_compose)
  have \<open>D* o\<^sub>C\<^sub>L D = D\<close>
    by (simp add: D_def cblinfun_compose_minus_left cblinfun_compose_minus_right adj_minus adj_Proj)
  then have \<open>D \<ge> 0\<close>
    by (metis positive_cblinfun_squareI)
  then show \<open>Proj S \<le> Proj T\<close>
    by (simp add: D_def)
next
  assume PS_PT: \<open>Proj S \<le> Proj T\<close>
  show \<open>S \<le> T\<close>
  proof (rule ccsubspace_leI_unit)
    fix \<psi> assume \<open>\<psi> \<in> space_as_set S\<close> and [simp]: \<open>norm \<psi> = 1\<close>
    then have \<open>1 = norm (Proj S *\<^sub>V \<psi>)\<close>
      by (simp add: Proj_fixes_image)
    also from PS_PT have \<open>\<dots> \<le> norm (Proj T *\<^sub>V \<psi>)\<close>
      by (metis (no_types, lifting) Proj_idempotent adj_Proj cblinfun_apply_cblinfun_compose cinner_adj_left cnorm_le less_eq_cblinfun_def)
    also have \<open>\<dots> \<le> 1\<close>
      by (metis Proj_is_Proj \<open>norm \<psi> = 1\<close> is_Proj_reduces_norm)
    ultimately have \<open>norm (Proj T *\<^sub>V \<psi>) = 1\<close>
      by auto
    then show \<open>\<psi> \<in> space_as_set T\<close>
      by (simp add: norm_Proj_apply_1)
  qed
qed

subsection \<open>Embedding vectors to operators\<close>

lift_definition vector_to_cblinfun :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::one_dim \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> is
  \<open>\<lambda>\<psi> \<phi>. one_dim_iso \<phi> *\<^sub>C \<psi>\<close>
  by (simp add: bounded_clinear_scaleC_const)

lemma vector_to_cblinfun_cblinfun_compose[simp]:
  "A  o\<^sub>C\<^sub>L (vector_to_cblinfun \<psi>) = vector_to_cblinfun (A *\<^sub>V \<psi>)"
  apply transfer
  unfolding comp_def bounded_clinear_def clinear_def Vector_Spaces.linear_def
    module_hom_def module_hom_axioms_def
  by simp

lemma vector_to_cblinfun_add: \<open>vector_to_cblinfun (x + y) = vector_to_cblinfun x + vector_to_cblinfun y\<close>
  by transfer (simp add: scaleC_add_right)

lemma norm_vector_to_cblinfun[simp]: "norm (vector_to_cblinfun x) = norm x"
proof transfer
  have "bounded_clinear (one_dim_iso::'a \<Rightarrow> complex)"
    by simp
  moreover have "onorm (one_dim_iso::'a \<Rightarrow> complex) * norm x = norm x"
    for x :: 'b
    by simp
  ultimately show "onorm (\<lambda>\<phi>. one_dim_iso (\<phi>::'a) *\<^sub>C x) = norm x"
    for x :: 'b
    by (subst onorm_scaleC_left)
qed

lemma bounded_clinear_vector_to_cblinfun[bounded_clinear]: "bounded_clinear vector_to_cblinfun"
  apply (rule bounded_clinearI[where K=1])
    apply (transfer, simp add: scaleC_add_right)
   apply (transfer, simp add: mult.commute)
  by simp

lemma vector_to_cblinfun_scaleC[simp]:
  "vector_to_cblinfun (a *\<^sub>C \<psi>) = a *\<^sub>C vector_to_cblinfun \<psi>" for a::complex
  by (intro clinear.scaleC bounded_clinear.clinear bounded_clinear_vector_to_cblinfun)

lemma vector_to_cblinfun_apply_one_dim[simp]:
  shows "vector_to_cblinfun \<phi> *\<^sub>V \<gamma> = one_dim_iso \<gamma> *\<^sub>C \<phi>"
  by transfer (rule refl)

lemma vector_to_cblinfun_one_dim_iso[simp]: \<open>vector_to_cblinfun = one_dim_iso\<close>
  by (auto intro!: ext cblinfun_eqI)

lemma vector_to_cblinfun_adj_apply[simp]:
  shows "vector_to_cblinfun \<psi>* *\<^sub>V \<phi> = of_complex (cinner \<psi> \<phi>)"
  by (simp add: cinner_adj_right one_dim_iso_def one_dim_iso_inj)

lemma vector_to_cblinfun_comp_one[simp]:
  "(vector_to_cblinfun s :: 'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L _) o\<^sub>C\<^sub>L 1
     = (vector_to_cblinfun s :: 'b::one_dim \<Rightarrow>\<^sub>C\<^sub>L _)"
  apply (transfer fixing: s)
  by fastforce

lemma vector_to_cblinfun_0[simp]: "vector_to_cblinfun 0 = 0"
  by (metis cblinfun.zero_left cblinfun_compose_zero_left vector_to_cblinfun_cblinfun_compose)

lemma image_vector_to_cblinfun[simp]: "vector_to_cblinfun x *\<^sub>S \<top> = ccspan {x}"
  \<comment> \<open>Not that the general case \<^term>\<open>vector_to_cblinfun x *\<^sub>S S\<close> can be handled by using
      that \<open>S = \<top>\<close> or \<open>S = \<bottom>\<close> by @{thm [source] one_dim_ccsubspace_all_or_nothing}\<close>
proof transfer
  show "closure (range (\<lambda>\<phi>::'b. one_dim_iso \<phi> *\<^sub>C x)) = closure (cspan {x})"
    for x :: 'a
  proof (rule arg_cong [where f = closure])
    have "k *\<^sub>C x \<in> range (\<lambda>\<phi>. one_dim_iso \<phi> *\<^sub>C x)" for k
      by (smt (z3) id_apply one_dim_iso_id one_dim_iso_idem range_eqI)
    thus "range (\<lambda>\<phi>. one_dim_iso (\<phi>::'b) *\<^sub>C x) = cspan {x}"
      unfolding complex_vector.span_singleton
      by auto
  qed
qed

lemma vector_to_cblinfun_adj_comp_vector_to_cblinfun[simp]:
  shows "vector_to_cblinfun \<psi>* o\<^sub>C\<^sub>L vector_to_cblinfun \<phi> = cinner \<psi> \<phi> *\<^sub>C id_cblinfun"
proof -
  have "one_dim_iso \<gamma> *\<^sub>C one_dim_iso (of_complex (\<psi> \<bullet>\<^sub>C \<phi>)) =
    (\<psi> \<bullet>\<^sub>C \<phi>) *\<^sub>C one_dim_iso \<gamma>"
    for \<gamma> :: "'c::one_dim"
    by (metis complex_vector.scale_left_commute of_complex_def one_dim_iso_of_one one_dim_iso_scaleC one_dim_scaleC_1)
  hence "one_dim_iso ((vector_to_cblinfun \<psi>* o\<^sub>C\<^sub>L vector_to_cblinfun \<phi>) *\<^sub>V \<gamma>)
      = one_dim_iso ((cinner \<psi> \<phi> *\<^sub>C id_cblinfun) *\<^sub>V \<gamma>)"
    for \<gamma> :: "'c::one_dim"
    by simp
  hence "((vector_to_cblinfun \<psi>* o\<^sub>C\<^sub>L vector_to_cblinfun \<phi>) *\<^sub>V \<gamma>) = ((cinner \<psi> \<phi> *\<^sub>C id_cblinfun) *\<^sub>V \<gamma>)"
    for \<gamma> :: "'c::one_dim"
    by (rule one_dim_iso_inj)
  thus ?thesis
    using cblinfun_eqI[where x = "vector_to_cblinfun \<psi>* o\<^sub>C\<^sub>L vector_to_cblinfun \<phi>"
        and y = "(\<psi> \<bullet>\<^sub>C \<phi>) *\<^sub>C id_cblinfun"]
    by auto
qed

lemma isometry_vector_to_cblinfun[simp]:
  assumes "norm x = 1"
  shows "isometry (vector_to_cblinfun x)"
  using assms cnorm_eq_1 isometry_def by force

lemma image_vector_to_cblinfun_adj: 
  assumes \<open>\<psi> \<notin> space_as_set (- S)\<close>
  shows \<open>(vector_to_cblinfun \<psi>)* *\<^sub>S S = \<top>\<close>
proof -
  from assms obtain \<phi> where \<open>\<phi> \<in> space_as_set S\<close> and \<open>\<not> is_orthogonal \<psi> \<phi>\<close>
    by (metis orthogonal_complementI uminus_ccsubspace.rep_eq)
  have \<open>((vector_to_cblinfun \<psi>)* *\<^sub>S S :: 'b ccsubspace) \<ge> (vector_to_cblinfun \<psi>)* *\<^sub>S ccspan {\<phi>}\<close> (is \<open>_ \<ge> \<dots>\<close>)
    by (simp add: \<open>\<phi> \<in> space_as_set S\<close> cblinfun_image_mono ccspan_leqI)
  also have \<open>\<dots> = ccspan {(vector_to_cblinfun \<psi>)* *\<^sub>V \<phi>}\<close>
    by (auto simp: cblinfun_image_ccspan)
  also have \<open>\<dots> = ccspan {of_complex (\<psi> \<bullet>\<^sub>C \<phi>)}\<close>
    by auto
  also have \<open>\<dots> > \<bottom>\<close>
    by (simp add: \<open>\<psi> \<bullet>\<^sub>C \<phi> \<noteq> 0\<close> flip: bot.not_eq_extremum )
  finally(dual_order.strict_trans1) show ?thesis
    using one_dim_ccsubspace_all_or_nothing bot.not_eq_extremum by auto
qed


lemma image_vector_to_cblinfun_adj': 
  assumes \<open>\<psi> \<noteq> 0\<close>
  shows \<open>(vector_to_cblinfun \<psi>)* *\<^sub>S \<top> = \<top>\<close>
  apply (rule image_vector_to_cblinfun_adj)
  using assms by simp

subsection \<open>Rank-1 operators / butterflies\<close>

definition rank1 where \<open>rank1 A \<longleftrightarrow> (\<exists>\<psi>\<noteq>0. A *\<^sub>S \<top> = ccspan {\<psi>})\<close>

definition "butterfly (s::'a::complex_normed_vector) (t::'b::chilbert_space)
   = vector_to_cblinfun s o\<^sub>C\<^sub>L (vector_to_cblinfun t :: complex \<Rightarrow>\<^sub>C\<^sub>L _)*"

abbreviation "selfbutter s \<equiv> butterfly s s"

lemma butterfly_add_left: \<open>butterfly (a + a') b = butterfly a b + butterfly a' b\<close>
  by (simp add: butterfly_def vector_to_cblinfun_add cbilinear_add_left bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose)

lemma butterfly_add_right: \<open>butterfly a (b + b') = butterfly a b + butterfly a b'\<close>
  by (simp add: butterfly_def adj_plus vector_to_cblinfun_add cblinfun_compose_add_right)

lemma butterfly_def_one_dim: "butterfly s t = (vector_to_cblinfun s :: 'c::one_dim \<Rightarrow>\<^sub>C\<^sub>L _)
                                          o\<^sub>C\<^sub>L (vector_to_cblinfun t :: 'c \<Rightarrow>\<^sub>C\<^sub>L _)*"
  (is "_ = ?rhs") for s :: "'a::complex_normed_vector" and t :: "'b::chilbert_space"
proof -
  let ?isoAC = "1 :: 'c \<Rightarrow>\<^sub>C\<^sub>L complex"
  let ?isoCA = "1 :: complex \<Rightarrow>\<^sub>C\<^sub>L 'c"
  let ?vector = "vector_to_cblinfun :: _ \<Rightarrow> ('c \<Rightarrow>\<^sub>C\<^sub>L _)"

  have "butterfly s t =
    (?vector s o\<^sub>C\<^sub>L ?isoCA) o\<^sub>C\<^sub>L (?vector t o\<^sub>C\<^sub>L ?isoCA)*"
    unfolding butterfly_def vector_to_cblinfun_comp_one by simp
  also have "\<dots> = ?vector s o\<^sub>C\<^sub>L (?isoCA o\<^sub>C\<^sub>L ?isoCA*) o\<^sub>C\<^sub>L (?vector t)*"
    by (metis (no_types, lifting) cblinfun_compose_assoc adj_cblinfun_compose)
  also have "\<dots> = ?rhs"
    by simp
  finally show ?thesis
    by simp
qed

lemma butterfly_comp_cblinfun: "butterfly \<psi> \<phi> o\<^sub>C\<^sub>L a = butterfly \<psi> (a* *\<^sub>V \<phi>)"
  unfolding butterfly_def
  by (simp add: cblinfun_compose_assoc flip: vector_to_cblinfun_cblinfun_compose)

lemma cblinfun_comp_butterfly: "a o\<^sub>C\<^sub>L butterfly \<psi> \<phi> = butterfly (a *\<^sub>V \<psi>) \<phi>"
  unfolding butterfly_def
  by (simp add: cblinfun_compose_assoc flip: vector_to_cblinfun_cblinfun_compose)

lemma butterfly_apply[simp]: "butterfly \<psi> \<psi>' *\<^sub>V \<phi> = (\<psi>' \<bullet>\<^sub>C \<phi>) *\<^sub>C \<psi>"
  by (simp add: butterfly_def scaleC_cblinfun.rep_eq)

lemma butterfly_scaleC_left[simp]: "butterfly (c *\<^sub>C \<psi>) \<phi> = c *\<^sub>C butterfly \<psi> \<phi>"
  unfolding butterfly_def vector_to_cblinfun_scaleC scaleC_adj
  by (simp add: cnj_x_x)

lemma butterfly_scaleC_right[simp]: "butterfly \<psi> (c *\<^sub>C \<phi>) = cnj c *\<^sub>C butterfly \<psi> \<phi>"
  unfolding butterfly_def vector_to_cblinfun_scaleC scaleC_adj
  by (simp add: cnj_x_x)

lemma butterfly_scaleR_left[simp]: "butterfly (r *\<^sub>R \<psi>) \<phi> = r *\<^sub>C butterfly \<psi> \<phi>"
  by (simp add: scaleR_scaleC)

lemma butterfly_scaleR_right[simp]: "butterfly \<psi> (r *\<^sub>R \<phi>) = r *\<^sub>C butterfly \<psi> \<phi>"
  by (simp add: butterfly_scaleC_right scaleR_scaleC)

lemma butterfly_adjoint[simp]: "(butterfly \<psi> \<phi>)* = butterfly \<phi> \<psi>"
  unfolding butterfly_def by auto

lemma butterfly_comp_butterfly[simp]: "butterfly \<psi>1 \<psi>2 o\<^sub>C\<^sub>L butterfly \<psi>3 \<psi>4 = (\<psi>2 \<bullet>\<^sub>C \<psi>3) *\<^sub>C butterfly \<psi>1 \<psi>4"
  by (simp add: butterfly_comp_cblinfun)

lemma butterfly_0_left[simp]: "butterfly 0 a = 0"
  by (simp add: butterfly_def)

lemma butterfly_0_right[simp]: "butterfly a 0 = 0"
  by (simp add: butterfly_def)

lemma butterfly_is_rank1:
  assumes \<open>\<phi> \<noteq> 0\<close>
  shows \<open>butterfly \<psi> \<phi> *\<^sub>S \<top> = ccspan {\<psi>}\<close>
  using assms by (simp add: butterfly_def cblinfun_compose_image image_vector_to_cblinfun_adj')


lemma rank1_is_butterfly:
  assumes \<open>A *\<^sub>S \<top> = ccspan {\<psi>::_::chilbert_space}\<close>
  shows \<open>\<exists>\<phi>. A = butterfly \<psi> \<phi>\<close>
proof (rule exI[of _ \<open>A* *\<^sub>V (\<psi> /\<^sub>R (norm \<psi>)\<^sup>2)\<close>], rule cblinfun_eqI)
  fix \<gamma> :: 'b
  from assms have \<open>A *\<^sub>V \<gamma> \<in> space_as_set (ccspan {\<psi>})\<close>
    by (simp flip: assms)
  then obtain c where c: \<open>A *\<^sub>V \<gamma> = c *\<^sub>C \<psi>\<close>
    apply atomize_elim
    apply (auto simp: ccspan.rep_eq)
    by (metis complex_vector.span_breakdown_eq complex_vector.span_empty eq_iff_diff_eq_0 singletonD)
  have \<open>A *\<^sub>V \<gamma> = butterfly \<psi> (\<psi> /\<^sub>R (norm \<psi>)\<^sup>2) *\<^sub>V (A *\<^sub>V \<gamma>)\<close>
    apply (auto simp: c simp flip: scaleC_scaleC)
    by (metis cinner_eq_zero_iff divideC_field_simps(1) power2_norm_eq_cinner scaleC_left_commute scaleC_zero_right)
  also have \<open>\<dots> = (butterfly \<psi> (\<psi> /\<^sub>R (norm \<psi>)\<^sup>2) o\<^sub>C\<^sub>L A) *\<^sub>V \<gamma>\<close>
    by simp
  also have \<open>\<dots> = butterfly \<psi> (A* *\<^sub>V (\<psi> /\<^sub>R (norm \<psi>)\<^sup>2)) *\<^sub>V \<gamma>\<close>
    by (simp add: cinner_adj_left)
  finally show \<open>A *\<^sub>V \<gamma> = \<dots>\<close>
    by -
qed

lemma zero_not_rank1[simp]: \<open>\<not> rank1 0\<close>
  unfolding rank1_def
  by auto (metis ccspan_superset insert_not_empty singleton_insert_inj_eq space_as_set_bot subset_singletonD)

lemma rank1_iff_butterfly: \<open>rank1 A \<longleftrightarrow> (\<exists>\<psi> \<phi>. A = butterfly \<psi> \<phi>) \<and> A \<noteq> 0\<close>
  for A :: \<open>_::complex_inner \<Rightarrow>\<^sub>C\<^sub>L _::chilbert_space\<close>
proof (rule iffI)
  assume \<open>rank1 A\<close>
  then obtain \<psi> where \<open>A *\<^sub>S \<top> = ccspan {\<psi>}\<close>
    using rank1_def by auto
  then have \<open>\<exists>\<phi>. A = butterfly \<psi> \<phi>\<close>
    by (rule rank1_is_butterfly)
  moreover from \<open>rank1 A\<close> have \<open>A \<noteq> 0\<close>
    by auto
  ultimately show \<open>(\<exists>\<psi> \<phi>. A = butterfly \<psi> \<phi>) \<and> A \<noteq> 0\<close>
    by auto
next
  assume asm: \<open>(\<exists>\<psi> \<phi>. A = butterfly \<psi> \<phi>) \<and> A \<noteq> 0\<close>
  then obtain \<psi> \<phi> where A: \<open>A = butterfly \<psi> \<phi>\<close>
    by auto
  from asm have \<open>A \<noteq> 0\<close>
    by simp
  with A have \<open>\<psi> \<noteq> 0\<close> and \<open>\<phi> \<noteq> 0\<close>
    by auto
  then have \<open>butterfly \<psi> \<phi> *\<^sub>S \<top> = ccspan {\<psi>}\<close>
    by (rule_tac butterfly_is_rank1)
  with A \<open>\<psi> \<noteq> 0\<close> show \<open>rank1 A\<close>
    by (auto intro!: exI[of _ \<psi>] simp: rank1_def)
qed

lemma butterfly_if_rank1: \<open>(\<exists>\<psi> \<phi>. A = butterfly \<psi> \<phi>) \<longleftrightarrow> rank1 A \<or> A = 0\<close>
  for A :: \<open>_::complex_inner \<Rightarrow>\<^sub>C\<^sub>L _::chilbert_space\<close>
  by (metis butterfly_0_left rank1_iff_butterfly)

lemma norm_butterfly: "norm (butterfly \<psi> \<phi>) = norm \<psi> * norm \<phi>"
proof (cases "\<phi>=0")
  case True
  then show ?thesis by simp
next
  case False
  show ?thesis
    unfolding norm_cblinfun.rep_eq
    thm onormI[OF _ False]
  proof (rule onormI[OF _ False])
    fix x

    have "cmod (\<phi> \<bullet>\<^sub>C x) * norm \<psi> \<le> norm \<psi> * norm \<phi> * norm x"
      by (metis ab_semigroup_mult_class.mult_ac(1) complex_inner_class.Cauchy_Schwarz_ineq2 mult.commute mult_left_mono norm_ge_zero)
    thus "norm (butterfly \<psi> \<phi> *\<^sub>V x) \<le> norm \<psi> * norm \<phi> * norm x"
      by (simp add: power2_eq_square)

    show "norm (butterfly \<psi> \<phi> *\<^sub>V \<phi>) = norm \<psi> * norm \<phi> * norm \<phi>"
      by (smt (z3) ab_semigroup_mult_class.mult_ac(1) butterfly_apply mult.commute norm_eq_sqrt_cinner norm_ge_zero norm_scaleC power2_eq_square real_sqrt_abs real_sqrt_eq_iff)
  qed
qed

lemma bounded_sesquilinear_butterfly[bounded_sesquilinear]: \<open>bounded_sesquilinear (\<lambda>(b::'b::chilbert_space) (a::'a::chilbert_space). butterfly a b)\<close>
proof standard
  fix a a' :: 'a and b b' :: 'b and r :: complex
  show \<open>butterfly (a + a') b = butterfly a b + butterfly a' b\<close>
    by (rule butterfly_add_left)
  show \<open>butterfly a (b + b') = butterfly a b + butterfly a b'\<close>
    by (rule butterfly_add_right)
  show \<open>butterfly (r *\<^sub>C a) b = r *\<^sub>C butterfly a b\<close>
    by simp
  show \<open>butterfly a (r *\<^sub>C b) = cnj r *\<^sub>C butterfly a b\<close>
    by simp
  show \<open>\<exists>K. \<forall>b a. norm (butterfly a b) \<le> norm b * norm a * K \<close>
    apply (rule exI[of _ 1])
    by (simp add: norm_butterfly)
qed

lemma inj_selfbutter_upto_phase:
  assumes "selfbutter x = selfbutter y"
  shows "\<exists>c. cmod c = 1 \<and> x = c *\<^sub>C y"
proof (cases "x = 0")
  case True
  from assms have "y = 0"
    using norm_butterfly
    by (metis True butterfly_0_left divisors_zero norm_eq_zero)
  with True show ?thesis
    using norm_one by fastforce
next
  case False
  define c where "c = (y \<bullet>\<^sub>C x) / (x \<bullet>\<^sub>C x)"
  have "(x \<bullet>\<^sub>C x) *\<^sub>C x = selfbutter x *\<^sub>V x"
    by (simp add: butterfly_apply)
  also have "\<dots> = selfbutter y *\<^sub>V x"
    using assms by simp
  also have "\<dots> = (y \<bullet>\<^sub>C x) *\<^sub>C y"
    by (simp add: butterfly_apply)
  finally have xcy: "x = c *\<^sub>C y"
    by (simp add: c_def ceq_vector_fraction_iff)
  have "cmod c * norm x = cmod c * norm y"
    using assms norm_butterfly
    by (smt (verit, ccfv_SIG) \<open>(x \<bullet>\<^sub>C x) *\<^sub>C x = selfbutter x *\<^sub>V x\<close> \<open>selfbutter y *\<^sub>V x = (y \<bullet>\<^sub>C x) *\<^sub>C y\<close> cinner_scaleC_right complex_vector.scale_left_commute complex_vector.scale_right_imp_eq mult_cancel_left norm_eq_sqrt_cinner norm_eq_zero scaleC_scaleC xcy)
  also have "cmod c * norm y = norm (c *\<^sub>C y)"
    by simp
  also have "\<dots> = norm x"
    unfolding xcy[symmetric] by simp
  finally have c: "cmod c = 1"
    by (simp add: False)
  from c xcy show ?thesis
    by auto
qed

lemma butterfly_eq_proj:
  assumes "norm x = 1"
  shows "selfbutter x = proj x"
proof -
  define B and \<phi> :: "complex \<Rightarrow>\<^sub>C\<^sub>L 'a"
    where "B = selfbutter x" and "\<phi> = vector_to_cblinfun x"
  then have B: "B = \<phi> o\<^sub>C\<^sub>L \<phi>*"
    unfolding butterfly_def by simp
  have \<phi>adj\<phi>: "\<phi>* o\<^sub>C\<^sub>L \<phi> = id_cblinfun"
    using \<phi>_def assms isometry_def isometry_vector_to_cblinfun by blast
  have "B o\<^sub>C\<^sub>L B = \<phi> o\<^sub>C\<^sub>L (\<phi>* o\<^sub>C\<^sub>L \<phi>) o\<^sub>C\<^sub>L \<phi>*"
    by (simp add: B cblinfun_assoc_left(1))
  also have "\<dots> = B"
    unfolding \<phi>adj\<phi> by (simp add: B)
  finally have idem: "B o\<^sub>C\<^sub>L B = B".
  have herm: "B = B*"
    unfolding B by simp
  from idem herm have BProj: "B = Proj (B *\<^sub>S top)"
    by (rule Proj_on_own_range'[symmetric])
  have "B *\<^sub>S top = ccspan {x}"
    by (simp add: B \<phi>_def assms cblinfun_compose_image range_adjoint_isometry)
  with BProj show "B = proj x"
    by simp
qed

lemma butterfly_sgn_eq_proj:
  shows "selfbutter (sgn x) = proj x"
proof (cases \<open>x = 0\<close>)
  case True
  then show ?thesis
    by simp
next
  case False
  then have \<open>selfbutter (sgn x) = proj (sgn x)\<close>
    by (simp add: butterfly_eq_proj norm_sgn)
  also have \<open>ccspan {sgn x} = ccspan {x}\<close>
    by (metis ccspan_singleton_scaleC scaleC_eq_0_iff scaleR_scaleC sgn_div_norm sgn_zero_iff)
  finally show ?thesis
    by -
qed

lemma butterfly_is_Proj:
  \<open>norm x = 1 \<Longrightarrow> is_Proj (selfbutter x)\<close>
  by (subst butterfly_eq_proj, simp_all)

lemma cspan_butterfly_UNIV:
  assumes \<open>cspan basisA = UNIV\<close>
  assumes \<open>cspan basisB = UNIV\<close>
  assumes \<open>is_ortho_set basisB\<close>
  assumes \<open>\<And>b. b \<in> basisB \<Longrightarrow> norm b = 1\<close>
  shows \<open>cspan {butterfly a b| (a::'a::{complex_normed_vector}) (b::'b::{chilbert_space,cfinite_dim}). a \<in> basisA \<and> b \<in> basisB} = UNIV\<close>
proof -
  have F: \<open>\<exists>F\<in>{butterfly a b |a b. a \<in> basisA \<and> b \<in> basisB}. \<forall>b'\<in>basisB. F *\<^sub>V b' = (if b' = b then a else 0)\<close>
    if \<open>a \<in> basisA\<close> and \<open>b \<in> basisB\<close> for a b
    apply (rule bexI[where x=\<open>butterfly a b\<close>])
    using assms that by (auto simp: is_ortho_set_def cnorm_eq_1)
  show ?thesis
    apply (rule cblinfun_cspan_UNIV[where basisA=basisB and basisB=basisA])
    using assms apply auto[2]
    using F by (smt (verit, ccfv_SIG) image_iff)
qed

lemma cindependent_butterfly:
  fixes basisA :: \<open>'a::chilbert_space set\<close> and basisB :: \<open>'b::chilbert_space set\<close>
  assumes \<open>is_ortho_set basisA\<close> \<open>is_ortho_set basisB\<close>
  assumes normA: \<open>\<And>a. a\<in>basisA \<Longrightarrow> norm a = 1\<close> and normB: \<open>\<And>b. b\<in>basisB \<Longrightarrow> norm b = 1\<close>
  shows \<open>cindependent {butterfly a b| a b. a\<in>basisA \<and> b\<in>basisB}\<close>
proof (unfold complex_vector.independent_explicit_module, intro allI impI, rename_tac T f g)
  fix T :: \<open>('b \<Rightarrow>\<^sub>C\<^sub>L 'a) set\<close> and f :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> complex\<close> and g :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assume \<open>finite T\<close>
  assume T_subset: \<open>T \<subseteq> {butterfly a b |a b. a \<in> basisA \<and> b \<in> basisB}\<close>
  define lin where \<open>lin = (\<Sum>g\<in>T. f g *\<^sub>C g)\<close>
  assume \<open>lin = 0\<close>
  assume \<open>g \<in> T\<close>
  (* To show: f g = 0 *)
  then obtain a b where g: \<open>g = butterfly a b\<close> and [simp]: \<open>a \<in> basisA\<close> \<open>b \<in> basisB\<close>
    using T_subset by auto

  have *: "(vector_to_cblinfun a)* *\<^sub>V f g *\<^sub>C g *\<^sub>V b = 0"
    if \<open>g \<in> T - {butterfly a b}\<close> for g
  proof -
    from that
    obtain a' b' where g: \<open>g = butterfly a' b'\<close> and [simp]: \<open>a' \<in> basisA\<close> \<open>b' \<in> basisB\<close>
      using T_subset by auto
    from that have \<open>g \<noteq> butterfly a b\<close> by auto
    with g consider (a) \<open>a\<noteq>a'\<close> | (b) \<open>b\<noteq>b'\<close>
      by auto
    then show \<open>(vector_to_cblinfun a)* *\<^sub>V f g *\<^sub>C g *\<^sub>V b = 0\<close>
    proof cases
      case a
      then show ?thesis
        using  \<open>is_ortho_set basisA\<close> unfolding g
        by (auto simp: is_ortho_set_def butterfly_def scaleC_cblinfun.rep_eq)
    next
      case b
      then show ?thesis
        using  \<open>is_ortho_set basisB\<close> unfolding g
        by (auto simp: is_ortho_set_def butterfly_def scaleC_cblinfun.rep_eq)
    qed
  qed

  have \<open>0 = (vector_to_cblinfun a)* *\<^sub>V lin *\<^sub>V b\<close>
    using \<open>lin = 0\<close> by auto
  also have \<open>\<dots> = (\<Sum>g\<in>T. (vector_to_cblinfun a)* *\<^sub>V (f g *\<^sub>C g) *\<^sub>V b)\<close>
    unfolding lin_def
    apply (rule complex_vector.linear_sum)
    by (smt (z3) cblinfun.scaleC_left cblinfun.scaleC_right cblinfun.add_right clinearI plus_cblinfun.rep_eq)
  also have \<open>\<dots> = (\<Sum>g\<in>{butterfly a b}. (vector_to_cblinfun a)* *\<^sub>V (f g *\<^sub>C g) *\<^sub>V b)\<close>
    apply (rule sum.mono_neutral_right)
    using \<open>finite T\<close> * \<open>g \<in> T\<close> g by auto
  also have \<open>\<dots> = (vector_to_cblinfun a)* *\<^sub>V (f g *\<^sub>C g) *\<^sub>V b\<close>
    by (simp add: g)
  also have \<open>\<dots> = f g\<close>
    unfolding g
    using normA normB by (auto simp: butterfly_def scaleC_cblinfun.rep_eq cnorm_eq_1)
  finally show \<open>f g = 0\<close>
    by simp
qed

lemma clinear_eq_butterflyI:
  fixes F G :: \<open>('a::{chilbert_space,cfinite_dim} \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner) \<Rightarrow> 'c::complex_vector\<close>
  assumes "clinear F" and "clinear G"
  assumes \<open>cspan basisA = UNIV\<close> \<open>cspan basisB = UNIV\<close>
  assumes \<open>is_ortho_set basisA\<close> \<open>is_ortho_set basisB\<close>
  assumes "\<And>a b. a\<in>basisA \<Longrightarrow> b\<in>basisB \<Longrightarrow> F (butterfly a b) = G (butterfly a b)"
  assumes \<open>\<And>b. b\<in>basisB \<Longrightarrow> norm b = 1\<close>
  shows "F = G"
  apply (rule complex_vector.linear_eq_on_span[where f=F, THEN ext, rotated 3])
     apply (subst cspan_butterfly_UNIV)
  using assms by auto

lemma sum_butterfly_is_Proj:
  assumes \<open>is_ortho_set E\<close>
  assumes \<open>\<And>e. e\<in>E \<Longrightarrow> norm e = 1\<close>
  shows \<open>is_Proj (\<Sum>e\<in>E. butterfly e e)\<close>
proof (cases \<open>finite E\<close>)
  case True
  show ?thesis
  proof (rule is_Proj_I)
    show \<open>(\<Sum>e\<in>E. butterfly e e)* = (\<Sum>e\<in>E. butterfly e e)\<close>
      by (simp add: sum_adj)
    have ortho: \<open>f \<noteq> e \<Longrightarrow> e \<in> E \<Longrightarrow> f \<in> E \<Longrightarrow> is_orthogonal f e\<close> for f e
      by (meson assms(1) is_ortho_set_def)
    have unit: \<open>e \<bullet>\<^sub>C e = 1\<close> if \<open>e \<in> E\<close> for e
      using assms(2) cnorm_eq_1 that by blast
    have *: \<open>(\<Sum>f\<in>E. (f \<bullet>\<^sub>C e) *\<^sub>C butterfly f e) = butterfly e e\<close> if \<open>e \<in> E\<close> for e
      apply (subst sum_single[where i=e])
      by (auto intro!: simp: that ortho unit True)
    show \<open>(\<Sum>e\<in>E. butterfly e e) o\<^sub>C\<^sub>L (\<Sum>e\<in>E. butterfly e e) = (\<Sum>e\<in>E. butterfly e e)\<close>
      by (auto simp: * cblinfun_compose_sum_right cblinfun_compose_sum_left)
  qed
next
  case False
  then show ?thesis
    by simp
qed

lemma rank1_compose_left: \<open>rank1 (a o\<^sub>C\<^sub>L b)\<close> if \<open>rank1 b\<close> and \<open>a o\<^sub>C\<^sub>L b \<noteq> 0\<close>
proof -
  from \<open>rank1 b\<close>
  obtain \<psi> where \<open>b *\<^sub>S \<top> = ccspan {\<psi>}\<close>
    using rank1_def by blast
  then have *: \<open>(a o\<^sub>C\<^sub>L b) *\<^sub>S \<top> = ccspan {a \<psi>}\<close>
    by (metis cblinfun_assoc_left(2) cblinfun_image_ccspan image_empty image_insert)
  with \<open>a o\<^sub>C\<^sub>L b \<noteq> 0\<close> have \<open>a \<psi> \<noteq> 0\<close>
    by auto
  with * show \<open>rank1 (a o\<^sub>C\<^sub>L b)\<close>
    using rank1_def by blast
qed

lemma rank1_compose_right: \<open>rank1 (a o\<^sub>C\<^sub>L b)\<close> if \<open>rank1 a\<close> and \<open>a o\<^sub>C\<^sub>L b \<noteq> 0\<close>
proof -
  from \<open>rank1 a\<close>
  obtain \<psi> where \<open>a *\<^sub>S \<top> = ccspan {\<psi>}\<close> and \<open>\<psi> \<noteq> 0\<close>
    using rank1_def by blast
  then have *: \<open>(a o\<^sub>C\<^sub>L b) *\<^sub>S \<top> \<le> ccspan {\<psi>}\<close>
    by (metis cblinfun_assoc_left(2) cblinfun_image_mono top_greatest)
  from \<open>a o\<^sub>C\<^sub>L b \<noteq> 0\<close> obtain \<phi> where \<phi>_ab: \<open>\<phi> \<in> space_as_set ((a o\<^sub>C\<^sub>L b) *\<^sub>S \<top>)\<close> and \<open>\<phi> \<noteq> 0\<close>
    by (metis cblinfun.real.zero_left cblinfun_apply_in_image cblinfun_eqI)
  with * have \<open>\<phi> \<in> space_as_set (ccspan {\<psi>})\<close>
    using less_eq_ccsubspace.rep_eq by blast
  with \<open>\<phi> \<noteq> 0\<close> obtain c where \<open>\<phi> = c *\<^sub>C \<psi>\<close> and \<open>c \<noteq> 0\<close>
    apply (simp add: ccspan.rep_eq)
    by (auto simp add: complex_vector.span_singleton)
  with \<phi>_ab have \<open>(a o\<^sub>C\<^sub>L b) *\<^sub>S \<top> \<ge> ccspan {\<psi>}\<close>
    by (metis ccspan_leqI ccspan_singleton_scaleC empty_subsetI insert_subset)
  with * have \<open>(a o\<^sub>C\<^sub>L b) *\<^sub>S \<top> = ccspan {\<psi>}\<close>
    by fastforce
  with \<open>\<psi> \<noteq> 0\<close> show \<open>rank1 (a o\<^sub>C\<^sub>L b)\<close>
    using rank1_def by blast
qed

lemma rank1_scaleC: \<open>rank1 (c *\<^sub>C a)\<close> if \<open>rank1 a\<close> and \<open>c \<noteq> 0\<close>
  using rank1_compose_left[OF \<open>rank1 a\<close>, where a=\<open>c *\<^sub>C id_cblinfun\<close>]
  using that by force

lemma rank1_uminus: \<open>rank1 (-a)\<close> if \<open>rank1 a\<close>
  using that rank1_scaleC[where c=\<open>-1\<close> and a=a] by simp

lemma rank1_uminus_iff[simp]: \<open>rank1 (-a) \<longleftrightarrow> rank1 a\<close>
  using rank1_uminus by force

lemma rank1_adj: \<open>rank1 (a*)\<close> if \<open>rank1 a\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  by (metis adj_0 butterfly_adjoint rank1_iff_butterfly that)

lemma rank1_adj_iff[simp]: \<open>rank1 (a*) \<longleftrightarrow> rank1 a\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  by (metis double_adj rank1_adj)

lemma butterflies_sum_id_finite: \<open>id_cblinfun = (\<Sum>x\<in>B. selfbutter x)\<close> if \<open>is_onb B\<close> for B :: \<open>'a :: {cfinite_dim, chilbert_space} set\<close>
proof (rule cblinfun_eq_gen_eqI)
  from \<open>is_onb B\<close> show \<open>ccspan B = \<top>\<close>
    by (simp add: is_onb_def)
  from \<open>is_onb B\<close> have \<open>cindependent B\<close>
    by (simp add: is_onb_def is_ortho_set_cindependent)
  then have [simp]: \<open>finite B\<close>
    using cindependent_cfinite_dim_finite by blast
  from \<open>is_onb B\<close>
  have 1: \<open>j \<noteq> b \<Longrightarrow> j \<in> B \<Longrightarrow> is_orthogonal j b\<close> if \<open>b \<in> B\<close> for j b
    using that by (auto simp add: is_onb_def is_ortho_set_def)
  from \<open>is_onb B\<close>
  have 2: \<open>b \<bullet>\<^sub>C b = 1\<close> if \<open>b \<in> B\<close> for b
    using that by (simp add: is_onb_def cnorm_eq_1)
  fix b assume \<open>b \<in> B\<close>
  then show \<open>id_cblinfun *\<^sub>V b = (\<Sum>x\<in>B. selfbutter x) *\<^sub>V b\<close>
    using 1 2 by (simp add: cblinfun.sum_left sum_single[where i=b])
qed

lemma butterfly_sum_left: \<open>butterfly (\<Sum>i\<in>M. \<psi> i) \<phi> = (\<Sum>i\<in>M. butterfly (\<psi> i) \<phi>)\<close>
  apply (induction M rule:infinite_finite_induct)
  by (auto simp add: butterfly_add_left)

lemma butterfly_sum_right: \<open>butterfly \<psi> (\<Sum>i\<in>M. \<phi> i) = (\<Sum>i\<in>M. butterfly \<psi> (\<phi> i))\<close>
  apply (induction M rule:infinite_finite_induct)
  by (auto simp add: butterfly_add_right)

subsection \<open>Banach-Steinhaus\<close>

theorem cbanach_steinhaus:
  fixes F :: \<open>'c \<Rightarrow> 'a::cbanach \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>\<And>x. \<exists>M. \<forall>n.  norm ((F n) *\<^sub>V x) \<le> M\<close>
  shows  \<open>\<exists>M. \<forall> n. norm (F n) \<le> M\<close>
  using cblinfun_blinfun_transfer[transfer_rule]
  apply fail? (* Clears "current facts" *)
proof (use assms in transfer)
  fix F :: \<open>'c \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'b\<close> assume \<open>(\<And>x. \<exists>M. \<forall>n. norm (F n *\<^sub>v x) \<le> M)\<close>
  hence \<open>\<And>x. bounded (range (\<lambda>n. blinfun_apply (F n) x))\<close>
    by (metis (no_types, lifting) boundedI rangeE)
  hence \<open>bounded (range F)\<close>
    by (simp add: banach_steinhaus)
  thus  \<open>\<exists>M. \<forall>n. norm (F n) \<le> M\<close>
    by (simp add: bounded_iff)
qed

subsection \<open>Riesz-representation theorem\<close>

theorem riesz_representation_cblinfun_existence:
  \<comment> \<open>Theorem 3.4 in \<^cite>\<open>conway2013course\<close>\<close>
  fixes f::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L complex\<close>
  shows \<open>\<exists>t. \<forall>x.  f *\<^sub>V x = (t \<bullet>\<^sub>C x)\<close>
  by transfer (rule riesz_representation_existence)

lemma riesz_representation_cblinfun_unique:
  \<comment> \<open>Theorem 3.4 in \<^cite>\<open>conway2013course\<close>\<close>
  fixes f::\<open>'a::complex_inner \<Rightarrow>\<^sub>C\<^sub>L complex\<close>
  assumes \<open>\<And>x. f *\<^sub>V x = (t \<bullet>\<^sub>C x)\<close>
  assumes \<open>\<And>x. f *\<^sub>V x = (u \<bullet>\<^sub>C x)\<close>
  shows \<open>t = u\<close>
  using assms by (rule riesz_representation_unique)

theorem riesz_representation_cblinfun_norm:
  includes notation_norm
  fixes f::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L complex\<close>
  assumes \<open>\<And>x.  f *\<^sub>V x = (t \<bullet>\<^sub>C x)\<close>
  shows \<open>\<parallel>f\<parallel> = \<parallel>t\<parallel>\<close>
  using assms
proof transfer
  fix f::\<open>'a \<Rightarrow> complex\<close> and t
  assume \<open>bounded_clinear f\<close> and \<open>\<And>x. f x = (t \<bullet>\<^sub>C x)\<close>
  from  \<open>\<And>x. f x = (t \<bullet>\<^sub>C x)\<close>
  have \<open>(norm (f x)) / (norm x) \<le> norm t\<close>
    for x
  proof(cases \<open>norm x = 0\<close>)
    case True
    thus ?thesis by simp
  next
    case False
    have \<open>norm (f x) = norm ((t \<bullet>\<^sub>C x))\<close>
      using \<open>\<And>x. f x = (t \<bullet>\<^sub>C x)\<close> by simp
    also have \<open>norm (t \<bullet>\<^sub>C x) \<le> norm t * norm x\<close>
      by (simp add: complex_inner_class.Cauchy_Schwarz_ineq2)
    finally have \<open>norm (f x) \<le> norm t * norm x\<close>
      by blast
    thus ?thesis
      by (metis False linordered_field_class.divide_right_mono nonzero_mult_div_cancel_right norm_ge_zero)
  qed
  moreover have \<open>(norm (f t)) / (norm t) = norm t\<close>
  proof(cases \<open>norm t = 0\<close>)
    case True
    thus ?thesis
      by simp
  next
    case False
    have \<open>f t = (t \<bullet>\<^sub>C t)\<close>
      using \<open>\<And>x. f x = (t \<bullet>\<^sub>C x)\<close> by blast
    also have \<open>\<dots> = (norm t)^2\<close>
      by (meson cnorm_eq_square)
    also have \<open>\<dots> = (norm t)*(norm t)\<close>
      by (simp add: power2_eq_square)
    finally have \<open>f t = (norm t)*(norm t)\<close>
      by blast
    thus ?thesis
      by (metis False Re_complex_of_real \<open>\<And>x. f x = cinner t x\<close> cinner_ge_zero complex_of_real_cmod nonzero_divide_eq_eq)
  qed
  ultimately have \<open>Sup {(norm (f x)) / (norm x)| x. True} = norm t\<close>
    by (smt cSup_eq_maximum mem_Collect_eq)
  moreover have \<open>Sup {(norm (f x)) / (norm x)| x. True} = (SUP x. (norm (f x)) / (norm x))\<close>
    by (simp add: full_SetCompr_eq)
  ultimately show \<open>onorm f = norm t\<close>
    by (simp add: onorm_def)
qed

definition the_riesz_rep :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L complex) \<Rightarrow> 'a\<close> where
  \<open>the_riesz_rep f = (SOME t. \<forall>x. f *\<^sub>V x = t \<bullet>\<^sub>C x)\<close>

lemma the_riesz_rep[simp]: \<open>the_riesz_rep f \<bullet>\<^sub>C x = f *\<^sub>V x\<close>
  unfolding the_riesz_rep_def
  apply (rule someI2_ex)
  by (simp_all add: riesz_representation_cblinfun_existence)

lemma the_riesz_rep_unique:
  assumes \<open>\<And>x. f *\<^sub>V x = t \<bullet>\<^sub>C x\<close>
  shows \<open>t = the_riesz_rep f\<close>
  using assms riesz_representation_cblinfun_unique the_riesz_rep by metis

lemma the_riesz_rep_scaleC: \<open>the_riesz_rep (c *\<^sub>C f) = cnj c *\<^sub>C the_riesz_rep f\<close>
  apply (rule the_riesz_rep_unique[symmetric])
  by auto

lemma the_riesz_rep_add: \<open>the_riesz_rep (f + g) = the_riesz_rep f + the_riesz_rep g\<close>
  apply (rule the_riesz_rep_unique[symmetric])
  by (auto simp: cinner_add_left cblinfun.add_left)

lemma the_riesz_rep_norm[simp]: \<open>norm (the_riesz_rep f) = norm f\<close>
  apply (rule riesz_representation_cblinfun_norm[symmetric])
  by simp

lemma bounded_antilinear_the_riesz_rep[bounded_antilinear]: \<open>bounded_antilinear the_riesz_rep\<close>
  by (metis (no_types, opaque_lifting) bounded_antilinear_intro dual_order.refl mult.commute mult_1 the_riesz_rep_add the_riesz_rep_norm the_riesz_rep_scaleC)

lift_definition the_riesz_rep_sesqui :: \<open>('a::complex_normed_vector \<Rightarrow> 'b::chilbert_space \<Rightarrow> complex) \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'b)\<close> is
  \<open>\<lambda>p. if bounded_sesquilinear p then the_riesz_rep o CBlinfun o p else 0\<close>
  by (metis (mono_tags, lifting) Cblinfun_comp_bounded_sesquilinear bounded_antilinear_o_bounded_antilinear' bounded_antilinear_the_riesz_rep bounded_clinear_0 fun.map_comp)

lemma the_riesz_rep_sesqui_apply:
  assumes \<open>bounded_sesquilinear p\<close>
  shows \<open>(the_riesz_rep_sesqui p *\<^sub>V x) \<bullet>\<^sub>C y = p x y\<close>
  apply (transfer fixing: p x y)
  by (auto simp add: CBlinfun_inverse bounded_sesquilinear_apply_bounded_clinear assms)

subsection \<open>Bidual\<close>

lift_definition bidual_embedding :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L (('a \<Rightarrow>\<^sub>C\<^sub>L complex) \<Rightarrow>\<^sub>C\<^sub>L complex)\<close>
  is \<open>\<lambda>x f. f *\<^sub>V x\<close>
  by (simp add: cblinfun.flip)

lemma bidual_embedding_apply[simp]: \<open>(bidual_embedding *\<^sub>V x) *\<^sub>V f = f *\<^sub>V x\<close>
  by (transfer fixing: x f, simp)

lemma bidual_embedding_isometric[simp]: \<open>norm (bidual_embedding *\<^sub>V x) = norm x\<close> for x :: \<open>'a::complex_inner\<close>
proof -
  define f :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L complex\<close> where \<open>f = CBlinfun (\<lambda>y. cinner x y)\<close>
  then have [simp]: \<open>f *\<^sub>V y = cinner x y\<close> for y
    by (simp add: bounded_clinear_CBlinfun_apply bounded_clinear_cinner_right)
  then have [simp]: \<open>norm f = norm x\<close>
    apply (auto intro!: norm_cblinfun_eqI[where x=x] simp: power2_norm_eq_cinner[symmetric])
     apply (smt (verit, best) norm_eq_sqrt_cinner norm_ge_zero power2_norm_eq_cinner real_div_sqrt)
    using Cauchy_Schwarz_ineq2 by blast
  show ?thesis
    apply (auto intro!: norm_cblinfun_eqI[where x=f])
     apply (metis norm_eq_sqrt_cinner norm_imp_pos_and_ge real_div_sqrt)
    by (metis norm_cblinfun ordered_field_class.sign_simps(33))
qed

lemma norm_bidual_embedding[simp]: \<open>norm (bidual_embedding :: 'a::{complex_inner, not_singleton} \<Rightarrow>\<^sub>C\<^sub>L _) = 1\<close>
proof -
  obtain x :: 'a where [simp]: \<open>norm x = 1\<close>
    by (meson UNIV_not_singleton ex_norm1)
  show ?thesis
    by (auto intro!: norm_cblinfun_eqI[where x=x])
qed

lemma isometry_bidual_embedding[simp]: \<open>isometry bidual_embedding\<close>
  by (simp add: norm_preserving_isometry)

lemma bidual_embedding_surj[simp]: \<open>surj (bidual_embedding :: 'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _)\<close>
proof -
  have \<open>\<exists>y''. \<forall>f. (bidual_embedding *\<^sub>V y'') *\<^sub>V f = y *\<^sub>V f\<close>
    for y :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L complex) \<Rightarrow>\<^sub>C\<^sub>L complex\<close>
  proof -
    define y' where \<open>y' = CBlinfun (\<lambda>z. cnj (y (cblinfun_cinner_right z)))\<close>
    have y'_apply: \<open>y' z = cnj (y (cblinfun_cinner_right z))\<close> for z
      unfolding y'_def
      apply (subst CBlinfun_inverse)
      by (auto intro!: bounded_linear_intros)
    obtain y'' where \<open>y' z = y'' \<bullet>\<^sub>C z\<close> for z
      using riesz_representation_cblinfun_existence by blast
    then have y'': \<open>z \<bullet>\<^sub>C y'' = cnj (y' z)\<close> for z
      by auto
    have \<open>(bidual_embedding *\<^sub>V y'') *\<^sub>V f = y *\<^sub>V f\<close> for f :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L complex\<close>
    proof -
      obtain f' where f': \<open>f z = f' \<bullet>\<^sub>C z\<close> for z
        using riesz_representation_cblinfun_existence by blast
      then have f'2: \<open>f = cblinfun_cinner_right f'\<close>
        using cblinfun_apply_inject by force
      show ?thesis
        by (auto simp add: f' f'2 y'' y'_apply)
    qed
    then show ?thesis
      by blast
  qed
  then show ?thesis
    by (metis cblinfun_eqI surj_def)
qed

subsection \<open>Extension of complex bounded operators\<close>

definition cblinfun_extension where
  "cblinfun_extension S \<phi> = (SOME B. \<forall>x\<in>S. B *\<^sub>V x = \<phi> x)"

definition cblinfun_extension_exists where
  "cblinfun_extension_exists S \<phi> = (\<exists>B. \<forall>x\<in>S. B *\<^sub>V x = \<phi> x)"

lemma cblinfun_extension_existsI:
  assumes "\<And>x. x\<in>S \<Longrightarrow> B *\<^sub>V x = \<phi> x"
  shows "cblinfun_extension_exists S \<phi>"
  using assms cblinfun_extension_exists_def by blast

lemma cblinfun_extension_exists_finite_dim:
  fixes \<phi>::"'a::{complex_normed_vector,cfinite_dim} \<Rightarrow> 'b::complex_normed_vector"
  assumes "cindependent S"
    and "cspan S = UNIV"
  shows "cblinfun_extension_exists S \<phi>"
proof-
  define f::"'a \<Rightarrow> 'b"
    where "f = complex_vector.construct S \<phi>"
  have "clinear f"
    by (simp add: complex_vector.linear_construct assms linear_construct f_def)
  have "bounded_clinear f"
    using \<open>clinear f\<close> assms by auto
  then obtain B::"'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
    where "B *\<^sub>V x = f x" for x
    using cblinfun_apply_cases by blast
  have "B *\<^sub>V x = \<phi> x"
    if c1: "x\<in>S"
    for x
  proof-
    have "B *\<^sub>V x = f x"
      by (simp add: \<open>\<And>x. B *\<^sub>V x = f x\<close>)
    also have "\<dots> = \<phi> x"
      using assms complex_vector.construct_basis f_def that
      by (simp add: complex_vector.construct_basis)
    finally show?thesis by blast
  qed
  thus ?thesis
    unfolding cblinfun_extension_exists_def
    by blast
qed

lemma cblinfun_extension_apply:
  assumes "cblinfun_extension_exists S f"
    and "v \<in> S"
  shows "(cblinfun_extension S f) *\<^sub>V v = f v"
  by (smt assms cblinfun_extension_def cblinfun_extension_exists_def tfl_some)

lemma
  fixes f :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::cbanach\<close>
  assumes \<open>csubspace S\<close>
  assumes \<open>closure S = UNIV\<close>
  assumes f_add: \<open>\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> f (x + y) = f x + f y\<close>
  assumes f_scale: \<open>\<And>c x y. x \<in> S \<Longrightarrow> f (c *\<^sub>C x) = c *\<^sub>C f x\<close>
  assumes bounded: \<open>\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> B * norm x\<close>
  shows cblinfun_extension_exists_bounded_dense: \<open>cblinfun_extension_exists S f\<close>
    and cblinfun_extension_norm_bounded_dense: \<open>B \<ge> 0 \<Longrightarrow> norm (cblinfun_extension S f) \<le> B\<close>
proof -
  define B' where \<open>B' = (if B\<le>0 then 1 else B)\<close>
  then have bounded': \<open>\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> B' * norm x\<close>
    using bounded by (metis mult_1 mult_le_0_iff norm_ge_zero order_trans)
  have \<open>B' > 0\<close>
    by (simp add: B'_def)

  have \<open>\<exists>xi. (xi \<longlonglongrightarrow> x) \<and> (\<forall>i. xi i \<in> S)\<close> for x
    using assms(2) closure_sequential by blast
  then obtain seq :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close> where seq_lim: \<open>seq x \<longlonglongrightarrow> x\<close> and seq_S: \<open>seq x i \<in> S\<close> for x i
    apply (atomize_elim, subst all_conj_distrib[symmetric])
    apply (rule choice)
    by auto
  define g where \<open>g x = lim (\<lambda>i. f (seq x i))\<close> for x
  have \<open>Cauchy (\<lambda>i. f (seq x i))\<close> for x
  proof (rule CauchyI)
    fix e :: real assume \<open>e > 0\<close>
    have \<open>Cauchy (seq x)\<close>
      using LIMSEQ_imp_Cauchy seq_lim by blast
    then obtain M where less_eB: \<open>norm (seq x m - seq x n) < e/B'\<close> if \<open>n \<ge> M\<close> and \<open>m \<ge> M\<close> for n m
      by atomize_elim (meson CauchyD \<open>0 < B'\<close> \<open>0 < e\<close> linordered_field_class.divide_pos_pos)
    have \<open>norm (f (seq x m) - f (seq x n)) < e\<close> if \<open>n \<ge> M\<close> and \<open>m \<ge> M\<close> for n m
    proof -
      have \<open>norm (f (seq x m) - f (seq x n)) = norm (f (seq x m - seq x n))\<close>
        using f_add f_scale seq_S
        by (metis add_diff_cancel assms(1) complex_vector.subspace_diff diff_add_cancel)
      also have \<open>\<dots> \<le> B' * norm (seq x m - seq x n)\<close>
        apply (rule bounded')
        by (simp add: assms(1) complex_vector.subspace_diff seq_S)
      also from less_eB have \<open>\<dots> < B' * (e/B')\<close>
        by (meson \<open>0 < B'\<close> linordered_semiring_strict_class.mult_strict_left_mono that)
      also have \<open>\<dots> \<le> e\<close>
        using \<open>0 < B'\<close> by auto
      finally show ?thesis
        by -
    qed
    then show \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (f (seq x m) - f (seq x n)) < e\<close>
      by auto
  qed
  then have f_seq_lim: \<open>(\<lambda>i. f (seq x i)) \<longlonglongrightarrow> g x\<close> for x
    by (simp add: Cauchy_convergent_iff convergent_LIMSEQ_iff g_def)
  have f_xi_lim: \<open>(\<lambda>i. f (xi i)) \<longlonglongrightarrow> g x\<close> if \<open>xi \<longlonglongrightarrow> x\<close> and \<open>\<And>i. xi i \<in> S\<close> for xi x
  proof -
    from seq_lim that
    have \<open>(\<lambda>i. B' * norm (xi i - seq x i)) \<longlonglongrightarrow> 0\<close>
      by (metis (no_types) \<open>0 < B'\<close> cancel_comm_monoid_add_class.diff_cancel norm_not_less_zero norm_zero tendsto_diff tendsto_norm_zero_iff tendsto_zero_mult_left_iff)
    then have \<open>(\<lambda>i. f (xi i + (-1) *\<^sub>C seq x i)) \<longlonglongrightarrow> 0\<close>
      apply (rule Lim_null_comparison[rotated])
      using bounded' by (simp add: assms(1) complex_vector.subspace_diff seq_S that(2))
    then have \<open>(\<lambda>i. f (xi i) - f (seq x i)) \<longlonglongrightarrow> 0\<close>
      apply (subst (asm) f_add)
        apply (auto simp: that \<open>csubspace S\<close> complex_vector.subspace_neg seq_S)[2]
      apply (subst (asm) f_scale)
      by (auto simp: that \<open>csubspace S\<close> complex_vector.subspace_neg seq_S)
    then show \<open>(\<lambda>i. f (xi i)) \<longlonglongrightarrow> g x\<close>
      using Lim_transform f_seq_lim by fastforce
  qed
  have g_add: \<open>g (x + y) = g x + g y\<close> for x y
  proof -
    obtain xi :: \<open>nat \<Rightarrow> 'a\<close> where \<open>xi \<longlonglongrightarrow> x\<close> and \<open>xi i \<in> S\<close> for i
      using seq_S seq_lim by auto
    obtain yi :: \<open>nat \<Rightarrow> 'a\<close> where \<open>yi \<longlonglongrightarrow> y\<close> and \<open>yi i \<in> S\<close> for i
      using seq_S seq_lim by auto
    have \<open>(\<lambda>i. xi i + yi i) \<longlonglongrightarrow> x + y\<close>
      using \<open>xi \<longlonglongrightarrow> x\<close> \<open>yi \<longlonglongrightarrow> y\<close> tendsto_add by blast
    then have lim1: \<open>(\<lambda>i. f (xi i + yi i)) \<longlonglongrightarrow> g (x + y)\<close>
      by (simp add: \<open>\<And>i. xi i \<in> S\<close> \<open>\<And>i. yi i \<in> S\<close> assms(1) complex_vector.subspace_add f_xi_lim)
    have \<open>(\<lambda>i. f (xi i + yi i)) = (\<lambda>i. f (xi i) + f (yi i))\<close>
      by (simp add: \<open>\<And>i. xi i \<in> S\<close> \<open>\<And>i. yi i \<in> S\<close> f_add)
    also have \<open>\<dots> \<longlonglongrightarrow> g x + g y\<close>
      by (simp add: \<open>\<And>i. xi i \<in> S\<close> \<open>\<And>i. yi i \<in> S\<close> \<open>xi \<longlonglongrightarrow> x\<close> \<open>yi \<longlonglongrightarrow> y\<close> f_xi_lim tendsto_add)
    finally show ?thesis
      using lim1 LIMSEQ_unique by blast
  qed
  have g_scale: \<open>g (c *\<^sub>C x) = c *\<^sub>C g x\<close> for c x
  proof -
    obtain xi :: \<open>nat \<Rightarrow> 'a\<close> where \<open>xi \<longlonglongrightarrow> x\<close> and \<open>xi i \<in> S\<close> for i
      using seq_S seq_lim by auto
    have \<open>(\<lambda>i. c *\<^sub>C xi i) \<longlonglongrightarrow> c *\<^sub>C x\<close>
      using \<open>xi \<longlonglongrightarrow> x\<close> bounded_clinear_scaleC_right clinear_continuous_at isCont_tendsto_compose by blast
    then have lim1: \<open>(\<lambda>i. f (c *\<^sub>C xi i)) \<longlonglongrightarrow> g (c *\<^sub>C x)\<close>
      by (simp add: \<open>\<And>i. xi i \<in> S\<close> assms(1) complex_vector.subspace_scale f_xi_lim)
    have \<open>(\<lambda>i. f (c *\<^sub>C xi i)) = (\<lambda>i. c *\<^sub>C f (xi i))\<close>
      by (simp add: \<open>\<And>i. xi i \<in> S\<close> f_scale)
    also have \<open>\<dots> \<longlonglongrightarrow> c *\<^sub>C g x\<close>
      using \<open>\<And>i. xi i \<in> S\<close> \<open>xi \<longlonglongrightarrow> x\<close> bounded_clinear_scaleC_right clinear_continuous_at f_xi_lim isCont_tendsto_compose by blast
    finally show ?thesis
      using lim1 LIMSEQ_unique by blast
  qed

  have [simp]: \<open>f x = g x\<close> if \<open>x \<in> S\<close> for x
  proof -
    have \<open>(\<lambda>_. x) \<longlonglongrightarrow> x\<close>
      by auto
    then have \<open>(\<lambda>_. f x) \<longlonglongrightarrow> g x\<close>
      using that by (rule f_xi_lim)
    then show \<open>f x = g x\<close>
      by (simp add: LIMSEQ_const_iff)
  qed

  have g_bounded: \<open>norm (g x) \<le> B' * norm x\<close> for x
  proof -
    obtain xi :: \<open>nat \<Rightarrow> 'a\<close> where \<open>xi \<longlonglongrightarrow> x\<close> and \<open>xi i \<in> S\<close> for i
      using seq_S seq_lim by auto
    then have \<open>(\<lambda>i. f (xi i)) \<longlonglongrightarrow> g x\<close>
      using f_xi_lim by presburger
    then have \<open>(\<lambda>i. norm (f (xi i))) \<longlonglongrightarrow> norm (g x)\<close>
      by (metis tendsto_norm)
    moreover have \<open>(\<lambda>i. B' * norm (xi i)) \<longlonglongrightarrow> B' * norm x\<close>
      by (simp add: \<open>xi \<longlonglongrightarrow> x\<close> tendsto_mult_left tendsto_norm)
    ultimately show \<open>norm (g x) \<le> B' * norm x\<close>
      apply (rule lim_mono[rotated])
      using bounded' using \<open>xi _ \<in> S\<close> by blast
  qed

  have \<open>bounded_clinear g\<close>
    using g_add g_scale apply (rule bounded_clinearI[where K=B'])
    using g_bounded by (simp add: ordered_field_class.sign_simps(5))
  then have [simp]: \<open>CBlinfun g *\<^sub>V x = g x\<close> for x
    by (subst CBlinfun_inverse, auto)

  show \<open>cblinfun_extension_exists S f\<close>
    apply (rule cblinfun_extension_existsI[where B=\<open>CBlinfun g\<close>])
    by auto

  then have \<open>cblinfun_extension S f *\<^sub>V \<psi> = CBlinfun g *\<^sub>V \<psi>\<close> if \<open>\<psi> \<in> S\<close> for \<psi>
    by (simp add: cblinfun_extension_apply that)

  then have ext_is_g: \<open>(*\<^sub>V) (cblinfun_extension S f) = g\<close>
    apply (rule_tac ext)
    apply (rule on_closure_eqI[where S=S])
    using  \<open>closure S = UNIV\<close> \<open>bounded_clinear g\<close>
    by (auto simp add: continuous_at_imp_continuous_on clinear_continuous_within)

  show \<open>norm (cblinfun_extension S f) \<le> B\<close> if \<open>B \<ge> 0\<close>
  proof (cases \<open>B > 0\<close>)
    case True
    then have \<open>B = B'\<close>
      unfolding B'_def
      by auto
    moreover have *: \<open>norm (cblinfun_extension S f) \<le> B'\<close>
      by (metis ext_is_g \<open>0 < B'\<close> g_bounded norm_cblinfun_bound order_le_less)
    ultimately show ?thesis
      by simp
  next
    case False
    with bounded have \<open>f x = 0\<close> if \<open>x \<in> S\<close> for x
      by (smt (verit) mult_nonpos_nonneg norm_ge_zero norm_le_zero_iff that)
    then have \<open>g x = (\<lambda>_. 0) x\<close> if \<open>x \<in> S\<close> for x
      using that by simp
    then have \<open>g x = 0\<close> for x
      apply (rule on_closure_eqI[where S=S])
      using \<open>closure S = UNIV\<close> \<open>bounded_clinear g\<close>
      by (auto simp add: continuous_at_imp_continuous_on clinear_continuous_within)
    with ext_is_g have \<open>cblinfun_extension S f = 0\<close>
      by (simp add: cblinfun_eqI)
    then show ?thesis
      using that by simp
  qed
qed

lemma cblinfun_extension_cong:
  assumes \<open>cspan A = cspan B\<close>
  assumes \<open>B \<subseteq> A\<close>
  assumes fg: \<open>\<And>x. x\<in>B \<Longrightarrow> f x = g x\<close>
  assumes \<open>cblinfun_extension_exists A f\<close>
  shows \<open>cblinfun_extension A f = cblinfun_extension B g\<close>
proof -
  from \<open>cblinfun_extension_exists A f\<close> fg \<open>B \<subseteq> A\<close>
  have \<open>cblinfun_extension_exists B g\<close>
    by (metis assms(2) cblinfun_extension_exists_def subset_eq)

  have \<open>(\<forall>x\<in>A. C *\<^sub>V x = f x) \<longleftrightarrow> (\<forall>x\<in>B. C *\<^sub>V x = f x)\<close> for C
    by (smt (verit, ccfv_SIG) assms(1) assms(2) assms(4) cblinfun_eq_on_span cblinfun_extension_exists_def complex_vector.span_eq subset_iff)
  also from fg have \<open>\<dots> C \<longleftrightarrow> (\<forall>x\<in>B. C *\<^sub>V x = g x)\<close> for C
    by auto
  finally show \<open>cblinfun_extension A f = cblinfun_extension B g\<close>
    unfolding cblinfun_extension_def
    by auto
qed

lemma
  fixes f :: \<open>'a::complex_inner \<Rightarrow> 'b::chilbert_space\<close> and S 
  assumes \<open>is_ortho_set S\<close> and \<open>closure (cspan S) = UNIV\<close>
  assumes ortho_f: \<open>\<And>x y. x\<in>S \<Longrightarrow> y\<in>S \<Longrightarrow> x\<noteq>y \<Longrightarrow> is_orthogonal (f x) (f y)\<close>
  assumes bounded: \<open>\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> B * norm x\<close>
  shows cblinfun_extension_exists_ortho: \<open>cblinfun_extension_exists S f\<close>
    and cblinfun_extension_exists_ortho_norm: \<open>B \<ge> 0 \<Longrightarrow> norm (cblinfun_extension S f) \<le> B\<close>
proof -
  define g where \<open>g = cconstruct S f\<close>
  have \<open>cindependent S\<close>
    using assms(1) is_ortho_set_cindependent by blast
  have g_f: \<open>g x = f x\<close> if \<open>x\<in>S\<close> for x
    unfolding g_def using \<open>cindependent S\<close> that by (rule complex_vector.construct_basis)
  have [simp]: \<open>clinear g\<close>
    unfolding g_def using \<open>cindependent S\<close> by (rule complex_vector.linear_construct)
  then have g_add: \<open>g (x + y) = g x + g y\<close> if \<open>x \<in> cspan S\<close> and \<open>y \<in> cspan S\<close> for x y
    using clinear_iff by blast
  from \<open>clinear g\<close> have g_scale: \<open>g (c *\<^sub>C x) = c *\<^sub>C g x\<close> if \<open>x \<in> cspan S\<close> for x c
    by (simp add: complex_vector.linear_scale)
  moreover have g_bounded: \<open>norm (g x) \<le> abs B * norm x\<close> if \<open>x \<in> cspan S\<close> for x
  proof -
    from that obtain t r where x_sum: \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close> and \<open>finite t\<close> and \<open>t \<subseteq> S\<close>
      unfolding complex_vector.span_explicit by auto
    have \<open>(norm (g x))\<^sup>2 = (norm (\<Sum>a\<in>t. r a *\<^sub>C g a))\<^sup>2\<close>
      by (simp add: x_sum complex_vector.linear_sum clinear.scaleC)
    also have \<open>\<dots> = (norm (\<Sum>a\<in>t. r a *\<^sub>C f a))\<^sup>2\<close>
      by (smt (verit) \<open>t \<subseteq> S\<close> g_f in_mono sum.cong)
    also have \<open>\<dots> = (\<Sum>a\<in>t. (norm (r a *\<^sub>C f a))\<^sup>2)\<close>
      using _ \<open>finite t\<close> apply (rule pythagorean_theorem_sum)
      using \<open>t \<subseteq> S\<close> ortho_f in_mono by fastforce
    also have \<open>\<dots> = (\<Sum>a\<in>t. (cmod (r a) * norm (f a))\<^sup>2)\<close>
      by simp
    also have \<open>\<dots> \<le> (\<Sum>a\<in>t. (cmod (r a) * B * norm a)\<^sup>2)\<close>
      apply (rule sum_mono)
      by (metis \<open>t \<subseteq> S\<close> assms(4) in_mono mult_left_mono mult_nonneg_nonneg norm_ge_zero power_mono vector_space_over_itself.scale_scale)
    also have \<open>\<dots> = B\<^sup>2 * (\<Sum>a\<in>t. (norm (r a *\<^sub>C a))\<^sup>2)\<close>
      by (simp add: sum_distrib_left mult.commute vector_space_over_itself.scale_left_commute flip: power_mult_distrib)
    also have \<open>\<dots> = B\<^sup>2 * (norm (\<Sum>a\<in>t. (r a *\<^sub>C a)))\<^sup>2\<close>
      apply (subst pythagorean_theorem_sum)
      using \<open>finite t\<close> by auto (meson \<open>t \<subseteq> S\<close> assms(1) is_ortho_set_def subsetD)
    also have \<open>\<dots> = (abs B * norm x)\<^sup>2\<close>
      by (simp add: power_mult_distrib x_sum)
    finally show \<open>norm (g x) \<le> abs B * norm x\<close>
      by auto
  qed
  
  from g_add g_scale g_bounded
  have extg_exists: \<open>cblinfun_extension_exists (cspan S) g\<close>
    apply (rule_tac cblinfun_extension_exists_bounded_dense[where B=\<open>abs B\<close>])
    using \<open>closure (cspan S) = UNIV\<close> by auto

  then show \<open>cblinfun_extension_exists S f\<close>
    by (metis (mono_tags, opaque_lifting) g_f cblinfun_extension_apply cblinfun_extension_existsI complex_vector.span_base)

  have norm_extg: \<open>norm (cblinfun_extension (cspan S) g) \<le> B\<close> if \<open>B \<ge> 0\<close>
    apply (rule cblinfun_extension_norm_bounded_dense)
    using g_add g_scale g_bounded \<open>closure (cspan S) = UNIV\<close> that by auto

  have extg_extf: \<open>cblinfun_extension (cspan S) g = cblinfun_extension S f\<close>
    apply (rule cblinfun_extension_cong)
    by (auto simp add: complex_vector.span_base g_f extg_exists)

  from norm_extg extg_extf
  show \<open>norm (cblinfun_extension S f) \<le> B\<close> if \<open>B \<ge> 0\<close>
    using that by simp
qed


lemma cblinfun_extension_exists_proj:
  fixes f :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::cbanach\<close>
  assumes \<open>csubspace S\<close>
  assumes ex_P: \<open>\<exists>P :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a. is_Proj P \<and> range P = closure S\<close>
  assumes f_add: \<open>\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> f (x + y) = f x + f y\<close>
  assumes f_scale: \<open>\<And>c x y. x \<in> S \<Longrightarrow> f (c *\<^sub>C x) = c *\<^sub>C f x\<close>
  assumes bounded: \<open>\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> B * norm x\<close>
  shows \<open>cblinfun_extension_exists S f\<close>
    \<comment> \<open>We cannot give a statement about the norm. While there is an extension with norm \<^term>\<open>B\<close>,
        there is no guarantee that \<^term>\<open>cblinfun_extension S f\<close> returns that specific extension since
        the extension is only determined on \<^term>\<open>ccspan S\<close>.\<close>
proof (cases \<open>B \<ge> 0\<close>)
  case True
  note True[simp]
  obtain P :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> where P_proj: \<open>is_Proj P\<close> and P_im: \<open>range P = closure S\<close>
    using ex_P by blast 
  define f' S' where \<open>f' \<psi> = f (P \<psi>)\<close> and \<open>S' = S + space_as_set (kernel P)\<close> for \<psi>
  have PS': \<open>P *\<^sub>V x \<in> S\<close> if \<open>x \<in> S'\<close> for x
  proof -
    obtain x1 x2 where x12: \<open>x = x1 + x2\<close> and x1: \<open>x1 \<in> S\<close> and x2: \<open>x2 \<in> space_as_set (kernel P)\<close>
      using that  S'_def \<open>x \<in> S'\<close> set_plus_elim by blast
    have \<open>P *\<^sub>V x = P *\<^sub>V x1\<close>
      using x2 by (simp add: x12 cblinfun.add_right kernel_memberD)
    also have \<open>\<dots> = x1\<close>
      by (metis (no_types, opaque_lifting) P_im P_proj cblinfun_apply_cblinfun_compose closure_insert image_iff insertI1 insert_absorb is_Proj_idempotent x1)
    also have \<open>\<dots> \<in> S\<close>
      by (fact x1)
    finally show ?thesis
      by -
  qed
  have SS': \<open>S \<subseteq> S'\<close>
    by (metis S'_def ordered_field_class.sign_simps(2) set_zero_plus2 zero_space_as_set)

  have \<open>csubspace S'\<close>
    by (simp add: S'_def assms(1) csubspace_set_plus)
  moreover have \<open>closure S' = UNIV\<close>
  proof auto
    fix \<psi>
    have \<open>\<psi> = P \<psi> + (id - P) \<psi>\<close>
      by simp
    also have \<open>\<dots> \<in> closure S + space_as_set (kernel P)\<close>
      by (smt (verit) P_im P_proj calculation cblinfun.real.add_right eq_add_iff is_Proj_idempotent kernel_memberI rangeI set_plus_intro simp_a_oCL_b')
    also have \<open>\<dots> \<subseteq> closure (closure S + space_as_set (kernel P))\<close>
      using closure_subset by blast
    also have \<open>\<dots> = closure (S + space_as_set (kernel P))\<close>
      using closed_sum_closure_left closed_sum_def by blast
    also have \<open>\<dots> = closure S'\<close>
      using S'_def by fastforce
    finally show \<open>\<psi> \<in> closure S'\<close>
      by -
  qed

  moreover have \<open>f' (x + y) = f' x + f' y\<close> if \<open>x \<in> S'\<close> and \<open>y \<in> S'\<close> for x y
    using that by (auto simp: f'_def cblinfun.add_right f_add PS')
  moreover have \<open>f' (c *\<^sub>C x) = c *\<^sub>C f' x\<close> if \<open>x \<in> S'\<close> for c x
    using that by (auto simp: f'_def cblinfun.scaleC_right f_scale PS')
  moreover 
  have \<open>norm (f' x) \<le> (B * norm P) * norm x\<close> if \<open>x \<in> S'\<close> for x
  proof -
    have \<open>norm (f' x) \<le> B* norm (P x)\<close>
      by (auto simp: f'_def PS' bounded that)
    also have \<open>\<dots> \<le> B * norm P * norm x\<close>
      by (simp add: mult.assoc mult_left_mono norm_cblinfun)
    finally show ?thesis
      by auto
  qed

  ultimately have F_ex: \<open>cblinfun_extension_exists S' f'\<close>
    by (rule cblinfun_extension_exists_bounded_dense)
  define F where \<open>F = cblinfun_extension S' f'\<close>
  have \<open>F \<psi> = f \<psi>\<close> if \<open>\<psi> \<in> S\<close> for \<psi>
  proof -
    from F_ex that SS' have \<open>F \<psi> = f' \<psi>\<close>
      by (auto simp add: F_def cblinfun_extension_apply)
    also have \<open>\<dots> = f (P *\<^sub>V \<psi>)\<close>
      by (simp add: f'_def)
    also have \<open>\<dots> = f \<psi>\<close>
      using P_proj P_im
      apply (transfer fixing: \<psi> S f)
      by (metis closure_subset in_mono is_projection_on_fixes_image is_projection_on_image that)
    finally show ?thesis
      by -
  qed
  then show \<open>cblinfun_extension_exists S f\<close>
    using cblinfun_extension_exists_def by blast
next
  case False
  then have \<open>S \<subseteq> {0}\<close>
    using bounded by auto (meson norm_ge_zero norm_le_zero_iff order_trans zero_le_mult_iff)
  then show \<open>cblinfun_extension_exists S f\<close>
    apply (rule_tac cblinfun_extension_existsI[where B=0])
    apply auto
    using bounded by fastforce
qed

lemma cblinfun_extension_exists_hilbert:
  fixes f :: \<open>'a::chilbert_space \<Rightarrow> 'b::cbanach\<close>
  assumes \<open>csubspace S\<close>
  assumes f_add: \<open>\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> f (x + y) = f x + f y\<close>
  assumes f_scale: \<open>\<And>c x y. x \<in> S \<Longrightarrow> f (c *\<^sub>C x) = c *\<^sub>C f x\<close>
  assumes bounded: \<open>\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> B * norm x\<close>
  shows \<open>cblinfun_extension_exists S f\<close>
    \<comment> \<open>We cannot give a statement about the norm. While there is an extension with norm \<^term>\<open>B\<close>,
        there is no guarantee that \<^term>\<open>cblinfun_extension S f\<close> returns that specific extension since
        the extension is only determined on \<^term>\<open>ccspan S\<close>.\<close>
proof -
  have \<open>\<exists>P. is_Proj P \<and> range ((*\<^sub>V) P) = closure S\<close>
    apply (rule exI[of _ \<open>Proj (ccspan S)\<close>])
    apply (rule conjI)
     by simp (metis Proj_is_Proj Proj_range Proj_range_closed assms(1) cblinfun_image.rep_eq ccspan.rep_eq closure_closed complex_vector.span_eq_iff space_as_set_top)

  from assms(1) this assms(2-4)
  show ?thesis
    by (rule cblinfun_extension_exists_proj)
qed

lemma cblinfun_extension_exists_restrict:
  assumes \<open>B \<subseteq> A\<close>
  assumes \<open>\<And>x. x\<in>B \<Longrightarrow> f x = g x\<close>
  assumes \<open>cblinfun_extension_exists A f\<close>
  shows \<open>cblinfun_extension_exists B g\<close>
  by (metis assms cblinfun_extension_exists_def subset_eq)

subsection \<open>Bijections between different ONBs\<close>

text \<open>Some of the theorems here logically belong into \<^theory>\<open>Complex_Bounded_Operators.Complex_Inner_Product\<close>
  but the proof uses some concepts from the present theory.\<close>

lemma all_ortho_bases_same_card:
  \<comment> \<open>Follows \<^cite>\<open>conway2013course\<close>, Proposition 4.14\<close>
  fixes E F :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_ortho_set E\<close> \<open>is_ortho_set F\<close> \<open>ccspan E = \<top>\<close> \<open>ccspan F = \<top>\<close>
  shows \<open>\<exists>f. bij_betw f E F\<close>
proof -
  have \<open>|F| \<le>o |E|\<close> if \<open>infinite E\<close> and
    \<open>is_ortho_set E\<close> \<open>is_ortho_set F\<close> \<open>ccspan E = top\<close> \<open>ccspan F = top\<close> for E F :: \<open>'a set\<close>
  proof -
    define F' where \<open>F' e = {f\<in>F. \<not> is_orthogonal f e}\<close> for e
    have \<open>\<exists>e\<in>E. cinner f e \<noteq> 0\<close> if \<open>f \<in> F\<close> for f
    proof (rule ccontr, simp)
      assume \<open>\<forall>e\<in>E. is_orthogonal f e\<close>
      then have \<open>f \<in> orthogonal_complement E\<close>
        by (simp add: orthogonal_complementI)
      also have \<open>\<dots> = orthogonal_complement (closure (cspan E))\<close>
        using orthogonal_complement_of_closure orthogonal_complement_of_cspan by blast
      also have \<open>\<dots> = space_as_set (- ccspan E)\<close>
        by transfer simp
      also have \<open>\<dots> = space_as_set (- top)\<close>
        by (simp add: \<open>ccspan E = top\<close>)
      also have \<open>\<dots> = {0}\<close>
        by (auto simp add: top_ccsubspace.rep_eq uminus_ccsubspace.rep_eq)
      finally have \<open>f = 0\<close>
        by simp
      with \<open>f \<in> F\<close> \<open>is_ortho_set F\<close> show False
        by (simp add: is_onb_def is_ortho_set_def)
    qed
    then have F'_union: \<open>F = (\<Union>e\<in>E. F' e)\<close>
      unfolding F'_def by auto
    have \<open>countable (F' e)\<close> for e
    proof -
      have \<open>(\<Sum>f\<in>M. (cmod (cinner (sgn f) e))\<^sup>2) \<le> (norm e)\<^sup>2\<close> if \<open>finite M\<close> and \<open>M \<subseteq> F\<close> for M
      proof -
        have [simp]: \<open>is_ortho_set M\<close>
          using \<open>is_ortho_set F\<close> is_ortho_set_antimono that(2) by blast
        have [simp]: \<open>norm (sgn f) = 1\<close> if \<open>f \<in> M\<close> for f
          by (metis \<open>is_ortho_set M\<close> is_ortho_set_def norm_sgn that)
        have \<open>(\<Sum>f\<in>M. (cmod (cinner (sgn f) e))\<^sup>2) = (\<Sum>f\<in>M. (norm ((cinner (sgn f) e) *\<^sub>C sgn f))\<^sup>2)\<close>
          apply (rule sum.cong[OF refl])
          by simp
        also have \<open>\<dots> = (norm (\<Sum>f\<in>M. ((cinner (sgn f) e) *\<^sub>C sgn f)))\<^sup>2\<close>
          apply (rule pythagorean_theorem_sum[symmetric])
          using that by auto (meson \<open>is_ortho_set M\<close> is_ortho_set_def)
        also have \<open>\<dots> = (norm (\<Sum>f\<in>M. proj f e))\<^sup>2\<close>
          by (metis butterfly_apply butterfly_sgn_eq_proj)
        also have \<open>\<dots> = (norm (Proj (ccspan M) e))\<^sup>2\<close>
          apply (rule arg_cong[where f=\<open>\<lambda>x. (norm x)\<^sup>2\<close>])
          using \<open>finite M\<close> \<open>is_ortho_set M\<close> apply induction
           by simp (smt (verit, ccfv_threshold) Proj_orthog_ccspan_insert insertCI is_ortho_set_def plus_cblinfun.rep_eq sum.insert)
        also have \<open>\<dots> \<le> (norm (Proj (ccspan M)) * norm e)\<^sup>2\<close>
          by (auto simp: norm_cblinfun intro!: power_mono)
        also have \<open>\<dots> \<le> (norm e)\<^sup>2\<close>
          apply (rule power_mono)
           apply (metis norm_Proj_leq1 mult_left_le_one_le norm_ge_zero)
          by simp
        finally show ?thesis
          by -
      qed
      then have \<open>(\<lambda>f. (cmod (cinner (sgn f) e))\<^sup>2) abs_summable_on F\<close>
        apply (intro nonneg_bdd_above_summable_on bdd_aboveI)
        by auto
      then have \<open>countable {f \<in> F. (cmod (sgn f \<bullet>\<^sub>C e))\<^sup>2 \<noteq> 0}\<close>
        by (rule abs_summable_countable)
      then have \<open>countable {f \<in> F. \<not> is_orthogonal (sgn f) e}\<close>
        by force
      then have \<open>countable {f \<in> F. \<not> is_orthogonal f e}\<close>
        by force
      then show ?thesis
        unfolding F'_def by simp
    qed
    then have F'_leq: \<open>|F' e| \<le>o natLeq\<close> for e
      using countable_leq_natLeq by auto

    from F'_union have \<open>|F| \<le>o |Sigma E F'|\<close> (is \<open>_ \<le>o \<dots>\<close>)
      using card_of_UNION_Sigma by blast
    also have \<open>\<dots> \<le>o |E \<times> (UNIV::nat set)|\<close> (is \<open>_ \<le>o \<dots>\<close>)
      apply (rule card_of_Sigma_mono1)
      using F'_leq
      using card_of_nat ordIso_symmetric ordLeq_ordIso_trans by blast
    also have \<open>\<dots> =o |E| *c natLeq\<close> (is \<open>ordIso2 _ \<dots>\<close>)
      by (metis Field_card_of Field_natLeq card_of_ordIso_subst cprod_def)
    also have \<open>\<dots> =o |E|\<close>
      apply (rule card_prod_omega)
      using that by (simp add: cinfinite_def)
    finally show \<open>|F| \<le>o |E|\<close>
      by -
  qed
  then have infinite: \<open>|E| =o |F|\<close> if \<open>infinite E\<close> and \<open>infinite F\<close>
    by (simp add: assms ordIso_iff_ordLeq that(1) that(2))

  have \<open>|E| =o |F|\<close> if \<open>finite E\<close> and \<open>is_ortho_set E\<close> \<open>is_ortho_set F\<close> \<open>ccspan E = top\<close> \<open>ccspan F = top\<close>
    for E F :: \<open>'a set\<close>
  proof -
    have \<open>card E = card F\<close>
      using that 
      by (metis bij_betw_same_card ccspan.rep_eq closure_finite_cspan complex_vector.bij_if_span_eq_span_bases 
          complex_vector.independent_span_bound is_ortho_set_cindependent top_ccsubspace.rep_eq top_greatest)
    with \<open>finite E\<close> have \<open>finite F\<close>
      by (metis ccspan.rep_eq closure_finite_cspan complex_vector.independent_span_bound is_ortho_set_cindependent that(3) that(4) top_ccsubspace.rep_eq top_greatest)
    with \<open>card E = card F\<close> that show ?thesis
      apply (rule_tac finite_card_of_iff_card[THEN iffD2])
      by auto
  qed

  with infinite assms have \<open>|E| =o |F|\<close>
    by (meson ordIso_symmetric)

  then show ?thesis
    by (simp add: card_of_ordIso)
qed

lemma all_onbs_same_card:
  fixes E F :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_onb E\<close> \<open>is_onb F\<close>
  shows \<open>\<exists>f. bij_betw f E F\<close>
  apply (rule all_ortho_bases_same_card)
  using assms by (auto simp: is_onb_def)

definition bij_between_bases where \<open>bij_between_bases E F = (SOME f. bij_betw f E F)\<close> for E F :: \<open>'a::chilbert_space set\<close>

lemma bij_between_bases_bij:
  fixes E F :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_onb E\<close> \<open>is_onb F\<close>
  shows \<open>bij_betw (bij_between_bases E F) E F\<close>
  using all_onbs_same_card
  by (metis assms(1) assms(2) bij_between_bases_def someI)

definition unitary_between where \<open>unitary_between E F = cblinfun_extension E (bij_between_bases E F)\<close>

lemma unitary_between_apply:
  fixes E F :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_onb E\<close> \<open>is_onb F\<close> \<open>e \<in> E\<close>
  shows \<open>unitary_between E F *\<^sub>V e = bij_between_bases E F e\<close>
proof -
  from \<open>is_onb E\<close> \<open>is_onb F\<close>
  have EF: \<open>bij_between_bases E F e \<in> F\<close> if \<open>e \<in> E\<close> for e
    by (meson bij_betwE bij_between_bases_bij that)
  have ortho: \<open>is_orthogonal (bij_between_bases E F x) (bij_between_bases E F y)\<close> if \<open>x \<noteq> y\<close> and \<open>x \<in> E\<close> and \<open>y \<in> E\<close> for x y
    by (smt (verit, del_insts) assms(1) assms(2) bij_betw_iff_bijections bij_between_bases_bij is_onb_def is_ortho_set_def that(1) that(2) that(3))
  have spanE: \<open>closure (cspan E) = UNIV\<close>
    by (metis assms(1) ccspan.rep_eq is_onb_def top_ccsubspace.rep_eq)
  show ?thesis
    unfolding unitary_between_def
    apply (rule cblinfun_extension_apply)
     apply (rule cblinfun_extension_exists_ortho[where B=1])
    using assms EF ortho spanE
    by (auto simp: is_onb_def)
qed

lemma unitary_between_unitary:
  fixes E F :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_onb E\<close> \<open>is_onb F\<close>
  shows \<open>unitary (unitary_between E F)\<close>
proof -
  have \<open>(unitary_between E F *\<^sub>V b) \<bullet>\<^sub>C (unitary_between E F *\<^sub>V c) = b \<bullet>\<^sub>C c\<close> if \<open>b \<in> E\<close> and \<open>c \<in> E\<close> for b c
  proof (cases \<open>b = c\<close>)
    case True
    from \<open>is_onb E\<close> that have 1: \<open>b \<bullet>\<^sub>C b = 1\<close>
      using cnorm_eq_1 is_onb_def by blast
    from that have \<open>unitary_between E F *\<^sub>V b \<in> F\<close>
      by (metis assms(1) assms(2) bij_betw_apply bij_between_bases_bij unitary_between_apply)
    with \<open>is_onb F\<close> have 2: \<open>(unitary_between E F *\<^sub>V b) \<bullet>\<^sub>C (unitary_between E F *\<^sub>V b) = 1\<close>
      by (simp add: cnorm_eq_1 is_onb_def)
    from 1 2 True show ?thesis
      by simp
  next
    case False
    from \<open>is_onb E\<close> that have 1: \<open>b \<bullet>\<^sub>C c = 0\<close>
      by (simp add: False is_onb_def is_ortho_set_def)
    from that have inF: \<open>unitary_between E F *\<^sub>V b \<in> F\<close> \<open>unitary_between E F *\<^sub>V c \<in> F\<close>
      by (metis assms(1) assms(2) bij_betw_apply bij_between_bases_bij unitary_between_apply)+
    have neq: \<open>unitary_between E F *\<^sub>V b \<noteq> unitary_between E F *\<^sub>V c\<close>
      by (metis (no_types, lifting) False assms(1) assms(2) bij_betw_iff_bijections bij_between_bases_bij that(1) that(2) unitary_between_apply)
    from inF neq \<open>is_onb F\<close> have 2: \<open>(unitary_between E F *\<^sub>V b) \<bullet>\<^sub>C (unitary_between E F *\<^sub>V c) = 0\<close>
      by (simp add: is_onb_def is_ortho_set_def)
    from 1 2 show ?thesis
      by simp
  qed
  then have iso: \<open>isometry (unitary_between E F)\<close>
    apply (rule_tac orthogonal_on_basis_is_isometry[where B=E])
    using assms(1) is_onb_def by auto
  have \<open>unitary_between E F *\<^sub>S top = unitary_between E F *\<^sub>S ccspan E\<close>
    by (metis assms(1) is_onb_def)
  also have \<open>\<dots> \<ge> ccspan (unitary_between E F ` E)\<close> (is \<open>_ \<ge> \<dots>\<close>)
    by (simp add: cblinfun_image_ccspan)
  also have \<open>\<dots> = ccspan (bij_between_bases E F ` E)\<close>
    by (metis assms(1) assms(2) image_cong unitary_between_apply)
  also have \<open>\<dots> = ccspan F\<close>
    by (metis assms(1) assms(2) bij_betw_imp_surj_on bij_between_bases_bij)
  also have \<open>\<dots> = top\<close>
    using assms(2) is_onb_def by blast
  finally have surj: \<open>unitary_between E F *\<^sub>S top = top\<close>
    by (simp add: top.extremum_unique)
  from iso surj show ?thesis
    by (rule surj_isometry_is_unitary)
qed


subsection \<open>Notation\<close>

bundle cblinfun_notation begin
notation cblinfun_compose (infixl "o\<^sub>C\<^sub>L" 67)
notation cblinfun_apply (infixr "*\<^sub>V" 70)
notation cblinfun_image (infixr "*\<^sub>S" 70)
notation adj ("_*" [99] 100)
type_notation cblinfun ("(_ \<Rightarrow>\<^sub>C\<^sub>L /_)" [22, 21] 21)
end

bundle no_cblinfun_notation begin
no_notation cblinfun_compose (infixl "o\<^sub>C\<^sub>L" 67)
no_notation cblinfun_apply (infixr "*\<^sub>V" 70)
no_notation cblinfun_image (infixr "*\<^sub>S" 70)
no_notation adj ("_*" [99] 100)
no_type_notation cblinfun ("(_ \<Rightarrow>\<^sub>C\<^sub>L /_)" [22, 21] 21)
end

unbundle no_cblinfun_notation
unbundle no_lattice_syntax

end
