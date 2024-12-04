section \<open>\<open>Von_Neumann_Algebras\<close> -- Von Neumann algebras and the double commutant theorem\<close>

theory Von_Neumann_Algebras
  imports Hilbert_Space_Tensor_Product
begin

subsection \<open>Commutants\<close>

definition \<open>commutant F = {x. \<forall>y\<in>F. x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x}\<close>

lemma sandwich_unitary_commutant: 
  fixes U :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes [simp]: \<open>unitary U\<close>
  shows \<open>sandwich U ` commutant X = commutant (sandwich U ` X)\<close>
proof (rule Set.set_eqI)
  fix x
  let ?comm = \<open>\<lambda>a b. a o\<^sub>C\<^sub>L b = b o\<^sub>C\<^sub>L a\<close>
  have \<open>x \<in> sandwich U ` commutant X \<longleftrightarrow> sandwich (U*) x \<in> commutant X\<close>
    apply (subst inj_image_mem_iff[symmetric, where f=\<open>sandwich (U*)\<close>])
    by (auto intro!: inj_sandwich_isometry simp: image_image
        simp flip: cblinfun_apply_cblinfun_compose sandwich_compose)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>y\<in>X. ?comm (sandwich (U*) x) y)\<close>
    by (simp add: commutant_def)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>y\<in>X. ?comm x (sandwich U y))\<close>
    apply (rule ball_cong, simp)
    apply (simp add: sandwich_apply)
    by (smt (verit) assms cblinfun_assoc_left(1) cblinfun_compose_id_left cblinfun_compose_id_right unitaryD1 unitaryD2)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>y\<in>sandwich U ` X. ?comm x y)\<close>
  by fast
  also have \<open>\<dots> \<longleftrightarrow> x \<in> commutant (sandwich U ` X)\<close>
    by (simp add: commutant_def)
  finally show \<open>(x \<in> (*\<^sub>V) (sandwich U) ` commutant X) \<longleftrightarrow> (x \<in> commutant ((*\<^sub>V) (sandwich U) ` X))\<close>
    by -
qed

lemma commutant_tensor1: \<open>commutant (range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun)) = range (\<lambda>b. id_cblinfun \<otimes>\<^sub>o b)\<close>
proof (rule Set.set_eqI, rule iffI)
  fix x :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close>
  fix \<gamma> :: 'a
  assume \<open>x \<in> commutant (range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun))\<close>
  then have comm: \<open>(a \<otimes>\<^sub>o id_cblinfun) *\<^sub>V x *\<^sub>V \<psi> = x *\<^sub>V (a \<otimes>\<^sub>o id_cblinfun) *\<^sub>V \<psi>\<close> for a \<psi>
    by (metis (mono_tags, lifting) commutant_def mem_Collect_eq rangeI cblinfun_apply_cblinfun_compose)

  define op where \<open>op = classical_operator (\<lambda>i. Some (\<gamma>,i::'b))\<close>
  have [simp]: \<open>classical_operator_exists (\<lambda>i. Some (\<gamma>,i))\<close>
    apply (rule classical_operator_exists_inj)
    using inj_map_def by blast
  define x' where \<open>x' = op* o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L op\<close>
  have x': \<open>cinner (ket j) (x' *\<^sub>V ket l) = cinner (ket (\<gamma>,j)) (x *\<^sub>V ket (\<gamma>,l))\<close> for j l
    by (simp add: x'_def op_def classical_operator_ket cinner_adj_right)

  have \<open>cinner (ket (i,j)) (x *\<^sub>V ket (k,l)) = cinner (ket (i,j)) ((id_cblinfun \<otimes>\<^sub>o x') *\<^sub>V ket (k,l))\<close> for i j k l
  proof -
    have \<open>cinner (ket (i,j)) (x *\<^sub>V ket (k,l))
        = cinner ((butterfly (ket i) (ket \<gamma>) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,j)) (x *\<^sub>V (butterfly (ket k) (ket \<gamma>) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,l))\<close>
      by (auto simp: tensor_op_ket tensor_ell2_ket)
    also have \<open>\<dots> = cinner (ket (\<gamma>,j)) ((butterfly (ket \<gamma>) (ket i) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V x *\<^sub>V (butterfly (ket k) (ket \<gamma>) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,l))\<close>
      by (metis (no_types, lifting) cinner_adj_left butterfly_adjoint id_cblinfun_adjoint tensor_op_adjoint)
    also have \<open>\<dots> = cinner (ket (\<gamma>,j)) (x *\<^sub>V (butterfly (ket \<gamma>) (ket i) \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L butterfly (ket k) (ket \<gamma>) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (\<gamma>,l))\<close>
      unfolding comm by (simp add: cblinfun_apply_cblinfun_compose)
    also have \<open>\<dots> = cinner (ket i) (ket k) * cinner (ket (\<gamma>,j)) (x *\<^sub>V ket (\<gamma>,l))\<close>
      by (simp add: comp_tensor_op tensor_op_ket tensor_op_scaleC_left cinner_ket tensor_ell2_ket)
    also have \<open>\<dots> = cinner (ket i) (ket k) * cinner (ket j) (x' *\<^sub>V ket l)\<close>
      by (simp add: x')
    also have \<open>\<dots> = cinner (ket (i,j)) ((id_cblinfun \<otimes>\<^sub>o x') *\<^sub>V ket (k,l))\<close>
      apply (simp add: tensor_op_ket)
      by (simp flip: tensor_ell2_ket)
    finally show ?thesis by -
  qed
  then have \<open>x = (id_cblinfun \<otimes>\<^sub>o x')\<close>
    by (auto intro!: equal_ket cinner_ket_eqI)
  then show \<open>x \<in> range (\<lambda>b. id_cblinfun \<otimes>\<^sub>o b)\<close>
    by auto
next
  fix x :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close>
  assume \<open>x \<in> range (\<lambda>b. id_cblinfun \<otimes>\<^sub>o b)\<close>
  then obtain b where x: \<open>x = id_cblinfun \<otimes>\<^sub>o b\<close>
    by auto
  then show \<open>x \<in> commutant (range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun))\<close>
    by (auto simp: x commutant_def comp_tensor_op)
qed

lemma csubspace_commutant[simp]: \<open>csubspace (commutant X)\<close>
  by (auto simp add: complex_vector.subspace_def commutant_def cblinfun_compose_add_right cblinfun_compose_add_left)

lemma closed_commutant[simp]: \<open>closed (commutant X)\<close>
proof (subst closed_sequential_limits, intro allI impI, erule conjE)
  fix s :: \<open>nat \<Rightarrow> _\<close> and l 
  assume s_comm: \<open>\<forall>n. s n \<in> commutant X\<close>
  assume \<open>s \<longlonglongrightarrow> l\<close>
  have \<open>l o\<^sub>C\<^sub>L x - x o\<^sub>C\<^sub>L l = 0\<close> if \<open>x \<in> X\<close> for x
  proof -
    from \<open>s \<longlonglongrightarrow> l\<close>
    have \<open>(\<lambda>n. s n o\<^sub>C\<^sub>L x - x o\<^sub>C\<^sub>L s n) \<longlonglongrightarrow> l o\<^sub>C\<^sub>L x - x o\<^sub>C\<^sub>L l\<close>
      apply (rule isCont_tendsto_compose[rotated])
      by (intro continuous_intros)
    then have \<open>(\<lambda>_. 0) \<longlonglongrightarrow> l o\<^sub>C\<^sub>L x - x o\<^sub>C\<^sub>L l\<close>
      using s_comm that by (auto simp add: commutant_def)
    then show ?thesis
      by (simp add: LIMSEQ_const_iff that)
  qed
  then show \<open>l \<in> commutant X\<close>
    by (simp add: commutant_def)
qed

lemma closed_csubspace_commutant[simp]: \<open>closed_csubspace (commutant X)\<close>
  apply (rule closed_csubspace.intro) by simp_all

lemma commutant_mult: \<open>a o\<^sub>C\<^sub>L b \<in> commutant X\<close> if \<open>a \<in> commutant X\<close> and \<open>b \<in> commutant X\<close>
  using that 
  apply (auto simp: commutant_def cblinfun_compose_assoc)
  by (simp flip: cblinfun_compose_assoc)

lemma double_commutant_grows[simp]: \<open>X \<subseteq> commutant (commutant X)\<close>
  by (auto simp add: commutant_def)

lemma commutant_antimono: \<open>X \<subseteq> Y \<Longrightarrow> commutant X \<supseteq> commutant Y\<close>
  by (auto simp add: commutant_def)




lemma triple_commutant[simp]: \<open>commutant (commutant (commutant X)) = commutant X\<close>
  by (auto simp: commutant_def)

lemma commutant_adj: \<open>adj ` commutant X = commutant (adj ` X)\<close>
  apply (auto intro!: image_eqI double_adj[symmetric] simp: commutant_def simp flip: adj_cblinfun_compose)
  by (metis adj_cblinfun_compose double_adj)

lemma commutant_empty[simp]: \<open>commutant {} = UNIV\<close>
  by (simp add: commutant_def)


lemma commutant_weak_star_closed[simp]: \<open>closedin weak_star_topology (commutant X)\<close>
proof -
  have comm_inter: \<open>commutant X = (\<Inter>x\<in>X. commutant {x})\<close>
    by (auto simp: commutant_def)
  have comm_x: \<open>commutant {x} = (\<lambda>y. x o\<^sub>C\<^sub>L y - y o\<^sub>C\<^sub>L x) -` {0}\<close> for x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    by (auto simp add: commutant_def vimage_def)
  have cont: \<open>continuous_map weak_star_topology weak_star_topology (\<lambda>y. x o\<^sub>C\<^sub>L y - y o\<^sub>C\<^sub>L x)\<close> for x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    apply (rule continuous_intros)
    by (simp_all add: continuous_map_left_comp_weak_star continuous_map_right_comp_weak_star)
  have \<open>closedin weak_star_topology ((\<lambda>y. x o\<^sub>C\<^sub>L y - y o\<^sub>C\<^sub>L x) -` {0})\<close> for x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    using closedin_vimage[where U=\<open>weak_star_topology\<close> and S=\<open>{0}\<close> and T=weak_star_topology]
    using cont by (auto simp add: closedin_Hausdorff_singleton)
  then show ?thesis
    apply (cases \<open>X = {}\<close>)
    using closedin_topspace[of weak_star_topology]
    by (auto simp add: comm_inter comm_x)
qed

lemma cspan_in_double_commutant: \<open>cspan X \<subseteq> commutant (commutant X)\<close>
  by (simp add: complex_vector.span_minimal)

lemma weak_star_closure_in_double_commutant: \<open>weak_star_topology closure_of X \<subseteq> commutant (commutant X)\<close>
  by (simp add: closure_of_minimal)

lemma weak_star_closure_cspan_in_double_commutant: \<open>weak_star_topology closure_of cspan X \<subseteq> commutant (commutant X)\<close>
  by (simp add: closure_of_minimal cspan_in_double_commutant)


lemma commutant_memberI:
  assumes \<open>\<And>y. y \<in> X \<Longrightarrow> x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x\<close>
  shows \<open>x \<in> commutant X\<close>
  using assms by (simp add: commutant_def)

lemma commutant_sot_closed: \<open>closedin cstrong_operator_topology (commutant A)\<close>
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Exercise IX.6.2\<close>
proof (cases \<open>A = {}\<close>)
  case True
  then show ?thesis
    apply simp
    by (metis closedin_topspace cstrong_operator_topology_topspace)
next
  case False
  have closed_a: \<open>closedin cstrong_operator_topology (commutant {a})\<close> for a :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  proof -
    have comm_a: \<open>commutant {a} = (\<lambda>b. a o\<^sub>C\<^sub>L b - b o\<^sub>C\<^sub>L a) -` {0}\<close>
      by (auto simp: commutant_def)
    have closed_0: \<open>closedin cstrong_operator_topology {0}\<close>
      apply (rule closedin_Hausdorff_singleton)
      by simp_all
    have cont: \<open>continuous_map cstrong_operator_topology cstrong_operator_topology (\<lambda>b. a o\<^sub>C\<^sub>L b - b o\<^sub>C\<^sub>L a)\<close>
      by (intro continuous_intros continuous_map_left_comp_sot continuous_map_right_comp_sot)
    show ?thesis
      using closedin_vimage[OF closed_0 cont]
      by (simp add: comm_a)
  qed
  have *: \<open>commutant A = (\<Inter>a\<in>A. commutant {a})\<close>
    by (auto simp add: commutant_def)
  show ?thesis
    by (auto intro!: closedin_Inter simp: * False closed_a)
qed

lemma commutant_tensor1': \<open>commutant (range (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a)) = range (\<lambda>b. b \<otimes>\<^sub>o id_cblinfun)\<close>
proof -
  have \<open>commutant (range (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a)) = commutant (sandwich swap_ell2 ` range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun))\<close>
    by (metis (no_types, lifting) image_cong range_composition swap_tensor_op_sandwich)
  also have \<open>\<dots> = sandwich swap_ell2 ` commutant (range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun))\<close>
    by (simp add: sandwich_unitary_commutant)
  also have \<open>\<dots> = sandwich swap_ell2 ` range (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a)\<close>
    by (simp add: commutant_tensor1)
  also have \<open>\<dots> = range (\<lambda>b. b \<otimes>\<^sub>o id_cblinfun)\<close>
    by force
  finally show ?thesis
    by -
qed


lemma closed_map_sot_tensor_op_id_right: 
  \<open>closed_map cstrong_operator_topology cstrong_operator_topology (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun :: ('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2)\<close>
proof (unfold closed_map_def, intro allI impI)
  fix U :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) set\<close>
  assume closed_U: \<open>closedin cstrong_operator_topology U\<close>

  have aux1: \<open>range f \<subseteq> X \<longleftrightarrow> (\<forall>x. f x \<in> X)\<close> for f :: \<open>'x \<Rightarrow> 'y\<close> and X
    by blast

  have \<open>l \<in> (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` U\<close> if range: \<open>range (\<lambda>x. f x) \<subseteq> (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` U\<close>
    and limit: \<open>limitin cstrong_operator_topology f l F\<close> and \<open>F \<noteq> \<bottom>\<close> 
  for f and l :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close> and F :: \<open>(('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2) filter\<close>
  proof -
    from range obtain f' where f'U: \<open>range f' \<subseteq> U\<close> and f_def: \<open>f y = f' y \<otimes>\<^sub>o id_cblinfun\<close> for y
      apply atomize_elim
      apply (subst aux1)
      apply (rule choice2)
      by auto
    have \<open>l \<in> commutant (range (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a))\<close>
    proof (rule commutant_memberI)
      fix c :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close> 
      assume \<open>c \<in> range (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a)\<close>
      then obtain c' where c_def: \<open>c = id_cblinfun \<otimes>\<^sub>o c'\<close>
        by blast
      from limit have 1: \<open>limitin cstrong_operator_topology ((\<lambda>z. z o\<^sub>C\<^sub>L c) o f) (l o\<^sub>C\<^sub>L c) F\<close>
        apply(rule continuous_map_limit[rotated])
        by (simp add: continuous_map_right_comp_sot)
      from limit have 2: \<open>limitin cstrong_operator_topology ((\<lambda>z. c o\<^sub>C\<^sub>L z) o f) (c o\<^sub>C\<^sub>L l) F\<close>
        apply(rule continuous_map_limit[rotated])
        by (simp add: continuous_map_left_comp_sot)
      have 3: \<open>f x o\<^sub>C\<^sub>L c = c o\<^sub>C\<^sub>L f x\<close> for x
        by (simp add: f_def c_def comp_tensor_op)
      from 1 2 show \<open>l o\<^sub>C\<^sub>L c = c o\<^sub>C\<^sub>L l\<close>
        unfolding 3 o_def
        by (meson hausdorff_sot limitin_Hausdorff_unique that(3))
    qed
    then have \<open>l \<in> range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun)\<close>
      by (simp add: commutant_tensor1')
    then obtain l' where l_def: \<open>l = l' \<otimes>\<^sub>o id_cblinfun\<close>
      by blast
    have \<open>limitin cstrong_operator_topology f' l' F\<close>
    proof (rule limitin_cstrong_operator_topology[THEN iffD2], rule allI)
      fix \<psi> fix b :: 'b
      have \<open>((\<lambda>x. f x *\<^sub>V (\<psi> \<otimes>\<^sub>s ket b)) \<longlongrightarrow> l *\<^sub>V (\<psi> \<otimes>\<^sub>s ket b)) F\<close>
        using limitin_cstrong_operator_topology that(2) by auto
      then have \<open>((\<lambda>x. (f' x *\<^sub>V \<psi>) \<otimes>\<^sub>s ket b) \<longlongrightarrow> (l' *\<^sub>V \<psi>) \<otimes>\<^sub>s ket b) F\<close>
        by (simp add: f_def l_def tensor_op_ell2)
      then have \<open>((\<lambda>x. (tensor_ell2_right (ket b))* *\<^sub>V ((f' x *\<^sub>V \<psi>) \<otimes>\<^sub>s ket b)) 
                  \<longlongrightarrow> (tensor_ell2_right (ket b))* *\<^sub>V ((l' *\<^sub>V \<psi>) \<otimes>\<^sub>s ket b)) F\<close>
        apply (rule cblinfun.tendsto[rotated])
        by simp
      then show \<open>((\<lambda>x. f' x *\<^sub>V \<psi>) \<longlongrightarrow> l' *\<^sub>V \<psi>) F\<close>
        by (simp add: tensor_ell2_right_adj_apply)
    qed
    with closed_U f'U \<open>F \<noteq> \<bottom>\<close> have \<open>l' \<in> U\<close>
      by (simp add: Misc_Tensor_Product.limitin_closedin)
    then show \<open>l \<in> (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` U\<close>
      by (simp add: l_def)
  qed
  then show \<open>closedin cstrong_operator_topology ((\<lambda>a. a \<otimes>\<^sub>o id_cblinfun :: ('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2) ` U)\<close>
    apply (rule_tac closedin_if_converge_inside)
    by simp_all
qed

lemma id_in_commutant[iff]: \<open>id_cblinfun \<in> commutant A\<close>
  by (simp add: commutant_memberI)

lemma double_commutant_hull: \<open>commutant (commutant X) = (\<lambda>X. commutant (commutant X) = X) hull X\<close>
  by (smt (verit) commutant_antimono double_commutant_grows hull_unique triple_commutant)

lemma commutant_adj_closed: \<open>(\<And>x. x \<in> X \<Longrightarrow> x* \<in> X) \<Longrightarrow> x \<in> commutant X \<Longrightarrow> x* \<in> commutant X\<close>
  by (metis (no_types, opaque_lifting) commutant_adj commutant_antimono double_adj imageI subset_iff)

lemma double_commutant_Un_left: \<open>commutant (commutant (commutant (commutant X) \<union> Y)) = commutant (commutant (X \<union> Y))\<close>
  apply (simp add: double_commutant_hull cong: arg_cong[where f=\<open>Hull.hull _\<close>])
  using hull_Un_left by fastforce

lemma double_commutant_Un_right: \<open>commutant (commutant (X \<union> commutant (commutant Y))) = commutant (commutant (X \<union> Y))\<close>
  by (metis Un_ac(3) double_commutant_Un_left)


lemma amplification_double_commutant_commute:
  \<open>commutant (commutant ((\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` X))
    = (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) `  commutant (commutant X)\<close>
\<comment> \<open>\<^cite>\<open>takesaki\<close>, Corollary IV.1.5\<close>
proof -
  define \<pi> :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) \<Rightarrow> (('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2)\<close> where 
    \<open>\<pi> a = a \<otimes>\<^sub>o id_cblinfun\<close> for a
  define U :: \<open>'b \<Rightarrow> 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close> where \<open>U i = tensor_ell2_right (ket i)\<close> for i :: 'b
  write commutant (\<open>_''\<close> [120] 120)
      \<comment> \<open>Notation \<^term>\<open>X '\<close> for \<^term>\<open>commutant X\<close>\<close>
  write id_cblinfun (\<open>\<one>\<close>)
  have *: \<open>(\<pi> ` X)'' \<subseteq> range \<pi>\<close> for X
  proof (rule subsetI)
    fix x assume asm: \<open>x \<in> (\<pi> ` X)''\<close>
    fix t
    define y where \<open>y = U t* o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L U t\<close>
    have \<open>ket (k,l) \<bullet>\<^sub>C (x *\<^sub>V ket (m,n)) = ket (k,l) \<bullet>\<^sub>C (\<pi> y *\<^sub>V ket (m,n))\<close> for k l m n
    proof -
      have comm: \<open>x o\<^sub>C\<^sub>L (U i o\<^sub>C\<^sub>L U j*) = (U i o\<^sub>C\<^sub>L U j*) o\<^sub>C\<^sub>L x\<close> for i j
      proof -
        have \<open>U i o\<^sub>C\<^sub>L U j* = id_cblinfun \<otimes>\<^sub>o butterfly (ket i) (ket j)\<close>
          by (simp add: U_def tensor_ell2_right_butterfly)
        also have \<open>\<dots> \<in> (\<pi> ` X)'\<close>
          by (simp add: \<pi>_def commutant_def comp_tensor_op)
        finally show ?thesis
          using asm
          by (simp add: commutant_def)
      qed
      have \<open>ket (k,l) \<bullet>\<^sub>C (x *\<^sub>V ket (m,n)) = ket k \<bullet>\<^sub>C (U l* *\<^sub>V x *\<^sub>V U n *\<^sub>V ket m)\<close>
        by (simp add: cinner_adj_right U_def tensor_ell2_ket)
      also have \<open>\<dots> = ket k \<bullet>\<^sub>C (U l* *\<^sub>V x *\<^sub>V U n *\<^sub>V U t* *\<^sub>V U t *\<^sub>V ket m)\<close>
        using U_def by fastforce
      also have \<open>\<dots> = ket k \<bullet>\<^sub>C (U l* *\<^sub>V U n *\<^sub>V U t* *\<^sub>V x *\<^sub>V U t *\<^sub>V ket m)\<close>
        using simp_a_oCL_b'[OF comm]
        by simp
      also have \<open>\<dots> = of_bool (l=n) * (ket k \<bullet>\<^sub>C (U t* *\<^sub>V x *\<^sub>V U t *\<^sub>V ket m))\<close>
        using U_def by fastforce
      also have \<open>\<dots> = of_bool (l=n) * (ket k \<bullet>\<^sub>C (y *\<^sub>V ket m))\<close>
        using y_def by force
      also have \<open>\<dots> = ket (k,l) \<bullet>\<^sub>C (\<pi> y *\<^sub>V ket (m,n))\<close>
        by (simp add: \<pi>_def tensor_op_ell2 flip: tensor_ell2_ket)
      finally show ?thesis
        by -
    qed
    then have \<open>x = \<pi> y\<close>
      by (metis cinner_ket_eqI equal_ket surj_pair)
    then show \<open>x \<in> range \<pi>\<close>
      by simp
  qed
  have **: \<open>\<pi> ` (Y ') = (\<pi> ` Y)' \<inter> range \<pi>\<close> for Y
    using inj_tensor_left[of id_cblinfun]
    apply (auto simp add: commutant_def \<pi>_def comp_tensor_op
        intro!: image_eqI)
    using injD by fastforce
  have 1: \<open>(\<pi> ` X)'' \<subseteq> \<pi> ` (X '')\<close> for X
  proof -
    have \<open>(\<pi> ` X)'' \<subseteq> (\<pi> ` X)'' \<inter> range \<pi>\<close>
      by (simp add: "*")
    also have \<open>\<dots> \<subseteq> ((\<pi> ` X)' \<inter> range \<pi>)' \<inter> range \<pi>\<close>
      by (simp add: commutant_antimono inf.coboundedI1)
    also have \<open>\<dots> = \<pi> ` (X '')\<close>
      by (simp add: ** )
    finally show ?thesis
      by -
  qed

  have \<open>x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x\<close> if \<open>x \<in> \<pi> ` (X '')\<close> and \<open>y \<in> (\<pi> ` X)'\<close> for x y
  proof (intro equal_ket cinner_ket_eqI)
    fix i j :: \<open>'a \<times> 'b\<close>
    from that obtain w where \<open>w \<in> X ''\<close> and x_def: \<open>x = w \<otimes>\<^sub>o \<one>\<close>
      by (auto simp: \<pi>_def)
    obtain i1 i2 where i_def: \<open>i = (i1, i2)\<close> by force
    obtain j1 j2 where j_def: \<open>j = (j1, j2)\<close> by force
    define y\<^sub>0 where \<open>y\<^sub>0 = U i2* o\<^sub>C\<^sub>L y o\<^sub>C\<^sub>L U j2\<close>

    have \<open>y\<^sub>0 \<in> X '\<close>
    proof (rule commutant_memberI)
      fix z assume \<open>z \<in> X\<close>
      then have \<open>z \<otimes>\<^sub>o \<one> \<in> \<pi> ` X\<close>
        by (auto simp: \<pi>_def)
      have \<open>y\<^sub>0 o\<^sub>C\<^sub>L z = U i2* o\<^sub>C\<^sub>L y o\<^sub>C\<^sub>L (z \<otimes>\<^sub>o \<one>) o\<^sub>C\<^sub>L U j2\<close>
        by (auto intro!: equal_ket simp add: y\<^sub>0_def U_def tensor_op_ell2)
      also have \<open>\<dots> = U i2* o\<^sub>C\<^sub>L (z \<otimes>\<^sub>o \<one>) o\<^sub>C\<^sub>L y o\<^sub>C\<^sub>L U j2\<close>
        using \<open>z \<otimes>\<^sub>o \<one> \<in> \<pi> ` X\<close> and \<open>y \<in> (\<pi> ` X)'\<close>
        apply (auto simp add: commutant_def)
        by (simp add: cblinfun_compose_assoc)
      also have \<open>\<dots> = z o\<^sub>C\<^sub>L y\<^sub>0\<close>
        by (auto intro!: equal_ket cinner_ket_eqI
            simp add: y\<^sub>0_def U_def tensor_op_ell2 tensor_op_adjoint simp flip: cinner_adj_left)
      finally show \<open>y\<^sub>0 o\<^sub>C\<^sub>L z = z o\<^sub>C\<^sub>L y\<^sub>0\<close>
        by -
    qed
    have \<open>ket i \<bullet>\<^sub>C ((x o\<^sub>C\<^sub>L y) *\<^sub>V ket j) = ket i1 \<bullet>\<^sub>C (U i2* *\<^sub>V (w \<otimes>\<^sub>o \<one>) *\<^sub>V y *\<^sub>V U j2 *\<^sub>V ket j1)\<close>
      by (simp add: U_def i_def j_def tensor_ell2_ket cinner_adj_right x_def)
    also have \<open>\<dots> = ket i1 \<bullet>\<^sub>C (U i2* *\<^sub>V (w \<otimes>\<^sub>o \<one>) *\<^sub>V (U i2 o\<^sub>C\<^sub>L U i2*) *\<^sub>V y *\<^sub>V U j2 *\<^sub>V ket j1)\<close>
      by (simp add: U_def tensor_ell2_right_butterfly tensor_op_adjoint tensor_op_ell2
          flip: cinner_adj_left)
    also have \<open>\<dots> = ket i1 \<bullet>\<^sub>C (w *\<^sub>V y\<^sub>0 *\<^sub>V ket j1)\<close>
      by (simp add: y\<^sub>0_def tensor_op_adjoint tensor_op_ell2 U_def flip: cinner_adj_left)
    also have \<open>\<dots> = ket i1 \<bullet>\<^sub>C (y\<^sub>0 *\<^sub>V w *\<^sub>V ket j1)\<close>
      using \<open>y\<^sub>0 \<in> X '\<close> \<open>w \<in> X ''\<close>
      apply (subst (asm) (2) commutant_def)
      using lift_cblinfun_comp(4) by force
    also have \<open>\<dots> = ket i1 \<bullet>\<^sub>C (U i2* *\<^sub>V y *\<^sub>V (U j2 o\<^sub>C\<^sub>L U j2*) *\<^sub>V (w \<otimes>\<^sub>o \<one>) *\<^sub>V U j2 *\<^sub>V ket j1)\<close>
      by (simp add: y\<^sub>0_def tensor_op_adjoint tensor_op_ell2 U_def flip: cinner_adj_left)
    also have \<open>\<dots> = ket i1 \<bullet>\<^sub>C (U i2* *\<^sub>V y *\<^sub>V (w \<otimes>\<^sub>o \<one>) *\<^sub>V U j2 *\<^sub>V ket j1)\<close>
      by (simp add: U_def tensor_ell2_right_butterfly tensor_op_adjoint tensor_op_ell2
          flip: cinner_adj_left)
    also have \<open>\<dots> = ket i \<bullet>\<^sub>C ((y o\<^sub>C\<^sub>L x) *\<^sub>V ket j)\<close>
      by (simp add: U_def i_def j_def tensor_ell2_ket cinner_adj_right x_def)
    finally show \<open>ket i \<bullet>\<^sub>C ((x o\<^sub>C\<^sub>L y) *\<^sub>V ket j) = ket i \<bullet>\<^sub>C ((y o\<^sub>C\<^sub>L x) *\<^sub>V ket j)\<close>
      by -
  qed
  then have 2: \<open>(\<pi> ` X)'' \<supseteq> \<pi> ` (X '')\<close>
    by (auto intro!: commutant_memberI)
  from 1 2 show ?thesis
    by (auto simp flip: \<pi>_def)
qed

lemma amplification_double_commutant_commute':
  \<open>commutant (commutant ((\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` X))
    = (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) `  commutant (commutant X)\<close>
proof -
  have \<open>commutant (commutant ((\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` X))
    = commutant (commutant (sandwich swap_ell2 ` (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` X))\<close>
    by (simp add: swap_tensor_op_sandwich image_image)
  also have \<open>\<dots> = sandwich swap_ell2 ` commutant (commutant ((\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` X))\<close>
    by (simp add: sandwich_unitary_commutant)
  also have \<open>\<dots> = sandwich swap_ell2 ` (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` commutant (commutant X)\<close>
    by (simp add: amplification_double_commutant_commute)
  also have \<open>\<dots> = (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) `  commutant (commutant X)\<close>
    by (simp add: swap_tensor_op_sandwich image_image)
  finally show ?thesis
    by -
qed

lemma commutant_cspan: \<open>commutant (cspan A) = commutant A\<close>
  by (meson basic_trans_rules(24) commutant_antimono complex_vector.span_superset cspan_in_double_commutant dual_order.trans)

lemma double_commutant_grows': \<open>x \<in> X \<Longrightarrow> x \<in> commutant (commutant X)\<close>
  using double_commutant_grows by blast



subsection \<open>Double commutant theorem\<close>



fun inflation_op' :: \<open>nat \<Rightarrow> ('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) list \<Rightarrow> ('a\<times>nat) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b\<times>nat) ell2\<close> where
  \<open>inflation_op' n Nil = 0\<close>
| \<open>inflation_op' n (a#as) = (a \<otimes>\<^sub>o butterfly (ket n) (ket n)) + inflation_op' (n+1) as\<close>

abbreviation \<open>inflation_op \<equiv> inflation_op' 0\<close>

fun inflation_state' :: \<open>nat \<Rightarrow> 'a ell2 list \<Rightarrow> ('a\<times>nat) ell2\<close> where
  \<open>inflation_state' n Nil = 0\<close>
| \<open>inflation_state' n (a#as) = (a \<otimes>\<^sub>s ket n) + inflation_state' (n+1) as\<close>

abbreviation \<open>inflation_state \<equiv> inflation_state' 0\<close>

fun inflation_space' :: \<open>nat \<Rightarrow> 'a ell2 ccsubspace list \<Rightarrow> ('a\<times>nat) ell2 ccsubspace\<close> where
  \<open>inflation_space' n Nil = 0\<close>
| \<open>inflation_space' n (S#Ss) = (S \<otimes>\<^sub>S ccspan {ket n}) + inflation_space' (n+1) Ss\<close>

abbreviation \<open>inflation_space \<equiv> inflation_space' 0\<close>

definition inflation_carrier :: \<open>nat \<Rightarrow> ('a\<times>nat) ell2 ccsubspace\<close> where
  \<open>inflation_carrier n = inflation_space (replicate n \<top>)\<close>

definition inflation_op_carrier :: \<open>nat \<Rightarrow> (('a\<times>nat) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b\<times>nat) ell2) set\<close> where
  \<open>inflation_op_carrier n = { Proj (inflation_carrier n) o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L Proj (inflation_carrier n) | a. True }\<close>

lemma inflation_op_compose_outside: \<open>inflation_op' m ops o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o butterfly (ket n) (ket n)) = 0\<close> if \<open>n < m\<close>
  using that apply (induction ops arbitrary: m)
  by (auto simp: cblinfun_compose_add_left comp_tensor_op cinner_ket)

lemma inflation_op_compose_outside_rev: \<open>(a \<otimes>\<^sub>o butterfly (ket n) (ket n)) o\<^sub>C\<^sub>L inflation_op' m ops = 0\<close> if \<open>n < m\<close>
  using that apply (induction ops arbitrary: m)
  by (auto simp: cblinfun_compose_add_right comp_tensor_op cinner_ket)


lemma Proj_inflation_carrier: \<open>Proj (inflation_carrier n) = inflation_op (replicate n id_cblinfun)\<close>
proof -
  have \<open>Proj (inflation_space' m (replicate n \<top>)) = inflation_op' m (replicate n id_cblinfun)\<close> for m
  proof (induction n arbitrary: m)
    case 0
    then show ?case
      by simp
  next
    case (Suc n)
    have *: \<open>orthogonal_spaces ((\<top> :: 'b ell2 ccsubspace) \<otimes>\<^sub>S ccspan {ket m}) (inflation_space' (Suc m) (replicate n \<top>))\<close>
      by (auto simp add: orthogonal_projectors_orthogonal_spaces Suc tensor_ccsubspace_via_Proj 
          Proj_on_own_range is_Proj_tensor_op inflation_op_compose_outside_rev butterfly_is_Proj
          simp flip: butterfly_eq_proj)
    show ?case 
      apply (simp add: Suc * Proj_sup)
      by (metis (no_types, opaque_lifting) Proj_is_Proj Proj_on_own_range Proj_top 
          butterfly_eq_proj is_Proj_tensor_op norm_ket tensor_ccsubspace_via_Proj)
  qed
  then show ?thesis
    by (force simp add: inflation_carrier_def)
qed

lemma inflation_op_carrierI:
  assumes \<open>Proj (inflation_carrier n) o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L Proj (inflation_carrier n) = a\<close>
  shows \<open>a \<in> inflation_op_carrier n\<close>
  using assms by (auto intro!: exI[of _ a] simp add: inflation_op_carrier_def)

lemma inflation_op_compose: \<open>inflation_op' n ops1 o\<^sub>C\<^sub>L inflation_op' n ops2 = inflation_op' n (map2 cblinfun_compose ops1 ops2)\<close>
proof (induction ops2 arbitrary: ops1 n)
  case Nil
  then show ?case by simp
next
  case (Cons op ops2)
  note IH = this
  fix ops1 :: \<open>('c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) list\<close>
  show \<open>inflation_op' n ops1 o\<^sub>C\<^sub>L inflation_op' n (op # ops2) =
        inflation_op' n (map2 (o\<^sub>C\<^sub>L) ops1 (op # ops2))\<close>
  proof (cases ops1)
    case Nil
    then show ?thesis 
      by simp
  next
    case (Cons a list)
    then show ?thesis
      by (simp add: cblinfun_compose_add_right cblinfun_compose_add_left tensor_op_ell2
          inflation_op_compose_outside comp_tensor_op inflation_op_compose_outside_rev
          flip: IH)
  qed
qed

lemma inflation_op_in_carrier: \<open>inflation_op ops \<in> inflation_op_carrier n\<close> if \<open>length ops \<le> n\<close>
  apply (rule inflation_op_carrierI)
  using that
  by (simp add: Proj_inflation_carrier inflation_op_carrier_def inflation_op_compose
      zip_replicate1 zip_replicate2 o_def)

lemma inflation_op'_apply_tensor_outside: \<open>n < m \<Longrightarrow> inflation_op' m as *\<^sub>V (v \<otimes>\<^sub>s ket n) = 0\<close>
  apply (induction as arbitrary: m)
  by (auto simp: cblinfun.add_left tensor_op_ell2 cinner_ket)

lemma inflation_op'_compose_tensor_outside: \<open>n < m \<Longrightarrow> inflation_op' m as o\<^sub>C\<^sub>L tensor_ell2_right (ket n) = 0\<close>
  apply (rule cblinfun_eqI)
  by (simp add: inflation_op'_apply_tensor_outside)

lemma inflation_state'_apply_tensor_outside: \<open>n < m \<Longrightarrow> (a \<otimes>\<^sub>o butterfly \<psi> (ket n)) *\<^sub>V inflation_state' m vs = 0\<close>
  apply (induction vs arbitrary: m)
  by (auto simp: cblinfun.add_right tensor_op_ell2 cinner_ket)

lemma inflation_op_apply_inflation_state: \<open>inflation_op' n ops *\<^sub>V inflation_state' n vecs = inflation_state' n (map2 cblinfun_apply ops vecs)\<close>
proof (induction vecs arbitrary: ops n)
  case Nil
  then show ?case by simp
next
  case (Cons v vecs)
  note IH = this
  fix ops :: \<open>('b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) list\<close>
  show \<open>inflation_op' n ops *\<^sub>V inflation_state' n (v # vecs) =
        inflation_state' n (map2 (*\<^sub>V) ops (v # vecs))\<close>
  proof (cases ops)
    case Nil
    then show ?thesis 
      by simp
  next
    case (Cons a list)
    then show ?thesis
      by (simp add: cblinfun.add_right cblinfun.add_left tensor_op_ell2
          inflation_op'_apply_tensor_outside inflation_state'_apply_tensor_outside
          flip: IH)
  qed
qed

lemma inflation_state_in_carrier: \<open>inflation_state vecs \<in> space_as_set (inflation_carrier n)\<close> if \<open>length vecs + m \<le> n\<close>
  apply (rule space_as_setI_via_Proj)
  using that
  by (simp add: Proj_inflation_carrier inflation_op_apply_inflation_state zip_replicate1 o_def)

lemma inflation_op'_apply_tensor_outside': \<open>n \<ge> length as + m \<Longrightarrow> inflation_op' m as *\<^sub>V (v \<otimes>\<^sub>s ket n) = 0\<close>
  apply (induction as arbitrary: m)
  by (auto simp: cblinfun.add_left tensor_op_ell2 cinner_ket)

lemma Proj_inflation_carrier_outside: \<open>Proj (inflation_carrier n) *\<^sub>V (\<psi> \<otimes>\<^sub>s ket i) = 0\<close> if \<open>i \<ge> n\<close>
  by (simp add: Proj_inflation_carrier inflation_op'_apply_tensor_outside' that)

lemma inflation_state'_is_orthogonal_outside: \<open>n < m \<Longrightarrow> is_orthogonal (a \<otimes>\<^sub>s ket n) (inflation_state' m vs)\<close>
  apply (induction vs arbitrary: m)
  by (auto simp: cinner_add_right)

lemma inflation_op_adj: \<open>(inflation_op' n ops)* = inflation_op' n (map adj ops)\<close>
  apply (induction ops arbitrary: n)
  by (simp_all add: adj_plus tensor_op_adjoint)


lemma inflation_state0:
  assumes \<open>\<And>v. v \<in> set f \<Longrightarrow> v = 0\<close>
  shows \<open>inflation_state' n f = 0\<close>
  using assms apply (induction f arbitrary: n)
   apply simp
  using tensor_ell2_0_left by force

lemma inflation_state_plus:
  assumes \<open>length f = length g\<close>
  shows \<open>inflation_state' n f + inflation_state' n g = inflation_state' n (map2 plus f g)\<close>
  using assms apply (induction f g arbitrary: n rule: list_induct2)
  by (auto simp: algebra_simps tensor_ell2_add1)

lemma inflation_state_minus:
  assumes \<open>length f = length g\<close>
  shows \<open>inflation_state' n f - inflation_state' n g = inflation_state' n (map2 minus f g)\<close>
  using assms apply (induction f g arbitrary: n rule: list_induct2)
  by (auto simp: algebra_simps tensor_ell2_diff1)

lemma inflation_state_scaleC:
  shows \<open>c *\<^sub>C inflation_state' n f = inflation_state' n (map (scaleC c) f)\<close>
  apply (induction f arbitrary: n)
  by (auto simp: algebra_simps tensor_ell2_scaleC1)

lemma inflation_op_compose_tensor_ell2_right:
  assumes \<open>i \<ge> n\<close> and \<open>i < n + length f\<close>
  shows \<open>inflation_op' n f o\<^sub>C\<^sub>L tensor_ell2_right (ket i) = tensor_ell2_right (ket i) o\<^sub>C\<^sub>L (f!(i-n))\<close>
proof (insert assms, induction f arbitrary: n)
  case Nil
  then show ?case
    by simp
next
  case (Cons a f)
  show ?case
  proof (cases \<open>i = n\<close>)
    case True
    have \<open>a \<otimes>\<^sub>o butterfly (ket n) (ket n) o\<^sub>C\<^sub>L tensor_ell2_right (ket n) = tensor_ell2_right (ket n) o\<^sub>C\<^sub>L a\<close>
      apply (rule cblinfun_eqI)
      by (simp add: tensor_op_ell2 cinner_ket)
    with True show ?thesis
      by (simp add: cblinfun_compose_add_left inflation_op'_compose_tensor_outside)
  next
    case False
    with Cons.prems have 1: \<open>Suc n \<le> i\<close>
      by presburger
    have 2: \<open>a \<otimes>\<^sub>o butterfly (ket n) (ket n) o\<^sub>C\<^sub>L tensor_ell2_right (ket i) = 0\<close>
      apply (rule cblinfun_eqI)
      using False by (simp add: tensor_op_ell2 cinner_ket)
    show ?thesis
      using Cons.prems 1
      by (simp add: cblinfun_compose_add_left Cons.IH[where n=\<open>Suc n\<close>] 2)
  qed
qed

lemma inflation_op_apply:
  assumes \<open>i \<ge> n\<close> and \<open>i < n + length f\<close>
  shows \<open>inflation_op' n f *\<^sub>V (\<psi> \<otimes>\<^sub>s ket i) = (f!(i-n) *\<^sub>V \<psi>) \<otimes>\<^sub>s ket i\<close>
  by (simp add: inflation_op_compose_tensor_ell2_right assms
      flip: tensor_ell2_right_apply cblinfun_apply_cblinfun_compose)

lemma norm_inflation_state:
  \<open>norm (inflation_state' n f) = sqrt (\<Sum>v\<leftarrow>f. (norm v)\<^sup>2)\<close>
proof -
  have \<open>(norm (inflation_state' n f))\<^sup>2 = (\<Sum>v\<leftarrow>f. (norm v)\<^sup>2)\<close>
  proof (induction f arbitrary: n)
    case Nil
    then show ?case by simp
  next
    case (Cons v f)
    have \<open>(norm (inflation_state' n (v # f)))\<^sup>2 = (norm (v \<otimes>\<^sub>s ket n + inflation_state' (Suc n) f))\<^sup>2\<close>
      by simp
    also have \<open>\<dots> = (norm (v \<otimes>\<^sub>s ket n))\<^sup>2 + (norm (inflation_state' (Suc n) f))\<^sup>2\<close>
      apply (rule pythagorean_theorem)
      apply (rule inflation_state'_is_orthogonal_outside)
      by simp
    also have \<open>\<dots> = (norm (v \<otimes>\<^sub>s ket n))\<^sup>2 + (\<Sum>v\<leftarrow>f. (norm v)\<^sup>2)\<close>
      by (simp add: Cons.IH)
    also have \<open>\<dots> = (norm v)\<^sup>2 + (\<Sum>v\<leftarrow>f. (norm v)\<^sup>2)\<close>
      by (simp add: norm_tensor_ell2)
    also have \<open>\<dots> = (\<Sum>v\<leftarrow>v#f. (norm v)\<^sup>2)\<close>
      by simp
    finally show ?case
      by -
  qed
  then show ?thesis
    by (simp add: real_sqrt_unique)
qed


lemma cstrong_operator_topology_in_closure_algebraicI:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition IX.5.3\<close>
  assumes space: \<open>csubspace A\<close>
  assumes mult: \<open>\<And>a a'. a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L a' \<in> A\<close>
  assumes one: \<open>id_cblinfun \<in> A\<close>
  assumes main: \<open>\<And>n S. S \<le> inflation_carrier n \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> inflation_op (replicate n a) *\<^sub>S S \<le> S) \<Longrightarrow>
                 inflation_op (replicate n b) *\<^sub>S S \<le> S\<close>
  shows \<open>b \<in> cstrong_operator_topology closure_of A\<close>
proof (rule cstrong_operator_topology_in_closureI)
  fix F :: \<open>'a ell2 set\<close> and \<epsilon> :: real
  assume \<open>finite F\<close> and \<open>\<epsilon> > 0\<close>
  obtain f where \<open>set f = F\<close> and \<open>distinct f\<close>
    using \<open>finite F\<close> finite_distinct_list by blast
  define n M' M where \<open>n = length f\<close>
    and \<open>M' = ((\<lambda>a. inflation_state (map (cblinfun_apply a) f)) ` A)\<close>
    and \<open>M = ccspan M'\<close>
  have M_carrier: \<open>M \<le> inflation_carrier n\<close>
  proof -
    have \<open>M' \<subseteq> space_as_set (inflation_carrier n)\<close>
      by (auto intro!: inflation_state_in_carrier simp add: M'_def n_def)
    then show ?thesis
      by (simp add: M_def ccspan_leqI)
  qed

  have \<open>inflation_op (replicate n a) *\<^sub>S M \<le> M\<close> if \<open>a \<in> A\<close> for a
  proof (unfold M_def, rule cblinfun_image_ccspan_leqI)
    fix v assume \<open>v \<in> M'\<close>
    then obtain a' where \<open>a' \<in> A\<close> and v_def: \<open>v = inflation_state (map (cblinfun_apply a') f)\<close>
      using M'_def by blast
    then have \<open>inflation_op (replicate n a) *\<^sub>V v = inflation_state (map ((*\<^sub>V) (a o\<^sub>C\<^sub>L a')) f)\<close>
      by (simp add: v_def n_def inflation_op_apply_inflation_state map2_map_map 
          flip: cblinfun_apply_cblinfun_compose map_replicate_const)
    also have \<open>\<dots> \<in> M'\<close>
      using M'_def \<open>a' \<in> A\<close> \<open>a \<in> A\<close> mult
      by simp
    also have \<open>\<dots> \<subseteq> space_as_set (ccspan M')\<close>
      by (simp add: ccspan_superset)
    finally show \<open>inflation_op (replicate n a) *\<^sub>V v \<in> space_as_set (ccspan M')\<close>
      by -
  qed
  then have b_invariant: \<open>inflation_op (replicate n b) *\<^sub>S M \<le> M\<close>
    using M_carrier by (simp add: main)
  have f_M: \<open>inflation_state f \<in> space_as_set M\<close>
  proof -
    have \<open>inflation_state f = inflation_state (map (cblinfun_apply id_cblinfun) f)\<close>
      by simp
    also have \<open>\<dots> \<in> M'\<close>
      using M'_def one by blast
    also have \<open>\<dots> \<subseteq> space_as_set M\<close>
      by (simp add: M_def ccspan_superset)
    finally show ?thesis
      by -
  qed
  have \<open>csubspace M'\<close>
  proof (rule complex_vector.subspaceI)
    fix c x y
    show \<open>0 \<in> M'\<close>
      apply (auto intro!: image_eqI[where x=0] simp add: M'_def)
       apply (subst inflation_state0)
      by (auto simp add: space complex_vector.subspace_0)
    show \<open>x \<in> M' \<Longrightarrow> y \<in> M' \<Longrightarrow> x + y \<in> M'\<close>
      by (auto intro!: image_eqI[where x=\<open>_ + _\<close>] 
          simp add: M'_def inflation_state_plus map2_map_map
          cblinfun.add_left[abs_def] space complex_vector.subspace_add)
    show \<open>c *\<^sub>C x \<in> M' \<close> if \<open>x \<in> M'\<close>
    proof -
      from that
      obtain a where \<open>a \<in> A\<close> and \<open>x = inflation_state (map ((*\<^sub>V) a) f)\<close>
        by (auto simp add: M'_def)
      then have \<open>c *\<^sub>C x = inflation_state (map ((*\<^sub>V) (c *\<^sub>C a)) f)\<close>
        by (simp add: inflation_state_scaleC o_def scaleC_cblinfun.rep_eq)
      moreover have \<open>c *\<^sub>C a \<in> A\<close>
         by (simp add: \<open>a \<in> A\<close> space complex_vector.subspace_scale)
      ultimately show ?thesis
        unfolding M'_def
        by (rule image_eqI)
    qed
  qed
  then have M_closure_M': \<open>space_as_set M = closure M'\<close>
    by (metis M_def ccspan.rep_eq complex_vector.span_eq_iff)
  have \<open>inflation_state (map (cblinfun_apply b) f) \<in> space_as_set M\<close>
  proof -
    have \<open>map2 (*\<^sub>V) (replicate n b) f = map ((*\<^sub>V) b) f\<close>
      using map2_map_map[where h=cblinfun_apply and g=id and f=\<open>\<lambda>_. b\<close> and xs=f]
      by (simp add: n_def flip: map_replicate_const)
    then have \<open>inflation_state (map (cblinfun_apply b) f) = inflation_op (replicate n b) *\<^sub>V inflation_state f\<close>
      by (simp add: inflation_op_apply_inflation_state)
    also have \<open>\<dots> \<in> space_as_set (inflation_op (replicate n b) *\<^sub>S M)\<close>
      by (simp add: f_M cblinfun_apply_in_image')
    also have \<open>\<dots> \<subseteq> space_as_set M\<close>
      using b_invariant less_eq_ccsubspace.rep_eq by blast
    finally show ?thesis
      by -
  qed
  then obtain m where \<open>m \<in> M'\<close> and m_close: \<open>norm (m - inflation_state (map (cblinfun_apply b) f)) \<le> \<epsilon>\<close>
    apply atomize_elim
    apply (simp add: M_closure_M' closure_approachable dist_norm)
    using \<open>\<epsilon> > 0\<close> by fastforce
  from \<open>m \<in> M'\<close>
  obtain a where \<open>a \<in> A\<close> and m_def: \<open>m = inflation_state (map (cblinfun_apply a) f)\<close>
    by (auto simp add: M'_def)
  have \<open>(\<Sum>v\<leftarrow>f. (norm ((a - b) *\<^sub>V v))\<^sup>2) \<le> \<epsilon>\<^sup>2\<close>
  proof -
    have \<open>(\<Sum>v\<leftarrow>f. (norm ((a - b) *\<^sub>V v))\<^sup>2) = (norm (inflation_state (map (cblinfun_apply (a - b)) f)))\<^sup>2\<close>
      apply (simp add: norm_inflation_state o_def)
      apply (subst real_sqrt_pow2)
       apply (rule sum_list_nonneg)
      by (auto simp: sum_list_nonneg)
    also have \<open>\<dots> = (norm (m - inflation_state (map (cblinfun_apply b) f)))\<^sup>2\<close>
      by (simp add: m_def inflation_state_minus map2_map_map cblinfun.diff_left[abs_def])
    also have \<open>\<dots> \<le> \<epsilon>\<^sup>2\<close>
      by (simp add: m_close power_mono)
    finally show ?thesis
      by -
  qed
  then have \<open>(norm ((a - b) *\<^sub>V v))\<^sup>2 \<le> \<epsilon>\<^sup>2\<close> if \<open>v \<in> F\<close> for v
    using that apply (simp flip: sum.distinct_set_conv_list add: \<open>distinct f\<close>)
    by (smt (verit) \<open>finite F\<close> \<open>set f = F\<close> sum_nonneg_leq_bound zero_le_power2)
  then show \<open>\<exists>a\<in>A. \<forall>f\<in>F. norm ((b - a) *\<^sub>V f) \<le> \<epsilon>\<close>
    using \<open>0 < \<epsilon>\<close> \<open>a \<in> A\<close>
    by (metis cblinfun.real.diff_left norm_minus_commute power2_le_imp_le power_eq_0_iff power_zero_numeral realpow_pos_nth_unique zero_compare_simps(12))
qed

lemma commutant_inflation:
  \<comment> \<open>One direction of \<^cite>\<open>conway2013course\<close>, Proposition IX.6.2.\<close>
  fixes n
  defines \<open>\<And>X. commutant' X \<equiv> commutant X \<inter> inflation_op_carrier n\<close>
  shows \<open>(\<lambda>a. inflation_op (replicate n a)) ` commutant (commutant A) 
         \<subseteq> commutant' (commutant' ((\<lambda>a. inflation_op (replicate n a)) ` A))\<close>
proof (unfold commutant'_def, rule subsetI, rule IntI)
  fix b
  assume \<open>b \<in> (\<lambda>a. inflation_op (replicate n a)) ` commutant (commutant A)\<close>
  then obtain b0 where b_def: \<open>b = inflation_op (replicate n b0)\<close> and b0_A'': \<open>b0 \<in> commutant (commutant A)\<close>
    by auto
  show \<open>b \<in> inflation_op_carrier n\<close>
    by (simp add: b_def inflation_op_in_carrier)
  show \<open>b \<in> commutant (commutant ((\<lambda>a. inflation_op (replicate n a)) ` A) \<inter> inflation_op_carrier n)\<close>
  proof (rule commutant_memberI)
    fix c
    assume \<open>c \<in> commutant ((\<lambda>a. inflation_op (replicate n a)) ` A) \<inter> inflation_op_carrier n\<close>
    then have c_comm: \<open>c \<in> commutant ((\<lambda>a. inflation_op (replicate n a)) ` A)\<close>
      and c_carr: \<open>c \<in> inflation_op_carrier n\<close>
      by auto
    define c' where \<open>c' i j = (tensor_ell2_right (ket i))* o\<^sub>C\<^sub>L c o\<^sub>C\<^sub>L tensor_ell2_right (ket j)\<close> for i j
    have \<open>c' i j o\<^sub>C\<^sub>L a = a o\<^sub>C\<^sub>L c' i j\<close> if \<open>a \<in> A\<close> and \<open>i < n\<close> and \<open>j < n\<close> for a i j
    proof -
      from c_comm have \<open>c o\<^sub>C\<^sub>L inflation_op (replicate n a) = inflation_op (replicate n a) o\<^sub>C\<^sub>L c\<close>
        using that by (auto simp: commutant_def)
      then have \<open>(tensor_ell2_right (ket i))* o\<^sub>C\<^sub>L c o\<^sub>C\<^sub>L (inflation_op (replicate n a) o\<^sub>C\<^sub>L tensor_ell2_right (ket j))
               = (inflation_op (replicate n (a*)) o\<^sub>C\<^sub>L (tensor_ell2_right (ket i)))* o\<^sub>C\<^sub>L c o\<^sub>C\<^sub>L tensor_ell2_right (ket j)\<close>
        apply (simp add: inflation_op_adj)
        by (metis (no_types, lifting) lift_cblinfun_comp(2))
      then show ?thesis
        apply (subst (asm) inflation_op_compose_tensor_ell2_right)
          apply (simp, simp add: that)
        apply (subst (asm) inflation_op_compose_tensor_ell2_right)
          apply (simp, simp add: that)
        by (simp add: that c'_def cblinfun_compose_assoc)
    qed
    then have \<open>c' i j \<in> commutant A\<close> if \<open>i < n\<close> and \<open>j < n\<close> for i j
      using that by (simp add: commutant_memberI)
    with b0_A'' have b0_c': \<open>b0 o\<^sub>C\<^sub>L c' i j = c' i j o\<^sub>C\<^sub>L b0\<close> if \<open>i < n\<close> and \<open>j < n\<close> for i j
      using that by (simp add: commutant_def)

    from c_carr obtain c'' where c'': \<open>c = Proj (inflation_carrier n) o\<^sub>C\<^sub>L c'' o\<^sub>C\<^sub>L Proj (inflation_carrier n)\<close>
      by (auto simp add: inflation_op_carrier_def)
    
    have c0: \<open>c *\<^sub>V (\<psi> \<otimes>\<^sub>s ket i) = 0\<close> if \<open>i \<ge> n\<close> for i \<psi>
      using that by (simp add: c'' Proj_inflation_carrier_outside)
    have cadj0: \<open>c* *\<^sub>V (\<psi> \<otimes>\<^sub>s ket j) = 0\<close> if \<open>j \<ge> n\<close> for j \<psi>
      using that by (simp add: c'' adj_Proj Proj_inflation_carrier_outside)

    have \<open>inflation_op (replicate n b0) o\<^sub>C\<^sub>L c = c o\<^sub>C\<^sub>L inflation_op (replicate n b0)\<close>
    proof (rule equal_ket, rule cinner_ket_eqI)
      fix ii jj
      obtain i' j' :: 'a and i j :: nat where ii_def: \<open>ii = (i',i)\<close> and jj_def: \<open>jj = (j',j)\<close>
        by force
      show \<open>ket ii \<bullet>\<^sub>C ((inflation_op (replicate n b0) o\<^sub>C\<^sub>L c) *\<^sub>V ket jj) =
                 ket ii \<bullet>\<^sub>C ((c o\<^sub>C\<^sub>L inflation_op (replicate n b0)) *\<^sub>V ket jj)\<close>
      proof (cases \<open>i < n \<and> j < n\<close>)
        case True
        have \<open>ket ii \<bullet>\<^sub>C ((inflation_op (replicate n b0) o\<^sub>C\<^sub>L c) *\<^sub>V ket jj) = ((b0* *\<^sub>V ket i') \<otimes>\<^sub>s ket i) \<bullet>\<^sub>C (c *\<^sub>V ket j' \<otimes>\<^sub>s ket j)\<close>
          using True by (simp add: ii_def jj_def inflation_op_adj inflation_op_apply flip: tensor_ell2_inner_prod
              flip: tensor_ell2_ket cinner_adj_left[where G=\<open>inflation_op _\<close>])
        also have \<open>\<dots> = (ket i' \<otimes>\<^sub>s ket i) \<bullet>\<^sub>C (c *\<^sub>V (b0 *\<^sub>V ket j') \<otimes>\<^sub>s ket j)\<close>
          using b0_c' apply (simp add: c'_def flip: tensor_ell2_right_apply cinner_adj_right)
          by (metis (no_types, lifting) True simp_a_oCL_b')
        also have \<open>\<dots> = ket ii \<bullet>\<^sub>C ((c o\<^sub>C\<^sub>L inflation_op (replicate n b0)) *\<^sub>V ket jj)\<close>
          by (simp add: True ii_def jj_def inflation_op_adj inflation_op_apply flip: tensor_ell2_inner_prod
              flip: tensor_ell2_ket cinner_adj_left[where G=\<open>inflation_op _\<close>])
        finally show ?thesis
          by -
      next
        case False
        then show ?thesis
          apply (auto simp add: ii_def jj_def inflation_op_adj c0 inflation_op'_apply_tensor_outside'
              simp flip: tensor_ell2_ket  cinner_adj_left[where G=\<open>inflation_op _\<close>])
          by (simp add: cadj0 flip: cinner_adj_left[where G=c])
      qed
    qed
    then show \<open>b o\<^sub>C\<^sub>L c = c o\<^sub>C\<^sub>L b\<close>
      by (simp add: b_def)
  qed
qed

lemma double_commutant_theorem_aux:
  \<comment> \<open>Basically the double commutant theorem, except that we restricted to spaces of the form \<^typ>\<open>'a ell2\<close>\<close>
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition IX.6.4\<close>
  fixes A :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) set\<close>
  assumes \<open>csubspace A\<close>
  assumes \<open>\<And>a a'. a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L a' \<in> A\<close>
  assumes \<open>id_cblinfun \<in> A\<close>
  assumes \<open>\<And>a. a \<in> A \<Longrightarrow> a* \<in> A\<close>
  shows \<open>commutant (commutant A) = cstrong_operator_topology closure_of A\<close>
proof (intro Set.set_eqI iffI)
  show \<open>x \<in> commutant (commutant A)\<close> if \<open>x \<in> cstrong_operator_topology closure_of A\<close> for x
    using closure_of_minimal commutant_sot_closed double_commutant_grows that by blast
next
  show \<open>b \<in> cstrong_operator_topology closure_of A\<close> if b_A'': \<open>b \<in> commutant (commutant A)\<close> for b
  proof (rule cstrong_operator_topology_in_closure_algebraicI)
    show \<open>csubspace A\<close> and \<open>a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L a' \<in> A\<close> and \<open>id_cblinfun \<in> A\<close> for a a'
      using assms by auto
    fix n M
    assume asm: \<open>a \<in> A \<Longrightarrow> inflation_op (replicate n a) *\<^sub>S M \<le> M\<close> for a
    assume M_carrier: \<open>M \<le> inflation_carrier n\<close>
    define commutant' where \<open>commutant' X = commutant X \<inter> inflation_op_carrier n\<close> for X :: \<open>(('a \<times> nat) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> nat) ell2) set\<close>
    define An where \<open>An = (\<lambda>a. inflation_op (replicate n a)) ` A\<close>
    have *: \<open>Proj M o\<^sub>C\<^sub>L (inflation_op (replicate n a) o\<^sub>C\<^sub>L Proj M) = inflation_op (replicate n a) o\<^sub>C\<^sub>L Proj M\<close> if \<open>a \<in> A\<close> for a
      apply (rule Proj_compose_cancelI)
      using asm that by (simp add: cblinfun_compose_image)
    have \<open>Proj M o\<^sub>C\<^sub>L inflation_op (replicate n a) = inflation_op (replicate n a) o\<^sub>C\<^sub>L Proj M\<close> if \<open>a \<in> A\<close> for a
    proof -
      have \<open>Proj M o\<^sub>C\<^sub>L inflation_op (replicate n a) = (inflation_op (replicate n (a*)) o\<^sub>C\<^sub>L Proj M)*\<close>
        by (simp add: inflation_op_adj adj_Proj)
      also have \<open>\<dots> = (Proj M o\<^sub>C\<^sub>L inflation_op (replicate n (a*)) o\<^sub>C\<^sub>L Proj M)*\<close>
        apply (subst *[symmetric])
        by (simp_all add: that assms flip: cblinfun_compose_assoc)
      also have \<open>\<dots> = Proj M o\<^sub>C\<^sub>L inflation_op (replicate n a) o\<^sub>C\<^sub>L Proj M\<close>
        by (simp add: inflation_op_adj adj_Proj cblinfun_compose_assoc)
      also have \<open>\<dots> = inflation_op (replicate n a) o\<^sub>C\<^sub>L Proj M\<close>
        apply (subst *[symmetric])
        by (simp_all add: that flip: cblinfun_compose_assoc)
      finally show ?thesis
        by -
    qed
    then have \<open>Proj M \<in> commutant' An\<close>
      using  M_carrier 
      apply (auto intro!: inflation_op_carrierI simp add: An_def commutant_def commutant'_def)
      by (metis Proj_compose_cancelI Proj_range adj_Proj adj_cblinfun_compose)
    from b_A'' have \<open>inflation_op (replicate n b) \<in> commutant' (commutant' An)\<close>
      using commutant_inflation[of n A, folded commutant'_def]
      by (auto simp add: An_def commutant'_def)
    with \<open>Proj M \<in> commutant' An\<close>
    have *: \<open>inflation_op (replicate n b) o\<^sub>C\<^sub>L Proj M = Proj M o\<^sub>C\<^sub>L inflation_op (replicate n b)\<close>
      by (simp add: commutant_def commutant'_def)
    show \<open>inflation_op (replicate n b) *\<^sub>S M \<le> M\<close>
    proof -
      have \<open>inflation_op (replicate n b) *\<^sub>S M = (inflation_op (replicate n b) o\<^sub>C\<^sub>L Proj M) *\<^sub>S \<top>\<close>
        by (metis lift_cblinfun_comp(3) Proj_range)
      also have \<open>\<dots> = (Proj M o\<^sub>C\<^sub>L inflation_op (replicate n b)) *\<^sub>S \<top>\<close>
        by (simp add: * )
      also have \<open>\<dots> \<le> M\<close>
        by (metis lift_cblinfun_comp(3) Proj_image_leq)
      finally show ?thesis
        by -
    qed
  qed
qed

lemma double_commutant_theorem_aux2:
  \<comment> \<open>Basically the double commutant theorem, except that we restricted to spaces of typeclass \<^class>\<open>not_singleton\<close>\<close>
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition IX.6.4\<close>
  fixes A :: \<open>('a::{chilbert_space,not_singleton} \<Rightarrow>\<^sub>C\<^sub>L 'a) set\<close>
  assumes subspace: \<open>csubspace A\<close>
  assumes mult: \<open>\<And>a a'. a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L a' \<in> A\<close>
  assumes id: \<open>id_cblinfun \<in> A\<close>
  assumes adj: \<open>\<And>a. a \<in> A \<Longrightarrow> a* \<in> A\<close>
  shows \<open>commutant (commutant A) = cstrong_operator_topology closure_of A\<close>
proof -
  define A' :: \<open>('a chilbert2ell2 ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a chilbert2ell2 ell2) set\<close>
    where \<open>A' = sandwich (ell2_to_hilbert*) ` A\<close>
  have subspace: \<open>csubspace A'\<close>
    using subspace by (auto intro!: complex_vector.linear_subspace_image simp: A'_def)
  have mult: \<open>\<And>a a'. a \<in> A' \<Longrightarrow> a' \<in> A' \<Longrightarrow> a o\<^sub>C\<^sub>L a' \<in> A'\<close>
    using mult by (auto simp add: A'_def sandwich_arg_compose unitary_ell2_to_hilbert)
  have id: \<open>id_cblinfun \<in> A'\<close>
    using id by (auto intro!: image_eqI simp add: A'_def sandwich_isometry_id unitary_ell2_to_hilbert)
  have adj: \<open>\<And>a. a \<in> A' \<Longrightarrow> a* \<in> A'\<close>
    using adj by (auto intro!: image_eqI simp: A'_def simp flip: sandwich_apply_adj)
  have homeo: \<open>homeomorphic_map cstrong_operator_topology cstrong_operator_topology
     ((*\<^sub>V) (sandwich ell2_to_hilbert))\<close>
    by (auto intro!: continuous_intros homeomorphic_maps_imp_map[where g=\<open>sandwich (ell2_to_hilbert*)\<close>]
        simp: homeomorphic_maps_def unitary_ell2_to_hilbert
        simp flip: cblinfun_apply_cblinfun_compose sandwich_compose)
  have \<open>commutant (commutant A') = cstrong_operator_topology closure_of A'\<close>
    using subspace mult id adj by (rule double_commutant_theorem_aux)
  then have \<open>sandwich ell2_to_hilbert ` commutant (commutant A') = sandwich ell2_to_hilbert ` (cstrong_operator_topology closure_of A')\<close>
    by simp
  then show ?thesis
    by (simp add: A'_def unitary_ell2_to_hilbert sandwich_unitary_commutant image_image homeo
        flip: cblinfun_apply_cblinfun_compose sandwich_compose
        homeomorphic_map_closure_of[where Y=cstrong_operator_topology])
qed

lemma double_commutant_theorem:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition IX.6.4\<close>
  fixes A :: \<open>('a::{chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'a) set\<close>
  assumes subspace: \<open>csubspace A\<close>
  assumes mult: \<open>\<And>a a'. a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L a' \<in> A\<close>
  assumes id: \<open>id_cblinfun \<in> A\<close>
  assumes adj: \<open>\<And>a. a \<in> A \<Longrightarrow> a* \<in> A\<close>
  shows \<open>commutant (commutant A) = cstrong_operator_topology closure_of A\<close>
proof (cases \<open>UNIV = {0::'a}\<close>)
  case True
  then have \<open>(x :: 'a) = 0\<close> for x
    by auto
  then have UNIV_0: \<open>UNIV = {0 :: 'a\<Rightarrow>\<^sub>C\<^sub>L'a}\<close>
    by (auto intro!: cblinfun_eqI)
  have \<open>0 \<in> commutant (commutant A)\<close>
    using complex_vector.subspace_0 csubspace_commutant by blast
  then have 1: \<open>commutant (commutant A) = UNIV\<close>
    using UNIV_0
    by force
  have \<open>0 \<in> A\<close>
    by (simp add: assms(1) complex_vector.subspace_0)
  then have \<open>0 \<in> cstrong_operator_topology closure_of A\<close>
    by (simp add: assms(1) complex_vector.subspace_0)
  then have 2: \<open>cstrong_operator_topology closure_of A = UNIV\<close>
    using UNIV_0
    by force
  from 1 2 show ?thesis 
    by simp
next
  case False
  note aux2 = double_commutant_theorem_aux2[where 'a=\<open>'z::{chilbert_space,not_singleton}\<close>, rule_format, internalize_sort \<open>'z::{chilbert_space,not_singleton}\<close>]
  have hilbert: \<open>class.chilbert_space (*\<^sub>R) (*\<^sub>C) (+) (0::'a) (-) uminus dist norm sgn uniformity open (\<bullet>\<^sub>C)\<close>
    by (rule chilbert_space_class.chilbert_space_axioms)
  from False
  have not_singleton: \<open>class.not_singleton TYPE('a)\<close>
    by (rule class_not_singletonI_monoid_add)
  show ?thesis 
    apply (rule aux2)
    using assms hilbert not_singleton by auto
qed

hide_fact double_commutant_theorem_aux double_commutant_theorem_aux2

lemma double_commutant_theorem_span:
  fixes A :: \<open>('a::{chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'a) set\<close>
  assumes mult: \<open>\<And>a a'. a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L a' \<in> A\<close>
  assumes id: \<open>id_cblinfun \<in> A\<close>
  assumes adj: \<open>\<And>a. a \<in> A \<Longrightarrow> a* \<in> A\<close>
  shows \<open>commutant (commutant A) = cstrong_operator_topology closure_of (cspan A)\<close>
proof -
  have \<open>commutant (commutant A) = commutant (commutant (cspan A))\<close>
    by (simp add: commutant_cspan)
  also have \<open>\<dots> = cstrong_operator_topology closure_of (cspan A)\<close>
    apply (rule double_commutant_theorem)
    using assms
    apply (auto simp: cspan_compose_closed cspan_adj_closed)
    using complex_vector.span_clauses(1) by blast
  finally show ?thesis
    by -
qed


subsection \<open>Von Neumann Algebras\<close>

definition one_algebra :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space) set\<close> where
  \<open>one_algebra = range (\<lambda>c. c *\<^sub>C id_cblinfun)\<close>


definition von_neumann_algebra where \<open>von_neumann_algebra A \<longleftrightarrow> (\<forall>a\<in>A. a* \<in> A) \<and> commutant (commutant A) = A\<close>
definition von_neumann_factor where \<open>von_neumann_factor A \<longleftrightarrow> von_neumann_algebra A \<and> A \<inter> commutant A = one_algebra\<close>

lemma von_neumann_algebraI: \<open>(\<And>a. a\<in>A \<Longrightarrow> a* \<in> A) \<Longrightarrow> commutant (commutant A) \<subseteq> A \<Longrightarrow> von_neumann_algebra A\<close> for \<FF>
  apply (auto simp: von_neumann_algebra_def)
  using double_commutant_grows by blast

lemma von_neumann_factorI:
  assumes \<open>von_neumann_algebra A\<close>
  assumes \<open>A \<inter> commutant A \<subseteq> one_algebra\<close>
  shows \<open>von_neumann_factor A\<close>
proof -
  have 1: \<open>A \<supseteq> one_algebra\<close>
    apply (subst asm_rl[of \<open>A = commutant (commutant A)\<close>])
    using assms(1) von_neumann_algebra_def apply blast
    by (auto simp: commutant_def one_algebra_def)
  have 2: \<open>commutant A \<supseteq> one_algebra\<close>
    by (auto simp: commutant_def one_algebra_def)
  from 1 2 assms show ?thesis
    by (auto simp add: von_neumann_factor_def)
qed

lemma commutant_UNIV: \<open>commutant (UNIV :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space) set) = one_algebra\<close>
  (* Not sure if the assumption chilbert_space is needed *)
proof -
  have 1: \<open>c *\<^sub>C id_cblinfun \<in> commutant UNIV\<close> for c
    by (simp add: commutant_def)
  moreover have 2: \<open>x \<in> range (\<lambda>c. c *\<^sub>C id_cblinfun)\<close> if x_comm: \<open>x \<in> commutant UNIV\<close> for x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  proof -
    obtain B :: \<open>'a set\<close> where \<open>is_onb B\<close>
      using is_onb_some_chilbert_basis by blast
    have \<open>\<exists>c. x *\<^sub>V \<psi> = c *\<^sub>C \<psi>\<close> for \<psi>
    proof -
      have \<open>norm (x *\<^sub>V \<psi>) = norm ((x o\<^sub>C\<^sub>L selfbutter (sgn \<psi>)) *\<^sub>V \<psi>)\<close>
        by (simp add: cnorm_eq_1)
      also have \<open>\<dots> = norm ((selfbutter (sgn \<psi>) o\<^sub>C\<^sub>L x) *\<^sub>V \<psi>)\<close>
        using x_comm by (simp add: commutant_def del: butterfly_apply)
      also have \<open>\<dots> = norm (proj \<psi> *\<^sub>V (x *\<^sub>V \<psi>))\<close>
        by (simp add: butterfly_sgn_eq_proj)
      finally have \<open>x *\<^sub>V \<psi> \<in> space_as_set (ccspan {\<psi>})\<close>
        by (metis norm_Proj_apply)
      then show ?thesis
        by (auto simp add: ccspan_finite complex_vector.span_singleton)
    qed
    then obtain f where f: \<open>x *\<^sub>V \<psi> = f \<psi> *\<^sub>C \<psi>\<close> for \<psi>
      apply atomize_elim apply (rule choice) by auto

    have \<open>f \<psi> = f \<phi>\<close> if \<open>\<psi> \<in> B\<close> and \<open>\<phi> \<in> B\<close> for \<psi> \<phi>
    proof (cases \<open>\<psi> = \<phi>\<close>)
      case True
      then show ?thesis by simp
    next
      case False
      with that \<open>is_onb B\<close>
      have [simp]: \<open>\<psi> \<bullet>\<^sub>C \<phi> = 0\<close>
        by (auto simp: is_onb_def is_ortho_set_def)
      then have [simp]: \<open>\<phi> \<bullet>\<^sub>C \<psi> = 0\<close>
        using is_orthogonal_sym by blast
      from that \<open>is_onb B\<close> have [simp]: \<open>\<psi> \<noteq> 0\<close>
        by (auto simp: is_onb_def)
      from that \<open>is_onb B\<close> have [simp]: \<open>\<phi> \<noteq> 0\<close>
        by (auto simp: is_onb_def)

      have \<open>f (\<psi>+\<phi>) *\<^sub>C \<psi> + f (\<psi>+\<phi>) *\<^sub>C \<phi> = f (\<psi>+\<phi>) *\<^sub>C (\<psi> + \<phi>)\<close>
        by (simp add: complex_vector.vector_space_assms(1))
      also have \<open>\<dots> = x *\<^sub>V (\<psi> + \<phi>)\<close>
        by (simp add: f)
      also have \<open>\<dots> = x *\<^sub>V \<psi> + x *\<^sub>V \<phi>\<close>
        by (simp add: cblinfun.add_right)
      also have \<open>\<dots> = f \<psi> *\<^sub>C \<psi> + f \<phi> *\<^sub>C \<phi>\<close>
        by (simp add: f)
      finally have *: \<open>f (\<psi> + \<phi>) *\<^sub>C \<psi> + f (\<psi> + \<phi>) *\<^sub>C \<phi> = f \<psi> *\<^sub>C \<psi> + f \<phi> *\<^sub>C \<phi>\<close>
        by -
      have \<open>f (\<psi> + \<phi>) = f \<psi>\<close>
        using *[THEN arg_cong[where f=\<open>cinner \<psi>\<close>]]
        by (simp add: cinner_add_right)
      moreover have \<open>f (\<psi> + \<phi>) = f \<phi>\<close>
        using *[THEN arg_cong[where f=\<open>cinner \<phi>\<close>]]
        by (simp add: cinner_add_right)
      ultimately show \<open>f \<psi> = f \<phi>\<close>
        by simp
    qed
    then obtain c where \<open>f \<psi> = c\<close> if \<open>\<psi> \<in> B\<close> for \<psi>
      by meson
    then have \<open>x *\<^sub>V \<psi> = (c *\<^sub>C id_cblinfun) *\<^sub>V \<psi>\<close> if \<open>\<psi> \<in> B\<close> for \<psi>
      by (simp add: f that)
    then have \<open>x = c *\<^sub>C id_cblinfun\<close>
      apply (rule cblinfun_eq_gen_eqI[where G=B])
      using \<open>is_onb B\<close> by (auto simp: is_onb_def)
    then show \<open>x \<in> range (\<lambda>c. c *\<^sub>C id_cblinfun)\<close>
      by (auto)
  qed

  from 1 2 show ?thesis
    by (auto simp: one_algebra_def)
qed


lemma von_neumann_algebra_UNIV: \<open>von_neumann_algebra UNIV\<close>
  by (auto simp: von_neumann_algebra_def commutant_def)

lemma von_neumann_factor_UNIV: \<open>von_neumann_factor UNIV\<close>
  by (simp add: von_neumann_factor_def commutant_UNIV von_neumann_algebra_UNIV)

lemma von_neumann_algebra_UNION:
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> von_neumann_algebra (A x)\<close>
  shows \<open>von_neumann_algebra (commutant (commutant (\<Union>x\<in>X. A x)))\<close>
proof (rule von_neumann_algebraI)
  show \<open>commutant (commutant (commutant (commutant (\<Union>x\<in>X. A x))))
    \<subseteq> commutant (commutant (\<Union>x\<in>X. A x))\<close>
    by (meson commutant_antimono double_commutant_grows)
next
  fix a
  assume \<open>a \<in> commutant (commutant (\<Union>x\<in>X. A x))\<close>
  then have \<open>a* \<in> adj ` commutant (commutant (\<Union>x\<in>X. A x))\<close>
    by simp
  also have \<open>\<dots> = commutant (commutant (\<Union>x\<in>X. adj ` A x))\<close>
    by (simp add: commutant_adj image_UN)
  also have \<open>\<dots> \<subseteq> commutant (commutant (\<Union>x\<in>X. A x))\<close>
    using assms by (auto simp: von_neumann_algebra_def intro!: commutant_antimono)
  finally show \<open>a* \<in> commutant (commutant (\<Union>x\<in>X. A x))\<close>
    by -
qed

lemma von_neumann_algebra_union:
  assumes \<open>von_neumann_algebra A\<close>
  assumes \<open>von_neumann_algebra B\<close>
  shows \<open>von_neumann_algebra (commutant (commutant (A \<union> B)))\<close>
  using von_neumann_algebra_UNION[where X=\<open>{True,False}\<close> and A=\<open>\<lambda>x. if x then A else B\<close>]
  by (auto simp: assms Un_ac(3))


lemma von_neumann_algebra_commutant: \<open>von_neumann_algebra (commutant A)\<close> if \<open>von_neumann_algebra A\<close>
proof (rule von_neumann_algebraI)
  show \<open>a* \<in> commutant A\<close> if \<open>a \<in> commutant A\<close> for a
    by (smt (verit) Set.basic_monos(7) \<open>von_neumann_algebra A\<close> commutant_adj commutant_antimono double_adj image_iff image_subsetI that von_neumann_algebra_def)
  show \<open>commutant (commutant (commutant A)) \<subseteq> commutant A \<close>
    by simp
qed

lemma von_neumann_algebra_def_sot:
  \<open>von_neumann_algebra \<FF> \<longleftrightarrow> 
      (\<forall>a\<in>\<FF>. a* \<in> \<FF>) \<and> csubspace \<FF> \<and> (\<forall>a\<in>\<FF>. \<forall>b\<in>\<FF>. a o\<^sub>C\<^sub>L b \<in> \<FF>) \<and> id_cblinfun \<in> \<FF> \<and>
      closedin cstrong_operator_topology \<FF>\<close>
proof (unfold von_neumann_algebra_def, intro iffI conjI; elim conjE; assumption?)
  assume comm: \<open>commutant (commutant \<FF>) = \<FF>\<close>
  from comm show \<open>closedin cstrong_operator_topology \<FF>\<close>
    by (metis commutant_sot_closed)
  from comm show \<open>csubspace \<FF>\<close>
    by (metis csubspace_commutant)
  from comm show \<open>\<forall>a\<in>\<FF>. \<forall>b\<in>\<FF>. a o\<^sub>C\<^sub>L b \<in> \<FF>\<close>
    using commutant_mult by blast
  from comm show \<open>id_cblinfun \<in> \<FF>\<close>
    by blast
next
  assume adj: \<open>\<forall>a\<in>\<FF>. a* \<in> \<FF>\<close>
  assume subspace: \<open>csubspace \<FF>\<close>
  assume closed: \<open>closedin cstrong_operator_topology \<FF>\<close>
  assume mult: \<open>\<forall>a\<in>\<FF>. \<forall>b\<in>\<FF>. a o\<^sub>C\<^sub>L b \<in> \<FF>\<close>
  assume id: \<open>id_cblinfun \<in> \<FF>\<close>
  have \<open>commutant (commutant \<FF>) = cstrong_operator_topology closure_of \<FF>\<close>
    apply (rule double_commutant_theorem)
    thm double_commutant_theorem[of \<FF>]
    using subspace subspace mult id adj 
    by simp_all
  also from closed have \<open>\<dots> = \<FF>\<close>
    by (simp add: closure_of_eq)
  finally show \<open>commutant (commutant \<FF>) = \<FF>\<close>
    by -
qed


lemma double_commutant_hull':
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> x* \<in> X\<close>
  shows \<open>commutant (commutant X) = von_neumann_algebra hull X\<close>
proof (rule antisym)
  show \<open>commutant (commutant X) \<subseteq> von_neumann_algebra hull X\<close>
    apply (subst double_commutant_hull)
    apply (rule hull_antimono)
    by (simp add: von_neumann_algebra_def)
  show \<open>von_neumann_algebra hull X \<subseteq> commutant (commutant X)\<close>
    apply (rule hull_minimal)
    by (simp_all add: von_neumann_algebra_def assms commutant_adj_closed)
qed


lemma commutant_one_algebra: \<open>commutant one_algebra = UNIV\<close>
  by (metis commutant_UNIV commutant_empty triple_commutant)

definition tensor_vn (infixr "\<otimes>\<^sub>v\<^sub>N" 70) where
  \<open>tensor_vn X Y = commutant (commutant ((\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` X \<union> (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` Y))\<close>

lemma von_neumann_algebra_adj_image: \<open>von_neumann_algebra X \<Longrightarrow> adj ` X = X\<close>
  by (auto simp: von_neumann_algebra_def intro!: image_eqI[where x=\<open>_*\<close>])

lemma von_neumann_algebra_tensor_vn:
  assumes \<open>von_neumann_algebra X\<close>
  assumes \<open>von_neumann_algebra Y\<close>
  shows \<open>von_neumann_algebra (X \<otimes>\<^sub>v\<^sub>N Y)\<close>
proof (rule von_neumann_algebraI)
  have \<open>adj ` (X \<otimes>\<^sub>v\<^sub>N Y) = commutant (commutant ((\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` adj ` X \<union> (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` adj ` Y))\<close>
    by (simp add: tensor_vn_def commutant_adj image_image image_Un tensor_op_adjoint)
  also have \<open>\<dots> = commutant (commutant ((\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` X \<union> (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` Y))\<close>
    using assms by (simp add: von_neumann_algebra_adj_image)
  also have \<open>\<dots> = X \<otimes>\<^sub>v\<^sub>N Y\<close>
    by (simp add: tensor_vn_def)
  finally show \<open>a* \<in> X \<otimes>\<^sub>v\<^sub>N Y\<close> if \<open>a \<in> X \<otimes>\<^sub>v\<^sub>N Y\<close> for a
    using that by blast
  show \<open>commutant (commutant (X \<otimes>\<^sub>v\<^sub>N Y)) \<subseteq> X \<otimes>\<^sub>v\<^sub>N Y\<close>
    by (simp add: tensor_vn_def)
qed

lemma tensor_vn_one_one[simp]: \<open>one_algebra \<otimes>\<^sub>v\<^sub>N one_algebra = one_algebra\<close>
  apply (simp add: tensor_vn_def one_algebra_def image_image
      tensor_op_scaleC_left tensor_op_scaleC_right)
  by (simp add: commutant_one_algebra commutant_UNIV flip: one_algebra_def)

lemma sandwich_swap_tensor_vn: \<open>sandwich swap_ell2 ` (X \<otimes>\<^sub>v\<^sub>N Y) = Y \<otimes>\<^sub>v\<^sub>N X\<close>
  by (simp add: tensor_vn_def sandwich_unitary_commutant image_Un image_image Un_commute)

lemma tensor_vn_one_left: \<open>one_algebra \<otimes>\<^sub>v\<^sub>N X = (\<lambda>x. id_cblinfun \<otimes>\<^sub>o x) ` X\<close> if \<open>von_neumann_algebra X\<close>
proof -
  have \<open>one_algebra \<otimes>\<^sub>v\<^sub>N X = commutant
     (commutant ((\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` X))\<close>
    apply (simp add: tensor_vn_def one_algebra_def image_image)
    by (metis (no_types, lifting) Un_commute Un_empty_right commutant_UNIV commutant_empty double_commutant_Un_right image_cong one_algebra_def tensor_id tensor_op_scaleC_left)
  also have \<open>\<dots> = (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` commutant (commutant X)\<close>
    by (simp add: amplification_double_commutant_commute')
  also have \<open>\<dots> = (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` X\<close>
    using that von_neumann_algebra_def by blast
  finally show ?thesis
    by -
qed
lemma tensor_vn_one_right: \<open>X \<otimes>\<^sub>v\<^sub>N one_algebra = (\<lambda>x. x \<otimes>\<^sub>o id_cblinfun) ` X\<close> if \<open>von_neumann_algebra X\<close>
proof -
  have \<open>X \<otimes>\<^sub>v\<^sub>N one_algebra = sandwich swap_ell2 ` (one_algebra \<otimes>\<^sub>v\<^sub>N X)\<close>
    by (simp add: sandwich_swap_tensor_vn)
  also have \<open>\<dots> = sandwich swap_ell2 ` (\<lambda>x. id_cblinfun \<otimes>\<^sub>o x) ` X\<close>
    by (simp add: tensor_vn_one_left that)
  also have \<open>\<dots> = (\<lambda>x. x \<otimes>\<^sub>o id_cblinfun) ` X\<close>
    by (simp add: image_image)
  finally show ?thesis
    by -
qed

lemma double_commutant_in_vn_algI: \<open>commutant (commutant X) \<subseteq> Y\<close>
  if \<open>von_neumann_algebra Y\<close> and \<open>X \<subseteq> Y\<close>
  by (metis commutant_antimono that(1) that(2) von_neumann_algebra_def)

lemma von_neumann_algebra_compose:
  assumes \<open>von_neumann_algebra M\<close>
  assumes \<open>x \<in> M\<close> and \<open>y \<in> M\<close>
  shows \<open>x o\<^sub>C\<^sub>L y \<in> M\<close>
  using assms apply (auto simp: von_neumann_algebra_def commutant_def)
  by (metis (no_types, lifting) assms(1) commutant_mult von_neumann_algebra_def)

lemma von_neumann_algebra_id:
  assumes \<open>von_neumann_algebra M\<close>
  shows \<open>id_cblinfun \<in> M\<close>
  using assms by (auto simp: von_neumann_algebra_def)

lemma tensor_vn_UNIV[simp]: \<open>UNIV \<otimes>\<^sub>v\<^sub>N UNIV = (UNIV :: (('a\<times>'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L _) set)\<close>
proof -
  have \<open>(UNIV \<otimes>\<^sub>v\<^sub>N UNIV :: (('a\<times>'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L _) set) = 
        commutant (commutant (range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) \<union> range (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a)))\<close> (is \<open>_ = ?rhs\<close>)
    by (simp add: tensor_vn_def commutant_cspan)
  also have \<open>\<dots> \<supseteq> commutant (commutant {a \<otimes>\<^sub>o b |a b. True})\<close> (is \<open>_ \<supseteq> \<dots>\<close>)
  proof (rule double_commutant_in_vn_algI)
    show vn: \<open>von_neumann_algebra ?rhs\<close>
      by (metis calculation von_neumann_algebra_UNIV von_neumann_algebra_tensor_vn)
    show \<open>{a \<otimes>\<^sub>o b |(a :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L _) (b :: 'b ell2 \<Rightarrow>\<^sub>C\<^sub>L _). True} \<subseteq> ?rhs\<close>
    proof (rule subsetI)
      fix x :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close>
      assume \<open>x \<in> {a \<otimes>\<^sub>o b |a b. True}\<close>
      then obtain a b where \<open>x = a \<otimes>\<^sub>o b\<close>
        by auto
      then have \<open>x = (a \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o b)\<close>
        by (simp add: comp_tensor_op)
      also have \<open>\<dots> \<in> ?rhs\<close>
      proof -
        have \<open>a \<otimes>\<^sub>o id_cblinfun \<in> ?rhs\<close>
          by (auto intro!: double_commutant_grows')
        moreover have \<open>id_cblinfun \<otimes>\<^sub>o b \<in> ?rhs\<close>
          by (auto intro!: double_commutant_grows')
        ultimately show ?thesis
          using commutant_mult by blast
      qed
      finally show \<open>x \<in> ?rhs\<close>
        by -
    qed
  qed
  also have \<open>\<dots> = cstrong_operator_topology closure_of (cspan {a \<otimes>\<^sub>o b |a b. True})\<close>
    apply (rule double_commutant_theorem_span)
      apply (auto simp: comp_tensor_op tensor_op_adjoint)
    using tensor_id[symmetric] by blast+
  also have \<open>\<dots> = UNIV\<close>
    using tensor_op_dense by blast
  finally show ?thesis
    by auto
qed



end