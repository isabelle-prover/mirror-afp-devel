section \<open>\<open>Eigenvalues\<close> -- Material related to eigenvalues and eigenspaces\<close>

theory Eigenvalues
  imports
    Weak_Operator_Topology
    Misc_Tensor_Product_TTS
begin

definition normal_op :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> bool\<close> where
  \<open>normal_op A  \<longleftrightarrow>  A o\<^sub>C\<^sub>L A* = A* o\<^sub>C\<^sub>L A\<close>

definition eigenvalues :: \<open>('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> complex set\<close> where
  \<open>eigenvalues a = {x. eigenspace x a \<noteq> 0}\<close>

definition invariant_subspace :: \<open>'a::complex_inner ccsubspace \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> bool\<close> where
  \<open>invariant_subspace S A \<longleftrightarrow> A *\<^sub>S S \<le> S\<close>

lemma invariant_subspaceI: \<open>A *\<^sub>S S \<le> S \<Longrightarrow> invariant_subspace S A\<close>
  by (simp add: invariant_subspace_def)

definition reducing_subspace :: \<open>'a::complex_inner ccsubspace \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> bool\<close> where
  \<open>reducing_subspace S A \<longleftrightarrow> invariant_subspace S A \<and> invariant_subspace (-S) A\<close>

lemma reducing_subspaceI: \<open>A *\<^sub>S S \<le> S \<Longrightarrow> A *\<^sub>S (-S) \<le> -S \<Longrightarrow> reducing_subspace S A\<close>
  by (simp add: reducing_subspace_def invariant_subspace_def)

lemma reducing_subspace_ortho[simp]: \<open>reducing_subspace (-S) A \<longleftrightarrow> reducing_subspace S A\<close>
  for S :: \<open>'a::chilbert_space ccsubspace\<close>
  by (auto simp: reducing_subspace_def)

lemma invariant_subspace_bot[simp]: \<open>invariant_subspace \<bottom> A\<close>
  by (simp add: invariant_subspaceI) 

lemma invariant_subspace_top[simp]: \<open>invariant_subspace \<top> A\<close>
  by (simp add: invariant_subspaceI) 

lemma reducing_subspace_bot[simp]: \<open>reducing_subspace \<bottom> A\<close>
  by (metis cblinfun_image_bot eq_refl orthogonal_bot orthogonal_spaces_leq_compl reducing_subspaceI) 

lemma reducing_subspace_top[simp]: \<open>reducing_subspace \<top> A\<close>
  by (simp add: reducing_subspace_def)

lemma kernel_uminus[simp]: "kernel (-A) = kernel A"
  for a :: complex and A :: "(_,_) cblinfun"
  by transfer auto

lemma kernel_scaleC': "kernel (a *\<^sub>C A) = (if a = 0 then \<top> else kernel A)"
  for a :: complex and A :: "(_,_) cblinfun"
  by (cases "a = 0") auto

lemma eigenvalues_0[simp]: \<open>eigenvalues (0 :: 'a::{not_singleton,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L 'a) = {0}\<close>
  by (auto simp: eigenvalues_def eigenspace_def kernel_scaleC')

lemma nonzero_ccsubspace_contains_unit_vector:
  assumes \<open>S \<noteq> 0\<close>
  shows \<open>\<exists>\<psi>. \<psi> \<in> space_as_set S \<and> norm \<psi> = 1\<close>
proof -
  from assms 
  obtain \<psi> where \<psi>: \<open>\<psi> \<in> space_as_set S\<close> \<open>\<psi> \<noteq> 0\<close>
    by transfer (auto simp: complex_vector.subspace_0)
  have \<open>sgn \<psi> \<in> space_as_set S\<close>
    using \<psi> by (simp add: complex_vector.subspace_scale scaleR_scaleC sgn_div_norm)
  moreover have \<open>norm (sgn \<psi>) = 1\<close>
    by (simp add: \<open>\<psi> \<noteq> 0\<close> norm_sgn)
  ultimately show ?thesis
    by auto
qed

lemma unit_eigenvector_ex: 
  assumes \<open>x \<in> eigenvalues a\<close>
  shows \<open>\<exists>h. norm h = 1 \<and> a h = x *\<^sub>C h\<close>
proof -
  from assms have \<open>eigenspace x a \<noteq> 0\<close>
    by (simp add: eigenvalues_def)
  then obtain \<psi> where \<psi>_ev: \<open>\<psi> \<in> space_as_set (eigenspace x a)\<close> and \<open>\<psi> \<noteq> 0\<close>
    using nonzero_ccsubspace_contains_unit_vector by force
  define h where \<open>h = sgn \<psi>\<close>
  with \<open>\<psi> \<noteq> 0\<close> have \<open>norm h = 1\<close>
    by (simp add: norm_sgn)
  from \<psi>_ev have \<open>h \<in> space_as_set (eigenspace x a)\<close>
    by (simp add: h_def sgn_in_spaceI)
  then have \<open>a *\<^sub>V h = x *\<^sub>C h\<close>
    unfolding eigenspace_def
    by (transfer' fixing: x) simp
  with \<open>norm h = 1\<close> show ?thesis
    by auto    
qed


lemma eigenvalue_norm_bound:
  assumes \<open>e \<in> eigenvalues a\<close>
  shows \<open>norm e \<le> norm a\<close>
proof -
  from assms obtain h where \<open>norm h = 1\<close> and ah_eh: \<open>a h = e *\<^sub>C h\<close>
    using unit_eigenvector_ex by blast
  have \<open>cmod e = norm (e *\<^sub>C h)\<close>
    by (simp add: \<open>norm h = 1\<close>)
  also have \<open>\<dots> = norm (a h)\<close>
    using ah_eh by presburger
  also have \<open>\<dots> \<le> norm a\<close>
    by (metis \<open>norm h = 1\<close> cblinfun.real.bounded_linear_right mult_cancel_left1 norm_cblinfun.rep_eq onorm)
  finally show \<open>cmod e \<le> norm a\<close>
    by -
qed

lemma eigenvalue_selfadj_real:
  assumes \<open>e \<in> eigenvalues a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>e \<in> \<real>\<close>
proof -
  from assms obtain h where \<open>norm h = 1\<close> and ah_eh: \<open>a h = e *\<^sub>C h\<close>
    using unit_eigenvector_ex by blast
  have \<open>e = h \<bullet>\<^sub>C (e *\<^sub>C h)\<close>
    by (metis \<open>norm h = 1\<close> cinner_simps(6) mult_cancel_left1 norm_one one_cinner_one power2_norm_eq_cinner power2_norm_eq_cinner)
  also have \<open>\<dots> = h \<bullet>\<^sub>C a h\<close>
    by (simp add: ah_eh)
  also from assms(2) have \<open>\<dots> \<in> \<real>\<close>
    using cinner_hermitian_real selfadjoint_def by blast
  finally show \<open>e \<in> \<real>\<close>
    by -
qed

lemma is_Sup_imp_ex_tendsto:
  fixes X :: \<open>'a::{linorder_topology,first_countable_topology} set\<close>
  assumes sup: \<open>is_Sup X l\<close>
  assumes \<open>X \<noteq> {}\<close>
  shows \<open>\<exists>f. range f \<subseteq> X \<and> f \<longlonglongrightarrow> l\<close>
proof (cases \<open>\<exists>x. x < l\<close>)
  case True
  obtain A :: \<open>nat \<Rightarrow> 'a set\<close> where openA: \<open>open (A n)\<close> and lA: \<open>l \<in> A n\<close>
    and fl: \<open>(\<And>n. f n \<in> A n) \<Longrightarrow> f \<longlonglongrightarrow> l\<close> for n f
    by (rule Topological_Spaces.countable_basis[of l]) blast
  obtain f where fAX: \<open>f n \<in> A n \<inter> X\<close> for n
  proof (atomize_elim, intro choice allI)
    fix n :: nat
    from True obtain x where \<open>x < l\<close>
      by blast
    from open_left[OF openA lA this]
    obtain b where \<open>b < l\<close> and bl_A: \<open>{b<..l} \<subseteq> A n\<close>
      by blast
    from sup \<open>b < l\<close> obtain x where \<open>x \<in> X\<close> and \<open>x > b\<close>
      by (meson is_Sup_def leD leI)
    from \<open>x \<in> X\<close> sup have \<open>x \<le> l\<close>
      by (simp add: is_Sup_def)
    from \<open>x \<le> l\<close> and \<open>x > b\<close> and bl_A
    have \<open>x \<in> A n\<close>
      by fastforce
    with \<open>x \<in> X\<close>
    show \<open>\<exists>x. x \<in> A n \<inter> X\<close>
      by blast
  qed
  with fl have \<open>f \<longlonglongrightarrow> l\<close>
    by auto
  moreover from fAX have \<open>range f \<subseteq> X\<close>
    by auto
  ultimately show ?thesis
    by blast
next
  case False
  from \<open>X \<noteq> {}\<close> obtain x where \<open>x \<in> X\<close>
    by blast
  with \<open>is_Sup X l\<close> have \<open>x \<le> l\<close>
    by (simp add: is_Sup_def)
  with False have \<open>x = l\<close>
    using basic_trans_rules(17) by auto
  with \<open>x \<in> X\<close> have \<open>l \<in> X\<close>
    by simp
  define f where \<open>f n = l\<close> for n :: nat
  then have \<open>f \<longlonglongrightarrow> l\<close>
    by (auto intro!: simp: f_def[abs_def])
  moreover from \<open>l \<in> X\<close> have \<open>range f \<subseteq> X\<close>
    by (simp add: f_def)
  ultimately show ?thesis
    by blast
qed

lemma eigenvaluesI:
  assumes \<open>A *\<^sub>V h = e *\<^sub>C h\<close>
  assumes \<open>h \<noteq> 0\<close>
  shows \<open>e \<in> eigenvalues A\<close>
proof -
  from assms have \<open>h \<in> space_as_set (eigenspace e A)\<close>
    by (simp add: eigenspace_def kernel.rep_eq cblinfun.diff_left)
  moreover from \<open>h \<noteq> 0\<close> have \<open>h \<notin> space_as_set \<bottom>\<close>
    by transfer simp
  ultimately have \<open>eigenspace e A \<noteq> \<bottom>\<close>
    by fastforce
  then show ?thesis
    by (simp add: eigenvalues_def)
qed

lemma tendsto_diff_const_left_rewrite:
  fixes c d :: \<open>'a::{topological_group_add, ab_group_add}\<close>
  assumes \<open>((\<lambda>x. f x) \<longlongrightarrow> c - d) F\<close>
  shows \<open>((\<lambda>x. c - f x) \<longlongrightarrow> d) F\<close>
  by (auto intro!: assms tendsto_eq_intros)

lemma not_not_singleton_no_eigenvalues:
  fixes a :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>\<not> class.not_singleton TYPE('a)\<close>
  shows \<open>eigenvalues a = {}\<close>
proof (rule equals0I)
  fix e assume \<open>e \<in> eigenvalues a\<close>
  then have \<open>eigenspace e a \<noteq> \<bottom>\<close>
    by (simp add: eigenvalues_def) 
  then obtain h where \<open>norm h = 1\<close> and \<open>h \<in> space_as_set (eigenspace e a)\<close>
    using nonzero_ccsubspace_contains_unit_vector by auto 
  from assms have \<open>h = 0\<close>
    by (rule not_not_singleton_zero)
  with \<open>norm h = 1\<close>
  show False
    by simp
qed

lemma cblinfun_cinner_eq0I:
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>\<And>h. h \<bullet>\<^sub>C a h = 0\<close>
  shows \<open>a = 0\<close>
  by (rule cblinfun_cinner_eqI) (use assms in simp)

lemma normal_op_iff_adj_same_norms:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition II.2.16\<close>
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  shows \<open>normal_op a \<longleftrightarrow> (\<forall>h. norm (a h) = norm ((a*) h))\<close>
proof -
  have aux: \<open>(\<And>h. a h = b h) ==> (\<forall>h. a h = (0::complex)) \<longleftrightarrow> (\<forall>h. b h = (0::real))\<close> for a :: \<open>'a \<Rightarrow> complex\<close> and b :: \<open>'a \<Rightarrow> real\<close>
    by simp
  have \<open>normal_op a \<longleftrightarrow> (a* o\<^sub>C\<^sub>L a) - (a o\<^sub>C\<^sub>L a*) = 0\<close>
    using normal_op_def by force
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>h. h \<bullet>\<^sub>C ((a* o\<^sub>C\<^sub>L a) - (a o\<^sub>C\<^sub>L a*)) h = 0)\<close>
    by (auto intro!: cblinfun_cinner_eqI simp: cblinfun.diff_left cinner_diff_right
        simp flip: cblinfun_apply_cblinfun_compose)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>h. (norm (a h))\<^sup>2 - (norm ((a*) h))\<^sup>2 = 0)\<close>
  proof (rule aux)
    fix h
    have \<open>(norm (a *\<^sub>V h))\<^sup>2 - (norm (a* *\<^sub>V h))\<^sup>2
        = (a *\<^sub>V h) \<bullet>\<^sub>C (a *\<^sub>V h) - (a* *\<^sub>V h) \<bullet>\<^sub>C (a* *\<^sub>V h)\<close>
      by (simp add: of_real_diff flip: cdot_square_norm of_real_power)
    also have \<open>\<dots> = h \<bullet>\<^sub>C ((a* o\<^sub>C\<^sub>L a) - (a o\<^sub>C\<^sub>L a*)) h\<close>
      by (simp add: cblinfun.diff_left cinner_diff_right cinner_adj_left
          cinner_adj_right flip: cinner_adj_left)
    finally show \<open>h \<bullet>\<^sub>C ((a* o\<^sub>C\<^sub>L a) - (a o\<^sub>C\<^sub>L a*)) h = (norm (a *\<^sub>V h))\<^sup>2 - (norm (a* *\<^sub>V h))\<^sup>2\<close>
      by simp
  qed
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>h. norm (a h) = norm ((a*) h))\<close>
    by simp
  finally show ?thesis.
qed


lemma normal_op_same_eigenspace_as_adj:
  \<comment> \<open>Shown inside the proof of \<^cite>\<open>"Proposition II.5.6" in conway2013course\<close>\<close>
  assumes \<open>normal_op a\<close>
  shows \<open>eigenspace l a = eigenspace (cnj l) (a* )\<close>
proof -
  from \<open>normal_op a\<close>
  have \<open>normal_op (a - l *\<^sub>C id_cblinfun)\<close>
    by (auto intro!: simp: normal_op_def cblinfun_compose_minus_left
        cblinfun_compose_minus_right adj_minus scaleC_diff_right)
  then have *: \<open>norm ((a - l *\<^sub>C id_cblinfun) h) = norm (((a - l *\<^sub>C id_cblinfun)*) h)\<close> for h
    using normal_op_iff_adj_same_norms by blast
  show ?thesis
  proof (rule ccsubspace_eqI)
    fix h
    have \<open>h \<in> space_as_set (eigenspace l a) \<longleftrightarrow> norm ((a - l *\<^sub>C id_cblinfun) h) = 0\<close>
      by (simp add: eigenspace_def kernel_member_iff)
    also have \<open>\<dots> \<longleftrightarrow> norm (((a*) - cnj l *\<^sub>C id_cblinfun) h) = 0\<close>
      by (simp add: "*" adj_minus)
    also have \<open>\<dots> \<longleftrightarrow> h \<in> space_as_set (eigenspace (cnj l) (a*))\<close>
      by (simp add: eigenspace_def kernel_member_iff)
    finally show \<open>h \<in> space_as_set (eigenspace l a) \<longleftrightarrow> h \<in> space_as_set (eigenspace (cnj l) (a*))\<close>.
  qed
qed

lemma normal_op_adj_eigenvalues: 
  assumes \<open>normal_op a\<close>
  shows \<open>eigenvalues (a*) = cnj ` eigenvalues a\<close>
  by (auto intro!: complex_cnj_cnj[symmetric] image_eqI
      simp: eigenvalues_def assms normal_op_same_eigenspace_as_adj)

lemma invariant_subspace_iff_PAP:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition II.3.7 (b)\<close>
  \<open>invariant_subspace S A \<longleftrightarrow> Proj S o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L Proj S = A o\<^sub>C\<^sub>L Proj S\<close>
proof -
  define S' where \<open>S' = space_as_set S\<close>
  have \<open>invariant_subspace S A \<longleftrightarrow> (\<forall>h\<in>S'. A h \<in> S')\<close>
  proof safe
    fix h assume A: "invariant_subspace S A" and h: "h \<in> S'"
    from h have "A *\<^sub>V h \<in> space_as_set (A *\<^sub>S S)"
      using cblinfun_apply_in_image'[of h S A] unfolding S'_def by auto
    also have "space_as_set (A *\<^sub>S S) \<subseteq> S'"
      using A unfolding S'_def invariant_subspace_def less_eq_ccsubspace_def by auto
    finally show "A *\<^sub>V h \<in> S'" .
  next
    assume *: "\<forall>h\<in>S'. A *\<^sub>V h \<in> S'"
    hence "A *\<^sub>S S \<le> S"
      unfolding S'_def using cblinfun_image_less_eqI by blast
    thus "invariant_subspace S A"
      unfolding invariant_subspace_def less_eq_ccsubspace_def map_fun_def o_def id_def .
  qed
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>h. A *\<^sub>V Proj S *\<^sub>V h \<in> S')\<close>
    by (metis (no_types, lifting) Proj_fixes_image Proj_range S'_def cblinfun_apply_in_image)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>h. Proj S *\<^sub>V A *\<^sub>V Proj S *\<^sub>V h = A *\<^sub>V Proj S *\<^sub>V h)\<close>
    using Proj_fixes_image S'_def space_as_setI_via_Proj by blast
  also have \<open>\<dots> \<longleftrightarrow> Proj S o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L Proj S = A o\<^sub>C\<^sub>L Proj S\<close>
    by (auto intro!: cblinfun_eqI simp: 
        simp flip: cblinfun_apply_cblinfun_compose cblinfun_compose_assoc)
  finally show ?thesis
    by -
qed

lemma reducing_iff_PA:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition II.3.7 (e)\<close>
  \<open>reducing_subspace S A \<longleftrightarrow> Proj S o\<^sub>C\<^sub>L A = A o\<^sub>C\<^sub>L Proj S\<close>
proof (rule iffI)
  assume red: \<open>reducing_subspace S A\<close>
  define P where \<open>P = Proj S\<close>
  from red have AP: \<open>P o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L P = A o\<^sub>C\<^sub>L P\<close>
    by (simp add: invariant_subspace_iff_PAP reducing_subspace_def P_def) 
  from red have \<open>reducing_subspace (- S) A\<close>
    by simp 
  then have \<open>(id_cblinfun - P) o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L (id_cblinfun - P) = A o\<^sub>C\<^sub>L (id_cblinfun - P)\<close>
    using invariant_subspace_iff_PAP[of \<open>- S\<close>] reducing_subspace_def P_def Proj_ortho_compl
    by metis
  then have \<open>P o\<^sub>C\<^sub>L A = P o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L P\<close>
    by (simp add: cblinfun_compose_minus_left cblinfun_compose_minus_right) 
  with AP show \<open>P o\<^sub>C\<^sub>L A = A o\<^sub>C\<^sub>L P\<close>
    by simp
next
  define P where \<open>P = Proj S\<close>
  assume \<open>P o\<^sub>C\<^sub>L A = A o\<^sub>C\<^sub>L P\<close>
  then have \<open>P o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L P = A o\<^sub>C\<^sub>L P o\<^sub>C\<^sub>L P\<close>
    by simp
  then have \<open>P o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L P = A o\<^sub>C\<^sub>L P\<close>
    by (metis P_def Proj_idempotent cblinfun_assoc_left(1)) 
  then have \<open>invariant_subspace S A\<close>
    by (simp add: P_def invariant_subspace_iff_PAP) 
  have \<open>(id_cblinfun - P) o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L (id_cblinfun - P) = A o\<^sub>C\<^sub>L (id_cblinfun - P)\<close>
    by (metis (no_types, opaque_lifting) P_def Proj_idempotent Proj_ortho_compl \<open>P o\<^sub>C\<^sub>L A = A o\<^sub>C\<^sub>L P\<close> cblinfun_assoc_left(1) cblinfun_compose_id_left cblinfun_compose_minus_left cblinfun_compose_minus_right) 
  then have \<open>invariant_subspace (- S) A\<close>
    by (simp add: P_def Proj_ortho_compl invariant_subspace_iff_PAP) 
  with \<open>invariant_subspace S A\<close>
  show \<open>reducing_subspace S A\<close>
    using reducing_subspace_def by blast 
qed

lemma reducing_iff_also_adj_invariant:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition II.3.7 (g)\<close>
  shows \<open>reducing_subspace S A \<longleftrightarrow> invariant_subspace S A \<and> invariant_subspace S (A*)\<close>
proof (intro iffI conjI; (erule conjE)?)
  assume \<open>invariant_subspace S A\<close> and \<open>invariant_subspace S (A*)\<close>
  have \<open>invariant_subspace (- S) A\<close>
  proof (intro invariant_subspaceI cblinfun_image_less_eqI)
    fix h assume \<open>h \<in> space_as_set (- S)\<close>
    show \<open>A *\<^sub>V h \<in> space_as_set (- S)\<close>
    proof (unfold uminus_ccsubspace.rep_eq, intro orthogonal_complementI)
      fix g assume \<open>g \<in> space_as_set S\<close>
      with \<open>invariant_subspace S (A*)\<close> have \<open>(A*) g \<in> space_as_set S\<close>
        by (metis Proj_compose_cancelI Proj_range cblinfun_apply_in_image' cblinfun_fixes_range invariant_subspace_def space_as_setI_via_Proj) 
      have \<open>A h \<bullet>\<^sub>C g = h \<bullet>\<^sub>C (A*) g\<close>
        by (simp add: cinner_adj_right)
      also from \<open>(A*) g \<in> space_as_set S\<close> and \<open>h \<in> space_as_set (- S)\<close>
      have \<open>\<dots> = 0\<close>
        using orthogonal_spaces_def orthogonal_spaces_leq_compl by blast 
      finally show \<open>A h \<bullet>\<^sub>C g = 0\<close>
        by blast
    qed
  qed
  with \<open>invariant_subspace S A\<close>
  show \<open>reducing_subspace S A\<close>
    using reducing_subspace_def by blast 
next
  assume \<open>reducing_subspace S A\<close>
  then show \<open>invariant_subspace S A\<close>
    using reducing_subspace_def by blast 
  show \<open>invariant_subspace S (A*)\<close>
    by (metis \<open>reducing_subspace S A\<close> adj_Proj adj_cblinfun_compose reducing_iff_PA reducing_subspace_def) 
qed

lemma eigenspace_is_reducing:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition II.5.6\<close>
  assumes \<open>normal_op a\<close>
  shows \<open>reducing_subspace (eigenspace l a) a\<close>
proof (unfold reducing_iff_also_adj_invariant invariant_subspace_def,
    intro conjI cblinfun_image_less_eqI subsetI)
  fix h
  assume h_eigen: \<open>h \<in> space_as_set (eigenspace l a)\<close>
  then have \<open>a h = l *\<^sub>C h\<close>
    by (simp add: eigenspace_memberD)
  also have \<open>\<dots> \<in> space_as_set (eigenspace l a)\<close>
    by (simp add: Proj_fixes_image cblinfun.scaleC_right h_eigen space_as_setI_via_Proj)
  finally show \<open>a h \<in> space_as_set (eigenspace l a)\<close>.
next
  fix h
  assume h_eigen: \<open>h \<in> space_as_set (eigenspace l a)\<close>
  then have \<open>h \<in> space_as_set (eigenspace (cnj l) (a*))\<close>
    by (simp add: assms normal_op_same_eigenspace_as_adj)
  then have \<open>(a*) h = cnj l *\<^sub>C h\<close>
    by (simp add: eigenspace_memberD)
  also have \<open>\<dots> \<in> space_as_set (eigenspace l a)\<close>
    by (simp add: Proj_fixes_image cblinfun.scaleC_right h_eigen space_as_setI_via_Proj)
  finally show \<open>(a*) h \<in> space_as_set (eigenspace l a)\<close>.
qed

lemma invariant_subspace_Inf:
  assumes \<open>\<And>S. S \<in> M \<Longrightarrow> invariant_subspace S a\<close>
  shows \<open>invariant_subspace (\<Sqinter>M) a\<close>
proof (rule invariant_subspaceI)
  have \<open>a *\<^sub>S \<Sqinter> M \<le> (\<Sqinter>S\<in>M. a *\<^sub>S S)\<close>
    using cblinfun_image_INF_leq[where U=a and V=id and X=M] by simp
  also have \<open>\<dots> \<le> (\<Sqinter>S\<in>M. S)\<close>
    by (rule INF_superset_mono, simp) (use assms in \<open>auto simp: invariant_subspace_def\<close>)
  also have \<open>\<dots> = \<Sqinter>M\<close>
    by simp
  finally show \<open>a *\<^sub>S \<Sqinter> M \<le> \<Sqinter> M\<close> .
qed

lemma invariant_subspace_INF:
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> invariant_subspace (S x) a\<close>
  shows \<open>invariant_subspace (\<Sqinter>x\<in>X. S x) a\<close>
  by (smt (verit) assms imageE invariant_subspace_Inf)

lemma invariant_subspace_Sup:
  assumes \<open>\<And>S. S \<in> M \<Longrightarrow> invariant_subspace S a\<close>
  shows \<open>invariant_subspace (\<Squnion>M) a\<close>
proof -
  have *: \<open>a ` cspan (\<Union>S\<in>M. space_as_set S) \<subseteq> space_as_set (\<Squnion>M)\<close>
  proof (rule image_subsetI)
    fix h
    assume \<open>h \<in> cspan (\<Union>S\<in>M. space_as_set S)\<close>
    then obtain F r where \<open>h = (\<Sum>g\<in>F. r g *\<^sub>C g)\<close> and F_in_union: \<open>F \<subseteq> (\<Union>S\<in>M. space_as_set S)\<close>
      by (auto intro!: simp: complex_vector.span_explicit)
    then have \<open>a h = (\<Sum>g\<in>F. r g *\<^sub>C a g)\<close>
      by (simp add: cblinfun.scaleC_right cblinfun.sum_right)
    also have \<open>\<dots> \<in> space_as_set (\<Squnion>M)\<close>
    proof (rule complex_vector.subspace_sum)
      show \<open>csubspace (space_as_set (\<Squnion> M))\<close>
        by simp
      fix g assume \<open>g \<in> F\<close>
      then obtain S where \<open>S \<in> M\<close> and \<open>g \<in> space_as_set S\<close>
        using F_in_union by auto
      from assms[OF \<open>S \<in> M\<close>] \<open>g \<in> space_as_set S\<close>
      have \<open>a g \<in> space_as_set S\<close>
        by (simp add: Set.basic_monos(7) cblinfun_apply_in_image' invariant_subspace_def less_eq_ccsubspace.rep_eq)
      also from \<open>S \<in> M\<close>have \<open>\<dots> \<subseteq> space_as_set (\<Squnion> M)\<close>
        by (meson Sup_upper less_eq_ccsubspace.rep_eq)
      finally show \<open>r g *\<^sub>C (a g) \<in> space_as_set (\<Squnion> M)\<close>
        by (simp add: complex_vector.subspace_scale)
    qed
    finally show \<open>a h \<in> space_as_set (\<Squnion>M)\<close>.
  qed
  have \<open>space_as_set (a *\<^sub>S \<Squnion>M) = closure (a ` closure (cspan (\<Squnion>S\<in>M. space_as_set S)))\<close>
    by (metis Sup_ccsubspace.rep_eq cblinfun_image.rep_eq)
  also have \<open>\<dots> = closure (a ` cspan (\<Squnion>S\<in>M. space_as_set S))\<close>
    by (rule closure_bounded_linear_image_subset_eq)
       (simp add: cblinfun.real.bounded_linear_right)
  also from * have \<open>\<dots> \<subseteq> closure (space_as_set (\<Squnion>M))\<close>
    by (meson closure_mono)
  also have \<open>\<dots> = space_as_set (\<Squnion>M)\<close>
    by force
  finally have \<open>a *\<^sub>S \<Squnion>M \<le> \<Squnion>M\<close>
    by (simp add: less_eq_ccsubspace.rep_eq)
  then show ?thesis
    using invariant_subspaceI by blast
qed

lemma invariant_subspace_SUP:
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> invariant_subspace (S x) a\<close>
  shows \<open>invariant_subspace (\<Squnion>x\<in>X. S x) a\<close>
  by (metis (mono_tags, lifting) assms imageE invariant_subspace_Sup)

lemma reducing_subspace_Inf:
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>\<And>S. S \<in> M \<Longrightarrow> reducing_subspace S a\<close>
  shows \<open>reducing_subspace (\<Sqinter>M) a\<close>
  using assms
  by (auto intro!: invariant_subspace_Inf invariant_subspace_SUP
      simp add: reducing_subspace_def uminus_Inf invariant_subspace_Inf)

lemma reducing_subspace_INF:
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> reducing_subspace (S x) a\<close>
  shows \<open>reducing_subspace (\<Sqinter>x\<in>X. S x) a\<close>
  by (metis (mono_tags, lifting) assms imageE reducing_subspace_Inf)

lemma reducing_subspace_Sup:
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>\<And>S. S \<in> M \<Longrightarrow> reducing_subspace S a\<close>
  shows \<open>reducing_subspace (\<Squnion>M) a\<close>
  using assms
  by (auto intro!: invariant_subspace_Sup invariant_subspace_INF
      simp add: reducing_subspace_def uminus_Sup invariant_subspace_Inf)

lemma reducing_subspace_SUP:
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> reducing_subspace (S x) a\<close>
  shows \<open>reducing_subspace (\<Squnion>x\<in>X. S x) a\<close>
  by (metis (mono_tags, lifting) assms imageE reducing_subspace_Sup)

lemma selfadjoint_imp_normal: \<open>normal_op a\<close> if \<open>selfadjoint a\<close>
  using that by (simp add: selfadjoint_def normal_op_def)

lemma eigenspaces_orthogonal:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition II.5.7\<close>
  assumes \<open>e \<noteq> f\<close>
  assumes \<open>normal_op a\<close>
  shows \<open>orthogonal_spaces (eigenspace e a) (eigenspace f a)\<close>
proof (intro orthogonal_spaces_def[THEN iffD2] ballI)
  fix g h assume g_eigen: \<open>g \<in> space_as_set (eigenspace e a)\<close> and h_eigen: \<open>h \<in> space_as_set (eigenspace f a)\<close>
  with \<open>normal_op a\<close> have \<open>g \<in> space_as_set (eigenspace (cnj e) (a*))\<close>
    by (simp add: normal_op_same_eigenspace_as_adj) 
  then have a_adj_g: \<open>(a*) g = cnj e *\<^sub>C g\<close>
    using eigenspace_memberD by blast 
  from h_eigen have a_h: \<open>a h = f *\<^sub>C h\<close>
    by (simp add: eigenspace_memberD) 
  have \<open>f * (g \<bullet>\<^sub>C h) = g \<bullet>\<^sub>C a h\<close>
    by (simp add: a_h) 
  also have \<open>\<dots> = (a*) g \<bullet>\<^sub>C h\<close>
    by (simp add: cinner_adj_left) 
  also have \<open>\<dots> = e * (g \<bullet>\<^sub>C h)\<close>
    using a_adj_g by auto 
  finally have \<open>(f - e) * (g \<bullet>\<^sub>C h) = 0\<close>
    by (simp add: vector_space_over_itself.scale_left_diff_distrib) 
  with \<open>e \<noteq> f\<close> show \<open>g \<bullet>\<^sub>C h = 0\<close>
    by simp 
qed

definition largest_eigenvalue :: \<open>('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> complex\<close> where
  \<open>largest_eigenvalue a = 
    (if \<exists>x. x \<in> eigenvalues a \<and> (\<forall>y \<in> eigenvalues a. cmod x \<ge> cmod y) then
    SOME x. x \<in> eigenvalues a \<and> (\<forall>y \<in> eigenvalues a. cmod x \<ge> cmod y) else 0)\<close>



lemma largest_eigenvalue_0_aux: 
  \<open>largest_eigenvalue (0 :: 'a::{not_singleton,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L 'a) = 0\<close>
proof -
  let ?zero = \<open>0 :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  define e where \<open>e = (SOME x. x \<in> eigenvalues ?zero \<and> (\<forall>y \<in> eigenvalues ?zero. cmod x \<ge> cmod y))\<close>
  have \<open>\<exists>e. e \<in> eigenvalues ?zero \<and> (\<forall>y\<in>eigenvalues ?zero. cmod y \<le> cmod e)\<close> (is \<open>\<exists>e. ?P e\<close>)
    by (auto intro!: exI[of _ 0])
  then have \<open>?P e\<close>
    unfolding e_def
    by (rule someI_ex)
  then have \<open>e = 0\<close>
    by simp
  then show \<open>largest_eigenvalue ?zero = 0\<close>
    by (simp add: largest_eigenvalue_def)
qed

lemma largest_eigenvalue_0[simp]:
  \<open>largest_eigenvalue (0 :: 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'a) = 0\<close>
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  show ?thesis
    using complex_normed_vector_axioms True
    by (rule largest_eigenvalue_0_aux[internalize_sort' 'a])
next
  case False
  then have \<open>eigenvalues (0 :: 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'a) = {}\<close>
    by (rule not_not_singleton_no_eigenvalues)
  then show ?thesis
    by (auto simp add: largest_eigenvalue_def)
qed

hide_fact largest_eigenvalue_0_aux


lemma eigenvalues_nonneg:
  assumes \<open>a \<ge> 0\<close> and \<open>v \<in> eigenvalues a\<close>
  shows \<open>v \<ge> 0\<close>
proof -
  from assms obtain h where \<open>norm h = 1\<close> and ahvh: \<open>a *\<^sub>V h = v *\<^sub>C h\<close>
    using unit_eigenvector_ex by blast
  have \<open>0 \<le> h \<bullet>\<^sub>C a h\<close>
    by (simp add: assms(1) cinner_pos_if_pos)
  also have \<open>\<dots> = v * (h \<bullet>\<^sub>C h)\<close>
    by (simp add: ahvh)
  also have \<open>\<dots> = v\<close>
    using \<open>norm h = 1\<close> cnorm_eq_1 by auto
  finally show \<open>v \<ge> 0\<close>
    by blast
qed



end