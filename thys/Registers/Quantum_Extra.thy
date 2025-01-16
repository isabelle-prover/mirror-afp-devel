section \<open>Derived facts about quantum registers\<close>

theory Quantum_Extra
  imports
    Laws_Quantum
    Quantum
begin

no_notation meet (infixl "\<sqinter>\<index>" 70)
no_notation Group.mult (infixl "\<otimes>\<index>" 70)
no_notation Order.top ("\<top>\<index>")
unbundle lattice_syntax
unbundle register_syntax
unbundle cblinfun_syntax

lemma zero_not_register[simp]: \<open>~ register (\<lambda>_. 0)\<close>
  unfolding register_def by simp

lemma register_pair_is_register_converse:
  \<open>register (F;G) \<Longrightarrow> register F\<close> \<open>register (F;G) \<Longrightarrow> register G\<close>
  using [[simproc del: Laws_Quantum.compatibility_warn]]
   apply (cases \<open>register F\<close>)
    apply (auto simp: register_pair_def)[2]
  apply (cases \<open>register G\<close>)
  by (auto simp: register_pair_def)[2]

lemma register_id'[simp]: \<open>register (\<lambda>x. x)\<close>
  using register_id by (simp add: id_def)

lemma compatible_proj_intersect:
  (* I think this also holds without is_Proj premises, but my proof ideas use the Penrose-Moore 
     pseudoinverse or simultaneous diagonalization and we do not have an existence theorem for either. *)
  assumes "compatible R S" and "is_Proj a" and "is_Proj b"
  shows "(R a *\<^sub>S \<top>) \<sqinter> (S b *\<^sub>S \<top>) = ((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>)"
proof (rule antisym)
  have "((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>) \<le> (S b *\<^sub>S \<top>)"
    apply (subst swap_registers[OF assms(1)])
    by (simp add: cblinfun_compose_image cblinfun_image_mono)
  moreover have "((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>) \<le> (R a *\<^sub>S \<top>)"
    by (simp add: cblinfun_compose_image cblinfun_image_mono)
  ultimately show \<open>((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>) \<le> (R a *\<^sub>S \<top>) \<sqinter> (S b *\<^sub>S \<top>)\<close>
    by auto

  have "is_Proj (R a)"
    using assms(1) assms(2) compatible_register1 register_projector by blast
  have "is_Proj (S b)"
    using assms(1) assms(3) compatible_register2 register_projector by blast
  show \<open>(R a *\<^sub>S \<top>) \<sqinter> (S b *\<^sub>S \<top>) \<le> (R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>\<close>
  proof (unfold less_eq_ccsubspace.rep_eq, rule subsetI)
    fix \<psi>
    assume asm: \<open>\<psi> \<in> space_as_set ((R a *\<^sub>S \<top>) \<sqinter> (S b *\<^sub>S \<top>))\<close>
    then have \<open>\<psi> \<in> space_as_set (R a *\<^sub>S \<top>)\<close>
      by auto
    then have R: \<open>R a *\<^sub>V \<psi> = \<psi>\<close>
      using \<open>is_Proj (R a)\<close> cblinfun_fixes_range is_Proj_algebraic by blast
    from asm have \<open>\<psi> \<in> space_as_set (S b *\<^sub>S \<top>)\<close>
      by auto
    then have S: \<open>S b *\<^sub>V \<psi> = \<psi>\<close>
      using \<open>is_Proj (S b)\<close> cblinfun_fixes_range is_Proj_algebraic by blast
    from R S have \<open>\<psi> = (R a o\<^sub>C\<^sub>L S b) *\<^sub>V \<psi>\<close>
      by (simp add: cblinfun_apply_cblinfun_compose)
    also have \<open>\<dots> \<in> space_as_set ((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>)\<close>
      apply simp by (metis R S calculation cblinfun_apply_in_image)
    finally show \<open>\<psi> \<in> space_as_set ((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>)\<close>
      by -
  qed
qed

lemma compatible_proj_mult:
  assumes "compatible R S" and "is_Proj a" and "is_Proj b"
  shows "is_Proj (R a o\<^sub>C\<^sub>L S b)"
proof -
  have aux: \<open>\<forall>a b. R a o\<^sub>C\<^sub>L S b = S b o\<^sub>C\<^sub>L R a \<Longrightarrow> S b o\<^sub>C\<^sub>L R a o\<^sub>C\<^sub>L (S b o\<^sub>C\<^sub>L R a) = S b o\<^sub>C\<^sub>L R a\<close>
    using assms
    by (metis (no_types, lifting) cblinfun_compose_assoc register_mult is_Proj_algebraic compatible_def)
  show ?thesis
    using [[simproc del: Laws_Quantum.compatibility_warn]]
    using assms unfolding is_Proj_algebraic compatible_def
    by (auto simp add: assms is_proj_selfadj register_projector aux)
qed

lemma sandwich_tensor: 
  fixes a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close> and b :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> 
  assumes [simp]: \<open>unitary a\<close> \<open>unitary b\<close>
  shows "(*\<^sub>V) (sandwich (a \<otimes>\<^sub>o b)) = sandwich a \<otimes>\<^sub>r sandwich b"
  apply (rule tensor_extensionality)
  by (auto simp: unitary_sandwich_register sandwich_apply register_tensor_is_register
      comp_tensor_op tensor_op_adjoint unitary_tensor_op intro!: register_preregister unitary_sandwich_register)

lemma sandwich_grow_left:
  fixes a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
  assumes "unitary a"
  shows "sandwich a \<otimes>\<^sub>r id = sandwich (a \<otimes>\<^sub>o id_cblinfun)"
  by (simp add: unitary_sandwich_register sandwich_tensor assms id_def)

lemma register_sandwich: \<open>register F \<Longrightarrow> F (sandwich a b) = sandwich (F a) (F b)\<close>
  by (smt (verit, del_insts) register_def sandwich_apply)

lemma assoc_ell2_sandwich: \<open>assoc = sandwich assoc_ell2\<close>
  apply (rule tensor_extensionality3')
    apply (simp_all add: unitary_sandwich_register)[2]
  apply (rule equal_ket)
  apply (case_tac x)
  by (simp add: sandwich_apply assoc_apply cblinfun_apply_cblinfun_compose tensor_op_ell2 assoc_ell2_tensor assoc_ell2'_tensor
      flip: tensor_ell2_ket)

lemma assoc_ell2'_sandwich: \<open>assoc' = sandwich (assoc_ell2*)\<close>
  apply (rule tensor_extensionality3)
    apply (simp_all add: unitary_sandwich_register)[2]
  apply (rule equal_ket)
  apply (case_tac x)
  by (simp add: sandwich_apply assoc'_apply cblinfun_apply_cblinfun_compose tensor_op_ell2 assoc_ell2_tensor assoc_ell2'_tensor 
           flip: tensor_ell2_ket)

lemma swap_sandwich: "swap = sandwich Uswap"
  apply (rule tensor_extensionality)
    apply (auto simp: sandwich_apply unitary_sandwich_register)[2]
  apply (rule tensor_ell2_extensionality)
  by (simp add: sandwich_apply cblinfun_apply_cblinfun_compose tensor_op_ell2)

lemma id_tensor_sandwich: 
  fixes a :: "'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::finite ell2"
  assumes "unitary a"
  shows "id \<otimes>\<^sub>r sandwich a = sandwich (id_cblinfun \<otimes>\<^sub>o a)"
  apply (rule tensor_extensionality) 
  using assms
  by (auto simp: register_tensor_is_register comp_tensor_op sandwich_apply tensor_op_adjoint unitary_sandwich_register
      intro!: register_preregister unitary_sandwich_register unitary_tensor_op)

lemma compatible_selfbutter_join:
  assumes [register]: "compatible R S"
  shows "R (selfbutter \<psi>) o\<^sub>C\<^sub>L S (selfbutter \<phi>) = (R; S) (selfbutter (\<psi> \<otimes>\<^sub>s \<phi>))"
  apply (subst register_pair_apply[symmetric, where F=R and G=S])
  using assms by (auto simp: tensor_butterfly)

lemma register_mult':
  assumes \<open>register F\<close>
  shows \<open>F a *\<^sub>V F b *\<^sub>V c = F (a o\<^sub>C\<^sub>L b) *\<^sub>V c\<close>
  by (simp add: assms lift_cblinfun_comp(4) register_mult)

lemma register_scaleC:
  assumes \<open>register F\<close> shows \<open>F (c *\<^sub>C a) = c *\<^sub>C F a\<close>
  using assms [[simproc del: Laws_Quantum.compatibility_warn]] 
  unfolding register_def
  by (simp add: bounded_clinear.clinear clinear.scaleC)

lemma register_adjoint: "F (a*) = (F a)*" if \<open>register F\<close>
  using register_def that by blast

lemma register_finite_dim: \<open>register F \<longleftrightarrow> clinear F \<and> F id_cblinfun = id_cblinfun \<and> (\<forall>a b. F (a o\<^sub>C\<^sub>L b) = F a o\<^sub>C\<^sub>L F b) \<and> (\<forall>a. F (a*) = F a*)\<close>
  for F :: \<open>'a::finite update \<Rightarrow> 'b::finite update\<close>
    (* I conjecture that this holds even when only 'a is finite. *)
proof
  assume \<open>register F\<close>
  then show \<open>clinear F \<and> F id_cblinfun = id_cblinfun \<and> (\<forall>a b. F (a o\<^sub>C\<^sub>L b) = F a o\<^sub>C\<^sub>L F b) \<and> (\<forall>a. F (a*) = F a*)\<close>
    unfolding register_def
    by (auto simp add: bounded_clinear_def)
next
  assume asm: \<open>clinear F \<and> F id_cblinfun = id_cblinfun \<and> (\<forall>a b. F (a o\<^sub>C\<^sub>L b) = F a o\<^sub>C\<^sub>L F b) \<and> (\<forall>a. F (a*) = F a*)\<close>
  then have \<open>clinear F\<close>
    by simp
  then have \<open>bounded_clinear F\<close>
    by simp
  then have \<open>continuous_map euclidean euclidean F\<close>
    by (auto intro!: continuous_at_imp_continuous_on clinear_continuous_at)
  then have wstar: \<open>continuous_map weak_star_topology weak_star_topology F\<close>
    by simp
  from asm \<open>bounded_clinear F\<close> wstar
  show \<open>register F\<close>
    unfolding register_def by simp
qed

unbundle no lattice_syntax
unbundle no register_syntax
unbundle no cblinfun_syntax

end

