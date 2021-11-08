section \<open>Derived facts about quantum registers\<close>

theory Quantum_Extra
  imports
    Laws_Quantum
    Quantum
begin

no_notation meet (infixl "\<sqinter>\<index>" 70)
no_notation Group.mult (infixl "\<otimes>\<index>" 70)
no_notation Order.top ("\<top>\<index>")
unbundle register_notation
unbundle cblinfun_notation

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

lemma register_projector:
  assumes "register F"
  assumes "is_Proj a"
  shows "is_Proj (F a)"
  using assms unfolding register_def is_Proj_algebraic by metis

lemma register_unitary:
  assumes "register F"
  assumes "unitary a"
  shows "unitary (F a)"
  using assms by (smt (verit, best) register_def unitary_def)

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
  proof (unfold less_eq_ccsubspace.rep_eq, rule)
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
  using [[simproc del: Laws_Quantum.compatibility_warn]]
  using assms unfolding is_Proj_algebraic compatible_def
  apply auto
   apply (metis (no_types, lifting) cblinfun_compose_assoc register_mult)
  by (simp add: assms(2) assms(3) is_proj_selfadj register_projector)

lemma unitary_sandwich_register: \<open>unitary a \<Longrightarrow> register (sandwich a)\<close>
  unfolding register_def
  apply (auto simp: sandwich_def)
   apply (metis (no_types, lifting) cblinfun_assoc_left(1) cblinfun_compose_id_right unitaryD1)
  by (simp add: lift_cblinfun_comp(2))

lemma sandwich_tensor: 
  fixes a :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close> and b :: \<open>'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> 
  assumes \<open>unitary a\<close> \<open>unitary b\<close>
  shows "sandwich (a \<otimes>\<^sub>o b) = sandwich a \<otimes>\<^sub>r sandwich b"
  apply (rule tensor_extensionality)
  by (auto simp: unitary_sandwich_register assms sandwich_def register_tensor_is_register comp_tensor_op tensor_op_adjoint)

lemma sandwich_grow_left: 
  fixes a :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
  assumes "unitary a"
  shows "sandwich a \<otimes>\<^sub>r id = sandwich (a \<otimes>\<^sub>o id_cblinfun)"
  by (simp add: unitary_sandwich_register assms sandwich_tensor sandwich_id)

lemma register_sandwich: \<open>register F \<Longrightarrow> F (sandwich a b) = sandwich (F a) (F b)\<close>
  by (smt (verit, del_insts) register_def sandwich_def)

lemma assoc_ell2_sandwich: \<open>assoc = sandwich assoc_ell2\<close>
  apply (rule tensor_extensionality3')
    apply (simp_all add: unitary_sandwich_register)[2]
  apply (rule equal_ket)
  apply (case_tac x)
  by (simp add: sandwich_def assoc_apply cblinfun_apply_cblinfun_compose tensor_op_ell2 assoc_ell2_tensor assoc_ell2'_tensor
           flip: tensor_ell2_ket)

lemma assoc_ell2'_sandwich: \<open>assoc' = sandwich assoc_ell2'\<close>
  apply (rule tensor_extensionality3)
    apply (simp_all add: unitary_sandwich_register)[2]
  apply (rule equal_ket)
  apply (case_tac x)
  by (simp add: sandwich_def assoc'_apply cblinfun_apply_cblinfun_compose tensor_op_ell2 assoc_ell2_tensor assoc_ell2'_tensor 
           flip: tensor_ell2_ket)

lemma swap_sandwich: "swap = sandwich Uswap"
  apply (rule tensor_extensionality)
    apply (auto simp: sandwich_def)[2]
  apply (rule tensor_ell2_extensionality)
  by (simp add: sandwich_def cblinfun_apply_cblinfun_compose tensor_op_ell2)

lemma id_tensor_sandwich: 
  fixes a :: "'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::finite ell2"
  assumes "unitary a"
  shows "id \<otimes>\<^sub>r sandwich a = sandwich (id_cblinfun \<otimes>\<^sub>o a)"
  apply (rule tensor_extensionality) 
  using assms by (auto simp: register_tensor_is_register comp_tensor_op sandwich_def tensor_op_adjoint unitary_sandwich_register)

lemma compatible_selfbutter_join:
  assumes [register]: "compatible R S"
  shows "R (selfbutter \<psi>) o\<^sub>C\<^sub>L S (selfbutter \<phi>) = (R; S) (selfbutter (\<psi> \<otimes>\<^sub>s \<phi>))"
  apply (subst register_pair_apply[symmetric, where F=R and G=S])
  using assms by auto

lemma register_mult':
  assumes \<open>register F\<close>
  shows \<open>F a *\<^sub>V F b *\<^sub>V c = F (a o\<^sub>C\<^sub>L b) *\<^sub>V c\<close>
  by (simp add: assms lift_cblinfun_comp(4) register_mult)

lemma register_scaleC:
  assumes \<open>register F\<close> shows \<open>F (c *\<^sub>C a) = c *\<^sub>C F a\<close>
  by (simp add: assms complex_vector.linear_scale)

lemma register_bounded_clinear: \<open>register F \<Longrightarrow> bounded_clinear F\<close>
  using bounded_clinear_finite_dim register_def by blast

lemma register_adjoint: "F (a*) = (F a)*" if \<open>register F\<close>
  using register_def that by blast

end

