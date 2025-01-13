section \<open>Quantum instantiation of registers\<close>

(* AXIOM INSTANTIATION (use instantiate_laws.py to generate Laws_Quantum.thy)

    # Type classes
    domain \<rightarrow> type
    domain_with_simple_complement \<rightarrow> finite

    # Types
    some_domain \<rightarrow> unit

    # Constants
    comp_update \<rightarrow> cblinfun_compose
    id_update \<rightarrow> id_cblinfun
    tensor_update \<rightarrow> tensor_op
    cdc \<rightarrow> register_decomposition_basis

    # Lemmas
    id_update_left \<rightarrow> cblinfun_compose_id_left
    id_update_right \<rightarrow> cblinfun_compose_id_right
    comp_update_assoc \<rightarrow> cblinfun_compose_assoc
    tensor_update_mult \<rightarrow> comp_tensor_op

    # Chapter name
    Generic laws about registers \<rightarrow> Generic laws about registers, instantiated quantumly
    Generic laws about complements \<rightarrow> Generic laws about complements, instantiated quantumly
*)

theory Axioms_Quantum
  imports Jordan_Normal_Form.Matrix_Impl "HOL-Library.Rewrite"
          Complex_Bounded_Operators.Complex_L2
          Hilbert_Space_Tensor_Product.Hilbert_Space_Tensor_Product
          Hilbert_Space_Tensor_Product.Weak_Star_Topology
          Hilbert_Space_Tensor_Product.Partial_Trace
          Hilbert_Space_Tensor_Product.Von_Neumann_Algebras
          With_Type.With_Type
          Misc
begin


unbundle cblinfun_syntax
unbundle no m_inv_syntax


type_synonym 'a update = \<open>('a ell2, 'a ell2) cblinfun\<close>

definition preregister :: \<open>('a update \<Rightarrow> 'b update) \<Rightarrow> bool\<close> where
  \<open>preregister F \<longleftrightarrow> bounded_clinear F \<and> continuous_map weak_star_topology weak_star_topology F\<close>

lemma preregister_mult_right: \<open>preregister (\<lambda>a. a o\<^sub>C\<^sub>L z)\<close>
  by (auto simp add: bounded_cbilinear.bounded_clinear_left bounded_cbilinear_cblinfun_compose
      preregister_def continuous_map_right_comp_weak_star)

lemma preregister_mult_left: \<open>preregister (\<lambda>a. z o\<^sub>C\<^sub>L a)\<close>
  by (auto simp add: bounded_cbilinear.bounded_clinear_right bounded_cbilinear_cblinfun_compose
      preregister_def continuous_map_left_comp_weak_star)

lemma comp_preregister: "preregister F \<Longrightarrow> preregister G \<Longrightarrow> preregister (G \<circ> F)"
  by (auto simp add: preregister_def continuous_map_compose comp_bounded_clinear)

lemma id_preregister: \<open>preregister id\<close>
  unfolding preregister_def by auto

lemma tensor_extensionality:
  \<open>preregister F \<Longrightarrow> preregister G \<Longrightarrow> (\<And>a b. F (tensor_op a b) = G (tensor_op a b)) \<Longrightarrow> F = G\<close>
  apply (rule weak_star_clinear_eq_butterfly_ketI)
  by (auto intro!: bounded_clinear.clinear simp: preregister_def simp flip: tensor_ell2_ket tensor_butterfly)

definition register :: \<open>('a update \<Rightarrow> 'b update) \<Rightarrow> bool\<close> where
  "register F \<longleftrightarrow> 
     bounded_clinear F
   \<and> continuous_map weak_star_topology weak_star_topology F
   \<and> F id_cblinfun = id_cblinfun 
   \<and> (\<forall>a b. F(a o\<^sub>C\<^sub>L b) = F a o\<^sub>C\<^sub>L F b)
   \<and> (\<forall>a. F (a*) = (F a)*)"

lemma register_of_id: \<open>register F \<Longrightarrow> F id_cblinfun = id_cblinfun\<close>
  by (simp add: register_def)

lemma register_id: \<open>register id\<close>
  by (simp add: register_def complex_vector.module_hom_id)

lemma register_preregister: "register F \<Longrightarrow> preregister F"
  unfolding register_def preregister_def by auto

lemma register_comp: "register F \<Longrightarrow> register G \<Longrightarrow> register (G \<circ> F)"
  using bounded_clinear_compose continuous_map_compose
  apply (simp add: o_def register_def)
  by blast

lemma register_mult: "register F \<Longrightarrow> cblinfun_compose (F a) (F b) = F (cblinfun_compose a b)"
  unfolding register_def
  by auto

lemma register_tensor_left: \<open>register (\<lambda>a. tensor_op a id_cblinfun)\<close>
  by (auto simp add: comp_tensor_op register_def tensor_op_cbilinear tensor_op_adjoint
      intro!: tensor_op_cbilinear.bounded_clinear_left)

lemma register_tensor_right: \<open>register (\<lambda>a. tensor_op id_cblinfun a)\<close>
  by (auto simp add: comp_tensor_op register_def tensor_op_cbilinear tensor_op_adjoint
      bounded_cbilinear_apply_bounded_clinear tensor_op_bounded_cbilinear)

definition register_pair ::
  \<open>('a update \<Rightarrow> 'c update) \<Rightarrow> ('b update \<Rightarrow> 'c update)
         \<Rightarrow> (('a\<times>'b) update \<Rightarrow> 'c update)\<close> where
  \<open>register_pair F G = (if register F \<and> register G \<and> (\<forall>a b. F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a) then 
                        SOME R. (\<forall>a b. register R \<and> R (a \<otimes>\<^sub>o b) = F a o\<^sub>C\<^sub>L G b) else (\<lambda>_. 0))\<close>

lemma cbilinear_F_comp_G[simp]: \<open>clinear F \<Longrightarrow> clinear G \<Longrightarrow> cbilinear (\<lambda>a b. F a o\<^sub>C\<^sub>L G b)\<close>
  unfolding cbilinear_def
  by (auto simp add: clinear_iff bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose bounded_cbilinear.add_right)

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

definition \<open>register_decomposition_basis \<Phi> = (SOME B. is_ortho_set B \<and> (\<forall>b\<in>B. norm b = 1) \<and> ccspan B = \<Phi> (butterfly (ket undefined) (ket undefined)) *\<^sub>S \<top>)\<close> 
  for \<Phi> :: \<open>'a update \<Rightarrow> 'b update\<close>

lemma register_decomposition:
  fixes \<Phi> :: \<open>'a update \<Rightarrow> 'b update\<close>
  assumes [simp]: \<open>register \<Phi>\<close>
  shows \<open>let 'c::type = register_decomposition_basis \<Phi> in
         (\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> 
              (\<forall>\<theta>. \<Phi> \<theta> = sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun)))\<close>
  \<comment> \<open>Proof based on @{cite daws21unitalanswer}\<close>
proof with_type_intro
  (* note [[simproc del: compatibility_warn]] *)
  define \<xi>0 :: 'a where \<open>\<xi>0 = undefined\<close>

  have \<open>bounded_clinear \<Phi>\<close>
    using assms register_def by blast
  then have [simp]: \<open>clinear \<Phi>\<close>
    by (simp add: bounded_clinear.clinear)

  define P where \<open>P i = butterfly (ket i) (ket i)\<close> for i :: 'a

  note blinfun_cblinfun_eq_bi_unique[transfer_rule del]
  note cblinfun.bi_unique[transfer_rule del]
  note cblinfun.left_unique[transfer_rule del]
  note cblinfun.right_unique[transfer_rule del]
  note cblinfun.right_total[transfer_rule del]
  note id_cblinfun.transfer[transfer_rule del]

  define P' where \<open>P' i = \<Phi> (P i)\<close> for i :: 'a
  have proj_P': \<open>is_Proj (P' i)\<close> for i
    by (simp add: P_def P'_def butterfly_is_Proj register_projector)
  have sumP'id2: \<open>has_sum_in weak_star_topology (\<lambda>i. P' i) UNIV id_cblinfun\<close>
  proof -
    from has_sum_butterfly_ket
    have \<open>has_sum_in weak_star_topology (\<Phi> o (\<lambda>x. butterfly (ket x) (ket x))) UNIV (\<Phi> id_cblinfun)\<close>
      apply (rule has_sum_in_comm_additive[rotated -1])
      using assms 
      by (auto simp: complex_vector.linear_add register_def Modules.additive_def 
          intro!: continuous_map_is_continuous_at_point complex_vector.linear_0 \<open>clinear \<Phi>\<close>)
    then show ?thesis
      by (simp add: P'_def P_def o_def register_of_id)
  qed
  define S where \<open>S i = P' i *\<^sub>S \<top>\<close> for i :: 'a
  have P'id: \<open>P' i *\<^sub>V \<psi> = \<psi>\<close> if \<open>\<psi> \<in> space_as_set (S i)\<close> for i \<psi>
    using S_def that proj_P'
    by (metis cblinfun_fixes_range is_Proj_algebraic)

  define S_iso' :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a update\<close> where \<open>S_iso' i j = classical_operator (Some o Transposition.transpose i j)\<close> for i j :: 'a
  have S_iso'_apply: \<open>S_iso' i j *\<^sub>V ket i = ket j\<close> for i j
    by (simp add: S_iso'_def classical_operator_ket classical_operator_exists_inj)
  have S_iso'_unitary: \<open>unitary (S_iso' i j)\<close> for i j
    by (simp add: S_iso'_def unitary_classical_operator)
  have S_iso'_id: \<open>S_iso' i i = id_cblinfun\<close> for i
    by (auto intro!: equal_ket simp: S_iso'_def classical_operator_ket classical_operator_exists_inj)
  have S_iso'_adj_apply: \<open>(S_iso' i j)* *\<^sub>V ket j = ket i\<close> for i j
    by (metis S_iso'_apply S_iso'_unitary cblinfun_apply_cblinfun_compose id_cblinfun_apply unitaryD1)
  define S_iso where \<open>S_iso i j = \<Phi> (S_iso' i j)\<close> for i j
  have uni_S_iso: \<open>unitary (S_iso i j)\<close> for i j
    by (simp add: S_iso_def S_iso'_unitary register_unitary)
  have S_iso_S: \<open>S_iso i j *\<^sub>S S i = S j\<close> for i j
  proof -
    have \<open>S_iso i j *\<^sub>S S i = S_iso i j *\<^sub>S P' i *\<^sub>S S_iso j i *\<^sub>S \<top>\<close>
      by (simp add: S_def uni_S_iso)
    also have \<open>\<dots> = S j\<close>
      by (simp add: S_def P'_def S_iso_def P_def register_mult butterfly_comp_cblinfun cblinfun_comp_butterfly S_iso'_apply S_iso'_adj_apply
        flip: cblinfun_compose_image)
    finally show ?thesis
      by -
  qed
  have S_iso_id[simp]: \<open>S_iso i i = id_cblinfun\<close> for i
    by (simp add: S_iso'_id S_iso_def register_of_id)

  obtain B\<^sub>0 where B\<^sub>0: \<open>is_ortho_set B\<^sub>0\<close> \<open>\<And>b. b \<in> B\<^sub>0 \<Longrightarrow> norm b = 1\<close> \<open>ccspan B\<^sub>0 = S \<xi>0\<close>
    using orthonormal_subspace_basis_exists[where S="{}" and V=\<open>S \<xi>0\<close>]
    apply atomize_elim by auto

  have register_decomposition_basis_\<Phi>: \<open>is_ortho_set (register_decomposition_basis \<Phi>) \<and>
       (\<forall>b\<in>register_decomposition_basis \<Phi>. norm b = 1) \<and>
       ccspan (register_decomposition_basis \<Phi>) = S \<xi>0\<close>
    unfolding register_decomposition_basis_def
    apply (rule someI2[where a=B\<^sub>0])
    using B\<^sub>0 by (auto simp: S_def P'_def P_def \<xi>0_def)

  define B where \<open>B i = S_iso \<xi>0 i ` register_decomposition_basis \<Phi>\<close> for i
  have B\<xi>0: \<open>B \<xi>0 = register_decomposition_basis \<Phi>\<close>
    using B_def by force
  have orthoB: \<open>is_ortho_set (B i)\<close> for i
  proof -
    have 1: \<open>x \<in> register_decomposition_basis \<Phi> \<Longrightarrow>
           y \<in> register_decomposition_basis \<Phi> \<Longrightarrow>
           S_iso \<xi>0 i *\<^sub>V x \<noteq> S_iso \<xi>0 i *\<^sub>V y \<Longrightarrow> is_orthogonal (S_iso \<xi>0 i *\<^sub>V x) (S_iso \<xi>0 i *\<^sub>V y)\<close> for x y
      by (metis (no_types, lifting) register_decomposition_basis_\<Phi> UNIV_I cblinfun_apply_cblinfun_compose cblinfun_fixes_range cinner_adj_left id_cblinfun_adjoint is_ortho_set_def top_ccsubspace.rep_eq uni_S_iso unitaryD1 unitary_id unitary_range)
    have 2: \<open>x \<in> register_decomposition_basis \<Phi> \<Longrightarrow> S_iso \<xi>0 i *\<^sub>V x \<noteq> 0\<close> for x
      by (metis register_decomposition_basis_\<Phi> cinner_ket_same cinner_zero_left cnorm_eq_1 isometry_preserves_norm orthogonal_ket uni_S_iso unitary_isometry)
    from 1 2 show ?thesis
      by (auto simp add: B_def is_ortho_set_def)
  qed
  have normalB: \<open>\<And>b. b \<in> B i \<Longrightarrow> norm b = 1\<close> for i
    by (metis (no_types, lifting) register_decomposition_basis_\<Phi> B_def imageE isometry_preserves_norm uni_S_iso unitary_twosided_isometry)
  have cspanB: \<open>ccspan (B i) = S i\<close> for i
    by (simp add: B_def register_decomposition_basis_\<Phi> B\<xi>0 S_iso_S flip: cblinfun_image_ccspan)

  from orthoB have indepB: \<open>cindependent (B i)\<close> for i
    by (simp add: Complex_Inner_Product.is_ortho_set_cindependent)

  have orthoBiBj: \<open>is_orthogonal x y\<close> if \<open>x \<in> B i\<close> and \<open>y \<in> B j\<close> and \<open>i \<noteq> j\<close> for x y i j
  proof -
    have \<open>P' i o\<^sub>C\<^sub>L P' j = 0\<close>
      using \<open>i \<noteq> j\<close>
      by (simp add: P'_def P_def register_mult butterfly_comp_butterfly cinner_ket
          \<open>clinear \<Phi>\<close> complex_vector.linear_0)
    then have *: \<open>Proj (ccspan (B i)) o\<^sub>C\<^sub>L Proj (ccspan (B j)) = 0\<close>
      by (simp add: Proj_on_own_range S_def cspanB proj_P')
    then show \<open>is_orthogonal x y\<close>
      by (meson orthogonal_projectors_orthogonal_spaces orthogonal_spaces_ccspan that(1) that(2))
  qed

  define B' where \<open>B' = (\<Union>i\<in>UNIV. B i)\<close>

  have P'B: \<open>P' i = Proj (ccspan (B i))\<close> for i
    unfolding cspanB S_def
    using proj_P' Proj_on_own_range'[symmetric] is_Proj_algebraic by blast

  show \<open>register_decomposition_basis \<Phi> \<noteq> {}\<close>
  proof (rule ccontr)
    assume \<open>\<not> register_decomposition_basis \<Phi> \<noteq> {}\<close>
    then have \<open>B i = {}\<close> for i
      by (simp add: B_def)
    then have \<open>S i = 0\<close> for i
      using cspanB by force
    then have \<open>P' i = 0\<close> for i
      by (simp add: P'B cspanB)
    with sumP'id2
    have \<open>has_sum_in weak_star_topology (\<lambda>i. 0) UNIV id_cblinfun\<close>
      by (metis (no_types, lifting) UNIV_I has_sum_in_0 has_sum_in_cong has_sum_in_unique hausdorff_weak_star id_cblinfun_not_0 weak_star_topology_topspace)
    then have \<open>id_cblinfun = 0\<close>
      using has_sum_in_0 has_sum_in_unique hausdorff_weak_star id_cblinfun_not_0 weak_star_topology_topspace by fast
    then show False
      using id_cblinfun_not_0 by blast
  qed

  from orthoBiBj orthoB have orthoB': \<open>is_ortho_set B'\<close>
    unfolding B'_def is_ortho_set_def by blast
  then have indepB': \<open>cindependent B'\<close>
    using is_ortho_set_cindependent by blast

  from orthoBiBj orthoB
  have Bdisj: \<open>B i \<inter> B j = {}\<close> if \<open>i \<noteq> j\<close> for i j
    unfolding is_ortho_set_def
    using cinner_eq_zero_iff that
    by fastforce

  fix rep_c :: \<open>'c \<Rightarrow> 'b ell2\<close>
  assume bij_rep_c: \<open>bij_betw rep_c UNIV (register_decomposition_basis \<Phi>)\<close>
  then interpret type_definition rep_c \<open>inv rep_c\<close> \<open>register_decomposition_basis \<Phi>\<close>
    by (simp add: type_definition_bij_betw_iff)

  from bij_rep_c have bij_rep_c: \<open>bij_betw rep_c (UNIV :: 'c set) (B \<xi>0)\<close>
    unfolding B\<xi>0 by simp

  define u where \<open>u = (\<lambda>(\<xi>,\<alpha>). \<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>V rep_c \<alpha>)\<close> for \<xi> :: 'a and \<alpha> :: \<open>'c\<close>

  have cinner_u: \<open>cinner (u \<xi>\<alpha>) (u \<xi>'\<alpha>') = of_bool (\<xi>\<alpha> = \<xi>'\<alpha>')\<close> for \<xi>\<alpha> \<xi>'\<alpha>'
  proof -
    obtain \<xi> \<alpha> \<xi>' \<alpha>' where \<xi>\<alpha>: \<open>\<xi>\<alpha> = (\<xi>,\<alpha>)\<close> and \<xi>'\<alpha>': \<open>\<xi>'\<alpha>' = (\<xi>',\<alpha>')\<close>
      apply atomize_elim by auto
    have \<open>cinner (u (\<xi>,\<alpha>)) (u (\<xi>', \<alpha>')) = cinner (\<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>V rep_c \<alpha>) (\<Phi> (butterfly (ket \<xi>') (ket \<xi>0)) *\<^sub>V rep_c \<alpha>')\<close>
      unfolding u_def by simp
    also have \<open>\<dots> = cinner ((\<Phi> (butterfly (ket \<xi>') (ket \<xi>0)))* *\<^sub>V \<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>V rep_c \<alpha>) (rep_c \<alpha>')\<close>
      by (simp add: cinner_adj_left)
    also have \<open>\<dots> = cinner (\<Phi> (butterfly (ket \<xi>') (ket \<xi>0) *) *\<^sub>V \<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>V rep_c \<alpha>) (rep_c \<alpha>')\<close>
      by (metis (no_types, lifting) assms register_def)
    also have \<open>\<dots> = cinner (\<Phi> (butterfly (ket \<xi>0) (ket \<xi>') o\<^sub>C\<^sub>L butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>V rep_c \<alpha>) (rep_c \<alpha>')\<close>
      by (simp add: register_mult cblinfun_apply_cblinfun_compose[symmetric])
    also have \<open>\<dots> = cinner (\<Phi> (of_bool (\<xi>'=\<xi>) *\<^sub>C butterfly (ket \<xi>0) (ket \<xi>0)) *\<^sub>V rep_c \<alpha>) (rep_c \<alpha>')\<close>
      by (simp add: cinner_ket_left ket.rep_eq)
    also have \<open>\<dots> = of_bool (\<xi>'=\<xi>) * cinner (\<Phi> (butterfly (ket \<xi>0) (ket \<xi>0)) *\<^sub>V rep_c \<alpha>) (rep_c \<alpha>')\<close>
      by (simp add: complex_vector.linear_0)
    also have \<open>\<dots> = of_bool (\<xi>'=\<xi>) * cinner (P' \<xi>0 *\<^sub>V rep_c \<alpha>) (rep_c \<alpha>')\<close>
      using P_def P'_def by simp
    also have \<open>\<dots> = of_bool (\<xi>'=\<xi>) * cinner (rep_c \<alpha>) (rep_c \<alpha>')\<close>
      apply (subst P'id)
      apply (metis B\<xi>0 Rep ccspan_superset cspanB in_mono)
      by simp
    also have \<open>\<dots> = of_bool (\<xi>'=\<xi>) * of_bool (\<alpha>=\<alpha>')\<close>
      using bij_rep_c orthoB normalB unfolding is_ortho_set_def
      by (smt (verit, best) B\<xi>0 Rep Rep_inject cnorm_eq_1 of_bool_eq(1) of_bool_eq(2))
    finally show ?thesis
      by (simp add: \<xi>'\<alpha>' \<xi>\<alpha>)
  qed
  define U where \<open>U = cblinfun_extension (range ket) (u o inv ket)\<close>
  have Uapply: \<open>U *\<^sub>V ket \<xi>\<alpha> = u \<xi>\<alpha>\<close> for \<xi>\<alpha>
  proof -
    have aux: \<open>(\<And>a b aa ba. u (a, b) \<bullet>\<^sub>C u (aa, ba) = of_bool (a = aa \<and> b = ba)) \<Longrightarrow> norm (u (a, b)) \<le> 1\<close> for a b
      by (metis (full_types) cinner_u cnorm_eq_1 of_bool_eq_1_iff order_refl)
    then show ?thesis
      unfolding U_def
      apply (subst cblinfun_extension_apply)
      using cinner_u by (auto intro!: cblinfun_extension_exists_ortho[where B=1])
  qed
  have \<open>isometry U\<close>
    apply (rule_tac orthogonal_on_basis_is_isometry[where B=\<open>range ket\<close>])
    by (auto simp: Uapply cinner_u)
  
  have 1: \<open>U* o\<^sub>C\<^sub>L \<Phi> \<theta> o\<^sub>C\<^sub>L U = \<theta> \<otimes>\<^sub>o id_cblinfun\<close> for \<theta>
  proof -
    have *: \<open>U* o\<^sub>C\<^sub>L \<Phi> (butterfly (ket \<xi>) (ket \<eta>)) o\<^sub>C\<^sub>L U = butterfly (ket \<xi>) (ket \<eta>) \<otimes>\<^sub>o id_cblinfun\<close> for \<xi> \<eta>
    proof (rule equal_ket, rename_tac \<xi>1\<alpha>)
      fix \<xi>1\<alpha> obtain \<xi>1 :: 'a and \<alpha> :: \<open>'c\<close> where \<xi>1\<alpha>: \<open>\<xi>1\<alpha> = (\<xi>1,\<alpha>)\<close> 
        apply atomize_elim by auto
      have \<open>(U* o\<^sub>C\<^sub>L \<Phi> (butterfly (ket \<xi>) (ket \<eta>)) o\<^sub>C\<^sub>L U) *\<^sub>V ket \<xi>1\<alpha> = U* *\<^sub>V \<Phi> (butterfly (ket \<xi>) (ket \<eta>)) *\<^sub>V \<Phi> (butterfly (ket \<xi>1) (ket \<xi>0)) *\<^sub>V rep_c \<alpha>\<close>
        unfolding cblinfun_apply_cblinfun_compose \<xi>1\<alpha> Uapply u_def by simp
      also have \<open>\<dots> = U* *\<^sub>V \<Phi> (butterfly (ket \<xi>) (ket \<eta>) o\<^sub>C\<^sub>L butterfly (ket \<xi>1) (ket \<xi>0)) *\<^sub>V rep_c \<alpha>\<close>
         by (metis assms register_mult simp_a_oCL_b')
      also have \<open>\<dots> = U* *\<^sub>V \<Phi> (of_bool (\<eta>=\<xi>1) *\<^sub>C butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>V rep_c \<alpha>\<close>
        by (simp add: cinner_ket)
      also have \<open>\<dots> = of_bool (\<eta>=\<xi>1) *\<^sub>C U* *\<^sub>V \<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>V rep_c \<alpha>\<close>
        by (simp add: complex_vector.linear_scale)
      also have \<open>\<dots> = of_bool (\<eta>=\<xi>1) *\<^sub>C U* *\<^sub>V U *\<^sub>V ket (\<xi>, \<alpha>)\<close>
        unfolding Uapply u_def by simp
      also from \<open>isometry U\<close> have \<open>\<dots> = of_bool (\<eta>=\<xi>1) *\<^sub>C ket (\<xi>, \<alpha>)\<close>
        unfolding cblinfun_apply_cblinfun_compose[symmetric] by simp
      also have \<open>\<dots> = (butterfly (ket \<xi>) (ket \<eta>) *\<^sub>V ket \<xi>1) \<otimes>\<^sub>s ket \<alpha>\<close>
        by (simp add: tensor_ell2_scaleC1 tensor_ell2_ket)
      also have \<open>\<dots> = (butterfly (ket \<xi>) (ket \<eta>) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket \<xi>1\<alpha>\<close>
        by (simp add: \<xi>1\<alpha> tensor_op_ket)
      finally show \<open>(U* o\<^sub>C\<^sub>L \<Phi> (butterfly (ket \<xi>) (ket \<eta>)) o\<^sub>C\<^sub>L U) *\<^sub>V ket \<xi>1\<alpha> = (butterfly (ket \<xi>) (ket \<eta>) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket \<xi>1\<alpha>\<close>
        by -
    qed

    have cont1: \<open>continuous_map weak_star_topology weak_star_topology (\<lambda>a. U* o\<^sub>C\<^sub>L \<Phi> a o\<^sub>C\<^sub>L U)\<close>
      apply (subst asm_rl[of \<open>(\<lambda>a. U* o\<^sub>C\<^sub>L \<Phi> a o\<^sub>C\<^sub>L U) = (\<lambda>x. x o\<^sub>C\<^sub>L U) o (\<lambda>x. U* o\<^sub>C\<^sub>L x) o \<Phi>\<close>])
       apply force
      apply (intro continuous_map_compose[where X'=weak_star_topology])
      using assms register_def continuous_map_left_comp_weak_star continuous_map_right_comp_weak_star by blast+

    have *: \<open>U* o\<^sub>C\<^sub>L \<Phi> \<theta> o\<^sub>C\<^sub>L U = \<theta> \<otimes>\<^sub>o id_cblinfun\<close> if \<open>\<theta> \<in> cspan (range (\<lambda>(\<xi>, \<eta>). butterfly (ket \<xi>) (ket \<eta>)))\<close> for \<theta>
      apply (rule complex_vector.linear_eq_on[where x=\<theta>, OF _ _ that])
        apply (intro \<open>clinear \<Phi>\<close>
          clinear_compose[OF _ clinear_cblinfun_compose_left, unfolded o_def]
          clinear_compose[OF _ clinear_cblinfun_compose_right, unfolded o_def])
       apply simp
      using * by fast
    have \<open>U* o\<^sub>C\<^sub>L \<Phi> \<theta> o\<^sub>C\<^sub>L U = \<theta> \<otimes>\<^sub>o id_cblinfun\<close> 
      if \<open>\<theta> \<in> (weak_star_topology closure_of (cspan (range (\<lambda>(\<xi>, \<eta>). butterfly (ket \<xi>) (ket \<eta>)))))\<close> for \<theta>
      apply (rule closure_of_eqI[OF _ _ that])
      using * cont1 left_amplification_weak_star_cont by auto
    with butterkets_weak_star_dense show ?thesis
      by auto
  qed
  have \<open>unitary U\<close>
  proof -
    have \<open>\<Phi> (butterfly (ket \<xi>) (ket \<xi>1)) *\<^sub>S \<top> \<le> U *\<^sub>S \<top>\<close> for \<xi> \<xi>1
    proof -
      have *: \<open>\<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>V b \<in> space_as_set (U *\<^sub>S \<top>)\<close> if \<open>b \<in> B \<xi>0\<close> for b
        apply (subst asm_rl[of \<open>\<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>V b = u (\<xi>, inv rep_c b)\<close>])
         apply (simp add: u_def, metis bij_betw_inv_into_right bij_rep_c that)
        by (metis Uapply cblinfun_apply_in_image)

      have \<open>\<Phi> (butterfly (ket \<xi>) (ket \<xi>1)) *\<^sub>S \<top> = \<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>S \<Phi> (butterfly (ket \<xi>0) (ket \<xi>0)) *\<^sub>S \<Phi> (butterfly (ket \<xi>0) (ket \<xi>1)) *\<^sub>S \<top>\<close>
        unfolding cblinfun_compose_image[symmetric] register_mult[OF assms]
        by simp
      also have \<open>\<dots> \<le> \<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>S \<Phi> (butterfly (ket \<xi>0) (ket \<xi>0)) *\<^sub>S \<top>\<close>
        by (meson cblinfun_image_mono top_greatest)
      also have \<open>\<dots> = \<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>S S \<xi>0\<close>
        by (simp add: S_def P'_def P_def)
      also have \<open>\<dots> = \<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>S ccspan (B \<xi>0)\<close>
        by (simp add: cspanB)
      also have \<open>\<dots> = ccspan (\<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) ` B \<xi>0)\<close>
        by (meson cblinfun_image_ccspan)
      also have \<open>\<dots> \<le> U *\<^sub>S \<top>\<close>
        by (rule ccspan_leqI, use * in auto)
      finally show ?thesis by -
    qed
    then have \<open>ccspan {\<Phi> (butterfly (ket \<xi>) (ket \<xi>)) *\<^sub>V \<alpha> |\<xi> \<alpha>. True} \<le> U *\<^sub>S \<top>\<close>
      apply (rule_tac ccspan_leqI)
      using cblinfun_apply_in_image less_eq_ccsubspace.rep_eq by blast
    moreover have \<open>ccspan {\<Phi> (butterfly (ket \<xi>) (ket \<xi>)) *\<^sub>V \<alpha> |\<xi> \<alpha>. True} = \<top>\<close>
    proof -
      define Q where \<open>Q = Proj (- ccspan {\<Phi> (butterfly (ket \<xi>) (ket \<xi>)) *\<^sub>V \<alpha> |\<xi> \<alpha>. True})\<close>
      have \<open>has_sum_in weak_star_topology (\<lambda>\<xi>. Q o\<^sub>C\<^sub>L \<Phi> (butterfly (ket \<xi>) (ket \<xi>))) UNIV (Q o\<^sub>C\<^sub>L id_cblinfun)\<close>
        apply (rule has_sum_in_comm_additive[where g=\<open>cblinfun_compose Q\<close> and T=weak_star_topology, unfolded o_def])
        using sumP'id2
        by (auto simp add: continuous_map_left_comp_weak_star P'_def P_def cblinfun_compose_add_right Modules.additive_def)
      moreover have \<open>Q o\<^sub>C\<^sub>L \<Phi> (butterfly (ket \<xi>) (ket \<xi>)) = 0\<close> for \<xi>
        apply (rule equal_ket)
        apply (simp add: Q_def Proj_ortho_compl cblinfun.diff_left)
        apply (subst Proj_fixes_image)
        by (auto intro!: ccspan_superset[THEN set_mp])
      ultimately have \<open>Q = 0\<close>
        apply (rule_tac has_sum_in_unique)
        by auto
      then show ?thesis
        by (smt (verit, del_insts) Q_def Proj_ortho_compl Proj_range cblinfun_image_id right_minus_eq)
    qed
    ultimately have \<open>U *\<^sub>S \<top> = \<top>\<close>
      by (simp add: top.extremum_unique)
    with \<open>isometry U\<close> show \<open>unitary U\<close>
      by (rule surj_isometry_is_unitary)
  qed

  have \<open>\<Phi> \<theta> = U o\<^sub>C\<^sub>L (\<theta> \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L U*\<close> for \<theta>
  proof -
    from \<open>unitary U\<close>
    have \<open>\<Phi> \<theta> = (U o\<^sub>C\<^sub>L U*) o\<^sub>C\<^sub>L \<Phi> \<theta> o\<^sub>C\<^sub>L (U o\<^sub>C\<^sub>L U*)\<close>
      by simp
    also have \<open>\<dots> = U o\<^sub>C\<^sub>L (U*  o\<^sub>C\<^sub>L \<Phi> \<theta> o\<^sub>C\<^sub>L U) o\<^sub>C\<^sub>L U*\<close>
      by (simp add: cblinfun_assoc_left)
    also have \<open>\<dots> = U o\<^sub>C\<^sub>L (\<theta> \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L U*\<close>
      using 1 by simp
    finally show ?thesis
      by -
  qed

  with \<open>unitary U\<close> show \<open>\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> (\<forall>\<theta>. \<Phi> \<theta> = sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun))\<close>
    by (auto simp: sandwich_apply)
qed

lemma register_bounded_clinear: \<open>register F \<Longrightarrow> bounded_clinear F\<close>
  using preregister_def register_preregister by blast

lemma clinear_register: \<open>register F \<Longrightarrow> clinear F\<close>
  using bounded_clinear.clinear register_bounded_clinear by blast

lemma weak_star_cont_register: \<open>register F \<Longrightarrow> continuous_map weak_star_topology weak_star_topology F\<close>
  using register_def by blast

lemma register_inv_weak_star_continuous:
  assumes \<open>register F\<close>
  shows \<open>continuous_map (subtopology weak_star_topology (range F)) weak_star_topology (inv F)\<close>
proof (rule continuous_map_iff_preserves_convergence, rename_tac K a)
  fix K a
  assume limit_id: \<open>limitin (subtopology weak_star_topology (range F)) id a K\<close>
  from register_decomposition
  have \<open>let 'c::type = register_decomposition_basis F in
        limitin weak_star_topology (inv F) (inv F a) K\<close>
  proof with_type_mp
    from assms show \<open>register F\<close> by -
  next
    with_type_case
    then obtain U :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> 
      where \<open>unitary U\<close> and FU: \<open>F \<theta> = sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun)\<close> for \<theta>
      by auto
    define \<delta> :: \<open>'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close> where \<open>\<delta> = selfbutter (ket (undefined))\<close>
    then have [simp]: \<open>trace_class \<delta>\<close>
      by simp
    define u where \<open>u t = U o\<^sub>C\<^sub>L (from_trace_class t \<otimes>\<^sub>o \<delta>) o\<^sub>C\<^sub>L U*\<close> for t
    have [simp]: \<open>trace_class (u t)\<close> for t
      unfolding u_def
      apply (rule trace_class_comp_left)
      apply (rule trace_class_comp_right)
      by (simp add: trace_class_tensor)
    have uF: \<open>trace (from_trace_class t o\<^sub>C\<^sub>L a) = trace (u t o\<^sub>C\<^sub>L F a)\<close> for t a 
    proof -
      have \<open>trace (from_trace_class t o\<^sub>C\<^sub>L a) = trace (from_trace_class t o\<^sub>C\<^sub>L a) * trace (\<delta> o\<^sub>C\<^sub>L id_cblinfun)\<close>
        by (simp add: \<delta>_def trace_butterfly)
      also have \<open>\<dots> = trace ((from_trace_class t o\<^sub>C\<^sub>L a) \<otimes>\<^sub>o (\<delta> o\<^sub>C\<^sub>L id_cblinfun))\<close>
        by (simp add: trace_class_comp_left trace_tensor)
      also have \<open>\<dots> = trace ((from_trace_class t \<otimes>\<^sub>o \<delta>) o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o id_cblinfun))\<close>
        by (simp add: comp_tensor_op)
      also have \<open>\<dots> = trace (U* o\<^sub>C\<^sub>L u t o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o id_cblinfun))\<close>
        using \<open>unitary U\<close>
        by (simp add: u_def lift_cblinfun_comp[OF unitaryD1] cblinfun_compose_assoc)
      also have \<open>\<dots> = trace (u t o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L U*)\<close>
        apply (subst (2) circularity_of_trace)
        by (simp_all add: trace_class_comp_left cblinfun_compose_assoc)
      also have \<open>\<dots> = trace (u t o\<^sub>C\<^sub>L F a)\<close>
        by (simp add: sandwich_apply FU cblinfun_compose_assoc)
      finally show ?thesis
        by -
    qed
    from limit_id
    have \<open>a \<in> range F\<close> and KrangeF: \<open>\<forall>\<^sub>F a in K. a \<in> range F\<close> and limit_id': \<open>limitin weak_star_topology id a K\<close>
      unfolding limitin_subtopology by auto
    from \<open>a \<in> range F\<close> have FiFa: \<open>F (inv F a) = a\<close>
      by (simp add: f_inv_into_f)
    from KrangeF
    have *: \<open>\<forall>\<^sub>F x in K. trace (from_trace_class t o\<^sub>C\<^sub>L F (inv F x)) = trace (from_trace_class t o\<^sub>C\<^sub>L x)\<close> for t
      apply (rule eventually_mono)
      by (simp add: f_inv_into_f)
    from limit_id' have \<open>((\<lambda>a'. trace (from_trace_class t o\<^sub>C\<^sub>L a')) \<longlongrightarrow> trace (from_trace_class t o\<^sub>C\<^sub>L a)) K\<close> for t
      unfolding limitin_weak_star_topology' by simp
    then have *: \<open>((\<lambda>a'. trace (from_trace_class t o\<^sub>C\<^sub>L F (inv F a'))) \<longlongrightarrow> trace (from_trace_class t o\<^sub>C\<^sub>L F (inv F a))) K\<close> for t
      unfolding FiFa using * by (rule tendsto_cong[THEN iffD2, rotated])
    have \<open>((\<lambda>a'. trace (u t o\<^sub>C\<^sub>L F (inv F a'))) \<longlongrightarrow> trace (u t o\<^sub>C\<^sub>L F (inv F a))) K\<close> for t
      using *[of \<open>Abs_trace_class (u t)\<close>]
      by (simp add: Abs_trace_class_inverse)
    then have \<open>((\<lambda>a'. trace (from_trace_class t o\<^sub>C\<^sub>L inv F a')) \<longlongrightarrow> trace (from_trace_class t o\<^sub>C\<^sub>L inv F a)) K\<close> for t
      by (simp add: uF[symmetric])
    then show \<open>limitin weak_star_topology (inv F) (inv F a) K\<close>
      by (simp add: limitin_weak_star_topology')
  qed
  note this[cancel_with_type]
  then show \<open>limitin weak_star_topology (inv F) (inv F a) K\<close>
    by -
qed

lemma register_inj: \<open>inj_on F X\<close> if [simp]: \<open>register F\<close>
proof -
  have \<open>let 'c::type = register_decomposition_basis F in inj F\<close>
    using register_decomposition[OF \<open>register F\<close>] 
  proof with_type_mp
    with_type_case
    then obtain U :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
      where \<open>unitary U\<close> and F: \<open>F a = Complex_Bounded_Linear_Function.sandwich U (a \<otimes>\<^sub>o id_cblinfun)\<close> for a
      apply atomize_elim by auto
    have \<open>inj (Complex_Bounded_Linear_Function.sandwich U)\<close>
      by (smt (verit, best) \<open>unitary U\<close> cblinfun_assoc_left inj_onI sandwich_apply cblinfun_compose_id_right cblinfun_compose_id_left unitary_def)
    moreover have \<open>inj (\<lambda>a::'a ell2 \<Rightarrow>\<^sub>C\<^sub>L _. a \<otimes>\<^sub>o id_cblinfun)\<close>
      by (rule inj_tensor_left, simp)
    ultimately show \<open>inj F\<close>
      unfolding F
      by (smt (z3) inj_def)
  qed
  from this[THEN with_type_prepare_cancel, cancel_type_definition, OF with_type_nonempty, OF this]
  show \<open>inj_on F X\<close>
    by (simp add: inj_on_def)
qed

lemma register_norm: \<open>norm (F a) = norm a\<close> if \<open>register F\<close>
proof -
  from register_decomposition[OF that]
  have \<open>let 'c::type = register_decomposition_basis F in
         norm (F a) = norm a\<close>
  proof with_type_mp
    with_type_case
    then obtain U :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> where \<open>unitary U\<close>
      and FU: \<open>F \<theta> = sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun)\<close> for \<theta>
      by metis
    show \<open>norm (F a) = norm a\<close>
      using \<open>unitary U\<close>
      by (simp add: FU sandwich_apply norm_isometry_compose norm_isometry_compose' norm_isometry tensor_op_norm)
  qed
  note this[cancel_with_type]
  then show ?thesis
    by simp
qed

lemma unitary_sandwich_register: \<open>unitary a \<Longrightarrow> register (sandwich a)\<close>
  by (auto simp: sandwich_apply register_def cblinfun.bounded_clinear_right
      lift_cblinfun_comp[OF unitaryD1] lift_cblinfun_comp[OF unitaryD2]
      cblinfun_assoc_left)

lemma register_adj: \<open>register F \<Longrightarrow> F (a*) = (F a)*\<close>
  using register_def by blast

lemma right_register_tensor_ex: \<open>\<exists>T :: ('a \<times> 'b) update \<Rightarrow> ('a \<times> 'c) update. 
        register T \<and> (\<forall>a b. T (a \<otimes>\<^sub>o b) = a \<otimes>\<^sub>o F b)\<close> if \<open>register F\<close>
proof -
  from register_decomposition[OF \<open>register F\<close>]
  have \<open>let 'g::type = register_decomposition_basis F in
        \<exists>T :: ('a \<times> 'b) update \<Rightarrow> ('a \<times> 'c) update. 
        register T \<and> (\<forall>a b. T (a \<otimes>\<^sub>o b) = a \<otimes>\<^sub>o F b)\<close>
  proof with_type_mp
    with_type_case
    then obtain U :: \<open>('b \<times> 'g) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close> 
      where [simp]: \<open>unitary U\<close> and F: \<open>F \<theta> = sandwich U *\<^sub>V \<theta> \<otimes>\<^sub>o id_cblinfun\<close> for \<theta>
      by auto
    define T :: \<open>('a \<times> 'b) update \<Rightarrow> ('a \<times> 'c) update\<close>
      where \<open>T = sandwich (id_cblinfun \<otimes>\<^sub>o U) o sandwich assoc_ell2 o (\<lambda>ab. ab \<otimes>\<^sub>o id_cblinfun)\<close>
    have \<open>register T\<close>
      by (auto intro!: register_comp register_tensor_left unitary_sandwich_register unitary_tensor_op simp add: T_def)
    moreover have \<open>T (a \<otimes>\<^sub>o b) = a \<otimes>\<^sub>o F b\<close> for a b
      by (simp add: T_def F sandwich_tensor_op)
    ultimately show \<open>\<exists>T :: ('a \<times> 'b) update \<Rightarrow> ('a \<times> 'c) update. register T \<and> (\<forall>a b. T (a \<otimes>\<^sub>o b) = a \<otimes>\<^sub>o F b)\<close>
      by auto
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed




(* Things that are probably missing to do the proof from page 44 in the register-paper:

- Existence of T(a\<otimes>\<^sub>ob) = F(a)\<otimes>\<^sub>oG(b) [proven via completely pos. maps and Takesaki; maybe we can do it easier with the explicit representation of F,G?]
- Inverse of (- \<otimes>\<^sub>o d) is weak*-continuous (shown in Conway-op, Prop 46.6).  [Similar to register_inv_weak_star_continuous?]

*)
lemma 
  fixes F :: \<open>'a update \<Rightarrow> 'c update\<close> and G
  assumes [simp]: \<open>register F\<close> \<open>register G\<close>
  assumes FG_comm: \<open>\<And>a b. F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a\<close>
  shows register_pair_apply: \<open>(register_pair F G) (tensor_op a b) = F a o\<^sub>C\<^sub>L G b\<close>
    and register_pair_is_register: \<open>register (register_pair F G)\<close>
proof -
  have *: \<open>register_pair F G = (SOME R. \<forall>a b. register R \<and> R (a \<otimes>\<^sub>o b) = F a o\<^sub>C\<^sub>L G b)\<close>
    using assms unfolding register_pair_def by simp
  from register_decomposition[OF \<open>register F\<close>] 
  have \<open>let 'd::type = register_decomposition_basis F in
        \<exists>R. \<forall>a b. register R \<and> R (a \<otimes>\<^sub>o b) = F a o\<^sub>C\<^sub>L G b\<close>
  proof with_type_mp
    with_type_case
(*     fix Rep :: \<open>'d \<Rightarrow> 'c ell2\<close> and Abs
    assume \<open>type_definition Rep Abs (register_decomposition_basis F)\<close>
    assume \<open>(\<exists>U :: ('a \<times> 'd) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2. unitary U \<and> 
              (\<forall>\<theta>. F \<theta> = sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun)))\<close> *)
    then obtain U :: \<open>('a \<times> 'd) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close> where [simp]: \<open>unitary U\<close>
      and FU: \<open>F \<theta> = sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun)\<close> for \<theta>
      by metis
    from register_decomposition[OF \<open>register G\<close>]
    have \<open>let 'f::type = register_decomposition_basis G in
          \<exists>R. \<forall>a b. register R \<and> R (a \<otimes>\<^sub>o b) = F a o\<^sub>C\<^sub>L G b\<close>
    proof with_type_mp
      with_type_case
      then obtain V :: \<open>('b \<times> 'f) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close> where [simp]: \<open>unitary V\<close>
        and GU: \<open>G \<theta> = sandwich V (\<theta> \<otimes>\<^sub>o id_cblinfun)\<close> for \<theta>
        by metis
      show \<open>\<exists>FG. \<forall>a b. register FG \<and> FG (a \<otimes>\<^sub>o b) = F a o\<^sub>C\<^sub>L G b\<close>
      proof -
        define G' and \<iota> :: \<open>'d update \<Rightarrow> ('a \<times> 'd) update\<close> and G\<^sub>1 
          where \<open>G' = sandwich (U*) o G\<close> and \<open>\<iota> d = id_cblinfun \<otimes>\<^sub>o d\<close> and \<open>G\<^sub>1 = inv \<iota> o G'\<close> for d
        have [simp]: \<open>register G'\<close>
          by (simp add: G'_def register_comp unitary_sandwich_register)
        then have [simp]: \<open>bounded_clinear G'\<close>
          by (meson register_bounded_clinear)
        then have [simp]: \<open>clinear G'\<close>
          by (simp add: bounded_clinear.axioms(1))

        
        have \<open>range G' = sandwich (U*) ` range G\<close>
          by (simp add: GU G'_def image_image)
        also have \<open>\<dots> \<subseteq> sandwich (U*) ` commutant (range F)\<close>
          by (auto intro!: image_mono simp: commutant_def FG_comm)
        also have \<open>\<dots> = commutant (sandwich (U*) ` range F)\<close>
          by (simp add: sandwich_unitary_commutant)
        also have \<open>\<dots> = commutant (range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun))\<close>
          apply (rule arg_cong[where f=commutant])
          by (simp add: FU image_image flip: sandwich_compose cblinfun_apply_cblinfun_compose)
        also have \<open>\<dots> = range (\<lambda>d. id_cblinfun \<otimes>\<^sub>o d)\<close>
          by (rule commutant_tensor1)
        also have \<open>\<dots> = range \<iota>\<close>
          by (simp add: \<iota>_def[abs_def])
        finally have range_G': \<open>range G' \<subseteq> range \<iota>\<close>
          by -

        have \<open>continuous_map weak_star_topology weak_star_topology G'\<close>
          by (auto intro!: continuous_map_compose[where X'=weak_star_topology] simp: G'_def  weak_star_cont_register)
        then have cont_G': \<open>continuous_map weak_star_topology (subtopology weak_star_topology (range \<iota>)) G'\<close>
          using range_G' by (auto intro!: continuous_map_into_subtopology)

        have [simp]: \<open>register \<iota>\<close>
          by (simp add: \<iota>_def[abs_def] register_tensor_right)
        then have cont_inv\<iota>: \<open>continuous_map (subtopology weak_star_topology (range \<iota>)) weak_star_topology (inv \<iota>)\<close>
          by (rule register_inv_weak_star_continuous)
        have \<iota>_inj: \<open>x = y\<close> if \<open>\<iota> x = \<iota> y\<close> for x y
          by (metis \<open>register \<iota>\<close> invI register_inj that)

        have [simp]: \<open>register G\<^sub>1\<close>
        proof (unfold register_def, intro conjI allI)
          from cont_G' cont_inv\<iota> 
          show cont_G\<^sub>1: \<open>continuous_map weak_star_topology weak_star_topology G\<^sub>1\<close>
            using G\<^sub>1_def continuous_map_compose by blast
          have \<iota>_cancel: \<open>\<iota> (inv \<iota> x) = x\<close> if \<open>x \<in> range G'\<close> for x
            by (meson f_inv_into_f range_G' subsetD that)

          show \<open>bounded_clinear G\<^sub>1\<close>
            using range_G' 
            by (auto intro!: bounded_clinearI[where K=1] \<iota>_inj 
                simp: G\<^sub>1_def complex_vector.linear_add[of \<iota>] bounded_clinear.clinear clinear_register
                \<iota>_cancel range_subsetD complex_vector.linear_scale[of \<iota>] register_norm[of G']
                simp flip: complex_vector.linear_add[of G'] complex_vector.linear_scale[of G']
                register_norm[of \<iota>])
          show \<open>G\<^sub>1 id_cblinfun = id_cblinfun\<close>
            by (auto intro!: \<iota>_inj register_of_id[of G'] simp add: G\<^sub>1_def \<iota>_cancel register_of_id[of \<iota>])
          show adj_G\<^sub>1: \<open>G\<^sub>1 (a*) = (G\<^sub>1 a)*\<close> for a
            using range_G' 
            by (auto intro!: \<iota>_inj 
                simp: G\<^sub>1_def \<iota>_cancel register_adj[of \<iota>]
                simp flip: register_adj[of G'])
          show mult_G\<^sub>1: \<open>G\<^sub>1 (a o\<^sub>C\<^sub>L b) = G\<^sub>1 a o\<^sub>C\<^sub>L G\<^sub>1 b\<close> for a b
            using range_G' 
            by (auto intro!: bounded_clinearI[where K=1] \<iota>_inj 
                simp: G\<^sub>1_def \<iota>_cancel register_mult[of G']
                simp flip: register_mult[of \<iota>])
        qed

        obtain T :: \<open>('a \<times> 'b) update \<Rightarrow> ('a \<times> 'd) update\<close>
          where [simp]: \<open>register T\<close> and T_apply: \<open>T (a \<otimes>\<^sub>o b) = a \<otimes>\<^sub>o G\<^sub>1 b\<close> for a b
          using \<open>register G\<^sub>1\<close> right_register_tensor_ex by blast
      
        define FG where \<open>FG = sandwich U o T\<close>
        then have [simp]: \<open>register FG\<close>
          by (auto intro!: register_comp unitary_sandwich_register simp add: FG_def)

        have \<open>FG (a \<otimes>\<^sub>o b) = F a o\<^sub>C\<^sub>L G b\<close> for a b
        proof -
          have FG_a: \<open>FG (a \<otimes>\<^sub>o id_cblinfun) = F a\<close>
            by (simp add: FG_def T_apply register_of_id FU)
          have \<open>FG (id_cblinfun \<otimes>\<^sub>o b) = sandwich U (\<iota> (G\<^sub>1 b))\<close>
            by (simp add: FG_def T_apply \<iota>_def)
          also have \<open>\<dots> = sandwich U (G' b)\<close>
            apply (rule arg_cong[where f=\<open>cblinfun_apply _\<close>])
            by (metis G\<^sub>1_def UNIV_I f_inv_into_f image_subset_iff o_def range_G')
          also have \<open>\<dots> = G b\<close>
            by (smt (verit) G'_def \<open>unitary U\<close> cblinfun_apply_cblinfun_compose cblinfun_compose_id_left cblinfun_compose_id_right comp_def id_cblinfun_adjoint sandwich.rep_eq sandwich_compose unitaryD2)
          finally have FG_b: \<open>FG (id_cblinfun \<otimes>\<^sub>o b) = G b\<close>
            by -
          have \<open>FG (a \<otimes>\<^sub>o b) = FG (a \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L FG (id_cblinfun \<otimes>\<^sub>o b)\<close>
            by (simp add: comp_tensor_op register_mult)
          also have \<open>\<dots> = F a o\<^sub>C\<^sub>L G b\<close>
            by (simp add: FG_a FG_b)
          finally show ?thesis
            by -
        qed
        with \<open>register FG\<close> show ?thesis
          by metis
      qed
    qed
    from this[cancel_with_type]
    show \<open>\<exists>R. \<forall>a b. register R \<and> R (a \<otimes>\<^sub>o b) = F a o\<^sub>C\<^sub>L G b\<close>
      by -
  qed
  from this[cancel_with_type]
  have \<open>\<exists>R. \<forall>a b. register R \<and> R (a \<otimes>\<^sub>o b) = F a o\<^sub>C\<^sub>L G b\<close>
    by -
  then have \<open>\<forall>a b. register (register_pair F G) \<and> (register_pair F G) (a \<otimes>\<^sub>o b) = F a o\<^sub>C\<^sub>L G b\<close>
    unfolding * by (smt (verit) someI_ex)
  then show \<open>(register_pair F G) (tensor_op a b) = F a o\<^sub>C\<^sub>L G b\<close> and \<open>register (register_pair F G)\<close>
    by auto
qed

unbundle no cblinfun_syntax

end
