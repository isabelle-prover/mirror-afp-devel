section \<open>Tensor products (finite dimensional)\<close>

theory Finite_Tensor_Product
  imports Complex_Bounded_Operators.Complex_L2 Misc
begin

declare cblinfun.scaleC_right[simp]

unbundle cblinfun_notation
no_notation m_inv ("inv\<index> _" [81] 80)

lift_definition tensor_ell2 :: \<open>'a::finite ell2 \<Rightarrow> 'b::finite ell2 \<Rightarrow> ('a\<times>'b) ell2\<close> (infixr "\<otimes>\<^sub>s" 70) is
  \<open>\<lambda>\<psi> \<phi> (i,j). \<psi> i * \<phi> j\<close>
  by simp

lemma tensor_ell2_add2: \<open>tensor_ell2 a (b + c) = tensor_ell2 a b + tensor_ell2 a c\<close>
  apply transfer apply (rule ext) apply (auto simp: case_prod_beta)
  by (meson algebra_simps)

lemma tensor_ell2_add1: \<open>tensor_ell2 (a + b) c = tensor_ell2 a c + tensor_ell2 b c\<close>
  apply transfer apply (rule ext) apply (auto simp: case_prod_beta)
  by (simp add: vector_space_over_itself.scale_left_distrib)

lemma tensor_ell2_scaleC2: \<open>tensor_ell2 a (c *\<^sub>C b) = c *\<^sub>C tensor_ell2 a b\<close>
  apply transfer apply (rule ext) by (auto simp: case_prod_beta)

lemma tensor_ell2_scaleC1: \<open>tensor_ell2 (c *\<^sub>C a) b = c *\<^sub>C tensor_ell2 a b\<close>
  apply transfer apply (rule ext) by (auto simp: case_prod_beta)

lemma tensor_ell2_inner_prod[simp]: \<open>\<langle>tensor_ell2 a b, tensor_ell2 c d\<rangle> = \<langle>a,c\<rangle> * \<langle>b,d\<rangle>\<close>
  apply transfer
  by (auto simp: case_prod_beta sum_product sum.cartesian_product mult.assoc mult.left_commute)

lemma clinear_tensor_ell21: "clinear (\<lambda>b. tensor_ell2 a b)"
  apply (rule clinearI; transfer)
   apply (auto simp: case_prod_beta)
  by (simp add: cond_case_prod_eta algebra_simps)

lemma clinear_tensor_ell22: "clinear (\<lambda>a. tensor_ell2 a b)"
  apply (rule clinearI; transfer)
   apply (auto simp: case_prod_beta)
  by (simp add: case_prod_beta' algebra_simps)

lemma tensor_ell2_ket[simp]: "tensor_ell2 (ket i) (ket j) = ket (i,j)"
  apply transfer by auto


definition tensor_op :: \<open>('a ell2, 'b::finite ell2) cblinfun \<Rightarrow> ('c ell2, 'd::finite ell2) cblinfun
      \<Rightarrow> (('a\<times>'c) ell2, ('b\<times>'d) ell2) cblinfun\<close> (infixr "\<otimes>\<^sub>o" 70) where
  \<open>tensor_op M N = (SOME P. \<forall>a c. P *\<^sub>V (ket (a,c))
      = tensor_ell2 (M *\<^sub>V ket a) (N *\<^sub>V ket c))\<close>

lemma tensor_op_ket: 
  fixes a :: \<open>'a::finite\<close> and b :: \<open>'b\<close> and c :: \<open>'c::finite\<close> and d :: \<open>'d\<close>
  shows \<open>tensor_op M N *\<^sub>V (ket (a,c)) = tensor_ell2 (M *\<^sub>V ket a) (N *\<^sub>V ket c)\<close>
proof -
  define S :: \<open>('a\<times>'c) ell2 set\<close> where "S = ket ` UNIV"
  define \<phi> where \<open>\<phi> = (\<lambda>(a,c). tensor_ell2 (M *\<^sub>V ket a) (N *\<^sub>V ket c))\<close>
  define \<phi>' where \<open>\<phi>' = \<phi> \<circ> inv ket\<close>

  have def: \<open>tensor_op M N = (SOME P. \<forall>a c. P *\<^sub>V (ket (a,c)) = \<phi> (a,c))\<close>
    unfolding tensor_op_def \<phi>_def by auto

  have \<open>cindependent S\<close>
    using S_def cindependent_ket by blast
  moreover have \<open>cspan S = UNIV\<close>
    using S_def cspan_range_ket_finite by blast
  ultimately have "cblinfun_extension_exists S \<phi>'"
    by (rule cblinfun_extension_exists_finite_dim)
  then have "\<exists>P. \<forall>x\<in>S. P *\<^sub>V x = \<phi>' x"
    unfolding cblinfun_extension_exists_def by auto
  then have ex: \<open>\<exists>P. \<forall>a c. P *\<^sub>V ket (a,c) = \<phi> (a,c)\<close>
    by (metis S_def \<phi>'_def comp_eq_dest_lhs inj_ket inv_f_f rangeI)


  then have \<open>tensor_op M N *\<^sub>V (ket (a,c)) = \<phi> (a,c)\<close>
    unfolding def apply (rule someI2_ex[where P=\<open>\<lambda>P. \<forall>a c. P *\<^sub>V (ket (a,c)) = \<phi> (a,c)\<close>])
    by auto
  then show ?thesis
    unfolding \<phi>_def by auto
qed


lemma tensor_op_ell2: "tensor_op A B *\<^sub>V tensor_ell2 \<psi> \<phi> = tensor_ell2 (A *\<^sub>V \<psi>) (B *\<^sub>V \<phi>)"
proof -
  have 1: \<open>clinear (\<lambda>a. tensor_op A B *\<^sub>V tensor_ell2 a (ket b))\<close> for b
    by (auto intro!: clinearI simp: tensor_ell2_add1 tensor_ell2_scaleC1 cblinfun.add_right)
  have 2: \<open>clinear (\<lambda>a. tensor_ell2 (A *\<^sub>V a) (B *\<^sub>V ket b))\<close> for b
    by (auto intro!: clinearI simp: tensor_ell2_add1 tensor_ell2_scaleC1 cblinfun.add_right)
  have 3: \<open>clinear (\<lambda>a. tensor_op A B *\<^sub>V tensor_ell2 \<psi> a)\<close>
    by (auto intro!: clinearI simp: tensor_ell2_add2 tensor_ell2_scaleC2 cblinfun.add_right)
  have 4: \<open>clinear (\<lambda>a. tensor_ell2 (A *\<^sub>V \<psi>) (B *\<^sub>V a))\<close>
    by (auto intro!: clinearI simp: tensor_ell2_add2 tensor_ell2_scaleC2 cblinfun.add_right)

  have eq_ket_ket: \<open>tensor_op A B *\<^sub>V tensor_ell2 (ket a) (ket b) = tensor_ell2 (A *\<^sub>V ket a) (B *\<^sub>V ket b)\<close> for a b
    by (simp add: tensor_op_ket)
  have eq_ket: \<open>tensor_op A B *\<^sub>V tensor_ell2 \<psi> (ket b) = tensor_ell2 (A *\<^sub>V \<psi>) (B *\<^sub>V ket b)\<close> for b
    apply (rule fun_cong[where x=\<psi>])
    using 1 2 eq_ket_ket by (rule clinear_equal_ket)
  show ?thesis 
    apply (rule fun_cong[where x=\<phi>])
    using 3 4 eq_ket by (rule clinear_equal_ket)
qed

lemma comp_tensor_op: "(tensor_op a b) o\<^sub>C\<^sub>L (tensor_op c d) = tensor_op (a o\<^sub>C\<^sub>L c) (b o\<^sub>C\<^sub>L d)"
  for a :: "'e::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c::finite ell2" and b :: "'f::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2" and
      c :: "'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'e ell2" and d :: "'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'f ell2"
  apply (rule equal_ket)
  apply (rename_tac ij, case_tac ij, rename_tac i j, hypsubst_thin)
  by (simp flip: tensor_ell2_ket add: tensor_op_ell2 cblinfun_apply_cblinfun_compose)


lemma tensor_op_cbilinear: \<open>cbilinear (tensor_op :: 'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::finite ell2
                                                 \<Rightarrow> 'c::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2 \<Rightarrow> _)\<close>
proof -
  have \<open>clinear (\<lambda>b::'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2. tensor_op a b)\<close> for a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
    apply (rule clinearI)
     apply (rule equal_ket, rename_tac ij, case_tac ij, rename_tac i j, hypsubst_thin)
     apply (simp flip: tensor_ell2_ket add: tensor_op_ell2 cblinfun.add_left tensor_ell2_add2)
    apply (rule equal_ket, rename_tac ij, case_tac ij, rename_tac i j, hypsubst_thin)
    by (simp add: scaleC_cblinfun.rep_eq tensor_ell2_scaleC2 tensor_op_ket)

  moreover have \<open>clinear (\<lambda>a::'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::finite ell2. tensor_op a b)\<close> for b :: \<open>'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
    apply (rule clinearI)
     apply (rule equal_ket, rename_tac ij, case_tac ij, rename_tac i j, hypsubst_thin)
     apply (simp flip: tensor_ell2_ket add: tensor_op_ell2 cblinfun.add_left tensor_ell2_add1)
    apply (rule equal_ket, rename_tac ij, case_tac ij, rename_tac i j, hypsubst_thin)
    by (simp add: scaleC_cblinfun.rep_eq tensor_ell2_scaleC1 tensor_op_ket)

  ultimately show ?thesis
    unfolding cbilinear_def by auto
qed


lemma tensor_butter: \<open>tensor_op (butterket i j) (butterket k l) = butterket (i,k) (j,l)\<close>
  for i :: "_" and j :: "_::finite" and k :: "_" and l :: "_::finite"
  apply (rule equal_ket, rename_tac x, case_tac x)
  apply (auto simp flip: tensor_ell2_ket simp: cblinfun_apply_cblinfun_compose tensor_op_ell2 butterfly_def)
  by (auto simp: tensor_ell2_scaleC1 tensor_ell2_scaleC2)

lemma cspan_tensor_op: \<open>cspan {tensor_op (butterket i j) (butterket k l)| i (j::_::finite) k (l::_::finite). True} = UNIV\<close>
  unfolding tensor_butter
  apply (subst cspan_butterfly_ket[symmetric])
  by (metis surj_pair)

lemma cindependent_tensor_op: \<open>cindependent {tensor_op (butterket i j) (butterket k l)| i (j::_::finite) k (l::_::finite). True}\<close>
  unfolding tensor_butter
  using cindependent_butterfly_ket
  by (smt (z3) Collect_mono_iff complex_vector.independent_mono)


lemma tensor_extensionality:
  fixes F G :: \<open>((('a::finite \<times> 'b::finite) ell2) \<Rightarrow>\<^sub>C\<^sub>L (('c::finite \<times> 'd::finite) ell2)) \<Rightarrow> 'e::complex_vector\<close>
  assumes [simp]: "clinear F" "clinear G"
  assumes tensor_eq: "(\<And>a b. F (tensor_op a b) = G (tensor_op a b))"
  shows "F = G"
proof (rule ext, rule complex_vector.linear_eq_on_span[where f=F and g=G])
  show \<open>clinear F\<close> and \<open>clinear G\<close>
    using assms by (simp_all add: cbilinear_def)
  show \<open>x \<in> cspan  {tensor_op (butterket i j) (butterket k l)| i j k l. True}\<close> 
    for x :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c \<times> 'd) ell2\<close>
    using cspan_tensor_op by auto
  show \<open>F x = G x\<close> if \<open>x \<in> {tensor_op (butterket i j) (butterket k l) |i j k l. True}\<close> for x
    using that by (auto simp: tensor_eq)
qed

lemma tensor_id[simp]: \<open>tensor_op id_cblinfun id_cblinfun = id_cblinfun\<close>
  apply (rule equal_ket, rename_tac x, case_tac x)
  by (simp flip: tensor_ell2_ket add: tensor_op_ell2)

lemma tensor_op_adjoint: \<open>(tensor_op a b)* = tensor_op (a*) (b*)\<close>
  apply (rule cinner_ket_adjointI[symmetric])
  apply (auto simp flip: tensor_ell2_ket simp: tensor_op_ell2)
  by (simp add: cinner_adj_left)

lemma tensor_butterfly[simp]: "tensor_op (butterfly \<psi> \<psi>') (butterfly \<phi> \<phi>') = butterfly (tensor_ell2 \<psi> \<phi>) (tensor_ell2 \<psi>' \<phi>')"
  apply (rule equal_ket, rename_tac x, case_tac x)
  by (simp flip: tensor_ell2_ket add: tensor_op_ell2 butterfly_def
      cblinfun_apply_cblinfun_compose tensor_ell2_scaleC1 tensor_ell2_scaleC2)

definition tensor_lift :: \<open>(('a1::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a2::finite ell2) \<Rightarrow> ('b1::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b2::finite ell2) \<Rightarrow> 'c)
                        \<Rightarrow> ((('a1\<times>'b1) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a2\<times>'b2) ell2) \<Rightarrow> 'c::complex_vector)\<close> where
  "tensor_lift F2 = (SOME G. clinear G \<and> (\<forall>a b. G (tensor_op a b) = F2 a b))"

lemma 
  fixes F2 :: "'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::finite ell2
            \<Rightarrow> 'c::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2
            \<Rightarrow> 'e::complex_normed_vector"
  assumes "cbilinear F2"
  shows tensor_lift_clinear: "clinear (tensor_lift F2)"
    and tensor_lift_correct:  \<open>(\<lambda>a b. tensor_lift F2 (tensor_op a b)) = F2\<close>
proof -
  define F2' t4 \<phi> where
    \<open>F2' = tensor_lift F2\<close> and
    \<open>t4 = (\<lambda>(i,j,k,l). tensor_op (butterket i j) (butterket k l))\<close> and
    \<open>\<phi> m = (let (i,j,k,l) = inv t4 m in F2 (butterket i j) (butterket k l))\<close> for m
  have t4inj: "x = y" if "t4 x = t4 y" for x y
  proof (rule ccontr)
    obtain i  j  k  l  where x: "x = (i,j,k,l)" by (meson prod_cases4) 
    obtain i' j' k' l' where y: "y = (i',j',k',l')" by (meson prod_cases4) 
    have 1: "bra (i,k) *\<^sub>V t4 x *\<^sub>V ket (j,l) = 1"
      by (auto simp: t4_def x tensor_op_ell2 butterfly_def cinner_ket simp flip: tensor_ell2_ket)
    assume \<open>x \<noteq> y\<close>
    then have 2: "bra (i,k) *\<^sub>V t4 y *\<^sub>V ket (j,l) = 0"
      by (auto simp: t4_def x y tensor_op_ell2 butterfly_def cblinfun_apply_cblinfun_compose cinner_ket
               simp flip: tensor_ell2_ket)
    from 1 2 that
    show False
      by auto
  qed
  have \<open>\<phi> (tensor_op (butterket i j) (butterket k l)) = F2 (butterket i j) (butterket k l)\<close> for i j k l
    apply (subst asm_rl[of \<open>tensor_op (butterket i j) (butterket k l) = t4 (i,j,k,l)\<close>])
     apply (simp add: t4_def)
    by (auto simp add: injI t4inj inv_f_f \<phi>_def)

  have *: \<open>range t4 = {tensor_op (butterket i j) (butterket k l) |i j k l. True}\<close>
    apply (auto simp: case_prod_beta t4_def)
    using image_iff by fastforce

  have "cblinfun_extension_exists (range t4) \<phi>"
    thm cblinfun_extension_exists_finite_dim[where \<phi>=\<phi>]
    apply (rule cblinfun_extension_exists_finite_dim)
     apply auto unfolding * 
    using cindependent_tensor_op
    using cspan_tensor_op
    by auto

  then obtain G where G: \<open>G *\<^sub>V (t4 (i,j,k,l)) = F2 (butterket i j) (butterket k l)\<close> for i j k l
    apply atomize_elim
    unfolding cblinfun_extension_exists_def
    apply auto
    by (metis (no_types, lifting) t4inj \<phi>_def f_inv_into_f rangeI split_conv)

  have *: \<open>G *\<^sub>V tensor_op (butterket i j) (butterket k l) = F2 (butterket i j) (butterket k l)\<close> for i j k l
    using G by (auto simp: t4_def)
  have *: \<open>G *\<^sub>V tensor_op a (butterket k l) = F2 a (butterket k l)\<close> for a k l
    apply (rule complex_vector.linear_eq_on_span[where g=\<open>\<lambda>a. F2 a _\<close> and B=\<open>{butterket k l|k l. True}\<close>])
    unfolding cspan_butterfly_ket
    using * apply (auto intro!: clinear_compose[unfolded o_def, where f=\<open>\<lambda>a. tensor_op a _\<close> and g=\<open>(*\<^sub>V) G\<close>])
     apply (metis cbilinear_def tensor_op_cbilinear)
    using assms unfolding cbilinear_def by blast
  have G_F2: \<open>G *\<^sub>V tensor_op a b = F2 a b\<close> for a b
    apply (rule complex_vector.linear_eq_on_span[where g=\<open>F2 a\<close> and B=\<open>{butterket k l|k l. True}\<close>])
    unfolding cspan_butterfly_ket
    using * apply (auto simp: cblinfun.add_right clinearI
                        intro!: clinear_compose[unfolded o_def, where f=\<open>tensor_op a\<close> and g=\<open>(*\<^sub>V) G\<close>])
    apply (meson cbilinear_def tensor_op_cbilinear)
    using assms unfolding cbilinear_def by blast

  have \<open>clinear F2' \<and> (\<forall>a b. F2' (tensor_op a b) = F2 a b)\<close>
    unfolding F2'_def tensor_lift_def 
    apply (rule someI[where x=\<open>(*\<^sub>V) G\<close> and P=\<open>\<lambda>G. clinear G \<and> (\<forall>a b. G (tensor_op a b) = F2 a b)\<close>])
    using G_F2 by (simp add: cblinfun.add_right clinearI)

  then show \<open>clinear F2'\<close> and \<open>(\<lambda>a b. tensor_lift F2 (tensor_op a b)) = F2\<close>
    unfolding F2'_def by auto
qed

lift_definition assoc_ell20 :: \<open>(('a::finite\<times>'b::finite)\<times>'c::finite) ell2 \<Rightarrow> ('a\<times>('b\<times>'c)) ell2\<close> is
  \<open>\<lambda>f (a,(b,c)). f ((a,b),c)\<close>
  by auto

lift_definition assoc_ell20' :: \<open>('a::finite\<times>('b::finite\<times>'c::finite)) ell2 \<Rightarrow> (('a\<times>'b)\<times>'c) ell2\<close> is
  \<open>\<lambda>f ((a,b),c). f (a,(b,c))\<close>
  by auto

lift_definition assoc_ell2 :: \<open>(('a::finite\<times>'b::finite)\<times>'c::finite) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>('b\<times>'c)) ell2\<close>
  is assoc_ell20
  apply (subst bounded_clinear_finite_dim)
   apply (rule clinearI; transfer)
  by auto

lift_definition assoc_ell2' :: \<open>('a::finite\<times>('b::finite\<times>'c::finite)) ell2 \<Rightarrow>\<^sub>C\<^sub>L (('a\<times>'b)\<times>'c) ell2\<close> is
  assoc_ell20'
  apply (subst bounded_clinear_finite_dim)
   apply (rule clinearI; transfer)
  by auto

lemma assoc_ell2_tensor: \<open>assoc_ell2 *\<^sub>V tensor_ell2 (tensor_ell2 a b) c = tensor_ell2 a (tensor_ell2 b c)\<close>
  apply (rule clinear_equal_ket[THEN fun_cong, where x=a])
    apply (simp add: cblinfun.add_right clinearI tensor_ell2_add1 tensor_ell2_scaleC1)
   apply (simp add: clinear_tensor_ell22)
  apply (rule clinear_equal_ket[THEN fun_cong, where x=b])
    apply (simp add: cblinfun.add_right clinearI tensor_ell2_add1 tensor_ell2_add2 tensor_ell2_scaleC1 tensor_ell2_scaleC2)
   apply (simp add: clinearI tensor_ell2_add1 tensor_ell2_add2 tensor_ell2_scaleC1 tensor_ell2_scaleC2)
  apply (rule clinear_equal_ket[THEN fun_cong, where x=c])
    apply (simp add: cblinfun.add_right clinearI tensor_ell2_add2 tensor_ell2_scaleC2)
   apply (simp add: clinearI tensor_ell2_add2 tensor_ell2_scaleC2)
  unfolding assoc_ell2.rep_eq
  apply transfer
  by auto

lemma assoc_ell2'_tensor: \<open>assoc_ell2' *\<^sub>V tensor_ell2 a (tensor_ell2 b c) = tensor_ell2 (tensor_ell2 a b) c\<close>
  apply (rule clinear_equal_ket[THEN fun_cong, where x=a])
    apply (simp add: cblinfun.add_right clinearI tensor_ell2_add1 tensor_ell2_scaleC1)
   apply (simp add: clinearI tensor_ell2_add1 tensor_ell2_scaleC1)
  apply (rule clinear_equal_ket[THEN fun_cong, where x=b])
    apply (simp add: cblinfun.add_right clinearI tensor_ell2_add1 tensor_ell2_add2 tensor_ell2_scaleC1 tensor_ell2_scaleC2)
   apply (simp add: clinearI tensor_ell2_add1 tensor_ell2_add2 tensor_ell2_scaleC1 tensor_ell2_scaleC2)
  apply (rule clinear_equal_ket[THEN fun_cong, where x=c])
    apply (simp add: cblinfun.add_right clinearI tensor_ell2_add2 tensor_ell2_scaleC2)
   apply (simp add: clinearI tensor_ell2_add2 tensor_ell2_scaleC2)
  unfolding assoc_ell2'.rep_eq
  apply transfer
  by auto

lemma adjoint_assoc_ell2[simp]: \<open>assoc_ell2* = assoc_ell2'\<close>
proof (rule adjoint_eqI[symmetric])
  have [simp]: \<open>clinear (cinner (assoc_ell2' *\<^sub>V x))\<close> for x :: \<open>('a \<times> 'b \<times> 'c) ell2\<close>
    by (metis (no_types, lifting) cblinfun.add_right cinner_scaleC_right clinearI complex_scaleC_def mult.comm_neutral of_complex_def vector_to_cblinfun_adj_apply)
  have [simp]: \<open>clinear (\<lambda>a. \<langle>x, assoc_ell2 *\<^sub>V a\<rangle>)\<close> for x :: \<open>('a \<times> 'b \<times> 'c) ell2\<close>
    by (simp add: cblinfun.add_right cinner_add_right clinearI)
  have [simp]: \<open>antilinear (\<lambda>a. \<langle>a, y\<rangle>)\<close> for y :: \<open>('a \<times> 'b \<times> 'c) ell2\<close>
    using bounded_antilinear_cinner_left bounded_antilinear_def by blast
  have [simp]: \<open>antilinear (\<lambda>a. \<langle>assoc_ell2' *\<^sub>V a, y\<rangle>)\<close> for y :: \<open>(('a \<times> 'b) \<times> 'c) ell2\<close>
    by (simp add: cblinfun.add_right cinner_add_left antilinearI)
  have \<open>\<langle>assoc_ell2' *\<^sub>V (ket x), ket y\<rangle> = \<langle>ket x, assoc_ell2 *\<^sub>V ket y\<rangle>\<close> for x :: \<open>'a \<times> 'b \<times> 'c\<close> and y
    apply (cases x, cases y)
    by (simp flip: tensor_ell2_ket add: assoc_ell2'_tensor assoc_ell2_tensor)
  then have \<open>\<langle>assoc_ell2' *\<^sub>V (ket x), y\<rangle> = \<langle>ket x, assoc_ell2 *\<^sub>V y\<rangle>\<close> for x :: \<open>'a \<times> 'b \<times> 'c\<close> and y
    by (rule clinear_equal_ket[THEN fun_cong, rotated 2], simp_all)
  then show \<open>\<langle>assoc_ell2' *\<^sub>V x, y\<rangle> = \<langle>x, assoc_ell2 *\<^sub>V y\<rangle>\<close> for x :: \<open>('a \<times> 'b \<times> 'c) ell2\<close> and y
    by (rule antilinear_equal_ket[THEN fun_cong, rotated 2], simp_all)
qed

lemma adjoint_assoc_ell2'[simp]: \<open>assoc_ell2'* = assoc_ell2\<close>
  by (simp flip: adjoint_assoc_ell2)


lift_definition swap_ell20 :: \<open>('a::finite\<times>'b::finite) ell2 \<Rightarrow> ('b\<times>'a) ell2\<close> is
  \<open>\<lambda>f (a,b). f (b,a)\<close>
  by auto

lift_definition swap_ell2 :: \<open>('a::finite\<times>'b::finite) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b\<times>'a) ell2\<close>
  is swap_ell20
  apply (subst bounded_clinear_finite_dim)
   apply (rule clinearI; transfer)
  by auto

lemma swap_ell2_tensor[simp]: \<open>swap_ell2 *\<^sub>V tensor_ell2 a b = tensor_ell2 b a\<close>
  apply (rule clinear_equal_ket[THEN fun_cong, where x=a])
    apply (simp add: cblinfun.add_right clinearI tensor_ell2_add1 tensor_ell2_scaleC1)
   apply (simp add: clinear_tensor_ell21)
  apply (rule clinear_equal_ket[THEN fun_cong, where x=b])
    apply (simp add: cblinfun.add_right clinearI tensor_ell2_add1 tensor_ell2_add2 tensor_ell2_scaleC1 tensor_ell2_scaleC2)
   apply (simp add: clinearI tensor_ell2_add1 tensor_ell2_add2 tensor_ell2_scaleC1 tensor_ell2_scaleC2)
  unfolding swap_ell2.rep_eq
  apply transfer
  by auto

lemma adjoint_swap_ell2[simp]: \<open>swap_ell2* = swap_ell2\<close>
proof (rule adjoint_eqI[symmetric])
  have [simp]: \<open>clinear (cinner (swap_ell2 *\<^sub>V x))\<close> for x :: \<open>('a \<times> 'b) ell2\<close>
    by (metis (no_types, lifting) cblinfun.add_right cinner_scaleC_right clinearI complex_scaleC_def mult.comm_neutral of_complex_def vector_to_cblinfun_adj_apply)
  have [simp]: \<open>clinear (\<lambda>a. \<langle>x, swap_ell2 *\<^sub>V a\<rangle>)\<close> for x :: \<open>('a \<times> 'b) ell2\<close>
    by (simp add: cblinfun.add_right cinner_add_right clinearI)
  have [simp]: \<open>antilinear (\<lambda>a. \<langle>a, y\<rangle>)\<close> for y :: \<open>('a \<times> 'b) ell2\<close>
    using bounded_antilinear_cinner_left bounded_antilinear_def by blast
  have [simp]: \<open>antilinear (\<lambda>a. \<langle>swap_ell2 *\<^sub>V a, y\<rangle>)\<close> for y :: \<open>('b \<times> 'a) ell2\<close>
    by (simp add: cblinfun.add_right cinner_add_left antilinearI)
  have \<open>\<langle>swap_ell2 *\<^sub>V (ket x), ket y\<rangle> = \<langle>ket x, swap_ell2 *\<^sub>V ket y\<rangle>\<close> for x :: \<open>'a \<times> 'b\<close> and y
    apply (cases x, cases y)
    by (simp flip: tensor_ell2_ket add: swap_ell2_tensor)
  then have \<open>\<langle>swap_ell2 *\<^sub>V (ket x), y\<rangle> = \<langle>ket x, swap_ell2 *\<^sub>V y\<rangle>\<close> for x :: \<open>'a \<times> 'b\<close> and y
    by (rule clinear_equal_ket[THEN fun_cong, rotated 2], simp_all)
  then show \<open>\<langle>swap_ell2 *\<^sub>V x, y\<rangle> = \<langle>x, swap_ell2 *\<^sub>V y\<rangle>\<close> for x :: \<open>('a \<times> 'b) ell2\<close> and y
    apply (rule antilinear_equal_ket[THEN fun_cong, rotated 2])
    by simp_all
qed


lemma tensor_ell2_extensionality:
  assumes "(\<And>s t. a *\<^sub>V (s \<otimes>\<^sub>s t) = b *\<^sub>V (s \<otimes>\<^sub>s t))"
  shows "a = b"
  apply (rule equal_ket, case_tac x, hypsubst_thin)
  by (simp add: assms flip: tensor_ell2_ket)

lemma assoc_ell2'_assoc_ell2[simp]: \<open>assoc_ell2' o\<^sub>C\<^sub>L assoc_ell2 = id_cblinfun\<close>
  by (auto intro!: equal_ket simp: cblinfun_apply_cblinfun_compose assoc_ell2'_tensor assoc_ell2_tensor simp flip: tensor_ell2_ket)

lemma assoc_ell2_assoc_ell2'[simp]: \<open>assoc_ell2 o\<^sub>C\<^sub>L assoc_ell2' = id_cblinfun\<close>
  by (auto intro!: equal_ket simp: cblinfun_apply_cblinfun_compose assoc_ell2'_tensor assoc_ell2_tensor simp flip: tensor_ell2_ket)

lemma unitary_assoc_ell2[simp]: "unitary assoc_ell2"
  unfolding unitary_def by auto

lemma unitary_assoc_ell2'[simp]: "unitary assoc_ell2'"
  unfolding unitary_def by auto

lemma tensor_op_left_add: \<open>(x + y) \<otimes>\<^sub>o b = x \<otimes>\<^sub>o b + y \<otimes>\<^sub>o b\<close>
  for x y :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c::finite ell2\<close> and b :: \<open>'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2\<close>
  apply (auto intro!: equal_ket simp: tensor_op_ket)
  by (simp add: plus_cblinfun.rep_eq tensor_ell2_add1 tensor_op_ket)

lemma tensor_op_right_add: \<open>b \<otimes>\<^sub>o (x + y) = b \<otimes>\<^sub>o x + b \<otimes>\<^sub>o y\<close>
  for x y :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c::finite ell2\<close> and b :: \<open>'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2\<close>
  apply (auto intro!: equal_ket simp: tensor_op_ket)
  by (simp add: plus_cblinfun.rep_eq tensor_ell2_add2 tensor_op_ket)

lemma tensor_op_scaleC_left: \<open>(c *\<^sub>C x) \<otimes>\<^sub>o b = c *\<^sub>C (x \<otimes>\<^sub>o b)\<close>
  for x :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c::finite ell2\<close> and b :: \<open>'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2\<close>
  apply (auto intro!: equal_ket simp: tensor_op_ket)
  by (metis scaleC_cblinfun.rep_eq tensor_ell2_ket tensor_ell2_scaleC1 tensor_op_ell2)

lemma tensor_op_scaleC_right: \<open>b \<otimes>\<^sub>o (c *\<^sub>C x) = c *\<^sub>C (b \<otimes>\<^sub>o x)\<close>
  for x :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c::finite ell2\<close> and b :: \<open>'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2\<close>
  apply (auto intro!: equal_ket simp: tensor_op_ket)
  by (metis scaleC_cblinfun.rep_eq tensor_ell2_ket tensor_ell2_scaleC2 tensor_op_ell2)

lemma clinear_tensor_left[simp]: \<open>clinear (\<lambda>a. a \<otimes>\<^sub>o b :: _::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L _::finite ell2)\<close>
  apply (rule clinearI)
   apply (rule tensor_op_left_add)
  by (rule tensor_op_scaleC_left)

lemma clinear_tensor_right[simp]: \<open>clinear (\<lambda>b. a \<otimes>\<^sub>o b :: _::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L _::finite ell2)\<close>
  apply (rule clinearI)
   apply (rule tensor_op_right_add)
  by (rule tensor_op_scaleC_right)

lemma tensor_ell2_nonzero: \<open>a \<otimes>\<^sub>s b \<noteq> 0\<close> if \<open>a \<noteq> 0\<close> and \<open>b \<noteq> 0\<close>
  apply (use that in transfer)
  apply auto
  by (metis mult_eq_0_iff old.prod.case)

lemma tensor_op_nonzero:
  fixes a :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c::finite ell2\<close> and b :: \<open>'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2\<close>
  assumes \<open>a \<noteq> 0\<close> and \<open>b \<noteq> 0\<close>
  shows \<open>a \<otimes>\<^sub>o b \<noteq> 0\<close>
proof -
  from \<open>a \<noteq> 0\<close> obtain i where i: \<open>a *\<^sub>V ket i \<noteq> 0\<close>
    by (metis cblinfun.zero_left equal_ket)
  from \<open>b \<noteq> 0\<close> obtain j where j: \<open>b *\<^sub>V ket j \<noteq> 0\<close>
    by (metis cblinfun.zero_left equal_ket)
  from i j have ijneq0: \<open>(a *\<^sub>V ket i) \<otimes>\<^sub>s (b *\<^sub>V ket j) \<noteq> 0\<close>
    by (simp add: tensor_ell2_nonzero)
  have \<open>(a *\<^sub>V ket i) \<otimes>\<^sub>s (b *\<^sub>V ket j) = (a \<otimes>\<^sub>o b) *\<^sub>V ket (i,j)\<close>
    by (simp add: tensor_op_ket)
  with ijneq0 show \<open>a \<otimes>\<^sub>o b \<noteq> 0\<close>
    by force
qed

lemma inj_tensor_ell2_left: \<open>inj (\<lambda>a::'a::finite ell2. a \<otimes>\<^sub>s b)\<close> if \<open>b \<noteq> 0\<close> for b :: \<open>'b::finite ell2\<close>
proof (rule injI, rule ccontr)
  fix x y :: \<open>'a ell2\<close>
  assume eq: \<open>x \<otimes>\<^sub>s b = y \<otimes>\<^sub>s b\<close>
  assume neq: \<open>x \<noteq> y\<close>
  define a where \<open>a = x - y\<close>
  from neq a_def have neq0: \<open>a \<noteq> 0\<close>
    by auto
  with \<open>b \<noteq> 0\<close> have \<open>a \<otimes>\<^sub>s b \<noteq> 0\<close>
    by (simp add: tensor_ell2_nonzero)
  then have \<open>x \<otimes>\<^sub>s b \<noteq> y \<otimes>\<^sub>s b\<close>
    unfolding a_def
    by (metis add_cancel_left_left diff_add_cancel tensor_ell2_add1)
  with eq show False
    by auto
qed

lemma inj_tensor_ell2_right: \<open>inj (\<lambda>b::'b::finite ell2. a \<otimes>\<^sub>s b)\<close> if \<open>a \<noteq> 0\<close> for a :: \<open>'a::finite ell2\<close>
proof (rule injI, rule ccontr)
  fix x y :: \<open>'b ell2\<close>
  assume eq: \<open>a \<otimes>\<^sub>s x = a \<otimes>\<^sub>s y\<close>
  assume neq: \<open>x \<noteq> y\<close>
  define b where \<open>b = x - y\<close>
  from neq b_def have neq0: \<open>b \<noteq> 0\<close>
    by auto
  with \<open>a \<noteq> 0\<close> have \<open>a \<otimes>\<^sub>s b \<noteq> 0\<close>
    by (simp add: tensor_ell2_nonzero)
  then have \<open>a \<otimes>\<^sub>s x \<noteq> a \<otimes>\<^sub>s y\<close>
    unfolding b_def
    by (metis add_cancel_left_left diff_add_cancel tensor_ell2_add2)
  with eq show False
    by auto
qed



lemma inj_tensor_left: \<open>inj (\<lambda>a::'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c::finite ell2. a \<otimes>\<^sub>o b)\<close> if \<open>b \<noteq> 0\<close> for b :: \<open>'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2\<close>
proof (rule injI, rule ccontr)
  fix x y :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close>
  assume eq: \<open>x \<otimes>\<^sub>o b = y \<otimes>\<^sub>o b\<close>
  assume neq: \<open>x \<noteq> y\<close>
  define a where \<open>a = x - y\<close>
  from neq a_def have neq0: \<open>a \<noteq> 0\<close>
    by auto
  with \<open>b \<noteq> 0\<close> have \<open>a \<otimes>\<^sub>o b \<noteq> 0\<close>
    by (simp add: tensor_op_nonzero)
  then have \<open>x \<otimes>\<^sub>o b \<noteq> y \<otimes>\<^sub>o b\<close>
    unfolding a_def
    by (metis add_cancel_left_left diff_add_cancel tensor_op_left_add) 
  with eq show False
    by auto
qed

lemma inj_tensor_right: \<open>inj (\<lambda>b::'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c::finite ell2. a \<otimes>\<^sub>o b)\<close> if \<open>a \<noteq> 0\<close> for a :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2\<close>
proof (rule injI, rule ccontr)
  fix x y :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close>
  assume eq: \<open>a \<otimes>\<^sub>o x = a \<otimes>\<^sub>o y\<close>
  assume neq: \<open>x \<noteq> y\<close>
  define b where \<open>b = x - y\<close>
  from neq b_def have neq0: \<open>b \<noteq> 0\<close>
    by auto
  with \<open>a \<noteq> 0\<close> have \<open>a \<otimes>\<^sub>o b \<noteq> 0\<close>
    by (simp add: tensor_op_nonzero)
  then have \<open>a \<otimes>\<^sub>o x \<noteq> a \<otimes>\<^sub>o y\<close>
    unfolding b_def
    by (metis add_cancel_left_left diff_add_cancel tensor_op_right_add) 
  with eq show False
    by auto
qed

lemma tensor_ell2_almost_injective:
  assumes \<open>tensor_ell2 a b = tensor_ell2 c d\<close>
  assumes \<open>a \<noteq> 0\<close>
  shows \<open>\<exists>\<gamma>. b = \<gamma> *\<^sub>C d\<close>
proof -
  from \<open>a \<noteq> 0\<close> obtain i where i: \<open>cinner (ket i) a \<noteq> 0\<close>
    by (metis cinner_eq_zero_iff cinner_ket_left ell2_pointwise_ortho)
  have \<open>cinner (ket i \<otimes>\<^sub>s ket j) (a \<otimes>\<^sub>s b) = cinner (ket i \<otimes>\<^sub>s ket j) (c \<otimes>\<^sub>s d)\<close> for j
    using assms by simp
  then have eq2: \<open>(cinner (ket i) a) * (cinner (ket j) b) = (cinner (ket i) c) * (cinner (ket j) d)\<close> for j
    by (metis tensor_ell2_inner_prod)
  then obtain \<gamma> where \<open>cinner (ket i) c = \<gamma> * cinner (ket i) a\<close>
    by (metis i eq_divide_eq)
  with eq2 have \<open>(cinner (ket i) a) * (cinner (ket j) b) = (cinner (ket i) a) * (\<gamma> * cinner (ket j) d)\<close> for j
    by simp
  then have \<open>cinner (ket j) b = cinner (ket j) (\<gamma> *\<^sub>C d)\<close> for j
    using i by force
  then have \<open>b = \<gamma> *\<^sub>C d\<close>
    by (simp add: cinner_ket_eqI)
  then show ?thesis
    by auto
qed


lemma tensor_op_almost_injective:
  fixes a c :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::finite ell2\<close>
    and b d :: \<open>'c::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2\<close>
  assumes \<open>tensor_op a b = tensor_op c d\<close>
  assumes \<open>a \<noteq> 0\<close>
  shows \<open>\<exists>\<gamma>. b = \<gamma> *\<^sub>C d\<close>
proof (cases \<open>d = 0\<close>)
  case False
  from \<open>a \<noteq> 0\<close> obtain \<psi> where \<psi>: \<open>a *\<^sub>V \<psi> \<noteq> 0\<close>
    by (metis cblinfun.zero_left cblinfun_eqI)
  have \<open>(a \<otimes>\<^sub>o b) (\<psi> \<otimes>\<^sub>s \<phi>) = (c \<otimes>\<^sub>o d) (\<psi> \<otimes>\<^sub>s \<phi>)\<close> for \<phi>
    using assms by simp
  then have eq2: \<open>(a \<psi>) \<otimes>\<^sub>s (b \<phi>) = (c \<psi>) \<otimes>\<^sub>s (d \<phi>)\<close> for \<phi>
    by (simp add: tensor_op_ell2)
  then have eq2': \<open>(d \<phi>) \<otimes>\<^sub>s (c \<psi>) = (b \<phi>) \<otimes>\<^sub>s (a \<psi>)\<close> for \<phi>
    by (metis swap_ell2_tensor)
  from False obtain \<phi>0 where \<phi>0: \<open>d \<phi>0 \<noteq> 0\<close>
    by (metis cblinfun.zero_left cblinfun_eqI)
  obtain \<gamma> where \<open>c \<psi> = \<gamma> *\<^sub>C a \<psi>\<close>
    apply atomize_elim
    using eq2' \<phi>0 by (rule tensor_ell2_almost_injective)
  with eq2 have \<open>(a \<psi>) \<otimes>\<^sub>s (b \<phi>) = (a \<psi>) \<otimes>\<^sub>s (\<gamma> *\<^sub>C d \<phi>)\<close> for \<phi>
    by (simp add: tensor_ell2_scaleC1 tensor_ell2_scaleC2)
  then have \<open>b \<phi> = \<gamma> *\<^sub>C d \<phi>\<close> for \<phi>
    by (smt (verit, best) \<psi> complex_vector.scale_cancel_right tensor_ell2_almost_injective tensor_ell2_nonzero tensor_ell2_scaleC2)
  then have \<open>b = \<gamma> *\<^sub>C d\<close>
    by (simp add: cblinfun_eqI)
  then show ?thesis
    by auto
next
  case True
  then have \<open>c \<otimes>\<^sub>o d = 0\<close>
    by (metis add_cancel_right_left tensor_op_right_add)
  then have \<open>a \<otimes>\<^sub>o b = 0\<close>
    using assms(1) by presburger
  with \<open>a \<noteq> 0\<close> have \<open>b = 0\<close>
    by (meson tensor_op_nonzero)
  then show ?thesis
    by auto
qed


lemma tensor_ell2_0_left[simp]: \<open>tensor_ell2 0 x = 0\<close>
  apply transfer by auto

lemma tensor_ell2_0_right[simp]: \<open>tensor_ell2 x 0 = 0\<close>
  apply transfer by auto

lemma tensor_op_0_left[simp]: \<open>tensor_op 0 x = (0 :: ('a::finite*'b::finite) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c::finite*'d::finite) ell2)\<close>
  apply (rule equal_ket)
  by (auto simp flip: tensor_ell2_ket simp: tensor_op_ell2)

lemma tensor_op_0_right[simp]: \<open>tensor_op x 0 = (0 :: ('a::finite*'b::finite) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c::finite*'d::finite) ell2)\<close>
  apply (rule equal_ket)
  by (auto simp flip: tensor_ell2_ket simp: tensor_op_ell2)

lemma bij_tensor_ell2_one_dim_left:
  assumes \<open>\<psi> \<noteq> 0\<close>
  shows \<open>bij (\<lambda>x::'b::finite ell2. (\<psi> :: 'a::CARD_1 ell2) \<otimes>\<^sub>s x)\<close>
proof (rule bijI)
  show \<open>inj (\<lambda>x::'b::finite ell2. (\<psi> :: 'a::CARD_1 ell2) \<otimes>\<^sub>s x)\<close>
    using assms by (rule inj_tensor_ell2_right)
  have \<open>\<exists>x. \<psi> \<otimes>\<^sub>s x = \<phi>\<close> for \<phi> :: \<open>('a*'b) ell2\<close>
  proof (use assms in transfer)
    fix \<psi> :: \<open>'a \<Rightarrow> complex\<close> and \<phi> :: \<open>'a*'b \<Rightarrow> complex\<close>
    assume \<open>has_ell2_norm \<phi>\<close> and \<open>\<psi> \<noteq> (\<lambda>_. 0)\<close>
    define c where \<open>c = \<psi> undefined\<close>
    then have \<open>\<psi> a = c\<close> for a 
      apply (subst everything_the_same[of _ undefined])
      by simp
    with \<open>\<psi> \<noteq> (\<lambda>_. 0)\<close> have \<open>c \<noteq> 0\<close>
      by auto

    define x where \<open>x j = \<phi> (undefined, j) / c\<close> for j
    have \<open>(\<lambda>(i, j). \<psi> i * x j) = \<phi>\<close>
      apply (auto intro!: ext simp: x_def \<open>\<psi> _ = c\<close> \<open>c \<noteq> 0\<close>)
      apply (subst (2) everything_the_same[of _ undefined])
      by simp
    then show \<open>\<exists>x\<in>Collect has_ell2_norm. (\<lambda>(i, j). \<psi> i * x j) = \<phi>\<close>
      apply (rule bexI[where x=x])
      by simp
  qed

  then show \<open>surj (\<lambda>x::'b::finite ell2. (\<psi> :: 'a::CARD_1 ell2) \<otimes>\<^sub>s x)\<close>
    by (metis surj_def)
qed

lemma bij_tensor_op_one_dim_left:
  assumes \<open>a \<noteq> 0\<close>
  shows \<open>bij (\<lambda>x::'c::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2. (a :: 'a::{CARD_1,enum} ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::{CARD_1,enum} ell2) \<otimes>\<^sub>o x)\<close>
proof (rule bijI)
  define t where \<open>t = (\<lambda>x::'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2. (a :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) \<otimes>\<^sub>o x)\<close>
  define i where
    \<open>i = tensor_lift (\<lambda>(x::'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) (y::'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2). (one_dim_iso x / one_dim_iso a) *\<^sub>C y)\<close>

  have [simp]: \<open>clinear i\<close>
    by (auto intro!: tensor_lift_clinear simp: i_def cbilinear_def clinearI scaleC_add_left add_divide_distrib)
  have [simp]: \<open>clinear t\<close>
    by (simp add: t_def)
  have \<open>i (x \<otimes>\<^sub>o y) = (one_dim_iso x / one_dim_iso a) *\<^sub>C y\<close> for x y
    by (auto intro!: clinearI tensor_lift_correct[THEN fun_cong, THEN fun_cong] simp: t_def i_def cbilinear_def  scaleC_add_left add_divide_distrib)
  then have \<open>t (i (x \<otimes>\<^sub>o y)) = x \<otimes>\<^sub>o y\<close> for x y
    apply (simp add: t_def)
    by (smt (z3) assms complex_vector.scale_eq_0_iff nonzero_mult_div_cancel_right one_dim_scaleC_1 scaleC_scaleC tensor_op_scaleC_left tensor_op_scaleC_right times_divide_eq_left)
  then have \<open>t (i x) = x\<close> for x
    apply (rule_tac fun_cong[where x=x])
    apply (rule tensor_extensionality)
    by (auto intro: clinear_compose complex_vector.module_hom_ident simp flip: o_def[of t i])
  then show \<open>surj t\<close> 
    by (rule surjI)

  show \<open>inj t\<close>
    unfolding t_def using assms by (rule inj_tensor_right)
qed

lemma swap_ell2_selfinv[simp]: \<open>swap_ell2 o\<^sub>C\<^sub>L swap_ell2 = id_cblinfun\<close>
  apply (rule tensor_ell2_extensionality)
  by auto

lemma bij_tensor_op_one_dim_right:
  assumes \<open>b \<noteq> 0\<close>
  shows \<open>bij (\<lambda>x::'c::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2. x \<otimes>\<^sub>o (b :: 'a::{CARD_1,enum} ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::{CARD_1,enum} ell2))\<close>
    (is \<open>bij ?f\<close>)
proof -
  let ?sf = \<open>(\<lambda>x. swap_ell2 o\<^sub>C\<^sub>L (?f x) o\<^sub>C\<^sub>L swap_ell2)\<close>
  let ?s = \<open>(\<lambda>x. swap_ell2 o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L swap_ell2)\<close>
  let ?g = \<open>(\<lambda>x::'c::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2. (b :: 'a::{CARD_1,enum} ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::{CARD_1,enum} ell2) \<otimes>\<^sub>o x)\<close>
  have \<open>?sf = ?g\<close>
    by (auto intro!: ext tensor_ell2_extensionality simp add: swap_ell2_tensor tensor_op_ell2)
  have \<open>bij ?g\<close>
    using assms by (rule bij_tensor_op_one_dim_left)
  have \<open>?s o ?sf = ?f\<close>
    apply (auto intro!: ext simp: cblinfun_assoc_left)
    by (auto simp: cblinfun_assoc_right)
  also have \<open>bij ?s\<close>
    apply (rule o_bij[where g=\<open>(\<lambda>x. swap_ell2 o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L swap_ell2)\<close>])
     apply (auto intro!: ext simp: cblinfun_assoc_left)
    by (auto simp: cblinfun_assoc_right)
  show \<open>bij ?f\<close>
    apply (subst \<open>?s o ?sf = ?f\<close>[symmetric], subst \<open>?sf = ?g\<close>)
    using \<open>bij ?g\<close> \<open>bij ?s\<close> by (rule bij_comp)
qed

lemma overlapping_tensor:
  fixes a23 :: \<open>('a2::finite*'a3::finite) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b2::finite*'b3::finite) ell2\<close>
    and b12 :: \<open>('a1::finite*'a2) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b1::finite*'b2) ell2\<close>
  assumes eq: \<open>butterfly \<psi> \<psi>' \<otimes>\<^sub>o a23 = assoc_ell2 o\<^sub>C\<^sub>L (b12 \<otimes>\<^sub>o butterfly \<phi> \<phi>') o\<^sub>C\<^sub>L assoc_ell2'\<close>
  assumes \<open>\<psi> \<noteq> 0\<close> \<open>\<psi>' \<noteq> 0\<close> \<open>\<phi> \<noteq> 0\<close> \<open>\<phi>' \<noteq> 0\<close>
  shows \<open>\<exists>c. butterfly \<psi> \<psi>' \<otimes>\<^sub>o a23 = butterfly \<psi> \<psi>' \<otimes>\<^sub>o c \<otimes>\<^sub>o butterfly \<phi> \<phi>'\<close>
proof -
  note [[show_types]]
  let ?id1 = \<open>id_cblinfun :: unit ell2 \<Rightarrow>\<^sub>C\<^sub>L unit ell2\<close>
  note id_cblinfun_eq_1[simp del]
  define d where \<open>d = butterfly \<psi> \<psi>' \<otimes>\<^sub>o a23\<close>

  define \<psi>\<^sub>n \<psi>\<^sub>n' a23\<^sub>n where \<open>\<psi>\<^sub>n = \<psi> /\<^sub>C norm \<psi>\<close> and \<open>\<psi>\<^sub>n' = \<psi>' /\<^sub>C norm \<psi>'\<close> and \<open>a23\<^sub>n = norm \<psi> *\<^sub>C norm \<psi>' *\<^sub>C a23\<close>
  have [simp]: \<open>norm \<psi>\<^sub>n = 1\<close> \<open>norm \<psi>\<^sub>n' = 1\<close>
    using \<open>\<psi> \<noteq> 0\<close> \<open>\<psi>' \<noteq> 0\<close> by (auto simp: \<psi>\<^sub>n_def \<psi>\<^sub>n'_def norm_inverse)
  have n1: \<open>butterfly \<psi>\<^sub>n \<psi>\<^sub>n' \<otimes>\<^sub>o a23\<^sub>n = butterfly \<psi> \<psi>' \<otimes>\<^sub>o a23\<close>
    apply (auto simp: \<psi>\<^sub>n_def \<psi>\<^sub>n'_def a23\<^sub>n_def tensor_op_scaleC_left tensor_op_scaleC_right)
    by (metis (no_types, lifting) assms(2) assms(3) inverse_mult_distrib mult.commute no_zero_divisors norm_eq_zero of_real_eq_0_iff right_inverse scaleC_one)

  define \<phi>\<^sub>n \<phi>\<^sub>n' b12\<^sub>n where \<open>\<phi>\<^sub>n = \<phi> /\<^sub>C norm \<phi>\<close> and \<open>\<phi>\<^sub>n' = \<phi>' /\<^sub>C norm \<phi>'\<close> and \<open>b12\<^sub>n = norm \<phi> *\<^sub>C norm \<phi>' *\<^sub>C b12\<close>
  have [simp]: \<open>norm \<phi>\<^sub>n = 1\<close> \<open>norm \<phi>\<^sub>n' = 1\<close>
    using \<open>\<phi> \<noteq> 0\<close> \<open>\<phi>' \<noteq> 0\<close> by (auto simp: \<phi>\<^sub>n_def \<phi>\<^sub>n'_def norm_inverse)
  have n2: \<open>b12\<^sub>n \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n' = b12 \<otimes>\<^sub>o butterfly \<phi> \<phi>'\<close>
    apply (auto simp: \<phi>\<^sub>n_def \<phi>\<^sub>n'_def b12\<^sub>n_def tensor_op_scaleC_left tensor_op_scaleC_right)
    by (metis (no_types, lifting) assms(4) assms(5) field_class.field_inverse inverse_mult_distrib mult.commute no_zero_divisors norm_eq_zero of_real_hom.hom_0 scaleC_one)

  define c' :: \<open>(unit*'a2*unit) ell2 \<Rightarrow>\<^sub>C\<^sub>L (unit*'b2*unit) ell2\<close> 
    where \<open>c' = (vector_to_cblinfun \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o vector_to_cblinfun \<phi>\<^sub>n)* o\<^sub>C\<^sub>L d
            o\<^sub>C\<^sub>L (vector_to_cblinfun \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o vector_to_cblinfun \<phi>\<^sub>n')\<close>

  define c'' :: \<open>'a2 ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b2 ell2\<close>
    where \<open>c'' = inv (\<lambda>c''. id_cblinfun \<otimes>\<^sub>o c'' \<otimes>\<^sub>o id_cblinfun) c'\<close>

  have *: \<open>bij (\<lambda>c''::'a2 ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b2 ell2. ?id1 \<otimes>\<^sub>o c'' \<otimes>\<^sub>o ?id1)\<close>
    apply (subst asm_rl[of \<open>_ = (\<lambda>x. id_cblinfun \<otimes>\<^sub>o x) o (\<lambda>c''. c'' \<otimes>\<^sub>o id_cblinfun)\<close>])
    using [[show_consts]]
    by (auto intro!: bij_comp bij_tensor_op_one_dim_left bij_tensor_op_one_dim_right)

  have c'_c'': \<open>c' = ?id1 \<otimes>\<^sub>o c'' \<otimes>\<^sub>o ?id1\<close>
    unfolding c''_def 
    apply (rule surj_f_inv_f[where y=c', symmetric])
    using * by (rule bij_is_surj)

  define c :: \<open>'a2 ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b2 ell2\<close>
    where \<open>c = c'' /\<^sub>C norm \<psi> /\<^sub>C norm \<psi>' /\<^sub>C norm \<phi> /\<^sub>C norm \<phi>'\<close>

  have aux: \<open>assoc_ell2' o\<^sub>C\<^sub>L (assoc_ell2 o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L assoc_ell2') o\<^sub>C\<^sub>L assoc_ell2 = x\<close> for x
    apply (simp add: cblinfun_assoc_left)
    by (simp add: cblinfun_assoc_right)
  have aux2: \<open>(assoc_ell2 o\<^sub>C\<^sub>L ((x \<otimes>\<^sub>o y) \<otimes>\<^sub>o z) o\<^sub>C\<^sub>L assoc_ell2') = x \<otimes>\<^sub>o (y \<otimes>\<^sub>o z)\<close> for x y z
    apply (rule equal_ket, rename_tac xyz)
    apply (case_tac xyz, hypsubst_thin)
    by (simp flip: tensor_ell2_ket add: assoc_ell2'_tensor assoc_ell2_tensor tensor_op_ell2)

  have \<open>d = (butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L d o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun)\<close>
    by (auto simp: d_def n1[symmetric] comp_tensor_op cnorm_eq_1[THEN iffD1])
  also have \<open>\<dots> = (butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L assoc_ell2 o\<^sub>C\<^sub>L (b12\<^sub>n \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n')
                  o\<^sub>C\<^sub>L assoc_ell2' o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun)\<close>
    by (auto simp: d_def eq n2 cblinfun_assoc_left)
  also have \<open>\<dots> = (butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L assoc_ell2 o\<^sub>C\<^sub>L 
               ((id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n) o\<^sub>C\<^sub>L (b12\<^sub>n \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n') o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n' \<phi>\<^sub>n'))
               o\<^sub>C\<^sub>L assoc_ell2' o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun)\<close>
    by (auto simp: comp_tensor_op cnorm_eq_1[THEN iffD1])
  also have \<open>\<dots> = (butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L assoc_ell2 o\<^sub>C\<^sub>L 
               ((id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n) o\<^sub>C\<^sub>L (assoc_ell2' o\<^sub>C\<^sub>L d o\<^sub>C\<^sub>L assoc_ell2) o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n' \<phi>\<^sub>n'))
               o\<^sub>C\<^sub>L assoc_ell2' o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun)\<close>
    by (auto simp: d_def n2 eq aux)
  also have \<open>\<dots> = ((butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L (assoc_ell2 o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n) o\<^sub>C\<^sub>L assoc_ell2'))
               o\<^sub>C\<^sub>L d o\<^sub>C\<^sub>L ((assoc_ell2 o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n' \<phi>\<^sub>n') o\<^sub>C\<^sub>L assoc_ell2') o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun))\<close>
    by (auto simp: sandwich_def cblinfun_assoc_left)
  also have \<open>\<dots> = (butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n)
               o\<^sub>C\<^sub>L d o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n' \<phi>\<^sub>n')\<close>
    apply (simp only: tensor_id[symmetric] comp_tensor_op aux2)
    by (simp add: cnorm_eq_1[THEN iffD1])
  also have \<open>\<dots> = (vector_to_cblinfun \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o vector_to_cblinfun \<phi>\<^sub>n)
               o\<^sub>C\<^sub>L c' o\<^sub>C\<^sub>L (vector_to_cblinfun \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o vector_to_cblinfun \<phi>\<^sub>n')*\<close>
    apply (simp add: c'_def butterfly_def_one_dim[where 'c="unit ell2"] cblinfun_assoc_left comp_tensor_op
                      tensor_op_adjoint cnorm_eq_1[THEN iffD1])
    by (simp add: cblinfun_assoc_right comp_tensor_op)
  also have \<open>\<dots> = butterfly \<psi>\<^sub>n \<psi>\<^sub>n' \<otimes>\<^sub>o c'' \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n'\<close>
    by (simp add: c'_c'' comp_tensor_op tensor_op_adjoint butterfly_def_one_dim[symmetric])
  also have \<open>\<dots> = butterfly \<psi> \<psi>' \<otimes>\<^sub>o c \<otimes>\<^sub>o butterfly \<phi> \<phi>'\<close>
    by (simp add: \<psi>\<^sub>n_def \<psi>\<^sub>n'_def \<phi>\<^sub>n_def \<phi>\<^sub>n'_def c_def tensor_op_scaleC_left tensor_op_scaleC_right)
  finally have d_c: \<open>d = butterfly \<psi> \<psi>' \<otimes>\<^sub>o c \<otimes>\<^sub>o butterfly \<phi> \<phi>'\<close>
    by -
  then show ?thesis
    by (auto simp: d_def)
qed

lemma norm_tensor_ell2: \<open>norm (a \<otimes>\<^sub>s b) = norm a * norm b\<close>
  apply transfer
  by (simp add: ell2_norm_finite sum_product sum.cartesian_product case_prod_beta
      norm_mult power_mult_distrib flip: real_sqrt_mult)

lemma bounded_cbilinear_tensor_ell2[bounded_cbilinear]: \<open>bounded_cbilinear (\<otimes>\<^sub>s)\<close>
proof standard
  fix a a' :: "'a ell2" and b b' :: "'b ell2" and r :: complex
  show \<open>tensor_ell2 (a + a') b = tensor_ell2 a b + tensor_ell2 a' b\<close>
    by (meson tensor_ell2_add1)
  show \<open>tensor_ell2 a (b + b') = tensor_ell2 a b + tensor_ell2 a b'\<close>
    by (simp add: tensor_ell2_add2)  
  show \<open>tensor_ell2 (r *\<^sub>C a) b = r *\<^sub>C tensor_ell2 a b\<close>
    by (simp add: tensor_ell2_scaleC1)
  show \<open>tensor_ell2 a (r *\<^sub>C b) = r *\<^sub>C tensor_ell2 a b\<close>
    by (simp add: tensor_ell2_scaleC2)
  show \<open>\<exists>K. \<forall>a b. norm (tensor_ell2 a b) \<le> norm a * norm b * K \<close>
    apply (rule exI[of _ 1])
    by (simp add: norm_tensor_ell2)
qed


end
