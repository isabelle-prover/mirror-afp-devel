section \<open>Tensor products as matrices\<close>

theory Finite_Tensor_Product_Matrices
  imports Finite_Tensor_Product
begin

definition tensor_pack :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) \<Rightarrow> nat"
  where "tensor_pack X Y = (\<lambda>(x, y). x * Y + y)"

definition tensor_unpack :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat)"
  where "tensor_unpack X Y xy = (xy div Y, xy mod Y)"

lemma tensor_unpack_inj:
  assumes "i < A * B" and "j < A * B"
  shows "tensor_unpack A B i = tensor_unpack A B j \<longleftrightarrow> i = j"
  by (metis div_mult_mod_eq prod.sel(1) prod.sel(2) tensor_unpack_def)

lemma tensor_unpack_bound1[simp]: "i < A * B \<Longrightarrow> fst (tensor_unpack A B i) < A"
  unfolding tensor_unpack_def
  apply auto
  using less_mult_imp_div_less by blast
lemma tensor_unpack_bound2[simp]: "i < A * B \<Longrightarrow> snd (tensor_unpack A B i) < B"
  unfolding tensor_unpack_def
  apply auto
  by (metis mod_less_divisor mult.commute mult_zero_left nat_neq_iff not_less0)

lemma tensor_unpack_fstfst: \<open>fst (tensor_unpack A B (fst (tensor_unpack (A * B) C i)))
     = fst (tensor_unpack A (B * C) i)\<close>
  unfolding tensor_unpack_def apply auto
  by (metis div_mult2_eq mult.commute)
lemma tensor_unpack_sndsnd: \<open>snd (tensor_unpack B C (snd (tensor_unpack A (B * C) i)))
     = snd (tensor_unpack (A * B) C i)\<close>
  unfolding tensor_unpack_def apply auto
  by (meson dvd_triv_right mod_mod_cancel)
lemma tensor_unpack_fstsnd: \<open>fst (tensor_unpack B C (snd (tensor_unpack A (B * C) i)))
     = snd (tensor_unpack A B (fst (tensor_unpack (A * B) C i)))\<close>
  unfolding tensor_unpack_def apply auto
  by (metis (no_types, lifting) Euclidean_Division.div_eq_0_iff add_0_iff bits_mod_div_trivial div_mult_self4 mod_mult2_eq mod_mult_self1_is_0 mult.commute)


definition "tensor_state_jnf \<psi> \<phi> = (let d1 = dim_vec \<psi> in let d2 = dim_vec \<phi> in
  vec (d1*d2) (\<lambda>i. let (i1,i2) = tensor_unpack d1 d2 i in (vec_index \<psi> i1) * (vec_index \<phi> i2)))"

lemma tensor_state_jnf_dim[simp]: \<open>dim_vec (tensor_state_jnf \<psi> \<phi>) = dim_vec \<psi> * dim_vec \<phi>\<close>
  unfolding tensor_state_jnf_def Let_def by simp

lemma enum_prod_nth_tensor_unpack:
  assumes \<open>i < CARD('a) * CARD('b)\<close>
  shows "(Enum.enum ! i :: 'a::enum\<times>'b::enum) = 
        (let (i1,i2) = tensor_unpack CARD('a) CARD('b) i in 
              (Enum.enum ! i1, Enum.enum ! i2))"
  using assms 
  by (simp add: enum_prod_def card_UNIV_length_enum product_nth tensor_unpack_def)

lemma vec_of_basis_enum_tensor_state_index:
  fixes \<psi> :: \<open>'a::enum ell2\<close> and \<phi> :: \<open>'b::enum ell2\<close>
  assumes [simp]: \<open>i < CARD('a) * CARD('b)\<close>
  shows \<open>vec_of_basis_enum (\<psi> \<otimes>\<^sub>s \<phi>) $ i = (let (i1,i2) = tensor_unpack CARD('a) CARD('b) i in
    vec_of_basis_enum \<psi> $ i1 * vec_of_basis_enum \<phi> $ i2)\<close>
proof -
  define i1 i2 where "i1 = fst (tensor_unpack CARD('a) CARD('b) i)"
    and "i2 = snd (tensor_unpack CARD('a) CARD('b) i)"
  have [simp]: "i1 < CARD('a)" "i2 < CARD('b)"
    using assms i1_def tensor_unpack_bound1 apply presburger
    using assms i2_def tensor_unpack_bound2 by presburger

  have \<open>vec_of_basis_enum (\<psi> \<otimes>\<^sub>s \<phi>) $ i = Rep_ell2 (\<psi> \<otimes>\<^sub>s \<phi>) (enum_class.enum ! i)\<close>
    by (simp add: vec_of_basis_enum_ell2_component)
  also have \<open>\<dots> = Rep_ell2 \<psi> (Enum.enum!i1) * Rep_ell2 \<phi> (Enum.enum!i2)\<close>
    apply (transfer fixing: i i1 i2)
    by (simp add: enum_prod_nth_tensor_unpack case_prod_beta i1_def i2_def)
  also have \<open>\<dots> = vec_of_basis_enum \<psi> $ i1 * vec_of_basis_enum \<phi> $ i2\<close>
    by (simp add: vec_of_basis_enum_ell2_component)
  finally show ?thesis
    by (simp add: case_prod_beta i1_def i2_def)
qed

lemma vec_of_basis_enum_tensor_state:
  fixes \<psi> :: \<open>'a::enum ell2\<close> and \<phi> :: \<open>'b::enum ell2\<close>
  shows \<open>vec_of_basis_enum (\<psi> \<otimes>\<^sub>s \<phi>) = tensor_state_jnf (vec_of_basis_enum \<psi>) (vec_of_basis_enum \<phi>)\<close>
  apply (rule eq_vecI, simp_all)
  apply (subst vec_of_basis_enum_tensor_state_index, simp_all)
  by (simp add: tensor_state_jnf_def case_prod_beta Let_def)


lemma mat_of_cblinfun_tensor_op_index:
  fixes a :: \<open>'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::enum ell2\<close> and b :: \<open>'c::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::enum ell2\<close>
  assumes [simp]: \<open>i < CARD('b) * CARD('d)\<close>
  assumes [simp]: \<open>j < CARD('a) * CARD('c)\<close>
  shows \<open>mat_of_cblinfun (tensor_op a b) $$ (i,j) = 
            (let (i1,i2) = tensor_unpack CARD('b) CARD('d) i in
             let (j1,j2) = tensor_unpack CARD('a) CARD('c) j in
                  mat_of_cblinfun a $$ (i1,j1) * mat_of_cblinfun b $$ (i2,j2))\<close>
proof -
  define i1 i2 j1 j2
    where "i1 = fst (tensor_unpack CARD('b) CARD('d) i)"
      and "i2 = snd (tensor_unpack CARD('b) CARD('d) i)"
      and "j1 = fst (tensor_unpack CARD('a) CARD('c) j)"
      and "j2 = snd (tensor_unpack CARD('a) CARD('c) j)"
  have [simp]: "i1 < CARD('b)" "i2 < CARD('d)" "j1 < CARD('a)" "j2 < CARD('c)"
    using assms i1_def tensor_unpack_bound1 apply presburger
    using assms i2_def tensor_unpack_bound2 apply blast
    using assms(2) j1_def tensor_unpack_bound1 apply blast
    using assms(2) j2_def tensor_unpack_bound2 by presburger

  have \<open>mat_of_cblinfun (tensor_op a b) $$ (i,j) 
       = Rep_ell2 (tensor_op a b *\<^sub>V ket (Enum.enum!j)) (Enum.enum ! i)\<close>
    by (simp add: mat_of_cblinfun_ell2_component)
  also have \<open>\<dots> = Rep_ell2 ((a *\<^sub>V ket (Enum.enum!j1)) \<otimes>\<^sub>s (b *\<^sub>V ket (Enum.enum!j2))) (Enum.enum!i)\<close>
    by (simp add: tensor_op_ell2 enum_prod_nth_tensor_unpack[where i=j] Let_def case_prod_beta j1_def[symmetric] j2_def[symmetric] flip: tensor_ell2_ket)
  also have \<open>\<dots> = vec_of_basis_enum ((a *\<^sub>V ket (Enum.enum!j1)) \<otimes>\<^sub>s b *\<^sub>V ket (Enum.enum!j2)) $ i\<close>
    by (simp add: vec_of_basis_enum_ell2_component)
  also have \<open>\<dots> = vec_of_basis_enum (a *\<^sub>V ket (enum_class.enum ! j1)) $ i1 *
                  vec_of_basis_enum (b *\<^sub>V ket (enum_class.enum ! j2)) $ i2\<close>
    by (simp add: case_prod_beta vec_of_basis_enum_tensor_state_index i1_def[symmetric] i2_def[symmetric])
  also have \<open>\<dots> = Rep_ell2 (a *\<^sub>V ket (enum_class.enum ! j1)) (enum_class.enum ! i1) *
                  Rep_ell2 (b *\<^sub>V ket (enum_class.enum ! j2)) (enum_class.enum ! i2)\<close>
    by (simp add: vec_of_basis_enum_ell2_component)
  also have \<open>\<dots> = mat_of_cblinfun a $$ (i1, j1) * mat_of_cblinfun b $$ (i2, j2)\<close>
    by (simp add: mat_of_cblinfun_ell2_component)
  finally show ?thesis
    by (simp add: i1_def[symmetric] i2_def[symmetric] j1_def[symmetric] j2_def[symmetric] case_prod_beta)
qed


definition "tensor_op_jnf A B = 
  (let r1 = dim_row A in
   let c1 = dim_col A in
   let r2 = dim_row B in
   let c2 = dim_col B in
   mat (r1*r2) (c1*c2)
   (\<lambda>(i,j). let (i1,i2) = tensor_unpack r1 r2 i in
            let (j1,j2) = tensor_unpack c1 c2 j in
              (A $$ (i1,j1)) * (B $$ (i2,j2))))"

lemma tensor_op_jnf_dim[simp]: 
  \<open>dim_row (tensor_op_jnf a b) = dim_row a * dim_row b\<close>
  \<open>dim_col (tensor_op_jnf a b) = dim_col a * dim_col b\<close>
  unfolding tensor_op_jnf_def Let_def by simp_all


lemma mat_of_cblinfun_tensor_op:
  fixes a :: \<open>'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::enum ell2\<close> and b :: \<open>'c::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::enum ell2\<close>
  shows \<open>mat_of_cblinfun (tensor_op a b) = tensor_op_jnf (mat_of_cblinfun a) (mat_of_cblinfun b)\<close>
  apply (rule eq_matI, simp_all add: )
  apply (subst mat_of_cblinfun_tensor_op_index, simp_all)
  by (simp add: tensor_op_jnf_def case_prod_beta Let_def)


lemma mat_of_cblinfun_assoc_ell2'[simp]: 
  \<open>mat_of_cblinfun (assoc_ell2' :: (('a::enum\<times>('b::enum\<times>'c::enum)) ell2 \<Rightarrow>\<^sub>C\<^sub>L _)) = one_mat (CARD('a)*CARD('b)*CARD('c))\<close>
  (is "mat_of_cblinfun ?assoc = _")
proof  (rule mat_eq_iff[THEN iffD2], intro conjI allI impI)

  show \<open>dim_row (mat_of_cblinfun ?assoc) =
    dim_row (1\<^sub>m (CARD('a) * CARD('b) * CARD('c)))\<close>
    by (simp)
  show \<open>dim_col (mat_of_cblinfun ?assoc) =
    dim_col (1\<^sub>m (CARD('a) * CARD('b) * CARD('c)))\<close>
    by (simp)

  fix i j
  let ?i = "Enum.enum ! i :: (('a\<times>'b)\<times>'c)" and ?j = "Enum.enum ! j :: ('a\<times>('b\<times>'c))"

  assume \<open>i < dim_row (1\<^sub>m (CARD('a) * CARD('b) * CARD('c)))\<close>
  then have iB[simp]: \<open>i < CARD('a) * CARD('b) * CARD('c)\<close> by simp
  then have iB'[simp]: \<open>i < CARD('a) * (CARD('b) * CARD('c))\<close> by linarith
  assume \<open>j < dim_col (1\<^sub>m (CARD('a) * CARD('b) * CARD('c)))\<close>
  then have jB[simp]: \<open>j < CARD('a) * CARD('b) * CARD('c)\<close> by simp
  then have jB'[simp]: \<open>j < CARD('a) * (CARD('b) * CARD('c))\<close> by linarith

  define i1 i23 i2 i3
    where "i1 = fst (tensor_unpack CARD('a) (CARD('b)*CARD('c)) i)"
      and "i23 = snd (tensor_unpack CARD('a) (CARD('b)*CARD('c)) i)"
      and "i2 = fst (tensor_unpack CARD('b) CARD('c) i23)"
      and "i3 = snd (tensor_unpack CARD('b) CARD('c) i23)"
  define j12 j1 j2 j3
    where "j12 = fst (tensor_unpack (CARD('a)*CARD('b)) CARD('c) j)"
      and "j1 = fst (tensor_unpack CARD('a) CARD('b) j12)"
      and "j2 = snd (tensor_unpack CARD('a) CARD('b) j12)"
      and "j3 = snd (tensor_unpack (CARD('a)*CARD('b)) CARD('c) j)"

  have [simp]: "j12 < CARD('a)*CARD('b)" "i23 < CARD('b)*CARD('c)"
    using j12_def jB tensor_unpack_bound1 apply presburger
    using i23_def iB' tensor_unpack_bound2 by blast

  have j1': \<open>fst (tensor_unpack CARD('a) (CARD('b) * CARD('c)) j) = j1\<close>
    by (simp add: j1_def j12_def tensor_unpack_fstfst)

  let ?i1 = "Enum.enum ! i1 :: 'a" and ?i2 = "Enum.enum ! i2 :: 'b" and ?i3 = "Enum.enum ! i3 :: 'c"
  let ?j1 = "Enum.enum ! j1 :: 'a" and ?j2 = "Enum.enum ! j2 :: 'b" and ?j3 = "Enum.enum ! j3 :: 'c"

  have i: \<open>?i = ((?i1,?i2),?i3)\<close>
    by (auto simp add: enum_prod_nth_tensor_unpack case_prod_beta
          tensor_unpack_fstfst tensor_unpack_fstsnd tensor_unpack_sndsnd i1_def i2_def i23_def i3_def)
  have j: \<open>?j = (?j1,(?j2,?j3))\<close> 
    by (auto simp add: enum_prod_nth_tensor_unpack case_prod_beta
        tensor_unpack_fstfst tensor_unpack_fstsnd tensor_unpack_sndsnd j1_def j2_def j12_def j3_def)
  have ijeq: \<open>(?i1,?i2,?i3) = (?j1,?j2,?j3) \<longleftrightarrow> i = j\<close>
    unfolding i1_def i2_def i3_def j1_def j2_def j3_def apply simp
    apply (subst enum_inj, simp, simp)
    apply (subst enum_inj, simp, simp)
    apply (subst enum_inj, simp, simp)
    apply (subst tensor_unpack_inj[symmetric, where i=i and j=j and A="CARD('a)" and B="CARD('b)*CARD('c)"], simp, simp)
    unfolding prod_eq_iff
    apply (subst tensor_unpack_inj[symmetric, where i=\<open>snd (tensor_unpack CARD('a) (CARD('b) * CARD('c)) i)\<close> and A="CARD('b)" and B="CARD('c)"], simp, simp)
    by (simp add: i1_def[symmetric] j1_def[symmetric] i2_def[symmetric] j2_def[symmetric] i3_def[symmetric] j3_def[symmetric]
        i23_def[symmetric] j12_def[symmetric] j1'
        prod_eq_iff tensor_unpack_fstsnd tensor_unpack_sndsnd)

  have \<open>mat_of_cblinfun ?assoc $$ (i, j) = Rep_ell2 (assoc_ell2' *\<^sub>V ket ?j) ?i\<close>
    by (subst mat_of_cblinfun_ell2_component, auto)
  also have \<open>\<dots> = Rep_ell2 ((ket ?j1 \<otimes>\<^sub>s ket ?j2) \<otimes>\<^sub>s ket ?j3) ?i\<close>
    by (simp add: j assoc_ell2'_tensor flip: tensor_ell2_ket)
  also have \<open>\<dots> = (if (?i1,?i2,?i3) = (?j1,?j2,?j3) then 1 else 0)\<close>
    by (auto simp add: ket.rep_eq i)
  also have \<open>\<dots> = (if i=j then 1 else 0)\<close>
    using ijeq by simp
  finally
  show \<open>mat_of_cblinfun ?assoc $$ (i, j) =
           1\<^sub>m (CARD('a) * CARD('b) * CARD('c)) $$ (i, j)\<close>
    by auto
qed

lemma assoc_ell2'_inv: "assoc_ell2 o\<^sub>C\<^sub>L assoc_ell2' = id_cblinfun"
  apply (rule equal_ket, case_tac x, hypsubst)
  by (simp flip: tensor_ell2_ket add: cblinfun_apply_cblinfun_compose assoc_ell2'_tensor assoc_ell2_tensor)

lemma assoc_ell2_inv: "assoc_ell2' o\<^sub>C\<^sub>L assoc_ell2 = id_cblinfun"
  apply (rule equal_ket, case_tac x, hypsubst)
  by (simp flip: tensor_ell2_ket add: cblinfun_apply_cblinfun_compose assoc_ell2'_tensor assoc_ell2_tensor)

lemma mat_of_cblinfun_assoc_ell2[simp]: 
  \<open>mat_of_cblinfun (assoc_ell2 :: ((('a::enum\<times>'b::enum)\<times>'c::enum) ell2 \<Rightarrow>\<^sub>C\<^sub>L _)) = one_mat (CARD('a)*CARD('b)*CARD('c))\<close>
  (is "mat_of_cblinfun ?assoc = _")
proof -
  let ?assoc' = "assoc_ell2' :: (('a::enum\<times>('b::enum\<times>'c::enum)) ell2 \<Rightarrow>\<^sub>C\<^sub>L _)"
  have "one_mat (CARD('a)*CARD('b)*CARD('c)) = mat_of_cblinfun (?assoc o\<^sub>C\<^sub>L ?assoc')"
    by (simp add: mult.assoc mat_of_cblinfun_id)
  also have \<open>\<dots> = mat_of_cblinfun ?assoc * mat_of_cblinfun ?assoc'\<close>
    using mat_of_cblinfun_compose by blast
  also have \<open>\<dots> = mat_of_cblinfun ?assoc * one_mat (CARD('a)*CARD('b)*CARD('c))\<close>
    by simp
  also have \<open>\<dots> = mat_of_cblinfun ?assoc\<close>
    apply (rule right_mult_one_mat')
    by (simp)
  finally show ?thesis
    by simp
qed

end
