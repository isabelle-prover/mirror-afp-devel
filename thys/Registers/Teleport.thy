section \<open>Quantum teleportation\<close>

theory Teleport
  imports 
    QHoare
    Real_Impl.Real_Impl
    "HOL-Library.Code_Target_Numeral"
    Finite_Tensor_Product_Matrices
    "HOL-Library.Word"
begin

hide_const (open) Finite_Cartesian_Product.vec
hide_type (open) Finite_Cartesian_Product.vec
hide_const (open) Finite_Cartesian_Product.mat
hide_const (open) Finite_Cartesian_Product.row
hide_const (open) Finite_Cartesian_Product.column
no_notation Group.mult (infixl "\<otimes>\<index>" 70)
no_notation Order.top ("\<top>\<index>")
unbundle no_vec_syntax
unbundle no_inner_syntax


locale teleport_locale = qhoare "TYPE('mem::finite)" +
  fixes X :: "bit update \<Rightarrow> 'mem::finite update"
    and \<Phi> :: "(bit*bit) update \<Rightarrow> 'mem update"
    and A :: "'atype::finite update \<Rightarrow> 'mem update"
    and B :: "'btype::finite update \<Rightarrow> 'mem update"
  assumes compat[register]: "mutually compatible (X,\<Phi>,A,B)"
begin

abbreviation "\<Phi>1 \<equiv> \<Phi> \<circ> Fst"
abbreviation "\<Phi>2 \<equiv> \<Phi> \<circ> Snd"
abbreviation "X\<Phi>2 \<equiv> (X;\<Phi>2)"
abbreviation "X\<Phi>1 \<equiv> (X;\<Phi>1)"
abbreviation "X\<Phi> \<equiv> (X;\<Phi>)"
abbreviation "XAB \<equiv> ((X;A); B)"
abbreviation "AB \<equiv> (A;B)"
abbreviation "\<Phi>2AB \<equiv> ((\<Phi> o Snd; A); B)"

definition "teleport a b = [
    apply CNOT X\<Phi>1,
    apply hadamard X,
    ifthen \<Phi>1 a,
    ifthen X b, 
    apply (if a=1 then pauliX else id_cblinfun) \<Phi>2,
    apply (if b=1 then pauliZ else id_cblinfun) \<Phi>2
  ]"


lemma \<Phi>_X\<Phi>: \<open>\<Phi> a = X\<Phi> (id_cblinfun \<otimes>\<^sub>o a)\<close>
  by (auto simp: register_pair_apply)
lemma X\<Phi>1_X\<Phi>: \<open>X\<Phi>1 a = X\<Phi> (assoc (a \<otimes>\<^sub>o id_cblinfun))\<close>
  apply (subst pair_o_assoc[unfolded o_def, of X \<Phi>1 \<Phi>2, simplified, THEN fun_cong])
  by (auto simp: register_pair_apply)
lemma X\<Phi>2_X\<Phi>: \<open>X\<Phi>2 a = X\<Phi> ((id \<otimes>\<^sub>r swap) (assoc (a \<otimes>\<^sub>o id_cblinfun)))\<close>
  apply (subst pair_o_tensor[unfolded o_def, THEN fun_cong], simp, simp, simp)
  apply (subst (2) register_Fst_register_Snd[symmetric, of \<Phi>], simp)
  using [[simproc del: compatibility_warn]]
  apply (subst pair_o_swap[unfolded o_def], simp)
  apply (subst pair_o_assoc[unfolded o_def, THEN fun_cong], simp, simp, simp)
  by (auto simp: register_pair_apply)
lemma \<Phi>2_X\<Phi>: \<open>\<Phi>2 a = X\<Phi> (id_cblinfun \<otimes>\<^sub>o (id_cblinfun \<otimes>\<^sub>o a))\<close>
  by (auto simp: Snd_def register_pair_apply)
lemma X_X\<Phi>: \<open>X a = X\<Phi> (a \<otimes>\<^sub>o id_cblinfun)\<close>
  by (auto simp: register_pair_apply)
lemma \<Phi>1_X\<Phi>: \<open>\<Phi>1 a = X\<Phi> (id_cblinfun \<otimes>\<^sub>o (a \<otimes>\<^sub>o id_cblinfun))\<close>
  by (auto simp: Fst_def register_pair_apply)
lemmas to_X\<Phi> = \<Phi>_X\<Phi> X\<Phi>1_X\<Phi> X\<Phi>2_X\<Phi> \<Phi>2_X\<Phi> X_X\<Phi> \<Phi>1_X\<Phi>

lemma X_X\<Phi>1: \<open>X a = X\<Phi>1 (a \<otimes>\<^sub>o id_cblinfun)\<close>
  by (auto simp: register_pair_apply)
lemmas to_X\<Phi>1 = X_X\<Phi>1

lemma XAB_to_X\<Phi>2_AB: \<open>XAB a = (X\<Phi>2;AB) ((swap \<otimes>\<^sub>r id) (assoc' (id_cblinfun \<otimes>\<^sub>o assoc a)))\<close>
  by (simp add: pair_o_tensor[unfolded o_def, THEN fun_cong] register_pair_apply
      pair_o_swap[unfolded o_def, THEN fun_cong]
      pair_o_assoc'[unfolded o_def, THEN fun_cong]
      pair_o_assoc[unfolded o_def, THEN fun_cong])

lemma X\<Phi>2_to_X\<Phi>2_AB: \<open>X\<Phi>2 a = (X\<Phi>2;AB) (a \<otimes>\<^sub>o id_cblinfun)\<close>
  by (simp add: register_pair_apply)

schematic_goal \<Phi>2AB_to_X\<Phi>2_AB: "\<Phi>2AB a = (X\<Phi>2;AB) ?b"
  apply (subst pair_o_assoc'[unfolded o_def, THEN fun_cong])
     apply simp_all[3]
  apply (subst register_pair_apply[where a=id_cblinfun])
   apply simp_all[2]
  apply (subst pair_o_assoc[unfolded o_def, THEN fun_cong])
     apply simp_all[3]
  by simp

lemmas to_X\<Phi>2_AB = XAB_to_X\<Phi>2_AB X\<Phi>2_to_X\<Phi>2_AB \<Phi>2AB_to_X\<Phi>2_AB

lemma teleport:
  assumes [simp]: "norm \<psi> = 1"
  shows "hoare (XAB =\<^sub>q \<psi> \<sqinter> \<Phi> =\<^sub>q \<beta>00) (teleport a b) (\<Phi>2AB =\<^sub>q \<psi>)"
proof -
  define XZ :: \<open>bit update\<close> where "XZ = (if a=1 then (if b=1 then pauliZ o\<^sub>C\<^sub>L pauliX else pauliX) else (if b=1 then pauliZ else id_cblinfun))"

  define pre where "pre = XAB =\<^sub>q \<psi>"

  define O1 where "O1 = \<Phi> (selfbutter \<beta>00)"
  have \<open>(XAB =\<^sub>q \<psi> \<sqinter> \<Phi> =\<^sub>q \<beta>00) = O1 *\<^sub>S pre\<close>
    unfolding pre_def O1_def EQ_def
    apply (subst compatible_proj_intersect[where R=XAB and S=\<Phi>])
       apply (simp_all add: butterfly_is_Proj)
    apply (subst swap_registers[where R=XAB and S=\<Phi>])
    by (simp_all add: cblinfun_assoc_left(2))

  also
  define O2 where "O2 = X\<Phi>1 CNOT o\<^sub>C\<^sub>L O1"
  have \<open>hoare (O1 *\<^sub>S pre) [apply CNOT X\<Phi>1] (O2 *\<^sub>S pre)\<close>
    apply (rule hoare_apply) by (simp add: O2_def cblinfun_assoc_left(2))

  also
  define O3 where \<open>O3 = X hadamard o\<^sub>C\<^sub>L O2\<close>
  have \<open>hoare (O2 *\<^sub>S pre) [apply hadamard X] (O3 *\<^sub>S pre)\<close>
    apply (rule hoare_apply) by (simp add: O3_def cblinfun_assoc_left(2))

  also
  define O4 where \<open>O4 = \<Phi>1 (selfbutterket a) o\<^sub>C\<^sub>L O3\<close>
  have \<open>hoare (O3 *\<^sub>S pre) [ifthen \<Phi>1 a] (O4 *\<^sub>S pre)\<close>
    apply (rule hoare_ifthen) by (simp add: O4_def cblinfun_assoc_left(2))

  also
  define O5 where \<open>O5 = X (selfbutterket b) o\<^sub>C\<^sub>L O4\<close>
  have \<open>hoare (O4 *\<^sub>S pre) [ifthen X b] (O5 *\<^sub>S pre)\<close>
    apply (rule hoare_ifthen) by (simp add: O5_def cblinfun_assoc_left(2))

  also
  define O6 where \<open>O6 = \<Phi>2 (if a=1 then pauliX else id_cblinfun) o\<^sub>C\<^sub>L O5\<close>
  have \<open>hoare (O5 *\<^sub>S pre) [apply (if a=1 then pauliX else id_cblinfun) (\<Phi> \<circ> Snd)] (O6 *\<^sub>S pre)\<close>
    apply (rule hoare_apply) by (auto simp add: O6_def cblinfun_assoc_left(2))

  also
  define O7 where \<open>O7 = \<Phi>2 (if b = 1 then pauliZ else id_cblinfun) o\<^sub>C\<^sub>L O6\<close>
  have O7: \<open>O7 = \<Phi>2 XZ o\<^sub>C\<^sub>L O5\<close>
    by (auto simp add: O6_def O7_def XZ_def register_mult lift_cblinfun_comp[OF register_mult])
  have \<open>hoare (O6 *\<^sub>S pre) [apply (if b=1 then pauliZ else id_cblinfun) (\<Phi> \<circ> Snd)] (O7 *\<^sub>S pre)\<close>
    apply (rule hoare_apply) 
    by (auto simp add: O7_def cblinfun_assoc_left(2))

  finally have hoare: \<open>hoare (XAB =\<^sub>q \<psi> \<sqinter> \<Phi> =\<^sub>q \<beta>00) (teleport a b) (O7 *\<^sub>S pre)\<close>
    by (auto simp add: teleport_def comp_def)

  have O5': "O5 = (1/2) *\<^sub>C \<Phi>2 (XZ*) o\<^sub>C\<^sub>L X\<Phi>2 Uswap o\<^sub>C\<^sub>L \<Phi> (butterfly (ket a \<otimes>\<^sub>s ket b) \<beta>00)"
    unfolding O7 O5_def O4_def O3_def O2_def O1_def 
    apply (simp split del: if_split only: to_X\<Phi> register_mult[of X\<Phi>])
    apply (simp split del: if_split add: register_mult[of X\<Phi>] 
                flip: complex_vector.linear_scale
                del: comp_apply)
    apply (rule arg_cong[of _ _ X\<Phi>])
    apply (rule cblinfun_eq_mat_of_cblinfunI)
    apply (simp add: assoc_ell2_sandwich mat_of_cblinfun_tensor_op XZ_def
                     butterfly_def mat_of_cblinfun_compose mat_of_cblinfun_vector_to_cblinfun
                     mat_of_cblinfun_adj vec_of_basis_enum_ket mat_of_cblinfun_id
                     swap_sandwich[abs_def] mat_of_cblinfun_scaleR mat_of_cblinfun_scaleC
                     id_tensor_sandwich vec_of_basis_enum_tensor_state mat_of_cblinfun_cblinfun_apply
                     mat_of_cblinfun_sandwich)
    by normalization

  have [simp]: "unitary XZ"
    unfolding unitary_def unfolding XZ_def apply auto
     apply (metis cblinfun_assoc_left(1) pauliXX pauliZZ cblinfun_compose_id_left)
    by (metis cblinfun_assoc_left(1) pauliXX pauliZZ cblinfun_compose_id_left)

  have O7': "O7 = (1/2) *\<^sub>C X\<Phi>2 Uswap o\<^sub>C\<^sub>L \<Phi> (butterfly (ket a \<otimes>\<^sub>s ket b) \<beta>00)"
    unfolding O7 O5'
    by (simp add: cblinfun_compose_assoc[symmetric] register_mult[of \<Phi>2] del: comp_apply)

  have "O7 *\<^sub>S pre = X\<Phi>2 Uswap *\<^sub>S XAB (selfbutter \<psi>) *\<^sub>S \<Phi> (butterfly (ket (a, b)) \<beta>00) *\<^sub>S \<top>"
    apply (simp add: O7' pre_def EQ_def cblinfun_compose_image)
    apply (subst lift_cblinfun_comp[OF swap_registers[where R=\<Phi> and S=XAB]], simp)
    by (simp add: cblinfun_assoc_left(2))
  also have \<open>\<dots> \<le> X\<Phi>2 Uswap *\<^sub>S XAB (selfbutter \<psi>) *\<^sub>S \<top>\<close>
    by (simp add: cblinfun_image_mono)
  also have \<open>\<dots> = (X\<Phi>2;AB) (Uswap \<otimes>\<^sub>o id_cblinfun) *\<^sub>S (X\<Phi>2;AB)
                      ((swap \<otimes>\<^sub>r id) (assoc' (id_cblinfun \<otimes>\<^sub>o assoc (selfbutter \<psi>)))) *\<^sub>S \<top>\<close>
    by (simp add: to_X\<Phi>2_AB)
  also have \<open>\<dots> = \<Phi>2AB (selfbutter \<psi>) *\<^sub>S X\<Phi>2 Uswap *\<^sub>S \<top>\<close>
    apply (simp add: swap_sandwich sandwich_grow_left to_X\<Phi>2_AB   
        cblinfun_compose_image[symmetric] register_mult)
    by (simp add: sandwich_def cblinfun_compose_assoc[symmetric] comp_tensor_op tensor_op_adjoint)
  also have \<open>\<dots> \<le> \<Phi>2AB =\<^sub>q \<psi>\<close>
    by (simp add: EQ_def cblinfun_image_mono)
  finally have \<open>O7 *\<^sub>S pre \<le> \<Phi>2AB =\<^sub>q \<psi>\<close>
    by simp

  with hoare
  show ?thesis
    by (meson basic_trans_rules(31) hoare_def less_eq_ccsubspace.rep_eq)
qed

end


locale concrete_teleport_vars begin

type_synonym a_state = "64 word"
type_synonym b_state = "1000000 word"
type_synonym mem = "a_state * bit * bit * b_state * bit"
type_synonym 'a var = \<open>'a update \<Rightarrow> mem update\<close>

definition A :: "a_state var" where \<open>A a = a \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o id_cblinfun\<close>
definition X :: \<open>bit var\<close> where \<open>X a = id_cblinfun \<otimes>\<^sub>o a \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o id_cblinfun\<close>
definition \<Phi>1 :: \<open>bit var\<close> where \<open>\<Phi>1 a = id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o a \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o id_cblinfun\<close>
definition B :: \<open>b_state var\<close> where \<open>B a = id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o a \<otimes>\<^sub>o id_cblinfun\<close>
definition \<Phi>2 :: \<open>bit var\<close> where \<open>\<Phi>2 a = id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o a\<close>

end


interpretation teleport_concrete:
  concrete_teleport_vars +
  teleport_locale concrete_teleport_vars.X
                  \<open>(concrete_teleport_vars.\<Phi>1; concrete_teleport_vars.\<Phi>2)\<close>
                  concrete_teleport_vars.A
                  concrete_teleport_vars.B
  apply standard
  using [[simproc del: compatibility_warn]]
  by (auto simp: concrete_teleport_vars.X_def[abs_def]
                 concrete_teleport_vars.\<Phi>1_def[abs_def]
                 concrete_teleport_vars.\<Phi>2_def[abs_def]
                 concrete_teleport_vars.A_def[abs_def]
                 concrete_teleport_vars.B_def[abs_def]
           intro!: compatible3' compatible3)

thm teleport
thm teleport_def

end
