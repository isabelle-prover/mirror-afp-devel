section \<open>Quantum mechanics basics\<close>

theory Quantum
  imports
    Finite_Tensor_Product
    "HOL-Library.Z2"
    Jordan_Normal_Form.Matrix_Impl 
    Real_Impl.Real_Impl
    "HOL-Library.Code_Target_Numeral"
begin

type_synonym ('a,'b) matrix = \<open>('a ell2, 'b ell2) cblinfun\<close>

subsection \<open>Basic quantum states\<close>

subsubsection \<open>EPR pair\<close>

definition "vector_\<beta>00 = vec_of_list [ 1/sqrt 2::complex, 0, 0, 1/sqrt 2 ]"
definition \<beta>00 :: \<open>(bit\<times>bit) ell2\<close> where [code del]: "\<beta>00 = basis_enum_of_vec vector_\<beta>00"
lemma vec_of_basis_enum_\<beta>00[simp]: "vec_of_basis_enum \<beta>00 = vector_\<beta>00"
  by (auto simp add: \<beta>00_def vector_\<beta>00_def)
lemma vec_of_ell2_\<beta>00[simp, code]: "vec_of_ell2 \<beta>00 = vector_\<beta>00"
  by (simp add: vec_of_ell2_def)

lemma norm_\<beta>00[simp]: "norm \<beta>00 = 1"
  by eval

subsubsection \<open>Ket plus\<close>

definition "vector_ketplus = vec_of_list [ 1/sqrt 2::complex, 1/sqrt 2 ]"
definition ketplus :: \<open>bit ell2\<close> ("|+\<rangle>") where [code del]: \<open>ketplus = basis_enum_of_vec vector_ketplus\<close>
lemma vec_of_basis_enum_ketplus[simp]: "vec_of_basis_enum ketplus = vector_ketplus"
  by (auto simp add: ketplus_def vector_ketplus_def)
lemma vec_of_ell2_ketplus[simp, code]: "vec_of_ell2 ketplus = vector_ketplus"
  by (simp add: vec_of_ell2_def)

subsection \<open>Basic quantum gates\<close>

subsubsection \<open>Pauli X\<close>

definition "matrix_pauliX = mat_of_rows_list 2 [ [0::complex, 1], [1, 0] ]"
definition pauliX :: \<open>(bit, bit) matrix\<close> where [code del]: "pauliX = cblinfun_of_mat matrix_pauliX"
lemma [simp, code]: "mat_of_cblinfun pauliX = matrix_pauliX"
  apply (auto simp add: pauliX_def matrix_pauliX_def)
  apply (subst cblinfun_of_mat_inverse)
  by (auto)

lemma pauliX_adjoint[simp]: "pauliX* = pauliX"
  by eval
lemma pauliXX[simp]: "pauliX o\<^sub>C\<^sub>L pauliX = id_cblinfun"
  by eval

subsubsection \<open>Pauli Z\<close>

definition "matrix_pauliZ = mat_of_rows_list 2 [ [1::complex, 0], [0, -1] ]"
definition pauliZ :: \<open>(bit, bit) matrix\<close> where [code del]: "pauliZ = cblinfun_of_mat matrix_pauliZ"
lemma [simp, code]: "mat_of_cblinfun pauliZ = matrix_pauliZ"
  apply (auto simp add: pauliZ_def matrix_pauliZ_def)
  apply (subst cblinfun_of_mat_inverse)
  by (auto)
lemma pauliZ_adjoint[simp]: "pauliZ* = pauliZ"
  by eval
lemma pauliZZ[simp]: "pauliZ o\<^sub>C\<^sub>L pauliZ = id_cblinfun"
  by eval


subsubsection Hadamard

definition "matrix_hadamard = mat_of_rows_list 2 [ [1/sqrt 2::complex, 1/sqrt 2], [1/sqrt 2, -1/sqrt 2] ]"
definition hadamard :: \<open>(bit,bit) matrix\<close> where [code del]: "hadamard = cblinfun_of_mat matrix_hadamard"

lemma [simp, code]: "mat_of_cblinfun hadamard = matrix_hadamard"
  apply (auto simp add: hadamard_def matrix_hadamard_def)
  apply (subst cblinfun_of_mat_inverse)
  by (auto)

lemma hada_adj[simp]: "hadamard* = hadamard"
  by eval


subsubsection CNOT

definition "matrix_CNOT = mat_of_rows_list 4 [ [1::complex,0,0,0], [0,1,0,0], [0,0,0,1], [0,0,1,0] ]"
definition CNOT :: \<open>(bit*bit, bit*bit) matrix\<close> where [code del]: "CNOT = cblinfun_of_mat matrix_CNOT"

lemma [simp, code]: "mat_of_cblinfun CNOT = matrix_CNOT"
  apply (auto simp add: CNOT_def matrix_CNOT_def)
  apply (subst cblinfun_of_mat_inverse)
  by (auto)

lemma [simp]: "CNOT* = CNOT"
  by eval

lemma cnot_apply[simp]: \<open>CNOT *\<^sub>V ket (i,j) = ket (i,j+i)\<close>
  apply (rule spec[where x=i], rule spec[where x=j])
  by eval

subsubsection \<open>Qubit swap\<close>


definition "matrix_Uswap = mat_of_rows_list 4 [ [1::complex, 0, 0, 0], [0,0,1,0], [0,1,0,0], [0,0,0,1] ]"
definition Uswap :: \<open>(bit\<times>bit, bit\<times>bit) matrix\<close> where
  [code del]: \<open>Uswap = cblinfun_of_mat matrix_Uswap\<close>

lemma mat_of_cblinfun_Uswap[simp, code]: "mat_of_cblinfun Uswap = matrix_Uswap"
  apply (auto simp add: Uswap_def matrix_Uswap_def)
  apply (subst cblinfun_of_mat_inverse)
  by (auto)

lemma dim_col_Uswap[simp]: "dim_col matrix_Uswap = 4"
  unfolding matrix_Uswap_def by simp
lemma dim_row_Uswap[simp]: "dim_row matrix_Uswap = 4"
  unfolding matrix_Uswap_def by simp
lemma Uswap_adjoint[simp]: "Uswap* = Uswap"
  by eval
lemma Uswap_involution[simp]: "Uswap o\<^sub>C\<^sub>L Uswap = id_cblinfun"
  by eval
lemma unitary_Uswap[simp]: "unitary Uswap"
  unfolding unitary_def by simp

lemma Uswap_apply[simp]: \<open>Uswap *\<^sub>V s \<otimes>\<^sub>s t = t \<otimes>\<^sub>s s\<close>
  apply (rule clinear_equal_ket[where f=\<open>\<lambda>s. Uswap *\<^sub>V s \<otimes>\<^sub>s t\<close>, THEN fun_cong])
    apply (simp add: cblinfun.add_right clinearI tensor_ell2_add1 tensor_ell2_scaleC1)
   apply (simp add: clinear_tensor_ell21)
  apply (rule clinear_equal_ket[where f=\<open>\<lambda>t. Uswap *\<^sub>V _ \<otimes>\<^sub>s t\<close>, THEN fun_cong])
    apply (simp add: cblinfun.add_right clinearI tensor_ell2_add2 tensor_ell2_scaleC2)
   apply (simp add: clinear_tensor_ell22)
  apply (rule basis_enum_eq_vec_of_basis_enumI)
  apply (simp add: mat_of_cblinfun_cblinfun_apply vec_of_basis_enum_ket)
  by (case_tac i; case_tac ia; hypsubst_thin; normalization)

end
