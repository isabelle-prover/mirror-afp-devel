(*  
    Title:      Echelon_Form_Inverse.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section{*Inverse matrix over principal ideal rings*}

theory Echelon_Form_Inverse
  imports 
    Echelon_Form_Det
    "../Gauss_Jordan/Inverse"
begin

subsection{*Computing the inverse of matrix over rings*}

lemma scalar_mult_mat: 
  fixes x :: "'a::comm_semiring_0"
  shows "x *k mat y = mat (x * y)"
  by (simp add: matrix_scalar_mult_def mat_def vec_eq_iff)

lemma matrix_mul_mat:
  fixes A :: "'a::comm_semiring_1 ^ 'm ^ 'n"
  shows "A ** mat x = x *k A"
  by (simp add: matrix_matrix_mult_def mat_def if_distrib setsum.If_cases matrix_scalar_mult_def vec_eq_iff ac_simps)

lemma mult_adjugate_det: "A ** adjugate A = mat (det A)"
  using mult_adjugate_det[of "from_vec A"]
  unfolding det_sq_matrix_eq adjugate_eq to_vec_eq_iff[symmetric] to_vec_matrix_matrix_mult to_vec_from_vec 
  by (simp add: to_vec_diag)


lemma invertible_imp_matrix_inv:
  assumes i: "invertible A"
  shows "matrix_inv A = ring_inv (det A) *k adjugate A"
proof -
  let ?A = "adjugate A"
  have "A ** ?A = det A *k mat 1" 
    unfolding mult_adjugate_det by (simp add: scalar_mult_mat)
  hence "matrix_inv A ** (A ** ?A) = matrix_inv A ** (det A *k mat 1)"
    by auto
  hence "?A = det A *k matrix_inv A"
    unfolding matrix_mul_assoc matrix_inv_left[OF i] matrix_mul_lid scalar_mult_mat matrix_mul_mat
    by simp
  thus "matrix_inv A = ring_inv (det A) *k ?A"
    by (metis (no_types, lifting) i invertible_iff_is_unit matrix_mul_assoc matrix_mul_mat
        matrix_mul_rid ring_inv_is_inv2 scalar_mult_mat) 
qed    

lemma inverse_matrix_code_rings[code_unfold]: 
  fixes A::"'a::{euclidean_ring}^'n::{mod_type}^'n::{mod_type}"
  shows "inverse_matrix A = (let d=det A in if is_unit d then Some (ring_inv d *k adjugate A) else None)"
  using invertible_imp_matrix_inv
  unfolding inverse_matrix_def invertible_iff_is_unit by auto

end
