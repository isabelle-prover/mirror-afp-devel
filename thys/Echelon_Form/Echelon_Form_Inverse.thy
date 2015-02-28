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

lemma invertible_imp_matrix_inv:
  assumes i: "invertible A"
  shows "matrix_inv A = ring_inv (det A) *ss adjugate A"
proof -
  have "A ** adjugate A = det A *ss mat 1" using adjugate_det_symmetric .
  hence "matrix_inv A ** (A ** adjugate A) = matrix_inv A ** (det A *ss mat 1)"
    by auto
  hence "adjugate A = det A *ss matrix_inv A"    
    by (metis i matrix_inv_left matrix_mul_assoc matrix_scalar_mat_one 
       one_scalar_mult_mat scalar_mat_matrix_mult_left)
  thus "matrix_inv A = ring_inv (det A) *ss adjugate A" 
    by (metis (erased, hide_lams) transpose_transpose i invertible_iff_is_unit matrix_mul_rid 
        matrix_scalar_assoc matrix_transpose_mul ring_inv_is_inv1 scalar_mat_matrix_mult_left 
        scalar_scalar_mult_assoc)
qed    

lemma inverse_matrix_code_rings[code_unfold]: 
  fixes A::"'a::{euclidean_ring}^'n::{mod_type}^'n::{mod_type}"
  shows "inverse_matrix A = (let d=det A in if is_unit d 
    then Some (ring_inv d *ss adjugate A) else None)"
  using invertible_imp_matrix_inv
  unfolding inverse_matrix_def invertible_iff_is_unit by auto

end
