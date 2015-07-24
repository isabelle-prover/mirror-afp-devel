(*  
    Title:      Echelon_Form_Inverse_IArrays.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section{*Inverse matrices over principal ideal rings using immutable arrays*}

theory Echelon_Form_Inverse_IArrays
  imports 
    Echelon_Form_Inverse
    Code_Cayley_Hamilton_IArrays
    "../Gauss_Jordan/Inverse_IArrays"
begin

subsection{*Computing the inverse of matrices over rings using immutable arrays*}

definition "inverse_matrix_ring_iarray A = (let d=det_iarrays_rings A in 
  if is_unit d then Some(ring_inv d *ssi adjugate_iarrays A) else None)"

lemma matrix_to_iarray_inverse: 
  fixes A::"'a::{euclidean_ring}^'n::{mod_type}^'n::{mod_type}"
  shows"matrix_to_iarray_option (inverse_matrix A) = inverse_matrix_ring_iarray (matrix_to_iarray A)"
  unfolding inverse_matrix_ring_iarray_def inverse_matrix_code_rings matrix_to_iarray_option_def
  unfolding matrix_to_iarray_det_euclidean_ring 
  by (metis (mono_tags) inverse_matrix_code_rings matrix_to_iarray_adjugate 
      matrix_to_iarray_det_euclidean_ring matrix_to_iarray_scalar_matrix_mult 
      option.distinct(1) option.sel)

end
