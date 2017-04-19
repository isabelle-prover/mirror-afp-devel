section \<open>Homomorphisms\<close>

text \<open>We register two homomorphism, namely lifting constants to polynomials,
  and lifting elements of some domain into their fraction field.\<close>
  
theory More_Homomorphisms
  imports "../Polynomial_Interpolation/Ring_Hom_Poly" 
begin

abbreviation (input) "coeff_lift == \<lambda>a. [: a :]"
  
interpretation coeff_lift_hom: inj_comm_semiring_hom coeff_lift
  by standard (simp_all add: ac_simps)
interpretation coeff_lift_hom: inj_comm_ring_hom coeff_lift..
interpretation coeff_lift_hom: inj_idom_hom coeff_lift..

text {* The following rule is incompatible with existing simp rules. *}
declare coeff_lift_hom.hom_mult[simp del]
declare coeff_lift_hom.hom_add[simp del]
declare coeff_lift_hom.hom_uminus[simp del]

interpretation to_fract_hom: inj_comm_ring_hom to_fract by (unfold_locales, auto)
interpretation to_fract_hom: idom_hom to_fract..
interpretation to_fract_hom: inj_idom_hom to_fract..

end