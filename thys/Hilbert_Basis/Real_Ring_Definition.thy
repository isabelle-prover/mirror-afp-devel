section \<open>The Real Ring definition\<close>

theory Real_Ring_Definition

imports 
  "HOL-Algebra.Module" 
  "HOL-Algebra.RingHom" 
  HOL.Real 
  "HOL-Computational_Algebra.Formal_Power_Series"
begin


text \<open>Defining real ring for examples on Noetherian Rings.\<close>
definition                       
  REAL :: "real ring"
  where "REAL = \<lparr>carrier = UNIV, monoid.mult = (*), one = 1, zero = 0, add = (+)\<rparr>"

lemma REAL_ring:\<open>ring REAL\<close>
  apply(rule ringI)
     apply(rule abelian_groupI)
  by (auto simp:REAL_def monoidI ab_group_add_class.ab_left_minus distrib_right distrib_left
      intro: exI[of _ "- x" for x])

lemma REAL_cring:\<open>cring REAL\<close>
  unfolding cring_def apply(safe) 
   apply (simp add: REAL_ring)
  apply(rule comm_monoidI)
  by(auto simp:REAL_def)

lemma REAL_field: \<open>field REAL\<close>
  unfolding field_def domain_def field_axioms_def
  apply(safe)
      apply(simp add:REAL_cring)
  unfolding domain_axioms_def 
  by(auto simp:REAL_def Units_def mult.commute nonzero_divide_eq_eq)
    (metis mult.commute nonzero_divide_eq_eq)

end