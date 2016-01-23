(* Title:      General Hoare Logic for Demonic Refinement Algebra
   Author:     Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section {* Propositional Hoare Logic for Demonic Refinement Algebra *}

text {* In this section the generic iteration operator is instantiated to the strong iteration operator of 
demonic refinement algebra that models possibly infinite iteration. *}

theory PHL_DRA
  imports DRA PHL_KA
begin

sublocale dra < total_phl: it_pre_dioid where it = strong_iteration 
  by standard (simp add: local.iteration_sim)
  
end
