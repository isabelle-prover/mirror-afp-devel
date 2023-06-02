(*
   Mike Stannett
   Feb 2023
*)

section \<open> AxTriangleInequality \<close>

text \<open> This theory declares the Triangle Inequality as an axiom.\<close>


theory AxTriangleInequality
  imports Norms
begin

(* TRIANGLE INEQUALITY *)
(* axTriangleInequality is defined in Norms *)

text \<open> Although AxTriangleInequality can be proven rather than asserted we have
left it as an axiom to illustrate the flexibility of using Isabelle for mathematical 
physics: well-known mathematical results can be asserted, leaving the researcher free 
to concentrate on the physics. We can return later to prove the mathematical results
when time permits. \<close> 



class AxTriangleInequality = Norms +
  assumes AxTriangleInequality: "\<forall> p q . axTriangleInequality p q"
begin
end (* of class AxTriangleInequality *)

end (* of theory AxTriangleInequality *)
