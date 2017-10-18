(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
License: LGPL
*)

section \<open>Generating Code for the Solver\<close>

theory Solver_Code
  imports Algorithm
begin

(*test whether Haskell code generation works*)
export_code solve checking Haskell

export_code solve integer_of_nat nat_of_integer in Haskell module_name HLDE file "generated/"

end
