(*
  File:      Elimination_Of_Repeated_Factors/ERF_Code_Test.thy
  Authors:   Katharina Kreuzer (TU München)
             Manuel Eberl (University of Innsbruck)

  Tests for the code generation of the ERF algorithm
*)

theory ERF_Code_Test
imports
  "HOL-Library.Code_Target_Numeral"
  ERF_Algorithm
  ERF_Code_Fixes
begin

hide_const (open) Formal_Power_Series.radical
notation (output) Abs_mod_ring ("_")

subsection \<open>Example for the code generation with \<open>GF(2)\<close>\<close>

type_synonym gf2 = "bool mod_ring"

definition x where "x = [:0, 1:]"
definition p :: "gf2 poly"
  where "p = x^16 + x^15 + x^13 + x^11 + x^9 + x^8 + x^6 + x^5 + x^4 + x^2 + x + 1"

value "ERF p"
value "radical p"

(* commented out until construction of Galois fields is in the AFP

subsection \<open>Some tests with \<open>GF(256)\<close>\<close>

definition "p1 = poly_of_list (map inject_gf256 [42, 97, 23, 7, 0, 21])"
definition "p2 = poly_of_list (map inject_gf256 [109, 2, 123, 47, 99, 33])"
definition "p3 = poly_of_list (map inject_gf256 [21, 4, 65, 221, 197])"
definition "p4 = poly_of_list (map inject_gf256 [3, 5])"

value "radical (p1^2 * p2^3 * p3 ^ 3 * p4 ^ 5)"
*)

end
