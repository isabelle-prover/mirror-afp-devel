(* Author: Fabian Immler, Alexander Maletzky *)

theory Code_Target_Rat
  imports Complex_Main "HOL-Library.Code_Target_Numeral"
begin

text \<open>Mapping type @{typ rat} to type "Rat.rat" in Isabelle/ML. Serialization for other target
  languages will be provided in the future.\<close>

(* For testing only. *)
(*
primrec logistic' :: "rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> rat" where "logistic' r x 0 = x"
  | "logistic' r x (Suc n) = logistic' r (r * x * (rat_of_int 1 - x)) n"
definition "logistic n = logistic' (3.6) (0.5) (nat_of_integer n)"
ML \<open>val logistic_int = @{code logistic}\<close>
ML \<open>
fun logistic' r x n = (if n = 0 then x else logistic' r (r * x * (Rat.of_int 1 - x)) (n - 1))
fun logistic_ml n = logistic' (Rat.make (36, 10)) (Rat.make (5, 10)) n
\<close>
*)

context includes integer.lifting begin

lift_definition rat_of_integer :: "integer \<Rightarrow> rat" is Rat.of_int .

lift_definition quotient_of' :: "rat \<Rightarrow> integer \<times> integer" is quotient_of .

lemma [code]: "Rat.of_int (int_of_integer x) = rat_of_integer x"
  by transfer simp

lemma [code_unfold]: "quotient_of = (\<lambda>x. map_prod int_of_integer int_of_integer (quotient_of' x))"
  by transfer simp

end

code_printing
  type_constructor rat \<rightharpoonup>
    (Eval) "Rat.rat" |
  constant "plus :: rat \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
    (Eval) "Rat.add" |
  constant "minus :: rat \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
    (Eval) "Rat.add ((_)) (Rat.neg ((_)))" |
  constant "times :: rat \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
    (Eval) "Rat.mult" |
  constant "inverse :: rat \<Rightarrow> _" \<rightharpoonup>
    (Eval) "Rat.inv" |
  constant "divide :: rat \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
    (Eval) "Rat.mult ((_)) (Rat.inv ((_)))" |
  constant "rat_of_integer :: integer \<Rightarrow> rat" \<rightharpoonup>
    (Eval) "Rat.of'_int" |
  constant "abs :: rat \<Rightarrow> _" \<rightharpoonup>
    (Eval) "Rat.abs" |
  constant "0 :: rat" \<rightharpoonup>
    (Eval) "!(Rat.make (0, 1))" |
  constant "1 :: rat" \<rightharpoonup>
    (Eval) "!(Rat.make (1, 1))" |
  constant "uminus :: rat \<Rightarrow> rat" \<rightharpoonup>
    (Eval) "Rat.neg" |
  constant "HOL.equal :: rat \<Rightarrow> _" \<rightharpoonup>
    (Eval) "!((_ : Rat.rat) = _)" |
  constant "quotient_of'" \<rightharpoonup>
    (Eval) "Rat.dest"

(* For testing only. *)
(*
ML \<open>val logistic_rat = @{code logistic}\<close>
ML \<open>timeap (fn n => let val r = logistic_int n in r end) 16\<close> (* 2.534s cpu time *)
ML \<open>timeap (fn n => let val r = logistic_ml n in r end) 16\<close> (* 0.021s cpu time *)
ML \<open>timeap (fn n => let val r = logistic_rat n in r end) 16\<close> (* 0.021s cpu time *)
*)

end (* theory *)
