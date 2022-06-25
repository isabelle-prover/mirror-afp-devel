(*  Title:      Code_Int_Integer_Conversion.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>A special case of a conversion.\<close>

theory Code_Int_Integer_Conversion
imports
  Main
begin

text \<open>
  Use this function to convert numeral @{typ integer}s quickly into @{typ int}s.
  By default, it works only for symbolic evaluation; normally generated code raises
  an exception at run-time. If theory \<^text>\<open>Code_Target_Int_Bit\<close> is imported,
  it works again, because then @{typ int} is implemented in terms of @{typ integer}
  even for symbolic evaluation.
\<close>

definition int_of_integer_symbolic :: "integer \<Rightarrow> int"
  where "int_of_integer_symbolic = int_of_integer"

lemma int_of_integer_symbolic_aux_code [code nbe]:
  "int_of_integer_symbolic 0 = 0"
  "int_of_integer_symbolic (Code_Numeral.Pos n) = Int.Pos n"
  "int_of_integer_symbolic (Code_Numeral.Neg n) = Int.Neg n"
  by (simp_all add: int_of_integer_symbolic_def)

end
