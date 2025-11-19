theory Test_Print
imports
  "../Preproc/Embed"
  Lazy_Case.Lazy_Case (* FIXME why is this import necessary *)
  CakeML.CakeML_Compiler
  "../Backend/CakeML_Byte"
  "../Compiler/Compiler"
  "../Preproc/Eval_Instances"
begin

definition seq :: "'a \<Rightarrow> 'b \<Rightarrow> 'a" where
"seq x y = x"

fun seq_list :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list" where
"seq_list [] _ = []" |
"seq_list (x # xs) f = x # seq (seq_list xs f) (f x)"

definition f :: "(char \<Rightarrow> 'b) \<Rightarrow> string" where
"f = seq_list (show True)"

declassify valid: f
thm valid

embed (eval, skip) f' is Test__Print_f .

definition result :: prog where
"result = compile f'.C_info f'"

declare
  constructors.C_def [code]
  constructors.as_static_cenv_def [code]
  constructors.flat_C_info_def [code]
  f'.C_info_def [code]
  cakeml.mk_exp.simps [code]
  cakeml.mk_con.simps [code]
  cakeml.mk_clauses.simps [code]
  cakeml.mk_letrec_body_def [code]
  cakeml.compile_group_def [code]

ML\<open>
  Code_Evaluation.dynamic_value @{context} @{const result}
  |> the
  |> CakeML_Sexp.print_prog
\<close>

end
