chapter "Code generation"

theory CakeML_Code
imports
  Evaluate_Single
begin

declare evaluate_list_eq[code_unfold]
declare fix_clock_evaluate[code_unfold]
declare fun_evaluate_equiv[code]

declare [[code abort: failwith fp64_negate fp64_sqrt fp64_sub fp64_mul fp64_div fp64_add fp64_abs]]

export_code evaluate fun_evaluate fun_evaluate_prog
  checking SML

end