chapter "CakeML Compiler"

theory CakeML_Compiler
imports
  "generated/CakeML/Ast"
  "Show.Show_Instances"
keywords "cakeml" :: diag
begin

hide_const (open) Lem_string.concat

ML_file "Tools/cakeml_sexp.ML"
ML_file "Tools/cakeml_compiler.ML"

end