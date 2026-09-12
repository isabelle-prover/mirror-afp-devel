theory Code_Test_Haskell
imports "../CakeML_Code"
options [condition = "$ISABELLE_GHC"]
begin

export_code evaluate fun_evaluate fun_evaluate_prog prim_sem_env
  checking Haskell

end