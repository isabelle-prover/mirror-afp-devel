\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>ML Eval Antiquotation\<close>
theory ML_Eval_Antiquotation
  imports
    ML_Unification.ML_Functor_Instances
begin

paragraph \<open>Summary\<close>
text \<open>Antiquotation for ML evaluation.\<close>

ML_file\<open>eval_antiquotation.ML\<close>

ML\<open>
  \<^functor_instance>\<open>struct_name: Standard_Eval_Antiquotation
    functor_name: Eval_Antiquotation
    id: \<open>""\<close>
    more_args: \<open>val init_args = {
      parser = SOME (Parse_Util.ML_string (K "eval string must be non-empty."))
    }\<close>\<close>
\<close>
local_setup \<open>Standard_Eval_Antiquotation.setup_attribute NONE\<close>
setup \<open>Standard_Eval_Antiquotation.setup_antiquotation\<close>

end
