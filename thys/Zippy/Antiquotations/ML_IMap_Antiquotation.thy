\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>ML Indexed-Map Antiquotation\<close>
theory ML_IMap_Antiquotation
  imports
    ML_Unification.ML_Functor_Instances
    ML_Unification.ML_General_Utils
begin

paragraph \<open>Summary\<close>
text \<open>Antiquotation for indexed maps\<close>

ML_file\<open>imap_antiquotation.ML\<close>

ML\<open>
\<^functor_instance>\<open>struct_name: IMap_Antiquotation
  functor_name: IMap_Antiquotation_Functor
  id: \<open>"imap"\<close>
  more_args: \<open>val init_args = {
    sep = SOME "\n",
    encl = SOME ("", ""),
    encl_inner = SOME ("", ""),
    start = SOME 1,
    stop = SOME 2}\<close>\<close>
\<close>
local_setup \<open>IMap_Antiquotation.setup_attribute NONE\<close>
setup \<open>IMap_Antiquotation.setup_antiquotation\<close>

end
