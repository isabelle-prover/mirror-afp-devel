theory Code_Utils
imports ML_Utils
begin

ML\<open>
  fun setup_conditional_functrans binding functrans =
    let
      val enabled = Attrib.setup_config_bool binding (K false)
      val code_functrans = Code_Preproc.simple_functrans (fn ctxt =>
        if Config.get ctxt enabled then
          functrans ctxt
        else
          K NONE)
      val _ = Theory.setup (Code_Preproc.add_functrans (Binding.name_of binding, code_functrans))
    in
      enabled
    end
\<close>

ML_file "pattern_compatibility.ML"
ML_file "dynamic_unfold.ML"

simproc_setup dynamic_unfold ("x") = \<open>Dynamic_Unfold.simproc\<close>
declare [[simproc del: dynamic_unfold]]

lemma [code]: \<comment> \<open>TODO: work-around non-well-behaved simproc\<close>
  \<open>m < 0 \<longleftrightarrow> False\<close>
  \<open>m < Suc n \<longleftrightarrow> m \<le> n\<close>
  by auto

setup \<open>Code_Preproc.map_pre (fn ctxt => ctxt addsimprocs [@{simproc dynamic_unfold}])\<close>

end