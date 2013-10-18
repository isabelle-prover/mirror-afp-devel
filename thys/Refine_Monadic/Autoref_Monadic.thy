header "Autoref for the Refinement Monad"
theory Autoref_Monadic
imports Refine_Transfer
begin

text {* Default setup of the autoref-tool for the monadic framework. *}

lemma autoref_monadicI:
  assumes "(b,a)\<in>\<langle>R\<rangle>nres_rel"
  assumes "RETURN c \<le> b"
  shows "(RETURN c, a)\<in>\<langle>R\<rangle>nres_rel"
  using assms
  unfolding nres_rel_def
  by simp


ML {*
  structure Autoref_Monadic = struct

    val cfg_plain = Attrib.setup_config_bool @{binding autoref_plain} (K false)

    fun autoref_monadic_tac ctxt = let
      open Autoref_Tacticals
      (*val optimize_tac = optimize_iterators_tac*)
      val ctxt = Autoref_Phases.init_data ctxt
      val plain = Config.get ctxt cfg_plain
      val trans_thms = if plain then [] else @{thms the_resI}
  
    in
      rtac @{thm autoref_monadicI}
      THEN' 
      IF_SOLVED (Autoref_Phases.all_phases_tac ctxt)
        (RefineG_Transfer.post_transfer_tac trans_thms ctxt)
        (*IF_SOLVED (RefineG_Transfer.transfer_tac trans_thms ctxt)
           (optimize_tac ctxt THEN' rtac @{thm detTAGI})
           (K all_tac) (* Transfer failed *)
        *)
        (K all_tac) (* Autoref failed *)

    end
  end
*}

method_setup autoref_monadic = {* let
    open Refine_Util Autoref_Monadic
    val autoref_flags = 
          parse_bool_config "trace" Autoref_Phases.cfg_trace
      ||  parse_bool_config "debug" Autoref_Phases.cfg_debug
      ||  parse_bool_config "plain" Autoref_Monadic.cfg_plain

  in
    parse_paren_lists autoref_flags 
    >>
    ( fn _ => fn ctxt => SIMPLE_METHOD' (
      let 
        val ctxt = Config.put Autoref_Phases.cfg_keep_goal true ctxt
      in autoref_monadic_tac ctxt end
    ))

  end

 *} 
 "Automatic Refinement and Determinization for the Monadic Refinement Framework"



end
