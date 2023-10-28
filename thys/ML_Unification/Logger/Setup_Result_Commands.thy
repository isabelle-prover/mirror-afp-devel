\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Setup Result Commands\<close>
theory Setup_Result_Commands
  imports Pure
  keywords "setup_result" :: thy_decl
  and "local_setup_result" :: thy_decl
begin

paragraph \<open>Summary\<close>
text \<open>Setup and local setup with result commands\<close>

ML\<open>
  let
    fun setup_result finish (name, (source, pos)) =
      ML_Context.expression pos
        (ML_Lex.read "val" @ name @ ML_Lex.read "= Context.>>> (" @ source @ ML_Lex.read ")")
      |> finish
    val parse = Parse.embedded_ml
      -- ((\<^keyword>\<open>=\<close> || \<^keyword>\<open>\<equiv>\<close>)
      |-- Parse.position Parse.embedded_ml)
  in
    Outer_Syntax.command \<^command_keyword>\<open>setup_result\<close>
      "ML setup with result for global theory"
      (parse >> (Toplevel.theory o setup_result Context.theory_map));
    Outer_Syntax.local_theory \<^command_keyword>\<open>local_setup_result\<close>
      "ML setup with result for local theory"
      (parse >> (setup_result
        (Local_Theory.declaration {pos = \<^here>, syntax = false, pervasive = false} o K)))
  end
\<close>

end
