\<^marker>\<open>creator "Kevin Kappelmann"\<close>
chapter \<open>ML Typeclasses\<close>
section \<open>Basic Setup for Generic Typeclasses\<close>
theory Gen_ML_Typeclasses_Base
  imports ML_Args_Antiquotations
    keywords "ML_gen_file" :: thy_decl
begin

ML\<open>
\<^functor_instance>\<open>struct_name: Para_Type_Args_Antiquotations
  functor_name: Args_Antiquotations
  id: \<open>"ParaT"\<close>
  more_args: \<open>val init_args = {
    args = SOME ["'p1"],
    sep = SOME ", ",
    encl = SOME ("", ""),
    encl_arg = SOME ("", ""),
    start = SOME 0,
    stop = SOME NONE}\<close>\<close>
\<close>
local_setup \<open>Para_Type_Args_Antiquotations.setup_args_attribute
  (SOME "set parameter type args antiquotation arguments")\<close>
setup \<open>Para_Type_Args_Antiquotations.setup_args_antiquotation\<close>
setup \<open>Para_Type_Args_Antiquotations.setup_arg_antiquotation\<close>

(*functions to create type generic ML code*)
ML\<open>
structure ML_Gen =
struct
  structure ParaT = Para_Type_Args_Antiquotations
  val ParaT_nargs = Context.the_generic_context #> ParaT.nargs
  val ParaT_nargs' = ParaT_nargs #> string_of_int
  val mk_name = space_implode "_"
  fun sfx_ParaT_nargs s = mk_name [s, ParaT_nargs' ()]
end
\<close>

text \<open>Setup alternative @{command ML_file} command to avoid errors when loading files twice.
This is needed since we provide ML files whose source depends on context variables and that should
be loadable in different contexts.\<close>

(*FIXME: generalise loading capabilities such that ML code can be reloaded from different places
and with different contexts.*)
ML\<open>
  let
    (*adapted from Pure/ML/ml_file.ML (removed duplicated file-loading check by skipping "provide")*)
    fun command environment catch_all debug get_file = Toplevel.generic_theory (fn gthy =>
      let
        val file = get_file (Context.theory_of gthy)
        (* val provide = Resources.provide_file file; *)
        val source = Token.file_source file

        val _ = Document_Output.check_comments (Context.proof_of gthy) (Input.source_explode source)

        val flags: ML_Compiler.flags =
          {environment = environment, redirect = true, verbose = true, catch_all = catch_all,
            debug = debug, writeln = writeln, warning = warning}
      in
        gthy
        |> Local_Theory.touch_ml_env
        |> ML_Context.exec (fn () => ML_Context.eval_source flags source)
        |> Local_Theory.propagate_ml_env
        (* |> Context.mapping provide (Local_Theory.background_theory provide) *)
      end)
    val ML = command "" false
  in
    Outer_Syntax.command \<^command_keyword>\<open>ML_gen_file\<close>
      "read and evaluate Isabelle/ML file without duplication check."
      (Resources.parse_file --| Scan.option \<^keyword>\<open>;\<close> >> ML NONE)
  end
\<close>

end