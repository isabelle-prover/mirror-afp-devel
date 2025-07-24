(*  Title:      ML_Utils/functor_instance_antiquot.ML
    Author:     Kevin Kappelmann

Antiquotation to create functor instances with FUNCTOR_INSTANCE_BASE (FI) arguments.
*)
signature FUNCTOR_INSTANCE_ANTIQUOT =
sig
  val binding : binding
end

structure Functor_Instance_Antiquot : FUNCTOR_INSTANCE_ANTIQUOT =
struct

@{parse_entries (struct) PA
  [path, struct_name, struct_sig, functor_name, FI_struct_name, id, more_args]}

structure PU = Parse_Util
structure MU = ML_Syntax_Util

val parse_arg_entries =
  let
    val required_keys = map PA.key [PA.functor_name, PA.id]
    val parse_nonempty_name = PU.nonempty_name o K o suffix " must not be empty"
    val parse_value = PA.parse_entry
      Parse.embedded
      Args.name
      (parse_nonempty_name "struct_sig")
      (parse_nonempty_name "functor_name")
      Args.name
      Parse.embedded
      Parse.embedded
    val parse_entry = Parse_Key_Value.parse_entry PA.parse_key PU.eq parse_value
    val default_entries = PA.empty_entries ()
      |> fold PA.set_entry [PA.FI_struct_name "FI", PA.more_args "", PA.path "", PA.struct_name ""]
  in PA.parse_entries_required Parse.and_list1 required_keys parse_entry default_entries end

fun mk_functor_instance (entries, pos) =
  let
    val path = PA.get_path entries
    val struct_name = PA.get_struct_name entries
    val full_name = if path = "" then quote struct_name
      else if struct_name = "" then path
      else MU.spaces [path, "^", quote (prefix "." struct_name)]
    val functor_arg = MU.mk_struct [
        PA.get_more_args entries,
        MU.mk_structure (PA.get_FI_struct_name entries) (SOME "FUNCTOR_INSTANCE_BASE") (MU.mk_struct [
          MU.mk_val_struct "binding" (MU.mk_app ["Binding.set_pos",
            MU.atomic (ML_Syntax.print_position pos),
            MU.mk_app_atomic ["Binding.qualified_name", MU.atomic full_name]]),
          MU.mk_val_struct "id" (PA.get_id entries)
        ])
      ]
  in
    (struct_name <> "" ? MU.mk_structure struct_name (PA.get_struct_sig_safe entries))
    (MU.mk_app [PA.get_functor_name entries, MU.atomic functor_arg])
  end

val binding = @{binding "functor_instance"}

val parse_antiquotation_args = (Parse.!!! parse_arg_entries |> PU.position |> Scan.lift)
  >> mk_functor_instance

fun read_antiquotation input ctxt =
  let
    val keywords = Thy_Header.get_keywords' ctxt
    val code = input
      |> Parse.read_embedded ctxt keywords
        (pair (Context.Proof ctxt) #> parse_antiquotation_args #> apsnd snd)
  in ML_Context.expand_antiquotes (ML_Code_Util.read code) ctxt end

val setup_antiquotation = ML_Context.add_antiquotation_embedded binding (K read_antiquotation)

val _ = Theory.setup setup_antiquotation

end
