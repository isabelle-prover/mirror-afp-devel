(*  Title:      ML_Utils/functor_instance_antiquot.ML
    Author:     Kevin Kappelmann

Antiquotation to create functor instances with FUNCTOR_INSTANCE_ARGS (FIA) arguments.
*)
signature FUNCTOR_INSTANCE_ANTIQUOT =
sig
end

structure Functor_Instance_Antiquot : FUNCTOR_INSTANCE_ANTIQUOT =
struct

@{parse_entries (struct) PA
  [accessor, struct_name, struct_sig, functor_name, FIA_struct_name, id, more_args]}

structure PU = Parse_Util
structure MU = ML_Syntax_Util

val parse_arg_entries =
  let
    val required_keys = map PA.key [PA.struct_name, PA.functor_name, PA.id]
    val parse_nonempty_name = PU.nonempty_name o K o suffix " must not be empty"
    val parse_value = PA.parse_entry
      Parse.embedded
      (parse_nonempty_name "struct_name")
      Parse.embedded
      (parse_nonempty_name "functor_name")
      (parse_nonempty_name "FIA_struct_name")
      Parse.embedded
      Parse.embedded
    val parse_entry = Parse_Key_Value.parse_entry PA.parse_key PU.eq parse_value
    val default_entries = PA.empty_entries ()
      |> fold PA.set_entry [PA.FIA_struct_name "FIA", PA.more_args "", PA.accessor (quote "")]
  in
    PA.parse_entries_required Parse.and_list1 required_keys parse_entry default_entries
  end

fun mk_functor_instance (entries, pos) =
  let val functor_arg = MU.mk_struct [
      MU.mk_structure (PA.get_FIA_struct_name entries) (SOME "FUNCTOR_INSTANCE_ARGS") (MU.mk_struct [
        MU.mk_val_struct "full_name"
          (MU.spaces [PA.get_accessor entries, "^", PA.get_struct_name entries |> quote]),
        MU.mk_val_struct "id" (PA.get_id entries),
        MU.mk_val_struct "pos" (ML_Syntax.print_position pos)
      ]),
      PA.get_more_args entries
    ]
  in
    MU.mk_structure (PA.get_struct_name entries) (PA.get_struct_sig_safe entries)
      (MU.mk_app [PA.get_functor_name entries, MU.atomic functor_arg])
  end

val functor_instance = ML_Antiquotation.inline @{binding "functor_instance"}
  ((Parse.!!! parse_arg_entries |> PU.position |> Scan.lift) >> mk_functor_instance)

val _ = Theory.setup functor_instance

end
