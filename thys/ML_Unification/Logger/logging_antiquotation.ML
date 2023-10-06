(*  Title:      Logger/logging_antiquotation.ML
    Author:     Kevin Kappelmann
*)
signature LOGGING_ANTIQUOTATION =
sig
  val show_log_pos: bool Config.T
end

structure Logging_Antiquotation : LOGGING_ANTIQUOTATION =
struct

structure Util = ML_Code_Util

val show_log_pos = Attrib.setup_config_bool @{binding "show_log_pos"} (K false)

val log =
  let
    fun body ts ((log_level, logger_binding), show_log_pos_opt) =
      let
        val (_, pos) = Token.name_of_src ts
        val ctxt_internal = Util.internal_name "ctxt"
        val show_log_pos = the_default
          (Util.spaces ["Config.get", ctxt_internal, " Logging_Antiquotation.show_log_pos"])
          show_log_pos_opt
        val additional_info = Util.spaces [
            "if", ML_Syntax.atomic show_log_pos,
            "then",
              ML_Syntax.print_string "\n", "^",
              ML_Syntax.atomic
                ("Position.here " ^ ML_Syntax.atomic (ML_Syntax.print_position pos)),
            "else", ML_Syntax.print_string ""
          ] |> ML_Syntax.atomic
        val message_f_internal = Util.internal_name "message_f"
        val code = Util.spaces [
            "fn", ctxt_internal, "=> fn", message_f_internal, "=> Logger.log",
            ML_Syntax.atomic logger_binding,
            ML_Syntax.atomic log_level,
            ctxt_internal,
            ML_Syntax.atomic (Util.spaces ["fn _ =>", message_f_internal, "() ^", additional_info])
          ] |> ML_Syntax.atomic
      in pair (K ("", code)) end
  in
    ML_Antiquotation.declaration @{binding "log"}
      (Scan.optional Parse.embedded "Logger.INFO"
        -- Scan.optional Parse.embedded "logger" (*works in particular if structure implements HAS_LOGGER*)
        -- Scan.option Parse.embedded
        |> Scan.lift)
      body
  end

(*setup the antiquotation*)
val _ = Theory.setup log

end