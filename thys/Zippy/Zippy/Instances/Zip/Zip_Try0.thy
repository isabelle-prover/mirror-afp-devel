\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Try0\<close>
theory Zip_Try0
  imports
    HOL.Sledgehammer
    Zip_Metis
begin

subsubsection \<open>Try0 Integration\<close>
ML\<open>

\<close>
ML \<open>
structure Zip =
struct open Zip
structure Try0 =
struct
  local open Context_Parsers
    val method_name = FI.id
    val clasimp_parser_id = "clasimp"
    val _ = @{assert} (Parsers_Data.Table.defined
      (Parsers_Data.get_table (Context.Proof @{context})) (Identifier.make NONE clasimp_parser_id))
  in
  fun name exec = method_name ^ "_" ^ exec
  fun run_config exec = implode_space
    ["run exec:", Zip.FI.struct_op (ML_Syntax_Util.mk_struct_access exec "all'")]
  fun method_with_config_clasimp config = implode_space [method_name, config,
    parsers_separator, clasimp_parser_id]
  fun command_update_config config method_with_config s =
    let
      val (pfx, sfx) = first_field method_with_config s |> the
        |>> (fn pfx => (not (String.isSuffix "(" pfx) ? suffix "(") pfx)
      val (mid, sfxs) = Substring.full sfx |> (if String.isSuffix "]" sfx
        then Substring.splitr (not o equal #"[")
          #>> (Substring.trimr 1) ##> (single #> cons (Substring.full "["))
        else rpair [])
      val (mid, close_parenth) = Substring.splitr (equal #")") mid ||> (K ")")
      val config_pfx = if Substring.isEmpty mid then "" else parsers_separator ^ " "
      val config = implode [config_pfx, config]
    in
      implode [pfx, method_name, Substring.string mid, " ", config, close_parenth,
        Substring.concat sfxs]
    end
  fun gen_register (name, (method, update_command)) = Try0.register_proof_method name
    {run_if_auto_try = true} (Option.map (fn {command, time, state,...} =>
        {name = name, command = update_command method command, time = time, state = state})
      ooo Try0_Util.apply_raw_named_method method true
        Try0_Util.full_attrs (Try0_HOL.silence_methods
          #> Context.proof_map (Logger.set_log_levels Logger.root Logger.OFF)))
  val mk_registrations = cons (method_name, (method_name, K I)) o
    map (fn exec => let val config = run_config exec
      in (name exec, (method_with_config_clasimp config, command_update_config config)) end)
end
end
end

local val registrations = Zip.Try0.mk_registrations Zip.Try.execs
in
val _ = map Zip.Try0.gen_register registrations
val _ = Theory.setup (Config.map_global Try0.schedule
  (prefix (implode_space (map fst registrations) ^ " ")))
end
\<close>

end
