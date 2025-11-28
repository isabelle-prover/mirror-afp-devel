\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Try0\<close>
theory Zip_Try0
  imports
    HOL.Sledgehammer
    Zip_Metis
begin

subsubsection \<open>Try0 Integration\<close>

ML \<open>
structure Zip =
struct open Zip
structure Try0 =
struct
  local val method_name = FI.id
  in
  fun add_run_config exec s =
    let
      val (pfx, sfx) = first_field method_name s |> the
        |> apfst (fn pfx => (not (String.isSuffix "(" pfx) ? suffix "(") pfx)
      val (mid, sfxs) = Substring.full sfx |> (if String.isSuffix "]" sfx
        then Substring.splitr (not o equal #"[")
          #> apfst (Substring.trimr 1) #> apsnd (single #> cons (Substring.full "["))
        else rpair [])
      val (mid, close_parenth) = Substring.splitr (equal #")") mid |> apsnd (K ")")
      val config_prefix = if Substring.isEmpty mid then ""
        else Zip.Context_Parsers.parsers_separator ^ " "
      val exec = Zip.FI.struct_op (ML_Syntax_Util.mk_struct_access exec "all'")
      val run_config = implode [config_prefix, "run exec: ", exec]
    in
      implode [pfx, method_name, Substring.string mid, " ", run_config, close_parenth]
      ^ Substring.concat sfxs
    end
  fun gen_register (name, update_command)=
    Try0.register_proof_method name {run_if_auto_try = true}
    (Option.map (fn {command, time, state,...} =>
      {name = name, command = update_command command, time = time, state = state})
      ooo Try0_Util.apply_raw_named_method method_name true Try0_Util.full_attrs
      (Try0_HOL.silence_methods
      #> Context.proof_map (Logger.set_log_levels Logger.root Logger.OFF)))
  val mk_registrations = map (fn exec => (method_name ^ "_" ^ exec, add_run_config exec))
    #> cons (method_name, I)
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
