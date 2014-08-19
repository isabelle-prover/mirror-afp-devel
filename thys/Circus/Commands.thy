header {* Pre-declaration of user commands to workaround statefulness of outer syntax *}

theory Commands imports Main
keywords "alphabet" "state" "channel" "nameset" "chanset" "schema" "action" and "circus_process" :: thy_decl
begin                                                                                              

ML {*

val circus_process_fn =
  Unsynchronized.ref (undefined:
     (string * string option) list * binding ->
     (binding * string) list ->
     (binding * string) list ->
     (string option * (binding * string option) list) ->
     (binding * string list) list ->
     (binding * bstring list) list ->
     (binding * (bool * string)) list -> string -> theory -> theory);
 
local

val fields =
  @{keyword "["} |-- Parse.enum1 "," (Parse.binding -- (@{keyword "::"} |-- Parse.!!! Parse.typ))
    --| @{keyword  "]"};

val constrs =
  (@{keyword  "["} |-- Parse.enum1 "," (Parse.binding -- Scan.option Parse.typ) --| @{keyword  "]"}) >> pair NONE
  || Parse.typ >> (fn b => (SOME b, []));
  
val names =
  @{keyword "["} |-- Parse.enum1 "," Parse.name --| @{keyword  "]"};

in

val _ =
  Outer_Syntax.command @{command_spec "circus_process"} "Circus process specification"
    ((Parse.type_args_constrained -- Parse.binding --| @{keyword  "="}) --
      Scan.optional (@{keyword "alphabet"} |-- Parse.!!! (@{keyword  "="} |-- fields)) [] --
      Scan.optional (@{keyword "state"} |-- Parse.!!! (@{keyword  "="} |-- fields)) [] --
      Scan.optional (@{keyword "channel"} |-- Parse.!!! (@{keyword  "="} |-- constrs)) (NONE, []) --
      Scan.repeat (@{keyword "nameset"} |-- Parse.!!! ((Parse.binding --| @{keyword "="}) -- names)) --
      Scan.repeat (@{keyword "chanset"} |-- Parse.!!! ((Parse.binding --| @{keyword "="}) -- names)) --
      Scan.repeat ((@{keyword "schema"} |-- Parse.!!! ((Parse.binding --| @{keyword "="}) -- (Parse.term >> pair true))) ||
                   (@{keyword "action"} |-- Parse.!!! ((Parse.binding --| @{keyword "="}) -- (Parse.term >> pair false)))) --
      (Parse.where_ |-- Parse.!!! Parse.term)
        >> (fn (((((((a, b), c), d), e), f), g), h) =>
          Toplevel.theory (fn thy => ! circus_process_fn a b c d e f g h thy)));

end;
*}

end
