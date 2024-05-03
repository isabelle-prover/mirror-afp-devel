(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Option_Scanner
imports ML_Record_Antiquotation
begin


text \<open>
The purpose of the option scanner is to provide an interface to scan lists of options 
(key / value) for toplevel commands. As values may have different types the idea is that
the collection of options is represented by an record of optional values. This record can be
provided individually for each command. The initial option-record "empty" has every component
assigned to @{ML NONE}. To be able to specify all options in a single list, we represent a single
parser / scanner for a field as an update function for the option-record, which is composed
by the map-functions for the record fields. So we can preserve different types for parsing
individual fields (and do not need an universal value type), while the specification list
is a monotype. 

\<close>
ML \<open>

signature OPTION_SCANNER =
  sig
    type 'opt parse = ('opt -> 'opt) parser
    type 'opt field =  string * 'opt parse * 'opt parse option (* name, parser, default value parser *)
    type ('opt, 'a) map_field = ('a option -> 'a option) -> ('opt -> 'opt)

    val mk_opt: string -> 'a parser -> (('opt, 'a) map_field) -> 'a option -> 'opt field

    val bool_opt: ('opt, bool) map_field -> bool option -> 'opt field
    val int_opt: ('opt, int) map_field -> int option -> 'opt field
    val real_opt: ('opt, real) map_field -> real option -> 'opt field
    val string_opt: ('opt, string) map_field -> string option -> 'opt field
    val path_opt: ('opt, string * Position.T) map_field -> (string * Position.T) option -> 'opt field
    val string_list_opt: ('opt, string list) map_field -> string list option -> 'opt field
    val path_list_opt: ('opt, (string * Position.T) list) map_field -> (string * Position.T) list option -> 'opt field
 
    val scan_bool: bool parser
    val scan_list: 'a parser -> 'b parser -> 'c list parser -> 'c list parser
    val scan_string_list: string list parser

    val get_options: 'opt -> (string * ('opt field)) list -> 'opt parser

  end

structure Option_Scanner:OPTION_SCANNER =
struct

  type 'opt parse = ('opt -> 'opt) parser
  type 'opt field =  string * 'opt parse * 'opt parse option 
  type ('opt, 'a) map_field = ('a option -> 'a option) -> ('opt -> 'opt)

  val equals = \<^keyword>\<open>=\<close>

  val scan_bool = Parse.group (fn _ => "bool (true / false)")
    (Parse.reserved "false" >> K false || Parse.reserved "true" >> K true)

  val scan_path = Scan.ahead Parse.not_eof -- Parse.path >> (fn (tok, name) => (name, Token.pos_of tok))

  fun scan_list scan_open scan_close scan_entries = 
   (scan_open -- scan_close >> K []) ||
   (scan_open |-- scan_entries  --| scan_close)

  val scan_string_list = scan_list \<^keyword>\<open>[\<close> \<^keyword>\<open>]\<close> (Parse.enum "," Parse.embedded)
  val scan_path_list = scan_list \<^keyword>\<open>[\<close> \<^keyword>\<open>]\<close> (Parse.enum "," scan_path)

  fun scan_field scan map_field = scan >> (map_field o K o SOME)
  fun scan_default default map_field = Option.map (fn v => Scan.succeed  (map_field (K (SOME v)))) default


  fun mk_opt (kind:string) scan map_field default = (kind, scan_field scan map_field, scan_default default map_field)


  fun bool_opt map_field default        = mk_opt "bool" scan_bool map_field default
  fun int_opt map_field default         = mk_opt "int" Parse.int map_field default
  fun real_opt map_field default        = mk_opt "real" Parse.real map_field default
  fun string_opt map_field default      = mk_opt "string" Parse.embedded map_field default
  fun path_opt map_field default        = mk_opt "path" scan_path map_field default
  fun string_list_opt map_field default = mk_opt "string list" scan_string_list map_field default
  fun path_list_opt map_field default   = mk_opt "path list" scan_path_list map_field default
 
  fun scan_config_value eq scan_value maybe_default =
    (eq |-- Parse.!!! scan_value) || 
    (case maybe_default of SOME d => d | _ => Scan.fail)

  fun scan_option (name, (_, scan_value, maybe_default)) =
    Parse.reserved name -- Parse.!!! (scan_config_value equals scan_value maybe_default) 

  fun scan_options opts = 
    let
      fun string_of_opt (name, (kind, parser, maybe_default)) = name ^ ": " ^ kind;
      val option_description = map (Pretty.str o string_of_opt) opts |> Pretty.list "(" ")" |> Pretty.string_of;
      val msg = fn () => "options " ^ option_description
      val one_of = Parse.group msg (Scan.first (map scan_option opts));
    in                  
      Scan.optional (scan_list \<^keyword>\<open>[\<close> \<^keyword>\<open>]\<close> (Parse.enum "," (Parse.!!! one_of))) []
    end

  fun no_duplicates xs =
    case duplicates (op =) xs of
     [] => ()
    | ds => error ("duplicate option(s) defined: " ^ Pretty.string_of (Pretty.list "[" "]" (map Pretty.str ds)))
 
  fun applies fs init =
    let 
      fun apply f x = f x
    in fold apply fs init end

  fun eval_options init opts =
    let
      val _ = no_duplicates (map fst opts)
    in
      applies (map snd opts) init
    end

  fun get_options init opts =
   scan_options opts >> eval_options init


end


\<close>


ML_val \<open>

\<comment>\<open>Setup step 1: 
  define the options record. By using the record antiquotation the
  map-functions for the fields will be automatically generated.\<close>

@{record 
  \<open>datatype opts = Opts of {i:int option, b:bool option, str:string list option}\<close>
}

\<comment>\<open>Setup step 2: 
  Define the "empty" record.\<close>

val empty_opts = make_opts {i=NONE, b=NONE, str = NONE}

\<comment>\<open>Setup step 3: 
  Define the options you want to support.\<close>

val opts = [("i_opt", Option_Scanner.int_opt map_i NONE), 
            ("b_opt", Option_Scanner.bool_opt map_b (SOME true)),
            ("flags", Option_Scanner.string_list_opt map_str NONE)]

\<comment>\<open>Aux functions to showcase the parsing\<close>
fun filtered_input b = 
  filter Token.is_proper (Token.explode (Thy_Header.get_keywords' @{context}) (Binding.pos_of b) (Binding.name_of b))

fun do_parse parser = Scan.error parser o filtered_input
fun do_parse_error parser input = 
  do_parse parser input 
  handle ERROR str => (warning str; (empty_opts, []))

\<comment>\<open>Examples for successful parsing.\<close>

val (opts1, _) = do_parse (Option_Scanner.get_options empty_opts opts) 
  @{binding \<open>[i_opt=22, b_opt=true]\<close>}

val (opts2, _) = do_parse (Option_Scanner.get_options empty_opts opts) 
  @{binding \<open>[i_opt=22, b_opt]\<close>}

val (opts3, _) = do_parse (Option_Scanner.get_options empty_opts opts) 
  @{binding \<open>[flags=[hallo, "echo", otto]]\<close>}

\<comment>\<open>Examples for error reporting.\<close>

val _ = do_parse_error (Option_Scanner.get_options empty_opts opts) 
  @{binding \<open>[b_opt=ddfsf]\<close>}

val _ = do_parse_error (Option_Scanner.get_options empty_opts opts) 
  @{binding \<open>[foo=42]\<close>}

val _ = do_parse_error (Option_Scanner.get_options empty_opts opts) 
  @{binding \<open>[i_opt=22, i_opt=23]\<close>}

\<close>

end

