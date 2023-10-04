(*  Title:      ML_Utils/parse_key_value_antiquot.ML
    Author:     Kevin Kappelmann

Antiquotation that creates boilerplate code to parse key-value pairs from a given list of keys.
*)
signature PARSE_KEY_VALUE_ANTIQUOT =
sig
  val mk_signature : string -> string list -> string
  val mk_structure : string -> string option -> string list -> string
  val mk_all : string -> string option -> string list -> string
end

structure Parse_Key_Value_Antiquot : PARSE_KEY_VALUE_ANTIQUOT =
struct

structure U = ML_Syntax_Util

val internal_param = U.internal_name o U.internal_name

val mk_poly_type_a = U.mk_poly_type_index "a"
fun mk_type_args mk_string = U.mk_type_args o map_index (mk_string o fst)

fun mk_entry_constructors mk_poly_type_a =
  map_index (fn (i, k) => (k, mk_poly_type_a i)) #> U.mk_constructors

val entry_type_name = "entry"
val mk_entry_type = U.mk_type_app entry_type_name oo mk_type_args

fun mk_entry_type_sig ks =
  U.mk_datatype (mk_entry_type mk_poly_type_a ks) (mk_entry_constructors mk_poly_type_a ks)

val mk_entry_type_struct = mk_entry_type_sig

val key_type_name = "key"
val mk_key_type = key_type_name

val mk_key_type_sig = U.mk_type_abstract mk_key_type

fun mk_key_type_struct ks = U.mk_type mk_key_type (mk_entry_type (K "unit") ks)

val key_name = "key"

fun mk_key_sig ks = U.mk_val_sig key_name
  (U.spaces ["(unit ->", mk_entry_type (K "unit") ks, ") ->", mk_key_type])

val mk_key_struct = let val kparam = internal_param "k"
  in U.mk_fun key_name kparam (U.mk_app [kparam, "()"]) end

val keys_name = internal_param "keys"
fun mk_keys_struct ks = U.mk_val_struct
  keys_name (U.mk_app ["map", key_name, U.mk_list ks])

val key_to_string_name = "key_to_string"

val mk_key_to_string_sig = U.mk_val_sig
  key_to_string_name (U.mk_fun_type [mk_key_type, "string"])

fun mk_key_to_string_struct_entry k = (U.mk_app_atomic [k, "_"], quote k)

val mk_key_to_string_struct = U.mk_fun_cases
  key_to_string_name (mk_key_to_string_struct_entry o snd)

val keys_strings_name = internal_param "keys_strings"
val mk_keys_strings_struct = U.mk_val_struct
  keys_strings_name (U.mk_app ["map", key_to_string_name, keys_name])

val key_from_string_name = internal_param "key_from_string"

fun mk_key_from_string_struct_entry k = (quote k, U.mk_app [key_name, k])

val mk_key_from_string_struct =
  let val kparam = internal_param "k"
  in
    U.mk_fun_cases key_from_string_name (mk_key_from_string_struct_entry o snd)
    #> U.add_fun_case key_from_string_name kparam (U.mk_app [
      U.mk_struct_access "Scan" "fail_with",
      U.mk_fn_atomic kparam
        (U.mk_app ["fn _ => \"key \"", "^",  kparam, "^",  "\" not registered\""]),
      kparam])
  end

fun mk_istate_type itype jtype atype =
  U.mk_type_app (U.mk_struct_access "Parse_Util" "istate") (U.mk_type_args [itype, jtype, atype])

val parse_entry_name = "parse_entry"

fun mk_parse_entry_sig ks =
  let
    val mk_parser_type = mk_istate_type "'i" "'j"
    val parser_types = map_index (mk_parser_type o mk_poly_type_a o fst) ks
      |> U.mk_fun_type
  in
    U.mk_val_sig parse_entry_name (U.mk_fun_type
      [parser_types, mk_key_type, mk_parser_type (mk_entry_type mk_poly_type_a ks)])
  end

fun mk_parse_entry_struct_entry ks (i, k) =
  let
    fun farg j = if i = j then "f" ^ string_of_int i else "_"
    val fargs = U.spaces (map_index (farg o fst)  ks)
  in (U.spaces [fargs, U.mk_app_atomic [k, "_"]], U.mk_app [farg i, ">>", k]) end

fun mk_parse_entry_struct ks =
  U.mk_fun_cases parse_entry_name (mk_parse_entry_struct_entry ks) ks

val mk_parser_type = U.mk_type_app (U.mk_struct_access "Token" "parser")

val parse_key_name = "parse_key"

val mk_parse_key_sig = U.mk_val_sig parse_key_name (mk_parser_type mk_key_type)

val Parse_Key_Value_op = U.mk_struct_access "Parse_Key_Value"

val mk_parse_key_struct = U.mk_val_struct parse_key_name
  (U.mk_app [Parse_Key_Value_op "parse_key", keys_strings_name, key_from_string_name])

val entries_type_name = "entries"
val mk_entries_type = U.mk_type_app entries_type_name oo mk_type_args

val mk_entries_type_sig = U.mk_type_abstract o mk_entries_type mk_poly_type_a

val mk_option_type = U.mk_type_app "option"

fun mk_entries_type_struct ks =
  let val record = map_index (apfst (mk_option_type o mk_poly_type_a) #> swap) ks |> U.mk_record ":"
  in U.mk_type (mk_entries_type mk_poly_type_a ks) record end

val empty_entries_name = "empty_entries"

fun mk_empty_entries_sig ks = U.mk_val_sig
  empty_entries_name (U.mk_fun_type ["unit", mk_entries_type mk_poly_type_a ks])

fun mk_empty_entries_struct ks =
  let val record = map_index (apfst (K "NONE") #> swap) ks |> U.mk_record "="
  in U.mk_fun empty_entries_name "_" record end

val set_entry_name = "set_entry"

fun mk_set_entry_sig ks =
  let val entries_type = mk_entries_type mk_poly_type_a ks
  in
    U.mk_val_sig set_entry_name
      (U.mk_fun_type [mk_entry_type mk_poly_type_a ks, entries_type, entries_type])
  end

fun mk_set_entry_struct_entry ks (i, k) =
  let
    val prefix_other = U.internal_name
    fun record_in_data (j, k) = (k, if i = j then "_" else prefix_other k)
    val record_in = map_index record_in_data ks |> U.mk_record "="
    val vparam = internal_param "v"
    fun record_out_data (j, k) = (k, if i = j then U.mk_app ["SOME", vparam] else prefix_other k)
    val record_out = map_index record_out_data ks |> U.mk_record "="
  in (U.spaces [U.mk_app_atomic [k, vparam], record_in], record_out) end

fun mk_set_entry_struct ks =
  U.mk_fun_cases set_entry_name (mk_set_entry_struct_entry ks) ks

val merge_entries_name = "merge_entries"

fun mk_merge_entries_sig ks =
  let val entries_type = mk_entries_type mk_poly_type_a ks
  in U.mk_val_sig merge_entries_name (U.mk_fun_type [entries_type, entries_type, entries_type]) end

fun mk_merge_entries_struct ks =
  let
    fun prefix i = suffix (string_of_int i) o U.internal_name
    fun record_in_data i k = (k, prefix i k)
    fun record_in i = map (record_in_data i) ks |> U.mk_record "="
    fun record_out_data k = (k, U.mk_app ["merge_options", U.mk_tuple [prefix 1 k, prefix 2 k]])
    val record_out = map record_out_data ks |> U.mk_record "="
  in U.mk_fun merge_entries_name (U.spaces [record_in 1, record_in 2]) record_out end

val mk_map_name = prefix "map_"
val mk_map_name_safe = suffix "_safe" o mk_map_name

fun mk_map_type mk_arg_type ks i = U.mk_fun_type [
    U.mk_fun_type_atomic [mk_arg_type (mk_poly_type_a i), U.mk_poly_type_index "b" i],
    mk_entries_type mk_poly_type_a ks,
    mk_entries_type (fn j => if i = j then U.mk_poly_type_index "b" j else mk_poly_type_a j) ks
  ]

fun mk_map_safe_sig ks (i, k) = U.mk_val_sig (mk_map_name_safe k) (mk_map_type mk_option_type ks i)
fun mk_map_safes_sig ks = map_index (mk_map_safe_sig ks) ks |> U.lines

fun mk_map_sig ks (i, k) = U.mk_val_sig (mk_map_name k) (mk_map_type I ks i)
fun mk_maps_sig ks = map_index (mk_map_sig ks) ks |> U.lines

fun mk_map_safe_struct ks (i, k) =
  let
    val prefix = U.internal_name
    fun record_in_data k = (k, prefix k)
    val record_in = map record_in_data ks |> U.mk_record "="
    val fparam = internal_param "f"
    fun record_out_data (j, k) = (k, if i = j
      then U.mk_app ["SOME", U.mk_app_atomic [fparam, prefix k]]
      else prefix k)
    val record_out = map_index record_out_data ks |> U.mk_record "="
  in U.mk_fun (mk_map_name_safe k) (U.spaces [fparam, record_in]) record_out end

fun mk_map_safes_struct ks = map_index (mk_map_safe_struct ks) ks |> U.lines

val the_value_name = internal_param "the_value"
val mk_the_value_struct =
  let val [kparam, vparam] = map internal_param ["k", "v"]
  in
    U.mk_fun the_value_name (U.spaces ["_", U.mk_app_atomic ["SOME", vparam]]) vparam
    |> U.add_fun_case the_value_name (U.spaces [kparam, "NONE"])
      (U.spaces ["error (\"No data for key \\\"\" ^", key_to_string_name, kparam, "^ \"\\\".\")"])
  end

fun mk_map_struct k =
  let val fparam = internal_param "f"
  in
    U.mk_fun (mk_map_name k) fparam (U.mk_app [
      mk_map_name_safe k,
      U.mk_app_atomic [fparam, "o",
        U.mk_app [the_value_name, U.mk_app_atomic [key_name, k]]]])
  end

val mk_maps_struct = map mk_map_struct #> U.lines

val mk_get_name = prefix "get_"
val mk_get_name_safe = suffix "_safe" o mk_get_name

fun mk_get_type mk_res_type ks i = U.mk_fun_type
  [mk_entries_type mk_poly_type_a ks, mk_res_type (mk_poly_type_a i)]

fun mk_get_safe_sig ks (i, k) = U.mk_val_sig (mk_get_name_safe k) (mk_get_type mk_option_type ks i)
fun mk_get_safes_sig ks = map_index (mk_get_safe_sig ks) ks |> U.lines

fun mk_get_sig ks (i, k) = U.mk_val_sig (mk_get_name k) (mk_get_type I ks i)
fun mk_gets_sig ks = map_index (mk_get_sig ks) ks |> U.lines

fun mk_get_safe_struct ks k =
  let
    val entries = internal_param "entries"
    val arg = (U.mk_type_annot entries (mk_entries_type mk_poly_type_a ks))
  in U.mk_fun (mk_get_name_safe k) arg (U.spaces [U.mk_record_sel k, entries]) end

fun mk_get_safes_struct ks = map (mk_get_safe_struct ks) ks |> U.lines

fun mk_get_struct k =
  let val entries = internal_param "entries"
  in
    U.mk_fun (mk_get_name k) entries (U.mk_app [the_value_name,
      U.mk_app_atomic [key_name, k],
      U.mk_app_atomic [mk_get_name_safe k, entries]])
  end

val mk_gets_struct = map mk_get_struct #> U.lines

val mk_list_type = U.mk_type_app "list"
fun mk_parse_key_value_entry_type mk_poly_type ks = U.mk_type_app (Parse_Key_Value_op "entry")
  (U.mk_type_args [mk_key_type, mk_entry_type mk_poly_type ks])
fun mk_parse_key_value_entries_type mk_poly_type ks = U.mk_type_app (Parse_Key_Value_op "entries")
  (U.mk_type_args [mk_key_type, mk_entry_type mk_poly_type ks])

val key_entry_entry_type_name = "key_entry_entry"
val mk_key_entry_entry_type =
  U.mk_type_app key_entry_entry_type_name oo mk_type_args

fun mk_key_entry_entry_type_sig ks = U.mk_type (mk_key_entry_entry_type mk_poly_type_a ks)
  (mk_parse_key_value_entry_type mk_poly_type_a ks)

val mk_key_entry_entry_type_struct = mk_key_entry_entry_type_sig

val key_entry_entries_type_name = "key_entry_entries"
val mk_key_entry_entries_type = U.mk_type_app key_entry_entries_type_name oo mk_type_args

fun mk_key_entry_entries_type_sig ks = U.mk_type (mk_key_entry_entries_type mk_poly_type_a ks)
  (mk_parse_key_value_entries_type mk_poly_type_a ks)

val mk_key_entry_entries_type_struct = mk_key_entry_entries_type_sig

val key_entry_entries_from_entries_name = "key_entry_entries_from_entries"

fun mk_key_entry_entries_from_entries_sig ks = U.mk_val_sig key_entry_entries_from_entries_name
  (U.mk_fun_type [mk_entries_type mk_poly_type_a ks, mk_key_entry_entries_type mk_poly_type_a ks])

fun mk_key_entry_entries_from_entries_struct ks =
  let
    val prefix_key = U.internal_name
    fun record_in_data k = (k, prefix_key k)
    val record_in = map record_in_data ks |> U.mk_record "="
    fun list_out_data k = U.mk_app [
      U.mk_struct_access "Option" "map",
      U.mk_app_atomic ["pair", U.mk_app_atomic [key_name, k], "o", k],
      prefix_key k]
    val list_out = map list_out_data ks |> U.mk_list
  in
    U.mk_fun key_entry_entries_from_entries_name record_in (U.mk_app [list_out,
      "|>", "map_filter", "I"])
  end

val mk_entries_from_entry_list_name = "entries_from_entry_list"

fun mk_entries_from_entry_list_sig ks = U.mk_val_sig mk_entries_from_entry_list_name
  (U.mk_fun_type [mk_list_type (mk_entry_type mk_poly_type_a ks), mk_entries_type mk_poly_type_a ks])

val mk_entries_from_entry_list_struct =
  let val kees = internal_param "kees"
  in
    U.mk_fun mk_entries_from_entry_list_name kees (U.mk_app
      ["fold", set_entry_name, kees, U.mk_app_atomic [empty_entries_name, "()"]])
  end

val mk_context_parser_type = U.mk_type_app (U.mk_struct_access "Token" "context_parser")

local
fun mk_names name = (prefix "gen_" name, name, suffix "'" name)

fun gen_mk_parse_key_value_result_type mk_result_type mk_type mk_poly_type =
  mk_type mk_poly_type #> mk_result_type
val mk_parse_key_value_result_type = gen_mk_parse_key_value_result_type mk_parser_type
val mk_parse_key_value_result_type' = gen_mk_parse_key_value_result_type mk_context_parser_type
in

val (gen_parse_key_entry_entries_required_name, parse_key_entry_entries_required_name,
  parse_key_entry_entries_required_name') = mk_names "parse_key_entry_entries_required"

val mk_gen_parse_key_entry_entries_required_struct =
  let
    val (args as [parse_entries_required, parse_list, ks, parse_entry]) = map internal_param
      ["parse_entries_required", "parse_list", "ks", "parse_entry"]
  in
    U.mk_fun gen_parse_key_entry_entries_required_name (U.spaces args)
      (U.mk_app [parse_entries_required, "(op =)", key_to_string_name, ks,
        U.mk_app_atomic [parse_list, parse_entry]])
  end

fun gen_mk_parse_entries_required_args_type mk_parse_key_value_result_type
  mk_poly_type_in mk_poly_type_out ks =
  let
    val entry_parser = mk_parse_key_value_result_type mk_key_entry_entry_type mk_poly_type_in ks
    val entries_parser = U.mk_fun_type_atomic [entry_parser,
      mk_parse_key_value_result_type mk_key_entry_entries_type mk_poly_type_out ks]
  in U.mk_fun_type [entries_parser, mk_list_type key_type_name, entry_parser] end

fun gen_mk_parse_key_entry_entries_required_sig name mk_parse_key_value_result_type ks =
  let val (mk_poly_type_in, mk_poly_type_out) = apply2 U.mk_poly_type_index ("a", "b")
  in
    U.mk_val_sig name (U.mk_fun_type [
      gen_mk_parse_entries_required_args_type mk_parse_key_value_result_type
        mk_poly_type_in mk_poly_type_out ks,
      mk_parse_key_value_result_type mk_key_entry_entries_type mk_poly_type_out ks])
  end

fun mk_parse_key_entry_entries_required_sigs ks = U.lines [
  gen_mk_parse_key_entry_entries_required_sig parse_key_entry_entries_required_name
    mk_parse_key_value_result_type ks,
  gen_mk_parse_key_entry_entries_required_sig parse_key_entry_entries_required_name'
    mk_parse_key_value_result_type' ks
]

fun gen_mk_parse_key_entry_entries_required_struct name parse_entries_required =
  let val parse_list = internal_param "parse_list"
  in
    U.mk_fun name parse_list (U.mk_app
      [gen_parse_key_entry_entries_required_name, parse_entries_required, parse_list])
  end

val mk_parse_key_entry_entries_required_structs = U.lines [
  gen_mk_parse_key_entry_entries_required_struct parse_key_entry_entries_required_name
    (Parse_Key_Value_op "parse_entries_required"),
  gen_mk_parse_key_entry_entries_required_struct parse_key_entry_entries_required_name'
    (Parse_Key_Value_op "parse_entries_required'")
]

val (gen_parse_entries_required_name, parse_entries_required_name, parse_entries_required_name') =
  mk_names "parse_entries_required"

val mk_gen_parse_entries_required_struct =
  let
    val (args as [parse_key_entry_entries_required, parse_list, ks, parse_entry, default_entries]) =
      map internal_param ["parse_key_entry_entries_required", "parse_list", "ks", "parse_entry",
        "default_entries"]
    val kees = internal_param "kees"
  in
    U.mk_fun gen_parse_entries_required_name (U.spaces args)
      (U.mk_app [parse_key_entry_entries_required, parse_list, ks, parse_entry,
      ">>", U.mk_fn_atomic kees
        (U.mk_app ["fold", U.mk_app_atomic [set_entry_name, "o", "snd"], kees, default_entries])])
  end

fun gen_mk_parse_entries_required_sig name mk_parse_key_value_result_type ks =
  let
    val (mk_poly_type_in, mk_poly_type_out) = apply2 U.mk_poly_type_index ("a", "b")
    val entries_type = mk_entries_type mk_poly_type_out ks
  in
    U.mk_val_sig name (U.mk_fun_type [
      gen_mk_parse_entries_required_args_type mk_parse_key_value_result_type
        mk_poly_type_in mk_poly_type_out ks,
      entries_type,
      mk_parse_key_value_result_type mk_entries_type mk_poly_type_out ks])
  end

fun mk_parse_entries_required_sigs ks = U.lines [
  gen_mk_parse_entries_required_sig parse_entries_required_name mk_parse_key_value_result_type ks,
  gen_mk_parse_entries_required_sig parse_entries_required_name' mk_parse_key_value_result_type' ks
]
end

fun gen_mk_parse_entries_required_struct name parse_key_entry_entries_required =
  let val parse_list = internal_param "parse_list"
  in
    U.mk_fun name parse_list (U.mk_app
      [gen_parse_entries_required_name, parse_key_entry_entries_required, parse_list])
  end

val mk_parse_entries_required_structs = U.lines [
  gen_mk_parse_entries_required_struct parse_entries_required_name
    parse_key_entry_entries_required_name,
  gen_mk_parse_entries_required_struct parse_entries_required_name'
    parse_key_entry_entries_required_name'
]

fun mk_signature sig_name ks = U.mk_signature sig_name [
    mk_entry_type_sig ks,
    mk_key_type_sig,
    mk_key_sig ks,
    mk_key_to_string_sig,
    mk_parse_entry_sig ks,
    mk_parse_key_sig,
    mk_entries_type_sig ks,
    mk_empty_entries_sig ks,
    mk_set_entry_sig ks,
    mk_merge_entries_sig ks,
    mk_map_safes_sig ks,
    mk_maps_sig ks,
    mk_get_safes_sig ks,
    mk_gets_sig ks,
    mk_key_entry_entry_type_sig ks,
    mk_key_entry_entries_type_sig ks,
    mk_key_entry_entries_from_entries_sig ks,
    mk_entries_from_entry_list_sig ks,
    mk_parse_key_entry_entries_required_sigs ks,
    mk_parse_entries_required_sigs ks
  ]

fun mk_structure struct_name optsig_name ks = U.mk_struct [
    mk_entry_type_struct ks,
    mk_key_type_struct ks,
    mk_key_struct,
    mk_keys_struct ks,
    mk_key_to_string_struct ks,
    mk_keys_strings_struct,
    mk_key_from_string_struct ks,
    mk_parse_entry_struct ks,
    mk_parse_key_struct,
    mk_entries_type_struct ks,
    mk_empty_entries_struct ks,
    mk_set_entry_struct ks,
    mk_merge_entries_struct ks,
    mk_the_value_struct,
    mk_map_safes_struct ks,
    mk_maps_struct ks,
    mk_get_safes_struct ks,
    mk_gets_struct ks,
    mk_key_entry_entry_type_struct ks,
    mk_key_entry_entries_type_struct ks,
    mk_key_entry_entries_from_entries_struct ks,
    mk_entries_from_entry_list_struct,
    mk_gen_parse_key_entry_entries_required_struct,
    mk_parse_key_entry_entries_required_structs,
    mk_gen_parse_entries_required_struct,
    mk_parse_entries_required_structs
  ] |> U.mk_structure struct_name optsig_name

fun mk_all struct_name optsig_name ks =
  let val sig_name = the_default (U.mk_signature_name struct_name) optsig_name
  in
    U.lines [
      mk_signature sig_name ks,
      mk_structure struct_name (SOME sig_name) ks
    ]
  end

val parse_sig_name = Parse_Util.nonempty_name (K "Signature name must not be empty.")
val parse_struct_name = Parse_Util.nonempty_name (K "Structure name must not be empty.")

val parse_keys =
  let
    val parse_key = Parse_Util.nonempty_name (K "Key names must not be empty.")
    val key_eq = (op =)
    fun dup_msg xs _ = Pretty.block [
        Pretty.str "All keys must be distinct. Duplicates: ",
        duplicates key_eq xs |> Parse_Key_Value.pretty_keys I
      ] |> Pretty.string_of
  in
    Args.bracks (Parse.list1 parse_key)
    |> Parse_Util.distinct_list key_eq dup_msg
  end

val parse_sig = parse_sig_name -- parse_keys
val parse_struct = parse_struct_name -- Scan.option parse_sig_name -- parse_keys
val parse_all = parse_struct_name -- Scan.option parse_sig_name -- parse_keys

datatype mode = SIG | STRUCT | ALL

fun mode_of_string "sig" = SIG
  | mode_of_string "struct" = STRUCT
  | mode_of_string "all" = ALL
  | mode_of_string m = Scan.fail_with (fn m => fn _ => "illegal mode " ^ m) m

val parse_mode = Parse_Key_Value.parse_key ["sig", "struct", "all"] mode_of_string

val parse =
  let
    val parse_mode = Scan.optional (Parse_Util.parenths (Parse.!!! parse_mode)) ALL
    fun parse_of_mode SIG = parse_sig >> uncurry mk_signature
      | parse_of_mode STRUCT = parse_struct
          >> (fn ((struct_name, optsig_name), ks) => mk_structure struct_name optsig_name ks)
      | parse_of_mode ALL = parse_all
          >> (fn ((struct_name, optsig_name), ks) => mk_all struct_name optsig_name ks)
  in parse_mode :|-- parse_of_mode end

val _ = Theory.setup (ML_Antiquotation.inline @{binding "parse_entries"} (Scan.lift parse))

end