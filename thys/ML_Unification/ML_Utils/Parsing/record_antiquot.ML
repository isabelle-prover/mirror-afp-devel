(*  Title:      ML_Utils/parse_key_value_antiquot.ML
    Author:     Kevin Kappelmann

Antiquotation that creates boilerplate code to parse key-value pairs from a given list of keys.
*)
signature RECORD_ANTIQUOT =
sig
  val mk_signature : string -> string -> string list -> string
  val mk_structure : string -> string -> string option -> string list -> string
  val mk_all : string -> string -> string option -> string list -> string
end

structure Record_Antiquot : RECORD_ANTIQUOT =
struct

structure U = ML_Syntax_Util

val internal_param = U.internal_name o U.internal_name

val mk_poly_type_a = U.mk_poly_type_index "a"
fun mk_type_args mk_string = U.mk_type_args o map_index (mk_string o fst)

val record_type_name = "data"
val mk_record_type = U.mk_type_app record_type_name oo mk_type_args

fun mk_record_type_sig Tconstr ks =
  let val record =
    map_index (apfst (U.mk_type_app Tconstr o mk_poly_type_a) #> swap) ks
    |> U.mk_record ":"
  in U.mk_type (mk_record_type mk_poly_type_a ks) record end

val mk_record_type_struct = mk_record_type_sig

val mk_map_name = prefix "map_"

fun mk_map_type Tconstr ks i =
  let val res_typei = U.mk_poly_type_index "b" i
  in
    U.mk_fun_type [
      U.mk_fun_type_atomic [
        U.mk_type_app Tconstr (mk_poly_type_a i),
        U.mk_type_app Tconstr res_typei
      ],
      mk_record_type mk_poly_type_a ks,
      mk_record_type (fn j => if i = j then res_typei else mk_poly_type_a j) ks
    ]
  end

fun mk_map_sig Tconstr ks (i, k) = U.mk_val_sig (mk_map_name k) (mk_map_type Tconstr ks i)
fun mk_maps_sig Tconstr ks = map_index (mk_map_sig Tconstr ks) ks |> U.lines

fun mk_map_struct ks (i, k) =
  let
    val prefix = U.internal_name
    fun record_in_data k = (k, prefix k)
    val record_in = map record_in_data ks |> U.mk_record "="
    val fparam = internal_param "f"
    fun record_out_data (j, k) = (k, if i = j
      then U.mk_app_atomic [fparam, prefix k]
      else prefix k)
    val record_out = map_index record_out_data ks |> U.mk_record "="
  in U.mk_fun (mk_map_name k) (U.spaces [fparam, record_in]) record_out end

fun mk_maps_struct ks = map_index (mk_map_struct ks) ks |> U.lines

val mk_get_name = prefix "get_"

fun mk_get_type Tconstr ks i = U.mk_fun_type
  [mk_record_type mk_poly_type_a ks, U.mk_type_app Tconstr (mk_poly_type_a i)]

fun mk_get_sig Tconstr ks (i, k) = U.mk_val_sig (mk_get_name k) (mk_get_type Tconstr ks i)
fun mk_gets_sig Tconstr ks = map_index (mk_get_sig Tconstr ks) ks |> U.lines

fun mk_get_struct ks k =
  let
    val record = internal_param "record"
    val arg = (U.mk_type_annot record (mk_record_type mk_poly_type_a ks))
  in U.mk_fun (mk_get_name k) arg (U.spaces [U.mk_record_sel k, record]) end

fun mk_gets_struct ks = map (mk_get_struct ks) ks |> U.lines

fun mk_signature Tconstr sig_name ks = U.mk_signature sig_name [
    mk_record_type_sig Tconstr ks,
    mk_maps_sig Tconstr ks,
    mk_gets_sig Tconstr ks
  ]

fun mk_structure Tconstr struct_name optsig_name ks = U.mk_struct [
    mk_record_type_struct Tconstr ks,
    mk_maps_struct ks,
    mk_gets_struct ks
  ] |> U.mk_structure struct_name optsig_name

fun mk_all Tconstr struct_name optsig_name ks =
  let val sig_name = the_default (U.mk_signature_name struct_name) optsig_name
  in
    U.lines [
      mk_signature Tconstr sig_name ks,
      mk_structure Tconstr struct_name (SOME sig_name) ks
    ]
  end

val parse_Tconstr = Parse_Util.nonempty_name (K "Type constructor must not be empty")
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
  in Args.bracks (Parse.list1 parse_key) |> Parse_Util.distinct_list key_eq dup_msg end

val parse_sig = parse_sig_name -- parse_keys
val parse_struct = parse_struct_name -- Scan.option parse_sig_name -- parse_keys
val parse_all = parse_struct

datatype mode = SIG | STRUCT | ALL

fun mode_of_string "sig" = SOME SIG
  | mode_of_string "struct" = SOME STRUCT
  | mode_of_string "all" = SOME ALL
  | mode_of_string _ = NONE

val parse_mode = Parse_Key_Value.parse_key ["sig", "struct", "all"] mode_of_string

val parse =
  let
    val parse_mode = Scan.optional (Args.parens (Parse.!!! parse_mode)) ALL
    val parse_Tconstr = Scan.optional (Args.parens (Parse.!!! parse_Tconstr)) ""
    fun parse_of_mode (SIG, Tconstr) = parse_sig >> (uncurry (mk_signature Tconstr))
      | parse_of_mode (STRUCT, Tconstr) = parse_struct >> uncurry (uncurry (mk_structure Tconstr))
      | parse_of_mode (ALL, Tconstr) = parse_all >> (uncurry (uncurry (mk_all Tconstr)))
  in parse_mode -- parse_Tconstr :|-- parse_of_mode end

val _ = Theory.setup (ML_Antiquotation.inline @{binding "record"} (Scan.lift parse))

end