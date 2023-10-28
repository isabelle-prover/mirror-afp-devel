(*  Title:      ML_Utils/ml_syntax_util.ML
    Author:     Kevin Kappelmann

Utilities to create ML syntax as strings.
*)
signature ML_SYNTAX_UTIL =
sig
  val atomic : string -> string
  val internal_name : string -> string
  val spaces : string list -> string
  val lines : string list -> string

  val mk_app : string list -> string
  val mk_app_atomic : string list -> string

  val mk_struct_access : string -> string -> string

  val mk_type_annot : string -> string -> string

  val mk_val_prefix : string -> string
  val mk_val_sig : string -> string -> string
  val mk_val_struct : string -> string -> string

  val mk_fun_prefix : string -> string
  val mk_fun_case : string -> string -> string -> string
  val mk_fun : string -> string -> string -> string
  val mk_fun_cases : string -> (int * 'a -> string * string) -> 'a list -> string
  val add_fun_case : string -> string -> string -> string -> string

  val mk_fn : string -> string -> string
  val mk_fn_atomic : string -> string -> string

  val mk_type_prefix : string -> string
  val mk_type_abstract : string -> string
  val mk_type : string -> string -> string

  val mk_datatype_prefix : string -> string
  val mk_datatype : string -> string -> string

  val mk_fun_type : string list -> string
  val mk_fun_type_atomic : string list -> string
  val mk_type_app : string -> string -> string
  val mk_poly_type : string -> string
  val mk_poly_type_index : string -> int -> string

  val mk_type_args : string list -> string

  val mk_constructor : string * string -> string
  val mk_constructors : (string * string) list -> string

  val mk_list : string list -> string
  val mk_tuple : string list -> string
  val mk_record : string -> (string * string) list -> string

  val mk_record_sel : string -> string

  val mk_signature_name : string -> string

  val mk_sig : string list -> string
  val mk_signature : string -> string list -> string

  val mk_struct : string list -> string
  val mk_structure : string -> string option -> string -> string
end

structure ML_Syntax_Util : ML_SYNTAX_UTIL =
struct

val atomic = ML_Syntax.atomic
val internal_name = ML_Code_Util.internal_name
val spaces = ML_Code_Util.spaces
val lines = cat_lines

val mk_app = spaces
val mk_app_atomic = mk_app #> atomic

fun mk_struct_access struct_name operation = implode [struct_name, ".", operation]

fun mk_type_annot v t = spaces [v, ":", t] |> atomic

val mk_val_prefix = prefix "val "
fun mk_val_sig s1 s2 = spaces [mk_val_prefix s1, ":", s2]
fun mk_val_struct s1 s2 = spaces [mk_val_prefix s1, "=", s2]

val mk_fun_prefix = prefix "fun "
fun mk_fun_case fun_name args def = spaces [fun_name, args, "=", def]
val mk_fun = mk_fun_prefix ooo mk_fun_case
fun mk_fun_cases fun_name mk_case =
  map_index (uncurry (mk_fun_case fun_name) o mk_case) #> space_implode "\n| " #> mk_fun_prefix
fun add_fun_case fun_name args def = suffix ("\n| " ^ mk_fun_case fun_name args def)

fun mk_fn arg body = spaces ["fn", arg, "=>", body]
val mk_fn_atomic = atomic oo mk_fn

val mk_type_prefix = prefix "type "
val mk_type_abstract = mk_type_prefix
fun mk_type s1 s2 = spaces [mk_type_prefix s1, "=", s2]

val mk_datatype_prefix = prefix "datatype "
fun mk_datatype s1 s2 = spaces [mk_datatype_prefix s1, "=", s2]

val mk_fun_type = space_implode " -> "
val mk_fun_type_atomic = space_implode " -> " #> atomic
fun mk_type_app t = suffix (" " ^ t) o enclose "(" ")"
val mk_poly_type = prefix "'"
fun mk_poly_type_index t = prefix (mk_poly_type t) o string_of_int

val mk_type_args = space_implode ", "

fun mk_constructor (n, args) = spaces [n, "of", args]
val mk_constructors = map mk_constructor #> space_implode "\n| "

val mk_list = ML_Syntax.print_list I
val mk_tuple = space_implode ", " #> enclose "(" ")"
fun mk_record delim = map (fn (v, t) => spaces [v, delim, t])
  #> space_implode ", " #> enclose "{" "}"

val mk_record_sel = prefix "#"

val mk_signature_name = String.map Char.toUpper

fun mk_sig body = lines ("sig" :: body @ ["end"])

fun mk_signature sig_name rhs = spaces ["signature", sig_name, "=", mk_sig rhs]

fun mk_struct body = lines ("struct" :: body @ ["end"])

fun mk_structure struct_name opt_sig_name rhs = spaces
  ["structure", struct_name, the_default "" (Option.map (prefix ": ") opt_sig_name), "=", rhs]

end