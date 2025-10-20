(* XXX: Rename to Json *)
signature JSONP = sig
  datatype json =
         Null
         | VString of string
         | VInt of int
         | VReal of real
         | Object of json Symtab.table
         | JArr of json list

  (* XXX: add get_int get_real   *)
  val find_str: string -> json -> string Error.res
  val find_int: string -> json -> int Error.res
  val find_real: string -> json -> real Error.res
  val find_arr: string -> json ->  json list Error.res
  val get_str: string -> json -> string Error.res
  val get_int: string -> json -> int Error.res
  val parse: string -> json Error.res
  val show: json -> string
  (* val find : string -> json -> json option *)
end

structure JsonP : JSONP = struct
datatype json =
         Null
         | VString of string
         | VInt of int
         | VReal of real
         | Object of json Symtab.table
         | JArr of json list

open Symbol
fun scan_kv scanner =
    ScannerCombinator.infix_pairc string scanner

fun str_v f (k, v) = (k, f v)
val json_str = str_v VString
val json_int = str_v VInt
val json_real = str_v VReal
val json_null = str_v (K Null)

fun json_list_to_strmap ls =
    List.foldl  (fn (kv, acc) => Symtab.update kv acc) Symtab.empty ls

fun json_list_to_json ls =
    json_list_to_strmap ls
    |> Object

 fun json_list (k, ls) =
    (k,
     json_list_to_json ls)

val json_arr = str_v (fn ls => JArr (List.map json_list_to_json ls))
val just_int = integer >> VInt
val just_real = real >> VReal
val just_str = string >> VString
val basic_types = just_int || just_str || just_real

fun scan_kstr s = scan_kv string ":" json_str s
and scan_kint s = scan_kv integer ":" json_int s
and scan_kreal s = scan_kv real ":" json_real s
and scan_knull s = scan_kv (Scan.this_string "null") ":" json_null s
and scan_karr s = scan_kv scan_arr ":" json_arr s
and scan_karray2 s = scan_kv
                         (ScannerCombinator.body "[" "]" "," basic_types)
                         ":" (apsnd JArr) s
and scan_kjson s = scan_kv scan_json ":" json_list s
and scan_arr s = ScannerCombinator.body "[" "]" "," scan_json s
and scan_json s = ScannerCombinator.body
                      "{" "}" "," (scan_kjson || scan_karr || scan_kreal || scan_knull
                                              || scan_kstr || scan_kint || scan_karray2
                                  ) s

open Either
fun parse s = ParserUtil.safe_scan "json" (scan_json >> json_list_to_json) s

fun json_err_to_ta_err x = Error.json_err x |> single

(* We use lift here couldn't we just already Lift in Json Module *)
fun lift_err x = mapL json_err_to_ta_err x

fun find' k (Object t) =
    (case Symtab.lookup t k of
             NONE => JsonError.not_in_obj k |> fail |> lift_err
       | SOME x => succeed x) |
    find' _ _ = Exn.error
                    "Some internal Error Parsing the json must have happened"

fun show' x =
    case x of
        Null => "null" |
        VString s => "\"" ^ s ^ "\""|
        VInt i => Int.toString i |
        VReal r => Real.toString r |
        Object t => "{" ^
                    (Symtab.fold
                        (fn (k, v) => fn (sofar, first) =>
                            ((if first then sofar else sofar ^ ", ") ^
                            "\"" ^ k ^ "\"" ^ ": " ^ show' v, false)
                        ) t ("", true) |> fst)
                    ^ "}" |
        JArr ls => "[" ^
                    (foldl
                        (fn (v, (sofar, first)) =>
                            ((if first then sofar else sofar ^ ", ")
                            ^ show' v, false)
                        ) ("", true) ls |> fst)
                    ^ "]"

val show = show'

(* Wrong type *)
fun wrong_type k =
    JsonError.wrong_type k
    #> fail
    #> lift_err

(* XXX: how to handle json values *)
(* probably we can add get_str_arr or so *)
(* use get_str with committed and broadcast and combine_map *)
fun get_str _ (VString s) = Either.Right s
  | get_str k _ = wrong_type k "string"

fun get_real _ (VReal r) = Either.Right r
  | get_real k _ = wrong_type k "real"

fun get_int _ (VInt i) = Either.Right i
  | get_int k _ = wrong_type k "int"

fun get_arr _ (JArr ls) = Either.Right ls
  | get_arr k _ = wrong_type k "JSON ARRAY"

fun find_get get k = bindR (get k) o find' k
val find_str = find_get get_str
val find_real = find_get get_real
val find_int = find_get get_int
val find_arr = find_get get_arr
end
