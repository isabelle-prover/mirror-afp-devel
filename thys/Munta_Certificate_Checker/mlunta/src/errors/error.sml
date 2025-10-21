(* XXX: Add lift_inlang_err *)
structure Error = struct
datatype t =
         JsonError of JsonError.t
         | ParsingError of string
         | CompilationError of CompilationError.t
         | InternalError of string
         | GeneralError of string

type 'a res = (t list, 'a) Either.t

fun json_err x = JsonError x
fun parser_err x = ParsingError x
fun comp_err x = CompilationError x
fun lift_err x = x |> Library.single |> Either.fail
fun lift_comp_err x = x |> comp_err |> lift_err
fun lift_naming_err x = x |> CompilationError.naming |> lift_comp_err
fun lift_lang_err x = x |> CompilationError.constr_err |> lift_comp_err

fun json_err_test p x =
    case x of
        (JsonError x') => p x' |
        _ => false
fun json_err_not_in x = json_err_test JsonError.is_notinobj x
fun json_err_wrong_ty x = json_err_test JsonError.is_wrongtype x
fun is_parsing_err x =
    case x of
        (ParsingError _) => true |
        _ => false
fun is_comp_err x =
    case x of
        (CompilationError _) => true |
        _ => false
val internal_err = InternalError

fun err_msg msg = "Error: " ^ msg ^ "\n"
fun print_err_msg msg = err_msg msg |> print

fun map_err json_f parse_f comp_f internal_f general_f error =
    case error of
        JsonError errs => json_f errs |
        ParsingError errs => parse_f errs |
        CompilationError errs => comp_f errs |
        InternalError msg => internal_f msg |
        GeneralError msg => general_f msg

fun print_err error =
    map_err (JsonError.print_err print_err_msg)
            print_err_msg
            (CompilationError.print_err print_err_msg)
            (fn msg => (print "Internal"; print_err_msg msg))
            print_err_msg
            error

fun err_to_str error =
    map_err (JsonError.print_err err_msg) err_msg
            (CompilationError.print_err err_msg)
            (fn msg => err_msg ("Internal Error" ^ msg))
            id
            error
end
