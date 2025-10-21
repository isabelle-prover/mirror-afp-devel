signature PARSER_UTIL = sig
  type error_msg = string
  val safe_scan: error_msg -> ('a Symbol.parser) -> string ->
                 'a Error.res
  val safe_default: error_msg -> 'a -> ('a Symbol.parser) -> string ->
                    'a Error.res
end

structure ParserUtil : PARSER_UTIL = struct
type error_msg = string
fun perr ty xs =
    ("Syntax Error in the " ^ ty ^ ": " ^ String.concat xs ^ "\n")
    |> Error.parser_err
    |> Library.single
    |> Either.fail

fun handle_error err (p : 'a Symbol.parser) xs  =
      Scan.recover (Either.succeed o Scan.error p) (K err) xs
      |> Either.bindR (fn (res, []) => Either.succeed res |
                           _        => err xs |> Either.mapR fst)

fun handle_empty default p xs =
    case xs of
        [] => (default, []) |
        _ => p xs

fun safe_scan' ty p s =
    s
    |> Symbol.explode
    |> handle_error (perr ty) p

fun safe_default' ty default p =
    safe_scan' ty (handle_empty default p)

fun safe_scan ty p =
    safe_scan' ty (Symbol.scan_finite p)

fun safe_default ty default p =
    safe_default' ty default (Symbol.scan_finite p)
end
