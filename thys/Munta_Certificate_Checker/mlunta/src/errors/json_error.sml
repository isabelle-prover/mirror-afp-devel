structure JsonError = struct
datatype t =
         WrongType of string * string
         | NotInObject of string
fun wrong_type k s = WrongType (k, s)
fun not_in_obj x = NotInObject x
fun is_notinobj x =
    case x of
        (NotInObject _ ) => true |
        _ => false
fun is_wrongtype x = is_notinobj x |> not

fun print_err logf error =
    case error of
        WrongType (k, t) => "Key :" ^ k ^ " is not of type " ^ t |> logf |
        NotInObject k => "Key :" ^ k ^ "is not in the json object" |> logf
end
