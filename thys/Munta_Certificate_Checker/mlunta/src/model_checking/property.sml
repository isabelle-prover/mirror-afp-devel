structure Property = struct
datatype 'a result =
         Satisfied of 'a |
         Unsatisfied of 'a

fun convert prop =
    case prop of
        Satisfied r => Unsatisfied r
      | Unsatisfied r => Satisfied r

fun result prop =
    case prop of
        Satisfied x => x |
        Unsatisfied x => x

fun map f p =
    case p of
        Satisfied x => Satisfied (f x) |
        Unsatisfied x => Unsatisfied (f x)

fun to_string p =
    case p of
        Satisfied _ => "Satisfied" |
        Unsatisfied _ => "Unsatisfied"

type sat = unit result
val sat = Satisfied ()
val unsat = Unsatisfied ()
fun just_prop x = x |> map (K ())
end
