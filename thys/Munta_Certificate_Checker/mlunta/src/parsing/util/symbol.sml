(* inspired by Isabelle Pure/General/symbol.sml *)
structure Symbol = struct
type symbol = string
type 'a parser = symbol list -> 'a * symbol list
fun is_char s = size s = 1
val eof = "";
fun is_eof s = s = eof;
fun not_eof s = s <> eof;
fun explode s = s |> String.explode |> map Char.toString
fun implode s = s |> String.concat
exception Ord
fun ord s =
    if String.size s = 0
    then raise Ord
    else Char.ord(String.sub(s, 0))

fun is p s =
    is_char s andalso String.substring (s, 0, 1) |> p

val is_letter =
    is (fn s => Char.ord #"A" <= ord s andalso ord s <= Char.ord #"Z" orelse
                Char.ord #"a" <= ord s andalso ord s <= Char.ord #"z")

val is_digit =
    is (fn s => Char.ord #"0" <= ord s andalso ord s <= Char.ord #"9")

val is_letter_digit =
    is_letter orf is_digit

val is_quasi =
    is (fn "'" => true | "_" => true | _ => false)

fun is_wsp s =
    is (fn " " => true
       | "\t" => true
       | "\n" => true
       | _ => false) s

val is_identifier = is_letter_digit orf is_quasi

local
  open Scan
in

val natural =
    Scan.many1 is_digit >> (implode #> Int.fromString #> the)

val scan_sign = $$ "-" >> K (~1)

val integer =
    Scan.optional (scan_sign) 1 -- natural >> op *

val scan_nat =
    Scan.many1 is_digit >> implode

val scan_integer =
    (Scan.optional ($$ "-") "") -- scan_nat >> (op ^)

fun to_real x =
    case Real.fromString x of
        NONE => Scan.fail () |
        SOME x => x

val real = scan_integer -- $$ "." -- scan_nat >>
                   (fn ((l, dot),r) => l ^ dot ^ r |> to_real)

val string = $$ "\\\"" |--
                Scan.optional (Scan.many (fn "\\\"" => false | _ => true)) []
                --| $$ "\\\"" >> String.concat

val stopper = Scan.stopper (K eof) is_eof
fun scan_finite p = Scan.finite stopper p

fun scan_pred p =
    (many1 p) >> implode

val whitespace = Scan.many is_wsp
val optional_whitespace = Scan.optional whitespace []

fun strip_whitespace p =
    optional_whitespace |-- p --| optional_whitespace

val identifier = scan_pred is_identifier

val only_identifier =
    strip_whitespace identifier

end
end
