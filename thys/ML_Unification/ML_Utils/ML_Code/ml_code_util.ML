(*  Title:      ML_Utils/ml_code_util.ML
    Author:     Kevin Kappelmann

Utilities to create and manipulate parsed ML code.
*)
signature ML_CODE_UTIL =
sig
  (*returns a name variant that ought to avoid name shadowing*)
  val internal_name : string -> string
  val spaces : string list -> string

  (*type of parsed ML code*)
  type code = ML_Lex.token Antiquote.antiquote list

  val parse_code : code parser

  val flat : code list -> code
  val read : string -> code
  val flat_read : string list -> code
  val reads : string list -> code

  val commas : code list -> code

  val enclose : code -> code -> code -> code
  val atomic : code -> code
  val tuple : code list -> code
  val list : code list -> code
  val record : code -> (code * code) list -> code

end

structure ML_Code_Util : ML_CODE_UTIL =
struct

val internal_name = prefix "INTERNAL___"
val spaces = space_implode " "

type code = ML_Lex.token Antiquote.antiquote list

val parse_code = Parse.embedded_ml

val flat = flat
val read = ML_Lex.read
val flat_read = String.concat #> read
val reads = map read #> flat
val commas = separate (read ",") #> flat

fun enclose start close code = flat [start, code, close]
val atomic = enclose (read "(") (read ")")
val tuple = commas #> enclose (read "(") (read ")")
val list = commas #> enclose (read "[") (read "]")
fun record delim = map (fn (v, t) => v @ delim @ t)
  #> commas #> enclose (read "{") (read "}")

end
