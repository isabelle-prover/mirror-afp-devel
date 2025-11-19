(*  Title:      Zippy/zippy_identifier.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_IDENTIFIER =
sig
  type id = binding
  val make : Position.T option -> bstring -> id
  val eq : id * id -> bool
  val ord : id ord
  val pretty : id -> Pretty.T
  val quoted_string : id -> string
  val prefix_name : Position.T option -> string -> id -> id
  val suffix_name : Position.T option -> string -> id -> id
end

structure Zippy_Identifier : ZIPPY_IDENTIFIER  =
struct

type id = binding
val make = Binding.make oo rpair o the_default Position.none
val string_of = Binding.long_name_of
val eq = apply2 string_of #> (op =)
val ord = apply2 string_of #> fast_string_ord
val pretty = Binding.pretty
val quoted_string = Binding.print

fun prefix_name opt_pos s = Binding.prefix_name s
  #> (Option.map Binding.set_pos opt_pos |> the_default I)
fun suffix_name opt_pos s = Binding.suffix_name s
  #> (Option.map Binding.set_pos opt_pos |> the_default I)

end
