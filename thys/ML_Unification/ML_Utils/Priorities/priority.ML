signature PRIO = sig
  type prio = int

  val VERY_LOW : prio
  val LOW : prio
  val MEDIUM : prio
  val HIGH : prio
  val VERY_HIGH : prio

  val eq : prio * prio -> bool
  val ord : prio ord

  structure Table : TABLE

  val parse : prio context_parser
  val pretty : prio -> Pretty.T

end

structure Prio : PRIO =
struct

type prio = int

val VERY_LOW = ~2000
val LOW = ~1000
val MEDIUM = 0
val HIGH = 1000
val VERY_HIGH = 2000

val eq = (op =)
val ord = int_ord o swap

structure Table = Table(type key = prio; val ord = ord)

val pretty = Pretty.str o string_of_int
val parse = Parse_Util.ML_int (K "priority may not be empty")

end