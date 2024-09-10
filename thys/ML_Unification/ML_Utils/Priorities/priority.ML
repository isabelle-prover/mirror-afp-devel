(*  Title:      ML_Utils/priority.ML
    Author:     Kevin Kappelmann
*)
signature PRIO =
sig
  type prio

  val VERY_LOW : prio
  val LOW : prio
  val MEDIUM : prio
  val HIGH : prio
  val VERY_HIGH : prio

  val eq : prio * prio -> bool
  val ord : prio ord

  val between : prio * prio -> prio
  val halve : prio -> prio

  val inc : prio -> prio
  val dec : prio -> prio

  structure Table : TABLE
  where type key = prio

  val pretty : prio -> Pretty.T

  structure Internal_Prio_Data : GENERIC_DATA
  val parse : prio context_parser

end

structure Prio : PRIO =
struct

datatype prio = Prio of Rat.rat

fun dest_prio (Prio prio) = prio

val eq = (op =)
val ord = Rat.ord o apply2 dest_prio

val two_rat = Rat.of_int 2

val BOTTOM_EXCLUSIVE = Prio (Rat.of_int 0)
val VERY_LOW = Prio (Rat.of_int 1)
val LOW = Prio (dest_prio VERY_LOW * two_rat)
val MEDIUM = Prio (dest_prio LOW * two_rat)
val HIGH = Prio (dest_prio MEDIUM * two_rat)
val VERY_HIGH = Prio (dest_prio HIGH * two_rat)

fun between (p1, p2) = Prio ((dest_prio p1 + dest_prio p2) / two_rat)
fun halve p = between (BOTTOM_EXCLUSIVE, p)

val epsilon = Rat.make (1, 100)
fun inc p = Prio (dest_prio p + epsilon)
fun dec p = let val r = dest_prio p in if r <= epsilon then halve p else Prio (r - epsilon) end

structure Table = Table(type key = prio; val ord = rev_order o ord)

val pretty = Pretty.str o Rat.string_of_rat o dest_prio

structure Internal_Prio_Data = Generic_Data( type T = prio; val empty = MEDIUM; val merge = fst)

val parse =
  let
    fun prio_from_code ((code, ctxt), pos) =
      let val put_int_code = ML_Code_Util.read "Prio.Internal_Prio_Data.put"
        @ ML_Code_Util.atomic code
      in
        Context.Proof ctxt
        |> ML_Attribute_Util.attribute_map_context (ML_Attribute.run_map_context (put_int_code, pos))
        |> Internal_Prio_Data.get
      end
    val empty_msg_of = K "priority may not be empty"
  in
    ((Scan.lift (Parse_Util.nonempty_code empty_msg_of) -- Args.context |> Parse_Util.position')
      >> prio_from_code)
  end

end