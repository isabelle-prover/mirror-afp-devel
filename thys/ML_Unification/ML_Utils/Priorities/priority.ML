(*  Title:      ML_Utils/priority.ML
    Author:     Kevin Kappelmann
*)
signature PRIO =
sig
  type prio

  (*in ascending order*)
  val VERY_LOW : prio
  val VERY_LOW1 : prio
  val VERY_LOW2 : prio
  val VERY_LOW3 : prio
  val VERY_LOW4 : prio
  val VERY_LOW5 : prio
  val LOW : prio
  val LOW1 : prio
  val LOW2 : prio
  val LOW3 : prio
  val LOW4 : prio
  val LOW5 : prio
  val MEDIUM : prio
  val MEDIUM1 : prio
  val MEDIUM2 : prio
  val MEDIUM3 : prio
  val MEDIUM4 : prio
  val MEDIUM5 : prio
  val HIGH : prio
  val HIGH1 : prio
  val HIGH2 : prio
  val HIGH3 : prio
  val HIGH4 : prio
  val HIGH5 : prio
  val VERY_HIGH : prio

  val eq : prio * prio -> bool
  val ord : prio ord

  val between : prio * prio -> prio
  val halve : prio -> prio
  val scale : Rat.rat -> prio -> prio
  val double : prio -> prio

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

fun between (p1, p2) = Prio ((dest_prio p1 + dest_prio p2) / two_rat)
(*assumption: BOTTOM_EXCLUSIVE = 0*)
fun halve p = between (BOTTOM_EXCLUSIVE, p)
fun scale r p = Prio (dest_prio p * r)
val double = scale two_rat

local
  fun mk_steps init next =
    let
      val n = 2
      val mid = between (init, next)
      val below = map_range (fn i => funpow i (fn p => between (init, p)) mid) n
      val above = map_range (fn i => funpow i (fn p => between (p, next)) mid) n
    in below @ (mid :: above) end
in
val VERY_LOW = Prio (Rat.of_int 1)
val LOW = double VERY_LOW
val MEDIUM = double LOW
val HIGH = double MEDIUM
val VERY_HIGH = double HIGH

val [VERY_LOW1, VERY_LOW2, VERY_LOW3, VERY_LOW4, VERY_LOW5] = mk_steps VERY_LOW LOW
val [LOW1, LOW2, LOW3, LOW4, LOW5] = mk_steps LOW MEDIUM
val [MEDIUM1, MEDIUM2, MEDIUM3, MEDIUM4, MEDIUM5] = mk_steps MEDIUM HIGH
val [HIGH1, HIGH2, HIGH3, HIGH4, HIGH5] = mk_steps HIGH VERY_HIGH
end

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
