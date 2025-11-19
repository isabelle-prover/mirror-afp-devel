(*  Title:      ML_Utils/cost_priority.ML
    Author:     Kevin Kappelmann
*)
signature COST =
sig
  type cost

  val eq : cost * cost -> bool
  val ord : cost ord
  val pretty : cost -> Pretty.T

  val add : cost * cost -> cost
  val between : cost * cost -> cost
  val halve : cost -> cost
  val scale : Rat.rat -> cost -> cost
  val double : cost -> cost

  (*in ascending order*)
  val VERY_LOW : cost
  val VERY_LOW1 : cost
  val VERY_LOW2 : cost
  val VERY_LOW3 : cost
  val VERY_LOW4 : cost
  val VERY_LOW5 : cost
  val LOW : cost
  val LOW1 : cost
  val LOW2 : cost
  val LOW3 : cost
  val LOW4 : cost
  val LOW5 : cost
  val MEDIUM : cost
  val MEDIUM1 : cost
  val MEDIUM2 : cost
  val MEDIUM3 : cost
  val MEDIUM4 : cost
  val MEDIUM5 : cost
  val HIGH : cost
  val HIGH1 : cost
  val HIGH2 : cost
  val HIGH3 : cost
  val HIGH4 : cost
  val HIGH5 : cost
  val VERY_HIGH : cost
end

signature PRIO =
sig
  type prio

  val eq : prio * prio -> bool
  val ord : prio ord
  val pretty : prio -> Pretty.T

  val between : prio * prio -> prio
  val halve : prio -> prio
  val scale : Rat.rat -> prio -> prio
  val double : prio -> prio

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
end

signature COST_PRIO =
sig
  structure Cost : COST
  structure Prio : PRIO
  val cost_from_prio : Prio.prio -> Cost.cost
  val prio_from_cost : Cost.cost -> Prio.prio
end

structure Cost_Prio : COST_PRIO =
struct

val zero_rat = Rat.of_int 0
val one_rat = Rat.of_int 1
val two_rat = Rat.of_int 2

structure Prio =
struct
  datatype prio = Prio of Rat.rat

  fun dest_prio (Prio prio) = prio

  val eq = (op =)
  val ord = Rat.ord o apply2 dest_prio
  val pretty = Pretty.str o Rat.string_of_rat o dest_prio

  val BOTTOM_EXCLUSIVE = Prio zero_rat

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
        val below = map_range (fn i => funpow (i + 1) (fn p => between (init, p)) mid) n
        val above = map_range (fn i => funpow (i + 1) (fn p => between (p, next)) mid) n
      in rev below @ (mid :: above) end
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
end

structure Cost =
struct
  datatype cost = Cost of Rat.rat
  fun dest_cost (Cost cost) = cost

  val eq = (op =)
  val ord = Rat.ord o apply2 dest_cost
  val pretty = Pretty.str o Rat.string_of_rat o dest_cost

  fun from_prio (Prio.Prio prio) = Cost (one_rat / prio)

  fun add (Cost c1, Cost c2) = Cost (c1 + c2)
  val BOTTOM_EXCLUSIVE = Cost zero_rat
  fun between (c1, c2) = Cost ((dest_cost c1 + dest_cost c2) / two_rat)
  (*assumption: BOTTOM_EXCLUSIVE = 0*)
  fun halve c = between (BOTTOM_EXCLUSIVE, c)
  fun scale r c = Cost (dest_cost c * r)
  val double = scale two_rat

  val [VERY_LOW, VERY_LOW1, VERY_LOW2, VERY_LOW3, VERY_LOW4, VERY_LOW5,
    LOW, LOW1, LOW2, LOW3, LOW4, LOW5,
    MEDIUM, MEDIUM1, MEDIUM2, MEDIUM3, MEDIUM4, MEDIUM5,
    HIGH, HIGH1, HIGH2, HIGH3, HIGH4, HIGH5,
    VERY_HIGH
  ] = map from_prio [
    Prio.VERY_HIGH, Prio.HIGH5, Prio.HIGH4, Prio.HIGH3, Prio.HIGH2, Prio.HIGH1,
    Prio.HIGH, Prio.MEDIUM5, Prio.MEDIUM4, Prio.MEDIUM3, Prio.MEDIUM2, Prio.MEDIUM1,
    Prio.MEDIUM, Prio.LOW5, Prio.LOW4, Prio.LOW3, Prio.LOW2, Prio.LOW1,
    Prio.LOW, Prio.VERY_LOW5, Prio.VERY_LOW4, Prio.VERY_LOW3, Prio.VERY_LOW2, Prio.VERY_LOW1,
    Prio.VERY_LOW]
end

val cost_from_prio = Cost.from_prio
fun prio_from_cost (Cost.Cost cost) = Prio.Prio (one_rat / cost)

local
open Prio
val prios =
  [VERY_LOW, VERY_LOW1, VERY_LOW2, VERY_LOW3, VERY_LOW4, VERY_LOW5,
  LOW, LOW1, LOW2, LOW3, LOW4, LOW5,
  MEDIUM, MEDIUM1, MEDIUM2, MEDIUM3, MEDIUM4, MEDIUM5,
  HIGH, HIGH1, HIGH2, HIGH3, HIGH4, HIGH5,
  VERY_HIGH]
open Cost
val costs =
  [VERY_LOW, VERY_LOW1, VERY_LOW2, VERY_LOW3, VERY_LOW4, VERY_LOW5,
  LOW, LOW1, LOW2, LOW3, LOW4, LOW5,
  MEDIUM, MEDIUM1, MEDIUM2, MEDIUM3, MEDIUM4, MEDIUM5,
  HIGH, HIGH1, HIGH2, HIGH3, HIGH4, HIGH5,
  VERY_HIGH]
in
val _ = @{assert} (map prio_from_cost costs = rev prios)
val _ = @{assert} (map cost_from_prio prios = rev costs)
end

end

structure Cost :
  sig
    include COST
    structure Internal_Data : GENERIC_DATA
    val parse : cost context_parser
  end =
struct
open Cost_Prio.Cost
structure Internal_Data = Generic_Data( type T = cost; val empty = MEDIUM; val merge = fst)
val parse =
  let
    fun cost_from_code ((code, ctxt), pos) =
      let val put_code = ML_Code_Util.read "Cost.Internal_Data.put"
        @ ML_Code_Util.atomic code
      in
        Context.Proof ctxt
        |> ML_Attribute_Util.attribute_map_context (ML_Attribute.run_map_context (put_code, pos))
        |> Internal_Data.get
      end
    val empty_msg_of = K "cost may not be empty"
  in
    ((Scan.lift (Parse_Util.nonempty_code empty_msg_of) -- Args.context |> Parse_Util.position')
      >> cost_from_code)
  end
end

structure Prio :
  sig
    include PRIO
    structure Internal_Data : GENERIC_DATA
    val parse : prio context_parser
  end =
struct
open Cost_Prio.Prio
structure Internal_Data = Generic_Data( type T = prio; val empty = MEDIUM; val merge = fst)
val parse =
  let
    fun prio_from_code ((code, ctxt), pos) =
      let val put_code = ML_Code_Util.read "Prio.Internal_Data.put"
        @ ML_Code_Util.atomic code
      in
        Context.Proof ctxt
        |> ML_Attribute_Util.attribute_map_context (ML_Attribute.run_map_context (put_code, pos))
        |> Internal_Data.get
      end
    val empty_msg_of = K "prio may not be empty"
  in
    ((Scan.lift (Parse_Util.nonempty_code empty_msg_of) -- Args.context |> Parse_Util.position')
      >> prio_from_code)
  end
end
