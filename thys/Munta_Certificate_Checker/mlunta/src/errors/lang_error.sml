(* XXX: rename everywhere to lang_err *)
signature CONSTRAINT_ERROR = sig
  type t
  val var_invar: string -> t              (* bexps *)
  val disj: string -> string -> t (* bexps *)
  val true_in_formula: t        (* bexps *)
  val diff_in_formula: string -> string -> t
  val clock_in_formula: string -> t (* bexps *)
  val broadcast_is_internal: string * string -> t
  val no_clocks: t
  val clock_and_var: string -> string -> t
  val print_err: (string -> 'a) -> t -> 'a
end

structure LangError : CONSTRAINT_ERROR = struct
datatype t =
         VarInInvar of string |
         BroadcastInternal of string * string |
         DisjunctionNotVar of string * string |
         DiffInFormula of string * string |
         TrueInFormula |
         ClockAndVar of string * string |
         ClockInFormular of string |
         NoClocks

fun diff_in_formula l r = DiffInFormula (l, r)
fun clock_in_formula x = ClockInFormular x
fun clock_and_var x y = ClockAndVar (x, y)
val true_in_formula = TrueInFormula

fun disj g constr = DisjunctionNotVar (g, constr)
fun broadcast_is_internal (src, dst) = BroadcastInternal (src, dst)
fun var_invar x = VarInInvar x

val no_clocks = NoClocks
fun print_err logf error =
    let
      val msg =
          case error of
              DisjunctionNotVar (g, constr) => "There is a Disjunction of a clock"
                                               ^ " constraint in the guard:\n"
                                               ^ g ^ "\n"
                                               ^ "Clock Constraint: "
                                               ^ constr |
              BroadcastInternal (src, dst) => "An internal edge from id: "
                                              ^ src ^
                                              " to id: "
                                              ^ dst ^
                                              "uses a broadcast label!" |
              ClockAndVar (x, y) => "Update or Constraint use variable "
                                    ^ "and clock: " ^ x ^ ", " ^ y |
              DiffInFormula (x, y) => "Formula contains a diff of: " ^ x
                                      ^ " and " ^ y |
              TrueInFormula => "True inside of Formula" |
              ClockInFormular name => "Clock: " ^ name ^ " inside of formula" |
              VarInInvar x => "Variable: "
                              ^ x ^ " is referenced in an invariant" |
              NoClocks => "The number of clocks in the Network must be > than 0"

    in
      logf msg
    end
end
