(*  Title:      ML_Unification/unify_THEN_base.ML
    Author:     Kevin Kappelmann

THEN attribute with adjustable unifier.
*)
signature UNIFY_THEN_BASE =
sig
  val unify_THEN : ('a -> 'b -> thm -> Proof.context -> int -> tactic) ->
    'a -> 'b -> int -> thm -> Proof.context -> thm -> thm option
  val unify_THEN_attribute : ('a -> 'b -> thm -> Proof.context -> int -> tactic) ->
    'a -> 'b -> int -> thm -> attribute
end

structure Unify_THEN_Base : UNIFY_THEN_BASE =
struct

fun unify_THEN f norms unify i thm ctxt arg_thm = SINGLE (f norms unify arg_thm ctxt i) thm

fun unify_THEN_attribute f norms unify i thm = Thm.rule_attribute []
  (fn context => fn arg_thm =>
    unify_THEN f norms unify i thm (Context.proof_of context) arg_thm
    |> (fn SOME thm => thm | _ => raise THM ("unify_THEN: no unifiers", i, [thm, arg_thm])))

end