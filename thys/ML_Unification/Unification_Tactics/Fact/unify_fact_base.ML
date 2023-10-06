(*  Title:      ML_Unification/unify_fact_base.ML
    Author:     Kevin Kappelmann

Fact tactic with adjustable unifier.
*)
signature UNIFY_FACT_BASE =
sig
  val unify_fact_tac : Unification_Base.normalisers -> Unification_Base.unifier ->
    thm list -> Proof.context -> int -> tactic
end

structure Unify_Fact_Base : UNIFY_FACT_BASE =
struct

val unify_fact_tac = Unify_Resolve_Base.unify_resolve_atomic_any_tac

end