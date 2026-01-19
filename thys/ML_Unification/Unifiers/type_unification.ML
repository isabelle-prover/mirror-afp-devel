(*  Title:      ML_Unification/type_unification.ML
    Author:     Kevin Kappelmann
*)
signature TYPE_UNIFICATION =
sig
  include HAS_LOGGER

  (*matches/unifies types of given terms and passes unification problem with updated environment
  to the passed matcher/unifier*)
  val e_match : Unification_Base.type_matcher -> Unification_Base.matcher ->
    Unification_Base.matcher
  val e_unify : Unification_Base.type_unifier -> Unification_Base.unifier ->
    Unification_Base.unifier
end

structure Type_Unification : TYPE_UNIFICATION =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Type_Unification"

structure Norm = Envir_Normalisation
structure Util = Unification_Util

fun e_match match_types match binders ctxt (pt as (p, t)) env = Seq.make (fn _ =>
  let val binder_types = Binders.binder_types binders
  in
    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Matching types of ",
        Util.pretty_unif_problem binders ctxt (apfst (Same.commit (Norm.norm_term_match env)) pt)
      ] |> Pretty.string_of);
    match_types ctxt (Envir.fastype env binder_types p, fastype_of1 (binder_types, t)) env
    |> match binders ctxt pt)
    |> Seq.pull
    handle Unification_Base.UNIF => NONE
  end)

fun e_unify unif_types unif binders ctxt st env = Seq.make (fn _ =>
  let val binder_types = Binders.binder_types binders
  in
    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Unifying types of ",
        Util.pretty_unif_problem binders ctxt (apply2 (Same.commit (Norm.norm_term_unif env)) st)
      ] |> Pretty.string_of);
    unif_types ctxt (apply2 (Envir.fastype env binder_types) st) env
    |> unif binders ctxt st)
    |> Seq.pull
    handle Unification_Base.UNIF => NONE
  end)

end
