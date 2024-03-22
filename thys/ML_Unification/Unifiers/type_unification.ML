(*  Title:      ML_Unification/type_unification.ML
    Author:     Kevin Kappelmann
*)
signature TYPE_UNIFICATION =
sig
  include HAS_LOGGER

  (*matches/unifies types of given terms and passes unification problem with updated environment
  to the fallback matcher/unifier*)
  val e_match : Unification_Base.type_matcher -> Unification_Base.e_matcher
  val e_unify : Unification_Base.type_unifier -> Unification_Base.e_unifier
end

structure Type_Unification : TYPE_UNIFICATION =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Type_Unification"

structure Norm = Envir_Normalisation
structure Util = Unification_Util

fun e_match match_types match_theory binders ctxt (pt as (p, t)) env =
  let val binder_types = Binders.binder_types binders
  in
    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Matching types of ",
        Util.pretty_unif_problem ctxt pt
      ] |> Pretty.string_of);
    match_types ctxt (Envir.fastype env binder_types p, fastype_of1 (binder_types, t)) env
    |> match_theory binders ctxt pt)
    handle Unification_Base.UNIF => Seq.empty
  end

fun e_unify unif_types unif_theory binders ctxt st env =
  let val binder_types = Binders.binder_types binders
  in
    (@{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Pretty.str "Unifying types of ",
        Util.pretty_unif_problem ctxt (apply2 (Norm.norm_term_unif env) st)
      ]
      |> Pretty.string_of);
    unif_types ctxt (apply2 (Envir.fastype env binder_types) st) env
    |> unif_theory binders ctxt st)
    handle Unification_Base.UNIF => Seq.empty
  end

end
