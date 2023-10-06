(*  Title:      ML_Unification/higher_order_unification.ML
    Author:     Kevin Kappelmann TU Muenchen

Higher-order unification from the Pure kernel adjusted to fit the
Unification_Base.unifier type, i.e. moving flex-flex pairs into the theorem
and support of open term unification.
*)

signature HIGHER_ORDER_UNIFICATION =
sig
  include HAS_LOGGER

  val unify : Unification_Base.unifier
  val norms : Unification_Base.normalisers
end

structure Higher_Order_Unification : HIGHER_ORDER_UNIFICATION =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Higher_Order_Unification"

structure Util = Unification_Util

fun unify binders ctxt tp env =
  let
    fun unif env =
      let
        val init_goal = Logic.mk_equals #> Thm.cterm_of ctxt #> Goal.init
        fun create_env_thmq env =
          (*replace binders and apply the computed unifier*)
          apply2 (Envir_Normalisation.beta_eta_short_norm_term_unif env o Binders.replace_binders binders) tp
          (*create a goal such that we can create a theorem including the flex-flex pairs*)
          |> init_goal
          (*kind of a hack: resolving against the equality theorem will add the
            flex-flex pairs to the theorem*)
          |> HEADGOAL (match_tac ctxt @{thms Pure.reflexive})
          (*conclude the goal and pair with the environment*)
          |> Seq.map (pair env o Goal.conclude)
      in
        (*find the unifiers*)
        Unify_Copy.hounifiers (map fst binders) (Context.Proof ctxt, env, [tp])
        (*FIXME: replace above line by the following one for the next Isabelle release*)
        (*Unify.hounifiers (map fst binders) (Context.Proof ctxt, env, [tp])*)
        (*add the flex-flex pairs to the theorem*)
        |> Seq.maps (create_env_thmq o fst)
      end
  in
    ((@{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Pretty.str "Higher-order unifying ",
        Util.pretty_unif_problem ctxt (apply2 (Envir.norm_term env) tp)
      ]
      |> Pretty.string_of);
    unif (Util.unify_types ctxt (apply2 Term.fastype_of tp) env))
    handle Unification_Base.UNIF => Seq.empty) (*types do not match*)
  end

val norms = Unification_Util.beta_eta_short_norms_unif

end

