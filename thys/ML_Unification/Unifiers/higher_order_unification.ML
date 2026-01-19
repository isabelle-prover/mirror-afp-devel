(*  Title:      ML_Unification/higher_order_unification.ML
    Author:     Kevin Kappelmann TU Muenchen

Higher-order unification from the Pure kernel adjusted to fit the
Unification_Base.unifier type, i.e. moving flex-flex pairs into the theorem
and support of open term unification.
*)

signature HIGHER_ORDER_UNIFICATION =
sig
  include HAS_LOGGER

  val ho_unifiers : term Binders.binders -> Proof.context -> term * term -> Envir.env ->
    (Envir.env * (term * term) list) Seq.seq
  val unify : Unification_Base.unifier
  val norms_unify : Unification_Base.normalisers
end

structure Higher_Order_Unification : HIGHER_ORDER_UNIFICATION =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Higher_Order_Unification"

structure Util = Unification_Util

val norms_unify = Unification_Util.beta_eta_short_norms_unif
fun ho_unifiers binders ctxt tp env =
  Unify.hounifiers (map fst binders) (Context.Proof ctxt, env, [tp])
fun unify binders ctxt tp env = Seq.make (fn _ =>
  let
    val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Higher-order unifying ",
        Util.pretty_unif_problem binders ctxt
          (apply2 (Same.commit (Envir_Normalisation.beta_norm_term_unif env)) tp)
      ] |> Pretty.string_of)
    val init_goal = Logic.mk_equals #> Thm.cterm_of ctxt #> Goal.init
    fun create_env_thmq env = tp
      (*replace binders and apply the computed unifier*)
      |> apply2 (Binders.replace_binders binders
        #> Same.commit (Util.inst_norm_term' norms_unify env))
      (*create a goal such that we can create a theorem including the flex-flex pairs*)
      |> init_goal
      (*kind of a hack: resolving against the equality theorem will add the
        flex-flex pairs to the theorem*)
      |> HEADGOAL (match_tac ctxt @{thms Pure.reflexive})
      (*conclude the goal and pair with the environment*)
      |> Seq.map (pair env o Goal.conclude)
  in
    (*find the unifiers*)
    ho_unifiers binders ctxt tp env
    (*add the flex-flex pairs to the theorem*)
    |> Seq.maps (fst #> create_env_thmq)
    |> Seq.pull
    |> (fn res => (if is_none res
      then @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Higher-order unification failed."
      ] |> Pretty.string_of)
      else (); res))
  end)

end

