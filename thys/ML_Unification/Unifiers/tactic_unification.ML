(*  Title:      ML_Unification/tactic_unification.ML
    Author:     Kevin Kappelmann

Solving equations for unification problems with environment-aware tactics.
*)
signature TACTIC_UNIFICATION =
sig
  include HAS_LOGGER

  type env_tactic = Envir.env * thm -> (Envir.env * thm) Seq.seq
  val tac_from_env_tac : env_tactic -> Envir.env -> tactic
  val tac_from_env_tac' : env_tactic -> tactic
  (*create environment-aware tactic from a tactic that *DOES NOT* instantiate meta variables*)
  val env_tac_from_no_inst_tac : (int -> tactic) -> int -> env_tactic

  (*rewrite a subgoal given an equality theorem and environment for the subgoal's conclusion*)
  val rewrite_subgoal_eq_concl_env_tac : Envir_Normalisation.term_normaliser ->
    (int -> Envir_Normalisation.thm_normaliser) -> Envir_Normalisation.thm_normaliser ->
    term Binders.binders -> thm -> Proof.context -> int -> env_tactic
  (*finish a subgoal given the theorem's conclusion as a theorem with environment*)
  val finish_subgoal_concl_env_tac : Envir_Normalisation.term_normaliser ->
    (int -> Envir_Normalisation.thm_normaliser) -> Envir_Normalisation.thm_normaliser ->
    term Binders.binders -> thm -> Proof.context -> int -> env_tactic

  (*solves subgoal "lhs \<equiv> rhs" by unification*)
  val unify_eq_env_tac : Unification_Base.normalisers -> Unification_Base.unifier ->
    term Binders.binders -> Proof.context -> int -> env_tactic

  val unify : Envir_Normalisation.term_normaliser -> (term * term -> int -> env_tactic) ->
    Unification_Base.unifier
end

structure Tactic_Unification : TACTIC_UNIFICATION =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Tactic_Unification"

type env_tactic = Envir.env * thm -> (Envir.env * thm) Seq.seq
fun tac_from_env_tac env_tac env state = env_tac (env, state) |> Seq.map snd
fun tac_from_env_tac' env_tac state = tac_from_env_tac env_tac
  (Envir.empty (Thm.maxidx_of state)) state
fun env_tac_from_no_inst_tac tac i (env, state) = tac i state |> Seq.map (pair env)

fun subgoal_concl_env_tac mk_subgoal_thm subgoal_tac inst_binders norm_state norm_concl_thm
  binders concl_thm ctxt i (env, state) =
  let
    (*updates binders with their normalised type*)
    fun normed_binders env = Binders.norm_binders (inst_binders env) binders
    val binders = normed_binders env
    val smash_tpairs_if_occurs = Seq.maps o Unification_Util.smash_tpairs_if_occurs ctxt
    fun env_concl_tac env concl_thm state =
      let
        val binders = normed_binders env
        val cterm_of = Thm.cterm_of ctxt
        val cprems = Term_Util.strip_nth_subgoal i state |> snd |> fst
          |> map (cterm_of o Binders.replace_binders binders)
      in
        (norm_concl_thm ctxt env concl_thm
        |> mk_subgoal_thm (map (apsnd cterm_of) binders) cprems ctxt
        |> Option.map (subgoal_tac env)
        |> \<^if_none>\<open>K (K Seq.empty)\<close>) i state
      end
  in
    (*smash tpairs in case some binder occurs*)
    fold (smash_tpairs_if_occurs o snd) binders (Seq.single (env, concl_thm))
    |> Seq.maps (fn (env, concl_thm) => PRIMITIVE (norm_state i ctxt env) state
      |> Seq.maps (env_concl_tac env concl_thm))
  end

val rewrite_subgoal_eq_concl_env_tac = subgoal_concl_env_tac Thm_Util.eq_subgoal_from_eq_concl
  (fn env => Seq.map (pair env) ooo Tactic_Util.rewrite_subgoal_tac)
val finish_subgoal_concl_env_tac = subgoal_concl_env_tac Thm_Util.subgoal_thm_from_concl_thm
  (fn env => fn thm => fn i => Seq.map (pair env) o
    PRIMITIVE (Drule.with_subgoal i (Thm.elim_implies thm)))

fun unify_eq_env_tac norms unify binders ctxt i (env, state) =
  case try (Term_Util.strip_nth_subgoal i #> apsnd (snd #> Logic.dest_equals)) state of
    NONE => Seq.empty
  | SOME (params, tp) => let val (subgoal_binders, ctxt) = Binders.fix_binders params ctxt
      in
        unify (Binders.add_binders subgoal_binders binders) ctxt tp env
        |> Seq.maps (fn (env, thm) => finish_subgoal_concl_env_tac (#inst_term norms)
          (Unification_Util.inst_norm_subgoal (#inst_thm norms) (#conv norms))
          (Unification_Util.inst_norm_thm (#inst_unif_thm norms) (#conv norms))
          subgoal_binders thm ctxt i (env, state))
      end

fun unify normt tac binders ctxt (tp as (lhs, rhs)) env = Seq.make (fn _ =>
  let
    val rev_binders = rev binders
    fun forall_elim (env, state) = Binders.norm_binders (normt env) rev_binders
      |> map (snd #> Thm.cterm_of ctxt)
      |> (fn binders => Drule.forall_elim_list binders state)
      |> pair env
  in
    (Term_Util.mk_equals binders tp
    |> curry Logic.list_all (map fst rev_binders)
    |> Thm.cterm_of ctxt
    |> Goal.init
    |> Tactic_Util.HEADGOAL (tac tp) o pair env
    |> Seq.map_filter (try (apsnd (Goal.finish ctxt)))
    |> Seq.map forall_elim)
    |> Seq.pull
    handle TYPE _ => (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Types of terms ",
        Unification_Util.pretty_terms ctxt [lhs, rhs],
        Pretty.str " are not equal."
      ] |> Pretty.string_of);
      NONE)
  end)

end
