(*  Title:      ML_Unification/unify_resolve_base.ML
    Author:     Kevin Kappelmann

Resolution with adjustable unifier.
*)
signature UNIFY_RESOLVE_BASE =
sig
  include HAS_LOGGER

  (*unify the conclusions of the rule and the subgoal and resolve*)
  val unify_resolve_tac : Unification_Base.normalisers ->
    Unification_Base.unifier -> thm -> Proof.context -> int -> tactic
  val unify_resolve_every_tac : Unification_Base.normalisers ->
    Unification_Base.unifier -> thm list -> Proof.context -> int -> tactic
  val unify_resolve_any_tac : Unification_Base.normalisers ->
    Unification_Base.unifier -> thm list -> Proof.context -> int -> tactic
  (*treats the rule and subgoal as atomic propositions; example:
    resolving rule A ==> B and subgoal A ==> B leads to A ==> A while
    resolving rule A ==> B and subgoal A ==> B atomically solves the subgoal*)
  val unify_resolve_atomic_tac : Unification_Base.normalisers ->
    Unification_Base.unifier -> thm -> Proof.context -> int -> tactic
  val unify_resolve_atomic_every_tac : Unification_Base.normalisers ->
    Unification_Base.unifier -> thm list -> Proof.context -> int -> tactic
  val unify_resolve_atomic_any_tac : Unification_Base.normalisers ->
    Unification_Base.unifier -> thm list -> Proof.context -> int -> tactic

  val unify_eresolve_tac_index : Unification_Base.normalisers -> Unification_Base.unifier ->
    Unification_Base.normalisers -> Unification_Base.unifier -> thm -> Proof.context ->
    int -> thm -> (int * thm) Seq.seq
  val unify_eresolve_tac : Unification_Base.normalisers -> Unification_Base.unifier ->
    Unification_Base.normalisers -> Unification_Base.unifier -> thm ->
    Proof.context -> int -> tactic
  val unify_eresolve_every_tac : Unification_Base.normalisers -> Unification_Base.unifier ->
    Unification_Base.normalisers -> Unification_Base.unifier -> thm list ->
    Proof.context -> int -> tactic
  val unify_eresolve_any_tac : Unification_Base.normalisers -> Unification_Base.unifier ->
    Unification_Base.normalisers -> Unification_Base.unifier -> thm list ->
    Proof.context -> int -> tactic

  val unify_dresolve_tac : Unification_Base.normalisers -> Unification_Base.unifier -> thm ->
    Proof.context -> int -> tactic
  val unify_dresolve_every_tac : Unification_Base.normalisers -> Unification_Base.unifier ->
    thm list -> Proof.context -> int -> tactic
  val unify_dresolve_any_tac : Unification_Base.normalisers -> Unification_Base.unifier ->
    thm list -> Proof.context -> int -> tactic

  val unify_fresolve_tac : Unification_Base.normalisers -> Unification_Base.unifier -> thm ->
    Proof.context -> int -> tactic
  val unify_fresolve_every_tac : Unification_Base.normalisers -> Unification_Base.unifier ->
    thm list -> Proof.context -> int -> tactic
  val unify_fresolve_any_tac : Unification_Base.normalisers -> Unification_Base.unifier ->
    thm list -> Proof.context -> int -> tactic

end

structure Unify_Resolve_Base : UNIFY_RESOLVE_BASE =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Unify_Resolve_Base"

structure Util = Unification_Util
structure HOPU = Higher_Order_Pattern_Unification

fun unify_resolve_tac norms unify rule ctxt =
  let fun tac cgoal i state =
    let
      val _ = @{log Logger.TRACE} ctxt (fn _ =>
          Pretty.block [
            Pretty.str ("Calling unification resolution tactic on subgoal "),
            Pretty.str (Int.toString i),
            Pretty.str ": ",
            Util.pretty_terms ctxt [Thm.term_of cgoal],
            Pretty.str (" and rule: "),
            Thm.pretty_thm ctxt rule
          ]
          |> Pretty.string_of
        )
      val lifted_rule = Thm.lift_rule cgoal (Drule.incr_indexes state rule)
      val nprems_rule = Thm.nprems_of rule
      val rparams = Term_Util.strip_all (Thm.term_of cgoal) |> fst
      val (binders, ctxt) = Binders.fix_binders rparams ctxt
      val conclp = (*only unify the conclusion of the rule and the goal*)
        apply2 Logic.strip_assums_concl (Thm.prop_of lifted_rule, Thm.term_of cgoal)
      val env_thmq = unify binders ctxt conclp (Envir.empty (Thm.maxidx_of lifted_rule))
      val norm_thm = #norm_thm norms
      fun rewrite_tac (env, unif_thm) =
        Tactic_Util.rewrite_subgoal_unif_concl norm_thm (#norm_unif_thm norms)
          binders (env, unif_thm) ctxt
        THEN' Tactic_Util.no_lift_resolve_tac (norm_thm ctxt env lifted_rule) nprems_rule ctxt
    in Seq.maps (fn res => rewrite_tac res i state) env_thmq end
  in Tactic_Util.CSUBGOAL_DATA I tac end

fun unify_resolve_tacs norms unify rules ctxt =
  map (fn rule => unify_resolve_tac norms unify rule ctxt) rules

fun unify_resolve_every_tac norms unify rules =
  unify_resolve_tacs norms unify rules #> EVERY'

fun unify_resolve_any_tac norms unify rules =
  unify_resolve_tacs norms unify rules #> Tactic_Util.CONCAT'

fun unify_resolve_atomic_tac norms unify rule ctxt =
  Tactic_Util.protect_tac 0 ctxt
  THEN' unify_resolve_tac norms unify (Thm_Util.protect rule) ctxt

fun unify_resolve_atomic_tacs norms unify rules ctxt =
  map (fn rule => unify_resolve_atomic_tac norms unify rule ctxt) rules

fun unify_resolve_atomic_every_tac norms unify rules =
  unify_resolve_atomic_tacs norms unify rules #> EVERY'

fun unify_resolve_atomic_any_tac norms unify rules =
  unify_resolve_atomic_tacs norms unify rules #> Tactic_Util.CONCAT'

fun unify_eresolve_tac_index norms_resolve unify_resolve norms_assume unify_assume
  rule ctxt i state =
  unify_resolve_tac norms_resolve unify_resolve rule ctxt i state
  |> Seq.maps (Unify_Assumption_Base.unify_assumption_tac_index norms_assume unify_assume ctxt i)

fun unify_eresolve_tac norms_resolve unify_resolve norms_assume unify_assume
  rule ctxt i state =
  let val nprems = Thm.nprems_of rule
  in
    if nprems = 0 then
      (@{log Logger.WARN} ctxt (fn _ =>
        Pretty.block [
          Pretty.str "elim-resolution rule ",
          Thm.pretty_thm ctxt rule,
          Pretty.str " has no premises."
        ] |> Pretty.string_of
      );
      Seq.empty)
    else
      unify_eresolve_tac_index norms_resolve unify_resolve norms_assume unify_assume rule ctxt i state
      |> Seq.maps (fn (n, state) =>
        Tactic_Util.EVERY_ARG (Tactic_Util.thin_tac n) (i upto i + nprems - 2) state)
  end

fun unify_eresolve_tacs norms_resolve unify_resolve norms_assume unify_assume rules ctxt =
  map (fn rule => unify_eresolve_tac norms_resolve unify_resolve norms_assume unify_assume rule ctxt)
    rules

fun unify_eresolve_every_tac norms_resolve unify_resolve norms_assume unify_assume rules =
  unify_eresolve_tacs norms_resolve unify_resolve norms_assume unify_assume rules
  #> EVERY'

fun unify_eresolve_any_tac norms_resolve unify_resolve norms_assume unify_assume rules =
  unify_eresolve_tacs norms_resolve unify_resolve norms_assume unify_assume rules
  #> Tactic_Util.CONCAT'

fun unify_dresolve_tac norms unify rule ctxt =
  let val nprems = Thm.nprems_of rule
  in
    if nprems = 0 then
      (@{log Logger.WARN} ctxt (fn _ =>
        Pretty.block [
          Pretty.str "destruct-resolution rule ",
          Thm.pretty_thm ctxt rule,
          Pretty.str " has no premises."
        ] |> Pretty.string_of
      );
      K no_tac)
    else unify_eresolve_tac HOPU.norms_unify HOPU.unify norms unify (Tactic.make_elim rule) ctxt
  end

fun unify_dresolve_tacs norms unify rules ctxt =
  map (fn rule => unify_dresolve_tac norms unify rule ctxt) rules

fun unify_dresolve_every_tac norms unify rules = unify_dresolve_tacs norms unify rules #> EVERY'

fun unify_dresolve_any_tac norms unify rules =
  unify_dresolve_tacs norms unify rules #> Tactic_Util.CONCAT'

fun unify_fresolve_tac norms unify rule ctxt i state =
  let val nprems = Thm.nprems_of rule
  in
    if nprems = 0 then
      (@{log Logger.WARN} ctxt (fn _ =>
        Pretty.block [
          Pretty.str "forward-resolution rule ",
          Thm.pretty_thm ctxt rule,
          Pretty.str " has no premises."
        ] |> Pretty.string_of
      );
      Seq.empty)
    else
      unify_eresolve_tac_index HOPU.norms_unify HOPU.unify norms unify (Tactic.make_elim rule)
        ctxt i state
      |> Seq.map snd
  end

fun unify_fresolve_tacs norms unify rules ctxt =
  map (fn rule => unify_fresolve_tac norms unify rule ctxt) rules

fun unify_fresolve_every_tac norms unify rules =
  unify_fresolve_tacs norms unify rules #> EVERY'

fun unify_fresolve_any_tac norms unify rules =
  unify_fresolve_tacs norms unify rules #> Tactic_Util.CONCAT'

end
