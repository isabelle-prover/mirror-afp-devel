(*  Title:      ML_Unification/unify_assumption_base.ML
    Author:     Kevin Kappelmann

Assumption tactic with adjustable unifier.
*)
signature UNIFY_ASSUMPTION_BASE =
sig
  include HAS_LOGGER

  val unify_assumption_tac_index : Unification_Base.normalisers -> Unification_Base.unifier ->
    Proof.context -> int -> thm -> (int * thm) Seq.seq
  val unify_assumption_tac : Unification_Base.normalisers -> Unification_Base.unifier ->
    Proof.context -> int -> tactic
end

structure Unify_Assumption_Base : UNIFY_ASSUMPTION_BASE =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Unify_Assumption_Base"

structure UBase = Unification_Base

local
(*returns unification result and updated state where the unified assumption is moved to the front*)
fun unify_assumption unify ctxt i state =
  (let
    val strip_subgoal = Term_Util.strip_nth_subgoal i
    val (rparams, (prems, _)) = strip_subgoal state
    val nprems = length prems
  in
    if nprems < 1 then Seq.empty
    else
      let
        val (binders, unif_ctxt) = Binders.fix_binders rparams ctxt
        fun prepare_nth_prem n prem =
          let val (params, nprems_prem) = Term_Util.strip_all prem ||> Logic.count_prems
          in
            if nprems - n < nprems_prem then Seq.empty (*too many subpremises in given premise*)
            else
              let val nprems_new = nprems - nprems_prem
              in
                (*protect conclusion*)
                Tactic_Util.protect_tac nprems_new ctxt i state
                (*move premise to the front*)
                |> Seq.maps (rotate_tac (n - 1) i)
                (*remove all other premises*)
                |> Seq.maps (Tactic_Util.thin_tacs (2 upto nprems_new) i)
                (*remove outermost parameters of premise*)
                |> Seq.maps (REPEAT_DETERM_N (length params) (dresolve_tac ctxt [@{thm Pure.meta_spec}] i))
                (*protect premise*)
                |> Seq.maps (dmatch_tac ctxt [Drule.protectI] i)
              end
          end
        fun mk_result prem_index state =
          (*unified assumption must be the first premise in the passed state*)
          (let val (_, (prem :: _, concl)) = strip_subgoal state
          in
            unify binders unif_ctxt (prem, concl) (Envir.empty (Thm.maxidx_of state))
            |> Seq.map (pair (prem_index, binders) o rpair state)
          end)
          handle TERM _ => Seq.empty
        fun unify_prem (n, prem) = let val prem_index = n + 1
          in
            prepare_nth_prem prem_index prem
            |> Seq.maps (mk_result prem_index)
            |> Seq.append
          end
      in General_Util.fold_rev_index unify_prem prems Seq.empty end
  end)
  handle TERM _ => Seq.empty
in

fun unify_assumption_tac_index norms unify ctxt i state =
  let
    val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Trying proof by assumption for subgoal ",
        Pretty.str (Int.toString i),
        Pretty.str ": ",
        (Thm.prop_of state |> Logic.nth_prem o pair i |> Syntax.pretty_term ctxt)
        handle TERM _ => Pretty.str "<no subgoal for given index>"
      ] |> Pretty.string_of)
    fun rewrite_subgoal ((n, binders), (res, state)) =
      (*rewrite conclusion to match the premise*)
      Tactic_Util.rewrite_subgoal_unif_concl (#norm_thm norms) (#norm_unif_thm norms)
        binders res ctxt i state
      (*unified premise is moved to the front; now close by equality assumption*)
      |> Seq.maps (DETERM (Tactic_Util.nth_eq_assume_tac 1 i))
      |> Seq.map (pair n)
  in unify_assumption unify ctxt i state |> Seq.maps rewrite_subgoal end

fun unify_assumption_tac norms =
  Seq.map snd oooo unify_assumption_tac_index norms

end

end