(*  Title:      ML_Unification/unification_hints_base.ML
    Author:     Kevin Kappelmann, Paul Bachmann

Unification hints (introduced in "Hints in unification" by Asperti et al, 2009).
We support a generalisation that
1. allows additional universal variables in premises
2. allows non-atomic left-hand sides for premises
3. allows arbitrary functions to perform the matching/unification of a hint with
   a disagreement pair.

General shape of a hint:
\<open>\<And>y1...yn. (\<And>x1...xn1. lhs1 \<equiv> rhs1) \<Longrightarrow> ... \<Longrightarrow> (\<And>x1...xnk. lhsk \<equiv> rhsk) \<Longrightarrow> lhs \<equiv> rhs\<close>
*)
signature UNIFICATION_HINTS_BASE =
sig
  include HAS_LOGGER

  type unif_hint = thm
  val cdest_hint : unif_hint -> (cterm * cterm) list * (cterm * cterm)
  val cdest_hint_concl : unif_hint -> cterm * cterm
  val symmetric_hint : unif_hint -> unif_hint
  val pretty_hint : Proof.context -> unif_hint -> Pretty.T

  type hint_preprocessor = Proof.context -> thm -> unif_hint
  val obj_logic_hint_preprocessor : thm -> conv -> hint_preprocessor

  val try_hint : Unification_Base.matcher -> Unification_Base.normalisers -> unif_hint ->
    Unification_Base.e_unifier

  type hint_retrieval = term Binders.binders -> Proof.context -> term * term -> Envir.env ->
    unif_hint Seq.seq

  val try_hints : hint_retrieval -> Unification_Base.matcher -> Unification_Base.normalisers ->
    Unification_Base.e_unifier
end

structure Unification_Hints_Base : UNIFICATION_HINTS_BASE =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Unification_Hints_Base"

structure GUtil = General_Util
structure TUtil = Term_Util
structure CUtil = Conversion_Util

type unif_hint = thm

val cdest_hint = Thm.cprop_of #> TUtil.strip_cimp #>> map Thm.dest_equals ##> Thm.dest_equals
val cdest_hint_concl = Thm.cconcl_of #> Thm.dest_equals

(*only flips the conclusion since unification calls for the premises should be symmetric*)
val symmetric_hint = Conv.concl_conv ~1 CUtil.symmetric_conv |> CUtil.thm_conv
val pretty_hint = Thm.pretty_thm

type hint_preprocessor = Proof.context -> thm -> unif_hint
fun obj_logic_hint_preprocessor eq_eq_meta_eq default_conv ctxt =
  let
    fun eq_conv ct = (if can Thm.dest_equals ct then Conv.all_conv
      else Conv.rewr_conv eq_eq_meta_eq else_conv default_conv) ct
    val forall_eq_conv = Conversion_Util.repeat_forall_conv (K o K eq_conv)
  in Conversion_Util.imp_conv (forall_eq_conv ctxt) eq_conv |> Conversion_Util.thm_conv end

(*Tries to apply a hint to solve E-unification of (t1 \<equiv>? t2).
Vars in hint are lifted wrt. the passed binders.
Unifies the hint's conclusion with (t1, t2) using match.
Unifies resulting unification problems using unify.
Normalises the terms and theorems after unify with norms.
Returns a sequence of (env, thm) pairs.*)
fun try_hint match norms hint unify binders ctxt (t1, t2)
  (Envir.Envir {maxidx, tenv, tyenv}) =
  let
    val dest_all_equals = TUtil.strip_all ##> Logic.dest_equals
    val rev_binders = rev binders
    val _ = @{log Logger.TRACE} ctxt (fn _ => Pretty.block [
        Pretty.str "Trying hint: ", pretty_hint ctxt hint
      ] |> Pretty.string_of)
    (*lift hint to include bound variables and increase indexes*)
    val lifted_hint =
      (*"P" is just some dummy proposition variable with appropriate index*)
      Logic.list_all (map fst rev_binders, Var (("P", maxidx + 1), propT))
      |> Thm.cterm_of ctxt
      (*lift bound variables to the hint*)
      |> GUtil.flip Thm.lift_rule hint
    val (hint_prems, hint_concl) = Thm.prop_of lifted_hint |> TUtil.strip_subgoal |> snd

    (*match hint with unification pair*)
    val (P, Q) = dest_all_equals hint_concl |> snd
    val match = match binders ctxt
    val (no_hint_match, match_env_concl_thmpq) =
      Envir.Envir {maxidx = Thm.maxidx_of lifted_hint, tenv = tenv, tyenv = tyenv}
      |> match (P, t1)
      |> Seq.maps (fn (env, thm1) => match (Q, t2) env |> Seq.map (apsnd (pair thm1)))
      |> GUtil.seq_is_empty
  in
    if no_hint_match then (@{log Logger.TRACE} ctxt (K "Hint does not match."); Seq.empty)
    else
      let
        val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
            Pretty.str "Hint ",
            pretty_hint ctxt hint,
            Pretty.str ((length hint_prems > 0 ? suffix " Unifying premises...") " matched.")
          ] |> Pretty.string_of)
        (*unify each hint premise and collect the theorems while iteratively extending the environment*)
        fun unif_prem prem =
          let
            val (params, PQ_prem) = dest_all_equals prem
            val (binders, ctxt) = Binders.fix_binders params ctxt
            fun unif_add_result (env, thms) = unify binders ctxt PQ_prem env
              |> Seq.map (apsnd (fn thm => (binders, thm) :: thms))
          in Seq.maps unif_add_result end
        fun unify_prems (match_env, concl_thmp) =
          fold unif_prem hint_prems (Seq.single (match_env, []))
          |> Seq.map (rpair concl_thmp)
        fun inst_discharge ((env_res, prem_thms), concl_thmp) =
          let
            (*instantiate the theorems*)
            val lifted_hint_inst = #norm_thm norms ctxt env_res lifted_hint
            val norm_term = #norm_term norms env_res
            val mk_norm_cbinders = map (Thm.cterm_of ctxt o norm_term o snd)
            val norm_unif_thm = #norm_unif_thm norms ctxt env_res
            fun forall_intr binders = fold Thm.forall_intr (mk_norm_cbinders binders) o norm_unif_thm
            val prem_thms_inst = map (uncurry forall_intr) prem_thms |> rev
            val (concl_thmL, concl_thmR) = apply2 norm_unif_thm concl_thmp
            (*discharge the hint premises*)
            val thm_res = Drule.implies_elim_list lifted_hint_inst prem_thms_inst
              |> Drule.forall_elim_list (mk_norm_cbinders rev_binders)
              |> GUtil.flip Thm.transitive concl_thmR
              |> Thm.transitive (Unification_Base.symmetric concl_thmL)
          in (env_res, thm_res) end
      in Seq.maps unify_prems match_env_concl_thmpq |> Seq.map inst_discharge end
  end

type hint_retrieval = term Binders.binders -> Proof.context -> term * term -> Envir.env ->
  unif_hint Seq.seq

fun try_hints get_hints match norms unif binders ctxt (t1, t2) env =
  (@{log Logger.DEBUG} ctxt (fn _ =>
    Pretty.block [
      Pretty.str "Trying unification hints for ",
      Unification_Util.pretty_unif_problem ctxt (t1, t2)
    ] |> Pretty.string_of);
  get_hints binders ctxt (t1, t2) env
  |> Seq.maps (fn hint => try_hint match norms hint unif binders ctxt (t1, t2) env))

end