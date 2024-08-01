(*  Title:      ML_Unification/simps_to_unif.ML
    Author:     Kevin Kappelmann

Create SIMPS_TO_UNIF theorems.
*)
signature SIMPS_TO_UNIF =
sig
  include HAS_LOGGER

  val dest_SIMPS_TO_UNIF : term -> (term * term)
  val cdest_SIMPS_TO_UNIF : cterm -> (cterm * cterm)

  val mk_SIMPS_TO_UNIF_cprop : cterm * cterm -> cterm

  val SIMPS_TO_UNIF_tac : (int -> tactic) -> (int -> thm -> 'a Seq.seq) -> int -> Proof.context ->
    int -> thm -> 'a Seq.seq
  val SIMPS_TO_UNIF_refl_tac : (int -> tactic) -> int -> Proof.context -> int -> tactic

  val SIMPS_TO_UNIF_env_tac : (int -> tactic) -> Unification_Base.normalisers ->
    Unification_Base.unifier -> Proof.context -> int -> Tactic_Unification.env_tactic
end

structure Simps_To_Unif : SIMPS_TO_UNIF =
struct

val logger = Logger.setup_new_logger simps_to_base_logger "Simps_To_Unif"

val dest_SIMPS_TO_UNIF = \<^Const_fn>\<open>SIMPS_TO_UNIF _ for lhs rhs => \<open>(lhs, rhs)\<close>\<close>
val cdest_SIMPS_TO_UNIF = Thm.dest_comb #>> Thm.dest_arg

fun mk_SIMPS_TO_UNIF_cprop (clhs, crhs) = \<^instantiate>\<open>'a = \<open>Thm.ctyp_of_cterm clhs\<close>
  and clhs and crhs in cprop\<open>PROP (SIMPS_TO_UNIF clhs crhs)\<close> for clhs :: 'a\<close>

fun SIMPS_TO_UNIF_tac simp_tac eq_tac maxidx ctxt =
  let open Tactic_Util
    fun inst_tac (params, concl) state =
      let
        val (binders, ctxt) = Binders.fix_binders params ctxt
        val (lhs, rhs) = Simps_To.dest_SIMPS_TO concl
        val env = Envir.empty (Thm.maxidx_of state)
      in
        Unify.hounifiers (map fst binders) (Context.Proof ctxt, env, [(rhs, lhs)])
        |> Seq.filter (fn (env, _) => Envir.above env maxidx) (*only keep the matchers*)
        |> Seq.map (fn (env, _) => #inst_thm Higher_Order_Unification.norms ctxt env state)
      end
    val simp_inst_tac = simp_tac THEN' Tactic_Util.SUBGOAL_STRIPPED (apsnd snd) (K o inst_tac)
  in
    match_tac ctxt [Thm.incr_indexes (maxidx + 1) @{thm SIMPS_TO_UNIFI}]
    (*unfortunately, the matcher fails to solve the trivial goal in case of flex-flex pairs; we
    hence have to use the unifier and hope that it does the right instantiation*)
    THEN' Simps_To.SIMPS_TO_unif_tac simp_inst_tac ctxt
    THEN' eq_tac
  end

fun SIMPS_TO_UNIF_refl_tac simp_tac maxidx ctxt =
  SIMPS_TO_UNIF_tac simp_tac (resolve_tac ctxt [@{thm reflexive}]) maxidx ctxt

fun SIMPS_TO_UNIF_env_tac simp_tac norms unif ctxt i (env, state) =
  let fun eq_tac i state =
    let
      val env = Unification_Util.update_maxidx_envir (Thm.maxidx_of state) env
      val (params, tp) = Thm.cprem_of state i |> Thm.term_of
        |> Term_Util.strip_all ||> Logic.dest_equals
      val (binders, ctxt) = Binders.fix_binders params ctxt
      fun norm_implies_elim (env, eq_thm) =
        let
          val inst_term = #inst_term norms env
          val conv = #conv norms
          val binders = map (snd #> inst_term #> Thm.cterm_of ctxt) binders
        in
          eq_thm
          |> Unification_Util.inst_norm_thm (#inst_unif_thm norms) conv ctxt env
          |> fold Thm.forall_intr binders
          |> Thm.implies_elim
            (Unification_Util.inst_norm_subgoal (#inst_thm norms) conv i ctxt env state)
          |> pair env
        end
    in unif binders ctxt tp env |> Seq.map norm_implies_elim end
  in SIMPS_TO_UNIF_tac simp_tac eq_tac (Envir.maxidx_of env) ctxt i state end

end
