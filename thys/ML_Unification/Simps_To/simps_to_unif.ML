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

  val SIMPS_TO_UNIF_tac : (int -> tactic) -> (int -> thm -> 'a Seq.seq) -> Proof.context -> int ->
    thm -> 'a Seq.seq

  val SIMPS_TO_UNIF_env_thmsq : (int -> tactic) -> Unification_Base.normalisers ->
    Unification_Base.closed_unifier -> Proof.context -> term * term -> Envir.env ->
    (Envir.env * thm) Seq.seq
end

structure Simps_To_Unif : SIMPS_TO_UNIF =
struct

val logger = Logger.setup_new_logger simps_to_base_logger "Simps_To_Unif"

val dest_SIMPS_TO_UNIF = \<^Const_fn>\<open>SIMPS_TO_UNIF _ for lhs rhs => \<open>(lhs, rhs)\<close>\<close>
val cdest_SIMPS_TO_UNIF = Thm.dest_comb #>> Thm.dest_arg

fun mk_SIMPS_TO_UNIF_cprop (clhs, crhs) = \<^instantiate>\<open>'a = \<open>Thm.ctyp_of_cterm clhs\<close>
  and clhs and crhs in cprop\<open>PROP (SIMPS_TO_UNIF clhs crhs)\<close> for clhs :: 'a\<close>

fun SIMPS_TO_UNIF_tac simp_tac eq_tac ctxt =
  Tactic_Util.THEN' (
    match_tac ctxt [@{thm SIMPS_TO_UNIFI}]
    THEN' Simps_To.SIMPS_TO_tac (Simps_To.simp_inst_tac simp_tac) ctxt,
    eq_tac)

fun SIMPS_TO_UNIF_env_thmsq simp_tac norms unif ctxt (tp as (lhs, rhs)) env =
  (let
    val goal = apply2 (Thm.cterm_of ctxt) tp |> mk_SIMPS_TO_UNIF_cprop |> Goal.init
    fun eq_tac i state =
      let
        val tp = Thm.cprem_of state i |> Thm.dest_equals |> apply2 Thm.term_of
        fun norm_resolve (env, eq_thm) = #norm_unif_thm norms ctxt env eq_thm
          |> Thm.implies_elim (#norm_thm norms ctxt env state)
          |> pair env
      in unif ctxt tp env |> Seq.map norm_resolve end
  in
    (@{log Logger.TRACE} ctxt (fn _ => Pretty.block [
        Pretty.str "Creating ",
        Syntax.pretty_term ctxt @{term SIMPS_TO_UNIF},
        Pretty.str " theorems for ",
        Unification_Util.pretty_terms ctxt [lhs, rhs]
      ] |> Pretty.string_of);
    Tactic_Util.HEADGOAL (SIMPS_TO_UNIF_tac simp_tac eq_tac ctxt) goal
    |> Seq.map (apsnd Goal.conclude))
  end)
  handle TYPE _ => (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
      Pretty.str "Types of terms ",
      Unification_Util.pretty_terms ctxt [lhs, rhs],
      Pretty.str " not equal"
    ] |> Pretty.string_of);
    Seq.empty)

end
