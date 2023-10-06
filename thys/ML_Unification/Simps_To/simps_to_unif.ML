(*  Title:      ML_Unification/simps_to_unif.ML
    Author:     Kevin Kappelmann

Create SIMPS_TO_UNIF theorems.
*)
signature SIMPS_TO_UNIF =
sig
  include HAS_LOGGER

  val dest_SIMPS_TO_UNIF : term -> (term * term)
  val cdest_SIMPS_TO_UNIF : cterm -> (cterm * cterm)

  val mk_SIMPS_TO_UNIF_cprop : cterm -> cterm -> cterm

  val mk_SIMPS_TO_UNIF_thm : thm -> thm -> thm

  val SIMPS_TO_UNIF_env_thmsq : (int -> tactic) -> Unification_Base.normalisers ->
    Unification_Base.unifier -> term Binders.binders -> Proof.context -> term * term -> Envir.env ->
    (Envir.env * thm) Seq.seq
end

structure Simps_To_Unif : SIMPS_TO_UNIF =
struct

val logger = Logger.setup_new_logger simps_to_base_logger "Simps_To_Unif"

val dest_SIMPS_TO_UNIF = \<^Const_fn>\<open>SIMPS_TO_UNIF _ for lhs rhs => \<open>(lhs, rhs)\<close>\<close>
val cdest_SIMPS_TO_UNIF = Thm.dest_comb #>> Thm.dest_arg

fun mk_SIMPS_TO_UNIF_cprop clhs crhs = \<^instantiate>\<open>'a = \<open>Thm.ctyp_of_cterm clhs\<close> and clhs and crhs
  in cprop\<open>PROP (SIMPS_TO_UNIF clhs crhs)\<close> for clhs :: 'a\<close>

fun mk_SIMPS_TO_UNIF_thm SIMPS_TO_thm eq_thm =
  Drule.incr_indexes2 SIMPS_TO_thm eq_thm @{thm SIMPS_TO_UNIFI}
  |> Thm_Util.match_implies_elim SIMPS_TO_thm
  |> Thm_Util.match_implies_elim eq_thm

fun SIMPS_TO_UNIF_env_thmsq simps_to_tac norms unif binders ctxt (lhs, rhs) env =
  let
    val SIMPS_TO_res = Binders.replace_binders binders lhs
      |> Thm.cterm_of ctxt
      |> Simps_To.SIMPS_TO_thm_resultsq simps_to_tac ctxt
    fun unif_res (SIMPS_TO_thm, clhs_norm) =
      let val tp = (Binders.replace_frees binders (Thm.term_of clhs_norm), rhs)
      in
        (@{log Logger.TRACE} ctxt (fn _ => Pretty.block [
            Pretty.str "Result: ",
            Thm.pretty_thm ctxt SIMPS_TO_thm,
            Pretty.str " Now unifying ",
            Unification_Util.pretty_unif_problem ctxt tp
          ] |> Pretty.string_of);
        unif binders ctxt tp env
        |> Seq.map (pair SIMPS_TO_thm))
      end
    fun SIMPS_TO_UNIF_res (SIMPS_TO_thm, (env, eq_thm)) =
      let val (SIMPS_TO_thm, eq_thm) =
        (#norm_thm norms ctxt env SIMPS_TO_thm, #norm_unif_thm norms ctxt env eq_thm)
      in (env, mk_SIMPS_TO_UNIF_thm SIMPS_TO_thm eq_thm) end
  in
    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Creating ",
        Syntax.pretty_term ctxt @{term SIMPS_TO_UNIF},
        Pretty.str " theorems for ",
        Unification_Util.pretty_terms ctxt [lhs, rhs]
      ] |> Pretty.string_of);
    SIMPS_TO_res
    |> Seq.maps unif_res
    |> Seq.map SIMPS_TO_UNIF_res)
  end

end
