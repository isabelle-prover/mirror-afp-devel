(*  Title:      ML_Utils/tactic_util.ML
    Author:     Kevin Kappelmann

Tactic utilities.
*)
signature TACTIC_UTIL =
sig
  include HAS_LOGGER
  (* tactic combinators*)
  val HEADGOAL : (int -> 'a) -> 'a

  val TRY' : ('a -> tactic) -> 'a -> tactic

  val EVERY_ARG : ('a -> tactic) -> 'a list -> tactic
  val EVERY_ARG' : ('a -> 'b -> tactic) -> 'a list -> 'b -> tactic
  val CONCAT : tactic list -> tactic
  val CONCAT' : ('a -> tactic) list -> 'a -> tactic

  val FOCUS_PARAMS' : (Subgoal.focus -> int -> tactic) -> Proof.context -> int -> tactic
  val FOCUS_PARAMS_CTXT : (Proof.context -> tactic) -> Proof.context -> int -> tactic
  val FOCUS_PARAMS_CTXT' : (Proof.context -> int -> tactic) -> Proof.context -> int -> tactic
  val FOCUS_PARAMS_FIXED' : (Subgoal.focus -> int -> tactic) -> Proof.context -> int -> tactic
  val FOCUS_PREMS' : (Subgoal.focus -> int -> tactic) -> Proof.context -> int -> tactic
  val FOCUS' : (Subgoal.focus -> int -> tactic) -> Proof.context -> int -> tactic
  val SUBPROOF' : (Subgoal.focus -> int -> tactic) -> Proof.context -> int -> tactic

  val CSUBGOAL_DATA : (cterm -> 'a) -> ('a -> int -> tactic) -> int -> tactic
  val CSUBGOAL_STRIPPED : (cterm Binders.binders * (cterm list * cterm) -> 'a) ->
    ('a -> int -> tactic) -> int -> tactic
  val SUBGOAL_DATA : (term -> 'a) -> ('a -> int -> tactic) -> int -> tactic
  val SUBGOAL_STRIPPED : ((string * typ) list * (term list * term) -> 'a) ->
    ('a -> int -> tactic) -> int -> tactic

  (* tactics *)
  val insert_tac : thm list -> Proof.context -> int -> tactic
  (*thin_tac n i deletes nth premise of the ith subgoal*)
  val thin_tac : int -> int -> tactic
  val thin_tacs : int list -> int -> tactic

  val safe_simp_tac : Proof.context -> int -> tactic

  (*nth_eq_assume_tac n i solves ith subgoal by assumption, without unification,
    preferring premise n*)
  val nth_eq_assume_tac : int -> int -> tactic

  (*resolution with matching and without lifting of premises and parameters*)
  val no_lift_biresolve_tac : bool -> thm -> int -> Proof.context -> int -> tactic
  val no_lift_resolve_tac : thm -> int -> Proof.context -> int -> tactic
  val no_lift_eresolve_tac : thm -> int -> Proof.context -> int -> tactic

  (*rewrite subgoal according to the given equality theorem "lhs \<equiv> subgoal"*)
  val rewrite_subgoal_tac : thm -> Proof.context -> int -> tactic

  (*creates equality theorem for a subgoal from an equality theorem for the subgoal's conclusion*)
  val eq_subgoal_from_eq_concl : cterm Binders.binders -> cterm list -> thm -> Proof.context -> thm

  (*rewrite a subgoal given an equality theorem and environment for the subgoal's conclusion*)
  val rewrite_subgoal_unif_concl : Envir_Normalisation.thm_normaliser ->
    Envir_Normalisation.thm_normaliser -> term Binders.binders -> (Envir.env * thm) ->
    Proof.context -> int -> tactic

  (*protect premises starting from (and excluding) the given index in the specified subgoal*)
  val protect_tac : int -> Proof.context -> int -> tactic
  (*unprotect the subgoal*)
  val unprotect_tac : Proof.context -> int -> tactic
  (*protect, then apply tactic, then unprotect*)
  val protected_tac : int -> (int -> tactic) -> Proof.context -> int -> tactic

  (*focus on the specified subgoal, introducing only the specified list of premises
    as theorems in the focus*)
  val focus_prems_tac : int list -> (Subgoal.focus -> int -> tactic) ->
    Proof.context -> int -> tactic
  (*focus_prems_tac and then deletes all focused premises*)
  val focus_delete_prems_tac : int list -> (Subgoal.focus -> int -> tactic) ->
    Proof.context -> int -> tactic

  (*apply tactic to the specified subgoal, where the state is given as a cterm*)
  val apply_tac : (int -> tactic) -> int -> cterm -> thm Seq.seq

end

structure Tactic_Util : TACTIC_UTIL =
struct

val logger = Logger.setup_new_logger Logger.root_logger "Tactic_Util"

(* tactic combinators *)
fun HEADGOAL f = f 1

fun TRY' tac =  tac ORELSE' K all_tac

fun EVERY_ARG tac = EVERY o map tac
fun EVERY_ARG' tac = EVERY' o map tac

fun CONCAT tacs = fold_rev (curry op APPEND) tacs no_tac
fun CONCAT' tacs = fold_rev (curry op APPEND') tacs (K no_tac)

fun FOCUS_PARAMS' tac = Subgoal.FOCUS_PARAMS (HEADGOAL o tac)
fun FOCUS_PARAMS_FIXED' tac = Subgoal.FOCUS_PARAMS_FIXED (HEADGOAL o tac)
fun FOCUS_PREMS' tac = Subgoal.FOCUS_PREMS (HEADGOAL o tac)
fun FOCUS' tac = Subgoal.FOCUS (HEADGOAL o tac)
fun SUBPROOF' tac = Subgoal.SUBPROOF (HEADGOAL o tac)

fun FOCUS_PARAMS_CTXT tac = Subgoal.FOCUS_PARAMS (#context #> tac)
fun FOCUS_PARAMS_CTXT' tac = FOCUS_PARAMS' (#context #> tac)

fun CSUBGOAL_DATA f tac = CSUBGOAL (uncurry tac o apfst f)
fun CSUBGOAL_STRIPPED f = CSUBGOAL_DATA (f o Term_Util.strip_csubgoal)
fun SUBGOAL_DATA f tac = SUBGOAL (uncurry tac o apfst f)
fun SUBGOAL_STRIPPED f = SUBGOAL_DATA (f o Term_Util.strip_subgoal)

(* tactics *)
fun insert_tac thms ctxt = Method.insert_tac ctxt thms

fun thin_tac n = if n < 1 then K no_tac
  else rotate_tac (n - 1) THEN' (DETERM o eresolve0_tac [thin_rl]) THEN' rotate_tac (~n + 1)
val thin_tacs = sort int_ord
  #> map_index ((op -) o swap)
  #> EVERY_ARG' thin_tac

(*some "safe" solvers create instantiations via flex-flex pairs, which we disallow here*)
fun safe_simp_tac ctxt i state =
  let val eq_flexps = Thm.tpairs_of
    #> pair (Thm.tpairs_of state)
    #> eq_list (eq_pair (op aconv) (op aconv))
  in Simplifier.safe_simp_tac ctxt i state |> Seq.filter eq_flexps end

fun nth_eq_assume_tac n = if n < 1 then K no_tac
  else rotate_tac (n - 1) THEN' eq_assume_tac

(*resolution*)
fun no_lift_biresolve_tac eres brule nsubgoals ctxt =
  Thm.bicompose (SOME ctxt) {flatten = true, match = true, incremented = true}
  (eres, brule, nsubgoals)
  #> PRIMSEQ

val no_lift_resolve_tac = no_lift_biresolve_tac false
val no_lift_eresolve_tac = no_lift_biresolve_tac true

fun rewrite_subgoal_tac eq_thm =
  let
    val (lhs, rhs) = Thm.dest_equals (Thm.cconcl_of eq_thm)
    val eq_elim = Thm.instantiate' [] [SOME lhs, SOME rhs] Drule.equal_elim_rule1
    val thm = Thm.implies_elim eq_elim eq_thm
  in no_lift_resolve_tac thm 1 end

fun eq_subgoal_from_eq_concl cbinders cprems eq_thm ctxt =
  let
    fun all_abstract ((x, T), cfree) =
      let val all_const = Logic.all_const T |> Thm.cterm_of ctxt
      in
        Thm.abstract_rule x cfree
        #> Drule.arg_cong_rule all_const
      end
  in
    (*introduce the premises*)
    fold_rev (Drule.imp_cong_rule o Thm.reflexive) cprems eq_thm
    (*introduce abstractions for the fresh Frees*)
    |> fold all_abstract cbinders
  end

fun rewrite_subgoal_unif_concl norm_state norm_eq_thm binders (env, eq_thm) ctxt i state =
  let
    fun rewrite_tac (rparams, (prems, _)) =
      let
        (*update binders with their normalised type*)
        val binders = map2 (fn (_, T) => fn ((n, _), Free (n', _)) => ((n, T), Free (n', T)))
          rparams binders
        val cterm_of = Thm.cterm_of ctxt
        val cprems = map (cterm_of o Binders.replace_binders binders) prems
        val eq_thm = eq_subgoal_from_eq_concl (map (apsnd cterm_of) binders) cprems
          (norm_eq_thm ctxt env eq_thm) ctxt
      in rewrite_subgoal_tac eq_thm ctxt end
  in
    ((PRIMITIVE (norm_state ctxt env) |> K)
    THEN' SUBGOAL_STRIPPED I rewrite_tac) i state
  end

fun protect_tac n ctxt =
  let fun protect cbinders (cprems, cconcl) i =
    let val nprems = length cprems
    in
      if nprems < n then
        (@{log Logger.WARN} ctxt (fn _ => Pretty.block [
          Pretty.str "Not enough premises to protect. Given number: ",
          Pretty.str (string_of_int n),
          Pretty.str ". But there are only ",
          Pretty.str (string_of_int nprems),
          Pretty.str " premise(s) in subgoal ",
          Pretty.str (string_of_int i),
          Pretty.str ": ",
          Logic.close_prop (map (apfst fst o apsnd Thm.term_of) cbinders) (map Thm.term_of cprems)
            (Thm.term_of cconcl) |> Syntax.pretty_term ctxt
        ] |> Pretty.string_of);
        no_tac)
      else
        let
          val (cprems_unprotected, cconcl_protected) = chop n cprems
            ||> Drule.list_implies o rpair cconcl
          val protected_eq_thm = @{thm Pure.prop_def}
            |> Thm.instantiate' [] [SOME cconcl_protected]
            |> (fn eq_thm => eq_subgoal_from_eq_concl cbinders cprems_unprotected eq_thm ctxt)
        in rewrite_subgoal_tac protected_eq_thm ctxt i end
    end
  in if n < 0 then K no_tac else CSUBGOAL_STRIPPED I (uncurry protect) end

fun unprotect_tac ctxt = match_tac ctxt [Drule.protectI]

fun protected_tac n tac ctxt =
  protect_tac n ctxt
  THEN' tac
  THEN_ALL_NEW (unprotect_tac ctxt)

fun focus_prems_tac is tac ctxt =
  CONVERSION (Conversion_Util.move_prems_to_front_conv is)
  THEN' protect_tac (length is) ctxt
  THEN' FOCUS' (fn {context=ctxt, params=params, prems=prems,
    asms=asms, concl=concl, schematics=schematics} =>
    let val concl = Term_Util.unprotect concl
    in
      unprotect_tac ctxt
      THEN' tac {context=ctxt, params=params, prems=prems, asms=asms, concl=concl,
        schematics=schematics}
    end
  ) ctxt

fun focus_delete_prems_tac is tac ctxt =
  focus_prems_tac is tac ctxt
  THEN' thin_tacs (1 upto length is)

fun apply_tac tac i = Goal.init #> tac i #> Seq.map Goal.conclude

end

