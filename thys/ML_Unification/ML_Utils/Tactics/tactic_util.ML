(*  Title:      ML_Utils/tactic_util.ML
    Author:     Kevin Kappelmann

Tactic utilities.
*)
signature TACTIC_UTIL =
sig
  include HAS_LOGGER
  (* tactic combinators *)
  val HEADGOAL : (int -> 'a) -> 'a

  val THEN : ('a -> 'b Seq.seq) * ('b -> 'c Seq.seq) -> 'a -> 'c Seq.seq
  val THEN' : ('a -> 'b -> 'c Seq.seq) * ('a -> 'c -> 'd Seq.seq) -> 'a -> 'b -> 'd Seq.seq

  val ORELSE : ('a -> 'b Seq.seq) * ('a -> 'b Seq.seq) -> 'a -> 'b Seq.seq
  val ORELSE' : ('a -> 'b -> 'c Seq.seq) * ('a -> 'b -> 'c Seq.seq) -> 'a -> 'b -> 'c Seq.seq

  val TRY' : ('a -> tactic) -> 'a -> tactic

  val EVERY_ARG : ('a -> tactic) -> 'a list -> tactic
  val EVERY_ARG' : ('a -> 'b -> tactic) -> 'a list -> 'b -> tactic
  val CONCAT : tactic list -> tactic
  val CONCAT' : ('a -> tactic) list -> 'a -> tactic

  (*filters duplicate results*)
  val unique_thmsq : thm Seq.seq -> thm Seq.seq
  val UNIQUE : tactic -> tactic
  val UNIQUE' : ('a -> tactic) -> 'a -> tactic

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

  val set_kernel_ho_unif_bounds : int -> int -> Proof.context -> Proof.context
  val silence_kernel_ho_bounds_exceeded : Proof.context -> Proof.context
  val safe_simp_tac : Proof.context -> int -> tactic

  (*nth_eq_assume_tac n i solves ith subgoal by assumption, without unification,
    preferring premise n*)
  val nth_eq_assume_tac : int -> int -> tactic

  (*resolution without lifting of premises and parameters*)
  val no_lift_biresolve_tac : bool -> thm -> int -> Proof.context -> int -> tactic
  val no_lift_resolve_tac : thm -> int -> Proof.context -> int -> tactic
  val no_lift_eresolve_tac : thm -> int -> Proof.context -> int -> tactic

  (*rewrite subgoal according to the given equality theorem "lhs \<equiv> subgoal"*)
  val rewrite_subgoal_tac : thm -> int -> tactic

  (*creates equality theorem for a subgoal from an equality theorem for the subgoal's conclusion;
    fails if the equality theorem contains a tpair or implicit Assumption mentioning one of the bound variables*)
  val eq_subgoal_from_eq_concl : cterm Binders.binders -> cterm list -> Proof.context -> thm ->
    thm option

  (*rewrite a subgoal given an equality theorem and environment for the subgoal's conclusion*)
  val rewrite_subgoal_unif_concl : Envir_Normalisation.term_normaliser ->
    (int -> Envir_Normalisation.thm_normaliser) -> Envir_Normalisation.thm_normaliser ->
    term Binders.binders -> (Envir.env * thm) -> Proof.context -> int -> tactic

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

val logger = Logger.setup_new_logger Logger.root "Tactic_Util"

(* tactic combinators *)
fun HEADGOAL f = f 1

fun (tac1 THEN tac2) = Seq.THEN (tac1, tac2)
fun (tac1 THEN' tac2) x = tac1 x THEN tac2 x

fun (tac1 ORELSE tac2) st = Seq.make (fn _ => case Seq.pull (tac1 st) of
    NONE => Seq.pull (tac2 st)
  | some => some)
fun (tac1 ORELSE' tac2) x = tac1 x ORELSE tac2 x

fun TRY' tac = tac ORELSE' K all_tac

fun EVERY_ARG tac = EVERY o map tac
fun EVERY_ARG' tac = EVERY' o map tac

fun CONCAT tacs = fold_rev (curry (op APPEND)) tacs no_tac
fun CONCAT' tacs = fold_rev (curry (op APPEND')) tacs (K no_tac)

local structure TI = Net
in
fun unique_thmsq thmsq =
  let fun go ti = Seq.pull #> Option.mapPartial (fn (thm, thmsq) =>
    let val key = Thm.full_prop_of thm |> TI.key_of_term
    in
      if null (TI.lookup ti key)
      then SOME (thm, Seq.make (fn _ => go (TI.insert (K false) (key, thm) ti) thmsq))
      else go ti thmsq
    end)
  in Seq.make (fn _ => go TI.empty thmsq) end
fun UNIQUE tac = unique_thmsq o tac
fun UNIQUE' tac = UNIQUE o tac
end

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

fun set_kernel_ho_unif_bounds trace_bound search_bound =
  Config.put Unify.unify_trace_bound trace_bound
  #> Config.put Unify.search_bound search_bound

val silence_kernel_ho_bounds_exceeded = Context_Position.set_visible false

(*some "safe" solvers create instantiations via flex-flex pairs, which we disallow here*)
fun safe_simp_tac ctxt i state =
  let
    val eq_flexps = Thm.tpairs_of
      #> pair (Thm.tpairs_of state)
      #> eq_list (eq_pair (op aconv) (op aconv))
    (*stop higher-order unifier from entering difficult unification problems*)
    val ctxt = set_kernel_ho_unif_bounds 1 1 ctxt |> silence_kernel_ho_bounds_exceeded
  in Simplifier.safe_simp_tac ctxt i state |> Seq.filter eq_flexps end

fun nth_eq_assume_tac n = if n < 1 then K no_tac
  else rotate_tac (n - 1) THEN' eq_assume_tac

(*resolution*)
fun no_lift_biresolve_tac eres brule nsubgoals ctxt =
  Thm.bicompose (SOME ctxt) {flatten = true, match = false, incremented = true}
  (eres, brule, nsubgoals)
  #> PRIMSEQ

val no_lift_resolve_tac = no_lift_biresolve_tac false
val no_lift_eresolve_tac = no_lift_biresolve_tac true

fun rewrite_subgoal_tac eq_thm = CONVERSION (K (Thm.symmetric eq_thm))

fun eq_subgoal_from_eq_concl cbinders cprems ctxt eq_thm =
  let
    fun all_abstract ((x, T), cfree) =
      let val all_const = Logic.all_const T |> Thm.cterm_of ctxt
      in
        Thm_Util.abstract_rule ctxt x cfree
        #> Option.map (Drule.arg_cong_rule all_const)
      end
  in
    (*introduce the premises*)
    SOME (fold_rev (Drule.imp_cong_rule o Thm.reflexive) cprems eq_thm)
    (*introduce abstractions for the fresh Frees*)
    |> fold (Option.mapPartial o all_abstract) cbinders
  end

fun rewrite_subgoal_unif_concl inst_binders norm_state norm_eq_thm binders (env_eq_thm as (env, _))
  ctxt i =
  let
    (*updates binders with their normalised type*)
    fun normed_binders env = Binders.norm_binders (inst_binders env) binders
    val binders = normed_binders env
    val smash_tpairs_if_occurs = Seq.maps o Unification_Util.smash_tpairs_if_occurs ctxt
    fun rewrite_tac env eq_thm prems =
      let
        val binders = normed_binders env
        val cterm_of = Thm.cterm_of ctxt
        val cprems = map (cterm_of o Binders.replace_binders binders) prems
      in
        norm_eq_thm ctxt env eq_thm
        |> eq_subgoal_from_eq_concl (map (apsnd cterm_of) binders) cprems ctxt
        |> Option.map rewrite_subgoal_tac
        |> the_default (K no_tac)
      end
  in
    (*smash tpairs in case some binder occurs*)
    fold (smash_tpairs_if_occurs o snd) binders (Seq.single env_eq_thm)
    |> Seq.lifts (fn (env, eq_thm) =>
      PRIMITIVE (norm_state i ctxt env)
      THEN SUBGOAL_STRIPPED (fst o snd) (rewrite_tac env eq_thm) i)
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
        in
          @{thm Pure.prop_def}
          |> Thm.instantiate' [] [SOME cconcl_protected]
          |> eq_subgoal_from_eq_concl cbinders cprems_unprotected ctxt
          |> Option.map (fn protected_eq_thm => rewrite_subgoal_tac protected_eq_thm i)
          |> the_default no_tac
        end
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
  THEN' FOCUS_PREMS' (fn {context=ctxt, params=params, prems=prems,
    asms=asms, schematics=schematics, concl=concl} => unprotect_tac ctxt
      THEN' tac {context=ctxt, params=params, prems=prems, asms=asms, schematics=schematics,
        concl=Term_Util.unprotect concl}
  ) ctxt

fun focus_delete_prems_tac is tac ctxt =
  focus_prems_tac is tac ctxt
  THEN' thin_tacs (1 upto length is)

fun apply_tac tac i = Seq.single #> Seq.map Goal.init #> Seq.maps (tac i) #> Seq.map Goal.conclude

end

