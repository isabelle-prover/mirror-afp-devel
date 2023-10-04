(*  Title:      ML_Utils/term_util.ML
    Author:     Kevin Kappelmann

Term utilities.
*)
signature TERM_UTIL =
sig
  val fresh_vars : string -> typ list -> int -> term list * int
  val fresh_var : string -> typ -> int -> term * int

  (*returns outer parameters in reversed order*)
  val strip_all : term -> (string * typ) list * term
  val strip_call : cterm -> cterm Binders.binders * cterm

  (*returns premises and conclusion*)
  val strip_imp : term -> term list * term
  val strip_cimp : cterm -> cterm list * cterm

  (*returns outer parameters in reversed order, premises, and conclusion*)
  val strip_subgoal : term -> (string * typ) list * (term list * term)
  val strip_csubgoal : cterm -> cterm Binders.binders * (cterm list * cterm)
  val strip_nth_subgoal : int -> thm -> (string * typ) list * (term list * term)
  val strip_nth_csubgoal : int -> thm -> cterm Binders.binders * (cterm list * cterm)

  (*replace outer parameters by fresh meta variables*)
  val forall_elim_vars : term -> int -> term * int

  val protect : cterm -> cterm
  val unprotect : cterm -> cterm

  val no_dummy_pattern : term -> bool
  val has_dummy_pattern : term -> bool
end

structure Term_Util : TERM_UTIL =
struct

fun fresh_vars name Ts idx =
  let fun mk_var_inc T i = (Var ((name, i + 1), T), (i + 1))
  in fold_map mk_var_inc Ts idx end

fun fresh_var name = yield_singleton (fresh_vars name)

val strip_all =
  let fun strip params (Const ("Pure.all", _) $ Abs (a, T, t)) = strip ((a, T) :: params) t
        | strip params t = (params, t)
  in strip [] end

val strip_call =
  let fun strip params ct =
    ((let val (cp as (_, cx)) = Thm.dest_comb ct
    in case apply2 Thm.term_of cp of
        (Const ("Pure.all", _), Abs (a, T, _)) =>
          let val (cf, cb) = Thm.dest_abs_global cx
          in strip (((a, T), cf) :: params) cb end
      | _ => (params, ct)
    end)
    handle CTERM _ => (params, ct))
  in strip [] end

fun strip_imp t =
  (let
    val (prem, t) = Logic.dest_implies t
    val (prems, concl) = strip_imp t
  in (prem :: prems, concl) end)
  handle TERM _ => ([], t)

fun strip_cimp ct =
  (let
    val (cprem, ct) = Thm.dest_implies ct
    val (cprems, cconcl) = strip_cimp ct
  in (cprem :: cprems, cconcl) end)
  handle TERM _ => ([], ct)

val strip_subgoal = strip_all ##> strip_imp
val strip_csubgoal = strip_call ##> strip_cimp
fun strip_nth_subgoal i = Thm.prop_of #> pair i #> Logic.nth_prem #> strip_subgoal
fun strip_nth_csubgoal i state = Thm.cprem_of state i |> strip_csubgoal

fun forall_elim_vars t i =
  let val (params, tbody) = strip_all t
  in
    if null params then (t, i)
    else
      fold_map (uncurry fresh_var) params i
      |>> Term.subst_bounds o rpair tbody
  end

val protect = Drule.protect
val unprotect = Thm.dest_arg

val no_dummy_pattern = can (Term.no_dummy_patterns)
val has_dummy_pattern = not o no_dummy_pattern

end