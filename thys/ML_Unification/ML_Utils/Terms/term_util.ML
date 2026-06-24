(*  Title:      ML_Utils/term_util.ML
    Author:     Kevin Kappelmann

Term utilities.
*)
signature TERM_UTIL =
sig
  val is_Abs : term -> bool
  val abstract_over : (term * term -> bool) -> term -> term Same.operation
  val lambda : (term * term -> bool) -> string * (term * typ) -> term -> term

  val fresh_vars : string -> typ list -> int -> term list * int
  val fresh_var : string -> typ -> int -> term * int

  val strip_ccomb : cterm -> cterm * cterm list

  (*returns outer parameters in reversed order*)
  val strip_all : term -> (string * typ) list * term
  val strip_call : cterm -> cterm Binders.binders * cterm

  (*returns premises and conclusion*)
  val strip_imp : term -> term list * term
  val strip_cimp : cterm -> cterm list * cterm

  (*returns outer parameters in reversed order, premises, and conclusion*)
  type subgoal = (string * typ) list * (term list * term)
  val strip_subgoal : term -> subgoal
  val strip_csubgoal : cterm -> cterm Binders.binders * (cterm list * cterm)
  val nth_subgoal : int -> thm -> term
  val strip_nth_subgoal : int -> thm -> subgoal
  val strip_nth_csubgoal : int -> thm -> cterm Binders.binders * (cterm list * cterm)

  val pretty_subgoal : Proof.context -> term -> Pretty.T
  val pretty_subgoal_concl : Proof.context -> term -> Pretty.T
  val pretty_subgoals : Proof.context -> term list -> Pretty.T

  (*replace outer parameters by fresh meta variables*)
  val forall_elim_vars : term -> int -> term * int

  val mk_equals : typ list -> term * term -> term

  val protect : cterm -> cterm
  val unprotect : cterm -> cterm

  val no_dummy_pattern : term -> bool
  val has_dummy_pattern : term -> bool

  val are_variants : term * term -> bool
  val are_beta_eta_variants : term * term -> bool
end

structure Term_Util : TERM_UTIL =
struct

fun is_Abs (Abs _) = true
  | is_Abs _ = false

fun abstract_over eq s =
  let fun term lev t = if eq (s, t) then Bound lev
    else case t of
        Abs (a, T, t) => Abs (a, T, term (lev + 1) t)
      | t $ u => (term lev t $ Same.commit (term lev) u handle Same.SAME => t $ term lev u)
      | _ => raise Same.SAME
  in term 0 end

fun lambda eq (x, (t, T)) s = Abs (if x = "" then Term.term_name t else x, T,
  Same.commit (abstract_over eq t) s)

fun fresh_vars name Ts idx =
  let fun mk_var_inc T i = (Var ((name, i + 1), T), (i + 1))
  in fold_map mk_var_inc Ts idx end

fun fresh_var name = yield_singleton (fresh_vars name)

val strip_ccomb =
  let fun strip cargs ct =
    ((let val (ct, cx) = Thm.dest_comb ct
    in strip (cx :: cargs) ct end)
    handle CTERM _ => (ct, cargs))
  in strip [] end

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

type subgoal = (string * typ) list * (term list * term)
val strip_subgoal = strip_all ##> strip_imp
val strip_csubgoal = strip_call ##> strip_cimp
fun nth_subgoal i = Thm.prop_of #> pair i #> Logic.nth_prem
fun strip_nth_subgoal i = Thm.prop_of #> pair i #> Logic.nth_prem #> strip_subgoal
fun strip_nth_csubgoal i state = Thm.cprem_of state i |> strip_csubgoal

fun gen_pretty_subgoal f ctxt = strip_all
  #> apfst (fn params => Binders.fix_binders params ctxt)
  #> (fn ((binders, ctxt), t) => f t |> Binders.replace_binders binders |> Syntax.pretty_term ctxt)
val pretty_subgoal = gen_pretty_subgoal I
val pretty_subgoal_concl = gen_pretty_subgoal (strip_imp #> snd)
fun pretty_subgoals ctxt = map (Syntax.pretty_term ctxt #> single #> Pretty.block)
  #> Pretty.fbreaks #> Pretty.block0

fun forall_elim_vars t i =
  let val (params, tbody) = strip_all t
  in
    if null params then (t, i)
    else
      fold_map (uncurry fresh_var) params i
      |>> Term.subst_bounds o rpair tbody
  end

fun mk_equals Ts (lhs, rhs) = \<^Const>\<open>Pure.eq \<open>fastype_of1 (Ts, lhs)\<close> for lhs rhs\<close>

val protect = Drule.protect
val unprotect = Thm.dest_arg

val no_dummy_pattern = can Term.no_dummy_patterns
val has_dummy_pattern = not o no_dummy_pattern

fun are_variants tp =
  let
    val thy = Context.the_global_context ()
    fun match tp = Pattern.first_order_match thy tp (Vartab.empty, Vartab.empty)
  in can match tp andalso can match (swap tp) end

val are_beta_eta_variants = apply2 (Same.commit Term_Normalisation.beta_eta_short)
  #> are_variants

end