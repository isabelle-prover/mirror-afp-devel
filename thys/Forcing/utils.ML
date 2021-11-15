signature UTILS =
 sig
    val add_: term -> term -> term
    val app_: term -> term -> term
    val concat_: term -> term -> term
    val dest_apply: term -> term * term
    val dest_iff_lhs: term -> term
    val dest_iff_rhs: term -> term
    val dest_iff_tms: term -> term * term
    val dest_lhs_def: term -> term
    val dest_rhs_def: term -> term
    val dest_satisfies_tms: term -> term * term
    val dest_satisfies_frm: term -> term
    val dest_eq_tms: term -> term * term
    val dest_sats_frm: term -> (term * term) * term
    val dest_trueprop: term -> term
    val eq_: term -> term -> term
    val fix_vars: thm -> string list -> Proof.context -> thm
    val formula_: term
    val freeName: term -> string
    val isFree: term -> bool
    val length_: term -> term
    val list_: term -> term
    val lt_: term -> term -> term
    val mem_: term -> term -> term
    val mk_FinSet: term list -> term
    val mk_Pair: term -> term -> term
    val mk_ZFlist: ('a -> term) -> 'a list -> term
    val mk_ZFnat: int -> term
    val nat_: term
    val nth_: term -> term -> term
    val subset_: term -> term -> term
    val thm_concl_tm :  Proof.context -> xstring -> 
        cterm Vars.table * term * Proof.context
    val to_ML_list: term -> term list
    val tp: term -> term
  end

structure Utils : UTILS =
struct 
(* Smart constructors for ZF-terms *)

fun mk_Pair t u = \<^Const>\<open>Pair for t u\<close>

fun mk_FinSet nil = \<^Const>\<open>zero\<close>
  | mk_FinSet (e :: es) = \<^Const>\<open>cons for e \<open>mk_FinSet es\<close>\<close>

fun mk_ZFnat 0 = \<^Const>\<open>zero\<close>
  | mk_ZFnat n = \<^Const>\<open>succ for \<open>mk_ZFnat (n-1)\<close>\<close>

fun mk_ZFlist _ nil = \<^Const>\<open>Nil\<close>
  | mk_ZFlist f (t :: ts) = \<^Const>\<open>Cons for \<open>f t\<close> \<open>mk_ZFlist f ts\<close>\<close>

fun to_ML_list \<^Const_>\<open>Nil\<close> = []
  | to_ML_list \<^Const_>\<open>Cons for t ts\<close> = t :: to_ML_list ts
  | to_ML_list _ = []

fun isFree (Free _) = true
  | isFree _ = false

fun freeName (Free (x, _)) = x
  | freeName _ = error "Not a free variable"

fun app_ t u = \<^Const>\<open>apply for t u\<close>

fun tp x = \<^Const>\<open>Trueprop for x\<close>
fun length_ env = \<^Const>\<open>length for env\<close>
fun nth_ t u = \<^Const>\<open>nth for t u\<close>
fun add_ t u = \<^Const>\<open>add for t u\<close>
fun mem_ t u = \<^Const>\<open>mem for t u\<close>
fun subset_ t u = \<^Const>\<open>Subset for t u\<close>
fun lt_ t u = \<^Const>\<open>lt for t u\<close>
fun concat_ t u = \<^Const>\<open>app for t u\<close>
fun eq_ t u = \<^Const>\<open>IFOL.eq \<^Type>\<open>i\<close> for t u\<close>

(* Abbreviation for sets *)
fun list_ t = \<^Const>\<open>list for t\<close>
val nat_ = \<^Const>\<open>nat\<close>
val formula_ = \<^Const>\<open>formula\<close>

(** Destructors of terms **)
fun dest_eq_tms \<^Const_>\<open>IFOL.eq _ for t u\<close> = (t, u)
  | dest_eq_tms t = raise TERM ("dest_eq_tms", [t])

fun dest_lhs_def \<^Const_>\<open>Pure.eq _ for x _\<close> = x
  | dest_lhs_def t = raise TERM ("dest_lhs_def", [t])

fun dest_rhs_def \<^Const_>\<open>Pure.eq _ for _ y\<close> = y
  | dest_rhs_def t = raise TERM ("dest_rhs_def", [t])


fun dest_apply \<^Const_>\<open>apply for t u\<close> = (t,u)
  | dest_apply t = raise TERM ("dest_applies_op", [t])

fun dest_satisfies_tms \<^Const_>\<open>Formula.satisfies for A f\<close> = (A,f)
  | dest_satisfies_tms t = raise TERM ("dest_satisfies_tms", [t]);

val dest_satisfies_frm = #2 o dest_satisfies_tms

fun dest_sats_frm t = t |> dest_eq_tms |> #1 |> dest_apply |>> dest_satisfies_tms ;

fun dest_trueprop \<^Const_>\<open>Trueprop for t\<close> = t
  | dest_trueprop t = t

fun dest_iff_tms \<^Const_>\<open>iff for t u\<close> = (t, u)
  | dest_iff_tms t = raise TERM ("dest_iff_tms", [t])

val dest_iff_lhs = #1 o dest_iff_tms
val dest_iff_rhs = #2 o dest_iff_tms

fun thm_concl_tm ctxt thm_ref =
  let
    val (((_,vars),thm_tms),ctxt1) = Variable.import true [Proof_Context.get_thm ctxt thm_ref] ctxt
  in (vars, thm_tms |> hd |> Thm.concl_of, ctxt1)
end

fun fix_vars thm vars ctxt = let
  val (_, ctxt1) = Variable.add_fixes vars ctxt
  in singleton (Proof_Context.export ctxt1 ctxt) thm
end

end;
