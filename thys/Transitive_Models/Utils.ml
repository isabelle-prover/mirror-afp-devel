signature Utils =
 sig
    val &&& : ('a -> 'b) * ('a -> 'c) -> 'a -> 'b * 'c
    val *** : ('a -> 'b) * ('c -> 'd) -> 'a * 'c -> 'b * 'd
    val @@ : ''a list * ''a list -> ''a list
    val --- : ''a list * ''a list -> ''a list
    val binop : term -> term -> term -> term
    val add_: term -> term -> term
    val add_to_context : string -> Proof.context -> Proof.context
    val app_: term -> term -> term
    val concat_: term -> term -> term
    val dest_apply: term -> term * term
    val dest_abs : string * typ * term -> string * term
    val dest_iff_lhs: term -> term
    val dest_iff_rhs: term -> term
    val dest_iff_tms: term -> term * term
    val dest_lhs_def: term -> term
    val dest_rhs_def: term -> term
    val dest_satisfies_tms: term -> term * term
    val dest_satisfies_frm: term -> term
    val dest_eq_tms: term -> term * term
    val dest_mem_tms: term -> term * term
    val dest_sats_frm: term -> (term * term) * term
    val dest_eq_tms': term -> term * term
    val dest_trueprop: term -> term
    val display : string -> Position.T -> (string * thm list) * Proof.context -> Proof.context
    val eq_: term -> term -> term
    val fix_vars: thm -> string list -> Proof.context -> thm
    val flat : ''a list list -> ''a list
    val formula_: term
    val freeName: term -> string
    val frees : term -> term list
    val length_: term -> term
    val list_: term -> term
    val lt_: term -> term -> term
    val map_option : ('a -> 'b) -> 'a option -> 'b option
    val mem_: term -> term -> term
    val mk_FinSet: term list -> term
    val mk_Pair: term -> term -> term
    val mk_ZFlist: ('a -> term) -> 'a list -> term
    val mk_ZFnat: int -> term
    val nat_: term
    val nth_: term -> term -> term
    val reachable : (''a -> ''a -> bool) -> ''a list -> ''a list -> ''a list
    val subset_: term -> term -> term
    val thm_concl_tm :  Proof.context -> xstring -> (Vars.key * cterm) list  * term * Proof.context
    val to_ML_list: term -> term list
    val tp: term -> term
    val var_i : string -> term
    val zip_with : ('a * 'b -> 'c) -> 'a list -> 'b list -> 'c list
  end

structure Utils : Utils =
struct
(* Smart constructors for ZF-terms *)

fun binop h t u = h $ t $ u

val mk_Pair  = binop @{const Pair}

fun mk_FinSet nil = @{const zero}
  | mk_FinSet (e :: es) = @{const cons} $ e $ mk_FinSet es

fun mk_ZFnat 0 = @{const zero}
  | mk_ZFnat n = @{const succ} $ mk_ZFnat (n-1)

fun mk_ZFlist _ nil = @{const "Nil"}
  | mk_ZFlist f (t :: ts) = @{const "Cons"} $ f t $ mk_ZFlist f ts

fun to_ML_list (@{const Nil}) = nil
  | to_ML_list (@{const Cons} $ t $ ts) = t :: to_ML_list ts
  |   to_ML_list _ = nil

fun freeName (Free (n,_)) = n
  | freeName _ = error "Not a free variable"

val app_ = binop @{const apply}

fun tp x = @{const Trueprop} $ x
fun length_ env = @{const length} $ env
val nth_ = binop @{const nth}
val add_ = binop @{const add}
val mem_ = binop @{const mem}
val subset_ = binop @{const Subset}
val lt_ = binop @{const lt}
val concat_ = binop @{const app}
val eq_ = binop @{const IFOL.eq(i)}

(* Abbreviation for sets *)
fun list_ set = @{const list} $ set
val nat_ = @{const nat}
val formula_ = @{const formula}

(** Destructors of terms **)
fun dest_eq_tms (Const (@{const_name IFOL.eq},_) $ t $ u) = (t, u)
  | dest_eq_tms t = raise TERM ("dest_eq_tms", [t])

fun dest_mem_tms (@{const mem} $ t $ u) = (t, u)
  | dest_mem_tms t = raise TERM ("dest_mem_tms", [t])


fun dest_eq_tms' (Const (@{const_name Pure.eq},_) $ t $ u) = (t, u)
  | dest_eq_tms' t = raise TERM ("dest_eq_tms", [t])

val dest_lhs_def = #1 o dest_eq_tms'
val dest_rhs_def = #2 o dest_eq_tms'

fun dest_apply (@{const apply} $ t $ u) = (t,u)
  | dest_apply t = raise TERM ("dest_applies_op", [t])

fun dest_satisfies_tms (@{const Formula.satisfies} $ A $ f) = (A,f)
  | dest_satisfies_tms t = raise TERM ("dest_satisfies_tms", [t]);

val dest_satisfies_frm = #2 o dest_satisfies_tms

fun dest_sats_frm t = t |> dest_eq_tms |> #1 |> dest_apply |>> dest_satisfies_tms ;

fun dest_trueprop (@{const IFOL.Trueprop} $ t) = t
  | dest_trueprop t = t

fun dest_iff_tms (@{const IFOL.iff} $ t $ u) = (t, u)
  | dest_iff_tms t = raise TERM ("dest_iff_tms", [t])

val dest_iff_lhs = #1 o dest_iff_tms
val dest_iff_rhs = #2 o dest_iff_tms

fun thm_concl_tm ctxt thm_ref =
  let
    val thm = Proof_Context.get_thm ctxt thm_ref
    val thm_vars = rev (Term.add_vars (Thm.full_prop_of thm) [])
    val (((_,inst),thm_tms),ctxt1) = Variable.import true [thm] ctxt
    val vars = map (fn v => (v, the (Vars.lookup inst v))) thm_vars
  in
    (vars, thm_tms |> hd |> Thm.concl_of, ctxt1)
end

fun fix_vars thm vars ctxt = let
  val (_, ctxt1) = Variable.add_fixes vars ctxt
  in singleton (Proof_Context.export ctxt1 ctxt) thm
end

fun display kind pos (thms,thy) =
  let val _ = Proof_Display.print_results true pos thy ((kind,""),[thms])
  in thy
end

(* lists as sets *)

infix 6 @@
fun op @@ (xs, ys) = union (op =) ys xs

fun flat xss = fold (curry op @@) xss []

infix 6 ---
fun op --- (xs, ys) = subtract (op =) ys xs

(* function product *)
infix 6 &&&
fun op &&& (f, g) = fn x => (f x, g x)

infix 6 ***
fun op *** (f, g) = fn (x, y) => (f x, g y)

(* add variable to context *)
fun add_to_context v c = if Variable.is_fixed c v then c else #2 (Variable.add_fixes [v] c)

(* get free variables of a term *)
fun frees t = fold_aterms (fn t => if is_Free t then cons t else I) t []

(* closure of a set wrt a preorder *)
(* the preorder is the reflexive-transitive closure of the given relation p *)
(* u represents the universe, and xs represents the starting points *)
(* [xs]_{p,u} = { v \<in> u . \<exists> x \<in> xs . p*(x, v) }*)
fun reachable p u xs =
  let
    val step = map (fn x => filter (p x) (u --- xs)) xs |> flat
    val acc = if null step then [] else reachable p (u --- xs) step
  in
    xs @@ acc
  end

fun zip_with _ [] _ = []
  | zip_with _ _ [] = []
  | zip_with f (x :: xs) (y :: ys) = f (x, y) :: zip_with f xs ys

fun var_i s = Free (s, @{typ "i"})

fun map_option f (SOME a) = SOME (f a)
  | map_option _ NONE = NONE

fun dest_abs (v, ty, t) = (v, Term.subst_bound ((Free (v, ty)), t))

end
