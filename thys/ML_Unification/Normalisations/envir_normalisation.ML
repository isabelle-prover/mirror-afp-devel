(*  Title:      ML_Unification/envir_normalisation.ML
    Author:     Kevin Kappelmann

Normalisations with respect to an environment. Adapted and generalised from envir.ML
*)
signature ENVIR_NORMALISATION =
sig
  (* types *)
  type type_normaliser = Type.tyenv -> typ -> typ
  val norm_type_match : type_normaliser
  val norm_type_unif : type_normaliser

  (* terms *)
  type term_type_normaliser = Type.tyenv -> Term_Normalisation.term_normaliser
  val norm_term_types : type_normaliser -> term_type_normaliser
  type term_normaliser = Envir.env -> Term_Normalisation.term_normaliser

  (** matching **)
  val norm_term_types_match : term_type_normaliser
  (*without beta-normalisation*)
  val norm_term_match : term_normaliser
  val eta_short_norm_term_match : term_normaliser
  (*with beta-normalisation*)
  val beta_norm_term_match : term_normaliser
  val beta_eta_short_norm_term_match : term_normaliser

  (** unification **)
  val norm_term_types_unif : term_type_normaliser
  (*without beta-normalisation*)
  val norm_term_unif : term_normaliser
  val eta_short_norm_term_unif : term_normaliser
  (*with beta-normalisation*)
  val beta_norm_term_unif : term_normaliser
  val beta_eta_short_norm_term_unif : term_normaliser

  (* theorems *)
  type thm_normaliser = Proof.context -> Envir.env -> thm -> thm
  type thm_type_normaliser = thm_normaliser

  val norm_thm_types : type_normaliser -> thm_normaliser
  val norm_thm_types_match : thm_normaliser
  val norm_thm_types_unif : thm_normaliser
  val norm_thm : type_normaliser -> term_normaliser -> thm_normaliser
  val norm_thm_match : thm_normaliser
  val norm_thm_unif : thm_normaliser
  val eta_short_norm_thm : type_normaliser -> term_normaliser -> thm_normaliser
  val eta_short_norm_thm_match : thm_normaliser
  val eta_short_norm_thm_unif : thm_normaliser
  (*with beta-normalisation and eta-contraction*)
  val beta_eta_short_norm_thm : type_normaliser -> term_normaliser -> thm_normaliser
  val beta_eta_short_norm_thm_match : thm_normaliser
  val beta_eta_short_norm_thm_unif : thm_normaliser

end

structure Envir_Normalisation : ENVIR_NORMALISATION =
struct

(* types *)
type type_normaliser = Type.tyenv -> typ -> typ

val norm_type_match = Envir.subst_type
val norm_type_unif = Envir.norm_type

(* terms *)
type term_type_normaliser = Type.tyenv -> Term_Normalisation.term_normaliser
fun norm_term_types norm_type = map_types o norm_type

type term_normaliser = Envir.env -> Term_Normalisation.term_normaliser

(** matching **)
val norm_term_types_match = norm_term_types norm_type_match

fun norm_abs_same2 normT norm (a, T, body) =
  Abs (a, normT T, Same.commit norm body)
  handle Same.SAME => Abs (a, T, norm body)

fun norm_abs_comb_same beta_norm norm (abs_args as (_, _, body)) arg = if beta_norm
  then Same.commit norm (subst_bound (arg, body))
  else let val f = Abs abs_args
    in (norm f $ Same.commit norm arg handle Same.SAME => f $ norm arg) end

fun norm_comb_same beta_norm norm f t = (case norm f of
    (nf as Abs (_, _, body)) => if beta_norm
      then Same.commit norm (subst_bound (t, body))
      else nf $ Same.commit norm t
  | nf => nf $ Same.commit norm t)
  handle Same.SAME => f $ norm t

fun norm_term_match1 beta_norm tenv : term Same.operation =
  let
    fun norm (Var v) = (case Envir.lookup1 tenv v of
          SOME u => u
        | NONE => raise Same.SAME)
      | norm (Abs (a, T, body)) = Abs (a, T, norm body)
      | norm (Abs abs_args $ t) = norm_abs_comb_same beta_norm norm abs_args t
      | norm (f $ t) = norm_comb_same beta_norm norm f t
      | norm _ = raise Same.SAME
  in norm end

fun norm_term_match2 beta_norm (Envir.Envir {tenv, tyenv, ...}) : term Same.operation =
  let
    val normT = Envir.subst_type_same tyenv
    fun norm (Const (a, T)) = Const (a, normT T)
      | norm (Free (a, T)) = Free (a, normT T)
      | norm (v as Var (xi, T)) =
          let
            fun lookup v = (case Envir.lookup1 tenv (dest_Var v) of
                SOME u => u
              | NONE => raise Same.SAME)
          in
            (normT T |> (fn T => Same.commit lookup (Var (xi, T))))
            handle Same.SAME => lookup v
          end
      | norm (Abs args) = norm_abs_same2 normT norm args
      | norm (Abs abs_args $ t) = norm_abs_comb_same beta_norm norm abs_args t
      | norm (f $ t) = norm_comb_same beta_norm norm f t
      | norm _ = raise Same.SAME
  in norm end

fun norm_term_match_same beta_norm (envir as Envir.Envir {tenv, tyenv, ...}) =
  if Vartab.is_empty tyenv then norm_term_match1 beta_norm tenv
  else norm_term_match2 beta_norm envir

fun norm_term_match env = Same.commit (norm_term_match_same false env)
fun beta_norm_term_match env = Same.commit (norm_term_match_same true env)
fun eta_short_norm_term_match env = norm_term_match env
  #> Term_Normalisation.eta_short
fun beta_eta_short_norm_term_match env = beta_norm_term_match env
  #> Term_Normalisation.eta_short

(** unification **)
val norm_term_types_unif = norm_term_types norm_type_unif

fun norm_type_unif_same tyenv : typ Same.operation =
  let
    fun norm (Type (a, Ts)) = Type (a, Same.map norm Ts)
      | norm (TFree _) = raise Same.SAME
      | norm (TVar v) =
          (case Type.lookup tyenv v of
            SOME U => Same.commit norm U
          | NONE => raise Same.SAME)
  in norm end

fun norm_term_unif1 beta_norm tenv : term Same.operation =
  let
    fun norm (Var v) = (case Envir.lookup1 tenv v of
          SOME u => Same.commit norm u
        | NONE => raise Same.SAME)
      | norm (Abs (a, T, body)) = Abs (a, T, norm body)
      | norm (Abs abs_args $ t) = norm_abs_comb_same beta_norm norm abs_args t
      | norm (f $ t) = norm_comb_same beta_norm norm f t
      | norm _ = raise Same.SAME
  in norm end

fun norm_term_unif2 beta_norm (envir as Envir.Envir {tyenv, ...}) : term Same.operation =
  let
    val normT = norm_type_unif_same tyenv
    fun norm (Const (a, T)) = Const (a, normT T)
      | norm (Free (a, T)) = Free (a, normT T)
      | norm (Var (xi, T)) = (case Envir.lookup envir (xi, T) of
          SOME u => Same.commit norm u
        | NONE => Var (xi, normT T))
      | norm (Abs args) = norm_abs_same2 normT norm args
      | norm (Abs abs_args $ t) = norm_abs_comb_same beta_norm norm abs_args t
      | norm (f $ t) = norm_comb_same beta_norm norm f t
      | norm _ = raise Same.SAME
  in norm end

fun norm_term_unif_same beta_norm (envir as Envir.Envir {tenv, tyenv, ...}) =
  if Vartab.is_empty tyenv then norm_term_unif1 beta_norm tenv
  else norm_term_unif2 beta_norm envir

fun norm_term_unif env = Same.commit (norm_term_unif_same false env)
fun beta_norm_term_unif env = Same.commit (norm_term_unif_same true env)
fun eta_short_norm_term_unif env = norm_term_unif env
  #> Term_Normalisation.eta_short
fun beta_eta_short_norm_term_unif env = beta_norm_term_unif env
  #> Term_Normalisation.eta_short

type thm_normaliser = Proof.context -> Envir.env -> thm -> thm
type thm_type_normaliser = thm_normaliser

(** theorems **)

(*collect and normalise TVars of a term*)
fun collect_norm_types norm_type ctxt tyenv t =
  let
    val norm_type' = norm_type tyenv
    fun prep_type_entry x = (x, Thm.ctyp_of ctxt (norm_type' (TVar x)))
  in
    fold_types (fold_atyps (fn TVar v => TVars.add (prep_type_entry v) | _ => I)) t
    |> TVars.build
  end

(*collect and normalise Vars of a term*)
fun collect_norm_terms norm_type norm_term ctxt (env as Envir.Envir {tyenv,...}) t =
  let
    val norm_type' = norm_type tyenv
    val norm_term' = norm_term env
    fun prep_term_entry (x as (n, T)) = ((n, norm_type' T), Thm.cterm_of ctxt (norm_term' (Var x)))
  in
    fold_aterms (fn Var v => Vars.add (prep_term_entry v) | _ => I) t
    |> Vars.build
  end

(*normalise types of a theorem*)
fun norm_thm_types norm_types ctxt (Envir.Envir {tyenv, ...}) thm =
  let
    val prop = Thm.full_prop_of thm
    val type_inst = collect_norm_types norm_types ctxt tyenv prop
    val inst = (type_inst, Vars.empty)
  in Thm.instantiate inst thm end

val norm_thm_types_match = norm_thm_types norm_type_match
val norm_thm_types_unif = norm_thm_types norm_type_unif

(*normalise a theorem*)
fun norm_thm norm_types norm_terms ctxt (env as Envir.Envir {tyenv,...}) thm =
  let
    val prop = Thm.full_prop_of thm
    val type_inst = collect_norm_types norm_types ctxt tyenv prop
    val term_inst = collect_norm_terms norm_types norm_terms ctxt env prop
    val inst = (type_inst, term_inst)
  in Thm.instantiate inst thm end

val norm_thm_match = norm_thm norm_type_match norm_term_match
val norm_thm_unif = norm_thm norm_type_unif norm_term_unif

fun eta_short_norm_thm norm_types norm_terms ctxt env =
  norm_thm norm_types norm_terms ctxt env
  #> Conv.fconv_rule Thm.eta_conversion

val eta_short_norm_thm_match = eta_short_norm_thm norm_type_match norm_term_match
val eta_short_norm_thm_unif = eta_short_norm_thm norm_type_unif norm_term_unif

fun beta_eta_short_norm_thm norm_types norm_terms ctxt env =
  norm_thm norm_types norm_terms ctxt env
  #> Conv.fconv_rule Drule.beta_eta_conversion

val beta_eta_short_norm_thm_match = beta_eta_short_norm_thm norm_type_match norm_term_match
val beta_eta_short_norm_thm_unif = beta_eta_short_norm_thm norm_type_unif norm_term_unif

end
