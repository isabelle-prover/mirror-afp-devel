(*  Title:      ML_Unification/first_order_unification.ML
    Author:     Kevin Kappelmann, Paul Bachmann

First-order E-unification.
*)
signature FIRST_ORDER_UNIFICATION =
sig
  include HAS_LOGGER

  (* e-matching *)
  val e_match : Unification_Base.type_matcher -> Unification_Base.e_matcher
  val match : Unification_Base.matcher
  val norms_match : Unification_Base.normalisers

  (* e-unification *)
  val e_unify : Unification_Base.type_unifier -> Unification_Base.e_unifier
  val unify : Unification_Base.unifier
  val norms_unify : Unification_Base.normalisers
end

structure First_Order_Unification : FIRST_ORDER_UNIFICATION =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "First_Order_Unification"

(* shared utils *)
structure Util = Unification_Util
structure Norm = Envir_Normalisation

exception FALLBACK

(*check if sequence is empty or raise FALLBACK exception*)
fun seq_try sq = General_Util.seq_try FALLBACK sq


(* e-matching *)

val norms_match = Util.eta_short_norms_match

(*Note: by E-matching we mean "matching modulo equalities" in the general sense,
i.e. when matching p \<equiv>? t, t may contain variables.*)
fun e_match match_types match_theory binders ctxt pt env =
  let
    val norm_pt = apfst o (#norm_term norms_match)
    fun rigid_rigid ctxt p n env = (*normalise the types in rigid-rigid cases*)
      Util.rigid_rigid Norm.norm_term_types_match match_types ctxt p n env |> seq_try
      handle Unification_Base.UNIF => Seq.empty (*types do not match*)
    (*standard first-order matcher that calls match_theory on failure;
    generated theorem is already normalised wrt. the resulting environment*)
    fun match binders ctxt (pt as (p, t)) (env as Envir.Envir {tenv, tyenv,...}) =
      (case pt of
        (Var (x, Tx), _) =>
          (case Envir.lookup1 tenv (x, Norm.norm_type_match tyenv Tx) of
            NONE =>
              if Term.is_open t then
                (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
                    Pretty.str "Failed to match (open term) ",
                    Util.pretty_unif_problem ctxt (norm_pt env pt)
                  ] |> Pretty.string_of);
                (*directly return empty sequence because the theory unifier
                cannot do anything meaningful at this point*)
                raise FALLBACK)
              else
                let val Tt = fastype_of1 (Binders.binder_types binders, t)
                in
                  ((match_types ctxt (Tx, Tt) env, Unification_Base.reflexive_term ctxt t)
                  (*insert new substitution x \<mapsto> t*)
                  |>> Envir.update ((x, Tt), t)
                  |> Seq.single)
                  handle Unification_Base.UNIF => Seq.empty (*types do not match*)
                end
          | SOME p' =>
            if Envir.aeconv (apply2 Envir.beta_norm (p', t)) then
              Seq.single (env, Unification_Base.reflexive_term ctxt t)
            else raise FALLBACK)
      | (Abs (np, Tp, tp), Abs (nt, Tt, tt)) =>
          ((let val name = if np = "" then nt else np
          in
            match_types ctxt (Tp, Tt) env
            |> Util.abstract_abstract (K I) match binders ctxt name Tt (tp, tt)
            |> seq_try
          end)
          handle Unification_Base.UNIF => Seq.empty) (*types do not match*)
      (*eta-expand on the fly*)
      | (Abs (np, Tp, tp), _) =>
          ((let val Ttarg = fastype_of1 (Binders.binder_types binders, t) |> Term.dest_funT |> fst
          in
            match_types ctxt (Tp, Ttarg) env
            |> Util.abstract_abstract (K I) match binders ctxt np Ttarg
                (tp, incr_boundvars 1 t $ Bound 0)
            |> seq_try
          end)
          handle TYPE _ => (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
              Pretty.str "First-order matching failed. Term is not of function type ",
              Util.pretty_unif_problem ctxt (norm_pt env pt)
            ]
            |> Pretty.string_of);
            Seq.empty)
          | Unification_Base.UNIF => Seq.empty) (*types do not match*)
      | (_, Abs (nt, Tt, tt)) =>
          ((let val Tp = Envir.fastype env (Binders.binder_types binders) p
          in
            match_types ctxt (Tp, fastype_of1 (Binders.binder_types binders, t)) env
            |> Util.abstract_abstract (K I) match binders ctxt nt Tt
                (incr_boundvars 1 p $ Bound 0, tt)
            |> seq_try
          end)
          handle Unification_Base.UNIF => Seq.empty) (*types do not match*)
      | (Bound i, Bound j) => Util.bound_bound binders ctxt (i, j) |> Seq.map (pair env)
      | (Free _, Free g) => rigid_rigid ctxt p g env
      | (Const _, Const d) => rigid_rigid ctxt p d env
      | (f $ x, g $ y) =>
          (*Note: types of recursive theorems are already normalised ==> we have to
          pass the identity type normaliser*)
          Util.comb_comb (K o K I) (match binders) ctxt (f, x) (g, y) env |> seq_try
      | _ => raise FALLBACK)
      handle FALLBACK =>
        (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
            Pretty.str "First-order matching failed. Calling theory matcher for ",
            Util.pretty_unif_problem ctxt (norm_pt env pt)
          ] |> Pretty.string_of);
        match_theory binders ctxt pt env)
  in
    (@{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Pretty.str "First-order matching ",
        Util.pretty_unif_problem ctxt (norm_pt env pt)
      ] |> Pretty.string_of);
    match binders ctxt pt env)
  end

(*standard first-order matching*)
val match = e_match Util.match_types Unification_Combinator.fail_match

(* e-unification *)

(*occurs check*)
fun occurs v (Var (x, _)) = x = v
  | occurs v (s $ t) = occurs v s orelse occurs v t
  | occurs v (Abs (_, _, t)) = occurs v t
  | occurs _ _ = false

val norms_unify = Util.eta_short_norms_unif

fun e_unify unify_types unify_theory binders ctxt st env =
  let
    val norm_st = apply2 o (#norm_term norms_unify)
    fun rigid_rigid ctxt t n env = (*we do not have to normalise types in rigid-rigid cases*)
      Util.rigid_rigid (K I) unify_types ctxt t n env |> seq_try
      handle Unification_Base.UNIF => Seq.empty (*types do not unify*)
    (*standard first-order unifier that calls unify_theory on failure*)
    fun unif binders ctxt (st as (s, t)) env =
      (case st of
        (Var (x, Tx), _) =>
          let val unif' = unif binders ctxt
          in
            (unif' (Envir.norm_term_same env s, t) env
            handle Same.SAME =>
              (unif' (s, Envir.norm_term_same env t) env
              handle Same.SAME =>
                if Term.is_open t then
                  (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
                      Pretty.str "Failed to unify (open term) ",
                      Util.pretty_unif_problem ctxt (norm_st env st)
                    ]
                    |> Pretty.string_of);
                  raise FALLBACK)
                else
                  let
                    val vars_eq = is_Var t andalso x = fst (dest_Var t)
                    fun update_env env =
                      (*unifying x=x ==> no new term substitution necessary*)
                      if vars_eq then env
                      (*insert new substitution x \<mapsto> t*)
                      else Envir.vupdate ((x, Tx), t) env
                  in
                    if not vars_eq andalso occurs x t then
                      (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
                          Pretty.str "Failed to unify (occurs check) ",
                          Util.pretty_unif_problem ctxt (norm_st env st)
                        ] |> Pretty.string_of);
                      raise FALLBACK)
                    else
                      ((unify_types ctxt (Tx, Envir.fastype env (Binders.binder_types binders) t) env,
                        Unification_Base.reflexive_term ctxt s)
                      |>> update_env
                      |> Seq.single)
                      handle Unification_Base.UNIF => Seq.empty (*types do not unify*)
                  end))
          end
       | (_, Var _) => unif binders ctxt (t, s) env |> Seq.map (apsnd Unification_Base.symmetric)
       | (Abs (ns, Ts, ts), Abs (nt, Tt, tt)) =>
          ((let val name = if ns = "" then nt else ns
          in
            unify_types ctxt (Ts, Tt) env
            |> Util.abstract_abstract Norm.norm_term_types_unif unif binders ctxt name Ts (ts, tt)
            |> seq_try
          end)
          handle Unification_Base.UNIF => Seq.empty) (*types do not unify*)
      (*eta-expand on the fly*)
      | (Abs (ns, Ts, ts), _) =>
          ((let val Tp = apply2 (Envir.fastype env (Binders.binder_types binders)) (s, t)
          in
            unify_types ctxt Tp env
            |> Util.abstract_abstract Norm.norm_term_types_unif unif binders ctxt ns Ts
              (ts, incr_boundvars 1 t $ Bound 0)
            |> seq_try
          end)
          handle Unification_Base.UNIF => Seq.empty) (*types do not unify*)
      | (_, Abs _) => unif binders ctxt (t, s) env |> Seq.map (apsnd Unification_Base.symmetric)
      | (Bound i, Bound j) => Util.bound_bound binders ctxt (i, j) |> Seq.map (pair env)
      | (Free _, Free g) => rigid_rigid ctxt s g env
      | (Const _, Const d) => rigid_rigid ctxt s d env
      (*we have to normalise types in comb cases*)
      | (f $ x, g $ y) =>
          Util.comb_comb Norm.norm_thm_types_unif (unif binders) ctxt (f, x) (g, y) env |> seq_try
      | _ => raise FALLBACK)
      handle FALLBACK =>
        (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
            Pretty.str "First-order unification failed. Calling theory unifier for ",
            Util.pretty_unif_problem ctxt (norm_st env st)
          ] |> Pretty.string_of);
        unify_theory binders ctxt st env)
  in
    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "First-order unifying ",
        Util.pretty_unif_problem ctxt (norm_st env st)
      ] |> Pretty.string_of);
    unif binders ctxt st env)
  end

(*standard first-order unification*)
val unify = e_unify Util.unify_types Unification_Combinator.fail_unify

end
