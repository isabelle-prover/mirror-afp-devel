(*  Title:      ML_Unification/higher_order_pattern_unification.ML
    Author:     Tobias Nipkow, Christine Heinzelmann, Stefan Berghofer, and
                Kevin Kappelmann TU Muenchen

Higher-Order Patterns due to Tobias Nipkow.
E-Unification and theorem construction due to Kevin Kappelmann.

See also:
Tobias Nipkow. Functional Unification of Higher-Order Patterns.
In Proceedings of the 8th IEEE Symposium Logic in Computer Science, 1993.

TODO: optimize red by special-casing it
*)
signature HIGHER_ORDER_PATTERN_UNIFICATION =
sig
  include HAS_LOGGER

  (* e-matching *)
  val e_match : Unification_Base.type_matcher -> Unification_Base.matcher ->
    Unification_Base.e_matcher
  val match : Unification_Base.matcher
  val norms_match : Unification_Base.normalisers

  (* e-unification *)
  val e_unify : Unification_Base.type_unifier -> Unification_Base.unifier ->
    Unification_Base.e_unifier
  val unify : Unification_Base.unifier
  val norms_unify : Unification_Base.normalisers
end

structure Higher_Order_Pattern_Unification : HIGHER_ORDER_PATTERN_UNIFICATION =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Higher_Order_Pattern_Unification"

(* shared utils *)
structure Util = Unification_Util
structure Norm = Envir_Normalisation

exception FALLBACK

(*check if sequence is empty or raise FALLBACK exception*)
fun seq_try sq = General_Util.seq_try FALLBACK sq

(*predicate: downto0 (is, n) <=> is = [n, n - 1, ..., 0]*)
fun downto0 ([], n) = n = ~1
  | downto0 (i :: is, n) = i = n andalso downto0 (is, n - 1)

fun mkabs (binders, is, t) =
  let fun abstract i acc =
    let val ((x, T), _) = nth binders i
    in Abs (x, T, acc) end
  in fold_rev abstract is t end

exception IDX

fun idx [] _ = raise IDX
  | idx (i :: is) j = if i = j then length is else idx is j

fun ints_of bs =
  (*collects arguments and checks if they are all distinct, bound variables*)
  let fun dest_check (Bound i) acc =
          if member (op =) acc i then raise Unification_Base.PATTERN else i :: acc
        | dest_check _ _ = raise Unification_Base.PATTERN
  in fold_rev dest_check bs [] end

fun app (s, []) = s
  | app (s, (i :: is)) = app (s $ Bound i, is)

(* matching *)

fun mapbnd f =
  let fun mpb d (Bound i) = if i < d then Bound i else Bound (f (i - d) + d)
        | mpb d (Abs (s, T, t)) = Abs (s, T, mpb (d + 1) t)
        | mpb d (u1 $ u2) = (mpb d u1) $ (mpb d u2)
        | mpb _ atom = atom
  in mpb 0 end

fun red (Abs (_, _, s)) (i :: is) js = red s is (i :: js)
  | red t [] [] = t
  | red t is jn = app (mapbnd (nth jn) t, is)

exception OPEN_TERM

fun match_bind (tenv, binders, ixn, T, is, t) =
  let val js = loose_bnos t
  in
    if null is then
      if null js then Vartab.update_new (ixn, (T, t)) tenv
      else raise OPEN_TERM
    else if subset (op =) (js, is) then
      let val t' = if downto0 (is, length binders - 1) then t else mapbnd (idx is) t
      in Vartab.update_new (ixn, (T, mkabs (binders, is, t'))) tenv end
    else raise OPEN_TERM
  end


(** higher-order pattern E-unification **)
val norms_match = Util.beta_eta_short_norms_match

fun e_match match_types match_theory_pattern match_theory_fail binders ctxt (pt as (p, t)) env =
  let
    val norm_pt = apfst o (#norm_term norms_match)
    fun rigid_rigid ctxt p n env = (*normalise the types in rigid-rigid cases*)
      Util.rigid_rigid Norm.norm_term_types_match match_types ctxt p n env |> seq_try
      handle Unification_Base.UNIF => Seq.empty (*types do not match*)
    (*generated theorem is already normalised wrt. the resulting environment*)
    fun match binders ctxt (pt as (p, t)) (env as Envir.Envir {maxidx, tenv, tyenv}) =
      let
        (*call match_theory on failure*)
        fun handle_failure match_theory failure_msg =
          (@{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
              failure_msg (),
              Pretty.block [
                Pretty.str "Calling theory matcher for ",
                Util.pretty_unif_problem ctxt (norm_pt env pt)
              ]
            ] |> Pretty.block |> Pretty.string_of);
          match_theory binders ctxt pt env)
      in
        (case pt of
          (Abs (np, _, tp), Abs (nt, Tt, tt)) =>
            let val name = if np = "" then nt else np
            in
              Util.abstract_abstract (K I) match binders ctxt name Tt (tp, tt) env
              |> seq_try
            end
        (*eta-expand on the fly*)
        | (Abs (np, Tp, tp), _) =>
            let val Tp' = Envir.subst_type tyenv Tp
            in
              Util.abstract_abstract (K I) match binders ctxt np Tp'
                (tp, incr_boundvars 1 t $ Bound 0) env
              |> seq_try
            end
        | (_, Abs (nt, Tt, tt)) =>
            Util.abstract_abstract (K I) match binders ctxt nt Tt
              (incr_boundvars 1 p $ Bound 0, tt) env
            |> seq_try
        | (Bound i, Bound j) => Util.bound_bound binders ctxt (i, j) |> Seq.map (pair env)
        | (Free _, Free g) => rigid_rigid ctxt p g env
        | (Const _, Const d) => rigid_rigid ctxt p d env
        | _ => case strip_comb p of
            (Var (x, T), ps) =>
              let
                val is = ints_of ps
                val T' = Norm.norm_type_match tyenv T
              in
                case Envir.lookup1 tenv (x, T') of
                  NONE =>
                    ((let
                      val tenv' = match_bind (tenv, binders, x, T', is, t)
                      val env' = Envir.Envir {maxidx=maxidx, tenv=tenv', tyenv=tyenv}
                      val t' = Binders.replace_binders binders t
                    in Seq.single (env', Unification_Base.reflexive_term ctxt t') end)
                    handle OPEN_TERM => (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
                        Pretty.str "Failed to unify (open term) ",
                        Util.pretty_unif_problem ctxt (norm_pt env pt)
                      ] |> Pretty.string_of);
                      Seq.empty))
                | SOME ph' =>
                    if Envir.aeconv (red ph' is [], t) then
                      Seq.single (env, Unification_Base.reflexive_term ctxt
                        (Binders.replace_binders binders t))
                    else raise FALLBACK
              end
          | (ph, ps) =>
              let val (th, ts) = strip_comb t
              in case (ph, th) of
                  (Abs _, _) => raise Unification_Base.PATTERN
                | (_, Abs _) => raise Unification_Base.PATTERN
                | _ => if null ps orelse null ts then raise FALLBACK
                    else (*Note: types of theorems are already normalised
                      ==> we pass the identity type normaliser*)
                      Util.strip_comb_strip_comb (K o K I) match binders ctxt (ph, th) (ps, ts) env
                      |> seq_try
              end)
        handle FALLBACK => handle_failure match_theory_fail
          (fn _ => Pretty.str "Higher-order pattern matching failed.")
        | Unification_Base.PATTERN => handle_failure match_theory_pattern
          (fn _ => Pretty.str "Terms not in Pattern fragment.")
      end
    val binder_types = Binders.binder_types binders
  in
    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Higher-order pattern matching ",
        Util.pretty_unif_problem ctxt (norm_pt env pt)
      ] |> Pretty.string_of);
    match_types ctxt (Envir.fastype env binder_types p, fastype_of1 (binder_types, t)) env
    |> match binders ctxt pt)
    handle Unification_Base.UNIF => Seq.empty (*types do not match*)
  end


(*standard higher-order pattern matching*)
val match = e_match Util.match_types Unification_Combinator.fail_match
  Unification_Combinator.fail_match

(*unification*)

fun string_of_term ctxt env binders t =
  (map (Free o fst) binders, t)
  |> subst_bounds
  |> Norm.norm_term_unif env
  |> Syntax.string_of_term ctxt

fun bname binders = fst o fst o nth binders
fun bnames binders is = map (bname binders) is |> space_implode " "

fun proj_fail ctxt (env, binders, F, _, is, t) reason =
  @{log Logger.DEBUG} ctxt (fn _ =>
    let
      val f = Term.string_of_vname F
      val xs = bnames binders is
      val u = string_of_term ctxt env binders t
    in
      cat_lines [
        "Cannot unify variable " ^ f ^ " (depending on bound variables [" ^ xs ^ "])",
        "with term " ^ u,
        reason ()
      ]
    end)

fun proj_fail_unif ctxt (params as (_, binders, _, _, is, t)) =
  let
    fun reason () =
      let val ys = bnames binders (subtract (op =) is (loose_bnos t))
      in "Term contains additional bound variable(s) " ^ ys end
  in proj_fail ctxt params reason end

fun proj_fail_type_app ctxt (params as (env, binders, _, _, _, _)) var_app =
  let
    fun reason () =
      let val var_app = string_of_term ctxt env binders var_app
      in "Projection " ^ var_app ^ " is not well-typed." end
  in proj_fail ctxt params reason end

fun ocheck_fail ctxt (F, t, binders, env) =
  @{log Logger.DEBUG} ctxt (fn _ => cat_lines [
      "Variable " ^ Term.string_of_vname F ^ " occurs in term",
      string_of_term ctxt env binders t,
      "Cannot unify!"
    ])

fun occurs (F, t, env) =
  let fun occ (Var (G, T)) = (case Envir.lookup env (G, T) of
            SOME t => occ t
          | NONE => F = G)
        | occ (t1 $ t2) = occ t1 orelse occ t2
        | occ (Abs (_, _, t)) = occ t
        | occ _ = false
  in occ t end

fun ints_of' env ts = ints_of (map (Envir.head_norm env) ts)

(*split_type ([T1,....,Tn]---> T) n = ([Tn,...,T1], T)*)
fun split_type t n =
  let fun split (T, 0, Ts) = (Ts, T)
        | split (Type ("fun", [T1, T2]), n, Ts) = split (T2, n - 1, T1 :: Ts)
        | split _ = raise Fail "split_type"
  in split (t, n, []) end

fun type_of_G (Envir.Envir {tyenv,...}) (T, n, is) =
  let val (Ts, U) = split_type (Norm.norm_type_unif tyenv T) n
  in map (nth Ts) is ---> U end

fun mk_hnf (binders, is, G, js) = mkabs (binders, is, app (G, js))

fun mk_new_hnf (env, binders, is, F as (a, _), T, js) =
  let val (env', G) = Envir.genvar a (env, type_of_G env (T, length is, js))
  in Envir.update ((F, T), mk_hnf (binders, is, G, js)) env' end

(*mk_proj_list is = [ |is| - k - 1 | 0 <= k < |is| and is[k] >= 0 ]*)
fun mk_proj_list is =
  let fun mk (SOME _) (acc, j) = (j :: acc, j + 1)
        | mk NONE (acc, j) = (acc, j + 1)
  in fold_rev mk is ([], 0) |> fst end

fun proj ctxt (s, env, binders, is) =
  let
    fun trans d i = if i < d then i else idx is (i - d) + d
    fun pr (s, env, d, binders) = (case Envir.head_norm env s of
        Abs (a, T, t) =>
          let
            val (binder, _) = Binders.fix_binder (a, T) ctxt
            val (t', env') = pr (t, env, d + 1, binder :: binders)
          in (Abs (a, T, t'), env') end
      | t => (case strip_comb t of
          (c as Const _, ts) =>
            let val (ts', env') = prs (ts, env, d, binders)
            in (list_comb (c, ts'), env') end
        | (f as Free _, ts) =>
            let val (ts', env') = prs (ts, env, d, binders)
            in (list_comb (f, ts'), env') end
        | (Bound i, ts) =>
            let
              val j = trans d i
              val (ts', env') = prs (ts, env, d, binders)
            in (list_comb (Bound j, ts'), env') end
        | (Var (F as (a, _), Fty), ts) =>
            let
              val js = ints_of' env ts
              val js' = map (try (trans d)) js
              val ks = mk_proj_list js'
              val ls = map_filter I js'
              val Hty = type_of_G env (Fty, length js, ks)
              val (env', H) = Envir.genvar a (env, Hty)
              val env'' = Envir.update ((F, Fty), mk_hnf (binders, js, H, ks)) env'
            in (app (H, ls), env'') end
        | _  => raise Unification_Base.PATTERN))
    and prs (s :: ss, env, d, binders) =
          let
            val (s', env1) = pr (s, env, d, binders)
            val (ss', env2) = prs (ss, env1, d, binders)
          in (s' :: ss', env2) end
      | prs ([], env, _, _) = ([], env)
  in
    if downto0 (is, length binders - 1) then (s, env)
    else pr (s, env, 0, binders)
  end

(*mk_ff_list (is, js) = [ |is| - k - 1 | 0 <= k < |is| and is[k] = js[k] ]*)
fun mk_ff_list (is,js) =
    let fun mk ([], [], _) = []
          | mk (i :: is, j :: js, k) =
              if i = j then k :: mk (is, js, k - 1)
              else mk (is, js, k - 1)
          | mk _ = raise Fail "mk_ff_list"
    in mk (is, js, length is - 1) end;

fun app_free (Envir.Envir {tyenv,...}) binders n T is =
  let val norm_type = Norm.norm_type_unif tyenv
  in list_comb (Var (n, norm_type T), map (map_types norm_type o Binders.nth_binder_data binders) is) end

fun flexflex1 unify_types ctxt (env, binders, F, Fty, Fty', is, js) =
  let
    val env' = unify_types ctxt (Fty, Fty') env
    val thm = app_free env binders F Fty is |> Unification_Base.reflexive_term ctxt
  in
    if is = js then (env', thm)
    else
      let
        val ks = mk_ff_list (is, js)
        val env'' = mk_new_hnf (env', binders, is, F, Fty, ks)
      in (env'', thm) end
  end

fun flexflex2 unify_types ctxt (env, binders, F, Fty, is, G, Gty, js) =
  let
    val var_app = app_free env binders F Fty is
    val binder_types = Binders.binder_types binders
    val env' = unify_types ctxt
      (apply2 (Envir.fastype env binder_types) (var_app, app (Var (G, Gty), js))) env
    val thm = Unification_Base.reflexive_term ctxt var_app
    fun ff (F, Fty, is, G as (a, _), Gty, js) =
      if subset (op =) (js, is) then
        let
          val t = mkabs (binders, is, app (Var (G, Gty), map (idx is) js))
          val env'' = Envir.update ((F, Fty), t) env'
        in (env'', thm) end
      else
        let
          val ks = inter (op =) js is
          val Hty = type_of_G env' (Fty, length is, map (idx is) ks)
          val (env'', H) = Envir.genvar a (env', Hty)
          fun lam is = mkabs (binders, is, app (H, map (idx is) ks))
          val env''' =
            Envir.update ((F, Fty), lam is) env''
            |> Envir.update ((G, Gty), lam js)
        in (env''', thm) end
  in
    if is_less (Term_Ord.indexname_ord (G, F)) then ff (F, Fty, is, G, Gty, js)
    else ff (G, Gty, js, F, Fty, is)
  end

fun flexrigid unify_types ctxt (params as (env, binders, F, Fty, is, t)) =
  if occurs (F, t, env) then (ocheck_fail ctxt (F, t, binders, env); raise FALLBACK)
  else
    let val var_app = app_free env binders F Fty is
    in
      let
        val binder_types = Binders.binder_types binders
        val env' = unify_types ctxt
          (apply2 (Envir.fastype env binder_types) (var_app, t)) env
        val (u, env'') = proj ctxt (t, env', binders, is)
        val env''' = Envir.update ((F, Fty), mkabs (binders, is, u)) env''
        val thm = Unification_Base.reflexive_term ctxt var_app
      in (env''', thm) end
      handle IDX => (proj_fail_unif ctxt params; raise OPEN_TERM)
      | TYPE _ => (proj_fail_type_app ctxt params var_app; raise Unification_Base.UNIF)
    end

(** higher-order pattern E-unification **)
val norms_unify = Util.beta_eta_short_norms_unif

fun e_unify unify_types unify_theory_pattern unify_theory_fail binders ctxt st env =
  let
    fun unif binders ctxt st env =
      let
        val (st' as (s', t')) = apply2 (Envir.head_norm env) st
        fun rigid_rigid ctxt t n env = (*we do not normalise types in base cases*)
          Util.rigid_rigid (K I) unify_types ctxt t n env |> seq_try
          handle Unification_Base.UNIF => Seq.empty (*types do not match*)
        (*call unify_theory on failure*)
        fun handle_failure unify_theory failure_msg =
          (@{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
            failure_msg (),
            Pretty.block [
              Pretty.str "Calling theory unifier for ",
              Util.pretty_unif_problem ctxt st'
            ]
          ] |> Pretty.block |> Pretty.string_of);
          (*Note: st' is already normalised*)
          unify_theory binders ctxt st' env)
      in
        (case st' of
          (Abs (ns, Ts, ts), Abs (nt, Tt, tt)) =>
            ((let val name = if ns = "" then nt else ns
            in
              unify_types ctxt (Ts, Tt) env
              |> Util.abstract_abstract Norm.norm_term_types_unif unif binders ctxt name Ts (ts, tt)
              |> seq_try
            end)
            handle Unification_Base.UNIF => Seq.empty) (*types do not unify*)
        (*eta-expand on the fly*)
        | (Abs (ns, Ts, ts), _) =>
            ((let val st = apply2 (Envir.fastype env (Binders.binder_types binders)) st'
            in
              unify_types ctxt st env
              |> Util.abstract_abstract Norm.norm_term_types_unif unif binders ctxt ns Ts
                (ts, incr_boundvars 1 t' $ Bound 0)
              |> seq_try
            end)
            handle Unification_Base.UNIF => Seq.empty) (*types do not unify*)
        | (_, Abs _) => unif binders ctxt (t', s') env |> Seq.map (apsnd Unification_Base.symmetric)
        | (Bound i, Bound j) => Util.bound_bound binders ctxt (i, j) |> Seq.map (pair env)
        | (Free _, Free g) => rigid_rigid ctxt s' g env
        | (Const _, Const d) => rigid_rigid ctxt s' d env
        (*case distinctions on head term*)
        | _ => case apply2 strip_comb st' of
            ((Var (F, Fty), ss), (Var (G, Gty), ts)) =>
              (((if F = G then
                flexflex1 unify_types ctxt (env, binders, F, Fty, Gty, ints_of' env ss, ints_of' env ts)
              else
                flexflex2 unify_types ctxt (env, binders, F, Fty, ints_of' env ss, G, Gty, ints_of' env ts))
              |> Seq.single)
              handle Unification_Base.UNIF => Seq.empty) (*types do not unify*)
          | ((Var (F, Fty), ss), _) =>
              (flexrigid unify_types ctxt (env, binders, F, Fty, ints_of' env ss, t')|> Seq.single
              handle OPEN_TERM => Seq.empty
              | Unification_Base.UNIF => Seq.empty) (*types do not unify*)
          | (_, (Var (F, Fty), ts)) =>
              (flexrigid unify_types ctxt (env, binders, F, Fty, ints_of' env ts, s') |> Seq.single
              handle OPEN_TERM => Seq.empty
              | Unification_Base.UNIF => Seq.empty) (*types do not unify*)
          | ((sh, ss), (th, ts)) => if null ss orelse null ts then raise FALLBACK
              else (*but we have to normalise in comb cases*)
                Util.strip_comb_strip_comb Norm.norm_thm_types_unif unif binders ctxt
                  (sh, th) (ss, ts) env
                |> seq_try)
        handle FALLBACK => handle_failure unify_theory_fail
          (fn _ => Pretty.str "Higher-order pattern unification failed.")
        | Unification_Base.PATTERN => handle_failure unify_theory_pattern
          (fn _ => Pretty.str "Terms not in Pattern fragment.")
      end
    val binder_types = Binders.binder_types binders
  in
    (@{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Pretty.str "Higher-order pattern unifying ",
        Util.pretty_unif_problem ctxt (apply2 (Norm.norm_term_unif env) st)
      ]
      |> Pretty.string_of);
    unif binders ctxt st (unify_types ctxt (apply2 (Envir.fastype env binder_types) st) env))
    handle Unification_Base.UNIF => Seq.empty (*types do not unify*)
  end

(*standard higher-order pattern unification*)
val unify = e_unify Util.unify_types Unification_Combinator.fail_unify
  Unification_Combinator.fail_unify

end
