(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


(*
Define mutually recursive functions over a chain-complete partial order (CCPO). Also allows
arbitrary patterns on the left-hand side of equations. The only restrictions are monotonicity of
the recursive calls, and uniqueness of the patterns.

The mutual recursion is resolved using a product construction. The recursive calls are projected
out of the input tuple. To keep the size of the least fixed point managable, we use a balanced
tuple instead of a linear representation. With the projections are ~ log N, so the functional has a
size of N * N * log N (N entries in the tuple, N calls per entry, and log N constants per
projections). With a linear representtion the projections have the size 1 ... N, resulting in a
fixed point size of N * N * (N + 1) / 2: N entries with projections of the size 1 ... N.

A more important improvement is reached by only using the projections which are necessary, i.e.
only the recursive calls are represented on the functional side.
*)

signature MUTUAL_CCPO_REC =
sig

type ccpo_data = {
  typ   : typ,
  ord   : term,
  lub   : term,
  bot   : term,
  class : thm }

val string_of_ccpo_data : Proof.context -> ccpo_data -> string

val add_ccpo : string -> (Proof.context -> typ -> ccpo_data) -> Context.generic -> Context.generic
val get_ccpo : Context.generic -> (Proof.context -> typ -> ccpo_data) Symtab.table

val synth_funs   : Proof.context -> typ list * ccpo_data -> ccpo_data
val synth_prod   : Proof.context -> ccpo_data -> ccpo_data -> ccpo_data
val synth_fun    : Proof.context -> typ -> ccpo_data -> ccpo_data
val synth_flat   : Proof.context -> term -> ccpo_data
val synth_option : Proof.context -> typ -> ccpo_data
val synth_lfp    : Proof.context -> typ -> ccpo_data
val synth_gfp    : Proof.context -> typ -> ccpo_data
val synth_ccpo   : Context.generic -> string -> typ -> ccpo_data

val ccpo_bot        : ccpo_data -> term
val ccpo_mono       : ccpo_data -> ccpo_data -> term
val ccpo_fixp       : ccpo_data -> term
val ccpo_chain      : ccpo_data -> term
val ccpo_admissible : ccpo_data -> term

val mono_tac        : Proof.context -> int -> tactic

type functional = {
  binding  : binding,
  mixfix   : mixfix,
  recs     : (string * typ) list,
  params   : (string * typ) list,
  ccpo     : ccpo_data,
  rhs      : term,
  mono_tac : Proof.context -> int -> tactic }

type result = {
  consts: term list,
  simps: (string * thm list) list,
  inducts: (string * thm list)
}

val mutual_ccpo_fixed_point :
  functional list -> Proof.context -> (term list * thm list * thm * thm list) * Proof.context

val fixed_point :
  (string * (binding * typ option * mixfix)) list ->
    Specification.multi_specs -> local_theory -> Proof.state

val fixed_point_cmd :
  (string * (binding * string option * mixfix)) list ->
    Specification.multi_specs_cmd -> local_theory -> Proof.state

val add_fixed_point :
  (string * (binding * typ option * mixfix)) list ->
    Specification.multi_specs -> (Proof.context -> tactic) -> local_theory -> (result * local_theory)

val add_fixed_point_cmd :
  (string * (binding * string option * mixfix)) list ->
    Specification.multi_specs_cmd ->  (Proof.context -> tactic) -> local_theory -> (result * local_theory)

end

structure Mutual_CCPO_Rec : MUTUAL_CCPO_REC =
struct

(*** BEGIN copied ***)

(* partial_function.ML *)

(*** Automated monotonicity proofs ***)

(*rewrite conclusion with k-th assumtion*)
fun rewrite_with_asm_tac ctxt k =
  Subgoal.FOCUS (fn {context = ctxt', prems, ...} =>
    Local_Defs.unfold0_tac ctxt' [nth prems k]) ctxt;

fun dest_case ctxt t =
  case strip_comb t of
    (Const (case_comb, _), args) =>
      (case Ctr_Sugar.ctr_sugar_of_case ctxt case_comb of
         NONE => NONE
       | SOME {case_thms, ...} =>
           let
             val lhs = Thm.prop_of (hd case_thms)
               |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst;
             val arity = length (snd (strip_comb lhs));
             fun conv () = funpow (length args - arity) Conv.fun_conv
               (Conv.rewrs_conv (map mk_meta_eq case_thms));
           in
             if arity <= length args then
               SOME (nth args (arity - 1), conv ())
             else NONE
           end)
  | _ => NONE;

(*split on case expressions*)
val split_cases_tac = Subgoal.FOCUS_PARAMS (fn {context = ctxt, ...} =>
  SUBGOAL (fn (t, i) => case t of
    _ $ (_ $ Abs (_, _, body)) =>
      (case dest_case ctxt body of
         NONE => no_tac
       | SOME (arg, conv) =>
           let open Conv in
              if Term.is_open arg then no_tac
              else ((DETERM o Induct.cases_tac ctxt false [[SOME arg]] NONE [])
                THEN_ALL_NEW (rewrite_with_asm_tac ctxt 0)
                THEN_ALL_NEW eresolve_tac ctxt @{thms thin_rl}
                THEN_ALL_NEW (CONVERSION
                  (params_conv ~1 (fn ctxt' =>
                    arg_conv (arg_conv (abs_conv (K conv) ctxt'))) ctxt))) i
           end)
  | _ => no_tac) 1);

(*remove arguments*)
val apply_app_tac = Subgoal.FOCUS_PARAMS (fn {context = ctxt, ...} =>
  SUBGOAL (fn (t, _) => case t of
    _ $ (_ $ Abs (a, T, body $ v)) =>
    if Term.is_open v then no_tac else
      resolve_tac ctxt [infer_instantiate' ctxt
        [NONE, NONE, SOME (Thm.cterm_of ctxt (Abs (a, T, body))), SOME (Thm.cterm_of ctxt v)]
        @{thm monotone_fun_ord_applyD}] 1
  | _ => no_tac) 1);

(*remove abstractions*)
val apply_abs_tac = Subgoal.FOCUS_PARAMS (fn {context = ctxt, ...} =>
  SUBGOAL (fn (t, _) => case t of
    _ $ (_ $ Abs (_, _, Abs (_, _, _))) =>
    resolve_tac ctxt [@{thm monotone_abs}] 1
  | _ => no_tac) 1);

(*monotonicity proof: apply rules + split case expressions*)
fun mono_tac ctxt =
  SOLVED_DETERM_verbose "mono_tac" ctxt (
    REPEAT_CHANGED_ALL_NEW
      (resolve_tac ctxt (rev (Named_Theorems.get ctxt \<^named_theorems>\<open>partial_function_mono\<close>))
        ORELSE' split_cases_tac ctxt
        ORELSE' (resolve_tac ctxt [@{thm monotone_abs}] THEN' split_cases_tac ctxt)
                (* ^- case for eta contracted splitters *)
        ORELSE' apply_app_tac ctxt
        ORELSE' apply_abs_tac ctxt
        ))


(*** END ***)

(* simple timing *)

val time_ref = Synchronized.var "fixed_point_timing" (NONE : Timing.start option)

fun TRACE msg =
  let
    val _ = case Synchronized.value time_ref of NONE => ()
      | SOME t =>
        let val tm = Timing.result t in
          (if Timing.is_relevant tm then
            tracing ("Finished: " ^ Timing.message tm)
          else ())
        end
    val _ = Synchronized.change time_ref (fn _ => SOME (Timing.start ()))
  in
    tracing msg
  end

fun reset_timing () = Synchronized.change time_ref (fn _ => NONE)

type ccpo_data = { typ : typ, ord : term, lub : term, bot : term, class : thm }

type functional =
  { binding: binding,
    mixfix: mixfix,
    recs: (string * typ) list,
    params: (string * typ) list,
    ccpo: ccpo_data,
    rhs: term,
    mono_tac: Proof.context -> int -> tactic }

type result = {
  consts: term list,
  simps: (string * thm list) list,
  inducts: (string * thm list)
}

structure Data = Generic_Data
(
  type T = (Proof.context -> typ -> ccpo_data) Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.merge (K true)
);

fun add_ccpo name synth = Data.map (Symtab.update_new (name, synth))
val get_ccpo = Data.get
fun synth_ccpo ctxt name =
  (Symtab.lookup (get_ccpo ctxt) name |> the) (Context.proof_of ctxt)

fun ordT a = a --> a --> HOLogic.boolT
fun lubT a = HOLogic.mk_setT a --> a

fun string_of_ccpo_data ctxt (ccpo_data : ccpo_data) =
  "{ typ = " ^ Syntax.string_of_typ ctxt (#typ ccpo_data) ^
  ", ord = " ^ Syntax.string_of_term ctxt (#ord ccpo_data) ^
  ", lub = " ^ Syntax.string_of_term ctxt (#lub ccpo_data) ^
  ", bot = " ^ Syntax.string_of_term ctxt (#bot ccpo_data) ^
  ", class = " ^ Syntax.string_of_term ctxt (Thm.prop_of (#class ccpo_data)) ^
  " }"

fun get_class ctxt ({class, ...}: ccpo_data) = Thm.transfer' ctxt class

fun synth_prod ctxt (a : ccpo_data) (b : ccpo_data) : ccpo_data =
  let
    val prodT = HOLogic.mk_prodT (#typ a, #typ b)
    val ordT = ordT (#typ a) --> ordT (#typ b) --> ordT prodT
    val lubT = lubT (#typ a) --> lubT (#typ b) --> lubT prodT
  in
    { typ = prodT,
      ord = Const (@{const_name rel_prod}, ordT) $ #ord a $ #ord b,
      lub = Const (@{const_name prod_lub}, lubT) $ #lub a $ #lub b,
      bot = HOLogic.mk_prod (#bot a, #bot b),
      class = Thm.trim_context (@{thm ccpo_rel_prodI} OF
        [get_class ctxt a, get_class ctxt b]) }
  end

fun synth_fun ctxt (a : typ) (b : ccpo_data) : ccpo_data =
  let
    val funT = a --> #typ b
    val ordT = ordT (#typ b) --> ordT funT
    val lubT = lubT (#typ b) --> lubT funT
  in
    { typ = funT,
      ord = Const (@{const_name fun_ord}, ordT) $ #ord b,
      lub = Const (@{const_name fun_lub}, lubT) $ #lub b,
      bot = Abs ("x", a, #bot b),
      class = Thm.trim_context (
        (instantiate'_normalize
          [SOME (Thm.ctyp_of ctxt (#typ b)), SOME (Thm.ctyp_of ctxt a)]
          [SOME (Thm.cterm_of ctxt (#lub b)), SOME (Thm.cterm_of ctxt (#ord b))]
          @{thm ccpo.ccpo_fun}) OF [get_class ctxt b]) }
  end

fun synth_gfp ctxt (a : typ) : ccpo_data =
  if Sign.of_sort (Proof_Context.theory_of ctxt) (a, @{sort complete_lattice}) then
    { typ = a,
      ord = Abs ("x", a, Abs ("y", a,
        Const (@{const_name "less_eq"}, ordT a) $ Bound 0 $ Bound 1)),
      lub = Const (@{const_name Inf}, lubT a),
      bot = Const (@{const_name top}, a),
      class = Thm.trim_context (
        instantiate'_normalize [SOME (Thm.ctyp_of ctxt a)] [] @{thm ccpo_Inf}) }
  else error ("Expect complete_lattice " ^ Syntax.string_of_typ ctxt a)

fun synth_lfp ctxt (a : typ) : ccpo_data =
  if Sign.of_sort (Proof_Context.theory_of ctxt) (a, @{sort complete_lattice}) then
    { typ = a,
      ord = Const (@{const_name "less_eq"}, ordT a),
      lub = Const (@{const_name Sup}, lubT a),
      bot = Const (@{const_name bot}, a),
      class = Thm.trim_context (
        instantiate'_normalize [SOME (Thm.ctyp_of ctxt a)] [] @{thm ccpo_Sup}) }
  else error ("Expect complete_lattice " ^ Syntax.string_of_typ ctxt a)

fun synth_flat ctxt (a : term) : ccpo_data =
  let val aT = fastype_of a in
    { typ = aT,
      ord = Const (@{const_name "flat_ord"}, aT --> ordT aT) $ a,
      lub = Const (@{const_name "flat_lub"}, aT --> lubT aT) $ a,
      bot = a,
      class = Thm.trim_context (
        instantiate'_normalize [SOME (Thm.ctyp_of ctxt aT)] [SOME (Thm.cterm_of ctxt a)]
        @{thm ccpo_flat}) }
  end

fun dest_optionT (Type (@{type_name option}, [a])) = a
  | dest_optionT t = raise TYPE ("dest_optionT", [t], [])

fun synth_option ctxt (a : typ) : ccpo_data =
  let
    val (argTs, rangeT) = strip_type a
    val _ = dest_optionT rangeT
  in synth_flat ctxt (Const (@{const_name None}, rangeT))
     |> fold_rev (synth_fun ctxt) argTs
  end

fun synth_funs _ ([], ccpo) = ccpo
  | synth_funs ctxt (aT :: aTs, ccpo) =
    synth_fun ctxt aT (synth_funs ctxt (aTs, ccpo))

fun ccpo_bot (ccpo : ccpo_data) = #bot ccpo

fun ccpo_fixp (ccpo : ccpo_data) =
  Const (@{const_name ccpo.fixp},
    lubT (#typ ccpo) --> ordT (#typ ccpo) --> (#typ ccpo --> #typ ccpo) --> #typ ccpo)
  $ #lub ccpo
  $ #ord ccpo


fun ccpo_mono (ccpoa : ccpo_data) (ccpob : ccpo_data) =
  \<^Const>\<open>monotone_on \<open>#typ ccpoa\<close> \<open>#typ ccpob\<close>\<close>$\<^Const>\<open>Orderings.top_class.top \<open>HOLogic.mk_setT (#typ ccpoa)\<close>\<close>
  $ #ord ccpoa
  $ #ord ccpob

fun ccpo_chain (ccpo : ccpo_data) =
  Const (@{const_name Complete_Partial_Order.chain},
    ordT (#typ ccpo) --> HOLogic.mk_setT (#typ ccpo) --> HOLogic.boolT)
  $ #ord ccpo

fun ccpo_admissible (ccpo : ccpo_data) =
  Const (@{const_name ccpo.admissible},
    lubT (#typ ccpo) --> ordT (#typ ccpo) --> (#typ ccpo --> HOLogic.boolT) --> HOLogic.boolT)
  $ #lub ccpo
  $ #ord ccpo

fun order_Sup (t : term) =
  let val T = fastype_of t |> HOLogic.dest_setT
  in Const (@{const_name Sup}, HOLogic.mk_setT T --> T) $ t end

fun mcont_id ctxt (ccpo : ccpo_data) =
  Thm.instantiate'
    [SOME (Thm.ctyp_of ctxt (#typ ccpo))]
    [SOME (Thm.cterm_of ctxt (#lub ccpo)), SOME (Thm.cterm_of ctxt (#ord ccpo))]
    @{thm mcont_id'}

fun SOLVED tac = SOLVED' (K tac) 1

val inductive_atomize = @{thms induct_atomize};
fun atomize_term thy = Raw_Simplifier.rewrite_term thy inductive_atomize [];

(* mutual_ccpo_fixed_point

Defines the fixed point given a list of mutually recursive functions and their defining equations.

  f_0 :: 'ps_0 \<Rightarrow> 'a_0     definition rhs_0   \<And>ps::'ps_0. f_0 ps = rhs_0
  ...                      ...
  f_n :: 'ps_n \<Rightarrow> 'a_n     definition rhs_n   \<And>ps::'ps_n. f_n ps = rhs_n

for each function provide a tactic to solve the monotonicity statement:

  monotone (\<le>) (\<le>) (\<lambda>F ps. rhs_0 ps [f_0 / \<pi>_0 F ... f_n / \<pi>_n F ]
  ...
  monotone (\<le>) (\<le>) (\<lambda>F ps. rhs_n ps [f_0 / \<pi>_0 F ... f_n / \<pi>_n F ]

It defines the constants:

  f_0 \<equiv> \<pi>_0 (lfp (\<lambda>F. (\<lambda>ps. rhs_0 ps F, ..., \<lambda>ps. rhs_0 ps F)))
  ...
  f_n \<equiv> \<pi>_n (lfp (\<lambda>F. (\<lambda>ps. rhs_0 ps F, ..., \<lambda>ps. rhs_0 ps F)))

Proving the equations eq_0 ... eq_n

Proving the *strong* induction rule:

  admissible (\<lambda>x. P (\<pi>_0 x) ... (\<pi>_n x)) \<Longrightarrow>
    (\<And>x. P x \<Longrightarrow> P (f_0_func x) ... (f_n_func x)) \<Longrightarrow> P f_0 ... f_n

Proving the n *weak* induction rule: (where i = 0 .. n)

  (i = 0 .. n: \<And>xs_i :: 'ps_i. admissible (P_i xs_i)) \<Longrightarrow>
  (i = 0 .. n: \<And>xs_i :: 'ps_i. P_i \<bottom>) \<Longrightarrow>
  (i = 0 .. n: \<And>xs_i :: 'ps_i.
    (j = 0 .. n: \<And>F_j :: 'ps_j => 'a_j) \<Longrightarrow>
    (j = 0 .. n: (\<And>ys_j :: 'ps_j. P_j ys_j (F_j ys_j)))  \<Longrightarrow>
    P_i xs_i (rhs_i xs_i)) \<Longrightarrow>
  \<And>xs_i :: 'ps_i. P_i xs_i (f_i xs_i)

*)

open Ctr_Sugar_Util

fun app_tower [] t = t
  | app_tower (f :: fs) t = app_tower fs (f $ t)

datatype 'a btree = Node of ('a btree * 'a btree)
                  | Leaf of 'a

fun map_btree f (Node (l, r)) = Node (map_btree f l, map_btree f r)
  | map_btree f (Leaf a) = Leaf (f a)

fun fold_btree f (Node (l, r)) = f (fold_btree f l, fold_btree f r)
  | fold_btree _ (Leaf a) = a

fun btree_of xs = Balanced_Tree.make Node (map Leaf xs)

fun btree_to_list (Node (l, r)) = btree_to_list l @ btree_to_list r
  | btree_to_list (Leaf a) = [a]

fun synth_btree ctxt (Leaf a) = synth_funs ctxt a
  | synth_btree ctxt (Node (l, r)) =
    synth_prod ctxt (synth_btree ctxt l) (synth_btree ctxt r)

fun projs_follow (p as Type (@{type_name prod}, [T1, T2])) (Node (l, r)) =
    Node (map_btree (fn ts => Const (@{const_name fst}, p --> T1) :: ts) (projs_follow T1 l),
      map_btree (fn ts => Const (@{const_name snd}, p --> T2) :: ts) (projs_follow T2 r))
  | projs_follow T (Node _) = raise TYPE ("Expect product", [T], [])
  | projs_follow _ (Leaf _) = Leaf []

fun WRAP_BTREE node_tac leaf_tac (Node (l, r)) =
      node_tac THEN WRAP_BTREE node_tac leaf_tac l THEN WRAP_BTREE node_tac leaf_tac r
  | WRAP_BTREE _ leaf_tac (Leaf a) = leaf_tac a

val tuple_of_btree = fold_btree HOLogic.mk_prod
val tupleT_of_btree = fold_btree HOLogic.mk_prodT

fun is_empty_binding ((b, _): Attrib.binding) = Binding.is_empty b

fun mutual_ccpo_fixed_point (fs : functional list) ctxt =
  let
    val b_fs = btree_of fs

    val ccpo_struct =
      b_fs
      |> map_btree (fn f => (map #2 (#params f), #ccpo f))
      |> synth_btree ctxt
    val ps = projs_follow (#typ ccpo_struct) b_fs

    val (recN, _) = singleton (Variable.variant_names ctxt) ("rec", ())
    val recF = (recN, #typ ccpo_struct)
    val projs = ps |> map_btree (fn ps => app_tower ps (Free recF)) |> btree_to_list
    val fixes = fs |> map (fn f => (Binding.name_of (#binding f),
      map #2 (#params f) ---> fastype_of (#rhs f)))
    val raw_functionals = b_fs |> map_btree (fn f =>
      #rhs f |> Term_Subst.instantiate_frees (TFrees.empty, Frees.make (fixes ~~ projs)) |> fold_rev absfree (#params f))

    val functional = tuple_of_btree raw_functionals |> absfree recF

val _ = TRACE ("prove mono thm ")

    val mono_thm =
      Goal.prove ctxt [] []
        (HOLogic.mk_Trueprop (ccpo_mono ccpo_struct ccpo_struct $ functional))
        (fn {context = ctxt, ...} =>
          WRAP_BTREE
            (resolve_tac ctxt @{thms monotone_pair} 1)
            (fn f : functional => SOLVED (
              EVERY (#params f |> map (K (apply_abs_tac ctxt 1))) THEN
              #mono_tac f ctxt 1))
            b_fs)

    val fixp = ccpo_fixp ccpo_struct $ functional

    val ((fixp_const, (_, fixp_def)), ctxt') =
      let
        val comb_name = Binding.prefix_name "fixp_" (Binding.conglomerate (map #binding fs))
val _ = TRACE ("define fixpoint " ^ Binding.print comb_name)
        val data =
            ((comb_name, NoSyn), ((Thm.def_binding comb_name, []), fixp))
      in
        Local_Theory.define data ctxt
      end

    fun define_f (f : functional, ps) =
      Local_Theory.define
        ((#binding f, #mixfix f), ((Thm.def_binding (#binding f), []), app_tower ps fixp_const))
      #> apfst (fn (c, (_, t)) => (f, ps, c, t))

    fun strong_induct ctxt0 cs defs induct_thm =
      let
val _ = TRACE "prepare strong induction"
        val (motivN, ctxt) = Variable.variant_fixes ["P"] ctxt0 |> apfst the_single
        val Ts = map (fn f : functional => map #2 (#params f) ---> #typ (#ccpo f)) fs
        val motiveF = Free (motivN, Ts ---> HOLogic.boolT)
        val motive = absfree recF (list_comb (motiveF,
            map (fn p => app_tower p (Free recF)) (btree_to_list ps)))
        val frees = map (fn f =>
          Free (Binding.name_of (#binding f), map #2 (#params f) ---> #typ (#ccpo f))) fs

        val induct' =
          instantiate'_normalize [] [SOME (Thm.cterm_of ctxt motive)] induct_thm

val _ = TRACE "strong induction"
        val induct_thm = Goal.prove ctxt []
          [HOLogic.mk_Trueprop (ccpo_admissible ccpo_struct $ motive),
            HOLogic.mk_Trueprop (list_comb (motiveF,
              map (fn f => ccpo_bot (synth_funs ctxt (map #2 (#params f), #ccpo f))) fs)),
            Logic.implies $
              (list_comb (motiveF, frees) |> HOLogic.mk_Trueprop) $
              (list_comb (motiveF, map (fn f => #rhs f |> fold_rev absfree (#params f)) fs)
                |> HOLogic.mk_Trueprop)
            |> fold_rev Logic.all frees]
            (list_comb (motiveF, cs) |> HOLogic.mk_Trueprop)
            (fn {context, prems, ...} =>
              let fun simp_tac ctxt st =
                full_simp_tac ((put_simpset HOL_basic_ss ctxt) addsimps
                  (@{thms Inf_empty Sup_empty prod_lub_empty fun_lub_empty
                          flat_lub_empty fst_conv snd_conv split_paired_all prod.collapse} @
                    map Thm.symmetric defs)) 1 st
              in
                cut_tac induct' 1 THEN
                SOLVED (simp_tac context) THEN
                EVERY (prems |> map (fn thm =>
                  Subgoal.SUBPROOF (fn { context, prems, ... } =>
                    cut_tac (thm OF prems) 1 THEN
                    simp_tac context) context 1))
              end)
      in
        Proof_Context.export ctxt ctxt0 [induct_thm] |> the_single
      end

    fun weak_inducts ctxt induct_thm =
      let
val _ = TRACE "prepare weak induction"
        fun gen_proj_cont t (Leaf _)      = Leaf t
          | gen_proj_cont t (Node (l, r)) =
            Node (gen_proj_cont (@{thm mcont2mcont_fst} OF [t]) l,
              gen_proj_cont (@{thm mcont2mcont_snd} OF [t]) r)
        val proj_thms =
          map2 (fn t => fn f => fold (K (fn t => @{thm mcont2mcont_call} OF [t])) (#params f) t)
            (gen_proj_cont (mcont_id ctxt ccpo_struct) b_fs |> btree_to_list) fs

        type motiv_data = { f : functional, P : term, F : term, args : term list }
        val (motiv_data, ctxt') =
          fold_map (fn f : functional =>
            Variable.variant_fixes ["P_" ^ Binding.name_of (#binding f)]
            #> apfst (fn names => let
              val Ts = map #2 (#params f)
              val P = Free (hd names, Ts ---> #typ (#ccpo f) --> HOLogic.boolT)
              val F = Free (Binding.name_of (#binding f), Ts ---> #typ (#ccpo f))
            in {f = f, P = P, F = F, args = map Free (#params f)} : motiv_data end)) fs ctxt

        val admissibles = motiv_data
          |> map (fn m : motiv_data =>
            ccpo_admissible (#ccpo (#f m)) $ list_comb (#P m, #args m)
            |> HOLogic.mk_Trueprop
            |> fold_rev Logic.all (#args m))

        val inits = motiv_data
          |> map (fn m : motiv_data =>
            list_comb (#P m, #args m) $ ccpo_bot (#ccpo (#f m))
            |> HOLogic.mk_Trueprop
            |> fold_rev Logic.all (#args m))

        val branches = motiv_data
          |> map (fn m : motiv_data => list_comb (#P m, #args m) $ (list_comb (#F m, #args m)))
        val hyps = map2 (fn b => fn m =>
          b |> HOLogic.mk_Trueprop |> fold_rev Logic.all (#args m)) branches motiv_data

        fun case_of (m : motiv_data) =
          Logic.list_implies (hyps,
            list_comb (#P m, #args m) $ #rhs (#f m) |> HOLogic.mk_Trueprop)
          |> fold_rev Logic.all (#args m)
          |> fold_rev Logic.all (map #F motiv_data)

        val motive =
          map2 (#args #> map dest_Free #> fold_rev (fn (x, T) => fn t => HOLogic.mk_all (x, T, t)))
            motiv_data branches
          |> foldr1 HOLogic.mk_conj
          |> fold_rev (#F #> dest_Free #> absfree) motiv_data

        val raw_induct =
          infer_instantiate' ctxt' [SOME (Thm.cterm_of ctxt' motive)] induct_thm

val _ = TRACE "weak induction"
        val induction_thms =
          Goal.prove_common ctxt' NONE []
            (admissibles @ inits @ map case_of motiv_data)
            hyps
            (fn {context, prems} =>
            let
              val ((adm, bot), cases) = prems |> (chop (length fs) ##>> chop (length fs))
              val adm = map2 (fn adm => fn proj =>
                @{thm admissible_subst} OF [adm, proj]) adm proj_thms
            in
              Object_Logic.full_atomize_tac context 1 THEN
              Local_Defs.unfold0_tac context @{thms conj_assoc} THEN
              resolve_tac context [raw_induct] 1 THEN
              SOLVED (REPEAT
                (resolve_tac context (@{thms admissible_conj admissible_all} @ adm) 1)) THEN
              SELECT_GOAL (SOLVED (REPEAT
                (resolve_tac context (@{thms conjI allI} @ bot) 1))) 1 THEN
              SOLVED (
                REPEAT (eresolve_tac context @{thms conjE} 1) THEN
                SUBPROOF (fn {context, prems, ...} =>
                  let
                    val hyps = map (Object_Logic.rulify context) prems
                  in
                    (TRY o REPEAT_ALL_NEW (resolve_tac context @{thms conjI allI})) 1 THEN
                    EVERY (map (fn case_thm => SOLVED (
                      resolve_tac context [case_thm OF hyps] 1)) cases)
                  end) context 1)
            end)
val _ = TRACE "finished weak induction"
      in
        Proof_Context.export ctxt' ctxt induction_thms
      end

    fun core_thms fs ctxt =
      let
        val b_fs = btree_of fs
        val defs = map_btree #4 b_fs
        val consts = map_btree #3 b_fs
        val mapping = fs |> map (fn (f, _, c, _) =>
          ((Binding.name_of (#binding f), fastype_of c), c))

val _ = TRACE "conversions"
        fun conv (Leaf thm)         = Conv.rewr_conv thm
          | conv (Node (l, r)) =
            Conv.arg1_conv (conv l) then_conv
            Conv.arg_conv (conv r) then_conv
            Conv.rewr_conv (Simpdata.mk_meta_eq @{thm prod.collapse})
        val unfold =
          (conv defs then_conv Conv.rewr_conv fixp_def)
            (Thm.cterm_of ctxt (tuple_of_btree consts))

        val unfold_fixp = @{thm ccpo.fixp_unfold_def} OF [get_class ctxt ccpo_struct, unfold, mono_thm]
        fun gconv (Leaf _)         = Conv.all_conv
          | gconv (Node (l, r)) =
            Conv.arg1_conv (gconv l) then_conv
            Conv.arg_conv (gconv r) then_conv
            Conv.rewr_conv (Simpdata.mk_meta_eq @{thm prod.inject[symmetric]})
val _ = TRACE "simp rules"
        val simps =
          Goal.prove_common ctxt NONE [] []
          (fs |> map (fn (f, _, c, _) =>
            HOLogic.mk_eq
              (c,
                #rhs f |> Term_Subst.instantiate_frees (TFrees.empty, Frees.make mapping) |>
                fold_rev absfree (#params f))
            |> HOLogic.mk_Trueprop))
          (fn {context, ...} =>
            Object_Logic.full_atomize_tac context 1 THEN
            CONVERSION (Conv.concl_conv 1 (Conv.arg_conv
              (gconv b_fs then_conv
                Conv.arg1_conv (Conv.rewr_conv (Simpdata.mk_meta_eq unfold_fixp))))) 1 THEN
            Local_Defs.unfold0_tac context @{thms fst_conv snd_conv} THEN
            resolve_tac context @{thms HOL.refl} 1)

        val induct_fixp = @{thm ccpo.fixp_induct_def} OF [get_class ctxt ccpo_struct, unfold, mono_thm]
        val strong_induct_thm =
          strong_induct ctxt (btree_to_list consts) (btree_to_list defs) induct_fixp
        val weak_induct_thms = weak_inducts ctxt strong_induct_thm
      in
        ((btree_to_list consts, simps, strong_induct_thm, weak_induct_thms), ctxt)
      end

val _ = TRACE "define functions"
  in
    ctxt'
    |> fold_map define_f (fs ~~ btree_to_list ps)
    |-> core_thms
  end

type functional_spec =
  { function: term,
    binding: binding,
    mixfix: mixfix,
    name: string,
    ccpo: ccpo_data,
    typ: typ,
    arg_vars: term list,
    result_var: term,
    preds: term list,
    pred_set : term,
    equations: ((string * typ) list * term list * term list * term * Attrib.binding) list }

type fixed_point_spec =
  { functions : functional_spec list,
    ccpo_struct : ccpo_data,
    body : term,
    mono : thm }



fun prepare_fixed_point prepare fixes_raw eqns_raw lthy =
  let

    val thy = Proof_Context.theory_of lthy

    val ((fixes', raw_eqs), lthy') = prepare (map #2 fixes_raw) eqns_raw lthy

    val fixes = map (#1 #> apfst Binding.name_of) fixes'
    val b_fixes = fixes |> btree_of
    val (recN, _) = singleton (Variable.variant_names lthy') ("rec", ())
    val tupleT = b_fixes |> map_btree #2 |> tupleT_of_btree
    val recF = (recN, tupleT)
    fun gen_projs t (Leaf f)      = Leaf (f, t)
      | gen_projs t (Node (l, r)) =
        Node (gen_projs (HOLogic.mk_fst t) l, gen_projs (HOLogic.mk_snd t) r)
    val projs = gen_projs (Free recF) b_fixes |> btree_to_list

    val (specs : functional_spec list, _) =
      let
        fun dest_eq (b, t) ctxt =
          let
            val ((params, body), ctxt') = Variable.focus NONE t ctxt
            val (prems, concl) = Logic.strip_horn body
            val (lhs, rhs) = concl |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
              handle TERM _ =>
                raise TERM ("Expect HOL equality in conclusion of a specification equation", [t])
            val (f, args) = strip_comb lhs
            val _ = if member (op aconv) (map Free fixes) f then  () else
              raise TERM ("Unexpected head in right-hand side of a specification equation", [t])
          in
            ((f, (params |> map #2,
                  prems |> map (atomize_term thy #> HOLogic.dest_Trueprop),
                  args,
                  rhs,
                  b)), ctxt')
          end
        fun rule_of_eq res vars (params, prems, args, rhs, _) =
          let
            val (mapped_vars, direct_vars) = chop (length args) vars
            val arg_eqs =
              map2 (fn a => fn b => HOLogic.mk_eq (a, b)) mapped_vars args
          in
            ( prems @ arg_eqs @
              [ HOLogic.mk_eq (res, list_comb (rhs, direct_vars)) ] )
            |> Library.foldr1 HOLogic.mk_conj
            |> Ctr_Sugar_Util.list_exists_free (map Free params)
          end
        fun spec_of_fixes ((binding, typ), mixfix) name eqs ctxt =
          let
            val f = Free (Binding.name_of binding, typ)
            val vars_cnt = fold (fn (_, _, a, _, _) => fn c => Int.max (length a, c)) eqs 0
            val (Ts'', T') = strip_type (fastype_of f)
            val (Ts, Ts') = chop vars_cnt Ts''
            val T = Ts' ---> T'
            val (ccpo : ccpo_data) = synth_ccpo (Context.Proof ctxt) name T
              handle Option.Option => raise TYPE ("Cannot synth CCPO " ^ name, [T], [])

            val vars = Variable.variant_names ctxt (map (pair "x") Ts) |> map Free
            val res =
              singleton (Variable.variant_names (fold Variable.declare_names vars ctxt)) ("r", T)
            val preds = map (rule_of_eq (Free res) vars) eqs
          in
            { function = f,
              binding = binding,
              mixfix = mixfix,
              name = dest_Free f |> #1,
              ccpo = ccpo,
              typ = T,
              arg_vars = vars,
              result_var = Free res,
              preds = preds,
              pred_set = HOLogic.mk_set (HOLogic.mk_setT T)
                (map (fn p => HOLogic.mk_Collect (#1 res, #2 res, p)) preds),
              equations = eqs }
          end
        val (eqs, ctxt') =
          fold_map dest_eq raw_eqs lthy' |> apfst Termtab.make_list
      in
        (@{map 3} (fn f => fn data => fn (mode, _) => case Termtab.lookup eqs (Free f) of
            SOME eqs => spec_of_fixes data mode eqs ctxt'
          | NONE => raise TERM ("No specification for", [Free f])) fixes fixes' fixes_raw,
          ctxt')
      end

    val ccpo_struct =
      btree_of specs
      |> map_btree (fn (s : functional_spec) => (map fastype_of (#arg_vars s), #ccpo s))
      |> synth_btree lthy'

    fun mk_subsingleton_set t =
      let
        val T = HOLogic.dest_setT (fastype_of t)
      in
        Const (@{const_name subsingleton_set}, T --> HOLogic.boolT) $
          (Const (@{const_name Sup}, HOLogic.mk_setT T --> T) $ t)
      end

    fun subsingleton_set (spec : functional_spec) = mk_subsingleton_set (#pred_set spec)

    val ss_goals = specs |> map (fn spec : functional_spec =>
      let
        val set = subsingleton_set spec
        val frees = Term.add_frees set [] |> filter_out (Variable.is_fixed lthy o fst) |> map Free
        val pat =
          list_comb (Var (("unique_" ^ Binding.name_of (#binding spec), 0),
            map fastype_of frees ---> HOLogic.boolT), frees)
          |> HOLogic.mk_Trueprop
          |> fold_rev Logic.all frees
      in
        [(set |> HOLogic.mk_Trueprop |> fold_rev Logic.all frees, [pat])]
      end)

    fun after_qed thmss ctxt =
      let
val _ = reset_timing ()
val _ = TRACE ("= start construction =")

        val assms = map the_single thmss

        fun functional (assm : thm, spec : functional_spec) ctxt =
          let
val _ = TRACE ("FUNCTIONAL: " ^ @{make_string} (#binding spec))
            val arg_names = map (dest_Free #> #1) (#arg_vars spec)

            val rec_calls =
              Term.add_free_names (#pred_set spec) []
            val recs = fixes |> filter (#1 #> member (op =) rec_calls)

val _ = TRACE (" * define function")
            val body =
              #lub (#ccpo spec) $ order_Sup (#pred_set spec)
              |> fold_rev (dest_Free #> absfree) (#arg_vars spec)
              |> fold_rev absfree recs
            val ((functional, (_, functional_def)), ctxt') = Local_Theory.define
              ((Binding.suffix_name "_functional" (#binding spec), NoSyn),
                ((Binding.suffix_name "_functional_def" (#binding spec), []),
                  body)) ctxt

val _ = TRACE (" ** assm_proj")
            val assm_proj = assm
              |> Thm.instantiate (TVars.empty,
                    projs |> map (fn ((n, T), p) => (((n, 0), T), Thm.cterm_of ctxt' p)) |> Vars.make)
              |> Drule.generalize (Names.empty, Names.make_set [recN])

            fun pre_mono_tac ctxt =
              let
                val cls_thm = get_class ctxt (#ccpo spec)
                val Ps = #pred_set spec
                  |> Term_Subst.instantiate_frees (TFrees.empty, Frees.make projs)
                  |> absfree recF
                  |> Thm.cterm_of ctxt
                val thm = (@{thm ccpo.monotone_Sup_of_subsingleton_sets} OF [cls_thm])
                  |> infer_instantiate' ctxt
                    [SOME Ps, SOME (Thm.cterm_of ctxt (#ord ccpo_struct))]
                |> Drule.generalize (Names.empty, Names.make_set arg_names)
              in
                resolve_tac ctxt [thm] THEN'
                SOLVED' (resolve_tac ctxt [assm_proj])
              end

val _ = TRACE (" ** mono_thms")
            val mono_const =
              ccpo_mono ccpo_struct (#ccpo spec)
            val mono_thms = #equations spec
              |> map (fn (params, _, _, rhs, _) =>
                Goal.prove ctxt (map #1 params) []
                  (HOLogic.mk_Trueprop (mono_const $
                    (rhs |> Term_Subst.instantiate_frees (TFrees.empty, Frees.make projs) |> absfree recF)))
                  (fn {context, ...} => mono_tac context 1))
            fun mono_tac context _ =
              unfold_tac context [functional_def] THEN
              pre_mono_tac context 1 THEN
              Subgoal.SUBPROOF (fn {context, prems, ...} =>
                REPEAT_ALL_NEW (resolve_tac context
                  @{thms sim_set_empty sim_set_insert sim_set_Collect_Ex sim_set_Collect_conj
                    sim_set_Collect_eq}) 1 THEN
                RANGE (mono_thms |> map (fn thm => SOLVED' (
                  resolve_tac context [(@{thm monotoneD} OF [thm]) OF prems]))) 1) context 1

val _ = TRACE (" * prove equations")
            val unfold_thm =
              @{thm ccpo.Sup_of_subsingleton_sets_eq} OF [get_class ctxt (#ccpo spec), assm]

val _ = TRACE (" ** eq_thms")
            val eq_thms = #equations spec |> map_index (fn (i, (params, prems, args, rhs, _)) =>
              Goal.prove ctxt' (map #1 recs @ map #1 params) (map HOLogic.mk_Trueprop prems)
                (HOLogic.mk_eq (list_comb (functional, map Free recs @ args), rhs)
                  |> HOLogic.mk_Trueprop)
                (fn {context, prems, ...} =>
                  unfold_tac context [functional_def] THEN
                  resolve_tac context [unfold_thm] 1 THEN
                  SOLVED (
                    EVERY ((1 upto i) |> map (fn _ => resolve_tac context [@{thm Set.insertI2}] 1))
                    THEN resolve_tac context [@{thm Set.insertI1}] 1) THEN
                  resolve_tac context [@{thm CollectI}] 1 THEN
                  EVERY (params |> map (fn param =>
                    resolve_tac context [@{thm exI} |> infer_instantiate' context
                      [NONE, SOME (Thm.cterm_of context (Free param))]] 1)) THEN
                  Ctr_Sugar_Util.CONJ_WRAP
                    (fn thm => resolve_tac context [thm] 1)
                    (prems @ replicate (length args + 1) @{thm HOL.refl})))

val _ = TRACE (" ** note")
            val binding = Binding.suffix_name "_functional" (#binding spec)
            val binding = Binding.qualify true
              (Binding.name_of binding)
              (Binding.set_pos (Binding.pos_of binding) (Binding.name "simps"))
            val ((_, eq_thms), ctxt'') = Local_Theory.note ((binding, []), eq_thms) ctxt'
val _ = TRACE (" * DONE")
          in ((functional, (assm, functional_def), recs, eq_thms, mono_tac), ctxt'') end
        val (functionals, lthy') = fold_map functional (assms ~~ specs) ctxt

        val fs =
          map2 (fn (f, _, recs, _, mono) => fn s =>
            ({ binding = #binding s,
               mixfix = #mixfix s, ccpo = #ccpo s,
               rhs = list_comb (f, map Free recs @ #arg_vars s),
               mono_tac = mono,
               recs = recs,
               params = #arg_vars s |> map dest_Free } : functional))
            functionals specs

val _ = TRACE ("= construct =")
        val assms = map #2 functionals
        val ((consts, def_rules, strong_induct, weak_inducts), lthy'') =
          mutual_ccpo_fixed_point fs lthy'

        fun prove_eq ctxt const def_rule simp_thm (params, guards, args, rhs, binding) =
          (Goal.prove ctxt (map #1 params) (map HOLogic.mk_Trueprop guards)
            ((list_comb (const, args), rhs) |> HOLogic.mk_eq |> HOLogic.mk_Trueprop |>
              Term_Subst.instantiate_frees (TFrees.empty, Frees.make (fixes ~~ consts)))
            (fn {context, prems} =>
              CONVERSION (Conv.arg_conv (Conv.arg1_conv
                (fold (K Conv.fun_conv) args
                  (Conv.rewr_conv (Simpdata.mk_meta_eq def_rule))))) 1 THEN
              resolve_tac context [simp_thm] 1 THEN
              EVERY (prems |> map (fn thm => resolve_tac context [thm] 1))), binding)

        fun prove_eqs ctxt const def_rule (eqs : thm list) (s : functional_spec) =
          @{map 2} (prove_eq ctxt const def_rule) eqs (#equations s)

        fun inducts ctxt induct_thms =
          let
            type motiv_data = { f : functional, P : term, F : term, args : term list }
            val (motiv_data, ctxt') =
              fold_map (fn f : functional =>
                Variable.variant_fixes ("P_" ^ Binding.name_of (#binding f) :: map #1 (#params f))
                #> apfst (fn names => let
                  val Ts = map #2 (#params f)
                  val P = Free (hd names, Ts ---> #typ (#ccpo f) --> HOLogic.boolT)
                  val args = map Free (tl names ~~ Ts)
                  val F = Free (Binding.name_of (#binding f), Ts ---> #typ (#ccpo f))
                in {f = f, P = P, F = F, args = args} : motiv_data end)) fs ctxt

            val admissibles = motiv_data
              |> map (fn m : motiv_data =>
                ccpo_admissible (#ccpo (#f m)) $ list_comb (#P m, #args m)
                |> HOLogic.mk_Trueprop
                |> fold_rev Logic.all (#args m))

            val inits = motiv_data
              |> map (fn m : motiv_data =>
                list_comb (#P m, #args m) $ ccpo_bot (#ccpo (#f m))
                |> HOLogic.mk_Trueprop
                |> fold_rev Logic.all (#args m))

            val branches = motiv_data
              |> map (fn m : motiv_data => list_comb (#P m, #args m) $ (list_comb (#F m, #args m)))
            val hyps = map2 (fn b => fn m =>
              b |> HOLogic.mk_Trueprop |> fold_rev Logic.all (#args m)) branches motiv_data

            fun case_of (m : motiv_data) (params, guards, args, rhs, _) =
              Logic.list_implies (hyps @ map HOLogic.mk_Trueprop guards,
                list_comb (#P m, args) $ rhs |> HOLogic.mk_Trueprop)
              |> fold_rev Logic.all (map Free params)
              |> fold_rev Logic.all (map #F motiv_data)

            val cases = maps (fn (m, s) => #equations s |> map (case_of m)) (motiv_data ~~ specs)

            val raw_inducts = induct_thms |> map
              (infer_instantiate' ctxt' (motiv_data |> map (#P #> Thm.cterm_of ctxt' #> SOME)))
          in
          Goal.prove_common ctxt NONE
            (map (#P #> dest_Free #> #1) motiv_data)
            (admissibles @ inits @ cases) hyps
            (fn {context, prems} =>
            let
              val ((adm, bot), cases) = prems |> (chop (length fs) ##>> chop (length fs))
              val eqs = map #equations specs
              val c = map2 (fn c => fn eq => c ~~ eq) (unflat eqs cases) eqs
              val cases' = assms ~~ motiv_data ~~ adm ~~ bot ~~ c
            in
              Goal.conjunction_tac 1 THEN
              EVERY (raw_inducts |> map (fn thm => Subgoal.SUBPROOF (fn { context, ... } =>
                resolve_tac context [thm] 1 THEN
                EVERY ((adm @ bot) |> map (fn thm => SOLVED (resolve_tac context [thm] 1))) THEN
                EVERY (cases' |> map (fn (((((ss_asm, def), m), adm), bot), cases) =>
                  Subgoal.SUBPROOF (fn { context, prems = hyps, params = hyps_params, ... } =>
                    unfold_tac context [def] THEN
                    resolve_tac context [
                      (@{thm ccpo.induct_Sup_of_subsingleton_sets} OF
                       [ get_class ctxt (#ccpo (#f m)) ]) OF [ss_asm, adm]] 1 THEN
                    Subgoal.SUBPROOF (fn { context, ...} =>
                      unfold_tac context (@{thms Inf_empty Sup_empty
                        prod_lub_empty fun_lub_empty flat_lub_empty fst_conv snd_conv
                        split_paired_all prod.collapse} @ [bot])) context 1 THEN
                    EVERY (cases |> map (fn (c, (_, guards, args, _, _)) =>
                      eresolve_tac context @{thms insertE} 1 THEN
                      bound_hyp_subst_tac context 1 THEN
                      REPEAT (eresolve_tac context @{thms CollectE exE} 1) THEN
                      Subgoal.SUBPROOF (fn { context, prems, ... } =>
                        let
                          val assm = the_single prems
                          val g = length guards
                          val a = length args
                          val (init, res_prem) = funpow_yield (g + a) (HOLogic.conj_elim ctxt) assm
                          val (guard_prems, arg_prems) = chop g init
                          val case_thm = c
                            |> Thm.instantiate' []
                              (map (#2 #> SOME) (take (length fixes) hyps_params))
                            |> (fn thm => thm OF (hyps @ guard_prems))
                        in
                          Local_Defs.unfold0_tac context (res_prem :: arg_prems) THEN
                          resolve_tac context [case_thm] 1
                        end) context 1)) THEN
                    eresolve_tac context @{thms emptyE} 1)
                    context 1)))
                context 1))
            end)
          end

val _ = TRACE "Final equations"
        val final_simps = @{map 4} (prove_eqs lthy'') consts def_rules (map #4 functionals) specs
val _ = TRACE "Final inducts"
        val final_inducts = inducts lthy'' weak_inducts
val _ = TRACE "install"
        fun opt_binding b =
          if forall is_empty_binding (maps (map snd) final_simps) then
            Binding.qualify_name true b "simps"
          else
            Binding.empty
        val _ = tracing ("attribs: " ^ @{make_string} (maps (map snd)  final_simps))
        val ((((simps, _), inducts), _), lthy''') =
          lthy''
          |> Local_Theory.notes (map2 (fn s => fn simps =>
              ((opt_binding (#binding s), []),
                map (fn (thm, _) => ([thm], [])) simps)) specs final_simps)
          ||>> fold_map (fn (thm, bnd) => Local_Theory.note (bnd, [thm])) (maps I final_simps)
          ||>> Local_Theory.note
                ((Binding.qualify_name true (Binding.conglomerate (map #binding specs)) "induct", []),
                  final_inducts)
          ||>> Local_Theory.note
                ((Binding.qualify_name true (Binding.conglomerate (map #binding specs)) "strong_induct", []),
                  [strong_induct])


val _ = TRACE "done"
val _ = reset_timing ()

      in ({consts = consts, simps = simps, inducts =  inducts}, lthy''') end
  in
    (ss_goals, after_qed)
  end

fun gen_fixed_point_cmd prepare fixes_raw eqns_raw lthy =
  let
    val (ss_goals, after_qed) = prepare_fixed_point prepare fixes_raw eqns_raw lthy
  in
    Proof.theorem NONE (snd oo after_qed) ss_goals lthy
  end

val fixed_point = gen_fixed_point_cmd Specification.check_multi_specs
val fixed_point_cmd = gen_fixed_point_cmd Specification.read_multi_specs

fun gen_add_fixed_point prepare fixes_raw eqns_raw ctxt_tac lthy =
  let
    val (ss_goals, after_qed) = prepare_fixed_point prepare fixes_raw eqns_raw lthy
    val goals = ss_goals |> flat |> map fst
    val thms = Goal.prove_common lthy NONE [] [] goals (fn {context, ...} =>
          Goal.conjunction_tac 1 THEN
          ctxt_tac context)
  in
    after_qed (map single thms) lthy
  end

val add_fixed_point = gen_add_fixed_point Specification.check_multi_specs
val add_fixed_point_cmd = gen_add_fixed_point Specification.read_multi_specs

val mode_vars =
  let
    open Parse
    val param_mixfix =
      binding -- Scan.option ($$$ "::" |-- typ) -- mixfix' >> (single o Scan.triple1)
    val mode = \<^keyword>\<open>(\<close> |-- Parse.name --| \<^keyword>\<open>)\<close>;
  in
    and_list1 (mode -- (param_mixfix || params) >> (fn (m, xs) => map (fn x => (m, x)) xs)) >> flat
  end

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>fixed_point\<close> "define fixed point"
    ((mode_vars -- Parse_Spec.where_multi_specs) >>
      (fn (vars, specs) => fixed_point_cmd vars specs));

end