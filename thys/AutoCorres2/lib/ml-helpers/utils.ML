(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

fun rev_app x f = f x 


(* FIXME Make Signature*)
structure Utils =
struct
(* verbose mode *)
val indent = Attrib.setup_config_int \<^binding>\<open>verbose_indent\<close> (K ~1);
fun indent_msg ctxt s = 
  let
    val indent = Config.get ctxt indent
  in 
    if indent > 0 
    then
      let
        val indent_str = String.concat (replicate indent " ")
      in Pretty.string_of (Pretty.blk (indent, [Pretty.str (indent_str ^ s)])) end
    else 
      s
  end
fun inc_indent n = Config.map indent (fn i => if i >= 0 then i + n else i)
val verbose = Attrib.setup_config_int \<^binding>\<open>verbose\<close> (K 0);
fun verbose_fn level ctxt f = if level <= Config.get ctxt verbose then f () else ();
fun verbose_msg level ctxt f = 
  let
    val current_level = Config.get ctxt verbose 
  in  
    if level <= current_level then tracing (indent_msg ctxt (f current_level)) else ()
  end
fun autocorres_verbose ctxt = Config.get ctxt verbose

fun gen_verbose_msg_tac tac level ctxt f st = (verbose_msg level ctxt f; tac st)  
val verbose_msg_tac = gen_verbose_msg_tac all_tac
val verbose_msg_no_tac = gen_verbose_msg_tac no_tac



(* timing *)

val timing = Attrib.setup_config_int \<^binding>\<open>verbose_timing\<close> (K 0);
val timing_threshold = Attrib.setup_config_int \<^binding>\<open>verbose_timing_threshold\<close> (K 3); (* in milliseconds *)


type ('a,'b) timing_info = {timing:Timing.timing, verbose:int, input:'a, output:'b}
fun set_input x {timing, verbose, input, output} = {timing=timing, verbose=verbose, input = x, output=output}
fun set_message_input x msg = fn info => msg (set_input x info)

fun sep_concat s1 s2 =
  if String.isSuffix " " s1 then s1 ^ s2 else s1 ^ " " ^ s2

fun dep_timeap_msg verbose (msg: ('a,'b) timing_info -> string) f x =
  let
    val (timing, y) = Timing.timing f x
    val str = msg {timing = timing, verbose = verbose, input = x, output = y}
    val _ = if str = "" then () else warning (sep_concat str (Timing.message timing)) 
  in   
     y 
  end

fun dep_timeit_msg verbose msg f = dep_timeap_msg verbose msg f ()

fun is_relevant_time t (time: Time.time) = time >= t;

fun is_relevant t ({elapsed, cpu, gc}: Timing.timing) = 
  is_relevant_time t elapsed orelse
  is_relevant_time t cpu orelse
  is_relevant_time t gc;

fun threshold_msg t msg (info:('a, 'b) timing_info as {timing=timing, ...}) =
  if is_relevant t timing then msg info else ""

fun timeap_msg level ctxt msg f x =
  if Config.get ctxt timing >= level 
  then
    let
      val threshold = Time.fromMilliseconds (Config.get ctxt timing_threshold)
      val verbose = Config.get ctxt verbose
      val msg' = indent_msg ctxt o threshold_msg threshold msg
    in
      dep_timeap_msg verbose msg' f x
    end 
  else f x

fun cat_lines' xs = xs |> filter_out (fn x => x = "") |> space_implode "\n " 

fun gen_tactic_message prep trace_subgoals ctxt msg info =
  let 
    val message = msg info
    val {input = st, output = seq_hd, ...} = prep info
  in 
    if message = "" then ""
    else
      let
        val (status, st') = if Thm.nprems_of st = 0 then ("no subgoals: ", st)
          else case seq_hd of  
                 NONE => ("tactic failed: ", st)
               |  SOME (st', _) => ("tactic success: ", st');
        val state = if trace_subgoals = 0 then "" 
          else if trace_subgoals > 0 then 
            st' |> Thm.prop_of |> (fn t => Logic.get_goal t trace_subgoals) 
            |> Syntax.pretty_term ctxt |> Pretty.string_of
          else Goal_Display.string_of_goal ctxt st'
      in
        cat_lines' [message, status, state]
      end
  end

val tactic_message = gen_tactic_message I 0


fun timeit_msg level ctxt msg f = timeap_msg level ctxt msg f ()

fun timeit_msg_seq level ctxt msg xs =
  Seq.make (fn () => 
   if Config.get ctxt timing >= level then 
     (case timeap_msg level ctxt msg (fn () => Seq.pull xs) () of
       NONE => NONE
     | SOME (x, xs) => SOME (x, (timeit_msg_seq level ctxt msg xs)))
   else Seq.pull xs)

fun gen_timeap_msg_tac trace_subgoals level ctxt msg tac st =
  let
    val msg' = gen_tactic_message I trace_subgoals ctxt msg
  in
    Seq.make (fn () => 
     if Config.get ctxt timing >= level then 
       (case timeap_msg level ctxt msg' (fn st => Seq.pull (tac st)) st of
         NONE => NONE
       | SOME (x, xs) => SOME (x, (timeit_msg_seq level ctxt (set_message_input st msg') xs)))
     else Seq.pull (tac st))
  end

val timeap_msg_tac = gen_timeap_msg_tac 0

(* ignore context for tactic messages *)
fun tactic_info_of_method_info {input = (_:Proof.context, st:thm), output = seq_hd, timing = timing, verbose=verbose} =
 let
   fun release_result (Seq.Result (_:Proof.context, st:thm)) = st
     | release_result (Seq.Error str) = error (str ())

   val seq_hd' = case seq_hd of NONE => NONE | SOME (res, xs) => SOME (release_result res, xs)
 in
   {input = st, output = seq_hd', timing = timing, verbose=verbose}
 end

 
fun gen_timeap_method trace_subgoals level ctxt msg (m: Method.method) thms cst = 
  let
    val msg' = (gen_tactic_message tactic_info_of_method_info trace_subgoals ctxt msg)
    fun get_ctxt (Seq.Result (ctxt', _)) = ctxt'
      | get_ctxt _ = ctxt
  in
    Seq.make (fn () => 
     if Config.get ctxt timing >= level then 
       (case timeap_msg level ctxt msg' (fn cst => Seq.pull (m thms cst)) cst of
         NONE => NONE
       | SOME (res, xs) => SOME (res, (timeit_msg_seq level (get_ctxt res) (set_message_input cst msg') xs)))
     else Seq.pull (m thms cst))
  end

val timeap_method = gen_timeap_method 0

fun timing_msg' level ctxt msg start =
  if Config.get ctxt timing >= level then
    let
      val threshold = Time.fromMilliseconds (Config.get ctxt timing_threshold)
      val timing = Timing.result start
      val str = threshold_msg threshold msg {timing=timing, verbose=level, input=(), output=()}
    in 
      if str = "" then () else warning (str ^ ": " ^ Timing.message timing)
    end
  else ()
   

fun timing_msg level ctxt s = if Config.get ctxt timing >= level then warning (s ()) else ();

fun lift_result_with_arity n lift f =
  let
    val (f_argTs, fresT) = strip_type (fastype_of f)
    val remaining_argTs = take (length f_argTs - n) f_argTs 
    val args = tag_list 1 remaining_argTs |> map (fn (i, T) => Free ("_x" ^ string_of_int i, T))
    val bdy = list_comb (f, args)
    val t = lift bdy   
      |> fold (fn a as Free (x, T) => fn bdy => Abs (unprefix "_" x, T, abstract_over (a, bdy)))
          (rev args) 
      |> Envir.norm_term (Envir.init)
  in
    t
  end

fun pretty_main_goal ctxt st =
  let
    val prop = Thm.prop_of st;
    val (_, B) = Logic.strip_horn prop;
  in Syntax.pretty_term ctxt B end


fun print_subgoal_tac msg ctxt = SUBGOAL (fn (t, i) => fn st =>
  let
    val np = Thm.nprems_of st
    val show_main_goal = Config.get ctxt Goal_Display.show_main_goal;
    val _ = tracing (indent_msg ctxt (msg ^ " subgoal " ^ string_of_int i ^ " of " ^ string_of_int np ^ ":\n "  ^ 
      (Pretty.string_of (Syntax.pretty_term ctxt t))) ^
      (if show_main_goal then
         "\n main goal: " ^ Pretty.string_of (pretty_main_goal ctxt st)
      else ""))
  in
    all_tac st
  end)
  ORELSE' (fn i => fn st =>
   let 
     val np = Thm.nprems_of st
     val _ = tracing (indent_msg ctxt (msg ^ " subgoal " ^ string_of_int i ^ " of " ^ string_of_int np ^ 
               " already solved."))
   in 
     all_tac st 
   end)
  

fun verbose_print_subgoal_tac level msg ctxt = 
  if level <= Config.get ctxt verbose then print_subgoal_tac msg ctxt else K all_tac

fun verbose_print_tac level msg ctxt = 
  if level <= Config.get ctxt verbose then print_tac ctxt msg else all_tac

fun print_maingoal_tac msg ctxt st = 
  let
    val main_goal = snd (Logic.strip_horn (Thm.prop_of st))
    val _ = tracing (indent_msg ctxt (msg ^ " maingoal:\n "  ^ 
      (Pretty.string_of (Syntax.pretty_term ctxt main_goal))))
  in
    all_tac st 
  end

fun verbose_print_maingoal_tac level msg ctxt = 
  if level <= Config.get ctxt verbose then print_maingoal_tac msg ctxt else all_tac

fun print_conv msg (ct:cterm) =
  let
    val _ = tracing (msg ^ ": " ^ @{make_string} ct);
  in Conv.all_conv ct end

fun gen_fix_variant_frees strict ts ctxt =
  let
    val (names, types) = split_list ts
    val (names', ctxt) = Variable.variant_fixes names ctxt
    val _ = if strict andalso names <> names' 
            then error ("gen_fix_variant_frees, name collission: " ^ @{make_string} (names, names'))
            else ()
    val frees = map Free (names' ~~ types)
    val ctxt = ctxt |> fold Variable.declare_term frees
  in (frees, ctxt) end

val fix_variant_frees = gen_fix_variant_frees false

fun gen_fix_variant_cfrees strict ts ctxt =
  gen_fix_variant_frees strict ts ctxt |> apfst (map (Thm.cterm_of ctxt))

val fix_variant_cfrees = gen_fix_variant_cfrees false

fun dummy_type (TVar _) = dummyT
  | dummy_type (TFree _) = dummyT
  | dummy_type (Type (n, Ts)) = Type (n, map dummy_type Ts) 

fun dummy (Free (x, T)) = Free (x, dummy_type T)
  | dummy (Const (x, T)) = Const (x, dummy_type T)
  | dummy (Var (x, T)) = Var (x, dummy_type T)
  | dummy (Abs (a, T, t)) = Abs (a, dummy_type T, dummy t)
  | dummy (t $ u) = dummy t $ dummy u
  | dummy b = b

local
fun dummy_tvar_tfree (TVar _) = dummyT
  | dummy_tvar_tfree (TFree _) = dummyT 
  | dummy_tvar_tfree _  = raise Same.SAME;
in
  val dummy_type_same = Term.map_atyps_same dummy_tvar_tfree
end

val dummy_same = Term.map_types_same (dummy_type_same)
val dummy = Same.commit dummy_same

local
fun dummy_tvar (TVar _) = dummyT
  | dummy_tvar _ = raise Same.SAME;
in
  val dummy_schematic_type_same = Term.map_atyps_same dummy_tvar
end

val dummy_schematic_same = Term.map_types_same (dummy_schematic_type_same)
val dummy_schematic = Same.commit dummy_schematic_same

fun is_dummyT T = T = dummyT
val not_dummyT = not o is_dummyT

fun no_dummy_typeT (T as Type (_, Ts)) = not_dummyT T andalso forall no_dummy_typeT Ts 
  | no_dummy_typeT _ = true

fun no_dummy_type t = true |> fold_types (fn T => fn b => b andalso no_dummy_typeT T) t
val has_dummy_type = not o no_dummy_type

fun infer_types_simple ctxt t =
  if has_dummy_type t 
  then t |>
    singleton (Type_Infer_Context.infer_types ctxt) |>
    singleton (Type_Infer.fixate ctxt false)
  else t

fun infer_schematic_types ctxt t =
  infer_types_simple ctxt (dummy_schematic t)

(*
 * Construct a term with the given args, inferring types in "term"
 * from args.
 *
 * We assume types in "args" are fully fixed and concrete.
 *)
fun infer_term ctxt term args =
  infer_types_simple ctxt (betapplys (Term.map_types (fn _ => dummyT) term, args))
  handle ERROR str => raise TERM (str, term:: args)

fun mk_cterm ctxt term cargs =
  let
    val term = Term.map_types (fn _ => dummyT) term
    fun dummy_arg (i, ct) ctxt = fix_variant_frees [("_" ^ string_of_int i, Thm.typ_of_cterm ct)] ctxt
    val (dummy_args, ctxt') = ctxt |> fold_map dummy_arg (tag_list 1 cargs) |>> flat
    val (head, args) = infer_types_simple ctxt' (list_comb (term, dummy_args)) |> strip_comb
    val term_args = take (length args - length cargs) args
    val cterm = list_comb (head, term_args) |> Thm.cterm_of ctxt
    val res = cterm |> fold (fn x => fn f => Thm.apply f x) cargs
  in
    res
  end

fun dest_all_open (Const (@{const_name "Pure.all"}, _) $ Abs (abs as (x, T, b))) = ((x, T), b)
  | dest_all_open t = raise TERM ("dest_all_open", [t]);

fun strip_all t = case try Logic.dest_all_global t of
      SOME (v, t') => let val (vs, r) = strip_all t' in (v::vs, r) end
    | NONE => ([], t)

fun strip_all_open vars (Const (@{const_name "Pure.all"}, _) $ Abs (abs as (x, T, b))) = 
      strip_all_open ((x,T)::vars) b
  | strip_all_open vars t = (vars, t)

fun gen_strip_concl_of_subgoal dest t =
  let
    fun dest_all t = case try dest t of
          SOME (v, t') => let val (vs, r) = dest_all t' in (v::vs, r) end
        | NONE => ([],t);
  in
    t |> dest_all |> apfst rev ||> Logic.strip_imp_concl 
  end

val strip_concl_of_subgoal = gen_strip_concl_of_subgoal Logic.dest_all_global
val strip_concl_of_subgoal_open = gen_strip_concl_of_subgoal dest_all_open

val concl_of_subgoal = snd o (strip_concl_of_subgoal)
val concl_of_subgoal_open = snd o (strip_concl_of_subgoal_open)

fun subst_rename_bounds ctxt bounds t =
  let
    val (names', ctxt') = Variable.variant_fixes (map fst bounds) ctxt
    val bounds' = names' ~~ map snd bounds
  in ((bounds', subst_bounds (map Free bounds', t)), ctxt') end

fun strip_concl_of_subgoal' ctxt t = 
 let
   val (bounds, t) = strip_concl_of_subgoal_open t
   val ((bounds', t'), ctxt') = subst_rename_bounds ctxt bounds t
 in ((rev bounds', t'), ctxt') end

fun concl_of_subgoal' ctxt t = #2 (#1 (strip_concl_of_subgoal' ctxt t))

fun split_filter P [] = ([], [])
  | split_filter P (x::xs) = 
      let
        val (hits, misses) = split_filter P xs
      in 
        if P x then (x::hits, misses) else (hits, x::misses) 
      end  
 
fun split_map_filter f [] = ([], [])
  | split_map_filter f (x::xs) = 
      let
         val (somes, nones) = split_map_filter f xs
      in 
        case f x of
          SOME y => (y :: somes, nones)
        | NONE => (somes, x :: nones)
      end

fun OFs asms thms =
  let
    fun maybe_OF thm = the_default thm (try (fn thm => thm OF asms) thm)
  in
    map maybe_OF thms
  end

fun first_OF [] thm = NONE
  | first_OF (prem::ps) thm = 
       case try (fn thm => thm OF [prem]) thm of 
         SOME thm => SOME thm
       | NONE => first_OF ps thm

fun first_OFs prems = split_map_filter (first_OF prems) 

fun simple_prove ctxt term tac =
  let
    val goal = timeit_msg 2 ctxt (fn _ => "simple_prove cterm_of: ") (fn _ =>  Thm.cterm_of ctxt term)
  in
    case SINGLE (tac {prems = [], context= ctxt}) (Goal.init goal) of 
      NONE => error ("simple_prove failed on: " ^ Syntax.string_of_term ctxt term)
    | SOME st => Goal.finish ctxt st
  end

fun check_finished check ctxt th =
  if check th then th
  else raise THM ("Proof failed.\n" ^ Goal_Display.string_of_goal ctxt th, 0, [th]);

fun check_simple_cprove check ctxt st tac =
    case SINGLE tac st of 
      NONE => error ("simple_cprove failed on: " ^ Thm.string_of_thm ctxt st)
    | SOME st => Goal.conclude (check_finished check ctxt st)

fun simple_cprove ctxt st tac =
    case SINGLE tac st of 
      NONE => error ("simple_cprove failed on: " ^ Thm.string_of_thm ctxt st)
    | SOME st => Goal.finish ctxt st
 
fun solve_sideconditions ctxt thm tac =
 let
   val nprems = Thm.nprems_of thm
   val st = Goal.protect nprems thm
 in
   simple_cprove ctxt st tac
 end

fun check_solve_sideconditions check ctxt thm tac =
 let
   val nprems = Thm.nprems_of thm
   val st = Goal.protect nprems thm
 in
   check_simple_cprove check ctxt st tac
 end

fun discharge_all_prems assms thms =
  let
    val (discharged_one_prem, discharged_nothing) = first_OFs assms thms
    val _ = null discharged_nothing orelse 
            forall (fn thm => Thm.nprems_of thm = 0) discharged_nothing orelse
            (raise THM ("discharge_all_prems, some unsolved prems: ", 0, discharged_nothing))
    val (solved, unsolved) = split_filter (fn thm => Thm.nprems_of thm = 0) discharged_one_prem
    val thms' = if null unsolved then [] else discharge_all_prems assms unsolved
  in 
    thms' @ solved @ discharged_nothing
  end


fun try_solve_sideconditions ctxt tac thm =
  if Thm.nprems_of thm = 0 then 
    SOME thm
  else
    try (solve_sideconditions ctxt thm) (ALLGOALS (tac ctxt))

fun derive_unconditional_facts_from_assms solver assms rules =
  let
    val (discharged_one_prem, discharged_nothing) = first_OFs assms rules
    val unconditional = map_filter solver discharged_nothing
    val (solved, unsolved) = split_filter (fn thm => Thm.nprems_of thm = 0) discharged_one_prem
    val solved' = if null unsolved then [] else derive_unconditional_facts_from_assms solver assms unsolved
  in 
    unconditional @ solved @ solved' 
  end


fun pretty_typs ctxt ts =
  Pretty.list "[" "]" (map (Syntax.pretty_typ ctxt) ts)
fun string_of_typs ctxt ts = pretty_typs ctxt ts |> Pretty.string_of
fun pretty_terms ctxt ts =
  Pretty.list "[" "]" (map (Syntax.pretty_term ctxt) ts)
fun string_of_terms ctxt ts = pretty_terms ctxt ts |> Pretty.string_of
fun string_of_cterm ctxt = Thm.term_of #> Syntax.string_of_term ctxt
fun string_of_cterms ctxt = map Thm.term_of #> string_of_terms ctxt

fun pretty_thms ctxt thms =
  Pretty.list "[" "]" (map (Thm.pretty_thm ctxt) thms)
fun pretty_big_list_thms name ctxt thms =
  Pretty.big_list name  (map (Thm.pretty_thm_item ctxt) thms)

fun pretty_numbered_rule ctxt (i, rule) = Pretty.block [Pretty.str (string_of_int i ^ ": "), Thm.pretty_thm ctxt rule]
fun pretty_rules name ctxt rs =  
  Pretty.block (Pretty.fbreaks (Pretty.str name :: map (pretty_numbered_rule ctxt) (tag_list 1 rs)))


fun string_of_thms ctxt thms = pretty_thms ctxt thms |> Pretty.string_of
fun big_list_of_thms name ctxt thms = pretty_rules name ctxt thms |> Pretty.string_of


fun unflatten thm_name = 
  let 
    val (xs, sfx) = thm_name |> space_explode "_" |> split_last
    
  in
    case Library.read_int (Symbol.explode sfx)  of
      (n, []) => (space_implode "_" xs, n)
    | _ => (thm_name, 0)

  end

fun guess_binding_of_thm ctxt thm =
  let
    val facts = Proof_Context.facts_of ctxt
    val raw_name = Thm.derivation_name thm
    val pos = \<^try>\<open>(raw_name |> unflatten |> fst |> Facts.intern facts 
                |> Name_Space.the_entry (Facts.space_of facts) |> #pos)
              catch _ =>  Position.make (Thread_Position.get ())\<close>
  in
    Binding.make(raw_name, pos)
  end

fun define_global def thy =
  let
    val lthy = Named_Target.theory_init thy
    val ((t, (_, thm)), lthy) = lthy |> Local_Theory.define def
    val phi = Local_Theory.target_morphism lthy
  in
    ((Morphism.term phi t, Morphism.thm phi thm), Local_Theory.exit_global lthy)
  end

(* Tactics *)

fun single_resolve_assm_tac ctxt thm = fn i => 
 let
   val nprems = Thm.nprems_of thm
 in
   resolve_tac ctxt [thm] i THEN 
   (if nprems > 0 then 
     EVERY (map (Method.assm_tac ctxt) (i + nprems downto i)) 
    else Tactical.all_tac)
 end

fun resolve_assm_tac ctxt thms = FIRST' (map (single_resolve_assm_tac ctxt) thms)

fun strip_comb_cterm ct =
  let             
    fun strip args ct =
      case try Thm.dest_comb ct of
        NONE => (ct, args)
      | SOME (l, r) => 
          strip (r::args) l
  in strip [] ct end

fun Trueprop_cterm P = \<^instantiate>\<open>P = P in cterm \<open>Trueprop P\<close>\<close>

fun cdest_funT cT = (Thm.dest_ctyp0 cT, Thm.dest_ctyp1 cT) 
val crange_type = Thm.dest_ctyp1
val cdom_type = Thm.dest_ctyp0

fun applies ps f = f |> fold (fn p => fn f => Thm.apply f p) ps
fun apply_beta_conv f p = Drule.beta_conv f p handle THM _ => Thm.apply f p
fun beta_applies ps f = f |> fold 
  (fn p => fn f => apply_beta_conv f p) ps  
val lambdas = fold_rev Thm.lambda_name
fun lambdas_tupled [] f = f
  | lambdas_tupled [x] f = Thm.lambda_name x f
  | lambdas_tupled (x:: xs) f =
       let
          val f' = lambdas_tupled xs f
          val f'' = Thm.lambda_name x f'
          val (xsT, rT) = cdest_funT (Thm.ctyp_of_cterm f')
       in \<^instantiate>\<open>'a = \<open>Thm.ctyp_of_cterm (snd x)\<close> and 'b = xsT and 'c = rT and 
            f = f'' in cterm \<open>case_prod f\<close>\<close> 
       end

fun can_unify ctxt ct1 ct2 =
  let
    val context = Context.Proof ctxt
    val t1 = Thm.term_of ct1 |> Logic.mk_term
    val t2 = Thm.term_of ct2 |> Logic.mk_term
    val maxidx = (~1) |> fold (Integer.max o Thm.maxidx_of_cterm) [ct1, ct2]

  in
    if Term.could_unify (t1, t2) then
      is_some (Seq.pull (Unify.unifiers (context, Envir.empty maxidx, [(t1, t2)])))
    else
      false
  end

fun is_reflexive ctxt eq_thm =
  can_unify ctxt (Thm.cprop_of @{thm reflexive}) (Thm.cconcl_of eq_thm)

fun single_resolve_consumes_assm_tac ctxt thm = fn i =>
  let
    val consumes = Int.max (0, Rule_Cases.get_consumes thm)
  in
    resolve_tac ctxt [thm] i THEN
    (if consumes > 0 then
       EVERY (map (Method.assm_tac ctxt) (i + (consumes - 1) downto i))
     else Tactical.all_tac)
  end
  
fun resolve_consumes_assm_tac ctxt thms = FIRST' (map (single_resolve_consumes_assm_tac ctxt) thms)
 
end

fun DETERM' tac i = DETERM (tac i)

local
fun FILTER_verbose pred leave_last_failed msg ctxt tac i st = 
  let
    val _ = Utils.verbose_print_subgoal_tac 5 ("TRYING: " ^ msg) ctxt i st         
    fun filter_verb last_st s =
      Seq.make (fn () =>
        (case Seq.pull s of
          NONE => 
            let
              val _ = Utils.verbose_print_subgoal_tac 4 (msg ^ " FAILED: empty result sequence after") ctxt i last_st          
            in 
              if leave_last_failed then 
                SOME (last_st, Seq.empty) 
              else 
                NONE
            end
        | SOME (st, s') => 
            if pred st then 
              let val _ = Utils.verbose_msg 3 ctxt (fn _ => msg ^ " succeeded on subgoal " ^ string_of_int i)
              in SOME (st, filter_verb st s') end  
            else
              let val _ = Utils.verbose_print_subgoal_tac 3 (msg ^ " failed, backtracking...") ctxt i st
              in Seq.pull (filter_verb st s') end))
  in filter_verb st (tac i st) end

fun gen_SOLVED_verbose leave_last_failed msg ctxt tac i st =
 let
  val orig_subgoals = Thm.nprems_of st
  fun solved st = (Thm.nprems_of st < orig_subgoals)
 in
   FILTER_verbose solved leave_last_failed msg ctxt tac i st
 end

in
(* tac can have several shots until it succeeds, but first solution is the final one. *)
fun SOLVED_verbose msg ctxt tac = DETERM' (gen_SOLVED_verbose false msg ctxt tac)
(* tac can have several shots until it succeeds, all solutions are enumerated.
   Enumeration might make sense in case of possibly different assignments to schematic variables in subgoal. *)
fun NONDET_SOLVED_verbose msg ctxt tac = gen_SOLVED_verbose false msg ctxt tac
(* tac only has one shot to succeed. *)
fun SOLVED_DETERM_verbose msg ctxt tac = gen_SOLVED_verbose false msg ctxt (DETERM' tac)


(* tac can have several shots until it succeeds, but first solution is the final one.
   Leaves last state as result in case of failure.  *)
fun SOLVED_verbose_continue msg ctxt tac = DETERM' (gen_SOLVED_verbose true msg ctxt tac)
(* tac only has one shot to succeed. 
   Leaves last state as result in case of failure. *)
fun SOLVED_DETERM_continue msg ctxt tac = gen_SOLVED_verbose true msg ctxt (DETERM' tac)



fun conv_by_tac tac ctxt ct =
 let
   val eq_prop = \<^instantiate>\<open>'a = \<open>Thm.ctyp_of_cterm ct\<close> and x = ct in 
         cprop (schematic) \<open>x \<equiv> CONV_ID X\<close> for x X::"'a::{}"\<close>
   val eq_thm = Goal.prove_internal ctxt [] eq_prop (fn _ => 
          tac ctxt THEN 
          resolve_tac ctxt @{thms CONV_ID_intro} 1)
          |> Conv.fconv_rule (Conv.arg_conv (Conv.rewr_conv @{thm CONV_ID_def}))
 in
   eq_thm
 end 

fun eq_by_tac tac ctxt ct = @{thm meta_eq_to_obj_eq} OF [conv_by_tac tac ctxt ct]

end

infix 0 UNCHANGED_ORELSE_ALL_NEW

fun (tac1 UNCHANGED_ORELSE_ALL_NEW tac2) =
  (CHANGED_GOAL tac1 THEN_ALL_NEW tac2) ORELSE' K all_tac

infix 0 OF_COMP 
fun (rule OF_COMP thms) = rule |> fold (fn th => fn r => th COMP r) thms


(*Repeatedly dig into any emerging subgoals, potentially leaving subgoals unsolved 
  in contrast to REPEAT_ALL_NEW *)
fun REPEAT_CHANGED_ALL_NEW tac =
  tac UNCHANGED_ORELSE_ALL_NEW (TRY o (fn i => REPEAT_CHANGED_ALL_NEW tac i));


val string_of_typs = Utils.string_of_typs
val string_of_terms = Utils.string_of_terms
val string_of_cterm = Utils.string_of_cterm
val string_of_cterms = Utils.string_of_cterms
val string_of_thms = Utils.string_of_thms

fun assert p msg = if p then () else error msg;
fun TRY' tac = tac ORELSE' (K all_tac);

 