(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Rewrite L2 specifications to use "nat" and "int" data-types instead of
 * "word" data types. The former tend to be easier to reason about.
 *
 * The main interface to this module is translate (and inner functions
 * convert and define). See AutoCorresUtil for a conceptual overview.
 *)

structure WordAbstract =
struct

(* Convenience shortcuts. *)
val warning = Utils.ac_warning
val apply_tac = Utils.apply_tac
val the' = Utils.the'
val timeit_msg = Utils.timeit_msg
val timing_msg' = Utils.timing_msg'
val verbose_msg = Utils.verbose_msg
val verbose_msg_tac = Utils.verbose_msg_tac

structure Data = Generic_Data (
  type T = (stamp * (int -> term -> term)) list;
  val empty = [];
  fun merge (mk_patterns1, mk_patterns2) =
    if pointer_eq (mk_patterns1, mk_patterns2) then mk_patterns1 
    else AList.merge (op =) (K true) (mk_patterns1, mk_patterns2);
)
  
fun add_pattern mk_pattern =
  Data.map (fn mk_patterns => mk_patterns @ [(stamp (), mk_pattern)])
    
val wa_resolve_match_rules = AutoCorresTrace.mk_resolve_match_rules (map snd o Data.get)

type WARules = {
     signed : bool,
     lentype : typ, ctype : typ, atype : typ,
     abs_fn : term, inv_fn : term,
     rules : thm list
}

fun WARules_update rules_upd {signed, lentype, ctype, atype, abs_fn, inv_fn, rules} =
  {signed = signed, lentype = lentype, ctype = ctype, atype = atype,
   abs_fn = abs_fn, inv_fn = inv_fn,
   rules = rules_upd rules}

val word_sizes = [@{typ 64}, @{typ 32}, @{typ 16}, @{typ 8}]

fun mk_word_abs_rule T =
{
  signed = false,
  lentype = T,
  ctype = \<^instantiate>\<open>'W = T in typ \<open>'W::len word\<close>\<close>,
  atype = @{typ nat},
  abs_fn = \<^instantiate>\<open>'W = T in term \<open>unat :: ('W::len) word => nat\<close>\<close>,
  inv_fn = \<^instantiate>\<open>'W = T in term \<open>of_nat :: nat => ('W::len) word\<close>\<close>,
  rules = @{thms word_abs_word}
}

val word_abs : WARules list =
    map mk_word_abs_rule word_sizes

fun mk_sword_abs_rule T =
{
  signed = true,
  lentype = T,
  ctype = \<^instantiate>\<open>'W = T in typ \<open>'W::len signed word\<close>\<close>,
  atype = @{typ int},
  abs_fn = \<^instantiate>\<open>'W = T in term \<open>sint :: ('W::len) signed word => int\<close>\<close>,
  inv_fn =\<^instantiate>\<open>'W = T in term \<open>of_int :: int => ('W::len) signed word\<close>\<close>,
  rules = @{thms word_abs_sword}
}

val sword_abs : WARules list =
    map mk_sword_abs_rule word_sizes

(* Make rules for signed word reads from the lifted heap.
 *
 * The lifted heap stores all words as unsigned, but we need to avoid
 * generating unsigned arith guards when accessing signed words.
 * These rules are placed early in the ruleset and kick in before the
 * unsigned abstract_val rules get to run. *)
fun mk_sword_heap_get_rule ctxt heap_info (rules: WARules) =
  let val uwordT = Type (@{type_name word}, [#lentype rules])
  in case try (HeapLiftBase.get_heap_getter heap_info) uwordT of
         NONE => NONE
       | SOME getter => SOME (@{thm abstract_val_heap_sword_template}
                              |> Drule.infer_instantiate ctxt
                                   [(("heap_get", 0), Thm.cterm_of ctxt getter)])
  end

(* Get abstract version of a HOL type. *)
fun get_abs_type_atomic (rules : WARules list) T =
    the_default T 
        (List.find (fn r => #ctype r = T) rules
         |> Option.map (fn r => #atype r))

fun get_abs_type rules \<^Type>\<open>prod T1 T2\<close> = \<^Type>\<open>prod \<open>get_abs_type rules T1\<close> \<open>get_abs_type rules T2\<close>\<close>
  | get_abs_type rules T = get_abs_type_atomic rules T

(* Get abstraction function for a HOL type. *)
fun get_abs_fn_atomic (rules : WARules list) T =
    the_default \<^Const>\<open>id T\<close>
        (List.find (fn r => #ctype r = T) rules
         |> Option.map (fn r => #abs_fn r))

fun get_abs_fn rules \<^Type>\<open>prod T1 T2\<close> =
     let
       val f1 = get_abs_fn rules T1
       val f2 = get_abs_fn rules T2
     in
      \<^instantiate>\<open>'a=T1 and 'b=\<open>range_type (fastype_of f1)\<close> and 'c=T2 and 'd=\<open>range_type (fastype_of f2)\<close> and f1 = f1 and f2 = f2 
        in term \<open>map_prod f1 f2 \<close>\<close>
     end
  | get_abs_fn rules T = get_abs_fn_atomic rules T

fun get_abs_fn_exit rules T =
  let
    val ex = get_abs_fn rules T
  in
    ex
  end

fun get_abs_inv_fn (rules : WARules list) t =
    the_default t 
        (List.find (fn r => #ctype r = fastype_of t) rules
         |> Option.map (fn r => #inv_fn r $ t))

(*
 * From a list of abstract arguments to a function, derive a list of
 * concrete arguments and types and a precondition that links the two.
 *)
fun get_wa_conc_args rules fn_ptr_infos l2_infos fn_name fn_args lthy =
let
  (* Construct arguments for the concrete body. We use the abstract names
   * with a prime ('), but with the concrete types. *)
  val args0 = case AList.lookup (op =) fn_ptr_infos fn_name of
         SOME info => #args (info FunctionInfo.L2) (* args should not change in HL phase *)
      | NONE => the (Symtab.lookup l2_infos fn_name) |> FunctionInfo.get_plain_args;
  val conc_types = map snd args0;
  val (conc_names, lthy) = Variable.variant_fixes (map (fn Free (n, T) => n ^ "'") fn_args) lthy;
  val conc_args = map Free (conc_names ~~ conc_types)
  val arg_pairs = (conc_args ~~ fn_args)

  (* Create preconditions that link the new types to the old types. *)
  val precond = arg_pairs
      |> map (fn (old, new) => \<^infer_instantiate>\<open>old = old and f = \<open>get_abs_fn rules (fastype_of old)\<close> and n = new 
               in term \<open>abs_var n f old\<close>\<close> lthy)
        
      |> Utils.mk_conj_list
in
  (conc_types, conc_args, precond, arg_pairs, lthy)
end

(* Get the expected type of a function from its name;  *)
fun get_monad_type rules fn_ptr_infos l2_infos fn_name =
let
  val (retT, exitT, stateT) = case AList.lookup (op =) fn_ptr_infos fn_name of 
         SOME info => let val wa_info = info FunctionInfo.WA 
                      in (AutoCorresData.retT_from_fn_ptr_info wa_info, @{typ "exit_status c_exntype"}, AutoCorresData.state_type_of_exn_monad (#prog_env wa_info)) end
      | NONE =>
          let
            val fn_info = the (Symtab.lookup l2_infos fn_name)
          in 
            (get_abs_type rules (FunctionInfo.get_return_type fn_info),
              get_abs_type rules (FunctionInfo.get_exn_type fn_info),
              AutoCorresData.state_type_of_exn_monad (FunctionInfo.get_const fn_info))
          end
in
  AutoCorresData.mk_l2monadT stateT retT exitT
end


(* Get the expected type of a function from its name; excluding the *)
fun get_expected_fn_type rules fn_ptr_infos l2_infos fn_name =
let
  val (argTs) = case AList.lookup (op =) fn_ptr_infos fn_name of 
        SOME info => map snd (#args (info FunctionInfo.WA))
      | NONE =>
          let
           val fn_info = the (Symtab.lookup l2_infos fn_name)
          in  map ((get_abs_type rules) o snd) (FunctionInfo.get_plain_args fn_info) end
in
  argTs ---> get_monad_type rules fn_ptr_infos l2_infos fn_name
end


fun mk_fn_ptr_infos ctxt prog_info fn_args info =
  AutoCorresData.mk_fn_ptr_infos ctxt prog_info "" fn_args info

(* Get the expected theorem that will be generated about a function. *)
fun get_wa_corres_prop skips prog_info rules prev_phase fn_ptr_infos l2_infos ctxt assume fn_name
                        function_free fn_args =
let

  val wa_corres_attr = AutoCorresData.corres_thm_attribute (ProgramInfo.get_prog_name prog_info) skips FunctionInfo.WA fn_name
  val (old_fn, new_fn, old_retT, old_errT, prev_props) = case AList.lookup (op =) fn_ptr_infos fn_name of
    SOME info => 
      let 
        val prev_info = info prev_phase
        val wa_info = info FunctionInfo.WA
        val P_prev = #prog_env prev_info
        val P_wa = #prog_env wa_info
        val p = Free (#ptr_val wa_info)
        val prev_args = map Free (#args prev_info)
      in (P_prev $ p, P_wa $ p, AutoCorresData.retT_from_fn_ptr_info prev_info, @{typ "exit_status c_exntype"}, []) end 
    | NONE => let val info = the (Symtab.lookup l2_infos fn_name) 
              in (FunctionInfo.get_const info, function_free, 
                  FunctionInfo.get_return_type info, FunctionInfo.get_exn_type info, []) end

  val (old_arg_types, old_args, precond, arg_pairs, _)
      = get_wa_conc_args rules fn_ptr_infos l2_infos fn_name fn_args ctxt
  val old_term = betapplys (old_fn, old_args)
  val new_term = betapplys (new_fn, fn_args)

  val prems = case Symtab.lookup l2_infos fn_name of 
        SOME info => (* regular function not a function pointer parameter *)
          let  (* We add corres preconditions for any function pointer parameter in this function *)
            val fn_ptr_param_infos = mk_fn_ptr_infos ctxt prog_info fn_args info           
          in
            fn_ptr_param_infos 
            |> map (fn (ptr, ptr_info) => 
                let
                  val wa_info = ptr_info FunctionInfo.WA
                  val p = Free (#ptr_val wa_info)
                  val args = map Free (#args wa_info)
                  val (prev_props, (wa_prop, _)) = 
                     get_wa_corres_prop skips prog_info rules prev_phase fn_ptr_param_infos l2_infos ctxt false ptr
                        p args
                  val prev_props = map fst prev_props  
                  val wa_prop = fold Logic.all (rev args) wa_prop
                in  prev_props @ [wa_prop] end)
            |> flat
          end
        | NONE => [] 

in
 (prev_props,
  (Logic.list_implies (prems, \<^infer_instantiate>\<open>rt = \<open>get_abs_fn rules old_retT\<close> and 
       ex = \<open>get_abs_fn_exit rules old_errT\<close> and A = new_term and 
       C = old_term  and P = precond
     in prop \<open>corresTA (%x. P) rt ex A C\<close>\<close> ctxt)
    |> fold (fn t => fn v => Logic.all t v) (rev (map fst arg_pairs)), [wa_corres_attr]))
end

(* Get arguments passed into the function. *)
fun get_expected_fn_args rules fn_ptr_infos l2_infos fn_name =
  case AList.lookup (op =) fn_ptr_infos fn_name of 
    SOME info => #args (info FunctionInfo.WA)
   | NONE => map (apsnd (get_abs_type rules)) (FunctionInfo.get_plain_args (the (Symtab.lookup l2_infos fn_name)))

(*
 * Convert a theorem of the form:
 *
 *    corresTA (%_. abs_var True a f a' \<and> abs_var True b f b' \<and> ...) ...
 *
 * into
 *
 *   [| abstract_val A a f a'; abstract_val B b (f b') |] ==> corresTA (%_. A \<and> B \<and> ...) ...
 *
 * the latter of which better suits our resolution approach of proof
 * construction.
 *)
fun extract_preconds_of_call thm =
let
  fun r thm =
    r (thm RS @{thm corresTA_extract_preconds_of_call_step})
    handle THM _ => (thm RS @{thm corresTA_extract_preconds_of_call_final}
    handle THM _ => thm RS @{thm corresTA_extract_preconds_of_call_final'});
in
  r (thm RS @{thm corresTA_extract_preconds_of_call_init})
end

fun norm_abstract_val_id thm =
 let
   val n = Thm.nprems_of thm
   fun try_rs i thm = @{thm abstract_val_id_unit_ptr} RSN (i, thm) handle THM _ => thm 
 in  
   thm |> fold try_rs (n downto 1)
 end

fun maybe_extract_preconds_of_call thm =
 extract_preconds_of_call thm handle THM _ => thm

fun extract_preconds_of_call_in_prems thm =
 let
   fun extract i thm =
     let
       fun r thm =
         r (@{thm corresTA_extract_preconds_of_call_step_prems} RSN (i, thm) )
         handle THM _ => (@{thm corresTA_extract_preconds_of_call_final_prems} RSN (i, thm) 
         handle THM _ => @{thm corresTA_extract_preconds_of_call_final'_prems} RSN (i, thm));
     in
        r (@{thm corresTA_extract_preconds_of_call_init_prems} RSN (i, thm))
     end

   val relevant_prems = Thm.prems_of thm |> tag_list 1 
     |> map_filter (fn (i, t) => Utils.concl_of_subgoal_open t 
          |> (fn @{term_pat "Trueprop (corresTA _ _ _ _ _)"}  => SOME i | _ => NONE))
 in
   thm |> fold extract (rev relevant_prems)
 end

local
fun is_abstract_val @{term_pat "Trueprop (abstract_val _ _ _ _)"} = true
  | is_abstract_val _ = false;

fun partition xs [] = (xs, [])
  | partition xs (false::ys) = partition (false::xs) ys
  | partition xs (true::ys) = (xs, (true :: ys));

fun rotate_factor prems  =
  let
    val prems = prems |> map is_abstract_val
    val (not_abstract_vals, abstract_vals) = partition [] prems
  in
    if forall (fn y => y = true) abstract_vals 
    then length not_abstract_vals
    else 0
  end
in
fun permute_abstract_val_first thm =
  let
    val prems = Thm.prems_of thm
    val k = rotate_factor prems
  in
    Thm.permute_prems 0 k thm
  end

fun rotate_abstract_val_first i thm =
  let
    val prem = nth (Thm.prems_of thm) (i - 1)
    val prems = Logic.strip_imp_prems prem
    val k = rotate_factor prems
  in
    Thm.rotate_rule k i thm
  end

fun rotate_abstract_val_first_in_prems thm =
  let
    val n = Thm.nprems_of thm
  in 
    thm |> fold rotate_abstract_val_first (1 upto n)
  end
end

val conj_True_simp = @{lemma \<open>(P \<and> True) = P\<close> by simp} 
fun wa_corres_normal_form ctxt thm =
    thm 
    |> maybe_extract_preconds_of_call 
    |> permute_abstract_val_first
    |> extract_preconds_of_call_in_prems
    |> rotate_abstract_val_first_in_prems
    |> Conv.fconv_rule ( 
         (Simplifier.asm_full_rewrite (put_simpset HOL_basic_ss ctxt 
           addsimps ([conj_True_simp] @ @{thms id_tuple_unfold}))))


val assumption_thm = @{lemma "P \<Longrightarrow> P" by simp}

local 
  val abs_var_rules = rev @{thms abs_var_rules}
in
fun abs_var_tac ctxt i ct =  
  let
    val t = Thm.term_of ct
    fun get_var @{term_pat "(\<lambda>s. ?f s = ?c)"} = c \<comment>\<open>special case for @{thm abstract_val_call_L1_arg}\<close>  
    fun get_var @{term_pat "(unat ?c)"} = c \<comment>\<open>special case for @{thm abstract_val_abs_var_sint_unat} and
                                               @{thm abstract_val_abs_var_uint_unat} indexing global const arrays\<close>  
      | get_var c = c
    fun is_id (Const (@{const_name id}, _)) = true
      | is_id _ = false
    val concl = Utils.concl_of_subgoal_open t
    val @{term_pat "Trueprop (abstract_val ?P ?a ?f ?c)"} = concl
    val tac = case get_var c of
                  Bound _ =>
                      (case get_var a of
                         Bound _ => [(assumption_thm, assume_tac ctxt i)] (* appears in context of function pointers as parameters *)
                       | _ => []) @
                      AutoCorresTrace.rules_tac ctxt abs_var_rules i
                | _ => if a = c andalso is_id f  
                       then AutoCorresTrace.rules_tac ctxt @{thms abstract_val_id_True} i
                       else raise Bind 
  in
    tac 
  end
  handle Bind => [];
end

fun TRY' tac i = TRY (tac i)
  
fun solve_conseq_preconds_tac ctxt i =
  let 
    val solve = FIRST' [resolve_tac ctxt @{thms HOL.TrueI}, assume_tac ctxt]
                THEN' (K (Utils.verbose_msg_tac 4 ctxt (fn _ => "solve_conseq_preconds_tac success")))
  in

    EVERY [
       REPEAT (ematch_tac ctxt @{thms conjE} i),
       (solve i) 
         ORELSE
       (REPEAT_ALL_NEW (EVERY' [match_tac ctxt @{thms conjI}, solve, TRY' solve])) i]
  end

fun thin_abs_var_tac ctxt st i = CSUBGOAL (fn (cgoal, i) => 
  let
    val t = Thm.term_of cgoal
    val (bounds, bdy) = Utils.strip_all_open [] t
  
    fun abs [] t = t
      | abs ((x,T)::bs) t = abs bs (Abs (x,T, t))
 
    fun add_abs_var vars (t as @{term_pat "Trueprop (abs_var ?x ?f ?x')"}) = 
          (case x' of Bound n => (n, (x, t))::vars | _ => vars)
      | add_abs_var vars _ = vars

    fun get_concr @{term_pat "corresTA _ _ _ _ ?C"} = C
      | get_concr @{term_pat "abstract_val _ _ _ ?C"} = C
      | get_concr t = error ("thin_abs_var_tac, unexpected term: " ^ @{make_string} t)
 
    fun strip_abs_vars vars t = 
      case t of 
         @{term_pat "PROP ?P ==> PROP ?C"} => strip_abs_vars (add_abs_var vars P) C
      | C => (vars, get_concr (HOLogic.dest_Trueprop C))

    val (abs_vars, concr) = strip_abs_vars [] bdy

    val used_concr_bounds = Term.loose_bnos concr

    val todo_thin_vars = filter_out (fn (n, _) => member (op =) used_concr_bounds n) abs_vars
    val ntodos = length todo_thin_vars

    val _ = if ntodos = 0 
            then (verbose_msg 2 ctxt (fn _ => "thin_abs_var_tac: nothing to be done"); 
                 raise THM ("nothing to be done", i, []))
            else verbose_msg 2 ctxt (fn _ => 
             "thin_abs_var_tac: removing " ^ string_of_int ntodos ^ " unused premise(s)")

    fun thin (n, (_, t)) = CSUBGOAL (fn (cgoal, i) =>
      let
        val lifted_thin_rl = Thm.lift_rule cgoal (Drule.thin_rl)
        val abs_var = abs bounds t |> Thm.cterm_of ctxt
        val thin_rl = Drule.infer_instantiate' ctxt [SOME abs_var] lifted_thin_rl
       in 
         compose_tac ctxt (true, thin_rl, Thm.nprems_of (Drule.thin_rl)) i    
       end)

    fun add_abs_bounds n bounds = 
      case AList.lookup (op =) abs_vars n of
        SOME (Bound m, _) => (m::bounds)
      | _ => bounds

    val used_abs_bounds = [] |> fold add_abs_bounds used_concr_bounds

    val used_bounds = used_abs_bounds @ used_concr_bounds
    val all_abs_bounds = map (fn (n, (Bound m, _)) => [n, m] | _ => []) abs_vars |> flat

    val maxidx = Thm.maxidx_of_cterm cgoal
  in
    EVERY' 
      ((map thin todo_thin_vars) @ 
      [Utils.prune_unused_bounds_tac ctxt maxidx all_abs_bounds used_bounds bdy, 
       Utils.verbose_print_subgoal_tac 4 "after thin_abs_var_tac" ctxt]) i  
  end) st i
  handle THM ("nothing to be done", _, _) => K all_tac st i
      
 


fun wa_fn_ptr info =
  let
    val wa_info = info FunctionInfo.WA
  in (#prog_env wa_info $ Free (#ptr_val wa_info)) end

fun mk_corresTA_fun_ptr_thm prog_info (rec_funs, rec_ptrs) ctxt ((P_prev as Const (_, T_prev), _) , (P as Const (Pname, T), _)) =
 let
   val (ptrT::prev_argTs, monad_prevT) = strip_type T_prev
   val funT = let val (ptrT::argTs, retT) = strip_type T in argTs ---> retT end
   fun mk_fun_ptr fname =HP_TermsTypes.mk_fun_ptr ctxt (ProgramInfo.get_prog_name prog_info) fname
   val (empty, ptr_assoc) = map_filter (fn fname => find_first (fn (n, _) => n = fname) rec_funs) rec_ptrs
     |> filter (fn (_, Free (_, fT)) => fT = funT)  
     |> `null 
     ||> map (apfst mk_fun_ptr) ||> map HOLogic.mk_prod 
     ||> HOLogic.mk_list (HOLogic.mk_prodT (@{typ "unit ptr"}, funT))
   val _ = if empty andalso not (null rec_funs) then raise Match else ()

   val {resT=ret_prevT, stateT, ...} = AutoCorresData.dest_exn_monad_result_type monad_prevT

   val (_ :: argTs, monadT) = strip_type T
   val {resT = retT, ...} = AutoCorresData.dest_exn_monad_result_type monadT

   val prev_args = map (fn T => ("x", T)) prev_argTs
   val args = map (fn T => ("y", T)) argTs

   val rt = ("rt", ret_prevT --> retT)
   val Q = ("Q", stateT --> HOLogic.boolT)
   val R = ("R", stateT --> HOLogic.boolT)
   val Pre = ("P", HOLogic.boolT)
   val (Pre::Q::R::rt::p'::prev_args, ctxt') = Utils.fix_variant_frees ([Pre, Q, R, rt, ("p'", ptrT)] @ prev_args) ctxt
   val (p::args, ctxt') = Utils.fix_variant_frees ([("p", ptrT)]@args) ctxt'
   val abs_val = \<^infer_instantiate>\<open>Pre = Pre and p = p and p' = p' in prop \<open>abstract_val Pre p id p'\<close>\<close> ctxt
   val P_prev = betapplys(P_prev, [p'] @ prev_args)
   val P = if empty then P else \<^infer_instantiate>\<open>P = P and xs = ptr_assoc in term \<open>map_of_default P xs\<close>\<close> ctxt
   val (P, P') = (betapplys(P, [p] @ args), betapplys(P, [p'] @ args))

   fun corres (Q, rt, P, P_prev) = \<^infer_instantiate>\<open>Q = Q and rt = rt and P = P and P_prev = P_prev 
         in prop \<open>corresTA Q rt id P P_prev\<close>\<close> ctxt
   val conj = \<^infer_instantiate>\<open>Pre = Pre and Q = Q in term \<open>\<lambda>s. Pre \<and> Q s\<close>\<close> ctxt
   val impl = \<^infer_instantiate>\<open>R = R and C = conj in term \<open>\<And>s. R s \<Longrightarrow> C s\<close>\<close> ctxt
   val corres_pre = @{term DYN_CALL} $ corres (Q, rt, P', P_prev)
   val goal = corres (R, rt, P, P_prev)

   val [thm] = Goal.prove ctxt' [] [abs_val, corres_pre, impl] goal (fn {context=ctxt,prems=[abs_val, corres_pre, impl], ...} => 
         EVERY [
           Method.insert_tac ctxt [impl, abs_val] 1,
           resolve_tac ctxt @{thms corresTA_assume_and_weaken_pre} 1,
           asm_full_simp_tac (ctxt addsimps @{thms abstract_val_def} delsimps @{thms map_of_default.simps}) 1,
           resolve_tac ctxt [Local_Defs.unfold ctxt @{thms DYN_CALL_def} corres_pre] 1,
           asm_full_simp_tac ctxt 1])
     |> single |> Proof_Context.export ctxt' ctxt
 in
   [("", thm)]
 end
 handle Match => []

(* Convert a program by abstracting words. *)
fun translate
      (skips: FunctionInfo.skip_info)
      (base_locale_opt: string option)
      (prog_info: ProgramInfo.prog_info)
      (* Needed for mk_sword_heap_get_rule *)
      (heap_info: HeapLiftBase.heap_info option)
      (* Note that we refer to the previous phase as "l2"; it may be
       * from the L2 or HL phase. *)
      (unsigned_abs: Symset.key Symset.set)
      (no_signed_abs: Symset.key Symset.set)
      (WA_opt: FunctionInfo.stage)
      (trace_opt: bool)
      (parallel: bool)
      (cliques: string list list)
      (lthy: local_theory)
      : string list list * local_theory =
let
  (*
   * Select the rules to translate each function.
   *)
  val phase = FunctionInfo.WA
  val prev_phase = FunctionInfo.prev_phase skips phase
  val wa_function_name = ProgramInfo.get_mk_fun_name prog_info phase
  fun rules_for fn_name =
      (if Symset.contains unsigned_abs fn_name then word_abs else []) @
      (if Symset.contains no_signed_abs fn_name then [] else sword_abs)

  (* Convert each function. *)
  fun convert lthy l2_infos f: AutoCorresUtil.convert_result =
  let
    val conversion_start = Timing.start ();
    val old_fn_info = the (Symtab.lookup l2_infos f);

    (* Add heap lift workaround for each word length that is in the heap. *)
    fun add_sword_heap_get_rules rules =
      if not (#signed rules) then [] else
      case heap_info of
          NONE => []
        | SOME hi => the_list (mk_sword_heap_get_rule lthy hi rules)
    val wa_rules = rules_for f
    val sword_heap_rules = map add_sword_heap_get_rules wa_rules


    (* Fix argument variables. *)
    val new_fn_args = get_expected_fn_args wa_rules [] l2_infos f;
    val (arg_frees, lthy') = Utils.fix_variant_frees new_fn_args lthy;

    val fn_ptr_infos = mk_fn_ptr_infos lthy' prog_info arg_frees old_fn_info

    (* Add callee assumptions. *)
    val (lthy'', callee_terms) =
      AutoCorresUtil.assume_called_functions_corres lthy' (map (apsnd wa_fn_ptr) (fn_ptr_infos))
        (FunctionInfo.get_recursive_clique old_fn_info)
        (fn f => get_expected_fn_type (rules_for f) fn_ptr_infos l2_infos f)
        (fn lthy => fn assume => fn f => get_wa_corres_prop skips prog_info (rules_for f) prev_phase fn_ptr_infos l2_infos lthy assume f)
        (fn f => get_expected_fn_args (rules_for f) fn_ptr_infos l2_infos f)
        (wa_function_name "");

    val rec_funs = map (fn (n, (t, _)) => (n, t)) callee_terms
    val rec_ptrs = FunctionInfo.get_clique_recursion_fun_ptrs old_fn_info

    val lthy'' = lthy'' 
      |> AutoCorresData.prove_and_note_fun_ptr_intros false (prev_phase, phase) prog_info 
           (mk_corresTA_fun_ptr_thm prog_info (rec_funs, rec_ptrs))

     (* Construct free variables to represent our concrete arguments. *)
    val (conc_types, conc_args, precond, arg_pairs, lthy'')
        = get_wa_conc_args wa_rules fn_ptr_infos l2_infos f arg_frees lthy''

    (* Fetch the function definition, and instantiate its arguments. *)
    val old_body_def = FunctionInfo.get_definition old_fn_info

    (* Get old body definition with function arguments. *)
    val old_term = betapplys (FunctionInfo.get_const old_fn_info, conc_args)
    (* Get a schematic variable accepting new arguments. *)
    val new_var = Var (("A", 0), get_monad_type wa_rules [] l2_infos f)

    (*
     * Generate a schematic goal.
     *
     * We only want ?A to depend on abstracted variables and C to depend on
     * concrete variables. We force this by applying bound variables to C
     * but not to the schematic ?A, giving us something like:
     *
     *     !!a' b'. corresTA ... ?A (C a' b')
     *
     * The abstract side will hence be prevented from capturing (i.e., using)
     * concrete variables. C is not a schematic but a concrete term.
     *)
    val ret = get_abs_fn wa_rules (FunctionInfo.get_return_type old_fn_info)
    val ex = get_abs_fn_exit wa_rules (FunctionInfo.get_exn_type old_fn_info)

    val goal = \<^infer_instantiate>\<open>ra = \<open>ret\<close> and ex = \<open>ex\<close> and
             A = new_var and C = old_term and precond = precond
           in prop \<open>corresTA (\<lambda>x. precond) ra ex A C\<close>\<close> lthy''
        |> fold (fn t => fn v => Logic.all t v) (rev (map fst arg_pairs))
        |> Thm.cterm_of lthy''
        |> Goal.init
        |> Utils.apply_tac lthy'' "move precond to assumption" (resolve_tac lthy'' @{thms corresTA_precond_to_asm} 1)
        |> Utils.apply_tac lthy'' "split precond" (REPEAT (CHANGED (eresolve_tac lthy'' @{thms conjE} 1)))
        |> Utils.apply_tac lthy'' "remove abs_var p id p'" 
             (asm_full_simp_tac (put_simpset HOL_ss lthy'' addsimps  @{thms abs_var_id_unit_ptr}) 1) 
        |> Utils.apply_tac lthy'' "create schematic precond" (resolve_tac lthy'' @{thms corresTA_precond_to_guard} 1) 
        |> Utils.apply_tac lthy'' "unfold RHS" (CHANGED (Utils.unfold_once_tac lthy'' old_body_def 1))
    val more_corres = Named_Theorems.get lthy'' @{named_theorems wa_corres} |> map (wa_corres_normal_form lthy'') 
    val known_function_corres = Named_Theorems.get lthy'' @{named_theorems known_function_corres} |> map (wa_corres_normal_form lthy'') 
    val rules = Utils.get_rules lthy'' @{named_theorems word_abs}
                @ List.concat (sword_heap_rules @ map #rules wa_rules)
                @ @{thms word_abs_default}
                @ more_corres
                @ known_function_corres
    val fo_rules = [@{thm abstract_val_fun_app}] 
    val fun_ptr_intros = Named_Theorems.get lthy'' @{named_theorems "fun_ptr_intros"}
    val rules = ((map (snd #> #2 #> hd #> wa_corres_normal_form lthy'' ) callee_terms)) @ 
                fun_ptr_intros @
                (rev rules)
    (* Apply a conversion to the abstract/concrete side of the given "abstract_val" term. *)
    fun wa_conc_body_conv conv =
      Conv.params_conv (~1) (K (Conv.concl_conv (~1) ((Conv.arg_conv (Utils.nth_arg_conv 4 conv)))))

    (*
     * Recursively solve subgoals.
     *
     * We allow backtracking in order to solve a particular subgoal, but once a
     * subgoal is completed we don't ever try to solve it in a different way.
     *
     * This allows us to try different approaches to solving subgoals,
     * hopefully reducing exponential explosion (of many different combinations
     * of "good solutions") once we hit an unsolvable subgoal.
     *)

    (*
     * Eliminate a lambda term in the concrete state, but only if the
     * lambda is "real".
     *
     * That is, we don't attempt to eta-expand in order to apply the theorem
     * "abstract_val_lambda", because that may lead to an infinite loop with
     * "abstract_val_fun_app".
     *)
    val lambda_tac = SUBGOAL (fn (t, i) =>
      case Utils.concl_of_subgoal_open t of
        (Const (@{const_name "Trueprop"}, _) $
            (Const (@{const_name "abstract_val"}, _) $ _ $ _ $ _ $ (t as (
                Abs (_, _, _))))) =>
                  if fst (Utils.eta_redex t) then no_tac 
                  else resolve_tac lthy'' @{thms abstract_val_lambda} i 
      | _ => no_tac )

    val thin_prems = Utils.THIN_tac thin_abs_var_tac 

    val rules_tac = wa_resolve_match_rules (Context.Proof lthy'') rules 1 

    val check = AutoCorresUtil.check_dyn_call_goal lthy prog_info (prev_phase, FunctionInfo.WA)

    (* All tactics we try, in the order we should try them. *)
    fun step_tacs ctxt ct = 
        [(@{thm thin_rl}, thin_prems ctxt 1)]
        @ rules_tac ctxt ct
        @ abs_var_tac ctxt 1 ct 
        @ [(@{thm corresTA_L2_guarded_simple}, AutoCorresUtil.dyn_call_split_simp_sidecondition_tac check
                  @{thms fold_id fold_id_unit} \<comment> \<open>undo unexpected application of @{thm id_apply} to eta expanded@{term "\<lambda>x. id x"}\<close>
                [] ctxt 1)]
        @ (map (fn thm => (thm, Utils.fo_arg_resolve_tac lthy'' thm ctxt 1)) fo_rules)
        @ [(@{thm abstract_val_lambda}, lambda_tac 1)] 
        @ [(@{thm eq_trivI}, resolve_tac ctxt @{thms eq_trivI} 1
             THEN simp_tac ctxt 1)]
        @ [(assumption_thm, solve_conseq_preconds_tac ctxt(*resolve_tac ctxt @{thms Pure.reflexive}*) 1)] (* instantiate inferred DYN_CALL precondition *)
        @ [(@{thm reflexive}, 
            fn st => 
            (if Config.get ctxt ML_Options.exception_trace then
              warning ("Could not solve subgoal: " ^
                (Goal_Display.string_of_goal ctxt st))
            else (); no_tac st))]

    (* Solve the goal. *)

    val thm = timeit_msg 1 lthy'' (fn _ => "Conversion (WA) - trace_solve_prove - " ^ f) (fn () =>
        AutoCorresTrace.trace_solve_prove lthy'' true 
                 step_tacs (SOME (comb_depth_of_term (Thm.prop_of goal) + 23)) goal)

    (* Clean out any final function application ($) constants or "id" constants
     * generated by some rules. *)
    fun corresTA_abs_conv conv =
      Utils.remove_meta_conv (fn ctxt => Utils.nth_arg_conv 4 (conv ctxt)) lthy''

    val thm =
      Conv.fconv_rule (
        corresTA_abs_conv (fn ctxt =>
          (Simplifier.rewrite (
                put_simpset HOL_basic_ss ctxt addsimps @{thms id_def fun_app_def}))
        )
      ) thm

    (* Ensure no schematics remain in the goal. *)
    val _ = Sign.no_vars lthy'' (Thm.prop_of thm)

    val _ = timing_msg' 1 lthy'' (fn _ => "Conversion (WA) - " ^ f) conversion_start;

    (* Apply peephole optimisations to the theorem. *)
    val _ = writeln ("Simplifying (WA) " ^ f)
    val _ = verbose_msg 1 lthy'' (fn _ => "WA (raw) - " ^ f ^ ": " ^ Thm.string_of_thm lthy'' thm);
    val thm = timeit_msg 1 lthy'' (fn _ => "Simplification (WA) - " ^ f) (fn _ =>
      L2Opt.cleanup_thm_tagged 
        (lthy'' |> AutoCorresTrace.put_trace_info f phase FunctionInfo.RAW)
        []
        []
        thm WA_opt 4 trace_opt "WA");
    val _ = verbose_msg 1 lthy'' (fn _ => "WA (opt) - " ^ f ^ ": " ^ Thm.string_of_thm lthy'' thm);

    (* We end up with an unwanted L2_guard outside the L2_recguard.
     * L2Opt should simplify the condition to (%_. True) even if (WA_opt = RAW),
     * so we match the guard and get rid of it here. *)
    val thm = Simplifier.rewrite_rule lthy'' @{thms corresTA_simp_trivial_guard} thm

    (* Convert all-quantified vars in the concrete body to schematics. *)
    val thm = Variable.gen_all lthy'' thm

    (* Extract the abstract term out of a corresTA thm. *)
    fun dest_corresTA_term_abs @{term_pat "corresTA _ _ _ ?t _"} = t
    val f_body =
        Thm.concl_of thm
        |> HOLogic.dest_Trueprop
        |> dest_corresTA_term_abs;

    (* Get actual recursive callees *)
    val rec_callees = AutoCorresUtil.get_rec_callees callee_terms f_body;

    (* Return the constants that we fixed. This will be used to process the returned body. *)
    val callee_consts =
          callee_terms |> map (fn (callee, (const, _)) => (callee, const)) |> Symtab.make;
  in
    { body = f_body,
      proof =  hd (Proof_Context.export lthy'' lthy [thm]),
      rec_callees = rec_callees,
      callee_consts = callee_consts,
      arg_frees = map dest_Free arg_frees
    }
  end

  (* Define a previously-converted function (or recursive function group).
   * lthy must include all definitions from wa_callees. *)
  fun define
        (lthy: local_theory)
        (funcs: AutoCorresUtil.convert_result Symtab.table)
        : local_theory = let
    val l2_infos = AutoCorresData.get_default_phase_info (Context.Proof lthy) (ProgramInfo.get_prog_name prog_info) prev_phase
    val funcs' = Symtab.dest funcs |>
          map (fn result as (name, {proof, arg_frees, ...}) =>
                     (name, (AutoCorresUtil.abstract_fn_body l2_infos result,
                             proof, arg_frees)));
    val (new_thms, lthy') =
          AutoCorresUtil.define_funcs
              skips
              phase prog_info I {concealed_named_theorems=false} (wa_function_name "")
              (fn f => get_expected_fn_type (rules_for f) [] l2_infos f)
              (fn lthy => fn assume => fn f => get_wa_corres_prop skips prog_info (rules_for f) prev_phase [] l2_infos lthy assume f)
              (fn f => get_expected_fn_args (rules_for f) [] l2_infos f)
              funcs'
              lthy;

    in lthy' end;

  val (new_groups, lthy) = lthy |>
      AutoCorresUtil.convert_and_define_cliques skips base_locale_opt prog_info phase parallel
        convert define cliques
in 
 (new_groups, lthy) 
end;

end
