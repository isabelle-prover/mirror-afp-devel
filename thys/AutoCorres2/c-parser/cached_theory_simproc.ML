(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature CACHED_THEORY_SIMPROC =
sig
  type thy_simpsets = simpset Symtab.table;
  val declare_init_thy_simpset: string -> (Proof.context -> Proof.context) -> local_theory -> local_theory
  val init_thy: theory -> theory
  val empty_caches: theory -> theory
  val put_time_warp_simpset: (thy_simpsets -> simpset) -> Proof.context -> Proof.context
  val put_time_warp_simpset': string -> Proof.context -> Proof.context

  val get_cache_ss: Proof.context -> simpset (* FIXME: should I export this? *)
  val trace_data: Proof.context -> unit
  val trace_cache: Proof.context -> unit
  val gen_asm_simproc: (Proof.context * (Proof.context -> thm list -> thm list) * (Proof.context -> thm list -> thm list)) 
        -> (term -> term) -> (Proof.context -> thm -> thm list) -> term list -> cterm -> thm option
  val gen_simproc: Proof.context * (Proof.context -> cterm -> cterm) * (Proof.context -> thm list -> thm list)
        -> (Proof.context -> thm -> thm list) -> cterm -> thm option

  (* Aux. functions *)
  val recert:  Proof.context -> cterm -> cterm
  val add_cache: Proof.context -> thm list -> thm list
  val derive_thms: thm list -> thm -> thm list
  val prems_of: Proof.context -> thm list
  val all_prems_of: Proof.context -> thm list
  val register: term -> Proof.context -> Proof.context
  val check_processing: Proof.context -> term -> unit
  val check_and_register: term -> Proof.context -> Proof.context
  val not_simplified: thm -> bool
  val rewrite_solve: Proof.context -> cterm -> thm
end

structure Cached_Theory_Simproc : CACHED_THEORY_SIMPROC =
struct

\<comment> \<open>
 General Idea

The cache is used for theory level rules for typ instances of @{class c_type}. The cache
is triggerd by simprocs. In order to fill the cache with sensible entries (that can be
applied later on) simplification has to be performed within the proper theory-level context.
So in case of a cache miss we have to "travel back in time" to the correct context before
doing the simplification and deriving the new entry. This context is maintained in 
component \<open>cache_ctxt\<close>. It is updated when we define new instances of @{class c_type}.

 Design of the simpsets / prevention from looping

The simplifier tries simprocs only after unconditional and conditional rules.
So when a rewrite rule has already transformed the redex the simproc will never see that redex.
This has two main implications:
* In order to have the simproc-based cache applied, there must not be a rule in the simpset that
  removes the redex before the cache actually has a chance to see it. This is why we maintain
  several simpsets \<open>thy_simpsets\<close> to control that behaviour. 
* When a cache miss was encountered and we apply the simplifier recursively to rewrite the redex
  we have to take care that the simproc is not invoked again on the same redex. When there
  is an unconditional rule in the simpset that rewrites that redex we are on the safe side. But
  beware of *conditional* rules. When the solver fails to solve the conditions the rule can fail and
  then the simproc is invoked again on the same redex. For these cases we keep the
  redexes the simproc has already seen in the \<open>processing\<close> set.
\<close>

type cache_simpset = simpset * simpset Synchronized.var
fun init_css ss = (ss, Synchronized.var "cache_simpset" ss):cache_simpset
fun persist_css (ss, tmp_ss) = (Synchronized.value tmp_ss, tmp_ss):cache_simpset
val empty_ss = Simplifier.empty_simpset @{context} 
  |> Simplifier.set_mksimps (Simpdata.mksimps Simpdata.mksimps_pairs)
  |> Simplifier.simpset_of
fun empty_css () = init_css empty_ss

fun reset_css ((ss, _):cache_simpset) = init_css ss
fun is_reset_css ((ss, tmp_ss):cache_simpset) =
  pointer_eq (ss, Synchronized.value tmp_ss)  (* FIXME fragile pointer_eq *)
fun merge_css (((ss1, _):cache_simpset), ((ss2, _):cache_simpset)) : cache_simpset  = 
  let
    val ss = Raw_Simplifier.merge_ss (ss1, ss2)
  in init_css ss end


type thy_simpsets = simpset Symtab.table;
type init_thy_simpsets = (Proof.context -> Proof.context) Symtab.table;

@{record \<open>datatype cached_calculation = Cached_Calculation of {
   time_warp_ctxt: Proof.context option,
   is_time_warp_ctxt: bool,  
   cache: cache_simpset, 
   thy_simpsets: thy_simpsets option,
   init_thy_simpsets: init_thy_simpsets,
   processing: Termtab.set (* prevent looping of simprocs *)
   }\<close>}

val empty_cc = make_cached_calculation {
  time_warp_ctxt = NONE, 
  is_time_warp_ctxt = false, 
  cache = empty_css (), 
  thy_simpsets = NONE,
  init_thy_simpsets = Symtab.empty,
  processing = Termtab.empty }

val merge_cc = Utils.fast_merge (fn (cc1, cc2) => 
      make_cached_calculation {
        time_warp_ctxt = NONE,
        is_time_warp_ctxt = false,
        cache = Utils.fast_merge merge_css (get_cache cc1, get_cache cc2),
        thy_simpsets = NONE,
        init_thy_simpsets = Symtab.merge (K true) (get_init_thy_simpsets cc1, get_init_thy_simpsets cc2),
        processing = Termtab.empty
      })

structure Cached_Data = Generic_Data (
struct
  type T = cached_calculation
  val empty = empty_cc;
  val merge = merge_cc
end
)

fun transfer_options ctxt1 ctxt2 =
  ctxt2 
  |> Config.restore Simplifier.simp_trace ctxt1 
  |> Config.restore Simplifier.simp_trace_depth_limit ctxt1
  |> Config.restore Simplifier.simp_depth_limit ctxt1
  |> Config.restore Simplifier.simp_debug ctxt1
  |> Config.restore Utils.verbose ctxt1

fun put_time_warp_simpset select ctxt =
  let
    val data = Cached_Data.get (Context.Proof ctxt)
    val time_warp_ctxt = 
          if get_is_time_warp_ctxt data then 
            ctxt 
          else 
            the (get_time_warp_ctxt data) |> transfer_options ctxt
  in
    Simplifier.put_simpset (select (the (get_thy_simpsets data))) time_warp_ctxt
  end

fun put_time_warp_simpset' name = put_time_warp_simpset (fn tab => the (Symtab.lookup tab name))
  
fun processing ctxt t =
  Termtab.defined (get_processing (Cached_Data.get (Context.Proof ctxt))) t

fun register t =
  Context.proof_map (Cached_Data.map (map_processing (Termtab.insert_set t)))

fun check_and_register t ctxt =
  if processing ctxt t 
  then (
    Utils.verbose_msg 3 ctxt (fn _ => "ABORT already processing: " ^ Syntax.string_of_term ctxt t);  
    raise Match)
  else register t ctxt

fun check_processing ctxt t =
  if processing ctxt t 
  then (
    Utils.verbose_msg 3 ctxt (fn _ => "ABORT already processing: " ^ Syntax.string_of_term ctxt t);  
    raise Match)
  else ()

fun add_init_thy_simpset name init =
  let
  in
    Cached_Data.map (map_init_thy_simpsets (Symtab.update_new (name, init)))
  end


fun declare_init_thy_simpset name init lthy =
  lthy 
  |> Context.proof_map (add_init_thy_simpset name init) 
  |> Local_Theory.background_theory (Context.theory_map (add_init_thy_simpset name init))

fun init_cache cc =
  cc 
  |> map_cache reset_css

fun init_simpsets thy cc =
  let
    val ctxt = Proof_Context.init_global thy
    fun apply init = init ctxt |> Simplifier.simpset_of
    val init_thy_simpsets = Cached_Data.get (Context.Theory thy) |> get_init_thy_simpsets
    val simpsets = Symtab.map (fn _ => fn init => apply init) init_thy_simpsets
  in
    cc
    |> map_thy_simpsets (K (SOME (simpsets)))
  end

fun init_cache_ctxt thy =
 let
   val ctxt = Proof_Context.init_global thy 
    |> Context.proof_map (Cached_Data.map (map_is_time_warp_ctxt (K true)))
 in 
   thy |> Context.theory_map (Cached_Data.map (map_time_warp_ctxt (K (SOME ctxt))))
 end

fun init_thy thy =
  thy
  |> Context.theory_map (Cached_Data.map init_cache)
  |> (fn thy => Context.theory_map (Cached_Data.map (init_simpsets thy)) thy)
  |> init_cache_ctxt

fun persist_cc cc = 
  cc 
  |> map_cache persist_css

val _ = Theory.local_setup (Proof_Context.background_theory (
  Theory.at_begin (fn thy =>
    let
      val data = Cached_Data.get (Context.Theory thy)
    in 
      if is_some (get_thy_simpsets data) then
        NONE (* without this termination case, Theory begin would loop *)
      else 
        SOME (init_thy thy)
    end) #> 
  Theory.at_end (fn thy =>
    let
      val data = Cached_Data.get (Context.Theory thy)
    in 
      if is_reset_css (get_cache data) then
        NONE (* without this termination case, Theory end would loop *)
      else 
        SOME (Context.theory_map (Cached_Data.map persist_cc) thy)
    end)))
 

val empty_caches = 
  Context.theory_map (Cached_Data.map (map_cache (K (empty_css ())))) 
  #> init_thy  
 
val _ = Theory.local_setup (Proof_Context.background_theory (
  Theory.at_begin (fn thy =>
    let
      val data = Cached_Data.get (Context.Theory thy)
    in 
      if is_some (get_thy_simpsets data) then
        NONE (* without this termination case, Theory begin would loop *)
      else 
        SOME (init_thy thy)
    end) #> 
  Theory.at_end (fn thy =>
    let
      val data = Cached_Data.get (Context.Theory thy)
    in 
      if is_reset_css (get_cache data) then
        NONE (* without this termination case, Theory end would loop *)
      else 
        SOME (Context.theory_map (Cached_Data.map persist_cc) thy)
    end)))
 
 
fun trace_data ctxt = Context.Proof ctxt |> Cached_Data.get |> 
  (fn data => tracing ("Cached_Data: " ^ @{make_string} data))

val get_cache_ss = 
  Context.Proof #> Cached_Data.get #> get_cache #> #2 #> Synchronized.value

fun derive_thms rules thm = map_filter (try (fn r => r OF [thm])) rules

fun pretty_cache name get ctxt=
  get ctxt |> Simplifier.dest_ss |> #simps |> map (Thm.pretty_thm_item ctxt o #2) |>
  Pretty.big_list (name ^ ": ")

val pretty_cache = pretty_cache "cache" get_cache_ss

fun trace_cache ctxt = tracing (Pretty.string_of (pretty_cache ctxt))

fun change_cache_ss f ctxt = 
 Synchronized.change (#2 (get_cache (Cached_Data.get (Context.Proof ctxt)))) f


fun add_ss ctxt thms ss = 
  let 
    val _ = Utils.verbose_msg 3 ctxt (fn _ => "caching: " ^ string_of_thms ctxt thms)
  in
    (Raw_Simplifier.put_simpset ss ctxt) addsimps thms |> Raw_Simplifier.simpset_of 
  end

fun add_cache ctxt thms = (change_cache_ss (add_ss ctxt thms) ctxt; thms) 

fun cache_ctxt ctxt = ctxt |> Raw_Simplifier.put_simpset (get_cache_ss ctxt)

fun not_simplified eq = op aconv (apply2 Thm.term_of (Thm.dest_equals (Thm.cprop_of eq)))

fun recert ctxt ct = Thm.cterm_of ctxt (Thm.term_of ct)

fun prems_of ctxt = Simplifier.prems_of ctxt 
|> map (Simplifier.mksimps ctxt) 
|> flat

fun all_prems_of ctxt = (Assumption.all_prems_of ctxt @ Simplifier.prems_of ctxt)
|> map (Simplifier.mksimps ctxt) 
|> flat

val simple_prover =
  SINGLE o (fn ctxt => ALLGOALS (resolve_tac ctxt (let 
     val prems = Assumption.all_prems_of ctxt 
     val _ = Utils.verbose_msg 5 ctxt (fn _ => "simple_prover prems: " ^ string_of_thms ctxt prems) 
     in prems end)));

val rewrite = Raw_Simplifier.rewrite_cterm (false, false, false) simple_prover

fun solve_all_tac solvers ctxt =
  let
    val subgoal_tac = Raw_Simplifier.subgoal_tac (Raw_Simplifier.set_solvers solvers ctxt);
    val solve_tac = subgoal_tac THEN_ALL_NEW (K no_tac);
  in DEPTH_SOLVE (solve_tac 1) end;

fun rewrite_prover ctxt =
  let
    val (unsafe_solvers, _) = Raw_Simplifier.solvers ctxt;
    val tacf = solve_all_tac (rev unsafe_solvers);
    fun prover ctxt th = (Utils.verbose_msg 5 ctxt (fn _ => "rewrite_prover invoked on: " ^ Thm.string_of_thm ctxt th);
         Option.map #1 (Seq.pull (tacf ctxt th)));
  in prover end;

fun rewrite' ctxt = Raw_Simplifier.rewrite_cterm (false, false, false) (rewrite_prover ctxt) ctxt

fun assume_addsimps derive asms goal ctxt =
  let 
    val (goal::asms, ctxt') = Variable.import_terms false (goal:: asms) ctxt
    val (thms, ctxt') = ctxt' |> Assumption.add_assumes (map (Thm.cterm_of ctxt') asms) 
    val _ = Utils.verbose_msg 5 ctxt (fn _ => "assuming: " ^ string_of_thms ctxt' thms)
    val derived_thms = derive ctxt' thms
    val _ = Utils.verbose_msg 5 ctxt (fn _ => "derived: " ^ string_of_thms ctxt' derived_thms)
  in
    (Thm.cterm_of ctxt' goal, ctxt' addsimps thms @ derived_thms)
  end
 
fun gen_asm_simproc (aux,  add, derive_asms) unfold augment asms ct =
  let
    val main_cache = cache_ctxt aux
    val (asms, goal) = 
      if null asms then 
        (asms, Thm.term_of ct)
      else (* We generalise here to remove simplifier internal ":000n" variables *)
        (map Logic.varify_global asms, Logic.varify_global (Thm.term_of ct))
 
    fun prepare ctxt goal =
      if null asms then 
         let val ct = Thm.cterm_of ctxt goal in (ct, ctxt) end 
      else  
         assume_addsimps derive_asms asms goal ctxt 
 
    val (ct, main_asm_cache) = prepare main_cache goal 

    val eq = ct |> rewrite main_asm_cache 
            
    val eq = if not_simplified eq then 
               let
                 val _ = Utils.verbose_msg 5 aux (fn _ => 
                    "cache miss: " ^ Syntax.string_of_term main_asm_cache (Thm.term_of ct))
                 val (ct, aux_ctxt) = prepare aux (unfold goal)
                 val aux_ctxt = register (Thm.term_of ct) aux_ctxt
               in
                 ct 
                 |> Simplifier.rewrite aux_ctxt 
                 |> tap (fn eq => 
                     if not_simplified eq then 
                       (Utils.verbose_msg 5 aux_ctxt (fn _ => "not simplified"); raise Match) 
                     else eq)
                 |> augment aux_ctxt |> Proof_Context.export aux_ctxt aux 
                 |> add aux |> hd
               end
             else 
               let
                 val _ =  Utils.verbose_msg 5 aux (fn _ => 
                    "cache hit: " ^ Thm.string_of_thm main_asm_cache eq)
               in
                 Proof_Context.export main_asm_cache main_cache [eq] |> hd
               end
  in 
    SOME eq
  end handle Match => NONE 
      | THM X => (Utils.verbose_msg 3 aux (fn _ => "gen_asm_simproc THM: " ^ @{make_string} X); NONE) 

fun ground_bool @{term_pat "Trueprop False"} = true
  | ground_bool @{term_pat "Trueprop True"} = true
  | ground_bool _ = false

fun gen_rewrite_solve solver ctxt ct = 
  case Thm.typ_of_cterm ct of
   @{typ bool} => (* ensure that also solvers are tried *)
      let 
         val prop = Thm.apply @{cterm Trueprop} ct
         val prop_eq = rewrite' ctxt prop
         val solve_tac = solver ctxt
         val rhs = Thm.rhs_of prop_eq
         val (res, kind) = if ground_bool (Thm.term_of rhs) then 
                      (@{thm trueprop_eq_bool_meta_eq} OF [prop_eq], "simplification")
                   else 
                      (case try (Goal.prove_internal ctxt [] rhs) (fn _ => solve_tac 1) of
                         SOME thm => (@{thm rewrite_solve_prop_eq} OF [prop_eq, thm], "solver")
                       | _ => (@{thm trueprop_eq_bool_meta_eq} OF [prop_eq], "simplification (failed solver)")) 
         val _ = Utils.verbose_msg 5 ctxt (fn _ => "gen_rewrite_solve " ^ kind ^ " yields: " ^ Thm.string_of_thm ctxt res)
      in
        res
      end
  | _ => Simplifier.rewrite ctxt ct

fun unsafe_solver_tac ctxt = 
  let
    val (unsafe_solvers, _) = Raw_Simplifier.solvers ctxt;
    val solve_tac = FIRST' (map (Raw_Simplifier.solver ctxt) (rev unsafe_solvers));
  in
    solve_tac
  end

val rewrite_solve' = gen_rewrite_solve unsafe_solver_tac
val rewrite_solve = gen_rewrite_solve asm_full_simp_tac


fun gen_simproc (aux, cert, add) augment ct =
  let
    val aux = check_and_register (Thm.term_of ct) aux
    val main_cache = cache_ctxt aux
    val ct = cert main_cache ct
    val eq = ct |> Simplifier.rewrite main_cache
    val eq = if not_simplified eq then 
               let
                 val _ =  Utils.verbose_msg 5 aux (fn _ => 
                    "cache miss: " ^ Syntax.string_of_term aux (Thm.term_of ct))
               in
                 recert aux ct 
                 |> rewrite_solve' aux 
                 |> tap (fn eq => 
                      if not_simplified eq then 
                        (Utils.verbose_msg 5 aux (fn _ => "not simplified"); raise Match) 
                      else eq)
                 |> augment aux |> add aux |> hd
               end
             else 
               let
                 val _ =  Utils.verbose_msg 5 aux (fn _ => 
                    "cache hit: " ^ Thm.string_of_thm main_cache eq)
               in
                 eq
               end
  in 
    SOME eq
  end handle Match => NONE
      | THM X => (Utils.verbose_msg 3 aux (fn _ => "gen_simproc THM: " ^ @{make_string} X); NONE) 
end
