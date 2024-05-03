(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

structure In_Out_Parameters =
struct

val cterm_eq = Utils.cterm_eq

datatype local_kind = Parameter of ProgramInfo.parameter_kind | Stack

datatype xlocal_kind = 
  Eliminate of local_kind 
| Keep of bool (* true = stack *) 
| Other

datatype return_kind =
  Final
| Intermediate
| Nothing

type params_of = string -> term list option -> (cterm * (xlocal_kind * term option)) list

fun kind_of params x: xlocal_kind option = 
  AList.lookup cterm_eq params x |> Option.map fst

fun name_of (Free (x, _)) = x
  | name_of _ = ""

val name_of_cterm = Thm.term_of #> name_of
val named = map (fn ct => (name_of_cterm ct, ct))

fun name_hint_of params x =
  case AList.lookup cterm_eq params x of
    SOME (_, SOME hint) => hint
  | _ => CLocals.embedded_name_hint (name_of_cterm x)

fun is_param params x = AList.defined cterm_eq params x

fun is_out params x = 
  case kind_of params x of
    SOME (Eliminate (Parameter FunctionInfo.Out)) => true
  | SOME (Eliminate (Parameter FunctionInfo.In_Out)) => true
  | _ => false

fun is_eliminate params x = 
  case kind_of params x of
    SOME (Eliminate _) => true
   | _ => false

fun is_keep_non_stack params x = 
  case kind_of params x of
    SOME (Keep false) => true
   | _ => false

type ('a, 'b) fixes = {M:'a, A:'a, t0:'a, s: 'a, t: 'a, 
  params:  ('b * (xlocal_kind * term option)) list, in_out_globals:bool}

type params = (cterm * (xlocal_kind * term option (* name hint *))) list
type args = {
  name: string,
  M: cterm, A: cterm, t0: cterm, s: cterm, t: cterm,
  params: params,
  params_of: params_of,
  in_out_globals: bool,
  prog_info: ProgramInfo.prog_info,
  cguards: thm list, (* FIXME: do I use these? they are in simp set and named theorems *)
  rel_alloc: thm,
  modified: cterm list,            (* modified upto current location *)
  try_modified: (cterm list * return_kind) list,   (* modified upto try location (nested Inl), bool indicates return *)
  disjoint: cterm list,
  return: return_kind,
  params_ctxt: Proof.context,
  addrs_fix_ctxt: Proof.context,
  alloc_ctxt: Proof.context} (* FIXME: unused? *)


type operations = {
  build_context: (string, cterm) fixes -> Proof.context ->  
     ({M: cterm, A: cterm, s: cterm, t: cterm, t0: cterm,
       addrs_fix_ctxt: Proof.context, params_ctxt: Proof.context,
       cguards: thm list, 
       rel_alloc: thm} * Proof.context), (* FIXME: hide this? *)
  mk_refines_cprop:  {closed: bool, apply_f: bool, might_exit: bool, in_out_globals: bool} -> Proof.context -> cterm -> 
    cterm option -> {M:cterm, A:cterm, t0:cterm, s:cterm, t:cterm} option -> params -> (cterm * Proof.context),
  mk_lifted_type: {might_exit: bool} -> Proof.context -> cterm -> params -> typ,
  in_out_expression: bool -> Proof.context -> (cterm * local_kind -> bool) -> args -> cterm ->
    {e': cterm, Q: cterm, result_rel_thm: thm, outs: cterm list, out_vals: (string * cterm) list,
      unit_seed: bool, needs_guard:bool, guard_ctxt: Proof.context, abs_guard: cterm}, (* FIXME: hide internal functions? *)
  in_out_guard: Proof.context -> args -> cterm ->
    {e': cterm, implication_thm: thm},
  in_out_statement: {might_exit:bool} -> Proof.context -> args -> cterm -> (thm * cterm) * Proof.context,
  refines_to_IOcorres_conv: Proof.context -> thm -> thm
};

structure Data = Interpretation_Data(type T = operations val name = "in_out_abstraction");

fun map_modified f {name, M, A, t0, s, t, params, params_of, in_out_globals, prog_info, cguards, rel_alloc, modified, try_modified, disjoint, 
  return, params_ctxt, addrs_fix_ctxt, alloc_ctxt}:args =
  {name = name, M = M, A = A, t0 = t0, s = s, t = t, params = params, params_of = params_of, in_out_globals = in_out_globals,
  prog_info = prog_info, cguards = cguards,
  rel_alloc = rel_alloc, modified = f modified, try_modified = try_modified, disjoint = disjoint, 
  return = return, params_ctxt = params_ctxt, addrs_fix_ctxt = addrs_fix_ctxt, alloc_ctxt = alloc_ctxt}

fun get_modified ({name, M, A, t0, s, t, params, params_of, in_out_globals, prog_info, cguards, rel_alloc, modified, try_modified, disjoint, 
  return, params_ctxt, addrs_fix_ctxt, alloc_ctxt}:args) = modified

fun map_try_modified f {name, M, A, t0, s, t, params, params_of, in_out_globals, prog_info, cguards, rel_alloc, modified, try_modified, disjoint, 
  return, params_ctxt, addrs_fix_ctxt, alloc_ctxt}:args =
  {name = name, M = M, A = A, t0 = t0, s = s, t = t, params = params, params_of = params_of, in_out_globals = in_out_globals,
  prog_info = prog_info,  cguards = cguards,
  rel_alloc = rel_alloc, modified = modified, try_modified = f try_modified, disjoint = disjoint, 
  return = return, params_ctxt = params_ctxt, addrs_fix_ctxt = addrs_fix_ctxt, alloc_ctxt = alloc_ctxt}

fun map_params f {name, M, A, t0, s, t, params, params_of, in_out_globals, prog_info, cguards, rel_alloc, modified, try_modified, disjoint,
  return, params_ctxt, addrs_fix_ctxt, alloc_ctxt}:args =
  {name = name, M = M, A = A, t0 = t0, s = s, t = t, params = f params, params_of = params_of, in_out_globals = in_out_globals,
  prog_info = prog_info, cguards = cguards,
  rel_alloc = rel_alloc, modified = modified, try_modified = try_modified, disjoint = disjoint, 
  return = return, params_ctxt = params_ctxt, addrs_fix_ctxt = addrs_fix_ctxt, alloc_ctxt = alloc_ctxt}

fun map_return f {name, M, A, t0, s, t, params, params_of, in_out_globals, prog_info, cguards, rel_alloc, modified, try_modified, disjoint, 
  return, params_ctxt, addrs_fix_ctxt, alloc_ctxt}:args =
  {name = name, M = M, A = A, t0 = t0, s = s, t = t, params = params, params_of = params_of, in_out_globals = in_out_globals,
  prog_info = prog_info, cguards = cguards,
  rel_alloc = rel_alloc, modified = modified, try_modified = try_modified, disjoint = disjoint, 
  return = f return, params_ctxt = params_ctxt, addrs_fix_ctxt = addrs_fix_ctxt, alloc_ctxt = alloc_ctxt}

fun map_cguards f {name, M, A, t0, s, t, params, params_of, in_out_globals, prog_info, cguards, rel_alloc, modified, try_modified, disjoint,
  return, params_ctxt, addrs_fix_ctxt, alloc_ctxt}:args =
  {name = name, M = M, A = A, t0 = t0, s = s, t = t, params = params, params_of = params_of, in_out_globals = in_out_globals,
  prog_info = prog_info, cguards = f cguards,
  rel_alloc = rel_alloc, modified = modified, try_modified = try_modified, disjoint = disjoint, 
  return = return, params_ctxt = params_ctxt, addrs_fix_ctxt = addrs_fix_ctxt, alloc_ctxt = alloc_ctxt}

fun map_t0 f {name, M, A, t0, s, t, params, params_of, in_out_globals, prog_info,  cguards, rel_alloc, modified, try_modified, disjoint,
  return, params_ctxt, addrs_fix_ctxt, alloc_ctxt}:args =
  {name = name, M = M, A = A, t0 = f t0, s = s, t = t, params = params, params_of = params_of, in_out_globals = in_out_globals,
  prog_info = prog_info, cguards = cguards,
  rel_alloc = rel_alloc, modified = modified, try_modified = try_modified, disjoint = disjoint,
  return = return,
  params_ctxt = params_ctxt, addrs_fix_ctxt = addrs_fix_ctxt, alloc_ctxt = alloc_ctxt}

fun map_s f {name, M, A, t0, s, t, params, params_of, in_out_globals, prog_info, cguards, rel_alloc, modified, try_modified, disjoint, 
  return, params_ctxt, addrs_fix_ctxt, alloc_ctxt}:args =
  {name = name, M = M, A = A, t0 = t0, s = f s, t = t, params = params, params_of = params_of, in_out_globals = in_out_globals,
  prog_info = prog_info, cguards = cguards,
  rel_alloc = rel_alloc, modified = modified, try_modified = try_modified, disjoint = disjoint, 
  return = return, params_ctxt = params_ctxt, addrs_fix_ctxt = addrs_fix_ctxt, alloc_ctxt = alloc_ctxt}

fun map_t f {name, M, A, t0, s, t, params, params_of, in_out_globals, prog_info, cguards, rel_alloc, modified, try_modified, disjoint, 
  return, params_ctxt, addrs_fix_ctxt, alloc_ctxt}:args =
  {name = name, M = M, A = A, t0 = t0, s = s, t = f t, params = params, params_of = params_of, in_out_globals = in_out_globals,
  prog_info = prog_info, cguards = cguards,
  rel_alloc = rel_alloc, modified = modified, try_modified = try_modified, disjoint = disjoint, 
  return = return, params_ctxt = params_ctxt, addrs_fix_ctxt = addrs_fix_ctxt, alloc_ctxt = alloc_ctxt}

fun map_rel_alloc f {name, M, A, t0, s, t, params, params_of, in_out_globals, prog_info, cguards, rel_alloc, modified, try_modified, disjoint,
  return, params_ctxt, addrs_fix_ctxt, alloc_ctxt}:args =
  {name = name, M = M, A = A, t0 = t0, s = s, t = t, params = params, params_of = params_of, in_out_globals = in_out_globals,
  prog_info = prog_info, cguards = cguards,
  rel_alloc = f rel_alloc, modified = modified, try_modified = try_modified, disjoint = disjoint,
  return = return, params_ctxt = params_ctxt, addrs_fix_ctxt = addrs_fix_ctxt, alloc_ctxt = alloc_ctxt}

fun map_addrs_fix_ctxt f {name, M, A, t0, s, t, params, params_of, in_out_globals, prog_info, cguards, rel_alloc, modified, try_modified, disjoint,
  return, params_ctxt, addrs_fix_ctxt, alloc_ctxt}:args =
  {name = name, M = M, A = A, t0 = t0, s = s, t = t, params = params, params_of = params_of, in_out_globals = in_out_globals,
  prog_info = prog_info, cguards = cguards,
  rel_alloc = rel_alloc, modified = modified, try_modified = try_modified, disjoint = disjoint,
  return = return, params_ctxt = params_ctxt, addrs_fix_ctxt = f addrs_fix_ctxt, alloc_ctxt = alloc_ctxt}

fun map_params_ctxt f {name, M, A, t0, s, t, params, params_of, in_out_globals, prog_info, cguards, rel_alloc, modified, try_modified, disjoint,
  return, params_ctxt, addrs_fix_ctxt, alloc_ctxt}:args =
  {name = name, M = M, A = A, t0 = t0, s = s, t = t, params = params, params_of = params_of, in_out_globals = in_out_globals,
  prog_info = prog_info, cguards = cguards,
  rel_alloc = rel_alloc, modified = modified, try_modified = try_modified, disjoint = disjoint,
  return = return, params_ctxt = f params_ctxt, addrs_fix_ctxt = addrs_fix_ctxt, alloc_ctxt = alloc_ctxt}

fun map_alloc_ctxt f {name, M, A, t0, s, t, params, params_of, in_out_globals, prog_info, cguards, rel_alloc, modified, try_modified, disjoint,
  return, params_ctxt, addrs_fix_ctxt, alloc_ctxt}:args =
  {name = name, M = M, A = A, t0 = t0, s = s, t = t, params = params, params_of = params_of, in_out_globals = in_out_globals,
  prog_info = prog_info, cguards = cguards,
  rel_alloc = rel_alloc, modified = modified, try_modified = try_modified, disjoint = disjoint,
  return = return, params_ctxt = params_ctxt, addrs_fix_ctxt = addrs_fix_ctxt, alloc_ctxt = f alloc_ctxt}

fun map_disjoint f {name, M, A, t0, s, t, params, params_of, in_out_globals, prog_info, cguards, rel_alloc, modified, try_modified, disjoint,
  return, params_ctxt, addrs_fix_ctxt, alloc_ctxt}:args =
  {name = name, M = M, A = A, t0 = t0, s = s, t = t, params = params, params_of = params_of, in_out_globals = in_out_globals,
  prog_info = prog_info, cguards = cguards,
  rel_alloc = rel_alloc, modified = modified, try_modified = try_modified, disjoint = f disjoint,
  return = return, params_ctxt = params_ctxt, addrs_fix_ctxt = addrs_fix_ctxt, alloc_ctxt = alloc_ctxt}

datatype check_result = Known_Good | Known_Bad | Neutral

fun merge_check_result _ Known_Bad = Known_Bad
  | merge_check_result Known_Bad _ = Known_Bad
  | merge_check_result Neutral x = x 
  | merge_check_result x Neutral = x
  | merge_check_result Known_Good Known_Good = Known_Good

fun passed Known_Bad = false
  | passed _ = true

fun promote Neutral = Known_Good
  | promote x = x
 
fun root_ptr @{term_pat \<open>Ptr (field_lvalue ?p _)\<close>} = root_ptr p
  | root_ptr @{term_pat \<open>ptr_coerce ?p +\<^sub>p _\<close>} = root_ptr p
  | root_ptr p = p

fun croot_ptr ct = ct |> Match_Cterm.switch [
  @{cterm_match \<open>Ptr (field_lvalue ?p _)\<close>} #> (fn {p,...} => croot_ptr p),
  @{cterm_match \<open>ptr_coerce ?p +\<^sub>p ?n\<close>} #> (fn {p, ...} => croot_ptr p),
  fn p => p]

fun all_check check xs =
  let
    fun all res [] = res
      | all res [x] = merge_check_result res (check x)
      | all res (x::xs) = case check x of Known_Bad => Known_Bad | r => all (merge_check_result res r) xs   
  in all Neutral xs end

exception Early_Exit
exception Early_Bad

(* Known_Bad immediately stops recursion and is propagated to toplevel
   Neutral continues recursion into subterms 
   Known_Good stops recursion on particular subterm but continues on outstanding subterms
*)
fun check_subterms_open check t =
  (case check t of
    Known_Good => Known_Good
  | Known_Bad => Known_Bad
  | Neutral => (case t of
                 Abs (x, T, t') => check_subterms_open check t'
               | (_ $ _) => let 
                        val (head, args) = strip_comb t
                      in all_check (check_subterms_open check ) (head :: args) end
               | _ => Neutral))
  handle Early_Bad => Known_Bad;


fun fold_opt f []     a = NONE
  | fold_opt f [x]    a = f x a
  | fold_opt f (x::xs) a = 
      (case f x a of
         SOME y => SOME (the_default y (fold_opt f xs y))
       | NONE   => fold_opt f xs a)

fun fold_subterms_open f t x =
  (case f t x of
     SOME y => SOME y
   | NONE => (case t of 
                Abs (_, T, t') => fold_subterms_open f t' x
              | (_ $ _) => 
                  let
                    val (head, args) = strip_comb t
                  in x |> fold_opt (fold_subterms_open f) (head::args) end
              | _ => NONE))

fun dest_sumT \<^Type>\<open>sum L R\<close> = SOME (L, R)
  | dest_sumT _ = NONE

fun exn_level x = 
  let
    fun dest x = x |> Match_Cterm.switch [
      @{cterm_match \<open>Inl ?x\<close>} #> (fn {x, ...} => 
           dest x + 1),
      @{cterm_match \<open>Inr ?x\<close>} #> (fn _ => 1),
      (fn _ => 0)
      ]
  in
    dest x
  end

fun mk_exn_stack_rel ctxt L_typ R_typ 1 true Q =
      \<^infer_instantiate>\<open>Q = Q and 'a = R_typ in cterm \<open>rel_xval_stack Q (\<lambda>_::heap_mem. (=)::'a \<Rightarrow> 'a \<Rightarrow> bool)\<close>\<close> ctxt
  | mk_exn_stack_rel ctxt L_typ R_typ 1 false Q = 
      \<^infer_instantiate>\<open>Q = Q and 'a = L_typ in cterm \<open>rel_xval_stack (\<lambda>_::heap_mem. (=)::'a \<Rightarrow> 'a \<Rightarrow> bool) Q\<close>\<close> ctxt
  | mk_exn_stack_rel ctxt L_typ R_typ n exn Q = 
      let                                                                                                               
        val l_rel = mk_exn_stack_rel ctxt L_typ R_typ (n - 1) exn Q
      in
        \<^infer_instantiate>\<open>Q = l_rel and 'a = R_typ in cterm \<open>rel_xval_stack Q (\<lambda>_::heap_mem. (=)::'a \<Rightarrow> 'a \<Rightarrow> bool)\<close>\<close> ctxt
      end
  | mk_exn_stack_rel ctxt _ _ n _ _ = error ("mk_exn_stack_rel: level " ^ string_of_int n ^ " unexpected")

fun Trueprop P = @{make_judgment} P

val dest_Trueprop = @{cterm_match \<open>Trueprop ?P\<close>} #> (fn {P,...} => P)

fun dest_rel_xval_stack ctxt = 
  @{cterm_match \<open>rel_xval_stack ?L ?R ?h ?x ?y\<close>} #> 
    (fn {L, R,...} => \<^infer_instantiate>\<open>L = L  and R = R in cterm \<open>rel_xval_stack L R\<close>\<close> ctxt)

fun dest_rel_sum_stack ctxt = 
  @{cterm_match \<open>rel_sum_stack ?L ?R ?h ?x ?y\<close>} #> 
    (fn {L, R,...} => \<^infer_instantiate>\<open>L = L  and R = R in cterm \<open>rel_sum_stack L R\<close>\<close> ctxt)

fun dest_rel_exit ctxt = 
  @{cterm_match \<open>rel_exit ?Q ?h ?x ?y\<close>} #> 
    (fn {Q, ...} => \<^infer_instantiate>\<open>Q in cterm \<open>rel_exit Q\<close>\<close> ctxt)

val dest_rel_exit_rel = 
  @{cterm_match \<open>rel_exit ?Q\<close>} #> 
    (fn {Q, ...} => Q)

fun make_exn_rel ctxt exit_unreachable is_left mk_seed_rel x = x |> Match_Cterm.switch [
     @{cterm_match \<open>Inl ?l\<close>} #> (fn {l, ...} => 
         let 
           val (L, thm, outs, unit_seed, seed_rel) = make_exn_rel ctxt exit_unreachable true mk_seed_rel l
           val rule = @{thm rel_sum_stack_InlI} 
             |>  Drule.infer_instantiate ctxt [(("L", 0), L)]  
             |> Thm.incr_indexes ((Thm.maxidx_of thm) + 1)
           val thm = rule OF [thm]
           val Q = thm |> Thm.cconcl_of |> dest_Trueprop |> dest_rel_sum_stack ctxt
         in 
           (Q, thm, outs, unit_seed, seed_rel)
         end),
     @{cterm_match \<open>Inr ?r\<close>} #> (fn {r, ...} =>  let 
           val (R, thm, outs, unit_seed, seed_rel) = make_exn_rel ctxt exit_unreachable false mk_seed_rel r
           val rule = @{thm rel_sum_stack_InrI} 
             |>  Drule.infer_instantiate ctxt [(("R", 0), R)] 
             |> Thm.incr_indexes ((Thm.maxidx_of thm) + 1)
           val thm = rule OF [thm]
           val Q = thm |> Thm.cconcl_of |> dest_Trueprop |> dest_rel_sum_stack ctxt
         in 
           (Q, thm, outs, unit_seed, seed_rel)
         end),
     @{cterm_match \<open>Nonlocal ?x\<close>} #> (fn {x, ...} =>  let 
           val (Q, thm, outs, unit_seed, seed_rel) = make_exn_rel ctxt exit_unreachable is_left mk_seed_rel x
           val thm = Drule.infer_instantiate ctxt [(("Q", 0), Q)] @{thm rel_exit_intro} OF [thm]
           val Q = thm |> Thm.cconcl_of |> dest_Trueprop |> dest_rel_exit ctxt
         in 
           (Q, thm, outs, unit_seed, seed_rel)
         end),
     fn x => 
       let
         val (L, thm, outs, unit_seed) = mk_seed_rel exit_unreachable is_left x
       in (L, thm, outs, unit_seed, L) end]

fun dest_stack_rel_typ T = 
  let
    val [@{typ heap_mem}, T, S] = binder_types T
  in (T, S) end                   


val is_bottom_stack_rel = Match_Cterm.switch [
      @{cterm_match \<open>\<lambda>_ _ _. False\<close>} #> (fn _ => true),
      @{cterm_match \<open>rel_exit (\<lambda>_ _ _. False)\<close>} #> (fn _ => true),
      (fn _ => false)]
 
fun is_bottom_exit ct = ct |> Match_Cterm.switch [
      @{cterm_match \<open>\<lambda>_ _ _. False\<close>} #> (fn _ => true),
      @{cterm_match \<open>rel_exit (\<lambda>_ _ _. False)\<close>} #> (fn _ => true),
      @{cterm_match \<open>rel_xval_stack ?L _\<close>} #> (fn {L, ...} => is_bottom_exit L),
      @{cterm_match \<open>rel_sum_stack ?L _\<close>} #> (fn {L, ...} => is_bottom_exit L),
      (fn _ => false)]

fun stack_rel ctxt orig_resT [] = ( \<^instantiate>\<open>'a=\<open>orig_resT\<close> in term \<open>\<lambda>_::heap_mem. (=)::'a \<Rightarrow> 'a => bool\<close>\<close>, false)
  | stack_rel ctxt \<^Type>\<open>unit\<close> [p] =( \<^infer_instantiate>\<open>p=p in term \<open>rel_singleton_stack p\<close>\<close> ctxt, true)
  | stack_rel ctxt orig_resT (p::ps) = 
      let
        val (rel, unit_seed) = stack_rel ctxt orig_resT ps
      in
       ( \<^infer_instantiate>\<open>R = rel and p = p in term \<open>rel_push p R\<close>\<close> ctxt, unit_seed)
      end

fun dest_stack_rel' @{term_pat "rel_singleton_stack ?p"} = [p]
  | dest_stack_rel' @{term_pat "rel_push ?p ?R"} = p::dest_stack_rel' R
  | dest_stack_rel' _ = []

fun gen_dest_stack_rel ct = ct |> Match_Cterm.switch [
      @{cterm_match "rel_singleton_stack ?p"} #> (fn {p,...} => ([p], (@{ctyp unit}, true))),
      @{cterm_match "rel_push ?p ?R"} #> (fn {p, R, ...} => apfst (cons p) (gen_dest_stack_rel R)),
      (fn _ => ([], Thm.strip_type (Thm.ctyp_of_cterm ct) |> fst |> (fn [_, xT, _] => (xT, false))))]

val dest_stack_rel = gen_dest_stack_rel #> fst

fun is_singleton ct = ct |> Match_Cterm.switch [
      @{cterm_match "rel_singleton_stack ?p"} #> (fn _ => true),
      (fn _ => false)]

val exn_eq_rel = @{term \<open>\<lambda>_::heap_mem. (=)::exit_status c_exntype \<Rightarrow> exit_status c_exntype => bool\<close>}

fun rel_xval_stack ctxt L R = \<^infer_instantiate>\<open>L=L and R=R in term \<open>rel_xval_stack L R\<close>\<close> ctxt

fun rel_alloc phi ctxt S M A t0 = 
    \<^morph_infer_instantiate>\<open>S = S and M = M and A = A and t0=t0
    in term \<open>rel_alloc S M A t0\<close>\<close> phi ctxt 

fun h_val phi ctxt s p =                 
 \<^morph_infer_instantiate>\<open>p = p and s = s in cterm \<open>h_val (hmem s) p\<close> for p and s\<close> phi ctxt



fun dest_hval' phi = Match_Cterm.switch [
  uncurry (@{morph_match \<open>h_val (hmem ?s) ?p\<close>} phi) #> (fn {p, s, ...} => SOME (p, s)),
  fn _ => NONE] |> curry


fun dest_hval phi = Match_Cterm.switch [
  @{cterm_morph_match \<open>h_val (hmem ?s) ?p\<close>} phi #> (fn {p, ...} => SOME p),
  fn _ => NONE]

fun cguard_bool p =
  let
    val T = Thm.dest_ctyp0 (Thm.ctyp_of_cterm p)
  in
   \<^instantiate>\<open>'a=T and p = p in cterm\<open>c_guard p\<close> for p::"'a::c_type ptr"\<close> 
  end

fun cguard p =
  let
    val T = Thm.dest_ctyp0 (Thm.ctyp_of_cterm p)
  in
   \<^instantiate>\<open>'a=T and p = p in cprop\<open>c_guard p\<close> for p::"'a::c_type ptr"\<close> 
  end

fun cguard_holds ctxt p =
  let
    val rhs = cguard p |> Simplifier.rewrite ctxt |> Thm.rhs_of
  in
    cterm_eq (rhs, \<^cprop>\<open>True\<close>)
  end
   
fun heap_update phi ctxt p v =
 \<^morph_infer_instantiate>\<open>p = p and v = v in term \<open>hmem_upd (heap_update p v)\<close> for p and v\<close> phi ctxt

datatype access = Field of string | Index of term
fun dest_access @{term_pat "replicate (?n::nat) CHR ''1''"} = Index n
  | dest_access t = Field (HOLogic.dest_string t)

fun field_from_access (Field str) = HOLogic.mk_string str
  | field_from_access (Index n) = \<^instantiate>\<open>n = n in term \<open>replicate n CHR ''1''\<close>\<close>

val path_from_accesses = map field_from_access #> HOLogic.mk_list @{typ string}

fun array_index_bound sz n = 
 \<^instantiate>\<open>n =n  and sz = \<open>HOLogic.mk_number @{typ nat} sz\<close> in term \<open>(n::nat) < sz\<close>\<close>

fun comps ctxt [] = error "comps: empty"
  | comps ctxt [f] = f
  | comps ctxt (f::fs) = 
      let
        val comps_fs = comps ctxt fs
      in 
       \<^infer_instantiate>\<open>f=f and g = comps_fs in term \<open>f o g\<close>\<close> ctxt
      end
 
fun conjs [] = @{term True}
  | conjs [P] = P
  | conjs (P::Ps) = \<^instantiate>\<open>P = P and Q = \<open>conjs Ps\<close> in term \<open>P \<and> Q\<close>\<close>

fun conjs_cterm [] = @{cterm True}
  | conjs_cterm [P] = P
  | conjs_cterm (P::Ps) = \<^instantiate>\<open>P = P and Q = \<open>conjs_cterm Ps\<close> in cterm \<open>P \<and> Q\<close>\<close>

fun dest_conjs ct = ct |> Match_Cterm.switch [
  @{cterm_match \<open>?P \<and> ?Q\<close>} #> (fn {P, Q, ...} => dest_conjs P @ dest_conjs Q),
  (fn _ => [ct])]

fun dest_accesses @{term_pat \<open>Ptr (field_lvalue ?p ?path)\<close>} = 
     let
       val (root, accs1) = dest_accesses p
       val accs2 = map dest_access (HOLogic.dest_list path)
     in (root, accs1 @ accs2) end
  | dest_accesses @{term_pat \<open>ptr_coerce ?p +\<^sub>p ?n\<close>} =
     let
       val (root, accs1) = dest_accesses p
       
     in
       (root, accs1 @ [Index (@{term nat} $ n)])
     end 
  | dest_accesses p = (p, [])

fun trivial_guard P = cterm_eq (P, @{cterm True})

fun simplified_cterm ctxt ct = ct |> Simplifier.rewrite ctxt |> Thm.rhs_of



fun ptr_to_lense ctxt ct =
  let
    val t = Thm.term_of ct
    val record_info = RecursiveRecordPackage.get_info (Proof_Context.theory_of ctxt)
    val (root, accesses) = dest_accesses t
    val \<^Type>\<open>ptr T\<close> = fastype_of root
    fun dest_access T (Field field) = 
         let
           val Type(record_name, _) = T
         in
           case Symtab.lookup record_info record_name of
             SOME {fields, updates, ...} => 
              let
                val idx = find_index (fn (xn, T) => Long_Name.base_name xn = field) fields
                val _ = idx >= 0 orelse error ("field_lvalue_to_lense: unknown field " ^ quote field ^ " for " ^ quote record_name)
                val (sel_name, fT) = nth fields idx
                val (upd_name, updT) = nth updates idx

              in 
                {typ=fT, sel = Const(sel_name, T --> fT), upd = Const(upd_name, updT), grd = []}
              end
            | NONE => error ("field_lvalue_to_lense: unknown struct type: " ^ quote record_name)
         end
      | dest_access T (Index n) = 
          let
             val (eT, sz) = TermsTypes.dest_array_index T
             val (_ , szT) = TermsTypes.dest_array_type T
             val sel = \<^instantiate>\<open>'n = szT and 'a = eT and n = n in term \<open>\<lambda>(arr::('a,'n::finite) array). index arr n\<close>\<close>
             val upd = \<^instantiate>\<open>'a = eT and 'b = szT and n = n in term \<open>fupdate n\<close>\<close>
          in {typ = eT, sel = sel, upd = upd, grd = [array_index_bound sz n]} end
 
    val root = Thm.cterm_of ctxt root
    fun triv_lense T root = {
      sel = \<^instantiate>\<open>'a = T in cterm \<open>\<lambda>(x::'a). x\<close>\<close>,
      upd = \<^instantiate>\<open>'a = T in cterm \<open>\<lambda>(f::'a \<Rightarrow> 'a) (x::'a). f x\<close>\<close>,
      grd = @{cterm True},
      root = root,
      ptr = root,
      eq = @{thm refl},
      trivial = true,
      trivial_eq = true
     }
   in
     if null accesses then 
       triv_lense (Thm.ctyp_of ctxt T) root
     else
       let
         val lenses = T |> 
           fold_map (fn acc => fn T => let val L = dest_access T acc in (L, #typ L) end) accesses 
           |> fst
         val sel = lenses |> map #sel |> rev |> comps ctxt |> Thm.cterm_of ctxt
         val fieldT = sel |> Thm.typ_of_cterm |> range_type |> Thm.ctyp_of ctxt
         val upd = lenses |> map #upd |> comps ctxt |> Thm.cterm_of ctxt
         val thy_ss = Proof_Context.theory_of ctxt |> Proof_Context.init_global |> Simplifier.simpset_of
         val grd = lenses |> map #grd |> flat |> conjs |> Thm.cterm_of ctxt 
           |> simplified_cterm (Simplifier.put_simpset thy_ss ctxt) (* avoid solving a guard that is in temp context *)
         val path = path_from_accesses accesses |> Thm.cterm_of ctxt
         val orig_trm = Thm.cterm_of ctxt t
         val eq = \<^infer_instantiate>\<open>'a=fieldT and orig = orig_trm and root = root and path = path in 
              cprop \<open>orig = PTR ('a) (field_lvalue root path)\<close>\<close> ctxt
         val prems = if trivial_guard grd then [] else [Utils.Trueprop_cterm grd]
         val simp_ctxt = ctxt 
             delsimps @{thms ptr_coerce.simps}
             addsimps 
               @{thms ptr_coerce_index_array_ptr_index_conv array_ptr_index_field_lvalue_conv}

         val eq_thm = Goal.prove_internal ctxt prems eq (fn prems =>
                Method.insert_tac ctxt prems 1 THEN
                asm_full_simp_tac (simp_ctxt) 1)
      in
        {sel = sel, upd = upd, grd = grd, root = root, ptr = ct, eq = eq_thm, trivial = false, trivial_eq = Utils.trivial_eq_thm eq_thm}
      end
   end

fun assume_grds grds ctxt =
 if null grds then ({grd = NONE, grds = []}, ctxt)
 else
   let
     val simp_ctxt = ctxt delsimps (Named_Theorems.get ctxt @{named_theorems size_simps})
       |> Simplifier.add_cong @{thm HOL.conj_cong}
     val grd = conjs_cterm grds |> simplified_cterm simp_ctxt
     val ([grd_thm], ctxt) = Assumption.add_assumes [Utils.Trueprop_cterm grd] ctxt
     val grd_thms = grds |> map (fn grd => Goal.prove_internal ctxt [] (Utils.Trueprop_cterm grd) (fn _ => 
            Method.insert_tac ctxt [grd_thm] 1 THEN asm_full_simp_tac ctxt 1))
     val eqs = grd_thms |> map (Simplifier.mksimps ctxt) |> flat |> sort_distinct Thm.thm_ord
     fun add_field_lookup_prems thm = 
       Thm.proof_attributes (map (Attrib.attribute ctxt) @{attributes [field_lookup_prems]}) thm 
       #> snd
     val ctxt = ctxt addsimps eqs |> fold add_field_lookup_prems eqs
   in
     ({grd = SOME grd_thm, grds = grd_thms}, ctxt)
 end


fun cterm_lambda x = Thm.lambda_name (name_of_cterm x, x)

fun ctyp_from_ptr ctxt p = 
  let
    val \<^Type>\<open>ptr T\<close> = Thm.typ_of_cterm p
  in Thm.ctyp_of ctxt T end


fun root_cguard ct = ct |> Match_Cterm.switch [
 @{cterm_match \<open>c_guard ?p\<close>} #> (fn {p, ...} => 
   let val root = croot_ptr p 
   in (cguard_bool root, cterm_eq (root, p)) end),
 (fn _ => (ct, true))
 ]

fun tuple_prj_from_pointers ctxt orig_resT ps n = 
  let
    val Ts = map (Thm.typ_of o ctyp_from_ptr ctxt) ps
    val Ts = if orig_resT = @{typ "unit"} then Ts else Ts @ [orig_resT]
    val T =  HOLogic.mk_tupleT Ts
    val sel = Abs ("w", T, Tuple_Tools.mk_sel' Ts (Bound 0) n) |> Thm.cterm_of ctxt
  in
    sel
  end

fun upd_select_same_root project phi ctxt s lenses =
  let
    val _ = not (null lenses) orelse error ("upd_select_same_root: empty")
    val root = (#root o fst) (hd lenses)
    val do_project = project lenses
    val resT = hd lenses |> snd |> Thm.typ_of_cterm |> (if do_project then domain_type else range_type)
    val pT = Thm.typ_of_cterm root
    val \<^Type>\<open>ptr T\<close> = pT
    val thy_ctxt = ctxt |> Proof_Context.theory_of |> Proof_Context.init_global
    val ([s'], ctxt') = Utils.fix_variant_cfrees [("s", Thm.typ_of_cterm s)] thy_ctxt

    
    val value = 
      let
        val ([w], ctxt') = Utils.fix_variant_cfrees [("w", resT)] ctxt
        val root_val = h_val phi ctxt' s root    
        val value = root_val |> fold (fn ({upd, ...}, prj) => fn x => 
           if do_project then
             \<^infer_instantiate>\<open>prj=prj and upd = upd and w = w and x = x in cterm \<open>upd (\<lambda>_. prj w) x\<close>\<close> ctxt'
           else
             \<^infer_instantiate>\<open>upd = upd and w = w and x = x in cterm \<open>upd (\<lambda>_. w) x\<close>\<close> ctxt') lenses
      in
         cterm_lambda w value
      end

    val grds = lenses |> map (#grd o fst) |> filter_out (curry cterm_eq \<^cterm>\<open>True\<close>) |> map Utils.Trueprop_cterm
    val root_val = h_val phi ctxt' s' root    
    fun sel_eq_thm {sel, eq, ...} = 
      let
        val fld_ptr = eq |> Thm.cconcl_of |> Utils.crhs_of_eq
        val fld_hval = h_val phi ctxt' s' fld_ptr
        val sel_eq = \<^infer_instantiate>\<open>fld_hval = fld_hval and value = root_val and sel = sel in 
          cprop \<open>fld_hval = sel value\<close>\<close> ctxt'
        val thm = Goal.prove_internal ctxt' grds sel_eq (fn prems => 
            Method.insert_tac ctxt' prems 1 THEN asm_full_simp_tac (ctxt' addsimps @{thms h_val_field_from_bytes'}) 1) 
        val thm = thm
           |> singleton (Proof_Context.export ctxt' thy_ctxt)
      in
        thm
      end
    val sel_eq_thms = map (sel_eq_thm o fst) lenses
  in
    (value, sel_eq_thms)
  end

fun map_tuple ctxt [] = error ("map_tuple: empty")
  | map_tuple ctxt [f] = f
  | map_tuple ctxt (f::fs) = \<^infer_instantiate>\<open>f=f and g = \<open>map_tuple ctxt fs\<close> in cterm \<open>map_prod f g\<close>\<close> ctxt

fun map_tuple' ctxt resT [] = \<^instantiate>\<open>'a=resT in cterm \<open>\<lambda>x. x\<close>\<close>
  | map_tuple' ctxt _ fs = map_tuple ctxt fs 

fun reverse_abs n =
  let
    fun rev 0 xs ct = ct |> fold_rev cterm_lambda xs
      | rev n xs ct = 
          let 
            val (x, ct') = Thm.dest_abs_global ct
          in rev (n - 1) (x::xs) ct' end
  in rev n [] end

fun rotate_abs n k =
  let
    fun rev 0 xs ct = ct |> fold cterm_lambda (drop (n - k) xs @ take (n - k) xs)
      | rev n xs ct = 
          let 
            val (x, ct') = Thm.dest_abs_global ct
          in rev (n - 1) (x::xs) ct' end
  in rev n [] end

fun dest_lambdas_but_first n =
  let
    fun rev 0 xs ct = ct |> fold_rev cterm_lambda (drop (n - 1) xs)
      | rev n xs ct = 
          let 
            val (x, ct') = Thm.dest_abs_global ct
          in rev (n - 1) (x::xs) ct' end
  in
    rev n []
  end
                                

fun in_param_val phi ctxt s (p, (Eliminate (Parameter FunctionInfo.In), _)) = [(p, h_val phi ctxt s p)]
  | in_param_val phi ctxt s (p, (Eliminate (Parameter FunctionInfo.In_Out), _)) = [(p, h_val phi ctxt s p)]
  | in_param_val phi ctxt s (p, (Eliminate (Parameter FunctionInfo.Out), _)) = []
  | in_param_val phi ctxt s (p, (Eliminate (Parameter FunctionInfo.Data), _)) = []
  | in_param_val phi ctxt s (p, (Eliminate Stack, _)) = [(p, h_val phi ctxt s p)]
  | in_param_val phi ctxt s (x, _) = [(x, x)]

fun ptr_param (p, (Other, _)) = []
  | ptr_param (p, _) = [p]

fun ptr_param_val phi ctxt s (p, (Other, _)) = []
  | ptr_param_val phi ctxt s (p, _) = [(p, h_val phi ctxt s p)]


fun derefT (\<^Type>\<open>ptr T\<close>) = T
  | derefT T = error ("derefT: not a pointer type " ^ @{make_string} T)

fun ptr_to_val (Free (p, pT)) = Free (p, derefT pT)
  | ptr_to_val t = error ("ptr_to_val expecting free pointer variable: " ^ @{make_string} t)

fun cptr_to_val ctxt = Thm.term_of #> ptr_to_val #> Thm.cterm_of ctxt

fun in_arg ctxt (p, (Eliminate (Parameter FunctionInfo.In), _)) = [cptr_to_val ctxt p]
  | in_arg ctxt (p, (Eliminate (Parameter FunctionInfo.In_Out), _)) = [cptr_to_val ctxt p]
  | in_arg ctxt (p, (Eliminate (Parameter FunctionInfo.Out), _)) = []
  | in_arg ctxt (p, (Eliminate (Parameter FunctionInfo.Data), _)) = []
  | in_arg ctxt (p, (Eliminate Stack, _)) = []
  | in_arg ctxt (x, _) = [x]


val val_name = suffix "'val"
val dest_val_name = unsuffix "'val"
fun is_ptrT ( \<^Type>\<open>ptr _\<close> ) = true
  | is_ptrT _ = false

fun ptr_val phi ctxt s p = (val_name (name_of_cterm p), h_val phi ctxt s p)
fun check_ptr x = case Thm.typ_of_cterm x of \<^Type>\<open>ptr _\<close> => SOME x | _ => NONE
val is_ptr = is_some o check_ptr

fun is_ptr_and_not_Other (_, (Other, _)) = false
  | is_ptr_and_not_Other (ptr, (_, _)) = is_ptr ptr

fun pair_cterm ctxt x y = \<^infer_instantiate>\<open>x = x and y = y in cterm "(x, y)"\<close> ctxt


fun ptr_val_tuple phi ctxt s [] v = (v, false)
  | ptr_val_tuple phi ctxt s [p] v = 
      if Thm.typ_of_cterm v = @{typ unit} then
        (h_val phi ctxt s p, true)
      else
        (pair_cterm ctxt (h_val phi ctxt s p) v, false)
  | ptr_val_tuple phi ctxt s (p::ps) v =
      let val (x, unit_seed) = ptr_val_tuple phi ctxt s ps v
      in (pair_cterm ctxt (h_val phi ctxt s p) x, unit_seed) end



fun guard_param (x, (Keep stack, _)) = if stack then [cguard x] else []
  | guard_param (x, (Other, _)) = []
  | guard_param (p, (Eliminate _, _)) = [cguard p]

fun return_all _ = true
fun return_none _ = false
fun return_outs (_, (Parameter FunctionInfo.Out)) = true
  | return_outs (_, (Parameter FunctionInfo.In_Out)) = true
  | return_outs _ = false
fun return_modified M (p, _) = member cterm_eq M p

fun returns M Final = return_outs
  | returns M Intermediate = return_modified M
  | returns M Nothing = return_none
 
(* returns_throw overapproximates Intermediate results to also include unmodified stack variables 
   (compared to returns). We do not know yet if there is another normal control flow path
   were the variables are modified *)
fun returns_throw M Final = return_outs
  | returns_throw M Intermediate = return_all 
  | returns_throw M Nothing = return_none

fun out_param return (p, (Eliminate kind, _)) = if return (p, kind) then [p] else []
  | out_param return (p, _) = []

fun modified_param return (p, (Eliminate kind, _)) = if return (p, kind) then [p] else []
  | modified_param return (p, (Keep false, _)) = [p]
  | modified_param return (p, _) = []


val alloc_ptrs = map_filter (fn (p, (Eliminate _, _)) => SOME p | _ => NONE)
val modified_ptrs = 
  let 
    fun modified (p, (Eliminate (Parameter FunctionInfo.Out), _)) = SOME p
      | modified (p, (Eliminate (Parameter FunctionInfo.In_Out), _)) = SOME p
      | modified _ = NONE
  in
    map_filter modified
  end 
val keep_ptrs = map_filter (fn (p, (Keep _, _)) => check_ptr p | _ => NONE)
val keep_stack_ptrs = map_filter (fn (p, (Keep true, _)) => check_ptr p | _ => NONE)



fun tuple [] = @{cterm "()"}
  | tuple [x] = x
  | tuple (x::xs) = 
     let
       val p = tuple xs
     in \<^instantiate>\<open>'a= \<open>Thm.ctyp_of_cterm x\<close> and 'b=\<open>Thm.ctyp_of_cterm p\<close> and x = x and p = p in 
       cterm \<open>(x, p)\<close>\<close>
     end

val curry_case_prod = mk_meta_eq @{thm curry_case_prod}
 
fun tupled_applies ctxt [] f = f
  | tupled_applies ctxt [x] f = Drule.beta_conv f x
  | tupled_applies ctxt xs f = 
      let 
        val n = length xs
        val eq = Tuple_Tools.get_tuple_case_eq_thm ctxt n
        val rhs = Conv.rewr_conv eq (Thm.apply f (tuple xs)) |> Thm.rhs_of
      in 
        rhs
      end

fun comps_rev ctxt [] = error "comps: empty"
  | comps_rev ctxt [f] = f
  | comps_rev ctxt fs = 
      let
        val (fs', g) = split_last fs
        val comps_fs' = comps_rev ctxt fs'
      in 
       \<^infer_instantiate>\<open>f=comps_fs' and g = g in cterm \<open>f o g\<close>\<close> ctxt
      end

fun decompose_funs ctxt f =
  let
    val domT = f |> Thm.typ_of_cterm |> domain_type
    val ([x], ctxt') = Utils.fix_variant_cfrees [("x", domT)] ctxt
    val app = Utils.beta_applies [x] f
    fun decomp g = g |> Match_Cterm.switch [
          @{cterm_match (fo) \<open>?f ?y\<close>} #> (fn {f, y, ...} =>
             if cterm_eq (y, x) then 
               [f]
             else
               f :: decomp y),
          fn g => [g]]
  in
    comps_rev ctxt (decomp app)
  end

fun untuple p = p |> Match_Cterm.switch [
      @{cterm_match (fo) \<open>Pair ?x ?y\<close>} #> (fn {x, y, ...} => x::untuple y),
      fn x => [x]]

fun decomp_upto_pair g = g |> Match_Cterm.switch [
          @{cterm_match (fo) \<open>Pair _ _\<close>} #> (fn _ => ([], g)),
          @{cterm_match (fo) \<open>?f ?y\<close>} #> (fn {f, y, ...} =>
               decomp_upto_pair y |> apfst (cons f)),
          fn x => ([],x) ]

fun decomp g = g |> Match_Cterm.switch [
          @{cterm_match (fo) \<open>Pair _ _\<close>} #> (fn _ => ([], g)),
          @{cterm_match (fo) \<open>?f ?y\<close>} #> (fn {f, y, ...} =>
               decomp y |> apfst (cons f)),
          fn x => ([],x) ]


fun emb'_from_rel_sum_stack ctxt ct =  ct |> Match_Cterm.switch [
  @{cterm_match \<open>Trueprop (rel_sum_stack ?L ?R ?h ?x ?y)\<close>} #> (fn {y,...} =>
      let
        val (_, p) = decomp_upto_pair y
        val emb' = Thm.lambda_name ("e'", p) y
      in
        emb'
      end),
  @{cterm_match \<open>Trueprop (rel_exit (\<lambda>_ _ _. False) ?h (Nonlocal ?x) ?y)\<close>} #> (fn {y, ...} =>
     let
       val emb' = \<^instantiate>\<open>'a=\<open>Thm.ctyp_of_cterm y\<close> in cterm \<open>\<lambda>x. x\<close>\<close>
     in
       emb'
     end),
  (fn _ => error ("emb'_from_rel_sum_stack: unexpected term: " ^ @{make_string} ct))
]

(* FIXME: unused ? *)
fun emb'_from_rel_xval_stack ctxt ct =  ct |> Match_Cterm.switch [
  @{cterm_match \<open>Trueprop (rel_xval_stack ?L ?R ?h ?x ?y)\<close>} #> (fn {y,...} =>
      let
        val (_, p) = decomp_upto_pair y
        val emb' = Thm.lambda_name ("e'", p) y
      in
        emb'
      end),
  @{cterm_match \<open>Trueprop (rel_exit (\<lambda>_ _ _. False) ?h (Nonlocal ?x) ?y)\<close>} #> (fn {y, ...} =>
     let
       val emb' = \<^instantiate>\<open>'a=\<open>Thm.ctyp_of_cterm y\<close> in cterm \<open>\<lambda>x. x\<close>\<close>
     in
       emb'
     end),
  (fn _ => error ("emb'_from_rel_sum_stack: unexpected term: " ^ @{make_string} ct))
]

fun gen_result_tuple phi ctxt s p_opt ps r_opt = case ps of 
      [] => (case r_opt of SOME r => r | _ => error ("gen_result_tuple: unexpected case (1)"))
    | (p:: ps') =>
        (case p_opt of 
          NONE => 
            let 
               val {x, ...} = @{cterm_match \<open>\<lambda>s. ?x s\<close>} (gen_result_tuple phi ctxt s p_opt ps' r_opt)
            in 
               if (range_type (Thm.typ_of_cterm x)) = @{typ unit} then
                 \<^morph_infer_instantiate>\<open>p = p and s = s
                   in cterm \<open>\<lambda>(s'::'s). (h_val (hmem s) p)\<close>\<close> phi ctxt
               else
                 \<^morph_infer_instantiate>\<open>p = p and x = x and s = s 
                   in cterm \<open>\<lambda>s'. (h_val (hmem s) p, x s')\<close>\<close> phi ctxt
            end
         | SOME p' =>  
             (case (cterm_eq (p', p), r_opt) of
              (true, SOME r) => 
                if null ps' then 
                  r
                else
                  let      
                    val {x, ...} = @{cterm_match \<open>\<lambda>s. ?x s\<close>} (gen_result_tuple phi ctxt s NONE ps' NONE)
                  in 
                    \<^morph_infer_instantiate>\<open>r = r and x = x 
                      in cterm \<open>\<lambda>s'. (r s', x s')\<close>\<close> phi ctxt
                  end
             | (false, _) =>                             
                 let 
                    val {x, ...} = @{cterm_match \<open>\<lambda>s. ?x s\<close>} (gen_result_tuple phi ctxt s p_opt ps' r_opt)
                 in 
                    \<^morph_infer_instantiate>\<open>p = p and x = x and s = s 
                      in cterm \<open>\<lambda>s'. (h_val (hmem s) p, x s')\<close>\<close> phi ctxt
                 end
             | _ =>
               error ("gen_result_tuple: unexpected case (2)"))) 

val norm_tuple = Match_Cterm.switch [
  @{cterm_match \<open>\<lambda>s. (?f s, ())\<close>} #> (fn {f,...} => f),
  fn t => t]

fun result_tuple_expr phi ctxt s ps r = gen_result_tuple phi ctxt s NONE ps (SOME r) |> norm_tuple
fun result_tuple_modifies p phi ctxt s ps r = gen_result_tuple phi ctxt s (SOME p) ps (SOME r)

fun result_tuple NONE = result_tuple_expr
  | result_tuple (SOME p) = result_tuple_modifies p




fun in_set ctxt A p = \<^infer_instantiate>\<open>p = p and A = A in cprop \<open>ptr_val p \<in> A\<close>\<close> ctxt



fun check_vars thm =
  let
    val vars = thm |> Thm.prop_of |> (fn t => Term.add_vars t []) |> distinct (op =)
  in
    ((map (fst o fst) vars |> Ord_List.make fast_string_ord, thm))
  end

fun recheck_vars (rule as (names:string list, thm)) =
  let
    val vars = thm |> Thm.prop_of |> (fn t => Term.add_vars t []) |> distinct (op =)
    fun check name =
      if AList.defined (fn (n, (x,i)) => x = n andalso i = 0) vars name then true
      else raise THM ("recheck_vars: no schematic variable for name " ^  quote name, 0, [thm])
    val _ = forall check names     
  in
    rule
  end

fun morph_check_vars phi thm =
  let
    val vars = thm |> Thm.prop_of |> (fn t => Term.add_vars t []) |> distinct (op =)
    val morph_thm = Morphism.thm phi thm
    val morph_vars = morph_thm |> Thm.prop_of |> (fn t => Term.add_vars t []) |> distinct (op =)

    fun check_var ((x, n), T) = 
      if n <> 0 then 
        error ("morph_check_vars: schematic variable " ^ quote x ^ " with unexpected index " ^ string_of_int n)
      else
        case AList.lookup (op =) morph_vars (x, n) of
          NONE => error ("morph_check_vaL2_rs: schematic variable " ^ quote x ^ " missing in morphed theorem: " ^ @{make_string} thm)
        | SOME (T') => if Type.could_unify (Morphism.typ phi T, T') then ()
                       else error ("morph_check_vars: schematic variable " ^ quote x ^ " has unecpected type: " ^ @{make_string} T')
    val _ = map check_var vars
  in
    ((map (fst o fst) vars |> Ord_List.make fast_string_ord, morph_thm))
  end

fun instantiate_thm' maxidx ctxt (insts:(string * cterm) list) thm =
  let
    (* avoid conflicts with schematic type variables *)
    val maxidx = maxidx |> fold (Integer.max o Thm.maxidx_of_cterm o snd) insts
    val i = maxidx + 1
  in
    Drule.infer_instantiate ctxt (map (apfst (rpair i)) insts) (Thm.incr_indexes i thm)
  end 

fun gen_instantiate_thm {unchecked} maxidx ctxt (insts:(string * cterm) list) (ordered_vars, thm) =
  let
    val inst_names = map fst insts
    val unknowns = filter_out (Ord_List.member fast_string_ord ordered_vars) inst_names
    val _ = unchecked orelse null unknowns orelse error ("instantiate_thm: unknown instantiations " ^ @{make_string} unknowns ^ 
      " for theorem: " ^ Thm.string_of_thm ctxt thm)
    val remaining_vars = filter_out (member (op =) inst_names) ordered_vars
  in
    (remaining_vars, instantiate_thm' maxidx ctxt insts thm)
  end 

fun instantiate_thm maxidx ctxt insts (ordered_vars, thm) =
  gen_instantiate_thm {unchecked=false} maxidx ctxt insts (ordered_vars, thm) |> snd

fun unchecked_instantiate_thm maxidx ctxt insts (ordered_vars, thm) =
  gen_instantiate_thm {unchecked=true} maxidx ctxt insts (ordered_vars, thm) |> snd

fun partial_instantiate_thm maxidx ctxt insts (ordered_vars, thm) =
  gen_instantiate_thm {unchecked=false} maxidx ctxt insts (ordered_vars, thm) |> apsnd (Goal.norm_result ctxt)
    
fun note thms attrs ctxt =
  let val ((_, thms), ctxt) = Proof_Context.note_thms "" ((Binding.empty, []), [(thms, attrs)]) ctxt
  in (thms, ctxt) end

fun assume_and_note cts attrs ctxt =
  let
    val (thms, ctxt) = Assumption.add_assumes cts ctxt
    val (thms, ctxt) = note thms attrs ctxt
  in
    (thms, ctxt)
  end

fun assume_and_note' cts attrs ctxt =
 assume_and_note cts (map (Attrib.attribute ctxt) attrs) ctxt

fun retrieve_exact rules_name ct ctxt =
  let
    val thms = Named_Rules.retrieve ctxt rules_name (Thm.term_of ct) 
  in find_first (fn thm => (is_equal o Thm.fast_term_ord) (ct, Thm.cprop_of thm)) thms end

fun ensure rules_name ct ctxt =
  case retrieve_exact rules_name ct ctxt of 
    SOME thm => (thm, ctxt)
  | NONE => assume_and_note [ct] [Named_Rules.add rules_name] ctxt |> apfst the_single

fun gen_transfer_assms except rules_name  ctxt2 ctxt1 =
  let
    val assms = Named_Rules.get ctxt2 rules_name
      |> filter_out except
      |> map Thm.cprop_of     
  in
    ctxt1 |> fold (snd oo ensure rules_name) assms
  end

fun transfer_assms except = gen_transfer_assms (member Thm.eq_thm except)

fun disjoint_sym thm = @{thm disjoint_symmetric} OF [thm]
val disjoint_syms = map disjoint_sym

fun add_disjoint_syms thms = thms @ disjoint_syms thms

fun disjoint_sym' thm = @{thm disjoint_symmetric'} OF [thm]
val disjoint_syms' = map disjoint_sym'

fun distinct_spans ptrs ctxt =
  let
    fun span p = \<^infer_instantiate>\<open>p = p in term \<open>ptr_span p\<close>\<close> ctxt
    val spans = HOLogic.mk_list \<^typ>\<open>addr set\<close> (map (span o Thm.term_of) ptrs)
    val disj = \<^infer_instantiate>\<open>spans = spans in term \<open>distinct_sets spans\<close>\<close> ctxt |> Thm.cterm_of ctxt
  in disj end

fun assume_distinct ptrs ctxt =
  let
    val disj = Utils.Trueprop_cterm (distinct_spans ptrs ctxt)
    val ([disj_thm], ctxt) = Assumption.add_assumes [disj] ctxt
    val simp_ctxt = ctxt
      delsimps (Named_Theorems.get ctxt @{named_theorems size_simps})
      addsimps @{thms disjoint_union_distrib}
    val disj_thms = disj_thm |> Simplifier.simplify simp_ctxt |> Simplifier.mksimps ctxt
    val disj_thms_sym = disjoint_syms' disj_thms
    val all_disj_thms = disj_thms @ disj_thms_sym
    val disj_fields = all_disj_thms |> map (fn thm => @{thm disj_ptr_span_field_disj_ptr_span''} OF [safe_mk_meta_eq thm])
    val attrs = map (Attrib.attribute ctxt) @{attributes [simp, disjoint_assms]}
    val ((_, thms), ctxt) = Proof_Context.note_thms "" ((Binding.empty, []), [(all_disj_thms @ disj_fields, attrs)]) ctxt
    val disj_cons = @{thm distinct_sets_consI} OF [disj_thm]
    val ctxt = ctxt addsimps [disj_cons]
  in
    ((disj_thm, thms), ctxt)
  end

(* FIXME: Do I really need to transfer alloc_assms, they seem to be handled different from modified_assms *)
fun transfer_all_assms except ctxt2 ctxt1 =
 ctxt1 |> fold (fn name => transfer_assms except name ctxt2) [
   @{named_rules alloc_assms}, 
   @{named_rules modifies_assms}, 
   @{named_rules disjoint_alloc}, 
   @{named_rules disjoint_stack_free}]

fun addr_set ctxt p =
  if is_ptr p then \<^infer_instantiate>\<open>p=p in cterm \<open>ptr_span p\<close>\<close> ctxt else p \<comment> \<open>\<G>\<close>


fun transfer_modifies_assms except_ptrs =
  let
    val ptrs = map Thm.term_of except_ptrs
  in
    gen_transfer_assms (fn thm => exists_subterm (member (op =) ptrs) (Thm.prop_of thm)) @{named_rules modifies_assms}
  end
fun ensure_alloc A p ctxt = ctxt |> ensure @{named_rules alloc_assms}
 (\<^infer_instantiate>\<open>p = p and A = A in cprop \<open>ptr_span p \<subseteq> A\<close>\<close> ctxt)

fun ensure_stack_ptr phi p ctxt = ctxt |> ensure @{named_rules stack_ptr}
 (\<^morph_infer_instantiate>\<open>p = p in cprop \<open>ptr_span p \<subseteq> \<S>\<close>\<close> phi ctxt)

fun ensure_disjoint_alloc A p ctxt = ctxt |> ensure @{named_rules disjoint_alloc}
 (\<^infer_instantiate>\<open>p = p and A = A in cprop \<open>ptr_span p \<inter> A = {}\<close>\<close> ctxt)

fun ensure_disjoint_alloc_globals phi A ctxt = ctxt |> ensure @{named_rules disjoint_alloc}
 (\<^morph_infer_instantiate>\<open>A = A in cprop \<open>\<G> \<inter> A = {}\<close>\<close> phi ctxt)

fun ensure_disjoint_stack_free phi s p ctxt = ctxt |> ensure @{named_rules disjoint_stack_free}
 (\<^morph_infer_instantiate>\<open>p = p and s = s in cprop \<open>ptr_span p \<inter> (stack_free (htd s)) = {}\<close>\<close> phi ctxt) 

fun ensure_disjoint_stack_free_globals phi s ctxt = ctxt |> ensure @{named_rules disjoint_stack_free}
 (\<^morph_infer_instantiate>\<open>s = s in cprop \<open>\<G> \<inter> (stack_free (htd s)) = {}\<close>\<close> phi ctxt)

fun ensure_disjoint_globals phi A s ctxt =
  let
    val (disj_alloc, ctxt1) = ensure_disjoint_alloc_globals phi A ctxt
    val (disj_stack, ctxt2) = ensure_disjoint_stack_free_globals phi s ctxt1
    val h_val_frame_disjoint_globals = (Morphism.thm phi @{thm h_val_frame_disjoint_globals}) 
         OF [disj_alloc, disj_stack]
    val ([hval_eq], ctxt') = note [h_val_frame_disjoint_globals] 
      [Named_Rules.add @{named_rules h_val_globals_frame_eq}] ctxt2  
  in 
    ([disj_alloc, disj_stack, hval_eq], ctxt')
  end
fun ensure_modifies M p ctxt = ctxt |> ensure @{named_rules modifies_assms}
 (\<^infer_instantiate>\<open>X = \<open>addr_set ctxt p\<close> and M = M in cprop \<open>X \<subseteq> M\<close>\<close> ctxt)

(* FIXME: make this kind of early application of phi for similar functions *)
fun ensure_modifies_globals phi =
  let
    val G = Morphism.cterm phi \<^cterm>\<open>\<G>\<close>
  in
    fn M => fn ctxt =>
      ctxt |> ensure @{named_rules modifies_assms}
       (\<^instantiate>\<open>G = G and M = M in cprop \<open>G \<subseteq> M\<close> for G::"addr set" and M ::"addr set"\<close> )
  end


fun ptr_span_contained ctxt G p = \<^infer_instantiate>\<open>p = p and G = G in cterm \<open>ptr_span p \<subseteq> G\<close>\<close> ctxt

fun gen_ptrs_of_set phi = 
  let
    fun ptrs_of_set' () = Match_Cterm.switch [
      @{cterm_morph_match \<open>{}::addr set\<close>} phi #> (fn _ => ([], false)),
      @{cterm_morph_match \<open>ptr_span ?p\<close>} phi #> (fn {p,...} => ([p], false)),
      @{cterm_morph_match \<open>(?S::addr set) \<union> ?T\<close>} phi #> (fn {S, T,...} => 
          let 
            val (ss, global1) = ptrs_of_set' () S
            val (ts, global2) = ptrs_of_set' () T
          in (ss @ ts, global1 orelse global2) end),
      @{cterm_morph_match \<open>{&(?p\<rightarrow>?f)..+?n}\<close>} phi #> (fn {p, ...} => ([p], false)),
      @{cterm_morph_match \<open>\<G>\<close>} phi #> (fn {ct_, ...} => ([ct_], true)),
      (fn ct => error ("ptrs_of_set: unexpected term: " ^ @{make_string} ct))
     ]
 in ptrs_of_set' () end

fun ptrs_of_set phi = gen_ptrs_of_set phi #> fst

fun set_of_ptrs' ctxt A [] = A
  | set_of_ptrs' ctxt A (p::ps) = \<^infer_instantiate>\<open>X = \<open>addr_set ctxt p\<close> and P = \<open>set_of_ptrs' ctxt A ps\<close> in cterm \<open>X \<union> P\<close>\<close> ctxt

fun set_of_ptrs ctxt [] = @{cterm \<open>{}::addr set\<close>}
  | set_of_ptrs ctxt [p] = \<^infer_instantiate>\<open>X = \<open>addr_set ctxt p\<close> in cterm \<open>X\<close>\<close> ctxt
  | set_of_ptrs ctxt (p::ps) = \<^infer_instantiate>\<open>X = \<open>addr_set ctxt p\<close> and P = \<open>set_of_ptrs ctxt ps\<close> in cterm \<open>X \<union> P\<close>\<close> ctxt

fun set_of_ptrs'' ctxt A [] = A
  | set_of_ptrs'' ctxt A ps = \<^infer_instantiate>\<open>P = \<open>set_of_ptrs ctxt ps\<close> and A = A in cterm \<open>P \<union> A\<close>\<close> ctxt

fun export_cterm ctxt2 ctxt1 =
  Morphism.cterm (Proof_Context.export_morphism ctxt2 ctxt1)

fun curried ctxt i ct =
  if i <= 1 then ct
  else
    let
      val t = Thm.term_of ct
      val args = Tuple_Tools.strip_case_prod' t
      val _ =  @{assert} (i <= length args)
      val (curried_args, rest) = chop i args
      val (args', ctxt') = curried_args @ (if null rest then [] else [("", HOLogic.mk_tupleT (map snd rest))])
        |> (fn args => Utils.fix_variant_cfrees args ctxt)
        |> apfst (map (fn ct => (name_of_cterm ct, ct)))
      val applied = tupled_applies ctxt' (map snd args') ct
      val res = Utils.lambdas args' applied
    in
      res
    end

fun shuffle ctxt perm Ts = 
 let
   val x = Free ("x", HOLogic.mk_tupleT Ts)
   val perms = map perm (0 upto (length Ts - 1))
   val xs_perm = tuple (map (fn i => Thm.cterm_of ctxt (Tuple_Tools.mk_sel' Ts x (i + 1))) perms)
   val res = Thm.lambda_name ("x", Thm.cterm_of ctxt x) xs_perm
 in
   res
 end

fun sanitize_names v ts =
  let
    fun sanitize n [] = []
      | sanitize n ((x, T)::xs) = 
          if x = Name.uu_ orelse x = Tuple_Tools.strip_uu then
            (v ^ string_of_int n, T)::sanitize (n + 1) xs
          else (x, T)::sanitize n xs
  in
    sanitize 1 ts
  end

fun stack_val (Free (x, \<^Type>\<open>ptr T\<close>)) = (x ^ "'val", T)
  | stack_val t = raise TERM("stack_val: ", [t])

fun append_distinct eq xs ys = xs @ ys |> distinct eq
val union_ptrs = append_distinct cterm_eq

fun snoc x xs = xs @ [x]


val dest_cFree = Thm.term_of #> Term.dest_Free
val name_cFree = dest_cFree #> fst

fun discharge_first_matching_assumption thm rule =
  let
    val n = Thm.nprems_of rule
    fun resolve i = 
          if i = n + 1 then 
            raise THM ("discharge_first_matching_assumption, no match:", i, [rule, thm])
          else 
            (case [thm] RLN (i, [rule]) of
              [rule'] => rule'
            | _ => resolve (i + 1))
  in
    resolve 1
  end

fun is_domain_bound @{term_pat "Trueprop (domain_bound _ _)"} = true
  | is_domain_bound _ = false

fun check_domain_bound st =
 Thm.prems_of st |> forall (is_domain_bound o Utils.concl_of_subgoal_open)


fun gen_normalise_rule prems ctxt thm =
  let
    val ((_, [thm']), ctxt') = Variable.import false [thm] ctxt
    fun select tac = 
      if null prems then 
        ALLGOALS tac
      else 
        EVERY (map tac prems)
  in  
    Utils.check_solve_sideconditions (K true) ctxt thm' ( 
        select (clarsimp_tac ctxt)) 
    |> singleton (Proof_Context.export ctxt' ctxt)
    |> Goal.norm_result ctxt
  end


val normalise_rule = gen_normalise_rule []

fun normalise_rel_stack prems ctxt =
  gen_normalise_rule prems (ctxt addsimps (Named_Theorems.get ctxt @{named_theorems rel_stack_simps}))
   
fun instantiate_normalise_thm maxidx prems ctxt insts rule =
  let 
    val (remaining_vars, thm) = gen_instantiate_thm {unchecked=false} maxidx ctxt insts rule
      |> apsnd (normalise_rel_stack prems ctxt)
  in
     (remaining_vars, thm)
  end

fun dprint_tac b ctxt msg = if b then print_tac ctxt msg else all_tac

val empty_names = \<^cterm>\<open>[]::nat list\<close>

fun gen_mk_name_hints ctxt unit_seed params outs orig_names =
  let
    val out_names = map (name_hint_of params) outs
    val names = if unit_seed then
                  if null outs then 
                    orig_names
                  else
                    out_names
                else
                  out_names @ orig_names
  in names |> HOLogic.mk_list @{typ nat} |> Thm.cterm_of ctxt end

fun mk_name_hints ctxt unit_seed params outs ns =
  let
    val orig_names = HOLogic.dest_list (Thm.term_of ns)
  in gen_mk_name_hints ctxt unit_seed params outs orig_names end

fun mk_name_hints' ctxt params outs = mk_name_hints ctxt true params outs empty_names

fun mk_name_hints_call_exit ctxt params outs =
  let 
    val orig_names = [\<^const>\<open>exit_'\<close>]
  in gen_mk_name_hints ctxt false params outs orig_names end

fun dest_list ct = ct |> Match_Cterm.switch [
  @{cterm_match \<open>?x#?xs\<close>} #> (fn {x, xs, ...} => x ::  dest_list xs),
  @{cterm_match \<open>[]\<close>} #> (fn _ => []),
  fn _ => error ("dest_list: unexpected term" ^ @{make_string} ct)
 ]

fun mk_list cT [] = \<^instantiate>\<open>'a = cT in cterm \<open>[]\<close>\<close>
  | mk_list cT (x::xs) = \<^instantiate>\<open>'a = cT and x=x and xs=\<open>mk_list cT xs\<close>in cterm \<open>x#xs\<close>\<close>

fun shuffle_list perm ct =
  let
    val elT = Thm.ctyp_of_cterm ct |> Thm.dest_ctyp0
    val xs = dest_list ct |> tag_list 0
    val xs_perm = map (fn i => the (AList.lookup (op =) xs (perm i))) (0 upto (length xs - 1))
    val res = mk_list elT xs_perm
  in 
    res
  end

fun ctl ct = ct |> Match_Cterm.switch [
  @{cterm_match \<open>?x#?xs\<close>} #> (fn {xs, ...} => xs),
  fn _ => error ("dest_list: unexpected term" ^ @{make_string} ct)
 ]

fun strip_guard ct = ct |> Match_Cterm.switch [
  @{cterm_match \<open>L2_seq (L2_guard ?P) (\<lambda>_. ?g)\<close>} #> (fn {P, g, ...} => {P = P, g = g}),
  fn _ => error ("strip_gaurd: unexpected term" ^ @{make_string} ct)
 ]

fun pair_input f x = case f x of SOME y => SOME (y, x) | _ => NONE

fun refines_arg_conv i conv = 
  Conv.fconv_rule (Conv.concl_conv (~1) (Conv.arg_conv (* Trueprop *) (Utils.nth_arg_conv i conv)))

val refines_f_conv = refines_arg_conv 1
val refines_g_conv = refines_arg_conv 2

fun refines_fold_f ctxt def = 
  refines_f_conv (Conv.rewr_conv (Utils.symmetric ctxt def))

fun refines_rewr_g eq = refines_g_conv (Conv.rewr_conv eq)


fun simplify_f ctxt thm =
  thm |>
  Conv.fconv_rule (Conv.concl_conv (Thm.nprems_of thm) 
    (Conv.arg_conv (* Trueprop *) 
      (Utils.nth_arg_conv 1 (* input_function_f *)  
        (Simplifier.rewrite ctxt))))

fun norm_accesses ctxt eqs thm =
  let
    (* normalise all accesses except for input function which *)
    val sym_eqs = eqs |> map (Utils.symmetric ctxt)
    val simp_ctxt = Simplifier.clear_simpset ctxt addsimps eqs
    val sym_simp_ctxt = Simplifier.clear_simpset ctxt addsimps sym_eqs
  in
    thm 
    |> Simplifier.asm_full_simplify simp_ctxt 
    |> simplify_f sym_simp_ctxt 
  end

fun simplify_result_rel ctxt thm =
  thm |>
  Conv.fconv_rule (Conv.concl_conv (Thm.nprems_of thm) 
    (Conv.arg_conv (* Trueprop *) 
      (Utils.nth_arg_conv 5 (* result relation of refines *)  
        (Simplifier.rewrite ctxt))))

val mk_projection = Rel_Spec_Monad_Synthesize_Rules.gen_mk_projection

fun eta_contract ctxt = Utils.eta_conv ctxt #> Thm.rhs_of

fun ensure_fixed ct ctxt =
  let
    val t = Thm.term_of ct
    val frees = Term.add_frees t []
    fun fix (x as (n, _)) ctxt = 
      if Variable.is_fixed ctxt n then
         ([], ctxt)
      else
        Utils.fix_variant_cfrees [x] ctxt
    val (new_fixed, ctxt') = ctxt |> fold_map fix frees |> apfst flat
  in
    (new_fixed, ctxt')
  end

fun strip_typ_ctyp ctxt cT = cT 
  |> Thm.typ_of 
  |> strip_type 
  |> apfst (map (Thm.ctyp_of ctxt)) 
  |> apsnd (Thm.ctyp_of ctxt)


fun select_call_thm thms {exit = false, singleton = false} = nth thms 0
  | select_call_thm thms {exit = false, singleton = false} = nth thms 0 
  | select_call_thm thms {exit = false, singleton = true } = nth thms 1
  | select_call_thm thms {exit = false, singleton = true } = nth thms 1
  | select_call_thm thms {exit = true , singleton = false} = nth thms 2
  | select_call_thm thms {exit = true , singleton = false} = nth thms 2
  | select_call_thm thms {exit = true , singleton = true } = nth thms 3
  | select_call_thm thms {exit = true , singleton = true } = nth thms 3

fun rewrs ctxt eqs thm = Conv.fconv_rule (Conv.bottom_rewrs_conv eqs ctxt) thm


datatype entail = Unify | Left of thm | Right of thm

fun entail_tac ctxt thms i = 
  REPEAT_ALL_NEW (
    eresolve_tac ctxt @{thms FalseE} ORELSE' 
    Method.assm_tac ctxt ORELSE'
    resolve_tac ctxt thms) i

val rel_sum_entail_rules = @{thms rel_sum_stack_entail}
fun entail_prover ctxt thms (P, Q) =
  let
    val goal = \<^infer_instantiate>\<open>P = P and Q = Q in cprop 
          \<open>\<And>h x y. P h x y \<Longrightarrow> Q h x y\<close>\<close> ctxt
  in
    Goal.prove_internal ctxt [] goal (fn _ =>
      entail_tac ctxt thms 1)
  end
 
fun rel_sum_entail_prover ctxt Q Q' =
  let


  in
  if Utils.can_unify ctxt Q Q' then Unify
  else 
    (case try (entail_prover ctxt rel_sum_entail_rules) (Q, Q') of
       SOME thm => Left thm
     | NONE => 
         (case try (entail_prover ctxt rel_sum_entail_rules) (Q', Q) of
           SOME thm => Right thm
          | NONE => error ("rel_sum_entail_prover: cannot derive entailment: " ^ 
                     string_of_cterm ctxt Q ^ " " ^ string_of_cterm ctxt Q'))) 
  end

fun select_rel_sum_stack_rule [unify_rule, left_rule, right_rule] ctxt Q Q' =
  (case rel_sum_entail_prover ctxt Q Q' of
     Unify => unify_rule
   | Left thm => left_rule OF_COMP [thm]
   | Right thm => right_rule OF_COMP [thm])


val dest_canonical_call = Match_Cterm.switch [
  @{cterm_match 
     \<open>L2_seq (L2_guard ?P) (\<lambda>_. 
        L2_seq 
          (L2_catch ?g 
             (\<lambda>x. L2_seq (liftE (?h x)) (\<lambda>_. L2_throw (?prj x) ?ns_exit))) ?X)\<close>} #> (fn {P, g, h, prj, ns_exit, X, ... } => 
       {P = P, g = g, h = h, prj = prj, ns_exit = ns_exit, X = X}),
  (fn ct => error ("dest_canonical_call: unexpected term: " ^ @{make_string} ct))
]

val dest_disjoint = Match_Cterm.switch [
  @{cterm_match \<open>Trueprop (?X \<inter> ?Y = {})\<close>} #> (fn {X, Y, ...} => (X, Y)),
  @{cterm_match \<open>?X \<inter> ?Y = {}\<close>} #> (fn {X, Y, ...} => (X, Y))
]

fun list_of_pair (x, y) = [x, y]


fun eta_tupled ctxt =
  let
    val ctxt' = Simplifier.clear_simpset ctxt 
      addsimps @{thms fst_conv snd_conv}
      addsimprocs [@{simproc ETA_TUPLED}]
  in Simplifier.asm_full_simplify ctxt' end

val L2_seq_eliminate_ptr = Unsynchronized.ref true;
val eliminate_ptr_local_def_tac = Unsynchronized.ref true;

val with_fresh_stack_ptr_eliminate_ptr = Unsynchronized.ref true;
val use_Union_Diff_conv = Unsynchronized.ref false;
val L2_seq_debug = Unsynchronized.ref false;
val d1 = Unsynchronized.ref false;
val d2 = Unsynchronized.ref false;
val d3 = Unsynchronized.ref false;
val d4 = Unsynchronized.ref false;
val d5 = Unsynchronized.ref false;
val d6 = Unsynchronized.ref false;
val d7 = Unsynchronized.ref false;
val d8 = Unsynchronized.ref false;
val d9 = Unsynchronized.ref false;
val d10 = Unsynchronized.ref false;
val d11 = Unsynchronized.ref false;
val sd1 = Unsynchronized.ref true;
val sd2 = Unsynchronized.ref true;
val sd3 = Unsynchronized.ref true;
val sd4 = Unsynchronized.ref true;
val sd5 = Unsynchronized.ref true;
val sd6 = Unsynchronized.ref true;
val sd7 = Unsynchronized.ref true;
val sd8 = Unsynchronized.ref true;
val sd9 = Unsynchronized.ref true;
val sd10 = Unsynchronized.ref true;
val sd11 = Unsynchronized.ref true;



fun sidecondition_simp_tac ctxt =
  SOLVED' (asm_simp_tac ctxt) ORELSE' (
    Utils.verbose_print_subgoal_tac 1 "asm_simp_tac failed, trying asm_full_simp_tac: " ctxt THEN'
    asm_full_simp_tac ctxt)

fun mk_equals (ct, ct') = \<^instantiate>\<open>'a = \<open>Thm.ctyp_of_cterm ct\<close> and x=ct and y=ct' in cterm "x \<equiv> y"\<close>
fun mk_eq (ct, ct') = \<^instantiate>\<open>'a = \<open>Thm.ctyp_of_cterm ct\<close> and x=ct and y=ct' in cterm "x = y"\<close>

fun msg' prfx ctxt i {input, timing:Timing.timing, ...} =
  if #elapsed timing > Time.fromMilliseconds 1000 then
    let
      val prfx' = if prfx = "" then "" else prfx ^ " ";
      val _ = Utils.print_subgoal_tac "" ctxt i input
    in prfx' ^ "subgoal " ^ string_of_int i end
  else ""

fun timeit_tac' prfx ctxt tac i st =
   Utils.timeap_msg_tac 2 ctxt (msg' prfx ctxt i) (tac i) st

fun msg prfx ctxt {input, timing:Timing.timing, ...} =
  if #elapsed timing > Time.fromMilliseconds 1000 then
    let
      val prfx' = if prfx = "" then "" else prfx ^ " ";
      val _ = print_tac ctxt "" input
    in prfx' ^ "goal " end
  else ""

fun timeit_tac prfx ctxt tac st =
   Utils.timeap_msg_tac 2 ctxt (msg prfx ctxt) (tac) st

fun solve_sideconditions ctxt thm0 tac terminal_tac =
  Utils.solve_sideconditions ctxt thm0 
    (tac THEN (timeit_tac "ALL terminal_tac" ctxt (ALLGOALS terminal_tac)))

fun dest_equal_upto_heap_on phi = Match_Cterm.switch [
  @{cterm_morph_match \<open>Trueprop (equal_upto_heap_on ?S ?s ?t)\<close>} phi #> (fn {S, s, t, ...} => {S=S, s=s, t=t}),
  @{cterm_morph_match \<open>equal_upto_heap_on ?S ?s ?t\<close>} phi #> (fn {S, s, t, ...} => {S=S, s=s, t=t})
  ]

fun norm_results ctxt = \<comment> \<open>cf. @{ML Goal.norm_result}\<close>
  map (Drule.flexflex_unique (SOME ctxt) #> Raw_Simplifier.norm_hhf_protect ctxt #> Thm.strip_shyps) 
  #> Drule.zero_var_indexes_list (* consistent renaming on all theorems *)

fun operations phi: operations =
let
  val G = Morphism.cterm phi \<^cterm>\<open>\<G>\<close>
  val dest_equal_upto_heap_on = dest_equal_upto_heap_on phi
  val ensure_disjoint_alloc_globals = ensure_disjoint_alloc_globals phi
  val ensure_modifies_globals = ensure_modifies_globals phi
  val ensure_disjoint_stack_free_globals = ensure_disjoint_stack_free_globals phi
  val ptrs_of_set = ptrs_of_set phi
  val sT = Morphism.typ phi @{typ 's} |> map_type_tvar (K @{typ unit})
  val frame_heap_independent_selector = Morphism.thm phi @{thm frame_heap_independent_selector}
  val L2_unknown_rel_stack = morph_check_vars phi @{thm L2_unknown_rel_stack}
  val L2_fail_rel_stack = morph_check_vars phi @{thm L2_fail_rel_stack}
  val L2_gets_rel_stack = morph_check_vars phi @{thm L2_gets_rel_stack}
  val L2_gets_rel_stack_guarded = morph_check_vars phi @{thm L2_gets_rel_stack_guarded}
  val L2_guard_rel_stack = morph_check_vars phi @{thm L2_guard_rel_stack}
  val L2_modify_heap_update_rel_stack = morph_check_vars phi @{thm L2_modify_heap_update_rel_stack}
  val L2_modify_keep_heap_update_rel_stack = morph_check_vars phi @{thm L2_modify_keep_heap_update_rel_stack}
  val L2_modify_keep_heap_update_rel_stack_guarded = morph_check_vars phi @{thm L2_modify_keep_heap_update_rel_stack_guarded}

  val L2_seq_rel_stack_g2_normalised = morph_check_vars phi @{thm L2_seq_rel_stack_g2_normalised}

  val L2_throw_rel_stack = morph_check_vars phi @{thm L2_throw_rel_stack}
  val L2_try_rel_stack = Morphism.thm phi @{thm L2_try_rel_stack}
  val L2_try_rel_stack_merge1 = Morphism.thm phi @{thm L2_try_rel_stack_merge1}
  val L2_try_rel_stack_merge2 = Morphism.thm phi @{thm L2_try_rel_stack_merge2}
  val L2_try_rule = select_rel_sum_stack_rule [L2_try_rel_stack, L2_try_rel_stack_merge2, L2_try_rel_stack_merge1]
  val with_fresh_stack_ptr_rel_stack_fix_initialized_g_normalised = morph_check_vars phi @{thm with_fresh_stack_ptr_rel_stack_fix_initialized_g_normalised}
  val with_fresh_stack_ptr_rel_stack_uninitialized_g_normalised = morph_check_vars phi @{thm with_fresh_stack_ptr_rel_stack_uninitialized_g_normalised}
  val keep_with_fresh_stack_ptr_rel_stack_g_normalised = morph_check_vars phi @{thm keep_with_fresh_stack_ptr_rel_stack_g_normalised}
  val refines_rel_stack_project_result = morph_check_vars phi @{thm refines_rel_stack_project_result}
  val refines_rel_stack_adjust_result = morph_check_vars phi @{thm refines_rel_stack_adjust_result}
  val L2_spec_rel_stack_heap_agnostic = morph_check_vars phi @{thm L2_spec_rel_stack_heap_agnostic}
  val L2_assume_rel_stack_heap_agnostic = morph_check_vars phi @{thm L2_assume_rel_stack_heap_agnostic}
  val rel_alloc_def = Morphism.thm phi @{thm rel_alloc_def}

  val L2_call_rel_stack_bare = morph_check_vars phi @{thm L2_call_rel_stack_bare}
  val L2_call_rel_stack_bare_retype_unreachable_exit = morph_check_vars phi @{thm L2_call_rel_stack_bare_retype_unreachable_exit}
  val L2_call_rel_stack_nest_exit_guarded = morph_check_vars phi @{thm L2_call_rel_stack_nest_exit_guarded}
  val L2_call_rel_stack_embellish_exit = morph_check_vars phi @{thm L2_call_rel_stack_embellish_exit}
  val globals_subset_trans = morph_check_vars phi @{thm globals_subset_trans}
  val globals_disjoint_subset = Morphism.thm phi @{thm globals_disjoint_subset}
  val refines_rel_stack_extend_modifies = morph_check_vars phi @{thm refines_rel_stack_extend_modifies}

  val refines_rel_stack_override_heap_on_exit_guarded = morph_check_vars phi @{thm refines_rel_stack_override_heap_on_exit_guarded}

  val refines_rel_stack_override_heap_emptyI = Morphism.thm phi @{thm refines_rel_stack_override_heap_emptyI}
  val override_heap_on_empty = Morphism.thm phi @{thm  override_heap_on_empty}
  val refines_rel_stack_shuffle_both = morph_check_vars phi @{thm refines_rel_stack_shuffle_both}
  val refines_rel_stack_shuffle_no_exit = morph_check_vars phi @{thm refines_rel_stack_shuffle_no_exit}

  val refines_rel_stack_pop_heap = [ 
    @{thm refines_rel_stack_pop_heap_no_exit_guarded},
    @{thm refines_rel_stack_pop_heap_no_exit_singleton_guarded},
    @{thm refines_rel_stack_pop_heap_both_guarded},
    @{thm refines_rel_stack_pop_heap_both_singleton_guarded}] 
    |> map (morph_check_vars phi) |> select_call_thm

  val L2_condition_rel_stack = morph_check_vars phi @{thm L2_condition_rel_stack}
  val L2_while_rel_stack = morph_check_vars phi @{thm L2_while_rel_stack}
  val L2_while_rel_stack_g_normalised = morph_check_vars phi @{thm L2_while_rel_stack_g_normalised}
  val L2_while_rel_stack_g_normalised_guarded = morph_check_vars phi @{thm L2_while_rel_stack_g_normalised_guarded}

  val refines_to_IOcorres = morph_check_vars phi @{thm refines_to_IOcorres}

  val equal_upto_disjoint_h_val = @{thm equal_upto_disjoint_h_val}

  val rel_alloc_fold_frame = morph_check_vars phi @{thm rel_alloc_fold_frame}
  val rel_alloc_stack_free_disjoint = map (Morphism.thm phi) @{thms rel_alloc_stack_free_disjoint_trans rel_alloc_stack_free_disjoint_trans'}
  val rel_alloc_stack_free_disjoint_field_lvalue = map (Morphism.thm phi) @{thms rel_alloc_stack_free_disjoint_field_lvalue_trans rel_alloc_stack_free_disjoint_field_lvalue_trans'}

  val h_val_frame_disjoint = Morphism.thm phi @{thm h_val_frame_disjoint}
  val h_val_frame_disjoint' = Morphism.thm phi @{thm h_val_frame_disjoint'}
  val h_val_frame_disjoint_globals = Morphism.thm phi @{thm h_val_frame_disjoint_globals}
  val h_val_rel_alloc_disjoint =  Morphism.thm phi @{thm h_val_rel_alloc_disjoint}

  val refines_widen_modifies'' = Morphism.thm phi @{thm refines_widen_modifies''}
  val refines_widen_modifies_weaken = Morphism.thm phi @{thm refines_widen_modifies_weaken}
  val refines_rel_stack_root_upd_result = morph_check_vars phi @{thm refines_rel_stack_root_upd_result}

  val rel_alloc_modifies_antimono = Morphism.thm phi @{thm rel_alloc_modifies_antimono}
  val refines_rel_sum_stack_generalise_exit = Morphism.thm phi @{thm refines_rel_xval_stack_generalise_exit}

  val equal_upto_heap_on_equal_upto_htd = Morphism.thm phi @{thm equal_upto_heap_on_equal_upto_htd}
  val equal_upto_heap_on_equal_upto_hmem = Morphism.thm phi @{thm equal_upto_heap_on_equal_upto_hmem}
  val equal_upto_heap_on_def = Morphism.thm phi @{thm equal_upto_heap_on_def}

  val dest_refines = @{cterm_morph_match \<open>Trueprop (refines ?f ?g ?s ?t (rel_stack ?S ?M ?A ?s ?t0.0 (rel_xval_stack ?L ?R)))\<close>} phi
  val dest_refines' = @{cterm_morph_match \<open>Trueprop (refines ?f ?g ?s ?t (rel_stack ?S ?M ?A ?s ?t0.0 ?Q))\<close>} phi
         (* FIXME: dummy pattern seem to be an issue for cterm_morph_match *)

  fun get_modifies thm = Thm.cconcl_of thm |> dest_refines |> (fn {M, ...} => ptrs_of_set M)
  fun get_stacked_outs thm = Thm.cconcl_of thm |> dest_refines |> (fn {R, ...} => dest_stack_rel R)

  fun get_spec ctxt f = 
    let
      val f_thms = Synthesize_Rules.retrieve_rules (Context.Proof ctxt) @{synthesize_rules_name refines_in_out} 
                (SOME f) |> snd |> map (Thm.transfer' ctxt o #rule o Synthesize_Rules.dest_rule)
      val f_thm = case f_thms of
            [f_thm] => f_thm
          | [] => error ("no in-out parameter theorem for: " ^ Syntax.string_of_term ctxt f)
          | _  => error ("multiple in-out parameter theorems for " ^ Syntax.string_of_term ctxt f ^ ":\n " ^ 
                          string_of_thms ctxt f_thms)
    in f_thm end

  val dest_rel_alloc = Match_Cterm.switch [
    @{cterm_morph_match \<open>Trueprop (rel_alloc ?S ?M ?A ?t0.0 ?s ?t)\<close>} phi #> (fn {S, M, A, t0, s, t, ...} =>
       SOME ({S = S, M = M, A = A, t0 = t0, s = s, t = t})),
    fn _ => NONE]

  fun domain_bound_tac ctxt = 
    let
       val domain_bound_intros = Named_Theorems.get ctxt @{named_theorems domain_bound_intros}
       val alloc_assms = Named_Rules.get ctxt @{named_rules alloc_assms}
    in
      DETERM' (REPEAT_ALL_NEW (resolve_tac ctxt (domain_bound_intros @ alloc_assms)))
    end


  val dest_hval' = dest_hval' phi

  \<comment> \<open>This function tunes the performance of resolution of a refines theorem under 
    locally bound variables and premises, like e.g. in rule @{thm L2_seq_rel_stack} the 
    theorem for the refinement of the second statement of @{term "L2_seq f1 f2"}. 
    It turned out that for large statements @{term f2} standard resolution and then simplification
    of @{term \<open>g2' s' w = g2 w\<close>} was rather slow. This function does both steps quite explicitly.
      It avoids lifting of the theorem by entering the context first (Subgoal.FOCUS_PREMS). Lifting
    seems to be very expensive when the theorem contains schematic variables. Note that in our
    flow the conclusion has an instantiated @{term f2} while the theorem may still have some
    schematic term and type variables in its version of @{term f2}
      We factor out the dependency of \<^term>\<open>g2'\<close> on \<^term>\<open>s'\<close> by providing equations that the
    value of the relevant pointers did not change. To do this simplification we explicitly abstract
    over the relevant heap pointers and fold the body into a local definition. This avoids that
    the simplifier has to traverse a potentially large body for \<^term>\<open>g2'\<close>\<close>
  fun resolve_refines_g_normalise ctxt A s0 ptrs0 rule =
    let
      fun is_disjoint_alloc thm = (thm |> Thm.cconcl_of |> dest_disjoint |> list_of_pair |> exists (fn x => cterm_eq (A, x)))
             handle Pattern.MATCH => false | Match => false
      fun is_equal_upto_heap_on thm = (thm |> Thm.cconcl_of |> dest_equal_upto_heap_on |> K true)
             handle Pattern.MATCH => false | Match => false

      val s = Thm.term_of s0
      val ptrs = map (Thm.term_of) ptrs0
      val ord = prod_ord Term_Ord.fast_term_ord Term_Ord.fast_term_ord
      fun tac {context, params, prems, concl, ... } = 
        let
          \<comment> \<open>for \<^term>\<open>with_fresh_stack_ptr\<close> rules we pre-calculate some properties
           for the bound pointer which come from the prems\<close>
          val disj_allocs = filter is_disjoint_alloc prems
          val disjoint_alloc_subset = disj_allocs
            |> maps (fn thm => Utils.OFs [thm] @{thms disjoint_subset_simps'})
          val equal_upto_heap_ons = filter is_equal_upto_heap_on prems
          val equal_upto_hmems = equal_upto_heap_ons |> maps (fn thm => Utils.OFs [thm] [equal_upto_heap_on_equal_upto_hmem])
          val disj_hvals = equal_upto_hmems |> maps (fn thm => Utils.OFs [thm] [equal_upto_disjoint_h_val])
          val dest_hval = dest_hval' (Proof_Context.theory_of context)
          fun is_hval_eq @{term_pat "Trueprop (?x = _)"} = is_some (dest_hval x)
            | is_hval_eq _ = false
          val hval_eq_prems = filter (is_hval_eq o Thm.concl_of) prems

          val {f = f_concl, s = s_concl,...} = dest_refines' concl
          val {f = f_rule, s = s_rule, ...} = rule |> Thm.cconcl_of |> dest_refines'
          val insts1 = Thm.match (f_rule, f_concl)
          val insts2 = Thm.match (s_rule, s_concl)
          val rule_inst = rule |> Thm.instantiate insts1 |> Thm.instantiate insts2
          val ((_, [rule_inst_imported]), ctxt) = Variable.import false [rule_inst] context
          val {g, ...} = rule_inst_imported |> Thm.cconcl_of |> dest_refines'


          val goal_params = map (Thm.term_of o snd) params
          val is_goal_param = member (aconv) goal_params
          val is_ptr = member (aconv) ptrs
          val dest = dest_hval #> Option.map
                (fn (p, s) => (
                   if is_goal_param s andalso is_ptr p then
                     Ord_List.make ord [(p, s)]
                   else []))

          fun merge t vs =
             dest t |> Option.map (fn vs' => Ord_List.union ord vs' vs)
             handle TERM _ => NONE

          val vs0 = Ord_List.make ord []
          val vs = vs0
            |> fold_subterms_open merge (Thm.term_of g)
            |> these

          val simp_ctxt = context addsimps (disjoint_alloc_subset @ disj_hvals)
          fun mk_hval_eq (p, s') =
            let
              val prop = \<^morph_infer_instantiate>\<open>p = p and s' = s' and s= s in 
                prop \<open>h_val (hmem s') p = h_val (hmem s) p\<close>\<close> phi context |> Thm.cterm_of context
              val thm = Goal.prove_internal simp_ctxt [] prop (fn _ => 
                Method.insert_tac simp_ctxt prems 1 THEN
                asm_full_simp_tac simp_ctxt 1)
            in thm end
          val eqs = Utils.timeit_msg 2 context (fn _ => "resolve_refines_g2_normalise eqs: ") (fn _ => Par_List.map mk_hval_eq vs)
          val all_eqs =  (eqs @ hval_eq_prems)
          val _ = if !L2_seq_debug then tracing ("eqs: " ^ string_of_thms context eqs) else ()
          val lhs = Utils.timeit_msg 2 context (fn _ => "resolve_refines_g2_normalise lhs: ") (fn _ => 
                  g |> eta_contract context)
          val hvals = map (Utils.clhs_of_eq o Thm.cconcl_of) all_eqs
          val lhs' = lhs |> fold (fn v => Thm.lambda v) hvals
          val ([g_fix], ctxt0) = Utils.fix_variant_cfrees [("g", Thm.typ_of_cterm lhs')] ctxt
          val ([def_eq], ctxt1) = Assumption.add_assms Local_Defs.def_export [mk_equals (g_fix, lhs')] ctxt0
          val (args_s', args_s) = map (Utils.dest_eq' o Thm.cconcl_of) all_eqs |> split_list
          val eq = mk_equals (
                    fold_rev (fn x => fn f => Thm.apply f x) args_s' g_fix,
                    fold_rev (fn x => fn f => Thm.apply f x) args_s g_fix)
          val eq_thm = Utils.timeit_msg 2 ctxt1 (fn _ => "resolve_refines_g2_normalise eq_thm: ") (fn _ => 
                Goal.prove_internal ctxt1 [] eq (fn _ =>
                  asm_full_simp_tac (Simplifier.clear_simpset ctxt1 addsimps all_eqs) 1))
          val [eq_thm1] = Utils.timeit_msg 2 ctxt1 (fn _ => "resolve_refines_g2_normalise export: ") (fn _ => 
                 Proof_Context.export ctxt1 context [eq_thm])
          val rule'' = refines_rewr_g eq_thm1 rule_inst
        in
          resolve_tac context [rule''] 1
        end
    in
      Subgoal.FOCUS_PREMS tac ctxt
    end
  fun check_in_out ctxt ps @{term_pat \<open>h_val _ ?p\<close>} = 
      if member (op =) ps (root_ptr p) then 
        Known_Good 
      else 
        Neutral
  | check_in_out ctxt ps @{term_pat \<open>c_guard ?p\<close>} = 
      if member (op =) ps (root_ptr p) then 
        Known_Good 
      else 
        Neutral
  | check_in_out ctxt ps @{term_pat \<open>heap_update ?p ?v\<close>} = 
      let val p_res = if member (op =) ps (root_ptr p) then Known_Good else Neutral
      in
         merge_check_result p_res (check_subterms_open (check_in_out ctxt ps) v)
      end
  | check_in_out ctxt ps @{term_pat \<open>L2_call ?f _ _\<close>} =
      let
        val (_, args) = strip_comb f
        val f_thm = \<^try>\<open>get_spec ctxt f catch _ => (
          Utils.verbose_msg 4 ctxt (fn _ => "check_in_out: no spec for " ^ Syntax.string_of_term ctxt f); 
          raise Early_Bad)\<close>
        val _ = Utils.verbose_msg 4 ctxt (fn _ => "check_in_out: got spec: " ^ Thm.string_of_thm ctxt f_thm)
        val {A, f=f_spec, ...} = f_thm |> Thm.cconcl_of |> dest_refines
        val A = Thm.term_of A
        fun dest_alloc @{term_pat \<open>Trueprop (ptr_span ?p \<subseteq> ?A')\<close>} =
             if A' = A then [p] else []
          | dest_alloc _ = []

        val alloc_ptrs = f_thm |> Thm.prems_of |> map dest_alloc |> flat
        val spec_args = f_spec |> Thm.term_of |> strip_comb |> snd
        fun is_in_out spec_arg = member (op =) alloc_ptrs spec_arg

        fun check_arg (p as Free _, spec_arg) = 
              if member (op =) ps p then
                if is_in_out spec_arg then Known_Good else Known_Bad
              else
                Neutral  
          | check_arg (p, _) = check_subterms_open (check_in_out ctxt ps) p
        val res = all_check check_arg (map root_ptr args ~~ spec_args)
      in 
        res
      end
  | check_in_out ctxt ps (p as (Free _)) = 
     if member (op =) ps p then 
       Known_Bad
     else
       Neutral
  | check_in_out _ _ _ = Neutral

  val ensure_disjoint_stack_free = ensure_disjoint_stack_free phi  
  val ensure_stack_ptr = ensure_stack_ptr phi
  val ensure_disjoint_globals = ensure_disjoint_globals phi

  fun enter_block (fixed as {M, A, params, in_out_globals:bool}) (fresh as {t0, s, t}) ctxt =
    let
      val ([t0, s, t], states_fix_ctxt) = Utils.fix_variant_cfrees ([t0, s, t]) ctxt
      val (_, ptr_allocs_ctxt) = states_fix_ctxt 
        |> fold_map (ensure_alloc A) (alloc_ptrs params)
        ||>> fold_map (ensure_modifies M) (modified_ptrs params)
        ||>> fold_map (ensure_disjoint_alloc A) (keep_ptrs params)
        ||>> fold_map (ensure_disjoint_stack_free s) (keep_ptrs params)
        ||>> fold_map (ensure_stack_ptr) (keep_stack_ptrs params)
        ||> in_out_globals ? (
              ensure_disjoint_globals A s #> snd #>
              ensure_modifies_globals M #> snd)
      val ([rel_alloc], alloc_ctxt) = Assumption.add_assumes [
            \<^morph_infer_instantiate>\<open>M = M and A = A and t\<^sub>0 = t0 and s = s and t = t in 
              cprop \<open>rel_alloc \<S> M A t\<^sub>0 s t\<close>\<close> phi ptr_allocs_ctxt] ptr_allocs_ctxt
    in
      ({t0 = t0, s = s, t = t, rel_alloc = rel_alloc}, alloc_ctxt)
    end

  fun abstract_params ctxt s params g =
    let
      val cparam_vals = map (in_param_val phi ctxt s) params |> flat |> map (fn (x, t) => (name_of_cterm x, t))
      val g' = g |> fold_rev Thm.lambda_name cparam_vals
    in 
      {g' = g', vals = map snd cparam_vals}
    end

  fun fix_params_state ctxt return s params p_opt e =
    let
      val cparam_vals = map (in_param_val phi ctxt s) params |> flat |> map (fn (x, t) => (name_of_cterm x, t))
      val outs = map (out_param return) params |> flat
      val n = length cparam_vals + 1;
      val e_s = Utils.apply_beta_conv e s
      val e' = e_s |> fold Thm.lambda_name cparam_vals |> Thm.lambda_name (name_of_cterm s, s)
        |> reverse_abs n |> Utils.beta_applies (map snd cparam_vals)
        |> result_tuple p_opt phi ctxt s outs
  
      val dest_hval = dest_hval' (Proof_Context.theory_of ctxt)
      val ord = Term_Ord.fast_term_ord
      val ptr_params = maps ptr_param params |> map Thm.term_of |> Ord_List.make ord
      val st = Thm.term_of s

      val dest = dest_hval #> Option.map
                (fn (p, s) => (
                   if s = st andalso not (Ord_List.member ord ptr_params p) then
                     Ord_List.make ord [p]
                   else []))
      fun merge t ps =
        dest t |> Option.map (fn ps' => Ord_List.union ord ps' ps)
        handle TERM _ => NONE
      val ps0 = Ord_List.make ord []
      val ps = ps0 |> fold_subterms_open merge (Thm.term_of e_s) |> these |> map (Thm.cterm_of ctxt)

    in
      {e' = e', n = n, outs = outs, 
        out_vals = map (fn p => (name_of_cterm p, h_val phi ctxt s p)) outs, 
        other_ptrs = ps}
    end

  fun abstract_ptr_vals ctxt ptrs s g =
    let
      val ptr_vals = map (ptr_val phi ctxt s) ptrs
      val g' = g |> fold_rev Thm.lambda_name ptr_vals
    in
      {g' = g', ptr_vals = ptr_vals}
    end

  fun abstract_vals vals g =
    let
      val named_vals = map (fn x => (name_of_cterm x, x)) vals
      val g' = g |> fold_rev Thm.lambda_name named_vals
    in
      g'
    end

  fun unmodified_params modified params =
    let
      val ps = maps ptr_param params |> filter_out (member cterm_eq modified)
    in
      ps
    end

  fun unmodified_param_vals ctxt modified s params =
    let
      val cparam_vals = map (ptr_param_val phi ctxt s) params |> flat
        |> filter_out (member cterm_eq modified o fst)
        |> map (fn (x, t) => (name_of_cterm x, (x, t)))
      in cparam_vals end

  fun abstract_unmodified ctxt modified s params g =
    let
      val cparam_vals = unmodified_param_vals ctxt modified s params
      val g' = g |> fold_rev Thm.lambda_name (map (apsnd snd) cparam_vals)
    in
      {g' = g', vals = cparam_vals}
    end

  fun global_guard ctxt other_ptrs t =
    let
      val global_grds = other_ptrs |> map (ptr_span_contained ctxt G)
      val needs_guard = not (null global_grds)
      val (contained_thms, abs_guard, guard_ctxt) = 
        if needs_guard then
         let
            val ({grd, grds}, guard_ctxt) = assume_grds global_grds ctxt
            val abs_guard = cterm_lambda t (dest_Trueprop (Thm.cprop_of (the grd)))
         in
           (grds, abs_guard, guard_ctxt)
         end 
        else ([], cterm_lambda t @{cterm "True"}, ctxt)
    in
      (contained_thms, abs_guard, needs_guard, guard_ctxt)
    end
 
  fun expr_simp_ctxt contained_thms ctxt =
    let
      val disjoint_alloc = Named_Rules.get ctxt @{named_rules disjoint_alloc}  
      val disjoint_stack_free = Named_Rules.get ctxt @{named_rules disjoint_stack_free}
      val h_val_globals_frame_eq = Named_Rules.get ctxt @{named_rules h_val_globals_frame_eq}

      (* instantiate h_val_frame_disjoint to have unconditional simp rule to avoid looping with
        frame_heap_independent_selector *)  
      val disjoint_simps = disjoint_alloc
        |> map_filter (fn thm => try (fn thm => h_val_frame_disjoint' OF [thm]) thm)
        |> map_filter (Utils.first_OF disjoint_stack_free)

      val disjoint_globals_simps = h_val_globals_frame_eq
        |> maps (fn rule => (map (fn p_G => rule OF [p_G]) contained_thms))

      val simp_ctxt = 
        ctxt addsimps (disjoint_globals_simps @ disjoint_simps @ [frame_heap_independent_selector])
          delsimps @{thms ptr_add_0_id}
    in
      simp_ctxt
    end

  fun in_out_expression export_guard ctxt return {A, params, t0, s, t, ...} e =
    let
      val {e', outs, out_vals, other_ptrs, ...} = fix_params_state ctxt return s params NONE e
      val orig_resT = Thm.typ_of_cterm e |> strip_type |> snd
      val (Q, unit_seed) = stack_rel ctxt orig_resT (map Thm.term_of outs) |> apfst (Thm.cterm_of ctxt)
      val goal = \<^morph_infer_instantiate>\<open>Q = Q and e = e and e' = e' and A = A and t\<^sub>0 = t0 and s = s in 
        cprop \<open>Q (hmem s) (e s) (e' (frame A t\<^sub>0 s))\<close>\<close> phi ctxt
      val (contained_thms, abs_guard, needs_guard, guard_ctxt) = global_guard ctxt other_ptrs t


      val rel_stack_intros = Named_Theorems.get ctxt @{named_theorems rel_stack_intros}
      val simp_ctxt = expr_simp_ctxt contained_thms guard_ctxt
      val result_rel_thm = Goal.prove_internal guard_ctxt [] goal (fn _ => 
        REPEAT_ALL_NEW (  
          resolve_tac guard_ctxt rel_stack_intros 
          ORELSE' (
            AutoCorresUtil.CHANGED' (asm_full_simp_tac (simp_ctxt)))) 1)
         |> export_guard ? singleton (Proof_Context.export guard_ctxt ctxt)
    in
      ({e' = e', Q = Q, result_rel_thm = result_rel_thm, outs = outs, out_vals = out_vals, 
          unit_seed = unit_seed, needs_guard = needs_guard, guard_ctxt = guard_ctxt, abs_guard = abs_guard})
    end 

  fun export_guarded guard_ctxt ctxt refines_thm = 
    let
      val refines_thm' = Assumption.export guard_ctxt ctxt refines_thm
    in
      if Thm.nprems_of refines_thm' > 0 then
          (Utils.verbose_msg 5 ctxt (fn _ => "export_guarded: "  ^ Thm.string_of_thm guard_ctxt refines_thm'); 
          (Thm.incr_indexes (Thm.maxidx_of refines_thm' + 1) @{thm refines_L2_guard_right}) OF_COMP [refines_thm'])
      else
        refines_thm
    end  
  fun in_out_exn ctxt {exit_unreachable, seed_rel_opt} ({params, modified, try_modified, A, t0, s, ...}:args) v =
    let
      val level = exn_level v
      val try_level = length try_modified
      val (outer_modified, return) = 
       if try_level <= level (* exit *) then
            ([], Final) 
       else 
         nth try_modified (level - 1)
      val modified = union_ptrs outer_modified modified
      fun relevant_out (p, kind) = returns_throw modified return (p, kind) 
      val outs = map (out_param relevant_out) params |> flat
   
      fun make_seed_rel exit_unreachable is_left x =
        let
          val xT = Thm.typ_of_cterm x
          val x = \<^infer_instantiate>\<open>'a = \<open>Thm.ctyp_of_cterm s\<close> and x = x in cterm \<open>\<lambda>_::'a. x\<close>\<close> ctxt
          val relevant_outs =
            if is_left andalso exit_unreachable then 
              outs (* we call a function and embellish exit-status *)
            else 
              case seed_rel_opt of 
                SOME Q => dest_stack_rel Q
              | NONE => outs;

          val x' = x |> result_tuple NONE phi ctxt s relevant_outs
          val x'T = x' |> Thm.ctyp_of_cterm |> Utils.crange_type
          val ((Q, unit_seed), prems) = 
             if is_left andalso exit_unreachable then
               (( \<^instantiate>\<open>'a=\<open>Thm.ctyp_of ctxt xT\<close> and 'b = x'T in cterm \<open>\<lambda>(_::heap_mem) (_::'a) (_::'b). False\<close>\<close>, false),
                 [@{cprop False}])
             else
               case seed_rel_opt of 
                 SOME Q => ((Q, false), [])
               | NONE => (stack_rel ctxt xT (map Thm.term_of relevant_outs) |> apfst (Thm.cterm_of ctxt), [])

          val goal = \<^morph_infer_instantiate>\<open>Q = Q and x = x and x' = x' and A = A and t\<^sub>0 = t0 and s = s in 
            cprop \<open>Q (hmem s) (x s) (x' (frame A t\<^sub>0 s)) \<close>\<close> phi ctxt

          val rel_stack_intros = Named_Theorems.get ctxt @{named_theorems rel_stack_intros}
          val seed_rel_thm = Goal.prove_internal ctxt prems goal (fn thms => 
            REPEAT_ALL_NEW (
              resolve_tac ctxt (rel_stack_intros @ thms)
              ORELSE' asm_full_simp_tac (ctxt addsimps ([frame_heap_independent_selector]))) 1)
        in
          (Q, seed_rel_thm, outs, unit_seed)
        end
      val (L, result_rel_thm, outs, unit_seed, seed_rel) = make_exn_rel ctxt exit_unreachable true make_seed_rel v
    in
      {L = L, result_rel_thm = result_rel_thm, outs = outs, unit_seed = unit_seed, seed_rel = seed_rel}
    end

  fun in_out_guard ctxt (args as {A, t0, params, s, cguards,...}: args) e =
    let
      val ctxt = ctxt |> Context_Position.set_visible false
      val eq = Simplifier.asm_full_rewrite (ctxt addsimps cguards) e
      val e' = eq |> Thm.rhs_of
      val {e', ...} = fix_params_state ctxt (K false) s params NONE e'
      val goal = \<^morph_infer_instantiate>\<open>e'= e' and e = e and A = A and t\<^sub>0 = t0 and s = s in 
        cprop \<open>e' (frame A t\<^sub>0 s) ==> e s\<close>\<close> phi ctxt
      val thm = Goal.prove_internal ctxt [] goal (fn _ =>
        asm_full_simp_tac (ctxt addsimps [eq, frame_heap_independent_selector]) 1)
    in
      {e' = e', implication_thm = thm}
    end

  fun in_out_ptr_modify ctxt return (args as {A, params, t0, s, t, ...}) p v =
    let
      val {e', outs, other_ptrs, ...} = fix_params_state ctxt return s params (SOME p) v
      val orig_resT = @{typ unit}
      val outs = if member cterm_eq outs p then outs else p::outs
      val (R, unit_seed) = stack_rel ctxt orig_resT (map Thm.term_of outs) |> apfst (Thm.cterm_of ctxt)
      val goal = \<^morph_infer_instantiate>\<open>R = R and p = p and v = v and e' = e' and A = A and t\<^sub>0 = t0 and s = s in 
        cprop \<open>R (heap_update p (v s) (hmem s)) () (e' (frame A t\<^sub>0 s))\<close>\<close> phi ctxt

      val (contained_thms, abs_guard, needs_guard, guard_ctxt) = global_guard ctxt other_ptrs t
      val rel_stack_intros = Named_Theorems.get ctxt @{named_theorems rel_stack_intros}
      val simp_ctxt = expr_simp_ctxt contained_thms guard_ctxt
              addsimps @{thms h_val_update_regions_disjoint}
              delsimps (Named_Theorems.get ctxt @{named_theorems size_simps})

      val result_rel_thm = Goal.prove_internal guard_ctxt [] goal (fn _ => 
        REPEAT_ALL_NEW (
          resolve_tac ctxt rel_stack_intros 
          ORELSE' SOLVED' (asm_full_simp_tac simp_ctxt)) 1)
    in
      {e' = e', R = R, result_rel_thm = result_rel_thm, outs = outs, 
        needs_guard = needs_guard, guard_ctxt = guard_ctxt}
    end

  val is_rel_alloc_eq = Match_Cterm.switch [
    @{cterm_morph_match (fo) \<open>rel_alloc \<S> ?M ?A ?t_0 ?s ?t \<equiv> True\<close>} phi #> (fn _ => true), 
    fn x => false]

  fun discharge thm cond_thm = cond_thm OF [thm]

  fun derived_rel_alloc_simps ctxt thm =
    if is_rel_alloc_eq (Thm.cprop_of thm) then 
      let
        val rel_alloc = @{thm Polish.eq_TrueD} OF [thm]
        val rel_alloc_independent_globals = Named_Rules.get ctxt @{named_rules rel_alloc_independent_globals}
        val eqs = map (discharge rel_alloc) rel_alloc_independent_globals 
          |> map_filter (try Simpdata.mk_eq)
      in
        eqs
      end 
    else []
    
  fun add_derived_rel_alloc_mksimps mksimps = (fn ctxt => fn thm =>
    let 
      val thms = mksimps ctxt thm;
      val derived_thms = maps (derived_rel_alloc_simps ctxt) thms
      val _ = Utils.verbose_msg 5 ctxt (fn _ => if null derived_thms then "" else
        "derived rel_alloc_simps: " ^ string_of_thms ctxt derived_thms ^ 
        "\n from:\n " ^ string_of_thms ctxt thms)
    in thms @ derived_thms end)

  fun set_derived_rel_alloc_mksimps ctxt =
    let
       val mksimps = Simpdata.mksimps Simpdata.mksimps_pairs
    in Simplifier.set_mksimps (add_derived_rel_alloc_mksimps mksimps) ctxt end

  fun mk_simp {silent, M} ctxt =
    let
        val size_simps = Named_Theorems.get ctxt @{named_theorems size_simps}

        val cguard_assms = Named_Rules.get ctxt @{named_rules cguard_assms} (* in simpset *)
        val disjoint_assms = Named_Rules.get ctxt @{named_rules disjoint_assms} (* in simpset *)
        val alloc_assms = Named_Rules.get ctxt @{named_rules alloc_assms}
        val disjoint_alloc = Named_Rules.get ctxt @{named_rules disjoint_alloc}
        val all_disjoint_alloc = add_disjoint_syms disjoint_alloc
        val disjoint_alloc_subset = disjoint_alloc 
          |> maps (fn thm => Utils.OFs [thm] @{thms disjoint_subset_simps'})
        val disjoint_stack_free = Named_Rules.get ctxt @{named_rules disjoint_stack_free}
        val all_disjoint_stack_free = add_disjoint_syms disjoint_stack_free
        val disjoint_stack_free_subset = disjoint_stack_free 
          |> maps (fn thm => Utils.OFs [thm] @{thms disjoint_subset_simps'})
        val stack_ptr = Named_Rules.get ctxt @{named_rules stack_ptr}
        val modifies_assms = Named_Rules.get ctxt @{named_rules modifies_assms}
        val globals_subset_trans = instantiate_thm (~1) ctxt [("Y", M)] globals_subset_trans


        val _ = if silent then () else
          let
            val _ = tracing ("cguard_assms: " ^ string_of_thms ctxt cguard_assms)
            val _ = tracing ("alloc_assms: " ^ string_of_thms ctxt alloc_assms)
            val _ = tracing ("all_disjoint_alloc: " ^ string_of_thms ctxt all_disjoint_alloc)
            val _ = tracing ("disjoint_alloc_subset: " ^ string_of_thms ctxt disjoint_alloc_subset)
            val _ = tracing ("all_disjoint_stack_free: " ^ string_of_thms ctxt all_disjoint_stack_free)
            val _ = tracing ("disjoint_stack_free_subset: " ^ string_of_thms ctxt disjoint_stack_free_subset)
            val _ = tracing ("stack_ptr: " ^ string_of_thms ctxt stack_ptr)
            val _ = tracing ("modifies_assms: " ^ string_of_thms ctxt modifies_assms)
            val _ = tracing ("disjoint_assms: " ^ string_of_thms ctxt disjoint_assms)
          in
            ()
          end 

        val simp_ctxt = (ctxt |> silent ? Context_Position.set_visible false 
              |> set_derived_rel_alloc_mksimps) 
              delsimps (size_simps @ @{thms ptr_val_ptr_add_simps})
              addsimps (alloc_assms @ 
                        all_disjoint_alloc @ 
                        all_disjoint_stack_free @ 
                        stack_ptr @ 
                        modifies_assms @ 
                        disjoint_alloc_subset @
                        disjoint_stack_free_subset @
                        [globals_subset_trans, globals_disjoint_subset] @
                        Named_Theorems.get ctxt @{named_theorems rel_stack_simps} @ 
                        @{thms disjoint_union_distrib inter_commute 
                            disjoint_stack_free_equal_upto_trans 
                            disjoint_stack_free_equal_on_trans} @
                        [equal_upto_disjoint_h_val,
                         equal_upto_heap_on_equal_upto_htd,
                         equal_upto_heap_on_equal_upto_hmem, 
                         h_val_rel_alloc_disjoint] @
                        rel_alloc_stack_free_disjoint)
     in
       simp_ctxt
     end

  fun root_h_val_conv ctxt field_lvalue_eqs thm =
    let
      val ctxt = Context_Position.set_visible false ctxt
      val h_val_ctxt = L2Opt.cleanup_ss ctxt [] FunctionInfo.PEEP
            delsimps (Named_Theorems.get ctxt (@{named_theorems size_simps}) @ @{thms ptr_val_ptr_add_simps})
            addsimps
            field_lvalue_eqs 
            |> Simplifier.add_cong @{thm L2_seq_guard_cong_stateless}
      val thm' = thm |> Simplifier.asm_full_simplify h_val_ctxt
    in
      thm'
    end

  fun generalise_unreachable_exit ctxt thm =
    let
      val generalise_unreachable_exitE = @{thms generalise_unreachable_exitE}
      val thm = Utils.solve_sideconditions ctxt refines_rel_sum_stack_generalise_exit (
        resolve_tac ctxt [thm] 1 THEN
        REPEAT (eresolve_tac ctxt generalise_unreachable_exitE 1))
    in
      thm
    end

  fun generalise_unreachable_exit2 ctxt thm1 thm2 =
    let
      val {L = L1, ...} = Thm.cconcl_of thm1 |> dest_refines
      val {L = L2, ...} = Thm.cconcl_of thm2 |> dest_refines
      val maxidx = (~1) |> fold (Integer.max o Thm.maxidx_of) [thm1, thm2]
      val L1 = Thm.incr_indexes_cterm (maxidx + 1) L1
      fun msg L1 L2 = quote (string_of_cterm ctxt L1) ^ " and " ^ quote (string_of_cterm ctxt L2)
    in
      if Utils.can_unify ctxt L1 L2 then
        let val _ = Utils.verbose_msg 7 ctxt (fn _ => "can unify: " ^ msg L1 L2)
        in (thm1, thm2) end
      else (Utils.verbose_msg 7 ctxt (fn _ => "cannot unify: " ^ msg L1 L2);
        if is_bottom_exit L1 then 
          let
            val gen_thm1 = generalise_unreachable_exit ctxt thm1 |> Thm.incr_indexes (maxidx + 1)
            val _ = Utils.verbose_msg 7 ctxt (fn _ => "generalised thm1: " ^ Thm.string_of_thm ctxt gen_thm1)
            val {L = L1', ...} = Thm.cconcl_of gen_thm1 |> dest_refines
            val _ = if Utils.can_unify ctxt L1' L2 then () else
                    tracing ("cannot unify\n L1': " ^ 
                      string_of_cterm ctxt L1' ^ "::" ^ @{make_string} (Thm.ctyp_of_cterm L1') ^ " and\n L2: "  ^ 
                      string_of_cterm ctxt L2  ^ "::" ^ @{make_string} (Thm.ctyp_of_cterm L2))
          in
            (gen_thm1, thm2)
          end
        else if is_bottom_exit L2 then
          let
            val gen_thm2 = generalise_unreachable_exit ctxt thm2 |> Thm.incr_indexes (maxidx + 1)
            val _ = Utils.verbose_msg 7 ctxt (fn _ => "generalised thm2: " ^ Thm.string_of_thm ctxt gen_thm2)
          in
            (thm1, gen_thm2)
          end
        else error ("generalise_unreachable_exit2, cannot merge: " ^ msg L1 L2))
    end

  fun result_stack_rel_unify ctxt thm1 thm2 =
    let
      val {R = R1, ...} = Thm.cconcl_of thm1 |> dest_refines
      val {R = R2, ...} = Thm.cconcl_of thm2 |> dest_refines
      val maxidx = (~1) |> fold (Integer.max o Thm.maxidx_of) [thm1, thm2]
      val R1' = Thm.incr_indexes_cterm (maxidx + 1) R1
    in Utils.can_unify ctxt R1' R2 end

  val dest_hval = dest_hval phi
  fun refines_to_IOcorres_conv ctxt thm =
    let
      val ((_, [thm']), ctxt') = Variable.import false [thm] ctxt
      val {f, g, s,  ...} = thm' |> Thm.cconcl_of |> dest_refines
      val (g, g_args) = Utils.strip_comb_cterm g
      val params = g_args |> map (fn v => case dest_hval v of NONE => (v, NONE) | SOME p => (p, SOME v)) 
      fun fix_param_eq (p, NONE) ctxt = ((p, NONE), ctxt) 
        | fix_param_eq (p, SOME hval) ctxt = 
        let
          val n = name_of_cterm p
          val T = Thm.typ_of_cterm hval
          val ([n_val], ctxt') = Utils.fix_variant_cfrees [(val_name n, T)] ctxt
          val eq = \<^infer_instantiate>\<open>x = n_val and v = hval in cterm \<open>x = v\<close>\<close> ctxt'
        in
          ((n_val, SOME eq), ctxt')
        end
      val (arg_eqs, ctxt') = ctxt' |> fold_map fix_param_eq params
      val eqs = arg_eqs |> map_filter snd
      fun is_rel_alloc @{term_pat "heap_state.rel_alloc"} = true
        | is_rel_alloc _ = false
      val prems = Thm.cprems_of thm' |> filter_out (Term.exists_subterm is_rel_alloc o Thm.term_of)
      fun pred_of ct = ct |> Match_Cterm.switch [
          @{cterm_match "Trueprop ?P"} #> (fn {P, ...} => P),
          fn _ => ct]

      fun mk_conj [] = @{cterm True}
        | mk_conj [P] = pred_of P
        | mk_conj (P::PS) = \<^instantiate>\<open>P1 = \<open>pred_of P\<close> and P2 = \<open>mk_conj PS\<close> in cterm \<open>P1 \<and> P2\<close>\<close>
      val P = mk_conj (eqs @ prems)

      val g' = Utils.applies (map fst arg_eqs) g
      val P = Thm.lambda_name ("s", s) P

      val rule = instantiate_thm (~1) ctxt' [("P", P), ("g", g')] refines_to_IOcorres
      val fun_of_rel_intros = Named_Theorems.get ctxt @{named_theorems fun_of_rel_intros}
      val simp_ctxt = ctxt' 
           delsimps (Named_Theorems.get ctxt @{named_theorems size_simps} @ @{thms ptr_val_ptr_add_simps})
           addsimps @{thms Hoare.conjE_simp}
      val d = !d1
      val thm = Utils.solve_sideconditions ctxt' rule ( 
           dprint_tac d ctxt' "IOcorres (0)" THEN
           asm_simp_tac ctxt' 3 THEN
           dprint_tac d ctxt' "IOcorres (1)" THEN
           resolve_tac ctxt' [thm (* sic *)] 3 THEN 
           dprint_tac d ctxt' "IOcorres (2)" THEN
           REPEAT1 (resolve_tac ctxt' fun_of_rel_intros 2) THEN
           REPEAT1 (resolve_tac ctxt' fun_of_rel_intros 1) THEN
           ALLGOALS (asm_full_simp_tac simp_ctxt)
           )
      val thm = thm |> singleton (Proof_Context.export ctxt' ctxt) |> Goal.norm_result ctxt
    in
      thm
    end
    handle Pattern.MATCH => thm 

    fun adjust_result is_try ctxt (args as {s, params, return, M, ...}) f_thm =
      let
        val returns = if is_try then returns_throw else returns
        val {M = f_M, R, ...} = dest_refines (Thm.cconcl_of f_thm)
        val is_schematic_R = is_Var (Thm.term_of R)
        val ([_, origT, _], _) = Thm.strip_type (Thm.ctyp_of_cterm R)
        val is_schematic_origT = is_TVar (Thm.typ_of origT)
        val (stack_ptrs2, (cseedT, singleton)) = R |> gen_dest_stack_rel
        val seedT = Thm.typ_of cseedT
        val seedTs = HOLogic.strip_tupleT seedT
        val arity_seed = length seedTs
        val unit_seed = (seedT = @{typ unit})
        val (x, xs, ctxt') = 
          if unit_seed then 
            (@{cterm "()"}, [] , ctxt)
          else
            let
              val xs = tag_list 1 seedTs |> map (fn (i, T) => ("x" ^ string_of_int i, T))
              val (xs', ctxt') = Utils.fix_variant_cfrees xs ctxt        
              val x = tuple xs'
            in 
              (x, map fst xs ~~ xs', ctxt')
            end
        val e = \<^instantiate>\<open>'a = \<open>Thm.ctyp_of_cterm s\<close> and 'b = cseedT and x = x in cterm \<open>\<lambda>_::'a. x::'b\<close>\<close>
        val modified_ptrs2 = ptrs_of_set f_M
        val modified = union_ptrs modified_ptrs2 (#modified args)
        val {e', Q, result_rel_thm, outs, out_vals, ...} = in_out_expression true ctxt' (returns modified return) args e
      in 
        if (length stack_ptrs2 = length outs andalso forall cterm_eq (stack_ptrs2 ~~ outs)) 
             (* expected and actual out tuple coincide*)
           orelse
           (is_schematic_R andalso is_schematic_origT) 
             (* we have a joker here for later instantiation so we don't have adapt *) then 
          f_thm
        else
          let
            val vals = map (fn p => (name_of_cterm p, h_val phi ctxt s p))
            val orig_outs = vals stack_ptrs2 @ xs
            val orig_outs = if null orig_outs then [("_", Thm.cterm_of ctxt (Free ("", @{typ unit})))] else orig_outs
            val new_outs = (map snd out_vals) @ (map snd xs)
            val adj = Utils.lambdas_tupled orig_outs (tuple new_outs)
            val ret = Thm.cterm_of ctxt (HOLogic.mk_list @{typ nat} (replicate arity_seed (CLocals.name_hint ctxt "ret'")))
            val ns = mk_name_hints ctxt unit_seed params outs ret
            val rule = instantiate_thm (~1) ctxt [("R'", Q), ("adj", adj), ("ns", ns)] refines_rel_stack_adjust_result
               |> eta_tupled ctxt
            val f2_thm' = rule OF [f_thm]
            val simp_ctxt = mk_simp {silent = !sd1, M = M} ctxt
                  addsimps @{thms split_paired_all}
            val f2_thm' = Utils.solve_sideconditions ctxt f2_thm' (
                  asm_full_simp_tac simp_ctxt 1)
            val _ = Utils.verbose_msg 5 ctxt (fn _ => "in_out_statement: L2_seq adapted f2:\n " ^ Thm.string_of_thm ctxt f2_thm')
          in
            f2_thm'
          end
       end

  fun in_out_statement () = Match_Cterm.switch [
    @{cterm_morph_match \<open>L2_fail\<close>} phi #> (fn {...} => fn ctxt => fn 
      args as {rel_alloc, ...}:args =>
      let
        val thm = instantiate_thm (~1) ctxt [] L2_fail_rel_stack OF [rel_alloc]
        val _ = Utils.verbose_msg 3 ctxt (fn _ => "in_out_statement: L2_fail:\n " ^ Thm.string_of_thm ctxt thm)
      in
        (thm, ctxt)
      end),
    @{cterm_morph_match \<open>L2_unknown ?ns\<close>} phi #> (fn {ns, ...} => fn ctxt => fn 
      args as {rel_alloc, ...} =>
      let
        val thm = instantiate_thm (~1) ctxt [("ns", ns)] L2_unknown_rel_stack OF [rel_alloc]
        val _ = Utils.verbose_msg 3 ctxt (fn _ => "in_out_statement: L2_unknown:\n " ^ Thm.string_of_thm ctxt thm)
      in
        (thm, ctxt)
      end),
    @{cterm_morph_match \<open>L2_gets ?e ?ns\<close>} phi #> (fn {e, ns, ct_, ...} => fn ctxt => fn 
      args as {A, t0, params, s , rel_alloc, return, modified, try_modified,  ...} =>
      let
        val {e', Q, result_rel_thm, outs, unit_seed, needs_guard, guard_ctxt,...} = 
              in_out_expression false ctxt (returns modified return) args e
        val ns' = mk_name_hints guard_ctxt unit_seed params outs ns
        val thm = (instantiate_thm (~1) guard_ctxt [("R", Q), ("e", e), ("e'", e'), ("ns", ns), ("ns'", ns')] 
          L2_gets_rel_stack OF_COMP [result_rel_thm, rel_alloc]) |> export_guarded guard_ctxt ctxt
        val _ = Utils.verbose_msg 3 ctxt (fn _ => "in_out_statement: L2_gets:\n " ^ Thm.string_of_thm ctxt thm)
      in
        (thm, ctxt)
      end),
    @{cterm_morph_match \<open>L2_guard ?e \<close>} phi #> (fn {e, ...} => fn ctxt => fn 
      args as {A, t0, params, s , rel_alloc,...} =>
      let
        val {e', implication_thm} = in_out_guard ctxt args e
        val thm = instantiate_thm (~1) ctxt [("e", e), ("e'", e')] L2_guard_rel_stack OF_COMP [implication_thm, rel_alloc]
        val _ = Utils.verbose_msg 3 ctxt (fn _ => "in_out_statement: L2_guard:\n " ^ Thm.string_of_thm ctxt thm)
      in
        (thm, ctxt)
      end),
    @{cterm_morph_match \<open>L2_modify (\<lambda>s. hmem_upd (heap_update ?p (?v s)) s)\<close>} phi #> (fn {p, v, ...} => fn ctxt => fn 
      args as {M, A, params, rel_alloc, return, s, modified, in_out_globals, ...} =>
        \<comment> \<open>We assume that p is a root pointer which should be the outcome of the L2-opt phase\<close>
        if is_param params p then
          if is_eliminate params p then
            let
              val ((alloc_p, modifies_p), ctxt) = ctxt 
                |> ensure_alloc A p
                ||>> ensure_modifies M p
              val {e', R, result_rel_thm, outs, needs_guard, guard_ctxt} = 
                in_out_ptr_modify ctxt (returns modified return) args p v
              val ns = map (name_hint_of params) outs
                |> HOLogic.mk_list @{typ nat} |> Thm.cterm_of guard_ctxt
              val thm = (instantiate_thm (~1) guard_ctxt [("p", p), ("v", v), ("e'", e'), ("R", R), ("ns",ns)]
                L2_modify_heap_update_rel_stack OF_COMP [result_rel_thm, rel_alloc, alloc_p, modifies_p])
                |> export_guarded guard_ctxt ctxt
              val _ = Utils.verbose_msg 3 ctxt (fn _ => "in_out_statement: L2_modify (eliminate):\n " ^ Thm.string_of_thm ctxt thm)
            in
              (thm, ctxt)
            end
          else
            let
              val (((disjoint_alloc_p, disjoint_stack_free_p), modifies_p), ctxt) = ctxt
                |> ensure_disjoint_alloc A p
                ||>> ensure_disjoint_stack_free s p
                ||>> ensure_modifies M p
              val {e'=v', Q, result_rel_thm, outs, unit_seed, ...} = in_out_expression true ctxt (return_none o snd) args v
              val thm = instantiate_thm (~1) ctxt [("p", p), ("v", v), ("v'", v')] L2_modify_keep_heap_update_rel_stack OF
                [result_rel_thm, rel_alloc, disjoint_alloc_p, disjoint_stack_free_p, modifies_p]
              val _ = Utils.verbose_msg 3 ctxt (fn _ => "in_out_statement: L2_modify (keep):\n " ^ Thm.string_of_thm ctxt thm)
            in
              (thm, ctxt)
            end
        else
          let
            val _ = in_out_globals orelse error ("L2_modify: case not yet implemented (maybe missing in_out_globals option?)")
            val global_grd = ptr_span_contained ctxt G p
            val {e'=v', Q, result_rel_thm, ...} = in_out_expression true ctxt (return_none o snd) args v
            val thm0 = instantiate_thm (~1) ctxt [("G", global_grd), ("p", p), ("v", v), ("v'", v')] L2_modify_keep_heap_update_rel_stack_guarded OF
                [result_rel_thm, rel_alloc]
            val simp_ctxt = mk_simp {silent = !sd2, M = M} ctxt
            val thm = Utils.solve_sideconditions ctxt thm0 (ALLGOALS (asm_full_simp_tac simp_ctxt))
            val globals_thm0 = instantiate_thm (~1) ctxt [("M2", G)] refines_rel_stack_extend_modifies OF [thm]
            val globals_thm = Utils.solve_sideconditions ctxt globals_thm0 (ALLGOALS (asm_full_simp_tac simp_ctxt))
            val _ = Utils.verbose_msg 3 ctxt (fn _ => "in_out_statement: L2_modify (globals):\n " ^ Thm.string_of_thm ctxt globals_thm)
          in 
            (globals_thm, ctxt)
          end),
    @{cterm_morph_match \<open>L2_modify (?global_upd)\<close>} phi #> (fn {global_upd, ct_, ...} => fn ctxt => fn 
        args as {M, A, params, rel_alloc, return, s, modified, ...} =>
        let
          val (glob_field_upd, v::_) = Utils.beta_applies [s] global_upd |> Utils.strip_comb_cterm
          val {v, ...} = @{cterm_match \<open>\<lambda>_. ?v\<close>} v 
          val v = Thm.lambda_name ("s", s) v
          val {e' = v', Q, result_rel_thm, outs, unit_seed, ...} = in_out_expression true ctxt (return_none o snd) args v
          val t_eq = instantiate_thm (~1) ctxt [] rel_alloc_fold_frame OF [rel_alloc]
          val result_rel_thm = result_rel_thm |> Local_Defs.unfold ctxt [t_eq]
          val thm = get_spec ctxt (Thm.term_of glob_field_upd) |> check_vars
          val thm = instantiate_thm (~1) ctxt [("v", v), ("v'", v')] thm OF 
               [rel_alloc, result_rel_thm]
          val _ = Utils.verbose_msg 3 ctxt (fn _ => "in_out_statement: L2_modify (global):\n " ^ Thm.string_of_thm ctxt thm)
        in 
           (thm, ctxt)
        end),
    @{cterm_morph_match \<open>L2_throw ?c ?ns\<close>} phi #> (fn {c, ns, ct_,  ...} => fn ctxt => fn 
        args as {modified, try_modified, rel_alloc, params, ...} =>
        let
          val {L, result_rel_thm, outs, unit_seed, ...} = in_out_exn ctxt {exit_unreachable = false, seed_rel_opt = NONE} args c
          val ns' = mk_name_hints ctxt unit_seed params outs ns
          val thm = instantiate_thm (~1) ctxt [("L", L), ("ns", ns), ("ns'", ns')] L2_throw_rel_stack OF [result_rel_thm, rel_alloc]
          val _ = Utils.verbose_msg 3 ctxt (fn _ => "in_out_statement: L2_throw:\n " ^ Thm.string_of_thm ctxt thm)
        in
          (thm, ctxt)
        end),
    @{cterm_morph_match \<open>L2_try ?f\<close>} phi #> (fn {f, ...} => fn ctxt => fn 
        args as {rel_alloc, return, ...} =>
        let
          val args' = args 
            |> map_try_modified (cons (#modified args, return))
            |> map_modified (K [])
          val (f_thm, ctxt) = in_out_statement () f ctxt args'
          fun inst_rule f_thm =
            let 
              val {L, R,  ...} = f_thm |> Thm.cconcl_of |> dest_refines
              val {R', ... } = @{cterm_match \<open>rel_sum_stack ?L ?R'\<close>} L
              val thm = L2_try_rule ctxt R R' OF [rel_alloc, f_thm]
            in thm end
          val thm = 
            case try inst_rule f_thm of 
              SOME thm => thm
            | NONE =>
               let
                 (* Exn (Inr ...) might overapproximate result tuples also with unmodified
                    stack variables. We adjust Result _ to match this within f and then
                    remove the unnecessary components again after the L2_try. Note that
                    L2_Exception_Rewrite.project_used_components_conv removes unnecessary clutter
                    in the postprocessing step.
                  *)
                 val f_thm1 = adjust_result true ctxt args f_thm
                 val try_thm = inst_rule f_thm1 
                 val try_thm1 = adjust_result false ctxt args try_thm
               in
                  try_thm1
               end;
          val _ = Utils.verbose_msg 3 ctxt (fn _ => "in_out_statement: L2_try:\n " ^ Thm.string_of_thm ctxt thm)
        in
          (thm, ctxt)
        end),
    @{cterm_morph_match \<open>L2_spec ?r\<close>} phi #> (fn {r, ...} => fn ctxt => fn 
        args as {rel_alloc, return, ...} =>
        let
          val thm = instantiate_thm (~1) ctxt [("r", r)] L2_spec_rel_stack_heap_agnostic OF [rel_alloc]
          val _ = Utils.verbose_msg 5 ctxt (fn _ => "in_out_statement: L2_spec (thm) \n " ^ Thm.string_of_thm ctxt thm)
          val thm = Utils.solve_sideconditions ctxt thm (
                ALLGOALS (Record.split_simp_tac ctxt [] (K ~1) THEN_ALL_NEW
                  clarsimp_tac (ctxt addsimps @{thms mex_def meq_def})))
          val _ = Utils.verbose_msg 3 ctxt (fn _ => "in_out_statement: L2_spec:\n " ^ Thm.string_of_thm ctxt thm)
        in
          (thm, ctxt)
        end),
    @{cterm_morph_match \<open>L2_assume ?f\<close>} phi #> (fn {f, ...} => fn ctxt => fn 
        args as {rel_alloc, return, ...} =>
        let
          val thm = instantiate_thm (~1) ctxt [("f", f)] L2_assume_rel_stack_heap_agnostic OF [rel_alloc]
          val _ = Utils.verbose_msg 5 ctxt (fn _ => "in_out_statement: L2_assume (thm) \n " ^ Thm.string_of_thm ctxt thm)
          val thm = Utils.solve_sideconditions ctxt thm (
                ALLGOALS (Record.split_simp_tac ctxt [] (K ~1) THEN_ALL_NEW
                  clarsimp_tac (ctxt addsimps @{thms mex_def meq_def})))
          val _ = Utils.verbose_msg 3 ctxt (fn _ => "in_out_statement: L2_assume:\n " ^ Thm.string_of_thm ctxt thm)
        in
          (thm, ctxt)
        end),
    @{cterm_morph_match \<open>L2_call ?f ?emb ?ns\<close>} phi #> (fn {f, emb, ns, ...} => fn ctxt => fn 
        args as {prog_info, params_of, rel_alloc, M, A, params, s, t, t0, addrs_fix_ctxt, params_ctxt, 
          try_modified, modified, return,...} =>
        let
          val f_thm = get_spec ctxt (Thm.term_of f)
          val (f, f_args) = Utils.strip_comb_cterm f
          val {f = f_spec, A = A_var, s = s_var, t = t_var, t0 = t0_var, ...} = f_thm |> Thm.cconcl_of |> dest_refines
          val [M_var] = Thm.cprems_of f_thm |> map_filter (dest_rel_alloc) |> map (#M)
          val [A_name, s_name, t_name, t0_name, M_name] = map (fst o dest_Var o Thm.term_of) [A_var, s_var, t_var, t0_var, M_var]
          val orig_resT = f_spec |> Thm.typ_of_cterm |> body_type |> AutoCorresData.dest_exn_monad_result_type |> #resT
          val f_arg_vars = Utils.strip_comb_cterm f_spec |> snd |> map (fst o dest_Var o Thm.term_of)
          val f_thm_call = Drule.infer_instantiate ctxt (f_arg_vars ~~ f_args) f_thm
          val _ = Utils.verbose_msg 5 ctxt (fn _ => "f_thm_call (0): " ^ Thm.string_of_thm ctxt f_thm_call)
          val {L, R, M = f_M, ...} = f_thm_call |> Thm.cconcl_of |> dest_refines
          val modifies = ptrs_of_set f_M
          val ptr_params = maps ptr_param params
          val nonglobal_modifies =  (filter (member cterm_eq ptr_params) (map croot_ptr modifies))
          val (_, ctxt) =  ctxt |> fold_map (ensure_modifies M) nonglobal_modifies

          val stacked_outs = dest_stack_rel R
          val is_bottom_L = is_bottom_stack_rel L
          val _ = @{assert} (is_bottom_L orelse forall cterm_eq ((dest_stack_rel (dest_rel_exit_rel L)) ~~ stacked_outs))
          val lenses = map (ptr_to_lense ctxt) stacked_outs
          val lense_field_lvalue_eqs = (map #eq (filter_out #trivial_eq lenses))
          val all_roots = forall #trivial lenses
          val grds = lenses |> map #grd |> filter_out trivial_guard
          val (elim_lenses_tagged, keep_lenses_tagged) = Utils.split_filter (is_eliminate params o #root o snd) (tag_list 0 lenses)
          val keep_lenses = map snd keep_lenses_tagged
          val elim_lenses = map snd elim_lenses_tagged
          val shuffled_lenses = keep_lenses_tagged @ elim_lenses_tagged
          val _ = Utils.verbose_msg 6 ctxt (fn _ => "keep_lenses: " ^ @{make_string} keep_lenses)
          val _ = Utils.verbose_msg 6 ctxt (fn _ => "elim_lenses: " ^ @{make_string} elim_lenses)
          val _ = Utils.verbose_msg 6 ctxt (fn _ => "stacked_outs: " ^ string_of_cterms ctxt stacked_outs)
          val _ = Utils.verbose_msg 6 ctxt (fn _ => "grds: " ^ string_of_cterms ctxt grds)
          val permutations = map fst shuffled_lenses |> tag_list 0
          val unshuffled = permutations |> forall (op =)
          fun perm i = the_default i (AList.lookup (op =) permutations i)

          val P = set_of_ptrs ctxt (map #ptr keep_lenses)
          val A_f = \<^infer_instantiate>\<open>P = P and A = A in cterm \<open>P \<union> A\<close>\<close> ctxt

          val f_thm_call = Drule.infer_instantiate ctxt [(A_name, A_f), (M_name, f_M)] f_thm_call
          val _ = Utils.verbose_msg 5 ctxt (fn _ => "f_thm_call (1): " ^ Thm.string_of_thm ctxt f_thm_call)
          val ns' = mk_name_hints ctxt (orig_resT = @{typ unit}) params (map croot_ptr stacked_outs) ns
          val ns_exit' = mk_name_hints_call_exit ctxt params (map croot_ptr stacked_outs)

          val (f_thm_call, ns', ns_exit') = if unshuffled then (f_thm_call, ns', ns_exit') else
            let
              val shuffled_cptrs = map (#ptr o snd) shuffled_lenses
              val shuffled_ptrs = map Thm.term_of shuffled_cptrs
              val (R', _) = stack_rel ctxt orig_resT shuffled_ptrs |> apfst (Thm.cterm_of ctxt)
              val (L', _) = stack_rel ctxt @{typ exit_status} shuffled_ptrs |> apfst (Thm.cterm_of ctxt)
              val value_type = Thm.typ_of_cterm #> derefT
              val Ts = map value_type shuffled_cptrs
              val Ts_exit = Ts @ [@{typ exit_status}]
              val shuffle_return = shuffle ctxt perm Ts
              val shuffle_exit = shuffle ctxt perm Ts_exit
              val ns_shuffle = shuffle_list perm ns'
              val ns_exit_shuffle = shuffle_list perm ns_exit'
              val rule = 
                if is_bottom_L then 
                  instantiate_thm (~1) ctxt  
                    [("R'", R'), ("shuffle", shuffle_return), ("ns", ns_shuffle)] 
                    refines_rel_stack_shuffle_no_exit  
                else
                  instantiate_thm (~1) ctxt  
                    [("R'", R'), ("L'", L'), ("shuffle", shuffle_return), ("shuffle_exit", shuffle_exit), 
                      ("ns", ns_shuffle), ("ns_exit", ns_exit_shuffle)] 
                    refines_rel_stack_shuffle_both 
               val simp_ctxt = ctxt addsimps @{thms rel_push_def rel_singleton_stack_def split_tupled_all}
               val d = !d2
               val thm = Utils.check_solve_sideconditions (K true) ctxt (rule OF [f_thm_call]) (
                 AutoCorresUtil.WITH_NSUBGOALS (fn n => 
                   dprint_tac d ctxt ("shuffle 0: " ^ @{make_string} n) THEN
                   SOLVED' (asm_full_simp_tac simp_ctxt) n THEN
                   dprint_tac d ctxt "shuffle 1" THEN
                   (if is_bottom_L then all_tac
                    else SOLVED' (asm_full_simp_tac simp_ctxt) (n - 1)) THEN
                   dprint_tac d ctxt "shuffle 2"))
               val _ = Utils.verbose_msg 5 ctxt (fn _ => "f_thm_shuffled: " ^ Thm.string_of_thm ctxt thm)
            in
              (thm, ns_shuffle, ns_exit_shuffle)
            end

          val {emb_core, ...} = @{cterm_match \<open>(?emb_core \<circ> the_Nonlocal)\<close>} (decompose_funs ctxt emb)
          val emb_core_unfolded = emb_core |> Simplifier.rewrite ((Simplifier.clear_simpset ctxt) addsimps @{thms comp_def})
               |> Thm.rhs_of


          val canonical =
            let
              val canonical_ctxt = Simplifier.clear_simpset ctxt
                   addsimps @{thms L2_call_canonical_convs fst_conv snd_conv Un_empty_left Un_empty_right} @ 
                     [override_heap_on_empty]
                   addsimprocs [@{simproc ETA_TUPLED}]
            in Simplifier.simplify canonical_ctxt end

          val f_name = f |> Thm.term_of |> dest_Const |> fst |> Long_Name.base_name |>
            ProgramInfo.get_dest_fun_name prog_info FunctionInfo.L2 ""
          val f_params = params_of f_name NONE
          val f_args_kind = map2 (fn x => fn (_, (kind, _)) => (x, kind)) f_args f_params
            |> filter_out (fn (_, Other) => true | _ => false) 
          val global_args = f_args_kind |> filter_out (fn (x, _) => member cterm_eq ptr_params (croot_ptr x))
          val _ =  Utils.verbose_msg 6 ctxt (fn _ => "global_args: " ^ @{make_string} global_args)

          val global_grds = (global_args |> map (ptr_span_contained ctxt G o fst))
          val globals = not (null global_grds)

          val global_grds1 = global_grds @
            (if not globals orelse length global_args <= 1 then [] else [distinct_spans (map fst global_args) ctxt])

          val alloc_assms = Named_Rules.get ctxt @{named_rules alloc_assms}
          val modifies_assms = Named_Rules.get ctxt @{named_rules modifies_assms}
          val disjoint_alloc = Named_Rules.get ctxt @{named_rules disjoint_alloc}
          val disjoint_stack_free = Named_Rules.get ctxt @{named_rules disjoint_stack_free}
          val stack_ptr = Named_Rules.get ctxt @{named_rules stack_ptr}

          val d = !d3
          val _ =
            if d then
              let
                val _ = tracing ("alloc_assms: " ^ string_of_thms ctxt alloc_assms)
                val _ = tracing ("modifies_assms: " ^ string_of_thms ctxt modifies_assms)
                val _ = tracing ("disjoint_alloc: " ^ string_of_thms ctxt disjoint_alloc)
                val _ = tracing ("disjoint_stack_free: " ^ string_of_thms ctxt disjoint_stack_free)
              in () end
            else ()

          val bare_rule =
            (case is_bottom_L of
               false => L2_call_rel_stack_bare
             | true  => L2_call_rel_stack_bare_retype_unreachable_exit)

          val bare_insts = [("ns", ns'), ("ns_exit", ns_exit'), ("P", conjs_cterm (grds @ global_grds1))]

          val bare_thm = instantiate_thm (~1) ctxt bare_insts bare_rule OF [f_thm_call]
          val _ = Utils.verbose_msg 5 ctxt (fn _ => "bare_thm: " ^ Thm.string_of_thm ctxt bare_thm)

          val heap_thm0 = if null keep_lenses then canonical bare_thm else
            let
              val guard_lenses = filter_out (cguard_holds ctxt o #root) keep_lenses
              (* FIXME: isn't this guard handling redundant. We might go for canonical solution to add all necessary guards
                 already in bare_thm and then propagate accordingly... *)
              val ({grd, grds}, guard_ctxt) = assume_grds (map (cguard_bool o #root) guard_lenses) ctxt
              val maxidx = Thm.maxidx_of bare_thm
              val rule = instantiate_thm maxidx ctxt [("P", P)] refines_rel_stack_override_heap_on_exit_guarded OF [rel_alloc]
              (* FIXME: same as pop simpset ? *)
              val simp_ctxt = mk_simp {silent = !sd3, M = M} guard_ctxt
                    addsimps (grds @ [rel_alloc_modifies_antimono]) @ @{thms 
                      c_guard_field_lvalue
                      field_lvalue_ptr_span_root_contained
                      field_lvalue_ptr_span_trans
                      root_disjoint_field_lvalue_disjoint1 root_disjoint_field_lvalue_disjoint2
                      Un_upper1 Un_upper2 subset_unI1 subset_unI2
                      }
              val d = !d4
              val thm = Utils.solve_sideconditions guard_ctxt rule (
                dprint_tac d ctxt "override_heap (0)" THEN
                resolve_tac ctxt [bare_thm] 1 THEN
                dprint_tac d ctxt "override_heap (1)" THEN
                ALLGOALS (timeit_tac' "override_heap" simp_ctxt (sidecondition_simp_tac simp_ctxt)) THEN
                dprint_tac d ctxt "override_heap (2)" 
               )
              val [thm] = Proof_Context.export guard_ctxt ctxt [thm]
              val thm = if null guard_lenses then thm else @{thm refines_L2_guard_right} OF_COMP [thm]
            in
              canonical thm
            end
          val _ = Utils.verbose_msg 5 ctxt (fn _ => "heap_thm0: " ^ Thm.string_of_thm ctxt heap_thm0)

          fun pop_to_heap (keep_lense as {ptr,...}) (thm, (ns', ns_exit')) =
            let
              val singleton = thm |> Thm.cconcl_of |> dest_refines |> (fn {R, ...} => is_singleton R)
              val ns'' = ctl ns'
              val ns_exit'' = ctl ns_exit'
              val rule = refines_rel_stack_pop_heap {exit= not is_bottom_L, singleton = singleton}
              val maxidx = Thm.maxidx_of thm
              val rule = unchecked_instantiate_thm maxidx ctxt [("ns", ns''), ("ns_exit", ns_exit'')] rule OF [rel_alloc]
              val simp_ctxt = mk_simp {silent = !sd4, M = M} ctxt
                    addsimps [rel_alloc_modifies_antimono] @ @{thms 
                      field_lvalue_ptr_span_root_contained
                      field_lvalue_ptr_span_trans 
                      root_disjoint_field_lvalue_disjoint1 root_disjoint_field_lvalue_disjoint2
                      }
              val d = !d5
              val thm = Utils.solve_sideconditions ctxt rule (
                dprint_tac d ctxt "POP (0)" THEN
                (resolve_tac ctxt [thm] 1 ORELSE 
                  (resolve_tac ctxt [refines_rel_stack_override_heap_emptyI] 1 THEN
                   resolve_tac ctxt [thm] 1)) THEN
                dprint_tac d ctxt "POP (1)" THEN
                ALLGOALS (asm_full_simp_tac simp_ctxt) THEN
                dprint_tac d ctxt "POP (2)" 
               )
            in
              (canonical thm, (ns'', ns_exit''))
            end
          val (heap_thm, (ns'', ns_exit'')) = (heap_thm0, (ns', ns_exit')) |> fold pop_to_heap keep_lenses
          val _ = Utils.verbose_msg 5 ctxt (fn _ => "heap_thm: " ^ Thm.string_of_thm ctxt heap_thm)

          val h_val_unfolds = Named_Theorems.get ctxt @{named_theorems h_val_unfold}
          val embellish_simp_ctxt = mk_simp {silent = !sd6, M = M} ctxt delsimps @{thms inter_commute}
                     addsimps (Named_Theorems.get ctxt @{named_theorems rel_stack_simps}) @
                       @{thms split_paired_all} @
                       h_val_unfolds @ 
                       lense_field_lvalue_eqs @
                       rel_alloc_stack_free_disjoint_field_lvalue @
                       @{thms 
                           field_lvalue_ptr_span_root_contained 
                           field_lvalue_ptr_span_trans 
                           field_lvalue_disjoint_fields_same_root

                           array_index_eq
                           index_fupdate_split
                           heap_access_Array_element''
                           array_ptr_index_field_lvalue_conv}

          val embellished_exit_thm = if is_bottom_L then heap_thm else
            let
              val {g, ...}  = heap_thm |> Thm.cconcl_of |> dest_refines
              val {prj, ...} = dest_canonical_call g
              val outs = map (out_param return_outs) params |> flat
              val xT = range_type (Thm.typ_of_cterm prj)
              val xTs = HOLogic.strip_tupleT xT
              val exitT = List.last xTs
              val arity = length xTs
              val ([x], ctxt') = Utils.fix_variant_cfrees [("x", xT)] ctxt
              val xt = Thm.term_of x
              val x_vals = tag_list 1 stacked_outs 
                |> map (fn (i, p) => (p, tuple_prj_from_pointers ctxt exitT stacked_outs i))
              val exit_val = Thm.cterm_of ctxt (Tuple_Tools.mk_sel' xTs xt arity)
              val ns_exit = mk_name_hints_call_exit ctxt params outs
              fun mk_upd_val p pvals = 
                let
                  val p_lenses = map_filter (fn l as {ptr, ...} => 
                         Option.map (fn sel => (l, sel)) (AList.lookup cterm_eq pvals ptr)) elim_lenses
                  val (upd, eqs) = upd_select_same_root (K true) phi ctxt s p_lenses
                  val v = Utils.beta_applies [x] upd
                in
                  v
                end
              fun mk_val p = 
                    (case filter (fn (q, _) => cterm_eq (p, croot_ptr q)) x_vals  of
                      [] => h_val phi ctxt s p 
                     | ps => mk_upd_val p ps)
              val emb = map mk_val outs @ [exit_val] |> tuple |> Thm.lambda_name ("x", x)

              val L' = stack_rel ctxt exitT (map Thm.term_of outs) |> fst |> Thm.cterm_of ctxt
              val maxidx = Thm.maxidx_of heap_thm
              val thm = instantiate_thm maxidx ctxt [("prj", prj), ("emb", emb), ("L'", L'), ("ns_exit", ns_exit)] 
                    L2_call_rel_stack_embellish_exit OF [rel_alloc, heap_thm]

              val d = !d6
              val thm = Utils.check_solve_sideconditions (K true) ctxt thm (AutoCorresUtil.WITH_NSUBGOALS (fn n =>
                   SOLVED' (asm_full_simp_tac embellish_simp_ctxt THEN' (K (dprint_tac d ctxt "embellish (1)"))) n THEN 
                   SOLVED' (asm_full_simp_tac embellish_simp_ctxt THEN' (K (dprint_tac d ctxt "embellish (2)")) ) (n - 1)))
            in
              thm
            end handle Early_Exit => heap_thm
          val _ = Utils.verbose_msg 5 ctxt (fn _ => "embellished_exit_thm: " ^ Thm.string_of_thm ctxt embellished_exit_thm)



          val (L, L', result_rel_thm, emb') =
            let
               val {L, ...} = embellished_exit_thm |> Thm.cconcl_of |> dest_refines
               val ([xT], emb_xT) = strip_typ_ctyp ctxt (Thm.ctyp_of_cterm emb_core_unfolded)      
               val ([x], ctxt') = Utils.fix_variant_cfrees [("x", Thm.typ_of xT)] ctxt
               val {L = L', result_rel_thm, seed_rel = L, ...} = 
                 in_out_exn ctxt' {exit_unreachable = is_bottom_L, seed_rel_opt = SOME (dest_rel_exit_rel L)} args (Utils.beta_applies [x] emb_core_unfolded)
               val [result_rel_thm] = Variable.export ctxt' addrs_fix_ctxt [result_rel_thm]
               val emb' = result_rel_thm |> Thm.cconcl_of |> emb'_from_rel_sum_stack addrs_fix_ctxt
            in
              (L, L', result_rel_thm, emb')
            end
          val globals_subset_trans1 = instantiate_thm (~1) ctxt [("Y", M)] globals_subset_trans
          val simp_ctxt = ctxt 
               delsimps (Named_Theorems.get ctxt @{named_theorems size_simps} @ @{thms ptr_val_ptr_add_simps})
               addsimps ([rel_alloc, rel_alloc_modifies_antimono OF [rel_alloc]] @ alloc_assms @ modifies_assms @ 
                 disjoint_alloc @ disjoint_stack_free @ stack_ptr @
                 [globals_subset_trans1, globals_disjoint_subset] @
                 @{thms c_guard_field_lvalue
                   field_lvalue_ptr_span_root_contained
                   field_lvalue_ptr_span_trans
                   field_lvalue_disjoint_fields_same_root
                   subset_union_left subset_union_right})

          val maxidx = Thm.maxidx_of embellished_exit_thm
          val nest_exit_thm = instantiate_thm maxidx ctxt 
                [("ns", ns), ("emb", emb_core), ("emb'", emb'), ("L", L), ("L'", L'), 
                 ("s", s), ("t", t), ("t\<^sub>0", t0)] 
                L2_call_rel_stack_nest_exit_guarded
            |> Local_Defs.unfold ctxt @{thms comp_def}

          val _ = Utils.verbose_msg 5 ctxt (fn _ => "nest_exit_thm (0): " ^ Thm.string_of_thm ctxt nest_exit_thm)
          val L_simp_ctxt = ctxt addsimps
                @{thms split_paired_all} @
                (Named_Theorems.get ctxt @{named_theorems rel_stack_simps})

          val d = !d7
          val nest_exit_thm = Utils.solve_sideconditions ctxt nest_exit_thm (
                      dprint_tac d  ctxt "nest_exit_thm_tac (0)" THEN
                      resolve_tac ctxt [embellished_exit_thm] 1 THEN AutoCorresUtil.WITH_NSUBGOALS (fn n =>
                      dprint_tac d  ctxt "nest_exit_thm_tac (1)" THEN
                      (SOLVED' (
                         asm_full_simp_tac L_simp_ctxt THEN_ALL_NEW (
                         (K (dprint_tac d ctxt "nest_exit_thm_tac (2)")) THEN' 
                         resolve_tac ctxt [result_rel_thm] THEN' 
                         asm_full_simp_tac ctxt THEN' 
                         (K (dprint_tac d ctxt "nest_exit_thm_tac (3)")))) n) THEN
                      dprint_tac d ctxt "nest_exit_thm_tac (4)" THEN
                      ALLGOALS (asm_full_simp_tac simp_ctxt) THEN
                      dprint_tac d ctxt "nest_exit_thm_tac (5)"))
          val _ = Utils.verbose_msg 5 ctxt (fn _ => "nest_exit_thm (1): " ^ Thm.string_of_thm ctxt nest_exit_thm)

          val modifies_globals_thm =
            if globals then 
              let
                val d = !d8
                val M2 = set_of_ptrs'' ctxt G nonglobal_modifies
                val maxidx = Thm.maxidx_of nest_exit_thm
                val thm = instantiate_thm maxidx ctxt [("M2", M2)] refines_rel_stack_extend_modifies OF [nest_exit_thm]
                val thm = Utils.solve_sideconditions ctxt thm (
                  dprint_tac d ctxt "modifies_globals_thm (0)" THEN
                  ALLGOALS (asm_full_simp_tac simp_ctxt) THEN
                  dprint_tac d ctxt "modifies_globals_thm (1)")
              in thm end
            else nest_exit_thm

          val _ = Utils.verbose_msg 5 ctxt (fn _ => "modifies_globals_thm: " ^ Thm.string_of_thm ctxt modifies_globals_thm)

          val {R, M=M1, ...} = modifies_globals_thm |> Thm.cconcl_of |> dest_refines

          val root_upd_result_thm = 
            if all_roots then modifies_globals_thm
            else
              let
                val tuple_prjs = (1 upto length lenses) |> map (tuple_prj_from_pointers ctxt orig_resT stacked_outs)
                val root_lenses = (lenses ~~ tuple_prjs) |> group_by (cterm_eq o apply2 (#root o fst))
                val elim_lenses = root_lenses |> map (filter (is_eliminate params o #root o fst)) |> filter_out null
                val (upds, sel_eqs) = map (upd_select_same_root (fn ls => length ls > 1) phi ctxt s) elim_lenses |> split_list |> apsnd flat
                val result_ptrs = map (#root o fst o hd) elim_lenses 
                val resT = dest_stack_rel_typ (Thm.typ_of_cterm R) |> snd |> Thm.ctyp_of ctxt 
                val emb = map_tuple' ctxt resT upds
                val R1 = stack_rel ctxt orig_resT (map Thm.term_of result_ptrs) |> fst |> Thm.cterm_of ctxt
                val M2 = M1 |> ptrs_of_set |> map croot_ptr |> set_of_ptrs ctxt
                val maxidx = Thm.maxidx_of modifies_globals_thm
                val embed_thm = instantiate_thm maxidx ctxt [("R1", R1), ("M2", M2), ("emb",emb), ("ns", ns')] 
                  refines_rel_stack_root_upd_result OF [rel_alloc, modifies_globals_thm]
                val embed_thm = Utils.solve_sideconditions ctxt embed_thm (
                   auto_tac embellish_simp_ctxt)
                val embed_thm = embed_thm 
                  |> Simplifier.simplify (Simplifier.clear_simpset ctxt 
                       addsimps (sel_eqs @ @{thms fst_conv snd_conv})
                       addsimprocs [@{simproc ETA_TUPLED}])
              in
                embed_thm
              end
          val _ = Utils.verbose_msg 5 ctxt (fn _ => "root_upd_result_thm: " ^ Thm.string_of_thm ctxt root_upd_result_thm)

          val thm = root_upd_result_thm
            |> Simplifier.asm_full_simplify ((Simplifier.clear_simpset ctxt) 
                  addsimps @{thms L2_call_pre_final_convs})
            |> tap (fn thm => Utils.verbose_msg 6 ctxt (fn _ => "after pre_final: " ^ Thm.string_of_thm ctxt thm)) 
            |> rewrs ctxt @{thms L2_call_ETA_TUPLED1 L2_call_ETA_TUPLED2}
            |> tap (fn thm => Utils.verbose_msg 6 ctxt (fn _ => "ETA_TUPLED: " ^ Thm.string_of_thm ctxt thm)) 
            |> Simplifier.asm_full_simplify ((Simplifier.clear_simpset ctxt) 
                 addsimps @{thms L2_call_final_convs fst_conv snd_conv}  
                 addsimprocs [@{simproc ETA_TUPLED}])

          val _ = Utils.verbose_msg 5 ctxt (fn _ => "thm (0): " ^ Thm.string_of_thm ctxt thm)
          val thm = thm |> Simplifier.asm_full_simplify ((Simplifier.clear_simpset ctxt) 
                 addsimps @{thms L2_call_final_convs})
          val _ = Utils.verbose_msg 6 ctxt (fn _ => "thm (1): " ^ Thm.string_of_thm ctxt thm)
          val root_h_val_thm = root_h_val_conv ctxt (map #eq (filter_out #trivial_eq lenses)) thm
          val _ = Utils.verbose_msg 6 ctxt (fn _ => "root_h_val_thm: " ^ Thm.string_of_thm ctxt root_h_val_thm)

          val {g, ...} = root_h_val_thm |> Thm.cconcl_of |> dest_refines
          val gt = Thm.term_of g
          val keep_global_ptrs = global_args |> map_filter (fn (p, Eliminate _) => SOME p | _ => NONE)
          val keep_heap_params = filter (is_keep_non_stack params o fst) params 
            |> map fst |> append keep_global_ptrs |> map (fn p => (p, h_val phi ctxt s p))
            |> filter (fn (p, v) => exists_subterm (fn t => t = Thm.term_of v) gt)
          val bind_keep_h_val_thm = root_h_val_thm |> not (null keep_heap_params) ? (fn thm =>
            let
              val {g, ...} = strip_guard g
              val g' = Utils.lambdas_tupled (map (apfst name_of_cterm) keep_heap_params) g
              val prj = Thm.lambda_name ("s", s) (tuple (map snd keep_heap_params))
              val ns = mk_name_hints' ctxt params (map fst keep_heap_params)
              val thm = Drule.infer_instantiate ctxt 
                    [(("prj", 0), prj), (("g'", 0), g'), (("ns", 0), ns)] 
                    @{thm refines_project_guard_right} OF [thm]
              val thm = Utils.solve_sideconditions ctxt thm (
                Method.insert_tac ctxt [rel_alloc] 1 THEN 
                clarsimp_tac ((mk_simp {silent = !sd7, M = M} ctxt) 
                    addsimps [rel_alloc_def, h_val_frame_disjoint]) 1)
            in thm end)
          val _ = Utils.verbose_msg 3 ctxt (fn _ => "in_out_statement: L2_call:\n " ^ Thm.string_of_thm ctxt bind_keep_h_val_thm)
        in
          (bind_keep_h_val_thm, ctxt) 
        end),
    @{cterm_morph_match \<open>L2_seq ?f1.0 ?f2.0\<close>} phi #> (fn {f1, f2, ...} => fn ctxt => fn 
       args as {addrs_fix_ctxt, alloc_ctxt, rel_alloc, s, params, return, M, A, ...} =>
       let
         val args1 = args |> map_modified (K []) |> map_return (K Intermediate) 
         val (f1_thm, ctxt) = Utils.timeit_msg 2 ctxt (fn _ => "L2_seq f1_thm: ") (fn _ => 
           in_out_statement () f1 ctxt args1)
         val vT = Thm.typ_of_cterm f2 |> domain_type
         val {M = M1, g = g1, R = R1, ...} = dest_refines (Thm.cconcl_of f1_thm)
         val modified_ptrs = ptrs_of_set M1
         val vs = Tuple_Tools.strip_case_prod' (Thm.term_of f2) |> sanitize_names "v"
         val stack_ptrs = R1 |> dest_stack_rel
         val modified_stack_ptrs = filter (member cterm_eq modified_ptrs) stack_ptrs (* preserve order for tupling *)

         val (vs, ctxt1) = ctxt 
            |> Utils.fix_variant_cfrees vs 
         val args' = args |> map_modified (union_ptrs modified_ptrs)
         val (f2_thm, ctxt2) = in_out_statement () (tupled_applies ctxt1 vs f2) ctxt1 args'
         val ctxt = transfer_all_assms [] ctxt2 ctxt

         (* adapt output value tuple if necessary *)
         val f2_thm = adjust_result false ctxt2 args' f2_thm 
         val vs' =
           if null stack_ptrs orelse not (vT = @{typ unit}) then
             vs
           else
             []
         val (f1_thm, f2_thm) = generalise_unreachable_exit2 ctxt f1_thm f2_thm
         val {g = g2', ...} = dest_refines (Thm.cconcl_of f2_thm) 
         val g2' = abstract_vals vs' g2'
         val {g' = g2', ptr_vals} = abstract_ptr_vals ctxt2 modified_stack_ptrs s g2'
         val {g' = g2, vals= unmodified_vals} = abstract_unmodified ctxt2 modified_ptrs s params g2'
         val unmodified_ptrs = unmodified_params modified_ptrs params
         val g2_thm = Drule.mk_term g2

         val f2_thm = f2_thm
           |> Assumption.export ctxt2 addrs_fix_ctxt
           (* avoid generalising local variables aka. binds from outer statements*)
         val [f2_thm, g2_thm] = [f2_thm, g2_thm]
           |> Variable.export ctxt2 ctxt
           |> Variable.export alloc_ctxt addrs_fix_ctxt
         val g2 = g2_thm |> Drule.dest_term |> Utils.beta_applies (map (snd o snd) unmodified_vals)
         val arity_f2 = length vs
         val arity_g2 = length vs' + length modified_stack_ptrs

         val maxidx = (~1) |> fold (Integer.max o Thm.maxidx_of) [f1_thm, f2_thm]

         val R1_inst = 
           if is_Var (Thm.term_of R1) then (* Inr is unreachbale branch, assume equality *)
             \<^instantiate>\<open>'a = \<open>nth (fst (Thm.strip_type (Thm.ctyp_of_cterm R1))) 2\<close> in 
               cterm \<open>\<lambda>_::heap_mem. ((=)::'a \<Rightarrow>'a \<Rightarrow> bool)\<close>\<close> 
           else R1
         val thy_ctxt = Proof_Context.theory_of ctxt |> Proof_Context.init_global (* avoid accidental name clash when splitting rule *)
         val rule = L2_seq_rel_stack_g2_normalised
           |> apsnd (Tuple_Tools.gen_split_rule thy_ctxt [("f2", arity_f2), ("g2", arity_g2)(*, ("g2'", arity_g2)*)]) 
           |> instantiate_normalise_thm maxidx [3(*, 4*)] ctxt [("R1", R1_inst)]
         val _ = Utils.verbose_msg 4 ctxt (fn _ => "in_out_statement: L2_seq rule:\n " ^ Thm.string_of_thm ctxt (snd rule))

         val f2_curried = Utils.timeit_msg 2 ctxt (fn _ => "L2_seq f2_curried: ") (fn _ => 
           curried ctxt arity_f2 f2)

         val thm = instantiate_thm maxidx ctxt [("f2", f2_curried),  ("g2", g2)] rule 
         val thm = thm OF [rel_alloc, f1_thm]

         val simp_ctxt = mk_simp {silent = !sd8, M = M} ctxt |>
           !use_Union_Diff_conv ? (fn ctxt => ctxt
             addsimprocs [@{simproc Union_Diff_conv}] addsimps @{thms Union_assoc})
         val d = !L2_seq_debug
         val _ = if d then tracing ("f1_thm: " ^ Thm.string_of_thm ctxt f1_thm) else ()
         val _ = if d then tracing ("f2_thm: " ^ Thm.string_of_thm ctxt f2_thm) else ()

         val nf2_prems = Thm.nprems_of f2_thm

         val thm = Utils.timeit_msg 2 ctxt (fn _ => "L2_seq thm: ") (fn _ =>
           solve_sideconditions ctxt thm
               (timeit_tac "L2_seq initial" ctxt (
                 dprint_tac d ctxt "before f2_thm" THEN
                 timeit_tac' "L2_seq resolve f2_thm" ctxt
                   (resolve_refines_g_normalise (simp_ctxt addsimps @{thms split_def}) A s unmodified_ptrs f2_thm) 1 THEN
                 dprint_tac d ctxt "after f2_thm" ))

               (timeit_tac' "L2_seq terminal" ctxt (sidecondition_simp_tac (simp_ctxt addsimps @{thms split_def}))))

         val _ = Utils.verbose_msg 3 ctxt (fn _ => "in_out_statement: L2_seq:\n " ^ Thm.string_of_thm ctxt thm)
       in
         (thm, ctxt)
       end),
    @{cterm_morph_match \<open>L2_condition ?c ?f1.0 ?f2.0\<close>} phi #> (fn {c, f1, f2, ...} => fn ctxt0 => fn 
      args0 as {rel_alloc, M,  ...} =>
      let
        val {e'=c', result_rel_thm = c_eq, guard_ctxt, ...} = in_out_expression false ctxt0 (return_none o snd) args0 c
        val (f1_thm0, ctxt) = in_out_statement () f1 ctxt0 args0
        val modified_f1 = get_modifies f1_thm0
        val args1 = args0 |> map_modified (union_ptrs modified_f1)
        val modified1 = get_modified args1
        val (f2_thm0, ctxt) = in_out_statement () f2 ctxt args1
        val modified_f2 = get_modifies f2_thm0
        val modified2 = union_ptrs modified1 modified_f2
        val args2 = map_modified (K modified2) args1
        val (f1_thm1, ctxt) = 
          if eq_set cterm_eq (modified1, modified2) then 
            (f1_thm0, ctxt)
          else 
            in_out_statement () f1 ctxt args2
        val (f1_thm, f2_thm) = generalise_unreachable_exit2 ctxt f1_thm1 f2_thm0
        val (f1_thm', f2_thm') = 
          if result_stack_rel_unify ctxt f1_thm f2_thm then
            (f1_thm, f2_thm)
          else apply2 (adjust_result false ctxt args2) (f1_thm, f2_thm)

        val maxidx = (~1) |> fold (Integer.max o Thm.maxidx_of) [f1_thm', f2_thm']
        val thm = instantiate_thm maxidx ctxt [("c", c), ("c'", c')] L2_condition_rel_stack OF [rel_alloc, c_eq, f1_thm', f2_thm']
        val simp_ctxt = mk_simp {silent = !sd9, M = M} ctxt 
        val thm = Utils.solve_sideconditions ctxt thm (ALLGOALS (asm_full_simp_tac simp_ctxt))
             |> export_guarded guard_ctxt ctxt0
        val _ = Utils.verbose_msg 3 ctxt (fn _ => "in_out_statement: L2_condition:\n " ^ Thm.string_of_thm ctxt thm)
      in
        (thm, ctxt)
      end),
    @{cterm_morph_match \<open>L2_while ?c ?f ?i ?ns\<close>} phi #> (fn {c, f, i, ns, ...} => fn ctxt => fn 
      args as {rel_alloc, params, s, alloc_ctxt, addrs_fix_ctxt, M, A, ...} =>
      let
        val vars = f |> Thm.term_of |> Tuple_Tools.strip_case_prod'
        val (vs, ctxt') = Utils.fix_variant_cfrees vars ctxt
        val f_arity = length vs
        val f_app = tupled_applies ctxt' vs f
        val args = args |> map_return (K Intermediate)
        val (f_thm, ctxt') = in_out_statement () f_app ctxt' args
        val {R, f, g, M=M1, ...} = f_thm |> Thm.cconcl_of |> dest_refines
        val (ps, (_, singleton_seed)) = R |> gen_dest_stack_rel

        val (i', unit_seed) = ptr_val_tuple phi ctxt s ps i
        val ns' = mk_name_hints ctxt unit_seed params ps ns
        val g_arity = f_arity + (if null ps then 0 else (length ps - (if singleton_seed then 1 else 0)))
        val ctxt =  transfer_all_assms [] ctxt' ctxt
        val f_thm = f_thm 
          |> Assumption.export ctxt' addrs_fix_ctxt
          (* avoid generalising local variables aka. binds from outer statements *)
          |> singleton (Variable.export ctxt' ctxt)
          |> singleton (Variable.export alloc_ctxt addrs_fix_ctxt)
        val maxidx = Thm.maxidx_of f_thm

        val thy_ctxt = Proof_Context.theory_of ctxt |> Proof_Context.init_global (* avoid accidental name clash when splitting rule *)

        val c = curried ctxt f_arity c
        val {e'=c', result_rel_thm = c_result_rel, needs_guard, abs_guard,...} = in_out_expression true ctxt (return_none o snd) args (Utils.beta_applies vs c)
        val rule = if needs_guard then L2_while_rel_stack_g_normalised_guarded else L2_while_rel_stack_g_normalised

        val splitted_thm = rule
          |> apsnd (Tuple_Tools.gen_split_rule thy_ctxt 
               ((if needs_guard then [("G'", g_arity)] else []) @
               [("f", f_arity), ("g", g_arity), ("c", f_arity), ("c'", g_arity)]))
          |> recheck_vars
          |> instantiate_normalise_thm maxidx [3, 4] thy_ctxt 
                [("R", eta_contract ctxt R (* avoid simplification in conclusion of 4 *))]
          |> recheck_vars

        val _ = Utils.verbose_msg 4 ctxt (fn _ => "in_out_statement: L2_while rule:\n " ^ Thm.string_of_thm ctxt (snd splitted_thm))
        val f = abstract_vals vs f

        val vs' = if singleton_seed then fst (split_last vs) else vs
        val g = abstract_vals vs' g

        val c' = abstract_vals vs' c'
        val {g'=c', ...} = abstract_params ctxt s (filter (member cterm_eq ps o fst) params) c'

        val G' = abstract_vals vs' abs_guard
        val {g'=G', ...} = abstract_params ctxt s (filter (member cterm_eq ps o fst) params) G'

        val {g', vals} = abstract_params ctxt s (filter (member cterm_eq ps o fst) params) g (* FIXME: same as abstract_modified in Seq ? *)

        val thm = (instantiate_thm maxidx ctxt 
          ((if needs_guard then [("G'", G'), ("G", abs_guard)] else []) @    
          [("f", f),  ("g", g'), ("i", i), ("i'", i'), ("M1", M1),
           ("c",c), ("c'",c'), ("ns", ns), ("ns'", ns')]) splitted_thm OF [rel_alloc])

        val d = !d9
        val _ = if d then tracing ("f_thm: " ^ Thm.string_of_thm ctxt f_thm) else ()
        val simp_ctxt = mk_simp {silent = !sd10, M = M} ctxt delsimprocs [@{simproc case_prod_beta}]
             (* Eta expansion in unification might yield (within g)
                  \<lambda>a. case a of (x1, x2) \<Rightarrow> Inl (undefined (x1, x2)) which gets
                  \<lambda>a. Inl (undefined a) with case_prod_beta       
                  but on the other hand (\<lambda>(x1, x2). Inl (undefined (x1, x2)) is not simplified (in g')
              *)
        val modified_ptrs = ptrs_of_set M1
        val unmodified_ptrs = unmodified_params modified_ptrs params
        val thm = Utils.solve_sideconditions ctxt thm (
              dprint_tac d ctxt "before R_i" THEN
              REPEAT1 (resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems rel_stack_intros}) 1) THEN  
              dprint_tac d ctxt "before f_thm: " THEN
              timeit_tac' "while f_thm: " ctxt (resolve_refines_g_normalise simp_ctxt A s unmodified_ptrs f_thm) 1 THEN
              dprint_tac d ctxt "after f_thm: " THEN 
              ALLGOALS (asm_full_simp_tac simp_ctxt) THEN
              dprint_tac d ctxt "after simp: " )
        val _ = Utils.verbose_msg 3 ctxt (fn _ => "in_out_statement: L2_while:\n " ^ Thm.string_of_thm ctxt thm)
      in
        (thm, ctxt)
      end),
    @{cterm_morph_match \<open>with_fresh_stack_ptr (Suc 0) ?I (L2_VARS ?f ?ns)\<close>} phi #> (fn {I, f, ns, ...} => fn ctxt => fn 
       args as {A, M, params = params0, s, t0, t, addrs_fix_ctxt, params_ctxt, in_out_globals,...} =>
       let
         val p_name = f |> Thm.term_of |> (fn (Abs (p, _, _)) => p | _ => "p")
         val pT = f |> Thm.typ_of_cterm |> domain_type
         val (_, locals_ctxt) = params_ctxt 
           |> ensure_fixed f
         val ([p], params_ctxt') = locals_ctxt
           |> Utils.fix_variant_cfrees [(p_name, pT)]
         val f_app = Utils.beta_applies [p] f
         val eliminate_ptr = passed (check_subterms_open (check_in_out params_ctxt' [Thm.term_of p]) (Thm.term_of f_app))
         val _ = Utils.verbose_msg 3 ctxt (fn _ =>
                  (if eliminate_ptr then "in_out_statement: eliminate: " else "in_out_statement: keep: ") ^ string_of_cterm ctxt p)

         val hint = case Thm.term_of ns of
                      @{term_pat "[?n]"} => SOME n
                    | _ => NONE 

         val p_param = (p, (if eliminate_ptr then Eliminate Stack else Keep true, hint))
         val params = p_param :: params0
         val (([cguard],_), params_ctxt') = params_ctxt'
           |> assume_and_note' (guard_param p_param) @{attributes [simp, cguard_assms]} 
           ||>> assume_distinct (map fst (filter is_ptr_and_not_Other params))
         val ([M', A'], addrs_fix_ctxt') = Utils.fix_variant_cfrees (map dest_cFree [M, A]) params_ctxt'

         val ({t0, s, t, rel_alloc}, alloc_ctxt) = addrs_fix_ctxt' 
           |> enter_block {M = M', A = A', params = params, in_out_globals = in_out_globals}
                {t0 = dest_cFree t0, s = dest_cFree s, t = dest_cFree t} 

         val ctxt' = alloc_ctxt 
           |> transfer_all_assms [] ctxt

         val args' = args 
           |> map_alloc_ctxt (K ctxt')
           |> map_params_ctxt (K params_ctxt')
           |> map_addrs_fix_ctxt (K addrs_fix_ctxt')
           |> map_params (K params)
           |> map_cguards (cons cguard)
           |> map_t0 (K t0)
           |> map_s (K s)
           |> map_t (K t)
           |> map_rel_alloc (K rel_alloc)

         val (f_thm, ctxt'') = in_out_statement () f_app ctxt' args'
         val {g, M = M_res, R,  ... } = dest_refines (Thm.cconcl_of f_thm)
         val M1 = M_res |> ptrs_of_set |> filter_out (fn x => cterm_eq(p, x)) |> set_of_ptrs ctxt''
         val ps = dest_stack_rel R
         (* eliminate pointer from result value stack if necessary *)
         val (g, f_thm) = (g, f_thm) |> (eliminate_ptr andalso member cterm_eq ps p) ? (fn _ => 
           let
             val maxidx = Thm.maxidx_of f_thm
             val ([_, _, vT], _) = strip_type (Thm.typ_of_cterm R)
             val Ts = HOLogic.strip_tupleT vT
             val (xTs, yTs) = chop (length ps) Ts
             val prj_enc = map (fn x => not (cterm_eq (x, p))) ps
             val (Ts, prj_enc, ns, unit, seedT) = 
               if null yTs then 
                 (xTs, prj_enc, [], true, @{typ unit})
               else
                 (xTs @ [HOLogic.mk_tupleT yTs], 
                  prj_enc @ [true], 
                 [(CLocals.name_hint ctxt'' "ret'")], 
                 false, HOLogic.mk_tupleT yTs)
             val prj = mk_projection Ts prj_enc |> Thm.cterm_of ctxt''
             val ps' = filter_out (fn x => cterm_eq (x, p)) ps
             val ns' = mk_name_hints ctxt'' unit params ps'
               (Thm.cterm_of ctxt'' (HOLogic.mk_list @{typ nat} ns))
             val R' = stack_rel ctxt'' seedT (map Thm.term_of ps') |> fst |> Thm.cterm_of ctxt''
             val rule = instantiate_thm maxidx ctxt'' [("prj", prj), ("R'", R'), ("ns", ns')] refines_rel_stack_project_result 
               |> eta_tupled ctxt''
             val thm = rule OF [f_thm]
             val thm = Utils.check_solve_sideconditions check_domain_bound ctxt'' thm (
               AutoCorresUtil.WITH_NSUBGOALS (fn n =>
                 asm_full_simp_tac (ctxt'' addsimps
                   @{thms split_paired_all} @
                   (Named_Theorems.get ctxt'' @{named_theorems rel_stack_simps})) n))
             val {g, ...} = dest_refines (Thm.cconcl_of thm)
           in (g, thm) end)

         val {g', vals} = abstract_params ctxt'' s [p_param] g
         val _ = Utils.verbose_msg 5 ctxt (fn _ => "in_out_statement: with_fresh_stack_ptr g':\n " ^ string_of_cterm ctxt'' g')

         val f_thm = f_thm
           |> Assumption.export ctxt'' params_ctxt 
         val [p_var, f_thm] = [Drule.mk_term p, f_thm]
           (* avoid generalising local variables aka. binds from outer statements *)
           |> Variable.export ctxt'' locals_ctxt
           |> norm_results ctxt
         val p_var = Drule.dest_term p_var

         val _ = Utils.verbose_msg 5 ctxt (fn _ => "in_out_statement: with_fresh_stack_ptr f_thm:\n " ^ Thm.string_of_thm ctxt f_thm)

         val M_inst = \<^infer_instantiate>\<open>p = p_var and M = M in cterm \<open>ptr_span p \<union> M\<close>\<close> params_ctxt

         val A_inst = if eliminate_ptr then
                        \<^infer_instantiate>\<open>p = p_var and A = A in cterm \<open>ptr_span p \<union> A\<close>\<close> params_ctxt
                      else
                        A
         val d = !d10

             (* instantiation of p_var should be exactly the same as the exported variable *)
         val f_thm = f_thm 
           |> Drule.infer_instantiate ctxt 
                    [((name_cFree M', 0), M_inst), ((name_cFree A', 0), A_inst)]

         val I_eqs = if eliminate_ptr then [] else [#result_rel_thm (in_out_expression true ctxt (return_none o snd) args I)]
         val ctxt = transfer_modifies_assms [p] ctxt'' ctxt



         val simp_ctxt = mk_simp {silent = !sd11, M = M} ctxt
               addsimps @{thms root_ptr_valid_c_guard
                  Un_upper1 Un_upper2 subset_unI1 subset_unI2 disjoint_subset_simps} @
                  [equal_upto_disjoint_h_val]

         val maxidx = Thm.maxidx_of f_thm
         val (g', thm) = 
           if eliminate_ptr then
             Utils.beta_applies [s] I |> Match_Cterm.switch [
                @{cterm_match \<open>{[?v]}\<close>} #> (fn {v,...} => (Utils.beta_applies [v] g',
                    partial_instantiate_thm maxidx ctxt [("I", I), ("v", v)] with_fresh_stack_ptr_rel_stack_fix_initialized_g_normalised)),
                @{cterm_match \<open>UNIV\<close>} #> (fn _ => (g', with_fresh_stack_ptr_rel_stack_uninitialized_g_normalised)),
                fn _ => error "with_fresh_stack_pointer: unsupported initializer"]
           else 
             (g', keep_with_fresh_stack_ptr_rel_stack_g_normalised)

         val thm = instantiate_thm maxidx ctxt [("f", f), ("g", g'), ("ns", ns), ("M1", M1)] thm

         val nf_prems = Thm.nprems_of f_thm
         val unmodified_ptrs = unmodified_params [p] params0

         val thm =  Utils.timeit_msg 2 ctxt (fn _ => "with_fresh_stack_ptr thm: ") (fn _ => Utils.check_solve_sideconditions check_domain_bound ctxt thm (
           dprint_tac d ctxt "debug 1" THEN 
           resolve_tac ctxt [rel_alloc] 1 THEN
           dprint_tac d ctxt "debug 2" THEN 
           (if eliminate_ptr then all_tac else resolve_tac ctxt I_eqs 1) THEN
           resolve_tac ctxt [refines_widen_modifies''] 1 THEN
           dprint_tac d ctxt "debug 3" THEN 
           Method.assm_tac ctxt 1 THEN
           dprint_tac d ctxt "before f_thm" THEN
           timeit_tac' "with_fresh_stack_ptr f_thm: " ctxt
             (resolve_refines_g_normalise simp_ctxt A s unmodified_ptrs f_thm) 1 THEN
           AutoCorresUtil.WITH_NSUBGOALS (fn n =>
             dprint_tac d ctxt "after f_thm" THEN
             domain_bound_tac ctxt n THEN
             dprint_tac d ctxt "after domain_bound_tac" THEN
             ALLGOALS (timeit_tac' "with_fresh_stack_ptr final" simp_ctxt (sidecondition_simp_tac simp_ctxt)) THEN 
           dprint_tac d ctxt "end")))
         val _ = Utils.verbose_msg 3 ctxt (fn _ => "in_out_statement: with_fresh_stack_ptr:\n " ^ Thm.string_of_thm ctxt thm)
       in
         (thm, ctxt)
       end),
       fn ct => fn ctxt => fn _  => error ("in_out_statement unmatched term: " ^ string_of_cterm ctxt ct) ]

  val in_out_statement = in_out_statement ()

  fun build_context ({M, A, t0, s, t, params, in_out_globals}:(string, cterm) fixes) ctxt  = 
    let
      val ((cguards,_), params_ctxt) = ctxt |>
        assume_and_note' (map guard_param params |> flat) @{attributes [simp, cguard_assms]}
        ||>> assume_distinct (map fst (filter is_ptr_and_not_Other params))
      val ([M, A], addrs_fix_ctxt) = Utils.fix_variant_cfrees ([(M, @{typ "addr set"}), (A, @{typ "addr set"})]) params_ctxt
      val ({t0, s, t, rel_alloc}, alloc_ctxt) = addrs_fix_ctxt 
        |> enter_block {M = M, A = A, params = params, in_out_globals=in_out_globals} {t0 = (t0, sT), s = (s, sT), t = (t, sT)} 
    in
      ({params_ctxt = params_ctxt, addrs_fix_ctxt = addrs_fix_ctxt, 
        M = M, A = A, t0 = t0 , s = s, t = t, rel_alloc = rel_alloc, cguards = cguards}, alloc_ctxt)
    end


  fun mk_refines_cprop phi {closed, apply_f, might_exit, in_out_globals} ctxt f g_opt fixes_opt params =
    let
      val ({M, A, s, t, t0}, ctxt') = 
        case fixes_opt of 
          SOME {M, A, s, t, t0} => ({M=M, A=A, s=s, t=t, t0=t0}, ctxt)
        | _ =>  
           let 
             val ({M, A, s, t, t0, ...}, ctxt') = ctxt 
               |> build_context {M="M", A="A", t0="t\<^sub>0", s="s", t="t", params = params, in_out_globals=in_out_globals}
           in ({M=M, A=A, s=s, t=t, t0=t0}, ctxt') end

      val f = f |> apply_f ? Utils.applies (map fst params)
      val {exT=\<^Type>\<open>c_exntype exitT\<close>, resT, ...} = Thm.typ_of_cterm f |> body_type |> AutoCorresData.dest_exn_monad_result_type 
      val outs = map (out_param return_outs) params |> flat 
      val R = stack_rel ctxt resT (map Thm.term_of outs) |> fst |> Thm.cterm_of ctxt
      val L = stack_rel ctxt exitT (map Thm.term_of outs) |> fst |> Thm.cterm_of ctxt
      val modified_ptrs = maps (modified_param return_outs) params @ (if in_out_globals then [G] else [])
      val M_res = modified_ptrs |> set_of_ptrs ctxt'
      val (_, ctxt') = ctxt' |> fold_map (ensure_modifies M) modified_ptrs
      val exitT' =   
            stack_rel ctxt exitT (map Thm.term_of outs) |> fst |> Thm.cterm_of ctxt |> Thm.typ_of_cterm |> binder_types 
            |> (fn ts => nth ts 2) |> Thm.ctyp_of ctxt
      val concl = case g_opt of
        SOME g => 
          let
             val g = Utils.applies (map (in_param_val phi ctxt s) params |> flat |> map snd) g
          in
           if might_exit then
            \<^morph_infer_instantiate>\<open>g = g and f = f and M_res = M_res and A = A and s = s and t = t and t\<^sub>0 = t0 and 
              L = L and R = R 
              in cprop \<open>refines f g s t (rel_stack \<S> M_res A s t\<^sub>0 (rel_xval_stack (rel_exit L) R))\<close> \<close> phi ctxt'
           else
            \<^morph_infer_instantiate>\<open>g = g and f = f and M_res = M_res and A = A and s = s and t = t and t\<^sub>0 = t0 and 
              R = R and 'b = exitT'
              in cprop \<open>refines f g s t (rel_stack \<S> M_res A s t\<^sub>0 (rel_xval_stack (rel_exit (\<lambda>_ (_::'a) (_::'b). False)) R))\<close>\<close> phi ctxt'
          end
      |  NONE =>
          if might_exit then
           \<^morph_infer_instantiate>\<open>f = f and M_res = M_res and A = A and s = s and t = t and t\<^sub>0 = t0 and 
              L = L and R = R
              in cprop (schematic) \<open>refines f g s t (rel_stack \<S> M_res A s t\<^sub>0 (rel_xval_stack (rel_exit L) R))\<close> \<close> phi ctxt'
          else
           \<^morph_infer_instantiate>\<open>f = f and M_res = M_res and A = A and s = s and t = t and t\<^sub>0 = t0 and 
              R = R and 'b = exitT'
              in cprop (schematic) \<open>refines f g s t (rel_stack \<S> M_res A s t\<^sub>0 (rel_xval_stack (rel_exit (\<lambda>_ (_::'a) (_::'b). False)) R))\<close> \<close> phi ctxt'
    in
      if is_none fixes_opt then 
        (Utils.export_prop {closed=closed} ctxt' ctxt concl, ctxt)
      else 
        (concl, ctxt')
    end

  fun mk_lifted_type phi {might_exit} ctxt f params =
    let
      val ({s, ...}, ctxt') = ctxt |> build_context {M="M", A="A", t0="t\<^sub>0", s="s", t="t", params = params, in_out_globals=false}
      val f = Utils.applies (map fst params) f
      val {exT=\<^Type>\<open>c_exntype exitT\<close>, resT, stateT} = Thm.typ_of_cterm f |> body_type |> AutoCorresData.dest_exn_monad_result_type
      val inTs = map (in_param_val phi ctxt s) params |> flat |> map snd |> map Thm.typ_of_cterm
      val outs = map (out_param return_outs) params |> flat |> map Thm.term_of
      val resT' = stack_rel ctxt resT outs |> fst |> Thm.cterm_of ctxt |> Thm.typ_of_cterm |> binder_types 
          |> (fn ts => nth ts 2)
      val exitT' =   
            stack_rel ctxt exitT outs |> fst |> Thm.cterm_of ctxt |> Thm.typ_of_cterm |> binder_types 
            |> (fn ts => nth ts 2)
    in
      inTs ---> AutoCorresData.mk_l2monadT sT resT' exitT' 
    end

  fun in_out_statement_internal {might_exit:bool} ctxt (args as {name, M, A, t0, s, t, params, rel_alloc, in_out_globals, ...}:args) f =
    let
      val (thm, res_ctxt) = Utils.timeit_msg 1 ctxt (fn _ => "in_out_statement: ") (fn _ => 
        in_out_statement f ctxt args)
      val _ = Utils.verbose_msg 5 ctxt (fn _ => "in_out_statement_internal: thm (0):\n " ^ Thm.string_of_thm res_ctxt thm)

      val thm = Utils.solve_sideconditions res_ctxt thm (ALLGOALS (domain_bound_tac res_ctxt))
           (* instantiates remaining "domain_bound A ?X" with \<lambda>_. (=) or  \<lambda>_ _ _. False*)
      val _ = Utils.verbose_msg 5 ctxt (fn _ => "in_out_statement_internal: thm (1):\n " ^ Thm.string_of_thm res_ctxt thm)
        (* Make prop explicit to instantiate schematics types in g and schematics L / R *)


      fun refines_prog_conv conv = Conv.fconv_rule (Utils.remove_meta_conv (fn ctxt =>
        Utils.nth_arg_conv 2 (conv ctxt)) ctxt)

      (* Cleanup. *)
      val _ = writeln ("Simplifying (IOopt) " ^ name)
      val _ = Utils.verbose_msg 1 res_ctxt (fn _ => "IO (raw) - " ^ name ^ ": " ^ Thm.string_of_thm res_ctxt thm)
      (* HACK: we need to avoid these simps until heap_lift *)
      val cleanup_del = @{thms ptr_coerce.simps ptr_add_0_id}
      val res_ctxt = res_ctxt |> AutoCorresTrace.put_trace_info name FunctionInfo.IO FunctionInfo.PEEP;
      val thm = Utils.timeit_msg 1 res_ctxt (fn _ => "Simplification (IOopt): " ^ name) (fn _ =>
        L2Opt.cleanup_thm_tagged (res_ctxt delsimps cleanup_del) [] [] thm
        FunctionInfo.PEEP 2 false "IO")
      val _ = Utils.verbose_msg 1 res_ctxt (fn _ => "IO (IOopt) - " ^ name ^ ": " ^ Thm.string_of_thm ctxt thm)
      val _ = writeln ("Remove unused tuple components (IOprj) " ^ name)
      val thm = Utils.timeit_msg 1 res_ctxt (fn _ => "Remove unused tuple components (IOprj): " ^ name) (fn _ =>
        thm
        |> refines_prog_conv (fn ctxt => (L2_Exception_Rewrite.project_used_components_conv ctxt)))
      val _ = Utils.verbose_msg 1 res_ctxt (fn _ => "IO (IOprj) - " ^ name ^ ": " ^ Thm.string_of_thm res_ctxt thm)

      val (prop, res_ctxt) = mk_refines_cprop phi {closed=false, apply_f=false, might_exit = might_exit, in_out_globals = in_out_globals} res_ctxt f 
                   NONE (SOME {M = M, A = A, t0 = t0, s = s, t = t}) params
      val _ = Utils.verbose_msg 5 ctxt (fn _ => "in_out_statement_internal: prop:\n " ^ string_of_cterm res_ctxt prop)
      val widen_modifies = refines_widen_modifies_weaken OF [rel_alloc, thm]
      val simp_ctxt = res_ctxt
        delsimps (Named_Theorems.get res_ctxt @{named_theorems size_simps} @ @{thms ptr_val_ptr_add_simps})
        addsimps (Named_Rules.get res_ctxt @{named_rules modifies_assms})
      val thm = Goal.prove_internal res_ctxt [] prop (fn _ => 
          resolve_tac res_ctxt [widen_modifies] 1 THEN
          blast_tac res_ctxt 1 THEN
          SOLVED' (asm_full_simp_tac simp_ctxt) 1 THEN
          entail_tac ctxt @{thms rel_xval_stack_entail rel_sum_stack_entail} 1)
      val _ = Utils.verbose_msg 5 ctxt (fn _ => "in_out_statement_internal: thm (2):\n " ^ Thm.string_of_thm res_ctxt thm)
      val {g, ...} = dest_refines (Thm.cconcl_of thm)
      val {g',...} = abstract_params res_ctxt s params g
    in
      ((thm, g'), res_ctxt)
    end
in
  {build_context = build_context,
   mk_refines_cprop = mk_refines_cprop phi,
   mk_lifted_type = mk_lifted_type phi,
   in_out_expression = in_out_expression,
   in_out_guard = in_out_guard,
   in_out_statement = in_out_statement_internal,
   refines_to_IOcorres_conv = refines_to_IOcorres_conv}
end


fun mk_param ctxt fn_name param_spec (name, t) =
  let
    val hint_ctxt = ctxt |> Context.proof_map (CLocals.Data.map (CLocals.enter_scope fn_name))
    val T = fastype_of t
    val (xspec, name_hint) = 
      if is_ptrT T then
        case AList.lookup (op =) param_spec name of
          SOME FunctionInfo.Data => (Other, NONE)
        | SOME x => (Eliminate (Parameter x), SOME (CLocals.name_hint hint_ctxt name))
        | NONE => (Keep false, SOME (CLocals.name_hint hint_ctxt name)) 
      else (Other, NONE)
   val _ = Proof_Context.export
  in
    (Thm.cterm_of ctxt t, (xspec, name_hint))
  end


fun mk_params prog_info l2_infos ctxt fn_name fn_arg_terms_opt = 
  let
    val (info: FunctionInfo.function_info) = the (Symtab.lookup l2_infos fn_name)
    val args = FunctionInfo.get_args info
    val default_args = map (fn (x, (T, _)) => (x, T)) args
    val fn_arg_terms = the_default (map Free default_args) fn_arg_terms_opt
    val arg_names = args |> map fst
    val param_spec = ProgramInfo.get_fun_options prog_info fn_name |> ProgramInfo.get_in_out_parameters
    val params = map (mk_param ctxt fn_name param_spec) (arg_names ~~ fn_arg_terms)
  in params end

  
fun get_io_corres_prop ops prog_info l2_infos ctxt assume fn_name fn_free fn_arg_terms = 
  let
    val attribs = @{attributes [synthesize_rule refines_in_out]} |> map (Attrib.attribute ctxt)
    val (info: FunctionInfo.function_info) = the (Symtab.lookup l2_infos fn_name)
    val params = mk_params prog_info l2_infos ctxt fn_name (SOME fn_arg_terms)
    val f = FunctionInfo.get_const info |> Thm.cterm_of ctxt
    val csenv = ProgramInfo.get_csenv prog_info
    val might_exit = ProgramAnalysis.is_exit_reachable csenv fn_name
    val in_out_globals = ProgramInfo.get_fun_options prog_info fn_name |> ProgramInfo.get_in_out_globals
    val prop = #mk_refines_cprop ops {closed = true, apply_f = true, might_exit = might_exit, in_out_globals = in_out_globals}
          ctxt f (SOME (Thm.cterm_of ctxt fn_free)) NONE params |> fst |> Thm.term_of
  in
    ([], (prop, attribs))
  end

fun get_fn_args_def prog_info l2_infos ctxt fn_name =
  let
    val params = mk_params prog_info l2_infos ctxt fn_name NONE
    val args = map (in_arg ctxt) params |> flat |> map Thm.term_of |> map Term.dest_Free
  in
    args
  end

fun get_fn_args_prop prog_info l2_infos ctxt fn_name =
  let
    val params = mk_params prog_info l2_infos ctxt fn_name NONE
    val args = map fst params |> map Thm.term_of |> map Term.dest_Free
  in
    args
  end
                  

fun get_fn_type (ops: operations) prog_info l2_infos ctxt fn_name = 
  let
    val params = mk_params prog_info l2_infos ctxt fn_name NONE
    val info  = the (Symtab.lookup l2_infos fn_name)
    val f = FunctionInfo.get_const info |> Thm.cterm_of ctxt
    val csenv = ProgramInfo.get_csenv prog_info
    val might_exit = ProgramAnalysis.is_exit_reachable csenv fn_name
    val gT = #mk_lifted_type ops {might_exit = might_exit} ctxt f params
  in
    gT
  end

fun translate 
      (skips: FunctionInfo.skip_info)
      (base_locale_opt: string option)
      (prog_info: ProgramInfo.prog_info) 
      (parallel : bool)
      (cliques: string list list)
      (lthy: local_theory) : string list list * local_theory =
  let
    val ops = the (Data.get (NameGeneration.global_rcd_name) lthy)
    val phase = FunctionInfo.IO
    val filename = ProgramInfo.get_prog_name prog_info
    val io_function_name = ProgramInfo.get_mk_fun_name prog_info phase
    val existing_l2_infos = AutoCorresData.get_default_phase_info (Context.Proof lthy) filename (FunctionInfo.prev_phase skips phase)
    val existing_io_infos = AutoCorresData.get_default_phase_info (Context.Proof lthy) filename phase
    val conversion_start = Timing.start ();

    val get_fn_type = get_fn_type ops prog_info existing_l2_infos lthy
    val get_fn_prop = get_io_corres_prop ops prog_info existing_l2_infos
    val get_fn_args_def = get_fn_args_def prog_info existing_l2_infos lthy
    val get_fn_args_prop = get_fn_args_prop prog_info existing_l2_infos lthy

    fun convert prog_info lthy l2_infos fn_name: AutoCorresUtil.convert_result =
      let
        val f_l2_info = the (Symtab.lookup l2_infos fn_name);
        val params_of = mk_params prog_info l2_infos lthy
        val params = params_of fn_name NONE
        val in_out_globals = ProgramInfo.get_fun_options prog_info fn_name |> ProgramInfo.get_in_out_globals
        val ctxt = lthy |> Context.proof_map (CLocals.Data.map (CLocals.enter_scope fn_name))
        val (paramfixes, params_fix_ctxt) = Utils.fix_variant_cfrees (map (Term.dest_Free o Thm.term_of o fst) params) ctxt
        val f_def = FunctionInfo.get_definition f_l2_info
        val f = f_def
          |> Utils.inst_args params_fix_ctxt paramfixes |> Thm.cconcl_of |> Utils.crhs_of
        val csenv = ProgramInfo.get_csenv prog_info
        val might_exit = ProgramAnalysis.is_exit_reachable csenv fn_name
        val params = paramfixes ~~ map snd params
        val fixes = {M = "M", A = "A", t0 = "t0", s = "s", t = "t", params = params, in_out_globals=in_out_globals}
        val fn_ptr_infos = [] (* FIXME *)

        val (rec_ctxt, callee_terms) =
          AutoCorresUtil.assume_called_functions_corres params_fix_ctxt fn_ptr_infos
            (FunctionInfo.get_recursive_clique f_l2_info)
            get_fn_type
            get_fn_prop
            get_fn_args_prop
            (io_function_name "")

        val ({M, A, t0, s, t, rel_alloc, params_ctxt, addrs_fix_ctxt, cguards}, alloc_ctxt) = 
          rec_ctxt |> #build_context ops fixes


        val ((thm, g), res_ctxt) = #in_out_statement ops {might_exit=might_exit} alloc_ctxt {
          params_of = params_of, prog_info = prog_info, in_out_globals = in_out_globals,
          name = fn_name, M = M, A = A, t0 = t0, s = s, t = t, params = params, 
          cguards = cguards, rel_alloc = rel_alloc, modified = [], try_modified = [], 
          disjoint = map fst params, return = Final, 
          params_ctxt = params_ctxt, addrs_fix_ctxt = addrs_fix_ctxt, alloc_ctxt = alloc_ctxt} f (* FIXME: maybe split parameters in constant and variable portion? *)

        val args = get_fn_args_def fn_name
        val bdy = betapplys (Thm.term_of g, map Free args)
        val thm = refines_fold_f res_ctxt f_def thm
        val [thm] = Proof_Context.export res_ctxt lthy [thm]
        val rec_callees = AutoCorresUtil.get_rec_callees callee_terms bdy;
        val callee_consts =
          callee_terms |> map (fn (callee, (const, _)) => (callee, const)) |> Symtab.make;
      in
        {body = bdy,
         proof = thm,
         rec_callees = rec_callees,
         callee_consts = callee_consts,
         arg_frees = args
        }
      end

    fun define (lthy: local_theory)
        (funcs: AutoCorresUtil.convert_result Symtab.table)
        : local_theory = 
      let
        val l2_infos = AutoCorresData.get_default_phase_info (Context.Proof lthy) (ProgramInfo.get_prog_name prog_info) FunctionInfo.L2 
        val funcs' = Symtab.dest funcs |>
          map (fn result as (name, {proof, arg_frees, ...}) =>
                     (name, (AutoCorresUtil.abstract_fn_body l2_infos result,
                             proof, arg_frees)));
        val (new_thms, lthy') =
          AutoCorresUtil.gen_define_funcs
              skips
              phase prog_info I {concealed_named_theorems=false} (io_function_name "")
              get_fn_type
              get_fn_prop
              get_fn_args_def
              get_fn_args_prop
              funcs'
              lthy;
      in lthy' end; 

    val (groups, lthy) = lthy |>
       AutoCorresUtil.convert_and_define_cliques skips base_locale_opt prog_info
        phase parallel
        (convert prog_info) define cliques
  in
    (groups, lthy)
  end


end