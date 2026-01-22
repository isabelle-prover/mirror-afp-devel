(*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature FUNCTION_POINTER =
sig
  val define_progenvs_and_rewrite_defs: string -> local_theory -> local_theory
  val d1: bool Unsynchronized.ref
  val d2: bool Unsynchronized.ref
end

structure Function_Pointer: FUNCTION_POINTER =
struct
val norm_name = NameGeneration.unC_field_name #> safe_unsuffix "'"

fun extract_ptr @{term_pat "(gets (?v::'a\<Rightarrow>unit ptr))"} = SOME v
  | extract_ptr @{term_pat "(return (?v::'a\<Rightarrow>unit ptr))"} = SOME v
  | extract_ptr @{term_pat "(ogets (?v::'a\<Rightarrow>unit ptr))"} = SOME v
  | extract_ptr @{term_pat "(oreturn (?v::unit ptr))"} = SOME v
  | extract_ptr _ = NONE

fun dest_abs (t as (Abs _)) = SOME (Term.dest_abs_global t)
  | dest_abs _ = NONE

val strip_p = fst o dest_comb
fun extract_bind binds v f = 
      (case extract_ptr v of
         SOME p => let in 
           (case dest_abs f of 
              SOME (free, bdy) => let 
                 in extract_map_of_default ((free, p):: binds) bdy end
            | NONE => extract_map_of_default binds (f$p)) end
       | NONE => extract_map_of_default binds v @ extract_map_of_default binds f)

and extract_map_of_default binds (t as @{term_pat "obind ?v ?f"}) = extract_bind binds v f
  | extract_map_of_default binds (t as @{term_pat "bind ?v ?f"}) = extract_bind binds v f
  | extract_map_of_default binds (t as @{term_pat "map_of_default ?d ?xs ?p" }) =
      (
       case p of Free free =>
        let
        in
          (case AList.lookup (op =) binds free of 
             SOME v => [(strip_p t, v)]
           | NONE => [(strip_p t, p)])
        end
        | _ => [(strip_p t, p)]
      )
  | extract_map_of_default binds (t1 $ t2) = extract_map_of_default binds t1 @ extract_map_of_default binds t2
  | extract_map_of_default binds (t as (Abs _)) = extract_map_of_default binds (snd (Term.dest_abs_global t))
  | extract_map_of_default _ _ = []


val dest_index = try HOLogic.dest_nat
fun check_selector ctxt (c as (Const (sel, \<^Type>\<open>fun \<open>Type (record, [])\<close> _\<close>))) = 
      if RecursiveRecordPackage.is_field (Proof_Context.theory_of ctxt) record sel
      then Long_Name.base_name sel else error ("check_selector: not a record selector: " ^ Syntax.string_of_term ctxt c)
  | check_selector ctxt t = error ("check_selector: not a record selector: " ^ Syntax.string_of_term ctxt t)

local
  open Expr
in

type root =  {global: bool, heap: bool, name: string}
type root_path = {path: Expr.selector list, root: root}

fun root_ord ({name = n1, global = g1, heap = h1}:root, {name = n2, global = g2, heap = h2}:root) = 
  prod_ord (fast_string_ord) (prod_ord (bool_ord) (bool_ord)) ((n1, (g1, h1)), (n2, (g2, h2)))
fun root_path_ord ({root = r1, path = p1}:root_path, {root = r2, path = p2}:root_path) =
  prod_ord root_ord Expr.selectors_ord ((r1, p1), (r2, p2))

fun dest_root t = 
  case strip_comb t of 
    (head, []) => {heap=false, name = Term.term_name head, global = is_Const head}
  | (_, args) => let val p = (snd (split_last args)) in {heap=true, name = Term.term_name p, global = is_Const p} end
  
fun dest_selection (i as {ignore_array}) ctxt @{term_pat "Arrays.index ?a ?n"} = 
      let 
        val {root, path} = dest_selection i ctxt a
      in {root = root, path = path @ (if ignore_array then [] else [Index (dest_index n)])} end
  | dest_selection ignore_array  ctxt ((c as (Const _)) $ x) =
      let
        val {root, path} = dest_selection ignore_array ctxt x
      in
        {root = root, path = path @ [Field (check_selector ctxt c)] }
      end
  | dest_selection _ _ t = {root = dest_root t, path = []}

fun dest_ptr ctxt t = case
  dest_abs t of 
    SOME (_, bdy) => dest_selection {ignore_array = true} ctxt bdy
  | NONE => dest_selection {ignore_array = true} ctxt t


end


fun extract_map_of_defaults ctxt =
  let
    val ts_defs0 = Named_Theorems.get ctxt @{named_theorems ts_def}
    val ts_defs = map (Variable.import_vars ctxt) ts_defs0
    fun dest_eq thm = Thm.cconcl_of thm |> Utils.dest_eq' |> apply2 (Thm.term_of) |> apfst (Term.term_name o head_of)
    fun extract rhs = extract_map_of_default [] rhs |> map (apsnd (dest_ptr ctxt)) |> distinct (op =) |> map (apfst (Thm.cterm_of ctxt))
    val res = map (apsnd extract o dest_eq) ts_defs
  in
    res
  end


fun map_of_default_thms ctxt domain_ptrs =
  let
    val all_distinct_thm = Proof_Context.get_thm ctxt "all_distinct"
    val clique_name = space_implode "_" (map Term.term_name domain_ptrs)
    val fnptr_guard_thms = Named_Bindings.get_thms ctxt @{named_bindings fun_ptr_guards}
    val {eqs = clique_eqs, fallthrough_eqs, distinct_thm, subtree_thm = SOME subtree_thm} =
      CalculateState.gen_eqs_from_all_distinct fnptr_guard_thms all_distinct_thm domain_ptrs ctxt
  in
        ([((Binding.make (suffix "_all_distinct" clique_name, \<^here>), @{attributes [fun_ptr_distinct]}),
           [([distinct_thm], [])]),
        ((Binding.make (suffix "_subtree" clique_name, \<^here>), @{attributes [fun_ptr_subtree]}),
           [([subtree_thm], [])])],

        [((Binding.make (suffix "_lookup_eqs" clique_name, \<^here>), [@{named_bindings fun_ptr_map_of_default_eqs}]),
           clique_eqs),
        ((Binding.make (suffix "_lookup_fallthrough_eqs" clique_name, \<^here>), [@{named_bindings fun_ptr_map_of_default_fallthrough_eqs}]),
           fallthrough_eqs)])     
  end


val d1 = Unsynchronized.ref false
val d2 = Unsynchronized.ref false

fun par_map f xs = if (!d2) then map f xs else Par_List.map f xs 

fun is_undefined (@{term_pat undefined}) = true
   | is_undefined(@{term_pat None}) = true
   | is_undefined (@{term_pat "\<top>::'a::top"}) = true
   | is_undefined (@{term_pat "ofail"}) = true
   | is_undefined _ = false 

val is_undefined_fun = is_undefined o strip_abs_body
val is_undefined_rhs = Thm.concl_of #> Utils.rhs_of_eq #> is_undefined_fun

fun is_map_of_default (@{term_pat "map_of_default"}) = true
  | is_map_of_default _ = false

fun define_progenvs_and_rewrite_defs prog_name lthy =
  let
    val _ = Named_Target.is_theory lthy orelse (error "define_progenvs should be invoced on theory")
    val thy = Proof_Context.theory_of lthy
    val get_fun_name = fst
    val get_map_of_default = fst o snd
    val get_root_path = snd o snd

    fun dest_map_of_default @{term_pat "map_of_default ?d ?xs"} = {d = d, xs = xs}    
    fun dest_ptrs ct = ct |> Thm.term_of |> dest_map_of_default |> #xs  
      |> HOLogic.dest_list |> map HOLogic.dest_prod |> map fst 
  
    val fun_infos = Utils.timeit_label 2 lthy "extract function pointer environments" (fn _ => 
      extract_map_of_defaults lthy)
    val domains = map (dest_ptrs o fst) (maps snd fun_infos) |> sort_distinct (list_ord Term_Ord.fast_term_ord)

    val fun_names = map fst fun_infos
    val flat_infos = maps (fn (fun_name, infos) => (map (pair fun_name) infos)) fun_infos
    val (globals, locals) = Utils.split_filter (fn (fun_name, (map_of_default, {root = {global = true, ...}, ...})) => true | _ => false) flat_infos
    val globalss = group_by (Utils.cterm_eq o (apply2 (get_map_of_default))) globals
    val (unique_globals, ambiguous_globals) = globalss |> Utils.split_map_filter (fn [x] => SOME x | _=> NONE)
    fun string_of (Expr.Field f ) = f
      
    fun mk_binding unique_global idx_opt (fun_name, {path, root = {name, global, heap}}) =
      let
        val sfx = case idx_opt of NONE => "" | SOME idx => string_of_int idx 
        val binding0 = Binding.make (AutoCorresData.progenvN ^ sfx, \<^here>)
        val qualifiers = 
          (if unique_global andalso global then [] else [fun_name]) @
           name::map string_of path 
          |> map norm_name
        val binding = binding0 |> fold_rev (Binding.qualify false) qualifiers
      in
        binding
      end

    fun define unique_global ((fun_name, (rhs, selector)), idx_opt) lthy = 
      let
        val binding = mk_binding unique_global idx_opt (fun_name, selector)
      in 
        lthy |> Utils.define_global_const binding false (Thm.term_of rhs) [] @{attributes [\<P>_defs]}
      end

    val locals' = flat ambiguous_globals @ locals
    val grouped_locals = fun_names
      |> map (fn fun_name => (fun_name, map_filter (fn (fun_name', x) => if fun_name = fun_name' then SOME x else NONE) locals')) 

    fun tag Ps =
      let
        val Pss = sort_group_by (root_path_ord o (apply2 (snd o snd))) Ps
        fun tag' Ps = if length Ps > 1 then map_index (fn (i, p) => (p, SOME (i + 1))) Ps else map (rpair NONE) Ps
        val Ps' = maps tag' Pss
      in Ps' end

    val ((unique_global_Ps, local_Ps), lthy1) = Utils.timeit_label 2 lthy "define \<P>s" (fn _ =>  
      lthy |> AutoCorresData.in_theory_result' (fn lthy =>
      let
        val globals' = tag unique_globals
        val (unique_global_Ps, lthy1) = lthy |> fold_map (define true) globals'
        fun define_local_Ps (fun_name, Ps) lthy =
          let
            val Ps' = (map (pair fun_name) Ps) |> tag
            val (res, lthy) = lthy |> fold_map (define false) Ps'
          in ((fun_name, res), lthy) end
        val (local_Ps, lthy2) = lthy1 |> fold_map define_local_Ps grouped_locals
      in ((unique_global_Ps, local_Ps), lthy2) end))





    val unique_global_P_eqs =  map snd unique_global_Ps
    val local_P_eqs = (map snd (maps snd local_Ps))
    val _ = Utils.verbose_msg 2 lthy (fn _ => big_list_of_thms "unique_global_P_eqs:" lthy unique_global_P_eqs)
    val _ = Utils.verbose_msg 2 lthy (fn _ => big_list_of_thms "local_P_eqs:" lthy local_P_eqs)
    val all_P_eqs = unique_global_P_eqs @ local_P_eqs
    val P_consts = map fst unique_global_Ps @ (map fst (maps snd local_Ps))

    val ts_defs = Named_Theorems.get lthy1 @{named_theorems ts_def}
    fun lhs_head eq = eq |> Thm.concl_of |> Utils.lhs_of_eq |> Term.head_of
    fun fun_name eq = lhs_head eq |> Term.term_name
    fun fold_local_Ps eq = 
      let
        val name = fun_name eq
        val eqs = (case AList.lookup (op =) local_Ps name of 
          SOME term_eqs => map snd term_eqs | NONE => [])
      in
        if null eqs then eq else (Local_Defs.fold lthy1 eqs eq)
      end

    val ts_defs_global = Utils.timeit_label 2 lthy "fold global \<P>s" (fn _ => 
      ts_defs |> map (Local_Defs.fold lthy1 unique_global_P_eqs))
    val ts_defs_global_and_local = Utils.timeit_label 2 lthy "fold local \<P>s" (fn _ => 
      ts_defs_global |> map fold_local_Ps)

    fun note (old_eq, new_eq) lthy =
      let
        val const = lhs_head new_eq
        val _ = not (exists_subterm is_map_of_default (Thm.concl_of new_eq)) orelse
          error ("map_of_default was not replaced by some \<P>: " ^ Thm.string_of_thm lthy new_eq)
        val base_name = Term.term_name const
        val changed = not (Utils.can_unify_thms lthy old_eq new_eq)
        val is_fixpoint = is_some (Mutual_CCPO_Rec.lookup_info (Context.Proof lthy) const)
        val b = 
          if is_fixpoint then 
            Binding.name "simps" |> Binding.qualify true base_name
          else
            Binding.name (base_name ^ "_def")
      in
        lthy 
        |> Utils.define_lemma'' (Binding.new_pos \<^here> b)
            (@{attributes [final_defs]} @ (if changed then @{attributes [ts_def]} else [])) 
            new_eq
        |> snd
      end
    val lthy2 = Utils.timeit_label 2 lthy "note final_defs" (fn _ =>  
      lthy1 |> fold note (ts_defs ~~ ts_defs_global_and_local))
                                               
    val loc = NameGeneration.intern_globals_locale_name thy prog_name
    val lthy3 = lthy2 |> AutoCorresData.in_locale loc (fn lthy0 =>  
      let
        val lthy = Utils.timeit_label 2 lthy0 "map_of_default function pointer thms" (fn _ =>  
          let
            val (notes_data, bindings_data) = par_map (map_of_default_thms lthy0) domains |> split_list
          in
            lthy0 
            |> Local_Theory.notes (flat notes_data) |> snd
            |> fold (snd oo Named_Bindings.note) (flat bindings_data)
          end )
        val all_distinct_thm = Proof_Context.get_thm lthy "all_distinct"
        val {tree, ...} = @{cterm_match "Trueprop (all_distinct ?tree)"} (all_distinct_thm |> Thm.cprop_of)
        val all_fun_ptrs = DistinctTreeProver.dest_tree (Thm.term_of tree)
        val fun_ptr_map_of_default_eqs = Named_Bindings.get_thms lthy @{named_bindings fun_ptr_map_of_default_eqs}
        val fun_ptr_map_of_default_fallthrough_eqs = Named_Bindings.get_thms lthy @{named_bindings fun_ptr_map_of_default_fallthrough_eqs}
        val simp_ctxt = (lthy addsimps all_P_eqs @ fun_ptr_map_of_default_eqs @ fun_ptr_map_of_default_fallthrough_eqs 
             delsimps @{thms map_of_default.simps})
          |> (!d2) ? Config.put Simplifier.simp_trace true
        fun mk_fun_ptr_eq P p = 
         let
           val res = P $ p |> Thm.cterm_of simp_ctxt |> Simplifier.rewrite simp_ctxt
           val _ = if !d1 then tracing ("mk_fun_ptr_eq: " ^ Thm.string_of_thm lthy res) else ()
         in res end
        val fun_ptr_eqs = Utils.timeit_label 2 lthy "mk_fun_ptr_eq" (fn _ =>  
          par_map (fn P => par_map (mk_fun_ptr_eq P) (\<^term>\<open>NULL::unit ptr\<close> :: all_fun_ptrs)) P_consts |> flat)
        val _ = if !d1 then tracing (big_list_of_thms "fun_ptr_eqs" lthy fun_ptr_eqs) else ()
        val (undefined_fun_ptr_eqs, fun_ptr_eqs) = fun_ptr_eqs |> Utils.split_filter is_undefined_rhs
      in
         Utils.timeit_label 2 lthy "note fun_ptr_simps / fun_ptr_undefined_simps" (fn _ =>  
          lthy
          |> Named_Bindings.note ((\<^binding>\<open>\<P>_fun_ptr_simps\<close>, [@{named_bindings fun_ptr_simps}]), fun_ptr_eqs) |> snd
          |> Named_Bindings.note ((\<^binding>\<open>\<P>_fun_ptr_undefined_simps\<close>, [@{named_bindings fun_ptr_undefined_simps}]), undefined_fun_ptr_eqs) |> snd)
      end)

    val _ = Utils.verbose_msg 0 lthy (fn _ => "define_progenvs_and_rewrite_defs: Done")
  in 
    lthy3
  end

  
end