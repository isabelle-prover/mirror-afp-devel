(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* fixme: all this should work on Proof.context or local_thy, not theory *)
signature UMM_PROOFS =
sig

  val skip_umm_proofs: bool Config.T
  type T

  type csenv = ProgramAnalysis.csenv

  val umm_empty_state : T
  val umm_finalise : T -> local_theory -> local_theory

  val umm_struct_calculation : csenv ->
      ((string * ((string * typ * int Absyn.ctype * CType.attribute list) list * CType.attribute list)) * thm * thm * T * local_theory) ->
      T * local_theory

  val umm_array_calculation : typ -> int -> T -> local_theory -> T * local_theory

  val c_type_name_instantiation : string -> local_theory -> local_theory
  val c_type_instantiation : (string * ((string * typ * int Absyn.ctype * CType.attribute list) list * CType.attribute list)) -> local_theory -> ((thm * thm) * local_theory)

  val set_array_bound_mksimps: Proof.context -> Proof.context

  (* high level simproc interface to cache *)

  val field_lookup_simproc: simproc
  val type_calculations_simproc: simproc
  val typuinfo_calculations_simproc: simproc

  val is_ctype : term -> bool
  val sub_typ_solver : thm list -> solver

  val dest_fields : term -> term list
  val is_ground_typ : typ -> bool

  (* debug *)
  val typuinfo_aux_ctxt: Proof.context -> Proof.context
  val field_lookup_aux_ctxt: Proof.context -> Proof.context
  val typinfo_aux_ctxt: Proof.context -> Proof.context

end

structure UMM_Proofs : UMM_PROOFS =
struct

(* cached calculations *)

local
fun basic_case_index (n, m) = 
  case (n, m) of
    (8 , 16 ) => SOME 0
  | (8 , 32 ) => SOME 1
  | (8 , 64 ) => SOME 2
  | (8 , 128) => SOME 3
  | (16, 32 ) => SOME 4
  | (16, 64 ) => SOME 5
  | (16, 128) => SOME 6
  | (32, 64 ) => SOME 7
  | (32, 128) => SOME 8
  | (64, 128) => SOME 9
  | _ => NONE

fun lookup_basic_cases thms (n, m) = Option.map (fn n => nth thms n) (basic_case_index (n, m))

fun signed_dest_wordT \<^Type>\<open>word \<^Type>\<open>signed T\<close>\<close> = (true, Word_Lib.dest_binT T, T)
  | signed_dest_wordT \<^Type>\<open>word T\<close> = (false, Word_Lib.dest_binT T, T)

fun dest_ucast (t as @{term_pat "unsigned ?x"}) = (fastype_of x, fastype_of t)  

fun ucast_signed_up ctxt x = try dest_ucast x |> Option.mapPartial (fn (D, R) =>
  let
    val (_, n, binD) = signed_dest_wordT D
    val (_, m, binR) = signed_dest_wordT R
  in
    if n < m then 
      (case lookup_basic_cases @{thms len_of_less_basic_cases} (n, m) of
         SOME thm => SOME thm
       | NONE =>
          let
            val prop = \<^instantiate>\<open>'a = binD and 'b = binR in prop \<open>LENGTH('a::len) < LENGTH('b::len)\<close>\<close>
          in
            SOME (Goal.prove ctxt [] [] prop (fn {context, ...} => asm_full_simp_tac context 1))
          end) 
    else NONE
   end)
 
fun ucast_unsigned_up ctxt x = try dest_ucast x |> Option.mapPartial (fn (D, R) =>
  let
    val (_, n, binD) = signed_dest_wordT D
    val (_, m, binR) = signed_dest_wordT R
  in
    if n <= m then
      (case lookup_basic_cases @{thms len_of_le_basic_cases} (n, m) of
         SOME thm => SOME thm
       | NONE => 
          let
            val prop = \<^instantiate>\<open>'a = binD and 'b = binR in prop \<open>LENGTH('a::len) \<le> LENGTH('b::len)\<close>\<close>
          in
            SOME (Goal.prove ctxt [] [] prop (fn {context, ...} => asm_full_simp_tac context 1))
          end) 
    else NONE
   end)

datatype num = Numeral of int | Of_Nat of term | Symbolic of term

val dest_of_nat = \<^Const_fn>\<open>of_nat _ for n => n\<close>

fun dest_number n = 
  let 
    val (T, num) = HOLogic.dest_number n
  in (T, Numeral num) end
  handle TERM _ =>
    let val T = fastype_of n 
    in (T, the_default  (Symbolic n) (Option.map Of_Nat (try dest_of_nat n))) end

fun is_positive n thm = 
  (case Thm.prop_of thm of
     @{term_pat \<open>0 \<le>s (?x::'a::len word) \<equiv> True\<close>} => n aconv x
   | _ => false)

in
fun derive_bounds ctxt bnd_thms =
  let
    fun derive_bound bnd_thm = 
      case (Thm.prop_of bnd_thm) of
        @{term_pat "((?x::?'a::len word) < ?n) \<equiv> True"} =>
           (case ucast_unsigned_up ctxt x of
              SOME ucast_up_thm => 
                (case dest_number n of
                   (_, Numeral 1) => [@{thm ucast_unat_less_helper_numeral'(2)} OF [bnd_thm, ucast_up_thm]]
                 | (_, Numeral _) => [@{thm ucast_unat_less_helper_numeral'(1)} OF [bnd_thm, ucast_up_thm]]
                 | (_, Of_Nat _)  => [@{thm ucast_unat_less_helper'} OF [bnd_thm, ucast_up_thm]]
                 | _ => [])
            | NONE =>
                (case dest_number n of
                   (_, Numeral 1) => [@{thm unat_less_helper_numeral'(2)} OF [bnd_thm]]
                 | (_, Numeral _) => [@{thm unat_less_helper_numeral'(1)} OF [bnd_thm]]
                 | (_, Of_Nat _)  => [@{thm unat_less_helper'} OF [bnd_thm]]
                 | _ => []))

      | @{term_pat "((?x::?'a::len word) <s ?n) \<equiv> True"} => 
           (case ucast_signed_up ctxt x of
              SOME ucast_up_thm => 
                (case dest_number n of
                   (_, Numeral 1) => [@{thm ucast_unat_sless_helper_numeral'(2)} OF [bnd_thm, ucast_up_thm]]
                 | (_, Numeral _) => [@{thm ucast_unat_sless_helper_numeral'(1)} OF [bnd_thm, ucast_up_thm]]
                 | (_, Of_Nat _)  => [@{thm ucast_unat_sless_helper'} OF [bnd_thm, ucast_up_thm]]
                 | _ => [])
            | NONE =>
               (case find_first (is_positive x) bnd_thms of
                  NONE => []
                | SOME positive_thm => 
                    (case dest_number n of
                      (_, Numeral 1) => [@{thm nat_sint_less_helper_numeral'(2)} OF [bnd_thm, positive_thm]]
                    | (_, Numeral _) => [@{thm nat_sint_less_helper_numeral'(1)} OF [bnd_thm, positive_thm]]
                    | (_, Of_Nat _)  => [@{thm nat_sint_less_helper'} OF [bnd_thm, positive_thm]]
                    | _ => [])))
      | _ => []
  in
    maps derive_bound bnd_thms
  end
end

fun add_array_bound_mksimps mksimps = (fn ctxt => fn thm =>
  let 
    val thms = mksimps ctxt thm;
    val bound_thms = derive_bounds ctxt thms |> map_filter (try Simpdata.mk_eq)
    val _ = Utils.verbose_msg 5 ctxt (fn _ => if null bound_thms then "" else
      "derived bound_thms: " ^ string_of_thms ctxt bound_thms ^ 
      "\n from:\n " ^ string_of_thms ctxt thms)
  in thms @ bound_thms end
)

fun set_array_bound_mksimps ctxt =
  let
     val mksimps = Simpdata.mksimps Simpdata.mksimps_pairs
  in Simplifier.set_mksimps (add_array_bound_mksimps mksimps) ctxt end

fun is_ground_typ (Type (_, Ts)) = forall is_ground_typ Ts
  | is_ground_typ _ = false

fun is_ctype (Const (@{const_name "Pure.type"}, Type ("itself", [T]))) = is_ground_typ (TermsTypes.innermost_element_type T)
  | is_ctype _ = false

fun dest_ctype (Const (@{const_name "Pure.type"}, Type ("itself", [Type T]))) = SOME T
  | dest_ctype _ = NONE

fun first_resolve_tac ctxt thms = FIRST' (map (fn thm => resolve_tac ctxt [thm]) thms)

local
  fun check @{term_pat "Trueprop (?t \<le>\<^sub>\<tau> ?s)"} = is_ctype t andalso is_ctype s
    | check _ = false
in
fun sub_typ_solver sub_typ_simps = Simplifier.mk_solver "sub_typ_solver" (fn ctxt => SUBGOAL (fn (t, i) =>
  if check t then
    let
      val _ = Utils.verbose_msg 3 ctxt (fn _ => "sub_typ_solver invoked on: " ^ Syntax.string_of_term ctxt t)
      val signed_unsigned = @{thms sub_typ_signed_unsiged sub_typ_unsigned_signed}
      val steps = sub_typ_simps @ @{thms element_typ_subtyp_array_typ le_array_typ_intro}
    in
       SOLVED_verbose "sub_typ_solver" ctxt (
         REPEAT_ALL_NEW ( (
           first_resolve_tac ctxt (steps @ signed_unsigned)
             ORELSE'
           (resolve_tac ctxt @{thms sub_typ_trans_rev} THEN' resolve_tac ctxt steps)))
      ) i
    end
  else
    no_tac
  ))
end

val field_ti_rules = @{thms wf_fd_field_ti_mem_type [OF meta_eq_to_obj_eq]}

fun typuinfo_aux_simpset thy_ctxt =
 let
   val umm_ctxt = Context_Position.set_visible false thy_ctxt
   val simps = @{thms export_uinfo_eq_sub_typ_conv typ_uinfo_eq_sub_typ_conv}
 in
  umm_ctxt addsimps simps
  |> Context_Position.restore_visible thy_ctxt
 end

fun field_lookup_aux_simpset thy_ctxt =
 let
   val umm_ctxt = Context_Position.set_visible false thy_ctxt
   val fl_Some_simps = Named_Theorems.get umm_ctxt @{named_theorems fl_Some_simps}
   val simps = @{thms field_lookup_cons fl_update field_lookup_array
         field_lookup_offset_shift
         field_ti_def
         UMM.field_lookup_typ_uinfo_t_Some field_lookup_export_uinfo_Some
         } @
         fl_Some_simps
 in
  umm_ctxt addsimps simps delsimps @{thms replicate_0 replicate_Suc replicate_numeral}
  |> Context_Position.restore_visible thy_ctxt
 end

fun typinfo_aux_simpset thy_ctxt =
 let
   val umm_ctxt = Context_Position.set_visible false thy_ctxt
   val all_field_names_no_padding = Named_Theorems.get umm_ctxt @{named_theorems all_field_names_no_padding}
   val td_names_simps = Named_Theorems.get umm_ctxt @{named_theorems td_names_simps}
   val sub_typ_simps = Named_Theorems.get umm_ctxt @{named_theorems sub_typ_simps}
   val typ_name_simps = Named_Theorems.get umm_ctxt @{named_theorems typ_name_simps}
   val simps = @{thms
         set_field_names_no_padding_all_field_names_no_padding_conv'
         set_filter_insert  neq_td_names_eq_neq_export_uinfo export_uinfo_adjust_ti wf_fd
         set_filter_cons_image set_filter_Sup set_filter_empty adjust_ti_wf_fd_pres
         cons_image_Sup
         set_filter_image_all set_filter_image_none set_filter_union_distrib
         not_sub_typ_via_td_name nat_to_bin_string_inj pad_typ_name_def
         sub_typ_proper_conv} @
         all_field_names_no_padding @
         td_names_simps @
         typ_name_simps
 in
  umm_ctxt addsimps simps
   addSolver (sub_typ_solver sub_typ_simps)
  |> Context_Position.restore_visible thy_ctxt
 end

val field_lookup_ssN = "field_lookup_ss";
val typinfo_ssN      = "typinfo_ss";
val typuinfo_ssN     = "typuinfo_ss";

val _ = Theory.local_setup (
  Cached_Theory_Simproc.declare_init_thy_simpset field_lookup_ssN field_lookup_aux_simpset #>
  Cached_Theory_Simproc.declare_init_thy_simpset typinfo_ssN typinfo_aux_simpset #>
  Cached_Theory_Simproc.declare_init_thy_simpset typuinfo_ssN typuinfo_aux_simpset);

fun get_field_lookup_ss tab = Symtab.lookup tab field_lookup_ssN |> the
fun get_typinfo_ss tab      = Symtab.lookup tab typinfo_ssN      |> the
fun get_typuinfo_ss tab     = Symtab.lookup tab typuinfo_ssN     |> the

val typuinfo_aux_ctxt = Cached_Theory_Simproc.put_time_warp_simpset get_typuinfo_ss
val typinfo_aux_ctxt = Cached_Theory_Simproc.put_time_warp_simpset get_typinfo_ss
val field_lookup_aux_ctxt = Cached_Theory_Simproc.put_time_warp_simpset get_field_lookup_ss

fun gen_field_lookup_asm_simproc derive_asms unfold augment ctxt =
  let val umm_ctxt = field_lookup_aux_ctxt ctxt
  in Cached_Theory_Simproc.gen_asm_simproc (umm_ctxt, Cached_Theory_Simproc.add_cache, derive_asms) unfold augment end

fun field_lookup_to_field_ti thm = @{thm field_lookup_field_ti [THEN eq_reflection]} OF [thm]

fun augment_field_lookup ctxt thm = [field_lookup_to_field_ti thm, thm]

fun simplified ctxt thms = Simplifier.simplify ((Raw_Simplifier.clear_simpset ctxt) addsimps thms)

fun fold_typ_uinfo_t ctxt thm = simplified ctxt @{thms fold_typ_uinfo_t} thm

fun dest_discriminator @{term_pat "replicate (?n::nat) CHR ''1''"} = SOME n
  | dest_discriminator t = (HOLogic.dest_string t; NONE)

fun dest_fields t = t |> HOLogic.dest_list |> map_filter dest_discriminator

fun get_bounds ctxt idxs thms =
  let
    fun unat x = \<^infer_instantiate>\<open>x = x in term \<open>unat x\<close>\<close> ctxt
    fun snat x = \<^infer_instantiate>\<open>x = x in term \<open>nat (sint x)\<close>\<close> ctxt
    fun is_bound thm =
         case (Thm.prop_of thm) of
           @{term_pat "Trueprop ((?n::nat) < _)"} => member (op =) idxs n
         | @{term_pat "((?n::nat) < _) \<equiv> True"} => member (op =) idxs n
         | @{term_pat "Trueprop ((?n::?'a::len word) < _)"} => member (op =) idxs (unat n)
         | @{term_pat "((?n::?'a::len word) < _) \<equiv> True"} => member (op =) idxs (unat n)
         | @{term_pat "Trueprop ((?n::?'a::len word) <s _)"} => member (op =) idxs (snat n)
         | @{term_pat "((?n::?'a::len word) <s _) \<equiv> True"} => member (op =) idxs (snat n)
         | @{term_pat "Trueprop (0 \<le>s (?n::?'a::len word))"} => member (op =) idxs (snat n)
         | @{term_pat "(0 \<le>s (?n::?'a::len word)) \<equiv> True"} => member (op =) idxs (snat n)
         | _ => false
  in
    filter is_bound thms |> sort_distinct (Thm.thm_ord)
  end

fun field_ti_to_field_lookup t =
  case t of
    @{term_pat "field_ti ?T ?fs"} =>
      \<^instantiate>\<open>'a = \<open>Logic.dest_type T\<close> and T=T and fs=fs in term \<open>field_lookup (typ_info_t T) fs 0\<close>\<close>
  | t => raise TERM ("field_ti_to_field_lookup: unexcpected term", [t])

val _ = Theory.local_setup (Simplifier.define_simproc
  {name= \<^binding>\<open>field_lookup\<close>, passive = false, kind = Simproc, identifier=[],
  lhss =[\<^term>\<open>field_lookup (typ_info_t (TYPE('a::c_type))) (f1#f2#fs) n\<close>,
         \<^term>\<open>field_lookup (typ_info_t (TYPE('c::c_type['d::finite]))) [f1] n\<close>,
         \<^term>\<open>field_lookup (typ_uinfo_t (TYPE('a::c_type))) fs n\<close>,
         \<^term>\<open>field_ti TYPE('a::c_type) (f1#f2#fs)\<close>,
         \<^term>\<open>field_ti TYPE('c::c_type['d::finite]) [f1]\<close>],
  proc =
    let
      fun check ctxt ct = (case Thm.term_of ct of
         @{term_pat "field_lookup (typ_info_t ?T) ?fs _"} =>
           if is_ctype T then (dest_fields fs, I, rev oo augment_field_lookup) else raise Match
       | @{term_pat "field_ti ?T ?fs"} =>
           if is_ctype T then
             (dest_fields fs, field_ti_to_field_lookup, augment_field_lookup) else raise Match
       | @{term_pat "field_lookup (typ_uinfo_t ?T) ?fs _"} =>
           if is_ctype T then (dest_fields fs, I, single oo fold_typ_uinfo_t) else raise Match
       | _ => raise Match)
      handle TERM _ => raise Match
    in
       fn phi => fn ctxt => fn ct =>
        let
          val (idxs, unfold, augment) = check ctxt ct
          val _ = Cached_Theory_Simproc.check_processing ctxt (Thm.term_of ct)
          val _ = Utils.verbose_msg 3 ctxt (fn _ =>
               "field_lookup_simproc invoked: " ^ Syntax.string_of_term ctxt (Thm.term_of ct))
          val asms =
            if null idxs then
              []
            else
              get_bounds ctxt idxs (Cached_Theory_Simproc.all_prems_of ctxt @ Named_Theorems.get ctxt @{named_theorems field_lookup_prems})
              (* N.B: Instead of picking the bounds from the context, we could infer the bounds
                 from the type-information of the array access. *)
          fun derive_assms ctxt assms =
            let
               val eqs = map_filter (try Simpdata.mk_eq) assms
            in derive_bounds ctxt eqs end
        in
          gen_field_lookup_asm_simproc derive_assms unfold augment ctxt (map Thm.prop_of asms) ct
        end
    handle Match => NONE
         | TERM _ => NONE
end} #> snd)

val (field_lookup_simproc_name, field_lookup_simproc) = Simplifier.check_simproc (Context.the_local_context ()) ("field_lookup", Position.none)

fun gen_typinfo_simproc augment ctxt =
  let val umm_ctxt = typinfo_aux_ctxt ctxt
  in Cached_Theory_Simproc.gen_simproc (umm_ctxt, Cached_Theory_Simproc.recert, Cached_Theory_Simproc.add_cache) augment end

fun gen_typuinfo_simproc augment ctxt =
  let val umm_ctxt = typuinfo_aux_ctxt ctxt
  in  Cached_Theory_Simproc.gen_simproc (umm_ctxt, Cached_Theory_Simproc.recert, Cached_Theory_Simproc.add_cache) augment end

val _ = Theory.local_setup (Simplifier.define_simproc
  {name = \<^binding>\<open>type_calculations\<close>, passive = false, kind = Simproc, identifier = [],
  lhss = [
   \<^term>\<open>set (field_names_no_padding (typ_info_t TYPE('a::c_type)) (export_uinfo (typ_info_t TYPE('b::c_type))))\<close>,
   \<^term>\<open>set (all_field_names_no_padding (typ_info_t TYPE('a::c_type)))\<close>,
   \<^term>\<open>TYPE('a::c_type) \<le>\<^sub>\<tau> TYPE('b::c_type)\<close>,
   \<^term>\<open>TYPE('a::c_type) <\<^sub>\<tau> TYPE('b::c_type)\<close>,
   \<^term>\<open>export_uinfo (typ_info_t TYPE('a::c_type)) = export_uinfo (typ_info_t TYPE('b::c_type))\<close>],
  proc =
    let
      fun check ct = case Thm.term_of ct of
            @{term_pat "set (field_names_no_padding (typ_info_t ?T) (export_uinfo (typ_info_t ?S)))"} =>
              if is_ctype T andalso is_ctype S then () else raise Match
          | @{term_pat "set (all_field_names_no_padding (typ_info_t ?T))"} =>
              if is_ctype T then () else raise Match
          | @{term_pat "?T \<le>\<^sub>\<tau> ?S"} =>
              if is_ctype T andalso is_ctype S then () else raise Match
          | @{term_pat "?T <\<^sub>\<tau> ?S"} =>
              if is_ctype T andalso is_ctype S then () else raise Match
          | @{term_pat "export_uinfo (typ_info_t ?T) = export_uinfo (typ_info_t ?S)"} =>
              if is_ctype T andalso is_ctype S then () else raise Match
          | _ => raise Match
    in
      fn phi => fn ctxt => fn ct =>
        let
          val _ = check ct
          val _ = Utils.verbose_msg 3 ctxt (fn _ =>
               "type_calculations invoked: " ^ Syntax.string_of_term ctxt (Thm.term_of ct))
        in
          gen_typinfo_simproc (K single) ctxt ct
        end
        handle Match => NONE
    end } #> snd);
val (type_calculations_simproc_name, type_calculations_simproc) = Simplifier.check_simproc (Context.the_local_context ()) ("type_calculations", Position.none)

val _ = Theory.local_setup (Simplifier.define_simproc
  {name = \<^binding>\<open>typuinfo_calculations\<close>, passive = false, kind = Simproc, identifier=[],
 lhss = [
   \<^term>\<open>export_uinfo (typ_info_t TYPE('a::c_type)) = export_uinfo (typ_info_t TYPE('b::c_type))\<close>,
   \<^term>\<open>typ_uinfo_t TYPE('a::c_type) = export_uinfo (typ_info_t TYPE('b::c_type))\<close>,
   \<^term>\<open>export_uinfo (typ_info_t TYPE('a::c_type)) = typ_uinfo_t TYPE('b::c_type)\<close>,
   \<^term>\<open>typ_uinfo_t TYPE('a::c_type) = typ_uinfo_t TYPE('b::c_type)\<close>],
  proc =
    let
      fun check ct = case Thm.term_of ct of
            @{term_pat "export_uinfo (typ_info_t ?T) = export_uinfo (typ_info_t ?S)"} =>
              if is_ctype T andalso is_ctype S then () else raise Match
          | @{term_pat "typ_uinfo_t ?T = export_uinfo (typ_info_t ?S)"} =>
              if is_ctype T andalso is_ctype S then () else raise Match
          | @{term_pat "export_uinfo (typ_info_t ?T) = typ_uinfo_t ?S"} =>
              if is_ctype T andalso is_ctype S then () else raise Match
          | @{term_pat "typ_uinfo_t ?T = typ_uinfo_t ?S"} =>
              if is_ctype T andalso is_ctype S then () else raise Match
          | _ => raise Match
    in
      fn phi => fn ctxt => fn ct =>
        let
          val _ = check ct
          val _ = Utils.verbose_msg 3 ctxt (fn _ =>
               "toplevel_type_calculations invoked: " ^ Syntax.string_of_term ctxt (Thm.term_of ct))
        in
           gen_typuinfo_simproc (K single) ctxt ct
        end
        handle Match => NONE
    end } #> snd);
val (typuinfo_calculations_simproc_name, typuinfo_calculations_simproc) = Simplifier.check_simproc (Context.the_local_context ()) ("typuinfo_calculations", Position.none)


(* UMM proofs *)

type csenv = ProgramAnalysis.csenv

val (skip_umm_proofs, setup_skip_umm_proofs) = Attrib.config_bool \<^binding>\<open>skip_umm_proofs\<close> (K false);
val _ = Theory.local_setup (Proof_Context.background_theory (setup_skip_umm_proofs))


fun notes xs lthy =
  let
     fun notes_format ((b,thm), attrs) =
       ((b , []), [([thm], attrs)])
  in
    lthy
    |> Local_Theory.notes (map notes_format xs)
    |>> flat o map snd
  end

fun notess xs lthy =
  let
     fun notes_format ((b,thms), attrs) =
       ((b , []), [(thms,  attrs)])
  in
    lthy
    |> Local_Theory.notes (map notes_format xs)
    |>> map snd
  end

open TermsTypes NameGeneration UMM_TermsTypes

type T = {
     starttime     : Time.time,
     fg_thms       : thm list,
     typ_info_thms : thm list,
     tag_def_thms  : thm list,
     typ_name_thms : thm list,
     upd_lift_thms : thm list,
     upd_other_thms : thm list,
     size_align_thms : thm list,
     fl_Some_thms    : thm list,
     fl_ti_thms    : thm list,
     records_done  : string list,
     arrayeltypes_done : typ Binaryset.set,
     structsize_done  : string Binaryset.set, (* name of struct type *)
     szclass_done : (string * string) Binaryset.set,
                    (* name of struct type coupled with sizeclass *)
     packed_done : (string * bool) list
};

val umm_empty_state =
    {starttime = Time.now (),
     fg_thms = [],
     typ_info_thms = [],
     tag_def_thms = [],
     typ_name_thms = [],
     upd_lift_thms = [],
     upd_other_thms = [],
     size_align_thms = [],
     fl_Some_thms = [],
     fl_ti_thms = [],
     records_done = [],
     arrayeltypes_done = Binaryset.empty typ_ord,
     structsize_done = Binaryset.empty string_ord,
     szclass_done = Binaryset.empty (prod_ord string_ord string_ord),
     packed_done = []};

(* Should these be prefixed by e.g. parser_ ?  They can be added to the simpset somewhere else *)
fun umm_finalise (st:T) lthy =
  let

    fun trac s = Feedback.informStr lthy (1, "finalise: " ^ s)
    val _ = trac "About to td_names ..."
    (* Declare the td_names (typ_info_t ..) = ... and add it to the simpset, done during
       finalisation because of potential recursive dependencies in normalisation. *)

    val typ_name_itself = Named_Theorems.get lthy @{named_theorems typ_name_itself}

    fun td_names_thm (recname, typtag_thm) lthy =
      let
        val td_names_name = recname ^ "_td_names";

        val thm = Thm.cterm_of lthy (mk_td_names (Thm.term_of (Thm.lhs_of typtag_thm)))
          |> Simplifier.asm_full_rewrite
               (lthy addsimps
                  (#typ_info_thms st) @
                  @{thms insert_commute nat_to_bin_string.simps})
          |> Drule.export_without_context
      in
        lthy
        |> notes [((Binding.name td_names_name, thm), @{attributes [td_names_simps, simp]})]
        |> snd
      end

    val lthy = lthy |> fold td_names_thm (#records_done st ~~ #typ_info_thms st)

    val thms = [(#fg_thms st, @{attributes [fg_cons_simps]}), (* alread in ss *)
                  (#typ_info_thms st, @{attributes [typ_info_simps]}),
                  (#typ_name_thms st, @{attributes [typ_name_simps]}), (* alread in ss *)
                  (#upd_lift_thms st,  @{attributes [upd_lift_simps]}),
                  (#upd_other_thms st, @{attributes [upd_other_simps]}),
                  (#size_align_thms st, @{attributes [size_align_simps]}), (* already in ss *)
                  (#fl_Some_thms st, @{attributes [fl_Some_simps]}), (* These should be intro simps *)
                  (#fl_ti_thms st, @{attributes [fl_ti_simps, simp]})
                 ]

    fun mapthis (thms, attrs) = ((Binding.empty, thms), attrs)
    val (_, lthy) = notess (map mapthis thms) lthy
  in
    lthy |> More_Local_Theory.in_theory Cached_Theory_Simproc.init_thy
  end;

fun add_st_thms fgs tis tags tns uts uos sas fls fltis
             {starttime, fg_thms, typ_info_thms, tag_def_thms, typ_name_thms,
              upd_lift_thms, upd_other_thms, size_align_thms, fl_Some_thms,
              fl_ti_thms, records_done, arrayeltypes_done, structsize_done,
              szclass_done, packed_done} =
    { starttime = starttime,
      fg_thms = fgs @ fg_thms,
      typ_info_thms = tis @ typ_info_thms,
      tag_def_thms = tags @ tag_def_thms,
      typ_name_thms = tns @ typ_name_thms,
      upd_lift_thms = uts @ upd_lift_thms,
      upd_other_thms = uos @ upd_other_thms,
      size_align_thms = sas @ size_align_thms,
      fl_Some_thms = fls @ fl_Some_thms,
      fl_ti_thms = fltis @ fl_ti_thms,
      records_done = records_done,
      arrayeltypes_done = arrayeltypes_done,
      structsize_done = structsize_done,
      szclass_done = szclass_done,
      packed_done = packed_done
    }

fun add_record_done nm {starttime, fg_thms, typ_info_thms, tag_def_thms,
                        typ_name_thms, upd_lift_thms, upd_other_thms,
                        size_align_thms, fl_Some_thms, fl_ti_thms,
                        records_done, arrayeltypes_done, structsize_done,
                        szclass_done, packed_done} =
    {starttime = starttime,
     fg_thms = fg_thms,
     typ_info_thms = typ_info_thms,
     tag_def_thms = tag_def_thms,
     typ_name_thms = typ_name_thms,
     upd_lift_thms = upd_lift_thms,
     upd_other_thms = upd_other_thms,
     size_align_thms = size_align_thms,
     fl_Some_thms = fl_Some_thms,
     fl_ti_thms = fl_ti_thms,
     records_done = nm :: records_done,
     arrayeltypes_done = arrayeltypes_done,
     structsize_done = structsize_done,
     szclass_done = szclass_done,
     packed_done = packed_done}

fun add_array_done i {starttime, fg_thms, typ_info_thms, tag_def_thms,
                      typ_name_thms, upd_lift_thms, upd_other_thms,
                      size_align_thms, fl_Some_thms, fl_ti_thms,
                      records_done, arrayeltypes_done, structsize_done,
                      szclass_done, packed_done} =
    {starttime = starttime,
     fg_thms = fg_thms,
     typ_info_thms = typ_info_thms,
     tag_def_thms = tag_def_thms,
     typ_name_thms = typ_name_thms,
     upd_lift_thms = upd_lift_thms,
     upd_other_thms = upd_other_thms,
     size_align_thms = size_align_thms,
     fl_Some_thms = fl_Some_thms,
     fl_ti_thms = fl_ti_thms,
     records_done = records_done,
     arrayeltypes_done = Binaryset.add(arrayeltypes_done, i),
     structsize_done = structsize_done,
     szclass_done = szclass_done,
     packed_done = packed_done}

fun add_structsize_done i {starttime, fg_thms, typ_info_thms, tag_def_thms,
                        typ_name_thms, upd_lift_thms, upd_other_thms,
                        size_align_thms, fl_Some_thms, fl_ti_thms,
                        records_done, arrayeltypes_done, structsize_done,
                        szclass_done, packed_done} =
    {starttime = starttime,
     fg_thms = fg_thms,
     typ_info_thms = typ_info_thms,
     tag_def_thms = tag_def_thms,
     typ_name_thms = typ_name_thms,
     upd_lift_thms = upd_lift_thms,
     upd_other_thms = upd_other_thms,
     size_align_thms = size_align_thms,
     fl_Some_thms = fl_Some_thms,
     fl_ti_thms = fl_ti_thms,
     records_done = records_done,
     arrayeltypes_done = arrayeltypes_done,
     structsize_done = Binaryset.add(structsize_done, i),
     szclass_done = szclass_done,
     packed_done = packed_done}

fun add_szclass_done i {starttime, fg_thms, typ_info_thms, tag_def_thms,
                        typ_name_thms, upd_lift_thms, upd_other_thms,
                        size_align_thms, fl_Some_thms, fl_ti_thms,
                        records_done, arrayeltypes_done, structsize_done,
                        szclass_done, packed_done} =
    {starttime = starttime,
     fg_thms = fg_thms,
     typ_info_thms = typ_info_thms,
     tag_def_thms = tag_def_thms,
     typ_name_thms = typ_name_thms,
     upd_lift_thms = upd_lift_thms,
     upd_other_thms = upd_other_thms,
     size_align_thms = size_align_thms,
     fl_Some_thms = fl_Some_thms,
     fl_ti_thms = fl_ti_thms,
     records_done = records_done,
     arrayeltypes_done = arrayeltypes_done,
     structsize_done = structsize_done,
     szclass_done = Binaryset.add(szclass_done, i),
     packed_done = packed_done}

fun add_packed_done i {starttime, fg_thms, typ_info_thms, tag_def_thms,
                        typ_name_thms, upd_lift_thms, upd_other_thms,
                        size_align_thms, fl_Some_thms, fl_ti_thms,
                        records_done, arrayeltypes_done, structsize_done,
                        szclass_done, packed_done} =
    {starttime = starttime,
     fg_thms = fg_thms,
     typ_info_thms = typ_info_thms,
     tag_def_thms = tag_def_thms,
     typ_name_thms = typ_name_thms,
     upd_lift_thms = upd_lift_thms,
     upd_other_thms = upd_other_thms,
     size_align_thms = size_align_thms,
     fl_Some_thms = fl_Some_thms,
     fl_ti_thms = fl_ti_thms,
     records_done = records_done,
     arrayeltypes_done = arrayeltypes_done,
     structsize_done = structsize_done,
     szclass_done = szclass_done,
     packed_done = i::packed_done}

fun phase ctxt st recname s =
    let
        val tm = (Time.now ()) - (#starttime st)
    in
        Feedback.informStr ctxt (2, "PHASE " ^ s ^ " " ^ recname ^ " " ^
                        LargeInt.toString (Time.toMilliseconds tm))
    end

val size_td_simps_arr =
    @{thms "size_td_simps"} @
    [@{thm "typ_info_array"}, @{thm "array_tag_def"},
     @{thm "align_td_array_tag"}]

fun umm_mem_type st recname fld_count recty typtag_thm tag_def_thm entire_component_upd_thm lthy = let
  val _ = Feedback.informStr lthy (1, "Proving UMM inversion for type "^recname^"... ")
  val lthy = Context_Position.set_visible false lthy
  val mem_type_instance_t =
      Logic.mk_of_class(recty, @{class xmem_contained_type})
  val stack_type_instance_t =
      Logic.mk_of_class(recty, @{class stack_type})

  (* typ_tag TYPE('a struct_scheme) = struct_tag_def *)
  val t_def_thms = [typtag_thm, tag_def_thm, @{thm "align_of_def"},
                    @{thm "size_of_def"}]
  val t_def_step = ALLGOALS (asm_full_simp_tac (lthy addsimps t_def_thms))

  (* wf_desc *)
  val wf_desc_Is = lthy addIs [@{thm "wf_desc_final_pad"},
                                @{thm "wf_desc_ti_typ_pad_combine"}]
  val wf_desc_step = force_tac (wf_desc_Is addsimps t_def_thms) 1

  (* wf_size_desc *)
  val wf_size_desc_Is =
      lthy addIs
      [@{thm "wf_size_desc_ti_typ_pad_combine"}, @{thm "wf_size_desc_final_pad"}]
  val wf_size_desc_step = force_tac (wf_size_desc_Is addsimps t_def_thms) 1

  val entire_update_step = resolve_tac lthy [entire_component_upd_thm] 1

  (* At Raf's request - important if screwed *)
  fun dprint_tac s st =
    let
      val level = Config.get lthy Feedback.level
      val short = not (Config.get lthy Feedback.verbose)
      val s = s ^ " - " ^ recname
    in if level > 2
       then if short then (tracing (s ^ " (" ^ @{make_string} (Thm.nprems_of st) ^ " subgoals)"); all_tac st)
            else print_tac lthy s st
       else all_tac st
    end

  fun asm_full_simp_tac' ctxt = SUBGOAL (fn (goal, i) =>
    let
      val depth = strip_comb_depth_of_term goal
      val ctxt' = ctxt |> Config.map simp_depth_limit (K (depth + 20))
    in
      SOLVED' (asm_full_simp_tac ctxt') i
    end)

  val align_dvd_size_step =
      asm_full_simp_tac
          (lthy addsimps t_def_thms @ [
             @{thm "align_of_def"}, @{thm "size_of_def"}]) 1

  val align_field_step =
      simp_tac (lthy addsimps t_def_thms) 1 THEN
      asm_full_simp_tac'
          (lthy addsimps [
             @{thm "align_td_array_tag"},
             @{thm "typ_info_array"}, @{thm "array_tag_def"}] @ @{thms wf_align_field_simps}) 1

  val size_lt_step =
      simp_tac (lthy addsimps t_def_thms) 1 THEN
      asm_full_simp_tac'
          (lthy addsimps
            size_td_simps_arr @
            [@{thm "addr_card"}, @{thm "align_of_def"},
             @{thm "size_of_def"}, @{thm "align_of_final_pad"}]) 1

   val wf_component_descs_step =
          simp_tac (lthy addsimps t_def_thms) 1 THEN
          UMM_Tools.wf_component_descs_tac lthy []

   val component_descs_independent_step =
          simp_tac (lthy addsimps t_def_thms) 1 THEN
          UMM_Tools.component_descs_independent_tac lthy []

   val wf_field_descs_step =
          simp_tac (lthy addsimps t_def_thms) 1 THEN
          UMM_Tools.wf_field_descs_tac lthy []

   val contained_field_descs_step =
          simp_tac (lthy addsimps t_def_thms) 1 THEN
          UMM_Tools.contained_field_descs_tac lthy []

   val wf_padding_step =
          let
            val ctxt = lthy addsimps (t_def_thms @ @{thms wf_padding_combinator_simps wf_padding})
              |> Config.map simp_depth_limit (K (fld_count + 20))
          in  asm_full_simp_tac ctxt 1 end

  val is_mem_type_thm =
    if Config.get lthy skip_umm_proofs then
      let val _ = warning "config skip_umm_proofs is set: skipping umm proof"
      in Goal.prove lthy [] [] mem_type_instance_t (fn _ => Skip_Proof.cheat_tac lthy 1) end
    else
      Goal.prove_future lthy [] [] mem_type_instance_t (fn _ =>
            DETERM (
                dprint_tac "tuned_xmem_contained_type_class_intro" THEN
                resolve_tac lthy @{thms tuned_xmem_contained_type_class_intro} 1 THEN
                dprint_tac "wf_desc" THEN
                wf_desc_step THEN
                dprint_tac "wf_size_desc" THEN
                wf_size_desc_step THEN
                dprint_tac "align_dvd_size" THEN
                align_dvd_size_step THEN
                dprint_tac "align_field" THEN
                align_field_step THEN
                dprint_tac "size_lt" THEN
                size_lt_step THEN
                dprint_tac "entire_update" THEN

                entire_update_step THEN
                dprint_tac "wf_component_descs" THEN
                wf_component_descs_step THEN
                dprint_tac "component_descs_independent" THEN
                component_descs_independent_step THEN
                dprint_tac "wf_field_descs" THEN
                wf_field_descs_step  THEN
                dprint_tac "contained_field_descs" THEN
                contained_field_descs_step THEN
                dprint_tac "wf_padding" THEN
                wf_padding_step THEN
                dprint_tac "mem_type instance done"
             ))

  val is_stack_type_thm =
    if Config.get lthy skip_umm_proofs then
      let val _ = warning "config skip_umm_proofs is set: skipping stack_type proof"
      in Goal.prove lthy [] [] stack_type_instance_t (fn _ => Skip_Proof.cheat_tac lthy 1) end
    else
      Goal.prove_future lthy [] [] stack_type_instance_t (fn {context,...} =>
        dprint_tac "stack_type_class_intro" THEN
        Class.intro_classes_tac context [] THEN
        simp_tac (context addsimps t_def_thms) 1 THEN
        asm_full_simp_tac' (context addsimps @{thms stack_typ_info_intros stack_byte_name_def}) 1)
in
  lthy
  |> More_Local_Theory.in_theory (Axclass.add_arity is_mem_type_thm)
  |> More_Local_Theory.in_theory (Axclass.add_arity is_stack_type_thm)
end;

val packed_type_simps = @{thms "packed_type_intro_simps"}
val packed_type_class_intro = @{thm "packed_type_class_intro"}
val td_packed_intros = @{thms "td_packed_intros"}

fun umm_packed_type recname recty typtag_thm tag_def_thm fgthms (st, lthy) = let
  val _ = Feedback.informStr lthy (1, "Proving UMM packed type for type "^recname^"... ")

  val packed_type_instance_t =
      Logic.mk_of_class (recty, "PackedTypes.packed_type")

  val simp_thms = [typtag_thm] @ packed_type_simps @ fgthms @
           @{thms align_td_array_info}   @
           @{thms max_non_zero_unfold}

  val pt_ss = (lthy addsimps simp_thms)

  (* Try to solve. If we fail, we catch the exception and ignore. *)
  val is_packed_type_thm =
      Goal.prove lthy [] [] packed_type_instance_t
       (fn _ => DETERM ((
                (resolve_tac lthy [packed_type_class_intro]
                 THEN' K (unfold_tac lthy [typtag_thm, tag_def_thm])
                 THEN' REPEAT_ALL_NEW (resolve_tac lthy td_packed_intros))
                 THEN_ALL_NEW (asm_simp_tac pt_ss)) 1))
in
 (add_packed_done (Syntax.string_of_typ lthy recty, true) st,
  lthy
  |> More_Local_Theory.in_theory (Axclass.add_arity is_packed_type_thm))
end handle ERROR _ => (Feedback.informStr lthy (0, "Failed to prove UMM packed type for type "^recname);
      (add_packed_done (Syntax.string_of_typ lthy recty, false) st, lthy))

exception AlreadyDone
fun calculate_record_size recname (st, lthy) ths ty =
  if Binaryset.member(#structsize_done st, recname) then (st, lthy)
  else let
      val tysize_th =
          Simplifier.rewrite
              (lthy addsimps
                          ((@{thm "size_of_def"} :: @{thm "typ_info_array"} ::
                            @{thm "array_tag_def"} :: @{thm "TWO"} ::
                            @{thms size_td_simps_3 max_non_zero_unfold} @ ths)))
              (Thm.cterm_of lthy (mk_sizeof (mk_TYPE ty)))
      val _ = let
        val size_t = Thm.term_of (Thm.rhs_of tysize_th)
      in
        (* check that it simplifies to a number *)
        numb_to_int size_t
        handle e as TERM _ =>
               (Feedback.informStr lthy (1, "Can't get good computation of size of type " ^
                         recname ^ " (got this RHS: "^
                         Syntax.string_of_term lthy size_t ^ ")");
                raise e)
      end
      val ([thm], lthy) =
        lthy
        |> notes [((Binding.name(recname^"_size"), tysize_th), @{attributes [size_simps, simp]})]
    in
      (add_structsize_done recname st, lthy)
    end

(* Combinator which saves the goal (after it was proved, before being
unified with subgoal). *)
fun MEMO_GOAL ctxt f tac i = let
  (* goal may contain schematics *)
  fun inner_tac (goal, i') = let
      val thm = Goal.prove ctxt [] [] goal (fn { context, ... } => tac context i')
    in
      (* This calls f eagerly, which may not be what we want (although it is protected by SUBGOAL) *)
      (f thm; resolve_tac ctxt [thm] i')
    end
  in
    SUBGOAL inner_tac i handle ERROR _ => no_tac
  end


val fold_comp_conv = Conv.bottom_conv (K (Conv.try_conv (Conv.rewr_conv @{thm heap_update_fold_comp_apply})))
val rhs_conv = Conv.arg_conv o Conv.arg_conv (* Trueprop and eq *)
fun fconv_concl_conv conv thm = Conv.fconv_rule (Conv.concl_conv (Thm.nprems_of thm) conv) thm
fun fold_rhs_comp_conv ctxt = fconv_concl_conv (rhs_conv (Conv.try_conv (fold_comp_conv ctxt)))
fun pointless_eq ctxt eq =
 case Thm.concl_of eq of
   @{term_pat "Trueprop (?f ?x = ?g ?y)"} =>
    if x = y then
      let
        val ext = Drule.infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt f), SOME (Thm.cterm_of ctxt g)] ext
      in
        (ext OF [eq])
        |> Simplifier.full_simplify (Simplifier.clear_simpset ctxt addsimps @{thms triv_forall_equality})
      end

    else
      eq
 | _ => eq

fun comp_pointless_eq ctxt = fold_rhs_comp_conv ctxt #>pointless_eq ctxt

fun gen_c_type_instantiation sort tac recname def thy =
  let
  in
    thy
    |> Class.instantiation ([recname], [], sort)
    |> `(fn lthy => apsnd (Syntax.check_term lthy) def)
    |-> Specification.definition NONE [] []
    |-> (fn (_, (_, eq_def)) =>
       Class.prove_instantiation_exit_result Morphism.thm tac eq_def)
  end

val c_type_name_instance = gen_c_type_instantiation @{sort c_type_name}
  (fn ctxt => fn _ => Class.intro_classes_tac ctxt [])

fun def_spec name attributes eq =
  let
    val b = the_default Binding.empty (Option.map (Binding.name) name)
  in ((b, attributes), eq) end

fun c_type_name_instantiation recname lthy =
  let
     fun trac s = Feedback.informStr lthy (1, recname ^ ": " ^ s)
     val fullrecname = Sign.intern_type (Proof_Context.theory_of lthy) recname
     val recty = Type(fullrecname, [])
     val typ_name_itself_lhs = \<^Const>\<open>typ_name_itself recty\<close> $ Free("x", mk_itself_type recty)
     val typ_name_itself_rhs = mk_string recname
     val typ_name_itself_triple =
       def_spec NONE @{attributes [typ_name_itself, simp]} (mk_defeqn(typ_name_itself_lhs, typ_name_itself_rhs))
     val (typ_name_itself_thm, lthy) = lthy |> More_Local_Theory.in_theory_result (
           c_type_name_instance fullrecname typ_name_itself_triple)
     val _ = trac ("c_type_name instantiation done")
  in
    lthy
  end

fun c_type_instance recname = gen_c_type_instantiation @{sort c_type}
        (fn ctxt => fn thm =>
          Class.intro_classes_tac ctxt [] THEN
          ALLGOALS (asm_full_simp_tac (ctxt addsimps [thm])))
        recname

fun c_type_instantiation (recname, (flds, attrs)) lthy =
  let
    fun trac s = Feedback.informStr lthy (1, recname ^ ": " ^ s)
    val thy = Proof_Context.theory_of lthy
    val fullrecname = Sign.intern_type thy recname
    val recty = Type(fullrecname, [])
    fun get_align [] = 0
      | get_align (CType.AlignedExponent n::_ ) = n
      | get_align (_::rest) = get_align rest

    fun gen_tag_pad flds tag =
      case flds of
        [] => error ("Record ("^recname^") with no fields??")
      | [(fldnm, ty, _, attrs)] => mk_tag_pad_tm (get_align attrs) recty ty fldnm lthy $ tag
      | (fldnm, ty, _, attrs)::rest =>
          gen_tag_pad rest (mk_tag_pad_tm (get_align attrs) recty ty fldnm lthy$ tag)
    val tag_rhs =
      final_pad_tm (get_align attrs) recty $ gen_tag_pad flds (empty_tag_tm recty 0 recname)
    val tag_nm = recname^"_tag"
    val (tag_def_thm, lthy) = prim_mk_defn tag_nm tag_rhs @{attributes [typ_tag_defs, simp]} lthy
      handle ERROR s => error ("Defining "^tag_nm^" as\n  "^
                              Syntax.string_of_term_global (Proof_Context.theory_of lthy) tag_rhs ^
                              "\nfailed with message: "^s)
    val _ = trac ("defined " ^ quote tag_nm)
    val tag_tm = Const(Sign.intern_const (Proof_Context.theory_of lthy) tag_nm, mk_tag_type recty)
    val typ_info_t_lhs = \<^Const>\<open>typ_info_t recty\<close> $ Free("x", mk_itself_type recty)
    val typ_info_t_rhs = tag_tm
    val typ_info_t_triple =
      def_spec NONE [] (mk_defeqn(typ_info_t_lhs, typ_info_t_rhs))
    val (typ_info_t_thm, lthy) = lthy |> More_Local_Theory.in_theory_result (
          c_type_instance fullrecname typ_info_t_triple)
    val _ = trac ("c_type instantiation done")
  in
    ((tag_def_thm, typ_info_t_thm), lthy)
  end

fun umm_struct_calculation cse ((recname, (flds, attrs)), tag_def_thm, typ_info_t_thm, st, lthy) = let
  val _ = not (member (op =) (#records_done st) recname) orelse
          (Feedback.informStr lthy (1, "UMM Proof for "^recname^" already done");
           raise AlreadyDone)
  (* useful stuff for what is to come *)
  val fullrecname = Sign.intern_type (Proof_Context.theory_of lthy) recname
  val recty = Type(fullrecname, [])

  val phase = phase lthy st recname
  fun trac s = Feedback.informStr lthy (1, recname ^ ": " ^ s)

  fun get_align [] = 0
    | get_align (CType.AlignedExponent n::_ ) = n
    | get_align (_::rest) = get_align rest

  val _ = Feedback.informStr lthy (0, "UMM setup for type "^recname^"... ")

  val _ = phase "START"

  val typ_info_TYPE = mk_typ_info_of recty

  (* make the definitions *)

  val lthy = lthy |> Context_Position.set_visible false

  val _ = phase "COMPONENT UPDATE"

  val entire_component_upd_thm =
    let
      val nested_size_align_thms = #size_align_thms st
      (* avoid simplifying size and alignment computations *)
      val entire_update_simps = @{thms field_update_typ_combinators_simps aggregate_typ_combinators_simps} @
         nested_size_align_thms @ [typ_info_t_thm, tag_def_thm] @ @{thms comp_apply}

      val component_upd = mk_field_update_component_desc_apply recty "bs" "v"
      fun upd_ss ctxt =
        Simplifier.put_simpset
          (merge_ss (HOL_basic_ss, RecursiveRecordPackage.get_simpset (Proof_Context.theory_of lthy))) ctxt

      val component_upd_thm = Simplifier.asm_full_rewrite ((upd_ss lthy) addsimps entire_update_simps) (Thm.cterm_of lthy component_upd)
          |> Drule.export_without_context

      val c_bs = Thm.cterm_of lthy (Free ("bs",@{typ "byte list"}))
      val c_v = Thm.cterm_of lthy (Free ("v", recty))
      val c_w = Thm.cterm_of lthy (Free ("w", recty))
      val entire_comp_upd_thm = (
            Drule.infer_instantiate lthy [(("bs",0),c_bs),(("v",0),c_v),(("w",0),c_w)] @{thm eq_comp}
            OF [Drule.infer_instantiate lthy [(("bs",0),c_bs),(("v",0),c_v)] component_upd_thm,
                Drule.infer_instantiate lthy [(("bs",0),c_bs),(("v",0),c_w)] component_upd_thm])
          |> Drule.export_without_context
     in entire_comp_upd_thm end



  val _ = phase "MEMTYPE"
  (* Add the mem_type instance *)
  val lthy = umm_mem_type st recname (length flds) recty typ_info_t_thm tag_def_thm entire_component_upd_thm lthy

  val _ = phase "SIZE"
  val _ = trac "About to size/align..."

  val (size_align_td_thm, partial_size_align_tds) = let
    val acc = Unsynchronized.ref ([] : thm list)
    fun upd_acc thm = Unsynchronized.change acc (fn thms => thm :: thms)


    (* probably not required if we are using thy2ctxt *)
    val idx = Variable.maxidx_of lthy
    val tm  = mk_size_aligntd typ_info_TYPE (Var (("s", idx + 1), nat)) (Var (("a", idx + 2), nat))
    val ctxt' = Variable.declare_maxidx (idx + 2) lthy
    val cterm = Thm.cterm_of ctxt' (HOLogic.mk_Trueprop tm)
    val sa_ss = ctxt' addsimps @{thms typ_info_array array_tag_def align_td_array_tag max_def padup_def}
                  delsimps @{thms One_nat_def}
    val tac = let
      fun rectac ctxt   = MEMO_GOAL ctxt upd_acc doit
      and doit ctxt  i  =
          DETERM (FIRST' [ resolve_tac ctxt @{thms size_align_td_empty_typ_infoI} (* No subgoals *)
                         , EVERY' [ resolve_tac ctxt @{thms size_align_td_ti_typ_pad_combineI size_align_td_ti_final_padI}
                                  , rectac ctxt
                                  , resolve_tac ctxt @{thms aggregate_ti_typ_pad_combine aggregate_empty_typ_info}
                                  , simp_tac sa_ss
                                  , simp_tac sa_ss
                                  ]
                         ] i)
    in doit end (* we don't memo the top-level *)

    val thm = Goal.prove_internal ctxt' [] cterm (fn _ => unfold_tac ctxt' [typ_info_t_thm, tag_def_thm] THEN tac ctxt' 1)
  in
    (thm, Unsynchronized.! acc)
  end

  val size_td_thm = @{thm size_align_td_size_td} OF [ size_align_td_thm ]
  val (st, lthy) = calculate_record_size recname (st, lthy) [size_td_thm] recty

  val _ = phase "ALIGN"
  val _ = trac "About to size/align 1..."

  val align_td_thm = @{thm size_align_td_align_td} OF [ size_align_td_thm ]


  val align_of_thm =
    let
      val (t, ctxt) = mk_align_of lthy recty
      val [thm] = Variable.export ctxt lthy (* FIXME: this seems to unfold typ_info_t TYPE... but should not *)
        [Simplifier.asm_full_rewrite
          (ctxt addsimps (@{thms align_of_def} @ [align_td_thm]))
          (Thm.cterm_of ctxt t)]
    in
      thm
    end

  val (recthms,lthy) =
    lthy
    |> notes [((Binding.name(recname^"_size_of") , size_td_thm), []),
              ((Binding.name(recname^"_align_td"), align_td_thm), []),
              ((Binding.name(recname^"_align_of"), align_of_thm), [])]

  fun err_msg rname kind int_val thm_val () =
      "UMM proof error: mismatch of internal value and theorem for " ^
       quote kind ^ " of " ^ quote rname ^ ": " ^
       quote (string_of_int int_val) ^ " vs. " ^ quote (string_of_int thm_val);

  val _ =
    let
      val pa_sz = ProgramAnalysis.sizeof_struct_or_union cse recname
      val thm_sz = Utils.rhs_of_eq (Thm.concl_of size_td_thm) |> Utils.dest_nat_or_number
      val _ = @{assert_msg} (pa_sz = thm_sz) (err_msg recname "sizeof" pa_sz thm_sz)

      val pa_al = ProgramAnalysis.alignof_struct_or_union cse recname
      val thm_al = Utils.rhs_of_eq (Thm.concl_of align_of_thm) |> Utils.dest_nat_or_number
      val _ = @{assert_msg} (pa_sz = thm_sz) (err_msg recname "alignof" pa_al thm_al)
    in () end


  val ([typtag_thm], lthy) =
    lthy
    |> notes [((Binding.name(recname^"_typ_info"), typ_info_t_thm) ,[])]


  val _ = phase "TYPNAME"
  val _ = trac "About to About to type typ_nametype typ_name ..."
  val typ_name_thm =
      Simplifier.asm_full_rewrite
          (lthy addsimps [typtag_thm])
          (Thm.cterm_of lthy (mk_typ_name_of recty))
  val (typ_name_thm, lthy) =
    lthy
    |> notes [((Binding.name(recname^"_typ_name") , typ_name_thm), @{attributes [simp]})]



  val _ = phase "FL"
  val _ = trac "About to type/field fl..."

  fun dest_Some (@{term_pat "Some ?x"}) = x

  val flthms = let
    (* This will keep adding new subgoals to the end, then start solving in a LIFO fashion.
       We want LIFO as we want to simplify the arithmetic from the inside out.
     *)
    val ss = lthy addsimps (@{thms padup_def max_def align_of_def align_td_array'} @ partial_size_align_tds)
    fun tac ctxt =
        rewrite_goal_tac ctxt [typtag_thm, tag_def_thm] 1
          THEN
          REPEAT_DETERM
          (FIRST'
             [ resolve_tac ctxt (@{thms field_lookup_ti_intros
                                        aggregate_ti_typ_pad_combine aggregate_empty_typ_info
                                        notin_field_names_list_ti_typ_pad_combine notin_field_names_list_empty_typ_info
                                  } @ partial_size_align_tds)
              , (* Remainder are solved by simp (eq and non-eq over chars and strings *)
                SOLVED' (simp_tac ss)
             ] 1)

    fun fl_thm f = let
      val thmname = Binding.name(recname^"_"^(#1 f) ^"_fl")
      val idx = Variable.maxidx_of lthy + 1
      val tm  = HOLogic.mk_eq (mk_field_lookup_nofs (recty, #1 f),
                               (Var (("x", idx), mk_option_ty (mk_prod_ty (mk_tag_type recty, nat)))))
      val lthy' = Variable.declare_maxidx idx lthy
      val cterm = Thm.cterm_of lthy' (HOLogic.mk_Trueprop tm)
      val thm = Goal.prove_internal lthy' [] cterm (fn _ => tac lthy')
    in
      ((thmname, thm), [])
    end
  in
    Par_List.map fl_thm flds
  end;

  val (flthms,lthy) = notes flthms lthy

  val _ = phase "FG"
  val _ = trac "About to fg..."
  val fgthms = let
    fun fg_thm f = Goal.prove_future lthy [] []
      (mk_prop (mk_fg_cons_tm recty (#2 f) (#1 f) lthy))
      (fn _ => asm_full_simp_tac
          (lthy addsimps [@{thm "fg_cons_def"}, @{thm comp_def}]) 1)
  in
    Par_List.map fg_thm flds
  end;

  val _ = phase "PACKEDTYPE"
  val (st, lthy) = umm_packed_type recname recty typtag_thm tag_def_thm fgthms (st, lthy)

  val _ = phase "FLSOME"
  val _ = trac "About to type/field fl_Some ..."
  val fl_Some_thms = let
      fun fl_thm' (fl, (name, _, _, _)) =
        let
          val concl_lhs = mk_field_lookup_nofs (recty, name)
          val thm =
              Simplifier.asm_full_rewrite (lthy addsimps [fl, @{thm TWO}])
                                          (Thm.cterm_of lthy concl_lhs) |>
                                          Drule.export_without_context
          val kind = "offsetof(" ^ recname ^ ", " ^ name^ ")"
          val pa_off = ProgramAnalysis.offsetof cse recname name
          val thm_off = Utils.rhs_of_eq (Thm.concl_of thm)
            |> dest_Some |> HOLogic.dest_prod |> #2 |> Utils.dest_nat_or_number
          val _ = @{assert_msg} (pa_off = thm_off) (err_msg recname kind pa_off thm_off)

        in
           ((Binding.name(recname^ "_" ^ name ^ "_fl_Some"), thm), [])
        end
  in
      Par_List.map fl_thm' (flthms ~~ flds)
  end
  val (fl_Some_thms, lthy) = notes fl_Some_thms lthy

  val _ = phase "FLTI"
  val _ = trac "About to type/field fl_ti ..."
  val fl_ti_thms = let
      val rl = @{thm "field_lookup_field_ti"}

      fun fl_thm' (fl_Some, (name, _, _, _)) = let
          val thm = rl OF [fl_Some]
      in
          ((Binding.name(recname^ "_" ^ name ^ "_fl_ti"), thm), [])
      end
  in
      Par_List.map fl_thm' (fl_Some_thms ~~ flds)
  end
  val (fl_ti_thms, lthy) = notes fl_ti_thms lthy

  val upd_lift_thms = []
  val upd_lift_other_thms = []

  val _ = phase "NAMES"

  val lthy =
      lthy |> More_Local_Theory.in_theory (Context.theory_map
               (Simplifier.map_ss
                    (fn ss => ss addsimps (recthms @ flthms @ fgthms))))

  val _ = phase "heap_update_fold_toplevel_fields"
  val _ = trac "About to heap_update_fold_toplevel_fields ..."

  val (heap_update_fold_thm, heap_update_fold_pointless_thm)  =
    let
      val aggregate = \<^infer_instantiate>\<open>t = typ_info_TYPE in prop \<open>aggregate t\<close>\<close> lthy
      val aggregate_thm = Goal.prove lthy [] [] aggregate (fn {context, ...} =>
             Simplifier.asm_full_simp_tac (context addsimps [typtag_thm]) 1)
      val lhs = \<^infer_instantiate>\<open>t = typ_info_TYPE in term \<open>filter (Not \<circ> padding_field_name) (toplevel_field_names t)\<close>\<close> lthy
      val filter_toplevel_field_names_eq = Thm.cterm_of lthy lhs
        |> Simplifier.asm_full_rewrite (lthy addsimps
             [typtag_thm] @
             @{thms toplevel_field_names_no_padding_combinator_simps})
      val ((_, [fold_thm]), ctxt) =
        Variable.import true
          [@{thm heap_update_fold_toplevel_field_names_no_padding} OF [aggregate_thm]] lthy
      val fold_thm = fold_thm
        |> Simplifier.asm_full_simplify (ctxt addsimps
             [filter_toplevel_field_names_eq] @
             @{thms to_bytes_def[symmetric] size_of_def heap_update_fold}
             delsimps @{thms heap_list.simps})
        |> singleton (Variable.export ctxt lthy) |>  Drule.zero_var_indexes
      val fold_pointless_thm = comp_pointless_eq lthy fold_thm
    in
      (fold_thm, fold_pointless_thm)
    end

  val lthy = lthy
    |> notes [((Binding.make (recname ^ "_heap_update_fold_toplevel_fields", \<^here>), heap_update_fold_thm),
              @{attributes [heap_update_fold_toplevel_fields]})]
    |> snd
    |> notes [((Binding.make (recname ^ "_heap_update_fold_toplevel_fields_pointless", \<^here>), heap_update_fold_pointless_thm),
              @{attributes [heap_update_fold_toplevel_fields_pointless]})]
    |> snd

  val _ = phase "h_val_fields"
  val _ = trac "About to h_val_fields ..."

  val h_val_field_eqs =
    let
      val h_val_field_eq_trms = map (fn (fldnm, ty, _, _) => mk_h_val_field_eq lthy recty ty "h" "p" fldnm ) flds
      fun prove eq = Goal.prove_future lthy ["h", "p"] [] eq (fn {context,...} =>
           asm_full_simp_tac (context addsimps fl_ti_thms @
                @{thms h_val_field_from_bytes' }) 1)
      val eqs = map prove h_val_field_eq_trms
    in
      eqs
    end

   val lthy = lthy
     |> notess [((Binding.make (recname ^ "_h_val_fields", \<^here>), h_val_field_eqs),
              @{attributes [h_val_fields]})]
     |> snd

  val _ = phase "heap_update_fields"
  val _ = trac "About to heap_update_fields ..."

  val heap_update_field_eqs =
    let
      val heap_update_field_eq_trms = map (fn (fldnm, ty, _, _) => mk_heap_update_field_eq lthy recty ty "h" "p" "v" fldnm ) flds
      val root_convs =  map (fn fl_Some => @{thm heap_update_field_root_conv''} OF [@{thm meta_eq_to_obj_eq} OF [fl_Some]]) fl_Some_thms
       |> map (Simplifier.simplify lthy)

      fun prove eq = Goal.prove_future lthy ["h", "p", "v"] [] eq (fn {context,...} =>
           asm_full_simp_tac (context addsimps root_convs @ @{thms h_val_field_from_bytes' }) 1)
      val eqs = map prove heap_update_field_eq_trms
    in
      eqs
    end

   val lthy = lthy
     |> notess [((Binding.make (recname ^ "_heap_update_fields", \<^here>), heap_update_field_eqs),
              @{attributes [heap_update_fields]})]
     |> snd

  val _ = phase "h_val_unfolds"
  val _ = trac "About to h_val_unfold ..."

   fun symmetric ctxt thm = fst (Thm.apply_attribute Calculation.symmetric thm (Context.Proof ctxt))
   val h_val_unfold =
     let
       val fs = map (fn (fldnm, ty, _, _) => (fldnm, ty)) flds
       val unfold = mk_h_val_unfold lthy recty "h" "p" fs
       val idupdates = Proof_Context.get_thms lthy (recname ^ "_idupdates")
       fun prove eq = Goal.prove_future lthy ["h", "p"] [] eq (fn {context,...} =>
           asm_full_simp_tac (context addsimps h_val_field_eqs) 1)
       val unfold_thm = prove unfold
     in
       unfold_thm
     end

   val lthy = lthy
     |> notes [((Binding.make (recname ^ "_h_val_unfold", \<^here>), h_val_unfold),
              @{attributes [h_val_unfold]})]
     |> snd

  val _ = phase "all_field_names_no_padding"
  val _ = trac "About to all_field_names_no_padding ..."
  val (all_field_names_no_padding, set_all_field_names_no_padding) =
   let
     val all_field_names_no_padding_thms = Named_Theorems.get lthy @{named_theorems all_field_names_no_padding}
     val lhs = \<^infer_instantiate>\<open>t = typ_info_TYPE in term \<open>all_field_names_no_padding t\<close>\<close> lthy
     val lhs_set = \<^infer_instantiate>\<open>t = typ_info_TYPE in term \<open>set (all_field_names_no_padding t)\<close>\<close> lthy
     val eq = Thm.cterm_of lthy lhs
       |> Simplifier.asm_full_rewrite (lthy addsimps
              [typtag_thm] @
              all_field_names_no_padding_thms @
              @{thms all_field_names_no_padding_combinator_simps})
     val eq_set = Thm.cterm_of lthy lhs_set
       |> Simplifier.asm_full_rewrite (lthy addsimps [eq])
   in
     (eq, eq_set)
   end
   val lthy = lthy
     |> notes [((Binding.make (recname ^ "_all_field_names_no_padding", \<^here>),  all_field_names_no_padding),
              @{attributes [all_field_names_no_padding]})]
     |> snd

   val lthy = lthy
     |> notes [((Binding.make (recname ^ "_set_all_field_names_no_padding", \<^here>),  set_all_field_names_no_padding),
              @{attributes [set_all_field_names_no_padding]})]
     |> snd

  val _ = phase "sub_typ_simps"
  val _ = trac "About to sub_typ_simps ..."
  val sub_typ_simps =
    let
      val ctxt = lthy delsimprocs [field_lookup_simproc, type_calculations_simproc]
      val distinct_fl_Some_thms = map #2 flds ~~ fl_Some_thms
           |> distinct (fn ((T1, _) , (T2, _)) => T1 = T2) |> map #2
      val thms = distinct_fl_Some_thms |>
        map (fn thm => (@{thm field_lookup_sub_typ'} OF [thm]) |> Simplifier.full_simplify ctxt)
    in
      thms
    end
   val lthy = lthy
     |> notess [((Binding.make (recname ^ "_sub_typ_simps", \<^here>),  sub_typ_simps),
              @{attributes [sub_typ_simps, simp]})]
     |> snd

  val zero_simps =
    let
      fun zero_simp fl_Some_thm =
        (@{thm field_lookup_zero'} OF [fl_Some_thm])
        |> Conv.fconv_rule (Simplifier.asm_full_rewrite lthy)
        |> (fn thm => thm OF @{thms refl})
        |> Conv.fconv_rule (Simplifier.asm_full_rewrite lthy)
    in
      map zero_simp fl_Some_thms
    end

  val lthy = lthy
    |> notess [((Binding.make (recname ^ "_zero_simps", \<^here>),  zero_simps), @{attributes [zero_simps]})]
    |> snd

  val make_zero =
    let
      val zero = \<^Const>\<open>c_type_class.zero recty\<close> |> Thm.cterm_of lthy
      val make_thm = nth (Proof_Context.get_thms lthy (recname ^ "_idupdates")) 0
        |> Drule.infer_instantiate' lthy [SOME zero]
        |> Conv.fconv_rule (Simplifier.asm_full_rewrite (lthy addsimps zero_simps))
    in
      make_thm
    end

  val lthy = lthy
    |> notes [((Binding.make (recname ^ "_make_zero", \<^here>),  make_zero), @{attributes [make_zero]})]
    |> snd

(*

thm field_lookup_zero' [OF inner_C_fld1_C_fl_Some, simplified, OF refl, simplified inv_p]
thm inner_C_idupdates(1) [of zero]

*)
  val _ = phase "END"
  val _ = trac "done"
in
  (st |> add_st_thms fgthms [typtag_thm] [tag_def_thm] typ_name_thm
                     upd_lift_thms upd_lift_other_thms recthms
                     fl_Some_thms fl_ti_thms
      |> add_record_done recname,
   lthy)
end handle TYPE (s, tps, ts) => let
             val _ = Feedback.informStr lthy (0, "EXN: " ^ s)
           in
             raise (TYPE (s, tps, ts))
           end
         | AlreadyDone => (st,lthy)


fun prove_type_in_szclass ty szclass (st, lthy) =  let
  val tyname = Syntax.string_of_typ lthy ty
in
  if Binaryset.member(#szclass_done st, (tyname, szclass)) then (st, lthy)
  else let
      fun tac ctxt _ =
          Class.intro_classes_tac ctxt [] THEN asm_full_simp_tac ctxt 1

      val instance_t = Logic.mk_of_class(ty, szclass)
      val instance_thm =
          Goal.prove_future lthy [] [] instance_t (tac lthy)
      val lthy = More_Local_Theory.in_theory (Axclass.add_arity instance_thm) lthy
      val st = add_szclass_done (tyname, szclass) st
    in
      tracing ("Proved "^tyname^" :: "^szclass);
      (st, lthy)
    end
end

fun prove_packed_outer_inner ty class (st, lthy) =
  let
    val tyname = Syntax.string_of_typ lthy ty
  in
    case AList.lookup (op =) (#packed_done st) tyname of
      SOME true => prove_type_in_szclass ty class (st, lthy)
    | SOME false => (st, lthy)
    | NONE => error ("prove_packed_outer_inner: required packed_type instance not yet attempted for: " ^  tyname)
  end


  (* prove that the new type is an instance of the class finite *)
  (* prove that the new type is an instance of the class array_max_count *)
fun umm_array_calculation el_ty n st lthy = let
  val _ = Feedback.informStr lthy (1, "Proving that an array of "^Int.toString n^" "^
                   Syntax.string_of_typ lthy el_ty ^" is a mem_type")

  (* Unlike in the struct case, we don't need to establish the new type as
     a c_type, because the array operator has already been declared to do this
     by the
        instance array :: (type,finite) c_type ..
     line in ArraysMemInstance.thy.

     So we can get straight onto showing that the array type is in mem_type.
     This is done exploiting the fact that we have the following instance
     in our context already

        instance array :: (array_outer_max_size, array_max_count) mem_type

     Thanks to the neat instance declarations in ArchArraysMemInstance.thy
     (all those classes with names lt<n>), the array_max_count for
     the array size will be handled automatically by type-checking.

     This means that we just need to do one independent instance proofs,
     for el_ty :: array_outer_max_size

     Even that may be done automatically, for certain element types.  For
     example all the word types have this happen through

       instance word :: (len8) array_outer_max_size
       instance word_length8 :: len8
       instance word_length16 :: len8
       instance word_length32 :: len8
       instance word_length64 :: len8

     Structures can't be done this way, so those need to get done by hand.

     Arrays get to use the

       instance array :: (array_inner_max_size, array_max_count) array_outer_max_size

     information.

  *)
in
  if Binaryset.member(#arrayeltypes_done st, el_ty) then (st, lthy)
  else let
      fun ex() = error ("Can't compute an element size class for " ^
                        Syntax.string_of_typ lthy el_ty)
      val (tyname, args) = case el_ty of Type p => p | _ => ex()
      val (st,lthy) =
          case args of
            [] => (* will be a record type *)
                  (st, lthy) |> prove_type_in_szclass el_ty @{class array_outer_max_size}
                  |> prove_packed_outer_inner el_ty @{class array_outer_packed}

          | [_] => (* can compute sizes for words and ptrs *)
            if tyname = @{type_name "Word.word"} then (st, lthy)
            else if tyname = @{type_name "CTypesBase.ptr"} then (st, lthy)
            else ex()
          | [a,_] => let
              val _ = tyname = @{type_name "array"} orelse
                      error "Binary type operator is not array."
              (* a is an element type and must be in array_inner_max_size *)
              val (atyname, aargs) = case a of Type p => p
                                             | _ => error "Array eltype is not Type"
            in
              case aargs of
                [] => (st, lthy)
                      |> prove_type_in_szclass a @{class array_inner_max_size}
                      |> prove_packed_outer_inner a @{class array_inner_packed}
              | [_] => if atyname = @{type_name "word"} orelse
                           atyname = @{type_name "ptr"}
                        then (st, lthy)
                        else error ("Unary operator type "^atyname^" not word or ptr")
              | _ => ex()
            end
          | _ => ex()
    in
      (add_array_done el_ty st, lthy)
    end
end




end; (* struct *)

