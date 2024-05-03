(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


theory UMM
  imports
   "Padding_Equivalence"
   "CLanguage"
begin
 
instantiation word :: (len8) stack_type
begin
instance
  by intro_classes (simp add: typ_info_word stack_typ_info_def stack_byte_name_def)
end

instantiation ptr :: (c_type) stack_type
begin
instance
  by intro_classes (simp add: typ_info_ptr stack_typ_info_def stack_byte_name_def )
end

lemma list_neq_witness: "x \<in> set ys \<Longrightarrow> x \<notin> set xs \<Longrightarrow> xs \<noteq> ys"
  by blast

lemma stack_typ_info_array_tag_n:
  "stack_typ_info ((array_tag_n n)::('a::{stack_type},'b::finite) array xtyp_info)"
  apply (induct n)
  subgoal
    apply (simp add: stack_typ_info_def atn_base stack_byte_name_def)
    apply (rule list_neq_witness [where x="CHR ''r''"])
     apply simp
    apply simp
    done
  apply (simp add: atn_rec)
  apply (rule stack_typ_info_ti_typ_combine')
  apply assumption
  done

instantiation array ::(stack_type, finite) stack_type
begin
instance
  by intro_classes (simp add: typ_info_array array_tag_def stack_typ_info_array_tag_n)
end

lemma max_non_zero_unfold: "NO_MATCH 0 a \<Longrightarrow> NO_MATCH 0 b \<Longrightarrow> max a b = (if a \<le> b then b else a)"
  by (simp add: max_def)

lemma eq_comp:
  assumes eq1: "field_update (component_desc x) bs v \<equiv> g"
  assumes eq2: "field_update (component_desc x) bs w \<equiv> g"
  shows "field_update (component_desc x) bs v = field_update (component_desc x) bs w"
  using eq1 eq2 by simp


lemma word_rcat_single: "word_rcat [x] = x"
  by (simp add: word_rcat_def bin_rcat_def)

lemma length_word_rsplit_8: "length ((word_rsplit (x::8 word)) :: 8 word list) = 1"
  by (simp add: word_rsplit_def bin_rsplit_def)
lemma length_word_rsplit_16: "length ((word_rsplit (x::16 word)) :: 8 word list) = 2"
  by (simp add: word_rsplit_def bin_rsplit_def)
lemma length_word_rsplit_32: "length ((word_rsplit (x::32 word)) :: 8 word list) = 4"
  by (simp add: word_rsplit_def bin_rsplit_def)
lemma length_word_rsplit_64: "length ((word_rsplit (x::64 word)) :: 8 word list) = 8"
  by (simp add: word_rsplit_def bin_rsplit_def)
lemma length_word_rsplit_128: "length ((word_rsplit (x::128 word)) :: 8 word list) = 16"
  by (simp add: word_rsplit_def bin_rsplit_def)

lemma length_word_rsplit_signed_8: "length ((word_rsplit (x::8 signed word)) :: 8 word list) = 1"
  by (simp add: word_rsplit_def bin_rsplit_def)
lemma length_word_rsplit_signed_16: "length ((word_rsplit (x::16 signed word)) :: 8 word list) = 2"
  by (simp add: word_rsplit_def bin_rsplit_def)
lemma length_word_rsplit_signed_32: "length ((word_rsplit (x::32 signed word)) :: 8 word list) = 4"
  by (simp add: word_rsplit_def bin_rsplit_def)
lemma length_word_rsplit_signed_64: "length ((word_rsplit (x::64 signed word)) :: 8 word list) = 8"
  by (simp add: word_rsplit_def bin_rsplit_def)
lemma length_word_rsplit_signed_128: "length ((word_rsplit (x::128 signed word)) :: 8 word list) = 16"
  by (simp add: word_rsplit_def bin_rsplit_def)

lemmas length_word_rsplit =
  length_word_rsplit_8
  length_word_rsplit_16
  length_word_rsplit_32
  length_word_rsplit_64
  length_word_rsplit_128
  length_word_rsplit_signed_8
  length_word_rsplit_signed_16
  length_word_rsplit_signed_32
  length_word_rsplit_signed_64
  length_word_rsplit_signed_128


lemmas wf_component_descs_intros =
  wf_component_descs_empty_typ_info
  wf_component_descs_final_pad
  wf_xfield.wf_component_descs_ti_typ_combine
  wf_xfield.wf_component_descs_ti_typ_pad_combine

lemmas component_descs_independent_intros =
  component_descs_independent_empty_typ_info
  component_descs_independent_final_pad
  wf_xfield.component_descs_independent_ti_typ_combine
  wf_xfield.component_desc_independent_ti_typ_pad_combine

lemmas wf_field_descs_intros =
  wf_field_descs_empty_typ_info
  wf_field_descs_final_pad
  wf_xfield.wf_field_descs_ti_typ_combine
  wf_xfield.wf_field_descs_ti_typ_pad_combine

lemmas contained_field_descs_intros =
  contained_field_descs_empty_typ_info
  contained_field_descs_final_pad
  contained_field_descs_ti_typ_combine
  contained_field_descs_ti_typ_pad_combine

lemmas field_update_simps =
 size_of_def ti_typ_pad_combine_def empty_typ_info_def ti_typ_combine_def ti_pad_combine_def
 final_pad_def padup_def Let_def


lemmas size_td_simps_arr_fl =
   size_td_simps
    size_td_array align_td_array max_def

method wf_xfield_solver =
 (intro_locales, rule wf_field.intro; simp add: comp_def)

method try_wf_xfield_solver methods m =
 (match conclusion in "wf_xfield acc upd" for acc upd \<Rightarrow> wf_xfield_solver | m)

method wf_component_descs_solver =
(try_wf_xfield_solver \<open>(rule wf_component_descs_intros)\<close>)+

(* don't evaluate (unfold) the type-tag just to get the toplevel field descs. make specialised rules, to
  select the toplevel field descs. *)
method field_desc_independent_solver =
(rule field_desc_independent_PAD_expand,
 simp only:  aggregate_typ_combinators_simps set_toplevel_field_descs_combinator_simps,
 (simp only: insert_union_out)?,
 rule field_desc_independent_PAD_collapse,
 rule field_desc_independent.intro;
 fastforce simp add: fu_commutes_def)


method component_descs_independent_solver =
 ( (try_wf_xfield_solver \<open>rule component_descs_independent_intros\<close>)+;
   field_desc_independent_solver)

method wf_field_descs_solver =
(try_wf_xfield_solver \<open>(rule wf_field_descs_intros)\<close>)+

method contained_field_descs_solver =
(rule contained_field_descs_intros)+

lemma unat_less_helper': "x < of_nat n \<equiv> True \<Longrightarrow> unat x < n"
  by (simp add: unat_less_helper)

lemma unat_less_helper_numeral:
  "x < (numeral n) \<Longrightarrow> unat x < (numeral n)"
  "x < 1 \<Longrightarrow> unat x < 1"
  by (simp_all add: unat_less_helper)

lemma unat_less_helper_numeral':
  "x < (numeral n) \<equiv> True \<Longrightarrow> unat x < (numeral n)"
  "x < 1 \<equiv> True \<Longrightarrow> unat x < 1"
  using unat_less_helper_numeral by blast+

lemma nat_sint_less_helper:
  "i <s of_nat n \<Longrightarrow> 0 \<le>s i \<Longrightarrow> (nat (sint i)) < n"
  by (simp add: sint_eq_uint unat_less_helper word_sle_msb_le word_sless_msb_less)

lemma nat_sint_less_helper':
  "i <s of_nat n \<equiv> True \<Longrightarrow> 0 \<le>s i \<equiv> True \<Longrightarrow> (nat (sint i)) < n"
  by (simp add: nat_sint_less_helper)

lemma nat_sint_less_helper_numeral: 
  "i <s (numeral n) \<Longrightarrow> 0 \<le>s i \<Longrightarrow> nat (sint i) < (numeral n)"
  "i <s 1 \<Longrightarrow> 0 \<le>s i \<Longrightarrow> nat (sint i) < 1"
  subgoal by (metis nat_uint_eq not_less signed.leD sint_eq_uint 
      unat_less_helper_numeral(1) word_msb_0 word_sle_msb_le)
  by (metis linorder_not_less nat_code(2) signed.leD signed_0 word_less_1 word_msb_0 word_sle_msb_le zero_less_one)

lemma nat_sint_less_helper_numeral': 
  "i <s (numeral n) \<equiv> True \<Longrightarrow> 0 \<le>s i \<equiv> True \<Longrightarrow> nat (sint i) < (numeral n)"
  "i <s 1 \<equiv> True \<Longrightarrow> 0 \<le>s i \<equiv> True \<Longrightarrow> nat (sint i) < 1"
  using nat_sint_less_helper_numeral by blast+

lemma sint_ucast_eq_uint':
    "\<lbrakk> LENGTH('a) < LENGTH('b)\<rbrakk>
            \<Longrightarrow> sint ((ucast :: ('a::len word \<Rightarrow> 'b::len word)) x) = uint x"
  apply (rule sint_ucast_eq_uint)
  apply (simp add: is_down_def target_size_def source_size_def)
  done

lemma sint_ucast_signed_eq_uint:
  "LENGTH('a) < LENGTH('b) \<Longrightarrow> sint (ucast (x :: 'a :: len word) :: 'b :: len signed word) = uint x"
  apply transfer
  apply (clarsimp simp add: signed_take_bit_take_bit)
  done


lemma ucast_unat_sless_helper: 
  "UCAST('a::len \<rightarrow> 'b::len signed) x <s of_nat n \<Longrightarrow> 
       LENGTH('a::len) < LENGTH('b::len) \<Longrightarrow> unat x < n"
  by (smt (verit, best) Word.of_nat_unat nat_int_comparison(2) of_nat_numeral 
      sint_ucast_signed_eq_uint unat_lt2p unat_of_nat_eq word_sless_sint_le)

lemma ucast_unat_sless_helper': 
  "UCAST('a::len \<rightarrow> 'b::len signed) x <s of_nat n \<equiv> True \<Longrightarrow> 
       LENGTH('a::len) < LENGTH('b::len) \<Longrightarrow> unat x < n"
  using ucast_unat_sless_helper by blast

lemma ucast_unat_sless_helper_numeral_n: 
  "UCAST('a::len \<rightarrow> 'b::len signed) x <s (numeral n) \<Longrightarrow> 
       LENGTH('a::len) < LENGTH('b::len) \<Longrightarrow> unat x < (numeral n)"
  using ucast_unat_sless_helper
  by (metis of_nat_numeral)

lemma ucast_unat_sless_helper_numeral_1:
  "UCAST('a::len \<rightarrow> 'b::len signed) x <s 1 \<Longrightarrow> 
       LENGTH('a::len) < LENGTH('b::len) \<Longrightarrow> unat x < 1"
  using ucast_unat_sless_helper
  by force

lemmas ucast_unat_sless_helper_numeral = 
  ucast_unat_sless_helper_numeral_n
  ucast_unat_sless_helper_numeral_1

lemma ucast_unat_sless_helper_numeral': 
  "UCAST('a::len \<rightarrow> 'b::len signed) x <s (numeral n) \<equiv> True \<Longrightarrow> 
       LENGTH('a::len) < LENGTH('b::len) \<Longrightarrow> unat x < (numeral n)"
  "UCAST('a::len \<rightarrow> 'b::len signed) x <s 1 \<equiv> True \<Longrightarrow> 
       LENGTH('a::len) < LENGTH('b::len) \<Longrightarrow> unat x < 1"
  using ucast_unat_sless_helper_numeral by blast+

lemma ucast_unat_less_helper: 
  "UCAST('a::len \<rightarrow> 'b::len) x < of_nat n \<Longrightarrow> 
   LENGTH('a::len) \<le> LENGTH('b::len) \<Longrightarrow> unat x < n"
  by (metis unat_less_helper unat_ucast_up_simp)

lemma ucast_unat_less_helper': 
  "UCAST('a::len \<rightarrow> 'b::len) x < of_nat n \<equiv> True \<Longrightarrow> 
   LENGTH('a::len) \<le> LENGTH('b::len) \<Longrightarrow> unat x < n"
  using ucast_unat_less_helper by blast

lemma ucast_unat_less_helper_numeral_n: 
  "UCAST('a::len \<rightarrow> 'b::len) x < (numeral n) \<Longrightarrow> 
   LENGTH('a::len) \<le> LENGTH('b::len) \<Longrightarrow> unat x < (numeral n)"
  using ucast_unat_less_helper
  by (metis of_nat_numeral)

lemma ucast_unat_less_helper_numeral_1: 
  "UCAST('a::len \<rightarrow> 'b::len) x < 1 \<Longrightarrow> 
   LENGTH('a::len) \<le> LENGTH('b::len) \<Longrightarrow> unat x < 1"
  using ucast_unat_less_helper
  by force

lemmas ucast_unat_less_helper_numeral = 
  ucast_unat_less_helper_numeral_n
  ucast_unat_less_helper_numeral_1

lemma ucast_unat_less_helper_numeral': 
  "UCAST('a::len \<rightarrow> 'b::len) x < (numeral n) \<equiv> True \<Longrightarrow> 
   LENGTH('a::len) \<le> LENGTH('b::len) \<Longrightarrow> unat x < (numeral n)"
  "UCAST('a::len \<rightarrow> 'b::len) x < 1 \<equiv> True \<Longrightarrow> 
   LENGTH('a::len) \<le> LENGTH('b::len) \<Longrightarrow> unat x < 1"
  using ucast_unat_less_helper_numeral by blast+

lemma len_of_less_basic_cases: 
  "LENGTH(8) < LENGTH(16)"
  "LENGTH(8) < LENGTH(32)"
  "LENGTH(8) < LENGTH(64)"
  "LENGTH(8) < LENGTH(128)"
  "LENGTH(16) < LENGTH(32)"
  "LENGTH(16) < LENGTH(64)"
  "LENGTH(16) < LENGTH(128)"
  "LENGTH(32) < LENGTH(64)"
  "LENGTH(32) < LENGTH(128)"
  "LENGTH(64) < LENGTH(128)"
  by simp_all

lemma len_of_le_basic_cases: 
  "LENGTH(8) \<le> LENGTH(16)"
  "LENGTH(8) \<le> LENGTH(32)"
  "LENGTH(8) \<le> LENGTH(64)"
  "LENGTH(8) \<le> LENGTH(128)"
  "LENGTH(16) \<le> LENGTH(32)"
  "LENGTH(16) \<le> LENGTH(64)"
  "LENGTH(16) \<le> LENGTH(128)"
  "LENGTH(32) \<le> LENGTH(64)"
  "LENGTH(32) \<le> LENGTH(128)"
  "LENGTH(64) \<le> LENGTH(128)"
  by simp_all

ML \<open>

structure UMM_Tools =
struct
fun tactic_from_method (m:Proof.context -> Method.method) ctxt thms st =
   (m ctxt thms (ctxt, st)) |> Seq.filter_results |> Seq.map snd

fun tactic_from_src ctxt src =
let
  val (_, tok) = Method.read_closure_input ctxt src
  val m = Method.method ctxt tok
in tactic_from_method m end

val wf_component_descs_tac = tactic_from_src @{context} \<open>wf_component_descs_solver\<close>
val component_descs_independent_tac = tactic_from_src @{context} \<open>component_descs_independent_solver\<close>
val wf_field_descs_tac = tactic_from_src @{context} \<open>wf_field_descs_solver\<close>
val contained_field_descs_tac = tactic_from_src @{context} \<open>contained_field_descs_solver\<close>

end

\<close>


ML \<open>val UMM_ss = simpset_of \<^context>\<close>


lemma heap_update_fold_comp_apply : "heap_update p v (g z) \<equiv> (heap_update p v \<circ> g) z"
  by (simp add: comp_apply)


named_theorems
  fg_cons_simps and
  typ_info_simps and
  td_names_simps and
  typ_name_simps and
  upd_lift_simps and
  upd_other_simps and
  size_align_simps and
  fl_Some_simps and
  fl_ti_simps and
  sub_typ_simps and
  typ_tag_defs and
  size_simps and
  typ_name_itself and
  heap_update_fold_toplevel_fields and
  heap_update_fold_toplevel_fields_pointless and
  h_val_fields and heap_update_fields and
  h_val_unfold

named_theorems field_lookup_prems (* additional prems for some simprocs *)

declare
  size_of_words[size_simps]
  size_of_swords[size_simps]
  size_of_array[size_simps]
  size_of_stack_byte[size_simps]
  size_of_ptr[size_simps]

lemma field_of_lookup_info:
  fixes p::"'a:: mem_type ptr"
  assumes field: "field_of off (typ_uinfo_t TYPE('b::mem_type)) (typ_uinfo_t TYPE('a))"
  shows "\<exists>f. f \<in> set (field_names_u (typ_uinfo_t TYPE('a)) (typ_uinfo_t TYPE('b))) \<and>
             field_lookup (typ_uinfo_t TYPE('a)) f 0 = Some (typ_uinfo_t TYPE('b), unat off) \<and>
             field_of_t (PTR('b) &(p\<rightarrow>f)) p \<and>
             &(p\<rightarrow>f) = ptr_val (p::'a ptr) + off \<and>
             {&(p\<rightarrow>f)..+size_td (typ_uinfo_t TYPE('b))} \<subseteq> ptr_span p"
proof -
  have "wf_desc (typ_info_t TYPE('a))" by (rule wf_desc)

  from td_set_field_lookup [OF wf_desc_export_uinfo_pres(1) [OF this]] field
  obtain f where lookup_u: "field_lookup (typ_uinfo_t TYPE('a)) f 0 = Some (typ_uinfo_t TYPE('b), unat off)"
    by (auto simp add: field_of_def typ_uinfo_t_def)
  from field_lookup_export_uinfo_Some_rev [OF lookup_u [simplified typ_uinfo_t_def]]
  obtain s' where lookup: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s', unat off)" and
       exp_s': "export_uinfo (typ_info_t TYPE('b)) = export_uinfo s'"
    by blast
  from field_names_SomeD3 [OF lookup]
  have f_in: "f \<in> set (field_names_u (typ_uinfo_t TYPE('a)) (typ_uinfo_t TYPE('b)))"
    by (simp add: field_names_u_field_names_export_uinfo_conv (1) [symmetric] typ_uinfo_t_def exp_s')

  from lookup
  have addr: "&(p\<rightarrow>f) = ptr_val (p::'a ptr) + off"
    by (simp add: field_lvalue_def)
  from field_tag_sub [OF lookup]
  have contained: "{&(p\<rightarrow>f)..+size_td (typ_uinfo_t TYPE('b))} \<subseteq> ptr_span p"
    by (simp add: exp_s' typ_uinfo_t_def)

  from field addr
  have "field_of_t (PTR('b) &(p\<rightarrow>f)) p"
    by (simp add: field_of_t_def field_of_def)

  with contained addr lookup_u f_in
  show ?thesis
    by blast
qed

lemma sub_typ_field_names_u_nonempty:
  assumes s_t: "s \<le> t"
  shows "field_names_u t s \<noteq> []"
proof -
  from s_t obtain n where "(s, n) \<in> td_set t 0"
    by (auto simp add: typ_tag_le_def)
  from td_set_field_names_u_nonempty (1) [OF this] show ?thesis.
qed

definition "TO_SUC (n::nat) \<equiv> n"

simproc_setup TO_SUC (\<open>TO_SUC (numeral x)\<close>) = \<open>
fn phi => fn ctxt => fn ct =>
  SOME (Simplifier.rewrite (ctxt addsimps @{thms TO_SUC_def Num.numeral_nat}) ct)
\<close>
declare [[simproc del: TO_SUC]]

lemma array_tag_SUC:
"array_tag (t::('a::c_type,'b::finite) array itself) = array_tag_n (TO_SUC (CARD('b)))"
  by (simp add: array_tag_def TO_SUC_def)

lemma field_lookup_cons: "field_lookup t [f] m = Some (t', n) \<Longrightarrow> wf_desc t \<Longrightarrow>
  field_lookup t (f # g # gs) m = field_lookup t' (g#gs) n"
  using field_lookup_prefix_Some''(1)[rule_format, where f = "[f]" and g = "g#gs"]
  by auto

lemma field_lookup_cons':
  "field_lookup (typ_info_t (TYPE('a::mem_type))) [f] m = Some (t', n) \<Longrightarrow>
  field_lookup (typ_info_t (TYPE('a::mem_type))) (f # g # gs) m = field_lookup t' (g#gs) n"
  by (simp add: field_lookup_cons)

lemma exists_conj_disj: "P \<Longrightarrow> (\<exists>n. (P \<and> Q n) \<or> R n) = (\<exists>n. Q n \<or> R n) "
  by blast

lemma abs_if_eq:
  assumes "\<And>x. b x \<Longrightarrow> f1 x = f2 x"
  assumes "\<And>x. \<not> b x \<Longrightarrow> g1 x = g2 x"
  shows "(\<lambda>x. if b x then f1 x else g1 x) = (\<lambda>x. if b x then f2 x else g2 x) \<longleftrightarrow> True"
  using assms
  by metis

lemma field_lookup_typ_uinfo_t_Some:
"field_lookup (typ_info_t TYPE('a::c_type)) f m = Some (s, n) \<Longrightarrow>
field_lookup (typ_uinfo_t TYPE('a)) f m = Some (export_uinfo s, n)"
  by (simp add: typ_uinfo_t_def field_lookup_export_uinfo_Some)

lemma adjust_ti_wf_fd_pres':
  fixes t::"'a xtyp_info"
  and st::"'a xtyp_info_struct"
  and ts::"'a xtyp_info_tuple list"
  and x::"'a xtyp_info_tuple"
  assumes fg_cons: "fg_cons acc upd"
shows
 "wf_fd t \<Longrightarrow>
    wf_fd (map_td (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) t)"
 "wf_fd_struct st \<Longrightarrow>
    wf_fd_struct (map_td_struct (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) st)"
 "wf_fd_list ts \<Longrightarrow>
    wf_fd_list (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) ts)"
 "wf_fd_tuple x \<Longrightarrow>
    wf_fd_tuple (map_td_tuple (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) x)"
proof (induct t and st and ts and x )
case (TypDesc algn st nm)
then show ?case by auto
next
case (TypScalar  algn st d)
  then show ?case 
    apply simp
    apply (simp add: fd_cons_struct_def)
    apply (insert fg_cons)
    apply (simp add: fd_cons_desc_def fg_cons_def)
    apply safe
    subgoal
      by (auto simp add: fd_cons_double_update_def update_desc_def)
        presburger
    subgoal
      by (auto simp add: fd_cons_update_access_def update_desc_def)
        presburger
    subgoal
      by (auto simp add: fd_cons_access_update_def update_desc_def)
    subgoal
      by (auto simp add: fd_cons_length_def update_desc_def)
    done
next
  case (TypAggregate ts)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc x fs)
  obtain d nm y where x: "x = DTuple d nm y" by (cases x) auto

  from Cons_typ_desc.prems obtain
    wf_fd_d: "wf_fd d" and
    wf_fd_fs: "wf_fd_list fs" and
    commutes_d_fs: "fu_commutes (update_ti_t d) (update_ti_list_t fs)" and
    fa_fu_ind_d_fs: "fa_fu_ind
     \<lparr>field_access = access_ti d, field_update = update_ti_t d, field_sz = size_td d\<rparr>
     \<lparr>field_access = access_ti_list fs, field_update = update_ti_list_t fs,
        field_sz = size_td_list fs\<rparr>
     (size_td_list fs) (size_td d)" and
    fa_fu_ind_fs_d: "fa_fu_ind
     \<lparr>field_access = access_ti_list fs, field_update = update_ti_list_t fs,
        field_sz = size_td_list fs\<rparr>
     \<lparr>field_access = access_ti d, field_update = update_ti_t d, field_sz = size_td d\<rparr>
     (size_td d) (size_td_list fs)"
     by (simp add: x)

   note hyps = Cons_typ_desc.hyps [simplified x, simplified]
   note hyp_d = hyps(1) [OF  wf_fd_d]
   note hyp_fs = hyps(2) [OF wf_fd_fs]
  show ?case
    apply (simp add: x hyp_d hyp_fs)
    apply safe
    subgoal
      using commutes_d_fs fg_cons
      apply (simp add: fu_commutes_def fg_cons_def)
      by auto (* takes a few seconds *)
        (smt (verit) adjust_ti_def fg_cons field_desc.select_convs(2) field_desc_adjust_ti(3) field_desc_list_def
          map_td_ext'(3) map_td_extI update_desc_def update_ti_t_adjust_ti wf_fd_d wf_fd_fs)
    subgoal
      using fa_fu_ind_d_fs fg_cons
      apply (simp add: fa_fu_ind_def fg_cons_def)
      apply clarsimp
      by (smt (verit) \<open>fu_commutes (update_ti_t (map_td (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) d)) (update_ti_list_t (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) fs))\<close>
          fa_fu_v fd_cons_length fd_cons_update_access fu_commutes_def hyp_d map_td_size(1) wf_fd_consD)
    subgoal
      using fa_fu_ind_fs_d fg_cons
      apply (simp add: fa_fu_ind_def fg_cons_def)
      apply clarsimp
      by (metis adjust_ti_def fg_cons update_ti_t_adjust_ti)
    done
next
  case (DTuple_typ_desc d nm y)
  then show ?case by auto
qed


lemma adjust_ti_wf_fd_pres[simp]: "fg_cons acc upd \<Longrightarrow> wf_fd t \<Longrightarrow> wf_fd (adjust_ti t acc upd)"
  by (simp add: adjust_ti_wf_fd_pres' adjust_ti_def)

lemma neq_td_names_eq_neq_export_uinfo: "td_names (typ_info_t t) \<noteq> td_names (typ_info_t s)
  \<Longrightarrow> export_uinfo (typ_info_t t) = export_uinfo (typ_info_t s) \<longleftrightarrow> False"
  by (metis td_names_export_uinfo)

lemma set_field_names_no_padding_all_field_names_no_padding_conv':
"set (field_names_no_padding (typ_info_t TYPE('a::mem_type)) t) =
 Set.filter
  (\<lambda>f. \<exists>s n. field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n) \<and> export_uinfo s = t)
  (set (all_field_names_no_padding (typ_info_t TYPE('a))))"
  by (simp add: set_field_names_no_padding_all_field_names_no_padding_conv Set.filter_def)

lemma field_names_no_padding_all_field_names_no_padding_conv':
"field_names_no_padding (typ_info_t TYPE('a::mem_type)) t =
 filter
  (\<lambda>f. \<exists>s n. field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n) \<and> export_uinfo s = t)
  (all_field_names_no_padding (typ_info_t TYPE('a)))"
  by (simp add: field_names_no_padding_all_field_names_no_padding_conv Set.filter_def)

lemma set_filter_insert: "Set.filter P (insert x S) =
   (if P x then insert x (Set.filter P S) else Set.filter P S)"
  by (auto simp add: Set.filter_def)

lemma set_filter_cons_image: "Set.filter P ((#) x ` S) = (#) x ` Set.filter (\<lambda>fs.  P (x#fs)) S"
  by (auto simp add: Set.filter_def)

lemma set_filter_Sup: "Set.filter P (\<Union>x\<in>X. S x) = (\<Union>x\<in>X. Set.filter P (S x))"
  by (auto simp add: Set.filter_def)

lemma set_filter_empty: "Set.filter P {} = {}"
  by (auto simp add: Set.filter_def)

lemma cons_image_Sup: "(#) x ` (\<Union>xs\<in>X. S xs) = (\<Union>xs\<in>X. ((#) x ` S xs))"
  by (rule image_UN)

lemma set_filter_image_all:
  assumes "\<And>x. x < n \<Longrightarrow> P (f x)"
  shows "Set.filter P (f ` {0..<n}) =  f ` {0..<n}"
  using assms
  by fastforce

lemma set_filter_image_none:
  assumes "\<And>x. x < n \<Longrightarrow> \<not> P (f x)"
  shows "Set.filter P (f ` {0..<n}) =  {}"
  using assms
  by fastforce

lemma set_filter_union_distrib: "Set.filter P (X \<union> Y) = Set.filter P X \<union> Set.filter P Y"
  by (auto simp add: Set.filter_def)

lemma sub_typ_refl [simp]: "TYPE('a) \<le>\<^sub>\<tau> TYPE('a::c_type)"
  by (simp add: sub_typ_def)

lemma not_sub_typ_via_td_name:
  assumes ta: "typ_name (typ_info_t TYPE('a :: c_type)) \<noteq> pad_typ_name"
  and   tina: "typ_name (typ_info_t TYPE('a :: c_type)) \<notin> td_names (typ_info_t TYPE('b :: c_type))"
shows   "\<not> TYPE('a :: c_type) \<le>\<^sub>\<tau> TYPE('b :: c_type)"
  using ta tina
  apply (clarsimp simp add: sub_typ_def typ_tag_le_def)
  apply (drule td_set_td_names)
   apply (auto simp add: typ_uinfo_t_def )
  done

lemma nat_to_bin_string_eq_to_nat_eq:
  assumes eq: "nat_to_bin_string n = nat_to_bin_string m"
shows "n = m"
  using eq
proof (induct n  arbitrary: m rule: nat_less_induct)
  case (1 n)
  then obtain eq: "nat_to_bin_string n = nat_to_bin_string m" and
    hyp: "\<And>m x. m < n \<Longrightarrow>  nat_to_bin_string m = nat_to_bin_string x \<Longrightarrow> m = x"
    by auto

  show ?case
  proof (cases n)
    case 0
    with eq show ?thesis
      apply(cases m)
       apply (simp add: ntbs)
      apply (simp add: ntbs)
      by (metis list.simps(3))
  next
    case (Suc n')
    note n' = this
    show ?thesis
    proof (cases m)
      case 0
      with eq show ?thesis
        apply (simp add: n' ntbs)
        by (meson list.simps(3))
    next
      case (Suc m')
      have le: "(Suc n' div 2) < n"
        by (simp add: n')

      note hyp' = hyp [OF le, of "Suc m' div 2"]
      from eq show ?thesis
        apply (simp add: n' Suc)
        apply (subst (asm) (1 2) ntbs)
        apply clarsimp
        apply (frule hyp')
        apply (clarsimp split: if_split_asm)
         apply arith+
        done
    qed
  qed
qed

lemma nat_to_bin_string_inj [simp]: "nat_to_bin_string n = nat_to_bin_string m \<longleftrightarrow> n = m"
  using nat_to_bin_string_eq_to_nat_eq by blast

simproc_setup nat_to_bin_string (\<open>nat_to_bin_string (numeral x)\<close>) = \<open>
fn phi => fn ctxt => fn ct =>
  SOME (Simplifier.rewrite (ctxt addsimps @{thms nat_to_bin_string.simps}) ct)
\<close>

lemma rewrite_solve_prop:
  assumes rew: "(PROP P) \<equiv> Trueprop Q"
  assumes solve: "PROP Trueprop Q"
  shows "(PROP P) \<equiv> Trueprop True"
proof -
  from solve have "Q = True" by simp
  from rew [simplified this]
  show "PROP ?thesis"
    by simp
qed

lemma trueprop_eq_bool_eq:
  assumes prop_eq: "PROP Trueprop P \<equiv> PROP Trueprop Q"
  shows "P = Q"
proof (cases P)
  case True
  with prop_eq have "Q"
    by (simp add: True)
  with True show ?thesis by simp
next
  case False
  with prop_eq have "Q = False"
    by (cases Q) auto
  with False show ?thesis by simp
qed

lemmas rewrite_solve_prop_eq = eq_reflection [OF trueprop_eq_bool_eq, OF rewrite_solve_prop]
lemmas trueprop_eq_bool_meta_eq = trueprop_eq_bool_eq [THEN eq_reflection]

lemma export_uinfo_typ_uinfo_t_match[simp]:
  "export_uinfo (typ_info_t TYPE('a)) = typ_uinfo_t (t::'a::c_type itself) = True"
  by (simp add: typ_uinfo_t_def)

lemma export_uinfo_eq_sub_typ_conv:
  "export_uinfo (typ_info_t TYPE('a::c_type)) = export_uinfo (typ_info_t TYPE('b::c_type))
      \<longleftrightarrow>
      TYPE('a) \<le>\<^sub>\<tau> TYPE('b) \<and> TYPE('b) \<le>\<^sub>\<tau> TYPE ('a)"
  apply standard
   apply (simp add: fold_typ_uinfo_t sub_typ_def)
  by (simp add: dual_order.antisym fold_typ_uinfo_t sub_typ_def)

lemma typ_uinfo_eq_sub_typ_conv:
  "typ_uinfo_t TYPE('a::c_type) = export_uinfo (typ_info_t TYPE('b::c_type))
      \<longleftrightarrow>
      TYPE('a) \<le>\<^sub>\<tau> TYPE('b) \<and> TYPE('b) \<le>\<^sub>\<tau> TYPE ('a)"
  "export_uinfo (typ_info_t TYPE('a::c_type)) = typ_uinfo_t TYPE('b::c_type)
      \<longleftrightarrow>
      TYPE('a) \<le>\<^sub>\<tau> TYPE('b) \<and> TYPE('b) \<le>\<^sub>\<tau> TYPE ('a)"
  "typ_uinfo_t TYPE('a::c_type) = typ_uinfo_t TYPE('b::c_type)
      \<longleftrightarrow>
      TYPE('a) \<le>\<^sub>\<tau> TYPE('b) \<and> TYPE('b) \<le>\<^sub>\<tau> TYPE ('a)"
  by (simp_all add: typ_uinfo_t_def export_uinfo_eq_sub_typ_conv)

lemma array_typ_subtyp_array_typ: 
  assumes "typ_uinfo_t (TYPE ('a::mem_type)) = typ_uinfo_t (TYPE('c::mem_type))"
  shows "typ_uinfo_t (TYPE ('a::mem_type['b::finite])) = typ_uinfo_t (TYPE('c['b::finite]))"
  apply (simp add: typ_uinfo_array_tag_n_m_eq)
  apply (simp add:  uinfo_array_tag_n_m_def)
  using assms
  by simp

lemma le_array_typ_intro: 
  "TYPE ('a::mem_type) \<le>\<^sub>\<tau> TYPE ('c::mem_type) \<Longrightarrow> 
  TYPE ('c::mem_type) \<le>\<^sub>\<tau> TYPE ('a::mem_type) \<Longrightarrow>
  TYPE('a::mem_type['b::finite]) \<le>\<^sub>\<tau> TYPE('c::mem_type['b::finite])"
  using typ_uinfo_eq_sub_typ_conv array_typ_subtyp_array_typ
  by (smt (verit))

lemma sub_typ_signed_unsiged: "TYPE('a::len8 signed word) \<le>\<^sub>\<tau> TYPE('a word)"
  by (simp add: sub_typ_def typ_uinfo_t_signed_word_word_conv)

lemma sub_typ_unsigned_signed: "TYPE('a word) \<le>\<^sub>\<tau> TYPE('a::len8 signed word)"
  by (simp add: sub_typ_def typ_uinfo_t_signed_word_word_conv)

lemma sub_typ_proper_conv: "TYPE('a::c_type) <\<^sub>\<tau> TYPE('b::c_type) \<longleftrightarrow>
       typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b) \<and> TYPE('a::c_type) \<le>\<^sub>\<tau> TYPE('b::c_type)"
  by (metis sub_typ_def sub_typ_proper_def typ_tag_lt_def)

lemma sub_typ_proper_to_sub_typ:
  "TYPE('a::c_type) <\<^sub>\<tau> TYPE('b::c_type) \<Longrightarrow> TYPE('a::c_type) \<le>\<^sub>\<tau> TYPE('b::c_type)"
  using sub_typ_proper_conv by blast

lemma to_bytes_p_zero: "to_bytes_p (c_type_class.zero::'a::xmem_type) = replicate (size_of TYPE('a)) 0"
  by (simp add: zero_def to_bytes_p_def to_bytes_from_bytes_id)

lemma field_lookup_zero:
  assumes fl: "field_lookup (typ_info_t TYPE('a::xmem_type)) f 0 = Some (t, n)"
  assumes match: "export_uinfo t = typ_uinfo_t TYPE('b::c_type)"
  shows "from_bytes (access_ti\<^sub>0 t (c_type_class.zero::'a)) = (c_type_class.zero::'b)"
proof -
  from field_access_take_dropD [OF fl, simplified]
  have eq1: "take (size_td t) (drop n (to_bytes_p (c_type_class.zero::'a))) = access_ti\<^sub>0 t (c_type_class.zero::'a)" by simp

  from fl match have sz: "size_td t = size_of TYPE('b)"
    by (simp add: export_size_of)
  from fl have le: "size_of TYPE('b) \<le> size_of TYPE('a) - n"
    by (metis export_size_of field_lookup_offset_size fold_typ_uinfo_t nat_move_sub_le sz)

  have "take (size_td t) (drop n (to_bytes_p (c_type_class.zero::'a))) = replicate (size_of TYPE('b)) 0"
    by (simp add:  to_bytes_p_zero sz le)
  with eq1 have eq2: "access_ti\<^sub>0 t (c_type_class.zero::'a) = replicate (size_of TYPE('b)) 0" by simp
  show ?thesis
    apply (simp add: eq2)
    apply (simp add: zero_def)
    done
qed


lemma field_lookup_zero':
  assumes fl: "field_lookup (typ_info_t TYPE('a::xmem_type)) f 0 \<equiv> Some (t, n)"
  assumes match: "export_uinfo t = export_uinfo (typ_info_t TYPE('b::c_type))"
  shows "from_bytes (access_ti\<^sub>0 t (c_type_class.zero::'a)) = (c_type_class.zero::'b)"
  using field_lookup_zero [simplified typ_uinfo_t_def, OF _ match] fl by blast

lemma array_index_zero:
  assumes i_bound: "i  < CARD('b)"
  shows "(c_type_class.zero::(('a :: array_outer_max_size)['b :: array_max_count])).[i] = (c_type_class.zero::'a)"
proof -
  from field_lookup_array  [OF i_bound, where 'a='a ]
  have fl: "field_lookup (typ_info_t TYPE('a['b])) [replicate i CHR ''1''] 0 =
         Some (adjust_ti (typ_info_t TYPE('a)) (\<lambda>x. x.[i]) (\<lambda>x f. Arrays.update f i x), i * size_of TYPE('a))"
    by simp

  have "export_uinfo (adjust_ti (typ_info_t TYPE('a)) (\<lambda>x::'a['b]. x.[i]) (\<lambda>x f. Arrays.update f i x)) = typ_uinfo_t TYPE('a)"
    by (simp add: typ_uinfo_t_def i_bound)


  from field_lookup_zero [OF fl this]
  show ?thesis
    by simp
qed

named_theorems zero_simps and make_zero
end