(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * This file contains theorems for dealing with a "simply" lifted
 * heap, where each byte of memory can be accessed as one (and only)
 * type.
 *
 * This is a simpler model of Tuch's "lift_t" model, where nested
 * struct fields cannot be directly accessed as pointers.
 *)

chapter \<open>IO phase: In/Out Parameters\<close>

section \<open>Heap Typing for Split Heap\<close>
theory TypHeapSimple
  imports 
    "AutoCorres_Base"
begin

section \<open>Valid root footprint\<close>

lemma c_null_guard_size_of_limit:
  "c_null_guard (p::'a::c_type ptr) \<Longrightarrow> size_td (typ_uinfo_t (TYPE('a))) < 2 ^ len_of TYPE(addr_bitsize) "
  unfolding c_null_guard_def size_of_def
  by (metis (no_types, opaque_lifting) add.commute add_diff_cancel_left' add_lessD1 
     cancel_comm_monoid_add_class.diff_cancel first_in_intvl nat_less_le nat_neq_iff 
     not_add_less1 typ_uinfo_size unat_lt2p unsigned_eq_0_iff zero_not_in_intvl_no_overflow)

lemma root_ptr_valid_legacy_def: "root_ptr_valid d p \<longleftrightarrow>
      valid_root_footprint d (ptr_val (p::'a ptr)) (typ_uinfo_t TYPE('a)) \<and>
      valid_simple_footprint d (ptr_val (p::'a::c_type ptr)) (typ_uinfo_t TYPE('a)) \<and> 
      d, c_guard \<Turnstile>\<^sub>t p"
  using c_null_guard_size_of_limit [of p]
  by (auto simp add: root_ptr_valid_def  c_guard_def addr_card_len_of_conv
    h_t_valid_def valid_root_footprint_valid_footprint intro!:  valid_root_footprint_valid_simple_footprint)


(* What I want is: root_ptr_valid d p \<longrightarrow>  d,c_guard \<Turnstile>\<^sub>t p *)
(*
 * Lift a heap from raw bytes and a heap description into
 * higher-level objects.
 *
 * This differs from Tuch's "lift_t" because we only support
 * simple lifting; that is, each byte in the heap may only
 * be accessed as a single type. Accessing struct fields by
 * their pointers is not supported.
 *)
definition
  simple_lift :: "heap_raw_state \<Rightarrow> ('a::c_type) ptr \<Rightarrow> 'a option"
where
  "simple_lift s p = (
     if (root_ptr_valid (hrs_htd s) p) then
       (Some (h_val (hrs_mem s) p))
     else
       None)"

lemma simple_lift_root_ptr_valid:
  "simple_lift s p = Some x \<Longrightarrow> root_ptr_valid (hrs_htd s) p"
  apply (clarsimp simp: simple_lift_def split: if_split_asm)
  done

lemma simple_lift_h_t_valid:
  "simple_lift s p = Some x \<Longrightarrow> (hrs_htd s), c_guard \<Turnstile>\<^sub>t p"
  apply (clarsimp simp: simple_lift_def root_ptr_valid_legacy_def split: if_split_asm)
  done

lemma simple_lift_valid_root_footprint:
  "simple_lift s (p::'a::c_type ptr) = Some x \<Longrightarrow> valid_root_footprint (hrs_htd s) (ptr_val p) (typ_uinfo_t (TYPE('a)))"
  apply (clarsimp simp: simple_lift_def root_ptr_valid_def split: if_split_asm)
  done

lemma simple_lift_c_guard:
  assumes lift: "simple_lift s p = Some x" 
  shows "c_guard p"
  using simple_lift_h_t_valid [OF lift]
  by (simp add: h_t_valid_def)




(* If we update one pointer in the heap, other valid pointers will be unaffected. *)
lemma root_ptr_valid_heap_update_other:
  assumes val_p: "root_ptr_valid d (p::'a::mem_type ptr)"
      and val_q: "root_ptr_valid d (q::'b::c_type ptr)"
      and neq: "ptr_val p \<noteq> ptr_val q"
  shows "h_val (heap_update p v h) q = h_val h q"
  apply (clarsimp simp: h_val_def heap_update_def)
  apply (subst heap_list_update_disjoint_same)
   apply simp
   apply (rule root_ptr_valid_neq_disjoint [OF val_p val_q neq])
  apply simp
  done

(* If we update one type in the heap, other types will be unaffected. *)
lemma root_ptr_valid_heap_update_other_typ:
  assumes val_p: "root_ptr_valid d (p::'a::mem_type ptr)"
      and val_q: "root_ptr_valid d (q::'b::c_type ptr)"
      and neq: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b)"
  shows "h_val (heap_update p v h) q = h_val h q"
  apply (clarsimp simp: h_val_def heap_update_def)
  apply (subst heap_list_update_disjoint_same)
   apply simp
   apply (rule root_ptr_valid_type_neq_disjoint [OF val_p val_q neq])
  apply simp
  done

(* Updating the raw heap is equivalent to updating the lifted heap. *)
lemma simple_lift_heap_update:
  "\<lbrakk> root_ptr_valid (hrs_htd h) p \<rbrakk> \<Longrightarrow>
      simple_lift (hrs_mem_update (heap_update p v) h)
          = (simple_lift h)(p := Some (v::'a::mem_type))"
  apply (rule ext)
  apply (clarsimp simp: simple_lift_def hrs_mem_update h_val_heap_update)
  apply (fastforce simp: root_ptr_valid_heap_update_other)
  done

(* Updating the raw heap of one type doesn't affect the lifted heap of other types. *)
lemma simple_lift_heap_update_other:
  "\<lbrakk> root_ptr_valid (hrs_htd d) (p::'b::mem_type ptr);
     typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b) \<rbrakk> \<Longrightarrow>
   simple_lift (hrs_mem_update (heap_update p v) d) = ((simple_lift d)::'a::c_type typ_heap)"
  apply (rule ext)+
  apply (clarsimp simp: simple_lift_def h_val_heap_update hrs_mem_update)
  apply (auto intro: root_ptr_valid_heap_update_other_typ)
  done



lemma h_val_simple_lift:
  "simple_lift h p = Some v \<Longrightarrow> h_val (hrs_mem h) p = v"
  apply (clarsimp simp: simple_lift_def split: if_split_asm)
  done

lemma the_simple_lift_h_val_conv:
  "root_ptr_valid (hrs_htd h) p \<Longrightarrow> the (simple_lift h p) = h_val (hrs_mem h) p"
  apply (clarsimp simp: simple_lift_def split: if_split_asm)
  done

lemma slift_clift_Some_same: 
assumes slift: "simple_lift s p = Some x" 
assumes clift: "clift s p = Some y" 
shows "x = y"
  using h_val_simple_lift [OF slift] h_val_clift' [OF clift]
  by simp

lemma simple_lift_Some_clift_Some:
  assumes slift: "simple_lift s p = Some x" 
  shows "clift s p = Some x"
  using simple_lift_h_t_valid [OF slift] h_t_valid_clift_Some_iff slift_clift_Some_same [OF slift]
  by (cases s) auto

lemma h_val_field_simple_lift:
  "\<lbrakk> simple_lift h (pa :: 'a ptr) = Some (v::'a::mem_type);
     field_ti TYPE('a) f = Some t;
     export_uinfo (the (field_ti TYPE('a) f)) = export_uinfo (typ_info_t TYPE('b :: mem_type)) \<rbrakk> \<Longrightarrow>
   h_val (hrs_mem h) (Ptr &(pa\<rightarrow>f) :: 'b :: mem_type ptr) = from_bytes (access_ti\<^sub>0 (the (field_ti TYPE('a) f)) v)"
  apply (clarsimp simp: simple_lift_def split: if_split_asm)
  apply (clarsimp simp: h_val_field_from_bytes)
  done

lemma simple_lift_heap_update':
  "simple_lift h p = Some v' \<Longrightarrow>
      simple_lift (hrs_mem_update (heap_update (p::('a::{mem_type}) ptr) v) h)
          = (simple_lift h)(p := Some v)"
  apply (rule simple_lift_heap_update)
  apply (erule simple_lift_root_ptr_valid)
  done


lemma simple_lift_hrs_mem_update_None [simp]:
    "(simple_lift (hrs_mem_update a hp) x = None) = (simple_lift hp x = None)"
  apply (clarsimp simp: simple_lift_def)
  done

lemma simple_lift_hrs_mem_update_Some: " (\<exists>z. simple_lift (hrs_mem_update upd h) x = Some z)
    \<longleftrightarrow>  (\<exists>z. simple_lift h x = Some z)"

  apply (cases "simple_lift h x")
   apply simp
   apply (cases "simple_lift (hrs_mem_update upd h) x")
   apply (auto)
  done

lemma clift_hrs_mem_update_None [simp]:
    "(clift (hrs_mem_update a hp) x = None) = (clift hp x = None)"
  using h_t_valid_clift_Some_iff 
  apply (cases hp)
  apply (clarsimp simp add: hrs_mem_update)
  apply (metis hrs_htd_def hrs_htd_mem_update lift_t_if option.distinct(1) prod.collapse)+
  done

lemma clift_hrs_mem_update_Some:
    "(\<exists>z. clift (hrs_mem_update a hp) x = Some z) = (\<exists>z. clift hp x = Some z)"
  apply (cases "clift hp x")
   apply simp
   apply (cases "clift (hrs_mem_update a hp) x")
   apply (auto)
  done


lemma simple_lift_data_eq:
   "\<lbrakk> h_val (hrs_mem h) p = h_val (hrs_mem h') p';
     root_ptr_valid (hrs_htd h) p = root_ptr_valid (hrs_htd h') p' \<rbrakk> \<Longrightarrow>
    simple_lift h p = simple_lift h' p'"
  apply (clarsimp simp: simple_lift_def)
  done

lemma h_val_heap_update_disjoint:
  "\<lbrakk> {ptr_val p ..+ size_of TYPE('a::c_type)}
        \<inter> {ptr_val q ..+ size_of TYPE('b::mem_type)} = {} \<rbrakk> \<Longrightarrow>
      h_val (heap_update (q :: 'b ptr) r h) (p :: 'a ptr) = h_val h p"
  apply (clarsimp simp: h_val_def)
  apply (clarsimp simp: heap_update_def)
  apply (subst heap_list_update_disjoint_same)
   apply clarsimp
   apply blast
   apply clarsimp
  done

lemma update_ti_t_valid_size:
  "size_of TYPE('b) = size_td t \<Longrightarrow>
   update_ti_t t (to_bytes_p (val::'b::mem_type)) obj = update_ti t (to_bytes_p val) obj"
  apply (clarsimp simp: update_ti_t_def to_bytes_p_def)
  done

lemma h_val_field_from_bytes':
  "\<lbrakk> field_ti TYPE('a::{mem_type}) f = Some t;
     export_uinfo t = export_uinfo (typ_info_t TYPE('b::{mem_type})) \<rbrakk> \<Longrightarrow>
    h_val h (Ptr &(pa\<rightarrow>f) :: 'b ptr) = from_bytes (access_ti\<^sub>0 t (h_val h pa))"
  apply (insert h_val_field_from_bytes[where f=f and pa=pa and t=t and h="(h,x)"
                                         and 'a='a and 'b='b for x])
  apply (clarsimp simp: hrs_mem_def)
  done


lemma h_val_field_from_root:
  fixes p::"'a:: mem_type ptr"
  assumes fl: 
    "field_lookup (typ_info_t TYPE('a::{mem_type})) f 0 = 
      Some (adjust_ti (typ_info_t TYPE('b::mem_type)) fld fld_update, n)"
  assumes fg_cons: "fg_cons fld (fld_update)"
  shows "h_val h (PTR('b) &(p\<rightarrow>f)) = fld (h_val h p)"
proof -
  from fl 
  have fl: "field_ti TYPE('a) f = Some (adjust_ti (typ_info_t TYPE('b::mem_type)) fld fld_update)"
    using field_lookup_field_ti by blast
  have exp: "export_uinfo (adjust_ti (typ_info_t TYPE('b)) fld fld_update) =
        export_uinfo (typ_info_t TYPE('b))"
    using fg_cons
    by simp
  from h_val_field_from_bytes' [OF fl exp]
  show ?thesis
    by simp
qed

lemma simple_lift_super_field_update_lookup:
  fixes dummy :: "'b :: mem_type"
  assumes "field_lookup (typ_info_t TYPE('b::mem_type)) f 0 = Some (s,n)"
    and "typ_uinfo_t TYPE('a) = export_uinfo s"
    and "simple_lift h p = Some v'"
  shows "(super_field_update_t (Ptr (&(p\<rightarrow>f))) (v::'a::mem_type) ((simple_lift h)::'b ptr \<Rightarrow> 'b option)) =
          ((simple_lift h)(p \<mapsto> field_update (field_desc s) (to_bytes_p v) v'))"
proof -
  from assms have [simp]: "unat (of_nat n :: addr) = n"
     apply (subst unat_of_nat)
     apply (subst mod_less)
      apply (drule td_set_field_lookupD)+
      apply (drule td_set_offset_size)+
      apply (subst len_of_addr_card)
      apply (subst (asm) size_of_def [symmetric, where t="TYPE('b)"])+
      apply (subgoal_tac "size_of TYPE('b) < addr_card")
       apply arith
      apply simp
     apply simp
     done
   from assms show ?thesis
    supply unsigned_of_nat [simp del]
    apply (clarsimp simp: super_field_update_t_def)
    apply (rule ext)
    apply (clarsimp simp: field_lvalue_def split: option.splits)
    apply (safe, simp_all)
       apply (frule_tac v=v and v'=v' in update_field_update)
       apply (clarsimp simp: field_of_t_def field_of_def typ_uinfo_t_def)
       apply (frule_tac m=0 in field_names_SomeD2)
        apply simp
       apply clarsimp
       apply (simp add: field_typ_def field_typ_untyped_def)
       apply (frule field_lookup_export_uinfo_Some)
       apply (frule_tac s=k in field_lookup_export_uinfo_Some)
       apply simp
       apply (drule (1) field_lookup_inject)
        apply (subst typ_uinfo_t_def [symmetric, where t="TYPE('b)"])
        apply simp
       apply simp
      apply (drule field_of_t_mem)+
      apply (cases h)
      apply (clarsimp simp: simple_lift_def split: if_split_asm)
      apply (drule (1) root_ptr_valid_neq_disjoint)
       apply simp
      apply fast
     apply (clarsimp simp: field_of_t_def field_of_def)
     apply (subst (asm) td_set_field_lookup)
      apply simp
     apply simp
     apply (frule field_lookup_export_uinfo_Some)
     apply (simp add: typ_uinfo_t_def)
    apply (clarsimp simp: field_of_t_def field_of_def)
    apply (subst (asm) td_set_field_lookup)
     apply simp
    apply simp
    apply (frule field_lookup_export_uinfo_Some)
    apply (simp add: typ_uinfo_t_def)
    done
qed

lemma field_offset_addr_card:
  "\<exists>x. field_lookup (typ_info_t TYPE('a::mem_type)) f 0 = Some x
    \<Longrightarrow> field_offset TYPE('a) f < addr_card"
  apply (clarsimp simp: field_offset_def field_offset_untyped_def typ_uinfo_t_def)
  apply (subst field_lookup_export_uinfo_Some)
   apply assumption
  apply (frule td_set_field_lookupD)
  apply (drule td_set_offset_size)
  apply (insert max_size [where ?'a="'a"])
  apply (clarsimp simp: size_of_def)
  done

lemma unat_of_nat_field_offset:
  "\<exists>x. field_lookup (typ_info_t TYPE('a::mem_type)) f 0 = Some x \<Longrightarrow>
      unat (of_nat (field_offset TYPE('a) f)  :: addr) = field_offset TYPE('a) f"
  apply (subst word_unat.Abs_inverse)
   apply (clarsimp simp: unats_def)
   apply (insert field_offset_addr_card [where f=f and ?'a="'a"])[1]
   apply (fastforce simp: addr_card)
  apply simp
  done

lemma field_of_t_field_lookup:
  assumes a: "field_lookup (typ_info_t TYPE('a::mem_type)) f 0 = Some (s, n)"
  assumes b: "export_uinfo s = typ_uinfo_t TYPE('b::mem_type)"
  assumes n: "n = field_offset TYPE('a) f"
  shows "field_of_t (Ptr &(ptr\<rightarrow>f) :: ('b ptr)) (ptr :: 'a ptr)"
  supply unsigned_of_nat [simp del]
  apply (clarsimp simp del: field_lookup_offset_eq
      simp: field_of_t_def field_of_def)
  apply (subst td_set_field_lookup)
   apply (rule wf_desc_typ_tag)
  apply (rule exI [where x=f])
  using a[simplified n] b
  apply (clarsimp simp: typ_uinfo_t_def)
  apply (subst field_lookup_export_uinfo_Some)
   apply assumption
  apply (clarsimp simp del: field_lookup_offset_eq
      simp: field_lvalue_def unat_of_nat_field_offset)
  done

lemma simple_lift_field_update':
  fixes val :: "'b :: mem_type" and ptr :: "'a :: mem_type ptr"
  assumes   fl: "field_lookup (typ_info_t TYPE('a)) f 0 =
                     Some (adjust_ti (typ_info_t TYPE('b)) xf xfu, n)"
  and   xf_xfu: "fg_cons xf xfu"
  and       cl: "simple_lift hp ptr = Some z"
  shows "(simple_lift (hrs_mem_update (heap_update (Ptr &(ptr\<rightarrow>f)) val) hp)) =
                (simple_lift hp)(ptr \<mapsto> xfu val z)"
    (is "?LHS = ?RHS")
proof (rule ext)
  fix p

  have eui: "typ_uinfo_t TYPE('b) =
       export_uinfo (adjust_ti (typ_info_t TYPE('b)) xf xfu)"
    using xf_xfu
    apply (subst export_tag_adjust_ti2 [OF _ wf_lf wf_desc])
    apply (simp add: fg_cons_def )
    apply (rule meta_eq_to_obj_eq [OF typ_uinfo_t_def])
    done

  have n_is_field_offset: "n = field_offset TYPE('a) f"
    apply (insert field_lookup_offset_eq [OF fl])
    apply (clarsimp)
    done

  have equal_case: "?LHS ptr = ?RHS ptr"
    supply unsigned_of_nat [simp del]
    apply (insert cl)
    apply (clarsimp simp: simple_lift_def split: if_split_asm)
    apply (clarsimp simp: hrs_mem_update)
    apply (subst h_val_super_update_bs)
     apply (rule field_of_t_field_lookup [OF fl])
      apply (clarsimp simp: eui)
     apply (clarsimp simp: n_is_field_offset)
    apply clarsimp
    apply (unfold from_bytes_def)
    apply (subst fi_fu_consistentD [where f=f and s="adjust_ti (typ_info_t TYPE('b)) xf xfu"])
        apply (clarsimp simp: fl)
        apply (clarsimp simp: n_is_field_offset field_lvalue_def)
        apply (metis unat_of_nat_field_offset fl)
       apply clarsimp
      apply (clarsimp simp: size_of_def)
     apply (clarsimp simp: size_of_def)
    apply clarsimp
    apply (subst update_ti_s_from_bytes)
     apply clarsimp
    apply (subst update_ti_t_adjust_ti)
     apply (rule xf_xfu)
    apply (subst update_ti_s_from_bytes)
     apply clarsimp
    apply clarsimp
    apply (clarsimp simp: h_val_def)
    done

  show "?LHS p = ?RHS p"
    apply (cases "p = ptr")
     apply (erule ssubst)
     apply (rule equal_case)
    apply (insert cl)
    apply (clarsimp simp: simple_lift_def hrs_mem_update split: if_split_asm)
    apply (rule h_val_heap_update_disjoint)
    apply (insert field_tag_sub [OF fl, where p=ptr])
    apply (clarsimp simp: size_of_def)
    apply (clarsimp simp: root_ptr_valid_legacy_def)
    apply (frule (1) valid_simple_footprint_neq_disjoint, fastforce)
    apply clarsimp
    apply blast
    done
qed

lemma simple_lift_field_update:
  fixes val :: "'b :: mem_type" and ptr :: "'a :: mem_type ptr"
  assumes   fl: "field_ti TYPE('a) f =
                     Some (adjust_ti (typ_info_t TYPE('b)) xf (xfu o (\<lambda>x _. x)))"
  and   xf_xfu: "fg_cons xf (xfu o (\<lambda>x _. x))"
  and       cl: "simple_lift hp ptr = Some z"
  shows "(simple_lift (hrs_mem_update (heap_update (Ptr &(ptr\<rightarrow>f)) val) hp)) =
                (simple_lift hp)(ptr \<mapsto> xfu (\<lambda>_. val) z)"
    (is "?LHS = ?RHS")
  apply (insert fl [unfolded field_ti_def])
  apply (clarsimp split: option.splits)
  apply (subst simple_lift_field_update' [where xf=xf and xfu="xfu o (\<lambda>x _. x)" and z=z])
     apply (clarsimp simp: o_def split: option.splits)
     apply (rule refl)
    apply (rule xf_xfu)
   apply (rule cl)
  apply clarsimp
  done

lemma simple_heap_diff_types_impl_diff_ptrs:
  "\<lbrakk> root_ptr_valid h (p::('a::c_type) ptr);
     root_ptr_valid h (q::('b::c_type) ptr);
     typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b) \<rbrakk> \<Longrightarrow>
   ptr_val p \<noteq> ptr_val q"
  apply (clarsimp simp: root_ptr_valid_legacy_def)
  apply (clarsimp simp: valid_simple_footprint_def)
  done

lemma h_val_update_regions_disjoint:
  "\<lbrakk> { ptr_val p ..+ size_of TYPE('a) } \<inter> { ptr_val x ..+ size_of TYPE('b)} = {} \<rbrakk> \<Longrightarrow>
        h_val (heap_update p (v::('a::mem_type)) h) x = h_val h (x::('b::c_type) ptr)"
  apply (clarsimp simp: heap_update_def)
  apply (clarsimp simp: h_val_def)
  apply (subst heap_list_update_disjoint_same)
   apply clarsimp
  apply clarsimp
  done

lemma h_val_heap_update_padding_disjoint:
  fixes p::"'a::mem_type ptr"
  fixes q::"'b::c_type ptr"
  shows "\<lbrakk> ptr_span p \<inter> ptr_span q = {}; length bs = size_of TYPE('a) \<rbrakk> \<Longrightarrow>
      h_val (heap_update_padding p  v bs h) q = h_val h q"
  apply (clarsimp simp: heap_update_padding_def)
  apply (clarsimp simp: h_val_def)
  apply (subst heap_list_update_disjoint_same)
   apply clarsimp
  apply clarsimp
  done


lemma simple_lift_field_update_t:
  fixes    val :: "'b :: mem_type" and ptr :: "'a :: mem_type ptr"
  assumes  fl: "field_ti TYPE('a) f = Some t"
  and      diff: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('c :: c_type)"
  and      eu: "export_uinfo t = export_uinfo (typ_info_t TYPE('b))"
  and      cl: "simple_lift hp ptr = Some z"
  shows "((simple_lift (hrs_mem_update (heap_update (Ptr &(ptr\<rightarrow>f)) val) hp)) :: 'c ptr \<Rightarrow> 'c option) =
             simple_lift hp"
  apply (rule ext)
  subgoal for x
    apply (cases "simple_lift hp x")
     apply clarsimp
    apply (cases "ptr_val x = ptr_val ptr")
     apply clarsimp
     apply (clarsimp simp: simple_lift_def hrs_mem_update split: if_split_asm)
     apply (cut_tac simple_lift_root_ptr_valid [OF cl])
     apply (drule (1) simple_heap_diff_types_impl_diff_ptrs [OF _ _ diff])
     apply simp
    apply (clarsimp simp: simple_lift_def hrs_mem_update split: if_split_asm)
    apply (rule field_ti_field_lookupE [OF fl])
    apply (frule_tac p=ptr in field_tag_sub)
    apply (clarsimp simp: h_val_def heap_update_def)
    apply (subst heap_list_update_disjoint_same)
     apply clarsimp
     apply (cut_tac simple_lift_root_ptr_valid [OF cl])
     apply (drule (2) root_ptr_valid_neq_disjoint)
     apply (clarsimp simp: export_size_of [unfolded typ_uinfo_t_def, OF eu])
     apply blast
    apply simp
    done
  done




lemma simple_lift_heap_update_other':
  "\<lbrakk> simple_lift h (p::'b::mem_type ptr) = Some v';
     typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b) \<rbrakk> \<Longrightarrow>
   simple_lift (hrs_mem_update (heap_update p v) h) = ((simple_lift h)::'a::c_type typ_heap)"
  apply (rule simple_lift_heap_update_other)
   apply (erule simple_lift_root_ptr_valid)
  apply simp
  done

(* If you update bytes inside an object of one type, it won't affect
 * heaps of other types. *)
lemma simple_lift_heap_update_bytes_in_other:
  "\<lbrakk> simple_lift h (p::'b::mem_type ptr) = Some v';
     typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE('c);
     { ptr_val q ..+ size_of TYPE('a)} \<subseteq> {ptr_val p  ..+ size_of TYPE('b) }  \<rbrakk> \<Longrightarrow>
   simple_lift (hrs_mem_update (heap_update (q::'a::mem_type ptr) v) h) = ((simple_lift h)::'c::mem_type typ_heap)"
  apply (rule ext)
  apply (clarsimp simp: simple_lift_def split: if_split_asm)
  apply (drule (1) root_ptr_valid_type_neq_disjoint, simp)
  apply (clarsimp simp: hrs_mem_update)
  apply (rule h_val_heap_update_disjoint)
  apply blast
  done



lemma typ_name_neq:
    "typ_name (export_uinfo (typ_info_t TYPE('a::c_type)))
        \<noteq> typ_name (export_uinfo (typ_info_t TYPE('b::c_type)))
    \<Longrightarrow> typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b)"
  apply (metis typ_uinfo_t_def)
  done

lemma of_nat_mod_div_decomp:
  "of_nat k
        = of_nat (k div size_of TYPE('b)) * of_nat (size_of TYPE('b::mem_type)) +
              of_nat (k mod size_of TYPE('b))"
  by (metis mod_div_decomp of_nat_add of_nat_mult)

lemma c_guard_array_c_guard:
  "\<lbrakk> \<And>x. x < CARD('a) \<Longrightarrow> c_guard (ptr_coerce p +\<^sub>p int x :: 'b ptr) \<rbrakk> \<Longrightarrow> c_guard ( p :: ('b :: mem_type, 'a :: finite) array ptr)"
  apply atomize
  apply (clarsimp simp: c_guard_def)
  apply (rule conjI)
   apply (drule_tac x=0 in spec)
   apply (clarsimp simp: ptr_aligned_def align_of_def align_td_array)
  apply (simp add: c_null_guard_def)
  apply (clarsimp simp: intvl_def)
  apply (drule_tac x="k div size_of TYPE('b)" in spec)
  apply (erule impE)
   apply (metis (full_types) less_nat_zero_code mult_is_0 neq0_conv td_gal_lt)
  apply clarsimp
  apply (drule_tac x="k mod size_of TYPE('b)" in spec)
  apply (clarsimp simp: CTypesDefs.ptr_add_def)
  apply (subst (asm) add.assoc)
  apply (subst (asm) of_nat_mod_div_decomp [symmetric])
  apply clarsimp
  done

lemma heap_list_update_list':
  "\<lbrakk> n + x \<le> length v; length v < addr_card; q = (p + of_nat x) \<rbrakk> \<Longrightarrow>
      heap_list (heap_update_list p v h) n q = take n (drop x v)"
  by (metis heap_list_update_list)

lemma outside_intvl_range:
    "p \<notin> {a ..+ b} \<Longrightarrow> p < a \<or> p \<ge> a + of_nat b"
  apply (clarsimp simp: intvl_def not_le not_less)
  apply (drule_tac x="unat (p-a)" in spec)
  apply clarsimp
  apply (metis add_diff_cancel2 le_less_linear le_unat_uoi
      mpl_lem not_add_less2 unat_mono word_less_minus_mono_left)
  done

lemma root_ptr_valid_intersect_array:
  "\<lbrakk> \<forall>j < n. root_ptr_valid htd (p +\<^sub>p int j);
        root_ptr_valid htd (q :: ('a :: c_type) ptr) \<rbrakk>
         \<Longrightarrow> (\<exists>m < n. q = (p +\<^sub>p int m))
    \<or> ({ptr_val p ..+ size_of TYPE ('a) * n} \<inter> {ptr_val q ..+ size_of TYPE ('a :: c_type)} = {})"
  apply (induct n)
   apply clarsimp
  subgoal for n
    apply atomize
    apply simp
    apply (cases "n = 0")
     apply clarsimp
     apply (metis root_ptr_valid_neq_disjoint ptr_val_inj)
    apply (erule disjE)
     apply (metis less_Suc_eq)
    apply (cases "q = p +\<^sub>p int n")
     apply force
    apply (frule_tac x=n in spec)
    apply (erule impE, simp)
    apply (drule (1) root_ptr_valid_neq_disjoint)
     apply simp
    apply (simp add: CTypesDefs.ptr_add_def)
    apply (rule disjI2)
    apply (cut_tac a=" of_nat n * of_nat (size_of TYPE('a))"
        and p="ptr_val p" and n="n * size_of TYPE('a) + size_of TYPE('a)" in intvl_split)
     apply clarsimp
    apply (clarsimp simp: field_simps Int_Un_distrib2)
    apply (metis IntI emptyE intvl_empty intvl_inter intvl_self neq0_conv)
    done
  done

(* Simplification rules for dealing with "lift_simple". *)

lemmas simple_lift_simps =
  typ_name_neq
  simple_lift_c_guard
  h_val_simple_lift
  simple_lift_heap_update
  simple_lift_heap_update_other
  c_guard_field
  h_val_field_simple_lift
  simple_lift_field_update
  simple_lift_field_update_t
  c_guard_array_field

(* Old name for the above simpset. *)
lemmas typ_simple_heap_simps = simple_lift_simps
 


lemma valid_footprint_overlap_cases:
  assumes valid_p: "valid_footprint d (ptr_val (p::'a::mem_type ptr)) (typ_uinfo_t TYPE('a))"
  assumes valid_q: "valid_footprint d (ptr_val (q::'b::mem_type ptr)) (typ_uinfo_t TYPE('b))"
  assumes overlap: "ptr_span p \<inter> ptr_span q \<noteq> {}" 
  shows "TYPE('a) \<le>\<^sub>\<tau> TYPE('b) \<or> TYPE('b) \<le>\<^sub>\<tau> TYPE('a)"
proof (cases "typ_uinfo_t (TYPE('a)) = typ_uinfo_t (TYPE('b))")
  case True
  thus ?thesis by (simp add: sub_typ_def)
next
  case False
  note not_eq = False
  show ?thesis
  proof (cases "TYPE('a) \<bottom>\<^sub>\<tau> TYPE('b)")
    case False
    thus ?thesis by (simp add: tag_disj_typ_def tag_disj_def sub_typ_def)
  next
    case True
    note disj_types = True

    with disj_types not_eq have ne_le_b_a: "\<not> typ_uinfo_t (TYPE('b)) < typ_uinfo_t (TYPE('a))"
      apply (simp add: tag_disj_typ_def tag_disj_def) 
      by (meson le_less)

    have not_field_of_p_q: "\<not> field_of (ptr_val p - ptr_val q) (typ_uinfo_t (TYPE('a))) (typ_uinfo_t (TYPE('b)))"
      apply (rule ccontr, simp)
      apply (drule field_of_sub)
      using disj_types 
      apply (simp add: tag_disj_typ_def tag_disj_def) 
      done
     
    from valid_footprint_neq_disjoint [OF valid_p valid_q ne_le_b_a not_field_of_p_q]
    have "ptr_span p \<inter> ptr_span q = {}"
      by (simp add: size_of_def)
    with overlap show ?thesis by auto
  qed
qed




lemma valid_root_footprint_valid_footprint_overlap_case:
  assumes valid_p: "valid_root_footprint d (ptr_val (p::'a:: mem_type ptr)) (typ_uinfo_t (TYPE('a)))"
  assumes valid_q: "valid_footprint d (ptr_val (q::'b::mem_type ptr)) (typ_uinfo_t (TYPE('b)))" 
  assumes overlap: "ptr_span p \<inter> ptr_span q \<noteq> {}" (* fixme: what is the canonical way size_td, vs. size_of / typ_info_t vs. typ_uinfo_t *)
  shows "TYPE('b) \<le>\<^sub>\<tau> TYPE('a)"
proof -
  from overlap [simplified size_of_def, folded typ_uinfo_t_def]
  have " {ptr_val p..+size_td (typ_uinfo_t TYPE('a))} \<inter> {ptr_val q..+size_td (typ_uinfo_t TYPE('b))} \<noteq> {}"
    by simp
  from valid_root_footprint_overlap_sub_typ [OF valid_p valid_q this]
  have "typ_uinfo_t TYPE('b) \<le> typ_uinfo_t TYPE('a)".
  thus ?thesis
    by (simp add: sub_typ_def)
qed

lemma valid_root_footprint_overlap_contained: 
  assumes valid_root_x: "valid_root_footprint d x t"
  assumes valid_y: "valid_footprint d y s" 
  assumes overlap: "{x ..+ size_td t} \<inter> {y ..+ size_td s} \<noteq> {}"
  shows "y \<in> {x ..+ size_td t}"
  using valid_root_x overlap valid_y 
  apply (clarsimp simp add: valid_root_footprint_def valid_footprint_def Let_def typ_tag_le_def)
  by (metis (no_types, opaque_lifting) intvl_inter intvl_inter_le le_less_trans less_irrefl overlap 
      valid_footprint_sub2 valid_root_footprint_overlap_sub_typ valid_root_footprint_valid_footprint valid_root_x valid_y zero_le)

lemma valid_footprint_field_of_contained:
  assumes valid_x: "valid_footprint d x t"
  assumes field: "field_of off s t"
  shows "{x + off ..+ size_td s} \<subseteq> {x ..+ size_td t}"
proof -
  from field have "(s, unat off) \<in> td_set t 0"
    by (simp add: field_of_def)
  from td_set_offset_size [OF this] have "size_td s + unat off \<le> size_td t".
  thus ?thesis
    by (simp add: intvl_sub_offset)
qed

lemma valid_root_footprint_overlap_field_of: 
  assumes valid_root_x: "valid_root_footprint d x t"
  assumes valid_y: "valid_footprint d y s"
  assumes y: "y \<in> {x ..+ size_td t}"
  shows "field_of (y - x) s t"
proof -
  from y have "{x ..+ size_td t} \<inter> {y ..+ size_td s} \<noteq> {}" 
    by (meson disjoint_iff intvl_self valid_footprint_def valid_y)
  from valid_root_footprint_overlap_sub_typ [OF valid_root_x valid_y this]
  have "s \<le> t" .
  with y show ?thesis
    by (meson le_less_trans less_irrefl valid_footprint_sub valid_root_footprint_valid_footprint valid_root_x valid_y)
qed

lemma valid_root_footprint_overlap_contained': 
  assumes valid_root_x: "valid_root_footprint d x t"
  assumes valid_y: "valid_footprint d y s" 
  assumes overlap: "{x ..+ size_td t} \<inter> {y ..+ size_td s} \<noteq> {}"
  shows "{y ..+ size_td s} \<subseteq> {x ..+ size_td t}"
proof -
  from valid_root_footprint_overlap_contained [OF valid_root_x valid_y overlap]
  have "y \<in> {x..+size_td t}" .
  from valid_root_footprint_overlap_field_of [OF valid_root_x valid_y this]
  have "field_of (y - x) s t" .
  from valid_footprint_field_of_contained [OF valid_root_footprint_valid_footprint [OF valid_root_x] this]
  have "{x + (y - x)..+size_td s} \<subseteq> {x..+size_td t}" .
  then show ?thesis
    by auto
qed

lemma valid_footprint_sub_cases:
  assumes valid_p: "valid_footprint d p s"
  assumes valid_q: "valid_footprint d q t"
  assumes sub: "\<not> t < s"
  shows "{p..+size_td s} \<inter> {q..+size_td t} = {} \<or> field_of (p - q) (s) (t)" 
  using valid_footprint_neq_disjoint valid_p valid_q sub by blast


lemma valid_root_footprint_dist_type_cases: 
  assumes valid_p: "valid_root_footprint d (ptr_val (p::'a:: mem_type ptr)) (typ_uinfo_t (TYPE('a)))"
  assumes valid_q:  "valid_footprint d (ptr_val (q::'b::mem_type ptr)) (typ_uinfo_t (TYPE('b)))" 
  assumes dist_type: "typ_uinfo_t (TYPE('a)) \<noteq> typ_uinfo_t (TYPE('b))"
  assumes nested_case: "\<And>f. f \<in> set (field_names_u (typ_uinfo_t (TYPE('a))) (typ_uinfo_t (TYPE('b))))  \<Longrightarrow> 
            field_lookup (typ_uinfo_t TYPE('a)) f 0 = Some (typ_uinfo_t TYPE('b), unat (ptr_val q - ptr_val p)) \<Longrightarrow>
            field_of_t (PTR('b) &(p\<rightarrow>f)) p \<Longrightarrow>
            ptr_val q = &(p\<rightarrow>f) \<Longrightarrow> 
            ptr_span q \<subseteq> ptr_span p \<Longrightarrow> P"
  assumes disj_case: "ptr_span p \<inter> ptr_span q = {} \<Longrightarrow> P"
  shows P
proof (cases "ptr_span p \<inter> ptr_span q = {}")
  case True thus ?thesis by (rule disj_case)
next
  case False
  from valid_root_footprint_valid_footprint_overlap_case [OF valid_p valid_q False]
  have le_b_a: "typ_uinfo_t TYPE('b) \<le> typ_uinfo_t TYPE('a)" by (simp add: sub_typ_def)
   
  from sub_typ_field_names_u_nonempty [OF this]
  obtain f where "f \<in> set (field_names_u (typ_uinfo_t (TYPE('a))) (typ_uinfo_t (TYPE('b))))"
    by fastforce

  from False have "{ptr_val p..+size_td (typ_uinfo_t TYPE('a))} \<inter> {ptr_val q..+size_td (typ_uinfo_t TYPE('b))} \<noteq> {}"
    by (simp add: size_of_def)
  from valid_root_footprint_overlap_contained' [OF valid_p valid_q this]
  have "{ptr_val q..+size_td (typ_uinfo_t TYPE('b))} \<subseteq> {ptr_val p..+size_td (typ_uinfo_t TYPE('a))}" .
  hence "ptr_val q \<in> {ptr_val p..+size_td (typ_uinfo_t TYPE('a))}" 
    by (simp add: size_of_tag subsetD)
  from valid_root_footprint_overlap_field_of [OF valid_p valid_q this]
  have "field_of (ptr_val q - ptr_val p) (typ_uinfo_t TYPE('b)) (typ_uinfo_t TYPE('a)) " .
  from field_of_lookup_info [OF this, of p]
  obtain f where
    "f \<in> set (field_names_u (typ_uinfo_t (TYPE('a))) (typ_uinfo_t (TYPE('b))))"
    "field_lookup (typ_uinfo_t TYPE('a)) f 0 =
       Some (typ_uinfo_t TYPE('b), unat (ptr_val q - ptr_val p))" 
    "field_of_t (PTR('b) &(p\<rightarrow>f)) p"
    "ptr_val q = &(p\<rightarrow>f)" 
    "ptr_span q \<subseteq> ptr_span p"
    by (auto simp add: size_of_def)
  from nested_case [OF this]
  show ?thesis .
qed


lemma cvalid_field_pres: 
  assumes lookup: "field_lookup (typ_uinfo_t TYPE('a::mem_type)) f 0 = Some (typ_uinfo_t TYPE('b::mem_type), n)"
  assumes valid: "d,c_guard \<Turnstile>\<^sub>t (p::'a:: mem_type ptr) "  
  shows "d, c_guard \<Turnstile>\<^sub>t PTR('b) &(p\<rightarrow>f)"
  using  field_lookup_export_uinfo_Some_rev [OF lookup [simplified typ_uinfo_t_def]]
  apply (clarsimp)
  apply (rule h_t_valid_mono [rule_format, OF _ _ c_guard_mono valid])
   apply (auto simp add: typ_uinfo_t_def)
  done

lemma cvalid_field_pres': 
  assumes ptr_val_eq: "ptr_val q = &(p\<rightarrow>f)"
  assumes lookup: "field_lookup (typ_uinfo_t TYPE('a::mem_type)) f 0 = Some (typ_uinfo_t TYPE('b::mem_type), n)"
  assumes valid: "d,c_guard \<Turnstile>\<^sub>t (p::'a:: mem_type ptr)"  
  shows "d, c_guard \<Turnstile>\<^sub>t (q::'b ptr)"
proof -
  from ptr_val_eq have "q = PTR('b) (&(p\<rightarrow>f))"
    by (cases q) (auto simp add: ptr_val_def)
  with cvalid_field_pres [OF lookup valid] 
  show ?thesis
    by simp
qed

lemma cvalid_field_pres'': 
  assumes ptr_val_eq: "ptr_val q = &(p\<rightarrow>f)"
  assumes lookup: "field_lookup (typ_info_t TYPE('a::mem_type)) f 0 = Some (s, n)"
  assumes match: "export_uinfo s = typ_uinfo_t TYPE('b::mem_type)"
  assumes valid: "d,c_guard \<Turnstile>\<^sub>t (p::'a:: mem_type ptr)"  
  shows "d, c_guard \<Turnstile>\<^sub>t (q::'b ptr)"
proof -
  from cvalid_field_pres' [OF ptr_val_eq _ valid] lookup match
  show ?thesis
    by (simp add: UMM.field_lookup_typ_uinfo_t_Some)
qed

lemma cvalid_field_pres''': 
  assumes lookup: "field_lookup (typ_info_t TYPE('a::mem_type)) f 0 = Some (t, n)"
  assumes match: "export_uinfo t = typ_uinfo_t TYPE('b::mem_type)"
  assumes valid: "d,c_guard \<Turnstile>\<^sub>t (p::'a:: mem_type ptr) "  
  shows "d, c_guard \<Turnstile>\<^sub>t PTR('b) &(p\<rightarrow>f)"
  using lookup match valid
  using c_guard_mono h_t_valid_mono by blast

lemma the_clift_eq_h_val_eq:
  assumes h_val_eq: "hrs_htd hp \<Turnstile>\<^sub>t p \<Longrightarrow> h_val (hrs_mem (hrs_mem_update a hp)) p = h_val (hrs_mem hp) p"
  shows "the (clift (hrs_mem_update a hp) p) = the (clift hp p)"
proof (cases "clift hp p")
  case None
  with clift_hrs_mem_update_None show ?thesis by metis
next
  case (Some v)
  with clift_hrs_mem_update_None obtain v' where "clift (hrs_mem_update a hp) p = Some v'"
    by (cases "clift (hrs_mem_update a hp) p") auto
  with Some h_val_clift' h_val_eq [OF h_t_valid_clift [OF Some]]
  show ?thesis by metis
qed

lemma field_lvalue_same_conv: "&(p::'a:: c_type ptr\<rightarrow>f) = &(q::'a:: c_type ptr\<rightarrow>f) \<Longrightarrow> p = q" 
  by (simp add: field_lvalue_def)

lemma ptr_val_field_convD: "ptr_val p = &(q\<rightarrow>f) \<Longrightarrow> p = Ptr &(q\<rightarrow>f)"
  by (cases p)  auto

lemma ptr_val_field_conv: "ptr_val p = &(q\<rightarrow>f) \<longleftrightarrow> p = Ptr &(q\<rightarrow>f)"
  by (cases p)  auto

lemma ptr_val_array_index_convD: 
  "ptr_val p = ptr_val (array_ptr_index q False j) \<Longrightarrow> p = array_ptr_index q False j"
  by (cases p)  auto

lemma ptr_val_conv': "ptr_coerce p = Ptr q \<longleftrightarrow> ptr_val p = q"
  by (cases p) simp

lemma ptr_val_conv: "p = q \<longleftrightarrow> ptr_val p = ptr_val q"
  by auto

lemma ptr_val_neq_conv: "p \<noteq> q \<longleftrightarrow> ptr_val p \<noteq> ptr_val q"
  by auto

lemma the_simple_lift_strong_eqI:
  fixes p::"'a::mem_type ptr"
  fixes q::"'b::mem_type ptr"

assumes eq: "\<And>x1 x2. root_ptr_valid  (hrs_htd s) q \<Longrightarrow> 
    simple_lift s q = Some x1 \<Longrightarrow> 
    (simple_lift (hrs_mem_update (heap_update p v) s) q) = Some x2 \<Longrightarrow> 
    x1 = x2" 
  shows "the (simple_lift
             (hrs_mem_update (heap_update p v) s) q) =
         the (simple_lift s q)"
proof (cases "root_ptr_valid  (hrs_htd s) q")
  case True
  with eq show ?thesis by (fastforce simp add: simple_lift_def)
next
  case False
  hence "simple_lift s q = None"
    by (simp add: simple_lift_def)
  with simple_lift_hrs_mem_update_None
  show ?thesis by metis
qed

lemma the_simple_lift_hval_eqI:
  fixes p::"'a::mem_type ptr"
  fixes q::"'b::mem_type ptr"

assumes eq: "root_ptr_valid  (hrs_htd s) q \<Longrightarrow> 
    (h_val ((heap_update p v) (hrs_mem s)) q) = h_val (hrs_mem s) q " 

  shows "the (simple_lift
             (hrs_mem_update (heap_update p v) s) q) =
         the (simple_lift s q)"
  apply (rule the_simple_lift_strong_eqI)
  apply (drule h_val_simple_lift)
  apply (drule h_val_simple_lift)
  apply (auto simp add: hrs_mem_update eq)
  done

lemma h_t_valid_hrs_mem_update_pres: "hrs_htd s,g \<Turnstile>\<^sub>t q \<Longrightarrow> 
  hrs_htd ((hrs_mem_update (heap_update p v) s)), g\<Turnstile>\<^sub>t q"
  by (cases s) (auto simp add: hrs_htd_def hrs_mem_update_def)

lemma field_the_clift_hval_eqI:
  fixes p::"'a::mem_type ptr"
  fixes q::"'b::mem_type ptr"
assumes eq: "hrs_htd s, c_guard \<Turnstile>\<^sub>t q \<Longrightarrow> 
    f (h_val ((heap_update p v) (hrs_mem s)) q) = f (h_val (hrs_mem s) q) " 
  shows "f (the (clift
             (hrs_mem_update (heap_update p v) s) q)) =
         f (the (clift s q))"
proof (cases "(clift s q)")
  case None
  then show ?thesis using clift_hrs_mem_update_None by metis
next
  case (Some x)
  from h_t_valid_clift [OF this] have valid: "hrs_htd s \<Turnstile>\<^sub>t q" .
  hence "hrs_htd ((hrs_mem_update (heap_update p v) s))\<Turnstile>\<^sub>t q"
    by (rule h_t_valid_hrs_mem_update_pres)
  with h_t_valid_clift_Some_iff
  obtain y where y: "clift (hrs_mem_update (heap_update p v) s) q = Some y"
    by blast
  from h_val_clift' [OF Some] h_val_clift' [OF this] eq [OF valid]
  show ?thesis by (auto simp add: Some y hrs_mem_update) 
qed

lemma the_clift_hval_eqI:
  fixes p::"'a::mem_type ptr"
  fixes q::"'b::mem_type ptr"
assumes eq: "hrs_htd s, c_guard \<Turnstile>\<^sub>t q \<Longrightarrow> 
    (h_val ((heap_update p v) (hrs_mem s)) q) = (h_val (hrs_mem s) q) " 
  shows "the (clift
             (hrs_mem_update (heap_update p v) s) q) =
         (the (clift s q))"
  apply (rule field_the_clift_hval_eqI)
  by (rule eq)

lemma valid_root_footprint_same_type_cases: 
  assumes valid_p: "valid_root_footprint d (ptr_val (p::'a:: mem_type ptr)) (typ_uinfo_t (TYPE('a)))"
  assumes valid_q:  "valid_footprint d (ptr_val (q::'a::mem_type ptr)) (typ_uinfo_t (TYPE('a)))" 

  assumes eq_case: "p = q \<Longrightarrow> P"
  assumes disj_case: "ptr_span p \<inter> ptr_span q = {} \<Longrightarrow> P"
  shows P
proof (cases "ptr_span p \<inter> ptr_span q = {}")
  case True
  then show ?thesis by (simp add: disj_case)
next
  case False
  from valid_root_footprint_overlap_contained [OF valid_p valid_q ] False
  have "ptr_val q \<in> ptr_span p"
    by (simp add: typ_uinfo_t_def size_of_def)
  hence "p = q"
    by (metis ptr_val_conv size_of_tag valid_footprint_neq_nmem valid_p valid_q valid_root_footprint_valid_footprint)
  thus ?thesis by (simp add: eq_case)
qed

lemma valid_footprint_overlap_contained: 
  assumes valid_root_x: "valid_footprint d x t"
  assumes valid_y: "valid_footprint d y s" 
  assumes overlap: "{x ..+ size_td t} \<inter> {y ..+ size_td s} \<noteq> {}"
  shows "y \<in> {x ..+ size_td t} \<or> x \<in> {y ..+ size_td s}"
  using valid_root_x overlap valid_y 
  apply (clarsimp simp add:  valid_footprint_def Let_def typ_tag_le_def)
  by (meson intvl_inter overlap)

lemma valid_footprint_same_type_cases: 
  assumes valid_p: "valid_footprint d (ptr_val (p::'a:: mem_type ptr)) (typ_uinfo_t (TYPE('a)))"
  assumes valid_q:  "valid_footprint d (ptr_val (q::'a::mem_type ptr)) (typ_uinfo_t (TYPE('a)))" 

  assumes eq_case: "p = q \<Longrightarrow> P"
  assumes disj_case: "ptr_span p \<inter> ptr_span q = {} \<Longrightarrow> P"
  shows P
proof (cases "ptr_span p \<inter> ptr_span q = {}")
  case True
  then show ?thesis by (simp add: disj_case)
next
  case False
  from valid_footprint_overlap_contained [OF valid_p valid_q ] False
  have "ptr_val q \<in> ptr_span p \<or> ptr_val p \<in> ptr_span q"
    by (simp add: typ_uinfo_t_def size_of_def)
  hence "p = q"
    by (metis ptr_val_conv size_of_tag valid_footprint_neq_nmem valid_p valid_q )
  thus ?thesis by (simp add: eq_case)
qed

theorem subfield_deref_append: 
  fixes "q"::"'a::mem_type ptr"
  fixes "p"::"'b::mem_type ptr"
  assumes base: "ptr_val p = &(q\<rightarrow>g)"
  assumes g: "g \<in> set (field_names_u (typ_uinfo_t (TYPE('a))) (typ_uinfo_t (TYPE('b))))"
  assumes f: "f \<in> set (all_field_names (typ_uinfo_t (TYPE('b))))" 
  shows "&(p\<rightarrow>f) = &(q\<rightarrow>(g@f))"
proof -
  have wf_a: "wf_desc (typ_info_t (TYPE('a)))" by simp
  have wf_b: "wf_desc (typ_info_t (TYPE('b)))" by simp
  from g have "g \<in> set (field_names (typ_info_t (TYPE('a))) (typ_uinfo_t (TYPE('b))))"
    by (simp add: typ_uinfo_t_def field_names_u_field_names_export_uinfo_conv(1))
  from field_names_Some2(1) [rule_format, OF wf_a this] obtain n s where
    fl_g: "field_lookup (typ_info_t TYPE('a)) g 0 = Some (s, n)" and
    s: "export_uinfo s = typ_uinfo_t TYPE('b)"
    by blast

  from fl_g have off_g: "field_offset TYPE('a) g = n"
    by (simp)

  from all_field_names_exists_field_names_u(1) [OF f] obtain t
    where "f \<in> set (field_names_u (typ_uinfo_t TYPE('b)) t)" by blast
  hence "f \<in> set (field_names (typ_info_t TYPE('b)) t)"
    by (simp add: field_names_u_field_names_export_uinfo_conv(1) typ_uinfo_t_def)
  from field_names_Some2(1) [rule_format, OF wf_b  this] obtain t' m where
    fl_f: "field_lookup (typ_info_t TYPE('b)) f 0 = Some (t', m)" and
    t': "export_uinfo t' = t"
    by blast

  from fl_f have off_f: "field_offset TYPE('b) f = m"
    by simp

  from field_lookup_prefix_Some''(1) [rule_format, OF fl_g wf_a, of f]
  have fl_g_f: "field_lookup (typ_info_t TYPE('a)) (g @ f) 0 = field_lookup s f n" .

  from field_lookup_export_uinfo_Some [OF fl_f] t'
  have "field_lookup (typ_uinfo_t TYPE('b)) f 0 = Some (t, m)"
    by (simp add: typ_uinfo_t_def)

  from field_lookup_offset_shift' [OF this, of n]
  have "field_lookup (typ_uinfo_t TYPE('b)) f n = Some (t, m + n)"
    by simp

  with s have "field_lookup (export_uinfo s) f n = Some (t, m + n)"
    by simp
  from field_lookup_export_uinfo_Some_rev [OF this] obtain t'' where
    fl_s_f: "field_lookup s f n = Some (t'', m + n)" and 
    t'': "t = export_uinfo t''"
    by blast
  from fl_g_f fl_s_f have off_g_f: "field_offset TYPE('a) (g@f) = m + n"
    by (simp)

  show ?thesis
    using base
    by (simp add: field_lvalue_def off_g off_f off_g_f)
qed


lemmas root_ptr_valid_same_type_cases = valid_root_footprint_same_type_cases [OF root_ptr_valid_valid_root_footprint h_t_valid_valid_footprint]
lemmas ptr_valid_same_type_cases = valid_footprint_same_type_cases [OF h_t_valid_valid_footprint h_t_valid_valid_footprint]



theorem root_ptr_valid_heap_update_other':
  assumes val_p: "root_ptr_valid d (p::'a::mem_type ptr)"
  assumes val_q: "d \<Turnstile>\<^sub>t (q::'b::mem_type ptr)"
  assumes not_subtype: "\<not> TYPE('b) \<le>\<^sub>\<tau> TYPE('a)"
  shows "h_val (heap_update p v h) q = h_val h q"
  apply (clarsimp simp: h_val_def heap_update_def)
  apply (subst heap_list_update_disjoint_same)
   apply simp
   apply (rule root_ptr_valid_not_subtype_disjoint [OF val_p val_q not_subtype])
  apply simp
  done

(* FIXME: make variant for array access *)
theorem root_ptr_valid_heap_update_field_other:
  assumes val_p: "root_ptr_valid d (p::'a::mem_type ptr)"
  assumes val_q: "d \<Turnstile>\<^sub>t (q::'b::mem_type ptr)"
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (t, n)"
  assumes match: "export_uinfo t = typ_uinfo_t TYPE('c::mem_type)"
  assumes not_subtype_b_c: "\<not> TYPE('b) \<le>\<^sub>\<tau> TYPE('c)"
  assumes not_subtype_c_b: "\<not> TYPE('c) \<le>\<^sub>\<tau> TYPE('b)"
  shows "h_val (heap_update (PTR('c) &(p\<rightarrow>f)) v h) q = h_val h q"
proof (cases "ptr_span (PTR('c) &(p\<rightarrow>f)) \<inter> ptr_span q = {}" )
  case True
  then show ?thesis by (simp add: h_val_update_regions_disjoint)
next
  case False
  from valid_footprint_overlap_cases [OF _ _ False] val_p val_q field_lookup_typ_uinfo_t_Some [OF fl] 
    not_subtype_b_c not_subtype_c_b match
  have False 
    by (smt (verit) cvalid_field_pres h_t_valid_valid_footprint root_ptr_valid_legacy_def) 
  thus ?thesis
    by simp
qed

(* FIXME: make variant for array access *)
theorem root_ptr_valid_heap_update_field_other':
  assumes val_p: "root_ptr_valid d (p::'a::mem_type ptr)"
  assumes val_q: "d \<Turnstile>\<^sub>t (q::'b::mem_type ptr)"
  assumes fl: "field_lookup (typ_info_t TYPE('b)) f 0 = Some (t, n)"
  assumes match: "export_uinfo t = typ_uinfo_t TYPE('c::mem_type)"
  assumes not_subtype_b_a: "\<not> TYPE('b) \<le>\<^sub>\<tau> TYPE('a)"
  shows "h_val (heap_update p v h) (PTR ('c) &(q\<rightarrow>f)) = h_val h (PTR ('c) &(q\<rightarrow>f))"
proof (cases "ptr_span p \<inter> ptr_span q = {}" )
  case True
  from fl val_q match have subset: "ptr_span (PTR('c) &(q\<rightarrow>f)) \<subseteq> ptr_span q"
    by (metis export_uinfo_size field_tag_sub ptr_val.ptr_val_def size_of_tag)
  show ?thesis 
    apply (rule  h_val_update_regions_disjoint)
    using True subset
    by auto
next
  case False
  from valid_root_footprint_valid_footprint_overlap_case [OF _ _ False] val_p val_q
  have "TYPE('b) \<le>\<^sub>\<tau> TYPE('a)"
    by (meson False cvalid_field_pres'' fl match ptr_val.ptr_val_def root_ptr_valid_not_subtype_disjoint)
  with not_subtype_b_a have False by simp
  thus ?thesis
    by simp
qed

  

lemmas root_ptr_valid_dist_type_cases = valid_root_footprint_dist_type_cases [OF root_ptr_valid_valid_root_footprint h_t_valid_valid_footprint,
    consumes 3, case_names Field Disjoint_Spans]

theorem ptr_valid_heap_update_field_disj:
  assumes val_p: "d \<Turnstile>\<^sub>t (p::'a::mem_type ptr)"
  assumes val_q: "d \<Turnstile>\<^sub>t (q::'b::mem_type ptr)"
  assumes subtype: "TYPE('b) \<le>\<^sub>\<tau> TYPE('a)"
  assumes disj [rule_format] (* presented as HOL-term to make simplifier solve it *): 
   "\<forall>f. f \<in> set (field_names_u (typ_uinfo_t (TYPE('a))) (typ_uinfo_t (TYPE('b)))) \<longrightarrow> q \<noteq> Ptr (&(p\<rightarrow>f))" 
 shows "h_val (heap_update p v h) q = h_val h q"
proof (cases "ptr_span p \<inter> ptr_span q = {}")
  case True
  then show ?thesis
    by (simp add: h_val_update_regions_disjoint)
next
  case False
  from subtype have "typ_uinfo_t TYPE('b) \<le> typ_uinfo_t TYPE('a)" by (simp add: sub_typ_def)

  from this False valid_footprint_sub_cases [OF h_t_valid_valid_footprint [OF val_q]  h_t_valid_valid_footprint [OF val_p]]
  have field_of: "field_of (ptr_val q - ptr_val p) (typ_uinfo_t TYPE('b)) (typ_uinfo_t TYPE('a))"
    apply (simp add: size_of_def)
    by (metis Int_commute le_less_trans less_irrefl)
  then obtain f where 
    fl: "field_lookup (typ_uinfo_t (TYPE('a))) f 0 = Some (typ_uinfo_t TYPE('b), unat (ptr_val q - ptr_val p))"
    using field_of_lookup_info by blast

  then obtain s where 
    fl': "field_lookup  (typ_info_t (TYPE('a))) f 0 = Some (s, unat (ptr_val q - ptr_val p))" and
    s: "export_uinfo s = typ_uinfo_t TYPE('b)"
    using field_lookup_uinfo_Some_rev by blast


  from fl have f: "f \<in> set (field_names_u (typ_uinfo_t TYPE('a)) (typ_uinfo_t TYPE('b)))" 
    by (metis field_names_Some3(1) field_names_u_field_names_export_uinfo_conv(1) fl' s typ_uinfo_t_def)

  from fl' 
  have ptr_val_q: "ptr_val q = &(p\<rightarrow>f)"
    by (simp add: field_lvalue_def)

  from disj [OF f] ptr_val_q
  show ?thesis
    by  (auto simp add: ptr_val_field_convD)
qed

lemma is_padding_tag_access_ti_eq: "is_padding_tag s \<Longrightarrow> access_ti s x bs =  access_ti s y bs"
  by (clarsimp simp add: is_padding_tag_def padding_tag_def from_bytes_def access_ti\<^sub>0_def padding_desc_def)

lemma is_padding_tag_access_ti\<^sub>0: "is_padding_tag s \<Longrightarrow> access_ti\<^sub>0 s x = replicate (size_td s) 0"
  by (clarsimp simp add: is_padding_tag_def padding_tag_def from_bytes_def access_ti\<^sub>0_def padding_desc_def)

lemma is_padding_tag_from_bytes_eq: "is_padding_tag s \<Longrightarrow> from_bytes (access_ti\<^sub>0 s x) = from_bytes (access_ti\<^sub>0 s y)"
  by (simp add: from_bytes_def  is_padding_tag_access_ti\<^sub>0)

theorem ptr_valid_heap_update_field_disj':
  assumes val_p: "d \<Turnstile>\<^sub>t (p::'a::xmem_type ptr)"
  assumes val_q: "d \<Turnstile>\<^sub>t (q::'b::xmem_type ptr)"
  assumes subtype: "TYPE('b) \<le>\<^sub>\<tau> TYPE('a)"
  assumes disj [rule_format] (* presented as HOL-term to make simplifier solve it *): 
   "\<forall>f. f \<in> set (field_names_no_padding (typ_info_t (TYPE('a))) (export_uinfo (typ_info_t (TYPE('b))))) \<longrightarrow> q \<noteq> Ptr (&(p\<rightarrow>f))" 
 shows "h_val (heap_update p v h) q = h_val h q"
proof (cases "ptr_span p \<inter> ptr_span q = {}")
  case True
  then show ?thesis
    by (simp add: h_val_update_regions_disjoint)
next
  case False
  from subtype have "typ_uinfo_t TYPE('b) \<le> typ_uinfo_t TYPE('a)" by (simp add: sub_typ_def)

  from this False valid_footprint_sub_cases [OF h_t_valid_valid_footprint [OF val_q]  h_t_valid_valid_footprint [OF val_p]]
  have field_of: "field_of (ptr_val q - ptr_val p) (typ_uinfo_t TYPE('b)) (typ_uinfo_t TYPE('a))"
    apply (simp add: size_of_def)
    by (metis Int_commute le_less_trans less_irrefl)
  then obtain f where 
    fl: "field_lookup (typ_uinfo_t (TYPE('a))) f 0 = Some (typ_uinfo_t TYPE('b), unat (ptr_val q - ptr_val p))"
    using field_of_lookup_info by blast

  then obtain s where 
    fl': "field_lookup  (typ_info_t (TYPE('a))) f 0 = Some (s, unat (ptr_val q - ptr_val p))" and
    s: "export_uinfo s = typ_uinfo_t TYPE('b)"
    using field_lookup_uinfo_Some_rev by blast


  from fl' have fl'': "field_ti (TYPE('a)) f = Some s"
    by (simp add: field_ti_def)

  from fl' have f: "f \<in> set (field_names (typ_info_t TYPE('a)) (typ_uinfo_t TYPE('b)))" 
    by (metis field_names_Some3(1) fl' s)

  from fl' 
  have ptr_val_q: "ptr_val q = &(p\<rightarrow>f)"
    by (simp add: field_lvalue_def)
  then have q: "q = PTR ('b) &(p\<rightarrow>f)"
    by (cases q) auto

  show ?thesis
  proof (cases "qualified_padding_field_name f")
    case True
    from field_lookup_qualified_padding_field_name(1) [OF fl' True] 
    have padding_tag_s: "is_padding_tag s"
      by (simp add: wf_padding)
    note h_val = h_val_field_from_bytes' [where pa=p,OF fl'' s [simplified typ_uinfo_t_def]]
    show ?thesis apply (simp add: q)
      apply (simp add: h_val)
      apply (simp add: is_padding_tag_from_bytes_eq [OF padding_tag_s])
      done
  next
    case False
    with f fl' s have "f \<in> set (field_names_no_padding (typ_info_t (TYPE('a))) (export_uinfo (typ_info_t (TYPE('b)))))"
      by (simp add: set_field_names_no_padding_all_field_names_no_padding_conv all_field_names_no_padding_def
          fold_typ_uinfo_t set_field_names_all_field_names_conv)
    with disj [OF this] ptr_val_q show ?thesis by  (auto simp add: ptr_val_field_convD)
  qed

qed

lemma is_padding_tag_update_ti_id: "is_padding_tag s \<Longrightarrow> update_ti s bs v = v"
  by (auto simp add: is_padding_tag_def padding_tag_def padding_desc_def)

theorem ptr_valid_heap_update_field_disj'':
  assumes val_p: "d \<Turnstile>\<^sub>t (p::'a::xmem_type ptr)"
  assumes val_q: "d \<Turnstile>\<^sub>t (q::'b::xmem_type ptr)"
  assumes subtype: "TYPE('b) \<le>\<^sub>\<tau> TYPE('a)"
  assumes fl_g: "field_lookup (typ_info_t TYPE('a)) g 0 = Some (t, n)"
  assumes match: "export_uinfo t = typ_uinfo_t TYPE('c::xmem_type)" 
  assumes disj [rule_format] (* presented as HOL-term to make simplifier solve it *): 
   "\<forall>f. f \<in> set (field_names_no_padding (typ_info_t (TYPE('a))) (export_uinfo (typ_info_t (TYPE('b))))) 
         \<longrightarrow> ptr_span (PTR('b) &(p\<rightarrow>f)) \<inter> ptr_span (PTR('c) &(p\<rightarrow>g)) = {}" 
 shows "h_val (heap_update q v h) (PTR('c) &(p\<rightarrow>g)) = h_val h (PTR('c) &(p\<rightarrow>g))"
proof (cases "ptr_span q \<inter> ptr_span (PTR('c) &(p\<rightarrow>g)) = {}")
  case True
  then show ?thesis by (simp add: h_val_update_regions_disjoint)
next
  case False
  from subtype have st: "typ_uinfo_t TYPE('b) \<le> typ_uinfo_t TYPE('a)" by (simp add: sub_typ_def)
  from fl_g match have "ptr_span (PTR('c) &(p\<rightarrow>g)) \<subseteq> ptr_span p"
    by (metis export_uinfo_size field_tag_sub ptr_val.ptr_val_def size_of_tag)
  with False have "ptr_span q \<inter> ptr_span p \<noteq> {}"
    by auto

  from this st valid_footprint_sub_cases [OF h_t_valid_valid_footprint [OF val_q]  h_t_valid_valid_footprint [OF val_p]]
  have field_of: "field_of (ptr_val q - ptr_val p) (typ_uinfo_t TYPE('b)) (typ_uinfo_t TYPE('a))"
    by (simp add: size_of_def)

  then obtain f where 
    fl: "field_lookup (typ_uinfo_t (TYPE('a))) f 0 = Some (typ_uinfo_t TYPE('b), unat (ptr_val q - ptr_val p))"
    using field_of_lookup_info by blast

  then obtain s where 
    fl': "field_lookup  (typ_info_t (TYPE('a))) f 0 = Some (s, unat (ptr_val q - ptr_val p))" and
    s: "export_uinfo s = typ_uinfo_t TYPE('b)"
    using field_lookup_uinfo_Some_rev by blast

  from fl' have fl'': "field_ti (TYPE('a)) f = Some s"
    by (simp add: field_ti_def)

  from fl' have f: "f \<in> set (field_names (typ_info_t TYPE('a)) (typ_uinfo_t TYPE('b)))" 
    by (metis field_names_Some3(1) fl' s)

  from val_p have cgrd_p: "c_guard p" 
    by (simp add: h_t_valid_c_guard)
  from fl' 
  have ptr_val_q: "ptr_val q = &(p\<rightarrow>f)"
    by (simp add: field_lvalue_def)
  then have q: "q = PTR ('b) &(p\<rightarrow>f)"
    by (cases q) auto

  show ?thesis 
  proof (cases "qualified_padding_field_name f")
    case True
    from field_lookup_qualified_padding_field_name(1) [OF fl' True] 
    have padding_tag_s: "is_padding_tag s"
      by (simp add: wf_padding)
    note h_upd = heap_update_field_root_conv''' [OF fl'' cgrd_p s]
   
    show ?thesis 
      apply (simp add: q)
      by (simp add: h_upd is_padding_tag_update_ti_id [OF padding_tag_s] xmem_type_class.heap_update_id)
  next
    case False
      with f fl' s have "f \<in> set (field_names_no_padding (typ_info_t (TYPE('a))) (export_uinfo (typ_info_t (TYPE('b)))))"
      by (simp add: set_field_names_no_padding_all_field_names_no_padding_conv all_field_names_no_padding_def
          fold_typ_uinfo_t set_field_names_all_field_names_conv)
    from disj [OF this] have "ptr_span (PTR('b) &(p\<rightarrow>f)) \<inter> ptr_span (PTR('c) &(p\<rightarrow>g)) = {}" .
    then show ?thesis
      by (simp add: q h_val_update_regions_disjoint)
  qed
qed

theorem ptr_valid_heap_update_field_access_ti_disj:
  assumes val_p: "d \<Turnstile>\<^sub>t (p::'a::xmem_type ptr)"
  assumes val_q: "d \<Turnstile>\<^sub>t (q::'b::xmem_type ptr)"
  assumes subtype: "TYPE('b) \<le>\<^sub>\<tau> TYPE('a)"
  assumes disj [rule_format] (* presented as HOL-term to make simplifier solve it *): 
   "\<forall>f. f \<in> set (field_names_u (typ_uinfo_t (TYPE('a))) (typ_uinfo_t (TYPE('b)))) \<longrightarrow>  
     (access_ti (fst (the (field_lookup (typ_info_t TYPE('a)) f 0))) 
        v 
        (heap_list h (size_of TYPE('b)) (ptr_val q))) = 
     (access_ti (fst (the (field_lookup (typ_info_t TYPE('a)) f 0))) 
       (h_val h p)
       (heap_list h (size_of TYPE('b)) (ptr_val q)))" 
 shows "h_val (heap_update p v h) q = h_val h q"
proof (cases "ptr_span p \<inter> ptr_span q = {}")
  case True
  then show ?thesis
    by (simp add: h_val_update_regions_disjoint)
next
  case False

  from subtype have "typ_uinfo_t TYPE('b) \<le> typ_uinfo_t TYPE('a)" by (simp add: sub_typ_def)

  from this False valid_footprint_sub_cases [OF h_t_valid_valid_footprint [OF val_q]  h_t_valid_valid_footprint [OF val_p]]
  have field_of: "field_of (ptr_val q - ptr_val p) (typ_uinfo_t TYPE('b)) (typ_uinfo_t TYPE('a))"
    apply (simp add: size_of_def)
    by (metis Int_commute le_less_trans less_irrefl)
  then obtain f where 
    fl: "field_lookup (typ_uinfo_t (TYPE('a))) f 0 = Some (typ_uinfo_t TYPE('b), unat (ptr_val q - ptr_val p))"
    using field_of_lookup_info by blast

  then obtain s where 
    fl': "field_lookup  (typ_info_t (TYPE('a))) f 0 = Some (s, unat (ptr_val q - ptr_val p))" and
    s: "export_uinfo s = typ_uinfo_t TYPE('b)"
    using field_lookup_uinfo_Some_rev by blast


  from fl have f: "f \<in> set (field_names_u (typ_uinfo_t TYPE('a)) (typ_uinfo_t TYPE('b)))" 
    by (metis field_names_Some3(1) field_names_u_field_names_export_uinfo_conv(1) fl' s typ_uinfo_t_def)

  from fl' 
  have ptr_val_q: "ptr_val q = &(p\<rightarrow>f)"
    by (simp add: field_lvalue_def)

  from field_of
  have contained: "ptr_span q \<subseteq> ptr_span p"
    by (metis (no_types, opaque_lifting) 
        add_diff_cancel_left' export_uinfo_size field_lvalue_def field_of_lookup_info ptr_val_q size_of_def typ_uinfo_t_def)


  from disj [OF f] fl' have from_bytes_eq: 
    "(access_ti s v (heap_list h (size_of TYPE('b)) (ptr_val q))) =
     (access_ti s (h_val h p) (heap_list h (size_of TYPE('b)) (ptr_val q)))" by simp

  from ptr_val_q have q: "ptr_val q = ptr_val p + word_of_nat (unat (ptr_val q - ptr_val p))" 
    by (simp add: field_lvalue_def field_offset_def field_offset_untyped_def fl)

  from fl' s
  have sz_bound:  "size_of TYPE('b) + unat (ptr_val q - ptr_val p)
        \<le> length (to_bytes v (heap_list h (size_of TYPE('a)) (ptr_val p)))"
    by (metis export_uinfo_size field_lookup_offset_size heap_list_length len size_of_def typ_uinfo_size)

  have lheap_list: "length (heap_list h (size_of TYPE('a)) (ptr_val p)) = size_of (TYPE('a))"
    by simp
  from s
  have sz_s: "size_td s = size_of TYPE('b)"
    by (simp add: export_size_of )

  from val_p
  have p_no_overflow: "unat (ptr_val p) + size_of TYPE('a) \<le> addr_card"
    by (meson c_guard_no_wrap' h_t_valid_def)

  from contained q 
  have q_bound: "unat (ptr_val q - ptr_val p) + size_of TYPE('b) \<le> size_of TYPE('a)"
    using sz_bound by auto

  from heap_list_take_drop' [OF p_no_overflow q_bound]
  have take_drop_eq: 
      "take (size_of TYPE('b))
        (drop (unat (ptr_val q - ptr_val p))
          (heap_list h (size_of TYPE('a)) (ptr_val p))) = 
       heap_list h (size_of TYPE('b)) (ptr_val q)"
    by (simp add: q [symmetric])

  note acc_eq =  mem_type_field_lookup_access_ti_take_drop [OF fl' lheap_list, simplified sz_s, of v, simplified take_drop_eq]

  note acc_eq' = mem_type_field_lookup_access_ti_take_drop [OF fl' lheap_list, simplified sz_s, of "h_val h p", simplified take_drop_eq]

  have acc_eq'':
    "(access_ti (typ_info_t TYPE('a)) (h_val h p)
           (heap_list h (size_of TYPE('a)) (ptr_val p))) = (heap_list h (size_of TYPE('a)) (ptr_val p))"
    apply (simp add: h_val_def)
    apply (simp add: to_bytes_def [symmetric])
    by (simp add: to_bytes_from_bytes_id)

  show ?thesis
    apply (simp add: heap_update_def h_val_def)
    apply (subst (1 2) q)
    apply (subst heap_list_update_list [OF sz_bound])
     apply simp
    apply (simp add: to_bytes_def)
    apply (subst acc_eq [symmetric])
    apply (subst from_bytes_eq)
    apply (subst acc_eq')
    apply (subst acc_eq'')
    apply (simp add: take_drop_eq)
    done
qed

lemma access_ti_field_names_no_padding_to_field_names_u:
  assumes val_p: "d \<Turnstile>\<^sub>t (p::'a::xmem_type ptr)"
  assumes val_q: "d \<Turnstile>\<^sub>t (q::'b::xmem_type ptr)"
  assumes subtype: "TYPE('b) \<le>\<^sub>\<tau> TYPE('a)"
  assumes disj [rule_format]:
   "\<forall>f. f \<in> set (field_names_no_padding (typ_info_t (TYPE('a))) (export_uinfo (typ_info_t (TYPE('b))))) \<longrightarrow>  
     (access_ti (fst (the (field_lookup (typ_info_t TYPE('a)) f 0))) 
        v 
        (heap_list h (size_of TYPE('b)) (ptr_val q))) = 
     (access_ti (fst (the (field_lookup (typ_info_t TYPE('a)) f 0))) 
       (h_val h p)
       (heap_list h (size_of TYPE('b)) (ptr_val q)))" 
 assumes f_in: "f \<in> set (field_names_u (typ_uinfo_t (TYPE('a))) (typ_uinfo_t (TYPE('b))))"
 shows "(access_ti (fst (the (field_lookup (typ_info_t TYPE('a)) f 0))) 
        v 
        (heap_list h (size_of TYPE('b)) (ptr_val q))) = 
     (access_ti (fst (the (field_lookup (typ_info_t TYPE('a)) f 0))) 
       (h_val h p)
       (heap_list h (size_of TYPE('b)) (ptr_val q)))"
proof -
  from f_in 
  obtain n s where 
    fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n)" and
    match: "export_uinfo s = export_uinfo (typ_info_t (TYPE('b)))"
    by (smt (verit) field_names_Some2(1) fold_typ_uinfo_t set_field_names_all_field_names_conv 
        set_field_names_u_all_field_names_conv wf_desc)

  show ?thesis
  proof (cases "qualified_padding_field_name f")
    case True
    from field_lookup_qualified_padding_field_name(1) [OF fl True] 
    have padding_tag_s: "is_padding_tag s"
      by (simp add: wf_padding) 
    show ?thesis by (simp add: fl is_padding_tag_access_ti_eq [OF padding_tag_s])
  next
    case False
    with fl match field_lookup_all_field_names(1) [OF fl]
    have "f \<in> set (field_names_no_padding (typ_info_t (TYPE('a))) (export_uinfo (typ_info_t (TYPE('b)))))"
      by (simp add: set_field_names_no_padding_all_field_names_no_padding_conv all_field_names_no_padding_def)

    from disj [rule_format, OF this]
    show ?thesis .
  qed
qed


theorem ptr_valid_heap_update_field_access_ti_disj':
  assumes val_p: "d \<Turnstile>\<^sub>t (p::'a::xmem_type ptr)"
  assumes val_q: "d \<Turnstile>\<^sub>t (q::'b::xmem_type ptr)"
  assumes subtype: "TYPE('b) \<le>\<^sub>\<tau> TYPE('a)"
  assumes disj (* presented as HOL-term to make simplifier solve it *): 
   "\<forall>f. f \<in> set (field_names_no_padding (typ_info_t (TYPE('a))) (export_uinfo (typ_info_t (TYPE('b))))) \<longrightarrow>  
     (access_ti (fst (the (field_lookup (typ_info_t TYPE('a)) f 0))) 
        v 
        (heap_list h (size_of TYPE('b)) (ptr_val q))) = 
     (access_ti (fst (the (field_lookup (typ_info_t TYPE('a)) f 0))) 
       (h_val h p)
       (heap_list h (size_of TYPE('b)) (ptr_val q)))" 
 shows "h_val (heap_update p v h) q = h_val h q"
  apply (rule ptr_valid_heap_update_field_access_ti_disj [OF val_p val_q subtype])
  apply clarify
  apply (rule access_ti_field_names_no_padding_to_field_names_u [OF val_p val_q subtype disj])
  apply assumption
  done


theorem ptr_valid_heap_update_subtype_field_access_ti_disj:
  assumes val_p: "d \<Turnstile>\<^sub>t (p::'a::xmem_type ptr)"
  assumes val_q: "d \<Turnstile>\<^sub>t (q::'b::xmem_type ptr)"
  assumes subtype_b_a: "TYPE('b) \<le>\<^sub>\<tau> TYPE('a)"
  assumes fl_g: "field_lookup (typ_uinfo_t TYPE('b)) g 0 = Some (typ_uinfo_t TYPE('c::xmem_type), n)"
  assumes disj [rule_format] (* presented as HOL-term to make simplifier solve it *): 
   "\<forall>f. f \<in> set (field_names_u (typ_uinfo_t (TYPE('a))) (typ_uinfo_t (TYPE('b)))) \<longrightarrow>  
     (access_ti (fst (the (field_lookup (typ_info_t TYPE('a)) f 0))) 
        v 
        (heap_list h (size_of TYPE('b)) (ptr_val q))) = 
     (access_ti (fst (the (field_lookup (typ_info_t TYPE('a)) f 0))) 
       (h_val h p)
       (heap_list h (size_of TYPE('b)) (ptr_val q)))" 
 shows "h_val (heap_update p v h) (PTR('c) (&(q\<rightarrow>g))) = h_val h (PTR('c) (&(q\<rightarrow>g)))"
proof (cases "ptr_span p \<inter> ptr_span q = {}")
  case True
  from fl_g have "ptr_span (PTR('c) (&(q\<rightarrow>g))) \<subseteq> ptr_span q"
    by (metis export_uinfo_size field_lookup_uinfo_Some_rev field_tag_sub ptr_val.ptr_val_def size_of_tag)
  with True have "ptr_span p \<inter> ptr_span (PTR('c) (&(q\<rightarrow>g))) = {}" by blast
  then show ?thesis
    by (simp add: h_val_update_regions_disjoint)
next
  case False
  from subtype_b_a have "typ_uinfo_t TYPE('b) \<le> typ_uinfo_t TYPE('a)" by (simp add: sub_typ_def)

  from this False valid_footprint_sub_cases [OF h_t_valid_valid_footprint [OF val_q]  h_t_valid_valid_footprint [OF val_p]]
  have field_of: "field_of (ptr_val q - ptr_val p) (typ_uinfo_t TYPE('b)) (typ_uinfo_t TYPE('a))"
    apply (simp add: size_of_def)
    by (metis Int_commute le_less_trans less_irrefl)
  then obtain f where 
    fl: "field_lookup (typ_uinfo_t (TYPE('a))) f 0 = Some (typ_uinfo_t TYPE('b), unat (ptr_val q - ptr_val p))"
    using field_of_lookup_info by blast

  then obtain s where 
    fl': "field_lookup  (typ_info_t (TYPE('a))) f 0 = Some (s, unat (ptr_val q - ptr_val p))" and
    s: "export_uinfo s = typ_uinfo_t TYPE('b)"
    using field_lookup_uinfo_Some_rev by blast

  from fl have f: "f \<in> set (field_names_u (typ_uinfo_t TYPE('a)) (typ_uinfo_t TYPE('b)))" 
    by (metis field_names_Some3(1) field_names_u_field_names_export_uinfo_conv(1) fl' s typ_uinfo_t_def)

  from fl' 
  have ptr_val_q: "ptr_val q = &(p\<rightarrow>f)"
    by (simp add: field_lvalue_def)

  from field_of
  have contained: "ptr_span q \<subseteq> ptr_span p"
    by (metis (no_types, opaque_lifting) 
        add_diff_cancel_left' export_uinfo_size field_lvalue_def field_of_lookup_info ptr_val_q size_of_def typ_uinfo_t_def)

 from fl_g have contained': "ptr_span (PTR('c) (&(q\<rightarrow>g))) \<subseteq> ptr_span q"
    by (metis export_uinfo_size field_lookup_uinfo_Some_rev field_tag_sub ptr_val.ptr_val_def size_of_tag)

 from disj [OF f] fl' have from_bytes_eq: 
    "(access_ti s v (heap_list h (size_of TYPE('b)) (ptr_val q))) =
     (access_ti s (h_val h p) (heap_list h (size_of TYPE('b)) (ptr_val q)))" by simp

  from ptr_val_q have q: "ptr_val q = ptr_val p + word_of_nat (unat (ptr_val q - ptr_val p))" 
    by (simp add: field_lvalue_def field_offset_def field_offset_untyped_def fl)

  from fl_g have q_g: "&(q\<rightarrow>g) = ptr_val q + word_of_nat n"
    by (simp add: field_lvalue_def field_offset_def field_offset_untyped_def)
  with q have q_g': "&(q\<rightarrow>g) = ptr_val p + word_of_nat (unat (ptr_val q - ptr_val p) + n)"
    by simp

  from fl' s
  have sz_bound:  "size_of TYPE('b) + unat (ptr_val q - ptr_val p)
        \<le> length (to_bytes v (heap_list h (size_of TYPE('a)) (ptr_val p)))"
    by (metis export_uinfo_size field_lookup_offset_size heap_list_length len size_of_def typ_uinfo_size)

  from fl_g have subtype_c_b: "TYPE('c::xmem_type) \<le>\<^sub>\<tau> TYPE('b)"
    by (meson sub_typ_def td_set_field_lookupD typ_tag_le_def)

  from contained' subtype_c_b fl_g 
  have sz_c_n: "size_of TYPE('c) + n \<le> size_of TYPE('b)"
    by (metis size_of_def td_set_field_lookupD td_set_offset_size typ_uinfo_size)

  from sz_c_n sz_bound
  have sz_bound': "size_of TYPE('c) + (unat (ptr_val q - ptr_val p) + n)
       \<le> length (to_bytes v (heap_list h (size_of TYPE('a)) (ptr_val p)))"
    by simp
  have lheap_list: "length (heap_list h (size_of TYPE('a)) (ptr_val p)) = size_of (TYPE('a))"
    by simp
  from s
  have sz_s: "size_td s = size_of TYPE('b)"
    by (simp add: export_size_of )

  from val_p
  have p_no_overflow: "unat (ptr_val p) + size_of TYPE('a) \<le> addr_card"
    by (meson c_guard_no_wrap' h_t_valid_def)

  from contained q 
  have q_bound: "unat (ptr_val q - ptr_val p) + size_of TYPE('b) \<le> size_of TYPE('a)"
    using sz_bound by auto

  from fl_g s obtain s' where 
    fl_s_g: "field_lookup s g 0 = Some (s', n)" and 
    s': "export_uinfo s' = typ_uinfo_t TYPE('c)"
    by (metis CTypes.field_lookup_export_uinfo_Some_rev)

  from s'
  have sz_s': "size_td s' = size_of TYPE('c)"
    by (simp add: export_size_of )

  from sz_c_n q_bound
  have q_bound': "unat (ptr_val q - ptr_val p) + n + size_of TYPE('c) \<le> size_of TYPE('a)"
    by simp
  have take_drop_eq: 
    "(take (size_of TYPE('c))
       (drop (unat (ptr_val q - ptr_val p) + n)
       (heap_list h (size_of TYPE('a)) (ptr_val p)))) = 
   heap_list h (size_of TYPE('c)) (&(q\<rightarrow>g))"
    apply (subst q_g')
    apply (rule  heap_list_take_drop' [OF p_no_overflow q_bound'])
    done

  from fl_s_g field_lookup_prefix_Some''(1) [rule_format, OF fl' wf_desc, where g=g ]
  have fl_f_g: "field_lookup (typ_info_t TYPE('a)) (f @ g) 0 = Some (s', unat (ptr_val q - ptr_val p) + n)"
    by (simp add: field_lookup_offset)


  note acc_eq =  mem_type_field_lookup_access_ti_take_drop [OF fl_f_g lheap_list, simplified sz_s', of v, simplified take_drop_eq]
  note acc_eq' = mem_type_field_lookup_access_ti_take_drop [OF fl_f_g lheap_list, simplified sz_s', of "h_val h p", simplified take_drop_eq]

  from s fl' have wf_fd_s: "wf_fd s" by (meson wf_fd wf_fd_field_lookupD)
  from s fl' have wf_desc_s: "wf_desc s" by (meson field_lookup_wf_desc_pres(1) wf_desc)
  from s fl' have wf_sz_s: "wf_size_desc s" by (meson field_lookup_wf_size_desc_pres(1) wf_size_desc)

  from s have lheap_list': "length (heap_list h (size_of TYPE('b)) (ptr_val q)) = size_td s"
    using sz_s by simp

  from from_bytes_eq  
    field_lookup_access_ti_take_drop [OF fl_s_g wf_fd_s wf_desc_s wf_sz_s lheap_list', of v]
    field_lookup_access_ti_take_drop [OF fl_s_g wf_fd_s wf_desc_s wf_sz_s lheap_list', of "h_val h p"]
  have from_bytes_eq': 
    "(access_ti s' v (heap_list h (size_of TYPE('c)) (&(q\<rightarrow>g)))) =
     (access_ti s' (h_val h p) (heap_list h (size_of TYPE('c)) (&(q\<rightarrow>g))))" 
   by (metis add_leD2 add_le_imp_le_diff drop_heap_list_le q_g sz_c_n sz_s' take_heap_list_le)

  have acc_eq'':
    "(access_ti (typ_info_t TYPE('a)) (h_val h p)
           (heap_list h (size_of TYPE('a)) (ptr_val p))) = (heap_list h (size_of TYPE('a)) (ptr_val p))"
    apply (simp add: h_val_def)
    apply (simp add: to_bytes_def [symmetric])
    by (simp add: to_bytes_from_bytes_id)

  show ?thesis
    apply (simp add: heap_update_def h_val_def)
    apply (subst (1 2) q_g')

    apply (subst heap_list_update_list [OF sz_bound'])
     apply simp
    apply (simp add: to_bytes_def)
    apply (subst acc_eq [symmetric])

    apply (subst from_bytes_eq')
    apply (subst acc_eq')
    apply (subst acc_eq'')
    apply (simp add: take_drop_eq q_g')
    done
qed


corollary ptr_valid_heap_update_subtype_field_access_ti_disj':
  assumes val_p: "d \<Turnstile>\<^sub>t (p::'a::xmem_type ptr)"
  assumes val_q: "d \<Turnstile>\<^sub>t (q::'b::xmem_type ptr)"
  assumes subtype_b_a: "TYPE('b) \<le>\<^sub>\<tau> TYPE('a)"
  assumes fl_g: "field_lookup (typ_info_t TYPE('b)) g 0 = Some (s, n)"
  assumes match: "export_uinfo s = typ_uinfo_t TYPE('c::xmem_type)"
  assumes disj (* presented as HOL-term to make simplifier solve it *): 
   "\<forall>f. f \<in> set (field_names_no_padding (typ_info_t (TYPE('a))) (export_uinfo (typ_info_t (TYPE('b))))) \<longrightarrow>
     (access_ti (fst (the (field_lookup (typ_info_t TYPE('a)) f 0))) 
        v 
        (heap_list h (size_of TYPE('b)) (ptr_val q))) = 
     (access_ti (fst (the (field_lookup (typ_info_t TYPE('a)) f 0))) 
       (h_val h p)
       (heap_list h (size_of TYPE('b)) (ptr_val q)))" 
 shows "h_val (heap_update p v h) (PTR('c) (&(q\<rightarrow>g))) = h_val h (PTR('c) (&(q\<rightarrow>g)))"
  apply (rule ptr_valid_heap_update_subtype_field_access_ti_disj [OF val_p val_q subtype_b_a])
   apply (simp add: match [symmetric] field_lookup_typ_uinfo_t_Some [OF fl_g])
  apply clarify
  apply (rule access_ti_field_names_no_padding_to_field_names_u [OF val_p val_q subtype_b_a disj])
  apply assumption
  done


lemma array_ptr_index_field_lvalue_conv:  
  fixes p:: "('a::c_type['b::finite]) ptr"
  assumes i_bound: "i < CARD('b)"
  shows "(array_ptr_index p False i) = (PTR('a) &(p\<rightarrow>[replicate i CHR ''1'']))"
proof -
  from field_lookup_array [OF i_bound, of 0, simplified]
  have "field_lookup (typ_info_t TYPE('a['b])) [replicate i CHR ''1''] 0 =
         Some (adjust_ti (typ_info_t TYPE('a)) (\<lambda>x. x.[i]) (\<lambda>x f. Arrays.update f i x),
               i * size_of TYPE('a))" .
  from field_lookup_offset_eq [OF this]
  have "field_offset TYPE('a['b]) [replicate i CHR ''1''] = i * size_of TYPE('a)" .
  then show ?thesis
    by (simp add: field_lvalue_def array_ptr_index_def ptr_add_def)
qed

lemma field_lvalue_array_index:
  fixes p:: "('a::c_type['b::finite]) ptr"
  shows "i < CARD('b) \<Longrightarrow> &(p\<rightarrow>[replicate i CHR ''1'']) =
    ptr_val (PTR_COERCE('a['b] \<rightarrow> 'a) p +\<^sub>p int i)"
  using array_ptr_index_field_lvalue_conv[where i=i and 'b='b and 'a='a and p=p]
  by (simp add: array_ptr_index_def)

lemma field_lvalue_array_index':
  fixes p:: "('a::c_type['b::finite]) ptr"
  shows "i < CARD('b) \<Longrightarrow> 
    PTR('a) &(p\<rightarrow>[replicate i CHR ''1'']) =
    (PTR_COERCE('a['b] \<rightarrow> 'a) p +\<^sub>p int i)"
  by (simp add: field_lvalue_array_index)

thm field_lvalue_append
corollary ptr_valid_heap_update_subtype_array_access_ti_disj:
  assumes val_p: "d \<Turnstile>\<^sub>t (p::'a::xmem_type ptr)"
  assumes val_q: "d \<Turnstile>\<^sub>t (q::('b::array_outer_max_size['c::array_max_count]) ptr)"
  assumes subtype_b_a: "TYPE('b['c]) \<le>\<^sub>\<tau> TYPE('a)"
  assumes i_bound: "i < CARD('c)"
  assumes disj (* presented as HOL-term to make simplifier solve it *): 
   "\<forall>f. f \<in> set (field_names_no_padding (typ_info_t (TYPE('a))) (export_uinfo (typ_info_t (TYPE('b['c]))))) \<longrightarrow>
     (access_ti (fst (the (field_lookup (typ_info_t TYPE('a)) f 0))) 
        v 
        (heap_list h (size_of TYPE('b['c])) (ptr_val q))) = 
     (access_ti (fst (the (field_lookup (typ_info_t TYPE('a)) f 0))) 
       (h_val h p)
       (heap_list h (size_of TYPE('b['c])) (ptr_val q)))" 
 shows "h_val (heap_update p v h) (array_ptr_index q False i) = h_val h (array_ptr_index q False i)"
proof -
  note fl = field_lookup_array [OF i_bound, of 0]

  have "export_uinfo
         (adjust_ti (typ_info_t TYPE('b)) (\<lambda>x. x.[i]) (\<lambda>x f. Arrays.update (f::'b['c]) i x)) = typ_uinfo_t TYPE('b)"
    using i_bound
    by (simp )
 
  from ptr_valid_heap_update_subtype_field_access_ti_disj' [OF val_p val_q subtype_b_a fl this disj]
  have "h_val (heap_update p v h) (PTR('b) &(q\<rightarrow>[replicate i CHR ''1''])) =
        h_val h (PTR('b) &(q\<rightarrow>[replicate i CHR ''1'']))".
  then show ?thesis 
    by (simp add: array_ptr_index_field_lvalue_conv i_bound)
qed

theorem ptr_valid_heap_update_subtype_field_access_ti_indep:
  assumes val_p: "d \<Turnstile>\<^sub>t (p::'a::xmem_type ptr)"
  assumes val_q: "d \<Turnstile>\<^sub>t (q::'a::xmem_type ptr)"
  assumes fl_f: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (t, n)"
  assumes match: "export_uinfo t = typ_uinfo_t (TYPE('b::xmem_type))"
  assumes disj:
   "(access_ti t v (heap_list h (size_of TYPE('b)) (ptr_val q))) = 
    (access_ti t (h_val h p) (heap_list h (size_of TYPE('b)) (ptr_val q)))" 
 shows "h_val (heap_update p v h) (PTR('b) (&(q\<rightarrow>f))) = h_val h (PTR('b) (&(q\<rightarrow>f)))"
proof (cases "ptr_span p \<inter> ptr_span q = {}")
  case True
  from fl_f have "ptr_span (PTR('b) (&(q\<rightarrow>f))) \<subseteq> ptr_span q"
    by (metis export_uinfo_size field_tag_sub match ptr_val.ptr_val_def size_of_def typ_uinfo_t_def)
  with True have "ptr_span p \<inter> ptr_span (PTR('b) (&(q\<rightarrow>f))) = {}" by blast
  then show ?thesis
    by (simp add: h_val_update_regions_disjoint)
next
  case False
  from val_p val_q False have pq: "p = q" 
    by (meson ptr_valid_same_type_cases)

  from fl_f have fl_f': "field_ti TYPE('a) f = Some t" 
    using field_lookup_field_ti by blast

  from h_val_field_from_bytes' [OF fl_f' match [simplified typ_uinfo_t_def], of h p ]
  have eq1: "h_val h (PTR('b) &(p\<rightarrow>f)) = from_bytes (access_ti\<^sub>0 t (h_val h p))" .

  from h_val_field_from_bytes' [OF fl_f' match [simplified typ_uinfo_t_def], of "heap_update p v h" p]
  have eq2: "h_val (heap_update p v h) (PTR('b) &(p\<rightarrow>f)) = from_bytes (access_ti\<^sub>0 t (h_val (heap_update p v h) p))".

  thm field_lookup_access_ti_to_bytes_field_conv [OF fl_f match ]

  have eq_upto1: "eq_upto_padding (export_uinfo t) 
     (access_ti t v (replicate (size_td t) 0)) 
     ((access_ti t v (replicate (size_td t) 0)))"
    by (metis access_ti\<^sub>0 eq_upto_padding_refl export_uinfo_size fd_cons fd_cons_length_p fd_consistentD fl_f)

  have eq_pad_zeros: "eq_padding (export_uinfo t) (replicate (size_td t) 0) (replicate (size_td t) 0)"
    by simp

  from field_lookup_access_ti_eq_upto_padding [OF fl_f match, of "(replicate (size_td t) 0)"]    
  have "eq_upto_padding (export_uinfo t) 
         (access_ti t v (replicate (size_td t) 0))
         (access_ti t v (heap_list h (size_of TYPE('b)) (ptr_val q)))" 
    by simp
 
  moreover

  have " length (heap_list h (size_of TYPE('b)) (ptr_val q)) = size_td t"
    by (simp add: export_size_of match)
  from field_lookup_access_ti_eq_upto_padding [OF fl_f match this]    
  have "eq_upto_padding (export_uinfo t) 
     (access_ti t (h_val h p) (heap_list h (size_of TYPE('b)) (ptr_val q)))
     (access_ti t (h_val h p) (replicate (size_td t) 0))"
    by simp

  ultimately
  have eq_upto: "eq_upto_padding (export_uinfo t) 
         (access_ti t v (replicate (size_td t) 0))
         (access_ti t (h_val h p) (replicate (size_td t) 0))"
    using disj
    by (simp add: eq_upto_padding_def)

  from field_lookup_access_ti_eq_padding_value[OF fl_f match, of "(replicate (size_td t) 0)"]
  have "eq_padding (export_uinfo t) 
         (access_ti t v (replicate (size_td t) 0))
         (access_ti t (h_val h p) (replicate (size_td t) 0))"
    by simp

  from this eq_upto
  have acc_eq: "access_ti t v (replicate (size_td t) 0) =
       access_ti t (h_val h p) (replicate (size_td t) 0)" 
    by (rule  eq_padding_eq_upto_padding_eq)

  show ?thesis
    apply (simp add: pq [symmetric] eq1 eq2)
    apply (simp add: access_ti\<^sub>0_def h_val_heap_update)

    apply (simp add: from_bytes_def)
    apply (simp add: acc_eq)
    done
qed


lemmas clift_field' = clift_field [simplified fold_typ_uinfo_t]

lemma field_lookup_cons_Some:
  fixes t::"('a, 'b) typ_desc"
  and st::"('a, 'b) typ_struct"
  and ts::"('a, 'b) typ_tuple list"
  and x::"('a, 'b) typ_tuple"
  shows
"wf_desc t \<Longrightarrow> field_lookup t (f#fs) n = Some (s, m) \<Longrightarrow> 
       \<exists>w k. field_lookup t [f] n = Some (w, k) \<and> field_lookup w fs k = Some (s, m)" 
"wf_desc_struct st \<Longrightarrow> field_lookup_struct st (f # fs) n = Some (s, m) \<Longrightarrow> 
        \<exists>w k. field_lookup_struct st [f] n = Some (w, k) \<and> field_lookup w fs k = Some (s, m)"
"wf_desc_list ts \<Longrightarrow> field_lookup_list ts (f#fs) n = Some (s, m) \<Longrightarrow>  
       \<exists>w k. field_lookup_list ts [f] n = Some (w, k) \<and> field_lookup w fs k = Some (s, m)" 
"wf_desc_tuple x \<Longrightarrow> field_lookup_tuple x (f # fs) n = Some (s, m) \<Longrightarrow> 
         f = dt_snd x \<and>  
         field_lookup (dt_fst x) fs n = Some (s, m)"
proof (induct t and st and ts and x arbitrary: n s m f fs and n s m f fs and n s m f fs and n s m f fs) 
  case (TypDesc nat typ_struct list)
  then show ?case by auto
next
  case (TypScalar nat1 nat2 a)
  then show ?case by auto
next
  case (TypAggregate list)
  then show ?case by auto
   
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc t ts)
  thus ?case apply clarsimp
    by (metis Cons_typ_desc.prems(1) append_Cons append_Nil field_lookup_list_None field_lookup_list_Some 
        field_lookup_prefix_Some''(3) fl4 not_Some_eq_tuple)

next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case by (auto split: if_split_asm)
qed

lemma field_offset_append: 
  assumes f: "field_lookup (typ_uinfo_t TYPE('a)) f 0 = Some (typ_uinfo_t TYPE('b), n)"
  assumes g: "field_lookup (typ_uinfo_t TYPE('b)) g 0 = Some x"
  shows "field_offset TYPE('a::mem_type) (f @ g) = 
       field_offset (TYPE('a::mem_type)) f + field_offset (TYPE('b::mem_type)) g"
proof -
  from field_lookup_prefix_Some''(1) [rule_format , OF f] 
  have "field_lookup (typ_uinfo_t TYPE('a)) (f @ g) 0 = field_lookup (typ_uinfo_t TYPE('b)) g n"
    by simp
  with f g field_lookup_offset_non_zero show ?thesis
    apply (simp add: field_offset_def field_offset_untyped_def)
    by (smt (verit, ccfv_threshold) eq_snd_iff field_lookup_offset option.sel)
qed


lemma field_lookup_struct_offset_shift: 
  "field_lookup_struct st f m = Some (s, k) \<Longrightarrow> field_lookup_struct st f n = Some (s, k + n - m)"
  by (metis (no_types, lifting) add.commute field_lookup_offset'(2) field_lookup_offset_le(2) 
    le_add_diff_inverse ordered_cancel_comm_monoid_diff_class.diff_add_assoc2)

lemma field_lookup_list_offset_shift: 
  "field_lookup_list ts f m = Some (s, k) \<Longrightarrow> field_lookup_list ts f n = Some (s, k + n - m)"
  by (metis Nat.add_diff_assoc2 add.commute field_lookup_list_offset field_lookup_list_offset2 field_lookup_offset_le(3))

lemma field_lookup_tuple_offset_shift: 
  "field_lookup_tuple x f m = Some (s, k) \<Longrightarrow> field_lookup_tuple x f n = Some (s, k + n - m)"
  by (metis (no_types, lifting) add.commute field_lookup_offset'(4) field_lookup_offset_le(4) ordered_cancel_comm_monoid_diff_class.add_diff_assoc2 
  ordered_cancel_comm_monoid_diff_class.add_diff_inverse)

lemma h_val_field_update:
  fixes p::"'a::mem_type ptr"
  and q::"'a::mem_type ptr"
  and v:: "'b::mem_type"
  assumes fl: "field_ti TYPE('a) f = Some t"
  assumes match: "export_uinfo t = typ_uinfo_t TYPE('b)"
  and valid_p: "hrs_htd h \<Turnstile>\<^sub>t p"
  and valid_q: "hrs_htd h \<Turnstile>\<^sub>t q"
shows "(h_val (heap_update (Ptr &(p\<rightarrow>f)) v (hrs_mem h)) q) = 
  (if p = q then field_update (field_desc t) (to_bytes_p v) (h_val (hrs_mem h) p) else (h_val (hrs_mem h) q))" 
proof -
  from clift_Some_eq_valid valid_p obtain z where z: "clift h p = Some z" by metis

  from clift_field_update [OF fl match [simplified typ_uinfo_t_def ] this]
  show ?thesis
    apply simp
    by (smt (verit) fun_upd_apply h_val_clift' hrs_htd_def hrs_mem_update lift_t_if prod.collapse valid_q z)
qed

theorem root_ptr_valid_field_disj_type_h_val_heap_update:
  assumes valid_p: "root_ptr_valid (hrs_htd h) (p::'b::mem_type ptr)"
  assumes valid_q: "root_ptr_valid (hrs_htd h) (q::'a::mem_type ptr)"
  assumes neq: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b)"
  assumes f: "field_lookup (typ_info_t (TYPE('a))) f 0 = Some (s, n)"
  assumes match: "export_uinfo s = typ_uinfo_t (TYPE('c))"
  shows "h_val (heap_update (PTR('c::mem_type) &(q\<rightarrow>f)) v (hrs_mem h)) p =
         h_val (hrs_mem h) p"
proof -
  from root_ptr_valid_type_neq_disjoint [OF valid_q valid_p neq]
  have disj: "ptr_span q \<inter> ptr_span p = {}" .

  from export_uinfo_size [of s] have "size_td s = size_td (typ_uinfo_t TYPE('c))" by (simp add: match)
  moreover have "size_td (typ_info_t TYPE('c)) = size_td (typ_uinfo_t (TYPE('c)))"
    by (simp add: typ_uinfo_t_def)
  ultimately have sz: "size_td s = size_of (TYPE('c))"
    unfolding size_of_def
    by metis


  from field_tag_sub [OF f] have "{&(q\<rightarrow>f)..+size_td s} \<subseteq> ptr_span q" .

  with disj sz
  have "ptr_span (PTR('c::mem_type) &(q\<rightarrow>f)) \<inter> ptr_span p = {}"
    apply (simp )
    by blast
  from h_val_update_regions_disjoint [OF this]
  show ?thesis .
qed


lemma ptr_empty_qualified_field_name_conv: 
  fixes p::"'a::c_type ptr"
  shows "p = PTR ('a) &(p\<rightarrow>[])"
  by (simp add: field_lvalue_def)



theorem root_ptr_valid_field_disj_h_val_heap_update_eq:
  assumes valid_p: "root_ptr_valid d (p::'a::mem_type ptr)"
  assumes valid_q: "root_ptr_valid d (q::'b::mem_type ptr)"
  assumes f: "field_lookup (typ_info_t (TYPE('a))) f 0 = Some (t, n)"
  assumes g: "field_lookup (typ_info_t (TYPE('b))) g 0 = Some (s, m)"
  assumes match_t: "export_uinfo t = typ_uinfo_t (TYPE('c))"
  assumes match_s: "export_uinfo s = typ_uinfo_t (TYPE('d))"
  assumes disj: "typ_uinfo_t (TYPE('a)) = (typ_uinfo_t (TYPE('b))) \<Longrightarrow>
                 ptr_val p = ptr_val q \<Longrightarrow> 
                 ptr_span (PTR('c::mem_type) &(p\<rightarrow>f)) \<inter> ptr_span (PTR('d::mem_type) &(q\<rightarrow>g)) = {}"
  shows "h_val (heap_update (PTR('c::mem_type) &(p\<rightarrow>f)) v h) (PTR('d::mem_type) &(q\<rightarrow>g)) =
         h_val h (PTR('d::mem_type) &(q\<rightarrow>g))"
proof -
  from f match_t 
  have sub_f_p: "ptr_span (PTR('c::mem_type) &(p\<rightarrow>f)) \<subseteq> ptr_span p"
    using export_size_of field_tag_sub by fastforce
  from g match_s 
  have sub_g_q: "ptr_span (PTR('d::mem_type) &(q\<rightarrow>g)) \<subseteq> ptr_span q"
    using export_size_of field_tag_sub by fastforce
  show ?thesis
  proof (cases "typ_uinfo_t (TYPE('a)) = typ_uinfo_t (TYPE('b))")
    case True
    note typ_eq = this
    show ?thesis 
    proof (cases "ptr_val p = ptr_val q")
      case True
      from disj [OF typ_eq True]
      have "ptr_span (PTR('c::mem_type) &(p\<rightarrow>f)) \<inter> ptr_span (PTR('d::mem_type) &(q\<rightarrow>g)) = {}" by blast
      then show ?thesis 
        by (simp add: h_val_update_regions_disjoint)
    next
      case False
      from root_ptr_valid_neq_disjoint [OF valid_p valid_q False]
      have "ptr_span p \<inter> ptr_span q = {}".
      with sub_f_p sub_g_q
      have "ptr_span (PTR('c::mem_type) &(p\<rightarrow>f)) \<inter> ptr_span (PTR('d::mem_type) &(q\<rightarrow>g)) = {}" by blast
      then show ?thesis 
        by (simp add: h_val_update_regions_disjoint)
    qed
  next
    case False
    from root_ptr_valid_type_neq_disjoint [OF valid_p valid_q False]
    have "ptr_span p \<inter> ptr_span q = {}".
    with sub_f_p sub_g_q
    have "ptr_span (PTR('c::mem_type) &(p\<rightarrow>f)) \<inter> ptr_span (PTR('d::mem_type) &(q\<rightarrow>g)) = {}" by blast
    then show ?thesis 
     by (simp add: h_val_update_regions_disjoint)
 qed
qed

definition "PTR_MATCH p q = (p = q)"

lemma PTR_MATCH_field:
"PTR_MATCH (PTR('a::c_type) &(p\<rightarrow>f)) (PTR('a) &(p\<rightarrow>f))"
  by (simp add: PTR_MATCH_def)

lemma PTR_MATCH_dummy:
"PTR_MATCH (p::'a::c_type ptr) (PTR('a) &(p\<rightarrow>[]))"
  by (simp add: PTR_MATCH_def)



theorem root_ptr_valid_field_disj_h_val_heap_update_eq':
  assumes p': "PTR_MATCH p' (PTR('c) &(p\<rightarrow>f))"
  assumes q': "PTR_MATCH q' (PTR('d) &(q\<rightarrow>g))"
  assumes valid_p: "root_ptr_valid d (p::'a::mem_type ptr)"
  assumes valid_q: "root_ptr_valid d (q::'b::mem_type ptr)"
  assumes disj: "typ_uinfo_t (TYPE('a)) = (typ_uinfo_t (TYPE('b))) \<Longrightarrow>
                 ptr_val p = ptr_val q \<Longrightarrow> 
                 ptr_span (PTR('c) &(p\<rightarrow>f)) \<inter> ptr_span (PTR('d) &(q\<rightarrow>g)) = {}"
  assumes match_s: "export_uinfo s = typ_uinfo_t (TYPE('d::mem_type))"
  assumes match_t: "export_uinfo t = typ_uinfo_t (TYPE('c::mem_type))"
  assumes g: "field_lookup (typ_info_t (TYPE('b))) g 0 = Some (s, n)"
  assumes f: "field_lookup (typ_info_t (TYPE('a))) f 0 = Some (t, m)"
  shows "h_val (heap_update p' v h) q' = h_val h q'"
  using root_ptr_valid_field_disj_h_val_heap_update_eq [OF valid_p valid_q f g match_t match_s disj] p' q'
  by (simp add: PTR_MATCH_def)



lemma field_lookup_single_field_disj':
  fixes t::"('a, 'b) typ_desc"
  and st::"('a, 'b) typ_struct"
  and ts::"('a, 'b) typ_tuple list"
  and x::"('a, 'b) typ_tuple"
shows
"field_lookup t [f] n = Some (s, n + m) \<Longrightarrow> 
  field_lookup t [g] n = Some (s', n + k) \<Longrightarrow> f \<noteq> g \<Longrightarrow>
  {m ..< m + size_td s} \<inter> {k ..<k + size_td s'} = {}"
"field_lookup_struct st [f] n = Some (s, n + m) \<Longrightarrow> 
  field_lookup_struct st [g] n = Some (s', n + k) \<Longrightarrow> f \<noteq> g \<Longrightarrow>
  {m ..< m + size_td s} \<inter> {k ..< k + size_td s'} = {}"
"field_lookup_list ts [f] n = Some (s, n + m) \<Longrightarrow> 
  field_lookup_list ts [g] n = Some (s', n + k) \<Longrightarrow> f \<noteq> g \<Longrightarrow>
  {m ..< m + size_td s} \<inter> {k ..< k + size_td s'} = {}"
"field_lookup_tuple x [f] n = Some (s, n + m) \<Longrightarrow> 
  field_lookup_tuple x [g] n = Some (s', n + k) \<Longrightarrow> f \<noteq> g \<Longrightarrow>
  {m ..< m + size_td s} \<inter> {k ..< k + size_td s'} = {}"
proof (induct t and st and ts and x arbitrary: n s s' m f g k and n s s' m f g k and n s s' m f g k and n s s' m f g k)
  case (TypDesc nat typ_struct list)
then show ?case by auto
next
  case (TypScalar nat1 nat2 a)
  then show ?case by auto
next
  case (TypAggregate list)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc x fs)
  obtain d nm y where x: "x = DTuple d nm y" by (cases x) auto
  show ?case
  proof (cases "nm=f")
    case True
    from True Cons_typ_desc.prems  obtain
      fl_g: "field_lookup_list fs [g] (n + size_td s) = Some (s', n + k)" and
      neq: "f \<noteq> g" and
      d_s: "d = s" and m: "m = 0" 
      by (auto simp add: x split: if_split_asm)
    from field_lookup_offset_le(3) [OF fl_g] have "n + size_td s \<le> n + k" .
    hence "size_td s \<le> k" by simp
    then show ?thesis by (simp add: m)
  next
    case False
    note not_nm_f = this
    show ?thesis
    proof (cases "nm = g")
      case True
      from True Cons_typ_desc.prems  obtain 
        fl_f: "field_lookup_list fs [f] (n + size_td s') = Some (s, n + m)" and
        neq: "f \<noteq> g"
        "d = s'" and 
        k: "k = 0"  
        by  (auto simp add: x split: if_split_asm)
      from field_lookup_offset_le(3) [OF fl_f] have "n + size_td s' \<le> n + m" .
      hence "size_td s' \<le> m" by simp
      then show ?thesis by (simp add: k)

    next
      case False
        from False not_nm_f Cons_typ_desc.prems obtain 
          fl_f: "field_lookup_list fs [f] (n + size_td d) = Some (s, n + m)" and
          fl_g: "field_lookup_list fs [g] (n + size_td d) = Some (s', n + k)" and
          neq: "f \<noteq> g"  
          by  (auto simp add: x split: if_split_asm)
        from field_lookup_list_offset_shift [OF fl_f, of n, simplified]
        have fl_f': "field_lookup_list fs [f] n = Some (s, m + n - size_td d)" .
        from field_lookup_offset_le(3)[OF fl_f] 
        have bounds1: "n + size_td d \<le> n + m".
        then have eq1: "m + n - size_td d = n + (m - size_td d)"
          by simp

        from field_lookup_list_offset_shift [OF fl_g, of n, simplified]
        have fl_g': "field_lookup_list fs [g] n = Some (s', k + n - size_td d)" .
        from field_lookup_offset_le(3)[OF fl_g] 
        have bounds2: "n + size_td d \<le> n + k".
        then have eq2: "k + n - size_td d = n + (k - size_td d)"
          by simp
        from Cons_typ_desc.hyps(2) [OF fl_f' [simplified eq1] fl_g' [simplified eq2] neq ]
        have "{m - size_td d..<m - size_td d + size_td s} \<inter>
              {k - size_td d..<k - size_td d + size_td s'} = {}" .
        then show ?thesis using bounds1 bounds2 by auto
      qed
    qed
 
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case by (auto split: option.splits if_split_asm)
qed

lemma field_lookup_single_field_disj:
  assumes fl_f: "field_lookup t [f] 0 = Some (s, m)"
  assumes fl_g: "field_lookup t [g] 0 = Some (s', k)"
  assumes neq: "f \<noteq> g"
  shows "{m ..<m + size_td s} \<inter> {k ..<k + size_td s'} = {}"
  using field_lookup_single_field_disj'(1) [where n=0, simplified, OF fl_f fl_g neq ]
  by simp



lemma field_lookup_non_prefix_disj:
  assumes wf: "wf_desc t"
  assumes f: "field_lookup t f 0 = Some (tf, n)" 
  assumes g: "field_lookup t g 0 = Some (tg, m)"
  assumes g_f:"\<not> prefix g f" 
  assumes f_g: "\<not> prefix f g "
  shows "{n ..<n + size_td tf} \<inter> {m ..<m + size_td tg} = {}"
  using wf f g g_f f_g
  proof (induct f arbitrary: t tf n g tg m  )
    case Nil
    then show ?case by simp
  next
    case (Cons f1 fs)
    from Cons.prems obtain
      wf: "wf_desc t" and
      fl_f: "field_lookup t (f1 # fs) 0 = Some (tf, n)" and
      fl_g: "field_lookup t g 0 = Some (tg, m)" and
      not_prefix_g_f: "\<not> prefix g (f1 # fs)" and
      not_prefix_f_g:  "\<not> prefix (f1 # fs) g" by simp

    from field_lookup_append_Some [OF wf, where f="[f1]" and g=fs, simplified, OF fl_f]
    obtain w k where fl_f1: "field_lookup t [f1] 0 = Some (w, k)" and fl_fs: "field_lookup w fs k = Some (tf, n)"
      by blast

    from field_lookup_wf_desc_pres(1) [OF wf fl_f1] have wf_w: "wf_desc w".
    show ?case 
    proof (cases g)
      case Nil
      with Cons.prems show ?thesis by simp
    next
      case (Cons g1 gs)
      from field_lookup_append_Some [OF wf, where f="[g1]" and g=gs, simplified, OF fl_g [simplified Cons]]
      obtain v l where fl_g1: "field_lookup t [g1] 0 = Some (v, l)" and fl_gs: "field_lookup v gs l = Some (tg, m)"
        by blast
      show ?thesis
      proof (cases "f1 = g1")
        case True
        with fl_f1 fl_g1 fl_gs obtain
          v_w: "v=w" and k_l: "k=l" and
          fl_g1': "field_lookup t [g1] 0 = Some (w, k)" and fl_gs': "field_lookup w gs k = Some (tg, m)"
          by auto
        from not_prefix_g_f Cons True have not_prefix_gs_fs: "\<not> prefix gs fs" by auto
        from not_prefix_f_g Cons True have not_prefix_fs_gs: "\<not> prefix fs gs" by auto

        from field_lookup_offset_le(1) [OF fl_fs] have le_k_n: "k \<le> n".
        from field_lookup_offset_shift' [OF fl_fs, of 0, simplified]
        have fl_fs': "field_lookup w fs 0 = Some (tf, n - k)".

        from field_lookup_offset_le(1) [OF fl_gs'] have le_k_m: "k \<le> m".
        from field_lookup_offset_shift' [OF fl_gs', of 0, simplified]
        have fl_gs': "field_lookup w gs 0 = Some (tg, m - k)".

      

        from Cons.hyps [OF wf_w fl_fs' fl_gs' not_prefix_gs_fs not_prefix_fs_gs]
        have " {n - k..<n - k + size_td tf} \<inter> {m - k..<m - k + size_td tg} = {}" .
        with le_k_n le_k_m show ?thesis
          by auto
      next
        case False
        from field_lookup_single_field_disj [OF fl_f1 fl_g1 False] 
        have disj: "{k..<k + size_td w} \<inter> {l..<l + size_td v} = {}" .
        from field_lookup_offset_le(1) [OF fl_fs] have k_n: "k \<le> n" .
        from field_lookup_offset_le(1) [OF fl_gs] have l_m: "l \<le> m" .
        from field_lookup_offset_shift' [OF fl_fs, of 0, simplified]
        have fl_fs': "field_lookup w fs 0 = Some (tf, n - k)" .
        from field_lookup_offset_shift' [OF fl_gs, of 0, simplified]
        have fl_gs': "field_lookup v gs 0 = Some (tg, m - l)" .
        from field_lookup_offset_size' [OF fl_fs'] have sz1: "size_td tf + (n - k) \<le> size_td w" .
        from field_lookup_offset_size' [OF fl_gs'] have sz2: "size_td tg + (m - l) \<le> size_td v" .

        show ?thesis
          using disj k_n l_m sz1 sz2
          by auto
      qed
    qed
  qed


theorem root_ptr_valid_non_prefix_disj:
  assumes valid_p: "root_ptr_valid d (p::'a::mem_type ptr)"
  assumes f: "field_lookup (typ_info_t (TYPE('a::mem_type))) f 0 = Some (t, n)"
  assumes g: "field_lookup (typ_info_t (TYPE('a::mem_type))) g 0 = Some (s, m)"
  assumes match_t: "export_uinfo t = typ_uinfo_t (TYPE('c))"
  assumes match_s: "export_uinfo s = typ_uinfo_t (TYPE('d))"
  assumes non_prefix_f_g: "\<not> prefix f g"
  assumes non_prefix_g_f: "\<not> prefix g f"
  shows "ptr_span (PTR('c::mem_type) &(p\<rightarrow>f)) \<inter> ptr_span (PTR('d::mem_type) &(p\<rightarrow>g)) = {}"
proof -
  from field_lookup_non_prefix_disj [OF wf_desc f g non_prefix_g_f non_prefix_f_g]
  have disj: "{n..<n + size_td t} \<inter> {m..<m + size_td s} = {} ".

  from match_t have sz_t: "size_td t = size_of TYPE('c)" 
    using export_size_of by force
  from match_s have sz_s: "size_td s = size_of TYPE('d)" 
    using export_size_of by force
  from f have off_f: "field_offset TYPE('a) f = n" 
    using field_lookup_offset_eq by blast
  from g have off_g: "field_offset TYPE('a) g = m" 
    using field_lookup_offset_eq by blast
  have le_addr_card: "size_td (typ_info_t TYPE('a)) < addr_card"
    by (metis max_size size_of_def)
  from field_lookup_offset_size' [OF f] have t_bound: "size_td t + n \<le> size_td (typ_info_t TYPE('a))".
  with le_addr_card have t_bound': "size_td t + n < addr_card"
    by simp
  from field_lookup_offset_size' [OF g] have s_bound: "size_td s + m \<le> size_td (typ_info_t TYPE('a))".
   with le_addr_card have s_bound': "size_td s + m < addr_card"
    by simp

  show ?thesis
    using disj t_bound' s_bound'
    apply (simp add: sz_t sz_s field_lvalue_def off_f off_g intvl_def)
    apply (safe; clarsimp simp add: unat_of_nat_eq)
    subgoal premises prems for k ka
    proof -
      from prems have "n + k = m + ka"
        by (metis (no_types, opaque_lifting) add.commute len_of_addr_card 
            less_trans nat_add_left_cancel_less of_nat_add sz_t t_bound' unat_of_nat_eq)
      with prems show False by simp
    qed
    subgoal premises prems for k ka
    proof -
      from prems have "n + k = m + ka"
         by (metis (no_types, opaque_lifting) add.commute len_of_addr_card 
            less_trans nat_add_left_cancel_less of_nat_add s_bound' sz_s unat_of_nat_eq)
       with prems show ?thesis by simp
     qed
     done
 qed

theorem root_ptr_valid_non_prefix_h_val_heap_update_eq': 
(* order of assumptions is deliberately choosen, as
 *  it is applied in a tactic by a mixture of resolution and simplifier
 *)
  assumes p': "PTR_MATCH p' (PTR('c) &(p\<rightarrow>f))"
  assumes q': "PTR_MATCH q' (PTR('d) &(q\<rightarrow>g))"
  assumes valid_p: "root_ptr_valid d (p::'a::mem_type ptr)"
  assumes valid_q: "root_ptr_valid d (q::'b::mem_type ptr)"
  assumes disj: "typ_uinfo_t (TYPE('a)) = (typ_uinfo_t (TYPE('b))) \<Longrightarrow>
                 ptr_val p = ptr_val q \<Longrightarrow> 
                 \<not> prefix f g \<and> \<not> prefix g f"
  assumes match_s: "export_uinfo s = typ_uinfo_t (TYPE('d::mem_type))"
  assumes match_t: "export_uinfo t = typ_uinfo_t (TYPE('c::mem_type))"
  assumes g: "field_lookup (typ_info_t (TYPE('b))) g 0 = Some (s, n)"
  assumes f: "field_lookup (typ_info_t (TYPE('a))) f 0 = Some (t, m)"
  shows "h_val (heap_update p' v h) q' = h_val h q'"
proof -
  {
   assume typ_eq: "typ_uinfo_t TYPE('a) = typ_uinfo_t TYPE('b)" 
   assume ptr_val_eq: "ptr_val p = ptr_val q"
   have "ptr_span (PTR('c) &(p\<rightarrow>f)) \<inter> ptr_span (PTR('d) &(q\<rightarrow>g)) = {}"
   proof -
     from disj [OF typ_eq ptr_val_eq] obtain 
       non_prefix_f_g: "\<not> prefix f g"  and non_prefix_g_f: "\<not> prefix g f" by blast

     from typ_eq ptr_val_eq g match_s ptr_val_eq
     have span_eq: "(PTR('d) &(q\<rightarrow>g)) = (PTR('d) &(p\<rightarrow>g))"
       by (simp add: field_lvalue_def field_offset_def)

     from field_lookup_typ_uinfo_t_Some [OF g] typ_eq 
     have fl_u: "field_lookup (typ_uinfo_t TYPE('a)) g 0 = Some (export_uinfo s, n)"
       by simp
     from field_lookup_export_uinfo_Some_rev [OF fl_u [simplified typ_uinfo_t_def]]
      match_s
     obtain s' where fl_g': "field_lookup (typ_info_t TYPE('a)) g 0 = Some (s', n)" and
        match_s': "export_uinfo s' = typ_uinfo_t TYPE('d)"
       by auto

     from root_ptr_valid_non_prefix_disj [OF valid_p f fl_g' match_t match_s' non_prefix_f_g non_prefix_g_f]
     show ?thesis by (simp add: span_eq)
   qed
 } note disj = this
  from root_ptr_valid_field_disj_h_val_heap_update_eq' [OF p' q' valid_p valid_q disj match_s match_t g f]
  show ?thesis by simp
qed

  
lemma field_tag_sub':
  assumes fl: "field_lookup (typ_uinfo_t TYPE('a::mem_type)) f 0 = Some (t, n)"
  shows "{&(p::'a ptr\<rightarrow>f)..+size_td t} \<subseteq> ptr_span p"
proof -
  from field_lookup_uinfo_Some_rev [OF fl] obtain s where
    fl': "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n)" and s_t:  "export_uinfo s = t"
    by auto
  from field_tag_sub [OF fl']
  have "{&(p\<rightarrow>f)..+size_td s} \<subseteq> ptr_span p" .
  with export_uinfo_size s_t
  show "{&(p\<rightarrow>f)..+size_td t} \<subseteq> ptr_span p" by auto
qed


lemma all_field_names_field_lookup:
  assumes "f \<in> set (all_field_names (typ_uinfo_t TYPE('a::mem_type)))"
  shows "\<exists>t n. field_lookup (typ_uinfo_t TYPE('a::mem_type)) f 0 = Some (t, n)"
  using all_field_names_union_field_names_u_conv field_names_u_field_names_export_uinfo_conv(1) field_names_SomeD assms
  by (metis all_field_names_exists_field_names_u(1) field_lookup_export_uinfo_Some not_Some_eq_tuple typ_uinfo_t_def)

lemma field_lvalue_same_type_conv:
  assumes valid_p: "d,g \<Turnstile>\<^sub>t  (p::'a::mem_type ptr)" 
  assumes valid_q: "d,g \<Turnstile>\<^sub>t (q::'a::mem_type ptr)" 
  assumes f1: "f1 \<in> set (all_field_names (typ_uinfo_t TYPE('a)))"  
  assumes f2: "f2 \<in> set (all_field_names (typ_uinfo_t TYPE('a)))"
  shows "(&(p\<rightarrow>f1) = &(q\<rightarrow>f2)) \<longleftrightarrow> (p = q \<and> field_offset (TYPE('a)) f1 = field_offset TYPE('a) f2)"
proof (cases rule: ptr_valid_same_type_cases [OF valid_p valid_q, case_names Same Disj])
  case Same
  with f1 f2 show ?thesis 
    apply (simp add: field_lvalue_def)
    apply (metis all_field_names_exists_field_names_u(1) field_names_SomeD2 
        field_names_u_field_names_export_uinfo_conv(1) typ_uinfo_t_def unat_of_nat_field_offset wf_desc)
    done
next
  case Disj
  from all_field_names_field_lookup [OF f1]
  obtain t1 n1 where fl1: "field_lookup (typ_uinfo_t TYPE('a)) f1 0 = Some (t1, n1)"
    by blast
  from all_field_names_field_lookup [OF f2]
  obtain t2 n2 where fl2: "field_lookup (typ_uinfo_t TYPE('a)) f2 0 = Some (t2, n2)"
    by blast

  from field_tag_sub' [OF fl1, of p] field_tag_sub' [OF fl2, of q] Disj
  have "{&(p\<rightarrow>f1)..+size_td t1} \<inter> {&(q\<rightarrow>f2)..+size_td t2} = {}"
    by blast
  moreover
  from field_lookup_wf_size_desc_gt [OF fl1] have "0 < size_td t1" by simp
  then have "&(p\<rightarrow>f1) \<in> {&(p\<rightarrow>f1)..+size_td t1}"
    using first_in_intvl by blast
  moreover
  from field_lookup_wf_size_desc_gt [OF fl2] have "0 < size_td t2" by simp
  then have "&(q\<rightarrow>f2) \<in> {&(q\<rightarrow>f2)..+size_td t2}"
    using first_in_intvl by blast
  ultimately
  have "&(p\<rightarrow>f1) \<noteq> &(q\<rightarrow>f2)"
    by auto
  thus ?thesis
    by (auto simp add: field_lvalue_def field_offset_def field_offset_untyped_def size_of_def fl1 fl2) 
qed

lemma field_lvalue_same_root_conv:
  assumes f1: "field_lookup (typ_info_t TYPE('a::mem_type)) f1 0 = Some(t1, n1)"  
  assumes f2: "field_lookup (typ_info_t TYPE('a::mem_type)) f2 0 = Some(t2, n2)" 
  shows "(&(p::'a ptr\<rightarrow>f1) = &(p\<rightarrow>f2)) \<longleftrightarrow> (n1 = n2)"
proof -
  have max: "size_of TYPE('a) < addr_card" by (rule max_size)
  from f1
  have n1_bound: "n1 < addr_card"
    using field_lookup_offset_eq field_offset_addr_card by blast

  from f2
  have n2_bound: "n2 < addr_card"
    using field_lookup_offset_eq field_offset_addr_card by blast
  from n1_bound n2_bound field_lookup_offset_size [OF f1] field_lookup_offset_size [OF f2]
  show ?thesis
    apply (simp add: field_lvalue_def field_lookup_offset_eq [OF f1] field_lookup_offset_eq [OF f2])
    by (metis len_of_addr_card unat_of_nat_eq)
qed

lemma field_lvalue_same_type_conv':
  assumes valid_p: "d,g \<Turnstile>\<^sub>t  (p::'a::mem_type ptr)" 
  assumes valid_q: "d,g \<Turnstile>\<^sub>t (q::'a::mem_type ptr)" 
  assumes f1: "f1 \<in> set (all_field_names_no_padding (typ_info_t TYPE('a)))"  
  assumes f2: "f2 \<in> set (all_field_names_no_padding (typ_info_t TYPE('a)))"
  shows "(&(p\<rightarrow>f1) = &(q\<rightarrow>f2)) \<longleftrightarrow> (p = q \<and> field_offset (TYPE('a)) f1 = field_offset TYPE('a) f2)"
proof -
  have "set (all_field_names_no_padding (typ_info_t TYPE('a))) \<subseteq> set (all_field_names (typ_uinfo_t TYPE('a)))"
    using subset_all_field_names_no_padding_all_field_names
      all_field_names_typ_uinfo_t_conv
    by metis
  then
  show ?thesis using field_lvalue_same_type_conv [OF valid_p valid_q] f1 f2 
    by blast
qed

lemma field_lvalue_same_root_conv':
  assumes f1: "f1 \<in> set (all_field_names (typ_uinfo_t TYPE('a::mem_type)))"  
  assumes f2: "f2 \<in> set (all_field_names (typ_uinfo_t TYPE('a)))"
  shows "(&(p::'a ptr\<rightarrow>f1) = &(p\<rightarrow>f2)) \<longleftrightarrow> (field_offset (TYPE('a)) f1 = field_offset TYPE('a) f2)"
proof -
  from all_field_names_field_lookup [OF f1]
  obtain t1 n1 where fl1: "field_lookup (typ_uinfo_t TYPE('a)) f1 0 = Some (t1, n1)"
    by blast
  from all_field_names_field_lookup [OF f2]
  obtain t2 n2 where fl2: "field_lookup (typ_uinfo_t TYPE('a)) f2 0 = Some (t2, n2)"
    by blast


  have max: "size_of TYPE('a) < addr_card" by (rule max_size)
 
  from field_lookup_offset_size' [OF fl1]
  have "n1 < size_of TYPE('a)"
    apply (simp add: size_of_def)
    by (metis add_diff_cancel_right' add_leD2 cancel_comm_monoid_add_class.diff_cancel field_lookup_wf_size_desc_gt 
        less_le local.fl1 not_add_less2 wf_size_desc_typ_uinfo_t_simp)
  with max have "n1 < addr_card" by arith


  moreover
  from field_lookup_offset_size' [OF fl2]
  have "n2 < size_of TYPE('a)"
    apply (simp add: size_of_def)
    by (metis add_diff_cancel_right' add_leD2 cancel_comm_monoid_add_class.diff_cancel field_lookup_wf_size_desc_gt 
        le_imp_less_or_eq less_not_refl2 local.fl2 not_add_less2 wf_size_desc_typ_uinfo_t_simp)
  with max have "n2 < addr_card" by arith

  ultimately

  show ?thesis
    apply (simp add: field_offset_def field_offset_untyped_def fl1 fl2 field_lvalue_def size_of_def)
    by (metis len_of_addr_card unat_of_nat_eq)

qed

lemma field_lvalue_same_root_conv'':
  assumes f1: "f1 \<in> set (all_field_names_no_padding (typ_info_t TYPE('a::mem_type)))"  
  assumes f2: "f2 \<in> set (all_field_names_no_padding (typ_info_t TYPE('a)))"
  shows "(&(p::'a ptr\<rightarrow>f1) = &(p\<rightarrow>f2)) \<longleftrightarrow> (field_offset (TYPE('a)) f1 = field_offset TYPE('a) f2)"
proof -
  have "set (all_field_names_no_padding (typ_info_t TYPE('a::mem_type))) \<subseteq> 
        set (all_field_names (typ_uinfo_t TYPE('a::mem_type)))"
    using subset_all_field_names_no_padding_all_field_names
      all_field_names_typ_uinfo_t_conv
    by metis
  with field_lvalue_same_root_conv' f1 f2 show ?thesis 
    by blast
qed


lemma disj_ptr_span_field_neq: 
  assumes disj: "ptr_span (p::'a::mem_type ptr) \<inter> ptr_span (q::'b::mem_type ptr) = {}"
  assumes fl1: "field_lookup (typ_info_t TYPE('a)) f1 0 = Some (t1, n1)"
  assumes fl2: "field_lookup (typ_info_t TYPE('b)) f2 0 = Some (t2, n2)"
  shows "&(p\<rightarrow>f1) \<noteq> &(q\<rightarrow>f2)"
proof -
  from field_tag_sub [OF fl1, of p] have "{&(p\<rightarrow>f1)..+size_td t1} \<subseteq> ptr_span p" .
  moreover 
  from field_tag_sub [OF fl2, of q] have "{&(q\<rightarrow>f2)..+size_td t2} \<subseteq> ptr_span q" .
  moreover
  from field_lookup_wf_size_desc_gt [OF fl1] have "0 < size_td t1" by simp
  then have "&(p\<rightarrow>f1) \<in> {&(p\<rightarrow>f1)..+size_td t1}"
    using first_in_intvl by blast
  moreover
  from field_lookup_wf_size_desc_gt [OF fl2] have "0 < size_td t2" by simp
  then have "&(q\<rightarrow>f2) \<in> {&(q\<rightarrow>f2)..+size_td t2}"
    using first_in_intvl by blast
  ultimately
  show "&(p\<rightarrow>f1) \<noteq> &(q\<rightarrow>f2)"
    using disj
    by force
qed

lemma disj_ptr_span_field_neq'': 
  assumes disj: "ptr_span (p::'a::mem_type ptr) \<inter> ptr_span (q::'b::mem_type ptr) = {}"
  assumes f1: "f1 \<in> set (all_field_names (typ_uinfo_t TYPE('a)))"
  assumes f2: "f2 \<in> set (all_field_names (typ_uinfo_t TYPE('b)))"
  shows "&(p\<rightarrow>f1) \<noteq> &(q\<rightarrow>f2)"
proof -
  from all_field_names_field_lookup [OF f1]
  obtain t1 n1 where fl1: "field_lookup (typ_uinfo_t TYPE('a)) f1 0 = Some (t1, n1)"
    by blast
  from all_field_names_field_lookup [OF f2]
  obtain t2 n2 where fl2: "field_lookup (typ_uinfo_t TYPE('b)) f2 0 = Some (t2, n2)"
    by blast
  from field_tag_sub' [OF fl1, of p] have "{&(p\<rightarrow>f1)..+size_td t1} \<subseteq> ptr_span p" .
  moreover 
  from field_tag_sub' [OF fl2, of q] have "{&(q\<rightarrow>f2)..+size_td t2} \<subseteq> ptr_span q" .
  moreover
  from field_lookup_wf_size_desc_gt [OF fl1] have "0 < size_td t1" by simp
  then have "&(p\<rightarrow>f1) \<in> {&(p\<rightarrow>f1)..+size_td t1}"
    using first_in_intvl by blast
  moreover
  from field_lookup_wf_size_desc_gt [OF fl2] have "0 < size_td t2" by simp
  then have "&(q\<rightarrow>f2) \<in> {&(q\<rightarrow>f2)..+size_td t2}"
    using first_in_intvl by blast
  ultimately
  show "&(p\<rightarrow>f1) \<noteq> &(q\<rightarrow>f2)"
    using disj
    by force
qed

lemma disj_ptr_span_field_neq': 
  assumes disj: "ptr_span (p::'a::mem_type ptr) \<inter> ptr_span (q::'b::mem_type ptr) = {}"
  assumes f1: "f1 \<in> set (all_field_names_no_padding (typ_info_t TYPE('a)))"
  assumes f2: "f2 \<in> set (all_field_names_no_padding (typ_info_t TYPE('b)))"
  shows "&(p\<rightarrow>f1) \<noteq> &(q\<rightarrow>f2)"
proof -
  have "set (all_field_names_no_padding (typ_info_t TYPE('a))) \<subseteq> set (all_field_names (typ_uinfo_t TYPE('a)))"
    using subset_all_field_names_no_padding_all_field_names
      all_field_names_typ_uinfo_t_conv
    by metis
  moreover
  have "set (all_field_names_no_padding (typ_info_t TYPE('b))) \<subseteq> set (all_field_names (typ_uinfo_t TYPE('b)))"
    using subset_all_field_names_no_padding_all_field_names
    all_field_names_typ_uinfo_t_conv
    by metis
  ultimately 
  show ?thesis using disj f1 f2 disj_ptr_span_field_neq'' by blast
qed

lemma disj_ptr_span_field_disj_ptr_span: 
  assumes disj: "ptr_span (p::'a::mem_type ptr) \<inter> ptr_span (q::'b::mem_type ptr) = {}"
  assumes f1: "f1 \<in> set (field_names_u (typ_uinfo_t TYPE('a)) (typ_uinfo_t (TYPE('c::mem_type))))"
  assumes f2: "f2 \<in> set (field_names_u (typ_uinfo_t TYPE('b)) (typ_uinfo_t (TYPE('d::mem_type))))"
  shows "ptr_span (PTR('c) &(p\<rightarrow>f1)) \<inter> ptr_span (PTR('d) (&(q\<rightarrow>f2))) = {}"
proof -
  from f1 
  obtain n1 where fl1: "field_lookup (typ_uinfo_t TYPE('a)) f1 0 = Some (typ_uinfo_t (TYPE('c::mem_type)), n1)"
    apply (simp add: typ_uinfo_t_def)
    by (smt (verit) field_lookup_export_uinfo_Some field_names_SomeD2 field_names_u_field_names_export_uinfo_conv(1) wf_desc)
  from f2
  obtain n2 where fl2: "field_lookup (typ_uinfo_t TYPE('b)) f2 0 = Some (typ_uinfo_t (TYPE('d::mem_type)), n2)"
    apply (simp add: typ_uinfo_t_def)
    by (smt (verit) field_lookup_export_uinfo_Some field_names_SomeD2 field_names_u_field_names_export_uinfo_conv(1) wf_desc)
   
  from field_tag_sub' [OF fl1, of p] have "{&(p\<rightarrow>f1)..+size_of TYPE('c)} \<subseteq> ptr_span p" 
    by (simp add: size_of_tag)
  moreover 
  from field_tag_sub' [OF fl2, of q] have "{&(q\<rightarrow>f2)..+size_of TYPE('d)} \<subseteq> ptr_span q" 
    by (simp add: size_of_tag)
  ultimately show ?thesis
    using disj
    by auto
qed

lemma disj_ptr_span_field_disj_ptr_span': 
  assumes disj: "ptr_span (p::'a::mem_type ptr) \<inter> ptr_span (q::'b::mem_type ptr) = {}"
  assumes f1: "field_lookup (typ_info_t (TYPE('a))) f1 0 = Some (s, n)"
  assumes match_s: "export_uinfo s = typ_uinfo_t (TYPE('c::mem_type))"
  assumes f2: "field_lookup (typ_info_t (TYPE('b))) f2 0 = Some (t, m)"
  assumes match_t: "export_uinfo t = typ_uinfo_t (TYPE('d::mem_type))"
  shows "{&(p\<rightarrow>f1)..+size_of TYPE('c)} \<inter> {&(q\<rightarrow>f2)..+size_of TYPE('d)} = {}"
proof -
  from f1 match_s 
  have f1': "f1 \<in> set (field_names_u (typ_uinfo_t TYPE('a)) (typ_uinfo_t (TYPE('c::mem_type))))"
    by (simp add: field_lookup_all_field_names(1) field_lookup_field_ti set_field_names_u_all_field_names_conv)
  from f2 match_t 
  have f2': "f2 \<in> set (field_names_u (typ_uinfo_t TYPE('b)) (typ_uinfo_t (TYPE('d::mem_type))))"
    by (simp add: field_lookup_all_field_names(1) field_lookup_field_ti set_field_names_u_all_field_names_conv)
  from disj_ptr_span_field_disj_ptr_span [OF disj f1' f2'] 
  show ?thesis
    by simp
qed

lemma disj_ptr_span_field_disj_ptr_span'': 
  assumes disj: "ptr_span (p::'a::mem_type ptr) \<inter> ptr_span (q::'b::mem_type ptr) \<equiv> {}"
  assumes f1: "field_lookup (typ_info_t (TYPE('a))) f1 0 = Some (s, n)"
  assumes match_s: "export_uinfo s = typ_uinfo_t (TYPE('c::mem_type))"
  assumes f2: "field_lookup (typ_info_t (TYPE('b))) f2 0 = Some (t, m)"
  assumes match_t: "export_uinfo t = typ_uinfo_t (TYPE('d::mem_type))"
  shows "{&(p\<rightarrow>f1)..+size_of TYPE('c)} \<inter> {&(q\<rightarrow>f2)..+size_of TYPE('d)} = {}"
  using disj_ptr_span_field_disj_ptr_span' [OF _ f1 match_s f2 match_t]
  by (simp add: disj)

lemma root_ptr_valid_disj_field_lvalue_conv:
  assumes valid_p: "root_ptr_valid d (p::'a::mem_type ptr)" 
  assumes valid_q: "root_ptr_valid d (q::'b::mem_type ptr)" 
  assumes neq: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b) "
  assumes f1: "f1 \<in> set (all_field_names (typ_uinfo_t TYPE('a)))"  
  assumes f2: "f2 \<in> set (all_field_names (typ_uinfo_t TYPE('b)))"
  shows "&(p\<rightarrow>f1) = &(q\<rightarrow>f2) = False"
  using root_ptr_valid_type_neq_disjoint [OF valid_p valid_q neq] f1 f2
  by (simp add: disj_ptr_span_field_neq'')

lemma root_ptr_valid_disj_field_lvalue_conv':
  assumes valid_p: "root_ptr_valid d (p::'a::mem_type ptr)" 
  assumes valid_q: "root_ptr_valid d (q::'b::mem_type ptr)" 
  assumes neq: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b) "
  assumes f1: "f1 \<in> set (all_field_names (typ_info_t TYPE('a)))"  
  assumes f2: "f2 \<in> set (all_field_names (typ_info_t TYPE('b)))"
  shows "&(p\<rightarrow>f1) = &(q\<rightarrow>f2) = False"
proof -
  have "set (all_field_names (typ_info_t TYPE('a))) = set (all_field_names (typ_uinfo_t TYPE('a)))"
    by (simp add: all_field_names_typ_uinfo_t_conv)
  moreover
  have "set (all_field_names (typ_info_t TYPE('b))) = set (all_field_names (typ_uinfo_t TYPE('b)))"
    by (simp add: all_field_names_typ_uinfo_t_conv)
  ultimately show ?thesis using root_ptr_valid_disj_field_lvalue_conv [OF valid_p valid_q neq] f1 f2
    by simp
qed

lemma intvl_non_zero_non_empty: "0 < n \<Longrightarrow> {p..+n} \<noteq> {}"
  by (metis empty_iff first_in_intvl less_numeral_extra(3))

lemma disj_inter_swap: "A \<inter> B = {} \<Longrightarrow> B \<inter> A = {}"
  by blast

lemma h_val_clift_field:
  "clift hp (Ptr &(p\<rightarrow>f)) = Some v \<Longrightarrow> v = h_val (hrs_mem hp) (Ptr &(p\<rightarrow>f))"
  by (simp add: h_val_clift')

lemma valid_root_footprints_no_overlap:
  assumes "valid_root_footprint d (ptr_val (p::'a::mem_type ptr)) (typ_uinfo_t TYPE('a))"
  assumes "valid_root_footprint d (ptr_val (q::'b::mem_type ptr)) (typ_uinfo_t TYPE('b))"
  assumes "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b)"
  shows "ptr_span p \<inter> ptr_span q = {}"
  by (metis antisym_conv assms(1) assms(2) assms(3) disj_inter_swap 
     export_uinfo_size size_of_def typ_uinfo_t_def valid_root_footprint_overlap_sub_typ valid_root_footprint_valid_footprint)

lemma valid_root_footprints_overlap:
  assumes "valid_root_footprint d (ptr_val (p::'a::mem_type ptr)) (typ_uinfo_t TYPE('a))"
  assumes "valid_root_footprint d (ptr_val (q::'b::mem_type ptr)) (typ_uinfo_t TYPE('b))"
  assumes "ptr_span p \<inter> ptr_span q \<noteq> {}"
  shows "(typ_uinfo_t TYPE('a)) = (typ_uinfo_t TYPE('b))"
  by (meson assms(1) assms(2) assms(3) valid_root_footprints_no_overlap)
  

lemma field_lookup_same_type_empty:
"field_lookup t f n = Some (s, m) \<Longrightarrow> s = t \<longleftrightarrow> f = []" 
"field_lookup_struct st f n = Some (s, m) \<Longrightarrow> f \<noteq> []"
"field_lookup_list ts f n = Some (s, m) \<Longrightarrow> f \<noteq> []"
"field_lookup_tuple td f n = Some (s, m) \<Longrightarrow> f \<noteq> []"
  apply (induct t and st and ts and td arbitrary: f n s m and f n s m  and f n s m  and f n s m )
  apply (auto split: if_split_asm dest!: td_set_struct_field_lookup_structD  td_set_struct_size_lte)
  done


lemma root_ptr_valid_root_only: 
  assumes valid: "root_ptr_valid d (p::'a::mem_type ptr)"
  assumes non_empty: "f \<noteq> []"
  assumes f: "f \<in> set (field_names_u (typ_uinfo_t TYPE('a)) (typ_uinfo_t TYPE('b)))"  
  shows "root_ptr_valid d (PTR('b::mem_type) &(p\<rightarrow>f)) = False"
proof -
  {
    assume "root_ptr_valid d (PTR('b::mem_type) &(p\<rightarrow>f))"
    hence valid_root: "valid_root_footprint d (ptr_val (PTR('b::mem_type) &(p\<rightarrow>f))) (typ_uinfo_t TYPE('b))"
      by (simp add: root_ptr_valid_def)

    have wf: "wf_desc (typ_info_t TYPE('a))" by simp
    from valid have valid_p: "valid_root_footprint d (ptr_val p) (typ_uinfo_t TYPE('a))"
      by (simp add: root_ptr_valid_def)


    from f have "f \<in> set (field_names (typ_info_t TYPE('a)) (typ_uinfo_t TYPE('b)))"
      by (simp add: field_names_u_field_names_export_uinfo_conv(1) typ_uinfo_t_def)

    from field_names_SomeD2 [OF this wf] obtain s n where 
      fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n)" and s: "export_uinfo s = typ_uinfo_t TYPE('b)"
      by blast

    from field_lookup_export_uinfo_Some [OF fl] s
    have fl': "field_lookup (typ_uinfo_t TYPE('a)) f 0 = Some (typ_uinfo_t TYPE('b), n)" by (simp add: typ_uinfo_t_def)

    from field_lookup_same_type_empty(1) [OF this] non_empty
    have "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b)" by simp
    from valid_root_footprints_no_overlap [OF valid_p valid_root this]
    have "disjnt (ptr_span p) (ptr_span (PTR('b) &(p\<rightarrow>f)))" by (simp add: disjnt_def)
    moreover
    from field_tag_sub' [OF fl'] have " {&(p\<rightarrow>f)..+size_td (typ_uinfo_t TYPE('b))} \<subseteq> ptr_span p" .
    ultimately
    have False
      by (metis Int_absorb Int_absorb1 disj_ptr_span_ptr_neq disjnt_def ptr_val.ptr_val_def
          size_of_tag)
  } thus ?thesis by blast
qed

lemma root_ptr_valid_root_only': 
  assumes valid: "root_ptr_valid d (p::'a::mem_type ptr)"
  assumes non_empty: "f \<noteq> []"
  assumes f: "f \<in> set (field_names (typ_info_t TYPE('a)) (export_uinfo (typ_info_t TYPE('b))))"  
  shows "root_ptr_valid d (PTR('b::mem_type) &(p\<rightarrow>f)) = False"
proof -
  have "set (field_names (typ_info_t TYPE('a)) (export_uinfo (typ_info_t TYPE('b)))) = 
        set (field_names_u (typ_uinfo_t TYPE('a)) (typ_uinfo_t TYPE('b)))" 
    by (simp add: fold_typ_uinfo_t set_field_names_all_field_names_conv set_field_names_u_all_field_names_conv)
  with root_ptr_valid_root_only [OF valid non_empty] f
  show ?thesis
    by simp
qed

lemma disj_subset:
  assumes "A \<inter> B = {}"
  assumes "A' \<subseteq> A"
  assumes "B' \<subseteq> B"
  shows "A' \<inter> B' = {}"
using assms
  by blast


lemma disj_intvl_subset: 
  assumes disj: "{p..+n1} \<inter> {q..+m1} = {}"
  assumes le1: "n2 + off1 \<le> n1"
  assumes le2: "m2 + off2 \<le> m1"
  shows "{p + of_nat off1..+n2} \<inter> {q + of_nat off2..+m2} = {}"
  apply (rule disj_subset [OF disj])
   apply (rule intvl_le [OF le1])
  apply (rule intvl_le [OF le2])
  done

lemma disj_intvl_field': 
  assumes disj: "{ptr_val p..+n1} \<inter> {ptr_val q..+m1} = {}"
  assumes f: "&(p\<rightarrow>f) = ptr_val p + (of_nat off1)"
  assumes g: "&(q\<rightarrow>g) = ptr_val q + (of_nat off2)"
  assumes le1: "n2 + off1 \<le> n1"
  assumes le2: "m2 + off2 \<le> m1"
  shows "{&(p\<rightarrow>f)..+n2} \<inter> {&(q\<rightarrow>g)..+m2} = {}"
  apply (simp add: f g)
  apply (rule disj_intvl_subset [OF disj le1 le2])
  done


lemma disj_intvl_field: 
  assumes disj: "{ptr_val (p::'a::mem_type ptr)..+n1} \<inter> {ptr_val (q::'b::mem_type ptr)..+m1} = {}"
  assumes le1: "n2 + (field_offset TYPE('a) f) \<le> n1"
  assumes le2: "m2 + (field_offset TYPE('b) g) \<le> m1"
  shows "{&(p\<rightarrow>f)..+n2} \<inter> {&(q\<rightarrow>g)..+m2} = {}"
  apply (simp add: field_lvalue_def)
  apply (rule disj_intvl_subset [OF disj le1 le2])
  done

lemma intvl_fields_disj1: 
assumes f: "&(p\<rightarrow>f) = ptr_val p + off1"
assumes g: "&(p\<rightarrow>g) = ptr_val p + off2"
assumes n_sz: "unat off1 + n \<le> addr_card"
assumes m_sz: "unat off2 + m \<le> addr_card"
assumes le: "unat off1 \<le> unat off2"
assumes disj: "unat off1 + n \<le> unat off2"
shows"{&(p\<rightarrow>f)..+n} \<inter> {&(p\<rightarrow>g)..+m} = {}"
proof -
  {
   fix k k'
   assume k_n: "k < n" 
   assume k'_m: "k' < m"
   assume eq: "off1 + word_of_nat k = off2 + word_of_nat k'"
   have False
   proof -
     from eq n_sz m_sz k_n k'_m have "unat off1 + k = unat off2 + k'"
       by (metis (no_types, opaque_lifting) word_bits_def add.right_neutral 
           len_of_addr_card less_le_trans nat_add_left_cancel_less of_nat_add unat_0 unat_of_nat_eq word_arith_nat_add)
     with disj k_n show False by arith
   qed
 } note lem = this
  show ?thesis

    apply (simp add: f g)
    apply (clarsimp simp add: intvl_def)
    using lem
    by auto
qed

lemma intvl_fields_disj: 
assumes f: "&(p\<rightarrow>f) = ptr_val p + off1"
assumes g: "&(p\<rightarrow>g) = ptr_val p + off2"
assumes n_sz: "unat off1 + n \<le> addr_card"
assumes m_sz: "unat off2 + m \<le> addr_card"
assumes disj: "if unat off1 \<le> unat off2 then unat off1 + n \<le> unat off2 else unat off2 + m \<le> unat off1"
shows"{&(p\<rightarrow>f)..+n} \<inter> {&(p\<rightarrow>g)..+m} = {}"
proof (cases "unat off1 \<le> unat off2")
  case True
  show ?thesis 
    apply (rule intvl_fields_disj1 [OF f g n_sz m_sz])
    using disj True
    by simp_all
next
  case False
  have "{&(p\<rightarrow>g)..+m} \<inter> {&(p\<rightarrow>f)..+n} = {}"
    apply (rule intvl_fields_disj1 [OF g f m_sz n_sz])
    using disj False
    by simp_all
  thus ?thesis by blast
qed


lemma intvl_fields_disj_calculation: 
assumes f: "&(p\<rightarrow>f) = ptr_val p + off1"
assumes g: "&(p\<rightarrow>g) = ptr_val p + off2"
assumes uoff1: "unat off1 = uoff1"
assumes uoff2: "unat off2 = uoff2"
assumes n_sz: "uoff1 + n \<le> addr_card"
assumes m_sz: "uoff2 + m \<le> addr_card"
assumes disj: "if uoff1 \<le> uoff2 then uoff1 + n \<le> uoff2 else uoff2 + m \<le> uoff1"
shows "{&(p\<rightarrow>f)..+n} \<inter> {&(p\<rightarrow>g)..+m} = {}"
  using intvl_fields_disj [OF f g] uoff1 uoff2 n_sz m_sz disj by simp

lemma disjoint_field_lvalue_propagation_right:
  fixes q::"'a::mem_type ptr"
  assumes disj: "A \<inter> {ptr_val q..+m} = {}"
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0  = Some (t, k)"
  assumes m: "m = size_of TYPE('a)"
  assumes n: "n = size_td t"
  shows "A \<inter> {&(q\<rightarrow>f)..+n} = {}"
  using disj fl m n
  by (meson disjoint_iff field_tag_sub subsetD)

lemma disjoint_field_lvalue_propagation_left:
  fixes q::"'a::mem_type ptr"
  assumes disj: "{ptr_val q..+m} \<inter> A = {}"
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0  = Some (t, k)"
  assumes m: "m = size_of TYPE('a)"
  assumes n: "n = size_td t"
  shows "{&(q\<rightarrow>f)..+n} \<inter> A = {}"
  using disj fl m n
  by (meson disjoint_iff field_tag_sub subsetD)


lemma disjoint_field_lvalue_propagation_both:
  fixes q::"'a::mem_type ptr"
  fixes p::"'b::mem_type ptr"
  assumes disj: "{ptr_val q..+m1} \<inter> {ptr_val p..+m2} = {}"
  assumes fl1: "field_lookup (typ_info_t TYPE('a)) f1 0  = Some (t1, k1)"
  assumes fl2: "field_lookup (typ_info_t TYPE('b)) f2 0  = Some (t2, k2)"
  assumes m1: "m1 = size_of TYPE('a)"
  assumes n1: "n1 = size_td t1"
  assumes m2: "m2 = size_of TYPE('b)"
  assumes n2: "n2 = size_td t2"
  shows "{&(q\<rightarrow>f1)..+n1} \<inter> {&(p\<rightarrow>f2)..+n2} = {}"
  using disj fl1 fl2 m1 n1 m2 n2
  by (meson disjoint_iff field_tag_sub subsetD)

lemmas disjoint_field_lvalue_propagation = 
  disjoint_field_lvalue_propagation_left
  disjoint_field_lvalue_propagation_right
  disjoint_field_lvalue_propagation_both

lemma disjoint_field_lvalue_neq:
  fixes q::"'a::mem_type ptr"
  fixes p::"'b::mem_type ptr"
  assumes disj: "{ptr_val q..+m1} \<inter> {ptr_val p..+m2} = {}"
  assumes fl1: "field_lookup (typ_info_t TYPE('a)) f1 0  = Some (t1, k1)"
  assumes fl2: "field_lookup (typ_info_t TYPE('b)) f2 0  = Some (t2, k2)"
  assumes m1: "m1 = size_of TYPE('a)"
  assumes n1: "n1 = size_td t1"
  assumes m2: "m2 = size_of TYPE('b)"
  assumes n2: "n2 = size_td t2"
  shows "&(q\<rightarrow>f1) = &(p\<rightarrow>f2) = False"
  using disjoint_field_lvalue_propagation_both [OF disj fl1 fl2 m1 n1 m2 n2 ] n1 n2
  by (metis field_lookup_wf_size_desc_gt intvl_start_inter local.fl1 local.fl2 wf_size_desc)

lemma overlap_field_disj_contradiction:
  fixes q::"'a::mem_type ptr"
  assumes overlap: "A \<inter> {&(q\<rightarrow>f)..+n} \<noteq> {}"  
  assumes disj: "A \<inter> {ptr_val q..+m} = {}"
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0  = Some (t, k)"
  assumes m: "m = size_of TYPE('a)"
  assumes n: "n = size_td t"
  shows False
  using overlap disj fl m n
  by (meson disjoint_iff field_tag_sub subsetD)

thm root_ptr_valid_non_prefix_disj

lemma overlap_field_prefix_left:
  fixes p::"'a::mem_type ptr"
  assumes overlap: "{&(p\<rightarrow>f) ..+n1} \<inter> {&(p\<rightarrow>g) ..+n2} \<noteq> {}"
  assumes less: "length f < length g"
  assumes f: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (t1, k1)"
  assumes g: "field_lookup (typ_info_t TYPE('a)) g 0 = Some (t2, k2)"
  assumes n1: "n1 = size_td t1"
  assumes n2: "n2 = size_td t2"
  shows "prefix f g"
proof (cases "prefix f g")
  case True
  then show ?thesis by simp
next
  case False
  from less have not_prefix: "\<not> prefix g f"
    by (simp add: More_Sublist.not_prefix_longer)
  have wf:"wf_desc (typ_info_t TYPE('a))" by simp
  have le_addr_card: "size_td (typ_info_t TYPE('a)) < addr_card"
    by (metis max_size size_of_def)
  from field_lookup_offset_size' [OF f] have t1_bound: "size_td t1 + k1 \<le> size_td (typ_info_t TYPE('a))".
  with le_addr_card have t1_bound': "size_td t1 + k1 < addr_card"
    by simp
  from field_lookup_offset_size' [OF g] have t2_bound: "size_td t2 + k2 \<le> size_td (typ_info_t TYPE('a))".
  with le_addr_card have t2_bound': "size_td t2 + k2 < addr_card"
    by simp

  from field_lookup_non_prefix_disj [OF wf f g not_prefix False] overlap n1 n2 
  have False 
    using f g
    apply (simp add: field_lvalue_def intvl_def)
    apply (safe; clarsimp simp add: unat_of_nat_eq)
    subgoal premises prems for k ka
    proof -
      from prems  have "k1 + k = k2 + ka"
        by (smt (verit, ccfv_threshold) Abs_fnat_hom_add add.commute add_mono_thms_linordered_field(2) 
            of_nat_lt_size_of order_less_le_trans size_of_def t1_bound t2_bound)
      with prems show False by simp
    qed
    subgoal premises prems for k ka
    proof -
      from prems  have "k1 + k = k2 + ka"
        by (smt (verit, ccfv_threshold) Abs_fnat_hom_add add.commute add_mono_thms_linordered_field(2) 
            of_nat_lt_size_of order_less_le_trans size_of_def t1_bound t2_bound)
      with prems show False by simp
    qed
    done
  thus ?thesis by simp
qed

lemma overlap_field_prefix_right:
  fixes p::"'a::mem_type ptr"
  assumes overlap: "{&(p\<rightarrow>g) ..+n2} \<inter> {&(p\<rightarrow>f) ..+n1} \<noteq> {}"
  assumes less: "length f < length g"
  assumes f: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (t1, k1)"
  assumes g: "field_lookup (typ_info_t TYPE('a)) g 0 = Some (t2, k2)"
  assumes n1: "n1 = size_td t1"
  assumes n2: "n2 = size_td t2"
  shows "prefix f g"
  using overlap_field_prefix_left
  using f g less n1 n2 overlap by blast

lemma field_lvalue_eq_non_prefix:
  fixes p::"'a::mem_type ptr"
  assumes fld_eq:  "&(p\<rightarrow>f) = &(p\<rightarrow>g)"
  assumes f: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (t1, k1)"
  assumes g: "field_lookup (typ_info_t TYPE('a)) g 0 = Some (t2, k2)"
  assumes f_g: "\<not> prefix f g"
  assumes g_f: "\<not> prefix g f"
  shows "f = g"
proof -
  have wf:"wf_desc (typ_info_t TYPE('a))" by simp
  show ?thesis using field_lookup_non_prefix_disj [OF wf f g g_f f_g] fld_eq f g
    apply (simp add: field_lvalue_def) 
    by (metis field_lookup_wf_size_desc_pres(1) field_lvalue_same_root_conv fld_eq 
        less_add_same_cancel1 nat_neq_iff wf_size_desc wf_size_desc_gt(1))
qed

lemma field_lvalue_eq_non_prefix_conv:
  fixes p::"'a::mem_type ptr"
  assumes f: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (t1, k1)"
  assumes g: "field_lookup (typ_info_t TYPE('a)) g 0 = Some (t2, k2)"
  assumes f_g: "\<not> prefix f g"
  assumes g_f: "\<not> prefix g f"
  shows "&(p\<rightarrow>f) = &(p\<rightarrow>g) \<longleftrightarrow> f = g"
  apply standard
   apply (drule field_lvalue_eq_non_prefix [OF _ f g f_g g_f])
   apply simp
  apply simp
  done

thm cvalid_field_pres''


lemma hrs_mem_update_comp: "hrs_mem_update f o hrs_mem_update g = hrs_mem_update (f o g)"
  apply (rule ext)
  apply (auto simp add: hrs_mem_update_def)
  done

lemma hrs_mem_update_comp': "hrs_mem_update f (hrs_mem_update g s) = hrs_mem_update (f o g) s"
  using hrs_mem_update_comp
  by (metis comp_eq_dest_lhs)

named_theorems plift_defs and 
 plift_cond_simps and 
 plift_iff and 
 plift_eqI and 
 ptr_valid_h_t_valid and
 plift_heap_update and
 ptr_valid_intros and
 h_val_field_plift and
 the_plift_h_val_conv

lemma map_option_the_conv: "f (the (map_option g x)) = f (the x) \<longleftrightarrow> (\<forall>v. x = Some v \<longrightarrow> f (g v) = f v)"
  by (metis handy_if_lemma option.exhaust_sel option.map_sel option.simps(8))

definition the_default:: "'a \<Rightarrow> 'a option \<Rightarrow> 'a" where 
  "the_default x v = (case v of Some z \<Rightarrow> z | None \<Rightarrow> x)"

lemma the_default_simps[simp]: 
  "the_default x None = x"
  "the_default x (Some z) = z"
  by (auto simp add: the_default_def)


locale wf_ptr_valid =
  fixes ptr_valid::"heap_typ_desc \<Rightarrow> 'a::mem_type ptr_guard"
  assumes ptr_valid_h_t_valid[ptr_valid_h_t_valid]: "\<And>d. ptr_valid d p \<Longrightarrow> d \<Turnstile>\<^sub>t p"
begin

definition plift:: "heap_raw_state \<Rightarrow> 'a typ_heap"  
  where [plift_defs]:"plift h = lift_t (ptr_valid (hrs_htd h)) h"

lemma plift_Some_iff [plift_iff]: 
  shows "(\<exists>v. plift h p = Some v) \<longleftrightarrow> ptr_valid (hrs_htd h) p"
  using ptr_valid_h_t_valid
  apply (cases h)
  apply (auto simp add: plift_def TypHeap.lift_t_if  hrs_htd_def h_t_valid_def)
  done

lemma plift_None_iff [plift_iff]: 
  shows "(plift h p = None) \<longleftrightarrow> \<not> ptr_valid (hrs_htd h) p"
  using ptr_valid_h_t_valid
  apply (cases h)
  apply (auto simp add: plift_def TypHeap.lift_t_if  hrs_htd_def h_t_valid_def)
  done

lemma plift_None: "\<not> ptr_valid (hrs_htd h) p \<Longrightarrow> plift h p = None"
  by (simp add: plift_None_iff)

lemma ptr_valid_c_guard: "ptr_valid d p \<Longrightarrow> c_guard p"
  by (auto intro: ptr_valid_h_t_valid h_t_valid_c_guard)

lemma plift_Some_ptr_valid[plift_cond_simps]: "plift h p = Some v \<Longrightarrow> ptr_valid (hrs_htd h) p"
  using plift_Some_iff by blast

lemma plift_Some_h_t_valid[plift_cond_simps]: "plift h p = Some v \<Longrightarrow> hrs_htd h \<Turnstile>\<^sub>t p"
  using plift_Some_ptr_valid ptr_valid_h_t_valid
  by blast

lemma plift_Some_c_guard[plift_cond_simps]: "plift h p = Some v \<Longrightarrow> c_guard p"
  using plift_Some_h_t_valid h_t_valid_c_guard
  by blast


lemma ptr_valid_heap_update_conv[simp]: 
  "ptr_valid (hrs_htd ((hrs_mem_update (heap_update p v) s))) q \<longleftrightarrow> ptr_valid (hrs_htd s) q" 
  by (cases s) (auto simp add: hrs_htd_def hrs_mem_update_def)

lemma ptr_valid_heap_update_padding_conv[simp]: 
  "ptr_valid (hrs_htd ((hrs_mem_update (heap_update_padding p v bs) s))) q \<longleftrightarrow> ptr_valid (hrs_htd s) q" 
  by (cases s) (auto simp add: hrs_htd_def hrs_mem_update_def)

lemma ptr_valid_heap_update_pres: "ptr_valid (hrs_htd s) q \<Longrightarrow> 
  ptr_valid (hrs_htd ((hrs_mem_update (heap_update p v)s))) q"
  by (simp add: ptr_valid_heap_update_conv)

lemma ptr_valid_heap_update_padding_pres: "ptr_valid (hrs_htd s) q \<Longrightarrow> 
  ptr_valid (hrs_htd ((hrs_mem_update (heap_update_padding p v bs)s))) q"
  by (simp add: ptr_valid_heap_update_conv)


lemma plift_Some_h_val: 
  assumes Some: "plift h p = Some v" 
  shows "h_val (hrs_mem h) p = v"
  using plift_Some_c_guard [OF Some] plift_Some_ptr_valid [OF Some] Some h_val_clift'
  apply (simp add: plift_def)
  by (smt (verit, del_insts) c_type_class.lift_def hrs_mem_def prod.collapse typ_simps(8))


lemma ptr_valid_plift_Some_hval:
  assumes "ptr_valid (hrs_htd h) p"
  shows "plift h p = Some (h_val (hrs_mem h) p)"
  using assms plift_Some_h_val plift_Some_iff by blast

lemma the_plift_hval_conv: "ptr_valid (hrs_htd h) p \<Longrightarrow> the (plift h p) = h_val (hrs_mem h) p"
  by (metis option.collapse plift_None_iff wf_ptr_valid.plift_Some_h_val wf_ptr_valid_axioms)

lemma the_default_plift_hval_conv[the_plift_h_val_conv]: 
  "ptr_valid (hrs_htd h) p \<Longrightarrow> the_default c_type_class.zero (plift h p) = h_val (hrs_mem h) p"
  by (simp add: ptr_valid_plift_Some_hval)

lemma valid_h_val_the_plift_conv:
  assumes valid: "ptr_valid (hrs_htd h) p"
  shows "h_val (hrs_mem h) p = the (plift h p)"
  using valid plift_Some_h_val plift_iff
  by (cases "plift h p") auto

lemma valid_h_val_the_default_plift_conv:
  assumes valid: "ptr_valid (hrs_htd h) p"
  shows "h_val (hrs_mem h) p = the_default c_type_class.zero (plift h p)"
  using valid plift_Some_h_val plift_iff
  by (cases "plift h p") auto

lemma plift_Some_clift_Some: 
  assumes Some: "plift h p = Some v"  
  shows "clift h p = Some v"
  using  plift_Some_h_t_valid [OF Some] 
    h_t_valid_clift_Some_iff [of h p] 
    h_val_clift' [of h p] plift_Some_h_val [OF Some]
  by auto

lemma clift_None_plift_None:
  assumes "clift h p = None"
  shows "plift h p = None"
  using assms
  by (metis plift_None_iff plift_Some_iff wf_ptr_valid.plift_Some_clift_Some wf_ptr_valid_axioms)

lemma plift_clift_conv: 
  assumes "ptr_valid (hrs_htd h) p"
  shows "plift h p = clift h p"
  by (metis assms plift_Some_clift_Some plift_Some_iff)

lemma the_plift_hval_fun_upd_eqI [plift_eqI]:
  fixes p::"'a::mem_type ptr"
  fixes q::"'a::mem_type ptr"
  assumes "ptr_valid (hrs_htd h) p"
  shows "(the_default c_type_class.zero (plift
             (hrs_mem_update (heap_update p v) h) q)) =
         ((\<lambda>p. the_default c_type_class.zero (plift h p))(p := v)) q"
  by (smt (verit, best) assms clift_heap_update fun_upd_apply hrs_htd_mem_update 
      local.ptr_valid_h_t_valid plift_clift_conv the_default_simps(2) wf_ptr_valid.plift_None_iff wf_ptr_valid_axioms)

lemma the_plift_hval_fun_upd_padding_eqI [plift_eqI]:
  fixes p::"'a::mem_type ptr"
  fixes q::"'a::mem_type ptr"
  assumes "ptr_valid (hrs_htd h) p"
  assumes "length bs = size_of TYPE('a)"
  shows "(the_default c_type_class.zero (plift
             (hrs_mem_update (heap_update_padding p v bs) h) q)) =
         ((\<lambda>p. the_default c_type_class.zero (plift h p))(p := v)) q"
  by (smt (verit, ccfv_SIG) CTypes.mem_type_simps(2) assms(1) assms(2) fun_upd_apply h_val_def 
      h_val_heap_update_padding heap_list_update_disjoint_same heap_update_padding_def 
      hrs_htd_mem_update hrs_mem_update ptr_valid_same_type_cases the_default_plift_hval_conv 
      wf_ptr_valid.plift_None_iff wf_ptr_valid.ptr_valid_h_t_valid wf_ptr_valid_axioms)


lemma field_the_plift_hval_fun_upd_eqI [plift_eqI]:
  fixes p::"'a::mem_type ptr"
  fixes q::"'a::mem_type ptr"
  assumes "ptr_valid (hrs_htd h) p \<and> f x = v"
  shows "f (the_default c_type_class.zero (plift
             (hrs_mem_update (heap_update p x) h) q)) =
         ((\<lambda>p. f (the_default c_type_class.zero (plift h p)))(p := v)) q"
  by (simp add: assms(1) the_plift_hval_fun_upd_eqI)

lemma field_the_plift_hval_fun_upd_padding_eqI [plift_eqI]:
  fixes p::"'a::mem_type ptr"
  fixes q::"'a::mem_type ptr"
  assumes "ptr_valid (hrs_htd h) p \<and> f x = v"
  assumes "length bs = size_of TYPE('a)"
  shows "f (the_default c_type_class.zero (plift
             (hrs_mem_update (heap_update_padding p x bs) h) q)) =
         ((\<lambda>p. f (the_default c_type_class.zero (plift h p)))(p := v)) q"
  by (simp add: assms the_plift_hval_fun_upd_padding_eqI)

lemma the_plift_hval_eqI [plift_eqI]:
  fixes p::"'b::c_type ptr"
  fixes q::"'a::mem_type ptr"
  assumes eq: "ptr_valid (hrs_htd h) q \<Longrightarrow> hrs_htd h \<Turnstile>\<^sub>t q \<Longrightarrow> 
    (h_val ((heap_update p v) (hrs_mem h)) q) = (h_val (hrs_mem h) q) " 
  shows "(the_default c_type_class.zero (plift
             (hrs_mem_update (heap_update p v) h) q)) =
         (the_default c_type_class.zero (plift h q))"
proof (cases "(plift h q)")
  case None
  then show ?thesis using plift_None_iff 
    by (metis hrs_htd_mem_update)
next
  case (Some x)
  from plift_Some_ptr_valid [OF Some] 
  have ptr_valid: "ptr_valid (hrs_htd h) q".
  from plift_Some_h_t_valid [OF Some] 
  have h_t_valid: "hrs_htd h \<Turnstile>\<^sub>t q".
  from eq [OF ptr_valid h_t_valid] 
  have h_val_eq: "(h_val (heap_update p v (hrs_mem h)) q) = (h_val (hrs_mem h) q)".
  
  with ptr_valid_heap_update_conv plift_Some_iff ptr_valid eq plift_Some_h_val
  show ?thesis
    by (smt (verit) hrs_mem_update option.sel)
qed

lemma the_plift_hval_padding_eqI [plift_eqI]:
  fixes p::"'b::c_type ptr"
  fixes q::"'a::mem_type ptr"
  assumes lbs: "length bs = size_of TYPE('b)"
  assumes eq: "ptr_valid (hrs_htd h) q \<Longrightarrow> hrs_htd h \<Turnstile>\<^sub>t q \<Longrightarrow> 
    (h_val ((heap_update_padding p v bs) (hrs_mem h)) q) = (h_val (hrs_mem h) q) " 
  shows "(the_default c_type_class.zero (plift
             (hrs_mem_update (heap_update_padding p v bs) h) q)) =
         (the_default c_type_class.zero (plift h q))"
proof (cases "(plift h q)")
  case None
  then show ?thesis using plift_None_iff 
    by (metis hrs_htd_mem_update)
next
  case (Some x)
  from plift_Some_ptr_valid [OF Some] 
  have ptr_valid: "ptr_valid (hrs_htd h) q".
  from plift_Some_h_t_valid [OF Some] 
  have h_t_valid: "hrs_htd h \<Turnstile>\<^sub>t q".
  from eq [OF ptr_valid h_t_valid] 
  have h_val_eq: "(h_val (heap_update_padding p v bs (hrs_mem h)) q) = (h_val (hrs_mem h) q)".
  
  with ptr_valid_heap_update_padding_conv plift_Some_iff ptr_valid eq plift_Some_h_val
  show ?thesis
    by (smt (z3) hrs_mem_update option.sel)
qed

lemma field_the_plift_hval_eqI [plift_eqI]:
  fixes p::"'b::c_type ptr"
  fixes q::"'a::mem_type ptr"
assumes eq: "ptr_valid (hrs_htd h) q \<Longrightarrow> hrs_htd h \<Turnstile>\<^sub>t q \<Longrightarrow> 
    f (h_val ((heap_update p v) (hrs_mem h)) q) = f (h_val (hrs_mem h) q) " 
  shows "f (the_default c_type_class.zero (plift
             (hrs_mem_update (heap_update p v) h) q)) =
         f (the_default c_type_class.zero (plift h q))"
proof (cases "(plift h q)")
  case None
  then show ?thesis using plift_None_iff 
    by (metis hrs_htd_mem_update)
next
  case (Some x)
  from plift_Some_ptr_valid [OF Some] 
  have ptr_valid: "ptr_valid (hrs_htd h) q".
  from plift_Some_h_t_valid [OF Some] 
  have h_t_valid: "hrs_htd h \<Turnstile>\<^sub>t q".
  from eq [OF ptr_valid h_t_valid] 
  have h_val_eq: "f (h_val (heap_update p v (hrs_mem h)) q) = f (h_val (hrs_mem h) q)".
  
  with ptr_valid_heap_update_conv plift_Some_iff ptr_valid eq plift_Some_h_val
  show ?thesis
    by (metis hrs_mem_f the_default_simps(2))
qed

lemma field_the_plift_hval_padding_eqI [plift_eqI]:
  fixes p::"'b::c_type ptr"
  fixes q::"'a::mem_type ptr"
  assumes lbs: "length bs = size_of TYPE('b)"
  assumes eq: "ptr_valid (hrs_htd h) q \<Longrightarrow> hrs_htd h \<Turnstile>\<^sub>t q \<Longrightarrow> 
    f (h_val ((heap_update_padding p v bs) (hrs_mem h)) q) = f (h_val (hrs_mem h) q) " 
  shows "f (the_default c_type_class.zero (plift
             (hrs_mem_update (heap_update_padding p v bs) h) q)) =
         f (the_default c_type_class.zero (plift h q))"
proof (cases "(plift h q)")
  case None
  then show ?thesis using plift_None_iff 
    by (metis hrs_htd_mem_update)
next
  case (Some x)
  from plift_Some_ptr_valid [OF Some] 
  have ptr_valid: "ptr_valid (hrs_htd h) q".
  from plift_Some_h_t_valid [OF Some] 
  have h_t_valid: "hrs_htd h \<Turnstile>\<^sub>t q".
  from eq [OF ptr_valid h_t_valid] 
  have h_val_eq: "f (h_val (heap_update_padding p v bs (hrs_mem h)) q) = f (h_val (hrs_mem h) q)".
  
  with ptr_valid_heap_update_padding_conv plift_Some_iff ptr_valid eq plift_Some_h_val
  show ?thesis
    by (metis hrs_mem_f the_default_simps(2))
qed

lemma plift_heap_update [plift_heap_update]:
  "\<lbrakk> ptr_valid (hrs_htd h) p \<rbrakk> \<Longrightarrow>
      plift (hrs_mem_update (heap_update p v) h)
          = (plift h)(p := Some (v::'a::mem_type))"
  using plift_Some_clift_Some ptr_valid_h_t_valid
  by (metis (no_types, opaque_lifting) h_t_valid_guard_subst hrs_htd_def hrs_htd_mem_update 
      hrs_mem_def hrs_mem_update lift_t_heap_update plift_def prod.collapse)

lemma plift_heap_update_padding [plift_heap_update]:
  "\<lbrakk> ptr_valid (hrs_htd h) p; length bs = size_of TYPE('a) \<rbrakk> \<Longrightarrow>
      plift (hrs_mem_update (heap_update_padding p v bs) h)
          = (plift h)(p := Some (v::'a::mem_type))"
  apply (rule ext)
  apply (clarsimp simp add: fun_upd_def, intro conjI)
  subgoal by (simp add: h_val_heap_update_padding hrs_mem_update wf_ptr_valid.ptr_valid_plift_Some_hval wf_ptr_valid_axioms)
  using plift_Some_clift_Some ptr_valid_h_t_valid
  by (smt (verit, best) fun_upd_apply hrs_htd_mem_update the_default_plift_hval_conv 
      the_plift_hval_fun_upd_padding_eqI wf_ptr_valid.plift_None_iff wf_ptr_valid.ptr_valid_plift_Some_hval wf_ptr_valid_axioms)


lemma h_val_field_plift [h_val_field_plift]:
  fixes pa :: "'a :: mem_type ptr"
  assumes cl: "plift hp pa = Some v"
  and     fl: "field_ti TYPE('a) f = Some t"
  and     eu: "export_uinfo t = typ_uinfo_t TYPE('b :: mem_type)"
  shows   "h_val (hrs_mem hp) (Ptr &(pa\<rightarrow>f) :: 'b :: mem_type ptr) = from_bytes (access_ti\<^sub>0 t v)"
  using cl fl eu
  using h_val_field_clift' plift_Some_clift_Some by blast
 
lemma plift_disjoint_region:
  fixes p:: "'a :: mem_type ptr"
  fixes q:: "'b :: mem_type ptr"
  assumes disj: "ptr_span q \<inter> ptr_span p = {}"
  shows "plift (hrs_mem_update (heap_update q v) m) p = plift m p"
  using disj
  by (metis Int_commute h_val_update_regions_disjoint hrs_htd_mem_update 
      hrs_mem_heap_update option.collapse plift_None_iff the_plift_hval_conv)

lemma plift_disjoint_region_padding:
  fixes p:: "'a :: mem_type ptr"
  fixes q:: "'b :: mem_type ptr"
  assumes disj: "ptr_span q \<inter> ptr_span p = {}"
  assumes lbs: "length bs = size_of TYPE('b)"
  shows "plift (hrs_mem_update (heap_update_padding q v bs) m) p = plift m p"
  using disj lbs
  by (metis (no_types, lifting) CTypes.mem_type_simps(2) disj h_val_def 
      heap_list_update_disjoint_same heap_update_padding_def hrs_htd_mem_update 
      hrs_mem_update wf_ptr_valid.plift_None_iff wf_ptr_valid.ptr_valid_plift_Some_hval wf_ptr_valid_axioms)

lemma map_option_the_plift_h_val_conv: 
  "f (the (map_option g (plift h p))) = f (the (plift h p)) \<longleftrightarrow> (ptr_valid (hrs_htd h) p \<longrightarrow> f (g (h_val (hrs_mem h) p)) = f (h_val (hrs_mem h) p))"
  apply (subst map_option_the_conv)
  apply standard
  using ptr_valid_plift_Some_hval apply blast
  using plift_Some_h_val plift_Some_ptr_valid by blast

lemma invalid_plift_heap_update_skip:
  assumes invalid_p: "\<not> ptr_valid (hrs_htd h) p"
  assumes typed_p: "hrs_htd h \<Turnstile>\<^sub>t p"
shows "plift (hrs_mem_update (heap_update p v) h) q = plift h q"
proof (cases "p = q")
  case True
  with invalid_p have invalid_q: "\<not> ptr_valid (hrs_htd h) q" by simp
  from invalid_q have "plift h q = None" 
    by (simp add: plift_None)
  moreover
  from invalid_q have "plift (hrs_mem_update (heap_update p v) h) q = None"
    by (simp add: plift_None)
  ultimately show ?thesis by simp
next
  case False
  note neq_p_q = this
  show ?thesis
  proof (cases "ptr_valid (hrs_htd h) q")
    case True     
    from ptr_valid_h_t_valid [OF True]
    have "hrs_htd h \<Turnstile>\<^sub>t q" .
    from ptr_valid_same_type_cases [OF typed_p this] neq_p_q
    have "ptr_span p \<inter> ptr_span q = {}" by blast
    then show ?thesis
      by (simp add: plift_disjoint_region)
  next
    case False
    from False have "plift h q = None" 
      by (simp add: plift_None)
    moreover
    from False have "plift (hrs_mem_update (heap_update p v) h) q = None"
      by (simp add: plift_None)
    ultimately show ?thesis by simp
  qed
qed

lemma invalid_plift_heap_update_padding_skip:
  assumes invalid_p: "\<not> ptr_valid (hrs_htd h) p"
  assumes typed_p: "hrs_htd h \<Turnstile>\<^sub>t p"
  assumes lbs: "length bs = size_of TYPE('a)"
shows "plift (hrs_mem_update (heap_update_padding p v bs) h) q = plift h q"
proof (cases "p = q")
  case True
  with invalid_p have invalid_q: "\<not> ptr_valid (hrs_htd h) q" by simp
  from invalid_q have "plift h q = None" 
    by (simp add: plift_None)
  moreover
  from invalid_q have "plift (hrs_mem_update (heap_update_padding p v bs) h) q = None"
    by (simp add: plift_None)
  ultimately show ?thesis by simp
next
  case False
  note neq_p_q = this
  show ?thesis
  proof (cases "ptr_valid (hrs_htd h) q")
    case True     
    from ptr_valid_h_t_valid [OF True]
    have "hrs_htd h \<Turnstile>\<^sub>t q" .
    from ptr_valid_same_type_cases [OF typed_p this] neq_p_q
    have "ptr_span p \<inter> ptr_span q = {}" by blast
    then show ?thesis
      using lbs
      by (simp add: plift_disjoint_region_padding)
  next
    case False
    from False have "plift h q = None" 
      by (simp add: plift_None)
    moreover
    from False have "plift (hrs_mem_update (heap_update_padding p v bs) h) q = None"
      by (simp add: plift_None)
    ultimately show ?thesis by simp
  qed
qed


end

global_interpretation simple_lift: wf_ptr_valid root_ptr_valid rewrites "simple_lift.plift = simple_lift"
   apply (unfold_locales) 
    apply (simp add: root_ptr_valid_h_t_valid)
  apply (rule ext, rule ext)
  by (metis root_ptr_valid_h_t_valid hrs_mem_def lift_t_if prod.collapse simple_lift_def 
      wf_ptr_valid.intro wf_ptr_valid.plift_None_iff wf_ptr_valid.plift_def)

named_theorems ptr_valid_stack_alloc and ptr_valid_stack_release and plift_stack_alloc and plift_stack_release

locale ptr_valid_stack_alloc = wf_ptr_valid +
  assumes alloc[ptr_valid_stack_alloc]:
    "\<And>d d' p q. (p, d') \<in> stack_alloc \<S> TYPE('a::mem_type) d \<Longrightarrow> 
                ptr_valid d' q \<longleftrightarrow> (q = p) \<or> ptr_valid d q"
begin

lemma plift_stack_alloc_update:
  assumes alloc: "(p, d) \<in> stack_alloc \<S> TYPE('a::mem_type) (hrs_htd m)"
  shows "(plift (hrs_htd_update (\<lambda>_. d) m))(p\<mapsto>x) = (\<lambda>q. if p = q then Some x else plift m q)"
  apply (rule ext)
  apply clarsimp
  using ptr_valid_stack_alloc [OF alloc]
  by (metis hrs_htd_update hrs_mem_htd_update option.collapse plift_None_iff 
      wf_ptr_valid.valid_h_val_the_plift_conv wf_ptr_valid_axioms)


lemma plift_stack_alloc_sim[plift_stack_alloc]:
  assumes alloc: "(p, d) \<in> stack_alloc \<S> TYPE('a::mem_type) (hrs_htd m)"
  shows "(plift (hrs_mem_update (heap_update p x) (hrs_htd_update (\<lambda>_. d) m))) = 
         (\<lambda>q. if p = q then Some x else plift m q)"
  using plift_stack_alloc_update [OF alloc]
  by (simp add: hrs_htd_update plift_heap_update ptr_valid_stack_alloc [OF alloc])

end

locale ptr_valid_stack_release = wf_ptr_valid +
  assumes release[ptr_valid_stack_release]: 
    "\<And>d p q. root_ptr_valid d p \<Longrightarrow> typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE(stack_byte) \<Longrightarrow> 
      ptr_valid (stack_release p d) q \<longleftrightarrow> ((q \<noteq> p) \<and> ptr_valid d q)"
begin

lemma plift_stack_release[plift_stack_release]:
  assumes root_valid: "root_ptr_valid (hrs_htd m) (p::'a::mem_type ptr)"
  assumes p: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  shows "plift (hrs_htd_update (stack_release p) m) q =
           (if p = q then None else plift m q)"
 using ptr_valid_stack_release [OF root_valid p]
  by (metis (no_types, lifting) hrs_htd_update hrs_mem_htd_update option.collapse 
      valid_h_val_the_plift_conv wf_ptr_valid.plift_None_iff wf_ptr_valid_axioms)
end

locale ptr_valid_stack = ptr_valid_stack_alloc + ptr_valid_stack_release

global_interpretation simple_lift: ptr_valid_stack root_ptr_valid 
   apply (unfold_locales) 
    apply (smt (verit) disjoint_iff ptr_force_type_same_cleared_region root_ptr_valid_def 
      root_ptr_valid_h_t_valid s_footprintD s_footprintI2 size_of_def stack_alloc_cases 
      stack_alloc_preserves_root_ptr_valid stack_release_other 
      stack_release_stack_alloc_inverse typ_uinfo_size valid_root_footprint_def)
   apply (smt (verit) disjoint_iff in_ptr_span_itself intvlI intvl_inter root_ptr_valid_def 
      root_ptr_valid_h_t_valid root_ptr_valid_neq_disjoint root_ptr_valid_same_type_cases 
      simple_heap_diff_types_impl_diff_ptrs size_of_def stack_release_other 
      stack_release_root_ptr_valid_footprint typ_uinfo_size valid_root_footprint_def)
  done


lemma valid_root_footprint_domain:
  assumes "valid_root_footprint d a t"
  assumes "\<And>x. x \<in> {a ..+ size_td t} \<Longrightarrow> d' x = d x"
  shows "valid_root_footprint d' a t"
  by (metis assms(1) assms(2) intvlI valid_root_footprint_def)

lemma valid_root_footprint_cases:
  assumes valid_a: "valid_root_footprint d a T"
  assumes root_p: "valid_root_footprint d b S"
  shows "(a = b \<and> S = T) \<or> {b ..+ size_td S} \<inter> {a ..+ size_td T} = {}"
proof (cases "{b ..+ size_td S} \<inter> {a ..+ size_td T} = {}")
  case True
  thus ?thesis by simp
next
  case False
  note overlap = this

  show ?thesis
  proof (cases "S = T")
    case True
    from valid_root_footprint_neq_disjoint [OF valid_a root_p] overlap 
    have "a = b"
      by (metis inf_commute size_of_tag)
    then show ?thesis by (simp add: True)
  next
    case False
    with valid_root_footprint_type_neq_disjoint [OF root_p valid_a False] overlap
    have False
      by (simp add: size_of_def)
    thus ?thesis
      by simp
  qed
qed

lemma valid_root_footprint_domain_cases:
  assumes valid_a: "valid_root_footprint d' a t"
  assumes other_eq: "\<And>x. x \<notin> {a ..+ size_td t} \<Longrightarrow> d' x = d x"
  assumes root_p: "valid_root_footprint d' b s"
  shows "
     (a = b \<and> s = t \<or> 
      valid_root_footprint d b s)"
proof (cases "{b ..+ size_td s} \<inter> {a ..+ size_td t} = {}")
  case True
  with other_eq have "\<And>x. x \<in> {b ..+ size_td s} \<Longrightarrow>  d' x = d x" by auto
  with valid_root_footprint_domain [OF root_p ]
  have "valid_root_footprint d b s"
    by auto
  thus ?thesis by blast
next
  case False
  note overlap = this

  show ?thesis
  proof (cases "s = t")
    case True
    from valid_root_footprint_neq_disjoint [OF valid_a root_p] overlap 
    have "a = b"
      by (metis inf_commute size_of_tag)
    then show ?thesis by (simp add: True)
  next
    case False
    with valid_root_footprint_type_neq_disjoint [OF root_p valid_a False] overlap
    have False
      by (simp add: size_of_def)
    thus ?thesis
      by simp
  qed
qed

lemma h_t_valid_ptr_span_preservation:
fixes p::"'a::mem_type ptr"
assumes valid: "d \<Turnstile>\<^sub>t p"
assumes eq: "\<And>a. a \<in> ptr_span p \<Longrightarrow> d' a = d a"
shows "d' \<Turnstile>\<^sub>t p"
  using valid eq
  by (auto simp add: h_t_valid_def valid_footprint_def Let_def intvlI size_of_def)

lemma 
  fixes p::"'a::mem_type ptr"
  fixes q::"'a::mem_type ptr"
  assumes "root_ptr_valid d p" 
  assumes "d \<Turnstile>\<^sub>t q"
  shows "p = q \<or> ptr_span p \<inter> ptr_span q = {}"
  by (meson assms(1) assms(2) root_ptr_valid_same_type_cases)

lemma stack_alloc_typing_other:
  fixes q::"'b::mem_type ptr"
  assumes stack_alloc: "(p, d') \<in> stack_alloc \<S> (TYPE('a::mem_type)) d"
  assumes no_stack: "typ_uinfo_t (TYPE('b)) \<noteq> typ_uinfo_t (TYPE(stack_byte))"
  assumes other: "\<not> TYPE('b) \<le>\<^sub>\<tau> (TYPE('a))"
  shows "d' \<Turnstile>\<^sub>t q = d \<Turnstile>\<^sub>t q"
proof
  assume valid_d'_q: "d' \<Turnstile>\<^sub>t q" 
  show "d \<Turnstile>\<^sub>t q"
  proof (cases "d \<Turnstile>\<^sub>t q")
    case True
    then show ?thesis by simp
  next
    case False
    have  invalid_d_q: "\<not> d \<Turnstile>\<^sub>t q" using False .

    from stack_alloc obtain
      d': "d' = ptr_force_type p d" and
      "typ_uinfo_t (TYPE('a)) \<noteq> typ_uinfo_t (TYPE(stack_byte))" and
      "ptr_span p \<subseteq> \<S>" and
      no_stack_d: "\<forall>a \<in> ptr_span p. root_ptr_valid d (PTR (stack_byte) a)" and
      "ptr_aligned p" and "c_guard p" and root_p: "root_ptr_valid d' p"
      by (cases rule: stack_alloc_cases) 
    from valid_d'_q obtain
      footprint_d'_q: "valid_footprint d' (ptr_val q) (typ_uinfo_t TYPE('b))" and
      c_guard_q: "c_guard q"
      by (auto simp add: h_t_valid_def)
    with invalid_d_q 
    have no_footprint_d_q: "\<not> (valid_footprint d (ptr_val q) (typ_uinfo_t TYPE('b)))"
      by (simp add: d' h_t_valid_def)
    from root_p valid_d'_q other have "ptr_span q \<inter> ptr_span p = {}" 
      by (meson disj_inter_swap root_ptr_valid_not_subtype_disjoint)
    with  no_footprint_d_q ptr_force_type_valid_footprint_disjoint2 [OF footprint_d'_q [simplified d']]
    have False
      by (simp add: size_of_tag)
    then show ?thesis by simp
  qed
  next
  assume "d \<Turnstile>\<^sub>t q" from stack_alloc_preserves_typing [OF stack_alloc no_stack this]
  show "d' \<Turnstile>\<^sub>t q" .
qed

lemma "TYPE('b::c_type) \<le>\<^sub>\<tau> (TYPE('a::c_type)) \<Longrightarrow> typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE('a) 
\<Longrightarrow> \<not>TYPE('a) \<le>\<^sub>\<tau> (TYPE('b))"

  using typ_uinfo_eq_sub_typ_conv(3) by blast

named_theorems stack_alloc_ptr_valid_parent and stack_release_ptr_valid_parent


lemma stack_alloc_root_ptr_valid_other:
  fixes q::"'b::mem_type ptr"
  assumes stack_alloc: "(p, d') \<in> stack_alloc \<S> (TYPE('a::mem_type)) d"
  assumes neq: "typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE('a)"
  assumes sub: "TYPE('a) \<le>\<^sub>\<tau> (TYPE('b))"
  shows "root_ptr_valid d' (q::'b::mem_type ptr) = root_ptr_valid d q"
proof 
  assume valid_d': "root_ptr_valid d' q" 
  show "root_ptr_valid d q"
      using neq stack_alloc stack_alloc_root_ptr_valid_new_cases valid_d' by blast
next
  assume "root_ptr_valid d q"  
  then show "root_ptr_valid d' q"
    by (smt (verit, best) sub stack_alloc stack_alloc_cases stack_release_root_ptr_valid_cases 
        stack_release_stack_alloc_inverse sub_typ_def sub_typ_stack_byte)
qed

lemma stack_release_root_ptr_valid_other:
  fixes p::"'a::mem_type ptr"
  fixes q::"'b::mem_type ptr"
  assumes root: "root_ptr_valid d p"
  assumes non_stack: "typ_uinfo_t (TYPE('a)) \<noteq> typ_uinfo_t (TYPE(stack_byte))"
  assumes neq: "typ_uinfo_t TYPE('b::mem_type) \<noteq> typ_uinfo_t TYPE('a)"
  assumes sub: "TYPE('a) \<le>\<^sub>\<tau> (TYPE('b))"
  shows "root_ptr_valid (stack_release p d) (q::'b::mem_type ptr) = root_ptr_valid d q"
  by (metis neq non_stack root root_ptr_valid_type_neq_disjoint 
      stack_release_root_ptr_valid1 stack_release_root_ptr_valid2 sub sub_typ_def sub_typ_stack_byte)

lemma bex_impl_forall_conv: "((\<exists>x\<in>A. P x) \<longrightarrow> Q) \<longleftrightarrow> (\<forall>x. x \<in> A \<longrightarrow> P x \<longrightarrow> Q)"
  by auto


end
