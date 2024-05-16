(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

chapter \<open>More Building Blocks for our C-Language Model\<close>

theory CLanguage
  imports 
    CProof
    Lens
begin

section \<open>addr bounds\<close>

lemma addr_card_eq: "addr_card = 2^LENGTH(addr_bitsize)"
  by (simp add: addr_card_def card_word)

lemma size_of_bnd: "size_of TYPE('a::mem_type) < 2^LENGTH(addr_bitsize)"
  by (rule less_le_trans[OF max_size]) (simp add: addr_card_eq)

lemma size_of_mem_type[simp]: "size_of TYPE('c::mem_type) \<noteq> 0"
  by simp

lemma addr_card_len_of_conv: "addr_card =  2 ^ len_of TYPE(addr_bitsize)"
  by (simp add: addr_card)

lemma intvl_split:
  "\<lbrakk> n \<ge> a \<rbrakk> \<Longrightarrow> { p :: ('a :: len) word ..+ n } = { p ..+ a } \<union> { p + of_nat a ..+ (n - a)}"
(*    supply unsigned_of_nat [simp del] *)
  apply (rule set_eqI, rule iffI)
   apply (clarsimp simp: intvl_def not_less)
  subgoal for k 
    apply (rule exI[where x=k])
    apply clarsimp
    apply (rule classical)
    apply (drule_tac x="k - a" in spec)
    apply (clarsimp simp: not_less)
    apply (metis diff_less_mono not_less)
    done
  subgoal for x
    apply (clarsimp simp: intvl_def not_less)
    apply (rule exI[where x="unat (x - p)"])
    apply clarsimp
    apply (erule disjE)
     apply clarsimp
     apply (metis le_unat_uoi less_or_eq_imp_le not_less order_trans)
    apply clarsimp
    apply (metis le_def le_eq_less_or_eq le_unat_uoi less_diff_conv
        add.commute of_nat_add)
    done
  done

section "More Heap Typing"


primrec
  htd_upd :: "addr \<Rightarrow> typ_slice list \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc"
where
  "htd_upd p [] d = d"
| "htd_upd p (x#xs) d = htd_upd (p+1) xs (d(p := (True, x)))"

definition (in c_type) ptr_force_type :: "'a ptr \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc" where
  "ptr_force_type p \<equiv> htd_upd (ptr_val p) (typ_slices TYPE('a))"

definition ptr_force_types :: "'a::c_type ptr list \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc" where
  "ptr_force_types = fold ptr_force_type"


definition ptr_force_free :: "addr \<Rightarrow> nat \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc" where
  "ptr_force_free p b = ptr_force_types (map (\<lambda>n. PTR(8 word) p +\<^sub>p n) (map of_nat [0..<2^b]))"

definition ptr_u :: "'a::c_type ptr \<Rightarrow> (addr \<times> typ_uinfo)" where
  "ptr_u p = (ptr_val p, typ_uinfo_t TYPE('a))"

abbreviation "ptr_span_u \<equiv> (\<lambda>(a, t). {a ..+ size_td t})"

definition typ_slices_u :: "typ_uinfo \<Rightarrow> typ_slice list" where
  "typ_slices_u t = map (\<lambda>n. list_map (typ_slice_t t n)) [0..<size_td t]"

definition ptr_force_type_u :: "typ_uinfo \<Rightarrow> addr \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc" where
  "ptr_force_type_u t a \<equiv> htd_upd a (typ_slices_u t)"

lemma heap_update_list_id: "heap_update_list x [] = (\<lambda>x. x)"
  by auto

lemma to_bytes_word8:
  "to_bytes (v :: word8) xs = [v]"
  by (simp add: to_bytes_def typ_info_word word_rsplit_same)

lemma heap_update_heap_update_list:
   "\<lbrakk> ptr_val p = q + (of_nat (length l)); Suc (length l) < addr_card \<rbrakk> \<Longrightarrow>
      heap_update (p :: word8 ptr) v (heap_update_list q l s) = (heap_update_list q (l @ [v]) s)"
  by (metis to_bytes_word8 heap_update_def heap_update_list_concat_fold)

lemma htd_upd_empty[simp]: "htd_upd p [] = id"
  by (simp add: fun_eq_iff)

lemma htd_upd_append:
  "htd_upd p (xs @ ys) = htd_upd (p + of_nat (length xs)) ys \<circ> htd_upd p xs"
  by (induction xs arbitrary: p) (simp_all add: fun_eq_iff ac_simps)

lemma htd_upd_singleton[simp]: "htd_upd p [x] = upd_fun p (\<lambda>h. (True, x))"
  by (simp add: fun_eq_iff upd_fun_def)

lemma intvl_Suc_eq: "{p ..+ Suc n} = insert p {p + 1 ..+ n}"
  using intvl_split[of 1 "Suc n" p] by (auto simp add: intvl_def)

lemma htd_upd_disj: "p \<notin> {p' ..+ length v} \<Longrightarrow> htd_upd p' v h p = h p"
  by (induction v arbitrary: p' h)
     (auto simp add: intvl_Suc_eq fun_upd_other simp del: fun_upd_apply)

lemma htd_upd_head:
  "xs \<noteq> [] \<Longrightarrow> length xs \<le> addr_card \<Longrightarrow> htd_upd p xs s p = (True, hd xs)"
  using intvl_Suc_nmem''[of "length xs" p] htd_upd_disj[of p "p + 1" "tl xs" _]
  by (cases xs) (simp_all add: addr_card_eq del: intvl_Suc_nmem')

lemma htd_upd_at:
  "i < length xs \<Longrightarrow> length xs \<le> addr_card \<Longrightarrow> htd_upd p xs s (p + of_nat i) = (True, xs ! i)"
proof (induction i arbitrary: p xs s)
  case 0 with htd_upd_head[of xs p s] show ?case by (simp add: hd_conv_nth)
next
  case (Suc n)
  from Suc.prems show ?case by (cases xs) (simp_all add: Suc.IH flip: add.assoc)
qed

lemma ptr_force_type_disj:
  "p \<notin> ptr_span (p' :: 'a::mem_type ptr) \<Longrightarrow> ptr_force_type p' h p = h p"
  unfolding ptr_force_type_def
  by (intro htd_upd_disj) simp_all

lemma ptr_force_types_disj:
  fixes xs :: "'a::mem_type ptr list"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> i \<notin> ptr_span x"
  shows "ptr_force_types xs h i = h i"
  by (use assms in \<open>induction xs rule: rev_induct\<close>)
     (auto simp: ptr_force_types_def ptr_force_type_disj)

subsection \<open>Heap type tag and valid simple footprint\<close>
(*
 * Each address in the heap can contain one of three things:
 *
 *   - A type tag, which inidicates that this address is the first
 *     byte of an object;
 *
 *   - A footprint, which indicates that this address is a latter byte
 *     of an object;
 *
 *   - Nothing, which indicates that this address does not fall inside
 *     an object.
 *)
datatype heap_typ_contents =
    HeapType typ_uinfo
  | HeapFootprint
  | HeapEmpty

(*
 * Given a Tuch-style heap representation (where each memory location
 * contains a set of different types, representing nested field types)
 * calculate a single top-level type of the heap.
 *
 * We just want to commit to a single type for this heap location,
 * and nothing more.
 *)
definition
  heap_type_tag :: "heap_typ_desc \<Rightarrow> addr \<Rightarrow> heap_typ_contents"
where
  "heap_type_tag d a \<equiv>
     (if fst (d a) = False \<or> (\<forall>x. (snd (d a)) x = None) \<or> (\<forall>x. (snd (d a)) x \<noteq> None) then
       HeapEmpty
     else
       case (snd (d a)) (GREATEST x. snd (d a) x \<noteq> None) of
         Some (_, False) \<Rightarrow> HeapFootprint
       | Some (x, True) \<Rightarrow> HeapType x
       | None \<Rightarrow> HeapEmpty)"



(*
 * Determine if the heap has a valid footprint for the given type at
 * the given address.
 *
 * A valid footprint means that the user has committed that the given
 * memory location will only be used for the given type.
 *
 * A "simple" footprint differs from the Tuch-style because we only
 * commit to a single type, and have no support for accessing nested
 * structures.
 *)
definition
  valid_simple_footprint :: "heap_typ_desc \<Rightarrow> addr \<Rightarrow> typ_uinfo \<Rightarrow> bool"
where
  "valid_simple_footprint d x t \<equiv>
    heap_type_tag d x = HeapType t \<and>
      (\<forall>y. y \<in> {x + 1..+  (size_td t)- Suc 0} \<longrightarrow> heap_type_tag d y = HeapFootprint)"

lemma valid_simple_footprint_size_td:
  assumes valid: "valid_simple_footprint d x t" 
  shows "size_td t \<le> addr_card"
proof (cases "size_td t \<le> addr_card")
  case True
  then show ?thesis by simp
next
  case False
  from valid have "heap_type_tag d x = HeapType t"
    by (simp add: valid_simple_footprint_def)
  moreover
  from False have "x \<in> {x + 1..+  (size_td t)- Suc 0}"
    apply (clarsimp simp add: intvl_def)
    apply (rule exI [where x = "addr_card - Suc 0"])
    by (metis (mono_tags, opaque_lifting) One_nat_def Suc_pred' diff_less_mono diff_zero 
        neq0_conv not_less not_less_eq_eq of_nat_1 of_nat_Suc of_nat_addr_card unatSuc 
        unat_minus_abs zero_diff zero_neq_one)
  with valid have "heap_type_tag d x = HeapFootprint" by (auto simp add: valid_simple_footprint_def)
  ultimately have False by simp
  thus ?thesis ..
qed

lemma valid_simple_footprintI:
  "\<lbrakk> heap_type_tag d x = HeapType t; \<And>y. y \<in> {x + 1..+(size_td t) - Suc 0} \<Longrightarrow> heap_type_tag d y = HeapFootprint \<rbrakk>
      \<Longrightarrow> valid_simple_footprint d x t"
  by (clarsimp simp: valid_simple_footprint_def)

lemma valid_simple_footprintD:
  "valid_simple_footprint d x t \<Longrightarrow> heap_type_tag d x = HeapType t"
  by (simp add: valid_simple_footprint_def)

lemma valid_simple_footprintD2:
  "\<lbrakk> valid_simple_footprint d x t; y \<in> {x + 1..+(size_td t) - Suc 0} \<rbrakk> \<Longrightarrow> heap_type_tag d y = HeapFootprint"
  by (simp add: valid_simple_footprint_def)

lemma typ_slices_not_empty:
    "typ_slices (x::('a::{mem_type} itself)) \<noteq> []"
  apply (clarsimp simp: typ_slices_def)
  done

lemma last_typ_slice_t:
    "(last (typ_slice_t t 0)) = (t, True)"
  apply (cases t)
  apply clarsimp
  done

lemma last_typ_slice_t_non_zero:
    "k \<noteq> 0 \<Longrightarrow> (last (typ_slice_t t k)) = (t, False)"
  apply (cases t)
  apply clarsimp
  done

lemma if_eqI:
 "\<lbrakk> a \<Longrightarrow> x = z; \<not> a \<Longrightarrow> y = z \<rbrakk> \<Longrightarrow> (if a then x else y) = z"
  by simp

lemma heap_type_tag_ptr_retyp:
    "snd (s (ptr_val t)) = Map.empty \<Longrightarrow>
        heap_type_tag (ptr_retyp (t :: 'a::mem_type ptr) s) (ptr_val t) = HeapType (typ_uinfo_t TYPE('a))"
  apply (unfold ptr_retyp_def heap_type_tag_def)
  apply (subst htd_update_list_index, fastforce, fastforce)+
  apply (rule if_eqI)
   apply clarsimp
   apply (erule disjE)
    apply (erule_tac x=0 in allE)
    apply clarsimp
   apply (erule_tac x="length (typ_slice_t (typ_uinfo_t TYPE('a)) 0)" in allE)
   apply (clarsimp simp: list_map_eq)
  apply (clarsimp simp: list_map_eq last_conv_nth [simplified, symmetric] last_typ_slice_t
            split: option.splits if_split_asm prod.splits)
  done

lemma not_snd_last_typ_slice_t:
    "k \<noteq> 0 \<Longrightarrow> \<not> snd (last (typ_slice_t z k))"
  by (cases z, clarsimp)

lemma heap_type_tag_ptr_retyp_rest:
    "\<lbrakk> snd (s (ptr_val t + k)) = Map.empty; 0 < k; unat k < size_td (typ_uinfo_t TYPE('a)) \<rbrakk> \<Longrightarrow>
        heap_type_tag (ptr_retyp (t :: 'a::mem_type ptr) s) (ptr_val t + k) = HeapFootprint"
  apply (unfold ptr_retyp_def heap_type_tag_def)
  apply (subst htd_update_list_index, simp, clarsimp,
      metis intvlI size_of_def word_unat.Rep_inverse)+
  apply (rule if_eqI)
   apply clarsimp
   apply (erule disjE)
    apply (erule_tac x=0 in allE)
    apply (clarsimp simp: size_of_def)
   apply (erule_tac x="length (typ_slice_t (typ_uinfo_t TYPE('a)) (unat k))" in allE)
   apply (clarsimp simp: size_of_def list_map_eq)
  apply (clarsimp simp: list_map_eq last_conv_nth [simplified, symmetric] size_of_def
      split: option.splits if_split_asm prod.splits bool.splits)
   apply (metis surj_pair)
  apply (subst (asm) (2) surjective_pairing)
  apply (subst (asm) not_snd_last_typ_slice_t)
   apply clarsimp
   apply unat_arith
  apply simp
  done

lemma typ_slices_addr_card [simp]:
    "length (typ_slices (x::('a::{mem_type} itself))) < addr_card"
  apply (clarsimp simp: typ_slices_def)
  done

lemma unat_less_impl_less:
    "unat a < unat b \<Longrightarrow> a < b"
  by unat_arith

lemma valid_simple_footprint_ptr_retyp:
    "\<lbrakk> \<forall>k < size_td (typ_uinfo_t TYPE('a)). snd (s (ptr_val t + of_nat k)) = Map.empty;
        1 \<le> size_td (typ_uinfo_t TYPE('a));
        size_td (typ_uinfo_t TYPE('a)) < addr_card \<rbrakk>
        \<Longrightarrow> valid_simple_footprint (ptr_retyp (t :: 'a::mem_type ptr) s) (ptr_val t) (typ_uinfo_t TYPE('a))"
  apply (clarsimp simp: valid_simple_footprint_def)
  apply (rule conjI)
   apply (subst heap_type_tag_ptr_retyp)
    apply (erule allE [where x="0"])
    apply clarsimp
   apply clarsimp
  apply (clarsimp simp: intvl_def)
  subgoal for k
    apply (erule_tac x="k + 1" in allE)
    apply (erule impE)
     apply (metis One_nat_def less_diff_conv)
    apply (subst add.assoc, subst heap_type_tag_ptr_retyp_rest)
       apply clarsimp
      apply (cases "1 + of_nat k = (0 :: addr)")
       apply (metis add.left_neutral intvlI intvl_Suc_nmem size_of_def)
      apply unat_arith
     apply clarsimp
     apply (metis lt_size_of_unat_simps size_of_def Suc_eq_plus1 One_nat_def less_diff_conv of_nat_Suc)
    apply simp
    done
  done

lemma heap_type_tag_cong: "s p = s' p \<Longrightarrow> heap_type_tag s p = heap_type_tag s' p"
  by (simp add: heap_type_tag_def cong: if_cong)

lemma heap_type_tag:
  assumes eq: "h p = (f, list_map l)"
  shows "heap_type_tag h p =
    (if \<not> f \<or> l = [] then HeapEmpty else
      case last l of (x, b) \<Rightarrow> if b then HeapType x else HeapFootprint)"
  unfolding heap_type_tag_def eq
  by (auto simp add: list_map_def)
     (auto simp: split_beta' last_conv_nth list_map_eq simp flip: list_map_def)

lemma valid_simple_footprint_cong_state:
  assumes t: "wf_size_desc t"
  assumes eq: "\<And>p'. p' \<in> {p ..+size_td t} \<Longrightarrow> s p' = s' p'"
  shows "valid_simple_footprint s p t \<longleftrightarrow> valid_simple_footprint s' p t"
  unfolding valid_simple_footprint_def
  using eq wf_size_desc_gt(1)[OF t]
  using intvl_split[of 1 "size_td t" p]
  by (intro arg_cong2[where f="(\<and>)"] all_cong arg_cong[where f="\<lambda>x. x = _"] heap_type_tag_cong)
     (auto simp: intvl_def)

lemma heap_type_tag_ptr_force_type_HeapType:
  fixes x :: "'a::mem_type ptr"
  shows "heap_type_tag (ptr_force_type x s) (ptr_val x) = HeapType (typ_uinfo_t TYPE('a))"
  by (subst heap_type_tag)
     (auto simp: ptr_force_type_def htd_upd_head typ_slices_not_empty max_size[THEN less_imp_le]
                 hd_conv_nth last_typ_slice_t)

lemma heap_type_tag_ptr_force_type_HeapFootprint:
  fixes p :: "'a::mem_type ptr"
  shows "p' \<in> {ptr_val p + 1 ..+ size_of TYPE('a) - Suc 0} \<Longrightarrow>
    heap_type_tag (ptr_force_type p s) p' = HeapFootprint"
  unfolding intvl_def
  apply (clarsimp simp: less_diff_conv add.assoc ptr_force_type_def simp flip: of_nat_Suc)
  subgoal premises prems for k
    using prems(1)
    apply (subst heap_type_tag)
    apply (subst htd_upd_at)
    apply (simp_all add: max_size[THEN less_imp_le])
    apply (simp add: last_typ_slice_t split_beta' not_snd_last_typ_slice_t)
    done
  done

lemma valid_simple_footprint_ptr_force_type_iff:
  fixes p :: "'a::mem_type ptr"
  assumes t: "wf_size_desc t"
  shows "valid_simple_footprint (ptr_force_type p s) a t \<longleftrightarrow>
    (valid_simple_footprint s a t \<and> disjnt {a ..+ size_td t} (ptr_span p)) \<or>
    (t = typ_uinfo_t TYPE('a) \<and> p = Ptr a)"
proof cases
  assume disjnt: "disjnt {a ..+ size_td t} (ptr_span p)"
  moreover have "p \<noteq> Ptr a"
    using disjnt[unfolded disjnt_iff, THEN spec, of a] t[THEN wf_size_desc_gt(1)]
    by (cases p) (auto simp: intvl_self)
  moreover have "valid_simple_footprint (ptr_force_type p s) a t = valid_simple_footprint s a t"
    using t disjnt
    by (intro valid_simple_footprint_cong_state ptr_force_type_disj) (simp_all add: disjnt_iff)
  ultimately show ?thesis
    by simp
next
  assume ndisjnt: "\<not> disjnt {a ..+ size_td t} (ptr_span p)"
  from intvl_inter[OF this[unfolded disjnt_def]]
  consider "a = ptr_val p"
    | "a \<in> {ptr_val p + 1 ..+ size_of TYPE('a) - 1}"
    | "ptr_val p \<in> {a + 1 ..+ size_td t - Suc 0}" "ptr_val p \<noteq> a"
    by (auto dest: intvl_neq_start)
  then show ?thesis
  proof cases
    case 1
    have "valid_simple_footprint (ptr_force_type p s) (ptr_val p) (typ_uinfo_t TYPE('a))"
      by (auto simp: valid_simple_footprint_def heap_type_tag_ptr_force_type_HeapType
                     heap_type_tag_ptr_force_type_HeapFootprint size_of_tag)
    with 1 valid_simple_footprintD[of "ptr_force_type p s" a t] ndisjnt
    show ?thesis
      by (auto simp: heap_type_tag_ptr_force_type_HeapType)
  next
    case 2 with valid_simple_footprintD[of "ptr_force_type p s" a t] show ?thesis
      by (auto simp: heap_type_tag_ptr_force_type_HeapFootprint ndisjnt)
  next
    case 3 with valid_simple_footprintD2[of "ptr_force_type p s" a t "ptr_val p"] show ?thesis
      by (auto simp add: heap_type_tag_ptr_force_type_HeapType ndisjnt)
  qed
qed

lemma valid_simple_footprint_fold_ptr_force_type_iff:
  fixes ps :: "'a::mem_type ptr list"
  assumes [simp]: "wf_size_desc t"
  shows "distinct_prop (\<lambda>p1 p2. disjnt (ptr_span p1) (ptr_span p2)) ps \<Longrightarrow>
    valid_simple_footprint (fold ptr_force_type ps s) a t \<longleftrightarrow>
      (valid_simple_footprint s a t \<and> disjnt {a ..+ size_td t} (\<Union>p\<in>set ps. ptr_span p)) \<or>
      (t = typ_uinfo_t TYPE('a) \<and> Ptr a \<in> set ps)"
  by (induction ps arbitrary: s)
     (auto simp: valid_simple_footprint_ptr_force_type_iff size_of_tag distinct_prop_append)

section "Pointers to local (stack) variables"

definition "stack_typ_info t = (stack_byte_name \<notin> td_names t)"

lemma stack_typ_info_export_uinfo[simp]: "stack_typ_info (export_uinfo t) = stack_typ_info t"
  by (simp add: stack_typ_info_def)

lemma stack_typ_info_td_set:
  assumes stack_typ: "stack_typ_info t" 
  assumes t': "(t', n) \<in> td_set t 0" 
  shows "typ_name t' \<noteq> stack_byte_name"
proof (cases "typ_name t' = pad_typ_name")
  case True
  then show ?thesis by (simp add: stack_byte_name_def pad_typ_name_def)
next
  case False
  from td_set_td_names [OF t' False]
  have "typ_name t' \<in> td_names t" .
  with stack_typ show ?thesis
    by (auto simp add: stack_typ_info_def)
qed


lemma stack_typ_info_td_set_stack_byte:
  assumes stack_typ: "stack_typ_info t" 
  assumes t': "(t', n) \<in> td_set t 0" 
  shows "t' \<noteq> typ_uinfo_t TYPE(stack_byte)"
  using stack_typ_info_td_set [OF stack_typ t']
  apply (cases t')
  apply (simp add: typ_uinfo_t_def typ_info_stack_byte)
  done

class stack_type = c_type +
  assumes stack_typ_info: "stack_typ_info (typ_info_t TYPE('a))"
begin
lemma stack_typ_uinfo: "stack_typ_info (typ_uinfo_t TYPE('a))" 
  using stack_typ_info
  by (simp add: typ_uinfo_t_def)

lemma no_stack_byte [simp]: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  by (metis order.refl stack_typ_info_td_set_stack_byte stack_typ_uinfo typ_tag_le_def)

end

lemma stack_typ_info_no_stack_byte: 
  "stack_typ_info t \<Longrightarrow> t \<noteq> typ_uinfo_t TYPE(stack_byte)"
  using stack_typ_info_def typ_tag_le_def stack_typ_info_td_set_stack_byte by fastforce


lemma stack_typ_info_empty_typ_info: 
  "nm \<noteq> stack_byte_name \<Longrightarrow> stack_typ_info (empty_typ_info algn nm)"
  by (simp add: empty_typ_info_def stack_typ_info_def  typ_info_stack_byte)


lemma td_set_list_to_set: 
  "(t, m) \<in> td_set_list xs n \<Longrightarrow> (\<exists>x k. x \<in> set xs \<and> (t, k) \<in> td_set (dt_fst x) 0)"
  apply (induct xs arbitrary: m n)
   apply simp
  by (metis Un_iff dt_tuple.collapse insertCI list.set(2) td_set_list.simps(2) 
      td_set_offset_0_conv' ts5)

lemma td_names_list_to_set: 
  "nm \<in> td_names_list xs \<Longrightarrow> (\<exists>x. x \<in> set xs \<and> nm \<in> td_names (dt_fst x))"
  apply (induct xs arbitrary: )
   apply simp
  by (metis Un_iff dt_tuple.collapse insert_iff list.set(2) td_names_list.simps(2) tnm5)

lemma set_to_td_names_list: 
  "x \<in> set xs \<Longrightarrow> nm \<in> td_names (dt_fst x) \<Longrightarrow> nm \<in> td_names_list xs"
  apply (induct xs arbitrary: )
   apply simp
  by (metis Un_iff dt_tuple.collapse insert_iff list.set(2) td_names_list.simps(2) tnm5)


lemma stack_typ_info_TypAggregateI:
  assumes xs: "\<And>x. x \<in> set xs \<Longrightarrow> stack_typ_info (dt_fst x)"  
  assumes nm: "nm \<noteq> stack_byte_name"
  shows "stack_typ_info (TypDesc algn (TypAggregate (xs)) nm)"
  using xs nm
  apply (auto simp add: stack_typ_info_def stack_byte_name_def dest: td_names_list_to_set)
  done

lemma TypAggregate_not_stack_byte: 
  "TypDesc algn (TypAggregate xs) nm \<noteq> typ_uinfo_t TYPE(stack_byte)"
  by (auto simp add: typ_info_stack_byte typ_uinfo_t_def)

lemma stack_typ_info_TypAggregateD:
  assumes aggr:  "stack_typ_info (TypDesc algn (TypAggregate (xs)) nm)"
  assumes x: "x \<in> set xs" 
  shows "stack_typ_info (dt_fst x)" 
  using aggr x
  by  (auto simp add: stack_typ_info_def stack_byte_name_def dest:set_to_td_names_list)

lemma stack_typ_info_extend_ti:
"stack_typ_info s \<Longrightarrow> stack_typ_info t \<Longrightarrow> 
stack_typ_info (extend_ti s t algn fn d)"
  apply (cases s)
  by (simp add: stack_typ_info_def)


lemma stack_typ_info_ti_pad_combine: 
  "stack_typ_info t \<Longrightarrow> stack_typ_info (ti_pad_combine n t) "
  apply (simp add: ti_pad_combine_def Let_def)
  apply (rule stack_typ_info_extend_ti)
   apply assumption
  apply (auto simp add: stack_typ_info_def typ_uinfo_t_def typ_info_stack_byte )
  done


lemma stack_typ_info_export_uinfo_adjust_ti':
  shows "stack_typ_info (adjust_ti (typ_info_t TYPE('b::stack_type)) acc upd)"
proof -
  from stack_typ_info
  have "stack_typ_info (typ_info_t TYPE('b))".
  then show ?thesis
    by (simp add: stack_typ_info_def)
qed

lemma stack_typ_info_export_uinfo_adjust_ti:
  shows "stack_typ_info (typ_info_t (TYPE('b))) \<Longrightarrow> stack_typ_info (adjust_ti (typ_info_t TYPE('b::c_type)) acc upd)"
  by (simp add: stack_typ_info_def)

lemma stack_typ_info_ti_typ_combine': 
  "stack_typ_info t \<Longrightarrow> 
  stack_typ_info (ti_typ_combine TYPE('b::stack_type) acc upd algn nm t)"
  apply (simp add: ti_typ_combine_def)
  apply (rule stack_typ_info_extend_ti)
   apply assumption
  apply (rule stack_typ_info_export_uinfo_adjust_ti')
  done

lemma stack_typ_info_ti_typ_combine: 
  "stack_typ_info (typ_info_t (TYPE('b))) \<Longrightarrow> stack_typ_info t \<Longrightarrow> 
  stack_typ_info (ti_typ_combine TYPE('b::c_type) acc upd algn nm t)"
  apply (simp add: ti_typ_combine_def)
  apply (rule stack_typ_info_extend_ti)
   apply assumption
  apply (simp add: stack_typ_info_export_uinfo_adjust_ti)
  done

lemma stack_typ_info_ti_typ_pad_combine': 
"stack_typ_info t \<Longrightarrow>
  stack_typ_info (ti_typ_pad_combine TYPE('b::stack_type) acc upd algn nm t)"
  by (auto simp add: ti_typ_pad_combine_def Let_def stack_typ_info_ti_typ_combine' stack_typ_info_ti_pad_combine)

lemma stack_typ_info_ti_typ_pad_combine: 
"stack_typ_info (typ_info_t (TYPE('b))) \<Longrightarrow> stack_typ_info t \<Longrightarrow>
  stack_typ_info (ti_typ_pad_combine TYPE('b::c_type) acc upd algn nm t)"
  by (auto simp add: ti_typ_pad_combine_def Let_def stack_typ_info_ti_typ_combine stack_typ_info_ti_pad_combine)

lemma stack_typ_info_map_align: 
  "stack_typ_info t \<Longrightarrow> stack_typ_info (map_align algn t)"
  by (cases t) (auto simp add: stack_typ_info_def)

lemma stack_typ_info_final_pad: "stack_typ_info t \<Longrightarrow> 
  stack_typ_info (final_pad algn t)"
  by (auto simp add: final_pad_def Let_def stack_typ_info_ti_pad_combine stack_typ_info_map_align)

lemmas stack_typ_info_intros =
 stack_typ_info_empty_typ_info
 stack_typ_info_ti_typ_pad_combine
 stack_typ_info_final_pad
 stack_typ_info

named_theorems stack_typ_info


definition valid_root_footprint :: "heap_typ_desc \<Rightarrow> addr \<Rightarrow> typ_uinfo \<Rightarrow> bool" where
  "valid_root_footprint d x t  \<equiv>
     let n = size_td t in
       0 < n \<and> (\<forall>y. y < n \<longrightarrow>
                    snd (d (x + of_nat y)) = list_map (typ_slice_t t y) \<and> fst (d (x + of_nat y)))"

lemma valid_root_footprint_valid_footprint: "valid_root_footprint d x t \<Longrightarrow> valid_footprint d x t"
  by (auto simp add: valid_root_footprint_def valid_footprint_def Let_def)

lemma valid_root_footprint_valid_footprint_dom_conv: 
     "valid_root_footprint d a t 
      \<longleftrightarrow> 
      (valid_footprint d a t \<and> 
      (\<forall>n. n < size_td t \<longrightarrow> dom (snd (d (a + of_nat n))) = {0..<length (typ_slice_t t n)}))"
  apply (clarsimp simp add: valid_footprint_def valid_root_footprint_def Let_def)
  apply (intro iffI conjI)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (metis list_map_eq not_None_eq dom_list_map map_le_same_dom_eq)
  by (metis dom_list_map map_le_same_dom_eq)

lemma valid_root_footprint_dom_typing: 
  "valid_root_footprint d a t \<Longrightarrow> n < size_td t \<Longrightarrow> 
     dom (snd (d (a + of_nat n))) = {0..<length (typ_slice_t t n)}"
  by (simp add: valid_root_footprint_valid_footprint_dom_conv)
 
lemma valid_root_footprint_typing_conv: 
  fixes p::"'a::c_type ptr"
  assumes valid: "valid_root_footprint d (ptr_val p) (typ_uinfo_t TYPE('a))"
  assumes n: "n < size_of (TYPE('a))" 
  shows "d (ptr_val p + of_nat n) = (True, list_map (typ_slice_t (typ_uinfo_t TYPE('a)) n))"
  using valid n
  by (simp add: valid_root_footprint_def Let_def size_of_def prod_eq_iff)

(* Determine if the given pointer is valid in the given heap. *)
definition
  root_ptr_valid :: "heap_typ_desc \<Rightarrow> 'a::c_type ptr \<Rightarrow> bool"
where
  "root_ptr_valid d p \<equiv>
     valid_root_footprint d (ptr_val (p::'a ptr)) (typ_uinfo_t TYPE('a)) \<and>  
     c_guard p"

lemma root_ptr_valid_c_guard: "root_ptr_valid d p \<Longrightarrow> c_guard p"
  by (simp add: root_ptr_valid_def)

lemma root_ptr_valid_typing_conv:
  fixes p::"'a::c_type ptr"
  assumes valid: "root_ptr_valid d p"
  assumes n: "n < size_of (TYPE('a))" 
  shows "d (ptr_val p + of_nat n) = (True, list_map (typ_slice_t (typ_uinfo_t TYPE('a)) n))"
  using valid
  by (simp add: root_ptr_valid_def valid_root_footprint_typing_conv [OF _ n])

lemma root_ptr_valid_h_t_valid: "root_ptr_valid d p \<Longrightarrow> d, c_guard \<Turnstile>\<^sub>t p"
  by (simp add: h_t_valid_def root_ptr_valid_def valid_root_footprint_valid_footprint_dom_conv)

lemma valid_root_footprint_cong_state:
  assumes t: "wf_size_desc t"
  assumes eq: "\<And>p'. p' \<in> {p ..+size_td t} \<Longrightarrow> s p' = s' p'"
  shows "valid_root_footprint s p t \<longleftrightarrow> valid_root_footprint s' p t"
  unfolding valid_root_footprint_def Let_def
  using eq wf_size_desc_gt(1)[OF t]
  using intvl_split[of 1 "size_td t" p]
  by (metis intvlI)

lemma (in mem_type) valid_root_foot_print_ptr_force_type:
  "valid_root_footprint
    (ptr_force_type (p::'a ptr) s) (ptr_val p) (typ_uinfo_t (TYPE('a)))"
  by (simp add: htd_upd_at local.ptr_force_type_def 
      local.size_of_fold order_less_imp_le valid_root_footprint_def)

lemma list_map_greatest_last: "xs \<noteq> [] \<Longrightarrow> last xs = v \<Longrightarrow> list_map xs (GREATEST k. \<exists>v. list_map xs k = Some v) = Some v"
proof (induct n == "length xs" arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc n xs)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis using Suc by simp
  next
    case (Cons x xs')
    have xs: "xs = x#xs'" by fact
    show ?thesis
    proof (cases xs')
      case Nil

      have *: "(GREATEST k::nat. \<exists>v'. [0 \<mapsto> v] k = Some v') = 0"
        by (rule Greatest_equality) (auto simp add: fun_upd_def split: if_split_asm)

      from Nil show ?thesis using Suc.prems xs 
        by (simp add: list_map_def * fun_upd_def Greatest_equality)
    next
      case (Cons x' xs'')
      from Suc xs Cons obtain n: "n = length xs'" and non_empty: "xs' \<noteq> []" and last: "last xs' = v"
        by simp
      
      from Suc.hyps (1)  [OF n non_empty last]
      have hyp: "list_map xs' (GREATEST x. \<exists>v. list_map xs' x = Some v) = Some v" .
      from hyp show ?thesis by (simp add: xs Cons add: list_map_eq split: if_split_asm)
    qed
  qed
qed


lemma valid_root_footprint_valid_simple_footprint:
  assumes valid_td: "size_td t \<le> addr_card"
  shows "valid_root_footprint d x t \<Longrightarrow> valid_simple_footprint d x t"
  apply (clarsimp simp add: valid_root_footprint_def valid_simple_footprint_def Let_def)
proof -
  assume sz: "0 < size_td t"
  assume root[rule_format]: "\<forall>y < size_td t. snd (d (x + word_of_nat y)) = list_map (typ_slice_t t y) \<and> fst (d (x + word_of_nat y))"
  from root [of 0, simplified] sz obtain 
    d_x: "d x = (True, list_map (typ_slice_t t 0))"
    by (cases "d x") auto

  have x_HeapType: "heap_type_tag d x = HeapType t"
  proof -
    from last_typ_slice_t have "last (typ_slice_t t 0) = (t, True)" .
  
    from list_map_greatest_last [OF typ_slice_t_not_empty this]
    have *: "list_map (typ_slice_t t 0) (GREATEST k. \<exists>a b. list_map (typ_slice_t t 0) k = Some (a,b)) = Some (t, True)"
      by auto
    from d_x  show ?thesis
      apply (clarsimp simp  add: heap_type_tag_def *, intro conjI)
      using * apply blast
      by (metis less_irrefl list_map_eq option.simps(3))
  qed

  show "heap_type_tag d x = HeapType t \<and> (\<forall>y. y \<in> {x + 1..+size_td t - Suc 0} \<longrightarrow> heap_type_tag d y = HeapFootprint)"
  proof
    from x_HeapType 
    show "heap_type_tag d x = HeapType t" .
  next
    show "\<forall>y. y \<in> {x + 1..+size_td t - Suc 0} \<longrightarrow> heap_type_tag d y = HeapFootprint"
    proof (standard+)
      fix y
      assume y_bounds: "y \<in> {x + 1..+size_td t - Suc 0}"
      with sz obtain off where y_off: "y = x + word_of_nat off" and off: "off < size_td t" 
        by (meson intvlD intvl_plus_sub_Suc)
      from root [OF off] y_off have d_y: "d y = (True, list_map (typ_slice_t t off))"
        by (cases "d (x + word_of_nat off)") auto
     

      have "x \<notin> {x + 1..+size_td t - Suc 0}"
        using intvl_Suc_nmem'' [OF valid_td [simplified addr_card_len_of_conv]] by blast
      with y_bounds y_off have off_non_zero: "off \<noteq> 0" by (cases off) auto

      from last_typ_slice_t_non_zero [OF off_non_zero] have "last (typ_slice_t t off) = (t, False)" .
      from list_map_greatest_last [OF typ_slice_t_not_empty this]
      have *: "list_map (typ_slice_t t off) (GREATEST k. \<exists>a b. list_map (typ_slice_t t off) k = Some (a,b)) =
                 Some (t, False)"
        by auto
      from d_y show "heap_type_tag d y = HeapFootprint" 
        apply (clarsimp simp  add: heap_type_tag_def *, intro conjI)
        using * apply blast
        by (metis less_irrefl list_map_eq option.simps(3))
    qed
  qed
qed

lemma valid_root_footprint_valid_simple_footprint_typ_uinfo_t:
  assumes valid_root: "valid_root_footprint d x (typ_uinfo_t TYPE('a::mem_type))" 
  shows "valid_simple_footprint d x (typ_uinfo_t TYPE('a::mem_type))"
  apply (rule valid_root_footprint_valid_simple_footprint [OF _ valid_root])
  by (metis less_imp_le max_size size_of_def typ_uinfo_size)

lemma first_in_intvl:
  "b \<noteq> 0 \<Longrightarrow> a \<in> {a ..+ b}"
  by (force simp: intvl_def)

lemma list_map_comono:
  assumes  s: "list_map m \<subseteq>\<^sub>m list_map n"
  shows    "m \<le> n"
  using s
proof (induct m arbitrary: n rule: rev_induct)
  case Nil thus ?case unfolding list_map_def by simp
next
  case (snoc x xs)

  from snoc.prems have
    sm: "[length xs \<mapsto> x] ++ list_map xs \<subseteq>\<^sub>m list_map n"
    unfolding list_map_def by simp

  hence xsn: "xs \<le> n"
    by (rule snoc.hyps [OF map_add_le_mapE])

  have "list_map n (length xs) = Some x" using sm
    by (simp add: map_le_def list_map_def merge_dom2 set_zip)

  hence "length xs < length n" and "x = n ! length xs"
    by (auto simp add: list_map_eq split: if_split_asm)

  thus "xs @ [x] \<le> n" using xsn
    by (simp add: append_one_prefix less_eq_list_def)
qed

lemma valid_root_footprint_overlap_sub_typ: 
  assumes valid_root_x: "valid_root_footprint d x t"
  assumes valid_y: "valid_footprint d y s" 
  assumes overlap: "{x ..+ size_td t} \<inter> {y ..+ size_td s} \<noteq> {}"
  shows "s \<le> t"
  using valid_root_x overlap valid_y 
  by (auto simp add: valid_root_footprint_def valid_footprint_def Let_def typ_tag_le_def)
    (metis intvlD list_map_comono typ_slice_sub typ_tag_le_def)

lemma valid_root_footprint_type_neq:
  "\<lbrakk> valid_root_footprint d p s;
     valid_root_footprint d q t;
     s \<noteq> t \<rbrakk> \<Longrightarrow>
   p \<notin> {q..+ (size_td t)}"
  by (metis antisym_conv disjoint_iff first_in_intvl neq0_conv valid_root_footprint_def 
      valid_root_footprint_overlap_sub_typ valid_root_footprint_valid_footprint)

lemma valid_root_footprint_ptr_force_type_iff:
  fixes p :: "'a::mem_type ptr"
  assumes t: "wf_size_desc t"
  shows "valid_root_footprint (ptr_force_type p s) a t \<longleftrightarrow>
    (valid_root_footprint s a t \<and> disjnt {a ..+ size_td t} (ptr_span p)) \<or>
    (t = typ_uinfo_t TYPE('a) \<and> p = Ptr a)"
proof cases
  assume disjnt: "disjnt {a ..+ size_td t} (ptr_span p)"
  moreover have "p \<noteq> Ptr a"
    using disjnt[unfolded disjnt_iff, THEN spec, of a] t[THEN wf_size_desc_gt(1)]
    by (cases p) (auto simp: intvl_self)
  moreover have "valid_root_footprint (ptr_force_type p s) a t = valid_root_footprint s a t"
    using t disjnt
    by (intro valid_root_footprint_cong_state ptr_force_type_disj) (simp_all add: disjnt_iff)
  ultimately show ?thesis
    by simp
next
  assume ndisjnt: "\<not> disjnt {a ..+ size_td t} (ptr_span p)"
  show ?thesis
    using ndisjnt
    by (metis (no_types) valid_root_footprint_valid_simple_footprint_typ_uinfo_t disjnt_def
        valid_root_foot_print_ptr_force_type intvl_inter ptr_val.ptr_val_def size_of_tag t
        valid_simple_footprint_ptr_force_type_iff valid_root_footprint_type_neq)
qed

lemma valid_root_footprint_fold_ptr_force_type_iff:
  fixes ps :: "'a::mem_type ptr list"
  assumes [simp]: "wf_size_desc t"
  shows "distinct_prop (\<lambda>p1 p2. disjnt (ptr_span p1) (ptr_span p2)) ps \<Longrightarrow>
    valid_root_footprint (fold ptr_force_type ps s) a t \<longleftrightarrow>
      (valid_root_footprint s a t \<and> disjnt {a ..+ size_td t} (\<Union>p\<in>set ps. ptr_span p)) \<or>
      (t = typ_uinfo_t TYPE('a) \<and> Ptr a \<in> set ps)"
  by (induction ps arbitrary: s)
     (auto simp: valid_root_footprint_ptr_force_type_iff size_of_tag distinct_prop_append)

(* Two valid footprints will either overlap completely or not at all. *)
lemma valid_simple_footprint_neq:
  assumes valid_p: "valid_simple_footprint d p s"
      and valid_q: "valid_simple_footprint d q t"
      and neq: "p \<noteq> q"
  shows "p \<notin> {q..+ (size_td t)}"
proof -
  have heap_type_p: "heap_type_tag d p = HeapType s"
    apply (metis valid_p valid_simple_footprint_def)
    done

  have heap_type_q: "heap_type_tag d q = HeapType t"
    apply (metis valid_q valid_simple_footprint_def)
    done

  have heap_type_q_footprint:
    "\<And>x. x \<in> {(q + 1)..+(size_td t - Suc 0)} \<Longrightarrow> heap_type_tag d x = HeapFootprint"
    apply (insert valid_q)
    apply (simp add: valid_simple_footprint_def)
    done

  show ?thesis
    using heap_type_q_footprint heap_type_p neq
         intvl_neq_start heap_type_q
    by (metis heap_typ_contents.simps(2))
qed

(* Two valid footprints with different types will never overlap. *)
lemma valid_simple_footprint_type_neq:
  "\<lbrakk> valid_simple_footprint d p s;
     valid_simple_footprint d q t;
     s \<noteq> t \<rbrakk> \<Longrightarrow>
   p \<notin> {q..+ (size_td t)}"
  apply (subgoal_tac "p \<noteq> q")
   apply (rule valid_simple_footprint_neq, simp_all)[1]
  apply (clarsimp simp: valid_simple_footprint_def)
  done

lemma valid_simple_footprint_neq_disjoint:
  "\<lbrakk> valid_simple_footprint d p s; valid_simple_footprint d q t; p \<noteq> q \<rbrakk> \<Longrightarrow>
      {p..+(size_td s)} \<inter> {q..+ (size_td t)} = {}"
  apply (rule ccontr)
  apply (fastforce simp: valid_simple_footprint_neq dest!: intvl_inter)
  done

lemma valid_simple_footprint_type_neq_disjoint:
  "\<lbrakk> valid_simple_footprint d p s;
     valid_simple_footprint d q t;
     s \<noteq> t \<rbrakk> \<Longrightarrow>
   {p..+(size_td s)} \<inter> {q..+ (size_td t)} = {}"
  apply (subgoal_tac "p \<noteq> q")
   apply (rule valid_simple_footprint_neq_disjoint, simp_all)[1]
  apply (clarsimp simp: valid_simple_footprint_def)
  done

lemma valid_simple_footprint_disjnt_or_eq:
  "valid_simple_footprint d a1 t1 \<Longrightarrow> valid_simple_footprint d a2 t2 \<Longrightarrow>
    disjnt {a1 ..+ size_td t1} {a2 ..+ size_td t2} \<or> (a1 = a2 \<and> t1 = t2)"
  using valid_simple_footprint_type_neq_disjoint[of d a1 t1 a2 t2]
  using valid_simple_footprint_neq_disjoint[of d a1 t1 a2 t2]
  by (auto simp: disjnt_def)

lemma valid_root_footprint_type_neq_disjoint:
  "\<lbrakk> valid_root_footprint d p s;
     valid_root_footprint d q t;
     s \<noteq> t \<rbrakk> \<Longrightarrow>
   {p..+(size_td s)} \<inter> {q..+ (size_td t)} = {}"
  by (metis intvl_inter valid_root_footprint_type_neq)

lemma valid_root_footprint_neq:
  assumes valid_p: "valid_root_footprint d p s"
      and valid_q: "valid_root_footprint d q t"
      and neq: "p \<noteq> q"
    shows "p \<notin> {q..+ (size_td t)}"
proof 
  assume p: "p \<in> {q..+size_td t}"
  then have "\<not> t \<le> s"
    by (metis (no_types, opaque_lifting) less_irrefl less_le_trans neq valid_footprint_sub2 
        valid_p valid_q valid_root_footprint_valid_footprint)
  moreover
  from p have "{p..+size_td s} \<inter> {q..+size_td t} \<noteq> {}"
    by (metis disjoint_iff first_in_intvl less_irrefl valid_p valid_root_footprint_def)

  from valid_root_footprint_overlap_sub_typ [OF valid_p  valid_root_footprint_valid_footprint [OF valid_q ] this] 
  have "t \<le> s" .
  ultimately show False
    by blast
qed

lemma valid_root_footprint_neq_disjoint:
  "\<lbrakk> valid_root_footprint d p s; valid_root_footprint d q t; p \<noteq> q \<rbrakk> \<Longrightarrow>
      {p..+(size_td s)} \<inter> {q..+ (size_td t)} = {}"
  by (metis intvl_inter valid_root_footprint_neq)

lemma valid_root_footprint_disjnt_or_eq:
  "valid_root_footprint d a1 t1 \<Longrightarrow> valid_root_footprint d a2 t2 \<Longrightarrow>
    disjnt {a1 ..+ size_td t1} {a2 ..+ size_td t2} \<or> (a1 = a2 \<and> t1 = t2)"
  using valid_root_footprint_type_neq_disjoint[of d a1 t1 a2 t2]
  using valid_root_footprint_neq_disjoint[of d a1 t1 a2 t2]
  by (auto simp: disjnt_def)

definition ptr_aligned_u :: "typ_uinfo \<Rightarrow> addr \<Rightarrow> bool" where
  "ptr_aligned_u t a \<equiv>  2^(align_td t) dvd unat a"

lemma ptr_aligned_ptr_aligned_u_conv:
  fixes p::"'a::c_type ptr"
  shows "ptr_aligned p = ptr_aligned_u (typ_uinfo_t TYPE('a)) (ptr_val p)"
  by (simp add: ptr_aligned_def ptr_aligned_u_def align_of_def typ_uinfo_t_def)

definition c_null_guard_u :: "typ_uinfo \<Rightarrow> addr \<Rightarrow> bool" where
  "c_null_guard_u t a \<equiv> 0 \<notin> {a..+size_td t}"

lemma c_null_guard_c_null_guard_u_conv:
  fixes p::"'a::c_type ptr"
  shows "c_null_guard p = c_null_guard_u (typ_uinfo_t TYPE('a)) (ptr_val p)"
  by (simp add: c_null_guard_def c_null_guard_u_def size_of_def)

definition c_guard_u :: "typ_uinfo \<Rightarrow> addr \<Rightarrow> bool" where
  "c_guard_u t a \<equiv>  ptr_aligned_u t a \<and> c_null_guard_u t a"

lemma c_guard_c_guard_u_conv:
  fixes p::"'a::c_type ptr"
  shows "c_guard p = c_guard_u (typ_uinfo_t TYPE('a)) (ptr_val p)"
  by (simp add: ptr_aligned_ptr_aligned_u_conv c_guard_def c_guard_u_def c_null_guard_c_null_guard_u_conv)

definition
  root_ptr_valid_u :: "typ_uinfo \<Rightarrow> heap_typ_desc \<Rightarrow> addr \<Rightarrow> bool" where
  "root_ptr_valid_u t d a \<equiv> valid_root_footprint d a t \<and> c_guard_u t a"

definition
  cvalid_u :: "typ_uinfo \<Rightarrow> heap_typ_desc \<Rightarrow> addr \<Rightarrow> bool" where
  "cvalid_u t d a \<equiv> valid_footprint d a t \<and> c_guard_u t a"

lemma root_ptr_valid_root_ptr_valid_u_conv:
  fixes p::"'a::c_type ptr"
  shows "root_ptr_valid d p = root_ptr_valid_u (typ_uinfo_t TYPE('a)) d (ptr_val p)"
  by (simp add: root_ptr_valid_def root_ptr_valid_u_def c_guard_c_guard_u_conv)

lemma root_ptr_valid_ptr_force_type:
  "c_guard p \<Longrightarrow> root_ptr_valid (ptr_force_type p s) (p::'a::mem_type ptr)"
  by (simp add: root_ptr_valid_root_ptr_valid_u_conv root_ptr_valid_u_def c_guard_c_guard_u_conv
                valid_root_foot_print_ptr_force_type)
lemma cvalid_cvalid_u_conv:
  fixes p::"'a::c_type ptr"
  shows "d \<Turnstile>\<^sub>t p = cvalid_u (typ_uinfo_t TYPE('a)) d (ptr_val p)"
  by  (simp add: h_t_valid_def cvalid_u_def c_guard_c_guard_u_conv)

lemma root_ptr_valid_u_cvalid_u: "root_ptr_valid_u t d a \<Longrightarrow> cvalid_u t d a"
  by (simp add: root_ptr_valid_u_def cvalid_u_def valid_root_footprint_valid_footprint)

lemma fold_root_ptr_valid_u:
 "root_ptr_valid_u (typ_uinfo_t TYPE('a::c_type)) d a = root_ptr_valid d (PTR ('a) a)"
  by (simp add: root_ptr_valid_root_ptr_valid_u_conv)

lemma ptr_force_type_eq_ptr_force_type_u:
  "ptr_force_type (p :: 'a::c_type ptr) = ptr_force_type_u (typ_uinfo_t TYPE('a)) (ptr_val p)"
  by (simp add: ptr_force_type_def ptr_force_type_u_def typ_slices_def typ_slices_u_def
      size_of_def)

lemma typ_slices_u_length [simp]: "length (typ_slices_u t) = size_td t"
  by (simp add: typ_slices_u_def)

lemma typ_slices_u_index [simp]:
  "n < size_td t \<Longrightarrow> typ_slices_u t ! n = list_map (typ_slice_t t n)"
  by (simp add: typ_slices_u_def)

lemma valid_root_footprint_ptr_force_type_u:
  "wf_size_desc t \<Longrightarrow> size_td t < addr_card \<Longrightarrow>
    valid_root_footprint (ptr_force_type_u t a h) a t"
  by (simp add: valid_root_footprint_def ptr_force_type_u_def Let_def wf_size_desc_gt htd_upd_at)

lemma valid_root_footprint_ptr_force_type_u_size:
  "wf_size_desc t \<Longrightarrow> size_td t < addr_card \<Longrightarrow>
    valid_root_footprint (ptr_force_type_u t a h) a t"
  by (simp add: valid_root_footprint_def ptr_force_type_u_def Let_def wf_size_desc_gt htd_upd_at)


definition 
stack_alloc:: "addr set \<Rightarrow> 'a:: mem_type itself \<Rightarrow> heap_typ_desc \<Rightarrow> ('a ptr \<times> heap_typ_desc) set" where
\<open>stack_alloc \<S> T d = {
  (p::'a ptr, d').
     ptr_span p \<subseteq> \<S> \<and> 
     typ_uinfo_t (TYPE('a)) \<noteq> typ_uinfo_t (TYPE(stack_byte)) \<and>
     (\<forall>a \<in> ptr_span p. root_ptr_valid d (PTR (stack_byte) a)) \<and>
     ptr_aligned p \<and> 
     d' = ptr_force_type p d  
    }\<close>

(* FIXME support for local arrays*)
definition 
stack_allocs:: "nat \<Rightarrow> addr set \<Rightarrow> 'a:: mem_type itself \<Rightarrow> heap_typ_desc \<Rightarrow> ('a ptr \<times> heap_typ_desc) set" where
\<open>stack_allocs n \<S> T d = {
  (p::'a ptr, d').
     0 < n \<and>
     (\<forall>i < n. ptr_span (p +\<^sub>p int i) \<subseteq> \<S>) \<and> 
     typ_uinfo_t (TYPE('a)) \<noteq> typ_uinfo_t (TYPE(stack_byte)) \<and>
     (\<forall>a \<in> {ptr_val p ..+ n * size_of TYPE('a)} . root_ptr_valid d (PTR (stack_byte) a)) \<and>
     ptr_aligned p \<and> 
     d' = fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) [0..<n] d  
    }\<close>

lemma stack_alloc_stack_allocs_conv: "stack_alloc = stack_allocs 1"
  by (simp add: stack_alloc_def stack_allocs_def fun_eq_iff)

lemma htd_update_list_other:  
  assumes bound: "length xs < addr_card"
  assumes notin: "x \<notin> {p..+length xs}" 
  shows "htd_update_list p xs d x = d x"
  using bound notin
proof (induct xs arbitrary: p d x)
  case Nil
  then show ?case by simp
next
  case (Cons x1 xs)
  from Cons.prems obtain 
    "Suc (length xs) < addr_card" and
    bound': "length xs < addr_card" and
    "x \<notin> {p..+Suc (length xs)}" and
    notin': "x \<notin> {(p + 1)..+(length xs)}" and
    neq: "x \<noteq> p" 
    apply clarsimp
    by (metis One_nat_def add_diff_cancel_left' intvl_plus_sub_Suc intvl_self 
        plus_1_eq_Suc zero_less_Suc)

  note hyp = Cons.hyps [OF bound' notin', where d = "(d(p := (True, snd (d p) ++ x1)))"]
  show ?case by (simp add: hyp fun_upd_other neq)
qed

lemma dom_typ_slice_t_stack_byte: 
  "dom (list_map (typ_slice_t (typ_uinfo_t TYPE(stack_byte)) n)) = {0}"
  by (simp add: typ_info_stack_byte typ_uinfo_t_def)

lemma htd_update_list_same':
  "\<lbrakk>0 < unat k; unat k \<le> addr_card - length v\<rbrakk> \<Longrightarrow> htd_update_list (p + k) v h p = h p"
  apply (insert htd_update_list_same [where v=v and p=p and h=h and k="unat k"])
  apply clarsimp
  done

lemma dom_htd_update_list:
 assumes xs_bound: "length xs < addr_card" 
 assumes n_bound: "n < length xs" 
 shows "dom (snd (htd_update_list a xs d (a + word_of_nat n))) =
         dom (snd (d (a + word_of_nat n))) \<union> dom (xs ! n)"
  using xs_bound n_bound
proof (induct xs arbitrary: n a d)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  from Cons.prems obtain 
    "Suc (length xs) < addr_card" and
    lxs: "length xs < addr_card" and
    n: "n < Suc (length xs)"
    by auto
  note hyp =  Cons.hyps [OF lxs]
  show ?case
  proof (cases n)
    case 0
    show ?thesis
      apply (simp add: 0)
      by (smt (verit, ccfv_threshold) One_nat_def add_cancel_left_right add_diff_cancel_left' 
          dom_map_add fun_upd_same htd_update_list_same' le_eq_less_or_eq le_iff_add 
          less_Suc_eq_0_disj lxs nat_neq_iff snd_conv sup_commute unsigned_1 zero_order(1))
  next
    case (Suc m)
    have conv: "a + 1 + word_of_nat m = a + (1 + word_of_nat m)"
      by simp
  
    from Suc n have m_xs: "m < length xs" by simp
    note hyp = hyp [where a = "a + 1" and d = "(d(a := (True, snd (d a) ++ x)))" and n = m, OF m_xs, simplified conv] 
    show ?thesis 
      apply (simp add: Suc)
      apply (simp add: hyp )
      by (smt (verit, best) add_cancel_left_right add_diff_cancel_left' add_leE fun_upd_other 
          less_natE linorder_not_less lxs m_xs one_plus_x_zero plus_1_eq_Suc)
  qed
qed

lemma dom_ptr_retyp:
  fixes p::"'a::mem_type ptr"
  assumes n: "n < size_of TYPE('a)"
  shows "dom (snd (ptr_retyp p d (ptr_val p + of_nat n))) = 
          dom (snd (d (ptr_val p + of_nat n))) \<union> 
          {0..<length (typ_slice_t (typ_uinfo_t TYPE('a)) n)}"
proof -
  have sz_bound: "size_of TYPE('a) < addr_card" by simp
  hence l_slices: "length (typ_slices TYPE('a)) < addr_card" by simp
  with sz_bound n have n': "n < length (typ_slices TYPE('a))" by simp 

  from n'
  have dom_conv: "dom (typ_slices TYPE('a) ! n) = {0..<length (typ_slice_t (typ_uinfo_t TYPE('a)) n)}"
    by (simp)
  show ?thesis
    apply (simp add: ptr_retyp_def size_of_def )
    apply (simp add:  dom_htd_update_list [OF l_slices n', where a = "ptr_val p" and d = d] dom_conv)
    done
qed

lemma length_typ_slice_t: "0 < length (typ_slice_t t n )" 
  by (cases t) auto 

lemma valid_root_footprint_retyp_stack':
  fixes p::"'a::mem_type ptr"
  assumes stack: "\<forall>a \<in> ptr_span p. valid_root_footprint d a (typ_uinfo_t TYPE(stack_byte))"
  shows "valid_root_footprint(ptr_retyp p d) (ptr_val p) (typ_uinfo_t TYPE('a))"
proof -
  {
    fix n 
    assume n_bound: "n < size_td (typ_info_t TYPE('a))"
    have "dom (snd (ptr_retyp p d (ptr_val p + word_of_nat n))) =
           {0..<length (typ_slice_t (typ_uinfo_t TYPE('a)) n)}" 
    proof -
      from n_bound have n_sz: "n < size_of (TYPE('a))" by (simp add: size_of_def)
      from n_sz
      have "ptr_val p + word_of_nat n \<in> ptr_span p"
        by (simp add: intvlI)
      note conv = valid_root_footprint_dom_typing [OF stack [rule_format, OF this], where n=0, simplified ]
      have dom_eq: "dom (snd (d (ptr_val p + word_of_nat n))) = {0}"
        by (simp add: conv typ_uinfo_t_def typ_info_stack_byte)

      from length_typ_slice_t have l: "0 < length (typ_slice_t (typ_uinfo_t TYPE('a)) n)" by simp
      show ?thesis 
        apply (simp add: dom_ptr_retyp [OF n_sz] dom_eq )
        using l atLeastLessThan_iff by blast
    qed
  } note  dom_conv = this
  show ?thesis
    by (simp add: valid_root_footprint_valid_footprint_dom_conv ptr_retyp_valid_footprint dom_conv)
qed


lemma (in mem_type) ptr_force_type_valid_footprint:
  "valid_footprint (ptr_force_type p d) (ptr_val (p::'a ptr)) (typ_uinfo_t TYPE('a))"
  using valid_root_foot_print_ptr_force_type valid_root_footprint_valid_footprint by blast

lemma ptr_force_type_valid_footprint:
  "valid_footprint (ptr_force_type p d) (ptr_val (p::'a::mem_type ptr)) (typ_uinfo_t TYPE('a))"
  using valid_root_foot_print_ptr_force_type valid_root_footprint_valid_footprint by blast

lemma valid_root_footprint_retyp_stack:
  fixes p::"'a::mem_type ptr"
  assumes stack: "\<forall>a \<in> ptr_span p. valid_root_footprint d a (typ_uinfo_t TYPE(stack_byte))"
  shows "valid_root_footprint(ptr_force_type p d) (ptr_val p) (typ_uinfo_t TYPE('a))"
proof -
  {
    fix n 
    assume n_bound: "n < size_td (typ_info_t TYPE('a))"
    have "dom (snd (ptr_force_type p d (ptr_val p + word_of_nat n))) =
           {0..<length (typ_slice_t (typ_uinfo_t TYPE('a)) n)}" 
    proof -
      from n_bound have n_sz: "n < size_of (TYPE('a))" by (simp add: size_of_def)
      from n_sz
      have "ptr_val p + word_of_nat n \<in> ptr_span p"
        by (simp add: intvlI)
      note conv = valid_root_footprint_dom_typing [OF stack [rule_format, OF this], where n=0, simplified ]
      have dom_eq: "dom (snd (d (ptr_val p + word_of_nat n))) = {0}"
        by (simp add: conv typ_uinfo_t_def typ_info_stack_byte)

      from length_typ_slice_t have l: "0 < length (typ_slice_t (typ_uinfo_t TYPE('a)) n)" by simp
      show ?thesis 
        by (simp add: n_sz size_of_tag valid_root_foot_print_ptr_force_type 
            valid_root_footprint_dom_typing)
    qed
  } note  dom_conv = this
  show ?thesis
    by (simp add: valid_root_footprint_valid_footprint_dom_conv ptr_force_type_valid_footprint dom_conv)
qed

lemma root_ptr_valid_retyp_stack':
  fixes p::"'a::mem_type ptr"
  assumes stack: "\<forall>a \<in> ptr_span p. root_ptr_valid d (PTR (stack_byte) a)"
  assumes aligned: "ptr_aligned p"
  shows "root_ptr_valid (ptr_retyp p d) p"
proof -
  from stack 
  have stack': "\<forall>a \<in> ptr_span p. valid_root_footprint d a (typ_uinfo_t TYPE(stack_byte))"
    by (simp add: root_ptr_valid_def)
  from stack aligned have c_guard: "c_guard p"
    apply (simp add: root_ptr_valid_def c_guard_def c_null_guard_def)
    using first_in_intvl by blast
  
  from valid_root_footprint_retyp_stack' [OF stack'] 
  have "valid_root_footprint (ptr_retyp p d) (ptr_val p) (typ_uinfo_t TYPE('a))".
  with c_guard show ?thesis
    by (simp add: root_ptr_valid_def)
qed

lemma root_ptr_valid_retyp_stack:
  fixes p::"'a::mem_type ptr"
  assumes stack: "\<forall>a \<in> ptr_span p. root_ptr_valid d (PTR (stack_byte) a)"
  assumes aligned: "ptr_aligned p"
  shows "root_ptr_valid (ptr_force_type p d) p"
proof -
  from stack 
  have stack': "\<forall>a \<in> ptr_span p. valid_root_footprint d a (typ_uinfo_t TYPE(stack_byte))"
    by (simp add: root_ptr_valid_def)
  from stack aligned have c_guard: "c_guard p"
    apply (simp add: root_ptr_valid_def c_guard_def c_null_guard_def)
    using first_in_intvl by blast
  
  from valid_root_footprint_retyp_stack [OF stack'] 
  have "valid_root_footprint (ptr_force_type p d) (ptr_val p) (typ_uinfo_t TYPE('a))".
  with c_guard show ?thesis
    by (simp add: root_ptr_valid_def)
qed

lemma fold_ptr_retyp_other:
  fixes p::"'a::mem_type ptr"
  assumes a_notin: "a \<notin> {ptr_val p ..+ n * size_of TYPE('a)}"
  shows "(fold (\<lambda>i. ptr_retyp (p +\<^sub>p int i)) [0..<n] d) a = d a"
  using a_notin 
proof (induct n arbitrary: d)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems have a_notin: "a \<notin> {ptr_val p..+ Suc n * size_of TYPE('a)}" .
  from a_notin 
  have a_notin_n: "a \<notin> {ptr_val p..+ n * size_of TYPE('a)}" 
    by (metis add_leD2 intvlD intvlI linorder_not_less mult.commute mult_Suc_right)
  from a_notin 
  have a_notin_Suc: "a \<notin> ptr_span (p +\<^sub>p int n)"
    apply (clarsimp simp add: intvl_def ptr_add_def)
    by (metis (no_types, opaque_lifting) add.commute add_less_cancel_right mult.commute of_nat_add of_nat_mult)

  have fold_split: "(fold (\<lambda>i. ptr_retyp (p +\<^sub>p int i)) ([0..<Suc n]) d) = 
        (fold (\<lambda>i. ptr_retyp (p +\<^sub>p int i)) ([0..<n] @ [n]) d)"
    apply (simp only: Many_More.split_upt_on_n [where n=n])
    apply simp
    done
  show ?case 
    apply (simp only: fold_split)
    apply (simp only: fold_append)
    apply (simp)
    apply (subst (2) Suc.hyps [OF a_notin_n, symmetric])
    apply (rule ptr_retyp_d [OF a_notin_Suc])
    done
qed

lemma (in mem_type) ptr_force_type_d:
  "x \<notin> {ptr_val (p::'a ptr)..+size_of TYPE('a)} \<Longrightarrow>
      ptr_force_type p d x = d x"
  by (simp add: htd_upd_disj local.ptr_force_type_def)

lemma fold_ptr_force_type_other:
  fixes p::"'a::mem_type ptr"
  assumes a_notin: "a \<notin> {ptr_val p ..+ n * size_of TYPE('a)}"
  shows "(fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) [0..<n] d) a = d a"
  using a_notin 
proof (induct n arbitrary: d)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems have a_notin: "a \<notin> {ptr_val p..+ Suc n * size_of TYPE('a)}" .
  from a_notin 
  have a_notin_n: "a \<notin> {ptr_val p..+ n * size_of TYPE('a)}" 
    by (metis add_leD2 intvlD intvlI linorder_not_less mult.commute mult_Suc_right)
  from a_notin 
  have a_notin_Suc: "a \<notin> ptr_span (p +\<^sub>p int n)"
    apply (clarsimp simp add: intvl_def ptr_add_def)
    by (metis (no_types, opaque_lifting) add.commute add_less_cancel_right mult.commute of_nat_add of_nat_mult)

  have fold_split: "(fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) ([0..<Suc n]) d) = 
        (fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) ([0..<n] @ [n]) d)"
    apply (simp only: Many_More.split_upt_on_n [where n=n])
    apply simp
    done
  show ?case 
    apply (simp only: fold_split)
    apply (simp only: fold_append)
    apply (simp)
    apply (subst (2) Suc.hyps [OF a_notin_n, symmetric])
    apply (rule ptr_force_type_d [OF a_notin_Suc])
    done
qed

lemma root_ptr_valid_domain:
  fixes p::"'a::mem_type ptr"
  assumes "root_ptr_valid d p"
  assumes "\<And>a. a \<in> ptr_span p \<Longrightarrow> d' a = d a"
  shows "root_ptr_valid d' p"
  by (metis (no_types, lifting) assms(1) assms(2) root_ptr_valid_def s_footprintD s_footprintI2 size_of_tag valid_root_footprint_def)

lemma root_ptr_valid_domain': 
  fixes p::"'a::mem_type ptr"
  assumes "\<And>a.  a \<in> ptr_span p \<Longrightarrow>  d' a = d a"
  shows "root_ptr_valid d' p = root_ptr_valid d p"
  by (metis assms root_ptr_valid_domain)

lemma root_ptr_valid_range_not_NULL:
  "root_ptr_valid htd (p :: ('a :: c_type) ptr)
      \<Longrightarrow> 0 \<notin> {ptr_val p ..+ size_of TYPE('a)}"
  apply (clarsimp simp: root_ptr_valid_def)
  apply (metis c_guard_def c_null_guard_def)
  done

lemma intvl_no_overflow_nat':
  assumes no_overflow: "unat a + b \<le> 2 ^ len_of TYPE('a::len)"
  shows "(x \<in> {(a :: 'a word) ..+ b}) = (unat a \<le> unat x \<and> unat x < (unat a + b))"
  apply (simp add: intvl_def)
  using no_overflow
  apply (intro iffI conjI)
    apply (smt (verit) add.commute nat_add_left_cancel_less nat_le_iff_add trans_less_add1 unat_of_nat_len word_arith_nat_add)
   apply (smt (verit) add.commute nat_add_left_cancel_less nat_le_iff_add trans_less_add1 unat_of_nat_len word_arith_nat_add)
  by (metis nat_add_left_cancel_less nat_le_iff_add of_nat_add unat_eq_of_nat unat_lt2p)

lemma intvl_no_overflow_nat:
  assumes no_overflow: "unat a + b \<le> addr_card"
  shows "(x \<in> {(a :: addr_bitsize word) ..+ b}) = (unat a \<le> unat x \<and> unat x < (unat a + b))"
  using no_overflow unfolding addr_card_def using intvl_no_overflow_nat' by (metis card_word)

lemma intvl_no_overflow_nat_conv:
  assumes no_overflow: "unat a + b \<le> addr_card"
  shows "{(a :: addr_bitsize word) ..+ b} = {x. (unat a \<le> unat x \<and> unat x < (unat a + b))}"
  using intvl_no_overflow_nat [OF no_overflow] by blast

lemma zero_not_in_intvl_no_overflow:
  "0 \<notin> {a :: 'a::len word ..+ b} \<Longrightarrow> unat a + b \<le> 2 ^ len_of TYPE('a)"
  apply (rule ccontr)
  apply (simp add: intvl_def not_le)
  apply (drule_tac x="2 ^ len_of TYPE('a) - unat a" in spec)
  apply (clarsimp simp: not_less)
  by (smt (verit) Nat.le_diff_conv2 add.commute add.left_neutral add_uminus_conv_diff 
       cancel_comm_monoid_add_class.diff_cancel diff_zero linorder_not_less 
        nat_less_le of_nat_numeral semiring_1_class.of_nat_power unat_0 
        unat_lt2p unat_minus' word_arith_nat_add word_exp_length_eq_0)

lemma root_ptr_valid_last_byte_no_overflow:
  "root_ptr_valid htd (p :: ('a :: c_type) ptr)
      \<Longrightarrow> unat (ptr_val p) + size_of TYPE('a) \<le> 2 ^ len_of TYPE(addr_bitsize)"
  by (metis c_guard_def c_null_guard_def root_ptr_valid_def
        zero_not_in_intvl_no_overflow)

lemma root_ptr_valid_retyps_stack':
  fixes p::"'a::mem_type ptr"
  assumes stack: "\<forall>a \<in> {ptr_val p ..+ n * size_of TYPE('a)}. root_ptr_valid d (PTR (stack_byte) a)"
  assumes aligned: "ptr_aligned p"
  assumes i_bound: "i < n"
  shows "root_ptr_valid (fold (\<lambda>i. ptr_retyp (p +\<^sub>p int i)) [0..<n] d) (p +\<^sub>p int i)"
  using stack i_bound 
proof (induct n arbitrary: d)
  case 0
  then show ?case by simp
next
  case (Suc n)

  have stack: "\<forall>a\<in>{ptr_val p..+ Suc n * size_of TYPE('a)}. root_ptr_valid d (PTR(stack_byte) a)" by fact
  from stack have stack_n: "\<forall>a\<in>{ptr_val p..+ n * size_of TYPE('a)}. root_ptr_valid d (PTR(stack_byte) a)" 
    by (metis add.commute intvlD intvlI mult_Suc trans_less_add1)
  from stack
  have stack_Suc: "\<forall>a \<in> ptr_span (p +\<^sub>p int n). root_ptr_valid d (PTR(stack_byte) a)" 
    apply (clarsimp simp add: intvl_def ptr_add_def)
    by (metis (no_types, opaque_lifting) add.assoc add.commute add_less_cancel_right 
        of_nat_add of_nat_mult)

  from stack have no_overflow: "0 \<notin> {ptr_val p..+ Suc n * size_of TYPE('a)}"
    apply (clarsimp simp add: intvl_def)
    by (metis c_guard_NULL_simp root_ptr_valid_def)

  from stack have no_overflow': "\<forall>a \<in> {ptr_val p..+ Suc n * size_of TYPE('a)}. 0 \<notin> ptr_span (PTR(stack_byte) a)"
    apply (clarsimp simp add: intvl_def)
    by (metis c_guard_NULL_simp root_ptr_valid_def)

  have i_bound: "i < Suc n" by fact

  have fold_split: "(fold (\<lambda>i. ptr_retyp (p +\<^sub>p int i)) ([0..<Suc n]) d) = 
        (fold (\<lambda>i. ptr_retyp (p +\<^sub>p int i)) ([0..<n] @ [n]) d)"
    apply (simp only: Many_More.split_upt_on_n [where n=n])
    apply simp
    done

  have sz_a: "0 < size_of (TYPE('a))"
    by simp
  hence sz_bound: "size_of TYPE(stack_byte) \<le> size_of TYPE('a)"
    using size_of_stack_byte(1) by linarith

  from stack 
  have bound3: "unat (ptr_val p) + n * size_of (TYPE('a)) < addr_card"
    by (smt (verit, ccfv_SIG) add.commute add.left_neutral add_less_cancel_right c_guard_NULL_simp len_of_addr_card less_le mult.commute mult_Suc_right not_less root_ptr_valid_def stack_n sz_a zero_not_in_intvl_no_overflow)
  from bound3 have unat_dist1: "unat (ptr_val (p +\<^sub>p int n)) = unat (ptr_val p) + n * size_of (TYPE('a)) "
    by (smt (verit, ccfv_threshold) Abs_fnat_hom_add Abs_fnat_hom_mult CTypesDefs.ptr_add_def len_of_addr_card 
          of_int_of_nat_eq of_nat_inverse ptr_val.ptr_val_def word_unat.Rep_inverse')
  show ?case
  proof (cases "i=n")
    case True
    show ?thesis
      apply (simp only: fold_split)
      apply (simp only: fold_append)
      apply (simp add: True)
      apply (rule root_ptr_valid_retyp_stack')
      subgoal
        apply clarify
        apply (rule root_ptr_valid_domain)
         apply (rule stack_Suc [rule_format])
         apply assumption
        apply (rule fold_ptr_retyp_other)
        apply (subst (asm) intvl_no_overflow_nat_conv)
        subgoal
          apply (simp add: unat_dist1)
          using bound3
          by (metis c_guard_NULL_simp len_of_addr_card root_ptr_valid_def stack_Suc unat_dist1 zero_not_in_intvl_no_overflow)
        apply (subst (asm) intvl_no_overflow_nat_conv)
        subgoal
          apply simp
          using bound3
          by (metis Suc_leI len_of_addr_card unat_lt2p)
        apply (subst intvl_no_overflow_nat_conv)
        subgoal 
          using bound3
          by (simp add: mult.commute)
        subgoal using bound3 by (simp add: mult.commute unat_dist1)
        done
      subgoal 
        using aligned ptr_aligned_plus by blast
      done
  next
    case False
    with i_bound have i_bound_n: "i < n" by simp
    from no_overflow have bound1: "unat (ptr_val p + word_of_nat n * word_of_nat (size_of TYPE('a))) < addr_card"
      by (metis len_of_addr_card unsigned_less)
    from Suc.hyps [OF stack_n i_bound_n] 
    have hyp: "root_ptr_valid (fold (\<lambda>i. ptr_retyp (p +\<^sub>p int i)) [0..<n] d) (p +\<^sub>p int i)" .
    from bound3 i_bound_n have unat_dist2: "unat (ptr_val (p +\<^sub>p int i)) = unat (ptr_val p) + i * size_of (TYPE('a)) "
      by (smt (verit, ccfv_threshold) Abs_fnat_hom_add Abs_fnat_hom_mult CTypesDefs.ptr_add_def add.commute 
          add_less_cancel_right len_of_addr_card mult_strict_right_mono nat_less_le of_int_of_nat_eq of_nat_inverse 
          order_less_le_trans ptr_val.ptr_val_def sz_nzero word_unat.Rep_inverse')
    show ?thesis 
      apply (simp only: fold_split)
      apply (simp only: fold_append)
      apply (simp)
      apply (rule root_ptr_valid_domain)
       apply (rule hyp)
      apply (rule ptr_retyp_d)

      apply (subst intvl_no_overflow_nat_conv)
      subgoal
        using bound1
        by (metis c_guard_NULL_simp len_of_addr_card root_ptr_valid_def stack_Suc zero_not_in_intvl_no_overflow)
      subgoal for a
        apply (subst (asm) intvl_no_overflow_nat_conv)
        subgoal using bound3 i_bound_n
          apply (simp add: ptr_add_def)
          by (metis (no_types, lifting) CTypesDefs.ptr_add_def hyp len_of_addr_card of_int_of_nat_eq 
              ptr_val.ptr_val_def root_ptr_valid_last_byte_no_overflow)
        subgoal using i_bound_n
          by (auto simp add: unat_dist1 unat_dist2 dest!: le_less_trans)
            (metis add.commute le_def less_le_mult_nat mem_type_class.mem_type_simps(3))
        done
      done
  qed  
qed

lemma root_ptr_valid_retyps_stack:
  fixes p::"'a::mem_type ptr"
  assumes stack: "\<forall>a \<in> {ptr_val p ..+ n * size_of TYPE('a)}. root_ptr_valid d (PTR (stack_byte) a)"
  assumes aligned: "ptr_aligned p"
  assumes i_bound: "i < n"
  shows "root_ptr_valid (fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) [0..<n] d) (p +\<^sub>p int i)"
  using stack i_bound 
proof (induct n arbitrary: d)
  case 0
  then show ?case by simp
next
  case (Suc n)

  have stack: "\<forall>a\<in>{ptr_val p..+ Suc n * size_of TYPE('a)}. root_ptr_valid d (PTR(stack_byte) a)" by fact
  from stack have stack_n: "\<forall>a\<in>{ptr_val p..+ n * size_of TYPE('a)}. root_ptr_valid d (PTR(stack_byte) a)" 
    by (metis add.commute intvlD intvlI mult_Suc trans_less_add1)
  from stack
  have stack_Suc: "\<forall>a \<in> ptr_span (p +\<^sub>p int n). root_ptr_valid d (PTR(stack_byte) a)" 
    apply (clarsimp simp add: intvl_def ptr_add_def)
    by (metis (no_types, opaque_lifting) add.assoc add.commute add_less_cancel_right 
        of_nat_add of_nat_mult)

  from stack have no_overflow: "0 \<notin> {ptr_val p..+ Suc n * size_of TYPE('a)}"
    apply (clarsimp simp add: intvl_def)
    by (metis c_guard_NULL_simp root_ptr_valid_def)

  from stack have no_overflow': "\<forall>a \<in> {ptr_val p..+ Suc n * size_of TYPE('a)}. 0 \<notin> ptr_span (PTR(stack_byte) a)"
    apply (clarsimp simp add: intvl_def)
    by (metis c_guard_NULL_simp root_ptr_valid_def)

  have i_bound: "i < Suc n" by fact

  have fold_split: "(fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) ([0..<Suc n]) d) = 
        (fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) ([0..<n] @ [n]) d)"
    apply (simp only: Many_More.split_upt_on_n [where n=n])
    apply simp
    done

  have sz_a: "0 < size_of (TYPE('a))"
    by simp
  hence sz_bound: "size_of TYPE(stack_byte) \<le> size_of TYPE('a)"
    using size_of_stack_byte(1) by linarith

  from stack 
  have bound3: "unat (ptr_val p) + n * size_of (TYPE('a)) < addr_card"
    by (smt (verit, ccfv_SIG) add.commute add.left_neutral add_less_cancel_right c_guard_NULL_simp len_of_addr_card less_le mult.commute mult_Suc_right not_less root_ptr_valid_def stack_n sz_a zero_not_in_intvl_no_overflow)
  from bound3 have unat_dist1: "unat (ptr_val (p +\<^sub>p int n)) = unat (ptr_val p) + n * size_of (TYPE('a)) "
    by (smt (verit, ccfv_threshold) Abs_fnat_hom_add Abs_fnat_hom_mult CTypesDefs.ptr_add_def len_of_addr_card 
          of_int_of_nat_eq of_nat_inverse ptr_val.ptr_val_def word_unat.Rep_inverse')
  show ?case
  proof (cases "i=n")
    case True
    show ?thesis
      apply (simp only: fold_split)
      apply (simp only: fold_append)
      apply (simp add: True)
      apply (rule root_ptr_valid_retyp_stack)
      subgoal
        apply clarify
        apply (rule root_ptr_valid_domain)
         apply (rule stack_Suc [rule_format])
         apply assumption
        apply (rule fold_ptr_force_type_other)
        apply (subst (asm) intvl_no_overflow_nat_conv)
        subgoal
          apply (simp add: unat_dist1)
          using bound3
          by (metis c_guard_NULL_simp len_of_addr_card root_ptr_valid_def stack_Suc unat_dist1 zero_not_in_intvl_no_overflow)
        apply (subst (asm) intvl_no_overflow_nat_conv)
        subgoal
          apply simp
          using bound3
          by (metis Suc_leI len_of_addr_card unat_lt2p)
        apply (subst intvl_no_overflow_nat_conv)
        subgoal 
          using bound3
          by (simp add: mult.commute)
        subgoal using bound3 by (simp add: mult.commute unat_dist1)
        done
      subgoal 
        using aligned ptr_aligned_plus by blast
      done
  next
    case False
    with i_bound have i_bound_n: "i < n" by simp
    from no_overflow have bound1: "unat (ptr_val p + word_of_nat n * word_of_nat (size_of TYPE('a))) < addr_card"
      by (metis len_of_addr_card unsigned_less)
    from Suc.hyps [OF stack_n i_bound_n] 
    have hyp: "root_ptr_valid (fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) [0..<n] d) (p +\<^sub>p int i)" .
    from bound3 i_bound_n have unat_dist2: "unat (ptr_val (p +\<^sub>p int i)) = unat (ptr_val p) + i * size_of (TYPE('a)) "
      by (smt (verit, ccfv_threshold) Abs_fnat_hom_add Abs_fnat_hom_mult CTypesDefs.ptr_add_def add.commute 
          add_less_cancel_right len_of_addr_card mult_strict_right_mono nat_less_le of_int_of_nat_eq of_nat_inverse 
          order_less_le_trans ptr_val.ptr_val_def sz_nzero word_unat.Rep_inverse')
    show ?thesis 
      apply (simp only: fold_split)
      apply (simp only: fold_append)
      apply (simp)
      apply (rule root_ptr_valid_domain)
       apply (rule hyp)
      apply (rule ptr_force_type_d)

      apply (subst intvl_no_overflow_nat_conv)
      subgoal
        using bound1
        by (metis c_guard_NULL_simp len_of_addr_card root_ptr_valid_def stack_Suc zero_not_in_intvl_no_overflow)
      subgoal for a
        apply (subst (asm) intvl_no_overflow_nat_conv)
        subgoal using bound3 i_bound_n
          apply (simp add: ptr_add_def)
          by (metis (no_types, lifting) CTypesDefs.ptr_add_def hyp len_of_addr_card of_int_of_nat_eq 
              ptr_val.ptr_val_def root_ptr_valid_last_byte_no_overflow)
        subgoal using i_bound_n
          by (auto simp add: unat_dist1 unat_dist2 dest!: le_less_trans)
            (metis add.commute le_def less_le_mult_nat mem_type_class.mem_type_simps(3))
        done
      done
  qed  
qed

definition stack_free :: "heap_typ_desc \<Rightarrow> addr set" where
"stack_free d = {a. root_ptr_valid d (PTR (stack_byte) a)}"

lemma stack_alloc_cases [consumes 1]:
  fixes p::"'a::mem_type ptr"
  assumes stack_alloc: "(p, d') \<in> stack_alloc \<S> T d" 
  assumes dest:
    "\<lbrakk>typ_uinfo_t (TYPE('a)) \<noteq> typ_uinfo_t (TYPE(stack_byte));
      ptr_span p \<subseteq> \<S>;
      \<forall>a \<in> ptr_span p. root_ptr_valid d (PTR (stack_byte) a);
      ptr_aligned p; c_guard p; root_ptr_valid d' p;
      d' = ptr_force_type p d\<rbrakk> \<Longrightarrow> P"
  shows P
  using dest root_ptr_valid_retyp_stack stack_alloc root_ptr_valid_c_guard
  by (auto simp add: stack_alloc_def)

lemma stack_allocs_cases [consumes 1]:
  fixes p::"'a::mem_type ptr"
  assumes stack_alloc: "(p, d') \<in> stack_allocs n \<S> T d" 
  assumes dest:
    "\<lbrakk>0 < n; 0 \<notin> {ptr_val p ..+ n * size_of TYPE('a)}; unat (ptr_val p) + n * size_of TYPE('a) \<le> addr_card;
     typ_uinfo_t (TYPE('a)) \<noteq> typ_uinfo_t (TYPE(stack_byte));
      \<forall>i < n. ptr_span (p +\<^sub>p int i) \<subseteq> \<S>;
      \<forall>a \<in> {ptr_val p ..+ n * size_of TYPE('a)}. root_ptr_valid d (PTR (stack_byte) a);
      {ptr_val p ..+ n * size_of TYPE('a)} \<subseteq> stack_free d;
      ptr_aligned p; c_guard p; root_ptr_valid d' p;
      \<forall>i < n. ptr_aligned (p +\<^sub>p int i); \<forall>i < n. c_guard (p +\<^sub>p int i); \<forall>i < n. root_ptr_valid d' (p +\<^sub>p int i);
      d' = fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) [0..<n] d\<rbrakk> \<Longrightarrow> P"
  shows P
proof -
  from stack_alloc obtain
    bound: "0 < n" and
    \<S>: "(\<forall>i < n. ptr_span (p +\<^sub>p int i) \<subseteq> \<S>)" and
    non_stack_byte: "typ_uinfo_t (TYPE('a)) \<noteq> typ_uinfo_t (TYPE(stack_byte))" and
    valid_stack_byte: "\<forall>a \<in> {ptr_val p ..+ n * size_of TYPE('a)} . root_ptr_valid d (PTR (stack_byte) a)" and
    stack_free: "{ptr_val p ..+ n * size_of TYPE('a)} \<subseteq> stack_free d" and
    aligned_p: "ptr_aligned p" and
    d': "d' = fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) [0..<n] d"
    by (auto simp add: stack_allocs_def stack_free_def)
  from valid_stack_byte have no_overflow: "0 \<notin> {ptr_val p ..+ n * size_of TYPE('a)}"
    using c_guard_NULL_simp root_ptr_valid_c_guard by blast
  hence no_overflow': "unat (ptr_val p) + n * size_of TYPE('a) \<le> addr_card"
    by (metis len_of_addr_card zero_not_in_intvl_no_overflow)
  note valid_retyps = root_ptr_valid_retyps_stack [OF valid_stack_byte aligned_p]
  show ?thesis
    apply (rule dest)
                 apply (rule bound)
                apply (rule no_overflow)
               apply (rule no_overflow')
              apply (rule non_stack_byte)
             apply (rule \<S>)
            apply (rule valid_stack_byte)
           apply (rule stack_free)
          apply (rule aligned_p)
    subgoal using valid_retyps [OF bound] root_ptr_valid_c_guard d'
      by auto
    subgoal using valid_retyps [OF bound] d'
      by auto
    subgoal using aligned_p
      by (auto simp add: ptr_aligned_plus)
    subgoal using valid_retyps root_ptr_valid_c_guard d'
      by auto
    subgoal using valid_retyps d'
      by auto
    apply (rule d')
    done
qed

lemma stack_allocs_no_overflow: 
  assumes stack_alloc: "(p, d') \<in> stack_allocs n \<S> (TYPE('a::mem_type)) d"
  shows "unat (ptr_val p) + n * size_of TYPE('a) \<le> addr_card"
  using stack_allocs_cases [OF stack_alloc] .

lemma stack_alloc_ptr_force_type: "(p, d') \<in> stack_alloc \<S> T d \<Longrightarrow> 
  d' = ptr_force_type p d"
  by (auto simp add: stack_alloc_def)

lemma stack_allocs_ptr_force_type: "(p, d') \<in> stack_allocs n \<S> T d \<Longrightarrow> 
  d' =  fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) [0..<n] d  "
  by (auto simp add: stack_allocs_def)

lemma stack_allocs_no_stack_byte: "(p::'a::mem_type ptr, d') \<in> stack_allocs n \<S> T d 
  \<Longrightarrow> typ_uinfo_t (TYPE('a)) \<noteq> typ_uinfo_t (TYPE(stack_byte))"
  by (erule stack_allocs_cases)

lemma stack_allocs_\<S>: "(p::'a::mem_type ptr, d') \<in> stack_allocs n \<S> T d \<Longrightarrow> i < n 
  \<Longrightarrow> ptr_span (p +\<^sub>p int i) \<subseteq> \<S>"
  by (erule stack_allocs_cases) auto

lemma ptr_retyp_split: "ptr_retyp (p::'a::mem_type ptr) d a = 
  (if a \<in> ptr_span p then 
     (True, snd (d a) ++ list_map (typ_slice_t (typ_uinfo_t TYPE('a)) (unat (a - ptr_val p)))) 
   else d a)"
  by (auto simp add: ptr_retyp_d ptr_retyp_footprint)

lemma (in mem_type) ptr_force_type_footprint:
  "x \<in> {ptr_val p..+size_of TYPE('a)} \<Longrightarrow>
      ptr_force_type (p::'a ptr) d x =
        (True,list_map (typ_slice_t (typ_uinfo_t TYPE('a)) (unat (x - ptr_val p))))"
  apply(clarsimp simp: ptr_force_type_def)
  by (metis add_diff_cancel_left' htd_upd_at intvlD less_imp_le local.lt_size_of_unat_simps 
      local.max_size local.typ_slices_index local.typ_slices_length word_unat.Rep_inverse)

lemma ptr_force_type_split: "ptr_force_type (p::'a::mem_type ptr) d a = 
  (if a \<in> ptr_span p then 
     (True, list_map (typ_slice_t (typ_uinfo_t TYPE('a)) (unat (a - ptr_val p)))) 
   else d a)"
  by (auto simp add: ptr_force_type_d ptr_force_type_footprint)

lemma in_intvl_Suc: "x \<in> {x..+Suc n}" 
  by (simp add: intvl_self)

definition zero_heap:: "heap_mem" where
  "zero_heap = (\<lambda>a. zero_class.zero)"

definition stack_byte_typing::"heap_typ_desc" where
   "stack_byte_typing = (\<lambda>a. ptr_force_type (PTR(stack_byte) a) empty_htd a)"

definition stack_release:: "'a::mem_type ptr \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc" where 
"stack_release p d = override_on d stack_byte_typing (ptr_span p)"

definition stack_releases:: "nat \<Rightarrow> 'a::mem_type ptr \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc" where 
"stack_releases n p d = override_on d stack_byte_typing {ptr_val p ..+ n * size_of TYPE('a)}"

lemma stack_release_stack_releases_conv: "stack_release = stack_releases 1"
  by (auto simp add: stack_release_def stack_releases_def fun_eq_iff)

lemma stack_releases_0 [simp]: "stack_releases 0 d = id"
  by (rule ext) (auto simp add: stack_releases_def)


lemma stack_release_stack_alloc_inverse: "(p, d') \<in> stack_alloc \<S> T d \<Longrightarrow> stack_release p d' = d"
  apply (rule ext)
  subgoal for x
    apply (clarsimp simp add: stack_alloc_def stack_release_def stack_byte_typing_def )
    apply (cases "x \<in> ptr_span p")
     apply (simp add: root_ptr_valid_def)
     apply (subst ptr_force_type_footprint)
      apply (simp add: in_intvl_Suc)
     apply (simp add: prod.expand valid_root_footprint_def)
    apply (simp add: ptr_force_type_d)
    done
  done

lemma stack_releases_stack_allocs_inverse: "(p, d') \<in> stack_allocs n \<S> T d \<Longrightarrow> stack_releases n p d' = d"
  apply (rule ext)
  subgoal for x
    apply (clarsimp simp add: stack_allocs_def stack_releases_def stack_byte_typing_def )
    apply (cases "x \<in> {ptr_val p ..+ n * size_of TYPE('a)}")
     apply (simp add: root_ptr_valid_def)
     apply (subst ptr_force_type_footprint)
      apply (simp add: in_intvl_Suc)
     apply (simp add: prod.expand valid_root_footprint_def)
    apply (simp add: fold_ptr_force_type_other)
    done
  done

lemma sub_typ_stack_byte: 
  "TYPE('b::c_type) \<le>\<^sub>\<tau> TYPE(stack_byte) \<Longrightarrow> typ_uinfo_t TYPE('b) = typ_uinfo_t TYPE(stack_byte)"
  by (simp add: sub_typ_def typ_uinfo_t_def typ_info_stack_byte typ_tag_le_def)


lemma root_ptr_valid_not_subtype_disjoint:
  "\<lbrakk> root_ptr_valid d (p::'a::mem_type ptr);
     d \<Turnstile>\<^sub>t (q::'b::mem_type ptr);
     \<not> TYPE('b) \<le>\<^sub>\<tau> TYPE('a) \<rbrakk> \<Longrightarrow>
   ptr_span p \<inter> ptr_span q = {}"
  by (metis h_t_valid_def root_ptr_valid_def size_of_tag sub_typ_def valid_root_footprint_overlap_sub_typ)

lemma stack_alloc_disjoint:
  fixes q::"'b::mem_type ptr"
  assumes stack_alloc: "(p, d') \<in> stack_alloc \<S> (TYPE('a::mem_type)) d"
  assumes no_stack: "typ_uinfo_t (TYPE('b)) \<noteq> typ_uinfo_t (TYPE(stack_byte))"
  assumes typed: "d \<Turnstile>\<^sub>t q"
  shows "ptr_span p \<inter> ptr_span q = {}"
proof -
  from stack_alloc obtain
    "typ_uinfo_t (TYPE('a)) \<noteq> typ_uinfo_t (TYPE(stack_byte))" and
    stack_bytes: "\<forall>a \<in> ptr_span p. root_ptr_valid d (PTR (stack_byte) a)" 
    by (cases rule: stack_alloc_cases) auto
  from no_stack have no_sub_typ: "\<not> TYPE('b) \<le>\<^sub>\<tau> TYPE(stack_byte)" by (metis sub_typ_stack_byte)
  {
    fix a
    assume a: "a \<in> ptr_span p"
    have "a \<notin> ptr_span q"
    proof - 
      from stack_bytes [rule_format, OF a] have "root_ptr_valid d (PTR (stack_byte) a)" .
      from root_ptr_valid_not_subtype_disjoint [OF this typed no_sub_typ] show ?thesis
        by (simp add: disjoint_iff first_in_intvl)
    qed
  }
  then show "ptr_span p \<inter> ptr_span q = {}"
    by auto
qed

lemma stack_allocs_disjoint:
  fixes q::"'b::mem_type ptr"
  assumes stack_alloc: "(p, d') \<in> stack_allocs n \<S> (TYPE('a::mem_type)) d"
  assumes no_stack: "typ_uinfo_t (TYPE('b)) \<noteq> typ_uinfo_t (TYPE(stack_byte))"
  assumes typed: "d \<Turnstile>\<^sub>t q"
  shows "{ptr_val p ..+ n * size_of TYPE('a)} \<inter> ptr_span q = {}"
proof -
  from stack_alloc obtain
    "typ_uinfo_t (TYPE('a)) \<noteq> typ_uinfo_t (TYPE(stack_byte))" and
    stack_bytes: "\<forall>a \<in> {ptr_val p ..+ n * size_of TYPE('a)}. root_ptr_valid d (PTR (stack_byte) a)" 
    by (cases rule: stack_allocs_cases) auto
  from no_stack have no_sub_typ: "\<not> TYPE('b) \<le>\<^sub>\<tau> TYPE(stack_byte)" by (metis sub_typ_stack_byte)
  {
    fix a
    assume a: "a \<in> {ptr_val p ..+ n * size_of TYPE('a)}"
    have "a \<notin> ptr_span q"
    proof - 
      from stack_bytes [rule_format, OF a] have "root_ptr_valid d (PTR (stack_byte) a)" .
      from root_ptr_valid_not_subtype_disjoint [OF this typed no_sub_typ] show ?thesis
        by (simp add: disjoint_iff first_in_intvl)
    qed
  }
  then show "{ptr_val p ..+ n * size_of TYPE('a)} \<inter> ptr_span q = {}"
    by auto
qed



lemma stack_allocs_contained:
  assumes stack_alloc: "(p, d') \<in> stack_allocs n \<S> (TYPE('a::mem_type)) d"
  assumes i: "i < n"
  shows "ptr_span (p +\<^sub>p int i) \<subseteq> {ptr_val p ..+ n * size_of TYPE('a)}"
  using i stack_allocs_no_overflow [OF stack_alloc]
  apply (clarsimp simp add: intvl_def ptr_add_def)
  by (metis (no_types, opaque_lifting) mult.commute nat_index_bound of_nat_add of_nat_mult)

lemma stack_allocs_disjoint':
  fixes q::"'b::mem_type ptr"
  assumes stack_alloc: "(p, d') \<in> stack_allocs n \<S> (TYPE('a::mem_type)) d"
  assumes no_stack: "typ_uinfo_t (TYPE('b)) \<noteq> typ_uinfo_t (TYPE(stack_byte))"
  assumes typed: "d \<Turnstile>\<^sub>t q"
  assumes i: "i < n"
  shows "ptr_span (p +\<^sub>p int i) \<inter> ptr_span q = {}"
  using stack_allocs_disjoint [OF stack_alloc no_stack typed] i stack_allocs_contained [OF stack_alloc]
  by blast

lemma ptr_retyp_valid_footprint_disjoint2:
  "\<lbrakk>valid_footprint (ptr_retyp (q::'b::mem_type ptr) d) p s; {p..+size_td s} \<inter> {ptr_val q..+size_of TYPE('b)} = {} \<rbrakk>
     \<Longrightarrow> valid_footprint d p s"
  apply(clarsimp simp: valid_footprint_def Let_def)
  apply (drule spec, drule (1) mp)
  apply(subgoal_tac "p + of_nat y \<in> {p..+size_td s}")
  apply (subst (asm) ptr_retyp_d)
    apply clarsimp
    apply fast
   apply (clarsimp simp add: ptr_retyp_d_eq_fst split: if_split_asm)
   apply fast
  apply (erule intvlI)
  done

lemma ptr_force_type_valid_footprint_disjoint2:
  "\<lbrakk>valid_footprint (ptr_force_type (q::'b::mem_type ptr) d) p s; {p..+size_td s} \<inter> {ptr_val q..+size_of TYPE('b)} = {} \<rbrakk>
     \<Longrightarrow> valid_footprint d p s"
  by (simp add: disjoint_iff intvlI ptr_force_type_d valid_footprint_def)

lemma ptr_span_no_overflow_split_last_disjoint:
  fixes p::"'a::mem_type ptr"
  assumes no_overflow: "0 \<notin> {ptr_val p..+Suc n * size_of TYPE('a)}"
  shows "ptr_span (p +\<^sub>p int n) \<inter> {ptr_val p..+n * size_of TYPE('a)} = {}"
proof -
  have sz_a: "0 < size_of (TYPE('a))"
    by simp
  from no_overflow sz_a
  have bound_Suc: "unat (ptr_val p) + Suc n * size_of (TYPE('a)) \<le> addr_card"
    by (metis len_of_addr_card zero_not_in_intvl_no_overflow)
  with sz_a
  have bound_n: "unat (ptr_val p) + n * size_of (TYPE('a)) < addr_card"
    by (metis lessI mult_less_cancel2 nat_add_left_cancel_less order_less_le_trans)
  show ?thesis
    apply (subst intvl_no_overflow_nat_conv)
    subgoal using bound_Suc 
      apply (simp add: ptr_add_def)
      by (smt (verit, best) Abs_fnat_hom_add Abs_fnat_hom_mult add.commute add.left_commute 
          bound_n len_of_addr_card mult.commute of_nat_inverse word_unat.Rep_inverse')
    apply (subst intvl_no_overflow_nat_conv)
    subgoal using bound_n by simp
    subgoal using bound_n bound_Suc 
      by auto (smt (verit) Abs_fnat_hom_add Abs_fnat_hom_mult CTypesDefs.ptr_add_def bound_n 
          len_of_addr_card mult_of_nat_commute not_le of_int_of_nat_eq ptr_val.ptr_val_def unat_of_nat_len word_unat.Rep_inverse')
    done
qed

lemma ptr_span_no_overflow_indexes_disjoint:
  fixes p::"'a::mem_type ptr"
  assumes no_overflow: "0 \<notin> {ptr_val p..+ n * size_of TYPE('a)}"
  assumes i: "i < n"
  assumes j: "j < n"
  assumes neq: "i \<noteq> j"
  shows "ptr_span (p +\<^sub>p int i) \<inter> ptr_span (p +\<^sub>p int j) = {}"
proof -
  have sz_a: "0 < size_of (TYPE('a))"
    by simp
  from no_overflow sz_a
  have bound_n: "unat (ptr_val p) + n * size_of (TYPE('a)) \<le> addr_card"
    by (metis len_of_addr_card zero_not_in_intvl_no_overflow)
  from bound_n i have bound_i: "unat (ptr_val p) + i * size_of (TYPE('a)) < addr_card"
    by (metis linorder_not_le mult_le_cancel2 nat_add_left_cancel_le order_less_le_trans sz_nzero)
  from bound_n j have bound_j: "unat (ptr_val p) + j * size_of (TYPE('a)) < addr_card"
    by (metis linorder_not_le mult_le_cancel2 nat_add_left_cancel_le order_less_le_trans sz_nzero)
  show ?thesis
    apply (subst intvl_no_overflow_nat_conv)
    subgoal using bound_i i bound_n
      apply (simp add: ptr_add_def)
      by (smt (verit, ccfv_SIG) len_of_addr_card less_le_mult mult_strict_right_mono 
          of_nat_add of_nat_inverse of_nat_le_iff of_nat_less_iff of_nat_mult word_unat.Rep_inverse)
    apply (subst intvl_no_overflow_nat_conv)
    subgoal using bound_j j bound_n
      apply (simp add: ptr_add_def)
      by (smt (verit, ccfv_SIG) len_of_addr_card less_le_mult mult_strict_right_mono 
          of_nat_add of_nat_inverse of_nat_le_iff of_nat_less_iff of_nat_mult word_unat.Rep_inverse)
    subgoal using bound_i bound_j i j neq
      by (auto simp add: ptr_add_def)
        (smt (verit, ccfv_SIG) len_of_addr_card less_le_mult mult_strict_right_mono 
          of_nat_add of_nat_eq_iff of_nat_inverse of_nat_less_iff of_nat_mult 
          order_le_less_trans word_unat.Rep_inverse)
    done
qed

lemma array_to_index_span: 
  assumes x_in: "x \<in> {ptr_val (p::'a::mem_type ptr)..+ n * size_of TYPE('a)}"
  shows "\<exists>i. i < n \<and> x \<in> ptr_span (p +\<^sub>p int i)"
  using x_in
  apply (clarsimp simp add: intvl_def ptr_add_def)
  subgoal for k
    apply (rule exI [where x="k div size_of TYPE('a)"]) 
    by (metis (no_types, opaque_lifting) less_mult_imp_div_less mod_div_decomp 
        mod_less_divisor of_nat_add of_nat_mult sz_nzero)
  done

lemma array_to_index_span_exact: 
  assumes x_in: "x \<in> {ptr_val (p::'a::mem_type ptr)..+ n * size_of TYPE('a)}"
  shows "x \<in> ptr_span (p +\<^sub>p int ((unat (x - ptr_val p)) div size_of TYPE('a)))"
  using x_in
  apply (clarsimp simp add: intvl_def ptr_add_def)
  by (metis (no_types, opaque_lifting) mod_div_decomp mod_less_divisor of_nat_add of_nat_mult 
      sz_nzero word_unat.Rep_inverse)

lemma array_index_span_conv: 
  "{ptr_val (p::'a::mem_type ptr)..+ n * size_of TYPE('a)} = (\<Union>i<n. ptr_span (p +\<^sub>p int i))"
  apply standard
  subgoal
    apply clarsimp
    using array_to_index_span by blast
  subgoal
    apply clarsimp
    by (smt (verit, del_insts) CTypesDefs.ptr_add_def add.assoc intvlD intvlI mult.commute 
        nat_index_bound of_int_of_nat_eq of_nat_add of_nat_mult ptr_val.ptr_val_def)
  done


lemma fold_ptr_retyp_footprint:
  fixes p::"'a::mem_type ptr"
  assumes no_overflow: "0 \<notin> {ptr_val p..+ n * size_of TYPE('a)}"
  assumes i: "i < n"
  assumes x: "x \<in> ptr_span (p +\<^sub>p int i)"
  shows "fold (\<lambda>i. ptr_retyp (p +\<^sub>p int i)) [0..<n] d x =
          (True, snd (d x) ++ list_map (typ_slice_t (typ_uinfo_t TYPE('a)) (unat (x - ptr_val (p +\<^sub>p int i)))))"
  using no_overflow i  
proof (induct n arbitrary: d )
  case 0
  then show ?case by simp
next
  case (Suc n)
  have no_overflow: "0 \<notin> {ptr_val p..+ Suc n * size_of TYPE('a)}" by fact
  hence no_overflow_n: "0 \<notin> {ptr_val p..+n * size_of TYPE('a)}" 
    by (meson intvl_start_le lessI mult_less_cancel2 order_less_le subsetD sz_nzero)
  from ptr_span_no_overflow_split_last_disjoint [OF no_overflow]
  have disj: "ptr_span (p +\<^sub>p int n) \<inter> {ptr_val p..+ n * size_of TYPE('a)} = {}" .
  have i: "i < Suc n" by fact
  show ?case
  proof (cases "i = n")
    case True
    with disj x have x_notin_n: "x \<notin> {ptr_val p..+ n * size_of TYPE('a)}" by auto
    from True x have x: "x \<in> ptr_span (p +\<^sub>p int n)" by simp
    show ?thesis 
      apply simp
      using x
      apply (simp add: ptr_retyp_split)
      apply (subst fold_ptr_retyp_other [OF x_notin_n])
      apply (simp add: True)
      done
  next
    case False
    with x ptr_span_no_overflow_indexes_disjoint [OF no_overflow i, of n]
    have x_notin_n: "x \<notin> ptr_span (p +\<^sub>p int n)" by blast
    from False i have "i < n" by simp
    note hyp = Suc.hyps [OF no_overflow_n this]
    show ?thesis 
      apply simp
      using x_notin_n
      apply (simp add: ptr_retyp_split)
      apply (simp add: hyp)
      done
  qed
qed

lemma ptr_retyp_idem: 
  "ptr_retyp p (ptr_retyp (p::'a::mem_type ptr) d) = ptr_retyp p d"
  apply (rule ext)
  apply (clarsimp simp add: ptr_retyp_split)
  by (metis (no_types, lifting) map_add_assoc map_add_dom_eq)

lemma fold_ptr_retyp_d_empty:
  fixes p::"'a::mem_type ptr"
  assumes no_overflow: "0 \<notin> {ptr_val p..+ n * size_of TYPE('a)}"
  assumes i: "i < n"
  assumes x: "x \<in> ptr_span (p +\<^sub>p int i)"
  shows "fold (\<lambda>i. ptr_retyp (p +\<^sub>p int i)) [0..<n] d x =
          (True, snd (d x) ++ snd (ptr_retyp (p +\<^sub>p int i) empty_htd x))"
  apply (simp add: fold_ptr_retyp_footprint [OF no_overflow i x])
  apply (simp add: ptr_retyp_footprint [OF x])
  done

lemma fold_ptr_retyp_eq_fst:
  assumes no_overflow: "0 \<notin> {ptr_val p..+ n * size_of TYPE('a)}"
  shows"fst (fold (\<lambda>i. ptr_retyp (p +\<^sub>p int i)) [0..<n] d x) =
          (if x \<in> {ptr_val (p::'a::mem_type ptr)..+ n * size_of TYPE('a)} then True else fst (d x))"
proof (cases "x \<in> {ptr_val (p::'a::mem_type ptr)..+ n * size_of TYPE('a)}")
  case True
  from array_to_index_span [OF True] 
  obtain i where i: "i < n" and x_in: "x \<in> ptr_span (p +\<^sub>p int i)"
    by blast

  from fold_ptr_retyp_footprint [OF no_overflow i x_in] True
  show ?thesis by simp
next
  case False
  from fold_ptr_retyp_other [OF False] False show ?thesis by simp
qed


lemma fold_ptr_retyp_valid_footprint_disjoint2:
  assumes no_overflow: "0 \<notin> {ptr_val q..+ n * size_of TYPE('b)}"
  shows "\<lbrakk>valid_footprint (fold (\<lambda>i. ptr_retyp ((q::'b::mem_type ptr) +\<^sub>p int i)) [0..<n] d) p s; 
     {p..+size_td s} \<inter> {ptr_val q ..+ n * size_of TYPE('b)} = {} \<rbrakk>
     \<Longrightarrow> valid_footprint d p s"
  apply(clarsimp simp: valid_footprint_def Let_def)
  apply (drule spec, drule (1) mp)
  apply(subgoal_tac "p + of_nat y \<in> {p..+size_td s}")
  apply (subst (asm) fold_ptr_retyp_other)
    apply clarsimp
    apply fast
   apply (clarsimp simp add: fold_ptr_retyp_eq_fst [OF no_overflow] split: if_split_asm)
   apply fast
  apply (erule intvlI)
  done


lemma ptr_retyp_disjoint2:
  "\<lbrakk>ptr_retyp (p::'a::mem_type ptr) d,g \<Turnstile>\<^sub>t q;
    ptr_span p \<inter> ptr_span q = {} \<rbrakk>
  \<Longrightarrow> d,g \<Turnstile>\<^sub>t (q::'b::mem_type ptr)"
apply(clarsimp simp: h_t_valid_def)
apply(erule ptr_retyp_valid_footprint_disjoint2)
apply(simp add: size_of_def)
apply fast
done

lemma fold_ptr_retyp_disjoint2:
  fixes p::"'a::mem_type ptr" 
  assumes no_overflow: "0 \<notin> {ptr_val p..+ n * size_of TYPE('a)}"
shows "\<lbrakk>fold (\<lambda>i. ptr_retyp (p +\<^sub>p int i)) [0..<n] d,g \<Turnstile>\<^sub>t q;
    {ptr_val p..+ n * size_of TYPE('a)} \<inter> ptr_span q= {} \<rbrakk>
  \<Longrightarrow> d,g \<Turnstile>\<^sub>t (q::'b::mem_type ptr)"
apply(clarsimp simp: h_t_valid_def)
apply(erule fold_ptr_retyp_valid_footprint_disjoint2 [OF no_overflow])
apply(simp add: size_of_def)
apply fast
done

lemma ptr_retyp_disjoint_iff:
  "{ptr_val p..+size_of TYPE('a)} \<inter> {ptr_val q..+size_of TYPE('b)} = {}
  \<Longrightarrow> ptr_retyp (p::'a::mem_type ptr) d,g \<Turnstile>\<^sub>t q = d,g \<Turnstile>\<^sub>t (q::'b::mem_type ptr)"
  apply standard
   apply (erule (1) ptr_retyp_disjoint2)
  apply (erule (1) ptr_retyp_disjoint)
  done

lemma (in mem_type) ptr_force_type_valid_footprint_disjoint:
  "\<lbrakk> valid_footprint d p s; {p..+size_td s} \<inter> {ptr_val q..+size_of TYPE('a)} = {} \<rbrakk>
     \<Longrightarrow> valid_footprint (ptr_force_type (q::'a ptr) d) p s"
  apply(clarsimp simp: valid_footprint_def Let_def)
  apply((subst ptr_force_type_d; clarsimp), fastforce intro: intvlI)+
  done

lemma ptr_force_type_disjoint:
  "\<lbrakk> d,g \<Turnstile>\<^sub>t (q::'b::mem_type ptr); {ptr_val p..+size_of TYPE('a)} \<inter>
      {ptr_val q..+size_of TYPE('b)} = {} \<rbrakk> \<Longrightarrow>
      ptr_force_type (p::'a::mem_type ptr) d,g \<Turnstile>\<^sub>t q"
  apply(clarsimp simp: h_t_valid_def)
  apply(erule ptr_force_type_valid_footprint_disjoint)
  apply(fastforce simp: size_of_def)
  done

lemma ptr_force_type_disjoint2:
  "\<lbrakk>ptr_force_type (p::'a::mem_type ptr) d,g \<Turnstile>\<^sub>t q;
    ptr_span p \<inter> ptr_span q = {} \<rbrakk>
  \<Longrightarrow> d,g \<Turnstile>\<^sub>t (q::'b::mem_type ptr)"
apply(clarsimp simp: h_t_valid_def)
apply(erule ptr_force_type_valid_footprint_disjoint2)
apply(simp add: size_of_def)
apply fast
done


lemma ptr_force_type_disjoint_iff:
  "{ptr_val p..+size_of TYPE('a)} \<inter> {ptr_val q..+size_of TYPE('b)} = {}
  \<Longrightarrow> ptr_force_type (p::'a::mem_type ptr) d,g \<Turnstile>\<^sub>t q = d,g \<Turnstile>\<^sub>t (q::'b::mem_type ptr)"
  apply standard
   apply (erule (1) ptr_force_type_disjoint2)
  apply (erule (1) ptr_force_type_disjoint)
  done

lemma fold_ptr_force_type_valid_footprint_disjoint2:
  assumes no_overflow: "0 \<notin> {ptr_val q..+ n * size_of TYPE('b)}"
  shows "\<lbrakk>valid_footprint (fold (\<lambda>i. ptr_force_type ((q::'b::mem_type ptr) +\<^sub>p int i)) [0..<n] d) p s; 
     {p..+size_td s} \<inter> {ptr_val q ..+ n * size_of TYPE('b)} = {} \<rbrakk>
     \<Longrightarrow> valid_footprint d p s"
  apply(clarsimp simp: valid_footprint_def Let_def)
  apply (drule spec, drule (1) mp)
  apply(subgoal_tac "p + of_nat y \<in> {p..+size_td s}")
  apply (subst (asm) fold_ptr_force_type_other)
    apply clarsimp
    apply fast
   apply (simp add: disjoint_iff fold_ptr_force_type_other)
  apply (erule intvlI)
  done

lemma fold_ptr_force_type_disjoint2:
  fixes p::"'a::mem_type ptr" 
  assumes no_overflow: "0 \<notin> {ptr_val p..+ n * size_of TYPE('a)}"
shows "\<lbrakk>fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) [0..<n] d,g \<Turnstile>\<^sub>t q;
    {ptr_val p..+ n * size_of TYPE('a)} \<inter> ptr_span q= {} \<rbrakk>
  \<Longrightarrow> d,g \<Turnstile>\<^sub>t (q::'b::mem_type ptr)"
apply(clarsimp simp: h_t_valid_def)
apply(erule fold_ptr_force_type_valid_footprint_disjoint2 [OF no_overflow])
apply(simp add: size_of_def)
apply fast
  done

lemma fold_ptr_retyp_valid_footprint_disjoint:
  "\<lbrakk> valid_footprint d p s; {p..+size_td s} \<inter> {ptr_val q ..+ n * size_of TYPE('b)} = {} \<rbrakk>
     \<Longrightarrow> valid_footprint (fold (\<lambda>i. ptr_retyp ((q::'b:: mem_type ptr) +\<^sub>p int i)) [0..<n] d) p s"
  apply(clarsimp simp: valid_footprint_def Let_def)
  apply((subst fold_ptr_retyp_other; clarsimp), fastforce intro: intvlI)+
  done

lemma fold_ptr_force_type_valid_footprint_disjoint:
  "\<lbrakk> valid_footprint d p s; {p..+size_td s} \<inter> {ptr_val q ..+ n * size_of TYPE('b)} = {} \<rbrakk>
     \<Longrightarrow> valid_footprint (fold (\<lambda>i. ptr_force_type ((q::'b:: mem_type ptr) +\<^sub>p int i)) [0..<n] d) p s"
  apply(clarsimp simp: valid_footprint_def Let_def)
  apply((subst fold_ptr_force_type_other; clarsimp), fastforce intro: intvlI)+
  done

lemma fold_ptr_retyp_disjoint:
  fixes p::"'a::mem_type ptr" 
  shows "\<lbrakk> d,g \<Turnstile>\<^sub>t (q::'b::mem_type ptr); {ptr_val p..+ n * size_of TYPE('a)} \<inter> ptr_span q = {} \<rbrakk> \<Longrightarrow>
          fold (\<lambda>i. ptr_retyp (p +\<^sub>p int i)) [0..<n] d,g \<Turnstile>\<^sub>t q"
  apply(clarsimp simp: h_t_valid_def)
  apply(erule fold_ptr_retyp_valid_footprint_disjoint)
  apply(fastforce simp: size_of_def)
  done

lemma fold_ptr_force_type_disjoint:
  fixes p::"'a::mem_type ptr" 
  shows "\<lbrakk> d,g \<Turnstile>\<^sub>t (q::'b::mem_type ptr); {ptr_val p..+ n * size_of TYPE('a)} \<inter> ptr_span q = {} \<rbrakk> \<Longrightarrow>
          fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) [0..<n] d,g \<Turnstile>\<^sub>t q"
  apply(clarsimp simp: h_t_valid_def)
  apply(erule fold_ptr_force_type_valid_footprint_disjoint)
  apply(fastforce simp: size_of_def)
  done

lemma fold_ptr_retyp_disjoint_iff:
  fixes p::"'a::mem_type ptr" 
  assumes no_overflow: "0 \<notin> {ptr_val p..+ n * size_of TYPE('a)}"
  shows "{ptr_val p..+ n * size_of TYPE('a)} \<inter> ptr_span q = {}
  \<Longrightarrow> fold (\<lambda>i. ptr_retyp (p +\<^sub>p int i)) [0..<n] d,g \<Turnstile>\<^sub>t q = d,g \<Turnstile>\<^sub>t (q::'b::mem_type ptr)"
  apply standard
   apply (erule (1) fold_ptr_retyp_disjoint2 [OF no_overflow])
  apply (erule (1) fold_ptr_retyp_disjoint)
  done

lemma fold_ptr_force_type_disjoint_iff:
  fixes p::"'a::mem_type ptr" 
  assumes no_overflow: "0 \<notin> {ptr_val p..+ n * size_of TYPE('a)}"
  shows "{ptr_val p..+ n * size_of TYPE('a)} \<inter> ptr_span q = {}
  \<Longrightarrow> fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) [0..<n] d,g \<Turnstile>\<^sub>t q = d,g \<Turnstile>\<^sub>t (q::'b::mem_type ptr)"
  apply standard
   apply (erule (1) fold_ptr_force_type_disjoint2 [OF no_overflow])
  apply (erule (1) fold_ptr_force_type_disjoint)
  done

lemma stack_alloc_preserves_typing:
  fixes q::"'b::mem_type ptr"
  assumes stack_alloc: "(p, d') \<in> stack_alloc \<S> (TYPE('a::mem_type)) d"
  assumes no_stack: "typ_uinfo_t (TYPE('b)) \<noteq> typ_uinfo_t (TYPE(stack_byte))"
  assumes typed: "d \<Turnstile>\<^sub>t q"
  shows "d' \<Turnstile>\<^sub>t q"
proof -
  from stack_alloc obtain
    d': "d' = ptr_force_type p d"
    by (cases rule: stack_alloc_cases) auto

  from stack_alloc_disjoint [OF stack_alloc no_stack typed]
  have "ptr_span p \<inter> ptr_span q = {}" .
  from ptr_force_type_disjoint_iff [OF this, where d=d and g=c_guard]  typed show ?thesis
    by (simp add: d')
qed

lemma stack_allocs_preserves_typing:
  fixes q::"'b::mem_type ptr"
  assumes stack_alloc: "(p, d') \<in> stack_allocs n \<S> (TYPE('a::mem_type)) d"
  assumes no_stack: "typ_uinfo_t (TYPE('b)) \<noteq> typ_uinfo_t (TYPE(stack_byte))"
  assumes typed: "d \<Turnstile>\<^sub>t q"
  shows "d' \<Turnstile>\<^sub>t q"
proof -
  from stack_alloc obtain
    d': "d' = fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) [0..<n] d" and
    no_overflow: "0 \<notin> {ptr_val p ..+ n * size_of TYPE('a)}"
    by (cases rule: stack_allocs_cases) auto

  from stack_allocs_disjoint [OF stack_alloc no_stack typed]
  have "{ptr_val p..+n * size_of TYPE('a)}  \<inter> ptr_span q = {}" .
  from fold_ptr_force_type_disjoint_iff [OF no_overflow this, where d=d and g=c_guard]  typed show ?thesis
    by (simp add: d')
qed

lemma h_t_valid_valid_footprint: "d,g \<Turnstile>\<^sub>t p \<Longrightarrow> valid_footprint d (ptr_val (p::'a::c_type ptr)) (typ_uinfo_t TYPE('a))"
  by (simp add: h_t_valid_def)

lemma stack_alloc_preserves_root_ptr_valid:
  fixes q::"'b::mem_type ptr"
  assumes stack_alloc: "(p, d') \<in> stack_alloc \<S> (TYPE('a::mem_type)) d"
  assumes no_stack: "typ_uinfo_t (TYPE('b)) \<noteq> typ_uinfo_t (TYPE(stack_byte))"
  assumes typed: "root_ptr_valid d q"
  shows "root_ptr_valid d' q"
proof -
  from stack_alloc obtain    
    d': "d' = ptr_force_type p d"
    by (cases rule: stack_alloc_cases) auto

  from typed have typed_q: "d \<Turnstile>\<^sub>t q"
    by (simp add: root_ptr_valid_h_t_valid)

  from stack_alloc_disjoint [OF stack_alloc no_stack this] 
  have disj: "ptr_span p \<inter> ptr_span q = {}" .
  from stack_alloc_preserves_typing [OF stack_alloc no_stack typed_q]
  have typed': "d' \<Turnstile>\<^sub>t q" .
  hence valid_fp: "valid_footprint d' (ptr_val q) (typ_uinfo_t TYPE('b))" 
    by (simp add: h_t_valid_valid_footprint)

  show ?thesis
    apply (simp add: root_ptr_valid_def valid_root_footprint_valid_footprint_dom_conv valid_fp 
        h_t_valid_c_guard [OF typed'])
    apply (simp add: d')
    by (metis (no_types, lifting) disj disjoint_iff intvlI ptr_force_type_d root_ptr_valid_def 
        size_of_def typ_uinfo_size typed valid_root_footprint_dom_typing)
qed

lemma stack_allocs_preserves_root_ptr_valid:
  fixes q::"'b::mem_type ptr"
  assumes stack_alloc: "(p, d') \<in> stack_allocs n \<S> (TYPE('a::mem_type)) d"
  assumes no_stack: "typ_uinfo_t (TYPE('b)) \<noteq> typ_uinfo_t (TYPE(stack_byte))"
  assumes typed: "root_ptr_valid d q"
  shows "root_ptr_valid d' q"
proof -
  from stack_alloc obtain    
    d': "d' = fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) [0..<n] d" and
    no_overflow: "0 \<notin> {ptr_val p ..+ n * size_of TYPE('a)}"
    by (cases rule: stack_allocs_cases) auto

  from typed have typed_q: "d \<Turnstile>\<^sub>t q"
    by (simp add: root_ptr_valid_h_t_valid)

  from stack_allocs_disjoint [OF stack_alloc no_stack this] 
  have disj: "{ptr_val p..+n * size_of TYPE('a)} \<inter> ptr_span q = {}" .
  from stack_allocs_preserves_typing [OF stack_alloc no_stack typed_q]
  have typed': "d' \<Turnstile>\<^sub>t q" .
  hence valid_fp: "valid_footprint d' (ptr_val q) (typ_uinfo_t TYPE('b))" 
    by (simp add: h_t_valid_valid_footprint)

  show ?thesis
    apply (simp add: root_ptr_valid_def valid_root_footprint_valid_footprint_dom_conv valid_fp 
        h_t_valid_c_guard [OF typed'])
    apply (simp add: d')
    using disj fold_ptr_force_type_other
    by (smt (verit) d' disjoint_iff dom_list_map root_ptr_valid_def s_footprintD 
        s_footprintI2 size_of_def stack_alloc stack_allocs_cases typ_uinfo_size typed valid_root_footprint_def)
qed

lemma stack_alloc_root_ptr_valid_new_cases:
  fixes q::"'b::mem_type ptr"
  assumes stack_alloc: "(p, d') \<in> stack_alloc \<S> (TYPE('a::mem_type)) d"
  assumes "root_ptr_valid d' q"
  shows "(ptr_val p = ptr_val q \<and> typ_uinfo_t (TYPE('b)) = typ_uinfo_t (TYPE('a))) \<or> root_ptr_valid d q"
  by (metis Ptr_ptr_val assms(2) ptr.inject root_ptr_valid_def stack_alloc stack_alloc_cases 
      valid_root_footprint_ptr_force_type_iff wf_size_desc_typ_uinfo_t_simp)

lemma valid_root_footprints_no_overlap:
  assumes "valid_root_footprint d a1 t1"
  assumes "valid_root_footprint d a2 t2"
  assumes "t1 \<noteq> t2"
  shows "{a1 ..+ size_td t1} \<inter> {a2 ..+ size_td t2} = {}"
  using assms(1) assms(2) assms(3) valid_root_footprint_type_neq_disjoint by presburger

lemma root_ptr_valid_neq_disjoint:
  "\<lbrakk> root_ptr_valid d (p::'a::c_type ptr);
     root_ptr_valid d (q::'b::c_type ptr);
     ptr_val p \<noteq> ptr_val q \<rbrakk> \<Longrightarrow>
   {ptr_val p..+size_of TYPE('a)} \<inter>
          {ptr_val q..+size_of TYPE('b)} = {}"
  apply (clarsimp simp only: size_of_tag [symmetric])
  by (metis boolean_algebra.conj_ac(2) h_t_valid_valid_footprint intvl_inter 
      order_antisym_conv root_ptr_valid_def root_ptr_valid_h_t_valid 
      valid_footprint_neq_nmem valid_root_footprint_overlap_sub_typ)

lemma root_ptr_valid_same_type_neq_disjoint: 
"root_ptr_valid d p \<Longrightarrow> root_ptr_valid d q \<Longrightarrow> p \<noteq> q = (ptr_span p \<inter> ptr_span q = {})"
  apply standard
   apply (simp add: root_ptr_valid_neq_disjoint)
  by (metis empty_iff inf.idem intvlI root_ptr_valid_def size_of_tag valid_root_footprint_def)

lemma cvalid_same_type_neq_disjoint: 
"d \<Turnstile>\<^sub>t p \<Longrightarrow> d \<Turnstile>\<^sub>t q \<Longrightarrow> p \<noteq> q = (ptr_span p \<inter> ptr_span q = {})"
  apply standard
  apply (simp add: h_t_valid_neq_disjoint peer_typ_not_field_of)
  by (metis disjoint_iff h_t_valid_valid_footprint intvl_self size_of_tag valid_footprint_def)

lemma root_ptr_valid_type_neq_disjoint:
  "\<lbrakk> root_ptr_valid d (p::'a::c_type ptr);
     root_ptr_valid d (q::'b::c_type ptr);
     typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b) \<rbrakk> \<Longrightarrow>
   {ptr_val p..+size_of TYPE('a)} \<inter>
          {ptr_val q..+size_of TYPE('b)} = {}"
  apply (subgoal_tac "ptr_val p \<noteq> ptr_val q")
   apply (rule root_ptr_valid_neq_disjoint, auto)[1]
  by (metis disjoint_iff intvlI root_ptr_valid_def sub_tag_antisym 
      valid_footprint_def valid_root_footprint_overlap_sub_typ 
      valid_root_footprint_valid_footprint_dom_conv)

lemma valid_root_footprints_cases:
  assumes "valid_root_footprint d a1 t1"
  assumes "valid_root_footprint d a2 t2"
  shows "(t1 = t2 \<and> a1 = a2) \<or> ({a1 ..+ size_td t1} \<inter> {a2 ..+ size_td t2} = {})"
  using assms valid_root_footprint_neq_disjoint valid_root_footprint_type_neq_disjoint by blast


lemma root_ptr_valid_cases:
  fixes p::"'a::mem_type ptr"
  fixes q:: "'b::mem_type ptr"
  assumes root_p: "root_ptr_valid d p" 
  assumes root_q: "root_ptr_valid d q"
  shows "(ptr_val p = ptr_val q \<and> typ_uinfo_t (TYPE('a)) = typ_uinfo_t (TYPE('b))) \<or>
        (ptr_span p \<inter> ptr_span q) = {}"
  using root_p root_ptr_valid_neq_disjoint root_ptr_valid_type_neq_disjoint root_q by blast

lemma root_ptr_valid_casesE [consumes 2]:
  fixes p::"'a::mem_type ptr"
  fixes q:: "'b::mem_type ptr"
  assumes root_p: "root_ptr_valid d p" 
  assumes root_q: "root_ptr_valid d q"
  assumes same: "(ptr_val q = ptr_val p \<and> typ_uinfo_t (TYPE('a)) = typ_uinfo_t (TYPE('b))) \<Longrightarrow> P"
  assumes disj: "ptr_span p \<inter> ptr_span q = {} \<Longrightarrow> P"
  shows "P"
  using root_ptr_valid_cases [OF root_p root_q] same disj by auto

lemma stack_allocs_root_ptr_valid_new_cases:
  fixes q::"'b::mem_type ptr"
  assumes stack_alloc: "(p, d') \<in> stack_allocs n \<S> (TYPE('a::mem_type)) d"
  assumes "root_ptr_valid d' q"
  shows "(\<exists>i<n. ptr_val q = ptr_val (p +\<^sub>p int i)  \<and> typ_uinfo_t (TYPE('b)) = typ_uinfo_t (TYPE('a))) \<or> root_ptr_valid d q"
proof (cases "{ptr_val p ..+ n * size_of TYPE('a)} \<inter> ptr_span q = {}")
  case True
  with stack_alloc show ?thesis 
    by (smt (verit, best) assms(2) disjoint_iff fold_ptr_force_type_other 
        root_ptr_valid_domain' stack_allocs_cases)
next
  case False
  with stack_alloc array_to_index_span  show ?thesis 
    by (smt (verit) assms(2) disjoint_iff root_ptr_valid_neq_disjoint 
        root_ptr_valid_type_neq_disjoint stack_allocs_cases)
qed

lemma stack_alloc_root_ptr_valid_same:
  fixes q::"'b::mem_type ptr"
  assumes stack_alloc: "(p, d') \<in> stack_alloc \<S> (TYPE('a::mem_type)) d"
  assumes addr_eq: "ptr_val p = ptr_val q"
  assumes match: "typ_uinfo_t (TYPE('b)) = typ_uinfo_t (TYPE('a))"
  shows "root_ptr_valid d' q"
proof (cases "root_ptr_valid d' q") 
  case True
  then show ?thesis by simp
next
  case False
  from stack_alloc have "root_ptr_valid d' p" by (rule stack_alloc_cases)
  with addr_eq match show ?thesis 
    apply (clarsimp simp add: root_ptr_valid_def )
    apply (simp add: c_guard_def c_null_guard_def ptr_aligned_def)
    apply (clarsimp simp add: align_of_def align_td_uinfo[symmetric] size_of_def  )
    by (metis typ_uinfo_size)
qed

lemma stack_allocs_root_ptr_valid_same:
  fixes q::"'b::mem_type ptr"
  assumes stack_alloc: "(p, d') \<in> stack_allocs n \<S> (TYPE('a::mem_type)) d"
  assumes i: "i < n"
  assumes addr_eq: "ptr_val q = ptr_val (p +\<^sub>p int i)"
  assumes match: "typ_uinfo_t (TYPE('b)) = typ_uinfo_t (TYPE('a))"
  shows "root_ptr_valid d' q"
proof (cases "root_ptr_valid d' q") 
  case True
  then show ?thesis by simp
next
  case False
  from stack_alloc have "root_ptr_valid d' (p +\<^sub>p int i)" 
    apply  (rule stack_allocs_cases) 
    using i
    by auto

  with addr_eq match show ?thesis 
    apply (clarsimp simp add: root_ptr_valid_def )
    apply (simp add: c_guard_def c_null_guard_def ptr_aligned_def)
    apply (clarsimp simp add: align_of_def align_td_uinfo[symmetric] size_of_def  )
    by (metis typ_uinfo_size)
qed

lemma stack_alloc_root_ptr_valid_other:
  fixes q::"'b::mem_type ptr"
  assumes stack_alloc: "(p, d') \<in> stack_alloc \<S> (TYPE('a::mem_type)) d"
  assumes valid_d: "root_ptr_valid d q"
  assumes non_stack: "typ_uinfo_t (TYPE('b)) \<noteq> typ_uinfo_t (TYPE(stack_byte))"
  shows "root_ptr_valid d' q"
proof (cases "root_ptr_valid d' q")
  case True
  then show ?thesis by simp
next
  case False
  from stack_alloc
  show ?thesis
    apply (rule stack_alloc_cases)
    using False valid_d non_stack
    using stack_alloc stack_alloc_preserves_root_ptr_valid by blast
qed

lemma stack_allocs_root_ptr_valid_other:
  fixes q::"'b::mem_type ptr"
  assumes stack_alloc: "(p, d') \<in> stack_allocs n \<S> (TYPE('a::mem_type)) d"
  assumes valid_d: "root_ptr_valid d q"
  assumes non_stack: "typ_uinfo_t (TYPE('b)) \<noteq> typ_uinfo_t (TYPE(stack_byte))"
  shows "root_ptr_valid d' q"
proof (cases "root_ptr_valid d' q")
  case True
  then show ?thesis by simp
next
  case False
  from stack_alloc
  show ?thesis
    apply (rule stack_allocs_cases)
    using False valid_d non_stack
    using stack_alloc stack_allocs_preserves_root_ptr_valid by blast
qed


lemma stack_alloc_root_ptr_valid_cases:
  fixes q::"'b::mem_type ptr"
  assumes stack_alloc: "(p, d') \<in> stack_alloc \<S> (TYPE('a::mem_type)) d"
  assumes non_stack_byte: "typ_uinfo_t (TYPE('b)) \<noteq> typ_uinfo_t (TYPE(stack_byte))"
  shows "root_ptr_valid d' q \<longleftrightarrow>
    (ptr_val p = ptr_val q \<and> typ_uinfo_t (TYPE('b)) = typ_uinfo_t (TYPE('a))) \<or> 
    root_ptr_valid d q
    "
  using stack_alloc non_stack_byte
    stack_alloc_root_ptr_valid_new_cases  stack_alloc_root_ptr_valid_other  stack_alloc_root_ptr_valid_same
  by blast

lemma stack_allocs_root_ptr_valid_cases:
  fixes q::"'b::mem_type ptr"
  assumes stack_alloc: "(p, d') \<in> stack_allocs n \<S> (TYPE('a::mem_type)) d"
  assumes non_stack_byte: "typ_uinfo_t (TYPE('b)) \<noteq> typ_uinfo_t (TYPE(stack_byte))"
  shows "root_ptr_valid d' q \<longleftrightarrow>
    (\<exists>i<n.  ptr_val q = ptr_val (p +\<^sub>p int i) \<and> typ_uinfo_t (TYPE('b)) = typ_uinfo_t (TYPE('a))) \<or> 
    root_ptr_valid d q
    "
  using stack_alloc non_stack_byte
    stack_allocs_root_ptr_valid_new_cases  stack_allocs_root_ptr_valid_other  stack_allocs_root_ptr_valid_same
  by metis


lemma stack_alloc_root_ptr_valid_same_type_cases:
  assumes stack_alloc: "(p, d') \<in> stack_alloc \<S> (TYPE('a::mem_type)) d"
  shows "root_ptr_valid d' q \<longleftrightarrow> p = q \<or> root_ptr_valid d q"
  by (metis ptr_val_inj stack_alloc stack_alloc_cases stack_alloc_root_ptr_valid_cases)

lemma stack_allocs_root_ptr_valid_same_type_cases:
  assumes stack_alloc: "(p, d') \<in> stack_allocs n \<S> (TYPE('a::mem_type)) d"
  shows "root_ptr_valid d' q \<longleftrightarrow> (\<exists>i<n. q = (p +\<^sub>p int i) \<or> root_ptr_valid d q)"
  using stack_alloc stack_allocs_cases stack_allocs_root_ptr_valid_cases
  by (metis ptr_val_inj)

lemma root_ptr_valid_valid_root_footprint: 
  "root_ptr_valid d (p::'a ptr) \<Longrightarrow> valid_root_footprint d (ptr_val p) (typ_uinfo_t TYPE('a::c_type))"
  by (simp add: root_ptr_valid_def)

definition 
  allocated_ptr:: "addr set \<Rightarrow> 'a::mem_type itself \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc \<Rightarrow> 'a ptr" where
  \<open>allocated_ptr \<S> T d d' = (THE p. (p, d') \<in> stack_alloc \<S> TYPE('a) d)\<close>

definition 
  allocated_ptrs:: "nat \<Rightarrow> addr set \<Rightarrow> 'a::mem_type itself \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc \<Rightarrow> 'a ptr" where
  \<open>allocated_ptrs n \<S> T d d' = (THE p. (p, d') \<in> stack_allocs n \<S> TYPE('a) d)\<close>

lemma allocated_ptr_allocated_ptrs_def: "allocated_ptr = allocated_ptrs 1"
  by (simp add: stack_alloc_stack_allocs_conv allocated_ptr_def allocated_ptrs_def fun_eq_iff)

abbreviation (input)
  cptr_type :: "('a :: c_type) ptr \<Rightarrow> 'a itself"
where
  "cptr_type p \<equiv> TYPE('a)"

lemma h_t_valid_guard_subst:
  "\<lbrakk> d,g \<Turnstile>\<^sub>t p; g' p \<rbrakk> \<Longrightarrow> d,g' \<Turnstile>\<^sub>t p"
 apply(simp add:h_t_valid_def)
  done

lemma h_t_valid_ptr_retyp_eq:
  "\<not> cptr_type p <\<^sub>\<tau> cptr_type p' \<Longrightarrow> h_t_valid (ptr_retyp p td) g p'
    = (if ptr_span (p::'a::mem_type ptr) \<inter> ptr_span (p'::'b::mem_type ptr) = {} then h_t_valid td g p'
        else field_of_t p' p \<and> g p')"
  apply (clarsimp simp: ptr_retyp_disjoint_iff split: if_split)
  apply (cases "g p'")
   apply (rule iffI)
    apply (rule ccontr, drule h_t_valid_neq_disjoint, rule ptr_retyp_h_t_valid, simp+)
    apply (simp add: Int_commute)
   apply (clarsimp simp: field_of_t_def field_of_def)
   apply (drule sub_h_t_valid[where p=p, rotated], rule ptr_retyp_h_t_valid, simp, simp)
   apply (erule(1) h_t_valid_guard_subst)
  apply (simp add: h_t_valid_def)
  done

lemma field_of_t_refl:
  "field_of_t p p' = (p = p')"
  apply (safe, simp_all add: field_of_t_def)
  apply (simp add: field_of_def)
  apply (drule td_set_size_lte)
  apply (simp add: unat_eq_0)
  done

lemma ptr_retyp_same_cleared_region:
  fixes p :: "'a :: mem_type ptr" and p' :: "'a :: mem_type ptr"
  assumes  ht: "ptr_retyp p td, g \<Turnstile>\<^sub>t p'"
  shows "p = p' \<or> {ptr_val p..+ size_of TYPE('a)} \<inter> {ptr_val p' ..+ size_of TYPE('a)} = {}"
  using ht
  by (simp add: h_t_valid_ptr_retyp_eq[where p=p and p'=p'] field_of_t_refl
         split: if_split_asm)

lemma (in mem_type) ptr_force_type_h_t_valid:
  "g p \<Longrightarrow> ptr_force_type p d,g \<Turnstile>\<^sub>t (p::'a ptr)"
  by (simp add: h_t_valid_def ptr_force_type_valid_footprint)

lemma h_t_valid_ptr_force_type_eq:
  "\<not> cptr_type p <\<^sub>\<tau> cptr_type p' \<Longrightarrow> h_t_valid (ptr_force_type p td) g p'
    = (if ptr_span (p::'a::mem_type ptr) \<inter> ptr_span (p'::'b::mem_type ptr) = {} then h_t_valid td g p'
        else field_of_t p' p \<and> g p')"
  apply (clarsimp simp: ptr_force_type_disjoint_iff split: if_split)
  apply (cases "g p'")
   apply (rule iffI)
    apply (rule ccontr, drule h_t_valid_neq_disjoint, rule ptr_force_type_h_t_valid, simp+)
    apply (simp add: Int_commute)
   apply (clarsimp simp: field_of_t_def field_of_def)
   apply (drule sub_h_t_valid[where p=p, rotated], rule ptr_force_type_h_t_valid, simp, simp)
   apply (erule(1) h_t_valid_guard_subst)
  apply (simp add: h_t_valid_def)
  done

lemma ptr_force_type_same_cleared_region:
  fixes p :: "'a :: mem_type ptr" and p' :: "'a :: mem_type ptr"
  assumes  ht: "ptr_force_type p td, g \<Turnstile>\<^sub>t p'"
  shows "p = p' \<or> {ptr_val p..+ size_of TYPE('a)} \<inter> {ptr_val p' ..+ size_of TYPE('a)} = {}"
  using ht
  by (simp add: h_t_valid_ptr_force_type_eq[where p=p and p'=p'] field_of_t_refl
         split: if_split_asm)

lemma stack_alloc_unique: 
  assumes p: "(p, d') \<in> stack_alloc \<S> (TYPE('a::mem_type)) d"  
  assumes q: "(q, d') \<in> stack_alloc \<S> (TYPE('a::mem_type)) d" 
  shows "p = q"
proof -
  from p obtain p_props:
    "typ_uinfo_t (TYPE('a)) \<noteq> typ_uinfo_t (TYPE(stack_byte))" 
    "\<forall>a \<in> ptr_span p. root_ptr_valid d (PTR (stack_byte) a)" 
    "ptr_aligned p" 
    "c_guard p" 
    "root_ptr_valid d' p" 
    "d' = ptr_force_type p d"
    by (cases rule: stack_alloc_cases) auto

  from q obtain q_props:
    "typ_uinfo_t (TYPE('a)) \<noteq> typ_uinfo_t (TYPE(stack_byte))" 
     "\<forall>a \<in> ptr_span q. root_ptr_valid d (PTR (stack_byte) a)" 
    "ptr_aligned q" 
    "c_guard q" 
    "root_ptr_valid d' q" and
    "d' = ptr_force_type q d"
    by (cases rule: stack_alloc_cases) auto

  show ?thesis
  proof (cases "ptr_val p = ptr_val q")
    case True
    then show ?thesis by simp
  next
    case False
    with p_props q_props show ?thesis
      by (metis disj_ptr_span_ptr_neq[unfolded disjnt_def] ptr_force_type_disjoint2
          ptr_force_type_same_cleared_region q root_ptr_valid_h_t_valid stack_alloc_disjoint)
  qed
qed

lemma stack_allocs_unique: 
  assumes p: "(p, d') \<in> stack_allocs n \<S> (TYPE('a::mem_type)) d"  
  assumes q: "(q, d') \<in> stack_allocs n \<S> (TYPE('a::mem_type)) d" 
  shows "p = q"
proof -
  from p obtain p_props:

    "0 \<notin> {ptr_val p ..+ n * size_of TYPE('a)}" 
    "typ_uinfo_t (TYPE('a)) \<noteq> typ_uinfo_t (TYPE(stack_byte))"
    "\<forall>a \<in> {ptr_val p ..+ n * size_of TYPE('a)}. root_ptr_valid d (PTR (stack_byte) a)"
    "ptr_aligned p" "c_guard p" "root_ptr_valid d' p"
    "d' = fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) [0..<n] d"
    by (cases rule: stack_allocs_cases) auto

  from q obtain q_props:
    "0 < n" 
    "0 \<notin> {ptr_val q ..+ n * size_of TYPE('a)}" 
    "typ_uinfo_t (TYPE('a)) \<noteq> typ_uinfo_t (TYPE(stack_byte))"
    "\<forall>a \<in> {ptr_val q ..+ n * size_of TYPE('a)}. root_ptr_valid d (PTR (stack_byte) a)"
    "ptr_aligned q" "c_guard q" "root_ptr_valid d' q"
    "d' = fold (\<lambda>i. ptr_force_type (q +\<^sub>p int i)) [0..<n] d"
    by (cases rule: stack_allocs_cases) auto



  show ?thesis
  proof (cases "ptr_val p = ptr_val q")
    case True
    then show ?thesis by simp
  next
    case False
    with p_props q_props show ?thesis
      using  disj_ptr_span_ptr_neq fold_ptr_retyp_disjoint2 ptr_force_type_same_cleared_region 
          q p root_ptr_valid_h_t_valid stack_allocs_disjoint
      by (smt (verit, ccfv_threshold) disjoint_iff fold_ptr_force_type_disjoint2 inf.idem 
          inf.order_iff intvl_inter intvl_no_overflow_nat len_of_addr_card mem_type_self 
          order_antisym_conv root_ptr_valid_cases stack_allocs_contained 
          stack_allocs_ptr_force_type zero_not_in_intvl_no_overflow)
  qed
qed

lemma stack_alloc_allocated_ptr: 
  "(p, d') \<in> stack_alloc \<S> TYPE('a) d \<Longrightarrow> allocated_ptr \<S> TYPE('a::mem_type) d d' = p"
  apply (simp add: allocated_ptr_def) 
  apply (rule theI2)
    apply (assumption)
   apply (erule (1) stack_alloc_unique)
  apply (erule (1) stack_alloc_unique)
  done

lemma stack_allocs_allocated_ptrs: 
  "(p, d') \<in> stack_allocs n \<S> TYPE('a) d \<Longrightarrow> allocated_ptrs n \<S> TYPE('a::mem_type) d d' = p"
  apply (simp add: allocated_ptrs_def) 
  apply (rule theI2)
    apply (assumption)
   apply (erule (1) stack_allocs_unique)
  apply (erule (1) stack_allocs_unique)
  done

lemma null_not_stack_free: "0 \<notin> stack_free d"
  by (simp add: root_ptr_valid_def stack_free_def)

lemma stack_alloc_stack_subset_stack_free: 
  "(p, d') \<in> stack_alloc \<S> TYPE('a::mem_type) d \<Longrightarrow> 
   ptr_span p \<subseteq> stack_free d"
  by (metis mem_Collect_eq stack_alloc_cases stack_free_def subsetI)

lemma stack_allocs_stack_subset_stack_free': 
  "(p, d') \<in> stack_allocs n \<S> TYPE('a::mem_type) d \<Longrightarrow> i < n \<Longrightarrow>
   ptr_span (p +\<^sub>p int i) \<subseteq> stack_free d"
  using stack_allocs_cases
    by (smt (verit, best) mem_Collect_eq stack_allocs_contained stack_free_def subsetD subsetI)

lemma stack_allocs_stack_subset_stack_free: 
  "(p, d') \<in> stack_allocs n \<S> TYPE('a::mem_type) d \<Longrightarrow> 
  {ptr_val p ..+ n * size_of TYPE('a)} \<subseteq> stack_free d"
  by (metis mem_Collect_eq stack_allocs_cases stack_free_def subsetI)

lemma stack_alloc_stack_free_mono: 
  assumes sub: "stack_free d1 \<subseteq> stack_free d2"
  assumes alloc_d1: "(p, d1') \<in> stack_alloc \<S> TYPE('a::mem_type) d1"
  shows "\<exists>d2'. (p, d2') \<in> stack_alloc \<S> TYPE('a) d2"
  by (smt (verit, del_insts) Collect_mono_iff alloc_d1 case_prodI mem_Collect_eq stack_alloc_cases 
      stack_alloc_def stack_free_def sub)

lemma stack_allocs_stack_free_mono: 
  assumes sub: "stack_free d1 \<subseteq> stack_free d2"
  assumes alloc_d1: "(p, d1') \<in> stack_allocs n \<S> TYPE('a::mem_type) d1"
  shows "\<exists>d2'. (p, d2') \<in> stack_allocs n \<S> TYPE('a) d2"
  using alloc_d1
  apply (rule stack_allocs_cases)
  using sub stack_allocs_stack_subset_stack_free' [OF alloc_d1]
  apply (auto simp add: stack_allocs_def stack_free_def)
  done 

lemma stack_alloc_stack_free_eq: 
  assumes sub: "stack_free d1 = stack_free d2"
  assumes alloc_d1: "(p, d1') \<in> stack_alloc \<S> TYPE('a::mem_type) d1"
  shows "\<exists>d2'. (p, d2') \<in> stack_alloc \<S> TYPE('a) d2"
  using stack_alloc_stack_free_mono [OF _ alloc_d1] sub by blast

lemma stack_allocs_stack_free_eq: 
  assumes sub: "stack_free d1 = stack_free d2"
  assumes alloc_d1: "(p, d1') \<in> stack_allocs n \<S> TYPE('a::mem_type) d1"
  shows "\<exists>d2'. (p, d2') \<in> stack_allocs n \<S> TYPE('a) d2"
  using stack_allocs_stack_free_mono [OF _ alloc_d1] sub by blast

lemma fresh_ptr_stack_free_disjunct: 
  "(p, d') \<in> stack_alloc \<S> TYPE('a::mem_type) d \<Longrightarrow> ptr_span p \<inter> stack_free d' = {}"
  by (smt (verit, best) disjoint_iff mem_Collect_eq mem_type_self ptr_val.ptr_val_def 
      root_ptr_valid_type_neq_disjoint stack_alloc_cases stack_free_def)

lemma fresh_ptrs_stack_free_disjunct': 
  "(p, d') \<in> stack_allocs n \<S> TYPE('a::mem_type) d \<Longrightarrow> i < n \<Longrightarrow> ptr_span (p +\<^sub>p int i) \<inter> stack_free d' = {}"
  using stack_allocs_cases
  by (smt (verit, ccfv_threshold) disjoint_iff mem_Collect_eq mem_type_self 
      ptr_val.ptr_val_def root_ptr_valid_casesE stack_free_def)

lemma fresh_ptrs_stack_free_disjunct:
  "(p, d') \<in> stack_allocs n \<S> TYPE('a::mem_type) d \<Longrightarrow> 
    {ptr_val p ..+ n * size_of TYPE('a) } \<inter> stack_free d' = {}"
  apply (simp add: array_index_span_conv)
  using fresh_ptrs_stack_free_disjunct' 
  apply blast
  done

lemma stack_allocs_neq: "(p, d') \<in> stack_allocs n \<S> TYPE('a::mem_type) d \<Longrightarrow> d \<noteq> d'"
  by (meson basic_trans_rules(31) disjoint_iff fresh_ptrs_stack_free_disjunct mem_type_self stack_allocs_cases stack_allocs_contained)

lemma stack_free_stack_alloc: 
  assumes p: "(p, d') \<in> stack_alloc \<S> TYPE('a::mem_type) d"
  shows "stack_free d' = stack_free d - ptr_span p"
proof -
  from p obtain 
    not_sb: "typ_uinfo_t (TYPE('a)) \<noteq> typ_uinfo_t (TYPE(stack_byte))" and
    sb: "\<forall>a \<in> ptr_span p. root_ptr_valid d (PTR (stack_byte) a)" and
    "ptr_aligned p" and
    c_guard: "c_guard p" and
    valid_d': "root_ptr_valid d' p" and
    d': "d' = ptr_force_type p d"
    by (cases rule: stack_alloc_cases) auto

  from c_guard valid_d' not_sb
  have not_stack: "\<forall>a \<in> ptr_span p. \<not> root_ptr_valid d' (PTR (stack_byte) a)"
    apply (simp add: d')
    by (metis IntI empty_iff mem_type_self ptr_force_type_h_t_valid ptr_val.ptr_val_def 
        root_ptr_valid_not_subtype_disjoint sub_typ_stack_byte)
  with fresh_ptr_stack_free_disjunct [OF p] stack_alloc_stack_subset_stack_free [OF p]

  show ?thesis
    apply safe
    subgoal
      using not_sb d' not_stack
      by (metis mem_Collect_eq p stack_alloc_root_ptr_valid_new_cases stack_free_def)
    subgoal by auto
    subgoal
      using sb d' not_stack
      by (simp add: ptr_force_type_d root_ptr_valid_def stack_free_def valid_root_footprint_def)
    done
qed

lemma stack_free_stack_allocs: 
  assumes p: "(p, d') \<in> stack_allocs n \<S> TYPE('a::mem_type) d"
  shows "stack_free d' = stack_free d - {ptr_val p ..+ n * size_of TYPE('a)}"
proof -
  from p obtain 
    not_sb: "typ_uinfo_t (TYPE('a)) \<noteq> typ_uinfo_t (TYPE(stack_byte))" and
    sb: "\<forall>a \<in> {ptr_val p ..+ n * size_of TYPE('a)}. root_ptr_valid d (PTR (stack_byte) a)" and

    aligned: "\<forall>i < n. ptr_aligned (p +\<^sub>p int i)" and
    c_guard: "\<forall>i < n. c_guard (p +\<^sub>p int i)" and
    root_valid: "\<forall>i < n. root_ptr_valid d' (p +\<^sub>p int i)"and
    d': "d' = fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) [0..<n] d"
    by (cases rule: stack_allocs_cases) auto

  from c_guard root_valid not_sb
  have not_stack: "\<forall>a \<in> {ptr_val p ..+ n * size_of TYPE('a)}. \<not> root_ptr_valid d' (PTR (stack_byte) a)"
    apply (simp add: d'  array_index_span_conv)
    by (smt (verit, best) disjoint_iff lessThan_iff mem_type_self ptr_val.ptr_val_def root_ptr_valid_casesE)

  with fresh_ptrs_stack_free_disjunct [OF p] stack_allocs_stack_subset_stack_free [OF p]
  show ?thesis
    apply safe
    subgoal
      using not_sb d' not_stack
      by (metis mem_Collect_eq p stack_allocs_root_ptr_valid_new_cases stack_free_def) 
    subgoal by auto
    subgoal
      using sb d' not_stack
      by (simp add: fold_ptr_force_type_other root_ptr_valid_def stack_free_def valid_root_footprint_def)
    done
qed

lemma stack_release_other: "x \<notin> ptr_span p \<Longrightarrow> stack_release p d x = d x"
  by (simp add: stack_release_def ptr_retyp_d)

lemma stack_releases_other: 
  fixes p::"'a::mem_type ptr"
  shows "x \<notin> {ptr_val p ..+ n * size_of TYPE('a::mem_type)} \<Longrightarrow> stack_releases n p d x = d x"
  by (simp add: stack_releases_def fold_ptr_retyp_other)

lemma in_ptr_span_itself: "x \<in> ptr_span (PTR('a::mem_type) x)"
  by (metis mem_type_self ptr_val.ptr_val_def)

lemma stack_byte_typing_footprint: 
  "stack_byte_typing x = (True, list_map (typ_slice_t (typ_uinfo_t TYPE(stack_byte)) 0))"
  apply (simp add: stack_release_def  stack_byte_typing_def)
  apply (subst ptr_force_type_footprint)
   apply (rule in_ptr_span_itself)
  apply simp
  done

lemma stack_release_footprint: "x \<in> ptr_span p \<Longrightarrow> 
  stack_release p d x = (True, list_map (typ_slice_t (typ_uinfo_t TYPE(stack_byte)) 0))"
  apply (simp add: stack_release_def  stack_byte_typing_def)
  apply (subst ptr_force_type_footprint)
   apply (rule in_ptr_span_itself)
  apply simp
  done

lemma stack_releases_footprint:
  fixes p::"'a::mem_type ptr"
  shows "x \<in> {ptr_val p ..+ n * size_of TYPE('a::mem_type)} \<Longrightarrow> 
    stack_releases n p d x = (True, list_map (typ_slice_t (typ_uinfo_t TYPE(stack_byte)) 0))"
  apply (simp add: stack_releases_def stack_byte_typing_def)
  apply (subst ptr_force_type_footprint)
   apply (rule in_ptr_span_itself)
  apply simp
  done


lemma stack_byte_typing_valid_root_footprint: "
  valid_root_footprint stack_byte_typing x (typ_uinfo_t TYPE(stack_byte))"
  using stack_byte_typing_footprint valid_root_footprint_def by (fastforce )

lemma stack_release_valid_root_footprint: "x \<in> ptr_span p \<Longrightarrow> 
  valid_root_footprint (stack_release p d) x (typ_uinfo_t TYPE(stack_byte))"
  using stack_release_footprint valid_root_footprint_def by (fastforce)

lemma stack_releases_valid_root_footprint:
  fixes p::"'a::mem_type ptr"
  shows  "x \<in> {ptr_val p ..+ n * size_of TYPE('a::mem_type)} \<Longrightarrow>
    valid_root_footprint (stack_releases n p d) x (typ_uinfo_t TYPE(stack_byte))"
  using stack_releases_footprint valid_root_footprint_def by fastforce

lemma stack_release_root_ptr_valid1:
  fixes p::"'a::mem_type ptr"
  fixes q:: "'b::mem_type ptr"
  assumes non_stack_p: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes non_stack_q: "typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes root_q: "root_ptr_valid (stack_release p d) q"  
  shows  "ptr_span p \<inter> ptr_span q = {} \<and> root_ptr_valid d q"
  apply (rule conjI)
  using assms
   apply (smt (verit, ccfv_threshold) disjoint_iff root_ptr_valid_valid_root_footprint size_of_tag 
      stack_release_valid_root_footprint valid_root_footprint_type_neq)
  by (smt (verit, best) intvlI non_stack_q root_ptr_valid_def root_q stack_release_other 
      stack_release_valid_root_footprint valid_root_footprint_def valid_root_footprint_type_neq)

lemma stack_releases_root_ptr_valid1:
  fixes p::"'a::mem_type ptr"
  fixes q:: "'b::mem_type ptr"
  assumes non_stack_p: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes non_stack_q: "typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes root_q: "root_ptr_valid (stack_releases n p d) q" 
  shows  "{ptr_val p ..+ n * size_of TYPE('a::mem_type)} \<inter> ptr_span q = {} \<and> root_ptr_valid d q"
  apply (rule context_conjI)
  subgoal 
    using assms
    by (smt (verit, best) disjoint_iff root_ptr_valid_def size_of_tag stack_releases_valid_root_footprint valid_root_footprint_type_neq)
  subgoal
    using assms 
    by (metis (full_types) disjoint_iff root_ptr_valid_domain' stack_releases_other)
  done

lemma stack_release_root_ptr_valid2:
  fixes p::"'a::mem_type ptr"
  fixes q:: "'b::mem_type ptr"
  assumes disj: "ptr_span p \<inter> ptr_span q = {}" 
  assumes valid_q: "root_ptr_valid d q"
  shows "root_ptr_valid (stack_release p d) q"  
  using assms
  by (smt (verit, ccfv_threshold) disjoint_iff intvlI root_ptr_valid_def size_of_def 
      stack_release_other typ_uinfo_size valid_root_footprint_def)

lemma stack_releases_root_ptr_valid2:
  fixes p::"'a::mem_type ptr"
  fixes q:: "'b::mem_type ptr"
  assumes disj: "{ptr_val p ..+ n * size_of TYPE('a::mem_type)} \<inter> ptr_span q = {}" 
  assumes valid_q: "root_ptr_valid d q"
  shows "root_ptr_valid (stack_releases n p d) q"
  using assms
  by (metis (full_types) disjoint_iff root_ptr_valid_domain' stack_releases_other)

lemma stack_release_root_ptr_valid_cases:
  fixes p::"'a::mem_type ptr"
  fixes q:: "'b::mem_type ptr"
  assumes non_stack_p: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes non_stack_q: "typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  shows  "root_ptr_valid (stack_release p d) q \<longleftrightarrow> ptr_span p \<inter> ptr_span q = {} \<and> root_ptr_valid d q"
  using assms stack_release_root_ptr_valid1 stack_release_root_ptr_valid2 by blast

lemma stack_releases_root_ptr_valid_cases:
  fixes p::"'a::mem_type ptr"
  fixes q:: "'b::mem_type ptr"
  assumes non_stack_p: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes non_stack_q: "typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  shows  "root_ptr_valid (stack_releases n p d) q \<longleftrightarrow> {ptr_val p ..+ n * size_of TYPE('a::mem_type)} \<inter> ptr_span q = {} \<and> root_ptr_valid d q"
  using assms stack_releases_root_ptr_valid1 stack_releases_root_ptr_valid2 by blast

lemma stack_release_root_ptr_valid_same_type_cases:
  fixes p::"'a::mem_type ptr"
  assumes cvalid_p: "d \<Turnstile>\<^sub>t p" 
  assumes non_stack_p: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  shows  "root_ptr_valid (stack_release p d) q \<longleftrightarrow> p \<noteq> q \<and> root_ptr_valid d q"
  using non_stack_p cvalid_p root_ptr_valid_h_t_valid cvalid_same_type_neq_disjoint stack_release_root_ptr_valid_cases 
  by fastforce

  
lemma stack_releases_root_ptr_valid_same_type_cases:
  fixes p::"'a::mem_type ptr"
  assumes cvalid_p: "\<And>i. i < n \<Longrightarrow> d \<Turnstile>\<^sub>t (p +\<^sub>p int i)" 
  assumes non_stack_p: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  shows  "root_ptr_valid (stack_releases n p d) q \<longleftrightarrow> (\<forall>i < n. q \<noteq> p +\<^sub>p (int i)) \<and> root_ptr_valid d q"
  apply standard
  subgoal
    using non_stack_p cvalid_p cvalid_same_type_neq_disjoint stack_releases_root_ptr_valid_cases array_index_span_conv
    by (smt (verit) Abs_fnat_hom_mult CTypesDefs.ptr_add_def disjoint_iff_not_equal ex_in_conv 
        in_ptr_span_itself intvlI intvl_empty mult_less_cancel2 mult_zero_left not_gr_zero 
        of_int_of_nat_eq ptr_add_0_id root_ptr_valid_domain semiring_1_class.of_nat_0 stack_releases_other)
  subgoal    
    using non_stack_p cvalid_p root_ptr_valid_same_type_neq_disjoint stack_releases_root_ptr_valid_cases array_index_span_conv
    by (smt (verit, best) array_to_index_span cvalid_same_type_neq_disjoint disjoint_iff root_ptr_valid_h_t_valid)
  done

lemma ptr_aligned_stack_byte[simp]: "ptr_aligned (PTR(stack_byte) x)"
  by (simp add: ptr_aligned_def)

lemma c_null_guard_cast_stack_byte:
  "x \<in> ptr_span (p::'a::mem_type ptr) \<Longrightarrow> c_null_guard p \<Longrightarrow> 
    c_null_guard (PTR (stack_byte) x)"
  apply (clarsimp simp add: c_null_guard_def )
  using intvl_Suc by blast

lemma c_guard_cast_stack_byte:
  "x \<in> ptr_span (p::'a::mem_type ptr) \<Longrightarrow> c_guard p \<Longrightarrow> 
    c_guard (PTR (stack_byte) x)"
  by (clarsimp simp add: c_guard_def c_null_guard_cast_stack_byte)

lemma stack_heap_typing_root_ptr_valid_footprint: "c_guard (p::stack_byte ptr) \<Longrightarrow> 
  root_ptr_valid stack_byte_typing p"
  by (simp add: root_ptr_valid_def stack_byte_typing_valid_root_footprint c_guard_cast_stack_byte)

lemma stack_release_root_ptr_valid_footprint: "x \<in> ptr_span p \<Longrightarrow> c_guard p \<Longrightarrow> 
  root_ptr_valid (stack_release p d) (PTR (stack_byte) x)"
  by (simp add: root_ptr_valid_def stack_release_valid_root_footprint c_guard_cast_stack_byte)

lemma stack_releases_root_ptr_valid_footprint: 
  fixes p::"'a::mem_type ptr"
  shows "x \<in> {ptr_val p ..+ n * size_of TYPE('a::mem_type)} \<Longrightarrow> \<forall>i < n. c_guard (p +\<^sub>p int i) \<Longrightarrow>
    root_ptr_valid (stack_releases n p d) (PTR (stack_byte) x)"
  apply (simp add: root_ptr_valid_def stack_releases_valid_root_footprint c_guard_cast_stack_byte)
  using array_to_index_span c_guard_cast_stack_byte by blast

lemma stack_alloc_other: 
  "(p, d') \<in> stack_alloc \<S> TYPE('a::mem_type) d \<Longrightarrow> x \<notin> ptr_span p \<Longrightarrow>
   d' x = d x"
  using ptr_force_type_d stack_alloc_cases by blast

lemma stack_allocs_other:
  "(p, d') \<in> stack_allocs n \<S> TYPE('a::mem_type) d \<Longrightarrow> x \<notin> {ptr_val p ..+ n * size_of TYPE('a::mem_type)} \<Longrightarrow>
   d' x = d x"
  using fold_ptr_force_type_other stack_allocs_cases by blast


lemma stack_free_stack_release_mono:
  shows "stack_free d \<subseteq> stack_free (stack_release p d)"
  by (smt (verit) Abs_fnat_hom_0 One_nat_def add.right_neutral less_Suc0 
      mem_Collect_eq root_ptr_valid_def size_of_stack_byte(2) 
      stack_release_other stack_release_valid_root_footprint stack_free_def 
      subsetI typ_uinfo_size valid_root_footprint_def)

lemma stack_free_stack_release_mono': 
  "stack_free d1 \<subseteq> stack_free d2 \<Longrightarrow> stack_free (stack_release p d1) \<subseteq> stack_free (stack_release p d2)"
  by (smt (verit) Collect_mono_iff One_nat_def less_Suc0 root_ptr_valid_def size_of_stack_byte(3)
      stack_free_def stack_release_footprint stack_release_other valid_root_footprint_def)

lemma stack_free_stack_releases_mono:
  shows "stack_free d \<subseteq> stack_free (stack_releases n p d)"
  by (smt (verit) Abs_fnat_hom_0 One_nat_def add.right_neutral less_Suc0 
      mem_Collect_eq root_ptr_valid_def size_of_stack_byte(2) 
      stack_releases_other stack_releases_valid_root_footprint stack_free_def 
      subsetI typ_uinfo_size valid_root_footprint_def)

lemma stack_free_stack_releases_mono': 
  "stack_free d1 \<subseteq> stack_free d2 \<Longrightarrow> stack_free (stack_releases n p d1) \<subseteq> stack_free (stack_releases n p d2)"
  apply (clarsimp simp add: stack_releases_def stack_free_def root_ptr_valid_def valid_root_footprint_def)
  by (smt (verit, best) Collect_mono_iff override_on_apply_in override_on_apply_notin)

lemma stack_free_ptr_span_stack_release:
  "c_null_guard p \<Longrightarrow> ptr_span p \<subseteq> stack_free (stack_release p d)"
  by (simp add: c_guard_def c_null_guard_cast_stack_byte root_ptr_valid_def 
      stack_release_valid_root_footprint stack_free_def subsetI)

lemma stack_free_ptr_span_stack_releases:
  fixes p::"'a::mem_type ptr"
  shows "(\<And>i. i < n \<Longrightarrow> c_null_guard (p +\<^sub>p int i)) \<Longrightarrow> 
    {ptr_val p ..+ n * size_of TYPE('a::mem_type)} \<subseteq> stack_free (stack_releases n p d)"
  by (fastforce simp add: c_guard_def c_null_guard_cast_stack_byte root_ptr_valid_def 
      stack_releases_valid_root_footprint stack_free_def subsetI array_index_span_conv)

lemma stack_free_stack_release: 
  assumes c_null_guard: "c_null_guard p"  
  shows "stack_free (stack_release p d) = ptr_span p \<union> stack_free d"
proof 
  show "stack_free (stack_release p d) \<subseteq> ptr_span p \<union> stack_free d"
  proof
    fix x
    assume x_in: "x \<in> stack_free (stack_release p d)" 
    show "x \<in> ptr_span p \<union> stack_free d"
    proof (cases "x \<in> ptr_span p")
      case True
      then show ?thesis 
        by simp
    next
      case False
      with c_null_guard x_in show ?thesis
        by (simp add: root_ptr_valid_def stack_release_other stack_free_def 
            valid_root_footprint_def)
    qed
  qed
next
  show "ptr_span p \<union> stack_free d \<subseteq> stack_free (stack_release p d)"
    using c_null_guard stack_free_ptr_span_stack_release stack_free_stack_release_mono
    by blast
qed

lemma stack_free_stack_releases: 
  fixes p::"'a::mem_type ptr"
  assumes c_null_guard: "\<And>i. i < n \<Longrightarrow> c_null_guard (p +\<^sub>p int i)"  
  shows "stack_free (stack_releases n p d) = {ptr_val p ..+ n * size_of TYPE('a::mem_type)} \<union> stack_free d"
proof 
  show "stack_free (stack_releases n p d) \<subseteq> {ptr_val p ..+ n * size_of TYPE('a::mem_type)} \<union> stack_free d"
  proof
    fix x
    assume x_in: "x \<in> stack_free (stack_releases n p d)" 
    show "x \<in> {ptr_val p ..+ n * size_of TYPE('a::mem_type)} \<union> stack_free d"
    proof (cases "x \<in> {ptr_val p ..+ n * size_of TYPE('a::mem_type)}")
      case True
      then show ?thesis 
        by simp
    next
      case False
      with c_null_guard x_in show ?thesis
        by (simp add: root_ptr_valid_def stack_releases_other stack_free_def 
            valid_root_footprint_def)
    qed
  qed
next
  show "{ptr_val p ..+ n * size_of TYPE('a::mem_type)} \<union> stack_free d \<subseteq> stack_free (stack_releases n p d)"
    using c_null_guard stack_free_ptr_span_stack_releases stack_free_stack_releases_mono
    by blast
qed

definition "On_Exit":: "('s, 'p, 'f) com \<Rightarrow> ('s, 'p, 'f) com \<Rightarrow> ('s, 'p, 'f) com" where
"On_Exit c cleanup = Seq (Catch c (Seq cleanup Throw)) cleanup"

locale heap_typing_state =
  lense htd htd_upd 
  for
  htd:: "'s \<Rightarrow> heap_typ_desc" and
  htd_upd:: "(heap_typ_desc \<Rightarrow> heap_typ_desc) \<Rightarrow> 's \<Rightarrow> 's" 

locale heap_mem_state =
  lense hmem hmem_upd 
  for
  hmem:: "'s \<Rightarrow> heap_mem" and
  hmem_upd:: "(heap_mem \<Rightarrow> heap_mem) \<Rightarrow> 's \<Rightarrow> 's" 

locale heap_state = 
  typing: heap_typing_state htd htd_upd + heap: heap_mem_state hmem hmem_upd 
  for
  htd:: "'s \<Rightarrow> heap_typ_desc" and
  htd_upd:: "(heap_typ_desc \<Rightarrow> heap_typ_desc) \<Rightarrow> 's \<Rightarrow> 's" and
  hmem:: "'s \<Rightarrow> heap_mem" and
  hmem_upd:: "(heap_mem \<Rightarrow> heap_mem) \<Rightarrow> 's \<Rightarrow> 's" +
  assumes heap_commute: "hmem_upd f (htd_upd g s) = htd_upd g (hmem_upd f s)"

begin
lemma htd_hmem_upd [simp]: "htd (hmem_upd f s) = htd s"
  by (metis heap_commute typing.get_upd typing.upd_get)

lemma hmem_htd_upd [simp]: "hmem (htd_upd f s) = hmem s"
  by (metis heap.get_upd heap.upd_get heap_commute)
end

locale heap_state_global =
  heap_state htd htd_upd hmem hmem_upd + lense glob glob_upd 
  for
  htd:: "'s \<Rightarrow> heap_typ_desc" and
  htd_upd:: "(heap_typ_desc \<Rightarrow> heap_typ_desc) \<Rightarrow> 's \<Rightarrow> 's" and
  hmem:: "'s \<Rightarrow> heap_mem" and
  hmem_upd:: "(heap_mem \<Rightarrow> heap_mem) \<Rightarrow> 's \<Rightarrow> 's" and
  glob:: "'s \<Rightarrow> 'a" and 
  glob_upd:: "('a \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> 's" +
  assumes glob_htd_commute: "\<And>g h. glob_upd g (htd_upd h s) = htd_upd h (glob_upd g s)"
  assumes glob_hmem_commute: "\<And>g h. glob_upd g (hmem_upd h s) = hmem_upd h (glob_upd g s)"

locale heap_raw_state =
  lense t_hrs t_hrs_update 
  for
  t_hrs :: "'s \<Rightarrow> heap_raw_state" and
  t_hrs_update:: "(heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 's \<Rightarrow> 's" 
begin
sublocale heap_state  
  "\<lambda>s. (hrs_htd (t_hrs s))" "\<lambda>upd. (t_hrs_update (hrs_htd_update upd))" 
  "\<lambda>s. (hrs_mem (t_hrs s))" "\<lambda>upd. (t_hrs_update (hrs_mem_update upd))" 
  apply (unfold_locales)
        apply (simp_all add: hrs_htd_update hrs_htd_update_comp hrs_mem_update hrs_mem_update_comp)
    apply (metis hrs_htd_def hrs_htd_update hrs_mem_def hrs_mem_htd_update prod.collapse upd_same)
   apply (metis hrs_htd_def hrs_htd_mem_update hrs_mem_def hrs_mem_update prod.expand upd_same)
  using hrs_update_commute by force
end

locale heap_raw_state_global =
  heap_raw_state t_hrs t_hrs_update + lense glob glob_upd 
  for
  t_hrs :: "'s \<Rightarrow> heap_raw_state" and
  t_hrs_update:: "(heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 's \<Rightarrow> 's" and
  glob:: "'s \<Rightarrow> 'a" and 
  glob_upd:: "('a \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> 's" +
assumes glob_heap_commute: "\<And>g h. glob_upd g (t_hrs_update h s) = t_hrs_update h (glob_upd g s)"
begin
sublocale heap_state_global   
  "\<lambda>s. (hrs_htd (t_hrs s))" "\<lambda>upd. (t_hrs_update (hrs_htd_update upd))" 
  "\<lambda>s. (hrs_mem (t_hrs s))" "\<lambda>upd. (t_hrs_update (hrs_mem_update upd))"
  "glob" "glob_upd"
  apply (unfold_locales)
  using glob_heap_commute
   apply simp
  using glob_heap_commute
  apply simp
  done
end




locale stack_heap_state = heap_state htd htd_upd hmem hmem_upd 
  for
    htd:: "'s \<Rightarrow> heap_typ_desc" and
    htd_upd:: "(heap_typ_desc \<Rightarrow> heap_typ_desc) \<Rightarrow> 's \<Rightarrow> 's" and
    hmem:: "'s \<Rightarrow> heap_mem" and
    hmem_upd:: "(heap_mem \<Rightarrow> heap_mem) \<Rightarrow> 's \<Rightarrow> 's" +
  fixes \<S>::"addr set"
begin

definition With_Fresh_Stack_Ptr:: "nat \<Rightarrow> ('s \<Rightarrow> 'a list set) \<Rightarrow> (('a::mem_type ptr) \<Rightarrow> ('s, 'p, strictc_errortype) com) \<Rightarrow> 
   ('s, 'p, strictc_errortype) com" where
\<open>With_Fresh_Stack_Ptr n init c = 
 Guard StackOverflow ({s. stack_allocs n \<S> TYPE('a) (htd s) \<noteq> {} \<and> (\<exists>vs. vs \<in> init s \<and> length vs = n)})
  (DynCom (\<lambda>s0. 
    Spec {(s, t). \<exists>p d' vs bs. 
       (p, d') \<in> stack_allocs n \<S> TYPE('a) (htd s) \<and>
       vs \<in> init s \<and> length vs = n \<and> length bs = n * size_of TYPE('a) \<and>
       t = hmem_upd (fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (vs!i) (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs))) [0..<n]) 
            (htd_upd (\<lambda>_. d') s)};; 
    DynCom (\<lambda>s1.
      On_Exit 
        (c (allocated_ptrs n \<S> TYPE('a) (htd s0) (htd s1)))
        (Spec {(s, t). \<exists>bs. length bs = n * size_of TYPE('a) \<and> 
          t = hmem_upd (heap_update_list (ptr_val (allocated_ptrs n \<S> TYPE('a) (htd s0) (htd s1))) bs) 
               (htd_upd (stack_releases n ((allocated_ptrs n \<S> TYPE('a) (htd s0) (htd s1)))) s)}))))
\<close>

ML \<open>

structure With_Fresh_Stack_Ptr =
struct

type data = {match: term -> {n:term, init:term, c:term, ct_: term, instantiate: {n:term, init:term, c:term} -> term},
             cterm_match: cterm -> {n:cterm, init:cterm, c:cterm, ct_: cterm, instantiate: {n:cterm, init:cterm, c:cterm} -> cterm}}

fun map_match f ({match, cterm_match}:data) = {match = f match, cterm_match = cterm_match}:data
fun map_cterm_match f ({match, cterm_match}:data) = {match = match, cterm_match = f cterm_match}:data
fun merge_match (f, g) = Utils.fast_merge (fn (f, g) => Utils.first_match [f, g]) (f, g)

structure Data = Generic_Data (
    type T = data
    val empty = {match = fn _ => raise Match, cterm_match = fn _ => raise Match};
    val merge = Utils.fast_merge (fn ({match = f1, cterm_match = g1}, {match = f2, cterm_match = g2}) => 
         {match = merge_match (f1, f2), cterm_match = merge_match (g1, g2)}); 
)

fun match ctxt = #match (Data.get (Context.Proof ctxt))
fun cterm_match ctxt = #cterm_match (Data.get (Context.Proof ctxt))

fun add_match match = Data.map (map_match (Utils.add_match match))
fun add_cterm_match cterm_match = Data.map (map_cterm_match (Utils.add_match cterm_match))
 

end
\<close>


declaration \<open>
fn phi => fn context =>
  let
    fun match t = @{morph_match (fo) \<open>With_Fresh_Stack_Ptr ?n ?init ?c\<close>} phi (Context.theory_of context) t
        handle Pattern.MATCH => raise Match
    fun cterm_match ct = @{cterm_morph_match (fo) \<open>With_Fresh_Stack_Ptr ?n ?init ?c\<close>} phi ct
        handle Pattern.MATCH => raise Match
  in
    context 
    |> With_Fresh_Stack_Ptr.add_match match 
    |> With_Fresh_Stack_Ptr.add_cterm_match cterm_match 
  end
\<close>

end

locale stack_heap_raw_state = heap_raw_state t_hrs t_hrs_update 
  for
  t_hrs :: "'s \<Rightarrow> heap_raw_state" and
  t_hrs_update:: "(heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 's \<Rightarrow> 's" +
fixes \<S>::"addr set"
begin
  sublocale stack_heap_state  
    "\<lambda>s. hrs_htd (t_hrs s)" "\<lambda>upd. t_hrs_update (hrs_htd_update upd)" 
    "\<lambda>s. hrs_mem (t_hrs s)" "\<lambda>upd. t_hrs_update (hrs_mem_update upd)" 
    "\<S>"
    by unfold_locales
end

locale globals_stack_heap_state = stack_heap_state htd htd_upd hmem hmem_upd \<S>
  for
    htd:: "'s \<Rightarrow> heap_typ_desc" and
    htd_upd:: "(heap_typ_desc \<Rightarrow> heap_typ_desc) \<Rightarrow> 's \<Rightarrow> 's" and
    hmem:: "'s \<Rightarrow> heap_mem" and
    hmem_upd:: "(heap_mem \<Rightarrow> heap_mem) \<Rightarrow> 's \<Rightarrow> 's" and
    \<S>::"addr set" +
  fixes \<G>::"addr set"

locale globals_stack_heap_raw_state = stack_heap_raw_state t_hrs t_hrs_update \<S>
  for
  t_hrs :: "'s \<Rightarrow> heap_raw_state" and
  t_hrs_update:: "(heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 's \<Rightarrow> 's" and
  \<S>::"addr set" +
  fixes \<G>::"addr set"
begin
sublocale globals_stack_heap_state
    "\<lambda>s. hrs_htd (t_hrs s)" "\<lambda>upd. t_hrs_update (hrs_htd_update upd)" 
    "\<lambda>s. hrs_mem (t_hrs s)" "\<lambda>upd. t_hrs_update (hrs_mem_update upd)" 
    "\<S>" "\<G>"
    by unfold_locales
end

section "Misc derived language elements"

definition
  creturn :: "(('e c_exntype \<Rightarrow> 'e c_exntype) \<Rightarrow> ('g, 'l, 'e, 'x) state_scheme \<Rightarrow> ('g, 'l, 'e, 'x) state_scheme)
      \<Rightarrow> (('a \<Rightarrow> 'a) \<Rightarrow> ('g, 'l, 'e, 'x) state_scheme \<Rightarrow> ('g, 'l, 'e, 'x) state_scheme)
      \<Rightarrow> (('g, 'l, 'e, 'x) state_scheme \<Rightarrow> 'a) \<Rightarrow> (('g, 'l, 'e, 'x) state_scheme,'p,'f) com"
where
  "creturn rtu xfu v \<equiv> (Basic (\<lambda>s. xfu (\<lambda>_. v s) s);; (Basic (rtu (\<lambda>_. Return));; THROW))"

definition

  creturn_void :: "(('e c_exntype \<Rightarrow> 'e c_exntype) \<Rightarrow> ('g, 'l, 'e, 'x) state_scheme
      \<Rightarrow> ('g, 'l, 'e, 'x) state_scheme) \<Rightarrow> (('g, 'l, 'e, 'x) state_scheme,'p,'f) com"
where
  "creturn_void rtu \<equiv> (Basic (rtu (\<lambda>_. Return));; THROW)"

definition
  cexit :: "(('g, 'l, 'e, 'x) state_scheme \<Rightarrow> ('g, 'l, 'e, 'x) state_scheme) \<Rightarrow> (('g, 'l, 'e, 'x) state_scheme,'p,'f) com"
where
  "cexit xfu \<equiv> (Basic xfu;; THROW)"


definition
  cbreak :: "(('e c_exntype \<Rightarrow> 'e c_exntype) \<Rightarrow> ('g, 'l, 'e, 'x) state_scheme
      \<Rightarrow> ('g, 'l, 'e, 'x) state_scheme) \<Rightarrow> (('g, 'l, 'e, 'x) state_scheme,'p,'f) com"
where
  "cbreak rtu \<equiv> (Basic (rtu (\<lambda>_. Break));; THROW)"

definition

  ccatchbrk :: "(('g, 'l, 'e, 'x) state_scheme \<Rightarrow>'e c_exntype) \<Rightarrow> (('g, 'l, 'e, 'x) state_scheme,'p,'f) com"
where
  "ccatchbrk rt \<equiv> Cond {s. rt s = Break} SKIP THROW"

definition
  cgoto :: "string \<Rightarrow> (('e c_exntype \<Rightarrow> 'e c_exntype) \<Rightarrow> ('g, 'l, 'e, 'x) state_scheme
      \<Rightarrow> ('g, 'l, 'e, 'x) state_scheme) \<Rightarrow> (('g, 'l, 'e, 'x) state_scheme,'p,'f) com"
where
  "cgoto l rtu \<equiv> (Basic (rtu (\<lambda>_. Goto l));; THROW)"

definition
  ccatchgoto :: "string \<Rightarrow> (('g, 'l, 'e, 'x) state_scheme \<Rightarrow> 'e c_exntype) \<Rightarrow> (('g, 'l, 'e, 'x) state_scheme,'p,'f) com"
where
  "ccatchgoto l rt \<equiv> Cond {s. rt s = Goto l} SKIP THROW"

definition
  ccatchreturn :: "(('g, 'l, 'e, 'x) state_scheme \<Rightarrow> 'e c_exntype) \<Rightarrow> (('g, 'l, 'e, 'x) state_scheme,'p,'f) com"
where
  "ccatchreturn rt \<equiv> Cond {s. is_local (rt s)} SKIP THROW"

definition
  cchaos :: "('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a,'c,'d) com"
where
  "cchaos upd \<equiv> Spec { (s0,s) . \<exists>v. s = upd v s0 }"

definition
  "guarded_spec_body F R = Guard F (fst ` R) (Spec R)"



end
