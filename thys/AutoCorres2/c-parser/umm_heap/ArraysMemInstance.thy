(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ArraysMemInstance
imports Arrays CompoundCTypes
begin

primrec (in c_type)
  array_tag_n :: "nat \<Rightarrow> ('a,'b::finite) array xtyp_info"
where
  atn_base:
  "array_tag_n 0 = ((empty_typ_info (align_td (typ_uinfo_t TYPE('a))) (typ_name (typ_uinfo_t TYPE('a)) @ ''_array_'' @
      nat_to_bin_string (CARD('b::finite))))::('a,'b) array
          xtyp_info)"
| atn_rec:
  "array_tag_n (Suc n) = ((ti_typ_combine TYPE('a)
      (\<lambda>x. index x n) (\<lambda>x f. update f n x) 0 (replicate n CHR ''1'')
          (array_tag_n n))::('a,'b::finite) array xtyp_info)"

definition (in c_type) array_tag :: "('a,'b::finite) array itself \<Rightarrow> ('a,'b) array xtyp_info" where
  "array_tag t \<equiv> array_tag_n (CARD('b))"


lemma (in c_type) typ_name_array_tag: "typ_name ((array_tag_n n)::('a,'b::finite) array xtyp_info) = 
  (typ_name (typ_uinfo_t TYPE('a)) @ ''_array_'' @ nat_to_bin_string (CARD('b)))"
  apply (induct n) 
   apply (simp add: empty_typ_info_def)
  apply (simp add: ti_typ_combine_def Let_def adjust_ti_def)
  done

instantiation array :: (c_type, finite) c_type 
begin

definition typ_info_array: 
  "typ_info_t (w::('a::c_type,'b::finite) array itself) \<equiv> array_tag w"

definition "typ_name_itself (w::('a::c_type,'b::finite) array itself) = typ_name (typ_info_t w)"

instance by (intro_classes) (simp add: typ_name_itself_array_def)
end

lemma (in c_type) field_names_array_tag_length [rule_format]:
  "x \<in> set (field_names_list (array_tag_n n)) \<longrightarrow> length x < n"
  by (induct n) (auto)

lemma (in c_type) replicate_mem_field_names_array_tag [simp]:
  "replicate n x \<notin> set (field_names_list (array_tag_n n))"
  by (fastforce dest: field_names_array_tag_length)

lemma (in c_type) aggregate_array_tag [simp]:
  "aggregate (array_tag_n n)"
  by (cases n; simp add: c_type.ti_typ_combine_def)

lemma (in mem_type) wf_desc_array_tag [simp]:
  "wf_desc ((array_tag_n n)::('a,'b::finite) array xtyp_info)"
  by (induct n; simp) (fastforce elim: wf_desc_ti_typ_combine)

lemma (in mem_type) wf_size_desc_array_tag [simp]:
  "0 < n \<Longrightarrow> wf_size_desc ((array_tag_n n)::('a,'b::finite) array xtyp_info)"
  apply(induct n; simp)
  subgoal for n 
    apply(cases "n=0"; simp)
    apply(rule wf_size_desc_ti_typ_combine)
    apply simp
    done
  done

lemma (in mem_type) upd_ind_array_tag_udpate [simp]:
  "\<lbrakk> n \<le> m; n \<le> CARD('b) \<rbrakk> \<Longrightarrow>
   upd_ind (lf_set ((array_tag_n n)::('a,'b::finite) array xtyp_info) []) (\<lambda>x f. update f m x)"
  by (induct n) (auto elim: upd_ind_ti_typ_combine )

lemma (in mem_type) fc_array_tag_udpate [simp]:
  "\<lbrakk> n \<le> m; n \<le> CARD('b) \<rbrakk> \<Longrightarrow>
   fu_commutes (update_ti_t ((array_tag_n n)::('a,'b::finite) array xtyp_info)) (\<lambda>x f. update f m x)"
  by (induct n; fastforce elim: fc_ti_typ_combine simp: fg_cons_def)

lemma (in mem_type) acc_ind_array_tag_udpate [simp]:
  "\<lbrakk> n \<le> m; m < CARD('b) \<rbrakk> \<Longrightarrow>
   acc_ind (\<lambda>x. index x m) (lf_fd ` lf_set ((array_tag_n n)::('a,'b::finite) array xtyp_info) [])"
  by (induct n; fastforce elim: acc_ind_ti_typ_combine)

lemma (in mem_type) fa_fu_g_array_tag_udpate [simp]:
  "\<lbrakk> n \<le> m; m < CARD('b) \<rbrakk> \<Longrightarrow>
   fa_ind (lf_fd ` lf_set ((array_tag_n n)::('a,'b::finite) array xtyp_info) []) (\<lambda>x f. update f m x)"
  by (induct n; fastforce elim: fa_ind_ti_typ_combine)

lemma (in mem_type) wf_fdp_array_tag [simp]:
  "n \<le> CARD('b) \<Longrightarrow> wf_lf (lf_set ((array_tag_n n)::('a,'b::finite) array xtyp_info) [])"
  by (induct n; fastforce elim: wf_lf_ti_typ_combine)

lemma upd_local_update [simp]:
  "upd_local (\<lambda>x f. update f n x)"
  unfolding upd_local_def
  by (metis update_update)

lemma (in mem_type) fu_eq_mask_array_tag [simp, rule_format]:
  "n \<le> CARD('b) \<longrightarrow> (\<forall>m. (\<forall>k v. k < CARD('b) \<longrightarrow>
      index ((m v)::('a,'b) array) k = (if n \<le> k then
          index (undefined::('a,'b::finite) array) k
          else index v k)) \<longrightarrow> fu_eq_mask (array_tag_n n) m)"
  apply(induct n; clarsimp)
   apply(rule fu_eq_mask_empty_typ_info)
   apply(clarsimp simp: array_index_eq)
  subgoal for n m
    apply(rule fu_eq_mask_ti_typ_combine; clarsimp?)
    apply (drule spec [where x="\<lambda>v. update (m v) n (index (undefined::'a['b]) n)"]) 
     apply(erule impE)
      apply clarsimp
    subgoal for k v
      by (cases "k=n") auto
    subgoal premises prems 
    proof -
      from prems 
      have "\<forall>v bs. m (update v n bs) = update (m v) n bs" 
        apply(clarsimp simp: array_index_eq)
        subgoal for v bs i
          apply(cases "i=n"; clarsimp)
          apply(cases "Suc n \<le> i"; clarsimp)
          done
        done
      then show ?thesis using prems  by clarsimp
    qed
    subgoal
      by(clarsimp simp: fg_cons_def)
    done
  done

lemma (in c_type) size_td_array_tag [simp]:
  "size_td (((array_tag_n n)::('a,'b::finite) array xtyp_info)) =
      n * size_of TYPE('a)"
  by (induct n; simp add: size_td_lt_ti_typ_combine size_of_def)

lemma (in c_type) align_td_wo_align_array_tag:
  "0 < n \<Longrightarrow>
   align_td_wo_align ((array_tag_n n)::('a,'b::finite) array xtyp_info) = (align_td_wo_align (typ_info_t (TYPE('a))))"
proof  (induct n)
  case 0
  then show ?case by clarsimp
next
  case (Suc n)
  then show ?case 
    by (cases "n = 0") (auto simp: align_of_def max_def)
qed

lemma align_td_export_uinfo[simp]: "align_td (export_uinfo t) = align_td t"
  apply (cases t)
  apply (simp add: export_uinfo_def)
  done

lemma (in c_type) align_td_uinfo: "align_td (typ_uinfo_t (TYPE('a))) = align_td (typ_info_t (TYPE('a)))"
  by (simp add: typ_uinfo_t_def)

lemma (in c_type) align_td_array_tag:
  "0 < n \<Longrightarrow>
   align_td ((array_tag_n n)::('a,'b::finite) array xtyp_info) = (align_td (typ_info_t (TYPE('a))))"
proof (induct n)
  case 0
  then show ?case by clarsimp
next
  case (Suc n)
  then show ?case 
    by (cases "n = 0") ( auto simp: align_of_def max_def align_td_uinfo)
qed 


lemma  align_of_array [simp]:
  "0 < CARD('b) \<Longrightarrow> align_of TYPE(('a,'b::finite) array) = align_of TYPE('a::c_type)"
  by (simp add: align_of_def typ_info_array array_tag_def align_td_array_tag)

lemma align_td_wo_align_array_info: "0 < CARD('b) \<Longrightarrow> align_td_wo_align (typ_info_t TYPE(('a,'b::finite) array)) 
 = align_td_wo_align (typ_info_t TYPE('a::c_type))"
  by (simp add: typ_info_array array_tag_def align_td_wo_align_array_tag)

lemma align_td_array_info: "0 < CARD('b) \<Longrightarrow> align_td (typ_info_t TYPE(('a,'b::finite) array)) 
 = align_td (typ_info_t TYPE('a::c_type))"
  by (simp add: typ_info_array array_tag_def align_td_array_tag)

lemma (in mem_type) align_field_array [simp]:
  "align_field ((array_tag_n n)::('a,'b::finite) array xtyp_info)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case 
    by clarsimp (metis align_field_ti_typ_combine align_of_def align_size_of dvd_mult size_td_array_tag)
qed
 

lemma (in mem_type) wf_align_array [simp]:
  "wf_align ((array_tag_n n)::('a,'b::finite) array xtyp_info)"
proof (induct n)
  case 0
  then show ?case by (simp add: wf_align_simps)
next
  case (Suc n)
  then show ?case by (simp add: wf_align_ti_typ_combine)
qed 

instance array :: (mem_type,finite) mem_type_sans_size
  apply intro_classes
       apply(simp_all add: typ_info_array array_tag_def size_of_def norm_bytes_def)
   apply clarsimp
   apply(rule fu_eq_mask)
    apply(simp add: size_of_def)
   apply(rule fu_eq_mask_array_tag; simp)
  apply (clarsimp simp: align_of_def typ_info_array array_tag_def align_td_wo_align_array_tag)
  apply (metis align_of_def align_size_of dvd_mult size_of_def)
  done

declare atn_base [simp del]
declare atn_rec [simp del]

lemma size_of_array [simp]:
  "size_of TYPE(('a,'b::finite) array) = CARD('b) * size_of TYPE('a::c_type)"
  by (simp add: size_of_def typ_info_array array_tag_def)

lemma size_td_array:
  "size_td (typ_info_t TYPE(('a,'b::finite) array)) = CARD('b) * size_of TYPE('a::c_type)"
  by (simp add: size_of_def typ_info_array array_tag_def)

lemma align_td_array:
  "2^align_td (typ_info_t TYPE(('a,'b::finite) array)) = align_of TYPE('a::c_type)"
  by (simp add: align_of_def typ_info_array array_tag_def align_td_array_tag)

lemma wf_field_array: 
 "n < CARD('b) \<Longrightarrow> wf_field (\<lambda>x. x.[n]) (\<lambda>x f. update (f::('a,'b::finite) array) n x)"
  by (simp add: wf_field_def)


lemma wf_cfield_array: 
 "n < CARD('b) \<Longrightarrow> wf_cfield (\<lambda>x. x.[n]) (\<lambda>x f. update (f::('a::c_type,'b::finite) array) n x)"
  by (simp add: wf_cfield_def wf_field_array)

lemma wf_xfield_array: 
 "n < CARD('b) \<Longrightarrow> wf_xfield (\<lambda>x. x.[n]) (\<lambda>x f. update (f::('a::xmem_type,'b::finite) array) n x)"
  by (simp add: wf_xfield_def wf_cfield_array)


lemma wf_component_descs_array_tag_n: "n \<le> CARD('b) 
\<Longrightarrow> wf_component_descs ((array_tag_n::nat \<Rightarrow> ('a::xmem_type,'b::finite) array xtyp_info) n)"
  apply (induct n)
   apply (simp add: atn_base)
  apply (simp add: atn_rec)
  apply (rule wf_xfield.wf_component_descs_ti_typ_combine)
  apply (simp add: wf_xfield_array)
  apply simp
  done

lemma wf_component_descs_array: "wf_component_descs (typ_info_t TYPE('a::xmem_type['b::finite]))"
  apply (simp add: typ_info_array array_tag_def)
  apply (rule wf_component_descs_array_tag_n)
  apply simp
  done


lemma (in c_type) set_toplevel_field_descs_array_tag_n:
"(set (toplevel_field_descs ( (array_tag_n::nat \<Rightarrow> ('a,'b::finite) array xtyp_info) n))) = 
{d. \<exists>m. m < n \<and> d = \<lparr>field_access = xto_bytes \<circ> (\<lambda>x. index x m), 
  field_update = (\<lambda>x f. update f m x) \<circ> xfrom_bytes,
  field_sz = size_of TYPE('a)\<rparr>}" (is "_ = ?D n")
proof (induct n)
  case 0
  then show ?case by (simp add: atn_base empty_typ_info_def)
next
  case (Suc n)
  from Suc.hyps have hyp: "set (toplevel_field_descs (array_tag_n n)) = ?D n" .

  show ?case
  proof
    show "set (toplevel_field_descs (array_tag_n (Suc n))) \<subseteq> ?D (Suc n)"
    proof
      fix d
      assume d_in: "d \<in> set (toplevel_field_descs ((array_tag_n::nat \<Rightarrow> ('a,'b::finite) array xtyp_info) (Suc n)))"
      show "d \<in> ?D (Suc n)"
      proof -
        from d_in consider 
        (d_new) "d = \<lparr>field_access = xto_bytes \<circ> (\<lambda>x. x.[n]), field_update = (\<lambda>x f. update f n x) \<circ> xfrom_bytes, field_sz = size_of TYPE('a)\<rparr>" |
        (d_old) "d \<in> set (toplevel_field_descs (array_tag_n n))"
          by (auto simp add: set_toplevel_field_descs_ti_typ_combine_aggregate atn_rec)
        then show ?thesis
        proof (cases)
          case d_new
          then show ?thesis by (auto simp add: comp_def)
        next
          case d_old
          with hyp less_Suc_eq show ?thesis by (auto)
        qed
      qed
    qed
  next
    show "?D (Suc n) \<subseteq> set (toplevel_field_descs (array_tag_n (Suc n)))"
    proof
      fix d
      assume d_in: "d \<in> ?D (Suc n)"
      show "d \<in> set (toplevel_field_descs ((array_tag_n::nat \<Rightarrow> ('a,'b::finite) array xtyp_info) (Suc n)))"
      proof -
        from d_in obtain m where m_bound: "m < Suc n" and
         d: "d = \<lparr>field_access = xto_bytes \<circ> (\<lambda>x. x.[m]),
                  field_update = (\<lambda>x f. update f m x) \<circ> xfrom_bytes,
                  field_sz = size_of TYPE('a)\<rparr>" by (auto simp add: comp_def)
        from m_bound d show ?thesis
          using hyp
          apply (simp add: set_toplevel_field_descs_ti_typ_combine_aggregate atn_rec)
          using not_less_less_Suc_eq by fastforce
      qed
    qed
  qed
qed

lemma (in xmem_type) field_desc_independent_extend_array:
 "n < CARD('b) \<Longrightarrow>
         field_desc_independent (xto_bytes \<circ> (\<lambda>x. x.[n]))
          ((\<lambda>x f. update (f::('a,'b::finite) array) n x) \<circ> xfrom_bytes)
          (set (toplevel_field_descs (array_tag_n n)))"
  apply (simp add: set_toplevel_field_descs_array_tag_n)
  apply (rule field_desc_independent.intro)
    apply (auto simp add: fu_commutes_def)
  done


lemma component_descs_independent_array_tag_n: "n \<le> CARD('b) 
\<Longrightarrow> component_descs_independent ((array_tag_n::nat \<Rightarrow> ('a::xmem_type,'b::finite) array xtyp_info) n)"
  apply (induct n)
   apply (simp add: atn_base)
  apply (simp add: atn_rec)
  apply (rule wf_xfield.component_descs_independent_ti_typ_combine)
    apply (simp add: wf_xfield_array)
   apply simp
  apply (rule field_desc_independent_extend_array)
  apply simp
  done


lemma component_descs_independent_array: "component_descs_independent (typ_info_t TYPE('a::xmem_type['b::finite]))"
  apply (simp add: typ_info_array array_tag_def)
  apply (rule component_descs_independent_array_tag_n)
  apply simp
  done

lemma complement_padding_extend_array: "n < CARD('b) \<Longrightarrow>
    complement_padding (xto_bytes \<circ> (\<lambda>x. x.[n]))
     ((\<lambda>x f. update (f::('a::xmem_type,'b::finite) array) n x) \<circ> xfrom_bytes) (size_of TYPE('a))"
  apply (unfold_locales)
  by (simp add: complement_padding.complement wf_cfield.intro wf_field_def wf_xfield.intro wf_xfield.padding_lift)


lemma wf_field_desc_extend_array: "n <  CARD('b) \<Longrightarrow> wf_field_desc
          \<lparr>field_access = xto_bytes \<circ> (\<lambda>x. x.[n]),
             field_update = (\<lambda>x f. update (f::('a::xmem_type,'b::finite) array) n x) \<circ> xfrom_bytes,
             field_sz = size_of TYPE('a::xmem_type)\<rparr>"
  apply (intro_locales)
   apply simp
   apply (rule complement_padding_extend_array, assumption)
  apply (unfold_locales)
  by (auto simp add: xfrom_bytes_xto_bytes_inv size_of_def xto_bytes_result_size xto_bytes_size xfrom_bytes_size)

lemma (in xmem_type) wf_field_desc_adjust_array_field: "n  <  CARD('b) \<Longrightarrow> 
 wf_field_descs
          (set (field_descs
                 (adjust_ti (typ_info_t TYPE('a)) (\<lambda>x. x.[n])
                   (\<lambda>x f. update (f::('a,'b::finite) array) n x))))"
  apply (rule wf_field.wf_field_descs_adjust_ti)
  apply (rule wf_field_array, assumption) 
  apply (simp add: wf_field_descs)
  done

lemma wf_field_descs_array_tag_n: "n \<le> CARD('b) 
\<Longrightarrow> wf_field_descs (set (field_descs ((array_tag_n::nat \<Rightarrow> ('a::xmem_type,'b::finite) array xtyp_info) n)))"
  apply (induct n)
   apply (simp add: atn_base)
  apply (simp add: atn_rec)
  apply (simp add: set_field_descs_ti_typ_combine_aggregate)
  apply (simp add: wf_field_desc_extend_array wf_field_desc_adjust_array_field)
  done


lemma wf_field_descs_array: "wf_field_descs (set (field_descs (typ_info_t TYPE('a::xmem_type['b::finite]))))"
  apply (simp add: typ_info_array array_tag_def)
  apply (rule wf_field_descs_array_tag_n)
  apply simp
  done


lemma (in xmem_contained_type) contained_field_descs_array_tag_n: 
"contained_field_descs ((array_tag_n::nat \<Rightarrow> ('a,'b::finite) array xtyp_info) n)"
  apply (induct n)
   apply (simp add: atn_base)
  apply (simp add: atn_rec)
  apply (rule contained_field_descs_ti_typ_combine)
  apply simp
  done

lemma contained_field_descs_array: "contained_field_descs (typ_info_t TYPE('a::xmem_contained_type['b::finite]))"
  apply (simp add: typ_info_array array_tag_def)
  apply (rule contained_field_descs_array_tag_n)
  done

lemma replicate_1_neq_padding: "replicate n CHR ''1'' \<noteq> CHR ''!'' # xs"
  by (cases n) auto

lemma (in xmem_type) wf_padding_array_tag_n: "n \<le> CARD('b) 
\<Longrightarrow> wf_padding ((array_tag_n::nat \<Rightarrow> ('a,'b::finite) array xtyp_info) n)"
  apply (induct n)
   apply (simp add: atn_base wf_padding_combinator_simps)
  apply (simp add: atn_rec wf_padding_ti_typ_combine wf_padding replicate_1_neq_padding)
  done

lemma wf_padding_array: "wf_padding (typ_info_t TYPE('a::xmem_type['b::finite]))"
  apply (simp add: typ_info_array array_tag_def)
  apply (rule wf_padding_array_tag_n)
  apply simp
  done



end
