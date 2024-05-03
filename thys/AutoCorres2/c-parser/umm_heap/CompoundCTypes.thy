(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory CompoundCTypes
  imports
    Vanilla32
    Padding
    Lens
begin

lemma simple_type_dest: "\<not>aggregate t \<Longrightarrow> \<exists>n sz align align' d. t = TypDesc align' (TypScalar sz align d) n"
  apply (cases t)
  subgoal for x1 st n
    apply (cases st)
     apply auto
    done
  done

definition empty_typ_info :: "nat \<Rightarrow> typ_name \<Rightarrow> ('a,'b) typ_desc" where
  "empty_typ_info algn tn \<equiv> TypDesc algn (TypAggregate []) tn"

(*
  More general type, may cause problems in some proofs as type inference
  extend_ti :: "('a,'b) typ_info \<Rightarrow> ('a,'b) typ_info \<Rightarrow> field_name \<Rightarrow> 'b \<Rightarrow> ('a,'b) typ_info" and
  extend_ti_struct :: "('a,'b) typ_info_struct \<Rightarrow> ('a,'b) typ_info \<Rightarrow> field_name \<Rightarrow> 'b \<Rightarrow> ('a,'b) typ_info_struct"

*)
primrec
  extend_ti :: "'a xtyp_info \<Rightarrow> 'a xtyp_info \<Rightarrow> nat \<Rightarrow> field_name \<Rightarrow> 'a field_desc \<Rightarrow> 'a xtyp_info" and
  extend_ti_struct :: "'a xtyp_info_struct \<Rightarrow> 'a xtyp_info \<Rightarrow> field_name \<Rightarrow> 'a field_desc \<Rightarrow> 'a xtyp_info_struct"
where
  et0: "extend_ti (TypDesc algn' st nm) t algn fn d  = TypDesc (max algn' (max algn (align_td t))) (extend_ti_struct st t fn d) nm"

| et1: "extend_ti_struct (TypScalar n sz algn) t fn d = TypAggregate [DTuple t fn d]"
| et2: "extend_ti_struct (TypAggregate ts) t fn d = TypAggregate (ts@[DTuple t fn d])"

lemma aggregate_empty_typ_info [simp]:
  "aggregate (empty_typ_info algn tn)"
  by (simp add: empty_typ_info_def)

lemma aggregate_extend_ti [simp]:
  "aggregate (extend_ti tag t algn f d)"
  apply(cases tag)
  subgoal for x1 typ_struct xs
    apply(cases typ_struct, auto)
    done
  done

lemma typ_name_extend_ti [simp]: "typ_name (extend_ti T t algn fn d) = typ_name T"
  by (cases T) auto

definition update_desc :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b field_desc \<Rightarrow> 'a field_desc" where
  "update_desc acc upd d \<equiv> \<lparr>field_access = (field_access d) \<circ>  acc,
                             field_update = \<lambda>bs v. upd (field_update d bs (acc v)) v, field_sz = field_sz d \<rparr>"

lemma update_desc_id[simp]: "update_desc id (\<lambda>x _. x) = id"
  by (simp add: update_desc_def fun_eq_iff)

term "map_td (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) t"


definition adjust_ti :: "'b xtyp_info \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a xtyp_info" where
  "adjust_ti t acc upd \<equiv> map_td (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) t"

lemma adjust_ti_adjust_ti:
  "adjust_ti (adjust_ti t g s) g' s' =
    adjust_ti t (g \<circ> g') (\<lambda>v x. s' (s v (g' x)) x)"
  by (simp add: adjust_ti_def map_td_map update_desc_def[abs_def] comp_def)

lemma typ_desc_size_update_ti [simp]:
  "(size_td (adjust_ti t acc upd) = size_td t)"
  by (simp add: adjust_ti_def)

lemma export_tag_adjust_ti[rule_format]:
  "\<forall>bs. fg_cons acc upd  \<longrightarrow> wf_fd t \<longrightarrow>
    export_uinfo (adjust_ti t acc upd) = export_uinfo t"
  "\<forall>bs. fg_cons acc upd \<longrightarrow> wf_fd_struct st \<longrightarrow>
    map_td_struct field_norm (\<lambda>_. ()) (map_td_struct (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) st) =
    map_td_struct field_norm (\<lambda>_. ()) st"
  "\<forall>bs. fg_cons acc upd \<longrightarrow> wf_fd_list ts \<longrightarrow>
    map_td_list field_norm (\<lambda>_. ()) (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) ts) =
    map_td_list field_norm (\<lambda>_. ()) ts"
  "\<forall>bs. fg_cons acc upd \<longrightarrow> wf_fd_tuple x \<longrightarrow>
    map_td_tuple field_norm (\<lambda>_. ()) (map_td_tuple (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) x) =
    map_td_tuple field_norm (\<lambda>_. ()) x"
  unfolding adjust_ti_def
  by (induct t and st and ts and x, all \<open>clarsimp simp: export_uinfo_def\<close>)
     (fastforce simp: update_desc_def field_norm_def fg_cons_def fd_cons_struct_def
                      fd_cons_access_update_def fd_cons_desc_def)


definition (in c_type) ti_typ_combine ::
  "'a itself \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> field_name \<Rightarrow> 'b xtyp_info \<Rightarrow> 'b xtyp_info"
  where
  "ti_typ_combine t_b acc upd algn fn tag \<equiv>
     let ft = adjust_ti (typ_info_t TYPE('a)) acc upd
     in extend_ti tag ft algn fn \<lparr>field_access = xto_bytes o acc, field_update = upd o xfrom_bytes, field_sz = size_of TYPE('a)\<rparr>"

primrec
  padding_fields :: "('a,'b) typ_desc \<Rightarrow> field_name list" and
  padding_fields_struct :: "('a,'b) typ_struct \<Rightarrow> field_name list"
where
  pf0: "padding_fields (TypDesc algn st tn) = padding_fields_struct st"

| pf1: "padding_fields_struct (TypScalar n algn d) = []"
| pf2: "padding_fields_struct (TypAggregate xs) = filter (\<lambda>x. hd x = CHR ''!'') (map dt_snd xs)"

primrec
  non_padding_fields :: "('a,'b) typ_desc \<Rightarrow> field_name list" and
  non_padding_fields_struct :: "('a,'b) typ_struct \<Rightarrow> field_name list"
where
  npf0: "non_padding_fields (TypDesc algn st tn) = non_padding_fields_struct st"

| npf1: "non_padding_fields_struct (TypScalar n algn d) = []"
| npf2: "non_padding_fields_struct (TypAggregate xs) = filter (\<lambda>x. hd x \<noteq> CHR ''!'') (map dt_snd xs)"

definition field_names_list :: "('a,'b) typ_desc \<Rightarrow> field_name list" where
  "field_names_list tag \<equiv> non_padding_fields tag @ padding_fields tag"




definition ti_pad_combine :: "nat \<Rightarrow> 'a xtyp_info \<Rightarrow> 'a xtyp_info" where
  "ti_pad_combine n tag \<equiv>
     let
       fn = foldl (@) ''!pad_'' (field_names_list tag);
       td = padding_desc n;
       nf = TypDesc 0 (TypScalar n 0 td) ''!pad_typ''
     in extend_ti tag nf 0 fn td"

lemma aggregate_ti_pad_combine [simp]:
  "aggregate (ti_pad_combine n tag)"
  by (simp add: ti_pad_combine_def Let_def)

definition (in c_type) ti_typ_pad_combine ::
  "'a itself \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> field_name \<Rightarrow> 'b xtyp_info \<Rightarrow> 'b xtyp_info"
  where
  "ti_typ_pad_combine t acc upd algn fn tag \<equiv>
     let
       pad = padup (max (2 ^ algn) (align_of TYPE('a))) (size_td tag);
       ntag = if 0 < pad then ti_pad_combine pad tag else tag
     in
       ti_typ_combine t acc upd algn fn ntag"

definition "map_align f t = (case t of TypDesc algn st n \<Rightarrow> TypDesc (f algn) st n)"
lemma map_align_simp [simp]: "map_align f (TypDesc algn st n) = TypDesc (f algn) st n"
  by (simp add: map_align_def)


definition final_pad :: "nat \<Rightarrow> 'a xtyp_info \<Rightarrow> 'a xtyp_info" where
  "final_pad algn tag \<equiv>
     let n = padup (2^(max algn (align_td tag))) (size_td tag)
     in map_align (max algn) (if 0 < n then ti_pad_combine n tag else tag)"

lemma field_names_list_empty_typ_info [simp]:
  "set (field_names_list (empty_typ_info algn tn)) = {}"
  by (simp add: empty_typ_info_def field_names_list_def)

lemma field_names_list_extend_ti [simp]:
  "set (field_names_list (extend_ti tag t algn fn d)) = set (field_names_list tag) \<union> {fn}"
  unfolding field_names_list_def
  apply(cases tag)
  subgoal for x1 typ_struct xs
    apply(cases typ_struct; simp)
    done
  done

lemma (in c_type) field_names_list_ti_typ_combine [simp]:
  "set (field_names_list (ti_typ_combine (t::'a itself) f f_upd algn fn tag))
     = set (field_names_list tag) \<union> {fn}"
  by (clarsimp simp: ti_typ_combine_def Let_def)

lemma field_names_list_ti_pad_combine [simp]:
  "set (field_names_list (ti_pad_combine n tag))
     = set (field_names_list tag) \<union> {foldl (@) ''!pad_'' (field_names_list tag)}"
  by (clarsimp simp: ti_pad_combine_def Let_def)

\<comment> \<open>matches on padding\<close>
lemma hd_string_hd_fold_eq [simp]:
  "\<lbrakk> s \<noteq> []; hd s = CHR ''!'' \<rbrakk> \<Longrightarrow> hd (foldl (@) s xs) = CHR ''!''"
  by (induct xs arbitrary: s; clarsimp)

lemma field_names_list_ti_typ_pad_combine [simp]:
  "hd x \<noteq> CHR ''!'' \<Longrightarrow>
      x \<in> set (field_names_list (ti_typ_pad_combine align t_b f_ab f_upd_ab fn tag))
          = (x \<in> set (field_names_list tag) \<union> {fn})"
  by (auto simp: ti_typ_pad_combine_def Let_def)

lemma wf_desc_empty_typ_info [simp]:
  "wf_desc (empty_typ_info algn tn)"
  by (simp add: empty_typ_info_def)

lemma wf_desc_extend_ti:
  "\<lbrakk> wf_desc tag; wf_desc t; f \<notin> set (field_names_list tag) \<rbrakk> \<Longrightarrow>
      wf_desc (extend_ti tag t algn f d)"
  unfolding field_names_list_def
  apply(cases tag)
  subgoal for x1 typ_struct xs
    apply(cases typ_struct; clarsimp)
    done
  done

lemma foldl_append_length:
  "length (foldl (@) s xs) \<ge> length s"
  apply(induct xs arbitrary: s, clarsimp)
  subgoal for  a list s
    apply(drule meta_spec [where x="s@a"])
    apply clarsimp
    done
  done

lemma foldl_append_nmem:
  "s \<noteq> [] \<Longrightarrow> foldl (@) s xs \<notin> set xs"
  apply(induct xs arbitrary: s, clarsimp)
  subgoal for a list s
  apply(drule meta_spec [where x="s@a"])
    apply clarsimp
    by (metis add_le_same_cancel2 foldl_append_length le_zero_eq length_0_conv length_append)
  done

lemma wf_desc_ti_pad_combine:
  "wf_desc tag \<Longrightarrow> wf_desc (ti_pad_combine n tag)"
  apply(clarsimp simp: ti_pad_combine_def Let_def)
  apply(erule wf_desc_extend_ti)
   apply simp
  apply(rule foldl_append_nmem, simp)
  done

lemma wf_desc_adjust_ti [simp]:
  "wf_desc (adjust_ti t f g) = wf_desc (t::'a xtyp_info)"
  by (simp add: adjust_ti_def wf_desc_map)

lemma (in wf_type) wf_desc_ti_typ_combine:
  "\<lbrakk> wf_desc tag; fn \<notin> set (field_names_list tag) \<rbrakk> \<Longrightarrow>
    wf_desc (ti_typ_combine (t_b::'a itself) acc upd_ab algn fn tag)"
  by (fastforce simp: ti_typ_combine_def Let_def elim: wf_desc_extend_ti)

lemma (in wf_type) wf_desc_ti_typ_pad_combine:
  "\<lbrakk> wf_desc tag;  fn \<notin> set (field_names_list tag); hd fn \<noteq> CHR ''!'' \<rbrakk> \<Longrightarrow>
   wf_desc (ti_typ_pad_combine (t_b::'a itself) acc upd algn fn tag)"
  unfolding ti_typ_pad_combine_def Let_def
  by (auto intro!: wf_desc_ti_typ_combine wf_desc_ti_pad_combine)

lemma wf_desc_map_align: "wf_desc tag \<Longrightarrow> wf_desc (map_align f tag)"
  by (cases tag) (simp)

lemma wf_desc_final_pad:
  "wf_desc tag \<Longrightarrow> wf_desc (final_pad algn tag)"
  by (auto simp: final_pad_def Let_def wf_desc_map_align wf_desc_ti_pad_combine)

lemma wf_size_desc_extend_ti:
  "\<lbrakk> wf_size_desc tag; wf_size_desc t \<rbrakk> \<Longrightarrow> wf_size_desc (extend_ti tag t algn fn d)"
  apply(cases tag)
  subgoal for x1 typ_struct list
    apply(cases typ_struct, auto)
    done
  done

lemma wf_size_desc_ti_pad_combine:
  "\<lbrakk> wf_size_desc tag; 0 < n \<rbrakk> \<Longrightarrow> wf_size_desc (ti_pad_combine n tag)"
  by (fastforce simp: ti_pad_combine_def Let_def elim: wf_size_desc_extend_ti)

lemma wf_size_desc_adjust_ti:
  "wf_size_desc (adjust_ti t f g) = wf_size_desc (t::'a xtyp_info)"
  by (simp add: adjust_ti_def wf_size_desc_map)

lemma (in wf_type) wf_size_desc_ti_typ_combine:
  "wf_size_desc tag \<Longrightarrow> wf_size_desc (ti_typ_combine (t_b::'a itself) acc upd_ab algn fn tag)"
  by (fastforce simp: wf_size_desc_adjust_ti ti_typ_combine_def Let_def elim: wf_size_desc_extend_ti)

lemma (in wf_type) wf_size_desc_ti_typ_pad_combine:
  "wf_size_desc tag \<Longrightarrow>
    wf_size_desc (ti_typ_pad_combine (t_b::'a itself) acc upd algn fn tag)"
  by (auto simp: ti_typ_pad_combine_def Let_def
           intro: wf_size_desc_ti_typ_combine
           elim: wf_size_desc_ti_pad_combine)

lemma (in wf_type) wf_size_desc_ti_typ_combine_empty [simp]:
  "wf_size_desc (ti_typ_combine (t_b::'a itself) acc upd algn fn (empty_typ_info algn' tn))"
  by (clarsimp simp: ti_typ_combine_def Let_def empty_typ_info_def wf_size_desc_adjust_ti)

lemma (in wf_type) wf_size_desc_ti_typ_pad_combine_empty [simp]:
  "wf_size_desc (ti_typ_pad_combine (t_b::'a itself) acc upd algn fn
      (empty_typ_info algn' tn))"
  by (clarsimp simp: ti_typ_pad_combine_def Let_def ti_typ_combine_def empty_typ_info_def
                     ti_pad_combine_def wf_size_desc_adjust_ti)

lemma wf_size_desc_msp_align:
  "wf_size_desc tag \<Longrightarrow> wf_size_desc (map_align f tag)"
  by (cases tag) (simp add: wf_size_desc_def)

lemma wf_size_desc_final_pad:
  "wf_size_desc tag \<Longrightarrow> wf_size_desc (final_pad algn tag)"
  by (fastforce simp: final_pad_def Let_def wf_size_desc_msp_align wf_size_desc_ti_pad_combine)

lemma wf_fdp_set_comp_simp [simp]:
  "wf_fdp {(a, n # b) |a b. (a, b) \<in> tf_set t} = wf_fdp (tf_set t)"
  unfolding wf_fdp_def by fastforce

lemma lf_set_adjust_ti':
  "\<forall>d fn. d \<in> lf_set (map_td (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) t) fn \<longrightarrow>
      (\<exists>y. lf_fd d=update_desc acc upd (lf_fd y) \<and> lf_sz d=lf_sz y \<and> lf_fn d=lf_fn y \<and> y \<in> lf_set t fn)"
  "\<forall>d fn. d \<in> lf_set_struct (map_td_struct (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) st) fn \<longrightarrow>
      (\<exists>y. lf_fd d=update_desc acc upd (lf_fd y) \<and> lf_sz d=lf_sz y \<and> lf_fn d=lf_fn y \<and> y \<in> lf_set_struct st fn)"
  "\<forall>d fn. d \<in> lf_set_list (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) ts) fn \<longrightarrow>
      (\<exists>y. lf_fd d=update_desc acc upd (lf_fd y) \<and> lf_sz d=lf_sz y \<and> lf_fn d=lf_fn y \<and> y \<in> lf_set_list ts fn)"
  "\<forall>d fn. d \<in> lf_set_tuple (map_td_tuple (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) x) fn \<longrightarrow>
      (\<exists>y. lf_fd d=update_desc acc upd (lf_fd y) \<and> lf_sz d=lf_sz y \<and> lf_fn d=lf_fn y \<and> y \<in> lf_set_tuple x fn)"
  unfolding update_desc_def
  by (induct t and st and ts and x) fastforce+

lemma lf_set_adjust_ti:
  "\<lbrakk> d \<in> lf_set (adjust_ti t acc upd) fn; \<And>y. upd (acc y) y = y \<rbrakk> \<Longrightarrow>
      (\<exists>y. lf_fd d=update_desc acc upd (lf_fd y) \<and> lf_sz d=lf_sz y \<and> lf_fn d=lf_fn y \<and> y \<in> lf_set t fn)"
  by (simp add: lf_set_adjust_ti' adjust_ti_def)

lemma fd_cons_struct_id_simp [simp]:
  "fd_cons_struct (TypScalar n algn \<lparr>field_access = \<lambda>v. id, field_update = \<lambda>bs. id, field_sz = m\<rparr>)"
  by (auto simp: fd_cons_struct_def fd_cons_double_update_def
                 fd_cons_update_access_def fd_cons_access_update_def fd_cons_length_def
                 fd_cons_update_normalise_def fd_cons_desc_def)


lemma field_desc_adjust_ti:
  "fg_cons acc upd \<longrightarrow>
     field_desc (adjust_ti (t::'a xtyp_info) acc upd) =
     update_desc acc upd (field_desc t)"
  "fg_cons acc upd \<longrightarrow>
     field_desc_struct (map_td_struct (\<lambda>n algn. update_desc  acc upd) (update_desc acc upd) st) =
     update_desc  acc upd (field_desc_struct st)"
  "fg_cons acc upd \<longrightarrow>
     field_desc_list (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) ts) =
     update_desc acc upd (field_desc_list ts)"
  "fg_cons acc upd \<longrightarrow>
     field_desc_tuple (map_td_tuple (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) x) =
     update_desc acc upd (field_desc_tuple x)"
  unfolding adjust_ti_def
     by (induct t and st and ts and x) (fastforce simp: fg_cons_def update_desc_def update_ti_t_struct_t)+

lemma update_ti_t_adjust_ti:
  "fg_cons acc upd \<Longrightarrow> update_ti_t (adjust_ti t acc upd) bs v = upd (update_ti_t t bs (acc v)) v"
  using field_desc_adjust_ti(1) [of acc upd t]
  by (clarsimp simp: update_desc_def)

declare field_desc_def [simp del]

lemma (in c_type) aggregate_ti_typ_combine [simp]:
  "aggregate (ti_typ_combine (t_b::'a itself) acc upd algn fn tag)"
  by (simp add: ti_typ_combine_def Let_def)

lemma (in c_type) aggregate_ti_typ_pad_combine [simp]:
  "aggregate (ti_typ_pad_combine (t_b::'a itself) acc upd algn fn tag)"
  by (simp add: ti_typ_pad_combine_def Let_def)

lemma align_of_empty_typ_info [simp]:
  "align_td_wo_align (empty_typ_info algn tn) = 0"
  by (simp add: empty_typ_info_def)

lemma align_of_empty_typ_info' [simp]:
  "align_td (empty_typ_info algn tn) = algn"
  by (simp add: empty_typ_info_def)

lemma align_of_tag_list [simp]:
  "align_td_wo_align_list (xs @ [DTuple t fn d]) = max (align_td_wo_align_list xs) (align_td_wo_align t)"
  by (induct xs) auto

lemma align_of_tag_list' [simp]:
  "align_td_list (xs @ [DTuple t fn d]) = max (align_td_list xs) (align_td t)"
  by (induct xs) auto

lemma align_of_extend_ti [simp]:
  "aggregate ti \<Longrightarrow> align_td_wo_align (extend_ti ti t algn fn d) = max (align_td_wo_align ti) (align_td_wo_align t)"
  apply (cases ti)
  subgoal for x1 typ_struct xs
    apply (cases typ_struct; clarsimp)
    done
  done

lemma align_of_extend_ti' [simp]:
  "aggregate ti \<Longrightarrow> align_td (extend_ti ti t algn fn d) = max (align_td ti) (max algn (align_td t))"
  apply (cases ti)
  subgoal for x1 typ_struct xs
    apply (cases typ_struct; clarsimp)
    done
  done

lemma align_of_adjust_ti [simp]:
  "align_td_wo_align (adjust_ti t acc upd) = align_td_wo_align (t::'a xtyp_info)"
  by (simp add: adjust_ti_def)

lemma align_of_adjust_ti' [simp]:
  "align_td (adjust_ti t acc upd) = align_td (t::'a xtyp_info)"
  by (simp add: adjust_ti_def)

lemma (in c_type) align_of_ti_typ_combine [simp]:
  "aggregate ti \<Longrightarrow>
     align_td_wo_align (ti_typ_combine (t::'a itself) acc upd algn fn ti) =
     max (align_td_wo_align ti) (align_td_wo_align (typ_info_t (TYPE('a))))"
  by (clarsimp simp: ti_typ_combine_def Let_def align_of_def)

lemma (in c_type) align_of_ti_typ_combine' [simp]:
  "aggregate ti \<Longrightarrow>
     align_td (ti_typ_combine (t::'a itself) acc upd algn fn ti) =
     max (align_td ti) (max algn (align_td (typ_info_t TYPE('a))))"
  by (clarsimp simp: ti_typ_combine_def Let_def align_of_def)

lemma align_of_ti_pad_combine [simp]:
  "aggregate ti \<Longrightarrow> align_td_wo_align (ti_pad_combine n ti) = (align_td_wo_align ti)"
  by (clarsimp simp: ti_pad_combine_def Let_def max_def)

lemma align_of_ti_pad_combine' [simp]:
  "aggregate ti \<Longrightarrow> align_td (ti_pad_combine n ti) = (align_td ti)"
  by (clarsimp simp: ti_pad_combine_def Let_def max_def)

lemma max_2_exp: "max ((2::nat) ^ a) (2 ^ b) = 2 ^ (max a b)"
  by (simp add: max_def)

lemma align_td_wo_align_map_align: "align_td_wo_align (map_align f t) = align_td_wo_align t"
  by (cases t) simp

lemma align_td_wo_align_final_pad:
  "aggregate ti \<Longrightarrow>
  align_td_wo_align (final_pad algn ti) = (align_td_wo_align ti)"
  by (simp add: final_pad_def Let_def  padup_def align_td_wo_align_map_align)

lemma align_td_map_align [simp]: "align_td (map_align f t) = f (align_td t)"
  by (cases t) simp

lemma align_of_final_pad:
  "aggregate ti \<Longrightarrow>
  align_td (final_pad algn ti) = max algn (align_td ti)"
  by (simp add: final_pad_def Let_def  padup_def align_td_map_align )


lemma (in c_type) align_td_wo_align_ti_typ_pad_combine [simp]:
  "aggregate ti \<Longrightarrow>
     align_td_wo_align (ti_typ_pad_combine (t::'a itself) acc upd algn fn ti) =
     max (align_td_wo_align ti) (align_td_wo_align (typ_info_t TYPE('a)))"
  by (clarsimp simp: ti_typ_pad_combine_def Let_def)

lemma (in c_type) align_td_ti_typ_pad_combine [simp]:
  "aggregate ti \<Longrightarrow>
     align_td (ti_typ_pad_combine (t::'a itself) acc upd algn fn ti) =
     max (align_td ti) (max algn (align_td (typ_info_t TYPE('a))))"
  by (clarsimp simp: ti_typ_pad_combine_def Let_def)

definition fu_s_comm_set :: "(byte list \<Rightarrow> 'a \<Rightarrow> 'a) set \<Rightarrow> (byte list \<Rightarrow> 'a \<Rightarrow> 'a) set \<Rightarrow> bool"
  where
  "fu_s_comm_set X Y \<equiv> \<forall>x y. x \<in> X \<and> y \<in> Y \<longrightarrow> (\<forall>v bs bs'. x bs (y bs' v) = y bs' (x bs v))"

lemma fc_empty_ti [simp]:
  "fu_commutes (update_ti_t (empty_typ_info algn tn)) f"
  by (auto simp: fu_commutes_def empty_typ_info_def)

lemma fc_extend_ti:
  "\<lbrakk> fu_commutes (update_ti_t s) h; fu_commutes (update_ti_t t) h \<rbrakk>
      \<Longrightarrow> fu_commutes (update_ti_t (extend_ti s t algn fn d)) h"
  apply(cases s)
  subgoal for x1 typ_struct xs
    apply(cases typ_struct, auto simp: fu_commutes_def)
    done
  done

lemma fc_update_ti:
  "\<lbrakk> fu_commutes (update_ti_t ti) h; fg_cons acc upd;
     \<forall>v bs bs'. upd bs (h bs' v) = h bs' (upd bs v); \<forall>bs v. acc (h bs v) = acc v  \<rbrakk>
   \<Longrightarrow> fu_commutes (update_ti_t (adjust_ti t acc upd)) h"
  by (auto simp: fu_commutes_def update_ti_t_adjust_ti)

lemma (in c_type) fc_ti_typ_combine:
  "\<lbrakk> fu_commutes (update_ti_t ti) h; fg_cons acc upd;
     \<forall>v bs bs'. upd bs (h bs' v) = h bs' (upd bs v); \<forall>bs v. acc (h bs v) = acc v \<rbrakk>
   \<Longrightarrow> fu_commutes (update_ti_t (ti_typ_combine (t::'a itself) acc upd algn fn ti)) h"
  apply(clarsimp simp: ti_typ_combine_def Let_def)
  apply(rule fc_extend_ti, assumption)
  apply(rule fc_update_ti; simp)
  done

lemma fc_ti_pad_combine:
  "fu_commutes (update_ti_t ti) f \<Longrightarrow> fu_commutes (update_ti_t (ti_pad_combine n ti)) f"
  apply(clarsimp simp: ti_pad_combine_def Let_def)
  apply(rule fc_extend_ti, assumption)
  apply(auto simp: fu_commutes_def padding_desc_def)
  done

lemma (in c_type) fc_ti_typ_pad_combine:
  "\<lbrakk> fu_commutes (update_ti_t ti) h; fg_cons acc upd;
     \<forall>v bs bs'. upd bs (h bs' v) = h bs' (upd bs v); \<forall>bs v. acc (h bs v) = acc v \<rbrakk>
   \<Longrightarrow> fu_commutes (update_ti_t (ti_typ_pad_combine (t::'a itself) acc upd algn fn ti)) h"
  apply(clarsimp simp: ti_typ_pad_combine_def Let_def)
  apply(rule conjI; clarsimp)
   apply(rule fc_ti_typ_combine; assumption?)
   apply(erule fc_ti_pad_combine)
  apply(erule (3) fc_ti_typ_combine)
  done

definition fu_eq_mask :: "'a xtyp_info \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "fu_eq_mask ti f \<equiv>
     \<forall>bs v v'. length bs = size_td ti \<longrightarrow> update_ti_t ti bs (f v) = update_ti_t ti bs (f v')"

lemma fu_eq_mask:
  "\<lbrakk> length bs = size_td ti; fu_eq_mask ti id  \<rbrakk> \<Longrightarrow>
      update_ti_t ti bs v = update_ti_t ti bs w"
 by (clarsimp simp: fu_eq_mask_def update_ti_t_def)

lemma fu_eq_mask_ti_pad_combine:
  "\<lbrakk> fu_eq_mask ti f; aggregate ti \<rbrakk> \<Longrightarrow> fu_eq_mask (ti_pad_combine n ti) f"
  unfolding ti_pad_combine_def Let_def
  apply(cases ti)
  subgoal for x1 typ_struct xs
    apply(cases typ_struct, auto simp: fu_eq_mask_def update_ti_list_t_def padding_desc_def)
    done
  done

lemma fu_eq_mask_map_align: "fu_eq_mask t f \<Longrightarrow> fu_eq_mask (map_align g t) f"
  by (cases t) (auto simp add: fu_eq_mask_def)

lemma fu_eq_mask_final_pad:
  "\<lbrakk> fu_eq_mask ti f; aggregate ti \<rbrakk> \<Longrightarrow> fu_eq_mask (final_pad algn ti) f"
  by(auto simp: final_pad_def Let_def fu_eq_mask_map_align fu_eq_mask_ti_pad_combine)

definition upd_local :: "('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "upd_local g \<equiv> \<forall>j k v v'. g k v = g k v' \<longrightarrow> g j v = g j v'"

lemma fg_cons_upd_local:
  "fg_cons f g \<Longrightarrow> upd_local g"
  apply(clarsimp simp: fg_cons_def upd_local_def)
  subgoal for j k v v'
    apply(drule arg_cong [where f="g j"])
    apply simp
    done
  done

lemma (in mem_type) fu_eq_mask_ti_typ_combine:
  "\<lbrakk> fu_eq_mask ti (\<lambda>v. (upd (acc undefined) (h v))); fg_cons acc upd;
      fu_commutes (update_ti_t ti) upd; aggregate ti \<rbrakk> \<Longrightarrow>
      fu_eq_mask (ti_typ_combine (t::'a itself) acc upd algn fn ti) h"
  apply(frule fg_cons_upd_local)
  apply(clarsimp simp: ti_typ_combine_def Let_def)
  apply(cases ti)
  subgoal for x1 typ_struct xs
    apply(cases typ_struct; clarsimp)
    subgoal for xs'
      apply(clarsimp simp: fu_eq_mask_def update_ti_t_adjust_ti)
      apply(clarsimp simp: update_ti_list_t_def size_of_def)
      apply(subst upd [where w="acc undefined"])
       apply(simp add: size_of_def)
      apply(subst upd [where w="acc undefined" and v="acc (h v')" for v'])
       apply(simp add: size_of_def)
      apply (smt (verit, ccfv_threshold) fu_commutes_def length_take min_ll upd_local_def)
      done
    done
  done

lemma (in mem_type) fu_eq_mask_ti_typ_pad_combine:
  "\<lbrakk> fu_eq_mask ti (\<lambda>v. (upd (acc undefined) (h v))); fg_cons acc upd;
      fu_commutes (update_ti_t ti) upd; aggregate ti \<rbrakk> \<Longrightarrow>
      fu_eq_mask (ti_typ_pad_combine (t::'a itself) acc upd algn fn ti) h"
  by (fastforce simp: ti_typ_pad_combine_def Let_def
                intro: fu_eq_mask_ti_typ_combine fu_eq_mask_ti_pad_combine fc_ti_pad_combine)

lemma fu_eq_mask_empty_typ_info_g:
  "\<exists>k. \<forall>v. f v = k \<Longrightarrow> fu_eq_mask t f"
  by (auto simp: fu_eq_mask_def)

lemma fu_eq_mask_empty_typ_info:
  "\<forall>v. f v = undefined \<Longrightarrow> fu_eq_mask t f"
 by (auto simp: fu_eq_mask_def)

lemma size_td_extend_ti:
  "aggregate s \<Longrightarrow> size_td (extend_ti s t algn fn d) = size_td s + size_td t"
  apply (cases s) 
  subgoal for x1 typ_struct xs 
    apply (cases typ_struct; simp)
    done
  done

lemma size_td_ti_pad_combine:
  "aggregate ti \<Longrightarrow> size_td (ti_pad_combine n ti) = n + size_td ti"
  unfolding ti_pad_combine_def Let_def by (simp add: size_td_extend_ti)

lemma size_td_map_align [simp]: "size_td (map_align f ti) = size_td ti"
  by (cases ti) auto

lemma align_of_dvd_size_of_final_pad [simp]:
  "aggregate ti \<Longrightarrow> 2^align_td (final_pad algn ti) dvd size_td (final_pad algn ti)"
  unfolding final_pad_def Let_def
  apply (cases ti)
  apply (auto simp: size_td_ti_pad_combine ac_simps padup_dvd power_le_dvd  intro: dvd_padup_add)
  done

lemma size_td_lt_ti_pad_combine:
  "aggregate t \<Longrightarrow> size_td (ti_pad_combine n t) = size_td t + n"
  by (metis add.commute size_td_ti_pad_combine)

lemma (in c_type) size_td_lt_ti_typ_combine:
  "aggregate ti \<Longrightarrow>
    size_td (ti_typ_combine (t::'a itself) f g algn fn ti) =
    size_td ti + size_td (typ_info_t TYPE('a))"
  by (clarsimp simp: ti_typ_combine_def Let_def size_td_extend_ti)

lemma (in c_type) size_td_lt_ti_typ_pad_combine:
  "aggregate ti  \<Longrightarrow>
      size_td (ti_typ_pad_combine (t::'a itself) f g algn fn ti) =
        (let k = size_td ti in
           k + size_td (typ_info_t TYPE('a)) + padup (2^(max algn (align_td (typ_info_t TYPE('a))))) k)"
  unfolding ti_typ_pad_combine_def Let_def
  by (auto simp: size_td_lt_ti_typ_combine size_td_ti_pad_combine align_of_def max_2_exp)

lemma size_td_lt_final_pad:
  "aggregate tag \<Longrightarrow>
   size_td (final_pad align tag) = (let k=size_td tag in k + padup (2^(max align (align_td tag))) k)"
  by (auto simp: final_pad_def Let_def size_td_ti_pad_combine)

lemma size_td_empty_typ_info [simp]:
  "size_td (empty_typ_info algn tn) = 0"
  by (clarsimp simp: empty_typ_info_def)

lemma wf_lf_empty_typ_info [simp]:
  "wf_lf {}"
  by (auto simp: wf_lf_def empty_typ_info_def)

lemma lf_fn_disj_fn:
  "fn \<notin> set (field_names_list (TypDesc algn (TypAggregate xs) tn)) \<Longrightarrow>
   lf_fn ` lf_set_list xs [] \<inter> lf_fn ` lf_set t [fn] = {}"
  apply(induct xs arbitrary: fn t tn, clarsimp)
  subgoal for  a list fn t tn
  apply(cases a, clarsimp)
  apply(drule meta_spec [where x=fn])
  apply(drule meta_spec [where  x=t])
  apply(drule meta_spec [where  x=tn])
  apply(drule meta_mp, fastforce simp: field_names_list_def split: if_split_asm)
  apply(safe)
   apply(fastforce dest!: lf_set_fn simp: field_names_list_def prefix_def less_eq_list_def
                  split: if_split_asm)
    by force
  done


lemma wf_lf_extend_ti:
  "\<lbrakk> wf_lf (lf_set t []); wf_lf (lf_set ti []); wf_desc t; fn \<notin> set (field_names_list ti);
     ti_ind (lf_set ti []) (lf_set t []) \<rbrakk> \<Longrightarrow>
   wf_lf (lf_set (extend_ti ti t algn fn d) [])"
  apply(cases ti)
  subgoal for x1 typ_struct xs
    apply(cases typ_struct; clarsimp)
     apply(subst wf_lf_fn; simp)
    apply(subst wf_lf_list, erule lf_fn_disj_fn)
    apply(subst ti_ind_sym2)
    apply(subst ti_ind_fn)
    apply(subst ti_ind_sym2)
    apply clarsimp
    apply(subst wf_lf_fn; simp)
    done
  done

lemma wf_lf_ti_pad_combine:
  "wf_lf (lf_set ti []) \<Longrightarrow> wf_lf (lf_set (ti_pad_combine n ti) [])"
  apply(clarsimp simp: ti_pad_combine_def Let_def padding_desc_def)
  apply(rule wf_lf_extend_ti)
      apply(clarsimp simp: wf_lf_def fd_cons_desc_def fd_cons_double_update_def
                           fd_cons_update_access_def fd_cons_access_update_def fd_cons_length_def)
     apply assumption
    apply(clarsimp)
   apply(rule foldl_append_nmem)
   apply clarsimp
  apply(clarsimp simp: ti_ind_def fu_commutes_def fa_fu_ind_def)
  done

lemma lf_set_map_align [simp]: "lf_set (map_align f ti) = lf_set ti"
  by (cases ti) auto

lemma wf_lf_final_pad:
  "wf_lf (lf_set ti []) \<Longrightarrow> wf_lf (lf_set (final_pad algn ti) [])"
  by (auto simp: final_pad_def Let_def elim: wf_lf_ti_pad_combine)

lemma wf_lf_adjust_ti:
  "\<lbrakk> wf_lf (lf_set t []); \<And>v. g (f v) v = v;
      \<And>bs bs' v. g bs (g bs' v) = g bs v; \<And>bs v. f (g bs v) = bs \<rbrakk>
      \<Longrightarrow> wf_lf (lf_set (adjust_ti t f g) [])"
  apply(clarsimp simp: wf_lf_def)
  apply(drule lf_set_adjust_ti; clarsimp)
  apply(rule conjI)
   apply(fastforce simp: fd_cons_desc_def fd_cons_double_update_def update_desc_def
                         fd_cons_update_access_def fd_cons_access_update_def fd_cons_length_def)
  apply(fastforce simp: fu_commutes_def update_desc_def fa_fu_ind_def dest!: lf_set_adjust_ti)
  done

lemma ti_ind_empty_typ_info [simp]:
  "ti_ind (lf_set (empty_typ_info algn tn) []) (lf_set (adjust_ti k f g) [])"
  by (clarsimp simp: ti_ind_def empty_typ_info_def)

lemma ti_ind_extend_ti:
  "\<lbrakk> ti_ind (lf_set t []) (lf_set (adjust_ti k acc upd) []);
      ti_ind (lf_set ti []) (lf_set (adjust_ti k acc upd) []) \<rbrakk>
      \<Longrightarrow> ti_ind (lf_set (extend_ti ti t algn n d) []) (lf_set (adjust_ti k acc upd) [])"
  apply(cases ti)
  subgoal for x1 typ_struct xs
    apply(cases typ_struct; clarsimp, subst ti_ind_fn, simp)
    done
  done

lemma ti_ind_ti_pad_combine:
  "ti_ind (lf_set ti []) (lf_set (adjust_ti k acc upd) []) \<Longrightarrow>
      ti_ind (lf_set (ti_pad_combine n ti) []) (lf_set (adjust_ti k acc upd) [])"
  apply(clarsimp simp: ti_pad_combine_def Let_def padding_desc_def)
  apply(rule ti_ind_extend_ti)
   apply(clarsimp simp: ti_ind_def fu_commutes_def fa_fu_ind_def)
  apply assumption
  done

definition acc_ind :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a field_desc set \<Rightarrow> bool" where
  "acc_ind acc X \<equiv> \<forall>x bs v. x \<in> X \<longrightarrow> acc (field_update x bs v) = acc v"

definition fu_s_comm_k :: "'a leaf_desc set \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "fu_s_comm_k X upd \<equiv> \<forall>x. x \<in> field_update ` lf_fd ` X \<longrightarrow> fu_commutes x upd"

definition upd_ind :: "'a leaf_desc set \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "upd_ind X upd \<equiv> fu_s_comm_k X upd"

definition fa_ind :: "'a field_desc set \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "fa_ind X upd \<equiv> \<forall>x bs v. x \<in> X \<longrightarrow> field_access x (upd bs v) = field_access x v"

lemma lf_fd_fn:
  "\<forall>fn. lf_fd ` (lf_set (t::'a xtyp_info) fn) = lf_fd ` (lf_set t [])"
  "\<forall>fn. lf_fd ` (lf_set_struct (st::'a xtyp_info_struct) fn) = lf_fd ` (lf_set_struct st [])"
  "\<forall>fn. lf_fd ` (lf_set_list (ts::'a xtyp_info_tuple list) fn) = lf_fd ` (lf_set_list ts [])"
  "\<forall>fn. lf_fd ` (lf_set_tuple (x::'a xtyp_info_tuple) fn) = lf_fd ` (lf_set_tuple x [])"
  by (induct t and st and ts and x, all \<open>clarsimp simp: image_Un\<close>) metis+

lemma lf_set_empty_typ_info [simp]:
  "lf_set (empty_typ_info algn tn) fn = {}"
  by (clarsimp simp: empty_typ_info_def)

lemma upd_ind_empty [simp]:
  "upd_ind {} upd"
  by (clarsimp simp: upd_ind_def fu_s_comm_k_def)

lemma upd_ind_extend_ti:
  "\<lbrakk> upd_ind (lf_set s []) upd; upd_ind (lf_set t []) upd \<rbrakk> \<Longrightarrow>
      upd_ind (lf_set (extend_ti s t algn fn d) []) upd"
  apply (cases s)
  subgoal for x1 typ_struct xs
    apply (cases typ_struct)
    subgoal 
      apply (simp add:  upd_ind_def image_Un fu_s_comm_k_def )
      by (metis lf_fd_fn(1))
    subgoal 
      apply (simp add:  upd_ind_def image_Un fu_s_comm_k_def )
      by (metis lf_fd_fn(1))
    done
  done


lemma (in c_type) upd_ind_ti_typ_combine:
  "\<lbrakk> upd_ind (lf_set ti []) h; \<And>w u v. upd w (h u v) = h u (upd w v);
      \<And>w v. acc (h w v) = acc v; \<And>v. upd (acc v) v = v \<rbrakk>
      \<Longrightarrow> upd_ind (lf_set (ti_typ_combine (t::'a itself) acc upd algn fn ti) []) h"
  apply(clarsimp simp: ti_typ_combine_def Let_def)
  apply(erule upd_ind_extend_ti)
  apply(clarsimp simp: upd_ind_def fu_s_comm_k_def)
  apply(drule lf_set_adjust_ti)
   apply clarsimp
  apply(clarsimp simp: update_desc_def fu_commutes_def )
  done

lemma upd_ind_ti_pad_combine:
  "upd_ind ((lf_set ti [])) upd \<Longrightarrow> upd_ind ((lf_set (ti_pad_combine n ti) [])) upd"
  apply(clarsimp simp: ti_pad_combine_def Let_def padding_desc_def)
  apply(erule upd_ind_extend_ti)
  apply(auto simp: upd_ind_def fu_s_comm_k_def fu_commutes_def)
  done

lemma (in c_type) upd_ind_ti_typ_pad_combine:
  "\<lbrakk> upd_ind (lf_set ti []) h; \<And>w u v. upd w (h u v) = h u (upd w v);
      \<And>w v. acc (h w v) = acc v; \<And>v. upd (acc v) v = v \<rbrakk>
      \<Longrightarrow> upd_ind (lf_set (ti_typ_pad_combine (t::'a itself) acc upd algn fn ti) []) h"
  unfolding ti_typ_pad_combine_def Let_def
  by (fastforce intro!: upd_ind_ti_typ_combine upd_ind_ti_pad_combine)

lemma acc_ind_empty [simp]:
  "acc_ind acc {}"
  by (clarsimp simp: acc_ind_def)

lemma acc_ind_extend_ti:
  "\<lbrakk> acc_ind acc (lf_fd ` lf_set s []); acc_ind acc (lf_fd ` lf_set t []) \<rbrakk> \<Longrightarrow>
      acc_ind acc (lf_fd ` lf_set (extend_ti s t algn fn d) [])"
  apply (cases s)
  subgoal for x1 typ_struct xs
    apply (cases typ_struct)
    subgoal 
      apply (simp add: acc_ind_def image_Un fu_s_comm_k_def )
      by (metis lf_fd_fn(1))
    subgoal 
      apply (simp add:  acc_ind_def image_Un fu_s_comm_k_def )
      by (metis lf_fd_fn(1))
    done
  done

lemma (in c_type) acc_ind_ti_typ_combine:
  "\<lbrakk> acc_ind h (lf_fd ` lf_set ti []); \<And>v w. h (upd w v) = h v;
      \<And>v. upd (acc v) v = v  \<rbrakk>
      \<Longrightarrow> acc_ind h (lf_fd ` lf_set (ti_typ_combine (t::'a itself) acc upd algn fn ti) [])"
  apply(clarsimp simp: ti_typ_combine_def Let_def)
  apply(erule acc_ind_extend_ti)
  apply(clarsimp simp: acc_ind_def)
  apply(drule lf_set_adjust_ti)
   apply clarsimp
  apply(clarsimp simp: update_desc_def)
  done

lemma acc_ind_ti_pad_combine:
  "acc_ind acc (lf_fd ` (lf_set t [])) \<Longrightarrow> acc_ind acc (lf_fd ` (lf_set (ti_pad_combine n t) []))"
  apply(clarsimp simp: ti_pad_combine_def Let_def padding_desc_def)
  apply(erule acc_ind_extend_ti)
  apply(auto simp: acc_ind_def)
  done

lemma (in c_type) acc_ind_ti_typ_pad_combine:
  "\<lbrakk> acc_ind h (lf_fd ` lf_set ti []); \<And>v w. h (upd w v) = h v; \<And>v. upd (acc v) v = v  \<rbrakk>
      \<Longrightarrow> acc_ind h (lf_fd ` lf_set (ti_typ_pad_combine (t::'a itself) acc upd algn fn ti) [])"
  by (auto simp: ti_typ_pad_combine_def Let_def intro: acc_ind_ti_typ_combine acc_ind_ti_pad_combine)

lemma fa_ind_empty [simp]:
  "fa_ind {} upd"
  by (clarsimp simp: fa_ind_def)

lemma fa_ind_extend_ti:
  "\<lbrakk> fa_ind (lf_fd ` lf_set s []) upd; fa_ind (lf_fd ` lf_set t []) upd \<rbrakk> \<Longrightarrow>
      fa_ind (lf_fd ` lf_set (extend_ti s t algn fn d) []) upd"
  apply (cases s)
  subgoal for x1 typ_struct xs
    apply (cases typ_struct)
    subgoal 
      apply (simp add: fa_ind_def image_Un fu_s_comm_k_def )
      by (metis lf_fd_fn(1))
    subgoal 
      apply (simp add:  fa_ind_def image_Un fu_s_comm_k_def )
      by (metis lf_fd_fn(1))
    done
  done
 
lemma (in c_type) fa_ind_ti_typ_combine:
  "\<lbrakk> fa_ind (lf_fd ` lf_set ti []) h; \<And>v w. acc (h w v) = acc v;
      \<And>v. upd (acc v) v = v   \<rbrakk>
      \<Longrightarrow> fa_ind (lf_fd ` lf_set (ti_typ_combine (t::'a itself) acc upd algn fn ti) []) h"
  apply(clarsimp simp: ti_typ_combine_def Let_def)
  apply(erule fa_ind_extend_ti)
  apply(clarsimp simp: fa_ind_def fu_s_comm_k_def)
  apply(drule lf_set_adjust_ti)
   apply clarsimp
  apply(clarsimp simp: update_desc_def fu_commutes_def)
  done

lemma fa_ind_ti_pad_combine:
  "fa_ind (lf_fd ` (lf_set ti [])) upd \<Longrightarrow> fa_ind (lf_fd ` (lf_set (ti_pad_combine n ti) [])) upd"
  apply(clarsimp simp: ti_pad_combine_def Let_def padding_desc_def)
  apply(erule fa_ind_extend_ti)
  apply(auto simp: fa_ind_def)
  done

lemma (in c_type) fa_ind_ti_typ_pad_combine:
  "\<lbrakk> fa_ind (lf_fd ` lf_set ti []) h; \<And>v w. f (h w v) = f v;
      \<And>v. g (f v) v = v   \<rbrakk>
      \<Longrightarrow> fa_ind (lf_fd ` lf_set (ti_typ_pad_combine (t::'a itself) f g algn fn ti) []) h"
  by (auto simp: ti_typ_pad_combine_def Let_def intro: fa_ind_ti_typ_combine fa_ind_ti_pad_combine)

lemma (in wf_type) wf_lf_ti_typ_combine:
  "\<lbrakk> wf_lf (lf_set ti []); fn \<notin> set (field_names_list ti);
      \<And>v. upd (acc v) v = v; \<And>w u v. upd w (upd u v) = upd w v;
      \<And>w v. acc (upd w v) = w;
      upd_ind (lf_set ti []) upd; acc_ind acc (lf_fd ` lf_set ti []);
      fa_ind (lf_fd ` lf_set ti []) upd \<rbrakk> \<Longrightarrow>
      wf_lf (lf_set (ti_typ_combine (t::'a itself) acc upd algn fn ti) [])"
  apply(clarsimp simp: ti_typ_combine_def Let_def)
  apply(rule wf_lf_extend_ti; simp?)
   apply(rule wf_lf_adjust_ti; simp)
  apply(clarsimp simp: ti_ind_def)
  apply(drule lf_set_adjust_ti, simp)
  apply(clarsimp simp: fu_commutes_def update_desc_def upd_ind_def acc_ind_def fu_s_comm_k_def
                       fa_fu_ind_def fa_ind_def)
  done

lemma (in wf_type) wf_lf_ti_typ_pad_combine:
  "\<lbrakk> wf_lf (lf_set ti []); fn \<notin> set (field_names_list ti); hd fn \<noteq> CHR ''!'';
      \<And>v. upd (acc v) v = v; \<And>w u v. upd w (upd u v) = upd w v;
      \<And>w v. acc (upd w v) = w;
      upd_ind (lf_set ti []) upd; acc_ind acc (lf_fd ` lf_set ti []);
      fa_ind (lf_fd ` lf_set ti []) upd \<rbrakk> \<Longrightarrow>
      wf_lf (lf_set (ti_typ_pad_combine (t::'a itself) acc upd algn fn ti) [])"
  apply(clarsimp simp: ti_typ_pad_combine_def Let_def)
  apply (fastforce intro!: wf_lf_ti_typ_combine wf_lf_ti_pad_combine upd_ind_ti_pad_combine
                           acc_ind_ti_pad_combine fa_ind_ti_pad_combine)
  done

definition "upd_fa_ind X upd  \<equiv>  upd_ind X upd \<and> fa_ind (lf_fd ` X) upd"

lemma (in wf_type) wf_lf_ti_typ_pad_combine':
  "\<lbrakk> wf_lf (lf_set ti []); fn \<notin> set (field_names_list ti); hd fn \<noteq> CHR ''!'';
      \<And>v. upd (acc v) v = v; \<And>w u v. upd w (upd u v) = upd w v;
      \<And>w v. acc (upd w v) = w;
      upd_fa_ind (lf_set ti []) upd; acc_ind acc (lf_fd ` lf_set ti [])\<rbrakk>
  \<Longrightarrow>
      wf_lf (lf_set (ti_typ_pad_combine (t::'a itself) acc upd algn fn ti) [])"
  unfolding upd_fa_ind_def
  by (erule conjE) (rule wf_lf_ti_typ_pad_combine)


lemma (in c_type) upd_fa_ind_ti_typ_pad_combine:
"\<lbrakk> upd_fa_ind (lf_set ti []) h; \<And>w u v. upd w (h u v) = h u (upd w v);
      \<And>w v. acc (h w v) = acc v; \<And>v. upd (acc v) v = v \<rbrakk>
      \<Longrightarrow> upd_fa_ind (lf_set (ti_typ_pad_combine (t::'a itself) acc upd algn fn ti) []) h"
  unfolding upd_fa_ind_def
  by (auto intro: upd_ind_ti_typ_pad_combine fa_ind_ti_typ_pad_combine)

lemma upd_fa_ind_empty [simp]:
  "upd_fa_ind {} h"
  by (simp add: upd_fa_ind_def)

lemma wf_align_empty_typ_info: "wf_align (empty_typ_info algn tn)"
  by (simp add: wf_align_def empty_typ_info_def)

lemma wf_align_list: "wf_align t \<Longrightarrow> wf_align_list fs \<Longrightarrow>  wf_align_list (fs @ [DTuple t f d])"
  by (induct fs) auto
lemma wf_align_struct: "wf_align t \<Longrightarrow> wf_align_struct st \<Longrightarrow> wf_align_struct (extend_ti_struct st t f d)"
  apply (cases st)
   apply simp
  apply (simp add: wf_align_list)
  done

lemma align_td_extend_ti: "align_td (extend_ti tag t algn f d) = max (align_td tag) (max algn (align_td t))"
  apply (cases tag)
  apply (simp)
  done

lemma align_td_struct_extend_ti: "aggregate_struct st \<Longrightarrow>
  align_td_struct (extend_ti_struct st t f d) = max (align_td_struct st) (align_td t)"
  by (cases st) auto
lemma wf_align_extend_ti':
  assumes wf_t: "wf_align t"
  assumes agg: "aggregate tag"
  assumes wf_tag: "wf_align tag"
  shows "wf_align (extend_ti tag t algn f d)"
proof (cases tag)
  case (TypDesc algn' st n)
  with wf_tag agg obtain le: "align_td_wo_align_struct st \<le> algn'"
   and le': "align_td_struct st \<le> algn'"
   and wf_st: "wf_align_struct st"
   and agg_st: "aggregate_struct st" by auto
  from wf_align_struct [OF wf_t wf_st]
  have wf_st: "wf_align_struct (extend_ti_struct st t f d)" .
  from align_td_wo_align_le_align_td (2) [OF this]
  have "align_td_wo_align_struct (extend_ti_struct st t f d) \<le> align_td_struct (extend_ti_struct st t f d)" .
  also from align_td_struct_extend_ti [OF agg_st]
  have "\<dots> = max (align_td_struct st) (align_td t)" .
  finally
  have "align_td_wo_align_struct (extend_ti_struct st t f d) \<le> max algn' (max algn (align_td t))"
    using le'
    by (metis (full_types) le_max_iff_disj max.orderE)
  moreover from align_td_struct_extend_ti [OF agg_st] le'
  have "align_td_struct (extend_ti_struct st t f d) \<le> max algn' (max algn (align_td t))"
    by (metis max.cobounded2 max.mono )
  ultimately show ?thesis
    by (simp add: TypDesc wf_st)
qed

lemma (in mem_type) wf_align_extend_ti:
  assumes agg: "aggregate tag"
  assumes wf_tag: "wf_align tag"
  shows "wf_align (extend_ti tag (typ_info_t (TYPE('a))) algn f d)"
proof -
  have "wf_align (typ_info_t (TYPE('a)))" by (rule wf_align)
  from wf_align_extend_ti' [OF this agg wf_tag] show ?thesis .
qed

lemma wf_align_map_td [simp]:
"wf_align (map_td f g d) = wf_align d"
"wf_align_struct (map_td_struct f g ts) = wf_align_struct (ts)"
"wf_align_list (map_td_list f g fs) = wf_align_list fs"
"wf_align_tuple (map_td_tuple f g fd) = wf_align_tuple fd"
  by (induct d and ts and fs and fd) auto

lemma wf_align_adjust_ti[simp]: "wf_align (adjust_ti t acc upd) = wf_align t"
  by (simp add: adjust_ti_def)

lemma (in mem_type) wf_align_ti_typ_combine:
 "aggregate tag \<Longrightarrow> wf_align tag \<Longrightarrow> wf_align (ti_typ_combine (TYPE('a)) acc upd algn fn tag)"
  apply (simp add: ti_typ_combine_def Let_def)
  apply (rule wf_align_extend_ti')
    apply (simp add: wf_align)
   apply assumption
  apply assumption
  done

lemma wf_align_ti_pad_combine:
 "aggregate tag \<Longrightarrow> wf_align tag \<Longrightarrow> wf_align (ti_pad_combine n tag)"
  apply (simp add: ti_pad_combine_def Let_def)
  apply (rule wf_align_extend_ti')
    apply simp
   apply assumption
  apply assumption
  done

lemma (in mem_type) wf_align_ti_typ_pad_combine:
 "aggregate tag \<Longrightarrow> wf_align tag \<Longrightarrow> wf_align (ti_typ_pad_combine (TYPE('a)) acc upd algn fn tag)"
  by (simp add: ti_typ_pad_combine_def Let_def wf_align_ti_pad_combine wf_align_ti_typ_combine)

lemma wf_align_map_align:
  assumes wf_tag: "wf_align tag"
  assumes mono: "\<And>a. a \<le> f a"
  shows "wf_align (map_align f tag)"
  using wf_tag mono
  apply (cases tag)
  using order_trans apply auto
  done

lemma wf_align_final_pad: "aggregate tag \<Longrightarrow> wf_align tag \<Longrightarrow> wf_align (final_pad algn tag)"
  by (auto simp add: final_pad_def Let_def max_2_exp wf_align_map_align wf_align_ti_pad_combine)

lemmas wf_align_simps =
  wf_align_empty_typ_info
  wf_align_ti_typ_pad_combine
  wf_align_ti_typ_combine
  wf_align_ti_pad_combine
  wf_align_final_pad

lemma align_field_empty_typ_info [simp]:
  "align_field (empty_typ_info algn tn)"
  by (clarsimp simp: empty_typ_info_def align_field_def)

lemma align_td_wo_align_field_lookup:
  "\<forall>f m s n. field_lookup (t::('a,'b) typ_desc) f m = Some (s,n) \<longrightarrow> align_td_wo_align s \<le> align_td_wo_align t"
  "\<forall>f m s n. field_lookup_struct (st::('a,'b) typ_struct) f m = Some (s,n) \<longrightarrow> align_td_wo_align s \<le> align_td_wo_align_struct st"
  "\<forall>f m s n. field_lookup_list (ts::('a,'b) typ_tuple list) f m = Some (s,n) \<longrightarrow> align_td_wo_align s \<le> align_td_wo_align_list ts"
  "\<forall>f m s n. field_lookup_tuple (x::('a,'b) typ_tuple) f m = Some (s,n) \<longrightarrow> align_td_wo_align s \<le> align_td_wo_align_tuple x"
  by (induct t and st and ts and x, all \<open>clarsimp\<close>)
     (fastforce simp: max_def split: option.splits)

lemma align_td_field_lookup[rule_format]:
  "\<forall>f m s n. wf_align t \<longrightarrow> field_lookup (t::('a,'b) typ_desc) f m = Some (s,n) \<longrightarrow> align_td s \<le> align_td t"
  "\<forall>f m s n. wf_align_struct st \<longrightarrow> field_lookup_struct (st::('a,'b) typ_struct) f m = Some (s,n) \<longrightarrow> align_td s \<le> align_td_struct st"
  "\<forall>f m s n. wf_align_list ts \<longrightarrow> field_lookup_list (ts::('a,'b) typ_tuple list) f m = Some (s,n) \<longrightarrow> align_td s \<le> align_td_list ts"
  "\<forall>f m s n. wf_align_tuple x \<longrightarrow> field_lookup_tuple (x::('a,'b) typ_tuple) f m = Some (s,n) \<longrightarrow> align_td s \<le> align_td_tuple x"
  apply (induct t and st and ts and x, all \<open>clarsimp\<close>)
    apply  (fastforce simp: max_def split: option.splits)+
  done

lemma (in mem_type) align_td_field_lookup_mem_type: "field_lookup (typ_info_t (TYPE('a))) f m = Some (s, n) \<Longrightarrow>
  align_td s \<le> align_td (typ_info_t (TYPE('a)))"
  apply (rule align_td_field_lookup(1))
   apply (rule wf_align)
  apply simp
  done

lemma align_field_extend_ti:
  "\<lbrakk> align_field s; align_field t; wf_align t;  2^(align_td t) dvd size_td s \<rbrakk> \<Longrightarrow>
      align_field (extend_ti s t algn fn d)"
  apply(cases s, clarsimp)
  subgoal for x1 typ_struct xs
    apply(cases typ_struct, clarsimp)
     apply(clarsimp simp: align_field_def split: option.splits)
    apply(clarsimp simp: align_field_def)
    apply(subst (asm) field_lookup_list_append)
    apply(clarsimp split: if_split_asm option.splits)
    subgoal for x2 f s n
      apply(cases f, clarsimp)
      apply clarsimp
      apply(frule field_lookup_offset2)
      apply (meson align_td_field_lookup(1) dvd_diffD field_lookup_offset_le(1) power_le_dvd)
      done
    subgoal for x2 f s n
      by(cases f) auto       
    done
  done

lemma align_field_ti_pad_combine:
  "align_field ti \<Longrightarrow> align_field (ti_pad_combine n ti)"
  apply(clarsimp simp: ti_pad_combine_def Let_def)
  apply(erule align_field_extend_ti)
   apply(clarsimp simp: align_field_def)
   apply clarsimp
  apply clarsimp
  done

lemma align_field_map_align [simp]: "align_field (map_align f t)  = align_field t"
  by (cases t) (auto simp add: align_field_def)

lemma align_field_final_pad:
  "align_field ti \<Longrightarrow> align_field (final_pad algn ti)"
  apply(clarsimp simp: final_pad_def Let_def split: if_split_asm)
  apply(erule align_field_ti_pad_combine)
  done

lemma field_lookup_adjust_ti_None:
  "\<forall>fn m s n. field_lookup (adjust_ti t acc upd) fn m = None \<longrightarrow>
      (field_lookup t fn m = None)"
  "\<forall>fn m s n. field_lookup_struct (map_td_struct (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) st)
        fn m = None \<longrightarrow>
        (field_lookup_struct st fn m = None)"
  "\<forall>fn m s n. field_lookup_list (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) ts) fn m = None \<longrightarrow>
        (field_lookup_list ts fn m = None)"
  "\<forall>fn m s n. field_lookup_tuple (map_td_tuple (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) x) fn m = None \<longrightarrow>
        (field_lookup_tuple x fn m = None)"
proof (induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case by (clarsimp simp: adjust_ti_def split: option.splits)
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
  case (Cons_typ_desc dt_tuple list)
  then show ?case
    apply (clarsimp simp: adjust_ti_def split: option.splits)
    apply (cases dt_tuple)
    apply clarsimp
    done
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case by (clarsimp simp: adjust_ti_def split: option.splits)
qed

lemma field_lookup_adjust_ti' [rule_format]:
  "\<forall>fn m s n. field_lookup (adjust_ti t acc upd) fn m = Some (s,n) \<longrightarrow>
      (\<exists>s'. field_lookup t fn m = Some (s',n) \<and> align_td_wo_align s = align_td_wo_align s')"
  "\<forall>fn m s n. field_lookup_struct (map_td_struct (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) st)
        fn m = Some (s,n) \<longrightarrow>
        (\<exists>s'. field_lookup_struct st fn m = Some (s',n) \<and> align_td_wo_align s = align_td_wo_align s')"
  "\<forall>fn m s n. field_lookup_list (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) ts) fn m = Some (s,n) \<longrightarrow>
        (\<exists>s'. field_lookup_list ts fn m = Some (s',n) \<and> align_td_wo_align s = align_td_wo_align s')"
  "\<forall>fn m s n. field_lookup_tuple (map_td_tuple (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) x) fn m = Some (s,n) \<longrightarrow>
        (\<exists>s'. field_lookup_tuple x fn m = Some (s',n) \<and> align_td_wo_align s = align_td_wo_align s')"
proof (induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case by (clarsimp simp: adjust_ti_def)
next
  case (TypScalar nat1 nat2 a)
  then show ?case by (clarsimp simp: adjust_ti_def)
next
  case (TypAggregate list)
  then show ?case by (clarsimp simp: adjust_ti_def)
next
  case Nil_typ_desc
  then show ?case by (clarsimp simp: adjust_ti_def)
next
  case (Cons_typ_desc dt_tuple list)
  then show ?case 
    apply (clarsimp simp: adjust_ti_def)
    apply(clarsimp split: option.splits)
     apply(rule conjI; clarsimp)
      apply(cases dt_tuple, clarsimp)
     apply(cases dt_tuple, clarsimp split: if_split_asm)
    subgoal for fn
      apply(drule spec [where x=fn])
      apply clarsimp
      apply(fold adjust_ti_def)
      apply(subst (asm) field_lookup_adjust_ti_None; simp)
      done
    apply fastforce
    done
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case by (clarsimp simp: adjust_ti_def)
qed

lemma field_lookup_adjust_ti''' [rule_format]:
  "\<forall>fn m s n. field_lookup (adjust_ti t acc upd) fn m = Some (s,n) \<longrightarrow>
      (\<exists>s'. field_lookup t fn m = Some (s',n) \<and> align_td s = align_td s')"
  "\<forall>fn m s n. field_lookup_struct (map_td_struct (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) st)
        fn m = Some (s,n) \<longrightarrow>
        (\<exists>s'. field_lookup_struct st fn m = Some (s',n) \<and> align_td s = align_td s')"
  "\<forall>fn m s n. field_lookup_list (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) ts) fn m = Some (s,n) \<longrightarrow>
        (\<exists>s'. field_lookup_list ts fn m = Some (s',n) \<and> align_td s = align_td s')"
  "\<forall>fn m s n. field_lookup_tuple (map_td_tuple (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) x) fn m = Some (s,n) \<longrightarrow>
        (\<exists>s'. field_lookup_tuple x fn m = Some (s',n) \<and> align_td s = align_td s')"
proof(induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case by (clarsimp simp: adjust_ti_def)
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
  case (Cons_typ_desc dt_tuple list)
  then show ?case 
    apply(clarsimp simp: adjust_ti_def)
    apply(clarsimp split: option.splits)
     apply(rule conjI; clarsimp)
      apply(cases dt_tuple, clarsimp)
     apply(cases dt_tuple, clarsimp split: if_split_asm)
    subgoal for fn
      apply(drule spec [where x=fn])
      apply clarsimp
      apply(fold adjust_ti_def)
      apply(subst (asm) field_lookup_adjust_ti_None; simp)
      done
    apply fastforce
    done
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case  by(clarsimp simp: adjust_ti_def)
qed

lemma field_lookup_adjust_ti:
  "\<lbrakk> field_lookup (adjust_ti t acc upd) fn m = Some (s,n) \<rbrakk> \<Longrightarrow>
      (\<exists>s'. field_lookup t fn m = Some (s',n) \<and> align_td_wo_align s = align_td_wo_align s')"
  by (rule field_lookup_adjust_ti')

lemma field_lookup_adjust_ti1:
  "\<lbrakk> field_lookup (adjust_ti t acc upd) fn m = Some (s,n) \<rbrakk> \<Longrightarrow>
      (\<exists>s'. field_lookup t fn m = Some (s',n) \<and> align_td s = align_td s')"
  by (rule field_lookup_adjust_ti''')

lemma align_adjust_ti:
  "align_field ti \<Longrightarrow> align_field (adjust_ti ti acc upd)"
  apply(clarsimp simp: align_field_def)
  apply(drule field_lookup_adjust_ti1)
  apply clarsimp
  done

lemma (in mem_type) align_field_ti_typ_combine:
  "\<lbrakk> align_field ti; 2 ^ align_td (typ_info_t TYPE('a)) dvd size_td ti \<rbrakk> \<Longrightarrow>
   align_field (ti_typ_combine (t::'a itself) acc upd algn fn ti)"
  apply(clarsimp simp: ti_typ_combine_def Let_def)
  apply(rule align_field_extend_ti, assumption)
   apply(rule align_adjust_ti)
   apply(rule align_field)
   apply (simp add: wf_align)
  apply simp
  done

lemma (in mem_type) align_td_wo_align_type_info_t_le_align_td:
  "align_td_wo_align (typ_info_t TYPE('a)) \<le> align_td (typ_info_t TYPE('a))"
proof -
  have "wf_align (typ_info_t TYPE('a))" by (rule wf_align)
  then show ?thesis thm wf_align.wfal0 by (rule align_td_wo_align_le_align_td(1))
qed

lemma (in mem_type) align_field_ti_typ_pad_combine:
  "\<lbrakk>wf_align ti; align_field ti; aggregate ti\<rbrakk> \<Longrightarrow>
   align_field (ti_typ_pad_combine (t::'a itself) acc upd algn fn ti)"

  unfolding ti_typ_pad_combine_def Let_def
  apply (rule align_field_ti_typ_combine)
  subgoal
    apply clarsimp
    apply (rule align_field_ti_pad_combine)
    apply assumption
    done
  apply clarsimp
  apply (rule conjI)
  subgoal
    apply (clarsimp simp add: align_of_def)
    apply (metis (no_types, lifting) align_td_wo_align_type_info_t_le_align_td dvd_padup_add max.cobounded2 max_2_exp
     power_le_dvd size_td_lt_ti_pad_combine zero_less_numeral zero_less_power)
    done
  apply (clarsimp simp add: align_of_def)
  by (simp add: max_2_exp padup_dvd power_le_dvd)

lemma npf_extend_ti [simp]:
  "non_padding_fields (extend_ti s t algn fn d) = non_padding_fields s @
      (if hd fn = CHR ''!'' then [] else [fn])"
  apply (cases s)
  subgoal for x1 typ_struct xs
    apply (cases typ_struct; simp)
    done
  done

lemma npf_ti_pad_combine [simp]:
  "non_padding_fields (ti_pad_combine n tag) = non_padding_fields tag"
  by (clarsimp simp: ti_pad_combine_def Let_def)

lemma (in c_type) npf_ti_typ_combine [simp]:
  "hd fn \<noteq> CHR ''!'' \<Longrightarrow>
   non_padding_fields (ti_typ_combine (t::'a itself) acc upd algn fn tag) = non_padding_fields tag @ [fn]"
  by (clarsimp simp: ti_typ_combine_def Let_def)

lemma (in c_type) npf_ti_typ_pad_combine [simp]:
  "hd fn \<noteq> CHR ''!'' \<Longrightarrow>
   non_padding_fields (ti_typ_pad_combine (t::'a itself) acc upd algn fn tag) = non_padding_fields tag @ [fn]"
  by (clarsimp simp: ti_typ_pad_combine_def Let_def)

lemma non_padding_fields_map_align [simp]:
 "non_padding_fields (map_align f t) = non_padding_fields t"
  by (cases t) simp

lemma npf_final_pad [simp]:
  "non_padding_fields (final_pad algn tag) = non_padding_fields tag"
  by (clarsimp simp: final_pad_def Let_def)

lemma npf_empty_typ_info [simp]:
  "non_padding_fields (empty_typ_info algn tn) = []"
  by (clarsimp simp: empty_typ_info_def)

definition field_fd' :: "'a xtyp_info \<Rightarrow> qualified_field_name \<rightharpoonup> 'a field_desc" where
  "field_fd' t f \<equiv> case field_lookup t f 0 of None \<Rightarrow> None | Some x \<Rightarrow> Some (field_desc (fst x))"

lemma padup_zero [simp]:
  "padup n 0 = 0"
  by (clarsimp simp: padup_def)

lemma padup_same [simp]:
  "padup n n = 0"
  by (clarsimp simp: padup_def)

lemmas size_td_simps_0 = size_td_lt_final_pad size_td_lt_ti_typ_pad_combine

lemmas size_td_simps_1 = size_td_simps_0
                         aggregate_ti_typ_pad_combine aggregate_empty_typ_info

lemmas size_td_simps_2 = padup_def align_of_final_pad align_of_def

lemmas size_td_simps = size_td_simps_1 size_td_simps_2

lemmas size_td_simps_3 = size_td_simps_0 size_td_simps_2


lemma fu_commutes_sym: "fu_commutes x y = fu_commutes y x"
  by (auto simp add: fu_commutes_def)

(*fixme: remove unused? *)
lemma wf_lf_insert_recursion:
  assumes wf_D:  "wf_lf D"
  assumes cons_x: "fd_cons_desc (lf_fd x) (lf_sz x)"
  assumes comm_D: "\<And>y. y \<in> D \<Longrightarrow> fu_commutes (field_update (lf_fd x)) (field_update (lf_fd y)) \<and>
            fa_fu_ind (lf_fd x) (lf_fd y) (lf_sz y) (lf_sz x) \<and>
            fa_fu_ind (lf_fd y) (lf_fd x) (lf_sz x) (lf_sz y)"
  shows "wf_lf (insert x D)"
proof -
  have comm_x_D:
   "fu_commutes (field_update (lf_fd x')) (field_update (lf_fd y))" and
   "fa_fu_ind (lf_fd x') (lf_fd y) (lf_sz y) (lf_sz x')"
    if x'_in: "x' \<in> insert x D" and y_in: "y \<in> insert x D" and neq: "lf_fn y \<noteq> lf_fn x'"
    for x' and y
  proof - (*(induct "x' = x")*)
    show "fu_commutes (field_update (lf_fd x')) (field_update (lf_fd y))"
      proof (cases "x' = x")
        case True
        from True y_in neq comm_D x'_in show ?thesis
          by auto
      next
        case False
        note neq_x'_x = this
        with x'_in have x'_D: "x' \<in> D"
          by auto
        from comm_D [OF this] have "fu_commutes (field_update (lf_fd x)) (field_update (lf_fd x'))"
          by auto
        with fu_commutes_sym have comm_x'_x: "fu_commutes (field_update (lf_fd x')) (field_update (lf_fd x))"
          by auto
        from neq have neq': "y \<noteq> x'"
          by auto
        show ?thesis
        proof (cases "y = x")
          case True
          with comm_x'_x show ?thesis by simp
        next
          case False
          from False y_in have y_D: "y \<in> D" by simp
          with x'_D neq wf_D
          show ?thesis
            by (auto simp add: wf_lf_def)
        qed
      qed
    next
      show "fa_fu_ind (lf_fd x') (lf_fd y) (lf_sz y) (lf_sz x')"
      proof (cases "x' = x")
        case True
        from True y_in neq comm_D x'_in show ?thesis
          by auto
      next
        case False
        note neq_x'_x = this
        with x'_in have x'_D: "x' \<in> D"
          by auto
        from comm_D [OF this] have "fa_fu_ind (lf_fd x) (lf_fd x') (lf_sz x') (lf_sz x)" and
            fa_fu_x'_x: "fa_fu_ind (lf_fd x') (lf_fd x) (lf_sz x) (lf_sz x')" by auto
        from neq have neq': "y \<noteq> x'"
          by auto
        show ?thesis
        proof (cases "y = x")
          case True
          with fa_fu_x'_x show ?thesis by simp
        next
          case False
          from False y_in have y_D: "y \<in> D" by simp
          with x'_D neq wf_D
          show ?thesis
            by (auto simp add: wf_lf_def)
        qed
      qed
    qed
    with cons_x wf_D
    show ?thesis
      by (auto simp add: wf_lf_def)
qed


(*fixme: remove unused? *)
lemma wf_lf_insert_recursion':
  assumes cons_x: "fd_cons_desc (lf_fd x) (lf_sz x)"
  assumes comm_D: "\<And>y. y \<in> D \<Longrightarrow> fu_commutes (field_update (lf_fd x)) (field_update (lf_fd y)) \<and>
            fa_fu_ind (lf_fd x) (lf_fd y) (lf_sz y) (lf_sz x) \<and>
            fa_fu_ind (lf_fd y) (lf_fd x) (lf_sz x) (lf_sz y)"
  assumes wf_D:  "wf_lf D"
  shows "wf_lf (insert x D)"
  using wf_D cons_x comm_D
  by (rule wf_lf_insert_recursion)

(*fixme: remove unused? *)
lemma wf_lf_insert_recursion'':
  assumes wf_D:  "wf_lf D"
  assumes cons_x: "fd_cons_desc (lf_fd x) (lf_sz x)"
  assumes comm_D: "\<And>y. y \<in> D \<Longrightarrow> lf_fn y \<noteq> lf_fn x \<Longrightarrow> fu_commutes (field_update (lf_fd x)) (field_update (lf_fd y)) \<and>
            fa_fu_ind (lf_fd x) (lf_fd y) (lf_sz y) (lf_sz x) \<and>
            fa_fu_ind (lf_fd y) (lf_fd x) (lf_sz x) (lf_sz y)"
  shows "wf_lf (insert x D)"
proof -
  have comm_x_D:
   "fu_commutes (field_update (lf_fd x')) (field_update (lf_fd y))" and
   "fa_fu_ind (lf_fd x') (lf_fd y) (lf_sz y) (lf_sz x')"
    if x'_in: "x' \<in> insert x D" and y_in: "y \<in> insert x D" and neq: "lf_fn y \<noteq> lf_fn x'"
    for x' and y
  proof - (*(induct "x' = x")*)
    show "fu_commutes (field_update (lf_fd x')) (field_update (lf_fd y))"
      proof (cases "x' = x")
        case True
        from True y_in neq comm_D x'_in show ?thesis
          by auto
      next
        case False
        note neq_x'_x = this
        with x'_in have x'_D: "x' \<in> D"
          by auto
        from neq have neq': "y \<noteq> x'"
          by auto
        show ?thesis
        proof (cases "y = x")
          case True
          with neq neq_x'_x neq'
          have "lf_fn x' \<noteq> lf_fn x" by simp
          from comm_D [OF x'_D this]  have "fu_commutes (field_update (lf_fd x)) (field_update (lf_fd x'))"
            by auto
          with fu_commutes_sym have comm_x'_x: "fu_commutes (field_update (lf_fd x')) (field_update (lf_fd x))"
            by auto
          from True comm_x'_x show ?thesis by simp
        next
          case False
          from False y_in have y_D: "y \<in> D" by simp
          with x'_D neq wf_D
          show ?thesis
            by (auto simp add: wf_lf_def)
        qed
      qed
    next
      show "fa_fu_ind (lf_fd x') (lf_fd y) (lf_sz y) (lf_sz x')"
      proof (cases "x' = x")
        case True
        from True y_in neq comm_D x'_in show ?thesis
          by auto
      next
        case False
        note neq_x'_x = this
        with x'_in have x'_D: "x' \<in> D"
          by auto
        from neq have neq': "y \<noteq> x'"
          by auto
        show ?thesis
        proof (cases "y = x")
          case True
          with neq neq_x'_x neq'
          have "lf_fn x' \<noteq> lf_fn x" by simp
          from comm_D [OF x'_D this] have "fa_fu_ind (lf_fd x) (lf_fd x') (lf_sz x') (lf_sz x)" and
            fa_fu_x'_x: "fa_fu_ind (lf_fd x') (lf_fd x) (lf_sz x) (lf_sz x')" by auto
          from True fa_fu_x'_x show ?thesis by simp
        next
          case False
          from False y_in have y_D: "y \<in> D" by simp
          with x'_D neq wf_D
          show ?thesis
            by (auto simp add: wf_lf_def)
        qed
      qed
    qed
    with cons_x wf_D
    show ?thesis
      by (auto simp add: wf_lf_def)
  qed


lemma wf_field_desc_empty [simp]:
"wf_field_desc \<lparr>field_access = \<lambda>v bs. [], field_update = \<lambda>bs. id, field_sz = 0\<rparr>"
  by (unfold_locales) (auto simp add: padding_base.eq_padding_def padding_base.eq_upto_padding_def)


lemma field_desc_independent_subset:
  "D \<subseteq> E \<Longrightarrow> field_desc_independent acc upd E \<Longrightarrow> field_desc_independent acc upd D"
  by (auto simp add: field_desc_independent_def)

lemma field_desc_independent_union_iff:
 "field_desc_independent acc upd (D \<union> E) =
   (field_desc_independent acc upd D \<and> field_desc_independent acc upd E)"
  by (auto simp add: field_desc_independent_def)

lemma field_desc_independent_unionI:
 "field_desc_independent acc upd D \<Longrightarrow> field_desc_independent acc upd E \<Longrightarrow>
  field_desc_independent acc upd (D \<union> E)"
  by (simp add: field_desc_independent_union_iff)

lemma field_desc_independent_unionD1:
 "field_desc_independent acc upd (D \<union> E) \<Longrightarrow>
   field_desc_independent acc upd D"
  by (simp add: field_desc_independent_union_iff)

lemma field_desc_independent_unionD2:
 "field_desc_independent acc upd (D \<union> E) \<Longrightarrow>
   field_desc_independent acc upd E"
  by (simp add: field_desc_independent_union_iff)

lemma field_desc_independent_insert_iff:
  "field_desc_independent acc upd (insert d D) =
    (field_desc_independent acc upd {d} \<and> field_desc_independent acc upd D)"
  apply (subst insert_is_Un)
  apply (simp only: field_desc_independent_union_iff)
  done

lemma field_desc_independent_insertI:
  "field_desc_independent acc upd {d} \<Longrightarrow> field_desc_independent acc upd D \<Longrightarrow>
   field_desc_independent acc upd (insert d D)"
  apply (subst insert_is_Un)
  apply (simp only: field_desc_independent_union_iff)
  done

lemma field_desc_independent_insertD1:
  assumes ins: "field_desc_independent acc upd (insert d D)"
  shows "field_desc_independent acc upd {d}"
proof -
  from ins have "field_desc_independent acc upd ({d} \<union> D)"
    by (simp)
  from field_desc_independent_unionD1 [OF this]
  show ?thesis .
qed

lemma field_desc_independent_insertD2:
  assumes ins: "field_desc_independent acc upd (insert d D)"
  shows "field_desc_independent acc upd D"
proof -
  from ins have "field_desc_independent acc upd ({d} \<union> D)"
    by (simp)
  from field_desc_independent_unionD2 [OF this]
  show ?thesis .
qed



lemma field_descs_independent_append_first: "field_descs_independent (xs @ ys) \<Longrightarrow> field_descs_independent xs"
  by (induct xs arbitrary: ys) (auto intro: field_desc_independent_subset)

lemma field_descs_independent_append_second: "field_descs_independent (xs @ ys) \<Longrightarrow> field_descs_independent ys"
  by (induct xs arbitrary: ys) (auto intro: field_desc_independent_subset)

lemma field_descs_independent_append_first_ind:
 "field_descs_independent (xs @ ys) \<Longrightarrow> x \<in> set xs \<Longrightarrow>
       field_desc_independent (field_access x) (field_update x) (set ys)"
by (induct xs arbitrary: ys) (auto simp add: field_desc_independent_union_iff)

lemma field_descs_independent_appendI1:
 "field_descs_independent xs \<Longrightarrow> field_descs_independent ys \<Longrightarrow>
 (\<forall>x \<in> set xs. field_desc_independent (field_access x) (field_update x) (set ys)) \<Longrightarrow>
 field_descs_independent (xs @ ys)"
  by (induct xs arbitrary: ys) (auto simp add: field_desc_independent_union_iff)


lemma field_desc_independent_symmetric:
"(\<forall>x \<in> X. field_desc_independent (field_access x) (field_update x) Y) \<Longrightarrow>
 (\<forall>y \<in> Y. field_desc_independent (field_access y) (field_update y) X)"
  by (simp add: field_desc_independent_def fu_commutes_def)

lemma field_desc_independent_symmetric_singleton:
"field_desc_independent (field_access x) (field_update x) Y \<Longrightarrow> y \<in> Y
\<Longrightarrow> field_desc_independent (field_access y) (field_update y) {x}"
  using field_desc_independent_symmetric by blast

lemma field_descs_independent_appendI2:
  assumes ind_xs: "field_descs_independent xs"
  assumes ind_ys: "field_descs_independent ys"
  assumes ind_xs_ys: "\<forall>y \<in> set ys. field_desc_independent (field_access y) (field_update y) (set xs)"
  shows "field_descs_independent (xs @ ys)"
  using field_desc_independent_symmetric [OF ind_xs_ys] ind_xs ind_ys
  by (auto intro: field_descs_independent_appendI1)


lemma field_desc_indepenent_empty [simp]:
  "field_desc_independent (field_access d) (field_update d) {}" by (simp add: field_desc_independent_def)



lemma field_update_apply_field_updates_commute:
  fixes d::"'a field_desc"
  fixes ds::"'a field_desc list"
assumes ind_d:"field_desc_independent (field_access d) (field_update d) (set ds)"
assumes ind_ds: "field_descs_independent ds"
shows "field_update d bs (fst (apply_field_updates ds bs' s)) =
  fst (apply_field_updates ds bs' (field_update d bs s))"
using ind_d ind_ds
proof (induct ds arbitrary: d bs bs' s)
case Nil
then show ?case by simp
next
  case (Cons d' ds')
  from Cons.prems obtain
    ind_d1:  "field_desc_independent (field_access d) (field_update d) (insert d' (set ds'))" and
    ind_d': "field_desc_independent (field_access d') (field_update d') (set ds')" and
    ind_d: "field_desc_independent (field_access d) (field_update d) (set ds')" and
    ind_ds': "field_descs_independent ds'"
    by (auto intro: field_desc_independent_subset)

  from ind_d1 interpret fi: field_desc_independent "field_access d" "field_update d" "insert d' (set ds')" .
  from fi.fu_commutes [of d']
  have "fu_commutes (field_update d) (field_update d')" by simp
  then
  have d_d'_com: "field_update d bs (field_update d' bs' s) = (field_update d' bs' (field_update d bs s))"
    by (auto simp add: fu_commutes_def)

  from Cons.prems obtain
    ind_d': "field_desc_independent (field_access d') (field_update d') (set ds')" and
    ind_d: "field_desc_independent (field_access d) (field_update d) (set ds')" and
    ind_ds': "field_descs_independent ds'"
    by (auto intro: field_desc_independent_subset)

  note hyp = Cons.hyps [OF ind_d ind_ds']

  show ?case by (simp add: hyp d_d'_com)
qed

lemma (in wf_field_desc) is_padding_byte_acc_upd_compose:
  assumes acc_upd: "\<And>v s. acc (upd v s) = v"
  shows "padding_base.is_padding_byte (field_access d \<circ> acc)
     (\<lambda>bs v. upd (field_update d bs (acc v)) v) (field_sz d) i =
     is_padding_byte i "
  apply (simp add: is_padding_byte_def padding_base.is_padding_byte_def)
  by (metis acc_upd)

lemma (in wf_field_desc) is_value_byte_acc_upd_compose:
  assumes acc_upd: "\<And>v s. acc (upd v s) = v"
  shows "padding_base.is_value_byte (field_access d \<circ> acc)
     (\<lambda>bs v. upd (field_update d bs (acc v)) v) (field_sz d) i =
     is_value_byte i "
  apply (simp add: is_value_byte_def padding_base.is_value_byte_def)
  by (metis acc_upd)

lemma (in wf_field_desc) wf_field_desc_update_desc:
  assumes double_update_upd: "\<And>v w s. upd v (upd w s) = upd v s"
  assumes acc_upd: "\<And>v s. acc (upd v s) = v"
  assumes upd_acc: "\<And>s. upd (acc s) s = s"
  shows "wf_field_desc (update_desc acc upd d)" (is "wf_field_desc ?upd")
proof (unfold_locales)
  fix i
  assume i_bound: "i < field_sz (update_desc acc upd d)"
  show "padding_base.is_padding_byte (field_access (update_desc acc upd d))
          (field_update (update_desc acc upd d))
          (field_sz (update_desc acc upd d)) i \<noteq>
         padding_base.is_value_byte (field_access (update_desc acc upd d))
          (field_update (update_desc acc upd d))
          (field_sz (update_desc acc upd d)) i"
    using complement i_bound
    by (simp add: update_desc_def is_padding_byte_acc_upd_compose [of acc upd, OF acc_upd]
        is_value_byte_acc_upd_compose [of acc upd, OF acc_upd])
next
  fix bs bs' s
  show "field_update ?upd bs (field_update ?upd bs' s) = field_update ?upd bs s"
    by (simp add: update_desc_def double_update double_update_upd acc_upd)
next
  fix bs s bs' s'
  show "field_access ?upd (field_update ?upd bs s) bs' = field_access ?upd (field_update ?upd bs s') bs'"
    by (simp add: update_desc_def access_update acc_upd)
next
  fix s bs
  show "field_update ?upd (field_access ?upd s bs) s = s"
    by (simp add: update_desc_def update_access upd_acc)
next
  fix s bs
  show "(field_access ?upd s (take (field_sz ?upd) bs)) = field_access ?upd s bs"
    by (simp add: update_desc_def access_size)
next
  fix s bs
  show "length (field_access ?upd s bs) = field_sz ?upd"
    by (simp add: update_desc_def access_result_size)
next
  fix bs
  show "field_update ?upd (take (field_sz ?upd) bs) = field_update ?upd bs"
    by (simp add: update_desc_def update_size)
qed



lemma toplevel_field_descs_subset:
  fixes t::"'a xtyp_info" and
   st::"'a xtyp_info_struct" and
   fs::"'a xtyp_info_tuple list" and
   f::"'a xtyp_info_tuple"
 shows
  "set (toplevel_field_descs t) \<subseteq> set (field_descs t)"
  "set (toplevel_field_descs_struct st) \<subseteq> set (field_descs_struct st)"
  "set (toplevel_field_descs_list fs) \<subseteq> set (field_descs_list fs)"
  "set (toplevel_field_descs_tuple f) \<subseteq> set (field_descs_tuple f)"
  by (induct t and st and fs and f) auto


lemma
  fixes t::"'a xtyp_info" and
   st::"'a xtyp_info_struct" and
   fs::"'a xtyp_info_tuple list" and
   f::"'a xtyp_info_tuple"
 shows
 " lf_fd ` lf_set t xs \<subseteq> set (field_descs t)"
  " lf_fd ` lf_set_struct st xs \<subseteq> set (field_descs_struct st)"
  " lf_fd ` lf_set_list fs xs \<subseteq> set (field_descs_list fs)"
  " lf_fd ` lf_set_tuple f xs \<subseteq> set (field_descs_tuple f)"
     apply (induction t and st and fs and f arbitrary: xs) apply auto
  oops (* fixme: checkout why arbitrary: xs does not work here *)



lemma lf_set_subset_field_descs:
  fixes t::"'a xtyp_info" and
   st::"'a xtyp_info_struct" and
   fs::"'a xtyp_info_tuple list" and
   f::"'a xtyp_info_tuple"
 shows
 "\<And>xs. lf_fd ` lf_set t xs \<subseteq> set (field_descs t)"
 "\<And>xs. lf_fd ` lf_set_struct st xs \<subseteq> set (field_descs_struct st)"
 "\<And>xs. lf_fd ` lf_set_list fs xs \<subseteq> set (field_descs_list fs)"
 "\<And>xs. lf_fd ` lf_set_tuple f xs \<subseteq> set (field_descs_tuple f)"
  by (induction t and st and fs and f) (auto simp add: image_subset_iff)


lemma wf_field_descs_empty_typ_info [simp]: "wf_field_descs (set (field_descs (empty_typ_info algn t)))"
  by (simp add: empty_typ_info_def wf_field_descs_def)


lemma field_descs_map:
  "field_descs (map_td (\<lambda>_ _. update_desc acc upd) (update_desc acc upd) t) =
     map (update_desc acc upd) (field_descs t)"
  "field_descs_struct (map_td_struct (\<lambda>_ _. update_desc acc upd) (update_desc acc upd) st) =
     map (update_desc acc upd) (field_descs_struct st)"
  "field_descs_list (map_td_list (\<lambda>_ _. update_desc acc upd) (update_desc acc upd) fs) =
     map (update_desc acc upd) (field_descs_list fs)"
  "field_descs_tuple (map_td_tuple (\<lambda>_ _. update_desc acc upd) (update_desc acc upd) f) =
     map (update_desc acc upd) (field_descs_tuple f)"
  by (induct t and st and fs and f) auto


lemma component_update_access:
  assumes wf:"wf_field_descs (set (field_descs t))"
  shows "field_update (component_desc t)
         (field_access (component_desc t) s bs) s = s"
proof (cases t)
  case (TypDesc algn st n)
  show ?thesis
  proof (cases st)
    case (TypScalar sz align d)
    from TypDesc TypScalar have "d \<in> set (field_descs t)" by simp
    with wf have "wf_field_desc d" by (simp add: wf_field_descs_def)
    then interpret wf_d: wf_field_desc d .
    from TypDesc TypScalar wf_d.update_access show ?thesis
      by simp
  next
    case (TypAggregate fs)
    from wf have "wf_field_descs (set (field_descs_list fs))" by (simp add: TypDesc TypAggregate)
    then
    have "fst (apply_field_updates (map dt_trd fs)
            (concat (split_map (component_access_tuple s) fs bs)) s) = s"
    proof (induct fs arbitrary: s bs)
      case Nil
      then show ?case by simp
    next
      case (Cons f fs')

      obtain ft fn d where f: "f = DTuple ft fn d" by (cases f) simp

      from Cons f obtain
        wf_d: "wf_field_desc d" and
        wf_ft: "wf_field_descs (set (field_descs ft))" and
        wf_fs': "wf_field_descs (set (field_descs_list fs'))" by auto


      from wf_d interpret wf_d: wf_field_desc d .
      from Cons.hyps [OF wf_fs']
      have "fst (apply_field_updates (map dt_trd fs')
             (concat (split_map (component_access_tuple s) fs' (drop (field_sz d) bs))) s) = s" .
      then
      show ?case
        by (simp add: Cons f wf_d.access_result_size wf_d.update_access_append)
    qed
    with TypDesc TypAggregate show ?thesis by simp
  qed
qed

lemma toplevel_field_descs_tuple_dt_trd: "toplevel_field_descs_tuple t = [dt_trd t]"
  by (cases t) simp
lemma toplevel_field_descs_list_map: "toplevel_field_descs_list fs = map dt_trd fs"
  by (induct fs) (auto simp add: toplevel_field_descs_tuple_dt_trd)

lemma component_double_update:
  assumes wf:"wf_field_descs (set (field_descs t))"
  assumes ind: "field_descs_independent (toplevel_field_descs t)"
  shows"field_update (component_desc t) bs (field_update (component_desc t) bs' s) =
        field_update (component_desc t) bs s"
proof (cases t)
  case (TypDesc algn st n)
  show ?thesis
  proof (cases st)
    case (TypScalar sz align d)
    from TypDesc TypScalar have "d \<in> set (field_descs t)" by simp
    with wf have "wf_field_desc d" by (simp add: wf_field_descs_def)
    then interpret wf_d: wf_field_desc d .
    from TypDesc TypScalar wf_d.double_update show ?thesis
      by simp
  next
    case (TypAggregate fs)
    from wf have wf: "wf_field_descs (set (field_descs_list fs))" by (simp add: TypDesc TypAggregate)
    from ind have ind: "field_descs_independent (toplevel_field_descs_list fs)" by (simp add: TypDesc TypAggregate)
    from wf ind
    have "fst (apply_field_updates (map dt_trd fs) bs
            (fst (apply_field_updates (map dt_trd fs) bs' s))) =
          fst (apply_field_updates (map dt_trd fs) bs s)"
    proof (induct fs arbitrary: s bs bs')
      case Nil
      then show ?case by simp
    next
      case (Cons f fs')
      obtain ft fn d where f: "f = DTuple ft fn d" by (cases f) simp

      from Cons.prems f obtain
        wf_d: "wf_field_desc d" and
        wf_ft: "wf_field_descs (set (field_descs ft))" and
        wf_fs': "wf_field_descs (set (field_descs_list fs'))" and
        ind_d: "field_desc_independent (field_access d) (field_update d)
          (set (toplevel_field_descs_list fs'))" and
        ind_fs': "field_descs_independent (toplevel_field_descs_list fs')"
        by auto


      from wf_d interpret wf_d: wf_field_desc d .
      from field_update_apply_field_updates_commute [OF ind_d ind_fs']
      have d_ds'_commute: "field_update d bs
             (fst (apply_field_updates (map dt_trd fs') (drop (field_sz d) bs')
                     (field_update d bs' s))) =
            fst (apply_field_updates (map dt_trd fs') (drop (field_sz d) bs') (field_update d bs s))"
        by (simp add: toplevel_field_descs_list_map wf_d.double_update)


      note hyp = Cons.hyps [OF wf_fs' ind_fs', where bs="(drop (field_sz d) bs)" and s="(field_update d bs s)"]
      show ?case
        by (simp add: Cons f wf_d.access_result_size d_ds'_commute hyp)
    qed
    then show ?thesis by (simp add: TypDesc TypAggregate)
  qed
qed


lemma component_access_update:
  assumes wf:"wf_field_descs (set (field_descs t))"
  assumes ind: "field_descs_independent (toplevel_field_descs t)"
  shows "field_access (component_desc t) (field_update (component_desc t) bs s) bs' =
        field_access (component_desc t) (field_update (component_desc t) bs s') bs'"
proof (cases t)
  case (TypDesc algn st n)
  show ?thesis
  proof (cases st)
    case (TypScalar sz align d)
    from TypDesc TypScalar have "d \<in> set (field_descs t)" by simp
    with wf have "wf_field_desc d" by (simp add: wf_field_descs_def)
    then interpret wf_d: wf_field_desc d .
    from TypDesc TypScalar wf_d.access_update show ?thesis
      by simp
  next
    case (TypAggregate fs)
    from wf have wf: "wf_field_descs (set (field_descs_list fs))" by (simp add: TypDesc TypAggregate)
    from ind have ind: "field_descs_independent (toplevel_field_descs_list fs)" by (simp add: TypDesc TypAggregate)
    from wf ind
    have "concat (split_map
           (component_access_tuple (fst (apply_field_updates (map dt_trd fs) bs s))) fs bs') =
          concat (split_map
           (component_access_tuple (fst (apply_field_updates (map dt_trd fs) bs s'))) fs bs')"
    proof (induct fs arbitrary: bs s bs' s')
      case Nil
      then show ?case by simp
    next
      case (Cons f fs')
      obtain ft fn d where f: "f = DTuple ft fn d" by (cases f) simp

      from Cons.prems f obtain
        wf_d: "wf_field_desc d" and
        wf_ft: "wf_field_descs (set (field_descs ft))" and
        wf_fs': "wf_field_descs (set (field_descs_list fs'))" and
        ind_d: "field_desc_independent (field_access d) (field_update d)
          (set (toplevel_field_descs_list fs'))" and
        ind_fs': "field_descs_independent (toplevel_field_descs_list fs')"
        by auto

      from wf_d interpret wf_d: wf_field_desc d .

      note hyp = Cons.hyps [OF wf_fs' ind_fs']
      from field_update_apply_field_updates_commute [OF ind_d ind_fs']
      have eq1: "fst ((apply_field_updates (map dt_trd fs') (drop (field_sz d) bs))
                 (field_update d bs s)) =
               field_update d bs
                 (fst (apply_field_updates (map dt_trd fs') (drop (field_sz d) bs) s))"
           (is "_ = ?rhs")
        by (simp add: toplevel_field_descs_list_map)
      have eq2: "field_access d ?rhs bs' = field_access d (field_update d bs s) bs'"
        by (simp add: wf_d.access_update)
      from field_update_apply_field_updates_commute [OF ind_d ind_fs']
      have eq3: "fst (apply_field_updates (map dt_trd fs') (drop (field_sz d) bs)
                   (field_update d bs s')) =
                 field_update d bs
                  (fst (apply_field_updates (map dt_trd fs') (drop (field_sz d) bs) s'))"
           (is "_ = ?rhs")
        by (simp add: toplevel_field_descs_list_map)
      have eq4: "field_access d ?rhs bs' = field_access d (field_update d bs s) bs'"
        by (simp add: wf_d.access_update)
      show ?case
        apply (simp add: f eq1 eq2 eq3 eq4 wf_d.access_result_size)
        apply (simp only: eq1 [symmetric] )
        apply (simp only: eq3 [symmetric] )
        apply (simp add: hyp)
        done
    qed

    then show ?thesis
      by (simp add: TypDesc TypAggregate)
  qed
qed

lemma sum_nat_foldl: "(n::nat) + foldl (+) m xs = foldl (+) (n + m) xs"
  by (induct xs arbitrary: n m) (auto simp add: semiring_normalization_rules(25))

lemma sum_nat_foldl_le: "(n::nat) \<le> foldl (+) n xs"
  by (induct xs arbitrary: n) (auto elim: add_leE)

lemma sum_add_sub_foldl: "foldl (+) (m + n) ns - n = foldl (+) (m::nat) ns"
  apply (induct ns arbitrary: m n)
   apply simp
  apply (metis diff_add_inverse2 semiring_normalization_rules(24) sum_nat_foldl)
  done

lemma sum_sub_zero_foldl: "foldl (+) n ns - (n::nat) = foldl (+) 0 ns"
  using sum_add_sub_foldl [where m=0, simplified]
  by simp

lemma drop_take_sub: "drop n (take (foldl (+) n ns) bs) = take (foldl (+) 0 ns) (drop n bs)"
  by (simp add: drop_take sum_sub_zero_foldl)


lemma component_access_size:
  assumes wf: "wf_field_descs (set (field_descs t))"
  shows "field_access (component_desc t) s (take (field_sz (component_desc t)) bs) =
         field_access (component_desc t) s bs"
proof (cases t)
  case (TypDesc algn st n)
  show ?thesis
  proof (cases st)
    case (TypScalar sz align d)
    from TypDesc TypScalar have "d \<in> set (field_descs t)" by simp
    with wf have "wf_field_desc d" by (simp add: wf_field_descs_def)
    then interpret wf_d: wf_field_desc d .
    from TypDesc TypScalar wf_d.access_size show ?thesis
      by simp
  next
    case (TypAggregate fs)
    from wf have wf: "wf_field_descs (set (field_descs_list fs))" by (simp add: TypDesc TypAggregate)
    from wf
    have "concat (split_map (component_access_tuple s) fs
            (take (foldl (+) 0 (map (field_sz \<circ> dt_trd) fs)) bs)) =
          concat (split_map (component_access_tuple s) fs bs)"
    proof (induct fs arbitrary: s bs)
      case Nil
      then show ?case by simp
    next
      case (Cons f fs')
      obtain ft fn d where f: "f = DTuple ft fn d" by (cases f) simp

      from Cons.prems f obtain
        wf_d: "wf_field_desc d" and
        wf_ft: "wf_field_descs (set (field_descs ft))" and
        wf_fs': "wf_field_descs (set (field_descs_list fs'))"
        by auto

      from wf_d interpret wf_d: wf_field_desc d .

      have "field_sz d \<le> foldl (+) (field_sz d) (map (\<lambda>f'. field_sz (dt_trd f')) fs')" (is "?n \<le> ?m")
        by (rule sum_nat_foldl_le)
      then
      have eq1: "take ?n (take ?m bs) = take ?n bs"
        by (simp add: min_def)

      from wf_d.access_size [where bs="take ?m bs"]
      have "field_access d s (take ?m bs) = field_access d s (take ?n (take ?m bs))"
        by (simp)
      also have "\<dots> = field_access d s (take ?n bs)" by (simp only: eq1)
      also have "\<dots> = field_access d s bs" by (simp add: wf_d.access_size)
      finally
      have eq_head: "field_access d s (take (foldl (+) (field_sz d) (map (\<lambda>f'. field_sz (dt_trd f')) fs')) bs) =
                     field_access d s bs" .

      from Cons.hyps [OF wf_fs']
      show ?case
        by (simp add: f eq_head wf_d.access_result_size drop_take_sub)
    qed

    then show ?thesis
      by (simp add: TypDesc TypAggregate)
  qed
qed

lemma component_access_result_size:
  assumes wf: "wf_field_descs (set (field_descs t))"
  shows "length (field_access (component_desc t) s bs) = field_sz (component_desc t)"
proof (cases t)
  case (TypDesc algn st n)
  show ?thesis
  proof (cases st)
    case (TypScalar sz align d)
    from TypDesc TypScalar have "d \<in> set (field_descs t)" by simp
    with wf have "wf_field_desc d" by (simp add: wf_field_descs_def)
    then interpret wf_d: wf_field_desc d .
    from TypDesc TypScalar wf_d.access_result_size show ?thesis
      by simp
  next
    case (TypAggregate fs)
    from wf have wf: "wf_field_descs (set (field_descs_list fs))" by (simp add: TypDesc TypAggregate)
    from wf
    have "length (concat (split_map (component_access_tuple s) fs bs)) =
            foldl (+) 0 (map (field_sz \<circ> dt_trd) fs)"
    proof (induct fs arbitrary: s bs)
      case Nil
      then show ?case by simp
    next
      case (Cons f fs')
      obtain ft fn d where f: "f = DTuple ft fn d" by (cases f) simp

      from Cons.prems f obtain
        wf_d: "wf_field_desc d" and
        wf_ft: "wf_field_descs (set (field_descs ft))" and
        wf_fs': "wf_field_descs (set (field_descs_list fs'))"
        by auto

      from wf_d interpret wf_d: wf_field_desc d .

      note hyp = Cons.hyps [OF wf_fs']
      show ?case
        by (simp add: hyp wf_d.access_result_size f sum_nat_foldl)
    qed
    then show ?thesis by (simp add: TypDesc TypAggregate)
  qed
qed

lemma component_update_size:
  assumes wf: "wf_field_descs (set (field_descs t))"
  shows "field_update (component_desc t) (take (field_sz (component_desc t)) bs) s =
         field_update (component_desc t) bs s"
proof (cases t)
  case (TypDesc algn st n)
  show ?thesis
  proof (cases st)
    case (TypScalar sz align d)
    from TypDesc TypScalar have "d \<in> set (field_descs t)" by simp
    with wf have "wf_field_desc d" by (simp add: wf_field_descs_def)
    then interpret wf_d: wf_field_desc d .
    from TypDesc TypScalar wf_d.update_size show ?thesis
      by simp
  next
    case (TypAggregate fs)
    from wf have wf: "wf_field_descs (set (field_descs_list fs))" by (simp add: TypDesc TypAggregate)
    then have "fst (apply_field_updates (map dt_trd fs)
                 (take (foldl (+) 0 (map (field_sz \<circ> dt_trd) fs)) bs) s) =
               fst (apply_field_updates (map dt_trd fs) bs s)"
    proof (induct fs arbitrary: s bs)
      case Nil
      then show ?case by simp
    next
      case (Cons f fs')
      obtain ft fn d where f: "f = DTuple ft fn d" by (cases f) simp

      from Cons.prems f obtain
        wf_d: "wf_field_desc d" and
        wf_ft: "wf_field_descs (set (field_descs ft))" and
        wf_fs': "wf_field_descs (set (field_descs_list fs'))"
        by auto

      from wf_d interpret wf_d: wf_field_desc d .

      have "field_sz d \<le> foldl (+) (field_sz d) (map (\<lambda>a. field_sz (dt_trd a)) fs')" (is "?n \<le> ?m")
        by (rule sum_nat_foldl_le)
      then
      have eq1: "take ?n (take ?m bs) = take ?n bs"
        by (simp add: min_def)

      from wf_d.update_size [where bs="take ?m bs"]
      have "field_update d ((take ?m) bs) s = field_update d (take ?n (take ?m bs)) s" by simp
      also have "\<dots> = field_update d (take ?n bs) s" by (simp only: eq1)
      also from wf_d.update_size [where bs=bs]
      have "\<dots> = field_update d bs s" by simp
      finally have eq: "field_update d ((take ?m) bs) s = field_update d bs s" .


      note hyp = Cons.hyps [OF wf_fs', simplified comp_def]

      show ?case
        apply (simp add: f )
        apply (simp only: eq)
        apply (simp only: drop_take_sub)
        apply (simp only: hyp)
        done
    qed
    then show ?thesis by (simp add: TypDesc TypAggregate)
  qed
qed


lemma apply_field_updates_access_cancel:
  assumes wf: "wf_field_descs (set (field_descs_list fs))"
  assumes ind: "field_descs_independent (toplevel_field_descs_list fs)"
  shows "fst (apply_field_updates (map dt_trd fs) (concat (split_map (component_access_tuple v) fs bs)) v) = v"
  using wf ind
proof (induct fs arbitrary: v bs)
  case Nil
  then show ?case by simp
next
  case (Cons f fs')
  obtain ft fn d where f: "f = DTuple ft fn d" by (cases f) simp
  from Cons.prems f obtain
    wf_d: "wf_field_desc d" and
    wf_ft: "wf_field_descs (set (field_descs ft))" and
    wf_fs': "wf_field_descs (set (field_descs_list fs'))" and
    ind_d: "field_desc_independent (field_access d) (field_update d)
            (set (toplevel_field_descs_list fs'))" and
    ind_fs': "field_descs_independent (toplevel_field_descs_list fs')"
    by auto

  from wf_d interpret wf_d: wf_field_desc d .

  from wf_d.update_size [of "(field_access d v bs @
     concat (split_map (component_access_tuple v) fs' (drop (length (field_access d v bs)) bs)))"]
  have eq1: "field_update d
            (field_access d v bs @
               concat
                 (split_map (component_access_tuple v) fs'
                  (drop (length (field_access d v bs)) bs)))
         v = field_update d (field_access d v bs) v"

    by  (simp add: wf_d.access_result_size)

  note hyp = Cons.hyps [OF wf_fs' ind_fs']
  show ?case apply (simp add: Cons.prems f)
    apply (simp add: eq1)
    apply (simp add: wf_d.access_result_size wf_d.update_access hyp)
    done
qed

lemma apply_field_updates_double:
  assumes wf: "wf_field_descs (set (field_descs_list fs))"
  assumes ind: "field_descs_independent (toplevel_field_descs_list fs)"
  shows "fst (apply_field_updates (map dt_trd fs) bs
           (fst (apply_field_updates (map dt_trd fs) bs' v))) =
         fst (apply_field_updates (map dt_trd fs) bs v)"
  using wf ind
proof (induct fs arbitrary: v bs bs')
  case Nil
  then show ?case by simp
next
  case (Cons f fs')
  obtain ft fn d where f: "f = DTuple ft fn d" by (cases f) simp
  from Cons.prems f obtain
    wf_d: "wf_field_desc d" and
    wf_ft: "wf_field_descs (set (field_descs ft))" and
    wf_fs': "wf_field_descs (set (field_descs_list fs'))" and
    ind_d: "field_desc_independent (field_access d) (field_update d)
            (set (toplevel_field_descs_list fs'))" and
    ind_fs': "field_descs_independent (toplevel_field_descs_list fs')"
    by auto

  note commute = field_update_apply_field_updates_commute [OF ind_d ind_fs', simplified toplevel_field_descs_list_map]
  note hyp = Cons.hyps [OF wf_fs' ind_fs']
  from wf_d interpret wf_d: wf_field_desc d .
  show ?case apply (simp add: Cons.prems f)
    by (simp add: commute hyp wf_d.double_update)
qed

lemma list_append_eq_split_conv: "length xs1 = length xs2 \<Longrightarrow> xs1 @ ys1 = xs2 @ ys2 \<longleftrightarrow> xs1 = xs2 \<and> ys1 = ys2"
  by auto

lemma component_complement_padding:
  assumes wf: "wf_field_descs (set (field_descs t))"
  assumes ind: "field_descs_independent (toplevel_field_descs t)"
  assumes i_bound: "i < field_sz (component_desc t)"
  shows "padding_base.is_padding_byte (field_access (component_desc t))
          (field_update (component_desc t)) (field_sz (component_desc t)) i \<noteq>
         padding_base.is_value_byte (field_access (component_desc t))
          (field_update (component_desc t)) (field_sz (component_desc t)) i"
proof (cases t)
  case (TypDesc algn st n)
  show ?thesis
  proof (cases st)
    case (TypScalar sz align d)
    from TypDesc TypScalar have "d \<in> set (field_descs t)" by simp
    with wf have "wf_field_desc d" by (simp add: wf_field_descs_def)
    then interpret wf_d: wf_field_desc d .
    from TypDesc TypScalar wf_d.complement show ?thesis
      using i_bound
      by auto
  next
    case (TypAggregate fs)
    from wf have wf: "wf_field_descs (set (field_descs_list fs))" by (simp add: TypDesc TypAggregate)
    from ind have ind: "field_descs_independent (toplevel_field_descs_list fs)" by (simp add: TypDesc TypAggregate)
    from i_bound have i_bound': "i < foldl (+) 0 (map (field_sz \<circ> dt_trd) fs)" by (simp add: TypDesc TypAggregate)
    from wf ind i_bound'
    have "padding_base.is_padding_byte (component_access_struct (TypAggregate fs))
            (component_update_struct (TypAggregate fs))
            (foldl (+) 0 (map (field_sz \<circ> dt_trd) fs)) i =
          (\<not> padding_base.is_value_byte (component_access_struct (TypAggregate fs))
            (component_update_struct (TypAggregate fs))
            (foldl (+) 0 (map (field_sz \<circ> dt_trd) fs)) i)"
    proof (induct fs arbitrary: i)
      case Nil
      then show ?case by (simp add: padding_base.is_padding_byte_def padding_base.is_value_byte_def)
    next
      case (Cons f fs')
      obtain ft fn d where f: "f = DTuple ft fn d" by (cases f) simp
      from Cons.prems f obtain
        wf_d: "wf_field_desc d" and
        wf_ft: "wf_field_descs (set (field_descs ft))" and
        wf_fs': "wf_field_descs (set (field_descs_list fs'))" and
        ind_d: "field_desc_independent (field_access d) (field_update d)
          (set (toplevel_field_descs_list fs'))" and
        ind_fs': "field_descs_independent (toplevel_field_descs_list fs')" and
        i_bound: "i < foldl (+) (field_sz d) (map (\<lambda>a. field_sz (dt_trd a)) fs')"
        by (auto)

      have split_foldl:
        "(foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))) =
           field_sz d + (foldl (+) 0 (map (field_sz \<circ> dt_trd) fs'))"
        by (auto simp add: f sum_nat_foldl)

      from wf_d interpret wf_d: wf_field_desc d .

      note commute = field_update_apply_field_updates_commute [OF ind_d ind_fs', symmetric, simplified toplevel_field_descs_list_map]
      note hyp = Cons.hyps [OF wf_fs' ind_fs']
      show ?case
      proof (cases "i < field_sz d")
        case True
        note i_in_d = this
        show ?thesis
        proof (cases "wf_d.is_padding_byte i")
          case True
          note is_padding_d = this
          with True wf_d.complement i_in_d have not_value_d: "\<not> wf_d.is_value_byte i" by simp
          have "padding_base.is_padding_byte
                 (component_access_struct (TypAggregate (f # fs')))
                 (component_update_struct (TypAggregate (f # fs')))
                (foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))) i"
          proof (rule padding_base.is_padding_byteI)
            show "i < foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))"
              using i_bound
              by (simp add: f comp_def)
          next
            fix v::'a and bs::"byte list"
            assume "i < foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))"
            assume "length bs = foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))"
            hence lbs: "length bs = foldl (+) (field_sz d) (map (\<lambda>x. field_sz (dt_trd x)) fs')"
              by (simp add: f comp_def)
            hence lbs': "field_sz d \<le> length bs"
              using sum_nat_foldl_le by auto
            hence ltake: "length (take (field_sz d) bs) = field_sz d" by simp
            from  wf_d.access_size
            have acc_d_take: "field_access d v bs = field_access d v (take (field_sz d) bs)" by simp
            from wf_d.access_result_size have acc_d_sz: "length (field_access d v bs) = field_sz d" .
            have "field_access d v bs ! i = bs ! i"
              using i_in_d
              by (simp add:  acc_d_take wf_d.access_result_size wf_d.is_padding_byte_acc_id [OF is_padding_d ltake])
            then
            show "component_access_struct (TypAggregate (f # fs')) v bs ! i = bs ! i"
              using i_bound lbs i_in_d
              by (simp add: Cons f nth_append acc_d_sz)
          next
            fix v::'a and bs::"byte list" and b::byte
            assume "i < foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))"
            assume "length bs = foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))"
            hence lbs: "length bs = foldl (+) (field_sz d) (map (\<lambda>x. field_sz (dt_trd x)) fs')"
              by (simp add: f comp_def)
            hence lbs': "field_sz d \<le> length bs"
              using sum_nat_foldl_le by auto
            with i_in_d have drop_eq: "(drop (field_sz d) (bs[i := b])) = drop (field_sz d) bs"
              by (meson drop_update_cancel)
            from lbs' have ltake: "length (take (field_sz d) bs) = field_sz d" by simp
            have "(field_update d (bs[i := b]) v) = field_update d bs v"
              apply (subst (1 2) wf_d.update_size [symmetric])
              using wf_d.is_padding_byte_upd_eq [OF is_padding_d ltake] ltake
              by (metis take_update_swap)
            then
            show "component_update_struct (TypAggregate (f # fs')) bs v =
               component_update_struct (TypAggregate (f # fs')) (bs[i := b]) v"
              by (simp add: Cons f drop_eq)
          qed
          moreover
          {
            assume is_value: "padding_base.is_value_byte
                 (component_access_struct (TypAggregate (f # fs')))
                 (component_update_struct (TypAggregate (f # fs')))
                (foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))) i"
            have "wf_d.is_value_byte i"
            proof (rule wf_d.is_value_byteI)
              show "i < field_sz d" by (rule i_in_d)
            next
              fix v::'a and bs::"byte list" and bs'::"byte list"
              assume lbs: "length bs = field_sz d"
              assume lbs': "length bs' = field_sz d"
              obtain xbs where
                lxbs:"length xbs = (foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs')))" and
                bs: "bs = take (field_sz d) xbs" and
                split_xbs: "xbs = take (field_sz d) xbs @ drop (field_sz d) xbs"
                using lbs append_eq_conv_conj
                unfolding split_foldl
                by (metis (no_types, opaque_lifting) Ex_list_of_length length_append)
              obtain xbs' where
                lxbs':"length xbs' = (foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs')))" and
                bs': "bs' = take (field_sz d) xbs'" and
                split_xbs': "xbs' = take (field_sz d) xbs' @ drop (field_sz d) xbs'"
                using lbs' append_eq_conv_conj
                unfolding split_foldl
                by (metis (no_types, opaque_lifting) Ex_list_of_length length_append)
              have xbs_i: "xbs ! i = bs ! i"
                using bs split_xbs'
                by (simp add: bs i_in_d)

              have upd_xbs: "field_update d xbs v = field_update d bs v"
                apply (subst split_xbs)
                apply (subst wf_d.update_size [symmetric])
                apply simp
                apply (simp add: bs [symmetric])
                done

              from commute [where bs'="(drop (field_sz d) xbs)" and bs = bs and s=v]
              have acc_upd: "field_access d
                     (fst (apply_field_updates (map dt_trd fs') (drop (field_sz d) xbs)
                     (field_update d bs v)))
                     bs' = field_access d (field_update d bs v) bs'"
                using wf_d.access_update by auto


              from padding_base.is_value_byte_acc_upd_cancel [OF is_value lxbs lxbs']
              have "component_access_struct (TypAggregate (f # fs'))
                     (component_update_struct (TypAggregate (f # fs')) xbs v) xbs' !
                     i = xbs ! i" .
              then
              show "field_access d (field_update d bs v) bs' ! i = bs ! i"
                using lbs'  lbs' i_in_d
                apply (simp add: f xbs_i)
                apply (subst (asm) wf_d.access_size [symmetric])
                apply (simp add: bs' [symmetric])
                apply (simp add: wf_d.access_result_size nth_append upd_xbs acc_upd)
                done

            next
              fix v::'a and bs::"byte list" and b::byte
              assume lbs: "length bs = field_sz d"
              obtain xbs where
                lxbs:"length xbs = (foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs')))" and
                bs: "bs = take (field_sz d) xbs" and
                split_xbs: "xbs = take (field_sz d) xbs @ drop (field_sz d) xbs"
                using lbs append_eq_conv_conj
                unfolding split_foldl
                by (metis (no_types, opaque_lifting) Ex_list_of_length length_append)
              have eq1: "field_access d v xbs = field_access d v bs"
                using bs wf_d.access_size by simp
              have eq2: "field_access d v (xbs[i := b]) = field_access d v (bs[i := b])"
                using i_in_d bs
                by (metis take_update_swap wf_d.access_size)

              from padding_base.is_value_byte_acc_eq [OF is_value lxbs]
              have "component_access_struct (TypAggregate (f # fs')) v xbs =
                component_access_struct (TypAggregate (f # fs')) v (xbs[i := b])" .
              then
              show "field_access d v bs = field_access d v (bs[i := b])"
                apply (simp add: f)
                apply (subst (asm) list_append_eq_split_conv)
                 apply (simp add: wf_d.access_result_size)
                apply (clarsimp simp add: eq1 eq2)
                done
            qed
          }
          then
          have "\<not> padding_base.is_value_byte
                 (component_access_struct (TypAggregate (f # fs')))
                 (component_update_struct (TypAggregate (f # fs')))
                (foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))) i"
            using not_value_d
             by blast
          ultimately show ?thesis by blast
        next
          case False
          note not_padding = this
          with wf_d.complement i_in_d have is_value: "wf_d.is_value_byte i" by simp
          have "padding_base.is_value_byte
            (component_access_struct (TypAggregate (f # fs')))
            (component_update_struct (TypAggregate (f # fs')))
            (foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))) i"
          proof (rule padding_base.is_value_byteI)
            show "i < foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))"
              using i_bound by (simp add: f comp_def)
          next
            fix v::'a and bs::"byte list" and bs'::"byte list"
            assume lbs: "length bs = foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))"
            assume lbs': "length bs' = foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))"
            from lbs have lbs_take: "length (take (field_sz d) bs) = field_sz d"
              using lbs split_foldl by (simp add: f comp_def)
            from lbs' have lbs'_take: "length (take (field_sz d) bs') = field_sz d"
              using lbs split_foldl by (simp add: f comp_def)

            show "component_access_struct (TypAggregate (f # fs'))
                   (component_update_struct (TypAggregate (f # fs')) bs v) bs' !
                   i = bs ! i"
              apply (simp add: f)
              apply (subst wf_d.access_size [symmetric])
              using i_in_d
              apply (simp add: wf_d.access_result_size nth_append)
              apply (subst commute)
              apply (subst wf_d.access_update [where s'=v])
              using wf_d.is_value_byte_acc_upd_cancel [OF is_value lbs_take lbs'_take, of v]
              apply (simp add: wf_d.update_size)
              done
          next
            fix v::'a and bs::"byte list" and b::byte
            assume lbs: "length bs = foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))"
            from lbs have lbs_take: "length (take (field_sz d) bs) = field_sz d"
              using lbs split_foldl by (simp add: f comp_def)
            have acc_eq: "field_access d v bs = field_access d v (bs[i:=b])"
              apply (subst (1 2) wf_d.access_size [symmetric])
              using wf_d.is_value_byte_acc_eq [OF is_value lbs_take] i_in_d
              by (metis take_update_swap)

            show "component_access_struct (TypAggregate (f # fs')) v bs =
              component_access_struct (TypAggregate (f # fs')) v (bs[i := b])"
              apply (simp add: f acc_eq)
              using lbs_take i_in_d
              by (simp add: wf_d.access_result_size)
          qed
          moreover
          {
            assume is_padding: "padding_base.is_padding_byte
              (component_access_struct (TypAggregate (f # fs')))
              (component_update_struct (TypAggregate (f # fs')))
              (foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))) i"
            have "wf_d.is_padding_byte i"
            proof (rule wf_d.is_padding_byteI)
              from i_in_d show "i < field_sz d" .
            next
              fix v::'a and bs::"byte list"
              assume lbs: "length bs = field_sz d"
              obtain xbs where
                lxbs:"length xbs = (foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs')))" and
                bs: "bs = take (field_sz d) xbs" and
                split_xbs: "xbs = take (field_sz d) xbs @ drop (field_sz d) xbs"
                using lbs append_eq_conv_conj
                unfolding split_foldl
                by (metis (no_types, opaque_lifting) Ex_list_of_length length_append)
              from padding_base.is_padding_byte_acc_eq [OF is_padding lxbs, where v=v]

              show "field_access d v bs ! i = bs ! i"
                apply (simp add: f)
                by (simp add: bs i_in_d nth_append wf_d.access_result_size wf_d.access_size)
            next
              fix v::'a and bs::"byte list" and b::byte
              assume lbs: "length bs = field_sz d"
              obtain xbs where
                lxbs:"length xbs = (foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs')))" and
                bs: "bs = take (field_sz d) xbs" and
                split_xbs: "xbs = take (field_sz d) xbs @ drop (field_sz d) xbs"
                using lbs append_eq_conv_conj
                unfolding split_foldl
                by (metis (no_types, opaque_lifting) Ex_list_of_length length_append)
              from padding_base.is_padding_byte_upd_eq [OF is_padding lxbs, where v=v]
              show "field_update d bs v = field_update d (bs[i := b]) v"
                apply (simp add: f)
                by (metis bs commute take_update_swap wf_d.access_update wf_d.double_update
                    wf_d.update_access wf_d.update_size_ext)
            qed
          }
          with not_padding
          have "\<not> padding_base.is_padding_byte
            (component_access_struct (TypAggregate (f # fs')))
            (component_update_struct (TypAggregate (f # fs')))
            (foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))) i" by blast
          ultimately show ?thesis by blast
        qed
      next
        case False
        note i_notin_d = this
        with i_bound obtain n j where
          j_bound: "j < foldl (+) 0 (map (field_sz \<circ> dt_trd) fs')" and
          j: "j = i - field_sz d" and
          i: "i = j + field_sz d"
          apply (subst (asm) (2) sum_nat_foldl [where m = 0, simplified, symmetric])
          by (fastforce simp add: comp_def)
        note complement_fs'_j = hyp [OF j_bound]
        show ?thesis
        proof (cases "padding_base.is_padding_byte (component_access_struct (TypAggregate fs'))
                        (component_update_struct (TypAggregate fs'))
                        (foldl (+) 0 (map (field_sz \<circ> dt_trd) fs')) j ")
          case True
          note is_padding_j = this
          with complement_fs'_j have not_is_value_j:
            "\<not> padding_base.is_value_byte (component_access_struct (TypAggregate fs'))
                 (component_update_struct (TypAggregate fs'))
                 (foldl (+) 0 (map (field_sz \<circ> dt_trd) fs')) j" by blast
          have "padding_base.is_padding_byte
            (component_access_struct (TypAggregate (f # fs')))
            (component_update_struct (TypAggregate (f # fs')))
            (foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))) i"
          proof (rule padding_base.is_padding_byteI)
            from i_bound show "i < foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))" by (simp add: f comp_def)
          next
            fix v::'a and bs::"byte list"
            assume lbs: "length bs = foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))"
            from lbs have lbs_drop: "length (drop (field_sz d) bs) = foldl (+) 0 (map (field_sz \<circ> dt_trd) fs')"
              apply (subst (asm) split_foldl)
              apply (simp add: f)
              done
            show "component_access_struct (TypAggregate (f # fs')) v bs ! i = bs ! i"
              apply (simp add: f)
              using i_notin_d i
              apply (simp add: nth_append wf_d.access_result_size)
              using padding_base.is_padding_byte_acc_eq [OF is_padding_j lbs_drop, of v]
              apply simp
              by (metis add.commute lbs le_add_same_cancel1 nth_drop split_foldl sum_nat_foldl_le)
          next
            fix v::'a and bs::"byte list" and b::byte
            assume lbs: "length bs = foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))"
            from lbs have lbs_drop: "length (drop (field_sz d) bs) = foldl (+) 0 (map (field_sz \<circ> dt_trd) fs')"
              apply (subst (asm) split_foldl)
              apply (simp add: f)
              done
            from i_notin_d
            have tk_eq: "take (field_sz d) (bs[i := b]) = take (field_sz d) bs"
              by (meson not_less take_update_cancel)
            have upd_eq: "field_update d bs v = field_update d (bs[i := b]) v"
              apply (subst (1 2) wf_d.update_size [symmetric])
              apply (simp add: tk_eq)
              done
            show "component_update_struct (TypAggregate (f # fs')) bs v =
              component_update_struct (TypAggregate (f # fs')) (bs[i := b]) v"
              apply (simp add: f)
              apply (simp add: upd_eq [symmetric])
              using padding_base.is_padding_byte_upd_eq [OF is_padding_j lbs_drop, where v= "(field_update d bs v)" and b=b]
              apply (simp)
              by (metis drop_update_swap i j le_add2)
          qed
          moreover
          {
            assume is_value: "padding_base.is_value_byte
              (component_access_struct (TypAggregate (f # fs')))
              (component_update_struct (TypAggregate (f # fs')))
              (foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))) i"
            have "padding_base.is_value_byte (component_access_struct (TypAggregate fs'))
                 (component_update_struct (TypAggregate fs'))
                 (foldl (+) 0 (map (field_sz \<circ> dt_trd) fs')) j"
            proof (rule padding_base.is_value_byteI)
              from j_bound show "j < foldl (+) 0 (map (field_sz \<circ> dt_trd) fs')" .
            next
              fix v::'a and bs::"byte list" and bs'::"byte list"
              assume lbs: "length bs = foldl (+) 0 (map (field_sz \<circ> dt_trd) fs')"
              assume lbs': "length bs' = foldl (+) 0 (map (field_sz \<circ> dt_trd) fs')"
              obtain d_bs v_bs where v_bs: "v_bs = field_access d v d_bs" and
                l_v_bs: "length v_bs = field_sz d"
                using wf_d.access_result_size by auto
              obtain xbs where
                xbs_def: "xbs = v_bs @ bs" and
                xbs: "xbs = take (field_sz d) xbs @ bs" and
                lxbs: "length xbs = field_sz d + length bs"
                by (simp add: l_v_bs)
              obtain xbs' where
                xbs': "xbs' = take (field_sz d) xbs' @ bs'" and
                lxbs': "length xbs' = field_sz d + length bs'"
                by (metis Ex_list_of_length append_eq_conv_conj length_append)
              have xbs_i: "xbs ! i = bs ! j"
                by (metis add.commute append_take_drop_id i le_add2 lxbs nth_drop same_append_eq xbs)
              have drop_xbs': "drop (field_sz d) xbs' = bs'"
                by (metis append_take_drop_id same_append_eq xbs')
              have drop_xbs: "drop (field_sz d) xbs = bs"
                by (metis append_take_drop_id same_append_eq xbs)
              have upd_xbs: "field_update d xbs v = v"
                by (simp add: v_bs wf_d.update_access_append xbs_def)
              show "component_access_struct (TypAggregate fs')
                     (component_update_struct (TypAggregate fs') bs v) bs' !
                     j = bs ! j"
                apply (simp )
                using padding_base.is_value_byte_acc_upd_cancel
                  [OF is_value, where bs=xbs and bs'=xbs', simplified split_foldl,
                    OF lxbs [simplified lbs] lxbs' [simplified lbs'], where v = v]
                apply (simp add: xbs_i f nth_append wf_d.access_result_size i_notin_d drop_xbs' drop_xbs
                    j [symmetric] upd_xbs)
                done
            next
              fix v::'a and bs::"byte list" and b::"byte"
              assume lbs: "length bs = foldl (+) 0 (map (field_sz \<circ> dt_trd) fs')"
              obtain d_bs v_bs where v_bs: "v_bs = field_access d v d_bs" and
                l_v_bs: "length v_bs = field_sz d"
                using wf_d.access_result_size by auto
              obtain xbs where
                xbs_def: "xbs = v_bs @ bs" and
                xbs: "xbs = take (field_sz d) xbs @ bs" and
                lxbs: "length xbs = field_sz d + length bs"
                by (simp add: l_v_bs)
              have xbs_i: "xbs[i := b] = bs [j := b]"

                by (metis calculation component_sz_struct_aggregate is_value l_v_bs lbs len_gt_0
                    length_append less_irrefl padding_base.is_padding_byte_def padding_base.is_value_byte_upd_neq
                    split_foldl word_power_less_1 xbs_def)
              have drop_xbs: "drop (length (field_access d v xbs)) xbs = bs"
                by (simp add: l_v_bs wf_d.access_result_size xbs_def)

              show "component_access_struct (TypAggregate fs') v bs =
                component_access_struct (TypAggregate fs') v (bs[j := b])"
                apply (simp )
                using padding_base.is_value_byte_acc_eq [OF is_value, where bs=xbs, simplified split_foldl,
                    OF lxbs [simplified lbs], where v=v and b=b]
                apply (simp add: f)
                apply (subst (asm) list_append_eq_split_conv)
                 apply (simp add: wf_d.access_result_size)
                apply (clarsimp simp add: drop_xbs)
                apply (simp add: xbs_i)
                by (metis (no_types, opaque_lifting) append_Nil append_eq_append_conv append_eq_conv_conj
                    l_v_bs length_list_update wf_d.access_result_size xbs_def xbs_i)
            qed
          }
          with not_is_value_j
          have "\<not> padding_base.is_value_byte
            (component_access_struct (TypAggregate (f # fs')))
            (component_update_struct (TypAggregate (f # fs')))
            (foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))) i" by blast

          ultimately show ?thesis by blast
        next
          case False
          note not_is_padding_j = this
          with complement_fs'_j have is_value_j:
            "padding_base.is_value_byte (component_access_struct (TypAggregate fs'))
                 (component_update_struct (TypAggregate fs'))
                 (foldl (+) 0 (map (field_sz \<circ> dt_trd) fs')) j" by blast
          have "padding_base.is_value_byte
                  (component_access_struct (TypAggregate (f # fs')))
                  (component_update_struct (TypAggregate (f # fs')))
                  (foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))) i"
          proof (rule padding_base.is_value_byteI)
            from i_bound show "i < foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))" by (simp add: f comp_def)
          next
            fix v::'a and bs::"byte list" and bs'::"byte list"
            assume lbs: "length bs = foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))"
            assume lbs': "length bs' = foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))"
            from lbs have lbs_drop: "length (drop (field_sz d) bs) = foldl (+) 0 (map (field_sz \<circ> dt_trd) fs')"
              apply (subst (asm) split_foldl)
              apply (simp add: f)
              done
            from lbs' have lbs'_drop: "length (drop (field_sz d) bs') = foldl (+) 0 (map (field_sz \<circ> dt_trd) fs')"
              apply (subst (asm) split_foldl)
              apply (simp add: f)
              done
            have drop_j: "drop (field_sz d) bs ! j = bs ! i"
              by (metis add.commute i lbs le_add_same_cancel1 nth_drop split_foldl zero_le)
            show "component_access_struct (TypAggregate (f # fs'))
                    (component_update_struct (TypAggregate (f # fs')) bs v) bs' !
                    i = bs ! i"
              apply (simp add: f nth_append i_notin_d wf_d.access_result_size j[symmetric])
              using padding_base.is_value_byte_acc_upd_cancel [OF is_value_j lbs_drop lbs'_drop, where v = "field_update d bs v"]
              apply (simp add: drop_j)
              done
          next
            fix v::'a and bs::"byte list" and b::"byte"
            assume lbs: "length bs = foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))"
            from lbs have lbs_drop: "length (drop (field_sz d) bs) = foldl (+) 0 (map (field_sz \<circ> dt_trd) fs')"
              apply (subst (asm) split_foldl)
              apply (simp add: f)
              done
            have acc_eq: "field_access d v bs = field_access d v (bs[i := b])"
              by (metis i le_add2 take_update_cancel wf_d.access_size)
            show "component_access_struct (TypAggregate (f # fs')) v bs =
                   component_access_struct (TypAggregate (f # fs')) v (bs[i := b])"
              apply (simp add: f)
              apply (subst list_append_eq_split_conv)
               apply (simp add: wf_d.access_result_size)
              apply (simp add: acc_eq)
              using padding_base.is_value_byte_acc_eq [OF is_value_j lbs_drop, where v="v" and b=b]
              apply simp
              by (metis drop_update_swap i j le_add2 wf_d.access_result_size)
          qed
          moreover
          {
            assume is_padding: "padding_base.is_padding_byte
                      (component_access_struct (TypAggregate (f # fs')))
                      (component_update_struct (TypAggregate (f # fs')))
                      (foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))) i"
            have "padding_base.is_padding_byte (component_access_struct (TypAggregate fs'))
                    (component_update_struct (TypAggregate fs'))
                    (foldl (+) 0 (map (field_sz \<circ> dt_trd) fs')) j"
            proof (rule padding_base.is_padding_byteI)
              from j_bound show "j < foldl (+) 0 (map (field_sz \<circ> dt_trd) fs')" .
            next
              fix v::'a and bs::"byte list"
              assume lbs: "length bs = foldl (+) 0 (map (field_sz \<circ> dt_trd) fs')"
              obtain d_bs v_bs where v_bs: "v_bs = field_access d v d_bs" and
                l_v_bs: "length v_bs = field_sz d"
                using wf_d.access_result_size by auto
              obtain xbs where
                xbs_def: "xbs = v_bs @ bs" and
                xbs: "xbs = take (field_sz d) xbs @ bs" and
                lxbs: "length xbs = field_sz d + length bs"
                by (simp add: l_v_bs)
              have drop_eq: "(drop (field_sz d) xbs) = bs"
                by (simp add: l_v_bs xbs_def)
              have xbs_i: "xbs ! i = bs ! j"
                by (simp add: i_notin_d j l_v_bs nth_append xbs_def)
              show "component_access_struct (TypAggregate fs') v bs ! j = bs ! j"
                using padding_base.is_padding_byte_acc_eq [OF is_padding, where bs=xbs, simplified split_foldl,
                    OF lxbs [simplified lbs], where v = v]
                apply (simp add: f nth_append wf_d.access_result_size i_notin_d j [symmetric] drop_eq xbs_i)
                done
            next
              fix v::'a and bs::"byte list" and b::byte
              assume lbs: "length bs = foldl (+) 0 (map (field_sz \<circ> dt_trd) fs')"
              obtain d_bs v_bs where v_bs: "v_bs = field_access d v d_bs" and
                l_v_bs: "length v_bs = field_sz d"
                using wf_d.access_result_size by auto
              obtain xbs where
                xbs_def: "xbs = v_bs @ bs" and
                xbs: "xbs = take (field_sz d) xbs @ bs" and
                lxbs: "length xbs = field_sz d + length bs"
                by (simp add: l_v_bs)
              have drop_eq: "(drop (field_sz d) xbs) = bs"
                by (simp add: l_v_bs xbs_def)

              have xbs_i: "xbs [i := b] = bs [j := b]"
                by (metis calculation is_padding l_v_bs lbs len_gt_0 length_append less_irrefl
                    padding_base.is_padding_byte_acc_neq padding_base.is_value_byte_def split_foldl word_power_less_1 xbs_def)
              have upd_eq: "(field_update d xbs v) = v"
                by (simp add: v_bs wf_d.update_access_append xbs_def)
              have eq: "fst (apply_field_updates (map dt_trd fs') (bs[j := b]) v) = fst (apply_field_updates (map dt_trd fs') bs v)"
                by (metis calculation is_padding lbs list_update_id lxbs padding_base.is_padding_byte_acc_neq
                    padding_base.is_value_byte_acc_eq split_foldl)
              show "component_update_struct (TypAggregate fs') bs v =
                      component_update_struct (TypAggregate fs') (bs[j := b]) v"
                using padding_base.is_padding_byte_upd_eq [OF is_padding, where bs=xbs, simplified split_foldl,
                    OF lxbs [simplified lbs], where v = v and b = b]
                apply (simp add: f drop_eq xbs_i upd_eq eq)
                done
            qed
          }
          with not_is_padding_j
          have "\<not> padding_base.is_padding_byte
                    (component_access_struct (TypAggregate (f # fs')))
                    (component_update_struct (TypAggregate (f # fs')))
                    (foldl (+) 0 (map (field_sz \<circ> dt_trd) (f # fs'))) i" by blast
          ultimately show ?thesis by blast
        qed
      qed
    qed

    then show ?thesis
      by (simp add: TypDesc TypAggregate)
  qed
qed


theorem wf_field_desc_component_desc:
  assumes wf:"wf_field_descs (set (field_descs t))"
  assumes ind: "field_descs_independent (toplevel_field_descs t)"
  shows "wf_field_desc (component_desc t)"
  apply (unfold_locales)
        apply (rule component_complement_padding [OF wf ind], assumption)
       apply (rule component_double_update [OF wf ind])
      apply (rule component_access_update [OF wf ind])
     apply (rule component_update_access [OF wf])
    apply (rule component_access_size [OF wf])
   apply (rule component_access_result_size [OF wf])
  apply (rule ext, rule component_update_size [OF wf])
  done



(* fixme: move up *)
lemma field_desc_list_append [simp]: "field_descs_list (fs1 @ fs2) = field_descs_list fs1 @ field_descs_list fs2"
  by (induct fs1 arbitrary: fs2) auto

(* fixme: move up *)
lemma toplevel_field_desc_list_append [simp]:
"toplevel_field_descs_list (fs1 @ fs2) = toplevel_field_descs_list fs1 @ toplevel_field_descs_list fs2"
  by (induct fs1 arbitrary: fs2) auto

corollary wf_field_descs_struct_append_first:
  assumes wf:"wf_field_descs (set (field_descs_struct (TypAggregate (fs1 @ fs2))))"
  assumes ind: "field_descs_independent (toplevel_field_descs_struct (TypAggregate (fs1 @ fs2)))"
  shows "wf_field_desc (component_desc_struct (TypAggregate fs1))"
proof -
  fix algn
  from wf have wf': "wf_field_descs (set (field_descs (TypDesc algn (TypAggregate fs1) [])))"
    by simp
  from ind
  have ind': "field_descs_independent (toplevel_field_descs (TypDesc algn (TypAggregate fs1) []))"
    by (simp add: field_descs_independent_append_first)
  from wf_field_desc_component_desc [OF wf' ind']
  show ?thesis
    by simp
qed

corollary wf_field_descs_struct_append_second:
  assumes wf:"wf_field_descs (set (field_descs_struct (TypAggregate (fs1 @ fs2))))"
  assumes ind: "field_descs_independent (toplevel_field_descs_struct (TypAggregate (fs1 @ fs2)))"
  shows "wf_field_desc (component_desc_struct (TypAggregate fs2))"
proof -
  fix algn
  from wf have wf': "wf_field_descs (set (field_descs (TypDesc algn (TypAggregate fs2) [])))"
    by simp
  from ind
  have ind': "field_descs_independent (toplevel_field_descs (TypDesc algn (TypAggregate fs2) []))"
    by (simp add: field_descs_independent_append_second)
  from wf_field_desc_component_desc [OF wf' ind']
  show ?thesis
    by simp
qed


corollary wf_field_descs_component_desc:
  assumes wf:"wf_field_descs (set (field_descs t))"
  assumes ind: "field_descs_independent (toplevel_field_descs t)"
  shows "wf_field_descs (insert (component_desc t) (set (field_descs t)))"
  using wf_field_desc_component_desc [OF wf ind] wf
  by simp

lemma size_td_field_sz:
  fixes
    t::"'a xtyp_info" and
    st::"'a xtyp_info_struct" and
    fs::"'a xtyp_info_tuple list" and
    f::"'a xtyp_info_tuple"
  shows
 "wf_component_descs t \<Longrightarrow> size_td t = field_sz (component_desc t)"
 "wf_component_descs_struct st \<Longrightarrow> size_td_struct st = field_sz (component_desc_struct st)"
 "wf_component_descs_list fs \<Longrightarrow> size_td_list fs = field_sz (component_desc_struct (TypAggregate fs))"
 "wf_component_descs_tuple f \<Longrightarrow> size_td_tuple f = field_sz (dt_trd f)"
proof (induct t and st and fs and f)
  case (Cons_typ_desc dt_tuple list)
  then show ?case 
    apply (cases dt_tuple)
    apply (clarsimp simp add: sum_nat_foldl)
    done
qed auto


(* fixme unused? *)
lemma (in c_type) simple_type_to_xto_eq:
  fixes v::"'a"
  assumes simple: "\<not> aggregate (typ_info_t TYPE('a))"
  shows "to_bytes v = xto_bytes v"
proof -
  from simple_type_dest [OF simple]
  show ?thesis
    by (clarsimp simp add: xto_bytes_def to_bytes_def)
qed


(* fixme move up *)
lemma field_desc_independent_empty [simp]: "field_desc_independent acc upd {}"
  by (simp add: field_desc_independent_def)


lemma component_descs_field_descs_independent:
 "component_descs_independent t \<Longrightarrow> field_descs_independent (toplevel_field_descs t)"
  apply (cases t)
  subgoal for x1 st nm
    apply (cases st)
     apply (simp )
    subgoal for fs
      apply (cases fs)
       apply simp
      apply simp
      done
    done
  done

lemma component_descs_list_field_descs_independent:
 "component_descs_independent_list fs \<Longrightarrow> field_descs_independent (toplevel_field_descs_list fs)"
   apply (cases fs)
   apply simp
  apply simp
  done


theorem access_ti_component_desc_compatible:
  "\<And>bs v::'a. \<lbrakk>wf_component_descs t; component_descs_independent t;
    wf_field_descs (set (field_descs t))\<rbrakk>
   \<Longrightarrow> access_ti t v bs = field_access (component_desc t) v bs"
  "\<And>bs v::'a. \<lbrakk>wf_component_descs_struct st; component_descs_independent_struct st;
    wf_field_descs (set (field_descs_struct st))\<rbrakk>
   \<Longrightarrow> access_ti_struct st v bs = field_access (component_desc_struct st) v bs"
  "\<And>bs v::'a. \<lbrakk>wf_component_descs_list fs; component_descs_independent_list fs;
    wf_field_descs (set (field_descs_list fs))\<rbrakk>
   \<Longrightarrow> access_ti_list fs v bs = field_access (component_desc_struct (TypAggregate fs)) v bs"
  "\<And>bs v::'a. \<lbrakk>wf_component_descs_tuple f; component_descs_independent_tuple f;
    wf_field_descs (set (field_descs (dt_fst f)))\<rbrakk>
   \<Longrightarrow> access_ti_tuple f v bs = field_access (dt_trd f) v bs"
proof (induct t and st and fs and f (*arbitrary: bs v*)) (* fixme: figure out why arbitrary bs v does not work *)
  case (TypDesc algn st n)
  then show ?case by simp
next
  case (TypScalar sz align d)
  then show ?case by simp
next
  case (TypAggregate fs)
  then show ?case by simp
next
  case Nil_typ_desc
  then show ?case by simp
next
  case (Cons_typ_desc f fs')
  obtain ft fn d where f: "f = DTuple ft fn d" by (cases f) simp

  from Cons_typ_desc.prems obtain
     wf_descs_f: "wf_component_descs_tuple f" and wf_descs_fs': "wf_component_descs_list fs'" and
     ind: "field_descs_independent (toplevel_field_descs_tuple f @ toplevel_field_descs_list fs')" and
     ind_cf: "component_descs_independent_tuple f" and
     ind_cfs': "component_descs_independent_list fs'" and
     wf_field_desc_f: "wf_field_descs (set (field_descs (dt_fst f)))" and
     wf_d: "wf_field_desc d" and wf_ft: "wf_field_descs (set (field_descs ft))" and
     wf_field_descs_fs': "wf_field_descs (set (field_descs_list fs'))"
    by (auto simp add: f)


  note ind_fs' = field_descs_independent_append_second [OF ind]

  from wf_d interpret wf_d: wf_field_desc d.


  have wf_fd_fs': "wf_field_descs (insert (component_desc_struct (TypAggregate fs'))
          (set (field_descs_list fs')))"
  proof -
    fix algn
    from wf_field_descs_fs'
    have wf:"wf_field_descs (set (field_descs (TypDesc algn (TypAggregate fs') [])))"
      by simp
    from ind_fs'
    have ind: "field_descs_independent (toplevel_field_descs (TypDesc algn (TypAggregate fs') []))"
      by simp
    from wf_field_descs_component_desc [OF wf ind] show ?thesis
      by simp
  qed


  from Cons_typ_desc.hyps(1) [OF wf_descs_f ind_cf wf_field_desc_f ]
  have eq_f: "access_ti_tuple f v (take (size_td ft) bs) =
              field_access (dt_trd f) v (take (size_td ft) bs)".
  from Cons_typ_desc.hyps(2) [OF wf_descs_fs' ind_cfs' wf_field_descs_fs' ]
  have eq_fs': "access_ti_list fs' v (drop (size_td ft) bs) =
                 field_access (component_desc_struct (TypAggregate fs')) v
                 (drop (size_td ft) bs)" .

  from wf_descs_f have sz_eq: "field_sz d = size_td ft" by (simp add: f size_td_field_sz)


  from sz_eq wf_d.access_size
  have eq_access_take: "field_access d v (take (size_td ft) bs) = field_access d v bs"
    by (simp )

  from wf_descs_f have sz_eq: "field_sz d = size_td ft" by (simp add: f size_td_field_sz)

  from eq_f eq_fs' eq_access_take
    show ?case by (simp add: f wf_d.access_result_size size_td_field_sz sz_eq)
next
  case (DTuple_typ_desc ft fn d)
  from DTuple_typ_desc.prems obtain
    d: "d = component_desc ft" and
    wf_ft: "wf_component_descs ft" and
    ind_cf: "component_descs_independent ft" and
    wf_descs_ft: "wf_field_descs (set (field_descs ft))"
    by auto

  from wf_field_descs_component_desc [OF wf_descs_ft] ind_cf
  have wf_desc_ft: "wf_field_desc (component_desc ft)"
    by (auto intro: component_descs_field_descs_independent)
  from component_descs_field_descs_independent [OF ind_cf]
  have "field_descs_independent (toplevel_field_descs ft)" .

  from DTuple_typ_desc.hyps [OF wf_ft ind_cf wf_descs_ft ]

  show ?case by (simp add: d)
qed

theorem update_ti_component_desc_compatible:
  "\<And>bs v::'a. \<lbrakk>wf_component_descs t; component_descs_independent t;
    wf_field_descs (set (field_descs t))\<rbrakk>
   \<Longrightarrow> update_ti t bs v = field_update (component_desc t) bs v"
  "\<And>bs v::'a. \<lbrakk>wf_component_descs_struct st; component_descs_independent_struct st;
    wf_field_descs (set (field_descs_struct st))\<rbrakk>
   \<Longrightarrow> update_ti_struct st bs v = field_update (component_desc_struct st) bs v"
  "\<And>bs v::'a. \<lbrakk>wf_component_descs_list fs; component_descs_independent_list fs;
    wf_field_descs (set (field_descs_list fs))\<rbrakk>
   \<Longrightarrow> update_ti_list fs bs v = field_update (component_desc_struct (TypAggregate fs)) bs v"
  "\<And>bs v::'a. \<lbrakk>wf_component_descs_tuple f; component_descs_independent_tuple f;
    wf_field_descs (set (field_descs (dt_fst f)))\<rbrakk>
   \<Longrightarrow> update_ti_tuple f bs v = field_update (dt_trd f) bs v"
proof (induct t and st and fs and f (*arbitrary: bs v*)) (* fixme: figure out why arbitrary bs v does not work *)
  case (TypDesc algn st n)
  then show ?case by simp
next
  case (TypScalar sz align d)
  then show ?case by simp
next
  case (TypAggregate fs)
  then show ?case by simp
next
  case Nil_typ_desc
  then show ?case by simp
next
  case (Cons_typ_desc f fs')
  obtain ft fn d where f: "f = DTuple ft fn d" by (cases f) simp

  from Cons_typ_desc.prems obtain
     wf_descs_f: "wf_component_descs_tuple f" and wf_descs_fs': "wf_component_descs_list fs'" and
     ind: "field_descs_independent (toplevel_field_descs_tuple f @ toplevel_field_descs_list fs')" and
     ind_cf: "component_descs_independent_tuple f" and
     ind_cfs': "component_descs_independent_list fs'" and
     ind_d: "field_desc_independent (field_access d) (field_update d) (set (toplevel_field_descs_list fs'))" and
     wf_field_desc_f: "wf_field_descs (set (field_descs (dt_fst f)))" and
     wf_d: "wf_field_desc d" and wf_ft: "wf_field_descs (set (field_descs ft))" and
     wf_field_descs_fs': "wf_field_descs (set (field_descs_list fs'))"
    by (auto simp add: f)


  note ind_fs' = field_descs_independent_append_second [OF ind]

  from wf_d interpret wf_d: wf_field_desc d.

  from Cons_typ_desc.hyps(2) [OF wf_descs_fs' ind_cfs' wf_field_descs_fs' ]
  have eq_fs': "update_ti_list fs' (drop (size_td ft) bs) v =
         fst (apply_field_updates (map dt_trd fs') (drop (size_td ft) bs) v)" (is "?upd_ti_fs' = ?upd_fs'")
    by simp

  from Cons_typ_desc.hyps(1) [OF wf_descs_f ind_cf wf_field_desc_f ]
  have eq_f: "update_ti ft (take (size_td ft) bs) ?upd_ti_fs' =
                field_update d (take (size_td ft) bs) ?upd_fs'" by (simp add: f eq_fs')
  also
  from field_update_apply_field_updates_commute [OF ind_d ind_fs', where bs= "(take (size_td ft) bs)" and bs'="(drop (size_td ft) bs)"]
  have "\<dots> = fst (apply_field_updates (toplevel_field_descs_list fs') (drop (size_td ft) bs)
                (field_update d (take (size_td ft) bs) v))"
    by (simp add: toplevel_field_descs_list_map)
  finally have eq_ft: "update_ti ft (take (size_td ft) bs) ?upd_ti_fs' =
    fst (apply_field_updates (toplevel_field_descs_list fs') (drop (size_td ft) bs)
          (field_update d (take (size_td ft) bs) v))" .

  from size_td_field_sz(1) [of ft] wf_descs_f
  have sz_d: "field_sz d = size_td ft"
    by (simp add: f)


  show ?case
    apply (simp add: f )
    apply (simp add: eq_ft toplevel_field_descs_list_map wf_d.update_size [simplified sz_d] sz_d)
    done
next
  case (DTuple_typ_desc ft fn d)
  then show ?case by simp
qed


context xmem_type
begin


lemma wf_field_desc_component_desc: "wf_field_desc (component_desc (typ_info_t (TYPE('a))))"
  using wf_field_descs component_descs_independent
  by (auto intro: wf_field_desc_component_desc component_descs_field_descs_independent)

lemma wf_field_descs': "wf_field_descs (insert (component_desc (typ_info_t (TYPE('a))))
                            (set (field_descs (typ_info_t (TYPE('a))))))"
  using wf_field_descs
  by (auto intro: wf_field_desc_component_desc)

lemma wf_field_desc_t: "wf_field_desc (component_desc (typ_info_t (TYPE('a))))"
  using wf_field_descs' by (simp)

sublocale xmem_type_wf_field_desc: wf_field_desc "component_desc (typ_info_t (TYPE('a)))"
  by (rule wf_field_desc_t)

lemma xfrom_bytes_xto_bytes_inv: "xfrom_bytes (xto_bytes (v::'a) bs) = v"
proof -
  define t where "t = (typ_info_t TYPE('a))"
  have wf_comp_descs_t: "wf_component_descs t" by (simp add: wf_component_descs t_def)
  have ind_t: "component_descs_independent t" by (simp add: component_descs_independent t_def)
  from wf_field_descs
  have wf_field_descs_t: "wf_field_descs (set (field_descs t))"
    by (simp add: t_def)
  have xto: "xto_bytes v bs = field_access (component_desc t) v bs" (is "(_ = ?acc)")
    by (simp add: xto_bytes_def t_def)

  from wf_field_desc_component_desc have "wf_field_desc (component_desc t)" by (simp add: t_def)
  then interpret wf_t: wf_field_desc "component_desc t".
  from wf_t.access_result_size
  have len_acc: "length ?acc = field_sz (component_desc t)" .
  from size_td_field_sz(1) [OF wf_comp_descs_t]
  have size_t: "size_td t = field_sz (component_desc t)".
  have len_acc': "size_td t = length ?acc" by (simp add: len_acc size_t)
  from size_t len_acc
  have len_acc'': "length ?acc = size_of TYPE('a)" by (simp add: size_of_def t_def)
  from len_acc'' len_acc'
  have len_acc''': "size_of TYPE('a) = size_td (typ_info_t TYPE('a))" by (simp add: t_def)

  from update_ti_component_desc_compatible(1) [OF wf_comp_descs_t ind_t wf_field_descs_t ]
  have "field_update (component_desc t) (field_access (component_desc t) v bs) undefined =
        update_ti t (field_access (component_desc t) v bs) undefined" by simp
  also
  from upd [rule_format, OF len_acc'', folded t_def, where v= undefined and w = v] len_acc' t_def
  have "\<dots> = update_ti t (field_access (component_desc t) v bs) v" by (simp add: update_ti_t_def)
  also
  from update_ti_component_desc_compatible(1) [OF wf_comp_descs_t ind_t wf_field_descs_t ]
  have "\<dots> = field_update (component_desc t) (field_access (component_desc t) v bs) v" .
  also
  from wf_t.update_access
  have "\<dots> = v" .
  finally
  have "field_update (component_desc t) (field_access (component_desc t) v bs) undefined = v" .

  with len_acc show ?thesis
    by (simp add: xto xfrom_bytes_def t_def)
qed

lemma xto_bytes_inj:
  "xto_bytes (v::'a) = xto_bytes (v'::'a) \<Longrightarrow> v = v'"
  apply (drule fun_cong [where x="replicate (size_of TYPE('a)) 0"])
  apply (drule arg_cong [where f="xfrom_bytes::byte list \<Rightarrow> 'a"])
  apply (simp add: xfrom_bytes_xto_bytes_inv)
  done

lemma field_update_update_ti_t:
  assumes len: "length bs = size_td (typ_info_t (TYPE('a)))"
  shows "field_update (component_desc (typ_info_t (TYPE('a)))) bs = update_ti_t (typ_info_t (TYPE('a))) bs"
proof -
  from len
    update_ti_component_desc_compatible(1) [OF wf_component_descs component_descs_independent
      wf_field_descs]
  show ?thesis
    by (simp add: update_ti_t_def fun_eq_iff)
qed

lemma field_update_update_ti:
  shows "field_update (component_desc (typ_info_t (TYPE('a)))) = update_ti (typ_info_t (TYPE('a)))"
proof -
  from
    update_ti_component_desc_compatible(1) [OF wf_component_descs component_descs_independent
      wf_field_descs]
  show ?thesis
    by (simp add: fun_eq_iff)
qed

lemma field_access_access_ti:
  shows "field_access (component_desc (typ_info_t (TYPE('a)))) = access_ti (typ_info_t (TYPE('a))) "
proof -
  from
    access_ti_component_desc_compatible(1) [OF wf_component_descs component_descs_independent
      wf_field_descs]
  show ?thesis
    by (simp add: fun_eq_iff)
qed

lemma field_sz_size_td:
  "field_sz (component_desc (typ_info_t (TYPE('a)))) = size_td (typ_info_t (TYPE('a)))"
  by (simp add: local.wf_component_descs size_td_field_sz(1))

lemma field_sz_size_of:
  "field_sz (component_desc (typ_info_t (TYPE('a)))) = size_of (TYPE('a))"
  by (simp add: size_of_def field_sz_size_td)



lemma xto_bytes_size: "xto_bytes (v::'a) (take (size_td (typ_info_t TYPE('a))) bs) = xto_bytes v bs"
proof -
  from xmem_type_wf_field_desc.access_size size_td_field_sz(1) [OF wf_component_descs]
  show ?thesis
  by (simp add: xto_bytes_def)
qed

lemma xto_bytes_result_size: "length (xto_bytes (v::'a) bs) = size_td (typ_info_t TYPE('a))"
proof -
  from xmem_type_wf_field_desc.access_result_size size_td_field_sz(1) [OF wf_component_descs]
  show ?thesis
  by (simp add: xto_bytes_def)
qed


lemma xfrom_bytes_size: "(xfrom_bytes::byte list \<Rightarrow> 'a) (take (size_td (typ_info_t TYPE('a))) bs) = xfrom_bytes bs"
proof -
  from xmem_type_wf_field_desc.update_size [where bs=bs] size_td_field_sz(1) [OF wf_component_descs]
  show ?thesis
    by (simp add: xfrom_bytes_def)
qed

lemma entire_update:
  shows "field_update (component_desc (typ_info_t (TYPE('a)))) bs v = field_update (component_desc (typ_info_t (TYPE('a)))) bs w"
    by (metis xmem_type_wf_field_desc.double_update xfrom_bytes_def xfrom_bytes_xto_bytes_inv)

lemma update_access_complete:
  shows "field_update (component_desc (typ_info_t (TYPE('a)))) (field_access (component_desc (typ_info_t (TYPE('a)))) v bs) w = v"
  by (metis entire_update xmem_type_wf_field_desc.update_access)


end


lemma contained_field_descs_list_all: "contained_field_descs_list xs = list_all contained_field_descs_tuple xs"
  by (induct xs) auto


lemma toplevel_field_descs_map:
  "toplevel_field_descs (map_td (\<lambda>_ _. update_desc acc upd) (update_desc acc upd) t) =
     map (update_desc acc upd) (toplevel_field_descs t)"
  "toplevel_field_descs_struct (map_td_struct (\<lambda>_ _. update_desc acc upd) (update_desc acc upd) st) =
     map (update_desc acc upd) (toplevel_field_descs_struct st)"
  "toplevel_field_descs_list (map_td_list (\<lambda>_ _. update_desc acc upd) (update_desc acc upd) fs) =
     map (update_desc acc upd) (toplevel_field_descs_list fs)"
  "toplevel_field_descs_tuple (map_td_tuple (\<lambda>_ _. update_desc acc upd) (update_desc acc upd) f) =
     map (update_desc acc upd) (toplevel_field_descs_tuple f)"
     by (induct t and st and fs and f) auto

lemma toplevel_field_descs_adjust_ti: "toplevel_field_descs (adjust_ti t acc upd) = map (update_desc acc upd) (toplevel_field_descs t)"
  by (simp add: adjust_ti_def toplevel_field_descs_map)

theorem contained_field_descs_empty_typ_info [simp]: "contained_field_descs (empty_typ_info algn n)"
  by (simp add: empty_typ_info_def)

lemma fields_contained_update_desc:
  assumes contained_t: "fields_contained (field_access d) (field_update d) (set (toplevel_field_descs t))"
  shows "fields_contained (field_access (update_desc acc upd d))
     (field_update (update_desc acc upd d))
     (update_desc acc upd ` set (toplevel_field_descs t))"
proof (rule fields_contained.intro)
  fix d' s s'
  assume d'_in: "d' \<in> update_desc acc upd ` set (toplevel_field_descs t)"
  assume acc_contained: "field_access (update_desc acc upd d) s =
       field_access (update_desc acc upd d) s'"

  interpret ft: fields_contained "(field_access d)" "(field_update d)" "set (toplevel_field_descs t)"
    by (rule contained_t)

  from acc_contained have acc: "field_access d (acc s) = field_access d (acc s')"
    by (simp add: update_desc_def)

  from d'_in obtain d'' where
    d''_in: "d'' \<in> set (toplevel_field_descs t)" and
    d': "d' = update_desc acc upd d''"
    by auto

  from ft.access_contained [OF d''_in acc]
  have "field_access d'' (acc s) = field_access d'' (acc s')".
  with d'
  show "field_access d' s = field_access d' s'"
    by (simp add: update_desc_def)
next
  fix d' bs s
  assume d'_in: "d' \<in> update_desc acc upd ` set (toplevel_field_descs t)"

  interpret ft: fields_contained "(field_access d)" "(field_update d)" "set (toplevel_field_descs t)"
    by (rule contained_t)

  from d'_in obtain d'' where
    d''_in: "d'' \<in> set (toplevel_field_descs t)" and
    d': "d' = update_desc acc upd d''"
    by auto
  from ft.update_contained [OF d''_in ]
  obtain bs' where cont: "\<forall>s'. field_access d (acc s') = field_access d (acc s) \<longrightarrow>
                              field_update d'' bs (acc s') = field_update d bs' (acc s')"
    by fastforce

  from cont
  show "\<exists>bs'.  \<forall>s'. field_access (update_desc acc upd d) s' =
                    field_access (update_desc acc upd d) s \<longrightarrow> field_update d' bs s' =
             field_update (update_desc acc upd d) bs' s'"
    by (auto simp add: update_desc_def d')
qed



lemma contained_field_descs_update_desc:
  "contained_field_descs t \<Longrightarrow>
     contained_field_descs (map_td (\<lambda>_ _. update_desc acc upd) (update_desc acc upd) t)"
  "contained_field_descs_struct st \<Longrightarrow>
     contained_field_descs_struct (map_td_struct (\<lambda>_ _. update_desc acc upd) (update_desc acc upd) st)"
  "contained_field_descs_list fs \<Longrightarrow>
     contained_field_descs_list (map_td_list (\<lambda>_ _. update_desc acc upd) (update_desc acc upd) fs)"
  "contained_field_descs_tuple f \<Longrightarrow>
     contained_field_descs_tuple (map_td_tuple (\<lambda>_ _. update_desc acc upd) (update_desc acc upd) f)"
proof (induct t and st and fs and f)
  case (TypDesc st n)
  then show ?case by simp
next
  case (TypScalar n sz d)
  then show ?case by simp
next
  case (TypAggregate fs)
  then show ?case by simp
next
  case Nil_typ_desc
  then show ?case by simp
next
  case (Cons_typ_desc f fs)
  then show ?case by simp
next
  case (DTuple_typ_desc ft fn d)
  note \<open>contained_field_descs_tuple (DTuple ft fn d)\<close>
  then obtain
    contained_ft: "contained_field_descs ft" and
    fields_contained_ft: "fields_contained (field_access d) (field_update d) (set (toplevel_field_descs ft))"
    by simp
  from contained_ft DTuple_typ_desc(1)
  have contained_map: "contained_field_descs
     (map_td (\<lambda>_ _. update_desc acc upd) (update_desc acc upd) ft)"
    by simp

  from fields_contained_update_desc [OF fields_contained_ft]
  have "fields_contained (field_access (update_desc acc upd d))
     (field_update (update_desc acc upd d))
     (update_desc acc upd ` set (toplevel_field_descs ft))" .

  then have "fields_contained (field_access (update_desc acc upd d))
          (field_update (update_desc acc upd d))
          (set (toplevel_field_descs (map_td (\<lambda>_ _. update_desc acc upd) (update_desc acc upd) ft)))"
    by (simp add: toplevel_field_descs_map)
  with DTuple_typ_desc show ?case by simp
qed

theorem contained_field_descs_adjust_ti:
  fixes t::"'a xtyp_info"
  assumes contained_t: "contained_field_descs t"
  shows "contained_field_descs (adjust_ti t acc upd)"
  using contained_field_descs_update_desc(1) [OF contained_t]
  by (simp add: adjust_ti_def)

theorem contained_field_descs_extend_ti:
  assumes contained_t: "contained_field_descs t"
  assumes contained_ft: "contained_field_descs ft"
  assumes fields_contained_ft: "fields_contained (field_access d) (field_update d) (set (toplevel_field_descs ft))"
  shows "contained_field_descs (extend_ti t ft algn n d)"
  using contained_t contained_ft fields_contained_ft
  apply (cases t)
  subgoal for x1 x2 x3
    apply  simp
    apply (cases x2)
     apply simp
    apply (simp add: contained_field_descs_list_all)
    done
  done

theorem contained_field_descs_ti_pad_combine:
  fixes t::"'a xtyp_info"
  assumes cont_t: "contained_field_descs t"
  shows "contained_field_descs (ti_pad_combine n t)"
proof -
  define d::"'a field_desc" where
   "d \<equiv> \<lparr>field_access = \<lambda>v bs. if n \<le> length bs then take n bs else replicate n 0,
         field_update = \<lambda>bs. id, field_sz = n\<rparr>"
  define ft::"'a xtyp_info" where "ft \<equiv> TypDesc 0 (TypScalar n 0 d) ''!pad_typ''"
  define fn where "fn \<equiv> (foldl (@) ''!pad_'' (field_names_list t))"
  have "contained_field_descs (extend_ti t ft 0 fn d )"
    by (rule contained_field_descs_extend_ti [OF cont_t]) (auto simp add: ft_def d_def fields_contained_def)

  then show ?thesis
    by (simp add: ti_pad_combine_def Let_def d_def ft_def fn_def padding_desc_def)
qed

lemma contained_field_descs_simp[simp]:
 "contained_field_descs (map_align f t) = contained_field_descs t"
  by (cases t) (simp)

theorem contained_field_descs_final_pad:
  fixes t::"'a xtyp_info"
  assumes cont_t: "contained_field_descs t"
  shows "contained_field_descs (final_pad algn t)"
  using cont_t
  by (simp add: final_pad_def contained_field_descs_ti_pad_combine Let_def)

lemma (in xmem_type) fields_contained_update_desc_mem_type:
  fixes acc:: "'b \<Rightarrow> 'a"
  fixes D:: "'a field_desc set"
  shows "fields_contained (xto_bytes \<circ> acc) (upd \<circ> xfrom_bytes) (update_desc acc upd ` D)"
proof (rule fields_contained.intro)
  fix d s s'
  assume d_in: "d \<in> update_desc acc upd ` D"
  assume to_btyes_eq: "(xto_bytes \<circ> acc) s = (xto_bytes \<circ> acc) s'"

  hence "acc s = acc s'"
    by (auto intro: xto_bytes_inj)

  with d_in
  show "field_access d s = field_access d s'"
    by (auto simp add: update_desc_def)
next
  fix d bs s
  assume d_in: "d \<in> update_desc acc upd ` D"

  from d_in obtain d' where d'_in: "d' \<in> D" and d: "d = update_desc acc upd d'"
    by auto

  define x where "x \<equiv> \<lambda>s. field_update d' bs (acc s)"


  from xfrom_bytes_xto_bytes_inv obtain bs' where
   cont: "\<forall>s'. acc s' = acc s \<longrightarrow> xfrom_bytes (xto_bytes (x s') bs') = (x s')"
    by auto


  from  d'_in cont
  show "\<exists>bs'.  \<forall>s'. (xto_bytes \<circ> acc) s' = (xto_bytes \<circ> acc) s \<longrightarrow>
    field_update d bs s' = (upd \<circ> xfrom_bytes) bs' s'"
    by (metis (no_types, lifting) comp_apply d field_desc.simps(2) update_desc_def x_def xto_bytes_inj)
qed





locale wf_field =
  fixes acc::"'s \<Rightarrow> 'a"
  fixes upd::"'a \<Rightarrow> 's \<Rightarrow> 's"
  assumes double_update_upd: "\<And>v w s. upd v (upd w s) = upd v s"
  assumes acc_upd: "\<And>v s. acc (upd v s) = v"
  assumes upd_acc: "\<And>s. upd (acc s) s = s"

locale wf_cfield = wf_field +
  constrains acc::"'s \<Rightarrow> 'a::c_type"
locale wf_xfield = wf_cfield +
  constrains acc::"'s \<Rightarrow> 'a::xmem_type"

lemma (in wf_field) wf_field_descs_adjust_ti:
  assumes wf_t: "wf_field_descs (set (field_descs t))"
  shows "wf_field_descs (set (field_descs (adjust_ti t acc upd)))"
proof -
  have "wf_field_descs (update_desc acc upd ` set (field_descs t))"
  proof (rule wf_field_descs.intro)
    fix d
    assume "d \<in> update_desc acc upd ` set (field_descs t)"
    then obtain d' where d'_in: "d' \<in> set (field_descs t)" and d: "d = update_desc acc upd d'"
      by auto
    from wf_t d'_in have "wf_field_desc d'"
      by (rule wf_field_descs.wf_desc)
    then interpret wf_d': wf_field_desc "d'" .
    from wf_d'.wf_field_desc_update_desc [of upd acc, OF double_update_upd acc_upd upd_acc]
    have "wf_field_desc (update_desc acc upd d')" .
    then
    show "wf_field_desc d"
      by (simp add: d)
  qed
  then show ?thesis
    by (simp add: adjust_ti_def field_descs_map)
qed



lemma field_descs_list_append [simp]: "field_descs_list (fs @ fs') = field_descs_list fs @ field_descs_list fs'"
  by (induct fs arbitrary: fs') auto

lemma wf_field_descs_extend_ti:
  assumes wf_t: "wf_field_descs (set (field_descs t))"
  assumes wf_ft: "wf_field_descs (set (field_descs ft))"
  assumes wf_d: "wf_field_desc d"
  shows "wf_field_descs (set (field_descs (extend_ti t ft algn fn d)))"
proof (cases t)
  case (TypDesc algn st n)
  note desc = this
  show ?thesis
  proof (cases st)
    case (TypScalar sz align d)
    with wf_ft wf_d show ?thesis
      by (simp add: desc)
  next
    case (TypAggregate fs)
    note aggr = this
    show ?thesis
    proof (cases fs)
      case Nil
      then show ?thesis
        using wf_ft wf_d by (simp add: desc aggr)
    next
      case (Cons f fs')
      note cons = this
      obtain ft' fn fd where f: "f = DTuple ft' fn fd" by (cases f)
      show ?thesis
        using wf_ft wf_t wf_d by (auto simp add: desc aggr cons f wf_field_descs_def)
    qed
  qed
qed


lemma padding_pad: "complement_padding (\<lambda>v bs. if n \<le> length bs then take n bs else replicate n 0) (\<lambda>bs. id) n"
  apply (unfold_locales)
  by (auto simp add: padding_base.is_padding_byte_def padding_base.is_value_byte_def) 
     (metis (mono_tags, opaque_lifting) Ex_list_of_length len8 len_not_eq_0
      less_irrefl neq0_conv nth_list_update_eq word_power_less_1)




lemma wf_field_desc_pad:
"wf_field_desc
     \<lparr>field_access = \<lambda>v bs. if n \<le> length bs then take n bs else replicate n 0,
      field_update = \<lambda>bs. id, field_sz = n\<rparr>"
  apply (intro_locales)
   apply simp
  apply (rule padding_pad)
  apply (unfold_locales)
       apply auto
  done

lemma wf_field_descs_ti_pad_combine: "wf_field_descs (set (field_descs t)) \<Longrightarrow>
    wf_field_descs (set (field_descs (ti_pad_combine n t)))"
  apply (simp add: ti_pad_combine_def Let_def)
  apply (rule wf_field_descs_extend_ti)
    apply (auto simp add: wf_field_desc_pad padding_desc_def)
  done

lemma set_field_descs_map_align[simp]: "set (field_descs (map_align f t)) = set (field_descs t)"
  by (cases t) simp

lemma wf_field_descs_final_pad: "wf_field_descs (set (field_descs t)) \<Longrightarrow>
  wf_field_descs (set (field_descs (final_pad algn t)))"
  apply (clarsimp simp add: final_pad_def Let_def)
  apply (rule wf_field_descs_ti_pad_combine)
  apply simp
  done


lemma (in wf_xfield) padding_lift:
shows "complement_padding (xto_bytes \<circ> acc) (upd \<circ> xfrom_bytes) (size_of TYPE('a))"
proof -
(* FIXME: remove
  have "wf_field_desc (component_desc (typ_info_t TYPE('a)))"
    using xmem_type_class.wf_field_desc_component_desc by blast
  then interpret wf_field_desc "(component_desc (typ_info_t TYPE('a)))" .
*)
  thm xmem_type_wf_field_desc.access_update
  thm xmem_type_wf_field_desc.is_padding_byte_acc_upd_compose
  show ?thesis
  proof
    fix i
    assume i_bound: "i < size_of TYPE('a)"

    {
      fix bs v
      have "upd (field_update (component_desc (typ_info_t TYPE('a))) bs (acc v)) v =
         upd (field_update (component_desc (typ_info_t TYPE('a))) bs undefined) v"
        by (simp add: entire_update [where bs = bs and v = "acc v" and w = undefined])
    } note tweak_eq = this

    have sz_eq: "field_sz (component_desc (typ_info_t TYPE('a))) = size_of TYPE('a)"
      by (simp add: size_of_def size_td_field_sz(1) wf_component_descs)

    from  xmem_type_wf_field_desc.is_padding_byte_acc_upd_compose [where acc=acc and upd=upd, OF acc_upd, of i]
       xmem_type_wf_field_desc.is_value_byte_acc_upd_compose [where acc=acc and upd=upd, OF acc_upd, of i]
    show "padding_base.is_padding_byte (xto_bytes \<circ> acc) (upd \<circ> xfrom_bytes)
          (size_of TYPE('a)) i \<noteq>
         padding_base.is_value_byte (xto_bytes \<circ> acc) (upd \<circ> xfrom_bytes)
          (size_of TYPE('a)) i"
      apply (simp add: xto_bytes_def xfrom_bytes_def [abs_def] comp_def tweak_eq sz_eq)
      using  xmem_type_wf_field_desc.complement i_bound sz_eq
        by metis
  qed
qed



(* move up *)
lemma (in wf_xfield) wf_field_desc_lift:
  shows "wf_field_desc \<lparr>field_access = xto_bytes \<circ> acc,
         field_update = upd \<circ> xfrom_bytes,
         field_sz = size_of (TYPE('a))\<rparr>" (is "wf_field_desc ?lift")
  apply (intro_locales, simp, rule padding_lift, unfold_locales)
proof -
  fix bs bs' s
  show "field_update ?lift bs (field_update ?lift bs' s) = field_update ?lift bs s"
    by (simp add: double_update_upd)
next
  fix bs s bs' s'
  show "field_access ?lift (field_update ?lift bs s) bs' = field_access ?lift (field_update ?lift bs s') bs'"
    by (simp add: acc_upd)
next
  fix s bs
  show "field_update ?lift (field_access ?lift s bs) s = s"
    by (simp add: upd_acc xfrom_bytes_xto_bytes_inv)
next
  fix s bs
  show "field_access ?lift s (take (field_sz ?lift) bs) = field_access ?lift s bs"
    by (simp add: xto_bytes_size size_of_def)
next
  fix s bs
  show "length (field_access ?lift s bs) = field_sz ?lift"
    by (simp add: xto_bytes_result_size size_of_def)
next
  fix bs
  show "field_update ?lift (take (field_sz ?lift) bs) = field_update ?lift bs"
    by (simp add: xfrom_bytes_size size_of_def)
qed



lemma (in wf_xfield) wf_field_descs_ti_typ_combine:
  assumes wf_ft: "wf_field_descs (set (field_descs ft))"
  shows "wf_field_descs (set (field_descs (ti_typ_combine (TYPE('a)) acc upd algn fn ft)))"
  apply (simp add: ti_typ_combine_def)
  apply (rule wf_field_descs_extend_ti)
    apply (rule wf_ft)
   apply (rule wf_field_descs_adjust_ti)
   apply (rule wf_field_descs)
  apply (rule wf_field_desc_lift)
  done


lemma (in wf_xfield) wf_field_descs_ti_typ_pad_combine:
  assumes wf_ft: "wf_field_descs (set (field_descs ft))"
  shows "wf_field_descs (set (field_descs (ti_typ_pad_combine (TYPE('a)) acc upd algn fn ft)))"
proof (cases "0 < padup (max (2 ^ algn) (align_of TYPE('a))) (size_td ft)")
  case True
  then show ?thesis
    apply (simp add: ti_typ_pad_combine_def Let_def)
    apply (rule wf_field_descs_ti_typ_combine)
    apply (rule wf_field_descs_ti_pad_combine)
    apply (rule wf_ft)
    done
next
  case False
  then show ?thesis
    apply (simp add: ti_typ_pad_combine_def Let_def)
    apply (rule wf_field_descs_ti_typ_combine)
    apply (rule wf_ft)
    done
qed

lemma wf_component_descs_empty_typ_info [simp]: "wf_component_descs (empty_typ_info algn n)"
  by (simp add: empty_typ_info_def)

lemma wf_component_descs_list_append [simp]:
  "wf_component_descs_list (fs @ fs') = (wf_component_descs_list fs \<and> wf_component_descs_list fs')"
  by (induct fs arbitrary: fs') auto

lemma wf_component_descs_extend_ti:
  assumes wf_t: "wf_component_descs t"
  assumes wf_ft: "wf_component_descs ft"
  assumes d: "d = (component_desc ft)"
  shows "wf_component_descs (extend_ti t ft algn fn d)"
  apply (cases t)
  subgoal for x1 st n
    apply (cases st)
     apply (simp add: wf_ft d)
    subgoal for fs
      apply (cases fs)
       apply (simp add: wf_ft d)
      subgoal for f fs'
        apply (cases f)
        apply (insert wf_t)
        apply (simp add: d wf_ft)
        done
      done
    done
  done

lemma wf_component_descs_ti_pad_combine:
  assumes wf_t: "wf_component_descs t"
  shows "wf_component_descs (ti_pad_combine n t)"
  apply (simp add: ti_pad_combine_def Let_def padding_desc_def)
  apply (rule wf_component_descs_extend_ti)
    apply (rule wf_t)
   apply simp
  apply simp
  done


lemma wf_component_descs_map_align [simp]: "wf_component_descs (map_align f t) = wf_component_descs t"
  by (cases t) simp

lemma wf_component_descs_final_pad:
  assumes wf_t: "wf_component_descs t"
  shows "wf_component_descs (final_pad algn t)"
  by (clarsimp simp add: final_pad_def Let_def wf_t wf_component_descs_ti_pad_combine)

lemma field_sz_update_desc [simp]: "field_sz (update_desc acc upd d) = field_sz d"
  by (simp add: update_desc_def)



lemma component_sz_struct_update_desc_commutes:
"(component_sz_struct (TypAggregate fs)) =
      component_sz_struct (map_td_struct (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) (TypAggregate fs))"
proof (induct fs)
  case Nil
  then show ?case by simp
next
  case (Cons f fs')
  obtain ft fn d where f: "f = DTuple ft fn d" by (cases f) simp
  have map_eq: "map (field_sz \<circ> dt_trd) (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) fs') =
        map (field_sz \<circ> dt_trd) fs'"
    apply (induct fs')
     apply simp
    subgoal for f' fs''
    apply (cases f')
    apply clarsimp
      done
    done
  show ?case by (simp add: f map_eq)
qed

lemma component_access_struct_update_desc_commutes':
"component_access_struct (TypAggregate fs) (acc v) bs =
      component_access_struct (map_td_struct (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) (TypAggregate fs)) v bs"
proof (induct fs arbitrary: bs)
  case Nil
  then show ?case by simp
next
  case (Cons f fs')
  obtain ft fn d where f: "f = DTuple ft fn d" by (cases f) simp

  have d_commutes: "field_access (update_desc acc upd d) v bs = field_access d (acc v) bs"
    by (simp add: update_desc_def)

  note hyp = Cons.hyps [where bs="(drop (length (field_access d (acc v) bs)) bs)" ]
  then
  show ?case
    by (simp add: f d_commutes hyp)
qed


lemma component_access_struct_update_desc_commutes:
"(component_access_struct (TypAggregate fs)) \<circ> acc =
      component_access_struct (map_td_struct (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) (TypAggregate fs))"
  apply -
  apply (rule ext)
  apply (rule ext)
  apply (simp only: comp_def)
  apply (rule component_access_struct_update_desc_commutes')
  done

lemma (in wf_field) lemma_component_update_struct_update_desc_commutes:
  shows "upd (component_update_struct (TypAggregate fs) bs (acc v)) v =
          component_update_struct (map_td_struct (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) (TypAggregate fs)) bs v"
proof (induct fs arbitrary: v bs)
  case Nil
  then show ?case by (simp add: upd_acc)
next
  case (Cons f fs')
  obtain ft fn d where f: "f = DTuple ft fn d" by (cases f) simp

  have acc_update_desc: "acc (field_update (update_desc acc upd d) bs v) = field_update d bs (acc v)"
    by (simp add: update_desc_def acc_upd)

  have upd_eq: "upd (fst (apply_field_updates (map dt_trd fs') (drop (field_sz d) bs)
                 (field_update d bs (acc v)))) (field_update (update_desc acc upd d) bs v) =
               upd (fst (apply_field_updates (map dt_trd fs') (drop (field_sz d) bs)
               (field_update d bs (acc v)))) v"
    by (simp add: update_desc_def double_update_upd)


  note hyp = Cons.hyps [where bs = "(drop (field_sz d) bs)" and v="field_update (update_desc acc upd d) bs v"]

  from hyp
  show ?case
    by (simp add: f acc_update_desc upd_eq)
qed

lemma (in wf_field) update_desc_component_desc_struct_commutes:
  shows "update_desc acc upd (component_desc_struct (TypAggregate fs)) =
          component_desc_struct (map_td_struct (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) (TypAggregate fs))"
  using  lemma_component_update_struct_update_desc_commutes
   component_access_struct_update_desc_commutes [where acc=acc and upd=upd and fs=fs]
   component_sz_struct_update_desc_commutes  [where acc=acc and upd=upd  and fs=fs]
  apply (simp only: update_desc_def)
  apply (fastforce simp add: component_desc_struct_def)
  done

lemma (in wf_field) update_desc_component_desc_commutes:
  shows "update_desc acc upd (component_desc t) =
         component_desc (map_td (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) t)"
  using update_desc_component_desc_struct_commutes
  apply (cases t)
  apply simp
  subgoal for x1 st n
    apply (cases st)
     apply simp
    apply simp
    done
  done

lemma (in wf_field) wf_component_descs_map_td_update_desc:
  shows
  "wf_component_descs t
   \<Longrightarrow> wf_component_descs (map_td (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) t)"
  "wf_component_descs_struct st
  \<Longrightarrow> wf_component_descs_struct (map_td_struct (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) st)"
  "wf_component_descs_list fs
  \<Longrightarrow> wf_component_descs_list (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) fs)"
  "wf_component_descs_tuple f
  \<Longrightarrow> wf_component_descs_tuple (map_td_tuple (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) f)"
     apply (induct t and st and fs and f)
       apply (auto simp add: update_desc_component_desc_commutes )
  done

lemma (in wf_field) wf_component_descs_adjust_ti:
  assumes wf_t: "wf_component_descs t"
  shows "wf_component_descs (adjust_ti t acc upd)"
using wf_component_descs_map_td_update_desc(1) [OF wf_t]
  by (simp add: adjust_ti_def)

lemma (in wf_xfield) update_desc_component_desc:
  shows
   "update_desc acc upd (component_desc (typ_info_t TYPE('a))) =
     \<lparr>field_access = xto_bytes \<circ> acc, field_update = upd \<circ> xfrom_bytes,
      field_sz = size_of TYPE('a)\<rparr>"
proof -
  have wf: "wf_component_descs (typ_info_t TYPE('a))" by (rule wf_component_descs)
  have eq: "\<And>bs v. field_update (component_desc (typ_info_t TYPE('a))) bs (acc v) =
                   field_update (component_desc (typ_info_t TYPE('a))) bs undefined"
    by (simp add: entire_update)
   show ?thesis
  using size_td_field_sz(1) [OF wf]
  apply (simp add: xto_bytes_def size_of_def update_desc_def)
  apply (rule ext)
  apply (rule ext)
  apply (simp add: xfrom_bytes_def eq)
  done
qed


lemma (in wf_xfield) wf_component_descs_ti_typ_combine:
  assumes wf_t: "wf_component_descs t"
  shows "wf_component_descs (ti_typ_combine ft acc upd algn fn t)"
proof -
  have wf_ft: "wf_component_descs (typ_info_t TYPE('a))" by (rule wf_component_descs)
  show ?thesis
  apply (simp add: ti_typ_combine_def Let_def)
  apply (rule wf_component_descs_extend_ti)
    apply (rule wf_t)
   apply (rule wf_component_descs_adjust_ti)
   apply (rule wf_ft)
  apply (simp add: adjust_ti_def Let_def update_desc_component_desc
      update_desc_component_desc_commutes[symmetric])
  done
qed

lemma (in wf_xfield) wf_component_descs_ti_typ_pad_combine:
  assumes wf_t: "wf_component_descs t"
  shows "wf_component_descs (ti_typ_pad_combine ft acc upd algn fn t)"
  apply (cases "0 < padup (max (2 ^ algn) (align_of TYPE('a))) (size_td t)")
   apply (simp add: ti_typ_pad_combine_def Let_def)
   apply (rule wf_component_descs_ti_typ_combine)
   apply (rule wf_component_descs_ti_pad_combine [OF wf_t])
  apply (simp add: ti_typ_pad_combine_def Let_def)
  apply (rule wf_component_descs_ti_typ_combine [OF wf_t])
  done


lemma component_descs_independent_empty_typ_info [simp]:
  "component_descs_independent  (empty_typ_info algn n)"
  by (simp add: empty_typ_info_def)


lemma component_descs_independent_list_appendI:
  assumes ind_xs_ys: "\<forall>x \<in> set (toplevel_field_descs_list xs).
       field_desc_independent (field_access x) (field_update x) (set (toplevel_field_descs_list ys))"
  assumes ind_xs: "component_descs_independent_list xs"
  assumes ind_ys: "component_descs_independent_list ys"
  shows "component_descs_independent_list (xs @ ys)"
  using ind_xs_ys ind_xs ind_ys
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain ft' fn' d' where x: "x = DTuple ft' fn' d'" by (cases x) simp

  from Cons.prems obtain

    find_d'_ys: "field_desc_independent (field_access d') (field_update d')
                   (set (toplevel_field_descs_list ys))" and
    find_xs_ys: "\<forall>x\<in>set (toplevel_field_descs_list xs).
                   field_desc_independent (field_access x) (field_update x) (set (toplevel_field_descs_list ys))" and
    find_d'_xs: "field_desc_independent (field_access d') (field_update d') (set (toplevel_field_descs_list xs))" and
    find_xs: "field_descs_independent (toplevel_field_descs_list xs)" and
    ind_ft': "component_descs_independent ft'" and
    ind_ys: "component_descs_independent_list ys" and
    ind_xs:"component_descs_independent_list xs"
    by (clarsimp simp add: x)


  from find_d'_xs find_d'_ys
  have find_d': "field_desc_independent (field_access d') (field_update d')
                 (set (toplevel_field_descs_list xs) \<union> set (toplevel_field_descs_list ys))"
    by (simp add: field_desc_independent_union_iff)

  from component_descs_list_field_descs_independent [OF ind_xs]
  have tl_xs: "field_descs_independent (toplevel_field_descs_list xs)".
  from component_descs_list_field_descs_independent [OF ind_ys]
  have tl_ys: "field_descs_independent (toplevel_field_descs_list ys)".

  from field_descs_independent_appendI1 [OF tl_xs tl_ys find_xs_ys]
  have tl_xs_ys: "field_descs_independent
                    (toplevel_field_descs_list xs @ toplevel_field_descs_list ys)" .

  from Cons.hyps [OF find_xs_ys ind_xs ind_ys]
  have ind_xs_ys: "component_descs_independent_list (xs @ ys)" .
  from find_d' tl_xs_ys ind_ft' ind_xs_ys
  show ?case
    by (simp add: x)
qed

lemma component_descs_independent_extend_ti:
  assumes ind_t: "component_descs_independent t"
  assumes ind_ft: "component_descs_independent ft"
  assumes ind_d_t: "field_desc_independent (field_access d) (field_update d) (set (toplevel_field_descs t))"
  shows "component_descs_independent (extend_ti t ft algn fn d)"
proof (cases t)
  case (TypDesc algn st nn)
  then show ?thesis
  proof (cases st)
    case (TypScalar sz align d)
    from ind_ft show ?thesis
      by (simp add: TypDesc TypScalar)
  next
    case (TypAggregate fs)
    then show ?thesis
    proof (cases fs)
      case Nil
      from ind_ft show ?thesis
        by (simp add: TypDesc TypAggregate Nil)
    next
      case (Cons f fs')
      obtain ft' fn' d' where f: "f = DTuple ft' fn' d'" by (cases f) simp
      from ind_t obtain
        field_ind_d'_fs': "field_desc_independent (field_access d') (field_update d')
                            (set (toplevel_field_descs_list fs'))" and
        field_ind_fs': "field_descs_independent (toplevel_field_descs_list fs')" and
        comp_ind_ft': "component_descs_independent ft'" and
        comp_ind_fs': "component_descs_independent_list fs'"
        by (simp add: TypDesc TypAggregate Cons f)

      from ind_d_t obtain ind_d_d': "field_desc_independent (field_access d) (field_update d) {d'}" and
       ind_d_fs': "field_desc_independent (field_access d) (field_update d) (set (toplevel_field_descs_list fs'))"
        apply  (simp add: TypDesc TypAggregate Cons f)
        supply field_desc_independent_insert_iff[iff]
        by fastforce


      from field_desc_independent_symmetric [of "{d}" "{d'}"] ind_d_d'
      have field_ind_d'_d: "field_desc_independent (field_access d') (field_update d') {d}"
        by auto

      from field_ind_d'_fs' field_ind_d'_d
      have field_ind_d'_d_fs': "field_desc_independent (field_access d') (field_update d')
                                 (insert d (set (toplevel_field_descs_list fs')))"
        apply (subst  insert_is_Un )
        apply (simp only: field_desc_independent_union_iff)
        done

      have ind_d: "field_descs_independent [d]" by simp
      from field_desc_independent_symmetric [of "set [d]" "set (toplevel_field_descs_list fs')"] ind_d_fs'
      have ind_fs'_d:  "\<forall>x\<in>set (toplevel_field_descs_list fs').
              field_desc_independent (field_access x) (field_update x) (set [d])" by simp
      from field_descs_independent_appendI1 [OF field_ind_fs' ind_d ind_fs'_d]
      have field_ind_fs'_d:"field_descs_independent (toplevel_field_descs_list fs' @ [d])" .

      from ind_fs'_d ind_ft
      have comp_ind_fs'_d: "component_descs_independent_list (fs' @ [DTuple ft fn d])"
        apply -
        apply (rule component_descs_independent_list_appendI [OF _ comp_ind_fs' ] )
         apply simp
        apply simp
        done
      from field_ind_d'_d_fs' field_ind_fs'_d comp_ind_ft' comp_ind_fs'_d
      show ?thesis
          by (simp add: TypDesc TypAggregate Cons f)
      qed
  qed
qed



(*
  "component_descs_independent_struct st
   \<Longrightarrow> component_descs_independent_struct  (extend_ti_struct st ft fn d)"
  "component_descs_independent_list fs
   \<Longrightarrow> component_descs_independent_list  (extend_ti_list fs ft fn d)"
*)
lemma fu_commutes_id1 [simp]: "fu_commutes (\<lambda>bs. id) upd"
  by (auto simp add: fu_commutes_def)

lemma fu_commutes_id2 [simp]: "fu_commutes upd (\<lambda>bs. id)"
  by (auto simp add: fu_commutes_def)

lemma field_desc_independent_pad: "field_desc_independent (\<lambda>v bs. if n \<le> length bs then take n bs else replicate n 0) (\<lambda>bs. id) D"
  by (rule field_desc_independent.intro) auto

lemma component_descs_independent_ti_pad_combine:
  assumes ind_t: "component_descs_independent t"
  shows "component_descs_independent (ti_pad_combine n t)"
  apply (simp add: ti_pad_combine_def Let_def padding_desc_def)
  apply (rule component_descs_independent_extend_ti [OF ind_t])
   apply simp
  apply (simp add: field_desc_independent_pad)
  done


lemma (in wf_field) field_desc_independent_update_desc:
  assumes ind: "field_desc_independent (field_access d) (field_update d) D"
  shows "field_desc_independent (field_access (update_desc acc upd d)) (field_update (update_desc acc upd d))
          (update_desc acc upd ` D)" (is "field_desc_independent ?acc ?upd ?U")
proof -
  from ind
  interpret ind: field_desc_independent "field_access d" "field_update d" "D" .
  show ?thesis
  proof
    fix ud
    assume "ud \<in> ?U"
    show "fu_commutes ?upd (field_update ud)"
      by (smt \<open>ud \<in> update_desc acc upd ` D\<close> acc_upd double_update_upd field_desc.select_convs(2)
          field_desc_independent.fu_commutes fu_commutes_def imageE ind.field_desc_independent_axioms update_desc_def)
  next
    fix ud bs v bs'
    assume "ud \<in> ?U"
    show "?acc (field_update ud bs v) bs' = ?acc v bs'"
      by (smt \<open>ud \<in> update_desc acc upd ` D\<close> acc_upd field_desc.select_convs(1) field_desc.select_convs(2)
          field_desc_independent.acc_upd_old imageE ind.field_desc_independent_axioms o_apply update_desc_def)
  next
    fix ud bs' v bs
    assume "ud \<in> ?U"
    show "field_access ud (?upd bs' v) bs = field_access ud v bs"
      by (smt \<open>ud \<in> update_desc acc upd ` D\<close> acc_upd field_desc.select_convs(1) field_desc.select_convs(2)
          field_desc_independent.acc_upd_new imageE ind.field_desc_independent_axioms o_apply update_desc_def)
  qed
qed



lemma (in wf_field) field_descs_independent_update_desc:
  "field_descs_independent (toplevel_field_descs t)
  \<Longrightarrow> field_descs_independent (toplevel_field_descs
        (map_td (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) t))"
  "field_descs_independent (toplevel_field_descs_struct st)
  \<Longrightarrow> field_descs_independent (toplevel_field_descs_struct
        (map_td_struct (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) st))"
  "field_descs_independent (toplevel_field_descs_list fs)
  \<Longrightarrow> field_descs_independent (toplevel_field_descs_list
        (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) fs))"
  "field_descs_independent (toplevel_field_descs_tuple f)
  \<Longrightarrow> field_descs_independent (toplevel_field_descs_tuple
        (map_td_tuple (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) f))"
proof (induct t and st and fs and f)
  case (TypDesc st n)
  then show ?case by simp
next
  case (TypScalar sz align d)
  then show ?case by simp
next
  case (TypAggregate fs)
  then show ?case by simp
next
  case Nil_typ_desc
  then show ?case by simp
next
  case (Cons_typ_desc f fs)

  obtain ft' fn' d' where f: "f = DTuple ft' fn' d'" by (cases f) simp

  from Cons_typ_desc.prems
  have ind_f_fs: "field_descs_independent
     (toplevel_field_descs_tuple f @ toplevel_field_descs_list fs)" by simp

  from field_descs_independent_append_first [OF ind_f_fs]
  have ind_f: "field_descs_independent (toplevel_field_descs_tuple f)" .

  from field_descs_independent_append_second [OF ind_f_fs]
  have ind_fs: "field_descs_independent (toplevel_field_descs_list fs)" .


  from Cons_typ_desc.hyps(1) [OF ind_f]
  have ind_upd_f: "field_descs_independent
                    (toplevel_field_descs_tuple
                      (map_td_tuple (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) f))".

  from Cons_typ_desc.hyps(2) [OF ind_fs]
  have ind_upd_fs: "field_descs_independent
                     (toplevel_field_descs_list
                       (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) fs))" .


  from field_descs_independent_append_first_ind [OF ind_f_fs]
  have "field_desc_independent (field_access d') (field_update d') (set (toplevel_field_descs_list fs))"
    by (auto simp add: f)
  from field_desc_independent_update_desc [OF this]
  have "field_desc_independent (field_access (update_desc acc upd d')) (field_update (update_desc acc upd d'))
           (update_desc acc upd ` set (toplevel_field_descs_list fs))" .
  then
  have upd_d'_fs: "field_desc_independent (field_access (update_desc acc upd d')) (field_update (update_desc acc upd d'))
         (set (toplevel_field_descs_list
                 (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) fs)))"
    by (simp add: toplevel_field_descs_map)
  from ind_upd_fs upd_d'_fs
  have ind_upd_f_fs: "field_descs_independent
     (toplevel_field_descs_tuple
       (map_td_tuple (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) f) @
      toplevel_field_descs_list
       (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) fs))"
    by (simp add: f)
  from Cons_typ_desc ind_upd_f_fs
  show ?case by simp
next
  case (DTuple_typ_desc ft fn d)
  then show ?case by simp
qed




lemma (in wf_field) component_descs_independent_update_desc:
  "component_descs_independent t
  \<Longrightarrow> component_descs_independent
       (map_td (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) t)"
  "component_descs_independent_struct st
  \<Longrightarrow> component_descs_independent_struct
       (map_td_struct (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) st)"
  "component_descs_independent_list fs
  \<Longrightarrow> component_descs_independent_list
       (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) fs)"
  "component_descs_independent_tuple f
  \<Longrightarrow> component_descs_independent_tuple
       (map_td_tuple (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) f)"
proof (induct t and st and fs and f)
  case (TypDesc st n)
then show ?case by simp
next
  case (TypScalar sz align d)
  then show ?case by simp
next
case (TypAggregate fs)
then show ?case by simp
next
  case Nil_typ_desc
  then show ?case by simp
next
  case (Cons_typ_desc f fs)

  obtain ft' fn' d' where f: "f = DTuple ft' fn' d'" by (cases f) simp

  from Cons_typ_desc.prems obtain
    find_f_fs: "field_descs_independent
                (toplevel_field_descs_tuple f @ toplevel_field_descs_list fs)" and
    ind_f: "component_descs_independent_tuple f" and
    ind_fs: "component_descs_independent_list fs"
    by simp


  from field_descs_independent_append_first [OF find_f_fs]
  have fi_f: "field_descs_independent (toplevel_field_descs_tuple f)" .

  from Cons_typ_desc.hyps(1) [OF ind_f]
  have ind_upd_f: "component_descs_independent_tuple
          (map_td_tuple (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) f)" .
  from field_descs_independent_update_desc(4) [OF fi_f]
  have "field_descs_independent (toplevel_field_descs_tuple
         (map_td_tuple (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) f))" .
  with ind_upd_f
  have ind_upd_f': "component_descs_independent_list
          (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) [f])"  by simp


  from Cons_typ_desc.hyps(2) [OF ind_fs]
  have ind_upd_fs: "component_descs_independent_list
          (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) fs)" .
  from component_descs_list_field_descs_independent [OF this]
  have find_upd_fs: "field_descs_independent (toplevel_field_descs_list
          (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) fs))" .
  from field_descs_independent_append_first_ind [OF find_f_fs]
  have find_fs: "field_desc_independent (field_access d') (field_update d') (set (toplevel_field_descs_list fs))"
    by (auto simp add: f)
  from field_desc_independent_update_desc [OF this]
  have "field_desc_independent (field_access (update_desc acc upd d')) (field_update (update_desc acc upd d'))
           (update_desc acc upd ` set (toplevel_field_descs_list fs))" .
  then
  have upd_d'_fs: "field_desc_independent (field_access (update_desc acc upd d')) (field_update (update_desc acc upd d'))
         (set (toplevel_field_descs_list
                 (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) fs)))"
    by (simp add: toplevel_field_descs_map)

  from upd_d'_fs find_upd_fs
  have ind_f_fs: "field_descs_independent
      (toplevel_field_descs_tuple
         (map_td_tuple (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) f) @
       toplevel_field_descs_list
         (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) fs))"
    by (simp add: f)
  from Cons_typ_desc ind_f_fs  show ?case
    by (simp)
next
  case (DTuple_typ_desc ft fn d)
  then show ?case by simp
qed


lemma (in wf_field) component_descs_independent_adjust_ti:
  assumes ind_t: "component_descs_independent t"
  shows "component_descs_independent (adjust_ti t acc upd)"
  apply (simp add: adjust_ti_def)
  apply (rule component_descs_independent_update_desc(1) [OF ind_t])
  done



theorem (in wf_xfield) component_descs_independent_ti_typ_combine:
  fixes
    ft::"'a::xmem_type itself" and
     t:: "'s xtyp_info"
   assumes ind_t: "component_descs_independent t"
   assumes ind_acc_upd: "field_desc_independent (xto_bytes \<circ> acc) (upd \<circ> xfrom_bytes)
                          (set (toplevel_field_descs t))"
  shows "component_descs_independent (ti_typ_combine ft acc upd algn fn t)"
  apply (simp add: ti_typ_combine_def)
  apply (rule component_descs_independent_extend_ti [OF ind_t])
   apply (rule component_descs_independent_adjust_ti [OF component_descs_independent])
  apply simp
  apply (rule ind_acc_upd)
  done


lemma (in wf_xfield) wf_field_desc_extend_ti:
   assumes ind_t: "field_desc_independent (xto_bytes \<circ> acc) (upd \<circ> xfrom_bytes) (set (toplevel_field_descs t))"
   assumes ind_d: "field_desc_independent (xto_bytes \<circ> acc) (upd \<circ> xfrom_bytes) {d}"
   shows
   "field_desc_independent (xto_bytes \<circ> acc) (upd \<circ> xfrom_bytes)
         (set (toplevel_field_descs (extend_ti t ft algn fn d)))"
proof (cases t)
  case (TypDesc algn' st nn)
  then show ?thesis
  proof (cases st)
    case (TypScalar sz align d)
    from ind_d show ?thesis
      by (simp add: TypDesc TypScalar)
  next
    case (TypAggregate fs)
    then show ?thesis
    proof (cases fs)
      case Nil
      from ind_d show ?thesis
        by (simp add: TypDesc TypAggregate Nil)
    next
      case (Cons f fs')
      obtain ft' fn' d' where f: "f = DTuple ft' fn' d'" by (cases f) simp
      from ind_d ind_t
      show ?thesis
        apply (simp add: TypDesc TypAggregate Cons f)
        by (meson field_desc_independent_insert_iff)
    qed
  qed
qed

lemma (in wf_xfield) field_desc_independent_ti_pad_combine:
   assumes ind_acc_upd: "field_desc_independent (xto_bytes \<circ> acc) (upd \<circ> xfrom_bytes)
                          (set (toplevel_field_descs t))"
   shows "field_desc_independent (xto_bytes \<circ> acc) (upd \<circ> xfrom_bytes)
           (set (toplevel_field_descs (ti_pad_combine n t)))"
  apply (simp add: ti_pad_combine_def Let_def padding_desc_def)
  apply (rule wf_field_desc_extend_ti [OF ind_acc_upd])
  by (auto simp add: field_desc_independent_def)

theorem (in wf_xfield) component_desc_independent_ti_typ_pad_combine:
  fixes
    ft::"'a::xmem_type itself" and
     t:: "'s xtyp_info"
   assumes ind_t: "component_descs_independent t"
   assumes ind_acc_upd: "field_desc_independent (xto_bytes \<circ> acc) (upd \<circ> xfrom_bytes)
                          (set (toplevel_field_descs t))"
   shows "component_descs_independent (ti_typ_pad_combine ft acc upd algn fn t)"

  apply (cases "0 < padup (max (2 ^ algn) (align_of TYPE('a))) (size_td t)")
   apply (simp add: ti_typ_pad_combine_def Let_def)
   apply (rule component_descs_independent_ti_typ_combine)
    apply (rule component_descs_independent_ti_pad_combine [OF ind_t])
   apply (rule field_desc_independent_ti_pad_combine [OF ind_acc_upd])
  apply (simp add: ti_typ_pad_combine_def Let_def)
  apply (rule component_descs_independent_ti_typ_combine [OF ind_t ind_acc_upd])
  done

lemma component_descs_independent_map_align[simp]:
"component_descs_independent (map_align f t) = component_descs_independent t"
  by (cases t) simp

lemma component_descs_independent_final_pad:
   assumes ind_t: "component_descs_independent t"
   shows "component_descs_independent (final_pad algn t)"
  apply (clarsimp simp add: final_pad_def Let_def ind_t)
  apply (rule  component_descs_independent_ti_pad_combine [OF ind_t])
  done


theorem (in xmem_contained_type) contained_field_descs_ti_typ_combine:
  fixes
    ft::"'a itself" and
     t:: "'b xtyp_info"
  assumes contained_t: "contained_field_descs t"
  shows "contained_field_descs (ti_typ_combine ft acc upd algn fn t)"
proof -
  from contained_field_descs_adjust_ti [OF contained_field_descs]
  have "contained_field_descs (adjust_ti (typ_info_t TYPE('a)) acc upd)" .
  moreover
  define d::"'b field_desc"
    where "d \<equiv> \<lparr>field_access = xto_bytes \<circ> acc, field_update = upd \<circ> xfrom_bytes,
                field_sz = size_of TYPE('a)\<rparr>"

  from fields_contained_update_desc_mem_type [of acc upd]
  have "fields_contained (field_access d) (field_update d)
           (set (toplevel_field_descs (adjust_ti (typ_info_t TYPE('a)) acc upd)))"
    by (simp add: toplevel_field_descs_adjust_ti d_def)
  ultimately
  show ?thesis
    using contained_t
    by (simp add: ti_typ_combine_def contained_field_descs_extend_ti d_def)
qed


theorem (in xmem_contained_type) contained_field_descs_ti_typ_pad_combine:
  fixes
    ft::"'a itself" and
     t:: "'b xtyp_info"
  assumes contained_t: "contained_field_descs t"
  shows "contained_field_descs (ti_typ_pad_combine ft acc upd algn fn t)"
  using contained_t contained_field_descs
  by (simp add: ti_typ_pad_combine_def Let_def contained_field_descs_ti_typ_combine contained_field_descs_ti_pad_combine)


locale ti_ind' =
  fixes X :: "'a leaf_desc set"
  fixes Y :: "'a leaf_desc set"
  assumes fu_commutes: "x \<in> X  \<Longrightarrow> y \<in> Y \<Longrightarrow> fu_commutes (field_update (lf_fd x)) (field_update (lf_fd y))"
  assumes fa_fu_ind_X: "x \<in> X  \<Longrightarrow> y \<in> Y \<Longrightarrow> fa_fu_ind (lf_fd x) (lf_fd y) (lf_sz y) (lf_sz x)"
  assumes fa_fu_ind_Y: "x \<in> X  \<Longrightarrow> y \<in> Y \<Longrightarrow> fa_fu_ind (lf_fd y) (lf_fd x) (lf_sz x) (lf_sz y)"

lemma ti_ind'_ti_ind: "ti_ind' X Y = ti_ind X Y"
  by (auto simp add: ti_ind_def ti_ind'_def)

lemma fields_contained_transitive:
  assumes d_in: "d \<in> D"
  assumes d_contains : "fields_contained (field_access d) (field_update d) X"
  assumes contained: "fields_contained acc upd D"
  shows "fields_contained acc upd X"
  using d_in d_contains contained unfolding fields_contained_def
  by metis


lemma fields_contained_singleton [simp]:
  "fields_contained (field_access d) (field_update d) {d}"
  by (auto simp add: fields_contained_def)

(* make inductive over other cases *)
lemma contained_field_descs_leaf:
  "contained_field_descs t \<Longrightarrow> ld \<in> lf_fd ` (lf_set t []) \<Longrightarrow>
     \<exists>d \<in> set (toplevel_field_descs t). fields_contained (field_access d) (field_update d) {ld}"
  "contained_field_descs_struct st \<Longrightarrow> ld \<in> lf_fd ` (lf_set_struct st []) \<Longrightarrow>
     \<exists>d \<in> set (toplevel_field_descs_struct st). fields_contained (field_access d) (field_update d) {ld}"
  "contained_field_descs_list fs \<Longrightarrow> ld \<in> lf_fd ` (lf_set_list fs []) \<Longrightarrow>
     \<exists>d \<in> set (toplevel_field_descs_list fs). fields_contained (field_access d) (field_update d) {ld}"
  "contained_field_descs_tuple f \<Longrightarrow> ld \<in> lf_fd ` (lf_set_tuple f []) \<Longrightarrow>
     \<exists>d \<in> set (toplevel_field_descs_tuple f). fields_contained (field_access d) (field_update d) {ld}"
proof (induct t and st and fs and f)
  case (TypDesc st n)
  then show ?case by auto
next
  case (TypScalar n sz d)
  then show ?case by auto
next
  case (TypAggregate fs)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc f fs)
  then show ?case by auto
next
  case (DTuple_typ_desc ft fn d)
  then show ?case
    by (metis contained_field_descs_tuple.simps toplevel_field_descs_tuple.simps fields_contained_transitive
     insertI1 lf_fd_fn(1) lf_set_tuple.simps list.simps(15))
qed




lemma wf_field_desc_wf_lf:
"wf_field_desc d \<Longrightarrow> sz = field_sz d \<Longrightarrow>  wf_lf {\<lparr>lf_fd = d, lf_sz = sz, lf_fn = xs\<rparr>}"
  by (simp add: wf_field_desc_def
fd_cons_access_update_def fd_cons_desc_def fd_cons_double_update_def fd_cons_length_def
fd_cons_update_access_def padding_lense.access_result_size padding_lense.access_update
padding_lense.double_update padding_lense.update_access wf_lf_def)


lemma wf_lf_unionI: "wf_lf A \<Longrightarrow> wf_lf B \<Longrightarrow> ti_ind' A B \<Longrightarrow> wf_lf (A \<union> B)"
  by (auto simp add: wf_lf_def ti_ind'_def fu_commutes_def)


lemma fields_contained_subset:
  assumes cont_X: "fields_contained acc upd X"
  assumes subs: "Y \<subseteq> X"
  shows "fields_contained acc upd Y"
proof -
  from cont_X interpret X: fields_contained acc upd X .
  show ?thesis
  proof
    fix d s s'
    assume d: "d \<in> Y"
    assume acc: "acc s = acc s'"
    show "field_access d s = field_access d s'"
      using d subs acc X.access_contained by blast
  next
    fix d bs s
    assume d: "d \<in> Y"
    show "\<exists>bs'.  \<forall>s'. acc s' = acc s \<longrightarrow> field_update d bs s' = upd bs' s'"
      using d subs X.update_contained by blast
  qed
qed


lemma fields_contained_unionD1:
  assumes "fields_contained acc upd (X \<union> Y)"
  shows "fields_contained acc upd X"
  using assms
  by (auto intro: fields_contained_subset)


lemma fields_contained_unionD2:
  assumes "fields_contained acc upd (X \<union> Y)"
  shows "fields_contained acc upd Y"
  using assms
  by (auto intro: fields_contained_subset)

lemma fields_contained_unionI:
  assumes cont_X: "fields_contained acc upd X"
  assumes cont_Y: "fields_contained acc upd Y"
  shows "fields_contained acc upd (X \<union> Y)"
proof -
  from cont_X interpret X: fields_contained acc upd X .
  from cont_Y interpret Y: fields_contained acc upd Y .
  show ?thesis
  proof
    fix d s s'
    assume d: "d \<in> X \<union> Y"
    assume acc: "acc s = acc s'"
    show "field_access d s = field_access d s'"
      using d acc X.access_contained Y.access_contained by blast
  next
    fix d bs s
    assume d: "d \<in> X \<union> Y"
    show "\<exists>bs'.  \<forall>s'. acc s' = acc s \<longrightarrow> field_update d bs s' = upd bs' s'"
      using d X.update_contained Y.update_contained by blast
  qed
qed

(* fixme: move up *)
lemma fields_contained_insertI:
  assumes cont_x: "fields_contained acc upd {x}"
  assumes cont_Y: "fields_contained acc upd Y"
  shows "fields_contained acc upd (insert x Y)"
  using fields_contained_unionI [OF cont_x cont_Y]
  by simp



lemma fields_contained_toplevel_to_field_descs:
  "\<And>(acc::'a \<Rightarrow> byte list \<Rightarrow> byte list) upd.
   contained_field_descs t \<Longrightarrow> fields_contained acc upd (set (toplevel_field_descs t))
   \<Longrightarrow> fields_contained acc upd (set (field_descs t))"
  "\<And>(acc::'a \<Rightarrow> byte list \<Rightarrow> byte list) upd.
  contained_field_descs_struct st \<Longrightarrow> fields_contained acc upd (set (toplevel_field_descs_struct st))
   \<Longrightarrow> fields_contained acc upd (set (field_descs_struct st))"
  "\<And>(acc::'a \<Rightarrow> byte list \<Rightarrow> byte list) upd.
  contained_field_descs_list fs \<Longrightarrow> fields_contained acc upd (set (toplevel_field_descs_list fs))
   \<Longrightarrow> fields_contained acc upd (set (field_descs_list fs))"
  "\<And>(acc::'a \<Rightarrow> byte list \<Rightarrow> byte list) upd.
   contained_field_descs_tuple f \<Longrightarrow> fields_contained acc upd (set (toplevel_field_descs_tuple f))
   \<Longrightarrow> fields_contained acc upd (set (field_descs_tuple f))"
proof (induct t and st and fs and f)
case (TypDesc st n)
  then show ?case by simp
next
  case (TypScalar st align d)
  then show ?case by simp
next
  case (TypAggregate fs)
  then show ?case by simp
next
  case Nil_typ_desc
  then show ?case by simp
next
  case (Cons_typ_desc f fs)
  from Cons_typ_desc.prems obtain
     fcont_f_fs: "fields_contained acc upd
                  (set (toplevel_field_descs_tuple f) \<union> set (toplevel_field_descs_list fs))" and
     cont_f: "contained_field_descs_tuple f" and
     cont_fs: "contained_field_descs_list fs" by clarsimp

  note fcont_f = fields_contained_unionD1 [OF fcont_f_fs]
  note fcont_fs = fields_contained_unionD2 [OF fcont_f_fs]

  from Cons_typ_desc.hyps(1) [OF cont_f fcont_f] Cons_typ_desc.hyps(2) [OF cont_fs fcont_fs]
  have "fields_contained acc upd (set (field_descs_tuple f) \<union> set (field_descs_list fs))"
    by (rule fields_contained_unionI)

  then show ?case
    by clarsimp

next
  case (DTuple_typ_desc ft fn d)
  then show ?case
    by (fastforce intro: fields_contained_insertI fields_contained_transitive)
qed


lemma fu_commutes_intro:
  assumes "\<And>v bs bs'. f bs (g bs' v) = g bs' (f bs v)"
  shows "fu_commutes f g"
  using assms by (simp add: fu_commutes_def)


lemma (in wf_field_desc) access_same_update_id:
  assumes "field_access d (field_update d bs v) bs' = field_access d v bs'"
  shows "field_update d bs v = v"
  by (metis assms double_update update_access)


lemma (in wf_field_desc) access_same_update_id':
  assumes upd_inv: "field_update d bs v = v"
  assumes acc_same: "field_access d v bs = field_access d v' bs"
  shows "field_update d bs v' = v'"
  by (metis acc_same access_update double_update upd_inv update_access)

lemma (in wf_field_desc) update_access_unequal:
  assumes neq_upd: "field_update d bs v \<noteq> v"
  shows "field_access d v bs' \<noteq> field_access d (field_update d bs v) bs'"
  by (metis access_same_update_id neq_upd)

lemma (in wf_field_desc) access_eq_update_eq:
  assumes "\<And>bs'. field_access d (field_update d bs v) bs' = field_access d v bs'"
  shows "field_update d bs v = v"
  by (metis assms double_update update_access)





lemma field_desc_independent_contained_transitive:
  assumes cont: "fields_contained (field_access e) (field_update e) D"
  assumes ind:  "field_desc_independent (field_access d) (field_update d) {e}"
  shows "field_desc_independent (field_access d) (field_update d) D"
proof -
  from cont interpret cont_e: fields_contained "field_access e" "field_update e" D .
  from ind interpret ind_e: field_desc_independent "field_access d" "field_update d" "{e}" .
  show ?thesis
  proof
    fix f
    assume f_in: "f \<in> D"
    show "fu_commutes (field_update d) (field_update f)"
    proof (rule fu_commutes_intro)
      fix v bs bs'

      from ind_e.acc_upd_new [of e]
      have e_d_ind: "field_access e (field_update d bs v) = field_access e v"
        by (rule ext) auto

      from cont_e.update_contained [OF f_in, where s=v] e_d_ind
      obtain bs1 where f_e_v: "field_update f bs' v = field_update e bs1 v" and
                       f_e_upd_v: "field_update f bs' (field_update d bs v) = field_update e bs1 (field_update d bs v)"

        by blast
      have "field_update d bs (field_update f bs' v) = field_update d bs (field_update e bs1 v)"
        by (simp add: f_e_v)
      also
      from ind_e.fu_commutes [of e] have "\<dots> = field_update e bs1 (field_update d bs v)"
        by (auto simp add: fu_commutes_def)
      also have "\<dots> = field_update f bs' (field_update d bs v)" by (simp add: f_e_upd_v)
      finally
      show "field_update d bs (field_update f bs' v) =
            field_update f bs' (field_update d bs v)".
    qed
  next
    fix f bs v bs'
    assume f_in: "f \<in> D"
    show "field_access d (field_update f bs v) bs' = field_access d v bs'"
      by (metis cont_e.update_contained f_in ind_e.acc_upd_old insertI1)
  next
    fix f bs' v bs
    assume f_in: "f \<in> D"
    show "field_access f (field_update d bs' v) bs = field_access f v bs"
    proof -
     from ind_e.acc_upd_new [of e]
     have e_d_ind: "field_access e (field_update d bs' v) = field_access e v"
        by (rule ext) auto
     from cont_e.access_contained [OF f_in e_d_ind]
     show ?thesis by simp
   qed
 qed
qed


lemma field_desc_independent_contained_toplevel_to_field_descs:
  assumes cont_fs: "contained_field_descs_list fs"
  assumes ind_tl: "field_desc_independent (field_access d) (field_update d)
            (set (toplevel_field_descs_list fs))"
  shows "field_desc_independent (field_access d) (field_update d)
           (set (field_descs_list fs))"
  using cont_fs ind_tl
proof (induct fs)
  case Nil
  then show ?case by simp
next
  case (Cons f fs)
  obtain ft fn d' where f: "f = DTuple ft fn d'" by (cases f) simp

  from Cons.prems obtain
    ind_d_tl: "field_desc_independent (field_access d) (field_update d)
                (insert d' (set (toplevel_field_descs_list fs)))" and
    cont_ft: "contained_field_descs ft" and
    cont_d'_ft: "fields_contained (field_access d') (field_update d')
                   (set (toplevel_field_descs ft))" and
    cont_fs: "contained_field_descs_list fs"
    by (simp add: f)


  note ind_d_fs_tl = field_desc_independent_insertD2 [OF ind_d_tl]

  from Cons.hyps [OF cont_fs ind_d_fs_tl]
  have ind_d_fs: "field_desc_independent (field_access d) (field_update d)
                   (set (field_descs_list fs))".

  from fields_contained_toplevel_to_field_descs(1) [OF cont_ft cont_d'_ft]
  have fcont_d'_ft: "fields_contained (field_access d') (field_update d')
                      (set (field_descs ft))" .

  from field_desc_independent_insertD1 [OF ind_d_tl]
  have ind_d_d': "field_desc_independent (field_access d) (field_update d) {d'}" .

  from field_desc_independent_contained_transitive [OF fcont_d'_ft ind_d_d']
  have "field_desc_independent (field_access d) (field_update d) (set (field_descs ft))" .


  from field_desc_independent_unionI [OF this ind_d_fs] field_desc_independent_insertD1 [OF ind_d_tl]
  have "field_desc_independent (field_access d) (field_update d)
         (insert d' (set (field_descs ft) \<union> set (field_descs_list fs)))"
    by (blast intro: field_desc_independent_insertI)
  then show ?case
    by (clarsimp simp add: f)
qed

theorem component_descs_independent_contained_wf_lf:
  fixes t::"'a xtyp_info" and
   st::"'a xtyp_info_struct" and
   fs::"'a xtyp_info_tuple list" and
   f::"'a xtyp_info_tuple"
 shows
 "\<And>ps. \<lbrakk>wf_desc t; wf_component_descs t; wf_field_descs (set (field_descs t)); component_descs_independent t;
  contained_field_descs t \<rbrakk>
  \<Longrightarrow> wf_lf (lf_set t ps)"
 "\<And>ps. \<lbrakk>wf_desc_struct st; wf_component_descs_struct st; wf_field_descs (set (field_descs_struct st));
   component_descs_independent_struct st; contained_field_descs_struct st\<rbrakk>
  \<Longrightarrow> wf_lf (lf_set_struct st ps)"
 "\<And>ps. \<lbrakk>wf_desc_list fs; wf_component_descs_list fs; wf_field_descs (set (field_descs_list fs));
   component_descs_independent_list fs; contained_field_descs_list fs\<rbrakk>
  \<Longrightarrow> wf_lf (lf_set_list fs ps)"
 "\<And>ps. \<lbrakk>wf_desc_tuple f; wf_component_descs_tuple f; wf_field_descs (set (field_descs_tuple f));
   component_descs_independent_tuple f; contained_field_descs_tuple f\<rbrakk>
  \<Longrightarrow> wf_lf (lf_set_tuple f ps)"
proof (induct t and st and fs and f)
case (TypDesc algn st n)
  then show ?case by simp
next
  case (TypScalar sz align d)
  then show ?case by (simp add: wf_field_desc_wf_lf)
next
  case (TypAggregate fs)
then show ?case by simp
next
  case Nil_typ_desc
  then show ?case by simp
next
  case (Cons_typ_desc f fs)
  obtain ft' fn' d' where f: "f = DTuple ft' fn' d'" by (cases f) simp
  from Cons_typ_desc.prems obtain
    wf_f: "wf_desc_tuple f" and
    wf_fs: "wf_desc_list fs" and
    wf_cd_f: "wf_component_descs_tuple f" and
    wf_cd_fs: "wf_component_descs_list fs" and
    wf_fd_f: "wf_field_descs (set (field_descs_tuple f))" and
    wf_fd_fs: "wf_field_descs (set (field_descs_list fs))" and
    ind_f_fs: "field_descs_independent
                (toplevel_field_descs_tuple f @ toplevel_field_descs_list fs)" and
    cont_f: "contained_field_descs_tuple f" and
    cont_fs: "contained_field_descs_list fs" and
    dist_names: "dt_snd f \<notin> dt_snd ` set fs" and
    ind_f: "component_descs_independent_tuple f" and
    ind_fs:"component_descs_independent_list fs"
    by clarsimp

  from Cons_typ_desc.hyps(1) [OF wf_f wf_cd_f wf_fd_f ind_f cont_f]
  have wf_lf_ft': "wf_lf (lf_set ft' (ps @ [fn']))" by (simp add: f)

  from Cons_typ_desc.hyps(2) [OF wf_fs wf_cd_fs wf_fd_fs ind_fs cont_fs]
  have wf_lf_fs: "wf_lf (lf_set_list fs ps)" .


  from field_descs_independent_append_first_ind [OF ind_f_fs, of d']
  have "field_desc_independent (field_access d') (field_update d')
            (set (toplevel_field_descs_list fs))" by (simp add: f)


  from cont_f field_desc_independent_contained_toplevel_to_field_descs [OF cont_fs, where d=d'] this
  have ind_d'_fs: "field_desc_independent (field_access d') (field_update d')
                       (set (field_descs_list fs))"
    by (simp add: f)

  from cont_f fields_contained_toplevel_to_field_descs
  have cont_d'_ft': "fields_contained (field_access d') (field_update d') (set (field_descs ft'))"
    by (auto simp add: f)

  have ti_ind: "ti_ind' (lf_set ft' (ps @ [fn'])) (lf_set_list fs ps)"
  proof
    fix x y
    assume x_in: "x \<in> lf_set ft' (ps @ [fn'])"
    assume y_in: "y \<in> lf_set_list fs ps"
    from lf_set_subset_field_descs(1) x_in
    have x_in': "lf_fd x \<in> set (field_descs ft')" by blast
    from lf_set_subset_field_descs(3) y_in
    have y_in': "lf_fd y \<in> set (field_descs_list fs)" by blast

    from field_desc_independent_symmetric_singleton [OF ind_d'_fs y_in']
    have "field_desc_independent (field_access (lf_fd y)) (field_update (lf_fd y)) {d'}" .

    from field_desc_independent_contained_transitive [OF cont_d'_ft' this]
    have "field_desc_independent (field_access (lf_fd y)) (field_update (lf_fd y))
            (set (field_descs ft'))" .

    from field_desc_independent.fu_commutes [OF this x_in'] fu_commutes_sym
    show "fu_commutes (field_update (lf_fd x)) (field_update (lf_fd y))"
      by blast
  next
    fix x y
    assume x_in: "x \<in> lf_set ft' (ps @ [fn'])"
    assume y_in: "y \<in> lf_set_list fs ps"
    from lf_set_subset_field_descs(1) x_in
    have x_in': "lf_fd x \<in> set (field_descs ft')" by blast
    from lf_set_subset_field_descs(3) y_in
    have y_in': "lf_fd y \<in> set (field_descs_list fs)" by blast

    from field_desc_independent_symmetric_singleton [OF ind_d'_fs y_in']
    have "field_desc_independent (field_access (lf_fd y)) (field_update (lf_fd y)) {d'}" .

    from field_desc_independent_contained_transitive [OF cont_d'_ft' this]
    have "field_desc_independent (field_access (lf_fd y)) (field_update (lf_fd y))
            (set (field_descs ft'))" .
    from field_desc_independent.acc_upd_new [OF this x_in']
    show "fa_fu_ind (lf_fd x) (lf_fd y) (lf_sz y) (lf_sz x)"
      by (auto simp add: fa_fu_ind_def)
  next
    fix x y
    assume x_in: "x \<in> lf_set ft' (ps @ [fn'])"
    assume y_in: "y \<in> lf_set_list fs ps"
    from lf_set_subset_field_descs(1) x_in
    have x_in': "lf_fd x \<in> set (field_descs ft')" by blast
    from lf_set_subset_field_descs(3) y_in
    have y_in': "lf_fd y \<in> set (field_descs_list fs)" by blast

    from field_desc_independent_symmetric_singleton [OF ind_d'_fs y_in']
    have "field_desc_independent (field_access (lf_fd y)) (field_update (lf_fd y)) {d'}" .

    from field_desc_independent_contained_transitive [OF cont_d'_ft' this]
    have "field_desc_independent (field_access (lf_fd y)) (field_update (lf_fd y))
            (set (field_descs ft'))" .
    from field_desc_independent.acc_upd_old [OF this x_in']
    show "fa_fu_ind (lf_fd y) (lf_fd x) (lf_sz x) (lf_sz y)"
      by (auto simp add: fa_fu_ind_def)
  qed

  from wf_lf_unionI [OF wf_lf_ft' wf_lf_fs ti_ind]
  have "wf_lf (lf_set ft' (ps @ [fn']) \<union> lf_set_list fs ps)" .

  then show ?case by (simp add: f)

next
  case (DTuple_typ_desc ft fn d)
  then show ?case by simp
qed

definition "wf_align_field ti \<equiv> wf_align ti \<and> align_field ti"



lemma wf_align_field_empty_typ_info: "wf_align_field (empty_typ_info algn n)"
  by (simp add: wf_align_field_def wf_align_simps align_field_empty_typ_info)

lemma (in mem_type) wf_align_field_ti_typ_pad_combine:
  "aggregate ti \<Longrightarrow> wf_align_field ti \<Longrightarrow>
      wf_align_field (ti_typ_pad_combine (TYPE('a)) acc upd algn fn ti)"
  by (auto simp add:  wf_align_field_def wf_align_ti_typ_pad_combine align_field_ti_typ_pad_combine)

lemma (in mem_type) wf_align_field_ti_typ_combine:
  "aggregate ti \<Longrightarrow> wf_align_field ti \<Longrightarrow> 2 ^ align_td (typ_info_t TYPE('a)) dvd size_td ti \<Longrightarrow>
      wf_align_field (ti_typ_combine (TYPE('a)) acc upd algn fn ti)"
  by (auto simp add: wf_align_field_def wf_align_ti_typ_combine align_field_ti_typ_combine)

lemma wf_align_field_ti_pad_combine: "aggregate ti \<Longrightarrow> wf_align_field ti \<Longrightarrow> wf_align_field (ti_pad_combine n ti)"
  by (auto simp add: wf_align_field_def wf_align_ti_pad_combine align_field_ti_pad_combine)

lemma wf_align_field_final_pad: "aggregate ti \<Longrightarrow> wf_align_field ti \<Longrightarrow> wf_align_field (final_pad algn ti)"
  by (auto simp add: wf_align_field_def wf_align_final_pad align_field_final_pad)

lemmas wf_align_field_simps =
  wf_align_field_empty_typ_info
  wf_align_field_ti_typ_pad_combine
  wf_align_field_ti_typ_combine
  wf_align_field_ti_pad_combine
  wf_align_field_final_pad


text \<open> The following theorem is used to prove that a new type is in class
@{class xmem_contained_type}, for which we have constructed the extended type info with:
 \<^item> @{const empty_typ_info}
 \<^item> @{const ti_typ_pad_combine} (@{const ti_typ_combine}, @{const ti_pad_combine})
 \<^item> @{const final_pad}.

Note that the field-types are already in @{class xmem_contained_type}.

\<close>
theorem tuned_xmem_contained_type_class_intro:
 assumes wf_desc: "wf_desc (typ_info_t TYPE('a))"
 assumes wf_size_desc: "wf_size_desc (typ_info_t TYPE('a))"
 assumes align_dvd: "align_of TYPE('a) dvd size_of TYPE('a)"
 assumes wf_align_field: "wf_align_field (typ_info_t TYPE('a))"
 assumes size: "size_of TYPE('a) < addr_card"
 assumes entire_update: "\<And>bs v w. length bs = size_of TYPE('a)
            \<Longrightarrow> field_update (component_desc (typ_info_t TYPE('a))) bs v =
                field_update (component_desc (typ_info_t TYPE('a))) bs w"
 assumes wf_component_descs: "wf_component_descs (typ_info_t TYPE('a))"
 assumes ind: "component_descs_independent (typ_info_t TYPE('a))"
 assumes wf_field_descs: "wf_field_descs (set (field_descs (typ_info_t TYPE('a))))"
 assumes contained_field_descs: "contained_field_descs (typ_info_t TYPE('a))"
 assumes wf_padding: "wf_padding (typ_info_t TYPE('a))"
 shows "OFCLASS('a::c_type, xmem_contained_type_class)"
proof
  show "wf_desc (typ_info_t TYPE('a))"
    by (rule wf_desc)
next
  show "wf_size_desc (typ_info_t TYPE('a))"
    by (rule wf_size_desc)
next
  show "wf_lf (lf_set (typ_info_t TYPE('a)) [])"
  proof -
    text \<open>We can show that all leafs of the tree are disjoint, by exploiting the correct
          nesting of fields in the \<open>toplevel_structure\<close>.\<close>
    from component_descs_independent_contained_wf_lf(1) [OF wf_desc wf_component_descs
         wf_field_descs ind contained_field_descs]
    show ?thesis .
  qed
next
  fix bs v w
  show "length bs = size_of TYPE('a) \<longrightarrow>
       update_ti_t (typ_info_t TYPE('a)) bs v =
       update_ti_t (typ_info_t TYPE('a)) bs w"
  proof
    text \<open>The updates are captured by the component-descriptor of the toplevel structure.\<close>
    assume len: "length bs = size_of TYPE('a)"
    from entire_update [OF len] wf_field_descs len wf_component_descs
    show "update_ti_t (typ_info_t TYPE('a)) bs v =
       update_ti_t (typ_info_t TYPE('a)) bs w"
      by (simp add: ind size_of_def update_ti_component_desc_compatible(1) update_ti_t_def)
  qed
next
  show "align_of TYPE('a) dvd size_of TYPE('a)" by (rule align_dvd)
next
  from wf_align_field
  show "align_field (typ_info_t TYPE('a))" by (simp add: wf_align_field_def)
next
  show "size_of TYPE('a) < addr_card" by (rule size)
next
  show "wf_component_descs (typ_info_t TYPE('a))" by (rule wf_component_descs)
next
  show "component_descs_independent (typ_info_t TYPE('a))" by (rule ind)
next
  show "wf_field_descs (set (field_descs (typ_info_t TYPE('a))))" by (rule wf_field_descs)
next
  show "contained_field_descs (typ_info_t TYPE('a))" by (rule contained_field_descs)
next
  from wf_align_field
  show "wf_align (typ_info_t TYPE('a))"
    by (simp add: wf_align_field_def)
next
  from wf_padding
  show "wf_padding (typ_info_t TYPE('a))" .
qed

lemma field_sz_extend_ti: "aggregate t \<Longrightarrow>
  field_sz (component_desc (extend_ti t ft algn fn d)) = field_sz (component_desc t) + field_sz d"
  apply (cases t)
  subgoal for x1 st n
    apply (cases st)
     apply (simp)
    subgoal for fs
      apply simp
      done
    done
  done

lemma field_sz_empty_typ_info: "field_sz (component_desc (empty_typ_info algn n)) = 0"
  by (simp add: empty_typ_info_def)

lemma (in c_type) field_sz_ti_typ_combine:
  fixes acc:: "'s \<Rightarrow> 'a"
  assumes agg: "aggregate t"
  shows " field_sz (component_desc (ti_typ_combine ft acc upd algn fn t)) =
    field_sz (component_desc t) +  size_of TYPE('a)"
  using agg
  by (simp add: ti_typ_combine_def Let_def field_sz_extend_ti )

lemma (in c_type) field_sz_ti_pad_combine:
  fixes acc:: "'s \<Rightarrow> 'a"
  assumes agg: "aggregate t"
  shows " field_sz (component_desc (ti_pad_combine n t)) =
    field_sz (component_desc t) +  n"
  using agg
  by (simp add: ti_pad_combine_def Let_def field_sz_extend_ti padding_desc_def)

lemma (in c_type) field_sz_ti_typ_pad_combine:
  fixes acc:: "'s \<Rightarrow> 'a"
  assumes agg: "aggregate t"
  shows "field_sz (component_desc (ti_typ_pad_combine ft acc upd algn fn t)) =
    field_sz (component_desc t) +  size_of TYPE('a) + padup (max (2 ^ algn) (align_of TYPE('a))) (size_td t)"
  using agg
  by (simp add: ti_typ_pad_combine_def Let_def field_sz_ti_pad_combine field_sz_ti_typ_combine)

lemma component_desc_map_align[simp]:"component_desc (map_align f t) = component_desc t"
  by (cases t) simp

lemma field_sz_final_pad:
  assumes agg: "aggregate t"
  shows " field_sz (component_desc (final_pad algn t)) =
    field_sz (component_desc t) + padup (2^(max algn (align_td t))) (size_td t)"
  using agg
  by (simp add: final_pad_def Let_def field_sz_ti_pad_combine)




lemma split_fold_append: "split_fold f (xs@ys) bs s =
(let (s', bs') = split_fold f xs bs s in split_fold f ys bs' s')"
  apply (induct xs arbitrary: bs ys s)
  apply simp
   apply clarsimp
  by (metis prod.case_distrib)

lemma apply_field_updates_append: "apply_field_updates (xs@ys) bs s =
(let (s', bs') = apply_field_updates xs bs s in apply_field_updates ys bs' s')"
  by (simp add: apply_field_updates_def split_fold_append)

lemma snd_apply_field_updates: "snd (apply_field_updates ds bs s) = (drop (foldl (+) 0 (map field_sz ds)) bs)"
  apply (induct ds arbitrary:bs s)
   apply simp
  apply (simp add: add.commute sum_nat_foldl)
  done


lemma field_update_extend_ti:
  assumes agg: "aggregate t"
  shows "field_update (component_desc (extend_ti t ft algn fn d)) bs v =
         field_update d ((drop (field_sz (component_desc t))) bs)
           (field_update (component_desc t) bs v)"
proof (cases t)
  case (TypDesc algn st n)
  show ?thesis
  proof (cases st)
    case (TypScalar sz align d)
    with agg show ?thesis by (simp add: TypDesc)
  next
    case (TypAggregate fs)
    from snd_apply_field_updates
    have "fst (apply_field_updates (map dt_trd fs @ [d]) bs v) =
          field_update d (drop (foldl (+) 0 (map (field_sz \<circ> dt_trd) fs)) bs)
           (fst (apply_field_updates (map dt_trd fs) bs v))"
      by (simp add: apply_field_updates_append case_prod_beta snd_apply_field_updates)

    then show ?thesis by (simp add: TypDesc TypAggregate)
  qed
qed


lemma field_update_empty_typ_info: "field_update (component_desc (empty_typ_info algn n)) bs s = s"
  by (simp add: empty_typ_info_def)

lemma (in c_type) field_update_ti_typ_combine:
  assumes agg: "aggregate t"
  shows "field_update (component_desc (ti_typ_combine (ft::'a itself) acc upd algn fn t)) bs v =
         (upd o xfrom_bytes) ((drop (field_sz (component_desc t))) bs)
           (field_update (component_desc t) bs v)"
  using agg
  by (simp add: ti_typ_combine_def field_update_extend_ti)

lemma field_update_ti_pad_combine:
  assumes agg: "aggregate t"
  shows "field_update (component_desc (ti_pad_combine n t)) bs v =
           field_update (component_desc t) bs v"
  using agg
  by (simp add: ti_pad_combine_def Let_def field_update_extend_ti padding_desc_def)


lemma (in c_type) field_update_ti_typ_pad_combine:
  fixes acc:: "'s \<Rightarrow> 'a"
  assumes agg: "aggregate t"
  shows "field_update (component_desc (ti_typ_pad_combine ft acc upd algn fn t)) bs v =
         (upd o xfrom_bytes)  (drop (field_sz (component_desc t) + padup (max (2 ^ algn) (align_of TYPE('a))) (size_td t)) bs)
           (field_update (component_desc t) bs v)"
  using agg
  apply (clarsimp simp add: ti_typ_pad_combine_def Let_def field_update_ti_pad_combine field_update_ti_typ_combine)
  apply (clarsimp simp add: ti_pad_combine_def field_update_extend_ti Let_def field_sz_extend_ti padding_desc_def)
  done

lemma field_update_final_pad:
  assumes agg: "aggregate t"
  shows "field_update (component_desc (final_pad algn t)) bs v =
           field_update (component_desc t) bs v"
  using agg
  by (simp add: final_pad_def field_update_ti_pad_combine Let_def)

lemma set_toplevel_field_descs_extend_ti:
"set (toplevel_field_descs (extend_ti t ft algn fn d)) \<subseteq> insert d (set (toplevel_field_descs t))"
  apply (cases t)
  subgoal for x1 st n
    apply (cases st)
     apply simp
    subgoal for fs
      apply (cases fs)
       apply simp
      subgoal for f fs'
        apply simp
        done
      done
    done
  done

lemma set_toplevel_field_descs_extend_ti_aggregate:
"aggregate t \<Longrightarrow> set (toplevel_field_descs (extend_ti t ft algn fn d)) = insert d (set (toplevel_field_descs t))"
  apply (cases t)
  subgoal for x1 st n
    apply (cases st)
     apply simp
    subgoal for fs
      apply (cases fs)
       apply simp
      subgoal for f fs'
        apply simp
        done
      done
    done
  done

lemma (in c_type) set_toplevel_field_descs_ti_typ_combine:
"set (toplevel_field_descs (ti_typ_combine ft (acc::'b \<Rightarrow> 'a) upd algn fn t)) \<subseteq>
 insert \<lparr>field_access = xto_bytes \<circ> acc, field_update = upd \<circ> xfrom_bytes, field_sz = size_of TYPE('a)\<rparr>
 (set (toplevel_field_descs t))"
  apply (simp add: ti_typ_combine_def)
  apply (rule set_toplevel_field_descs_extend_ti)
  done

lemma (in c_type) set_toplevel_field_descs_ti_typ_combine_aggregate:
  fixes acc::"'s \<Rightarrow> 'a"
  assumes agg: "aggregate t"
  shows "set (toplevel_field_descs (ti_typ_combine ft acc upd algn fn t)) =
         insert \<lparr>field_access = xto_bytes \<circ> acc, field_update = upd \<circ> xfrom_bytes, field_sz = size_of TYPE('a)\<rparr>
         (set (toplevel_field_descs t))"
  using agg
  apply (simp add: ti_typ_combine_def)
  apply (rule set_toplevel_field_descs_extend_ti_aggregate)
  apply simp
  done

lemma set_field_descs_extend_ti_aggregate:
"aggregate t \<Longrightarrow> set (field_descs (extend_ti t ft algn fn d)) = insert d (set (field_descs ft) \<union> set (field_descs t))"
  apply (cases t)
  subgoal for x1 st n
    apply (cases st)
     apply simp
    subgoal for fs
      apply (cases fs)
       apply simp
      subgoal for f fs'
        apply auto
        done
      done
    done
  done

lemma (in c_type) set_field_descs_ti_typ_combine_aggregate:
  fixes acc::"'s \<Rightarrow> 'a"
  assumes agg: "aggregate t"
  shows "set (field_descs (ti_typ_combine ft acc upd algn fn t)) =
           insert \<lparr>field_access = xto_bytes \<circ> acc, field_update = upd \<circ> xfrom_bytes, field_sz = size_of TYPE('a)\<rparr>
           (set (field_descs (adjust_ti (typ_info_t TYPE('a)) acc upd)) \<union> set (field_descs t))"
  using agg
  apply (simp add: ti_typ_combine_def)
  apply (simp add: set_field_descs_extend_ti_aggregate)
  done


locale padding=
  fixes d::"'a field_desc"
  assumes independent: "field_desc_independent acc upd {d}"


lemma pad_is_padding: "padding (padding_desc n)"
  unfolding padding_desc_def
  apply (rule padding.intro)
  apply (rule field_desc_independent.intro)
    apply (auto simp add: fu_commutes_def)
  done

definition PAD::"'a field_desc set" where "PAD = {d. padding d}"

lemma in_PAD_iff[iff]: "d \<in> PAD \<longleftrightarrow> (padding d)" by (auto simp add: PAD_def)

lemma (in c_type) set_toplevel_field_descs_ti_pad_combine_aggregate:
  fixes acc::"'s \<Rightarrow> 'a"
  assumes agg: "aggregate t"
  shows "set (toplevel_field_descs (ti_pad_combine n t)) \<union> PAD =
         set (toplevel_field_descs t) \<union> PAD"
  using agg
  by (auto simp add: ti_pad_combine_def Let_def set_toplevel_field_descs_extend_ti_aggregate
      pad_is_padding)

lemma (in c_type) set_toplevel_field_descs_ti_typ_pad_combine_aggregate:
  fixes acc::"'s \<Rightarrow> 'a"
  assumes agg: "aggregate t"
  shows "set (toplevel_field_descs (ti_typ_pad_combine ft acc upd algn fn t)) \<union> PAD  =
           insert \<lparr>field_access = xto_bytes \<circ> acc, field_update = upd \<circ> xfrom_bytes, field_sz = size_of TYPE('a)\<rparr>
           ((set (toplevel_field_descs t)) \<union> PAD) "
  using agg
  apply (simp add: ti_typ_pad_combine_def Let_def)
  apply (cases "0 < padup (max (2 ^ algn) (align_of TYPE('a))) (size_td t)")
   apply clarsimp
   using set_toplevel_field_descs_ti_pad_combine_aggregate [OF agg, of  "(padup (max (2 ^ algn) (align_of TYPE('a))) (size_td t))"]
      set_toplevel_field_descs_ti_typ_combine_aggregate [OF aggregate_ti_pad_combine [of "(padup (max (2 ^ algn) (align_of TYPE('a))) (size_td t))" t], of ft acc upd algn fn]
   apply clarsimp
  apply (simp add: set_toplevel_field_descs_ti_typ_combine_aggregate)
  done

lemma toplevel_field_descs_map_align[simp]: "toplevel_field_descs (map_align f t) = toplevel_field_descs t"
  by (cases t) simp

lemma set_toplevel_field_descs_final_pad_aggregate:
  assumes agg: "aggregate t"
  shows "set (toplevel_field_descs (final_pad algn t)) \<union> PAD =
         set (toplevel_field_descs t) \<union> PAD"
  using agg
  by (auto simp add: final_pad_def Let_def set_toplevel_field_descs_ti_pad_combine_aggregate)

lemma set_toplevel_field_descs_empty_typ_info: "set (toplevel_field_descs (empty_typ_info algn n)) = {}"
  by (simp add: empty_typ_info_def)

lemmas set_toplevel_field_descs_combinator_simps =
  set_toplevel_field_descs_empty_typ_info
  set_toplevel_field_descs_ti_typ_combine_aggregate
  set_toplevel_field_descs_ti_typ_pad_combine_aggregate
  set_toplevel_field_descs_final_pad_aggregate

lemma field_descs_independent_PAD:
"field_desc_independent acc upd (D \<union> PAD) = field_desc_independent acc upd D"
  by (auto simp add: field_desc_independent_def padding_def)


lemma field_desc_independent_PAD_expand:
"field_desc_independent acc upd (D \<union> PAD) \<Longrightarrow> field_desc_independent acc upd D"
  by (simp add:  field_descs_independent_PAD)

lemma field_desc_independent_PAD_collapse:
"field_desc_independent acc upd D \<Longrightarrow> field_desc_independent acc upd (D \<union> PAD)"
  by (simp add:  field_descs_independent_PAD)

lemma insert_union_out: "insert d (X \<union> Y) = insert d X \<union> Y"
  by blast


lemmas field_sz_typ_combinators_simps =
  field_sz_final_pad
  field_sz_ti_typ_pad_combine
  field_sz_ti_typ_combine
  field_sz_empty_typ_info

lemmas field_update_typ_combinators_simps =
  field_update_final_pad
  field_update_ti_typ_pad_combine
  field_update_ti_typ_combine
  field_update_empty_typ_info

lemma aggregate_map_align[simp]: "aggregate (map_align f t) = aggregate t"
  by (cases t) simp

lemma aggregate_final_pad[simp]: "aggregate t \<Longrightarrow> aggregate (final_pad algn t)"
  by (simp add: final_pad_def Let_def)

lemmas aggregate_typ_combinators_simps =
  aggregate_empty_typ_info
  aggregate_ti_pad_combine
  aggregate_ti_typ_pad_combine
  aggregate_final_pad



lemma wf_padding_empty_typ_info: "wf_padding (empty_typ_info algn tn)"
  by (simp add: empty_typ_info_def)

lemma is_padding_tag_padding_tag[simp]: "is_padding_tag (padding_tag n)"
  by (simp add: is_padding_tag_def padding_tag_def)

lemma is_padding_tag_pad_typ[simp]: "is_padding_tag (TypDesc 0 (TypScalar n 0 (padding_desc n)) ''!pad_typ'')"
  by (simp add: is_padding_tag_def padding_tag_def)

lemma wf_padding_padding_tag: "wf_padding (padding_tag n)"
  by (simp add: padding_tag_def)

lemma wf_padding_tuple_padI:
  "is_padding_tag s \<Longrightarrow>  wf_padding_tuple (DTuple s (CHR ''!''#xs) d)"
  by (auto simp add: is_padding_tag_def wf_padding_padding_tag)

lemma wf_padding_tuple_no_padI:
  "\<not> padding_field_name fn \<Longrightarrow> wf_padding s \<Longrightarrow> wf_padding_tuple (DTuple s fn d)"
  by (simp)

lemma wf_padding_extend_ti:
  fixes
  t :: "'a xtyp_info" and
  st :: "'a xtyp_info_struct" and
  ts :: "'a xtyp_info_tuple list" and
  x :: "'a xtyp_info_tuple"
  shows
"wf_padding t \<Longrightarrow> wf_padding_tuple (DTuple s fn d) \<Longrightarrow>
    wf_padding (extend_ti t s n fn d)"

"wf_padding_struct st \<Longrightarrow> wf_padding_tuple (DTuple s fn d) \<Longrightarrow>
    wf_padding_struct (extend_ti_struct st s fn d)"

"wf_padding_list ts \<Longrightarrow> wf_padding_tuple (DTuple s fn d) \<Longrightarrow>
   wf_padding_list (ts @ [DTuple s fn d])"

"wf_padding_tuple x \<Longrightarrow> wf_padding_tuple x"
  by (induct t and st and ts and x) auto

lemma is_padding_tag_update_desc: "is_padding_tag t \<Longrightarrow>
      (\<And>x. upd (acc x) x = x) \<Longrightarrow>
       is_padding_tag
        (map_td (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) t)"
  by (auto simp add: is_padding_tag_def padding_tag_def padding_desc_def update_desc_def fun_eq_iff)


lemma wf_padding_adjust_ti:
  fixes
  t :: "'a xtyp_info" and
  st :: "'a xtyp_info_struct" and
  ts :: "'a xtyp_info_tuple list" and
  x :: "'a xtyp_info_tuple"
assumes upd_acc_id: "(\<And>x. upd (acc x) x = x)"
  shows
"wf_padding t \<Longrightarrow>
  wf_padding (map_td (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) t)"

"wf_padding_struct st \<Longrightarrow>
  wf_padding_struct (map_td_struct (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) st)"

"wf_padding_list ts \<Longrightarrow>
  wf_padding_list (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) ts)"

"wf_padding_tuple x \<Longrightarrow>
  wf_padding_tuple (map_td_tuple (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) x)"
  apply  (induct t and st and ts and x)
  by (auto simp add: is_padding_tag_update_desc upd_acc_id)


lemma wf_padding_ti_pad_combine: "wf_padding t \<Longrightarrow> wf_padding (ti_pad_combine n t)"
  by (simp add: ti_pad_combine_def Let_def wf_padding_extend_ti(1) )

lemma (in c_type) wf_padding_ti_typ_combine:
"wf_padding t \<Longrightarrow> wf_padding (typ_info_t TYPE('a)) \<Longrightarrow> (\<And>xs. fn \<noteq> CHR ''!''#xs) \<Longrightarrow> (\<And>x. upd (acc x) x = x) \<Longrightarrow>
 wf_padding (ti_typ_combine (TYPE('a)) acc upd algn fn t)"
  apply (simp add: ti_typ_combine_def Let_def)
  apply (rule wf_padding_extend_ti(1))
   apply assumption
  apply (simp add: adjust_ti_def wf_padding_adjust_ti(1) padding_field_name_def)
  done

lemma (in c_type) wf_padding_ti_typ_pad_combine:
"wf_padding t \<Longrightarrow> wf_padding (typ_info_t TYPE('a)) \<Longrightarrow> (\<And>xs. fn \<noteq> CHR ''!''#xs) \<Longrightarrow> (\<And>x. upd (acc x) x = x) \<Longrightarrow>
 wf_padding (ti_typ_pad_combine (TYPE('a)) acc upd algn fn t)"
  by (simp add: ti_typ_pad_combine_def wf_padding_ti_typ_combine wf_padding_ti_pad_combine Let_def)

lemma wf_padding_map_align: "wf_padding t \<Longrightarrow> wf_padding (map_align f t)"
  by (cases t) (simp add: map_align_def)

lemma wf_padding_final_pad: "wf_padding t \<Longrightarrow> wf_padding (final_pad n t)"
  by (simp add: final_pad_def wf_padding_ti_pad_combine Let_def wf_padding_map_align)

lemmas wf_padding_combinator_simps =
  wf_padding_empty_typ_info
  wf_padding_final_pad
  wf_padding_ti_typ_pad_combine
  wf_padding_ti_typ_combine


end
