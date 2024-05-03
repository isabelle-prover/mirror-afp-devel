(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* License: BSD, terms see file ./LICENSE *)

(* Definitions supporting the extremely long CTypes.thy *)

theory CTypesDefs
imports
  CTypesBase
begin

section "C types setup"

type_synonym field_name = string
type_synonym qualified_field_name = "field_name list"

type_synonym typ_name = string


text \<open>A \<open>typ_desc\<close> wraps a \<open>typ_struct\<close> with a typ name.
        A \<open>typ_struct\<close> is either a Scalar, with size, alignment and either a
        field description (for \<open>typ_info\<close>) or a 'normalisor'
        (for \<open>typ_uinfo\<close>), or an Aggregate, with a list of \<open>typ_desc\<close>,
        field name, and field descripton (for the complete sub-structure) or unit
        (for \<open>typ_uinfo\<close>). The field description for aggregates is an extension of
        the original work of H. Tuch. It is used to make the construction of a new structure from
        nested structures / arrays more efficient. Properties like commutation of fields can
        be expressed and proven for the toplevel fields only, without having to re-examine the
        nested leafs of the tree.
\<close>

datatype
         ('a,'b) typ_desc   = TypDesc nat "('a, 'b) typ_struct" typ_name
    and  ('a,'b) typ_struct = TypScalar nat nat "'a" |
                         TypAggregate "(('a, 'b) typ_desc, field_name, 'b) dt_tuple list"

datatype_compat dt_tuple
datatype_compat typ_desc typ_struct
print_theorems
(* These recreate the precise order of subgoals of the old datatype package *)
lemma typ_desc_induct:
  "\<lbrakk>\<And>nat typ_struct list. P2 typ_struct \<Longrightarrow> P1 (TypDesc nat typ_struct list); \<And>nat1 nat2 a. P2 (TypScalar nat1 nat2 a);
       \<And>list. P3 list \<Longrightarrow> P2 (TypAggregate list); P3 []; \<And>dt_tuple list. \<lbrakk>P4 dt_tuple; P3 list\<rbrakk> \<Longrightarrow> P3 (dt_tuple # list);
       \<And>typ_desc list b. P1 typ_desc \<Longrightarrow> P4 (DTuple typ_desc list b)\<rbrakk>
      \<Longrightarrow> P1 typ_desc"
   by (rule compat_typ_desc.induct)

lemma typ_struct_induct:
    "\<lbrakk>\<And>nat typ_struct list. P2 typ_struct \<Longrightarrow> P1 (TypDesc nat typ_struct list); \<And>nat1 nat2 a. P2 (TypScalar nat1 nat2 a);
       \<And>list. P3 list \<Longrightarrow> P2 (TypAggregate list); P3 []; \<And>dt_tuple list. \<lbrakk>P4 dt_tuple; P3 list\<rbrakk> \<Longrightarrow> P3 (dt_tuple # list);
       \<And>typ_desc list b. P1 typ_desc \<Longrightarrow> P4 (DTuple typ_desc list b)\<rbrakk>
      \<Longrightarrow> P2 typ_struct"
   by (rule compat_typ_struct.induct)

lemma typ_list_induct:
    "\<lbrakk>\<And>nat typ_struct list. P2 typ_struct \<Longrightarrow> P1 (TypDesc nat typ_struct list); \<And>nat1 nat2 a. P2 (TypScalar nat1 nat2 a);
      \<And>list. P3 list \<Longrightarrow> P2 (TypAggregate list); P3 []; \<And>dt_tuple list. \<lbrakk>P4 dt_tuple; P3 list\<rbrakk> \<Longrightarrow> P3 (dt_tuple # list);
      \<And>typ_desc list b. P1 typ_desc \<Longrightarrow> P4 (DTuple typ_desc list b)\<rbrakk>
     \<Longrightarrow> P3 list"
   by (rule compat_typ_desc_char_list_dt_tuple_list.induct)

lemma typ_dt_tuple_induct:
    "\<lbrakk>\<And>nat typ_struct list. P2 typ_struct \<Longrightarrow> P1 (TypDesc nat typ_struct list); \<And>nat1 nat2 a. P2 (TypScalar nat1 nat2 a);
      \<And>list. P3 list \<Longrightarrow> P2 (TypAggregate list); P3 []; \<And>dt_tuple list. \<lbrakk>P4 dt_tuple; P3 list\<rbrakk> \<Longrightarrow> P3 (dt_tuple # list);
      \<And>typ_desc list b. P1 typ_desc \<Longrightarrow> P4 (DTuple typ_desc list b)\<rbrakk>
     \<Longrightarrow> P4 dt_tuple"
   by (rule compat_typ_desc_char_list_dt_tuple.induct)

\<comment> \<open>Declare as default induct rule with old case names\<close>
lemmas typ_desc_typ_struct_inducts [case_names
  TypDesc TypScalar TypAggregate Nil_typ_desc Cons_typ_desc DTuple_typ_desc, induct type] =
  typ_desc_induct typ_struct_induct typ_list_induct typ_dt_tuple_induct

\<comment> \<open>Make sure list induct rule is tried first\<close>
declare list.induct [induct type]

type_synonym ('a, 'b) typ_tuple = "(('a, 'b) typ_desc,field_name, 'b) dt_tuple"

type_synonym typ_uinfo = "(normalisor, unit) typ_desc"
type_synonym typ_uinfo_struct = "(normalisor, unit) typ_struct"
type_synonym typ_uinfo_tuple = "(normalisor, unit) typ_tuple"

record 'a field_desc =
  field_access :: "'a \<Rightarrow> byte list \<Rightarrow> byte list"
  field_update :: "byte list \<Rightarrow> 'a \<Rightarrow> 'a"
  field_sz :: nat

type_synonym ('a, 'b) typ_info = "('a field_desc, 'b) typ_desc"
type_synonym ('a, 'b) typ_info_struct = "('a field_desc, 'b) typ_struct"
type_synonym ('a, 'b) typ_info_tuple = "('a field_desc, 'b) typ_tuple"

type_synonym 'a xtyp_tuple = "('a, 'a) typ_tuple"
type_synonym 'a xtyp_info = "('a field_desc, 'a field_desc) typ_desc"
type_synonym 'a xtyp_info_struct = "('a field_desc, 'a field_desc) typ_struct"
type_synonym 'a xtyp_info_tuple = "'a field_desc xtyp_tuple"

definition fu_commutes :: "('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "fu_commutes f g \<equiv> \<forall>v bs bs'. f bs (g bs' v) = g bs' (f bs v)"


text \<open>\<open>size_td\<close> returns the sum of the sizes of all Scalar fields
        comprising a \<open>typ_desc\<close> i.e. the overall size of the type\<close>

(* Could express this and many other typ_desc primrecs as tree fold/map
   combos, but the intuition this way is clearer for anything non-trivial *)
primrec
  size_td :: "('a, 'b) typ_desc \<Rightarrow> nat" and
  size_td_struct :: "('a, 'b) typ_struct \<Rightarrow> nat" and
  size_td_list :: "('a, 'b) typ_tuple list \<Rightarrow> nat" and
  size_td_tuple :: "('a, 'b) typ_tuple \<Rightarrow> nat"
where
  tz0: "size_td (TypDesc algn st nm) = size_td_struct st"

| tz1: "size_td_struct (TypScalar n algn d) = n"
| tz2: "size_td_struct (TypAggregate xs) = size_td_list xs"

| tz3: "size_td_list [] = 0"
| tz4: "size_td_list (x#xs) = size_td_tuple x + size_td_list xs"

| tz5: "size_td_tuple (DTuple t n d) = size_td t"


text \<open>\<open>access_ti\<close> overlays the byte-wise representation of an object
        on a given byte list, given the \<open>typ_info\<close> (i.e. the layout)\<close>

primrec
  access_ti :: "('a, 'b) typ_info \<Rightarrow> ('a \<Rightarrow> byte list \<Rightarrow> byte list)" and
  access_ti_struct :: "('a, 'b) typ_info_struct \<Rightarrow>
    ('a \<Rightarrow> byte list \<Rightarrow> byte list)" and
  access_ti_list :: "('a,  'b) typ_info_tuple list \<Rightarrow>
    ('a \<Rightarrow> byte list \<Rightarrow> byte list)" and
  access_ti_tuple :: "('a, 'b) typ_info_tuple \<Rightarrow> ('a \<Rightarrow> byte list \<Rightarrow> byte list)"
where
  fa0: "access_ti (TypDesc algn st nm) = access_ti_struct st"

| fa1: "access_ti_struct (TypScalar n algn d) = field_access d"
| fa2: "access_ti_struct (TypAggregate xs) = access_ti_list xs"

| fa3: "access_ti_list [] = (\<lambda>v bs. [])"
| fa4: "access_ti_list (x#xs) =
         (\<lambda>v bs. access_ti_tuple x v (take (size_td_tuple x) bs) @
                 access_ti_list xs v (drop (size_td_tuple x) bs))"

| fa5: "access_ti_tuple (DTuple t nm d) = access_ti t"

text \<open>@{text access_ti\<^sub>0} overlays the representation of an object on a
        list of zero bytes\<close>

definition access_ti\<^sub>0 :: "('a, 'b) typ_info \<Rightarrow> ('a \<Rightarrow> byte list)" where
  "access_ti\<^sub>0 t \<equiv> \<lambda>v. access_ti t v (replicate (size_td t) 0)"

text \<open>\<open>update_ti\<close> updates an object, given a list of bytes (the
        representation of the new value), and the \<open>typ_info\<close>\<close>

primrec
  update_ti :: "('a, 'b) typ_info \<Rightarrow> (byte list \<Rightarrow> 'a \<Rightarrow> 'a)" and
  update_ti_struct :: "('a, 'b) typ_info_struct \<Rightarrow> (byte list \<Rightarrow> 'a \<Rightarrow> 'a)" and
  update_ti_list :: "('a, 'b) typ_info_tuple list \<Rightarrow> (byte list \<Rightarrow> 'a \<Rightarrow> 'a)" and
  update_ti_tuple :: "('a, 'b) typ_info_tuple \<Rightarrow> (byte list \<Rightarrow> 'a \<Rightarrow> 'a)"
where
  fu0: "update_ti (TypDesc algn st nm) = update_ti_struct st"

| fu1: "update_ti_struct (TypScalar n algn d) = field_update d"
| fu2: "update_ti_struct (TypAggregate xs) = update_ti_list xs"

| fu3: "update_ti_list [] = (\<lambda>bs. id)"
| fu4: "update_ti_list (x#xs) = (\<lambda>bs v.
         update_ti_tuple x (take (size_td_tuple x) bs)
             (update_ti_list xs (drop (size_td_tuple x) bs) v))"

| fu5: "update_ti_tuple (DTuple t nm d) = update_ti t"


text \<open>\<open>update_ti_t\<close> updates an object only if the length of the
        supplied representation equals the object size\<close>

definition update_ti_t :: "('a, 'b) typ_info \<Rightarrow> (byte list \<Rightarrow> 'a \<Rightarrow> 'a)" where
  "update_ti_t t \<equiv> \<lambda>bs. if length bs = size_td t then
      update_ti t bs else id"

definition update_ti_struct_t :: "('a, 'b) typ_info_struct \<Rightarrow> (byte list \<Rightarrow> 'a \<Rightarrow> 'a)" where
  "update_ti_struct_t t \<equiv> \<lambda>bs. if length bs = size_td_struct t then
      update_ti_struct t bs else id"

definition update_ti_list_t :: "('a, 'b) typ_info_tuple list  \<Rightarrow> (byte list \<Rightarrow> 'a \<Rightarrow> 'a)" where
  "update_ti_list_t t \<equiv> \<lambda>bs. if length bs = size_td_list t then
      update_ti_list t bs else id"

definition update_ti_tuple_t :: "('a, 'b) typ_info_tuple \<Rightarrow> (byte list \<Rightarrow> 'a \<Rightarrow> 'a)" where
  "update_ti_tuple_t t \<equiv> \<lambda>bs. if length bs = size_td_tuple t then
      update_ti_tuple t bs else id"

lemma update_ti_t_struct_t [simp]: "update_ti_t (TypDesc algn st nm) = update_ti_struct_t st"
  apply (rule ext)
  apply (simp add: update_ti_t_def update_ti_struct_t_def)
  done

lemma update_ti_update_ti_t:
  "length bs = size_td s \<Longrightarrow> update_ti s bs v = update_ti_t s bs v"
  unfolding update_ti_t_def by simp

text \<open>\<open>field_desc\<close> generates the access/update pair for a field,
        given the field's \<open>type_desc\<close>\<close>

definition field_desc :: "('a,  'b) typ_info \<Rightarrow> 'a field_desc" where
  "field_desc t \<equiv> \<lparr> field_access = access_ti t,
      field_update = update_ti_t t, field_sz = size_td t \<rparr>"

declare field_desc_def [simp add]

definition field_desc_struct :: "('a, 'b) typ_info_struct \<Rightarrow> 'a field_desc" where
  "field_desc_struct t \<equiv> \<lparr> field_access = access_ti_struct t,
      field_update = update_ti_struct_t t, field_sz = size_td_struct t \<rparr>"

declare field_desc_struct_def [simp add]

definition field_desc_list :: "('a, 'b) typ_info_tuple list \<Rightarrow> 'a field_desc"
where
  "field_desc_list t \<equiv> \<lparr> field_access = access_ti_list t,
      field_update = update_ti_list_t t, field_sz = size_td_list t \<rparr>"

declare field_desc_list_def [simp add]

definition field_desc_tuple :: "('a, 'b) typ_info_tuple \<Rightarrow> 'a field_desc"
where
  "field_desc_tuple t \<equiv> \<lparr> field_access = access_ti_tuple t,
      field_update = update_ti_tuple_t t, field_sz = size_td_tuple t \<rparr>"

declare field_desc_tuple_def [simp add]


primrec
  map_td :: "(nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('a, 'c) typ_desc \<Rightarrow> ('b, 'd) typ_desc" and
  map_td_struct :: "(nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('a, 'c) typ_struct  \<Rightarrow> ('b, 'd) typ_struct" and
  map_td_list :: "(nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('a, 'c) typ_tuple list \<Rightarrow>
    ('b, 'd) typ_tuple list" and
  map_td_tuple :: "(nat \<Rightarrow> nat \<Rightarrow> 'a  \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('a, 'c) typ_tuple \<Rightarrow> ('b, 'd) typ_tuple"
where
  mat0: "map_td f g (TypDesc algn st nm) = TypDesc algn (map_td_struct f g st) nm"

| mat1: "map_td_struct f g (TypScalar n algn d) = TypScalar n algn (f n algn d)"
| mat2: "map_td_struct f g (TypAggregate xs) = TypAggregate (map_td_list f g xs)"

| mat3: "map_td_list f g [] = []"
| mat4: "map_td_list f g (x#xs) = map_td_tuple f g x # map_td_list f g xs"

| mat5: "map_td_tuple f g (DTuple t n d) = DTuple (map_td f g t) n (g d)"

definition field_norm :: "nat \<Rightarrow> nat \<Rightarrow> ('a,'b) field_desc_scheme \<Rightarrow> (byte list \<Rightarrow> byte list)"
where
  "field_norm \<equiv> \<lambda>n algn d bs.
      if length bs = n then
          field_access d (field_update d bs undefined) (replicate n 0) else
          []"

definition export_uinfo :: "('a, 'b) typ_info \<Rightarrow> typ_uinfo" where
  "export_uinfo t \<equiv> map_td field_norm (\<lambda>_. ()) t"


primrec
  wf_desc :: "('a, 'b) typ_desc \<Rightarrow> bool" and
  wf_desc_struct :: "('a, 'b) typ_struct \<Rightarrow> bool" and
  wf_desc_list :: "('a, 'b) typ_tuple list \<Rightarrow> bool" and
  wf_desc_tuple :: "('a, 'b) typ_tuple \<Rightarrow> bool"
where
  wfd0: "wf_desc (TypDesc algn ts n) = wf_desc_struct ts"

| wfd1: "wf_desc_struct (TypScalar n algn d) = True"
| wfd2: "wf_desc_struct (TypAggregate ts) = wf_desc_list ts"

| wfd3: "wf_desc_list [] = True"
| wfd4: "wf_desc_list (x#xs) = (wf_desc_tuple x \<and> \<not> dt_snd x \<in> dt_snd ` set xs \<and>
          wf_desc_list xs)"

| wfd5: "wf_desc_tuple (DTuple x n d) = wf_desc x"


primrec
  wf_size_desc :: "('a, 'b) typ_desc \<Rightarrow> bool" and
  wf_size_desc_struct :: "('a, 'b) typ_struct \<Rightarrow> bool" and
  wf_size_desc_list :: "('a, 'b) typ_tuple list \<Rightarrow> bool" and
  wf_size_desc_tuple :: "('a, 'b) typ_tuple \<Rightarrow> bool"
where
  wfsd0: "wf_size_desc (TypDesc algn ts n) = wf_size_desc_struct ts"

| wfsd1: "wf_size_desc_struct (TypScalar n algn d) = (0 < n)"
| wfsd2: "wf_size_desc_struct (TypAggregate ts) =
           (ts \<noteq> [] \<and> wf_size_desc_list ts)"

| wfsd3: "wf_size_desc_list [] = True"
| wfsd4: "wf_size_desc_list (x#xs) =
           (wf_size_desc_tuple x \<and> wf_size_desc_list xs)"

| wfsd5: "wf_size_desc_tuple (DTuple x n d) = wf_size_desc x"


definition
  typ_struct :: "('a, 'b) typ_desc \<Rightarrow> ('a, 'b) typ_struct"
where
  "typ_struct t = (case t of TypDesc algn st sz \<Rightarrow> st)"

lemma typ_struct [simp]:
  "typ_struct (TypDesc algn st sz) = st"
  by (simp add: typ_struct_def)

primrec
  typ_name :: "('a, 'b) typ_desc \<Rightarrow> typ_name"
where
  "typ_name (TypDesc algn st nm) = nm"


primrec
  norm_tu :: "typ_uinfo \<Rightarrow> normalisor" and
  norm_tu_struct :: "typ_uinfo_struct \<Rightarrow> normalisor" and
  norm_tu_list :: "typ_uinfo_tuple list \<Rightarrow> normalisor" and
  norm_tu_tuple :: "typ_uinfo_tuple \<Rightarrow> normalisor"
where
  tn0: "norm_tu (TypDesc algn st nm) = norm_tu_struct st"

| tn1: "norm_tu_struct (TypScalar n aln f) = f"
| tn2: "norm_tu_struct (TypAggregate xs) = norm_tu_list xs"

| tn3: "norm_tu_list [] = (\<lambda>bs. [])"
| tn4: "norm_tu_list (x#xs) = (\<lambda>bs.
         norm_tu_tuple x (take (size_td_tuple x) bs) @
         norm_tu_list xs (drop (size_td_tuple x) bs))"

| tn5: "norm_tu_tuple (DTuple t n d) = norm_tu t"

class c_type_name =
  fixes
    typ_name_itself :: "'a itself \<Rightarrow> typ_name"

class c_type = c_type_name +
  fixes
    typ_info_t :: "'a itself \<Rightarrow> 'a xtyp_info"
  assumes type_name_itself_typ_name: "typ_name_itself T = typ_name (typ_info_t T)"

instance c_type \<subseteq> type ..


definition (in c_type) typ_uinfo_t :: "'a itself \<Rightarrow> typ_uinfo" where
  "typ_uinfo_t t \<equiv> export_uinfo (typ_info_t TYPE('a))"

definition (in c_type) to_bytes :: "'a \<Rightarrow> byte list \<Rightarrow> byte list" where
  "to_bytes v \<equiv> access_ti (typ_info_t TYPE('a)) v"


(* from_bytes is now total - all partial C types 'a need to be instantiated
   as c_types using 'a option and the parser needs to do some work
   extracting the value and generating guards for non-None when these are
   used. Luckily for us in our work we never use them. *)
definition (in c_type) from_bytes :: "byte list \<Rightarrow> 'a" where
  "from_bytes bs \<equiv>
      field_update (field_desc (typ_info_t TYPE('a))) bs undefined"


type_synonym ('a, 'b) flr = "(('a, 'b) typ_desc \<times> nat) option"

primrec
  field_lookup :: "('a, 'b) typ_desc \<Rightarrow> qualified_field_name \<Rightarrow> nat \<Rightarrow> ('a, 'b) flr" and
  field_lookup_struct :: "('a, 'b) typ_struct \<Rightarrow> qualified_field_name \<Rightarrow> nat \<Rightarrow>
    ('a, 'b) flr" and
  field_lookup_list :: "('a, 'b) typ_tuple list \<Rightarrow> qualified_field_name \<Rightarrow> nat \<Rightarrow>
    ('a, 'b) flr" and
  field_lookup_tuple :: "('a, 'b) typ_tuple \<Rightarrow> qualified_field_name \<Rightarrow> nat \<Rightarrow> ('a, 'b) flr"
where
  fl0: "field_lookup (TypDesc algn st nm) f m =
         (if f=[] then Some (TypDesc algn st nm,m) else field_lookup_struct st f m)"

| fl1: "field_lookup_struct (TypScalar n algn d) f m = None"
| fl2: "field_lookup_struct (TypAggregate xs) f m = field_lookup_list xs f m"

| fl3: "field_lookup_list [] f m = None"
| fl4: "field_lookup_list (x#xs) f m = (
         case field_lookup_tuple x f m of
           None \<Rightarrow> field_lookup_list xs f (m + size_td (dt_fst x)) |
           Some y \<Rightarrow> Some y)"

| fl5: "field_lookup_tuple (DTuple t nm d) f m =
         (if nm=hd f \<and> f \<noteq> [] then field_lookup t (tl f) m else None)"


lemma field_lookup_wf_desc_pres:
  fixes t::"('a, 'b) typ_desc"
  and st::"('a, 'b) typ_struct"
  and ts::"('a, 'b) typ_tuple list"
  and x::"('a, 'b) typ_tuple"
shows
"wf_desc t \<Longrightarrow> field_lookup t f n = Some (s, m) \<Longrightarrow> wf_desc s"
"wf_desc_struct st \<Longrightarrow> field_lookup_struct st f n = Some (s, m) \<Longrightarrow> wf_desc s"
"wf_desc_list ts \<Longrightarrow> field_lookup_list ts f n = Some (s, m) \<Longrightarrow> wf_desc s"
"wf_desc_tuple x \<Longrightarrow> field_lookup_tuple x f n = Some (s, m) \<Longrightarrow> wf_desc s"
by (induct t and st and ts and x arbitrary: n s m f and n s m f  and n s m f and n s m f)
   (auto split: if_split_asm option.splits)

definition map_td_flr :: "(nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow>
  (('a,'c) typ_desc \<times> nat) option \<Rightarrow> ('b, 'd) flr"
where
  "map_td_flr f g \<equiv> case_option None (\<lambda>(s,n). Some (map_td f g s,n))"


definition
  import_flr :: "(nat \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> ('d \<Rightarrow> 'c) \<Rightarrow>  ('a, 'c) flr \<Rightarrow> (('b,'d) typ_desc \<times> nat) option \<Rightarrow> bool"
where
  "import_flr f g s k \<equiv> case_option (k=None)
      (\<lambda>(s,m). case_option False (\<lambda>(t,n). n=m \<and> map_td f g t=s) k )
      s"

definition
  field_offset_untyped :: "('a, 'b) typ_desc \<Rightarrow> qualified_field_name \<Rightarrow> nat"
where
  "field_offset_untyped t n \<equiv> snd (the (field_lookup t n 0))"

definition (in c_type)
  field_offset :: "'a itself \<Rightarrow> qualified_field_name \<Rightarrow> nat"
where
  "field_offset t n \<equiv> field_offset_untyped (typ_uinfo_t TYPE('a)) n"

definition (in c_type)
  field_ti :: "'a itself \<Rightarrow> qualified_field_name \<rightharpoonup> 'a xtyp_info"
where
  "field_ti t n \<equiv> case_option None (Some \<circ> fst)
      (field_lookup (typ_info_t TYPE('a)) n 0)"


definition (in c_type)
  field_size :: "'a itself \<Rightarrow> qualified_field_name \<Rightarrow> nat"
where
  "field_size t n \<equiv> size_td (the (field_ti t n))"

definition (in c_type)
  field_lvalue :: "'a ptr \<Rightarrow> qualified_field_name \<Rightarrow> addr" ("&'(_\<rightarrow>_')")
where
  "&(p\<rightarrow>f) \<equiv> ptr_val (p::'a ptr) + of_nat (field_offset TYPE('a) f)"

definition (in c_type)
  size_of :: "'a itself \<Rightarrow> nat" where
  "size_of t \<equiv> size_td (typ_info_t TYPE('a))"

lemma (in c_type) size_of_fold: "size_td (typ_info_t TYPE('a)) = size_of TYPE('a)"
  by (simp add: size_of_def)

definition (in c_type)
  norm_bytes :: "'a itself \<Rightarrow> normalisor" where
  "norm_bytes t \<equiv> norm_tu (export_uinfo (typ_info_t t))"

definition (in c_type) to_bytes_p :: "'a \<Rightarrow> byte list" where
  "to_bytes_p v \<equiv> to_bytes v (replicate (size_of TYPE('a)) 0)"

definition (in c_type) zero ::"'a" where
  "zero \<equiv> from_bytes (replicate (size_of TYPE('a)) 0)"

hide_const (open) zero \<comment> \<open>mandatory qualifier: \<^const>\<open>c_type_class.zero\<close>\<close>

syntax
  "_zero" :: "type \<Rightarrow> logic" ("(1ZERO/(1'(_')))")
translations
  "ZERO('a)" => "CONST c_type_class.zero :: ('a)"

typed_print_translation \<open>
let
  val show_zero_types = Attrib.setup_config_bool @{binding show_zero_types} (K true);

  fun zero_tr' ctxt typ _ =
    if Config.get ctxt show_zero_types then
      Syntax.const @{syntax_const "_zero"} $ Syntax_Phases.term_of_typ ctxt typ
    else
      raise Match;

in [(@{const_syntax c_type_class.zero}, zero_tr' )]
end\<close>

primrec
  align_td_wo_align :: "('a, 'b) typ_desc \<Rightarrow> nat" and
  align_td_wo_align_struct :: "('a, 'b) typ_struct \<Rightarrow> nat" and
  align_td_wo_align_list :: "('a, 'b) typ_tuple list \<Rightarrow> nat" and
  align_td_wo_align_tuple :: "('a, 'b) typ_tuple \<Rightarrow> nat"
where
  al0:  "align_td_wo_align (TypDesc algn st nm) = align_td_wo_align_struct st"

| al1:  "align_td_wo_align_struct (TypScalar n algn d) = algn"
| al2:  "align_td_wo_align_struct (TypAggregate xs) = align_td_wo_align_list xs"

| al3:  "align_td_wo_align_list [] = 0"
| al4:  "align_td_wo_align_list (x#xs) = max (align_td_wo_align_tuple x) (align_td_wo_align_list xs)"

| al5:  "align_td_wo_align_tuple (DTuple t n d) = align_td_wo_align t"

primrec
  align_td :: "('a, 'b) typ_desc \<Rightarrow> nat" and
  align_td_struct :: "('a, 'b) typ_struct \<Rightarrow> nat" and
  align_td_list :: "('a, 'b) typ_tuple list \<Rightarrow> nat" and
  align_td_tuple :: "('a, 'b) typ_tuple \<Rightarrow> nat"
where
  al0:  "align_td (TypDesc algn st nm) = algn"

| al1:  "align_td_struct (TypScalar n algn d) = algn"
| al2:  "align_td_struct (TypAggregate xs) = align_td_list xs"

| al3:  "align_td_list [] = 0"
| al4:  "align_td_list (x#xs) = max (align_td_tuple x) (align_td_list xs)"

| al5:  "align_td_tuple (DTuple t n d) = align_td t"


primrec
  wf_align :: "('a, 'b) typ_desc \<Rightarrow> bool" and
  wf_align_struct :: "('a, 'b) typ_struct \<Rightarrow> bool" and
  wf_align_list :: "('a, 'b) typ_tuple list \<Rightarrow> bool" and
  wf_align_tuple :: "('a, 'b) typ_tuple \<Rightarrow> bool"
where
  wfal0: "wf_align (TypDesc algn ts n) = (align_td_wo_align_struct ts \<le> algn \<and>
                                          align_td_struct ts \<le> algn \<and>
                                          wf_align_struct ts)"

| wfal1: "wf_align_struct (TypScalar n algn d) = True"
| wfal2: "wf_align_struct (TypAggregate ts) = (wf_align_list ts)"

| wfal3: "wf_align_list [] = True"
| wfal4: "wf_align_list (x#xs) =
           (wf_align_tuple x \<and> wf_align_list xs)"

| wfal5: "wf_align_tuple (DTuple x n d) = wf_align x"



definition (in c_type) align_of :: "'a itself \<Rightarrow> nat" where
  "align_of t \<equiv> 2^(align_td (typ_info_t TYPE('a)))"

lemma align_td_wo_align_le_align_td:
  fixes t::"('a,'b) typ_info" and
   st::"('a,'b) typ_info_struct" and
   fs::"('a,'b) typ_info_tuple list" and
   f::"('a,'b) typ_info_tuple"
 shows
 "wf_align t \<Longrightarrow> align_td_wo_align t \<le> align_td t"
 "wf_align_struct st \<Longrightarrow> align_td_wo_align_struct st \<le> align_td_struct st"
 "wf_align_list fs \<Longrightarrow> align_td_wo_align_list fs \<le> align_td_list fs"
 "wf_align_tuple f \<Longrightarrow> align_td_wo_align_tuple f \<le> align_td_tuple f"
     apply (induct t and st and fs and f rule: typ_desc_typ_struct_inducts)
       apply auto
  done

lemma (in c_type) align_td_wo_align_le_align_of:
  assumes wf: "wf_align (typ_info_t TYPE('a))"
  shows "2^(align_td_wo_align (typ_info_t TYPE('a))) \<le> align_of (TYPE('a))"
  using align_td_wo_align_le_align_td (1) [OF wf]
  by (simp add: align_of_def)

definition (in c_type)
  ptr_add :: "'a ptr \<Rightarrow> int \<Rightarrow> 'a ptr" (infixl "+\<^sub>p" 65)
where
  "ptr_add (a :: 'a ptr) w \<equiv>
     Ptr (ptr_val a + of_int w * of_nat (size_of (TYPE('a))))"

lemma (in c_type) ptr_add_def':
  "ptr_add (Ptr p :: ('a) ptr) n
      = (Ptr (p + of_int n * of_nat (size_of TYPE('a))))"
  by (cases p, auto simp: ptr_add_def scast_id)

definition (in c_type)
  ptr_sub :: "'a ptr \<Rightarrow> 'a ptr \<Rightarrow> addr_bitsize signed word" (infixl "-\<^sub>p" 65)
where
  "ptr_sub (a :: 'a ptr) p \<equiv>
     ucast (ptr_val a - ptr_val p) div of_nat (size_of (TYPE('a)))"

definition (in c_type) ptr_aligned :: "'a ptr \<Rightarrow> bool" where
  "ptr_aligned p \<equiv> align_of TYPE('a) dvd unat (ptr_val (p::'a ptr))"

type_synonym 'a ptr_guard = "'a ptr \<Rightarrow> bool"

definition (in c_type) c_null_guard :: "'a ptr_guard" where
  "c_null_guard \<equiv> \<lambda>p. 0 \<notin> {ptr_val p..+size_of TYPE('a)}"

definition (in c_type) c_guard :: "'a ptr_guard" where
   "c_guard \<equiv> \<lambda>p. ptr_aligned p \<and> c_null_guard p"

primrec
  td_set :: "('a, 'b) typ_desc \<Rightarrow> nat \<Rightarrow> (('a, 'b) typ_desc \<times> nat) set" and
  td_set_struct :: "('a, 'b) typ_struct \<Rightarrow> nat \<Rightarrow> (('a, 'b) typ_desc \<times> nat) set" and
  td_set_list :: "('a, 'b) typ_tuple list \<Rightarrow> nat \<Rightarrow> (('a,'b) typ_desc \<times> nat) set" and
  td_set_tuple :: "('a, 'b) typ_tuple \<Rightarrow> nat \<Rightarrow> (('a, 'b) typ_desc \<times> nat) set"
where
  ts0:  "td_set (TypDesc algn st nm) m = {(TypDesc algn st nm,m)} \<union> td_set_struct st m"

| ts1:  "td_set_struct (TypScalar n algn d) m = {}"
| ts2:  "td_set_struct (TypAggregate xs) m = td_set_list xs m"

| ts3:  "td_set_list [] m = {}"
| ts4:  "td_set_list (x#xs) m = td_set_tuple x m \<union> td_set_list xs (m + size_td (dt_fst x))"

| ts5:  "td_set_tuple (DTuple t nm d) m = td_set t m"


instantiation typ_desc :: (type, type) ord
begin

definition
  typ_tag_le_def:  "s \<le> (t::('a, 'b) typ_desc) \<equiv> (\<exists>n. (s,n) \<in> td_set t 0)"
definition
  typ_tag_lt_def: "s < (t::('a, 'b) typ_desc) \<equiv> s \<le> t \<and> s \<noteq> t"
instance ..

end


definition
  fd_cons_double_update :: "('a, 'x) field_desc_scheme \<Rightarrow> bool"
where
  "fd_cons_double_update d \<equiv>
      (\<forall>v bs bs'. length bs = length bs' \<longrightarrow> field_update d bs (field_update d bs' v) = field_update d bs v)"

definition
  fd_cons_update_access :: "('a, 'x) field_desc_scheme \<Rightarrow> nat \<Rightarrow> bool"
where
  "fd_cons_update_access d n \<equiv>
      (\<forall>v bs. length bs = n \<longrightarrow> field_update d (field_access d v bs) v = v)"

definition
  norm_desc  :: "('a, 'x) field_desc_scheme \<Rightarrow> nat \<Rightarrow> (byte list \<Rightarrow> byte list)"
where
  "norm_desc d n \<equiv> \<lambda>bs. field_access d (field_update d bs undefined) (replicate n 0)"

definition
  fd_cons_length :: "('a, 'x) field_desc_scheme \<Rightarrow> nat \<Rightarrow> bool"
where
  "fd_cons_length d n \<equiv> \<forall>v bs. length bs = n \<longrightarrow> length (field_access d v bs) = n"

definition
  fd_cons_access_update :: "('a, 'x) field_desc_scheme \<Rightarrow> nat \<Rightarrow> bool"
where
  "fd_cons_access_update d n \<equiv> \<forall>bs bs' v v'. length bs = n \<longrightarrow>
      length bs' = n \<longrightarrow>
      field_access d (field_update d bs v) bs' = field_access d (field_update d bs v') bs'"


definition
  fd_cons_update_normalise :: "('a, 'x) field_desc_scheme \<Rightarrow> nat \<Rightarrow> bool"
where
  "fd_cons_update_normalise d n  \<equiv>
      (\<forall>v bs. length bs=n \<longrightarrow> field_update d (norm_desc d n bs) v = field_update d bs v)"


definition
  fd_cons_desc :: "('a,'x) field_desc_scheme \<Rightarrow> nat \<Rightarrow> bool"
where
  "fd_cons_desc d n \<equiv> fd_cons_double_update d \<and>
      fd_cons_update_access d n \<and>
      fd_cons_access_update d n \<and>
      fd_cons_length d n"

definition
  fd_cons :: "('a, 'b) typ_info \<Rightarrow> bool"
where
  "fd_cons t \<equiv> fd_cons_desc (field_desc t) (size_td t)"

definition
  fd_cons_struct :: "('a, 'b) typ_info_struct \<Rightarrow> bool"
where
  "fd_cons_struct t \<equiv> fd_cons_desc (field_desc_struct t) (size_td_struct t)"

definition
  fd_cons_list :: "('a, 'b) typ_info_tuple list \<Rightarrow> bool"
where
  "fd_cons_list t \<equiv> fd_cons_desc (field_desc_list t) (size_td_list t)"

definition
  fd_cons_tuple :: "('a,  'b) typ_info_tuple \<Rightarrow> bool"
where
  "fd_cons_tuple t \<equiv> fd_cons_desc (field_desc_tuple t) (size_td_tuple t)"


definition
  fa_fu_ind :: "'a field_desc \<Rightarrow> 'a field_desc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>bool"
where
  "fa_fu_ind d d' n n' \<equiv> \<forall>v bs bs'. length bs = n \<longrightarrow> length bs' = n' \<longrightarrow>
      field_access d (field_update d' bs v) bs' = field_access d v bs'"

definition
  wf_fdp :: "(('a, 'b) typ_info \<times> qualified_field_name) set \<Rightarrow> bool"
where
  "wf_fdp t \<equiv> \<forall>x m. (x,m) \<in> t \<longrightarrow> (fd_cons x \<and> (\<forall>y n. (y,n) \<in> t \<and> \<not> m \<le> n \<and> \<not> n \<le> m
      \<longrightarrow> fu_commutes (field_update (field_desc x)) (field_update (field_desc y)) \<and>
          fa_fu_ind (field_desc x) (field_desc y) (size_td y) (size_td x)))"

lemma wf_fdp_list:
  "wf_fdp (xs \<union> ys) \<Longrightarrow> wf_fdp xs \<and> wf_fdp ys"
  by (auto simp: wf_fdp_def)


primrec
  wf_fd :: "('a, 'b) typ_info \<Rightarrow> bool" and
  wf_fd_struct :: "('a, 'b) typ_info_struct \<Rightarrow> bool" and
  wf_fd_list :: "('a, 'b) typ_info_tuple list \<Rightarrow> bool" and
  wf_fd_tuple :: "('a, 'b) typ_info_tuple \<Rightarrow> bool"
where
  wffd0:  "wf_fd (TypDesc algn ts n) = (wf_fd_struct ts)"

| wffd1:  "wf_fd_struct (TypScalar n algn d) = fd_cons_struct (TypScalar n algn d::('a,'b) typ_info_struct)"
| wffd2:  "wf_fd_struct (TypAggregate ts) = wf_fd_list ts"

| wffd3:  "wf_fd_list [] = True"
| wffd4:  "wf_fd_list (x#xs) = (wf_fd_tuple x \<and> wf_fd_list xs \<and>
      fu_commutes (update_ti_tuple_t x) (update_ti_list_t xs) \<and>
      fa_fu_ind (field_desc_tuple x) (field_desc_list xs) (size_td_list xs) (size_td_tuple x)\<and>
      fa_fu_ind (field_desc_list xs) (field_desc_tuple x) (size_td_tuple x) (size_td_list xs))"

| wffd5:  "wf_fd_tuple (DTuple x n d) = wf_fd x"


definition
  tf_set :: "('a, 'b) typ_info \<Rightarrow> (('a, 'b) typ_info \<times> qualified_field_name) set"
where
  "tf_set td \<equiv> {(s,f) | s f. \<exists>n. field_lookup td f 0 = Some (s,n)}"

definition
  tf_set_struct :: "('a, 'b) typ_info_struct \<Rightarrow> (('a, 'b) typ_info \<times> qualified_field_name) set"
where
  "tf_set_struct td \<equiv> {(s,f) | s f. \<exists>n. field_lookup_struct td f 0 = Some (s,n)}"

definition
  tf_set_list :: "('a, 'b) typ_info_tuple list \<Rightarrow> (('a, 'b) typ_info \<times> qualified_field_name) set"
where
  "tf_set_list td \<equiv> {(s,f) | s f. \<exists>n. field_lookup_list td f 0 = Some (s,n)}"

definition
  tf_set_tuple :: "('a, 'b) typ_info_tuple \<Rightarrow> (('a, 'b) typ_info \<times> qualified_field_name) set"
where
  "tf_set_tuple td \<equiv> {(s,f) | s f. \<exists>n. field_lookup_tuple td f 0 = Some (s,n)}"


record 'a leaf_desc =
  lf_fd :: "'a field_desc"
  lf_sz :: nat
  lf_fn :: qualified_field_name


primrec
  lf_set :: "('a, 'b) typ_info \<Rightarrow> qualified_field_name \<Rightarrow> 'a leaf_desc set" and
  lf_set_struct :: "('a, 'b) typ_info_struct \<Rightarrow> qualified_field_name \<Rightarrow> 'a leaf_desc set" and
  lf_set_list :: "('a, 'b) typ_info_tuple list \<Rightarrow> qualified_field_name \<Rightarrow> 'a leaf_desc set" and
  lf_set_tuple :: "('a, 'b) typ_info_tuple \<Rightarrow> qualified_field_name \<Rightarrow> 'a leaf_desc set"
where
  fds0:  "lf_set (TypDesc algn st nm) fn = lf_set_struct st fn"

| fds1:  "lf_set_struct (TypScalar n algn d) fn = {(\<lparr> lf_fd = d, lf_sz = n, lf_fn = fn \<rparr>)}"
| fds2:  "lf_set_struct (TypAggregate xs) fn = lf_set_list xs fn"

| fds3:  "lf_set_list [] fn = {}"
| fds4:  "lf_set_list (x#xs) fn = lf_set_tuple x fn \<union> lf_set_list xs fn"

| fds5:  "lf_set_tuple (DTuple t n d) fn = lf_set t (fn@[n])"


definition
  wf_lf :: "'a leaf_desc set \<Rightarrow> bool"
where
  "wf_lf D \<equiv> \<forall>x. x \<in> D \<longrightarrow> (fd_cons_desc (lf_fd x) (lf_sz x) \<and> (\<forall>y. y \<in> D \<longrightarrow> lf_fn y \<noteq> lf_fn x
      \<longrightarrow> fu_commutes (field_update (lf_fd x)) (field_update (lf_fd y)) \<and>
          fa_fu_ind (lf_fd x) (lf_fd y) (lf_sz y) (lf_sz x)))"

definition
  ti_ind :: "'a leaf_desc set \<Rightarrow> 'a leaf_desc set \<Rightarrow> bool"
where
  "ti_ind X Y \<equiv> \<forall>x y. x \<in> X \<and> y \<in> Y \<longrightarrow> (
      fu_commutes (field_update (lf_fd x)) (field_update (lf_fd y)) \<and>
          fa_fu_ind (lf_fd x) (lf_fd y) (lf_sz y) (lf_sz x) \<and>
          fa_fu_ind (lf_fd y) (lf_fd x) (lf_sz x) (lf_sz y))"


definition
  t2d :: "(('a, 'b) typ_info \<times> qualified_field_name) \<Rightarrow> 'a leaf_desc"
where
  "t2d x \<equiv> \<lparr> lf_fd = field_desc (fst x), lf_sz = size_td (fst x), lf_fn = snd x\<rparr>"


definition
  fd_consistent :: "('a, 'b) typ_info \<Rightarrow> bool"
where
  "fd_consistent t \<equiv> \<forall>f s n. field_lookup t f 0 = Some (s,n)
      \<longrightarrow> fd_cons s"

class wf_type = c_type +
  assumes wf_desc [simp]: "wf_desc (typ_info_t TYPE('a))"
  assumes wf_size_desc [simp]: "wf_size_desc (typ_info_t TYPE('a))"
  assumes wf_lf [simp]: "wf_lf (lf_set (typ_info_t TYPE('a)) [])"

definition
  super_update_bs :: "byte list \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow> byte list"
where
  "super_update_bs v bs n \<equiv> take n bs @ v @
      drop (n + length v) bs"

definition
  disj_fn :: "qualified_field_name \<Rightarrow> qualified_field_name \<Rightarrow> bool"
where
  "disj_fn s t \<equiv> \<not> s \<le> t \<and> \<not> t \<le> s"

definition
  fs_path :: "qualified_field_name list \<Rightarrow> qualified_field_name set"
where
  "fs_path xs \<equiv> {x. \<exists>k. k \<in> set xs \<and> x \<le> k} \<union> {x. \<exists>k. k \<in> set xs \<and> k \<le> x}"

definition
  field_names :: "('a, 'b) typ_desc \<Rightarrow> qualified_field_name set"
where
  "field_names t \<equiv> {f. field_lookup t f 0 \<noteq> None}"

definition
  align_field :: "('a, 'b) typ_desc \<Rightarrow> bool"
where
  "align_field ti \<equiv> \<forall>f s n. field_lookup ti f 0 = Some (s,n) \<longrightarrow>
      2^(align_td s) dvd n"

class mem_type_sans_size = wf_type +
  assumes upd:
     "length bs = size_of TYPE('a) \<longrightarrow>
      update_ti_t (typ_info_t TYPE('a)) bs v
          = update_ti_t (typ_info_t TYPE('a)) bs w"
  assumes align_size_of: "align_of (TYPE('a)) dvd size_of TYPE('a)"
  assumes align_field: "align_field (typ_info_t TYPE('a))"
  assumes wf_align: "wf_align (typ_info_t TYPE('a))"


class mem_type = mem_type_sans_size +
  assumes max_size: "size_of (TYPE('a)) < addr_card"


primrec
  aggregate :: "('a, 'b) typ_desc \<Rightarrow> bool" and
  aggregate_struct :: "('a, 'b) typ_struct \<Rightarrow> bool"
where
  "aggregate (TypDesc algn st tn) = aggregate_struct st"

| "aggregate_struct (TypScalar n algn d) = False"
| "aggregate_struct (TypAggregate ts) = True"

class simple_mem_type = mem_type +
  assumes simple_tag: "\<not> aggregate (typ_info_t TYPE('a))"

definition
  field_of :: "addr \<Rightarrow> ('a, 'b) typ_desc \<Rightarrow> ('a, 'b) typ_desc \<Rightarrow> bool"
where
  "field_of q s t \<equiv> (s,unat q) \<in> td_set t 0"

definition (in c_type)
  field_of_t :: "'a ptr \<Rightarrow> 'b::c_type ptr \<Rightarrow> bool"
where
  "field_of_t p q \<equiv> field_of (ptr_val p - ptr_val q) (typ_uinfo_t TYPE('a))
      (typ_uinfo_t TYPE('b))"

definition (in c_type)
  h_val :: "heap_mem \<Rightarrow> 'a ptr \<Rightarrow> 'a"
where
  "h_val h \<equiv> \<lambda>p. from_bytes (heap_list h (size_of TYPE ('a))
      (ptr_val (p::'a ptr)))"

primrec
  heap_update_list :: "addr \<Rightarrow> byte list \<Rightarrow> heap_mem \<Rightarrow> heap_mem"
where
  heap_update_list_base: "heap_update_list p [] h = h"
| heap_update_list_rec:
  "heap_update_list p (x#xs) h = heap_update_list (p + 1) xs (h(p:= x))"

type_synonym 'a typ_heap_g = "'a ptr \<Rightarrow> 'a"

(* fixme: now redundant with h_val *)
definition (in c_type)
  lift :: "heap_mem \<Rightarrow> 'a typ_heap_g"
where
  "lift h \<equiv> h_val h"

definition (in c_type)
  heap_update :: "'a ptr \<Rightarrow> 'a \<Rightarrow> heap_mem \<Rightarrow> heap_mem"
where
  "heap_update p v h \<equiv> heap_update_list (ptr_val p) (to_bytes v (heap_list h (size_of TYPE('a)) (ptr_val p))) h"

definition (in c_type)
  heap_update_padding :: "'a ptr \<Rightarrow> 'a \<Rightarrow> byte list \<Rightarrow> heap_mem \<Rightarrow> heap_mem" where
"heap_update_padding p v bs h =
  heap_update_list (ptr_val p) (to_bytes v bs) h"

lemma (in c_type) heap_update_heap_update_padding_conv:
  "heap_update p v h = heap_update_padding p v (heap_list h (size_of TYPE('a)) (ptr_val p)) h"
  by (simp add: heap_update_def heap_update_padding_def)

definition (in c_type) heap_upd where
  "heap_upd p f s = heap_update p (f (h_val s p)) s"

definition heap_upd_list :: "nat \<Rightarrow> addr \<Rightarrow> (byte list \<Rightarrow> byte list) \<Rightarrow> heap_mem \<Rightarrow> heap_mem" where
  "heap_upd_list n p f h = heap_update_list p (f (heap_list h n p)) h"

fun
  fold_td' :: "(typ_name \<Rightarrow> ('a \<times> field_name) list \<Rightarrow> 'a) \<times> ('a, 'b) typ_desc \<Rightarrow> 'a"
where
fot0: "fold_td' (f,TypDesc algn st nm) = (case st of
           TypScalar n algn d \<Rightarrow> d |
           TypAggregate ts \<Rightarrow> f nm (map (\<lambda>x. case x of DTuple t n d \<Rightarrow> (fold_td' (f,t),n)) ts))"


definition
  fold_td :: "(typ_name \<Rightarrow> ('a \<times> field_name) list \<Rightarrow> 'a) \<Rightarrow> ('a, 'b) typ_desc \<Rightarrow> 'a"
where
  "fold_td \<equiv> \<lambda>f t. fold_td' (f,t)"

declare fold_td_def [simp]

definition
  fold_td_struct :: "typ_name \<Rightarrow> (typ_name \<Rightarrow> ('a \<times> field_name) list \<Rightarrow> 'a) \<Rightarrow> ('a, 'b) typ_struct \<Rightarrow> 'a"
where
  "fold_td_struct tn f st \<equiv> (case st of
           TypScalar n algn d \<Rightarrow> d |
           TypAggregate ts \<Rightarrow> f tn (map (\<lambda>x. case x of DTuple t n d \<Rightarrow> (fold_td' (f,t),n)) ts))"

declare fold_td_struct_def [simp]

definition
  fold_td_list :: "typ_name \<Rightarrow> (typ_name \<Rightarrow> ('a \<times> field_name) list \<Rightarrow> 'a) \<Rightarrow> ('a, 'b) typ_tuple list \<Rightarrow> 'a"
where
  "fold_td_list tn f ts \<equiv> f tn (map (\<lambda>x. case x of DTuple t n d \<Rightarrow> (fold_td' (f,t),n)) ts)"

declare fold_td_list_def [simp]

definition
  fold_td_tuple :: "(typ_name \<Rightarrow> ('a \<times> field_name) list \<Rightarrow> 'a) \<Rightarrow> ('a, 'b) typ_tuple \<Rightarrow> 'a"
where
  "fold_td_tuple f x \<equiv> (case x of DTuple t n d \<Rightarrow> fold_td' (f,t))"

declare fold_td_tuple_def [simp]

fun
  map_td' :: "((nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) \<times> ('a, 'c) typ_desc \<Rightarrow> ('b, 'd) typ_desc"
where
  "map_td' ((f,g),TypDesc algn st nm) = (TypDesc algn (case st of
           TypScalar n algn d \<Rightarrow> TypScalar n algn (f n algn d) |
           TypAggregate ts \<Rightarrow> TypAggregate (map (\<lambda>x. case x of DTuple t n d \<Rightarrow> DTuple (map_td' ((f,g),t)) n (g d)) ts)) nm)"

definition
  tnSum :: "typ_name \<Rightarrow> (nat \<times> field_name) list \<Rightarrow> nat"
where
  "tnSum \<equiv> \<lambda>tn ts. foldr ((+) o fst) ts 0"

definition
  tnMax :: "typ_name \<Rightarrow> (nat \<times> field_name) list \<Rightarrow> nat"
where
  "tnMax \<equiv> \<lambda>tn ts. foldr (\<lambda>x y. max (fst x) y) ts 0"

definition
  wfd :: "typ_name \<Rightarrow> (bool \<times> field_name) list \<Rightarrow> bool"
where
  "wfd \<equiv> \<lambda>tn ts. distinct (map snd ts) \<and> foldr (\<and>) (map fst ts) True"

definition
  wfsd :: "typ_name \<Rightarrow> (bool \<times> field_name) list \<Rightarrow> bool"
where
  "wfsd \<equiv> \<lambda>tn ts. ts \<noteq> [] \<and> foldr (\<and>) (map fst ts) True"


definition "component_desc_tuple t \<equiv> case t of (DTuple t n d) \<Rightarrow> d"

lemma component_desc_tuple_simp [simp]: "component_desc_tuple (DTuple t n d) = d"
  by (simp add: component_desc_tuple_def)

primrec split_list:: "nat list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "split_list [] bs = [bs]"
| "split_list (n#ns) bs = take n bs # split_list ns (drop n bs)"


lemma concat_split [simp]: "concat (split_list ns bs) = bs"
  by (induct ns arbitrary: bs) auto

primrec split_map':: "('b \<Rightarrow> nat) \<Rightarrow> ('b \<Rightarrow> 'a list \<Rightarrow> 'c) \<Rightarrow> 'b list \<Rightarrow> 'a list \<Rightarrow> 'c list" where
  "split_map' n f [] bs = []"
| "split_map' n f (x#xs) bs = f x (take (n x) bs) # split_map' n f xs (drop (n x) bs)"


lemma length_split_map' [simp]: "length (split_map' n f xs bs) = length xs"
  by (induct xs arbitrary: bs) auto

lemma "split_map' n f xs bs = map (\<lambda>(f',bs'). f' bs') (zip (map f xs) (split_list (map n xs) bs))"
  by (induct xs arbitrary: bs) auto

primrec split_map:: "('b \<Rightarrow> 'a list \<Rightarrow> 'c list) \<Rightarrow> 'b list \<Rightarrow> 'a list \<Rightarrow> 'c list list" where
  "split_map f [] bs = []"
| "split_map f (x#xs) bs = f x bs # split_map f xs (drop (length (f x bs)) bs)"

lemma length_split_map [simp]: "length (split_map f xs bs) = length xs"
  by (induct xs arbitrary: bs) auto

primrec split_fold:: "('b \<Rightarrow> 'a list \<Rightarrow> 'd  \<Rightarrow> ('d \<times> 'a list)) \<Rightarrow> 'b list \<Rightarrow> 'a list \<Rightarrow> 'd \<Rightarrow> ('d \<times> 'a list)"  where
  "split_fold f [] bs s = (s, bs)"
| "split_fold f (x#xs) bs s = (let (s', bs') = f x bs s in split_fold f xs bs' s')"


definition apply_field_update::"'a field_desc \<Rightarrow> byte list \<Rightarrow> 'a \<Rightarrow> ('a \<times> byte list)" where
  "apply_field_update d bs s \<equiv> (field_update d bs s, drop (field_sz d) bs)"

definition apply_field_updates :: "'a field_desc list \<Rightarrow> byte list \<Rightarrow> 'a \<Rightarrow> ('a \<times> byte list)" where
  "apply_field_updates \<equiv> split_fold apply_field_update"

lemma apply_field_updates_Nil [simp]: "apply_field_updates [] bs s = (s, bs)"
  by (simp add: apply_field_updates_def)

lemma apply_field_updates_Cons [simp]: "apply_field_updates (d#ds) bs s =
  apply_field_updates ds (drop (field_sz d) bs) (field_update d bs s)"
  by (simp add: apply_field_updates_def apply_field_update_def)


definition "component_access_tuple v t bs \<equiv> case t of (DTuple t n d) \<Rightarrow> field_access d v bs"

lemma component_access_tuple_simp [simp]: "component_access_tuple v (DTuple t n d) = field_access d v"
  by (auto simp add: component_access_tuple_def)


definition "component_access_struct st v bs =
  (case st of TypScalar _ _ d \<Rightarrow> field_access d v bs
   | TypAggregate fs \<Rightarrow> concat (split_map (component_access_tuple v) fs bs))"

lemma component_access_struct_scalar [simp]:
  "component_access_struct (TypScalar sz align d) = field_access d"
  apply (rule ext)
  apply (rule ext)
  apply (simp add: component_access_struct_def)
  done

lemma component_access_struct_aggregate [simp]:
  "component_access_struct (TypAggregate fs) v bs = concat (split_map (component_access_tuple v) fs bs)"
  by (simp add: component_access_struct_def)

lemma component_access_struct_aggregate_nil [simp]:
"component_access_struct (TypAggregate []) = (\<lambda>v bs. [])"
  apply (rule ext)
  apply (rule ext)
  apply simp
  done


definition "component_update_tuple t bs \<equiv> case t of (DTuple t n d) \<Rightarrow> field_update d bs"

lemma component_update_tuple_simp [simp]: "component_update_tuple (DTuple t n d) = field_update d"
  by (auto simp add: component_update_tuple_def)


definition "component_update_struct st bs v =
  (case st of TypScalar _ _ d \<Rightarrow> field_update d bs v
   | TypAggregate fs \<Rightarrow> fst (apply_field_updates (map dt_trd fs) bs v))"

lemma component_update_struct_scalar [simp]:
  "component_update_struct (TypScalar sz align d) = field_update d"
  apply (rule ext)
  apply (rule ext)
  apply (simp add: component_update_struct_def)
  done

lemma component_update_struct_aggregate [simp]:
  "component_update_struct (TypAggregate fs) bs v = fst (apply_field_updates (map dt_trd fs) bs v)"
  by (simp add: component_update_struct_def)

lemma component_update_struct_aggregate_nil [simp]:
"component_update_struct (TypAggregate []) = (\<lambda>bs. id)"
  apply (rule ext)
  apply (rule ext)
  apply simp
  done


definition "component_sz_struct st =
  (case st of TypScalar _ _ d \<Rightarrow> field_sz d
   | TypAggregate fs \<Rightarrow> foldl (+) 0 (map (field_sz o dt_trd) fs))"

lemma component_sz_struct_scalar [simp]:
  "component_sz_struct (TypScalar sz align d) = field_sz d"
  by (simp add: component_sz_struct_def)


lemma component_sz_struct_aggregate [simp]:
  "component_sz_struct (TypAggregate fs) = foldl (+) 0 (map (field_sz o dt_trd) fs)"
  by (simp add: component_sz_struct_def)



definition "component_desc_struct st =
  \<lparr>field_access = component_access_struct st,
   field_update = component_update_struct st,
   field_sz = component_sz_struct st\<rparr>"

lemma component_desc_struct_simps [simp]:
  "field_access (component_desc_struct st) = component_access_struct st"
  "field_update (component_desc_struct st) = component_update_struct st"
  "field_sz (component_desc_struct st) = component_sz_struct st"
  "component_desc_struct (TypScalar sz align d) = d"
  by (auto simp add: component_desc_struct_def)


definition "component_desc t \<equiv> case t of TypDesc algn st n \<Rightarrow> component_desc_struct st"

lemma component_desc_simps [simp]: "component_desc (TypDesc algn st n) = component_desc_struct st"
  by (simp add: component_desc_def)


definition (in c_type) xto_bytes :: "'a \<Rightarrow> byte list \<Rightarrow> byte list" where
  "xto_bytes \<equiv> field_access (component_desc (typ_info_t TYPE('a)))"

definition (in c_type) xfrom_bytes  :: "byte list \<Rightarrow> 'a" where
  "xfrom_bytes bs \<equiv> field_update (component_desc (typ_info_t TYPE('a))) bs undefined"

primrec
  toplevel_field_descs :: "'a xtyp_info \<Rightarrow> 'a field_desc list" and
  toplevel_field_descs_struct :: "'a xtyp_info_struct \<Rightarrow> 'a field_desc list" and
  toplevel_field_descs_list :: "'a xtyp_info_tuple list \<Rightarrow> 'a field_desc list" and
  toplevel_field_descs_tuple :: "'a xtyp_info_tuple \<Rightarrow> 'a field_desc list"
where
  tfd0: "toplevel_field_descs (TypDesc algn st nm) = toplevel_field_descs_struct st"

| tfd1: "toplevel_field_descs_struct (TypScalar n algn d) = [d]"
| tfd2: "toplevel_field_descs_struct (TypAggregate xs) = toplevel_field_descs_list xs"

| tfd3: "toplevel_field_descs_list [] = []"
| tfd4: "toplevel_field_descs_list (x#xs) = toplevel_field_descs_tuple x @ toplevel_field_descs_list xs"

| tfd5: "toplevel_field_descs_tuple (DTuple t nm d) = [d]"

locale padding_base =
  fixes acc::"'a \<Rightarrow> byte list \<Rightarrow> byte list"
  fixes upd:: "byte list \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes sz::nat
begin
  definition eq_padding::"byte list \<Rightarrow> byte list \<Rightarrow> bool" where
    "eq_padding bs bs' \<equiv> length bs = sz \<and> length bs' = sz \<and> (\<forall>v. acc v bs = acc v bs')"
  definition eq_upto_padding::"byte list \<Rightarrow> byte list \<Rightarrow> bool" where
    "eq_upto_padding bs bs' \<equiv> length bs = sz \<and> length bs' = sz \<and> (\<forall>v. upd bs v = upd bs' v)"


definition is_padding_byte::"nat \<Rightarrow> bool" where
    "is_padding_byte i \<equiv> i < sz \<and> (\<forall>v bs. length bs = sz \<longrightarrow>
          (acc v bs ! i  = bs ! i) \<and>
          (\<forall>b. upd bs v = upd (bs[i:=b]) v))"


definition is_value_byte::"nat \<Rightarrow> bool" where
    "is_value_byte i \<equiv> i < sz \<and> (\<forall>v bs. length bs = sz \<longrightarrow>
       (\<forall>bs'. length bs' = sz \<longrightarrow> (acc (upd bs v) bs' ! i) = bs ! i) \<and>
       (\<forall>b. acc v bs = acc v (bs[i:=b])))"

lemma is_padding_byteI:
  assumes "i < sz"
  assumes "\<And>v bs. i < sz \<Longrightarrow> length bs = sz \<Longrightarrow> acc v bs ! i = bs ! i"
  assumes "\<And>v bs b. i < sz \<Longrightarrow> length bs = sz \<Longrightarrow> upd bs v = upd (bs[i:=b]) v"
  shows "is_padding_byte i"
  using assms
  by  (simp add: is_padding_byte_def)

lemma is_value_byteI:
  assumes "i < sz"
  assumes "\<And>v bs bs'. i < sz \<Longrightarrow> length bs = sz \<Longrightarrow> length bs' = sz \<Longrightarrow>
              (acc (upd bs v) bs' ! i) = bs ! i"
  assumes "\<And>v bs b. i < sz \<Longrightarrow> length bs = sz \<Longrightarrow> acc v bs = acc v (bs[i:=b])"
  shows "is_value_byte i"
  using assms
  by  (simp add: is_value_byte_def)

lemma is_padding_byte_acc_id: "
    is_padding_byte i \<Longrightarrow> length bs = sz \<Longrightarrow> (acc v bs ! i) = bs ! i"
  by (simp add: is_padding_byte_def)

lemma is_value_byte_acc_upd_cancel: "
    is_value_byte i \<Longrightarrow> length bs = sz \<Longrightarrow> length bs' = sz \<Longrightarrow>
      (acc (upd bs v) bs' ! i) = bs ! i"
  by (simp add: is_value_byte_def)

lemma is_padding_byte_eq_upto_padding: "is_padding_byte i \<Longrightarrow> length bs = sz \<Longrightarrow> eq_upto_padding bs (bs[i:=b])"
  by (simp add: eq_upto_padding_def is_padding_byte_def)

lemma is_value_byte_eq_padding: "is_value_byte i \<Longrightarrow> length bs = sz \<Longrightarrow> eq_padding bs (bs[i:=b])"
  by (simp add: eq_padding_def is_value_byte_def)

lemma is_padding_byte_acc_neq:
  "is_padding_byte i \<Longrightarrow> b \<noteq> bs!i \<Longrightarrow> length bs = sz \<Longrightarrow> acc v bs \<noteq> acc v (bs[i:=b])"
  by (metis is_padding_byte_def length_list_update nth_list_update_eq)

lemma is_padding_byte_acc_eq:
  "is_padding_byte i \<Longrightarrow> length bs = sz  \<Longrightarrow>
         acc v bs ! i  = bs ! i"
  by (auto simp add: is_padding_byte_def)

lemma is_padding_byte_upd_eq:
  "is_padding_byte i \<Longrightarrow> length bs = sz \<Longrightarrow> upd bs v = upd (bs[i:=b]) v"
  by (auto simp add: is_padding_byte_def)

lemma is_padding_byte_not_eq_padding: "is_padding_byte i \<Longrightarrow> b \<noteq> bs!i \<Longrightarrow> length bs = sz \<Longrightarrow>  \<not> eq_padding bs (bs[i:=b])"
  by (simp add: padding_base.eq_padding_def padding_base.is_padding_byte_acc_neq)


lemma is_value_byte_upd_neq:
  "is_value_byte i \<Longrightarrow> b \<noteq> bs!i \<Longrightarrow> length bs = sz \<Longrightarrow> upd bs v \<noteq> upd (bs[i:=b]) v"
  by (metis length_list_update nth_list_update_eq is_value_byte_def)

lemma is_value_byte_update_depends:
  assumes is_value: "is_value_byte i"
  assumes lbs: "length bs = sz"
  shows "\<exists>b. upd (bs[i := b]) v \<noteq> upd bs v"
proof -
  obtain b where "b \<noteq> bs!i"
    by (metis len8 len_gt_0 less_le word_power_less_1)
  from is_value_byte_upd_neq [OF is_value this lbs, of v] show ?thesis by metis
qed

lemma is_value_byte_acc_eq:
  "is_value_byte i \<Longrightarrow> length bs = sz \<Longrightarrow> acc v bs = acc v (bs[i:=b])"
  by (auto simp add: is_value_byte_def)

lemma is_value_byte_not_eq_upto_padding:
  "is_value_byte i \<Longrightarrow> b \<noteq> bs!i \<Longrightarrow> length bs = sz \<Longrightarrow>  \<not> eq_upto_padding bs (bs[i:=b])"
  by (simp add: padding_base.eq_upto_padding_def padding_base.is_value_byte_upd_neq)



lemma eq_paddingI[intro?]:
  assumes "length bs = sz"
  assumes "length bs' = sz"
  assumes "\<And>v. acc v bs = acc v bs'"
  shows "eq_padding bs bs'"
  using assms by (auto simp add: eq_padding_def)

lemma eq_upto_paddingI[intro?]:
  assumes "length bs = sz"
  assumes "length bs' = sz"
  assumes "\<And>v. upd bs v = upd bs' v"
  shows "eq_upto_padding bs bs'"
  using assms by (auto simp add: eq_upto_padding_def)

lemma eq_padding_length1: "eq_padding bs bs' \<Longrightarrow> length bs = sz"
  by (simp add: eq_padding_def)

lemma eq_padding_length2: "eq_padding bs bs' \<Longrightarrow> length bs' = sz"
  by (simp add: eq_padding_def)

lemma eq_upto_padding_length1: "eq_upto_padding bs bs' \<Longrightarrow> length bs = sz"
  by (simp add: eq_upto_padding_def)

lemma eq_upto_padding_length2: "eq_upto_padding bs bs' \<Longrightarrow> length bs' = sz"
  by (simp add: eq_upto_padding_def)

lemma eq_padding_length_eq: "eq_padding bs bs' \<Longrightarrow> length bs = length bs'"
  by (simp add: eq_padding_def)

lemma eq_upto_padding_length_eq: "eq_upto_padding bs bs' \<Longrightarrow> length bs = length bs'"
  by (simp add: eq_upto_padding_def)

lemma eq_padding_acc: "eq_padding bs bs' \<Longrightarrow> acc v bs = acc v bs'"
  by (simp add: eq_padding_def)

lemma eq_upto_padding_upd: "eq_upto_padding bs bs' \<Longrightarrow> upd bs v = upd bs' v"
  by (simp add: eq_upto_padding_def)

lemma eq_padding_refl[simp]: "length bs = sz \<Longrightarrow> eq_padding bs bs"
  by (simp add: eq_padding_def)

lemma eq_upto_padding_refl[simp]: "length bs = sz \<Longrightarrow> eq_upto_padding bs bs"
  by (simp add: eq_upto_padding_def)

lemma eq_padding_sym: "eq_padding bs bs' \<longleftrightarrow> eq_padding bs' bs"
  by (auto simp add: eq_padding_def)

lemma eq_padding_symp: "symp eq_padding"
  by (simp add: symp_def eq_padding_sym)

lemma eq_upto_padding_sym: "eq_upto_padding bs bs' \<longleftrightarrow> eq_upto_padding bs' bs"
  by (auto simp add: eq_upto_padding_def)

lemma eq_upto_padding_symp: "symp eq_upto_padding"
  by (simp add: symp_def eq_upto_padding_sym)

lemma eq_padding_trans: "eq_padding bs1 bs2 \<Longrightarrow> eq_padding bs2 bs3 \<Longrightarrow> eq_padding bs1 bs3"
  by (auto simp add: eq_padding_def)

lemma eq_padding_transp: "transp eq_padding"
  unfolding transp_def
  by (auto intro: eq_padding_trans)

lemma eq_upto_padding_trans: "eq_upto_padding bs1 bs2 \<Longrightarrow> eq_upto_padding bs2 bs3 \<Longrightarrow> eq_upto_padding bs1 bs3"
  by (auto simp add: eq_upto_padding_def)

lemma eq_upto_padding_transp: "transp eq_upto_padding"
  unfolding transp_def
  by (auto intro: eq_upto_padding_trans)

lemma eq_padding_to_padding_byte_eq: "eq_padding bs bs' \<Longrightarrow>
  length bs = sz \<and> length bs' = sz \<and>  (\<forall>i. is_padding_byte i \<longrightarrow> bs ! i = bs' ! i)"
  by (metis is_padding_byte_acc_id padding_base.eq_padding_def)

lemma eq_upto_padding_to_value_byte_eq: "eq_upto_padding bs bs' \<Longrightarrow>
  length bs = sz \<and> length bs' = sz \<and>  (\<forall>i. is_value_byte i \<longrightarrow> bs ! i = bs' ! i)"
  by (metis (no_types, opaque_lifting) is_value_byte_acc_upd_cancel local.eq_upto_padding_def)


end

locale complement_padding = padding_base +
  assumes complement: "i < sz \<Longrightarrow>
    is_padding_byte i \<noteq> is_value_byte i"
begin


lemma eq_padding_eq_upto_padding_complement:
  assumes lbs: "length bs = sz"
  assumes i_bound: "i < length bs"
  assumes neq: "b \<noteq> bs!i"
  shows "eq_padding bs (bs[i := b]) \<noteq> eq_upto_padding bs (bs[i := b])"
  by (metis (no_types, opaque_lifting) complement i_bound lbs length_list_update neq padding_base.eq_paddingI
   padding_base.eq_upto_padding_def padding_base.is_padding_byte_not_eq_padding
   padding_base.is_padding_byte_upd_eq padding_base.is_value_byte_acc_eq padding_base.is_value_byte_not_eq_upto_padding)


lemma eq_padding_padding_byte_id:
  assumes eq_padding: "eq_padding bs bs'"
  assumes is_padding: "is_padding_byte i"
  shows "bs!i = bs'!i"
  by (metis eq_padding is_padding is_padding_byte_acc_id padding_base.eq_padding_def)



lemma eq_upto_padding_value_byte_id:
  assumes eq_padding: "eq_upto_padding bs bs'"
  assumes is_value: "is_value_byte i"
  shows "bs!i = bs'!i"
  by (metis (no_types, opaque_lifting) eq_padding eq_upto_padding_length1
      eq_upto_padding_length2 eq_upto_padding_upd is_value is_value_byte_acc_upd_cancel)


lemma eq_upto_padding_neq_is_padding_byte:
  assumes eq_upto_padding: "eq_upto_padding bs bs'"
  assumes i_bound: "i < length bs"
  assumes neq: "bs!i \<noteq> bs'!i"
  shows "is_padding_byte i"
  by (metis eq_upto_padding eq_upto_padding_value_byte_id i_bound neq
      complement_padding.complement complement_padding_axioms padding_base.eq_upto_padding_length2 padding_base.eq_upto_padding_length_eq)

lemma eq_padding_neq_is_value_byte:
  assumes eq_upto_padding: "eq_padding bs bs'"
  assumes i_bound: "i < length bs"
  assumes neq: "bs!i \<noteq> bs'!i"
  shows "is_value_byte i"
  by (metis complement eq_padding_padding_byte_id eq_upto_padding i_bound
      neq padding_base.eq_padding_length2 padding_base.eq_padding_length_eq)

lemma padding_eq_complement:
  assumes eq_padding: "eq_padding bs bs'"
  assumes eq_upto_padding: "eq_upto_padding bs bs'"
  shows "bs = bs'"
  by (meson eq_padding eq_padding_padding_byte_id eq_upto_padding eq_upto_padding_length_eq
      eq_upto_padding_neq_is_padding_byte nth_equalityI)

end

locale padding_lense = complement_padding +
  assumes double_update: "upd bs (upd bs' s) = upd bs s"
  assumes access_update: "acc (upd bs s) bs' = acc (upd bs s') bs'"
  assumes update_access: "upd (acc s bs) s = s"
  assumes access_size: "acc s (take sz bs) = acc s bs"
  assumes access_result_size: "length (acc s bs) = sz"
  assumes update_size: "upd (take sz bs) = upd bs"
begin

lemma update_size_ext: "upd (take sz bs) s = upd bs s"
  by (simp add: update_size)

lemma update_access_append: "upd ((acc s bs)@bs') s = s" (is "?lhs = ?rhs")
proof -
  have "?lhs = upd (take sz ((acc s bs)@bs')) s"
    by (rule update_size_ext [symmetric])
  also
  from access_result_size
  have "take sz ((acc s bs)@bs') = acc s bs"
    by auto
  also note update_access
  finally show ?thesis .
qed


lemma field_access_eq_padding1: "length bs = sz \<Longrightarrow> eq_padding (acc v bs) bs"
  apply (rule eq_paddingI)
    apply (simp add: access_result_size)
   apply simp
  by (smt (verit) complement is_padding_byte_acc_id is_value_byte_acc_upd_cancel
      nth_equalityI access_result_size update_access padding_lense_axioms)

lemma field_access_eq_padding2: "length bs = sz \<Longrightarrow> eq_padding (acc v2 bs) (acc v2 bs)"
  apply (rule eq_paddingI)
    apply (simp_all add: access_result_size)
  done


lemma field_access_eq_upto_padding: "length bs = sz \<Longrightarrow> length bs = sz \<Longrightarrow>
  eq_upto_padding (acc v bs) (acc v bs')"
  apply (rule eq_upto_paddingI)
    apply (simp add: access_result_size)
  apply (simp add: access_result_size)
  by (metis access_update double_update update_access)

lemma padding_byte_to_eq_padding_eq:
  "eq_padding bs bs'"
  if
    "length bs = sz"
    "length bs' = sz"
    "(\<forall>i. is_padding_byte i \<longrightarrow> bs ! i = bs' ! i)"
  using that(1,2)
  apply (rule eq_paddingI)
  apply (rule nth_equalityI)
  unfolding access_result_size
  apply (rule refl)
  by (metis access_result_size complement is_padding_byte_acc_id is_value_byte_acc_upd_cancel that
      update_access)

lemma eq_padding_is_padding_byte_conv:
"eq_padding bs bs' \<longleftrightarrow> length bs = sz \<and> length bs' = sz \<and>  (\<forall>i. is_padding_byte i \<longrightarrow> bs ! i = bs' ! i)"
  using eq_padding_to_padding_byte_eq padding_byte_to_eq_padding_eq by blast

lemma value_byte_to_eq_upto_padding_eq:
  assumes lbs: "length bs = sz"
  assumes lbs': "length bs' = sz"
  assumes is_value: "\<forall>i. is_value_byte i \<longrightarrow> bs ! i = bs' ! i"
  shows "eq_upto_padding bs bs'"
proof (rule eq_upto_paddingI [OF lbs lbs'])
  fix v
  have leq: "length (acc (upd bs' v) bs) = sz"
    by (simp add: access_result_size)
  then have "acc (upd bs' v) bs = bs"
    by (smt (verit) eq_padding_neq_is_value_byte field_access_eq_padding1
        is_value is_value_byte_acc_upd_cancel lbs lbs' nth_equalityI)
  then
  show "upd bs v = upd bs' v"
    by (metis double_update update_access)
qed

lemma eq_upto_padding_is_value_byte_conv:
"eq_upto_padding bs bs' \<longleftrightarrow> length bs = sz \<and> length bs' = sz \<and>  (\<forall>i. is_value_byte i \<longrightarrow> bs ! i = bs' ! i)"
  using eq_upto_padding_to_value_byte_eq value_byte_to_eq_upto_padding_eq by blast

end

locale wf_field_desc = padding_lense "(field_access d)" "(field_update d)" "(field_sz d)" for d::"'a field_desc"

locale field_desc_independent =
  fixes
    acc::"'a \<Rightarrow> byte list \<Rightarrow> byte list" and
    upd::"byte list \<Rightarrow> 'a \<Rightarrow> 'a" and
    D:: "'a field_desc set"
  assumes fu_commutes: "d \<in> D \<Longrightarrow> fu_commutes upd (field_update d)"
  assumes acc_upd_old: "d \<in> D \<Longrightarrow> acc (field_update d bs v) bs' = acc v bs'"
  assumes acc_upd_new: "d \<in> D \<Longrightarrow> field_access d (upd bs' v) bs = field_access d v bs"

primrec
  field_descs :: "'a xtyp_info \<Rightarrow> 'a field_desc list" and
  field_descs_struct :: "'a xtyp_info_struct \<Rightarrow> 'a field_desc list" and
  field_descs_list :: "'a xtyp_info_tuple list \<Rightarrow> 'a field_desc list" and
  field_descs_tuple :: "'a xtyp_info_tuple \<Rightarrow> 'a field_desc list"
where
  fd0: "field_descs (TypDesc algn st nm) = field_descs_struct st"

| fd1: "field_descs_struct (TypScalar n algn d) = [d]"
| fd2: "field_descs_struct (TypAggregate xs) = field_descs_list xs"

| fd3: "field_descs_list [] = []"
| fd4: "field_descs_list (x#xs) = field_descs_tuple x @ field_descs_list xs"

| fd5: "field_descs_tuple (DTuple t nm d) = [d] @ field_descs t"

primrec
  wf_component_descs :: "'a xtyp_info \<Rightarrow> bool" and
  wf_component_descs_struct :: "'a xtyp_info_struct \<Rightarrow> bool" and
  wf_component_descs_list :: "'a xtyp_info_tuple list \<Rightarrow> bool" and
  wf_component_descs_tuple :: "'a xtyp_info_tuple \<Rightarrow> bool"
where
  wfc0: "wf_component_descs (TypDesc algn st nm) = wf_component_descs_struct st"

| wfc1: "wf_component_descs_struct (TypScalar n algn d) = (n = field_sz d)"
| wfc2: "wf_component_descs_struct (TypAggregate xs) = (wf_component_descs_list xs)"

| wfc3: "wf_component_descs_list [] = True"
| wfc4: "wf_component_descs_list (x#xs) = (wf_component_descs_tuple x \<and> wf_component_descs_list xs)"

| wfc5: "wf_component_descs_tuple (DTuple t nm d) =
          (d = component_desc t  \<and> wf_component_descs t)"

primrec field_descs_independent:: "'a field_desc list \<Rightarrow> bool"
  where
"field_descs_independent [] = True" |
"field_descs_independent (d#ds) =
   (field_desc_independent (field_access d) (field_update d) (set ds) \<and>
    field_descs_independent ds)"

primrec
  component_descs_independent :: "'a xtyp_info \<Rightarrow> bool" and
  component_descs_independent_struct :: "'a xtyp_info_struct \<Rightarrow> bool" and
  component_descs_independent_list :: "'a xtyp_info_tuple list \<Rightarrow> bool" and
  component_descs_independent_tuple :: "'a xtyp_info_tuple \<Rightarrow> bool"
where
  cdi0: "component_descs_independent (TypDesc algn st nm) = component_descs_independent_struct st"

| cdi1: "component_descs_independent_struct (TypScalar n algn d) = True"
| cdi2: "component_descs_independent_struct (TypAggregate xs) = (component_descs_independent_list xs)"

| cdi3: "component_descs_independent_list [] = True"
| cdi4: "component_descs_independent_list (f#fs) = (field_descs_independent (toplevel_field_descs_list (f#fs)) \<and>
          component_descs_independent_tuple f \<and> component_descs_independent_list fs)"

| cdi5: "component_descs_independent_tuple (DTuple ft fn d) =  (component_descs_independent ft)"

locale wf_field_descs =
  fixes D::"'a field_desc set"
  assumes wf_desc[intro]: "d \<in> D \<Longrightarrow> wf_field_desc d"

lemma wf_field_descs_union [simp]: "wf_field_descs (D \<union> E) = (wf_field_descs D \<and> wf_field_descs E)"
  by (auto simp add: wf_field_descs_def)

lemma wf_field_descs_empty[simp]: "wf_field_descs {}"
  by (simp add: wf_field_descs_def)

lemma wf_field_descs_insert [simp]: "wf_field_descs (insert d D) = (wf_field_desc d \<and> wf_field_descs D)"
  by (auto simp add: wf_field_descs_def)


definition padding_desc:: "nat \<Rightarrow> 'a field_desc" where
  "padding_desc n = \<lparr>field_access = \<lambda>v bs.  if n \<le> length bs then take n bs else replicate n 0, field_update = \<lambda>bs. id, field_sz = n\<rparr>"

definition "is_padding_desc d = (\<exists>n. d = padding_desc n)"

definition "padding_tag n = TypDesc 0 (TypScalar n 0 (padding_desc n)) ''!pad_typ''"

definition "is_padding_tag t = (\<exists>n. t = padding_tag n)"

definition "padding_field_name f = (\<exists>xs. f = CHR ''!'' # xs)"

lemma padding_field_name_empty[simp]: "padding_field_name [] = False"
  by (simp add: padding_field_name_def)

lemma padding_field_name_cons[simp]: "padding_field_name (f#fs) = (f = CHR ''!'')"
  by (simp add: padding_field_name_def)

definition "qualified_padding_field_name fs = (\<exists>f fs'. fs= f#fs' \<and> padding_field_name (last fs))"

lemma qualified_pading_field_name_empty[simp]: "qualified_padding_field_name [] = False"
  by (simp add: qualified_padding_field_name_def)

lemma qualified_pading_field_name_single[simp]: "qualified_padding_field_name [f] = padding_field_name f"
  by (simp add: qualified_padding_field_name_def)

lemma qualified_pading_field_name_cons[simp]: "qualified_padding_field_name (f#fs) = padding_field_name (last (f#fs))"
  by (simp add: qualified_padding_field_name_def)


primrec
  wf_padding :: "('a, 'b) typ_info \<Rightarrow> bool" and
  wf_padding_struct :: "('a, 'b) typ_info_struct \<Rightarrow> bool" and
  wf_padding_list :: "('a, 'b) typ_info_tuple list \<Rightarrow> bool" and
  wf_padding_tuple :: "('a, 'b) typ_info_tuple \<Rightarrow> bool"
where
   "wf_padding (TypDesc algn st nm) = wf_padding_struct st"

| "wf_padding_struct (TypScalar m algn d) = True"
| "wf_padding_struct (TypAggregate xs) = wf_padding_list xs"

| "wf_padding_list [] = True"
| "wf_padding_list (x#xs) = (wf_padding_tuple x \<and> wf_padding_list xs)"

| "wf_padding_tuple (DTuple s f d) = ((padding_field_name f \<longrightarrow> is_padding_tag s) \<and> wf_padding s)"



class xmem_type = mem_type +
  assumes wf_component_descs: "wf_component_descs (typ_info_t TYPE('a))"
  assumes component_descs_independent: "component_descs_independent (typ_info_t TYPE('a))"
  assumes wf_field_descs: "wf_field_descs (set (field_descs (typ_info_t TYPE('a))))"
  assumes wf_padding: "wf_padding (typ_info_t TYPE('a))"



locale fields_contained =
  fixes
    acc::"'a \<Rightarrow> byte list \<Rightarrow> byte list" and
    upd::"byte list \<Rightarrow> 'a \<Rightarrow> 'a" and
    D:: "'a field_desc set"
  assumes access_contained: "d \<in> D \<Longrightarrow> acc s = acc s' \<Longrightarrow> field_access d s = field_access d s'"
  assumes update_contained: "d \<in> D \<Longrightarrow> \<exists>bs'. \<forall>s'. acc s' = acc s \<longrightarrow> field_update d bs s' = upd bs' s'"


primrec
  contained_field_descs :: "'a xtyp_info \<Rightarrow> bool" and
  contained_field_descs_struct :: "'a xtyp_info_struct \<Rightarrow> bool" and
  contained_field_descs_list :: "'a xtyp_info_tuple list \<Rightarrow> bool" and
  contained_field_descs_tuple :: "'a xtyp_info_tuple \<Rightarrow> bool"
where
  wfd0: "contained_field_descs (TypDesc algn st nm) = contained_field_descs_struct st"

| wfd1: "contained_field_descs_struct (TypScalar n algn d) = True"
| wfd2: "contained_field_descs_struct (TypAggregate xs) = contained_field_descs_list xs"

| wfd3: "contained_field_descs_list [] = True"
| wfd4: "contained_field_descs_list (x#xs) = (contained_field_descs_tuple x \<and> contained_field_descs_list xs)"

| wfd5: "contained_field_descs_tuple (DTuple t nm d) =
   (contained_field_descs t \<and>
   fields_contained (field_access d) (field_update d) (set (toplevel_field_descs t)))"

class xmem_contained_type = xmem_type +
  assumes contained_field_descs: "contained_field_descs (typ_info_t (TYPE('a)))"

text \<open>In order to construct a type of class @{class mem_type} we usually construct extended type-info for
class @{class xmem_contained_type}. The extendend type-info is better behaved with respect to
composition of sub-structures / arrays.
\<close>
end
