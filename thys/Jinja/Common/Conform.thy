(*  Title:      Jinja/J/Conform.thy

    Author:     David von Oheimb, Tobias Nipkow
    Copyright   1999 Technische Universitaet Muenchen
*)

section \<open>Conformance Relations for Type Soundness Proofs\<close>

theory Conform
imports Exceptions
begin

definition conf :: "'m prog \<Rightarrow> heap \<Rightarrow> val \<Rightarrow> ty \<Rightarrow> bool"   (\<open>_,_ \<turnstile> _ :\<le> _\<close>  [51,51,51,51] 50)
where
  "P,h \<turnstile> v :\<le> T  \<equiv>
  \<exists>T'. typeof\<^bsub>h\<^esub> v = Some T' \<and> P \<turnstile> T' \<le> T"

definition oconf :: "'m prog \<Rightarrow> heap \<Rightarrow> obj \<Rightarrow> bool"   (\<open>_,_ \<turnstile> _ \<surd>\<close> [51,51,51] 50)
where
  "P,h \<turnstile> obj \<surd>  \<equiv>
  let (C,fs) = obj in \<forall>F D T. P \<turnstile> C has F:T in D \<longrightarrow>
  (\<exists>v. fs(F,D) = Some v \<and> P,h \<turnstile> v :\<le> T)"

definition hconf :: "'m prog \<Rightarrow> heap \<Rightarrow> bool"  (\<open>_ \<turnstile> _ \<surd>\<close> [51,51] 50)
where
  "P \<turnstile> h \<surd>  \<equiv>
  (\<forall>a obj. h a = Some obj \<longrightarrow> P,h \<turnstile> obj \<surd>) \<and> preallocated h"

definition lconf :: "'m prog \<Rightarrow> heap \<Rightarrow> (vname \<rightharpoonup> val) \<Rightarrow> (vname \<rightharpoonup> ty) \<Rightarrow> bool"   (\<open>_,_ \<turnstile> _ '(:\<le>') _\<close> [51,51,51,51] 50)
where
  "P,h \<turnstile> l (:\<le>) E  \<equiv>
  \<forall>V v. l V = Some v \<longrightarrow> (\<exists>T. E V = Some T \<and> P,h \<turnstile> v :\<le> T)"

abbreviation
  confs :: "'m prog \<Rightarrow> heap \<Rightarrow> val list \<Rightarrow> ty list \<Rightarrow> bool" 
             (\<open>_,_ \<turnstile> _ [:\<le>] _\<close> [51,51,51,51] 50) where
  "P,h \<turnstile> vs [:\<le>] Ts \<equiv> list_all2 (conf P h) vs Ts"


subsection\<open>Value conformance \<open>:\<le>\<close>\<close>

lemma conf_Null [simp]: "P,h \<turnstile> Null :\<le> T  =  P \<turnstile> NT \<le> T"
(*<*)by (simp (no_asm) add: conf_def)(*>*)

lemma typeof_conf[simp]: "typeof\<^bsub>h\<^esub> v = Some T \<Longrightarrow> P,h \<turnstile> v :\<le> T"
(*<*)by (induct v) (auto simp: conf_def)(*>*)

lemma typeof_lit_conf[simp]: "typeof v = Some T \<Longrightarrow> P,h \<turnstile> v :\<le> T"
(*<*)by (rule typeof_conf[OF typeof_lit_typeof])(*>*)

lemma defval_conf[simp]: "P,h \<turnstile> default_val T :\<le> T"
(*<*)by (cases T) (auto simp: conf_def)(*>*)

lemma conf_upd_obj: "h a = Some(C,fs) \<Longrightarrow> (P,h(a\<mapsto>(C,fs')) \<turnstile> x :\<le> T) = (P,h \<turnstile> x :\<le> T)"
(*<*)by (rule val.induct) (auto simp:conf_def fun_upd_apply)(*>*)

lemma conf_widen: "P,h \<turnstile> v :\<le> T \<Longrightarrow> P \<turnstile> T \<le> T' \<Longrightarrow> P,h \<turnstile> v :\<le> T'"
(*<*)by (induct v) (auto intro: widen_trans simp: conf_def)(*>*)

lemma conf_hext: "h \<unlhd> h' \<Longrightarrow> P,h \<turnstile> v :\<le> T \<Longrightarrow> P,h' \<turnstile> v :\<le> T"
(*<*)by (induct v) (auto dest: hext_objD simp: conf_def)(*>*)

lemma conf_ClassD: "P,h \<turnstile> v :\<le> Class C \<Longrightarrow>
  v = Null \<or> (\<exists>a obj T. v = Addr a \<and>  h a = Some obj \<and> obj_ty obj = T \<and>  P \<turnstile> T \<le> Class C)"
(*<*)by(induct v) (auto simp: conf_def)(*>*)

lemma conf_NT [iff]: "P,h \<turnstile> v :\<le> NT = (v = Null)"
(*<*)by (auto simp add: conf_def)(*>*)

lemma non_npD: "\<lbrakk> v \<noteq> Null; P,h \<turnstile> v :\<le> Class C \<rbrakk>
  \<Longrightarrow> \<exists>a C' fs. v = Addr a \<and> h a = Some(C',fs) \<and> P \<turnstile> C' \<preceq>\<^sup>* C"
(*<*)by (auto dest: conf_ClassD)(*>*)


subsection\<open>Value list conformance \<open>[:\<le>]\<close>\<close>

lemma confs_widens [trans]: "\<lbrakk>P,h \<turnstile> vs [:\<le>] Ts; P \<turnstile> Ts [\<le>] Ts'\<rbrakk> \<Longrightarrow> P,h \<turnstile> vs [:\<le>] Ts'"
(*<*)by(auto intro: list_all2_trans conf_widen)(*>*)

lemma confs_rev: "P,h \<turnstile> rev s [:\<le>] t = (P,h \<turnstile> s [:\<le>] rev t)"
(*<*)by (simp add: list_all2_rev1)(*>*)

lemma confs_conv_map:
  "\<And>Ts'. P,h \<turnstile> vs [:\<le>] Ts' = (\<exists>Ts. map typeof\<^bsub>h\<^esub> vs = map Some Ts \<and> P \<turnstile> Ts [\<le>] Ts')"
(*<*)
proof(induct vs)
  case (Cons a vs)
  then show ?case by(case_tac Ts') (auto simp add:conf_def)
qed simp
(*>*)

lemma confs_hext: "P,h \<turnstile> vs [:\<le>] Ts \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> P,h' \<turnstile> vs [:\<le>] Ts"
(*<*)by (erule list_all2_mono, erule conf_hext, assumption)(*>*)

lemma confs_Cons2: "P,h \<turnstile> xs [:\<le>] y#ys = (\<exists>z zs. xs = z#zs \<and> P,h \<turnstile> z :\<le> y \<and> P,h \<turnstile> zs [:\<le>] ys)"
(*<*)by (rule list_all2_Cons2)(*>*)


subsection "Object conformance"

lemma oconf_hext: "P,h \<turnstile> obj \<surd> \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> P,h' \<turnstile> obj \<surd>"
(*<*)by (fastforce elim:conf_hext simp: oconf_def)(*>*)

lemma oconf_init_fields:
 "P \<turnstile> C has_fields FDTs \<Longrightarrow> P,h \<turnstile> (C, init_fields FDTs) \<surd>"
by(fastforce simp add: has_field_def oconf_def init_fields_def map_of_map
            dest: has_fields_fun)

lemma oconf_fupd [intro?]:
  "\<lbrakk> P \<turnstile> C has F:T in D; P,h \<turnstile> v :\<le> T; P,h \<turnstile> (C,fs) \<surd> \<rbrakk> 
  \<Longrightarrow> P,h \<turnstile> (C, fs((F,D)\<mapsto>v)) \<surd>"
(*<*)by (auto dest: has_fields_fun simp add: oconf_def has_field_def fun_upd_apply)(*>*)

(*<*)
lemmas oconf_new = oconf_hext [OF _ hext_new]
lemmas oconf_upd_obj = oconf_hext [OF _ hext_upd_obj]
(*>*)

subsection "Heap conformance"

lemma hconfD: "\<lbrakk> P \<turnstile> h \<surd>; h a = Some obj \<rbrakk> \<Longrightarrow> P,h \<turnstile> obj \<surd>"
(*<*)by (unfold hconf_def) fast(*>*)

lemma hconf_new: "\<lbrakk> P \<turnstile> h \<surd>; h a = None; P,h \<turnstile> obj \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> h(a\<mapsto>obj) \<surd>"
(*<*)by (unfold hconf_def) (auto intro: oconf_new preallocated_new)(*>*)

lemma hconf_upd_obj: "\<lbrakk> P \<turnstile> h\<surd>; h a = Some(C,fs); P,h \<turnstile> (C,fs')\<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> h(a\<mapsto>(C,fs'))\<surd>"
(*<*)by (unfold hconf_def) (auto intro: oconf_upd_obj preallocated_upd_obj)(*>*)


subsection "Local variable conformance"

lemma lconf_hext: "\<lbrakk> P,h \<turnstile> l (:\<le>) E; h \<unlhd> h' \<rbrakk> \<Longrightarrow> P,h' \<turnstile> l (:\<le>) E"
(*<*)by (unfold lconf_def) (fast elim: conf_hext)(*>*)

lemma lconf_upd:
  "\<lbrakk> P,h \<turnstile> l (:\<le>) E; P,h \<turnstile> v :\<le> T; E V = Some T \<rbrakk> \<Longrightarrow> P,h \<turnstile> l(V\<mapsto>v) (:\<le>) E"
(*<*)by (unfold lconf_def) auto(*>*)

lemma lconf_empty[iff]: "P,h \<turnstile> Map.empty (:\<le>) E"
(*<*)by(simp add:lconf_def)(*>*)

lemma lconf_upd2: "\<lbrakk>P,h \<turnstile> l (:\<le>) E; P,h \<turnstile> v :\<le> T\<rbrakk> \<Longrightarrow> P,h \<turnstile> l(V\<mapsto>v) (:\<le>) E(V\<mapsto>T)"
(*<*)by(simp add:lconf_def)(*>*)


end
