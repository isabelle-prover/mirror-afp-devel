(*  Title:      JinjaThreads/Common/Conform.thy
    Author:     David von Oheimb, Tobias Nipkow, Andreas Lochbihler

    Based on the Jinja theory Common/Conform.thy by David von Oheimb and Tobias Nipkow
*)

header {* \isaheader{Conformance Relations for Type Soundness Proofs} *}

theory Conform
imports Exceptions
begin

constdefs
  conf :: "'m prog \<Rightarrow> heap \<Rightarrow> val \<Rightarrow> ty \<Rightarrow> bool"   ("_,_ \<turnstile> _ :\<le> _"  [51,51,51,51] 50)
  "P,h \<turnstile> v :\<le> T  \<equiv>
  \<exists>T'. typeof\<^bsub>h\<^esub> v = Some T' \<and> P \<turnstile> T' \<le> T"

  oconf :: "'m prog \<Rightarrow> heap \<Rightarrow> heapobj \<Rightarrow> bool"   ("_,_ \<turnstile> _ \<surd>" [51,51,51] 50)
  "P,h \<turnstile> obj \<surd>  \<equiv> (case obj of Obj C fs    \<Rightarrow> is_class P C \<and> (\<forall>F D T. P \<turnstile> C has F:T in D \<longrightarrow> (\<exists>v. fs(F,D) = Some v \<and> P,h \<turnstile> v :\<le> T))
                             | Arr T si el \<Rightarrow> is_type P T \<and> (\<forall>idx. 0 \<le> idx \<and> idx < si \<longrightarrow> P,h \<turnstile> el idx :\<le> T))"

  hconf :: "'m prog \<Rightarrow> heap \<Rightarrow> bool"  ("_ \<turnstile> _ \<surd>" [51,51] 50)
  "P \<turnstile> h \<surd>  \<equiv>
  (\<forall>a obj. h a = Some obj \<longrightarrow> P,h \<turnstile> obj \<surd>) \<and> preallocated h"

  lconf :: "'m prog \<Rightarrow> heap \<Rightarrow> (vname \<rightharpoonup> val) \<Rightarrow> (vname \<rightharpoonup> ty) \<Rightarrow> bool"   ("_,_ \<turnstile> _ '(:\<le>') _" [51,51,51,51] 50)
  "P,h \<turnstile> l (:\<le>) E  \<equiv>
  \<forall>V v. l V = Some v \<longrightarrow> (\<exists>T. E V = Some T \<and> P,h \<turnstile> v :\<le> T)"

(*<*)

abbreviation
  confs :: "'m prog \<Rightarrow> heap \<Rightarrow> val list \<Rightarrow> ty list \<Rightarrow> bool" ("_,_ \<turnstile> _ [:\<le>] _" [51,51,51,51] 50)
where
  "P,h \<turnstile> vs [:\<le>] Ts  ==  list_all2 (conf P h) vs Ts"


section{* Value conformance @{text":\<le>"} *}

lemma conf_Null [simp]: "P,h \<turnstile> Null :\<le> T  =  P \<turnstile> NT \<le> T"
(*<*)
apply (unfold conf_def)
apply (simp (no_asm))
done
(*>*)

lemma typeof_conf[simp]: "typeof\<^bsub>h\<^esub> v = Some T \<Longrightarrow> P,h \<turnstile> v :\<le> T"
(*<*)
apply (unfold conf_def)
apply (induct v)
apply auto
done
(*>*)

lemma typeof_lit_conf[simp]: "typeof v = Some T \<Longrightarrow> P,h \<turnstile> v :\<le> T"
(*<*)by (rule typeof_conf[OF typeof_lit_typeof])(*>*)

lemma defval_conf[simp]: "P,h \<turnstile> default_val T :\<le> T"
(*<*)
apply (unfold conf_def)
apply (cases T)
apply auto
done
(*>*)

lemma conf_upd_obj: "h a = Some(Obj C fs) \<Longrightarrow> (P,h(a\<mapsto>(Obj C fs')) \<turnstile> x :\<le> T) = (P,h \<turnstile> x :\<le> T)"
(*<*)
apply (unfold conf_def)
apply (rule val.induct)
apply (auto simp:fun_upd_apply)
done
(*>*)

lemma conf_upd_arr: "h a = Some(Arr T s el) \<Longrightarrow> (P,h(a\<mapsto>(Arr T s el')) \<turnstile> x :\<le> T) = (P,h \<turnstile> x :\<le> T)"
apply(unfold conf_def)
apply (rule val.induct)
by (auto simp:fun_upd_apply)


lemma conf_widen: "P,h \<turnstile> v :\<le> T \<Longrightarrow> P \<turnstile> T \<le> T' \<Longrightarrow> P,h \<turnstile> v :\<le> T'"
(*<*)
apply (unfold conf_def)
apply (induct v)
apply (auto intro: widen_trans)
done
(*>*)

lemma conf_hext: "h \<unlhd> h' \<Longrightarrow> P,h \<turnstile> v :\<le> T \<Longrightarrow> P,h' \<turnstile> v :\<le> T"
proof (unfold conf_def, induct v)
  case Unit
  thus ?case by simp
next
  case Null
  thus ?case by simp
next
  case Bool
  thus ?case by simp
next
  case Intg
  thus ?case by simp
next
  case (Addr a)
  thus ?case
  proof (auto)
    fix v T'
    assume "h \<unlhd> h'" "h a = \<lfloor>v\<rfloor>"
    thus "\<exists>y. h' a = \<lfloor>y\<rfloor>" by (rule hext_objarrD)
  next
    fix v T' w
    assume "h \<unlhd> h'"
      and "h a = \<lfloor>v\<rfloor>"
      and "(case v of Obj C fs \<Rightarrow> \<lfloor>Class C\<rfloor> | Arr t s e \<Rightarrow> \<lfloor>t\<lfloor>\<rceil>\<rfloor>) = \<lfloor>T'\<rfloor>"
      and TsT: "P \<turnstile> T' \<le> T"
      and "h' a = \<lfloor>w\<rfloor>"
    hence "(case w of Obj C fs \<Rightarrow> \<lfloor>Class C\<rfloor> | Arr t s e \<Rightarrow> \<lfloor>t\<lfloor>\<rceil>\<rfloor>) = \<lfloor>T'\<rfloor>"
      apply(cases w)
       apply(cases v)
        apply(fastsimp dest:hext_objD hext_arrD)+
      apply(cases v)
       by(fastsimp dest:hext_objD hext_arrD)+
    with TsT show "\<exists>T'. (case w of Obj C fs \<Rightarrow> \<lfloor>Class C\<rfloor> | Arr t s e \<Rightarrow> \<lfloor>t\<lfloor>\<rceil>\<rfloor>) = \<lfloor>T'\<rfloor> \<and> P \<turnstile> T' \<le> T" by blast
  qed
qed

lemma conf_ClassD: "P,h \<turnstile> v :\<le> Class C \<Longrightarrow>
  v = Null \<or> (\<exists>a obj T. v = Addr a \<and> h a = Some obj \<and> obj_ty obj = T \<and> P \<turnstile> T \<le> Class C)"
(*<*)
apply (unfold conf_def)
apply(induct "v")
apply(auto)
apply(case_tac a)
 apply(simp)
apply(simp)
done
(*>*)

lemma conf_NT [iff]: "P,h \<turnstile> v :\<le> NT = (v = Null)"
(*<*)by (auto simp add: conf_def)(*>*)



section{* Value list conformance @{text"[:\<le>]"} *}

lemma confs_widens [trans]: "\<lbrakk>P,h \<turnstile> vs [:\<le>] Ts; P \<turnstile> Ts [\<le>] Ts'\<rbrakk> \<Longrightarrow> P,h \<turnstile> vs [:\<le>] Ts'"
(*<*)
  apply (rule list_all2_trans)
    by(rule conf_widen)
(*>*)

lemma confs_rev: "P,h \<turnstile> rev s [:\<le>] t = (P,h \<turnstile> s [:\<le>] rev t)"
(*<*)
  apply rule
  apply (rule subst [OF list_all2_rev])
  apply simp
  apply (rule subst [OF list_all2_rev])
  apply simp
  done
(*>*)

lemma confs_conv_map:
  "\<And>Ts'. P,h \<turnstile> vs [:\<le>] Ts' = (\<exists>Ts. map typeof\<^bsub>h\<^esub> vs = map Some Ts \<and> P \<turnstile> Ts [\<le>] Ts')"
(*<*)
apply(induct vs)
 apply simp
apply(case_tac Ts')
apply(auto simp add:conf_def)
apply(rule_tac x="T' # Ts" in exI)
apply(simp add: fun_of_def)
done
(*>*)

lemma confs_hext: "P,h \<turnstile> vs [:\<le>] Ts \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> P,h' \<turnstile> vs [:\<le>] Ts"
(*<*)by (erule list_all2_mono, erule conf_hext, assumption)(*>*)

lemma confs_Cons2: "P,h \<turnstile> xs [:\<le>] y#ys = (\<exists>z zs. xs = z#zs \<and> P,h \<turnstile> z :\<le> y \<and> P,h \<turnstile> zs [:\<le>] ys)"
(*<*)by (rule list_all2_Cons2)(*>*)


section "Object conformance"

lemma oconf_hext: "P,h \<turnstile> obj \<surd> \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> P,h' \<turnstile> obj \<surd>"
(*<*)
apply (unfold oconf_def)
apply(cases obj)
apply (fastsimp elim:conf_hext)+
done
(*>*)

lemma oconf_init_fields:
 "P \<turnstile> C has_fields FDTs \<Longrightarrow> P,h \<turnstile> (Obj C (init_fields FDTs)) \<surd>"
apply(frule has_fields_is_class)
by(fastsimp simp add: has_field_def oconf_def init_fields_def map_of_map
            dest: has_fields_fun)

lemma oconf_init_arr:
 "is_type P U \<Longrightarrow> P,h \<turnstile> (Arr U si (\<lambda>i. default_val U)) \<surd>"
by(simp add: oconf_def)

lemma oconf_fupd [intro?]:
  "\<lbrakk> P \<turnstile> C has F:T in D; P,h \<turnstile> v :\<le> T; P,h \<turnstile> (Obj C fs) \<surd> \<rbrakk> 
  \<Longrightarrow> P,h \<turnstile> (Obj C (fs((F,D)\<mapsto>v))) \<surd>"
(*<*)
  apply (unfold oconf_def has_field_def)
  apply clarsimp
  apply (drule (1) has_fields_fun)
  apply (auto simp add: fun_upd_apply)
  done                                    
(*>*)

lemma oconf_fupd_arr [intro?]:
  "\<lbrakk> 0 \<le> i; i < si; P,h \<turnstile> v :\<le> T; P,h \<turnstile> (Arr T si el) \<surd> \<rbrakk>
  \<Longrightarrow> P,h \<turnstile> (Arr T si (el(i := v))) \<surd>"
apply(unfold oconf_def)
apply(clarsimp)
done


lemmas oconf_new = oconf_hext [OF _ hext_new]
lemmas oconf_upd_obj = oconf_hext [OF _ hext_upd_obj]
lemmas oconf_upd_arr = oconf_hext [OF _ hext_upd_arr]

section "Heap conformance"

lemma hconfD: "\<lbrakk> P \<turnstile> h \<surd>; h a = Some obj \<rbrakk> \<Longrightarrow> P,h \<turnstile> obj \<surd>"
(*<*)
apply (unfold hconf_def)
apply (fast)
done
(*>*)

lemma hconf_new: "\<lbrakk> P \<turnstile> h \<surd>; h a = None; P,h \<turnstile> obj \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> h(a\<mapsto>obj) \<surd>"
(*<*)by (unfold hconf_def) (auto intro: oconf_new preallocated_new)(*>*)

lemma hconf_upd_obj: "\<lbrakk> P \<turnstile> h\<surd>; h a = Some(Obj C fs); P,h \<turnstile> (Obj C fs') \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> h(a\<mapsto>(Obj C fs'))\<surd>"
(*<*)by (unfold hconf_def) (auto intro: oconf_upd_obj preallocated_upd_obj)(*>*)

lemma hconf_upd_arr: "\<lbrakk> P \<turnstile> h\<surd>; h a = Some(Arr T si el); P,h \<turnstile> (Arr T si el') \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> h(a\<mapsto>(Arr T si el'))\<surd>"
by(unfold hconf_def)(auto intro: oconf_upd_arr preallocated_upd_arr)

section "Local variable conformance"

lemma lconf_hext: "\<lbrakk> P,h \<turnstile> l (:\<le>) E; h \<unlhd> h' \<rbrakk> \<Longrightarrow> P,h' \<turnstile> l (:\<le>) E"
(*<*)
apply (unfold lconf_def)
apply  (fast elim: conf_hext)
done
(*>*)

lemma lconf_upd:
  "\<lbrakk> P,h \<turnstile> l (:\<le>) E; P,h \<turnstile> v :\<le> T; E V = Some T \<rbrakk> \<Longrightarrow> P,h \<turnstile> l(V\<mapsto>v) (:\<le>) E"
(*<*)
apply (unfold lconf_def)
apply auto
done
(*>*)

lemma lconf_empty[iff]: "P,h \<turnstile> empty (:\<le>) E"
(*<*)by(simp add:lconf_def)(*>*)

lemma lconf_upd2: "\<lbrakk>P,h \<turnstile> l (:\<le>) E; P,h \<turnstile> v :\<le> T\<rbrakk> \<Longrightarrow> P,h \<turnstile> l(V\<mapsto>v) (:\<le>) E(V\<mapsto>T)"
(*<*)by(simp add:lconf_def)(*>*)


end
