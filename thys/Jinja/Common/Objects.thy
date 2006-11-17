(*  Title:      HOL/MicroJava/J/State.thy
    ID:         $Id: Objects.thy,v 1.4 2006-11-17 01:28:44 makarius Exp $
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{Objects and the Heap} *}

theory Objects imports TypeRel Value begin

subsection{* Objects *}

types 
  fields = "vname \<times> cname \<rightharpoonup> val"  -- "field name, defining class, value"
  obj = "cname \<times> fields"    -- "class instance with class name and fields"

constdefs
  obj_ty  :: "obj \<Rightarrow> ty"
  "obj_ty obj  \<equiv>  Class (fst obj)"

  init_fields :: "((vname \<times> cname) \<times> ty) list \<Rightarrow> fields"
  "init_fields  \<equiv>  map_of \<circ> map (\<lambda>(F,T). (F,default_val T))"
  
  -- "a new, blank object with default values in all fields:"
  blank :: "'m prog \<Rightarrow> cname \<Rightarrow> obj"
  "blank P C  \<equiv>  (C,init_fields (fields P C))" 

lemma [simp]: "obj_ty (C,fs) = Class C"
(*<*)by (simp add: obj_ty_def)(*>*)

subsection{* Heap *}

types heap  = "addr \<rightharpoonup> obj"

abbreviation
  cname_of :: "heap \<Rightarrow> addr \<Rightarrow> cname" where
  "cname_of hp a == fst (the (hp a))"

constdefs
  new_Addr  :: "heap \<Rightarrow> addr option"
  "new_Addr h  \<equiv>  if \<exists>a. h a = None then Some(SOME a. h a = None) else None"

  cast_ok :: "'m prog \<Rightarrow> cname \<Rightarrow> heap \<Rightarrow> val \<Rightarrow> bool"
  "cast_ok P C h v  \<equiv>  v = Null \<or> P \<turnstile> cname_of h (the_Addr v) \<preceq>\<^sup>* C"

  hext :: "heap \<Rightarrow> heap \<Rightarrow> bool" ("_ \<unlhd> _" [51,51] 50)
  "h \<unlhd> h'  \<equiv>  \<forall>a C fs. h a = Some(C,fs) \<longrightarrow> (\<exists>fs'. h' a = Some(C,fs'))"

consts
  typeof_h :: "heap \<Rightarrow> val \<Rightarrow> ty option"  ("typeof\<^bsub>_\<^esub>")
primrec
  "typeof\<^bsub>h\<^esub>  Unit    = Some Void"
  "typeof\<^bsub>h\<^esub>  Null    = Some NT"
  "typeof\<^bsub>h\<^esub> (Bool b) = Some Boolean"
  "typeof\<^bsub>h\<^esub> (Intg i) = Some Integer"
  "typeof\<^bsub>h\<^esub> (Addr a) = (case h a of None \<Rightarrow> None | Some(C,fs) \<Rightarrow> Some(Class C))"

lemma new_Addr_SomeD:
  "new_Addr h = Some a \<Longrightarrow> h a = None"
 (*<*)by(fastsimp simp add:new_Addr_def split:if_splits intro:someI)(*>*)

lemma [simp]: "(typeof\<^bsub>h\<^esub> v = Some Boolean) = (\<exists>b. v = Bool b)"
 (*<*)by(induct v) auto(*>*)

lemma [simp]: "(typeof\<^bsub>h\<^esub> v = Some Integer) = (\<exists>i. v = Intg i)"
(*<*)by(cases v) auto(*>*)

lemma [simp]: "(typeof\<^bsub>h\<^esub> v = Some NT) = (v = Null)"
 (*<*)by(cases v) auto(*>*)

lemma [simp]: "(typeof\<^bsub>h\<^esub> v = Some(Class C)) = (\<exists>a fs. v = Addr a \<and> h a = Some(C,fs))"
 (*<*)by(cases v) auto(*>*)

lemma [simp]: "h a = Some(C,fs) \<Longrightarrow> typeof\<^bsub>(h(a\<mapsto>(C,fs')))\<^esub> v = typeof\<^bsub>h\<^esub> v"
 (*<*)by(induct v) (auto simp:fun_upd_apply)(*>*)

text{* For literal values the first parameter of @{term typeof} can be
set to @{term empty} because they do not contain addresses: *}

abbreviation
  typeof :: "val \<Rightarrow> ty option" where
  "typeof v == typeof_h empty v"

lemma typeof_lit_typeof:
  "typeof v = Some T \<Longrightarrow> typeof\<^bsub>h\<^esub> v = Some T"
 (*<*)by(cases v) auto(*>*)

lemma typeof_lit_is_type: 
  "typeof v = Some T \<Longrightarrow> is_type P T"
 (*<*)by (induct v) (auto simp:is_type_def)(*>*)


section {* Heap extension @{text"\<unlhd>"} *}

lemma hextI: "\<forall>a C fs. h a = Some(C,fs) \<longrightarrow> (\<exists>fs'. h' a = Some(C,fs')) \<Longrightarrow> h \<unlhd> h'"
(*<*)
apply (unfold hext_def)
apply auto
done
(*>*)

lemma hext_objD: "\<lbrakk> h \<unlhd> h'; h a = Some(C,fs) \<rbrakk> \<Longrightarrow> \<exists>fs'. h' a = Some(C,fs')"
(*<*)
apply (unfold hext_def)
apply (force)
done
(*>*)

lemma hext_refl [iff]: "h \<unlhd> h"
(*<*)
apply (rule hextI)
apply (fast)
done
(*>*)

lemma hext_new [simp]: "h a = None \<Longrightarrow> h \<unlhd> h(a\<mapsto>x)"
(*<*)
apply (rule hextI)
apply (auto simp:fun_upd_apply)
done
(*>*)

lemma hext_trans: "\<lbrakk> h \<unlhd> h'; h' \<unlhd> h'' \<rbrakk> \<Longrightarrow> h \<unlhd> h''"
(*<*)
apply (rule hextI)
apply (fast dest: hext_objD)
done
(*>*)

lemma hext_upd_obj: "h a = Some (C,fs) \<Longrightarrow> h \<unlhd> h(a\<mapsto>(C,fs'))"
(*<*)
apply (rule hextI)
apply (auto simp:fun_upd_apply)
done
(*>*)

lemma hext_typeof_mono: "\<lbrakk> h \<unlhd> h'; typeof\<^bsub>h\<^esub> v = Some T \<rbrakk> \<Longrightarrow> typeof\<^bsub>h'\<^esub> v = Some T"
(*<*)
apply(cases v)
    apply simp
   apply simp
  apply simp
 apply simp
apply(fastsimp simp:hext_def)
done
(*>*)


end
