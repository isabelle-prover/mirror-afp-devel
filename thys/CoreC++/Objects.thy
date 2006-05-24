(*  Title:       CoreC++
    ID:          $Id: Objects.thy,v 1.3 2006-05-24 01:09:42 lsf37 Exp $
    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

   Based on the Jinja theory Common/Objects.thy by Tobias Nipkow 
*)


header {* Objects and the Heap *}

theory Objects imports SubObj begin

subsection{* Objects *}

types
  subo = "(path \<times> (vname \<rightharpoonup> val))"     -- "subobjects realized on the heap"
  obj  = "cname \<times> subo set"            -- "mdc and subobject"


constdefs
  init_class_fieldmap :: "prog \<Rightarrow> cname \<Rightarrow> (vname \<rightharpoonup> val)"
  "init_class_fieldmap P C \<equiv> 
     map_of (map (\<lambda>(F,T).(F,default_val T)) (fst(snd(the(class P C)))) )"

consts
  init_obj :: "prog \<Rightarrow> cname \<Rightarrow>  (path \<times> (vname \<rightharpoonup> val))set"

inductive "init_obj P C"
intros
  "(C,Cs) \<in> Subobjs P \<Longrightarrow> (Cs,init_class_fieldmap P (last Cs)) \<in> init_obj P C"


lemma init_obj_nonempty: "(Cs,fs) \<in> init_obj P C \<Longrightarrow> Cs \<noteq> []"
by (fastsimp elim:init_obj.elims dest:Subobjs_nonempty)

lemma init_obj_no_Ref: 
"\<lbrakk>(Cs,fs) \<in> init_obj P C;  fs F = Some(Ref(a',Cs'))\<rbrakk> \<Longrightarrow> False"
by (fastsimp elim:init_obj.elims default_val_no_Ref 
                  simp:init_class_fieldmap_def map_of_map)

lemma SubobjsSet_init_objSet:
  "{Cs. (C,Cs) \<in> Subobjs P} = {Cs. \<exists>vmap. (Cs,vmap) \<in> init_obj P C}"
by ( fastsimp intro:init_obj.intros elim:init_obj.elims)


constdefs
  obj_ty  :: "obj \<Rightarrow> ty"
  "obj_ty obj  \<equiv>  Class (fst obj)"


 -- "a new, blank object with default values in all fields:"
  blank :: "prog \<Rightarrow> cname \<Rightarrow> obj"
  "blank P C  \<equiv> (C, init_obj P C)"


lemma [simp]: "obj_ty (C,S) = Class C"
  by (simp add: obj_ty_def)

subsection{* Heap *}

types heap  = "addr \<rightharpoonup> obj"

syntax
  cname_of  :: "heap \<Rightarrow> addr \<Rightarrow> cname" 
translations
  "cname_of hp a"  == "fst (the (hp a))"

constdefs
  new_Addr  :: "heap \<Rightarrow> addr option"
  "new_Addr h  \<equiv>  if \<exists>a. h a = None then Some(SOME a. h a = None) else None"

lemma new_Addr_SomeD:
  "new_Addr h = Some a \<Longrightarrow> h a = None"
 by(fastsimp simp add:new_Addr_def split:if_splits intro:someI)


end
