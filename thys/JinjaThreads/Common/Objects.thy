(*  Title:      JinjaThreads/Common/Objects.thy
    Author:     David von Oheimb, Andreas Lochbihler

    Based on the Jinja theory Common/Objects.thy by David von Oheimb
*)

header {* \isaheader{Objects and the Heap} *}

theory Objects imports TypeRel Value begin

subsection{* Objects and Arrays *}

types 
  fields = "vname \<times> cname \<rightharpoonup> val"       -- "field name, defining class, value"

datatype heapobj
  = Obj cname fields                    -- "class instance with class name and fields"
  | Arr ty int "int \<Rightarrow> val"             -- "element type, size of the array and mapping cell index to cell content"

consts
  obj_ty  :: "heapobj \<Rightarrow> ty"
primrec
"obj_ty (Obj c f)   = Class c"
"obj_ty (Arr t s e) = Array t"

fun is_Arr :: "heapobj \<Rightarrow> bool" where
  "is_Arr (Obj C fs)    = False"
| "is_Arr (Arr T si el) = True"

lemma is_Arr_conv:
  "is_Arr arrobj = (\<exists>T si el. arrobj = Arr T si el)"
by(cases arrobj, auto)

lemma is_ArrE:
  "\<lbrakk> is_Arr arrobj; \<And>T si el. arrobj = Arr T si el \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
  "\<lbrakk> \<not> is_Arr arrobj; \<And>C fs. arrobj = Obj C fs \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
by(cases arrobj, auto)+

constdefs
  init_fields :: "((vname \<times> cname) \<times> ty) list \<Rightarrow> fields"
  "init_fields  \<equiv>  map_of \<circ> map (\<lambda>(F,T). (F,default_val T))"
  
  -- "a new, blank object with default values in all fields:"
  blank :: "'m prog \<Rightarrow> cname \<Rightarrow> heapobj"
  "blank P C  \<equiv>  Obj C (init_fields (fields P C))"

  blank_arr :: "ty \<Rightarrow> int \<Rightarrow> heapobj"
  "blank_arr T i \<equiv> Arr T i (\<lambda>n. default_val T)"

lemma blank_obj: "\<exists>c f. blank P C = Obj c f"
apply(rule_tac x = "C" in exI)
apply(rule_tac x = "init_fields (fields P C)" in exI)
by(simp add: blank_def)

lemma obj_ty_blank [iff]: "obj_ty (blank P C) = Class C"
  by (simp add: blank_def)


subsection{* Heap *}

types heap = "addr \<rightharpoonup> heapobj"

fun the_obj :: "heapobj \<Rightarrow> cname \<times> fields" where
  "the_obj (Obj C fs) = (C, fs)"

fun the_arr :: "heapobj \<Rightarrow> ty \<times> int \<times> (int \<Rightarrow> val)" where
  "the_arr (Arr T si el) = (T, si, el)"


abbreviation
  cname_of :: "heap \<Rightarrow> addr \<Rightarrow> cname" where
  "cname_of hp a == fst (the_obj (the (hp a)))"

constdefs
  new_Addr  :: "heap \<Rightarrow> addr option"
  "new_Addr h  \<equiv>  if \<exists>a. h a = None then Some(SOME a. h a = None) else None"

  hext :: "heap \<Rightarrow> heap \<Rightarrow> bool" ("_ \<unlhd> _" [51,51] 50)
  "h \<unlhd> h'  \<equiv> (\<forall>a C fs. h a = \<lfloor>Obj C fs\<rfloor> \<longrightarrow> (\<exists>fs'. h' a = \<lfloor>Obj C fs'\<rfloor>))
           \<and> (\<forall>a T s e. h a = \<lfloor>Arr T s e\<rfloor> \<longrightarrow> (\<exists>e'. h' a = \<lfloor>Arr T s e'\<rfloor>))"

consts
  typeof_h :: "heap \<Rightarrow> val \<Rightarrow> ty option"  ("typeof\<^bsub>_\<^esub>")
primrec
  "typeof\<^bsub>h\<^esub>  Unit    = Some Void"
  "typeof\<^bsub>h\<^esub>  Null    = Some NT"
  "typeof\<^bsub>h\<^esub> (Bool b) = Some Boolean"
  "typeof\<^bsub>h\<^esub> (Intg i) = Some Integer"
  "typeof\<^bsub>h\<^esub> (Addr a) = (case h a of None \<Rightarrow> None 
                                 | Some ho \<Rightarrow> (case ho of Obj C fs \<Rightarrow> \<lfloor>Class C\<rfloor>
                                                        | Arr t s e \<Rightarrow> \<lfloor>Array t\<rfloor>))"

lemma new_Addr_SomeD:
  "new_Addr h = Some a \<Longrightarrow> h a = None"
 (*<*)by(fastsimp simp add:new_Addr_def split:if_splits intro:someI)(*>*)

lemma [simp]: "(typeof\<^bsub>h\<^esub> v = Some Boolean) = (\<exists>b. v = Bool b)"
by(cases v, auto split:heapobj.split)

lemma [simp]: "(typeof\<^bsub>h\<^esub> v = Some Integer) = (\<exists>i. v = Intg i)"
by(cases v, auto split: heapobj.split)

lemma [simp]: "(typeof\<^bsub>h\<^esub> v = Some NT) = (v = Null)"
by(cases v, auto split:heapobj.split)

lemma [simp]: "(typeof\<^bsub>h\<^esub> v = Some(Class C)) = (\<exists>a fs. v = Addr a \<and> h a = Some(Obj C fs))"
by(cases v, auto split:heapobj.split)

lemma [simp]: "(typeof\<^bsub>h\<^esub> v = Some(Array T)) = (\<exists>a s e. v = Addr a \<and> h a = Some(Arr T s e))"
by(cases v, auto split:heapobj.split)

lemma [simp]: "h a = Some(Obj C fs) \<Longrightarrow> typeof\<^bsub>(h(a\<mapsto>(Obj C fs')))\<^esub> v = typeof\<^bsub>h\<^esub> v"
by(induct v) (auto simp:fun_upd_apply)

lemma [simp]: "h a = Some(Arr t s e) \<Longrightarrow> typeof\<^bsub>(h(a\<mapsto>(Arr t s e')))\<^esub> v = typeof\<^bsub>h\<^esub> v"
by(induct v) (auto simp:fun_upd_apply)


text{* For literal values the first parameter of @{term typeof} can be
set to @{term empty} because they do not contain addresses: *}

consts
  typeof :: "val \<Rightarrow> ty option"

translations
  "typeof v" == "typeof_h (CONST empty) v"

lemma typeof_lit_typeof:
  "typeof v = Some T \<Longrightarrow> typeof\<^bsub>h\<^esub> v = Some T"
 (*<*)by(cases v) auto(*>*)

lemma typeof_lit_is_type: 
  "typeof v = Some T \<Longrightarrow> is_type P T"
 (*<*)by (induct v) (auto)(*>*)

lemma typeof_NoneD [simp,dest]:
  "typeof v = Some x \<Longrightarrow> \<not>is_Addr v"
  by (cases v) auto


definition cast_ok :: "'m prog \<Rightarrow> ty \<Rightarrow> heap \<Rightarrow> val \<Rightarrow> bool" where
  "cast_ok P T h v \<equiv> \<exists>U. typeof\<^bsub>h\<^esub> v = \<lfloor>U\<rfloor> \<and> P \<turnstile> U \<le> T"

section {* Heap extension @{text"\<unlhd>"} *}

lemma hextI:
  "\<lbrakk>\<forall>a C fs. h a = Some(Obj C fs) \<longrightarrow> (\<exists>fs'. h' a = Some(Obj C fs'));
    \<forall>a T s e. h a = Some(Arr T s e) \<longrightarrow> (\<exists>e'. h' a = Some(Arr T s e')) \<rbrakk>
  \<Longrightarrow> h \<unlhd> h'"
(*<*)
apply (unfold hext_def)
apply auto
done
(*>*)

lemma hext_objD: "\<lbrakk> h \<unlhd> h'; h a = Some(Obj C fs) \<rbrakk> \<Longrightarrow> \<exists>fs'. h' a = Some(Obj C fs')"
(*<*)
apply (unfold hext_def)
apply (force)
done
(*>*)

lemma hext_arrD: "\<lbrakk> h \<unlhd> h'; h a = Some(Arr T s e) \<rbrakk> \<Longrightarrow> \<exists>e'. h' a = Some(Arr T s e')"
apply(unfold hext_def)
apply(force)
done

lemma hext_objarrD: "\<lbrakk> h \<unlhd> h'; h a = Some v \<rbrakk> \<Longrightarrow> \<exists>w. h' a = Some w"
apply(case_tac v)
by(auto dest: hext_objD hext_arrD)

lemma hext_refl [iff]: "h \<unlhd> h"
(*<*)
apply (rule hextI)
apply (fast)
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
apply (fast dest: hext_arrD)
done
(*>*)

lemma hext_upd_obj: "h a = Some (Obj C fs) \<Longrightarrow> h \<unlhd> h(a\<mapsto>(Obj C fs'))"
(*<*)
apply (rule hextI)
apply (auto simp:fun_upd_apply)
done
(*>*)

lemma hext_upd_arr: "h a = Some (Arr T s e) \<Longrightarrow> h \<unlhd> h(a\<mapsto>(Arr T s e'))"
apply(rule hextI)
apply (auto simp:fun_upd_apply)
done

lemma hext_typeof_mono: "\<lbrakk> h \<unlhd> h'; typeof\<^bsub>h\<^esub> v = Some T \<rbrakk> \<Longrightarrow> typeof\<^bsub>h'\<^esub> v = Some T"
proof (cases v)
  case Unit
  assume "h \<unlhd> h'" "typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor>" "v = Unit"
  thus ?thesis by simp
next
  case Null
  assume "h \<unlhd> h'" "typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor>" "v = Null"
  thus ?thesis by simp
next
  case (Bool b)
  assume "h \<unlhd> h'" "typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor>" "v = Bool b"
  thus ?thesis by simp
next
  case (Intg i)
  assume "h \<unlhd> h'" "typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor>" "v = Intg i"
  thus ?thesis by simp
next
  case(Addr a)
  assume hexth: "h \<unlhd> h'" and thT: "typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor>" and vIi: "v = Addr a"
  from hexth have hextobj: "\<forall>a C fs. h a = \<lfloor>Obj C fs\<rfloor> \<longrightarrow> (\<exists>fs'. h' a = \<lfloor>Obj C fs'\<rfloor>)" by (simp add: hext_def)
  from hexth have hextarr: "\<forall>a T s e. h a = \<lfloor>Arr T s e\<rfloor> \<longrightarrow> (\<exists>e'. h' a = \<lfloor>Arr T s e'\<rfloor>)" by (simp add: hext_def)
  show "typeof\<^bsub>h'\<^esub> v = Some T"
  proof (cases "h a")
    case None
    with vIi have "typeof\<^bsub>h\<^esub> v = None" by (simp split:heapobj.split)
    with thT have False by simp
    thus ?thesis by simp
  next
    case (Some ho)
    show "typeof\<^bsub>h'\<^esub> v = Some T"
    proof (cases ho)
      case (Obj C fs)
      with hextobj Some have exfsh':"\<exists>fs'. h' a = \<lfloor>Obj C fs'\<rfloor>" by simp
      then obtain fs' where "h' a = \<lfloor>Obj C fs'\<rfloor>" by clarify
      with vIi Some Obj thT show ?thesis by simp
    next
      case (Arr T s e)
      with hextarr Some have "\<exists>e'. h' a = \<lfloor>Arr T s e'\<rfloor>" by simp
      then obtain e' where "h' a = \<lfloor>Arr T s e'\<rfloor>" by clarify
      with vIi Some Arr thT show ?thesis by simp
    qed
  qed
qed

lemma hext_None: "\<lbrakk> hext h h'; h' a = None \<rbrakk> \<Longrightarrow> h a = None"
by(cases "h a", auto dest: hext_objarrD)

lemma hext_new_Addr:
  assumes "hext h h'"
  and "new_Addr h' = \<lfloor>a'\<rfloor>"
  obtains a where "new_Addr h = \<lfloor>a\<rfloor>"
using prems
apply(auto dest!: hext_None simp add: new_Addr_def split: split_if_asm)
apply(fastsimp)
done

lemma hext_typeof_eq:
  "\<lbrakk> hext h h'; h a = \<lfloor>v\<rfloor> \<rbrakk> \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr a) = typeof\<^bsub>h'\<^esub> (Addr a)"
apply(cases v, auto dest: hext_objD hext_arrD)
apply(auto simp: hext_def)
 apply(erule_tac x="a" in allE, fastsimp)
apply(erule_tac x="a" in allE, fastsimp)
done

lemma type_of_hext_type_of:
  "\<lbrakk> typeof\<^bsub>h\<^esub> w = \<lfloor>T\<rfloor>; hext h h' \<rbrakk> \<Longrightarrow> typeof\<^bsub>h'\<^esub> w = \<lfloor>T\<rfloor>"
apply(cases w, auto)
 apply(case_tac a, auto dest: hext_objarrD)
apply(case_tac a, auto)
 apply(case_tac aa, auto dest: hext_objD hext_arrD)+
done

end
