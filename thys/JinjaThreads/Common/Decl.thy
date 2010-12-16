(*  Title:      JinjaThreads/Common/Decl.thy
    Author:     David von Oheimb, Andreas Lochbihler

    Based on the Jinja theory Common/Decl.thy by David von Oheimb
*)

header {* \isaheader{Class Declarations and Programs} *}

theory Decl imports Type begin

types volatile = bool

record fmod =
  volatile :: volatile

types 
  fdecl    = "vname \<times> ty \<times> fmod"        -- "field declaration"

  'm mdecl = "mname \<times> ty list \<times> ty \<times> 'm"     -- "method = name, arg. types, return type, body"

  'm "class" = "cname \<times> fdecl list \<times> 'm mdecl list"       -- "class = superclass, fields, methods"

  'm cdecl = "cname \<times> 'm class"  -- "class declaration"

  'm prog  = "'m cdecl list"     -- "program"

translations
  (type) "fdecl"   <= (type) "String.literal \<times> ty \<times> fmod"
  (type) "'c mdecl" <= (type) "String.literal \<times> ty list \<times> ty \<times> 'c"
  (type) "'c class" <= (type) "String.literal \<times> fdecl list \<times> ('c mdecl) list"
  (type) "'c cdecl" <= (type) "String.literal \<times> ('c class)"
  (type) "'c prog" <= (type) "('c cdecl) list"

definition "class" :: "'m prog \<Rightarrow> cname \<rightharpoonup> 'm class"
where
  "class  \<equiv>  map_of"

definition is_class :: "'m prog \<Rightarrow> cname \<Rightarrow> bool"
where
  "is_class P C  \<equiv>  class P C \<noteq> None"

lemma finite_is_class: "finite {C. is_class P C}"
(*<*)
apply (unfold is_class_def class_def)
apply (fold dom_def)
apply (rule finite_dom_map_of)
done
(*>*)


primrec is_type :: "'m prog \<Rightarrow> ty \<Rightarrow> bool"
where
  is_type_void:   "is_type P Void = True"
| is_type_bool:   "is_type P Boolean = True"
| is_type_int:    "is_type P Integer = True"
| is_type_nt:     "is_type P NT = True"
| is_type_class:  "is_type P (Class C) = is_class P C"
| is_type_array:  "is_type P (A\<lfloor>\<rceil>) = is_type P A"

lemma NT_Array_is_type: "is_NT_Array A \<Longrightarrow> is_type P A"
by(induct A, auto)

abbreviation "types" :: "'m prog \<Rightarrow> ty set"
where "types P \<equiv> {T. is_type P T}"

subsection {* Code generation *}

lemma is_class_intros [code_pred_intro]:
  "is_class ((C, data) # P) C"
  "is_class P C \<Longrightarrow> is_class ((D, data) # P) C"
by(auto simp add: is_class_def class_def simp del: split_paired_Ex)

lemma is_class_cases:
  assumes "is_class P C"
  obtains data P' where "P = (C, data) # P'"
  | D data P' where "P = (D, data) # P'" "is_class P' C"
using assms
by(cases P)(fastsimp simp add: is_class_def class_def split: split_if_asm)+

code_pred is_class
by(erule is_class_cases) fastsimp+

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> bool)
  [inductify]
  is_type
.

end
