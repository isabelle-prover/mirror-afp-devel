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

datatype
  'm prog = Program "'m cdecl list" 

translations
  (type) "fdecl"   <= (type) "String.literal \<times> ty \<times> fmod"
  (type) "'c mdecl" <= (type) "String.literal \<times> ty list \<times> ty \<times> 'c"
  (type) "'c class" <= (type) "String.literal \<times> fdecl list \<times> ('c mdecl) list"
  (type) "'c cdecl" <= (type) "String.literal \<times> ('c class)"

primrec the_Program :: "'m prog \<Rightarrow> 'm cdecl list"
where
  "the_Program (Program P) = P"

primrec "class" :: "'m prog \<Rightarrow> cname \<rightharpoonup> 'm class"
where
  "class (Program p) = map_of p"

definition is_class :: "'m prog \<Rightarrow> cname \<Rightarrow> bool"
where
  "is_class P C  \<equiv>  class P C \<noteq> None"

lemma finite_is_class: "finite {C. is_class P C}"
(*<*)
apply(cases P)
apply (unfold is_class_def)
apply (fold dom_def)
apply(simp add: finite_dom_map_of)
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
  "class P C \<noteq> None \<Longrightarrow> is_class P C"
by(auto simp add: is_class_def)

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> bool)
  is_class 
unfolding is_class_def by simp

declare is_class_def[code]

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> bool)
  [inductify]
  is_type
.

declare is_type.equation(2)[code del]
declare is_type.simps [code]

end
