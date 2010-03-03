(*  Title:      JinjaThreads/Common/Decl.thy
    Author:     David von Oheimb, Andreas Lochbihler

    Based on the Jinja theory Common/Decl.thy by David von Oheimb
*)

header {* \isaheader{Class Declarations and Programs} *}

theory Decl imports Type begin

types 
  fdecl    = "vname \<times> ty"        -- "field declaration"

  'm mdecl = "mname \<times> ty list \<times> ty \<times> 'm"     -- "method = name, arg. types, return type, body"

  'm "class" = "cname \<times> fdecl list \<times> 'm mdecl list"       -- "class = superclass, fields, methods"

  'm cdecl = "cname \<times> 'm class"  -- "class declaration"

  'm prog  = "'m cdecl list"     -- "program"

(*<*)
translations
  (type) "fdecl"   <= (type) "String.literal \<times> ty"
  (type) "'c mdecl" <= (type) "String.literal \<times> ty list \<times> ty \<times> 'c"
  (type) "'c class" <= (type) "String.literal \<times> fdecl list \<times> ('c mdecl) list"
  (type) "'c cdecl" <= (type) "String.literal \<times> ('c class)"
  (type) "'c prog" <= (type) "('c cdecl) list"
(*>*)

constdefs
  "class" :: "'m prog \<Rightarrow> cname \<rightharpoonup> 'm class"
  "class  \<equiv>  map_of"

  is_class :: "'m prog \<Rightarrow> cname \<Rightarrow> bool"
  "is_class P C  \<equiv>  class P C \<noteq> None"

lemma finite_is_class: "finite {C. is_class P C}"
(*<*)
apply (unfold is_class_def class_def)
apply (fold dom_def)
apply (rule finite_dom_map_of)
done
(*>*)

consts
  is_type :: "'m prog \<Rightarrow> ty \<Rightarrow> bool"
primrec
is_type_void:   "is_type P Void = True"
is_type_bool:   "is_type P Boolean = True"
is_type_int:    "is_type P Integer = True"
is_type_nt:     "is_type P NT = True"
is_type_class:  "is_type P (Class C) = is_class P C"
is_type_array:  "is_type P (A\<lfloor>\<rceil>) = is_type P A"

lemma NT_Array_is_type: "is_NT_Array A \<Longrightarrow> is_type P A"
by(induct A, auto)

end
