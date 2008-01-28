(*  Title:      HOL/MicroJava/J/Decl.thy
    ID:         $Id: Decl.thy,v 1.4 2008-01-28 22:38:21 makarius Exp $
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{Class Declarations and Programs} *}

theory Decl imports Type begin

types 
  fdecl    = "vname \<times> ty"        -- "field declaration"

  'm mdecl = "mname \<times> ty list \<times> ty \<times> 'm"     -- {* method = name, arg.\ types, return type, body *}

  'm "class" = "cname \<times> fdecl list \<times> 'm mdecl list"       -- "class = superclass, fields, methods"

  'm cdecl = "cname \<times> 'm class"  -- "class declaration"

  'm prog  = "'m cdecl list"     -- "program"

(*<*)
translations
  "fdecl"   <= (type) "vname \<times> ty"
  "mdecl c" <= (type) "mname \<times> ty list \<times> ty \<times> c"
  "class c" <= (type) "cname \<times> fdecl list \<times> (c mdecl) list"
  "cdecl c" <= (type) "cname \<times> (c class)"
  "prog  c" <= (type) "(c cdecl) list"
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

constdefs
  is_type :: "'m prog \<Rightarrow> ty \<Rightarrow> bool"
  "is_type P T  \<equiv>
  (case T of Void \<Rightarrow> True | Boolean \<Rightarrow> True | Integer \<Rightarrow> True | NT \<Rightarrow> True
   | Class C \<Rightarrow> is_class P C)"

lemma is_type_simps [simp]:
  "is_type P Void \<and> is_type P Boolean \<and> is_type P Integer \<and>
  is_type P NT \<and> is_type P (Class C) = is_class P C"
(*<*)by(simp add:is_type_def)(*>*)


translations
  "types P" == "Collect (is_type P)"

end
