(*  Title:      Jinja/Common/Type.thy
    ID:         $Id: Type.thy,v 1.1 2005-05-31 23:21:04 lsf37 Exp $
    Author:     David von Oheimb, Tobias Nipkow
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{Jinja types} *}

theory Type = Aux:

types
 cname = string -- "class names"
 mname = string -- "method name"
 vname = string -- "names for local/field variables"

constdefs
  Object :: cname
  "Object \<equiv> ''Object''"
  this :: vname
  "this \<equiv> ''this''"

-- "types"
datatype ty
  = Void          -- "type of statements"
  | Boolean
  | Integer
  | NT            -- "null type"
  | Class cname   -- "class type"

constdefs
  is_refT :: "ty \<Rightarrow> bool"
  "is_refT T  \<equiv>  T = NT \<or> (\<exists>C. T = Class C)"

lemma [iff]: "is_refT NT"
(*<*)by(simp add:is_refT_def)(*>*)

lemma [iff]: "is_refT(Class C)"
(*<*)by(simp add:is_refT_def)(*>*)

lemma refTE:
  "\<lbrakk>is_refT T; T = NT \<Longrightarrow> P; \<And>C. T = Class C \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
(*<*)by (auto simp add: is_refT_def)(*>*)

lemma not_refTE:
  "\<lbrakk> \<not>is_refT T; T = Void \<or> T = Boolean \<or> T = Integer \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
(*<*)by (cases T, auto simp add: is_refT_def)(*>*)

end
