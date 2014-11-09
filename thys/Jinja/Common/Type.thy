(*  Title:      Jinja/Common/Type.thy

    Author:     David von Oheimb, Tobias Nipkow
    Copyright   1999 Technische Universitaet Muenchen
*)

section {* Jinja types *}

theory Type imports Auxiliary begin

type_synonym cname = string -- "class names"
type_synonym mname = string -- "method name"
type_synonym vname = string -- "names for local/field variables"

definition Object :: cname
where
  "Object \<equiv> ''Object''"

definition this :: vname
where
  "this \<equiv> ''this''"

-- "types"
datatype ty
  = Void          -- "type of statements"
  | Boolean
  | Integer
  | NT            -- "null type"
  | Class cname   -- "class type"

definition is_refT :: "ty \<Rightarrow> bool"
where
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
