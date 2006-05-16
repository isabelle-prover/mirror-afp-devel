(* Author: Daniel Wasserrab
   Based on the Jinja theory Common/Decl.thy by David von Oheimb and Tobias Nipkow *)

header {* CoreC++ types *}

theory Type imports Aux begin

types
 cname = string -- "class names"
 mname = string -- "method name"
 vname = string -- "names for local/field variables"
 

constdefs
 this :: vname
"this \<equiv> ''this''"

-- "types"
datatype ty
  = Void          -- "type of statements"
  | Boolean
  | Integer
  | NT            -- "null type"
  | Class cname   -- "class type"

datatype base  -- "superclass"
  = Repeats cname  -- "repeated (nonvirtual) inheritance"
  | Shares cname   -- "shared (virtual) inheritance"

consts 
  getbase :: "base \<Rightarrow> cname"
  isRepBase :: "base \<Rightarrow> bool"
  isShBase :: "base \<Rightarrow> bool"

primrec
  "getbase (Repeats C) = C"
  "getbase (Shares C)  = C"
primrec
  "isRepBase (Repeats C) = True"
  "isRepBase (Shares C) = False"
primrec
  "isShBase(Repeats C) = False"
  "isShBase(Shares C) = True"

constdefs
  is_refT :: "ty \<Rightarrow> bool"
  "is_refT T  \<equiv>  T = NT \<or> (\<exists>C. T = Class C)"

lemma [iff]: "is_refT NT"
by(simp add:is_refT_def)

lemma [iff]: "is_refT(Class C)"
by(simp add:is_refT_def)

lemma refTE:
  "\<lbrakk>is_refT T; T = NT \<Longrightarrow> Q; \<And>C. T = Class C \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by (auto simp add: is_refT_def)

lemma not_refTE:
  "\<lbrakk> \<not>is_refT T; T = Void \<or> T = Boolean \<or> T = Integer \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by (cases T, auto simp add: is_refT_def)

types 
  env  = "vname \<rightharpoonup> ty"

end

