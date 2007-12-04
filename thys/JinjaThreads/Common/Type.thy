(*  Title:      JinjaThreads/Common/Type.thy
    Author:     David von Oheimb, Tobias Nipkow, Andreas Lochbihler

    Based on the Jinja theory Common/Type.thy by David von Oheimb and Tobias Nipkow
*)

header {* \isaheader{Jinja types} *}

theory Type imports Aux begin

types
 cname = string -- "class names"
 mname = string -- "method name"
 vname = string -- "names for local/field variables"

constdefs
  Object :: cname
  "Object \<equiv> ''Object''"
  Thread :: cname
  "Thread \<equiv> ''Thread''"
  this :: vname
  "this \<equiv> ''this''"
  run :: mname
  "run \<equiv> ''run''"
  start :: mname
  "start \<equiv> ''start''"
  wait :: mname
  "wait \<equiv> ''wait''"
  notify :: mname
  "notify \<equiv> ''notify''"
  notifyAll :: mname
  "notifyAll \<equiv> ''notifyAll''"

lemma threadnobject [simp]: "Thread \<noteq> Object"
by(simp add: Thread_def Object_def)

-- "types"
datatype ty
  = Void          -- "type of statements"
  | Boolean
  | Integer
  | NT            -- "null type"
  | Class cname   -- "class type"
  | Array ty      ("_\<lfloor>\<rceil>" 95) -- "array type"

constdefs
  is_refT :: "ty \<Rightarrow> bool"
  "is_refT T  \<equiv>  T = NT \<or> (\<exists>C. T = Class C) \<or> (\<exists>A. T = Array A)"

constdefs
  is_refT_class :: "ty \<Rightarrow> bool"
  "is_refT_class T \<equiv> T = NT \<or> (\<exists>C. T = Class C)"

lemma [iff]: "is_refT NT"
(*<*)by(simp add:is_refT_def)(*>*)

lemma [iff]: "is_refT(Class C)"
(*<*)by(simp add:is_refT_def)(*>*)

lemma [iff]: "is_refT(A\<lfloor>\<rceil>)"
by(simp add:is_refT_def)

lemma [iff]: "is_refT_class NT"
(*<*)by(simp add:is_refT_class_def)(*>*)

lemma [iff]: "is_refT_class(Class C)"
(*<*)by(simp add:is_refT_class_def)(*>*)

lemma refTE:
  "\<lbrakk> is_refT T; T = NT \<Longrightarrow> P; \<And>C. T = Class C \<Longrightarrow> P; \<And>A. T = Array A \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
(*<*)by (auto simp add: is_refT_def)(*>*)

lemma not_refTE:
  "\<lbrakk> \<not>is_refT T; T = Void \<or> T = Boolean \<or> T = Integer \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
(*<*)by (cases T, auto simp add: is_refT_def)(*>*)

lemma refT_classE:
  "\<lbrakk>is_refT_class T; T = NT \<Longrightarrow> P; \<And>C. T = Class C \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
(*<*)by (auto simp add: is_refT_class_def)(*>*)

lemma not_refT_classE:
  "\<lbrakk> \<not>is_refT_class T; T = Void \<or> T = Boolean \<or> T = Integer \<or> (\<exists>A. T = Array A) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
(*<*)by (cases T, auto simp add: is_refT_class_def)(*>*)



end
