(* Author: Daniel Wasserrab
   Based on the Jinja theory Common/Decl.thy by David von Oheimb *)

header {* Class Declarations and Programs *}

theory Decl imports Expr begin

types
  fdecl    = "vname \<times> ty"                        -- "field declaration"
  method = "ty list \<times> ty \<times> (vname list \<times> expr)"    -- "arg.\ types, return type, params, body"
  mdecl = "mname \<times> method"                         -- "method declaration"
  class = "base list \<times> fdecl list \<times> mdecl list"  -- "class = superclasses, fields, methods"
  cdecl = "cname \<times> class"                        -- "classa declaration"
  prog  = "cdecl list"                           -- "program"


translations
  "fdecl" <= (type) "vname \<times> ty"
  "mdecl" <= (type) "mname \<times> ty list \<times> ty \<times> (vname list \<times> expr)"
  "class" <= (type) "cname \<times> fdecl list \<times> mdecl list"
  "cdecl" <= (type) "cname \<times> class"
  "prog " <= (type) "cdecl list"


constdefs
  class :: "prog \<Rightarrow> cname \<rightharpoonup> class"
  "class \<equiv> map_of"

  is_class :: "prog \<Rightarrow> cname \<Rightarrow> bool"
  "is_class P C \<equiv> class P C \<noteq> None"

  baseClasses :: "base list \<Rightarrow> cname set"
  "baseClasses Bs \<equiv> set ((map getbase) Bs)"

  RepBases :: "base list \<Rightarrow> cname set"
  "RepBases Bs \<equiv> set ((map getbase) (filter isRepBase Bs))"

  SharedBases :: "base list \<Rightarrow> cname set"
  "SharedBases Bs \<equiv> set ((map getbase) (filter isShBase Bs))"


lemma not_getbase_repeats:
  "D \<notin> set (map getbase xs) \<Longrightarrow> Repeats D \<notin> set xs"
by (induct rule:set.induct, auto)

lemma not_getbase_shares:
  "D \<notin> set (map getbase xs) \<Longrightarrow> Shares D \<notin> set xs"
by (induct rule:set.induct, auto)


lemma RepBaseclass_isBaseclass:
  "\<lbrakk>class P C = Some(Bs,fs,ms); Repeats D \<in> set Bs\<rbrakk>
\<Longrightarrow> D \<in> baseClasses Bs"
by (simp add:baseClasses_def, induct rule:set.induct, 
  auto simp:not_getbase_repeats)

lemma ShBaseclass_isBaseclass:
  "\<lbrakk>class P C = Some(Bs,fs,ms); Shares D \<in> set Bs\<rbrakk>
\<Longrightarrow> D \<in> baseClasses Bs"
by (simp add:baseClasses_def, induct rule:set.induct, 
  auto simp:not_getbase_shares)

lemma base_repeats_or_shares:
  "\<lbrakk>B \<in> set Bs; D = getbase B\<rbrakk> 
\<Longrightarrow> Repeats D \<in> set Bs \<or> Shares D \<in> set Bs"
by(induct B rule:base.induct) simp+

lemma baseClasses_repeats_or_shares:
  "D \<in> baseClasses Bs \<Longrightarrow> Repeats D \<in> set Bs \<or> Shares D \<in> set Bs"
by (auto elim!:bexE base_repeats_or_shares 
  simp add:baseClasses_def image_def)


lemma finite_is_class: "finite {C. is_class P C}"

apply (unfold is_class_def class_def)
apply (fold dom_def)
apply (rule finite_dom_map_of)
done


lemma finite_baseClasses: 
  "class P C = Some(Bs,fs,ms) \<Longrightarrow> finite (baseClasses Bs)"

apply (unfold is_class_def class_def baseClasses_def)
apply clarsimp
done



constdefs
  is_type :: "prog \<Rightarrow> ty \<Rightarrow> bool"
  "is_type P T  \<equiv>
  (case T of Void \<Rightarrow> True | Boolean \<Rightarrow> True | Integer \<Rightarrow> True | NT \<Rightarrow> True
   | Class C \<Rightarrow> is_class P C)"

lemma is_type_simps [simp]:
  "is_type P Void \<and> is_type P Boolean \<and> is_type P Integer \<and>
  is_type P NT \<and> is_type P (Class C) = is_class P C"
by(simp add:is_type_def)

translations
  "types P" == "Collect (is_type P)"

lemma typeof_lit_is_type: 
  "typeof v = Some T \<Longrightarrow> is_type P T"
 by (induct v) (auto)


end
