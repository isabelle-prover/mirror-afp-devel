(*  ID:         $Id: TameEnum.thy,v 1.1 2006-05-22 09:54:04 nipkow Exp $
    Author:     Gertrud Bauer, Tobias Nipkow
*)

header {* Neglectable Final Graphs *}

theory TameEnum
imports Generator Plane4
begin

constdefs
 is_tame :: "graph \<Rightarrow> bool"
"is_tame g  \<equiv>  tame\<^isub>4\<^isub>5 g \<and> tame\<^isub>6 g \<and> tame\<^isub>8 g \<and> is_tame\<^isub>7 g \<and> is_tame\<^isub>3 g"

constdefs
 next_tame :: "nat \<Rightarrow> graph \<Rightarrow> graph list"  ("next'_tame\<^bsub>_\<^esub>")
 "next_tame\<^bsub>p\<^esub> \<equiv> filter (\<lambda>g. \<not> final g \<or> is_tame g) o next_tame1\<^bsub>p\<^esub>"

constdefs
 TameEnumP :: "nat \<Rightarrow> graph set" ("TameEnum\<^bsub>_\<^esub>")
"TameEnum\<^bsub>p\<^esub> \<equiv> {g. Seed\<^bsub>p\<^esub> [next_tame\<^bsub>p\<^esub>]\<rightarrow>* g \<and> final g}"

 TameEnum :: "graph set"
"TameEnum \<equiv> \<Union>p\<le>5. TameEnum\<^bsub>p\<^esub>"

end