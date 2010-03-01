(*  Author:     Gertrud Bauer, Tobias Nipkow
*)

header {* Neglectable Final Graphs *}

theory TameEnum
imports Generator Plane4
begin

definition is_tame :: "graph \<Rightarrow> bool" where
  "is_tame g  \<equiv>  tame\<^isub>4\<^isub>5 g \<and> tame\<^isub>6 g \<and> tame\<^isub>8 g \<and> is_tame\<^isub>7 g \<and> is_tame\<^isub>3 g"

definition next_tame :: "nat \<Rightarrow> graph \<Rightarrow> graph list" ("next'_tame\<^bsub>_\<^esub>") where
  "next_tame\<^bsub>p\<^esub> \<equiv> filter (\<lambda>g. \<not> final g \<or> is_tame g) o next_tame1\<^bsub>p\<^esub>"

definition TameEnumP :: "nat \<Rightarrow> graph set" ("TameEnum\<^bsub>_\<^esub>") where
  "TameEnum\<^bsub>p\<^esub> \<equiv> {g. Seed\<^bsub>p\<^esub> [next_tame\<^bsub>p\<^esub>]\<rightarrow>* g \<and> final g}"

definition TameEnum :: "graph set" where
  "TameEnum \<equiv> \<Union>p\<le>5. TameEnum\<^bsub>p\<^esub>"

end