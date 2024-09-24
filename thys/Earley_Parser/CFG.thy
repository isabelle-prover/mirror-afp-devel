theory CFG
  imports Main
begin

section \<open>Adjusted content from AFP/LocalLexing\<close>

type_synonym 'a rule = "'a \<times> 'a list"

type_synonym 'a rules = "'a rule list"

datatype 'a cfg = CFG (\<RR> : "'a rules") (\<SS> : "'a")

definition nonterminals :: "'a cfg \<Rightarrow> 'a set" where
  "nonterminals G = set (map fst (\<RR> G)) \<union> {\<SS> G}"

definition is_word :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> bool" where
  "is_word \<G> \<omega> = (nonterminals \<G> \<inter> set \<omega> = {})"

definition derives1 :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "derives1 \<G> u v \<equiv> \<exists> x y A \<alpha>. 
    u = x @ [A] @ y \<and>
    v = x @ \<alpha> @ y \<and>
    (A, \<alpha>) \<in> set (\<RR> \<G>)"  

definition derivations1 :: "'a cfg \<Rightarrow> ('a list \<times> 'a list) set" where
  "derivations1 \<G> \<equiv> { (u,v) | u v. derives1 \<G> u v }"

definition derivations :: "'a cfg \<Rightarrow> ('a list \<times> 'a list) set" where 
  "derivations \<G> \<equiv> (derivations1 \<G>)^*"

definition derives :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "derives \<G> u v \<equiv> ((u, v) \<in> derivations \<G>)"

syntax
  "derives1" :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" (\<open>_ \<turnstile> _ \<Rightarrow> _\<close> [1000,0,0] 1000)

syntax
  "derives" :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" (\<open>_ \<turnstile> _ \<Rightarrow>\<^sup>* _\<close> [1000,0,0] 1000)

notation (latex output)
  derives1 (\<open>_ \<turnstile> _ \<Rightarrow> _\<close> [1000,0,0] 1000)

notation (latex output)
  derives (\<open>_ \<turnstile> _ \<^latex>\<open>\ensuremath{\Rightarrow^{\ast}}\<close> _\<close> [1000,0,0] 1000)

end