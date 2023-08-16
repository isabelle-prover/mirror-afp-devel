theory CFG
  imports Main
begin

section \<open>Adjusted content from AFP/LocalLexing\<close>

type_synonym 'a rule = "'a \<times> 'a list"

type_synonym 'a rules = "'a rule list"

type_synonym 'a sentence = "'a list"

datatype 'a cfg = 
  CFG (\<NN> : "'a list") (\<TT> : "'a list") (\<RR> : "'a rules") (\<SS> : "'a")

definition disjunct_symbols :: "'a cfg \<Rightarrow> bool" where
  "disjunct_symbols \<G> \<equiv> set (\<NN> \<G>) \<inter> set (\<TT> \<G>) = {}"

definition valid_startsymbol :: "'a cfg \<Rightarrow> bool" where
  "valid_startsymbol \<G> \<equiv> \<SS> \<G> \<in> set (\<NN> \<G>)"

definition valid_rules :: "'a cfg \<Rightarrow> bool" where
  "valid_rules \<G> \<equiv> \<forall>(N, \<alpha>) \<in> set (\<RR> \<G>). N \<in> set (\<NN> \<G>) \<and> (\<forall>s \<in> set \<alpha>. s \<in> set (\<NN> \<G>) \<union> set (\<TT> \<G>))"

definition distinct_rules :: "'a cfg \<Rightarrow> bool" where
  "distinct_rules \<G> \<equiv> distinct (\<RR> \<G>)"

definition wf_\<G> :: "'a cfg \<Rightarrow> bool" where
  "wf_\<G> \<G> \<equiv> disjunct_symbols \<G> \<and> valid_startsymbol \<G> \<and> valid_rules \<G> \<and> distinct_rules \<G>"

lemmas wf_\<G>_defs = wf_\<G>_def valid_rules_def valid_startsymbol_def disjunct_symbols_def distinct_rules_def

definition is_terminal :: "'a cfg \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_terminal \<G> x \<equiv> x \<in> set (\<TT> \<G>)"

definition is_nonterminal :: "'a cfg \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_nonterminal \<G> x \<equiv> x \<in> set (\<NN> \<G>)"

definition is_symbol :: "'a cfg \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_symbol \<G> x \<equiv> is_terminal \<G> x \<or> is_nonterminal \<G> x"

definition wf_sentence :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "wf_sentence \<G> \<omega> \<equiv> \<forall>x \<in> set \<omega>. is_symbol \<G> x"

lemma is_nonterminal_startsymbol:
  "wf_\<G> \<G> \<Longrightarrow> is_nonterminal \<G> (\<SS> \<G>)"
  by (simp add: is_nonterminal_def wf_\<G>_defs)

definition is_word :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "is_word \<G> \<omega> \<equiv> \<forall>x \<in> set \<omega>. is_terminal \<G> x"

definition derives1 :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "derives1 \<G> u v \<equiv> \<exists> x y N \<alpha>. 
    u = x @ [N] @ y \<and>
    v = x @ \<alpha> @ y \<and>
    (N, \<alpha>) \<in> set (\<RR> \<G>)"  

definition derivations1 :: "'a cfg \<Rightarrow> ('a sentence \<times> 'a sentence) set" where
  "derivations1 \<G> \<equiv> { (u,v) | u v. derives1 \<G> u v }"

definition derivations :: "'a cfg \<Rightarrow> ('a sentence \<times> 'a sentence) set" where 
  "derivations \<G> \<equiv> (derivations1 \<G>)^*"

definition derives :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "derives \<G> u v \<equiv> ((u, v) \<in> derivations \<G>)"

end