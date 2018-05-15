section {* Basic lemmas about functions *}

theory FunctionLemmas

imports Main
  "HOL-Library.FuncSet"
begin

text {*These are used in simplification. Note that the difference from Pi-mem is that the statement
about the function comes first, so Isabelle can more easily figure out what $S$ is.*}

lemma PiE_mem2: "f \<in> S\<rightarrow>\<^sub>E T \<Longrightarrow> x \<in> S \<Longrightarrow> f x \<in> T"
  unfolding PiE_def by auto
lemma Pi_mem2: "f \<in> S\<rightarrow> T \<Longrightarrow> x \<in> S \<Longrightarrow> f x \<in> T"
  unfolding Pi_def by auto

end
