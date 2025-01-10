section\<open>Interactive and automated theorem proving\<close>
subsection\<open>SurjectiveCantor.thy (Figure 2 of \cite{J75})\<close>
text\<open>The surjective Cantor theorem is used in \cite{J75} to illustrate some aspects of interactive and 
automated theorem proving in Isabelle/HOL as relevant for the paper. To keep the provided data material complete 
wrt. \cite{J75}, we include these data sources also here.\<close>
theory SurjectiveCantor imports Main
begin 
text\<open>Surjective Cantor theorem: traditional interactive proof\<close>
theorem SurjectiveCantor: "\<not>(\<exists>G.\<forall>F::'a\<Rightarrow>bool.\<exists>X::'a. G X = F)" 
  proof
    assume 1: "\<exists>G.\<forall>F::'a\<Rightarrow>bool.\<exists>X::'a. G X = F" 
    obtain g::"'a\<Rightarrow>('a\<Rightarrow>bool)" where 2: "\<forall>F.\<exists>X. g X = F" using 1 by auto 
    let ?F = "\<lambda>X.\<not> g X X" 
    have 3: "\<exists>Y. g Y = ?F" using 2 by metis 
    obtain a::'a where 4: "g a = ?F" using 3 by auto 
    have 5: "g a a = ?F a" using 4 by metis 
    have 6: "g a a = (\<not> g a a)" using 5 by auto 
    show False using 6 by auto 
  qed
text\<open>Avoiding proof by contradiction (Fuenmayor \<open>&\<close> Benzmüller, 2021)\<close>
theorem SurjectiveCantor': "\<not>(\<exists>G.\<forall>F::'a\<Rightarrow>bool.\<exists>X::'a. G X = F)" 
  proof - 
    {fix g :: "'a\<Rightarrow>('a\<Rightarrow>bool)"
      have 1: "\<forall>X.\<exists>Y.(\<not>g X Y) = (\<not>g Y Y)" by auto 
      have 2: "\<forall>X.\<exists>Y.(\<not>g X Y) = ((\<lambda>Z.\<not>g Z Z) Y)" using 1 by auto 
      have 3: "\<exists>F.\<forall>X.\<exists>Y.(\<not>g X Y) = (F Y)" using 2 by auto
      have 4: "\<exists>F.\<forall>X.\<not>(\<forall>Y.(g X Y) = (F Y))" using 3 by auto 
      have "\<exists>F.\<forall>X.\<not>(g X = F)" using 4 by metis 
    }
    hence 5: "\<forall>G.\<exists>F::'a\<Rightarrow>bool.\<forall>X::'a.\<not>(G X = F)" by auto 
    have 6: "\<not>(\<exists>G.\<forall>F::'a\<Rightarrow>bool.\<exists>X::'a. G X = F)" using 5 by auto 
    thus ?thesis . \<comment>\<open>done, avoiding proof by contradiction\<close>
  qed
text\<open>Surjective Cantor theorem: automated proof by some internal/external theorem provers\<close>
theorem SurjectiveCantor'': "\<not>(\<exists>G.\<forall>F::'a\<Rightarrow>bool.\<exists>X::'a. G X = F)" 
  nitpick[expect=none] \<comment>\<open>no counterexample found\<close> 
  \<comment>\<open>sledgehammer\<close> \<comment>\<open>most internal provers give up\<close>
  \<comment>\<open>sledgehammer[remote\_leo2 remote\_leo3]\<close> \<comment>\<open>proof found: leo provers succeed\<close>
  oops
text\<open>Surjective Cantor theorem (wrong formalization attempt): the types are crucial\<close>
theorem SurjectiveCantor''': "\<not>(\<exists>G.\<forall>F::'b.\<exists>X::'a. G X = F)" 
  nitpick \<comment>\<open>counterexample found for card 'a = 1 and card 'b = 1: G=(\<open>\<lambda>\<close>x. (a1 := b1)\<close>
  nitpick[satisfy, expect=genuine] \<comment>\<open>model found for card 'a = 1 and card 'b = 2\<close>
  nitpick[card 'a=2, card 'b=3, expect=none] \<comment>\<open>no counterexample found\<close> 
  oops 
end





