theory logics_consequence
  imports boolean_algebra
begin

section \<open>Logics based on Topological Boolean Algebras\<close>

subsection \<open>Logical Consequence and Validity\<close>

text\<open>Logical validity can be defined as truth in all points (i.e. as denoting the top element).\<close>
abbreviation (input) gtrue::"'w \<sigma> \<Rightarrow> bool" ("[\<turnstile> _]") 
  where  "[\<turnstile> A] \<equiv> \<forall>w. A w"   
lemma gtrue_def: "[\<turnstile> A] \<equiv> A \<^bold>= \<^bold>\<top>" by (simp add: setequ_def top_def)

text\<open>When defining a logic over an existing algebra we have two choices: a global (truth preserving)
and a local (degree preserving) notion of logical consequence. For LFIs/LFUs we prefer the latter.\<close>
abbreviation (input) conseq_global1::"'w \<sigma> \<Rightarrow> 'w \<sigma>\<Rightarrow>bool" ("[_ \<turnstile>\<^sub>g _]") 
  where "[A \<turnstile>\<^sub>g B] \<equiv> [\<turnstile> A] \<longrightarrow> [\<turnstile> B]"
abbreviation (input) conseq_global21::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> bool" ("[_,_ \<turnstile>\<^sub>g _]") 
  where "[A\<^sub>1, A\<^sub>2 \<turnstile>\<^sub>g B] \<equiv> [\<turnstile> A\<^sub>1] \<and> [\<turnstile> A\<^sub>2] \<longrightarrow> [\<turnstile> B]"
abbreviation (input) conseq_global31::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> bool" ("[_,_,_ \<turnstile>\<^sub>g _]") 
  where "[A\<^sub>1, A\<^sub>2, A\<^sub>3 \<turnstile>\<^sub>g B] \<equiv> [\<turnstile> A\<^sub>1] \<and> [\<turnstile> A\<^sub>2] \<and> [\<turnstile> A\<^sub>3] \<longrightarrow> [\<turnstile> B]"

abbreviation (input) conseq_local1::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> bool" ("[_ \<turnstile> _]") 
  where "[A \<turnstile> B] \<equiv> A \<^bold>\<le> B"
abbreviation (input) conseq_local21::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> bool" ("[_,_ \<turnstile> _]") 
  where "[A\<^sub>1, A\<^sub>2 \<turnstile> B] \<equiv> A\<^sub>1 \<^bold>\<and> A\<^sub>2 \<^bold>\<le> B"
abbreviation (input) conseq_local12::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> bool" ("[_ \<turnstile> _,_]") 
  where "[A \<turnstile> B\<^sub>1, B\<^sub>2] \<equiv> A \<^bold>\<le> B\<^sub>1 \<^bold>\<or> B\<^sub>2"
abbreviation (input) conseq_local31::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> bool" ("[_,_,_ \<turnstile> _]") 
  where "[A\<^sub>1, A\<^sub>2, A\<^sub>3 \<turnstile> B] \<equiv> A\<^sub>1 \<^bold>\<and> A\<^sub>2 \<^bold>\<and> A\<^sub>3 \<^bold>\<le> B"
(*add more as the need arises...*)

end
