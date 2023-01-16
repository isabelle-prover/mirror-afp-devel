subsection\<open>Simplified Variant (Fig.~6 in \<^cite>\<open>"C85"\<close>)\<close>

theory SimpleVariant imports 
  HOML 
  MFilter 
  BaseDefs
begin
text\<open>Axiom's of new, simplified variant.\<close>
axiomatization where 
  A1': "\<lfloor>\<^bold>\<not>(\<P>(\<lambda>x.(x\<^bold>\<noteq>x)))\<rfloor>" and 
  A2': "\<lfloor>\<^bold>\<forall>X Y.(((\<P> X) \<^bold>\<and> ((X\<^bold>\<sqsubseteq>Y) \<^bold>\<or> (X\<Rrightarrow>Y))) \<^bold>\<rightarrow> (\<P> Y))\<rfloor>" and
  A3:  "\<lfloor>\<^bold>\<forall>\<Z>.((\<P>\<o>\<s> \<Z>) \<^bold>\<rightarrow> (\<^bold>\<forall>X.((X\<Sqinter>\<Z>) \<^bold>\<rightarrow> (\<P> X))))\<rfloor>" 

lemma T2: "\<lfloor>\<P> \<G>\<rfloor>" by (metis A3 G_def) \<comment>\<open>From A3\<close>
lemma L1: "\<lfloor>\<P>(\<lambda>x.(x\<^bold>=x))\<rfloor>" by (metis A2' A3) 

text\<open>Necessary existence of a Godlike entity.\<close> 
theorem T6: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>"  \<comment>\<open>Proof found by sledgehammer\<close>
proof -
  have T1: "\<lfloor>\<^bold>\<forall>X.((\<P> X) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E X))\<rfloor>" by (metis A1' A2') 
  have T3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" using T1 T2 by simp
  have T5: "\<lfloor>(\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" by (metis A1' A2' T2)
  thus ?thesis using T3 by blast qed

lemma True nitpick[satisfy] oops \<comment>\<open>Consistency: model found\<close>

text\<open>Modal collapse and monotheism: not implied.\<close>
lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> \<^bold>\<box>\<Phi>)\<rfloor>" nitpick oops \<comment>\<open>Countermodel\<close>
lemma MT: "\<lfloor>\<^bold>\<forall>x y.(((\<G> x) \<^bold>\<and> (\<G> y)) \<^bold>\<rightarrow> (x\<^bold>=y))\<rfloor>" 
  nitpick oops \<comment>\<open>Countermodel.\<close>

text\<open>Gödel's A1, A4, A5: not implied anymore.\<close>
lemma A1: "\<lfloor>\<^bold>\<forall>X.((\<^bold>\<not>(\<P> X))\<^bold>\<leftrightarrow>(\<P>(\<^bold>\<rightharpoondown>X)))\<rfloor>" nitpick oops \<comment>\<open>Countermodel\<close>
lemma A4: "\<lfloor>\<^bold>\<forall>X.((\<P> X) \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X))\<rfloor>" nitpick oops \<comment>\<open>Countermodel\<close>
lemma A5: "\<lfloor>\<P> \<N>\<E>\<rfloor>" nitpick oops \<comment>\<open>Countermodel\<close>

text\<open>Checking filter and ultrafilter properties.\<close> 
theorem F1: "\<lfloor>Filter \<P>\<rfloor>" oops \<comment>\<open>Proof found by sledgehammer, but reconstruction timeout\<close>
theorem U1: "\<lfloor>UFilter \<P>\<rfloor>" nitpick oops  \<comment>\<open>Countermodel\<close>
end

