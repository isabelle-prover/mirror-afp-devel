subsection\<open>Simplified Variant with Axiom T2 (Fig.~7 in \<^cite>\<open>"C85"\<close>)\<close>

theory SimpleVariantPG imports 
  HOML 
  MFilter 
  BaseDefs
begin
text\<open>Axiom's of simplified variant with A3 replaced.\<close> 
axiomatization where 
  A1': "\<lfloor>\<^bold>\<not>(\<P>(\<lambda>x.(x\<^bold>\<noteq>x)))\<rfloor>" and
  A2': "\<lfloor>\<^bold>\<forall>X Y.(((\<P> X) \<^bold>\<and> ((X\<^bold>\<sqsubseteq>Y)\<^bold>\<or>(X\<Rrightarrow>Y))) \<^bold>\<rightarrow> (\<P> Y))\<rfloor>" and
  T2:  "\<lfloor>\<P> \<G>\<rfloor>"

text\<open>Necessary existence of a Godlike entity.\<close> 
theorem T6:  "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>"  \<comment>\<open>Proof found by sledgehammer\<close>
proof -
  have T1: "\<lfloor>\<^bold>\<forall>X.((\<P> X) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E X))\<rfloor>" by (metis A1' A2') 
  have T3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" using T1 T2 by simp
  have T5: "\<lfloor>(\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" by (metis A1' A2' T2)
  thus ?thesis using T3 by blast qed

lemma True nitpick[satisfy] oops  \<comment>\<open>Consistency: model found\<close>

text\<open>Modal collapse and Monotheism: not implied.\<close>
lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> \<^bold>\<box>\<Phi>)\<rfloor>" nitpick oops  \<comment>\<open>Countermodel\<close>
lemma MT: "\<lfloor>\<^bold>\<forall>x y.(((\<G> x)\<^bold>\<and>(\<G> y))\<^bold>\<rightarrow>(x\<^bold>=y))\<rfloor>" nitpick oops  \<comment>\<open>Countermodel\<close>
end
