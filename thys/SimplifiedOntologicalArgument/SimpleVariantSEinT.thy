subsection\<open>Simplified Variant with Simple Entailment in Logic T (Fig.~9 in \<^cite>\<open>"C85"\<close>)\<close>

theory SimpleVariantSEinT imports 
  HOML 
  MFilter 
  BaseDefs
begin
text\<open>Axiom's of new variant based on ultrafilters.\<close> 
axiomatization where 
  A1': "\<lfloor>\<^bold>\<not>(\<P>(\<lambda>x.(x\<^bold>\<noteq>x)))\<rfloor>" and
  A2'': "\<lfloor>\<^bold>\<forall>X Y.(((\<P> X) \<^bold>\<and> (X\<^bold>\<sqsubseteq>Y)) \<^bold>\<rightarrow> (\<P> Y))\<rfloor>" and
  T2:   "\<lfloor>\<P> \<G>\<rfloor>" 

text\<open>Modal Logic T.\<close> 
axiomatization where T: "\<lfloor>\<^bold>\<forall>\<phi>.((\<^bold>\<box>\<phi>) \<^bold>\<rightarrow> \<phi>)\<rfloor>" 
lemma T': "\<lfloor>\<^bold>\<forall>\<phi>.(\<phi> \<^bold>\<rightarrow> (\<^bold>\<diamond>\<phi>))\<rfloor>" by (metis T)

text\<open>Necessary existence of a Godlike entity.\<close> 
theorem T6: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>"  \<comment>\<open>Proof found by sledgehammer\<close>
proof -
  have T1: "\<lfloor>\<^bold>\<forall>X.((\<P> X)\<^bold>\<rightarrow>(\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E X)))\<rfloor>" by (metis A1' A2'' T') 
  have T3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" by (metis T1 T2)
  have T5: "\<lfloor>(\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" by (metis A1' A2'' T2) 
  thus ?thesis using T3 by simp qed

text\<open>T6 again, with an alternative, simpler proof.\<close>
theorem T6again: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>"  
proof -
  have L1: "\<lfloor>(\<^bold>\<exists>X.((\<P> X)\<^bold>\<and>\<^bold>\<not>(\<^bold>\<exists>\<^sup>EX)))\<^bold>\<rightarrow>(\<P>(\<lambda>x.(x\<^bold>\<noteq>x)))\<rfloor>" 
    by (smt A2'') 
  have L2: "\<lfloor>\<^bold>\<not>(\<^bold>\<exists>X.((\<P> X) \<^bold>\<and> \<^bold>\<not>(\<^bold>\<exists>\<^sup>E X)))\<rfloor>" by (metis L1 A1')
  have T1': "\<lfloor>\<^bold>\<forall>X.((\<P> X) \<^bold>\<rightarrow> (\<^bold>\<exists>\<^sup>E X))\<rfloor>" by (metis L2)  
  have T3': "\<lfloor>\<^bold>\<exists>\<^sup>E \<G>\<rfloor>" by (metis T1' T2)
  have L3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" by (metis T3' T') \<comment>\<open>not needed\<close>
  thus ?thesis using T3' by simp qed
end

