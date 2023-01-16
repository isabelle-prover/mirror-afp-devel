subsection\<open>Simplified Variant with Simple Entailment in Logic K (Fig.~8 in \<^cite>\<open>"C85"\<close>)\<close>

theory SimpleVariantSE imports 
  HOML 
  MFilter 
  BaseDefs
begin
text\<open>Axiom's of new variant based on ultrafilters.\<close> 
axiomatization where 
  A1': "\<lfloor>\<^bold>\<not>(\<P>(\<lambda>x.(x\<^bold>\<noteq>x)))\<rfloor>" and
  A2'': "\<lfloor>\<^bold>\<forall>X Y.(((\<P> X) \<^bold>\<and> (X\<^bold>\<sqsubseteq>Y)) \<^bold>\<rightarrow> (\<P> Y))\<rfloor>" and
  T2:  "\<lfloor>\<P> \<G>\<rfloor>" 

text\<open>Necessary existence of a Godlike entity.\<close>  
theorem T6: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" using A1' A2'' T2 by blast 
theorem T7: "\<lfloor>\<^bold>\<exists>\<^sup>E \<G>\<rfloor>" using A1' A2'' T2 by blast 

text\<open>Possible existence of a Godlike: has counterodel.\<close>  
lemma T3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" nitpick oops \<comment>\<open>Countermodel\<close>

lemma T3': assumes T: "\<lfloor>\<^bold>\<forall>\<phi>.((\<^bold>\<box>\<phi>) \<^bold>\<rightarrow> \<phi>)\<rfloor>" 
  shows "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" 
  using A1' A2'' T2 T by metis
end
