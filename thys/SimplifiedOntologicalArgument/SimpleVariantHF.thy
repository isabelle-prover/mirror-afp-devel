subsection\<open>Hauptfiltervariant (Fig.~10 in \<^cite>\<open>"C85"\<close>)\<close>

theory SimpleVariantHF imports
  HOML 
  MFilter 
  BaseDefs
begin
text\<open>Definition: Set of supersets of \<open>X\<close>, we call this \<open>\<H>\<F> X\<close>.\<close>
abbreviation HF::"\<gamma>\<Rightarrow>(\<gamma>\<Rightarrow>\<sigma>)"  where "HF X \<equiv> \<lambda>Y.(X\<^bold>\<sqsubseteq>Y)"

text\<open>Postulate: \<open>\<H>\<F> \<G>\<close> is a filter; i.e., Hauptfilter of \<open>\<G>\<close>.\<close> 
axiomatization where F1: "\<lfloor>Filter (HF \<G>)\<rfloor>" 

text\<open>Necessary existence of a Godlike entity.\<close> 
theorem T6: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" using F1 by auto \<comment>\<open>Proof found\<close>

theorem T6again: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>"  
proof -
 have T3': "\<lfloor>\<^bold>\<exists>\<^sup>E \<G>\<rfloor>" using F1 by auto
 have T6:  "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" using T3' by blast 
 thus ?thesis by simp qed

text\<open>Possible existence of Godlike entity not implied.\<close>
lemma T3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" nitpick oops  \<comment>\<open>Countermodel\<close>

text\<open>Axiom T enforces possible existence of Godlike entity.\<close>
axiomatization 
lemma T3: assumes T: "\<lfloor>\<^bold>\<forall>\<phi>.((\<^bold>\<box>\<phi>) \<^bold>\<rightarrow> \<phi>)\<rfloor>"
          shows "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>E \<G>)\<rfloor>" using F1 T by auto

lemma True nitpick[satisfy] oops \<comment>\<open>Consistency: model found\<close>

text\<open>Modal collapse: not implied anymore.\<close>
lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> \<^bold>\<box>\<Phi>)\<rfloor>" nitpick oops  \<comment>\<open>Countermodel\<close>
lemma MT: "\<lfloor>\<^bold>\<forall>x y.(((\<G> x) \<^bold>\<and> (\<G> y)) \<^bold>\<rightarrow> (x\<^bold>=y))\<rfloor>" 
          nitpick oops \<comment>\<open>Countermodel\<close>
end

