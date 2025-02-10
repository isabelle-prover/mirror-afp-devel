subsection\<open>ScottVariantHOMLinK.thy (Figure 13 of \cite{J75})\<close>
text\<open>Scott's variant of Gödel's argument fails for base logic K (but only it the last step).\<close>
theory ScottVariantHOMLinK imports HOMLinHOLonlyK
begin 

consts PositiveProperty::"(e\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("P") 

axiomatization where A1: "\<lfloor>\<^bold>\<not>P \<phi> \<^bold>\<leftrightarrow> P \<^bold>~\<phi>\<rfloor>"

axiomatization where A2: "\<lfloor>P \<phi> \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ey. \<phi> y \<^bold>\<supset> \<psi> y) \<^bold>\<supset> P \<psi>\<rfloor>" 

theorem T1: "\<lfloor>P \<phi> \<^bold>\<supset> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ex. \<phi> x)\<rfloor>" using A1 A2 by blast

definition God ("G") where "G x \<equiv> \<^bold>\<forall>\<phi>. P \<phi> \<^bold>\<supset> \<phi> x"

axiomatization where A3: "\<lfloor>P G\<rfloor>"

theorem Coro: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ex. G x)\<rfloor>" nitpick[satisfy,eval="G"] using A3 T1 by blast

axiomatization where A4: "\<lfloor>P \<phi> \<^bold>\<supset> \<^bold>\<box> P \<phi>\<rfloor>"

definition Ess ("_Ess._") where "\<phi> Ess. x \<equiv> \<phi> x \<^bold>\<and> (\<^bold>\<forall>\<psi>. \<psi> x \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ey. \<phi> y \<^bold>\<supset> \<psi> y))"

theorem T2: "\<lfloor>G x \<^bold>\<supset> G Ess. x\<rfloor>" using A1 A4 Ess_def God_def by fastforce

definition NecExist ("NE") where "NE x \<equiv> \<^bold>\<forall>\<phi>. \<phi> Ess. x \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ex. \<phi> x)"

axiomatization where A5: "\<lfloor>P NE\<rfloor>"

lemma True nitpick[satisfy,card=1,eval="\<lfloor>P (\<lambda>x.\<^bold>\<top>)\<rfloor>"] oops \<comment>\<open>One model found of cardinality one\<close>

theorem T3: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>Ex. G x)\<rfloor>" nitpick[card e=1, card i=2, eval="G"] oops \<comment>\<open>Counterexample\<close>

lemma MC: "\<lfloor>\<phi> \<^bold>\<supset> \<^bold>\<box>\<phi>\<rfloor>" nitpick[card e=1, card i=2, eval="G"] oops \<comment>\<open>Counterexample\<close>

end






