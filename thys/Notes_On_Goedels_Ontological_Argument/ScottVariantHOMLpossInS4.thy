subsection\<open>ScottVariantHOMLpossInS4.thy\<close>
text\<open>\<close>
theory ScottVariantHOMLpossInS4 imports HOMLinHOLonlyS4 
begin 

consts PositiveProperty::"(e\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("P") 

axiomatization where A1: "\<lfloor>\<^bold>\<not>P \<phi> \<^bold>\<leftrightarrow> P \<^bold>~\<phi>\<rfloor>" 

axiomatization where A2: "\<lfloor>P \<phi> \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>y. \<phi> y \<^bold>\<supset> \<psi> y) \<^bold>\<supset> P \<psi>\<rfloor>"

theorem T1: "\<lfloor>P \<phi> \<^bold>\<supset> \<^bold>\<diamond>(\<^bold>\<exists>x. \<phi> x)\<rfloor>" using A1 A2 by blast

definition God ("G") where "G x \<equiv> \<^bold>\<forall>\<phi>. P \<phi> \<^bold>\<supset> \<phi> x"

axiomatization where A3: "\<lfloor>P G\<rfloor>"

theorem Coro: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. G x)\<rfloor>" using A3 T1 by blast

axiomatization where A4: "\<lfloor>P \<phi> \<^bold>\<supset> \<^bold>\<box> P \<phi>\<rfloor>"

definition Ess ("_Ess._") where "\<phi> Ess. x \<equiv> \<phi> x \<^bold>\<and> (\<^bold>\<forall>\<psi>. \<psi> x \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<forall>y::e. \<phi> y \<^bold>\<supset> \<psi> y))"

theorem T2: "\<lfloor>G x \<^bold>\<supset> G Ess. x\<rfloor>" using A1 A4 Ess_def God_def by fastforce

definition NecExist ("NE") where "NE x \<equiv> \<^bold>\<forall>\<phi>. \<phi> Ess. x \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>x. \<phi> x)"

axiomatization where A5: "\<lfloor>P NE\<rfloor>"

lemma True nitpick[satisfy,card=1,eval="\<lfloor>P (\<lambda>x.\<^bold>\<bottom>)\<rfloor>"] oops \<comment>\<open>One model found of cardinality one\<close>

theorem T3: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>x. G x)\<rfloor>" nitpick[card e=1, card i=2] oops \<comment>\<open>Countermodel found\<close>

lemma MC: "\<lfloor>\<phi> \<^bold>\<supset> \<^bold>\<box>\<phi>\<rfloor>" nitpick[card e=1, card i=2] oops \<comment>\<open>Countermodel found\<close>

end



