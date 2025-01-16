subsection\<open>EvilDerivable.thy (Figure 20 of \cite{J75})\<close>
text\<open>The necessary existence of an Evil-like entity proved from (controversially) modified assumptions.
By rejecting Gödel’s assumptions and instead postulating corresponding negative versions of them, 
as shown in the Figure 20, the necessary existence of Evil becomes derivable. 
The non-positive properties of this Evil-like entity are however identical to the positive 
properties of Gödel’s God-like entity.\<close>
theory EvilDerivable imports HOMLinHOL ModalFilter
begin 

consts PositiveProperty::"(e\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("P") 

definition Evil ("Evil") where "Evil x \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<not> P \<phi> \<^bold>\<supset> \<phi> x"

definition Essence ("_Ess._") where "\<phi> Ess. x \<equiv> \<phi> x \<^bold>\<and> (\<^bold>\<forall>\<psi>. \<psi> x \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ey. \<phi> y \<^bold>\<supset> \<psi> y))"

definition NecExist ("E") where "E x \<equiv> \<^bold>\<forall>\<phi>. \<phi> Ess. x \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ex. \<phi> x)"

axiomatization where A1: "\<lfloor>\<^bold>\<not>P \<phi> \<^bold>\<leftrightarrow> P \<^bold>~\<phi>\<rfloor>"

axiomatization where A2: "\<lfloor>\<^bold>\<not>P \<phi> \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ey. \<phi> y \<^bold>\<supset> \<psi> y) \<^bold>\<supset> \<^bold>\<not>P \<psi>\<rfloor>"

axiomatization where A4: "\<lfloor>\<^bold>\<not>P Evil\<rfloor>"

axiomatization where A3: "\<lfloor>\<^bold>\<not>P \<phi> \<^bold>\<supset> \<^bold>\<box> (\<^bold>\<not>P \<phi>)\<rfloor>"

axiomatization where A5: "\<lfloor>\<^bold>\<not>P E\<rfloor>"

lemma True nitpick[satisfy,card i=1,eval="\<lfloor>P (\<lambda>x.\<^bold>\<bottom>)\<rfloor>",eval="\<lfloor>P (\<lambda>x.\<^bold>\<top>)\<rfloor>"] oops \<comment>\<open>Model found\<close>

theorem T1: "\<lfloor>\<^bold>\<not>P \<phi> \<^bold>\<supset> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ex. \<phi> x)\<rfloor>" using A1 A2 by blast

theorem T2: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ex. Evil x)\<rfloor>" using A4 T1 by blast

theorem T3: "\<lfloor>Evil x \<^bold>\<supset> Evil Ess. x\<rfloor>" using A1 A3 Essence_def Evil_def by (smt (verit, best))

theorem T4: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ex. Evil x) \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ey. Evil y)\<rfloor>" using A5 Evil_def NecExist_def Rsymm T3 by smt

theorem T5: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>Ex. Evil x)\<rfloor>" using T2 T4 by presburger

lemma MC: "\<lfloor>\<phi> \<^bold>\<supset> \<^bold>\<box>\<phi>\<rfloor>" 
  \<comment>\<open>sledgehammer(A1 A3 T5 Evil\_def Rsymm)\<close> oops \<comment>\<open>proof found\<close>

lemma PosProps: "\<lfloor>P (\<lambda>x.\<^bold>\<bottom>) \<^bold>\<and> P (\<lambda>x. x \<^bold>\<noteq> x)\<rfloor>" using A1 A2 by blast
lemma NegProps: "\<lfloor>\<^bold>\<not>P(\<lambda>x.\<^bold>\<top>) \<^bold>\<and> \<^bold>\<not>P(\<lambda>x. x \<^bold>= x)\<rfloor>" using A1 A2 by blast
lemma UniqueEss1: "\<lfloor>\<phi> Ess. x \<^bold>\<and> \<psi> Ess. x \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ey. \<phi> y \<^bold>\<leftrightarrow> \<psi> y)\<rfloor>" using Essence_def by smt
lemma UniqueEss2: "\<lfloor>\<phi> Ess. x \<^bold>\<and> \<psi> Ess. x \<^bold>\<supset> \<^bold>\<box>(\<phi> \<^bold>= \<psi>)\<rfloor>" nitpick[card i=2] oops \<comment>\<open>Countermodel found\<close>
lemma Monoevilism: "\<lfloor>Evil x \<^bold>\<and> Evil y \<^bold>\<supset> x \<^bold>\<equiv> y\<rfloor>" using A1 Evil_def by smt
lemma Filter: "\<lfloor>Filter (\<lambda> \<phi>. \<^bold>\<not>P \<phi>)\<rfloor>" using A1 Evil_def Rsymm T1 T5 by (smt (verit, best))
lemma UltraFilter: "\<lfloor>UFilter (\<lambda> \<phi>. \<^bold>\<not>P \<phi>)\<rfloor>" using Filter A1 by blast

end
