subsection\<open>ScottVariantHOMLAndersonQuant.thy (Figure 15 of \cite{J75})\<close>
text\<open>Verification of Scott’s variant of Gödel’s argument with a mixed use of actualist and possibilist quantifiers 
for entities; cf. Footnote 20 in \cite{J75}.\<close>
theory ScottVariantHOMLAndersonQuant imports HOMLinHOL ModalFilter
begin 

consts PositiveProperty::"(e\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("P") 

axiomatization where A1: "\<lfloor>\<^bold>\<not>P \<phi> \<^bold>\<leftrightarrow> P \<^bold>~\<phi>\<rfloor>" 

axiomatization where A2: "\<lfloor>P \<phi> \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>y. \<phi> y \<^bold>\<supset> \<psi> y) \<^bold>\<supset> P \<psi>\<rfloor>" 

theorem T1: "\<lfloor>P \<phi> \<^bold>\<supset> \<^bold>\<diamond>(\<^bold>\<exists>x. \<phi> x)\<rfloor>" using A1 A2 by smt

definition God ("G") where "G x \<equiv> \<^bold>\<forall>\<phi>. P \<phi> \<^bold>\<supset> \<phi> x"

axiomatization where A3: "\<lfloor>P G\<rfloor>" 

theorem Coro: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. G x)\<rfloor>" using A3 T1 by blast

axiomatization where A4: "\<lfloor>P \<phi> \<^bold>\<supset> \<^bold>\<box> P \<phi>\<rfloor>" 

definition Ess ("_Ess._") where "\<phi> Ess. x \<equiv> \<phi> x \<^bold>\<and> (\<^bold>\<forall>\<psi>. \<psi> x \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<forall>y::e. \<phi> y \<^bold>\<supset> \<psi> y))"

theorem T2: "\<lfloor>G x \<^bold>\<supset> G Ess. x\<rfloor>" using A1 A4 Ess_def God_def by smt

definition NecExist ("NE") where "NE x \<equiv> \<^bold>\<forall>\<phi>. \<phi> Ess. x \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ex. \<phi> x)"

axiomatization where A5: "\<lfloor>P NE\<rfloor>"

lemma True nitpick[satisfy,card=1,eval="\<lfloor>P (\<lambda>x.\<^bold>\<top>)\<rfloor>"] oops \<comment>\<open>One model found of cardinality one\<close>

theorem T3: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>Ex. G x)\<rfloor>" 
  \<comment>\<open>sledgehammer(A5 Coro God\_def NecExist\_def Rsymm T2)\<close> \<comment>\<open>Proof found\<close>
  proof -
    have 1: "\<lfloor>(G x \<^bold>\<supset> NE x) \<^bold>\<and> (G Ess. x \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ex. G x))\<rfloor>" using A5 Ess_def God_def NecExist_def by smt
    hence 2: "\<lfloor>(\<^bold>\<exists>x. G x) \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ex. G x)\<rfloor>" using A5 God_def NecExist_def T2 by smt
    hence 3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. G x) \<^bold>\<supset> (\<^bold>\<diamond>(\<^bold>\<box>(\<^bold>\<exists>x. G x)) \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ex. G x))\<rfloor>" using Rsymm by blast
    thus ?thesis using 2 Coro by blast
  qed

lemma MC: "\<lfloor>\<phi> \<^bold>\<supset> \<^bold>\<box>\<phi>\<rfloor>" 
  \<comment>\<open>sledgehammer(A1 A4 God\_def Rsymm T3)\<close> \<comment>\<open>Proof found\<close> 
  proof - {fix w fix Q
    have 1: "\<forall>x.(G x w \<longrightarrow> (\<^bold>\<forall>Z. Z x \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<forall>z.((G z) \<^bold>\<supset> (Z z)))) w)" using A1 A4 God_def by smt
    have 2: "(\<exists>x. G x w)\<longrightarrow>((Q \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<forall>z.((G z) \<^bold>\<supset> Q))) w)" using 1 by force
    have 3: "(Q \<^bold>\<supset> \<^bold>\<box>Q) w" using 2 T3 Rsymm by blast} 
   thus ?thesis by auto 
 qed

lemma PosProps: "\<lfloor>P (\<lambda>x.\<^bold>\<top>) \<^bold>\<and> P (\<lambda>x. x \<^bold>= x)\<rfloor>" using A1 A2 by blast
lemma NegProps: "\<lfloor>\<^bold>\<not>P(\<lambda>x.\<^bold>\<bottom>) \<^bold>\<and> \<^bold>\<not>P(\<lambda>x. x \<^bold>\<noteq> x)\<rfloor>" using A1 A2 by blast
lemma UniqueEss1: "\<lfloor>\<phi> Ess. x \<^bold>\<and> \<psi> Ess. x \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<forall>y. \<phi> y \<^bold>\<leftrightarrow> \<psi> y)\<rfloor>" using Ess_def by smt
lemma UniqueEss2: "\<lfloor>\<phi> Ess. x \<^bold>\<and> \<psi> Ess. x \<^bold>\<supset> \<^bold>\<box>(\<phi> \<^bold>= \<psi>)\<rfloor>" nitpick[card i=2] oops \<comment>\<open>Countermodel found\<close>
lemma UniqueEss3: "\<lfloor>\<phi> Ess. x \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<forall>y. \<phi> y \<^bold>\<supset> y \<^bold>\<equiv> x)\<rfloor>" using Ess_def MC by auto
lemma Monotheism: "\<lfloor>G x \<^bold>\<and> G y \<^bold>\<supset> x \<^bold>\<equiv> y\<rfloor>" using A1 God_def by smt
lemma Filter: "\<lfloor>Filter P\<rfloor>" using A1 God_def Rsymm T1 T3 by (smt (verit, best))
lemma UltraFilter: "\<lfloor>UFilter P\<rfloor>" using Filter A1 by blast
lemma True nitpick[satisfy,card=1,eval="\<lfloor>P (\<lambda>x.\<^bold>\<bottom>)\<rfloor>"] oops \<comment>\<open>One model found of cardinality one\<close>

end






