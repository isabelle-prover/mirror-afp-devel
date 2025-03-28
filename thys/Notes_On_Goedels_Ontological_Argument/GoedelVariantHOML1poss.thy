section\<open>Appendix\<close>
subsection\<open>GoedelVariantHOML1poss.thy (Figure 16 of \cite{J75})\<close>
text\<open>Gödel's axioms and definitions, as presented in the 1970 manuscript, are inconsistent. 
In contrast to Figure 6 we here use only possibilist quantifiers and still derive falsity.\<close>
theory GoedelVariantHOML1poss imports HOMLinHOL
begin 

consts PositiveProperty::"(e\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("P") 

axiomatization where Ax1: "\<lfloor>P \<phi> \<^bold>\<and> P \<psi> \<^bold>\<supset> P (\<phi> \<^bold>. \<psi>)\<rfloor>"

axiomatization where Ax2a: "\<lfloor>P \<phi> \<^bold>\<or>\<^sup>e P \<^bold>~\<phi>\<rfloor>" 

definition God ("G") where "G x \<equiv> \<^bold>\<forall>\<phi>. P \<phi> \<^bold>\<supset> \<phi> x"

abbreviation PropertyInclusion ("_\<^bold>\<supset>\<^sub>N_") where "\<phi> \<^bold>\<supset>\<^sub>N \<psi> \<equiv> \<^bold>\<box>(\<^bold>\<forall>y::e. \<phi> y \<^bold>\<supset> \<psi> y)"

definition Essence ("_Ess._") where "\<phi> Ess. x \<equiv> \<^bold>\<forall>\<psi>. \<psi> x \<^bold>\<supset> (\<phi> \<^bold>\<supset>\<^sub>N \<psi>)"

axiomatization where Ax2b: "\<lfloor>P \<phi> \<^bold>\<supset> \<^bold>\<box> P \<phi>\<rfloor>"

lemma Ax2b': "\<lfloor>\<^bold>\<not>P \<phi> \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<not>P \<phi>)\<rfloor>" using Ax2a Ax2b by blast

theorem Th1: "\<lfloor>G x \<^bold>\<supset> G Ess. x\<rfloor>" using Ax2a Ax2b Essence_def God_def by (smt (verit))

definition NecExist ("E") where "E x \<equiv> \<^bold>\<forall>\<phi>. \<phi> Ess. x \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>x. \<phi> x)"

axiomatization where Ax3: "\<lfloor>P E\<rfloor>"

theorem Th2: "\<lfloor>G x \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>y. G y)\<rfloor>" using Ax3 Th1 God_def NecExist_def by smt

theorem Th3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. G x) \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>y. G y)\<rfloor>" 
  \<comment>\<open>sledgehammer(Th2 Rsymm)\<close> \<comment>\<open>Proof found\<close>
  proof -
    have 1: "\<lfloor>(\<^bold>\<exists>x. G x) \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>y. G y)\<rfloor>" using Th2 by blast
    have 2: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. G x) \<^bold>\<supset> \<^bold>\<diamond>\<^bold>\<box>(\<^bold>\<exists>y. G y)\<rfloor>" using 1 by blast
    have 3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. G x) \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>y. G y)\<rfloor>" using 2 Rsymm by blast
    thus ?thesis by blast
  qed

axiomatization where Ax4: "\<lfloor>P \<phi> \<^bold>\<and> (\<phi> \<^bold>\<supset>\<^sub>N \<psi>) \<^bold>\<supset> P \<psi>\<rfloor>"

lemma True nitpick[satisfy,expect=unknown] oops \<comment>\<open>No model found\<close>

lemma EmptyEssL: "\<lfloor>(\<lambda>y.\<^bold>\<bottom>) Ess. x\<rfloor>" using Essence_def by metis

theorem Inconsistency: False 
  \<comment>\<open>sledgehammer(Ax2a Ax3 Ax4 EmptyEssL NecExist\_def)\<close> \<comment>\<open>Proof found\<close>
  proof -
    have 1: "\<lfloor>\<^bold>\<not>(P (\<lambda>x.\<^bold>\<bottom>))\<rfloor>" using Ax2a Ax4 by blast
    have 2: "\<lfloor>P (\<lambda>x.(\<lambda>y.\<^bold>\<bottom>) Ess. x \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>z::e.(\<lambda>y.\<^bold>\<bottom>)z))\<rfloor>" using Ax3 Ax4 NecExist_def by smt
    have 3: "\<lfloor>P (\<lambda>x.\<^bold>\<box>(\<^bold>\<exists>z. (\<lambda>x.\<^bold>\<bottom>) z))\<rfloor>" using 2 EmptyEssL Ax4 by smt
    have 4: "\<lfloor>P (\<lambda>x.\<^bold>\<box>\<^bold>\<bottom>)\<rfloor>" using 3 by auto
    have 5: "\<lfloor>P (\<lambda>x.\<^bold>\<bottom>)\<rfloor>" using 4 Ax2a Ax4 by smt
    have 6: "\<lfloor>\<^bold>\<bottom>\<rfloor>" using 1 5 by blast
    thus ?thesis by blast
  qed

end



