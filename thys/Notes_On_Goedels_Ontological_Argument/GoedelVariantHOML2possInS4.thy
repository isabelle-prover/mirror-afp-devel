subsection\<open>GoedelVariantHOML2possInS4.thy\<close>
text\<open>The same as GoedelVariantHOML2poss, but now in logic S4, where the proof of theorem Th3 fails.\<close>
theory GoedelVariantHOML2possInS4 imports HOMLinHOLonlyS4
begin 

consts PositiveProperty::"(e\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("P") 

axiomatization where Ax1: "\<lfloor>P \<phi> \<^bold>\<and> P \<psi> \<^bold>\<supset> P (\<phi> \<^bold>. \<psi>)\<rfloor>"

abbreviation "PosProps \<Phi> \<equiv> \<^bold>\<forall>\<phi>. \<Phi> \<phi> \<^bold>\<supset> P \<phi>"

abbreviation "ConjOfPropsFrom \<phi> \<Phi> \<equiv> \<^bold>\<box>(\<^bold>\<forall>z. \<phi> z \<^bold>\<leftrightarrow> (\<^bold>\<forall>\<psi>. \<Phi> \<psi> \<^bold>\<supset> \<psi> z))"

axiomatization where Ax1Gen: "\<lfloor>(PosProps \<Phi> \<^bold>\<and> ConjOfPropsFrom \<phi> \<Phi>) \<^bold>\<supset> P \<phi>\<rfloor>"

axiomatization where Ax2a: "\<lfloor>P \<phi> \<^bold>\<or>\<^sup>e P \<^bold>~\<phi>\<rfloor>"

definition God ("G") where "G x \<equiv> \<^bold>\<forall>\<phi>. P \<phi> \<^bold>\<supset> \<phi> x"

abbreviation PropertyInclusion ("_\<^bold>\<supset>\<^sub>N_") where "\<phi> \<^bold>\<supset>\<^sub>N \<psi> \<equiv> \<^bold>\<box>(\<^bold>\<forall>y::e. \<phi> y \<^bold>\<supset> \<psi> y)"

definition Essence ("_Ess._") where "\<phi> Ess. x \<equiv> \<phi> x \<^bold>\<and> (\<^bold>\<forall>\<psi>. \<psi> x \<^bold>\<supset> (\<phi> \<^bold>\<supset>\<^sub>N \<psi>))"

axiomatization where Ax2b: "\<lfloor>P \<phi> \<^bold>\<supset> \<^bold>\<box> P \<phi>\<rfloor>"

lemma Ax2b': "\<lfloor>\<^bold>\<not>P \<phi> \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<not>P \<phi>)\<rfloor>" using Ax2a Ax2b by blast

theorem Th1: "\<lfloor>G x \<^bold>\<supset> G Ess. x\<rfloor>" using Ax2a Ax2b Essence_def God_def by (smt (verit))

definition NecExist ("E") where "E x \<equiv> \<^bold>\<forall>\<phi>. \<phi> Ess. x \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>x. \<phi> x)"

axiomatization where Ax3: "\<lfloor>P E\<rfloor>"

axiomatization where Ax4: "\<lfloor>P \<phi> \<^bold>\<and> (\<phi> \<^bold>\<supset>\<^sub>N \<psi>) \<^bold>\<supset> P \<psi>\<rfloor>"

theorem Th2: "\<lfloor>G x \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>y. G y)\<rfloor>" using Ax3 Th1 God_def NecExist_def by smt

theorem Th3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. G x) \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>y. G y)\<rfloor>" \<comment>\<open>nitpick sledgehammer\<close> oops \<comment>\<open>Open problem\<close>

end



