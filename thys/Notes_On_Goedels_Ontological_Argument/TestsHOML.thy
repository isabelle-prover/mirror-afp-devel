subsection\<open>TestsHOML.thy (Figure 4 of \cite{J75})\<close>
text\<open>Tests and verifications of properties for the embedding of HOML (S5) in HOL.\<close>
theory TestsHOML imports HOMLinHOL
begin 

\<comment>\<open>Test for S5 modal logic\<close>
lemma axM: "\<lfloor>\<^bold>\<box>\<phi> \<^bold>\<supset> \<phi>\<rfloor>" using Rrefl by blast
lemma axD: "\<lfloor>\<^bold>\<box>\<phi> \<^bold>\<supset> \<^bold>\<diamond>\<phi>\<rfloor>" using Rrefl by blast
lemma axB: "\<lfloor>\<phi> \<^bold>\<supset> \<^bold>\<box>\<^bold>\<diamond>\<phi>\<rfloor>" using Rsymm by blast
lemma ax4: "\<lfloor>\<^bold>\<box>\<phi> \<^bold>\<supset> \<^bold>\<box>\<^bold>\<box>\<phi>\<rfloor>" using Rtrans by blast
lemma ax5: "\<lfloor>\<^bold>\<diamond>\<phi> \<^bold>\<supset> \<^bold>\<box>\<^bold>\<diamond>\<phi>\<rfloor>" using Rsymm Rtrans by blast 

\<comment>\<open>Test for Barcan and converse Barcan formula:\<close>
lemma BarcanAct: "\<lfloor>(\<^bold>\<forall>\<^sup>Ex.\<^bold>\<box>(\<phi> x)) \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex.(\<phi> x))\<rfloor>" 
  nitpick[expect=genuine] oops \<comment>\<open>Countermodel found\<close>
lemma ConvBarcanAct: "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex.(\<phi> x)) \<^bold>\<supset> (\<^bold>\<forall>\<^sup>Ex.\<^bold>\<box>(\<phi> x))\<rfloor>" 
  nitpick[expect=genuine] oops \<comment>\<open>Countermodel found\<close>
lemma BarcanPoss: "\<lfloor>(\<^bold>\<forall>x.\<^bold>\<box>(\<phi> x)) \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<forall>x. \<phi> x)\<rfloor>" by blast 
lemma ConvBarcanPoss: "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>x.(\<phi> x)) \<^bold>\<supset> (\<^bold>\<forall>x.\<^bold>\<box>(\<phi> x))\<rfloor>" by blast

\<comment>\<open>A simple Hilbert system for classical propositional logic is derived\<close>
lemma Hilbert_A1: "\<lfloor>A \<^bold>\<supset> (B \<^bold>\<supset> A)\<rfloor>" by blast
lemma Hilbert_A2: "\<lfloor>(A \<^bold>\<supset> (B \<^bold>\<supset> C)) \<^bold>\<supset> ((A \<^bold>\<supset> B) \<^bold>\<supset> (A \<^bold>\<supset> C))\<rfloor>" by blast
lemma Hilbert_MP: assumes "\<lfloor>A\<rfloor>" and "\<lfloor>A \<^bold>\<supset> B\<rfloor>" shows "\<lfloor>B\<rfloor>" using assms by blast

\<comment>\<open>We have a polymorphic possibilist quantifier for which existential import holds\<close>
lemma Quant_1: assumes "\<lfloor>A\<rfloor>" shows "\<lfloor>\<^bold>\<forall>x::'a. A\<rfloor>" using assms by auto

\<comment>\<open>Existential import holds for possibilist quantifiers\<close>
lemma ExImPossibilist1: "\<lfloor>\<^bold>\<exists>x::e. x \<^bold>= x\<rfloor>" by blast 
lemma ExImPossibilist2: "\<lfloor>\<^bold>\<exists>x::e. x \<^bold>\<equiv> x\<rfloor>" by blast
lemma ExImPossibilist3: "\<lfloor>\<^bold>\<exists>x::e. x \<^bold>= t\<rfloor>" by blast 
lemma ExImPossibilist4: "\<lfloor>\<^bold>\<exists>x::'a. x \<^bold>\<equiv> t::'a\<rfloor>" by blast
lemma ExImPossibilist: "\<lfloor>\<^bold>\<exists>x::'a. \<^bold>\<top>\<rfloor>" by blast

\<comment>\<open>We have an actualist quantifier for individuals for which existential import does not hold\<close>
lemma Quant_2: assumes "\<lfloor>A\<rfloor>" shows "\<lfloor>\<^bold>\<forall>\<^sup>Ex::e. A\<rfloor>" using assms by auto

\<comment>\<open>Existential import does not hold for our actualist quantifiers (for individuals)\<close>
lemma ExImActualist1: "\<lfloor>\<^bold>\<exists>\<^sup>Ex::e. x \<^bold>= x\<rfloor>" 
  nitpick[card=1,expect=genuine] oops \<comment>\<open>Countermodel found\<close>
lemma ExImActualist2: "\<lfloor>\<^bold>\<exists>\<^sup>Ex::e. x \<^bold>\<equiv> x\<rfloor>" 
  nitpick[card=1,expect=genuine] oops \<comment>\<open>Countermodel found\<close>
lemma ExImActualist3: "\<lfloor>\<^bold>\<exists>\<^sup>Ex::e. x \<^bold>= t\<rfloor>" 
  nitpick[card=1,expect=genuine] oops \<comment>\<open>Countermodel found\<close>
lemma ExImActualist: "\<lfloor>\<^bold>\<exists>\<^sup>Ex::e. \<^bold>\<top>\<rfloor>" 
  nitpick[card=1,expect=genuine] oops \<comment>\<open>Countermodel found\<close>

\<comment>\<open>Properties of the embedded primitive equality, which coincides with Leibniz equality\<close>
lemma EqRefl: "\<lfloor>x \<^bold>= x\<rfloor>" by blast
lemma EqSym: "\<lfloor>(x \<^bold>= y) \<^bold>\<leftrightarrow> (y \<^bold>= x)\<rfloor>" by blast
lemma EqTrans: "\<lfloor>((x \<^bold>= y) \<^bold>\<and> (y \<^bold>= z)) \<^bold>\<supset> (x \<^bold>= z)\<rfloor>" by blast
lemma EQCong: "\<lfloor>(x \<^bold>= y) \<^bold>\<supset> ((\<phi> x) \<^bold>= (\<phi> y))\<rfloor>" by blast
lemma EQFuncExt: "\<lfloor>(\<phi> \<^bold>= \<psi>) \<^bold>\<supset> (\<^bold>\<forall>x. ((\<phi> x) \<^bold>= (\<psi> x)))\<rfloor>" by blast
lemma EQBoolExt1: "\<lfloor>(\<phi> \<^bold>= \<psi>) \<^bold>\<supset> (\<phi> \<^bold>\<leftrightarrow> \<psi>)\<rfloor>" by blast
lemma EQBoolExt2: "\<lfloor>(\<phi> \<^bold>\<leftrightarrow> \<psi>) \<^bold>\<supset> (\<phi> \<^bold>= \<psi>)\<rfloor>" 
  nitpick[card=2] oops \<comment>\<open>Countermodel found\<close>
lemma EQBoolExt3: "\<lfloor>(\<phi> \<^bold>\<leftrightarrow> \<psi>)\<rfloor> \<longrightarrow> \<lfloor>(\<phi> \<^bold>= \<psi>)\<rfloor>" by blast 
lemma EqPrimLeib: "\<lfloor>(x \<^bold>= y) \<^bold>\<leftrightarrow> (x \<^bold>\<equiv> y)\<rfloor>" by auto

\<comment>\<open>Comprehension is natively supported in HOL (due to lambda-abstraction)\<close>
lemma Comprehension1: "\<lfloor>\<^bold>\<exists>\<phi>. \<^bold>\<forall>x. (\<phi> x) \<^bold>\<leftrightarrow> A\<rfloor>" by force
lemma Comprehension2: "\<lfloor>\<^bold>\<exists>\<phi>. \<^bold>\<forall>x. (\<phi> x) \<^bold>\<leftrightarrow> (A x)\<rfloor>" by force
lemma Comprehension3: "\<lfloor>\<^bold>\<exists>\<phi>. \<^bold>\<forall>x y. (\<phi> x y) \<^bold>\<leftrightarrow> (A x y)\<rfloor>" by force

\<comment>\<open>Modal collapse does not hold\<close>
lemma ModalCollapse: "\<lfloor>\<^bold>\<forall>\<phi>. \<phi> \<^bold>\<supset> \<^bold>\<box>\<phi>\<rfloor>" 
  nitpick[card=2,expect=genuine] oops \<comment>\<open>Countermodel found\<close>

\<comment>\<open>Empty property and self-difference\<close>
lemma TruePropertyAndSelfIdentity: "\<lfloor>(\<lambda>x::e. \<^bold>\<top>) \<^bold>= (\<lambda>x. x \<^bold>= x)\<rfloor>" by blast 
lemma EmptyPropertyAndSelfDifference: "\<lfloor>(\<lambda>x::e. \<^bold>\<bottom>) \<^bold>= (\<lambda>x. x \<^bold>\<noteq> x)\<rfloor>" by blast 
lemma EmptyProperty2: "\<lfloor>\<^bold>\<exists>x. \<phi> x\<rfloor> \<longrightarrow> \<lfloor>\<phi> \<^bold>\<noteq> (\<lambda>x::e. \<^bold>\<bottom>)\<rfloor>" by blast 
lemma EmptyProperty3: "\<lfloor>\<^bold>\<exists>\<^sup>Ex. \<phi> x\<rfloor> \<longrightarrow> \<lfloor>\<phi> \<^bold>\<noteq> (\<lambda>x::e. \<^bold>\<bottom>)\<rfloor>" by blast 
lemma EmptyProperty4: "\<lfloor>\<phi> \<^bold>\<noteq> (\<lambda>x::e. \<^bold>\<bottom>)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<exists>x. \<phi> x\<rfloor>" 
  nitpick[expect=genuine] oops \<comment>\<open>Countermodel found\<close>
lemma EmptyProperty5: "\<lfloor>\<phi> \<^bold>\<noteq> (\<lambda>x::e. \<^bold>\<bottom>)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<exists>\<^sup>Ex. \<phi> x\<rfloor>" 
  nitpick[expect=genuine] oops \<comment>\<open>Countermodel found\<close>

end




