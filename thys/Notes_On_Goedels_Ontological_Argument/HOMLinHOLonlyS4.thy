subsection\<open>HOMLinHOLonlyS4.thy (slight variation of Figure 3 of \cite{J75})\<close>
text\<open>Shallow embedding of higher-order modal logic (HOML) in the classical higher-order logic (HOL)
of Isabelle/HOL utilizing the LogiKEy methodology. Here logic S4 is introduced.\<close>
theory HOMLinHOLonlyS4 imports Main
begin

\<comment>\<open>Global parameters setting for the model finder nitpick and the parser; unimport for the reader\<close>
nitpick_params[user_axioms,expect=genuine,show_all,format=2,max_genuine=3]
declare[[syntax_ambiguity_warning=false]] 

\<comment>\<open>Type i is associated with possible worlds and type e with entities:\<close>
typedecl i \<comment>\<open>Possible worlds\<close> 
typedecl e \<comment>\<open>Individuals/entities\<close> 
type_synonym \<sigma> = "i\<Rightarrow>bool" \<comment>\<open>World-lifted propositions\<close>
type_synonym \<tau> = "e\<Rightarrow>\<sigma>" \<comment>\<open>modal properties\<close>

consts R::"i\<Rightarrow>i\<Rightarrow>bool" ("_\<^bold>r_") \<comment>\<open>Accessibility relation between worlds\<close>
axiomatization where 
  Rrefl: "\<forall>x. x\<^bold>rx" and 
  Rtrans: "\<forall>x y z. x\<^bold>ry \<and> y\<^bold>rz \<longrightarrow> x\<^bold>rz" 

\<comment>\<open>Logical connectives (operating on truth-sets)\<close>
abbreviation Mbot::\<sigma> ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"
abbreviation Mtop::\<sigma> ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True"
abbreviation Mneg::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_" [52]53) where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>(\<phi> w)"
abbreviation Mand::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixl "\<^bold>\<and>" 50) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi> w \<and> \<psi> w" 
abbreviation Mor::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixl "\<^bold>\<or>" 49) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi> w \<or> \<psi> w "
abbreviation Mimp::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<supset>" 48) where "\<phi>\<^bold>\<supset>\<psi> \<equiv> \<lambda>w. \<phi> w \<longrightarrow> \<psi> w" 
abbreviation Mequiv::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixl "\<^bold>\<leftrightarrow>" 47) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi> w \<longleftrightarrow> \<psi> w"
abbreviation Mbox::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<box>_" [54]55) where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w.\<forall>v. w \<^bold>r v \<longrightarrow> \<phi> v"
abbreviation Mdia::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<diamond>_" [54]55) where "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w.\<exists>v. w \<^bold>r v \<and> \<phi> v"
abbreviation Mprimeq::"'a\<Rightarrow>'a\<Rightarrow>\<sigma>" ("_\<^bold>=_") where "x\<^bold>=y \<equiv> \<lambda>w. x=y"
abbreviation Mprimneg::"'a\<Rightarrow>'a\<Rightarrow>\<sigma>" ("_\<^bold>\<noteq>_") where "x\<^bold>\<noteq>y \<equiv> \<lambda>w. x\<noteq>y"
abbreviation Mnegpred::"\<tau>\<Rightarrow>\<tau>" ("\<^bold>~_") where "\<^bold>~\<Phi> \<equiv> \<lambda>x.\<lambda>w. \<not>\<Phi> x w"
abbreviation Mconpred::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixl "\<^bold>." 50) where "\<Phi>\<^bold>.\<Psi> \<equiv> \<lambda>x.\<lambda>w. \<Phi> x w \<and> \<Psi> x w"
abbreviation Mexclor::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixl "\<^bold>\<or>\<^sup>e" 49) where "\<phi>\<^bold>\<or>\<^sup>e\<psi> \<equiv> (\<phi> \<^bold>\<or> \<psi>) \<^bold>\<and> \<^bold>\<not>(\<phi> \<^bold>\<and> \<psi>)" 

\<comment>\<open>Possibilist quantifiers (polymorphic)\<close>
abbreviation Mallposs::"('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. \<Phi> x w"
abbreviation Mallpossb (binder "\<^bold>\<forall>" [8]9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>" 
abbreviation Mexiposs::"('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. \<Phi> x w" 
abbreviation Mexipossb (binder "\<^bold>\<exists>" [8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>" 

\<comment>\<open>Actualist quantifiers (for individuals/entities)\<close>
consts existsAt::"e\<Rightarrow>\<sigma>" ("_\<^bold>@_") 
abbreviation Mallact::"(e\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>\<^sup>E") where "\<^bold>\<forall>\<^sup>E\<Phi> \<equiv> \<lambda>w.\<forall>x. x\<^bold>@w \<longrightarrow> \<Phi> x w"
abbreviation Mallactb (binder "\<^bold>\<forall>\<^sup>E" [8]9) where "\<^bold>\<forall>\<^sup>Ex. \<phi>(x) \<equiv> \<^bold>\<forall>\<^sup>E\<phi>" 
abbreviation Mexiact::"(e\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>\<^sup>E") where "\<^bold>\<exists>\<^sup>E\<Phi> \<equiv> \<lambda>w.\<exists>x. x\<^bold>@w \<and> \<Phi> x w"
abbreviation Mexiactb (binder "\<^bold>\<exists>\<^sup>E" [8]9) where "\<^bold>\<exists>\<^sup>Ex. \<phi>(x) \<equiv> \<^bold>\<exists>\<^sup>E\<phi>"

\<comment>\<open>Leibniz equality (polymorphic)\<close>
abbreviation Mleibeq::"'a\<Rightarrow>'a\<Rightarrow>\<sigma>" ("_\<^bold>\<equiv>_") where "x\<^bold>\<equiv>y \<equiv> \<^bold>\<forall>P. P x \<^bold>\<supset> P y"

\<comment>\<open>Meta-logical predicate for global validity\<close>
abbreviation Mvalid::"\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>") where "\<lfloor>\<psi>\<rfloor> \<equiv> \<forall>w. \<psi> w"

end





