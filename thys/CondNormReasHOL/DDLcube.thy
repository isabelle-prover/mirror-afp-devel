section  \<open>Shallow Embedding of \AA qvist's system {\bf E}\<close>

  text \<open>This is Aqvist's system E from the 2019 IfColog paper \cite{J45}.\<close>

subsection  \<open>System {\bf E}\<close>

theory DDLcube 
  imports Main  (*** Benzmueller/Parent 2024 ***)

begin  
nitpick_params [user_axioms,show_all,format=2]  \<comment>\<open>Settings for model finder Nitpick\<close>

typedecl i  \<comment>\<open>Possible worlds\<close>
type_synonym \<sigma> = "(i\<Rightarrow>bool)"
type_synonym \<alpha> = "i\<Rightarrow>\<sigma>"  \<comment>\<open>Type of betterness relation between worlds\<close>
type_synonym \<tau> = "\<sigma>\<Rightarrow>\<sigma>"

consts aw::i  \<comment>\<open>Actual world\<close>
abbreviation etrue  :: "\<sigma>" (\<open>\<^bold>\<top>\<close>) where "\<^bold>\<top> \<equiv> \<lambda>w. True" 
abbreviation efalse :: "\<sigma>" (\<open>\<^bold>\<bottom>\<close>)  where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"   
abbreviation enot :: "\<sigma>\<Rightarrow>\<sigma>" (\<open>\<^bold>\<not>_\<close>[52]53)  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)" 
abbreviation eand :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr\<open>\<^bold>\<and>\<close>51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<and>\<psi>(w)"   
abbreviation eor  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr\<open>\<^bold>\<or>\<close>50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<or>\<psi>(w)"   
abbreviation eimpf :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr\<open>\<^bold>\<rightarrow>\<close>49) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longrightarrow>\<psi>(w)"  
abbreviation eimpb :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr\<open>\<^bold>\<leftarrow>\<close>49) where "\<phi>\<^bold>\<leftarrow>\<psi> \<equiv> \<lambda>w. \<psi>(w)\<longrightarrow>\<phi>(w)"  
abbreviation eequ :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr\<open>\<^bold>\<leftrightarrow>\<close>48) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longleftrightarrow>\<psi>(w)" 

abbreviation ebox :: "\<sigma>\<Rightarrow>\<sigma>" (\<open>\<box>\<close>) where "\<box>\<phi> \<equiv> \<lambda>w. \<forall>v. \<phi>(v)"  
abbreviation ddediomond  :: "\<sigma>\<Rightarrow>\<sigma>" (\<open>\<diamond>\<close>) where "\<diamond>\<phi> \<equiv> \<lambda>w. \<exists>v. \<phi>(v)"

abbreviation evalid :: "\<sigma>\<Rightarrow>bool" (\<open>\<lfloor>_\<rfloor>\<close>[8]109)  \<comment>\<open>Global validity\<close>
  where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"
abbreviation ecjactual :: "\<sigma>\<Rightarrow>bool" (\<open>\<lfloor>_\<rfloor>\<^sub>l\<close>[7]105)  \<comment>\<open>Local validity --- in world aw\<close>
  where "\<lfloor>p\<rfloor>\<^sub>l \<equiv> p(aw)"

consts r :: "\<alpha>" (infixr \<open>\<^bold>r\<close> 70)  \<comment>\<open>Betterness relation\<close>

abbreviation esubset :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" (infix \<open>\<^bold>\<subseteq>\<close> 53)
  where "\<phi> \<^bold>\<subseteq> \<psi> \<equiv> \<forall>x. \<phi> x \<longrightarrow> \<psi> x"

  text \<open>We introduce the opt and max rules. These express two candidate truth-conditions for
conditional obligation and permission.\<close>

abbreviation eopt  :: "\<sigma>\<Rightarrow>\<sigma>" (\<open>opt<_>\<close>)  \<comment>\<open>opt rule\<close>
  where "opt<\<phi>> \<equiv> (\<lambda>v. ( (\<phi>)(v) \<and> (\<forall>x. ((\<phi>)(x) \<longrightarrow> v \<^bold>r x) )) )" 
abbreviation econdopt :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (\<open>\<odot><_|_>\<close>)
  where "\<odot><\<psi>|\<phi>> \<equiv>  \<lambda>w. opt<\<phi>> \<^bold>\<subseteq> \<psi>"
abbreviation eperm :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (\<open>\<P><_|_>\<close>) 
  where "\<P><\<psi>|\<phi>> \<equiv> \<^bold>\<not>\<odot><\<^bold>\<not>\<psi>|\<phi>>" \<comment>\<open>permission is the dual of obligation\<close>

abbreviation emax  :: "\<sigma>\<Rightarrow>\<sigma>" (\<open>max<_>\<close>)  \<comment>\<open>max rule\<close>
  where "max<\<phi>> \<equiv> (\<lambda>v. ( (\<phi>)(v) \<and> (\<forall>x. ((\<phi>)(x) \<longrightarrow> (x \<^bold>r v \<longrightarrow>  v \<^bold>r x)) )) )" 
abbreviation econd  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (\<open>\<circle><_|_>\<close>)
  where "\<circle><\<psi>|\<phi>> \<equiv>  \<lambda>w. max<\<phi>> \<^bold>\<subseteq> \<psi>"
abbreviation euncobl :: "\<sigma>\<Rightarrow>\<sigma>" (\<open>\<^bold>\<circle><_>\<close>)   
  where "\<^bold>\<circle><\<phi>> \<equiv> \<circle><\<phi>|\<^bold>\<top>>" 
abbreviation ddeperm :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (\<open>P<_|_>\<close>) 
  where "P<\<psi>|\<phi>> \<equiv>\<^bold>\<not>\<circle><\<^bold>\<not>\<psi>|\<phi>>"

  text \<open>A first consistency check is performed.\<close>

lemma True 
  nitpick [expect=genuine,satisfy] \<comment>\<open>model found\<close>
  oops

  text \<open>We show that the max-rule and opt-rule do not coincide.\<close>

lemma "\<odot><\<psi>|\<phi>> \<equiv> \<circle><\<psi>|\<phi>>" 
  nitpick [expect=genuine,card i=1] \<comment>\<open>counterexample found\<close>
  oops

  text \<open>David Lewis's truth conditions for the deontic modalities are introduced.\<close>

abbreviation lewcond :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"  (\<open>\<circ><_|_>\<close>)
  where "\<circ><\<psi>|\<phi>> \<equiv> \<lambda>v. (\<not>(\<exists>x. (\<phi>)(x))\<or>  
        (\<exists>x. ((\<phi>)(x)\<and>(\<psi>)(x) \<and> (\<forall>y. ((y \<^bold>r x) \<longrightarrow> (\<phi>)(y)\<longrightarrow>(\<psi>)(y))))))"
abbreviation lewperm :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (\<open>\<integral><_|_>\<close>) 
  where "\<integral><\<psi>|\<phi>> \<equiv>\<^bold>\<not>\<circ><\<^bold>\<not>\<psi>|\<phi>>"

  text \<open>Kratzer's truth conditions for the deontic modalities are introduced.\<close>

abbreviation kratcond :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"  (\<open>\<ominus><_|_>\<close>)
  where "\<ominus><\<psi>|\<phi>> \<equiv> \<lambda>v. ((\<forall>x. ((\<phi>)(x) \<longrightarrow> 
     (\<exists>y. ((\<phi>)(y)\<and>(y \<^bold>r x) \<and> ((\<forall>z. ((z \<^bold>r y) \<longrightarrow> (\<phi>)(z) \<longrightarrow> (\<psi>)(z)))))))))"
abbreviation kratperm :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (\<open>\<times><_|_>\<close>) 
  where "\<times><\<psi>|\<phi>> \<equiv>\<^bold>\<not>\<ominus><\<^bold>\<not>\<psi>|\<phi>>"


subsection \<open>Properties\<close>

  text \<open>Extensions of {\bf E} are obtained by putting suitable constraints on the betterness relation.\<close>

  text \<open>These are the standard properties of the betterness relation.\<close>

abbreviation "reflexivity  \<equiv> (\<forall>x. x \<^bold>r x)"
abbreviation "transitivity \<equiv> (\<forall>x y z. (x \<^bold>r y \<and> y \<^bold>r z) \<longrightarrow> x \<^bold>r z)"
abbreviation "totality \<equiv> (\<forall>x y. (x \<^bold>r y \<or> y \<^bold>r x))"

  text \<open>4 versions of Lewis's limit assumption can be distinguished.\<close>

abbreviation "mlimitedness \<equiv> (\<forall>\<phi>. (\<exists>x. (\<phi>)x) \<longrightarrow> (\<exists>x. max<\<phi>>x))"

abbreviation "msmoothness \<equiv>
   (\<forall>\<phi> x. ((\<phi>)x \<longrightarrow> (max<\<phi>>x \<or> (\<exists>y. (y \<^bold>r x \<and> \<not>(x \<^bold>r y) \<and> max<\<phi>>y)))))"

abbreviation "olimitedness \<equiv> (\<forall>\<phi>. (\<exists>x. (\<phi>)x) \<longrightarrow> (\<exists>x. opt<\<phi>>x))"

abbreviation "osmoothness \<equiv>
   (\<forall>\<phi> x. ((\<phi>)x \<longrightarrow> (opt<\<phi>>x \<or> (\<exists>y. (y \<^bold>r x \<and> \<not>(x \<^bold>r y) \<and> opt<\<phi>>y)))))"

  text \<open>Weaker forms of transitivity can be defined. They require the notion of
transitive closure.\<close>

definition transitive :: "\<alpha>\<Rightarrow>bool"
  where "transitive Rel \<equiv> \<forall>x y z. Rel x y \<and>  Rel y z \<longrightarrow> Rel x z"

definition sub_rel :: "\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>bool" 
  where "sub_rel Rel1 Rel2 \<equiv> \<forall>u v. Rel1 u v \<longrightarrow> Rel2 u v"

definition assfactor::"\<alpha>\<Rightarrow>\<alpha>"
  where "assfactor Rel \<equiv> \<lambda>u v. Rel u v \<and> \<not>Rel v u "

  text \<open>In HOL the transitive closure of a relation can be defined in a single line - Here 
we apply the construction to the betterness relation and its strict variant.\<close>

definition tcr  
  where "tcr \<equiv> \<lambda>x y. \<forall>Q. transitive Q \<longrightarrow> (sub_rel r Q \<longrightarrow> Q x y)"

definition tcr_strict
  where "tcr_strict \<equiv> \<lambda>x y. \<forall>Q. transitive Q 
                               \<longrightarrow> (sub_rel (\<lambda>u v. u \<^bold>r v \<and> \<not>v \<^bold>r u) Q \<longrightarrow> Q x y)"

  text \<open>Quasi-transitivity requires the strict betterness relation is transitive.\<close>

abbreviation Quasitransit 
  where "Quasitransit  \<equiv> \<forall>x y z. (assfactor r x y \<and>  
                    assfactor r y z) \<longrightarrow> assfactor r x z"

  text \<open>Suzumura consistency requires that cycles with at least  one  non-strict betterness link are ruled out.\<close>

abbreviation Suzumura  
  where "Suzumura \<equiv> \<forall>x y. tcr x y \<longrightarrow> (y \<^bold>r x \<longrightarrow> x \<^bold>r y)"

theorem T1: "Suzumura \<equiv> \<forall>x y. tcr x y \<longrightarrow> \<not> (y \<^bold>r x \<and> \<not> (x \<^bold>r y))" by simp

  text \<open>Acyclicity requires that cycles where all the links are strict are ruled out.\<close>

abbreviation loopfree
  where "loopfree \<equiv> \<forall>x y. tcr_strict x y \<longrightarrow> (y \<^bold>r x \<longrightarrow> x \<^bold>r y)"

  text \<open>Interval order is the combination of reflexivity and Ferrers.\<close>
 
abbreviation Ferrers
  where "Ferrers \<equiv> (\<forall>x y z u. (x \<^bold>r u \<and> y \<^bold>r z) \<longrightarrow> (x \<^bold>r z \<or> y \<^bold>r u))"

theorem T2:
  assumes Ferrers and reflexivity  \<comment>\<open>fact overlooked in the literature\<close>
  shows totality
  \<comment>\<open>sledgehammer\<close>
  by (simp add: assms(1) assms(2)) 

  text \<open>We study the relationships between these candidate weakenings of transitivity.\<close>

theorem T3: 
  assumes transitivity 
  shows "Suzumura"
  \<comment>\<open>sledgehammer\<close>
  by (metis assms sub_rel_def tcr_def transitive_def)
 
theorem T4:
  assumes transitivity 
  shows Quasitransit
  \<comment>\<open>sledgehammer\<close>
  by (metis assfactor_def assms) 

theorem T5:
  assumes Suzumura
  shows loopfree
  \<comment>\<open>sledgehammer\<close>
  by (metis (no_types, lifting) assms sub_rel_def tcr_def tcr_strict_def)

theorem T6: 
  assumes Quasitransit 
  shows loopfree
  \<comment>\<open>sledgehammer\<close>
  by (smt (verit, best) assfactor_def assms sub_rel_def tcr_strict_def transitive_def)

theorem T7: 
  assumes reflexivity and Ferrers 
  shows Quasitransit
  \<comment>\<open>sledgehammer\<close> 
  by (metis assfactor_def assms) 

section  \<open>Meta-Logical Study\<close>

subsection \<open>Correspondence - Max rule\<close>

  text \<open>The inference rules of {\bf E} preserve validity in all models.\<close>

lemma MP: "\<lbrakk>\<lfloor>\<phi>\<rfloor>; \<lfloor>\<phi> \<^bold>\<rightarrow> \<psi>\<rfloor>\<rbrakk> \<Longrightarrow> \<lfloor>\<psi>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close> 
  by simp

lemma NEC: "\<lfloor>\<phi>\<rfloor> \<Longrightarrow> \<lfloor>\<box>\<phi>\<rfloor>" 
    \<comment>\<open>sledgehammer\<close> 
  by simp

  text \<open>@{term "\<box>"} is an S5 modality\<close>

lemma C_1_refl: "\<lfloor>\<box>\<phi> \<^bold>\<rightarrow> \<phi>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close> 
  by simp

lemma C_1_trans: "\<lfloor>\<box>\<phi> \<^bold>\<rightarrow> (\<box>(\<box>\<phi>))\<rfloor>" 
  \<comment>\<open>sledgehammer\<close> 
  by simp

lemma C_1_sym: "\<lfloor>\<phi> \<^bold>\<rightarrow> (\<box>(\<diamond>\<phi>))\<rfloor>"  
  \<comment>\<open>sledgehammer\<close> 
  by simp

  text \<open>All the axioms of {\bf E} hold - they do not correspond to a property of the betterness relation.\<close>

lemma Abs: "\<lfloor>\<circle><\<psi>|\<phi>> \<^bold>\<rightarrow> \<box>\<circle><\<psi>|\<phi>>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close>
  by blast 

lemma Nec: "\<lfloor>\<box>\<psi> \<^bold>\<rightarrow> \<circle><\<psi>|\<phi>>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close>
  by blast 

lemma Ext: "\<lfloor>\<box>(\<phi>\<^sub>1\<^bold>\<leftrightarrow>\<phi>\<^sub>2) \<^bold>\<rightarrow> (\<circle><\<psi>|\<phi>\<^sub>1> \<^bold>\<leftrightarrow> \<circle><\<psi>|\<phi>\<^sub>2>)\<rfloor>"  
  \<comment>\<open>sledgehammer\<close>
  by simp

lemma Id: "\<lfloor>\<circle><\<phi>|\<phi>>\<rfloor>"  
  \<comment>\<open>sledgehammer\<close>
  by blast 

lemma Sh: "\<lfloor>\<circle><\<psi>|\<phi>\<^sub>1\<^bold>\<and>\<phi>\<^sub>2> \<^bold>\<rightarrow> \<circle><(\<phi>\<^sub>2\<^bold>\<rightarrow>\<psi>)|\<phi>\<^sub>1>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close>
  by blast 

lemma COK:"\<lfloor>\<circle><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circle><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circle><\<psi>\<^sub>2|\<phi>>)\<rfloor>" 
  \<comment>\<open>sledgehammer\<close>
  by blast

  text \<open>The axioms of the stronger systems do not hold in general.\<close>

lemma "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> (\<circle><\<psi>|\<phi>> \<^bold>\<rightarrow> P<\<psi>|\<phi>>)\<rfloor>" 
  nitpick [expect=genuine,card i=3]  \<comment>\<open>counterexample found\<close>
  oops 

lemma "\<lfloor>(\<circle><\<psi>|\<phi>> \<^bold>\<and> \<circle><\<chi>|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>"
  nitpick [expect=genuine,card i=3]  \<comment>\<open>counterexample found\<close>
  oops 

lemma "\<lfloor>\<circle><\<chi>|(\<phi>\<^bold>\<or>\<psi>)> \<^bold>\<rightarrow> ((\<circle><\<chi>|\<phi>>) \<^bold>\<or> (\<circle><\<chi>|\<psi>>))\<rfloor>"
  nitpick [expect=genuine,card i=3]  \<comment>\<open>counterexample found\<close>
  oops 

  text \<open>Now we identify a number of correspondences under the max rule. Only the direction property => axiom is verified.\<close>

  text \<open>Max-limitedness corresponds to D*, the distinctive axiom of {\bf F}. The first implies the second,
but not the other around.\<close>

theorem T8: 
  assumes mlimitedness
  shows  "D*": "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> \<circle><\<psi>|\<phi>> \<^bold>\<rightarrow> P<\<psi>|\<phi>>\<rfloor>"  
  \<comment>\<open>sledgehammer\<close>
  by (metis assms)

lemma 
  assumes "D*": "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>(\<circle><\<psi>|\<phi>> \<^bold>\<and> \<circle><\<^bold>\<not>\<psi>|\<phi>>)\<rfloor>"
  shows mlimitedness 
  nitpick [expect=genuine,card i=3]  \<comment>\<open>counterexample found\<close>
  oops

  text \<open>Smoothness implies cautious monotony, the distinctive axiom of {\bf F}+(CM), but not the other
way around.\<close>

theorem T9: 
  assumes msmoothness    
  shows CM: "\<lfloor>(\<circle><\<psi>|\<phi>> \<^bold>\<and> \<circle><\<chi>|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close>
  using assms by force 

lemma 
  assumes CM: "\<lfloor>(\<circle><\<psi>|\<phi>> \<^bold>\<and> \<circle><\<chi>|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>"
  shows  msmoothness
  nitpick [expect=genuine,card i=3]  \<comment>\<open>counterexample found\<close>
  oops  

  text \<open>Interval order corresponds to disjunctive rationality, the distinctive axiom of {\bf F}+(DR), but not the
other way around.\<close>

lemma 
  assumes reflexivity
  shows  DR: "\<lfloor>\<circle><\<chi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<rightarrow> (\<circle><\<chi>|\<phi>> \<^bold>\<or> \<circle><\<chi>|\<psi>>)\<rfloor>" 
  nitpick [expect=genuine,card i=3]  \<comment>\<open>counterexample found\<close>
  oops 

theorem T10: 
  assumes reflexivity and Ferrers
  shows  DR: "\<lfloor>\<circle><\<chi>|(\<phi>\<^bold>\<or>\<psi>)> \<^bold>\<rightarrow> (\<circle><\<chi>|\<phi>> \<^bold>\<or> \<circle><\<chi>|\<psi>>)\<rfloor>" 
  \<comment>\<open>sledgehammer\<close>
  by (metis assms(1) assms(2))
  
lemma 
  assumes DR: "\<lfloor>\<circle><\<chi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<rightarrow> (\<circle><\<chi>|\<phi>> \<^bold>\<or> \<circle><\<chi>|\<psi>>)\<rfloor>" 
  shows reflexivity 
  nitpick [expect=genuine,card i=1]  \<comment>\<open>counterexample found\<close> 
  oops 

lemma 
  assumes DR: "\<lfloor>\<circle><\<chi>|\<phi>\<^bold>\<or>\<psi>>\<^bold>\<rightarrow>(\<circle><\<chi>|\<phi>> \<^bold>\<or> \<circle><\<chi>|\<psi>>)\<rfloor>" 
  shows Ferrers  
  nitpick [expect=genuine,card i=2]  \<comment>\<open>counterexample found\<close>
  oops 

  text \<open>Transitivity and totality jointly correspond to the Spohn axiom (Sp), the distinctive axiom of system  {\bf G}, but not vice-versa. They also jointly correspond to a
 principle of transitivity for the betterness relation on formulas, but the converse fails.\<close>

lemma 
  assumes transitivity
  shows  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  nitpick [expect=genuine,card i=3] \<comment>\<open>counterexample found\<close> 
  oops

lemma 
  assumes totality
  shows  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  nitpick [expect=genuine,card i=3] \<comment>\<open>counterexample found\<close>
  oops

theorem T11: 
  assumes transitivity and totality
  shows  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close>
  by (metis assms)

theorem T12: 
  assumes transitivity and totality
  shows  transit: "\<lfloor>( P<\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> P<\<psi>|\<psi>\<^bold>\<or>\<chi>>) \<^bold>\<rightarrow> P<\<phi>|(\<phi>\<^bold>\<or>\<chi>)>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close>
  by (metis assms(1) assms(2))
                                                          
lemma 
  assumes  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  shows totality   
  nitpick [expect=genuine,card i=1] \<comment>\<open>counterexample found\<close> 
  oops

lemma 
  assumes  Sp: "\<lfloor>( P<\<psi>|\<phi>> \<^bold>\<and> \<circle><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  shows transitivity 
  nitpick [expect=genuine,card i=2] \<comment>\<open>counterexample found\<close> 
  oops 

subsection \<open>Correspondence - Opt Rule\<close>

  text \<open>Opt-limitedness corresponds to D, but not vice-versa.\<close>

theorem T13: 
  assumes olimitedness   
  shows  D: "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> \<odot><\<psi>|\<phi>> \<^bold>\<rightarrow> \<P><\<psi>|\<phi>>\<rfloor>"   
  \<comment>\<open>sledgehammer\<close> 
  by (simp add: assms) 

lemma 
  assumes D: "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> \<odot><\<psi>|\<phi>> \<^bold>\<rightarrow> \<P><\<psi>|\<phi>>\<rfloor>"         
  shows olimitedness   
  nitpick [expect=genuine,card i=1] \<comment>\<open>counterexample found\<close>  
  oops 

  text \<open>Smoothness implies cautious monotony, but not vice-versa.\<close>

theorem T14: 
  assumes osmoothness   
  shows CM': "\<lfloor>( \<odot><\<psi>|\<phi>> \<^bold>\<and> \<odot><\<chi>|\<phi>> ) \<^bold>\<rightarrow> \<odot><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>"   
  \<comment>\<open>sledgehammer\<close> 
  using assms by force 

lemma 
  assumes CM: "\<lfloor>( \<odot><\<psi>|\<phi>> \<^bold>\<and> \<odot><\<chi>|\<phi>> ) \<^bold>\<rightarrow> \<odot><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  shows  osmoothness 
  nitpick [expect=genuine,card i=1] \<comment>\<open>counterexample found\<close>
  oops
 
  text \<open>Transitivity (on worlds) implies Sp and transitivity (on formulas), but not vice-versa.\<close>

theorem T15: 
  assumes transitivity   
  shows  Sp': "\<lfloor>( \<P><\<psi>|\<phi>> \<^bold>\<and> \<odot><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<odot><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"   
  \<comment>\<open>sledgehammer\<close> 
  by (metis assms) 

theorem T16: 
  assumes transitivity    
  shows  Trans': "\<lfloor>( \<P><\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> \<P><\<psi>|\<psi>\<^bold>\<or>\<xi>> )\<^bold>\<rightarrow> \<P><\<phi>|\<phi>\<^bold>\<or>\<xi>>\<rfloor>"   
  \<comment>\<open>sledgehammer\<close> 
  by (metis assms) 

lemma 
  assumes Sp: "\<lfloor>( \<P><\<psi>|\<phi>> \<^bold>\<and> \<odot><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>> ) \<^bold>\<rightarrow> \<odot><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"
  assumes Trans: "\<lfloor>( \<P><\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> \<P><\<psi>|\<psi>\<^bold>\<or>\<xi>> ) \<^bold>\<rightarrow> \<P><\<phi>|\<phi>\<^bold>\<or>\<xi>>\<rfloor>"
  shows transitivity    
  nitpick [expect=genuine,card i=2] \<comment>\<open>counterexample found\<close>
  oops 

  text \<open>Interval order implies disjunctive rationality, but not vice-versa.\<close>

lemma 
  assumes reflexivity
  shows  DR': "\<lfloor>\<odot><\<chi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<rightarrow> (\<odot><\<chi>|\<phi>> \<^bold>\<or> \<odot><\<chi>|\<psi>>)\<rfloor>"   
  nitpick [expect=genuine,card i=3] \<comment>\<open>counterexample found\<close>   
  oops 

theorem T17: 
  assumes reflexivity and Ferrers
  shows  DR': "\<lfloor>\<odot><\<chi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<rightarrow> (\<odot><\<chi>|\<phi>> \<^bold>\<or> \<odot><\<chi>|\<psi>>)\<rfloor>"   
  \<comment>\<open>sledgehammer\<close> 
  by (metis assms(2))
 
lemma 
  assumes DR: "\<lfloor>\<odot><\<chi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<rightarrow> (\<odot><\<chi>|\<phi>> \<^bold>\<or> \<odot><\<chi>|\<psi>>)\<rfloor>" 
  shows reflexivity   
  nitpick [expect=genuine,card i=1] \<comment>\<open>counterexample found\<close>  
  oops 

lemma 
  assumes DR: "\<lfloor>\<odot><\<chi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<rightarrow> (\<odot><\<chi>|\<phi>> \<^bold>\<or> \<odot><\<chi>|\<psi>>)\<rfloor>" 
  shows Ferrers  
  nitpick [expect=genuine,card i=2] \<comment>\<open>counterexample found\<close>
  oops 

subsection \<open>Correspondence - Lewis' rule\<close>

  text \<open>We have deontic explosion under the max rule.\<close>

theorem DEX: "\<lfloor>(\<diamond>\<phi> \<^bold>\<and> \<circle><\<psi>|\<phi>> \<^bold>\<and> \<circle><\<^bold>\<not>\<psi>|\<phi>>) \<^bold>\<rightarrow> \<circle><\<chi>|\<phi>>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close> 
  by blast  

  text \<open>But no deontic explosion under Lewis' rule.\<close>

lemma DEX: "\<lfloor>(\<diamond>\<phi> \<^bold>\<and> \<circ><\<psi>|\<phi>> \<^bold>\<and> \<circ><\<^bold>\<not>\<psi>|\<phi>>) \<^bold>\<rightarrow> \<circ><\<chi>|\<phi>>\<rfloor>"
  nitpick [expect=genuine,card i=2] \<comment>\<open>counterexample found\<close> 
  oops

  text \<open>The three rules are equivalent when the betterness relation  meets all the standard properties.\<close>

theorem T18:
  assumes mlimitedness and transitivity and totality
  shows "\<lfloor>\<circ><\<psi>|\<phi>>\<^bold>\<leftrightarrow>\<odot><\<psi>|\<phi>>\<rfloor>"   
  \<comment>\<open>sledgehammer\<close>
  by (smt (z3) assms)

theorem T19: 
  assumes mlimitedness and transitivity and totality
  shows "\<lfloor>\<circ><\<psi>|\<phi>>\<^bold>\<leftrightarrow>\<circle><\<psi>|\<phi>>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close>
  by (smt (z3) assms) 


  text \<open>These are the axioms of {\bf E} that do not call for a property.\<close>

theorem Abs': "\<lfloor>\<circ><\<psi>|\<phi>> \<^bold>\<rightarrow> \<box>\<circ><\<psi>|\<phi>>\<rfloor>"   
  \<comment>\<open>sledgehammer\<close> 
  by auto

theorem Nec': "\<lfloor>\<box>\<psi> \<^bold>\<rightarrow> \<circ><\<psi>|\<phi>>\<rfloor>"  
  \<comment>\<open>sledgehammer\<close>
  by auto

theorem Ext': "\<lfloor>\<box>(\<phi>\<^sub>1\<^bold>\<leftrightarrow>\<phi>\<^sub>2) \<^bold>\<rightarrow> (\<circ><\<psi>|\<phi>\<^sub>1> \<^bold>\<leftrightarrow> \<circ><\<psi>|\<phi>\<^sub>2>)\<rfloor>"  
  \<comment>\<open>sledgehammer\<close> 
  by auto

theorem Id': "\<lfloor>\<circ><\<phi>|\<phi>>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close> 
  by auto

theorem Sh': "\<lfloor>\<circ><\<psi>|\<phi>\<^sub>1\<^bold>\<and>\<phi>\<^sub>2> \<^bold>\<rightarrow> \<circ><(\<phi>\<^sub>2\<^bold>\<rightarrow>\<psi>)|\<phi>\<^sub>1>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close> 
  by auto

  text \<open>One axiom of {\bf E}, and the distinctive axioms of its extensions are invalidated in the absence of 
a property of the betterness relation.\<close>

lemma D: "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> (\<circ><\<psi>|\<phi>> \<^bold>\<rightarrow> \<integral><\<psi>|\<phi>>)\<rfloor>"
  nitpick [expect=genuine,card i=2] \<comment>\<open>counterexample found\<close> 
  oops

lemma Sp: "\<lfloor>( \<integral><\<psi>|\<phi>> \<^bold>\<and> \<circ><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circ><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>" 
  nitpick [expect=genuine,card i=3] \<comment>\<open>counterexample found\<close> 
  oops 

lemma COK:"\<lfloor>\<circ><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circ><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circ><\<psi>\<^sub>2|\<phi>>)\<rfloor>" 
  nitpick [expect=genuine,card i=2] \<comment>\<open>counterexample found\<close> 
  oops 

lemma CM: "\<lfloor>(\<circ><\<psi>|\<phi>>\<^bold>\<and>\<circ><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<circ><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  nitpick [expect=genuine,card i=2] \<comment>\<open>counterexample found\<close> 
  oops 

  text \<open>Totality implies the distinctive axiom of {\bf F}, but not vice-versa.\<close>

theorem T20:
  assumes totality
  shows "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> (\<circ><\<psi>|\<phi>> \<^bold>\<rightarrow> \<integral><\<psi>|\<phi>>)\<rfloor>" 
  \<comment>\<open>sledgehammer\<close> 
  using assms by blast

lemma  
  assumes  "\<lfloor>\<diamond>\<phi> \<^bold>\<rightarrow> (\<circ><\<psi>|\<phi>> \<^bold>\<rightarrow> \<integral><\<psi>|\<phi>>)\<rfloor>" 
  shows totality
  nitpick [expect=genuine,card i=3] \<comment>\<open>counterexample found\<close> 
  oops 

  text \<open>Transitivity implies the distinctive axioms of {\bf G}, but not vice-versa.\<close>

theorem T21:
  assumes transitivity
  shows Sp'': "\<lfloor>(\<integral><\<psi>|\<phi>> \<^bold>\<and> \<circ><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circ><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"   
 \<comment>\<open>sledgehammer\<close>
  using assms by blast 

theorem T22:
  assumes transitivity
  shows  Tr'': "\<lfloor>(\<integral><\<phi>|\<phi>\<^bold>\<or>\<psi>>\<^bold>\<and>\<integral><\<psi>|\<psi>\<^bold>\<or>\<chi>>)\<^bold>\<rightarrow> \<integral><\<phi>|\<phi>\<^bold>\<or>\<chi>>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close>
  using assms by blast

lemma
  assumes Sp'': "\<lfloor>( \<integral><\<psi>|\<phi>> \<^bold>\<and> \<circ><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<circ><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"  
  shows transitivity
  nitpick  \<comment>\<open>counterexample found\<close> 
  oops

lemma
  assumes  Tr'': "\<lfloor>(\<integral><\<phi>|\<phi>\<^bold>\<or>\<psi>>\<^bold>\<and>\<integral><\<psi>|\<psi>\<^bold>\<or>\<chi>>)\<^bold>\<rightarrow> \<integral><\<phi>|\<phi>\<^bold>\<or>\<chi>>\<rfloor>" 
  shows transitivity
  nitpick  \<comment>\<open>counterexample found\<close> 
  oops

lemma
  assumes transitivity
  shows COK:"\<lfloor>\<circ><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circ><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circ><\<psi>\<^sub>2|\<phi>>)\<rfloor>" 
  nitpick [expect=genuine,card i=2] \<comment>\<open>counterexample found\<close> 
  oops  

lemma 
  assumes totality
  shows COK:"\<lfloor>\<circ><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circ><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circ><\<psi>\<^sub>2|\<phi>>)\<rfloor>" 
  nitpick [expect=genuine,card i=3] \<comment>\<open>counterexample found\<close> 
  oops 

  text \<open>Transitivity and totality imply an axiom of {\bf E} and the distinctive axiom of {\bf F}+CM,
but not vice-versa.\<close>

theorem T23:
  assumes transitivity and totality
  shows COK':"\<lfloor>\<circ><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circ><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circ><\<psi>\<^sub>2|\<phi>>)\<rfloor>" 
  \<comment>\<open>sledgehammer\<close> 
  by (smt (verit, ccfv_SIG) assms(1) assms(2)) 

lemma
  assumes COK':"\<lfloor>\<circ><(\<psi>\<^sub>1\<^bold>\<rightarrow>\<psi>\<^sub>2)|\<phi>> \<^bold>\<rightarrow> (\<circ><\<psi>\<^sub>1|\<phi>> \<^bold>\<rightarrow> \<circ><\<psi>\<^sub>2|\<phi>>)\<rfloor>" 
  shows transitivity and totality
  nitpick [expect=genuine,card i=3] \<comment>\<open>counterexample found\<close> 
  oops 

theorem T24:
  assumes transitivity and totality
  shows CM'': "\<lfloor>(\<circ><\<psi>|\<phi>>\<^bold>\<and>\<circ><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<circ><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  \<comment>\<open>sledgehammer\<close> 
  by (metis assms)

lemma
  assumes  CM'': "\<lfloor>(\<circ><\<psi>|\<phi>>\<^bold>\<and>\<circ><\<chi>|\<phi>>)\<^bold>\<rightarrow> \<circ><\<chi>|\<phi>\<^bold>\<and>\<psi>>\<rfloor>" 
  shows transitivity and totality
  nitpick [expect=genuine,card i=3] \<comment>\<open>counterexample found\<close> 
  oops 

  text \<open>Under the opt rule transitivity alone imply Sp and Trans, but not vice-versa.\<close>

theorem T25:
  assumes transitivity 
  shows "\<lfloor>(\<P><\<psi>|\<phi>> \<^bold>\<and> \<odot><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<odot><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"   
  \<comment>\<open>sledgehammer\<close> 
  by (metis assms) 

lemma 
  assumes "transitivity"    
  shows  "\<lfloor>(\<P><\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> \<P><\<xi>|\<psi>\<^bold>\<or>\<xi>>)\<^bold>\<rightarrow>\<P><\<xi>|\<phi>\<^bold>\<or>\<xi>>\<rfloor>"   
  nitpick [expect=genuine,card i=2]  \<comment>\<open>counterexample found\<close> 
  oops 

lemma 
  assumes Sp: "\<lfloor>( \<P><\<psi>|\<phi>> \<^bold>\<and> \<odot><(\<psi>\<^bold>\<rightarrow>\<chi>)|\<phi>>) \<^bold>\<rightarrow> \<odot><\<chi>|(\<phi>\<^bold>\<and>\<psi>)>\<rfloor>"
          and  Trans: "\<lfloor>(\<P><\<phi>|\<phi>\<^bold>\<or>\<psi>> \<^bold>\<and> \<P><\<xi>|\<psi>\<^bold>\<or>\<xi>>)\<^bold>\<rightarrow>\<P><\<xi>|\<phi>\<^bold>\<or>\<xi>>\<rfloor>"
  shows transitivity    
  nitpick [expect=genuine,card i=2]  \<comment>\<open>counterexample found\<close> 
  oops 

end