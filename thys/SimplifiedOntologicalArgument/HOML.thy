section\<open>Higher-Order Modal Logic in HOL (cf.~\<^cite>\<open>"J23"\<close> and Fig.~1 in \<^cite>\<open>"C85"\<close>).\<close>

theory HOML imports Main
begin
nitpick_params[user_axioms,expect=genuine]

text\<open>Type i is associated with possible worlds and type e with entities:\<close>
typedecl i \<comment>\<open>Possible worlds\<close>  
typedecl e \<comment>\<open>Individuals\<close>      
type_synonym \<sigma> = "i\<Rightarrow>bool" \<comment>\<open>World-lifted propositions\<close>
type_synonym \<gamma> = "e\<Rightarrow>\<sigma>" \<comment>\<open>Lifted predicates\<close>
type_synonym \<mu> = "\<sigma>\<Rightarrow>\<sigma>" \<comment>\<open>Unary modal connectives\<close>
type_synonym \<nu> = "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" \<comment>\<open>Binary modal connectives\<close>

text\<open>Logical connectives (operating on truth-sets):\<close>
abbreviation c1::\<sigma> ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"
abbreviation c2::\<sigma> ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True"
abbreviation c3::\<mu> ("\<^bold>\<not>_"[52]53) where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w.\<not>(\<phi> w)"
abbreviation c4::\<nu> (infix"\<^bold>\<and>"50) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<and>(\<psi> w)"   
abbreviation c5::\<nu> (infix"\<^bold>\<or>"49) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<or>(\<psi> w)"
abbreviation c6::\<nu> (infix"\<^bold>\<rightarrow>"48) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<longrightarrow>(\<psi> w)"  
abbreviation c7::\<nu> (infix"\<^bold>\<leftrightarrow>"47) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w.(\<phi> w)\<longleftrightarrow>(\<psi> w)"
consts R::"i\<Rightarrow>i\<Rightarrow>bool" ("_\<^bold>r_")  \<comment>\<open>Accessibility relation\<close>
abbreviation c8::\<mu> ("\<^bold>\<box>_"[54]55) where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w.\<forall>v.(w\<^bold>rv)\<longrightarrow>(\<phi> v)"
abbreviation c9::\<mu> ("\<^bold>\<diamond>_"[54]55) where "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w.\<exists>v.(w\<^bold>rv)\<and>(\<phi> v)"
abbreviation c10::"\<gamma>\<Rightarrow>\<gamma>" ("\<^bold>\<not>_"[52]53) where "\<^bold>\<not>\<Phi> \<equiv> \<lambda>x.\<lambda>w.\<not>(\<Phi> x w)"
abbreviation c11::"\<gamma>\<Rightarrow>\<gamma>" ("\<^bold>\<rightharpoondown>_") where "\<^bold>\<rightharpoondown>\<Phi> \<equiv> \<lambda>x.\<lambda>w.\<not>(\<Phi> x w)"
abbreviation c12::"e\<Rightarrow>e\<Rightarrow>\<sigma>" ("_\<^bold>=_") where "x\<^bold>=y \<equiv> \<lambda>w.(x=y)"
abbreviation c13::"e\<Rightarrow>e\<Rightarrow>\<sigma>" ("_\<^bold>\<noteq>_") where "x\<^bold>\<noteq>y \<equiv> \<lambda>w.(x\<noteq>y)"

text\<open>Polymorphic possibilist quantification:\<close>
abbreviation q1::"('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x.(\<Phi> x w)"
abbreviation q2 (binder"\<^bold>\<forall>"[10]11) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
abbreviation q3::"('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x.(\<Phi> x w)"   
abbreviation q4 (binder"\<^bold>\<exists>"[10]11) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>" 

text\<open>Actualist quantification for individuals/entities:\<close>
consts existsAt::\<gamma> ("_\<^bold>@_")  
abbreviation q5::"\<gamma>\<Rightarrow>\<sigma>" ("\<^bold>\<forall>\<^sup>E") where "\<^bold>\<forall>\<^sup>E\<Phi> \<equiv> \<lambda>w.\<forall>x.(x\<^bold>@w)\<longrightarrow>(\<Phi> x w)"
abbreviation q6 (binder"\<^bold>\<forall>\<^sup>E"[8]9) where "\<^bold>\<forall>\<^sup>Ex. \<phi>(x) \<equiv> \<^bold>\<forall>\<^sup>E\<phi>"     
abbreviation q7::"\<gamma>\<Rightarrow>\<sigma>" ("\<^bold>\<exists>\<^sup>E") where "\<^bold>\<exists>\<^sup>E\<Phi> \<equiv> \<lambda>w.\<exists>x.(x\<^bold>@w)\<and>(\<Phi> x w)"
abbreviation q8 (binder"\<^bold>\<exists>\<^sup>E"[8]9) where "\<^bold>\<exists>\<^sup>Ex. \<phi>(x) \<equiv> \<^bold>\<exists>\<^sup>E\<phi>"

text\<open>Meta-logical predicate for global validity:\<close>
abbreviation g1::"\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>") where "\<lfloor>\<psi>\<rfloor> \<equiv>  \<forall>w. \<psi> w"

text\<open>Barcan and converse Barcan formula:\<close>
lemma True nitpick[satisfy] oops  \<comment>\<open>Model found by Nitpick\<close>
lemma "\<lfloor>(\<^bold>\<forall>\<^sup>Ex.\<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex.(\<phi> x))\<rfloor>" nitpick oops \<comment>\<open>Ctm\<close>
lemma "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex.(\<phi> x)) \<^bold>\<rightarrow> (\<^bold>\<forall>\<^sup>Ex.\<^bold>\<box>(\<phi> x))\<rfloor>" nitpick oops \<comment>\<open>Ctm\<close>
lemma "\<lfloor>(\<^bold>\<forall>x.\<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x. \<phi> x)\<rfloor>" by simp 
lemma "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>x.(\<phi> x)) \<^bold>\<rightarrow> (\<^bold>\<forall>x.\<^bold>\<box>(\<phi> x))\<rfloor>" by simp
end
