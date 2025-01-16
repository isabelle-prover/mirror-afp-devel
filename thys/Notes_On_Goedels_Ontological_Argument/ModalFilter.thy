subsection\<open>ModalFilter.thy (Figure 5 of \cite{J75})\<close>
text\<open>Set filter and ultrafilter formalized for our modal logic setting.\<close>
theory ModalFilter imports HOMLinHOL
begin 

type_synonym \<tau>="e\<Rightarrow>\<sigma>"
abbreviation Element::"\<tau>\<Rightarrow>(\<tau>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (infix "\<^bold>\<in>" 90) where "\<phi>\<^bold>\<in>S \<equiv> S \<phi>"
abbreviation EmptySet::\<tau> ("\<^bold>\<emptyset>") where "\<^bold>\<emptyset> \<equiv> \<lambda>x. \<^bold>\<bottom>" 
abbreviation UniversalSet::\<tau> ("\<^bold>U") where "\<^bold>U \<equiv> \<lambda>x. \<^bold>\<top>"
abbreviation Subset::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<sigma>" (infix "\<^bold>\<subseteq>" 80) 
  where "\<phi>\<^bold>\<subseteq>\<psi> \<equiv> \<^bold>\<forall>x.((\<phi> x) \<^bold>\<supset> (\<psi> x))"
abbreviation SubsetE::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<sigma>" (infix "\<^bold>\<subseteq>\<^sup>E" 80) 
  where "\<phi>\<^bold>\<subseteq>\<^sup>E\<psi> \<equiv> \<^bold>\<forall>\<^sup>Ex.((\<phi> x) \<^bold>\<supset> (\<psi> x))"
abbreviation Intersection::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infix "\<^bold>\<sqinter>" 91) 
  where "\<phi>\<^bold>\<sqinter>\<psi> \<equiv> \<lambda>x.((\<phi> x) \<^bold>\<and> (\<psi> x))"
abbreviation Inverse::"\<tau>\<Rightarrow>\<tau>" ("\<inverse>") 
  where "\<inverse>\<psi> \<equiv> \<lambda>x. \<^bold>\<not>(\<psi> x)" 
abbreviation "Filter \<Phi> \<equiv> \<^bold>U\<^bold>\<in>\<Phi> \<^bold>\<and> \<^bold>\<not>(\<^bold>\<emptyset>\<^bold>\<in>\<Phi>) \<^bold>\<and>
  (\<^bold>\<forall>\<phi> \<psi>. \<phi>\<^bold>\<in>\<Phi> \<^bold>\<and> \<phi>\<^bold>\<subseteq>\<^sup>E\<psi> \<^bold>\<supset> \<psi>\<^bold>\<in>\<Phi>) \<^bold>\<and> (\<^bold>\<forall>\<phi> \<psi>. \<phi>\<^bold>\<in>\<Phi> \<^bold>\<and> \<psi>\<^bold>\<in>\<Phi> \<^bold>\<supset> \<phi>\<^bold>\<sqinter>\<psi>\<^bold>\<in>\<Phi>)"
abbreviation "UFilter \<Phi> \<equiv> Filter \<Phi> \<^bold>\<and> (\<^bold>\<forall>\<phi>. \<phi>\<^bold>\<in>\<Phi> \<^bold>\<or> (\<inverse>\<phi>)\<^bold>\<in>\<Phi>)"
abbreviation "FilterP \<Phi> \<equiv> \<^bold>U\<^bold>\<in>\<Phi> \<^bold>\<and> \<^bold>\<not>(\<^bold>\<emptyset>\<^bold>\<in>\<Phi>) \<^bold>\<and> (\<^bold>\<forall>\<phi> \<psi>. \<phi>\<^bold>\<in>\<Phi> \<^bold>\<and> \<phi>\<^bold>\<subseteq>\<psi> \<^bold>\<supset> \<psi>\<^bold>\<in>\<Phi>) \<^bold>\<and>
  (\<^bold>\<forall>\<phi> \<psi>. \<phi>\<^bold>\<in>\<Phi> \<^bold>\<and> \<psi>\<^bold>\<in>\<Phi> \<^bold>\<supset> \<phi>\<^bold>\<sqinter>\<psi>\<^bold>\<in>\<Phi>)"
abbreviation "UFilterP \<Phi> \<equiv> FilterP \<Phi> \<^bold>\<and> (\<^bold>\<forall>\<phi>. \<phi>\<^bold>\<in>\<Phi> \<^bold>\<or> (\<inverse>\<phi>)\<^bold>\<in>\<Phi>)"

end





