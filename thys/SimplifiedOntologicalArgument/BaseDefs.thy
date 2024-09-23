subsection\<open>Preliminaries: Further Basic Notions (Fig.~3 in \<^cite>\<open>"C85"\<close>)\<close>

theory BaseDefs imports HOML
begin  
text\<open>Positive properties.\<close> 
consts posProp::"\<gamma>\<Rightarrow>\<sigma>" (\<open>\<P>\<close>)

text\<open>Basic definitions for modal ontological argument.\<close>
abbreviation a (\<open>_\<^bold>\<sqsubseteq>_\<close>) where "X\<^bold>\<sqsubseteq>Y \<equiv> \<^bold>\<forall>\<^sup>Ez.((X z) \<^bold>\<rightarrow> (Y z))"
abbreviation b (\<open>_\<Rrightarrow>_\<close>) where "X\<Rrightarrow>Y \<equiv> \<^bold>\<box>(X\<^bold>\<sqsubseteq>Y)"
abbreviation c (\<open>\<P>\<o>\<s>\<close>) where "\<P>\<o>\<s> Z \<equiv> \<^bold>\<forall>X.((Z X) \<^bold>\<rightarrow> (\<P> X))"
abbreviation d (\<open>_\<Sqinter>_\<close>) where "X\<Sqinter>\<Z> \<equiv> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Eu.((X u) \<^bold>\<leftrightarrow> (\<^bold>\<forall>Y.((\<Z> Y) \<^bold>\<rightarrow> (Y u)))))"

text\<open>Definition of Godlike.\<close>
definition G (\<open>\<G>\<close>) where "\<G> x \<equiv> \<^bold>\<forall>Y.((\<P> Y) \<^bold>\<rightarrow> (Y x))"

text\<open>Definitions of Essence and Necessary Existence.\<close>
definition E (\<open>\<E>\<close>) where "\<E> Y x \<equiv> (Y x) \<^bold>\<and> (\<^bold>\<forall>Z.((Z x) \<^bold>\<rightarrow> (Y\<Rrightarrow>Z)))"
definition NE (\<open>\<N>\<E>\<close>) where "\<N>\<E> x \<equiv> \<^bold>\<forall>Y.((\<E> Y x) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>E Y))"
end


