subsection\<open>ThereIsNoEvil1.thy (Figure 10 of \cite{J75})\<close>
text\<open>Importing Gödel’s modified axioms from Figure 7 we can prove that necessarily there exists
no entity that possesses all non-positive (=negative) properties.\<close>
theory ThereIsNoEvil1 imports GoedelVariantHOML2
begin  

definition Evil ("Evil") where "Evil x \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<not> P \<phi> \<^bold>\<supset> \<phi> x"

theorem NecNoEvil: "\<lfloor>\<^bold>\<box>(\<^bold>\<not>(\<^bold>\<exists>\<^sup>Ex.  Evil x))\<rfloor>" 
  \<comment>\<open>sledgehammer(Ax2a Ax4 Evil\_def)\<close>  \<comment>\<open>Proof found\<close>
  proof -
    have    "\<lfloor>\<^bold>\<not>P(\<lambda>y.\<^bold>\<bottom>)\<rfloor>"  using Ax2a Ax4 by blast
    hence  "\<lfloor>(\<^bold>\<forall>\<^sup>Ex.  Evil x \<^bold>\<supset> (\<lambda>y.\<^bold>\<bottom>) x)\<rfloor>" using Evil_def by auto
    hence  "\<lfloor>(\<^bold>\<forall>\<^sup>Ex.  Evil x \<^bold>\<supset> \<^bold>\<bottom>)\<rfloor>" by auto
    hence  "\<lfloor>(\<^bold>\<exists>\<^sup>Ex.  Evil x) \<^bold>\<supset> \<^bold>\<bottom>\<rfloor>" by auto
    hence  "\<lfloor>\<^bold>\<not>(\<^bold>\<exists>\<^sup>Ex. Evil x)\<rfloor>" by blast
    thus ?thesis by blast
  qed

end


