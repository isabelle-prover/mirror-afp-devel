subsection\<open>ThereIsNoEvil2.thy (Figure 11 of \cite{J75})\<close>
text\<open>Importing Gödel's modified axioms from Figure 8 we can prove that necessarily there exists
no entity that possesses all non-positive (=negative) properties.\<close>
theory ThereIsNoEvil2 imports GoedelVariantHOML3
begin  

definition Evil ("Evil") where "Evil x \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<not> P \<phi> \<^bold>\<supset> \<phi> x"
theorem NecNoEvil: "\<lfloor>\<^bold>\<box>(\<^bold>\<not>(\<^bold>\<exists>\<^sup>Ex.  Evil x))\<rfloor>" 
  \<comment>\<open>sledgehammer(Ax1Gen Ax2a Evil\_def)\<close> oops  \<comment>\<open>Proof found\<close>

end
