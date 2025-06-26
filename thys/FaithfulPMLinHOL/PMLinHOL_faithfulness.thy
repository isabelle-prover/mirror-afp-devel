section\<open>Automated faithfulness proofs\label{sec:faithfulness}\<close>

theory PMLinHOL_faithfulness (* Christoph Benzmüller, 2025 *)
  imports PMLinHOL_deep PMLinHOL_shallow PMLinHOL_shallow_minimal
begin 

\<comment>\<open>Mappings: deep to maximal shallow and deep to minimal shallow\<close>
primrec DpToShMax ("\<lparr>_\<rparr>") where "\<lparr>\<phi>\<^sup>d\<rparr>= \<phi>\<^sup>s" | "\<lparr>\<not>\<^sup>d \<phi>\<rparr> = \<not>\<^sup>s \<lparr>\<phi>\<rparr>" | "\<lparr>\<phi> \<supset>\<^sup>d \<psi>\<rparr> = \<lparr>\<phi>\<rparr> \<supset>\<^sup>s \<lparr>\<psi>\<rparr>" | "\<lparr>\<box>\<^sup>d \<phi>\<rparr> = \<box>\<^sup>s \<lparr>\<phi>\<rparr>" 
primrec DpToShMin ("\<lbrakk>_\<rbrakk>") where "\<lbrakk>\<phi>\<^sup>d\<rbrakk>= \<phi>\<^sup>m" | "\<lbrakk>\<not>\<^sup>d \<phi>\<rbrakk> = \<not>\<^sup>m \<lbrakk>\<phi>\<rbrakk>" | "\<lbrakk>\<phi> \<supset>\<^sup>d \<psi>\<rbrakk> = \<lbrakk>\<phi>\<rbrakk> \<supset>\<^sup>m \<lbrakk>\<psi>\<rbrakk>" | "\<lbrakk>\<box>\<^sup>d \<phi>\<rbrakk> = \<box>\<^sup>m \<lbrakk>\<phi>\<rbrakk>" 

\<comment>\<open>Proving faithfulness between deep and maximal shallow\<close>
theorem Faithful1a: "\<forall>W R V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<longleftrightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>s \<lparr>\<phi>\<rparr>" apply induct by auto
theorem Faithful1b: "\<Turnstile>\<^sup>d \<phi> \<longleftrightarrow> \<Turnstile>\<^sup>s \<lparr>\<phi>\<rparr>" using Faithful1a by auto

\<comment>\<open>Proving faithfulness between deep and minimal shallow\<close>
theorem Faithful2: "\<forall>w. \<langle>(\<lambda>x::\<w>. True),R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi> \<longleftrightarrow> w \<Turnstile>\<^sup>m \<lbrakk>\<phi>\<rbrakk>" apply induct by auto

\<comment>\<open>Proving faithfulness maximal shallow and minimal shallow\<close>
theorem Faithful3: "\<forall>w. \<langle>(\<lambda>x::\<w>. True),R,V\<rangle>,w \<Turnstile>\<^sup>s \<lparr>\<phi>\<rparr> \<longleftrightarrow> w \<Turnstile>\<^sup>m \<lbrakk>\<phi>\<rbrakk>" apply induct by auto

\<comment>\<open>Additional check for soundness for the minimal shallow embedding\<close>
lemma Sound1: "\<Turnstile>\<^sup>m \<psi> \<longrightarrow> (\<exists>\<phi>. \<psi>=\<lbrakk>\<phi>\<rbrakk> \<and> \<Turnstile>\<^sup>d \<phi>)"  \<comment>\<open>sledgehammer: Proof found; metis reconstruction timeout\<close> oops
lemma Sound2: "\<Turnstile>\<^sup>m \<psi> \<longrightarrow> (\<exists>\<phi>. \<psi>=\<lbrakk>\<phi>\<rbrakk> \<and> \<Turnstile>\<^sup>m \<lbrakk>\<phi>\<rbrakk>)" \<comment>\<open>sledgehammer: Proof found; metis reconstruction timeout\<close> oops
end


