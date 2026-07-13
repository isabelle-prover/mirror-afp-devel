theory MSOinHOL_faithfulness
  imports MSOinHOL_shallow_minimal
begin

text \<open>Re-issuing the locale faithfulness theorems at the constants level.\<close>

text \<open>Deep \<open>\<longleftrightarrow>\<close> maximal shallow.\<close>

theorem "(\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>s \<lbrakk>\<phi>\<rbrakk>) \<longleftrightarrow> (\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>)"
  using FaithfulSDlem .

theorem "(\<Turnstile>\<^sup>s \<lbrakk>\<phi>\<rbrakk>) \<longleftrightarrow> (\<Turnstile>\<^sup>d \<phi>)"
  using FaithfulSD .

text \<open>Deep \<open>\<longleftrightarrow>\<close> minimal shallow, relative to the ranges of the chosen
  assignments \<open>gg\<close> and \<open>GG\<close>.\<close>

theorem "\<lparr>\<phi>\<rparr> \<longleftrightarrow> (\<langle>II,Range gg,Range GG\<rangle>,gg,GG \<Turnstile>\<^sup>d \<phi>)"
  using FaithfulMDlem .

theorem "(\<Turnstile>\<^sup>m \<lparr>\<phi>\<rparr>) \<longleftrightarrow> (\<langle>II,Range gg,Range GG\<rangle>,gg,GG \<Turnstile>\<^sup>d \<phi>)"
  using FaithfulMD .

text \<open>Minimal shallow \<open>\<longleftrightarrow>\<close> maximal shallow, again relative to the ranges
  of \<open>gg\<close> and \<open>GG\<close>; obtained by composing the two preceding bridges.\<close>

theorem "\<lparr>\<phi>\<rparr> \<longleftrightarrow> (\<langle>II,Range gg,Range GG\<rangle>,gg,GG \<Turnstile>\<^sup>s \<lbrakk>\<phi>\<rbrakk>)"
  using FaithfulMSlem .

theorem "(\<Turnstile>\<^sup>m \<lparr>\<phi>\<rparr>) \<longleftrightarrow> (\<langle>II,Range gg,Range GG\<rangle>,gg,GG \<Turnstile>\<^sup>s \<lbrakk>\<phi>\<rbrakk>)"
  using FaithfulMS .

text \<open>Global form across all interpretations and the one-directional bridge
  to full deep validity.\<close>

theorem
  "(\<forall>II gg GG. (\<Turnstile>\<^sup>m (MinS.DpToShM II gg GG \<phi>))) = (\<forall>I g G. \<langle>I,Range g,Range G\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>)"
  using FaithfulMS_all by (simp add: MinS.ValM_def)

theorem "(\<Turnstile>\<^sup>d \<phi>) \<Longrightarrow> (\<forall>II gg GG. (\<Turnstile>\<^sup>m (MinS.DpToShM II gg GG \<phi>)))"
  using Deep_to_MinS by (simp add: MinS.ValM_def)

text \<open>Consistency check.\<close>

lemma True nitpick[satisfy] oops

end
