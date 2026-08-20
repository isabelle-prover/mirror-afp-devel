theory MSOinHOL_faithfulness_locale
  imports
    MSOinHOL_deep
    MSOinHOL_shallow
    MSOinHOL_shallow_minimal_locale
    MSOinHOL_deep_subst_lemma
begin

text \<open>Translation from deep to maximal shallow (transparent: both use
  named-variable binders).\<close>

fun DpToShS ("\<lbrakk>_\<rbrakk>")
  where
    "\<lbrakk>r\<^sup>d(x,y)\<rbrakk> = r\<^sup>s(x,y)"
  | "\<lbrakk>X\<^sup>d(x)\<rbrakk> = X\<^sup>s(x)"
  | "\<lbrakk>\<not>\<^sup>d\<phi>\<rbrakk> = \<not>\<^sup>s\<lbrakk>\<phi>\<rbrakk>"
  | "\<lbrakk>\<phi> \<and>\<^sup>d \<psi>\<rbrakk> = \<lbrakk>\<phi>\<rbrakk> \<and>\<^sup>s \<lbrakk>\<psi>\<rbrakk>"
  | "\<lbrakk>\<exists>\<^sup>dv. \<phi>\<rbrakk> = (\<exists>\<^sup>sv. \<lbrakk>\<phi>\<rbrakk>)"
  | "\<lbrakk>\<exists>\<^sup>d\<^sub>2V. \<phi>\<rbrakk> = (\<exists>\<^sup>s\<^sub>2V. \<lbrakk>\<phi>\<rbrakk>)"

text \<open>Translation from deep to minimal shallow (within the locale
  \<open>MinS\<close>): each binder is bridged by safe substitution into a HOL-level
  binder---first-order via \<open>[v\<leftarrow>\<^sub>rd]\<close>, second-order via
  \<open>[V\<leftarrow>\<^sub>r\<^sub>2D]\<close>.\<close>

fun (in MinS) DpToShM ("\<lparr>_\<rparr>")
  where
    "\<lparr>r\<^sup>d(x,y)\<rparr> = r\<^sup>m(x,y)"
  | "\<lparr>X\<^sup>d(x)\<rparr> = X\<^sup>m(x)"
  | "\<lparr>\<not>\<^sup>d\<phi>\<rparr> = \<not>\<^sup>m\<lparr>\<phi>\<rparr>"
  | "\<lparr>\<phi> \<and>\<^sup>d \<psi>\<rparr> = \<lparr>\<phi>\<rparr> \<and>\<^sup>m \<lparr>\<psi>\<rparr>"
  | "\<lparr>\<exists>\<^sup>dv. \<phi>\<rparr> = (\<exists>\<^sup>md. \<lparr>[v \<leftarrow>\<^sub>r d](\<phi>)\<rparr>)"
  | "\<lparr>\<exists>\<^sup>d\<^sub>2V. \<phi>\<rparr> = (\<exists>\<^sup>m\<^sub>2D. \<lparr>[V \<leftarrow>\<^sub>r\<^sub>2 D](\<phi>)\<rparr>)"

text \<open>Faithfulness deep \<open>\<longleftrightarrow>\<close> maximal shallow.  Pointwise first; global
  by unfolding validity.\<close>

theorem FaithfulSDlem:
  "(\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>s \<lbrakk>\<phi>\<rbrakk>) \<longleftrightarrow> (\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>)"
  by (induct \<phi> arbitrary: g G; auto simp: DefS DefD)

theorem FaithfulSD: "(\<Turnstile>\<^sup>s \<lbrakk>\<phi>\<rbrakk>) \<longleftrightarrow> (\<Turnstile>\<^sup>d \<phi>)"
  by (simp add: FaithfulSDlem ValD_def ValS_def)

text \<open>Faithfulness deep \<open>\<longleftrightarrow>\<close> minimal shallow, parametrised by the
  locale, relative to the ranges of \<open>gg\<close> and \<open>GG\<close>.\<close>

context MinS
begin

theorem FaithfulMDlem:
  "\<lparr>\<phi>\<rparr> \<longleftrightarrow> (\<langle>II,Range gg,Range GG\<rangle>,gg,GG \<Turnstile>\<^sup>d \<phi>)"
  by (induct \<phi> rule: QInduct; simp add: DefD DefM) blast+

theorem FaithfulMD:
  "(\<Turnstile>\<^sup>m \<lparr>\<phi>\<rparr>) \<longleftrightarrow> (\<langle>II,Range gg,Range GG\<rangle>,gg,GG \<Turnstile>\<^sup>d \<phi>)"
  using FaithfulMDlem by (simp add: ValM_def)

text \<open>Faithfulness minimal shallow \<open>\<longleftrightarrow>\<close> maximal shallow, parametrised by
  the locale, relative to the ranges of \<open>gg\<close> and \<open>GG\<close>; obtained by
  composing @{thm [source] FaithfulSDlem} and @{thm [source] FaithfulMDlem}.\<close>

theorem FaithfulMSlem:
  "\<lparr>\<phi>\<rparr> \<longleftrightarrow> (\<langle>II,Range gg,Range GG\<rangle>,gg,GG \<Turnstile>\<^sup>s \<lbrakk>\<phi>\<rbrakk>)"
  using FaithfulSDlem FaithfulMDlem by auto

theorem FaithfulMS:
  "(\<Turnstile>\<^sup>m \<lparr>\<phi>\<rparr>) \<longleftrightarrow> (\<langle>II,Range gg,Range GG\<rangle>,gg,GG \<Turnstile>\<^sup>s \<lbrakk>\<phi>\<rbrakk>)"
  using FaithfulMSlem by (simp add: ValM_def)

end

text \<open>Global faithfulness: a formula holds in every minimal interpretation
  of \<open>MinS\<close> iff it holds in every model whose first- and second-order
  domains are exactly the ranges of the chosen assignments.\<close>

theorem FaithfulMS_all:
  "(\<forall>II gg GG. MinS.ValM (MinS.DpToShM II gg GG \<phi>)) = (\<forall>I g G. \<langle>I,Range g,Range G\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>)"
  by (simp add: MinS.FaithfulMD)

text \<open>One direction toward full deep validity: deep validity transfers to
  every minimal interpretation.  The converse is the (second-order)
  surjectivity problem discussed in the paper.\<close>

theorem Deep_to_MinS:
  "(\<Turnstile>\<^sup>d \<phi>) \<Longrightarrow> (\<forall>II gg GG. MinS.ValM (MinS.DpToShM II gg GG \<phi>))"
  by (metis (mono_tags, lifting) MinS.FaithfulMD ValD_def)

text \<open>Consistency check.\<close>

lemma True nitpick[satisfy] oops

end
