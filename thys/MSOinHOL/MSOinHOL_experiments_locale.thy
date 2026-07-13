theory MSOinHOL_experiments_locale
  imports MSOinHOL_faithfulness_locale
begin

text \<open>Demonstration: minimal-shallow proofs that hold in every
  interpretation of the \<open>MinS\<close> locale transfer to validity in the model
  class whose domains are the assignment ranges.\<close>

text \<open>Derived rule: from validity in every minimal interpretation to
  range-relative deep validity.\<close>

lemmas MinS_to_Deep = FaithfulMS_all[THEN iffD1, rule_format]

text \<open>Cosmetic locale-level rewrite rules for derived connectives under
  \<open>DpToShM\<close>.\<close>

lemma (in MinS) OrM_simp [DefM]: "\<lparr>\<phi> \<or>\<^sup>d \<psi>\<rparr> = \<lparr>\<phi>\<rparr> \<or>\<^sup>m \<lparr>\<psi>\<rparr>"
  by (simp add: OrD_def OrM_def)

lemma (in MinS) ImpM_simp [DefM]: "\<lparr>\<phi> \<supset>\<^sup>d \<psi>\<rparr> = \<lparr>\<phi>\<rparr> \<supset>\<^sup>m \<lparr>\<psi>\<rparr>"
  by (simp add: ImpD_def DefM)

text \<open>Example: a membership tautology proved using only minimal-shallow
  infrastructure.\<close>

lemma (in MinS) Mem_MinS: "\<Turnstile>\<^sup>m \<lparr>(P\<^sup>d(x,x)) \<supset>\<^sup>d (P\<^sup>d(x,x))\<rparr>"
  by (auto simp: DefM)

text \<open>Transfer to the range-relative deep embedding requires no further
  work.\<close>

lemma "\<langle>I,Range g,Range G\<rangle>,g,G \<Turnstile>\<^sup>d ((P\<^sup>d(x,x)) \<supset>\<^sup>d (P\<^sup>d(x,x)))"
  by (rule MinS_to_Deep) (blast intro: MinS.Mem_MinS)

end
