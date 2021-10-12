theory Labeled_Hoare
imports
  "../../Case_Labeling"
  "HOL-Hoare.Hoare_Logic"
begin

subsection \<open>A labeling VCG for HOL/Hoare\<close>

context begin
  interpretation Labeling_Syntax .

  lemma LSeqRule:
    assumes "C\<langle>IC,CT,OC1: Valid P c1 a1 Q\<rangle>"
      and "C\<langle>Suc OC1,CT,OC: Valid Q c2 a2 R\<rangle>"
    shows "C\<langle>IC,CT,OC: Valid P (Seq c1 c2) (Aseq a1 a2) R\<rangle>"
    using assms unfolding LABEL_simps by (rule SeqRule)

  lemma LSkipRule:
    assumes "V\<langle>(''weaken'', IC, []),CT: p \<subseteq> q\<rangle>"
    shows "C\<langle>IC,CT,IC: Valid p SKIP a q\<rangle>"
    using assms unfolding LABEL_simps  by (rule SkipRule)

  lemmas LAbortRule = LSkipRule  \<comment> \<open>dummy version\<close>

  lemma LBasicRule:
    assumes "V\<langle>(''basic'', IC, []),CT: p \<subseteq> {s. f s \<in> q}\<rangle>"
    shows "C\<langle>IC,CT,IC: Valid p (Basic f) a q\<rangle>"
    using assms unfolding LABEL_simps  by (rule BasicRule)

  lemma LCondRule:
    fixes IC CT defines "CT' \<equiv> (''cond'', IC, []) # CT "
    assumes "V\<langle>(''vc'', IC, []),(''cond'', IC, []) # CT: p \<subseteq> {s. (s \<in> b \<longrightarrow> s \<in> w) \<and> (s \<notin> b \<longrightarrow> s \<in> w')}\<rangle>"
      and "C\<langle>Suc IC,(''then'', IC, []) # (''cond'', IC, []) # CT,OC1: Valid w c1 a1 q\<rangle>"
      and "C\<langle>Suc OC1,(''else'', Suc OC1, []) # (''cond'', IC, []) # CT,OC: Valid w' c2 a2 q\<rangle>"
    shows "C\<langle>IC,CT,OC: Valid p (Cond b c1 c2) (Acond a1 a2) q\<rangle>"
    using assms(2-) unfolding LABEL_simps by (rule CondRule)

  lemma LWhileRule:
    fixes IC CT defines "CT' \<equiv> (''while'', IC, []) # CT"
    assumes "V\<langle>(''precondition'', IC, []),(''while'', IC, []) # CT: p \<subseteq> i\<rangle>"
      and "C\<langle>Suc IC,(''invariant'', Suc IC, []) # (''while'', IC, []) # CT,OC: Valid (i \<inter> b) c (A 0) i\<rangle>"
      and "V\<langle>(''postcondition'', IC, []),(''while'', IC, []) # CT: i \<inter> - b \<subseteq> q\<rangle>"
    shows "C\<langle>IC,CT,OC: Valid p (While b c) (Awhile i v A) q\<rangle>"
    using assms(2-) unfolding LABEL_simps  by (rule WhileRule)

  lemma LABELs_to_prems:
    "(C\<langle>IC, CT, OC: True\<rangle> \<Longrightarrow> P) \<Longrightarrow> C\<langle>IC, CT, OC: P\<rangle>"
    "(V\<langle>x, ct: True\<rangle> \<Longrightarrow> P) \<Longrightarrow> V\<langle>x, ct: P\<rangle>"
    unfolding LABEL_simps by simp_all

  lemma LABELs_to_concl:
    "C\<langle>IC, CT, OC: True\<rangle> \<Longrightarrow> C\<langle>IC, CT, OC: P\<rangle> \<Longrightarrow> P"
    "V\<langle>x, ct: True\<rangle> \<Longrightarrow> V\<langle>x, ct: P\<rangle> \<Longrightarrow> P"
    unfolding LABEL_simps .

end


ML_file \<open>labeled_hoare_tac.ML\<close>

method_setup labeled_vcg = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (Labeled_Hoare.hoare_tac ctxt (K all_tac)))\<close>
  "verification condition generator"

method_setup labeled_vcg_simp = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (Labeled_Hoare.hoare_tac ctxt (asm_full_simp_tac ctxt)))\<close>
  "verification condition generator"

method_setup casified_vcg = \<open>
  Scan.lift (Casify.casify_options casify_defs) >>
    (fn opt => fn ctxt => Util.SIMPLE_METHOD_CASES (
      HEADGOAL (Labeled_Hoare.hoare_tac ctxt (K all_tac))
      THEN_CONTEXT Casify.casify_tac opt))
\<close>

method_setup casified_vcg_simp = \<open>
  Scan.lift (Casify.casify_options casify_defs) >>
    (fn opt => fn ctxt => Util.SIMPLE_METHOD_CASES (
      HEADGOAL (Labeled_Hoare.hoare_tac ctxt (asm_full_simp_tac ctxt))
      THEN_CONTEXT Casify.casify_tac opt))
\<close>

end
