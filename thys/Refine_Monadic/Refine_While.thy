header {* \isaheader{While-Loops} *}
theory Refine_While
imports 
  Refine_Basic "Generic/RefineG_While"
begin

definition WHILEIT ("WHILE\<^sub>T\<^bsup>_\<^esup>") where 
  "WHILEIT \<equiv> iWHILEIT bind RETURN"
definition WHILEI ("WHILE\<^bsup>_\<^esup>") where "WHILEI \<equiv> iWHILEI bind RETURN"
definition WHILET ("WHILE\<^sub>T") where "WHILET \<equiv> iWHILET bind RETURN"
definition WHILE where "WHILE \<equiv> iWHILE bind RETURN"

interpretation while?: generic_WHILE_rules bind RETURN SPEC
  WHILEIT WHILEI WHILET WHILE
  apply unfold_locales
  apply (simp_all add: WHILEIT_def WHILEI_def WHILET_def WHILE_def)
  apply (subst RES_Sup_RETURN[symmetric]) 
  apply (rule_tac f=Sup in arg_cong) apply auto []
  apply (erule bind_rule)
  done

lemmas [refine_vcg] = WHILEI_rule
lemmas [refine_vcg] = WHILEIT_rule

subsection {* Data Refinement Rules *}

lemma ref_WHILEI_invarI:
  assumes "I s \<Longrightarrow> M \<le> \<Down>R (WHILEI I b f s)"
  shows "M \<le> \<Down>R (WHILEI I b f s)"
  apply (subst WHILEI_unfold)
  apply (cases "I s")
  apply (subst WHILEI_unfold[symmetric])
  apply (erule assms)
  apply simp
  done

lemma WHILEI_le_rule:
  assumes R0: "(s,s')\<in>R"
  assumes RS: "\<And>W s s'. \<lbrakk>\<And>s s'. (s,s')\<in>R \<Longrightarrow> W s \<le> M s'; (s,s')\<in>R\<rbrakk> \<Longrightarrow> 
    do {ASSERT (I s); if b s then bind (f s) W else RETURN s} \<le> M s'"
  shows "WHILEI I b f s \<le> M s'"
  unfolding WHILEI_def
  apply (rule REC_le_rule[where M=M])
  apply (rule WHILEI_mono)
  apply (rule R0)
  apply (erule (1) order_trans[rotated,OF RS])
  unfolding WHILEI_body_def
  apply auto
  done

text {* WHILE-refinement rule with invisible concrete steps.
  Intuitively, a concrete step may either refine an abstract step, or
  must not change the corresponding abstract state. *}
lemma WHILEI_invisible_refine:
  assumes R0: "(s,s')\<in>R"
  assumes SV: "single_valued R"
  assumes RI: "\<And>s s'. \<lbrakk> (s,s')\<in>R; I' s' \<rbrakk> \<Longrightarrow> I s"
  assumes RB: "\<And>s s'. \<lbrakk> (s,s')\<in>R; I' s'; I s; b' s' \<rbrakk> \<Longrightarrow> b s"
  assumes RS: "\<And>s s'. \<lbrakk> (s,s')\<in>R; I' s'; I s; b s \<rbrakk> 
    \<Longrightarrow> f s \<le> sup (\<Down>R (do {ASSUME (b' s'); f' s'})) (\<Down>R (RETURN s'))"
  shows "WHILEI I b f s \<le> \<Down>R (WHILEI I' b' f' s')"
  apply (rule WHILEI_le_rule[where R=R])
  apply (rule R0)
  apply (rule ref_WHILEI_invarI)
  apply (frule (1) RI)
  apply (case_tac "b s=False")
  apply (subst WHILEI_unfold)
  apply (auto dest: RB intro: RETURN_refine_sv[OF SV]) []

  apply simp
  apply (rule order_trans[OF monoD[OF bind_mono1 RS]], assumption+)
  apply (simp only: bind_distrib_sup)
  apply (rule sup_least)
    apply (subst WHILEI_unfold)
    apply (simp add: RB, intro impI)
    apply (rule bind_refine)
    apply (rule order_refl)
    apply simp

    apply (simp add: pw_le_iff refine_pw_simps, blast)
  done

lemma WHILEI_refine[refine]:
  assumes R0: "(x,x')\<in>R"
  assumes SV: "single_valued R"
  assumes IREF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I' x' \<rbrakk> \<Longrightarrow> I x"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I x; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "WHILEI I b f x \<le>\<Down>R (WHILEI I' b' f' x')" 
  apply (rule WHILEI_invisible_refine[OF R0 SV])
  apply (erule (1) IREF)
  apply (simp add: COND_REF)
  apply (rule le_supI1)
  apply (simp add: COND_REF STEP_REF)
  done

lemma WHILE_invisible_refine:
  assumes R0: "(s,s')\<in>R"
  assumes SV: "single_valued R"
  assumes RB: "\<And>s s'. \<lbrakk> (s,s')\<in>R; b' s' \<rbrakk> \<Longrightarrow> b s"
  assumes RS: "\<And>s s'. \<lbrakk> (s,s')\<in>R; b s \<rbrakk> 
    \<Longrightarrow> f s \<le> sup (\<Down>R (do {ASSUME (b' s'); f' s'})) (\<Down>R (RETURN s'))"
  shows "WHILE b f s \<le> \<Down>R (WHILE b' f' s')"
  unfolding WHILE_def
  apply (rule WHILEI_invisible_refine)
  using assms by auto

lemma WHILE_le_rule:
  assumes R0: "(s,s')\<in>R"
  assumes RS: "\<And>W s s'. \<lbrakk>\<And>s s'. (s,s')\<in>R \<Longrightarrow> W s \<le> M s'; (s,s')\<in>R\<rbrakk> \<Longrightarrow> 
    do {if b s then bind (f s) W else RETURN s} \<le> M s'"
  shows "WHILE b f s \<le> M s'"
  unfolding WHILE_def
  apply (rule WHILEI_le_rule[OF R0])
  apply (simp add: RS)
  done

lemma WHILE_refine[refine]:
  assumes R0: "(x,x')\<in>R"
  assumes SV: "single_valued R"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "WHILE b f x \<le>\<Down>R (WHILE b' f' x')"
  unfolding WHILE_def
  apply (rule WHILEI_refine)
  using assms by auto

lemma WHILE_refine'[refine]:
  assumes R0: "(x,x')\<in>R"
  assumes SV: "single_valued R"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "WHILE b f x \<le>\<Down>R (WHILEI I' b' f' x')"
  unfolding WHILE_def
  apply (rule WHILEI_refine)
  using assms by auto

lemma AIF_leI: "\<lbrakk>\<Phi>; \<Phi> \<Longrightarrow> S\<le>S'\<rbrakk> \<Longrightarrow> (if \<Phi> then S else FAIL) \<le> S'"
  by auto
lemma ref_AIFI: "\<lbrakk>\<Phi> \<Longrightarrow> S\<le>\<Down>R S'\<rbrakk> \<Longrightarrow> S \<le> \<Down>R (if \<Phi> then S' else FAIL)"
  by (cases \<Phi>) auto

lemma WHILEIT_refine[refine]:
  assumes R0: "(x,x')\<in>R"
  assumes SV: "single_valued R"
  assumes IREF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I' x' \<rbrakk> \<Longrightarrow> I x"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I x; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "WHILEIT I b f x \<le>\<Down>R (WHILEIT I' b' f' x')" 
  unfolding WHILEIT_def
  apply (rule RECT_refine[OF WHILEI_mono R0])
  unfolding WHILEI_body_def
  apply (rule ref_AIFI)
  apply (rule AIF_leI)
  apply (blast intro: IREF)
  apply (rule if_refine)
  apply (simp add: COND_REF)
  apply (rule bind_refine)
  apply (rule STEP_REF, assumption+) []
  apply assumption

  apply (simp add: RETURN_refine_sv[OF SV])
  done

lemma WHILET_refine[refine]:
  assumes R0: "(x,x')\<in>R"
  assumes SV: "single_valued R"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "WHILET b f x \<le>\<Down>R (WHILET b' f' x')"
  unfolding WHILET_def
  apply (rule WHILEIT_refine)
  using assms by auto

lemma WHILET_refine'[refine]:
  assumes R0: "(x,x')\<in>R"
  assumes SV: "single_valued R"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "WHILET b f x \<le>\<Down>R (WHILEIT I' b' f' x')"
  unfolding WHILET_def
  apply (rule WHILEIT_refine)
  using assms by auto

end
