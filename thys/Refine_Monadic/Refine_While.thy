section {* While-Loops *}
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

lemma ref_WHILEIT_invarI:
  assumes "I s \<Longrightarrow> M \<le> \<Down>R (WHILEIT I b f s)"
  shows "M \<le> \<Down>R (WHILEIT I b f s)"
  apply (subst WHILEIT_unfold)
  apply (cases "I s")
  apply (subst WHILEIT_unfold[symmetric])
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
lemma WHILEI_invisible_refine_genR:
  assumes R0: "I' s' \<Longrightarrow> (s,s')\<in>R'"
  assumes SV: "single_valued R"
  assumes RI: "\<And>s s'. \<lbrakk> (s,s')\<in>R'; I' s' \<rbrakk> \<Longrightarrow> I s"
  assumes RB: "\<And>s s'. \<lbrakk> (s,s')\<in>R'; I' s'; I s; b' s' \<rbrakk> \<Longrightarrow> b s"
  assumes RS: "\<And>s s'. \<lbrakk> (s,s')\<in>R'; I' s'; I s; b s \<rbrakk> 
    \<Longrightarrow> f s \<le> sup (\<Down>R' (do {ASSUME (b' s'); f' s'})) (\<Down>R' (RETURN s'))"
  assumes R_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; \<not>b x; \<not>b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> (x,x')\<in>R"
  shows "WHILEI I b f s \<le> \<Down>R (WHILEI I' b' f' s')"
  apply (rule ref_WHILEI_invarI)
  apply (rule WHILEI_le_rule[where R=R'])
  apply (erule R0)
  apply (rule ref_WHILEI_invarI)
  apply (frule (1) RI)
  apply (case_tac "b s=False")
  apply (subst WHILEI_unfold)
  apply (auto dest: RB intro: RETURN_refine_sv[OF SV] R_REF) []

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


lemma WHILEI_refine_genR:
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R'"
  assumes SV: "single_valued R"
  assumes IREF: "\<And>x x'. \<lbrakk> (x,x')\<in>R'; I' x' \<rbrakk> \<Longrightarrow> I x"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R'; I x; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R' (f' x')"
  assumes R_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; \<not>b x; \<not>b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> (x,x')\<in>R"
  shows "WHILEI I b f x \<le>\<Down>R (WHILEI I' b' f' x')" 
  apply (rule WHILEI_invisible_refine_genR[OF R0 SV])
  apply assumption
  apply (erule (1) IREF)
  apply (simp add: COND_REF)
  apply (rule le_supI1)
  apply (simp add: COND_REF STEP_REF)
  apply (rule R_REF, assumption+)
  done

lemma WHILE_invisible_refine_genR:
  assumes R0: "(s,s')\<in>R'"
  assumes SV: "single_valued R"
  assumes RB: "\<And>s s'. \<lbrakk> (s,s')\<in>R'; b' s' \<rbrakk> \<Longrightarrow> b s"
  assumes RS: "\<And>s s'. \<lbrakk> (s,s')\<in>R'; b s \<rbrakk> 
    \<Longrightarrow> f s \<le> sup (\<Down>R' (do {ASSUME (b' s'); f' s'})) (\<Down>R' (RETURN s'))"
  assumes R_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; \<not>b x; \<not>b' x' \<rbrakk> \<Longrightarrow> (x,x')\<in>R"
  shows "WHILE b f s \<le> \<Down>R (WHILE b' f' s')"
  unfolding WHILE_def
  apply (rule WHILEI_invisible_refine_genR)
  apply (rule assms, (assumption+)?)+
  done

lemma WHILE_refine_genR:
  assumes R0: "(x,x')\<in>R'"
  assumes SV: "single_valued R"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; b x; b' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R' (f' x')"
  assumes R_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; \<not>b x; \<not>b' x' \<rbrakk> \<Longrightarrow> (x,x')\<in>R"
  shows "WHILE b f x \<le>\<Down>R (WHILE b' f' x')"
  unfolding WHILE_def
  apply (rule WHILEI_refine_genR)
  apply (rule assms, (assumption+)?)+
  done

lemma WHILE_refine_genR':
  assumes R0: "(x,x')\<in>R'"
  assumes SV: "single_valued R"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R'; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; b x; b' x'; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R' (f' x')"
  assumes R_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; \<not>b x; \<not>b' x' \<rbrakk> \<Longrightarrow> (x,x')\<in>R"
  shows "WHILE b f x \<le>\<Down>R (WHILEI I' b' f' x')"
  unfolding WHILE_def
  apply (rule WHILEI_refine_genR)
  apply (rule assms TrueI, (assumption+)?)+
  done

text {* WHILE-refinement rule with invisible concrete steps.
  Intuitively, a concrete step may either refine an abstract step, or
  must not change the corresponding abstract state. *}
lemma WHILEI_invisible_refine:
  assumes R0: "I' s' \<Longrightarrow> (s,s')\<in>R"
  assumes SV: "single_valued R"
  assumes RI: "\<And>s s'. \<lbrakk> (s,s')\<in>R; I' s' \<rbrakk> \<Longrightarrow> I s"
  assumes RB: "\<And>s s'. \<lbrakk> (s,s')\<in>R; I' s'; I s; b' s' \<rbrakk> \<Longrightarrow> b s"
  assumes RS: "\<And>s s'. \<lbrakk> (s,s')\<in>R; I' s'; I s; b s \<rbrakk> 
    \<Longrightarrow> f s \<le> sup (\<Down>R (do {ASSUME (b' s'); f' s'})) (\<Down>R (RETURN s'))"
  shows "WHILEI I b f s \<le> \<Down>R (WHILEI I' b' f' s')"
  apply (rule WHILEI_invisible_refine_genR[where R'=R])
  apply (rule assms, (assumption+)?)+
  done

lemma WHILEI_refine[refine]:
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R"
  assumes SV: "single_valued R"
  assumes IREF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I' x' \<rbrakk> \<Longrightarrow> I x"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I x; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "WHILEI I b f x \<le>\<Down>R (WHILEI I' b' f' x')" 
  apply (rule WHILEI_invisible_refine[OF R0 SV])
  apply assumption
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
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R"
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

text {* Refinement with generalized refinement relation. Required to exploit
  the fact that the condition does not hold at the end of the loop. *}
lemma WHILEIT_refine_genR:
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R'"
  assumes SV: "single_valued R"
  assumes IREF: "\<And>x x'. \<lbrakk> (x,x')\<in>R'; I' x' \<rbrakk> \<Longrightarrow> I x"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R'; I x; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R' (f' x')"
  assumes R_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; \<not>b x; \<not>b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> (x,x')\<in>R"
  shows "WHILEIT I b f x \<le>\<Down>R (WHILEIT I' b' f' x')" 
  apply (rule ref_WHILEIT_invarI)
  unfolding WHILEIT_def
  apply (rule RECT_refine[OF WHILEI_mono R0])
  apply assumption
  unfolding WHILEI_body_def
  apply (rule ref_AIFI)
  apply (rule AIF_leI)
  apply (blast intro: IREF)
  apply (rule if_refine)
  apply (simp add: COND_REF)
  apply (rule bind_refine)
  apply (rule STEP_REF, assumption+) []
  apply assumption

  apply (rule RETURN_refine_sv)
  apply (rule SV)
  apply (simp add: R_REF)
  done


lemma WHILET_refine_genR:
  assumes R0: "(x,x')\<in>R'"
  assumes SV: "single_valued R"
  assumes COND_REF: "\<And>x x'. (x,x')\<in>R' \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; b x; b' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R' (f' x')"
  assumes R_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; \<not>b x; \<not>b' x' \<rbrakk> \<Longrightarrow> (x,x')\<in>R"
  shows "WHILET b f x \<le>\<Down>R (WHILET b' f' x')"
  unfolding WHILET_def
  apply (rule WHILEIT_refine_genR[OF R0 SV])
  apply (rule TrueI)
  apply (rule assms, assumption+)+
  done

lemma WHILET_refine_genR':
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R'"
  assumes SV: "single_valued R"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R'; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; b x; b' x'; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R' (f' x')"
  assumes R_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; \<not>b x; \<not>b' x'; I' x' \<rbrakk> \<Longrightarrow> (x,x')\<in>R"
  shows "WHILET b f x \<le>\<Down>R (WHILEIT I' b' f' x')"
  unfolding WHILET_def
  apply (rule WHILEIT_refine_genR[OF R0 SV])
  apply assumption
  apply (rule TrueI)
  apply (rule assms, assumption+)+
  done

lemma WHILEIT_refine[refine]:
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R"
  assumes SV: "single_valued R"
  assumes IREF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I' x' \<rbrakk> \<Longrightarrow> I x"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I x; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "WHILEIT I b f x \<le>\<Down>R (WHILEIT I' b' f' x')" 
  using WHILEIT_refine_genR[where R=R and R'=R, OF assms] .

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
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R"
  assumes SV: "single_valued R"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "WHILET b f x \<le>\<Down>R (WHILEIT I' b' f' x')"
  unfolding WHILET_def
  apply (rule WHILEIT_refine)
  using assms by auto


lemma WHILEI_refine_new_invar:
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R"
  assumes SV: "single_valued R"
  assumes INV0: "\<lbrakk> I' x'; (x,x')\<in>R \<rbrakk> \<Longrightarrow> I x"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I x; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  assumes STEP_INV: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I x; I' x'; nofail (f x) \<rbrakk> \<Longrightarrow> f x \<le> SPEC I"
  shows "WHILEI I b f x \<le>\<Down>R (WHILEI I' b' f' x')"
  apply (rule WHILEI_refine_genR[where 
    I=I and I'=I' and x'=x' and x=x and R=R and b=b and b'=b' and f'=f' and f=f
    and R'="{ (c,a). (c,a)\<in>R \<and> I c }"
    ])
  using assms
  by (auto intro: sv_add_invar_refineI)

lemma WHILEIT_refine_new_invar:
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R"
  assumes SV: "single_valued R"
  assumes INV0: "\<lbrakk> I' x'; (x,x')\<in>R \<rbrakk> \<Longrightarrow> I x"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I x; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  assumes STEP_INV: 
    "\<And>x x'. \<lbrakk> nofail (f x); (x,x')\<in>R; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le> SPEC I"
  shows "WHILEIT I b f x \<le>\<Down>R (WHILEIT I' b' f' x')"
  apply (rule WHILEIT_refine_genR[where 
    I=I and I'=I' and x'=x' and x=x and R=R and b=b and b'=b' and f'=f' and f=f
    and R'="{ (c,a). (c,a)\<in>R \<and> I c }"
    ])
  using assms
  by (auto intro: sv_add_invar_refineI)






subsection {* Autoref Setup *}

(*lemma id_WHILE[autoref_id_self]: "ID_LIST 
  (l (WHILET,3) (WHILEIT I,3) (WHILE,3) (WHILEI I,3))"
  by simp_all*)

context begin interpretation autoref_syn .

lemma [autoref_op_pat]:
  "WHILEIT I \<equiv> OP (WHILEIT I)"
  "WHILEI I \<equiv> OP (WHILEI I)"
  by auto

lemma autoref_WHILET[autoref_rules]:
  assumes "PREFER single_valued R"
  assumes "\<And>x x'. \<lbrakk> (x,x')\<in>R\<rbrakk> \<Longrightarrow> (c x,c'$x') \<in> Id"
  assumes "\<And>x x'. \<lbrakk> REMOVE_INTERNAL c' x'; (x,x')\<in>R\<rbrakk> 
    \<Longrightarrow> (f x,f'$x') \<in> \<langle>R\<rangle>nres_rel"
  assumes "(s,s')\<in>R"
  shows "(WHILET c f s,
    (OP WHILET:::(R\<rightarrow>Id)\<rightarrow>(R\<rightarrow>\<langle>R\<rangle>nres_rel)\<rightarrow>R\<rightarrow>\<langle>R\<rangle>nres_rel)$c'$f'$s')
   \<in> \<langle>R\<rangle>nres_rel"
  using assms
  by (auto simp add: nres_rel_def fun_rel_def intro!: WHILET_refine)

lemma autoref_WHILEIT[autoref_rules]:
  assumes "PREFER single_valued R"
  assumes "\<And>x x'. \<lbrakk>I x'; (x,x')\<in>R\<rbrakk> \<Longrightarrow> (c x,c'$x') \<in> Id"
  assumes "\<And>x x'. \<lbrakk>I x'; (x,x')\<in>R\<rbrakk> \<Longrightarrow> (f x,f'$x') \<in> \<langle>R\<rangle>nres_rel"
  assumes "I s' \<Longrightarrow> (s,s')\<in>R"
  shows "(WHILET c f s,
    (OP (WHILEIT I):::(R\<rightarrow>Id)\<rightarrow>(R\<rightarrow>\<langle>R\<rangle>nres_rel)\<rightarrow>R\<rightarrow>\<langle>R\<rangle>nres_rel)$c'$f'$s')
   \<in> \<langle>R\<rangle>nres_rel"
  using assms
  by (auto simp add: nres_rel_def fun_rel_def intro!: WHILET_refine')

lemma autoref_WHILE[autoref_rules]:
  assumes "PREFER single_valued R"
  assumes "\<And>x x'. \<lbrakk> (x,x')\<in>R\<rbrakk> \<Longrightarrow> (c x,c'$x') \<in> Id"
  assumes "\<And>x x'. \<lbrakk> REMOVE_INTERNAL c' x'; (x,x')\<in>R\<rbrakk> 
    \<Longrightarrow> (f x,f'$x') \<in> \<langle>R\<rangle>nres_rel"
  assumes "(s,s')\<in>R"
  shows "(WHILE c f s,
      (OP WHILE ::: (R\<rightarrow>Id) \<rightarrow> (R\<rightarrow>\<langle>R\<rangle>nres_rel) \<rightarrow> R \<rightarrow> \<langle>R\<rangle>nres_rel)$c'$f'$s'
    )\<in>\<langle>R\<rangle>nres_rel"
  using assms
  by (auto simp add: nres_rel_def fun_rel_def intro!: WHILE_refine)

lemma autoref_WHILEI[autoref_rules]:
  assumes "PREFER single_valued R"
  assumes "\<And>x x'. \<lbrakk>I x'; (x,x')\<in>R\<rbrakk> \<Longrightarrow> (c x,c'$x') \<in> Id"
  assumes "\<And>x x'. \<lbrakk>I x'; (x,x')\<in>R\<rbrakk> \<Longrightarrow>(f x,f'$x') \<in> \<langle>R\<rangle>nres_rel"
  assumes "I s' \<Longrightarrow> (s,s')\<in>R"
  shows "(WHILE c f s,
      (OP (WHILEI I) ::: (R\<rightarrow>Id) \<rightarrow> (R\<rightarrow>\<langle>R\<rangle>nres_rel) \<rightarrow> R \<rightarrow> \<langle>R\<rangle>nres_rel)$c'$f'$s'
    )\<in>\<langle>R\<rangle>nres_rel"
  using assms
  by (auto simp add: nres_rel_def fun_rel_def intro!: WHILE_refine')
end

subsection {* Convenience *}

subsubsection {* Iterate over range of list *}
lemma range_set_WHILE:
  assumes CEQ: "\<And>i s. c (i,s) \<longleftrightarrow> i<u"
  assumes F0: "F {} s0 = s0"
  assumes Fs: "\<And>s i X. \<lbrakk>l\<le>i; i<u\<rbrakk> 
    \<Longrightarrow> f (i, (F X s)) \<le> SPEC (\<lambda>(i',r). i'=i+1 \<and> r=F (insert (list!i) X) s)"
  shows "WHILET c f (l,s0) 
    \<le> SPEC (\<lambda>(_,r). r=F {list!i | i. l\<le>i \<and> i<u} s0)"
  apply (cases "\<not>(l<u)")
  apply (subst WHILET_unfold)
  using F0 apply (simp add: CEQ)
  apply (rule subst, assumption)
  apply ((fo_rule cong refl)+, auto) []

  apply (simp)
  apply (rule WHILET_rule[
    where R = "measure (\<lambda>(i,_). u-i)"
    and I = "\<lambda>(i,s). l\<le>i \<and> i\<le>u \<and> s = F {list!j | j. l\<le>j \<and> j<i} s0"
    ])
  apply rule

  apply simp
  apply (subst F0[symmetric])
  apply ((fo_rule cong refl)+, auto) []

  apply (clarsimp simp: CEQ)
  apply (rule order_trans[OF Fs], simp_all) []
  apply (auto
    intro!: fun_cong[OF arg_cong[of _ _ F]]
    elim: less_SucE) []

  apply (auto simp: CEQ) []
  done


end
