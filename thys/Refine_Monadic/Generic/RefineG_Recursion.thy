header {* \isaheader{Generic Recursion Combinator for Complete Lattice Structured Domains} *}
theory RefineG_Recursion
imports "../Refine_Misc" RefineG_Transfer
begin

text {*
  We define a recursion combinator that asserts monotonicity.
*}

(* TODO: Once complete_lattice and ccpo typeclass are unified,
  we should also define a REC-combinator for ccpos! *)

definition REC where "REC B x \<equiv> if (mono B) then (lfp B x) else top"
definition RECT ("REC\<^sub>T") where "RECT B x \<equiv> if (mono B) then (gfp B x) else top"

lemma REC_unfold: "mono B \<Longrightarrow> REC B x = B (REC B) x"
  unfolding REC_def [abs_def]
  by (simp add: lfp_unfold[symmetric])

lemma RECT_unfold: "mono B \<Longrightarrow> RECT B x = B (RECT B) x"
  unfolding RECT_def [abs_def]
  by (simp add: gfp_unfold[symmetric])

lemma REC_mono[refine_mono]:
  assumes [simp]: "mono B"
  assumes LE: "\<And>F x. B F x \<le> B' F x"
  shows "REC B x \<le> REC B' x"
  unfolding REC_def
  apply clarsimp
  apply (rule lfp_mono[THEN le_funD])
  apply (rule le_funI[OF LE])
  done

lemma RECT_mono[refine_mono]:
  assumes [simp]: "mono B"
  assumes LE: "\<And>F x. B F x \<le> B' F x"
  shows "RECT B x \<le> RECT B' x"
  unfolding RECT_def
  apply clarsimp
  apply (rule gfp_mono[THEN le_funD])
  apply (rule le_funI[OF LE])
  done


lemma REC_le_RECT: "REC body x \<le> RECT body x"
  unfolding REC_def RECT_def
  apply clarsimp
  apply (erule lfp_le_gfp')
  done

text {* The following lemma shows that greatest and least fixed point are equal,
  if we can provide a variant. *}
lemma RECT_eq_REC:
  assumes WF: "wf V"
  assumes I0: "I x"
  assumes IS: "\<And>f x. I x \<Longrightarrow> 
    body (\<lambda>x'. if (I x' \<and> (x',x)\<in>V) then f x' else top) x \<le> body f x"
  shows "RECT body x = REC body x"
proof (cases "mono body")
  assume "\<not>mono body"
  thus ?thesis unfolding REC_def RECT_def by simp
next
  assume MONO: "mono body"

  from lfp_le_gfp' MONO have "lfp body x \<le> gfp body x" .
  moreover have "I x \<longrightarrow> gfp body x \<le> lfp body x"
    using WF
    apply (induct rule: wf_induct[consumes 1])
    apply (rule impI)
    apply (subst lfp_unfold[OF MONO])
    apply (subst gfp_unfold[OF MONO])
    apply (rule order_trans[OF _ IS])
    apply (rule monoD[OF MONO,THEN le_funD])
    apply (rule le_funI)
    apply simp
    apply simp
    done
  ultimately show ?thesis
    unfolding REC_def RECT_def
    apply (rule_tac antisym)
    using I0 MONO by auto
qed

text {*
  The following lemma is a stronger version of @{thm [source] "RECT_eq_REC"},
  which allows to keep track of a function specification, that can be used to
  argue about nested recursive calls.
*}
lemma RECT_eq_REC':
  assumes MONO: "mono body"
  assumes WF: "wf R"
  assumes I0: "I x"
  assumes IS: "\<And>f x. \<lbrakk>I x; 
    \<And>x'. \<lbrakk> I x'; (x',x)\<in>R \<rbrakk> \<Longrightarrow> f x' \<le> M x'
  \<rbrakk> \<Longrightarrow> 
    body (\<lambda>x'. if (I x' \<and> (x',x)\<in>R) then f x' else top) x \<le> body f x \<and>
    body f x \<le> M x"
  shows "RECT body x = REC body x \<and> RECT body x \<le> M x"
proof -
  (*assume MONO: "mono body"'*)

  from lfp_le_gfp' MONO have "lfp body x \<le> gfp body x" .
  moreover have "I x \<longrightarrow> gfp body x \<le> lfp body x \<and> lfp body x \<le> M x"
    using WF
    apply (induct rule: wf_induct[consumes 1])
    apply (rule impI)
    apply (rule conjI)
    apply (subst lfp_unfold[OF MONO])
    apply (subst gfp_unfold[OF MONO])
    apply (rule order_trans[OF _ conjunct1[OF IS]])
    apply (rule monoD[OF MONO,THEN le_funD])
    apply (rule le_funI)
    apply simp
    apply simp
    apply simp

    apply (subst lfp_unfold[OF MONO])
    apply (rule conjunct2[OF IS])
    apply simp
    apply simp
    done
  ultimately show ?thesis
    unfolding REC_def RECT_def
    using I0 MONO by auto
qed


lemma REC_rule:
  fixes x::"'x"
  assumes M: "mono body"
  assumes I0: "\<Phi> x"
  assumes IS: "\<And>f x. \<lbrakk> \<And>x. \<Phi> x \<Longrightarrow> f x \<le> M x; \<Phi> x \<rbrakk> 
    \<Longrightarrow> body f x \<le> M x"
  shows "REC body x \<le> M x"
proof -
  have "\<forall>x. \<Phi> x \<longrightarrow> lfp body x \<le> M x"
    apply (rule lfp_cadm_induct[OF _ M])
      apply rule
      apply rule
      apply rule
      unfolding Sup_fun_def
      apply (rule SUP_least)
      apply simp

      apply (rule)
      apply (rule)
      apply (rule IS)
      apply blast
      apply assumption
    done
  thus ?thesis
    unfolding REC_def
    by (auto simp: I0 M)
qed

lemma RECT_rule:
  assumes M: "mono body"
  assumes WF: "wf (V::('x\<times>'x) set)"
  assumes I0: "\<Phi> (x::'x)"
  assumes IS: "\<And>f x. \<lbrakk> \<And>x'. \<lbrakk>\<Phi> x'; (x',x)\<in>V\<rbrakk> \<Longrightarrow> f x' \<le> M x'; \<Phi> x \<rbrakk> 
    \<Longrightarrow> body f x \<le> M x"
  shows "RECT body x \<le> M x"
proof -
  have "\<Phi> x \<longrightarrow> gfp body x \<le> M x"
    using WF
    apply (induct x rule: wf_induct[consumes 1])
    apply (rule impI)
    apply (subst gfp_unfold[OF M])
    apply (rule IS)
    apply simp
    apply simp
    done
  with I0 M show ?thesis unfolding RECT_def by auto
qed

subsection {* Transfer *}

lemma (in transfer) transfer_RECT'[refine_transfer]:
  assumes REC_EQ: "\<And>x. fr x = b fr x"
  assumes REF: "\<And>F f x. \<lbrakk>\<And>x. \<alpha> (f x) \<le> F x \<rbrakk> \<Longrightarrow> \<alpha> (b f x) \<le> B F x"
  shows "\<alpha> (fr x) \<le> RECT B x"
  unfolding RECT_def
proof clarsimp
  assume MONO: "mono B"
  show "\<alpha> (fr x) \<le> gfp B x"
    apply (rule_tac x=x in spec)
    apply (rule gfp_cadm_induct[where f=B])
    apply rule
    apply (intro allI)

    apply (unfold Inf_fun_def INF_def)
    apply (drule chain_dualI)
    apply (drule_tac x=x in point_chainI)
  
    apply (case_tac "A={}")
    apply simp
    apply (rule Inf_greatest)
    apply (auto intro: le_funI) []

    apply fact
  
    using REF REC_EQ by force
qed

lemma (in ordered_transfer) transfer_RECT[refine_transfer]:
  assumes REF: "\<And>F f x. \<lbrakk>\<And>x. \<alpha> (f x) \<le> F x \<rbrakk> \<Longrightarrow> \<alpha> (b f x) \<le> B F x"
  assumes "mono b"
  shows "\<alpha> (RECT b x) \<le> RECT B x"
  apply (rule transfer_RECT')
  apply (rule RECT_unfold[OF `mono b`])
  by fact

lemma (in dist_transfer) transfer_REC[refine_transfer]:
  assumes REF: "\<And>F f x. \<lbrakk>\<And>x. \<alpha> (f x) \<le> F x \<rbrakk> \<Longrightarrow> \<alpha> (b f x) \<le> B F x"
  assumes "mono b"
  shows "\<alpha> (REC b x) \<le> REC B x"
  unfolding REC_def
proof (clarsimp simp add: `mono b`)
  assume "mono B"
  show "\<alpha> (lfp b x) \<le> lfp B x"
    apply (rule_tac x=x in spec)
    apply (rule lfp_cadm_induct[OF _ `mono b`])

    apply rule
    apply clarsimp

    apply (unfold Sup_fun_def SUP_def)
    apply (drule_tac x=x in point_chainI)
    apply (simp add: \<alpha>_dist)
    apply (rule Sup_least)
    apply auto []

    apply clarsimp
    apply (subst lfp_unfold[OF `mono B`])
    apply (rule REF)
    apply simp
    done
qed

end
