header {* \isaheader{Generic While-Combinator} *}
theory RefineG_While
imports 
  RefineG_Recursion
  "~~/src/HOL/Library/While_Combinator"
begin

definition
  "WHILEI_body bind return I b f \<equiv> 
  (\<lambda>W s. 
    if I s then 
      if b s then bind (f s) W else return s
    else top)"
definition 
  "iWHILEI bind return I b f s0 \<equiv> REC (WHILEI_body bind return I b f) s0"
definition 
  "iWHILEIT bind return I b f s0 \<equiv> RECT (WHILEI_body bind return I b f) s0"
definition "iWHILE bind return \<equiv> iWHILEI bind return (\<lambda>_. True)"
definition "iWHILET bind return \<equiv> iWHILEIT bind return (\<lambda>_. True)"


locale generic_WHILE =
  fixes bind :: "'m \<Rightarrow> ('a\<Rightarrow>'m) \<Rightarrow> ('m::complete_lattice)"
  fixes return :: "'a \<Rightarrow> 'm"
  fixes WHILEIT WHILEI WHILET WHILE 
  assumes imonad1: "bind (return x) f = f x"
  assumes imonad2: "bind M return = M"
  assumes imonad3: "bind (bind M f) g = bind M (\<lambda>x. bind (f x) g)"
  assumes ibind_mono1: "mono bind"
  assumes ibind_mono2: "mono (bind M)"
  assumes WHILEIT_eq: "WHILEIT \<equiv> iWHILEIT bind return"
  assumes WHILEI_eq: "WHILEI \<equiv> iWHILEI bind return"
  assumes WHILET_eq: "WHILET \<equiv> iWHILET bind return"
  assumes WHILE_eq: "WHILE \<equiv> iWHILE bind return"
begin

  lemmas WHILEIT_def = WHILEIT_eq[unfolded iWHILEIT_def_raw]
  lemmas WHILEI_def = WHILEI_eq[unfolded iWHILEI_def_raw]
  lemmas WHILET_def = WHILET_eq[unfolded iWHILET_def, folded WHILEIT_eq]
  lemmas WHILE_def = WHILE_eq[unfolded iWHILE_def_raw, folded WHILEI_eq]

  lemmas imonad_laws = imonad1 imonad2 imonad3
  
  lemma ibind_mono: "m \<le> m' \<Longrightarrow> f \<le> f' \<Longrightarrow> bind m f \<le> bind m' f'"
    by (metis (no_types) ibind_mono1 ibind_mono2 le_funD monoD order_trans)


lemma WHILEI_mono: "mono (WHILEI_body bind return I b f)"
  apply rule
  unfolding WHILEI_body_def
  apply (rule le_funI)
  apply (clarsimp)
  apply (rule_tac x=x and y=y in monoD)
  apply (auto intro: ibind_mono2)
  done


lemma WHILEI_unfold: "WHILEI I b f x = (
  if (I x) then (if b x then bind (f x) (WHILEI I b f) else return x) else top) "
  unfolding WHILEI_def
  apply (subst REC_unfold[OF WHILEI_mono])
  unfolding WHILEI_body_def
  apply (rule refl)
  done

lemma WHILEI_weaken:
  assumes IW: "\<And>x. I x \<Longrightarrow> I' x"
  shows "WHILEI I' b f x \<le> WHILEI I b f x"
  unfolding WHILEI_def
  apply (rule REC_mono[OF WHILEI_mono])
  apply (auto simp add: WHILEI_body_def dest: IW)
  done

lemma WHILEIT_unfold: "WHILEIT I b f x = (
  if (I x) then 
    (if b x then bind (f x) (WHILEIT I b f) else return x) 
  else top) "
  unfolding WHILEIT_def
  apply (subst RECT_unfold[OF WHILEI_mono])
  unfolding WHILEI_body_def
  apply (rule refl)
  done

lemma WHILEIT_weaken:
  assumes IW: "\<And>x. I x \<Longrightarrow> I' x"
  shows "WHILEIT I' b f x \<le> WHILEIT I b f x"
  unfolding WHILEIT_def
  apply (rule RECT_mono[OF WHILEI_mono])
  apply (auto simp add: WHILEI_body_def dest: IW)
  done

lemma WHILEI_le_WHILEIT: "WHILEI I b f s \<le> WHILEIT I b f s"
  unfolding WHILEI_def WHILEIT_def
  by (rule REC_le_RECT)

subsubsection {* While without Annotated Invariant*}

lemma WHILE_unfold: 
  "WHILE b f s = (if b s then bind (f s) (WHILE b f) else return s)"
  unfolding WHILE_def
  apply (subst WHILEI_unfold)
  apply simp
  done

lemma WHILET_unfold: 
  "WHILET b f s = (if b s then bind (f s) (WHILET b f) else return s)"
  unfolding WHILET_def
  apply (subst WHILEIT_unfold)
  apply simp
  done

lemma transfer_WHILEIT_esc[refine_transfer]:
  assumes REF: "\<And>x. return (f x) \<le> F x"
  shows "return (while b f x) \<le> WHILEIT I b F x"
proof -
  interpret transfer return .
  show ?thesis
    unfolding WHILEIT_def
    apply (rule transfer_RECT'[where fr="while b f"])
    apply (rule while_unfold)
    unfolding WHILEI_body_def
    apply (split split_if, intro allI impI conjI)+
    apply simp_all
    apply (rule order_trans[OF _ monoD[OF ibind_mono1 REF, THEN le_funD]])
    apply (simp add: imonad_laws)
    done
qed

lemma transfer_WHILET_esc[refine_transfer]:
  assumes REF: "\<And>x. return (f x) \<le> F x"
  shows "return (while b f x) \<le> WHILET b F x"
  unfolding WHILET_def
  using assms by (rule transfer_WHILEIT_esc)


lemma WHILE_mono_prover_rule[refine_mono]:
  notes [refine_mono] = ibind_mono
  assumes "\<And>x. f x \<le> f' x"
  shows "WHILE b f s0 \<le> WHILE b f' s0"
  unfolding WHILE_def WHILEI_def WHILEI_body_def
  using assms apply -
  apply refine_mono
  done

lemma WHILEI_mono_prover_rule[refine_mono]:
  notes [refine_mono] = ibind_mono
  assumes "\<And>x. f x \<le> f' x"
  shows "WHILEI I b f s0 \<le> WHILEI I b f' s0"
  unfolding WHILE_def WHILEI_def WHILEI_body_def
  using assms apply -
  apply refine_mono
  done

lemma WHILET_mono_prover_rule[refine_mono]:
  notes [refine_mono] = ibind_mono
  assumes "\<And>x. f x \<le> f' x"
  shows "WHILET b f s0 \<le> WHILET b f' s0"
  unfolding WHILET_def WHILEIT_def WHILEI_body_def
  using assms apply -
  apply refine_mono
  done

lemma WHILEIT_mono_prover_rule[refine_mono]:
  notes [refine_mono] = ibind_mono
  assumes "\<And>x. f x \<le> f' x"
  shows "WHILEIT I b f s0 \<le> WHILEIT I b f' s0"
  unfolding WHILET_def WHILEIT_def WHILEI_body_def
  using assms apply -
  apply refine_mono
  done

end

locale transfer_WHILE = 
  c!: generic_WHILE cbind creturn cWHILEIT cWHILEI cWHILET cWHILE + 
  a!: generic_WHILE abind areturn aWHILEIT aWHILEI aWHILET aWHILE +
  dist_transfer \<alpha>
  for cbind and creturn::"'a \<Rightarrow> 'mc::complete_lattice" 
  and cWHILEIT cWHILEI cWHILET cWHILE
  and abind and areturn::"'a \<Rightarrow> 'ma::complete_lattice"
  and aWHILEIT aWHILEI aWHILET aWHILE
  and \<alpha> :: "'mc \<Rightarrow> 'ma" +
  assumes transfer_bind: "\<lbrakk>\<alpha> m \<le> M; \<And>x. \<alpha> (f x) \<le> F x \<rbrakk> 
    \<Longrightarrow> \<alpha> (cbind m f) \<le> abind M F"
  assumes transfer_return: "\<alpha> (creturn x) \<le> areturn x"
begin

lemma transfer_WHILEIT[refine_transfer]:
  assumes REF: "\<And>x. \<alpha> (f x) \<le> F x"
  shows "\<alpha> (cWHILEIT I b f x) \<le> aWHILEIT I b F x"
  unfolding c.WHILEIT_def a.WHILEIT_def
  apply (rule transfer_RECT[OF _ c.WHILEI_mono])
  unfolding WHILEI_body_def
  apply auto
  apply (rule transfer_bind)
  apply (rule REF)
  apply assumption
  apply (rule transfer_return)
  done

lemma transfer_WHILEI[refine_transfer]:
  assumes REF: "\<And>x. \<alpha> (f x) \<le> F x"
  shows "\<alpha> (cWHILEI I b f x) \<le> aWHILEI I b F x"
  unfolding c.WHILEI_def a.WHILEI_def
  apply (rule transfer_REC[OF _ c.WHILEI_mono])
  unfolding WHILEI_body_def
  apply auto
  apply (rule transfer_bind)
  apply (rule REF)
  apply assumption
  apply (rule transfer_return)
  done

lemma transfer_WHILE[refine_transfer]:
  assumes REF: "\<And>x. \<alpha> (f x) \<le> F x"
  shows "\<alpha> (cWHILE b f x) \<le> aWHILE b F x"
  unfolding c.WHILE_def a.WHILE_def
  using assms by (rule transfer_WHILEI)

lemma transfer_WHILET[refine_transfer]:
  assumes REF: "\<And>x. \<alpha> (f x) \<le> F x"
  shows "\<alpha> (cWHILET b f x) \<le> aWHILET b F x"
  unfolding c.WHILET_def a.WHILET_def
  using assms by (rule transfer_WHILEIT)

end

locale generic_WHILE_rules = 
  generic_WHILE bind return WHILEIT WHILEI WHILET WHILE
  for bind return SPEC WHILEIT WHILEI WHILET WHILE +
  assumes iSPEC_eq: "SPEC \<Phi> = Sup {return x  | x. \<Phi> x}"
  assumes ibind_rule: "\<lbrakk> M \<le> SPEC (\<lambda>x. f x \<le> SPEC \<Phi>) \<rbrakk> \<Longrightarrow> bind M f \<le> SPEC \<Phi>"
begin

  lemma ireturn_eq: "return x = SPEC (op = x)"
    unfolding iSPEC_eq by auto

  lemma iSPEC_rule: "(\<And>x. \<Phi> x \<Longrightarrow> \<Psi> x) \<Longrightarrow> SPEC \<Phi> \<le> SPEC \<Psi>"
    unfolding iSPEC_eq
    by (auto intro: Sup_mono)

  lemma ireturn_rule: "\<Phi> x \<Longrightarrow> return x \<le> SPEC \<Phi>"
    unfolding ireturn_eq
    by (auto intro: iSPEC_rule)

lemma WHILEI_rule:
  assumes I0: "I s"
  assumes ISTEP: "\<And>s. \<lbrakk>I s; b s\<rbrakk> \<Longrightarrow> f s \<le> SPEC I"
  assumes CONS: "\<And>s. \<lbrakk> I s; \<not> b s \<rbrakk> \<Longrightarrow> \<Phi> s"
  shows "WHILEI I b f s \<le> SPEC \<Phi>"
  apply (rule order_trans[where y="SPEC (\<lambda>s. I s \<and> \<not> b s)"])
    apply (unfold WHILEI_def)
    apply (rule REC_rule[OF WHILEI_mono])
      apply (rule I0)
    
      unfolding WHILEI_body_def
      apply (split split_if)+
      apply (intro impI conjI)
      apply simp_all
      apply (rule ibind_rule)
        apply (erule (1) order_trans[OF ISTEP])
        apply (rule iSPEC_rule, assumption)
      
        apply (rule ireturn_rule)
        apply simp

    apply (rule iSPEC_rule)
    apply (simp add: CONS)
  done

lemma WHILEIT_rule:
  assumes WF: "wf R"
  assumes I0: "I s"
  assumes IS: "\<And>s. \<lbrakk> I s; b s \<rbrakk> \<Longrightarrow> f s \<le> SPEC (\<lambda>s'. I s' \<and> (s',s)\<in>R)"
  assumes PHI: "\<And>s. \<lbrakk> I s; \<not> b s \<rbrakk> \<Longrightarrow> \<Phi> s"
  shows "WHILEIT I b f s \<le> SPEC \<Phi>"

  unfolding WHILEIT_def
  apply (rule RECT_rule[OF WHILEI_mono WF, where \<Phi>=I,OF I0])
  unfolding WHILEI_body_def
  apply (split split_if)+
  apply (intro impI conjI)
  apply simp_all

  apply (rule ibind_rule)
  apply (rule order_trans[OF IS], assumption+)
  apply (rule iSPEC_rule)
  apply simp

  apply (rule ireturn_rule)
  apply (simp add: PHI)
  done
  
lemma WHILE_rule:
  assumes I0: "I s"
  assumes ISTEP: "\<And>s. \<lbrakk>I s; b s\<rbrakk> \<Longrightarrow> f s \<le> SPEC I"
  assumes CONS: "\<And>s. \<lbrakk> I s; \<not> b s \<rbrakk> \<Longrightarrow> \<Phi> s"
  shows "WHILE b f s \<le> SPEC \<Phi>"
  unfolding WHILE_def
  apply (rule order_trans[OF WHILEI_weaken WHILEI_rule])
  apply (rule TrueI)
  apply (rule I0)
  using assms by auto


lemma WHILET_rule:
  assumes WF: "wf R"
  assumes I0: "I s"
  assumes IS: "\<And>s. \<lbrakk> I s; b s \<rbrakk> \<Longrightarrow> f s \<le> SPEC (\<lambda>s'. I s' \<and> (s',s)\<in>R)"
  assumes PHI: "\<And>s. \<lbrakk> I s; \<not> b s \<rbrakk> \<Longrightarrow> \<Phi> s"
  shows "WHILET b f s \<le> SPEC \<Phi>"
  unfolding WHILET_def
  apply (rule order_trans[OF WHILEIT_weaken WHILEIT_rule])
  apply (rule TrueI)
  apply (rule WF)
  apply (rule I0)
  using assms by auto

end

end
