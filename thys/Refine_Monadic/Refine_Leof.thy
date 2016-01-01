section {* Less-Equal or Fail *}
(* TODO: Move to Refinement Framework *)
theory Refine_Leof
imports Refine_Basic
begin
  text {* A predicate that states refinement or that the LHS fails. *}


  definition le_or_fail :: "'a nres \<Rightarrow> 'a nres \<Rightarrow> bool" (infix "\<le>\<^sub>n" 50) where
    "m \<le>\<^sub>n m' \<equiv> nofail m \<longrightarrow> m \<le> m'"

  lemma leofI[intro?]: 
    assumes "nofail m \<Longrightarrow> m \<le> m'" shows "m \<le>\<^sub>n m'" 
    using assms unfolding le_or_fail_def by auto
  
  lemma leofD:  
    assumes "nofail m"
    assumes "m \<le>\<^sub>n m'"
    shows "m \<le> m'"
    using assms unfolding le_or_fail_def by blast

  lemma pw_leof_iff:
    "m \<le>\<^sub>n m' \<longleftrightarrow> (nofail m \<longrightarrow> (\<forall>x. inres m x \<longrightarrow> inres m' x))"
    unfolding le_or_fail_def by (auto simp add: pw_le_iff refine_pw_simps)
  
  lemma (in -) inres_leof_mono: "m\<le>\<^sub>nm' \<Longrightarrow> nofail m \<Longrightarrow> inres m x \<Longrightarrow> inres m' x"
    by (auto simp: pw_leof_iff)

  lemma leof_trans[trans]: "\<lbrakk>a \<le>\<^sub>n RES X; RES X \<le>\<^sub>n c\<rbrakk> \<Longrightarrow> a \<le>\<^sub>n c"
    by (auto simp: pw_leof_iff)

  lemma leof_trans_nofail: "\<lbrakk> a\<le>\<^sub>nb; nofail b; b\<le>\<^sub>nc \<rbrakk> \<Longrightarrow> a \<le>\<^sub>n c"  
    by (auto simp: pw_leof_iff)

  lemma leof_refl[simp]: "a \<le>\<^sub>n a" 
    by (auto simp: pw_leof_iff)

  lemma leof_RES_UNIV[simp, intro!]: "m \<le>\<^sub>n RES UNIV" 
    by (auto simp: pw_leof_iff)

  lemma leof_lift:
    "m \<le> F \<Longrightarrow> m \<le>\<^sub>n F"
    by (auto simp add: pw_leof_iff pw_le_iff)

  lemma leof_RETURN_rule[refine_vcg]: 
    "\<Phi> m \<Longrightarrow> RETURN m \<le>\<^sub>n SPEC \<Phi>" by (simp add: pw_leof_iff)
  
  lemma leof_bind_rule[refine_vcg]: 
    "\<lbrakk> m \<le>\<^sub>n SPEC (\<lambda>x. f x \<le>\<^sub>n SPEC \<Phi>) \<rbrakk> \<Longrightarrow> m\<bind>f \<le>\<^sub>n SPEC \<Phi>" 
    by (auto simp add: pw_leof_iff refine_pw_simps)
  
  lemma RETURN_leof_RES_iff[simp]: "RETURN x \<le>\<^sub>n RES Y \<longleftrightarrow> x\<in>Y"
    by (auto simp add: pw_leof_iff refine_pw_simps)

  lemma RES_leof_RES_iff[simp]: "RES X \<le>\<^sub>n RES Y \<longleftrightarrow> X \<subseteq> Y"
    by (auto simp add: pw_leof_iff refine_pw_simps)
   
  lemma leof_Let_rule[refine_vcg]: "f x \<le>\<^sub>n SPEC \<Phi> \<Longrightarrow> Let x f \<le>\<^sub>n SPEC \<Phi>" 
    by simp

  lemma leof_If_rule[refine_vcg]: 
    "\<lbrakk>c \<Longrightarrow> t \<le>\<^sub>n SPEC \<Phi>; \<not>c \<Longrightarrow> e \<le>\<^sub>n SPEC \<Phi>\<rbrakk> \<Longrightarrow> If c t e \<le>\<^sub>n SPEC \<Phi>" 
    by simp

  lemma leof_RES_rule[refine_vcg]:
    "\<lbrakk>\<And>x. \<Psi> x \<Longrightarrow> \<Phi> x\<rbrakk> \<Longrightarrow> SPEC \<Psi> \<le>\<^sub>n SPEC \<Phi>"
    "\<lbrakk>\<And>x. x\<in>X \<Longrightarrow> \<Phi> x\<rbrakk> \<Longrightarrow> RES X \<le>\<^sub>n SPEC \<Phi>"
    by auto

  lemma leof_True_rule: "\<lbrakk>\<And>x. \<Phi> x\<rbrakk> \<Longrightarrow> m \<le>\<^sub>n SPEC \<Phi>"
    by (auto simp add: pw_leof_iff refine_pw_simps)

  lemma leof_option_rule[refine_vcg]: 
  "\<lbrakk>v = None \<Longrightarrow> S1 \<le>\<^sub>n SPEC \<Phi>; \<And>x. v = Some x \<Longrightarrow> f2 x \<le>\<^sub>n SPEC \<Phi>\<rbrakk>
    \<Longrightarrow> (case v of None \<Rightarrow> S1 | Some x \<Rightarrow> f2 x) \<le>\<^sub>n SPEC \<Phi>"
    by (cases v) auto

  lemma ASSERT_leof_rule[refine_vcg]:
    assumes "\<Phi> \<Longrightarrow> m \<le>\<^sub>n m'"
    shows "do {ASSERT \<Phi>; m} \<le>\<^sub>n m'"
    using assms
    by (cases \<Phi>, auto simp: pw_leof_iff)

  lemma SPEC_rule_conj_leofI1:
    assumes "m \<le> SPEC \<Phi>"
    assumes "m \<le>\<^sub>n SPEC \<Psi>"
    shows "m \<le> SPEC (\<lambda>s. \<Phi> s \<and> \<Psi> s)"
    using assms by (auto simp: pw_le_iff pw_leof_iff)

  lemma SPEC_rule_conj_leofI2:
    assumes "m \<le>\<^sub>n SPEC \<Phi>"
    assumes "m \<le> SPEC \<Psi>"
    shows "m \<le> SPEC (\<lambda>s. \<Phi> s \<and> \<Psi> s)"
    using assms by (auto simp: pw_le_iff pw_leof_iff)

  lemma SPEC_rule_leof_conjI: 
    assumes "m \<le>\<^sub>n SPEC \<Phi>" "m \<le>\<^sub>n SPEC \<Psi>"
    shows "m \<le>\<^sub>n SPEC (\<lambda>x. \<Phi> x \<and> \<Psi> x)"
    using assms by (auto simp: pw_leof_iff)

  lemma leof_use_spec_rule:
    assumes "m \<le>\<^sub>n SPEC \<Psi>"
    assumes "m \<le>\<^sub>n SPEC (\<lambda>s. \<Psi> s \<longrightarrow> \<Phi> s)"
    shows "m \<le>\<^sub>n SPEC \<Phi>"
    using assms by (auto simp: pw_leof_iff refine_pw_simps)
  
  lemma use_spec_leof_rule:
    assumes "m \<le>\<^sub>n SPEC \<Psi>"
    assumes "m \<le> SPEC (\<lambda>s. \<Psi> s \<longrightarrow> \<Phi> s)"
    shows "m \<le> SPEC \<Phi>"
    using assms by (auto simp: pw_leof_iff pw_le_iff refine_pw_simps)

  lemma leof_strengthen_SPEC: 
    "m \<le>\<^sub>n SPEC \<Phi> \<Longrightarrow> m \<le>\<^sub>n SPEC (\<lambda>x. inres m x \<and> \<Phi> x)"
    by (auto simp: pw_leof_iff)


  lemma ASSERT_leof_defI:
    assumes "c \<equiv> do { ASSERT \<Phi>; m'}"
    assumes "\<Phi> \<Longrightarrow> m' \<le>\<^sub>n m"
    shows "c \<le>\<^sub>n m"
    using assms by (auto simp: pw_leof_iff refine_pw_simps)
  


end


