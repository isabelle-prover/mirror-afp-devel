section \<open>Elementary Logic\<close>

theory Elementary_Logic
  imports
    Proof_System
    Propositional_Wff
begin

no_notation funcset (infixr "\<rightarrow>" 60)
notation funcset (infixr "\<Zpfun>" 60)

subsection \<open>Proposition 5200\<close>

proposition prop_5200:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows "\<turnstile> A =\<^bsub>\<alpha>\<^esub> A"
  using assms and equality_reflexivity and dv_thm by simp

corollary hyp_prop_5200:
  assumes "is_hyps \<H>" and "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows "\<H> \<turnstile> A =\<^bsub>\<alpha>\<^esub> A"
  using derivability_implies_hyp_derivability[OF prop_5200[OF assms(2)] assms(1)] .

subsection \<open>Proposition 5201 (Equality Rules)\<close>

proposition prop_5201_1:
  assumes "\<H> \<turnstile> A" and "\<H> \<turnstile> A \<equiv>\<^sup>\<Q> B"
  shows "\<H> \<turnstile> B"
proof -
  from assms(2) have "\<H> \<turnstile> A =\<^bsub>o\<^esub> B"
    unfolding equivalence_def .
  with assms(1) show ?thesis
    by (rule rule_R'[where p = "[]"]) auto
qed

proposition prop_5201_2:
  assumes "\<H> \<turnstile> A =\<^bsub>\<alpha>\<^esub> B"
  shows "\<H> \<turnstile> B =\<^bsub>\<alpha>\<^esub> A"
proof -
  have "\<H> \<turnstile> A =\<^bsub>\<alpha>\<^esub> A"
  proof (rule hyp_prop_5200)
    from assms show "is_hyps \<H>"
      by (blast elim: is_derivable_from_hyps.cases)
    show "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
      by (fact hyp_derivable_form_is_wffso[OF assms, THEN wffs_from_equality(1)])
  qed
  from this and assms show ?thesis
    by (rule rule_R'[where p = "[\<guillemotleft>,\<guillemotright>]"]) (force+, fastforce dest: subforms_from_app)
qed

proposition prop_5201_3:
  assumes "\<H> \<turnstile> A =\<^bsub>\<alpha>\<^esub> B" and "\<H> \<turnstile> B =\<^bsub>\<alpha>\<^esub> C"
  shows "\<H> \<turnstile> A =\<^bsub>\<alpha>\<^esub> C"
  using assms by (rule rule_R'[where p = "[\<guillemotright>]"]) (force+, fastforce dest: subforms_from_app)

proposition prop_5201_4:
  assumes "\<H> \<turnstile> A =\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> B" and "\<H> \<turnstile> C =\<^bsub>\<alpha>\<^esub> D"
  shows "\<H> \<turnstile> A \<sqdot> C =\<^bsub>\<beta>\<^esub> B \<sqdot> D"
proof -
  have "\<H> \<turnstile> A \<sqdot> C =\<^bsub>\<beta>\<^esub> A \<sqdot> C"
  proof (rule hyp_prop_5200)
    from assms show "is_hyps \<H>"
      by (blast elim: is_derivable_from_hyps.cases)
    from assms have "A \<in> wffs\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>" and "C \<in> wffs\<^bsub>\<alpha>\<^esub>"
      using hyp_derivable_form_is_wffso and wffs_from_equality by blast+
    then show "A \<sqdot> C \<in> wffs\<^bsub>\<beta>\<^esub>"
      by auto
  qed
  from this and assms(1) have "\<H> \<turnstile> A \<sqdot> C =\<^bsub>\<beta>\<^esub> B \<sqdot> C"
    by (rule rule_R'[where p = "[\<guillemotright>,\<guillemotleft>]"]) (force+, fastforce dest: subforms_from_app)
  from this and assms(2) show ?thesis
    by (rule rule_R'[where p = "[\<guillemotright>,\<guillemotright>]"]) (force+, fastforce dest: subforms_from_app)
qed

proposition prop_5201_5:
  assumes "\<H> \<turnstile> A =\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> B" and "C \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows "\<H> \<turnstile> A \<sqdot> C =\<^bsub>\<beta>\<^esub> B \<sqdot> C"
proof -
  have "\<H> \<turnstile> A \<sqdot> C =\<^bsub>\<beta>\<^esub> A \<sqdot> C"
  proof (rule hyp_prop_5200)
    from assms(1) show "is_hyps \<H>"
      by (blast elim: is_derivable_from_hyps.cases)
    have "A \<in> wffs\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>"
      by (fact hyp_derivable_form_is_wffso[OF assms(1), THEN wffs_from_equality(1)])
    with assms(2) show "A \<sqdot> C \<in> wffs\<^bsub>\<beta>\<^esub>"
      by auto
  qed
  from this and assms(1) show ?thesis
    by (rule rule_R'[where p = "[\<guillemotright>,\<guillemotleft>]"]) (force+, fastforce dest: subforms_from_app)
qed

proposition prop_5201_6:
  assumes "\<H> \<turnstile> C =\<^bsub>\<alpha>\<^esub> D" and "A \<in> wffs\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>"
  shows "\<H> \<turnstile> A \<sqdot> C =\<^bsub>\<beta>\<^esub> A \<sqdot> D"
proof -
  have "\<H> \<turnstile> A \<sqdot> C =\<^bsub>\<beta>\<^esub> A \<sqdot> C"
  proof (rule hyp_prop_5200)
    from assms(1) show "is_hyps \<H>"
      by (blast elim: is_derivable_from_hyps.cases)
    have "C \<in> wffs\<^bsub>\<alpha>\<^esub>"
      by (fact hyp_derivable_form_is_wffso[OF assms(1), THEN wffs_from_equality(1)])
    with assms(2) show "A \<sqdot> C \<in> wffs\<^bsub>\<beta>\<^esub>"
      by auto
  qed
  from this and assms(1) show ?thesis
    by (rule rule_R'[where p = "[\<guillemotright>,\<guillemotright>]"]) (force+, fastforce dest: subforms_from_app)
qed

lemmas Equality_Rules = prop_5201_1 prop_5201_2 prop_5201_3 prop_5201_4 prop_5201_5 prop_5201_6

subsection \<open>Proposition 5202 (Rule RR)\<close>

proposition prop_5202:
  assumes "\<turnstile> A =\<^bsub>\<alpha>\<^esub> B \<or> \<turnstile> B =\<^bsub>\<alpha>\<^esub> A"
  and "p \<in> positions C" and "A \<preceq>\<^bsub>p\<^esub> C" and "C\<lblot>p \<leftarrow> B\<rblot> \<rhd> D"
  and "\<H> \<turnstile> C"
  shows "\<H> \<turnstile> D"
proof -
  from assms(5) have "\<turnstile> C =\<^bsub>o\<^esub> C"
    using prop_5200 and hyp_derivable_form_is_wffso by blast
  moreover from assms(1) consider (a) "\<turnstile> A =\<^bsub>\<alpha>\<^esub> B" | (b) "\<turnstile> B =\<^bsub>\<alpha>\<^esub> A"
    by blast
  then have "\<turnstile> A =\<^bsub>\<alpha>\<^esub> B"
    by cases (assumption, fact Equality_Rules(2))
  ultimately have "\<turnstile> C =\<^bsub>o\<^esub> D"
    by (rule rule_R[where p = "\<guillemotright> # p"]) (use assms(2-4) in auto)
  then have "\<H> \<turnstile> C =\<^bsub>o\<^esub> D"
  proof -
    from assms(5) have "is_hyps \<H>"
      by (blast elim: is_derivable_from_hyps.cases)
    with \<open>\<turnstile> C =\<^bsub>o\<^esub> D\<close> show ?thesis
      by (fact derivability_implies_hyp_derivability)
  qed
  with assms(5) show ?thesis
    by (rule Equality_Rules(1)[unfolded equivalence_def])
qed

lemmas rule_RR = prop_5202 (* synonym *)

subsection \<open>Proposition 5203\<close>

proposition prop_5203:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<beta>\<^esub>"
  and "\<forall>v \<in> vars A. \<not> is_bound v B"
  shows "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A =\<^bsub>\<beta>\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> A} B"
using assms(2,1,3) proof induction
  case (var_is_wff \<beta> y)
  then show ?case
  proof (cases "y\<^bsub>\<beta>\<^esub> = x\<^bsub>\<alpha>\<^esub>")
    case True
    then have "\<alpha> = \<beta>"
      by simp
    moreover from assms(1) have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. x\<^bsub>\<alpha>\<^esub>) \<sqdot> A =\<^bsub>\<alpha>\<^esub> A"
      using axiom_4_2 by (intro axiom_is_derivable_from_no_hyps)
    moreover have "\<^bold>S {(x, \<alpha>) \<Zinj> A} (x\<^bsub>\<alpha>\<^esub>) = A"
      by force
    ultimately show ?thesis
      using True by (simp only:)
  next
    case False
    with assms(1) have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. y\<^bsub>\<beta>\<^esub>) \<sqdot> A =\<^bsub>\<beta>\<^esub> y\<^bsub>\<beta>\<^esub>"
      using axiom_4_1_var by (intro axiom_is_derivable_from_no_hyps)
    moreover from False have "\<^bold>S {(x, \<alpha>) \<Zinj> A} (y\<^bsub>\<beta>\<^esub>) = y\<^bsub>\<beta>\<^esub>"
      by auto
    ultimately show ?thesis
      by (simp only:)
  qed
next
  case (con_is_wff \<beta> c)
  from assms(1) have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>) \<sqdot> A =\<^bsub>\<beta>\<^esub> \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>"
    using axiom_4_1_con by (intro axiom_is_derivable_from_no_hyps)
  moreover have "\<^bold>S {(x, \<alpha>) \<Zinj> A} (\<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>) = \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>"
    by auto
  ultimately show ?case
    by (simp only:)
next
  case (app_is_wff \<gamma> \<beta> D C)
  from app_is_wff.prems(2) have not_bound_subforms: "\<forall>v \<in> vars A. \<not> is_bound v D \<and> \<not> is_bound v C"
    using is_bound_in_app_homomorphism by fast
  from \<open>D \<in> wffs\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub>\<close> have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. D) \<sqdot> A =\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> A} D"
    using app_is_wff.IH(1)[OF assms(1)] and not_bound_subforms by simp
  moreover from \<open>C \<in> wffs\<^bsub>\<gamma>\<^esub>\<close> have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. C) \<sqdot> A =\<^bsub>\<gamma>\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> A} C"
    using app_is_wff.IH(2)[OF assms(1)] and not_bound_subforms by simp
  moreover have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. D \<sqdot> C) \<sqdot> A =\<^bsub>\<beta>\<^esub> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. D) \<sqdot> A) \<sqdot> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. C) \<sqdot> A)"
    using axiom_is_derivable_from_no_hyps[OF axiom_4_3[OF assms(1) \<open>D \<in> wffs\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub>\<close> \<open>C \<in> wffs\<^bsub>\<gamma>\<^esub>\<close>]] .
  ultimately show ?case
    using Equality_Rules(3,4) and substitute.simps(3) by presburger
next
  case (abs_is_wff \<beta> D \<gamma> y)
  then show ?case
  proof (cases "y\<^bsub>\<gamma>\<^esub> = x\<^bsub>\<alpha>\<^esub>")
    case True
    then have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>y\<^bsub>\<gamma>\<^esub>. D) \<sqdot> A =\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub> \<lambda>y\<^bsub>\<gamma>\<^esub>. D"
      using axiom_is_derivable_from_no_hyps[OF axiom_4_5[OF assms(1) abs_is_wff.hyps(1)]] by fast
    moreover from True have "\<^bold>S {(x, \<alpha>) \<Zinj> A} (\<lambda>y\<^bsub>\<gamma>\<^esub>. D) = \<lambda>y\<^bsub>\<gamma>\<^esub>. D"
      using empty_substitution_neutrality
      by (simp add: singleton_substitution_simps(4) fmdrop_fmupd_same)
    ultimately show ?thesis
      by (simp only:)
  next
    case False
    have "binders_at (\<lambda>y\<^bsub>\<gamma>\<^esub>. D) [\<guillemotleft>] = {(y, \<gamma>)}"
      by simp
    then have "is_bound (y, \<gamma>) (\<lambda>y\<^bsub>\<gamma>\<^esub>. D)"
      by fastforce
    with abs_is_wff.prems(2) have "(y, \<gamma>) \<notin> vars A"
      by blast
    with \<open>y\<^bsub>\<gamma>\<^esub> \<noteq> x\<^bsub>\<alpha>\<^esub>\<close> have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>y\<^bsub>\<gamma>\<^esub>. D) \<sqdot> A =\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub> \<lambda>y\<^bsub>\<gamma>\<^esub>. (\<lambda>x\<^bsub>\<alpha>\<^esub>. D) \<sqdot> A"
      using axiom_4_4[OF assms(1) abs_is_wff.hyps(1)] and axiom_is_derivable_from_no_hyps by blast
    moreover have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. D) \<sqdot> A =\<^bsub>\<beta>\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> A} D"
    proof -
      have "\<forall>p. y\<^bsub>\<gamma>\<^esub> \<preceq>\<^bsub>\<guillemotleft> # p\<^esub> \<lambda>y\<^bsub>\<gamma>\<^esub>. D \<longrightarrow> y\<^bsub>\<gamma>\<^esub> \<preceq>\<^bsub>p\<^esub> D"
        using subforms_from_abs by fastforce
      from abs_is_wff.prems(2) have "\<forall>v \<in> vars A. \<not> is_bound v D"
        using is_bound_in_abs_body by fast
      then show ?thesis
        by (fact abs_is_wff.IH[OF assms(1)])
    qed
    ultimately have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>y\<^bsub>\<gamma>\<^esub>. D) \<sqdot> A =\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub> \<lambda>y\<^bsub>\<gamma>\<^esub>. \<^bold>S {(x, \<alpha>) \<Zinj> A} D"
      by (rule rule_R[where p = "[\<guillemotright>,\<guillemotleft>]"]) force+
    with False show ?thesis
      by simp
  qed
qed

subsection \<open>Proposition 5204\<close>

proposition prop_5204:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<beta>\<^esub>" and "C \<in> wffs\<^bsub>\<beta>\<^esub>"
  and "\<turnstile> B =\<^bsub>\<beta>\<^esub> C"
  and "\<forall>v \<in> vars A. \<not> is_bound v B \<and> \<not> is_bound v C"
  shows "\<turnstile> \<^bold>S {(x, \<alpha>) \<Zinj> A} (B =\<^bsub>\<beta>\<^esub> C)"
proof -
  have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A =\<^bsub>\<beta>\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A"
  proof -
    have "(\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A \<in> wffs\<^bsub>\<beta>\<^esub>"
      using assms(1,2) by auto
    then show ?thesis
      by (fact prop_5200)
  qed
  from this and assms(4) have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A =\<^bsub>\<beta>\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. C) \<sqdot> A"
    by (rule rule_R[where p = "[\<guillemotright>,\<guillemotleft>,\<guillemotleft>]"]) force+
  moreover from assms(1,2,5) have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A =\<^bsub>\<beta>\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> A} B"
    using prop_5203 by auto
  moreover from assms(1,3,5) have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. C) \<sqdot> A =\<^bsub>\<beta>\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> A} C"
    using prop_5203 by auto
  ultimately have "\<turnstile> (\<^bold>S {(x, \<alpha>) \<Zinj> A} B) =\<^bsub>\<beta>\<^esub> (\<^bold>S {(x, \<alpha>) \<Zinj> A} C)"
    using Equality_Rules(2,3) by blast
  then show ?thesis
    by simp
qed

subsection \<open>Proposition 5205 ($\eta$-conversion)\<close>

proposition prop_5205:
  shows "\<turnstile> \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> =\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> (\<lambda>y\<^bsub>\<alpha>\<^esub>. \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> y\<^bsub>\<alpha>\<^esub>)"
proof -
  {
  fix y
  assume "y\<^bsub>\<alpha>\<^esub> \<noteq> \<xx>\<^bsub>\<alpha>\<^esub>"
  let ?A = "\<lambda>y\<^bsub>\<alpha>\<^esub>. \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> y\<^bsub>\<alpha>\<^esub>"
  have "\<turnstile> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> =\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> ?A) =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>\<alpha>\<^esub>. (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> ?A \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>)"
  proof -
    have "\<turnstile> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> =\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>) =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>\<alpha>\<^esub>. (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>)" (is "\<turnstile> ?B =\<^bsub>o\<^esub> ?C")
      using axiom_3[unfolded equivalence_def] by (rule axiom_is_derivable_from_no_hyps)
    have "\<turnstile> \<^bold>S {(\<gg>, \<alpha>\<rightarrow>\<beta>) \<Zinj> ?A} (?B =\<^bsub>o\<^esub> ?C)"
    proof -
      have "?A \<in> wffs\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>" and "?B \<in> wffs\<^bsub>o\<^esub>" and "?C \<in> wffs\<^bsub>o\<^esub>"
        by auto
      moreover have "\<forall>v \<in> vars ?A. \<not> is_bound v ?B \<and> \<not> is_bound v ?C"
      proof
        fix v
        assume "v \<in> vars ?A"
        have "vars ?B = {(\<ff>, \<alpha>\<rightarrow>\<beta>), (\<gg>, \<alpha>\<rightarrow>\<beta>)}" and "vars ?C = {(\<ff>, \<alpha>\<rightarrow>\<beta>), (\<xx>, \<alpha>), (\<gg>, \<alpha>\<rightarrow>\<beta>)}"
          by force+
        with \<open>y\<^bsub>\<alpha>\<^esub> \<noteq> \<xx>\<^bsub>\<alpha>\<^esub>\<close> have "(y, \<alpha>) \<notin> vars ?B" and "(y, \<alpha>) \<notin> vars ?C"
          by force+
        then have "\<not> is_bound (y, \<alpha>) ?B" and "\<not> is_bound (y, \<alpha>) ?C"
          using absent_var_is_not_bound by blast+
        moreover have "\<not> is_bound (\<ff>, \<alpha>\<rightarrow>\<beta>) ?B" and "\<not> is_bound (\<ff>, \<alpha>\<rightarrow>\<beta>) ?C"
          by code_simp+
        moreover from \<open>v \<in> vars ?A\<close> have "v \<in> {(y, \<alpha>), (\<ff>, \<alpha>\<rightarrow>\<beta>)}"
          by auto
        ultimately show "\<not> is_bound v ?B \<and> \<not> is_bound v ?C"
          by fast
      qed
      ultimately show ?thesis
        using \<open>\<turnstile> ?B =\<^bsub>o\<^esub> ?C\<close> and prop_5204 by presburger
    qed
    then show ?thesis
      by simp
  qed
  moreover have "\<turnstile> ?A \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>"
  proof -
    have "\<xx>\<^bsub>\<alpha>\<^esub> \<in> wffs\<^bsub>\<alpha>\<^esub>" and "\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> y\<^bsub>\<alpha>\<^esub> \<in> wffs\<^bsub>\<beta>\<^esub>"
      by auto
    moreover have "\<forall>v \<in> vars (\<xx>\<^bsub>\<alpha>\<^esub>). \<not> is_bound v (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> y\<^bsub>\<alpha>\<^esub>)"
      using \<open>y\<^bsub>\<alpha>\<^esub> \<noteq> \<xx>\<^bsub>\<alpha>\<^esub>\<close> by auto
    moreover have "\<^bold>S {(y, \<alpha>) \<Zinj> \<xx>\<^bsub>\<alpha>\<^esub>} (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> y\<^bsub>\<alpha>\<^esub>) =  \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>"
      by simp
    ultimately show ?thesis
      using prop_5203 by metis
  qed
  ultimately have "\<turnstile> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> =\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> ?A) =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>\<alpha>\<^esub>. (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>)"
    by (rule rule_R[where p = "[\<guillemotright>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]"]) force+
  moreover have "\<turnstile> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> =\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>) =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>\<alpha>\<^esub>. (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>)"
  proof -
    let ?A = "\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>"
    have "\<turnstile> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> =\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>) =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>\<alpha>\<^esub>. (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>)" (is "\<turnstile> ?B =\<^bsub>o\<^esub> ?C")
      using axiom_3[unfolded equivalence_def] by (rule axiom_is_derivable_from_no_hyps)
    have "\<turnstile> \<^bold>S {(\<gg>, \<alpha>\<rightarrow>\<beta>) \<Zinj> ?A} (?B =\<^bsub>o\<^esub> ?C)"
    proof -
      have "?A \<in> wffs\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>" and "?B \<in> wffs\<^bsub>o\<^esub>" and "?C \<in> wffs\<^bsub>o\<^esub>"
        by auto
      moreover have "\<forall>v \<in> vars ?A. \<not> is_bound v ?B \<and> \<not> is_bound v ?C"
      proof
        fix v
        assume "v \<in> vars ?A"
        have "vars ?B = {(\<ff>, \<alpha>\<rightarrow>\<beta>), (\<gg>, \<alpha>\<rightarrow>\<beta>)}" and "vars ?C = {(\<ff>, \<alpha>\<rightarrow>\<beta>), (\<xx>, \<alpha>), (\<gg>, \<alpha>\<rightarrow>\<beta>)}"
          by force+
        with \<open>y\<^bsub>\<alpha>\<^esub> \<noteq> \<xx>\<^bsub>\<alpha>\<^esub>\<close> have "(y, \<alpha>) \<notin> vars ?B" and "(y, \<alpha>) \<notin> vars ?C"
          by force+
        then have "\<not> is_bound (y, \<alpha>) ?B" and "\<not> is_bound (y, \<alpha>) ?C"
          using absent_var_is_not_bound by blast+
        moreover have "\<not> is_bound (\<ff>, \<alpha>\<rightarrow>\<beta>) ?B" and "\<not> is_bound (\<ff>, \<alpha>\<rightarrow>\<beta>) ?C"
          by code_simp+
        moreover from \<open>v \<in> vars ?A \<close>have "v \<in> {(y, \<alpha>), (\<ff>, \<alpha>\<rightarrow>\<beta>)}"
          by auto
        ultimately show "\<not> is_bound v ?B \<and> \<not> is_bound v ?C"
          by fast
      qed
      ultimately show ?thesis
        using \<open>\<turnstile> ?B =\<^bsub>o\<^esub> ?C\<close> and prop_5204 by presburger
    qed
    then show ?thesis
      by simp
  qed
  ultimately have "\<turnstile> \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> =\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> (\<lambda>y\<^bsub>\<alpha>\<^esub>. \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> y\<^bsub>\<alpha>\<^esub>)"
    using Equality_Rules(1)[unfolded equivalence_def] and Equality_Rules(2) and prop_5200
    by (metis wffs_of_type_intros(1))
  }
  note x_neq_y = this
  then have "\<section>6": "\<turnstile> \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> =\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<lambda>\<yy>\<^bsub>\<alpha>\<^esub>. \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<yy>\<^bsub>\<alpha>\<^esub>" (is "\<turnstile> ?B =\<^bsub>_\<^esub> ?C")
    by simp
  then have "\<section>7": "\<turnstile> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) =\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> (\<lambda>\<yy>\<^bsub>\<alpha>\<^esub>. (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) \<sqdot> \<yy>\<^bsub>\<alpha>\<^esub>)"
  proof -
    let ?A = "\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>"
    have "?A \<in> wffs\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>" and "?B \<in> wffs\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>" and "?C \<in> wffs\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>"
      by auto
    moreover have "\<forall>v \<in> vars ?A. \<not> is_bound v ?B \<and> \<not> is_bound v ?C"
    proof
      fix v
      assume "v \<in> vars ?A"
      have "\<not> is_bound (\<xx>, \<alpha>) ?B" and "\<not> is_bound (\<xx>, \<alpha>) ?C"
        by code_simp+
      moreover have "\<not> is_bound (\<ff>, \<alpha>\<rightarrow>\<beta>) ?B" and "\<not> is_bound (\<ff>, \<alpha>\<rightarrow>\<beta>) ?C"
        by code_simp+
      moreover from \<open>v \<in> vars ?A \<close>have "v \<in> {(\<xx>, \<alpha>), (\<ff>, \<alpha>\<rightarrow>\<beta>)}"
        by auto
      ultimately show "\<not> is_bound v ?B \<and> \<not> is_bound v ?C"
        by fast
    qed
    ultimately have "\<turnstile> \<^bold>S {(\<ff>, \<alpha>\<rightarrow>\<beta>) \<Zinj> ?A} (?B =\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> ?C)"
      using "\<section>6" and prop_5204 by presburger
    then show ?thesis
      by simp
  qed
  have "\<turnstile> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) =\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> (\<lambda>\<yy>\<^bsub>\<alpha>\<^esub>. \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<yy>\<^bsub>\<alpha>\<^esub>)"
  proof -
    have "\<turnstile> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) \<sqdot> \<yy>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<yy>\<^bsub>\<alpha>\<^esub>"
    proof -
      have "\<yy>\<^bsub>\<alpha>\<^esub> \<in> wffs\<^bsub>\<alpha>\<^esub>" and "\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> \<in> wffs\<^bsub>\<beta>\<^esub>"
        by auto
      moreover have "\<forall>v \<in> vars (\<yy>\<^bsub>\<alpha>\<^esub>). \<not> is_bound v (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>)"
        by simp
      moreover have "\<^bold>S {(\<xx>, \<alpha>) \<Zinj> \<yy>\<^bsub>\<alpha>\<^esub>} (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) = \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<yy>\<^bsub>\<alpha>\<^esub>"
        by simp
      ultimately show ?thesis
        using prop_5203 by metis
    qed
    from "\<section>7" and this show ?thesis
      by (rule rule_R [where p = "[\<guillemotright>,\<guillemotleft>]"]) force+
  qed
  with "\<section>6" and x_neq_y[of y] show ?thesis
    using Equality_Rules(2,3) by blast
qed

subsection \<open>Proposition 5206 ($\alpha$-conversion)\<close>

proposition prop_5206:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  and "(z, \<beta>) \<notin> free_vars A"
  and "is_free_for (z\<^bsub>\<beta>\<^esub>) (x, \<beta>) A"
  shows "\<turnstile> (\<lambda>x\<^bsub>\<beta>\<^esub>. A) =\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> (\<lambda>z\<^bsub>\<beta>\<^esub>. \<^bold>S {(x, \<beta>) \<Zinj> z\<^bsub>\<beta>\<^esub>} A)"
proof -
  have "is_substitution {(x, \<beta>) \<Zinj> z\<^bsub>\<beta>\<^esub>}"
    by auto
  from this and assms(1) have "\<^bold>S {(x, \<beta>) \<Zinj> z\<^bsub>\<beta>\<^esub>} A \<in> wffs\<^bsub>\<alpha>\<^esub>"
    by (fact substitution_preserves_typing)
  obtain y where "(y, \<beta>) \<notin> {(x, \<beta>), (z, \<beta>)} \<union> vars A"
  proof -
    have "finite ({(x, \<beta>), (z, \<beta>)} \<union> vars A)"
      using vars_form_finiteness by blast
    with that show ?thesis
      using fresh_var_existence by metis
  qed
  then have "(y, \<beta>) \<noteq> (x, \<beta>)" and "(y, \<beta>) \<noteq> (z, \<beta>)" and "(y, \<beta>) \<notin> vars A" and "(y, \<beta>) \<notin> free_vars A"
    using free_vars_in_all_vars by auto
  have "\<section>1": "\<turnstile> (\<lambda>x\<^bsub>\<beta>\<^esub>. A) =\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> (\<lambda>y\<^bsub>\<beta>\<^esub>. (\<lambda>x\<^bsub>\<beta>\<^esub>. A) \<sqdot> y\<^bsub>\<beta>\<^esub>)"
  proof -
    let ?A = "\<lambda>x\<^bsub>\<beta>\<^esub>. A"
    have *: "\<turnstile> \<ff>\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> =\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> (\<lambda>y\<^bsub>\<beta>\<^esub>. \<ff>\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> \<sqdot> y\<^bsub>\<beta>\<^esub>)" (is "\<turnstile> ?B =\<^bsub>_\<^esub> ?C")
      by (fact prop_5205)
    moreover have "\<turnstile> \<^bold>S {(\<ff>, \<beta>\<rightarrow>\<alpha>) \<Zinj> ?A} (?B =\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> ?C)"
    proof -
      from assms(1) have "?A \<in> wffs\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub>" and "?B \<in> wffs\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub>" and "?C \<in> wffs\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub>"
        by auto
      moreover have "\<forall>v \<in> vars ?A. \<not> is_bound v ?B \<and> \<not> is_bound v ?C"
      proof
        fix v
        assume "v \<in> vars ?A"
        then consider (a) "v = (x, \<beta>)" | (b) "v \<in> vars A"
          by fastforce
        then show "\<not> is_bound v ?B \<and> \<not> is_bound v ?C"
        proof cases
          case a
          then show ?thesis
            using \<open>(y, \<beta>) \<noteq> (x, \<beta>)\<close> by force
        next
          case b
          then have "\<not> is_bound v ?B"
            by simp
          moreover have "\<not> is_bound v ?C"
            using b and \<open>(y, \<beta>) \<notin> vars A\<close> by code_simp force
          ultimately show ?thesis
            by blast
        qed
      qed
      ultimately show ?thesis
        using prop_5204 and * by presburger
    qed
    ultimately show ?thesis
      by simp
  qed
  then have "\<section>2": "\<turnstile> (\<lambda>x\<^bsub>\<beta>\<^esub>. A) =\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> (\<lambda>y\<^bsub>\<beta>\<^esub>. \<^bold>S {(x, \<beta>) \<Zinj> y\<^bsub>\<beta>\<^esub>} A)"
  proof -
    have "\<turnstile> (\<lambda>x\<^bsub>\<beta>\<^esub>. A) \<sqdot> y\<^bsub>\<beta>\<^esub> =\<^bsub>\<alpha>\<^esub> \<^bold>S {(x, \<beta>) \<Zinj> y\<^bsub>\<beta>\<^esub>} A" (is "\<turnstile> (\<lambda>x\<^bsub>\<beta>\<^esub>. ?B) \<sqdot> ?A =\<^bsub>_\<^esub> _")
    proof -
      have "?A \<in> wffs\<^bsub>\<beta>\<^esub>" and "?B \<in> wffs\<^bsub>\<alpha>\<^esub>"
        by blast fact
      moreover have "\<forall>v \<in> vars ?A. \<not> is_bound v ?B"
        using \<open>(y, \<beta>) \<notin> vars A\<close> and absent_var_is_not_bound by auto
      ultimately show ?thesis
        by (fact prop_5203)
    qed
    with "\<section>1" show ?thesis
      by (rule rule_R [where p = "[\<guillemotright>,\<guillemotleft>]"]) force+
  qed
  moreover
  have "\<section>3": "\<turnstile> (\<lambda>z\<^bsub>\<beta>\<^esub>. \<^bold>S {(x, \<beta>) \<Zinj> z\<^bsub>\<beta>\<^esub>} A) =\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> (\<lambda>y\<^bsub>\<beta>\<^esub>. (\<lambda>z\<^bsub>\<beta>\<^esub>. \<^bold>S {(x, \<beta>) \<Zinj> z\<^bsub>\<beta>\<^esub>} A) \<sqdot> y\<^bsub>\<beta>\<^esub>)"
  proof -
    let ?A = "\<lambda>z\<^bsub>\<beta>\<^esub>. \<^bold>S {(x, \<beta>) \<Zinj> z\<^bsub>\<beta>\<^esub>} A"
    have *: "\<turnstile> \<ff>\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> =\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> (\<lambda>y\<^bsub>\<beta>\<^esub>. \<ff>\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> \<sqdot> y\<^bsub>\<beta>\<^esub>)" (is "\<turnstile> ?B =\<^bsub>_\<^esub> ?C")
      by (fact prop_5205)
    moreover have "\<turnstile> \<^bold>S {(\<ff>, \<beta>\<rightarrow>\<alpha>) \<Zinj> ?A} (?B =\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> ?C)"
    proof -
      have "?A \<in> wffs\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub>" and "?B \<in> wffs\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub>" and "?C \<in> wffs\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub>"
        using \<open>\<^bold>S {(x, \<beta>) \<Zinj> z\<^bsub>\<beta>\<^esub>} A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> by auto
      moreover have "\<forall>v \<in> vars ?A. \<not> is_bound v ?B \<and> \<not> is_bound v ?C"
      proof
        fix v
        assume "v \<in> vars ?A"
        then consider (a) "v = (z, \<beta>)" | (b) "v \<in> vars (\<^bold>S {(x, \<beta>) \<Zinj> z\<^bsub>\<beta>\<^esub>} A)"
          by fastforce
        then show "\<not> is_bound v ?B \<and> \<not> is_bound v ?C"
        proof cases
          case a
          then show ?thesis
            using \<open>(y, \<beta>) \<noteq> (z, \<beta>)\<close> by auto
        next
          case b
          then have "\<not> is_bound v ?B"
            by simp
          moreover from b and \<open>(y, \<beta>) \<notin> vars A\<close> and \<open>(y, \<beta>) \<noteq> (z, \<beta>)\<close> have "v \<noteq> (y, \<beta>)"
            using renaming_substitution_minimal_change by blast
          then have "\<not> is_bound v ?C"
            by code_simp simp
          ultimately show ?thesis
            by blast
        qed
      qed
      ultimately show ?thesis
        using prop_5204 and * by presburger
    qed
    ultimately show ?thesis
      by simp
  qed
  then have "\<section>4": "\<turnstile> (\<lambda>z\<^bsub>\<beta>\<^esub>. \<^bold>S {(x, \<beta>) \<Zinj> z\<^bsub>\<beta>\<^esub>} A) =\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> (\<lambda>y\<^bsub>\<beta>\<^esub>. \<^bold>S {(x, \<beta>) \<Zinj> y\<^bsub>\<beta>\<^esub>} A)"
  proof -
    have "\<turnstile> (\<lambda>z\<^bsub>\<beta>\<^esub>. \<^bold>S {(x, \<beta>) \<Zinj> z\<^bsub>\<beta>\<^esub>} A) \<sqdot> y\<^bsub>\<beta>\<^esub> =\<^bsub>\<alpha>\<^esub> \<^bold>S {(x, \<beta>) \<Zinj> y\<^bsub>\<beta>\<^esub>} A" (is "\<turnstile> (\<lambda>z\<^bsub>\<beta>\<^esub>. ?B) \<sqdot> ?A =\<^bsub>_\<^esub> _")
    proof -
      have "?A \<in> wffs\<^bsub>\<beta>\<^esub>" and "?B \<in> wffs\<^bsub>\<alpha>\<^esub>"
        by blast fact
      moreover from \<open>(y, \<beta>) \<notin> vars A\<close> and \<open>(y, \<beta>) \<noteq> (z, \<beta>)\<close> have "\<forall>v \<in> vars ?A. \<not> is_bound v ?B"
        using absent_var_is_not_bound and renaming_substitution_minimal_change by auto
      ultimately have "\<turnstile> (\<lambda>z\<^bsub>\<beta>\<^esub>. \<^bold>S {(x, \<beta>) \<Zinj> z\<^bsub>\<beta>\<^esub>} A) \<sqdot> y\<^bsub>\<beta>\<^esub> =\<^bsub>\<alpha>\<^esub> \<^bold>S {(z, \<beta>) \<Zinj> y\<^bsub>\<beta>\<^esub>} \<^bold>S {(x, \<beta>) \<Zinj> z\<^bsub>\<beta>\<^esub>} A"
        using prop_5203 by fast
      moreover have "\<^bold>S {(z, \<beta>) \<Zinj> y\<^bsub>\<beta>\<^esub>} \<^bold>S {(x, \<beta>) \<Zinj> z\<^bsub>\<beta>\<^esub>} A = \<^bold>S {(x, \<beta>) \<Zinj> y\<^bsub>\<beta>\<^esub>} A"
        by (fact renaming_substitution_composability[OF assms(2,3)])
      ultimately show ?thesis
        by (simp only:)
    qed
    with "\<section>3" show ?thesis
      by (rule rule_R [where p = "[\<guillemotright>,\<guillemotleft>]"]) auto
  qed
  ultimately show ?thesis
    using Equality_Rules(2,3) by blast
qed

lemmas "\<alpha>" = prop_5206 (* synonym *)

subsection \<open>Proposition 5207 ($\beta$-conversion)\<close>

context
begin

private lemma bound_var_renaming_equality:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  and "z\<^bsub>\<gamma>\<^esub> \<noteq> y\<^bsub>\<gamma>\<^esub>"
  and "(z, \<gamma>) \<notin> vars A"
  shows "\<turnstile> A =\<^bsub>\<alpha>\<^esub> rename_bound_var (y, \<gamma>) z A"
using assms proof induction
  case (var_is_wff \<alpha> x)
  then show ?case
    using prop_5200 by force
next
  case (con_is_wff \<alpha> c)
  then show ?case
    using prop_5200 by force
next
  case (app_is_wff \<alpha> \<beta> A B)
  then show ?case
    using Equality_Rules(4) by auto
next
  case (abs_is_wff \<beta> A \<alpha> x)
  then show ?case
  proof (cases "(y, \<gamma>) = (x, \<alpha>)")
    case True
    have "\<turnstile> \<lambda>y\<^bsub>\<gamma>\<^esub>. A =\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub> \<lambda>y\<^bsub>\<gamma>\<^esub>. A"
      by (fact abs_is_wff.hyps[THEN prop_5200[OF wffs_of_type_intros(4)]])
    moreover have "\<turnstile> A =\<^bsub>\<beta>\<^esub> rename_bound_var (y, \<gamma>) z A"
      using abs_is_wff.IH[OF assms(2)] and abs_is_wff.prems(2) by fastforce
    ultimately have "\<turnstile> \<lambda>y\<^bsub>\<gamma>\<^esub>. A =\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub> \<lambda>y\<^bsub>\<gamma>\<^esub>. rename_bound_var (y, \<gamma>) z A"
      by (rule rule_R[where p = "[\<guillemotright>,\<guillemotleft>]"]) force+
    moreover
    have "
      \<turnstile> \<lambda>y\<^bsub>\<gamma>\<^esub>. rename_bound_var (y, \<gamma>) z A
        =\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub>
        \<lambda>z\<^bsub>\<gamma>\<^esub>. \<^bold>S {(y, \<gamma>) \<Zinj> z\<^bsub>\<gamma>\<^esub>} (rename_bound_var (y, \<gamma>) z A)"
    proof -
      have "rename_bound_var (y, \<gamma>) z A \<in> wffs\<^bsub>\<beta>\<^esub>"
        using hyp_derivable_form_is_wffso[OF \<open>\<turnstile> A =\<^bsub>\<beta>\<^esub> rename_bound_var (y, \<gamma>) z A\<close>]
        by (blast dest: wffs_from_equality)
      moreover from abs_is_wff.prems(2) have "(z, \<gamma>) \<notin> free_vars (rename_bound_var (y, \<gamma>) z A)"
        using rename_bound_var_free_vars[OF abs_is_wff.hyps assms(2)] by simp
      moreover from abs_is_wff.prems(2) have "is_free_for (z\<^bsub>\<gamma>\<^esub>) (y, \<gamma>) (rename_bound_var (y, \<gamma>) z A)"
        using is_free_for_in_rename_bound_var[OF abs_is_wff.hyps assms(2)] by simp
      ultimately show ?thesis
        using "\<alpha>" by fast
    qed
    ultimately have "\<turnstile> \<lambda>y\<^bsub>\<gamma>\<^esub>. A =\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub> \<lambda>z\<^bsub>\<gamma>\<^esub>. \<^bold>S {(y, \<gamma>) \<Zinj> z\<^bsub>\<gamma>\<^esub>} (rename_bound_var (y, \<gamma>) z A)"
      by (rule Equality_Rules(3))
    then show ?thesis
      using True by auto
  next
    case False
    have "\<turnstile> \<lambda>x\<^bsub>\<alpha>\<^esub>. A =\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<lambda>x\<^bsub>\<alpha>\<^esub>. A"
      by (fact abs_is_wff.hyps[THEN prop_5200[OF wffs_of_type_intros(4)]])
    moreover have "\<turnstile> A =\<^bsub>\<beta>\<^esub> rename_bound_var (y, \<gamma>) z A"
      using abs_is_wff.IH[OF assms(2)] and abs_is_wff.prems(2) by fastforce
    ultimately have "\<turnstile> \<lambda>x\<^bsub>\<alpha>\<^esub>. A =\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<lambda>x\<^bsub>\<alpha>\<^esub>. rename_bound_var (y, \<gamma>) z A"
      by (rule rule_R[where p = "[\<guillemotright>,\<guillemotleft>]"]) force+
    then show ?thesis
      using False by auto
  qed
qed

proposition prop_5207:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<beta>\<^esub>"
  and "is_free_for A (x, \<alpha>) B"
  shows "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A =\<^bsub>\<beta>\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> A} B"
using assms proof (induction "form_size B" arbitrary: B \<beta> rule: less_induct)
  case less
  from less(3,1,2,4) show ?case
  proof (cases B rule: wffs_of_type_cases)
    case (var_is_wff y)
    then show ?thesis
    proof (cases "y\<^bsub>\<beta>\<^esub> = x\<^bsub>\<alpha>\<^esub>")
      case True
      then have "\<alpha> = \<beta>"
        by simp
      moreover from assms(1) have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. x\<^bsub>\<alpha>\<^esub>) \<sqdot> A =\<^bsub>\<alpha>\<^esub> A"
        using axiom_4_2 by (intro axiom_is_derivable_from_no_hyps)
      moreover have "\<^bold>S {(x, \<alpha>) \<Zinj> A} (x\<^bsub>\<alpha>\<^esub>) = A"
        by force
      ultimately show ?thesis
        unfolding True and var_is_wff by simp
    next
      case False
      with assms(1) have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. y\<^bsub>\<beta>\<^esub>) \<sqdot> A =\<^bsub>\<beta>\<^esub> y\<^bsub>\<beta>\<^esub>"
        using axiom_4_1_var by (intro axiom_is_derivable_from_no_hyps)
      moreover from False have "\<^bold>S {(x, \<alpha>) \<Zinj> A} (y\<^bsub>\<beta>\<^esub>) = y\<^bsub>\<beta>\<^esub>"
        by auto
      ultimately show ?thesis
        unfolding False and var_is_wff by simp
    qed
  next
    case (con_is_wff c)
     from assms(1) have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>) \<sqdot> A =\<^bsub>\<beta>\<^esub> \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>"
      using axiom_4_1_con by (intro axiom_is_derivable_from_no_hyps)
    moreover have "\<^bold>S {(x, \<alpha>) \<Zinj> A} (\<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>) = \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>"
      by auto
    ultimately show ?thesis
      by (simp only: con_is_wff)
  next
    case (app_is_wff \<gamma> D C)
    have "form_size D < form_size B" and "form_size C < form_size B"
      unfolding app_is_wff(1) by simp_all
    from less(4)[unfolded app_is_wff(1)] have "is_free_for A (x, \<alpha>) D" and "is_free_for A (x, \<alpha>) C"
      using is_free_for_from_app by iprover+
    from \<open>is_free_for A (x, \<alpha>) D\<close> have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. D) \<sqdot> A =\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> A} D"
      by (fact less(1)[OF \<open>form_size D < form_size B\<close> assms(1) app_is_wff(2)])
    moreover from \<open>is_free_for A (x, \<alpha>) C\<close> have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. C) \<sqdot> A =\<^bsub>\<gamma>\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> A} C"
      by (fact less(1)[OF \<open>form_size C < form_size B\<close> assms(1) app_is_wff(3)])
    moreover have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. D \<sqdot> C) \<sqdot> A =\<^bsub>\<beta>\<^esub> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. D) \<sqdot> A) \<sqdot> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. C) \<sqdot> A)"
      by (fact axiom_4_3[OF assms(1) app_is_wff(2,3), THEN axiom_is_derivable_from_no_hyps])
    ultimately show ?thesis
      unfolding app_is_wff(1) using Equality_Rules(3,4) and substitute.simps(3) by presburger
  next
    case (abs_is_wff \<delta> D \<gamma> y)
    then show ?thesis
    proof (cases "y\<^bsub>\<gamma>\<^esub> = x\<^bsub>\<alpha>\<^esub>")
      case True
      with abs_is_wff(1) have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>y\<^bsub>\<gamma>\<^esub>. D) \<sqdot> A =\<^bsub>\<beta>\<^esub> \<lambda>y\<^bsub>\<gamma>\<^esub>. D"
        using axiom_4_5[OF assms(1) abs_is_wff(3)] by (simp add: axiom_is_derivable_from_no_hyps)
      moreover have "\<^bold>S {(x, \<alpha>) \<Zinj> A} (\<lambda>y\<^bsub>\<gamma>\<^esub>. D) = \<lambda>y\<^bsub>\<gamma>\<^esub>. D"
        using True by (simp add: empty_substitution_neutrality fmdrop_fmupd_same)
      ultimately show ?thesis
        unfolding abs_is_wff(2) by (simp only:)
    next
      case False
      have "form_size D < form_size B"
        unfolding abs_is_wff(2) by simp
      have "is_free_for A (x, \<alpha>) D"
        using is_free_for_from_abs[OF less(4)[unfolded abs_is_wff(2)]] and \<open>y\<^bsub>\<gamma>\<^esub> \<noteq> x\<^bsub>\<alpha>\<^esub>\<close> by blast
      have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. (\<lambda>y\<^bsub>\<gamma>\<^esub>. D)) \<sqdot> A =\<^bsub>\<beta>\<^esub> \<lambda>y\<^bsub>\<gamma>\<^esub>. \<^bold>S {(x, \<alpha>) \<Zinj> A} D"
      proof (cases "(y, \<gamma>) \<notin> vars A")
        case True
        with \<open>y\<^bsub>\<gamma>\<^esub> \<noteq> x\<^bsub>\<alpha>\<^esub>\<close> have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>y\<^bsub>\<gamma>\<^esub>. D) \<sqdot> A =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> \<lambda>y\<^bsub>\<gamma>\<^esub>. (\<lambda>x\<^bsub>\<alpha>\<^esub>. D) \<sqdot> A"
          using axiom_4_4[OF assms(1) abs_is_wff(3)] and axiom_is_derivable_from_no_hyps by auto
        moreover have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. D) \<sqdot> A =\<^bsub>\<delta>\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> A} D"
          by
            (
              fact less(1)
                [OF \<open>form_size D < form_size B\<close> assms(1) \<open>D \<in> wffs\<^bsub>\<delta>\<^esub>\<close> \<open>is_free_for A (x, \<alpha>) D\<close>]
            )
        ultimately show ?thesis
          unfolding abs_is_wff(1) by (rule rule_R[where p = "[\<guillemotright>,\<guillemotleft>]"]) force+
      next
        case False
        have "finite (vars {A, D})"
          using vars_form_finiteness and vars_form_set_finiteness by simp
        then obtain z where "(z, \<gamma>) \<notin> ({(x, \<alpha>), (y, \<gamma>)} \<union> vars {A, D})"
          using fresh_var_existence by (metis Un_insert_left finite.simps insert_is_Un)
        then have "z\<^bsub>\<gamma>\<^esub> \<noteq> x\<^bsub>\<alpha>\<^esub>" and "z\<^bsub>\<gamma>\<^esub> \<noteq> y\<^bsub>\<gamma>\<^esub>" and "(z, \<gamma>) \<notin> vars {A, D}"
          by simp_all
        then show ?thesis
        proof (cases "(x, \<alpha>) \<notin> free_vars D")
          case True
          define D' where "D' = \<^bold>S {(y, \<gamma>) \<Zinj> z\<^bsub>\<gamma>\<^esub>} D"
          have "is_substitution {(y, \<gamma>) \<Zinj> z\<^bsub>\<gamma>\<^esub>}"
            by auto
          with \<open>D \<in> wffs\<^bsub>\<delta>\<^esub>\<close> and D'_def have "D' \<in> wffs\<^bsub>\<delta>\<^esub>"
            using substitution_preserves_typing by blast
          then have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>z\<^bsub>\<gamma>\<^esub>. D') \<sqdot> A =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> \<lambda>z\<^bsub>\<gamma>\<^esub>. (\<lambda>x\<^bsub>\<alpha>\<^esub>. D') \<sqdot> A"
            using \<open>z\<^bsub>\<gamma>\<^esub> \<noteq> x\<^bsub>\<alpha>\<^esub>\<close> and \<open>(z, \<gamma>) \<notin> vars {A, D}\<close> and axiom_4_4[OF assms(1)]
            and axiom_is_derivable_from_no_hyps
            by auto
          moreover have "\<section>2": "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. D') \<sqdot> A =\<^bsub>\<delta>\<^esub> D'"
          proof -
            have "form_size D' = form_size D"
              unfolding D'_def by (fact renaming_substitution_preserves_form_size)
            then have "form_size D' < form_size B"
              using \<open>form_size D < form_size B\<close> by simp
            moreover from \<open>z\<^bsub>\<gamma>\<^esub> \<noteq> x\<^bsub>\<alpha>\<^esub>\<close> have "is_free_for A (x, \<alpha>) D'"
              unfolding D'_def and is_free_for_def
              using substitution_preserves_freeness[OF True] and is_free_at_in_free_vars
              by fast
            ultimately have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. D') \<sqdot> A =\<^bsub>\<delta>\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> A} D'"
              using less(1) and assms(1) and \<open>D' \<in> wffs\<^bsub>\<delta>\<^esub>\<close> by simp
            moreover from \<open>z\<^bsub>\<gamma>\<^esub> \<noteq> x\<^bsub>\<alpha>\<^esub>\<close> have "(x, \<alpha>) \<notin> free_vars D'"
              unfolding D'_def using substitution_preserves_freeness[OF True] by fast
            then have "\<^bold>S {(x, \<alpha>) \<Zinj> A} D' = D'"
              by (fact free_var_singleton_substitution_neutrality)
            ultimately show ?thesis
              by (simp only:)
          qed
          ultimately have "\<section>3": "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>z\<^bsub>\<gamma>\<^esub>. D') \<sqdot> A =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> \<lambda>z\<^bsub>\<gamma>\<^esub>. D'" (is \<open>\<turnstile> ?A3\<close>)
            by (rule rule_R[where p = "[\<guillemotright>,\<guillemotleft>]"]) force+
          moreover have "\<section>4": "\<turnstile> (\<lambda>y\<^bsub>\<gamma>\<^esub>. D) =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> \<lambda>z\<^bsub>\<gamma>\<^esub>. D'"
          proof -
            have "(z, \<gamma>) \<notin> free_vars D"
              using \<open>(z, \<gamma>) \<notin> vars {A, D}\<close> and free_vars_in_all_vars_set by auto
            moreover have "is_free_for (z\<^bsub>\<gamma>\<^esub>) (y, \<gamma>) D"
              using \<open>(z, \<gamma>) \<notin> vars {A, D}\<close> and absent_var_is_free_for by force
            ultimately have "\<turnstile> \<lambda>y\<^bsub>\<gamma>\<^esub>. D =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> \<lambda>z\<^bsub>\<gamma>\<^esub>. \<^bold>S {(y, \<gamma>) \<Zinj> z\<^bsub>\<gamma>\<^esub>} D"
              using "\<alpha>"[OF \<open>D \<in> wffs\<^bsub>\<delta>\<^esub>\<close>] by fast
            then show ?thesis
              using D'_def by blast
          qed
          ultimately have "\<section>5": "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>y\<^bsub>\<gamma>\<^esub>. D) \<sqdot> A =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> \<lambda>y\<^bsub>\<gamma>\<^esub>. D"
          proof -
            note rule_RR' = rule_RR[OF disjI2]
            have "\<section>5\<^sub>1": "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>y\<^bsub>\<gamma>\<^esub>. D) \<sqdot> A =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> \<lambda>z\<^bsub>\<gamma>\<^esub>. D'" (is \<open>\<turnstile> ?A5\<^sub>1\<close>)
              by (rule rule_RR'[OF "\<section>4", where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotleft>]" and C = "?A3"]) (use "\<section>3" in \<open>force+\<close>)
            show ?thesis
              by (rule rule_RR'[OF "\<section>4", where p = "[\<guillemotright>]" and C = "?A5\<^sub>1"]) (use "\<section>5\<^sub>1" in \<open>force+\<close>)
          qed
          then show ?thesis
            using free_var_singleton_substitution_neutrality[OF \<open>(x, \<alpha>) \<notin> free_vars D\<close>]
            by (simp only: \<open>\<beta> = \<gamma>\<rightarrow>\<delta>\<close>)
        next
          case False
          have "(y, \<gamma>) \<notin> free_vars A"
          proof (rule ccontr)
            assume "\<not> (y, \<gamma>) \<notin> free_vars A"
            moreover from \<open>\<not> (x, \<alpha>) \<notin> free_vars D\<close> obtain p
              where "p \<in> positions D" and "is_free_at (x, \<alpha>) p D"
              using free_vars_in_is_free_at by blast
            then have "\<guillemotleft> # p \<in> positions (\<lambda>y\<^bsub>\<gamma>\<^esub>. D)" and "is_free_at (x, \<alpha>) (\<guillemotleft> # p) (\<lambda>y\<^bsub>\<gamma>\<^esub>. D)"
              using is_free_at_to_abs[OF \<open>is_free_at (x, \<alpha>) p D\<close>] and \<open>y\<^bsub>\<gamma>\<^esub> \<noteq> x\<^bsub>\<alpha>\<^esub>\<close> by (simp, fast)
            moreover have "in_scope_of_abs (y, \<gamma>) (\<guillemotleft> # p) (\<lambda>y\<^bsub>\<gamma>\<^esub>. D)"
              by force
            ultimately have "\<not> is_free_for A (x, \<alpha>) (\<lambda>y\<^bsub>\<gamma>\<^esub>. D)"
              by blast
            with \<open>is_free_for A (x, \<alpha>) B\<close>[unfolded abs_is_wff(2)] show False
              by contradiction
          qed
          define A' where "A' = rename_bound_var (y, \<gamma>) z A"
          have "A' \<in> wffs\<^bsub>\<alpha>\<^esub>"
            unfolding A'_def by (fact rename_bound_var_preserves_typing[OF assms(1)])
          from \<open>(z, \<gamma>) \<notin> vars {A, D}\<close> have "(y, \<gamma>) \<notin> vars A'"
            using
              old_var_not_free_not_occurring_after_rename
              [
                OF assms(1) \<open>z\<^bsub>\<gamma>\<^esub> \<noteq> y\<^bsub>\<gamma>\<^esub>\<close> \<open>(y, \<gamma>) \<notin> free_vars A\<close>
              ]
            unfolding A'_def by simp
          from A'_def have "\<section>6": "\<turnstile> A =\<^bsub>\<alpha>\<^esub> A'"
            using bound_var_renaming_equality[OF assms(1) \<open>z\<^bsub>\<gamma>\<^esub> \<noteq> y\<^bsub>\<gamma>\<^esub>\<close>] and \<open>(z, \<gamma>) \<notin> vars {A, D}\<close>
            by simp
          moreover have "\<section>7": "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>y\<^bsub>\<gamma>\<^esub>. D) \<sqdot> A' =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> \<lambda>y\<^bsub>\<gamma>\<^esub>. (\<lambda>x\<^bsub>\<alpha>\<^esub>. D) \<sqdot> A'" (is \<open>\<turnstile> ?A7\<close>)
            using axiom_4_4[OF \<open>A' \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> \<open>D \<in> wffs\<^bsub>\<delta>\<^esub>\<close>]
            and \<open>(y, \<gamma>) \<notin> vars A'\<close> and \<open>y\<^bsub>\<gamma>\<^esub> \<noteq> x\<^bsub>\<alpha>\<^esub>\<close> and axiom_is_derivable_from_no_hyps
            by auto
          ultimately have "\<section>8": "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>y\<^bsub>\<gamma>\<^esub>. D) \<sqdot> A =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> \<lambda>y\<^bsub>\<gamma>\<^esub>. (\<lambda>x\<^bsub>\<alpha>\<^esub>. D) \<sqdot> A"
          proof -
            note rule_RR' = rule_RR[OF disjI2]
            have "\<section>8\<^sub>1": "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>y\<^bsub>\<gamma>\<^esub>. D) \<sqdot> A =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> \<lambda>y\<^bsub>\<gamma>\<^esub>. (\<lambda>x\<^bsub>\<alpha>\<^esub>. D) \<sqdot> A'" (is \<open>\<turnstile> ?A8\<^sub>1\<close>)
              by (rule rule_RR'[OF "\<section>6", where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]" and C = "?A7"]) (use "\<section>7" in \<open>force+\<close>)
            show ?thesis
              by (rule rule_RR'[OF "\<section>6", where p = "[\<guillemotright>,\<guillemotleft>,\<guillemotright>]" and C = "?A8\<^sub>1"]) (use "\<section>8\<^sub>1" in \<open>force+\<close>)
          qed
          moreover have "form_size D < form_size B"
            unfolding abs_is_wff(2) by (simp only: form_size.simps(4) lessI)
          with assms(1) have "\<section>9": "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. D) \<sqdot> A =\<^bsub>\<delta>\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> A} D"
            using less(1) and \<open>D \<in> wffs\<^bsub>\<delta>\<^esub>\<close> and \<open>is_free_for A (x, \<alpha>) D\<close> by (simp only:)
          ultimately show ?thesis
            unfolding \<open>\<beta> = \<gamma>\<rightarrow>\<delta>\<close> by (rule rule_R[where p = "[\<guillemotright>,\<guillemotleft>]"]) force+
        qed
      qed
      then show ?thesis
        unfolding abs_is_wff(2) using False and singleton_substitution_simps(4) by simp
    qed
  qed
qed

end

subsection \<open>Proposition 5208\<close>

proposition prop_5208:
  assumes "vs \<noteq> []" and "B \<in> wffs\<^bsub>\<beta>\<^esub>"
  shows "\<turnstile> \<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) (map FVar vs) =\<^bsub>\<beta>\<^esub> B"
using assms(1) proof (induction vs rule: list_nonempty_induct)
  case (single v)
  obtain x and \<alpha> where "v = (x, \<alpha>)"
    by fastforce
  then have "\<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> [v] B) (map FVar [v]) = (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> x\<^bsub>\<alpha>\<^esub>"
    by simp
  moreover have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> x\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> B"
  proof -
    have "is_free_for (x\<^bsub>\<alpha>\<^esub>) (x, \<alpha>) B"
      by fastforce
    then have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> x\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> x\<^bsub>\<alpha>\<^esub>} B"
      by (rule prop_5207 [OF wffs_of_type_intros(1) assms(2)])
    then show ?thesis
      using identity_singleton_substitution_neutrality by (simp only:)
  qed
  ultimately show ?case
    by (simp only:)
next
  case (cons v vs)
  obtain x and \<alpha> where "v = (x, \<alpha>)"
    by fastforce
  have "\<turnstile> \<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> (v # vs) B) (map FVar (v # vs)) =\<^bsub>\<beta>\<^esub> \<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) (map FVar vs)"
  proof -
    have "\<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> (v # vs) B) (map FVar (v # vs)) \<in> wffs\<^bsub>\<beta>\<^esub>"
    proof -
      have "\<lambda>\<^sup>\<Q>\<^sub>\<star> (v # vs) B \<in> wffs\<^bsub>foldr (\<rightarrow>) (map snd (v # vs)) \<beta>\<^esub>"
        using generalized_abs_wff [OF assms(2)] by blast
      moreover
      have "\<forall>k < length (map FVar (v # vs)). map FVar (v # vs) ! k \<in> wffs\<^bsub>map snd (v # vs) ! k\<^esub>"
      proof safe
        fix k
        assume *: "k < length (map FVar (v # vs))"
        moreover obtain x and \<alpha> where "(v # vs) ! k = (x, \<alpha>)"
          by fastforce
        with * have "map FVar (v # vs) ! k = x\<^bsub>\<alpha>\<^esub>" and "map snd (v # vs) ! k = \<alpha>"
          by (metis length_map nth_map snd_conv)+
        ultimately show "map FVar (v # vs) ! k \<in> wffs\<^bsub>map snd (v # vs) ! k\<^esub>"
          by fastforce
      qed
      ultimately show ?thesis
        using generalized_app_wff[where As = "map FVar (v # vs)" and ts = "map snd (v # vs)"] by simp
    qed
    then have "
      \<turnstile> \<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> (v # vs) B) (map FVar (v # vs)) =\<^bsub>\<beta>\<^esub> \<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> (v # vs) B) (map FVar (v # vs))"
      by (fact prop_5200)
    then have "
      \<turnstile> \<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> (v # vs) B) (map FVar (v # vs)) =\<^bsub>\<beta>\<^esub> \<sqdot>\<^sup>\<Q>\<^sub>\<star> ((\<lambda>\<^sup>\<Q>\<^sub>\<star> (v # vs) B) \<sqdot> FVar v) (map FVar vs)"
      by simp
    moreover have "\<turnstile> (\<lambda>\<^sup>\<Q>\<^sub>\<star> (v # vs) B) \<sqdot> FVar v =\<^bsub>foldr (\<rightarrow>) (map snd vs) \<beta>\<^esub> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B)"
    proof -
      have "\<turnstile> (\<lambda>\<^sup>\<Q>\<^sub>\<star> (v # vs) B) \<sqdot> FVar v =\<^bsub>foldr (\<rightarrow>) (map snd vs) \<beta>\<^esub> \<^bold>S {v \<Zinj> FVar v} (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B)"
      proof -
        from \<open>v = (x, \<alpha>)\<close> have "\<lambda>\<^sup>\<Q>\<^sub>\<star> (v # vs) B = \<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>\<^sup>\<Q>\<^sub>\<star> vs B"
          by simp
        have "\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B \<in> wffs\<^bsub>foldr (\<rightarrow>) (map snd vs) \<beta>\<^esub>"
          using generalized_abs_wff[OF assms(2)] by blast
        moreover have "is_free_for (x\<^bsub>\<alpha>\<^esub>) (x, \<alpha>) (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B)"
          by fastforce
        ultimately
        have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) \<sqdot> x\<^bsub>\<alpha>\<^esub> =\<^bsub>foldr (\<rightarrow>) (map snd vs) \<beta>\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> x\<^bsub>\<alpha>\<^esub>} \<lambda>\<^sup>\<Q>\<^sub>\<star> vs B"
          by (rule prop_5207 [OF wffs_of_type_intros(1)])
        with \<open>v = (x, \<alpha>)\<close> show ?thesis
          by simp
      qed
    then show ?thesis
      using identity_singleton_substitution_neutrality by (simp only:)
    qed
    ultimately show ?thesis
    proof (induction rule: rule_R [where p = "[\<guillemotright>] @ replicate (length vs) \<guillemotleft>"])
      case occ_subform
      then show ?case
        unfolding equality_of_type_def using leftmost_subform_in_generalized_app
        by (metis append_Cons append_Nil is_subform_at.simps(3) length_map)
    next
      case replacement
      then show ?case
        unfolding equality_of_type_def using leftmost_subform_in_generalized_app_replacement
        and is_subform_implies_in_positions and leftmost_subform_in_generalized_app
        by (metis append_Cons append_Nil length_map replace_right_app)
    qed
  qed
  moreover have "\<turnstile> \<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) (map FVar vs) =\<^bsub>\<beta>\<^esub> B"
    by (fact cons.IH)
  ultimately show ?case
    by (rule rule_R [where p = "[\<guillemotright>]"]) auto
qed

subsection \<open>Proposition 5209\<close>

proposition prop_5209:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<beta>\<^esub>" and "C \<in> wffs\<^bsub>\<beta>\<^esub>"
  and "\<turnstile> B =\<^bsub>\<beta>\<^esub> C"
  and "is_free_for A (x, \<alpha>) (B =\<^bsub>\<beta>\<^esub> C)"
  shows "\<turnstile> \<^bold>S {(x, \<alpha>) \<Zinj> A} (B =\<^bsub>\<beta>\<^esub> C)"
proof -
  have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A =\<^bsub>\<beta>\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A"
  proof -
    have "(\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A \<in> wffs\<^bsub>\<beta>\<^esub>"
      using assms(1,2) by blast
    then show ?thesis
      by (fact prop_5200)
  qed
  from this and assms(4) have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A =\<^bsub>\<beta>\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. C) \<sqdot> A"
    by (rule rule_R [where p = "[\<guillemotright>,\<guillemotleft>,\<guillemotleft>]"]) force+
  moreover have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A =\<^bsub>\<beta>\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> A} B"
  proof -
    from assms(5)[unfolded equality_of_type_def] have "is_free_for A (x, \<alpha>) (Q\<^bsub>\<beta>\<^esub> \<sqdot> B)"
      by (rule is_free_for_from_app)
    then have "is_free_for A (x, \<alpha>) B"
      by (rule is_free_for_from_app)
    with assms(1,2) show ?thesis
      by (rule prop_5207)
  qed
  moreover have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. C) \<sqdot> A =\<^bsub>\<beta>\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> A} C"
  proof -
    from assms(5)[unfolded equality_of_type_def] have "is_free_for A (x, \<alpha>) C"
      by (rule is_free_for_from_app)
    with assms(1,3) show ?thesis
      by (rule prop_5207)
  qed
  ultimately have "\<turnstile> (\<^bold>S {(x, \<alpha>) \<Zinj> A} B) =\<^bsub>\<beta>\<^esub> (\<^bold>S {(x, \<alpha>) \<Zinj> A} C)"
    using Equality_Rules(2,3) by blast
  then show ?thesis
    by simp
qed

subsection \<open>Proposition 5210\<close>

proposition prop_5210:
  assumes "B \<in> wffs\<^bsub>\<beta>\<^esub>"
  shows "\<turnstile> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> (B =\<^bsub>\<beta>\<^esub> B)"
proof -
  have "\<section>1": "
    \<turnstile>
      ((\<lambda>\<yy>\<^bsub>\<beta>\<^esub>. \<yy>\<^bsub>\<beta>\<^esub>) =\<^bsub>\<beta>\<rightarrow>\<beta>\<^esub> (\<lambda>\<yy>\<^bsub>\<beta>\<^esub>. \<yy>\<^bsub>\<beta>\<^esub>))
      =\<^bsub>o\<^esub>
      \<forall>\<xx>\<^bsub>\<beta>\<^esub>. ((\<lambda>\<yy>\<^bsub>\<beta>\<^esub>. \<yy>\<^bsub>\<beta>\<^esub>) \<sqdot> \<xx>\<^bsub>\<beta>\<^esub> =\<^bsub>\<beta>\<^esub> (\<lambda>\<yy>\<^bsub>\<beta>\<^esub>. \<yy>\<^bsub>\<beta>\<^esub>) \<sqdot> \<xx>\<^bsub>\<beta>\<^esub>)"
  proof -
    have "\<turnstile> (\<ff>\<^bsub>\<beta>\<rightarrow>\<beta>\<^esub> =\<^bsub>\<beta>\<rightarrow>\<beta>\<^esub> \<gg>\<^bsub>\<beta>\<rightarrow>\<beta>\<^esub>) =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>\<beta>\<^esub>. (\<ff>\<^bsub>\<beta>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<beta>\<^esub> =\<^bsub>\<beta>\<^esub> \<gg>\<^bsub>\<beta>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<beta>\<^esub>)" (is "\<turnstile> ?B =\<^bsub>o\<^esub> ?C")
      using axiom_3[unfolded equivalence_def] by (rule axiom_is_derivable_from_no_hyps)
    moreover have "(\<lambda>\<yy>\<^bsub>\<beta>\<^esub>. \<yy>\<^bsub>\<beta>\<^esub>) \<in> wffs\<^bsub>\<beta>\<rightarrow>\<beta>\<^esub>" and "?B \<in> wffs\<^bsub>o\<^esub>" and "?C \<in> wffs\<^bsub>o\<^esub>"
      by auto
    moreover have "is_free_for (\<lambda>\<yy>\<^bsub>\<beta>\<^esub>. \<yy>\<^bsub>\<beta>\<^esub>) (\<ff>, \<beta>\<rightarrow>\<beta>) (?B =\<^bsub>o\<^esub> ?C)"
      by simp
    ultimately have "\<turnstile> \<^bold>S {(\<ff>, \<beta>\<rightarrow>\<beta>) \<Zinj> (\<lambda>\<yy>\<^bsub>\<beta>\<^esub>. \<yy>\<^bsub>\<beta>\<^esub>)} (?B =\<^bsub>o\<^esub> ?C)" (is "\<turnstile> ?S")
      using prop_5209 by presburger
    moreover have "?S =
      (
        (\<lambda>\<yy>\<^bsub>\<beta>\<^esub>. \<yy>\<^bsub>\<beta>\<^esub>) =\<^bsub>\<beta>\<rightarrow>\<beta>\<^esub> \<gg>\<^bsub>\<beta>\<rightarrow>\<beta>\<^esub>) =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>\<beta>\<^esub>. ((\<lambda>\<yy>\<^bsub>\<beta>\<^esub>. \<yy>\<^bsub>\<beta>\<^esub>) \<sqdot> \<xx>\<^bsub>\<beta>\<^esub> =\<^bsub>\<beta>\<^esub> \<gg>\<^bsub>\<beta>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<beta>\<^esub>
      )" (is "_ = ?B' =\<^bsub>o\<^esub> ?C'")
      by simp
    ultimately have "\<turnstile> ?B' =\<^bsub>o\<^esub> ?C'"
      by (simp only:)
    moreover from \<open>(\<lambda>\<yy>\<^bsub>\<beta>\<^esub>. \<yy>\<^bsub>\<beta>\<^esub>) \<in> wffs\<^bsub>\<beta>\<rightarrow>\<beta>\<^esub>\<close> have "?B' \<in> wffs\<^bsub>o\<^esub>" and "?C' \<in> wffs\<^bsub>o\<^esub>"
      by auto
    moreover have "is_free_for (\<lambda>\<yy>\<^bsub>\<beta>\<^esub>. \<yy>\<^bsub>\<beta>\<^esub>) (\<gg>, \<beta>\<rightarrow>\<beta>) (?B' =\<^bsub>o\<^esub> ?C')"
      by simp
    ultimately have "\<turnstile> \<^bold>S {(\<gg>, \<beta>\<rightarrow>\<beta>) \<Zinj> (\<lambda>\<yy>\<^bsub>\<beta>\<^esub>. \<yy>\<^bsub>\<beta>\<^esub>)} (?B' =\<^bsub>o\<^esub> ?C')" (is "\<turnstile> ?S'")
      using prop_5209[OF \<open>(\<lambda>\<yy>\<^bsub>\<beta>\<^esub>. \<yy>\<^bsub>\<beta>\<^esub>) \<in> wffs\<^bsub>\<beta>\<rightarrow>\<beta>\<^esub>\<close>] by blast
    then show ?thesis
      by simp
  qed
  then have "\<turnstile> (\<lambda>\<xx>\<^bsub>\<beta>\<^esub>. T\<^bsub>o\<^esub>) =\<^bsub>\<beta>\<rightarrow>o\<^esub> (\<lambda>\<xx>\<^bsub>\<beta>\<^esub>. (\<xx>\<^bsub>\<beta>\<^esub> =\<^bsub>\<beta>\<^esub> \<xx>\<^bsub>\<beta>\<^esub>))"
  proof -
    have "\<lambda>\<yy>\<^bsub>\<beta>\<^esub>. \<yy>\<^bsub>\<beta>\<^esub> \<in> wffs\<^bsub>\<beta>\<rightarrow>\<beta>\<^esub>"
      by blast
    then have "\<turnstile> \<lambda>\<yy>\<^bsub>\<beta>\<^esub>. \<yy>\<^bsub>\<beta>\<^esub> =\<^bsub>\<beta>\<rightarrow>\<beta>\<^esub> \<lambda>\<yy>\<^bsub>\<beta>\<^esub>. \<yy>\<^bsub>\<beta>\<^esub>"
      by (fact prop_5200)
    with "\<section>1" have "\<turnstile> \<forall>\<xx>\<^bsub>\<beta>\<^esub>. ((\<lambda>\<yy>\<^bsub>\<beta>\<^esub>. \<yy>\<^bsub>\<beta>\<^esub>) \<sqdot> \<xx>\<^bsub>\<beta>\<^esub> =\<^bsub>\<beta>\<^esub> (\<lambda>\<yy>\<^bsub>\<beta>\<^esub>. \<yy>\<^bsub>\<beta>\<^esub>) \<sqdot> \<xx>\<^bsub>\<beta>\<^esub>)"
      using rule_R and is_subform_at.simps(1) by blast
    moreover have "\<turnstile> (\<lambda>\<yy>\<^bsub>\<beta>\<^esub>. \<yy>\<^bsub>\<beta>\<^esub>) \<sqdot> \<xx>\<^bsub>\<beta>\<^esub> =\<^bsub>\<beta>\<^esub> \<xx>\<^bsub>\<beta>\<^esub>"
      using axiom_4_2[OF wffs_of_type_intros(1)] by (rule axiom_is_derivable_from_no_hyps)
    ultimately have "\<turnstile> \<forall>\<xx>\<^bsub>\<beta>\<^esub>. (\<xx>\<^bsub>\<beta>\<^esub> =\<^bsub>\<beta>\<^esub> (\<lambda>\<yy>\<^bsub>\<beta>\<^esub>. \<yy>\<^bsub>\<beta>\<^esub>) \<sqdot> \<xx>\<^bsub>\<beta>\<^esub>)"
      by (rule rule_R[where p = "[\<guillemotright>,\<guillemotleft>,\<guillemotleft>,\<guillemotright>]"]) auto
    from this and \<open>\<turnstile> (\<lambda>\<yy>\<^bsub>\<beta>\<^esub>. \<yy>\<^bsub>\<beta>\<^esub>) \<sqdot> \<xx>\<^bsub>\<beta>\<^esub> =\<^bsub>\<beta>\<^esub> \<xx>\<^bsub>\<beta>\<^esub>\<close> have "\<turnstile> \<forall>\<xx>\<^bsub>\<beta>\<^esub>. (\<xx>\<^bsub>\<beta>\<^esub> =\<^bsub>\<beta>\<^esub> \<xx>\<^bsub>\<beta>\<^esub>)"
      by (rule rule_R[where p = "[\<guillemotright>,\<guillemotleft>,\<guillemotright>]"]) auto
    then show ?thesis
      unfolding forall_def and PI_def by (fold equality_of_type_def)
  qed
  from this and assms have 3: "\<turnstile> (\<lambda>\<xx>\<^bsub>\<beta>\<^esub>. T\<^bsub>o\<^esub>) \<sqdot> B =\<^bsub>o\<^esub> (\<lambda>\<xx>\<^bsub>\<beta>\<^esub>. (\<xx>\<^bsub>\<beta>\<^esub> =\<^bsub>\<beta>\<^esub> \<xx>\<^bsub>\<beta>\<^esub>)) \<sqdot> B"
    by (rule Equality_Rules(5))
  then show ?thesis
  proof -
    have "\<turnstile> (\<lambda>\<xx>\<^bsub>\<beta>\<^esub>. T\<^bsub>o\<^esub>) \<sqdot> B =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
      using prop_5207[OF assms true_wff] by fastforce
    from 3 and this have "\<turnstile> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> (\<lambda>\<xx>\<^bsub>\<beta>\<^esub>. (\<xx>\<^bsub>\<beta>\<^esub> =\<^bsub>\<beta>\<^esub> \<xx>\<^bsub>\<beta>\<^esub>)) \<sqdot> B"
      by (rule rule_R[where p = "[\<guillemotleft>,\<guillemotright>]"]) auto
    moreover have "\<turnstile> (\<lambda>\<xx>\<^bsub>\<beta>\<^esub>. (\<xx>\<^bsub>\<beta>\<^esub> =\<^bsub>\<beta>\<^esub> \<xx>\<^bsub>\<beta>\<^esub>)) \<sqdot> B =\<^bsub>o\<^esub> (B =\<^bsub>\<beta>\<^esub> B)"
    proof -
      have "\<xx>\<^bsub>\<beta>\<^esub> =\<^bsub>\<beta>\<^esub> \<xx>\<^bsub>\<beta>\<^esub> \<in> wffs\<^bsub>o\<^esub>" and "is_free_for B (\<xx>, \<beta>) (\<xx>\<^bsub>\<beta>\<^esub> =\<^bsub>\<beta>\<^esub> \<xx>\<^bsub>\<beta>\<^esub>)"
        by (blast, intro is_free_for_in_equality is_free_for_in_var)
      moreover have "\<^bold>S {(\<xx>, \<beta>) \<Zinj> B} (\<xx>\<^bsub>\<beta>\<^esub> =\<^bsub>\<beta>\<^esub> \<xx>\<^bsub>\<beta>\<^esub>) = (B =\<^bsub>\<beta>\<^esub> B)"
        by simp
      ultimately show ?thesis
        using prop_5207[OF assms] by metis
    qed
    ultimately show ?thesis
      by (rule rule_R [where p = "[\<guillemotright>]"]) auto
  qed
qed

subsection \<open>Proposition 5211\<close>

proposition prop_5211:
  shows "\<turnstile> (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
proof -
  have const_T_wff: "(\<lambda>x\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>" for x
   by blast
  have "\<section>1": "\<turnstile> (\<lambda>\<yy>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) \<sqdot> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> (\<lambda>\<yy>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) \<sqdot> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. (\<lambda>\<yy>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) \<sqdot> \<xx>\<^bsub>o\<^esub>"
  proof -
    have "\<turnstile> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>" (is "\<turnstile> ?B =\<^bsub>o\<^esub> ?C")
      using axiom_1[unfolded equivalence_def] by (rule axiom_is_derivable_from_no_hyps)
    moreover have "?B \<in> wffs\<^bsub>o\<^esub>" and "?C \<in> wffs\<^bsub>o\<^esub>"
      by auto
    moreover have "is_free_for (\<lambda>\<yy>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) (\<gg>, o\<rightarrow>o) (?B =\<^bsub>o\<^esub> ?C)"
      by simp
    ultimately have "\<turnstile> \<^bold>S {(\<gg>, o\<rightarrow>o) \<Zinj> (\<lambda>\<yy>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>)} (?B =\<^bsub>o\<^esub> ?C)"
      using const_T_wff and prop_5209 by presburger
    then show ?thesis
      by simp
  qed
  then have "\<turnstile> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>"
  proof -
    have T_\<beta>_redex: "\<turnstile> (\<lambda>\<yy>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) \<sqdot> A =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" if "A \<in> wffs\<^bsub>o\<^esub>" for A
      using that and prop_5207[OF that true_wff] by fastforce
    from "\<section>1" and T_\<beta>_redex[OF true_wff]
    have "\<turnstile> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> (\<lambda>\<yy>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) \<sqdot> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. (\<lambda>\<yy>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) \<sqdot> \<xx>\<^bsub>o\<^esub>"
      by (rule rule_R[where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]"]) force+
    from this and T_\<beta>_redex[OF false_wff] have "\<turnstile> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. (\<lambda>\<yy>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) \<sqdot> \<xx>\<^bsub>o\<^esub>"
      by (rule rule_R[where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]"]) force+
    from this and T_\<beta>_redex[OF wffs_of_type_intros(1)] show ?thesis
      by (rule rule_R[where p = "[\<guillemotright>,\<guillemotright>,\<guillemotleft>]"]) force+
  qed
  moreover have "\<turnstile> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>"
    using prop_5210[OF const_T_wff] by simp
  ultimately show ?thesis
    using Equality_Rules(2,3) by blast
qed

lemma true_is_derivable:
  shows "\<turnstile> T\<^bsub>o\<^esub>"
  unfolding true_def using Q_wff by (rule prop_5200)

subsection \<open>Proposition 5212\<close>

proposition prop_5212:
  shows "\<turnstile> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> T\<^bsub>o\<^esub>"
proof -
  have "\<turnstile> T\<^bsub>o\<^esub>"
    by (fact true_is_derivable)
  moreover have "\<turnstile> (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
    by (fact prop_5211)
  then have "\<turnstile> T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> T\<^bsub>o\<^esub>)"
    unfolding equivalence_def by (fact Equality_Rules(2))
  ultimately show ?thesis
    by (rule Equality_Rules(1))
qed

subsection \<open>Proposition 5213\<close>

proposition prop_5213:
  assumes "\<turnstile> A =\<^bsub>\<alpha>\<^esub> B" and "\<turnstile> C =\<^bsub>\<beta>\<^esub> D"
  shows "\<turnstile> (A =\<^bsub>\<alpha>\<^esub> B) \<and>\<^sup>\<Q> (C =\<^bsub>\<beta>\<^esub> D)"
proof -
  from assms have "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "C \<in> wffs\<^bsub>\<beta>\<^esub>"
    using hyp_derivable_form_is_wffso and wffs_from_equality by blast+
  have "\<turnstile> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> (A =\<^bsub>\<alpha>\<^esub> A)"
    by (fact prop_5210[OF \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close>])
  moreover have "\<turnstile> A =\<^bsub>\<alpha>\<^esub> B"
    by fact
  ultimately have "\<turnstile> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> (A =\<^bsub>\<alpha>\<^esub> B)"
    by (rule rule_R[where p = "[\<guillemotright>,\<guillemotright>]"]) force+
  have "\<turnstile> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> (C =\<^bsub>\<beta>\<^esub> C)"
    by (fact prop_5210[OF \<open>C \<in> wffs\<^bsub>\<beta>\<^esub>\<close>])
  moreover have "\<turnstile> C =\<^bsub>\<beta>\<^esub> D"
    by fact
  ultimately have "\<turnstile> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> (C =\<^bsub>\<beta>\<^esub> D)"
    by (rule rule_R[where p = "[\<guillemotright>,\<guillemotright>]"]) force+
  then show ?thesis
  proof -
    have "\<turnstile> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> T\<^bsub>o\<^esub>"
      by (fact prop_5212)
    from this and \<open>\<turnstile> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> (A =\<^bsub>\<alpha>\<^esub> B)\<close> have "\<turnstile> (A =\<^bsub>\<alpha>\<^esub> B) \<and>\<^sup>\<Q> T\<^bsub>o\<^esub>"
      by (rule rule_R[where p = "[\<guillemotleft>,\<guillemotright>]"]) force+
    from this and \<open>\<turnstile> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> (C =\<^bsub>\<beta>\<^esub> D)\<close> show ?thesis
      by (rule rule_R[where p = "[\<guillemotright>]"]) force+
  qed
qed

subsection \<open>Proposition 5214\<close>

proposition prop_5214:
  shows "\<turnstile> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
proof -
  have id_on_o_is_wff: "(\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>) \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>"
    by blast
  have "\<section>1": "\<turnstile> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>) \<sqdot> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>) \<sqdot> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. (\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>) \<sqdot> \<xx>\<^bsub>o\<^esub>"
  proof -
    have "\<turnstile> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>" (is "\<turnstile> ?B =\<^bsub>o\<^esub> ?C")
      using axiom_1[unfolded equivalence_def] by (rule axiom_is_derivable_from_no_hyps)
    moreover have "?B \<in> wffs\<^bsub>o\<^esub>" and "?C \<in> wffs\<^bsub>o\<^esub>" and "is_free_for (\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>) (\<gg>, o\<rightarrow>o) (?B =\<^bsub>o\<^esub> ?C)"
      by auto
    ultimately have "\<turnstile> \<^bold>S {(\<gg>, o\<rightarrow>o) \<Zinj> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>)} (?B =\<^bsub>o\<^esub> ?C)"
      using id_on_o_is_wff and prop_5209 by presburger
    then show ?thesis
      by simp
  qed
  then have "\<turnstile> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>"
  proof -
    have id_\<beta>_redex: "\<turnstile> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>) \<sqdot> A =\<^bsub>o\<^esub> A" if "A \<in> wffs\<^bsub>o\<^esub>" for A
      by (fact axiom_is_derivable_from_no_hyps[OF axiom_4_2[OF that]])
    from "\<section>1" and id_\<beta>_redex[OF true_wff]
    have "\<turnstile> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>) \<sqdot> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. (\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>) \<sqdot> \<xx>\<^bsub>o\<^esub>"
      by (rule rule_R[where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]"]) force+
    from this and id_\<beta>_redex[OF false_wff] have "\<turnstile> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. (\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>) \<sqdot> \<xx>\<^bsub>o\<^esub>"
      by (rule rule_R[where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]"]) force+
    from this and id_\<beta>_redex[OF wffs_of_type_intros(1)] show ?thesis
      by (rule rule_R[where p = "[\<guillemotright>,\<guillemotright>,\<guillemotleft>]"]) force+
  qed
  then show ?thesis
    by simp
qed

subsection \<open>Proposition 5215 (Universal Instantiation)\<close>

proposition prop_5215:
  assumes "\<H> \<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. B" and "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  and "is_free_for A (x, \<alpha>) B"
  shows "\<H> \<turnstile> \<^bold>S {(x, \<alpha>) \<Zinj> A} B"
proof -
  from assms(1) have "is_hyps \<H>"
    by (blast elim: is_derivable_from_hyps.cases)
  from assms(1) have "\<H> \<turnstile> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) =\<^bsub>\<alpha>\<rightarrow>o\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)"
    by simp
  with assms(2) have "\<H> \<turnstile> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) \<sqdot> A =\<^bsub>o\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A"
    by (intro Equality_Rules(5))
  then have "\<H> \<turnstile> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> A} B"
  proof -
    have "\<H> \<turnstile> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) \<sqdot> A =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
    proof -
      have "\<turnstile> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) \<sqdot> A =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        using prop_5207[OF assms(2) true_wff is_free_for_in_true] and derived_substitution_simps(1)
        by (simp only:)
      from this and \<open>is_hyps \<H>\<close> show ?thesis
        by (rule derivability_implies_hyp_derivability)
    qed
    moreover have "\<H> \<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A =\<^bsub>o\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> A} B"
    proof -
      have "B \<in> wffs\<^bsub>o\<^esub>"
        using hyp_derivable_form_is_wffso[OF assms(1)] by (fastforce elim: wffs_from_forall)
      with assms(2,3) have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A =\<^bsub>o\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> A} B"
        using prop_5207 by (simp only:)
      from this and \<open>is_hyps \<H>\<close> show ?thesis
        by (rule derivability_implies_hyp_derivability)
    qed
    ultimately show ?thesis
      using \<open>\<H> \<turnstile> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) \<sqdot> A =\<^bsub>o\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A\<close> and Equality_Rules(2,3) by meson
  qed
  then show ?thesis
  proof -
    have "\<H> \<turnstile> T\<^bsub>o\<^esub>"
      by (fact derivability_implies_hyp_derivability[OF true_is_derivable \<open>is_hyps \<H>\<close>])
    from this and \<open>\<H> \<turnstile> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> A} B\<close> show ?thesis
      by (rule Equality_Rules(1)[unfolded equivalence_def])
  qed
qed

lemmas "\<forall>I" = prop_5215 (* synonym *)

subsection \<open>Proposition 5216\<close>

proposition prop_5216:
  assumes "A \<in> wffs\<^bsub>o\<^esub>"
  shows "\<turnstile> (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> A) =\<^bsub>o\<^esub> A"
proof -
  let ?B = "\<lambda>\<xx>\<^bsub>o\<^esub>. (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>)"
  have B_is_wff: "?B \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>"
    by auto
  have "\<section>1": "\<turnstile> ?B \<sqdot> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> ?B \<sqdot> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. ?B \<sqdot> \<xx>\<^bsub>o\<^esub>"
  proof -
    have "\<turnstile> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>" (is "\<turnstile> ?C =\<^bsub>o\<^esub> ?D")
      using axiom_1[unfolded equivalence_def] by (rule axiom_is_derivable_from_no_hyps)
    moreover have "?C \<in> wffs\<^bsub>o\<^esub>" and "?D \<in> wffs\<^bsub>o\<^esub>" and "is_free_for ?B (\<gg>, o\<rightarrow>o) (?C =\<^bsub>o\<^esub> ?D)"
      by auto
    ultimately have "\<turnstile> \<^bold>S {(\<gg>, o\<rightarrow>o) \<Zinj> ?B} (?C =\<^bsub>o\<^esub> ?D)"
      using B_is_wff and prop_5209 by presburger
    then show ?thesis
      by simp
  qed
  have *: "is_free_for A (\<xx>, o) (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>)" for A
    by (intro is_free_for_in_conj is_free_for_in_equality is_free_for_in_true is_free_for_in_var)
  have "\<turnstile> (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>) \<and>\<^sup>\<Q> (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>)"
    by (fact prop_5213[OF prop_5211 prop_5214])
  moreover
  have "\<turnstile> (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>) \<and>\<^sup>\<Q> (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>)"
  proof -
    have B_\<beta>_redex: "\<turnstile> ?B \<sqdot> A =\<^bsub>o\<^esub> (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> A =\<^bsub>o\<^esub> A)" if "A \<in> wffs\<^bsub>o\<^esub>" for A
    proof -
      have "T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<^esub>"
        by blast
      moreover have "\<^bold>S {(\<xx>, o) \<Zinj> A} (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>) = (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> A =\<^bsub>o\<^esub> A)"
        by simp
      ultimately show ?thesis
        using * and prop_5207[OF that] by metis
    qed
    from "\<section>1" and B_\<beta>_redex[OF true_wff]
    have "\<turnstile> (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>) \<and>\<^sup>\<Q> ?B \<sqdot> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. ?B \<sqdot> \<xx>\<^bsub>o\<^esub>"
      by (rule rule_R[where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]"]) force+
    from this and B_\<beta>_redex[OF false_wff]
    have "\<turnstile> (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>) \<and>\<^sup>\<Q> (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. ?B \<sqdot> \<xx>\<^bsub>o\<^esub>"
      by (rule rule_R[where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]"]) force+
    from this and B_\<beta>_redex[OF wffs_of_type_intros(1)] show ?thesis
      by (rule rule_R[where p = "[\<guillemotright>,\<guillemotright>,\<guillemotleft>]"]) force+
  qed
  ultimately have "\<turnstile> \<forall>\<xx>\<^bsub>o\<^esub>. (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>)"
    by (rule rule_R[where p = "[]"]) fastforce+
  show ?thesis
    using "\<forall>I"[OF \<open>\<turnstile> \<forall>\<xx>\<^bsub>o\<^esub>. (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>)\<close> assms *] by simp
qed

subsection \<open>Proposition 5217\<close>

proposition prop_5217:
  shows "\<turnstile> (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
proof -
  let ?B = "\<lambda>\<xx>\<^bsub>o\<^esub>. (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>)"
  have B_is_wff: "?B \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>"
    by auto
  have *: "is_free_for A (\<xx>, o) (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>)" for A
    by (intro is_free_for_in_equality is_free_for_in_true is_free_for_in_var)
  have "\<section>1": "\<turnstile> ?B \<sqdot> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> ?B \<sqdot> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. ?B \<sqdot> \<xx>\<^bsub>o\<^esub>"
  proof -
    have "\<turnstile> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>" (is "\<turnstile> ?C =\<^bsub>o\<^esub> ?D")
      using axiom_1[unfolded equivalence_def] by (rule axiom_is_derivable_from_no_hyps)
    moreover have "?C \<in> wffs\<^bsub>o\<^esub>" and "?D \<in> wffs\<^bsub>o\<^esub>" and "is_free_for ?B (\<gg>, o\<rightarrow>o) (?C =\<^bsub>o\<^esub> ?D)"
      by auto
    ultimately have "\<turnstile> \<^bold>S {(\<gg>, o\<rightarrow>o) \<Zinj> ?B} (?C =\<^bsub>o\<^esub> ?D)"
      using B_is_wff and prop_5209 by presburger
    then show ?thesis
      by simp
  qed
  then have "\<turnstile> (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>) \<and>\<^sup>\<Q> (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>)" (is "\<turnstile> ?A")
  proof -
    have B_\<beta>_redex: "\<turnstile> ?B \<sqdot> A =\<^bsub>o\<^esub> (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> A)" if "A \<in> wffs\<^bsub>o\<^esub>" for A
    proof -
      have "T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<^esub>"
        by auto
      moreover have "\<^bold>S {(\<xx>, o) \<Zinj> A} (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>) = (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> A)"
        by simp
      ultimately show ?thesis
        using * and prop_5207[OF that] by metis
    qed
    from "\<section>1" and B_\<beta>_redex[OF true_wff] have "\<turnstile> (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>) \<and>\<^sup>\<Q> ?B \<sqdot> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. ?B \<sqdot> \<xx>\<^bsub>o\<^esub>"
      by (rule rule_R[where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]"]) force+
    from this and B_\<beta>_redex[OF false_wff]
    have "\<turnstile> (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>) \<and>\<^sup>\<Q> (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. ?B \<sqdot> \<xx>\<^bsub>o\<^esub>"
      by (rule rule_R[where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]"]) force+
    from this and B_\<beta>_redex[OF wffs_of_type_intros(1)] show ?thesis
      by (rule rule_R[where p = "[\<guillemotright>,\<guillemotright>,\<guillemotleft>]"]) force+
  qed
  from prop_5210[OF true_wff] have "\<turnstile> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>)"
    by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]" and C = ?A]) (force+, fact)
  from this and prop_5216[where A = "T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"]
  have "\<turnstile> (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>)"
    by (rule rule_R [where p = "[\<guillemotleft>,\<guillemotright>]"]) force+
  moreover have "\<section>5": "
    \<turnstile> ((\<lambda>\<xx>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) =\<^bsub>o\<rightarrow>o\<^esub> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>)) =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. ((\<lambda>\<xx>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) \<sqdot> \<xx>\<^bsub>o\<^esub> =\<^bsub>o\<^esub> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>) \<sqdot> \<xx>\<^bsub>o\<^esub>)"
  proof -
    have "\<turnstile> (\<ff>\<^bsub>o\<rightarrow>o\<^esub> =\<^bsub>o\<rightarrow>o\<^esub> \<gg>\<^bsub>o\<rightarrow>o\<^esub>) =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. (\<ff>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>)" (is "\<turnstile> ?C =\<^bsub>o\<^esub> ?D")
      using axiom_3[unfolded equivalence_def] by (rule axiom_is_derivable_from_no_hyps)
    moreover have "is_free_for ((\<lambda>\<xx>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>)) (\<ff>, o\<rightarrow>o) (?C =\<^bsub>o\<^esub> ?D)"
      by fastforce
    moreover have "(\<lambda>\<xx>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>" and "?C \<in> wffs\<^bsub>o\<^esub>" and "?D \<in> wffs\<^bsub>o\<^esub>"
      by auto
    ultimately have "\<turnstile> \<^bold>S {(\<ff>, o\<rightarrow>o) \<Zinj> (\<lambda>\<xx>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>)} (?C =\<^bsub>o\<^esub> ?D)"
      using prop_5209 by presburger
    then have "\<turnstile> ((\<lambda>\<xx>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) =\<^bsub>o\<rightarrow>o\<^esub> \<gg>\<^bsub>o\<rightarrow>o\<^esub>) =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. ((\<lambda>\<xx>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) \<sqdot> \<xx>\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>)"
      (is "\<turnstile> ?C' =\<^bsub>o\<^esub> ?D'")
      by simp
    moreover have "is_free_for ((\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>)) (\<gg>, o\<rightarrow>o) (?C' =\<^bsub>o\<^esub> ?D')"
      by fastforce
    moreover have "(\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>) \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>" and "?C' \<in> wffs\<^bsub>o\<^esub>" and "?D' \<in> wffs\<^bsub>o\<^esub>"
      using \<open>(\<lambda>\<xx>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>\<close> by auto
    ultimately have "\<turnstile> \<^bold>S {(\<gg>, o\<rightarrow>o) \<Zinj> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>)} (?C' =\<^bsub>o\<^esub> ?D')"
      using prop_5209 by presburger
    then show ?thesis
      by simp
  qed
  then have "\<turnstile> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>)"
  proof -
    have "\<turnstile> (\<lambda>\<xx>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) \<sqdot> \<xx>\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
      using prop_5208[where vs = "[(\<xx>, o)]"] and true_wff by simp
    with "\<section>5" have *: "
      \<turnstile> ((\<lambda>\<xx>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) =\<^bsub>o\<rightarrow>o\<^esub> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>)) =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>) \<sqdot> \<xx>\<^bsub>o\<^esub>)"
      by (rule rule_R[where p = "[\<guillemotright>,\<guillemotright>,\<guillemotleft>,\<guillemotleft>,\<guillemotright>]"]) force+
    have "\<turnstile> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>) \<sqdot> \<xx>\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>"
      using prop_5208[where vs = "[(\<xx>, o)]"] by fastforce
    with * have "\<turnstile> ((\<lambda>\<xx>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) =\<^bsub>o\<rightarrow>o\<^esub> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>)) =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>)"
      by (rule rule_R[where p = "[\<guillemotright>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]"]) force+
    then show ?thesis
      by simp
  qed
  ultimately show ?thesis
    using Equality_Rules(2,3) by blast
qed

subsection \<open>Proposition 5218\<close>

proposition prop_5218:
  assumes "A \<in> wffs\<^bsub>o\<^esub>"
  shows "\<turnstile> (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> A) =\<^bsub>o\<^esub> A"
proof -
  let ?B = "\<lambda>\<xx>\<^bsub>o\<^esub>. ((T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>)"
  have B_is_wff: "?B \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>"
    by auto
  have "\<section>1": "\<turnstile> ?B \<sqdot> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> ?B \<sqdot> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. ?B \<sqdot> \<xx>\<^bsub>o\<^esub>"
  proof -
    have "\<turnstile> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>" (is "\<turnstile> ?C =\<^bsub>o\<^esub> ?D")
      using axiom_1[unfolded equivalence_def] by (rule axiom_is_derivable_from_no_hyps)
    moreover have "?C \<in> wffs\<^bsub>o\<^esub>" and "?D \<in> wffs\<^bsub>o\<^esub>" and "is_free_for ?B (\<gg>, o\<rightarrow>o) (?C =\<^bsub>o\<^esub> ?D)"
      by auto
    ultimately have "\<turnstile> \<^bold>S {(\<gg>, o\<rightarrow>o) \<Zinj> ?B} (?C =\<^bsub>o\<^esub> ?D)"
      using prop_5209[OF B_is_wff] by presburger
    then show ?thesis
      by simp
  qed
  have *: "is_free_for A (\<xx>, o) ((T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>)" for A
    by (intro is_free_for_in_equality is_free_for_in_true is_free_for_in_var)
  have "\<section>2": "
    \<turnstile>
      ((T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>) \<and>\<^sup>\<Q> ((T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>)
      =\<^bsub>o\<^esub>
      \<forall>\<xx>\<^bsub>o\<^esub>. ((T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>)"
  proof -
    have B_\<beta>_redex: "\<turnstile> ?B \<sqdot> A =\<^bsub>o\<^esub> ((T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> A) =\<^bsub>o\<^esub> A)" if "A \<in> wffs\<^bsub>o\<^esub>" for A
    proof -
      have "(T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<^esub>"
        by auto
      moreover have "\<^bold>S {(\<xx>, o) \<Zinj> A} ((T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>) = ((T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> A) =\<^bsub>o\<^esub> A)"
        by simp
      ultimately show ?thesis
        using * and prop_5207[OF that] by metis
    qed
    from "\<section>1" and B_\<beta>_redex[OF true_wff]
    have "\<turnstile> ((T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>) \<and>\<^sup>\<Q> ?B \<sqdot> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. ?B \<sqdot> \<xx>\<^bsub>o\<^esub>"
      by (rule rule_R[where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]"]) force+
    from this and B_\<beta>_redex[OF false_wff]
    have "\<turnstile> ((T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>) \<and>\<^sup>\<Q> ((T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. ?B \<sqdot> \<xx>\<^bsub>o\<^esub>"
      by (rule rule_R[where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]"]) force+
    from this and B_\<beta>_redex[OF wffs_of_type_intros(1)] show ?thesis
      by (rule rule_R[where p = "[\<guillemotright>,\<guillemotright>,\<guillemotleft>]"]) force+
  qed
  have "\<section>3": "\<turnstile> (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
    by (fact Equality_Rules(2)[OF prop_5210 [OF true_wff]])
  have "\<turnstile> ((T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>) \<and>\<^sup>\<Q> ((T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>)"
    by (fact prop_5213[OF "\<section>3" prop_5217])
  from this and "\<section>2" have "\<section>4": "\<turnstile> \<forall>\<xx>\<^bsub>o\<^esub>. ((T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> \<xx>\<^bsub>o\<^esub>)"
    by (rule rule_R[where p = "[]"]) fastforce+
  then show ?thesis
    using "\<forall>I"[OF "\<section>4" assms *] by simp
qed

subsection \<open>Proposition 5219 (Rule T)\<close>

proposition prop_5219_1:
  assumes "A \<in> wffs\<^bsub>o\<^esub>"
  shows "\<H> \<turnstile> A \<longleftrightarrow> \<H> \<turnstile> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> A"
proof safe
  assume "\<H> \<turnstile> A"
  then have "is_hyps \<H>"
    by (blast dest: is_derivable_from_hyps.cases)
  then have "\<H> \<turnstile> (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> A) =\<^bsub>o\<^esub> A"
    by (fact derivability_implies_hyp_derivability[OF prop_5218[OF assms]])
  with \<open>\<H> \<turnstile> A\<close> show "\<H> \<turnstile> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> A"
    using Equality_Rules(1)[unfolded equivalence_def] and Equality_Rules(2) by blast
next
  assume "\<H> \<turnstile> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> A"
  then have "is_hyps \<H>"
    by (blast dest: is_derivable_from_hyps.cases)
  then have "\<H> \<turnstile> (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> A) =\<^bsub>o\<^esub> A"
    by (fact derivability_implies_hyp_derivability[OF prop_5218[OF assms]])
  with \<open>\<H> \<turnstile> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> A\<close> show "\<H> \<turnstile> A"
    by (rule Equality_Rules(1)[unfolded equivalence_def])
qed

proposition prop_5219_2:
  assumes "A \<in> wffs\<^bsub>o\<^esub>"
  shows "\<H> \<turnstile> A \<longleftrightarrow> \<H> \<turnstile> A =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
  using prop_5219_1[OF assms] and Equality_Rules(2) by blast

lemmas rule_T = prop_5219_1 prop_5219_2

subsection \<open>Proposition 5220 (Universal Generalization)\<close>

context
begin

private lemma const_true_\<alpha>_conversion:
  shows "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) =\<^bsub>\<alpha>\<rightarrow>o\<^esub> (\<lambda>z\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>)"
proof -
  have "(z, \<alpha>) \<notin> free_vars T\<^bsub>o\<^esub>" and "is_free_for (z\<^bsub>\<alpha>\<^esub>) (x, \<alpha>) T\<^bsub>o\<^esub>"
    by auto
  then have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) =\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<lambda>z\<^bsub>\<alpha>\<^esub>. \<^bold>S {(x, \<alpha>) \<Zinj> z\<^bsub>\<alpha>\<^esub>} T\<^bsub>o\<^esub>"
    by (rule prop_5206[OF true_wff])
  then show ?thesis
    by simp
qed

proposition prop_5220:
  assumes "\<H> \<turnstile> A"
  and "(x, \<alpha>) \<notin> free_vars \<H>"
  shows "\<H> \<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. A"
proof -
  from \<open>\<H> \<turnstile> A\<close> have "is_hyps \<H>"
    by (blast dest: is_derivable_from_hyps.cases)
  have "\<H> \<turnstile> A"
    by fact
  then have "\<section>2": "\<H> \<turnstile> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> A"
    using rule_T(1)[OF hyp_derivable_form_is_wffso[OF \<open>\<H> \<turnstile> A\<close>]] by simp
  have "\<section>3": "\<H> \<turnstile> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) =\<^bsub>\<alpha>\<rightarrow>o\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>)"
    by (fact derivability_implies_hyp_derivability[OF const_true_\<alpha>_conversion \<open>is_hyps \<H>\<close>])
  from "\<section>3" and "\<section>2" have "\<H> \<turnstile> \<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub> =\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<lambda>x\<^bsub>\<alpha>\<^esub>. A"
  proof (induction rule: rule_R'[where p = "[\<guillemotright>, \<guillemotleft>]"])
    case no_capture
    have *: "[\<guillemotright>,\<guillemotleft>] \<in> positions (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub> =\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<lambda>x\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>)"
      by simp
    show ?case
      unfolding rule_R'_side_condition_def and capture_exposed_vars_at_alt_def[OF *] using assms(2)
      by simp
  qed force+
  then show ?thesis
    unfolding forall_def[unfolded PI_def, folded equality_of_type_def] .
qed

end

lemmas Gen = prop_5220 (* synonym *)

proposition generalized_Gen:
  assumes "\<H> \<turnstile> A"
  and "lset vs \<inter> free_vars \<H> = {}"
  shows "\<H> \<turnstile> \<forall>\<^sup>\<Q>\<^sub>\<star> vs A"
using assms(2) proof (induction vs)
  case Nil
  then show ?case
    using assms(1) by simp
next
  case (Cons v vs)
  obtain x and \<alpha> where "v = (x, \<alpha>)"
    by fastforce
  with Cons.prems have "lset vs \<inter> free_vars \<H> = {}" and "(x, \<alpha>) \<notin> free_vars \<H>"
    by simp_all
  from \<open>lset vs \<inter> free_vars \<H> = {}\<close> have "\<H> \<turnstile> \<forall>\<^sup>\<Q>\<^sub>\<star> vs A"
    by (fact Cons.IH)
  with \<open>(x, \<alpha>) \<notin> free_vars \<H>\<close> and \<open>v = (x, \<alpha>)\<close> show ?case
    using Gen by simp
qed

subsection \<open>Proposition 5221 (Substitution)\<close>

context
begin

private lemma prop_5221_aux:
  assumes "\<H> \<turnstile> B"
  and "(x, \<alpha>) \<notin> free_vars \<H>"
  and "is_free_for A (x, \<alpha>) B"
  and "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows "\<H> \<turnstile> \<^bold>S {(x, \<alpha>) \<Zinj> A} B"
proof -
  have "\<H> \<turnstile> B"
    by fact
  from this and assms(2) have "\<H> \<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. B"
    by (rule Gen)
  from this and assms(4,3) show ?thesis
    by (rule "\<forall>I")
qed

proposition prop_5221:
  assumes "\<H> \<turnstile> B"
  and "is_substitution \<theta>"
  and "\<forall>v \<in> fmdom' \<theta>. var_name v \<notin> free_var_names \<H> \<and> is_free_for (\<theta> $$! v) v B"
  and "\<theta> \<noteq> {$$}"
  shows "\<H> \<turnstile> \<^bold>S \<theta> B"
proof -
  obtain xs and As
    where "lset xs = fmdom' \<theta>" \<comment> \<open>i.e., $x^1_{\alpha_1},\dots,x^n_{\alpha_n}$\<close>
    and "As = map (($$!) \<theta>) xs" \<comment> \<open>i.e., $A^1_{\alpha_1},\dots,A^n_{\alpha_n}$\<close>
    and "length xs = card (fmdom' \<theta>)"
    by (metis distinct_card finite_distinct_list finite_fmdom')
  then have "distinct xs"
    by (simp add: card_distinct)
  from \<open>lset xs = fmdom' \<theta>\<close> and \<open>As = map (($$!) \<theta>) xs\<close> have "lset As = fmran' \<theta>"
    by (intro subset_antisym subsetI) (force simp add: fmlookup_dom'_iff fmlookup_ran'_iff)+
  from assms(1) have "finite (var_name ` (vars B \<union> vars (lset As) \<union> vars \<H>))"
    by (cases rule: is_derivable_from_hyps.cases) (simp_all add: finite_Domain vars_form_finiteness)
  then obtain ys \<comment> \<open>i.e., $y^1_{\alpha_1},\dots,y^n_{\alpha_n}$\<close>
    where "length ys = length xs"
    and "distinct ys"
    and ys_fresh: "
      (var_name ` lset ys) \<inter> (var_name ` (vars B \<union> vars (lset As) \<union> vars \<H> \<union> lset xs)) = {}"
    and "map var_type ys = map var_type xs"
    using fresh_var_list_existence by (metis image_Un)
  have "length xs = length As"
    by (simp add: \<open>As = map (($$!) \<theta>) xs\<close>)
  \<comment> \<open>$\mathcal{H}\;\vdash\;\d{\textsf{S}}\;
      ^{x^1_{\alpha_1}\;\dots\;x^k_{\alpha_k} x^{k+1}_{\alpha_{k+1}}\;\dots\;x^n_{\alpha_n}}
      _{A^1_{\alpha_1}\;\dots\;A^k_{\alpha_k} y^{k+1}_{\alpha_{k+1}}\;\dots\;y^n_{\alpha_n}} B$\<close>
  have "\<H> \<turnstile> \<^bold>S (fmap_of_list (zip xs (take k As @ drop k (map FVar ys)))) B" if "k \<le> length xs" for k
  using that proof (induction k)
    case 0
    have "\<H> \<turnstile> \<^bold>S (fmap_of_list (zip xs (map FVar ys))) B"
      using \<open>length ys = length xs\<close>
      and \<open>length xs = length As\<close>
      and \<open>(var_name ` lset ys) \<inter> (var_name ` (vars B \<union> vars (lset As) \<union> vars \<H> \<union> lset xs)) = {}\<close>
      and \<open>lset xs = fmdom' \<theta>\<close>
      and \<open>distinct ys\<close>
      and assms(3)
      and \<open>map var_type ys = map var_type xs\<close>
      and \<open>distinct xs\<close>
      and \<open>length xs = card (fmdom' \<theta>)\<close>
    proof (induction ys xs As arbitrary: \<theta> rule: list_induct3)
      case Nil
      with assms(1) show ?case
        using empty_substitution_neutrality by auto
    next
      \<comment> \<open>In the following:
        \begin{itemize}
        \item $\vartheta =
          \{x^1_{\alpha_1} \rightarrowtail y^1_{\alpha_1},\dots,x^n_{\alpha_n} \rightarrowtail y^n_{\alpha_n}\}$
        \item \emph?$\vartheta =
          \{x^2_{\alpha_2} \rightarrowtail y^2_{\alpha_2},\dots,x^n_{\alpha_n} \rightarrowtail y^n_{\alpha_n}\}$
        \item $v_x = x^1_{\alpha_1}$, and $v_y = y^1_{\alpha_1}$
        \end{itemize}
      \<close>
      case (Cons v\<^sub>y ys v\<^sub>x xs A' As')
      let ?\<theta> = "fmap_of_list (zip xs (map FVar ys))"
      from Cons.hyps(1) have "lset xs = fmdom' ?\<theta>"
        by simp
      from Cons.hyps(1) and Cons.prems(6) have "fmran' ?\<theta> = FVar ` lset ys"
        by force
      have "is_substitution ?\<theta>"
      unfolding is_substitution_def proof
        fix v
        assume "v \<in> fmdom' ?\<theta>"
        with \<open>lset xs = fmdom' ?\<theta>\<close> obtain k where "v = xs ! k" and "k < length xs"
          by (metis in_set_conv_nth)
        moreover obtain \<alpha> where "var_type v = \<alpha>"
          by blast
        moreover from \<open>k < length xs\<close> and \<open>v = xs ! k\<close> have "?\<theta> $$! v = (map FVar ys) ! k"
          using Cons.hyps(1) and Cons.prems(6) by auto
        moreover from this and \<open>k < length xs\<close> obtain y and \<beta> where "?\<theta> $$! v = y\<^bsub>\<beta>\<^esub>"
          using Cons.hyps(1) by force
        ultimately have "\<alpha> = \<beta>"
          using Cons.hyps(1) and Cons.prems(5)
          by (metis form.inject(1) list.inject list.simps(9) nth_map snd_conv)
        then show "case v of (x, \<alpha>) \<Rightarrow> ?\<theta> $$! (x, \<alpha>) \<in> wffs\<^bsub>\<alpha>\<^esub>"
          using \<open>?\<theta> $$! v = y\<^bsub>\<beta>\<^esub>\<close> and \<open>var_type v = \<alpha>\<close> by fastforce
      qed
      have "v\<^sub>x \<notin> fmdom' ?\<theta>"
        using Cons.prems(6) and \<open>lset xs = fmdom' ?\<theta>\<close> by auto
      obtain x and \<alpha> where "v\<^sub>x = (x, \<alpha>)"
        by fastforce
      have "FVar v\<^sub>y \<in> wffs\<^bsub>\<alpha>\<^esub>"
        using Cons.prems(5) and surj_pair[of v\<^sub>y] unfolding \<open>v\<^sub>x = (x, \<alpha>)\<close> by fastforce
      have "distinct xs"
        using Cons.prems(6) by fastforce
      moreover have ys_fresh': "
        (var_name ` lset ys) \<inter> (var_name ` (vars B \<union> vars (lset As') \<union> vars \<H> \<union> lset xs)) = {}"
      proof -
        have "vars (lset (A' # As')) = vars {A'} \<union> vars (lset As')"
          by simp
        moreover have "var_name ` (lset (v\<^sub>x # xs)) = {var_name v\<^sub>x} \<union> var_name ` (lset xs)"
          by simp
        moreover from Cons.prems(1) have "
          var_name ` lset ys
          \<inter>
          (
            var_name ` (vars B) \<union> var_name ` (vars (lset (A' # As'))) \<union> var_name ` (vars \<H>)
            \<union> var_name ` (lset (v\<^sub>x # xs))
          )
          = {}"
          by (simp add: image_Un)
        ultimately have "
          var_name ` lset ys
          \<inter>
          (
            var_name ` (vars B) \<union> var_name ` (vars (lset As')) \<union> var_name ` (vars \<H>)
            \<union> var_name ` (lset (v\<^sub>x # xs))
          )
          = {}"
          by fast
        then show ?thesis
          by (simp add: image_Un)
      qed
      moreover have "distinct ys"
        using Cons.prems(3) by auto
      moreover have "\<forall>v \<in> fmdom' ?\<theta>. var_name v \<notin> free_var_names \<H> \<and> is_free_for (?\<theta> $$! v) v B"
      proof
        fix v
        assume "v \<in> fmdom' ?\<theta>"
        with Cons.hyps(1) obtain y where "?\<theta> $$! v = FVar y" and "y \<in> lset ys"
          by (metis (mono_tags, lifting) fmap_of_zipped_list_range image_iff length_map list.set_map)
        moreover from Cons.prems(2,4) have "var_name v \<notin> free_var_names \<H>"
          using \<open>lset xs = fmdom' ?\<theta>\<close> and \<open>v \<in> fmdom' ?\<theta>\<close> by auto
        moreover from \<open>y \<in> lset ys\<close> have "y \<notin> vars B"
          using ys_fresh' by blast
        then have "is_free_for (FVar y) v B"
          by (intro absent_var_is_free_for)
        ultimately show "var_name v \<notin> free_var_names \<H> \<and> is_free_for (?\<theta> $$! v) v B"
          by simp
      qed
      moreover have "map var_type ys = map var_type xs"
        using Cons.prems(5) by simp
      moreover have "length xs = card (fmdom' ?\<theta>)"
        by (fact distinct_card[OF \<open>distinct xs\<close>, unfolded \<open>lset xs = fmdom' ?\<theta>\<close>, symmetric])
      \<comment> \<open>$\mathcal{H}\;\vdash\;\d{\textsf{S}}\;
          ^{x^2_{\alpha_2}\;\dots\;x^n_{\alpha_n}}
          _{y^2_{\alpha_2}\;\dots\;y^n_{\alpha_n}} B$\<close>
      ultimately have "\<H> \<turnstile> \<^bold>S ?\<theta> B"
        using Cons.IH and \<open>lset xs = fmdom' ?\<theta>\<close> by blast
      moreover from Cons.prems(2,4) have "(x, \<alpha>) \<notin> free_vars \<H>"
        using \<open>v\<^sub>x = (x, \<alpha>)\<close> by auto
      moreover have "is_free_for (FVar v\<^sub>y) (x, \<alpha>) (\<^bold>S ?\<theta> B)"
      proof -
        have "v\<^sub>y \<notin> fmdom' ?\<theta>"
          using Cons.prems(1) and \<open>lset xs = fmdom' ?\<theta>\<close> by force
        moreover have "fmran' ?\<theta> = lset (map FVar ys)"
          using Cons.hyps(1) and \<open>distinct xs\<close> by simp
        then have "v\<^sub>y \<notin> vars (fmran' ?\<theta>)"
          using Cons.prems(3) by force
        moreover have "v\<^sub>y \<notin> vars B"
          using Cons.prems(1) by fastforce
        ultimately have "v\<^sub>y \<notin> vars (\<^bold>S ?\<theta> B)"
          by (rule excluded_var_from_substitution[OF \<open>is_substitution ?\<theta>\<close>])
        then show ?thesis
          by (fact absent_var_is_free_for)
      qed
      \<comment> \<open>$\mathcal{H}\;\vdash\;\d{\textsf{S}}\;^{x^1_{\alpha_1}}_{y^1_{\alpha_1}}\;\d{\textsf{S}}\;
          ^{x^2_{\alpha_2}\;\dots\;x^n_{\alpha_n}}_{y^2_{\alpha_2}\;\dots\;y^n_{\alpha_n}} B$\<close>
      ultimately have "\<H> \<turnstile> \<^bold>S {(x, \<alpha>) \<Zinj> FVar v\<^sub>y} (\<^bold>S ?\<theta> B)"
        using \<open>FVar v\<^sub>y \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> by (rule prop_5221_aux)
      \<comment> \<open>$\d{\textsf{S}}\;^{x^1_{\alpha_1}}_{y^1_{\alpha_1}}\;\d{\textsf{S}}\;
          ^{x^2_{\alpha_2}\;\dots\;x^n_{\alpha_n}}_{y^2_{\alpha_2}\;\dots\;y^n_{\alpha_n}} B =
          \d{\textsf{S}}\;^{x^1_{\alpha_1}\;\dots\;x^n_{\alpha_n}}_{y^1_{\alpha_1}\;\dots\;y^n_{\alpha_n}} B$\<close>
      moreover have "\<^bold>S {v\<^sub>x \<Zinj> FVar v\<^sub>y} \<^bold>S ?\<theta> B = \<^bold>S ({v\<^sub>x \<Zinj> FVar v\<^sub>y} ++\<^sub>f ?\<theta>) B"
      proof -
        have "v\<^sub>x \<notin> lset ys"
          using Cons.prems(1) by fastforce
        then have "\<^bold>S {v\<^sub>x \<Zinj> FVar v\<^sub>y} (FVar y) = FVar y" if "y \<in> lset ys" for y
          using that and free_var_singleton_substitution_neutrality and surj_pair[of y] by fastforce
        with \<open>fmran' ?\<theta> = FVar ` lset ys\<close> have "fmmap (\<lambda>A'. \<^bold>S {v\<^sub>x \<Zinj> FVar v\<^sub>y} A') ?\<theta> = ?\<theta>"
          by (fastforce intro: fmap.map_ident_strong)
        with \<open>v\<^sub>x \<notin> fmdom' ?\<theta>\<close> show ?thesis
          using \<open>\<forall>v \<in> fmdom' ?\<theta>. var_name v \<notin> free_var_names \<H> \<and> is_free_for (?\<theta> $$! v) v B\<close>
          and substitution_consolidation by auto
      qed
      \<comment> \<open>$\mathcal{H}\;\vdash\;\d{\textsf{S}}\;
          ^{x^1_{\alpha_1}\;\dots\;x^n_{\alpha_n}}_{y^1_{\alpha_1}\;\dots\;y^n_{\alpha_n}} B$\<close>
      ultimately show ?case
        using \<open>v\<^sub>x = (x, \<alpha>)\<close> and \<open>v\<^sub>x \<notin> fmdom' ?\<theta>\<close> and fmap_singleton_comm by fastforce
    qed
    with 0 and that show ?case
      by auto
  next
    case (Suc k)
    let ?ps = "\<lambda>k. zip xs (take k As @ drop k (map FVar ys))"
    let ?y = "ys ! k" and ?A = "As ! k"
    let ?\<theta> = "\<lambda>k. fmap_of_list (?ps k)"
    let ?\<theta>' = "\<lambda>k. fmap_of_list (map (\<lambda>(v', A'). (v', \<^bold>S {?y \<Zinj> ?A} A')) (?ps k))"
    have "fmdom' (?\<theta> k') = lset xs" for k'
      by (simp add: \<open>length xs = length As\<close> \<open>length ys = length xs\<close>)
    have "fmdom' (?\<theta>' k') = lset xs" for k'
      using \<open>length xs = length As\<close> and \<open>length ys = length xs\<close> and fmdom'_fmap_of_list by simp
    have "?y \<in> lset ys"
      using Suc.prems \<open>length ys = length xs\<close> by simp
    have "\<forall>j < length ys. ys ! j \<notin> vars (\<H>::form set) \<and> ys ! j \<notin> vars B"
      using \<open>(var_name ` lset ys) \<inter> (var_name ` (vars B \<union> vars (lset As) \<union> vars \<H> \<union> lset xs)) = {}\<close>
      by force
    obtain n\<^sub>y and \<alpha>\<^sub>y where "(n\<^sub>y, \<alpha>\<^sub>y) = ?y"
      using surj_pair[of ?y] by fastforce
    moreover have "?A \<in> wffs\<^bsub>\<alpha>\<^sub>y\<^esub>"
    proof -
      from Suc.prems and \<open>(n\<^sub>y, \<alpha>\<^sub>y) = ?y\<close> have "var_type (xs ! k) = \<alpha>\<^sub>y"
        using \<open>length ys = length xs\<close> and \<open>map var_type ys = map var_type xs\<close> and Suc_le_lessD
        by (metis nth_map snd_conv)
      with Suc.prems and assms(2) and \<open>lset xs = fmdom' \<theta>\<close> and \<open>As = map (($$!) \<theta>) xs\<close> show ?thesis
        using less_eq_Suc_le and nth_mem by fastforce
    qed
    ultimately have "is_substitution {?y \<Zinj> ?A}"
      by auto
    have wfs: "is_substitution (?\<theta> k)" for k
    unfolding is_substitution_def proof
      fix v
      assume "v \<in> fmdom' (?\<theta> k)"
      with \<open>fmdom' (?\<theta> k) = lset xs\<close> obtain j where "v = xs ! j" and "j < length xs"
        by (fastforce simp add: in_set_conv_nth)
      obtain \<alpha> where "var_type v = \<alpha>"
        by blast
      show "case v of (x, \<alpha>) \<Rightarrow> (?\<theta> k) $$! (x, \<alpha>) \<in> wffs\<^bsub>\<alpha>\<^esub>"
      proof (cases "j < k")
        case True
        with \<open>j < length xs\<close> and \<open>v = xs ! j\<close> have "(?\<theta> k) $$! v = As ! j"
          using \<open>distinct xs\<close> and \<open>length xs = length As\<close> and \<open>length ys = length xs\<close> by force
        with assms(2) \<open>v = xs ! j\<close> and \<open>v \<in> fmdom' (?\<theta> k)\<close> and \<open>var_type v = \<alpha>\<close> and \<open>j < length xs\<close>
        have "(?\<theta> k) $$! v \<in> wffs\<^bsub>\<alpha>\<^esub>"
          using \<open>As = map (($$!) \<theta>) xs\<close> and \<open>fmdom' (?\<theta> k) = lset xs\<close> and \<open>lset xs = fmdom' \<theta>\<close>
          by auto
        then show ?thesis
          using \<open>var_type v = \<alpha>\<close> by force
      next
        case False
        with \<open>j < length xs\<close> and \<open>v = xs ! j\<close> have "(?\<theta> k) $$! v = FVar (ys ! j)"
          using \<open>distinct xs\<close> and \<open>length xs = length As\<close> and \<open>length ys = length xs\<close> by force
        with \<open>j < length xs\<close> and \<open>v = xs ! j\<close> and \<open>var_type v = \<alpha>\<close> and \<open>length ys = length xs\<close>
        have "(?\<theta> k) $$! v \<in> wffs\<^bsub>\<alpha>\<^esub>"
          using \<open>map var_type ys = map var_type xs\<close> and surj_pair[of "ys ! j"]
          by (metis nth_map snd_conv wffs_of_type_intros(1))
        then show ?thesis
          using \<open>var_type v = \<alpha>\<close> by force
      qed
    qed
    have \<theta>'_alt_def: "?\<theta>' k = fmap_of_list
      (zip xs
        (take k (map (\<lambda>A'. \<^bold>S {?y \<Zinj> ?A} A') As)
        @
        (drop k (map (\<lambda>A'. \<^bold>S {?y \<Zinj> ?A} A') (map FVar ys)))))"
    proof -
      have "
        fmap_of_list (zip xs (map (\<lambda>A'. \<^bold>S {?y \<Zinj> ?A} A') (take k As @ drop k (map FVar ys))))
        =
        fmap_of_list
          (zip xs
            (map (\<lambda>A'. \<^bold>S {?y \<Zinj> ?A} A') (take k As)
            @
            (drop k (map (\<lambda>A'. \<^bold>S {?y \<Zinj> ?A} A') (map FVar ys)))))"
        by (simp add: drop_map)
      then show ?thesis
        by (metis take_map zip_map2)
    qed
    \<comment> \<open>$\mathcal{H}\;\vdash\;\d{\textsf{S}}\;
        ^{x^1_{\alpha_1}\;\dots\;x^k_{\alpha_k} x^{k+1}_{\alpha_{k+1}}\;\dots\;x^n_{\alpha_n}}
        _{A^1_{\alpha_1}\;\dots\;A^k_{\alpha_k} y^{k+1}_{\alpha_{k+1}}\;\dots\;y^n_{\alpha_n}} B$\<close>
    have "\<H> \<turnstile> \<^bold>S (?\<theta> k) B"
      by (fact Suc.IH[OF Suc_leD[OF Suc.prems]])
    \<comment> \<open>$\mathcal{H}\;\vdash\;\d{\textsf{S}}\;^{y^{k+1}_{\alpha_{k+1}}}_{A^{k+1}_{\alpha_{k+1}}}\;
        \d{\textsf{S}}\;
        ^{x^1_{\alpha_1}\;\dots\;x^k_{\alpha_k} x^{k+1}_{\alpha_{k+1}}\;\dots\;x^n_{\alpha_n}}
        _{A^1_{\alpha_1}\;\dots\;A^k_{\alpha_k} y^{k+1}_{\alpha_{k+1}}\;\dots\;y^n_{\alpha_n}} B$\<close>
    then have "\<H> \<turnstile> \<^bold>S {?y \<Zinj> ?A} \<^bold>S (?\<theta> k) B"
    proof -
      from \<open>(n\<^sub>y, \<alpha>\<^sub>y) = ?y\<close> and \<open>length ys = length xs\<close> have "(n\<^sub>y, \<alpha>\<^sub>y) \<notin> free_vars \<H>"
        using \<open>\<forall>j < length ys. ys ! j \<notin> vars (\<H>::form set) \<and> ys ! j \<notin> vars B\<close>
        and free_vars_in_all_vars_set and Suc_le_lessD[OF Suc.prems] by fastforce
      moreover have "is_free_for ?A (n\<^sub>y, \<alpha>\<^sub>y) (\<^bold>S (?\<theta> k) B)"
      proof -
        have "is_substitution (fmdrop (xs ! k) (?\<theta> k))"
          using wfs and \<open>fmdom' (?\<theta> k) = lset xs\<close> by force
        moreover from Suc_le_lessD[OF Suc.prems] have "var_type (xs ! k) = var_type (ys ! k)"
          using \<open>length ys = length xs\<close> and \<open>map var_type ys = map var_type xs\<close> by (metis nth_map)
        then have "is_substitution {xs ! k \<Zinj> FVar ?y}"
          unfolding is_substitution_def using \<open>(n\<^sub>y, \<alpha>\<^sub>y) = ?y\<close>
          by (intro ballI) (clarsimp, metis snd_eqD wffs_of_type_intros(1))
        moreover have "(xs ! k) \<notin> fmdom' (fmdrop (xs ! k) (?\<theta> k))"
          by simp
        moreover have "
          \<forall>v \<in> fmdom' (fmdrop (xs ! k) (?\<theta> k)). ?y \<notin> vars (fmdrop (xs ! k) (?\<theta> k) $$! v)"
        proof
          fix v
          assume "v \<in> fmdom' (fmdrop (xs ! k) (?\<theta> k))"
          then have "v \<in> fmdom' (?\<theta> k)"
            by simp
          with \<open>fmdom' (?\<theta> k) = lset xs\<close> obtain j where "v = xs ! j" and "j < length xs" and "j \<noteq> k"
            using \<open>v \<in> fmdom' (fmdrop (xs ! k) (?\<theta> k))\<close>
            and \<open>(xs ! k) \<notin> fmdom' (fmdrop (xs ! k) (?\<theta> k))\<close> by (metis in_set_conv_nth)
          then show "?y \<notin> vars ((fmdrop (xs ! k) (?\<theta> k)) $$! v)"
          proof (cases "j < k")
            case True
            with \<open>j < length xs\<close> and \<open>v = xs ! j\<close> have "(?\<theta> k) $$! v = As ! j"
              using \<open>distinct xs\<close> and \<open>length xs = length As\<close> and \<open>length ys = length xs\<close> by force
            moreover from \<open>j < length xs\<close> and \<open>length xs = length As\<close> have "?y \<notin> vars (As ! j)"
              using \<open>?y \<in> lset ys\<close> and ys_fresh by fastforce
            ultimately show ?thesis
              using \<open>v \<in> fmdom' (fmdrop (xs ! k) (?\<theta> k))\<close> by auto
          next
            case False
            with \<open>j < length xs\<close> and \<open>v = xs ! j\<close> have "(?\<theta> k) $$! v = FVar (ys ! j)"
              using \<open>distinct xs\<close> and \<open>length xs = length As\<close> and \<open>length ys = length xs\<close> by force
            moreover from Suc_le_lessD[OF Suc.prems] and \<open>j \<noteq> k\<close> have "?y \<noteq> ys ! j"
              by (simp add: \<open>distinct ys\<close> \<open>j < length xs\<close> \<open>length ys = length xs\<close> nth_eq_iff_index_eq)
            ultimately show ?thesis
              using \<open>v \<in> fmdom' (fmdrop (xs ! k) (?\<theta> k))\<close>
              and \<open>xs ! k \<notin> fmdom' (fmdrop (xs ! k) (?\<theta> k))\<close> and surj_pair[of "ys ! j"] by fastforce
          qed
        qed
        moreover from \<open>k < length xs\<close> and \<open>length ys = length xs\<close> have "?y \<notin> vars B"
          by (simp add: \<open>\<forall>j < length ys. ys ! j \<notin> vars \<H> \<and> ys ! j \<notin> vars B\<close>)
        moreover have "is_free_for ?A (xs ! k) B"
        proof -
          from Suc_le_lessD[OF Suc.prems] and \<open>lset xs = fmdom' \<theta>\<close> have "xs ! k \<in> fmdom' \<theta>"
            using nth_mem by blast
          moreover from Suc.prems and \<open>As = map (($$!) \<theta>) xs\<close> have "\<theta> $$! (xs ! k) = ?A"
            by fastforce
          ultimately show ?thesis
            using assms(3) by simp
        qed
        moreover
        have "\<forall>v \<in> fmdom' (fmdrop (xs ! k) (?\<theta> k)). is_free_for (fmdrop (xs ! k) (?\<theta> k) $$! v) v B"
        proof
          fix v
          assume "v \<in> fmdom' (fmdrop (xs ! k) (?\<theta> k))"
          then have "v \<in> fmdom' (?\<theta> k)"
            by simp
          with \<open>fmdom' (?\<theta> k) = lset xs\<close> obtain j where "v = xs ! j" and "j < length xs" and "j \<noteq> k"
            using \<open>v \<in> fmdom' (fmdrop (xs ! k) (?\<theta> k))\<close>
            and \<open>(xs ! k) \<notin> fmdom' (fmdrop (xs ! k) (?\<theta> k))\<close> by (metis in_set_conv_nth)
          then show "is_free_for (fmdrop (xs ! k) (?\<theta> k) $$! v) v B"
          proof (cases "j < k")
            case True
            with \<open>j < length xs\<close> and \<open>v = xs ! j\<close> have "(?\<theta> k) $$! v = As ! j"
              using \<open>distinct xs\<close> and \<open>length xs = length As\<close> and \<open>length ys = length xs\<close> by force
            moreover have "is_free_for (As ! j) v B"
            proof -
              from \<open>j < length xs\<close> and \<open>lset xs = fmdom' \<theta>\<close> and \<open>v = xs ! j\<close> have "v \<in> fmdom' \<theta>"
                using nth_mem by blast
              moreover have "\<theta> $$! v = As ! j"
                by (simp add: \<open>As = map (($$!) \<theta>) xs\<close> \<open>j < length xs\<close> \<open>v = xs ! j\<close>)
              ultimately show ?thesis
                using assms(3) by simp
              qed
            ultimately show ?thesis
              using \<open>v \<in> fmdom' (fmdrop (xs ! k) (?\<theta> k))\<close> by auto
          next
            case False
            with \<open>j < length xs\<close> and \<open>v = xs ! j\<close> have "(?\<theta> k) $$! v = FVar (ys ! j)"
              using \<open>distinct xs\<close> and \<open>length xs = length As\<close> and \<open>length ys = length xs\<close> by force
            moreover from \<open>j < length xs\<close> and \<open>length ys = length xs\<close> have "ys ! j \<notin> vars B"
              using \<open>\<forall>j < length ys. ys ! j \<notin> vars \<H> \<and> ys ! j \<notin> vars B\<close> by simp
            then have "is_free_for (FVar (ys ! j)) v B"
              by (fact absent_var_is_free_for)
            ultimately show ?thesis
              using \<open>v \<in> fmdom' (fmdrop (xs ! k) (?\<theta> k))\<close> by auto
          qed
        qed
        ultimately have "is_free_for ?A (ys ! k) \<^bold>S ({xs ! k \<Zinj> FVar ?y} ++\<^sub>f fmdrop (xs ! k) (?\<theta> k)) B"
          using is_free_for_with_renaming_substitution by presburger
        moreover have "\<^bold>S ({xs ! k \<Zinj> FVar ?y} ++\<^sub>f fmdrop (xs ! k) (?\<theta> k)) B = \<^bold>S (?\<theta> k) B"
          using \<open>length xs = length As\<close> and \<open>length ys = length xs\<close> and Suc_le_eq and Suc.prems
          and \<open>distinct xs\<close> by simp
        ultimately show ?thesis
          unfolding \<open>(n\<^sub>y, \<alpha>\<^sub>y) = ?y\<close> by simp
      qed
      ultimately show ?thesis
        using prop_5221_aux[OF \<open>\<H> \<turnstile> \<^bold>S (?\<theta> k) B\<close>] and \<open>?A \<in> wffs\<^bsub>\<alpha>\<^sub>y\<^esub>\<close> and \<open>(n\<^sub>y, \<alpha>\<^sub>y) = ?y\<close> by metis
    qed
    \<comment> \<open>$\d{\textsf{S}}\;^{y^{k+1}_{\alpha_{k+1}}}_{A^{k+1}_{\alpha_{k+1}}}\;
        \d{\textsf{S}}\;
        ^{x^1_{\alpha_1}\;\dots\;x^k_{\alpha_k} x^{k+1}_{\alpha_{k+1}}\;\dots\;x^n_{\alpha_n}}
        _{A^1_{\alpha_1}\;\dots\;A^k_{\alpha_k} y^{k+1}_{\alpha_{k+1}}\;\dots\;y^n_{\alpha_n}} B =
        \d{\textsf{S}}\;
        ^{x^1_{\alpha_1}\;\dots\;x^k_{\alpha_k} x^{k+1}_{\alpha_{k+1}} x^{k+2}_{\alpha_{k+2}}
         \;\dots\;x^n_{\alpha_n}}
        _{A^1_{\alpha_1}\;\dots\;A^k_{\alpha_k} A^{k+1}_{\alpha_{k+1}} y^{k+2}_{\alpha_{k+2}}
         \;\dots\;y^n_{\alpha_n}} B$\<close>
    moreover have "\<^bold>S {?y \<Zinj> ?A} \<^bold>S (?\<theta> k) B = \<^bold>S (?\<theta> (Suc k)) B"
    proof -
      have "\<^bold>S {?y \<Zinj> ?A} \<^bold>S (?\<theta> k) B = \<^bold>S {?y \<Zinj> ?A} ++\<^sub>f (?\<theta>' k) B"
      proof -
        have "?y \<notin> fmdom' (?\<theta> k)"
          using \<open>?y \<in> lset ys\<close> and \<open>fmdom' (?\<theta> k) = lset xs\<close> and ys_fresh by blast
        moreover have "(?\<theta>' k) = fmmap (\<lambda>A'. \<^bold>S {?y \<Zinj> ?A} A') (?\<theta> k)"
          using \<open>length xs = length As\<close> and \<open>length ys = length xs\<close> by simp
        moreover have "\<forall>v' \<in> fmdom' (?\<theta> k). is_free_for (?\<theta> k $$! v') v' B"
        proof
          fix v'
          assume "v' \<in> fmdom' (?\<theta> k)"
          with \<open>fmdom' (?\<theta> k) = lset xs\<close> obtain j where "v' = xs ! j" and "j < length xs"
            by (metis in_set_conv_nth)
          obtain \<alpha> where "var_type v' = \<alpha>"
            by blast
          show "is_free_for (?\<theta> k $$! v') v' B"
          proof (cases "j < k")
            case True
            with \<open>j < length xs\<close> and \<open>v' = xs ! j\<close> have "(?\<theta> k) $$! v' = As ! j"
              using \<open>distinct xs\<close> and \<open>length xs = length As\<close> and \<open>length ys = length xs\<close> by force
            moreover from \<open>lset xs = fmdom' \<theta>\<close> and assms(3) have "is_free_for (As ! j) (xs ! j) B"
              by (metis \<open>As = map (($$!) \<theta>) xs\<close> \<open>j < length xs\<close> nth_map nth_mem)
            ultimately show ?thesis
              using \<open>v' = xs ! j\<close> by (simp only:)
          next
            case False
            with \<open>j < length xs\<close> and \<open>v' = xs ! j\<close> have "(?\<theta> k) $$! v' = FVar (ys ! j)"
              using \<open>distinct xs\<close> and \<open>length xs = length As\<close> and \<open>length ys = length xs\<close> by force
            moreover from \<open>j < length xs\<close> have "is_free_for (FVar (ys ! j)) (xs ! j) B"
              using \<open>\<forall>j < length ys. ys ! j \<notin> vars \<H> \<and> ys ! j \<notin> vars B\<close> and \<open>length ys = length xs\<close>
              and absent_var_is_free_for by presburger
            ultimately show ?thesis
              using \<open>v' = xs ! j\<close> by (simp only:)
          qed
        qed
        ultimately show ?thesis
          using substitution_consolidation by simp
      qed
      also have "\<dots> = \<^bold>S {?y \<Zinj> ?A} ++\<^sub>f (?\<theta> (Suc k)) B"
      proof -
        have "?\<theta>' k = ?\<theta> (Suc k)"
        proof (intro fsubset_antisym[unfolded fmsubset_alt_def] fmpredI)
          {
            fix v' and A'
            assume "?\<theta>' k $$ v' = Some A'"
            then have "v' \<in> fmdom' (?\<theta>' k)"
              by (intro fmdom'I)
            then obtain j where "j < length xs" and "xs ! j = v'"
              using \<open>fmdom' (?\<theta>' k) = lset xs\<close> by (metis in_set_conv_nth)
            then consider (a) "j < k" | (b) "j = k" | (c) "j \<in> {k<..< length xs}"
              by fastforce
            then show "?\<theta> (Suc k) $$ v' = Some A'"
            proof cases
              case a
              with \<theta>'_alt_def and \<open>distinct xs\<close> and \<open>j < length xs\<close>
              have "?\<theta>' k $$ (xs ! j) = Some (take k (map (\<lambda>A'. \<^bold>S {?y \<Zinj> ?A} A') As) ! j)"
                using \<open>length xs = length As\<close> and \<open>length ys = length xs\<close> by auto
              also from a and Suc.prems have "\<dots> = Some (\<^bold>S {?y \<Zinj> ?A} (As ! j))"
                using \<open>length xs = length As\<close> by auto
              also have "\<dots> = Some (As ! j)"
              proof -
                from Suc.prems and \<open>length ys = length xs\<close> have "Suc k \<le> length ys"
                  by (simp only:)
                moreover have "j < length As"
                  using \<open>j < length xs\<close> and \<open>length xs = length As\<close> by (simp only:)
                ultimately have "?y \<notin> vars (As ! j)"
                  using ys_fresh by force
                then show ?thesis
                  using free_var_singleton_substitution_neutrality and free_vars_in_all_vars by blast
              qed
              also from a and \<open>xs ! j = v'\<close> and \<open>distinct xs\<close> have "\<dots> = ?\<theta> (Suc k) $$ v'"
                using \<open>j < length xs\<close> and \<open>length xs = length As\<close> and \<open>length ys = length xs\<close>
                by fastforce
              finally show ?thesis
                using \<open>?\<theta>' k $$ v' = Some A'\<close> and \<open>xs ! j = v'\<close> by simp
            next
              case b
              then have "
                ?\<theta>' k $$ (xs ! k) = Some (drop k (map (\<lambda>A'. \<^bold>S {?y \<Zinj> ?A} A') (map FVar ys)) ! 0)"
                using \<open>distinct xs\<close> and \<open>j < length xs\<close> and \<open>length xs = length As\<close>
                and \<open>length ys = length xs\<close> and fmap_of_list_nth_split by simp
              also from Suc.prems have "\<dots> = Some (\<^bold>S {?y \<Zinj> ?A} (FVar ?y))"
                using \<open>length ys = length xs\<close> by simp
              also from \<open>(n\<^sub>y, \<alpha>\<^sub>y) = ys ! k\<close> have "\<dots> = Some ?A"
                by (metis singleton_substitution_simps(1))
              also from b and \<open>xs ! j = v'\<close> and \<open>distinct xs\<close> have "\<dots> = ?\<theta> (Suc k) $$ v'"
                using \<open>j < length xs\<close> and \<open>length xs = length As\<close> and \<open>length ys = length xs\<close>
                by fastforce
              finally show ?thesis
                using b and \<open>?\<theta>' k $$ v' = Some A'\<close> and \<open>xs ! j = v'\<close> by force
            next
              case c
              then have "j > k"
                by simp
              with \<theta>'_alt_def and \<open>distinct xs\<close> and \<open>j < length xs\<close> have "
                ?\<theta>' k $$ (xs ! j) = Some (drop k (map (\<lambda>A'. \<^bold>S {?y \<Zinj> ?A} A') (map FVar ys)) ! (j - k))"
                using fmap_of_list_nth_split and \<open>length xs = length As\<close> and \<open>length ys = length xs\<close>
                by simp
              also from Suc.prems and c have "\<dots> = Some (\<^bold>S {?y \<Zinj> ?A} (FVar (ys ! j)))"
                using \<open>length ys = length xs\<close> by simp
              also from Suc_le_lessD[OF Suc.prems] and \<open>distinct ys\<close> have "\<dots> = Some (FVar (ys ! j))"
                using \<open>j < length xs\<close> and \<open>k < j\<close> and \<open>length ys = length xs\<close>
                by (metis nless_le nth_eq_iff_index_eq prod.exhaust_sel singleton_substitution_simps(1))
              also from c and \<open>distinct xs\<close> have "\<dots> = ?\<theta> (Suc k) $$ v'"
                using \<open>xs ! j = v'\<close> and \<open>length xs = length As\<close> and \<open>length ys = length xs\<close> by force
              finally show ?thesis
                using \<open>?\<theta>' k $$ v' = Some A'\<close> and \<open>xs ! j = v'\<close> by force
            qed
          }
          note \<theta>_k_in_Sub_k = this
          {
            fix v' and A'
            assume "?\<theta> (Suc k) $$ v' = Some A'"
            then have "v' \<in> fmdom' (?\<theta> (Suc k))"
              by (intro fmdom'I)
            then obtain j where "j < length xs" and "xs ! j = v'"
              using \<open>fmdom' (?\<theta> (Suc k)) = lset xs\<close> by (metis in_set_conv_nth)
            then consider (a) "j < k" | (b) "j = k" | (c) "j \<in> {k<..< length xs}"
              by fastforce
            with \<open>j < length xs\<close> and \<open>xs ! j = v'\<close> and \<theta>_k_in_Sub_k show "?\<theta>' k $$ v' = Some A'"
              using \<open>\<And>k'. fmdom' (?\<theta>' k') = lset xs\<close> and \<open>?\<theta> (Suc k) $$ v' = Some A'\<close>
              by (metis (mono_tags, lifting) fmlookup_dom'_iff nth_mem)+
          }
        qed
        then show ?thesis
          by presburger
      qed
      also have "\<dots> = \<^bold>S (?\<theta> (Suc k)) B"
      proof -
        have "?\<theta> (Suc k) $$ ?y = None"
          using \<open>?y \<in> lset ys\<close> \<open>\<And>k'. fmdom' (?\<theta> k') = lset xs\<close> and ys_fresh by blast
        moreover from Suc_le_lessD[OF Suc.prems] have "?y \<notin> vars B"
          using \<open>\<forall>j < length ys. ys ! j \<notin> vars \<H> \<and> ys ! j \<notin> vars B\<close> and \<open>length ys = length xs\<close>
          by auto
        ultimately show ?thesis
          by (rule substitution_absorption)
      qed
      finally show ?thesis .
    qed
    \<comment> \<open>$\mathcal{H}\;\vdash\;\d{\textsf{S}}\;
        ^{x^1_{\alpha_1}\;\dots\;x^k_{\alpha_k} x^{k+1}_{\alpha_{k+1}} x^{k+2}_{\alpha_{k+2}}
         \;\dots\;x^n_{\alpha_n}}
        _{A^1_{\alpha_1}\;\dots\;A^k_{\alpha_k} A^{k+1}_{\alpha_{k+1}} y^{k+2}_{\alpha_{k+2}}
         \;\dots\;y^n_{\alpha_n}} B$\<close>
    ultimately show ?case
      by (simp only:)
  qed
  \<comment> \<open>$\mathcal{H}\;\vdash\;\d{\textsf{S}}\;
      ^{x^1_{\alpha_1}\;\dots\;x^n_{\alpha_n}} _{A^1_{\alpha_1}\;\dots\;A^n_{\alpha_n}} B$\<close>
  then have "\<H> \<turnstile> \<^bold>S (fmap_of_list (zip xs As)) B"
    using \<open>length xs = length As\<close> and \<open>length ys = length xs\<close> by force
  moreover have "fmap_of_list (zip xs As) = \<theta>"
  proof (intro fsubset_antisym[unfolded fmsubset_alt_def] fmpredI)
    fix v and A
    assume "fmap_of_list (zip xs As) $$ v = Some A"
    with \<open>lset xs = fmdom' \<theta>\<close> have "v \<in> fmdom' \<theta>"
      by (fast dest: fmap_of_list_SomeD set_zip_leftD)
    with \<open>fmap_of_list (zip xs As) $$ v = Some A\<close> and \<open>As = map (($$!) \<theta>) xs\<close> show "\<theta> $$ v = Some A"
      by
        (simp add: map_of_zip_map fmap_of_list.rep_eq split: if_splits)
        (meson fmdom'_notI option.exhaust_sel)
  next
    fix v and A
    assume "\<theta> $$ v = Some A"
    with \<open>As = map (($$!) \<theta>) xs\<close> show "fmap_of_list (zip xs As) $$ v = Some A"
      using \<open>lset xs = fmdom' \<theta>\<close> by (simp add: fmap_of_list.rep_eq fmdom'I map_of_zip_map)
  qed
  ultimately show ?thesis
    by (simp only:)
qed

end

lemmas Sub = prop_5221 (* synonym *)

subsection \<open>Proposition 5222 (Rule of Cases)\<close>

lemma forall_\<alpha>_conversion:
  assumes "A \<in> wffs\<^bsub>o\<^esub>"
  and "(z, \<beta>) \<notin> free_vars A"
  and "is_free_for (z\<^bsub>\<beta>\<^esub>) (x, \<beta>) A"
  shows "\<turnstile> \<forall>x\<^bsub>\<beta>\<^esub>. A =\<^bsub>o\<^esub> \<forall>z\<^bsub>\<beta>\<^esub>. \<^bold>S {(x, \<beta>) \<Zinj> z\<^bsub>\<beta>\<^esub>} A"
proof -
  from assms(1) have "\<forall>x\<^bsub>\<beta>\<^esub>. A \<in> wffs\<^bsub>o\<^esub>"
    by (intro forall_wff)
  then have "\<turnstile> \<forall>x\<^bsub>\<beta>\<^esub>. A =\<^bsub>o\<^esub> \<forall>x\<^bsub>\<beta>\<^esub>. A"
    by (fact prop_5200)
  moreover from assms have "\<turnstile> (\<lambda>x\<^bsub>\<beta>\<^esub>. A) =\<^bsub>\<beta>\<rightarrow>o\<^esub> (\<lambda>z\<^bsub>\<beta>\<^esub>. \<^bold>S {(x, \<beta>) \<Zinj> z\<^bsub>\<beta>\<^esub>} A)"
    by (rule prop_5206)
  ultimately show ?thesis
    unfolding forall_def and PI_def by (rule rule_R [where p = "[\<guillemotright>,\<guillemotright>]"]) force+
qed

proposition prop_5222:
  assumes "\<H> \<turnstile> \<^bold>S {(x, o) \<Zinj> T\<^bsub>o\<^esub>} A" and "\<H> \<turnstile> \<^bold>S {(x, o) \<Zinj> F\<^bsub>o\<^esub>} A"
  and "A \<in> wffs\<^bsub>o\<^esub>"
  shows "\<H> \<turnstile> A"
proof -
  from assms(1) have "is_hyps \<H>"
    by (blast elim: is_derivable_from_hyps.cases)
  have "\<section>1": "\<H> \<turnstile> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> (\<lambda>x\<^bsub>o\<^esub>. A) \<sqdot> T\<^bsub>o\<^esub>"
  proof -
    have "\<turnstile> (\<lambda>x\<^bsub>o\<^esub>. A) \<sqdot> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<^bold>S {(x, o) \<Zinj> T\<^bsub>o\<^esub>} A"
      using prop_5207[OF true_wff assms(3) closed_is_free_for] by simp
    from this and assms(1) have "\<H> \<turnstile> (\<lambda>x\<^bsub>o\<^esub>. A) \<sqdot> T\<^bsub>o\<^esub>"
      using rule_RR[OF disjI2, where p = "[]"] by fastforce
    moreover have "(\<lambda>x\<^bsub>o\<^esub>. A) \<sqdot> T\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<^esub>"
      by (fact hyp_derivable_form_is_wffso[OF \<open>\<H> \<turnstile> (\<lambda>x\<^bsub>o\<^esub>. A) \<sqdot> T\<^bsub>o\<^esub>\<close>])
    ultimately show ?thesis
      using rule_T(1) by blast
  qed
  moreover have "\<section>2": "\<H> \<turnstile> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> (\<lambda>x\<^bsub>o\<^esub>. A) \<sqdot> F\<^bsub>o\<^esub>"
  proof -
    have "\<turnstile> (\<lambda>x\<^bsub>o\<^esub>. A) \<sqdot> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<^bold>S {(x, o) \<Zinj> F\<^bsub>o\<^esub>} A"
      using prop_5207[OF false_wff assms(3) closed_is_free_for] by simp
    from this and assms(2) have "\<H> \<turnstile> (\<lambda>x\<^bsub>o\<^esub>. A) \<sqdot> F\<^bsub>o\<^esub>"
      using rule_RR[OF disjI2, where p = "[]"] by fastforce
    moreover have "(\<lambda>x\<^bsub>o\<^esub>. A) \<sqdot> F\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<^esub>"
      by (fact hyp_derivable_form_is_wffso[OF \<open>\<H> \<turnstile> (\<lambda>x\<^bsub>o\<^esub>. A) \<sqdot> F\<^bsub>o\<^esub>\<close>])
    ultimately show ?thesis
      using rule_T(1) by blast
  qed
  moreover from prop_5212 and \<open>is_hyps \<H>\<close> have "\<section>3": "\<H> \<turnstile> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> T\<^bsub>o\<^esub>"
    by (rule derivability_implies_hyp_derivability)
  ultimately have "\<H> \<turnstile> (\<lambda>x\<^bsub>o\<^esub>. A) \<sqdot> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> (\<lambda>x\<^bsub>o\<^esub>. A) \<sqdot> F\<^bsub>o\<^esub>"
  proof -
    from "\<section>3" and "\<section>1" have "\<H> \<turnstile> (\<lambda>x\<^bsub>o\<^esub>. A) \<sqdot> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> T\<^bsub>o\<^esub>"
      by (rule rule_R'[where p = "[\<guillemotleft>,\<guillemotright>]"]) (force+, fastforce dest: subforms_from_app)
    from this and "\<section>2" show ?thesis
      by (rule rule_R'[where p = "[\<guillemotright>]"]) (force+, fastforce dest: subforms_from_app)
  qed
  moreover have "\<turnstile> (\<lambda>x\<^bsub>o\<^esub>. A) \<sqdot> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> (\<lambda>x\<^bsub>o\<^esub>. A) \<sqdot> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>x\<^bsub>o\<^esub>. A"
  proof -
    have "\<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<^esub>"
      by blast
    have "\<turnstile> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>"
      using axiom_1[unfolded equivalence_def] by (rule axiom_is_derivable_from_no_hyps)
    \<comment> \<open>By $\alpha$-conversion\<close>
    then have "\<turnstile> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>x\<^bsub>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> x\<^bsub>o\<^esub>" (is "\<turnstile> ?B =\<^bsub>o\<^esub> ?C")
    proof -
      have "\<turnstile> \<forall>\<xx>\<^bsub>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>x\<^bsub>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> x\<^bsub>o\<^esub>"
      proof (cases "x = \<xx>")
        case True
        from \<open>\<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<^esub>\<close> have "\<turnstile> \<forall>\<xx>\<^bsub>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>"
          by (fact prop_5200[OF forall_wff])
        with True show ?thesis
          using identity_singleton_substitution_neutrality by simp
      next
        case False
        from \<open>\<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<^esub>\<close>
        have "\<turnstile> \<forall>\<xx>\<^bsub>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>x\<^bsub>o\<^esub>. \<^bold>S {(\<xx>, o) \<Zinj> x\<^bsub>o\<^esub>} (\<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>)"
          by
            (rule forall_\<alpha>_conversion)
            (simp add: False, intro is_free_for_to_app is_free_for_in_var)
        then show ?thesis
          by force
      qed
      with \<open>\<turnstile> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>\<xx>\<^bsub>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>\<close> show ?thesis
        using Equality_Rules(3) by blast
    qed
    \<comment> \<open>By Sub\<close>
    then have *: "\<turnstile> (\<lambda>x\<^bsub>o\<^esub>. A) \<sqdot> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> (\<lambda>x\<^bsub>o\<^esub>. A) \<sqdot> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<forall>x\<^bsub>o\<^esub>. (\<lambda>x\<^bsub>o\<^esub>. A) \<sqdot> x\<^bsub>o\<^esub>"
    proof -
      let ?\<theta> = "{(\<gg>, o\<rightarrow>o) \<Zinj> \<lambda>x\<^bsub>o\<^esub>. A}"
      from assms(3) have "is_substitution ?\<theta>"
        by auto
      moreover have "
        \<forall>v \<in> fmdom' ?\<theta>.
          var_name v \<notin> free_var_names ({}::form set) \<and> is_free_for (?\<theta> $$! v) v (?B =\<^bsub>o\<^esub> ?C)"
        by (code_simp, (unfold atomize_conj[symmetric])?, simp)+ blast
      moreover have "?\<theta> \<noteq> {$$}"
        by simp
      ultimately have "\<turnstile> \<^bold>S ?\<theta> (?B =\<^bsub>o\<^esub> ?C)"
        by (rule Sub [OF \<open>\<turnstile> ?B =\<^bsub>o\<^esub> ?C\<close>])
      then show ?thesis
        by simp
    qed
    \<comment> \<open>By $\lambda$-conversion\<close>
    then show ?thesis
    proof -
      have "\<turnstile> (\<lambda>x\<^bsub>o\<^esub>. A) \<sqdot> x\<^bsub>o\<^esub> =\<^bsub>o\<^esub> A"
        using prop_5208[where vs = "[(x, o)]"] and assms(3) by simp
      from * and this show ?thesis
        by (rule rule_R[where p = "[\<guillemotright>,\<guillemotright>,\<guillemotleft>]"]) force+
    qed
  qed
  ultimately have "\<H> \<turnstile> \<forall>x\<^bsub>o\<^esub>. A"
    using rule_RR and is_subform_at.simps(1) by (blast intro: empty_is_position)
  then show ?thesis
  proof -
    have "is_free_for (x\<^bsub>o\<^esub>) (x, o) A"
      by fastforce
    from \<open>\<H> \<turnstile> \<forall>x\<^bsub>o\<^esub>. A\<close> and wffs_of_type_intros(1) and this show ?thesis
      by (rule "\<forall>I"[of \<H> x o A "x\<^bsub>o\<^esub>", unfolded identity_singleton_substitution_neutrality])
  qed
qed

lemmas Cases = prop_5222 (* synonym *)

subsection \<open>Proposition 5223\<close>

proposition prop_5223:
  shows "\<turnstile> (T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> \<yy>\<^bsub>o\<^esub>"
proof -
  have "\<turnstile> (T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>))"
  proof -
    let ?A = "(\<lambda>\<xx>\<^bsub>o\<^esub>. \<lambda>\<yy>\<^bsub>o\<^esub>. (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) \<sqdot> T\<^bsub>o\<^esub> \<sqdot> \<yy>\<^bsub>o\<^esub>"
    have "?A \<in> wffs\<^bsub>o\<^esub>"
      by force
    then have "\<turnstile> ?A =\<^bsub>o\<^esub> ?A"
      by (fact prop_5200)
    then have "\<turnstile> (T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> ?A"
      unfolding imp_fun_def and imp_op_def .
    moreover
    have "\<turnstile> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<lambda>\<yy>\<^bsub>o\<^esub>. (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) \<sqdot> T\<^bsub>o\<^esub> =\<^bsub>o\<rightarrow>o\<^esub> \<lambda>\<yy>\<^bsub>o\<^esub>. (T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)"
    proof -
      have "\<lambda>\<yy>\<^bsub>o\<^esub>. (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>) \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>"
        by auto
      moreover
      have "is_free_for T\<^bsub>o\<^esub> (\<xx>, o) (\<lambda>\<yy>\<^bsub>o\<^esub>. (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>))"
        by fastforce
      moreover
      have "\<^bold>S {(\<xx>, o) \<Zinj> T\<^bsub>o\<^esub>} (\<lambda>\<yy>\<^bsub>o\<^esub>. (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) = (\<lambda>\<yy>\<^bsub>o\<^esub>. (T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>))"
        by simp
      ultimately show ?thesis
        using prop_5207[OF true_wff] by metis
    qed
    ultimately have *: "\<turnstile> (T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> (\<lambda>\<yy>\<^bsub>o\<^esub>. (T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) \<sqdot> \<yy>\<^bsub>o\<^esub>"
      by (rule rule_R [where p = "[\<guillemotright>,\<guillemotleft>]"]) force+
    have "T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<^esub>"
      by auto
    then have "\<turnstile> (\<lambda>\<yy>\<^bsub>o\<^esub>. (T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) \<sqdot> \<yy>\<^bsub>o\<^esub> =\<^bsub>o\<^esub> (T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)"
      using prop_5208[where vs = "[(\<yy>, o)]"] by simp
    from * and this show ?thesis
      by (rule rule_R[where p = "[\<guillemotright>]"]) force+
  qed
  with prop_5218 have "\<turnstile> (T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)"
    using rule_R and Equality_Rules(3) by (meson conj_op_wff true_wff wffs_of_type_intros(1))
  with prop_5216 show ?thesis
    using rule_R and Equality_Rules(3) by (meson conj_op_wff true_wff wffs_of_type_intros(1))
qed

corollary generalized_prop_5223:
  assumes "A \<in> wffs\<^bsub>o\<^esub>"
  shows "\<turnstile> (T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> A) =\<^bsub>o\<^esub> A"
proof -
  have "T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<^esub>" and "is_free_for A (\<yy>, o) ((T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> \<yy>\<^bsub>o\<^esub>)"
   by (blast, intro is_free_for_in_equality is_free_for_in_imp is_free_for_in_true is_free_for_in_var)
  from this(2) have "\<turnstile> \<^bold>S {(\<yy>, o) \<Zinj> A} ((T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> \<yy>\<^bsub>o\<^esub>)"
    by (rule prop_5209[OF assms \<open>T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<^esub>\<close> wffs_of_type_intros(1) prop_5223])
  then show ?thesis
    by simp
qed

subsection \<open>Proposition 5224 (Modus Ponens)\<close>

proposition prop_5224:
  assumes "\<H> \<turnstile> A" and "\<H> \<turnstile> A \<supset>\<^sup>\<Q> B"
  shows "\<H> \<turnstile> B"
proof -
  have "\<H> \<turnstile> A \<supset>\<^sup>\<Q> B"
    by fact
  moreover from assms(1) have "A \<in> wffs\<^bsub>o\<^esub>"
    by (fact hyp_derivable_form_is_wffso)
  from this and assms(1) have "\<H> \<turnstile> A =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
    using rule_T(2) by blast
  ultimately have "\<H> \<turnstile> T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> B"
    by (rule rule_R'[where p = "[\<guillemotleft>,\<guillemotright>]"]) (force+, fastforce dest: subforms_from_app)
  have "\<turnstile> (T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> B) =\<^bsub>o\<^esub> B"
  proof -
    let ?\<theta> = "{(\<yy>, o) \<Zinj> B}"
    have "B \<in> wffs\<^bsub>o\<^esub>"
      by (fact hyp_derivable_form_is_wffso[OF assms(2), THEN wffs_from_imp_op(2)])
    then have "is_substitution ?\<theta>"
      by simp
    moreover have "
      \<forall>v \<in> fmdom' ?\<theta>.
        var_name v \<notin> free_var_names ({}::form set) \<and>
        is_free_for (?\<theta> $$! v) v ((T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> \<yy>\<^bsub>o\<^esub>)"
      by (code_simp, (unfold atomize_conj[symmetric])?, simp)+ blast
    moreover have "?\<theta> \<noteq> {$$}"
      by simp
    ultimately have "\<turnstile> \<^bold>S ?\<theta> ((T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> \<yy>\<^bsub>o\<^esub>)"
      by (rule Sub[OF prop_5223])
    then show ?thesis
      by simp
  qed
  then show ?thesis
    by (rule rule_RR[OF disjI1, where p = "[]"]) (use \<open>\<H> \<turnstile> T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> B\<close> in \<open>force+\<close>)
qed

lemmas MP = prop_5224 (* synonym *)

corollary generalized_modus_ponens:
  assumes "\<H> \<turnstile> hs \<supset>\<^sup>\<Q>\<^sub>\<star> B" and "\<forall>H \<in> lset hs. \<H> \<turnstile> H"
  shows "\<H> \<turnstile> B"
using assms proof (induction hs arbitrary: B rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc H' hs)
  from \<open>\<forall>H \<in> lset (hs @ [H']). \<H> \<turnstile> H\<close> have "\<H> \<turnstile> H'"
    by simp
  moreover have "\<H> \<turnstile> H' \<supset>\<^sup>\<Q> B"
  proof -
    from \<open>\<H> \<turnstile> (hs @ [H']) \<supset>\<^sup>\<Q>\<^sub>\<star> B\<close> have "\<H> \<turnstile> hs \<supset>\<^sup>\<Q>\<^sub>\<star> (H' \<supset>\<^sup>\<Q> B)"
      by simp
    moreover from \<open>\<forall>H \<in> lset (hs @ [H']). \<H> \<turnstile> H\<close> have "\<forall>H \<in> lset hs. \<H> \<turnstile> H"
      by simp
    ultimately show ?thesis
      by (elim snoc.IH)
  qed
  ultimately show ?case
    by (rule MP)
qed

subsection \<open>Proposition 5225\<close>

proposition prop_5225:
  shows "\<turnstile> \<Prod>\<^bsub>\<alpha>\<^esub> \<sqdot> \<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<supset>\<^sup>\<Q> \<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>"
proof -
  have "\<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> \<in> wffs\<^bsub>o\<^esub>"
    by blast
  have "\<section>1": "
    \<turnstile>
      \<Prod>\<^bsub>\<alpha>\<^esub> \<sqdot> \<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<supset>\<^sup>\<Q> (((\<lambda>\<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub>. \<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) \<sqdot> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>))
      =\<^bsub>o\<^esub>
      ((\<lambda>\<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub>. \<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) \<sqdot> \<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub>))"
  proof -
    let ?\<theta> = "{(\<hh>, (\<alpha>\<rightarrow>o)\<rightarrow>o) \<Zinj> \<lambda>\<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub>. \<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>, (\<xx>, \<alpha>\<rightarrow>o) \<Zinj> \<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>, (\<yy>, \<alpha>\<rightarrow>o) \<Zinj> \<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub>}"
      and ?A = "(\<xx>\<^bsub>\<alpha>\<rightarrow>o\<^esub> =\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<yy>\<^bsub>\<alpha>\<rightarrow>o\<^esub>) \<supset>\<^sup>\<Q> (\<hh>\<^bsub>(\<alpha>\<rightarrow>o)\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<equiv>\<^sup>\<Q> \<hh>\<^bsub>(\<alpha>\<rightarrow>o)\<rightarrow>o\<^esub> \<sqdot> \<yy>\<^bsub>\<alpha>\<rightarrow>o\<^esub>)"
    have "\<turnstile> ?A"
      by (fact axiom_is_derivable_from_no_hyps[OF axiom_2])
    moreover have "\<lambda>\<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub>. \<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> \<in> wffs\<^bsub>(\<alpha>\<rightarrow>o)\<rightarrow>o\<^esub>" and "\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub> \<in> wffs\<^bsub>\<alpha>\<rightarrow>o\<^esub>"
      and "\<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<in> wffs\<^bsub>\<alpha>\<rightarrow>o\<^esub>"
      by blast+
    then have "is_substitution ?\<theta>"
      by simp
    moreover have "
      \<forall>v \<in> fmdom' ?\<theta>. var_name v \<notin> free_var_names ({}::form set) \<and> is_free_for (?\<theta> $$! v) v ?A"
      by (code_simp, (unfold atomize_conj[symmetric])?, simp)+ blast
    moreover have "?\<theta> \<noteq> {$$}"
      by simp
    ultimately have "\<turnstile> \<^bold>S ?\<theta> ?A"
      by (rule Sub)
    then show ?thesis
      by simp
  qed
  have "\<turnstile> \<Prod>\<^bsub>\<alpha>\<^esub> \<sqdot> \<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<supset>\<^sup>\<Q> (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>)"
  proof -
    have "
      \<turnstile> (\<lambda>\<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub>. \<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) \<sqdot> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>"
      (is "\<turnstile> (\<lambda>?x\<^bsub>?\<beta>\<^esub>. ?B) \<sqdot> ?A =\<^bsub>o\<^esub> ?C")
    proof -
      have "\<turnstile> (\<lambda>?x\<^bsub>?\<beta>\<^esub>. ?B) \<sqdot> ?A =\<^bsub>o\<^esub> \<^bold>S {(?x, ?\<beta>) \<Zinj> ?A} ?B"
        using prop_5207[OF wffs_of_type_intros(4)[OF true_wff] \<open>?B \<in> wffs\<^bsub>o\<^esub>\<close>] by fastforce
      then show ?thesis
        by simp
    qed
    moreover have "\<turnstile> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
      using prop_5208[where vs = "[(\<xx>, \<alpha>)]"] and true_wff by simp
    ultimately have "\<turnstile> (\<lambda>\<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub>. \<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) \<sqdot> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
      by (rule Equality_Rules(3))
    from "\<section>1" and this have "\<turnstile> \<Prod>\<^bsub>\<alpha>\<^esub> \<sqdot> \<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<supset>\<^sup>\<Q> (T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> ((\<lambda>\<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub>. \<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) \<sqdot> \<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub>))"
      by (rule rule_R[where p = "[\<guillemotright>,\<guillemotleft>,\<guillemotright>]"]) force+
    moreover have "\<turnstile> (\<lambda>\<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub>. \<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) \<sqdot> \<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub> =\<^bsub>o\<^esub> \<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>"
      using prop_5208[where vs = "[(\<ff>, \<alpha>\<rightarrow>o)]"] by force
    ultimately show ?thesis
      by (rule rule_R[where p = "[\<guillemotright>,\<guillemotright>]"]) force+
  qed
  from this and prop_5218[OF \<open>\<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> \<in> wffs\<^bsub>o\<^esub>\<close>] show ?thesis
    by (rule rule_R[where p = "[\<guillemotright>]"]) auto
qed

subsection \<open>Proposition 5226\<close>

proposition prop_5226:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
  and "is_free_for A (x, \<alpha>) B"
  shows "\<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. B \<supset>\<^sup>\<Q> \<^bold>S {(x, \<alpha>) \<Zinj> A} B"
proof -
  have "\<turnstile> \<Prod>\<^bsub>\<alpha>\<^esub> \<sqdot> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<supset>\<^sup>\<Q> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A"
  proof -
    let ?\<theta> = "{(\<ff>, \<alpha>\<rightarrow>o) \<Zinj> \<lambda>x\<^bsub>\<alpha>\<^esub>. B, (\<xx>, \<alpha>) \<Zinj> A}"
    have "\<turnstile> \<Prod>\<^bsub>\<alpha>\<^esub> \<sqdot> \<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<supset>\<^sup>\<Q> \<ff>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>" (is "\<turnstile> ?C")
      by (fact prop_5225)
    moreover from assms have "is_substitution ?\<theta>"
      by auto
    moreover have "
      \<forall>v \<in> fmdom' ?\<theta>. var_name v \<notin> free_var_names ({}::form set) \<and> is_free_for (?\<theta> $$! v) v ?C"
      by (code_simp, (unfold atomize_conj[symmetric])?, fastforce)+ blast
    moreover have "?\<theta> \<noteq> {$$}"
      by simp
    ultimately have "\<turnstile> \<^bold>S ?\<theta> ?C"
      by (rule Sub)
    moreover have "\<^bold>S ?\<theta> ?C = \<Prod>\<^bsub>\<alpha>\<^esub> \<sqdot> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<supset>\<^sup>\<Q> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A"
      by simp
    ultimately show ?thesis
      by (simp only:)
  qed
  moreover from assms have "\<turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A =\<^bsub>o\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> A} B"
    by (rule prop_5207)
  ultimately show ?thesis
    by (rule rule_R [where p = "[\<guillemotright>]"]) force+
qed

subsection \<open>Proposition 5227\<close>

corollary prop_5227:
  shows "\<turnstile> F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub>"
proof -
  have "\<turnstile> \<forall>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<^bold>S {(\<xx>, o) \<Zinj> \<xx>\<^bsub>o\<^esub>} (\<xx>\<^bsub>o\<^esub>)"
    by (rule prop_5226) auto
  then show ?thesis
    using identity_singleton_substitution_neutrality by simp
qed

corollary generalized_prop_5227:
  assumes "A \<in> wffs\<^bsub>o\<^esub>"
  shows "\<turnstile> F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> A"
proof -
  let ?\<theta> = "{(\<xx>, o) \<Zinj> A}" and ?B = "F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub>"
  from assms have "is_substitution ?\<theta>"
    by simp
  moreover have "is_free_for A (\<xx>, o) ?B"
    by (intro is_free_for_in_false is_free_for_in_imp is_free_for_in_var)
  then have "
    \<forall>v \<in> fmdom' ?\<theta>. var_name v \<notin> free_var_names ({}::form set) \<and> is_free_for (?\<theta> $$! v) v ?B"
    by force
  ultimately have "\<turnstile> \<^bold>S {(\<xx>, o) \<Zinj> A} (F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub>)"
    using Sub[OF prop_5227, where \<theta> = ?\<theta>] by fastforce
  then show ?thesis
    by simp
qed

subsection \<open>Proposition 5228\<close>

proposition prop_5228:
  shows "\<turnstile> (T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
  and "\<turnstile> (T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
  and "\<turnstile> (F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
  and "\<turnstile> (F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
proof -
  show "\<turnstile> (T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" and "\<turnstile> (T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
    using generalized_prop_5223 by blast+
next
  have "\<turnstile> F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> F\<^bsub>o\<^esub>" and "\<turnstile> F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> T\<^bsub>o\<^esub>"
    using generalized_prop_5227 by blast+
  then show "\<turnstile> (F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" and "\<turnstile> (F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
    using rule_T(2) by blast+
qed

subsection \<open>Proposition 5229\<close>

lemma false_in_conj_provability:
  assumes "A \<in> wffs\<^bsub>o\<^esub>"
  shows "\<turnstile> F\<^bsub>o\<^esub> \<and>\<^sup>\<Q> A \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>"
proof -
  have "\<turnstile> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<lambda>\<yy>\<^bsub>o\<^esub>. (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) \<sqdot> F\<^bsub>o\<^esub> \<sqdot> A"
    by (intro generalized_prop_5227[OF assms, unfolded imp_op_def imp_fun_def])
  moreover have "
    \<turnstile>
      (\<lambda>\<xx>\<^bsub>o\<^esub>. \<lambda>\<yy>\<^bsub>o\<^esub>. (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) \<sqdot> F\<^bsub>o\<^esub>
      =\<^bsub>o\<rightarrow>o\<^esub>
      \<lambda>\<yy>\<^bsub>o\<^esub>. (F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)"
    (is "\<turnstile> (\<lambda>?x\<^bsub>?\<beta>\<^esub>. ?A) \<sqdot> ?B =\<^bsub>?\<gamma>\<^esub> ?C")
  proof -
    have "?B \<in> wffs\<^bsub>?\<beta>\<^esub>" and "?A \<in> wffs\<^bsub>?\<gamma>\<^esub>" and "is_free_for ?B (?x, ?\<beta>) ?A"
      by auto
    then have "\<turnstile> (\<lambda>?x\<^bsub>?\<beta>\<^esub>. ?A) \<sqdot> ?B =\<^bsub>?\<gamma>\<^esub> \<^bold>S {(?x, ?\<beta>) \<Zinj> ?B} ?A"
      by (rule prop_5207)
    moreover have "\<^bold>S {(?x, ?\<beta>) \<Zinj> ?B} ?A = ?C"
      by simp
    ultimately show ?thesis
      by (simp only:)
  qed
  ultimately have "\<turnstile> (\<lambda>\<yy>\<^bsub>o\<^esub>. (F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) \<sqdot> A"
    by (rule rule_R[where p = "[\<guillemotleft>]"]) auto
  moreover have "
    \<turnstile>
      (\<lambda>\<yy>\<^bsub>o\<^esub>. (F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) \<sqdot> A
      =\<^bsub>o\<^esub>
      (F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub> \<and>\<^sup>\<Q> A)"
    (is "\<turnstile> (\<lambda>?x\<^bsub>?\<beta>\<^esub>. ?A) \<sqdot> ?B =\<^bsub>o\<^esub> ?C")
  proof -
    have "?B \<in> wffs\<^bsub>?\<beta>\<^esub>" and "?A \<in> wffs\<^bsub>o\<^esub>"
      using assms by auto
    moreover have "is_free_for ?B (?x, ?\<beta>) ?A"
      by (intro is_free_for_in_equivalence is_free_for_in_conj is_free_for_in_false) fastforce
    ultimately have "\<turnstile> (\<lambda>?x\<^bsub>?\<beta>\<^esub>. ?A) \<sqdot> ?B =\<^bsub>o\<^esub> \<^bold>S {(?x, ?\<beta>) \<Zinj> ?B} ?A"
      by (rule prop_5207)
    moreover
    have "\<^bold>S {(?x, ?\<beta>) \<Zinj> ?B} ?A = ?C"
      by simp
    ultimately show ?thesis
      by (simp only:)
  qed
  ultimately have "\<turnstile> F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub> \<and>\<^sup>\<Q> A"
    by (rule rule_R[where p = "[]"]) auto
  then show ?thesis
    unfolding equivalence_def by (rule Equality_Rules(2))
qed

proposition prop_5229:
  shows "\<turnstile> (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
  and "\<turnstile> (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
  and "\<turnstile> (F\<^bsub>o\<^esub> \<and>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
  and "\<turnstile> (F\<^bsub>o\<^esub> \<and>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
proof -
  show "\<turnstile> (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" and "\<turnstile> (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
    using prop_5216 by blast+
next
  show "\<turnstile> (F\<^bsub>o\<^esub> \<and>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>" and "\<turnstile> (F\<^bsub>o\<^esub> \<and>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
    using false_in_conj_provability and true_wff and false_wff by simp_all
qed

subsection \<open>Proposition 5230\<close>

proposition prop_5230:
  shows "\<turnstile> (T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
  and "\<turnstile> (T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
  and "\<turnstile> (F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
  and "\<turnstile> (F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
proof -
  show "\<turnstile> (T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" and "\<turnstile> (T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
    unfolding equivalence_def using prop_5218 by blast+
next
  show "\<turnstile> (F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
    unfolding equivalence_def by (rule Equality_Rules(2)[OF prop_5210[OF false_wff]])
next
  have "\<section>1": "\<turnstile> (F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) \<supset>\<^sup>\<Q> ((\<lambda>\<xx>\<^bsub>o\<^esub>. (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>)) \<sqdot> F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> (\<lambda>\<xx>\<^bsub>o\<^esub>. (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>)) \<sqdot> T\<^bsub>o\<^esub>)"
  proof -
    let ?\<theta> = "{(\<hh>, o\<rightarrow>o) \<Zinj> \<lambda>\<xx>\<^bsub>o\<^esub>. (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>), (\<xx>, o) \<Zinj> F\<^bsub>o\<^esub>, (\<yy>, o) \<Zinj> T\<^bsub>o\<^esub>}"
      and ?A = "(\<xx>\<^bsub>o\<^esub> =\<^bsub>o\<^esub> \<yy>\<^bsub>o\<^esub>) \<supset>\<^sup>\<Q> (\<hh>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<hh>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<yy>\<^bsub>o\<^esub>)"
    have "\<turnstile> ?A"
      by (fact axiom_is_derivable_from_no_hyps[OF axiom_2])
    moreover have "is_substitution ?\<theta>"
      by auto
    moreover have "
      \<forall>v \<in> fmdom' ?\<theta>. var_name v \<notin> free_var_names ({}::form set) \<and> is_free_for (?\<theta> $$! v) v ?A"
      by (code_simp, unfold atomize_conj[symmetric], simp, force)+ blast
    moreover have "?\<theta> \<noteq> {$$}"
      by simp
    ultimately have "\<turnstile> \<^bold>S ?\<theta> ?A"
      by (rule Sub)
    then show ?thesis
      by simp
  qed
  then have "\<section>2": "\<turnstile> (F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) \<supset>\<^sup>\<Q> ((F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>) \<equiv>\<^sup>\<Q> (T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>))" (is "\<turnstile> ?A2")
  proof -
    have "is_free_for A (\<xx>, o) (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>)" for A
      by code_simp blast
    have \<beta>_reduction: "\<turnstile> (\<lambda>\<xx>\<^bsub>o\<^esub>. (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>)) \<sqdot> A =\<^bsub>o\<^esub> (A \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>)" if "A \<in> wffs\<^bsub>o\<^esub>" for A
      using
        prop_5207
        [
          OF that equivalence_wff[OF wffs_of_type_intros(1) false_wff]
          \<open>is_free_for A (\<xx>, o) (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>)\<close>
        ]
      by simp
    from "\<section>1" and \<beta>_reduction[OF false_wff] have "
      \<turnstile> (F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>) \<supset>\<^sup>\<Q> ((F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>) \<equiv>\<^sup>\<Q> (\<lambda>\<xx>\<^bsub>o\<^esub>. (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>)) \<sqdot> T\<^bsub>o\<^esub>)"
      by (rule rule_R[where p = "[\<guillemotright>,\<guillemotleft>,\<guillemotright>]"]) force+
    from this and \<beta>_reduction[OF true_wff] show ?thesis
      by (rule rule_R[where p = "[\<guillemotright>,\<guillemotright>]"]) force+
  qed
  then have "\<section>3": "\<turnstile> (F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) \<supset>\<^sup>\<Q> F\<^bsub>o\<^esub>"
  proof -
    note r1 = rule_RR[OF disjI1] and r2 = rule_RR[OF disjI2]
    have "\<section>3\<^sub>1": "\<turnstile> (F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) \<supset>\<^sup>\<Q> ((F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>) \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>)" (is \<open>\<turnstile> ?A3\<^sub>1\<close>)
      by (rule r1[OF prop_5218[OF false_wff], where p = "[\<guillemotright>,\<guillemotright>]" and C = ?A2]) (use "\<section>2" in \<open>force+\<close>)
    have "\<section>3\<^sub>2": "\<turnstile> (F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) \<supset>\<^sup>\<Q> (T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>)" (is \<open>\<turnstile> ?A3\<^sub>2\<close>)
      by (rule r2[OF prop_5210[OF false_wff], where p = "[\<guillemotright>,\<guillemotleft>,\<guillemotright>]" and C = ?A3\<^sub>1]) (use "\<section>3\<^sub>1" in \<open>force+\<close>)
    show ?thesis
      by (rule r1[OF prop_5218[OF false_wff], where p = "[\<guillemotright>]" and C = ?A3\<^sub>2]) (use "\<section>3\<^sub>2" in \<open>force+\<close>)
  qed
  then have "\<turnstile> (F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) \<equiv>\<^sup>\<Q> ((F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) \<and>\<^sup>\<Q> F\<^bsub>o\<^esub>)"
  proof -
    have "
      \<turnstile>
        (\<lambda>\<xx>\<^bsub>o\<^esub>. \<lambda>\<yy>\<^bsub>o\<^esub>. (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) \<sqdot> (F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>)
        =\<^bsub>o\<rightarrow>o\<^esub>
        \<^bold>S {(\<xx>, o) \<Zinj> F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>} (\<lambda>\<yy>\<^bsub>o\<^esub>. (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>))"
      by (rule prop_5207) auto
    from "\<section>3"[unfolded imp_op_def imp_fun_def] and this
    have "\<turnstile> (\<lambda>\<yy>\<^bsub>o\<^esub>. ((F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) \<equiv>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) \<sqdot> F\<^bsub>o\<^esub>"
      by (rule rule_R[where p = "[\<guillemotleft>]"]) force+
    moreover have "
      \<turnstile>
        (\<lambda>\<yy>\<^bsub>o\<^esub>. ((F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) \<equiv>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) \<sqdot> F\<^bsub>o\<^esub>
        =\<^bsub>o\<^esub>
        \<^bold>S {(\<yy>, o) \<Zinj> F\<^bsub>o\<^esub>} ((F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) \<equiv>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)"
      by (rule prop_5207) auto
    ultimately show ?thesis
      by (rule rule_R[where p = "[]"]) force+
  qed
  moreover have "\<section>5": "\<turnstile> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>"
  proof -
    from prop_5229(2,4) have "
      \<turnstile> \<^bold>S {(\<xx>, o) \<Zinj> T\<^bsub>o\<^esub>} (\<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>)" and "\<turnstile> \<^bold>S {(\<xx>, o) \<Zinj> F\<^bsub>o\<^esub>} (\<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>)"
      by simp_all
    moreover have "\<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<^esub>"
      by auto
    ultimately show ?thesis
      by (rule Cases)
  qed
  then have "\<turnstile> (F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) \<and>\<^sup>\<Q> F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>"
  proof -
    let ?\<theta> = "{(\<xx>, o) \<Zinj> F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>}"
    have "is_substitution ?\<theta>"
      by auto
    moreover have "\<forall>v \<in> fmdom' ?\<theta>.
      var_name v \<notin> free_var_names ({}::form set) \<and> is_free_for (?\<theta> $$! v) v (\<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>)"
      by simp
    moreover have "?\<theta> \<noteq> {$$}"
      by simp
    ultimately have "\<turnstile> \<^bold>S ?\<theta> (\<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>)"
      by (rule Sub[OF \<open>\<turnstile> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>\<close>])
    then show ?thesis
      by simp
  qed
  ultimately show "\<turnstile> (F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
    unfolding equivalence_def by (rule Equality_Rules(3))
qed

subsection \<open>Proposition 5231\<close>

proposition prop_5231:
  shows "\<turnstile> \<sim>\<^sup>\<Q> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
  and "\<turnstile> \<sim>\<^sup>\<Q> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
  using prop_5230(3,4) unfolding neg_def and equivalence_def and equality_of_type_def .

subsection \<open>Proposition 5232\<close>

lemma disj_op_alt_def_provability:
  assumes "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
  shows "\<turnstile> A \<or>\<^sup>\<Q> B =\<^bsub>o\<^esub> \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> A \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> B)"
proof -
  let ?C = "(\<lambda>\<xx>\<^bsub>o\<^esub>. \<lambda>\<yy>\<^bsub>o\<^esub>. \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) \<sqdot> A \<sqdot> B"
  from assms have "?C \<in> wffs\<^bsub>o\<^esub>"
    by blast
  have "(\<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) \<in> wffs\<^bsub>o\<^esub>"
    by auto
  moreover obtain z where "(z, o) \<notin> {(\<xx>, o), (\<yy>, o)}" and "(z, o) \<notin> free_vars A"
    using free_vars_form_finiteness and fresh_var_existence
    by (metis Un_iff Un_insert_right free_vars_form.simps(1,3) inf_sup_aci(5) sup_bot_left)
  then have "(z, o) \<notin> free_vars (\<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>))"
    by simp
  moreover have "is_free_for (z\<^bsub>o\<^esub>) (\<yy>, o) (\<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>))"
    by (intro is_free_for_in_conj is_free_for_in_neg is_free_for_in_var)
  ultimately have "
    \<turnstile> (\<lambda>\<yy>\<^bsub>o\<^esub>. \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) =\<^bsub>o\<rightarrow>o\<^esub> (\<lambda>z\<^bsub>o\<^esub>. \<^bold>S {(\<yy>, o) \<Zinj> z\<^bsub>o\<^esub>} \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>))"
    by (rule "\<alpha>")
  then have "\<turnstile> (\<lambda>\<yy>\<^bsub>o\<^esub>. \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) =\<^bsub>o\<rightarrow>o\<^esub> (\<lambda>z\<^bsub>o\<^esub>. \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> z\<^bsub>o\<^esub>))"
    by simp
  from prop_5200[OF \<open>?C \<in> wffs\<^bsub>o\<^esub>\<close>] and this have "
    \<turnstile>
      (\<lambda>\<xx>\<^bsub>o\<^esub>. \<lambda>z\<^bsub>o\<^esub>. \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> z\<^bsub>o\<^esub>)) \<sqdot> A \<sqdot> B
      =\<^bsub>o\<^esub>
      (\<lambda>\<xx>\<^bsub>o\<^esub>. \<lambda>\<yy>\<^bsub>o\<^esub>. \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) \<sqdot> A \<sqdot> B"
    by (rule rule_R[where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotleft>,\<guillemotleft>]"]) force+
  moreover have "\<lambda>z\<^bsub>o\<^esub>. \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> z\<^bsub>o\<^esub>) \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>"
    by blast
  have "
    \<turnstile>
      (\<lambda>\<xx>\<^bsub>o\<^esub>. \<lambda>z\<^bsub>o\<^esub>. \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> z\<^bsub>o\<^esub>)) \<sqdot> A
      =\<^bsub>o\<rightarrow>o\<^esub>
      \<^bold>S {(\<xx>, o) \<Zinj> A} (\<lambda>z\<^bsub>o\<^esub>. \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> z\<^bsub>o\<^esub>))"
    by
      (rule prop_5207)
      (
        fact, blast, intro is_free_for_in_neg is_free_for_in_conj is_free_for_to_abs,
        (fastforce simp add: \<open>(z, o) \<notin> free_vars A\<close>)+
      )
  then have "\<turnstile> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<lambda>z\<^bsub>o\<^esub>. \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> z\<^bsub>o\<^esub>)) \<sqdot> A =\<^bsub>o\<rightarrow>o\<^esub> (\<lambda>z\<^bsub>o\<^esub>. \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> A \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> z\<^bsub>o\<^esub>))"
    using \<open>(z, o) \<notin> free_vars (\<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>))\<close> by simp
  ultimately have "
    \<turnstile> (\<lambda>z\<^bsub>o\<^esub>. \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> A \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> z\<^bsub>o\<^esub>)) \<sqdot> B =\<^bsub>o\<^esub> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<lambda>\<yy>\<^bsub>o\<^esub>. \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) \<sqdot> A \<sqdot> B"
    by (rule rule_R[where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>]"]) force+
  moreover have "\<turnstile> (\<lambda>z\<^bsub>o\<^esub>. \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> A \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> z\<^bsub>o\<^esub>)) \<sqdot> B =\<^bsub>o\<^esub> \<^bold>S {(z, o) \<Zinj> B} (\<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> A \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> z\<^bsub>o\<^esub>))"
    by
      (rule prop_5207)
      (
        fact, blast intro: assms(1), intro is_free_for_in_neg is_free_for_in_conj,
        use \<open>(z, o) \<notin> free_vars A\<close> is_free_at_in_free_vars in \<open>fastforce+\<close>
      )
  moreover have "\<^bold>S {(z, o) \<Zinj> B} (\<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> A \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> z\<^bsub>o\<^esub>)) = \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> A \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> B)"
    using free_var_singleton_substitution_neutrality[OF \<open>(z, o) \<notin> free_vars A\<close>] by simp
  ultimately have "\<turnstile> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<lambda>\<yy>\<^bsub>o\<^esub>. \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) \<sqdot> A \<sqdot> B =\<^bsub>o\<^esub> \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> A \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> B)"
    using Equality_Rules(2,3) by metis
  then show ?thesis
    by simp
qed

context begin

private lemma prop_5232_aux:
  assumes "\<turnstile> \<sim>\<^sup>\<Q> (A \<and>\<^sup>\<Q> B) =\<^bsub>o\<^esub> C"
  and "\<turnstile> \<sim>\<^sup>\<Q> A' =\<^bsub>o\<^esub> A" and "\<turnstile> \<sim>\<^sup>\<Q> B' =\<^bsub>o\<^esub> B"
  shows "\<turnstile> A' \<or>\<^sup>\<Q> B' =\<^bsub>o\<^esub> C"
proof -
  let ?D = "\<sim>\<^sup>\<Q> (A \<and>\<^sup>\<Q> B) =\<^bsub>o\<^esub> C"
  from assms(2) have "\<turnstile> \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> A' \<and>\<^sup>\<Q> B) =\<^bsub>o\<^esub> C" (is \<open>\<turnstile> ?A1\<close>)
    by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]" and C = ?D]) (use assms(1) in \<open>force+\<close>)
  from assms(3) have "\<turnstile> \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> A' \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> B') =\<^bsub>o\<^esub> C"
    by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>,\<guillemotright>]" and C = ?A1]) (use \<open>\<turnstile> ?A1\<close> in \<open>force+\<close>)
  moreover from assms(2,3) have "A' \<in> wffs\<^bsub>o\<^esub>" and "B' \<in> wffs\<^bsub>o\<^esub>"
    using hyp_derivable_form_is_wffso by (blast dest: wffs_from_equality wffs_from_neg)+
  then have "\<turnstile> A' \<or>\<^sup>\<Q> B' =\<^bsub>o\<^esub> \<sim>\<^sup>\<Q> (\<sim>\<^sup>\<Q> A' \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> B')"
    by (rule disj_op_alt_def_provability)
  ultimately show ?thesis
    using prop_5201_3 by blast
qed

proposition prop_5232:
  shows "\<turnstile> (T\<^bsub>o\<^esub> \<or>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
  and "\<turnstile> (T\<^bsub>o\<^esub> \<or>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
  and "\<turnstile> (F\<^bsub>o\<^esub> \<or>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
  and "\<turnstile> (F\<^bsub>o\<^esub> \<or>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
proof -
  from prop_5231(2) have "\<turnstile> \<sim>\<^sup>\<Q> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A\<close>) .
  from prop_5229(4) have "\<turnstile> \<sim>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<and>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
    by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]" and C = ?A]) (use \<open>\<turnstile> ?A\<close> in \<open>force+\<close>)
  from prop_5232_aux[OF this prop_5231(1) prop_5231(1)] show "\<turnstile> (T\<^bsub>o\<^esub> \<or>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" .
  from prop_5229(3) have "\<turnstile> \<sim>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<and>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
    by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]" and C = ?A]) (use \<open>\<turnstile> ?A\<close> in \<open>force+\<close>)
  from prop_5232_aux[OF this prop_5231(1) prop_5231(2)] show "\<turnstile> (T\<^bsub>o\<^esub> \<or>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" .
  from prop_5229(2) have "\<turnstile> \<sim>\<^sup>\<Q> (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
    by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]" and C = ?A]) (use \<open>\<turnstile> ?A\<close> in \<open>force+\<close>)
  from prop_5232_aux[OF this prop_5231(2) prop_5231(1)] show "\<turnstile> (F\<^bsub>o\<^esub> \<or>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" .
next
  from prop_5231(1) have "\<turnstile> \<sim>\<^sup>\<Q> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A\<close>) .
  from prop_5229(1) have "\<turnstile> \<sim>\<^sup>\<Q> (T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
    by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]" and C = ?A]) (use \<open>\<turnstile> ?A\<close> in \<open>force+\<close>)
  from prop_5232_aux[OF this prop_5231(2) prop_5231(2)] show "\<turnstile> (F\<^bsub>o\<^esub> \<or>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>" .
qed

end

subsection \<open>Proposition 5233\<close>

context begin

private lemma lem_prop_5233_no_free_vars:
  assumes "A \<in> pwffs" and "free_vars A = {}"
  shows "(\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> A = \<^bold>T) \<longrightarrow> \<turnstile> A =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" (is "?A\<^sub>T \<longrightarrow> _")
  and "(\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> A = \<^bold>F) \<longrightarrow> \<turnstile> A =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>" (is "?A\<^sub>F \<longrightarrow> _")
proof -
  from assms have "(?A\<^sub>T \<longrightarrow> \<turnstile> A =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>) \<and> (?A\<^sub>F \<longrightarrow> \<turnstile> A =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>)"
  proof induction
    case T_pwff
    have "\<turnstile> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
      by (rule prop_5200[OF true_wff])
    moreover have "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> T\<^bsub>o\<^esub> = \<^bold>T"
      using \<V>\<^sub>B_T by blast
    then have "\<not> (\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> T\<^bsub>o\<^esub> = \<^bold>F)"
      by (auto simp: inj_eq)
    ultimately show ?case
      by blast
  next
    case F_pwff
    have "\<turnstile> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
      by (rule prop_5200[OF false_wff])
    moreover have "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> F\<^bsub>o\<^esub> = \<^bold>F"
      using \<V>\<^sub>B_F by blast
    then have "\<not> (\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> F\<^bsub>o\<^esub> = \<^bold>T)"
      by (auto simp: inj_eq)
    ultimately show ?case
      by blast
  next
    case (var_pwff p) \<comment> \<open>impossible case\<close>
    then show ?case
      by simp
  next
    case (neg_pwff B)
    from neg_pwff.hyps have "\<sim>\<^sup>\<Q> B \<in> pwffs" and "free_vars B = {}"
      using neg_pwff.prems by (force, auto elim: free_vars_form.elims)
    consider
      (a) "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> B = \<^bold>T"
    | (b) "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> B = \<^bold>F"
      using closed_pwff_denotation_uniqueness[OF neg_pwff.hyps \<open>free_vars B = {}\<close>]
      and neg_pwff.hyps[THEN \<V>\<^sub>B_graph_denotation_is_truth_value[OF \<V>\<^sub>B_graph_\<V>\<^sub>B]]
      by (auto dest: tv_cases) metis
    then show ?case
    proof cases
      case a
      with \<open>free_vars B = {}\<close> have "\<turnstile> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> B"
        using neg_pwff.IH and Equality_Rules(2) by blast
      from prop_5231(1)[unfolded neg_def, folded equality_of_type_def] and this
      have "\<turnstile> \<sim>\<^sup>\<Q> B =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        unfolding neg_def[folded equality_of_type_def] by (rule rule_R[where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]"]) force+
      moreover from a have "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (\<sim>\<^sup>\<Q> B) = \<^bold>F"
        using \<V>\<^sub>B_neg[OF neg_pwff.hyps] by simp
      ultimately show ?thesis
        by (auto simp: inj_eq)
    next
      case b
      with \<open>free_vars B = {}\<close> have "\<turnstile> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> B"
        using neg_pwff.IH and Equality_Rules(2) by blast
      then have "\<turnstile> \<sim>\<^sup>\<Q> B =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        unfolding neg_def[folded equality_of_type_def]
        using rule_T(2)[OF hyp_derivable_form_is_wffso] by blast
      moreover from b have "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (\<sim>\<^sup>\<Q> B) = \<^bold>T"
        using \<V>\<^sub>B_neg[OF neg_pwff.hyps] by simp
      ultimately show ?thesis
        by (auto simp: inj_eq)
    qed
  next
    case (conj_pwff B C)
    from conj_pwff.prems have "free_vars B = {}" and "free_vars C = {}"
      by simp_all
    with conj_pwff.hyps obtain b and b'
      where B_den: "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> B = b"
      and C_den: "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> C = b'"
      using closed_pwff_denotation_uniqueness by metis
    then have "b \<in> elts \<bool>" and "b' \<in> elts \<bool>"
      using closed_pwff_denotation_uniqueness[OF conj_pwff.hyps(1) \<open>free_vars B = {}\<close>]
      and closed_pwff_denotation_uniqueness[OF conj_pwff.hyps(2) \<open>free_vars C = {}\<close>]
      and conj_pwff.hyps[THEN \<V>\<^sub>B_graph_denotation_is_truth_value[OF \<V>\<^sub>B_graph_\<V>\<^sub>B]]
      by force+
    with conj_pwff.hyps consider
      (a) "b = \<^bold>T" and "b' = \<^bold>T"
    | (b) "b = \<^bold>T" and "b' = \<^bold>F"
    | (c) "b = \<^bold>F" and "b' = \<^bold>T"
    | (d) "b = \<^bold>F" and "b' = \<^bold>F"
      by auto
    then show ?case
    proof cases
      case a
      from prop_5229(1) have "\<turnstile> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A1\<close>) .
      from B_den[unfolded a(1)] and \<open>free_vars B = {}\<close> have "\<turnstile> B =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        using conj_pwff.IH(1) by simp
      then have "\<turnstile> B \<and>\<^sup>\<Q> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"  (is \<open>\<turnstile> ?A2\<close>)
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]" and C = ?A1]) (use \<open>\<turnstile> ?A1\<close> in \<open>force+\<close>)
      from C_den[unfolded a(2)] and \<open>free_vars C = {}\<close> have "\<turnstile> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        using conj_pwff.IH(2) by simp
      then have "\<turnstile> B \<and>\<^sup>\<Q> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]" and C = ?A2]) (use \<open>\<turnstile> ?A2\<close> in \<open>force+\<close>)
      then have "(\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<and>\<^sup>\<Q> C) = \<^bold>T) \<longrightarrow> \<turnstile> B \<and>\<^sup>\<Q> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        by blast
      moreover have "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<and>\<^sup>\<Q> C) \<noteq> \<^bold>F"
        using \<V>\<^sub>B_conj[OF conj_pwff.hyps] and B_den[unfolded a(1)] and C_den[unfolded a(2)]
        by (auto simp: inj_eq)
      ultimately show ?thesis
        by force
    next
      case b
      from prop_5229(2) have "\<turnstile> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A1\<close>) .
      from B_den[unfolded b(1)] and \<open>free_vars B = {}\<close> have "\<turnstile> B =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        using conj_pwff.IH(1) by simp
      then have "\<turnstile> B \<and>\<^sup>\<Q> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"  (is \<open>\<turnstile> ?A2\<close>)
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]" and C = ?A1]) (use \<open>\<turnstile> ?A1\<close> in \<open>force+\<close>)
      from C_den[unfolded b(2)] and \<open>free_vars C = {}\<close> have "\<turnstile> C =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        using conj_pwff.IH(2) by simp
      then have "\<turnstile> B \<and>\<^sup>\<Q> C =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]" and C = ?A2]) (use \<open>\<turnstile> ?A2\<close> in \<open>force+\<close>)
      then have "(\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<and>\<^sup>\<Q> C) = \<^bold>F) \<longrightarrow> \<turnstile> B \<and>\<^sup>\<Q> C =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        by blast
      moreover have "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<and>\<^sup>\<Q> C) \<noteq> \<^bold>T"
        using \<V>\<^sub>B_conj[OF conj_pwff.hyps] and B_den[unfolded b(1)] and C_den[unfolded b(2)]
        by (auto simp: inj_eq)
      ultimately show ?thesis
        by force
    next
      case c
      from prop_5229(3) have "\<turnstile> F\<^bsub>o\<^esub> \<and>\<^sup>\<Q> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A1\<close>) .
      from B_den[unfolded c(1)] and \<open>free_vars B = {}\<close> have "\<turnstile> B =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        using conj_pwff.IH(1) by simp
      then have "\<turnstile> B \<and>\<^sup>\<Q> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"  (is \<open>\<turnstile> ?A2\<close>)
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]" and C = ?A1]) (use \<open>\<turnstile> ?A1\<close> in \<open>force+\<close>)
      from C_den[unfolded c(2)] and \<open>free_vars C = {}\<close> have "\<turnstile> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        using conj_pwff.IH(2) by simp
      then have "\<turnstile> B \<and>\<^sup>\<Q> C =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]" and C = ?A2]) (use \<open>\<turnstile> ?A2\<close> in \<open>force+\<close>)
      then have "(\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<and>\<^sup>\<Q> C) = \<^bold>F) \<longrightarrow> \<turnstile> B \<and>\<^sup>\<Q> C =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        by blast
      moreover have "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<and>\<^sup>\<Q> C) \<noteq> \<^bold>T"
        using \<V>\<^sub>B_conj[OF conj_pwff.hyps] and B_den[unfolded c(1)] and C_den[unfolded c(2)]
        by (auto simp: inj_eq)
      ultimately show ?thesis
        by force
    next
      case d
      from prop_5229(4) have "\<turnstile> F\<^bsub>o\<^esub> \<and>\<^sup>\<Q> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A1\<close>) .
      from B_den[unfolded d(1)] and \<open>free_vars B = {}\<close> have "\<turnstile> B =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        using conj_pwff.IH(1) by simp
      then have "\<turnstile> B \<and>\<^sup>\<Q> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"  (is \<open>\<turnstile> ?A2\<close>)
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]" and C = ?A1]) (use \<open>\<turnstile> ?A1\<close> in \<open>force+\<close>)
      from C_den[unfolded d(2)] and \<open>free_vars C = {}\<close> have "\<turnstile> C =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        using conj_pwff.IH(2) by simp
      then have "\<turnstile> B \<and>\<^sup>\<Q> C =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]" and C = ?A2]) (use \<open>\<turnstile> ?A2\<close> in \<open>force+\<close>)
      then have "(\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<and>\<^sup>\<Q> C) = \<^bold>F) \<longrightarrow> \<turnstile> B \<and>\<^sup>\<Q> C =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        by blast
      moreover have "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<and>\<^sup>\<Q> C) \<noteq> \<^bold>T"
        using \<V>\<^sub>B_conj[OF conj_pwff.hyps] and B_den[unfolded d(1)] and C_den[unfolded d(2)]
        by (auto simp: inj_eq)
      ultimately show ?thesis
        by force
    qed
  next
    case (disj_pwff B C)
    from disj_pwff.prems have "free_vars B = {}" and "free_vars C = {}"
      by simp_all
    with disj_pwff.hyps obtain b and b'
      where B_den: "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> B = b"
      and C_den: "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> C = b'"
      using closed_pwff_denotation_uniqueness by metis
    then have "b \<in> elts \<bool>" and "b' \<in> elts \<bool>"
      using closed_pwff_denotation_uniqueness[OF disj_pwff.hyps(1) \<open>free_vars B = {}\<close>]
      and closed_pwff_denotation_uniqueness[OF disj_pwff.hyps(2) \<open>free_vars C = {}\<close>]
      and disj_pwff.hyps[THEN \<V>\<^sub>B_graph_denotation_is_truth_value[OF \<V>\<^sub>B_graph_\<V>\<^sub>B]]
      by force+
    with disj_pwff.hyps consider
      (a) "b = \<^bold>T" and "b' = \<^bold>T"
    | (b) "b = \<^bold>T" and "b' = \<^bold>F"
    | (c) "b = \<^bold>F" and "b' = \<^bold>T"
    | (d) "b = \<^bold>F" and "b' = \<^bold>F"
      by auto
    then show ?case
    proof cases
      case a
      from prop_5232(1) have "\<turnstile> T\<^bsub>o\<^esub> \<or>\<^sup>\<Q> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A1\<close>) .
      from B_den[unfolded a(1)] and \<open>free_vars B = {}\<close> have "\<turnstile> B =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        using disj_pwff.IH(1) by simp
      then have "\<turnstile> B \<or>\<^sup>\<Q> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A2\<close>)
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]" and C = ?A1]) (use \<open>\<turnstile> ?A1\<close> in \<open>force+\<close>)
      from C_den[unfolded a(2)] and \<open>free_vars C = {}\<close> have "\<turnstile> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        using disj_pwff.IH(2) by simp
      then have "\<turnstile> B \<or>\<^sup>\<Q> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]" and C = ?A2]) (use \<open>\<turnstile> ?A2\<close> in \<open>force+\<close>)
      then have "(\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<or>\<^sup>\<Q> C) = \<^bold>T) \<longrightarrow> \<turnstile> B \<or>\<^sup>\<Q> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        by blast
      moreover have "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<or>\<^sup>\<Q> C) \<noteq> \<^bold>F"
        using \<V>\<^sub>B_disj[OF disj_pwff.hyps] and B_den[unfolded a(1)] and C_den[unfolded a(2)]
        by (auto simp: inj_eq)
      ultimately show ?thesis
        by force
    next
      case b
      from prop_5232(2) have "\<turnstile> T\<^bsub>o\<^esub> \<or>\<^sup>\<Q> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A1\<close>) .
      from B_den[unfolded b(1)] and \<open>free_vars B = {}\<close> have "\<turnstile> B =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        using disj_pwff.IH(1) by simp
      then have "\<turnstile> B \<or>\<^sup>\<Q> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A2\<close>)
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]" and C = ?A1]) (use \<open>\<turnstile> ?A1\<close> in \<open>force+\<close>)
      from C_den[unfolded b(2)] and \<open>free_vars C = {}\<close> have "\<turnstile> C =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        using disj_pwff.IH(2) by simp
      then have "\<turnstile> B \<or>\<^sup>\<Q> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]" and C = ?A2]) (use \<open>\<turnstile> ?A2\<close> in \<open>force+\<close>)
      then have "(\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<or>\<^sup>\<Q> C) = \<^bold>T) \<longrightarrow> \<turnstile> B \<or>\<^sup>\<Q> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        by blast
      moreover have "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<or>\<^sup>\<Q> C) \<noteq> \<^bold>F"
        using \<V>\<^sub>B_disj[OF disj_pwff.hyps] and B_den[unfolded b(1)] and C_den[unfolded b(2)]
        by (auto simp: inj_eq)
      ultimately show ?thesis
        by force
    next
      case c
      from prop_5232(3) have "\<turnstile> F\<^bsub>o\<^esub> \<or>\<^sup>\<Q> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A1\<close>) .
      from B_den[unfolded c(1)] and \<open>free_vars B = {}\<close> have "\<turnstile> B =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        using disj_pwff.IH(1) by simp
      then have "\<turnstile> B \<or>\<^sup>\<Q> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"  (is \<open>\<turnstile> ?A2\<close>)
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]" and C = ?A1]) (use \<open>\<turnstile> ?A1\<close> in \<open>force+\<close>)
      from C_den[unfolded c(2)] and \<open>free_vars C = {}\<close> have "\<turnstile> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        using disj_pwff.IH(2) by simp
      then have "\<turnstile> B \<or>\<^sup>\<Q> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]" and C = ?A2]) (use \<open>\<turnstile> ?A2\<close> in \<open>force+\<close>)
      then have "(\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<or>\<^sup>\<Q> C) = \<^bold>T) \<longrightarrow> \<turnstile> B \<or>\<^sup>\<Q> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        by blast
      moreover have "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<or>\<^sup>\<Q> C) \<noteq> \<^bold>F"
        using \<V>\<^sub>B_disj[OF disj_pwff.hyps] and B_den[unfolded c(1)] and C_den[unfolded c(2)]
        by (auto simp: inj_eq)
      ultimately show ?thesis
        by force
    next
      case d
      from prop_5232(4) have "\<turnstile> F\<^bsub>o\<^esub> \<or>\<^sup>\<Q> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A1\<close>) .
      from B_den[unfolded d(1)] and \<open>free_vars B = {}\<close> have "\<turnstile> B =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        using disj_pwff.IH(1) by simp
      then have "\<turnstile> B \<or>\<^sup>\<Q> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A2\<close>)
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]" and C = ?A1]) (use \<open>\<turnstile> ?A1\<close> in \<open>force+\<close>)
      from C_den[unfolded d(2)] and \<open>free_vars C = {}\<close> have "\<turnstile> C =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        using disj_pwff.IH(2) by simp
      then have "\<turnstile> B \<or>\<^sup>\<Q> C =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]" and C = ?A2]) (use \<open>\<turnstile> ?A2\<close> in \<open>force+\<close>)
      then have "(\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<or>\<^sup>\<Q> C) = \<^bold>T) \<longrightarrow> \<turnstile> B \<or>\<^sup>\<Q> C =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        by blast
      moreover have "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<or>\<^sup>\<Q> C) \<noteq> \<^bold>T"
        using \<V>\<^sub>B_disj[OF disj_pwff.hyps] and B_den[unfolded d(1)] and C_den[unfolded d(2)]
        by (auto simp: inj_eq)
      ultimately show ?thesis
        using \<open>\<turnstile> B \<or>\<^sup>\<Q> C =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>\<close> by auto
    qed
  next
    case (imp_pwff B C)
    from imp_pwff.prems have "free_vars B = {}" and "free_vars C = {}"
      by simp_all
    with imp_pwff.hyps obtain b and b'
      where B_den: "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> B = b"
      and C_den: "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> C = b'"
      using closed_pwff_denotation_uniqueness by metis
    then have "b \<in> elts \<bool>" and "b' \<in> elts \<bool>"
      using closed_pwff_denotation_uniqueness[OF imp_pwff.hyps(1) \<open>free_vars B = {}\<close>]
      and closed_pwff_denotation_uniqueness[OF imp_pwff.hyps(2) \<open>free_vars C = {}\<close>]
      and imp_pwff.hyps[THEN \<V>\<^sub>B_graph_denotation_is_truth_value[OF \<V>\<^sub>B_graph_\<V>\<^sub>B]]
      by force+
    with imp_pwff.hyps consider
      (a) "b = \<^bold>T" and "b' = \<^bold>T"
    | (b) "b = \<^bold>T" and "b' = \<^bold>F"
    | (c) "b = \<^bold>F" and "b' = \<^bold>T"
    | (d) "b = \<^bold>F" and "b' = \<^bold>F"
      by auto
    then show ?case
    proof cases
      case a
      from prop_5228(1) have "\<turnstile> T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A1\<close>) .
      from B_den[unfolded a(1)] and \<open>free_vars B = {}\<close> have "\<turnstile> B =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        using imp_pwff.IH(1) by simp
      then have "\<turnstile> B \<supset>\<^sup>\<Q> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A2\<close>)
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]" and C = ?A1]) (use \<open>\<turnstile> ?A1\<close> in \<open>force+\<close>)
      from C_den[unfolded a(2)] and \<open>free_vars C = {}\<close> have "\<turnstile> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        using imp_pwff.IH(2) by simp
      then have "\<turnstile> B \<supset>\<^sup>\<Q> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]" and C = ?A2]) (use \<open>\<turnstile> ?A2\<close> in \<open>force+\<close>)
      then have "(\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<supset>\<^sup>\<Q> C) = \<^bold>T) \<longrightarrow> \<turnstile> B \<supset>\<^sup>\<Q> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        by blast
      moreover have "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<supset>\<^sup>\<Q> C) \<noteq> \<^bold>F"
        using \<V>\<^sub>B_imp[OF imp_pwff.hyps] and B_den[unfolded a(1)] and C_den[unfolded a(2)]
        by (auto simp: inj_eq)
      ultimately show ?thesis
        by force
    next
      case b
      from prop_5228(2) have "\<turnstile> T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A1\<close>) .
      from B_den[unfolded b(1)] and \<open>free_vars B = {}\<close> have "\<turnstile> B =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        using imp_pwff.IH(1) by simp
      then have "\<turnstile> B \<supset>\<^sup>\<Q> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A2\<close>)
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]" and C = ?A1]) (use \<open>\<turnstile> ?A1\<close> in \<open>force+\<close>)
      from C_den[unfolded b(2)] and \<open>free_vars C = {}\<close> have "\<turnstile> C =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        using imp_pwff.IH(2) by simp
      then have "\<turnstile> B \<supset>\<^sup>\<Q> C =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]" and C = ?A2]) (use \<open>\<turnstile> ?A2\<close> in \<open>force+\<close>)
      then have "(\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<supset>\<^sup>\<Q> C) = \<^bold>F) \<longrightarrow> \<turnstile> B \<supset>\<^sup>\<Q> C =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        by blast
      moreover have "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<supset>\<^sup>\<Q> C) \<noteq> \<^bold>T"
        using \<V>\<^sub>B_imp[OF imp_pwff.hyps] and B_den[unfolded b(1)] and C_den[unfolded b(2)]
        by (auto simp: inj_eq)
      ultimately show ?thesis
        by force
    next
      case c
      from prop_5228(3) have "\<turnstile> F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A1\<close>) .
      from B_den[unfolded c(1)] and \<open>free_vars B = {}\<close> have "\<turnstile> B =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        using imp_pwff.IH(1) by simp
      then have "\<turnstile> B \<supset>\<^sup>\<Q> T\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A2\<close>)
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]" and C = ?A1]) (use \<open>\<turnstile> ?A1\<close> in \<open>force+\<close>)
      from C_den[unfolded c(2)] and \<open>free_vars C = {}\<close> have "\<turnstile> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        using imp_pwff.IH(2) by simp
      then have "\<turnstile> B \<supset>\<^sup>\<Q> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]" and C = ?A2]) (use \<open>\<turnstile> ?A2\<close> in \<open>force+\<close>)
      then have "(\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<supset>\<^sup>\<Q> C) = \<^bold>T) \<longrightarrow> \<turnstile> B \<supset>\<^sup>\<Q> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        by blast
      moreover have "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<supset>\<^sup>\<Q> C) \<noteq> \<^bold>F"
        using \<V>\<^sub>B_imp[OF imp_pwff.hyps] and B_den[unfolded c(1)] and C_den[unfolded c(2)]
        by (auto simp: inj_eq)
      ultimately show ?thesis
        by force
    next
      case d
      from prop_5228(4) have "\<turnstile> F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A1\<close>) .
      from B_den[unfolded d(1)] and \<open>free_vars B = {}\<close> have "\<turnstile> B =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        using imp_pwff.IH(1) by simp
      then have "\<turnstile> B \<supset>\<^sup>\<Q> F\<^bsub>o\<^esub> =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A2\<close>)
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]" and C = ?A1]) (use \<open>\<turnstile> ?A1\<close> in \<open>force+\<close>)
      from C_den[unfolded d(2)] and \<open>free_vars C = {}\<close> have "\<turnstile> C =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        using imp_pwff.IH(2) by simp
      then have "\<turnstile> B \<supset>\<^sup>\<Q> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]" and C = ?A2]) (use \<open>\<turnstile> ?A2\<close> in \<open>force+\<close>)
      then have "(\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<supset>\<^sup>\<Q> C) = \<^bold>T) \<longrightarrow> \<turnstile> B \<supset>\<^sup>\<Q> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        by blast
      moreover have "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<supset>\<^sup>\<Q> C) \<noteq> \<^bold>F"
        using \<V>\<^sub>B_imp[OF imp_pwff.hyps] and B_den[unfolded d(1)] and C_den[unfolded d(2)]
        by (auto simp: inj_eq)
      ultimately show ?thesis
        by force
    qed
  next
    case (eqv_pwff B C)
    from eqv_pwff.prems have "free_vars B = {}" and "free_vars C = {}"
      by simp_all
    with eqv_pwff.hyps obtain b and b'
      where B_den: "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> B = b"
      and C_den: "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> C = b'"
      using closed_pwff_denotation_uniqueness by metis
    then have "b \<in> elts \<bool>" and "b' \<in> elts \<bool>"
      using closed_pwff_denotation_uniqueness[OF eqv_pwff.hyps(1) \<open>free_vars B = {}\<close>]
      and closed_pwff_denotation_uniqueness[OF eqv_pwff.hyps(2) \<open>free_vars C = {}\<close>]
      and eqv_pwff.hyps[THEN \<V>\<^sub>B_graph_denotation_is_truth_value[OF \<V>\<^sub>B_graph_\<V>\<^sub>B]]
      by force+
    with eqv_pwff.hyps consider
      (a) "b = \<^bold>T" and "b' = \<^bold>T"
    | (b) "b = \<^bold>T" and "b' = \<^bold>F"
    | (c) "b = \<^bold>F" and "b' = \<^bold>T"
    | (d) "b = \<^bold>F" and "b' = \<^bold>F"
      by auto
    then show ?case
    proof cases
      case a
      from prop_5230(1) have "\<turnstile> (T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A1\<close>) .
      from B_den[unfolded a(1)] and \<open>free_vars B = {}\<close> have "\<turnstile> B =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        using eqv_pwff.IH(1) by simp
      then have "\<turnstile> (B \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A2\<close>)
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]" and C = ?A1]) (use \<open>\<turnstile> ?A1\<close> in \<open>force+\<close>)
      from C_den[unfolded a(2)] and \<open>free_vars C = {}\<close> have "\<turnstile> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        using eqv_pwff.IH(2) by simp
      then have "\<turnstile> (B \<equiv>\<^sup>\<Q> C) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]" and C = ?A2]) (use \<open>\<turnstile> ?A2\<close> in \<open>force+\<close>)
      then have "(\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<equiv>\<^sup>\<Q> C) = \<^bold>T) \<longrightarrow> \<turnstile> (B \<equiv>\<^sup>\<Q> C) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        by blast
      moreover have "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<equiv>\<^sup>\<Q> C) \<noteq> \<^bold>F"
        using \<V>\<^sub>B_eqv[OF eqv_pwff.hyps] and B_den[unfolded a(1)] and C_den[unfolded a(2)]
        by (auto simp: inj_eq)
      ultimately show ?thesis
        by force
    next
      case b
      from prop_5230(2) have "\<turnstile> (T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A1\<close>) .
      from B_den[unfolded b(1)] and \<open>free_vars B = {}\<close> have "\<turnstile> B =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        using eqv_pwff.IH(1) by simp
      then have "\<turnstile> (B \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A2\<close>)
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]" and C = ?A1]) (use \<open>\<turnstile> ?A1\<close> in \<open>force+\<close>)
      from C_den[unfolded b(2)] and \<open>free_vars C = {}\<close> have "\<turnstile> C =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        using eqv_pwff.IH(2) by simp
      then have "\<turnstile> (B \<equiv>\<^sup>\<Q> C) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]" and C = ?A2]) (use \<open>\<turnstile> ?A2\<close> in \<open>force+\<close>)
      then have "(\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<equiv>\<^sup>\<Q> C) = \<^bold>F) \<longrightarrow> \<turnstile> (B \<equiv>\<^sup>\<Q> C) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        by blast
      moreover have "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<equiv>\<^sup>\<Q> C) \<noteq> \<^bold>T"
        using \<V>\<^sub>B_eqv[OF eqv_pwff.hyps] and B_den[unfolded b(1)] and C_den[unfolded b(2)]
        by (auto simp: inj_eq)
      ultimately show ?thesis
        by force
    next
      case c
      from prop_5230(3) have "\<turnstile> (F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A1\<close>) .
      from B_den[unfolded c(1)] and \<open>free_vars B = {}\<close> have "\<turnstile> B =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        using eqv_pwff.IH(1) by simp
      then have "\<turnstile> (B \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A2\<close>)
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]" and C = ?A1]) (use \<open>\<turnstile> ?A1\<close> in \<open>force+\<close>)
      from C_den[unfolded c(2)] and \<open>free_vars C = {}\<close> have "\<turnstile> C =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        using eqv_pwff.IH(2) by simp
      then have "\<turnstile> (B \<equiv>\<^sup>\<Q> C) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]" and C = ?A2]) (use \<open>\<turnstile> ?A2\<close> in \<open>force+\<close>)
      then have "(\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<equiv>\<^sup>\<Q> C) = \<^bold>F) \<longrightarrow> \<turnstile> (B \<equiv>\<^sup>\<Q> C) =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        by blast
      moreover have "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<equiv>\<^sup>\<Q> C) \<noteq> \<^bold>T"
        using \<V>\<^sub>B_eqv[OF eqv_pwff.hyps] and B_den[unfolded c(1)] and C_den[unfolded c(2)]
        by (auto simp: inj_eq)
      ultimately show ?thesis
        by force
    next
      case d
      from prop_5230(4) have "\<turnstile> (F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A1\<close>) .
      from B_den[unfolded d(1)] and \<open>free_vars B = {}\<close> have "\<turnstile> B =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        using eqv_pwff.IH(1) by simp
      then have "\<turnstile> (B \<equiv>\<^sup>\<Q> F\<^bsub>o\<^esub>) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" (is \<open>\<turnstile> ?A2\<close>)
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]" and C = ?A1]) (use \<open>\<turnstile> ?A1\<close> in \<open>force+\<close>)
      from C_den[unfolded d(2)] and \<open>free_vars C = {}\<close> have "\<turnstile> C =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
        using eqv_pwff.IH(2) by simp
      then have "\<turnstile> (B \<equiv>\<^sup>\<Q> C) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        by (rule rule_RR[OF disjI2, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>]" and C = ?A2]) (use \<open>\<turnstile> ?A2\<close> in \<open>force+\<close>)
      then have "(\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<equiv>\<^sup>\<Q> C) = \<^bold>T) \<longrightarrow> \<turnstile> (B \<equiv>\<^sup>\<Q> C) =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
        by blast
      moreover have "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> (B \<equiv>\<^sup>\<Q> C) \<noteq> \<^bold>F"
        using \<V>\<^sub>B_eqv[OF eqv_pwff.hyps] and B_den[unfolded d(1)] and C_den[unfolded d(2)]
        by (auto simp: inj_eq)
      ultimately show ?thesis
        by force
    qed
  qed
  then show "?A\<^sub>T \<longrightarrow> \<turnstile> A =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>" and "?A\<^sub>F \<longrightarrow> \<turnstile> A =\<^bsub>o\<^esub> F\<^bsub>o\<^esub>"
    by blast+
qed

proposition prop_5233:
  assumes "is_tautology A"
  shows "\<turnstile> A"
proof -
  have "finite (free_vars A)"
    using free_vars_form_finiteness by presburger
  from this and assms show ?thesis
  proof (induction "free_vars A" arbitrary: A)
    case empty
    from empty(2) have "A \<in> pwffs" and "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> A = \<^bold>T"
      unfolding is_tautology_def by blast+
    with empty(1) have "\<turnstile> A =\<^bsub>o\<^esub> T\<^bsub>o\<^esub>"
      using lem_prop_5233_no_free_vars(1) by (simp only:)
    then show ?case
      using rule_T(2)[OF tautology_is_wffo[OF empty(2)]] by (simp only:)
  next
    case (insert v F)
    from insert.prems have "A \<in> pwffs"
      by blast
    with insert.hyps(4) obtain p where "v = (p, o)"
      using pwffs_free_vars_are_propositional by blast
    from \<open>v = (p, o)\<close> and insert.hyps(4) have "
      is_tautology (\<^bold>S {(p, o) \<Zinj> T\<^bsub>o\<^esub>} A)" and "is_tautology (\<^bold>S {(p, o) \<Zinj> F\<^bsub>o\<^esub>} A)"
      using pwff_substitution_tautology_preservation [OF insert.prems] by blast+
    moreover from insert.hyps(2,4) and \<open>v = (p, o)\<close> and \<open>A \<in> pwffs\<close>
    have "free_vars (\<^bold>S {(p, o) \<Zinj> T\<^bsub>o\<^esub>} A) = F" and "free_vars (\<^bold>S {(p, o) \<Zinj> F\<^bsub>o\<^esub>} A) = F"
      using closed_pwff_substitution_free_vars and T_pwff and F_pwff and T_fv and F_fv
      by (metis Diff_insert_absorb insertI1)+
    ultimately have "\<turnstile> \<^bold>S {(p, o) \<Zinj> T\<^bsub>o\<^esub>} A" and "\<turnstile> \<^bold>S {(p, o) \<Zinj> F\<^bsub>o\<^esub>} A"
      using insert.hyps(3) by (simp_all only:)
    from this and tautology_is_wffo[OF insert.prems] show ?case
      by (rule Cases)
  qed
qed

end

subsection \<open>Proposition 5234 (Rule P)\<close>

text \<open>
  According to the proof in @{cite "andrews:2002"}, if $[A^1 \wedge \dots \wedge A^n] \supset B$ is
  tautologous, then clearly $A^1 \supset (\dots (A^n \supset B) \dots)$ is also tautologous.
  Since this is not clear to us, we prove instead the version of Rule P found in @{cite "andrews:1965"}:
\<close>

proposition tautologous_horn_clause_is_hyp_derivable:
  assumes "is_hyps \<H>" and "is_hyps \<G>"
  and "\<forall>A \<in> \<G>. \<H> \<turnstile> A"
  and "lset hs = \<G>"
  and "is_tautologous (hs \<supset>\<^sup>\<Q>\<^sub>\<star> B)"
  shows "\<H> \<turnstile> B"
proof -
  from assms(5) obtain \<theta> and C
    where "is_tautology C"
    and "is_substitution \<theta>"
    and "\<forall>(x, \<alpha>) \<in> fmdom' \<theta>. \<alpha> = o"
    and "hs \<supset>\<^sup>\<Q>\<^sub>\<star> B = \<^bold>S \<theta> C"
    by blast
  then have "\<turnstile> hs \<supset>\<^sup>\<Q>\<^sub>\<star> B"
  proof (cases "\<theta> = {$$}")
    case True
    with \<open>hs \<supset>\<^sup>\<Q>\<^sub>\<star> B = \<^bold>S \<theta> C\<close> have "C = hs \<supset>\<^sup>\<Q>\<^sub>\<star> B"
      using empty_substitution_neutrality by simp
    with \<open>hs \<supset>\<^sup>\<Q>\<^sub>\<star> B = \<^bold>S \<theta> C\<close> and \<open>is_tautology C\<close> show ?thesis
      using prop_5233 by (simp only:)
  next
    case False
    from \<open>is_tautology C\<close> have "\<turnstile> C" and "C \<in> pwffs"
      using prop_5233 by simp_all
    moreover have "
      \<forall>v \<in> fmdom' \<theta>. var_name v \<notin> free_var_names ({}::form set) \<and> is_free_for (\<theta> $$! v) v C"
    proof
      fix v
      assume "v \<in> fmdom' \<theta>"
      then show "var_name v \<notin> free_var_names ({}::form set) \<and> is_free_for (\<theta> $$! v) v C"
      proof (cases "v \<in> free_vars C")
        case True
        with \<open>C \<in> pwffs\<close> show ?thesis
          using is_free_for_in_pwff by simp
      next
        case False
        then have "is_free_for (\<theta> $$! v) v C"
          unfolding is_free_for_def using is_free_at_in_free_vars by blast
        then show ?thesis
          by simp
      qed
    qed
    ultimately show ?thesis
      using False and \<open>is_substitution \<theta>\<close> and Sub
      by (simp add: \<open>hs \<supset>\<^sup>\<Q>\<^sub>\<star> B = \<^bold>S \<theta> C\<close>[unfolded generalized_imp_op_def])
  qed
  from this and assms(1) have "\<H> \<turnstile> hs \<supset>\<^sup>\<Q>\<^sub>\<star> B"
    by (rule derivability_implies_hyp_derivability)
  with assms(3,4) show ?thesis
    using generalized_modus_ponens by blast
qed

corollary tautologous_is_hyp_derivable:
  assumes "is_hyps \<H>"
  and "is_tautologous B"
  shows "\<H> \<turnstile> B"
  using assms and tautologous_horn_clause_is_hyp_derivable[where \<G> = "{}"] by simp

lemmas prop_5234 = tautologous_horn_clause_is_hyp_derivable tautologous_is_hyp_derivable

lemmas rule_P = prop_5234 (* synonym *)

subsection \<open>Proposition 5235\<close>

proposition prop_5235:
  assumes "A \<in> pwffs" and "B \<in> pwffs"
  and "(x, \<alpha>) \<notin> free_vars A"
  shows "\<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. (A \<or>\<^sup>\<Q> B) \<supset>\<^sup>\<Q> (A \<or>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. B)"
proof -
  have "\<section>1": "\<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. (T\<^bsub>o\<^esub> \<or>\<^sup>\<Q> B) \<supset>\<^sup>\<Q> (T\<^bsub>o\<^esub> \<or>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. B)"
  proof (intro rule_P(2))
    show "is_tautologous (\<forall>x\<^bsub>\<alpha>\<^esub>. (T\<^bsub>o\<^esub> \<or>\<^sup>\<Q> B) \<supset>\<^sup>\<Q> T\<^bsub>o\<^esub> \<or>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. B)"
    proof -
      let ?\<theta> = "{(\<xx>, o) \<Zinj> \<forall>x\<^bsub>\<alpha>\<^esub>. (T\<^bsub>o\<^esub> \<or>\<^sup>\<Q> B), (\<yy>, o) \<Zinj> \<forall>x\<^bsub>\<alpha>\<^esub>. B}" and ?C = "\<xx>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> (T\<^bsub>o\<^esub> \<or>\<^sup>\<Q> (\<yy>\<^bsub>o\<^esub>))"
      have "is_tautology ?C"
        using \<V>\<^sub>B_simps by simp
      moreover from assms(2) have "is_pwff_substitution ?\<theta>"
        using pwffs_subset_of_wffso by fastforce
      moreover have "\<forall>x\<^bsub>\<alpha>\<^esub>. (T\<^bsub>o\<^esub> \<or>\<^sup>\<Q> B) \<supset>\<^sup>\<Q> T\<^bsub>o\<^esub> \<or>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. B = \<^bold>S ?\<theta> ?C"
        by simp
      ultimately show ?thesis
        by blast
    qed
  qed simp
  have "\<section>2": "\<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. B \<supset>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<or>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. B)"
  proof (intro rule_P(2))
    show "is_tautologous (\<forall>x\<^bsub>\<alpha>\<^esub>. B \<supset>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<or>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. B))"
    proof -
      let ?\<theta> = "{(\<xx>, o) \<Zinj> \<forall>x\<^bsub>\<alpha>\<^esub>. B}" and ?C = "\<xx>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<or>\<^sup>\<Q> (\<xx>\<^bsub>o\<^esub>))"
      have "is_tautology (\<xx>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<or>\<^sup>\<Q> (\<xx>\<^bsub>o\<^esub>)))" (is \<open>is_tautology ?C\<close>)
        using \<V>\<^sub>B_simps by simp
      moreover from assms(2) have "is_pwff_substitution ?\<theta>"
        using pwffs_subset_of_wffso by auto
      moreover have "\<forall>x\<^bsub>\<alpha>\<^esub>. B \<supset>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<or>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. B) = \<^bold>S ?\<theta> ?C"
        by simp
      ultimately show ?thesis
        by blast
    qed
  qed simp
  have "\<section>3": "\<turnstile> B \<equiv>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<or>\<^sup>\<Q> B)"
  proof (intro rule_P(2))
    show "is_tautologous (B \<equiv>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<or>\<^sup>\<Q> B))"
    proof -
      let ?\<theta> = "{(\<xx>, o) \<Zinj> B}" and ?C = "\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<or>\<^sup>\<Q> (\<xx>\<^bsub>o\<^esub>))"
      have "is_tautology ?C"
        using \<V>\<^sub>B_simps by simp
      moreover from assms(2) have "is_pwff_substitution ?\<theta>"
        using pwffs_subset_of_wffso by auto
      moreover have "B \<equiv>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<or>\<^sup>\<Q> B) = \<^bold>S ?\<theta> ?C"
        by simp
      ultimately show ?thesis
        by blast
    qed
  qed simp
  from "\<section>2" and "\<section>3"[unfolded equivalence_def] have "\<section>4":
    "\<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. (F\<^bsub>o\<^esub> \<or>\<^sup>\<Q> B) \<supset>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<or>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. B)"
    by (rule rule_R[where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>,\<guillemotleft>]"]) force+
  obtain p where "(p, o) \<notin> vars (\<forall>x\<^bsub>\<alpha>\<^esub>. (A \<or>\<^sup>\<Q> B) \<supset>\<^sup>\<Q> (A \<or>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. B))"
    by (meson fresh_var_existence vars_form_finiteness)
  then have "(p, o) \<noteq> (x, \<alpha>)" and "(p, o) \<notin> vars A" and "(p, o) \<notin> vars B"
    by simp_all
  from \<open>(p, o) \<notin> vars B\<close> have sub: "\<^bold>S {(p, o) \<Zinj> C} B = B" for C
    using free_var_singleton_substitution_neutrality and free_vars_in_all_vars by blast
  have "\<section>5": "\<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. (p\<^bsub>o\<^esub> \<or>\<^sup>\<Q> B) \<supset>\<^sup>\<Q> (p\<^bsub>o\<^esub> \<or>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. B)" (is \<open>\<turnstile> ?C\<close>)
  proof -
    from sub and "\<section>1" have "\<turnstile> \<^bold>S {(p, o) \<Zinj> T\<^bsub>o\<^esub>} ?C"
      using \<open>(p, o) \<noteq> (x, \<alpha>)\<close> by auto
    moreover from sub and "\<section>4" have "\<turnstile> \<^bold>S {(p, o) \<Zinj> F\<^bsub>o\<^esub>} ?C"
      using \<open>(p, o) \<noteq> (x, \<alpha>)\<close> by auto
    moreover from assms(2) have "?C \<in> wffs\<^bsub>o\<^esub>"
      using pwffs_subset_of_wffso by auto
    ultimately show ?thesis
      by (rule Cases)
  qed
  then show ?thesis
  proof -
    let ?\<theta> = "{(p, o) \<Zinj> A}"
    from assms(1) have "is_substitution ?\<theta>"
      using pwffs_subset_of_wffso by auto
    moreover have "
      \<forall>v \<in> fmdom' ?\<theta>. var_name v \<notin> free_var_names ({}::form set) \<and> is_free_for (?\<theta> $$! v) v ?C"
    proof
      fix v
      assume "v \<in> fmdom' ?\<theta>"
      then have "v = (p, o)"
        by simp
      with assms(3) and \<open>(p, o) \<notin> vars B\<close> have "is_free_for (?\<theta> $$! v) v ?C"
        using occurs_in_vars
        by (intro is_free_for_in_imp is_free_for_in_forall is_free_for_in_disj) auto
      moreover have "var_name v \<notin> free_var_names ({}::form set)"
        by simp
      ultimately show "var_name v \<notin> free_var_names ({}::form set) \<and> is_free_for (?\<theta> $$! v) v ?C"
        unfolding \<open>v = (p, o)\<close> by blast
    qed
    moreover have "?\<theta> \<noteq> {$$}"
      by simp
    ultimately have "\<turnstile> \<^bold>S ?\<theta> ?C"
      by (rule Sub[OF "\<section>5"])
    moreover have "\<^bold>S ?\<theta> ?C = \<forall>x\<^bsub>\<alpha>\<^esub>. (A \<or>\<^sup>\<Q> B) \<supset>\<^sup>\<Q> (A \<or>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. B)"
      using \<open>(p, o) \<noteq> (x, \<alpha>)\<close> and sub[of A] by simp fast
    ultimately show ?thesis
      by (simp only:)
  qed
qed

subsection \<open>Proposition 5237 ($\supset \forall$ Rule)\<close>

text \<open>
  The proof in @{cite "andrews:2002"} uses the pseudo-rule Q and the axiom 5 of \<open>\<F>\<close>. Therefore, we
  prove such axiom, following the proof of Theorem 143 in @{cite "andrews:1965"}:
\<close>

context begin

private lemma prop_5237_aux:
  assumes "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
  and "(x, \<alpha>) \<notin> free_vars A"
  shows "\<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. (A \<supset>\<^sup>\<Q> B) \<equiv>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> (\<forall>x\<^bsub>\<alpha>\<^esub>. B))"
proof -
  have "is_tautology (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> (T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub>))" (is \<open>is_tautology ?C\<^sub>1\<close>)
    using \<V>\<^sub>B_simps by simp
  have "is_tautology (\<xx>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)))" (is \<open>is_tautology ?C\<^sub>2\<close>)
    using \<V>\<^sub>B_simps by simp
  have "\<section>1": "\<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. B \<equiv>\<^sup>\<Q> (T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. B)"
  proof (intro rule_P(2))
    show "is_tautologous (\<forall>x\<^bsub>\<alpha>\<^esub>. B \<equiv>\<^sup>\<Q> (T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. B))"
    proof -
      let ?\<theta> = "{(\<xx>, o) \<Zinj> \<forall>x\<^bsub>\<alpha>\<^esub>. B}"
      from assms(2) have "is_pwff_substitution ?\<theta>"
        using pwffs_subset_of_wffso by auto
      moreover have "\<forall>x\<^bsub>\<alpha>\<^esub>. B \<equiv>\<^sup>\<Q> (T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. B) = \<^bold>S ?\<theta> ?C\<^sub>1"
        by simp
      ultimately show ?thesis
        using \<open>is_tautology ?C\<^sub>1\<close> by blast
    qed
  qed simp
  have "\<section>2": "\<turnstile> B \<equiv>\<^sup>\<Q> (T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> B)"
  proof (intro rule_P(2))
    show "is_tautologous (B \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> B)"
    proof -
      let ?\<theta> = "{(\<xx>, o) \<Zinj> B}"
      from assms(2) have "is_pwff_substitution ?\<theta>"
        using pwffs_subset_of_wffso by auto
      moreover have "B \<equiv>\<^sup>\<Q> T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> B = \<^bold>S ?\<theta> ?C\<^sub>1"
        by simp
      ultimately show ?thesis
        using \<open>is_tautology ?C\<^sub>1\<close> by blast
    qed
  qed simp
  have "\<turnstile> T\<^bsub>o\<^esub>"
    by (fact true_is_derivable)
  then have "\<section>3": "\<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>"
    using Gen by simp
  have "\<section>4": "\<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. B)"
  proof (intro rule_P(1)[where \<G> = "{\<forall>x\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>}"])
    show "is_tautologous ([\<forall>x\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>] \<supset>\<^sup>\<Q>\<^sub>\<star> (\<forall>x\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. B)))"
    proof -
      let ?\<theta> = "{(\<xx>, o) \<Zinj> \<forall>x\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>, (\<yy>, o) \<Zinj> \<forall>x\<^bsub>\<alpha>\<^esub>. B}"
      from assms(2) have "is_pwff_substitution ?\<theta>"
        using pwffs_subset_of_wffso by auto
      moreover have "[\<forall>x\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>] \<supset>\<^sup>\<Q>\<^sub>\<star> (\<forall>x\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. B)) = \<^bold>S ?\<theta> ?C\<^sub>2"
        by simp
      ultimately show ?thesis
        using \<open>is_tautology ?C\<^sub>2\<close> by blast
    qed
  qed (use "\<section>3" in fastforce)+
  have "\<section>5": "\<turnstile> T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> B)"
  proof (intro rule_P(2))
    show "is_tautologous (T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> B))"
    proof -
      let ?\<theta> = "{(\<xx>, o) \<Zinj> B}" and ?C = "T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub>)"
      have "is_tautology ?C"
        using \<V>\<^sub>B_simps by simp
      moreover from assms(2) have "is_pwff_substitution ?\<theta>"
        using pwffs_subset_of_wffso by auto
      moreover have "T\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> B) = \<^bold>S ?\<theta> ?C"
        by simp
      ultimately show ?thesis
        by blast
    qed
  qed simp
  from "\<section>4" and "\<section>5" have "\<section>6": "\<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. (F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> B) \<equiv>\<^sup>\<Q> (F\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. B)"
    unfolding equivalence_def by (rule rule_R[where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>,\<guillemotleft>]"]) force+
  from "\<section>1" and "\<section>2" have "\<section>7": "\<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. (T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> B) \<equiv>\<^sup>\<Q> (T\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. B)"
    unfolding equivalence_def by (rule rule_R[where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>,\<guillemotleft>]"]) force+
  obtain p where "(p, o) \<notin> vars B" and "p \<noteq> x"
    using fresh_var_existence and vars_form_finiteness by (metis finite_insert insert_iff)
  from \<open>(p, o) \<notin> vars B\<close> have sub: "\<^bold>S {(p, o) \<Zinj> C} B = B" for C
    using free_var_singleton_substitution_neutrality and free_vars_in_all_vars by blast
  have "\<section>8": "\<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. (p\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> B) \<equiv>\<^sup>\<Q> (p\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. B)" (is \<open>\<turnstile> ?C\<^sub>3\<close>)
  proof -
    from sub and "\<section>7" have "\<turnstile> \<^bold>S {(p, o) \<Zinj> T\<^bsub>o\<^esub>} ?C\<^sub>3"
      using \<open>p \<noteq> x\<close> by auto
    moreover from sub and "\<section>6" have "\<turnstile> \<^bold>S {(p, o) \<Zinj> F\<^bsub>o\<^esub>} ?C\<^sub>3"
      using \<open>p \<noteq> x\<close> by auto
    moreover from assms(2) have "?C\<^sub>3 \<in> wffs\<^bsub>o\<^esub>"
      using pwffs_subset_of_wffso by auto
    ultimately show ?thesis
      by (rule Cases)
  qed
  then show ?thesis
  proof -
    let ?\<theta> = "{(p, o) \<Zinj> A}"
    from assms(1) have "is_substitution ?\<theta>"
      using pwffs_subset_of_wffso by auto
    moreover have "
      \<forall>v \<in> fmdom' ?\<theta>. var_name v \<notin> free_var_names ({}::form set) \<and> is_free_for (?\<theta> $$! v) v ?C\<^sub>3"
    proof
      fix v
      assume "v \<in> fmdom' ?\<theta>"
      then have "v = (p, o)"
        by simp
      with assms(3) and \<open>(p, o) \<notin> vars B\<close> have "is_free_for (?\<theta> $$! v) v ?C\<^sub>3"
        using occurs_in_vars
        by (intro is_free_for_in_imp is_free_for_in_forall is_free_for_in_equivalence) auto
      moreover have "var_name v \<notin> free_var_names ({}::form set)"
        by simp
      ultimately show "var_name v \<notin> free_var_names ({}::form set) \<and> is_free_for (?\<theta> $$! v) v ?C\<^sub>3"
        unfolding \<open>v = (p, o)\<close> by blast
    qed
    moreover have "?\<theta> \<noteq> {$$}"
      by simp
    ultimately have "\<turnstile> \<^bold>S ?\<theta> ?C\<^sub>3"
      by (rule Sub[OF "\<section>8"])
    moreover have "\<^bold>S ?\<theta> ?C\<^sub>3 = \<forall>x\<^bsub>\<alpha>\<^esub>. (A \<supset>\<^sup>\<Q> B) \<equiv>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. B)"
      using \<open>p \<noteq> x\<close> and sub[of A] by simp
    ultimately show ?thesis
      by (simp only:)
  qed
qed

proposition prop_5237:
  assumes "is_hyps \<H>"
  and "\<H> \<turnstile> A \<supset>\<^sup>\<Q> B"
  and "(x, \<alpha>) \<notin> free_vars ({A} \<union> \<H>)"
  shows "\<H> \<turnstile> A \<supset>\<^sup>\<Q> (\<forall>x\<^bsub>\<alpha>\<^esub>. B)"
proof -
  have "\<H> \<turnstile> A \<supset>\<^sup>\<Q> B"
    by fact
  with assms(3) have "\<H> \<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. (A \<supset>\<^sup>\<Q> B)"
    using Gen by simp
  moreover have "\<H> \<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. (A \<supset>\<^sup>\<Q> B) \<equiv>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> (\<forall>x\<^bsub>\<alpha>\<^esub>. B))"
  proof -
    from assms(2) have "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
      using hyp_derivable_form_is_wffso by (blast dest: wffs_from_imp_op)+
    with assms(1,3) show ?thesis
      using prop_5237_aux and derivability_implies_hyp_derivability by simp
  qed
  ultimately show ?thesis
    by (rule Equality_Rules(1))
qed

lemmas "\<supset>\<forall>" = prop_5237 (* synonym *)

corollary generalized_prop_5237:
  assumes "is_hyps \<H>"
  and "\<H> \<turnstile> A \<supset>\<^sup>\<Q> B"
  and "\<forall>v \<in> S. v \<notin> free_vars ({A} \<union> \<H>)"
  and "lset vs = S"
  shows "\<H> \<turnstile> A \<supset>\<^sup>\<Q> (\<forall>\<^sup>\<Q>\<^sub>\<star> vs B)"
using assms proof (induction vs arbitrary: S)
  case Nil
  then show ?case
    by simp
next
  case (Cons v vs)
  obtain x and \<alpha> where "v = (x, \<alpha>)"
    by fastforce
  from Cons.prems(3) have *: "\<forall>v' \<in> S. v' \<notin> free_vars ({A} \<union> \<H>)"
    by blast
  then show ?case
  proof (cases "v \<in> lset vs")
    case True
    with Cons.prems(4) have "lset vs = S"
      by auto
    with assms(1,2) and * have "\<H> \<turnstile> A \<supset>\<^sup>\<Q> \<forall>\<^sup>\<Q>\<^sub>\<star> vs B"
      by (fact Cons.IH)
    with True and \<open>lset vs = S\<close> and \<open>v = (x, \<alpha>)\<close> and * have "\<H> \<turnstile> A \<supset>\<^sup>\<Q> (\<forall>x\<^bsub>\<alpha>\<^esub>. \<forall>\<^sup>\<Q>\<^sub>\<star> vs B)"
      using prop_5237[OF assms(1)] by simp
    with \<open>v = (x, \<alpha>)\<close> show ?thesis
      by simp
  next
    case False
    with \<open>lset (v # vs) = S\<close> have "lset vs = S - {v}"
      by auto
    moreover from * have "\<forall>v' \<in> S - {v}. v' \<notin> free_vars ({A} \<union> \<H>)"
      by blast
    ultimately have "\<H> \<turnstile> A \<supset>\<^sup>\<Q> \<forall>\<^sup>\<Q>\<^sub>\<star> vs B"
      using assms(1,2) by (intro Cons.IH)
    moreover from Cons.prems(4) and \<open>v = (x, \<alpha>)\<close> and * have "(x, \<alpha>) \<notin> free_vars ({A} \<union> \<H>)"
      by auto
    ultimately have "\<H> \<turnstile> A \<supset>\<^sup>\<Q> (\<forall>x\<^bsub>\<alpha>\<^esub>. \<forall>\<^sup>\<Q>\<^sub>\<star> vs B)"
      using assms(1) by (intro prop_5237)
    with \<open>v = (x, \<alpha>)\<close> show ?thesis
      by simp
  qed
qed

end

subsection \<open>Proposition 5238\<close>

context begin

private lemma prop_5238_aux:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows "\<turnstile> ((\<lambda>x\<^bsub>\<beta>\<^esub>. A) =\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> (\<lambda>x\<^bsub>\<beta>\<^esub>. B)) \<equiv>\<^sup>\<Q> \<forall>x\<^bsub>\<beta>\<^esub>. (A =\<^bsub>\<alpha>\<^esub> B)"
proof -
  have "\<section>1": "
    \<turnstile> (\<ff>\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> =\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> \<gg>\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub>) \<equiv>\<^sup>\<Q> \<forall>\<xx>\<^bsub>\<beta>\<^esub>. (\<ff>\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> \<sqdot> \<xx>\<^bsub>\<beta>\<^esub> =\<^bsub>\<alpha>\<^esub> \<gg>\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> \<sqdot> \<xx>\<^bsub>\<beta>\<^esub>)" (is \<open>\<turnstile> _ \<equiv>\<^sup>\<Q> \<forall>\<xx>\<^bsub>\<beta>\<^esub>. ?C\<^sub>1\<close>)
    by (fact axiom_is_derivable_from_no_hyps[OF axiom_3])
  then have "\<section>2": "
    \<turnstile> (\<ff>\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> =\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> \<gg>\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub>) \<equiv>\<^sup>\<Q> \<forall>x\<^bsub>\<beta>\<^esub>. (\<ff>\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> \<sqdot> x\<^bsub>\<beta>\<^esub> =\<^bsub>\<alpha>\<^esub> \<gg>\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> \<sqdot> x\<^bsub>\<beta>\<^esub>)" (is \<open>\<turnstile> ?C\<^sub>2\<close>)
  proof (cases "x = \<xx>")
    case True
    with "\<section>1" show ?thesis
      by (simp only:)
  next
    case False
    have "?C\<^sub>1 \<in> wffs\<^bsub>o\<^esub>"
      by blast
    moreover from False have "(x, \<beta>) \<notin> free_vars ?C\<^sub>1"
      by simp
    moreover have "is_free_for (x\<^bsub>\<beta>\<^esub>) (\<xx>, \<beta>) ?C\<^sub>1"
      by (intro is_free_for_in_equality is_free_for_to_app) simp_all
    ultimately have "\<turnstile> \<lambda>\<xx>\<^bsub>\<beta>\<^esub>. ?C\<^sub>1 =\<^bsub>\<beta>\<rightarrow>o\<^esub> \<lambda>x\<^bsub>\<beta>\<^esub>. (\<^bold>S {(\<xx>, \<beta>) \<Zinj> x\<^bsub>\<beta>\<^esub>} ?C\<^sub>1)"
      by (rule "\<alpha>")
    from "\<section>1" and this show ?thesis
      by (rule rule_R[where p = "[\<guillemotright>,\<guillemotright>]"]) force+
  qed
  then have "\<section>3": "
    \<turnstile> ((\<lambda>x\<^bsub>\<beta>\<^esub>. A) =\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> (\<lambda>x\<^bsub>\<beta>\<^esub>. B)) \<equiv>\<^sup>\<Q> \<forall>x\<^bsub>\<beta>\<^esub>. ((\<lambda>x\<^bsub>\<beta>\<^esub>. A) \<sqdot> x\<^bsub>\<beta>\<^esub> =\<^bsub>\<alpha>\<^esub> (\<lambda>x\<^bsub>\<beta>\<^esub>. B) \<sqdot> x\<^bsub>\<beta>\<^esub>)"
  proof -
    let ?\<theta> = "{(\<ff>, \<beta>\<rightarrow>\<alpha>) \<Zinj> \<lambda>x\<^bsub>\<beta>\<^esub>. A, (\<gg>, \<beta>\<rightarrow>\<alpha>) \<Zinj> \<lambda>x\<^bsub>\<beta>\<^esub>. B}"
    have "\<lambda>x\<^bsub>\<beta>\<^esub>. A \<in> wffs\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub>" and "\<lambda>x\<^bsub>\<beta>\<^esub>. B \<in> wffs\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub>"
      by (blast intro: assms(1,2))+
    then have "is_substitution ?\<theta>"
      by simp
    moreover have "
      \<forall>v \<in> fmdom' ?\<theta>. var_name v \<notin> free_var_names ({}::form set) \<and> is_free_for (?\<theta> $$! v) v ?C\<^sub>2"
    proof
      fix v
      assume "v \<in> fmdom' ?\<theta>"
      then consider (a) "v = (\<ff>, \<beta>\<rightarrow>\<alpha>)" | (b) "v = (\<gg>, \<beta>\<rightarrow>\<alpha>)"
        by fastforce
      then show "var_name v \<notin> free_var_names ({}::form set) \<and> is_free_for (?\<theta> $$! v) v ?C\<^sub>2"
      proof cases
        case a
        have "(x, \<beta>) \<notin> free_vars (\<lambda>x\<^bsub>\<beta>\<^esub>. A)"
          by simp
        then have "is_free_for (\<lambda>x\<^bsub>\<beta>\<^esub>. A) (\<ff>, \<beta>\<rightarrow>\<alpha>) ?C\<^sub>2"
          unfolding equivalence_def
          by (intro is_free_for_in_equality is_free_for_in_forall is_free_for_to_app, simp_all)
        with a show ?thesis
          by force
      next
        case b
        have "(x, \<beta>) \<notin> free_vars (\<lambda>x\<^bsub>\<beta>\<^esub>. B)"
          by simp
        then have "is_free_for (\<lambda>x\<^bsub>\<beta>\<^esub>. B) (\<gg>, \<beta>\<rightarrow>\<alpha>) ?C\<^sub>2"
          unfolding equivalence_def
          by (intro is_free_for_in_equality is_free_for_in_forall is_free_for_to_app, simp_all)
        with b show ?thesis
          by force
      qed
    qed
    moreover have "?\<theta> \<noteq> {$$}"
      by simp
    ultimately have "\<turnstile> \<^bold>S ?\<theta> ?C\<^sub>2"
      by (rule Sub[OF "\<section>2"])
    then show ?thesis
      by simp
  qed
  then have "\<section>4": "\<turnstile> ((\<lambda>x\<^bsub>\<beta>\<^esub>. A) =\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> (\<lambda>x\<^bsub>\<beta>\<^esub>. B)) \<equiv>\<^sup>\<Q> \<forall>x\<^bsub>\<beta>\<^esub>. (A =\<^bsub>\<alpha>\<^esub> (\<lambda>x\<^bsub>\<beta>\<^esub>. B) \<sqdot> x\<^bsub>\<beta>\<^esub>)"
  proof -
    have "\<turnstile> (\<lambda>x\<^bsub>\<beta>\<^esub>. A) \<sqdot> x\<^bsub>\<beta>\<^esub> =\<^bsub>\<alpha>\<^esub> A"
      using prop_5208[where vs = "[(x, \<beta>)]"] and assms(1) by simp
    from "\<section>3" and this show ?thesis
      by (rule rule_R[where p = "[\<guillemotright>,\<guillemotright>,\<guillemotleft>,\<guillemotleft>,\<guillemotright>]"]) force+
  qed
  then show ?thesis
  proof -
    have "\<turnstile> (\<lambda>x\<^bsub>\<beta>\<^esub>. B) \<sqdot> x\<^bsub>\<beta>\<^esub> =\<^bsub>\<alpha>\<^esub> B"
      using prop_5208[where vs = "[(x, \<beta>)]"] and assms(2) by simp
    from "\<section>4" and this show ?thesis
      by (rule rule_R[where p = "[\<guillemotright>,\<guillemotright>,\<guillemotleft>,\<guillemotright>]"]) force+
  qed
qed

proposition prop_5238:
  assumes "vs \<noteq> []" and "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows "\<turnstile> \<lambda>\<^sup>\<Q>\<^sub>\<star> vs A =\<^bsub>foldr (\<rightarrow>) (map var_type vs) \<alpha>\<^esub> \<lambda>\<^sup>\<Q>\<^sub>\<star> vs B \<equiv>\<^sup>\<Q> \<forall>\<^sup>\<Q>\<^sub>\<star> vs (A =\<^bsub>\<alpha>\<^esub> B)"
using assms proof (induction vs arbitrary: A B \<alpha> rule: rev_nonempty_induct)
  case (single v)
  obtain x and \<beta> where "v = (x, \<beta>)"
    by fastforce
  from single.prems have "
    \<lambda>\<^sup>\<Q>\<^sub>\<star> vs A =\<^bsub>foldr (\<rightarrow>) (map var_type vs) \<alpha>\<^esub> \<lambda>\<^sup>\<Q>\<^sub>\<star> vs B \<equiv>\<^sup>\<Q> \<forall>\<^sup>\<Q>\<^sub>\<star> vs (A =\<^bsub>\<alpha>\<^esub> B) \<in> wffs\<^bsub>o\<^esub>"
    by blast
  with single.prems and \<open>v = (x, \<beta>)\<close> show ?case
    using prop_5238_aux by simp
next
  case (snoc v vs)
  obtain x and \<beta> where "v = (x, \<beta>)"
    by fastforce
  from snoc.prems have "\<lambda>x\<^bsub>\<beta>\<^esub>. A \<in> wffs\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub>" and "\<lambda>x\<^bsub>\<beta>\<^esub>. B \<in> wffs\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub>"
    by auto
  then have "
    \<turnstile>
      \<lambda>\<^sup>\<Q>\<^sub>\<star> vs (\<lambda>x\<^bsub>\<beta>\<^esub>. A) =\<^bsub>foldr (\<rightarrow>) (map var_type vs) (\<beta>\<rightarrow>\<alpha>)\<^esub> \<lambda>\<^sup>\<Q>\<^sub>\<star> vs (\<lambda>x\<^bsub>\<beta>\<^esub>. B)
      \<equiv>\<^sup>\<Q>
      \<forall>\<^sup>\<Q>\<^sub>\<star> vs ((\<lambda>x\<^bsub>\<beta>\<^esub>. A) =\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> (\<lambda>x\<^bsub>\<beta>\<^esub>. B))"
    by (fact snoc.IH)
  moreover from snoc.prems have "\<turnstile> \<lambda>x\<^bsub>\<beta>\<^esub>. A =\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> \<lambda>x\<^bsub>\<beta>\<^esub>. B \<equiv>\<^sup>\<Q> \<forall>x\<^bsub>\<beta>\<^esub>. (A =\<^bsub>\<alpha>\<^esub> B)"
    by (fact prop_5238_aux)
  ultimately have "
    \<turnstile>
      \<lambda>\<^sup>\<Q>\<^sub>\<star> vs (\<lambda>x\<^bsub>\<beta>\<^esub>. A) =\<^bsub>foldr (\<rightarrow>) (map var_type vs) (\<beta>\<rightarrow>\<alpha>)\<^esub> \<lambda>\<^sup>\<Q>\<^sub>\<star> vs (\<lambda>x\<^bsub>\<beta>\<^esub>. B)
      \<equiv>\<^sup>\<Q>
      \<forall>\<^sup>\<Q>\<^sub>\<star> vs \<forall>x\<^bsub>\<beta>\<^esub>. (A =\<^bsub>\<alpha>\<^esub> B)"
  unfolding equivalence_def proof (induction rule: rule_R[where p = "\<guillemotright> # foldr (\<lambda>_. (@) [\<guillemotright>,\<guillemotleft>]) vs []"])
    case occ_subform
    then show ?case
      using innermost_subform_in_generalized_forall[OF snoc.hyps] and is_subform_at.simps(3)
      by fastforce
  next
    case replacement
    then show ?case
      using innermost_replacement_in_generalized_forall[OF snoc.hyps]
      and is_replacement_at_implies_in_positions and replace_right_app by force
  qed
  with \<open>v = (x, \<beta>)\<close> show ?case
    by simp
qed

end

subsection \<open>Proposition 5239\<close>

lemma replacement_derivability:
  assumes "C \<in> wffs\<^bsub>\<beta>\<^esub>"
  and "A \<preceq>\<^bsub>p\<^esub> C"
  and "\<turnstile> A =\<^bsub>\<alpha>\<^esub> B"
  and "C\<lblot>p \<leftarrow> B\<rblot> \<rhd> D"
  shows "\<turnstile> C =\<^bsub>\<beta>\<^esub> D"
using assms proof (induction arbitrary: D p)
  case (var_is_wff \<gamma> x)
  from var_is_wff.prems(1) have "p = []" and "A = x\<^bsub>\<gamma>\<^esub>"
    by (auto elim: is_subform_at.elims(2))
  with var_is_wff.prems(2) have "\<alpha> = \<gamma>"
    using hyp_derivable_form_is_wffso and wff_has_unique_type and wffs_from_equality by blast
  moreover from \<open>p = []\<close> and var_is_wff.prems(3) have "D = B"
    using is_replacement_at_minimal_change(1) and is_subform_at.simps(1) by iprover
  ultimately show ?case
    using \<open>A = x\<^bsub>\<gamma>\<^esub>\<close> and var_is_wff.prems(2) by (simp only:)
next
  case (con_is_wff \<gamma> c)
  from con_is_wff.prems(1) have "p = []" and "A = \<lbrace>c\<rbrace>\<^bsub>\<gamma>\<^esub>"
    by (auto elim: is_subform_at.elims(2))
  with con_is_wff.prems(2) have "\<alpha> = \<gamma>"
    using hyp_derivable_form_is_wffso and wff_has_unique_type
    by (meson wffs_from_equality wffs_of_type_intros(2))
  moreover from \<open>p = []\<close> and con_is_wff.prems(3) have "D = B"
    using is_replacement_at_minimal_change(1) and is_subform_at.simps(1) by iprover
  ultimately show ?case
    using \<open>A = \<lbrace>c\<rbrace>\<^bsub>\<gamma>\<^esub>\<close> and con_is_wff.prems(2) by (simp only:)
next
  case (app_is_wff \<gamma> \<delta> C\<^sub>1 C\<^sub>2)
  from app_is_wff.prems(1) consider
    (a) "p = []"
  | (b) "\<exists>p'. p = \<guillemotleft> # p' \<and> A \<preceq>\<^bsub>p'\<^esub> C\<^sub>1"
  | (c) "\<exists>p'. p = \<guillemotright> # p' \<and> A \<preceq>\<^bsub>p'\<^esub> C\<^sub>2"
    using subforms_from_app by blast
  then show ?case
  proof cases
    case a
    with app_is_wff.prems(1) have "A = C\<^sub>1 \<sqdot> C\<^sub>2"
      by simp
    moreover from a and app_is_wff.prems(3) have "D = B"
      using is_replacement_at_minimal_change(1) and at_top_is_self_subform by blast
    moreover from \<open>A = C\<^sub>1 \<sqdot> C\<^sub>2\<close> and \<open>D = B\<close> and app_is_wff.hyps(1,2) and assms(3) have "\<alpha> = \<delta>"
      using hyp_derivable_form_is_wffso and wff_has_unique_type
      by (blast dest: wffs_from_equality)
    ultimately show ?thesis
      using assms(3) by (simp only:)
  next
    case b
    then obtain p' where "p = \<guillemotleft> # p'" and "A \<preceq>\<^bsub>p'\<^esub> C\<^sub>1"
      by blast
    moreover obtain D\<^sub>1 where "D = D\<^sub>1 \<sqdot> C\<^sub>2" and "C\<^sub>1\<lblot>p' \<leftarrow> B\<rblot> \<rhd> D\<^sub>1"
      using app_is_wff.prems(3) and \<open>p = \<guillemotleft> # p'\<close> by (force dest: is_replacement_at.cases)
    ultimately have "\<turnstile> C\<^sub>1 =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> D\<^sub>1"
      using app_is_wff.IH(1) and assms(3) by blast
    moreover have "\<turnstile> C\<^sub>2 =\<^bsub>\<gamma>\<^esub> C\<^sub>2"
      by (fact prop_5200[OF app_is_wff.hyps(2)])
    ultimately have "\<turnstile> C\<^sub>1 \<sqdot> C\<^sub>2 =\<^bsub>\<delta>\<^esub> D\<^sub>1 \<sqdot> C\<^sub>2"
      using Equality_Rules(4) by (simp only:)
    with \<open>D = D\<^sub>1 \<sqdot> C\<^sub>2\<close> show ?thesis
      by (simp only:)
  next
    case c
    then obtain p' where "p = \<guillemotright> # p'" and "A \<preceq>\<^bsub>p'\<^esub> C\<^sub>2"
      by blast
    moreover obtain D\<^sub>2 where "D = C\<^sub>1 \<sqdot> D\<^sub>2" and "C\<^sub>2\<lblot>p' \<leftarrow> B\<rblot> \<rhd> D\<^sub>2"
      using app_is_wff.prems(3) and \<open>p = \<guillemotright> # p'\<close> by (force dest: is_replacement_at.cases)
    ultimately have "\<turnstile> C\<^sub>2 =\<^bsub>\<gamma>\<^esub> D\<^sub>2"
      using app_is_wff.IH(2) and assms(3) by blast
    moreover have "\<turnstile> C\<^sub>1 =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> C\<^sub>1"
      by (fact prop_5200[OF app_is_wff.hyps(1)])
    ultimately have "\<turnstile> C\<^sub>1 \<sqdot> C\<^sub>2 =\<^bsub>\<delta>\<^esub> C\<^sub>1 \<sqdot> D\<^sub>2"
      using Equality_Rules(4) by (simp only:)
    with \<open>D = C\<^sub>1 \<sqdot> D\<^sub>2\<close> show ?thesis
      by (simp only:)
  qed
next
  case (abs_is_wff \<delta> C' \<gamma> x)
  from abs_is_wff.prems(1) consider (a) "p = []" | (b) "\<exists>p'. p = \<guillemotleft> # p' \<and> A \<preceq>\<^bsub>p'\<^esub> C'"
    using subforms_from_abs by blast
  then show ?case
  proof cases
    case a
    with abs_is_wff.prems(1) have "A = \<lambda>x\<^bsub>\<gamma>\<^esub>. C'"
      by simp
    moreover from a and abs_is_wff.prems(3) have "D = B"
      using is_replacement_at_minimal_change(1) and at_top_is_self_subform by blast
    moreover from \<open>A = \<lambda>x\<^bsub>\<gamma>\<^esub>. C'\<close> and \<open>D = B\<close> and abs_is_wff.hyps(1) and assms(3) have "\<alpha> = \<gamma>\<rightarrow>\<delta>"
      using hyp_derivable_form_is_wffso and wff_has_unique_type
      by (blast dest: wffs_from_abs wffs_from_equality)
    ultimately show ?thesis
      using assms(3) by (simp only:)
  next
    case b
    then obtain p' where "p = \<guillemotleft> # p'" and "A \<preceq>\<^bsub>p'\<^esub> C'"
      by blast
    moreover obtain D' where "D = \<lambda>x\<^bsub>\<gamma>\<^esub>. D'" and "C'\<lblot>p' \<leftarrow> B\<rblot> \<rhd> D'"
      using abs_is_wff.prems(3) and \<open>p = \<guillemotleft> # p'\<close> by (force dest: is_replacement_at.cases)
    ultimately have "\<turnstile> C' =\<^bsub>\<delta>\<^esub> D'"
      using abs_is_wff.IH and assms(3) by blast
    then have "\<turnstile> \<lambda>x\<^bsub>\<gamma>\<^esub>. C' =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> \<lambda>x\<^bsub>\<gamma>\<^esub>. D'"
    proof -
      from \<open>\<turnstile> C' =\<^bsub>\<delta>\<^esub> D'\<close> have "\<turnstile> \<forall>x\<^bsub>\<gamma>\<^esub>. (C' =\<^bsub>\<delta>\<^esub> D')"
        using Gen by simp
      moreover from \<open>\<turnstile> C' =\<^bsub>\<delta>\<^esub> D'\<close> and abs_is_wff.hyps have "D' \<in> wffs\<^bsub>\<delta>\<^esub>"
        using hyp_derivable_form_is_wffso by (blast dest: wffs_from_equality)
      with abs_is_wff.hyps have "\<turnstile> (\<lambda>x\<^bsub>\<gamma>\<^esub>. C' =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> \<lambda>x\<^bsub>\<gamma>\<^esub>. D') \<equiv>\<^sup>\<Q> \<forall>x\<^bsub>\<gamma>\<^esub>. (C' =\<^bsub>\<delta>\<^esub> D')"
        using prop_5238[where vs = "[(x, \<gamma>)]"] by simp
      ultimately show ?thesis
        using Equality_Rules(1,2) unfolding equivalence_def by blast
    qed
    with \<open>D = \<lambda>x\<^bsub>\<gamma>\<^esub>. D'\<close> show ?thesis
      by (simp only:)
  qed
qed

context
begin

private lemma prop_5239_aux_1:
  assumes "p \<in> positions (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar v) (map FVar vs))"
  and "p \<noteq> replicate (length vs) \<guillemotleft>"
  shows "
    (\<exists>A B. A \<sqdot> B \<preceq>\<^bsub>p\<^esub> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar v) (map FVar vs)))
    \<or>
    (\<exists>v \<in> lset vs. occurs_at v p (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar v) (map FVar vs)))"
using assms proof (induction vs arbitrary: p rule: rev_induct)
  case Nil
  then show ?case
    using surj_pair[of v] by fastforce
next
  case (snoc v' vs)
  from snoc.prems(1) consider
    (a) "p = []"
  | (b) "p = [\<guillemotright>]"
  | (c) "\<exists>p' \<in> positions (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar v) (map FVar vs)). p = \<guillemotleft> # p'"
    using surj_pair[of v'] by fastforce
  then show ?case
  proof cases
    case c
    then obtain p' where "p' \<in> positions (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar v) (map FVar vs))" and "p = \<guillemotleft> # p'"
      by blast
    from \<open>p = \<guillemotleft> # p'\<close> and snoc.prems(2) have "p' \<noteq> replicate (length vs) \<guillemotleft>"
      by force
    then have "
      (\<exists>A B. A \<sqdot> B \<preceq>\<^bsub>p'\<^esub> \<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar v) (map FVar vs))
      \<or>
      (\<exists>v \<in> lset vs. occurs_at v p' (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar v) (map FVar vs)))"
      using \<open>p' \<in> positions (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar v) (map FVar vs))\<close> and snoc.IH by simp
    with \<open>p = \<guillemotleft> # p'\<close> show ?thesis
      by auto
  qed simp_all
qed

private lemma prop_5239_aux_2:
  assumes "t \<notin> lset vs \<union> vars C"
  and "C\<lblot>p \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar t) (map FVar vs))\<rblot> \<rhd> G"
  and "C\<lblot>p \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) (map FVar vs))\<rblot> \<rhd> G'"
  shows "\<^bold>S {t \<Zinj> \<lambda>\<^sup>\<Q>\<^sub>\<star> vs A} G = G'" (is \<open>\<^bold>S ?\<theta> G = G'\<close>)
proof -
  have "\<^bold>S ?\<theta> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar t) (map FVar vs)) = \<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<^bold>S ?\<theta> (FVar t)) (map (\<lambda>v'. \<^bold>S ?\<theta> v') (map FVar vs))"
    using generalized_app_substitution by blast
  moreover have "\<^bold>S ?\<theta> (FVar t) = \<lambda>\<^sup>\<Q>\<^sub>\<star> vs A"
    using surj_pair[of t] by fastforce
  moreover from assms(1) have "map (\<lambda>v'. \<^bold>S ?\<theta> v') (map FVar vs) = map FVar vs"
    by (induction vs) auto
  ultimately show ?thesis
  using assms proof (induction C arbitrary: G G' p)
    case (FVar v)
    from FVar.prems(5) have "p = []" and "G = \<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar t) (map FVar vs)"
      by (blast dest: is_replacement_at.cases)+
    moreover from FVar.prems(6) and \<open>p = []\<close> have "G' = \<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) (map FVar vs)"
      by (blast dest: is_replacement_at.cases)
    ultimately show ?case
      using FVar.prems(1-3) by (simp only:)
  next
    case (FCon k)
    from FCon.prems(5) have "p = []" and "G = \<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar t) (map FVar vs)"
      by (blast dest: is_replacement_at.cases)+
    moreover from FCon.prems(6) and \<open>p = []\<close> have "G' = \<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) (map FVar vs)"
      by (blast dest: is_replacement_at.cases)
    ultimately show ?case
      using FCon.prems(1-3) by (simp only:)
  next
    case (FApp C\<^sub>1 C\<^sub>2)
    from FApp.prems(4) have "t \<notin> lset vs \<union> vars C\<^sub>1" and "t \<notin> lset vs \<union> vars C\<^sub>2"
      by auto
    consider (a) "p = []" | (b) "\<exists>p'. p = \<guillemotleft> # p'" | (c) "\<exists>p'. p = \<guillemotright> # p'"
      by (metis direction.exhaust list.exhaust)
    then show ?case
    proof cases
      case a
      with FApp.prems(5) have "G = \<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar t) (map FVar vs)"
        by (blast dest: is_replacement_at.cases)
      moreover from FApp.prems(6) and \<open>p = []\<close> have "G' = \<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) (map FVar vs)"
        by (blast dest: is_replacement_at.cases)
      ultimately show ?thesis
        using FApp.prems(1-3) by (simp only:)
    next
      case b
      then obtain p' where "p = \<guillemotleft> # p'"
        by blast
      with FApp.prems(5) obtain G\<^sub>1 where "G = G\<^sub>1 \<sqdot> C\<^sub>2" and "C\<^sub>1\<lblot>p' \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar t) (map FVar vs))\<rblot> \<rhd> G\<^sub>1"
        by (blast elim: is_replacement_at.cases)
      moreover from \<open>p = \<guillemotleft> # p'\<close> and FApp.prems(6)
      obtain G'\<^sub>1 where "G' = G'\<^sub>1 \<sqdot> C\<^sub>2" and "C\<^sub>1\<lblot>p' \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) (map FVar vs))\<rblot> \<rhd> G'\<^sub>1"
        by (blast elim: is_replacement_at.cases)
      moreover from \<open>t \<notin> lset vs \<union> vars C\<^sub>2\<close> have "\<^bold>S {t \<Zinj> \<lambda>\<^sup>\<Q>\<^sub>\<star> vs A} C\<^sub>2 = C\<^sub>2"
        using surj_pair[of t] and free_var_singleton_substitution_neutrality
        by (simp add: vars_is_free_and_bound_vars)
      ultimately show ?thesis
        using FApp.IH(1)[OF FApp.prems(1-3) \<open>t \<notin> lset vs \<union> vars C\<^sub>1\<close>] by simp
    next
      case c
      then obtain p' where "p = \<guillemotright> # p'"
        by blast
      with FApp.prems(5) obtain G\<^sub>2 where "G = C\<^sub>1 \<sqdot> G\<^sub>2" and "C\<^sub>2\<lblot>p' \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar t) (map FVar vs))\<rblot> \<rhd> G\<^sub>2"
        by (blast elim: is_replacement_at.cases)
      moreover from \<open>p = \<guillemotright> # p'\<close> and FApp.prems(6)
      obtain G'\<^sub>2 where "G' = C\<^sub>1 \<sqdot> G'\<^sub>2" and "C\<^sub>2\<lblot>p' \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) (map FVar vs))\<rblot> \<rhd> G'\<^sub>2"
        by (blast elim: is_replacement_at.cases)
      moreover from \<open>t \<notin> lset vs \<union> vars C\<^sub>1\<close> have "\<^bold>S {t \<Zinj> \<lambda>\<^sup>\<Q>\<^sub>\<star> vs A} C\<^sub>1 = C\<^sub>1"
        using surj_pair[of t] and free_var_singleton_substitution_neutrality
        by (simp add: vars_is_free_and_bound_vars)
      ultimately show ?thesis
        using FApp.IH(2)[OF FApp.prems(1-3) \<open>t \<notin> lset vs \<union> vars C\<^sub>2\<close>] by simp
    qed
  next
    case (FAbs v C')
    from FAbs.prems(4) have "t \<notin> lset vs \<union> vars C'" and "t \<noteq> v"
      using vars_form.elims by blast+
    from FAbs.prems(5) consider (a) "p = []" | (b) "\<exists>p'. p = \<guillemotleft> # p'"
      using is_replacement_at.simps by blast
    then show ?case
    proof cases
      case a
      with FAbs.prems(5) have "G = \<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar t) (map FVar vs)"
        by (blast dest: is_replacement_at.cases)
      moreover from FAbs.prems(6) and \<open>p = []\<close> have "G' = \<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) (map FVar vs)"
        by (blast dest: is_replacement_at.cases)
      ultimately show ?thesis
        using FAbs.prems(1-3) by (simp only:)
    next
      case b
      then obtain p' where "p = \<guillemotleft> # p'"
        by blast
      then obtain G\<^sub>1 where "G = FAbs v G\<^sub>1" and "C'\<lblot>p' \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar t) (map FVar vs))\<rblot> \<rhd> G\<^sub>1"
        using FAbs.prems(5) by (blast elim: is_replacement_at.cases)
      moreover from \<open>p = \<guillemotleft> # p'\<close> and FAbs.prems(6)
      obtain G'\<^sub>1 where "G' = FAbs v G'\<^sub>1" and "C'\<lblot>p' \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) (map FVar vs))\<rblot> \<rhd> G'\<^sub>1"
        by (blast elim: is_replacement_at.cases)
      ultimately have "\<^bold>S {t \<Zinj> \<lambda>\<^sup>\<Q>\<^sub>\<star> vs A} G\<^sub>1 = G'\<^sub>1"
        using FAbs.IH[OF FAbs.prems(1-3) \<open>t \<notin> lset vs \<union> vars C'\<close>] by simp
      with \<open>G = FAbs v G\<^sub>1\<close> and \<open>G' = FAbs v G'\<^sub>1\<close> and \<open>t \<noteq> v\<close> show ?thesis
        using surj_pair[of v] by fastforce
    qed
  qed
qed

private lemma prop_5239_aux_3:
  assumes "t \<notin> lset vs \<union> vars {A, C}"
  and "C\<lblot>p \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar t) (map FVar vs))\<rblot> \<rhd> G"
  and "occurs_at t p' G"
  shows "p' = p @ replicate (length vs) \<guillemotleft>" (is \<open>p' = ?p\<^sub>t\<close>)
proof (cases "vs = []")
  case True
  then have "t \<notin> vars C"
    using assms(1) by auto
  moreover from True and assms(2) have "C\<lblot>p \<leftarrow> FVar t\<rblot> \<rhd> G"
    by force
  ultimately show ?thesis
    using assms(3) and True and fresh_var_replacement_position_uniqueness by simp
next
  case False
  show ?thesis
  proof (rule ccontr)
    assume "p' \<noteq> ?p\<^sub>t"
    have "\<not> prefix ?p\<^sub>t p"
      by (simp add: False)
    from assms(3) have "p' \<in> positions G"
      using is_subform_implies_in_positions by fastforce
    from assms(2) have "?p\<^sub>t \<in> positions G"
      using is_replacement_at_minimal_change(1) and is_subform_at_transitivity
      and is_subform_implies_in_positions and leftmost_subform_in_generalized_app
      by (metis length_map)
    from assms(2) have "occurs_at t ?p\<^sub>t G"
      unfolding occurs_at_def using is_replacement_at_minimal_change(1) and is_subform_at_transitivity
      and leftmost_subform_in_generalized_app
      by (metis length_map)
    moreover from assms(2) and \<open>p' \<in> positions G\<close> have *: "
      subform_at C p' = subform_at G p'" if "\<not> prefix p' p" and "\<not> prefix p p'"
      using  is_replacement_at_minimal_change(2) by (simp add: that(1,2))
    ultimately show False
    proof (cases "\<not> prefix p' p \<and> \<not> prefix p p'")
      case True
      with assms(3) and * have "occurs_at t p' C"
        using is_replacement_at_occurs[OF assms(2)] by blast
      then have "t \<in> vars C"
        using is_subform_implies_in_positions and occurs_in_vars by fastforce
      with assms(1) show ?thesis
        by simp
    next
      case False
      then consider (a) "prefix p' p" | (b) "prefix p p'"
        by blast
      then show ?thesis
      proof cases
        case a
        with \<open>occurs_at t ?p\<^sub>t G\<close> and \<open>p' \<noteq> ?p\<^sub>t\<close> and assms(3) show ?thesis
          unfolding occurs_at_def using loop_subform_impossibility
          by (metis prefix_order.dual_order.order_iff_strict prefix_prefix)
      next
        case b
        have "strict_prefix p' ?p\<^sub>t"
        proof (rule ccontr)
          assume "\<not> strict_prefix p' ?p\<^sub>t"
          then consider
            (b\<^sub>1) "p' = ?p\<^sub>t"
          | (b\<^sub>2) "strict_prefix ?p\<^sub>t p'"
          | (b\<^sub>3) "\<not> prefix p' ?p\<^sub>t" and "\<not> prefix ?p\<^sub>t p'"
            by fastforce
          then show False
          proof cases
            case b\<^sub>1
            with \<open>p' \<noteq> ?p\<^sub>t\<close> show ?thesis
              by contradiction
          next
            case b\<^sub>2
            with \<open>occurs_at t ?p\<^sub>t G\<close> and assms(3) show ?thesis
              using loop_subform_impossibility by blast
          next
            case b\<^sub>3
            from b obtain p'' where "p' = p @ p''" and "p'' \<in> positions (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar t) (map FVar vs))"
              using is_replacement_at_new_positions and \<open>p' \<in> positions G\<close> and assms(2) by blast
            moreover have "p'' \<noteq> replicate (length vs) \<guillemotleft>"
              using \<open>p' = p @ p''\<close> and \<open>p' \<noteq> ?p\<^sub>t\<close> by blast
            ultimately consider
              (b\<^sub>3\<^sub>_\<^sub>1) "\<exists>F\<^sub>1 F\<^sub>2. F\<^sub>1 \<sqdot> F\<^sub>2 \<preceq>\<^bsub>p''\<^esub> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar t) (map FVar vs))"
            | (b\<^sub>3\<^sub>_\<^sub>2) "\<exists>v \<in> lset vs. occurs_at v p'' (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar t) (map FVar vs))"
              using prop_5239_aux_1 and b\<^sub>3(1,2) and is_replacement_at_occurs
              and leftmost_subform_in_generalized_app_replacement
              by (metis (no_types, opaque_lifting) length_map prefix_append)
            then show ?thesis
            proof cases
              case b\<^sub>3\<^sub>_\<^sub>1
              with assms(2) and \<open>p' = p @ p''\<close> have "\<exists>F\<^sub>1 F\<^sub>2. F\<^sub>1 \<sqdot> F\<^sub>2 \<preceq>\<^bsub>p'\<^esub> G"
                using is_replacement_at_minimal_change(1) and is_subform_at_transitivity by meson
              with \<open>occurs_at t p' G\<close> show ?thesis
                using is_subform_at_uniqueness by fastforce
            next
              case b\<^sub>3\<^sub>_\<^sub>2
              with assms(2) and \<open>p' = p @ p''\<close> have "\<exists>v \<in> lset vs. occurs_at v p' G"
                unfolding occurs_at_def
                using is_replacement_at_minimal_change(1) and is_subform_at_transitivity by meson
              with assms(1,3) show ?thesis
                using is_subform_at_uniqueness by fastforce
            qed
          qed
        qed
        with \<open>occurs_at t ?p\<^sub>t G\<close> and assms(3) show ?thesis
          using loop_subform_impossibility by blast
      qed
    qed
  qed
qed

private lemma prop_5239_aux_4:
  assumes "t \<notin> lset vs \<union> vars {A, C}"
  and "A \<preceq>\<^bsub>p\<^esub> C"
  and "lset vs \<supseteq> capture_exposed_vars_at p C A"
  and "C\<lblot>p \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar t) (map FVar vs))\<rblot> \<rhd> G"
  shows "is_free_for (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) t G"
unfolding is_free_for_def proof (intro ballI impI)
  let ?p\<^sub>t = "p @ replicate (length vs) \<guillemotleft>"
  from assms(4) have "FVar t \<preceq>\<^bsub>?p\<^sub>t\<^esub> G"
    using is_replacement_at_minimal_change(1) and is_subform_at_transitivity
    and leftmost_subform_in_generalized_app by (metis length_map)
  fix v' and p'
  assume "v' \<in> free_vars (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A)" and "p' \<in> positions G" and "is_free_at t p' G"
  have "v' \<notin> binders_at G ?p\<^sub>t"
  proof -
    have "free_vars (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) = free_vars A - lset vs"
      by (fact free_vars_of_generalized_abs)
    also from assms(2,3) have "\<dots> \<subseteq> free_vars A - (binders_at C p \<inter> free_vars A)"
      using capture_exposed_vars_at_alt_def and is_subform_implies_in_positions by fastforce
    also have "\<dots> = free_vars A - (binders_at G p \<inter> free_vars A)"
      using assms(2,4) is_replacement_at_binders is_subform_implies_in_positions by blast
    finally have "free_vars (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) \<subseteq> free_vars A - (binders_at G p \<inter> free_vars A)" .
    moreover have "binders_at (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (FVar t) (map FVar vs)) (replicate (length vs) \<guillemotleft>) = {}"
      by (induction vs rule: rev_induct) simp_all
    with assms(4) have "binders_at G ?p\<^sub>t = binders_at G p"
      using binders_at_concat and is_replacement_at_minimal_change(1) by blast
    ultimately show ?thesis
      using \<open>v' \<in> free_vars (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A)\<close> by blast
  qed
  moreover have "p' = ?p\<^sub>t"
    by
      (
        fact prop_5239_aux_3
          [OF assms(1,4) \<open>is_free_at t p' G\<close>[unfolded is_free_at_def, THEN conjunct1]]
      )
  ultimately show "\<not> in_scope_of_abs v' p' G"
    using binders_at_alt_def[OF \<open>p' \<in> positions G\<close>] and in_scope_of_abs_alt_def by auto
qed

proposition prop_5239:
  assumes "is_rule_R_app p D C (A =\<^bsub>\<alpha>\<^esub> B)"
  and "lset vs =
    {(x, \<beta>) | x \<beta> p' E. strict_prefix p' p \<and> \<lambda>x\<^bsub>\<beta>\<^esub>. E \<preceq>\<^bsub>p'\<^esub> C \<and> (x, \<beta>) \<in> free_vars (A =\<^bsub>\<alpha>\<^esub> B)}"
  shows "\<turnstile> \<forall>\<^sup>\<Q>\<^sub>\<star> vs (A =\<^bsub>\<alpha>\<^esub> B) \<supset>\<^sup>\<Q> (C \<equiv>\<^sup>\<Q> D)"
proof -
  let ?\<gamma> = "foldr (\<rightarrow>) (map var_type vs) \<alpha>"
  obtain t where "(t, ?\<gamma>) \<notin> lset vs \<union> vars {A,B,C,D}"
    using fresh_var_existence and vars_form_set_finiteness
    by (metis List.finite_set finite.simps finite_UnI)
  from assms(1) have "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<alpha>\<^esub>" and "A \<preceq>\<^bsub>p\<^esub> C"
    using wffs_from_equality[OF equality_wff] by simp_all
  from assms(1) have "C \<in> wffs\<^bsub>o\<^esub>" and "D \<in> wffs\<^bsub>o\<^esub>"
    using replacement_preserves_typing by fastforce+
  have "\<sqdot>\<^sup>\<Q>\<^sub>\<star> t\<^bsub>?\<gamma>\<^esub> (map FVar vs) \<in> wffs\<^bsub>\<alpha>\<^esub>"
    using generalized_app_wff[where As = "map FVar vs" and ts = "map var_type vs"]
    by (metis eq_snd_iff length_map nth_map wffs_of_type_intros(1))
  from assms(1) have "p \<in> positions C"
    using is_subform_implies_in_positions by fastforce
  then obtain G where "C\<lblot>p \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> t\<^bsub>?\<gamma>\<^esub> (map FVar vs))\<rblot> \<rhd> G"
    using is_replacement_at_existence by blast
  with  \<open>A \<preceq>\<^bsub>p\<^esub> C\<close> and \<open>\<sqdot>\<^sup>\<Q>\<^sub>\<star> t\<^bsub>?\<gamma>\<^esub> (map FVar vs) \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> have "G \<in> wffs\<^bsub>o\<^esub>"
    using \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> and \<open>C \<in> wffs\<^bsub>o\<^esub>\<close> and replacement_preserves_typing by blast
  let ?\<theta> = "{(\<hh>, ?\<gamma>\<rightarrow>o) \<Zinj> \<lambda>t\<^bsub>?\<gamma>\<^esub>. G, (\<xx>, ?\<gamma>) \<Zinj> \<lambda>\<^sup>\<Q>\<^sub>\<star> vs A, (\<yy>, ?\<gamma>) \<Zinj> \<lambda>\<^sup>\<Q>\<^sub>\<star> vs B}"
    and ?A = "(\<xx>\<^bsub>?\<gamma>\<^esub> =\<^bsub>?\<gamma>\<^esub> \<yy>\<^bsub>?\<gamma>\<^esub>) \<supset>\<^sup>\<Q> (\<hh>\<^bsub>?\<gamma>\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>?\<gamma>\<^esub> \<equiv>\<^sup>\<Q> \<hh>\<^bsub>?\<gamma>\<rightarrow>o\<^esub> \<sqdot> \<yy>\<^bsub>?\<gamma>\<^esub>)"
  have "\<turnstile> ?A"
    by (fact axiom_is_derivable_from_no_hyps[OF axiom_2])
  moreover have "\<lambda>t\<^bsub>?\<gamma>\<^esub>. G \<in> wffs\<^bsub>?\<gamma>\<rightarrow>o\<^esub>" and "\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A \<in> wffs\<^bsub>?\<gamma>\<^esub>" and "\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B \<in> wffs\<^bsub>?\<gamma>\<^esub>"
    by (blast intro: \<open>G \<in> wffs\<^bsub>o\<^esub>\<close> \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> \<open>B \<in> wffs\<^bsub>\<alpha>\<^esub>\<close>)+
  then have "is_substitution ?\<theta>"
    by simp
  moreover have "
    \<forall>v \<in> fmdom' ?\<theta>. var_name v \<notin> free_var_names ({}::form set) \<and> is_free_for (?\<theta> $$! v) v ?A"
    by
    (
      (
        code_simp, unfold atomize_conj[symmetric], simp,
        use is_free_for_in_equality is_free_for_in_equivalence is_free_for_in_imp is_free_for_in_var
        is_free_for_to_app in presburger
      )+,
      blast
    )
  moreover have "?\<theta> \<noteq> {$$}"
    by simp
  ultimately have "\<turnstile> \<^bold>S ?\<theta> ?A"
    by (rule Sub)
  moreover have "
    \<^bold>S ?\<theta> ?A = (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A =\<^bsub>?\<gamma>\<^esub> \<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) \<supset>\<^sup>\<Q> ((\<lambda>t\<^bsub>?\<gamma>\<^esub>. G) \<sqdot> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) \<equiv>\<^sup>\<Q> (\<lambda>t\<^bsub>?\<gamma>\<^esub>. G) \<sqdot> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B))"
    by simp
  ultimately have "\<section>1": "
    \<turnstile> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A =\<^bsub>?\<gamma>\<^esub> \<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) \<supset>\<^sup>\<Q> ((\<lambda>t\<^bsub>?\<gamma>\<^esub>. G) \<sqdot> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) \<equiv>\<^sup>\<Q> (\<lambda>t\<^bsub>?\<gamma>\<^esub>. G) \<sqdot> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B))"
    by (simp only:)
  then have "\<section>2": "\<turnstile> (\<forall>\<^sup>\<Q>\<^sub>\<star> vs (A =\<^bsub>\<alpha>\<^esub> B)) \<supset>\<^sup>\<Q> ((\<lambda>t\<^bsub>?\<gamma>\<^esub>. G) \<sqdot> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) \<equiv>\<^sup>\<Q> (\<lambda>t\<^bsub>?\<gamma>\<^esub>. G) \<sqdot> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B))"
  proof (cases "vs = []")
    case True
    with "\<section>1" show ?thesis
      by simp
  next
    case False
    from "\<section>1" and prop_5238[OF False \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> \<open>B \<in> wffs\<^bsub>\<alpha>\<^esub>\<close>] show ?thesis
      unfolding equivalence_def by (rule rule_R[where p = "[\<guillemotleft>,\<guillemotright>]"]) force+
  qed
  moreover have "\<turnstile> (\<lambda>t\<^bsub>?\<gamma>\<^esub>. G) \<sqdot> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) =\<^bsub>o\<^esub> C" and "\<turnstile> (\<lambda>t\<^bsub>?\<gamma>\<^esub>. G) \<sqdot> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) =\<^bsub>o\<^esub> D"
  proof -
    from assms(1) have "B \<preceq>\<^bsub>p\<^esub> D"
      using is_replacement_at_minimal_change(1) by force
    from assms(1) have "D\<lblot>p \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> t\<^bsub>?\<gamma>\<^esub> (map FVar vs))\<rblot> \<rhd> G"
      using \<open>C\<lblot>p \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> t\<^bsub>?\<gamma>\<^esub> (map FVar vs))\<rblot> \<rhd> G\<close> and replacement_override
      by (meson is_rule_R_app_def)
    from \<open>B \<preceq>\<^bsub>p\<^esub> D\<close> have "p \<in> positions D"
      using is_subform_implies_in_positions by auto
    from assms(1) have "binders_at D p = binders_at C p"
      using is_replacement_at_binders by fastforce
    then have "binders_at D p \<inter> free_vars B = binders_at C p \<inter> free_vars B"
      by simp
    with assms(2)
      [
        folded capture_exposed_vars_at_def,
        unfolded capture_exposed_vars_at_alt_def[OF \<open>p \<in> positions C\<close>]
      ] have "lset vs \<supseteq> capture_exposed_vars_at p D B"
      unfolding capture_exposed_vars_at_alt_def[OF \<open>p \<in> positions D\<close>] by auto
    have "is_free_for (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) (t, ?\<gamma>) G" and "is_free_for (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) (t, ?\<gamma>) G"
    proof -
      have "(t, ?\<gamma>) \<notin> lset vs \<union> vars {A, C}" and "(t, ?\<gamma>) \<notin> lset vs \<union> vars {B, D}"
        using \<open>(t, ?\<gamma>) \<notin> lset vs \<union> vars {A, B, C, D}\<close> by simp_all
      moreover from assms(2) have "
        lset vs \<supseteq> capture_exposed_vars_at p C A" and "lset vs \<supseteq> capture_exposed_vars_at p D B"
        by fastforce fact
      ultimately show "is_free_for (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) (t, ?\<gamma>) G" and "is_free_for (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) (t, ?\<gamma>) G"
        using prop_5239_aux_4 and \<open>B \<preceq>\<^bsub>p\<^esub> D\<close> and \<open>A \<preceq>\<^bsub>p\<^esub> C\<close> and \<open>C\<lblot>p \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> t\<^bsub>?\<gamma>\<^esub> (map FVar vs))\<rblot> \<rhd> G\<close>
        and \<open>D\<lblot>p \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> t\<^bsub>?\<gamma>\<^esub> (map FVar vs))\<rblot> \<rhd> G\<close> by meson+
    qed
    then have "\<turnstile> (\<lambda>t\<^bsub>?\<gamma>\<^esub>. G) \<sqdot> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) =\<^bsub>o\<^esub> \<^bold>S {(t, ?\<gamma>) \<Zinj> \<lambda>\<^sup>\<Q>\<^sub>\<star> vs A} G"
      and "\<turnstile> (\<lambda>t\<^bsub>?\<gamma>\<^esub>. G) \<sqdot> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) =\<^bsub>o\<^esub> \<^bold>S {(t, ?\<gamma>) \<Zinj> \<lambda>\<^sup>\<Q>\<^sub>\<star> vs B} G"
      using prop_5207[OF \<open>\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A \<in> wffs\<^bsub>?\<gamma>\<^esub>\<close> \<open>G \<in> wffs\<^bsub>o\<^esub>\<close>]
      and prop_5207[OF \<open>\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B \<in> wffs\<^bsub>?\<gamma>\<^esub>\<close> \<open>G \<in> wffs\<^bsub>o\<^esub>\<close>] by auto
    moreover obtain G'\<^sub>1 and G'\<^sub>2
      where "C\<lblot>p \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) (map FVar vs))\<rblot> \<rhd> G'\<^sub>1"
      and "D\<lblot>p \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) (map FVar vs))\<rblot> \<rhd> G'\<^sub>2"
      using is_replacement_at_existence[OF \<open>p \<in> positions C\<close>]
      and is_replacement_at_existence[OF \<open>p \<in> positions D\<close>] by metis
    then have "\<^bold>S {(t, ?\<gamma>) \<Zinj> \<lambda>\<^sup>\<Q>\<^sub>\<star> vs A} G = G'\<^sub>1" and "\<^bold>S {(t, ?\<gamma>) \<Zinj> \<lambda>\<^sup>\<Q>\<^sub>\<star> vs B} G = G'\<^sub>2"
    proof -
      have "(t, ?\<gamma>) \<notin> lset vs \<union> vars C" and "(t, ?\<gamma>) \<notin> lset vs \<union> vars D"
        using \<open>(t, ?\<gamma>) \<notin> lset vs \<union> vars {A, B, C, D}\<close> by simp_all
      then show "\<^bold>S {(t, ?\<gamma>) \<Zinj> \<lambda>\<^sup>\<Q>\<^sub>\<star> vs A} G = G'\<^sub>1" and "\<^bold>S {(t, ?\<gamma>) \<Zinj> \<lambda>\<^sup>\<Q>\<^sub>\<star> vs B} G = G'\<^sub>2"
        using \<open>C\<lblot>p \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> t\<^bsub>?\<gamma>\<^esub> (map FVar vs))\<rblot> \<rhd> G\<close> and \<open>D\<lblot>p \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> t\<^bsub>?\<gamma>\<^esub> map FVar vs)\<rblot> \<rhd> G\<close>
        and \<open>C\<lblot>p \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) (map FVar vs))\<rblot> \<rhd> G'\<^sub>1\<close>
        and \<open>D\<lblot>p \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) (map FVar vs))\<rblot> \<rhd> G'\<^sub>2\<close> and prop_5239_aux_2 by blast+
    qed
    ultimately have "\<turnstile> (\<lambda>t\<^bsub>?\<gamma>\<^esub>. G) \<sqdot> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) =\<^bsub>o\<^esub> G'\<^sub>1" and "\<turnstile> (\<lambda>t\<^bsub>?\<gamma>\<^esub>. G) \<sqdot> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) =\<^bsub>o\<^esub> G'\<^sub>2"
      by (simp_all only:)
    moreover
    have "\<turnstile> A =\<^bsub>\<alpha>\<^esub> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) (map FVar vs))" and "\<turnstile> B =\<^bsub>\<alpha>\<^esub> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) (map FVar vs))"
    unfolding atomize_conj proof (cases "vs = []")
      assume "vs = []"
      show "\<turnstile> A =\<^bsub>\<alpha>\<^esub> \<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) (map FVar vs) \<and> \<turnstile> B =\<^bsub>\<alpha>\<^esub> \<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) (map FVar vs)"
        unfolding \<open>vs = []\<close> using prop_5200 and \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> and \<open>B \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> by simp
    next
      assume "vs \<noteq> []"
      show "\<turnstile> A =\<^bsub>\<alpha>\<^esub> \<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) (map FVar vs) \<and> \<turnstile> B =\<^bsub>\<alpha>\<^esub> \<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) (map FVar vs)"
        using Equality_Rules(2)[OF prop_5208[OF \<open>vs \<noteq> []\<close>]] and \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> and \<open>B \<in> wffs\<^bsub>\<alpha>\<^esub>\<close>
        by blast+
    qed
    with
      \<open>C\<lblot>p \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) (map FVar vs))\<rblot> \<rhd> G'\<^sub>1\<close>
    and
      \<open>D\<lblot>p \<leftarrow> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) (map FVar vs))\<rblot> \<rhd> G'\<^sub>2\<close>
    have "\<turnstile> G'\<^sub>1 =\<^bsub>o\<^esub> C" and "\<turnstile> G'\<^sub>2 =\<^bsub>o\<^esub> D"
      using Equality_Rules(2)[OF replacement_derivability] and \<open>C \<in> wffs\<^bsub>o\<^esub>\<close> and \<open>D \<in> wffs\<^bsub>o\<^esub>\<close>
      and \<open>A \<preceq>\<^bsub>p\<^esub> C\<close> and \<open>B \<preceq>\<^bsub>p\<^esub> D\<close> by blast+
    ultimately show "\<turnstile> (\<lambda>t\<^bsub>?\<gamma>\<^esub>. G) \<sqdot> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) =\<^bsub>o\<^esub> C" and "\<turnstile> (\<lambda>t\<^bsub>?\<gamma>\<^esub>. G) \<sqdot> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) =\<^bsub>o\<^esub> D"
      using Equality_Rules(3) by blast+
  qed
  ultimately show ?thesis
  proof -
    from "\<section>2" and \<open>\<turnstile> (\<lambda>t\<^bsub>?\<gamma>\<^esub>. G) \<sqdot> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs A) =\<^bsub>o\<^esub> C\<close> have "
      \<turnstile> (\<forall>\<^sup>\<Q>\<^sub>\<star> vs (A =\<^bsub>\<alpha>\<^esub> B)) \<supset>\<^sup>\<Q> (C \<equiv>\<^sup>\<Q> (\<lambda>t\<^bsub>?\<gamma>\<^esub>. G) \<sqdot> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B))"
      by (rule rule_R[where p = "[\<guillemotright>,\<guillemotleft>,\<guillemotright>]"]) force+
    from this and \<open>\<turnstile> (\<lambda>t\<^bsub>?\<gamma>\<^esub>. G) \<sqdot> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) =\<^bsub>o\<^esub> D\<close> show ?thesis
      by (rule rule_R[where p = "[\<guillemotright>,\<guillemotright>]"]) force+
  qed
qed

end

subsection \<open>Theorem 5240 (Deduction Theorem)\<close>

lemma pseudo_rule_R_is_tautologous:
  assumes "C \<in> wffs\<^bsub>o\<^esub>" and "D \<in> wffs\<^bsub>o\<^esub>" and "E \<in> wffs\<^bsub>o\<^esub>" and "H \<in> wffs\<^bsub>o\<^esub>"
  shows "is_tautologous (((H \<supset>\<^sup>\<Q> C) \<supset>\<^sup>\<Q> ((H \<supset>\<^sup>\<Q> E) \<supset>\<^sup>\<Q> ((E \<supset>\<^sup>\<Q> (C \<equiv>\<^sup>\<Q> D)) \<supset>\<^sup>\<Q> (H \<supset>\<^sup>\<Q> D)))))"
proof -
  let ?\<theta> = "{(\<xx>, o) \<Zinj> C, (\<yy>, o) \<Zinj> D, (\<zz>, o) \<Zinj> E, (\<hh>, o) \<Zinj> H}"
  have "
    is_tautology
      (((\<hh>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub>) \<supset>\<^sup>\<Q> ((\<hh>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<zz>\<^bsub>o\<^esub>) \<supset>\<^sup>\<Q> ((\<zz>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) \<supset>\<^sup>\<Q> (\<hh>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)))))"
    using \<V>\<^sub>B_simps by simp
  moreover have "is_substitution ?\<theta>"
    using assms by auto
  moreover have "\<forall>(x, \<alpha>) \<in> fmdom' ?\<theta>. \<alpha> = o"
    by simp
  moreover have "
    ((H \<supset>\<^sup>\<Q> C) \<supset>\<^sup>\<Q> ((H \<supset>\<^sup>\<Q> E) \<supset>\<^sup>\<Q> ((E \<supset>\<^sup>\<Q> (C \<equiv>\<^sup>\<Q> D)) \<supset>\<^sup>\<Q> (H \<supset>\<^sup>\<Q> D))))
    =
    \<^bold>S ?\<theta> (((\<hh>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub>) \<supset>\<^sup>\<Q> ((\<hh>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<zz>\<^bsub>o\<^esub>) \<supset>\<^sup>\<Q> ((\<zz>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) \<supset>\<^sup>\<Q> (\<hh>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)))))"
    by simp
  ultimately show ?thesis
    by blast
qed

syntax
  "_HypDer" :: "form \<Rightarrow> form set \<Rightarrow> form \<Rightarrow> bool" ("_,_ \<turnstile> _" [50, 50, 50] 50)
translations
  "\<H>, H \<turnstile> P" \<rightharpoonup> "\<H> \<union> {H} \<turnstile> P"

theorem thm_5240:
  assumes "finite \<H>"
  and "\<H>, H \<turnstile> P"
  shows "\<H> \<turnstile> H \<supset>\<^sup>\<Q> P"
proof -
  from \<open>\<H>, H \<turnstile> P\<close> obtain \<S>\<^sub>1 and \<S>\<^sub>2 where *: "is_hyp_proof_of (\<H> \<union> {H}) \<S>\<^sub>1 \<S>\<^sub>2 P"
    using hyp_derivability_implies_hyp_proof_existence by blast
  have "\<H> \<turnstile> H \<supset>\<^sup>\<Q> (\<S>\<^sub>2 ! i')" if "i' <length \<S>\<^sub>2" for i'
  using that proof (induction i' rule: less_induct)
    case (less i')
    let ?R = "\<S>\<^sub>2 ! i'"
    from less.prems(1) and * have "is_hyps \<H>"
      by fastforce
    from less.prems and * have "?R \<in> wffs\<^bsub>o\<^esub>"
      using elem_of_proof_is_wffo[simplified] by auto
    from less.prems and * have "is_hyp_proof_step (\<H> \<union> {H}) \<S>\<^sub>1 \<S>\<^sub>2 i'"
      by simp
    then consider
      (hyp) "?R \<in> \<H> \<union> {H}"
    | (seq) "?R \<in> lset \<S>\<^sub>1"
    | (rule_R') "\<exists>j k p. {j, k} \<subseteq> {0..<i'} \<and> is_rule_R'_app (\<H> \<union> {H}) p ?R (\<S>\<^sub>2 ! j) (\<S>\<^sub>2 ! k)"
      by force
    then show ?case
    proof cases
      case hyp
      then show ?thesis
      proof (cases "?R = H")
        case True
        with \<open>?R \<in> wffs\<^bsub>o\<^esub>\<close> have "is_tautologous (H \<supset>\<^sup>\<Q> ?R)"
          using implication_reflexivity_is_tautologous by (simp only:)
        with \<open>is_hyps \<H>\<close> show ?thesis
          by (rule rule_P(2))
      next
        case False
        with hyp have "?R \<in> \<H>"
          by blast
        with \<open>is_hyps \<H>\<close> have "\<H> \<turnstile> ?R"
          by (intro dv_hyp)
        moreover from less.prems(1) and * have "is_tautologous (?R \<supset>\<^sup>\<Q> (H \<supset>\<^sup>\<Q> ?R))"
          using principle_of_simplification_is_tautologous[OF \<open>?R \<in> wffs\<^bsub>o\<^esub>\<close>] by force
        moreover from \<open>?R \<in> wffs\<^bsub>o\<^esub>\<close> have "is_hyps {?R}"
          by simp
        ultimately show ?thesis
          using rule_P(1)[where \<G> = "{?R}" and hs = "[?R]", OF \<open>is_hyps \<H>\<close>] by simp
      qed
    next
      case seq
      then have "\<S>\<^sub>1 \<noteq> []"
        by force
      moreover from less.prems(1) and * have "is_proof \<S>\<^sub>1"
        by fastforce
      moreover from seq obtain i'' where "i'' < length \<S>\<^sub>1" and "?R = \<S>\<^sub>1 ! i''"
        by (metis in_set_conv_nth)
      ultimately have "is_theorem ?R"
        using proof_form_is_theorem by fastforce
      with \<open>is_hyps \<H>\<close> have "\<H> \<turnstile> ?R"
        by (intro dv_thm)
      moreover from \<open>?R \<in> wffs\<^bsub>o\<^esub>\<close> and less.prems(1) and * have "is_tautologous (?R \<supset>\<^sup>\<Q> (H \<supset>\<^sup>\<Q> ?R))"
        using principle_of_simplification_is_tautologous by force
      moreover from \<open>?R \<in> wffs\<^bsub>o\<^esub>\<close> have "is_hyps {?R}"
        by simp
      ultimately show ?thesis
        using rule_P(1)[where \<G> = "{?R}" and hs = "[?R]", OF \<open>is_hyps \<H>\<close>] by simp
    next
      case rule_R'
      then obtain j and k and p
        where "{j, k} \<subseteq> {0..<i'}" and rule_R'_app: "is_rule_R'_app (\<H> \<union> {H}) p ?R (\<S>\<^sub>2 ! j) (\<S>\<^sub>2 ! k)"
        by auto
      then obtain A and B and C and \<alpha> where "C = \<S>\<^sub>2 ! j" and "\<S>\<^sub>2 ! k = A =\<^bsub>\<alpha>\<^esub> B"
        by fastforce
      with \<open>{j, k} \<subseteq> {0..<i'}\<close> have "\<H> \<turnstile> H \<supset>\<^sup>\<Q> C" and "\<H> \<turnstile> H \<supset>\<^sup>\<Q> (A =\<^bsub>\<alpha>\<^esub> B)"
        using less.IH and less.prems(1) by (simp, force)
      define S where "S \<equiv>
        {(x, \<beta>) | x \<beta> p' E. strict_prefix p' p \<and> \<lambda>x\<^bsub>\<beta>\<^esub>. E \<preceq>\<^bsub>p'\<^esub> C \<and> (x, \<beta>) \<in> free_vars (A =\<^bsub>\<alpha>\<^esub> B)}"
      with \<open>C = \<S>\<^sub>2 ! j\<close> and \<open>\<S>\<^sub>2 ! k = A =\<^bsub>\<alpha>\<^esub> B\<close> have "\<forall>v \<in> S. v \<notin> free_vars (\<H> \<union> {H})"
        using rule_R'_app by fastforce
      moreover have "S \<subseteq> free_vars (A =\<^bsub>\<alpha>\<^esub> B)"
        unfolding S_def by blast
      then have "finite S"
        by (fact rev_finite_subset[OF free_vars_form_finiteness])
      then obtain vs where "lset vs = S"
        using finite_list by blast
      ultimately have "\<H> \<turnstile> H \<supset>\<^sup>\<Q> \<forall>\<^sup>\<Q>\<^sub>\<star> vs (A =\<^bsub>\<alpha>\<^esub> B)"
        using generalized_prop_5237[OF \<open>is_hyps \<H>\<close> \<open>\<H> \<turnstile> H \<supset>\<^sup>\<Q> (A =\<^bsub>\<alpha>\<^esub> B)\<close>] by simp
      moreover have rule_R_app: "is_rule_R_app p ?R (\<S>\<^sub>2 ! j) (\<S>\<^sub>2 ! k)"
        using rule_R'_app by fastforce
      with S_def and \<open>lset vs = S\<close> have "\<turnstile> \<forall>\<^sup>\<Q>\<^sub>\<star> vs (A =\<^bsub>\<alpha>\<^esub> B) \<supset>\<^sup>\<Q> (C \<equiv>\<^sup>\<Q> ?R)"
        unfolding \<open>C = \<S>\<^sub>2 ! j\<close> and \<open>\<S>\<^sub>2 ! k = A =\<^bsub>\<alpha>\<^esub> B\<close> using prop_5239 by (simp only:)
      with \<open>is_hyps \<H>\<close> have "\<H> \<turnstile> \<forall>\<^sup>\<Q>\<^sub>\<star> vs (A =\<^bsub>\<alpha>\<^esub> B) \<supset>\<^sup>\<Q> (C \<equiv>\<^sup>\<Q> ?R)"
        by (elim derivability_implies_hyp_derivability)
      ultimately show ?thesis
      proof -
        let ?A\<^sub>1 = "H \<supset>\<^sup>\<Q> C" and ?A\<^sub>2 = "H \<supset>\<^sup>\<Q> \<forall>\<^sup>\<Q>\<^sub>\<star> vs (A =\<^bsub>\<alpha>\<^esub> B)"
          and ?A\<^sub>3 = "\<forall>\<^sup>\<Q>\<^sub>\<star> vs (A =\<^bsub>\<alpha>\<^esub> B) \<supset>\<^sup>\<Q> (C \<equiv>\<^sup>\<Q> ?R)"
        let ?hs = "[?A\<^sub>1, ?A\<^sub>2, ?A\<^sub>3]"
        let ?\<G> = "lset ?hs"
        from \<open>\<H> \<turnstile> ?A\<^sub>1\<close> have "H \<in> wffs\<^bsub>o\<^esub>"
          using hyp_derivable_form_is_wffso by (blast dest: wffs_from_imp_op(1))
        moreover from \<open>\<H> \<turnstile> ?A\<^sub>2\<close> have "\<forall>\<^sup>\<Q>\<^sub>\<star> vs (A =\<^bsub>\<alpha>\<^esub> B) \<in> wffs\<^bsub>o\<^esub>"
          using hyp_derivable_form_is_wffso by (blast dest: wffs_from_imp_op(2))
        moreover from \<open>C = \<S>\<^sub>2 ! j\<close> and rule_R_app have "C \<in> wffs\<^bsub>o\<^esub>"
          using replacement_preserves_typing by fastforce
        ultimately have *: "is_tautologous (?A\<^sub>1 \<supset>\<^sup>\<Q> (?A\<^sub>2 \<supset>\<^sup>\<Q> (?A\<^sub>3 \<supset>\<^sup>\<Q> (H \<supset>\<^sup>\<Q> ?R))))"
          using \<open>?R \<in> wffs\<^bsub>o\<^esub>\<close> by (intro pseudo_rule_R_is_tautologous)
        moreover from \<open>\<H> \<turnstile> ?A\<^sub>1\<close> and \<open>\<H> \<turnstile> ?A\<^sub>2\<close> and \<open>\<H> \<turnstile> ?A\<^sub>3\<close> have "is_hyps ?\<G>"
          using hyp_derivable_form_is_wffso by simp
        moreover from \<open>\<H> \<turnstile> ?A\<^sub>1\<close> and \<open>\<H> \<turnstile> ?A\<^sub>2\<close> and \<open>\<H> \<turnstile> ?A\<^sub>3\<close> have "\<forall>A \<in> ?\<G>. \<H> \<turnstile> A"
          by force
        ultimately show ?thesis
          using rule_P(1)[where \<G> = ?\<G> and hs = ?hs and B = "H \<supset>\<^sup>\<Q> ?R", OF \<open>is_hyps \<H>\<close>] by simp
      qed
    qed
  qed
  moreover from \<open>is_hyp_proof_of (\<H> \<union> {H}) \<S>\<^sub>1 \<S>\<^sub>2 P\<close> have "\<S>\<^sub>2 ! (length \<S>\<^sub>2 - 1) = P"
    using last_conv_nth by fastforce
  ultimately show ?thesis
    using \<open>is_hyp_proof_of (\<H> \<union> {H}) \<S>\<^sub>1 \<S>\<^sub>2 P\<close> by force
qed

lemmas Deduction_Theorem = thm_5240 (* synonym *)

text \<open>
  We prove a generalization of the Deduction Theorem, namely that if \<open>\<H> \<union> {H\<^sub>1, \<dots> ,H\<^sub>n} \<turnstile> P\<close> then
  \<open>\<H> \<turnstile> H\<^sub>1 \<supset>\<^sup>\<Q> (\<cdots> \<supset>\<^sup>\<Q> (H\<^sub>n \<supset>\<^sup>\<Q> P) \<cdots>)\<close>:
\<close>

corollary generalized_deduction_theorem:
  assumes "finite \<H>" and "finite \<H>'"
  and "\<H> \<union> \<H>' \<turnstile> P"
  and "lset hs = \<H>'"
  shows "\<H> \<turnstile> hs \<supset>\<^sup>\<Q>\<^sub>\<star> P"
using assms proof (induction hs arbitrary: \<H>' P rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc H hs)
  from \<open>lset (hs @ [H]) = \<H>'\<close> have "H \<in> \<H>'"
    by fastforce
  from \<open>lset (hs @ [H]) = \<H>'\<close> obtain \<H>'' where "\<H>'' \<union> {H} = \<H>'" and "\<H>'' = lset hs"
    by simp
  from \<open>\<H>'' \<union> {H} = \<H>'\<close> and \<open>\<H> \<union> \<H>' \<turnstile> P\<close> have "\<H> \<union> \<H>'' \<union> {H} \<turnstile> P"
    by fastforce
  with \<open>finite \<H>\<close> and \<open>finite \<H>'\<close> and \<open>\<H>'' = lset hs\<close> have "\<H> \<union> \<H>'' \<turnstile> H \<supset>\<^sup>\<Q> P"
    using Deduction_Theorem by simp
  with \<open>\<H>'' = lset hs\<close> and \<open>finite \<H>\<close> have "\<H> \<turnstile> foldr (\<supset>\<^sup>\<Q>) hs (H \<supset>\<^sup>\<Q> P)"
    using snoc.IH by fastforce
  moreover have "(hs @ [H]) \<supset>\<^sup>\<Q>\<^sub>\<star> P = hs \<supset>\<^sup>\<Q>\<^sub>\<star> (H \<supset>\<^sup>\<Q> P)"
    by simp
  ultimately show ?case
    by auto
qed

subsection \<open>Proposition 5241\<close>

proposition prop_5241:
  assumes "is_hyps \<G>"
  and "\<H> \<turnstile> A" and "\<H> \<subseteq> \<G>"
  shows "\<G> \<turnstile> A"
proof (cases "\<H> = {}")
  case True
  show ?thesis
    by (fact derivability_implies_hyp_derivability[OF assms(2)[unfolded True] assms(1)])
next
  case False
  then obtain hs where "lset hs = \<H>" and "hs \<noteq> []"
    using hyp_derivability_implies_hyp_proof_existence[OF assms(2)] unfolding is_hyp_proof_of_def
    by (metis empty_set finite_list)
  with assms(2) have "\<turnstile> hs \<supset>\<^sup>\<Q>\<^sub>\<star> A"
    using generalized_deduction_theorem by force
  moreover from \<open>lset hs = \<H>\<close> and assms(1,3) have "\<G> \<turnstile> H" if "H \<in> lset hs" for H
    using that by (blast intro: dv_hyp)
  ultimately show ?thesis
    using assms(1) and generalized_modus_ponens and derivability_implies_hyp_derivability by meson
qed

subsection \<open>Proposition 5242 (Rule of Existential Generalization)\<close>

proposition prop_5242:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
  and "\<H> \<turnstile> \<^bold>S {(x, \<alpha>) \<Zinj> A} B"
  and "is_free_for A (x, \<alpha>) B"
  shows "\<H> \<turnstile> \<exists>x\<^bsub>\<alpha>\<^esub>. B"
proof -
  from assms(3) have "is_hyps \<H>"
    by (blast dest: is_derivable_from_hyps.cases)
  then have "\<H> \<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. \<sim>\<^sup>\<Q> B \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> \<^bold>S {(x, \<alpha>) \<Zinj> A} B" (is \<open>\<H> \<turnstile> ?C \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> ?D\<close>)
    using prop_5226[OF assms(1) neg_wff[OF assms(2)] is_free_for_in_neg[OF assms(4)]]
    unfolding derived_substitution_simps(4) using derivability_implies_hyp_derivability by (simp only:)
  moreover have *: "is_tautologous ((?C \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> ?D) \<supset>\<^sup>\<Q> (?D \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> ?C))"
  proof -
    have "?C \<in> wffs\<^bsub>o\<^esub>" and "?D \<in> wffs\<^bsub>o\<^esub>"
      using assms(2) and hyp_derivable_form_is_wffso[OF assms(3)] by auto
    then show ?thesis
      by (fact pseudo_modus_tollens_is_tautologous)
  qed
  moreover from assms(3) and \<open>\<H> \<turnstile> ?C \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> ?D\<close> have "is_hyps {?C \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> ?D, ?D}"
    using hyp_derivable_form_is_wffso by force
  ultimately show ?thesis
    unfolding exists_def using assms(3)
    and rule_P(1)
      [
        where \<G> = "{?C \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> ?D, ?D}" and hs = "[?C \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> ?D, ?D]" and B = "\<sim>\<^sup>\<Q> ?C",
        OF \<open>is_hyps \<H>\<close>
      ]
    by simp
qed

lemmas "\<exists>Gen" = prop_5242 (* synonym *)

subsection \<open>Proposition 5243 (Comprehension Theorem)\<close>

context
begin

private lemma prop_5243_aux:
  assumes "\<sqdot>\<^sup>\<Q>\<^sub>\<star> B (map FVar vs) \<in> wffs\<^bsub>\<gamma>\<^esub>"
  and "B \<in> wffs\<^bsub>\<beta>\<^esub>"
  and "k < length vs"
  shows "\<beta> \<noteq> var_type (vs ! k)"
proof -
  from assms(1) obtain ts
    where "length ts = length (map FVar vs)"
    and *: "\<forall>k < length (map FVar vs). (map FVar vs) ! k \<in> wffs\<^bsub>ts ! k\<^esub>"
    and "B \<in> wffs\<^bsub>foldr (\<rightarrow>) ts \<gamma>\<^esub>"
    using wffs_from_generalized_app by force
  have "\<beta> = foldr (\<rightarrow>) ts \<gamma>"
    by (fact wff_has_unique_type[OF assms(2) \<open>B \<in> wffs\<^bsub>foldr (\<rightarrow>) ts \<gamma>\<^esub>\<close>])
  have "ts = map var_type vs"
  proof -
    have "length ts = length (map var_type vs)"
      by (simp add: \<open>length ts = length (map FVar vs)\<close>)
    moreover have "\<forall>k < length ts. ts ! k = (map var_type vs) ! k"
    proof (intro allI impI)
      fix k
      assume "k < length ts"
      with * have "(map FVar vs) ! k \<in> wffs\<^bsub>ts ! k\<^esub>"
        by (simp add: \<open>length ts = length (map FVar vs)\<close>)
      with \<open>k < length ts\<close> and \<open>length ts = length (map var_type vs)\<close>
      show "ts ! k = (map var_type vs) ! k"
        using surj_pair[of "vs ! k"] and wff_has_unique_type and wffs_of_type_intros(1) by force
    qed
    ultimately show ?thesis
      using list_eq_iff_nth_eq by blast
  qed
  with \<open>\<beta> = foldr (\<rightarrow>) ts \<gamma>\<close> and assms(3) show ?thesis
    using fun_type_atoms_neq_fun_type by (metis length_map nth_map)
qed

proposition prop_5243:
  assumes "B \<in> wffs\<^bsub>\<beta>\<^esub>"
  and "\<gamma> = foldr (\<rightarrow>) (map var_type vs) \<beta>"
  and "(u, \<gamma>) \<notin> free_vars B"
  shows "\<turnstile> \<exists>u\<^bsub>\<gamma>\<^esub>. \<forall>\<^sup>\<Q>\<^sub>\<star> vs ((\<sqdot>\<^sup>\<Q>\<^sub>\<star> u\<^bsub>\<gamma>\<^esub> (map FVar vs)) =\<^bsub>\<beta>\<^esub> B)"
proof (cases "vs = []")
  case True
  with assms(2) have "\<gamma> = \<beta>"
    by simp
  from assms(1) have "u\<^bsub>\<beta>\<^esub> =\<^bsub>\<beta>\<^esub> B \<in> wffs\<^bsub>o\<^esub>"
    by blast
  moreover have "\<turnstile> B =\<^bsub>\<beta>\<^esub> B"
    by (fact prop_5200[OF assms(1)])
  then have "\<turnstile> \<^bold>S {(u, \<beta>) \<Zinj> B} (u\<^bsub>\<beta>\<^esub> =\<^bsub>\<beta>\<^esub> B)"
    using free_var_singleton_substitution_neutrality[OF assms(3)] unfolding \<open>\<gamma> = \<beta>\<close> by simp
  moreover from assms(3)[unfolded \<open>\<gamma> = \<beta>\<close>] have "is_free_for B (u, \<beta>) (u\<^bsub>\<beta>\<^esub> =\<^bsub>\<beta>\<^esub> B)"
    by (intro is_free_for_in_equality) (use is_free_at_in_free_vars in auto)
  ultimately have "\<turnstile> \<exists>u\<^bsub>\<beta>\<^esub>. (u\<^bsub>\<beta>\<^esub> =\<^bsub>\<beta>\<^esub> B)"
    by (rule "\<exists>Gen"[OF assms(1)])
  with \<open>\<gamma> = \<beta>\<close> and True show ?thesis
    by simp
next
  case False
  let ?\<theta> = "{(u, \<gamma>) \<Zinj> \<lambda>\<^sup>\<Q>\<^sub>\<star> vs B}"
  from assms(2) have *: "(u, \<gamma>) \<noteq> v" if "v \<in> lset vs" for v
    using that and fun_type_atoms_neq_fun_type by (metis in_set_conv_nth length_map nth_map snd_conv)
  from False and assms(1) have "\<turnstile> \<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) (map FVar vs) =\<^bsub>\<beta>\<^esub> B"
    by (fact prop_5208)
  then have "\<turnstile> \<forall>\<^sup>\<Q>\<^sub>\<star> vs (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) (map FVar vs) =\<^bsub>\<beta>\<^esub> B)"
    using generalized_Gen by simp
  moreover
  have "\<^bold>S ?\<theta> (\<forall>\<^sup>\<Q>\<^sub>\<star> vs ((\<sqdot>\<^sup>\<Q>\<^sub>\<star> u\<^bsub>\<gamma>\<^esub> (map FVar vs)) =\<^bsub>\<beta>\<^esub> B)) = \<forall>\<^sup>\<Q>\<^sub>\<star> vs (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) (map FVar vs) =\<^bsub>\<beta>\<^esub> B)"
  proof -
    from * have **: "map (\<lambda>A. \<^bold>S {(u, \<gamma>) \<Zinj> B} A) (map FVar vs) = map FVar vs" for B
      by (induction vs) fastforce+
    from * have "
      \<^bold>S ?\<theta> (\<forall>\<^sup>\<Q>\<^sub>\<star> vs ((\<sqdot>\<^sup>\<Q>\<^sub>\<star> u\<^bsub>\<gamma>\<^esub> (map FVar vs)) =\<^bsub>\<beta>\<^esub> B)) = \<forall>\<^sup>\<Q>\<^sub>\<star> vs (\<^bold>S ?\<theta> ((\<sqdot>\<^sup>\<Q>\<^sub>\<star> u\<^bsub>\<gamma>\<^esub> (map FVar vs)) =\<^bsub>\<beta>\<^esub> B))"
      using generalized_forall_substitution by force
    also have "\<dots> = \<forall>\<^sup>\<Q>\<^sub>\<star> vs ((\<^bold>S ?\<theta> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> u\<^bsub>\<gamma>\<^esub> (map FVar vs))) =\<^bsub>\<beta>\<^esub> \<^bold>S {(u, \<gamma>) \<Zinj> \<lambda>\<^sup>\<Q>\<^sub>\<star> vs B} B)"
      by simp
    also from assms(3) have "\<dots> = \<forall>\<^sup>\<Q>\<^sub>\<star> vs ((\<^bold>S ?\<theta> (\<sqdot>\<^sup>\<Q>\<^sub>\<star> u\<^bsub>\<gamma>\<^esub> (map FVar vs))) =\<^bsub>\<beta>\<^esub> B)"
      using free_var_singleton_substitution_neutrality by simp
    also have "\<dots> = \<forall>\<^sup>\<Q>\<^sub>\<star> vs (\<sqdot>\<^sup>\<Q>\<^sub>\<star> \<^bold>S ?\<theta> (u\<^bsub>\<gamma>\<^esub>) (map (\<lambda>A. \<^bold>S ?\<theta> A) (map FVar vs)) =\<^bsub>\<beta>\<^esub> B)"
      using generalized_app_substitution by simp
    also have "\<dots> = \<forall>\<^sup>\<Q>\<^sub>\<star> vs (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) (map (\<lambda>A. \<^bold>S ?\<theta> A) (map FVar vs)) =\<^bsub>\<beta>\<^esub> B)"
      by simp
    also from ** have "\<dots> = \<forall>\<^sup>\<Q>\<^sub>\<star> vs (\<sqdot>\<^sup>\<Q>\<^sub>\<star> (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) (map FVar vs) =\<^bsub>\<beta>\<^esub> B)"
      by presburger
    finally show ?thesis .
  qed
  ultimately have "\<turnstile> \<^bold>S ?\<theta> (\<forall>\<^sup>\<Q>\<^sub>\<star> vs (\<sqdot>\<^sup>\<Q>\<^sub>\<star> u\<^bsub>\<gamma>\<^esub> (map FVar vs) =\<^bsub>\<beta>\<^esub> B))"
    by simp
  moreover from assms(3) have "is_free_for (\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B) (u, \<gamma>) (\<forall>\<^sup>\<Q>\<^sub>\<star> vs (\<sqdot>\<^sup>\<Q>\<^sub>\<star> u\<^bsub>\<gamma>\<^esub> (map FVar vs) =\<^bsub>\<beta>\<^esub> B))"
    by
      (intro is_free_for_in_generalized_forall is_free_for_in_equality is_free_for_in_generalized_app)
      (use free_vars_of_generalized_abs is_free_at_in_free_vars in \<open>fastforce+\<close>)
  moreover have "\<lambda>\<^sup>\<Q>\<^sub>\<star> vs B \<in> wffs\<^bsub>\<gamma>\<^esub>" and "\<forall>\<^sup>\<Q>\<^sub>\<star> vs (\<sqdot>\<^sup>\<Q>\<^sub>\<star> u\<^bsub>\<gamma>\<^esub> (map FVar vs) =\<^bsub>\<beta>\<^esub> B) \<in> wffs\<^bsub>o\<^esub>"
  proof -
    have "FVar (vs ! k) \<in> wffs\<^bsub>var_type (vs ! k)\<^esub>" if "k < length vs" for k
      using that and surj_pair[of "vs ! k"] by fastforce
    with assms(2) have "\<sqdot>\<^sup>\<Q>\<^sub>\<star> u\<^bsub>\<gamma>\<^esub> (map FVar vs) \<in> wffs\<^bsub>\<beta>\<^esub>"
      using generalized_app_wff[where ts = "map var_type vs"] by force
    with assms(1) show "\<forall>\<^sup>\<Q>\<^sub>\<star> vs (\<sqdot>\<^sup>\<Q>\<^sub>\<star> u\<^bsub>\<gamma>\<^esub> (map FVar vs) =\<^bsub>\<beta>\<^esub> B) \<in> wffs\<^bsub>o\<^esub>"
      by (auto simp only:)
  qed (use assms(1,2) in blast)
  ultimately show ?thesis
    using "\<exists>Gen" by (simp only:)
qed

end

subsection \<open>Proposition 5244 (Existential Rule)\<close>

text \<open>
  The proof in @{cite "andrews:2002"} uses the pseudo-rule Q and 2123 of \<open>\<F>\<close>. Therefore, we instead
  base our proof on the proof of Theorem 170 in @{cite "andrews:1965"}:
\<close>

lemma prop_5244_aux:
  assumes "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
  and "(x, \<alpha>) \<notin> free_vars A"
  shows "\<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. (B \<supset>\<^sup>\<Q> A) \<supset>\<^sup>\<Q> (\<exists>x\<^bsub>\<alpha>\<^esub>. B \<supset>\<^sup>\<Q> A)"
proof -
  have "B \<supset>\<^sup>\<Q> A \<in> wffs\<^bsub>o\<^esub>"
    using assms by blast
  moreover have "is_free_for (x\<^bsub>\<alpha>\<^esub>) (x, \<alpha>) (B \<supset>\<^sup>\<Q> A)"
    by simp
  ultimately have "\<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. (B \<supset>\<^sup>\<Q> A) \<supset>\<^sup>\<Q> (B \<supset>\<^sup>\<Q> A)"
    using prop_5226[where A = "x\<^bsub>\<alpha>\<^esub>" and B = "B \<supset>\<^sup>\<Q> A", OF wffs_of_type_intros(1)]
    and identity_singleton_substitution_neutrality by metis
  moreover have "is_hyps {\<forall>x\<^bsub>\<alpha>\<^esub>. (B \<supset>\<^sup>\<Q> A)}"
    using \<open>B \<supset>\<^sup>\<Q> A \<in> wffs\<^bsub>o\<^esub>\<close> by blast
  ultimately have "\<section>1": "{\<forall>x\<^bsub>\<alpha>\<^esub>. (B \<supset>\<^sup>\<Q> A)} \<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. (B \<supset>\<^sup>\<Q> A) \<supset>\<^sup>\<Q> (B \<supset>\<^sup>\<Q> A)"
    by (fact derivability_implies_hyp_derivability)
  have "\<section>2": "{\<forall>x\<^bsub>\<alpha>\<^esub>. (B \<supset>\<^sup>\<Q> A)} \<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. (B \<supset>\<^sup>\<Q> A)"
    using \<open>B \<supset>\<^sup>\<Q> A \<in> wffs\<^bsub>o\<^esub>\<close> by (blast intro: dv_hyp)
  have "\<section>3": "{\<forall>x\<^bsub>\<alpha>\<^esub>. (B \<supset>\<^sup>\<Q> A)} \<turnstile> \<sim>\<^sup>\<Q> A \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> B"
  proof (intro rule_P(1)
    [where \<H> = "{\<forall>x\<^bsub>\<alpha>\<^esub>. (B \<supset>\<^sup>\<Q> A)}" and \<G> = "{\<forall>x\<^bsub>\<alpha>\<^esub>. (B \<supset>\<^sup>\<Q> A) \<supset>\<^sup>\<Q> (B \<supset>\<^sup>\<Q> A), \<forall>x\<^bsub>\<alpha>\<^esub>. (B \<supset>\<^sup>\<Q> A)}"])
    have "is_tautologous ([C \<supset>\<^sup>\<Q> (B \<supset>\<^sup>\<Q> A), C] \<supset>\<^sup>\<Q>\<^sub>\<star> (\<sim>\<^sup>\<Q> A \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> B))" if "C \<in> wffs\<^bsub>o\<^esub>" for C
    proof -
      let ?\<theta> = "{(\<xx>, o) \<Zinj> A, (\<yy>, o) \<Zinj> B, (\<zz>, o) \<Zinj> C}"
      have "is_tautology ((\<zz>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> (\<yy>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub>)) \<supset>\<^sup>\<Q> (\<zz>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> (\<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)))"
        (is "is_tautology ?A")
        using \<V>\<^sub>B_simps by (auto simp add: inj_eq)
      moreover have "is_pwff_substitution ?\<theta>"
        using assms(1,2) and that by auto
      moreover have "[C \<supset>\<^sup>\<Q> (B \<supset>\<^sup>\<Q> A), C] \<supset>\<^sup>\<Q>\<^sub>\<star> (\<sim>\<^sup>\<Q> A \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> B) = \<^bold>S ?\<theta> ?A"
        by simp
      ultimately show ?thesis
        by blast
    qed
    then show "is_tautologous ([\<forall>x\<^bsub>\<alpha>\<^esub>. (B \<supset>\<^sup>\<Q> A) \<supset>\<^sup>\<Q> (B \<supset>\<^sup>\<Q> A), \<forall>x\<^bsub>\<alpha>\<^esub>. (B \<supset>\<^sup>\<Q> A)] \<supset>\<^sup>\<Q>\<^sub>\<star> (\<sim>\<^sup>\<Q> A \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> B))"
      using \<open>B \<supset>\<^sup>\<Q> A \<in> wffs\<^bsub>o\<^esub>\<close> and forall_wff by simp
  qed (use "\<section>1" "\<section>2" \<open>is_hyps {\<forall>x\<^bsub>\<alpha>\<^esub>. (B \<supset>\<^sup>\<Q> A)}\<close> hyp_derivable_form_is_wffso[OF "\<section>1"] in force)+
  have "\<section>4": "{\<forall>x\<^bsub>\<alpha>\<^esub>. (B \<supset>\<^sup>\<Q> A)} \<turnstile> \<sim>\<^sup>\<Q> A \<supset>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. \<sim>\<^sup>\<Q> B"
    using prop_5237[OF \<open>is_hyps {\<forall>x\<^bsub>\<alpha>\<^esub>. (B \<supset>\<^sup>\<Q> A)}\<close> "\<section>3"] and assms(3) by auto
  have "\<section>5": "{\<forall>x\<^bsub>\<alpha>\<^esub>. (B \<supset>\<^sup>\<Q> A)} \<turnstile> \<exists>x\<^bsub>\<alpha>\<^esub>. B \<supset>\<^sup>\<Q> A"
  unfolding exists_def
  proof (intro rule_P(1)[where \<H> = "{\<forall>x\<^bsub>\<alpha>\<^esub>. (B \<supset>\<^sup>\<Q> A)}" and \<G> = "{\<sim>\<^sup>\<Q> A \<supset>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. \<sim>\<^sup>\<Q> B}"])
    have "is_tautologous ([\<sim>\<^sup>\<Q> A \<supset>\<^sup>\<Q> C] \<supset>\<^sup>\<Q>\<^sub>\<star> (\<sim>\<^sup>\<Q> C \<supset>\<^sup>\<Q> A))" if "C \<in> wffs\<^bsub>o\<^esub>" for C
    proof -
      let ?\<theta> = "{(\<xx>, o) \<Zinj> A, (\<yy>, o) \<Zinj> C}"
      have "is_tautology ((\<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>) \<supset>\<^sup>\<Q> (\<sim>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub>))" (is "is_tautology ?A")
        using \<V>\<^sub>B_simps by (auto simp add: inj_eq)
      moreover have "is_pwff_substitution ?\<theta>"
        using assms(1) and that by auto
      moreover have "[\<sim>\<^sup>\<Q> A \<supset>\<^sup>\<Q> C] \<supset>\<^sup>\<Q>\<^sub>\<star> (\<sim>\<^sup>\<Q> C \<supset>\<^sup>\<Q> A) = \<^bold>S ?\<theta> ?A"
        by simp
      ultimately show ?thesis
        by blast
    qed
    then show "is_tautologous ([\<sim>\<^sup>\<Q> A \<supset>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. \<sim>\<^sup>\<Q> B] \<supset>\<^sup>\<Q>\<^sub>\<star> (\<sim>\<^sup>\<Q> \<forall>x\<^bsub>\<alpha>\<^esub>. \<sim>\<^sup>\<Q> B \<supset>\<^sup>\<Q> A))"
      using forall_wff[OF neg_wff[OF assms(2)]] by (simp only:)
  qed (use "\<section>4" \<open>is_hyps {\<forall>x\<^bsub>\<alpha>\<^esub>. (B \<supset>\<^sup>\<Q> A)}\<close> hyp_derivable_form_is_wffso[OF "\<section>4"] in force)+
  then show ?thesis
    using Deduction_Theorem by simp
qed

proposition prop_5244:
  assumes "\<H>, B \<turnstile> A"
  and "(x, \<alpha>) \<notin> free_vars (\<H> \<union> {A})"
  shows "\<H>, \<exists>x\<^bsub>\<alpha>\<^esub>. B \<turnstile> A"
proof -
  from assms(1) have "is_hyps \<H>"
    using hyp_derivability_implies_hyp_proof_existence by force
  then have "\<H> \<turnstile> B \<supset>\<^sup>\<Q> A"
    using assms(1) and Deduction_Theorem by simp
  then have "\<H> \<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. (B \<supset>\<^sup>\<Q> A)"
    using Gen and assms(2) by simp
  moreover have "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
    by
    (
      fact hyp_derivable_form_is_wffso[OF assms(1)],
      fact hyp_derivable_form_is_wffso[OF \<open>\<H> \<turnstile> B \<supset>\<^sup>\<Q> A\<close>, THEN wffs_from_imp_op(1)]
    )
  with assms(2) and \<open>is_hyps \<H>\<close> have "\<H> \<turnstile> \<forall>x\<^bsub>\<alpha>\<^esub>. (B \<supset>\<^sup>\<Q> A) \<supset>\<^sup>\<Q> (\<exists>x\<^bsub>\<alpha>\<^esub>. B \<supset>\<^sup>\<Q> A)"
    using prop_5244_aux[THEN derivability_implies_hyp_derivability] by simp
  ultimately have "\<H> \<turnstile> \<exists>x\<^bsub>\<alpha>\<^esub>. B \<supset>\<^sup>\<Q> A"
    by (rule MP)
  then have "\<H>, \<exists>x\<^bsub>\<alpha>\<^esub>. B \<turnstile> \<exists>x\<^bsub>\<alpha>\<^esub>. B \<supset>\<^sup>\<Q> A"
    using prop_5241 and exists_wff[OF \<open>B \<in> wffs\<^bsub>o\<^esub>\<close>] and \<open>is_hyps \<H>\<close>
    by (meson Un_subset_iff empty_subsetI finite.simps finite_Un inf_sup_ord(3) insert_subsetI)
  moreover from \<open>is_hyps \<H>\<close> and \<open>B \<in> wffs\<^bsub>o\<^esub>\<close> have "is_hyps (\<H> \<union> {\<exists>x\<^bsub>\<alpha>\<^esub>. B})"
    by auto
  then have "\<H>, \<exists>x\<^bsub>\<alpha>\<^esub>. B \<turnstile> \<exists>x\<^bsub>\<alpha>\<^esub>. B"
    using dv_hyp by simp
  ultimately show ?thesis
    using MP by blast
qed

lemmas "\<exists>_Rule" = prop_5244 (* synonym *)

subsection \<open>Proposition 5245 (Rule C)\<close>

lemma prop_5245_aux:
  assumes "x \<noteq> y"
  and "(y, \<alpha>) \<notin> free_vars (\<exists>x\<^bsub>\<alpha>\<^esub>. B)"
  and "is_free_for (y\<^bsub>\<alpha>\<^esub>) (x, \<alpha>) B"
  shows "is_free_for (x\<^bsub>\<alpha>\<^esub>) (y, \<alpha>) \<^bold>S {(x, \<alpha>) \<Zinj> y\<^bsub>\<alpha>\<^esub>} B"
using assms(2,3) proof (induction B)
  case (FVar v)
  then show ?case
    using surj_pair[of v] by fastforce
next
  case (FCon k)
  then show ?case
    using surj_pair[of k] by fastforce
next
  case (FApp B\<^sub>1 B\<^sub>2)
  from FApp.prems(1) have "(y, \<alpha>) \<notin> free_vars (\<exists>x\<^bsub>\<alpha>\<^esub>. B\<^sub>1)" and "(y, \<alpha>) \<notin> free_vars (\<exists>x\<^bsub>\<alpha>\<^esub>. B\<^sub>2)"
    by force+
  moreover from FApp.prems(2) have "is_free_for (y\<^bsub>\<alpha>\<^esub>) (x, \<alpha>) B\<^sub>1" and "is_free_for (y\<^bsub>\<alpha>\<^esub>) (x, \<alpha>) B\<^sub>2"
    using is_free_for_from_app by iprover+
  ultimately have "is_free_for (x\<^bsub>\<alpha>\<^esub>) (y, \<alpha>) \<^bold>S {(x, \<alpha>) \<Zinj> y\<^bsub>\<alpha>\<^esub>} B\<^sub>1"
    and "is_free_for (x\<^bsub>\<alpha>\<^esub>) (y, \<alpha>) \<^bold>S {(x, \<alpha>) \<Zinj> y\<^bsub>\<alpha>\<^esub>} B\<^sub>2"
    using FApp.IH by simp_all
  then have "is_free_for (x\<^bsub>\<alpha>\<^esub>) (y, \<alpha>) ((\<^bold>S {(x, \<alpha>) \<Zinj> y\<^bsub>\<alpha>\<^esub>} B\<^sub>1) \<sqdot> (\<^bold>S {(x, \<alpha>) \<Zinj> y\<^bsub>\<alpha>\<^esub>} B\<^sub>2))"
    by (intro is_free_for_to_app)
  then show ?case
    unfolding singleton_substitution_simps(3) .
next
  case (FAbs v B')
  obtain z and \<beta> where "v = (z, \<beta>)"
    by fastforce
  then show ?case
  proof (cases "v = (x, \<alpha>)")
    case True
    with FAbs.prems(1) have "(y, \<alpha>) \<notin> free_vars (\<exists>x\<^bsub>\<alpha>\<^esub>. B')"
      by simp
    moreover from assms(1) have "(y, \<alpha>) \<noteq> (x, \<alpha>)"
      by blast
    ultimately have "(y, \<alpha>) \<notin> free_vars B'"
      using FAbs.prems(1) by simp
    with \<open>(y, \<alpha>) \<noteq> (x, \<alpha>)\<close> have "(y, \<alpha>) \<notin> free_vars (\<lambda>x\<^bsub>\<alpha>\<^esub>. B')"
      by simp
    then have "is_free_for (x\<^bsub>\<alpha>\<^esub>) (y, \<alpha>) (\<lambda>x\<^bsub>\<alpha>\<^esub>. B')"
      unfolding is_free_for_def using is_free_at_in_free_vars by blast
    then have "is_free_for (x\<^bsub>\<alpha>\<^esub>) (y, \<alpha>) \<^bold>S {(x, \<alpha>) \<Zinj> y\<^bsub>\<alpha>\<^esub>} (\<lambda>x\<^bsub>\<alpha>\<^esub>. B')"
      using singleton_substitution_simps(4) by presburger
    then show ?thesis
      unfolding True .
  next
    case False
    from assms(1) have "(y, \<alpha>) \<noteq> (x, \<alpha>)"
      by blast
    with FAbs.prems(1) have *: "(y, \<alpha>) \<notin> free_vars (\<exists>x\<^bsub>\<alpha>\<^esub>. (\<lambda>z\<^bsub>\<beta>\<^esub>. B'))"
      using \<open>v = (z, \<beta>)\<close> by fastforce
    then show ?thesis
    proof (cases "(y, \<alpha>) \<noteq> v")
      case True
      from True[unfolded \<open>v = (z, \<beta>)\<close>] and * have "(y, \<alpha>) \<notin> free_vars (\<exists>x\<^bsub>\<alpha>\<^esub>. B')"
        by simp
      moreover from False[unfolded \<open>v = (z, \<beta>)\<close>] have "is_free_for (y\<^bsub>\<alpha>\<^esub>) (x, \<alpha>) B'"
        using is_free_for_from_abs[OF FAbs.prems(2)[unfolded \<open>v = (z, \<beta>)\<close>]] by blast
      ultimately have "is_free_for (x\<^bsub>\<alpha>\<^esub>) (y, \<alpha>) (\<^bold>S {(x, \<alpha>) \<Zinj> y\<^bsub>\<alpha>\<^esub>} B')"
        by (fact FAbs.IH)
      then have "is_free_for (x\<^bsub>\<alpha>\<^esub>) (y, \<alpha>) (\<lambda>z\<^bsub>\<beta>\<^esub>. (\<^bold>S {(x, \<alpha>) \<Zinj> y\<^bsub>\<alpha>\<^esub>} B'))"
        using False[unfolded \<open>v = (z, \<beta>)\<close>] by (intro is_free_for_to_abs, fastforce+)
      then show ?thesis
        unfolding singleton_substitution_simps(4) and \<open>v = (z, \<beta>)\<close> using \<open>(z, \<beta>) \<noteq> (x, \<alpha>)\<close> by auto
    next
      case False
      then have "v = (y, \<alpha>)"
        by simp
      have "is_free_for (x\<^bsub>\<alpha>\<^esub>) (y, \<alpha>) (\<lambda>y\<^bsub>\<alpha>\<^esub>. \<^bold>S {(x, \<alpha>) \<Zinj> y\<^bsub>\<alpha>\<^esub>} B')"
      proof-
        have "(y, \<alpha>) \<notin> free_vars (\<lambda>y\<^bsub>\<alpha>\<^esub>. \<^bold>S {(x, \<alpha>) \<Zinj> y\<^bsub>\<alpha>\<^esub>} B')"
          by simp
        then show ?thesis
          using is_free_at_in_free_vars by blast
      qed
      with\<open>v = (y, \<alpha>)\<close> and \<open>(y, \<alpha>) \<noteq> (x, \<alpha>)\<close> show ?thesis
       using singleton_substitution_simps(4) by presburger
    qed
  qed
qed

proposition prop_5245:
  assumes "\<H> \<turnstile> \<exists>x\<^bsub>\<alpha>\<^esub>. B"
  and "\<H>, \<^bold>S {(x, \<alpha>) \<Zinj> y\<^bsub>\<alpha>\<^esub>} B \<turnstile> A"
  and "is_free_for (y\<^bsub>\<alpha>\<^esub>) (x, \<alpha>) B"
  and "(y, \<alpha>) \<notin> free_vars (\<H> \<union> {\<exists>x\<^bsub>\<alpha>\<^esub>. B, A})"
  shows "\<H> \<turnstile> A"
proof -
  from assms(1) have "is_hyps \<H>"
    by (blast elim: is_derivable_from_hyps.cases)
  from assms(2,4) have "\<H>, \<exists>y\<^bsub>\<alpha>\<^esub>. \<^bold>S {(x, \<alpha>) \<Zinj> y\<^bsub>\<alpha>\<^esub>} B \<turnstile> A"
    using "\<exists>_Rule" by simp
  then have *: "\<H> \<turnstile> (\<exists>y\<^bsub>\<alpha>\<^esub>. \<^bold>S {(x, \<alpha>) \<Zinj> y\<^bsub>\<alpha>\<^esub>} B) \<supset>\<^sup>\<Q> A" (is \<open>_ \<turnstile> ?F\<close>)
    using Deduction_Theorem and \<open>is_hyps \<H>\<close> by blast
  then have "\<H> \<turnstile> \<exists>x\<^bsub>\<alpha>\<^esub>. B \<supset>\<^sup>\<Q> A"
  proof (cases "x = y")
    case True
    with * show ?thesis
      using identity_singleton_substitution_neutrality by force
  next
    case False
    from assms(4) have "(y, \<alpha>) \<notin> free_vars (\<exists>x\<^bsub>\<alpha>\<^esub>. B)"
      using free_vars_in_all_vars by auto
    have "\<sim>\<^sup>\<Q> \<^bold>S {(x, \<alpha>) \<Zinj> y\<^bsub>\<alpha>\<^esub>} B \<in> wffs\<^bsub>o\<^esub>"
      by
        (
          fact hyp_derivable_form_is_wffso
          [OF *, THEN wffs_from_imp_op(1), THEN wffs_from_exists, THEN neg_wff]
        )
    moreover from False have "(x, \<alpha>) \<notin> free_vars (\<sim>\<^sup>\<Q> \<^bold>S {(x, \<alpha>) \<Zinj> y\<^bsub>\<alpha>\<^esub>} B)"
      using free_var_in_renaming_substitution by simp
    moreover have "is_free_for (x\<^bsub>\<alpha>\<^esub>) (y, \<alpha>) (\<sim>\<^sup>\<Q> \<^bold>S {(x, \<alpha>) \<Zinj> y\<^bsub>\<alpha>\<^esub>} B)"
      by (intro is_free_for_in_neg prop_5245_aux[OF False \<open>(y, \<alpha>) \<notin> free_vars (\<exists>x\<^bsub>\<alpha>\<^esub>. B)\<close> assms(3)])
    moreover from assms(3,4) have "\<^bold>S {(y, \<alpha>) \<Zinj> x\<^bsub>\<alpha>\<^esub>} \<^bold>S {(x, \<alpha>) \<Zinj> y\<^bsub>\<alpha>\<^esub>} B = B"
      using identity_singleton_substitution_neutrality and renaming_substitution_composability
      by force
    ultimately have "\<turnstile> (\<lambda>y\<^bsub>\<alpha>\<^esub>. \<sim>\<^sup>\<Q> \<^bold>S {(x, \<alpha>) \<Zinj> y\<^bsub>\<alpha>\<^esub>} B) =\<^bsub>\<alpha>\<rightarrow>o\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<sim>\<^sup>\<Q> B)"
      using "\<alpha>"[where A = "\<sim>\<^sup>\<Q> \<^bold>S {(x, \<alpha>) \<Zinj> y\<^bsub>\<alpha>\<^esub>} B"] by (metis derived_substitution_simps(4))
    then show ?thesis
      by (rule rule_RR[OF disjI1, where p = "[\<guillemotleft>,\<guillemotright>,\<guillemotright>,\<guillemotright>]" and C = "?F"]) (use * in force)+
  qed
  with assms(1) show ?thesis
    by (rule MP)
qed

lemmas Rule_C = prop_5245 (* synonym *)

end
