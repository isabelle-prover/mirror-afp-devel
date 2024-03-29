(*  Author:     Ata Keskin, TU München 
*)

section \<open>Stopping Times and Hitting Times\<close>

text \<open>In this section we formalize stopping times and hitting times. A stopping time is a random variable that represents the time at which a certain event occurs within a stochastic process. 
      A hitting time, also known as first passage time or first hitting time, is a specific type of stopping time that represents the first time a stochastic process reaches a particular state or crosses a certain threshold.\<close>

theory Stopping_Time
imports Martingales_Updates
begin                      

subsection \<open>Stopping Time\<close>

text \<open>The formalization of stopping times here is simply a rewrite of the document \<open>HOL-Probability.Stopping_Time\<close> \<^cite>\<open>"hoelzl2011measuretheory"\<close>.
      We have adapted the document to use the locales defined in our formalization of filtered measure spaces \<^cite>\<open>keskin2023formalization\<close> \<^cite>\<open>"Martingales-AFP"\<close>.
      This way we can omit the partial formalization of filtrations in the original document. Furthermore, we can include the initial time index \<^term>\<open>t\<^sub>0\<close> that we introduced as well.\<close>

context linearly_filtered_measure
begin

\<comment> \<open>A stopping time is a measurable function from the measure space (possible events) into the time axis.\<close>

definition stopping_time :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "stopping_time T = ((T \<in> space M \<rightarrow> {t\<^sub>0..}) \<and> (\<forall>t\<ge>t\<^sub>0. Measurable.pred (F t) (\<lambda>x. T x \<le> t)))"

lemma stopping_time_cong: 
  assumes "\<And>t x. t \<ge> t\<^sub>0 \<Longrightarrow> x \<in> space (F t) \<Longrightarrow> T x = S x"
  shows "stopping_time T = stopping_time S"
proof (cases "T \<in> space M \<rightarrow> {t\<^sub>0..}")
  case True
  hence "S \<in> space M \<rightarrow> {t\<^sub>0..}" using assms space_F by force
  then show ?thesis unfolding stopping_time_def 
    using assms arg_cong[where f="(\<lambda>P. \<forall>t\<ge>t\<^sub>0. P t)"] measurable_cong[where M="F _" and f="\<lambda>x. T x \<le> _" and g="\<lambda>x. S x \<le> _"] True by metis
next
  case False
  hence "S \<notin> space M \<rightarrow> {t\<^sub>0..}" using assms space_F by force
  then show ?thesis unfolding stopping_time_def using False by blast
qed

lemma stopping_time_ge_zero:
  assumes "stopping_time T" "\<omega> \<in> space M"
  shows "T \<omega> \<ge> t\<^sub>0"
  using assms unfolding stopping_time_def by auto

lemma stopping_timeD: 
  assumes "stopping_time T" "t \<ge> t\<^sub>0"
  shows "Measurable.pred (F t) (\<lambda>x. T x \<le> t)"
  using assms unfolding stopping_time_def by simp

lemma stopping_timeI[intro?]: 
  assumes "\<And>x. x \<in> space M \<Longrightarrow> T x \<ge> t\<^sub>0"
          "(\<And>t. t \<ge> t\<^sub>0 \<Longrightarrow> Measurable.pred (F t) (\<lambda>x. T x \<le> t))"
  shows "stopping_time T"
  using assms by (auto simp: stopping_time_def)

lemma stopping_time_measurable:
  assumes "stopping_time T"
  shows "T \<in> borel_measurable M"
proof (rule borel_measurableI_le)
  {
    fix t assume "\<not> t \<ge> t\<^sub>0"
    hence "{x \<in> space M. T x \<le> t} = {}" using assms dual_order.trans[of _ t "t\<^sub>0"] unfolding stopping_time_def by fastforce
    hence "{x \<in> space M. T x \<le> t} \<in> sets M" by (metis sets.empty_sets)
  }
  moreover
  {
    fix t assume asm: "t \<ge> t\<^sub>0"
    hence "{x \<in> space M. T x \<le> t} \<in> sets M" using stopping_timeD[OF assms asm] sets_F_subset unfolding Measurable.pred_def space_F[OF asm] by blast
  }
  ultimately show "{x \<in> space M. T x \<le> t} \<in> sets M" for t by blast
qed

lemma stopping_time_const: 
  assumes "t \<ge> t\<^sub>0"
  shows "stopping_time (\<lambda>x. t)" using assms by (auto simp: stopping_time_def)

lemma stopping_time_min:
  assumes "stopping_time T" "stopping_time S"
  shows "stopping_time (\<lambda>x. min (T x) (S x))"
  using assms by (auto simp: stopping_time_def min_le_iff_disj intro!: pred_intros_logic)

lemma stopping_time_max:
  assumes "stopping_time T" "stopping_time S"
  shows "stopping_time (\<lambda>x. max (T x) (S x))"
  using assms by (auto simp: stopping_time_def intro!: pred_intros_logic max.coboundedI1) 

subsection \<open>\<open>\<sigma>\<close>-algebra of a Stopping Time\<close>

text \<open>Moving on, we define the \<open>\<sigma>\<close>-algebra associated with a stopping time \<^term>\<open>T\<close>.
      It contains all the information up to time \<^term>\<open>T\<close>, the same way \<^term>\<open>F t\<close> contains all the information up to time \<^term>\<open>t\<close>.\<close>

definition pre_sigma :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a measure" where
  "pre_sigma T = sigma (space M) {A \<in> sets M. \<forall>t\<ge>t\<^sub>0. {\<omega> \<in> A. T \<omega> \<le> t} \<in> sets (F t)}"

lemma measure_pre_sigma[simp]: "emeasure (pre_sigma T) = (\<lambda>_. 0)" by (simp add: pre_sigma_def emeasure_sigma)

lemma sigma_algebra_pre_sigma:
  assumes "stopping_time T"
  shows "sigma_algebra (space M) {A \<in> sets M. \<forall>t\<ge>t\<^sub>0. {\<omega>\<in>A. T \<omega> \<le> t} \<in> sets (F t)}"
proof -
  let ?\<Sigma> = "{A \<in> sets M. \<forall>t\<ge>t\<^sub>0. {\<omega>\<in>A. T \<omega> \<le> t} \<in> sets (F t)}"
  {
    fix A assume asm: "A \<in> ?\<Sigma>"
    {
      fix t assume asm': "t \<ge> t\<^sub>0"
      hence "{\<omega>\<in>A. T \<omega> \<le> t} \<in> sets (F t)" using asm by blast
      then have "{\<omega> \<in> space (F t). T \<omega> \<le> t} - {\<omega> \<in> A. T \<omega> \<le> t} \<in> sets (F t)" using assms[THEN stopping_timeD, OF asm'] by auto
      also have "{\<omega> \<in> space (F t). T \<omega> \<le> t} - {\<omega> \<in> A. T \<omega> \<le> t} = {\<omega> \<in> space M - A. T \<omega> \<le> t}" using space_F[OF asm'] by blast
      finally have "{\<omega> \<in> (space M) - A. T \<omega> \<le> t} \<in> sets (F t)" .
    }
    hence "space M - A \<in> ?\<Sigma>" using asm by blast
  }
  moreover 
  {
    fix A :: "nat \<Rightarrow> 'a set" assume asm: "range A \<subseteq> ?\<Sigma>"
    {
      fix t assume "t \<ge> t\<^sub>0"
      then have "(\<Union>i. {\<omega> \<in> A i. T \<omega> \<le> t}) \<in> sets (F t)" using asm by auto
      also have "(\<Union>i. {\<omega> \<in> A i. T \<omega> \<le> t}) = {\<omega> \<in> \<Union>(A ` UNIV). T \<omega> \<le> t}" by auto
      finally have "{\<omega> \<in> \<Union>(range A). T \<omega> \<le> t} \<in> sets (F t)" .
    }
    hence "\<Union>(range A) \<in> ?\<Sigma>" using asm by blast
  }
  ultimately show ?thesis unfolding sigma_algebra_iff2 by (auto intro!: sets.sets_into_space[THEN PowI, THEN subsetI])
qed

lemma space_pre_sigma[simp]: "space (pre_sigma T) = space M" unfolding pre_sigma_def by (intro space_measure_of_conv)

lemma sets_pre_sigma: 
  assumes "stopping_time T"
  shows "sets (pre_sigma T) = {A \<in> sets M. \<forall>t\<ge>t\<^sub>0. {\<omega>\<in>A. T \<omega> \<le> t} \<in> F t}"
  unfolding pre_sigma_def using sigma_algebra.sets_measure_of_eq[OF sigma_algebra_pre_sigma, OF assms] by blast

lemma sets_pre_sigmaI: 
  assumes "stopping_time T"
      and "\<And>t. t \<ge> t\<^sub>0 \<Longrightarrow> {\<omega> \<in> A. T \<omega> \<le> t} \<in> F t"
    shows "A \<in> pre_sigma T"
proof (cases "\<exists>t\<ge>t\<^sub>0. \<forall>t'. t' \<le> t")
  case True
  then obtain t where "t \<ge> t\<^sub>0" "{\<omega> \<in> A. T \<omega> \<le> t} = A" by blast
  hence "A \<in> M" using assms(2)[of t] sets_F_subset[of t] by fastforce
  thus ?thesis using assms(2) unfolding sets_pre_sigma[OF assms(1)] by blast
next
  case False
  hence *: "{t<..} \<noteq> {}" if "t \<ge> t\<^sub>0" for t by (metis not_le empty_iff greaterThan_iff)
  obtain D :: "'b set" where D: "countable D" "\<And>X. open X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> D \<inter> X \<noteq> {}" by (metis countable_dense_setE disjoint_iff)
  have **: "D \<inter> {t<..} \<noteq> {}" if "t \<ge> t\<^sub>0" for t using * that by (intro D(2)) auto
  {
    fix \<omega>
    obtain t where t: "t \<ge> t\<^sub>0" "T \<omega> \<le> t" using linorder_linear by auto
    moreover obtain t' where "t' \<in> D \<inter> {t<..} \<inter> {t\<^sub>0..}" using ** t by fastforce
    moreover have "T \<omega> \<le> t'" using calculation by fastforce
    ultimately have "\<exists>t. \<exists>t' \<in> D \<inter> {t<..} \<inter> {t\<^sub>0..}. T \<omega> \<le> t'" by blast
  }
  hence "(\<Union>t'\<in>(\<Union>t. D \<inter> {t<..} \<inter> {t\<^sub>0..}). {\<omega> \<in> A. T \<omega> \<le> t'}) = A" by fast
  moreover have "(\<Union>t'\<in>(\<Union>t. D \<inter> {t<..} \<inter> {t\<^sub>0..}). {\<omega> \<in> A. T \<omega> \<le> t'}) \<in> M" using D assms(2) sets_F_subset by (intro sets.countable_UN'', fastforce, fast) 
  ultimately have "A \<in> M" by argo
  thus ?thesis using assms(2) unfolding sets_pre_sigma[OF assms(1)] by blast
qed

lemma pred_pre_sigmaI:
  assumes "stopping_time T"
  shows "(\<And>t. t \<ge> t\<^sub>0 \<Longrightarrow> Measurable.pred (F t) (\<lambda>\<omega>. P \<omega> \<and> T \<omega> \<le> t)) \<Longrightarrow> Measurable.pred (pre_sigma T) P"
  unfolding pred_def space_pre_sigma using assms by (auto intro: sets_pre_sigmaI[OF assms(1)])

lemma sets_pre_sigmaD: 
  assumes "stopping_time T" "A \<in> pre_sigma T" "t \<ge> t\<^sub>0" 
  shows "{\<omega> \<in> A. T \<omega> \<le> t} \<in> sets (F t)"
  using assms sets_pre_sigma by auto

lemma borel_measurable_stopping_time_pre_sigma:
  assumes "stopping_time T" 
  shows "T \<in> borel_measurable (pre_sigma T)"
proof (intro borel_measurableI_le sets_pre_sigmaI[OF assms])
  fix t t' assume asm: "t \<ge> t\<^sub>0"
  {
    assume "\<not> t' \<ge> t\<^sub>0"
    hence "{\<omega> \<in> {x \<in> space (pre_sigma T). T x \<le> t'}. T \<omega> \<le> t} = {}" using assms dual_order.trans[of _ t' "t\<^sub>0"] unfolding stopping_time_def by fastforce
    hence "{\<omega> \<in> {x \<in> space (pre_sigma T). T x \<le> t'}. T \<omega> \<le> t} \<in> sets (F t)" by (metis sets.empty_sets)
  }
  moreover
  {
    assume asm': "t' \<ge> t\<^sub>0"
    have "{\<omega> \<in> space (F (min t' t)). T \<omega> \<le> min t' t} \<in> sets (F (min t' t))"
      using assms asm asm' unfolding pred_def[symmetric] by (intro stopping_timeD) auto
    also have "\<dots> \<subseteq> sets (F t)"
      using assms asm asm' by (intro sets_F_mono) auto
    finally have "{\<omega> \<in> {x \<in> space (pre_sigma T). T x \<le> t'}. T \<omega> \<le> t} \<in> sets (F t)"
      using asm asm' by simp
  }
  ultimately show "{\<omega> \<in> {x \<in> space (pre_sigma T). T x \<le> t'}. T \<omega> \<le> t} \<in> sets (F t)" by blast
qed

lemma mono_pre_sigma:
  assumes "stopping_time T" "stopping_time S"
      and "\<And>x. x \<in> space M \<Longrightarrow> T x \<le> S x"
    shows "pre_sigma T \<subseteq> pre_sigma S"
proof
  fix A assume "A \<in> pre_sigma T"
  hence asm: "A \<in> sets M" "t \<ge> t\<^sub>0 \<Longrightarrow> {\<omega> \<in> A. T \<omega> \<le> t} \<in> sets (F t)" for t using assms sets_pre_sigma by blast+
  {
    fix t assume asm': "t \<ge> t\<^sub>0"
    then have "A \<subseteq> space M" using sets.sets_into_space asm by blast
    have "{\<omega>\<in>A. T \<omega> \<le> t} \<inter> {\<omega>\<in>space (F t). S \<omega> \<le> t} \<in> sets (F t)"
      using asm asm' stopping_timeD[OF assms(2)] by (auto simp: pred_def)
    also have "{\<omega>\<in>A. T \<omega> \<le> t} \<inter> {\<omega>\<in>space (F t). S \<omega> \<le> t} = {\<omega>\<in>A. S \<omega> \<le> t}"
      using sets.sets_into_space[OF asm(1)] assms(3) order_trans asm' by fastforce
    finally have "{\<omega>\<in>A. S \<omega> \<le> t} \<in> sets (F t)" by simp
  }
  thus "A \<in> pre_sigma S" by (intro sets_pre_sigmaI assms asm) blast
qed

lemma stopping_time_measurable_le: 
  assumes "stopping_time T" "s \<ge> t\<^sub>0" "t \<ge> s" 
  shows "Measurable.pred (F t) (\<lambda>\<omega>. T \<omega> \<le> s)"
  using assms stopping_timeD[of T] sets_F_mono[of _ t] by (auto simp: pred_def)

lemma stopping_time_measurable_less:
  assumes "stopping_time T" "s \<ge> t\<^sub>0" "t \<ge> s"
  shows "Measurable.pred (F t) (\<lambda>\<omega>. T \<omega> < s)"
proof -
  have "Measurable.pred (F t) (\<lambda>\<omega>. T \<omega> < t)" if asm: "stopping_time T" "t \<ge> t\<^sub>0" for T t
  proof - 
    obtain D :: "'b set" where D: "countable D" "\<And>X. open X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> D \<inter> X \<noteq> {}" by (metis countable_dense_setE disjoint_iff)
    show ?thesis
    proof cases
      assume *: "\<forall>t'\<in>{t\<^sub>0..<t}. {t'<..<t} \<noteq> {}"
      hence **: "D \<inter> {t'<..< t} \<noteq> {}" if "t' \<in> {t\<^sub>0..<t}" for t' using that by (intro D(2)) fastforce+
  
      show ?thesis
      proof (rule measurable_cong[THEN iffD2])
        show "T \<omega> < t \<longleftrightarrow> (\<exists>r\<in>D \<inter> {t\<^sub>0..<t}. T \<omega> \<le> r)" if "\<omega> \<in> space (F t)" for \<omega> 
          using **[of "T \<omega>"] that less_imp_le stopping_time_ge_zero asm by fastforce
        show "Measurable.pred (F t) (\<lambda>w. \<exists>r\<in>D \<inter> {t\<^sub>0..<t}. T w \<le> r)"
          using stopping_time_measurable_le asm D by (intro measurable_pred_countable) auto
      qed
    next
      assume "\<not> (\<forall>t'\<in>{t\<^sub>0..<t}. {t'<..<t} \<noteq> {})"
      then obtain t' where t': "t' \<in> {t\<^sub>0..<t}" "{t'<..<t} = {}" by blast
      show ?thesis
      proof (rule measurable_cong[THEN iffD2])
        show "T \<omega> < t \<longleftrightarrow> T \<omega> \<le> t'" for \<omega> using t' by (metis atLeastLessThan_iff emptyE greaterThanLessThan_iff linorder_not_less order.strict_trans1)
        show "Measurable.pred (F t) (\<lambda>w. T w \<le> t')" using t' by (intro stopping_time_measurable_le[OF asm(1)]) auto
      qed
    qed
  qed
  thus ?thesis
  using assms sets_F_mono[of _ t] by (auto simp add: pred_def)
qed

lemma stopping_time_measurable_ge:
  assumes "stopping_time T" "s \<ge> t\<^sub>0" "t \<ge> s"
  shows "Measurable.pred (F t) (\<lambda>\<omega>. T \<omega> \<ge> s)"
  by (auto simp: not_less[symmetric] intro: stopping_time_measurable_less[OF assms] Measurable.pred_intros_logic)

lemma stopping_time_measurable_gr: 
  assumes "stopping_time T" "s \<ge> t\<^sub>0" "t \<ge> s"
  shows "Measurable.pred (F t) (\<lambda>x. s < T x)"
  by (auto simp add: not_le[symmetric] intro: stopping_time_measurable_le[OF assms] Measurable.pred_intros_logic)

lemma stopping_time_measurable_eq:
  assumes "stopping_time T" "s \<ge> t\<^sub>0" "t \<ge> s"
  shows "Measurable.pred (F t) (\<lambda>\<omega>. T \<omega> = s)"
  unfolding eq_iff using stopping_time_measurable_le[OF assms] stopping_time_measurable_ge[OF assms]
  by (intro pred_intros_logic)

lemma stopping_time_less_stopping_time:
  assumes "stopping_time T" "stopping_time S"
  shows "Measurable.pred (pre_sigma T) (\<lambda>\<omega>. T \<omega> < S \<omega>)"
proof (rule pred_pre_sigmaI)
  fix t assume asm: "t \<ge> t\<^sub>0"
  obtain D :: "'b set" where D: "countable D" and semidense_D: "\<And>x y. x < y \<Longrightarrow> (\<exists>b\<in>D. x \<le> b \<and> b < y)"
    using countable_separating_set_linorder2 by auto
  show "Measurable.pred (F t) (\<lambda>\<omega>. T \<omega> < S \<omega> \<and> T \<omega> \<le> t)"
  proof (rule measurable_cong[THEN iffD2])
    let ?f = "\<lambda>\<omega>. if T \<omega> = t then \<not> S \<omega> \<le> t else \<exists>s\<in>D \<inter> {t\<^sub>0..t}. T \<omega> \<le> s \<and> \<not> (S \<omega> \<le> s)"
    { 
      fix \<omega> assume "\<omega> \<in> space (F t)" "T \<omega> \<le> t" "T \<omega> \<noteq> t" "T \<omega> < S \<omega>"
      hence "t\<^sub>0 \<le> T \<omega>" "T \<omega> < min t (S \<omega>)" using asm stopping_time_ge_zero[OF assms(1)] by auto
      then obtain r where "r \<in> D" "t\<^sub>0 \<le> r" "T \<omega> \<le> r" "r < min t (S \<omega>)" using semidense_D order_trans by blast
      hence "\<exists>s\<in>D \<inter> {t\<^sub>0..t}. T \<omega> \<le> s \<and> s < S \<omega>" by auto 
    }
    thus "(T \<omega> < S \<omega> \<and> T \<omega> \<le> t) = ?f \<omega>" if "\<omega> \<in> space (F t)" for \<omega> using that by force
    show "Measurable.pred (F t) ?f"
      using assms asm D
      by (intro pred_intros_logic measurable_If measurable_pred_countable countable_Collect
                stopping_time_measurable_le predE stopping_time_measurable_eq) auto
  qed
qed (intro assms)

end  

lemma (in enat_filtered_measure) stopping_time_SUP_enat:
  fixes T :: "nat \<Rightarrow> ('a \<Rightarrow> enat)"
  shows "(\<And>i. stopping_time (T i)) \<Longrightarrow> stopping_time (SUP i. T i)"
  unfolding stopping_time_def SUP_apply SUP_le_iff by (auto intro!: pred_intros_countable)

lemma (in enat_filtered_measure) stopping_time_Inf_enat:
  assumes "\<And>i. Measurable.pred (F i) (P i)"
  shows "stopping_time (\<lambda>\<omega>. Inf {i. P i \<omega>})"
proof -
  {
    fix t :: enat assume asm: "t \<noteq> \<infinity>"
    moreover
    { 
      fix i \<omega> assume "Inf {i. P i \<omega>} \<le> t"
      moreover have "a < eSuc b \<longleftrightarrow> (a \<le> b \<and> a \<noteq> \<infinity>)" for a b by (cases a) auto
      ultimately have "(\<exists>i\<le>t. P i \<omega>)" using asm unfolding Inf_le_iff by (cases t) (auto elim!: allE[of _ "eSuc t"])
    }
    ultimately have *: "\<And>\<omega>. Inf {i. P i \<omega>} \<le> t \<longleftrightarrow> (\<exists>i\<in>{..t}. P i \<omega>)" by (auto intro!: Inf_lower2)
    have "Measurable.pred (F t) (\<lambda>\<omega>. Inf {i. P i \<omega>} \<le> t)" unfolding * using sets_F_mono assms by (intro pred_intros_countable_bounded) (auto simp: pred_def)
  }
  moreover have "Measurable.pred (F t) (\<lambda>\<omega>. Inf {i. P i \<omega>} \<le> t)" if "t = \<infinity>" for t using that by simp
  ultimately show ?thesis by (blast intro: stopping_timeI[OF i0_lb])
qed

lemma (in nat_filtered_measure) stopping_time_Inf_nat:
  assumes "\<And>i. Measurable.pred (F i) (P i)" 
          "\<And>i \<omega>. \<omega> \<in> space M \<Longrightarrow> \<exists>n. P n \<omega>"
  shows "stopping_time (\<lambda>\<omega>. Inf {i. P i \<omega>})"
proof (rule stopping_time_cong[THEN iffD2])
  show "stopping_time (\<lambda>x. LEAST n. P n x)"
  proof
    fix t
    have "((LEAST n. P n \<omega>) \<le> t) = (\<exists>i\<le>t. P i \<omega>)" if "\<omega> \<in> space M" for \<omega> by (rule LeastI2_wellorder_ex[OF assms(2)[OF that]]) auto
    moreover have "Measurable.pred (F t) (\<lambda>w. \<exists>i\<in>{..t}. P i w)" using sets_F_mono[of _ t] assms by (intro pred_intros_countable_bounded) (auto simp: pred_def)
    ultimately show "Measurable.pred (F t) (\<lambda>\<omega>. (LEAST n. P n \<omega>) \<le> t)" by (subst measurable_cong[of "F t"]) auto
  qed (simp)
qed (simp add: Inf_nat_def)

definition stopped_value :: "('b \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c)" where
  "stopped_value X \<tau> \<omega> = X (\<tau> \<omega>) \<omega>"

subsection \<open>Hitting Time\<close>

text \<open>Given a stochastic process \<open>X\<close> and a borel set \<open>A\<close>, \<open>hitting_time X A s t\<close> is the first time \<open>X\<close> is in \<open>A\<close> after time \<open>s\<close> and before time \<open>t\<close>.
      If \<open>X\<close> does not hit \<open>A\<close> after time \<open>s\<close> and before \<open>t\<close> then the hitting time is simply \<open>t\<close>. The definition presented here coincides with the definition of hitting times in mathlib \<^cite>\<open>"ying2022formalization"\<close>.\<close>

context linearly_filtered_measure
begin

definition hitting_time :: "('b \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> 'c set \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "hitting_time X A s t = (\<lambda>\<omega>. if \<exists>i\<in>{s..t} \<inter> {t\<^sub>0..}. X i \<omega> \<in> A then Inf ({s..t} \<inter> {t\<^sub>0..} \<inter> {i. X i \<omega> \<in> A}) else max t\<^sub>0 t)"

lemma hitting_time_def':
  "hitting_time X A s t = (\<lambda>\<omega>. Inf (insert (max t\<^sub>0 t) ({s..t} \<inter> {t\<^sub>0..} \<inter> {i. X i \<omega> \<in> A})))"
proof cases
  assume asm: "t\<^sub>0 \<le> s \<and> s \<le> t"
  hence "{s..t} \<inter> {t\<^sub>0..} = {s..t}" by simp
  {
    fix \<omega>
    assume *: "{s..t} \<inter> {t\<^sub>0..} \<inter> {i. X i \<omega> \<in> A} \<noteq> {}"
    then obtain i where "i \<in> {s..t} \<inter> {t\<^sub>0..} \<inter> {i. X i \<omega> \<in> A}" by blast
    hence "Inf ({s..t} \<inter> {t\<^sub>0..} \<inter> {i. X i \<omega> \<in> A}) \<le> t" by (intro cInf_lower[of i, THEN order_trans]) auto
    hence "Inf (insert (max t\<^sub>0 t) ({s..t} \<inter> {t\<^sub>0..} \<inter> {i. X i \<omega> \<in> A})) = Inf ({s..t} \<inter> {t\<^sub>0..} \<inter> {i. X i \<omega> \<in> A})" using asm * inf_absorb2 by (subst cInf_insert_If) force+ 
    also have "... = hitting_time X A s t \<omega>" using * unfolding hitting_time_def by auto
    finally have "hitting_time X A s t \<omega> = Inf (insert (max t\<^sub>0 t) ({s..t} \<inter> {t\<^sub>0..} \<inter> {i. X i \<omega> \<in> A}))" by argo
  }
  moreover
  {
    fix \<omega>
    assume "{s..t} \<inter> {t\<^sub>0..} \<inter> {i. X i \<omega> \<in> A} = {}"
    hence "hitting_time X A s t \<omega> = Inf (insert (max t\<^sub>0 t) ({s..t} \<inter> {t\<^sub>0..} \<inter> {i. X i \<omega> \<in> A}))" unfolding hitting_time_def by auto
  }
  ultimately show ?thesis by fast
next
  assume "\<not> (t\<^sub>0 \<le> s \<and> s \<le> t)"
  moreover
  {
    assume asm: "s < t\<^sub>0" "t \<ge> t\<^sub>0"
    hence "{s..t} \<inter> {t\<^sub>0..} = {t\<^sub>0..t}" by simp
    {
      fix \<omega>
      assume *: "{s..t} \<inter> {t\<^sub>0..} \<inter> {i. X i \<omega> \<in> A} \<noteq> {}"
      then obtain i where "i \<in> {s..t} \<inter> {t\<^sub>0..} \<inter> {i. X i \<omega> \<in> A}" by blast
      hence "Inf ({s..t} \<inter> {t\<^sub>0..} \<inter> {i. X i \<omega> \<in> A}) \<le> t" by (intro cInf_lower[of i, THEN order_trans]) auto
      hence "Inf (insert (max t\<^sub>0 t) ({s..t} \<inter> {t\<^sub>0..} \<inter> {i. X i \<omega> \<in> A})) = Inf ({s..t} \<inter> {t\<^sub>0..} \<inter> {i. X i \<omega> \<in> A})" using asm * inf_absorb2 by (subst cInf_insert_If) force+ 
      also have "... = hitting_time X A s t \<omega>" using * unfolding hitting_time_def by auto
      finally have "hitting_time X A s t \<omega> = Inf (insert (max t\<^sub>0 t) ({s..t} \<inter> {t\<^sub>0..} \<inter> {i. X i \<omega> \<in> A}))" by argo
    }
    moreover
    {
      fix \<omega>
      assume "{s..t} \<inter> {t\<^sub>0..} \<inter> {i. X i \<omega> \<in> A} = {}"
      hence "hitting_time X A s t \<omega> = Inf (insert (max t\<^sub>0 t) ({s..t} \<inter> {t\<^sub>0..} \<inter> {i. X i \<omega> \<in> A}))" unfolding hitting_time_def by auto
    }
    ultimately have ?thesis by fast  
  }
  moreover have ?thesis if "s < t\<^sub>0" "t < t\<^sub>0" using that unfolding hitting_time_def by auto
  moreover have ?thesis if "s > t" using that unfolding hitting_time_def by auto
  ultimately show ?thesis by fastforce
qed

\<comment> \<open>The following lemma provides a sufficient condition for an injective function to preserve a hitting time.\<close>

lemma hitting_time_inj_on:
  assumes "inj_on f S" "\<And>\<omega> t. t \<ge> t\<^sub>0 \<Longrightarrow> X t \<omega> \<in> S" "A \<subseteq> S"
  shows "hitting_time X A = hitting_time (\<lambda>t \<omega>. f (X t \<omega>)) (f ` A)"
proof -
  have "X t \<omega> \<in> A \<longleftrightarrow> f (X t \<omega>) \<in> f ` A" if "t \<ge> t\<^sub>0" for t \<omega> using assms that inj_on_image_mem_iff by meson
  hence "{t\<^sub>0..} \<inter> {i. X i \<omega> \<in> A} = {t\<^sub>0..} \<inter> {i. f (X i \<omega>) \<in> f ` A}" for \<omega> by blast
  thus ?thesis unfolding hitting_time_def' Int_assoc by presburger
qed

lemma hitting_time_translate: 
  fixes c :: "_ :: ab_group_add"
  shows "hitting_time X A = hitting_time (\<lambda>n \<omega>. X n \<omega> + c) (((+) c) ` A)"
  by (subst hitting_time_inj_on[OF inj_on_add, of _ UNIV]) (simp add: add.commute)+

lemma hitting_time_le: 
  assumes "t \<ge> t\<^sub>0"
  shows "hitting_time X A s t \<omega> \<le> t"
  unfolding hitting_time_def' using assms 
  by (intro cInf_lower[of "max t\<^sub>0 t", THEN order_trans]) auto

lemma hitting_time_ge: 
  assumes "t \<ge> t\<^sub>0" "s \<le> t"
  shows "s \<le> hitting_time X A s t \<omega>"
  unfolding hitting_time_def' using assms 
  by (intro le_cInf_iff[THEN iffD2]) auto

lemma hitting_time_mono:
  assumes "t \<ge> t\<^sub>0" "s \<le> s'" "t \<le> t'"
  shows "hitting_time X A s t \<omega> \<le> hitting_time X A s' t' \<omega>"
  unfolding hitting_time_def' using assms by (fastforce intro!: cInf_mono)
  
end

context nat_filtered_measure
begin               

\<comment> \<open>Hitting times are stopping times for adapted processes.\<close>

lemma stopping_time_hitting_time:
  assumes "adapted_process M F 0 X" "A \<in> borel"
  shows "stopping_time (hitting_time X A s t)"
proof -
  interpret adapted_process M F 0 X by (rule assms)
  have "insert t ({s..t} \<inter> {i. X i \<omega> \<in> A}) = {i. i = t \<or> i \<in> ({s..t} \<inter> {i. X i \<omega> \<in> A})}" for \<omega> by blast
  hence "hitting_time X A s t = (\<lambda>\<omega>. Inf {i. i = t \<or> i \<in> ({s..t} \<inter> {i. X i \<omega> \<in> A})})" unfolding hitting_time_def' by simp
  thus ?thesis using assms by (auto intro: stopping_time_Inf_nat)
qed

lemma stopping_time_hitting_time':
  assumes "adapted_process M F 0 X" "A \<in> borel" "stopping_time s" "\<And>\<omega>. s \<omega> \<le> t"
  shows "stopping_time (\<lambda>\<omega>. hitting_time X A (s \<omega>) t \<omega>)"
proof -
  interpret adapted_process M F 0 X by (rule assms)
  {
    fix n
    have "s \<omega> \<le> hitting_time X A (s \<omega>) t \<omega>" if "s \<omega> > n" for \<omega> using hitting_time_ge[OF _ assms(4)] by simp
    hence "(\<Union>i\<in>{n<..}. {\<omega>. s \<omega> = i} \<inter> {\<omega>. hitting_time X A i t \<omega> \<le> n}) = {}" by fastforce
    hence *: "(\<lambda>\<omega>. hitting_time X A (s \<omega>) t \<omega> \<le> n) = (\<lambda>\<omega>. \<exists>i\<le>n. s \<omega> = i \<and> hitting_time X A i t \<omega> \<le> n)" by force
    
    have "Measurable.pred (F n) (\<lambda>\<omega>. s \<omega> = i \<and> hitting_time X A i t \<omega> \<le> n)" if "i \<le> n" for i
    proof -
      have "Measurable.pred (F i) (\<lambda>\<omega>. s \<omega> = i)" using stopping_time_measurable_eq assms by blast
      hence "Measurable.pred (F n) (\<lambda>\<omega>. s \<omega> = i)" by (meson less_eq_nat.simps measurable_from_subalg subalgebra_F that)
      moreover have "Measurable.pred (F n) (\<lambda>\<omega>. hitting_time X A i t \<omega> \<le> n)" using stopping_timeD[OF stopping_time_hitting_time, OF assms(1,2)] by blast
      ultimately show ?thesis by auto
    qed
    hence "Measurable.pred (F n) (\<lambda>\<omega>. \<exists>i\<le>n. s \<omega> = i \<and> hitting_time X A i t \<omega> \<le> n)" by (intro pred_intros_countable) auto
    hence "Measurable.pred (F n) (\<lambda>\<omega>. hitting_time X A (s \<omega>) t \<omega> \<le> n)" using * by argo
  }
  thus ?thesis by (intro stopping_timeI) auto
qed

\<comment> \<open>If \<^term>\<open>X\<close> hits \<^term>\<open>A\<close> at time \<^term>\<open>j \<in> {s..t}\<close>, then the stopped value of \<^term>\<open>X\<close> at the hitting time of \<^term>\<open>A\<close> in the interval \<^term>\<open>{s..t}\<close> is an element of \<^term>\<open>A\<close>.\<close>

lemma stopped_value_hitting_time_mem:
  assumes "j \<in> {s..t}" "X j \<omega> \<in> A"
  shows "stopped_value X (hitting_time X A s t) \<omega> \<in> A"
proof -
  have "\<exists>i\<in>{s..t} \<inter> {0..}. X i \<omega> \<in> A" using assms by blast
  moreover have "Inf ({s..t} \<inter> {i. X i \<omega> \<in> A}) \<in> {s..t} \<inter> {i. X i \<omega> \<in> A}" using assms by (blast intro!: Inf_nat_def1)
  ultimately show ?thesis unfolding hitting_time_def stopped_value_def by simp
qed

lemma hitting_time_le_iff:
  assumes "i < t"
  shows "hitting_time X A s t \<omega> \<le> i \<longleftrightarrow> (\<exists>j \<in> {s..i}. X j \<omega> \<in> A)" (is "?lhs = ?rhs")
proof 
  assume ?lhs
  moreover have "hitting_time X A s t \<omega> \<in> insert t ({s..t} \<inter> {i. X i \<omega> \<in> A})" by (metis hitting_time_def' Int_atLeastAtMostR2 inf_sup_aci(1) insertI1 max_0L wellorder_InfI)
  ultimately have "hitting_time X A s t \<omega> \<in> {s..i} \<inter> {i. X i \<omega> \<in> A}" using assms by force
  thus ?rhs by blast
next
  assume ?rhs
  then obtain j where j: "j \<in> {s..i}" "X j \<omega> \<in> A" by blast
  hence "hitting_time X A s t \<omega> \<le> j" unfolding hitting_time_def' using assms by (auto intro: cInf_lower)
  thus ?lhs using j by simp
qed

lemma hitting_time_less_iff:
  assumes "i \<le> t"
  shows "hitting_time X A s t \<omega> < i \<longleftrightarrow> (\<exists>j \<in> {s..<i}. X j \<omega> \<in> A)" (is "?lhs = ?rhs")
proof 
  assume ?lhs
  moreover have "hitting_time X A s t \<omega> \<in> insert t ({s..t} \<inter> {i. X i \<omega> \<in> A})" by (metis hitting_time_def' Int_atLeastAtMostR2 inf_sup_aci(1) insertI1 max_0L wellorder_InfI)
  ultimately have "hitting_time X A s t \<omega> \<in> {s..<i} \<inter> {i. X i \<omega> \<in> A}" using assms by force
  thus ?rhs by blast
next
  assume ?rhs
  then obtain j where j: "j \<in> {s..<i}" "X j \<omega> \<in> A" by blast
  hence "hitting_time X A s t \<omega> \<le> j" unfolding hitting_time_def' using assms by (auto intro: cInf_lower)
  thus ?lhs using j by simp
qed

\<comment> \<open>If \<^term>\<open>X\<close> already hits \<^term>\<open>A\<close> in the interval \<^term>\<open>{s..t}\<close>, then \<^term>\<open>hitting_time X A s t = hitting_time X A s t'\<close> for \<^term>\<open>t' \<ge> t\<close>.\<close>

lemma hitting_time_eq_hitting_time:
  assumes "t \<le> t'" "j \<in> {s..t}" "X j \<omega> \<in> A"
  shows "hitting_time X A s t \<omega> = hitting_time X A s t' \<omega>" (is "?lhs = ?rhs")
proof -
  have "hitting_time X A s t \<omega> \<in> {s..t'}" using hitting_time_le[THEN order_trans, of t t' X A s] hitting_time_ge[of t s X A] assms by auto
  moreover have "stopped_value X (hitting_time X A s t) \<omega> \<in> A" by (blast intro: stopped_value_hitting_time_mem assms)
  ultimately have "hitting_time X A s t' \<omega> \<le> hitting_time X A s t \<omega>" by (fastforce simp add: hitting_time_def'[where t=t'] stopped_value_def intro!: cInf_lower)
  thus ?thesis by (blast intro: le_antisym hitting_time_mono[OF _ order_refl assms(1)])
qed

end

end