(*  Title:   Disintegration.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

section \<open> Disintegration Theorem \<close>

theory Disintegration
  imports "S_Finite_Measure_Monad.Kernels"
          "Lemmas_Disintegration"
begin

subsection \<open> Definition 14.D.2. (Mixture and Disintegration) \<close>
context measure_kernel
begin

definition mixture_of :: "[('a \<times>'b) measure, 'a measure] \<Rightarrow> bool" where
"mixture_of \<nu> \<mu> \<longleftrightarrow> sets \<nu> = sets (X \<Otimes>\<^sub>M Y) \<and> sets \<mu> = sets X \<and> (\<forall>C\<in>sets (X \<Otimes>\<^sub>M Y). \<nu> C = (\<integral>\<^sup>+x. \<integral>\<^sup>+y. indicator C (x,y) \<partial>(\<kappa> x) \<partial>\<mu>))"

definition disintegration :: "[('a \<times>'b) measure, 'a measure] \<Rightarrow> bool" where
"disintegration \<nu> \<mu> \<longleftrightarrow> sets \<nu> = sets (X \<Otimes>\<^sub>M Y) \<and> sets \<mu> = sets X \<and> (\<forall>A\<in>sets X. \<forall>B\<in>sets Y. \<nu> (A \<times> B) = (\<integral>\<^sup>+x\<in>A. (\<kappa> x B) \<partial>\<mu>))"

lemma disintegrationI:
  assumes "sets \<nu> = sets (X \<Otimes>\<^sub>M Y)" "sets \<mu> = sets X"
      and "\<And>A B. A \<in> sets X \<Longrightarrow> B \<in> sets Y \<Longrightarrow> \<nu> (A \<times> B) = (\<integral>\<^sup>+x\<in>A. (\<kappa> x B) \<partial>\<mu>)"
    shows "disintegration \<nu> \<mu>"
  by(simp add: disintegration_def assms)

lemma mixture_of_disintegration:
  assumes "mixture_of \<nu> \<mu>"
  shows "disintegration \<nu> \<mu>"
  unfolding disintegration_def
proof safe
  fix A B
  assume [simp]:"A \<in> sets X" "B \<in> sets Y"
  have [simp,measurable_cong]: "sets \<mu> = sets X" "space \<mu> = space X"
    using assms by(auto simp: mixture_of_def intro!: sets_eq_imp_space_eq)
  have "A \<times> B \<in> sets (X \<Otimes>\<^sub>M Y)" by simp
  with assms have "\<nu> (A \<times> B) = (\<integral>\<^sup>+x. \<integral>\<^sup>+y. indicator (A \<times> B) (x,y) \<partial>(\<kappa> x) \<partial>\<mu>)"
    by(simp add: mixture_of_def)
  also have "... = (\<integral>\<^sup>+x. \<integral>\<^sup>+y. indicator A x * indicator B y \<partial>(\<kappa> x) \<partial>\<mu>)"
    by(simp add: indicator_times)
  also have "... =  (\<integral>\<^sup>+x\<in>A. (\<kappa> x B) \<partial>\<mu>)"
    by(auto intro!: nn_integral_cong simp: kernel_sets nn_integral_cmult_indicator mult.commute)
  finally show "emeasure \<nu> (A \<times> B) = \<integral>\<^sup>+x\<in>A. emeasure (\<kappa> x) B\<partial>\<mu>" .
qed(use assms[simplified mixture_of_def] in auto)

lemma
  shows mixture_of_sets_eq: "mixture_of \<nu> \<mu> \<Longrightarrow> sets \<nu> = sets (X \<Otimes>\<^sub>M Y)" "mixture_of \<nu> \<mu> \<Longrightarrow> sets \<mu> = sets X"
    and mixture_of_space_eq: "mixture_of \<nu> \<mu> \<Longrightarrow> space \<nu> = space (X \<Otimes>\<^sub>M Y)" "mixture_of \<nu> \<mu> \<Longrightarrow> space \<mu> = space X"
    and disintegration_sets_eq: "disintegration \<nu> \<mu> \<Longrightarrow> sets \<nu> = sets (X \<Otimes>\<^sub>M Y)" "disintegration \<nu> \<mu> \<Longrightarrow> sets \<mu> = sets X"
    and disintegration_space_eq: "disintegration \<nu> \<mu> \<Longrightarrow> space \<nu> = space (X \<Otimes>\<^sub>M Y)" "disintegration \<nu> \<mu> \<Longrightarrow> space \<mu> = space X"
  by(auto simp: mixture_of_def disintegration_def intro!: sets_eq_imp_space_eq)

lemma
  shows mixture_ofD: "mixture_of \<nu> \<mu> \<Longrightarrow> C \<in> sets (X \<Otimes>\<^sub>M Y) \<Longrightarrow> \<nu> C = (\<integral>\<^sup>+x. \<integral>\<^sup>+y. indicator C (x,y) \<partial>(\<kappa> x) \<partial>\<mu>)"
    and disintegrationD: "disintegration \<nu> \<mu> \<Longrightarrow> A \<in> sets X \<Longrightarrow> B \<in> sets Y \<Longrightarrow> \<nu> (A \<times> B) = (\<integral>\<^sup>+x\<in>A. (\<kappa> x B) \<partial>\<mu>)"
  by(auto simp: mixture_of_def disintegration_def)

lemma disintegration_restrict_space:
  assumes "disintegration \<nu> \<mu>" "A \<inter> space X \<in> sets X"
  shows "measure_kernel.disintegration (restrict_space X A) Y \<kappa> (restrict_space \<nu> (A \<times> space Y)) (restrict_space \<mu> A)"
proof(rule measure_kernel.disintegrationI[OF restrict_measure_kernel[of A]])
  have "sets (restrict_space \<nu> (A \<times> space Y)) = sets (restrict_space (X \<Otimes>\<^sub>M Y) (A \<times> space Y))"
    by(auto simp: disintegration_sets_eq[OF assms(1)] intro!: sets_restrict_space_cong)
  also have "... = sets (restrict_space X A \<Otimes>\<^sub>M Y)"
    using sets_pair_restrict_space[of X A Y "space Y"]
    by simp
  finally show "sets (restrict_space \<nu> (A \<times> space Y)) = sets (restrict_space X A \<Otimes>\<^sub>M Y)" .
next
  show "sets (restrict_space \<mu> A) = sets (restrict_space X A)"
    by(auto simp: disintegration_sets_eq[OF assms(1)] intro!: sets_restrict_space_cong)
next
  fix a b
  assume h:"a \<in> sets (restrict_space X A)" "b \<in> sets Y"
  then have "restrict_space \<nu> (A \<times> space Y) (a \<times> b) = \<nu> (a \<times> b)"
    using sets.sets_into_space
    by(auto intro!: emeasure_restrict_space  simp: disintegration_space_eq[OF assms(1)] disintegration_sets_eq[OF assms(1)] sets_restrict_space)
      (metis Sigma_Int_distrib1 assms(2) pair_measureI sets.top space_pair_measure)
  also have "... = (\<integral>\<^sup>+x\<in>a. emeasure (\<kappa> x) b \<partial>\<mu>)"
    using sets_restrict_space_iff[OF assms(2)] h assms(1)
    by(auto simp: disintegration_def)
  also have "... = (\<integral>\<^sup>+x\<in>A. (emeasure (\<kappa> x) b * indicator a x) \<partial>\<mu>)"
    using h(1) by(auto intro!: nn_integral_cong simp: sets_restrict_space)
                 (metis IntD1 indicator_simps(1) indicator_simps(2) mult.comm_neutral mult_zero_right)
  also have "... = (\<integral>\<^sup>+x\<in>a. emeasure (\<kappa> x) b \<partial>restrict_space \<mu> A)"
    by (metis (no_types, lifting) assms disintegration_sets_eq(2) disintegration_space_eq(2) nn_integral_cong nn_integral_restrict_space)
  finally show "restrict_space \<nu> (A \<times> space Y) (a \<times> b) = (\<integral>\<^sup>+x\<in>a. emeasure (\<kappa> x) b \<partial>restrict_space \<mu> A)" .
qed

end

context subprob_kernel
begin
lemma countable_disintegration_AE_unique:
  assumes "countable (space Y)" and [measurable_cong]:"sets Y = Pow (space Y)"
      and "subprob_kernel X Y \<kappa>'" "sigma_finite_measure \<mu>"
      and "disintegration \<nu> \<mu>" "measure_kernel.disintegration X Y \<kappa>' \<nu> \<mu>"
    shows "AE x in \<mu>. \<kappa> x = \<kappa>' x"
proof -
  interpret \<kappa>': subprob_kernel X Y \<kappa>' by fact
  interpret s: sigma_finite_measure \<mu> by fact
  have sets_eq[measurable_cong]: "sets \<mu> = sets X" "sets \<nu> = sets (X \<Otimes>\<^sub>M Y)"
    using assms(5) by(auto simp: disintegration_def)
  have 1:"AE x in \<mu>. \<forall>y \<in> space Y. \<kappa> x {y} = \<kappa>' x {y}"
    unfolding AE_ball_countable[OF assms(1)]
  proof
    fix y
    assume y: "y \<in> space Y"
    show "AE x in \<mu>. emeasure (\<kappa> x) {y} = emeasure (\<kappa>' x) {y}"
    proof(rule s.sigma_finite)
      fix J :: "nat \<Rightarrow> _"
      assume J:"range J \<subseteq> sets \<mu>" " \<Union> (range J) = space \<mu>" "\<And>i. emeasure \<mu> (J i) \<noteq> \<infinity>"
      from y have [measurable]: "(\<lambda>x. \<kappa> x {y}) \<in> borel_measurable X" "(\<lambda>x. \<kappa>' x {y}) \<in> borel_measurable X"
        using emeasure_measurable \<kappa>'.emeasure_measurable by auto
      define A where "A \<equiv> {x \<in> space \<mu>. \<kappa> x {y} \<le> \<kappa>' x {y}}"
      have [measurable]:"A \<in> sets \<mu>"
        by(auto simp: A_def)
      have A: "\<And>x. x \<in> space \<mu> \<Longrightarrow> x \<notin> A \<Longrightarrow>  \<kappa>' x {y} \<le> \<kappa> x {y}"
        by(auto simp: A_def)
      have 1: "AE x\<in>A in \<mu>. \<kappa> x {y} = \<kappa>' x {y}"
      proof -
        have "AE x in \<mu>. \<forall>n. (x \<in> A \<inter> J n \<longrightarrow> \<kappa> x {y} = \<kappa>' x {y})"
          unfolding AE_all_countable
        proof
          fix n
          have ninf:"(\<integral>\<^sup>+x\<in>A \<inter> J n. (\<kappa> x) {y}\<partial>\<mu>) < \<infinity>"
          proof -
            have "(\<integral>\<^sup>+x\<in>A \<inter> J n. (\<kappa> x) {y}\<partial>\<mu>) \<le> (\<integral>\<^sup>+x\<in>A \<inter> J n. (\<kappa> x) (space Y) \<partial>\<mu>)"
              using kernel_sets y by(auto intro!: nn_integral_mono emeasure_mono simp: indicator_def disintegration_space_eq(2)[OF assms(5)])
            also have "... \<le> (\<integral>\<^sup>+x\<in>A \<inter> J n. 1 \<partial>\<mu>)"
              using subprob_space by(auto intro!: nn_integral_mono simp: indicator_def disintegration_space_eq(2)[OF assms(5)])
            also have "... = \<mu> (A \<inter> J n)"
              using J by simp
            also have "... \<le> \<mu> (J n)"
              using J by (auto intro!: emeasure_mono)
            also have "... < \<infinity>"
              using J(3)[of n] by (simp add: top.not_eq_extremum)
            finally show ?thesis .
          qed
          have "(\<integral>\<^sup>+x. (\<kappa>' x) {y} * indicator (A \<inter> J n) x - (\<kappa> x) {y} * indicator (A \<inter> J n) x \<partial>\<mu>) = (\<integral>\<^sup>+x\<in>A \<inter> J n. (\<kappa>' x) {y} \<partial>\<mu>) - (\<integral>\<^sup>+x\<in>A \<inter> J n. (\<kappa> x) {y}  \<partial>\<mu>)"
            using J ninf by(auto intro!: nn_integral_diff simp: indicator_def A_def)
          also have "... = 0"
          proof -
            have 0: "\<nu> ((A \<inter> J n) \<times> {y}) = (\<integral>\<^sup>+x\<in>A \<inter> J n. (\<kappa> x) {y} \<partial>\<mu>)"
              using J y sets_eq by(auto intro!: disintegrationD[OF assms(5),of "A \<inter> J n" "{y}"])
            have [simp]: "(\<integral>\<^sup>+x\<in>A \<inter> J n. (\<kappa>' x) {y} \<partial>\<mu>) = \<nu> ((A \<inter> J n) \<times> {y})"
              using J y sets_eq by(auto intro!: \<kappa>'.disintegrationD[OF assms(6),of "A \<inter> J n" "{y}",symmetric])
            show ?thesis
              using ninf by (simp add: 0 diff_eq_0_iff_ennreal)
          qed
          finally have assm:"AE x in \<mu>. (\<kappa>' x) {y} * indicator (A \<inter> J n) x - (\<kappa> x) {y} * indicator (A \<inter> J n) x = 0"
            using J by(simp add: nn_integral_0_iff_AE)
          show "AE x\<in>A \<inter> J n in \<mu>. (\<kappa> x) {y} = (\<kappa>' x) {y}"
          proof(rule AE_mp[OF assm])
            show "AE x in \<mu>. emeasure (\<kappa>' x) {y} * indicator (A \<inter> J n) x - emeasure (\<kappa> x) {y} * indicator (A \<inter> J n) x = 0 \<longrightarrow> x \<in> A \<inter> J n \<longrightarrow> emeasure (\<kappa> x) {y} = emeasure (\<kappa>' x) {y}"
            proof -
              {
                fix x
                assume h: "(\<kappa>' x) {y} - (\<kappa> x) {y} = 0" "x \<in> A"
                have "(\<kappa> x) {y} = (\<kappa>' x) {y}"
                  using h(2) by(auto intro!: antisym ennreal_minus_eq_0[OF h(1)] simp: A_def)
              }
              thus ?thesis
                by(auto simp: indicator_def)
            qed
          qed
        qed
        hence "AE x\<in>A \<inter> (\<Union> (range J))in \<mu>. \<kappa> x {y} = \<kappa>' x {y}"
          by auto
        thus ?thesis
          using J(2) by auto
      qed
      have 2: "AE x\<in> (space \<mu> - A) in \<mu>. \<kappa> x {y} = \<kappa>' x {y}"
      proof -
        have "AE x in \<mu>. \<forall>n. x \<in> (space \<mu> - A) \<inter> J n \<longrightarrow> \<kappa> x {y} = \<kappa>' x {y}"
          unfolding AE_all_countable
        proof
          fix n
          have ninf:"(\<integral>\<^sup>+x\<in>(space \<mu> - A) \<inter> J n. (\<kappa>' x) {y}\<partial>\<mu>) < \<infinity>"
          proof -
            have "(\<integral>\<^sup>+x\<in>(space \<mu> - A) \<inter> J n. (\<kappa>' x) {y}\<partial>\<mu>) \<le> (\<integral>\<^sup>+x\<in>(space \<mu> - A) \<inter> J n. (\<kappa>' x) (space Y) \<partial>\<mu>)"
              using kernel_sets y by(auto intro!: nn_integral_mono emeasure_mono simp: indicator_def disintegration_space_eq(2)[OF assms(5)])
            also have "... \<le> (\<integral>\<^sup>+x\<in>(space \<mu> - A) \<inter> J n. 1 \<partial>\<mu>)"
              using \<kappa>'.subprob_space by(auto intro!: nn_integral_mono simp: indicator_def disintegration_space_eq(2)[OF assms(5)])
            also have "... = \<mu> ((space \<mu> - A) \<inter> J n)"
              using J by simp
            also have "... \<le> \<mu> (J n)"
              using J by (auto intro!: emeasure_mono)
            also have "... < \<infinity>"
              using J(3)[of n] by (simp add: top.not_eq_extremum)
            finally show ?thesis .
          qed
          have "(\<integral>\<^sup>+x. (\<kappa> x) {y} * indicator ((space \<mu> - A) \<inter> J n) x - (\<kappa>' x) {y} * indicator ((space \<mu> - A) \<inter> J n) x \<partial>\<mu>) = (\<integral>\<^sup>+x\<in>(space \<mu> - A) \<inter> J n. (\<kappa> x) {y} \<partial>\<mu>) - (\<integral>\<^sup>+x\<in>(space \<mu> - A) \<inter> J n. (\<kappa>' x) {y}  \<partial>\<mu>)"
            using J ninf A by(auto intro!: nn_integral_diff simp: indicator_def)
          also have "... = 0"
          proof -
            have 0: "(\<integral>\<^sup>+x\<in>(space \<mu> - A) \<inter> J n. (\<kappa>' x) {y} \<partial>\<mu>) = \<nu> (((space \<mu> - A) \<inter> J n) \<times> {y})"
              using J y sets_eq by(auto intro!: \<kappa>'.disintegrationD[OF assms(6),of "(space \<mu> - A) \<inter> J n" "{y}",symmetric])
            have [simp]: "\<nu> (((space \<mu> - A) \<inter> J n) \<times> {y}) = (\<integral>\<^sup>+x\<in>(space \<mu> - A) \<inter> J n. (\<kappa> x) {y} \<partial>\<mu>)"
              using J y sets_eq by(auto intro!: disintegrationD[OF assms(5),of "(space \<mu> - A) \<inter> J n" "{y}"])
            show ?thesis
              using ninf by (simp add: 0 diff_eq_0_iff_ennreal)
          qed
          finally have assm:"AE x in \<mu>. (\<kappa> x) {y} * indicator ((space \<mu> - A) \<inter> J n) x - (\<kappa>' x) {y} * indicator ((space \<mu> - A) \<inter> J n) x = 0"
            using J by(simp add: nn_integral_0_iff_AE)
          show "AE x\<in>(space \<mu> - A) \<inter> J n in \<mu>. (\<kappa> x) {y} = (\<kappa>' x) {y}"
          proof(rule AE_mp[OF assm])
            show "AE x in \<mu>. emeasure (\<kappa> x) {y} * indicator ((space \<mu> - A) \<inter> J n) x - emeasure (\<kappa>' x) {y} * indicator ((space \<mu> - A) \<inter> J n) x = 0 \<longrightarrow> x \<in> (space \<mu> - A) \<inter> J n \<longrightarrow> emeasure (\<kappa> x) {y} = emeasure (\<kappa>' x) {y}"
            proof -
              {
                fix x
                assume h: "(\<kappa> x) {y} - (\<kappa>' x) {y} = 0" "x \<in> space \<mu>" "x \<notin> A"
                have "(\<kappa> x) {y} = (\<kappa>' x) {y}"
                  using A[OF h(2,3)] by(auto intro!: antisym ennreal_minus_eq_0[OF h(1)] simp: A_def)
              }
              thus ?thesis
                by(auto simp: indicator_def)
            qed
          qed
        qed
        hence "AE x\<in>(space \<mu> - A) \<inter> (\<Union> (range J))in \<mu>. \<kappa> x {y} = \<kappa>' x {y}"
          by auto
        thus ?thesis
          using J(2) by auto
      qed
      show "AE x in \<mu>. \<kappa> x {y} = \<kappa>' x {y}"
        using 1 2 by(auto simp: A_def)
    qed
  qed
  show ?thesis
  proof(rule AE_mp[OF 1])
    {
      fix x
      assume x: "x \<in> space X"
        and h: "\<forall>y\<in>space Y. \<kappa> x {y} = \<kappa>' x {y}"
      have "\<kappa> x = \<kappa>' x "
        by (simp add: \<kappa>'.kernel_sets assms h kernel_sets measure_eqI_countable x)
    }
    thus " AE x in \<mu>. (\<forall>y\<in>space Y. emeasure (\<kappa> x) {y} = emeasure (\<kappa>' x) {y}) \<longrightarrow> \<kappa> x = \<kappa>' x"
      by(auto simp: sets_eq_imp_space_eq[OF sets_eq(1)])
  qed
qed

end

lemma(in subprob_kernel) nu_mu_spaceY_le:
  assumes "disintegration \<nu> \<mu>" "A \<in> sets X"
  shows "\<nu> (A \<times> space Y) \<le> \<mu> A"
proof -
  have "\<nu> (A \<times> space Y) = (\<integral>\<^sup>+x\<in>A. (\<kappa> x (space Y)) \<partial>\<mu>)"
    using assms by(simp add: disintegration_def)
  also have "... \<le> (\<integral>\<^sup>+x\<in>A. 1 \<partial>\<mu>)"
    using assms subprob_space by(auto intro!: nn_integral_mono simp:  disintegration_space_eq) (metis dual_order.refl indicator_simps(1) indicator_simps(2) mult.commute mult_1 mult_zero_right)
  also have "... = \<mu> A"
    using assms by (simp add: disintegration_def) 
  finally show ?thesis .
qed

context prob_kernel
begin

lemma countable_disintegration_AE_unique_prob:
  assumes "countable (space Y)" and [measurable_cong]:"sets Y = Pow (space Y)"
      and "prob_kernel X Y \<kappa>'" "sigma_finite_measure \<mu>"
      and "disintegration \<nu> \<mu>" "measure_kernel.disintegration X Y \<kappa>' \<nu> \<mu>"
    shows "AE x in \<mu>. \<kappa> x = \<kappa>' x"
  by(auto intro!: countable_disintegration_AE_unique[OF assms(1,2) _ assms(4-6)] prob_kernel.subprob_kernel assms(3))

end

subsection \<open> Lemma 14.D.3. \<close>
lemma(in prob_kernel) nu_mu_spaceY:
  assumes "disintegration \<nu> \<mu>" "A \<in> sets X"
  shows "\<nu> (A \<times> space Y) = \<mu> A"
proof -
  have "\<nu> (A \<times> space Y) = (\<integral>\<^sup>+x\<in>A. (\<kappa> x (space Y)) \<partial>\<mu>)"
    using assms by(simp add: disintegration_def)
  also have "... = (\<integral>\<^sup>+x\<in>A. 1 \<partial>\<mu>)"
    using assms by(auto intro!: nn_integral_cong simp: prob_space disintegration_space_eq)
  also have "... = \<mu> A"
    using assms by (simp add: disintegration_def) 
  finally show ?thesis .
qed

corollary(in subprob_kernel) nu_finite:
  assumes "disintegration \<nu> \<mu>" "finite_measure \<mu>"
  shows "finite_measure \<nu>"
proof
  have "\<nu> (space \<nu>) = \<nu> (space (X \<Otimes>\<^sub>M Y))"
    using assms by(simp add: disintegration_space_eq)
  also have "... \<le> \<mu> (space \<mu>)"
    using assms by(simp add: nu_mu_spaceY_le disintegration_space_eq space_pair_measure)
  finally show "\<nu> (space \<nu>) \<noteq> \<infinity>"
    using assms(2) by (metis finite_measure.emeasure_finite infinity_ennreal_def neq_top_trans)
qed

corollary(in subprob_kernel) nu_subprob_space:
  assumes "disintegration \<nu> \<mu>" "subprob_space \<mu>"
  shows "subprob_space \<nu>"
proof
  have "\<nu> (space \<nu>) = \<nu> (space (X \<Otimes>\<^sub>M Y))"
    using assms by(simp add: disintegration_space_eq)
  also have "... \<le> \<mu> (space \<mu>)"
    using assms by(simp add: nu_mu_spaceY_le disintegration_space_eq space_pair_measure)
  finally show "\<nu> (space \<nu>) \<le> 1"
    using assms(2) order.trans subprob_space.emeasure_space_le_1 by auto
next
  show "space \<nu> \<noteq> {}"
    using Y_not_empty assms by(auto simp: disintegration_space_eq subprob_space_def subprob_space_axioms_def space_pair_measure)
qed

corollary(in prob_kernel) nu_prob_space:
  assumes "disintegration \<nu> \<mu>" "prob_space \<mu>"
  shows "prob_space \<nu>"
proof
  have "\<nu> (space \<nu>) = \<nu> (space (X \<Otimes>\<^sub>M Y))"
    using assms by(simp add: disintegration_space_eq)
  also have "... = \<mu> (space \<mu>)"
    using assms by(simp add: nu_mu_spaceY disintegration_space_eq space_pair_measure)
  finally show "\<nu> (space \<nu>) = 1"
    by (simp add: assms(2) prob_space.emeasure_space_1)
qed

lemma(in subprob_kernel) nu_sigma_finite:
  assumes "disintegration \<nu> \<mu>" "sigma_finite_measure \<mu>"
  shows "sigma_finite_measure \<nu>"
proof
  obtain A where A:"countable A" "A \<subseteq> sets \<mu>" "\<Union> A = space \<mu>" "\<forall>a\<in>A. emeasure \<mu> a \<noteq> \<infinity>"
    using assms(2) by (meson sigma_finite_measure.sigma_finite_countable)
  have "countable {a \<times> space Y |a. a \<in> A}"
    using countable_image[OF A(1),of "\<lambda>a. a \<times> space Y"]
    by (simp add: Setcompr_eq_image)
  moreover have "{a \<times> space Y |a. a \<in> A} \<subseteq> sets \<nu>"
    using A(2) assms(1) disintegration_def by auto
  moreover have "\<Union> {a \<times> space Y |a. a \<in> A} = space \<nu>"
    using assms A(3) by(simp add: disintegration_space_eq space_pair_measure) blast
  moreover have "\<forall>b\<in>{a \<times> space Y |a. a \<in> A}. emeasure \<nu> b \<noteq> \<infinity>"
    using neq_top_trans[OF _ nu_mu_spaceY_le[OF assms(1)]] A(2,4) assms disintegration_sets_eq(2) by auto
  ultimately show "\<exists>B. countable B \<and> B \<subseteq> sets \<nu> \<and> \<Union> B = space \<nu> \<and> (\<forall>b\<in>B. emeasure \<nu> b \<noteq> \<infinity>)"
    by blast
qed

subsection \<open> Theorem 14.D.4. (Measure Mixture Theorem) \<close>
lemma(in measure_kernel) exist_nu:
  assumes "sets \<mu> = sets X"
  shows "\<exists>\<nu>. disintegration \<nu> \<mu>"
proof -
  define \<nu> where "\<nu> = extend_measure (space X \<times> space Y) {(a, b). a \<in> sets X \<and> b \<in> sets Y} (\<lambda>(a, b). a \<times> b) (\<lambda>(a, b). \<integral>\<^sup>+x\<in>a. emeasure (\<kappa> x) b\<partial>\<mu>) "
  have 1: "sets \<nu> = sets (X \<Otimes>\<^sub>M Y)"
  proof -
    have "sets \<nu> = sigma_sets (space X \<times> space Y) ((\<lambda>(a, b). a \<times> b) ` {(a, b). a \<in> sets X \<and> b \<in> sets Y})"
      unfolding \<nu>_def
      by(rule sets_extend_measure) (use sets.space_closed[of X] sets.space_closed[of Y] in blast)
    also have "... = sigma_sets (space X \<times> space Y) {a \<times> b |a b. a \<in> sets X \<and> b \<in> sets Y}"
      by(auto intro!: sigma_sets_eqI)
    also have "... = sets (X \<Otimes>\<^sub>M Y)"
      by(simp add: sets_pair_measure)
    finally show ?thesis .
  qed
  have 2: "\<nu> (A \<times> B) = (\<integral>\<^sup>+x\<in>A. (\<kappa> x B) \<partial>\<mu>)" if "A \<in> sets X" "B \<in> sets Y" for A B
  proof(rule extend_measure_caratheodory_pair[OF \<nu>_def])
    fix i j k l
    assume "i \<in> sets X \<and> j \<in> sets Y" "k \<in> sets X \<and> l \<in> sets Y" "i \<times> j = k \<times> l"
    then consider "i = k" "j = l" | "i \<times> j = {}" "k \<times> l = {}" by blast
    thus "(\<integral>\<^sup>+x\<in>i. emeasure (\<kappa> x) j \<partial>\<mu>) = (\<integral>\<^sup>+x\<in>k. emeasure (\<kappa> x) l \<partial>\<mu>)" 
      by cases auto
  next
    fix A B j k
    assume h: "\<And>n::nat. A n \<in> sets X \<and> B n \<in> sets Y" "j \<in> sets X \<and> k \<in> sets Y" "disjoint_family (\<lambda>n. A n \<times> B n)" "(\<Union>i. A i \<times> B i) = j \<times> k"
    show "(\<Sum>n. \<integral>\<^sup>+x\<in>A n. emeasure (\<kappa> x) (B n)\<partial>\<mu>) = (\<integral>\<^sup>+x\<in>j. emeasure (\<kappa> x) k\<partial>\<mu>)"
         (is "?lhs = ?rhs")
    proof -
      have "?lhs = (\<integral>\<^sup>+x. (\<Sum>n. \<kappa> x (B n) * indicator (A n) x)\<partial>\<mu>)"
      proof(rule nn_integral_suminf[symmetric])
        fix n
        have [measurable]:"(\<lambda>x. emeasure (\<kappa> x) (B n)) \<in> borel_measurable \<mu>" "indicator (A n) \<in> borel_measurable \<mu>"
          using h(1)[of n] emeasure_measurable[of "B n"] assms(1) by auto
        thus "(\<lambda>x. emeasure (\<kappa> x) (B n) * indicator (A n) x) \<in> borel_measurable \<mu>"
          by simp
      qed
      also have "... = ?rhs"
      proof(safe intro!: nn_integral_cong)
        fix x
        assume "x \<in> space \<mu>"
        consider "j = {}" | "k = {}" | "j \<noteq> {}" "k \<noteq> {}" by auto
        then show "(\<Sum>n. emeasure (\<kappa> x) (B n) * indicator (A n) x) = emeasure (\<kappa> x) k * indicator j x"
        proof cases
          case 1
          then have "\<And>n. A n \<times> B n = {}"
            using h(4) by auto
          have "emeasure (\<kappa> x) (B n) * indicator (A n) x = 0" for n
            using \<open>A n \<times> B n = {}\<close> by(auto simp: Sigma_empty_iff)
          thus ?thesis
            by(simp only: 1,simp)
        next
          case 2
          then have "\<And>n. A n \<times> B n = {}"
            using h(4) by auto
          have "emeasure (\<kappa> x) (B n) * indicator (A n) x = 0" for n
            using \<open>A n \<times> B n = {}\<close> by(auto simp: Sigma_empty_iff)
          thus ?thesis
            by(simp only: 2,simp)
        next
          case 3
          then have xinjiff:"x \<in> j \<longleftrightarrow> (\<exists>i. \<exists>y\<in>B i. (x,y) \<in> A i \<times> B i)"
            using h(4) by blast
          have bunk:"\<Union> (B ` {i. x \<in> A i}) = k" if "x \<in> j"
            using that 3 h(4) by blast
          show ?thesis
          proof(cases "x \<in> j")
            case False
            then have "\<And>n. x \<notin> A n \<or> B n = {}"
              using h(4) 3 xinjiff by auto
            have "emeasure (\<kappa> x) (B n) * indicator (A n) x = 0" for n
              using \<open>x \<notin> A n \<or> B n = {}\<close> by auto
            thus ?thesis
              by(simp only:)(simp add: False)
          next
            case True
            then have [simp]: "emeasure (\<kappa> x) k * indicator j x = emeasure (\<kappa> x) k"
              by simp
            have "(\<Sum>n. emeasure (\<kappa> x) (B n) * indicator (A n) x) = (\<Sum>n. emeasure (\<kappa> x) (if x \<in> A n then B n else {}))"
              by(auto intro!: suminf_cong)
            also have "... = emeasure (\<kappa> x) (\<Union>n. if x \<in> A n then B n else {})"
            proof(rule suminf_emeasure)
              show "disjoint_family (\<lambda>i. if x \<in> A i then B i else {})"
                using disjoint_family_onD[OF h(3)] by (auto simp: disjoint_family_on_def)
            next
              show "range (\<lambda>i. if x \<in> A i then B i else {}) \<subseteq> sets (\<kappa> x)"
                using h(1) kernel_sets[of x] \<open>x \<in> space \<mu>\<close> sets_eq_imp_space_eq[OF assms(1)] by auto
            qed
            also have "... = emeasure (\<kappa> x) k"
              using True by(simp add: bunk)
            finally show ?thesis by simp
          qed
        qed
      qed
      finally show ?thesis .
    qed
  qed(use that in auto)
  show ?thesis
    using 1 2 assms
    by(auto simp: disintegration_def)
qed

lemma(in subprob_kernel) exist_unique_nu_sigma_finite':
  assumes "sets \<mu> = sets X" "sigma_finite_measure \<mu>"
  shows "\<exists>!\<nu>. disintegration \<nu> \<mu>"
proof -
  obtain \<nu> where disi: "disintegration \<nu> \<mu>"
    using exist_nu[OF assms(1)] by auto
  with assms(2) interpret sf: sigma_finite_measure \<nu>
    by(simp add: nu_sigma_finite)
  interpret \<mu>: sigma_finite_measure \<mu> by fact
  show ?thesis
  proof(rule ex1I[where a=\<nu>])
    fix \<nu>'
    assume disi':"disintegration \<nu>' \<mu>"
    show "\<nu>' = \<nu>"
    proof(rule \<mu>.sigma_finite_disjoint)
      fix A :: "nat \<Rightarrow> _"
      assume A: "range A \<subseteq> sets \<mu>" "\<Union> (range A) = space \<mu>" "\<And>i. emeasure \<mu> (A i) \<noteq> \<infinity>" "disjoint_family A"
      define B where "B \<equiv> \<lambda>i. A i \<times> space Y"
      show "\<nu>' = \<nu>"
      proof(rule measure_eqI_generator_eq[where E=" {a \<times> b|a b. a \<in> sets X \<and> b \<in> sets Y}" and A=B and \<Omega>="space X \<times> space Y"])
        show "\<And>C. C \<in> {a \<times> b |a b. a \<in> sets X \<and> b \<in> sets Y} \<Longrightarrow> emeasure \<nu>' C = emeasure \<nu> C"
             "sets \<nu>' = sigma_sets (space X \<times> space Y) {a \<times> b |a b. a \<in> sets X \<and> b \<in> sets Y}"
             "sets \<nu> = sigma_sets (space X \<times> space Y) {a \<times> b |a b. a \<in> sets X \<and> b \<in> sets Y}"
          using disi disi' by(auto simp: disintegration_def sets_pair_measure)
      next
        show "range B \<subseteq> {a \<times> b |a b. a \<in> sets X \<and> b \<in> sets Y}"
             "\<Union> (range B) = space X \<times> space Y"
          using A(1,2) by(auto simp: B_def assms(1) sets_eq_imp_space_eq[OF assms(1)])
      next
        fix i
        show "emeasure \<nu>' (B i) \<noteq> \<infinity>"
          using A(1) nu_mu_spaceY_le[OF disi',of "A i"] A(3)[of i] by(auto simp: B_def assms top.extremum_uniqueI)
      qed(simp_all add: Int_stable_pair_measure_generator pair_measure_closed)
    qed
  qed fact
qed

lemma(in subprob_kernel) exist_unique_nu_sigma_finite:
  assumes "sets \<mu> = sets X" "sigma_finite_measure \<mu>"
  shows "\<exists>!\<nu>. disintegration \<nu> \<mu> \<and> sigma_finite_measure \<nu>"
  using assms exist_unique_nu_sigma_finite' nu_sigma_finite by blast

lemma(in subprob_kernel) exist_unique_nu_finite:
  assumes "sets \<mu> = sets X" "finite_measure \<mu>"
  shows "\<exists>!\<nu>. disintegration \<nu> \<mu> \<and> finite_measure \<nu>"
  using assms nu_finite finite_measure.sigma_finite_measure[OF assms(2)] exist_unique_nu_sigma_finite' by blast

lemma(in subprob_kernel) exist_unique_nu_sub_prob_space:
  assumes "sets \<mu> = sets X" "subprob_space \<mu>"
  shows "\<exists>!\<nu>. disintegration \<nu> \<mu> \<and> subprob_space \<nu>"
  using assms nu_subprob_space subprob_space_imp_sigma_finite[OF assms(2)] exist_unique_nu_sigma_finite' by blast

lemma(in prob_kernel) exist_unique_nu_prob_space:
  assumes "sets \<mu> = sets X" "prob_space \<mu>"
  shows "\<exists>!\<nu>. disintegration \<nu> \<mu> \<and> prob_space \<nu>"
  using assms nu_prob_space prob_space_imp_sigma_finite[OF assms(2)] exist_unique_nu_sigma_finite' by blast


lemma(in subprob_kernel) nn_integral_fst_finite':
  assumes "f \<in> borel_measurable (X \<Otimes>\<^sub>M Y)" "disintegration \<nu> \<mu>" "finite_measure \<mu>"
  shows "(\<integral>\<^sup>+z. f z \<partial>\<nu>) = (\<integral>\<^sup>+x. \<integral>\<^sup>+y. f (x,y) \<partial>(\<kappa> x) \<partial>\<mu>)"
  using assms(1)
proof induction
  case (cong f g)
  have "integral\<^sup>N \<nu> f = integral\<^sup>N \<nu> g"
    using cong(3) by(auto intro!: nn_integral_cong simp: disintegration_space_eq(1)[OF assms(2)])
  with cong(3) show ?case
    by(auto simp: cong(4) kernel_space disintegration_space_eq(2)[OF assms(2)] space_pair_measure intro!: nn_integral_cong)
next
  case (set A)
  show ?case
  proof(rule sigma_sets_induct_disjoint[of "{a \<times> b|a b. a \<in> sets X \<and> b \<in> sets Y}" "space X \<times> space Y"])
    show "A \<in> sigma_sets (space X \<times> space Y) {a \<times> b |a b. a \<in> sets X \<and> b \<in> sets Y}"
      using set by(simp add: sets_pair_measure)
  next
    fix A
    assume "A \<in> {a \<times> b |a b. a \<in> sets X \<and> b \<in> sets Y}"
    then obtain a b where ab: "A = a \<times> b" "a \<in> sets X" "b \<in> sets Y"
      by auto
    with assms(2) have "integral\<^sup>N \<nu> (indicator A) = (\<integral>\<^sup>+x\<in>a. (\<kappa> x b) \<partial>\<mu>)"
      by(simp add: disintegration_def)
    also have "... = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator A (x, y) \<partial>\<kappa> x \<partial>\<mu>)"
      by(auto simp: ab(1) indicator_times disintegration_space_eq(2)[OF assms(2)] ab(3) kernel_sets mult.commute nn_integral_cmult_indicator intro!: nn_integral_cong)
    finally show "integral\<^sup>N \<nu> (indicator A) = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator A (x, y) \<partial>\<kappa> x \<partial>\<mu>)" .
  next
    fix A
    assume h: "A \<in> sigma_sets (space X \<times> space Y) {a \<times> b |a b. a \<in> sets X \<and> b \<in> sets Y}" "integral\<^sup>N \<nu> (indicator A) = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator A (x, y) \<partial>\<kappa> x \<partial>\<mu>)"
    show "integral\<^sup>N \<nu> (indicator (space X \<times> space Y - A)) = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator (space X \<times> space Y - A) (x, y) \<partial>\<kappa> x \<partial>\<mu>)" (is "?lhs = ?rhs")
    proof -
      have "?lhs = (\<integral>\<^sup>+ z. 1 - indicator A z \<partial>\<nu>)"
        by(auto intro!: nn_integral_cong simp: disintegration_space_eq(1)[OF assms(2)] space_pair_measure indicator_def)
      also have "... = (\<integral>\<^sup>+ z. 1 \<partial>\<nu>) - (\<integral>\<^sup>+ z. indicator A z \<partial>\<nu>)"
      proof(rule nn_integral_diff)
        show "integral\<^sup>N \<nu> (indicator A) \<noteq> \<infinity>"
          using h(1)[simplified sets_pair_measure[symmetric]] disintegration_sets_eq(1)[OF assms(2)] finite_measure.emeasure_finite[OF nu_finite[OF assms(2,3)]]
          by auto
      next
        show "indicator A \<in> borel_measurable \<nu>"
          using h(1)[simplified sets_pair_measure[symmetric]] disintegration_sets_eq(1)[OF assms(2)] by simp
      qed(simp_all add: indicator_def)
      also have "... = (\<integral>\<^sup>+ z. 1 \<partial>\<nu>) - (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator A (x, y) \<partial>\<kappa> x \<partial>\<mu>)"
        by(simp add: h(2))
      also have "... = \<nu> (space X \<times> space Y) - (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator A (x, y) \<partial>\<kappa> x \<partial>\<mu>)"
        using nn_integral_indicator[OF sets.top[of \<nu>]] by(simp add: space_pair_measure disintegration_space_eq(1)[OF assms(2)])
      also have "... = (\<integral>\<^sup>+ x. \<kappa> x (space Y) \<partial>\<mu>) - (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator A (x, y) \<partial>\<kappa> x \<partial>\<mu>)"
      proof -
        have "\<nu> (space X \<times> space Y) = (\<integral>\<^sup>+ x. \<kappa> x (space Y) \<partial>\<mu>)"
          using assms(2) by(auto simp: disintegration_def disintegration_space_eq(2)[OF assms(2)] intro!: nn_integral_cong)
        thus ?thesis by simp
      qed
      also have "... = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator (space X \<times> space Y) (x, y) \<partial>\<kappa> x \<partial>\<mu>) - (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator A (x, y) \<partial>\<kappa> x \<partial>\<mu>)"
      proof -
        have "(\<integral>\<^sup>+ x. \<kappa> x (space Y) \<partial>\<mu>) = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator (space X \<times> space Y) (x, y) \<partial>\<kappa> x \<partial>\<mu>)"
          using kernel_sets by(auto intro!: nn_integral_cong simp: indicator_times disintegration_space_eq(2)[OF assms(2)] )
        thus ?thesis by simp
      qed
      also have "... = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. indicator (space X \<times> space Y) (x, y) \<partial>\<kappa> x) - (\<integral>\<^sup>+ y. indicator A (x, y) \<partial>\<kappa> x) \<partial>\<mu>)"
      proof(rule nn_integral_diff[symmetric])
        show "(\<lambda>x. \<integral>\<^sup>+ y. indicator (space X \<times> space Y) (x, y) \<partial>\<kappa> x) \<in> borel_measurable \<mu>"
             "(\<lambda>x. \<integral>\<^sup>+ y. indicator A (x, y) \<partial>\<kappa> x) \<in> borel_measurable \<mu>"
           by(use disintegration_sets_eq[OF assms(2)] nn_integral_measurable_f h(1)[simplified sets_pair_measure[symmetric]] in auto)+
       next
         have "(\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator A (x, y) \<partial>\<kappa> x \<partial>\<mu>) \<le> (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. 1 \<partial>\<kappa> x \<partial>\<mu>)"
           by(rule nn_integral_mono)+ (simp add: indicator_def)
         also have "... \<le> (\<integral>\<^sup>+ x. 1 \<partial>\<mu>)"
           by(rule nn_integral_mono) (simp add: subprob_spaces disintegration_space_eq(2)[OF assms(2)] subprob_space.subprob_emeasure_le_1)
         also have "... < \<infinity>"
           using finite_measure.emeasure_finite[OF assms(3)]
           by (simp add: top.not_eq_extremum) 
         finally show "(\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator A (x, y) \<partial>\<kappa> x \<partial>\<mu>) \<noteq> \<infinity>"
           by auto
       next
         have "A \<subseteq> space X \<times> space Y"
           by (metis h(1) sets.sets_into_space sets_pair_measure space_pair_measure)
         hence "\<And>x. (\<integral>\<^sup>+ y. indicator A (x, y) \<partial>\<kappa> x) \<le> (\<integral>\<^sup>+ y. indicator (space X \<times> space Y) (x, y) \<partial>\<kappa> x)"
           by(auto intro!: nn_integral_mono)
         thus "AE x in \<mu>. (\<integral>\<^sup>+ y. indicator A (x, y) \<partial>\<kappa> x) \<le> (\<integral>\<^sup>+ y. indicator (space X \<times> space Y) (x, y) \<partial>\<kappa> x)"
           by simp
       qed
       also have "... = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. indicator (space X \<times> space Y) (x, y) - indicator A (x, y) \<partial>\<kappa> x) \<partial>\<mu>)"
       proof(intro nn_integral_cong nn_integral_diff[symmetric])
         fix x
         assume "x \<in> space \<mu>"
         then have "x \<in> space X"
           by(auto simp: disintegration_space_eq(2)[OF assms(2)])
         with kernel_sets[OF this] h(1)[simplified sets_pair_measure[symmetric]]
         show "(\<lambda>y. indicator (space X \<times> space Y) (x, y)) \<in> borel_measurable (\<kappa> x)"
              "(\<lambda>y. indicator A (x, y)) \<in> borel_measurable (\<kappa> x)"
           by auto
       next
         fix x
         assume "x \<in> space \<mu>"
         then have "x \<in> space X"
           by(auto simp: disintegration_space_eq(2)[OF assms(2)])
         have "(\<integral>\<^sup>+ y. indicator A (x, y) \<partial>\<kappa> x) \<le> (\<integral>\<^sup>+ y. 1 \<partial>\<kappa> x)"
           by(rule nn_integral_mono) (simp add: indicator_def)
         also have "... \<le> 1"
           using subprob_spaces[OF \<open>x \<in> space X\<close>] by (simp add: subprob_space.subprob_emeasure_le_1)
         also have "... < \<infinity>"
           by auto           
         finally show "(\<integral>\<^sup>+ y. indicator A (x, y) \<partial>\<kappa> x) \<noteq> \<infinity>"
           by simp
         have "A \<subseteq> space X \<times> space Y"
           by (metis h(1) sets.sets_into_space sets_pair_measure space_pair_measure)
         thus "AE y in \<kappa> x. indicator A (x, y) \<le> (indicator (space X \<times> space Y) (x, y) :: ennreal)"
           by auto
       qed
       also have "... = ?rhs"
         by(auto simp: indicator_def intro!: nn_integral_cong)
       finally show ?thesis .
     qed
   next
    fix A
    assume h:"disjoint_family A" "range A \<subseteq> sigma_sets (space X \<times> space Y) {a \<times> b |a b. a \<in> sets X \<and> b \<in> sets Y}"
              "\<And>i::nat.  integral\<^sup>N \<nu> (indicator (A i)) = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator (A i) (x, y) \<partial>\<kappa> x \<partial>\<mu>)"
    show "integral\<^sup>N \<nu> (indicator (\<Union> (range A))) = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator (\<Union> (range A)) (x, y) \<partial>\<kappa> x \<partial>\<mu>)" (is "?lhs = ?rhs")
    proof -
      have "?lhs = (\<integral>\<^sup>+ z. (\<Sum>i. indicator (A i) z) \<partial>\<nu>)"
        by(simp add: suminf_indicator[OF h(1)])
      also have "... = (\<Sum>i. (\<integral>\<^sup>+ z. indicator (A i) z \<partial>\<nu>))" 
        by(rule nn_integral_suminf) (use disintegration_sets_eq(1)[OF assms(2)] h(2)[simplified sets_pair_measure[symmetric]] in simp)
      also have "... = (\<Sum>i. (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator (A i) (x, y) \<partial>\<kappa> x \<partial>\<mu>))"
        by(simp add: h)
      also have "... = (\<integral>\<^sup>+ x. (\<Sum>i. (\<integral>\<^sup>+ y. indicator (A i) (x, y) \<partial>\<kappa> x)) \<partial>\<mu>)"
        by(rule nn_integral_suminf[symmetric]) (use h(2)[simplified sets_pair_measure[symmetric]] disintegration_sets_eq(2)[OF assms(2)] nn_integral_measurable_f in simp)       
      also have "... = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. (\<Sum>i.  indicator (A i) (x, y)) \<partial>\<kappa> x \<partial>\<mu>)"
        using h(2)[simplified sets_pair_measure[symmetric]] kernel_sets
        by(auto intro!: nn_integral_cong nn_integral_suminf[symmetric] simp: disintegration_space_eq(2)[OF assms(2)])
      also have "... = ?rhs"
        by(simp add: suminf_indicator[OF h(1)])
      finally show ?thesis .
    qed
  qed(simp_all add: Int_stable_pair_measure_generator pair_measure_closed)   
next
  case (mult u c)
  show ?case (is "?lhs = ?rhs")
  proof -
    have "?lhs = c * (\<integral>\<^sup>+ z. u z \<partial>\<nu>)"
      using disintegration_sets_eq(1)[OF assms(2)] mult
      by(simp add: nn_integral_cmult)
    also have "... = c * ( \<integral>\<^sup>+ x. \<integral>\<^sup>+ y. u (x, y) \<partial>\<kappa> x \<partial>\<mu>)"
      by(simp add: mult)
    also have "... = ( \<integral>\<^sup>+ x. c * (\<integral>\<^sup>+ y. u (x, y) \<partial>\<kappa> x) \<partial>\<mu>)"
      using nn_integral_measurable_f'[OF mult(2)] disintegration_sets_eq(2)[OF assms(2)]
      by(simp add: nn_integral_cmult)
    also have "... = ?rhs"
      using mult by(auto intro!: nn_integral_cong nn_integral_cmult[symmetric] simp: disintegration_space_eq(2)[OF assms(2)])
    finally show ?thesis .
  qed
next
  case (add u v)
  show ?case (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<integral>\<^sup>+ z. v z \<partial>\<nu>) + (\<integral>\<^sup>+ z. u z \<partial>\<nu>)"
      using add disintegration_sets_eq(1)[OF assms(2)] by (simp add: nn_integral_add)
    also have "... = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. v (x, y) \<partial>\<kappa> x \<partial>\<mu>) + (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. u (x, y) \<partial>\<kappa> x \<partial>\<mu>)"
      by(simp add: add)
    also have "... = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. v (x, y) \<partial>\<kappa> x) + (\<integral>\<^sup>+ y. u (x, y) \<partial>\<kappa> x) \<partial>\<mu>)"
      using nn_integral_measurable_f'[OF add(1)] nn_integral_measurable_f'[OF add(3)] disintegration_sets_eq[OF assms(2)]
      by(auto intro!: nn_integral_add[symmetric])
    also have "... = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. v (x, y) + u (x, y) \<partial>\<kappa> x) \<partial>\<mu>)"
      using add by(auto intro!: nn_integral_add[symmetric] nn_integral_cong simp: disintegration_space_eq(2)[OF assms(2)])
    finally show ?thesis .
  qed
next
  case (seq fi)
  have "(\<integral>\<^sup>+ y. (\<Squnion> range fi) (x, y) \<partial>\<kappa> x) = (\<Squnion>i. \<integral>\<^sup>+ y. fi i (x, y) \<partial>\<kappa> x)" (is "?lhs = ?rhs") if "x \<in> space X" for x
  proof -
    have "?lhs = (\<integral>\<^sup>+ y. (\<Squnion>i. fi i (x, y)) \<partial>\<kappa> x)"
      by(metis SUP_apply)
    also have "... = ?rhs"
    proof(rule nn_integral_monotone_convergence_SUP)
      show "incseq (\<lambda>i y. fi i (x, y))"
        using seq mono_compose by blast 
    next
      fix i
      show "(\<lambda>y. fi i (x, y)) \<in> borel_measurable (\<kappa> x)"
        using seq(1)[of i] that kernel_sets[OF that] by simp
    qed
    finally show ?thesis .
  qed
  have "integral\<^sup>N \<nu> (\<Squnion> range fi) = (\<integral>\<^sup>+ x. (\<Squnion>i. fi i x) \<partial>\<nu>)"
    by (metis SUP_apply)
  also have "... = (\<Squnion>i. integral\<^sup>N \<nu> (fi i))"
    using disintegration_sets_eq(1)[OF assms(2)] seq(1,3)
    by(auto intro!: nn_integral_monotone_convergence_SUP)
  also have "... = (\<Squnion>i. \<integral>\<^sup>+ x. \<integral>\<^sup>+ y. fi i (x, y) \<partial>\<kappa> x \<partial>\<mu>)"
    by(simp add: seq)
  also have "... = (\<integral>\<^sup>+ x. (\<Squnion>i. \<integral>\<^sup>+ y. fi i (x, y) \<partial>\<kappa> x) \<partial>\<mu>)"
  proof(safe intro!: nn_integral_monotone_convergence_SUP[symmetric])
    show "incseq (\<lambda>i x. \<integral>\<^sup>+ y. fi i (x, y) \<partial>\<kappa> x)"
      using le_funD[OF incseq_SucD[OF seq(3)]]
      by(auto intro!: incseq_SucI le_funI nn_integral_mono)
  qed(use disintegration_sets_eq(2)[OF assms(2)] nn_integral_measurable_f'[OF seq(1)] in auto)
  also have "... = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. (\<Squnion>i. fi i (x, y)) \<partial>\<kappa> x \<partial>\<mu>)"
    using kernel_sets seq(1)
    by(auto intro!: nn_integral_cong nn_integral_monotone_convergence_SUP[symmetric] simp: disintegration_space_eq(2)[OF assms(2)] mono_compose seq(3))
  also have "... = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. (\<Squnion> range fi) (x, y) \<partial>\<kappa> x \<partial>\<mu>)"
    by(auto intro!: nn_integral_cong simp: image_image)
  finally show ?case .
qed

lemma(in prob_kernel) nn_integral_fst:
  assumes "f \<in> borel_measurable (X \<Otimes>\<^sub>M Y)" "disintegration \<nu> \<mu>" "sigma_finite_measure \<mu>"
  shows "(\<integral>\<^sup>+z. f z \<partial>\<nu>) = (\<integral>\<^sup>+x. \<integral>\<^sup>+y. f (x,y) \<partial>(\<kappa> x) \<partial>\<mu>)"
proof(rule sigma_finite_measure.sigma_finite_disjoint[OF assms(3)])
  fix A
  assume A:"range A \<subseteq> sets \<mu>" "\<Union> (range A) = space \<mu>" "\<And>i::nat. emeasure \<mu> (A i) \<noteq> \<infinity>" "disjoint_family A"
  then have A': "range (\<lambda>i. A i \<times> space Y) \<subseteq> sets \<nu>" "\<Union> (range (\<lambda>i. A i \<times> space Y)) = space \<nu>" "disjoint_family (\<lambda>i. A i \<times> space Y)"
    by(auto simp: disintegration_sets_eq[OF assms(2)] disjoint_family_on_def disintegration_space_eq[OF assms(2)] space_pair_measure) blast
  show ?thesis (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<integral>\<^sup>+z\<in>\<Union> (range (\<lambda>i. A i \<times> space Y)). f z \<partial>\<nu>)"
      using A'(2) by auto
    also have "... = (\<Sum>i. \<integral>\<^sup>+z\<in> A i \<times> space Y. f z \<partial>\<nu>)"
      using A'(1,3) assms(1) disintegration_sets_eq[OF assms(2)]
      by(auto intro!: nn_integral_disjoint_family)
    also have "... = (\<Sum>i. \<integral>\<^sup>+z. f z \<partial>restrict_space \<nu> (A i \<times> space Y))"
      using A'(1) by(auto intro!: suminf_cong nn_integral_restrict_space[symmetric])
    also have "... = (\<Sum>i. \<integral>\<^sup>+x. \<integral>\<^sup>+y. f (x,y) \<partial>(\<kappa> x) \<partial>restrict_space \<mu> (A i))"
    proof(safe intro!: suminf_cong)
      fix n
      interpret pk: prob_kernel "restrict_space X (A n)" Y \<kappa>
        by(rule restrict_probability_kernel)
      have An:"A n \<inter> space X \<in> sets X" "A n \<inter> space X = A n"
        using A(1) by(auto simp: disintegration_sets_eq[OF assms(2)])
      have f:"f \<in> borel_measurable (restrict_space X (A n) \<Otimes>\<^sub>M Y)"
      proof -
        have 1:"sets (restrict_space X (A n) \<Otimes>\<^sub>M Y) = sets (restrict_space (X \<Otimes>\<^sub>M Y) (A n \<times> space Y))"
          using sets_pair_restrict_space[where Y=Y and B="space Y"] by simp
        show ?thesis
          using assms(1) by(simp add: measurable_cong_sets[OF 1 refl] measurable_restrict_space1)
      qed
      have fin: "finite_measure (restrict_space \<mu> (A n))"
        by (metis A(1) A(3) UNIV_I emeasure_restrict_space finite_measureI image_subset_iff space_restrict_space space_restrict_space2 subset_eq)
      show "(\<integral>\<^sup>+z. f z \<partial>restrict_space \<nu> (A n \<times> space Y)) = (\<integral>\<^sup>+x. \<integral>\<^sup>+y. f (x,y) \<partial>(\<kappa> x) \<partial>restrict_space \<mu> (A n))"
        by(rule pk.nn_integral_fst_finite'[OF f disintegration_restrict_space[OF assms(2) An(1)] fin])
    qed
    also have "... = (\<Sum>i. \<integral>\<^sup>+x\<in>A i. \<integral>\<^sup>+y. f (x,y) \<partial>(\<kappa> x) \<partial>\<mu>)"
      using A(1) by(auto intro!: suminf_cong nn_integral_restrict_space)
    also have "... = (\<integral>\<^sup>+x\<in>\<Union> (range A). \<integral>\<^sup>+y. f (x,y) \<partial>(\<kappa> x) \<partial>\<mu>)"
      using A(1,4) nn_integral_measurable_f'[OF assms(1)] disintegration_sets_eq[OF assms(2)]
      by(auto intro!: nn_integral_disjoint_family[symmetric])
    also have "... = ?rhs"
      using A(2) by simp
    finally show ?thesis .
  qed
qed

lemma(in prob_kernel) integrable_eq1:
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes [measurable]:"f \<in> borel_measurable (X \<Otimes>\<^sub>M Y)"
      and "disintegration \<nu> \<mu>" "sigma_finite_measure \<mu>"
    shows "(\<integral>\<^sup>+ z. ennreal (norm (f z)) \<partial>\<nu>) < \<infinity> \<longleftrightarrow> (\<integral>\<^sup>+x. \<integral>\<^sup>+y. ennreal (norm (f (x,y))) \<partial>(\<kappa> x) \<partial>\<mu>) < \<infinity>"
  by(simp add: nn_integral_fst[OF _ assms(2,3)])

lemma(in prob_kernel) integrable_kernel_integrable:
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes "integrable \<nu> f" "disintegration \<nu> \<mu>" "sigma_finite_measure \<mu>"
  shows "AE x in \<mu>. integrable (\<kappa> x) (\<lambda>y. f (x,y))"
proof -
  have [measurable]:"f \<in> borel_measurable (X \<Otimes>\<^sub>M Y)"
    using integrable_iff_bounded assms(1) disintegration_sets_eq[OF assms(2)] by simp
  show ?thesis
    unfolding integrable_iff_bounded
  proof -
    have 1:"(\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. ennreal (norm (f (x,y))) \<partial>\<kappa> x \<partial>\<mu>) < \<infinity>"
      using assms(1) integrable_eq1[OF _ assms(2,3),of f] by(simp add: integrable_iff_bounded)
    have "AE x in \<mu>. (\<integral>\<^sup>+ y. ennreal (norm (f (x,y))) \<partial>\<kappa> x) \<noteq> \<infinity>"
      by(rule nn_integral_PInf_AE) (use 1 disintegration_sets_eq[OF assms(2)] nn_integral_measurable_f in auto)
    thus "AE x in \<mu>. (\<lambda>y. f (x, y)) \<in> borel_measurable (\<kappa> x) \<and> (\<integral>\<^sup>+ y. ennreal (norm (f (x,y))) \<partial>\<kappa> x) < \<infinity>"
      using top.not_eq_extremum by(fastforce simp: disintegration_space_eq[OF assms(2)])
  qed
qed

lemma(in prob_kernel) integrable_lebesgue_integral_integrable':
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes "integrable \<nu> f" "disintegration \<nu> \<mu>" "sigma_finite_measure \<mu>"
  shows "integrable \<mu> (\<lambda>x. \<integral>y. f (x,y) \<partial>(\<kappa> x))"
  unfolding integrable_iff_bounded
proof
  show "(\<lambda>x. \<integral>y. f (x,y) \<partial>(\<kappa> x)) \<in> borel_measurable \<mu>"
    using disintegration_sets_eq[OF assms(2)] assms(1) integral_measurable_f'[of f]
    by(auto simp: integrable_iff_bounded)
next
  have "(\<integral>\<^sup>+ x. ennreal (norm (\<integral>y. f (x,y) \<partial>(\<kappa> x))) \<partial>\<mu>) \<le> (\<integral>\<^sup>+ x. \<integral>\<^sup>+y. ennreal (norm (f (x,y))) \<partial>(\<kappa> x) \<partial>\<mu>)"
    using integral_norm_bound_ennreal integrable_kernel_integrable[OF assms]
    by(auto intro!: nn_integral_mono_AE)
  also have "... < \<infinity>"
    using integrable_eq1[OF _ assms(2,3),of f] assms(1) disintegration_sets_eq[OF assms(2)]
    by(simp add: integrable_iff_bounded)
  finally show "(\<integral>\<^sup>+ x. ennreal (norm (\<integral>y. f (x,y) \<partial>(\<kappa> x))) \<partial>\<mu>) < \<infinity>" .
qed

lemma(in prob_kernel) integrable_lebesgue_integral_integrable:
  fixes f :: "_ \<Rightarrow>_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes "integrable \<nu> (\<lambda>(x,y). f x y)" "disintegration \<nu> \<mu>" "sigma_finite_measure \<mu>"
  shows "integrable \<mu> (\<lambda>x. \<integral>y. f x y \<partial>(\<kappa> x))"
  using integrable_lebesgue_integral_integrable'[OF assms] by simp

lemma(in prob_kernel) integral_fst:
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes "integrable \<nu> f" "disintegration \<nu> \<mu>" "sigma_finite_measure \<mu>"
  shows "(\<integral>z. f z \<partial>\<nu>) = (\<integral>x. \<integral>y. f (x,y) \<partial>(\<kappa> x) \<partial>\<mu>)"
  using assms(1)
proof induct
  case b:(base A c)
  then have 0:"integrable \<nu> (indicat_real A)"
    by blast
  then have 1[measurable]: "indicat_real A \<in> borel_measurable  (X \<Otimes>\<^sub>M Y)"
    using disintegration_sets_eq[OF assms(2)] by auto
  have eq:"(\<integral>z. indicat_real A z \<partial>\<nu>) = (\<integral>x. \<integral>y. indicat_real A (x,y) \<partial>\<kappa> x \<partial>\<mu>)" (is "?lhs = ?rhs")
  proof -
    have "?lhs = enn2real (\<integral>\<^sup>+ z. ennreal (indicat_real A z) \<partial>\<nu>)"
      by(rule integral_eq_nn_integral) (use b in auto)
    also have "... = enn2real (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. ennreal (indicat_real A (x,y)) \<partial>\<kappa> x \<partial>\<mu>)"
      using nn_integral_fst[OF _ assms(2,3)] b disintegration_sets_eq[OF assms(2)] by auto
    also have "... = enn2real (\<integral>\<^sup>+ x. ennreal (\<integral> y. indicat_real A (x,y) \<partial>\<kappa> x) \<partial>\<mu>)"
    proof -
      have "(\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. ennreal (indicat_real A (x,y)) \<partial>\<kappa> x \<partial>\<mu>) = (\<integral>\<^sup>+ x. ennreal (\<integral> y. indicat_real A (x,y) \<partial>\<kappa> x) \<partial>\<mu>)"
     proof(safe intro!: nn_integral_cong nn_integral_eq_integral)
        fix x
        assume "x \<in> space \<mu>"
        then have "x \<in> space X"
          by(simp add:  disintegration_space_eq[OF assms(2)])
        hence [simp]:"prob_space (\<kappa> x)" "sets (\<kappa> x) = sets Y" "space (\<kappa> x) = space Y"
          by(auto intro!: prob_spaces sets_eq_imp_space_eq kernel_sets)
        have [simp]:"{y. (x, y) \<in> A} \<in> sets Y"
        proof -
          have "{y. (x, y) \<in> A} = (\<lambda>y. (x,y)) -` A \<inter> space Y"
            using b(1)[simplified disintegration_sets_eq[OF assms(2)]]
            by auto
          also have "... \<in> sets Y"
            using b(1)[simplified disintegration_sets_eq[OF assms(2)]] \<open>x \<in> space X\<close>
            by auto
          finally show ?thesis .
        qed
        have [simp]: "(\<lambda>y. indicat_real A (x, y)) = indicat_real {y. (x,y) \<in> A}"
          by (auto simp: indicator_def)
        show "integrable (\<kappa> x) (\<lambda>y. indicat_real A (x, y))"
          using prob_space.emeasure_le_1[of "\<kappa> x" "{y. (x, y) \<in> A}"]
          by(auto simp add: integrable_indicator_iff order_le_less_trans)
      qed simp
      thus ?thesis by simp
    qed
    also have "... = ?rhs"
      using disintegration_sets_eq[OF assms(2)] integral_measurable_f'[OF 1]
      by(auto intro!: integral_eq_nn_integral[symmetric])
    finally show ?thesis .
  qed
  show ?case (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<integral>z. indicat_real A z \<partial>\<nu>) *\<^sub>R c"
      using 0 by auto
    also have "... = (\<integral>x. \<integral>y. indicat_real A (x,y) \<partial>\<kappa> x \<partial>\<mu>) *\<^sub>R c"
      by(simp only: eq)
    also have "... = (\<integral>x. (\<integral>y. indicat_real A (x,y) \<partial>\<kappa> x) *\<^sub>R c \<partial>\<mu>)"
      using integrable_lebesgue_integral_integrable'[OF 0 assms(2,3)]
      by(auto intro!: integral_scaleR_left[symmetric])
    also have "... = ?rhs"
      using integrable_kernel_integrable[OF 0 assms(2,3)] integral_measurable_f'[of " indicat_real A"] integral_measurable_f'[of "\<lambda>z. indicat_real A z *\<^sub>R c"] disintegration_sets_eq[OF assms(2)]
      by(auto intro!: integral_cong_AE)
    finally show ?thesis .
  qed
next
  case fg:(add f g)
  note [measurable] = integrable_lebesgue_integral_integrable'[OF fg(1) assms(2,3)] integrable_lebesgue_integral_integrable'[OF fg(3) assms(2,3)] integrable_lebesgue_integral_integrable'[OF Bochner_Integration.integrable_add[OF fg(1,3)] assms(2,3)]
  show ?case (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<integral>x. (\<integral>y. f (x,y) \<partial>(\<kappa> x)) + (\<integral>y. g (x,y) \<partial>(\<kappa> x)) \<partial>\<mu>)"
      by(simp add: Bochner_Integration.integral_add[OF fg(1,3)] fg Bochner_Integration.integral_add[OF integrable_lebesgue_integral_integrable'[OF fg(1) assms(2,3)] integrable_lebesgue_integral_integrable'[OF fg(3) assms(2,3)]])
    also have "... = ?rhs"
      using integrable_kernel_integrable[OF fg(1) assms(2,3)] integrable_kernel_integrable[OF fg(3) assms(2,3)]
      by(auto intro!: integral_cong_AE)
    finally show ?thesis .
  qed
next
  case (lim f s)
  then have [measurable]: "f \<in> borel_measurable \<nu>" "\<And>i. s i \<in> borel_measurable \<nu>"
    by auto
  show ?case
  proof (rule LIMSEQ_unique)
    show "(\<lambda>i. integral\<^sup>L \<nu> (s i)) \<longlonglongrightarrow> integral\<^sup>L \<nu> f"
    proof (rule integral_dominated_convergence)
      show "integrable \<nu> (\<lambda>x. 2 * norm (f x))"
        using lim(5) by auto
    qed(use lim in auto)
  next
    have "(\<lambda>i. \<integral> x. \<integral> y. s i (x, y) \<partial>(\<kappa> x) \<partial>\<mu>) \<longlonglongrightarrow> \<integral> x. \<integral> y. f (x, y) \<partial>(\<kappa> x) \<partial>\<mu>"
    proof (rule integral_dominated_convergence)
     have "AE x in \<mu>. \<forall>i. integrable (\<kappa> x) (\<lambda>y. s i (x, y))"
        unfolding AE_all_countable using integrable_kernel_integrable[OF lim(1) assms(2,3)] ..
      with AE_space integrable_kernel_integrable[OF lim(5) assms(2,3)]
      show "AE x in \<mu>. (\<lambda>i. \<integral> y. s i (x, y) \<partial>(\<kappa> x)) \<longlonglongrightarrow> \<integral> y. f (x, y) \<partial>(\<kappa> x)"
      proof eventually_elim
        fix x assume x: "x \<in> space \<mu>" and
          s: "\<forall>i. integrable (\<kappa> x) (\<lambda>y. s i (x, y))" and f: "integrable (\<kappa> x) (\<lambda>y. f (x, y))"
        show "(\<lambda>i. \<integral> y. s i (x, y) \<partial>(\<kappa> x)) \<longlonglongrightarrow> \<integral> y. f (x, y) \<partial>(\<kappa> x)"
        proof (rule integral_dominated_convergence)
          show "integrable (\<kappa> x) (\<lambda>y. 2 * norm (f (x, y)))"
             using f by auto
          show "AE xa in (\<kappa> x). (\<lambda>i. s i (x, xa)) \<longlonglongrightarrow> f (x, xa)"
            using x lim(3) kernel_space by (auto simp: space_pair_measure disintegration_space_eq[OF assms(2)])
          show "\<And>i. AE xa in (\<kappa> x). norm (s i (x, xa)) \<le> 2 * norm (f (x, xa))"
            using x lim(4) kernel_space by (auto simp: space_pair_measure disintegration_space_eq[OF assms(2)])
        qed (use x disintegration_sets_eq[OF assms(2)] disintegration_space_eq[OF assms(2)] in auto)
      qed
    next
      show "integrable \<mu> (\<lambda>x. (\<integral> y. 2 * norm (f (x, y)) \<partial>(\<kappa> x)))"
        using integrable_lebesgue_integral_integrable'[OF _ assms(2,3),of "\<lambda>z. 2 * norm (f (fst z, snd z))"] lim(5)
        by auto
    next
      fix i show "AE x in \<mu>. norm (\<integral> y. s i (x, y) \<partial>(\<kappa> x)) \<le> (\<integral> y. 2 * norm (f (x, y)) \<partial>(\<kappa> x))"
        using AE_space integrable_kernel_integrable[OF lim(1) assms(2,3),of i] integrable_kernel_integrable[OF lim(5) assms(2,3)]
      proof eventually_elim
        case sf:(elim x)
       from sf(2) have "norm (\<integral> y. s i (x, y) \<partial>(\<kappa> x)) \<le> (\<integral>\<^sup>+y. norm (s i (x, y)) \<partial>(\<kappa> x))"
          by (rule integral_norm_bound_ennreal)
        also have "\<dots> \<le> (\<integral>\<^sup>+y. 2 * norm (f (x, y)) \<partial>(\<kappa> x))"
          using sf lim kernel_space by (auto intro!: nn_integral_mono simp: space_pair_measure disintegration_space_eq[OF assms(2)])
        also have "\<dots> = (\<integral>y. 2 * norm (f (x, y)) \<partial>(\<kappa> x))"
          using sf by (intro nn_integral_eq_integral) auto
        finally show "norm (\<integral> y. s i (x, y) \<partial>(\<kappa> x)) \<le> (\<integral> y. 2 * norm (f (x, y)) \<partial>(\<kappa> x))"
          by simp
      qed
    qed(use integrable_lebesgue_integral_integrable'[OF lim(1) assms(2,3)] integrable_lebesgue_integral_integrable'[OF lim(5) assms(2,3)] disintegration_sets_eq[OF assms(2)] in auto)
    then show "(\<lambda>i. integral\<^sup>L \<nu> (s i)) \<longlonglongrightarrow> \<integral> x. \<integral> y. f (x, y) \<partial>(\<kappa> x) \<partial>\<mu>"
      using lim by simp
  qed
qed

subsection \<open> Marginal Measure \<close>
definition marginal_measure_on :: "['a measure, 'b measure, ('a \<times> 'b) measure, 'b set] \<Rightarrow> 'a measure" where
"marginal_measure_on X Y \<nu> B = measure_of (space X) (sets X) (\<lambda>A. \<nu> (A \<times> B))"

abbreviation marginal_measure :: "['a measure, 'b measure, ('a \<times> 'b) measure] \<Rightarrow> 'a measure" where
"marginal_measure X Y \<nu> \<equiv> marginal_measure_on X Y \<nu> (space Y)"

lemma space_marginal_measure: "space (marginal_measure_on X Y \<nu> B) = space X"
  and sets_marginal_measure: "sets (marginal_measure_on X Y \<nu> B) = sets X"
  by(simp_all add: marginal_measure_on_def)

lemma emeasure_marginal_measure_on:
  assumes "sets \<nu> = sets (X \<Otimes>\<^sub>M Y)" "B \<in> sets Y" "A \<in> sets X"
  shows "marginal_measure_on X Y \<nu> B A = \<nu> (A \<times> B)"
  unfolding marginal_measure_on_def
proof(rule emeasure_measure_of_sigma)
  show "countably_additive (sets X) (\<lambda>A. emeasure \<nu> (A \<times> B))"
  proof(rule countably_additiveI)
    fix A :: "nat \<Rightarrow> _"
    assume h:"range A \<subseteq> sets X" "disjoint_family A" "\<Union> (range A) \<in> sets X"
    have [simp]: "(\<Union>i. A i \<times> B) = (\<Union> (range A) \<times> B)"
      by blast
    have "range (\<lambda>i. A i \<times> B) \<subseteq> sets \<nu>" "disjoint_family (\<lambda>i. A i \<times> B)"
      using h assms(1,2) by(auto simp: disjoint_family_on_def)
    from suminf_emeasure[OF this]
    show " (\<Sum>i. \<nu> (A i \<times> B)) = \<nu> (\<Union> (range A) \<times> B)"
      by simp
  qed
qed(insert assms, auto simp: positive_def sets.sigma_algebra_axioms)

lemma emeasure_marginal_measure:
  assumes "sets \<nu> = sets (X \<Otimes>\<^sub>M Y)" "A \<in> sets X"
  shows "marginal_measure X Y \<nu> A = \<nu> (A \<times> space Y)"
  using emeasure_marginal_measure_on[OF assms(1) _ assms(2)] by simp

lemma finite_measure_marginal_measure_on_finite:
  assumes "finite_measure \<nu>" "sets \<nu> = sets (X \<Otimes>\<^sub>M Y)" "B \<in> sets Y"
  shows "finite_measure (marginal_measure_on X Y \<nu> B)"
  by (simp add: assms emeasure_marginal_measure_on finite_measure.emeasure_finite finite_measureI space_marginal_measure)

lemma finite_measure_marginal_measure_finite:
  assumes "finite_measure \<nu>" "sets \<nu> = sets (X \<Otimes>\<^sub>M Y)"
  shows "finite_measure (marginal_measure X Y \<nu>)"
  by(rule finite_measure_marginal_measure_on_finite[OF assms sets.top])

lemma marginal_measure_restrict_space:
  assumes "sets \<nu> = sets (X \<Otimes>\<^sub>M Y)" "B \<in> sets Y"
  shows "marginal_measure X (restrict_space Y B) (restrict_space \<nu> (space X \<times> B)) = marginal_measure_on X Y \<nu> B"
proof(rule measure_eqI)
  fix A
  assume "A \<in> sets (marginal_measure X (restrict_space Y B) (restrict_space \<nu> (space X \<times> B)))"
  then have "A \<in> sets X"
    by(simp add: sets_marginal_measure)
  have 1:"sets (restrict_space \<nu> (space X \<times> B)) = sets (X \<Otimes>\<^sub>M restrict_space Y B)"
    by (metis assms(1) restrict_space_space sets_pair_restrict_space sets_restrict_space_cong)
  show "emeasure (marginal_measure X (restrict_space Y B) (restrict_space \<nu> (space X \<times> B))) A = emeasure (marginal_measure_on X Y \<nu> B) A"
    apply(simp add: emeasure_marginal_measure_on[OF assms(1) assms(2) \<open>A \<in> sets X\<close>] emeasure_marginal_measure[OF 1  \<open>A \<in> sets X\<close>])
    apply(simp add: space_restrict_space)
    by (metis Sigma_cong Sigma_mono \<open>A \<in> sets X\<close> assms(1) assms(2) emeasure_restrict_space inf_le1 pair_measureI sets.Int_space_eq2 sets.sets_into_space sets.top)
qed(simp add: sets_marginal_measure)

lemma restrict_space_marginal_measure_on:
  assumes "sets \<nu> = sets (X \<Otimes>\<^sub>M Y)" "B \<in> sets Y" "A \<in> sets X"
  shows "restrict_space (marginal_measure_on X Y \<nu> B) A = marginal_measure_on (restrict_space X A) Y (restrict_space \<nu> (A \<times> space Y)) B"
proof(rule measure_eqI)
  fix A'
  assume "A' \<in> sets (restrict_space (marginal_measure_on X Y \<nu> B) A)"
  then have h:"A' \<in> sets.restricted_space X A"
    by(simp add: sets_marginal_measure sets_restrict_space)
  show "emeasure (restrict_space (marginal_measure_on X Y \<nu> B) A) A' = emeasure (marginal_measure_on (restrict_space X A) Y (restrict_space \<nu> (A \<times> space Y)) B) A'" (is "?lhs = ?rhs")
  proof -
    have 1:"sets (restrict_space \<nu> (A \<times> space Y)) = sets (restrict_space X A \<Otimes>\<^sub>M Y)"
      by (metis assms(1) restrict_space_space sets_pair_restrict_space sets_restrict_space_cong)
    have "?lhs = emeasure (marginal_measure_on X Y \<nu> B) A'"
      using h by(auto intro!: emeasure_restrict_space simp: space_marginal_measure sets_marginal_measure assms)
    also have "... = \<nu> (A' \<times> B)"
      using emeasure_marginal_measure_on[OF assms(1,2),of A'] h assms(3) by auto
    also have "... = restrict_space \<nu> (A \<times> space Y) (A' \<times> B)"
      using h assms sets.sets_into_space
      by(auto intro!: emeasure_restrict_space[symmetric])
    also have "... = ?rhs"
      using emeasure_marginal_measure_on[OF 1 assms(2),simplified sets_restrict_space,OF h] ..
    finally show ?thesis .
  qed
qed(simp add: sets_marginal_measure sets_restrict_space)

lemma restrict_space_marginal_measure:
  assumes "sets \<nu> = sets (X \<Otimes>\<^sub>M Y)" "A \<in> sets X"
  shows "restrict_space (marginal_measure X Y \<nu>) A = marginal_measure (restrict_space X A) Y (restrict_space \<nu> (A \<times> space Y))"
  using restrict_space_marginal_measure_on[OF assms(1) _ assms(2)] by simp

lemma marginal_measure_mono:
  assumes "sets \<nu> = sets (X \<Otimes>\<^sub>M Y)" "A \<in> sets Y" "B \<in> sets Y" "A \<subseteq> B"
  shows "emeasure (marginal_measure_on X Y \<nu> A) \<le> emeasure (marginal_measure_on X Y \<nu> B)"
proof(rule le_funI)
  fix U
  show "emeasure (marginal_measure_on X Y \<nu> A) U \<le> emeasure (marginal_measure_on X Y \<nu> B) U"
  proof -
    have 1:"U \<times> A \<subseteq> U \<times> B" using assms(4) by auto
    show ?thesis
    proof(cases "U \<in> sets X")
      case True
      then show ?thesis
        by (simp add: "1" assms emeasure_marginal_measure_on emeasure_mono) 
    next
      case False
      then show ?thesis
        by (simp add: emeasure_notin_sets sets_marginal_measure)
    qed
  qed
qed

lemma marginal_measure_absolutely_countinuous:
  assumes "sets \<nu> = sets (X \<Otimes>\<^sub>M Y)" "A \<in> sets Y" "B \<in> sets Y" "A \<subseteq> B"
  shows "absolutely_continuous (marginal_measure_on X Y \<nu> B) (marginal_measure_on X Y \<nu> A)"
  using emeasure_marginal_measure[OF assms(1)] assms(2,3) le_funD[OF marginal_measure_mono[OF assms]]
  by(auto intro!: mono_absolutely_continuous simp: sets_marginal_measure)

lemma marginal_measure_absolutely_continuous':
  assumes "sets \<nu> = sets (X \<Otimes>\<^sub>M Y)" "A \<in> sets Y"
  shows "absolutely_continuous (marginal_measure X Y \<nu>) (marginal_measure_on X Y \<nu> A)"
  by(rule marginal_measure_absolutely_countinuous[OF assms sets.top sets.sets_into_space[OF assms(2)]])

subsection \<open> Lemma 14.D.6. \<close>
locale sigma_finite_measure_on_pair =
  fixes X :: "'a measure" and Y :: "'b measure" and \<nu> :: "('a \<times> 'b) measure"
  assumes nu_sets[measurable_cong]: "sets \<nu> = sets (X \<Otimes>\<^sub>M Y)"
      and sigma_finite: "sigma_finite_measure \<nu>"
begin

abbreviation "\<nu>x \<equiv> marginal_measure X Y \<nu>"

end

locale projection_sigma_finite =
  fixes X :: "'a measure" and Y :: "'b measure" and \<nu> :: "('a \<times> 'b) measure"
  assumes nu_sets[measurable_cong]: "sets \<nu> = sets (X \<Otimes>\<^sub>M Y)"
      and marginal_sigma_finite: "sigma_finite_measure (marginal_measure X Y \<nu>)"
begin

sublocale \<nu>x : sigma_finite_measure "marginal_measure X Y \<nu>"
  by(rule marginal_sigma_finite)

lemma \<nu>_sigma_finite: "sigma_finite_measure \<nu>"
proof(rule \<nu>x.sigma_finite[simplified sets_marginal_measure space_marginal_measure])
  fix A :: "nat \<Rightarrow> _"
  assume A: "range A \<subseteq> sets X" "\<Union> (range A) = space X" "\<And>i. marginal_measure X Y \<nu> (A i) \<noteq> \<infinity>"
  define C where "C \<equiv> range (\<lambda>n. A n \<times> space Y)"
  have 1:"C \<subseteq> sets \<nu>" "countable C" "\<Union> C = space \<nu>"
    using nu_sets A(1,2) by(auto simp: C_def sets_eq_imp_space_eq[OF nu_sets] space_pair_measure)
  show "sigma_finite_measure \<nu>"
    unfolding sigma_finite_measure_def
  proof(safe intro!: exI[where x=C,simplified C_def])
    fix n
    assume "\<nu> (A n \<times> space Y) = \<infinity>"
    moreover have "\<nu> (A n \<times> space Y) \<noteq> \<infinity>"
      using A(3)[of n] emeasure_marginal_measure[OF nu_sets,of "A n"] A(1) by auto
    ultimately show False by auto
  qed (use 1 C_def in auto)
qed

sublocale sigma_finite_measure_on_pair
  using \<nu>_sigma_finite by(auto simp: sigma_finite_measure_on_pair_def nu_sets)

definition \<kappa>' :: "'a \<Rightarrow> 'b set \<Rightarrow> ennreal" where
 "\<kappa>' x B \<equiv> RN_deriv \<nu>x (marginal_measure_on X Y \<nu> B) x"
(* Notice that \<kappa>' has the type "'a \<Rightarrow> 'b set \<Rightarrow> ennreal" not "'a \<Rightarrow> 'b measure"
   because \<kappa>' x is not a measure in general. *)

lemma kernel_measurable[measurable]:
 "(\<lambda>x. RN_deriv (marginal_measure X Y \<nu>) (marginal_measure_on X Y \<nu> B) x) \<in> borel_measurable \<nu>x"
  by simp

corollary \<kappa>'_measurable[measurable]:
 "(\<lambda>x. \<kappa>' x B) \<in> borel_measurable X"
  using sets_marginal_measure[of X Y \<nu> "space Y"] by(auto simp: \<kappa>'_def)

lemma kernel_RN_deriv:
  assumes "A \<in> sets X" "B \<in> sets Y"
  shows "\<nu> (A \<times> B) = (\<integral>\<^sup>+x\<in>A. \<kappa>' x B \<partial>\<nu>x)"
  unfolding \<kappa>'_def
proof -
  have "emeasure \<nu> (A \<times> B) = emeasure (density \<nu>x (RN_deriv \<nu>x (marginal_measure_on X Y \<nu> B))) A"
    by (simp add: \<nu>x.density_RN_deriv assms emeasure_marginal_measure_on marginal_measure_absolutely_continuous' nu_sets sets_marginal_measure)
  then show "emeasure \<nu> (A \<times> B) = set_nn_integral \<nu>x A (RN_deriv \<nu>x (marginal_measure_on X Y \<nu> B))"
    by (simp add: assms(1) emeasure_density sets_marginal_measure)
qed

lemma empty_Y_bot:
  assumes "space Y = {}"
  shows "\<nu> = \<bottom>"
proof -
  have "sets \<nu> = {{}}"
    using nu_sets space_empty_iff[of "X \<Otimes>\<^sub>M Y",simplified space_pair_measure] assms
    by simp
  thus ?thesis
    by(simp add: sets_eq_bot)
qed

lemma empty_Y_nux:
  assumes "space Y = {}"
  shows "\<nu>x A = 0"
proof(cases "A \<in> sets X")
  case True
  from emeasure_marginal_measure[OF nu_sets this]
  show ?thesis
    by(simp add: assms)
next
  case False
  with sets_marginal_measure[of X Y \<nu> "space Y"]
  show ?thesis 
    by(auto intro!: emeasure_notin_sets)
qed

lemma kernel_empty0_AE:
  "AE x in \<nu>x. \<kappa>' x {} = 0"
  unfolding \<kappa>'_def by(rule AE_symmetric[OF \<nu>x.RN_deriv_unique]) (auto intro!: measure_eqI simp: sets_marginal_measure emeasure_density emeasure_marginal_measure_on[OF nu_sets])

lemma kernel_Y1_AE:
  "AE x in \<nu>x. \<kappa>' x (space Y) = 1"
  unfolding \<kappa>'_def by(rule AE_symmetric[OF \<nu>x.RN_deriv_unique]) (auto intro!: measure_eqI simp: emeasure_density)

lemma kernel_suminf_AE:
  assumes "disjoint_family F"
      and "\<And>i. F i \<in> sets Y"
    shows "AE x in \<nu>x. (\<Sum>i.  \<kappa>' x (F i)) = \<kappa>' x (\<Union> (range F))"
  unfolding \<kappa>'_def
proof(rule \<nu>x.RN_deriv_unique)
  show "density \<nu>x (\<lambda>x. \<Sum>i. RN_deriv local.\<nu>x (marginal_measure_on X Y \<nu> (F i)) x) = marginal_measure_on X Y \<nu> (\<Union> (range F))"
  proof(rule measure_eqI)
    fix A
    assume [measurable]:"A \<in> sets (density \<nu>x (\<lambda>x. \<Sum>i. RN_deriv \<nu>x (marginal_measure_on X Y \<nu> (F i)) x))"
    then have [measurable]:"A \<in> sets \<nu>x" "A \<in> sets X" by(auto simp: sets_marginal_measure)
    show "(density \<nu>x (\<lambda>x. \<Sum>i. RN_deriv \<nu>x (marginal_measure_on X Y \<nu> (F i)) x)) A = (marginal_measure_on X Y \<nu> (\<Union> (range F))) A"
         (is "?lhs = ?rhs")
    proof -
      have "?lhs = (\<integral>\<^sup>+x\<in>A. (\<Sum>i. RN_deriv \<nu>x (marginal_measure_on X Y \<nu> (F i)) x)\<partial>\<nu>x)"
        by(auto intro!: emeasure_density)
      also have "... = (\<integral>\<^sup>+x. (\<Sum>i. RN_deriv \<nu>x (marginal_measure_on X Y \<nu> (F i)) x * indicator A x)\<partial>\<nu>x)"
        by simp
      also have "... = (\<Sum>i. (\<integral>\<^sup>+x\<in>A. RN_deriv \<nu>x (marginal_measure_on X Y \<nu> (F i)) x \<partial>\<nu>x))"
        by(rule nn_integral_suminf) auto
      also have "... = (\<Sum>i. \<nu> (A \<times> F i))"
        using kernel_RN_deriv[of A "F _"] assms by(auto intro!: suminf_cong simp: \<kappa>'_def)
      also have "... = \<nu> (\<Union>i. A \<times> F i)"
        using assms nu_sets by(fastforce intro!: suminf_emeasure simp: disjoint_family_on_def)
      also have "... = \<nu> (A \<times> (\<Union>i. F i))"
      proof -
        have "(\<Union>i. A \<times> F i) = (A \<times> (\<Union>i. F i))" by blast
        thus ?thesis by simp
      qed
      also have "... = ?rhs"
        using nu_sets assms by(auto intro!: emeasure_marginal_measure_on[symmetric])
      finally show ?thesis .
    qed
  qed(simp add: sets_marginal_measure)
qed auto

lemma kernel_finite_sum_AE:
  assumes "disjoint_family_on F S" "finite S"
      and "\<And>i. i \<in> S \<Longrightarrow> F i \<in> sets Y"
    shows "AE x in \<nu>x. (\<Sum>i\<in>S. \<kappa>' x (F i)) = \<kappa>' x (\<Union>i\<in>S. F i)"
proof -
  consider "S = {}" | "S \<noteq> {}" by auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      by(simp add: kernel_empty0_AE)
  next
    case S:2
    define F' where "F' \<equiv> (\<lambda>n. if n < card S then F (from_nat_into S n) else {})"
    have F'[simp]:"\<And>i. F' i \<in> sets Y"
      using assms(3)
      by (metis F'_def bot.extremum_strict bot_nat_def card.empty from_nat_into sets.empty_sets)
    have F'_disj: "disjoint_family F'"
      unfolding disjoint_family_on_def
    proof safe
      fix m n x
      assume h:"m \<noteq> n" "x \<in> F' m" "x \<in> F' n"
      consider "n < card S" "m < card S" | "n \<ge> card S" | "m \<ge> card S" by arith
      then show "x \<in> {}"
      proof cases
        case 1
        then have "S \<noteq> {}"
          by auto
        with 1 have "from_nat_into S n \<in> S" "from_nat_into S m \<in> S"
          using from_nat_into[of S ] by blast+
        moreover have "from_nat_into S n \<noteq> from_nat_into S m"
          by (metis "1"(1) "1"(2) assms(2) bij_betw_def h(1) lessThan_iff to_nat_on_finite to_nat_on_from_nat_into)
        ultimately show ?thesis
          using h assms(1) 1 by(auto simp: disjoint_family_on_def F'_def)
      qed(use h F'_def in simp_all)
    qed
    have 1:"(\<Sum>i\<in>S. \<kappa>' x (F i)) = (\<Sum>i<card S. \<kappa>' x (F' i))" for x
      unfolding F'_def by auto (metis (no_types, lifting) sum.card_from_nat_into sum.cong)
    have 2: "(\<Union> (range F')) = (\<Union>i\<in>S. F i)"
    proof safe
      fix x n
      assume h:"x \<in> F' n"
      then have "S \<noteq> {}" "n < card S"
        by(auto simp: F'_def) (meson empty_iff)
      with h show "x \<in> \<Union> (F ` S)"
        by(auto intro!: exI[where x="from_nat_into S n"] simp: F'_def from_nat_into \<open>S \<noteq> {}\<close>)
    next
      fix x s
      assume "s \<in> S" "x \<in> F s"
      with bij_betwE[OF to_nat_on_finite[OF assms(2)]]
      show "x \<in> \<Union> (range F')"
        by(auto intro!: exI[where x="to_nat_on S s"] simp: F'_def from_nat_into_to_nat_on[OF countable_finite[OF assms(2)]])
    qed
    have "AE x in \<nu>x. (\<Sum>i<card S. \<kappa>' x (F' i)) = (\<Sum>i. \<kappa>' x (F' i))"
    proof -
      have "AE x in \<nu>x. \<forall>i\<ge>card S. \<kappa>' x (F' i) = 0"
        using kernel_empty0_AE by(auto simp: F'_def)
      hence "AE x in \<nu>x. (\<Sum>i. \<kappa>' x (F' i)) = (\<Sum>i<card S. \<kappa>' x (F' i))"
      proof
        show "AE x in \<nu>x. (\<forall>i\<ge>card S. \<kappa>' x (F' i) = 0) \<longrightarrow> (\<Sum>i. \<kappa>' x (F' i)) = (\<Sum>i<card S. \<kappa>' x (F' i))"
        proof -
          {
            fix x
            assume "\<forall>i\<ge>card S. \<kappa>' x (F' i) = 0"
            then have "(\<Sum>i. \<kappa>' x (F' i)) = (\<Sum>i<card S. \<kappa>' x (F' i))"
              using suminf_offset[of "\<lambda>i. \<kappa>' x (F' i)" "card S"]
              by(auto simp: F'_def)
          }
          thus ?thesis
            by auto
        qed
      qed
      thus ?thesis
        by auto
    qed
    moreover have "AE x in \<nu>x. (\<Sum>i. \<kappa>' x (F' i)) = \<kappa>' x (\<Union> (range F'))"
      using kernel_suminf_AE[OF F'_disj] by simp
    ultimately show ?thesis
      by(auto simp: 1 2)
  qed
qed

lemma kernel_disjoint_sum_AE:
  assumes "B \<in> sets Y" "C \<in> sets Y"
      and "B \<inter> C = {}"
    shows "AE x in \<nu>x. \<kappa>' x (B \<union> C) = \<kappa>' x B + \<kappa>' x C"
proof -
  define F where "F \<equiv> \<lambda>b. if b then B else C"
  have [simp]:"disjoint_family F" "\<And>i. F i \<in> sets Y" "\<And>x. (\<Sum>i\<in>UNIV. \<kappa>' x (F i)) = \<kappa>' x B + \<kappa>' x C" "\<Union> (range F) = B \<union> C"
    using assms by(auto simp: F_def disjoint_family_on_def comm_monoid_add_class.sum.Int_Diff[of UNIV _ "{True}"])
  show ?thesis
    using kernel_finite_sum_AE[of F UNIV] by auto
qed

lemma kernel_mono_AE:
  assumes "B \<in> sets Y" "C \<in> sets Y"
      and "B \<subseteq> C"
    shows "AE x in \<nu>x. \<kappa>' x B \<le> \<kappa>' x C"
proof -
  have 1: "B \<union> (C - B) = C" using assms(3) by auto
  have "AE x in \<nu>x. \<kappa>' x C = \<kappa>' x B + \<kappa>' x (C - B)"
    using assms by(auto intro!: kernel_disjoint_sum_AE[of B "C - B",simplified 1])
  thus ?thesis
    by auto
qed

lemma kernel_incseq_AE:
  assumes "range B \<subseteq> sets Y" "incseq B"
  shows  "AE x in \<nu>x. incseq (\<lambda>n. \<kappa>' x (B n))"
  using assms(1) by(auto simp: incseq_Suc_iff AE_all_countable intro!: kernel_mono_AE[OF _ _ incseq_SucD[OF assms(2)]])

lemma kernel_decseq_AE:
  assumes "range B \<subseteq> sets Y" "decseq B"
  shows  "AE x in \<nu>x. decseq (\<lambda>n. \<kappa>' x (B n))"
  using assms(1) by(auto simp: decseq_Suc_iff AE_all_countable intro!: kernel_mono_AE[OF _ _ decseq_SucD[OF assms(2)]])

corollary kernel_01_AE:
  assumes "B \<in> sets Y"
  shows "AE x in \<nu>x. 0 \<le> \<kappa>' x B \<and> \<kappa>' x B \<le> 1"
proof -
  have "{} \<subseteq> B" "B \<subseteq> space Y"
    using assms sets.sets_into_space by auto
  from kernel_empty0_AE kernel_Y1_AE kernel_mono_AE[OF _ _ this(1)] kernel_mono_AE[OF _ _ this(2)] assms
  show ?thesis
    by auto
qed

lemma kernel_get_0: "0 \<le> \<kappa>' x B"
  by simp

lemma kernel_le1_AE:
  assumes "B \<in> sets Y"
  shows "AE x in \<nu>x. \<kappa>' x B \<le> 1"
  using kernel_01_AE[OF assms] by auto

corollary kernel_n_infty:
  assumes "B \<in> sets Y"
  shows "AE x in \<nu>x. \<kappa>' x B \<noteq> \<top>"
  by(rule AE_mp[OF kernel_le1_AE[OF assms]],standard) (auto simp: neq_top_trans[OF ennreal_one_neq_top])

corollary kernel_le_infty:
  assumes "B \<in> sets Y"
  shows "AE x in \<nu>x. \<kappa>' x B < \<top>"
  using kernel_n_infty[OF assms] by (simp add: top.not_eq_extremum)

lemma kernel_SUP_incseq:
  assumes "range B \<subseteq> sets Y" "incseq B"
  shows "AE x in \<nu>x. \<kappa>' x (\<Union> (range B)) = (\<Squnion>n. \<kappa>' x (B n))"
proof -
  define Bn where "Bn \<equiv> (\<lambda>n. if n = 0 then {} else B (n - 1))"
  have "incseq Bn"
    using assms(2) by(auto simp: Bn_def incseq_def)
  define Cn where "Cn \<equiv> (\<lambda>n. Bn (Suc n) - Bn n)"
  have Cn_simp: "Cn 0 = B 0" "Cn (Suc n) = B (Suc n) - B n" for n
    by(simp_all add: Cn_def Bn_def)
  have Cn_sets:"Cn n \<in> sets Y" for n
    using assms(1) by(induction n) (auto simp: Cn_simp)
  have Cn_disj: "disjoint_family Cn"
    by(auto intro!: disjoint_family_Suc[OF ] incseq_SucD[OF \<open>incseq Bn\<close>] simp: Cn_def)
  have Cn_un: "(\<Union>k<Suc n. Cn k) = B n" for n
    using incseq_SucD[OF assms(2)]
    by (induction n) (auto simp: Cn_simp lessThan_Suc sup_commute)
  have Cn_sum_Bn:"AE x in \<nu>x. \<forall>n. (\<Sum>i<Suc n. \<kappa>' x (Cn i)) = \<kappa>' x (B n)"
    unfolding AE_all_countable
    using kernel_finite_sum_AE[OF disjoint_family_on_mono[OF _ Cn_disj],of "{..<Suc _}"] Cn_sets
    by(auto simp: Cn_un)
  have Cn_bn_un: "(\<Union> (range B)) = (\<Union> (range Cn))" (is "?lhs = ?rhs")
  proof safe
    fix n x
    assume "x \<in> B n"
    with Cn_un[of n] show "x \<in> \<Union> (range Cn)"
      by blast
  next
    fix n x
    assume "x \<in> Cn n"
    then show "x \<in> \<Union> (range B)"
      by(cases n,auto simp: Cn_simp)
  qed
  hence "AE x in \<nu>x. \<kappa>' x (\<Union> (range B)) =  \<kappa>' x (\<Union> (range Cn))"
    by simp
  moreover have "AE x in \<nu>x. \<kappa>' x (\<Union> (range Cn)) = (\<Sum>n. \<kappa>' x (Cn n))"
    by(rule AE_symmetric[OF kernel_suminf_AE[OF Cn_disj]]) (use Cn_def Bn_def assms(1) in auto)
  moreover have "AE x in \<nu>x. (\<Sum>n. \<kappa>' x (Cn n)) = (\<Squnion>n. \<Sum>i<n. \<kappa>' x (Cn i))"
    by(auto simp: suminf_eq_SUP)
  moreover have "AE x in \<nu>x. (\<Squnion>n. \<Sum>i<n. \<kappa>' x (Cn i)) = (\<Squnion>n. \<Sum>i<Suc n. \<kappa>' x (Cn i))"
  proof(intro AE_I2 antisym)
    fix x
    show "(\<Squnion>n. \<Sum>i<n. \<kappa>' x (Cn i)) \<le> (\<Squnion>n. \<Sum>i<Suc n. \<kappa>' x (Cn i))"
      by(rule complete_lattice_class.Sup_mono, auto, use le_iff_add  in blast)
  next
    fix x
    show "(\<Squnion>n. \<Sum>i<n. \<kappa>' x (Cn i)) \<ge> (\<Squnion>n. \<Sum>i<Suc n. \<kappa>' x (Cn i))"
      by(rule complete_lattice_class.Sup_mono) blast
  qed
  moreover have "AE x in \<nu>x. (\<Squnion>n. \<Sum>i<Suc n. \<kappa>' x (Cn i)) = (\<Squnion>n. \<kappa>' x (B n))"
    by(rule AE_mp[OF Cn_sum_Bn]) (standard+, auto)
  ultimately show ?thesis by auto
qed

lemma kernel_lim_incseq:
  assumes "range B \<subseteq> sets Y" "incseq B"
  shows "AE x in \<nu>x. (\<lambda>n. \<kappa>' x (B n)) \<longlonglongrightarrow> \<kappa>' x (\<Union> (range B))"
  by(rule AE_mp[OF AE_conjI[OF kernel_SUP_incseq[OF assms] kernel_incseq_AE[OF assms]]],auto simp: LIMSEQ_SUP)

lemma kernel_INF_decseq:
  assumes "range B \<subseteq> sets Y" "decseq B"
  shows "AE x in \<nu>x. \<kappa>' x (\<Inter> (range B)) = (\<Sqinter>n. \<kappa>' x (B n))"
proof -
  define C where "C \<equiv> (\<lambda>k. space Y - B k)"
  have C:"range C \<subseteq> sets Y" "incseq C"
    using assms by(auto simp: C_def decseq_def incseq_def)
  have eq1: "AE x in \<nu>x. 1 - \<kappa>' x (\<Inter> (range B)) = \<kappa>' x (\<Union> (range C))"
  proof -
    have "AE x in \<nu>x. \<kappa>' x (\<Union> (range C)) + \<kappa>' x (\<Inter> (range B)) - \<kappa>' x (\<Inter> (range B)) = \<kappa>' x (\<Union> (range C))"
      using assms(1) kernel_n_infty[of "\<Inter> (range B)"] by auto
    moreover have "AE x in \<nu>x. \<kappa>' x (\<Union> (range C)) + \<kappa>' x (\<Inter> (range B)) = 1"
    proof -
      have [simp]:"(\<Union> (range C)) \<union> (\<Inter> (range B)) = space Y" "(\<Union> (range C)) \<inter> (\<Inter> (range B)) = {}"
        by(auto simp: C_def) (meson assms(1) range_subsetD sets.sets_into_space subsetD)
      from kernel_disjoint_sum_AE[OF _ _ this(2)] C(1) assms(1) kernel_Y1_AE
      show ?thesis by auto
    qed
    ultimately show ?thesis
      by auto
  qed
  have eq2: "AE x in \<nu>x. \<kappa>' x (\<Union> (range C)) = (\<Squnion>n. \<kappa>' x (C n))"
    using kernel_SUP_incseq[OF C] by auto
  have eq3: "AE x in \<nu>x. (\<Squnion>n. \<kappa>' x (C n)) = (\<Squnion>n. 1 -  \<kappa>' x (B n))"
  proof -
    have "AE x in \<nu>x. \<forall>n. \<kappa>' x (C n) = 1 -  \<kappa>' x (B n)"
      unfolding AE_all_countable
    proof safe
      fix n
      have "AE x in \<nu>x. \<kappa>' x (C n) + \<kappa>' x (B n) - \<kappa>' x (B n) = \<kappa>' x (C n)"
        using assms(1) kernel_n_infty[of "B n"] by auto
      moreover have "AE x in \<nu>x. \<kappa>' x (C n) + \<kappa>' x (B n) = 1"
      proof -
        have [simp]: "C n \<union> B n = space Y" "C n \<inter> B n = {}"
          by(auto simp: C_def) (meson assms(1) range_subsetD sets.sets_into_space subsetD)
        thus ?thesis
          using kernel_disjoint_sum_AE[of "C n" "B n"] C(1) assms(1) kernel_Y1_AE by fastforce
      qed
      ultimately show "AE x in \<nu>x. \<kappa>' x (C n) = 1 - \<kappa>' x (B n)" by auto
    qed
    thus ?thesis by auto
  qed
  have [simp]: "(\<Squnion>n. 1 -  \<kappa>' x (B n)) = 1 - (\<Sqinter>n. \<kappa>' x (B n))" for x
    by(auto simp: ennreal_INF_const_minus)
  have eq: "AE x in \<nu>x. 1 - \<kappa>' x (\<Inter> (range B)) = 1 - (\<Sqinter>n. \<kappa>' x (B n))"
    using eq1 eq2 eq3 by auto
  have le1: "AE x in \<nu>x. (\<Sqinter>n. \<kappa>' x (B n)) \<le> 1"
  proof -
    have "AE x in \<nu>x. \<forall>n. \<kappa>' x (B n) \<le> 1"
      using assms(1) by(auto intro!: kernel_le1_AE simp: AE_all_countable)
    thus ?thesis
      by (auto simp: INF_lower2)
  qed 
  show ?thesis
    by(rule AE_mp[OF AE_conjI[OF AE_conjI[OF eq le1] kernel_le1_AE[of "\<Inter> (range B)"]]])
      (insert assms(1),auto simp: ennreal_minus_cancel[OF ennreal_one_neq_top])
qed

lemma kernel_lim_decseq:
  assumes "range B \<subseteq> sets Y" "decseq B"
  shows "AE x in \<nu>x. (\<lambda>n. \<kappa>' x (B n)) \<longlonglongrightarrow> \<kappa>' x (\<Inter> (range B))"
  by(rule AE_mp[OF AE_conjI[OF kernel_INF_decseq[OF assms] kernel_decseq_AE[OF assms]]],standard,auto simp: LIMSEQ_INF)

end

subsection \<open> Theorem 14.D.10. (Measure Disintegration Theorem) \<close>
locale projection_sigma_finite_standard = projection_sigma_finite + standard_borel_ne Y
begin

theorem measure_disintegration:
    "\<exists>\<kappa>. prob_kernel X Y \<kappa> \<and> measure_kernel.disintegration X Y \<kappa> \<nu> \<nu>x \<and>
       (\<forall>\<kappa>''. prob_kernel X Y \<kappa>'' \<longrightarrow> measure_kernel.disintegration X Y \<kappa>'' \<nu> \<nu>x \<longrightarrow> (AE x in \<nu>x. \<kappa> x = \<kappa>'' x))"
proof -
  have *:"\<exists>\<kappa>. prob_kernel X (borel :: real measure) \<kappa> \<and> measure_kernel.disintegration X borel \<kappa> \<nu> (marginal_measure X borel \<nu>) \<and>
             (\<forall>\<kappa>''. prob_kernel X borel \<kappa>'' \<longrightarrow> measure_kernel.disintegration X borel \<kappa>'' \<nu> (marginal_measure X borel \<nu>) \<longrightarrow> (AE x in (marginal_measure X borel \<nu>). \<kappa> x = \<kappa>'' x))"
        if nu_sets': "sets \<nu> = sets (X \<Otimes>\<^sub>M borel)" and marginal_sigma_finite': "sigma_finite_measure (marginal_measure X borel \<nu>)" for X :: "'a measure" and \<nu>

  proof -
    interpret r: projection_sigma_finite X borel \<nu>
      using that by(auto simp: projection_sigma_finite_def)
    define \<phi> :: "'a \<Rightarrow> rat \<Rightarrow> real"
      where "\<phi> \<equiv> (\<lambda>x r. enn2real (r.\<kappa>' x {..real_of_rat r}))"
    have as1: "AE x in r.\<nu>x. \<forall>r s. r \<le> s \<longrightarrow> \<phi> x r \<le> \<phi> x s"
      unfolding AE_all_countable
    proof(safe intro!: AE_impI)
      fix r s :: rat
      assume "r \<le> s"
      have "AE x in r.\<nu>x. r.\<kappa>' x {..real_of_rat k} < top" for k
        using atMost_borel r.kernel_le_infty by blast
      from this[of s] r.kernel_mono_AE[of "{..real_of_rat r}" "{..real_of_rat s}"] \<open>r \<le> s\<close>
      show "AE x in r.\<nu>x. \<phi> x r \<le> \<phi> x s"
        by(auto simp: \<phi>_def of_rat_less_eq enn2real_mono)
    qed
    have as2: "AE x in r.\<nu>x. \<forall>r. (\<lambda>n. \<phi> x (r + 1 / rat_of_nat (Suc n))) \<longlonglongrightarrow> \<phi> x r"
      unfolding AE_all_countable
    proof safe
      fix r
      have 1:"(\<Inter>n. {..real_of_rat (r + 1 / rat_of_nat (Suc n))}) = {..real_of_rat r}"
      proof safe
        fix x
        assume h:" x \<in> (\<Inter>n. {..real_of_rat (r + 1 / rat_of_nat (Suc n))})"
        show "x \<le> real_of_rat r"
        proof(rule ccontr)
          assume "\<not> x \<le> real_of_rat r"
          then have "0 < x - real_of_rat r" by simp
          then obtain n where "(1 / (real (Suc n))) < x - real_of_rat r"
            using nat_approx_posE by blast
          hence "real_of_rat (r + 1 / (1 + rat_of_nat n)) < x"
            by (simp add: of_rat_add of_rat_divide)
          with h show False
            using linorder_not_le by fastforce
        qed
      next
        fix x n
        assume "x \<le> real_of_rat r"
        then  show " x \<le> real_of_rat (r + 1 / rat_of_nat (Suc n))"
          by (metis le_add_same_cancel1 of_nat_0_le_iff of_rat_less_eq order_trans zero_le_divide_1_iff)
      qed
      have "AE x in r.\<nu>x. (\<lambda>n. r.\<kappa>' x {..real_of_rat (r + 1 / rat_of_nat (Suc n))}) \<longlonglongrightarrow> r.\<kappa>' x {..real_of_rat r}"
        unfolding 1[symmetric] by(rule r.kernel_lim_decseq) (auto simp: decseq_Suc_iff of_rat_less_eq frac_le)
      from AE_conjI[OF r.kernel_le_infty[of "{..real_of_rat r}",simplified] this] tendsto_enn2real
      show "AE x in r.\<nu>x. (\<lambda>n. \<phi> x (r + 1 / (rat_of_nat (Suc n)))) \<longlonglongrightarrow> \<phi> x r"
        by(auto simp: \<phi>_def)
    qed

    have as3: "AE x in r.\<nu>x. (\<phi> x \<longlongrightarrow> 0) at_bot"
    proof -
      have 0: "range (\<lambda>n. {..- real n}) \<subseteq> sets borel" "decseq (\<lambda>n. {..- real n})"
        by(auto simp: decseq_def)
      show ?thesis
      proof(safe intro!: AE_I2[THEN AE_mp[OF AE_conjI[OF r.kernel_empty0_AE AE_conjI[OF r.kernel_lim_decseq[OF 0] as1]]]])
        fix x
        assume h: "r.\<kappa>' x {} = 0" " (\<lambda>n. r.\<kappa>' x {..- real n}) \<longlonglongrightarrow> r.\<kappa>' x (\<Inter>n. {..- real n})" "\<forall>r s. r \<le> s \<longrightarrow> \<phi> x r \<le> \<phi> x s"
        have [simp]: "(\<Inter>n. {..- real n}) = {}" by auto (meson le_minus_iff linorder_not_less reals_Archimedean2)
        show "(\<phi> x \<longlongrightarrow> 0) at_bot"
        proof(rule decreasing_tendsto)
          fix r :: real
          assume "0 < r"
          with h(2) eventually_sequentially
          obtain N where N:"\<And>n. n \<ge> N \<Longrightarrow> r.\<kappa>' x {..- real n} < r"
            by(fastforce simp: order_tendsto_iff h(1))
          show "\<forall>\<^sub>F q in at_bot. \<phi> x q < r"
            unfolding eventually_at_bot_linorder
          proof(safe intro!: exI[where x="- rat_of_nat N"])
            fix q
            assume "q \<le> - rat_of_nat N"
            with h(3) have "\<phi> x q \<le> \<phi> x (- rat_of_nat N)" by simp
            also have "... < r"
              by(auto simp: \<phi>_def) (metis N[OF order_refl] \<open>0 < r\<close> enn2real_less_iff enn2real_top of_rat_minus of_rat_of_nat_eq top.not_eq_extremum)
            finally show "\<phi> x q < r" .
          qed
        qed(simp add: \<phi>_def)
      qed
    qed

    have as4: "AE x in r.\<nu>x. (\<phi> x \<longlongrightarrow> 1) at_top"
    proof -
      have 0: "range (\<lambda>n. {..real n}) \<subseteq> sets borel" "incseq (\<lambda>n. {..real n})"
        by(auto simp: incseq_def)
      have [simp]: "(\<Union>n. {..real n}) = UNIV" by (auto simp: real_arch_simple)
      have 1: "AE x in r.\<nu>x. \<forall>n. r.\<kappa>' x {..real n} \<le> 1" "AE x in r.\<nu>x. \<forall>q. r.\<kappa>' x {..real_of_rat q} \<le> 1"
        by(auto simp: AE_all_countable intro!: r.kernel_le1_AE)
      show ?thesis
      proof(safe intro!: AE_I2[THEN AE_mp[OF AE_conjI[OF AE_conjI[OF 1] AE_conjI[OF r.kernel_Y1_AE AE_conjI[OF r.kernel_lim_incseq[OF 0] as1]]],simplified]])
        fix x
        assume h: "\<forall>q. r.\<kappa>' x {..real_of_rat q} \<le> 1" "\<forall>n. r.\<kappa>' x {..real n} \<le> 1"
                  "(\<lambda>n. r.\<kappa>' x {..real n}) \<longlonglongrightarrow> r.\<kappa>' x UNIV" "\<forall>r s. r \<le> s \<longrightarrow> \<phi> x r \<le> \<phi> x s" "r.\<kappa>' x UNIV = 1"
        then have h3: "(\<lambda>n. r.\<kappa>' x {..real n}) \<longlonglongrightarrow> 1"
          by auto
        show "(\<phi> x \<longlongrightarrow> 1) at_top"
        proof(rule increasing_tendsto)
          fix r :: real
          assume "r < 1"
          with h3 eventually_sequentially
          obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> r < r.\<kappa>' x {..real n}"
            by(fastforce simp: order_tendsto_iff)
          show "\<forall>\<^sub>F n in at_top. r < \<phi> x n"
            unfolding eventually_at_top_linorder
          proof(safe intro!: exI[where x="rat_of_nat N"])
            fix q
            assume "rat_of_nat N \<le> q"
            have "r < \<phi> x (rat_of_nat N)"
              by(auto simp: \<phi>_def) (metis N[OF order_refl] h(2) enn2real_1 enn2real_ennreal enn2real_positive_iff ennreal_cases ennreal_leI linorder_not_less zero_less_one)
            also have "... \<le> \<phi> x q"
              using h(4) \<open>rat_of_nat N \<le> q\<close> by simp
            finally show "r < \<phi> x q" .
          qed
        qed(use h(1) enn2real_leI \<phi>_def in auto)
      qed
    qed
    from AE_E3[OF AE_conjI[OF as1 AE_conjI[OF as2 AE_conjI[OF as3 as4]]],simplified space_marginal_measure]
    obtain N where N: "N \<in> null_sets r.\<nu>x" "\<And>x r s. x \<in> space X - N \<Longrightarrow> r \<le> s \<Longrightarrow> \<phi> x r \<le> \<phi> x s"
                      "\<And>x r. x \<in> space X - N \<Longrightarrow>  (\<lambda>n. \<phi> x (r + 1 / rat_of_nat (Suc n))) \<longlonglongrightarrow> \<phi> x r"
                      "\<And>x. x \<in> space X - N \<Longrightarrow> (\<phi> x \<longlongrightarrow> 0) at_bot" "\<And>x. x \<in> space X - N \<Longrightarrow> (\<phi> x \<longlongrightarrow> 1) at_top"
      by metis
    define F where "F \<equiv> (\<lambda>x y. indicat_real (space X - N) x * Inf {\<phi> x r |r. y \<le> real_of_rat r} + indicat_real N x * indicat_real {0..} y)"
    have [simp]: "{\<phi> x r |r. y \<le> real_of_rat r} \<noteq> {}" for x y
      by auto (meson gt_ex less_eq_real_def of_rat_dense)
    have [simp]: "bdd_below {\<phi> x r |r. y \<le> real_of_rat r}" if "x \<in> space X - N" for x y
    proof -
      obtain r' where "real_of_rat r' \<le> y"
        by (metis less_eq_real_def lt_ex of_rat_dense)
      from order_trans[OF this] of_rat_less_eq show ?thesis
        by(auto intro!: bdd_belowI[of _ "\<phi> x r'"] N(2)[OF that])
    qed
    have Feq: "F x (real_of_rat r) = \<phi> x r" if "x \<in> space X - N" for x r
      using that N(2)[OF that] by(auto intro!: cInf_eq_minimum simp: of_rat_less_eq F_def)
    have Fmono: "mono (F x)" if "x \<in> space X" for x
      by(auto simp: F_def mono_def indicator_def intro!: cInf_superset_mono) (meson gt_ex less_eq_real_def of_rat_dense)

    have F1: "(F x \<longlongrightarrow> 0) at_bot" if "x \<in> space X" for x
    proof(cases "x \<in> N")
      case True
      with that show ?thesis
        by(auto simp: F_def tendsto_iff eventually_at_bot_dense indicator_def intro!: exI[where x=0])
    next
      case False
      with qlim_eq_lim_mono_at_bot[OF Fmono[OF that] N(4)] Feq that
      show ?thesis by auto
    qed
    have F2: "(F x \<longlongrightarrow> 1) at_top" if "x \<in> space X" for x
    proof(cases "x \<in> N")
      case True
      with that show ?thesis
        by(auto simp: F_def tendsto_iff eventually_at_top_dense indicator_def intro!: exI[where x=0])
    next
      case False
      with qlim_eq_lim_mono_at_top[OF Fmono[OF that] N(5)] Feq that
      show ?thesis by auto
    qed
    have F3: "continuous (at_right a) (F x)" if "x \<in> space X" for x a
    proof(cases "x \<in> N")
      case x:True
      {
        fix e :: real
        assume e:"0 < e"
        consider "a \<ge> 0" | "a < 0" by fastforce
        then have "\<exists>d>0. indicat_real {0..} (a + d) - indicat_real {0..} a < e"
        proof cases
          case 1
          with e show ?thesis
            by(auto intro!: exI[where x=1])
        next
          case 2
          then obtain b where "b > 0" "a + b < 0"
            by (metis add_less_same_cancel2 of_rat_dense real_add_less_0_iff)
          with e 2 show ?thesis
            by(auto intro!: exI[where x=b])
        qed
      }
      with x show ?thesis
        unfolding continuous_at_right_real_increasing[of "F x",OF monoD[OF Fmono[OF that]],simplified]
        by(auto simp: F_def)
    next
      case x:False
      {
        fix e :: real
        assume e: "e > 0"
        have "\<exists>k. a \<le> real_of_rat k \<and> \<Sqinter> {\<phi> x r |r. a \<le> real_of_rat r} +  e / 2 \<ge> \<phi> x k"
        proof(rule ccontr)
          assume "\<nexists>k. a \<le> real_of_rat k \<and> \<phi> x k \<le> \<Sqinter> {\<phi> x r |r. a \<le> real_of_rat r} + e / 2"
          then have cont: "\<And>k. a \<le> real_of_rat k \<Longrightarrow> \<phi> x k - e / 2 > \<Sqinter> {\<phi> x r |r. a \<le> real_of_rat r}"
            by auto
          hence "a \<le> real_of_rat k \<Longrightarrow> \<exists>r. a \<le> real_of_rat r \<and> \<phi> x r  < \<phi> x k - e / 2" for k
            using cont \<open>x \<in> space X\<close> x cInf_less_iff [of "{\<phi> x r |r. a \<le> real_of_rat r}" "\<phi> x k - e / 2"]
            by auto
          then obtain r where r:"\<And>k. a \<le> real_of_rat k \<Longrightarrow> a \<le> real_of_rat (r k)" "\<And>k. a \<le> real_of_rat k \<Longrightarrow> \<phi> x (r k) < \<phi> x k - e / 2"
            by metis
          obtain k where k:"a \<le> real_of_rat k"
            by (meson gt_ex less_eq_real_def of_rat_dense)
          define f where "f \<equiv> rec_nat k (\<lambda>n fn. r fn)"
          have f_simp: "f 0 = k" "f (Suc n) = r (f n)" for n
            by(auto simp: f_def)
          have f1: "a \<le> real_of_rat (f n)" for n
            using r(1) k by(induction n) (auto simp: f_simp)
          have f2: "n \<ge> 1 \<Longrightarrow> \<phi> x (f n) < \<phi> x k - real n * e / 2" for n
          proof(induction n)
            case ih:(Suc n)
            consider "n = 0" | "n \<ge> 1" by fastforce
            then show ?case
            proof cases
              case 1
              with r k show ?thesis
                by(simp add: f_simp)
            next
              case 2
              show ?thesis
                using less_trans[OF r(2)[OF f1[of n]] diff_strict_right_mono[OF ih(1)[OF 2],of "e / 2"]]
                by(auto simp: f_simp ring_distribs(2) add_divide_distrib)
            qed
          qed simp
          have "\<not> bdd_below {\<phi> x r |r. a \<le> real_of_rat r}"
            unfolding bdd_below_def
          proof safe
            fix M
            obtain n where "\<phi> x k - M < real n * e / 2"
              using f2 e reals_Archimedean3 by fastforce
            then have "\<phi> x k - M < real (Suc n) * e / 2"
              using divide_strict_right_mono pos_divide_less_eq e by fastforce
            thus "Ball {\<phi> x r |r. a \<le> real_of_rat r} ((\<le>) M) \<Longrightarrow> False"
              using f2[of "Suc n"] f1[of "Suc n"] by(auto intro!: exI[where x="\<phi> x (f (Suc n))"])
          qed
          with that x show False
            by simp
        qed
        then obtain k where k: "a \<le> real_of_rat k" "\<Sqinter> {\<phi> x r |r. a \<le> real_of_rat r} +  e / 2 \<ge> \<phi> x k"
          by auto
        obtain no where no:"\<And>n. n\<ge>no \<Longrightarrow> (\<phi> x (k + 1 / rat_of_nat (Suc n))) - (\<phi> x k) < e / 2"
          using \<open>x \<in> space X\<close> x metric_LIMSEQ_D[OF N(3)[of x k],of "e/2"] e N(2)[of x k "k + 1 / rat_of_nat (Suc _)"]
          by(auto simp: dist_real_def)
        have "\<exists>d>0. \<Sqinter> {\<phi> x r |r. a + d \<le> real_of_rat r} - \<Sqinter> {\<phi> x r |r. a \<le> real_of_rat r} < e"
        proof(safe intro!: exI[where x="real_of_rat (1 / rat_of_nat (Suc no))"])
          have "\<phi> x (k + 1 / rat_of_nat (Suc no)) - e < \<phi> x k - e / 2"
            using no[OF order_refl] by simp
          also have "... \<le> \<Sqinter> {\<phi> x r |r. a \<le> real_of_rat r}"
            using k by simp
          finally have "\<phi> x (k + 1 / rat_of_nat (Suc no)) - \<Sqinter> {\<phi> x r |r. a \<le> real_of_rat r} < e" by simp
          moreover have "\<Sqinter> {\<phi> x r |r. a + real_of_rat (1 / (1 + rat_of_nat no)) \<le> real_of_rat r} \<le> \<phi> x (k + 1 / rat_of_nat (Suc no))"
            using k that x by(auto intro!: cInf_lower simp: of_rat_add)
          ultimately show "\<Sqinter> {\<phi> x r |r. a + real_of_rat (1 / (rat_of_nat (Suc no))) \<le> real_of_rat r} - \<Sqinter> {\<phi> x r |r. a \<le> real_of_rat r} < e"
            by simp
        qed simp
      }
      with that x show ?thesis
        unfolding continuous_at_right_real_increasing[of "F x",OF monoD[OF Fmono[OF that]],simplified]
        by(auto simp: F_def)
    qed

    define \<kappa> where "\<kappa> \<equiv> (\<lambda>x. interval_measure (F x))"

    have \<kappa>: "\<And>x. x \<in> space X \<Longrightarrow> \<kappa> x UNIV = 1"
            "\<And>x r. x \<in> space X \<Longrightarrow> \<kappa> x {..r} = ennreal (F x r)"
 and[simp]: "\<And>x. sets (\<kappa> x) = sets borel" "\<And>x. space (\<kappa> x) = UNIV"
      using emeasure_interval_measure_Iic[OF _ F3 F1] interval_measure_UNIV[OF _ F3 F1 F2] Fmono
      by(auto simp: mono_def \<kappa>_def)
    
    interpret \<kappa>: prob_kernel X borel \<kappa>
      unfolding prob_kernel_def'
    proof(rule measurable_prob_algebra_generated[OF _ atMostq_Int_stable,of _ UNIV])
      show "\<And>a. a \<in> space X \<Longrightarrow> prob_space (\<kappa> a)"
        by(auto intro!: prob_spaceI \<kappa>(1))
    next
      fix A
      assume "A \<in> {{..r} |r::real. r \<in> \<rat>}"
      then obtain r where r: "A = {..real_of_rat r}"
        using Rats_cases by blast
      have "(\<lambda>x. ennreal (indicat_real (space X - N) x * \<phi> x r + indicat_real N x * indicat_real {0..} (real_of_rat r))) \<in> borel_measurable X" 
      proof -
        have "N \<in> sets X"
          using null_setsD2[OF N(1)] by(auto simp: sets_marginal_measure)
        thus ?thesis by(auto simp: \<phi>_def)
      qed
      moreover have "indicat_real (space X - N) x * \<phi> x r + indicat_real N x * indicat_real {0..} (real_of_rat r) = emeasure (\<kappa> x) A" if "x \<in> space X" for x
        using Feq[of x r] \<kappa>(2)[OF that,of "real_of_rat r"]
        by(cases "x \<in> N") (auto simp: r indicator_def F_def)
      ultimately show " (\<lambda>x. emeasure (\<kappa> x) A) \<in> borel_measurable X"
        using measurable_cong[of _ "\<lambda>x. emeasure (\<kappa> x) A" "\<lambda>x. ennreal (indicat_real (space X - N) x * \<phi> x r + indicat_real N x * indicat_real {0..} (real_of_rat r))"]
        by simp
    qed(auto simp: rborel_eq_atMostq)
    have \<kappa>_AE:"AE x in r.\<nu>x. \<kappa> x {..real_of_rat r} = r.\<kappa>' x {..real_of_rat r}" for r
    proof -
      have "AE x in r.\<nu>x. \<kappa> x {..real_of_rat r} = ennreal (F x (real_of_rat r))"
        by(auto simp: space_marginal_measure \<kappa>(2))
      moreover have "AE x in r.\<nu>x. ennreal (F x (real_of_rat r))= ennreal (\<phi> x r)"
        using Feq[of _ r] by(auto simp add: space_marginal_measure intro!: AE_I''[OF N(1)])
      moreover have "AE x in r.\<nu>x. ennreal (\<phi> x r) = ennreal (enn2real (r.\<kappa>' x  {..real_of_rat r}))"
        by(simp add: \<phi>_def)
      moreover have "AE x in r.\<nu>x. ennreal (enn2real (r.\<kappa>' x  {..real_of_rat r})) = r.\<kappa>' x {..real_of_rat r}"
        using r.kernel_le_infty[of "{..real_of_rat r}",simplified]
        by(auto simp: ennreal_enn2real_if)
      ultimately show ?thesis by auto
    qed
    have \<kappa>_dis: "\<kappa>.disintegration \<nu> r.\<nu>x"
    proof -
      interpret D: Dynkin_system UNIV "{B \<in> sets borel. \<forall>A\<in> sets X. \<nu> (A \<times> B) = (\<integral>\<^sup>+x\<in>A. (\<kappa> x) B\<partial>r.\<nu>x)}"
      proof
        {
          fix A
          assume h:"A\<in> sets X"
          then have "\<nu> (A \<times> UNIV) = (\<integral>\<^sup>+x\<in>A. 1 \<partial>r.\<nu>x)"
            using emeasure_marginal_measure[OF nu_sets' h] sets_marginal_measure[of X borel \<nu> "space borel"] by auto
          also have "... = (\<integral>\<^sup>+x\<in>A. (\<kappa> x) UNIV\<partial>r.\<nu>x)"
            by(auto intro!: nn_integral_cong simp: \<kappa> space_marginal_measure)
          finally have "\<nu> (A \<times> UNIV) = (\<integral>\<^sup>+x\<in>A. emeasure (\<kappa> x) UNIV\<partial>r.\<nu>x)" .
        }
        thus "UNIV \<in> {B \<in> sets borel. \<forall>A\<in>sets X. emeasure \<nu> (A \<times> B) = \<integral>\<^sup>+x\<in>A. emeasure (\<kappa> x) B\<partial>r.\<nu>x}"
          by auto
        hence univ:"\<And>A. A \<in> sets X \<Longrightarrow> \<nu> (A \<times> UNIV) = (\<integral>\<^sup>+x\<in>A. emeasure (\<kappa> x) UNIV\<partial>r.\<nu>x)" by auto
        show "\<And>B. B \<in> {B \<in> sets borel. \<forall>A\<in>sets X. emeasure \<nu> (A \<times> B) = \<integral>\<^sup>+x\<in>A. emeasure (\<kappa> x) B\<partial>r.\<nu>x} \<Longrightarrow> UNIV - B \<in> {B \<in> sets borel. \<forall>A\<in>sets X. emeasure \<nu> (A \<times> B) = \<integral>\<^sup>+x\<in>A. emeasure (\<kappa> x) B\<partial>r.\<nu>x}"
        proof(rule r.\<nu>x.sigma_finite_disjoint)
          fix B and J :: "nat \<Rightarrow> _"
          assume "B \<in> {B \<in> sets borel. \<forall>A\<in>sets X. emeasure \<nu> (A \<times> B) = (\<integral>\<^sup>+x\<in>A. emeasure (\<kappa> x) B \<partial>r.\<nu>x)}" "range J \<subseteq> sets r.\<nu>x" "\<Union> (range J) = space r.\<nu>x"
                 "(\<And>i. emeasure r.\<nu>x (J i) \<noteq> \<infinity>)" "disjoint_family J"
          then have B: "B \<in> sets borel" " \<forall>A\<in>sets X. \<nu> (A \<times> B) = (\<integral>\<^sup>+x\<in>A. (\<kappa> x) B\<partial>r.\<nu>x)"
             and J: "range J \<subseteq> sets X" "\<Union> (range J) = space X" "\<And>i. emeasure r.\<nu>x (J i) \<noteq> \<infinity>" "disjoint_family J"
            by (auto simp: sets_marginal_measure space_marginal_measure)
          {
            fix A
            assume A: "A \<in> sets X"
            have "\<nu> (A \<times> (UNIV - B)) = (\<integral>\<^sup>+x\<in>A. (\<kappa> x) (UNIV - B)\<partial>r.\<nu>x)" (is "?lhs = ?rhs")
            proof -
              have AJi1: "disjoint_family (\<lambda>i. (A \<inter> J i) \<times> (UNIV - B))"
                using B(1) J(4) by(fastforce simp: disjoint_family_on_def)
              have AJi2[simp]: "(\<Union>i. ((A \<inter> J i) \<times> (UNIV - B))) = A \<times> (UNIV - B)"
                using J(2) sets.sets_into_space[OF A] by blast
              have AJi3: "(range (\<lambda>i. (A \<inter> J i) \<times> (UNIV - B))) \<subseteq> sets \<nu>"
                using B(1) J(1) A by(auto simp: nu_sets')

              have "?lhs = (\<Sum>i. \<nu> ((A \<inter> J i) \<times> (UNIV - B)))"
                by(simp add: suminf_emeasure[OF AJi3 AJi1])
              also have "... = (\<Sum>i. (\<integral>\<^sup>+x\<in> A \<inter> J i. (\<kappa> x) (UNIV - B) \<partial>r.\<nu>x))"
              proof(safe intro!: suminf_cong)
                fix n
                have Jn: "J n \<in> sets X"
                  using J by auto
                have fin: "\<nu> ((A \<inter> J n) \<times> C) \<noteq> \<infinity>" for C
                proof(cases "(A \<inter> J n) \<times> C \<in> sets \<nu>")
                  case True
                  then have "\<nu> ((A \<inter> J n) \<times> C) \<le> \<nu> ((A \<inter> J n) \<times> UNIV)"
                    using Jn nu_sets' A by(intro emeasure_mono) auto
                  also have "\<nu> ((A \<inter> J n) \<times> UNIV) \<le> \<nu> (J n \<times> UNIV)"
                    using Jn nu_sets' by(intro emeasure_mono) auto
                  also have "... = r.\<nu>x (J n)"
                    using emeasure_marginal_measure[OF nu_sets' Jn] by simp
                  finally show ?thesis
                    by (metis J(3)[of n] infinity_ennreal_def neq_top_trans)
                qed(simp add: emeasure_notin_sets)
                show "\<nu> ((A \<inter> J n) \<times> (UNIV - B)) = (\<integral>\<^sup>+x\<in> A \<inter> J n. (\<kappa> x) (UNIV - B) \<partial>r.\<nu>x)" (is "?lhs = ?rhs")
                proof -
                  have "?lhs = \<nu> ((A \<inter> J n) \<times> UNIV) - \<nu> ((A \<inter> J n) \<times> B)"
                  proof -
                    have [simp]: "?lhs + \<nu> ((A \<inter> J n) \<times> B) = \<nu> ((A \<inter> J n) \<times> UNIV)"
                    proof -
                      have [simp]:"((A \<inter> J n) \<times> (UNIV - B)) \<union> ((A \<inter> J n) \<times> B) = ((A \<inter> J n) \<times> UNIV)" by blast
                      show ?thesis
                        using B(1) A Jn nu_sets' by(intro plus_emeasure[of "(A \<inter> J n) \<times> (UNIV - B)" _ "(A \<inter> J n) \<times> B",simplified]) auto
                    qed
                    have "?lhs = ?lhs + \<nu> ((A \<inter> J n) \<times> B) - \<nu> ((A \<inter> J n) \<times> B)"
                      by(simp only: ennreal_add_diff_cancel[OF fin[of B]])
                    also have "... = \<nu> ((A \<inter> J n) \<times> UNIV) - \<nu> ((A \<inter> J n) \<times> B)"
                      by simp
                    finally show ?thesis .
                  qed
                  also have "... = (\<integral>\<^sup>+x\<in> A \<inter> J n. (\<kappa> x) UNIV \<partial>r.\<nu>x) - (\<integral>\<^sup>+x\<in> A \<inter> J n. (\<kappa> x) B \<partial>r.\<nu>x)"
                    using B(2) A Jn univ by auto
                  also have "... = (\<integral>\<^sup>+x. ((\<kappa> x) UNIV * indicator (A \<inter> J n) x - (\<kappa> x) B * indicator (A \<inter> J n) x) \<partial>r.\<nu>x)"
                  proof(rule nn_integral_diff[symmetric])
                    show "(\<lambda>x. (\<kappa> x) UNIV * indicator (A \<inter> J n) x) \<in> borel_measurable r.\<nu>x" "(\<lambda>x. (\<kappa> x) B * indicator (A \<inter> J n) x) \<in> borel_measurable r.\<nu>x"
                      using sets_marginal_measure[of X borel \<nu> "space borel"] \<kappa>.emeasure_measurable[OF B(1)] \<kappa>.emeasure_measurable[of UNIV] A Jn
                      by(auto simp del: space_borel)
                  next
                    show "\<integral>\<^sup>+x\<in>A \<inter> J n. (\<kappa> x) B\<partial>r.\<nu>x \<noteq> \<infinity>"
                      using B(2) A Jn univ fin[of B] by auto
                  next
                    show "AE x in r.\<nu>x. (\<kappa> x) B * indicator (A \<inter> J n) x \<le> (\<kappa> x) UNIV * indicator (A \<inter> J n) x"
                      by(standard, auto simp: space_marginal_measure indicator_def intro!: emeasure_mono)
                  qed
                  also have "... = (\<integral>\<^sup>+x\<in> A \<inter> J n. ((\<kappa> x) UNIV - (\<kappa> x) B) \<partial>r.\<nu>x)"
                    by(auto intro!: nn_integral_cong simp: indicator_def)
                  also have "... = ?rhs"
                  proof(safe intro!: nn_integral_cong)
                    fix x
                    assume "x \<in> space r.\<nu>x"
                    then have "x \<in> space X"
                      by(simp add: space_marginal_measure)
                    show "((\<kappa> x) UNIV - (\<kappa> x) B) * indicator (A \<inter> J n) x = (\<kappa> x) (UNIV - B) * indicator (A \<inter> J n) x"
                      by(auto intro!: emeasure_compl[of B "\<kappa> x",simplified,symmetric] simp: B \<kappa>.prob_spaces \<open>x \<in> space X\<close> prob_space_imp_subprob_space subprob_space.emeasure_subprob_space_less_top indicator_def)
                  qed
                  finally show ?thesis .
                qed
              qed
              also have "... = (\<integral>\<^sup>+x. (\<Sum>i. (\<kappa> x) (UNIV - B) * indicator (A \<inter> J i) x)\<partial>r.\<nu>x)"
                using \<kappa>.emeasure_measurable[of "UNIV - B"] B(1) sets_marginal_measure[of X borel \<nu> "space borel"] A J
                by(intro nn_integral_suminf[symmetric]) (auto simp del: space_borel)
              also have "... = (\<integral>\<^sup>+x. (\<kappa> x) (UNIV - B) * indicator A x *  (\<Sum>i. indicator (A \<inter> J i) x) \<partial>r.\<nu>x)"
                by(auto simp: indicator_def intro!: nn_integral_cong)
              also have "... = (\<integral>\<^sup>+x. (\<kappa> x) (UNIV - B) * indicator A x * (indicator (\<Union>i. A \<inter> J i) x) \<partial>r.\<nu>x)"
              proof -
                have "(\<Sum>i. indicator (A \<inter> J i) x) = (indicator (\<Union>i. A \<inter> J i) x :: ennreal)" for x
                  using J(4) by(intro suminf_indicator) (auto simp: disjoint_family_on_def)
                thus ?thesis
                  by(auto intro!: nn_integral_cong)
              qed
              also have "... = ?rhs"
                using J(2) by(auto simp: indicator_def space_marginal_measure intro!: nn_integral_cong)
              finally show ?thesis .
            qed
          }
          thus "UNIV - B \<in> {B \<in> sets borel. \<forall>A\<in>sets X. emeasure \<nu> (A \<times> B) = (\<integral>\<^sup>+x\<in>A. emeasure (\<kappa> x) B \<partial>r.\<nu>x)}"
            using B by auto
        qed
      next
        fix J :: "nat \<Rightarrow> _"
        assume J1: "disjoint_family J" "range J \<subseteq> {B \<in> sets borel. \<forall>A\<in>sets X. \<nu> (A \<times> B) = \<integral>\<^sup>+x\<in>A. (\<kappa> x) B\<partial>r.\<nu>x}"
        then have J2: "range J \<subseteq> sets borel" "\<Union> (range J) \<in> sets borel" "\<And>n A. A \<in> sets X \<Longrightarrow> \<nu> (A \<times> (J n)) = (\<integral>\<^sup>+x\<in>A. (\<kappa> x) (J n) \<partial>r.\<nu>x)"
          by auto
        show "\<Union> (range J) \<in> {B \<in> sets borel. \<forall>A\<in>sets X. \<nu> (A \<times> B) = \<integral>\<^sup>+x\<in>A. (\<kappa> x) B\<partial>r.\<nu>x}"
        proof -
          {
            fix A
            assume A:"A \<in> sets X"
            have "\<nu> (A \<times> \<Union> (range J)) = (\<integral>\<^sup>+x\<in>A. (\<kappa> x) (\<Union> (range J)) \<partial>r.\<nu>x)" (is "?lhs = ?rhs")
            proof -
              have "?lhs = \<nu> (\<Union>n. A \<times> J n)"
              proof -
                have "(A \<times> \<Union> (range J)) = (\<Union>n. A \<times> J n)" by blast
                thus ?thesis by simp
              qed
              also have "... = (\<Sum>n. \<nu> (A \<times> J n))"
                using J1(1) J2(1) A nu_sets' by(fastforce intro!: suminf_emeasure[symmetric] simp: disjoint_family_on_def)
              also have "... = (\<Sum>n. (\<integral>\<^sup>+x\<in>A. (\<kappa> x) (J n) \<partial>r.\<nu>x))"
                by(simp add: J2(3)[OF A])
              also have "... = (\<integral>\<^sup>+x. (\<Sum>n. (\<kappa> x) (J n) * indicator A x) \<partial>r.\<nu>x)"
                using \<kappa>.emeasure_measurable J2(1) A sets_marginal_measure[of X borel \<nu> "space borel"]
                by(intro nn_integral_suminf[symmetric]) auto
              also have "... = (\<integral>\<^sup>+x\<in>A. (\<Sum>n. (\<kappa> x) (J n)) \<partial>r.\<nu>x)"
                by auto
              also have "... = (\<integral>\<^sup>+x\<in>A. (\<kappa> x) (\<Union> (range J)) \<partial>r.\<nu>x)"
                using J1 J2 by(auto intro!: nn_integral_cong suminf_emeasure simp: space_marginal_measure indicator_def)
              finally show ?thesis .
            qed
          }
          thus ?thesis
            using J2(2) by auto
        qed
      qed auto
      have "{ {..r} | r::real. r \<in> \<rat>} \<subseteq> {B \<in> sets borel. \<forall>A\<in> sets X. \<nu> (A \<times> B) = (\<integral>\<^sup>+x\<in>A. (\<kappa> x) B\<partial>r.\<nu>x)}"
      proof -
        {
          fix r ::real and A
          assume h: "r \<in> \<rat>" "A \<in> sets X"
          then obtain r' where r':"r = real_of_rat r'"
            using Rats_cases by blast
          have "\<nu> (A \<times> {..r}) = (\<integral>\<^sup>+x\<in>A. (\<kappa> x) {..r} \<partial>r.\<nu>x)" (is "?lhs = ?rhs")
          proof -
            have "?lhs = (\<integral>\<^sup>+x\<in>A. r.\<kappa>' x {..r}\<partial>r.\<nu>x)"
              using h by(simp add: r.kernel_RN_deriv)
            also have "... = ?rhs"
              using \<kappa>_AE[of r'] by(auto intro!: nn_integral_cong_AE simp: r' simp del: space_borel)
            finally show ?thesis .
          qed
        }
        thus ?thesis
          by auto
      qed
      from D.Dynkin_subset[OF this] rborel_eq_atMostq[symmetric]
      show ?thesis
        by(auto simp: \<kappa>.disintegration_def sets_marginal_measure nu_sets' sigma_eq_Dynkin[OF _ atMostq_Int_stable,of UNIV,simplified,symmetric] rborel_eq_atMostq_sets simp del: space_borel)
    qed
    show ?thesis
    proof(intro exI conjI strip)
      fix \<kappa>''
      assume "prob_kernel X (borel :: real measure) \<kappa>''"
      interpret \<kappa>'':  prob_kernel X borel \<kappa>'' by fact
      assume disi: "\<kappa>''.disintegration \<nu> r.\<nu>x"
      have eq_atMostr_AE:"AE x in r.\<nu>x. \<forall>r. \<kappa> x {..real_of_rat r} = \<kappa>'' x {..real_of_rat r}"
        unfolding AE_all_countable
      proof safe
        fix r
        have "AE x in r.\<nu>x. (\<kappa>'' x) {..real_of_rat r} = r.\<kappa>' x {..real_of_rat r}"
        proof(safe intro!: r.\<nu>x.RN_deriv_unique[of "\<lambda>x. \<kappa>'' x {..real_of_rat r}" "marginal_measure_on X borel \<nu> {..real_of_rat r}",simplified r.\<kappa>'_def[of _ "{..real_of_rat r}",symmetric]])
          show 1:"(\<lambda>x. emeasure (\<kappa>'' x) {..real_of_rat r}) \<in> borel_measurable r.\<nu>x"
            using \<kappa>''.emeasure_measurable[of "{..real_of_rat r}"] sets_marginal_measure[of X borel \<nu> "space borel"] by simp
          show "density r.\<nu>x (\<lambda>x. emeasure (\<kappa>'' x) {..real_of_rat r}) = marginal_measure_on X borel \<nu> {..real_of_rat r}"
          proof(rule measure_eqI)
            fix A
            assume "A \<in> sets (density r.\<nu>x (\<lambda>x. (\<kappa>'' x) {..real_of_rat r}))"
            then have A [measurable]:"A \<in> sets X"
              by(simp add: sets_marginal_measure)
            show "emeasure (density r.\<nu>x (\<lambda>x. emeasure (\<kappa>'' x) {..real_of_rat r})) A = emeasure (marginal_measure_on X borel \<nu> {..real_of_rat r}) A" (is "?lhs = ?rhs")
            proof -
              have "?lhs = (\<integral>\<^sup>+x\<in>A. (\<kappa>'' x) {..real_of_rat r} \<partial>r.\<nu>x)"
                using emeasure_density[OF 1,of A] A 
                by(simp add: sets_marginal_measure)
              also have "... = \<nu> (A \<times> {..real_of_rat r})"
                using disi A by(auto simp: \<kappa>''.disintegration_def)
              also have "... = ?rhs"
                by(simp add: emeasure_marginal_measure_on[OF nu_sets' _ A])
              finally show ?thesis .
            qed
          qed(simp add: sets_marginal_measure)
        qed
        with \<kappa>_AE[of r]
        show "AE x in r.\<nu>x. \<kappa> x {..real_of_rat r} = \<kappa>'' x {..real_of_rat r}"
          by auto
      qed
      { fix x
        assume h:"x \<in> space r.\<nu>x" " \<forall>r. (\<kappa> x) {..real_of_rat r} = (\<kappa>'' x) {..real_of_rat r}"
        then have x: "x \<in> space X"
          by(simp add: space_marginal_measure)
        have "\<kappa> x = \<kappa>'' x"
        proof(rule measure_eqI_generator_eq[OF atMostq_Int_stable,of UNIV _ _ "\<lambda>n. {..real n}"])
          show "\<And>A. A \<in> {{..r} |r. r \<in> \<rat>} \<Longrightarrow> (\<kappa> x) A = (\<kappa>'' x) A"
            using h(2) Rats_cases by auto
        next
          show "(\<Union>n. {..real n}) = UNIV"
            by (simp add: real_arch_simple subsetI subset_antisym)
        next
          fix n
          have "(\<kappa> x) {..real n} \<le> \<kappa> x UNIV"
            by(auto intro!: emeasure_mono)
          also have "... = 1"
            by(rule \<kappa>(1)[OF x])
          finally show "(\<kappa> x) {..real n} \<noteq> \<infinity>"
            using linorder_not_le by fastforce
        next
          show "range (\<lambda>n. {..real n}) \<subseteq> {{..r} |r. r \<in> \<rat>}"
            using Rats_of_nat by blast
        qed(auto simp: \<kappa>.kernel_sets[OF x] \<kappa>''.kernel_sets[OF x] rborel_eq_atMostq_sets)
      }
      then show "AE x in r.\<nu>x. \<kappa> x = \<kappa>'' x"
        using eq_atMostr_AE by fastforce
    qed(auto simp del: space_borel simp add: \<kappa>_dis \<kappa>.prob_kernel_axioms)
  qed

  show ?thesis
  proof -
    define \<nu>' where "\<nu>' = distr \<nu> (X \<Otimes>\<^sub>M borel) (\<lambda>(x,y). (x, to_real y))"
    have \<nu>_distr:"\<nu> = distr \<nu>' (X \<Otimes>\<^sub>M Y) (\<lambda>(x,y). (x, from_real y))"
      using nu_sets sets_eq_imp_space_eq[OF nu_sets] from_real_to_real
      by(auto simp: \<nu>'_def distr_distr space_pair_measure intro!: distr_id'[symmetric])
    have \<nu>x_eq:"(marginal_measure X borel \<nu>') = \<nu>x"
      using emeasure_marginal_measure[of \<nu>' X borel] emeasure_marginal_measure[OF nu_sets] sets_eq_imp_space_eq[OF nu_sets]
      by(auto intro!: measure_eqI simp: sets_marginal_measure \<nu>'_def emeasure_distr map_prod_vimage[of id to_real,simplified map_prod_def id_def] space_pair_measure Times_Int_Times)
    interpret \<nu>' : projection_sigma_finite X borel \<nu>'
      by(auto simp: projection_sigma_finite_def \<nu>x_eq \<nu>x.sigma_finite_measure_axioms simp del: space_borel,auto simp add: \<nu>'_def)
    obtain \<kappa>' where \<kappa>': "prob_kernel X borel \<kappa>'" "measure_kernel.disintegration X borel \<kappa>' \<nu>' \<nu>'.\<nu>x"
         "\<And>\<kappa>''. prob_kernel X borel \<kappa>'' \<Longrightarrow> measure_kernel.disintegration X borel \<kappa>'' \<nu>' \<nu>'.\<nu>x \<Longrightarrow> (AE x in \<nu>'.\<nu>x. \<kappa>' x = \<kappa>'' x)"
      using *[of \<nu>' X] \<nu>'.nu_sets \<nu>'.\<nu>x.sigma_finite_measure_axioms by blast
    interpret \<kappa>': prob_kernel X borel \<kappa>' by fact
    define \<kappa> where "\<kappa> \<equiv> (\<lambda>x. distr (\<kappa>' x) Y from_real)"
    interpret \<kappa>: prob_kernel X Y \<kappa>
      by(auto simp: prob_kernel_def' \<kappa>_def)
    have disi: "\<kappa>.disintegration \<nu> \<nu>x"
    proof(rule \<kappa>.disintegrationI)
      fix A B
      assume A[measurable]:"A \<in> sets X" and B[measurable]: "B \<in> sets Y"
      have [measurable]: "from_real -` B \<in> sets borel"
        by(simp add: measurable_sets_borel[OF _ B])
      show "\<nu> (A \<times> B) = (\<integral>\<^sup>+x\<in>A. \<kappa> x B\<partial>\<nu>x)" (is "?lhs = ?rhs")
      proof -
        have "?lhs = \<nu>' (A \<times> (from_real -` B))"
          by(auto simp: \<nu>_distr emeasure_distr map_prod_vimage[of id from_real,simplified map_prod_def id_def])
        also have "... = (\<integral>\<^sup>+x\<in>A. \<kappa>' x (from_real -` B) \<partial>\<nu>x)"
          using \<kappa>'.disintegrationD[OF \<kappa>'(2),of A "from_real -` B"]
          by(auto simp add: \<nu>x_eq simp del: space_borel)
        also have "... = ?rhs"
          by(auto intro!: nn_integral_cong simp: space_marginal_measure \<kappa>_def emeasure_distr)
        finally show ?thesis .
      qed
    qed(simp_all add: sets_marginal_measure nu_sets)

    show ?thesis
    proof(safe intro!: exI[where x=\<kappa>])
      fix \<kappa>''
      assume h:"prob_kernel X Y \<kappa>''"
               "measure_kernel.disintegration X Y \<kappa>'' \<nu> \<nu>x"
      interpret \<kappa>'': prob_kernel X Y \<kappa>'' by fact
      show "AE x in \<nu>x. \<kappa> x = \<kappa>'' x"
      proof -
       define \<kappa>''' where "\<kappa>''' \<equiv> (\<lambda>x. distr (\<kappa>'' x) borel to_real)"
        interpret \<kappa>''': prob_kernel X borel \<kappa>'''
          by(auto simp: prob_kernel_def' \<kappa>'''_def)
        have \<kappa>''_def: "\<kappa>'' x = distr (\<kappa>''' x) Y from_real" if "x \<in> space X" for x
          using distr_distr[of from_real borel Y to_real "\<kappa>'' x",simplified measurable_cong_sets[OF \<kappa>''.kernel_sets[OF that] refl,of borel]] 
          by(auto simp: \<kappa>'''_def comp_def \<kappa>''.kernel_sets[OF that] measurable_cong_sets[OF \<kappa>''.kernel_sets[OF that] \<kappa>''.kernel_sets[OF that]] sets_eq_imp_space_eq[OF \<kappa>''.kernel_sets[OF that]] intro!: distr_id'[symmetric])
        have \<kappa>'''_disi: "\<kappa>'''.disintegration \<nu>' \<nu>'.\<nu>x"
        proof(rule \<kappa>'''.disintegrationI)
          fix A and B :: "real set"
          assume A[measurable]:"A \<in> sets X" and B[measurable]:"B \<in> sets borel"
          show "\<nu>' (A \<times> B) = (\<integral>\<^sup>+x\<in>A. (\<kappa>''' x) B \<partial>\<nu>'.\<nu>x)" (is "?lhs = ?rhs")
          proof -
            have "?lhs = \<nu> (A \<times> (to_real -` B \<inter> space Y))"
              by(auto simp: \<nu>'_def emeasure_distr map_prod_vimage[of id to_real,simplified map_prod_def id_def] sets_eq_imp_space_eq[OF nu_sets] space_pair_measure Times_Int_Times)
            also have "... = (\<integral>\<^sup>+x\<in>A. (\<kappa>'' x) (to_real -` B \<inter> space Y) \<partial>\<nu>x)"
              using \<kappa>''.disintegrationD[OF h(2) A,of "to_real -` B \<inter> space Y"] by auto
            also have "... = ?rhs"
              by(auto simp: \<nu>x_eq[symmetric] space_marginal_measure \<kappa>'''_def emeasure_distr sets_eq_imp_space_eq[OF \<kappa>''.kernel_sets] intro!: nn_integral_cong)
            finally show ?thesis .
          qed
        qed(auto simp: \<nu>'_def sets_marginal_measure) 
        show ?thesis
          by(rule AE_mp[OF \<kappa>'(3)[OF \<kappa>'''.prob_kernel_axioms \<kappa>'''_disi,simplified \<nu>x_eq]],standard) (auto simp: space_marginal_measure \<kappa>''_def \<kappa>_def)
      qed
    qed(simp_all add: disi \<kappa>.prob_kernel_axioms)
  qed
qed

end

subsection \<open> Lemma 14.D.12. \<close>
lemma ex_finite_density_measure:
  fixes A :: "nat \<Rightarrow> _"
  assumes A: "range A \<subseteq> sets M" "\<Union> (range A) = space M" "\<And>i. emeasure M (A i) \<noteq> \<infinity>" "disjoint_family A"
  defines "h \<equiv> (\<lambda>x. (\<Sum>n. (1/2)^(Suc n) * (1 / (1 + M (A n))) * indicator (A n) x))"
  shows "h \<in> borel_measurable M"
        "\<And>x. x \<in> space M \<Longrightarrow> 0 < h x"
        "\<And>x. x \<in> space M \<Longrightarrow> h x < 1"
        "finite_measure (density M h)"
proof -
  have less1:"0 < 1 / (1 + M (A n))" "1 / (1 + M (A n)) \<le> 1" for n
    using A(3)[of n] ennreal_zero_less_divide[of 1 "1 + M (A n)"]
    by (auto intro!: divide_le_posI_ennreal simp: add_pos_nonneg)
  show [measurable]:"h \<in> borel_measurable M"
    using A by(simp add: h_def)
  {
    fix x
    assume x:"x \<in> space M"
    then obtain i where i: "x \<in> A i"
      using A(2) by auto
    show "0 < h x"
      using A(3)[of i] less1[of i]
      by(auto simp: h_def suminf_pos_iff i ennreal_divide_times ennreal_zero_less_divide power_divide_distrib_ennreal power_less_top_ennreal intro!: exI[where x=i])
    have "h x = (\<Sum>n. (1/2)^(Suc n + 2) * (1 / (1 + M (A (n + 2)))) * indicator (A (n + 2)) x) + (1/2) * (1 / (1 + M (A 0))) * indicator (A 0) x + (1/2)^2 * (1 / (1 + M (A 1))) * indicator (A 1) x"
      by(auto simp: h_def suminf_split_head suminf_offset[of "\<lambda>n. (1/2)^(Suc n) * (1 / (1 + M (A n))) * indicator (A n) x" 2] simp del: power_Suc sum_mult_indicator) (auto simp: numeral_2_eq_2)
    also have "... \<le> 1/4 +  (1/2) * (1 / (1 + M (A 0))) * indicator (A 0) x + (1/2)^2 * (1 / (1 + M (A 1))) * indicator (A 1) x"
    proof -
      have "(\<Sum>n. (1/2)^(Suc n + 2) * (1 / (1 + M (A (n + 2)))) * indicator (A (n + 2)) x) \<le> (\<Sum>n. (1/2)^(Suc n + 2))"
        using less1(2)[of "Suc (Suc _)"] by(intro suminf_le,auto simp: indicator_def) (metis mult.right_neutral mult_left_mono zero_le)
      also have "... = (\<Sum>n. ennreal ((1 / 2) ^ (Suc n + 2)))"
        by(simp only: ennreal_power[of "1/2",symmetric]) (metis divide_ennreal ennreal_1 ennreal_numeral linorder_not_le not_one_less_zero zero_less_numeral)
      also have "... = ennreal (\<Sum>n. (1 / 2) ^ (Suc n + 2))"
        by(rule suminf_ennreal2) auto
      also have "... = ennreal (1/4)"
        using nsum_of_r'[of "1/2" "Suc (Suc (Suc 0))" 1] by auto
      also have "... = 1 / 4"
        by (metis ennreal_divide_numeral ennreal_numeral numeral_One zero_less_one_class.zero_le_one)
      finally show ?thesis by simp
    qed
    also have "... < 1" (is "?lhs < _")
    proof(cases "x \<in> A 0")
      case True
      then have "x \<notin> A 1"
        using A(4) by (auto simp: disjoint_family_on_def)
      hence "?lhs =  1 / 4 + 1 / 2 * (1 / (1 + emeasure M (A 0)))"
        by(simp add: True)
      also have "... \<le> 1 / 4 + 1 / 2"
        using less1(2)[of 0] by (simp add: divide_right_mono_ennreal ennreal_divide_times)
      also have "... = 1 / 4 + 2 / 4"
        using divide_mult_eq[of 2 1 2] by simp
      also have "... = 3 / 4"
        by(simp add: add_divide_distrib_ennreal[symmetric])
      also have "... < 1"
        by(simp add: divide_less_ennreal)
      finally show ?thesis .
    next
      case False
      then have "?lhs = 1 / 4 + (1 / 2)\<^sup>2 * (1 / (1 + emeasure M (A 1))) * indicator (A 1) x"
        by simp
      also have "... \<le>  1 / 4 + (1 / 2)\<^sup>2"
        by (metis less1(2)[of 1] add_left_mono indicator_eq_0_iff indicator_eq_1_iff mult.right_neutral mult_eq_0_iff mult_left_mono zero_le)
      also have "... = 2 / 4"
        by(simp add: power_divide_distrib_ennreal add_divide_distrib_ennreal[symmetric])
      also have "... < 1"
        by(simp add: divide_less_ennreal)
      finally show ?thesis .
    qed
    finally show "h x < 1" .
  }
  show "finite_measure (density M h)"
  proof
    show "emeasure (density M h) (space (density M h)) \<noteq> \<infinity>"
    proof -
      have "integral\<^sup>N M h \<noteq> \<top>" (is "?lhs \<noteq> _")
      proof -
        have "?lhs = (\<Sum>n. (\<integral>\<^sup>+ x\<in>A n. ((1/2)^(Suc n) * (1 / (1 + M (A n)))) \<partial>M))"
          using A by(simp add: h_def nn_integral_suminf)
        also have "... = (\<Sum>n. (1/2)^(Suc n) * (1 / (1 + M (A n))) * M (A n))"
          by(rule suminf_cong,rule nn_integral_cmult_indicator) (use A in auto)
        also have "... = (\<Sum>n. (1/2)^(Suc n) * ((1 / (1 + M (A n))) * M (A n)))"
          by (simp add: mult.assoc)
        also have "... \<le> (\<Sum>n. (1/2)^(Suc n))"
        proof -
          have "(1 / (1 + M (A n))) * M (A n) \<le> 1" for n
            using A(3)[of n] by (simp add: add_pos_nonneg divide_le_posI_ennreal ennreal_divide_times)
          thus ?thesis
            by(intro suminf_le) (metis mult.right_neutral mult_left_mono zero_le,auto)
        qed
        also have "... = (\<Sum>n. ennreal ((1/2)^(Suc n)))"
          by(simp only: ennreal_power[of "1/2",symmetric]) (metis divide_ennreal ennreal_1 ennreal_numeral linorder_not_le not_one_less_zero zero_less_numeral)
        also have "... = ennreal (\<Sum>n. (1/2)^(Suc n))"
          by(rule suminf_ennreal2) auto
        also have "... = 1"
          using nsum_of_r'[of "1/2" 1 1] by auto
        finally show ?thesis
          using nle_le by fastforce
      qed
      thus ?thesis
        by(simp add: emeasure_density)
    qed
  qed
qed

lemma(in sigma_finite_measure) finite_density_measure:
  obtains h where "h \<in> borel_measurable M"
                  "\<And>x. x \<in> space M \<Longrightarrow> 0 < h x"
                  "\<And>x. x \<in> space M \<Longrightarrow> h x < 1"
                  "finite_measure (density M h)"
  by (metis (no_types, lifting) sigma_finite_disjoint ex_finite_density_measure)

subsection \<open> Lemma 14.D.13. \<close>
lemma (in measure_kernel)
  assumes "disintegration \<nu> \<mu>"
  defines "\<nu>x \<equiv> marginal_measure X Y \<nu>"
  shows disintegration_absolutely_continuous: "absolutely_continuous \<mu> \<nu>x"
    and disintegration_density: "\<nu>x = density \<mu> (\<lambda>x. \<kappa> x (space Y))"
    and disintegration_absolutely_continuous_iff:
        "absolutely_continuous \<nu>x \<mu> \<longleftrightarrow> (AE x in \<mu>. \<kappa> x (space Y) > 0)"
proof -
  note sets_eq[measurable_cong] = disintegration_sets_eq[OF assms(1)]
  note [measurable] = emeasure_measurable[OF sets.top]
  have \<nu>x_eq: "\<nu>x A = (\<integral>\<^sup>+x\<in>A. (\<kappa> x (space Y)) \<partial>\<mu>)" if A:"A \<in> sets X" for A
    by(simp add: disintegrationD[OF assms(1) A sets.top] emeasure_marginal_measure[OF sets_eq(1) A] \<nu>x_def)
  thus 1:"\<nu>x = density \<mu> (\<lambda>x. \<kappa> x (space Y))"
    by(auto intro!: measure_eqI simp: sets_marginal_measure \<nu>x_def sets_eq emeasure_density)
  hence sets_\<nu>x:"sets \<nu>x = sets X"
    using sets_eq by simp
  show "absolutely_continuous \<mu> \<nu>x"
    unfolding absolutely_continuous_def
  proof safe
    fix A
    assume A: "A \<in> null_sets \<mu>"
    have "0 = (\<integral>\<^sup>+x\<in>A. (\<kappa> x (space Y)) \<partial>\<mu>)"
      by(simp add: A nn_integral_null_set)
    also have "... = \<nu>x A"
      using A \<nu>x_eq[of A,simplified sets_eq(2)[symmetric]]
      by auto
    finally show "A \<in> null_sets \<nu>x"
      using A by(auto simp: null_sets_def \<nu>x_def sets_marginal_measure sets_eq)
  qed
  show "absolutely_continuous \<nu>x \<mu> \<longleftrightarrow> (AE x in \<mu>. \<kappa> x (space Y) > 0)"
  proof
    assume h:"absolutely_continuous \<nu>x \<mu>"
    define N where "N = {x \<in> space \<mu>. (\<kappa> x) (space Y) = 0}"
    have "N \<in> null_sets \<mu>"
    proof -
      have "\<nu>x N = (\<integral>\<^sup>+x\<in>N. (\<kappa> x (space Y)) \<partial>\<mu>)"
        using \<nu>x_eq[of N] by(simp add: N_def sets_eq_imp_space_eq[OF sets_eq(2)])
      also have "... = (\<integral>\<^sup>+x\<in>N. 0 \<partial>\<mu>)"
        by(rule nn_integral_cong) (auto simp: N_def indicator_def)
      also have "... = 0" by simp
      finally have "N \<in> null_sets \<nu>x"
        by(auto simp: null_sets_def 1 N_def)
      thus ?thesis
        using h by(auto simp: absolutely_continuous_def)
    qed
    then show "AE x in \<mu>. 0 < (\<kappa> x) (space Y)"
      by(auto intro!: AE_I'[OF _ subset_refl] simp: N_def)
  next
    assume "AE x in \<mu>. 0 < (\<kappa> x) (space Y)"
    then show "absolutely_continuous \<nu>x \<mu>"
      using \<nu>x_eq by(auto simp: absolutely_continuous_def intro!: null_if_pos_func_has_zero_nn_int[where f="\<lambda>x. emeasure (\<kappa> x) (space Y)"]) (auto simp: null_sets_def sets_\<nu>x)
  qed
qed

subsection \<open> Theorem 14.D.14. \<close>
locale sigma_finite_measure_on_pair_standard = sigma_finite_measure_on_pair + standard_borel_ne Y

sublocale projection_sigma_finite_standard \<subseteq> sigma_finite_measure_on_pair_standard
  by (simp add: sigma_finite_measure_on_pair_axioms sigma_finite_measure_on_pair_standard_def standard_borel_ne_axioms)

context sigma_finite_measure_on_pair_standard
begin

lemma measure_disintegration_extension:
   "\<exists>\<mu> \<kappa>. finite_measure \<mu> \<and> measure_kernel X Y \<kappa> \<and> measure_kernel.disintegration X Y \<kappa> \<nu> \<mu> \<and>
               (\<forall>x\<in>space X. sigma_finite_measure (\<kappa> x)) \<and>
               (\<forall>x\<in>space X. \<kappa> x (space Y) > 0) \<and>
                \<mu> ~\<^sub>M \<nu>x" (is "?goal")
proof(rule sigma_finite_measure.sigma_finite_disjoint[OF sigma_finite])
  fix A :: "nat \<Rightarrow> _"
  assume A:"range A \<subseteq> sets \<nu>" "\<Union> (range A) = space \<nu>" "\<And>i. emeasure \<nu> (A i) \<noteq> \<infinity>" "disjoint_family A"
  define h where "h \<equiv> (\<lambda>x. \<Sum>n. (1 / 2) ^ Suc n * (1 / (1 + emeasure \<nu> (A n))) * indicator (A n) x)"
  have h: "h \<in> borel_measurable \<nu>" "\<And>x y. x \<in> space X \<Longrightarrow> y \<in> space Y \<Longrightarrow> 0 < h (x,y)" "\<And>x y. x \<in> space X \<Longrightarrow> y \<in> space Y \<Longrightarrow> h (x,y) < 1" "finite_measure (density \<nu> h)"
    using ex_finite_density_measure[OF A] by(auto simp: sets_eq_imp_space_eq[OF nu_sets] h_def space_pair_measure)

  interpret psfs_\<nu>x: finite_measure "marginal_measure X Y (density \<nu> h)"
    by(rule finite_measure_marginal_measure_finite[OF h(4),simplified,OF nu_sets])

  interpret psfs: projection_sigma_finite_standard X Y "density \<nu> h"
    by(auto simp: projection_sigma_finite_standard_def projection_sigma_finite_def standard_borel_ne_axioms nu_sets finite_measure.sigma_finite_measure[OF finite_measure_marginal_measure_finite[OF h(4),simplified,OF nu_sets]])
  from psfs.measure_disintegration
  obtain \<kappa>' where \<kappa>': "prob_kernel X Y \<kappa>'" "measure_kernel.disintegration X Y \<kappa>' (density \<nu> h) psfs.\<nu>x" by auto
  interpret pk: prob_kernel X Y \<kappa>' by fact
  define \<kappa> where "\<kappa> \<equiv> (\<lambda>x. density (\<kappa>' x) (\<lambda>y. 1 / h (x,y)))"
  have \<kappa>B: "\<kappa> x B = (\<integral>\<^sup>+y\<in>B. (1 / h (x, y))\<partial>\<kappa>' x)" if "x \<in> space X" and [measurable]:"B \<in> sets Y" for x B
    using nu_sets pk.kernel_sets[OF that(1)] that h(1) by(auto simp: \<kappa>_def emeasure_density)
  interpret mk: measure_kernel X Y \<kappa>
  proof
    fix B
    assume [measurable]:"B \<in> sets Y"
    have 1:"(\<lambda>x. \<integral>\<^sup>+y\<in>B. (1 / h (x, y))\<partial>\<kappa>' x) \<in> borel_measurable X"
      using h(1) nu_sets by(auto intro!: pk.nn_integral_measurable_f'[of "\<lambda>z. (1 / h z) * indicator B (snd z)",simplified])
    show "(\<lambda>x. (\<kappa> x) B) \<in> borel_measurable X"
      by(rule measurable_cong[THEN iffD1,OF _ 1],simp add: \<kappa>B)
  qed(simp_all add: \<kappa>_def pk.kernel_sets space_ne)

  have disi: "mk.disintegration \<nu> psfs.\<nu>x"
  proof(rule mk.disintegrationI)
    fix A B
    assume A[measurable]:"A \<in> sets X" and B[measurable]:"B \<in> sets Y"
    show "\<nu> (A \<times> B) = (\<integral>\<^sup>+x\<in>A. (\<kappa> x) B\<partial>psfs.\<nu>x)" (is "?lhs = ?rhs")
    proof -
      have "?lhs = (\<integral>\<^sup>+z\<in>A \<times> B. 1 \<partial>\<nu>)"
        by auto
      also have "... = (\<integral>\<^sup>+z\<in>A \<times> B. (1 / h z * h z) \<partial>\<nu>)"
      proof -
        have 1: "a * (1 / a) = 1" if "0 < a" "a < 1" for a :: ennreal
        proof -
          have "a * (1 / a) = ennreal (enn2real a * 1 / (enn2real a))"
            by (simp add: divide_eq_1_ennreal enn2real_eq_0_iff ennreal_times_divide)
          also have "... = ennreal 1"
            using enn2real_eq_0_iff that by fastforce
          finally show ?thesis
            using ennreal_1 by simp
        qed
        show ?thesis
          by(rule nn_integral_cong,auto simp add: sets_eq_imp_space_eq[OF nu_sets] space_pair_measure ennreal_divide_times indicator_def 1[OF h(2,3)])
      qed
      also have "... = (\<integral>\<^sup>+z. h z * ((1 / h z) * indicator (A \<times> B) z) \<partial>\<nu>)"
        by(auto intro!: nn_integral_cong simp: indicator_def mult.commute)
      also have "... = (\<integral>\<^sup>+z\<in>A \<times> B. (1 / h z) \<partial>(density \<nu> h))"
        using h(1) by(simp add: nn_integral_density)
      also have "... = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. (1 / h (x,y) * indicator (A \<times> B) (x,y)) \<partial>\<kappa>' x \<partial>psfs.\<nu>x)"
        using h(1) by(simp add: pk.nn_integral_fst_finite'[OF _ \<kappa>'(2) psfs_\<nu>x.finite_measure_axioms])
      also have "... = (\<integral>\<^sup>+ x\<in>A. (\<integral>\<^sup>+ y\<in>B. (1 / h (x,y)) \<partial>\<kappa>' x) \<partial>psfs.\<nu>x)"
        by(auto intro!: nn_integral_cong simp: indicator_def)
      also have "... = ?rhs"
        by(auto intro!: nn_integral_cong simp: \<kappa>B[OF _ B] space_marginal_measure)
      finally show ?thesis .
    qed
  qed(simp_all add: nu_sets sets_marginal_measure)
  have geq0: "0 < (\<kappa> x) (space Y)" if "x \<in> space X" for x
  proof -
    have "0 = (\<integral>\<^sup>+ y. 0 \<partial>\<kappa>' x)" by simp
    also have "... < (\<integral>\<^sup>+ y. (1 / h (x,y)) \<partial>\<kappa>' x)"
    proof(rule nn_integral_less)
      show "\<not> (AE y in \<kappa>' x. 1 / h (x, y) \<le> 0)"
      proof
        assume "AE y in \<kappa>' x. 1 / h (x, y) \<le> 0"
        moreover have "h (x,y) \<noteq> \<top>" if "y \<in> space (\<kappa>' x)" for y
          using h(3)[OF \<open>x \<in> space X\<close> that[simplified sets_eq_imp_space_eq[OF pk.kernel_sets[OF \<open>x \<in> space X\<close>]]]] top.not_eq_extremum
          by fastforce
        ultimately show False
          using prob_space.AE_False[OF pk.prob_spaces[OF that]] by simp
      qed
    qed(use h(1) pk.kernel_sets[OF that] that in auto)
    also have "... = (\<kappa> x) (space Y)"
      by(simp add: \<kappa>B[OF that sets.top]) (simp add: sets_eq_imp_space_eq[OF pk.kernel_sets[OF that],symmetric])
    finally show ?thesis .
  qed

  show ?goal
  proof(safe intro!: exI[where x=psfs.\<nu>x] exI[where x=\<kappa>] disi)
    show "absolutely_continuous \<nu>x psfs.\<nu>x"
      unfolding mk.disintegration_absolutely_continuous_iff[OF disi]
      by standard (simp add: space_marginal_measure geq0)
  next
    fix x
    assume x:"x \<in> space X"
    define C where "C \<equiv> range (\<lambda>n. Pair x -` (A n) \<inter> space Y)"
    have 1:"countable C" "C \<subseteq> sets Y"
      using A(1,2) x by (auto simp: nu_sets sets_eq_imp_space_eq[OF nu_sets] space_pair_measure C_def)
    have 2: "\<Union> C = space Y"
      using A(1,2)  by(auto simp: sets_eq_imp_space_eq[OF nu_sets] space_pair_measure C_def) (use x in auto)

    show "sigma_finite_measure (\<kappa> x)"
      unfolding sigma_finite_measure_def
    proof(safe intro!: exI[where x=C])
      fix c
      assume "c \<in> C" "(\<kappa> x) c = \<infinity>"
      then obtain n where c:"c = Pair x -` (A n) \<inter> space Y" by(auto simp: C_def)
      have "(\<kappa> x) c = (\<integral>\<^sup>+y\<in>c. (1 / h (x, y))\<partial>\<kappa>' x)"
        using \<kappa>B[OF x,of c] 1 \<open>c \<in> C\<close> by auto
      also have "... = (\<integral>\<^sup>+y\<in>Pair x -` (A n). (1 / h (x, y))\<partial>\<kappa>' x)"
        by(auto intro!: nn_integral_cong simp: c indicator_def sets_eq_imp_space_eq[OF pk.kernel_sets[OF x]])
      also have "... = (\<integral>\<^sup>+y\<in>Pair x -` (A n). (1 / ((1 / 2) ^ Suc n * (1 / (1 + emeasure \<nu> (A n))))) \<partial>\<kappa>' x)"
      proof -
        {
          fix y
          assume xy:"(x, y) \<in> A n"
          have "1 / h (x, y) = 1 / ((1 / 2) ^ Suc n * (1 / (1 + emeasure \<nu> (A n))))"
          proof -
            have "h (x, y) = (1 / 2) ^ Suc n * (1 / (1 + emeasure \<nu> (A n)))" (is "?lhs = ?rhs")
            proof -
              have "?lhs = (\<Sum>m. (1 / 2) ^ Suc m * (1 / (1 + emeasure \<nu> (A m))) * indicator (A m) (x,y))"
                by(simp add: h_def)
              also have "... = (\<Sum>m. if m = n then (1 / 2) ^ Suc n * (1 / (1 + emeasure \<nu> (A n))) else 0)"
                using xy A(4) by(fastforce intro!: suminf_cong simp: disjoint_family_on_def indicator_def)
              also have "... = (\<Sum>j. if j + Suc n = n then (1 / 2) ^ Suc n * (1 / (1 + emeasure \<nu> (A n))) else 0) + (\<Sum>j<Suc n. if j = n then (1 / 2) ^ Suc n * (1 / (1 + emeasure \<nu> (A n))) else 0)"
                by(auto simp: suminf_offset[of "\<lambda>m. if m = n then (1 / 2) ^ Suc n * (1 / (1 + emeasure \<nu> (A n))) else 0" "Suc n"] simp del: power_Suc)
              also have "... = ?rhs"
                by simp
              finally show ?thesis .
            qed
            thus ?thesis by simp
          qed
        }
        thus ?thesis
          by(intro nn_integral_cong) (auto simp: sets_eq_imp_space_eq[OF pk.kernel_sets[OF x]] indicator_def simp del: power_Suc)
      qed
      also have "... \<le> (\<integral>\<^sup>+y. (1 / ((1 / 2) ^ Suc n * (1 / (1 + emeasure \<nu> (A n))))) \<partial>\<kappa>' x)"
        by(rule nn_integral_mono) (auto simp: indicator_def)
      also have "... = (1 / ((1 / 2) ^ Suc n * (1 / (1 + emeasure \<nu> (A n)))))"
        by(simp add: prob_space.emeasure_space_1[OF pk.prob_spaces[OF x]])
      also have "... < \<infinity>"
        by (metis A(3) ennreal_add_eq_top ennreal_divide_eq_0_iff ennreal_divide_eq_top_iff ennreal_top_neq_one infinity_ennreal_def mult_eq_0_iff power_eq_0_iff top.not_eq_extremum top_neq_numeral)
      finally show False
        using \<open>(\<kappa> x) c = \<infinity>\<close> by simp
    qed(insert 1 2, auto simp: mk.kernel_sets[OF x] sets_eq_imp_space_eq[OF mk.kernel_sets[OF x]])
  qed(auto simp: psfs_\<nu>x.finite_measure_axioms geq0 mk.measure_kernel_axioms mk.disintegration_absolutely_continuous[OF disi])
qed

end

(* TODO: \<open>AE x in \<mu>. \<forall>B \<in> sets Y. ... = ...\<close> for a standard Borel Y. *)
lemma(in sigma_finite_measure_on_pair) measure_disintegration_extension_AE_unique:
  assumes "sigma_finite_measure \<mu>" "sigma_finite_measure \<mu>'"
          "measure_kernel X Y \<kappa>" "measure_kernel X Y \<kappa>'"
          "measure_kernel.disintegration X Y \<kappa> \<nu> \<mu>" "measure_kernel.disintegration X Y \<kappa>' \<nu> \<mu>'"
      and "absolutely_continuous \<mu> \<mu>'" "B \<in> sets Y"
    shows "AE x in \<mu>. \<kappa>' x B * RN_deriv \<mu> \<mu>' x = \<kappa> x B"
proof -
  interpret s1: sigma_finite_measure \<mu> by fact
  interpret s2: sigma_finite_measure \<mu>' by fact
  interpret mk1: measure_kernel X Y \<kappa> by fact
  interpret mk2: measure_kernel X Y \<kappa>' by fact
  have sets[measurable_cong]:"sets \<mu> = sets X" "sets \<mu>' = sets X"
    using assms(5,6) by(auto dest: mk1.disintegration_sets_eq mk2.disintegration_sets_eq)
  have 1:"AE x in \<mu>. \<kappa> x B = RN_deriv \<mu> (marginal_measure_on X Y \<nu> B) x"
    using sets mk1.emeasure_measurable[OF assms(8)] mk1.disintegrationD[OF assms(5) _ assms(8)]
    by(auto intro!: measure_eqI s1.RN_deriv_unique  simp: emeasure_density emeasure_marginal_measure_on[OF nu_sets assms(8)] sets sets_marginal_measure)
  have 2:"AE x in \<mu>. \<kappa>' x B * RN_deriv \<mu> \<mu>' x = RN_deriv \<mu> (marginal_measure_on X Y \<nu> B) x"
  proof -
    {
      fix A
      assume A: "A \<in> sets X"
      have "(\<integral>\<^sup>+x\<in>A.  ((\<kappa>' x) B * RN_deriv \<mu> \<mu>' x) \<partial>\<mu>) = (\<integral>\<^sup>+x. RN_deriv \<mu> \<mu>' x * (\<kappa>' x B * indicator A x)\<partial>\<mu>)"
        by(auto intro!: nn_integral_cong simp: indicator_def mult.commute)
      also have "... = (\<integral>\<^sup>+x\<in>A. \<kappa>' x B \<partial>\<mu>')"
        using mk2.emeasure_measurable[OF assms(8)] sets A
        by(auto intro!: s1.RN_deriv_nn_integral[OF assms(7),symmetric])
      also have "... = \<nu> (A \<times> B)"
        by(simp add: mk2.disintegrationD[OF assms(6) A assms(8)])
      finally have "(\<integral>\<^sup>+x\<in>A.  ((\<kappa>' x) B * RN_deriv \<mu> \<mu>' x) \<partial>\<mu>) = \<nu> (A \<times> B)" .
    }
    thus ?thesis
      using sets mk2.emeasure_measurable[OF assms(8)] 
      by(auto intro!: measure_eqI s1.RN_deriv_unique  simp: emeasure_density emeasure_marginal_measure_on[OF nu_sets assms(8)]sets sets_marginal_measure)
  qed
  show ?thesis
    using 1 2 by auto
qed

end