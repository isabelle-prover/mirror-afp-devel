(*  Author:     Ata Keskin, TU München 
*)

section \<open>Updates for the entry Martingales\<close>

text \<open>This section contains the changes done for the entry Martingales \<^cite>\<open>"Martingales-AFP"\<close>. 
      We simplified the locale hierarchy by removing unnecessary locales and moving lemmas under more general locales where possible. 
      We have to redefine almost all of the constants, in order to make sure we use the new locale hierarchy. 
      The changes will be incorporated into the entry Martingales \<^cite>\<open>"Martingales-AFP"\<close> and this file will be removed when the next Isabelle version rolls out.\<close>

theory Martingales_Updates
imports Martingales.Martingale
begin

(* Fresh new updates for the entry Martingales. This file will be removed when the next Isabelle version comes out.  *)

subsection \<open>Updates for \<open>Martingales.Filtered_Measure\<close>\<close>

lemma (in filtered_measure) sets_F_subset[simp]: 
  assumes "t\<^sub>0 \<le> t"
  shows "sets (F t) \<subseteq> sets M"
  using subalgebras assms by (simp add: subalgebra_def)

locale linearly_filtered_measure = filtered_measure M F t\<^sub>0 for M and F :: "_ :: {linorder_topology, conditionally_complete_lattice} \<Rightarrow> _" and t\<^sub>0

context linearly_filtered_measure
begin

\<comment> \<open>We define \<open>F\<^sub>\<infinity>\<close> to be the smallest \<open>\<sigma>\<close>-algebra containing all the \<open>\<sigma>\<close>-algebras in the filtration.\<close>

definition F_infinity :: "'a measure" where 
  "F_infinity = sigma (space M) (\<Union>t\<in>{t\<^sub>0..}. sets (F t))"

notation F_infinity (\<open>F\<^sub>\<infinity>\<close>)

lemma space_F_infinity[simp]: "space F\<^sub>\<infinity> = space M" unfolding F_infinity_def space_measure_of_conv by simp

lemma sets_F_infinity: "sets F\<^sub>\<infinity> = sigma_sets (space M) (\<Union>t\<in>{t\<^sub>0..}. sets (F t))"
  unfolding F_infinity_def using sets.space_closed[of "F _"] space_F by (blast intro!: sets_measure_of)

lemma subset_F_infinity: 
  assumes "t \<ge> t\<^sub>0"
  shows "F t \<subseteq> F\<^sub>\<infinity>" unfolding sets_F_infinity using assms by blast

lemma F_infinity_subset: "F\<^sub>\<infinity> \<subseteq> M" 
  unfolding sets_F_infinity using sets_F_subset
  by (simp add: SUP_le_iff sets.sigma_sets_subset)

lemma F_infinity_measurableI:
  assumes "t \<ge> t\<^sub>0" "f \<in> borel_measurable (F t)"
  shows "f \<in> borel_measurable (F\<^sub>\<infinity>)"
  by (metis assms borel_measurable_subalgebra space_F space_F_infinity subset_F_infinity)

end

locale nat_filtered_measure = linearly_filtered_measure M F 0 for M and F :: "nat \<Rightarrow> _"
locale enat_filtered_measure = linearly_filtered_measure M F 0 for M and F :: "enat \<Rightarrow> _"
locale real_filtered_measure = linearly_filtered_measure M F 0 for M and F :: "real \<Rightarrow> _"
locale ennreal_filtered_measure = linearly_filtered_measure M F 0 for M and F :: "ennreal \<Rightarrow> _"

locale nat_sigma_finite_filtered_measure = sigma_finite_filtered_measure M F "0 :: nat" for M F
locale enat_sigma_finite_filtered_measure = sigma_finite_filtered_measure M F "0 :: enat" for M F
locale real_sigma_finite_filtered_measure = sigma_finite_filtered_measure M F "0 :: real" for M F
locale ennreal_sigma_finite_filtered_measure = sigma_finite_filtered_measure M F "0 :: ennreal" for M F

sublocale nat_sigma_finite_filtered_measure \<subseteq> nat_filtered_measure ..
sublocale enat_sigma_finite_filtered_measure \<subseteq> enat_filtered_measure ..
sublocale real_sigma_finite_filtered_measure \<subseteq> real_filtered_measure ..
sublocale ennreal_sigma_finite_filtered_measure \<subseteq> ennreal_filtered_measure ..

sublocale nat_sigma_finite_filtered_measure \<subseteq> sigma_finite_subalgebra M "F i" by blast
sublocale enat_sigma_finite_filtered_measure \<subseteq> sigma_finite_subalgebra M "F i" by fastforce
sublocale real_sigma_finite_filtered_measure \<subseteq> sigma_finite_subalgebra M "F \<bar>i\<bar>" by fastforce 
sublocale ennreal_sigma_finite_filtered_measure \<subseteq> sigma_finite_subalgebra M "F i" by fastforce

locale finite_filtered_measure = filtered_measure + finite_measure

sublocale finite_filtered_measure \<subseteq> sigma_finite_filtered_measure 
  using subalgebras by (unfold_locales, blast, meson dual_order.refl finite_measure_axioms finite_measure_def finite_measure_restr_to_subalg sigma_finite_measure.sigma_finite_countable)

locale nat_finite_filtered_measure = finite_filtered_measure M F "0 :: nat" for M F
locale enat_finite_filtered_measure = finite_filtered_measure M F "0 :: enat" for M F
locale real_finite_filtered_measure = finite_filtered_measure M F "0 :: real" for M F
locale ennreal_finite_filtered_measure = finite_filtered_measure M F "0 :: ennreal" for M F

sublocale nat_finite_filtered_measure \<subseteq> nat_sigma_finite_filtered_measure ..
sublocale enat_finite_filtered_measure \<subseteq> enat_sigma_finite_filtered_measure ..
sublocale real_finite_filtered_measure \<subseteq> real_sigma_finite_filtered_measure ..
sublocale ennreal_finite_filtered_measure \<subseteq> ennreal_sigma_finite_filtered_measure ..

subsection \<open>Updates for \<open>Martingales.Stochastic_Process\<close>\<close>

lemma (in nat_filtered_measure) partial_sum_Suc_adapted:
  assumes "adapted_process M F 0 X"
  shows "adapted_process M F 0 (\<lambda>n \<xi>. \<Sum>i<n. X (Suc i) \<xi>)"
proof (unfold_locales)
  interpret adapted_process M F 0 X using assms by blast
  fix i
  have "X j \<in> borel_measurable (F i)" if "j \<le> i" for j using that adaptedD by blast
  thus "(\<lambda>\<xi>. \<Sum>i<i. X (Suc i) \<xi>) \<in> borel_measurable (F i)" by auto
qed

lemma (in enat_filtered_measure) partial_sum_eSuc_adapted:
  assumes "adapted_process M F 0 X"
  shows "adapted_process M F 0 (\<lambda>n \<xi>. \<Sum>i<n. X (eSuc i) \<xi>)"
proof (unfold_locales)
  interpret adapted_process M F 0 X using assms by blast
  fix i
  have "X (eSuc j) \<in> borel_measurable (F i)" if "j < i" for j using that adaptedD by (simp add: ileI1)
  thus "(\<lambda>\<xi>. \<Sum>i<i. X (eSuc i) \<xi>) \<in> borel_measurable (F i)" by auto
qed

lemma (in filtered_measure) adapted_process_sum:
  assumes "\<And>i. i \<in> I \<Longrightarrow> adapted_process M F t\<^sub>0 (X i)"
  shows "adapted_process M F t\<^sub>0 (\<lambda>k \<xi>. \<Sum>i \<in> I. X i k \<xi>)" 
proof -
  {
    fix i k assume "i \<in> I" and asm: "t\<^sub>0 \<le> k"
    then interpret adapted_process M F t\<^sub>0 "X i" using assms by simp
    have "X i k \<in> borel_measurable M" "X i k \<in> borel_measurable (F k)" using measurable_from_subalg subalgebras adapted asm by (blast, simp)
  }
  thus ?thesis by (unfold_locales) simp
qed

context linearly_filtered_measure
begin

definition \<Sigma>\<^sub>P :: "('b \<times> 'a) measure" where predictable_sigma: "\<Sigma>\<^sub>P \<equiv> sigma ({t\<^sub>0..} \<times> space M) ({{s<..t} \<times> A | A s t. A \<in> F s \<and> t\<^sub>0 \<le> s \<and> s < t} \<union> {{t\<^sub>0} \<times> A | A. A \<in> F t\<^sub>0})"

lemma space_predictable_sigma[simp]: "space \<Sigma>\<^sub>P = ({t\<^sub>0..} \<times> space M)" unfolding predictable_sigma space_measure_of_conv by blast

lemma sets_predictable_sigma: "sets \<Sigma>\<^sub>P = sigma_sets ({t\<^sub>0..} \<times> space M) ({{s<..t} \<times> A | A s t. A \<in> F s \<and> t\<^sub>0 \<le> s \<and> s < t} \<union> {{t\<^sub>0} \<times> A | A. A \<in> F t\<^sub>0})" 
  unfolding predictable_sigma using space_F sets.sets_into_space by (subst sets_measure_of) fastforce+

lemma measurable_predictable_sigma_snd:
  assumes "countable \<I>" "\<I> \<subseteq> {{s<..t} | s t. t\<^sub>0 \<le> s \<and> s < t}" "{t\<^sub>0<..} \<subseteq> (\<Union>\<I>)"
  shows "snd \<in> \<Sigma>\<^sub>P \<rightarrow>\<^sub>M F t\<^sub>0"
proof (intro measurableI)
  fix S :: "'a set" assume asm: "S \<in> F t\<^sub>0"
  have countable: "countable ((\<lambda>I. I \<times> S) ` \<I>)" using assms(1) by blast
  have "(\<lambda>I. I \<times> S) ` \<I> \<subseteq> {{s<..t} \<times> A | A s t. A \<in> F s \<and> t\<^sub>0 \<le> s \<and>  s < t}" using sets_F_mono[OF order_refl, THEN subsetD, OF _ asm] assms(2) by blast
  hence "(\<Union>I\<in>\<I>. I \<times> S) \<union> {t\<^sub>0} \<times> S \<in> \<Sigma>\<^sub>P" unfolding sets_predictable_sigma using asm by (intro sigma_sets_Un[OF sigma_sets_UNION[OF countable] sigma_sets.Basic] sigma_sets.Basic) blast+
  moreover have "snd -` S \<inter> space \<Sigma>\<^sub>P = {t\<^sub>0..} \<times> S" using sets.sets_into_space[OF asm] by fastforce
  moreover have "{t\<^sub>0} \<union> {t\<^sub>0<..} = {t\<^sub>0..}" by auto
  moreover have "(\<Union>I\<in>\<I>. I \<times> S) \<union> {t\<^sub>0} \<times> S = {t\<^sub>0..} \<times> S" using assms(2,3) calculation(3) by fastforce
  ultimately show "snd -` S \<inter> space \<Sigma>\<^sub>P \<in> \<Sigma>\<^sub>P" by argo
qed (auto)

lemma measurable_predictable_sigma_fst:
  assumes "countable \<I>" "\<I> \<subseteq> {{s<..t} | s t. t\<^sub>0 \<le> s \<and> s < t}" "{t\<^sub>0<..} \<subseteq> (\<Union>\<I>)"
  shows "fst \<in> \<Sigma>\<^sub>P \<rightarrow>\<^sub>M borel"
proof -
  have "A \<times> space M \<in> sets \<Sigma>\<^sub>P" if "A \<in> sigma_sets {t\<^sub>0..} {{s<..t} | s t. t\<^sub>0 \<le> s \<and> s < t}" for A unfolding sets_predictable_sigma using that 
  proof (induction rule: sigma_sets.induct)
    case (Basic a)
    thus ?case using space_F sets.top by blast
  next
    case (Compl a)
    have "({t\<^sub>0..} - a) \<times> space M = {t\<^sub>0..} \<times> space M - a \<times> space M" by blast
    then show ?case using Compl(2)[THEN sigma_sets.Compl] by presburger
  next
    case (Union a)
    have "\<Union> (range a) \<times> space M = \<Union> (range (\<lambda>i. a i \<times> space M))" by blast
    then show ?case using Union(2)[THEN sigma_sets.Union] by presburger
  qed (auto)
  moreover have "restrict_space borel {t\<^sub>0..} = sigma {t\<^sub>0..} {{s<..t} | s t. t\<^sub>0 \<le> s \<and> s < t}"
  proof -
    have "sigma_sets {t\<^sub>0..} ((\<inter>) {t\<^sub>0..} ` sigma_sets UNIV (range greaterThan)) = sigma_sets {t\<^sub>0..} {{s<..t} |s t. t\<^sub>0 \<le> s \<and> s < t}"
    proof (intro sigma_sets_eqI ; clarify)
      fix A :: "'b set" assume asm: "A \<in> sigma_sets UNIV (range greaterThan)"
      thus "{t\<^sub>0..} \<inter> A \<in> sigma_sets {t\<^sub>0..} {{s<..t} |s t. t\<^sub>0 \<le> s \<and> s < t}"
      proof (induction rule: sigma_sets.induct)
        case (Basic a)
        then obtain s where s: "a = {s<..}" by blast
        show ?case
        proof (cases "t\<^sub>0 \<le> s")
          case True
          hence *: "{t\<^sub>0..} \<inter> a = (\<Union>i \<in> \<I>. {s<..} \<inter> i)" using s assms(3) by force
          have "((\<inter>) {s<..} ` \<I>) \<subseteq> sigma_sets {t\<^sub>0..} {{s<..t} | s t. t\<^sub>0 \<le> s \<and> s < t}"
          proof (clarify)
            fix A assume "A \<in> \<I>"
            then obtain s' t' where A: "A = {s'<..t'}" "t\<^sub>0 \<le> s'" "s' < t'" using assms(2) by blast
            hence "{s<..} \<inter> A = {max s s'<..t'}" by fastforce
            moreover have "t\<^sub>0 \<le> max s s'" using A True by linarith
            moreover have "max s s' < t'" if "s < t'" using A that by linarith
            moreover have "{s<..} \<inter> A = {}" if "\<not> s < t'" using A that by force
            ultimately show "{s<..} \<inter> A \<in> sigma_sets {t\<^sub>0..} {{s<..t} |s t. t\<^sub>0 \<le> s \<and> s < t}" by (cases "s < t'") (blast, simp add: sigma_sets.Empty)
          qed
          thus ?thesis unfolding * using assms(1) by (intro sigma_sets_UNION) auto
        next
          case False
          hence "{t\<^sub>0..} \<inter> a = {t\<^sub>0..}" using s by force
          thus ?thesis using sigma_sets_top by auto
        qed
      next
        case (Compl a)
        have "{t\<^sub>0..} \<inter> (UNIV - a) = {t\<^sub>0..} - ({t\<^sub>0..} \<inter> a)" by blast
        then show ?case using Compl(2)[THEN sigma_sets.Compl] by presburger
      next
        case (Union a)
        have "{t\<^sub>0..} \<inter> \<Union> (range a) = \<Union> (range (\<lambda>i. {t\<^sub>0..} \<inter> a i))" by blast
        then show ?case using Union(2)[THEN sigma_sets.Union] by presburger
      qed (simp add: sigma_sets.Empty)
    next 
      fix s t assume asm: "t\<^sub>0 \<le> s" "s < t"
      hence *: "{s<..t} = {s<..} \<inter> ({t\<^sub>0..} - {t<..})" by force
      have "{s<..} \<in> sigma_sets {t\<^sub>0..} ((\<inter>) {t\<^sub>0..} ` sigma_sets UNIV (range greaterThan))" using asm by (intro sigma_sets.Basic) auto
      moreover have "{t\<^sub>0..} - {t<..} \<in> sigma_sets {t\<^sub>0..} ((\<inter>) {t\<^sub>0..} ` sigma_sets UNIV (range greaterThan))" using asm by (intro sigma_sets.Compl sigma_sets.Basic) auto
      ultimately show "{s<..t} \<in> sigma_sets {t\<^sub>0..} ((\<inter>) {t\<^sub>0..} ` sigma_sets UNIV (range greaterThan))" unfolding * Int_range_binary[of "{s<..}"] by (intro sigma_sets_Inter[OF _ binary_in_sigma_sets]) auto        
    qed
    thus ?thesis unfolding borel_Ioi restrict_space_def emeasure_sigma by (force intro: sigma_eqI)
  qed
  ultimately have "restrict_space borel {t\<^sub>0..} \<Otimes>\<^sub>M sigma (space M) {} \<subseteq> sets \<Sigma>\<^sub>P" 
    unfolding sets_pair_measure space_restrict_space space_measure_of_conv
    using space_predictable_sigma sets.sigma_algebra_axioms[of \<Sigma>\<^sub>P] 
    by (intro sigma_algebra.sigma_sets_subset) (auto simp add: sigma_sets_empty_eq sets_measure_of_conv)
  moreover have "space (restrict_space borel {t\<^sub>0..} \<Otimes>\<^sub>M sigma (space M) {}) = space \<Sigma>\<^sub>P" by (simp add: space_pair_measure)
  moreover have "fst \<in> restrict_space borel {t\<^sub>0..} \<Otimes>\<^sub>M sigma (space M) {} \<rightarrow>\<^sub>M borel" by (fastforce intro: measurable_fst''[OF measurable_restrict_space1, of "\<lambda>x. x"]) 
  ultimately show ?thesis by (meson borel_measurable_subalgebra)
qed

end

locale predictable_process = linearly_filtered_measure M F t\<^sub>0 for M F t\<^sub>0 and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {second_countable_topology, banach}" +
  assumes predictable: "(\<lambda>(t, x). X t x) \<in> borel_measurable \<Sigma>\<^sub>P"
begin

lemmas predictableD = measurable_sets[OF predictable, unfolded space_predictable_sigma]

end

lemma (in nat_filtered_measure) measurable_predictable_sigma_snd':
  shows "snd \<in> \<Sigma>\<^sub>P \<rightarrow>\<^sub>M F 0"
  by (intro measurable_predictable_sigma_snd[of "range (\<lambda>x. {Suc x})"]) (force | simp add: greaterThan_0)+

lemma (in nat_filtered_measure) measurable_predictable_sigma_fst':
  shows "fst \<in> \<Sigma>\<^sub>P \<rightarrow>\<^sub>M borel"
  by (intro measurable_predictable_sigma_fst[of "range (\<lambda>x. {Suc x})"]) (force | simp add: greaterThan_0)+

lemma (in enat_filtered_measure) measurable_predictable_sigma_snd':
  shows "snd \<in> \<Sigma>\<^sub>P \<rightarrow>\<^sub>M F 0"
  by (intro measurable_predictable_sigma_snd[of "{{0<..\<infinity>}}"]) force+

lemma (in enat_filtered_measure) measurable_predictable_sigma_fst':
  shows "fst \<in> \<Sigma>\<^sub>P \<rightarrow>\<^sub>M borel"
  by (intro measurable_predictable_sigma_fst[of "{{0<..\<infinity>}}"]) force+

lemma (in real_filtered_measure) measurable_predictable_sigma_snd':
  shows "snd \<in> \<Sigma>\<^sub>P \<rightarrow>\<^sub>M F 0"
  using real_arch_simple by (intro measurable_predictable_sigma_snd[of "range (\<lambda>x::nat. {0<..real (Suc x)})"]) (fastforce intro: add_increasing)+

lemma (in real_filtered_measure) measurable_predictable_sigma_fst':
  shows "fst \<in> \<Sigma>\<^sub>P \<rightarrow>\<^sub>M borel"
  using real_arch_simple by (intro measurable_predictable_sigma_fst[of "range (\<lambda>x::nat. {0<..real (Suc x)})"]) (fastforce intro: add_increasing)+

lemma (in ennreal_filtered_measure) measurable_predictable_sigma_snd':
  shows "snd \<in> \<Sigma>\<^sub>P \<rightarrow>\<^sub>M F 0"
  by (intro measurable_predictable_sigma_snd[of "{{0<..\<infinity>}}"]) force+

lemma (in ennreal_filtered_measure) measurable_predictable_sigma_fst':
  shows "fst \<in> \<Sigma>\<^sub>P \<rightarrow>\<^sub>M borel"
  by (intro measurable_predictable_sigma_fst[of "{{0<..\<infinity>}}"]) force+

lemma (in linearly_filtered_measure) predictable_process_const_fun:
  assumes "snd \<in> \<Sigma>\<^sub>P \<rightarrow>\<^sub>M F t\<^sub>0" "f \<in> borel_measurable (F t\<^sub>0)"
    shows "predictable_process M F t\<^sub>0 (\<lambda>_. f)"
  using measurable_compose_rev[OF assms(2)] assms(1) by (unfold_locales) (auto simp add: measurable_split_conv)

lemma (in nat_filtered_measure) predictable_process_const_fun'[intro]:
  assumes "f \<in> borel_measurable (F 0)"
  shows "predictable_process M F 0 (\<lambda>_. f)"
  using assms by (intro predictable_process_const_fun[OF measurable_predictable_sigma_snd'])

lemma (in enat_filtered_measure) predictable_process_const_fun'[intro]:
  assumes "f \<in> borel_measurable (F 0)"
  shows "predictable_process M F 0 (\<lambda>_. f)"
  using assms by (intro predictable_process_const_fun[OF measurable_predictable_sigma_snd'])

lemma (in real_filtered_measure) predictable_process_const_fun'[intro]:
  assumes "f \<in> borel_measurable (F 0)"
  shows "predictable_process M F 0 (\<lambda>_. f)"
  using assms by (intro predictable_process_const_fun[OF measurable_predictable_sigma_snd'])

lemma (in ennreal_filtered_measure) predictable_process_const_fun'[intro]:
  assumes "f \<in> borel_measurable (F 0)"
  shows "predictable_process M F 0 (\<lambda>_. f)"
  using assms by (intro predictable_process_const_fun[OF measurable_predictable_sigma_snd'])

lemma (in linearly_filtered_measure) predictable_process_const:
  assumes "fst \<in> borel_measurable \<Sigma>\<^sub>P" "c \<in> borel_measurable borel"
  shows "predictable_process M F t\<^sub>0 (\<lambda>i _. c i)"
  using assms by (unfold_locales) (simp add: measurable_split_conv)

lemma (in linearly_filtered_measure) predictable_process_const_const[intro]:
  shows "predictable_process M F t\<^sub>0 (\<lambda>_ _. c)"
  by (unfold_locales) simp

lemma (in nat_filtered_measure) predictable_process_const'[intro]:
  assumes "c \<in> borel_measurable borel"
  shows "predictable_process M F 0 (\<lambda>i _. c i)"
  using assms by (intro predictable_process_const[OF measurable_predictable_sigma_fst'])

lemma (in enat_filtered_measure) predictable_process_const'[intro]:
  assumes "c \<in> borel_measurable borel"
  shows "predictable_process M F 0 (\<lambda>i _. c i)"
  using assms by (intro predictable_process_const[OF measurable_predictable_sigma_fst'])

lemma (in real_filtered_measure) predictable_process_const'[intro]:
  assumes "c \<in> borel_measurable borel"
  shows "predictable_process M F 0 (\<lambda>i _. c i)"
  using assms by (intro predictable_process_const[OF measurable_predictable_sigma_fst'])

lemma (in ennreal_filtered_measure) predictable_process_const'[intro]:
  assumes "c \<in> borel_measurable borel"
  shows "predictable_process M F 0 (\<lambda>i _. c i)"
  using assms by (intro predictable_process_const[OF measurable_predictable_sigma_fst'])

context predictable_process
begin

lemma compose_predictable:
  assumes "fst \<in> borel_measurable \<Sigma>\<^sub>P" "case_prod f \<in> borel_measurable borel"
  shows "predictable_process M F t\<^sub>0 (\<lambda>i \<xi>. (f i) (X i \<xi>))"
proof
  have "(\<lambda>(i, \<xi>). (i, X i \<xi>)) \<in> \<Sigma>\<^sub>P \<rightarrow>\<^sub>M borel \<Otimes>\<^sub>M borel" using predictable assms(1) by (auto simp add: measurable_pair_iff measurable_split_conv)
  moreover have "(\<lambda>(i, \<xi>). f i (X i \<xi>)) = case_prod f o (\<lambda>(i, \<xi>). (i, X i \<xi>))" by fastforce
  ultimately show "(\<lambda>(i, \<xi>). f i (X i \<xi>)) \<in> borel_measurable \<Sigma>\<^sub>P" unfolding borel_prod using assms by simp
qed

lemma norm_predictable: "predictable_process M F t\<^sub>0 (\<lambda>i \<xi>. norm (X i \<xi>))" using measurable_compose[OF predictable borel_measurable_norm] 
  by (unfold_locales) (simp add: prod.case_distrib)

lemma scaleR_right_predictable:
  assumes "predictable_process M F t\<^sub>0 R"
  shows "predictable_process M F t\<^sub>0 (\<lambda>i \<xi>. (R i \<xi>) *\<^sub>R (X i \<xi>))"
  using predictable predictable_process.predictable[OF assms] by (unfold_locales) (auto simp add: measurable_split_conv)

lemma scaleR_right_const_fun_predictable: 
  assumes "snd \<in> \<Sigma>\<^sub>P \<rightarrow>\<^sub>M F t\<^sub>0" "f \<in> borel_measurable (F t\<^sub>0)" 
  shows "predictable_process M F t\<^sub>0 (\<lambda>i \<xi>. f \<xi> *\<^sub>R (X i \<xi>))"
  using assms by (fast intro: scaleR_right_predictable predictable_process_const_fun)

lemma scaleR_right_const_predictable: 
  assumes "fst \<in> borel_measurable \<Sigma>\<^sub>P" "c \<in> borel_measurable borel"
  shows "predictable_process M F t\<^sub>0 (\<lambda>i \<xi>. c i *\<^sub>R (X i \<xi>))" 
  using assms by (fastforce intro: scaleR_right_predictable predictable_process_const)

lemma scaleR_right_const'_predictable: "predictable_process M F t\<^sub>0 (\<lambda>i \<xi>. c *\<^sub>R (X i \<xi>))" 
  by (fastforce intro: scaleR_right_predictable)

lemma add_predictable:
  assumes "predictable_process M F t\<^sub>0 Y"
  shows "predictable_process M F t\<^sub>0 (\<lambda>i \<xi>. X i \<xi> + Y i \<xi>)"
  using predictable predictable_process.predictable[OF assms] by (unfold_locales) (auto simp add: measurable_split_conv)

lemma diff_predictable:
  assumes "predictable_process M F t\<^sub>0 Y"
  shows "predictable_process M F t\<^sub>0 (\<lambda>i \<xi>. X i \<xi> - Y i \<xi>)"
  using predictable predictable_process.predictable[OF assms] by (unfold_locales) (auto simp add: measurable_split_conv)

lemma uminus_predictable: "predictable_process M F t\<^sub>0 (-X)" using scaleR_right_const'_predictable[of "-1"] by (simp add: fun_Compl_def)

end

sublocale predictable_process \<subseteq> progressive_process
proof (unfold_locales)
  fix i :: 'b assume asm: "t\<^sub>0 \<le> i"
  {
    fix S :: "('b \<times> 'a) set" assume "S \<in> {{s<..t} \<times> A | A s t. A \<in> F s \<and> t\<^sub>0 \<le> s \<and> s < t} \<union> {{t\<^sub>0} \<times> A | A. A \<in> F t\<^sub>0}"
    hence "(\<lambda>x. x) -` S \<inter> ({t\<^sub>0..i} \<times> space M) \<in> restrict_space borel {t\<^sub>0..i} \<Otimes>\<^sub>M F i"
    proof
      assume "S \<in> {{s<..t} \<times> A | A s t. A \<in> F s \<and> t\<^sub>0 \<le> s \<and> s < t}"
      then obtain s t A where S_is: "S = {s<..t} \<times> A" "t\<^sub>0 \<le> s" "s < t" "A \<in> F s" by blast
      hence "(\<lambda>x. x) -` S \<inter> ({t\<^sub>0..i} \<times> space M) = {s<..min i t} \<times> A" using sets.sets_into_space[OF S_is(4)] by auto
      then show ?thesis using S_is sets_F_mono[of s i] by (cases "s \<le> i") (fastforce simp add: sets_restrict_space_iff)+
    next
      assume "S \<in> {{t\<^sub>0} \<times> A | A. A \<in> F t\<^sub>0}"
      then obtain A where S_is: "S = {t\<^sub>0} \<times> A" "A \<in> F t\<^sub>0" by blast
      hence "(\<lambda>x. x) -` S \<inter> ({t\<^sub>0..i} \<times> space M) = {t\<^sub>0} \<times> A" using asm sets.sets_into_space[OF S_is(2)] by auto
      thus ?thesis using S_is(2) sets_F_mono[OF order_refl asm] asm by (fastforce simp add: sets_restrict_space_iff)
    qed
    hence "(\<lambda>x. x) -` S \<inter> space (restrict_space borel {t\<^sub>0..i} \<Otimes>\<^sub>M F i) \<in> restrict_space borel {t\<^sub>0..i} \<Otimes>\<^sub>M F i" by (simp add: space_pair_measure space_F[OF asm])
  }
  moreover have "{{s<..t} \<times> A |A s t. A \<in> sets (F s) \<and> t\<^sub>0 \<le> s \<and> s < t} \<union> {{t\<^sub>0} \<times> A |A. A \<in> sets (F t\<^sub>0)} \<subseteq> Pow ({t\<^sub>0..} \<times> space M)" using sets.sets_into_space by force
  ultimately have "(\<lambda>x. x) \<in> restrict_space borel {t\<^sub>0..i} \<Otimes>\<^sub>M F i \<rightarrow>\<^sub>M \<Sigma>\<^sub>P" using space_F[OF asm] by (intro measurable_sigma_sets[OF sets_predictable_sigma]) (fast, force simp add: space_pair_measure)
  thus "case_prod X \<in> borel_measurable (restrict_space borel {t\<^sub>0..i} \<Otimes>\<^sub>M F i)" using predictable by simp
qed

lemma (in nat_filtered_measure) sets_in_filtration:
  assumes "(\<Union>i. {i} \<times> A i) \<in> \<Sigma>\<^sub>P"
  shows "A (Suc i) \<in> F i" "A 0 \<in> F 0"
  using assms unfolding sets_predictable_sigma
proof (induction "(\<Union>i. {i} \<times> A i)" arbitrary: A)
  case Basic
  {
    assume "\<exists>S. (\<Union>i. {i} \<times> A i) = {0} \<times> S"
    then obtain S where S: "(\<Union>i. {i} \<times> A i) = {0} \<times> S" by blast
    hence "S \<in> F 0" using Basic by (fastforce simp add: times_eq_iff)
    moreover have "A i = {}" if "i \<noteq> 0" for i using that S unfolding bot_nat_def[symmetric] by blast
    moreover have "A 0 = S" using S by blast
    ultimately have "A 0 \<in> F 0" "A (Suc i) \<in> F i" for i by auto
  }
  note * = this
  {
    assume "\<nexists>S. (\<Union>i. {i} \<times> A i) = {0} \<times> S"
    then obtain s t B where B: "(\<Union>i. {i} \<times> A i) = {s<..t} \<times> B" "B \<in> sets (F s)" "s < t" using Basic by auto
    hence "A i = B" if "i \<in> {s<..t}" for i using that by fast
    moreover have "A i = {}" if "i \<notin> {s<..t}" for i using B that by fastforce
    ultimately have "A 0 \<in> F 0" "A (Suc i) \<in> F i" for i using B sets_F_mono 
      by (simp, metis less_Suc_eq_le sets.empty_sets subset_eq bot_nat_0.extremum greaterThanAtMost_iff)
      
  }
  note ** = this
  show "A (Suc i) \<in> sets (F i)" "A 0 \<in> F 0" using *(2)[of i] *(1) **(2)[of i] **(1) by blast+
next
  case Empty
  {
    case 1
    then show ?case using Empty by simp
  next
    case 2
    then show ?case using Empty by simp
  }
next
  case (Compl a)
  have a_in: "a \<subseteq> {0..} \<times> space M" using Compl(1) sets.sets_into_space sets_predictable_sigma space_predictable_sigma by metis
  hence A_in: "A i \<subseteq> space M" for i using Compl(4) by blast
  have a: "a = {0..} \<times> space M - (\<Union>i. {i} \<times> A i)" using a_in Compl(4) by blast
  also have "... = - (\<Inter>j. - ({j} \<times> (space M - A j)))" by blast
  also have "... = (\<Union>j. {j} \<times> (space M - A j))" by blast
  finally have *: "(space M - A (Suc i)) \<in> F i" "(space M - A 0) \<in> F 0" using Compl(2,3) by auto
  {
    case 1
    then show ?case using * A_in by (metis bot_nat_0.extremum double_diff sets.Diff sets.top sets_F_mono sets_le_imp_space_le space_F)
 next
    case 2
    then show ?case using * A_in by (metis bot_nat_0.extremum double_diff sets.Diff sets.top sets_F_mono sets_le_imp_space_le space_F)
  }
next
  case (Union a)
  have a_in: "a i \<subseteq> {0..} \<times> space M" for i using Union(1) sets.sets_into_space sets_predictable_sigma space_predictable_sigma by metis
  hence A_in: "A i \<subseteq> space M" for i using Union(4) by blast
  have "snd x \<in> snd ` (a i \<inter> ({fst x} \<times> space M))" if "x \<in> a i" for i x using that a_in by fastforce
  hence a_i: "a i = (\<Union>j. {j} \<times> (snd ` (a i \<inter> ({j} \<times> space M))))" for i by force
  have A_i: "A i = snd ` (\<Union> (range a) \<inter> ({i} \<times> space M))" for i unfolding Union(4) using A_in by force 
  have *: "snd ` (a j \<inter> ({Suc i} \<times> space M)) \<in> F i" "snd ` (a j \<inter> ({0} \<times> space M)) \<in> F 0" for j using Union(2,3)[OF a_i] by auto
  {
    case 1
    have "(\<Union>j. snd ` (a j \<inter> ({Suc i} \<times> space M))) \<in> F i" using * by fast
    moreover have "(\<Union>j. snd ` (a j \<inter> ({Suc i} \<times> space M))) = snd ` (\<Union> (range a) \<inter> ({Suc i} \<times> space M))" by fast
    ultimately show ?case using A_i by metis
  next
    case 2
    have "(\<Union>j. snd ` (a j \<inter> ({0} \<times> space M))) \<in> F 0" using * by fast
    moreover have "(\<Union>j. snd ` (a j \<inter> ({0} \<times> space M))) = snd ` (\<Union> (range a) \<inter> ({0} \<times> space M))" by fast
    ultimately show ?case using A_i by metis
  }
qed

lemma (in nat_filtered_measure) predictable_implies_adapted_Suc: 
  assumes "predictable_process M F 0 X"
  shows "adapted_process M F 0 (\<lambda>i. X (Suc i))"
proof (unfold_locales, intro borel_measurableI)
  interpret predictable_process M F 0 X by (rule assms)
  fix S :: "'b set" and i assume open_S: "open S"
  have "{Suc i} = {i<..Suc i}" by fastforce
  hence "{Suc i} \<times> space M \<in> \<Sigma>\<^sub>P" using space_F[symmetric, of i] unfolding sets_predictable_sigma by (intro sigma_sets.Basic) blast
  moreover have "case_prod X -` S \<inter> (UNIV \<times> space M) \<in> \<Sigma>\<^sub>P" unfolding atLeast_0[symmetric] using open_S by (intro predictableD, simp add: borel_open)
  ultimately have "case_prod X -` S \<inter> ({Suc i} \<times> space M) \<in> \<Sigma>\<^sub>P" unfolding sets_predictable_sigma using space_F sets.sets_into_space
    by (subst Times_Int_distrib1[of "{Suc i}" UNIV "space M", simplified], subst inf.commute, subst Int_assoc[symmetric], subst Int_range_binary) 
       (intro sigma_sets_Inter binary_in_sigma_sets, fast)+
  moreover have "case_prod X -` S \<inter> ({Suc i} \<times> space M) = {Suc i} \<times> (X (Suc i) -` S \<inter> space M)" by (auto simp add: le_Suc_eq)
  moreover have "... = (\<Union>j. {j} \<times> (if j = Suc i then (X (Suc i) -` S \<inter> space M) else {}))" by (force split: if_splits)
  ultimately have "(\<Union>j. {j} \<times> (if j = Suc i then (X (Suc i) -` S \<inter> space M) else {})) \<in> \<Sigma>\<^sub>P" by argo
  thus "X (Suc i) -` S \<inter> space (F i) \<in> sets (F i)" using sets_in_filtration[of "\<lambda>j. if j = Suc i then (X (Suc i) -` S \<inter> space M) else {}"] space_F[OF zero_le] by presburger
qed

theorem (in nat_filtered_measure) predictable_process_iff: "predictable_process M F 0 X \<longleftrightarrow> adapted_process M F 0 (\<lambda>i. X (Suc i)) \<and> X 0 \<in> borel_measurable (F 0)"
proof (intro iffI)
  assume asm: "adapted_process M F 0 (\<lambda>i. X (Suc i)) \<and> X 0 \<in> borel_measurable (F 0)"
  interpret adapted_process M F 0 "\<lambda>i. X (Suc i)" using asm by blast
  have "(\<lambda>(x, y). X x y) \<in> borel_measurable \<Sigma>\<^sub>P"
  proof (intro borel_measurableI)
    fix S :: "'b set" assume open_S: "open S"
    have "{i} \<times> (X i -` S \<inter> space M) \<in> sets \<Sigma>\<^sub>P" for i 
    proof (cases i)
      case 0
      then show ?thesis unfolding sets_predictable_sigma 
        using measurable_sets[OF _ borel_open[OF open_S], of "X 0" "F 0"] asm by auto
    next
      case (Suc i)
      have "{Suc i} = {i<..Suc i}" by fastforce
      then show ?thesis unfolding sets_predictable_sigma 
        using measurable_sets[OF adapted borel_open[OF open_S], of i] 
        by (intro sigma_sets.Basic, auto simp add: Suc)
    qed
    moreover have "(\<lambda>(x, y). X x y) -` S \<inter> space \<Sigma>\<^sub>P = (\<Union>i. {i} \<times> (X i -` S \<inter> space M))" by fastforce
    ultimately show "(\<lambda>(x, y). X x y) -` S \<inter> space \<Sigma>\<^sub>P \<in> sets \<Sigma>\<^sub>P" by simp
  qed
  thus "predictable_process M F 0 X" by (unfold_locales)
next
  assume asm: "predictable_process M F 0 X"
  interpret predictable_process M F 0 X using asm by blast
  show "adapted_process M F 0 (\<lambda>i. X (Suc i)) \<and> X 0 \<in> borel_measurable (F 0)" using predictable_implies_adapted_Suc asm by auto
qed

corollary (in nat_filtered_measure) predictable_processI[intro!]:
  assumes "X 0 \<in> borel_measurable (F 0)" "\<And>i. X (Suc i) \<in> borel_measurable (F i)"
  shows "predictable_process M F 0 X"
  unfolding predictable_process_iff
  using assms
  by (meson adapted_process.intro adapted_process_axioms_def filtered_measure_axioms)


subsection \<open>Updates for \<open>Martingales.Martingale\<close>\<close>

locale martingale = sigma_finite_filtered_measure + adapted_process +
  assumes integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)"
      and martingale_property: "\<And>i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X j) \<xi>"

locale martingale_order = martingale M F t\<^sub>0 X for M F t\<^sub>0 and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {order_topology, ordered_real_vector}"
locale martingale_linorder = martingale M F t\<^sub>0 X for M F t\<^sub>0 and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology, ordered_real_vector}"
sublocale martingale_linorder \<subseteq> martingale_order ..

lemma (in sigma_finite_filtered_measure) martingale_const_fun[intro]:  
  assumes "integrable M f" "f \<in> borel_measurable (F t\<^sub>0)"
  shows "martingale M F t\<^sub>0 (\<lambda>_. f)"
  using assms sigma_finite_subalgebra.cond_exp_F_meas[OF _ assms(1), THEN AE_symmetric] borel_measurable_mono
  by (unfold_locales) blast+

lemma (in sigma_finite_filtered_measure) martingale_cond_exp[intro]:  
  assumes "integrable M f"
  shows "martingale M F t\<^sub>0 (\<lambda>i. cond_exp M (F i) f)"
  using sigma_finite_subalgebra.borel_measurable_cond_exp' borel_measurable_cond_exp 
  by (unfold_locales) (auto intro: sigma_finite_subalgebra.cond_exp_nested_subalg[OF _ assms] simp add: subalgebra_F subalgebras)

corollary (in sigma_finite_filtered_measure) martingale_zero[intro]: "martingale M F t\<^sub>0 (\<lambda>_ _. 0)" by fastforce

corollary (in finite_filtered_measure) martingale_const[intro]: "martingale M F t\<^sub>0 (\<lambda>_ _. c)" by fastforce

locale submartingale = sigma_finite_filtered_measure M F t\<^sub>0 + adapted_process M F t\<^sub>0 X for M F t\<^sub>0 and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {order_topology, ordered_real_vector}" +
  assumes integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)"
      and submartingale_property: "\<And>i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X j) \<xi>"

locale submartingale_linorder = submartingale M F t\<^sub>0 X for M F t\<^sub>0 and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"

lemma (in sigma_finite_filtered_measure) submartingale_const_fun[intro]:  
  assumes "integrable M f" "f \<in> borel_measurable (F t\<^sub>0)"
  shows "submartingale M F t\<^sub>0 (\<lambda>_. f)"
proof -
  interpret martingale M F t\<^sub>0 "\<lambda>_. f" using assms by (rule martingale_const_fun)
  show "submartingale M F t\<^sub>0 (\<lambda>_. f)" using martingale_property by (unfold_locales) (force simp add: integrable)+
qed

lemma (in sigma_finite_filtered_measure) submartingale_cond_exp[intro]:  
  assumes "integrable M f"
  shows "submartingale M F t\<^sub>0 (\<lambda>i. cond_exp M (F i) f)"
proof -
  interpret martingale M F t\<^sub>0 "\<lambda>i. cond_exp M (F i) f" using assms by (rule martingale_cond_exp)
  show "submartingale M F t\<^sub>0 (\<lambda>i. cond_exp M (F i) f)" using martingale_property by (unfold_locales) (force simp add: integrable)+
qed

corollary (in finite_filtered_measure) submartingale_const[intro]: "submartingale M F t\<^sub>0 (\<lambda>_ _. c)" by fastforce

sublocale martingale_order \<subseteq> submartingale using martingale_property by (unfold_locales) (force simp add: integrable)+
sublocale martingale_linorder \<subseteq> submartingale_linorder ..

locale supermartingale = sigma_finite_filtered_measure M F t\<^sub>0 + adapted_process M F t\<^sub>0 X for M F t\<^sub>0 and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {order_topology, ordered_real_vector}" +
  assumes integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)"
      and supermartingale_property: "\<And>i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> AE \<xi> in M. X i \<xi> \<ge> cond_exp M (F i) (X j) \<xi>"

locale supermartingale_linorder = supermartingale M F t\<^sub>0 X for M F t\<^sub>0 and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"

lemma (in sigma_finite_filtered_measure) supermartingale_const_fun[intro]:  
  assumes "integrable M f" "f \<in> borel_measurable (F t\<^sub>0)"
  shows "supermartingale M F t\<^sub>0 (\<lambda>_. f)"
proof -
  interpret martingale M F t\<^sub>0 "\<lambda>_. f" using assms by (rule martingale_const_fun)
  show "supermartingale M F t\<^sub>0 (\<lambda>_. f)" using martingale_property by (unfold_locales) (force simp add: integrable)+
qed

lemma (in sigma_finite_filtered_measure) supermartingale_cond_exp[intro]:  
  assumes "integrable M f"
  shows "supermartingale M F t\<^sub>0 (\<lambda>i. cond_exp M (F i) f)"
proof -
  interpret martingale M F t\<^sub>0 "\<lambda>i. cond_exp M (F i) f" using assms by (rule martingale_cond_exp)
  show "supermartingale M F t\<^sub>0 (\<lambda>i. cond_exp M (F i) f)" using martingale_property by (unfold_locales) (force simp add: integrable)+
qed

corollary (in finite_filtered_measure) supermartingale_const[intro]: "supermartingale M F t\<^sub>0 (\<lambda>_ _. c)" by fastforce

sublocale martingale_order \<subseteq> supermartingale using martingale_property by (unfold_locales) (force simp add: integrable)+
sublocale martingale_linorder \<subseteq> supermartingale_linorder ..

lemma martingale_iff: 
  shows "martingale M F t\<^sub>0 X \<longleftrightarrow> submartingale M F t\<^sub>0 X \<and> supermartingale M F t\<^sub>0 X"
proof (rule iffI)
  assume asm: "martingale M F t\<^sub>0 X"
  interpret martingale_order M F t\<^sub>0 X by (intro martingale_order.intro asm)
  show "submartingale M F t\<^sub>0 X \<and> supermartingale M F t\<^sub>0 X" using submartingale_axioms supermartingale_axioms by blast
next
  assume asm: "submartingale M F t\<^sub>0 X \<and> supermartingale M F t\<^sub>0 X"
  interpret submartingale M F t\<^sub>0 X by (simp add: asm)
  interpret supermartingale M F t\<^sub>0 X by (simp add: asm)
  show "martingale M F t\<^sub>0 X" using submartingale_property supermartingale_property by (unfold_locales) (intro integrable, blast, force)
qed

context martingale
begin

lemma cond_exp_diff_eq_zero:
  assumes "t\<^sub>0 \<le> i" "i \<le> j"
  shows "AE \<xi> in M. cond_exp M (F i) (\<lambda>\<xi>. X j \<xi> - X i \<xi>) \<xi> = 0"
  using martingale_property[OF assms] assms
        sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable adapted, of i]
        sigma_finite_subalgebra.cond_exp_diff[OF _ integrable(1,1), of "F i" j i] by fastforce

lemma set_integral_eq:
  assumes "A \<in> F i" "t\<^sub>0 \<le> i" "i \<le> j"
  shows "set_lebesgue_integral M A (X i) = set_lebesgue_integral M A (X j)"
proof -
  interpret sigma_finite_subalgebra M "F i" using assms(2) by blast
  have "(\<integral>x \<in> A. X i x \<partial>M) = (\<integral>x \<in> A. cond_exp M (F i) (X j) x \<partial>M)" using martingale_property[OF assms(2,3)] borel_measurable_cond_exp' assms subalgebras subalgebra_def by (intro set_lebesgue_integral_cong_AE[OF _ random_variable]) fastforce+
  also have "... = (\<integral>x \<in> A. X j x \<partial>M)" using assms by (auto simp: integrable intro: cond_exp_set_integral[symmetric])
  finally show ?thesis .
qed

lemma scaleR_const[intro]:
  shows "martingale M F t\<^sub>0 (\<lambda>i x. c *\<^sub>R X i x)"
proof -
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    interpret sigma_finite_subalgebra M "F i" using asm by blast
    have "AE x in M. c *\<^sub>R X i x = cond_exp M (F i) (\<lambda>x. c *\<^sub>R X j x) x" using asm cond_exp_scaleR_right[OF integrable, of j, THEN AE_symmetric] martingale_property[OF asm] by force
  }
  thus ?thesis by (unfold_locales) (auto simp add: integrable martingale.integrable)
qed

lemma uminus[intro]:
  shows "martingale M F t\<^sub>0 (- X)" 
  using scaleR_const[of "-1"] by (force intro: back_subst[of "martingale M F t\<^sub>0"])

lemma add[intro]:
  assumes "martingale M F t\<^sub>0 Y"
  shows "martingale M F t\<^sub>0 (\<lambda>i \<xi>. X i \<xi> + Y i \<xi>)"
proof -
  interpret Y: martingale M F t\<^sub>0 Y by (rule assms)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    hence "AE \<xi> in M. X i \<xi> + Y i \<xi> = cond_exp M (F i) (\<lambda>x. X j x + Y j x) \<xi>" 
      using sigma_finite_subalgebra.cond_exp_add[OF _ integrable martingale.integrable[OF assms], of "F i" j j, THEN AE_symmetric]
            martingale_property[OF asm] martingale.martingale_property[OF assms asm] by force
  }
  thus ?thesis using assms
  by (unfold_locales) (auto simp add: integrable martingale.integrable)
qed

lemma diff[intro]:
  assumes "martingale M F t\<^sub>0 Y"
  shows "martingale M F t\<^sub>0 (\<lambda>i x. X i x - Y i x)"
proof -
  interpret Y: martingale M F t\<^sub>0 Y by (rule assms)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    hence "AE \<xi> in M. X i \<xi> - Y i \<xi> = cond_exp M (F i) (\<lambda>x. X j x - Y j x) \<xi>" 
      using sigma_finite_subalgebra.cond_exp_diff[OF _ integrable martingale.integrable[OF assms], of "F i" j j, THEN AE_symmetric] 
            martingale_property[OF asm] martingale.martingale_property[OF assms asm] by fastforce
  }
  thus ?thesis using assms by (unfold_locales) (auto simp add: integrable martingale.integrable)  
qed

end

lemma (in sigma_finite_filtered_measure) martingale_of_cond_exp_diff_eq_zero: 
  assumes adapted: "adapted_process M F t\<^sub>0 X"
      and integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)" 
      and diff_zero: "\<And>i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> AE x in M. cond_exp M (F i) (\<lambda>\<xi>. X j \<xi> - X i \<xi>) x = 0"
    shows "martingale M F t\<^sub>0 X"
proof
  interpret adapted_process M F t\<^sub>0 X by (rule adapted)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    thus "AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X j) \<xi>" 
      using diff_zero[OF asm] sigma_finite_subalgebra.cond_exp_diff[OF _ integrable(1,1), of "F i" j i] 
            sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable adapted, of i] by fastforce
  }
qed (auto intro: integrable adapted[THEN adapted_process.adapted])

lemma (in sigma_finite_filtered_measure) martingale_of_set_integral_eq:
  assumes adapted: "adapted_process M F t\<^sub>0 X"
      and integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)"
      and "\<And>A i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X i) = set_lebesgue_integral M A (X j)" 
    shows "martingale M F t\<^sub>0 X"
proof (unfold_locales)
  fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
  interpret adapted_process M F t\<^sub>0 X by (rule adapted)
  interpret sigma_finite_subalgebra M "F i" using asm by blast
  interpret r: sigma_finite_measure "restr_to_subalg M (F i)" by (simp add: sigma_fin_subalg)
  {
    fix A assume "A \<in> restr_to_subalg M (F i)"
    hence *: "A \<in> F i" using sets_restr_to_subalg subalgebras asm by blast 
    have "set_lebesgue_integral (restr_to_subalg M (F i)) A (X i) = set_lebesgue_integral M A (X i)" using * subalg asm by (auto simp: set_lebesgue_integral_def intro: integral_subalgebra2 borel_measurable_scaleR adapted borel_measurable_indicator) 
    also have "... = set_lebesgue_integral M A (cond_exp M (F i) (X j))" using * assms(3)[OF asm] cond_exp_set_integral[OF integrable] asm by auto
    finally have "set_lebesgue_integral (restr_to_subalg M (F i)) A (X i) = set_lebesgue_integral (restr_to_subalg M (F i)) A (cond_exp M (F i) (X j))" using * subalg by (auto simp: set_lebesgue_integral_def intro!: integral_subalgebra2[symmetric] borel_measurable_scaleR borel_measurable_cond_exp borel_measurable_indicator)
  }
  hence "AE \<xi> in restr_to_subalg M (F i). X i \<xi> = cond_exp M (F i) (X j) \<xi>" using asm by (intro r.density_unique_banach, auto intro: integrable_in_subalg subalg borel_measurable_cond_exp integrable)
  thus "AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X j) \<xi>" using AE_restr_to_subalg[OF subalg] by blast
qed (auto intro: integrable adapted[THEN adapted_process.adapted])

context submartingale
begin

lemma cond_exp_diff_nonneg:
  assumes "t\<^sub>0 \<le> i" "i \<le> j"
  shows "AE x in M. cond_exp M (F i) (\<lambda>\<xi>. X j \<xi> - X i \<xi>) x \<ge> 0"
  using submartingale_property[OF assms] assms sigma_finite_subalgebra.cond_exp_diff[OF _ integrable(1,1), of _ j i] sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable adapted, of i] by fastforce

lemma add[intro]:
  assumes "submartingale M F t\<^sub>0 Y"
  shows "submartingale M F t\<^sub>0 (\<lambda>i \<xi>. X i \<xi> + Y i \<xi>)"
proof -
  interpret Y: submartingale M F t\<^sub>0 Y by (rule assms)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    hence "AE \<xi> in M. X i \<xi> + Y i \<xi> \<le> cond_exp M (F i) (\<lambda>x. X j x + Y j x) \<xi>" 
      using sigma_finite_subalgebra.cond_exp_add[OF _ integrable submartingale.integrable[OF assms], of "F i" j j] 
            submartingale_property[OF asm] submartingale.submartingale_property[OF assms asm] add_mono[of "X i _" _ "Y i _"] by force
  }
  thus ?thesis using assms by (unfold_locales) (auto simp add: borel_measurable_add random_variable adapted integrable Y.random_variable Y.adapted submartingale.integrable)  
qed

lemma diff[intro]:
  assumes "supermartingale M F t\<^sub>0 Y"
  shows "submartingale M F t\<^sub>0 (\<lambda>i \<xi>. X i \<xi> - Y i \<xi>)"
proof -
  interpret Y: supermartingale M F t\<^sub>0 Y by (rule assms)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    hence "AE \<xi> in M. X i \<xi> - Y i \<xi> \<le> cond_exp M (F i) (\<lambda>x. X j x - Y j x) \<xi>" 
      using sigma_finite_subalgebra.cond_exp_diff[OF _ integrable supermartingale.integrable[OF assms], of "F i" j j] 
            submartingale_property[OF asm] supermartingale.supermartingale_property[OF assms asm] diff_mono[of "X i _" _ _ "Y i _"] by force
  }
  thus ?thesis using assms by (unfold_locales) (auto simp add: borel_measurable_diff random_variable adapted integrable Y.random_variable Y.adapted supermartingale.integrable)  
qed

lemma scaleR_nonneg: 
  assumes "c \<ge> 0"
  shows "submartingale M F t\<^sub>0 (\<lambda>i \<xi>. c *\<^sub>R X i \<xi>)"
proof
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    thus "AE \<xi> in M. c *\<^sub>R X i \<xi> \<le> cond_exp M (F i) (\<lambda>\<xi>. c *\<^sub>R X j \<xi>) \<xi>"  
      using sigma_finite_subalgebra.cond_exp_scaleR_right[OF _ integrable, of "F i" j c] submartingale_property[OF asm] by (fastforce intro!: scaleR_left_mono[OF _ assms])
  }
qed (auto simp add: borel_measurable_integrable borel_measurable_scaleR integrable random_variable adapted borel_measurable_const_scaleR)

lemma scaleR_le_zero: 
  assumes "c \<le> 0"
  shows "supermartingale M F t\<^sub>0 (\<lambda>i \<xi>. c *\<^sub>R X i \<xi>)"
proof
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    thus "AE \<xi> in M. c *\<^sub>R X i \<xi> \<ge> cond_exp M (F i) (\<lambda>\<xi>. c *\<^sub>R X j \<xi>) \<xi>" 
      using sigma_finite_subalgebra.cond_exp_scaleR_right[OF _ integrable, of "F i" j c] submartingale_property[OF asm] 
            by (fastforce intro!: scaleR_left_mono_neg[OF _ assms])
  }
qed (auto simp add: borel_measurable_integrable borel_measurable_scaleR integrable random_variable adapted borel_measurable_const_scaleR)

lemma uminus[intro]:
  shows "supermartingale M F t\<^sub>0 (- X)"
  unfolding fun_Compl_def using scaleR_le_zero[of "-1"] by simp

end

context submartingale_linorder
begin

lemma set_integral_le:
  assumes "A \<in> F i" "t\<^sub>0 \<le> i" "i \<le> j"
  shows "set_lebesgue_integral M A (X i) \<le> set_lebesgue_integral M A (X j)"  
  using submartingale_property[OF assms(2), of j] assms subsetD[OF sets_F_subset]
  by (subst sigma_finite_subalgebra.cond_exp_set_integral[OF _ integrable assms(1), of j])
     (auto intro!: scaleR_left_mono integral_mono_AE_banach integrable_mult_indicator integrable simp add: set_lebesgue_integral_def)

lemma max:
  assumes "submartingale M F t\<^sub>0 Y"
  shows "submartingale M F t\<^sub>0 (\<lambda>i \<xi>. max (X i \<xi>) (Y i \<xi>))"
proof (unfold_locales)
  interpret Y: submartingale_linorder M F t\<^sub>0 Y by (intro submartingale_linorder.intro assms)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    have "AE \<xi> in M. max (X i \<xi>) (Y i \<xi>) \<le> max (cond_exp M (F i) (X j) \<xi>) (cond_exp M (F i) (Y j) \<xi>)"
      using submartingale_property[of i j] Y.submartingale_property[of i j] asm
      unfolding max_def by fastforce
    thus "AE \<xi> in M. max (X i \<xi>) (Y i \<xi>) \<le> cond_exp M (F i) (\<lambda>\<xi>. max (X j \<xi>) (Y j \<xi>)) \<xi>"
      using sigma_finite_subalgebra.cond_exp_max[OF _ integrable Y.integrable, of "F i" j j] asm
      by (fast intro: order.trans)
  }
  show "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> (\<lambda>\<xi>. max (X i \<xi>) (Y i \<xi>)) \<in> borel_measurable (F i)" "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (\<lambda>\<xi>. max (X i \<xi>) (Y i \<xi>))" by (force intro: Y.integrable integrable assms)+
qed

lemma max_0:
  shows "submartingale M F t\<^sub>0 (\<lambda>i \<xi>. max 0 (X i \<xi>))"
proof -
  interpret zero: martingale_linorder M F t\<^sub>0 "\<lambda>_ _. 0" by (force intro: martingale_linorder.intro martingale_order.intro)
  show ?thesis by (intro zero.max submartingale_linorder.intro submartingale_axioms)
qed

end

lemma (in sigma_finite_filtered_measure) submartingale_of_cond_exp_diff_nonneg:
  assumes adapted: "adapted_process M F t\<^sub>0 X"
      and integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow>  integrable M (X i)" 
      and diff_nonneg: "\<And>i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> AE x in M. cond_exp M (F i) (\<lambda>\<xi>. X j \<xi> - X i \<xi>) x \<ge> 0"
    shows "submartingale M F t\<^sub>0 X"
proof (unfold_locales)
  interpret adapted_process M F t\<^sub>0 X by (rule adapted)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    thus "AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X j) \<xi>" 
      using diff_nonneg[OF asm] sigma_finite_subalgebra.cond_exp_diff[OF _ integrable(1,1), of "F i" j i]
            sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable adapted, of i] by fastforce
  }
qed (auto intro: integrable adapted[THEN adapted_process.adapted])

lemma (in sigma_finite_filtered_measure) submartingale_of_set_integral_le:
  fixes X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"
  assumes adapted: "adapted_process M F t\<^sub>0 X"
      and integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)"
      and "\<And>A i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X i) \<le> set_lebesgue_integral M A (X j)"
    shows "submartingale M F t\<^sub>0 X"
proof (unfold_locales)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    interpret adapted_process M F t\<^sub>0 X by (rule adapted)
    interpret r: sigma_finite_measure "restr_to_subalg M (F i)" using asm sigma_finite_subalgebra.sigma_fin_subalg by blast
    {
      fix A assume "A \<in> restr_to_subalg M (F i)"
      hence *: "A \<in> F i" using asm sets_restr_to_subalg subalgebras by blast
      have "set_lebesgue_integral (restr_to_subalg M (F i)) A (X i) = set_lebesgue_integral M A (X i)" using * asm subalgebras by (auto simp: set_lebesgue_integral_def intro: integral_subalgebra2 borel_measurable_scaleR adapted borel_measurable_indicator) 
      also have "... \<le> set_lebesgue_integral M A (cond_exp M (F i) (X j))" using * assms(3)[OF asm] asm sigma_finite_subalgebra.cond_exp_set_integral[OF _ integrable] by fastforce
      also have "... = set_lebesgue_integral (restr_to_subalg M (F i)) A (cond_exp M (F i) (X j))" using * asm subalgebras by (auto simp: set_lebesgue_integral_def intro!: integral_subalgebra2[symmetric] borel_measurable_scaleR borel_measurable_cond_exp borel_measurable_indicator)
      finally have "0 \<le> set_lebesgue_integral (restr_to_subalg M (F i)) A (\<lambda>\<xi>. cond_exp M (F i) (X j) \<xi> - X i \<xi>)" using * asm subalgebras by (subst set_integral_diff, auto simp add: set_integrable_def sets_restr_to_subalg intro!: integrable adapted integrable_in_subalg borel_measurable_scaleR borel_measurable_indicator borel_measurable_cond_exp integrable_mult_indicator)
    }
    hence "AE \<xi> in restr_to_subalg M (F i). 0 \<le> cond_exp M (F i) (X j) \<xi> - X i \<xi>"
      by (intro r.density_nonneg integrable_in_subalg asm subalgebras borel_measurable_diff borel_measurable_cond_exp adapted Bochner_Integration.integrable_diff integrable_cond_exp integrable)  
    thus "AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X j) \<xi>" using AE_restr_to_subalg[OF subalgebras] asm by simp
  }
qed (auto intro: integrable adapted[THEN adapted_process.adapted])

context supermartingale
begin

lemma cond_exp_diff_nonneg:
  assumes "t\<^sub>0 \<le> i" "i \<le> j"
  shows "AE x in M. cond_exp M (F i) (\<lambda>\<xi>. X i \<xi> - X j \<xi>) x \<ge> 0"
  using assms supermartingale_property[OF assms] sigma_finite_subalgebra.cond_exp_diff[OF _ integrable(1,1), of "F i" i j] 
        sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable adapted, of i] by fastforce

lemma add[intro]:
  assumes "supermartingale M F t\<^sub>0 Y"
  shows "supermartingale M F t\<^sub>0 (\<lambda>i \<xi>. X i \<xi> + Y i \<xi>)"
proof -
  interpret Y: supermartingale M F t\<^sub>0 Y by (rule assms)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    hence "AE \<xi> in M. X i \<xi> + Y i \<xi> \<ge> cond_exp M (F i) (\<lambda>x. X j x + Y j x) \<xi>" 
      using sigma_finite_subalgebra.cond_exp_add[OF _ integrable supermartingale.integrable[OF assms], of "F i" j j] 
            supermartingale_property[OF asm] supermartingale.supermartingale_property[OF assms asm] add_mono[of _ "X i _" _ "Y i _"] by force
  }
  thus ?thesis using assms by (unfold_locales) (auto simp add: borel_measurable_add random_variable adapted integrable Y.random_variable Y.adapted supermartingale.integrable)  
qed

lemma diff[intro]:
  assumes "submartingale M F t\<^sub>0 Y"
  shows "supermartingale M F t\<^sub>0 (\<lambda>i \<xi>. X i \<xi> - Y i \<xi>)"
proof -
  interpret Y: submartingale M F t\<^sub>0 Y by (rule assms)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    hence "AE \<xi> in M. X i \<xi> - Y i \<xi> \<ge> cond_exp M (F i) (\<lambda>x. X j x - Y j x) \<xi>" 
      using sigma_finite_subalgebra.cond_exp_diff[OF _ integrable submartingale.integrable[OF assms], of "F i" j j, unfolded fun_diff_def] 
            supermartingale_property[OF asm] submartingale.submartingale_property[OF assms asm] diff_mono[of _ "X i _" "Y i _"] by force
  }
  thus ?thesis using assms by (unfold_locales) (auto simp add: borel_measurable_diff random_variable adapted integrable Y.random_variable Y.adapted submartingale.integrable)  
qed

lemma scaleR_nonneg: 
  assumes "c \<ge> 0"
  shows "supermartingale M F t\<^sub>0 (\<lambda>i \<xi>. c *\<^sub>R X i \<xi>)"
proof
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    thus "AE \<xi> in M. c *\<^sub>R X i \<xi> \<ge> cond_exp M (F i) (\<lambda>\<xi>. c *\<^sub>R X j \<xi>) \<xi>"
      using sigma_finite_subalgebra.cond_exp_scaleR_right[OF _ integrable, of "F i" j c] supermartingale_property[OF asm] by (fastforce intro!: scaleR_left_mono[OF _ assms])
  }
qed (auto simp add: borel_measurable_integrable borel_measurable_scaleR integrable random_variable adapted borel_measurable_const_scaleR)

lemma scaleR_le_zero: 
  assumes "c \<le> 0"
  shows "submartingale M F t\<^sub>0 (\<lambda>i \<xi>. c *\<^sub>R X i \<xi>)"
proof
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    thus "AE \<xi> in M. c *\<^sub>R X i \<xi> \<le> cond_exp M (F i) (\<lambda>\<xi>. c *\<^sub>R X j \<xi>) \<xi>" 
      using sigma_finite_subalgebra.cond_exp_scaleR_right[OF _ integrable, of "F i" j c] supermartingale_property[OF asm] by (fastforce intro!: scaleR_left_mono_neg[OF _ assms])
  }
qed (auto simp add: borel_measurable_integrable borel_measurable_scaleR integrable random_variable adapted borel_measurable_const_scaleR)

lemma uminus[intro]:
  shows "submartingale M F t\<^sub>0 (- X)"
  unfolding fun_Compl_def using scaleR_le_zero[of "-1"] by simp

end

context supermartingale_linorder
begin

lemma set_integral_ge:
  assumes "A \<in> F i" "t\<^sub>0 \<le> i" "i \<le> j"
  shows "set_lebesgue_integral M A (X i) \<ge> set_lebesgue_integral M A (X j)"
  using supermartingale_property[OF assms(2), of j] assms subsetD[OF sets_F_subset]
  by (subst sigma_finite_subalgebra.cond_exp_set_integral[OF _ integrable assms(1), of j])
     (auto intro!: scaleR_left_mono integral_mono_AE_banach integrable_mult_indicator integrable simp add: set_lebesgue_integral_def)

lemma min:
  assumes "supermartingale M F t\<^sub>0 Y"
  shows "supermartingale M F t\<^sub>0 (\<lambda>i \<xi>. min (X i \<xi>) (Y i \<xi>))"
proof (unfold_locales)
  interpret Y: supermartingale_linorder M F t\<^sub>0 Y by (intro supermartingale_linorder.intro assms)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    have "AE \<xi> in M. min (X i \<xi>) (Y i \<xi>) \<ge> min (cond_exp M (F i) (X j) \<xi>) (cond_exp M (F i) (Y j) \<xi>)"
      using supermartingale_property[of i j] Y.supermartingale_property[of i j] asm
      unfolding min_def by fastforce
    thus "AE \<xi> in M. min (X i \<xi>) (Y i \<xi>) \<ge> cond_exp M (F i) (\<lambda>\<xi>. min (X j \<xi>) (Y j \<xi>)) \<xi>"
      using sigma_finite_subalgebra.cond_exp_min[OF _ integrable Y.integrable, of "F i" j j] asm by (fast intro: order.trans)
  }
  show "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> (\<lambda>\<xi>. min (X i \<xi>) (Y i \<xi>)) \<in> borel_measurable (F i)" "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (\<lambda>\<xi>. min (X i \<xi>) (Y i \<xi>))" by (force intro: Y.integrable integrable assms)+
qed

lemma min_0:
  shows "supermartingale M F t\<^sub>0 (\<lambda>i \<xi>. min 0 (X i \<xi>))"
proof -
  interpret zero: martingale_linorder M F t\<^sub>0 "\<lambda>_ _. 0" by (force intro: martingale_linorder.intro)
  show ?thesis by (intro zero.min supermartingale_linorder.intro supermartingale_axioms)
qed

end

lemma (in sigma_finite_filtered_measure) supermartingale_of_cond_exp_diff_le_zero:
  assumes adapted: "adapted_process M F t\<^sub>0 X"
      and integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)" 
      and diff_le_zero: "\<And>i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> AE x in M. cond_exp M (F i) (\<lambda>\<xi>. X j \<xi> - X i \<xi>) x \<le> 0"
    shows "supermartingale M F t\<^sub>0 X"
proof 
  interpret adapted_process M F t\<^sub>0 X by (rule adapted)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    thus "AE \<xi> in M. X i \<xi> \<ge> cond_exp M (F i) (X j) \<xi>" 
      using diff_le_zero[OF asm] sigma_finite_subalgebra.cond_exp_diff[OF _ integrable(1,1), of "F i" j i] 
            sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable adapted, of i] by fastforce
  }
qed (auto intro: integrable adapted[THEN adapted_process.adapted])

lemma (in sigma_finite_filtered_measure) supermartingale_of_set_integral_ge:
  fixes X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"
  assumes adapted: "adapted_process M F t\<^sub>0 X"
      and integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)" 
      and "\<And>A i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X j) \<le> set_lebesgue_integral M A (X i)" 
    shows "supermartingale M F t\<^sub>0 X"
proof -
  interpret adapted_process M F t\<^sub>0 X by (rule adapted)
  note * = set_integral_uminus[unfolded set_integrable_def, OF integrable_mult_indicator[OF _ integrable]]
  have "supermartingale M F t\<^sub>0 (-(- X))"
    using ord_eq_le_trans[OF * ord_le_eq_trans[OF le_imp_neg_le[OF assms(3)] *[symmetric]]] sets_F_subset[THEN subsetD]
    by (intro submartingale.uminus submartingale_of_set_integral_le[OF uminus_adapted]) 
       (clarsimp simp add: fun_Compl_def integrable | fastforce)+
  thus ?thesis unfolding fun_Compl_def by simp
qed

context nat_sigma_finite_filtered_measure
begin

lemma predictable_const:
  assumes "martingale M F 0 X" 
    and "predictable_process M F 0 X"
  shows "AE \<xi> in M. X i \<xi> = X j \<xi>"
proof -
  interpret martingale M F 0 X by (rule assms)
  have *: "AE \<xi> in M. X i \<xi> = X 0 \<xi>" for i
  proof (induction i)
    case 0
    then show ?case by (simp add: bot_nat_def)
  next
    case (Suc i)
    interpret S: adapted_process M F 0 "\<lambda>i. X (Suc i)" by (intro predictable_implies_adapted_Suc assms)
    show ?case using Suc S.adapted[of i] martingale_property[OF _ le_SucI, of i] sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable, of "F i" "Suc i"] by fastforce
  qed
  show ?thesis using *[of i] *[of j] by force
qed

lemma martingale_of_set_integral_eq_Suc:
  assumes adapted: "adapted_process M F 0 X"
      and integrable: "\<And>i. integrable M (X i)"
      and "\<And>A i. A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X i) = set_lebesgue_integral M A (X (Suc i))" 
    shows "martingale M F 0 X"
proof (intro martingale_of_set_integral_eq adapted integrable)
  fix i j A assume asm: "i \<le> j" "A \<in> sets (F i)"
  show "set_lebesgue_integral M A (X i) = set_lebesgue_integral M A (X j)" using asm
  proof (induction "j - i" arbitrary: i j)
    case 0
    then show ?case using asm by simp
  next
    case (Suc n)
    hence *: "n = j - Suc i" by linarith
    have "Suc i \<le> j" using Suc(2,3) by linarith
    thus ?case using sets_F_mono[OF _ le_SucI] Suc(4) Suc(1)[OF *] by (auto intro: assms(3)[THEN trans])
  qed
qed

lemma martingale_nat:
  assumes adapted: "adapted_process M F 0 X"
      and integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X (Suc i)) \<xi>" 
    shows "martingale M F 0 X"
proof (unfold_locales)
  interpret adapted_process M F 0 X by (rule adapted)
  fix i j :: nat assume asm: "i \<le> j"
  show "AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X j) \<xi>" using asm
  proof (induction "j - i" arbitrary: i j)
    case 0
    hence "j = i" by simp
    thus ?case using sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable adapted, THEN AE_symmetric] by blast
  next
    case (Suc n)
    have j: "j = Suc (n + i)" using Suc by linarith
    have n: "n = n + i - i" using Suc by linarith
    have *: "AE \<xi> in M. cond_exp M (F (n + i)) (X j) \<xi> = X (n + i) \<xi>" unfolding j using assms(3)[THEN AE_symmetric] by blast
    have "AE \<xi> in M. cond_exp M (F i) (X j) \<xi> = cond_exp M (F i) (cond_exp M (F (n + i)) (X j)) \<xi>" by (intro cond_exp_nested_subalg integrable subalg, simp add: subalgebra_def sets_F_mono)
    hence "AE \<xi> in M. cond_exp M (F i) (X j) \<xi> = cond_exp M (F i) (X (n + i)) \<xi>" using cond_exp_cong_AE[OF integrable_cond_exp integrable *] by force
    thus ?case using Suc(1)[OF n] by fastforce
  qed
qed (auto simp add: integrable adapted[THEN adapted_process.adapted])

lemma martingale_of_cond_exp_diff_Suc_eq_zero:
  assumes adapted: "adapted_process M F 0 X"
      and integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. cond_exp M (F i) (\<lambda>\<xi>. X (Suc i) \<xi> - X i \<xi>) \<xi> = 0" 
    shows "martingale M F 0 X"
proof (intro martingale_nat integrable adapted)
  interpret adapted_process M F 0 X by (rule adapted)
  fix i 
  show "AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X (Suc i)) \<xi>" using cond_exp_diff[OF integrable(1,1), of i "Suc i" i] cond_exp_F_meas[OF integrable adapted, of i] assms(3)[of i] by fastforce
qed

end

context nat_sigma_finite_filtered_measure
begin

lemma predictable_mono:
  assumes "submartingale M F 0 X"
    and "predictable_process M F 0 X" "i \<le> j"
  shows "AE \<xi> in M. X i \<xi> \<le> X j \<xi>"
  using assms(3)
proof (induction "j - i" arbitrary: i j)
  case 0
  then show ?case by simp 
next
  case (Suc n)
  hence *: "n = j - Suc i" by linarith
  interpret submartingale M F 0 X by (rule assms)
  interpret S: adapted_process M F 0 "\<lambda>i. X (Suc i)" by (intro predictable_implies_adapted_Suc assms)
  have "Suc i \<le> j" using Suc(2,3) by linarith
  thus ?case using Suc(1)[OF *] S.adapted[of i] submartingale_property[OF _ le_SucI, of i] sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable, of "F i" "Suc i"] by fastforce
qed

lemma submartingale_of_set_integral_le_Suc:
  fixes X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"
  assumes adapted: "adapted_process M F 0 X"
      and integrable: "\<And>i. integrable M (X i)" 
      and "\<And>A i. A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X i) \<le> set_lebesgue_integral M A (X (Suc i))" 
    shows "submartingale M F 0 X"
proof (intro submartingale_of_set_integral_le adapted integrable)
  fix i j A assume asm: "i \<le> j" "A \<in> sets (F i)"
  show "set_lebesgue_integral M A (X i) \<le> set_lebesgue_integral M A (X j)" using asm
  proof (induction "j - i" arbitrary: i j)
    case 0
    then show ?case using asm by simp
  next
    case (Suc n)
    hence *: "n = j - Suc i" by linarith
    have "Suc i \<le> j" using Suc(2,3) by linarith
    thus ?case using sets_F_mono[OF _ le_SucI] Suc(4) Suc(1)[OF *] by (auto intro: assms(3)[THEN order_trans])
  qed
qed

lemma submartingale_nat:
  fixes X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"
  assumes adapted: "adapted_process M F 0 X"
      and integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X (Suc i)) \<xi>" 
    shows "submartingale M F 0 X"
proof -
  show ?thesis using subalg assms(3) integrable
    by (intro submartingale_of_set_integral_le_Suc adapted integrable ord_le_eq_trans[OF set_integral_mono_AE_banach cond_exp_set_integral[symmetric]])
       (meson in_mono integrable_mult_indicator set_integrable_def subalgebra_def, meson integrable_cond_exp in_mono integrable_mult_indicator set_integrable_def subalgebra_def, fast+)
qed

lemma submartingale_of_cond_exp_diff_Suc_nonneg:
  fixes X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"
  assumes adapted: "adapted_process M F 0 X"
      and integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. cond_exp M (F i) (\<lambda>\<xi>. X (Suc i) \<xi> - X i \<xi>) \<xi> \<ge> 0" 
    shows "submartingale M F 0 X"
proof (intro submartingale_nat integrable adapted)
  interpret adapted_process M F 0 X by (rule assms)
  fix i 
  show "AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X (Suc i)) \<xi>" using cond_exp_diff[OF integrable(1,1), of i "Suc i" i] cond_exp_F_meas[OF integrable adapted, of i] assms(3)[of i] by fastforce
qed

lemma submartingale_partial_sum_scaleR:
  assumes "submartingale_linorder M F 0 X"
    and "adapted_process M F 0 C" "\<And>i. AE \<xi> in M. 0 \<le> C i \<xi>" "\<And>i. AE \<xi> in M. C i \<xi> \<le> R"
  shows "submartingale M F 0 (\<lambda>n \<xi>. \<Sum>i<n. C i \<xi> *\<^sub>R (X (Suc i) \<xi> - X i \<xi>))"
proof -
  interpret submartingale_linorder M F 0 X by (rule assms)
  interpret C: adapted_process M F 0 C by (rule assms)
  interpret C': adapted_process M F 0 "\<lambda>i \<xi>. C (i - 1) \<xi> *\<^sub>R (X i \<xi> - X (i - 1) \<xi>)" by (intro adapted_process.scaleR_right_adapted adapted_process.diff_adapted, unfold_locales) (auto intro: adaptedD C.adaptedD)+
  interpret S: adapted_process M F 0 "\<lambda>n \<xi>. \<Sum>i<n. C i \<xi> *\<^sub>R (X (Suc i) \<xi> - X i \<xi>)" using C'.adapted_process_axioms[THEN partial_sum_Suc_adapted] diff_Suc_1 by simp
  have "integrable M (\<lambda>x. C i x *\<^sub>R (X (Suc i) x - X i x))" for i using assms(3,4)[of i] by (intro Bochner_Integration.integrable_bound[OF integrable_scaleR_right, OF Bochner_Integration.integrable_diff, OF integrable(1,1), of R "Suc i" i]) (auto simp add: mult_mono)
  moreover have "AE \<xi> in M. 0 \<le> cond_exp M (F i) (\<lambda>\<xi>. (\<Sum>i<Suc i. C i \<xi> *\<^sub>R (X (Suc i) \<xi> - X i \<xi>)) - (\<Sum>i<i. C i \<xi> *\<^sub>R (X (Suc i) \<xi> - X i \<xi>))) \<xi>" for i 
    using sigma_finite_subalgebra.cond_exp_measurable_scaleR[OF _ calculation _ C.adapted, of i] 
          cond_exp_diff_nonneg[OF _ le_SucI, OF _ order.refl, of i] assms(3,4)[of i] by (fastforce simp add: scaleR_nonneg_nonneg integrable)
  ultimately show ?thesis by (intro submartingale_of_cond_exp_diff_Suc_nonneg S.adapted_process_axioms Bochner_Integration.integrable_sum, blast+)
qed

lemma submartingale_partial_sum_scaleR':
  assumes "submartingale_linorder M F 0 X"
    and "predictable_process M F 0 C" "\<And>i. AE \<xi> in M. 0 \<le> C i \<xi>" "\<And>i. AE \<xi> in M. C i \<xi> \<le> R"
  shows "submartingale M F 0 (\<lambda>n \<xi>. \<Sum>i<n. C (Suc i) \<xi> *\<^sub>R (X (Suc i) \<xi> - X i \<xi>))"
proof -
  interpret Suc_C: adapted_process M F 0 "\<lambda>i. C (Suc i)" using predictable_implies_adapted_Suc assms by blast
  show ?thesis by (intro submartingale_partial_sum_scaleR[OF assms(1), of _ R] assms) (intro_locales)
qed

end

context nat_sigma_finite_filtered_measure
begin

lemma predictable_mono':
  assumes "supermartingale M F 0 X"
    and "predictable_process M F 0 X" "i \<le> j"
  shows "AE \<xi> in M. X i \<xi> \<ge> X j \<xi>"
  using assms(3)
proof (induction "j - i" arbitrary: i j)
  case 0
  then show ?case by simp 
next
  case (Suc n)
  hence *: "n = j - Suc i" by linarith
  interpret supermartingale M F 0 X by (rule assms)
  interpret S: adapted_process M F 0 "\<lambda>i. X (Suc i)" by (intro predictable_implies_adapted_Suc assms)
  have "Suc i \<le> j" using Suc(2,3) by linarith
  thus ?case using Suc(1)[OF *] S.adapted[of i] supermartingale_property[OF _ le_SucI, of i] sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable, of "F i" "Suc i"] by fastforce
qed
  
lemma supermartingale_of_set_integral_ge_Suc:
  fixes X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"
  assumes adapted: "adapted_process M F 0 X"
      and integrable: "\<And>i. integrable M (X i)" 
      and "\<And>A i. A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X i) \<ge> set_lebesgue_integral M A (X (Suc i))" 
    shows "supermartingale M F 0 X"
proof -
  interpret adapted_process M F 0 X by (rule assms)
  interpret uminus_X: adapted_process M F 0 "-X" by (rule uminus_adapted)
  note * = set_integral_uminus[unfolded set_integrable_def, OF integrable_mult_indicator[OF _ integrable]]
  have "supermartingale M F 0 (-(- X))" 
    using ord_eq_le_trans[OF * ord_le_eq_trans[OF le_imp_neg_le[OF assms(3)] *[symmetric]]] sets_F_subset[THEN subsetD]
    by (intro submartingale.uminus submartingale_of_set_integral_le_Suc[OF uminus_adapted]) 
       (clarsimp simp add: fun_Compl_def integrable | fastforce)+
  thus ?thesis unfolding fun_Compl_def by simp
qed

lemma supermartingale_nat:
  fixes X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"
  assumes adapted: "adapted_process M F 0 X"
      and integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. X i \<xi> \<ge> cond_exp M (F i) (X (Suc i)) \<xi>" 
    shows "supermartingale M F 0 X"
proof -
  interpret adapted_process M F 0 X by (rule assms)
  have "AE \<xi> in M. - X i \<xi> \<le> cond_exp M (F i) (\<lambda>x. - X (Suc i) x) \<xi>" for i using assms(3) cond_exp_uminus[OF integrable, of i "Suc i"] by force
  hence "supermartingale M F 0 (-(- X))" by (intro submartingale.uminus submartingale_nat[OF uminus_adapted]) (auto simp add: fun_Compl_def integrable)
  thus ?thesis unfolding fun_Compl_def by simp
qed

lemma supermartingale_of_cond_exp_diff_Suc_le_zero:
  fixes X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"
  assumes adapted: "adapted_process M F 0 X"
      and integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. cond_exp M (F i) (\<lambda>\<xi>. X (Suc i) \<xi> - X i \<xi>) \<xi> \<le> 0" 
    shows "supermartingale M F 0 X"
proof (intro supermartingale_nat integrable adapted) 
  interpret adapted_process M F 0 X by (rule assms)
  fix i
  show "AE \<xi> in M. X i \<xi> \<ge> cond_exp M (F i) (X (Suc i)) \<xi>" using cond_exp_diff[OF integrable(1,1), of i "Suc i" i] cond_exp_F_meas[OF integrable adapted, of i] assms(3)[of i] by fastforce
qed

end

end