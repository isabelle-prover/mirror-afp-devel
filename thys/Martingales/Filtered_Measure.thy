(*  Author:     Ata Keskin, TU München 
*)

theory Filtered_Measure
  imports "HOL-Probability.Conditional_Expectation"
begin

section \<open>Filtered Measure Spaces\<close>

subsection \<open>Filtered Measure\<close>

locale filtered_measure = 
  fixes M F and t\<^sub>0 :: "'b :: {second_countable_topology, order_topology, t2_space}"
  assumes subalgebras: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> subalgebra M (F i)"
      and sets_F_mono: "\<And>i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> sets (F i) \<le> sets (F j)"
begin

lemma space_F[simp]: 
  assumes "t\<^sub>0 \<le> i"
  shows "space (F i) = space M"
  using subalgebras assms by (simp add: subalgebra_def)

lemma subalgebra_F[intro]: 
  assumes "t\<^sub>0 \<le> i" "i \<le> j"
  shows "subalgebra (F j) (F i)"
  unfolding subalgebra_def using assms by (simp add: sets_F_mono)

lemma borel_measurable_mono:
  assumes "t\<^sub>0 \<le> i" "i \<le> j"
  shows "borel_measurable (F i) \<subseteq> borel_measurable (F j)"
  unfolding subset_iff by (metis assms subalgebra_F measurable_from_subalg)

end

locale linearly_filtered_measure = filtered_measure M F t\<^sub>0 for M and F :: "_ :: {linorder_topology} \<Rightarrow> _" and t\<^sub>0

locale nat_filtered_measure = linearly_filtered_measure M F 0 for M and F :: "nat \<Rightarrow> _"
locale real_filtered_measure = linearly_filtered_measure M F 0 for M and F :: "real \<Rightarrow> _"

subsection \<open>\<open>\<sigma>\<close>-Finite Filtered Measure\<close>

text \<open>The locale presented here is a generalization of the \<^locale>\<open>sigma_finite_subalgebra\<close> for a particular filtration.\<close>

locale sigma_finite_filtered_measure = filtered_measure +
  assumes sigma_finite_initial: "sigma_finite_subalgebra M (F t\<^sub>0)"

lemma (in sigma_finite_filtered_measure) sigma_finite_subalgebra_F[intro]:
  assumes "t\<^sub>0 \<le> i"
  shows "sigma_finite_subalgebra M (F i)"
  using assms by (metis dual_order.refl sets_F_mono sigma_finite_initial sigma_finite_subalgebra.nested_subalg_is_sigma_finite subalgebras subalgebra_def)

locale nat_sigma_finite_filtered_measure = sigma_finite_filtered_measure M F "0 :: nat" for M F
locale real_sigma_finite_filtered_measure = sigma_finite_filtered_measure M F "0 :: real" for M F

sublocale nat_sigma_finite_filtered_measure \<subseteq> sigma_finite_subalgebra M "F i" by blast
sublocale real_sigma_finite_filtered_measure \<subseteq> sigma_finite_subalgebra M "F \<bar>i\<bar>" by fastforce 

subsection \<open>Finite Filtered Measure\<close>

locale finite_filtered_measure = filtered_measure + finite_measure

sublocale finite_filtered_measure \<subseteq> sigma_finite_filtered_measure 
  using subalgebras by (unfold_locales, blast, meson dual_order.refl finite_measure_axioms finite_measure_def finite_measure_restr_to_subalg sigma_finite_measure.sigma_finite_countable)

locale nat_finite_filtered_measure = finite_filtered_measure M F "0 :: nat" for M F
locale real_finite_filtered_measure = finite_filtered_measure M F "0 :: real" for M F

sublocale nat_finite_filtered_measure \<subseteq> nat_sigma_finite_filtered_measure ..
sublocale real_finite_filtered_measure \<subseteq> real_sigma_finite_filtered_measure ..

subsection \<open>Constant Filtration\<close>

lemma filtered_measure_constant_filtration:
  assumes "subalgebra M F"
  shows "filtered_measure M (\<lambda>_. F) t\<^sub>0"
  using assms by (unfold_locales) blast+

sublocale sigma_finite_subalgebra \<subseteq> constant_filtration: sigma_finite_filtered_measure M "\<lambda>_ :: 't :: {second_countable_topology, linorder_topology}. F" t\<^sub>0
  using subalg by (unfold_locales) blast+

lemma (in finite_measure) filtered_measure_constant_filtration:
  assumes "subalgebra M F"
  shows "finite_filtered_measure M (\<lambda>_. F) t\<^sub>0"
  using assms by (unfold_locales) blast+

end