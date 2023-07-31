section \<open>Minimum and Maximum of Potentially Infinite Sets\<close>

theory Minimum_Maximum
  imports Main
begin

text \<open>We define minima and maxima of sets. In contrast
  to the existing @{const Min} and @{const Max} operators,
  these operators are not restricted to finite sets \<close>

definition Maximum :: "'a :: linorder set \<Rightarrow> 'a" where 
  "Maximum S = (THE x. x \<in> S \<and> (\<forall> y \<in> S. y \<le> x))" 
definition Minimum :: "'a :: linorder set \<Rightarrow> 'a" where 
  "Minimum S = (THE x. x \<in> S \<and> (\<forall> y \<in> S. x \<le> y))" 

definition has_Maximum where "has_Maximum S = (\<exists> x. x \<in> S \<and> (\<forall> y \<in> S. y \<le> x))"
definition has_Minimum where "has_Minimum S = (\<exists> x. x \<in> S \<and> (\<forall> y \<in> S. x \<le> y))"

lemma eqMaximumI:  
  assumes "x \<in> S" 
  and "\<And> y. y \<in> S \<Longrightarrow> y \<le> x" 
shows "Maximum S = x" 
  unfolding Maximum_def
  by (standard, insert assms, auto, fastforce) 

lemma eqMinimumI: 
  assumes "x \<in> S" 
  and "\<And> y. y \<in> S \<Longrightarrow> x \<le> y" 
shows "Minimum S = x" 
  unfolding Minimum_def
  by (standard, insert assms, auto, fastforce) 

lemma has_MaximumD:  
  assumes "has_Maximum S" 
  shows "Maximum S \<in> S"
    "x \<in> S \<Longrightarrow> x \<le> Maximum S"
proof -
  from assms[unfolded has_Maximum_def]
  obtain m where *: "m \<in> S" "\<And> y. y \<in> S \<Longrightarrow> y \<le> m" by auto
  have id: "Maximum S = m" 
    by (rule eqMaximumI, insert *, auto)
  from * id show "Maximum S \<in> S" "x \<in> S \<Longrightarrow> x \<le> Maximum S" by auto
qed

lemma has_MinimumD: 
  assumes "has_Minimum S" 
  shows "Minimum S \<in> S"
    "x \<in> S \<Longrightarrow> Minimum S \<le> x"
proof -
  from assms[unfolded has_Minimum_def]
  obtain m where *: "m \<in> S" "\<And> y. y \<in> S \<Longrightarrow> m \<le> y" by auto
  have id: "Minimum S = m" 
    by (rule eqMinimumI, insert *, auto)
  from * id show "Minimum S \<in> S" "x \<in> S \<Longrightarrow> Minimum S \<le> x" by auto
qed

text \<open>On non-empty finite sets, @{const Minimum} and @{const Min} 
  coincide, and similarly @{const Maximum} and @{const Max}.\<close>

lemma Minimum_Min: assumes "finite S" "S \<noteq> {}"
  shows "Minimum S = Min S" 
  by (rule eqMinimumI, insert assms, auto)

lemma Maximum_Max: assumes "finite S" "S \<noteq> {}"
  shows "Maximum S = Max S" 
  by (rule eqMaximumI, insert assms, auto)

text \<open>For natural numbers, having a maximum is the same as being bounded from above and non-empty,
 or being finite and non-empty.\<close>
lemma has_Maximum_nat_iff_bdd_above: "has_Maximum (A :: nat set) \<longleftrightarrow> bdd_above A \<and> A \<noteq> {}" 
  unfolding has_Maximum_def
  by (metis bdd_above.I bdd_above_nat emptyE finite_has_maximal nat_le_linear)

lemma has_Maximum_nat_iff_finite: "has_Maximum (A :: nat set) \<longleftrightarrow> finite A \<and> A \<noteq> {}" 
  unfolding has_Maximum_nat_iff_bdd_above bdd_above_nat ..

lemma bdd_above_Maximum_nat: "(x :: nat) \<in> A \<Longrightarrow> bdd_above A \<Longrightarrow> x \<le> Maximum A" 
  by (rule has_MaximumD, auto simp: has_Maximum_nat_iff_bdd_above)

end