section \<open>Bertrand's postulate\<close>
(*
  File:     Bertrand_Discrete_Sqrt.thy
  Authors:  Julian Biendarra, Manuel Eberl <eberlm@in.tum.de>

  Some facts about the discrete square root. Should be merged into the distribution 
  for Isabelle2017.
*)
theory Bertrand_Discrete_Sqrt
imports Main "~~/src/HOL/Library/Discrete"
begin

subsection \<open>Facts about the discrete square root\<close>
  
lemma Suc_sqrt_power2_gt: "n < (Suc (Discrete.sqrt n))^2"
  using Max_ge[OF Discrete.sqrt_aux(1), of "Discrete.sqrt n + 1" n]
  by (cases "n < (Suc (Discrete.sqrt n))^2") (simp_all add: Discrete.sqrt_def)

lemma le_sqrt_iff: "x \<le> Discrete.sqrt y \<longleftrightarrow> x^2 \<le> y"
proof -
  have "x \<le> Discrete.sqrt y \<longleftrightarrow> (\<exists>z. z\<^sup>2 \<le> y \<and> x \<le> z)"    
    using Max_ge_iff[OF Discrete.sqrt_aux, of x y] by (simp add: Discrete.sqrt_def)
  also have "\<dots> \<longleftrightarrow> x^2 \<le> y"
  proof safe
    fix z assume "x \<le> z" "z ^ 2 \<le> y"
    thus "x^2 \<le> y" by (intro le_trans[of "x^2" "z^2" y]) (simp_all add: power2_nat_le_eq_le)
  qed auto
  finally show ?thesis .
qed
  
lemma le_sqrtI: "x^2 \<le> y \<Longrightarrow> x \<le> Discrete.sqrt y"
  by (simp add: le_sqrt_iff)

lemma sqrt_le_iff: "Discrete.sqrt y \<le> x \<longleftrightarrow> (\<forall>z. z^2 \<le> y \<longrightarrow> z \<le> x)"
  using Max.bounded_iff[OF Discrete.sqrt_aux] by (simp add: Discrete.sqrt_def)

lemma sqrt_leI:
  "(\<And>z. z^2 \<le> y \<Longrightarrow> z \<le> x) \<Longrightarrow> Discrete.sqrt y \<le> x"
  by (simp add: sqrt_le_iff)
    
lemma sqrt_Suc:
  "Discrete.sqrt (Suc n) = (if \<exists>m. Suc n = m^2 then Suc (Discrete.sqrt n) else Discrete.sqrt n)"
proof cases
  assume "\<exists> m. Suc n = m^2"
  then obtain m where m_def: "Suc n = m^2" by blast
  then have lhs: "Discrete.sqrt (Suc n) = m" by simp
  from m_def sqrt_power2_le[of n] 
    have "(Discrete.sqrt n)^2 < m^2" by linarith
  with power2_less_imp_less have lt_m: "Discrete.sqrt n < m" by blast
  from m_def Suc_sqrt_power2_gt[of "n"]
    have "m^2 \<le> (Suc(Discrete.sqrt n))^2" by simp
  with power2_nat_le_eq_le have "m \<le> Suc (Discrete.sqrt n)" by blast
  with lt_m have "m = Suc (Discrete.sqrt n)" by simp
  with lhs m_def show ?thesis by fastforce
next
  assume asm: "\<not> (\<exists> m. Suc n = m^2)"
  hence "Suc n \<noteq> (Discrete.sqrt (Suc n))^2" by simp
  with sqrt_power2_le[of "Suc n"] 
    have "Discrete.sqrt (Suc n) \<le> Discrete.sqrt n" by (intro le_sqrtI) linarith
  moreover have "Discrete.sqrt (Suc n) \<ge> Discrete.sqrt n"
    by (intro monoD[OF mono_sqrt]) simp_all
  ultimately show ?thesis using asm by simp
qed

end