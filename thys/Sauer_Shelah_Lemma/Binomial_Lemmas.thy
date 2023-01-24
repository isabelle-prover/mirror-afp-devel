(*  Title:      Binomial_Lemmas.thy
    Author:     Ata Keskin, TU München
*)

section \<open>Lemmas involving the binomial coefficient\<close>

text \<open>In this section, we prove lemmas that use the term for the binomial coefficient @{term choose}.\<close>

theory Binomial_Lemmas
  imports Main
begin

lemma choose_mono:
  assumes "x \<le> y"
  shows "x choose n \<le> y choose n"
proof -
  have "finite {0..<y}" by blast
  with finite_Pow_iff[of "{0..<y}"] have finiteness: "finite {K \<in> Pow {0..<y}. card K = n}" by simp
  from assms have "Pow {0..<x} \<subseteq> Pow {0..<y}" by force
  then have "{K \<in> Pow {0..<x}. card K = n} \<subseteq> {K \<in> Pow {0..<y}. card K = n}" by blast
  from card_mono[OF finiteness this] show ?thesis unfolding binomial_def .
qed

lemma choose_row_sum_set:
  assumes "finite (\<Union>F)"
  shows "card {S. S \<subseteq> \<Union>F \<and> card S \<le> k} = (\<Sum>i\<le>k. card (\<Union> F) choose i)"
proof (induction k)
  case 0
  from rev_finite_subset[OF assms] have "S \<subseteq> \<Union>F \<and> card S \<le> 0 \<longleftrightarrow> S = {}" for S by fastforce
  then show ?case by simp
next
  case (Suc k)
  let ?FS = "{S. S \<subseteq> \<Union> F \<and> card S \<le> Suc k}"
  and ?F_Asm = "{S. S \<subseteq> \<Union> F \<and> card S \<le> k}" 
  and ?F_Step = "{S. S \<subseteq> \<Union> F \<and> card S = Suc k}"

  from finite_Pow_iff[of "\<Union>F"] assms have finite_Pow_Un_F: "finite (Pow (\<Union> F))" ..
  have "?F_Asm \<subseteq> Pow (\<Union> F)" and "?F_Step \<subseteq> Pow (\<Union> F)" by fast+
  with rev_finite_subset[OF finite_Pow_Un_F] have finite_F_Asm: "finite ?F_Asm" and finite_F_Step: "finite ?F_Step" by presburger+

  have F_Un: "?FS = ?F_Asm \<union> ?F_Step"  and F_disjoint: "?F_Asm \<inter> ?F_Step = {}" by fastforce+
  from card_Un_disjoint[OF finite_F_Asm finite_F_Step F_disjoint] F_Un have "card ?FS = card ?F_Asm + card ?F_Step" by argo
  also from Suc have "... = (\<Sum>i\<le>k. card (\<Union> F) choose i) + card ?F_Step" by argo
  also from n_subsets[OF assms, of "Suc k"] have "... = (\<Sum>i\<le>Suc k. card (\<Union> F) choose i)" by force
  finally show ?case by blast
qed

end