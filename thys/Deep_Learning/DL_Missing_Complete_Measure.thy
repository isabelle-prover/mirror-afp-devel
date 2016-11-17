(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Missing Lemmas of Complete\_Measure\<close>

theory DL_Missing_Complete_Measure
imports "~~/src/HOL/Probability/Complete_Measure"
begin

lemma null_sets_completion_subset:
assumes "A \<in> null_sets (completion M)" "B \<subseteq> A"
shows "B \<in> null_sets (completion M)" 
proof -
  obtain N where "N \<in> null_sets M" "null_part M A \<subseteq> N" 
    using null_part[OF null_setsD2[OF assms(1)]] by blast
  then have "B \<subseteq> main_part M A \<union> N" 
    using main_part_null_part_Un[OF null_setsD2[OF assms(1)]] `B \<subseteq> A` by auto
  have "main_part M A \<in> null_sets M" using emeasure_completion[OF null_setsD2[OF assms(1)]] 
    by (metis assms(1) main_part_sets null_setsD1 null_setsD2 null_setsI)
  then have "main_part M A \<union> N \<in> null_sets M" using \<open>N \<in> null_sets M\<close> by blast
  then show ?thesis using null_sets_completion 
    by (metis \<open>B \<subseteq> main_part M A \<union> N\<close> assms(1) assms(2) emeasure_Un_null_set le_iff_sup null_setsD1 null_setsI)
qed

end
