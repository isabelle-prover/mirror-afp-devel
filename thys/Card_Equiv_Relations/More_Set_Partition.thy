(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section {* More on Set Partitions *}

theory More_Set_Partition
imports
  "../Bell_Numbers_Spivey/Set_Partition"
begin

lemma partitions_mem_the_unique_part:
  assumes "partitions P A"
  assumes "x \<in> A"
  shows "x \<in> (THE X. x \<in> X \<and> X \<in> P)"
proof -
  from \<open>x \<in> A\<close> have "\<exists>!X. x \<in> X \<and> X \<in> P"
    using \<open>partitions P A\<close> by (simp add: partitions_partitions_unique)
  from this show "x \<in> (THE X. x \<in> X \<and> X \<in> P)"
    by (metis (no_types, lifting) theI)
qed

lemma the_unique_part_alternative_def:
  assumes "partitions P A"
  assumes "x \<in> A"
  shows "(THE X. x \<in> X \<and> X \<in> P) = {y. \<exists>X\<in>P. x \<in> X \<and> y \<in> X}"
proof
  show "(THE X. x \<in> X \<and> X \<in> P) \<subseteq> {y. \<exists>X\<in>P. x \<in> X \<and> y \<in> X}"
  proof
    fix y
    assume "y \<in> (THE X. x \<in> X \<and> X \<in> P)"
    moreover from \<open>x \<in> A\<close> have "x \<in> (THE X. x \<in> X \<and> X \<in> P)"
      using \<open>partitions P A\<close> partitions_mem_the_unique_part by force
    moreover from \<open>x \<in> A\<close> have "(THE X. x \<in> X \<and> X \<in> P) \<in> P"
      using \<open>partitions P A\<close> partitions_the_part_mem by force
    ultimately show "y \<in> {y. \<exists>X\<in>P. x \<in> X \<and> y \<in> X}" by auto
  qed
next
  show "{y. \<exists>X\<in>P. x \<in> X \<and> y \<in> X} \<subseteq> (THE X. x \<in> X \<and> X \<in> P)"
  proof
    fix y
    assume "y \<in> {y. \<exists>X\<in>P. x \<in> X \<and> y \<in> X}"
    from this obtain X where "x \<in> X" and "y \<in> X" and "X \<in> P" by auto
    from \<open>x \<in> X\<close> \<open>X \<in> P\<close> have "(THE X. x \<in> X \<and> X \<in> P) = X"
      using \<open>partitions P A\<close> partitions_the_part_eq by force
    from this \<open>y \<in> X\<close> show "y \<in> (THE X. x \<in> X \<and> X \<in> P)" by simp
  qed
qed

lemma partitions_part_characteristic:
  assumes "partitions P A"
  assumes "X \<in> P" "x \<in> X"
  shows "X = {y. \<exists>X\<in>P. x \<in> X \<and> y \<in> X}"
proof -
  from \<open>x \<in> X\<close> \<open>X \<in> P\<close> have "x \<in> A"
    using \<open>partitions P A\<close> partitionsE by blast
  from  \<open>x \<in> X\<close> \<open>X \<in> P\<close> have "X = (THE X. x \<in> X \<and> X \<in> P)"
    using \<open>partitions P A\<close> by (simp add: partitions_the_part_eq)
  also from \<open>x \<in> A\<close> have "(THE X. x \<in> X \<and> X \<in> P) = {y. \<exists>X\<in>P. x \<in> X \<and> y \<in> X}"
    using \<open>partitions P A\<close> the_unique_part_alternative_def by force
  finally show ?thesis .
qed

lemma partitions_no_partition_outside_carrier:
  assumes "partitions P A"
  assumes "x \<notin> A"
  shows "{y. \<exists>X\<in>P. x \<in> X \<and> y \<in> X} = {}"
using assms unfolding partitions_def by auto

end
