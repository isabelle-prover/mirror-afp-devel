(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section {* More on Set Partitions *}

theory More_Set_Partition
imports
  Bell_Numbers_Spivey.Set_Partition
begin

lemma the_unique_part_alternative_def:
  assumes "partition_on A P"
  assumes "x \<in> A"
  shows "(THE X. x \<in> X \<and> X \<in> P) = {y. \<exists>X\<in>P. x \<in> X \<and> y \<in> X}"
proof
  show "(THE X. x \<in> X \<and> X \<in> P) \<subseteq> {y. \<exists>X\<in>P. x \<in> X \<and> y \<in> X}"
  proof
    fix y
    assume "y \<in> (THE X. x \<in> X \<and> X \<in> P)"
    moreover from \<open>x \<in> A\<close> have "x \<in> (THE X. x \<in> X \<and> X \<in> P)"
      using \<open>partition_on A P\<close> partition_on_in_the_unique_part by force
    moreover from \<open>x \<in> A\<close> have "(THE X. x \<in> X \<and> X \<in> P) \<in> P"
      using \<open>partition_on A P\<close> partition_on_the_part_mem by force
    ultimately show "y \<in> {y. \<exists>X\<in>P. x \<in> X \<and> y \<in> X}" by auto
  qed
next
  show "{y. \<exists>X\<in>P. x \<in> X \<and> y \<in> X} \<subseteq> (THE X. x \<in> X \<and> X \<in> P)"
  proof
    fix y
    assume "y \<in> {y. \<exists>X\<in>P. x \<in> X \<and> y \<in> X}"
    from this obtain X where "x \<in> X" and "y \<in> X" and "X \<in> P" by auto
    from \<open>x \<in> X\<close> \<open>X \<in> P\<close> have "(THE X. x \<in> X \<and> X \<in> P) = X"
      using \<open>partition_on A P\<close> partition_on_the_part_eq by force
    from this \<open>y \<in> X\<close> show "y \<in> (THE X. x \<in> X \<and> X \<in> P)" by simp
  qed
qed

lemma partition_on_part_characteristic:
  assumes "partition_on A P"
  assumes "X \<in> P" "x \<in> X"
  shows "X = {y. \<exists>X\<in>P. x \<in> X \<and> y \<in> X}"
proof -
  from \<open>x \<in> X\<close> \<open>X \<in> P\<close> have "x \<in> A"
    using \<open>partition_on A P\<close> partition_onE by blast
  from  \<open>x \<in> X\<close> \<open>X \<in> P\<close> have "X = (THE X. x \<in> X \<and> X \<in> P)"
    using \<open>partition_on A P\<close> by (simp add: partition_on_the_part_eq)
  also from \<open>x \<in> A\<close> have "(THE X. x \<in> X \<and> X \<in> P) = {y. \<exists>X\<in>P. x \<in> X \<and> y \<in> X}"
    using \<open>partition_on A P\<close> the_unique_part_alternative_def by force
  finally show ?thesis .
qed

lemma partition_on_no_partition_outside_carrier:
  assumes "partition_on A P"
  assumes "x \<notin> A"
  shows "{y. \<exists>X\<in>P. x \<in> X \<and> y \<in> X} = {}"
using assms unfolding partition_on_def by auto

end
