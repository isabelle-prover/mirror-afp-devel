theory List_Permutation_Util
  imports "HOL-Combinatorics.List_Permutation" "../util/List_Util"
begin

lemma perm_distinct_set_of_upt_iff:
  "xs <~~> [0..<n] \<longleftrightarrow> distinct xs \<and> set xs = {0..<n}"
  by (metis atLeastLessThan_upt distinct_upt perm_distinct_iff set_eq_iff_mset_eq_distinct)

lemma distinct_set_of_upto_length:
  "\<lbrakk>distinct xs; set xs = {0..<n}\<rbrakk> \<Longrightarrow> length xs = n"
  apply (drule (1) iffD2[OF perm_distinct_set_of_upt_iff conjI])
  apply (drule perm_length; simp)
  done

lemma set_perm_upt:
  "xs <~~> [0..<n] \<Longrightarrow> set xs = {0..<n}"
  using perm_distinct_set_of_upt_iff by blast

lemma perm_upt_length:
  "xs <~~> [0..<n] \<Longrightarrow> length xs = n"
  using distinct_set_of_upto_length perm_distinct_set_of_upt_iff by blast

lemma perm_nth_ex:
  "\<lbrakk>xs <~~> [0..<n]; i < n\<rbrakk> \<Longrightarrow> \<exists>k < n. xs ! i = k"
  using perm_upt_length set_perm_upt by fastforce

lemma ex_perm_nth:
  "\<lbrakk>xs <~~> [0..<n]; k < n\<rbrakk> \<Longrightarrow> \<exists>i < n. xs ! i = k"
  by (metis atLeast_upt distinct_Ex1 distinct_upt lessThan_iff perm_distinct_iff perm_set_eq
            perm_upt_length)

lemma set_map_nth_perm_subset:
  "\<lbrakk>ys <~~> [0..<n]; n \<le> length xs\<rbrakk> \<Longrightarrow> set (map (nth xs) ys) \<subseteq> set xs"
  by (simp add: nth_image set_perm_upt set_take_subset)

lemma set_map_nth_perm_eq:
  "ys <~~> [0..<length xs] \<Longrightarrow> set (map (nth xs) ys) = set xs"
  by (metis perm_set_eq set_map set_map_nth_eq)

lemma distinct_map_nth_perm:
  "\<lbrakk>distinct xs; n \<le> length xs; ys <~~> [0..<n]\<rbrakk> \<Longrightarrow> distinct (map (nth xs) ys)"
  by (metis distinct_map distinct_map_nth perm_distinct_iff perm_set_eq)

theorem distinct_set_imp_perm:
  assumes "distinct xs"
  and     "distinct ys"
  and     "set xs = set ys"
shows "xs <~~> ys"
proof -
  from set_eq_iff_mset_eq_distinct[OF assms(1,2), THEN iffD1, OF assms(3)]
  show ?thesis
    by simp
qed

theorem perm_nth:
  assumes "xs <~~> ys"
  and     "i < length xs"
shows "\<exists>j < length ys. ys ! j = xs ! i"
  by (metis assms(1) assms(2) in_set_conv_nth perm_set_eq)

lemma sort_perm:
  "xs <~~> sort xs"
  by simp

end