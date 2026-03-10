theory List_Extra \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> 
  imports Main
begin

definition set_list :: "'a set \<Rightarrow> 'a list" where
  "set_list S \<equiv> SOME xs. set xs = S \<and> distinct xs"

lemma set_list_empty [simp]: "set_list {} = []"
  unfolding set_list_def
  by auto

lemma set_list_singleton [simp]: "set_list {x} = [x]"
proof (unfold set_list_def, rule some1_equality, intro ex_ex1I)

  show "\<And>xs y. \<lbrakk>set xs = {x} \<and> distinct xs; set y = {x} \<and> distinct y\<rbrakk> \<Longrightarrow> xs = y"
    by (metis distinct_card replicate_eqI singleton_iff)
qed (auto simp: finite_distinct_list)

lemma set_list_set [simp]:
  assumes "finite S"
  shows "set (set_list S) = S"
  unfolding set_list_def
  by (rule someI2_ex[OF finite_distinct_list[OF assms]]) argo

lemma set_list_distinct [simp]:
  assumes "finite S"
  shows "distinct (set_list S)"
  unfolding set_list_def
  by (rule someI2_ex[OF finite_distinct_list[OF assms]]) argo

end
