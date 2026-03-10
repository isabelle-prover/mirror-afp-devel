theory Finite_Map_Extra \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> 
  imports 
    "HOL-Library.Finite_Map" 
    List_Extra
begin

definition fmap_dom_list :: "('k, 'v) fmap \<Rightarrow> 'k list" where
  "fmap_dom_list m \<equiv> SOME xs. set xs = fmdom' m \<and> distinct xs"

lemma fmap_dom_list_exists [intro]: "\<exists>xs. set xs = fmdom' m \<and> distinct xs"
  by (induction m) (auto simp: finite_distinct_list)

lemma set_fmap_dom_list [simp]: "set (fmap_dom_list m) = fmdom' m"
  unfolding fmap_dom_list_def
  by (rule someI2_ex[OF fmap_dom_list_exists]) argo

lemma distinct_fmap_dom_list [simp]: "distinct (fmap_dom_list m)"
  unfolding fmap_dom_list_def
  by (rule someI2_ex[OF fmap_dom_list_exists]) argo

lemma fmap_dom_list_empty [simp]: "fmap_dom_list fmempty = []"
  by (metis set_fmap_dom_list fmdom'_empty set_empty)

definition fmap_list :: "('k, 'v) fmap \<Rightarrow> ('k \<times> 'v) list" where
  "fmap_list m \<equiv> map (\<lambda>k. (k, the (fmlookup m k))) (fmap_dom_list m)"

lemma fmap_list_empty [simp]: "fmap_list fmempty = []"
  unfolding fmap_list_def
  by simp

lemma set_fst_fmap_list [simp]: "set (map fst (fmap_list m)) = fmdom' m"
  unfolding fmap_list_def 
  by simp

lemma distinct_fst_fmap_list [simp]: "distinct (map fst (fmap_list m))"
  unfolding fmap_list_def
  by (simp add: map_idI)

lemma fmap_list_mem_iff: "(k, v) \<in> set (fmap_list m) \<longleftrightarrow> fmlookup m k = Some v"
proof (rule iffI)
  assume "(k,v) \<in> set (fmap_list m)"

  then show "fmlookup m k = Some v"
    unfolding fmap_list_def
    by (metis dom_fmlookup graph_eq_to_snd_dom in_graphD list.set_map set_fmap_dom_list)
next
  assume "fmlookup m k = Some v"
 
  then show "(k,v) \<in> set (fmap_list m)"
    unfolding fmap_list_def
    using set_fmap_dom_list distinct_fmap_dom_list
    by fastforce
qed

definition fmap_of_set :: "'k set \<Rightarrow> ('k \<Rightarrow> 'v) \<Rightarrow> ('k,'v) fmap" where
  "fmap_of_set X f \<equiv> fold (\<lambda>x m. fmupd x (f x) m) (set_list X) fmempty"

lemma fmap_of_set_empty [simp]: "fmap_of_set {} f = fmempty"
  unfolding fmap_of_set_def
  by simp

lemma fmlookup_fold_fmupd_notin [simp]:
  assumes "x \<notin> set xs"
  shows "fmlookup (fold (\<lambda>k m. fmupd k (f k) m) xs m) x = fmlookup m x"
  using assms
  by (induction xs arbitrary: m) auto

lemma fmlookup_fold_fmupd_in [simp]:
  assumes "distinct xs" "x \<in> set xs"
  shows "fmlookup (fold (\<lambda>k m. fmupd k (f k) m) xs m) x = Some (f x)"
  using assms
  by (induction xs arbitrary: m) auto

lemma fmlookup_fmap_of_set_notin [simp]:
  assumes "finite X" "x \<notin> X"
  shows "fmlookup (fmap_of_set X f) x = None"
  using assms
  unfolding fmap_of_set_def
  by auto

lemma fmlookup_fmap_of_set_in [simp]:
  assumes "finite X"  and "x \<in> X"
  shows "fmlookup (fmap_of_set X f) x = Some (f x)"
  using assms
  unfolding fmap_of_set_def
  by auto

end
