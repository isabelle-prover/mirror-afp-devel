theory AList_Extra
  imports "HOL-Library.AList" List_util
begin

lemma list_all2_rel_prod_updateI:
  assumes "list_all2 (rel_prod (=) R) xs ys" and "R xval yval"
  shows "list_all2 (rel_prod (=) R) (AList.update k xval xs) (AList.update k yval ys)"
  using assms(1,1,2)
  by (induction xs ys rule: list.rel_induct) auto

lemma length_map_entry[simp]: "length (AList.map_entry k f al) = length al"
  by (induction al) simp_all

lemma map_entry_id0[simp]: "AList.map_entry k id = id"
proof (rule ext)
  fix xs
  show "AList.map_entry k id xs = id xs"
    by (induction xs) auto
qed

lemma map_entry_id: "AList.map_entry k id xs = xs"
  by simp

lemma map_entry_map_of_Some_conv:
  "map_of xs k = Some v \<Longrightarrow> AList.map_entry k f xs = AList.update k (f v) xs"
  by (induction xs) auto

lemma map_entry_map_of_None_conv:
  "map_of xs k = None \<Longrightarrow> AList.map_entry k f xs = xs"
  by (induction xs) auto

lemma list_all2_rel_prod_map_entry:
  assumes
    "list_all2 (rel_prod (=) R) xs ys" and
    "\<And>xval yval. map_of xs k = Some xval \<Longrightarrow> map_of ys k = Some yval \<Longrightarrow> R (f xval) (g yval)"
  shows "list_all2 (rel_prod (=) R) (AList.map_entry k f xs) (AList.map_entry k g ys)"
  using assms(1)[THEN rel_option_map_of, of k]
proof (cases rule: option.rel_cases)
  case None
  thus ?thesis
    using assms(1) by (simp add: map_entry_map_of_None_conv)
next
  case (Some xval yval)
  then show ?thesis
    using assms(1,2)
    by (auto simp add: map_entry_map_of_Some_conv intro!: list_all2_rel_prod_updateI)
qed

lemmas list_all2_rel_prod_map_entry1 = list_all2_rel_prod_map_entry[where g = id, simplified]
lemmas list_all2_rel_prod_map_entry2 = list_all2_rel_prod_map_entry[where f = id, simplified]

lemma list_all_updateI:
  assumes "list_all P xs" and "P (k, v)"
  shows "list_all P (AList.update k v xs)"
  using assms
  by (induction xs) auto

lemma set_update: "set (AList.update k v xs) \<subseteq> {(k, v)} \<union> set xs"
  by (induction xs) auto

end