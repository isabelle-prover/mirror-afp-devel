theory Map_Extra
  imports Main "HOL-Library.Library"
begin

lemmas map_of_eq_Some_imp_key_in_fst_dom[intro] =
  domI[of "map_of xs" for xs, unfolded dom_map_of_conv_image_fst]

lemma very_weak_map_of_SomeI: "k \<in> fst ` set kvs \<Longrightarrow> \<exists>v. map_of kvs k = Some v"
  by (induction kvs) auto

lemma map_of_fst_hd_neq_Nil[simp]:
  assumes "xs \<noteq> []"
  shows "map_of xs (fst (hd xs)) = Some (snd (hd xs))"
  using assms
  by (cases xs) simp_all

definition map_merge where
  "map_merge f m1 m2 x =
    (case (m1 x, m2 x) of
      (None, None) \<Rightarrow> None
    | (None, Some z) \<Rightarrow> Some z
    | (Some y, None) \<Rightarrow> Some y
    | (Some y, Some z) \<Rightarrow> f y z)"

lemma option_case_cancel[simp]: "(case opt of None \<Rightarrow> x | Some _ \<Rightarrow> x) = x"
  using option.case_eq_if
  by (simp add: option.case_eq_if)

lemma map_le_map_merge_Some_const:
  "f \<subseteq>\<^sub>m map_merge (\<lambda>x y. Some x) f g" and
  "g \<subseteq>\<^sub>m map_merge (\<lambda>x y. Some y) f g"
  unfolding map_le_def atomize_conj
  find_theorems "_ &&& _"
proof (intro conjI ballI)
  fix x
  assume "x \<in> dom f"
  then obtain y where "f x = Some y"
    by blast
  then show "f x = map_merge (\<lambda>x y. Some x) f g x"
    unfolding map_merge_def
    by simp
next
  fix x
  assume "x \<in> dom g"
  then obtain z where "g x = Some z"
    by blast
  then show "g x = map_merge (\<lambda>x. Some) f g x"
    unfolding map_merge_def
    by (simp add: option.case_eq_if)
qed

section \<open>pred\_map\<close>

definition pred_map where
  "pred_map P m \<equiv> (\<forall>x y. m x = Some y \<longrightarrow> P y)"

lemma pred_map_get:
  assumes "pred_map P m" and "m x = Some y"
  shows "P y"
  using assms unfolding pred_map_def by simp

end