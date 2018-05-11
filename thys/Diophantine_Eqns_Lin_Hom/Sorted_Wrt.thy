(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
License: LGPL
*)

theory Sorted_Wrt
  imports Main
begin

lemma sorted_wrt_filter:
  "sorted_wrt P xs \<Longrightarrow> sorted_wrt P (filter Q xs)"
  by (induct xs) (auto)

lemma sorted_wrt_map_mono:
  assumes "sorted_wrt Q xs"
    and "\<And>x y. Q x y \<Longrightarrow> P (f x) (f y)"
  shows "sorted_wrt P (map f xs)"
  using assms by (induct xs) (auto)

lemma sorted_wrt_concat_map_map:
  assumes "sorted_wrt Q xs"
    and "sorted_wrt Q ys"
    and "\<And>a x y. Q x y \<Longrightarrow> P (f x a) (f y a)"
    and "\<And>x y u v. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> Q u v \<Longrightarrow> P (f x u) (f y v)"
  shows "sorted_wrt P [f x y . y \<leftarrow> ys, x \<leftarrow> xs]"
  using assms by (induct ys)
    (auto simp: sorted_wrt_append intro: sorted_wrt_map_mono [of Q])

lemma sorted_wrt_concat_map:
  assumes "sorted_wrt P (map h xs)"
    and "\<And>x. x \<in> set xs \<Longrightarrow> sorted_wrt P (map h (f x))"
    and "\<And>x y u v. P (h x) (h y) \<Longrightarrow> x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> u \<in> set (f x) \<Longrightarrow> v \<in> set (f y) \<Longrightarrow> P (h u) (h v)"
  shows "sorted_wrt P (concat (map (map h \<circ> f) xs))"
  using assms by (induct xs) (auto simp: sorted_wrt_append)

lemma sorted_wrt_map_distr:
  assumes "sorted_wrt (\<lambda>x y. P x y) (map f xs)"
  shows "sorted_wrt (\<lambda>x y. P (f x) (f y)) xs"
  using assms
  by (induct xs) (auto)

lemma sorted_wrt_tl:
  "xs \<noteq> [] \<Longrightarrow> sorted_wrt P xs \<Longrightarrow> sorted_wrt P (tl xs)"
  by (cases xs) (auto)

lemma trans_sorted_wrtI:
  assumes trans: "\<And>x y z. P x y \<Longrightarrow> P y z \<Longrightarrow> P x z"
    and "\<forall>i. Suc i < length xs \<longrightarrow> P (xs ! i) (xs ! Suc i)"
  shows "sorted_wrt P xs"
  using assms(2)
proof (induct xs)
  case (Cons a xs)
  then show ?case
  by (metis (no_types, lifting) append.simps(1) assms(1) id_take_nth_drop length_pos_if_in_set
    nth_Cons_0 nth_Cons_Suc sorted_wrt.simps(2) sorted_wrt2 take_0 transp_def Suc_less_eq
    length_Cons)
qed auto

lemma sorted_wrt_imp_distinct:
  assumes "sorted_wrt P xs" and "\<And>x. \<not> P x x"
  shows "distinct xs"
  using assms by (induct xs) (auto)

lemma sorted_wrt_nth_less:
  assumes "sorted_wrt P xs"
    and "i < length xs" and "j < length xs"
    and "i < j"
  shows "P (xs ! i) (xs ! j)"
  using assms by (induct xs arbitrary: i j) (auto simp: nth_Cons')

end
