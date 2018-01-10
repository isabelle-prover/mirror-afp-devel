(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
License: LGPL
*)

theory Sorted_Wrt
  imports Main
begin

inductive sorted_wrt for P
  where
    Nil [iff]: "sorted_wrt P []"
  | Cons: "\<forall>y\<in>set xs. P x y \<Longrightarrow> sorted_wrt P xs \<Longrightarrow> sorted_wrt P (x # xs)"

lemma sorted_wrt_single [iff]: "sorted_wrt P [x]"
  by (rule sorted_wrt.Cons) auto

lemma sorted_wrt_Cons: "sorted_wrt P (x # xs) \<longleftrightarrow> (\<forall>y\<in>set xs. P x y) \<and> sorted_wrt P xs"
  by (induct xs arbitrary: x)
    (auto elim: sorted_wrt.cases simp: sorted_wrt.Cons)

lemma sorted_wrt_filter:
  "sorted_wrt P xs \<Longrightarrow> sorted_wrt P (filter Q xs)"
  by (induct xs) (auto simp: sorted_wrt_Cons)

lemma sorted_wrt_append:
  "sorted_wrt P (xs @ ys) \<longleftrightarrow> sorted_wrt P xs \<and> sorted_wrt P ys \<and> (\<forall>x\<in>set xs. \<forall>y\<in>set ys. P x y)"
  by (induct xs) (auto simp: sorted_wrt_Cons)

lemma sorted_wrt_map:
  assumes "sorted_wrt P xs"
    and "\<And>x y. P x y \<Longrightarrow> P (f x) (f y)"
  shows "sorted_wrt P (map f xs)"
  using assms by (induct xs) (auto simp: sorted_wrt_Cons)

lemma sorted_wrt_map_mono:
  assumes "sorted_wrt Q xs"
    and "\<And>x y. Q x y \<Longrightarrow> P (f x) (f y)"
  shows "sorted_wrt P (map f xs)"
  using assms by (induct xs) (auto simp: sorted_wrt_Cons)

lemma sorted_wrt_concat_map_map:
  assumes "sorted_wrt Q xs"
    and "sorted_wrt Q ys"
    and "\<And>a x y. Q x y \<Longrightarrow> P (f x a) (f y a)"
    and "\<And>x y u v. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> Q u v \<Longrightarrow> P (f x u) (f y v)"
  shows "sorted_wrt P [f x y . y \<leftarrow> ys, x \<leftarrow> xs]"
  using assms by (induct ys)
    (auto simp: sorted_wrt_append sorted_wrt_Cons intro: sorted_wrt_map_mono [of Q])

lemma sorted_wrt_concat:
  assumes "sorted_wrt P xs"
    and "\<And>x y u v. P u v \<Longrightarrow> length y = length x \<Longrightarrow> P (g x u) (g y v)"
    and "\<And>x y z. P x y \<Longrightarrow> P (g x z) (g y z)"
    and "\<And>x. x \<in> set xs \<Longrightarrow> sorted_wrt P (f x)"
    and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set (f x) \<Longrightarrow> length y = n"
  shows "sorted_wrt P (concat (map (\<lambda>x. map (\<lambda>y. g y x) (f x)) xs))"
  using assms
  apply (induct xs)
   apply (auto simp: sorted_wrt_append intro: sorted_wrt_map)
   apply fastforce+
  done

lemma sorted_wrt_concat_map:
  assumes "sorted_wrt P (map h xs)"
    and "\<And>x. x \<in> set xs \<Longrightarrow> sorted_wrt P (map h (f x))"
    and "\<And>x y u v. P (h x) (h y) \<Longrightarrow> x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> u \<in> set (f x) \<Longrightarrow> v \<in> set (f y) \<Longrightarrow> P (h u) (h v)"
  shows "sorted_wrt P (concat (map (map h \<circ> f) xs))"
  using assms by (induct xs) (auto simp: sorted_wrt_append sorted_wrt_Cons)

lemma sorted_wrt_upt [intro, simp]: "sorted_wrt (<) [m ..< n]"
  by (induct n) (simp_all add: sorted_wrt_append)

lemma sorted_wrt_map_distr:
  assumes "sorted_wrt (\<lambda>x y. P x y) (map f xs)"
  shows "sorted_wrt (\<lambda>x y. P (f x) (f y)) xs"
  using assms
  by (induct xs) (auto simp: sorted_wrt_Cons)

lemma sorted_wrt_mono:
  assumes "\<And>x y. P x y \<Longrightarrow> Q x y"
    and "sorted_wrt P xs"
  shows "sorted_wrt Q xs"
  using assms(2) by (induct xs) (auto dest: assms(1) intro: sorted_wrt.Cons)

lemma sorted_wrt_tl:
  "xs \<noteq> [] \<Longrightarrow> sorted_wrt P xs \<Longrightarrow> sorted_wrt P (tl xs)"
  by (cases xs) (auto simp: sorted_wrt_Cons)

lemma trans_sorted_wrtI:
  assumes trans: "\<And>x y z. P x y \<Longrightarrow> P y z \<Longrightarrow> P x z"
    and "\<forall>i. Suc i < length xs \<longrightarrow> P (xs ! i) (xs ! Suc i)"
  shows "sorted_wrt P xs"
  using assms(2)
proof (induct xs)
  case (Cons a xs)
  then show ?case
    by(auto simp: sorted_wrt_Cons nth_Cons split: nat.splits)
      (metis append.simps(1) assms(1) id_take_nth_drop length_pos_if_in_set
        list.simps(3) nth_Cons_0 rel_simps(70) set_ConsD sorted_wrt.cases take_0)
qed  (auto simp: sorted_wrt_Cons nth_Cons split: nat.splits)

lemma sorted_wrt_imp_distinct:
  assumes "sorted_wrt P xs" and "\<And>x. \<not> P x x"
  shows "distinct xs"
  using assms by (induct) (auto)

lemma sorted_wrt_nth_less:
  assumes "sorted_wrt P xs"
    and "i < length xs" and "j < length xs"
    and "i < j"
  shows "P (xs ! i) (xs ! j)"
  using assms by (induct xs arbitrary: i j) (auto simp: nth_Cons split: nat.splits)

end
