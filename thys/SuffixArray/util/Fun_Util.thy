theory Fun_Util
  imports Main
begin

section \<open>Monotonic Functions\<close>

lemma strict_mono_leD: "strict_mono r \<Longrightarrow> m \<le> n \<Longrightarrow> r m \<le> r n"
  by (erule (1) monoD [OF strict_mono_mono])

definition map_to_nat :: "('a :: linorder list) \<Rightarrow> ('a \<Rightarrow> nat)"
  where
"map_to_nat xs = (\<lambda>x. card {y|y. y \<in> set xs \<and> y < x})"

lemma map_to_nat_strict_mono_on:
  "strict_mono_on (set xs) (map_to_nat xs)"
  unfolding strict_mono_on_def map_to_nat_def
proof safe
 fix x y :: 'a
  assume "x < y" "x \<in> set xs" "y \<in> set xs"
  have "finite {a |a. a \<in> set xs \<and> a < y}"
    by auto
  moreover
  have "{a |a. a \<in> set xs \<and> a < x} \<subset> {a |a. a \<in> set xs \<and> a < y}"
  proof (intro psubsetI subsetI notI)
    fix k
    assume "k \<in> {a |a. a \<in> set xs \<and> a < x}"
    hence "k < x" "k \<in> set xs"
      by simp_all
    hence "k < y" "k \<in> set xs"
      using \<open>x < y\<close> by auto
    then show "k \<in> {a |a. a \<in> set xs \<and> a < y}"
      by simp
  next
    assume "{a |a. a \<in> set xs \<and> a < x} = {a |a. a \<in> set xs \<and> a < y}"
    moreover
    have "x \<in> {a |a. a \<in> set xs \<and> a < y}"
      using \<open>x < y\<close> `x \<in> set xs` by auto
    moreover
    have "x \<notin> {a |a. a \<in> set xs \<and> a < x}"
      by auto
    ultimately show False
      by simp
  qed
  ultimately show "card {a |a. a \<in> set xs \<and> a < x} < card {a |a. a \<in> set xs \<and> a < y}"
    using psubset_card_mono[of "{a |a. a \<in> set xs \<and> a < y}" "{a |a. a \<in> set xs \<and> a < x}"]
    by blast
qed

lemma strict_mono_on_map_set_ex:
  "\<exists>(f :: ('a :: linorder \<Rightarrow> nat)). strict_mono_on (set xs) f"
  using map_to_nat_strict_mono_on by blast

locale Linorder_to_Nat_List =
  fixes map_to_nat :: "'a :: linorder list \<Rightarrow> 'a \<Rightarrow> nat"
  and   xs :: "'a :: linorder list"
  assumes map_to_nat_strict_mono_on: "strict_mono_on (set xs) (map_to_nat xs)"

context Linorder_to_Nat_List begin

lemma strict_mono_on_Suc_map_to_nat:
  "strict_mono_on (set xs) (\<lambda>x. Suc (map_to_nat xs x))"
  by (metis (mono_tags, lifting) Suc_mono ord.strict_mono_on_def map_to_nat_strict_mono_on)

end (* of context *)

lemma Linorder_to_Nat_List_ex:
  "\<exists>\<alpha>. Linorder_to_Nat_List \<alpha> xs"
  by (meson Linorder_to_Nat_List.intro strict_mono_on_map_set_ex)


end