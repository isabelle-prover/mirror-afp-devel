(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Auxiliary Lemmas for the Minimal Bad Sequence Proof *}

theory Kruskal_Auxiliaries
imports
  Almost_Full_Relations
begin

lemma no_bad_of_special_shape_imp_good':
  assumes "\<not> (\<exists>R f::nat seq. (\<forall>i. R i \<in> set (B (f i)) \<and> f 0 \<le> f i) \<and> bad P R)"
    and refl: "reflp_on P {x. \<exists>i. x \<in> set (B i)}"
    and elts: "\<forall>i. f i \<in> {x. \<exists>i. x \<in> set (B i)}"
  shows "good P f"
proof (rule ccontr)
  let ?B = "\<lambda>i. set (B i)"
  assume "bad P f"
  from elts have "\<forall>i. \<exists>j. f i \<in> ?B j" by auto
  from choice [OF this] obtain g where B: "\<forall>i. f i \<in> ?B (g i)" by auto
  have "\<forall>i. \<exists>j>i. g 0 \<le> g j"
  proof (rule ccontr)
    assume "\<not> (\<forall>i. \<exists>j>i. g 0 \<le> g j)"
    then obtain i where *: "\<forall>j>i. g j < g 0" by force
    let ?I = "{j. j > i}"
    have "g ` ?I \<subseteq> {..<g 0}"
      using * unfolding image_subset_iff by (metis lessThan_iff mem_Collect_eq)
    moreover have "finite {..<g 0}" by auto
    ultimately have 1: "finite (g ` ?I)" using finite_subset by blast
    have 2: "infinite ?I" by (rule infinite_wo_prefix)
    from pigeonhole_infinite [OF 2 1]
      obtain k where "k > i" and 3: "infinite {j. j > i \<and> g j = g k}" by auto
    from this [unfolded infinite_nat_iff_unbounded]
      have "\<forall>m. \<exists>n>m. n > i \<and> g n = g k" by auto
    from choice [OF this] obtain h where
      **: "\<forall>m. h m > m \<and> h m > i \<and> g (h m) = g k" by auto
    let ?g = "g \<circ> h"
    let ?h = "\<lambda>i. (h ^^ Suc i) 0"
    from B have "\<forall>i. f (?h i) \<in> ?B ((g \<circ> ?h) i)" by auto
    with ** have "\<forall>i. f (?h i) \<in> ?B (g k)" by simp
    with pigeonhole_infinite_rel [of "UNIV::nat set" "?B (g k)" "\<lambda>a b. f (?h a) = b"]
      obtain x where "x \<in> ?B (g k)" and "infinite {a. f (?h a) = x}" by auto
    hence all: "\<forall>m. \<exists>n>m. f (?h n) = x" unfolding infinite_nat_iff_unbounded by auto
    from all obtain u where u: "f (?h u) = x" by auto
    from all obtain v where "v > u" and v: "f (?h v) = x" by auto

    from ** have "\<forall>i\<ge>0. h i > i" by auto
    from funpow_mono [OF this] have ***: "\<And>i j. i < j \<Longrightarrow> ?h i < ?h j" by best
    from this [OF `v > u`] have "?h u < ?h v" .
    moreover have "P (f (?h u)) (f (?h v))"
    proof -
      from refl and `x \<in> ?B (g k)` have "P x x" by (auto simp: reflp_on_def)
      thus ?thesis unfolding u v .
    qed
    ultimately show False using `bad P f` by (auto simp: good_def)
  qed
  from choice [OF this] obtain h
    where "\<forall>i. (h i) > i" and *: "\<And>i. g (h i) \<ge> g 0" by blast
  hence "\<forall>i\<ge>0. (h i) > i" by auto
  from funpow_mono [OF this] have **: "\<And>i j. i < j \<Longrightarrow> (h ^^ i) 0 < (h ^^ j) 0" by auto
  let ?i = "\<lambda>i. (h ^^ i) 0"
  let ?f = "\<lambda>i. g (?i i)"
  let ?R = "\<lambda>i. f (?i i)"
  have "\<forall>i. ?R i \<in> ?B (?f i)" using B by auto
  moreover have "\<forall>i. ?f i \<ge> ?f 0"
  proof
    fix i show "?f i \<ge> ?f 0" using * by (induct i) auto
  qed
  moreover have "bad P ?R"
  proof
    assume "good P ?R"
    then obtain i j where "i < j" and "P (?R i) (?R j)" by (auto simp: good_def)
    hence "P (f (?i i)) (f (?i j))" by simp
    moreover from ** [OF `i < j`] have "?i i < ?i j" .
    ultimately show False using `bad P f` by (auto simp: good_def)
  qed
  ultimately have "(\<forall>i. ?R i \<in> ?B (?f i) \<and> ?f i \<ge> ?f 0) \<and> bad P ?R" by auto
  hence "\<exists>f. (\<forall>i. ?R i \<in> ?B (f i) \<and> f i \<ge> f 0) \<and> bad P ?R" by auto
  hence "\<exists>R f. (\<forall>i. R i \<in> ?B (f i) \<and> f i \<ge> f 0) \<and> bad P R" by metis
  with assms(1) show False by blast
qed

end

