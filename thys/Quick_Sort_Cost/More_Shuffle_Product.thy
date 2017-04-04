(*
  File:     More_Shuffle_Product.thy
  Author:   Manuel Eberl <eberlm@in.tum.de>

  The shuffle product on finite lists.
*)
section \<open>Additional facts on the shuffle product\<close>
theory More_Shuffle_Product
  imports Complex_Main "~~/src/HOL/Library/Multiset" "../Regular-Sets/Regular_Set"
begin

(* TODO: Shuffle product should probably pulled out of Regular-Sets and into the library *)

(*
fun shuffle :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list set" where
  "shuffle [] ys = {ys}"
| "shuffle xs [] = {xs}"
| "shuffle (x#xs) (y#ys) = (op # x) ` shuffle xs (y#ys) \<union> (op # y) ` shuffle (x#xs) ys"
*)
  
lemma shuffle_Cons: 
  "shuffle (x # xs) (y # ys) = (op # x) ` shuffle xs (y # ys) \<union> (op # y) ` shuffle (x # xs) ys"
  by auto

lemma Nil_in_shuffleI: "xs = [] \<Longrightarrow> ys = [] \<Longrightarrow> [] \<in> shuffle xs ys" 
  by simp
    
lemma Cons_in_shuffle_leftI: "zs \<in> shuffle xs ys \<Longrightarrow> z # zs \<in> shuffle (z # xs) ys"
  by (cases ys) auto

lemma Cons_in_shuffle_rightI: "zs \<in> shuffle xs ys \<Longrightarrow> z # zs \<in> shuffle xs (z # ys)"
  by (cases xs) auto

lemma finite_shuffle [simp, intro]: "finite (shuffle xs ys)"
  by (induction xs ys rule: shuffle.induct) simp_all
    
lemma length_shuffle [simp]: "zs \<in> shuffle xs ys \<Longrightarrow> length zs = length xs + length ys"
  by (induction xs ys arbitrary: zs rule: shuffle.induct) auto

lemma mset_shuffle [simp]: "zs \<in> shuffle xs ys \<Longrightarrow> mset zs = mset xs + mset ys"
  by (induction xs ys arbitrary: zs rule: shuffle.induct) auto
    
lemma set_shuffle [simp]: "zs \<in> shuffle xs ys \<Longrightarrow> set zs = set xs \<union> set ys"
  by (induction xs ys arbitrary: zs rule: shuffle.induct) auto

lemma distinct_disjoint_shuffle:
  assumes "distinct xs" "distinct ys" "set xs \<inter> set ys = {}" "zs \<in> shuffle xs ys"
  shows   "distinct zs"
  using assms by (auto simp: distinct_count_atmost_1)

lemma shuffle_commutes: "shuffle xs ys = shuffle ys xs"
  by (induction xs ys rule: shuffle.induct) (simp_all add: Un_commute)
    
lemma card_disjoint_shuffle: 
  assumes "set xs \<inter> set ys = {}"
  shows   "card (shuffle xs ys) = (length xs + length ys) choose length xs"
using assms
proof (induction xs ys rule: shuffle.induct)
  case (3 x xs y ys)
  have "shuffle (x # xs) (y # ys) = op # x ` shuffle xs (y # ys) \<union> op # y ` shuffle (x # xs) ys"
    by (rule shuffle_Cons)
  also have "card \<dots> = card (op # x ` shuffle xs (y # ys)) + card (op # y ` shuffle (x # xs) ys)"
    by (rule card_Un_disjoint) (insert "3.prems", auto)
  also have "card (op # x ` shuffle xs (y # ys)) = card (shuffle xs (y # ys))"
    by (rule card_image) auto
  also have "\<dots> = (length xs + length (y # ys)) choose length xs"
    using "3.prems" by (intro "3.IH") auto
  also have "card (op # y ` shuffle (x # xs) ys) = card (shuffle (x # xs) ys)"
    by (rule card_image) auto
  also have "\<dots> = (length (x # xs) + length ys) choose length (x # xs)"
    using "3.prems" by (intro "3.IH") auto
  also have "length xs + length (y # ys) choose length xs + \<dots> = 
               (length (x # xs) + length (y # ys)) choose length (x # xs)" by simp
  finally show ?case .
qed auto

lemma image_filter_Cons: 
  "filter P ` op # x ` A = (if P x then op # x ` filter P ` A else filter P ` A)"
  by (auto simp: image_image)

lemma Cons_shuffle_subset1: "op # x ` shuffle xs ys \<subseteq> shuffle (x # xs) ys"
  by (cases ys) auto
    
lemma Cons_shuffle_subset2: "op # y ` shuffle xs ys \<subseteq> shuffle xs (y # ys)"
  by (cases xs) auto

lemma filter_shuffle:
  "filter P ` shuffle xs ys = shuffle (filter P xs) (filter P ys)"
  by (induction xs ys rule: shuffle.induct)
     (simp_all split: if_splits add: image_Un image_filter_Cons Un_absorb1 Un_absorb2 
           Cons_shuffle_subset1 Cons_shuffle_subset2 shuffle_Cons del: shuffle.simps(3))

lemma filter_shuffle_disjoint1:
  assumes "set xs \<inter> set ys = {}" "zs \<in> shuffle xs ys"
  shows   "filter (\<lambda>x. x \<in> set xs) zs = xs" (is "filter ?P _ = _")
    and   "filter (\<lambda>x. x \<notin> set xs) zs = ys" (is "filter ?Q _ = _")
  using assms
proof -
  from assms have "filter ?P zs \<in> filter ?P ` shuffle xs ys" by blast
  also have "filter ?P ` shuffle xs ys = shuffle (filter ?P xs) (filter ?P ys)"
    by (rule filter_shuffle)
  also have "filter ?P xs = xs" by (rule filter_True) simp_all
  also have "filter ?P ys = []" by (rule filter_False) (insert assms(1), auto)
  also have "shuffle xs [] = {xs}" by simp
  finally show "filter ?P zs = xs" by simp
next
  from assms have "filter ?Q zs \<in> filter ?Q ` shuffle xs ys" by blast
  also have "filter ?Q ` shuffle xs ys = shuffle (filter ?Q xs) (filter ?Q ys)"
    by (rule filter_shuffle)
  also have "filter ?Q ys = ys" by (rule filter_True) (insert assms(1), auto)
  also have "filter ?Q xs = []" by (rule filter_False) (insert assms(1), auto)
  also have "shuffle [] ys = {ys}" by simp
  finally show "filter ?Q zs = ys" by simp
qed

lemma filter_shuffle_disjoint2:
  assumes "set xs \<inter> set ys = {}" "zs \<in> shuffle xs ys"
  shows   "filter (\<lambda>x. x \<in> set ys) zs = ys" "filter (\<lambda>x. x \<notin> set ys) zs = xs"
  using filter_shuffle_disjoint1[of ys xs zs] assms 
  by (simp_all add: shuffle_commutes Int_commute)

lemma partition_in_shuffle:
  "xs \<in> shuffle (filter P xs) (filter (\<lambda>x. \<not>P x) xs)"
proof (induction xs)
  case (Cons x xs)
  show ?case
  proof (cases "P x")
    case True
    hence "x # xs \<in> op # x ` shuffle (filter P xs) (filter (\<lambda>x. \<not>P x) xs)"
      by (intro imageI Cons.IH)
    also have "\<dots> \<subseteq> shuffle (filter P (x # xs)) (filter (\<lambda>x. \<not>P x) (x # xs))"
      by (simp add: True Cons_shuffle_subset1)
    finally show ?thesis .
  next
    case False
    hence "x # xs \<in> op # x ` shuffle (filter P xs) (filter (\<lambda>x. \<not>P x) xs)"
      by (intro imageI Cons.IH)
    also have "\<dots> \<subseteq> shuffle (filter P (x # xs)) (filter (\<lambda>x. \<not>P x) (x # xs))"
      by (simp add: False Cons_shuffle_subset2)
    finally show ?thesis .
  qed
qed auto

lemma inv_image_partition:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> P x" "\<And>y. y \<in> set ys \<Longrightarrow> \<not>P y"
  shows   "partition P -` {(xs, ys)} = shuffle xs ys"
proof (intro equalityI subsetI)
  fix zs assume zs: "zs \<in> shuffle xs ys"
  hence [simp]: "set zs = set xs \<union> set ys" by (rule set_shuffle)
  from assms have "filter P zs = filter (\<lambda>x. x \<in> set xs) zs" 
                  "filter (\<lambda>x. \<not>P x) zs = filter (\<lambda>x. x \<in> set ys) zs"
    by (intro filter_cong refl; force)+
  moreover from assms have "set xs \<inter> set ys = {}" by auto
  ultimately show "zs \<in> partition P -` {(xs, ys)}" using zs
    by (simp add: o_def filter_shuffle_disjoint1 filter_shuffle_disjoint2)
next
  fix zs assume "zs \<in> partition P -` {(xs, ys)}"
  thus "zs \<in> shuffle xs ys" using partition_in_shuffle[of zs] by (auto simp: o_def)
qed

end
