section \<open>Rankings\<close>
theory Rankings
imports
  "HOL-Combinatorics.Multiset_Permutations"
  "List-Index.List_Index"
  "Randomised_Social_Choice.Order_Predicates"
begin

subsection \<open>Preliminaries\<close>

(* TODO Move *)
lemma find_index_map: "find_index P (map f xs) = find_index (\<lambda>x. P (f x)) xs"
  by (induction xs) auto

lemma map_index_self:
  assumes "distinct xs"
  shows   "map (index xs) xs = [0..<length xs]"
proof -
  have "xs = map (\<lambda>i. xs ! i) [0..<length xs]"
    by (simp add: map_nth)
  also have "map (index xs) \<dots> = map id [0..<length xs]"
    unfolding map_map by (intro map_cong) (use assms in \<open>simp_all add: index_nth_id\<close>)
  finally show ?thesis
    by simp
qed

lemma bij_betw_map_prod:
  assumes "bij_betw f A B" "bij_betw g C D"
  shows   "bij_betw (map_prod f g) (A \<times> C) (B \<times> D)"
  using assms unfolding bij_betw_def by (auto simp: inj_on_def)

definition comap_relation :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a relation \<Rightarrow> 'b relation" where
  "comap_relation f R = (\<lambda>x y. \<exists>x' y'. x = f x' \<and> y = f y' \<and> R x' y')"
(* END TODO  *)

(* TODO: of_weak_ranking should be moved here *)
lemma is_weak_ranking_map_singleton_iff [simp]:
  "is_weak_ranking (map (\<lambda>x. {x}) xs) \<longleftrightarrow> distinct xs"
  by (induction xs) (auto simp: is_weak_ranking_Cons)

lemma is_finite_weak_ranking_map_singleton_iff [simp]:
  "is_finite_weak_ranking (map (\<lambda>x. {x}) xs) \<longleftrightarrow> distinct xs"
  by (induction xs) (auto simp: is_finite_weak_ranking_Cons)

lemma of_weak_ranking_altdef':
  assumes "is_weak_ranking xs"
  shows   "of_weak_ranking xs x y \<longleftrightarrow> x \<in> \<Union>(set xs) \<and> y \<in> \<Union>(set xs) \<and>
             find_index ((\<in>) x) xs \<ge> find_index ((\<in>) y) xs"
proof (cases "x \<in> \<Union>(set xs) \<and> y \<in> \<Union>(set xs)")
  case True
  thus ?thesis
    using True of_weak_ranking_altdef[OF assms, of x y] by auto
next
  case False
  interpret total_preorder_on "\<Union>(set xs)" "of_weak_ranking xs"
    by (rule total_preorder_of_weak_ranking) (use assms in auto)
  have "\<not>of_weak_ranking xs x y"
    using not_outside False by blast
  thus ?thesis using False
    by blast
qed


subsection \<open>Definition\<close>

text \<open>
  A \<^emph>\<open>ranking\<close> is a representation of a linear order on a finite set as a list in descending
  order, starting with the biggest element. Clearly, this gives a bijection between the linear
  orders on a finite set and the permutations of that set.
\<close>

inductive of_ranking :: "'alt list \<Rightarrow> 'alt relation" where
  "i \<le> j \<Longrightarrow> i < length xs \<Longrightarrow> j < length xs \<Longrightarrow>  xs ! i \<succeq>[of_ranking xs] xs ! j"

lemma of_ranking_conv_of_weak_ranking:
  "x \<succeq>[of_ranking xs] y \<longleftrightarrow> x \<succeq>[of_weak_ranking (map (\<lambda>x. {x}) xs)] y"
  unfolding of_ranking.simps of_weak_ranking.simps by fastforce

lemma of_ranking_imp_in_set:
  assumes "of_ranking xs a b"
  shows   "a \<in> set xs" "b \<in> set xs"
  using assms by (fastforce elim!: of_ranking.cases)+

lemma of_ranking_Nil [simp]: "of_ranking [] = (\<lambda>_ _. False)"
  by (auto simp: of_ranking.simps fun_eq_iff)

lemma of_ranking_Nil' [code]: "of_ranking [] x y = False"
  by simp

lemma of_ranking_Cons [code]:
  "x \<succeq>[of_ranking (z#zs)] y \<longleftrightarrow> x = z \<and> y \<in> set (z#zs) \<or> x \<succeq>[of_ranking zs] y" 
  by (auto simp: of_ranking_conv_of_weak_ranking of_weak_ranking_Cons)

lemma of_ranking_Cons':
  assumes "distinct (x#xs)" "a \<in> set (x#xs)" "b \<in> set (x#xs)"
  shows   "of_ranking (x#xs) a b \<longleftrightarrow> b = x \<or> (a \<noteq> x \<and> of_ranking xs a b)"
  using assms of_ranking_imp_in_set[of xs a b] by (auto simp: of_ranking_Cons)

lemma of_ranking_append:
  "x \<succeq>[of_ranking (xs @ ys)] y \<longleftrightarrow> x \<in> set xs \<and> y \<in> set ys \<or> x \<succeq>[of_ranking xs] y \<or> x \<succeq>[of_ranking ys] y" 
  by (induction xs) (auto simp: of_ranking_Cons)

lemma of_ranking_strongly_preferred_Cons_iff:
  assumes "distinct (x # xs)"
  shows   "a \<succ>[of_ranking (x # xs)] b \<longleftrightarrow> x = a \<and> b \<in> set xs \<or> a \<succ>[of_ranking xs] b"
  using assms of_ranking_imp_in_set[of xs]
  by (auto simp: strongly_preferred_def of_ranking_Cons)

lemma of_ranking_strongly_preferred_append_iff:
  assumes "distinct (xs @ ys)"
  shows   "a \<succ>[of_ranking (xs @ ys)] b \<longleftrightarrow> 
             a \<in> set xs \<and> b \<in> set ys \<or> a \<succ>[of_ranking xs] b \<or> a \<succ>[of_ranking ys] b"
  using assms of_ranking_imp_in_set[of xs a b] of_ranking_imp_in_set[of ys a b] 
              of_ranking_imp_in_set[of xs b a] of_ranking_imp_in_set[of ys b a]
  unfolding strongly_preferred_def of_ranking_append distinct_append set_eq_iff Int_iff empty_iff
  by metis

lemma not_strongly_preferred_of_ranking_iff:
  assumes "a \<in> set xs" "b \<in> set xs"
  shows   "\<not>a \<prec>[of_ranking xs] b \<longleftrightarrow> a \<succeq>[of_ranking xs] b"
  using assms unfolding strongly_preferred_def
  by (metis index_less_size_conv linorder_le_cases nth_index of_ranking.intros)

lemma of_ranking_refl:
  assumes "x \<in> set xs"
  shows   "x \<preceq>[of_ranking xs] x"
  using assms by (induction xs) (auto simp: of_ranking_Cons)

lemma of_ranking_altdef:
  assumes "distinct xs" "x \<in> set xs" "y \<in> set xs"
  shows   "of_ranking xs x y \<longleftrightarrow> index xs x \<ge> index xs y"
  unfolding of_ranking_conv_of_weak_ranking
  by (subst of_weak_ranking_altdef)
     (use assms in \<open>auto simp: index_def find_index_map eq_commute[of _ y] eq_commute[of _ x]\<close>)

lemma of_ranking_altdef':
  assumes "distinct xs"
  shows   "of_ranking xs x y \<longleftrightarrow> x \<in> set xs \<and> y \<in> set xs \<and> index xs x \<ge> index xs y"
  unfolding of_ranking_conv_of_weak_ranking
  by (subst of_weak_ranking_altdef')
     (use assms in \<open>auto simp: index_def find_index_map eq_commute[of _ y] eq_commute[of _ x]\<close>)

lemma of_ranking_nth_iff:
  assumes "distinct xs" "i < length xs" "j < length xs"
  shows   "of_ranking xs (xs ! i) (xs ! j) \<longleftrightarrow> i \<ge> j"
  using assms by (simp add: index_nth_id of_ranking_altdef)

lemma strongly_preferred_of_ranking_nth_iff:
  assumes "distinct xs" "i < length xs" "j < length xs"
  shows   "xs ! i \<succ>[of_ranking xs] xs ! j \<longleftrightarrow> i < j"
  using assms by (auto simp: strongly_preferred_def of_ranking_nth_iff)

lemma of_ranking_total: "x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> of_ranking xs x y \<or> of_ranking xs y x"
  by (induction xs) (auto simp: of_ranking_Cons)

lemma of_ranking_antisym: 
  "x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> of_ranking xs x y \<Longrightarrow> of_ranking xs y x \<Longrightarrow> distinct xs \<Longrightarrow> x = y"
  by (simp add: of_ranking_altdef')


lemma finite_linorder_of_ranking:
  assumes "set xs = A" "distinct xs"
  shows   "finite_linorder_on A (of_ranking xs)"
proof -
  interpret total_preorder_on A "of_ranking xs"
    unfolding of_ranking_conv_of_weak_ranking
    by (rule total_preorder_of_weak_ranking) (use assms in auto)
  show ?thesis
  proof
    fix x y assume "of_ranking xs x y" "of_ranking xs y x"
    thus "x = y"
      by (metis assms(1,2) index_eq_index_conv nle_le not_outside(2) of_ranking_altdef)
  qed (use assms(1) in auto)
qed

lemma linorder_of_ranking:
  assumes "set xs = A" "distinct xs"
  shows   "linorder_on A (of_ranking xs)"
proof -
  interpret finite_linorder_on A "of_ranking xs"
    by (rule finite_linorder_of_ranking) fact+
  show ?thesis ..
qed

lemma total_preorder_of_ranking:
  assumes "set xs = A" "distinct xs"
  shows   "total_preorder_on A (of_ranking xs)"
  unfolding of_ranking_conv_of_weak_ranking
  by (rule total_preorder_of_weak_ranking) (use assms in auto)



subsection \<open>Transformations\<close>

lemma map_relation_of_ranking:
  "map_relation f (of_ranking xs) = of_weak_ranking (map (\<lambda>x. f -` {x}) xs)"
  unfolding of_ranking_conv_of_weak_ranking of_weak_ranking_map map_map o_def ..

lemma of_ranking_map: "of_ranking (map f xs) = comap_relation f (of_ranking xs)"
  by (induction xs) (auto simp: comap_relation_def of_ranking_Cons fun_eq_iff)

lemma of_ranking_permute':
  assumes "f permutes set xs"
  shows   "map_relation f (of_ranking xs) = of_ranking (map (inv f) xs)"
  unfolding of_ranking_conv_of_weak_ranking
  by (subst of_weak_ranking_permute') (use assms in \<open>auto simp: map_map o_def\<close>)

lemma of_ranking_permute:
  assumes "f permutes set xs"
  shows   "of_ranking (map f xs) = map_relation (inv f) (of_ranking xs)"
  using of_ranking_permute'[OF permutes_inv[OF assms]] assms
  by (simp add: inv_inv_eq permutes_bij)

lemma of_ranking_rev [simp]:
  "of_ranking (rev xs) x y \<longleftrightarrow> of_ranking xs y x"
  unfolding of_ranking_conv_of_weak_ranking by (simp flip: rev_map)

lemma of_ranking_filter:
  "of_ranking (filter P xs) = restrict_relation {x. P x} (of_ranking xs)"
  by (induction xs) (auto simp: of_ranking_Cons restrict_relation_def fun_eq_iff)

lemma strongly_preferred_of_ranking_conv_index:
  assumes "distinct xs"
  shows   "x \<prec>[of_ranking xs] y \<longleftrightarrow> x \<in> set xs \<and> y \<in> set xs \<and> index xs x > index xs y"
  unfolding strongly_preferred_def using of_ranking_altdef'[OF assms] by auto

lemma restrict_relation_of_weak_ranking_Cons:
  assumes "distinct (x # xs)"
  shows   "restrict_relation (set xs) (of_ranking (x # xs)) = of_ranking xs"
proof -
  from assms interpret R: total_preorder_on "set xs" "of_ranking xs"
    by (intro total_preorder_of_ranking) auto
  from assms show ?thesis using R.not_outside
    by (intro ext) (auto simp: restrict_relation_def of_ranking_Cons)
qed

lemma of_ranking_zero_upt_nat:
  "of_ranking [0::nat..<n] = (\<lambda>x y. x \<ge> y \<and> x < n)"
  by (induction n) (auto simp: of_ranking_append of_ranking_Cons fun_eq_iff)

lemma of_ranking_rev_zero_upt_nat:
  "of_ranking (rev [0::nat..<n]) = (\<lambda>x y. x \<le> y \<and> y < n)"
  by (induction n) (auto simp: of_ranking_Cons fun_eq_iff)

lemma sorted_wrt_ranking: "distinct xs \<Longrightarrow> sorted_wrt (of_ranking xs) (rev xs)"
  unfolding sorted_wrt_iff_nth_less by (force simp: of_ranking.simps rev_nth)


subsection \<open>Inverse operation and isomorphism\<close>

lemma (in finite_linorder_on) of_ranking_ranking: "of_ranking (ranking le) = le"
proof -
  have "of_ranking (ranking le) = 
          of_weak_ranking (map (\<lambda>x. {the_elem x}) (weak_ranking le))"
    unfolding of_ranking_conv_of_weak_ranking ranking_def by (simp add: map_map o_def)
  also have "map (\<lambda>x. {the_elem x}) (weak_ranking le) = map (\<lambda>x. x) (weak_ranking le)"
    by (intro map_cong HOL.refl) 
       (metis is_singleton_the_elem singleton_weak_ranking)+
  also have "of_weak_ranking (map (\<lambda>x. x) (weak_ranking le)) = le"
    using of_weak_ranking_weak_ranking[OF finite_total_preorder_on_axioms] by simp
  finally show ?thesis .
qed

lemma (in finite_linorder_on) distinct_ranking: "distinct (ranking le)"
  using weak_ranking_ranking weak_ranking_total_preorder(1) by simp

lemma ranking_of_ranking:
  assumes "distinct xs"
  shows   "ranking (of_ranking xs) = xs"
proof -
  have "ranking (of_ranking xs) = map the_elem (weak_ranking (of_weak_ranking (map (\<lambda>x. {x}) xs)))"
    unfolding ranking_def of_ranking_conv_of_weak_ranking ..
  also have "\<dots> = xs"
    by (subst weak_ranking_of_weak_ranking) (use assms in \<open>auto simp: o_def\<close>)
  finally show ?thesis .
qed

lemma (in finite_linorder_on) set_ranking: "set (ranking le) = carrier"
  using weak_ranking_Union weak_ranking_ranking by auto

lemma bij_betw_permutations_of_set_finite_linorders_on:
  "bij_betw of_ranking (permutations_of_set A) {R. finite_linorder_on A R}"
  by (rule bij_betwI[of _ _ _ ranking])
     (auto simp: finite_linorder_on.of_ranking_ranking ranking_of_ranking 
                 permutations_of_set_def finite_linorder_on.distinct_ranking 
                 finite_linorder_on.set_ranking intro: finite_linorder_of_ranking)

lemma bij_betw_permutations_of_set_finite_linorders_on':
  "bij_betw ranking {R. finite_linorder_on A R} (permutations_of_set A)"
  by (rule bij_betwI[of _ _ _ of_ranking])
     (auto simp: finite_linorder_on.of_ranking_ranking ranking_of_ranking 
                 permutations_of_set_def finite_linorder_on.distinct_ranking 
                 finite_linorder_on.set_ranking intro: finite_linorder_of_ranking)

lemma card_linorders_on:
  assumes "finite A"
  shows   "card {R. linorder_on A R} = fact (card A)"
proof -
  have "{R. linorder_on A R} = {R. finite_linorder_on A R}"
    using assms by (simp add: finite_linorder_on_def finite_linorder_on_axioms_def)
  also have "card \<dots> = card (permutations_of_set A)"
    using bij_betw_same_card[OF bij_betw_permutations_of_set_finite_linorders_on[of A]] by simp
  also have "\<dots> = fact (card A)"
    using assms by simp
  finally show ?thesis .
qed

lemma finite_linorders_on [intro]:
  assumes "finite A"
  shows   "finite {R. linorder_on A R}"
proof -
  from assms have "finite (permutations_of_set A)"
    by simp
  also have "finite (permutations_of_set A) \<longleftrightarrow> finite {R. finite_linorder_on A R}"
    by (rule bij_betw_finite[OF bij_betw_permutations_of_set_finite_linorders_on])
  also have "{R. finite_linorder_on A R} = {R. linorder_on A R}"
    using assms by (simp add: finite_linorder_on_axioms.intro finite_linorder_on_def)
  finally show ?thesis .
qed

end
