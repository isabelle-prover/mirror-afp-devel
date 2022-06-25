section \<open>Ranks, $k$ smallest element and elements\<close>

theory K_Smallest
  imports 
    Frequency_Moments_Preliminary_Results
    Interpolation_Polynomials_HOL_Algebra.Interpolation_Polynomial_Cardinalities
begin

text \<open>This section contains definitions and results for the selection of the $k$ smallest elements, the $k$-th smallest element, rank of an element in an ordered set.\<close>

definition rank_of :: "'a :: linorder \<Rightarrow> 'a set \<Rightarrow> nat" where "rank_of x S = card {y \<in> S. y < x}"  
text \<open>The function @{term "rank_of"} returns the rank of an element within a set.\<close>

lemma rank_mono:
  assumes "finite S"
  shows "x \<le> y \<Longrightarrow> rank_of x S \<le> rank_of y S"
  unfolding rank_of_def using assms by (intro card_mono, auto)

lemma rank_mono_2:
  assumes "finite S"
  shows "S' \<subseteq> S \<Longrightarrow> rank_of x S' \<le> rank_of x S"
  unfolding rank_of_def using assms by (intro card_mono, auto)

lemma rank_mono_commute:
  assumes "finite S"
  assumes "S \<subseteq> T"
  assumes "strict_mono_on T f"
  assumes "x \<in> T"
  shows "rank_of x S = rank_of (f x) (f ` S)"
proof -
  have a: "inj_on f T"
    by (metis assms(3) strict_mono_on_imp_inj_on)

  have "rank_of (f x) (f ` S) = card (f ` {y \<in> S. f y < f x})"
    unfolding rank_of_def by (intro arg_cong[where f="card"], auto)
  also have "... = card (f ` {y \<in> S. y < x})"
    using assms by (intro arg_cong[where f="card"] arg_cong[where f="(`) f"])
     (meson in_mono linorder_not_le strict_mono_onD strict_mono_on_leD set_eq_iff)
  also have "... = card {y \<in> S. y < x}"
    using assms by (intro card_image  inj_on_subset[OF a], blast)
  also have "... = rank_of x S"
    by (simp add:rank_of_def)
  finally show ?thesis
    by simp
qed

definition least where "least k S = {y \<in> S. rank_of y S < k}"
text \<open>The function @{term "least"} returns the k smallest elements of a finite set.\<close>

lemma rank_strict_mono: 
  assumes "finite S"
  shows "strict_mono_on S (\<lambda>x. rank_of x S)"
proof -
  have "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x < y \<Longrightarrow> rank_of x S < rank_of y S"
    unfolding rank_of_def using assms 
    by (intro psubset_card_mono, auto)

  thus ?thesis
    by (simp add:rank_of_def strict_mono_on_def)
qed

lemma rank_of_image:
  assumes "finite S"
  shows "(\<lambda>x. rank_of x S) ` S = {0..<card S}"
proof (rule card_seteq)
  show "finite {0..<card S}" by simp

  have "\<And>x. x \<in> S \<Longrightarrow> card {y \<in> S. y < x} < card S"
    by (rule psubset_card_mono, metis assms, blast)
  thus "(\<lambda>x. rank_of x S) ` S \<subseteq> {0..<card S}"
    by (intro image_subsetI, simp add:rank_of_def)

  have "inj_on (\<lambda>x. rank_of x S) S"
    by (metis strict_mono_on_imp_inj_on rank_strict_mono assms) 
  thus "card {0..<card S} \<le> card ((\<lambda>x. rank_of x S) ` S)"
    by (simp add:card_image)
qed

lemma card_least:
  assumes "finite S"
  shows "card (least k S) = min k (card S)"
proof (cases "card S < k")
  case True
  have "\<And>t. rank_of t S \<le> card S" 
    unfolding rank_of_def using assms 
    by (intro card_mono, auto)
  hence "\<And>t. rank_of t S < k" 
    by (metis True not_less_iff_gr_or_eq order_less_le_trans)
  hence "least k S = S"
    by (simp add:least_def)
  then show ?thesis using True by simp
next
  case False
  hence a:"card S \<ge> k" using leI by blast
  hence "card ((\<lambda>x. rank_of x S) -` {0..<k} \<inter> S) = card {0..<k}"
    using assms
    by (intro card_vimage_inj_on strict_mono_on_imp_inj_on rank_strict_mono)
     (simp_all add: rank_of_image)
  hence "card (least k S) = k"
    by (simp add: Collect_conj_eq Int_commute least_def vimage_def)
  then show ?thesis using a by linarith
qed

lemma least_subset: "least k S \<subseteq> S"
  by (simp add:least_def)

lemma least_mono_commute:
  assumes "finite S"
  assumes "strict_mono_on S f"
  shows "f ` least k S = least k (f ` S)"
proof -
  have a:"inj_on f S" 
    using strict_mono_on_imp_inj_on[OF assms(2)] by simp

  have "card (least k (f ` S)) = min k (card (f ` S))"
    by (subst card_least, auto simp add:assms)
  also have "... = min k (card S)"
    by (subst card_image, metis a, auto)
  also have "... = card (least k S)"
    by (subst card_least, auto simp add:assms)
  also have "... = card (f ` least k S)"
    by (subst card_image[OF inj_on_subset[OF a]], simp_all add:least_def)
  finally have b: "card (least k (f ` S)) \<le> card (f ` least k S)" by simp

  have c: "f ` least k S \<subseteq>least k (f ` S)"
    using assms by (intro image_subsetI) 
      (simp add:least_def rank_mono_commute[symmetric, where T="S"])

  show ?thesis
    using b c assms by (intro card_seteq, simp_all add:least_def)
qed

lemma least_eq_iff:
  assumes "finite B"
  assumes "A \<subseteq> B"
  assumes "\<And>x. x \<in> B \<Longrightarrow> rank_of x B < k \<Longrightarrow> x \<in> A"
  shows "least k A = least k B"
proof -
  have "least k B \<subseteq> least k A"
    using assms rank_mono_2[OF assms(1,2)] order_le_less_trans
    by (simp add:least_def, blast) 
  moreover have "card (least k B) \<ge> card (least k A)"
    using assms finite_subset[OF assms(2,1)] card_mono[OF assms(1,2)]
    by (simp add: card_least min_le_iff_disj)
  moreover have "finite (least k A)" 
    using finite_subset least_subset assms(1,2) by metis
  ultimately show ?thesis
    by (intro card_seteq[symmetric], simp_all)
qed

lemma least_insert: 
  assumes "finite S"
  shows "least k (insert x (least k S)) = least k (insert x S)" (is "?lhs = ?rhs")
proof (rule least_eq_iff)
  show "finite (insert x S)"
    using assms(1) by simp
  show "insert x (least k S) \<subseteq> insert x S"
    using least_subset by blast
  show "y \<in> insert x (least k S)" if a: "y \<in> insert x S" and b: "rank_of y (insert x S) < k" for y
  proof -
    have "rank_of y S \<le> rank_of y (insert x S)"
      using assms by (intro rank_mono_2, auto)
    also have "... < k" using b by simp
    finally have "rank_of y S < k" by simp
    hence "y = x \<or> (y \<in> S \<and> rank_of y S < k)" 
      using a by simp
    thus ?thesis by (simp add:least_def)
  qed
qed


definition count_le where "count_le x M = size {#y \<in># M. y \<le> x#}"
definition count_less where "count_less x M = size {#y \<in># M. y < x#}"

definition nth_mset :: "nat \<Rightarrow> ('a :: linorder) multiset \<Rightarrow> 'a" where
  "nth_mset k M = sorted_list_of_multiset M ! k"

lemma nth_mset_bound_left:
  assumes "k < size M"
  assumes "count_less x M \<le> k"
  shows "x \<le> nth_mset k M"
proof (rule ccontr)
  define xs where "xs = sorted_list_of_multiset M"
  have s_xs: "sorted xs" by (simp add:xs_def sorted_sorted_list_of_multiset)
  have l_xs: "k < length xs"
    using  assms(1) by (simp add:xs_def size_mset[symmetric]) 
  have M_xs: "M = mset xs" by (simp add:xs_def)
  hence a:"\<And>i. i \<le> k \<Longrightarrow> xs ! i \<le> xs ! k"
    using s_xs l_xs sorted_iff_nth_mono by blast

  assume "\<not>(x \<le> nth_mset k M)"
  hence "x > nth_mset k M" by simp
  hence b:"x > xs ! k" by (simp add:nth_mset_def xs_def[symmetric])

  have "k < card {0..k}" by simp
  also have "... \<le> card {i. i < length xs \<and> xs ! i < x}"
    using a b l_xs order_le_less_trans 
    by (intro card_mono subsetI) auto
  also have "... = length (filter (\<lambda>y. y < x) xs)"
    by (subst length_filter_conv_card, simp)
  also have "... = size (mset (filter (\<lambda>y. y < x) xs))"
    by (subst size_mset, simp)
  also have "... = count_less x M"
    by (simp add:count_less_def M_xs)
  also have "... \<le> k"
    using assms by simp
  finally show "False" by simp
qed

lemma nth_mset_bound_left_excl:
  assumes "k < size M"
  assumes "count_le x M \<le> k"
  shows "x < nth_mset k M"
proof (rule ccontr)
  define xs where "xs = sorted_list_of_multiset M"
  have s_xs: "sorted xs" by (simp add:xs_def sorted_sorted_list_of_multiset)
  have l_xs: "k < length xs" 
    using  assms(1) by (simp add:xs_def size_mset[symmetric]) 
  have M_xs: "M = mset xs" by (simp add:xs_def)
  hence a:"\<And>i. i \<le> k \<Longrightarrow> xs ! i \<le> xs ! k"
    using s_xs l_xs sorted_iff_nth_mono by blast

  assume "\<not>(x < nth_mset k M)"
  hence "x \<ge> nth_mset k M" by simp
  hence b:"x \<ge> xs ! k" by (simp add:nth_mset_def xs_def[symmetric])

  have "k+1 \<le> card {0..k}" by simp
  also have "... \<le> card {i. i < length xs \<and> xs ! i \<le> xs ! k}"
    using a b l_xs order_le_less_trans
    by (intro card_mono subsetI, auto)
  also have "... \<le> card {i. i < length xs \<and> xs ! i \<le> x}"
    using b by (intro card_mono subsetI, auto)
  also have "... = length (filter (\<lambda>y. y \<le> x) xs)"
    by (subst length_filter_conv_card, simp)
  also have "... = size (mset (filter (\<lambda>y. y \<le> x) xs))"
    by (subst size_mset, simp)
  also have "... = count_le x M"
    by (simp add:count_le_def M_xs)
  also have "... \<le> k"
    using assms by simp
  finally show "False" by simp
qed

lemma nth_mset_bound_right:
  assumes "k < size M"
  assumes "count_le x M > k"
  shows "nth_mset k M \<le> x"
proof (rule ccontr)
  define xs where "xs = sorted_list_of_multiset M"
  have s_xs: "sorted xs" by (simp add:xs_def sorted_sorted_list_of_multiset)
  have l_xs: "k < length xs" 
    using  assms(1) by (simp add:xs_def size_mset[symmetric]) 
  have M_xs: "M = mset xs" by (simp add:xs_def)

  assume "\<not>(nth_mset k M \<le> x)"
  hence "x < nth_mset k M" by simp
  hence "x < xs ! k" 
    by (simp add:nth_mset_def xs_def[symmetric])
  hence a:"\<And>i. i < length xs \<and> xs ! i \<le> x \<Longrightarrow> i < k"
    using s_xs l_xs sorted_iff_nth_mono leI by fastforce
  have "count_le x M = size (mset (filter (\<lambda>y. y \<le> x) xs))"
    by (simp add:count_le_def M_xs)
  also have "... = length (filter (\<lambda>y. y \<le> x) xs)"
    by (subst size_mset, simp)
  also have "... = card {i. i < length xs \<and> xs ! i \<le> x}"
    by (subst length_filter_conv_card, simp)
  also have "... \<le> card {i. i < k}"
    using a by (intro card_mono subsetI, auto)
  also have "... = k" by simp
  finally have "count_le x M \<le> k" by simp
  thus "False" using assms by simp
qed

lemma nth_mset_commute_mono:
  assumes "mono f"
  assumes "k < size M"
  shows "f (nth_mset k M) = nth_mset k (image_mset f M)"
proof -
  have a:"k < length (sorted_list_of_multiset M)"
    by (metis assms(2) mset_sorted_list_of_multiset size_mset)
  show ?thesis
    using a by (simp add:nth_mset_def sorted_list_of_multiset_image_commute[OF assms(1)])
qed 

lemma nth_mset_max: 
  assumes "size A > k"
  assumes "\<And>x. x \<le> nth_mset k A \<Longrightarrow> count A x \<le> 1"
  shows "nth_mset k A = Max (least (k+1) (set_mset A))" and "card (least (k+1) (set_mset A)) = k+1"
proof -
  define xs where "xs = sorted_list_of_multiset A"
  have k_bound: "k < length xs" unfolding xs_def
    by (metis size_mset mset_sorted_list_of_multiset assms(1))  

  have A_def: "A = mset xs" by (simp add:xs_def)
  have s_xs: "sorted xs" by (simp add:xs_def sorted_sorted_list_of_multiset)
  have "\<And>x. x \<le> xs ! k \<Longrightarrow> count A x \<le> Suc 0"
    using assms(2) by (simp add:xs_def[symmetric] nth_mset_def)
  hence no_col: "\<And>x. x \<le> xs ! k \<Longrightarrow> count_list xs x \<le> 1" 
    by (simp add:A_def count_mset) 

  have inj_xs: "inj_on (\<lambda>k. xs ! k) {0..k}"
    by (rule inj_onI, simp) (metis (full_types) count_list_ge_2_iff k_bound no_col
        le_neq_implies_less linorder_not_le order_le_less_trans s_xs sorted_iff_nth_mono)

  have "\<And>y. y < length xs \<Longrightarrow> rank_of (xs ! y) (set xs) < k+1 \<Longrightarrow> y < k+1"
  proof (rule ccontr)
    fix y
    assume b:"y < length xs"
    assume "\<not>y < k +1"
    hence a:"k + 1 \<le> y" by simp

    have d:"Suc k < length xs" using a b by simp

    have "k+1 = card ((!) xs ` {0..k})" 
      by (subst card_image[OF inj_xs], simp)
    also have "... \<le> rank_of (xs ! (k+1)) (set xs)"
      unfolding rank_of_def using k_bound
      by (intro card_mono image_subsetI conjI, simp_all) (metis count_list_ge_2_iff no_col not_le le_imp_less_Suc s_xs 
          sorted_iff_nth_mono d order_less_le)
    also have "... \<le> rank_of (xs ! y) (set xs)"
      unfolding rank_of_def
      by (intro card_mono subsetI, simp_all)
       (metis Suc_eq_plus1 a b s_xs order_less_le_trans sorted_iff_nth_mono)
    also assume "... < k+1"
    finally show "False" by force
  qed

  moreover have "rank_of (xs ! y) (set xs) < k+1" if a:"y < k + 1" for y
  proof -
    have "rank_of (xs ! y) (set xs) \<le> card ((\<lambda>k. xs ! k) ` {k. k < length xs \<and> xs ! k < xs ! y})"
      unfolding rank_of_def
      by (intro card_mono subsetI, simp)
       (metis (no_types, lifting) imageI in_set_conv_nth mem_Collect_eq)
    also have "... \<le> card {k. k < length xs \<and> xs ! k < xs ! y}"
      by (rule card_image_le, simp)
    also have "... \<le> card {k. k < y}"
      by (intro card_mono subsetI, simp_all add:not_less)
       (metis sorted_iff_nth_mono s_xs linorder_not_less)
    also have "... = y" by simp
    also have "... < k + 1" using a by simp
    finally show "rank_of (xs ! y) (set xs) < k+1" by simp
  qed

  ultimately have rank_conv: "\<And>y. y < length xs \<Longrightarrow> rank_of (xs ! y) (set xs) < k+1 \<longleftrightarrow> y < k+1"
    by blast

  have "y \<le> xs ! k"  if a:"y \<in> least (k+1) (set xs)"  for y
  proof -
    have "y \<in> set xs" using a least_subset by blast
    then obtain i where i_bound: "i < length xs" and y_def: "y = xs ! i" using in_set_conv_nth by metis
    hence "rank_of (xs ! i) (set xs) < k+1"
      using a y_def i_bound by (simp add: least_def)
    hence "i < k+1"
      using rank_conv i_bound by blast
    hence "i \<le> k" by linarith
    hence "xs ! i \<le> xs ! k"
      using s_xs i_bound k_bound sorted_nth_mono by blast
    thus "y \<le> xs ! k" using y_def by simp
  qed

  moreover have "xs ! k \<in> least (k+1) (set xs)"
    using k_bound rank_conv by (simp add:least_def)

  ultimately have "Max (least (k+1) (set xs)) = xs ! k"
    by (intro Max_eqI finite_subset[OF least_subset], auto)

  hence "nth_mset k A = Max (K_Smallest.least (Suc k) (set xs))" 
    by (simp add:nth_mset_def xs_def[symmetric])
  also have "... = Max (least (k+1) (set_mset A))"
    by (simp add:A_def)
  finally show "nth_mset k A = Max (least (k+1) (set_mset A))"  by simp

  have "k + 1 = card ((\<lambda>i. xs ! i) ` {0..k})" 
    by (subst card_image[OF inj_xs], simp) 
  also have "... \<le> card (least (k+1) (set xs))"
    using rank_conv k_bound
    by (intro card_mono image_subsetI finite_subset[OF least_subset], simp_all add:least_def)
  finally have "card (least (k+1) (set xs)) \<ge> k+1" by simp
  moreover have "card (least (k+1) (set xs)) \<le> k+1"
    by (subst card_least, simp, simp)
  ultimately have "card (least (k+1) (set xs)) = k+1" by simp
  thus "card (least (k+1) (set_mset A)) = k+1"  by (simp add:A_def)
qed

end
