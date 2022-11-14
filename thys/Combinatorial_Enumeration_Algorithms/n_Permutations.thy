section "N-Permutations"

theory n_Permutations
  imports
    "HOL-Combinatorics.Multiset_Permutations"
    Common_Lemmas
    "Falling_Factorial_Sum.Falling_Factorial_Sum_Combinatorics"
begin
subsection"Definition"

definition n_permutations :: "'a set \<Rightarrow> nat \<Rightarrow> 'a list set" where
  "n_permutations A n = {xs. set xs \<subseteq> A \<and> distinct xs \<and> length xs = n}"
text "Permutations with a maximum length. They are different from \<open>HOL-Combinatorics.Multiset_Permutations\<close>
because the entries must all be distinct."
text "Cardinality: \<open>'falling factorial' (card A) n\<close>"
text "Example: \<open>n_permutations {0,1,2} 2 = {[0,1], [0,2], [1,0], [1,2], [2,0], [2,1]}\<close>"

lemma "permutations_of_set A \<subseteq> n_permutations A (card A)"
  by (simp add: length_finite_permutations_of_set n_permutations_def permutations_of_setD subsetI)


subsection"Algorithm"
(*algorithm for permutations with arbitrary length exists in HOL-Combinatorics.Multiset_Permutations*)
fun n_permutation_enum :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list list" where
  "n_permutation_enum xs 0 = [[]]"
| "n_permutation_enum xs (Suc n) = [x#r . x \<leftarrow> xs, r \<leftarrow> n_permutation_enum (remove1 x xs) n]"

subsection"Verification"

subsubsection"Correctness"

lemma n_permutation_enum_subset: "ys \<in> set (n_permutation_enum xs n) \<Longrightarrow> set ys \<subseteq> set xs "
proof(induct n arbitrary: ys xs)
  case 0
  then show ?case by simp
next
  case (Suc n)
  obtain x where o1: "x\<in>set xs" and o2: " ys \<in> (#) x ` set (n_permutation_enum (remove1 x xs) n)"
    using Suc by auto

  have "y \<in> set (n_permutation_enum (remove1 x xs) n) \<Longrightarrow> set y \<subseteq> set xs" for y
    using Suc set_remove1_subset by fast
    
  then show ?case using o1 o2
    by fastforce
qed

lemma n_permutation_enum_length: "ys \<in> set (n_permutation_enum xs n) \<Longrightarrow> length ys = n"
  by (induct n arbitrary: ys xs) auto

lemma n_permutation_enum_elem_distinct: "distinct xs \<Longrightarrow> ys \<in> set (n_permutation_enum xs n) \<Longrightarrow> distinct ys"
proof (induct n arbitrary: ys xs)
  case 0
  then show ?case 
    by simp
next
  case (Suc n)
  then obtain z zs where o: "ys = z # zs"
    by auto
  from this Suc have t: "zs \<in> set (n_permutation_enum (remove1 z xs) n)"
    by auto

  then have "distinct zs"
    using Suc distinct_remove1 by fast

  also have "z \<notin> set zs"
    using o t n_permutation_enum_subset Suc by fastforce

  ultimately show ?case
    using o by simp
qed

lemma n_permutation_enum_correct1: "distinct xs \<Longrightarrow> set (n_permutation_enum xs n) \<subseteq> n_permutations (set xs) n"
  unfolding n_permutations_def
  using n_permutation_enum_subset n_permutation_enum_elem_distinct n_permutation_enum_length
  by fast

lemma n_permutation_enum_correct2: "ys \<in> n_permutations (set xs) n \<Longrightarrow> ys \<in> set (n_permutation_enum xs n)"
proof(induct n arbitrary: xs ys)
  case 0
  then show ?case unfolding n_permutations_def by simp
next
  case (Suc n)
  show ?case proof(cases ys)
    case Nil
    then show ?thesis using Suc
      by (simp add: n_permutations_def) 
  next
    case (Cons z zs)

    have z_in: "z \<in> set xs"
      using Suc Cons unfolding n_permutations_def by simp
    
    have 1: "set zs \<subseteq> set xs"
      using Suc Cons unfolding n_permutations_def by simp

    have 2: "length zs = n"
      using Suc Cons unfolding n_permutations_def by simp

    have 3: "distinct zs"
      using Suc Cons unfolding n_permutations_def by simp

    show ?thesis proof(cases "z \<in> set zs")
      case True
      then have "zs \<in> set (n_permutation_enum (remove1 z xs) n)" 
        using Suc Cons unfolding n_permutations_def by auto
      then show ?thesis
        using True Cons z_in by auto
    next
      case False
      then have "x \<in> set zs \<Longrightarrow> x \<in> set (remove1 z xs)" for x
        using 1 by(cases "x = z") auto

      then have "zs \<in> n_permutations (set (remove1 z xs)) n"
        unfolding n_permutations_def using 2 3 by auto
      then have "zs \<in> set (n_permutation_enum (remove1 z xs) n)"
        using Suc by simp
      then have "\<exists>x\<in>set xs. z # zs \<in> (#) x ` set (n_permutation_enum (remove1 x xs) n)"
        unfolding image_def using z_in by simp
      then show ?thesis
        using False Cons by simp
    qed
  qed 
qed

theorem n_permutation_enum_correct: "distinct xs \<Longrightarrow> set (n_permutation_enum xs n) = n_permutations (set xs) n"
proof standard
  show "distinct xs \<Longrightarrow> set (n_permutation_enum xs n) \<subseteq> n_permutations (set xs) n"
    by (simp add: n_permutation_enum_correct1)
next
  show "distinct xs \<Longrightarrow> n_permutations (set xs) n \<subseteq> set (n_permutation_enum xs n)"
    by (simp add: n_permutation_enum_correct2 subsetI)
qed


subsubsection"Distinctness"

theorem n_permutation_distinct: "distinct xs \<Longrightarrow> distinct (n_permutation_enum xs n)"
proof(induct n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?f = "\<lambda>x. (n_permutation_enum (remove1 x xs) n)"
  from Suc have "distinct (?f x)" for x
    by simp

  from this Suc show ?case
    by (auto simp: Cons_distinct_concat_map_function_distinct_on_all [of ?f xs])
qed


subsubsection"Cardinality"
thm card_lists_distinct_length_eq
theorem "finite A \<Longrightarrow> card (n_permutations A n) = ffact n (card A)"
  unfolding n_permutations_def using card_lists_distinct_length_eq
  by (metis (no_types, lifting) Collect_cong) 



subsection"\<open>n_multiset\<close> extension (with remdups)"

definition n_multiset_permutations :: "'a multiset \<Rightarrow> nat \<Rightarrow> 'a list set" where
  "n_multiset_permutations A n = {xs. mset xs \<subseteq># A \<and> length xs = n}"

fun n_multiset_permutation_enum :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list list" where
  "n_multiset_permutation_enum xs n = remdups (n_permutation_enum xs n)"

lemma "distinct (n_multiset_permutation_enum xs n)"
  by auto

lemma n_multiset_permutation_enum_correct1:
  "mset ys \<subseteq># mset xs \<Longrightarrow> ys \<in> set (n_permutation_enum xs (length ys))" 
proof(induct "ys" arbitrary: xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons y ys)
  then have "y \<in> set xs"
    by (simp add: insert_subset_eq_iff)
  moreover have "ys \<in> set (n_permutation_enum (remove1 y xs) (length ys))"
    using Cons by (simp add: insert_subset_eq_iff)
  ultimately show ?case
    using Cons by auto
qed

lemma n_multiset_permutation_enum_correct2:
  "ys \<in> set (n_permutation_enum xs n) \<Longrightarrow> mset ys \<subseteq># mset xs"
proof(induct "n" arbitrary: xs ys)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    using insert_subset_eq_iff mset_remove1 by fastforce
qed

lemma n_multiset_permutation_enum_correct:
  "set (n_multiset_permutation_enum xs n) = n_multiset_permutations (mset xs) n"
  unfolding n_multiset_permutations_def
proof(standard)
  show "set (n_multiset_permutation_enum xs n) \<subseteq> {xsa. mset xsa \<subseteq># mset xs \<and> length xsa = n}"
    by (simp add: n_multiset_permutation_enum_correct2 n_permutation_enum_length subsetI) 
next
  show "{xsa. mset xsa \<subseteq># mset xs \<and> length xsa = n} \<subseteq> set (n_multiset_permutation_enum xs n)"
    using n_multiset_permutation_enum_correct1 by auto
qed


end
