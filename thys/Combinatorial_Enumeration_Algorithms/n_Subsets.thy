section "N-Subsets"

theory n_Subsets
  imports
    Common_Lemmas
    "HOL-Combinatorics.Multiset_Permutations"
    Filter_Bool_List
begin

subsection"Definition"

definition n_subsets :: "'a set \<Rightarrow> nat \<Rightarrow> 'a set set" where
  "n_subsets A n = {B. B \<subseteq> A \<and> card B = n}"

text "Cardinality: \<open>binomial (card A) n\<close>"
text "Example: \<open>n_subsets {0,1,2} 2 = {{0,1}, {0,2}, {1,2}}\<close>"

subsection"Algorithm"

fun n_bool_lists :: "nat \<Rightarrow> nat \<Rightarrow> bool list list" where
  "n_bool_lists n 0 = (if n > 0 then [] else [[]])"
| "n_bool_lists n (Suc x) = (if n = 0 then [replicate (Suc x) False]
    else if n = Suc x then [replicate (Suc x) True]
    else if n > x then []
    else [False#xs . xs \<leftarrow> n_bool_lists n x] @ [True#xs . xs \<leftarrow> n_bool_lists (n-1) x])"

fun n_subset_enum :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list list" where
  "n_subset_enum xs n = [(filter_bool_list bs xs) . bs \<leftarrow> (n_bool_lists n (length xs))]"

subsection"Verification"
                        
subsubsection"n-bool-lists"

lemma n_bool_lists_True_count: "xs \<in> set (n_bool_lists n x) \<Longrightarrow> count_list xs True = n"
 by (induct x arbitrary: xs n) (auto split: if_splits simp: count_list_replicate)

lemma n_bool_lists_length: "xs \<in> set (n_bool_lists n x) \<Longrightarrow> length xs = x"
  by (induct x arbitrary: xs n) (auto split: if_splits)

lemma n_bool_lists_distinct: "distinct (n_bool_lists n x)"
proof(induct x arbitrary: n)
  case 0
  then show ?case by simp
next
  case (Suc x)
  then show ?case
    using distinct_map by fastforce
qed

lemma replicate_True_not_False: "count_list ys True = 0 \<longleftrightarrow> ys = replicate (length ys) False"
  using count_list_zero_not_elem count_list_full_elem count_list_length_replicate by fastforce

lemma n_bool_lists_correct_aux:
  "length xs = x \<Longrightarrow> count_list xs True = n \<Longrightarrow> xs \<in> set (n_bool_lists n x)"
proof(induct x arbitrary: n xs)
  case 0
  then show ?case by auto
next
  case (Suc x)
   show ?case proof(cases "n = 0")
    case True
    then show ?thesis
      using Suc True replicate_True_not_False by auto
  next
    case c1: False
    then show ?thesis proof(cases "n = Suc x")
      case True
      then have "xs = True # replicate x True "
        using Suc.prems count_list_length_replicate replicate_Suc by metis
      then show ?thesis
        using True by simp
    next
      case c2: False
      then show ?thesis proof(cases "n > x")
        case True
        then have "xs = []"
          using Suc.prems c2 count_le_length by (metis Suc_lessI linorder_not_less)
        then show ?thesis
          using Suc by auto
      next
        case c3: False
        then show ?thesis proof (cases xs)
          case Nil
          then show ?thesis
            using Suc.prems(1) by auto 
        next
          case (Cons y ys)
          then show ?thesis proof (cases y)
            case True
            then show ?thesis using Suc c1 c2 c3 Cons
              by simp 
          next
            case False 
            then show ?thesis using Suc c1 c2 c3 Cons
              by simp
          qed 
        qed
      qed
    qed
  qed
qed

lemma n_bool_lists_correct: "set (n_bool_lists n x) = {xs. length xs = x \<and> count_list xs True = n}"
proof(standard)
  show "set (n_bool_lists n x) \<subseteq> {xs. length xs = x \<and> count_list xs True = n}"
  proof(cases x)
    case 0
    then show ?thesis by simp
  next
    case (Suc x)
    then show ?thesis using n_bool_lists_True_count n_bool_lists_length
      by blast
  qed
next
  show "{xs. length xs = x \<and> count_list xs True = n} \<subseteq> set (n_bool_lists n x)"
    using n_bool_lists_correct_aux by auto
qed


subsubsection"Correctness"

lemma n_subset_enum_correct_aux1:
  "\<lbrakk>distinct xs; length ys = length xs\<rbrakk>
    \<Longrightarrow> set (filter_bool_list ys xs) \<in> n_subsets (set xs) (count_list ys True)"
  unfolding n_subsets_def
  by (auto simp: filter_bool_list_card filter_bool_list_elem)

lemma n_subset_enum_correct_aux2:
  "distinct xs \<Longrightarrow> n_subsets (set xs) n \<subseteq> set (map set (n_subset_enum xs n))"
  unfolding n_subsets_def
  by (auto simp: n_bool_lists_correct image_def filter_bool_list_exist_length_card_True)

theorem n_subset_enum_correct:
  "distinct xs \<Longrightarrow> set (map set (n_subset_enum xs n)) = n_subsets (set xs) n"
proof(standard)
  show "distinct xs \<Longrightarrow> set (map set (n_subset_enum xs n)) \<subseteq> n_subsets (set xs) n"
    using n_subset_enum_correct_aux1 n_bool_lists_correct by auto
next
  show "distinct xs \<Longrightarrow> n_subsets (set xs) n \<subseteq> set (map set (n_subset_enum xs n))"
    using n_subset_enum_correct_aux2 by auto
qed

subsubsection"Distinctness"

theorem n_subset_enum_distinct_elem:
  "distinct xs \<Longrightarrow> ys \<in> set (n_subset_enum xs n) \<Longrightarrow> distinct ys"
  by(cases "length xs < n") (auto simp: filter_bool_list_distinct)

theorem n_subset_enum_distinct: "distinct xs \<Longrightarrow> distinct (n_subset_enum xs n)"
  by(auto simp: distinct_map n_bool_lists_distinct inj_on_def filter_bool_list_inj_aux n_bool_lists_length)

subsubsection"Cardinality"

text \<open>Cardinality of @{term "n_subsets"} is already shown in @{thm [source] "Binomial.n_subsets"}.\<close>

subsection "Alternative using Multiset permutations"

text "It would be possible to define \<open>n_bool_lists\<close> using \<open>permutations_of_multiset\<close> with the
following definition:"

fun n_bool_lists2 :: "nat \<Rightarrow> nat \<Rightarrow> bool list set" where
  "n_bool_lists2 n x = (if n > x then {}
    else permutations_of_multiset (mset (replicate n True @ replicate (x-n) False)))"

subsection"\<open>mset_count\<close>"

text"Correspondence between \<open>count_list\<close> and \<open>count (mset xs)\<close> and transfer of a few results
for multisets to lists."

lemma count_list_count_mset: "count_list ys T = n \<Longrightarrow> count (mset ys) T = n"
  by(induct ys arbitrary: n) auto

lemma count_mset_count_list: "count (mset ys) T = n \<Longrightarrow> count_list ys T = n"
  by(induct ys arbitrary: n) auto

lemma count_mset_replicate_aux1:
  "\<lbrakk>\<not> x < n; mset ys = mset (replicate n True) + mset (replicate (x - n) False)\<rbrakk>
    \<Longrightarrow> count (mset ys) True = n"
  by (auto simp: count_list_count_mset count_mset)

lemma  count_mset_replicate_aux2: 
  assumes "\<not> length xs < count_list xs True"
  shows "mset xs = mset (replicate (count_list xs True) True) + mset (replicate (length xs - count_list xs True) False)"
proof -
  have "count_list xs B =
         count_list (replicate (count_list xs True) True) B + count_list (replicate (length xs - count_list xs True) False) B"
    for B
  proof(cases B)
    case True
    then show ?thesis
      by (simp add: count_list_replicate)
  next
    case False

    have "count_list xs False = count_list (replicate (length xs - count_list xs True) False) False"
      by (metis count_list_True_False count_list_replicate diff_add_inverse)
      
    from this False show ?thesis
      using assms by auto 
  qed

  then have "count (mset xs) B =
         count (mset (replicate (count_list xs True) True) + mset (replicate (length xs - count_list xs True) False)) B"
    for B
    by (metis count_mset_count_list count_union)
  
  then show "mset xs = mset (replicate (count_list xs True) True) + mset (replicate (length xs - count_list xs True) False)"
    using multiset_eqI by blast
qed

lemma n_bool_lists2_correct: "set (n_bool_lists n x) = n_bool_lists2 n x"
proof(standard)
  have "\<lbrakk>\<not> length ys < count_list ys True; x = length ys; n = count_list ys True\<rbrakk>
          \<Longrightarrow> ys \<in> permutations_of_multiset
                     (mset (replicate (count_list ys True) True) + mset (replicate (length ys - count_list ys True) False))"
          for ys
    using count_mset_replicate_aux2 permutations_of_multisetI by blast
  
  then show "set (n_bool_lists n x) \<subseteq> n_bool_lists2 n x"
    unfolding n_bool_lists_correct
    by (auto simp: count_le_length leD)
next
  have "\<lbrakk>\<not> x < n; ys \<in> permutations_of_multiset (mset (replicate n True) + mset (replicate (x - n) False))\<rbrakk>
          \<Longrightarrow> count (mset ys) True = n " for ys
    using count_mset_replicate_aux1 permutations_of_multisetD by blast
  then have "\<lbrakk>\<not> x < n; ys \<in> permutations_of_multiset (mset (replicate n True) + mset (replicate (x - n) False))\<rbrakk>
          \<Longrightarrow>  count_list ys True = n " for ys
    by (simp add: count_list_count_mset) 
  then show "n_bool_lists2 n x \<subseteq> set (n_bool_lists n x)" unfolding n_bool_lists_correct 
    by (auto simp: length_finite_permutations_of_multiset)
qed

end
