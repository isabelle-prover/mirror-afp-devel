theory BMSSP_Partition_Data_Structure
  imports BMSSP_Partition_Pull_Bridge
begin

section \<open>Concrete Partition Data Structure\<close>

text \<open>
  The abstract partition interface uses a set of active keys together with a
  value function.  A concrete implementation must be careful around \<open>Pull\<close>:
  the abstract contract removes keys but leaves the value function unchanged.
  The state below therefore stores a sorted active list and a value memory.
  Removing a key only removes it from the active list; the remembered value is
  retained for the abstraction relation.
\<close>

record 'k partition_state =
  entries_of :: "('k \<times> real) list"
  values_of :: "'k \<Rightarrow> real"

definition entry_keys :: "('k \<times> real) list \<Rightarrow> 'k set" where
  "entry_keys xs = fst ` set xs"

definition partition_state_invar :: "'k partition_state \<Rightarrow> bool" where
  "partition_state_invar P \<longleftrightarrow>
     distinct (map fst (entries_of P)) \<and>
     sorted_wrt (\<lambda>p q. snd p \<le> snd q) (entries_of P) \<and>
     (\<forall>(x, b)\<in>set (entries_of P). values_of P x = b)"

definition partition_state_view :: "'k partition_state \<Rightarrow> 'k partition_view" where
  "partition_state_view P =
     \<lparr> keys_of = entry_keys (entries_of P), value_of = values_of P \<rparr>"

definition partition_state_refines ::
  "'k partition_state \<Rightarrow> 'k partition_view \<Rightarrow> bool" where
  "partition_state_refines P D \<longleftrightarrow>
     partition_state_invar P \<and> partition_state_view P = D"

definition empty_partition_state :: "('k \<Rightarrow> real) \<Rightarrow> 'k partition_state" where
  "empty_partition_state v = \<lparr> entries_of = [], values_of = v \<rparr>"

definition partition_state_from_keys ::
  "('k \<Rightarrow> real) \<Rightarrow> 'k list \<Rightarrow> 'k partition_state" where
  "partition_state_from_keys d xs =
     \<lparr> entries_of = sort_key snd (map (\<lambda>x. (x, d x)) xs),
       values_of = d \<rparr>"

definition partition_state_insert ::
  "'k \<Rightarrow> real \<Rightarrow> 'k partition_state \<Rightarrow> 'k partition_state" where
  "partition_state_insert x b P =
     (let b' = (if x \<in> entry_keys (entries_of P)
          then min (values_of P x) b else b);
        rest = filter (\<lambda>p. fst p \<noteq> x) (entries_of P)
      in \<lparr> entries_of = sort_key snd ((x, b') # rest),
           values_of = (values_of P)(x := b') \<rparr>)"

definition partition_state_batch_prepend ::
  "('k \<times> real) list \<Rightarrow> 'k partition_state \<Rightarrow> 'k partition_state" where
  "partition_state_batch_prepend xs P =
     fold (\<lambda>(x, b) P'. partition_state_insert x b P') xs P"

definition partition_state_pull_prefix ::
  "nat \<Rightarrow> 'k partition_state \<Rightarrow> ('k \<times> real) list" where
  "partition_state_pull_prefix M P =
     (let xs = entries_of P in
      if length xs \<le> M then xs
      else takeWhile (\<lambda>p. snd p < snd (xs ! M)) xs)"

definition partition_state_pull_set ::
  "nat \<Rightarrow> 'k partition_state \<Rightarrow> 'k set" where
  "partition_state_pull_set M P =
     entry_keys (partition_state_pull_prefix M P)"

definition partition_state_pull_bound ::
  "nat \<Rightarrow> real \<Rightarrow> 'k partition_state \<Rightarrow> real" where
  "partition_state_pull_bound M B P =
     (let xs = entries_of P in if length xs \<le> M then B else snd (xs ! M))"

definition partition_state_delete_keys ::
  "'k set \<Rightarrow> 'k partition_state \<Rightarrow> 'k partition_state" where
  "partition_state_delete_keys S P =
     \<lparr> entries_of = filter (\<lambda>p. fst p \<notin> S) (entries_of P),
       values_of = values_of P \<rparr>"

definition partition_state_pull ::
  "nat \<Rightarrow> real \<Rightarrow> 'k partition_state \<Rightarrow>
    'k set \<times> real \<times> 'k partition_state" where
  "partition_state_pull M B P =
     (let S = partition_state_pull_set M P;
        beta = partition_state_pull_bound M B P
      in (S, beta, partition_state_delete_keys S P))"

definition costed_partition_state_insert ::
  "nat \<Rightarrow> 'k partition_state \<Rightarrow> 'k \<Rightarrow> real \<Rightarrow> nat \<Rightarrow>
    'k partition_state \<Rightarrow> bool" where
  "costed_partition_state_insert t P x b c P' \<longleftrightarrow>
     P' = partition_state_insert x b P \<and> c = t"

definition costed_partition_state_batch_prepend ::
  "nat \<Rightarrow> 'k partition_state \<Rightarrow> ('k \<times> real) list \<Rightarrow> nat \<Rightarrow>
    'k partition_state \<Rightarrow> bool" where
  "costed_partition_state_batch_prepend t P xs c P' \<longleftrightarrow>
     P' = partition_state_batch_prepend xs P \<and> c = t * length xs"

definition costed_partition_state_pull ::
  "nat \<Rightarrow> real \<Rightarrow> 'k partition_state \<Rightarrow> 'k set \<Rightarrow> real \<Rightarrow>
    'k partition_state \<Rightarrow> nat \<Rightarrow> bool" where
  "costed_partition_state_pull M B P S beta P' c \<longleftrightarrow>
     partition_state_pull M B P = (S, beta, P') \<and> c = card S"

lemma costed_partition_state_insert_exists:
  "\<exists>c P'. costed_partition_state_insert t P x b c P'"
  unfolding costed_partition_state_insert_def by blast

lemma costed_partition_state_insert_deterministic:
  assumes "costed_partition_state_insert t P x b c P'"
    and "costed_partition_state_insert t P x b c' P''"
  shows "c = c' \<and> P' = P''"
  using assms unfolding costed_partition_state_insert_def by blast

lemma costed_partition_state_batch_prepend_exists:
  "\<exists>c P'. costed_partition_state_batch_prepend t P xs c P'"
  unfolding costed_partition_state_batch_prepend_def by blast

lemma costed_partition_state_batch_prepend_deterministic:
  assumes "costed_partition_state_batch_prepend t P xs c P'"
    and "costed_partition_state_batch_prepend t P xs c' P''"
  shows "c = c' \<and> P' = P''"
  using assms unfolding costed_partition_state_batch_prepend_def by blast

lemma costed_partition_state_pull_exists:
  "\<exists>S beta P' c. costed_partition_state_pull M B P S beta P' c"
  unfolding costed_partition_state_pull_def
  by (metis prod_cases3)

lemma costed_partition_state_pull_deterministic:
  assumes "costed_partition_state_pull M B P S beta P' c"
    and "costed_partition_state_pull M B P S' beta' P'' c'"
  shows "S = S' \<and> beta = beta' \<and> P' = P'' \<and> c = c'"
  using assms unfolding costed_partition_state_pull_def by auto

lemma entry_keys_simps [simp]:
  "entry_keys [] = {}"
  "entry_keys (x # xs) = insert (fst x) (entry_keys xs)"
  unfolding entry_keys_def by auto

lemma entry_keys_filter_notin:
  "entry_keys (filter (\<lambda>p. fst p \<notin> S) xs) = entry_keys xs - S"
  unfolding entry_keys_def by auto

lemma entry_keys_filter_neq:
  "entry_keys (filter (\<lambda>p. fst p \<noteq> x) xs) = entry_keys xs - {x}"
  unfolding entry_keys_def by auto

lemma entry_keys_sort_key [simp]:
  "entry_keys (sort_key f xs) = entry_keys xs"
  unfolding entry_keys_def by simp

lemma entry_keys_insort_key [simp]:
  "entry_keys (insort_key f x xs) = insert (fst x) (entry_keys xs)"
  unfolding entry_keys_def by (simp add: set_insort_key)

lemma sorted_wrt_snd_sort_key [simp]:
  "sorted_wrt (\<lambda>p q. snd p \<le> snd q) (sort_key snd xs)"
proof -
  have "sorted (map snd (sort_key snd xs))"
    by (rule sorted_sort_key)
  then show ?thesis
    by (simp add: sorted_map)
qed

lemma distinct_map_fst_sort_key:
  assumes "distinct (map fst xs)"
  shows "distinct (map fst (sort_key f xs))"
proof -
  have distinct_sort: "distinct (sort_key f xs)"
    using assms unfolding distinct_map by simp
  have inj: "inj_on fst (set (sort_key f xs))"
    using assms unfolding distinct_map by simp
  show ?thesis
    unfolding distinct_map using distinct_sort inj by simp
qed

lemma empty_partition_state_invar [simp]:
  "partition_state_invar (empty_partition_state v)"
  unfolding empty_partition_state_def partition_state_invar_def by simp

lemma empty_partition_state_view [simp]:
  "partition_state_view (empty_partition_state v) =
    \<lparr> keys_of = {}, value_of = v \<rparr>"
  unfolding empty_partition_state_def partition_state_view_def by simp

lemma partition_state_from_keys_invar:
  assumes "distinct xs"
  shows "partition_state_invar (partition_state_from_keys d xs)"
proof -
  let ?ps = "map (\<lambda>x. (x, d x)) xs"
  have base_distinct: "distinct (map fst ?ps)"
    using assms by (simp add: o_def)
  have distinct_ps: "distinct (map fst (sort_key snd ?ps))"
    by (rule distinct_map_fst_sort_key[OF base_distinct])
  have values_consistent:
    "\<And>x b. (x, b) \<in> set (sort_key snd ?ps) \<Longrightarrow> d x = b"
    by auto
  have sorted_ps:
    "sorted_wrt (\<lambda>p q. snd p \<le> snd q) (sort_key snd ?ps)"
    by simp
  have consistent_ps:
    "\<forall>(x, b)\<in>set (sort_key snd ?ps). d x = b"
    using values_consistent by blast
  show ?thesis
    unfolding partition_state_from_keys_def partition_state_invar_def
    using distinct_ps sorted_ps consistent_ps by simp
qed

lemma partition_state_from_keys_view:
  "partition_state_view (partition_state_from_keys d xs) =
    \<lparr> keys_of = set xs, value_of = d \<rparr>"
  unfolding partition_state_from_keys_def partition_state_view_def entry_keys_def
  by (simp add: image_image)

lemma partition_state_from_keys_refines:
  assumes "distinct xs"
  shows "partition_state_refines (partition_state_from_keys d xs)
    \<lparr> keys_of = set xs, value_of = d \<rparr>"
  using partition_state_from_keys_invar[OF assms] partition_state_from_keys_view
  unfolding partition_state_refines_def by blast

lemma partition_state_insert_invar:
  assumes inv: "partition_state_invar P"
  shows "partition_state_invar (partition_state_insert x b P)"
proof -
  let ?b = "if x \<in> entry_keys (entries_of P) then min (values_of P x) b else b"
  let ?rest = "filter (\<lambda>p. fst p \<noteq> x) (entries_of P)"
  have distinct_rest: "distinct (map fst ?rest)"
    using inv unfolding partition_state_invar_def by (simp add: distinct_map_filter)
  have x_not_rest: "x \<notin> fst ` set ?rest"
    by auto
  have distinct_new: "distinct (map fst ((x, ?b) # ?rest))"
    using distinct_rest x_not_rest by simp
  have values_consistent:
    "\<And>y c. (y, c) \<in> set (sort_key snd ((x, ?b) # ?rest)) \<Longrightarrow>
      ((values_of P)(x := ?b)) y = c"
  proof -
    fix y c
    assume yc: "(y, c) \<in> set (sort_key snd ((x, ?b) # ?rest))"
    then have yc_set: "(y, c) \<in> set ((x, ?b) # ?rest)"
      by (metis set_sort)
    show "((values_of P)(x := ?b)) y = c"
    proof (cases "y = x")
      case True
      then have "c = ?b"
        using yc_set x_not_rest by auto
      then show ?thesis
        using True by simp
    next
      case False
      then have "(y, c) \<in> set (entries_of P)"
        using yc_set by auto
      then have "values_of P y = c"
        using inv unfolding partition_state_invar_def by auto
      then show ?thesis
        using False by simp
    qed
  qed
  have distinct_sorted:
    "distinct (map fst (sort_key snd ((x, ?b) # ?rest)))"
    by (rule distinct_map_fst_sort_key[OF distinct_new])
  have sorted_new:
    "sorted_wrt (\<lambda>p q. snd p \<le> snd q) (sort_key snd ((x, ?b) # ?rest))"
  proof -
    have "sorted (map snd (sort_key snd ((x, ?b) # ?rest)))"
      by (rule sorted_sort_key)
    then show ?thesis
      by (simp add: sorted_map)
  qed
  have consistent_new:
    "\<forall>(y, c)\<in>set (sort_key snd ((x, ?b) # ?rest)).
      ((values_of P)(x := ?b)) y = c"
    using values_consistent by blast
  show ?thesis
    unfolding partition_state_insert_def partition_state_invar_def Let_def
    using distinct_sorted sorted_new consistent_new by simp
qed

theorem partition_state_insert_refines_min_update:
  assumes "partition_state_invar P"
  shows "partition_state_view (partition_state_insert x b P) =
    min_update (partition_state_view P) x b"
  unfolding partition_state_insert_def partition_state_view_def min_update_def Let_def
  by (simp add: entry_keys_filter_neq)

theorem partition_state_insert_refines_insert_spec:
  assumes inv: "partition_state_invar P"
  shows "insert_spec (partition_state_view P) x b
    (partition_state_view (partition_state_insert x b P))"
  unfolding partition_state_insert_refines_min_update[OF inv]
  by (rule min_update_insert_spec)

theorem partition_state_insert_refines_view:
  assumes ref: "partition_state_refines P D"
  shows "partition_state_refines (partition_state_insert x b P)
    (min_update D x b)"
proof -
  have inv: "partition_state_invar P"
    and view: "partition_state_view P = D"
    using ref unfolding partition_state_refines_def by blast+
  have inv': "partition_state_invar (partition_state_insert x b P)"
    by (rule partition_state_insert_invar[OF inv])
  have view': "partition_state_view (partition_state_insert x b P) =
      min_update D x b"
    using partition_state_insert_refines_min_update[OF inv, of x b]
    unfolding view .
  show ?thesis
    using inv' view' unfolding partition_state_refines_def by blast
qed

lemma partition_state_batch_prepend_invar:
  assumes "partition_state_invar P"
  shows "partition_state_invar (partition_state_batch_prepend xs P)"
  using assms
proof (induction xs arbitrary: P)
  case Nil
  then show ?case
    unfolding partition_state_batch_prepend_def by simp
next
  case (Cons xb xs)
  obtain x b where xb: "xb = (x, b)"
    by force
  have step: "partition_state_invar (partition_state_insert x b P)"
    by (rule partition_state_insert_invar[OF Cons.prems])
  have unfold_step:
    "partition_state_batch_prepend (xb # xs) P =
      partition_state_batch_prepend xs (partition_state_insert x b P)"
    unfolding partition_state_batch_prepend_def xb by simp
  show ?case
    unfolding unfold_step
    by (rule Cons.IH[OF step])
qed

theorem partition_state_batch_prepend_refines_batch_min_update:
  assumes "partition_state_invar P"
  shows "partition_state_view (partition_state_batch_prepend xs P) =
    batch_min_update (partition_state_view P) xs"
  using assms
proof (induction xs arbitrary: P)
  case Nil
  then show ?case
    unfolding partition_state_batch_prepend_def batch_min_update_def by simp
next
  case (Cons xb xs)
  obtain x b where xb: "xb = (x, b)"
    by force
  have step_inv: "partition_state_invar (partition_state_insert x b P)"
    by (rule partition_state_insert_invar[OF Cons.prems])
  have step_view:
    "partition_state_view (partition_state_insert x b P) =
      min_update (partition_state_view P) x b"
    by (rule partition_state_insert_refines_min_update[OF Cons.prems])
  have unfold_state:
    "partition_state_batch_prepend (xb # xs) P =
      partition_state_batch_prepend xs (partition_state_insert x b P)"
    unfolding partition_state_batch_prepend_def xb by simp
  have unfold_view:
    "batch_min_update (partition_state_view P) (xb # xs) =
      batch_min_update (min_update (partition_state_view P) x b) xs"
    unfolding batch_min_update_def xb by simp
  show ?case
    unfolding unfold_state unfold_view
    using Cons.IH[OF step_inv] step_view by simp
qed

theorem partition_state_batch_prepend_refines_view:
  assumes ref: "partition_state_refines P D"
  shows "partition_state_refines (partition_state_batch_prepend xs P)
    (batch_min_update D xs)"
proof -
  have inv: "partition_state_invar P"
    and view: "partition_state_view P = D"
    using ref unfolding partition_state_refines_def by blast+
  have inv': "partition_state_invar (partition_state_batch_prepend xs P)"
    by (rule partition_state_batch_prepend_invar[OF inv])
  have view': "partition_state_view (partition_state_batch_prepend xs P) =
      batch_min_update D xs"
    using partition_state_batch_prepend_refines_batch_min_update[OF inv, of xs]
    unfolding view .
  show ?thesis
    using inv' view' unfolding partition_state_refines_def by blast
qed

lemma partition_state_delete_keys_invar:
  assumes "partition_state_invar P"
  shows "partition_state_invar (partition_state_delete_keys S P)"
  using assms
  unfolding partition_state_delete_keys_def partition_state_invar_def
  by (auto simp: distinct_map_filter sorted_wrt_filter)

lemma partition_state_delete_keys_view:
  "partition_state_view (partition_state_delete_keys S P) =
    \<lparr> keys_of = keys_of (partition_state_view P) - S,
      value_of = value_of (partition_state_view P) \<rparr>"
  unfolding partition_state_delete_keys_def partition_state_view_def
  by (auto simp: entry_keys_def)

lemma partition_state_pull_prefix_subset:
  "set (partition_state_pull_prefix M P) \<subseteq> set (entries_of P)"
  unfolding partition_state_pull_prefix_def by (auto simp: Let_def dest: set_takeWhileD)

lemma partition_state_pull_set_subset:
  "partition_state_pull_set M P \<subseteq> keys_of (partition_state_view P)"
  using partition_state_pull_prefix_subset[of M P]
  unfolding partition_state_pull_set_def partition_state_view_def entry_keys_def by auto

lemma partition_state_pull_prefix_card_le:
  assumes inv: "partition_state_invar P"
  shows "card (partition_state_pull_set M P) \<le> M"
proof (cases "length (entries_of P) \<le> M")
  case True
  have "card (partition_state_pull_set M P) =
      card (set (map fst (entries_of P)))"
    unfolding partition_state_pull_set_def partition_state_pull_prefix_def
      entry_keys_def using True by (simp add: Let_def)
  also have "\<dots> = length (entries_of P)"
  proof -
    have "distinct (map fst (entries_of P))"
      using inv unfolding partition_state_invar_def by blast
    then have "card (set (map fst (entries_of P))) =
        length (map fst (entries_of P))"
      by (rule distinct_card)
    then show ?thesis
      by simp
  qed
  finally show ?thesis
    using True by simp
next
  case False
  let ?xs = "entries_of P"
  let ?beta = "snd (?xs ! M)"
  let ?pref = "takeWhile (\<lambda>p. snd p < ?beta) ?xs"
  have M_lt: "M < length ?xs"
    using False by simp
  have len_pref: "length ?pref \<le> M"
  proof (rule ccontr)
    assume "\<not> length ?pref \<le> M"
    then have M_pref: "M < length ?pref"
      by simp
    have "?pref ! M = ?xs ! M"
      by (rule takeWhile_nth[OF M_pref])
    moreover have "?pref ! M \<in> set ?pref"
      using M_pref by simp
    ultimately show False
      using set_takeWhileD[of "?pref ! M" "\<lambda>p. snd p < ?beta" ?xs]
      by simp
  qed
  have "card (partition_state_pull_set M P) \<le> length ?pref"
  proof -
    have "card (fst ` set ?pref) \<le> card (set ?pref)"
      by (rule card_image_le) simp
    also have "\<dots> \<le> length ?pref"
      by (rule card_length)
    finally show ?thesis
      unfolding partition_state_pull_set_def partition_state_pull_prefix_def
        entry_keys_def using False by (simp add: Let_def)
  qed
  then show ?thesis
    using len_pref by linarith
qed

lemma sorted_wrt_takeWhile_less_eq_filter:
  fixes f :: "'a \<Rightarrow> 'b::linorder"
  assumes sorted: "sorted_wrt (\<lambda>x y. f x \<le> f y) xs"
  shows "takeWhile (\<lambda>x. f x < t) xs = filter (\<lambda>x. f x < t) xs"
proof (rule takeWhile_eq_filter)
  fix x
  assume x_drop: "x \<in> set (dropWhile (\<lambda>x. f x < t) xs)"
  let ?pref = "takeWhile (\<lambda>x. f x < t) xs"
  let ?drop = "dropWhile (\<lambda>x. f x < t) xs"
  obtain i where i: "i < length ?drop" "x = ?drop ! i"
    using x_drop by (auto simp: in_set_conv_nth)
  have xs_split: "?pref @ ?drop = xs"
    by simp
  have len_xs: "length xs = length ?pref + length ?drop"
    by (metis length_append xs_split)
  then have idx: "length ?pref + i < length xs"
    using i len_xs by simp
  have pref_len: "length ?pref < length xs"
    using idx by simp
  have not_first: "\<not> f (xs ! length ?pref) < t"
    using nth_length_takeWhile[of "\<lambda>x. f x < t" xs] pref_len by simp
  have "f (xs ! length ?pref) \<le> f (xs ! (length ?pref + i))"
  proof (cases i)
    case 0
    then show ?thesis by simp
  next
    case (Suc j)
    have "length ?pref < length ?pref + i"
      using Suc by simp
    then show ?thesis
      by (rule sorted_wrt_nth_less[OF sorted]) (use pref_len idx in simp_all)
  qed
  moreover have "x = xs ! (length ?pref + i)"
  proof -
    have "?drop ! i = (?pref @ ?drop) ! (length ?pref + i)"
      by (simp only: nth_append_length_plus)
    also have "\<dots> = xs ! (length ?pref + i)"
      using xs_split by simp
    finally show ?thesis
      using i by simp
  qed
  ultimately show "\<not> f x < t"
    using not_first by auto
qed

lemma partition_state_pull_set_exact:
  assumes inv: "partition_state_invar P"
    and upper: "\<And>u. u \<in> keys_of (partition_state_view P) \<Longrightarrow>
      value_of (partition_state_view P) u < B"
  shows "partition_state_pull_set M P =
    {u \<in> keys_of (partition_state_view P).
      value_of (partition_state_view P) u < partition_state_pull_bound M B P}"
proof (cases "length (entries_of P) \<le> M")
  case True
  then have pull_all:
    "partition_state_pull_set M P = keys_of (partition_state_view P)"
    unfolding partition_state_pull_set_def partition_state_pull_prefix_def
      partition_state_view_def by (simp add: Let_def)
  moreover have "partition_state_pull_bound M B P = B"
    using True unfolding partition_state_pull_bound_def by (simp add: Let_def)
  ultimately show ?thesis
    using upper by auto
next
  case False
  let ?xs = "entries_of P"
  let ?beta = "snd (?xs ! M)"
  have beta: "partition_state_pull_bound M B P = ?beta"
    using False unfolding partition_state_pull_bound_def by (simp add: Let_def)
  have sorted: "sorted_wrt (\<lambda>p q. snd p \<le> snd q) ?xs"
    using inv unfolding partition_state_invar_def by blast
  have filter_eq:
    "takeWhile (\<lambda>p. snd p < ?beta) ?xs =
      filter (\<lambda>p. snd p < ?beta) ?xs"
    by (rule sorted_wrt_takeWhile_less_eq_filter[OF sorted])
  have consistent:
    "\<And>x b. (x, b) \<in> set ?xs \<Longrightarrow> values_of P x = b"
    using inv unfolding partition_state_invar_def by auto
  show ?thesis
    unfolding partition_state_pull_set_def partition_state_pull_prefix_def
      partition_state_view_def entry_keys_def beta using False filter_eq consistent
    by (auto simp: Let_def)
qed

theorem partition_state_pull_refines_pull_separates:
  assumes inv: "partition_state_invar P"
    and upper: "\<And>u. u \<in> keys_of (partition_state_view P) \<Longrightarrow>
      value_of (partition_state_view P) u < B"
    and pull: "partition_state_pull M B P = (S, beta, P')"
  shows "pull_separates (partition_state_view P) M B S beta
    (partition_state_view P')"
proof -
  have S_def: "S = partition_state_pull_set M P"
    and beta_def: "beta = partition_state_pull_bound M B P"
    and P'_def: "P' = partition_state_delete_keys S P"
    using pull unfolding partition_state_pull_def by (auto simp: Let_def)
  have S_subset:
    "S \<subseteq> keys_of (partition_state_view P)"
    unfolding S_def by (rule partition_state_pull_set_subset)
  have card_S: "card S \<le> M"
    unfolding S_def by (rule partition_state_pull_prefix_card_le[OF inv])
  have P'_keys:
    "keys_of (partition_state_view P') = keys_of (partition_state_view P) - S"
    unfolding P'_def partition_state_delete_keys_view by simp
  have P'_values:
    "value_of (partition_state_view P') = value_of (partition_state_view P)"
    unfolding P'_def partition_state_delete_keys_view by simp
  have exact:
    "S = {u \<in> keys_of (partition_state_view P).
      value_of (partition_state_view P) u < beta}"
    unfolding S_def beta_def
    by (rule partition_state_pull_set_exact[OF inv upper])
  have pulled_before_remaining:
    "\<And>u v. \<lbrakk>u \<in> S; v \<in> keys_of (partition_state_view P')\<rbrakk> \<Longrightarrow>
      value_of (partition_state_view P) u \<le>
      value_of (partition_state_view P') v"
  proof -
    fix u v
    assume u: "u \<in> S" and v: "v \<in> keys_of (partition_state_view P')"
    have "value_of (partition_state_view P) u < beta"
      using u exact by blast
    moreover have "\<not> value_of (partition_state_view P) v < beta"
      using v P'_keys exact by blast
    ultimately show
      "value_of (partition_state_view P) u \<le>
        value_of (partition_state_view P') v"
      using P'_values by simp
  qed
  show ?thesis
  proof (cases "keys_of (partition_state_view P') = {}")
    case True
    have beta_B: "beta = B"
    proof (cases "length (entries_of P) \<le> M")
      case True
      then show ?thesis
        using beta_def unfolding partition_state_pull_bound_def by (simp add: Let_def)
    next
      case False
      let ?xs = "entries_of P"
      have M_lt: "M < length ?xs"
        using False by simp
      have nth_key: "fst (?xs ! M) \<in> keys_of (partition_state_view P)"
        unfolding partition_state_view_def entry_keys_def using nth_mem[OF M_lt] by auto
      have nth_not_S: "fst (?xs ! M) \<notin> S"
      proof -
        have beta_eq: "beta = snd (?xs ! M)"
          using beta_def False unfolding partition_state_pull_bound_def by (simp add: Let_def)
        have value_eq:
          "value_of (partition_state_view P) (fst (?xs ! M)) = snd (?xs ! M)"
          using inv nth_mem[OF M_lt]
          unfolding partition_state_invar_def partition_state_view_def by auto
        show ?thesis
          using exact beta_eq value_eq by auto
      qed
      then have "fst (?xs ! M) \<in> keys_of (partition_state_view P')"
        using nth_key P'_keys by blast
      then show ?thesis
        using True by blast
    qed
    show ?thesis
      unfolding pull_separates_def
      using S_subset card_S P'_keys P'_values True beta_B
        pulled_before_remaining by auto
  next
    case False
    have upper_pulled:
      "\<And>u. u \<in> S \<Longrightarrow> value_of (partition_state_view P) u < beta"
      using exact by blast
    have lower_remaining:
      "\<And>v. v \<in> keys_of (partition_state_view P') \<Longrightarrow>
        beta \<le> value_of (partition_state_view P') v"
      using exact P'_keys P'_values by fastforce
    show ?thesis
      unfolding pull_separates_def
      using S_subset card_S P'_keys P'_values False pulled_before_remaining
        upper_pulled lower_remaining by auto
  qed
qed

theorem partition_state_pull_refines_view:
  assumes ref: "partition_state_refines P D"
    and upper: "\<And>u. u \<in> keys_of D \<Longrightarrow> value_of D u < B"
    and pull: "partition_state_pull M B P = (S, beta, P')"
  defines "D' \<equiv> \<lparr> keys_of = keys_of D - S, value_of = value_of D \<rparr>"
  shows "partition_state_refines P' D' \<and> pull_separates D M B S beta D'"
proof -
  have inv: "partition_state_invar P"
    and view: "partition_state_view P = D"
    using ref unfolding partition_state_refines_def by blast+
  have S_def: "S = partition_state_pull_set M P"
    and P'_def: "P' = partition_state_delete_keys S P"
    using pull unfolding partition_state_pull_def by (auto simp: Let_def)
  have inv': "partition_state_invar P'"
    unfolding P'_def by (rule partition_state_delete_keys_invar[OF inv])
  have sep:
    "pull_separates (partition_state_view P) M B S beta
      (partition_state_view P')"
  proof (rule partition_state_pull_refines_pull_separates[OF inv _ pull])
    fix u
    assume "u \<in> keys_of (partition_state_view P)"
    then show "value_of (partition_state_view P) u < B"
      using upper unfolding view by simp
  qed
  have view': "partition_state_view P' = D'"
  proof -
    show ?thesis
      unfolding P'_def D'_def partition_state_delete_keys_view view by simp
  qed
  show ?thesis
    using inv' view' sep unfolding partition_state_refines_def view D'_def by simp
qed

theorem partition_state_pull_invar:
  assumes inv: "partition_state_invar P"
    and pull: "partition_state_pull M B P = (S, beta, P')"
  shows "partition_state_invar P'"
  using pull partition_state_delete_keys_invar[OF inv]
  unfolding partition_state_pull_def by (auto simp: Let_def)

theorem costed_partition_state_insert_refines:
  assumes inv: "partition_state_invar P"
    and op: "costed_partition_state_insert t P x b c P'"
  shows "partition_state_invar P' \<and>
    insert_spec (partition_state_view P) x b (partition_state_view P') \<and>
    partition_insert_cost_bound c t"
proof -
  have P'_def: "P' = partition_state_insert x b P"
    and c_def: "c = t"
    using op unfolding costed_partition_state_insert_def by blast+
  have inv': "partition_state_invar P'"
    unfolding P'_def by (rule partition_state_insert_invar[OF inv])
  have spec:
    "insert_spec (partition_state_view P) x b (partition_state_view P')"
    unfolding P'_def by (rule partition_state_insert_refines_insert_spec[OF inv])
  have cost: "partition_insert_cost_bound c t"
    unfolding c_def partition_insert_cost_bound_def by (rule order_refl)
  show ?thesis
    using inv' spec cost by blast
qed

theorem costed_partition_state_batch_prepend_refines:
  assumes inv: "partition_state_invar P"
    and op: "costed_partition_state_batch_prepend t P xs c P'"
  shows "partition_state_invar P' \<and>
    partition_state_view P' = batch_min_update (partition_state_view P) xs \<and>
    partition_batch_cost_bound c t xs"
proof -
  have P'_def: "P' = partition_state_batch_prepend xs P"
    and c_def: "c = t * length xs"
    using op unfolding costed_partition_state_batch_prepend_def by blast+
  have inv': "partition_state_invar P'"
    unfolding P'_def by (rule partition_state_batch_prepend_invar[OF inv])
  have view:
    "partition_state_view P' = batch_min_update (partition_state_view P) xs"
    unfolding P'_def
    by (rule partition_state_batch_prepend_refines_batch_min_update[OF inv])
  have cost: "partition_batch_cost_bound c t xs"
    unfolding c_def partition_batch_cost_bound_def by (rule order_refl)
  show ?thesis
    using inv' view cost by blast
qed

theorem costed_partition_state_pull_refines:
  assumes inv: "partition_state_invar P"
    and upper: "\<And>u. u \<in> keys_of (partition_state_view P) \<Longrightarrow>
      value_of (partition_state_view P) u < B"
    and op: "costed_partition_state_pull M B P S beta P' c"
  shows "partition_state_invar P' \<and>
    pull_separates (partition_state_view P) M B S beta
      (partition_state_view P') \<and>
    partition_pull_cost_bound c S"
proof -
  have pull: "partition_state_pull M B P = (S, beta, P')"
    and c_def: "c = card S"
    using op unfolding costed_partition_state_pull_def by blast+
  have inv': "partition_state_invar P'"
    by (rule partition_state_pull_invar[OF inv pull])
  have sep:
    "pull_separates (partition_state_view P) M B S beta
      (partition_state_view P')"
    by (rule partition_state_pull_refines_pull_separates[OF inv upper pull])
  have cost: "partition_pull_cost_bound c S"
    unfolding c_def partition_pull_cost_bound_def by (rule order_refl)
  show ?thesis
    using inv' sep cost by blast
qed

context unique_shortest_digraph
begin

lemma partition_state_from_keys_label_view:
  "partition_state_view (partition_state_from_keys d xs) =
    label_partition_view d (set xs)"
  unfolding partition_state_from_keys_view label_partition_view_def by simp

theorem partition_state_pull_label_set_eq_split_below:
  assumes inv: "partition_state_invar P\<^sub>D"
    and view: "partition_state_view P\<^sub>D = label_partition_view d S"
    and upper: "\<And>u. u \<in> S \<Longrightarrow> d u < B"
    and pull: "partition_state_pull M B P\<^sub>D = (S_pull, beta, P\<^sub>D')"
  shows "S_pull = split_below d S beta"
proof -
  have pull_sep:
    "pull_separates (partition_state_view P\<^sub>D) M B S_pull beta
      (partition_state_view P\<^sub>D')"
  proof (rule partition_state_pull_refines_pull_separates[OF inv _ pull])
    fix u
    assume "u \<in> keys_of (partition_state_view P\<^sub>D)"
    then show "value_of (partition_state_view P\<^sub>D) u < B"
      using upper unfolding view by simp
  qed
  show ?thesis
    using pull_separates_label_set_eq_split_below[of d S M B S_pull beta
        "partition_state_view P\<^sub>D'"] pull_sep upper
    unfolding view .
qed

theorem partition_state_pull_establishes_lower_pre:
  assumes inv: "partition_state_invar P\<^sub>D"
    and view: "partition_state_view P\<^sub>D = label_partition_view d S"
    and pre: "bmssp_pre_full d S (Fin B)"
    and upper: "\<And>u. u \<in> S \<Longrightarrow> d u < B"
    and pull: "partition_state_pull M B P\<^sub>D = (S_pull, beta, P\<^sub>D')"
  shows "bmssp_pre_full d S_pull (Fin beta)"
proof -
  have pull_eq: "S_pull = split_below d S beta"
    by (rule partition_state_pull_label_set_eq_split_below[OF inv view upper pull])
  have pull_sep:
    "pull_separates (partition_state_view P\<^sub>D) M B S_pull beta
      (partition_state_view P\<^sub>D')"
  proof (rule partition_state_pull_refines_pull_separates[OF inv _ pull])
    fix u
    assume "u \<in> keys_of (partition_state_view P\<^sub>D)"
    then show "value_of (partition_state_view P\<^sub>D) u < B"
      using upper unfolding view by simp
  qed
  show ?thesis
    unfolding pull_eq
  proof (cases "keys_of (partition_state_view P\<^sub>D') = {}")
    case True
    have "beta = B"
      using pull_separates_empty_bound[OF pull_sep True] .
    moreover have "split_below d S B = S"
      using upper unfolding split_below_def by auto
    then show "bmssp_pre_full d (split_below d S beta) (Fin beta)"
      using pre calculation by simp
  next
    case False
    obtain v where v: "v \<in> keys_of (partition_state_view P\<^sub>D')"
      using False by blast
    have beta_le_B: "beta < B"
    proof -
      have beta_le: "beta \<le> value_of (partition_state_view P\<^sub>D') v"
        by (rule pull_separates_nonempty_bound[OF pull_sep False v])
      have v_old: "v \<in> S"
        using v pull_sep unfolding pull_separates_def view by auto
      have val_eq: "value_of (partition_state_view P\<^sub>D') v = d v"
        using pull_sep unfolding pull_separates_def view by auto
      show ?thesis
        using beta_le upper[OF v_old] val_eq by linarith
    qed
    show "bmssp_pre_full d (split_below d S beta) (Fin beta)"
      by (rule pull_minimum_pre_for_lower_split[OF pre]) (simp add: beta_le_B)
  qed
qed

end

end
