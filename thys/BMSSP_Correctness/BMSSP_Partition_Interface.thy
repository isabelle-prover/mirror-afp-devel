theory BMSSP_Partition_Interface
  imports BMSSP_Correctness
begin

section \<open>Partition Data-Structure Interface\<close>

text \<open>
  The algorithm's non-base BMSSP loop depends on a partition data structure with
  \<open>Insert\<close>, \<open>BatchPrepend\<close>, and \<open>Pull\<close>.  This theory records the
  mathematical contract of those operations.  It also gives a sorted reference
  implementation of the functional \<open>Pull\<close> contract.  The separate concrete
  partition-state theory refines this view with explicit active entries,
  retained value memory, costed operations, and pull-to-split bridge theorems.

  The interface is intentionally small.  A partition view is just a finite set
  of keys with a real-valued label for each key.  In the algorithm those labels
  are tentative distances, but the interface does not mention graphs.  This
  separation is what lets the correctness proof talk about the mathematical
  effect of a pull, while the bucketed refinement later proves that a concrete
  representation implements the same effect with the desired costs.

  Three design choices are worth making explicit.  First, inserts are
  minimum-updates: inserting an existing key keeps the smaller label.  Second,
  batch prepends are admissible only when every prepended label is below every
  remaining partition label.  This is the abstract form of the "prepend a lower
  block" operation in the paper.  Third, a pull does not merely return any small
  set.  It returns a prefix of the partition order, a separating bound, and a
  residual view whose values are unchanged.

  The sorted reference implementation at the end of the file is not the
  efficient implementation used for the final headline.  It is a specification
  device.  Sorting the keys by label makes the pull contract transparent, and
  the bucketed structure is later shown to realise the same contract while
  satisfying the paper-tight amortised bounds.
\<close>

record 'k partition_view =
  keys_of :: "'k set"
  value_of :: "'k \<Rightarrow> real"

definition min_update where
  "min_update D x b =
    \<lparr> keys_of = insert x (keys_of D),
      value_of = (value_of D)(x := if x \<in> keys_of D then min (value_of D x) b else b) \<rparr>"

definition insert_spec where
  "insert_spec D x b D' \<longleftrightarrow>
     keys_of D' = insert x (keys_of D) \<and>
     value_of D' x = (if x \<in> keys_of D then min (value_of D x) b else b) \<and>
     (\<forall>y. y \<noteq> x \<longrightarrow> value_of D' y = value_of D y)"

definition batch_min_update where
  "batch_min_update D xs = fold (\<lambda>(x, b) D'. min_update D' x b) xs D"

definition pull_separates where
  "pull_separates D M B S x D' \<longleftrightarrow>
     S \<subseteq> keys_of D \<and>
     card S \<le> M \<and>
     keys_of D' = keys_of D - S \<and>
     value_of D' = value_of D \<and>
     (\<forall>u\<in>S. \<forall>v\<in>keys_of D'. value_of D u \<le> value_of D' v) \<and>
     (if keys_of D' = {} then x = B
      else (\<forall>u\<in>S. value_of D u < x) \<and> (\<forall>v\<in>keys_of D'. x \<le> value_of D' v))"

definition batch_prepend_admissible where
  "batch_prepend_admissible D xs \<longleftrightarrow>
     (\<forall>(x, b)\<in>set xs. \<forall>y\<in>keys_of D. b \<le> value_of D y)"

definition partition_upper_bound where
  "partition_upper_bound D B \<longleftrightarrow> (\<forall>u\<in>keys_of D. value_of D u < B)"

definition partition_insert_cost_bound where
  "partition_insert_cost_bound c t \<longleftrightarrow> c \<le> t"

definition partition_batch_cost_bound where
  "partition_batch_cost_bound c t xs \<longleftrightarrow> c \<le> t * length xs"

definition partition_pull_cost_bound where
  "partition_pull_cost_bound c S \<longleftrightarrow> c \<le> card S"

text \<open>
  The three cost predicates are deliberately parametric and algebraic.  They do
  not prescribe an implementation, only the local budget that an implementation
  must provide to plug into the runtime recurrence.  The sorted reference pull
  has a linear cost, while the bucketed implementation later supplies the
  stronger logarithmic and amortised bounds required by the paper.

  The summation lemmas below are the interface's first payoff: once individual
  operations satisfy their local predicates, loop-level proofs can sum costs by
  list induction without opening the implementation of the data structure.
\<close>

lemma partition_insert_costs_sum_bound:
  assumes "list_all (\<lambda>c. partition_insert_cost_bound c t) cs"
  shows "sum_list cs \<le> t * length cs"
  using assms
proof (induction cs)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  then have c: "c \<le> t"
    unfolding partition_insert_cost_bound_def by simp
  have tail: "sum_list cs \<le> t * length cs"
    using Cons.IH Cons.prems by simp
  show ?case
    using c tail by simp
qed

lemma partition_batch_costs_sum_bound:
  assumes "list_all2 (\<lambda>c xs. partition_batch_cost_bound c t xs) cs xss"
  shows "sum_list cs \<le> t * sum_list (map length xss)"
  using assms
proof (induction cs arbitrary: xss)
  case Nil
  then show ?case
    by (cases xss) simp_all
next
  case (Cons c cs)
  then obtain xs xss' where xss: "xss = xs # xss'"
    and c: "c \<le> t * length xs"
    and rest: "list_all2 (\<lambda>c xs. partition_batch_cost_bound c t xs) cs xss'"
    by (cases xss) (auto simp: partition_batch_cost_bound_def)
  have tail: "sum_list cs \<le> t * sum_list (map length xss')"
    using Cons.IH[OF rest] .
  show ?case
  proof -
    have "c + sum_list cs \<le>
        t * length xs + t * sum_list (map length xss')"
      using c tail by simp
    also have "\<dots> = t * (length xs + sum_list (map length xss'))"
      by (simp add: algebra_simps)
    finally show ?thesis
      unfolding xss by simp
  qed
qed

lemma partition_pull_costs_sum_bound:
  assumes "list_all2 (\<lambda>c S. partition_pull_cost_bound c S) cs Ss"
  shows "sum_list cs \<le> sum_list (map card Ss)"
  using assms
proof (induction cs arbitrary: Ss)
  case Nil
  then show ?case
    by (cases Ss) simp_all
next
  case (Cons c cs)
  then obtain S Ss' where Ss: "Ss = S # Ss'"
    and c: "c \<le> card S"
    and rest: "list_all2 (\<lambda>c S. partition_pull_cost_bound c S) cs Ss'"
    by (cases Ss) (auto simp: partition_pull_cost_bound_def)
  have tail: "sum_list cs \<le> sum_list (map card Ss')"
    using Cons.IH[OF rest] .
  show ?case
    using c tail unfolding Ss by simp
qed

lemma partition_batch_cost_bound_append:
  assumes xs: "partition_batch_cost_bound c_x t xs"
    and ys: "partition_batch_cost_bound c_y h ys"
    and h_le_t: "h \<le> t"
  shows "partition_batch_cost_bound (c_x + c_y) t (xs @ ys)"
proof -
  have c_x: "c_x \<le> t * length xs"
    using xs unfolding partition_batch_cost_bound_def by simp
  have c_y: "c_y \<le> h * length ys"
    using ys unfolding partition_batch_cost_bound_def by simp
  have "h * length ys \<le> t * length ys"
    using h_le_t by simp
  then have "c_x + c_y \<le> t * length xs + t * length ys"
    using c_x c_y by linarith
  also have "\<dots> = t * length (xs @ ys)"
    by (simp add: algebra_simps)
  finally show ?thesis
    unfolding partition_batch_cost_bound_def .
qed

lemma batch_prepend_admissibleI:
  assumes "\<And>x b y. \<lbrakk>(x, b) \<in> set xs; y \<in> keys_of D\<rbrakk> \<Longrightarrow>
    b \<le> value_of D y"
  shows "batch_prepend_admissible D xs"
  using assms unfolding batch_prepend_admissible_def by auto

lemma batch_prepend_admissible_below_all:
  assumes vals: "\<And>x b. (x, b) \<in> set xs \<Longrightarrow> b \<le> L"
    and lower: "\<And>y. y \<in> keys_of D \<Longrightarrow> L \<le> value_of D y"
  shows "batch_prepend_admissible D xs"
proof (rule batch_prepend_admissibleI)
  fix x b y
  assume xb: "(x, b) \<in> set xs" and y: "y \<in> keys_of D"
  have "b \<le> L"
    by (rule vals[OF xb])
  moreover have "L \<le> value_of D y"
    by (rule lower[OF y])
  then show "b \<le> value_of D y"
    using calculation by linarith
qed

lemma sorted_value_less_nth_in_take:
  fixes f :: "'a \<Rightarrow> 'b::linorder"
  assumes sorted: "sorted_wrt (\<lambda>u v. f u \<le> f v) xs"
    and y: "y \<in> set xs"
    and lt: "f y < f (xs ! k)"
    and k: "k < length xs"
  shows "y \<in> set (take k xs)"
proof -
  obtain i where i: "i < length xs" "xs ! i = y"
    using y by (auto simp: in_set_conv_nth)
  have "i < k"
  proof (rule ccontr)
    assume "\<not> i < k"
    then have k_le_i: "k \<le> i"
      by simp
    show False
    proof (cases "k = i")
      case True
      have "f y < f y"
        using lt i(2) True by simp
      then show ?thesis
        using less_irrefl by blast
    next
      case False
      with k_le_i have "k < i"
        by simp
      then have "f (xs ! k) \<le> f (xs ! i)"
        using sorted_wrt_nth_less[OF sorted, of k i] i(1) by simp
      then show ?thesis
        using lt i(2) by simp
    qed
  qed
  then have "i < length (take k xs)" "take k xs ! i = y"
    using i by auto
  then show ?thesis
    using nth_mem by metis
qed

text \<open>
  The sorted reference view chooses one canonical order of the partition keys:
  any distinct list sorted by @{const value_of}.  Isabelle's Hilbert choice is
  used only to avoid committing to a concrete sorting algorithm in the
  specification.  The theorem \<open>partition_key_order_properties\<close> immediately
  recovers the facts needed by later proofs: the order contains exactly the
  keys, has no duplicates, and is sorted by label.

  The reference pull then takes the first block of that order.  If at most
  \<open>M\<close> keys remain, the pull consumes everything and returns the outer bound.
  Otherwise it uses the \<open>M\<close>-th key as the separating bound and pulls exactly
  the keys with smaller labels.  This strict comparison matches the BMSSP lower
  split used by the correctness proof.
\<close>

definition partition_key_order where
  "partition_key_order D =
    (SOME xs. set xs = keys_of D \<and> distinct xs \<and>
      sorted_wrt (\<lambda>u v. value_of D u \<le> value_of D v) xs)"

definition sorted_pull_cost where
  "sorted_pull_cost D = length (partition_key_order D)"

lemma partition_key_order_properties:
  assumes finite_keys: "finite (keys_of D)"
  shows "set (partition_key_order D) = keys_of D"
    and "distinct (partition_key_order D)"
    and "sorted_wrt (\<lambda>u v. value_of D u \<le> value_of D v) (partition_key_order D)"
proof -
  obtain xs where xs: "set xs = keys_of D" "distinct xs"
    using finite_distinct_list[OF finite_keys] by blast
  let ?ys = "sort_key (value_of D) xs"
  have exists:
    "\<exists>ys. set ys = keys_of D \<and> distinct ys \<and>
      sorted_wrt (\<lambda>u v. value_of D u \<le> value_of D v) ys"
  proof (intro exI[of _ ?ys] conjI)
    show "set ?ys = keys_of D"
      using xs by simp
    show "distinct ?ys"
      using xs by simp
    show "sorted_wrt (\<lambda>u v. value_of D u \<le> value_of D v) ?ys"
    proof -
      have "sorted (map (value_of D) ?ys)"
        by (rule sorted_sort_key)
      then show ?thesis
        by (simp add: sorted_map)
    qed
  qed
  have props: "set (partition_key_order D) = keys_of D \<and>
      distinct (partition_key_order D) \<and>
      sorted_wrt (\<lambda>u v. value_of D u \<le> value_of D v) (partition_key_order D)"
    unfolding partition_key_order_def by (rule someI_ex[OF exists])
  then show "set (partition_key_order D) = keys_of D"
    by blast
  from props show "distinct (partition_key_order D)"
    by blast
  from props show "sorted_wrt (\<lambda>u v. value_of D u \<le> value_of D v) (partition_key_order D)"
    by blast
qed

definition sorted_pull_set where
  "sorted_pull_set M D =
    (let xs = partition_key_order D in
      if length xs \<le> M then set xs
      else {u \<in> keys_of D. value_of D u < value_of D (xs ! M)})"

definition sorted_pull_bound where
  "sorted_pull_bound M B D =
    (let xs = partition_key_order D in
      if length xs \<le> M then B else value_of D (xs ! M))"

definition remove_keys_view where
  "remove_keys_view D S =
    \<lparr> keys_of = keys_of D - S, value_of = value_of D \<rparr>"

lemma min_update_keys [simp]:
  "keys_of (min_update D x b) = insert x (keys_of D)"
  unfolding min_update_def by simp

lemma min_update_value_same:
  assumes "y \<noteq> x"
  shows "value_of (min_update D x b) y = value_of D y"
  using assms unfolding min_update_def by simp

lemma min_update_value_key_new:
  assumes "x \<notin> keys_of D"
  shows "value_of (min_update D x b) x = b"
  using assms unfolding min_update_def by simp

lemma min_update_value_key_old:
  assumes "x \<in> keys_of D"
  shows "value_of (min_update D x b) x = min (value_of D x) b"
  using assms unfolding min_update_def by simp

lemma min_update_value_le_old:
  assumes "x \<in> keys_of D"
  shows "value_of (min_update D y b) x \<le> value_of D x"
proof (cases "x = y")
  case True
  then show ?thesis
    using assms unfolding min_update_def by simp
next
  case False
  then show ?thesis
    using min_update_value_same[of x y D b] by simp
qed

lemma min_update_value_le_inserted:
  "value_of (min_update D x b) x \<le> b"
  unfolding min_update_def by simp

theorem min_update_insert_spec:
  "insert_spec D x b (min_update D x b)"
  unfolding insert_spec_def min_update_def by auto

lemma min_update_preserves_upper_bound:
  assumes upper: "partition_upper_bound D B"
    and b_lt: "b < B"
  shows "partition_upper_bound (min_update D x b) B"
proof -
  have "\<And>u. u \<in> keys_of (min_update D x b) \<Longrightarrow>
      value_of (min_update D x b) u < B"
  proof -
    fix u
    assume u: "u \<in> keys_of (min_update D x b)"
    show "value_of (min_update D x b) u < B"
    proof (cases "u = x")
      case True
      then show ?thesis
      proof (cases "x \<in> keys_of D")
        case True
        then have "min (value_of D x) b < B"
          using upper b_lt unfolding partition_upper_bound_def by simp
        then show ?thesis
          using \<open>u = x\<close> True unfolding min_update_def by simp
      next
        case False
        then show ?thesis
          using \<open>u = x\<close> b_lt unfolding min_update_def by simp
      qed
    next
      case False
      then have "u \<in> keys_of D"
        using u unfolding min_update_def by simp
      then have "value_of D u < B"
        using upper unfolding partition_upper_bound_def by blast
      then show ?thesis
        using False min_update_value_same[of u x D b] by simp
    qed
  qed
  then show ?thesis
    unfolding partition_upper_bound_def by blast
qed

lemma batch_min_update_keys_subset:
  "keys_of (batch_min_update D xs) \<subseteq> keys_of D \<union> fst ` set xs"
proof (induction xs arbitrary: D)
  case Nil
  then show ?case
    unfolding batch_min_update_def by simp
next
  case (Cons xb xs)
  obtain x b where xb: "xb = (x, b)"
    by force
  have "keys_of (batch_min_update (min_update D x b) xs)
      \<subseteq> keys_of (min_update D x b) \<union> fst ` set xs"
    using Cons.IH[of "min_update D x b"] .
  also have "\<dots> \<subseteq> keys_of D \<union> fst ` set (xb # xs)"
    using xb by auto
  finally show ?case
    unfolding batch_min_update_def xb by simp
qed

lemma batch_min_update_keys:
  "keys_of (batch_min_update D xs) = keys_of D \<union> fst ` set xs"
proof (induction xs arbitrary: D)
  case Nil
  then show ?case
    unfolding batch_min_update_def by simp
next
  case (Cons xb xs)
  obtain x b where xb: "xb = (x, b)"
    by force
  have "keys_of (batch_min_update (min_update D x b) xs) =
      keys_of (min_update D x b) \<union> fst ` set xs"
    using Cons.IH[of "min_update D x b"] .
  then show ?case
    unfolding batch_min_update_def xb by auto
qed

lemma batch_min_update_value_le_old:
  assumes "x \<in> keys_of D"
  shows "value_of (batch_min_update D xs) x \<le> value_of D x"
  using assms
proof (induction xs arbitrary: D)
  case Nil
  then show ?case
    unfolding batch_min_update_def by simp
next
  case (Cons xb xs)
  obtain y b where xb: "xb = (y, b)"
    by force
  have x_in_step: "x \<in> keys_of (min_update D y b)"
    using Cons.prems by simp
  have tail:
    "value_of (batch_min_update (min_update D y b) xs) x \<le>
      value_of (min_update D y b) x"
    by (rule Cons.IH[OF x_in_step])
  have step: "value_of (min_update D y b) x \<le> value_of D x"
    by (rule min_update_value_le_old[OF Cons.prems])
  have tail_fold:
    "value_of (fold (\<lambda>(x, b) D'. min_update D' x b) xs (min_update D y b)) x \<le>
      value_of (min_update D y b) x"
    using tail unfolding batch_min_update_def .
  show ?case
    unfolding batch_min_update_def xb
    using tail_fold step by (simp add: case_prod_beta)
qed

lemma batch_min_update_value_le_pair:
  assumes "(x, b) \<in> set xs"
  shows "value_of (batch_min_update D xs) x \<le> b"
  using assms
proof (induction xs arbitrary: D)
  case Nil
  then show ?case by simp
next
  case (Cons xb xs)
  obtain y c where xb: "xb = (y, c)"
    by force
  show ?case
  proof (cases "(x, b) = (y, c)")
    case True
    have x_in_step: "x \<in> keys_of (min_update D y c)"
      using True by simp
    have tail:
      "value_of (batch_min_update (min_update D y c) xs) x \<le>
        value_of (min_update D y c) x"
      by (rule batch_min_update_value_le_old[OF x_in_step])
    have step: "value_of (min_update D y c) x \<le> b"
      using True min_update_value_le_inserted[of D y c] by simp
    have tail_fold:
      "value_of (fold (\<lambda>(x, b) D'. min_update D' x b) xs (min_update D y c)) x \<le>
        value_of (min_update D y c) x"
      using tail unfolding batch_min_update_def .
    show ?thesis
      unfolding batch_min_update_def xb
      using tail_fold step by (simp add: case_prod_beta)
  next
    case False
    then have "(x, b) \<in> set xs"
      using Cons.prems xb by auto
    then have tail:
      "value_of (batch_min_update (min_update D y c) xs) x \<le> b"
      by (rule Cons.IH)
    have tail_fold:
      "value_of (fold (\<lambda>(x, b) D'. min_update D' x b) xs (min_update D y c)) x \<le> b"
      using tail unfolding batch_min_update_def .
    show ?thesis
      unfolding batch_min_update_def xb
      using tail_fold by (simp add: case_prod_beta)
  qed
qed

lemma sorted_pull_cost_linear:
  assumes finite_keys: "finite (keys_of D)"
  shows "sorted_pull_cost D = card (keys_of D)"
proof -
  have "length (partition_key_order D) = card (set (partition_key_order D))"
    using partition_key_order_properties(2)[OF finite_keys] by (simp add: distinct_card)
  also have "\<dots> = card (keys_of D)"
    using partition_key_order_properties(1)[OF finite_keys] by simp
  finally show ?thesis
    unfolding sorted_pull_cost_def .
qed

text \<open>
  The minimum-update lemmas establish the functional behaviour of inserts and
  batches.  They are intentionally elementary: keys are added, old values are
  never increased, inserted values are respected, and an upper bound is
  preserved when every inserted value is below that bound.  These facts are used
  by the operational refresh step after a recursive child call has returned.
\<close>

lemma batch_min_update_preserves_upper_bound:
  assumes upper: "partition_upper_bound D B"
    and values_lt: "\<And>x b. (x, b) \<in> set xs \<Longrightarrow> b < B"
  shows "partition_upper_bound (batch_min_update D xs) B"
  using assms
proof (induction xs arbitrary: D)
  case Nil
  then show ?case
    unfolding batch_min_update_def by simp
next
  case (Cons xb xs)
  obtain x b where xb: "xb = (x, b)"
    by force
  have b_lt: "b < B"
    using Cons.prems(2)[of x b] xb by simp
  have upper_step: "partition_upper_bound (min_update D x b) B"
    using min_update_preserves_upper_bound[OF Cons.prems(1) b_lt] .
  have tail_lt: "\<And>y c. (y, c) \<in> set xs \<Longrightarrow> c < B"
  proof -
    fix y c
    assume "(y, c) \<in> set xs"
    then show "c < B"
      using Cons.prems(2)[of y c] by simp
  qed
  have ih: "partition_upper_bound (batch_min_update (min_update D x b) xs) B"
    by (rule Cons.IH[OF upper_step tail_lt])
  then show ?case
    unfolding batch_min_update_def xb by (simp add: case_prod_beta)
qed

lemma pull_separates_pulled_smallest:
  assumes "pull_separates D M B S x D'"
    and "u \<in> S"
    and "v \<in> keys_of D'"
  shows "value_of D u \<le> value_of D' v"
  using assms unfolding pull_separates_def by blast

lemma pull_separates_remaining_keys:
  assumes "pull_separates D M B S x D'"
  shows "keys_of D' = keys_of D - S"
  using assms unfolding pull_separates_def by blast

lemma pull_separates_card:
  assumes "pull_separates D M B S x D'"
  shows "card S \<le> M"
  using assms unfolding pull_separates_def by blast

lemma pull_separates_subset:
  assumes "pull_separates D M B S x D'"
  shows "S \<subseteq> keys_of D"
  using assms unfolding pull_separates_def by blast

lemma pull_separates_preserves_upper_bound:
  assumes pull: "pull_separates D M B0 S x D'"
    and upper: "partition_upper_bound D B"
  shows "partition_upper_bound D' B"
    using pull upper unfolding pull_separates_def partition_upper_bound_def by auto

text \<open>
  The pull lemmas unpack the abstract separator contract.  A successful pull
  gives a source set of size at most \<open>M\<close>, a residual key set with the pulled
  keys removed, and a bound that lies between the pulled prefix and the
  residual suffix.  The admissibility lemma for batch prepend is the property
  needed by the BMSSP loop: if every new batch value is below the separator,
  then the batch may be prepended in front of the residual partition.
\<close>

lemma pull_separates_empty_bound:
  assumes "pull_separates D M B S x D'"
    and "keys_of D' = {}"
  shows "x = B"
  using assms unfolding pull_separates_def by simp

lemma pull_separates_nonempty_bound:
  assumes "pull_separates D M B S x D'"
    and "keys_of D' \<noteq> {}"
    and "v \<in> keys_of D'"
  shows "x \<le> value_of D' v"
  using assms unfolding pull_separates_def by auto

lemma pull_separates_bound_le:
  assumes pull: "pull_separates D M B S x D'"
    and upper: "partition_upper_bound D B"
  shows "x \<le> B"
proof (cases "keys_of D' = {}")
  case True
  then show ?thesis
    using pull_separates_empty_bound[OF pull True] by simp
next
  case False
  then obtain v where v: "v \<in> keys_of D'"
    by blast
  have x_le_v: "x \<le> value_of D' v"
    by (rule pull_separates_nonempty_bound[OF pull False v])
  have v_old: "v \<in> keys_of D"
    using pull v unfolding pull_separates_def by auto
  have val_eq: "value_of D' = value_of D"
    using pull unfolding pull_separates_def by blast
  have "value_of D v < B"
    using upper v_old unfolding partition_upper_bound_def by blast
  then show ?thesis
    using x_le_v val_eq by auto
qed

lemma pull_separates_batch_prepend_admissible:
  assumes pull: "pull_separates D M B S x D'"
    and vals: "\<And>u b. (u, b) \<in> set xs \<Longrightarrow> b \<le> x"
  shows "batch_prepend_admissible D' xs"
proof (cases "keys_of D' = {}")
  case True
  then show ?thesis
    unfolding batch_prepend_admissible_def by simp
next
  case False
  show ?thesis
  proof (rule batch_prepend_admissible_below_all[OF vals])
    fix y
    assume "y \<in> keys_of D'"
    then show "x \<le> value_of D' y"
      by (rule pull_separates_nonempty_bound[OF pull False])
  qed
qed

theorem pull_separates_exact_split:
  assumes pull: "pull_separates D M B S x D'"
    and upper: "\<And>u. u \<in> keys_of D \<Longrightarrow> value_of D u < B"
  shows "S = {u \<in> keys_of D. value_of D u < x}"
proof -
  have S_subset: "S \<subseteq> keys_of D"
    using pull_separates_subset[OF pull] .
  have D'_keys: "keys_of D' = keys_of D - S"
    using pull unfolding pull_separates_def by blast
  show ?thesis
  proof (cases "keys_of D' = {}")
    case True
    have x_B: "x = B"
      using pull True by (rule pull_separates_empty_bound)
    have S_keys: "S = keys_of D"
      using S_subset D'_keys True by blast
    have "{u \<in> keys_of D. value_of D u < x} = keys_of D"
      using upper unfolding x_B by blast
    then show ?thesis
      using S_keys by simp
  next
    case False
    have S_to_split: "S \<subseteq> {u \<in> keys_of D. value_of D u < x}"
    proof
      fix u
      assume uS: "u \<in> S"
      then have "value_of D u < x"
        using pull False unfolding pull_separates_def by auto
      then show "u \<in> {u \<in> keys_of D. value_of D u < x}"
        using uS S_subset by blast
    qed
    have split_to_S: "{u \<in> keys_of D. value_of D u < x} \<subseteq> S"
    proof
      fix u
      assume u: "u \<in> {u \<in> keys_of D. value_of D u < x}"
      show "u \<in> S"
      proof (rule ccontr)
        assume "u \<notin> S"
        then have uD': "u \<in> keys_of D'"
          using u D'_keys by blast
        have "x \<le> value_of D' u"
          by (rule pull_separates_nonempty_bound[OF pull False uD'])
        moreover have "value_of D' u = value_of D u"
          using pull unfolding pull_separates_def by simp
        ultimately show False
          using u by simp
      qed
    qed
    show ?thesis
      using S_to_split split_to_S by blast
  qed
qed

text \<open>
  The final theorems connect the sorted reference operation to the abstract pull
  contract.  \<open>sorted_pull_separates\<close> proves that the reference operation
  really returns a separating prefix, and \<open>sorted_pull_exact_split\<close> proves
  that the same prefix is exactly the strict lower split at the returned bound
  whenever all labels are below the outer bound.

  These two facts are specification tools.  The executable bucketed partition
  does not sort all keys on every pull; instead, it proves the same separator
  and split properties for its bucket state and then plugs those properties into
  the generic BMSSP correctness and cost layers.
\<close>

theorem sorted_pull_separates:
  fixes M :: nat
    and B :: real
  assumes finite_keys: "finite (keys_of D)"
    and S_def: "S = sorted_pull_set M D"
    and x_def: "x = sorted_pull_bound M B D"
    and D'_def: "D' = remove_keys_view D S"
  shows "pull_separates D M B S x D'"
proof -
  let ?xs = "partition_key_order D"
  have set_xs: "set ?xs = keys_of D"
    using partition_key_order_properties(1)[OF finite_keys] .
  have distinct_xs: "distinct ?xs"
    using partition_key_order_properties(2)[OF finite_keys] .
  have sorted_xs: "sorted_wrt (\<lambda>u v. value_of D u \<le> value_of D v) ?xs"
    using partition_key_order_properties(3)[OF finite_keys] .
  show ?thesis
  proof (cases "length ?xs \<le> M")
    case True
    have S_all: "S = keys_of D"
      using True set_xs unfolding S_def sorted_pull_set_def by (simp add: Let_def)
    have D_empty: "keys_of D' = {}"
      unfolding D'_def remove_keys_view_def S_all by simp
    have "x = B"
      using True unfolding x_def sorted_pull_bound_def by (simp add: Let_def)
    moreover have "card S \<le> M"
    proof -
      have "card S = card (set ?xs)"
        using S_all set_xs by simp
      also have "\<dots> = length ?xs"
        using distinct_xs by (simp add: distinct_card)
      finally have "card S = length ?xs" .
      then show ?thesis
        using True by simp
    qed
    ultimately show ?thesis
      unfolding pull_separates_def D'_def remove_keys_view_def
      using S_all D_empty by auto
  next
    case False
    then have M_lt: "M < length ?xs"
      by simp
    let ?beta = "value_of D (?xs ! M)"
    have x_beta: "x = ?beta"
      using False unfolding x_def sorted_pull_bound_def by (simp add: Let_def)
    have S_lt: "S = {u \<in> keys_of D. value_of D u < ?beta}"
      using False unfolding S_def sorted_pull_set_def by (simp add: Let_def)
    have S_subset: "S \<subseteq> keys_of D"
      unfolding S_lt by blast
    have S_take: "S \<subseteq> set (take M ?xs)"
    proof
      fix u
      assume uS: "u \<in> S"
      then have u_keys: "u \<in> keys_of D" and lt: "value_of D u < ?beta"
        unfolding S_lt by auto
      then have "u \<in> set ?xs"
        using set_xs by simp
      then show "u \<in> set (take M ?xs)"
        using sorted_value_less_nth_in_take[OF sorted_xs _ lt M_lt] by blast
    qed
    have card_S: "card S \<le> M"
    proof -
      have "card S \<le> card (set (take M ?xs))"
        using S_take by (intro card_mono) simp_all
      also have "\<dots> \<le> length (take M ?xs)"
        by (rule card_length)
      also have "\<dots> = M"
        using M_lt by simp
      finally show ?thesis .
    qed
    have D'_keys: "keys_of D' = keys_of D - S"
      unfolding D'_def remove_keys_view_def by simp
    have D'_value: "value_of D' = value_of D"
      unfolding D'_def remove_keys_view_def by simp
    have remaining_nonempty: "keys_of D' \<noteq> {}"
    proof -
      have nth_in: "?xs ! M \<in> keys_of D"
        using set_xs M_lt nth_mem by metis
      have "?xs ! M \<notin> S"
        unfolding S_lt by simp
      then have "?xs ! M \<in> keys_of D - S"
        using nth_in by blast
      then show ?thesis
        using D'_keys by blast
    qed
    have pulled_before_remaining:
      "\<And>u v. \<lbrakk>u \<in> S; v \<in> keys_of D'\<rbrakk> \<Longrightarrow> value_of D u \<le> value_of D' v"
    proof -
      fix u v
      assume uS: "u \<in> S" and vD: "v \<in> keys_of D'"
      have "value_of D u < ?beta"
        using uS unfolding S_lt by blast
      moreover have "\<not> value_of D v < ?beta"
        using vD D'_keys unfolding S_lt by blast
      ultimately have "value_of D u \<le> value_of D v"
        by simp
      then show "value_of D u \<le> value_of D' v"
        using D'_value by simp
    qed
    have lower_remaining:
      "\<And>v. v \<in> keys_of D' \<Longrightarrow> x \<le> value_of D' v"
    proof -
      fix v
      assume vD: "v \<in> keys_of D'"
      have "\<not> value_of D v < ?beta"
        using vD D'_keys unfolding S_lt by blast
      then show "x \<le> value_of D' v"
        using x_beta D'_value by simp
    qed
    have upper_pulled:
      "\<And>u. u \<in> S \<Longrightarrow> value_of D u < x"
      using x_beta unfolding S_lt by blast
    show ?thesis
      unfolding pull_separates_def
      using S_subset card_S D'_keys D'_value remaining_nonempty
        pulled_before_remaining lower_remaining upper_pulled
      by auto
  qed
qed

theorem sorted_pull_exact_split:
  assumes finite_keys: "finite (keys_of D)"
    and upper: "\<And>u. u \<in> keys_of D \<Longrightarrow> value_of D u < B"
  shows "sorted_pull_set M D =
    {u \<in> keys_of D. value_of D u < sorted_pull_bound M B D}"
proof -
  let ?xs = "partition_key_order D"
  have set_xs: "set ?xs = keys_of D"
    using partition_key_order_properties(1)[OF finite_keys] .
  show ?thesis
  proof (cases "length ?xs \<le> M")
    case True
    then have "sorted_pull_set M D = keys_of D"
      using set_xs unfolding sorted_pull_set_def by (simp add: Let_def)
    moreover have "sorted_pull_bound M B D = B"
      using True unfolding sorted_pull_bound_def by (simp add: Let_def)
    ultimately show ?thesis
    proof -
      have "{u \<in> keys_of D. value_of D u < sorted_pull_bound M B D} = keys_of D"
      proof
        show "{u \<in> keys_of D. value_of D u < sorted_pull_bound M B D} \<subseteq> keys_of D"
          by blast
      next
        show "keys_of D \<subseteq> {u \<in> keys_of D. value_of D u < sorted_pull_bound M B D}"
        proof
          fix u
          assume u: "u \<in> keys_of D"
          then have "value_of D u < B"
            by (rule upper)
          then show "u \<in> {u \<in> keys_of D. value_of D u < sorted_pull_bound M B D}"
            using u \<open>sorted_pull_bound M B D = B\<close> by simp
        qed
      qed
      then show ?thesis
        using \<open>sorted_pull_set M D = keys_of D\<close> by simp
    qed
  next
    case False
    then show ?thesis
      unfolding sorted_pull_set_def sorted_pull_bound_def by (simp add: Let_def)
  qed
qed

end
