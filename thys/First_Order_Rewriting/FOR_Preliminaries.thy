section\<open>Preliminaries\<close>
text\<open>This theory contains some auxiliary results previously located in Auxx.Util of IsaFoR.\<close>
theory FOR_Preliminaries
  imports
    Polynomial_Factorization.Missing_List 
begin

lemma in_set_idx: "a \<in> set as \<Longrightarrow> \<exists>i. i < length as \<and> a = as ! i"
  unfolding set_conv_nth by auto

lemma finite_card_eq_imp_bij_betw:
  assumes "finite A"
    and "card (f ` A) = card A"
  shows "bij_betw f A (f ` A)"
  using \<open>card (f ` A) = card A\<close>
  unfolding inj_on_iff_eq_card [OF \<open>finite A\<close>, symmetric]
  by (rule inj_on_imp_bij_betw)

text \<open>Every bijective function between two finite subsets of a set \<open>S\<close> can be turned
  into a compatible renaming (with finite domain) on \<open>S\<close>.\<close>
lemma bij_betw_extend:
  assumes *: "bij_betw f A B"
    and "A \<subseteq> S"
    and "B \<subseteq> S"
    and "finite A"
  shows "\<exists>g. finite {x. g x \<noteq> x} \<and>
    (\<forall>x\<in>UNIV - (A \<union> B). g x = x) \<and>
    (\<forall>x\<in>A. g x = f x) \<and>
    bij_betw g S S"
proof -
  have "finite B" using assms by (metis bij_betw_finite)
  have [simp]: "card A = card B" by (metis * bij_betw_same_card)
  have "card (A - B) = card (B - A)"
  proof -
    have "card (A - B) = card A - card (A \<inter> B)"
      by (metis \<open>finite A\<close> card_Diff_subset_Int finite_Int)
    moreover have "card (B - A) = card B - card (A \<inter> B)"
      by (metis \<open>finite A\<close> card_Diff_subset_Int finite_Int inf_commute)
    ultimately show ?thesis by simp
  qed
  then obtain g where **: "bij_betw g (B - A) (A - B)"
    by (metis \<open>finite A\<close> \<open>finite B\<close> bij_betw_iff_card finite_Diff)
  define h where "h = (\<lambda>x. if x \<in> A then f x else if x \<in> B - A then g x else x)"
  have "bij_betw h A B"
    by (metis (full_types) * bij_betw_cong h_def)
  moreover have "bij_betw h (S - (A \<union> B)) (S - (A \<union> B))"
    by (auto simp: bij_betw_def h_def inj_on_def)
  moreover have "B \<inter> (S - (A \<union> B)) = {}" by blast
  ultimately have "bij_betw h (A \<union> (S - (A \<union> B))) (B \<union> (S - (A \<union> B)))"
    by (rule bij_betw_combine)
  moreover have "A \<union> (S - (A \<union> B)) = S - (B - A)"
    and "B \<union> (S - (A \<union> B)) = S - (A - B)"
    using \<open>A \<subseteq> S\<close> and \<open>B \<subseteq> S\<close> by blast+
  ultimately have "bij_betw h (S - (B - A)) (S - (A - B))" by simp
  moreover have "bij_betw h (B - A) (A - B)"
    using ** by (auto simp: bij_betw_def h_def inj_on_def)
  moreover have "(S - (A - B)) \<inter> (A - B) = {}" by blast
  ultimately have "bij_betw h ((S - (B - A)) \<union> (B - A)) ((S - (A - B)) \<union> (A - B))"
    by (rule bij_betw_combine)
  moreover have "(S - (B - A)) \<union> (B - A) = S"
    and "(S - (A - B)) \<union> (A - B) = S"
    using \<open>A \<subseteq> S\<close> and \<open>B \<subseteq> S\<close> by auto
  ultimately have "bij_betw h S S" by simp
  moreover have "\<forall>x\<in>A. h x = f x" by (auto simp: h_def)
  moreover have "finite {x. h x \<noteq> x}"
  proof -
    have "finite (A \<union> (B - A))" using \<open>finite A\<close> and \<open>finite B\<close> by auto
    moreover have "{x. h x \<noteq> x} \<subseteq> (A \<union> (B - A))" by (auto simp: h_def)
    ultimately show ?thesis by (metis finite_subset)
  qed
  moreover have "\<forall>x\<in>UNIV - (A \<union> B). h x = x" by (simp add: h_def)
  ultimately show ?thesis by blast
qed

lemma concat_nth:
  assumes "m < length xs" and "n < length (xs ! m)"
    and "i = sum_list (map length (take m xs)) + n"
  shows "concat xs ! i = xs ! m ! n" 
  using assms
proof (induct xs arbitrary: m n i)
  case (Cons x xs)
  show ?case
  proof (cases m)
    case 0
    then show ?thesis using Cons by (simp add: nth_append)
  next
    case (Suc k)
    with Cons(1) [of k n "i - length x"] and Cons(2-)
    show ?thesis by (simp_all add: nth_append)
  qed
qed simp

lemma concat_nth_length:
  "i < length uss \<Longrightarrow> j < length (uss ! i) \<Longrightarrow>
    sum_list (map length (take i uss)) + j < length (concat uss)"
proof (induct uss arbitrary: i j)
  case (Cons u uss i j)
  thus ?case by (cases i, auto)
qed auto

lemma less_length_concat:
  assumes "i < length (concat xs)"
  shows "\<exists>m n.
    i = sum_list (map length (take m xs)) + n \<and>
    m < length xs \<and> n < length (xs ! m) \<and> concat xs ! i = xs ! m ! n"
  using assms
proof (induct xs arbitrary: i rule: length_induct)
  case (1 xs)
  then show ?case
  proof (cases xs)
    case (Cons y ys)
    note [simp] = this
    { assume *: "i < length y"
      with 1 obtain n where "i = n" and "n < length y"
        and "y ! i = y ! n" by simp
      then have "i = sum_list (map length (take 0 xs)) + n"
        and "0 < length xs" and "n < length (xs ! 0)"
        and "concat xs ! i = xs ! 0 ! n"
        using * by (auto simp: nth_append)
      then have ?thesis by blast }
    moreover
    { assume *: "i \<ge> length y"
      define j where "j = i - length y"
      then have "length ys < length xs" "j < length (concat ys)"
        using * and "1.prems" by auto
      with 1 obtain m n where "j = sum_list (map length (take m ys)) + n"
        and "m < length ys" and "n < length (ys ! m)"
        and "concat ys ! j = ys ! m ! n" by blast
      then have "i = sum_list (map length (take (Suc m) xs)) + n"
        and "Suc m < length xs" and "n < length (xs ! Suc m)"
        and "concat xs ! i = xs ! Suc m ! n"
        using * by (simp_all add: j_def nth_append)
      then have ?thesis by blast }
    ultimately show ?thesis by force
  qed simp
qed

lemma concat_remove_nth:
  assumes "i < length sss"
    and "j < length (sss ! i)"
  defines "k \<equiv> sum_list (map length (take i sss)) + j"
  shows "concat (take i sss @ remove_nth j (sss ! i) # drop (Suc i) sss) = remove_nth k (concat sss)"
  using assms
  unfolding remove_nth_def
proof (induct sss rule: List.rev_induct)
  case Nil then show ?case by auto
next
  case (snoc ss sss)
  then have "i = length sss \<or> i < length sss" by auto 
  then show ?case
  proof
    assume i:"i = length sss"
    have "sum_list (map length sss) = length (concat sss)" by (simp add: length_concat)
    with snoc i show ?thesis by simp
  next
    assume i:"i < length sss"
    then have nth:"(sss @ [ss]) ! i = sss ! i" by (simp add: nth_append)
    from i have drop:"drop (Suc i) (sss @ [ss]) = drop (Suc i) sss @ [ss]" by auto
    from i have take:"take i (sss @ [ss]) = take i sss" by auto
    from snoc(1)[OF i] snoc(2-) have 1:"concat (take i (sss @ [ss]) @ 
      (take j ((sss @ [ss]) ! i) @ drop (Suc j) ((sss @ [ss]) ! i)) # drop (Suc i) (sss @ [ss])) = 
      take k (concat sss) @ drop (Suc k) (concat sss) @ ss" unfolding take nth drop by simp
    from snoc(4) take have k:"k = sum_list (map length (take i sss)) + j" by auto
    from nth snoc(3) have j: "j < length (sss ! i)" by auto
    have takek:"take (sum_list (map length (take i sss)) + j) (concat (sss @ [ss])) = 
      take (sum_list (map length (take i sss)) + j) (concat sss)"
      using concat_nth_length[OF i j] by auto
    have dropk:"drop (Suc (sum_list (map length (take i sss)) + j)) (concat sss) @ ss = 
      drop (Suc (sum_list (map length (take i sss)) + j)) (concat (sss @ [ss]))"
      using concat_nth_length[OF i j] by auto
    have "take k (concat sss) @ drop (Suc k) (concat sss) @ ss = 
      take k (concat (sss @ [ss])) @ drop (Suc k) (concat (sss @ [ss]))"
      unfolding k takek dropk ..
    with 1 show ?thesis by auto
  qed
qed

lemma nth_append_Cons: "(xs @ y # zs) ! i =
  (if i < length xs then xs ! i else if i = length xs then y else zs ! (i - Suc (length xs)))"
  by (cases i "length xs" rule: linorder_cases, auto simp: nth_append)

lemma finite_imp_eq [simp]:
  "finite {x. P x \<longrightarrow> Q x} \<longleftrightarrow> finite {x. \<not> P x} \<and> finite {x. Q x}"
  by (auto simp: Collect_imp_eq Collect_neg_eq)

lemma sum_list_take_eq:
  fixes xs :: "nat list"
  shows "k < i \<Longrightarrow> i < length xs \<Longrightarrow> sum_list (take i xs) =
    sum_list (take k xs) + xs ! k + sum_list (take (i - Suc k) (drop (Suc k) xs))"
  by (subst id_take_nth_drop [of k]) (auto simp: min_def drop_take)

lemma nth_equalityE:
  "xs = ys \<Longrightarrow> (length xs = length ys \<Longrightarrow> (\<And>i. i < length xs \<Longrightarrow> xs ! i = ys ! i) \<Longrightarrow> P) \<Longrightarrow> P"
  by simp

fun fold_map :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<times> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'c list \<times> 'b" where
  "fold_map f [] y = ([], y)" 
| "fold_map f (x#xs) y = (case f x y of
      (x', y') \<Rightarrow> case fold_map f xs y' of
      (xs', y'') \<Rightarrow> (x' # xs', y''))"

lemma fold_map_cong [fundef_cong]:
  assumes "a = b" and "xs = ys"
    and "\<And>x. x \<in> set xs \<Longrightarrow> f x = g x"
  shows "fold_map f xs a = fold_map g ys b"
  using assms by (induct ys arbitrary: a b xs) simp_all

lemma fold_map_map_conv:
  assumes "\<And>x ys. x \<in> set xs \<Longrightarrow> f (g x) (g' x @ ys) = (h x, ys)"
  shows "fold_map f (map g xs) (concat (map g' xs) @ ys) = (map h xs, ys)"
  using assms by (induct xs) simp_all

lemma map_fst_fold_map:
  "map f (fst (fold_map g xs y)) = fst (fold_map (\<lambda>a b. apfst f (g a b)) xs y)"
  by (induct xs arbitrary: y) (auto split: prod.splits, metis fst_conv)

lemma not_Nil_imp_last: "xs \<noteq> [] \<Longrightarrow> \<exists>ys y. xs = ys@[y]"
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons x xs) show ?case
  proof (cases xs)
    assume "xs = []" with Cons show ?thesis by simp
  next
    fix x' xs' assume "xs = x'#xs'"
    then have "xs \<noteq> []" by simp
    with Cons obtain ys y where "xs = ys@[y]" by auto
    then have "x#xs = x#(ys@[y])" by simp
    then have "x#xs = (x#ys)@[y]" by simp
    then show ?thesis by auto
  qed
qed

lemma Nil_or_last: "xs = [] \<or> (\<exists>ys y. xs = ys@[y])"
  using not_Nil_imp_last by blast

subsection \<open>Combinators\<close>

definition const :: "'a \<Rightarrow> 'b \<Rightarrow> 'a" where
  "const \<equiv> (\<lambda>x y. x)"

definition flip :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c)" where
  "flip f \<equiv> (\<lambda>x y. f y x)"
declare flip_def[simp]

lemma const_apply[simp]: "const x y = x"
  by (simp add: const_def)

lemma foldr_Cons_append_conv [simp]:
  "foldr (#) xs ys = xs @ ys"
  by (induct xs) simp_all

lemma foldl_flip_Cons[simp]:
  "foldl (flip (#)) xs ys = rev ys @ xs"
  by (induct ys arbitrary: xs) simp_all

text \<open>already present as @{thm [source] foldr_conv_foldl}, but
  direction seems odd\<close>
lemma foldr_flip_rev[simp]:
  "foldr (flip f) (rev xs) a = foldl f a xs"
  by (simp add: foldr_conv_foldl)

text \<open>already present as @{thm [source] foldl_conv_foldr}, but
  direction seems odd\<close>
lemma foldl_flip_rev[simp]:
  "foldl (flip f) a (rev xs) = foldr f xs a"
  by (simp add: foldl_conv_foldr)

fun debug :: "(String.literal \<Rightarrow> String.literal) \<Rightarrow> String.literal \<Rightarrow> 'a \<Rightarrow> 'a" where "debug i t x = x"

subsection \<open>Distinct Lists and Partitions\<close>

text \<open>This theory provides some auxiliary lemmas related to lists with distinct elements and
partitions. This is mainly used for dealing with \emph{linear} terms.\<close>

lemma distinct_alt:
  assumes "\<forall> x. length (filter ((=) x) xs) \<le> 1"
  shows "distinct xs"
  using assms proof(induct xs)
  case (Cons x xs)
  then have IH:"distinct xs"
    by (metis dual_order.trans filter.simps(2) impossible_Cons nle_le) 
  from Cons(2) have "length (filter ((=) x) xs) = 0"
    by (metis (mono_tags) One_nat_def add.right_neutral add_Suc_right filter.simps(2) le_less length_0_conv less_Suc0 list.simps(3) list.size(4) nat.inject)
  then have "x \<notin> set (xs)"
    by (metis (full_types) filter_empty_conv length_0_conv) 
  with IH show ?case
    by simp
qed simp

lemma distinct_filter2:
  assumes "\<forall>i < size xs. \<forall> j < size xs. i \<noteq> j \<and> f (xs!i) \<and> f (xs!j) \<longrightarrow> xs!i \<noteq> xs!j" 
  shows "distinct (filter f xs)"
  using assms proof(induct xs)
  case (Cons x xs)
  {fix i j assume "i < length xs" "j < length xs" "i \<noteq> j" "f (xs!i)" "f (xs!j)" 
    with Cons(2) have "xs!i \<noteq> xs!j"  
      by (metis not_less_eq nth_Cons_Suc Suc_inject length_Cons) 
  }
  with Cons(1) have IH:"distinct (filter f xs)"
    by presburger 
  show ?case proof(cases "f x")
    case True
    with Cons(2) have "\<forall>j<length xs. f (xs ! j) \<longrightarrow> x \<noteq> xs ! j" by fastforce 
    then have "x \<notin> set (filter f xs)" by (metis filter_set in_set_conv_nth member_filter)
    then show ?thesis unfolding filter.simps using True IH by simp
  next
    case False
    then show ?thesis unfolding filter.simps using IH by presburger
  qed
qed simp

lemma distinct_is_partition:
  assumes "distinct xs"
  shows "is_partition (map (\<lambda>x. {x}) xs)"
  using assms proof(induct xs)
  case (Cons x xs)
  then show ?case unfolding list.map(2) is_partition_Cons by force
qed (simp add: is_partition_Nil)

lemma is_partition_append:
  assumes "is_partition xs" and "is_partition zs" 
    and "\<forall>i < length xs. xs!i \<inter> \<Union> (set zs) = {}"
  shows "is_partition (xs@zs)"
  by (smt (verit, del_insts) add_diff_inverse_nat assms(1) assms(2) assms(3) disjoint_iff is_partition_alt is_partition_alt_def length_append mem_simps(9) nat_add_left_cancel_less nth_append nth_mem)

lemma distinct_is_partitition_sets:
  assumes "distinct xs"
    and "xs = concat ys"
  shows "is_partition (map set ys)" 
  using assms proof(induct ys arbitrary:xs)
  case (Cons y ys)
  have "is_partition (map set ys)" proof-
    from Cons(2,3) have "distinct (concat ys)"
      unfolding concat.simps by simp
    with Cons(1) show ?thesis by simp 
  qed
  moreover from Cons(2,3) have "set y \<inter> \<Union> (set (map set ys)) = {}"
    using distinct_append[of y "concat ys"]by simp
  ultimately show ?case 
    unfolding is_partition_Cons list.map by simp
qed (simp add: is_partition_Nil)

end