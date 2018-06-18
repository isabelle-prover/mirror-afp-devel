section \<open>General Utilities\<close>

theory General
  imports Main
begin

text \<open>A couple of general-purpose functions and lemmas, mainly related to lists.\<close>

subsection \<open>Lists\<close>

primrec insort_wrt :: "('c \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> 'c list \<Rightarrow> 'c list" where
  "insort_wrt _ x [] = [x]" |
  "insort_wrt r x (y # ys) =
    (if r x y then (x # y # ys) else y # (insort_wrt r x ys))"

lemma insort_wrt_not_Nil [simp]: "insort_wrt r x xs \<noteq> []"
  by (induct xs, simp_all)

lemma length_insort_wrt [simp]: "length (insort_wrt r x xs) = Suc (length xs)"
  by (induct xs, simp_all)

lemma set_insort_wrt [simp]: "set (insort_wrt r x xs) = insert x (set xs)"
  by (induct xs, auto)

lemma sorted_wrt_insort_wrt_imp_sorted_wrt:
  assumes "sorted_wrt r (insort_wrt s x xs)"
  shows "sorted_wrt r xs"
  using assms
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases "s x a")
    case True
    with Cons.prems have "sorted_wrt r (x # a # xs)" by simp
    thus ?thesis by simp
  next
    case False
    with Cons(2) have "sorted_wrt r (a # (insort_wrt s x xs))" by simp
    hence *: "(\<forall>y\<in>set xs. r a y)" and "sorted_wrt r (insort_wrt s x xs)"
      by (simp_all)
    from this(2) have "sorted_wrt r xs" by (rule Cons(1))
    with * show ?thesis by (simp)
  qed
qed

lemma sorted_wrt_imp_sorted_wrt_insort_wrt:
  assumes "transp r" and "\<And>a. r a x \<or> r x a" and "sorted_wrt r xs"
  shows "sorted_wrt r (insort_wrt r x xs)"
  using assms(3)
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases "r x a")
    case True
    with Cons(2) assms(1) show ?thesis by (auto dest: transpD)
  next
    case False
    with assms(2) have "r a x" by blast
    from Cons(2) have *: "(\<forall>y\<in>set xs. r a y)" and "sorted_wrt r xs"
      by (simp_all)
    from this(2) have "sorted_wrt r (insort_wrt r x xs)" by (rule Cons(1))
    with \<open>r a x\<close> * show ?thesis by (simp add: False)
  qed
qed

corollary sorted_wrt_insort_wrt:
  assumes "transp r" and "\<And>a. r a x \<or> r x a"
  shows "sorted_wrt r (insort_wrt r x xs) \<longleftrightarrow> sorted_wrt r xs" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then show ?r by (rule sorted_wrt_insort_wrt_imp_sorted_wrt)
next
  assume ?r
  with assms show ?l by (rule sorted_wrt_imp_sorted_wrt_insort_wrt)
qed

definition diff_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "--" 65)
  where "diff_list xs ys = fold removeAll ys xs"

lemma set_diff_list: "set (xs -- ys) = set xs - set ys"
  by (simp only: diff_list_def, induct ys arbitrary: xs, auto)

lemma diff_list_disjoint: "set ys \<inter> set (xs -- ys) = {}"
  unfolding set_diff_list by (rule Diff_disjoint)

lemma subset_append_diff_cancel:
  assumes "set ys \<subseteq> set xs"
  shows "set (ys @ (xs -- ys)) = set xs"
  by (simp only: set_append set_diff_list Un_Diff_cancel, rule Un_absorb1, fact)

definition insert_list :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "insert_list x xs = (if x \<in> set xs then xs else x # xs)"

lemma set_insert_list: "set (insert_list x xs) = insert x (set xs)"
  by (auto simp add: insert_list_def)

subsection \<open>@{term map_idx}\<close>

primrec map_idx :: "('a \<Rightarrow> nat \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'b list" where
  "map_idx f [] n = []"|
  "map_idx f (x # xs) n = (f x n) # (map_idx f xs (Suc n))"

lemma map_idx_eq_map2: "map_idx f xs n = map2 f xs [n..<n + length xs]"
proof (induct xs arbitrary: n)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  have eq: "[n..<n + length (x # xs)] = n # [Suc n..<Suc (n + length xs)]"
    by (metis add_Suc_right length_Cons less_add_Suc1 upt_conv_Cons)
  show ?case unfolding eq by (simp add: Cons del: upt_Suc)
qed

lemma length_map_idx [simp]: "length (map_idx f xs n) = length xs"
  by (simp add: map_idx_eq_map2)

lemma map_idx_append: "map_idx f (xs @ ys) n = (map_idx f xs n) @ (map_idx f ys (n + length xs))"
  by (simp add: map_idx_eq_map2 ab_semigroup_add_class.add_ac(1) zip_append1)

lemma map_idx_nth:
  assumes "i < length xs"
  shows "(map_idx f xs n) ! i = f (xs ! i) (n + i)"
  using assms by (simp add: map_idx_eq_map2)

lemma map_map_idx: "map f (map_idx g xs n) = map_idx (\<lambda>x i. f (g x i)) xs n"
  by (auto simp add: map_idx_eq_map2)

lemma map_idx_map: "map_idx f (map g xs) n = map_idx (f \<circ> g) xs n"
  by (simp add: map_idx_eq_map2 map_zip_map)

lemma map_idx_no_idx: "map_idx (\<lambda>x _. f x) xs n = map f xs"
  by (induct xs arbitrary: n, simp_all)

lemma map_idx_no_elem: "map_idx (\<lambda>_. f) xs n = map f [n..<n + length xs]"
proof (induct xs arbitrary: n)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  have eq: "[n..<n + length (x # xs)] = n # [Suc n..<Suc (n + length xs)]"
    by (metis add_Suc_right length_Cons less_add_Suc1 upt_conv_Cons)
  show ?case unfolding eq by (simp add: Cons del: upt_Suc)
qed

lemma map_idx_eq_map: "map_idx f xs n = map (\<lambda>i. f (xs ! i) (i + n)) [0..<length xs]"
proof (induct xs arbitrary: n)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  have eq: "[0..<length (x # xs)] = 0 # [Suc 0..<Suc (length xs)]"
    by (metis length_Cons upt_conv_Cons zero_less_Suc)
  have "map (\<lambda>i. f ((x # xs) ! i) (i + n)) [Suc 0..<Suc (length xs)] =
        map ((\<lambda>i. f ((x # xs) ! i) (i + n)) \<circ> Suc) [0..<length xs]"
    by (metis map_Suc_upt map_map)
  also have "... = map (\<lambda>i. f (xs ! i) (Suc (i + n))) [0..<length xs]"
    by (rule map_cong, fact refl, simp)
  finally show ?case unfolding eq by (simp add: Cons del: upt_Suc)
qed

lemma set_map_idx: "set (map_idx f xs n) = (\<lambda>i. f (xs ! i) (i + n)) ` {0..<length xs}"
  by (simp add: map_idx_eq_map)

end (* theory *)
