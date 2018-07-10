section \<open>General Utilities\<close>

theory General
  imports Polynomials.Utils
begin

text \<open>A couple of general-purpose functions and lemmas, mainly related to lists.\<close>

subsection \<open>Lists\<close>

lemma distinct_reorder: "distinct (xs @ (y # ys)) = distinct (y # (xs @ ys))" by auto
    
lemma set_reorder: "set (xs @ (y # ys)) = set (y # (xs @ ys))" by simp

lemma distinctI:
  assumes "\<And>i j. i < j \<Longrightarrow> i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> xs ! i \<noteq> xs ! j"
  shows "distinct xs"
  using assms
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (simp, intro conjI, rule)
    assume "x \<in> set xs"
    then obtain j where "j < length xs" and "x = xs ! j" by (metis in_set_conv_nth)
    hence "Suc j < length (x # xs)" by simp
    have "(x # xs) ! 0 \<noteq> (x # xs) ! (Suc j)" by (rule Cons(2), simp, simp, fact)
    thus False by (simp add: \<open>x = xs ! j\<close>)
  next
    show "distinct xs"
    proof (rule Cons(1))
      fix i j
      assume "i < j" and "i < length xs" and "j < length xs"
      hence "Suc i < Suc j" and "Suc i < length (x # xs)" and "Suc j < length (x # xs)" by simp_all
      hence "(x # xs) ! (Suc i) \<noteq> (x # xs) ! (Suc j)" by (rule Cons(2))
      thus "xs ! i \<noteq> xs ! j" by simp
    qed
  qed
qed

lemma filter_nth_pairE:
  assumes "i < j" and "i < length (filter P xs)" and "j < length (filter P xs)"
  obtains i' j' where "i' < j'" and "i' < length xs" and "j' < length xs"
    and "(filter P xs) ! i = xs ! i'" and "(filter P xs) ! j = xs ! j'"
  using assms
proof (induct xs arbitrary: i j thesis)
  case Nil
  from Nil(3) show ?case by simp
next
  case (Cons x xs)
  let ?ys = "filter P (x # xs)"
  show ?case
  proof (cases "P x")
    case True
    hence *: "?ys = x # (filter P xs)" by simp
    from \<open>i < j\<close> obtain j0 where j: "j = Suc j0" using lessE by blast
    have len_ys: "length ?ys = Suc (length (filter P xs))" and ys_j: "?ys ! j = (filter P xs) ! j0"
      by (simp only: * length_Cons, simp only: j * nth_Cons_Suc)
    from Cons(5) have "j0 < length (filter P xs)" unfolding len_ys j by auto
    show ?thesis
    proof (cases "i = 0")
      case True
      from \<open>j0 < length (filter P xs)\<close> obtain j' where "j' < length xs" and **: "(filter P xs) ! j0 = xs ! j'"
        by (metis (no_types, lifting) in_set_conv_nth mem_Collect_eq nth_mem set_filter)
      have "0 < Suc j'" by simp
      thus ?thesis
        by (rule Cons(2), simp, simp add: \<open>j' < length xs\<close>, simp only: True * nth_Cons_0,
            simp only: ys_j nth_Cons_Suc **)
    next
      case False
      then obtain i0 where i: "i = Suc i0" using lessE by blast
      have ys_i: "?ys ! i = (filter P xs) ! i0" by (simp only: i * nth_Cons_Suc)
      from Cons(3) have "i0 < j0" by (simp add: i j)
      from Cons(4) have "i0 < length (filter P xs)" unfolding len_ys i by auto
      from _ \<open>i0 < j0\<close> this \<open>j0 < length (filter P xs)\<close> obtain i' j'
        where "i' < j'" and "i' < length xs" and "j' < length xs"
          and i': "filter P xs ! i0 = xs ! i'" and j': "filter P xs ! j0 = xs ! j'"
        by (rule Cons(1))
      from \<open>i' < j'\<close> have "Suc i' < Suc j'" by simp
      thus ?thesis
        by (rule Cons(2), simp add: \<open>i' < length xs\<close>, simp add: \<open>j' < length xs\<close>,
            simp only: ys_i nth_Cons_Suc i', simp only: ys_j nth_Cons_Suc j')
    qed
  next
    case False
    hence *: "?ys = filter P xs" by simp
    with Cons(4) Cons(5) have "i < length (filter P xs)" and "j < length (filter P xs)" by simp_all
    with _ \<open>i < j\<close> obtain i' j' where "i' < j'" and "i' < length xs" and "j' < length xs"
      and i': "filter P xs ! i = xs ! i'" and j': "filter P xs ! j = xs ! j'"
      by (rule Cons(1))
    from \<open>i' < j'\<close> have "Suc i' < Suc j'" by simp
    thus ?thesis
      by (rule Cons(2), simp add: \<open>i' < length xs\<close>, simp add: \<open>j' < length xs\<close>,
          simp only: * nth_Cons_Suc i', simp only: * nth_Cons_Suc j')
  qed
qed

lemma distinct_filterI:
  assumes "\<And>i j. i < j \<Longrightarrow> i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> P (xs ! i) \<Longrightarrow> P (xs ! j) \<Longrightarrow> xs ! i \<noteq> xs ! j"
  shows "distinct (filter P xs)"
proof (rule distinctI)
  fix i j::nat
  assume "i < j" and "i < length (filter P xs)" and "j < length (filter P xs)"
  then obtain i' j' where "i' < j'" and "i' < length xs" and "j' < length xs"
    and i: "(filter P xs) ! i = xs ! i'" and j: "(filter P xs) ! j = xs ! j'" by (rule filter_nth_pairE)
  from \<open>i' < j'\<close> \<open>i' < length xs\<close> \<open>j' < length xs\<close> show "(filter P xs) ! i \<noteq> (filter P xs) ! j" unfolding i j
  proof (rule assms)
    from \<open>i < length (filter P xs)\<close> show "P (xs ! i')" unfolding i[symmetric] using nth_mem by force
  next
    from \<open>j < length (filter P xs)\<close> show "P (xs ! j')" unfolding j[symmetric] using nth_mem by force
  qed
qed

lemma set_zip_map: "set (zip (map f xs) (map g xs)) = (\<lambda>x. (f x, g x)) ` (set xs)"
proof -
  have "{(map f xs ! i, map g xs ! i) |i. i < length xs} = {(f (xs ! i), g (xs ! i)) |i. i < length xs}"
  proof (rule Collect_eqI, rule, elim exE conjE, intro exI conjI, simp add: map_nth, assumption,
      elim exE conjE, intro exI)
    fix x i
    assume "x = (f (xs ! i), g (xs ! i))" and "i < length xs"
    thus "x = (map f xs ! i, map g xs ! i) \<and> i < length xs" by (simp add: map_nth)
  qed
  also have "... = (\<lambda>x. (f x, g x)) ` {xs ! i | i. i < length xs}" by blast
  finally show "set (zip (map f xs) (map g xs)) = (\<lambda>x. (f x, g x)) ` (set xs)"
    by (simp add: set_zip set_conv_nth[symmetric])
qed

lemma set_zip_map1: "set (zip (map f xs) xs) = (\<lambda>x. (f x, x)) ` (set xs)"
proof -
  have "set (zip (map f xs) (map id xs)) = (\<lambda>x. (f x, id x)) ` (set xs)" by (rule set_zip_map)
  thus ?thesis by simp
qed

lemma set_zip_map2: "set (zip xs (map f xs)) = (\<lambda>x. (x, f x)) ` (set xs)"
proof -
  have "set (zip (map id xs) (map f xs)) = (\<lambda>x. (id x, f x)) ` (set xs)" by (rule set_zip_map)
  thus ?thesis by simp
qed

lemma UN_upt: "(\<Union>i\<in>{0..<length xs}. f (xs ! i)) = (\<Union>x\<in>set xs. f x)"
  by (metis image_image map_nth set_map set_upt)

lemma sum_list_zeroI':
  assumes "\<And>i. i < length xs \<Longrightarrow> xs ! i = 0"
  shows "sum_list xs = 0"
proof (rule sum_list_zeroI, rule, simp)
  fix x
  assume "x \<in> set xs"
  then obtain i where "i < length xs" and "x = xs ! i" by (metis in_set_conv_nth)
  from this(1) show "x = 0" unfolding \<open>x = xs ! i\<close> by (rule assms)
qed

lemma sum_list_map2_plus:
  assumes "length xs = length ys"
  shows "sum_list (map2 (+) xs ys) = sum_list xs + sum_list (ys::'a::comm_monoid_add list)"
  using assms
proof (induct rule: list_induct2)
  case Nil
  show ?case by simp
next
  case (Cons x xs y ys)
  show ?case by (simp add: Cons(2) ac_simps)
qed

lemma sum_list_eq_nthI:
  assumes "i < length xs" and "\<And>j. j < length xs \<Longrightarrow> j \<noteq> i \<Longrightarrow> xs ! j = 0"
  shows "sum_list xs = xs ! i"
  using assms
proof (induct xs arbitrary: i)
  case Nil
  from Nil(1) show ?case by simp
next
  case (Cons x xs)
  have *: "xs ! j = 0" if "j < length xs" and "Suc j \<noteq> i" for j
  proof -
    have "xs ! j = (x # xs) ! (Suc j)" by simp
    also have "... = 0" by (rule Cons(3), simp add: \<open>j < length xs\<close>, fact)
    finally show ?thesis .
  qed
  show ?case
  proof (cases i)
    case 0
    have "sum_list xs = 0" by (rule sum_list_zeroI', erule *, simp add: 0)
    with 0 show ?thesis by simp
  next
    case (Suc k)
    with Cons(2) have "k < length xs" by simp
    hence "sum_list xs = xs ! k"
    proof (rule Cons(1))
      fix j
      assume "j < length xs"
      assume "j \<noteq> k"
      hence "Suc j \<noteq> i" by (simp add: Suc)
      with \<open>j < length xs\<close> show "xs ! j = 0" by (rule *)
    qed
    moreover have "x = 0"
    proof -
      have "x = (x # xs) ! 0" by simp
      also have "... = 0" by (rule Cons(3), simp_all add: Suc)
      finally show ?thesis .
    qed
    ultimately show ?thesis by (simp add: Suc)
  qed
qed

subsubsection \<open>\<open>max_list\<close>\<close>

fun (in ord) max_list :: "'a list \<Rightarrow> 'a" where
  "max_list (x # xs) = (case xs of [] \<Rightarrow> x | _ \<Rightarrow> max x (max_list xs))"

lemma (in linorder) max_list_Max: "xs \<noteq> [] \<Longrightarrow> max_list xs = Max (set xs)"
  by (induct xs rule: induct_list012, auto)

subsubsection \<open>\<open>insort_wrt\<close>\<close>

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

subsubsection \<open>\<open>diff_list\<close> and \<open>insert_list\<close>\<close>

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

subsubsection \<open>\<open>remdups_wrt\<close>\<close>

primrec remdups_wrt :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  remdups_wrt_base: "remdups_wrt _ [] = []" |
  remdups_wrt_rec: "remdups_wrt f (x # xs) = (if f x \<in> f ` set xs then remdups_wrt f xs else x # remdups_wrt f xs)"
    
lemma set_remdups_wrt: "f ` set (remdups_wrt f xs) = f ` set xs"
proof (induct xs)
  case Nil
  show ?case unfolding remdups_wrt_base ..
next
  case (Cons a xs)
  show ?case unfolding remdups_wrt_rec
  proof (simp only: split: if_splits, intro conjI, intro impI)
    assume "f a \<in> f ` set xs"
      have "f ` set (a # xs) = insert (f a) (f ` set xs)" by simp
    have "f ` set (remdups_wrt f xs) = f ` set xs" by fact
    also from \<open>f a \<in> f ` set xs\<close> have "... = insert (f a) (f ` set xs)" by (simp add: insert_absorb)
    also have "... = f ` set (a # xs)" by simp
    finally show "f ` set (remdups_wrt f xs) = f ` set (a # xs)" .
  qed (simp add: Cons.hyps)
qed

lemma subset_remdups_wrt: "set (remdups_wrt f xs) \<subseteq> set xs"
  by (induct xs, auto)

lemma remdups_wrt_distinct_wrt:
  assumes "x \<in> set (remdups_wrt f xs)" and "y \<in> set (remdups_wrt f xs)" and "x \<noteq> y"
  shows "f x \<noteq> f y"
  using assms(1) assms(2)
proof (induct xs)
  case Nil
  thus ?case unfolding remdups_wrt_base by simp
next
  case (Cons a xs)
  from Cons(2) Cons(3) show ?case unfolding remdups_wrt_rec
  proof (simp only: split: if_splits)
    assume "x \<in> set (remdups_wrt f xs)" and "y \<in> set (remdups_wrt f xs)"
    thus "f x \<noteq> f y" by (rule Cons.hyps)
  next
    assume "\<not> True"
    thus "f x \<noteq> f y" by simp
  next
    assume "f a \<notin> f ` set xs" and xin: "x \<in> set (a # remdups_wrt f xs)" and yin: "y \<in> set (a # remdups_wrt f xs)"
    from yin have y: "y = a \<or> y \<in> set (remdups_wrt f xs)" by simp
    from xin have "x = a \<or> x \<in> set (remdups_wrt f xs)" by simp
    thus "f x \<noteq> f y"
    proof
      assume "x = a"
      from y show ?thesis
      proof
        assume "y = a"
        with \<open>x \<noteq> y\<close> show ?thesis unfolding \<open>x = a\<close> by simp
      next
        assume "y \<in> set (remdups_wrt f xs)"
        have "y \<in> set xs" by (rule, fact, rule subset_remdups_wrt)
        hence "f y \<in> f ` set xs" by simp
        with \<open>f a \<notin> f ` set xs\<close> show ?thesis unfolding \<open>x = a\<close> by auto
      qed
    next
      assume "x \<in> set (remdups_wrt f xs)"
      from y show ?thesis
      proof
        assume "y = a"
        have "x \<in> set xs" by (rule, fact, rule subset_remdups_wrt)
        hence "f x \<in> f ` set xs" by simp
        with \<open>f a \<notin> f ` set xs\<close> show ?thesis unfolding \<open>y = a\<close> by auto
      next
        assume "y \<in> set (remdups_wrt f xs)"
        with \<open>x \<in> set (remdups_wrt f xs)\<close> show ?thesis by (rule Cons.hyps)
      qed
    qed
  qed
qed
  
lemma distinct_remdups_wrt: "distinct (remdups_wrt f xs)"
proof (induct xs)
  case Nil
  show ?case unfolding remdups_wrt_base by simp
next
  case (Cons a xs)
  show ?case unfolding remdups_wrt_rec
  proof (split if_split, intro conjI impI, rule Cons.hyps)
    assume "f a \<notin> f ` set xs"
    hence "a \<notin> set xs" by auto
    hence "a \<notin> set (remdups_wrt f xs)" using subset_remdups_wrt[of f xs] by auto
    with Cons.hyps show "distinct (a # remdups_wrt f xs)" by simp
  qed
qed

lemma map_remdups_wrt: "map f (remdups_wrt f xs) = remdups (map f xs)"
  by (induct xs, auto)

lemma remdups_wrt_append:
  "remdups_wrt f (xs @ ys) = (filter (\<lambda>a. f a \<notin> f ` set ys) (remdups_wrt f xs)) @ (remdups_wrt f ys)"
  by (induct xs, auto)

subsubsection \<open>\<open>map_idx\<close>\<close>

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

subsubsection \<open>\<open>map_dup\<close>\<close>

primrec map_dup :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map_dup _ _ [] = []"|
  "map_dup f g (x # xs) = (if x \<in> set xs then g x else f x) # (map_dup f g xs)"

lemma length_map_dup[simp]: "length (map_dup f g xs) = length xs"
  by (induct xs, simp_all)

lemma map_dup_distinct:
  assumes "distinct xs"
  shows "map_dup f g xs = map f xs"
  using assms by (induct xs, simp_all)

lemma filter_map_dup_const:
  "filter (\<lambda>x. x \<noteq> c) (map_dup f (\<lambda>_. c) xs) = filter (\<lambda>x. x \<noteq> c) (map f (remdups xs))"
  by (induct xs, simp_all)

lemma filter_zip_map_dup_const:
  "filter (\<lambda>(a, b). a \<noteq> c) (zip (map_dup f (\<lambda>_. c) xs) xs) =
    filter (\<lambda>(a, b). a \<noteq> c) (zip (map f (remdups xs)) (remdups xs))"
  by (induct xs, simp_all)

end (* theory *)
