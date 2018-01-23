section \<open>General Utilities\<close>

theory General
  imports Main
begin

text \<open>A couple of general-purpose functions and lemmas, mainly related to lists.\<close>

subsection \<open>Lists\<close>

lemma distinct_sorted_wrt_irrefl:
  assumes "irreflp rel" and "transp rel" and "sorted_wrt rel xs"
  shows "distinct xs"
  using assms(3)
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  from Cons(2) have "sorted_wrt rel xs" and *: "\<forall>y\<in>set xs. rel x y"
    by (simp_all add: sorted_wrt_Cons[OF assms(2)])
  from this(1) have "distinct xs" by (rule Cons(1))
  show ?case
  proof (simp add: \<open>distinct xs\<close>, rule)
    assume "x \<in> set xs"
    with * have "rel x x" ..
    with assms(1) show False by (simp add: irreflp_def)
  qed
qed

lemma distinct_sorted_wrt_imp_sorted_wrt_strict:
  assumes "distinct xs" and "sorted_wrt rel xs"
  shows "sorted_wrt (\<lambda>x y. rel x y \<and> \<not> x = y) xs"
  using assms
proof (induct xs)
  case Nil
  show ?case by simp
next
  case step: (Cons x xs)
  show ?case
  proof (cases "xs")
    case Nil
    thus ?thesis by simp
  next
    case (Cons y zs)
    from step(2) have "x \<noteq> y" and 1: "distinct (y # zs)" by (simp_all add: Cons)
    from step(3) have "rel x y" and 2: "sorted_wrt rel (y # zs)" by (simp_all add: Cons)
    from 1 2 have "sorted_wrt (\<lambda>x y. rel x y \<and> x \<noteq> y) (y # zs)" by (rule step(1)[simplified Cons])
    with \<open>x \<noteq> y\<close> \<open>rel x y\<close> show ?thesis by (simp add: Cons)
  qed
qed

lemma sorted_wrt_distinct_set_unique:
  assumes "transp rel" and "antisymp rel"
  assumes "sorted_wrt rel xs" "distinct xs" "sorted_wrt rel ys" "distinct ys" "set xs = set ys"
  shows "xs = ys"
proof -
  from assms have 1: "length xs = length ys" by (auto dest!: distinct_card)
  from assms(3, 4, 5, 6, 7) show ?thesis
  proof(induct rule:list_induct2[OF 1])
    case 1
    show ?case by simp
  next
    case (2 x xs y ys)
    from 2(4) have "x \<notin> set xs" and "distinct xs" by simp_all
    from 2(6) have "y \<notin> set ys" and "distinct ys" by simp_all
    have "x = y"
    proof (rule ccontr)
      assume "x \<noteq> y"
      from 2(3) have "\<forall>z\<in>set xs. rel x z" by (simp add: sorted_wrt_Cons[OF assms(1)])
      moreover from \<open>x \<noteq> y\<close> have "y \<in> set xs" using 2(7) by auto
      ultimately have *: "rel x y" ..
      from 2(5) have "\<forall>z\<in>set ys. rel y z" by (simp add: sorted_wrt_Cons[OF assms(1)])
      moreover from \<open>x \<noteq> y\<close> have "x \<in> set ys" using 2(7) by auto
      ultimately have "rel y x" ..
      with assms(2) * have "x = y" by (rule antisympD)
      with \<open>x \<noteq> y\<close> show False ..
    qed
    from 2(3) have "sorted_wrt rel xs" by (simp add: sorted_wrt_Cons[OF assms(1)])
    moreover note \<open>distinct xs\<close>
    moreover from 2(5) have "sorted_wrt rel ys" by (simp add: sorted_wrt_Cons[OF assms(1)])
    moreover note \<open>distinct ys\<close>
    moreover from 2(7) \<open>x \<notin> set xs\<close> \<open>y \<notin> set ys\<close> have "set xs = set ys" by (auto simp add: \<open>x = y\<close>)
    ultimately have "xs = ys" by (rule 2(2))
    with \<open>x = y\<close> show ?case by simp
  qed
qed

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
  assumes "transp r" and "sorted_wrt r (insort_wrt s x xs)"
  shows "sorted_wrt r xs"
  using assms(2)
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases "s x a")
    case True
    with Cons(2) have "sorted_wrt r (x # a # xs)" by simp
    thus ?thesis by simp
  next
    case False
    with Cons(2) have "sorted_wrt r (a # (insort_wrt s x xs))" by simp
    hence *: "(\<forall>y\<in>set xs. r a y)" and "sorted_wrt r (insort_wrt s x xs)"
      by (simp_all add: sorted_wrt_Cons[OF assms(1)])
    from this(2) have "sorted_wrt r xs" by (rule Cons(1))
    with * show ?thesis by (simp add: sorted_wrt_Cons[OF assms(1)])
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
    from Cons(2) show ?thesis by (simp add: True)
  next
    case False
    with assms(2) have "r a x" by blast
    from Cons(2) have *: "(\<forall>y\<in>set xs. r a y)" and "sorted_wrt r xs"
      by (simp_all add: sorted_wrt_Cons[OF assms(1)])
    from this(2) have "sorted_wrt r (insort_wrt r x xs)" by (rule Cons(1))
    with \<open>r a x\<close> * show ?thesis by (simp add: False sorted_wrt_Cons[OF assms(1)])
  qed
qed

corollary sorted_wrt_insort_wrt:
  assumes "transp r" and "\<And>a. r a x \<or> r x a"
  shows "sorted_wrt r (insort_wrt r x xs) \<longleftrightarrow> sorted_wrt r xs" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  with assms(1) show ?r by (rule sorted_wrt_insort_wrt_imp_sorted_wrt)
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

fun merge_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "merge_wrt _ xs [] = xs"|
  "merge_wrt rel [] ys = ys"|
  "merge_wrt rel (x # xs) (y # ys) =
    (if x = y then
      y # (merge_wrt rel xs ys)
    else if rel x y then
      x # (merge_wrt rel xs (y # ys))
    else
      y # (merge_wrt rel (x # xs) ys)
    )"

lemma set_merge_wrt: "set (merge_wrt rel xs ys) = set xs \<union> set ys"
proof (induct rel xs ys rule: merge_wrt.induct)
  case (1 rel xs)
  show ?case by simp
next
  case (2 rel y ys)
  show ?case by simp
next
  case (3 rel x xs y ys)
  show ?case
  proof (cases "x = y")
    case True
    thus ?thesis by (simp add: 3(1))
  next
    case False
    show ?thesis
    proof (cases "rel x y")
      case True
      with \<open>x \<noteq> y\<close> show ?thesis by (simp add: 3(2) insert_commute)
    next
      case False
      with \<open>x \<noteq> y\<close> show ?thesis by (simp add: 3(3))
    qed
  qed
qed

lemma sorted_merge_wrt:
  assumes "transp rel" and "\<And>x y. x \<noteq> y \<Longrightarrow> rel x y \<or> rel y x"
    and "sorted_wrt rel xs" and "sorted_wrt rel ys"
  shows "sorted_wrt rel (merge_wrt rel xs ys)"
  using assms
proof (induct rel xs ys rule: merge_wrt.induct)
  case (1 rel xs)
  from 1(3) show ?case by simp
next
  case (2 rel y ys)
  from 2(4) show ?case by simp
next
  case (3 rel x xs y ys)
  show ?case
  proof (cases "x = y")
    case True
    show ?thesis
    proof (simp add: True, rule sorted_wrt_ConsI)
      fix z
      assume "z \<in> set (merge_wrt rel xs ys)"
      hence "z \<in> set xs \<union> set ys" by (simp only: set_merge_wrt)
      thus "rel y z"
      proof
        assume "z \<in> set xs"
        with 3(6) show ?thesis by (simp add: True sorted_wrt_Cons[OF 3(4)])
      next
        assume "z \<in> set ys"
        with 3(7) show ?thesis by (simp add: sorted_wrt_Cons[OF 3(4)])
      qed
    next
      note True 3(4, 5)
      moreover from 3(6) have "sorted_wrt rel xs" by (simp add: sorted_wrt_Cons[OF 3(4)])
      moreover from 3(7) have "sorted_wrt rel ys" by (simp add: sorted_wrt_Cons[OF 3(4)])
      ultimately show "sorted_wrt rel (merge_wrt rel xs ys)" by (rule 3(1))
    qed
  next
    case False
    show ?thesis
    proof (cases "rel x y")
      case True
      show ?thesis
      proof (simp add: False True, rule sorted_wrt_ConsI)
        fix z
        assume "z \<in> set (merge_wrt rel xs (y # ys))"
        hence "z \<in> insert y (set xs \<union> set ys)" by (simp add: set_merge_wrt)
        thus "rel x z"
        proof
          assume "z = y"
          with True show ?thesis by simp
        next
          assume "z \<in> set xs \<union> set ys"
          thus ?thesis
          proof
            assume "z \<in> set xs"
            with 3(6) show ?thesis by (simp add: sorted_wrt_Cons[OF 3(4)])
          next
            assume "z \<in> set ys"
            with 3(7) have "rel y z" by (simp add: sorted_wrt_Cons[OF 3(4)])
            with 3(4) True show ?thesis by (rule transpD)
          qed
        qed
      next
        note False True 3(4, 5)
        moreover from 3(6) have "sorted_wrt rel xs" by (simp add: sorted_wrt_Cons[OF 3(4)])
        ultimately show "sorted_wrt rel (merge_wrt rel xs (y # ys))" using 3(7) by (rule 3(2))
      qed
    next
      assume "\<not> rel x y"
      from \<open>x \<noteq> y\<close> have "rel x y \<or> rel y x" by (rule 3(5))
      with \<open>\<not> rel x y\<close> have *: "rel y x" by simp
      show ?thesis
      proof (simp add: False \<open>\<not> rel x y\<close>, rule sorted_wrt_ConsI)
        fix z
        assume "z \<in> set (merge_wrt rel (x # xs) ys)"
        hence "z \<in> insert x (set xs \<union> set ys)" by (simp add: set_merge_wrt)
        thus "rel y z"
        proof
          assume "z = x"
          with * show ?thesis by simp
        next
          assume "z \<in> set xs \<union> set ys"
          thus ?thesis
          proof
            assume "z \<in> set xs"
            with 3(6) have "rel x z" by (simp add: sorted_wrt_Cons[OF 3(4)])
            with 3(4) * show ?thesis by (rule transpD)
          next
            assume "z \<in> set ys"
            with 3(7) show ?thesis by (simp add: sorted_wrt_Cons[OF 3(4)])
          qed
        qed
      next
        note False \<open>\<not> rel x y\<close> 3(4, 5, 6)
        moreover from 3(7) have "sorted_wrt rel ys" by (simp add: sorted_wrt_Cons[OF 3(4)])
        ultimately show "sorted_wrt rel (merge_wrt rel (x # xs) ys)" by (rule 3(3))
      qed
    qed
  qed
qed

lemma set_fold:
  assumes "\<And>x ys. set (f (g x) ys) = set (g x) \<union> set ys"
  shows "set (fold (\<lambda>x. f (g x)) xs ys) = (\<Union>x\<in>set xs. set (g x)) \<union> set ys"
proof (induct xs arbitrary: ys)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  have eq: "set (fold (\<lambda>x. f (g x)) xs (f (g x) ys)) = (\<Union>x\<in>set xs. set (g x)) \<union> set (f (g x) ys)"
    by (rule Cons)
  show ?case by (simp add: o_def assms set_merge_wrt eq ac_simps)
qed

end (* theory *)
