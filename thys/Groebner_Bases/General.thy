text \<open>Some further general properties of, and functions on, lists.\<close>

theory General
imports Main
begin

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

end (* theory *)
