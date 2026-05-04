theory Utils
imports
  Main
  "HOL-Library.Finite_Map"
  "HOL-Library.Monad_Syntax"
begin

section \<open>Relators\<close>

lemma set_listall:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> (\<And>y. R x y = (f x = y))"
  shows "list_all2 R xs ys = (map f xs = ys)"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by blast
next
  case (Cons a xs)
  then show ?case
    by (smt (verit, best) list.set_intros(1,2) list.simps(9) list_all2_Cons1)
qed

section \<open>Fold\<close>

lemma fold_none_none[simp]:
  "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x y')) xs None = None"
  by (induction xs) (simp_all)

lemma fold_take:
  assumes "n < length xs"
  shows "fold f (take (Suc n) xs) s = f (xs!n) (fold f (take n xs) s)"
  using assms
proof (induction xs arbitrary: s n)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases n) (simp_all)
qed

lemma fold_some_take_some:
  assumes "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x y')) xs a = Some x"
     and "n < length xs"
  obtains y where "(fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x y')) (take n xs) a) \<bind> (\<lambda>y'. f (xs!n) y') = Some y"
proof -
  have "\<forall>n. n < length xs \<longrightarrow> (\<exists>y. (\<lambda>x y. y \<bind> (\<lambda>y'. f x y')) (xs!n) (fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x y')) (take n xs) a) = Some y)"
  proof (rule ccontr)
    assume "\<not> (\<forall>n. n < length xs \<longrightarrow> (\<exists>y. fold (\<lambda>x y. y \<bind> f x) (take n xs) a \<bind> f (xs ! n) = Some y))"
    then obtain n where *: "n < length xs" and **: "fold (\<lambda>x y. y \<bind> f x) (take n xs) a \<bind> f (xs ! n) = None" by blast
    {
      fix n' assume "n \<le> n'"
      then have "n' < length xs \<longrightarrow> fold (\<lambda>x y. y \<bind> f x) (take n' xs) a \<bind> f (xs ! n') = None"
      proof (induction rule: nat_induct_at_least)
        case base
        then show ?case using ** by simp
      next
        case (Suc n')
        then show ?case by (simp add: fold_take)
      qed
    }
    then have "fold (\<lambda>x y. y \<bind> f x) (take (length xs - 1) xs) a \<bind> f (xs ! (length xs - 1)) = None"
      using "*" One_nat_def by auto
    then have "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x y')) xs a = None"
      using * fold_take[of "(length xs - 1)" xs "(\<lambda>x y. y \<bind> f x)"] by auto
    then show False using assms by simp
  qed
  then show ?thesis using that using assms(2) by blast
qed

lemma fold_same:
  assumes "\<forall>x\<in>set xs. f x = g x"
  shows "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs L
      = fold (\<lambda>x y. y \<bind> (\<lambda>y'. g x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs L"
  using assms
  by (induction xs arbitrary: L,auto)

lemma fold_f_none_none[simp]:
  assumes "f a = None"
  shows "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) (a # xs) (Some X) = None"
using assms by (induction xs) (simp_all)

lemma fold_none_the_fold:
  assumes "(fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some X)) \<noteq> None
         \<or> (fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some (X |\<union>| Y))) \<noteq> None"
     shows "the (fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some (X |\<union>| Y))) =
           (the (fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some X))) |\<union>| Y"
  using assms
proof (induction xs arbitrary: X)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases "f a")
    case None
    then show ?thesis using Cons by auto
  next
    case (Some a')
    moreover from Cons(2) have
      "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some (a' |\<union>| X)) \<noteq> None
     \<or> fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) (a # xs) (Some (X |\<union>| Y)) \<noteq> None"
      using Some by (simp add: funion_assoc)
    ultimately show ?thesis 
    using Cons(1)[of "((a' |\<union>| X))"] by (simp add: sup_assoc)
  qed
qed

lemma fold_some_some:
  shows "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) (take (n) xs) (Some (finsert x X))
       = fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) (take (n) xs) (Some X) \<bind> Some \<circ> finsert x"
proof (induction xs arbitrary: n X)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis by auto
  next
    case (Suc n')
    show ?thesis
    proof (cases "f a")
      case None
      then show ?thesis using Suc by auto
    next
      case (Some a')
      then show ?thesis 
      using Cons(1)[of n' "the (f a) |\<union>| X"] Suc by auto
    qed
  qed
qed

lemma fold_insert_same:
  assumes "x \<notin> fset (the (fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) (take n xs) (Some X)))"
     shows "the (fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) (take n xs) (Some X)) =
           (the (fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) (take n xs) (Some (finsert x X)))) |-| {|x|}"
  using assms
proof (induction xs arbitrary: n X)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis using Cons by auto
  next
    case (Suc n')
    show ?thesis
    proof (cases "f a")
      case None
      then show ?thesis using Suc Cons by auto
    next
      case (Some a')
      then show ?thesis 
      using Cons(1)[of n' "the (f a) |\<union>| X"] Cons Suc by auto
    qed
  qed
qed

lemma fold_some_diff:
  assumes "x \<notin> fset (the (fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) (take n xs) (Some {||})))"
      and "(fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) (take n xs) (Some {||})) \<noteq> None"
  shows "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) (take n xs) (Some {||}) =
      Some ((the (fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) (take n xs) (Some {|x|}))) |-| {|x|})"
  using fold_insert_same[OF assms(1)] assms by fastforce

lemma fold_none[simp]:
  "fold (\<lambda>x y. y \<bind> g x) xs None = None"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by auto
qed

lemma fold_some:
  assumes "fold (\<lambda>x y. y \<bind> (\<lambda>y'. (f x) \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs X0 = Some X"
  shows "\<exists>X'. X0 = Some X' \<and> X' |\<subseteq>| X"
  using assms
proof (induction xs arbitrary: X0)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  from Cons(2) obtain X' where "X0 = Some X'" by (case_tac X0, auto)
  with Cons(2) have *: "(fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (f a \<bind> (\<lambda>l. Some (l |\<union>| X')))) = Some X" by auto
  with Cons(1) obtain X'' where X''_def: "f a \<bind> (\<lambda>l. Some (l |\<union>| X')) = Some X''" and "X'' |\<subseteq>| X" by auto
  moreover from * X''_def have "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some X'') = Some X"
    by auto
  ultimately show ?case using `X0 = Some X'` by (case_tac "f a", auto)
qed

lemma fold_some_ex:
  assumes "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some X') = Some X"
    and "i |\<in>| X"
    and "i |\<notin>| X'"
  shows "\<exists>x A. x \<in> set xs \<and> f x = Some A \<and> i |\<in>| A"
  using assms
proof (induction xs arbitrary: X')
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  from Cons(2) obtain X'' where fa_def: "f a = Some X''" by fastforce
  show ?case
  proof (cases "i |\<in>| X''")
    case True
    then show ?thesis using Cons fa_def by auto
  next
    case False
    moreover from Cons(2) have "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (f a \<bind> (\<lambda>l. Some (l |\<union>| X'))) = Some X" by auto
    ultimately show ?thesis using Cons(1)[of "X'' |\<union>| X'", OF _ Cons(3)] Cons(4) fa_def by auto
  qed
qed

lemma fold_some_subs:
  assumes "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs X' = Some X"
    and "i \<in> set xs"
  shows "\<exists>A. f i = Some A \<and> A |\<subseteq>| X"
  using assms
proof (induction xs arbitrary: X')
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  from Cons(2) obtain X'' where "X' = Some X''" by (case_tac X', auto)
  with Cons have xx: "(fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (f a \<bind> (\<lambda>l. Some (l |\<union>| X'')))) = Some X" by auto
  
  then show ?case
  proof (cases "i = a")
    case True
    with xx obtain XX where "(f i \<bind> (\<lambda>l. Some (l |\<union>| X''))) = Some XX" and "XX |\<subseteq>| X" using fold_some by blast
    then obtain XXX where "f i = Some XXX" and "XX = XXX |\<union>| X''" by (cases "f i", auto)
    then show ?thesis using `XX |\<subseteq>| X` by simp
  next
    case False
    then show ?thesis using xx Cons.IH Cons.prems(2) by auto
  qed
qed

lemma fold_subs_none:
  assumes "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some X) = None"
      and "X |\<subseteq>| Y"
    shows "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some Y) = None"
  using assms
proof (induction xs arbitrary: X Y)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
  proof (cases "f x")
    case None
    then show ?thesis using Cons by simp
  next
    case (Some x')
    then have "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) (x # xs) (Some Y) =
             fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some (x' |\<union>| Y))" by simp
    moreover have "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some (x' |\<union>| Y)) = None"
      apply (rule Cons(1)) using Cons(2,3) Some by auto
    ultimately show ?thesis by auto
  qed
qed

lemma fold_f_set_none:
  assumes "a \<in> set xs"
    and "f a = None"
  shows "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some X) = None"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
  proof (cases "x=a")
    case True
    then show ?thesis using Cons by simp
  next
    case False
    then have "a \<in> set xs" using Cons by simp
    then have "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some X) = None"
      using Cons by simp
    then show ?thesis by (cases "f x",auto simp add: fold_subs_none)
  qed
qed

lemma fold_f_set_some:
  assumes "\<forall>a \<in> set xs. f a \<noteq> None"
  shows "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some X) \<noteq> None"
  using assms
proof (induction xs arbitrary: X)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then obtain y where "(f x \<bind> (\<lambda>l. Some (l |\<union>| X))) = Some (y |\<union>| X)" by auto
  moreover from Cons have "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some (y |\<union>| X)) \<noteq> None" by simp
  ultimately show ?case by simp
qed

lemma fold_disj:
  assumes "\<forall>x \<in> set xs. \<forall>L. f x = Some L \<longrightarrow> s |\<inter>| L = {||}"
      and "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some X) = Some L"
      and "X |\<inter>| s = {||}"
    shows "s |\<inter>| L = {||}"
  using assms
proof (induction xs arbitrary:X)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  from Cons(2) have "\<forall>x\<in>set xs. \<forall>L. f x = Some L \<longrightarrow> s |\<inter>| L = {||}" by simp
  moreover from Cons(3) obtain L'
    where *: "f a = Some L'"
      and "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some (L' |\<union>| X)) = Some L"
    by (cases "f a"; simp)
  moreover have "L' |\<inter>| s = {||}" using Cons(2) * by auto
  ultimately show ?case using Cons(1,4) by blast
qed

lemma fold_union_in:
  assumes "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some L) = Some L'"
      and "x |\<in>| L'"
    shows "x |\<in>| L \<or> (\<exists>n L''. n<length xs \<and> f (xs ! n) = Some L'' \<and> x |\<in>| L'')"
  using assms
proof (induction xs arbitrary: L)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  from Cons(2) have
    *: "fold
          (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y'))))
          xs
          (f a \<bind> (\<lambda>l. Some (l |\<union>| L)))
       = Some L'"
    by simp
  moreover from * obtain L''' where "f a = Some L'''" by fastforce
  ultimately have
    "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some (L''' |\<union>| L)) = Some L'"
    by simp
  then have "x |\<in>| (L''' |\<union>| L) \<or> (\<exists>n L''. n < length xs \<and> f (xs ! n) = Some L'' \<and> x |\<in>| L'')"
    using Cons by blast
  then show ?case
  proof
    assume "x |\<in>| L''' |\<union>| L"
    then show ?thesis
    proof
      assume "x |\<in>| L'''"
      then show "x |\<in>| L \<or> (\<exists>n L''. n < length (a # xs) \<and> f ((a # xs) ! n) = Some L'' \<and> x |\<in>| L'')"
        using \<open>f a = Some L'''\<close> by auto
    next
      assume "x |\<in>| L"
      then show ?thesis by simp
    qed
  next
    assume "\<exists>n L''. n < length xs \<and> f (xs ! n) = Some L'' \<and> x |\<in>| L''"
    then show ?thesis by auto
  qed
qed

lemma fold_subs:
  assumes "\<forall>x \<in> set xs. \<forall>L. f x = Some L \<longrightarrow> fset L \<subseteq> Y"
      and "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some X) = Some L"
      and "fset X \<subseteq> Y"
    shows "fset L \<subseteq> Y"
  using assms
proof (induction xs arbitrary:X)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  from Cons(2) have "\<forall>x\<in>set xs. \<forall>L. f x = Some L \<longrightarrow> fset L \<subseteq> Y" by simp
  moreover from Cons(3) obtain L'
    where *: "f a = Some L'"
      and "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some (L' |\<union>| X)) = Some L"
    by (cases "f a"; simp)
  moreover have "fset L' \<subseteq> Y" using Cons(2) * by auto
  ultimately show ?case using Cons(1,4) by blast
qed

lemma fold_in_subs:
  assumes "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some X) = Some L"
      and "x \<in> set xs"
      and "f x = Some S"
    shows "S |\<subseteq>| L"
using assms
proof (induction xs arbitrary:X)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  from Cons(2) obtain L'
    where *: "f a = Some L'"
      and **: "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some (L' |\<union>| X)) = Some L"
    by (cases "f a"; simp)
  then have "L' |\<subseteq>| L" using fold_some[of f xs "(Some (L' |\<union>| X))" L] by simp
  show ?case
  proof (cases "a = x")
    case True
    then show ?thesis using \<open>L' |\<subseteq>| L\<close>
      using "*" assms(3) by auto
  next
    case False
    then show ?thesis using Cons(1)[OF **] Cons(3)
      using assms(3) by auto
  qed
qed

section \<open>Take\<close>

lemma take_all:
  assumes "\<forall>n \<le> length xs. P (take n xs) (take n ys)"
      and "length xs = length ys"
  shows "P xs ys"
  using assms
  by auto

lemma take_all1:
  assumes "\<forall>n \<le> length xs. P (take n xs)"
  shows "P xs"
  using assms
  by auto

lemma rev_induct2 [consumes 1, case_names Nil snoc]:
  assumes "length xs = length ys" and "P [] []"
      and "(\<And>x xs y ys. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (xs @ [x]) (ys @ [y]))"
    shows "P xs ys"
proof -
  have "P (rev (rev xs)) (rev (rev ys))"
    by (rule_tac xs = "rev xs" and ys = "rev ys" in list_induct2, simp_all add: assms)
  then show ?thesis by simp
qed

section \<open>Filter\<close>

lemma length_filter_take_suc:
  assumes "n<length daa"
      and "P (daa!n)"
    shows "length (filter P (take (Suc n) daa)) = Suc (length (filter P (take n daa)))"
  using assms
proof (induction daa arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis
      using Cons.prems(2) by auto
  next
    case (Suc nat)
    then have "nat < length (x)"
      using Cons.prems(1) by auto
    moreover have "P (x ! nat)"
      using Cons.prems(2) Suc by auto
    ultimately have "length (filter P (take (Suc nat) x)) = Suc (length (filter P (take nat x)))"
      using Cons.IH by blast
    then show ?thesis by (simp add: Suc)
  qed
qed

section \<open>Those\<close>

lemma those_map:
  assumes "length xs = length ys"
      and "those (map f (x # xs)) = Some (y # ys)"
    shows "those (map f xs) = Some ys \<and> f x = Some y"
  using assms
  by (induction xs ys rule: list_induct2; simp split:option.split_asm)

lemma those_map_eq:
  assumes "\<forall>x \<in> set xs. \<forall>y. f x = Some y \<longrightarrow> g x = Some y"
      and "\<forall>x \<in> set xs. f x \<noteq> None"
    shows "those (map f xs) = those (map g xs)"
  using assms
  by (metis list.map_cong0 option.exhaust)

lemma those_map_none:
  assumes "those (map f xs) = Some y"
  shows "\<forall>x \<in> set xs. f x \<noteq> None"
proof (rule ccontr)
  assume "\<not> (\<forall>x\<in>set xs. f x \<noteq> None)"
  then obtain x where "x\<in>set xs" and "f x = None" by auto
  then have "those (map f xs) = None"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case by (auto split:option.split)
  qed
  then show False using assms by simp
qed

lemma those_map_some[simp]:
  "those (map Some xs) = Some xs"
by (induction xs) (simp_all)

lemma those_some_map:
  assumes "those xs = Some xs'"
    shows "xs = map Some xs'"
  using assms by (induction xs arbitrary:xs') (auto split:option.split_asm)

lemma those_those:
  assumes "those xs = Some xs'"
      and "those ys = Some ys'"
    shows "(those (xs @ ys)) = Some (xs' @ ys')"
  by (metis assms(1) assms(2) map_append those_map_some those_some_map)

lemma those_map_none_none:
  assumes "those (map f as) = None"
  shows "\<exists>x \<in> set as. f x = None"
  using assms
  by (induction as;fastforce)

lemma those_map_some_some:
  assumes "\<forall>x \<in> set as. f x \<noteq> None"
  shows "those (map f as) \<noteq> None"
  using those_map_none_none assms by blast

lemma map_some_those_some:
  assumes "length as = length ls"
      and "\<forall>i<length as. map f ls ! i = Some (as ! i)"
    shows "those (map f ls) = Some as"
  using assms
  by (metis map_equality_iff nth_map those_map_some)

section \<open>Fold Map\<close>

fun fold_map where
    "fold_map _ [] y = ([], y)"
  | "fold_map f (x # xs) y =
      (let (x', y') = f x y in
       (let (xs', y'') = fold_map f xs y'
      in (x' # xs', y'')))"

lemma fold_map_length:
  "length (fst (fold_map f ds m)) = length ds"
proof (induction ds arbitrary: m)
  case Nil
  then show ?case by simp
next
  case (Cons a ds)
  from Cons(1)[of "snd (f a m)"] show ?case by (auto split:prod.split)
qed

lemma fold_map_mono:
  assumes "\<And>x y x' y'. (f x y) = (x',y') \<Longrightarrow> f' y' \<ge> ((f' y):: nat)"
    and "fold_map f x y = (x', y')"
  shows "f' y' \<ge> f' y"
using assms by (induction x arbitrary: y x' y', simp) (force split:prod.split prod.split_asm)

lemma fold_map_geq:
  assumes "\<And>y x. f' (snd (f y x)) \<ge> ((f' x):: nat)"
  shows "f' (snd (fold_map f x y)) \<ge> f' y"
proof (rule fold_map_mono[of f f' x])
  show "fold_map f x y = (fst (fold_map f x y), snd (fold_map f x y))" by simp
next
  fix x y x' y'
  assume "f x y = (x', y')"
  then show "f' y \<le> f' y'" using assms by (metis snd_conv)
qed

lemma fold_map_cong [fundef_cong]:
  "a = b \<Longrightarrow> xs = ys \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> f x = g x)
    \<Longrightarrow> fold_map f xs a = fold_map g ys b"
  by (induct ys arbitrary: a b xs) simp_all

lemma fold_map_take_fst:
  assumes "n < length (fst (fold_map f xs m))"
  shows "fst (fold_map f xs m) ! n = fst (f (xs ! n) (snd (fold_map f (take n xs) m)))"
  using assms
proof (induction xs arbitrary: m n)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
   show ?case
  proof (cases n)
    case 0
    then show ?thesis by (auto split:prod.split)
  next
    case (Suc n')
    then have "n' < length (fst (fold_map f xs (snd (f a m))))" using Cons(2) by (auto split:prod.split_asm)
    then have "fst (fold_map f xs (snd (f a m))) ! n' = fst (f (xs ! n') (snd (fold_map f (take n' xs) (snd (f a m)))))" using Cons(1)[of "n'" "(snd (f a m))"] by simp
    moreover have "fst (fold_map f (a # xs) m) ! Suc n' = fst ((fold_map f xs (snd (f a m)))) ! n'" by (simp split:prod.split)
    moreover have "(a # xs) ! Suc n' = xs ! n'" by simp
    moreover have "(snd (fold_map f (take n' xs) (snd (f a m)))) = (snd (fold_map f (take (Suc n') (a # xs)) m))" by (simp split:prod.split)
    ultimately show ?thesis by (simp add: Suc)
  qed
qed

lemma fold_map_take_snd:
  assumes "n < length xs"
  shows "snd (fold_map f (take (Suc n) xs) m) = snd (f (xs ! n) (snd (fold_map f (take n xs) m)))"
  using assms
proof (induction xs arbitrary: m n)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis by (auto split:prod.split)
  next
    case (Suc n')
    then have "snd (fold_map f (take (Suc n') xs) (snd (f a m)))
             = snd (f (xs ! n') (snd (fold_map f (take n' xs) (snd (f a m)))))" using Cons by auto
    then show ?thesis using Suc by (auto split:prod.split)
  qed
qed

section \<open>Prefix\<close>

definition prefix where "prefix m0 mf = (\<exists>m'''. mf = m0@m''')"

lemma prefix_id[intro]: "prefix x x" unfolding prefix_def by simp

lemma prefix_trans: "prefix x y \<Longrightarrow> prefix y z \<Longrightarrow> prefix x z" unfolding prefix_def by fastforce

definition sprefix where "sprefix m0 mf = (\<exists>m''' \<noteq> []. mf = m0@m''')"

lemma sprefix_append[simp]: "sprefix xs (xs@[y])" unfolding sprefix_def by blast

lemma sprefix_prefix: "sprefix m0 mf \<Longrightarrow> prefix m0 mf" unfolding prefix_def sprefix_def by auto

lemma sprefix_trans: "sprefix x y \<Longrightarrow> sprefix y z \<Longrightarrow> sprefix x z" unfolding sprefix_def by fastforce

lemma sprefix_length: "sprefix x y \<Longrightarrow> length x < length y" unfolding sprefix_def by auto

lemma fold_map_prefix:
  assumes "fold_map f ds m = (ls, m')"
    and "\<And>x y x' y'. f x y = (x', y') \<Longrightarrow> prefix y y'"
  shows "prefix m m'"
  using assms
proof (induction ds arbitrary: m m' ls)
  case Nil
  then show ?case unfolding prefix_def by simp
next
  case (Cons a ds)
  from Cons(2) show ?case
  proof (auto split:prod.split_asm)
    fix x1 x2 x1a
    assume *: "f a m = (x1, x2)"
      and "fold_map f ds x2 = (x1a, m')"
      and "ls = x1 # x1a"
    then have "prefix x2 m'" using Cons by simp
    moreover have "prefix m x2" using Cons(3)[OF *] by simp
    ultimately show "prefix m m'" unfolding prefix_def by auto
  qed
qed


definition length_append where "length_append m x = (length m, m@[x])"

primrec ofold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b option" where
  fold_Nil:  "ofold f [] = Some" |
  fold_Cons: "ofold f (x # xs) b = ofold f xs b \<bind> f x"

lemma ofold_cong [fundef_cong]:
  "a = b \<Longrightarrow> xs = ys \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> f x = g x)
    \<Longrightarrow> ofold f xs a = ofold g ys b"
  by (induct ys arbitrary: a b xs) simp_all

fun K where "K f _ = f"

fun append (infixr "@@" 65) where "append xs x = xs @ [x]"

abbreviation case_list where "case_list l a b \<equiv> List.case_list a b l"

section \<open>Nth safe\<close>

definition nth_safe :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" (infixl "$" 100)
  where "nth_safe xs i = (if i < length xs then Some (xs!i) else None)"

lemma nth_safe_some[simp]: "i < length xs \<Longrightarrow> xs $ i = Some (xs!i)" unfolding nth_safe_def by simp
lemma nth_safe_none[simp]: "i \<ge> length xs \<Longrightarrow> xs $ i = None" unfolding nth_safe_def by simp
lemma nth_safe_length: "xs $ i = Some x \<Longrightarrow> i < length xs" unfolding nth_safe_def by (simp split: if_split_asm)

definition list_update_safe :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('a list) option"
  where "list_update_safe xs i a = (if i < length xs then Some (list_update xs i a) else None)"

lemma those_map_nth:
  assumes "those (map f as) = Some xs"
  shows "as $ x \<bind> f = xs $ x"
proof -
  from assms(1) have "length as = length xs" using those_some_map map_equality_iff by blast
  then show ?thesis using assms
  proof (induction as xs arbitrary: x rule: list_induct2)
    case Nil
    then show ?case by simp
  next
    case (Cons x' xs' y' ys')
    then have *: "those (map f xs') = Some ys'" and **: "f x' = Some y'" using those_map by metis+
    from * have ***: "\<And>x. xs' $ x \<bind> f = ys' $ x" using Cons(2) by blast
    then have "(x' # xs') $ x \<bind> f = (y' # ys') $ x"
    proof (cases x)
      case 0
      then show ?thesis
      using ** by (auto)
    next
      case (Suc nat)
      moreover from *** have "(xs') $ nat \<bind> f = (ys') $ nat" by simp
      ultimately show ?thesis
        by (metis Suc_less_eq length_Cons nth_Cons_Suc nth_safe_def)
    qed
    then show ?case by auto
  qed
qed

lemma nth_in_set:
  assumes "xs $ x = Some y"
  shows "y \<in> set xs"
  using assms unfolding nth_safe_def by (auto split:if_split_asm)

lemma set_nth_some:
  assumes "y \<in> set xs"
  shows "\<exists>x. xs $ x = Some y"
  using assms unfolding nth_safe_def 
  by (metis in_set_conv_nth)

lemma those_map_some_nth:
  assumes "those (map f as) = Some a"
    and "as $ x = Some y"
  obtains z where "f y = Some z"
  using assms
  by (metis not_None_eq nth_mem nth_safe_def option.inject those_map_none)

lemma nth_safe_prefix:
  assumes "m $ l = Some v"
  and "prefix m m'"
shows "m' $ l = Some v"
  using assms unfolding prefix_def nth_safe_def
  by (auto split:if_split_asm simp add: nth_append_left)

section \<open>Some Basic Lemmas for Finite Maps\<close>

lemma fmfinite: "finite ({(ad, x). fmlookup y ad = Some x})"
proof -
  have "{(ad, x). fmlookup y ad = Some x} \<subseteq> dom (fmlookup y) \<times> ran (fmlookup y)"
  proof
    fix x assume "x \<in> {(ad, x). fmlookup y ad = Some x}"
    then have "fmlookup y (fst x) = Some (snd x)" by auto
    then have "fst x \<in> dom (fmlookup y)" and "snd x \<in> ran (fmlookup y)" using Map.ranI by (blast,metis)
    then show "x \<in> dom (fmlookup y) \<times> ran (fmlookup y)" by (simp add: mem_Times_iff)
  qed
  thus ?thesis by (simp add: finite_ran finite_subset)
qed

lemma fmlookup_finite:
  fixes f :: "'a \<Rightarrow> 'a"
    and y :: "('a, 'b) fmap"
  assumes "inj_on (\<lambda>(ad, x). (f ad, x)) {(ad, x). (fmlookup y \<circ> f) ad = Some x}"
  shows "finite {(ad, x). (fmlookup y \<circ> f) ad = Some x}"
proof (cases rule: inj_on_finite[OF assms(1), of "{(ad, x)|ad x. (fmlookup y) ad = Some x}"])
  case 1
  then show ?case by auto
next
  case 2
  then have *: "finite {(ad, x) |ad x. fmlookup y ad = Some x}" using fmfinite[of y] by simp
  show ?case using finite_image_set[OF *, of "\<lambda>(ad, x). (ad, x)"] by simp
qed

section "Address class with example instantiation"

class address = finite +
  fixes null :: 'a

definition aspace_carrier where "aspace_carrier={0::nat, 1, 2, 3, 4, 5, 6, 7, 8, 9}"

lemma aspace_carrier_finite: "finite aspace_carrier" unfolding aspace_carrier_def by simp

typedef aspace = aspace_carrier
  unfolding aspace_carrier_def
  by (rule_tac x = 0 in exI) simp

setup_lifting type_definition_aspace

lift_definition A0 :: aspace is 0 unfolding aspace_carrier_def by simp
lift_definition A1 :: aspace is 1 unfolding aspace_carrier_def by simp
lift_definition A2 :: aspace is 2 unfolding aspace_carrier_def by simp
lift_definition A3 :: aspace is 3 unfolding aspace_carrier_def by simp
lift_definition A4 :: aspace is 4 unfolding aspace_carrier_def by simp
lift_definition A5 :: aspace is 5 unfolding aspace_carrier_def by simp
lift_definition A6 :: aspace is 6 unfolding aspace_carrier_def by simp
lift_definition A7 :: aspace is 7 unfolding aspace_carrier_def by simp
lift_definition A8 :: aspace is 8 unfolding aspace_carrier_def by simp
lift_definition A9 :: aspace is 9 unfolding aspace_carrier_def by simp

lemma aspace_finite: "finite (UNIV::aspace set)"
  using finite_imageI[OF aspace_carrier_finite, of Abs_aspace]
    type_definition.Abs_image[OF type_definition_aspace] by simp

lemma A1_neq_A0[simp]: "A1 \<noteq> A0"
  by transfer simp

instantiation aspace :: address
begin
  definition null_def: "null = A0"
  instance proof
    show "finite (UNIV::aspace set)" using aspace_finite by simp
  qed
end

instantiation aspace :: equal
begin

definition "HOL.equal (x::aspace) y \<longleftrightarrow> Rep_aspace x = Rep_aspace y"

instance apply standard by(simp add: Rep_aspace_inject equal_aspace_def)

end

section "Common lemmas for sums"

lemma sum_addr:
  fixes f::"('a::address)\<Rightarrow>nat"
  shows "(\<Sum>ad\<in>UNIV. f ad) = (\<Sum>ad|ad \<noteq> addr. f ad) + f addr"
proof -
  have "finite {ad \<in> UNIV. ad \<noteq> addr}" and "finite {ad \<in> UNIV. ad = addr}" using finite by simp+
  moreover have "UNIV = {ad \<in> UNIV. ad \<noteq> addr} \<union> {ad \<in> UNIV. ad = addr}" by auto
  moreover have "{ad \<in> UNIV. ad \<noteq> addr} \<inter> {ad \<in> UNIV. ad = addr} = {}" by auto
  ultimately have "sum f UNIV = sum f {ad \<in> UNIV. ad \<noteq> addr} + sum f {ad \<in> UNIV. ad = addr}"
    using sum_Un_nat[of "{ad\<in>UNIV. ad \<noteq> addr}" "{ad\<in>UNIV. ad = addr}" f] by simp
  moreover have "sum f {ad \<in> UNIV. ad = addr} = f addr" by simp
  ultimately show ?thesis by simp
qed

lemma sum_addr2:
  fixes f::"'a::address\<Rightarrow>nat"
  assumes "addr \<in> A"
  shows "(\<Sum>ad\<in>A. f ad) = (\<Sum>ad|ad\<in>A \<and> ad \<noteq> addr. f ad) + f addr"
proof -
  have "finite {ad \<in> A. ad \<noteq> addr}" and "finite {ad \<in> A. ad = addr}" using finite by simp+
  moreover have "A = {ad \<in> A. ad \<noteq> addr} \<union> {ad \<in> A. ad = addr}" by auto
  moreover have "{ad \<in> A. ad \<noteq> addr} \<inter> {ad \<in> A. ad = addr} = {}" by auto
  ultimately have "(\<Sum>ad\<in>A. f ad) = (\<Sum>ad|ad\<in>A \<and> ad \<noteq> addr. f ad) + (\<Sum>ad|ad\<in>A \<and> ad = addr. f ad)"
    using sum_Un_nat[of "{ad\<in>A. ad \<noteq> addr}" "{ad\<in>A. ad = addr}" f] by simp
  moreover have "{ad \<in> A. ad = addr} = {addr}" using assms by auto
  then have "sum f {ad \<in> A. ad = addr} = f addr" by simp
  ultimately show ?thesis by simp
qed

lemma sum_addr3:
  fixes f::"'a::address\<Rightarrow>nat"
  assumes "addr \<notin> A"
  shows "(\<Sum>ad\<in>A. f ad) = (\<Sum>ad|ad\<in>A \<and> ad \<noteq> addr. f ad)"
proof -
  have "finite {ad \<in> A. ad \<noteq> addr}" and "finite {ad \<in> A. ad = addr}" using finite by simp+
  moreover have "A = {ad \<in> A. ad \<noteq> addr} \<union> {ad \<in> A. ad = addr}" by auto
  moreover have "{ad \<in> A. ad \<noteq> addr} \<inter> {ad \<in> A. ad = addr} = {}" by auto
  ultimately have "(\<Sum>ad\<in>A. f ad) = (\<Sum>ad|ad\<in>A \<and> ad \<noteq> addr. f ad) + (\<Sum>ad|ad\<in>A \<and> ad = addr. f ad)"
    using sum_Un_nat[of "{ad\<in>A. ad \<noteq> addr}" "{ad\<in>A. ad = addr}" f] by simp
  moreover have "{ad \<in> A. ad = addr} = {}" using assms by simp
  then have "sum f {ad \<in> A. ad = addr} = 0" by simp
  ultimately show ?thesis by simp
qed

section \<open>Pred Some\<close>

definition pred_some where
  "pred_some P v = (\<exists>v'. v = Some v' \<and> P v')"

definition fs_disj_fs where
  "fs_disj_fs B C = pred_some (\<lambda>C'. pred_some (\<lambda>B'. C' |\<inter>| B' = {||}) B) C"

definition s_disj_fs where
  "s_disj_fs B C = pred_some (\<lambda>C'. fset C' \<inter> B = {}) C"

definition s_eq_fs where
  "s_eq_fs B C = pred_some (\<lambda>C'. B = fset C') C"

definition s_subs_fs where
  "s_subs_fs B C = pred_some (\<lambda>C'. B \<subseteq> fset C') C"

definition fs_subs_fs where
  "fs_subs_fs B C = pred_some (\<lambda>B'. B' |\<subseteq>| C) B"

definition fs_subs_s where
  "fs_subs_s B C = pred_some (\<lambda>B'. fset B' \<subseteq> C) B"

definition s_union_fs where
  "s_union_fs A B C = pred_some (\<lambda>C'. A = B \<union> fset C') C"

definition loc where
  "loc m = {l. l < length m}"

lemma s_disj_fs_prefix:
  assumes "prefix m m'"
    and "s_disj_fs (loc m') X"
  shows "s_disj_fs (loc m) X"
  using assms unfolding prefix_def s_disj_fs_def pred_some_def loc_def by fastforce

lemma s_union_fs_s_union_fs_union:
  assumes "s_union_fs B X B'"
      and "A = (B - C) \<union> D"
      and "A' = Some ((the B' |-| C') |\<union>| the D')"
      and "C \<inter> X = {}"
      and "C = fset C'"
      and "D = fset (the D')"
    shows "s_union_fs A X A'"
  using assms unfolding s_union_fs_def pred_some_def
  by fastforce

lemma s_union_fs_diff:
  assumes "s_union_fs A B C"
    and "B \<inter> fset (the C) = {}"
  shows "(A - B) = fset (the C)"
  using assms unfolding s_union_fs_def pred_some_def by auto

lemma s_disj_fs_loc_fold:
  assumes "s_disj_fs (loc m0) (fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (X))"
    and "s_disj_fs (loc m0) X"
  shows "s_disj_fs (loc m0) (fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) (take n xs) (X))"
  using assms
proof (induction xs arbitrary:n X)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis using Cons by simp
  next
    case (Suc nat)
    show ?thesis
    proof (cases "f a")
      case None
      then show ?thesis using Suc Cons by simp
    next
      case (Some a')
      moreover have "s_disj_fs (loc m0) (fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs ((\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) a X))" using Cons(2) by auto
      moreover have "s_disj_fs (loc m0) ((\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) a X)"
      proof -
        obtain y where *: "X = Some y" using Cons(3) unfolding s_disj_fs_def pred_some_def by blast
        moreover from Cons(2) have "s_disj_fs (loc m0) (fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some (a' |\<union>| y)))"
          using Some * by simp
        moreover from Cons(2) have "fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some ({||} |\<union>| (a' |\<union>| y))) \<noteq> None"
          using * Some unfolding s_disj_fs_def pred_some_def by auto
        then have "the (fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some (a' |\<union>| y)))
        = the (fold (\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) xs (Some {||})) |\<union>| (a' |\<union>| y)"
          using fold_none_the_fold[of f xs "{||}" "(a' |\<union>| y)"] by simp
        ultimately show ?thesis using Some unfolding s_disj_fs_def pred_some_def by auto 
      qed
      ultimately show ?thesis
        using Cons(1)[of "((\<lambda>x y. y \<bind> (\<lambda>y'. f x \<bind> (\<lambda>l. Some (l |\<union>| y')))) a (X))" nat] Suc
        by auto
    qed
  qed
qed

lemma s_disj_union_fs: "s_disj_fs B C \<Longrightarrow> s_union_fs A B C \<Longrightarrow> fset (the C) = A - B"
unfolding s_disj_fs_def s_union_fs_def pred_some_def by fastforce

lemma disj_empty[simp]: "s_disj_fs X (Some {||})" unfolding s_disj_fs_def pred_some_def by simp

lemma s_union_fs_s_union_fs_diff:
  assumes "s_union_fs X Y Z"
    and "X' = X - {a}"
    and "the Z' = the Z |-| {|a|}"
    and "Z' \<noteq> None"
    and "a \<notin> Y"
  shows "s_union_fs X' Y Z'"
  using assms unfolding s_union_fs_def pred_some_def
  by fastforce

section \<open>Termination Lemmas\<close>

lemma card_less_card:
  assumes "m $ p1 = Some a"
      and "p1 |\<notin>| s1"
    shows "card ({0..length m} - insert p1 (fset s1)) < card ({0..length m} - fset s1)"
proof -
  have "card ({0..length m} - insert p1 (fset s1)) = card ({0..length m}) - card ({0..length m} \<inter> insert p1 (fset s1))"
   and "card ({0..length m} - fset s1) = card ({0..length m}) - card ({0..length m} \<inter> (fset s1))" by (rule card_Diff_subset_Int, simp)+
  moreover from assms(2) have "card ({0..length m} \<inter> insert p1 (fset s1)) = Suc (card ({0..length m} \<inter> (fset s1)))" using nth_safe_length[OF assms(1)] by simp
  moreover have "card ({0..length m}) \<ge> card ({0..length m} \<inter> insert p1 (fset s1))" by (rule card_mono, auto)
  ultimately show ?thesis by simp
qed

end