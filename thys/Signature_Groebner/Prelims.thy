(* Author: Alexander Maletzky *)

section \<open>Preliminaries\<close>

theory Prelims
  imports Polynomials.Utils Groebner_Bases.General
begin

subsection \<open>Lists\<close>

subsubsection \<open>Sequences of Lists\<close>

lemma list_seq_length_mono:
  fixes seq :: "nat \<Rightarrow> 'a list"
  assumes "\<And>i. (\<exists>x. seq (Suc i) = x # seq i)" and "i < j"
  shows "length (seq i) < length (seq j)"
proof -
  from assms(2) obtain k where "j = Suc (i + k)" using less_iff_Suc_add by auto
  show ?thesis unfolding \<open>j = Suc (i + k)\<close>
  proof (induct k)
    case 0
    from assms(1) obtain x where eq: "seq (Suc i) = x # seq i" ..
    show ?case by (simp add: eq)
  next
    case (Suc k)
    from assms(1) obtain x where "seq (Suc (i + Suc k)) = x # seq (i + Suc k)" ..
    hence eq: "seq (Suc (Suc (i + k))) = x # seq (Suc (i + k))" by simp
    note Suc
    also have "length (seq (Suc (i + k))) < length (seq (Suc (i + Suc k)))" by (simp add: eq)
    finally show ?case .
  qed
qed

corollary list_seq_length_mono_weak:
  fixes seq :: "nat \<Rightarrow> 'a list"
  assumes "\<And>i. (\<exists>x. seq (Suc i) = x # seq i)" and "i \<le> j"
  shows "length (seq i) \<le> length (seq j)"
proof (cases "i = j")
  case True
  thus ?thesis by simp
next
  case False
  with assms(2) have "i < j" by simp
  with assms(1) have "length (seq i) < length (seq j)" by (rule list_seq_length_mono)
  thus ?thesis by simp
qed

lemma list_seq_indexE_length:
  fixes seq :: "nat \<Rightarrow> 'a list"
  assumes "\<And>i. (\<exists>x. seq (Suc i) = x # seq i)"
  obtains j where "i < length (seq j)"
proof (induct i arbitrary: thesis)
  case 0
  have "0 \<le> length (seq 0)" by simp
  also from assms lessI have "... < length (seq (Suc 0))" by (rule list_seq_length_mono)
  finally show ?case by (rule 0)
next
  case (Suc i)
  obtain j where "i < length (seq j)" by (rule Suc(1))
  hence "Suc i \<le> length (seq j)" by simp
  also from assms lessI have "... < length (seq (Suc j))" by (rule list_seq_length_mono)
  finally show ?case by (rule Suc(2))
qed

lemma list_seq_nth:
  fixes seq :: "nat \<Rightarrow> 'a list"
  assumes "\<And>i. (\<exists>x. seq (Suc i) = x # seq i)" and "i < length (seq j)" and "j \<le> k"
  shows "rev (seq k) ! i = rev (seq j) ! i"
proof -
  from assms(3) obtain l where "k = j + l" using nat_le_iff_add by blast
  show ?thesis unfolding \<open>k = j + l\<close>
  proof (induct l)
    case 0
    show ?case by simp
  next
    case (Suc l)
    note assms(2)
    also from assms(1) le_add1 have "length (seq j) \<le> length (seq (j + l))"
      by (rule list_seq_length_mono_weak)
    finally have i: "i < length (seq (j + l))" .
    from assms(1) obtain x where "seq (Suc (j + l)) = x # seq (j + l)" ..
    thus ?case by (simp add: nth_append i Suc)
  qed
qed

corollary list_seq_nth':
  fixes seq :: "nat \<Rightarrow> 'a list"
  assumes "\<And>i. (\<exists>x. seq (Suc i) = x # seq i)" and "i < length (seq j)" and "i < length (seq k)"
  shows "rev (seq k) ! i = rev (seq j) ! i"
proof (rule linorder_cases)
  assume "j < k"
  hence "j \<le> k" by simp
  with assms(1, 2) show ?thesis by (rule list_seq_nth)
next
  assume "k < j"
  hence "k \<le> j" by simp
  with assms(1, 3) have "rev (seq j) ! i = rev (seq k) ! i" by (rule list_seq_nth)
  thus ?thesis by (rule HOL.sym)
next
  assume "j = k"
  thus ?thesis by simp
qed

subsubsection \<open>@{const filter}\<close>

lemma filter_merge_wrt_1:
  assumes "\<And>y. y \<in> set ys \<Longrightarrow> P y \<Longrightarrow> False"
  shows "filter P (merge_wrt rel xs ys) = filter P xs"
  using assms
proof (induct rel xs ys rule: merge_wrt.induct)
  case (1 rel xs)
  show ?case by simp
next
  case (2 rel y ys)
  hence "P y \<Longrightarrow> False" and "\<And>z. z \<in> set ys \<Longrightarrow> P z \<Longrightarrow> False" by auto
  thus ?case by (auto simp: filter_empty_conv)
next
  case (3 rel x xs y ys)
  hence "\<not> P y" and x: "\<And>z. z \<in> set ys \<Longrightarrow> P z \<Longrightarrow> False" by auto
  have a: "filter P (merge_wrt rel xs ys) = filter P xs" if "x = y" using that x by (rule 3(1))
  have b: "filter P (merge_wrt rel xs (y # ys)) = filter P xs" if "x \<noteq> y" and "rel x y"
    using that 3(4) by (rule 3(2))
  have c: "filter P (merge_wrt rel (x # xs) ys) = filter P (x # xs)" if "x \<noteq> y" and "\<not> rel x y"
    using that x by (rule 3(3))
  show ?case by (simp add: a b c \<open>\<not> P y\<close>)
qed

lemma filter_merge_wrt_2:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> P x \<Longrightarrow> False"
  shows "filter P (merge_wrt rel xs ys) = filter P ys"
  using assms
proof (induct rel xs ys rule: merge_wrt.induct)
  case (1 rel xs)
  thus ?case by (auto simp: filter_empty_conv)
next
  case (2 rel y ys)
  show ?case by simp
next
  case (3 rel x xs y ys)
  hence "\<not> P x" and x: "\<And>z. z \<in> set xs \<Longrightarrow> P z \<Longrightarrow> False" by auto
  have a: "filter P (merge_wrt rel xs ys) = filter P ys" if "x = y" using that x by (rule 3(1))
  have b: "filter P (merge_wrt rel xs (y # ys)) = filter P (y # ys)" if "x \<noteq> y" and "rel x y"
    using that x by (rule 3(2))
  have c: "filter P (merge_wrt rel (x # xs) ys) = filter P ys" if "x \<noteq> y" and "\<not> rel x y"
    using that 3(4) by (rule 3(3))
  show ?case by (simp add: a b c \<open>\<not> P x\<close>)
qed

lemma length_filter_le_1:
  assumes "length (filter P xs) \<le> 1" and "i < length xs" and "j < length xs"
    and "P (xs ! i)" and "P (xs ! j)"
  shows "i = j"
proof -
  have *: thesis if "a < b" and "b < length xs"
    and "\<And>as bs cs. as @ ((xs ! a) # (bs @ ((xs ! b) # cs))) = xs \<Longrightarrow> thesis" for a b thesis
  proof (rule that(3))
    from that(1, 2) have 1: "a < length xs" by simp
    with that(1, 2) have 2: "b - Suc a < length (drop (Suc a) xs)" by simp
    from that(1) \<open>a < length xs\<close> have eq: "xs ! b = drop (Suc a) xs ! (b - Suc a)" by simp
    show "(take a xs) @ ((xs ! a) # ((take (b - Suc a) (drop (Suc a) xs)) @ ((xs ! b) #
                  drop (Suc (b - Suc a)) (drop (Suc a) xs)))) = xs"
      by (simp only: eq id_take_nth_drop[OF 1, symmetric] id_take_nth_drop[OF 2, symmetric])
  qed
  show ?thesis
  proof (rule linorder_cases)
    assume "i < j"
    then obtain as bs cs where "as @ ((xs ! i) # (bs @ ((xs ! j) # cs))) = xs"
      using assms(3) by (rule *)
    hence "filter P xs = filter P (as @ ((xs ! i) # (bs @ ((xs ! j) # cs))))" by simp
    also from assms(4, 5) have "... = (filter P as) @ ((xs ! i) # ((filter P bs) @ ((xs ! j) # (filter P cs))))"
      by simp
    finally have "\<not> length (filter P xs) \<le> 1" by simp
    thus ?thesis using assms(1) ..
  next
    assume "j < i"
    then obtain as bs cs where "as @ ((xs ! j) # (bs @ ((xs ! i) # cs))) = xs"
      using assms(2) by (rule *)
    hence "filter P xs = filter P (as @ ((xs ! j) # (bs @ ((xs ! i) # cs))))" by simp
    also from assms(4, 5) have "... = (filter P as) @ ((xs ! j) # ((filter P bs) @ ((xs ! i) # (filter P cs))))"
      by simp
    finally have "\<not> length (filter P xs) \<le> 1" by simp
    thus ?thesis using assms(1) ..
  qed
qed

lemma length_filter_eq [simp]: "length (filter ((=) x) xs) = count_list xs x"
  by (induct xs, simp_all)

subsubsection \<open>@{const drop}\<close>

lemma nth_in_set_dropI:
  assumes "j \<le> i" and "i < length xs"
  shows "xs ! i \<in> set (drop j xs)"
  using assms
proof (induct xs arbitrary: i j)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases j)
    case 0
    with Cons(3) show ?thesis by (metis drop0 nth_mem)
  next
    case (Suc j0)
    with Cons(2) Suc_le_D obtain i0 where i: "i = Suc i0" by blast
    with Cons(2) have "j0 \<le> i0" by (simp add: \<open>j = Suc j0\<close>)
    moreover from Cons(3) have "i0 < length xs" by (simp add: i)
    ultimately have "xs ! i0 \<in> set (drop j0 xs)" by (rule Cons(1))
    thus ?thesis by (simp add: i \<open>j = Suc j0\<close>)
  qed
qed

subsubsection \<open>@{const count_list}\<close>

lemma count_list_append [simp]: "count_list (xs @ ys) a = count_list xs a + count_list ys a"
  by (induct xs, simp_all)

lemma count_list_upt [simp]: "count_list [a..<b] x = (if a \<le> x \<and> x < b then 1 else 0)"
proof (cases "a \<le> b")
  case True
  then obtain k where "b = a + k" using le_Suc_ex by blast
  show ?thesis unfolding \<open>b = a + k\<close> by (induct k, simp_all)
next
  case False
  thus ?thesis by simp
qed

subsubsection \<open>@{const sorted_wrt}\<close>

lemma sorted_wrt_upt_iff: "sorted_wrt rel [a..<b] \<longleftrightarrow> (\<forall>i j. a \<le> i \<longrightarrow> i < j \<longrightarrow> j < b \<longrightarrow> rel i j)"
proof (cases "a \<le> b")
  case True
  then obtain k where "b = a + k" using le_Suc_ex by blast
  show ?thesis unfolding \<open>b = a + k\<close>
  proof (induct k)
    case 0
    show ?case by simp
  next
    case (Suc k)
    show ?case
    proof (simp add: sorted_wrt_append Suc, intro iffI allI ballI impI conjI)
      fix i j
      assume "(\<forall>i\<ge>a. \<forall>j>i. j < a + k \<longrightarrow> rel i j) \<and> (\<forall>x\<in>{a..<a + k}. rel x (a + k))"
      hence 1: "\<And>i' j'. a \<le> i' \<Longrightarrow> i' < j' \<Longrightarrow> j' < a + k \<Longrightarrow> rel i' j'"
        and 2: "\<And>x. a \<le> x \<Longrightarrow> x < a + k \<Longrightarrow> rel x (a + k)" by simp_all
      assume "a \<le> i" and "i < j"
      assume "j < Suc (a + k)"
      hence "j < a + k \<or> j = a + k" by auto
      thus "rel i j"
      proof
        assume "j < a + k"
        with \<open>a \<le> i\<close> \<open>i < j\<close> show ?thesis by (rule 1)
      next
        assume "j = a + k"
        from \<open>a \<le> i\<close> \<open>i < j\<close> show ?thesis unfolding \<open>j = a + k\<close> by (rule 2)
      qed
    next
      fix i j
      assume "\<forall>i\<ge>a. \<forall>j>i. j < Suc (a + k) \<longrightarrow> rel i j" and "a \<le> i" and "i < j" and "j < a + k"
      thus "rel i j" by simp
    next
      fix x
      assume "x \<in> {a..<a + k}"
      hence "a \<le> x" and "x < a + k" by simp_all
      moreover assume "\<forall>i\<ge>a. \<forall>j>i. j < Suc (a + k) \<longrightarrow> rel i j"
      ultimately show "rel x (a + k)" by simp
    qed
  qed
next
  case False
  thus ?thesis by simp
qed

subsubsection \<open>@{const insort_wrt} and @{const merge_wrt}\<close>

lemma map_insort_wrt:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> r2 (f y) (f x) \<longleftrightarrow> r1 y x"
  shows "map f (insort_wrt r1 y xs) = insort_wrt r2 (f y) (map f xs)"
  using assms
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  have "x \<in> set (x # xs)" by simp
  hence "r2 (f y) (f x) = r1 y x" by (rule Cons(2))
  moreover have "map f (insort_wrt r1 y xs) = insort_wrt r2 (f y) (map f xs)"
  proof (rule Cons(1))
    fix x'
    assume "x' \<in> set xs"
    hence "x' \<in> set (x # xs)" by simp
    thus "r2 (f y) (f x') = r1 y x'" by (rule Cons(2))
  qed
  ultimately show ?case by simp
qed

lemma map_merge_wrt:
  assumes "f ` set xs \<inter> f ` set ys = {}"
    and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> r2 (f x) (f y) \<longleftrightarrow> r1 x y"
  shows "map f (merge_wrt r1 xs ys) = merge_wrt r2 (map f xs) (map f ys)"
  using assms
proof (induct r1 xs ys rule: merge_wrt.induct)
  case (1 uu xs)
  show ?case by simp
next
  case (2 r1 v va)
  show ?case by simp
next
  case (3 r1 x xs y ys)
  from 3(4) have "f x \<noteq> f y" and 1: "f ` set xs \<inter> f ` set (y # ys) = {}"
    and 2: "f ` set (x # xs) \<inter> f ` set ys = {}" by auto
  from this(1) have "x \<noteq> y" by auto
  have eq2: "map f (merge_wrt r1 xs (y # ys)) = merge_wrt r2 (map f xs) (map f (y # ys))"
    if "r1 x y" using \<open>x \<noteq> y\<close> that 1
  proof (rule 3(2))
    fix a b
    assume "a \<in> set xs"
    hence "a \<in> set (x # xs)" by simp
    moreover assume "b \<in> set (y # ys)"
    ultimately show "r2 (f a) (f b) \<longleftrightarrow> r1 a b" by (rule 3(5))
  qed
  have eq3: "map f (merge_wrt r1 (x # xs) ys) = merge_wrt r2 (map f (x # xs)) (map f ys)"
    if "\<not> r1 x y" using \<open>x \<noteq> y\<close> that 2
  proof (rule 3(3))
    fix a b
    assume "a \<in> set (x # xs)"
    assume "b \<in> set ys"
    hence "b \<in> set (y # ys)" by simp
    with \<open>a \<in> set (x # xs)\<close> show "r2 (f a) (f b) \<longleftrightarrow> r1 a b" by (rule 3(5))
  qed
  have eq4: "r2 (f x) (f y) \<longleftrightarrow> r1 x y" by (rule 3(5), simp_all)
  show ?case by (simp add: eq2 eq3 eq4 \<open>f x \<noteq> f y\<close> \<open>x \<noteq> y\<close>)
qed

subsubsection \<open>Filtering Minimal Elements\<close>

context
  fixes rel :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

primrec filter_min_aux :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "filter_min_aux [] ys = ys"|
  "filter_min_aux (x # xs) ys =
    (if (\<exists>y\<in>(set xs \<union> set ys). rel y x) then (filter_min_aux xs ys)
    else (filter_min_aux xs (x # ys)))"

definition filter_min :: "'a list \<Rightarrow> 'a list"
  where "filter_min xs = filter_min_aux xs []"

definition filter_min_append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "filter_min_append xs ys =
                  (let P = (\<lambda>zs. \<lambda>x. \<not> (\<exists>z\<in>set zs. rel z x)); ys1 = filter (P xs) ys in
                    (filter (P ys1) xs) @ ys1)"
  
lemma filter_min_aux_supset: "set ys \<subseteq> set (filter_min_aux xs ys)"
proof (induct xs arbitrary: ys)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  have "set ys \<subseteq> set (x # ys)" by auto
  also have "set (x # ys) \<subseteq> set (filter_min_aux xs (x # ys))" by (rule Cons.hyps)
  finally have "set ys \<subseteq> set (filter_min_aux xs (x # ys))" .
  moreover have "set ys \<subseteq> set (filter_min_aux xs ys)" by (rule Cons.hyps)
  ultimately show ?case by simp
qed
    
lemma filter_min_aux_subset: "set (filter_min_aux xs ys) \<subseteq> set xs \<union> set ys"
proof (induct xs arbitrary: ys)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  note Cons.hyps
  also have "set xs \<union> set ys \<subseteq> set (x # xs) \<union> set ys" by fastforce
  finally have c1: "set (filter_min_aux xs ys) \<subseteq> set (x # xs) \<union> set ys" .
  
  note Cons.hyps
  also have "set xs \<union> set (x # ys) = set (x # xs) \<union> set ys" by simp
  finally have "set (filter_min_aux xs (x # ys)) \<subseteq> set (x # xs) \<union> set ys" .
  with c1 show ?case by simp
qed

lemma filter_min_aux_relE:
  assumes "transp rel" and "x \<in> set xs" and "x \<notin> set (filter_min_aux xs ys)"
  obtains y where "y \<in> set (filter_min_aux xs ys)" and "rel y x"
  using assms(2, 3)
proof (induct xs arbitrary: x ys thesis)
  case Nil
  from Nil(2) show ?case by simp
next
  case (Cons x0 xs)
  from Cons(3) have "x = x0 \<or> x \<in> set xs" by simp
  thus ?case
  proof
    assume "x = x0"
    from Cons(4) have *: "\<exists>y\<in>set xs \<union> set ys. rel y x0"
    proof (simp add: \<open>x = x0\<close> split: if_splits)
      assume "x0 \<notin> set (filter_min_aux xs (x0 # ys))"
      moreover from filter_min_aux_supset have "x0 \<in> set (filter_min_aux xs (x0 # ys))"
        by (rule subsetD) simp
      ultimately show False ..
    qed
    hence eq: "filter_min_aux (x0 # xs) ys = filter_min_aux xs ys" by simp
    from * obtain x1 where "x1 \<in> set xs \<union> set ys" and "rel x1 x" unfolding \<open>x = x0\<close> ..
    from this(1) show ?thesis
    proof
      assume "x1 \<in> set xs"
      show ?thesis
      proof (cases "x1 \<in> set (filter_min_aux xs ys)")
        case True
        hence "x1 \<in> set (filter_min_aux (x0 # xs) ys)" by (simp only: eq)
        thus ?thesis using \<open>rel x1 x\<close> by (rule Cons(2))
      next
        case False
        with \<open>x1 \<in> set xs\<close> obtain y where "y \<in> set (filter_min_aux xs ys)" and "rel y x1"
          using Cons.hyps by blast
        from this(1) have "y \<in> set (filter_min_aux (x0 # xs) ys)" by (simp only: eq)
        moreover from assms(1) \<open>rel y x1\<close> \<open>rel x1 x\<close> have "rel y x" by (rule transpD)
        ultimately show ?thesis by (rule Cons(2))
      qed
    next
      assume "x1 \<in> set ys"
      hence "x1 \<in> set (filter_min_aux (x0 # xs) ys)" using filter_min_aux_supset ..
      thus ?thesis using \<open>rel x1 x\<close> by (rule Cons(2))
    qed
  next
    assume "x \<in> set xs"
    show ?thesis
    proof (cases "\<exists>y\<in>set xs \<union> set ys. rel y x0")
      case True
      hence eq: "filter_min_aux (x0 # xs) ys = filter_min_aux xs ys" by simp
      with Cons(4) have "x \<notin> set (filter_min_aux xs ys)" by simp
      with \<open>x \<in> set xs\<close> obtain y where "y \<in> set (filter_min_aux xs ys)" and "rel y x"
        using Cons.hyps by blast
      from this(1) have "y \<in> set (filter_min_aux (x0 # xs) ys)" by (simp only: eq)
      thus ?thesis using \<open>rel y x\<close> by (rule Cons(2))
    next
      case False
      hence eq: "filter_min_aux (x0 # xs) ys = filter_min_aux xs (x0 # ys)" by simp
      with Cons(4) have "x \<notin> set (filter_min_aux xs (x0 # ys))" by simp
      with \<open>x \<in> set xs\<close> obtain y where "y \<in> set (filter_min_aux xs (x0 # ys))" and "rel y x"
        using Cons.hyps by blast
      from this(1) have "y \<in> set (filter_min_aux (x0 # xs) ys)" by (simp only: eq)
      thus ?thesis using \<open>rel y x\<close> by (rule Cons(2))
    qed
  qed
qed

lemma filter_min_aux_minimal:
  assumes "transp rel" and "x \<in> set (filter_min_aux xs ys)" and "y \<in> set (filter_min_aux xs ys)"
    and "rel x y"
  assumes "\<And>a b. a \<in> set xs \<union> set ys \<Longrightarrow> b \<in> set ys \<Longrightarrow> rel a b \<Longrightarrow> a = b"
  shows "x = y"
  using assms(2-5)
proof (induct xs arbitrary: x y ys)
  case Nil
  from Nil(1) have "x \<in> set [] \<union> set ys" by simp
  moreover from Nil(2) have "y \<in> set ys" by simp
  ultimately show ?case using Nil(3) by (rule Nil(4))
next
  case (Cons x0 xs)
  show ?case
  proof (cases "\<exists>y\<in>set xs \<union> set ys. rel y x0")
    case True
    hence eq: "filter_min_aux (x0 # xs) ys = filter_min_aux xs ys" by simp
    with Cons(2, 3) have "x \<in> set (filter_min_aux xs ys)" and "y \<in> set (filter_min_aux xs ys)"
      by simp_all
    thus ?thesis using Cons(4)
    proof (rule Cons.hyps)
      fix a b
      assume "a \<in> set xs \<union> set ys"
      hence "a \<in> set (x0 # xs) \<union> set ys" by simp
      moreover assume "b \<in> set ys" and "rel a b"
      ultimately show "a = b" by (rule Cons(5))
    qed
  next
    case False
    hence eq: "filter_min_aux (x0 # xs) ys = filter_min_aux xs (x0 # ys)" by simp
    with Cons(2, 3) have "x \<in> set (filter_min_aux xs (x0 # ys))" and "y \<in> set (filter_min_aux xs (x0 # ys))"
      by simp_all
    thus ?thesis using Cons(4)
    proof (rule Cons.hyps)
      fix a b
      assume a: "a \<in> set xs \<union> set (x0 # ys)" and "b \<in> set (x0 # ys)" and "rel a b"
      from this(2) have "b = x0 \<or> b \<in> set ys" by simp
      thus "a = b"
      proof
        assume "b = x0"
        from a have "a = x0 \<or> a \<in> set xs \<union> set ys" by simp
        thus ?thesis
        proof
          assume "a = x0"
          with \<open>b = x0\<close> show ?thesis by simp
        next
          assume "a \<in> set xs \<union> set ys"
          hence "\<exists>y\<in>set xs \<union> set ys. rel y x0" using \<open>rel a b\<close> unfolding \<open>b = x0\<close> ..
          with False show ?thesis ..
        qed
      next
        from a have "a \<in> set (x0 # xs) \<union> set ys" by simp
        moreover assume "b \<in> set ys"
        ultimately show ?thesis using \<open>rel a b\<close> by (rule Cons(5))
      qed
    qed
  qed
qed
  
lemma filter_min_aux_distinct:
  assumes "reflp rel" and "distinct ys"
  shows "distinct (filter_min_aux xs ys)"
  using assms(2)
proof (induct xs arbitrary: ys)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (simp split: if_split, intro conjI impI)
    from Cons(2) show "distinct (filter_min_aux xs ys)" by (rule Cons.hyps)
  next
    assume a: "\<forall>y\<in>set xs \<union> set ys. \<not> rel y x"
    show "distinct (filter_min_aux xs (x # ys))"
    proof (rule Cons.hyps)
      have "x \<notin> set ys"
      proof
        assume "x \<in> set ys"
        hence "x \<in> set xs \<union> set ys" by simp
        with a have "\<not> rel x x" ..
        moreover from assms(1) have "rel x x" by (rule reflpD)
        ultimately show False ..
      qed
      with Cons(2) show "distinct (x # ys)" by simp
    qed
  qed
qed

lemma filter_min_subset: "set (filter_min xs) \<subseteq> set xs"
  using filter_min_aux_subset[of xs "[]"] by (simp add: filter_min_def)

lemma filter_min_cases:
  assumes "transp rel" and "x \<in> set xs"
  assumes "x \<in> set (filter_min xs) \<Longrightarrow> thesis"
  assumes "\<And>y. y \<in> set (filter_min xs) \<Longrightarrow> x \<notin> set (filter_min xs) \<Longrightarrow> rel y x \<Longrightarrow> thesis"
  shows thesis
proof (cases "x \<in> set (filter_min xs)")
  case True
  thus ?thesis by (rule assms(3))
next
  case False
  with assms(1, 2) obtain y where "y \<in> set (filter_min xs)" and "rel y x"
    unfolding filter_min_def by (rule filter_min_aux_relE)
  from this(1) False this(2) show ?thesis by (rule assms(4))
qed

corollary filter_min_relE:
  assumes "transp rel" and "reflp rel" and "x \<in> set xs"
  obtains y where "y \<in> set (filter_min xs)" and "rel y x"
  using assms(1, 3)
proof (rule filter_min_cases)
  assume "x \<in> set (filter_min xs)"
  moreover from assms(2) have "rel x x" by (rule reflpD)
  ultimately show ?thesis ..
qed

lemma filter_min_minimal:
  assumes "transp rel" and "x \<in> set (filter_min xs)" and "y \<in> set (filter_min xs)" and "rel x y"
  shows "x = y"
  using assms unfolding filter_min_def by (rule filter_min_aux_minimal) simp

lemma filter_min_distinct:
  assumes "reflp rel"
  shows "distinct (filter_min xs)"
  unfolding filter_min_def by (rule filter_min_aux_distinct, fact, simp)

lemma filter_min_append_subset: "set (filter_min_append xs ys) \<subseteq> set xs \<union> set ys"
  by (auto simp: filter_min_append_def)

lemma filter_min_append_cases:
  assumes "transp rel" and "x \<in> set xs \<union> set ys"
  assumes "x \<in> set (filter_min_append xs ys) \<Longrightarrow> thesis"
  assumes "\<And>y. y \<in> set (filter_min_append xs ys) \<Longrightarrow> x \<notin> set (filter_min_append xs ys) \<Longrightarrow> rel y x \<Longrightarrow> thesis"
  shows thesis
proof (cases "x \<in> set (filter_min_append xs ys)")
  case True
  thus ?thesis by (rule assms(3))
next
  case False
  define P where "P = (\<lambda>zs. \<lambda>a. \<not> (\<exists>z\<in>set zs. rel z a))"
  from assms(2) obtain y where "y \<in> set (filter_min_append xs ys)" and "rel y x"
  proof
    assume "x \<in> set xs"
    with False obtain y where "y \<in> set (filter_min_append xs ys)" and "rel y x"
      by (auto simp: filter_min_append_def P_def)
    thus ?thesis ..
  next
    assume "x \<in> set ys"
    with False obtain y where "y \<in> set xs" and "rel y x"
      by (auto simp: filter_min_append_def P_def)
    show ?thesis
    proof (cases "y \<in> set (filter_min_append xs ys)")
      case True
      thus ?thesis using \<open>rel y x\<close> ..
    next
      case False
      with \<open>y \<in> set xs\<close> obtain y' where y': "y' \<in> set (filter_min_append xs ys)" and "rel y' y"
        by (auto simp: filter_min_append_def P_def)
      from assms(1) this(2) \<open>rel y x\<close> have "rel y' x" by (rule transpD)
      with y' show ?thesis ..
    qed
  qed
  from this(1) False this(2) show ?thesis by (rule assms(4))
qed

corollary filter_min_append_relE:
  assumes "transp rel" and "reflp rel" and "x \<in> set xs \<union> set ys"
  obtains y where "y \<in> set (filter_min_append xs ys)" and "rel y x"
  using assms(1, 3)
proof (rule filter_min_append_cases)
  assume "x \<in> set (filter_min_append xs ys)"
  moreover from assms(2) have "rel x x" by (rule reflpD)
  ultimately show ?thesis ..
qed

lemma filter_min_append_minimal:
  assumes "\<And>x' y'. x' \<in> set xs \<Longrightarrow> y' \<in> set xs \<Longrightarrow> rel x' y' \<Longrightarrow> x' = y'"
    and "\<And>x' y'. x' \<in> set ys \<Longrightarrow> y' \<in> set ys \<Longrightarrow> rel x' y' \<Longrightarrow> x' = y'"
    and "x \<in> set (filter_min_append xs ys)" and "y \<in> set (filter_min_append xs ys)" and "rel x y"
  shows "x = y"
proof -
  define P where "P = (\<lambda>zs. \<lambda>a. \<not> (\<exists>z\<in>set zs. rel z a))"
  define ys1 where "ys1 = filter (P xs) ys"
  from assms(3) have "x \<in> set xs \<union> set ys1"
    by (auto simp: filter_min_append_def P_def ys1_def)
  moreover from assms(4) have "y \<in> set (filter (P ys1) xs) \<union> set ys1"
    by (simp add: filter_min_append_def P_def ys1_def)
  ultimately show ?thesis
  proof (elim UnE)
    assume "x \<in> set xs"
    assume "y \<in> set (filter (P ys1) xs)"
    hence "y \<in> set xs" by simp
    with \<open>x \<in> set xs\<close> show ?thesis using assms(5) by (rule assms(1))
  next
    assume "y \<in> set ys1"
    hence "\<And>z. z \<in> set xs \<Longrightarrow> \<not> rel z y" by (simp add: ys1_def P_def)
    moreover assume "x \<in> set xs"
    ultimately have "\<not> rel x y" by blast
    thus ?thesis using \<open>rel x y\<close> ..
  next
    assume "y \<in> set (filter (P ys1) xs)"
    hence "\<And>z. z \<in> set ys1 \<Longrightarrow> \<not> rel z y" by (simp add: P_def)
    moreover assume "x \<in> set ys1"
    ultimately have "\<not> rel x y" by blast
    thus ?thesis using \<open>rel x y\<close> ..
  next
    assume "x \<in> set ys1" and "y \<in> set ys1"
    hence "x \<in> set ys" and "y \<in> set ys" by (simp_all add: ys1_def)
    thus ?thesis using assms(5) by (rule assms(2))
  qed
qed

lemma filter_min_append_distinct:
  assumes "reflp rel" and "distinct xs" and "distinct ys"
  shows "distinct (filter_min_append xs ys)"
proof -
  define P where "P = (\<lambda>zs. \<lambda>a. \<not> (\<exists>z\<in>set zs. rel z a))"
  define ys1 where "ys1 = filter (P xs) ys"
  from assms(2) have "distinct (filter (P ys1) xs)" by simp
  moreover from assms(3) have "distinct ys1" by (simp add: ys1_def)
  moreover have "set (filter (P ys1) xs) \<inter> set ys1 = {}"
  proof (simp add: set_eq_iff, intro allI impI notI)
    fix x
    assume "P ys1 x"
    hence "\<And>z. z \<in> set ys1 \<Longrightarrow> \<not> rel z x" by (simp add: P_def)
    moreover assume "x \<in> set ys1"
    ultimately have "\<not> rel x x" by blast
    moreover from assms(1) have "rel x x" by (rule reflpD)
    ultimately show False ..
  qed
  ultimately show ?thesis by (simp add: filter_min_append_def ys1_def P_def)
qed

end

subsection \<open>Recursive Functions\<close>

locale recursive =
  fixes h' :: "'b \<Rightarrow> 'b"
  fixes b :: 'b
  assumes b_fixpoint: "h' b = b"
begin

context
  fixes Q :: "'a \<Rightarrow> bool"
  fixes g :: "'a \<Rightarrow> 'b"
  fixes h :: "'a \<Rightarrow> 'a"
begin

function (domintros) recfun_aux :: "'a \<Rightarrow> 'b" where
  "recfun_aux x = (if Q x then g x else h' (recfun_aux (h x)))"
  by pat_completeness auto

lemmas [induct del] = recfun_aux.pinduct

definition dom :: "'a \<Rightarrow> bool"
  where "dom x \<longleftrightarrow> (\<exists>k. Q ((h ^^ k) x))"

lemma domI:
  assumes "\<not> Q x \<Longrightarrow> dom (h x)"
  shows "dom x"
proof (cases "Q x")
  case True
  hence "Q ((h ^^ 0) x)" by simp
  thus ?thesis unfolding dom_def ..
next
  case False
  hence "dom (h x)" by (rule assms)
  then obtain k where "Q ((h ^^ k) (h x))" unfolding dom_def ..
  hence "Q ((h ^^ (Suc k)) x)" by (simp add: funpow_swap1)
  thus ?thesis unfolding dom_def ..
qed

lemma domD:
  assumes "dom x" and "\<not> Q x"
  shows "dom (h x)"
proof -
  from assms(1) obtain k where *: "Q ((h ^^ k) x)" unfolding dom_def ..
  with assms(2) have "k \<noteq> 0" using funpow_0 by fastforce
  then obtain m where "k = Suc m" using nat.exhaust by blast
  with * have "Q ((h ^^ m) (h x))" by (simp add: funpow_swap1)
  thus ?thesis unfolding dom_def ..
qed

lemma recfun_aux_domI:
  assumes "dom x"
  shows "recfun_aux_dom x"
proof -
  from assms obtain k where "Q ((h ^^ k) x)" unfolding dom_def ..
  thus ?thesis
  proof (induct k arbitrary: x)
    case 0
    hence "Q x" by simp
    with recfun_aux.domintros show ?case by blast
  next
    case (Suc k)
    from Suc(2) have "Q ((h ^^ k) (h x))" by (simp add: funpow_swap1)
    hence "recfun_aux_dom (h x)" by (rule Suc(1))
    with recfun_aux.domintros show ?case by blast
  qed
qed

lemma recfun_aux_domD:
  assumes "recfun_aux_dom x"
  shows "dom x"
  using assms
proof (induct x rule: recfun_aux.pinduct)
  case (1 x)
  show ?case
  proof (cases "Q x")
    case True
    with domI show ?thesis by blast
  next
    case False
    hence "dom (h x)" by (rule 1(2))
    thus ?thesis using domI by blast
  qed
qed

corollary recfun_aux_dom_alt: "recfun_aux_dom = dom"
  by (auto dest: recfun_aux_domI recfun_aux_domD)

definition "fun" :: "'a \<Rightarrow> 'b"
  where "fun x = (if recfun_aux_dom x then recfun_aux x else b)"

lemma simps: "fun x = (if Q x then g x else h' (fun (h x)))"
proof (cases "dom x")
  case True
  hence dom: "recfun_aux_dom x" by (rule recfun_aux_domI)
  show ?thesis
  proof (cases "Q x")
    case True
    with dom show ?thesis by (simp add: fun_def recfun_aux.psimps)
  next
    case False
    have "recfun_aux_dom (h x)" by (rule recfun_aux_domI, rule domD, fact True, fact False)
    thus ?thesis by (simp add: fun_def dom False recfun_aux.psimps)
  qed
next
  case False
  moreover have "\<not> Q x"
  proof
    assume "Q x"
    hence "dom x" using domI by blast
    with False show False ..
  qed
  moreover have "\<not> dom (h x)"
  proof
    assume "dom (h x)"
    hence "dom x" using domI by blast
    with False show False ..
  qed
  ultimately show ?thesis by (simp add: recfun_aux_dom_alt fun_def b_fixpoint split del: if_split)
qed

lemma eq_fixpointI: "\<not> dom x \<Longrightarrow> fun x = b"
  by (simp add: fun_def recfun_aux_dom_alt)

lemma pinduct: "dom x \<Longrightarrow> (\<And>x. dom x \<Longrightarrow> (\<not> Q x \<Longrightarrow> P (h x)) \<Longrightarrow> P x) \<Longrightarrow> P x"
  unfolding recfun_aux_dom_alt[symmetric] by (fact recfun_aux.pinduct)

end

end (* recursive *)

interpretation tailrec: recursive "\<lambda>x. x" undefined
  by (standard, fact refl)

subsection \<open>Binary Relations\<close>

lemma almost_full_on_Int:
  assumes "almost_full_on P1 A1" and "almost_full_on P2 A2"
  shows "almost_full_on (\<lambda>x y. P1 x y \<and> P2 x y) (A1 \<inter> A2)" (is "almost_full_on ?P ?A")
proof (rule almost_full_onI)
  fix f :: "nat \<Rightarrow> 'a"
  assume a: "\<forall>i. f i \<in> ?A"
  define g where "g = (\<lambda>i. (f i, f i))"
  from assms have "almost_full_on (prod_le P1 P2) (A1 \<times> A2)" by (rule almost_full_on_Sigma)
  moreover from a have "\<And>i. g i \<in> A1 \<times> A2" by (simp add: g_def)
  ultimately obtain i j where "i < j" and "prod_le P1 P2 (g i) (g j)" by (rule almost_full_onD)
  from this(2) have "?P (f i) (f j)" by (simp add: g_def prod_le_def)
  with \<open>i < j\<close> show "good ?P f" by (rule goodI)
qed

corollary almost_full_on_same:
  assumes "almost_full_on P1 A" and "almost_full_on P2 A"
  shows "almost_full_on (\<lambda>x y. P1 x y \<and> P2 x y) A"
proof -
  from assms have "almost_full_on (\<lambda>x y. P1 x y \<and> P2 x y) (A \<inter> A)" by (rule almost_full_on_Int)
  thus ?thesis by simp
qed

context ord
begin

definition is_le_rel :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "is_le_rel rel = (rel = (=) \<or> rel = (\<le>) \<or> rel = (<))"

lemma is_le_relI [simp]: "is_le_rel (=)" "is_le_rel (\<le>)" "is_le_rel (<)"
  by (simp_all add: is_le_rel_def)

lemma is_le_relE:
  assumes "is_le_rel rel"
  obtains "rel = (=)" | "rel = (\<le>)" | "rel = (<)"
  using assms unfolding is_le_rel_def by blast

end (* ord *)

context preorder
begin

lemma is_le_rel_le:
  assumes "is_le_rel rel"
  shows "rel x y \<Longrightarrow> x \<le> y"
  using assms by (rule is_le_relE, auto dest: less_imp_le)

lemma is_le_rel_trans:
  assumes "is_le_rel rel"
  shows "rel x y \<Longrightarrow> rel y z \<Longrightarrow> rel x z"
  using assms by (rule is_le_relE, auto dest: order_trans less_trans)

lemma is_le_rel_trans_le_left:
  assumes "is_le_rel rel"
  shows "x \<le> y \<Longrightarrow> rel y z \<Longrightarrow> x \<le> z"
  using assms by (rule is_le_relE, auto dest: order_trans le_less_trans less_imp_le)

lemma is_le_rel_trans_le_right:
  assumes "is_le_rel rel"
  shows "rel x y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  using assms by (rule is_le_relE, auto dest: order_trans less_le_trans less_imp_le)

lemma is_le_rel_trans_less_left:
  assumes "is_le_rel rel"
  shows "x < y \<Longrightarrow> rel y z \<Longrightarrow> x < z"
  using assms by (rule is_le_relE, auto dest: less_le_trans less_imp_le)

lemma is_le_rel_trans_less_right:
  assumes "is_le_rel rel"
  shows "rel x y \<Longrightarrow> y < z \<Longrightarrow> x < z"
  using assms by (rule is_le_relE, auto dest: le_less_trans less_imp_le)

end (* preorder *)

context order
begin

lemma is_le_rel_distinct:
  assumes "is_le_rel rel"
  shows "rel x y \<Longrightarrow> x \<noteq> y \<Longrightarrow> x < y"
  using assms by (rule is_le_relE, auto)

lemma is_le_rel_antisym:
  assumes "is_le_rel rel"
  shows "rel x y \<Longrightarrow> rel y x \<Longrightarrow> x = y"
  using assms by (rule is_le_relE, auto)

end (* order *)

end (* theory *)
