(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
subsection \<open>Missing List\<close>

text \<open>The provides some standard algorithms and lemmas on lists.\<close>
theory Missing_List
imports 
  "../Matrix/Utility"
begin

fun concat_lists :: "'a list list \<Rightarrow> 'a list list" where
  "concat_lists [] = [[]]"
| "concat_lists (as # xs) = concat (map (\<lambda>vec. map (\<lambda>a. a # vec) as) (concat_lists xs))"

lemma concat_lists_listset: "set (concat_lists xs) = listset (map set xs)" 
  by (induct xs, auto simp: set_Cons_def)

lemma sum_list_concat: "sum_list (concat ls) = sum_list (map sum_list ls)"
  by (induct ls, auto)


(* TODO: move to src/HOL/List *)
lemma listset: "listset xs = { ys. length ys = length xs \<and> (\<forall> i < length xs. ys ! i \<in> xs ! i)}"
proof (induct xs)
  case (Cons x xs)
  let ?n = "length xs" 
  from Cons 
  have "?case = (set_Cons x {ys. length ys = ?n \<and> (\<forall>i < ?n. ys ! i \<in> xs ! i)} =
    {ys. length ys = Suc ?n \<and> ys ! 0 \<in> x \<and> (\<forall>i < ?n. ys ! Suc i \<in> xs ! i)})" 
    (is "_ = (?L = ?R)")
    by (auto simp: all_Suc_conv)
  also have "?L = ?R"
    by (auto simp: set_Cons_def, case_tac xa, auto)
  finally show ?case by simp
qed auto

lemma set_concat_lists[simp]: "set (concat_lists xs) = {as. length as = length xs \<and> (\<forall>i<length xs. as ! i \<in> set (xs ! i))}"
  unfolding concat_lists_listset listset by simp

declare concat_lists.simps[simp del]

fun find_map_filter :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b option" where
  "find_map_filter f p [] = None"
| "find_map_filter f p (a # as) = (let b = f a in if p b then Some b else find_map_filter f p as)"

lemma find_map_filter_Some: "find_map_filter f p as = Some b \<Longrightarrow> p b \<and> b \<in> f ` set as"
  by (induct f p as rule: find_map_filter.induct, auto simp: Let_def split: if_splits)

lemma find_map_filter_None: "find_map_filter f p as = None \<Longrightarrow> \<forall> b \<in> f ` set as. \<not> p b"
  by (induct f p as rule: find_map_filter.induct, auto simp: Let_def split: if_splits)

lemma remdups_adj_sorted_distinct[simp]: "sorted xs \<Longrightarrow> distinct (remdups_adj xs)"
proof (induct xs rule: sorted.induct)
  case (Cons xs x) note oCons = this
  show ?case 
  proof (cases xs)
    case (Cons y ys)
    with oCons have "x \<le> y" by auto
    show ?thesis
    proof (cases "x = y")
      case True
      with oCons Cons show ?thesis by auto
    next
      case False
      with `x \<le> y` have "x < y" by auto      
      with oCons Cons have id: "remdups_adj (x # xs) = x # remdups_adj xs" by auto
      {
        assume "x \<in> set xs" 
        with `sorted xs` have "y \<le> x" unfolding Cons by (cases, auto)
        with `x < y` have False by auto
      }
      thus ?thesis using oCons(3) unfolding id by auto
    qed
  qed simp
qed simp

lemma subseqs_length_simple:
  assumes "b \<in> set (subseqs xs)" shows "length b \<le> length xs"
  using assms by(induct xs arbitrary:b;auto simp:Let_def Suc_leD)

lemma subseqs_length_simple_False:
  assumes "b \<in> set (subseqs xs)" " length xs < length b" shows False
  using assms subseqs_length_simple by fastforce

lemma empty_subseqs[simp]: "[] \<in> set (subseqs xs)" by (induct xs, auto simp: Let_def)

lemma full_list_subseqs: "{ys. ys \<in> set (subseqs xs) \<and> length ys = length xs} = {xs}" 
proof (induct xs)
  case (Cons x xs)
  have "?case = ({ys \<in> op # x ` set (subseqs xs) \<union> set (subseqs xs). 
    length ys = Suc (length xs)} = op # x ` {xs})" (is "_ = (?l = ?r)")
    by (auto simp: Let_def)
  also have "?l = {ys \<in> op # x ` set (subseqs xs). length ys = Suc (length xs)}" 
    using length_subseqs[of xs]
    using subseqs_length_simple_False by force
  also have "\<dots> = op # x ` {ys \<in> set (subseqs xs). length ys = length xs}"
    by auto
  also have "\<dots> = op # x ` {xs}" unfolding Cons by auto
  finally show ?case by simp
qed simp

lemma nth_concat_split: assumes "i < length (concat xs)" 
  shows "\<exists> j k. j < length xs \<and> k < length (xs ! j) \<and> concat xs ! i = xs ! j ! k"
  using assms
proof (induct xs arbitrary: i)
  case (Cons x xs i)
  define I where "I = i - length x" 
  show ?case 
  proof (cases "i < length x")
    case True note l = this
    hence i: "concat (Cons x xs) ! i = x ! i" by (auto simp: nth_append)
    show ?thesis unfolding i
      by (rule exI[of _ 0], rule exI[of _ i], insert Cons l, auto)
  next
    case False note l = this
    from l Cons(2) have i: "i = length x + I" "I < length (concat xs)" unfolding I_def by auto
    hence iI: "concat (Cons x xs) ! i = concat xs ! I" by (auto simp: nth_append)
    from Cons(1)[OF i(2)] obtain j k where
      IH: "j < length xs \<and> k < length (xs ! j) \<and> concat xs ! I = xs ! j ! k" by auto
    show ?thesis unfolding iI
      by (rule exI[of _ "Suc j"], rule exI[of _ k], insert IH, auto)
  qed
qed simp

lemma nth_concat_diff: assumes "i1 < length (concat xs)" "i2 < length (concat xs)" "i1 \<noteq> i2"
  shows "\<exists> j1 k1 j2 k2. (j1,k1) \<noteq> (j2,k2) \<and> j1 < length xs \<and> j2 < length xs
    \<and> k1 < length (xs ! j1) \<and> k2 < length (xs ! j2) 
    \<and> concat xs ! i1 = xs ! j1 ! k1 \<and> concat xs ! i2 = xs ! j2 ! k2"
  using assms
proof (induct xs arbitrary: i1 i2)
  case (Cons x xs)
  define I1 where "I1 = i1 - length x" 
  define I2 where "I2 = i2 - length x" 
  show ?case 
  proof (cases "i1 < length x")
    case True note l1 = this
    hence i1: "concat (Cons x xs) ! i1 = x ! i1" by (auto simp: nth_append)
    show ?thesis
    proof (cases "i2 < length x")
      case True note l2 = this
      hence i2: "concat (Cons x xs) ! i2 = x ! i2" by (auto simp: nth_append)
      show ?thesis unfolding i1 i2 
        by (rule exI[of _ 0], rule exI[of _ i1], rule exI[of _ 0], rule exI[of _ i2], 
         insert Cons(4) l1 l2, auto)
    next
      case False note l2 = this
      from l2 Cons(3) have i22: "i2 = length x + I2" "I2 < length (concat xs)" unfolding I2_def by auto
      hence i2: "concat (Cons x xs) ! i2 = concat xs ! I2" by (auto simp: nth_append)
      from nth_concat_split[OF i22(2)] obtain j2 k2 where
        *: "j2 < length xs \<and> k2 < length (xs ! j2) \<and> concat xs ! I2 = xs ! j2 ! k2" by auto
      show ?thesis unfolding i1 i2
        by (rule exI[of _ 0], rule exI[of _ i1], rule exI[of _ "Suc j2"], rule exI[of _ k2],
         insert * l1, auto)
    qed
  next
    case False note l1 = this
    from l1 Cons(2) have i11: "i1 = length x + I1" "I1 < length (concat xs)" unfolding I1_def by auto
    hence i1: "concat (Cons x xs) ! i1 = concat xs ! I1" by (auto simp: nth_append)
    show ?thesis
    proof (cases "i2 < length x")
      case False note l2 = this
      from l2 Cons(3) have i22: "i2 = length x + I2" "I2 < length (concat xs)" unfolding I2_def by auto
      hence i2: "concat (Cons x xs) ! i2 = concat xs ! I2" by (auto simp: nth_append)
      from Cons(4) i11 i22 have diff: "I1 \<noteq> I2" by auto
      from Cons(1)[OF i11(2) i22(2) diff] obtain j1 k1 j2 k2
        where IH: "(j1,k1) \<noteq> (j2,k2) \<and> j1 < length xs \<and> j2 < length xs
        \<and> k1 < length (xs ! j1) \<and> k2 < length (xs ! j2) 
        \<and> concat xs ! I1 = xs ! j1 ! k1 \<and> concat xs ! I2 = xs ! j2 ! k2" by auto
      show ?thesis unfolding i1 i2 
        by (rule exI[of _ "Suc j1"], rule exI[of _ k1], rule exI[of _ "Suc j2"], rule exI[of _ k2],
        insert IH, auto)
    next
      case True note l2 = this
      hence i2: "concat (Cons x xs) ! i2 = x ! i2" by (auto simp: nth_append)
      from nth_concat_split[OF i11(2)] obtain j1 k1 where
        *: "j1 < length xs \<and> k1 < length (xs ! j1) \<and> concat xs ! I1 = xs ! j1 ! k1" by auto
      show ?thesis unfolding i1 i2
        by (rule exI[of _ "Suc j1"], rule exI[of _ k1], rule exI[of _ 0], rule exI[of _ i2],
         insert * l2, auto)
    qed
  qed      
qed auto

lemma list_all2_map_map: "(\<And> x. x \<in> set xs \<Longrightarrow> R (f x) (g x)) \<Longrightarrow> list_all2 R (map f xs) (map g xs)"
  by (induct xs, auto)


end
