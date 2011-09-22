(*  Title:       Abstract Rewriting
    Author:      Christian Sternagel <christian.sternagel@uibk.ac.at>
                 Rene Thiemann       <rene.tiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and Rene Thiemann
    License:     LGPL
*)

(*
Copyright 2009 Christian Sternagel and René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)

header {* Util *}

theory Util
imports Main Finite_Set
  "~~/src/HOL/Library/Infinite_Set"
  "~~/src/HOL/Library/Monad_Syntax"
begin

section {* Auxiliary Lemmas *}

lemma set_not_empty: "xs \<noteq> [] \<longleftrightarrow> set xs \<noteq> {}" by simp

lemma ballI2: assumes "\<And>x y. (x,y) \<in> A \<Longrightarrow> P x y" shows "\<forall>(x,y)\<in>A. P x y"
  using assms by auto

fun
  debug :: "string \<Rightarrow> string \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "debug i t x = x"

lemma all_Suc: "(\<forall> i < Suc n. P i) = (P 0 \<and> (\<forall> i < n. P (Suc i)))" (is "?l = ?r")
proof 
  assume ?l thus ?r by auto
next
  assume ?r
  show ?l
  proof (intro allI impI)
    fix i
    assume "i < Suc n"
    with `?r` show "P i"
      by (cases i, auto)
  qed
qed

lemma ex_Suc: "(\<exists> i < Suc n. P i) = (P 0 \<or> (\<exists> i < n. P (Suc i)))" (is "?l = ?r")
  using all_Suc[of n "\<lambda> i. \<not> P i"] by blast


subsection {* Induction Rules *}

text {* Induction over a finite set of natural numbers. *}
lemma bound_nat_induct[consumes 1]:
  assumes "n \<in> {l..u}" and "P l" and "\<And>n. \<lbrakk>P n;n \<in> {l..<u}\<rbrakk> \<Longrightarrow> P(Suc n)"
  shows "P n"
using assms proof (induct n rule: nat.induct)
 case zero thus ?case by simp
next
 case (Suc n) thus ?case
 proof (cases "Suc n = l")
  case True with `P l` show ?thesis by simp
 next
  case False with Suc show ?thesis by auto
 qed
qed


subsection {* Functions on Lists *}

lemma list_all_cong[fundef_cong]: fixes xs ys f g 
  assumes "xs = ys" and "\<And>x. x \<in> set ys \<Longrightarrow> f x = g x" 
  shows "list_all f xs = list_all g ys" 
using assms by (simp add: list_all_iff)

lemma list_ex_cong[fundef_cong]: fixes xs ys f g 
  assumes "xs = ys" and "\<And>x. x \<in> set ys \<Longrightarrow> f x = g x" 
  shows "list_ex f xs = list_ex g ys" 
using assms by (simp add: list_ex_iff)

lemmas list_all_ex = list_ex_iff list_all_iff

primrec find :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a option"
where "find _ [] = None"
    | "find p (x#xs) = (if p x then Some x else find p xs)"

lemma find_NoneE: 
  assumes "find f xs = None" shows "\<not>(\<exists>x. x \<in> set xs \<and> f x)"
using assms proof (induct xs)
  case Nil show ?case by simp
next
  case (Cons x xs)
  hence "\<not>(f x)" unfolding find.simps by auto
  with Cons show ?case by auto
qed

lemma find_NoneI:
  assumes "(\<not>(\<exists>x. x \<in> set xs \<and> f x))" shows "find f xs = None"
using assms proof (induct xs)
 case Nil
 show ?case by simp
next
 case (Cons x xs)
 assume "\<not>(\<exists>y. y \<in> set (x # xs) \<and> f y)" hence "\<not> (f x)" by auto 
 with Cons show ?case by auto
qed

lemma not_mem_find_None_conv: "(\<not>(\<exists>x. x \<in> set xs \<and> f x)) = (find f xs = None)"
 using find_NoneI find_NoneE by blast

lemma find_SomeE: 
  assumes "find p xs = Some x"
  shows "\<exists>i<length xs. p(xs!i) \<and> x = (xs!i) \<and> (\<forall>j<i. \<not> p(xs!j))"
using assms proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons y ys)
  show ?case
  proof (cases "p y")
    case True with Cons show ?thesis by auto
  next
    case False with Cons have "find p ys = Some x" by simp
    with Cons have "\<exists>i<length ys. p(ys!i) \<and> x = ys!i \<and> (\<forall>j<i. \<not> p(ys!j))" by simp
    then obtain i where "i < length ys" and "p(ys!i)" and "x = ys!i"
      and "\<forall>j<i. \<not> p(ys!j)" by auto
    from `i < length ys` have "Suc i < length(y#ys)" by simp
    moreover from `p(ys!i)` have "p((y#ys)!Suc i)" by simp
    moreover from `x = ys!i` have "x = (y#ys)!(Suc i)" by simp
    moreover have "\<forall>j<Suc i. \<not> p((y#ys)!j)"
    proof (intro allI impI)
      fix j assume "j < Suc i" thus "\<not>p((y#ys)!j)" using `\<forall>j<i. \<not>p(ys!j)` False
        by (induct j) auto
    qed
    ultimately show ?thesis by best
  qed
qed

lemma find_SomeI:
  assumes "\<exists>i<length xs. f(xs!i) \<and> x = (xs!i) \<and> (\<forall>j<i. \<not> f(xs!j))"
  shows "find f xs = Some x"
using assms proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons y ys)
  with `\<exists> i < length (y # ys). f ((y # ys) ! i) \<and> (x =  ((y # ys) ! i)) \<and> (\<forall> j < i. \<not> f ((y # ys) ! j))`
  obtain i where "i < length (y # ys)" and "f ((y # ys) ! i)" 
           and "x = ((y # ys) ! i)" and "\<forall> j < i. \<not> f ((y # ys) ! j)" by auto
  show ?case
  proof (cases i, simp)
   case 0
    with `f ((y # ys) ! i)` have "f y" by simp
    with  `x = (y # ys) ! i` 0 have "y = x" by simp
    with `f y` show " (f y \<longrightarrow> y = x) \<and> (\<not> f y \<longrightarrow> find f ys = Some x)" by auto
  next
   case (Suc k)
    from Suc `\<forall> j < i. \<not> f ((y # ys) ! j)` have "\<not> f y" by auto
    hence rec:"find f (y # ys) = find f ys" by auto
    from Suc `i < length (y # ys)` have k1:"k < length ys" by simp
    from Suc `f ((y # ys) ! i)` have k2:"f (ys ! k)" by simp
    from Suc `x = (y # ys) ! i` have k3:"x = (ys ! k)" by simp
    from Suc `\<forall> j < i. \<not> f ((y # ys) ! j)` have "\<forall> j < k. \<not> f (ys ! j)" by auto
    with k1 k2 k3 have "\<exists>i<length ys. f (ys ! i) \<and> x = ys ! i \<and> (\<forall>j<i. \<not> f (ys ! j))" by auto
    with Cons have "find f ys = Some x" by auto
    with rec show "find f (y#ys) = Some x" by simp
  qed
qed

lemma ex_find_Some_conv:
 "(\<exists>i<length xs. f(xs!i) \<and> x = (xs!i) \<and> (\<forall>j<i. \<not> f(xs!j))) = (find f xs = Some x)"
by (rule iffI,rule find_SomeI,assumption,rule find_SomeE,assumption)

lemma find_cong[fundef_cong]:
  assumes xs: "xs = ys" and set: "\<And>x. x \<in> set ys \<Longrightarrow> f x = g x" 
  shows "find f xs = find g ys"
proof (cases "find f xs")
  case None
  hence "find f ys = None" using xs by simp
  hence "\<not>(\<exists> x. x \<in> set ys \<and> f x)" using find_NoneE by auto
  hence "\<not>(\<exists> x. x \<in> set ys \<and> g x)" using set by best   
  hence "find g ys = None" using find_NoneI by auto
  thus ?thesis using None by auto
next
  case (Some x) 
  hence "find f ys = Some x" using xs by simp
  hence "\<exists>i<length ys. f(ys!i) \<and> (x = (ys!i)) \<and> (\<forall>j<i. \<not> f (ys!j))" by (rule find_SomeE[where ?xs=ys])
  hence "\<exists>i<length ys. g(ys!i) \<and> (x = (ys!i)) \<and> (\<forall>j<i. \<not> g (ys!j))" using set by auto
  hence "find g ys = Some x" by (rule find_SomeI) 
  thus ?thesis using Some by auto
qed

lemma partition_filter_conv[simp]:
  "partition f xs = (filter f xs,filter (Not o f) xs)"
  unfolding partition_filter2[symmetric]
  unfolding partition_filter1[symmetric] by simp

declare partition.simps[simp del]

primrec
  list_union :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "list_union [] ys = ys" |
  "list_union (x # xs) ys = (let zs = list_union xs ys in if x \<in> set zs then zs else x # zs)"

lemma list_union_sound[simp]: "set (list_union xs ys) = set xs \<union> set ys"
proof (induct xs)
  case (Cons x xs) thus ?case by (cases "x \<in> set (list_union xs ys)") (auto)
qed simp

declare list_union.simps[simp del]

(* why was list_inter thrown out of List.thy? *)
fun list_inter :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "list_inter [] bs = []"
  | "list_inter (a#as) bs =
     (if a \<in> set bs then a # list_inter as bs else list_inter as bs)"

lemma list_inter[simp]:
  "set (list_inter xs ys) = set xs \<inter> set ys"
  by (induct rule: list_inter.induct, auto)

declare list_inter.simps[simp del]

primrec
  list_diff :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "list_diff [] ys = []" |
  "list_diff (x # xs) ys = (let zs = list_diff xs ys in if x \<in> set ys then zs else x # zs)"

lemma list_diff_sound[simp]: "set (list_diff xs ys) = set xs - set ys"
proof (induct xs)
  case (Cons x xs) thus ?case by (cases "x \<in> set ys") (auto)
qed simp

declare list_diff.simps[simp del]

abbreviation map_filter :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list"
where "map_filter f g xs \<equiv> foldr (\<lambda> x rest. if f x then g x # rest else rest) xs []"

fun lookup :: "'a \<Rightarrow> ('a \<times> 'b)list \<Rightarrow> 'b option"
where "lookup _ [] = None"
   |  "lookup a ((a',b) # xs) = (if a = a' then Some b else lookup a xs)"

lemma lookup_complete: assumes "lookup a ps = None"
  shows "\<not>(\<exists>b. (a,b) \<in> set ps)"
using assms
proof (induct ps, simp)
  case (Cons ab xs)
  show ?case
  proof (cases ab)
    case (Pair a' b)
    with Cons show ?thesis by (cases "a = a'", auto)
  qed
qed

lemma lookup_sound: assumes "lookup a ps = Some b"
  shows "(a,b) \<in> set ps"
using assms
proof (induct ps, simp)
  case (Cons ab xs)
  show ?case
  proof (cases ab)
    case (Pair a' b)
    with Cons show ?thesis by (cases "a = a'", auto)
  qed
qed

subsection {* Lists and Sets *}


lemma nth_append_take:
  assumes "i \<le> length xs" shows "(take i xs @ y#ys)!i = y"
proof -
  from assms have a: "length(take i xs) = i" by simp
  have "(take i xs @ y#ys)!(length(take i xs)) = y" by (rule nth_append_length)
  thus ?thesis unfolding a .
qed

lemma nth_append_take_is_nth_conv:
  assumes "i < j" and "j \<le> length xs" shows "(take j xs @ ys)!i = xs!i"
proof -
  from assms have "i < length(take j xs)" by simp
  hence "(take j xs @ ys)!i = take j xs ! i" unfolding nth_append by simp
  thus ?thesis unfolding nth_take[OF assms(1)] .
qed

lemma nth_append_drop_is_nth_conv:
  assumes "j < i" and "j \<le> length xs" and "i \<le> length xs"
  shows "(take j xs @ y # drop (Suc j) xs)!i = xs!i"
proof -
  from assms have j: "length(take j xs) = j" by auto
  from `j < i` obtain n where "Suc(j + n) = i" using less_imp_Suc_add by auto
  with assms have i: "i = length(take j xs) + Suc n" by auto
  have len: "Suc j + n \<le> length xs" using assms i by auto
  have "(take j xs @ y # drop (Suc j) xs)!i =
    (y # drop (Suc j) xs)!(i - length(take j xs))" unfolding nth_append i by auto
  also have "\<dots> = (y # drop (Suc j) xs)!(Suc n)" unfolding i by simp
  also have "\<dots> = (drop (Suc j) xs)!n" by simp
  finally show ?thesis unfolding nth_drop[OF len] using i j by simp
qed

lemma nth_append_take_drop_is_nth_conv: 
 assumes "i \<le> length xs" and "j \<le> length xs" and "i \<noteq> j" 
 shows "(take j xs @ y # drop (Suc j) xs)!i = xs!i"
proof -
 from assms have "i < j \<or> i > j" by auto
 thus ?thesis
 proof
  assume "i < j" thus ?thesis using assms by (auto simp: nth_append_take_is_nth_conv)
 next
  assume "j < i" thus ?thesis using assms by (auto simp: nth_append_drop_is_nth_conv)
 qed
qed
  
lemma take_drop_imp_nth: "\<lbrakk>take i ss @ x # drop (Suc i) ss = ss\<rbrakk> \<Longrightarrow> x = ss!i"
proof (induct ss arbitrary: i)
 case Nil thus ?case by auto
next
 case (Cons s ss)
 from `take i (s#ss) @ x # drop (Suc i) (s#ss) = (s#ss)` show ?case
 proof (induct i)
  case 0 thus ?case by auto
 next
  case (Suc i)
  from Cons have IH: "take i ss @ x # drop (Suc i) ss = ss \<Longrightarrow> x = ss!i" by auto
  from Suc have "take i ss @ x # drop (Suc i) ss = ss" by auto
  with IH show ?case by auto
 qed
qed

lemma nth_take_prefix:
 "length ys \<le> length xs \<Longrightarrow> \<forall>i < length ys. xs!i = ys!i \<Longrightarrow> take (length ys) xs = ys"
proof (induct ys arbitrary: xs)
 case Nil thus ?case by auto
next
 case (Cons y ys) note IH = this
 show ?case
 proof (cases xs)
  case Nil thus ?thesis using Cons by simp
 next
  case (Cons z zs)
  hence "xs!0 = z" by simp
  with IH have "z = y" by auto
  from IH have "\<forall>i < length ys. xs!(Suc i) = ys!i" by auto
  hence A:"\<forall>i < length ys. zs!i = ys!i" using Cons by auto
  have B:"length ys \<le> length zs" using IH Cons by auto
  have C:"take (length ys) zs = ys" using IH A B by simp
  have "take (length (y#ys)) (z#zs) = z#(take (length ys) zs)" by simp
  also have "\<dots> = z#ys" using C by simp
  finally show ?thesis unfolding `z = y` `xs = z#zs` .
 qed
qed

lemma nth_drop_0: "0 < length ss \<Longrightarrow> (ss!0)#drop (Suc 0) ss = ss" by (induct ss) auto


lemma map_nth_Suc: "map f [0 ..< Suc n] = f 0 # map (\<lambda> i. f (Suc i)) [0 ..< n]"
  by (induct n arbitrary: f, auto)

lemma zip_nth_conv: "length xs = length ys \<Longrightarrow> zip xs ys = map (\<lambda> i. (xs ! i, ys ! i)) [0 ..< length ys]"
proof (induct xs arbitrary: ys, simp)
  case (Cons x xs)
  then obtain y yys where ys: "ys = y # yys" by (cases ys, auto)
  with Cons have len: "length xs = length yys" by simp
  show ?case unfolding ys 
    by (simp del: upt_Suc add: map_nth_Suc, unfold Cons(1)[OF len], simp) 
qed

lemma append_Cons_nth_left:
  assumes "i < length xs"
  shows "(xs @ u # ys) ! i = xs ! i"
using assms nth_append[of xs _ i] by simp

lemma append_Cons_nth_middle:
  assumes "i = length xs"
  shows "(xs @ y # zs) ! i = y"
using assms by auto

lemma append_Cons_nth_right:
  assumes "i > length xs"
  shows "(xs @ u # ys) ! i = (xs @ z # ys) ! i"
proof -
  from assms have "i - length xs > 0" by auto
  then obtain j where j: "i - length xs = Suc j" by (cases "i - length xs", auto)
  thus ?thesis by (simp add: nth_append)
qed

lemma append_Cons_nth_not_middle:
  assumes "i \<noteq> length xs"
  shows "(xs @ u # ys) ! i = (xs @ z # ys) ! i"
proof (cases "i < length xs")
  case True
  thus ?thesis by (simp add: append_Cons_nth_left)
next
  case False 
  with assms have "i > length xs" by arith
  thus ?thesis by (rule append_Cons_nth_right)
qed

lemmas append_Cons_nth = append_Cons_nth_middle append_Cons_nth_not_middle

lemma map_id[simp]: "map id xs = xs" by (induct xs) auto


lemma map_nth_conv: "map f ss = map g ts \<Longrightarrow> \<forall>i < length ss. f(ss!i) = g(ts!i)"
proof (intro allI impI)
  fix i show "map f ss = map g ts \<Longrightarrow> i < length ss \<Longrightarrow> f(ss!i) = g(ts!i)"
  proof (induct ss arbitrary: i ts)
    case Nil thus ?case by (induct ts) auto
  next
    case (Cons s ss) thus ?case
    proof (induct ts)
      case Nil thus ?case by simp
    next
      case (Cons t ts) thus ?case by (cases i) auto
    qed
  qed
qed

(* The version of List is not general enough. *)
lemma map_eq_imp_length_eq:
assumes "map f ss = map g ts"
shows "length ss = length ts"
proof -
  from assms have "length(map f ss) = length(map g ts)" by simp
  thus ?thesis unfolding length_map .
qed

lemma replicate_prop: assumes "p x"
  shows "\<forall> y \<in> set (replicate n x). p y"
using assms by (induct n, auto)


lemma length_remdups_card_conv: "length(remdups xs) = card(set xs)"
proof -
  have xs: "concat[xs] = xs" by simp
  from length_remdups_concat[of "[xs]"] show ?thesis unfolding xs by simp
qed

lemma set_foldr_remdups_set_map_conv[simp]:
  "set(foldr (\<lambda>x xs. remdups(f x@xs)) xs []) = \<Union>set(map (set o f) xs)"
  by (induct xs) auto

lemma zip_same: "((a,b) \<in> set (zip xs xs)) = (a \<in> set xs \<and> a = b)"
  by (induct xs, auto)

lemma nth_map_conv:
assumes "length xs = length ys"
  and "\<forall>i<length xs. f(xs!i) = g(ys!i)"
shows "map f xs = map g ys"
using assms proof (induct xs arbitrary: ys)
  case Nil thus ?case by simp
next
  case (Cons x xs) thus ?case
  proof (induct ys)
    case Nil thus ?case by simp
  next
    case (Cons y ys)
    have "\<forall>i<length xs. f(xs!i) = g(ys!i)"
    proof (intro allI impI)
      fix i assume "i < length xs" thus "f(xs!i) = g(ys!i)" using Cons(4) by force
    qed
    with Cons show ?case by auto
  qed
qed


lemma map_nth_eq_conv: assumes len: "length xs = length ys"
  shows "(map f xs = ys) = (\<forall> i < length ys. f (xs ! i) = ys ! i)" (is "?l = ?r")
proof -
  have "(map f xs = ys) = (map f xs = map id ys)" by auto
  also have "... = (\<forall> i < length ys. f (xs ! i) = id (ys ! i))" using map_nth_conv[of f xs id ys] nth_map_conv[OF len, of f id] unfolding len
    by blast
  finally  show ?thesis by auto
qed


lemma eq_length_concat_nth: assumes "length xs = length ys"
  and "\<And> i. i < length xs \<Longrightarrow> length (xs ! i) = length (ys ! i)"
  shows "length (concat xs) = length (concat ys)"
using assms
proof (induct xs arbitrary: ys)
  case Nil
  thus ?case by auto
next
  case (Cons x xs zs)
  from Cons(2) obtain y ys where zs: "zs = y # ys" by (cases zs, auto)
  note Cons = Cons[unfolded zs]
  from Cons(2) have len: "length xs = length ys" by simp
  from Cons(3)[of 0] have xy: "length x = length y" by simp
  {
    fix i
    assume "i < length xs"
    with Cons(3)[of "Suc i"] 
    have "length (xs ! i) = length (ys ! i)" by simp
  } 
  from Cons(1)[OF len this] have ind: "length (concat xs) = length (concat ys)" by simp
  show ?case unfolding zs using xy ind by auto
qed

lemma concat_all_nth: assumes "length xs = length ys"
  and "\<And> i. i < length xs \<Longrightarrow> length (xs ! i) = length (ys ! i)"
  and "\<And> i j. i < length xs \<Longrightarrow> j < length (xs ! i) \<Longrightarrow> P (xs ! i ! j) (ys ! i ! j)"
  shows "\<forall>k<length (concat xs).
            P (concat xs ! k) (concat ys ! k)" 
using assms
proof (induct xs arbitrary: ys)
  case Nil
  thus ?case by auto
next
  case (Cons x xs zs)
  from Cons(2) obtain y ys where zs: "zs = y # ys" by (cases zs, auto)
  note Cons = Cons[unfolded zs]
  from Cons(2) have len: "length xs = length ys" by simp
  from Cons(3)[of 0] have xy: "length x = length y" by simp
  from Cons(4)[of 0] xy have pxy: "\<And> j. j < length x \<Longrightarrow> P (x ! j) (y ! j)" by auto
  {
    fix i
    assume i: "i < length xs"
    with Cons(3)[of "Suc i"] 
    have len: "length (xs ! i) = length (ys ! i)" by simp
    from Cons(4)[of "Suc i"] i len have "\<And> j. j < length (xs ! i) \<Longrightarrow> P (xs ! i ! j) (ys ! i ! j)"
      by auto
    note len and this
  } 
  from Cons(1)[OF len this] have ind: "\<And> k. k < length (concat xs) \<Longrightarrow> P (concat xs ! k) (concat ys ! k)" 
    by auto
  show ?case unfolding zs concat.simps
  proof (intro allI impI) 
    fix k
    assume k: "k < length (x @ concat xs)"
    show "P ((x @ concat xs) ! k) ((y @ concat ys) ! k)"
    proof (cases "k < length x")
      case True
      show ?thesis unfolding nth_append using True xy pxy[OF True]
        by simp
    next
      case False
      with k have "k - (length x) < length (concat xs)" by auto
      then obtain n where n: "k - length x = n" and nxs: "n < length (concat xs)" by auto
      show ?thesis unfolding nth_append n n[unfolded xy] using False xy ind[OF nxs]
        by auto
    qed
  qed
qed

lemma [code_inline]: "(set xs \<subseteq> set ys) = list_all (\<lambda> x. x \<in> set ys) xs"
  unfolding list_all_iff by auto

fun concat_lists :: "'a list list \<Rightarrow> 'a list list"
where "concat_lists [] = [[]]"
    | "concat_lists (as # xs) = (let rec = concat_lists xs in concat (map (\<lambda> vec. map (\<lambda> a. a # vec) as) rec))" 
lemma concat_lists[simp]: 
  shows "set (concat_lists xs) = { as. length as = length xs \<and> (\<forall> i < length xs. as ! i \<in> set (xs ! i))}"
proof (induct xs)
  case Nil
  show ?case by auto
next
  case (Cons as xs)
  have id: "set (concat_lists (as # xs)) = 
    {(a # bs) | a bs. length (a # bs) = length (as # xs) \<and> (\<forall>i<Suc (length xs). (a # bs) ! i \<in> set ((as # xs) ! i))}" (is "?L = ?M") unfolding all_Suc by (auto simp: Cons)
  show ?case (is "_ = ?R")
  proof -
    have one: "?M \<subseteq> ?R" by auto
    {
      fix cs
      assume cs: "cs \<in> ?R"
      then obtain c bs where cbs: "cs = c # bs" by (cases cs, auto)
      from cs have "cs \<in> ?M" unfolding cbs by auto
    }
    with one show ?thesis unfolding id by auto
  qed
qed

declare concat_lists.simps[simp del]


fun max_list :: "nat list \<Rightarrow> nat"
where "max_list [] = 0"
  | "max_list (x # xs) = max x (max_list xs)"

lemma max_list: "x \<in> set xs \<Longrightarrow> x \<le> max_list xs"
  by (induct xs, auto)
  
fun max_f :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
where "max_f f 0 = 0"
 | "max_f f (Suc i) = max (f i) (max_f f i)"

lemma max_f: "i < n \<Longrightarrow> f i \<le> max_f f n"
proof (induct n, simp)
  case (Suc n)
  thus ?case by (cases "i = n", auto)
qed

lemma max_list_mem: "xs \<noteq> [] \<Longrightarrow> max_list xs \<in> set xs"
proof (induct xs)
  case (Cons x xs)
  show ?case
  proof (cases "x \<ge> max_list xs")
    case True
    thus ?thesis by auto
  next
    case False
    hence max: "max_list xs > x" by auto
    hence nil: "xs \<noteq> []" by (cases xs, auto)
    from max have max: "max x (max_list xs) = max_list xs" by auto
    from Cons(1)[OF nil] max show ?thesis by auto
  qed
qed simp

lemma max_list_set: "max_list xs = (if set xs = {} then 0 else (THE x. x \<in> set xs \<and> (\<forall> y \<in> set xs. y \<le> x)))"
proof (cases "xs = []")
  case True thus ?thesis by simp
next
  case False
  note p = max_list_mem[OF this] max_list[of _ xs] 
  from False have id: "(set xs = {}) = False" by simp
  show ?thesis unfolding id if_False
  proof (rule the_equality[symmetric], intro conjI ballI, rule p, rule p)
    fix x 
    assume "x \<in> set xs \<and> (\<forall> y \<in> set xs. y \<le> x)"
    hence mem: "x \<in> set xs" and le: "\<And> y. y \<in> set xs \<Longrightarrow> y \<le> x" by auto
    from max_list[OF mem] le[OF max_list_mem[OF False]] 
    show "x = max_list xs" by simp
  qed
qed
      
lemma max_list_eq_set: "set xs = set ys \<Longrightarrow> max_list xs = max_list ys"
  unfolding max_list_set by simp


fun min_list :: "('a :: linorder) list \<Rightarrow> 'a"
where "min_list [x] = x"
   | "min_list (x # xs) = min x (min_list xs)" 


lemma min_list: "(x :: 'a :: linorder) \<in> set xs \<Longrightarrow> min_list xs \<le> x"
proof (induct xs, simp)
  case (Cons y ys) note oCons = this
  show ?case
  proof (cases ys)
    case Nil
    thus ?thesis using Cons by auto
  next
    case (Cons z zs)
    hence id: "min_list (y # ys) = min y (min_list ys)" 
      by auto
    show ?thesis 
    proof (cases "x = y")
      case True
      show ?thesis unfolding id True by auto
    next
      case False
      have "min y (min_list ys) \<le> min_list ys" by auto
      also have "... \<le> x" using oCons False by auto
      finally show ?thesis unfolding id .
    qed
  qed
qed

lemma min_list_cons: assumes xy: "x \<le> y"
  and len: "length xs = length ys"
  and xsys: "min_list xs \<le> min_list ys"
  shows "min_list (x # xs) \<le> min_list (y # ys)"
proof (cases xs)
  case Nil
  with len have ys: "ys = []" by simp
  with xy Nil show ?thesis by simp
next
  case (Cons x' xs')
  with len obtain y' ys' where ys: "ys = y' # ys'" by (cases ys, auto)
  from Cons have one: "min_list (x # xs) = min x (min_list xs)" by auto
  from ys have two: "min_list (y # ys) = min y (min_list ys)" by auto
  show ?thesis unfolding one two using xy xsys 
    unfolding  min_def by auto
qed

lemma min_list_nth: assumes "length xs = length ys"
  and "\<And> i. i < length ys \<Longrightarrow> xs ! i \<le> ys ! i"
  shows "min_list xs \<le> min_list ys"
using assms
proof (induct xs arbitrary: ys)
  case Nil
  thus ?case by auto
next
  case (Cons x xs zs)
  from Cons(2) obtain y ys where zs: "zs = y # ys" by (cases zs, auto)
  note Cons = Cons[unfolded zs]
  from Cons(2) have len: "length xs = length ys" by simp
  from Cons(3)[of 0] have xy: "x \<le> y" by simp
  {
    fix i
    assume "i < length xs"
    with Cons(3)[of "Suc i"] Cons(2)
    have "xs ! i \<le> ys ! i" by simp
  } 
  from Cons(1)[OF len this] Cons(2) have ind: "min_list xs \<le> min_list ys" by simp
  show ?case unfolding zs
    by (rule min_list_cons[OF xy len ind])
qed

lemma min_list_ex: assumes "xs \<noteq> []" shows
  "\<exists> x \<in> set xs. min_list xs = x"
  using assms
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs) note oCons = this
  show ?case
  proof (cases xs)
    case Nil
    thus ?thesis by auto
  next
    case (Cons y ys)
    hence id: "min_list (x # xs) = min x (min_list xs)" and nNil: "xs \<noteq> []" by auto
    show ?thesis
    proof (cases "x \<le> min_list xs")
      case True
      show ?thesis unfolding id 
        by (rule bexI[of _ x], insert True, auto simp: min_def)
    next
      case False
      show ?thesis unfolding id min_def
        using oCons(1)[OF nNil] False by auto
    qed
  qed
qed

lemma min_list_subset: assumes subset: "set ys \<subseteq> set xs" and mem: "min_list xs \<in> set ys" shows
  "min_list xs = min_list ys"
proof -
  from subset mem have "xs \<noteq> []" by auto
  from min_list_ex[OF this] obtain x where x: "x \<in> set xs" and mx: "min_list xs = x" by auto
  from min_list[OF mem] have two: "min_list ys \<le> min_list xs" by auto
  from mem have "ys \<noteq> []" by auto
  from min_list_ex[OF this] obtain y where y: "y \<in> set ys" and my: "min_list ys = y" by auto
  from y subset have "y \<in> set xs" by auto
  from min_list[OF this] have one: "min_list xs \<le> y" by auto
  from one two 
  show ?thesis unfolding mx my by auto
qed



lemma lookup_None[simp]:
  assumes "V \<inter> set vs = {}" and "x \<in> V" shows "lookup x (zip vs ts) = None"
using assms proof (induct vs arbitrary: ts)
  case Nil show ?case by simp
next
  case (Cons v vs)
  note IH = this
  hence neq: "v \<noteq> x" by auto
  show ?case
  proof (cases ts)
    case Nil show ?thesis unfolding Nil by simp
  next
     case (Cons t ts')
     from IH have IH': "lookup x (zip vs ts') = None" by auto
     have "lookup x (zip (v#vs) ts) = lookup x ((v,t)#zip vs ts')" unfolding Cons by simp
     also have "\<dots> = lookup x (zip vs ts')" using neq by simp
     also have "\<dots> = None" unfolding IH' by simp
     finally show ?thesis .
  qed
qed


lemma lookup_Some[simp]:
  assumes "distinct vs" and "length vs \<le> length ts" and "i < length vs"
  shows "lookup (vs!i) (zip vs ts) = Some(ts!i)"
using assms proof (induct i arbitrary: vs ts)
  case 0 thus ?case by (induct ts) (induct vs,auto)+
next
  case (Suc i) show ?case
  proof (cases ts)
    case Nil with Suc show ?thesis unfolding Nil by simp
  next
    case (Cons t ts')
    note Cons' = this
    show ?thesis
    proof (cases vs)
      case Nil from Suc show ?thesis unfolding Cons' Nil by simp
    next
      case (Cons v vs') from Suc show ?thesis unfolding Cons Cons' by auto
    qed
  qed
qed

lemma lookup_append_Some: "lookup x ps = Some y \<Longrightarrow> lookup x (ps @ qs) = Some y"
  by (induct ps, auto)

lemma lookup_append_None: "lookup x ps = None \<Longrightarrow> lookup x (ps @ qs) = lookup x qs"
  by (induct ps, auto)

lemma take_drop_update_first: assumes "j < length ds" and "length cs = length ds"
  shows "(take j ds @ drop j cs)[j := ds ! j] = take (Suc j) ds @ drop (Suc j) cs" 
using assms
proof (induct j arbitrary: ds cs)
  case 0
  then obtain d dds c ccs where ds: "ds = d # dds" and cs: "cs = c # ccs" by (cases ds, simp, cases cs, auto)
  show ?case unfolding ds cs by auto
next
  case (Suc j)
  then obtain d dds c ccs where ds: "ds = d # dds" and cs: "cs = c # ccs" by (cases ds, simp, cases cs, auto)
  from Suc(1)[of dds ccs] Suc(2) Suc(3) show ?case unfolding ds cs by auto
qed


lemma take_drop_update_second: assumes "j < length ds" and "length cs = length ds"
  shows "(take j ds @ drop j cs)[j := cs ! j] = take j ds @ drop j cs"
using assms
proof (induct j arbitrary: ds cs)
  case 0
  then obtain d dds c ccs where ds: "ds = d # dds" and cs: "cs = c # ccs" by (cases ds, simp, cases cs, auto)
  show ?case unfolding ds cs by auto
next
  case (Suc j)
  then obtain d dds c ccs where ds: "ds = d # dds" and cs: "cs = c # ccs" by (cases ds, simp, cases cs, auto)
  from Suc(1)[of dds ccs] Suc(2) Suc(3) show ?case unfolding ds cs by auto
qed


lemma distinct_take_drop: assumes dist: "distinct vs" and len: "i < length vs" shows "distinct(take i vs @ drop (Suc i) vs)" (is "distinct(?xs@?ys)")
proof -
  from id_take_nth_drop[OF len] have vs[symmetric]: "vs = ?xs @ vs!i # ?ys" .
  with dist have "distinct ?xs" and "distinct(vs!i#?ys)" and "set ?xs \<inter> set(vs!i#?ys) = {}" using distinct_append[of ?xs "vs!i#?ys"] by auto
  hence "distinct ?ys" and "set ?xs \<inter> set ?ys = {}" by auto
  with `distinct ?xs` show ?thesis using distinct_append[of ?xs ?ys] vs by simp
qed

primrec option_to_list :: "'a option \<Rightarrow> 'a list" where
  "option_to_list (Some a) = [a]"
| "option_to_list None = []"

lemma option_to_list_sound[simp]: "set (option_to_list t) \<equiv> Option.set t"
  by (induct t) auto


fun decomp :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list option"
  where "decomp [] [] = Some []"
      | "decomp (_#_) [] = None"
      | "decomp [] (_#_) = None"
      | "decomp (s#ss) (t#ts) = 
            (case decomp ss ts of 
                None \<Rightarrow> None
               | Some pairs \<Rightarrow> Some ((s,t)#pairs))"

lemma decompZip: "decomp ss ts = Some pairs \<Longrightarrow> pairs = zip ss ts"
proof (induct ss ts arbitrary: pairs rule: decomp.induct)
  case 1 thus ?case by simp next
  case 2 thus ?case by simp next
  case 3 thus ?case by simp next
  case (4 s ss t ts pairs) thus ?case by (cases "decomp ss ts", auto)
qed

lemma decompLength: "decomp ss ts = Some pairs \<Longrightarrow> length ss = length ts"
proof (induct ss ts arbitrary: pairs rule: decomp.induct)
  case 1 thus ?case by simp next
  case 2 thus ?case by simp next
  case 3 thus ?case by simp next
  case (4 s ss t ts pairs) thus ?case by (cases "decomp ss ts", auto)
qed

lemma decompNone: "decomp ss ts = None \<Longrightarrow> length ss \<noteq> length ts"
using assms
proof (induct rule: decomp.induct)
  case 1 thus ?case by simp next
  case 2 thus ?case by simp next
  case 3 thus ?case by simp next
  case (4 s sss t tss) thus ?case by (cases "decomp sss tss = None", auto)
qed

declare decomp.simps[simp del]



fun "extract" :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'a \<times> 'a list)option"
where "extract p [] = None"
  |   "extract p (x # xs) = (if p x then Some ([], x, xs) else 
                                case extract p xs of
                                   None \<Rightarrow> None
                                 | Some (ys,y,zs) \<Rightarrow> Some (x # ys, y, zs))"


lemma extract_None: "extract p xs = None \<Longrightarrow> \<forall> x \<in> set xs. \<not> p x"
proof (induct xs, simp)
  case (Cons x xs)
  show ?case 
  proof (cases "p x")
    case True
    hence False using Cons(2) by simp
    thus ?thesis ..
  next
    case False
    with Cons show ?thesis by (cases "extract p xs", auto)
  qed
qed

lemma extract_Some: assumes "extract p xs = Some (ys, y, zs)" 
  shows "xs = ys @ y # zs \<and> p y"
using assms
proof (induct xs arbitrary: ys, simp)
  case (Cons x xs)
  show ?case 
  proof (cases "p x")
    case True
    thus ?thesis using Cons(2) by auto
  next
    case False
    show ?thesis 
    proof (cases "extract p xs")
      case None
      with Cons(2) False show ?thesis by simp
    next
      case (Some res)
      with False Cons(2) obtain us where rec: "extract p xs = Some (us, y, zs)" and ys: "ys = x # us" by (cases res, auto)
      from Cons(1)[OF rec] ys show ?thesis by simp        
    qed
  qed
qed


fun distinct_eq :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where "distinct_eq _ [] = True"
  |   "distinct_eq eq (x # xs) = ((\<forall> y \<in> set xs. \<not> (eq y x)) \<and> distinct_eq eq xs)"

lemma distinct_eq_append: "distinct_eq eq (xs @ ys) = (distinct_eq eq xs \<and> distinct_eq eq ys \<and> (\<forall> x \<in> set xs. \<forall> y \<in> set ys. \<not> (eq y x)))"
  by (induct xs, auto)

subsection {* size estimations *}

lemma list_size_pointwise2: assumes "length xs = length ys"
  and "\<And> i. i < length ys \<Longrightarrow> f (xs ! i) \<le> g (ys ! i)"
  shows "list_size f xs \<le> list_size g ys"
proof -
  have id: "(list_size f xs \<le> list_size g ys) = (listsum (map f xs) \<le> listsum (map g ys))"
    unfolding list_size_conv_listsum assms(1) by auto
  have "map f xs = map f (map (op ! xs) [0..<length xs])" using map_nth[of xs] by simp
  also have "... = map (\<lambda> i. f (xs ! i)) [0..<length xs]" (is "_ = ?xs") by simp
  finally have xs: "map f xs = ?xs" .
  have "map g ys = map g (map (op ! ys) [0..<length ys])" using map_nth[of ys] by simp
  also have "... = map (\<lambda> i. g (ys ! i)) [0..<length xs]" (is "_ = ?ys") using assms by simp
  finally have ys: "map g ys = ?ys" .
  show ?thesis
    unfolding id unfolding xs ys
    by (rule listsum_mono, insert assms, auto)
qed    


lemma size_simp1: "t \<in> set ts \<Longrightarrow> size t < Suc (list_size size ts)"
by (induct ts) auto
lemma size_simp2: "t \<in> set ts \<Longrightarrow> size t < Suc (Suc(size s + list_size size ts))"
by (induct ts) auto
lemma size_simp3: assumes mem: "(x,y) \<in> set (zip xs ys)" 
  shows "size x < Suc (list_size size xs)"
  using set_zip_leftD[OF mem]  size_simp1 by auto 
lemma size_simp4: assumes mem: "(x,y) \<in> set (zip xs ys)" 
  shows "size y < Suc (list_size size ys)"
  using set_zip_rightD[OF mem] using size_simp1 by auto 


subsection {* Partitions *}
text {* Check whether a list of sets forms a partition, i.e.,
whether the sets are pairwise disjoint. *}
definition is_partition :: "('a set)list \<Rightarrow> bool"
where "is_partition cs = (\<forall>j<length cs. \<forall>i<j. cs!i \<inter> cs!j = {})"

(* and an equivalent but more symmetric version *)
definition is_partition_alt :: "('a set)list \<Rightarrow> bool"
where "is_partition_alt cs = (\<forall> i j. i < length cs \<and> j < length cs \<and> i \<noteq> j \<longrightarrow> cs!i \<inter> cs!j = {})"

lemma is_partition_alt: "is_partition = is_partition_alt"
proof (intro ext)
  fix cs
  {
    assume "is_partition_alt cs"
    hence "is_partition cs" unfolding is_partition_def is_partition_alt_def by auto
  }
  moreover
  {
    assume part: "is_partition cs"
    have "is_partition_alt cs" unfolding is_partition_alt_def
    proof (intro allI impI)
      fix i j
      assume "i < length cs \<and> j < length cs \<and> i \<noteq> j"
      with part show "cs ! i \<inter> cs ! j = {}"
        unfolding is_partition_def
        by (cases "i < j", simp, cases "j < i", force, simp)
    qed
  }
  ultimately
  show "is_partition cs = is_partition_alt cs" by auto
qed
      
lemma is_partition_Nil: "is_partition [] = True" unfolding is_partition_def by auto
lemma is_partition_Cons:
 "is_partition(x#xs) = (is_partition xs \<and> x \<inter> \<Union>set xs = {})" (is "?l = ?r")
proof
  assume ?l
  have one: "is_partition xs"
  proof (unfold is_partition_def, intro allI impI)
    fix j i assume "j < length xs" and "i < j"
    hence "Suc j < length(x#xs)" and "Suc i < Suc j" by auto
    from `?l`[unfolded is_partition_def,THEN spec,THEN mp,THEN spec,THEN mp,OF this]
    have "(x#xs)!(Suc i) \<inter> (x#xs)!(Suc j) = {}" .
    thus "xs!i \<inter> xs!j = {}" by simp
  qed
  have two: "x \<inter> \<Union>set xs = {}"
  proof (rule ccontr)
    assume "x \<inter> \<Union>set xs \<noteq> {}"
    then obtain y where "y \<in> x" and "y \<in> \<Union>set xs" by auto
    then obtain z where "z \<in> set xs" and "y \<in> z" by auto
    then obtain i where "i < length xs" and "xs!i = z" using in_set_conv_nth[of z xs] by auto
    with `y \<in> z` have "y \<in> (x#xs)!Suc i" by auto
    moreover with `y \<in> x` have "y \<in> (x#xs)!0" by simp
    ultimately have "(x#xs)!0 \<inter> (x#xs)!Suc i \<noteq> {}" by auto
    moreover from `i < length xs` have "Suc i < length(x#xs)" by simp
    ultimately show False using `?l`[unfolded is_partition_def] by best
  qed
  from one two show ?r ..
next
  assume ?r
  show ?l
  proof (unfold is_partition_def, intro allI impI)
    fix j i
    assume j: "j < length (x # xs)"
    assume i: "i < j"
    from i obtain j' where j': "j = Suc j'" by (cases j, auto)
    with j have j'len: "j' < length xs" and j'elem: "(x # xs) ! j = xs ! j'" by auto
    show "(x # xs) ! i \<inter> (x # xs) ! j = {}"
    proof (cases i)
      case 0
      with j'elem have "(x # xs) ! i \<inter> (x # xs) ! j = x \<inter> xs ! j'" by auto
      also have "\<dots> \<subseteq> x \<inter> \<Union>set xs" using j'len by force
      finally show ?thesis using `?r` by auto
    next
      case (Suc i')
      with i j' have i'j': "i' < j'" by auto
      from Suc j' have "(x # xs) ! i \<inter> (x # xs) ! j = xs ! i' \<inter> xs ! j'" by auto
      with `?r` i'j' j'len show ?thesis unfolding is_partition_def by auto
    qed
  qed
qed


subsection {*merging functions*}

definition fun_merge :: "('a \<Rightarrow> 'b)list \<Rightarrow> 'a set list \<Rightarrow> 'a \<Rightarrow> 'b"
  where "fun_merge fs as a \<equiv> (fs ! (LEAST i. i < length as \<and> a \<in> as ! i)) a"

lemma fun_merge: assumes 
      i: "i < length as"
  and a: "a \<in> as ! i"
  and ident: "\<And> i j a. i < length as \<Longrightarrow> j < length as \<Longrightarrow> a \<in> as ! i \<Longrightarrow> a \<in> as ! j \<Longrightarrow> (fs ! i) a = (fs ! j) a"
  shows "fun_merge fs as a = (fs ! i) a"
proof -
  let ?p = "\<lambda> i. i < length as \<and> a \<in> as ! i"
  let ?l = "LEAST i. ?p i"
  have p: "?p ?l"
    by (rule LeastI, insert i a, auto)
  show ?thesis unfolding fun_merge_def
    by (rule ident[OF _ i _ a], insert p, auto)
qed

lemma fun_merge_part: assumes 
      part: "is_partition as"
  and i: "i < length as"
  and a: "a \<in> as ! i"
  shows "fun_merge fs as a = (fs ! i) a"
proof(rule fun_merge[OF i a])
  fix i j a
  assume "i < length as" and "j < length as" and "a \<in> as ! i" and "a \<in> as ! j"
  hence "i = j" using part[unfolded is_partition_alt is_partition_alt_def] by (cases "i = j", auto)
  thus "(fs ! i) a = (fs ! j) a" by simp
qed

subsection {* assignments from key-value pairs *}

fun enum_vectors :: "'c list \<Rightarrow> 'v list \<Rightarrow> ('v \<times> 'c)list list"
where "enum_vectors C [] = [[]]"
    | "enum_vectors C (x # xs) = (let rec = enum_vectors C xs in concat (map (\<lambda> vec. map (\<lambda> c. (x,c) # vec) C) rec))" 

definition fun_of :: "('v \<times> 'c)list \<Rightarrow> 'v \<Rightarrow> 'c"
where [simp]: "fun_of vec x = the (lookup x vec)"

lemma enum_vectors_complete: assumes "C \<noteq> []"
  shows "\<exists> vec \<in> set (enum_vectors C xs). \<forall> x \<in> set xs. \<forall> c \<in> set C. \<alpha> x = c \<longrightarrow> fun_of vec x = c"
proof (induct xs, simp)
  case (Cons x xs)
  from this obtain vec where enum: "vec \<in> set (enum_vectors C xs)" and eq: "\<forall> x \<in> set xs. \<forall> c \<in> set C. \<alpha> x = c \<longrightarrow> fun_of vec x = c" by auto
  from enum have res: "set (map (\<lambda> c. (x,c) # vec) C) \<subseteq> set (enum_vectors C (x # xs)) " (is "_ \<subseteq> ?res") by auto
  show ?case 
  proof (cases "\<alpha> x \<in> set C")
    case False
    from assms have "hd C \<in> set C" by auto
    with res have elem: "(x,hd C) # vec \<in> ?res" (is "?vec \<in> _") by auto
    from eq False have "\<forall> y \<in> set (x # xs). \<forall> c \<in> set C. \<alpha> y = c \<longrightarrow> fun_of ?vec y = c" by auto
    with elem show ?thesis by blast
  next
    case True
    with res have elem: "(x, \<alpha> x) # vec \<in> ?res" (is "?vec \<in> _") by auto
    from eq True have "\<forall> y \<in> set (x # xs). \<forall> c \<in> set C. \<alpha> y = c \<longrightarrow> fun_of ?vec y = c" by auto
    with elem show ?thesis by blast
  qed
qed

lemma enum_vectors_sound: assumes "y \<in> set xs" and "vec \<in> set (enum_vectors C xs)"
  shows "fun_of vec y \<in> set C"
  using assms
proof (induct xs arbitrary: vec, simp)
  case (Cons x xs vec)
  from Cons(3) obtain v vecc where vec: "vec = v # vecc" by auto
  note C3 = Cons(3)[unfolded vec enum_vectors.simps Let_def]
  from C3 have vecc: "vecc \<in> set (enum_vectors C xs)" by auto
  from C3 obtain c where v: "v = (x,c)" and c: "c \<in> set C" by auto
  show ?case 
  proof (cases "y = x")
    case True
    show ?thesis unfolding vec v True using c by auto
  next
    case False
    with Cons(2) have y: "y \<in> set xs" by auto
    from False have id: "fun_of vec y = fun_of vecc y"
      unfolding vec v by auto
    show ?thesis unfolding id
      by (rule Cons(1)[OF y vecc])
  qed
qed


declare fun_of_def[simp del]    

lemma fun_of_concat: assumes mem: "x \<in> set (map fst (\<tau>s i))"
  and i: "i < n"
  and ident: "\<And> i j. i < n \<Longrightarrow> j < n \<Longrightarrow> x \<in> set (map fst (\<tau>s i)) \<Longrightarrow> x \<in> set (map fst (\<tau>s j)) \<Longrightarrow> fun_of (\<tau>s i) x = fun_of (\<tau>s j) x"
  shows "fun_of (concat (map \<tau>s [0..<n])) x = fun_of (\<tau>s i) x"
using assms
proof (induct n arbitrary: i \<tau>s)
  case 0
  thus ?case by simp
next
  case (Suc n i \<tau>s) note IH = this
  let ?\<tau>s = "\<lambda>i. \<tau>s (Suc i)"
  have id: "concat (map \<tau>s [0..<Suc n]) = \<tau>s 0 @ concat (map ?\<tau>s [0..<n])" unfolding map_nth_Suc by simp
  let ?l = "lookup x (\<tau>s 0)"
  show ?case
  proof (cases i)
    case 0
    with IH(2) have x: "x \<in> set (map fst (\<tau>s 0))" by auto
    then obtain y where xy: "(x,y) \<in> set (\<tau>s 0)" by auto
    from lookup_complete[of x "\<tau>s 0"] xy  have "?l \<noteq> None" by auto
    then obtain y where look: "?l = Some y" by (cases "\<tau>s 0", auto)
    show ?thesis unfolding 0 fun_of_def id look lookup_append_Some[OF look] by simp
  next
    case (Suc j)
    with IH(3)
    have 0: "0 < i" and j: "j < n" by auto
    show ?thesis 
    proof (cases "x \<in> set (map fst (\<tau>s 0))")
      case False
      have l: "?l = None"
      proof (cases "?l")
        case (Some y)
        from lookup_sound[OF this] False show ?thesis by force
      qed simp
      show ?thesis unfolding fun_of_def id lookup_append_None[OF l]
        unfolding fun_of_def[symmetric] Suc
      proof (rule IH(1)[OF _ j])
        show "x \<in> set (map fst (\<tau>s (Suc j)))" using IH(2) unfolding Suc .
      next
        fix i j
        assume "i < n" and "j < n" and "x \<in> set (map fst (\<tau>s (Suc i)))" and "x \<in> set (map fst (\<tau>s (Suc j)))"
        thus "fun_of (\<tau>s (Suc i)) x = fun_of (\<tau>s (Suc j)) x"
          using IH(4)[of "Suc i" "Suc j"] by auto
      qed
    next
      case True
      then obtain y where xy: "(x,y) \<in> set (\<tau>s 0)" by auto
      from lookup_complete[of x "\<tau>s 0"] xy  have "?l \<noteq> None" by auto
      then obtain y where look: "?l = Some y" by (cases "\<tau>s 0", auto)
      have "fun_of (concat (map \<tau>s [0..<Suc n])) x = fun_of (\<tau>s 0) x" 
        unfolding id fun_of_def look
        lookup_append_Some[OF look] by simp
      also have "... = fun_of (\<tau>s i) x"
      proof (rule IH(4)[OF _ IH(3)])
        from xy show "x \<in> set (map fst (\<tau>s 0))" by force
      next
        from IH(2) show "x \<in> set (map fst (\<tau>s i))" by force
      qed simp
      finally show ?thesis .
    qed
  qed
qed

lemma fun_of_concat_part: assumes mem: "x \<in> set (map fst (\<tau>s i))"
  and i: "i < n"
  and partition: "is_partition (map (\<lambda> i. set (map fst (\<tau>s i))) [0..<n])"
  shows "fun_of (concat (map \<tau>s [0..<n])) x = fun_of (\<tau>s i) x"
proof (rule fun_of_concat, rule mem, rule i)
  fix i j
  assume "i < n" and "j < n" and "x \<in> set (map fst (\<tau>s i))" and "x \<in> set (map fst (\<tau>s j))"
  hence "i = j" using partition[unfolded is_partition_alt is_partition_alt_def] by (cases "i = j", auto)
  thus "fun_of (\<tau>s i) x = fun_of (\<tau>s j) x" by simp
qed

lemma fun_of_concat_merge: assumes "\<And> i. i < length ts \<Longrightarrow> x \<in> h (ts ! i) \<Longrightarrow> fun_of (f i) x = (g ! i) x"
  and "length ts = length g"
  and "\<And> i. i < length ts \<Longrightarrow> (lookup x (f i) \<noteq> None) = (x \<in> h (ts ! i))"
  and "x \<in> h (ts ! i)"
  and "i < length ts"
  shows "fun_of (concat (map f [0..<length ts])) x = fun_merge g (map h ts) x"
  using assms 
  unfolding fun_merge_def fun_of_def
proof (induct ts arbitrary: i f g)
  case Nil
  thus ?case by simp
next
  case (Cons xy ts)
  let ?p' = "\<lambda> ts i. i < length (map h ts) \<and> x \<in> map h ts ! i"
  let ?p = "?p' (xy # ts)"
  let ?P = "?p' ts"
  let ?L = "LEAST i. ?p i"
  have id: "the (lookup x (concat (map f [0..<length (xy # ts)]))) = 
    the (lookup x (f 0 @ concat (map (\<lambda> i. f (Suc i)) [0..<length ts])))" (is "?l = the (lookup x ( _ @ ?l'))")
    by (simp add: map_nth_Suc del: upt_Suc) 
  show ?case 
  proof (cases "lookup x (f 0)")
    case (Some y)
    from lookup_append_Some[OF Some]
    have ly: "?l = y" unfolding id Some by simp
    have "?p 0" using Cons(4)[of 0] using Some by auto
    hence L0: "?L = 0" 
      by (rule Least_equality, simp)
    from Cons(4)[of 0] Some have x: "x \<in> h xy" by auto
    show ?thesis unfolding ly L0 using Cons(2)[of 0, unfolded Some] x by simp
  next
    case None
    from lookup_append_None[OF None]
    have ll: "?l = the (lookup x ?l')" unfolding id by simp
    from Cons(4)[of 0] None have x: "x \<notin> h xy" by auto
    hence p0: "\<not> ?p 0" by simp
    from Cons(5) Cons(6) have pI: "?p i" unfolding nth_map[OF Cons(6)] by simp
    from Least_Suc[of ?p, OF pI p0] have L: "?L = Suc (LEAST m. ?P m)" by simp
    from Cons(3) obtain a g' where g: "g = a # g'" by (cases g, auto)
    from Cons(5) x obtain j where i: "i = Suc j" by (cases i, auto)
    show ?thesis unfolding ll L g nth_Cons_Suc
    proof (rule Cons(1))
      from g Cons(3) show "length ts = length g'" by auto
    next
      from Cons(5) i show "x \<in> h (ts ! j)" by auto
    next
      from Cons(6) i show "j < length ts" by auto
    next
      fix m
      assume "m < length ts"
      thus "(lookup x (f (Suc m)) \<noteq> None) = (x \<in> h (ts ! m))"
        using Cons(4)[of "Suc m"] by auto
    next
      fix m
      assume "m < length ts" and "x \<in> h (ts ! m)"
      thus "the (lookup x (f (Suc m))) = (g' ! m) x"
        using Cons(2)[of "Suc m"] unfolding g by auto
    qed
  qed
qed

subsection {* assembling infinite words from finite words *}

(* inf_concat_simple: for concatenating infinitely many non-empty words to an infinite word *)
fun inf_concat_simple :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> (nat \<times> nat)"
where "inf_concat_simple f 0 = (0,0)"
  |   "inf_concat_simple f (Suc n) = (let (i,j) = inf_concat_simple f n in 
           if Suc j < f i 
               then (i,Suc j)
               else (Suc i, 0))"

lemma inf_concat_simple_add: assumes ck: "inf_concat_simple f k = (i,j)"
  and jl: "j + l < f i"
  shows "inf_concat_simple f (k + l) = (i,j + l)"
  using jl
proof (induct l)
  case 0
  thus ?case using ck by simp
next
  case (Suc l)
  hence c: "inf_concat_simple f (k + l) = (i, j+ l)" by auto
  show ?case 
    by (simp add: c, insert Suc(2), auto)
qed

lemma inf_concat_simple_surj_zero: "\<exists> k. inf_concat_simple f k = (i,0)"
proof (induct i)
  case 0
  show ?case 
    by (rule exI[of _ 0], simp)
next
  case (Suc i)
  then obtain k where ck: "inf_concat_simple f k = (i,0)" by auto
  show ?case
  proof (cases "f i")
    case 0
    show ?thesis
      by (rule exI[of _ "Suc k"], simp add: ck 0)
  next
    case (Suc n)
    hence "0 + n < f i" by auto
    from inf_concat_simple_add[OF ck, OF this] Suc
    show ?thesis
      by (intro exI[of _ "k + Suc n"], auto)
  qed
qed

lemma inf_concat_simple_surj: assumes "j < f i"
  shows "\<exists> k. inf_concat_simple f k = (i,j)"
proof -
  from assms have j: "0 + j < f i" by auto
  from inf_concat_simple_surj_zero obtain k where "inf_concat_simple f k = (i,0)" by auto
  from inf_concat_simple_add[OF this, OF j] show ?thesis by auto
qed

lemma inf_concat_simple_mono: assumes "k \<le> k'" shows "fst (inf_concat_simple f k) \<le> fst (inf_concat_simple f k')"
proof -
  from assms have "k' = k + (k' - k)" by auto
  then obtain l where k': "k' = k + l" by auto
  show ?thesis  unfolding k'
  proof (induct l)
    case (Suc l)
    obtain i j where ckl: "inf_concat_simple f (k+l) = (i,j)" by (cases "inf_concat_simple f (k+l)", auto)
    with Suc have "fst (inf_concat_simple f k) \<le> i" by auto
    also have "... \<le> fst (inf_concat_simple f (k + Suc l))"
      by (simp add: ckl)
    finally show ?case .
  qed simp
qed


(* inf_concat assembles infinitely many (possibly empty) words to an infinite word *)
fun inf_concat :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<times> nat"
  where "inf_concat n 0 = (LEAST j. n j > 0,0)"
     |  "inf_concat n (Suc k) = (let (i,j) = inf_concat n k in (if Suc j < n i then (i, Suc j) else (LEAST i'. i' > i \<and> n i' > 0, 0)))"

lemma inf_concat_bounds: assumes inf: "INFM i. n i > 0"
  and res: "inf_concat n k = (i,j)"
  shows "j < n i"
proof (cases k)
  case 0
  with res have i: "i = (LEAST i. n i > 0)" and j: "j = 0" by auto
  from inf[unfolded INFM_nat_le] obtain i' where i': "0 < n i'" by auto
  have "0 < n (LEAST i. n i > 0)" 
    by (rule LeastI, rule i')
  with i j show ?thesis by auto
next
  case (Suc k')
  obtain i' j' where res': "inf_concat n k' = (i',j')" by force
  note res = res[unfolded Suc inf_concat.simps res' Let_def split]
  show ?thesis 
  proof (cases "Suc j' < n i'")
    case True
    with res show ?thesis by auto
  next
    case False
    with res have i: "i = (LEAST f. i' < f \<and> 0 < n f)" and j: "j = 0" by auto
    from inf[unfolded INFM_nat] obtain f where f: "i' < f \<and> 0 < n f" by auto
    have "0 < n (LEAST f. i' < f \<and> 0 < n f)"
      using LeastI[of "\<lambda> f. i' < f \<and> 0 < n f", OF f]
      by auto
    with i j show ?thesis by auto
  qed
qed

lemma inf_concat_add: assumes res: "inf_concat n k = (i,j)"
  and j: "j + m < n i"
  shows "inf_concat n (k + m) = (i,j+m)"
  using j
proof (induct m)
  case 0 show ?case using res by auto
next
  case (Suc m)
  hence "inf_concat n (k + m) = (i, j+m)" by auto
  with Suc(2)
  show ?case by auto
qed

lemma inf_concat_step: assumes res: "inf_concat n k = (i,j)"
  and j: "Suc (j + m) = n i"
  shows "inf_concat n (k + Suc m) = (LEAST i'. i' > i \<and> 0 < n i', 0)"
proof -
  from j have "j + m < n i" by auto
  note res = inf_concat_add[OF res, OF this]
  show ?thesis by (simp add: res j)
qed

lemma inf_concat_surj_zero: assumes "0 < n i"
  shows "\<exists> k. inf_concat n k = (i,0)"
proof -
  {
    fix l
    have "\<forall> j. j < l \<and> 0 < n j \<longrightarrow> (\<exists> k. inf_concat n k = (j,0))"
    proof (induct l)
      case 0
      thus ?case by auto
    next
      case (Suc l)
      show ?case
      proof (intro allI impI, elim conjE)
        fix j
        assume j: "j < Suc l" and nj: "0 < n j"
        show "\<exists> k. inf_concat n k = (j, 0)"
        proof (cases "j < l")
          case True
          from Suc[THEN spec[of _ j]] True nj show ?thesis by auto
        next
          case False
          with j have j: "j = l" by auto
          show ?thesis
          proof (cases "\<exists> j'. j' < l \<and> 0 < n j'")
            case False
            have l: "(LEAST i. 0 < n i) = l"
            proof (rule Least_equality, rule nj[unfolded j])
              fix l'
              assume "0 < n l'"
              with False have "\<not> l' < l" by auto
              thus "l \<le> l'" by auto
            qed
            show ?thesis
              by (rule exI[of _ 0], simp add: l j)
          next
            case True
            then obtain lll where lll: "lll < l" and nlll: "0 < n lll" by auto 
            then obtain ll where l: "l = Suc ll" by (cases l, auto)   
            from lll l have lll: "lll = ll - (ll - lll)" by auto
            let ?l' = "LEAST d. 0 < n (ll - d)"
            have nl': "0 < n (ll - ?l')"
            proof (rule LeastI)
              show "0 < n (ll - (ll - lll))" using lll nlll by auto
            qed
            with Suc[THEN spec[of _ "ll - ?l'"]] obtain k where k:
              "inf_concat n k = (ll - ?l',0)" unfolding l by auto
            from nl' obtain off where off: "Suc (0 + off) = n (ll - ?l')" by (cases "n (ll - ?l')", auto)
            from inf_concat_step[OF k, OF off]
            have id: "inf_concat n (k + Suc off) = (LEAST i'. ll - ?l' < i' \<and> 0 < n i',0)" (is "_ = (?l,0)") .
            have ll: "?l = l" unfolding l
            proof (rule Least_equality)
              show "ll - ?l' < Suc ll \<and> 0 < n (Suc ll)" using nj[unfolded j l] by simp
            next
              fix l'
              assume ass: "ll - ?l' < l' \<and> 0 < n l'"
              show "Suc ll \<le> l'" 
              proof (rule ccontr)
                assume not: "\<not> ?thesis"
                hence "l' \<le> ll" by auto
                hence "ll = l' + (ll - l')" by auto
                then obtain k where ll: "ll = l' + k" by auto
                from ass have "l' + k - ?l' < l'" unfolding ll by auto
                hence kl': "k < ?l'" by auto
                have "0 < n (ll - k)" using ass unfolding ll by simp
                from Least_le[of "\<lambda> k. 0 < n (ll - k)", OF this] kl'
                show False by auto
              qed
            qed            
            show ?thesis unfolding j
              by (rule exI[of _ "k + Suc off"], unfold id ll, simp)
          qed
        qed
      qed
    qed
  }
  with assms show ?thesis by auto
qed

lemma inf_concat_surj: assumes j: "j < n i"
  shows "\<exists> k. inf_concat n k = (i,j)"
proof -
  from j have "0 < n i" by auto
  from inf_concat_surj_zero[of n, OF this]
  obtain k where "inf_concat n k = (i,0)" by auto
  from inf_concat_add[OF this, of j] j
  show ?thesis by auto
qed

lemma inf_concat_mono: assumes inf: "INFM i. n i > 0"
  and resk: "inf_concat n k = (i,j)"
  and reskp: "inf_concat n k' = (i',j')"
  and lt: "i < i'"
  shows "k < k'"
proof -
  note bounds = inf_concat_bounds[OF inf]
  {
    assume "k' \<le> k"
    hence "k = k' + (k - k')" by auto
    then obtain l where k: "k = k' + l" by auto
    have "i' \<le> fst (inf_concat n (k' + l))" 
    proof (induct l)
      case 0
      with reskp show ?case by auto
    next      
      case (Suc l)
      obtain i'' j'' where l: "inf_concat n (k' + l) = (i'',j'')" by force
      with Suc have one: "i' \<le> i''" by auto
      from bounds[OF l] have j'': "j'' < n i''" by auto
      show ?case 
      proof (cases "Suc j'' < n i''")
        case True
        show ?thesis by (simp add: l True one)
      next
        case False
        let ?i = "LEAST i'. i'' < i' \<and> 0 < n i'"
        from inf[unfolded INFM_nat] obtain k where "i'' < k \<and> 0 < n k" by auto
        from LeastI[of "\<lambda> k. i'' < k \<and> 0 < n k", OF this]
        have "i'' < ?i" by auto
        with one show ?thesis by (simp add: l False)
      qed
    qed      
    with resk k lt have False by auto
  }
  thus ?thesis by arith
qed

lemma inf_concat_Suc: assumes inf: "INFM i. n i > 0"
  and f: "\<And> i. f i (n i) = f (Suc i) 0"
  and resk: "inf_concat n k = (i,j)"
  and ressk: "inf_concat n (Suc k) = (i',j')"
  shows "f i' j' = f i (Suc j)"
proof - 
  note bounds = inf_concat_bounds[OF inf]
  from bounds[OF resk] have j: "j < n i" .
  show ?thesis
  proof (cases "Suc j < n i")
    case True
    with ressk resk
    show ?thesis by simp
  next
    case False
    let ?p = "\<lambda> i'. i < i' \<and> 0 < n i'"
    let ?i' = "LEAST i'. ?p i'"
    from False j have id: "Suc (j + 0) = n i" by auto
    from inf_concat_step[OF resk, OF id] ressk
    have i': "i' = ?i'" and j': "j' = 0" by auto
    from id have j: "Suc j = n i" by simp
    from inf[unfolded INFM_nat] obtain k where "?p k" by auto
    from LeastI[of ?p, OF this] have "?p ?i'" .
    hence "?i' = Suc i + (?i' - Suc i)" by simp
    then obtain d where ii': "?i' = Suc i + d" by auto
    from not_less_Least[of _ ?p, unfolded ii'] have d': "\<And> d'. d' < d \<Longrightarrow> n (Suc i + d') = 0" by auto
    have "f (Suc i) 0 = f ?i' 0" unfolding ii' using d'
    proof (induct d)
      case 0
      show ?case by simp
    next
      case (Suc d)
      hence "f (Suc i) 0 = f (Suc i + d) 0" by auto
      also have "... = f (Suc (Suc i + d)) 0"
        unfolding f[symmetric]
        using Suc(2)[of d] by simp
      finally show ?case by simp
    qed
    thus ?thesis unfolding i' j' j f by simp
  qed
qed

subsection {* map for option monad *}
fun mapM :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list option"
  where "mapM f [] = Some []"
      | "mapM f (x # xs) = do { y \<leftarrow> f x; ys \<leftarrow> mapM f xs; Some (y # ys)}"

lemma mapM_None: "(mapM f xs = None) = (\<exists> x \<in> set xs. f x = None)" 
proof (induct xs)
  case (Cons x xs) thus ?case 
    by (cases "f x", simp, cases "mapM f xs", auto)
qed simp

lemma mapM_Some: "mapM f xs = Some ys \<Longrightarrow> ys = map (\<lambda> x. the (f x)) xs \<and> (\<forall> x \<in> set xs. f x \<noteq> None)"
proof (induct xs arbitrary: ys)
  case (Cons x xs ys)   
  thus ?case 
    by (cases "f x", simp, cases "mapM f xs", auto)
qed simp

lemma mapM_Some_idx: assumes some: "mapM f xs = Some ys" and i: "i < length xs" 
  shows "\<exists> y. f (xs ! i) = Some y \<and> ys ! i = y"
proof -
  note m =  mapM_Some[OF some]
  from m[unfolded set_conv_nth] i have "f (xs ! i) \<noteq> None" by auto
  then obtain y where f: "f (xs ! i) = Some y" by auto
  have "f (xs ! i) = Some y \<and> ys ! i = y" unfolding m[THEN conjunct1] using i f by auto
  thus ?thesis ..
qed


lemma mapM_cong[fundef_cong]: assumes id1: "xs = ys" and id2: "\<And> x. x \<in> set ys \<Longrightarrow> f x = g x"
  shows "mapM f xs = mapM g ys" unfolding id1
  using id2 by (induct ys, auto)

lemma mapM_map: "mapM f xs = (if (\<forall> x \<in> set xs. f x \<noteq> None) then Some (map (\<lambda> x. the (f x)) xs) else None)"
proof (cases "mapM f xs")
  case None
  thus ?thesis using mapM_None by auto
next
  case (Some ys)
  with mapM_Some[OF Some] show ?thesis by auto
qed


lemma mapM_mono[partial_function_mono]: fixes C :: "'a \<Rightarrow> ('b \<Rightarrow> 'c option) \<Rightarrow> 'd option"
  assumes C: "\<And> y. mono_option (C y)"
  shows "mono_option (\<lambda> f. mapM (\<lambda> y. C y f) B)" 
proof (induct B)
  case Nil
  show ?case unfolding mapM.simps 
    by (rule option.const_mono)
next
  case (Cons b B)
  show ?case unfolding mapM.simps
    by (rule bind_mono[OF C bind_mono[OF Cons option.const_mono]])
qed


subsection {* Miscellaneous *}

lemma infinite_imp_elem: "\<not> finite A \<Longrightarrow> \<exists> x. x \<in> A"
  by (cases "A = {}", auto)

lemma inf_pigeon_hole_principle: assumes "\<forall> k :: nat. \<exists> i < n :: nat. f k i"
  shows "\<exists> i < n. \<forall> k. \<exists> k' \<ge> k. f k' i"
proof -
  have nfin: "~ finite (UNIV :: nat set)" by auto
  have fin: "finite ({i. i < n})" by auto
  from pigeonhole_infinite_rel[OF nfin fin] assms
  obtain i where i: "i < n" and nfin: "\<not> finite {a. f a i}" by auto
  show ?thesis 
  proof (intro exI conjI, rule i, intro allI)
    fix k
    have "finite {a. f a i \<and> a < k}" by auto
    with nfin have "\<not> finite ({a. f a i} - {a. f a i \<and> a < k})" by auto
    from infinite_imp_elem[OF this]
    obtain a where "f a i" and "a \<ge> k" by auto
    thus "\<exists> k' \<ge> k. f k' i" by force
  qed
qed

subsection {* if something holds infinitely often, get a function that points to these elements *}

locale infinite_hits =
  fixes p :: "nat \<Rightarrow> bool"
  assumes infinite: "INFM j. p j"
begin

lemma inf: "\<exists> j \<ge> i. p j" using infinite[unfolded INFM_nat_le] by auto

fun
  index :: "nat \<Rightarrow> nat"
where
  "index 0 = (LEAST n. p n)" |
  "index (Suc n) = (LEAST k. p k \<and> k > index n)"

lemma index_p: "p (index n)"
proof (induct n)
  case 0
  from inf obtain j where "p j" by auto
  with LeastI[of p j] show ?case by auto
next
  case (Suc n)
  from inf obtain k where "k \<ge> Suc (index n) \<and> p k" by auto
  with LeastI[of "\<lambda> k. p k \<and> k > index n" k] show ?case by auto
qed
  
lemma index_ordered: "index n < index (Suc n)"
proof -
  from inf obtain k where "k \<ge> Suc (index n) \<and> p k" by auto
  with LeastI[of "\<lambda> k. p k \<and> k > index n" k] show ?thesis by auto
qed
  
lemma index_not_p_between: assumes i1: "index n < i"
  and i2: "i < index (Suc n)"
  shows "\<not> p i"
proof -
  from not_less_Least[OF i2[simplified]] i1 show ?thesis by auto
qed

lemma index_ordered_le: assumes "i \<le> j" shows "index i \<le> index j"
proof - 
  from assms have "j = i + (j - i)" by auto
  then obtain k where j: "j = i + k" by auto
  have "index i \<le> index (i + k)"
  proof (induct k)
    case (Suc k)
    with index_ordered[of "i + k"]
    show ?case by auto
  qed simp
  thus ?thesis unfolding j .
qed

lemma index_surj: assumes "k \<ge> index l" shows "\<exists> i j. k = index i + j \<and> index i + j < index (Suc i)"
proof -
  from assms have "k = index l + (k - index l)" by auto
  then obtain u where k: "k = index l + u" by auto
  show ?thesis unfolding k
  proof (induct u)
    case 0
    show ?case
      by (intro exI conjI, rule refl, insert index_ordered[of l], simp)
  next
    case (Suc u)
    then obtain i j
      where lu: "index l + u = index i + j" and lt: "index i + j < index (Suc i)" by auto
    hence "index l + u < index (Suc i)" by auto
    show ?case
    proof (cases "index l + (Suc u) = index (Suc i)")
      case False
      show ?thesis
        by (rule exI[of _ i], rule exI[of _ "Suc j"], insert lu lt False, auto)
    next
      case True
      show ?thesis
        by (rule exI[of _ "Suc i"], rule exI[of _ 0], insert True index_ordered[of "Suc i"], auto)
    qed
  qed
qed

lemma index_ordered_less: assumes "i < j" shows "index i < index j"
proof - 
  from assms have "Suc i \<le> j" by auto
  from index_ordered_le[OF this]
  have "index (Suc i) \<le> index j" .
  with index_ordered[of i] show ?thesis by auto
qed
end

subsection {*Combinators*}

definition const :: "'a \<Rightarrow> 'b \<Rightarrow> 'a" where
  "const \<equiv> (\<lambda>x y. x)"

definition flip :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c)" where
  "flip f \<equiv> (\<lambda>x y. f y x)"
declare flip_def[simp]

lemma const_apply[simp]: "const x y = x"
  by (simp add: const_def)

lemma foldr_Cons[simp]:
  "foldr op # xs ys = xs @ ys"
  by (induct xs) simp_all

lemma foldl_flip_Cons[simp]:
  "foldl (flip op #) xs ys = rev ys @ xs"
  by (induct ys arbitrary: xs) simp_all

(*FIXME: already present as List.foldl_foldr, but
direction seems odd.*)
lemma foldr_flip_rev[simp]:
  "foldr (flip f) (rev xs) a = foldl f a xs"
  by (simp add: foldr_foldl)

(*FIXME: already present as List.foldr_foldr, but
direction seems odd.*)
lemma foldl_flip_rev[simp]:
  "foldl (flip f) a (rev xs) = foldr f xs a"
  by (simp add: foldl_foldr)

(*FIXME: available in HOL library?*)
interpretation o!: semigroup_add "op \<circ>"
  by (unfold_locales) (simp add: o_assoc)

lemma foldl_assoc:
  fixes b :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 55)
  assumes "\<And>f g h. f \<cdot> (g \<cdot> h) = f \<cdot> g \<cdot> h"
  shows "foldl op \<cdot> (x \<cdot> y) zs = x \<cdot> foldl op \<cdot> y zs"
proof -
  interpret semigroup_add b by (unfold_locales) (simp add: assms)
  show ?thesis by (simp add: foldl_assoc)
qed

lemma foldr_assoc:
  assumes "\<And>f g h. b (b f g) h = b f (b g h)"
  shows "foldr b xs (b y z) = b (foldr b xs y) z"
  using assms by (induct xs) simp_all

lemma foldl_foldr_o_id[symmetric]:
  "foldr op \<circ> fs id = foldl op \<circ> id fs"
  by (induct fs) (simp_all add: o.foldl_assoc[symmetric]
                           del: o_apply id_apply)

lemma foldr_o_o_id[simp]:
  "foldr (op \<circ> \<circ> f) xs id a = foldr f xs a"
  by (induct xs) simp_all


end
