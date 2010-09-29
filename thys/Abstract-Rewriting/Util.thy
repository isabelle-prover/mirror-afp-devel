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
imports Main
begin

text {* Some auxiliary lemmas that do not fit elsewhere. *}

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

subsection {* Properties of @{const take} and @{const drop} *}

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

text {* A tail recursive variant for @{term "concat(map f xs)"}. *}
primrec rev_append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where "rev_append [] ys = ys"
    | "rev_append (x#xs) ys = rev_append xs (x#ys)"

text {* @{const rev_append} is characterized through @{const rev} and @{const append}. *}
lemma rev_append_conv[simp]: "rev_append xs ys = rev xs @ ys"
  by (induct xs arbitrary: ys) auto
declare rev_append.simps[simp del]

(* FIXME: cf. List.concat_map ??? *)
primrec flat_map_aux :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'b list"
where "flat_map_aux f [] ys = rev ys"
    | "flat_map_aux f (x#xs) ys = flat_map_aux f xs (rev_append (f x) ys)"

lemma flat_map_aux_conv: "flat_map_aux f xs ys = rev ys @ concat(map f xs)"
  by (induct xs arbitrary: ys) auto

definition flat_map where "flat_map f xs \<equiv> flat_map_aux f xs []"

text {* @{const flat_map_aux} is no longer needed. *}
hide_const flat_map_aux 

lemma flat_map_concat_map_conv[simp]: "flat_map f xs = concat(map f xs)"
  unfolding flat_map_def flat_map_aux_conv by simp

text {* For code-generation, replace algebraically nice functions by
efficient and/or tail recursive ones. *}
lemma [code_inline]: "concat(map f xs) = flat_map f xs"
  by (rule flat_map_concat_map_conv[symmetric])

lemma flat_map_cong[fundef_cong]:
  fixes f g::"'a \<Rightarrow> 'b list"
  assumes "xs = ys" and "\<And>(x::'a). x \<in> set ys \<Longrightarrow> f x = g x"
  shows "flat_map f xs = flat_map g ys"
using map_cong[OF assms] by simp


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


subsection {* Miscellaneous *}

text {* Check whether a list of sets forms a partition, i.e.,
whether the sets are pairwise disjoint. *}
definition is_partition :: "('a set)list \<Rightarrow> bool"
where "is_partition cs = (\<forall>j<length cs. \<forall>i<j. cs!i \<inter> cs!j = {})"

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

lemma pigeonhole_infinite_rel:
assumes "~finite A" and "finite B" and "ALL a:A. EX b:B. R a b"
shows "EX b:B. ~finite{a:A. R a b}"
(* to come from Isabelle Finite_Set *)
oops


lemma infinite_imp_elem: "\<not> finite A \<Longrightarrow> \<exists> x. x \<in> A"
  by (cases "A = {}", auto)

lemma inf_pigeon_hole_principle: assumes "\<forall> k :: nat. \<exists> i < n :: nat. f k i"
  shows "\<exists> i < n. \<forall> k. \<exists> k' \<ge> k. f k' i"
(* alternative proof via pigeonhole_infinite_rel
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
*)
using assms 
proof (induct n arbitrary: f, simp)
  case (Suc n)
  show ?case
  proof (cases "\<forall> k. \<exists> k' \<ge> k. f k' n")
    case True
    thus ?thesis by auto
  next
    case False
    then obtain k where k: "\<forall> k' \<ge> k. \<not> f k' n" by auto
    let ?f = "\<lambda> k' i. f (k + k') i"
    have n: "\<forall> k'. \<exists> i < n. ?f k' i"
    proof
      fix k'
      have k': "k + k' \<ge> k" by simp
      from mp[OF spec[OF k] k'] have notN: "\<not> ?f k' n" by auto
      from spec[OF Suc(2), of "k + k'"] obtain i where i: "i < Suc n" and f:  "?f k' i"
        by auto
      with notN have "i \<noteq> n" by auto 
      with i have "i < n" by auto
      with f show "\<exists> i < n. ?f k' i" by auto
    qed
    from Suc(1)[OF n] obtain i where i: "i < n" and f: "\<forall> l. \<exists> k' \<ge> l. ?f k' i" by auto
    hence i: "i < Suc n" by auto
    show ?thesis
    proof (rule exI[of _ i], intro conjI allI)
      fix l
      from spec[OF f, of l] obtain k' where k': "(k' :: nat) \<ge> l" and f: "f (k + k') i" by auto
      from k' have "k + k' \<ge> l" by simp
      with f show "\<exists> k' \<ge> l. f k' i" by auto
    qed (simp add: i)
  qed
qed


locale infinite_hits =
  fixes p :: "nat \<Rightarrow> bool"
  assumes infinite: "\<forall> i. \<exists> j \<ge> i. p j"
begin

fun
  index :: "nat \<Rightarrow> nat"
where
  "index 0 = (LEAST n. p n)" |
  "index (Suc n) = (LEAST k. p k \<and> k > index n)"

lemma index_p: "p (index n)"
proof (induct n)
  case 0
  from infinite obtain j where "p j" by auto
  with LeastI[of p j] show ?case by auto
next
  case (Suc n)
  from infinite obtain k where "k \<ge> Suc (index n) \<and> p k" by auto
  with LeastI[of "\<lambda> k. p k \<and> k > index n" k] show ?case by auto
qed
  
lemma index_ordered: "index n < index (Suc n)"
proof -
  from infinite obtain k where "k \<ge> Suc (index n) \<and> p k" by auto
  with LeastI[of "\<lambda> k. p k \<and> k > index n" k] show ?thesis by auto
qed
  
lemma index_not_p_between: assumes i1: "index n < i"
  and i2: "i < index (Suc n)"
  shows "\<not> p i"
proof -
  from not_less_Least[OF i2[simplified]] i1 show ?thesis by auto
qed
end


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

end
