(* Author: Tobias Nipkow *)

theory List_Index imports Main begin

text{* \noindent
This theory defines three functions for finding the index of items in a list:
\begin{description}
\item[@{text "find_index P xs"}] finds the index of the first element in
 @{text xs} that satisfies @{text P}.
\item[@{text "index xs x"}] finds the index of the first occurrence of
 @{text x} in @{text xs}.
\item[@{text "last_index xs x"}] finds the index of the last occurrence of
 @{text x} in @{text xs}.
\end{description}
All functions return @{term "length xs"} if @{text xs} does not contain a
suitable element.

The argument order of @{text find_index} follows the function of the same
name in the Haskell standard library. For @{text index} (and @{text
last_index}) the order is intentionally reversed: @{text index} maps
lists to a mapping from elements to their indices, almost the inverse of
function @{text nth}. *}

primrec find_index :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
"find_index _ [] = 0" |
"find_index P (x#xs) = (if P x then 0 else find_index P xs + 1)"

definition index :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"index xs = (\<lambda>a. find_index (\<lambda>x. x=a) xs)"

definition last_index :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"last_index xs x =
 (let i = index (rev xs) x; n = size xs
  in if i = n then i else n - (i+1))"

lemma find_index_le_size: "find_index P xs <= size xs"
by(induct xs) simp_all

lemma index_le_size: "index xs x <= size xs"
by(simp add: index_def find_index_le_size)

lemma last_index_le_size: "last_index xs x <= size xs"
by(simp add: last_index_def Let_def index_le_size)

lemma index_Nil[simp]: "index [] a = 0"
by(simp add: index_def)

lemma index_Cons[simp]: "index (x#xs) a = (if x=a then 0 else index xs a + 1)"
by(simp add: index_def)

lemma index_append: "index (xs @ ys) x =
  (if x : set xs then index xs x else size xs + index ys x)"
by (induct xs) simp_all

lemma index_conv_size_if_notin[simp]: "x \<notin> set xs \<Longrightarrow> index xs x = size xs"
by (induct xs) auto

lemma find_index_eq_size_conv:
  "size xs = n \<Longrightarrow> (find_index P xs = n) = (ALL x : set xs. ~ P x)"
by(induct xs arbitrary: n) auto

lemma size_eq_find_index_conv:
  "size xs = n \<Longrightarrow> (n = find_index P xs) = (ALL x : set xs. ~ P x)"
by(metis find_index_eq_size_conv)

lemma index_size_conv: "size xs = n \<Longrightarrow> (index xs x = n) = (x \<notin> set xs)"
by(auto simp: index_def find_index_eq_size_conv)

lemma size_index_conv: "size xs = n \<Longrightarrow> (n = index xs x) = (x \<notin> set xs)"
by (metis index_size_conv)

lemma last_index_size_conv:
  "size xs = n \<Longrightarrow> (last_index xs x = n) = (x \<notin> set xs)"
apply(auto simp: last_index_def index_size_conv)
apply(drule length_pos_if_in_set)
apply arith
done

lemma size_last_index_conv:
  "size xs = n \<Longrightarrow> (n = last_index xs x) = (x \<notin> set xs)"
by (metis last_index_size_conv)

lemma find_index_less_size_conv:
  "(find_index P xs < size xs) = (EX x : set xs. P x)"
by (induct xs) auto

lemma index_less_size_conv:
  "(index xs x < size xs) = (x \<in> set xs)"
by(auto simp: index_def find_index_less_size_conv)

lemma last_index_less_size_conv:
  "(last_index xs x < size xs) = (x : set xs)"
by(simp add: last_index_def Let_def index_size_conv length_pos_if_in_set
        del:length_greater_0_conv)

lemma index_less[simp]:
  "x : set xs \<Longrightarrow> size xs <= n \<Longrightarrow> index xs x < n"
apply(induct xs) apply auto
apply (metis index_less_size_conv less_eq_Suc_le less_trans_Suc)
done

lemma last_index_less[simp]:
  "x : set xs \<Longrightarrow> size xs <= n \<Longrightarrow> last_index xs x < n"
by(simp add: last_index_less_size_conv[symmetric])

lemma last_index_Cons: "last_index (x#xs) y =
  (if x=y then
      if x \<in> set xs then last_index xs y + 1 else 0
   else last_index xs y + 1)"
using index_le_size[of "rev xs" y]
apply(auto simp add: last_index_def index_append Let_def)
apply(simp add: index_size_conv)
done

lemma last_index_append: "last_index (xs @ ys) x =
  (if x : set ys then size xs + last_index ys x
   else if x : set xs then last_index xs x else size xs + size ys)"
by (induct xs) (simp_all add: last_index_Cons last_index_size_conv)

lemma last_index_Snoc[simp]:
  "last_index (xs @ [x]) y =
  (if x=y then size xs
   else if y : set xs then last_index xs y else size xs + 1)"
by(simp add: last_index_append last_index_Cons)

lemma nth_find_index: "find_index P xs < size xs \<Longrightarrow> P(xs ! find_index P xs)"
by (induct xs) auto

lemma nth_index[simp]: "x \<in> set xs \<Longrightarrow> xs ! index xs x = x"
by (induct xs) auto

lemma nth_last_index[simp]: "x \<in> set xs \<Longrightarrow> xs ! last_index xs x = x"
by(simp add:last_index_def index_size_conv Let_def rev_nth[symmetric])

lemma index_eq_index_conv[simp]: "x \<in> set xs \<or> y \<in> set xs \<Longrightarrow>
  (index xs x = index xs y) = (x = y)"
by (induct xs) auto

lemma last_index_eq_index_conv[simp]: "x \<in> set xs \<or> y \<in> set xs \<Longrightarrow>
  (last_index xs x = last_index xs y) = (x = y)"
by (induct xs) (auto simp:last_index_Cons)

lemma inj_on_index: "inj_on (index xs) (set xs)"
by (simp add:inj_on_def)

lemma inj_on_last_index: "inj_on (last_index xs) (set xs)"
by (simp add:inj_on_def)

lemma index_conv_takeWhile: "index xs x = size(takeWhile (\<lambda>y. x\<noteq>y) xs)"
by(induct xs) auto

lemma index_take: "\<lbrakk> x \<in> set xs; index xs x >= i \<rbrakk> \<Longrightarrow> x \<notin> set(take i xs)"
apply(subst (asm) index_conv_takeWhile)
apply(subgoal_tac "set(take i xs) <= set(takeWhile (op \<noteq> x) xs)")
 apply(blast dest: set_takeWhileD)
apply(metis set_take_subset_set_take takeWhile_eq_take)
done

lemma last_index_drop:
  "\<lbrakk> x \<in> set xs; last_index xs x < i \<rbrakk> \<Longrightarrow> x \<notin> set(drop i xs)"
apply(subgoal_tac "set(drop i xs) = set(take (size xs - i) (rev xs))")
 apply(simp add: last_index_def index_take Let_def split:split_if_asm)
apply (metis rev_drop set_rev)
done

end
