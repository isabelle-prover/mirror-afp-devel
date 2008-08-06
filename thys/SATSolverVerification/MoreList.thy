(*    Title:              SATSolverVerification/MoreList.thy
      ID:                 $Id: MoreList.thy,v 1.3 2008-08-06 15:27:21 filipmaric Exp $
      Author:             Filip Maric
*)

header{* MoreList *}

theory MoreList
imports Main Multiset
begin

text{* Theory contains some additional lemmas and functions for the
@{term List} datatype. Warning: some of these notions are obsolete
because they already exist in {\em List.thy} in similiar form. *}

(*********************************************************)
(*               last and butlast                        *)
(*********************************************************)
subsection{* @{term "last"} and @{term "butlast"} - last element of list and elements before it *}
lemma listEqualsButlastAppendLast: 
  assumes "list \<noteq> []"
  shows "list = (butlast list) @ [last list]"
using assms
by (induct list) auto

lemma lastListInList [simp]: 
  assumes "list \<noteq> []"
  shows "last list \<in> set list"
using assms
by (induct list) auto

lemma butlastIsSubset: 
  shows "set (butlast list) \<subseteq> set list"
by (induct list) (auto split: split_if_asm)

lemma setListIsSetButlastAndLast: 
  shows "set list \<subseteq> set (butlast list) \<union> {last list}" 
by (induct list) auto

lemma butlastAppend: 
  shows "butlast (list1 @ list2) = (if list2 = [] then butlast list1 else (list1 @ butlast list2))"
by (induct list1) auto

(*********************************************************)
(*                   removeAll                           *)
(*********************************************************)
subsection{* @{term removeAll} - element removal *}

text{* Function @{term "removeAll"} - removes all occurences of a given element from a list. *}

consts
removeAll :: "'a => 'a list => 'a list"
primrec
"removeAll x [] = []"
"removeAll x (h#t) = (if x=h then (removeAll x t) else h#(removeAll x t))"

lemma removeAll_set: 
  shows "set (removeAll a list) = set list - {a}"
by (induct list) auto

lemma removeAll_id:
  assumes "a \<notin> set list"
  shows "removeAll a list = list"
using assms
by (induct list) auto

lemma removeAll_append [simp]: 
  shows "removeAll x (l1 @ l2) = removeAll x l1 @ removeAll x l2"
by (induct l1) auto

lemma removeAll_multiset:
  assumes "distinct a" "x \<in> set a"
  shows "multiset_of a = {#x#} + multiset_of (removeAll x a)"
using assms
proof (induct a)
  case (Cons y a')
  thus ?case
  proof (cases "x = y")
    case True
    with `distinct (y # a')` `x \<in> set (y # a')`
    have "\<not>  x \<in> set a'"
      by auto
    hence "removeAll x a' = a'"
      by (rule removeAll_id)
    with `x = y` show ?thesis
      by (simp add: union_commute)
  next
    case False
    with `x \<in> set (y # a')` 
    have "x \<in> set a'"
      by simp
    with `distinct (y # a')`
    show ?thesis
      using Cons(1)
      by (auto simp add: union_assoc)
  qed
qed simp

lemma removeAll_map:
  assumes "\<forall> x y. x \<noteq> y \<longrightarrow> f x \<noteq> f y"
  shows "removeAll (f x) (map f a) = map f (removeAll x a)"
using assms
by (induct a arbitrary: x) auto

 
(*********************************************************)
(*                   uniq                                *)
(*********************************************************)
subsection{* @{term uniq} - no duplicate elements. *}
text{* @{term "(uniq list)"} holds iff there are no repeated elements
in a list.  Obsolete: same as @{term "distinct"} in {\em List.thy}. *}

consts
uniq :: "'a list => bool"
primrec
"uniq [] = True"
"uniq (h#t) = (h \<notin> set t \<and> uniq t)"

lemma uniqAppend: 
  assumes "uniq (l1 @ l2)" 
  shows "uniq l1" "uniq l2"
using assms
by (induct l1) auto

lemma uniqAppendIff: 
  "uniq (l1 @ l2) = (uniq l1 \<and> uniq l2 \<and> set l1 \<inter> set l2 = {})" (is "?lhs = ?rhs")
by (induct l1) auto

lemma uniqAppendElement: 
  assumes "uniq l" 
  shows "e \<notin> set l = uniq (l @ [e])"
using assms
by (induct l) (auto split: split_if_asm)

lemma uniqImpliesNotLastMemButlast:
  assumes "uniq l"
  shows "last l \<notin> set (butlast l)"
proof (cases "l = []")
  case True
  thus ?thesis
    using assms
    by simp
next
  case False
  hence "l = butlast l @ [last l]"
    by (rule listEqualsButlastAppendLast)
  moreover
  with `uniq l` 
  have "uniq (butlast l)"
    using uniqAppend[of "butlast l" "[last l]"]
    by simp
  ultimately
  show ?thesis
    using assms
    using uniqAppendElement[of "butlast l" "last l"]
    by simp
qed

lemma uniqButlastNotUniqListImpliesLastMemButlast: 
  assumes "uniq (butlast l)" "\<not> uniq l" 
  shows "last l \<in> set (butlast l)"
proof (cases "l = []")
  case True
  thus ?thesis
    using assms
    by auto
next
  case False
  hence "l = butlast l @ [(last l)]"
    by (rule listEqualsButlastAppendLast)
  thus ?thesis
    using assms
    using uniqAppendElement[of "butlast l" "last l"]
    by auto
qed

lemma uniqRemdups:
  shows "uniq (remdups x)"
by (induct x) auto

(*********************************************************)
(*                   firstPos                            *)
(*********************************************************)
subsection {* @{term firstPos} - first position of an element *}
text{* @{term "firstPos"} returns the zero-based index of the first
  occurence of an element int a list, or the length of the list if the
  element does not occur. *}

consts firstPos :: "'a => 'a list => nat"
primrec
"firstPos a [] = 0"
"firstPos a (h # t) = (if a = h then 0 else 1 + (firstPos a t))"

lemma firstPosEqualZero:
  shows "(firstPos a (m # M') = 0) = (a = m)"
by (induct M') auto

lemma firstPosLeLength: 
  assumes "a \<in> set l"
  shows "firstPos a l < length l"
using assms
by (induct l) auto

lemma firstPosAppend: 
  assumes "a \<in> set l" 
  shows "firstPos a l = firstPos a (l @ l')"
using assms
by (induct l) auto

lemma firstPosAppendNonMemberFirstMemberSecond: 
  assumes "a \<notin> set l1" and  "a \<in> set l2"
  shows "firstPos a (l1 @ l2) = length l1 + firstPos a l2"
using assms
by (induct l1) auto

lemma firstPosDomainForElements: 
  shows "(0 \<le> firstPos a l \<and> firstPos a l < length l) = (a \<in> set l)" (is "?lhs = ?rhs")
  by (induct l) auto

lemma firstPosEqual: 
  assumes "a \<in> set l" and "b \<in> set l" 
  shows "(firstPos a l = firstPos b l) = (a = b)" (is "?lhs = ?rhs")
proof-
  {
    assume "?lhs"
    hence "?rhs"
      using assms
    proof (induct l)
      case (Cons m l')
      {
	assume "a = m"
	have "b = m"
	proof-
	  from `a = m` 
	  have "firstPos a (m # l') = 0"
	    by simp
	  with Cons 
	  have "firstPos b (m # l') = 0"
	    by simp
	  with `b \<in> set (m # l')` 
	  have "firstPos b (m # l') = 0"
	    by simp
	  thus ?thesis
	    using firstPosEqualZero[of "b" "m" "l'"]
	    by simp
	qed
	with `a = m` 
	have ?case
	  by simp
      }
      note * = this
      moreover
      {
	assume "b = m"
	have "a = m"
	proof-
	  from `b = m` 
	  have "firstPos b (m # l') = 0"
	    by simp
	  with Cons 
	  have "firstPos a (m # l') = 0"
	    by simp
	  with `a \<in> set (m # l')` 
	  have "firstPos a (m # l') = 0"
	    by simp
	  thus ?thesis
	    using firstPosEqualZero[of "a" "m" "l'"]
	    by simp
	qed
	with `b = m` 
	have ?case
	  by simp
      }
      note ** = this
      moreover
      {
	assume Q: "a \<noteq> m" "b \<noteq> m"
	from Q `a \<in> set (m # l')`
	have "a \<in> set l'"
	  by simp
	from Q `b \<in> set (m # l')`
	have "b \<in> set l'"
	  by simp
	from `a \<in> set l'` `b \<in> set l'` Cons
	have "firstPos a l' = firstPos b l'"
	  by (simp split: split_if_asm)
	with Cons 
	have ?case
	  by (simp split: split_if_asm)
      }
      note *** = this
      moreover
      {
	have "a = m \<or> b = m \<or> a \<noteq> m \<and> b \<noteq> m"
	  by auto
      }
      ultimately
      show ?thesis
      proof (cases "a = m")
	case True
	thus ?thesis
	  by (rule *)
      next
	case False
	thus ?thesis
	proof (cases "b = m")
	  case True
	  thus ?thesis
	    by (rule **)
	next
	  case False
	  with `a \<noteq> m` show ?thesis
	    by (rule ***)
	qed
      qed
    qed simp
  } thus ?thesis
    by auto
qed

(*********************************************************)
(*                   preceeds                            *)
(*********************************************************)
subsection{* @{term preceeds} - ordering relation induced by @{term firstPos} *}
definition preceeds :: "'a => 'a => 'a list => bool"
where
"preceeds a b l == (a \<in> set l \<and> b \<in> set l \<and>  firstPos a l <= firstPos b l)"

lemma noElementsPreceedsFirstElement: 
  assumes "a \<noteq> b"
  shows "\<not> preceeds a b (b # list)"
proof-
  {
    assume "preceeds a b (b # list)"
    hence "a \<in> set (b # list)" "firstPos a (b # list) <= 0"
      unfolding preceeds_def
      by (auto split: split_if_asm)
    hence  "firstPos a (b # list) = 0"
      by auto
    with `a \<noteq> b` 
    have False
      using firstPosEqualZero[of "a" "b" "list"]
      by simp
  }
  thus ?thesis
    by auto
qed

lemma preceedsAppend: 
  assumes "preceeds a b l" 
  shows "preceeds a b (l @ l')"
proof-
  from `preceeds a b l` 
  have "a \<in> set l" "b \<in> set l" "firstPos a l \<le> firstPos b l"
    unfolding preceeds_def
    by (auto split: split_if_asm)
  thus ?thesis
    using firstPosAppend[of "a" "l" "l'"]
    using firstPosAppend[of "b" "l" "l'"]
    unfolding preceeds_def
    by simp
qed

lemma preceedsMemberHeadMemberTail: 
  assumes "a \<in> set l1" and "b \<notin> set l1" and "b \<in> set l2"
  shows "preceeds a b (l1 @ l2)"
proof-
  from `a \<in> set l1` 
  have "firstPos a l1 < length l1"
    using firstPosLeLength [of "a" "l1"]
    by simp
  moreover
  from `a \<in> set l1` 
  have "firstPos a (l1 @ l2) = firstPos a l1"
    using firstPosAppend[of "a" "l1" "l2"]
    by simp
  moreover
  from `b \<notin> set l1` `b \<in> set l2`
  have "firstPos b (l1 @ l2) = length l1 + firstPos b l2"
    by (rule firstPosAppendNonMemberFirstMemberSecond)
  moreover
  have "firstPos b l2 \<ge> 0"
    by auto
  ultimately
  show ?thesis
    unfolding preceeds_def
    using `a \<in> set l1` `b \<in> set l2`
    by simp
qed


lemma preceedsReflexivity: 
  assumes "a \<in> set l"
  shows "preceeds a a l"
using assms
unfolding preceeds_def
by simp

lemma preceedsTransitivity: 
  assumes 
  "a \<in> set l" and "b \<in> set l" and "c \<in> set l"
  "preceeds a b l" and "preceeds b c l" 
  shows 
  "preceeds a c l"
using assms
unfolding preceeds_def
by auto

lemma preceedsAntisymmetry: 
  assumes
  "a \<in> set l" and "b \<in> set l" and
  "preceeds a b l" and "preceeds b a l"
  shows
  "a = b"
proof-
  from assms
  have "firstPos a l = firstPos b l"
    unfolding preceeds_def
    by auto
  thus ?thesis
    using firstPosEqual[of "a" "l" "b"]
    using assms
    by simp
qed

lemma preceedsTotalOrder: 
  assumes "a \<in> set l" and "b \<in> set l"
  shows "a=b \<or> preceeds a b l \<or> preceeds b a l"
using assms
unfolding preceeds_def
by auto

lemma preceedsMap:
  assumes "preceeds a b list" and "\<forall> x y. x \<noteq> y \<longrightarrow> f x \<noteq> f y"
  shows "preceeds (f a) (f b) (map f list)"
using assms
proof (induct list)
  case (Cons l list')
    {
      assume "a = l"
      have ?case
      proof-
	from `a = l` 
	have "firstPos (f a) (map f (l # list')) = 0"
	  using firstPosEqualZero[of "f a" "f l" "map f list'"]
	  by simp
	moreover
	from `preceeds a b (l # list')` 
	have "b \<in> set (l # list')"
	  unfolding preceeds_def
	  by simp
	hence "f b \<in> set (map f (l # list'))"
	  by auto
	moreover
	hence "firstPos (f b) (map f (l # list')) \<ge>  0"
	  by auto
	ultimately
	show ?thesis
	  using `a = l` `f b \<in> set (map f (l # list'))`
	  unfolding preceeds_def
	  by simp
      qed
    }
    moreover
    {
      assume "b = l"
      with `preceeds a b (l # list')`
      have "a = l"
	using noElementsPreceedsFirstElement[of "a" "l" "list'"]
	by auto
      from `a = l` `b = l` 
      have ?case
	unfolding preceeds_def
	by simp
    }
    moreover
    {
      assume "a \<noteq> l" "b \<noteq> l"
      with `\<forall> x y. x \<noteq> y \<longrightarrow> f x \<noteq> f y`
      have "f a \<noteq> f l" "f b \<noteq> f l"
	by auto
      from `preceeds a b (l # list')` 
      have "b \<in> set(l # list')" "a \<in> set(l # list')" "firstPos a (l # list') \<le> firstPos b (l # list')"
	unfolding preceeds_def
	by auto
      with `a \<noteq> l` `b \<noteq> l` 
      have "a \<in> set list'" "b \<in> set list'" "firstPos a list' \<le> firstPos b list'"
	by auto
      hence "preceeds a b list'"
	unfolding preceeds_def
	by simp
      with Cons
      have "preceeds (f a) (f b) (map f list')"
	by simp
      with `f a \<noteq> f l` `f b \<noteq> f l`
      have ?case
	unfolding preceeds_def
	by auto
    }
    ultimately 
    show ?case
      by auto
next
  case Nil
  thus ?case
    unfolding preceeds_def
    by simp
qed

lemma preceedsFilter: 
  assumes "preceeds a b list" and "f a" and "f b"
  shows "preceeds a b (filter f list)"
using assms
proof(induct list)
  case (Cons l list')
  show ?case
  proof-
    from `preceeds a b (l # list')` 
    have "a \<in> set(l # list')" "b \<in> set(l # list')" "firstPos a (l # list') \<le> firstPos b (l # list')"
      unfolding preceeds_def
      by auto
    from `f a` `a \<in> set(l # list')` 
    have "a \<in> set(filter f (l # list'))"
      by auto
    moreover
    from `f b` `b \<in> set(l # list')` 
    have "b \<in> set(filter f (l # list'))"
      by auto
    moreover
    have "firstPos a (filter f (l # list')) \<le> firstPos b (filter f (l # list'))"
    proof- 
      {
	assume "a = l"
	with `f a` 
	have "firstPos a (filter f (l # list')) = 0"
	  by auto
	with `b \<in> set (filter f (l # list'))` 
	have ?thesis
	  by auto
      }
      moreover
      {
	assume "b = l"
	with `preceeds a b (l # list')`
	have "a = b"
	  using noElementsPreceedsFirstElement[of "a" "b" "list'"]
	  by (auto simp del: preceeds_def)
	hence ?thesis
	  by (simp add: preceedsReflexivity)
      }
      moreover
      {
	assume "a \<noteq> l" "b \<noteq> l"
	with `preceeds a b (l # list')` 
	have "firstPos a list' \<le> firstPos b list'"
	  unfolding preceeds_def
	  by auto
	moreover
	from `a \<noteq> l` `a \<in> set (l # list')` 
	have "a \<in> set list'"
	  by simp
	moreover
	from `b \<noteq> l` `b \<in> set (l # list')` 
	have "b \<in> set list'"
	  by simp
	ultimately
	have "preceeds a b list'"
	  unfolding preceeds_def
	  by simp
	with `f a` `f b` Cons(1)
	have "preceeds a b (filter f list')"
	  by (simp del: preceeds_def)
	with `a \<noteq> l` `b \<noteq> l`
	have ?thesis
	  unfolding preceeds_def
	  by auto
      }
      ultimately
      show ?thesis
	by blast
    qed
    ultimately
    show ?thesis
      unfolding preceeds_def
      by simp
  qed
qed simp

definition
"preceedsOrder list == {(a, b). preceeds a b list \<and> a \<noteq> b}"

lemma wellFoundedPreceedsOrder:
  shows "wf (preceedsOrder list)"
unfolding wf_eq_minimal
proof-
  show "\<forall>Q a. a:Q \<longrightarrow> (\<exists> aMin \<in> Q. \<forall> a'. (a', aMin) \<in> preceedsOrder list \<longrightarrow> a' \<notin> Q)"
  proof-
    {
      fix a :: "'a" and Q::"'a set"
      assume "a \<in> Q"
      let ?listQ = "filter (\<lambda> x. x \<in> Q) list"
      have "\<exists> aMin \<in> Q. \<forall> a'. (a', aMin) \<in> preceedsOrder list \<longrightarrow> a' \<notin> Q"
      proof (cases "?listQ = []")
	case True
	let ?aMin = a
	have "\<forall> a'. (a', ?aMin) \<in> preceedsOrder list \<longrightarrow> a' \<notin> Q"
	proof-
	  {
	    fix a'
	    assume "(a', ?aMin) \<in> preceedsOrder list"
	    hence "a \<in> set list"
	      unfolding preceedsOrder_def
	      unfolding preceeds_def
	      by simp
	    with `a \<in> Q`
	    have "a \<in> set ?listQ"
	      by (induct list) auto
	    with `?listQ = []` 
	    have "False"
	      by simp
	    hence "a' \<notin> Q"
	      by simp
	  }
	  thus ?thesis
	    by simp
	qed
	with `a \<in> Q` obtain aMin where "aMin \<in> Q" "\<forall> a'. (a', aMin) \<in> preceedsOrder list \<longrightarrow> a' \<notin> Q"
	  by auto
	thus ?thesis
	  by auto
      next
	case False
	let ?aMin = "hd ?listQ"
	from False 
	have "?aMin \<in> Q"
	  by (induct list) auto
	have "\<forall> a'. (a', ?aMin) \<in> preceedsOrder list \<longrightarrow> a' \<notin> Q"
	proof
	  fix a'
	  {
	    assume "(a', ?aMin) \<in> preceedsOrder list"
	    hence "a' \<in> set list" "preceeds a' ?aMin list" "a' \<noteq> ?aMin"
	      unfolding preceedsOrder_def
	      unfolding preceeds_def
	      by auto
	    have "a' \<notin> Q"
	    proof-
	      {
		assume "a' \<in> Q"
		with `?aMin \<in> Q` `preceeds a' ?aMin list`
		have "preceeds a' ?aMin ?listQ"
		    using preceedsFilter[of "a'" "?aMin" "list" "\<lambda> x. x \<in> Q"]
		    by blast
		from `a' \<noteq> ?aMin` 
		have "\<not> preceeds a' (hd ?listQ) (hd ?listQ # tl ?listQ)"
		  by (rule noElementsPreceedsFirstElement)
		with False `preceeds a' ?aMin ?listQ`
		have "False"
		  by auto
	      }
	      thus ?thesis
		by auto
	    qed
	  } thus "(a', ?aMin) \<in> preceedsOrder list \<longrightarrow> a' \<notin> Q"
	    by simp
	qed
	with `?aMin \<in> Q`
	show ?thesis
	  ..
      qed
    }
    thus ?thesis
      by simp
  qed
qed


(*********************************************************)
(*                   prefix                              *)
(*********************************************************)
subsection{* @{term isPrefix} - prefixes of list. *}
text{* Check if a list is a prefix of another list. Obsolete: similiar
notion is defined in {\em List\_prefixes.thy}. *}

consts
isPrefix :: "'a list => 'a list => bool"
defs
isPrefix_def: "isPrefix p t == \<exists> s. p @ s = t"

lemma prefixIsSubset:
  assumes "isPrefix p l"
  shows "set p \<subseteq> set l"
using assms
unfolding isPrefix_def
by auto

lemma uniqListImpliesUniqPrefix:
assumes "isPrefix p l" and "uniq l"
shows "uniq p"
proof-
  from `isPrefix p l` obtain s
    where "p @ s = l"
    unfolding isPrefix_def
    by auto
  with `uniq l`
  show ?thesis
    using uniqAppend[of "p" "s"]
    by simp
qed

lemma firstPosPrefixElement: 
  assumes "isPrefix p l" and "a \<in> set p"
  shows "firstPos a p = firstPos a l"
proof-
  from `isPrefix p l` obtain s
    where "p @ s = l"
    unfolding isPrefix_def
    by auto
  with `a \<in> set p` 
  show ?thesis
    using firstPosAppend[of "a" "p" "s"]
    by simp
qed

lemma laterInPrefixRetainsPreceeds: 
  assumes 
  "isPrefix p l" and "preceeds a b l" and "b \<in> set p"
  shows 
  "preceeds a b p"
proof-
  from `isPrefix p l` obtain s
    where "p @ s = l"
    unfolding isPrefix_def
    by auto
  from `preceeds a b l` 
  have "a \<in> set l" "b \<in> set l" "firstPos a l \<le> firstPos b l"
    unfolding preceeds_def
    by (auto split: split_if_asm)

  from `p @ s = l` `b \<in> set p` 
  have "firstPos b l = firstPos b p"
    using firstPosAppend [of "b" "p" "s"]
    by simp

  show ?thesis
  proof (cases "a \<in> set p")
    case True
    from `p @ s = l` `a \<in> set p` 
    have "firstPos a l = firstPos a p"
      using firstPosAppend [of "a" "p" "s"]
      by simp

    from `firstPos a l = firstPos a p` `firstPos b l = firstPos b p` `firstPos a l \<le> firstPos b l`
    `a \<in> set p` `b \<in> set p`
    show ?thesis
      unfolding preceeds_def
      by simp
  next
    case False
    from `a \<notin> set p` `a \<in> set l` `p @ s = l`
    have "a \<in> set s"
      by auto
    with `a \<notin> set p` `p @ s = l`
    have "firstPos a l = length p + firstPos a s"
      using firstPosAppendNonMemberFirstMemberSecond[of "a" "p" "s"]
      by simp
    moreover
    from `b \<in> set p` 
    have "firstPos b p < length p"
      by (rule firstPosLeLength)
    ultimately
    show ?thesis
      using `firstPos b l = firstPos b p` `firstPos a l \<le> firstPos b l`
      by simp
  qed
qed

(*********************************************************)
(*                       List diff                       *)
(*********************************************************)
subsection{* @{term "list_diff"} - the set difference operation on two lists. *}

consts 
list_diff :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
primrec 
"list_diff x [] = x"
"list_diff x (y#ys) = list_diff (removeAll y x) ys"

lemma [simp]: 
  shows "list_diff [] y = []"
by (induct y) auto

lemma [simp]: 
  shows "list_diff (x # xs) y = (if x \<in> set y then list_diff xs y else x # list_diff xs y)"
proof (induct y arbitrary: xs)
  case (Cons y ys)
  thus ?case
  proof (cases "x = y")
    case True
    thus ?thesis
      by simp
  next
    case False
    thus ?thesis
    proof (cases "x \<in> set ys")
      case True
      thus ?thesis
	using Cons
	by simp
    next
      case False
      thus ?thesis
	using Cons
	by simp
    qed
  qed
qed simp

lemma listDiffIff:
  shows "(x \<in> set a \<and> x \<notin> set b) = (x \<in> set (list_diff a b))"
by (induct a) auto

lemma listDiffDoubleRemoveAll: 
  assumes "x \<in> set a"
  shows "list_diff b a = list_diff b (x # a)"
using assms
by (induct b) auto

lemma removeAllListDiff[simp]:
  shows "removeAll x (list_diff a b) = list_diff (removeAll x a) b"
by (induct a) auto

lemma listDiffRemoveAllNonMember:
  assumes "x \<notin> set a"
  shows "list_diff a b = list_diff a (removeAll x b)"
using assms
proof (induct b arbitrary: a)
  case (Cons y b')
  from `x \<notin> set a` 
  have "x \<notin> set (removeAll y a)"
    by (auto simp add: removeAll_set)
  thus ?case
  proof (cases "x = y")
    case False
    thus ?thesis
      using Cons(2)
      using Cons(1)[of "removeAll y a"]
      using `x \<notin> set (removeAll y a)`
      by auto
  next
    case True
    thus ?thesis
      using Cons(1)[of "removeAll y a"]
      using `x \<notin> set a`
      using `x \<notin> set (removeAll y a)`
      by (auto simp add: removeAll_id)
  qed
qed simp

lemma listDiffMap: 
  assumes "\<forall> x y. x \<noteq> y \<longrightarrow> f x \<noteq> f y"
  shows "map f (list_diff a b) = list_diff (map f a) (map f b)"
using assms
by (induct b arbitrary: a) (auto simp add: removeAll_map)

(*********************************************************)
(*                       Remdups                         *)
(*********************************************************)
subsection{* @{term remdups} - removing duplicates *}
lemma remdupsRemoveAllCommute[simp]:
  shows "remdups (removeAll a list) = removeAll a (remdups list)"
by (induct list) (auto simp add: removeAll_set)

lemma remdupsAppend: 
  shows "remdups (a @ b) = remdups (list_diff a b) @ remdups b"
proof (induct a)
  case (Cons x a')
  thus ?case
    using listDiffIff[of "x" "a'" "b"]
    by auto
qed simp

lemma remdupsAppendSet: 
  shows "set (remdups (a @ b)) = set (remdups a @ remdups (list_diff b a))"
proof (induct a)
  case Nil
  thus ?case
    by auto
next
  case (Cons x a')
  thus ?case
  proof (cases "x \<in> set a'")
    case True
    thus ?thesis
      using Cons
      using listDiffDoubleRemoveAll[of "x" "a'" "b"]
      by simp
  next
    case False
    thus ?thesis
    proof (cases "x \<in> set b")
      case True
      show ?thesis
      proof-
	have "set (remdups (x # a') @ remdups (list_diff b (x # a'))) = 
	  set (x # remdups a' @ remdups (list_diff b (x # a')))"
	  using `x \<notin> set a'`
	  by auto
	also have "\<dots> = set (x # remdups a' @ remdups (list_diff (removeAll x b) a'))"
	  by auto
	also have "\<dots> = set (x # remdups a' @ remdups (removeAll x (list_diff b a')))"
	  by simp
	also have "\<dots> = set (remdups a' @ x # remdups (removeAll x (list_diff b a')))"
	  by simp
	also have "\<dots> = set (remdups a' @ x # removeAll x (remdups (list_diff b a')))"
	  by (simp only: remdupsRemoveAllCommute)
	also have "\<dots> = set (remdups a') \<union> set (x # removeAll x (remdups (list_diff b a')))"
	  by simp
	also have "\<dots> = set (remdups a') \<union> {x} \<union> set (removeAll x (remdups (list_diff b a')))"
	  by simp
	also have "\<dots> = set (remdups a') \<union> set (remdups (list_diff b a'))"
	proof-
	  from `x \<notin> set a'` `x \<in> set b`
	  have "x \<in> set (list_diff b a')"
	    using listDiffIff[of "x" "b" "a'"]
	    by simp
	  hence "x \<in> set (remdups (list_diff b a'))"
	    by auto
	  thus ?thesis
	    by (auto simp add: removeAll_set)
	qed
	also have "\<dots> = set (remdups (a' @ b))"
	  using Cons(1)
	  by simp
	also have "\<dots> = set (remdups ((x # a') @ b))"
	  using `x \<in> set b`
	  by simp
	finally show ?thesis
	  by simp
      qed
    next
      case False
      thus ?thesis
      proof-
	have "set (remdups (x # a') @ remdups (list_diff b (x # a'))) = 
	  set (x # (remdups a') @ remdups (list_diff b (x # a')))"
	  using `x \<notin> set a'`
	  by auto
	also have "\<dots> = set (x # remdups a' @ remdups (list_diff (removeAll x b) a'))"
	  by auto
	also have "\<dots> = set (x # remdups a' @ remdups (list_diff b a'))"
	  using `x \<notin> set b`
	  by (auto simp add: removeAll_id)
	also have "\<dots> = {x} \<union> set (remdups (a' @ b))"
	  using Cons(1)
	  by simp
	also have "\<dots> = set (remdups ((x # a') @ b))"
	  by auto
	finally show ?thesis
	  by simp
      qed
    qed
  qed
qed

lemma remdupsAppendMultiSet: 
  shows "multiset_of (remdups (a @ b)) = multiset_of (remdups a @ remdups (list_diff b a))"
proof (induct a)
  case Nil
  thus ?case
    by auto
next
  case (Cons x a')
  thus ?case
  proof (cases "x \<in> set a'")
    case True
    thus ?thesis
      using Cons
      using listDiffDoubleRemoveAll[of "x" "a'" "b"]
      by simp
    next
    case False
    thus ?thesis
    proof (cases "x \<in> set b")
      case True
      show ?thesis
      proof-
	have "multiset_of (remdups (x # a') @ remdups (list_diff b (x # a'))) = 
	  multiset_of (x # remdups a' @ remdups (list_diff b (x # a')))"
	proof-
	  have "remdups (x # a') = x # remdups a'"
	    using `x \<notin> set a'`
	    by auto
	  thus ?thesis
	    by simp
	qed
	also have "\<dots> = multiset_of (x # remdups a' @ remdups (list_diff (removeAll x b) a'))"
	  by auto
	also have "\<dots> = multiset_of (x # remdups a' @ remdups (removeAll x (list_diff b a')))"
	  by simp
	also have "\<dots> = multiset_of (remdups a' @ x # remdups (removeAll x (list_diff b a')))"
	  by (simp add: union_assoc)
	also have "\<dots> = multiset_of (remdups a' @ x # removeAll x (remdups (list_diff b a')))"
	  by (simp only: remdupsRemoveAllCommute)
	also have "\<dots> = multiset_of (remdups a') + multiset_of (x # removeAll x (remdups (list_diff b a')))"
	  by simp
	also have "\<dots> = multiset_of (remdups a') + {#x#} + multiset_of (removeAll x (remdups (list_diff b a')))"
	  by (simp add: union_assoc) (simp add: union_commute)
	also have "\<dots> = multiset_of (remdups a') + multiset_of (remdups (list_diff b a'))"
	proof-
	  from `x \<notin> set a'` `x \<in> set b`
	  have "x \<in> set (list_diff b a')"
	    using listDiffIff[of "x" "b" "a'"]
	    by simp
	  hence "x \<in> set (remdups (list_diff b a'))"
	    by auto
	  thus ?thesis
	    using removeAll_multiset[of "remdups (list_diff b a')" "x"]
	    by (simp add: union_assoc)
	qed
	also have "\<dots> = multiset_of (remdups (a' @ b))"
	  using Cons(1)
	  by simp
	also have "\<dots> = multiset_of (remdups ((x # a') @ b))"
	  using `x \<in> set b`
	  by simp
	finally show ?thesis
	  by simp
      qed
    next
      case False
      thus ?thesis
      proof-
	have "multiset_of (remdups (x # a') @ remdups (list_diff b (x # a'))) = 
	  multiset_of (x # remdups a' @ remdups (list_diff b (x # a')))"
	proof-
	  have "remdups (x # a') = x # remdups a'"
	    using `x \<notin> set a'`
	    by auto
	  thus ?thesis
	    by simp
	qed
	also have "\<dots> = multiset_of (x # remdups a' @ remdups (list_diff (removeAll x b) a'))"
	  by auto
	also have "\<dots> = multiset_of (x # remdups a' @ remdups (list_diff b a'))"
	  using `x \<notin> set b`
	  using removeAll_id[of "x" "b"]
	  by simp
	also have "\<dots> = {#x#} + multiset_of (remdups (a' @ b))"
	  using Cons(1)
	  by (simp add: union_commute)
	also have "\<dots> = multiset_of (remdups ((x # a') @ b))"
	  using `x \<notin> set a'` `x \<notin> set b`
	  by (auto simp add: union_commute)
	finally show ?thesis
	  by simp
      qed
    qed
  qed
qed
 

(*********************************************************)
(*                       Levi                            *)
(*********************************************************)
subsection{* Levi's lemma *}

text{* Obsolete: these two lemmas are already proved as @{term
append_eq_append_conv2} and @{term append_eq_Cons_conv}. *}

lemma FullLevi: 
  shows "(x @ y = z @ w) = 
                (x = z \<and> y = w \<or> 
                (\<exists> t. z @ t = x \<and> t @ y = w) \<or> 
                (\<exists> t. x @ t = z \<and> t @ w = y))" (is "?lhs = ?rhs")
proof
  assume "?rhs"
  thus "?lhs"
    by auto
next
  assume "?lhs"
  thus "?rhs"
  proof (induct x arbitrary: z)
    case (Cons a x')
    show ?case
    proof (cases "z = []")
      case True
      with `(a # x') @ y = z @ w`
      obtain t where "z @ t = a # x'" "t @ y = w"
	by auto
      thus ?thesis
	by auto
    next
      case False
      then obtain b and z' where "z = b # z'"
	by (auto simp add: neq_Nil_conv)
      with `(a # x') @ y = z @ w`
      have "x' @ y = z' @ w" "a = b"
	by auto
      with Cons(1)[of "z'"]
      have "x' = z' \<and> y = w \<or> (\<exists>t. z' @ t = x' \<and> t @ y = w) \<or> (\<exists>t. x' @ t = z' \<and> t @ w = y)"
	by simp
      with `a = b` `z = b # z'` 
      show ?thesis
	by auto
    qed
  qed simp
qed

lemma SimpleLevi:
  shows "(p @ s = a # list) = 
             ( p = [] \<and> s = a # list \<or> 
              (\<exists> t. p = a # t \<and> t @ s = list))"
by (induct p) auto

end
