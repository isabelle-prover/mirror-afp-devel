(*    Title:              SATSolverVerification/MyList.thy
      ID:                 $Id: MoreList.thy,v 1.2 2008-07-27 14:23:32 lsf37 Exp $
      Author:             Filip Maric
      Maintainer:         Filip Maric <filip at matf.bg.ac.yu>
*)

header{* MoreList *}

theory MoreList
imports Main Multiset
begin
text{* Theory contains some additional lemmas and functions for the @{term List} datatype. *}

(*********************************************************)
(*                      mem                              *)
(*********************************************************)
subsection{* @{text mem} - list membership *}
lemma nonEmptyList: 
  assumes "x mem list"
  shows  "list \<noteq> []"
using assms
by (induct list) auto

lemma memAppend: 
"x mem (list1 @ list2) = (x mem list1 \<or> x mem list2)"
by (induct list1) auto

lemma nonemptyIsHeadTail: 
  assumes "list \<noteq> []"
  shows "\<exists> x list'. list = x # list'"
using assms
by (induct list) auto

(*********************************************************)
(*               last \<and> butlast                         *)
(*********************************************************)
subsection{* @{term "last"} and @{term "butlast"} - last element of list and elements before it *}
lemma listEqualsButlastAppendLast: 
  assumes "list \<noteq> []"
  shows "list = (butlast list) @ [last list]"
using assms
by (induct list) auto

lemma lastListMemList [simp]: 
  assumes "list \<noteq> []"
  shows "last list mem list"
using assms
by (induct list) auto

lemma memButlastImpliesMemList: 
  assumes "x mem (butlast list)"
  shows "x mem list"
using assms
by (induct list) (auto split: split_if_asm)

lemma memListImpliesMemButlastOrLast: 
  assumes "x mem list" 
  shows "x mem butlast list \<or> x = last list"
using assms
by (induct list) auto

lemma butlastAppend: 
  shows "butlast (list1 @ list2) = (if list2 = [] then butlast list1 else (list1 @ butlast list2))"
by (induct list1) auto

(*********************************************************)
(*                   remove                              *)
(*********************************************************)
subsection{* @{term remove} - element removal *}

text{* Function @{term "remove"} removes all occurences of a given element from a list *}

consts
remove :: "'a => 'a list => 'a list"
primrec
"remove x [] = []"
"remove x (h#t) = (if x=h then (remove x t) else h#(remove x t))"

lemma removeAppend [simp]: 
  shows "remove x (l1 @ l2) = remove x l1 @ remove x l2"
by (induct l1) auto

lemma memRemoveImpliesMemList:
  assumes "x mem remove a l"
  shows "x mem l"
using assms
by (induct l) (auto split: split_if_asm)

lemma memRemoveImpliesNotRemoved:
  assumes "x mem remove a l"
  shows "x \<noteq> a"
using assms
by (induct l) (auto split: split_if_asm)

lemma removedNotMemRemove: 
  shows "\<not> x mem (remove x l)"
by (induct l) auto

lemma memListImpliesMemRemoveOrRemoved:
  assumes "x mem l" 
  shows "x mem remove a l \<or> x=a"
using assms
by (induct l) auto

lemma memRemoveIffMemListAndNotRemoved: 
  shows "x mem remove e l = (x mem l \<and> x \<noteq> e)"
by (induct l) auto

lemma removeNonMember:
  assumes "\<not> a mem list"
  shows "remove a list = list"
using assms
by (induct list) auto

(* TODO: remove - easy consequence of memRemoveImpliesMemList and memAppend *)
lemma memRemoveL1AppendL2: 
  assumes "x mem remove a l1 @ l2"
  shows "x mem (l1 @ l2)"
using assms
by (induct l1) (auto split: split_if_asm)

lemma setRemove: "set list \<subseteq> {a} \<union> set (remove a list)"
by (induct list) auto

lemma setRemoveSubset:
  shows "set (remove x a) \<subseteq> set a"
by (induct a) auto

lemma setRemoveIff:
  assumes "x mem a"
  shows "{x} \<union> set (remove x a) = set a" (is "?lhs = ?rhs")
proof
  show "?rhs \<subseteq> ?lhs"
    by (induct a) auto
next
  show "?lhs \<subseteq> ?rhs"
    using assms
  proof (induct a)
    case (Cons y a')
    thus ?case
    proof (cases "x = y")
      case True
      thus ?thesis
	using setRemoveSubset[of "y" "a'"]
	by auto
    next
      case False
      with `x mem y # a'` 
      have "x mem a'"
	by simp
      hence "{x} \<union> set (remove x a') \<subseteq> set a'"
	using Cons(1)
	by simp
      thus ?thesis
	by auto
    qed
  qed simp
qed

lemma multisetRemoveIff:
  assumes "distinct a" "x mem a"
  shows "multiset_of a = {#x#} + multiset_of (remove x a)"
using assms
proof (induct a)
  case (Cons y a')
  thus ?case
  proof (cases "x = y")
    case True
    with `distinct (y # a')` `x mem y # a'`
    have "\<not>  x mem a'"
      by (auto iff: mem_iff)
    hence "remove x a' = a'"
      by (rule removeNonMember)
    with `x = y` show ?thesis
      by (simp add: union_commute)
  next
    case False
    with `x mem y # a'` 
    have "x mem a'"
      by simp
    with `distinct (y # a')`
    show ?thesis
      using Cons(1)
      by (auto iff: mem_iff simp add: union_assoc)
  qed
qed simp
 
lemma removeMap:
  assumes "\<forall> x y. x \<noteq> y \<longrightarrow> f x \<noteq> f y"
  shows "remove (f x) (map f a) = map f (remove x a)"
using assms
by (induct a arbitrary: x) auto

(*********************************************************)
(*                   uniq                                *)
(*********************************************************)
subsection{* @{term uniq} - no duplicate elements *}
text{* @{term "(uniq list)"} holds iff there are no repeated elements in a list *}
consts
uniq :: "'a list => bool"
primrec
"uniq [] = True"
"uniq (h#t) = (\<not> h mem t \<and> uniq t)"

lemma uniqAppend: 
  assumes "uniq (l1 @ l2)" 
  shows "uniq l1" "uniq l2"
using assms
by (induct l1) (auto simp add: memAppend)

lemma uniqAppendIff: 
  "uniq (l1 @ l2) = (uniq l1 \<and> uniq l2 \<and> set l1 \<inter> set l2 = {})" (is "?lhs = ?rhs")
by (induct l1) (auto simp add: mem_iff)

lemma uniqAppendElement: 
  assumes "uniq l" 
  shows "\<not> e mem l = uniq (l @ [e])"
using assms
by (induct l) (auto split: split_if_asm simp add: memAppend)

lemma uniqImpliesNotLastMemButlast:
  assumes "uniq l"
  shows "\<not> last l mem butlast l"
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
  with `uniq l` have "uniq (butlast l)"
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
  shows "last l mem butlast l"
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
by (induct x) (auto simp add: mem_iff)

(*********************************************************)
(*                   intLength                           *)
(*********************************************************)
subsection{* @{term intLength} - length of a list *}

consts intLength :: "'a list => int"
primrec 
"intLength [] = 0"
"intLength (h#t) = 1 + intLength(t)"

lemma intLengthGeqZero:
  shows "intLength l >= 0"
by (induct "l") auto

lemma intLengthNonEmptyGeq1:
  assumes "list \<noteq> []"
  shows "intLength list >= 1"
using assms
by (induct list) (auto simp add:intLengthGeqZero)

lemma intLengthAppend:
  shows "intLength (a @ b) = intLength a + intLength b"
by (induct "a") auto

(*********************************************************)
(*                   firstPos                            *)
(*********************************************************)
subsection {* @{term firstPos} - index of an element *}

text{* @{term "firstPos"} returns the zero-based index of the first occurence of an element
  int a list, or -1 if the element does not occur *}

consts firstPos_aux :: "'a => 'a list => int"
primrec
"firstPos_aux a [] = 0"
"firstPos_aux a (h # t) = (if a = h then 0 else 1 + (firstPos_aux a t))"

definition  firstPos :: "'a => 'a list => int"
where
firstPos_def: "firstPos a l == (if a mem l then (firstPos_aux a l) else -1)"


lemma firstPos_auxGeqZero: "firstPos_aux a list >= 0"
by (induct list) auto

lemma firstPosEqualZero:
  shows "(firstPos a (m # M') = 0) = (a = m)"
proof
  assume "firstPos a (m # M') = 0"
  hence "a mem (m # M')" "firstPos_aux a (m # M') = 0"
    unfolding firstPos_def
    by (auto split: split_if_asm)
  {
    assume "a \<noteq> m"
    with `firstPos_aux a (m # M') = 0`
    have "1 + firstPos_aux a M' = 0"
      by simp
    hence False
      using firstPos_auxGeqZero[of "a" "M'"]
      by simp
  }
  thus "a = m"
    by auto
next
  assume "a = m"
  thus "firstPos a (m # M') = 0"
    unfolding firstPos_def
    by auto
qed

lemma firstPosGeqZero:
  assumes "a mem list" 
  shows "firstPos a list >= 0"
using assms
unfolding firstPos_def
by (auto simp add:firstPos_auxGeqZero)

lemma firstPosLeqLength: 
  assumes "a mem l"
  shows "firstPos a l < intLength l"
using assms
unfolding firstPos_def
proof (induct l)
  case (Cons m l')
  thus ?case
  proof (cases "a = m")
    case True
    thus ?thesis
      using intLengthGeqZero[of "l'"]
      by simp
  next
    case False
    with `a mem (m # l')`
    have "a mem l'"
      by simp
    with Cons(1)
    have "firstPos a l' < intLength l'"
      unfolding firstPos_def
      by simp
    thus ?thesis
      unfolding firstPos_def
      using False
      by auto
  qed
qed simp

lemma firstPosAppend: 
  assumes "a mem l" 
  shows "firstPos a l = firstPos a (l @ l')"
using assms
unfolding firstPos_def
by (induct l) (auto simp add: memAppend)

lemma firstPosAppendNonMemberFirstMemberSecond: 
  assumes "\<not> a mem l1" and  "a mem l2"
  shows "firstPos a (l1 @ l2) = intLength l1 + firstPos a l2"
using assms
proof (induct l1)
  case (Cons m l1')
  from `\<not> a mem m # l1'` have "\<not>  a mem l1'" "a \<noteq> m"
    by (auto split: split_if_asm)
  with `a mem l2` Cons(1)
  have "firstPos a (l1' @ l2) = intLength l1' + firstPos a l2"
    by simp
  moreover
  from `a \<noteq> m` `a mem l2` have 
    "firstPos a ((m # l1') @ l2) = 1 + firstPos a (l1' @ l2)"
    unfolding firstPos_def
    by (auto simp add: memAppend)
  ultimately
  show ?case
    by simp
qed simp

lemma firstPosDomainForElements: 
  shows "(firstPos a l >= 0 \<and> firstPos a l < intLength l) = a mem l" (is "?lhs = ?rhs")
proof
  assume "?lhs"
  thus "?rhs"
    unfolding firstPos_def
    by (auto split: split_if_asm)
next
  assume "?rhs"
  thus "?lhs"
    using firstPosGeqZero[of "a" "l"]
    using firstPosLeqLength[of "a" "l"]
    by auto
qed

lemma firstPosEqual: 
  assumes "a mem l" and "b mem l" and "firstPos a l = firstPos b l"
  shows "a = b"
using assms
unfolding firstPos_def
proof (induct l)
case (Cons m l')
hence P: "firstPos_aux a (m # l') = firstPos_aux b (m # l')"
  by (simp split: split_if_asm)
{
  assume "a = m"
  have "b = m"
  proof-
    from `a = m` have "firstPos_aux a (m # l') = 0"
      by simp
    with P have "firstPos_aux b (m # l') = 0"
      by simp
    with `b mem (m # l')` have
      "firstPos b (m # l') = 0"
      unfolding firstPos_def
      by simp
    thus ?thesis
    using firstPosEqualZero[of "b" "m" "l'"]
    by simp
  qed
  with `a = m` have ?case
    by simp
}
note * = this
moreover
{
  assume "b = m"
  have "a = m"
  proof-
    from `b = m` have "firstPos_aux b (m # l') = 0"
      by simp
    with P have "firstPos_aux a (m # l') = 0"
      by simp
    with `a mem (m # l')` have
      "firstPos a (m # l') = 0"
      unfolding firstPos_def
      by simp
    thus ?thesis
    using firstPosEqualZero[of "a" "m" "l'"]
    by simp
  qed
  with `b = m` have ?case
    by simp
}
note ** = this
moreover
{
  assume Q: "a \<noteq> m" "b \<noteq> m"
  from Q `a mem (m # l')`
  have "a mem l'"
    by simp
  from Q `b mem (m # l')`
  have "b mem l'"
    by simp
  from `a mem l'` `b mem l'` P Q
  have "firstPos_aux a l' = firstPos_aux b l'"
    by (simp split: split_if_asm)
  with Cons Q have ?case
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
(*********************************************************)
(*                   preceeds                            *)
(*********************************************************)
subsection{* @{term preceeds} - ordering relation induced by @{term firstPos} *}
definition preceeds :: "'a => 'a => 'a list => bool"
where
"preceeds a b l == (a mem l \<and> b mem l \<and>  firstPos a l <= firstPos b l)"

lemma noElementsPreceedsFirstElement: 
  assumes "a \<noteq> b"
  shows "\<not> preceeds a b (b # list)"
proof-
  {
    assume "preceeds a b (b # list)"
    hence "a mem (b # list)" "firstPos a (b # list) <= 0"
      unfolding preceeds_def
      unfolding firstPos_def
      by (auto split: split_if_asm)
    hence  "firstPos a (b # list) = 0"
      using firstPosGeqZero[of "a" "b # list"]
      by simp
    with `a \<noteq> b` have False
      using firstPosEqualZero[of "a" "b" "list"]
      by (simp del: firstPos_def)
  }
  thus ?thesis
    by auto
qed

lemma preceedsAppend: 
  assumes "preceeds a b l" 
  shows "preceeds a b (l @ l')"
proof-
  from `preceeds a b l` have "a mem l" "b mem l" "firstPos a l \<le> firstPos b l"
    unfolding preceeds_def
    by (auto split: split_if_asm)
  thus ?thesis
    using firstPosAppend[of "a" "l" "l'"]
    using firstPosAppend[of "b" "l" "l'"]
    unfolding preceeds_def
    by (simp add:memAppend)
qed

lemma preceedsMemberHeadMemberTail: 
  assumes "a mem l1" and "\<not> b mem l1" and "b mem l2"
  shows "preceeds a b (l1 @ l2)"
proof-
  from `a mem l1` have "firstPos a l1 < intLength l1"
    using firstPosLeqLength [of "a" "l1"]
    by simp
  moreover
  from `a mem l1` have "firstPos a (l1 @ l2) = firstPos a l1"
    using firstPosAppend[of "a" "l1" "l2"]
    by simp
  moreover
  from `\<not> b mem l1` `b mem l2`
  have "firstPos b (l1 @ l2) = intLength l1 + firstPos b l2"
    by (rule firstPosAppendNonMemberFirstMemberSecond)
  moreover
  from `b mem l2` 
  have "firstPos b l2 >= 0"
    by (rule firstPosGeqZero)
  ultimately
  show ?thesis
    unfolding preceeds_def
    using `a mem l1` `b mem l2`
    by (simp add: memAppend)
qed


lemma preceedsReflexivity: 
  assumes "a mem l"
  shows "preceeds a a l"
using assms
unfolding preceeds_def
by simp

lemma preceedsTransitivity: 
  assumes 
  "a mem l" and "b mem l" and "c mem l"
  "preceeds a b l" and "preceeds b c l" 
  shows 
  "preceeds a c l"
using assms
unfolding preceeds_def
by auto

lemma preceedsAntisymmetry: 
  assumes
  "a mem l" and "b mem l" and
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
  assumes "a mem l" and "b mem l"
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
	from `a = l` have "firstPos (f a) (map f (l # list')) = 0"
	  using firstPosEqualZero[of "f a" "f l" "map f list'"]
	  by simp
	moreover
	from `preceeds a b (l # list')` 
	have "b mem l # list'"
	  unfolding preceeds_def
	  by simp
	hence "f b mem map f (l # list')"
	  by (auto simp add: mem_iff)
	hence "firstPos (f b) (map f (l # list')) >= 0"
	  using firstPosGeqZero[of "f b" "map f (l # list')"]
	  by simp
	ultimately
	show ?thesis
	  using `a = l` `f b mem map f (l # list')`
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
      have "b mem l # list'" "a mem l # list'" "firstPos a (l # list') <= firstPos b (l # list')"
	unfolding preceeds_def
	by auto
      with `a \<noteq> l` `b \<noteq> l` have "a mem list'" "b mem list'" "firstPos a list' <= firstPos b list'"
	unfolding firstPos_def
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
	unfolding firstPos_def
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
    have "a mem l # list'" "b mem l # list'" "firstPos a (l # list') <= firstPos b (l # list')"
      unfolding preceeds_def
      by auto
    from `f a` `a mem l # list'` have "a mem filter f (l # list')"
      by (auto simp add: mem_iff)
    moreover
    from `f b` `b mem (l # list')` have "b mem filter f (l # list')"
      by (auto simp add: mem_iff)
    moreover
    have "firstPos a (filter f (l # list')) <= firstPos b (filter f (l # list'))"
    proof- 
      {
	assume "a = l"
	with `f a` have "firstPos a (filter f (l # list')) = 0"
	  unfolding firstPos_def
	  by auto
	with `b mem (filter f (l # list'))` have ?thesis
	  using firstPosGeqZero[of "b" "(filter f (l # list'))"]
	  by simp
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
	with `preceeds a b (l # list')` have "firstPos a list' <= firstPos b list'"
	  unfolding preceeds_def
	  unfolding firstPos_def
	  by auto
	moreover
	from `a \<noteq> l` `a mem l # list'` have "a mem list'"
	  by simp
	moreover
	from `b \<noteq> l` `b mem l # list'` have "b mem list'"
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
	  unfolding firstPos_def
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
	    hence "a mem list"
	      unfolding preceedsOrder_def
	      unfolding preceeds_def
	      by simp
	    with `a \<in> Q`
	    have "a mem ?listQ"
	      by (induct list) auto
	    with `?listQ = []` have "False"
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
	from False have "?aMin \<in> Q"
	  by (induct list) auto
	have "\<forall> a'. (a', ?aMin) \<in> preceedsOrder list \<longrightarrow> a' \<notin> Q"
	proof
	  fix a'
	  {
	    assume "(a', ?aMin) \<in> preceedsOrder list"
	    hence "a' mem list" "preceeds a' ?aMin list" "a' \<noteq> ?aMin"
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
		from `a' \<noteq> ?aMin` have "\<not> preceeds a' (hd ?listQ) (hd ?listQ # tl ?listQ)"
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
subsection{* @{term prefix} - prefixes of list *}

text{* Check if a list is a prefix of another list *}

consts
isPrefix :: "'a list => 'a list => bool"
defs
isPrefix_def: "isPrefix p t == \<exists> s. p @ s = t"

lemma memPrefixImpliesMemList:
  assumes "isPrefix p l" and "x mem p" 
  shows "x mem l"
using assms
unfolding isPrefix_def
by (auto simp add: memAppend)

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
  assumes "isPrefix p l" and "a mem p"
  shows "firstPos a p = firstPos a l"
proof-
  from `isPrefix p l` obtain s
    where "p @ s = l"
    unfolding isPrefix_def
    by auto
  with `a mem p` 
  show ?thesis
    using firstPosAppend[of "a" "p" "s"]
    by simp
qed

lemma laterInPrefixRetainsPreceeds: 
  assumes 
  "isPrefix p l" and "preceeds a b l" and "b mem p"
  shows 
  "preceeds a b p"
proof-
  from `isPrefix p l` obtain s
    where "p @ s = l"
    unfolding isPrefix_def
    by auto
  from `preceeds a b l` have "a mem l" "b mem l" "firstPos a l \<le> firstPos b l"
    unfolding preceeds_def
    by (auto split: split_if_asm)

  from `p @ s = l` `b mem p` have "firstPos b l = firstPos b p"
    using firstPosAppend [of "b" "p" "s"]
    by simp

  show ?thesis
  proof (cases "a mem p")
    case True
    from `p @ s = l` `a mem p` have "firstPos a l = firstPos a p"
      using firstPosAppend [of "a" "p" "s"]
      by simp

    from `firstPos a l = firstPos a p` `firstPos b l = firstPos b p` `firstPos a l \<le> firstPos b l`
    `a mem p` `b mem p`
    show ?thesis
      unfolding preceeds_def
      by simp
  next
    case False
    from `\<not> a mem p` `a mem l` `p @ s = l`
    have "a mem s"
      by (auto simp add: memAppend)
    with `\<not> a mem p` `p @ s = l`
    have "firstPos a l = intLength p + firstPos a s"
      using firstPosAppendNonMemberFirstMemberSecond[of "a" "p" "s"]
      by simp
    moreover
    from `a mem s` have "firstPos a s >= 0"
      by (rule firstPosGeqZero)
    moreover
    from `b mem p` 
    have "firstPos b p < intLength p"
      by (rule firstPosLeqLength)
    ultimately
    show ?thesis
      using `firstPos b l = firstPos b p` `firstPos a l \<le> firstPos b l`
      by simp
  qed
qed


(*********************************************************)
(*                       List diff                       *)
(*********************************************************)
subsection{* @{term "list_diff"} - difference of lists *}

consts 
list_diff :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
primrec 
"list_diff x [] = x"
"list_diff x (y#ys) = list_diff (remove y x) ys"

lemma [simp]: 
  shows "list_diff [] y = []"
by (induct y) auto

lemma [simp]: 
  shows "list_diff (x # xs) y = (if x mem y then list_diff xs y else x # list_diff xs y)"
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
    proof (cases "x mem ys")
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
  shows "(x mem a \<and> \<not> x mem b) = x mem list_diff a b"
by (induct a) auto

lemma listDiffDoubleRemove: 
  assumes "x mem a"
  shows "list_diff b a = list_diff b (x # a)"
using assms
by (induct b) auto

lemma removeListDiff[simp]:
  shows "remove x (list_diff a b) = list_diff (remove x a) b"
by (induct a) auto

lemma listDiffRemoveNonMember:
  assumes "\<not> x mem a"
  shows "list_diff a b = list_diff a (remove x b)"
using assms
proof (induct b arbitrary: a)
  case (Cons y b')
  from `\<not> x mem a` have "\<not> x mem remove y a"
    using setRemoveSubset[of "y" "a"]
    by (auto iff: mem_iff)
  thus ?case
  proof (cases "x = y")
    case False
    thus ?thesis
      using Cons(2)
      using Cons(1)[of "remove y a"]
      using `\<not> x mem (remove y a)`
      by auto
  next
    case True
    thus ?thesis
      using Cons(1)[of "remove y a"]
      using `\<not> x mem a`
      using `\<not> x mem remove y a`
      by (auto simp add: removeNonMember)
  qed
qed simp

lemma listDiffMap: 
  assumes "\<forall> x y. x \<noteq> y \<longrightarrow> f x \<noteq> f y"
  shows "map f (list_diff a b) = list_diff (map f a) (map f b)"
using assms
by (induct b arbitrary: a) (auto simp add: removeMap)

(*********************************************************)
(*                       Remdups                         *)
(*********************************************************)
subsection{* @{term remdups} - removing duplicates *}
lemma remdupsRemoveCommute[simp]:
  shows "remdups (remove a list) = remove a (remdups list)"
proof (induct list)
  case (Cons l list')
  thus ?case
  proof (cases "a = l")
    case True
    with Cons show ?thesis
      by auto
  next
    case False
    with Cons
    show ?thesis
    proof-
      {
	assume "l \<in> set list'"
	with `a \<noteq> l`
	have "l \<in> set (remove a list')"
	  using setRemove[of "list'" "a"]
	  by auto
      }
      moreover
      {
	assume "l \<notin> set list'"
	with `a \<noteq> l`
	have "l \<notin> set (remove a list')"
	  using memRemoveImpliesMemList[of "l" "a" "list'"]
	  by (auto simp add: mem_iff)
      }
      ultimately 
      show ?thesis
	using Cons
	by auto
    qed
  qed
qed simp

lemma remdupsAppend: 
  shows "remdups (a @ b) = remdups (list_diff a b) @ remdups b"
proof (induct a)
  case (Cons x a')
  thus ?case
  proof (cases "x mem b")
    case True
    thus ?thesis
      using Cons
      by (simp add: mem_iff)
  next
    case False
    thus ?thesis
    proof (cases "x mem a'")
      case True
      from `x mem a'` `\<not> x mem b` 
      show ?thesis
	using Cons
	using listDiffIff[of "x" "a'" "b"]
	by (auto iff: mem_iff)
    next
      case False
      thus ?thesis
	using Cons
	using listDiffIff[of "x" "a'" "b"]
	by (auto iff: mem_iff)
    qed
  qed
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
  proof (cases "x mem a'")
    case True
    thus ?thesis
      using Cons
      using listDiffDoubleRemove[of "x" "a'" "b"]
      by (simp add: mem_iff)
  next
    case False
    thus ?thesis
    proof (cases "x mem b")
      case True
      show ?thesis
      proof-
	have "set (remdups (x # a') @ remdups (list_diff b (x # a'))) = 
	  set (x # remdups a' @ remdups (list_diff b (x # a')))"
	  using `\<not> x mem a'`
	  by auto
	also have "\<dots> = set (x # remdups a' @ remdups (list_diff (remove x b) a'))"
	  by auto
	also have "\<dots> = set (x # remdups a' @ remdups (remove x (list_diff b a')))"
	  by simp
	also have "\<dots> = set (remdups a' @ x # remdups (remove x (list_diff b a')))"
	  by simp
	also have "\<dots> = set (remdups a' @ x # remove x (remdups (list_diff b a')))"
	  by (simp only: remdupsRemoveCommute)
	also have "\<dots> = set (remdups a') \<union> set (x # remove x (remdups (list_diff b a')))"
	  by simp
	also have "\<dots> = set (remdups a') \<union> {x} \<union> set (remove x (remdups (list_diff b a')))"
	  by simp
	also have "\<dots> = set (remdups a') \<union> set (remdups (list_diff b a'))"
	proof-
	  from `\<not> x mem a'` `x mem b`
	  have "x mem list_diff b a'"
	    using listDiffIff[of "x" "b" "a'"]
	    by simp
	  hence "x mem remdups (list_diff b a')"
	    by (auto iff: mem_iff)
	  thus ?thesis
	    using setRemoveIff[of "x" "remdups (list_diff b a')"]
	    by auto
	qed
	also have "\<dots> = set (remdups (a' @ b))"
	  using Cons(1)
	  by simp
	also have "\<dots> = set (remdups ((x # a') @ b))"
	  using `x mem b`
	  by (simp add: mem_iff)
	finally show ?thesis
	  by simp
      qed
    next
      case False
      thus ?thesis
      proof-
	have "set (remdups (x # a') @ remdups (list_diff b (x # a'))) = 
	  set (x # (remdups a') @ remdups (list_diff b (x # a')))"
	  using `\<not> x mem a'`
	  by auto
	also have "\<dots> = set (x # remdups a' @ remdups (list_diff (remove x b) a'))"
	  by auto
	also have "\<dots> = set (x # remdups a' @ remdups (list_diff b a'))"
	  using `\<not> x mem b`
	  using removeNonMember[of "x" "b"]
	  by simp
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
  proof (cases "x mem a'")
    case True
    thus ?thesis
      using Cons
      using listDiffDoubleRemove[of "x" "a'" "b"]
      by (simp add: mem_iff)
    next
    case False
    thus ?thesis
    proof (cases "x mem b")
      case True
      show ?thesis
      proof-
	have "multiset_of (remdups (x # a') @ remdups (list_diff b (x # a'))) = 
	  multiset_of (x # remdups a' @ remdups (list_diff b (x # a')))"
	proof-
	  have "remdups (x # a') = x # remdups a'"
	    using `\<not> x mem a'`
	    by (auto iff: mem_iff)
	  thus ?thesis
	    by simp
	qed
	also have "\<dots> = multiset_of (x # remdups a' @ remdups (list_diff (remove x b) a'))"
	  by auto
	also have "\<dots> = multiset_of (x # remdups a' @ remdups (remove x (list_diff b a')))"
	  by simp
	also have "\<dots> = multiset_of (remdups a' @ x # remdups (remove x (list_diff b a')))"
	  by (simp add: union_assoc)
	also have "\<dots> = multiset_of (remdups a' @ x # remove x (remdups (list_diff b a')))"
	  by (simp only: remdupsRemoveCommute)
	also have "\<dots> = multiset_of (remdups a') + multiset_of (x # remove x (remdups (list_diff b a')))"
	  by simp
	also have "\<dots> = multiset_of (remdups a') + {#x#} + multiset_of (remove x (remdups (list_diff b a')))"
	  by (simp add: union_assoc) (simp add: union_commute)
	also have "\<dots> = multiset_of (remdups a') + multiset_of (remdups (list_diff b a'))"
	proof-
	  from `\<not> x mem a'` `x mem b`
	  have "x mem (list_diff b a')"
	    using listDiffIff[of "x" "b" "a'"]
	    by simp
	  hence "x mem (remdups (list_diff b a'))"
	    by (auto iff: mem_iff)
	  thus ?thesis
	    using multisetRemoveIff[of "remdups (list_diff b a')" "x"]
	    by (simp add: union_assoc)
	qed
	also have "\<dots> = multiset_of (remdups (a' @ b))"
	  using Cons(1)
	  by simp
	also have "\<dots> = multiset_of (remdups ((x # a') @ b))"
	  using `x mem b`
	  by (simp add: mem_iff)
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
	    using `\<not> x mem a'`
	    by (auto iff: mem_iff)
	  thus ?thesis
	    by simp
	qed
	also have "\<dots> = multiset_of (x # remdups a' @ remdups (list_diff (remove x b) a'))"
	  by auto
	also have "\<dots> = multiset_of (x # remdups a' @ remdups (list_diff b a'))"
	  using `\<not> x mem b`
	  using removeNonMember[of "x" "b"]
	  by simp
	also have "\<dots> = {#x#} + multiset_of (remdups (a' @ b))"
	  using Cons(1)
	  by (simp add: union_commute)
	also have "\<dots> = multiset_of (remdups ((x # a') @ b))"
	  using `\<not> x mem a'` `\<not> x mem b`
	  by (auto iff: mem_iff simp add: union_commute)
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
