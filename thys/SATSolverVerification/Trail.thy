(*    Title:              SATSolverVerification/Trail.thy
      ID:                 $Id: Trail.thy,v 1.2 2008-07-27 14:23:35 lsf37 Exp $
      Author:             Filip Maric
      Maintainer:         Filip Maric <filip at matf.bg.ac.yu>
*)

header{*  Trail datatype definition and its properties *}

theory Trail
imports MoreList
begin

text{*   Trail is a list in which some elements can be marked. *}
types 'a Trail = "('a*bool) list"

consts 
element :: "('a*bool) \<Rightarrow> 'a"
marked  :: "('a*bool) \<Rightarrow> bool"

translations
"element x" == "fst x"
"marked  x" == "snd x"


(*--------------------------------------------------------------------------------*)
subsection{* Trail elements *}

text{* Elements of the trail with marks removed *}
consts elements              :: "'a Trail \<Rightarrow> 'a list"
primrec
"elements [] = []"
"elements (h#t) = (element h) # (elements t)"

lemma eitherMarkedOrNotMarkedElement: 
  shows "a = (element a, True) \<or> a = (element a, False)"
by (cases a) auto

lemma eitherMarkedOrNotMarked:
  assumes "e mem (elements M)"
  shows "(e, True) mem M \<or> (e, False) mem M"
using assms
proof (induct M)
  case (Cons m M')
  thus ?case
    proof (cases "e = element m")
      case True
      thus ?thesis
	using eitherMarkedOrNotMarkedElement [of "m"]
	by auto
    next
      case False
      with Cons
      show ?thesis
	by simp
    qed
qed simp

lemma elementMemElements [simp]:
  assumes "x mem M"
  shows "element x mem (elements M)"
using assms
by (induct M) (auto split: split_if_asm)

lemma elementsAppend [simp]:
  shows "elements (a @ b) = elements a @ elements b"
by (induct a) auto

lemma elementsEmptyIffTrailEmpty [simp]:
  shows "(elements list = []) = (list = [])"
by (induct list) auto

lemma elementsButlastTrailIsButlastElementsTrail [simp]:
  shows "elements (butlast M) = butlast (elements M)"
by (induct M) auto

lemma elementLastTrailIsLastElementsTrail [simp]:
  assumes "M \<noteq> []"
  shows "element (last M) = last (elements M)" 
using assms
by (induct M) auto

lemma isPrefixElements:
  assumes "isPrefix a b"
  shows "isPrefix (elements a) (elements b)"
using assms
unfolding isPrefix_def
by auto

lemma memElementsPrefixImpliesMemElementsTrail:
  assumes 
  "isPrefix p M" and "x mem elements p"
  shows 
  "x mem (elements M)"
using assms
unfolding isPrefix_def
by (auto simp add: memAppend)

lemma uniqElementsTrailImpliesUniqElementsPrefix:
  assumes 
  "isPrefix p M" and "uniq (elements M)"
  shows
  "uniq (elements p)"
proof-
  from `isPrefix p M`
  obtain s 
    where "M = p @ s"
    unfolding isPrefix_def
    by auto
  with `uniq (elements M)`
  show ?thesis
    using uniqAppend[of "elements p" "elements s"]
    by simp
qed

lemma [simp]: 
  assumes "(e, d) mem M"
  shows "e mem elements M"
  using assms
  by (induct M) auto

lemma uniqImpliesExclusiveTrueOrFalse:
  assumes
  "(e, d) mem M" and "uniq (elements M)"
  shows
  "\<not> (e, \<not> d) mem M"
using assms
proof (induct M)
  case (Cons m M')
  {
    assume "(e, d) = m"
    hence "(e, \<not> d) \<noteq> m"
      by auto
    from `(e, d) = m` `uniq (elements (m # M'))`
    have "\<not> (e, d) mem M'"
      by (auto simp add: uniqAppendIff)
    with Cons
    have ?case
      by (auto split: split_if_asm)
  }
  moreover
  {
    assume "(e, \<not> d) = m"
    hence "(e, d) \<noteq> m"
      by auto
    from `(e, \<not> d) = m` `uniq (elements (m # M'))`
    have "\<not> (e, \<not> d) mem M'"
      by (auto simp add: uniqAppendIff)
    with Cons
    have ?case
      by (auto split: split_if_asm)
  }
  moreover
  {
    assume "(e, d) \<noteq> m" "(e, \<not> d) \<noteq> m"
    from `(e, d) \<noteq> m` `(e, d) mem m # M'` have 
      "(e, d) mem M'"
      by simp
    with `uniq (elements (m # M'))` Cons(1)
    have "\<not> (e, \<not> d) mem M'"
      by simp
    with `(e, \<not> d) \<noteq> m`
    have ?case
      by simp
  }
  moreover 
  {
    have "(e, d) = m \<or> (e, \<not> d) = m \<or> (e, d) \<noteq> m \<and> (e, \<not> d) \<noteq> m"
      by auto
  }
  ultimately
  show ?case
    by auto
qed simp

(*--------------------------------------------------------------------------------*)
subsection{* Marked trail elements *}

consts markedElements        :: "'a Trail \<Rightarrow> 'a list"
primrec
"markedElements [] = []"
"markedElements (h#t) =  (if (marked h) then (element h) # (markedElements t) else (markedElements t))"

lemma markedElementIsMarkedTrue: 
  shows "m mem (markedElements M) = (m, True) mem M"
using assms
by (induct M) (auto split: split_if_asm)

lemma markedElementsAppend: 
  shows "markedElements (M1 @ M2) = markedElements M1 @ markedElements M2"
by (induct M1) auto

lemma markedElementsAreElements:
  assumes "m mem (markedElements M)"
  shows   "m mem (elements M)"
using assms markedElementIsMarkedTrue[of "m" "M"]
by auto

lemma markedAndMemberImpliesIsMarkedElement:
  assumes "marked m" "m mem M"
  shows "(element m) mem markedElements M"
proof-
  have "m = (element m, marked m)"
    by auto
  with `marked m` 
  have "m = (element m, True)"
    by simp
  with `m mem M` have
    "(element m, True) mem M"
    by simp
  thus ?thesis
    using markedElementIsMarkedTrue [of "element m" "M"]
    by simp
qed

lemma markedElementsPrefixAreMarkedElementsTrail:
  assumes "isPrefix p M" "m mem markedElements p"
  shows "m mem (markedElements M)"
proof-
  from `m mem markedElements p` 
  have "(m, True) mem p"
    by (simp add: markedElementIsMarkedTrue)
  with `isPrefix p M`
  have "(m, True) mem M"
    using memPrefixImpliesMemList[of "p" "M" "(m, True)"]
    by simp
  thus ?thesis
    by (simp add: markedElementIsMarkedTrue)
qed

lemma markedElementsTrailMemPrefixAreMarkedElementsPrefix:
  assumes 
  "uniq (elements M)" and
  "isPrefix p M" and
  "m mem (elements p)" and
  "m mem (markedElements M)" 
  shows
  "m mem (markedElements p)"
proof-
  from `m mem (markedElements M)` have "(m, True) mem M"
    by (simp add: markedElementIsMarkedTrue)
  with `uniq (elements M)` `m mem (elements p)`
  have "(m, True) mem p"
  proof-
    {
      assume "(m, False) mem p"
      with `isPrefix p M`
      have "(m, False) mem M"
	using memPrefixImpliesMemList[of "p" "M" "(m, False)"]
	by simp
      with `(m, True) mem M` `uniq (elements M)`
      have False
	using uniqImpliesExclusiveTrueOrFalse[of "m" "True" "M"]
	by simp
    }
    with `m mem (elements p)`
    show ?thesis
      using eitherMarkedOrNotMarked[of "m" "p"]
      by auto
  qed
  thus ?thesis
    using markedElementIsMarkedTrue[of "m" "p"]
    by simp
qed

(*--------------------------------------------------------------------------------*)
subsection{* Prefix before/upto a trail element *}

text{* Elements of the trail before the first occurence of a given element - not incuding it *}
consts prefixBeforeElement  :: "'a \<Rightarrow> 'a Trail \<Rightarrow> 'a Trail"
primrec
"prefixBeforeElement e [] = []"
"prefixBeforeElement e (h#t) = 
 (if (element h) = e then
     []
  else
     (h # (prefixBeforeElement e t))
 )"

text{* Elements of the trail before the first occurence of a given element - incuding it *}
consts prefixToElement  :: "'a \<Rightarrow> 'a Trail \<Rightarrow> 'a Trail"
primrec
"prefixToElement e [] = []"
"prefixToElement e (h#t) = 
 (if (element h) = e then
     [h]
  else
     (h # (prefixToElement e t))
 )"

lemma isPrefixPrefixToElement:
  shows "isPrefix (prefixToElement e t) t"
unfolding isPrefix_def
by (induct t) auto

lemma isPrefixPrefixBeforeElement:
  shows "isPrefix (prefixBeforeElement e t) t"
unfolding isPrefix_def
by (induct t) auto

lemma prefixToElementContainsTrailElement:
  assumes "e mem elements M"
  shows "e mem elements (prefixToElement e M)"
using assms
by (induct M) auto

lemma prefixBeforeElementDoesNotContainTrailElement:
  assumes "e mem elements M"
  shows "\<not> e mem (elements (prefixBeforeElement e M))"
using assms
by (induct M) auto

lemma prefixToElementAppend: 
  shows "prefixToElement e (M1 @ M2) = 
            (if e mem elements M1 then 
                prefixToElement e M1
             else   
                M1 @ prefixToElement e M2
             )"
by (induct M1) auto


lemma prefixToElementToPrefixElement:
  assumes
  "isPrefix p M" and "e mem (elements p)"
  shows
  "prefixToElement e M = prefixToElement e p"
using assms
unfolding isPrefix_def
proof (induct p arbitrary: M)
  case (Cons a p')
  then obtain s 
    where "(a # p') @ s = M"
    by auto
  show ?case
  proof (cases "(element a) = e")
    case True
    from True `(a # p') @ s = M` have "prefixToElement e M = [a]"
      by auto
    moreover
    from True have "prefixToElement e (a # p') = [a]"
      by auto
    ultimately
    show ?thesis
      by simp
  next
    case False
    from False `(a # p') @ s = M` have "prefixToElement e M = a # prefixToElement e (p' @ s)"
      by auto
    moreover
    from False have "prefixToElement e (a # p') = a # prefixToElement e p'"
      by simp
    moreover
    from False `e mem elements (a # p')` have "e mem elements p'"
      by simp
    have "? s . (p' @ s = p' @ s)"
      by simp
    from `e mem elements p'`  `? s. (p' @ s = p' @ s)` 
      have "prefixToElement e (p' @ s) = prefixToElement e p'"
      using Cons(1) [of "p' @ s"]
      by simp
    ultimately show ?thesis
      by simp
  qed
qed simp

(*--------------------------------------------------------------------------------*)
subsection{* Marked elements upto a given trail element *}

text{* Marked elements of the trail upto the given element (which is also included if it is marked) *}
consts
markedElementsTo :: "'a \<Rightarrow> 'a Trail \<Rightarrow> 'a list"
defs 
markedElementsTo_def: "markedElementsTo e t == markedElements (prefixToElement e t)"

lemma markedElementsToArePrefixOfMarkedElements:
  shows "isPrefix (markedElementsTo e M) (markedElements M)"
unfolding isPrefix_def
unfolding markedElementsTo_def
by (induct M) auto

lemma markedElementsToAreMarkedElements: 
  assumes "m mem (markedElementsTo e M)"
  shows "m mem (markedElements M)"
using assms
using markedElementsToArePrefixOfMarkedElements[of "e" "M"]
using memPrefixImpliesMemList[of "markedElementsTo e M" "markedElements M" "m"]
by simp

lemma markedElementsToNonMemberAreAllMarkedElements:
  assumes "\<not> e mem (elements M)"
  shows "markedElementsTo e M = markedElements M" 
using assms
unfolding markedElementsTo_def
by (induct M) auto

lemma markedElementsToAppend: 
  shows "markedElementsTo e (M1 @ M2) = 
          (if e mem elements M1 then 
                 markedElementsTo e M1
           else 
                 markedElements M1 @ markedElementsTo e M2
          )"
unfolding markedElementsTo_def
by (auto simp add: prefixToElementAppend markedElementsAppend)

lemma markedElementsEmptyImpliesMarkedElementsToEmpty: 
  assumes "markedElements M = []"
  shows "markedElementsTo e M = []"
using assms
using markedElementsToArePrefixOfMarkedElements [of "e" "M"]
unfolding isPrefix_def
by auto

lemma markedElementIsMemberOfItsMarkedElementsTo: 
  assumes
  "uniq (elements M)" and "marked e" and "e mem M"
  shows 
  "element e mem markedElementsTo (element e) M"
using assms
unfolding markedElementsTo_def
by (induct M) (auto split: split_if_asm)

lemma markedElementsToPrefixElement: 
  assumes "isPrefix p M" and "e mem (elements p)"
  shows "markedElementsTo e M = markedElementsTo e p"
unfolding markedElementsTo_def
using assms
by (simp add: prefixToElementToPrefixElement)


(*--------------------------------------------------------------------------------*)
subsection{* Last marked element in a trail *}

consts
lastMarked :: "'a Trail \<Rightarrow> 'a"
defs
lastMarked_def: "lastMarked t == last (markedElements t)"

lemma lastMarkedIsMarkedElement: 
  assumes "markedElements M \<noteq> []" 
  shows "lastMarked M mem (markedElements M)"
using assms
unfolding lastMarked_def
by simp

lemma removeLastMarkedFromMarkedElementsToLastMarkedAreAllMarkedElementsInPrefixLastMarked: 
  assumes
  "markedElements M \<noteq> []"
  shows
  "remove (lastMarked M) (markedElementsTo (lastMarked M) M) = markedElements (prefixBeforeElement (lastMarked M) M)"
using assms
unfolding lastMarked_def
unfolding markedElementsTo_def
by (induct M) auto

lemma markedElementsToLastMarkedAreAllMarkedElements:
  assumes
  "uniq (elements M)" and "markedElements M \<noteq> []"
  shows
  "markedElementsTo (lastMarked M) M = markedElements M"
using assms
unfolding lastMarked_def
unfolding markedElementsTo_def
by (induct M) (auto simp add: markedElementsAreElements)

lemma lastTrailElementMarkedImpliesMarkedElementsToLastElementAreAllMarkedElements:
  assumes
  "marked (last M)" and "~(last (elements M)) mem (butlast (elements M))"
  shows
  "markedElementsTo (last (elements M)) M = markedElements M"
using assms
unfolding markedElementsTo_def
by (induct M) auto

lemma lastMarkedIsMemberOfItsMarkedElementsTo: 
  assumes
  "uniq (elements M)" and "markedElements M \<noteq> []"
  shows
  "lastMarked M mem (markedElementsTo (lastMarked M) M)"
using assms
using markedElementsToLastMarkedAreAllMarkedElements [of "M"]
using lastMarkedIsMarkedElement [of "M"]
by auto

lemma lastTrailElementNotMarkedImpliesMarkedElementsToLAreMarkedElementsToLInButlastTrail: 
  assumes "\<not> marked (last M)"
  shows "markedElementsTo e M = markedElementsTo e (butlast M)"
using assms
unfolding markedElementsTo_def
by (induct M) auto


(*--------------------------------------------------------------------------------*)
subsection{* Level of a trail element *}

text{* Level of an element is the number of marked elements that precede it *}

consts
elementLevel :: "'a \<Rightarrow> 'a Trail \<Rightarrow> int"
defs
elementLevel_def: "elementLevel e t == intLength (markedElementsTo e t)"

lemma elementLevelGeqZero:
  shows "elementLevel e trail >= 0"
unfolding elementLevel_def
by (simp add:intLengthGeqZero)

lemma elementLevelMarkedGeq1:
  assumes
  "uniq (elements M)" and "e mem (markedElements M)"
  shows
  "elementLevel e M >= 1"
proof-
  from `e mem (markedElements M)` have "(e, True) mem M"
    by (simp add: markedElementIsMarkedTrue)
  with `uniq (elements M)`  have "e mem (markedElementsTo e M)"
    using markedElementIsMemberOfItsMarkedElementsTo[of "M" "(e, True)"]
    by simp
  hence "markedElementsTo e M \<noteq> []"
    by auto
  thus ?thesis
    unfolding elementLevel_def
    by (simp add: intLengthNonEmptyGeq1)
qed

lemma elementLevelAppend:
  assumes "a mem (elements M)"
  shows "elementLevel a M = elementLevel a (M @ M')"
using assms
unfolding elementLevel_def
by (simp add: intLengthAppend markedElementsToAppend)


lemma elementLevelPreceedsLeq: 
  assumes
  "preceeds a b (elements M)" 
  shows
  "elementLevel a M <= elementLevel b M"
using assms
proof (induct M)
  case (Cons m M')
  {
    assume "a = element m"
    hence ?case
      unfolding elementLevel_def
      unfolding markedElementsTo_def
      by (auto simp add: intLengthGeqZero)
  }
  moreover
  {
    assume "b = element m"
    {
      assume "a \<noteq> b"
      hence "\<not> preceeds a b (b # (elements M'))"
	by (rule noElementsPreceedsFirstElement)
      with `b = element m` `preceeds a b (elements (m # M'))`
      have False
	by simp
    }
    hence "a = b"
      by auto
    hence ?case
      by simp
  }
  moreover 
  { 
    assume "a \<noteq> element m" "b \<noteq> element m"
    moreover
    from `preceeds a b (elements (m # M'))`
    have "a mem (elements (m # M'))" "b mem (elements (m # M'))"
      unfolding preceeds_def
      by (auto split: split_if_asm)
    from `a \<noteq> element m` `a mem (elements (m # M'))`
    have "a mem elements M'"
      by simp
    moreover
    from `b \<noteq> element m` `b mem (elements (m # M'))`
    have "b mem elements M'"
      by simp
    ultimately
    have "elementLevel a M' \<le> elementLevel b M'"
      using Cons
      unfolding preceeds_def
      unfolding firstPos_def
      by auto
    hence ?case
      using `a \<noteq> element m` `b \<noteq> element m`
      unfolding elementLevel_def
      unfolding markedElementsTo_def
      by auto
  }
  ultimately
  show ?case
    by auto
next
  case Nil
  thus ?case
    unfolding preceeds_def
    unfolding firstPos_def
    by simp
qed


lemma elementLevelPreceedsMarkedElementLt: 
  assumes
  "uniq (elements M)" and
  "e \<noteq> d" and
  "d mem (markedElements M)" and
  "preceeds e d (elements M)"
  shows
  "elementLevel e M < elementLevel d M"
using assms
proof (induct M)
  case (Cons m M')
  {
    assume "e = element m"
    moreover
    with `e \<noteq> d` have "d \<noteq> element m"
      by simp
    moreover
    from `uniq (elements (m # M'))` `d mem markedElements (m # M')`
    have "1 \<le> elementLevel d (m # M')"
      using elementLevelMarkedGeq1[of "m # M'" "d"]
      by auto
    moreover
    from `d \<noteq> element m` `d mem markedElements (m # M')`
    have "d mem markedElements M'"
      by (simp split: split_if_asm)
    from `uniq (elements (m # M'))` `d mem markedElements M'`
    have "1 \<le> elementLevel d M'"
      using elementLevelMarkedGeq1[of "M'" "d"]
      by auto
    ultimately
    have ?case
      unfolding elementLevel_def
      unfolding markedElementsTo_def
      by (simp split: split_if_asm)
  }
  moreover
  {
    assume "d = element m"
    from `e \<noteq> d` have "\<not> preceeds e d (d # (elements M'))"
      using noElementsPreceedsFirstElement[of "e" "d" "elements M'"]
      by simp
    with `d = element m` `preceeds e d (elements (m # M'))`
    have False
      by simp
    hence ?case
      by simp
  }
  moreover
  {
    assume "e \<noteq> element m" "d \<noteq> element m"    
    moreover
    from `preceeds e d (elements (m # M'))`
    have "e mem (elements (m # M'))" "d mem (elements (m # M'))"
      unfolding preceeds_def
      by (auto split: split_if_asm)
    from `e \<noteq> element m` `e mem (elements (m # M'))`
    have "e mem elements M'"
      by simp
    moreover
    from `d \<noteq> element m` `d mem (elements (m # M'))`
    have "d mem elements M'"
      by simp
    moreover
    from `d \<noteq> element m` `d mem markedElements (m # M')`
    have "d mem markedElements M'"
      by (simp split: split_if_asm)
    ultimately
    have "elementLevel e M' < elementLevel d M'"
      using `uniq (elements (m # M'))` Cons
      unfolding preceeds_def
      unfolding firstPos_def
      by auto
    hence ?case
      using `e \<noteq> element m` `d \<noteq> element m`
      unfolding elementLevel_def
      unfolding markedElementsTo_def
      by auto
  }
  ultimately
  show ?case
    by auto
qed simp

lemma differentMarkedElementsHaveDifferentLevels:
  assumes
  "uniq (elements M)" and
  "a mem (markedElements M)" and
  "b mem (markedElements M)" and
  "a \<noteq> b" 
  shows "elementLevel a M \<noteq> elementLevel b M"
proof-
  from `a mem (markedElements M)`
  have "a mem (elements M)"
    by (simp add: markedElementsAreElements)
  moreover
  from `b mem (markedElements M)`
  have "b mem (elements M)"
    by (simp add: markedElementsAreElements)
  ultimately
  have "preceeds a b (elements M) \<or> preceeds b a (elements M)"
    using `a \<noteq> b`
    using preceedsTotalOrder[of "a" "elements M" "b"]
    by simp
  moreover
  {
    assume "preceeds a b (elements M)"
    with assms
    have ?thesis
      using elementLevelPreceedsMarkedElementLt[of "M" "a" "b"]
      by auto
  }
  moreover
  {
    assume "preceeds b a (elements M)"
    with assms
    have ?thesis
      using elementLevelPreceedsMarkedElementLt[of "M" "b" "a"]
      by auto
  }
  ultimately
  show ?thesis
    by auto
qed


(* ------------------------------------------------------------------------- *)
subsection{* Current trail level *}

text{* Current level is the number of marked elements in the trail *}

consts
currentLevel :: "'a Trail \<Rightarrow> int"
defs
currentLevel_def:
"currentLevel t == intLength (markedElements t)"

lemma currentLevelNonMarked: 
  shows "currentLevel M = currentLevel (M @ [(l, False)])"
by (auto simp add:currentLevel_def markedElementsAppend)

lemma currentLevelPrefix:
  assumes "isPrefix a b" 
  shows "currentLevel a <= currentLevel b"
using assms
unfolding isPrefix_def
unfolding currentLevel_def
by (auto simp add: intLengthAppend intLengthGeqZero markedElementsAppend)

lemma elementLevelLeqCurrentLevel:
  shows "elementLevel a M <= currentLevel M"
proof-
  have "isPrefix (prefixToElement a M) M"
    using isPrefixPrefixToElement[of "a" "M"]
    .
  then obtain s
    where "prefixToElement a M @ s = M"
    unfolding isPrefix_def
    by auto
  hence "M = prefixToElement a M @ s"
    by (rule sym)
  hence "currentLevel M = currentLevel (prefixToElement a M @ s)"
    by simp
  hence "currentLevel M = intLength (markedElements (prefixToElement a M)) + intLength (markedElements s)"
    unfolding currentLevel_def
    by (simp add: intLengthAppend markedElementsAppend)
  thus ?thesis
    unfolding elementLevel_def
    unfolding markedElementsTo_def
    by (simp add: intLengthGeqZero)
qed

lemma elementOnCurrentLevel:
  assumes "\<not> a mem (elements M)"
  shows "elementLevel a (M @ [(a, d)]) = currentLevel  (M @ [(a, d)])"
using assms
unfolding currentLevel_def
unfolding elementLevel_def
unfolding markedElementsTo_def 
by (auto simp add: prefixToElementAppend intLengthAppend)

(*--------------------------------------------------------------------------------*)
subsection{* Prefix to a given trail level *}

text{* Prefix is made or elements of the trail up to a given element level *}
consts
prefixToLevel :: "int \<Rightarrow> 'a Trail \<Rightarrow> 'a Trail"
prefixToLevel_aux :: "'a Trail \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'a Trail"

defs
prefixToLevel_def: "(prefixToLevel l t) == (prefixToLevel_aux t l 0)"

primrec
"(prefixToLevel_aux [] l cl) = []"
"(prefixToLevel_aux (h#t) l cl) = 
  (if (marked h) then
    (if (cl >= l) then [] else (h # (prefixToLevel_aux t l (cl+1))))
  else
    (h # (prefixToLevel_aux t l cl))
  )"

lemma isPrefixPrefixToLevel_aux:
  shows "\<exists> s. prefixToLevel_aux t l i @ s = t"
by (induct t arbitrary: i) auto

lemma isPrefixPrefixToLevel:
  shows "(isPrefix (prefixToLevel l t) t)"
using isPrefixPrefixToLevel_aux[of "t" "l"]
unfolding isPrefix_def
unfolding prefixToLevel_def
by simp

lemma currentLevelPrefixToLevel_aux: 
  assumes "l >= i"
  shows "currentLevel (prefixToLevel_aux M l i) <= l - i"
using assms
proof (induct M arbitrary: i)
  case (Cons m M')
  {
    assume "marked m" "i = l"
    hence ?case
      unfolding currentLevel_def
      by simp
  }
  moreover
  {
    assume "marked m" "i < l"
    hence ?case
      using Cons(1) [of "i+1"]
      unfolding currentLevel_def
      by simp
  }
  moreover
  {
    assume "\<not> marked m"
    hence ?case
      using Cons
      unfolding currentLevel_def
      by simp
  }
  ultimately
  show ?case
    using `i <= l`
    by auto
next
  case Nil
  thus ?case
    unfolding currentLevel_def
    by simp
qed

lemma currentLevelPrefixToLevel: 
  assumes "level >= 0"
  shows "currentLevel (prefixToLevel level M) <= level"
using assms
using currentLevelPrefixToLevel_aux[of "0" "level" "M"]
unfolding prefixToLevel_def
by simp


lemma prefixToLevel_auxIncreaseAuxilaryCounter: 
  assumes "k >= i"
  shows "prefixToLevel_aux M l i = prefixToLevel_aux M (l + (k - i)) k"
using assms
proof (induct M arbitrary: i k)
  case (Cons m M')
  {
    assume "\<not> marked m"
    hence ?case
      using Cons(1)[of "i" "k"] Cons(2)
      by simp
  }
  moreover
  {
    assume "i >= l" "marked m"
    hence ?case
      by simp
  }
  moreover
  {
    assume "i < l" "marked m"
    hence ?case
      using Cons(1)[of "i+1" "k+1"] Cons(2)
      by simp
  }
  ultimately
  show ?case
    by auto
qed simp

lemma isPrefixPrefixToLevel_auxLowerLevel:
  assumes "i <= j"
  shows "isPrefix (prefixToLevel_aux M i k) (prefixToLevel_aux M j k)"
using assms
by (induct M arbitrary: k) (auto simp add:isPrefix_def)

lemma prefixToLevel_auxPrefixToLevel_auxHigherLevel: 
  assumes "i <= j"
  shows "prefixToLevel_aux a i k = prefixToLevel_aux (prefixToLevel_aux a j k) i k"
using assms
by (induct a arbitrary: k) auto

lemma prefixToLevelAppend_aux1:
  assumes
  "l >= i" and "l - i < currentLevel a"
  shows 
  "prefixToLevel_aux (a @ b) l i = prefixToLevel_aux a l i"
using assms
proof (induct a arbitrary: i)
  case (Cons a a')
  {
    assume "\<not> marked a"
    hence ?case
      using Cons(1)[of "i"] `i \<le> l` `l - i < currentLevel (a # a')`
      unfolding currentLevel_def
      by simp
  }
  moreover
  {
    assume "marked a" "l = i"
    hence ?case
      by simp
  }
  moreover
  {
    assume "marked a" "l > i"
    hence ?case
      using Cons(1)[of "i + 1"] `i \<le> l` `l - i < currentLevel (a # a')`
      unfolding currentLevel_def
      by simp
  }
  ultimately
  show ?case
    using `i <= l`
    by auto
next
  case Nil
  thus ?case
    unfolding currentLevel_def
    by simp
qed


lemma prefixToLevelAppend_aux2: 
  assumes 
  "i <= l" and "currentLevel a + i <= l"
  shows "prefixToLevel_aux (a @ b) l i = a @ prefixToLevel_aux b l (i + (currentLevel a))"
using assms
proof (induct a arbitrary: i)
  case (Cons a a')
  {
    assume "\<not> marked a"
    hence ?case
      using Cons
      unfolding currentLevel_def
      by simp
  }
  moreover
  {
    assume "marked a" "l = i"
    hence ?case
      using `(currentLevel (a # a')) + i <= l`
      unfolding currentLevel_def
      using intLengthGeqZero[of "markedElements a'"]
      by simp
  }
  moreover
  {
    assume "marked a" "l > i"
    hence "prefixToLevel_aux (a' @ b) l (i + 1) = a' @ prefixToLevel_aux b l (i + 1 + currentLevel a')"
      using Cons(1) [of "i + 1"] `(currentLevel (a # a')) + i <= l`
      unfolding currentLevel_def
      by simp
    moreover
    have "i + 1 + intLength (markedElements a') = i + (1 + intLength (markedElements a'))"
      by simp
    ultimately
    have ?case
      using `marked a` `l > i`
      unfolding currentLevel_def
      by simp
  }
  ultimately
  show ?case
    using `l >= i`
    by auto
next
  case Nil
  thus ?case
    unfolding currentLevel_def
    by simp
qed

lemma prefixToLevelAppend:
  assumes "level >= 0"
  shows "prefixToLevel level (a @ b) = 
  (if level < currentLevel a then 
      prefixToLevel level a
  else 
      a @ prefixToLevel_aux b level (currentLevel a)
  )"
proof (cases "level < currentLevel a")
  case True
  thus ?thesis
    unfolding prefixToLevel_def
    using prefixToLevelAppend_aux1[of "0" "level" "a"] `level >= 0`
    by simp
next
  case False
  thus ?thesis
    unfolding prefixToLevel_def
    using prefixToLevelAppend_aux2[of "0" "level" "a"] `level >= 0`
    by simp
qed

lemma isProperPrefixPrefixToLevel:
  assumes "l < currentLevel t" "l >= 0"
  shows "\<exists> s. (prefixToLevel l t) @ s = t \<and> s \<noteq> [] \<and> (marked (hd s))"
proof-
  have "isPrefix (prefixToLevel l t) t"
    by (simp add:isPrefixPrefixToLevel)
  then obtain s::"'a Trail"
    where "(prefixToLevel l t) @ s = t"
    unfolding isPrefix_def
    by auto
  moreover
  have "s \<noteq> []"
  proof-
    {
      assume "s = []"
      with `(prefixToLevel l t) @ s = t` 
      have "prefixToLevel l t = t"
	by simp
      with `l >= 0` have "currentLevel (prefixToLevel l t) <= l"
	using currentLevelPrefixToLevel[of "l" "t"]
	by simp
      with `prefixToLevel l t = t` have "currentLevel t <= l"
	by simp
      with `l < currentLevel t` have False
	by simp
    }
    thus ?thesis
      by auto
  qed
  moreover
  have "marked (hd s)"
  proof-
    {
      assume "\<not> marked (hd s)"
      from `l >= 0` have "currentLevel (prefixToLevel l t) <= l"
	by (simp add:currentLevelPrefixToLevel)
      from `s \<noteq> []` have "s = [hd s] @ (tl s)"
	by simp
      with `(prefixToLevel l t) @ s = t` have
	"t = (prefixToLevel l t) @ [hd s] @ (tl s)"
	by simp
      hence "(prefixToLevel l t) = (prefixToLevel l ((prefixToLevel l t) @ [hd s] @ (tl s)))"
	by simp
      also
      with `l >= 0` `currentLevel (prefixToLevel l t) <= l` 
      have "\<dots> = ((prefixToLevel l t) @ (prefixToLevel_aux ([hd s] @ (tl s)) l (currentLevel (prefixToLevel l t))))"
	by (auto simp add: prefixToLevelAppend)
      also
      have "\<dots> = 
	((prefixToLevel l t) @ (hd s) # prefixToLevel_aux (tl s) l (currentLevel (prefixToLevel l t)))"
      proof-
	from `currentLevel (prefixToLevel l t) <= l` `\<not> marked (hd s)`
	have "prefixToLevel_aux ([hd s] @ (tl s)) l (currentLevel (prefixToLevel l t)) = 
	  (hd s) # prefixToLevel_aux (tl s) l (currentLevel (prefixToLevel l t))"
	  by simp
	thus ?thesis
	  by simp
      qed
      ultimately
      have "(prefixToLevel l t) = (prefixToLevel l t) @ (hd s) # prefixToLevel_aux (tl s) l (currentLevel (prefixToLevel l t))"
	by simp
      hence "False"
	by auto
    }
    thus ?thesis
      by auto
  qed
  ultimately
  show ?thesis
    by auto
qed

lemma prefixToLevelElementsElementLevel: 
  assumes 
  "level >= 0" and
  "e mem (elements (prefixToLevel level M))"
  shows
  "elementLevel e M <= level"
proof -
  have "elementLevel e (prefixToLevel level M) <= currentLevel (prefixToLevel  level M)"
    by (simp add: elementLevelLeqCurrentLevel)
  moreover
  with `level >= 0` have "currentLevel (prefixToLevel level M) <= level"
    using currentLevelPrefixToLevel[of "level" "M"]
    by simp
  ultimately have "elementLevel e (prefixToLevel level M) <= level"
    by simp
  moreover
  have "isPrefix (prefixToLevel level M) M"
    by (simp add:isPrefixPrefixToLevel)
  then obtain s
    where "(prefixToLevel level M) @ s = M"
    unfolding isPrefix_def
    by auto
  with `e mem (elements (prefixToLevel level M))` 
  have "elementLevel e (prefixToLevel level M) = elementLevel e M"
    using elementLevelAppend [of "e" "prefixToLevel level M" "s"]
    by simp
  ultimately
  show ?thesis
    by simp
qed


lemma elementLevelLtLevelImpliesMemberPrefixToLevel_aux:
  assumes
  "e mem (elements M)" and
  "elementLevel e M + i <= level" and
  "i <= level"
  shows 
  "e mem elements (prefixToLevel_aux M level i)"
using assms
proof (induct M arbitrary: i)
  case (Cons m M')
  thus ?case
  proof (cases "e = element m")
    case True
    thus ?thesis
      using `elementLevel e (m # M') + i \<le> level`
      unfolding prefixToLevel_def
      unfolding elementLevel_def
      unfolding markedElementsTo_def
      by (simp split: split_if_asm)
  next
    case False
    with `e mem (elements (m # M'))`
    have "e mem elements M'"
      by simp

    show ?thesis
    proof (cases "marked m")
      case True
      with Cons `e \<noteq> element m`
      have "(elementLevel e M') + i + 1 \<le> level"
	unfolding elementLevel_def
	unfolding markedElementsTo_def
	by (simp split: split_if_asm)
      moreover
      have "elementLevel e M' >= 0"
	by (simp add:elementLevelGeqZero)
      ultimately
      have "i + 1 <= level"
	by simp
      with `e mem (elements M')` `(elementLevel e M') + i + 1 \<le> level` Cons(1)[of "i+1"]
      have "e mem elements (prefixToLevel_aux M' level (i + 1))"
	by simp
      with `e \<noteq> element m` `i + 1 <= level` True show ?thesis
	by simp
    next
      case False
      with `e \<noteq> element m` `elementLevel e (m # M') + i \<le> level` have "elementLevel e M' + i \<le> level"
	unfolding elementLevel_def
	unfolding markedElementsTo_def
	by (simp split: split_if_asm)
      with `e mem elements M'` have "e mem elements (prefixToLevel_aux M' level i)"
	using Cons
	by (auto split: split_if_asm)
      with `e \<noteq> element m` False show ?thesis
	by simp
    qed
  qed
qed simp

lemma elementLevelLtLevelImpliesMemberPrefixToLevel:
  assumes
  "e mem (elements M)" and
  "elementLevel e M <= level"
  shows 
  "e mem elements (prefixToLevel level M)"
using assms
using elementLevelGeqZero[of "e" "M"]
using elementLevelLtLevelImpliesMemberPrefixToLevel_aux[of "e" "M" "0" "level"]
unfolding prefixToLevel_def
by simp

lemma literalNotInEarlierLevelsThanItsLevel: 
  assumes
  "level >= 0" and
  "level < elementLevel e M" 
  shows 
  "\<not> e mem (elements (prefixToLevel level M))"
proof-
  {
    assume "\<not> ?thesis"
    with `level >= 0` have "level >= elementLevel e M"
      by (simp add: prefixToLevelElementsElementLevel)
    with `level < elementLevel e M`
    have False
      by simp
  }
  thus ?thesis
    by auto
qed

lemma elementLevelPrefixElement: 
  assumes "e mem elements (prefixToLevel level M)"
  shows "elementLevel e (prefixToLevel level M) = elementLevel e M"
using assms
proof-
  have "isPrefix (prefixToLevel level M) M"
    by (simp add: isPrefixPrefixToLevel)
  then obtain s where "(prefixToLevel level M) @ s = M"
    unfolding isPrefix_def
    by auto
  with assms show ?thesis
    using elementLevelAppend[of "e" "prefixToLevel level M" "s"]
    by auto
qed

(*--------------------------------------------------------------------------------*)
subsection{* Number of literals of every trail level *}

consts
levelsCounter_aux :: "'a Trail \<Rightarrow> nat list \<Rightarrow> nat list"
primrec
"levelsCounter_aux [] l = l"
"levelsCounter_aux (h # t) l = 
  (if (marked h) then 
      levelsCounter_aux t (l @ [1]) 
   else
      levelsCounter_aux t (butlast l @ [Suc (last l)])
  )"

constdefs
levelsCounter :: "'a Trail \<Rightarrow> nat list"
"levelsCounter t == levelsCounter_aux t [0]"

lemma levelsCounter_aux_startIrellevant: 
  "\<forall> y. y \<noteq> [] \<longrightarrow> levelsCounter_aux a (x @ y) = (x @ levelsCounter_aux a y)"
by (induct a) (auto simp add: butlastAppend)

lemma levelsCounter_auxSuffixContinues: "\<forall> l. levelsCounter_aux (a @ b) l = levelsCounter_aux b (levelsCounter_aux a l)"
by (induct a) auto

lemma levelsCounter_auxNotEmpty: "\<forall> l. l \<noteq> [] \<longrightarrow> levelsCounter_aux a l \<noteq> []"
by (induct a) auto

lemma levelsCounter_auxIncreasesFirst: 
"\<forall> m n l1 l2. levelsCounter_aux a (m # l1) = n # l2 \<longrightarrow> m <= n"
proof (induct "a")
  case Nil
  {
    fix m::nat and n::nat and l1::"nat list" and l2::"nat list"
    assume "levelsCounter_aux [] (m # l1) = n # l2"
    hence "m = n"
      by simp
  }
  thus ?case
    by simp
next
  case (Cons a list)
  {
    fix m::nat and n::nat and l1::"nat list" and l2::"nat list"
    assume "levelsCounter_aux (a # list) (m # l1) = n # l2"
    have "m <= n"
    proof (cases "marked a")
      case True
      with `levelsCounter_aux (a # list) (m # l1) = n # l2` 
      have "levelsCounter_aux list (m # l1 @ [Suc 0]) = n # l2"
	by simp
      with Cons
      show ?thesis
	by auto
    next
      case False
      show ?thesis 
      proof (cases "l1 = []")
	case True
	with `\<not> marked a` `levelsCounter_aux (a # list) (m # l1) = n # l2` 
	have "levelsCounter_aux list [Suc m] = n # l2"
	  by simp
	with Cons
	have "Suc m <= n"
	  by auto
	thus ?thesis
	  by simp
      next
	case False
	with `\<not> marked a` `levelsCounter_aux (a # list) (m # l1) = n # l2` 
	have "levelsCounter_aux list (m # butlast l1 @ [Suc (last l1)]) = n # l2"
	  by simp
	with Cons
	show ?thesis
	  by auto
      qed
    qed
  }
  thus ?case
    by simp
qed

lemma levelsCounterPrefix:
  assumes "(isPrefix p a)"
  shows "? rest. rest \<noteq> [] \<and> levelsCounter a = butlast (levelsCounter p) @ rest \<and> last (levelsCounter p) <= hd rest"
proof-
  from assms
  obtain s :: "'a Trail" where "p @ s = a"
    unfolding isPrefix_def
    by auto
  from `p @ s = a` have "levelsCounter a = levelsCounter (p @ s)"
    by simp
  show ?thesis
  proof (cases "s = []")
    case True
    have "(levelsCounter a) = (butlast (levelsCounter p)) @ [last (levelsCounter p)] \<and> 
      (last (levelsCounter p)) <= hd [last (levelsCounter p)]"
      using `p @ s = a` `s = []`
      unfolding levelsCounter_def
      using levelsCounter_auxNotEmpty[of "p"]
      by auto
    thus ?thesis
      by auto
  next
    case False
    show ?thesis
    proof (cases "marked (hd s)")
      case True
      from `p @ s = a` have "levelsCounter a = levelsCounter (p @ s)"
	by simp
      also
      have "\<dots> = levelsCounter_aux s (levelsCounter_aux p [0])"
	unfolding levelsCounter_def
	by (simp add: levelsCounter_auxSuffixContinues)
      also
      have "\<dots> = levelsCounter_aux (tl s) ((levelsCounter_aux p [0]) @ [1])"
      proof-
	from `s \<noteq> []` have "s = hd s # tl s"
	  by simp
	then have "levelsCounter_aux s (levelsCounter_aux p [0]) = levelsCounter_aux (hd s # tl s) (levelsCounter_aux p [0])"
	  by simp
	with `marked (hd s)` show ?thesis
	  by simp
      qed
      also
      have "\<dots> = levelsCounter_aux p [0] @ (levelsCounter_aux (tl s) [1])"
	by (simp add: levelsCounter_aux_startIrellevant)
      finally 
      have "levelsCounter a = levelsCounter p @ (levelsCounter_aux (tl s) [1])"
	unfolding levelsCounter_def
	by simp
      hence "(levelsCounter a) = (butlast (levelsCounter p)) @ ([last (levelsCounter p)] @ (levelsCounter_aux (tl s) [1])) \<and> 
	(last (levelsCounter p)) <= hd ([last (levelsCounter p)] @ (levelsCounter_aux (tl s) [1]))"
	unfolding levelsCounter_def
	using levelsCounter_auxNotEmpty[of "p"]
	by auto
      thus ?thesis
	by auto
    next
      case False
      from `p @ s = a` have "levelsCounter a = levelsCounter (p @ s)"
	by simp
      also
      have "\<dots> = levelsCounter_aux s (levelsCounter_aux p [0])"
	unfolding levelsCounter_def
	by (simp add: levelsCounter_auxSuffixContinues)
      also
      have "\<dots> = levelsCounter_aux (tl s) ((butlast (levelsCounter_aux p [0])) @ [Suc (last (levelsCounter_aux p [0]))])"
      proof-
	from `s \<noteq> []` have "s = hd s # tl s"
	  by simp
	then have "levelsCounter_aux s (levelsCounter_aux p [0]) = levelsCounter_aux (hd s # tl s) (levelsCounter_aux p [0])"
	  by simp
	with `~marked (hd s)` show ?thesis
	  by simp
      qed
      also
      have "\<dots> = butlast (levelsCounter_aux p [0]) @ (levelsCounter_aux (tl s) [Suc (last (levelsCounter_aux p [0]))])"
	by (simp add: levelsCounter_aux_startIrellevant)
      finally 
      have "levelsCounter a = butlast (levelsCounter_aux p [0]) @ (levelsCounter_aux (tl s) [Suc (last (levelsCounter_aux p [0]))])"
	unfolding levelsCounter_def
	by simp
      moreover
      have "hd (levelsCounter_aux (tl s) [Suc (last (levelsCounter_aux p [0]))]) >= Suc (last (levelsCounter_aux p [0]))"
      proof-
	have "(levelsCounter_aux (tl s) [Suc (last (levelsCounter_aux p [0]))]) \<noteq> []"
	  using levelsCounter_auxNotEmpty[of "tl s"]
	  by simp
	then obtain h t where "(levelsCounter_aux (tl s) [Suc (last (levelsCounter_aux p [0]))]) = h # t"
	  using neq_Nil_conv[of "(levelsCounter_aux (tl s) [Suc (last (levelsCounter_aux p [0]))])"]
	  by auto
	hence "h >= Suc (last (levelsCounter_aux p [0]))"
	  using levelsCounter_auxIncreasesFirst[of "tl s"]
	  by auto
	with `(levelsCounter_aux (tl s) [Suc (last (levelsCounter_aux p [0]))]) = h # t` 
	show ?thesis
	  by simp
      qed
      ultimately
      have "levelsCounter a = butlast (levelsCounter p) @ (levelsCounter_aux (tl s) [Suc (last (levelsCounter_aux p [0]))]) \<and> 
	last (levelsCounter p) <= hd (levelsCounter_aux (tl s) [Suc (last (levelsCounter_aux p [0]))])"
	unfolding levelsCounter_def
	by simp
      thus ?thesis
	using levelsCounter_auxNotEmpty[of "tl s"]
	by auto
    qed
  qed
qed
  
lemma levelsCounterPrefixToLevel:
  assumes "p = prefixToLevel level a" "level >= 0" "level < currentLevel a" 
  shows "? rest . rest \<noteq> [] \<and> (levelsCounter a) = (levelsCounter p) @ rest"
proof-
  from assms
  obtain s :: "'a Trail" where "p @ s = a" "s \<noteq> []" "marked (hd s)"
    using isProperPrefixPrefixToLevel[of "level" "a"]
    by auto
  from `p @ s = a` have "levelsCounter a = levelsCounter (p @ s)"
    by simp
  also
  have "\<dots> = levelsCounter_aux s (levelsCounter_aux p [0])"
    unfolding levelsCounter_def
    by (simp add: levelsCounter_auxSuffixContinues)
  also
  have "\<dots> = levelsCounter_aux (tl s) ((levelsCounter_aux p [0]) @ [1])"
  proof-
    from `s \<noteq> []` have "s = hd s # tl s"
      by simp
    then have "levelsCounter_aux s (levelsCounter_aux p [0]) = levelsCounter_aux (hd s # tl s) (levelsCounter_aux p [0])"
      by simp
    with `marked (hd s)` show ?thesis
      by simp
  qed
  also
  have "\<dots> = levelsCounter_aux p [0] @ (levelsCounter_aux (tl s) [1])"
    by (simp add: levelsCounter_aux_startIrellevant)
  finally 
  have "levelsCounter a = levelsCounter p @ (levelsCounter_aux (tl s) [1])"
    unfolding levelsCounter_def
    by simp
  moreover
  have "levelsCounter_aux (tl s) [1] \<noteq> []"
    by (simp add: levelsCounter_auxNotEmpty)
  ultimately
  show ?thesis
    by simp
qed


(*--------------------------------------------------------------------------------*)
subsection{* Prefix before last marked element *}

consts prefixBeforeLastMarked  :: "'a Trail \<Rightarrow> 'a Trail"
primrec
"prefixBeforeLastMarked [] = []"
"prefixBeforeLastMarked (h#t) =  (if (marked h) \<and> (markedElements t) = [] then [] else (h#(prefixBeforeLastMarked t)))"

lemma prefixBeforeLastMarkedIsPrefixBeforeLastLevel:
  assumes "markedElements M \<noteq> []"
  shows "prefixBeforeLastMarked M = prefixToLevel ((currentLevel M) - 1) M"
using assms
proof (induct M)
  case Nil
  thus ?case
    by simp
next
  case (Cons a M')
  thus ?case
  proof (cases "marked a")
    case True
    hence "currentLevel (a # M') \<ge> 1"
      using intLengthNonEmptyGeq1[of "markedElements (a#M')"]
      unfolding currentLevel_def
      by simp
    with True Cons show ?thesis
      using intLengthNonEmptyGeq1[of "markedElements M'"]
      using prefixToLevel_auxIncreaseAuxilaryCounter[of "0" "1" "M'" "currentLevel M' - 1"]
      unfolding prefixToLevel_def
      unfolding currentLevel_def
      by auto
  next
    case False
    with Cons show ?thesis
      unfolding prefixToLevel_def
      unfolding currentLevel_def
      by auto
  qed
qed

lemma isPrefixPrefixBeforeLastMarked:
  shows "isPrefix (prefixBeforeLastMarked M) M"
unfolding isPrefix_def
by (induct M) auto

lemma lastMarkedNotInPrefixBeforeLastMarked:
  assumes "uniq (elements M)" and "markedElements M \<noteq> []"
  shows "\<not> (lastMarked M) mem (elements (prefixBeforeLastMarked M))"
using assms
unfolding lastMarked_def
by (induct M) (auto split: split_if_asm simp add: markedElementsAreElements)

lemma uniqImpliesPrefixBeforeLastMarkedIsPrefixBeforeLastMarked:
  assumes "markedElements M \<noteq> []" and "\<not> (lastMarked M) mem (elements M)"
  shows "prefixBeforeLastMarked M = prefixBeforeElement (lastMarked M) M"
using assms
unfolding lastMarked_def
proof (induct M)
  case Nil
  thus ?case
    by auto
next
  case (Cons a M')
  show ?case
  proof (cases "marked a \<and> (markedElements M') = []")
    case True
    thus ?thesis
      unfolding lastMarked_def
      by auto
  next
    case False
    hence "last (markedElements (a # M')) = last (markedElements M')"
      by auto
    thus ?thesis
      using Cons
      by (auto split: split_if_asm simp add: markedElementsAreElements)
  qed
qed

lemma markedElementsAreElementsBeforeLastDecisionAndLastDecision: 
  assumes "markedElements M \<noteq> []"
  shows "(markedElements M) = (markedElements (prefixBeforeLastMarked M)) @ [lastMarked M]"
using assms
unfolding lastMarked_def
by (induct M) (auto split: split_if_asm)

end