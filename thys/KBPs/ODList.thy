(*<*)
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory ODList
imports Main List_local
begin
(*>*)

text{*

Define a type of ordered distinct lists, intended to represent sets.

The advantage of this representation is that it is isomorphic to the
set of finite sets. Conversely it requires the carrier type to be a
linear order.

FIXME provide a bunch of invariant-preserving list operations too.

FIXME note this representation does not arise from a quotient on
lists. We need to consider only the sorted lists, which we could
quotient under membership. Starting with all lists we have junk
representations.

FIXME Based on Florian Haftmann's DList.thy and Nipkow's mergesort
proofs.

*}

context linorder
begin

text{* "Absorbing" mergesort, a variant of Tobias Nipkow's proof from
1992. FIXME this is a tad pointless, but we can aim to make it
efficient...*}

fun
  merge :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "merge [] ys = ys"
| "merge xs [] = xs"
| "merge (x#xs) (y#ys) =
    (if x = y then merge xs (y#ys)
             else if x < y then x # merge xs (y#ys)
                           else y # merge (x#xs) ys)"

(*<*)
lemma set_merge[simp]:
  "set (merge xs ys) = set (xs @ ys)"
  by (induct xs ys rule: merge.induct) auto

lemma distinct_sorted_merge[simp]:
  "\<lbrakk> distinct xs; distinct ys; sorted xs; sorted ys \<rbrakk>
     \<Longrightarrow> distinct (merge xs ys) \<and> sorted (merge xs ys)"
  by (induct xs ys rule: merge.induct) (auto iff: sorted_Cons)
(*>*)

text{* Deal a list into two sublists.

FIXME what is the most efficient thing to do here? This does a lot
more allocation than one might like.

Probably best is to @{term "map (op # [])"} and merge pairs of
sublists until there is only one left.

*}

definition
  deal_body :: "'a \<Rightarrow> bool \<times> ('a list \<times> 'a list) \<Rightarrow> bool \<times> ('a list \<times> 'a list)"
where
  [code]: "deal_body \<equiv> \<lambda>x (b, ys, zs). if b then (False, x # ys, zs) else (True, ys, x # zs)"

definition
  deal :: "'a list \<Rightarrow> 'a list \<times> 'a list"
where
  [code]: "deal xs \<equiv> snd (foldr deal_body xs (False, [], []))"

(*<*)
lemma length_deal_aux:
  "foldr deal_body zs (b, ([], [])) = (b', xs, ys)
     \<Longrightarrow> length xs < Suc (length zs)
       \<and> length ys < Suc (length zs)"
proof(induct zs arbitrary: as bs b b' xs ys)
  case (Cons z zs)
  then obtain b'' xs' ys'
    where F: "foldr deal_body zs (b, [], []) = (b'', xs', ys')"
    apply (case_tac "foldr deal_body zs (b, [], [])")
    apply auto
    done
  with Cons(1)
  have "length xs' < Suc (length zs) \<and> length ys' < Suc (length zs)"
    by blast
  with F Cons(2) show ?case
    unfolding deal_body_def
    apply simp
    apply (fold deal_body_def)+
    apply (cases b'')
    apply auto
    done
qed simp

lemma length_deal[simp]:
  "(xs, ys) = deal zs \<Longrightarrow> length xs < Suc (length zs) \<and> length ys < Suc (length zs)"
  unfolding deal_def
  apply (cases "foldr deal_body zs (False, [], [])")
  using length_deal_aux
  apply simp
  done

lemma set_deal_aux:
  "foldr deal_body zs (b, ([], [])) = (b', xs, ys)
     \<Longrightarrow> set xs \<union> set ys = set zs"
proof(induct zs arbitrary: as bs b b' xs ys)
  case (Cons z zs)
  then obtain b'' xs' ys'
    where F: "foldr deal_body zs (b, [], []) = (b'', xs', ys')"
    apply (case_tac "foldr deal_body zs (b, [], [])")
    apply auto
    done
  with Cons have "set xs' \<union> set ys' = set zs" by simp
  with F Cons(2) show ?case
    unfolding deal_body_def
    apply simp_all
    apply (fold deal_body_def)+
    apply (cases b'')
     apply clarsimp
    apply clarsimp
    done
qed simp

lemma set_deal:
  "deal zs = (xs, ys) \<Longrightarrow> set xs \<union> set ys = set zs"
  unfolding deal_def
  apply (cases "foldr deal_body zs (False, [], [])")
  using set_deal_aux
  apply simp
  done

lemma distinct_deal_aux:
  "\<lbrakk> foldr deal_body zs (b, ([], [])) = (b', xs, ys); distinct zs \<rbrakk>
     \<Longrightarrow> distinct xs \<and> distinct ys \<and> set xs \<union> set ys = set zs"
proof(induct zs arbitrary: as bs b b' xs ys)
  case (Cons z zs)
  then obtain b'' xs' ys'
    where F: "foldr deal_body zs (b, [], []) = (b'', xs', ys')"
    apply (case_tac "foldr deal_body zs (b, [], [])")
    apply auto
    done
  with Cons have "distinct xs' \<and> distinct ys' \<and> set xs' \<union> set ys' = set zs" by simp
  with F Cons(2) Cons(3) show ?case
    unfolding deal_body_def
    apply simp_all
    apply (fold deal_body_def)+
    apply (cases b'')
     apply clarsimp
     apply blast
    apply clarsimp
    apply blast
    done
qed simp

lemma distinct_deal[simp]:
  "\<lbrakk> (xs, ys) = deal zs; distinct zs \<rbrakk> \<Longrightarrow> distinct xs \<and> distinct ys"
  unfolding deal_def
  apply (cases "foldr deal_body zs (False, [], [])")
  using distinct_deal_aux
  apply simp
  done

(*>*)

text{* The "absorbing" sort itself. *}

fun
  mergesort :: "'a list \<Rightarrow> 'a list"
where
  "mergesort []  = []"
| "mergesort [x] = [x]"
| "mergesort (x # y # zs) =
     (let (xs, ys) = deal zs
       in merge (mergesort (x # xs)) (mergesort (y # ys)))"

(*<*)

declare mergesort.simps [code]

lemma mergesort_distinct_sorted:
  "distinct (mergesort xs) \<and> sorted (mergesort xs)"
  by (induct xs rule: mergesort.induct) (auto split: split_split)

lemma mergesort_set:
  "set (mergesort xs) = set xs"
proof(induct xs rule: mergesort.induct)
  case (3 x y zs)
  hence X: "\<And>xs ys. deal zs = (xs, ys) \<Longrightarrow> set (mergesort (x # xs)) = set (x # xs)"
    and Y: "\<And>xs ys. deal zs = (xs, ys) \<Longrightarrow> set (mergesort (y # ys)) = set (y # ys)"
    by force+
  show ?case
    apply simp
    apply (cases "deal zs")
    apply (frule set_deal[symmetric])
    apply (frule X)
    apply (frule Y)
    apply auto
    done
qed simp_all

lemma mergesort_remdups:
  "remdups (mergesort xs) = mergesort xs"
  by (simp add: mergesort_distinct_sorted)

lemma mergesort_idle[simp]:
  "\<lbrakk> distinct xs; sorted xs \<rbrakk> \<Longrightarrow> mergesort xs = xs"
  apply (rule map_sorted_distinct_set_unique[where f=id])
  using mergesort_distinct_sorted mergesort_set
  apply auto
  done

(*>*)

end (* FIXME context *)

section {* The @{term "odlist"} type *}

typedef (open) ('a :: linorder) odlist = "{ x::'a list . sorted x \<and> distinct x }"
  morphisms toList odlist_Abs
  apply (rule exI[where x="[]"])
  apply simp
  done

lemma distinct_toList[simp]: "distinct (toList xs)"
  using toList by auto

lemma sorted_toList[simp]: "sorted (toList xs)"
  using toList by auto

text{* FIXME code generator voodoo: this is the constructor for the
abstract type. *}

definition
  ODList :: "('a :: linorder) list \<Rightarrow> 'a odlist"
where
  "ODList \<equiv> odlist_Abs \<circ> mergesort"

lemma toList_ODList:
  "toList (ODList xs) = mergesort xs"
  unfolding ODList_def by (simp add: mergesort_distinct_sorted odlist_Abs_inverse)

lemma ODList_toList[simp, code abstype]:
  "ODList (toList xs) = xs"
  unfolding ODList_def
  apply (cases xs)
  apply (simp add: odlist_Abs_inverse)
  done

text{* Runtime cast from @{typ "'a list"} into @{typ "'a
odlist"}. This is just a renaming of @{term "ODList"} -- names are
significant to the code generator's abstract type machinery. *}

definition
  fromList :: "('a :: linorder) list \<Rightarrow> 'a odlist"
where
  "fromList \<equiv> ODList"

lemma toList_fromList[code abstract]:
  "toList (fromList xs) = mergesort xs"
  unfolding fromList_def by (simp add: toList_ODList)

subsection{* Basic properties: equality, finiteness *}

(*<*)
declare toList_inject[iff]
(*>*)

instantiation odlist :: (linorder) equal
(*<*)
begin

definition [code]:
  "HOL.equal A B \<longleftrightarrow> odlist_equal (toList A) (toList B)"

instance proof
qed (simp add: equal_odlist_def)

end
(*>*)

instance odlist :: ("{finite, linorder}") finite
(*<*)
proof
  let ?ol = "UNIV :: 'a odlist set"
  let ?s = "UNIV :: 'a set set"
  have "finite ?s" by simp
  moreover then have "?ol \<subseteq> range (odlist_Abs \<circ> sorted_list_of_set)"
    apply -
    apply rule
    apply auto
    apply (rule_tac x="set (toList x)" in image_eqI)
    apply simp_all
    apply (simp only: sorted_list_of_set_sort_remdups)
    apply (case_tac x)
    apply (simp add: odlist_Abs_inverse odlist_Abs_inject)
    done
  ultimately show "finite ?ol" by (blast intro: finite_surj)
qed
(*>*)

subsection{* Constants *}

definition
  empty :: "('a :: linorder) odlist"
where
  "empty \<equiv> ODList []"

lemma toList_empty[simp, code abstract]:
  "toList empty = []"
  unfolding empty_def by (simp add: toList_ODList)

subsection{* Operations *}

text{* FIXME we need to hoist all list operations we want to use and
show they preserve the invariant. We cannot generate code for toList,
so there's no getting around this. *}

subsubsection{* toSet *}

definition
  toSet :: "('a :: linorder) odlist \<Rightarrow> 'a set"
where
  "toSet X = set (toList X)"

lemma toSet_empty[simp]:
  "toSet empty = {}"
  unfolding toSet_def empty_def by (simp add: toList_ODList)

lemma toSet_ODList[simp]:
  "\<lbrakk> distinct xs; sorted xs \<rbrakk> \<Longrightarrow> toSet (ODList xs) = set xs"
  unfolding toSet_def by (simp add: toList_ODList)

lemma toSet_fromList_set[simp]:
  "toSet (fromList xs) = set xs"
  unfolding toSet_def fromList_def
  by (simp add: toList_ODList mergesort_set)

lemma toSet_inj[intro, simp]: "inj toSet"
  apply (rule injI)
  unfolding toSet_def
  apply (case_tac x)
  apply (case_tac y)
  apply (auto iff: odlist_Abs_inject odlist_Abs_inverse sorted_distinct_set_unique)
  done

lemma toSet_eq_iff:
  "X = Y \<longleftrightarrow> toSet X = toSet Y"
  by (blast dest: injD[OF toSet_inj])

subsubsection{* head *}

definition
  hd :: "('a :: linorder) odlist \<Rightarrow> 'a"
where
  [code]: "hd \<equiv> List.hd \<circ> toList"

lemma hd_toList: "toList xs = y # ys \<Longrightarrow> ODList.hd xs = y"
  unfolding hd_def by simp

subsubsection{* Filter *}

definition
  filter :: "(('a :: linorder) \<Rightarrow> bool) \<Rightarrow> 'a odlist \<Rightarrow> 'a odlist"
where
  "filter P xs \<equiv> ODList (List.filter P (toList xs))"

lemma toList_filter[simp, code abstract]:
  "toList (filter P xs) = List.filter P (toList xs)"
  unfolding filter_def by (simp add: toList_ODList)

lemma toSet_filter[simp]:
  "toSet (filter P xs) = { x \<in> toSet xs . P x }"
  unfolding filter_def
  apply simp
  apply (simp add: toSet_def)
  done

subsubsection{* All *}

definition
  odlist_all :: "('a :: linorder \<Rightarrow> bool) \<Rightarrow> 'a odlist \<Rightarrow> bool"
where
  [code]: "odlist_all P xs \<equiv> list_all P (toList xs)"

lemma odlist_all_iff:
  "odlist_all P xs \<longleftrightarrow> (\<forall>x \<in> toSet xs. P x)"
  unfolding odlist_all_def toSet_def by (simp only: list_all_iff)

lemma odlist_all_cong [fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x \<in> toSet ys \<Longrightarrow> f x = g x) \<Longrightarrow> odlist_all f xs = odlist_all g ys"
  by (simp add: odlist_all_iff)

subsubsection{* Difference *}

definition
  difference :: "('a :: linorder) odlist \<Rightarrow> 'a odlist \<Rightarrow> 'a odlist"
where
  "difference xs ys = ODList (List_local.difference (toList xs) (toList ys))"

lemma toList_difference[simp, code abstract]:
  "toList (difference xs ys) = List_local.difference (toList xs) (toList ys)"
  unfolding difference_def by (simp add: toList_ODList)

lemma toSet_difference[simp]:
  "toSet (difference xs ys) = toSet xs - toSet ys"
  unfolding difference_def
  apply simp
  apply (simp add: toSet_def)
  done

subsubsection{* Intersection *}

definition
  intersection :: "('a :: linorder) odlist \<Rightarrow> 'a odlist \<Rightarrow> 'a odlist"
where
  "intersection xs ys = ODList (List_local.intersection (toList xs) (toList ys))"

lemma toList_intersection[simp, code abstract]:
  "toList (intersection xs ys) = List_local.intersection (toList xs) (toList ys)"
  unfolding intersection_def by (simp add: toList_ODList)

lemma toSet_intersection[simp]:
  "toSet (intersection xs ys) = toSet xs \<inter> toSet ys"
  unfolding intersection_def
  apply simp
  apply (simp add: toSet_def)
  done

subsubsection{* Union *}

definition
  union :: "('a :: linorder) odlist \<Rightarrow> 'a odlist \<Rightarrow> 'a odlist"
where
  "union xs ys = ODList (merge (toList xs) (toList ys))"

lemma toList_union[simp, code abstract]:
  "toList (union xs ys) = merge (toList xs) (toList ys)"
  unfolding union_def by (simp add: toList_ODList)

lemma toSet_union[simp]:
  "toSet (union xs ys) = toSet xs \<union> toSet ys"
  unfolding union_def
  apply simp
  apply (simp add: toSet_def)
  done

subsubsection{* Case distinctions *}

text{*

FIXME we construct ODLists out of lists, so talk in terms of those,
not a one-step constructor we don't use.

*}

lemma distinct_sorted_induct [consumes 2, case_names Nil insert]:
  assumes "distinct xs"
  assumes "sorted xs"
  assumes base: "P []"
  assumes step: "\<And>x xs. \<lbrakk> distinct (x # xs); sorted (x # xs); P xs \<rbrakk> \<Longrightarrow> P (x # xs)"
  shows "P xs"
using `distinct xs` `sorted xs` proof (induct xs)
  case Nil from `P []` show ?case .
next
  case (Cons x xs)
  then have "distinct (x # xs)" and "sorted (x # xs)" and "P xs" by (simp_all add: sorted_Cons)
  with step show "P (x # xs)" .
qed

lemma odlist_induct [case_names empty insert, cases type: odlist]:
  assumes empty: "\<And>dxs. dxs = empty \<Longrightarrow> P dxs"
  assumes insrt: "\<And>dxs x xs. \<lbrakk> dxs = fromList (x # xs); distinct (x # xs); sorted (x # xs); P (fromList xs) \<rbrakk>
                            \<Longrightarrow> P dxs"
  shows "P dxs"
proof (cases dxs)
  case (odlist_Abs xs)
  then have dxs: "dxs = ODList xs" and distinct: "distinct xs" and sorted: "sorted xs"
    by (simp_all add: ODList_def)
  from `distinct xs` and `sorted xs` have "P (ODList xs)"
  proof (induct xs rule: distinct_sorted_induct)
    case Nil from empty show ?case by (simp add: empty_def)
  next
    case (insert x xs) thus ?case
      apply -
      apply (rule insrt)
      apply (auto iff: sorted_Cons fromList_def)
      done
  qed
  with dxs show "P dxs" by simp
qed

lemma odlist_case [case_names empty insert, cases type: odlist]:
  assumes empty: "dxs = empty \<Longrightarrow> P"
  assumes insert: "\<And>x xs. \<lbrakk> dxs = fromList (x # xs); distinct (x # xs); sorted (x # xs) \<rbrakk>
                            \<Longrightarrow> P"
  shows P
proof (cases dxs)
  case (odlist_Abs xs)
  then have dxs: "dxs = ODList xs" and distinct: "distinct xs" and sorted: "sorted xs"
    by (simp_all add: ODList_def)
  show P proof (cases xs)
    case Nil with dxs have "dxs = empty" by (simp add: empty_def)
    with empty show P .
  next
    case (Cons y ys)
    with dxs distinct sorted insert
    show P by (simp add: fromList_def)
  qed
qed

subsubsection{* Relations *}

text{*

FIXME

*}

type_synonym 'a ODRelation = "('a \<times> 'a) odlist"

subsubsection{* Image *}

text{* Note the output of @{term "List_local.image"} is not guaranteed
to be ordered or distinct. Also the relation need not be
monomorphic. *}

definition
  image :: "('a :: linorder \<times> 'b :: linorder) odlist \<Rightarrow> 'a odlist \<Rightarrow> 'b odlist"
where
  "image R xs = ODList (List_local.image (toList R) (toList xs))"

lemma toList_image[simp, code abstract]:
  "toList (image R xs) = mergesort (List_local.image (toList R) (toList xs))"
  unfolding image_def by (simp add: toList_ODList)

lemma toSet_image[simp]:
  "toSet (image R xs) = toSet R `` toSet xs"
  unfolding image_def by (simp add: toSet_def toList_ODList mergesort_set)

subsubsection{* Linear order *}

text{* FIXME Lexicographic ordering on lists. Executable, unlike in
List.thy. *}

instantiation odlist :: (linorder) linorder
begin

fun
  less_eq_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "less_eq_list [] ys = True"
| "less_eq_list xs [] = False"
| "less_eq_list (x # xs) (y # ys) = (x < y \<or> (x = y \<and> less_eq_list xs ys))"

lemma less_eq_list_nil_inv: "less_eq_list xs [] \<Longrightarrow> xs = []"
  by (cases xs) simp_all

lemma less_eq_list_cons_inv: "less_eq_list (x # xs) yys \<Longrightarrow> \<exists>y ys. yys = y # ys \<and> (x < y \<or> (x = y \<and> less_eq_list xs ys))"
  by (cases yys) auto

lemma less_eq_list_refl:
  "less_eq_list xs xs"
  by (induct xs) simp_all

lemma less_eq_list_trans:
  "\<lbrakk> less_eq_list xs ys; less_eq_list ys zs \<rbrakk> \<Longrightarrow> less_eq_list xs zs"
  apply (induct xs ys arbitrary: zs rule: less_eq_list.induct)
    apply simp
   apply simp
  apply clarsimp
  apply (erule disjE)
   apply (drule less_eq_list_cons_inv)
   apply clarsimp
   apply (erule disjE)
    apply auto[1]
   apply auto[1]
  apply (auto dest: less_eq_list_cons_inv)
  done

lemma less_eq_list_antisym:
  "\<lbrakk> less_eq_list xs ys; less_eq_list ys xs \<rbrakk> \<Longrightarrow> xs = ys"
  by (induct xs ys rule: less_eq_list.induct) (auto dest: less_eq_list_nil_inv)

lemma less_eq_list_linear: "less_eq_list xs ys \<or> less_eq_list ys xs"
  by (induct xs ys rule: less_eq_list.induct) auto

definition
  less_eq_odlist :: "'a odlist \<Rightarrow> 'a odlist \<Rightarrow> bool"
where
  "xs \<le> ys \<equiv> less_eq_list (toList xs) (toList ys)"

fun
  less_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "less_list [] [] = False"
| "less_list [] ys = True"
| "less_list xs [] = False"
| "less_list (x # xs) (y # ys) = (x < y \<or> (x = y \<and> less_list xs ys))"

definition
  less_odlist :: "'a odlist \<Rightarrow> 'a odlist \<Rightarrow> bool"
where
  "xs < ys \<equiv> less_list (toList xs) (toList ys)"

lemma less_eq_list_not_le:
  "(less_list xs ys) = (less_eq_list xs ys \<and> \<not> less_eq_list ys xs)"
  by (induct xs ys rule: less_list.induct) auto

instance
  apply intro_classes
  unfolding less_eq_odlist_def less_odlist_def
  using less_eq_list_not_le less_eq_list_refl less_eq_list_trans less_eq_list_antisym
  apply blast
  using less_eq_list_not_le less_eq_list_refl less_eq_list_trans less_eq_list_antisym
  apply blast
  using less_eq_list_not_le less_eq_list_refl less_eq_list_trans less_eq_list_antisym
  apply blast
  using less_eq_list_not_le less_eq_list_refl less_eq_list_trans less_eq_list_antisym
  apply blast
  apply (rule less_eq_list_linear)
  done

end

subsubsection{* Finite maps *}

text{*

FIXME A few operations on finite maps.

Unlike the AssocList theory, ODLists give us canonical
representations, so we can order them. Our tabulate has the wrong type
(we want to take an odlist, not a list) so we can't use that
part of the framework.

*}

definition
  lookup :: "('a :: linorder \<times> 'b :: linorder) odlist \<Rightarrow> ('a \<rightharpoonup> 'b)"
where
  [code]: "lookup = map_of \<circ> toList"

text{* FIXME specific to ODLists. *}

definition
  tabulate :: "('a :: linorder) odlist \<Rightarrow> ('a \<Rightarrow> 'b :: linorder) \<Rightarrow> ('a \<times> 'b) odlist"
where
  "tabulate ks f = ODList (List.map (\<lambda>k. (k, f k)) (toList ks))"

(* FIXME mono + inj \<Longrightarrow> strictly increasing? Isabelle def? See Orderings. *)

definition (in order) mono_on :: "('a \<Rightarrow> 'b\<Colon>order) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "mono_on f X \<longleftrightarrow> (\<forall>x\<in>X. \<forall>y\<in>X. x \<le> y \<longrightarrow> f x \<le> f y)"

lemma (in order) mono_onI [intro?]:
  fixes f :: "'a \<Rightarrow> 'b\<Colon>order"
  shows "(\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y) \<Longrightarrow> mono_on f X"
  unfolding mono_on_def by simp

lemma (in order) mono_onD [dest?]:
  fixes f :: "'a \<Rightarrow> 'b\<Colon>order"
  shows "mono_on f X \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
  unfolding mono_on_def by simp

lemma (in order) mono_on_subset:
  fixes f :: "'a \<Rightarrow> 'b\<Colon>order"
  shows "mono_on f X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> mono_on f Y"
  unfolding mono_on_def by auto

lemma sorted_mono_map:
  "\<lbrakk> sorted xs; mono_on f (set xs) \<rbrakk> \<Longrightarrow> sorted (List.map f xs)"
  apply (induct xs)
   apply simp
  apply (simp add: sorted_Cons)
  apply (cut_tac X="insert a (set xs)" and Y="set xs" in mono_on_subset)
  apply (auto dest: mono_onD)
  done

lemma mergesort_map:
  "\<lbrakk> distinct xs; sorted xs; inj_on f (set xs); mono_on f (set xs) \<rbrakk> \<Longrightarrow> mergesort (List.map f xs) = List.map f xs"
  apply (rule mergesort_idle)
   apply (simp add: distinct_map)
  apply (simp add: sorted_mono_map)
  done

lemma tabulate_odlist[simp, code abstract]:
  "toList (tabulate ks f) = List.map (\<lambda>k. (k, f k)) (toList ks)"
  unfolding tabulate_def
  apply (simp add: toList_ODList)
  apply (subst mergesort_map)
  apply simp_all
   apply (rule inj_onI)
   apply simp
  apply (rule mono_onI)
  unfolding less_eq_prod_def
  apply auto
  done

lemma lookup_tabulate [simp]:
  "lookup (tabulate ks f) = (Some o f) |` toSet ks"
proof(induct ks rule: odlist_induct)
  case (empty dxs) thus ?case unfolding tabulate_def lookup_def by (simp add: toList_ODList)
next
  case (insert dxs x xs)
  from insert have "map_of (List.map (\<lambda>k. (k, f k)) xs) = map_of (mergesort (List.map (\<lambda>k. (k, f k)) xs))"
    apply (subst mergesort_map)
    apply (auto intro: inj_onI simp: sorted_Cons)
    apply (rule mono_onI)
    unfolding less_eq_prod_def
    apply auto
    done
  also from insert have "... = lookup (tabulate (fromList xs) f)"
    unfolding tabulate_def lookup_def
    by (simp add: toList_ODList toList_fromList sorted_Cons)
  also from insert have "... = (Some \<circ> f) |` toSet (fromList xs)"
    by (simp only: toSet_fromList_set)
  finally have IH: "map_of (List.map (\<lambda>k. (k, f k)) xs) = (Some \<circ> f) |` toSet (fromList xs)" .
  from insert have "lookup (tabulate dxs f) = map_of (toList (ODList (List.map (\<lambda>k. (k, f k)) (x # xs))))"
    unfolding tabulate_def lookup_def by (simp add: toList_fromList)
  also have "... = map_of (mergesort (List.map (\<lambda>k. (k, f k)) (x # xs)))"
    by (simp only: toList_ODList)
  also from insert have "... = map_of (List.map (\<lambda>k. (k, f k)) (x # xs))"
    apply (subst mergesort_map)
    apply (auto intro: inj_onI)
    apply (rule mono_onI)
    unfolding less_eq_prod_def
    apply auto
    done
  also with insert IH have "... = (Some \<circ> f) |` toSet dxs"
    by (auto simp add: restrict_map_def fun_eq_iff)
  finally show ?case .
qed

(*<*)
end
(*>*)
