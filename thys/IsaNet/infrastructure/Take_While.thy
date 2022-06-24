(*******************************************************************************

  Project: IsaNet

  Author:  Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
           Tobias Klenze, ETH Zurich <tobias.klenze@inf.ethz.ch>
           Andreas Lochbiehler (initial Version)
  Version: JCSPaper.1.0
  Isabelle Version: Isabelle2021-1

  Copyright (c) 2022
  Licence: Mozilla Public License 2.0 (MPL) / BSD-3-Clause (dual license)

*******************************************************************************)

theory Take_While imports Tools
begin

(******************************************************************************)
section \<open>takeW, holds and extract: Applying context-sensitive checks on list elements\<close>
(******************************************************************************)

text\<open>This theory defines three functions, takeW, holds and extract. It is embedded in a locale
       that takes predicate P as an input that works on three arguments: pre, x, and z. x is an
       element of a list, while pre is the left neighbour on that list and z is the right neighbour.
       They are all of the same type 'a, except that pre and z are of 'a option type, since
       neighbours don't always exist at the beginning and the end of lists. The functions takeW and
       holds work on an 'a list (with an additional pre and z 'a option parameter).
       Both repeatedly apply P on elements xi in the list with their neighbours as context:\<close>
text_raw \<open>\begin{verbatim}
          holds pre (x1#x2#...#xn#[]) z = 
              P pre x1 x2 /\ P x1 x2 x3 /\ ... /\ P (xn-2) (xn-1) xn /\ P xn-1 xn z
          takeW pre (x1#x2#...#xn#[]) z = the prefix of the list for which 'holds' holds.
\end{verbatim}\<close>
text\<open>  extract is a function that returns the last element of the list, or z if the list is empty.

       @{text "holds_takeW_extract"} is an interesting lemma that relates all three functions.

       In our applications, we usually invoke takeW and holds with the parameters None l None, where
       l is a list of elements which we want to check for P (using their neighboring elements as 
       context). takeW and holds thus mostly have the pre and z parameters for their recursive 
       definition and induction schemes.\<close>

text\<open>The predicate P gets both a predecessor and a successor (if existant). 
We originally used this theory for both the interface check (which makes use of the predecessor)
and the cryptographic check (which makes use of the successor). However, with the introduction of
mutable uinfo fields, we have split up the takeWhile formalization for the cryptographic check into
a separate theory (@{text "Take_While_Update"}). Since the interface check does not make use of the
successor, the third parameter of the function P defined in this theory is not actually required.\<close>

locale TW =
  fixes P :: "('a option \<Rightarrow> 'a \<Rightarrow> 'a option \<Rightarrow> bool)"
begin

subsection\<open>Definitions\<close>

text\<open>holds returns true iff every element of a list, together with its context, satisfies P.\<close>
fun holds :: "'a option \<Rightarrow> 'a list \<Rightarrow> 'a option \<Rightarrow> bool"
where
  "holds pre (x # y # ys) nxt \<longleftrightarrow> P pre x (Some y) \<and> holds (Some x) (y # ys) nxt"
| "holds pre [x] nxt \<longleftrightarrow> P pre x nxt"
| "holds pre [] nxt \<longleftrightarrow> True"

text\<open>holds returns the longest prefix of a list for every element, together with its context, satisfies P.\<close>
function takeW :: "'a option \<Rightarrow> 'a list \<Rightarrow> 'a option \<Rightarrow> 'a list" where
  "takeW _ [] _ = []"
| "P pre x xo \<Longrightarrow> takeW pre [x] xo = [x]"
| "\<not> P pre x xo \<Longrightarrow> takeW pre [x] xo = []"
| "P pre x (Some y) \<Longrightarrow> takeW pre (x # y # xs) xo = x # takeW (Some x) (y # xs) xo"
| "\<not> P pre x (Some y) \<Longrightarrow> takeW pre (x # y # xs) xo = []"
apply auto
  by (metis remdups_adj.cases)
termination
  by lexicographic_order

text\<open>extract returns the last element of a list, or nxt if the list is empty.\<close>
fun "extract" :: "'a option \<Rightarrow> 'a list \<Rightarrow> 'a option \<Rightarrow> 'a option"
where
  "extract pre (x # y # ys) nxt = (if P pre x (Some y) then extract (Some x) (y # ys) nxt else Some x)"
| "extract pre [x] nxt = (if P pre x nxt then nxt else (Some x))"
| "extract pre [] nxt = nxt"


subsection\<open>Lemmas\<close>

text \<open>Lemmas packing singleton and at least two element cases into a single equation.\<close>

lemma takeW_singleton:
  "takeW pre [x] xo = (if P pre x xo then [x] else [])"
by (simp)

lemma takeW_two_or_more:
  "takeW pre (x # y # zs) xo = (if P pre x (Some y) then x # takeW (Some x) (y # zs) xo else [])"
by (simp)


text \<open>Some lemmas for splitting the tail of the list argument.\<close>

text \<open>Splitting lemma formulated with if-then-else rather than case.\<close>

lemma takeW_split_tail:
  "takeW pre (x # xs) nxt =
     (if xs = []
      then (if P pre x nxt then [x] else [])
      else (if P pre x (Some (hd xs)) then x # takeW (Some x) xs nxt else []))"
by (cases xs, auto)

lemma extract_split_tail:
  "extract pre (x # xs) nxt =
     (case xs of
          [] \<Rightarrow> (if P pre x nxt then nxt else (Some x))
        | (y # ys) \<Rightarrow> (if P pre x (Some y) then extract (Some x) (y # ys) nxt else Some x))"
by (cases xs, auto)

lemma holds_split_tail:
  "holds pre (x # xs) nxt \<longleftrightarrow>
      (case xs of
          [] \<Rightarrow> P pre x nxt
        | (y # ys) \<Rightarrow> P pre x (Some y) \<and> holds (Some x) (y # ys) nxt)"
by (cases xs, auto)

lemma holds_Cons_P:
  "holds pre (x # xs) nxt \<Longrightarrow> \<exists>y . P pre x y"
by (cases xs, auto)

lemma holds_Cons_holds:
  "holds pre (x # xs) nxt \<Longrightarrow> holds (Some x) xs nxt"
by (cases xs, auto)

lemmas tail_splitting_lemmas =
  extract_split_tail holds_split_tail

text \<open>Interaction between @{term holds}, @{term takeWhile}, and @{term extract}.\<close>
declare if_split_asm [split]

lemma holds_takeW_extract: "holds pre (takeW pre xs nxt) (extract pre xs nxt)"
apply(induction pre xs nxt rule: takeW.induct)
apply auto
subgoal for pre x y ys
  apply(cases "ys")
  apply(simp_all)
  done
done

text \<open>Interaction of @{term holds}, @{term takeWhile}, and @{term extract}
with @{term append}.\<close>

lemma takeW_append:
  "takeW pre (xs @ ys) nxt =
     (let y = case ys of [] \<Rightarrow> nxt | x # _ \<Rightarrow> Some x in
     (let new_pre = case xs of [] \<Rightarrow> pre | _ \<Rightarrow> (Some (last xs)) in
        if holds pre xs y then xs @ takeW new_pre ys nxt
                           else takeW pre xs y))"
apply(induction pre xs nxt rule: takeW.induct)
apply (simp_all add: Let_def split: list.split)
done

lemma holds_append:
  "holds pre (xs @ ys) nxt =
     (let y = case ys of [] \<Rightarrow> nxt | x # _ \<Rightarrow> Some x in
     (let new_pre = case xs of [] \<Rightarrow> pre | _ \<Rightarrow> (Some (last xs)) in
        holds pre xs y \<and> holds new_pre ys nxt))"
apply(induction pre xs nxt rule: takeW.induct)
apply (auto simp add: Let_def split: list.split)
done

corollary holds_cutoff:
  "holds pre (l1@l2) nxt \<Longrightarrow> \<exists> nxt' . holds pre l1 nxt'"
by (meson holds_append)

lemma extract_append:
  "extract pre (xs @ ys) nxt =
     (let y = case ys of [] \<Rightarrow> nxt | x # _ \<Rightarrow> Some x in
     (let new_pre = case xs of [] \<Rightarrow> pre | _ \<Rightarrow> (Some (last xs)) in
        if holds pre xs y then extract new_pre ys nxt else extract pre xs y))"
apply(induction pre xs nxt rule: takeW.induct)
apply (simp_all add: Let_def split: list.split)
done

lemma takeW_prefix:
  "prefix (takeW pre l nxt) l"
by (induction pre l nxt rule: takeW.induct) auto

lemma takeW_set: "t \<in> set (TW.takeW P pre l nxt) \<Longrightarrow> t \<in> set l"
by(auto intro: takeW_prefix elim: set_prefix)

lemma holds_implies_takeW_is_identity:
  "holds pre l nxt \<Longrightarrow> takeW pre l nxt = l"
by (induction pre l nxt rule: takeW.induct) auto

(*even stronger...*)
lemma holds_takeW_is_identity[simp]:
  "takeW pre l nxt = l \<longleftrightarrow> holds pre l nxt"
  by (induction pre l nxt rule: takeW.induct) auto


lemma takeW_takeW_extract:
  "takeW pre (takeW pre l nxt) (extract pre l nxt)
 = takeW pre l nxt"
using holds_takeW_extract holds_implies_takeW_is_identity
  by blast

text\<open>Show the equivalence of two takeW with different pres\<close>
lemma takeW_pre_eqI:
"\<lbrakk>\<And>x . l = [x] \<Longrightarrow> P pre x nxt \<longleftrightarrow> P pre' x nxt;
 \<And>x1 x2 l' . l = x1#x2#l' \<Longrightarrow> P pre x1 (Some x2) \<longleftrightarrow> P pre' x1 (Some x2)\<rbrakk> \<Longrightarrow>
 takeW pre l nxt = takeW pre' l nxt"
  apply(cases l)
  subgoal by auto
  subgoal for a list
    by(cases list, auto simp add: takeW_singleton takeW_split_tail)
  done

lemma takeW_replace_pre:
"\<lbrakk>P pre x1 n; n = ifhead xs nxt\<rbrakk> \<Longrightarrow> prefix (TW.takeW P pre' (x1#xs) nxt) (TW.takeW P pre (x1#xs) nxt)"
  apply(cases xs)
  by(auto simp add: takeW_singleton takeW_split_tail)

(******************************************************************************)
subsubsection \<open>Holds unfolding\<close>
(******************************************************************************)
text \<open>This section contains various lemmas that show how one can deduce P pre' x' nxt' for some of
        pre' x' nxt' out of a list l, for which we know that holds pre l nxt is true.\<close>

lemma holds_set_list: "\<lbrakk>holds pre l nxt; x \<in> set l\<rbrakk> \<Longrightarrow> \<exists> p y . P p x y"
 by (metis TW.holds_append holds_Cons_P split_list_first)

lemma holds_unfold: "holds pre l None \<Longrightarrow>
  l = [] \<or>
  (\<exists> x . l = [x] \<and> P pre x None) \<or>
  (\<exists> x y ys . l = (x#y#ys) \<and> P pre x (Some y) \<and> holds (Some x) (y#ys) None)"
apply auto by (meson holds.elims(2))

lemma holds_unfold_prexnxt:
  "\<lbrakk>suffix (x0#x1#x2#xs) l; holds pre l nxt\<rbrakk>
 \<Longrightarrow> P (Some x0) x1 (Some x2)"
  by (auto simp add: suffix_def TW.holds_append)

lemma holds_unfold_prexnxt':
  "\<lbrakk>holds pre l nxt; l = (zs@(x0#x1#x2#xs))\<rbrakk>
 \<Longrightarrow> P (Some x0) x1 (Some x2)"
  by (auto simp add: TW.holds_append)

lemma holds_unfold_xz:
  "\<lbrakk>suffix (x1#x2#xs) l; holds pre l nxt\<rbrakk> \<Longrightarrow> \<exists> pre'. P pre' x1 (Some x2)"
  by (auto simp add: suffix_def TW.holds_append)

lemma holds_unfold_prex:
  "\<lbrakk>suffix (x1#x2#xs) l; holds pre l nxt\<rbrakk> \<Longrightarrow> \<exists> nxt'. P (Some x1) x2 nxt'"
by (auto simp add: suffix_def TW.holds_append dest: holds_Cons_P)

lemma holds_suffix:
  "\<lbrakk>holds pre l nxt; suffix l' l\<rbrakk> \<Longrightarrow> \<exists> pre'. holds pre' l' nxt"
  by (metis holds_append suffix_def)

lemma holds_unfold_prelnil:
  "\<lbrakk>holds pre l nxt; l = (zs@(x0#x1#[]))\<rbrakk>
 \<Longrightarrow> P (Some x0) x1 nxt"
  by (auto simp add: TW.holds_append)

end
end
