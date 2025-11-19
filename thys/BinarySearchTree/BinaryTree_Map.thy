(*  Title:       Binary Search Trees, Isar-Style
    Author:      Viktor Kuncak, MIT CSAIL, November 2003
    Maintainer:  Larry Paulson <Larry.Paulson at cl.cam.ac.uk>
    License:     LGPL
*)

section \<open>Mostly Isar-style Reasoning for Binary Tree Operations\<close>
theory BinaryTree_Map imports BinaryTree begin

text \<open>We prove correctness of map operations
 implemented using binary search trees from BinaryTree.

 This document is LGPL.

 Author: Viktor Kuncak, MIT CSAIL, November 2003\<close>


(*============================================================*)
section \<open>Map implementation and an abstraction function\<close>
(*============================================================*)

type_synonym 
  'a tarray = "(index * 'a) Tree"

definition valid_tmap :: "'a tarray => bool" where
  "valid_tmap t \<equiv> sortedTree fst t"

declare valid_tmap_def [simp]

definition mapOf :: "'a tarray => index => 'a option" where
  \<comment> \<open>the abstraction function from trees to maps\<close>
  "mapOf t i \<equiv>
   (case (tlookup fst i t) of
     None => None
   | Some ia => Some (snd ia))"

(*============================================================*)
section \<open>Auxiliary Properties of our Implementation\<close>
(*============================================================*)

lemma mapOf_lookup1: "tlookup fst i t = None ==> mapOf t i = None"
  by (simp add: mapOf_def)

lemma mapOf_lookup2: "tlookup fst i t = Some (j,a) ==> mapOf t i = Some a"
  by (simp add: mapOf_def)

lemma mapOf_lookup3: 
    assumes h: "mapOf t i = None"
    shows "tlookup fst i t = None"
proof (cases "tlookup fst i t")
  case None 
  then show ?thesis by assumption
next 
  case (Some ia) 
  then show ?thesis
    by (metis h mapOf_def option.discI option.simps(5))
qed

lemma mapOf_lookup4: 
  assumes v: "valid_tmap t"
  assumes h: "mapOf t i = Some a"
  shows "tlookup fst i t = Some (i,a)"
proof (cases "tlookup fst i t")
  case None 
  then show ?thesis
    by (metis h mapOf_lookup1 option.discI)
next 
  case (Some ia) 
  then show ?thesis
    by (metis h mapOf_def option.simps(5) prod.exhaust_sel tlookup_some v
        valid_tmap_def)
qed

subsection \<open>Lemmas \<open>mapset_none\<close> and \<open>mapset_some\<close> establish 
              a relation between the set and map abstraction of the tree\<close>

lemma mapset_none: 
  assumes "valid_tmap t"
  shows "(mapOf t i = None) = (\<forall>a. (i,a) \<notin> setOf t)"
  using assms 
  unfolding valid_tmap_def
  by (metis mapOf_lookup1 mapOf_lookup3 not_None_eq split_pairs tlookup_none
      tlookup_some)

lemma mapset_some: 
  assumes "valid_tmap t"
  shows "(mapOf t i = Some a) = ((i,a) \<in> setOf t)"
  unfolding valid_tmap_def
  using assms mapOf_lookup2 mapOf_lookup4 tlookup_finds tlookup_some
  by fastforce

(*============================================================*)
section \<open>Empty Map\<close>
(*============================================================*)

lemma mnew_spec_valid: "valid_tmap Tip"
  by (simp add: mapOf_def)

lemma mtip_spec_empty: "mapOf Tip k = None"
  by (simp add: mapOf_def)


(*============================================================*)
section \<open>Map Update Operation\<close>
(*============================================================*)

definition mupdate :: "index => 'a => 'a tarray => 'a tarray" where
  "mupdate i a t \<equiv> binsert fst (i,a) t"

lemma  mupdate_map:
  assumes "valid_tmap t"
  shows "mapOf (mupdate i a t) = (mapOf t)(i |-> a)"
proof
  fix j
  let ?tr = "binsert fst (i,a) t"
  have upres: "mupdate i a t = ?tr" by (simp add: mupdate_def)
  from assms binsert_set 
  have setSpec: "setOf ?tr = setOf t - eqs fst (i,a) Un {(i,a)}" 
    by fastforce
  from assms binsert_sorted have vr: "valid_tmap ?tr" 
    by fastforce
  show "mapOf (mupdate i a t) j = ((mapOf t)(i |-> a)) j"
  proof (cases "i = j")
    case True 
    then show ?thesis
      using mapset_some setSpec upres vr by fastforce
  next 
    case False note i2nei = this
    from i2nei have rhs_res: "((mapOf t)(i |-> a)) j = mapOf t j" by auto
    have lhs_res: "mapOf (mupdate i a t) j = mapOf t j"
    proof (cases "mapOf t j")
      case None 
      then show ?thesis
        by (metis DiffD1 Un_empty_right Un_insert_right i2nei insertE mapset_none
            prod.inject setSpec upres assms vr)
    next 
      case (Some z) 
      then have mapSome: "mapOf t j = Some z" 
        by simp
      then have "(j,z) \<in> setOf t"
        by (meson mapset_some assms)
      with setSpec i2nei mapset_some vr have "mapOf ?tr j = Some z"
        by (fastforce simp: eqs_def)
      then show ?thesis
        by (simp add: mapSome upres)
    qed
    from lhs_res rhs_res show ?thesis by simp
  qed
qed

lemma mupdate_valid: 
  assumes "valid_tmap t" shows "valid_tmap (mupdate i a t)"
  by (metis binsert_sorted mupdate_def assms valid_tmap_def)

(*============================================================*)
section \<open>Map Remove Operation\<close>
(*============================================================*)

definition mremove :: "index => 'a tarray => 'a tarray" where
  "mremove i t \<equiv> remove fst (i, undefined) t"

lemma mremove_valid: 
  assumes "valid_tmap t"
  shows "valid_tmap (mremove i t)"
  by (metis mremove_def remove_sort assms valid_tmap_def)

lemma mremove_map: 
  assumes "valid_tmap t"
  shows "mapOf (mremove i t) i = None"
  using assms
  by (auto simp: mremove_def eqs_def mapset_none remove_set remove_sort)

end
