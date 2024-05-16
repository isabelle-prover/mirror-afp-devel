(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
theory Lens
  imports Main Distinct_Prop
begin

section \<open>Auxiliary Theorems\<close>

lemma distinct_prop_cons:
  "list_all (R x) xs \<Longrightarrow> distinct_prop R xs \<Longrightarrow> distinct_prop R (x # xs)"
  by (simp add: list_all_iff)

lemma distinct_prop_distrib_all:
  "distinct_prop (\<lambda>x y. \<forall>a. R a x y) xs \<longleftrightarrow> (\<forall>a. distinct_prop (R a) xs)"
  by (induction xs) auto

lemma pairwise_set_of_distinct_prop:
  "(\<And>a b. R a b \<longleftrightarrow> R b a) \<Longrightarrow> distinct_prop R xs \<Longrightarrow> pairwise R (set xs)"
  by (induction xs) (auto simp: pairwise_insert)

lemma distinct_prop_iff_nth:
  "distinct_prop R xs \<longleftrightarrow> (\<forall>i j. i < j \<longrightarrow> j < length xs \<longrightarrow> R (xs!i) (xs!j))"
proof (induction xs)
  have split: "(\<forall>i. P i) \<longleftrightarrow> P 0 \<and> (\<forall>i. P (Suc i))" for P :: "nat \<Rightarrow> bool"
    by (metis not0_implies_Suc)

  case (Cons x xs)
  then have "distinct_prop R (x # xs) \<longleftrightarrow>
    (\<forall>j. j < length xs \<longrightarrow> R x (xs ! j)) \<and>
    (\<forall>i j. i < j \<longrightarrow> j < length xs \<longrightarrow> R (xs ! i) (xs ! j))"
    by (auto simp add: set_conv_nth)
  also have "\<dots> \<longleftrightarrow> (\<forall>i j. i < j \<longrightarrow> j < Suc (length xs) \<longrightarrow> R ((x # xs) ! i) ((x # xs) ! j))"
    apply (subst (4) split)
    apply (subst (4 6) split)
    apply simp
    done
  finally show ?case by simp
qed simp

lemma distinct_prop_mono:
  "(\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> P x y \<Longrightarrow> R x y) \<Longrightarrow>
    distinct_prop P xs \<Longrightarrow> distinct_prop R xs"
  by (induction xs) auto

lemma distinct_prop_nil: "distinct_prop R []"
  by simp

lemma list_all_concat: "list_all p (concat xs) = list_all (list_all p) xs"
  by (induction xs) auto

lemma list_all_conj: "list_all P xs \<Longrightarrow> list_all Q xs \<Longrightarrow> list_all (\<lambda>x. P x \<and> Q x) xs"
  using Ball_set by blast

lemma list_all_zip_iff_list_all2:
  "length as = length bs \<Longrightarrow> list_all R (zip as bs) \<longleftrightarrow> list_all2 (\<lambda>a b. R (a, b)) as bs"
  by (simp add: Ball_set_list_all list_all2_iff)

lemma disjnt_comm: "disjnt A B \<longleftrightarrow> disjnt B A"
  by (metis disjnt_sym)

lemma disjnt_image: "disjnt (f ` x) (f ` y) \<Longrightarrow> disjnt x y"
  by (auto simp: disjnt_def)

lemma disjnt_of_nat:
  "s \<subseteq> {0..<2^LENGTH('a::len)} \<Longrightarrow> t \<subseteq> {0..<2^LENGTH('a)} \<Longrightarrow>
    disjnt ((of_nat :: nat \<Rightarrow> 'a word) ` s) (of_nat ` t) \<longleftrightarrow> disjnt s t"
  proof (rule disjnt_inj_on_iff[of _ "Pow {0..<2^LENGTH('a)}"])
  qed (simp_all add: inj_on_word_of_nat)

lemma list_all_zip_zip_cons:
  "R a b c \<Longrightarrow>
    list_all (\<lambda>(a, b, c). R a b c) (zip as (zip bs cs)) \<Longrightarrow>
    list_all (\<lambda>(a, b, c). R a b c) (zip (a#as) (zip (b#bs) (c#cs)))"
  by simp

lemma list_all_zip_zip_empty:
  "list_all (\<lambda>(a, b, c). R a b c) (zip [] (zip [] []))"
  by simp

lemma list_all_cons: "P x \<Longrightarrow> list_all P xs \<Longrightarrow> list_all P (x # xs)"
  by simp

lemma list_all_nil: "list_all P []"
  by simp

lemma fold_functor:
  "F id = id \<Longrightarrow> (\<And>a b. F (a \<circ> b) = F a \<circ> F b) \<Longrightarrow> F (fold a xs) = fold (\<lambda>x. F (a x)) xs"
  by (induction xs; simp)

section \<open>Legacy definition \<open>fg_cons\<close>\<close>

definition fg_cons :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "fg_cons acc upd \<equiv>
     (\<forall>bs v. acc (upd bs v) = bs) \<and> (\<forall>bs bs' v. upd bs (upd bs' v) = upd bs v) \<and> (\<forall>v. upd (acc v) v = v)"

section \<open>Lense definition using an update function \<open>lense\<close>\<close>

type_synonym 'a upd = "'a \<Rightarrow> 'a"

named_theorems update_compose

locale lense =
  fixes
    get :: "'s \<Rightarrow> 'a" and
    upd :: "'a upd \<Rightarrow> 's upd"
  assumes get_upd    [simp]: "get (upd f s) = f (get s)"
  assumes upd_same         : "f (get s) = get s \<Longrightarrow> upd f s = s"
  assumes upd_compose[update_compose, simp]: "upd f (upd g s) = upd (f o g) s"
begin

lemma upd_comp[simp]: "upd f \<circ> upd g = upd (f \<circ> g)"
  by (simp add: fun_eq_iff)
lemma upd_get [simp]: "upd (\<lambda>_. get s) s = s"
  by (simp add: upd_same)
lemma upd_id [simp]: "upd (\<lambda>x. x) s = s"
  by (simp add: upd_same)
lemma upd_cong: "f (get s) = f' (get s) \<Longrightarrow> upd f s = upd f' s"
  by (metis fun_upd_same get_upd upd_compose upd_same)

lemma upd_comp_fold: "upd (fold f xs) = fold (upd \<circ> f) xs"
  apply (induction xs)
  apply (simp_all add: upd_same del: comp_apply flip: upd_comp)
  apply (simp add: fun_eq_iff comp_def)
  done

lemma fg_cons: "fg_cons get (upd \<circ> (\<lambda>x _. x))"
  unfolding fg_cons_def o_def by (simp add: comp_def)

end

(* this fits better with the way lenses are constructed by the Recursive_Record package *)
lemma lenseI:
  fixes get upd
  assumes 1:"(\<And>s f. get (upd f s) = f (get s))" "(\<And>s. upd (\<lambda>x. get s) s = s)"
    and 2[cong]: "(\<And>s f g. f (get s) = g (get s) \<Longrightarrow> upd g s = upd f s)"
    and 3: "(\<And>s f g. upd f (upd g s) = upd (f o g) s)"
  shows "lense get upd"
  using 1 3
  by (simp add: lense_def)

lemma lenseI_equiv:
  "(\<And>x. f (g x) = x) \<Longrightarrow> (\<And>x. g (f x) = x) \<Longrightarrow> lense g (\<lambda>v x. f (v (g x)))"
  by (simp add: lense_def)

lemma lense_comp:
  assumes lense1: "lense sel1 upd1"
  assumes lense2: "lense sel2 upd2"
  shows "lense (sel2 o sel1) (upd1 o upd2)"
proof -
  interpret lense1: lense sel1 upd1 by (rule lense1)
  interpret lense2: lense sel2 upd2 by (rule lense2)
  show ?thesis
    apply (unfold_locales)
    subgoal by (simp add: comp_def)
    subgoal using lense1.upd_same lense2.upd_same by simp
    subgoal using lense1.upd_compose lense2.upd_compose by (simp add: comp_def)
    done
qed

lemma lense_compose:
  assumes "lense sel1 upd1" "lense sel2 upd2"
  shows "lense (\<lambda>x. sel2 (sel1 x)) (\<lambda>f. upd1 (upd2 f))"
  using lense_comp[OF assms] by (simp add: comp_def)

lemma lense_of_fg_cons:
  "fg_cons g s \<Longrightarrow> lense g (\<lambda>f x. s (f (g x)) x)"
  by (simp add: fg_cons_def lense_def)

lemma lense_of_fg_cons':
  "fg_cons g (u \<circ> (\<lambda>x _. x)) \<Longrightarrow>
    (\<And>f x. u f x = u (\<lambda>_. f (g x)) x) \<Longrightarrow>
    lense g u"
  by (simp_all add: fg_cons_def fun_eq_iff comp_def lense_def) metis

section \<open>Update for functions\<close>

definition upd_fun :: "'a \<Rightarrow> 'b upd \<Rightarrow> ('a \<Rightarrow> 'b) upd" where
  "upd_fun i f g = g(i := f (g i))"

global_interpretation upd_fun: lense "\<lambda>f. f a" "upd_fun a"
  by (simp add: lense_def upd_fun_def)

lemma upd_fun_ne: "i \<noteq> j \<Longrightarrow> upd_fun i f g j = g j"
  by (simp add: upd_fun_def fun_upd_def)

lemma upd_fun_commute: "i \<noteq> j \<Longrightarrow> upd_fun i f \<circ> upd_fun j g = upd_fun j g \<circ> upd_fun i f"
  by (auto simp: upd_fun_def fun_eq_iff fun_upd_def)

section \<open>Scenes\<close>

text \<open>Scenes allow us to represent a projection/lense without referring to a second type. \<close>

type_synonym 'a scene = "'a \<Rightarrow> 'a \<Rightarrow> 'a"

locale is_scene =
  fixes s :: "'a scene"
  assumes left[simp]: "s (s a b) c = s a c"
  assumes right[simp]: "s a (s b c) = s a c"
  assumes idem[simp]: "s a a = a"

lemma is_scene_all[simp]: "is_scene (\<lambda>a b. a)"
  by (simp add: is_scene_def)

lemma is_scene_id[simp]: "is_scene (\<lambda>a. id)"
  by (simp add: is_scene_def)

lemma is_scene_flip: "is_scene m \<Longrightarrow> is_scene (\<lambda>a b. m b a)"
  by (simp add: is_scene_def)

lemma is_scene_of_lense: "lense r w \<Longrightarrow> is_scene (\<lambda>a. w (\<lambda>_. r a))"
  by (simp add: lense_def is_scene_def K_record_comp)

lemma is_scene_of_fg_cons: "fg_cons r w \<Longrightarrow> is_scene (\<lambda>a. w (r a))"
  by (simp add: fg_cons_def is_scene_def)

lemma scene_comp_idem: "is_scene m \<Longrightarrow> m a \<circ> m a = m a"
  by (simp add: fun_eq_iff is_scene.right)

definition comm_scene :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> bool" where
  "comm_scene m1 m2 \<longleftrightarrow> (\<forall>a b. m1 a (m2 a b) = m2 a (m1 a b))"

lemma comm_scene_comm: "comm_scene m1 m2 \<longleftrightarrow> comm_scene m2 m1"
  by (simp add: comm_scene_def) metis

lemma comm_scene_sym[intro]: "comm_scene m1 m2 \<Longrightarrow> comm_scene m2 m1"
  by (simp add: comm_scene_comm)

lemma comm_sceneD: "comm_scene m1 m2 \<Longrightarrow> m1 a (m2 a c) = m2 a (m1 a c)"
  by (simp add: comm_scene_def)

lemma comm_scene_all_left[simp]: "is_scene m \<Longrightarrow> comm_scene (\<lambda>a b. a) m"
  by (simp add: comm_scene_def is_scene.idem)

lemma comm_scene_all_right[simp]: "is_scene m \<Longrightarrow> comm_scene m (\<lambda>a b. a)"
  by (simp add: comm_scene_def is_scene.idem)

lemma comm_scene_id_left[simp]: "comm_scene (\<lambda>a. id) m"
  by (simp add: comm_scene_def)

lemma comm_scene_id_right[simp]: "comm_scene m (\<lambda>a. id)"
  by (simp add: comm_scene_def)

lemma comm_scene_refl[intro, simp]: "comm_scene m m"
  by (simp add: comm_scene_def)

lemma is_scene_comp:
  "is_scene m1 \<Longrightarrow> is_scene m2 \<Longrightarrow> comm_scene m1 m2 \<Longrightarrow> is_scene (\<lambda>a. m1 a \<circ> m2 a)"
  by (simp add: is_scene_def comm_scene_def) metis

lemma comm_scene_comp_left:
  "comm_scene m1 m2 \<Longrightarrow> comm_scene m1 m \<Longrightarrow> comm_scene m2 m \<Longrightarrow> comm_scene (\<lambda>a. m1 a \<circ> m2 a) m"
  by (simp add: is_scene_def comm_scene_def)

lemma comm_scene_comp_right:
  "comm_scene m m1 \<Longrightarrow> comm_scene m m2 \<Longrightarrow> comm_scene m1 m2 \<Longrightarrow> comm_scene m (\<lambda>a. m1 a \<circ> m2 a)"
  using comm_scene_comp_left[of m1 m2 m] by (simp add: comm_scene_comm)

lemma comm_scene_fold:
  "pairwise comm_scene (insert m (set ms)) \<Longrightarrow> comm_scene (\<lambda>a. fold (\<lambda>m. m a) ms) m"
  by (induction ms arbitrary: m) (auto intro!: comm_scene_comp_left simp: pairwise_def)

lemma is_scene_fold:
  "list_all is_scene ms \<Longrightarrow> pairwise comm_scene (set ms) \<Longrightarrow> is_scene (\<lambda>a. fold (\<lambda>m. m a) ms)"
  by (induction ms) (simp_all add: is_scene_comp comm_scene_fold pairwise_def)

lemma is_scene_fold':
  "list_all (\<lambda>x. is_scene (m x)) ms \<Longrightarrow> pairwise comm_scene (m ` set ms) \<Longrightarrow>
    is_scene (\<lambda>a. fold (\<lambda>x. m x a) ms)"
  using is_scene_fold[of "map m ms"] by (simp add: list.pred_map comp_def fold_map)

text \<open> This expresses "disjointness" on scenes, saying that two scenes occupy disjnt parts of the
type.

It is stronger than "commutativity" \<open>\<forall>a c. m1 a (m2 a b) = m2 a (m1 a b)\<close> which is enough
to show composition, but in our cases we are interested in disjointness. Important difference:
  a scene \<open>m\<close> "commutes" with itself, but only \<open>\<lambda>a. id\<close> is disjoint with itself. \<close>
definition disjnt_scene :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> bool" where
  "disjnt_scene m1 m2 \<longleftrightarrow> (\<forall>a b c. m1 a (m2 b c) = m2 b (m1 a c))"

lemma comm_scene_of_disjnt_scene[intro, simp]: "disjnt_scene m1 m2 \<Longrightarrow> comm_scene m1 m2"
  by (simp add: disjnt_scene_def comm_scene_def)

lemma disjnt_scene_comm: "disjnt_scene m1 m2 \<longleftrightarrow> disjnt_scene m2 m1"
  by (simp add: disjnt_scene_def) metis

lemma disjnt_scene_sym[intro]: "disjnt_scene m1 m2 \<Longrightarrow> disjnt_scene m2 m1"
  by (simp add: disjnt_scene_comm)

lemma disjnt_sceneD: "disjnt_scene m1 m2 \<Longrightarrow> m1 a (m2 b c) = m2 b (m1 a c)"
  by (simp add: disjnt_scene_def)

lemma disjnt_sceneD_left: "is_scene m1 \<Longrightarrow> disjnt_scene m1 m2 \<Longrightarrow> m1 (m2 a b) c = m1 b c"
  by (simp add: disjnt_scene_def is_scene_def) metis

lemma disjnt_sceneD_right: "is_scene m2 \<Longrightarrow> disjnt_scene m1 m2 \<Longrightarrow> m2 (m1 a b) c = m2 b c"
  using disjnt_sceneD_left[of m2 m1, OF _ disjnt_scene_sym] .

lemma disjnt_scene_all_left[simp]: "disjnt_scene (\<lambda>a b. a) m \<longleftrightarrow> m = (\<lambda>a. id)"
  by (auto simp add: disjnt_scene_def fun_eq_iff)

lemma disjnt_scene_all_right[simp]: "disjnt_scene m (\<lambda>a b. a) \<longleftrightarrow> m = (\<lambda>a. id)"
  by (auto simp add: disjnt_scene_def fun_eq_iff)

lemma disjnt_scene_id_left[simp]: "disjnt_scene (\<lambda>a. id) m"
  by (simp add: disjnt_scene_def)

lemma disjnt_scene_id_right[simp]: "disjnt_scene m (\<lambda>a. id)"
  by (simp add: disjnt_scene_def)

lemma disjnt_scene_comp_left:
  "comm_scene m1 m2 \<Longrightarrow> disjnt_scene m1 m \<Longrightarrow> disjnt_scene m2 m \<Longrightarrow>
    disjnt_scene (\<lambda>a. m1 a \<circ> m2 a) m"
  by (simp add: is_scene_def disjnt_scene_def)

lemma disjnt_scene_comp_right:
  "disjnt_scene m m1 \<Longrightarrow> disjnt_scene m m2 \<Longrightarrow> comm_scene m1 m2 \<Longrightarrow>
    disjnt_scene m (\<lambda>a. m1 a \<circ> m2 a)"
  using disjnt_scene_comp_left[of m1 m2 m] by (simp add: disjnt_scene_comm)

lemma disjnt_scene_fold:
  "list_all (disjnt_scene m) ms \<Longrightarrow> pairwise comm_scene (set ms) \<Longrightarrow>
    disjnt_scene (\<lambda>a. fold (\<lambda>m. m a) ms) m"
  by (induction ms arbitrary: m)
     (auto simp: pairwise_def intro!: disjnt_scene_comp_left comm_scene_fold)

lemma fold_disjnt_scene:
  "list_all is_scene ms \<Longrightarrow> pairwise comm_scene (set ms) \<Longrightarrow>
    list_all (\<lambda>m. disjnt_scene m m' \<or> m = m') ms \<Longrightarrow> m' \<in> set ms \<Longrightarrow>
    fold (\<lambda>m. m (m' a b)) ms c = m' a (fold (\<lambda>m. m b) ms c)"
proof (induction ms rule: rev_induct)
  case (snoc m ms)
  show ?case
  proof cases
    assume "m' \<in> set ms"
    with snoc have eq[simp]: "fold (\<lambda>m. m (m' a b)) ms c = m' a (fold (\<lambda>m. m b) ms c)"
      and m_m': "disjnt_scene m m' \<or> m = m'"
      and m: "is_scene m" and m': "is_scene m'"
      by (auto simp: list_all_iff pairwise_def)

    show ?thesis
      using m_m' m m'
      by (auto simp: disjnt_sceneD_left disjnt_sceneD
                     is_scene.right[OF m'] is_scene.left[OF m'])
  next
    assume "m' \<notin> set ms"
    with snoc.prems have m'_ms: "list_all (disjnt_scene m') ms"
      and [simp]: "list_all is_scene ms" "pairwise comm_scene (set ms)"
      and [simp]: "m = m'" and m': "is_scene m'"
      by (auto simp: list_all_iff pairwise_def)

    have [simp]: "fold (\<lambda>m. m (m' a b)) ms c = fold (\<lambda>m. m b) ms c"
      by (rule disjnt_sceneD_left[OF is_scene_fold disjnt_scene_fold[OF m'_ms]]; simp)

    show ?thesis
      by (simp add: is_scene.right[OF m'] is_scene.left[OF m'])
  qed
qed simp

end