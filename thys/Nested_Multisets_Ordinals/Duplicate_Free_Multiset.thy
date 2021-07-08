(*
  File:                      Duplicate_Free_Multiset.thy
  Authors and contributors:  Mathias Fleury, Daniela Kaufmann, JKU;
                             Jose Divasón, Sebastiaan Joosten, René Thiemann, Akihisa Yamada
*)

theory Duplicate_Free_Multiset
imports Multiset_More
begin

section \<open>Duplicate Free Multisets\<close>

text \<open>Duplicate free multisets are isomorphic to finite sets, but it can be useful to reason about
  duplication to speak about intermediate execution steps in the refinements.
\<close>

definition distinct_mset :: "'a multiset \<Rightarrow> bool" where
  "distinct_mset S \<longleftrightarrow> (\<forall>a. a \<in># S \<longrightarrow> count S a = 1)"

lemma distinct_mset_count_less_1: "distinct_mset S \<longleftrightarrow> (\<forall>a. count S a \<le> 1)"
  using eq_iff nat_le_linear unfolding distinct_mset_def by fastforce

lemma distinct_mset_empty[simp]: "distinct_mset {#}"
  unfolding distinct_mset_def by auto

lemma distinct_mset_singleton: "distinct_mset {#a#}"
  unfolding distinct_mset_def by auto

lemma distinct_mset_union:
  assumes dist: "distinct_mset (A + B)"
  shows "distinct_mset A"
  unfolding distinct_mset_count_less_1
proof (rule allI)
  fix a
  have \<open>count A a \<le> count (A + B) a\<close> by auto
  moreover have \<open>count (A + B) a \<le> 1\<close>
    using dist unfolding distinct_mset_count_less_1 by auto
  ultimately show \<open>count A a \<le> 1\<close>
    by simp
qed

lemma distinct_mset_minus[simp]: "distinct_mset A \<Longrightarrow> distinct_mset (A - B)"
  by (metis diff_subset_eq_self mset_subset_eq_exists_conv distinct_mset_union)

lemma distinct_mset_rempdups_union_mset:
  assumes "distinct_mset A" and "distinct_mset B"
  shows "A \<union># B = remdups_mset (A + B)"
  using assms nat_le_linear unfolding remdups_mset_def
  by (force simp add: multiset_eq_iff max_def count_mset_set_if distinct_mset_def not_in_iff)

lemma distinct_mset_add_mset[simp]: "distinct_mset (add_mset a L) \<longleftrightarrow> a \<notin># L \<and> distinct_mset L"
  unfolding distinct_mset_def
  apply (rule iffI)
   apply (auto split: if_split_asm; fail)[]
  by (auto simp: not_in_iff; fail)

lemma distinct_mset_size_eq_card: "distinct_mset C \<Longrightarrow> size C = card (set_mset C)"
  by (induction C) auto

lemma distinct_mset_add:
  "distinct_mset (L + L') \<longleftrightarrow> distinct_mset L \<and> distinct_mset L' \<and> L \<inter># L' = {#}"
  by (induction L arbitrary: L') auto

lemma distinct_mset_set_mset_ident[simp]: "distinct_mset M \<Longrightarrow> mset_set (set_mset M) = M"
  by (induction M) auto

lemma distinct_finite_set_mset_subseteq_iff[iff]:
  assumes "distinct_mset M" "finite N"
  shows "set_mset M \<subseteq> N \<longleftrightarrow> M \<subseteq># mset_set N"
  by (metis assms distinct_mset_set_mset_ident finite_set_mset msubset_mset_set_iff)

lemma distinct_mem_diff_mset:
  assumes dist: "distinct_mset M" and mem: "x \<in> set_mset (M - N)"
  shows "x \<notin> set_mset N"
proof -
  have "count M x = 1"
    using dist mem by (meson distinct_mset_def in_diffD)
  then show ?thesis
    using mem by (metis count_greater_eq_one_iff in_diff_count not_less)
qed

lemma distinct_set_mset_eq:
  assumes "distinct_mset M" "distinct_mset N" "set_mset M = set_mset N"
  shows "M = N"
  using assms distinct_mset_set_mset_ident by fastforce

lemma distinct_mset_union_mset[simp]:
  \<open>distinct_mset (D \<union># C) \<longleftrightarrow> distinct_mset D \<and> distinct_mset C\<close>
  unfolding distinct_mset_count_less_1 by force

lemma distinct_mset_inter_mset:
  "distinct_mset C \<Longrightarrow> distinct_mset (C \<inter># D)"
  "distinct_mset D \<Longrightarrow> distinct_mset (C \<inter># D)"
  by (auto simp add: distinct_mset_def min_def count_eq_zero_iff elim!: le_SucE)

lemma distinct_mset_remove1_All: "distinct_mset C \<Longrightarrow> remove1_mset L C = removeAll_mset L C"
  by (auto simp: multiset_eq_iff distinct_mset_count_less_1)

lemma distinct_mset_size_2: "distinct_mset {#a, b#} \<longleftrightarrow> a \<noteq> b"
  by auto

lemma distinct_mset_filter: "distinct_mset M \<Longrightarrow> distinct_mset {# L \<in># M. P L#}"
  by (simp add: distinct_mset_def)

lemma distinct_mset_mset_distinct[simp]: \<open>distinct_mset (mset xs) = distinct xs\<close>
  by (induction xs) auto

lemma distinct_image_mset_inj:
  \<open>inj_on f (set_mset M) \<Longrightarrow> distinct_mset (image_mset f M) \<longleftrightarrow> distinct_mset M\<close>
  by (induction M) (auto simp: inj_on_def)

lemma distinct_mset_remdups_mset_id: \<open>distinct_mset C \<Longrightarrow> remdups_mset C = C\<close>
  by (induction C)  auto

lemma distinct_mset_image_mset:
  \<open>distinct_mset (image_mset f (mset xs)) \<longleftrightarrow> distinct (map f xs)\<close>
  apply (subst mset_map[symmetric])
  apply (subst distinct_mset_mset_distinct)
  ..

lemma distinct_mset_mono: \<open>D' \<subseteq># D \<Longrightarrow> distinct_mset D \<Longrightarrow> distinct_mset D'\<close>
  by (metis distinct_mset_union subset_mset.le_iff_add)

lemma distinct_mset_mono_strict: \<open>D' \<subset># D \<Longrightarrow> distinct_mset D \<Longrightarrow> distinct_mset D'\<close>
  using distinct_mset_mono by auto

lemma distinct_set_mset_eq_iff:
  assumes \<open>distinct_mset M\<close> \<open>distinct_mset N\<close>
  shows \<open>set_mset M = set_mset N \<longleftrightarrow> M = N\<close>
  using assms distinct_mset_set_mset_ident by fastforce

lemma distinct_mset_union2:
  \<open>distinct_mset (A + B) \<Longrightarrow> distinct_mset B\<close>
  using distinct_mset_union[of B A]
  by (auto simp: ac_simps)

lemma distinct_mset_mset_set: \<open>distinct_mset (mset_set A)\<close>
  unfolding distinct_mset_def count_mset_set_if by (auto simp: not_in_iff)

lemma distinct_mset_inter_remdups_mset:
  assumes dist: \<open>distinct_mset A\<close>
  shows \<open>A \<inter># remdups_mset B = A \<inter># B\<close>
proof -
  have [simp]: \<open>A' \<inter># remove1_mset a (remdups_mset Aa) = A' \<inter># Aa\<close>
    if
      \<open>A' \<inter># remdups_mset Aa = A' \<inter># Aa\<close> and
      \<open>a \<notin># A'\<close> and
      \<open>a \<in># Aa\<close>
    for A' Aa :: \<open>'a multiset\<close> and a
  by (metis insert_DiffM inter_add_right1 set_mset_remdups_mset that)

  show ?thesis
    using dist
    apply (induction A)
    subgoal by auto
     subgoal for a A'
       by (cases \<open>a \<in># B\<close>)
         (use multi_member_split[of a \<open>B\<close>]  multi_member_split[of a \<open>A\<close>] in
           \<open>auto simp: mset_set.insert_remove\<close>)
    done
qed

abbreviation (input) is_mset_set :: \<open>'a multiset \<Rightarrow> bool\<close>
  where \<open>is_mset_set \<equiv> distinct_mset\<close>

lemma is_mset_set_def:
  \<open>is_mset_set X \<longleftrightarrow> (\<forall>x \<in># X. count X x = 1)\<close>
  by (auto simp add: distinct_mset_def)

lemma is_mset_setD[dest]: "is_mset_set X \<Longrightarrow> x \<in># X \<Longrightarrow> count X x = 1"
  unfolding is_mset_set_def by auto

lemma is_mset_setI[intro]:
  assumes "\<And>x. x \<in># X \<Longrightarrow> count X x = 1"
  shows "is_mset_set X"
  using assms unfolding is_mset_set_def by auto

lemma is_mset_set[simp]: "is_mset_set (mset_set X)"
  by (fact distinct_mset_mset_set)

lemma is_mset_set_add[simp]:
  "is_mset_set (X + {#x#}) \<longleftrightarrow> is_mset_set X \<and> x \<notin># X" (is "?L \<longleftrightarrow> ?R")
proof(intro iffI conjI)
  assume L: ?L
  with count_eq_zero_iff count_single show "is_mset_set X"
    unfolding is_mset_set_def
    by (metis (no_types, opaque_lifting) add_mset_add_single count_add_mset nat.inject set_mset_add_mset_insert union_single_eq_member)
  show "x \<notin># X"
  proof
    assume "x \<in># X"
    then have "count (X + {#x#}) x > 1" by auto
    with L show False by (auto simp: is_mset_set_def)
  qed
next
  assume R: ?R show ?L
  proof
    fix x' assume x': "x' \<in># X + {#x#}"
    show "count (X + {#x#}) x' = 1"
    proof(cases "x' \<in># X")
      case True with R have "count X x' = 1" by auto
        moreover from True R have "count {#x#} x' = 0" by auto
        ultimately show ?thesis by auto
    next
      case False then have "count X x' = 0" by (simp add: not_in_iff)
        with R x' show ?thesis by auto
    qed
  qed
qed

lemma mset_set_id:
  assumes "is_mset_set X"
  shows "mset_set (set_mset X) = X"
  using assms by (fact distinct_mset_set_mset_ident)

lemma is_mset_set_image:
  assumes "inj_on f (set_mset X)" and "is_mset_set X"
  shows "is_mset_set (image_mset f X)"
proof (cases X)
  case empty then show ?thesis by auto
next
  case (add x X)
    define X' where "X' \<equiv> add_mset x X"
    with assms add have inj:"inj_on f (set_mset X')"
          and X': "is_mset_set X'" by auto
  show ?thesis
  proof(unfold add, intro is_mset_setI, fold X'_def)
    fix y assume "y \<in># image_mset f X'"
    then have "y \<in> f ` set_mset X'" by auto 
    with inj have "\<exists>!x'. x' \<in># X' \<and> y = f x'" by (meson imageE inj_onD)
    then obtain x' where x': "{x'. x' \<in># X' \<and> y = f x'} = {x'}" by auto
    then have "count (image_mset f X') y = count X' x'"
      by (simp add: count_image_mset')
    also from X' x' have "... = 1" by auto
    finally show "count (image_mset f X') y = 1".
  qed
qed

end
