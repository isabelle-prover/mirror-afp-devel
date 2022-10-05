(* Author: Bernhard Stöckl *)

theory JoinTree
  imports Complex_Main "HOL-Library.Multiset" "Selectivities"
begin

section \<open>Join Tree\<close>

text\<open>
  Relations have an identifier and cardinalities. Joins have two children and a result cardinality.
  The datatype only represents the structure while cardinalities are given by a separate function.
\<close>
datatype (relations:'a) joinTree = Relation 'a | Join "'a joinTree" "'a joinTree"

type_synonym 'a card = "'a \<Rightarrow> real"

subsection \<open>Functions\<close>

subsubsection \<open>Functions for Information Retrieval\<close>

fun inorder :: "'a joinTree \<Rightarrow> 'a list" where
  "inorder (Relation rel) = [rel]"
| "inorder (Join l r) = inorder l @ inorder r"

fun revorder :: "'a joinTree \<Rightarrow> 'a list" where
  "revorder (Relation rel) = [rel]"
| "revorder (Join l r) = revorder r @ revorder l"

fun relations_mset :: "'a joinTree \<Rightarrow> 'a multiset" where
  "relations_mset (Relation rel) = {#rel#}"
| "relations_mset (Join l r) = relations_mset l + relations_mset r"

fun card :: "'a card \<Rightarrow> 'a selectivity \<Rightarrow> 'a joinTree \<Rightarrow> real" where
  "card cf f (Relation rel) = cf rel"
| "card cf f (Join l r) =
    list_sel f (inorder l) (inorder r) * card cf f l * card cf f r"

fun cards_list :: "'a card \<Rightarrow> 'a joinTree \<Rightarrow> ('a\<times>real) list" where
  "cards_list cf (Relation rel) = [(rel,cf rel)]"
| "cards_list cf (Join l r) = cards_list cf l @ cards_list cf r"

fun height :: "'a joinTree \<Rightarrow> nat" where
  "height (Relation _) = 0"
| "height (Join l r) = max (height l) (height r) + 1"

fun num_relations :: "'a joinTree \<Rightarrow> nat" where
  "num_relations (Relation _) = 1"
| "num_relations (Join l r) = num_relations l + num_relations r"

fun first_node :: "'a joinTree \<Rightarrow> 'a" where
  "first_node (Relation r) = r"
| "first_node (Join l _) = first_node l"


subsubsection \<open>Functions for Correctness Checks\<close>

text \<open>
  Cardinalities must be positive and selectivities need to be @{text "\<in> (0,1]"}.
\<close>
fun reasonable_cards :: "'a card \<Rightarrow> 'a selectivity \<Rightarrow> 'a joinTree \<Rightarrow> bool" where
  "reasonable_cards cf f (Relation rel) = (cf rel > 0)"
| "reasonable_cards cf f (Join l r) = (let c = card cf f (Join l r) in
    c \<le> card cf f l * card cf f r \<and> c > 0 \<and> reasonable_cards cf f l \<and> reasonable_cards cf f r)"

definition pos_rel_cards :: "'a card \<Rightarrow> 'a joinTree \<Rightarrow> bool" where
  "pos_rel_cards cf t = (\<forall>(_,c)\<in>set (cards_list cf t). c > 0)"

definition pos_list_cards :: "'a card \<Rightarrow> 'a list \<Rightarrow> bool" where
  "pos_list_cards cf xs = (\<forall>x\<in>set xs. cf x > 0)"

text\<open>
  Each node should have a unique identifier.
\<close>
definition distinct_relations :: "'a joinTree \<Rightarrow> bool" where
  "distinct_relations t = distinct (inorder t)"

subsubsection \<open>Functions for Modifications\<close>

fun mirror :: "'a joinTree \<Rightarrow> 'a joinTree" where
  "mirror (Relation rel) = Relation rel"
| "mirror (Join l r) = Join (mirror r) (mirror l)"

fun create_rdeep :: "'a list \<Rightarrow> 'a joinTree" where
  "create_rdeep [] = undefined"
| "create_rdeep [x] = Relation x"
| "create_rdeep (x#xs) = Join (Relation x) (create_rdeep xs)"

fun create_ldeep_rev :: "'a list \<Rightarrow> 'a joinTree" where
  "create_ldeep_rev [] = undefined"
| "create_ldeep_rev [x] = Relation x"
| "create_ldeep_rev (x#xs) = Join (create_ldeep_rev xs) (Relation x)"

definition create_ldeep :: "'a list \<Rightarrow> 'a joinTree" where
  "create_ldeep xs = create_ldeep_rev (rev xs)"

subsubsection \<open>Additional properties\<close>
(** functions that check for certain properties **)

fun left_deep :: "'a joinTree \<Rightarrow> bool" where
  "left_deep (Relation _) = True"
| "left_deep (Join l (Relation _)) = left_deep l"
| "left_deep _ = False"

fun right_deep :: "'a joinTree \<Rightarrow> bool" where
  "right_deep (Relation _) = True"
| "right_deep (Join (Relation _) r) = right_deep r"
| "right_deep _ = False"

fun zig_zag :: "'a joinTree \<Rightarrow> bool" where
  "zig_zag (Relation _) = True"
| "zig_zag (Join l (Relation _)) = zig_zag l"
| "zig_zag (Join (Relation _) r) = zig_zag r"
| "zig_zag _ = False"

subsubsection \<open>Cardinality Calculations for Left-deep Trees\<close>

text \<open>
  Expects a reversed list of relations rs and calculates the cardinality of a left-deep tree.
\<close>

fun ldeep_n :: "'a selectivity \<Rightarrow> 'a card \<Rightarrow> 'a list \<Rightarrow> real" where
  "ldeep_n f cf [] = 1"
| "ldeep_n f cf (r#rs) = cf r * (list_sel_aux' f rs r) * ldeep_n f cf rs"

definition ldeep_T :: "('a \<Rightarrow> real) \<Rightarrow> 'a card \<Rightarrow> 'a list \<Rightarrow> real" where
  "ldeep_T sf cf xs = foldl (\<lambda>a b. a * cf b * sf b) 1 xs"

fun ldeep_T' :: "('a \<Rightarrow> real) \<Rightarrow> 'a card \<Rightarrow> 'a list \<Rightarrow> real" where
  "ldeep_T' f cf [] = 1"
| "ldeep_T' f cf (r#rs) = cf r * f r * ldeep_T' f cf rs"


subsection \<open>Proofs\<close>
(** proofs that properties are maintained **)

lemma ldeep_eq_rdeep: "left_deep t = right_deep (mirror t)"
  by(induction t rule: left_deep.induct) (auto)

lemma mirror_twice_id[simp]: "mirror (mirror t) = t"
  by(induction t) auto

lemma rdeep_eq_ldeep: "right_deep t = left_deep (mirror t)"
  apply(induction t rule: right_deep.induct)
  by(auto)

lemma mirror_zig_zag_preserv: "zig_zag (mirror t) = zig_zag t"
  apply(induction t rule: zig_zag.induct)
  using zig_zag.elims(2) by fastforce+

lemma ldeep_zig_zag: "left_deep t \<Longrightarrow> zig_zag t"
  by(induction t rule: zig_zag.induct) auto

lemma rdeep_zig_zag: "right_deep t \<Longrightarrow> zig_zag t"
  using rdeep_eq_ldeep ldeep_zig_zag mirror_zig_zag_preserv by blast

lemma relations_nempty: "relations t \<noteq> {}"
  by (induction t) auto

lemma set_implies_mset: "x \<in> relations t \<Longrightarrow> x \<in># relations_mset t"
  by(induction t) (auto)

lemma mset_implies_set: "x \<in># relations_mset t \<Longrightarrow> x \<in> relations t"
  by(induction t) (auto)

lemma inorder_eq_mset: "mset (inorder t) = relations_mset t"
  by(induction t) (auto)

lemma relations_set_eq_mset: "set_mset (relations_mset t) = relations t"
  using mset_implies_set set_implies_mset by fast

lemma inorder_eq_set: "set (inorder t) = relations t"
  by(induction t) (auto)

lemma revorder_eq_mset: "mset (revorder t) = relations_mset t"
  by(induction t) (auto)

lemma revorder_eq_set: "set (revorder t) = relations t"
  by(induction t) (auto)

lemma revorder_eq_rev_inorder: "revorder t = rev (inorder t)"
  by(induction t) (auto)

lemma inorder_eq_rev_revorder: "inorder t = rev (revorder t)"
  by(induction t) (auto)

lemma mirror_mset_eq[simp]: "relations_mset (mirror t) = relations_mset t"
  by(induction t) auto

lemma distinct_rels_alt: "distinct_relations t \<longleftrightarrow> distinct (revorder t)"
  unfolding distinct_relations_def inorder_eq_rev_revorder by simp

lemma distinct_rels_alt':
  "distinct_relations t \<longleftrightarrow> (let multi=relations_mset t in \<forall>x\<in># multi. count multi x = 1)"
  using distinct_relations_def inorder_eq_mset distinct_alt by metis

lemma inorder_nempty: "inorder t \<noteq> []"
  by (induction t) auto

lemma revorder_nempty: "revorder t \<noteq> []"
  by (induction t) auto

lemma mirror_distinct: "distinct_relations t \<Longrightarrow> distinct_relations (mirror t)"
  by(simp add: distinct_rels_alt')

lemma mirror_set_eq[simp]: "relations (mirror t) = relations t"
  by(induction t) auto

lemma mirror_inorder_rev: "inorder (mirror t) = rev (inorder t)"
  by(induction t) auto

lemma mirror_revorder_rev: "revorder (mirror t) = rev (revorder t)"
  by(induction t) auto

corollary mirror_revorder_inorder: "revorder (mirror t) = inorder t"
  unfolding mirror_revorder_rev inorder_eq_rev_revorder by simp

corollary mirror_inorder_revorder: "inorder (mirror t) = revorder t"
  unfolding mirror_inorder_rev revorder_eq_rev_inorder by simp

lemma mirror_card_eq[simp]: "sel_symm f \<Longrightarrow> card cf f (mirror t) = card cf f t"
proof(induction t)
  case (Join l r)
  let ?r = "mirror r" and ?l = "mirror l"
  have 0: "mset (inorder ?r) = mset (inorder r)" by (simp add: inorder_eq_mset)
  have 1: "mset (inorder ?l) = mset (inorder l)" by (simp add: inorder_eq_mset)
  have "card cf f (mirror (Join l r)) = card cf f (Join (mirror r) (mirror l))" by simp
  also have "\<dots> = list_sel f (inorder ?r) (inorder ?l) * card cf f r * card cf f l"
    using Join by simp
  also have "\<dots> = list_sel f (inorder r) (inorder ?l) * card cf f r * card cf f l"
    using 0 mset_x_eq_list_sel_eq by auto
  also have "\<dots> = list_sel f (inorder r) (inorder l) * card cf f r * card cf f l"
    using 1 mset_y_eq_list_sel_eq by auto
  finally show ?case using list_sel_symm Join.prems by auto
qed(simp)

lemma mirror_reasonable_cards:
  "\<lbrakk>sel_symm f; reasonable_cards cf f t\<rbrakk> \<Longrightarrow> reasonable_cards cf f (mirror t)"
proof(induction t)
  case (Join l r)
  let ?r = "mirror r" and ?l = "mirror l"
  let ?c = "card cf f (mirror (Join l r))"
  let ?c' = "card cf f (Join l r)"
  have "reasonable_cards cf f (mirror (Join l r))
      = reasonable_cards cf f (Join (mirror r) (mirror l))" by simp
  also have "\<dots> = (?c \<le> card cf f ?r * card cf f ?l \<and> ?c>0
             \<and> reasonable_cards cf f ?l \<and> reasonable_cards cf f ?r)"
    by (auto simp: Let_def)
  also have "\<dots> = (?c \<le> card cf f ?r * card cf f ?l \<and> ?c>0)"
    using Join by fastforce
  also have "\<dots> = (?c' \<le> card cf f r * card cf f l \<and> ?c'>0)"
    using mirror_card_eq Join.prems by metis
  also have "\<dots> = (?c' \<le> card cf f r * card cf f l \<and> ?c'>0
            \<and> reasonable_cards cf f l \<and> reasonable_cards cf f r)"
    using Join.prems by auto
  also have "\<dots> = (?c' \<le> card cf f l * card cf f r \<and> ?c'>0
            \<and> reasonable_cards cf f l \<and> reasonable_cards cf f r)"
    by argo
  finally show ?case using Join.prems by force
qed(simp)

lemma joinTree_cases: "(\<exists>r. t=(Relation r)) \<or> (\<exists>l rr. t=(Join l (Relation rr)))
    \<or> (\<exists>l lr rr. t=(Join l (Join lr rr)))"
  apply(cases t)
   apply(auto)[2]
  by (meson joinTree.exhaust)

lemma joinTree_cases_ldeep: "left_deep t
    \<Longrightarrow> (\<exists>r. t=(Relation r)) \<or> (\<exists>l rr. t=(Join l (Relation rr)))"
  apply(cases t)
   apply(auto)[2]
  using joinTree_cases by fastforce

lemma ldeep_trans: "left_deep (Join l r) \<Longrightarrow> left_deep l"
  by(cases r) auto

lemma subtree_elem_count_l:
  assumes "\<forall>x\<in># (relations_mset (Join l r)). count (relations_mset (Join l r)) x = 1"
      and "x \<in># relations_mset l"
    shows "count (relations_mset l) x = 1"
proof -
  have 0: "count (relations_mset l) x \<ge> 1" using assms by auto
  have "count (relations_mset l) x \<le> 1" using assms by force
  then show ?thesis using 0 by linarith
qed

lemma subtree_elem_count_r:
  assumes "\<forall>x\<in># (relations_mset (Join l r)). count (relations_mset (Join l r)) x = 1"
      and "x \<in># relations_mset r"
    shows "count (relations_mset r) x = 1"
proof -
  have 0: "count (relations_mset r) x \<ge> 1" using assms by auto
  have "count (relations_mset r) x \<le> 1" using assms by force
  then show ?thesis using 0 by linarith
qed

lemma first_node_first_inorder: "\<exists>xs. inorder t = first_node t # xs"
  by(induction t) auto

lemma first_node_last_revorder: "\<exists>xs. revorder t = xs @ [first_node t]"
  by(induction t) auto

lemma first_node_eq_hd: "first_node t = hd (inorder t)"
  using first_node_first_inorder[of t] by auto

lemma distinct_elem_right_not_left:
  assumes "distinct_relations (Join l r)"
      and "x \<in> relations r"
    shows "x \<notin> relations l"
proof
  assume "x \<in> relations l"
  then have "x \<in># relations_mset l" using set_implies_mset by fast
  then have 0: "count (relations_mset l) x \<ge> 1" by simp
  have "x \<in># relations_mset r" using set_implies_mset assms(2) by fast
  then have "count (relations_mset r) x \<ge> 1" by simp
  moreover have "count (relations_mset l + relations_mset r) x
      = count (relations_mset l) x + count (relations_mset r) x" by simp
  ultimately have "count (relations_mset l + relations_mset r) x \<ge> 2" using 0 by linarith
  then have "count (relations_mset (Join l r)) x \<ge> 2" by simp
  then have 1: "count (relations_mset (Join l r)) x \<noteq> 1" by simp
  let ?multi = "(relations_mset (Join l r))"
  have "distinct_relations (Join l r) = (\<forall>y\<in># ?multi. count ?multi y = 1)"
    by (simp add: distinct_rels_alt')
  then show False using 1 assms set_implies_mset by fastforce
qed

lemma distinct_elem_left_not_right:
  assumes "distinct_relations (Join l r)"
      and "x \<in> relations l"
    shows "x \<notin> relations r"
  using distinct_elem_right_not_left assms by fast

lemma distinct_relations_disjoint: "distinct_relations (Join l r) \<Longrightarrow> relations l \<inter> relations r = {}"
  using distinct_elem_right_not_left by fast

lemma distinct_trans_l: "distinct_relations (Join l r) \<Longrightarrow> distinct_relations l"
  using subtree_elem_count_l by (fastforce simp: distinct_rels_alt)

lemma distinct_trans_r: "distinct_relations (Join l r) \<Longrightarrow> distinct_relations r"
  using subtree_elem_count_r by (fastforce simp: distinct_rels_alt)

lemma distinct_and_disjoint_impl_count1:
  assumes "distinct_relations l"
      and "distinct_relations r"
      and "relations l \<inter> relations r = {}"
      and "x \<in># relations_mset (Join l r)"
  shows "count (relations_mset (Join l r)) x = 1"
proof -
  show ?thesis
  proof(cases "x\<in>relations l")
    case True
    then have "x\<in># relations_mset l" using set_implies_mset by fast
    then have 0: "count (relations_mset l) x = 1" using assms(1) distinct_rels_alt' by metis
    have "x\<notin># relations_mset r" using True assms(3) disjoint_iff mset_implies_set by fast
    then have "count (relations_mset r) x = 0" by (simp add: count_eq_zero_iff)
    then show ?thesis using 0 by simp
  next
    case False
    have "x\<in># relations_mset r" using False assms(4) using mset_implies_set by force
    then have 0: "count (relations_mset r) x = 1" using assms(2) distinct_rels_alt' by metis
    have "x\<notin># relations_mset l" using False assms(3) disjoint_iff mset_implies_set by fast
    then have "count (relations_mset l) x = 0" by (simp add: count_eq_zero_iff)
    then show ?thesis using 0 by simp
  qed
qed

lemma distinct_and_disjoint_impl_distinct:
  "\<lbrakk>distinct_relations l; distinct_relations r; relations l \<inter> relations r = {}\<rbrakk>
    \<Longrightarrow> distinct_relations (Join l r)"
  using distinct_and_disjoint_impl_count1 distinct_rels_alt' by fastforce

lemma reasonable_trans:
  "reasonable_cards cf f (Join l r) \<Longrightarrow> reasonable_cards cf f l \<and> reasonable_cards cf f r"
  by (simp add: Let_def)

lemma mirror_height_eq: "height (mirror t) = height t"
  by(induction t) auto

lemma height_0_rel: "height t = 0 \<Longrightarrow> \<exists>r. t = Relation r"
  by(cases t) auto

lemma height_gt_0_join: "height t > 0 \<Longrightarrow> \<exists>l r. t = Join l r"
  by(cases t) auto

lemma height_decr_l: "height (Join l r) > height l"
  by simp

lemma height_decr_r: "height (Join l r) > height r"
  by simp

lemma mirror_num_relations_eq: "num_relations (mirror t) = num_relations t"
  by(induction t) auto

lemma zig_zag_num_relations_height: "zig_zag t \<Longrightarrow> num_relations t = height t + 1"
  by(induction t rule: zig_zag.induct) auto

lemma ldeep_num_relations_height: "left_deep t \<Longrightarrow> num_relations t = height t + 1"
  by (simp add: zig_zag_num_relations_height ldeep_zig_zag)

lemma rdeep_num_relations_height: "right_deep t \<Longrightarrow> num_relations t = height t + 1"
  by (simp add: zig_zag_num_relations_height rdeep_zig_zag)

lemma num_relations_eq_length: "num_relations t = length (inorder t)"
  by(induction t) auto

lemma reasonable_impl_pos: "reasonable_cards cf f t \<Longrightarrow> pos_rel_cards cf t"
  by(induction t) (auto simp: pos_rel_cards_def Let_def)

lemma cards_list_eq_inorder: "map (\<lambda>(a,_). a) (cards_list cf t) = inorder t"
  by(induction t) auto

lemma cards_list_eq_relations: "(\<lambda>(a,_). a) ` set (cards_list cf t) = relations t"
  by (simp add: cards_list_eq_inorder image_set inorder_eq_set)

lemma cards_eq_c: "(rel,c)\<in>set(cards_list cf t) \<Longrightarrow> cf rel = c"
  by(induction t) auto

lemma finite_trans: "finite (relations (Join l r)) \<Longrightarrow> finite (relations l) \<and> finite (relations r)"
  by simp

lemma distinct_impl_card_eq_length:
  "finite (relations t) \<Longrightarrow> height t \<le> n \<Longrightarrow> distinct_relations t
    \<Longrightarrow> Finite_Set.card (relations t) = length (inorder t)"
proof(induction n arbitrary: t)
  case 0
  then obtain r where "Relation r = t" using height_0_rel by auto
  then show ?case using distinct_relations_def by force
next
  case (Suc n)
  then show ?case
  proof(cases "height t = Suc n")
    case True
    then have "0 < height t" by simp
    then obtain l r where join[simp]: "Join l r = t" using height_gt_0_join by blast
    then have 0: "finite (relations l) \<and> finite (relations r)"
      using Suc.prems(1) finite_trans by blast
    have 1: "height l \<le> n" using True join by (metis height_decr_l less_Suc_eq_le)
    have 2: "height r \<le> n" using True join by (metis height_decr_r less_Suc_eq_le)
    have "Finite_Set.card (relations t) + Finite_Set.card (relations l \<inter> relations r)
              = Finite_Set.card (relations l) + Finite_Set.card (relations r)"
      using card_Un_Int join 0 by (metis JoinTree.joinTree.simps(16))
    then have "Finite_Set.card (relations t)
              = Finite_Set.card (relations l) + Finite_Set.card (relations r)"
      by (simp add: local.Suc.prems(3) distinct_relations_disjoint)
    moreover have "length (inorder t)
              = length (inorder l) + length (inorder r)"
      by (metis JoinTree.inorder.simps(2) join length_append)
    moreover have "Finite_Set.card (relations l) = length (inorder l)"
      using Suc.IH Suc.prems(3) distinct_trans_l 0 1 join by blast
    moreover have "Finite_Set.card (relations r) = length (inorder r)"
      using Suc.IH Suc.prems(3) distinct_trans_r 0 2 join by blast
    ultimately show ?thesis by simp
  next
    case False
    then show ?thesis using Suc by simp
  qed
qed

lemma card_le_length: "Finite_Set.card (relations t) \<le> length (inorder t)"
  apply(induction t)
   apply(auto)[2]
  by (meson add_mono card_Un_le le_trans)

lemma card_eq_length_impl_disjunct:
  assumes "finite (relations (Join l r))"
      and "Finite_Set.card (relations (Join l r)) = length (inorder (Join l r))"
    shows "relations l \<inter> relations r = {}"
proof (rule ccontr)
  assume 0: "relations l \<inter> relations r \<noteq> {}"
  have 1: "finite (relations l) \<and> finite (relations r)" using assms(1) by simp
  then have 2: "Finite_Set.card (relations (Join l r)) + Finite_Set.card (relations l \<inter> relations r)
            = Finite_Set.card (relations l) + Finite_Set.card (relations r)"
    using card_Un_Int by (metis JoinTree.joinTree.simps(16))
  moreover have "Finite_Set.card (relations l \<inter> relations r) > 0" using 0 1 by auto
  ultimately have "Finite_Set.card (relations (Join l r))
            < Finite_Set.card (relations l) + Finite_Set.card (relations r)" by simp
  also have "\<dots> \<le> length (inorder l) + Finite_Set.card (relations r)"
    by (simp add: card_le_length)
  also have "\<dots> \<le> length (inorder l) + length (inorder r)"
    by (simp add: card_le_length)
  finally have "Finite_Set.card (relations (Join l r)) < length (inorder (Join l r))"
    by simp
  then show "False" using assms(2) by simp
qed

lemma card_eq_length_trans_l:
  assumes "finite (relations (Join l r))"
      and "Finite_Set.card (relations (Join l r)) = length (inorder (Join l r))"
    shows "Finite_Set.card (relations l) = length (inorder l)"
proof (rule ccontr)
  assume 0: "Finite_Set.card (relations l) \<noteq> length (inorder l)"
  have "Finite_Set.card (relations (Join l r))
      = length (inorder l) + length (inorder r)"
    using assms(2) by simp
  have "finite (relations l) \<and> finite (relations r)" using assms(1) by simp
  then have "Finite_Set.card (relations (Join l r)) + Finite_Set.card (relations l \<inter> relations r)
            = Finite_Set.card (relations l) + Finite_Set.card (relations r)"
    using card_Un_Int by (metis JoinTree.joinTree.simps(16))
  then have "Finite_Set.card (relations (Join l r))
            = Finite_Set.card (relations l) + Finite_Set.card (relations r)"
    using assms by (simp add: card_eq_length_impl_disjunct)
  moreover have "Finite_Set.card (relations l) < length (inorder l)"
    using 0 card_le_length le_imp_less_or_eq by blast
  ultimately have "Finite_Set.card (relations (Join l r))
            < length (inorder l) + Finite_Set.card (relations r)"
    by simp
  also have "\<dots> \<le> length (inorder l) + length (inorder r)"
    by (simp add: card_le_length)
  finally have "Finite_Set.card (relations (Join l r)) < length (inorder (Join l r))"
    by simp
  then show "False" using assms(2) by simp
qed

lemma card_eq_length_trans_r:
  assumes "finite (relations (Join l r))"
      and "Finite_Set.card (relations (Join l r)) = length (inorder (Join l r))"
    shows "Finite_Set.card (relations r) = length (inorder r)"
  using assms card_eq_length_trans_l mirror_set_eq
  by (metis JoinTree.mirror.simps(2) mirror_num_relations_eq num_relations_eq_length)

lemma card_eq_length_impl_distinct:
  "\<lbrakk>finite (relations t); height t \<le> n; Finite_Set.card (relations t) = length (inorder t)\<rbrakk>
    \<Longrightarrow> distinct_relations t"
proof(induction n arbitrary: t)
  case 0
  then obtain r where "Relation r = t" using height_0_rel by auto
  then show ?case using distinct_relations_def by force
next
  case (Suc n)
  then show ?case
  proof(cases "height t = Suc n")
    case True
    then have "0 < height t" by simp
    then obtain l r where join[simp]: "Join l r = t" using height_gt_0_join by blast
    then have 0: "finite (relations l) \<and> finite (relations r)"
      using Suc.prems(1) finite_trans by blast
    have 1: "height l \<le> n" using True join by (metis height_decr_l less_Suc_eq_le)
    have 2: "height r \<le> n" using True join by (metis height_decr_r less_Suc_eq_le)
    have "Finite_Set.card (relations t) + Finite_Set.card (relations l \<inter> relations r)
              = Finite_Set.card (relations l) + Finite_Set.card (relations r)"
      using card_Un_Int join 0 by (metis JoinTree.joinTree.simps(16))
    then have "Finite_Set.card (relations t)
              = Finite_Set.card (relations l) + Finite_Set.card (relations r)"
      using Suc.prems(1,3) by (simp add: card_eq_length_impl_disjunct)

    have "Finite_Set.card (relations l) = length (inorder l)"
      using Suc.prems(1,3) card_eq_length_trans_l join by blast
    then have 3: "distinct_relations l" using Suc.IH 0 1 by blast
    have "Finite_Set.card (relations r) = length (inorder r)"
      using Suc.IH Suc.prems(1,3) card_eq_length_trans_r join by blast
    then have 4: "distinct_relations r" using Suc.IH 0 2 by blast
    have "relations l \<inter> relations r = {}"
      using card_eq_length_impl_disjunct join Suc.prems(1,3) by blast
    then show ?thesis using 3 4 distinct_and_disjoint_impl_distinct by fastforce
  next
    case False
    then show ?thesis using Suc by simp
  qed
qed

lemma list_sel_revorder_eq_inorder_x: "list_sel f (revorder l) ys = list_sel f (inorder l) ys"
  unfolding revorder_eq_rev_inorder using mset_x_eq_list_sel_eq mset_rev by blast

lemma list_sel_revorder_eq_inorder_y: "list_sel f xs (revorder r) = list_sel f xs (inorder r)"
  unfolding revorder_eq_rev_inorder using mset_y_eq_list_sel_eq mset_rev by blast

lemma list_sel_revorder_eq_inorder:
  "list_sel f (revorder l) (revorder r) = list_sel f (inorder l) (inorder r)"
  unfolding list_sel_revorder_eq_inorder_x list_sel_revorder_eq_inorder_y by simp

lemma card_join_alt:
  "card cf f (Join l r) = list_sel f (revorder l) (revorder r) * card cf f l * card cf f r"
  unfolding list_sel_revorder_eq_inorder by simp

lemma distinct_alt:
  "finite (relations t)
    \<Longrightarrow> distinct_relations t \<longleftrightarrow> Finite_Set.card (relations t) = length (inorder t)"
  using card_eq_length_impl_distinct distinct_impl_card_eq_length by auto

lemma distinct_alt2:
  "distinct_relations (Join l r)
    \<longleftrightarrow> distinct_relations l \<and> distinct_relations r \<and> relations l \<inter> relations r = {}"
  using distinct_relations_disjoint distinct_trans_l distinct_trans_r
  by (auto elim: distinct_and_disjoint_impl_distinct)

lemma pos_rel_cards_subtrees:
  "pos_rel_cards cf (Join l r) = (pos_rel_cards cf l \<and> pos_rel_cards cf r)"
proof -
  have "pos_rel_cards cf (Join l r) = (\<forall>(_,c)\<in>set (cards_list cf (Join l r)). c>0)"
    by (simp add: pos_rel_cards_def)
  also have "\<dots> = (\<forall>(_,c)\<in>set (cards_list cf l @ cards_list cf r). c>0)" by simp
  also have "\<dots> = ((\<forall>(_,c)\<in>set (cards_list cf l). c>0) \<and> (\<forall>(_,c)\<in>set (cards_list cf r). c>0))"
    by auto
  also have "\<dots> = (pos_rel_cards cf l \<and> pos_rel_cards cf r)"
    by (simp add: pos_rel_cards_def)
  finally show ?thesis by simp
qed

lemma pos_rel_cards_eq_pos_list_cards:
  "pos_rel_cards cf t \<longleftrightarrow> pos_list_cards cf (inorder t)"
  by(induction t) (auto simp: pos_rel_cards_def pos_list_cards_def)

lemma pos_list_cards_split:
  "pos_list_cards cf (xs@ys) \<longleftrightarrow> pos_list_cards cf xs \<and> pos_list_cards cf ys"
  by(induction xs) (auto simp: pos_list_cards_def)

lemma pos_sel_reason_impl_reason:
  "\<lbrakk>pos_rel_cards cf t; sel_reasonable sel\<rbrakk> \<Longrightarrow> reasonable_cards cf sel t"
proof(induction t)
  case (Join l r)
  then have "pos_rel_cards cf l \<and> pos_rel_cards cf r" using pos_rel_cards_subtrees by blast
  then have 0: "reasonable_cards cf sel l \<and> reasonable_cards cf sel r" using Join by simp
  have "list_sel sel (inorder l) (inorder r) \<le> 1"
    using Join.prems(2) sel_reasonable_def list_sel_reasonable by fast
  obtain c where 1:
    "list_sel sel (inorder l) (inorder r) * card cf sel l * card cf sel r = c"
    by simp
  then have "c = list_sel sel (inorder l) (inorder r) * card cf sel l * card cf sel r"
    by simp
  then have 2: "c \<le> 1 * card cf sel l * card cf sel r"
    using Join.prems(2) list_sel_reasonable 0 mult_left_le_one_le mult_right_less_imp_less
    by (smt (verit, ccfv_SIG) card.simps(1) card.simps(2) reasonable_cards.elims(2))
  from 1 have "c > 0 * card cf sel l * card cf sel r"
    using Join.prems(2) list_sel_reasonable 0 mult_pos_pos
    by (metis card.simps(1) card.simps(2) mult_eq_0_iff reasonable_cards.elims(2))
  then show ?case using 0 1 2 by simp
qed(simp add: pos_rel_cards_def)

lemma create_rdeep_order: "xs \<noteq> [] \<Longrightarrow> inorder (create_rdeep xs) = xs"
proof(induction xs)
  case (Cons x xs)
  then show ?case by(cases xs) auto
qed(simp)

lemma create_ldeep_rev_order: "xs \<noteq> [] \<Longrightarrow> inorder (create_ldeep_rev xs) = rev xs"
proof(induction xs)
  case (Cons x xs)
  then show ?case by(cases xs) auto
qed(simp)

lemma create_ldeep_order: "xs \<noteq> [] \<Longrightarrow> inorder (create_ldeep xs) = xs"
  by (simp add: create_ldeep_def create_ldeep_rev_order)

lemma create_rdeep_rdeep: "xs \<noteq> [] \<Longrightarrow> right_deep (create_rdeep xs)"
proof(induction xs)
  case (Cons x xs)
  then show ?case by(cases xs) auto
qed(simp)

lemma create_ldeep_rev_ldeep: "xs \<noteq> [] \<Longrightarrow> left_deep (create_ldeep_rev xs)"
proof(induction xs)
  case (Cons x xs)
  then show ?case by(cases xs) auto
qed(simp)

lemma create_ldeep_ldeep: "xs \<noteq> [] \<Longrightarrow> left_deep (create_ldeep xs)"
  by (simp add: create_ldeep_rev_ldeep create_ldeep_def)

lemma create_ldeep_rev_relations: "xs \<noteq> [] \<Longrightarrow> relations (create_ldeep_rev xs) = set xs"
  using create_ldeep_rev_order[of xs] inorder_eq_set by force

lemma create_ldeep_relations: "xs \<noteq> [] \<Longrightarrow> relations (create_ldeep xs) = set xs"
  by (simp add: create_ldeep_rev_relations create_ldeep_def)

lemma create_ldeep_rev_Cons:
  "xs \<noteq> [] \<Longrightarrow> create_ldeep_rev (x#xs) = Join (create_ldeep_rev xs) (Relation x)"
  using create_ldeep_rev.simps(3) neq_Nil_conv by metis

lemma create_ldeep_snoc: "xs \<noteq> [] \<Longrightarrow> create_ldeep (xs@[x]) = Join (create_ldeep xs) (Relation x)"
  by (simp add: create_ldeep_rev_Cons create_ldeep_def)

lemma create_ldeep_inorder[simp]: "left_deep t \<Longrightarrow> create_ldeep (inorder t) = t"
  apply(induction t)
   apply (simp add: create_ldeep_def)
  by (metis Nil_is_append_conv create_ldeep_snoc inorder.simps
      ldeep_trans left_deep.simps(3) not_Cons_self2 relations_mset.cases)

lemma create_rdeep_inorder[simp]: "right_deep t \<Longrightarrow> create_rdeep (inorder t) = t"
  apply(induction t)
   apply simp
  by (metis create_rdeep.simps(3) create_rdeep_order first_node_first_inorder
      joinTree.distinct(1) joinTree.inject(2) neq_Nil_conv right_deep.elims(2))

lemma ldeep_div_eq_sel:
  assumes "reasonable_cards cf f (Join l (Relation rel))"
      and "c = card cf f (Join l (Relation rel))"
      and "cr = card cf f (Relation rel)"
    shows "c / (card cf f l * cr) = list_sel f (inorder l) [rel]"
  using assms by auto

lemma ldeep_n_eq_card:
  "\<lbrakk>distinct_relations t; left_deep t\<rbrakk> \<Longrightarrow> ldeep_n f cf (revorder t) = card cf f t"
proof(induction t arbitrary: cf rule: left_deep.induct)
  case (2 l rr)
  let ?rev = "revorder (Join l (Relation rr))"
  have "?rev = rr # revorder l" by simp
  have "ldeep_n f cf ?rev = ldeep_n f cf (rr#revorder l)" by simp
  also have "\<dots> = list_sel_aux' f (revorder l) rr
      * cf rr * ldeep_n f cf (revorder l)" by simp
  also have "\<dots> = list_sel_aux' f (inorder l) rr * cf rr
              * ldeep_n f cf (revorder l)"
    using mset_x_eq_list_sel_aux'_eq mset_rev by (fastforce simp: revorder_eq_rev_inorder)
  also have "\<dots> = list_sel_aux' f (inorder l) rr * cf rr * card cf f l"
    using 2 distinct_trans_l by auto
  finally show ?case
    using list_sel_sing_aux' card.simps mult.commute
    by (metis ab_semigroup_mult_class.mult_ac(1) inorder.simps(1))
qed(auto)

lemma ldeep_n_eq_card_subtree:
  "\<lbrakk>distinct_relations (Join t r'); left_deep t\<rbrakk> \<Longrightarrow> ldeep_n f cf (revorder t) = card cf f t"
  using ldeep_n_eq_card distinct_trans_l by blast


lemma distinct_ldeep_T'_prepend:
  "distinct (ys@xs) \<Longrightarrow> ldeep_T' (ldeep_s f (ys@xs)) cf xs = ldeep_T' (ldeep_s f xs) cf xs"
proof(induction xs arbitrary: ys)
  case (Cons x xs)
  then have 0: "distinct (x#xs)" by simp
  have "ldeep_T' (ldeep_s f (ys@x#xs)) cf (x#xs)
           = cf x * (ldeep_s f (ys@x#xs)) x * ldeep_T' (ldeep_s f (ys@x#xs)) cf xs" by simp
  also have "\<dots> = cf x * (ldeep_s f (ys@x#xs)) x * ldeep_T' (ldeep_s f xs) cf xs"
    using Cons.IH[of "ys@[x]"] Cons.prems by simp
  also have "\<dots> = cf x * list_sel_aux' f xs x * ldeep_T' (ldeep_s f xs) cf xs"
    using distinct_ldeep_s_eq_aux[OF Cons.prems] by simp
  also have "\<dots> = cf x * (ldeep_s f (x#xs)) x * ldeep_T' (ldeep_s f xs) cf xs"
    using distinct_ldeep_s_eq_aux Cons.prems by simp
  also have "\<dots> = cf x * (ldeep_s f (x#xs)) x * ldeep_T' (ldeep_s f (x#xs)) cf xs"
    using Cons.IH[of "[x]"] 0 by simp
  finally show ?case by simp
qed(simp)

lemma ldeep_T'_eq_ldeep_n: "distinct xs \<Longrightarrow> ldeep_T' (ldeep_s f xs) cf xs = ldeep_n f cf xs"
proof(induction xs)
  case (Cons x xs)
  then have 0: "distinct xs" by simp
  have "ldeep_T' (ldeep_s f (x # xs)) cf (x # xs)
           = cf x * (ldeep_s f (x # xs)) x * ldeep_T' (ldeep_s f (x # xs)) cf xs" by simp
  also have "\<dots> = cf x * list_sel_aux' f xs x * ldeep_T' (ldeep_s f (x # xs)) cf xs" by simp
  also have "\<dots> = cf x * list_sel_aux' f xs x * ldeep_T' (ldeep_s f xs) cf xs"
    using distinct_ldeep_T'_prepend[of "[x]"] Cons.prems by simp
  also have "\<dots> = cf x * list_sel_aux' f xs x * ldeep_n f cf xs"
    using Cons.IH 0 by simp
  finally show ?case by simp
qed(simp)

lemma ldeep_T'_eq_foldl: "acc * ldeep_T' f cf xs = foldl (\<lambda>a b. a * cf b * f b) acc xs"
proof(induction xs arbitrary: acc)
  case (Cons x xs)
  have "acc * ldeep_T' f cf (x # xs) = acc * cf x * f x * ldeep_T' f cf xs" by simp
  also have "\<dots> = foldl (\<lambda>a b. a * cf b * f b) (acc * cf x * f x) xs" using Cons by simp
  finally show ?case by simp
qed(simp)

lemma distinct_ldeep_T_prepend:
  "distinct (ys@xs) \<Longrightarrow> ldeep_T (ldeep_s f (ys@xs)) cf xs = ldeep_T (ldeep_s f xs) cf xs"
  using ldeep_T'_eq_foldl[of 1 "ldeep_s f (ys@xs)" cf xs]
  by (simp add: distinct_ldeep_T'_prepend ldeep_T_def ldeep_T'_eq_foldl)

lemma ldeep_T_eq_ldeep_T'_aux: "ldeep_T sf cf xs = ldeep_T' sf cf xs"
  using ldeep_T'_eq_foldl[of 1 sf] ldeep_T_def by fastforce

lemma ldeep_T_eq_ldeep_T': "ldeep_T = ldeep_T'"
  using ldeep_T_eq_ldeep_T'_aux by blast

lemma ldeep_T_eq_ldeep_n: "distinct xs \<Longrightarrow> ldeep_T (ldeep_s f xs) cf xs = ldeep_n f cf xs"
  by (simp add: ldeep_T_eq_ldeep_T' ldeep_T'_eq_ldeep_n)

lemma ldeep_T_app: "ldeep_T f cf (xs@ys) = ldeep_T f cf xs * ldeep_T f cf ys"
  using ldeep_T_def foldl_append ldeep_T'_eq_foldl
  by (metis (mono_tags, lifting) monoid.left_neutral mult.monoid_axioms)

lemma ldeep_T_empty: "ldeep_T f cf [] = 1"
  by (simp add: ldeep_T_def)

lemma ldeep_T_eq_if_cf_eq: "\<forall>x \<in> set xs. f x = g x \<Longrightarrow> ldeep_T sf f xs = ldeep_T sf g xs"
  unfolding ldeep_T_eq_ldeep_T' by (induction xs) auto

lemma ldeep_n_pos: "\<lbrakk>pos_list_cards cf xs; sel_reasonable f\<rbrakk> \<Longrightarrow> ldeep_n f cf xs > 0"
proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    using list_sel_aux'_reasonable pos_list_cards_def mult_pos_pos set_subset_Cons
    by (metis list.set_intros(1) ldeep_n.simps(2) subset_code(1))
qed

lemma ldeep_T_eq_card:
  "\<lbrakk>distinct_relations t; left_deep t\<rbrakk>
    \<Longrightarrow> ldeep_T (ldeep_s f (revorder t)) cf (revorder t) = card cf f t"
  using ldeep_T_eq_ldeep_n[of "revorder t"] ldeep_n_eq_card distinct_rels_alt by fastforce

lemma ldeep_T_pos':
  "\<lbrakk>distinct xs; pos_list_cards cf xs; sel_reasonable f\<rbrakk> \<Longrightarrow> ldeep_T (ldeep_s f xs) cf xs > 0"
  by (simp add: ldeep_T_eq_ldeep_n ldeep_n_pos)

lemma ldeep_T_pos: "\<lbrakk>\<forall>x\<in> set ys. cf x > 0; sel_reasonable f\<rbrakk> \<Longrightarrow> ldeep_T (ldeep_s f xs) cf ys > 0"
  apply(induction ys arbitrary: xs)
   apply(auto simp: ldeep_T_def)[2]
  by (metis Groups.comm_monoid_mult_class.mult_1 ldeep_T'_eq_foldl ldeep_s_pos zero_less_mult_iff)

end