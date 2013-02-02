(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* General Interface for Finite Trees *}

theory Finite_Tree
imports
  "~~/src/HOL/Library/Sublist"
  Restricted_Predicates
begin

text {*By the interface we are actually not necessarily finite, but just
finitely branching. However, all interesting properties below are only valid
on the inductively defined set of trees built from the constructor 'mk'.*}
locale finite_tree =
  fixes mk :: "'b \<Rightarrow> 'a list \<Rightarrow> 'a" -- "constract a tree from a node and a list of trees"
    and root :: "'a \<Rightarrow> 'b" -- "the root-node of a tree"
    and succs :: "'a \<Rightarrow> 'a list" -- "the direct subtrees of a tree"
  assumes inject: "mk x ts = mk x' ts' \<longleftrightarrow> x = x' \<and> ts = ts'" -- "'mk' behaves like a dataype constructor"
    and root_mk [simp]: "root (mk x ts) = x"
    and succs_mk [simp]: "succs (mk x ts) = ts"
begin

inductive_set
  trees
and
  trees_list
for A
where
  "x \<in> A \<Longrightarrow> ts \<in> trees_list A \<Longrightarrow> mk x ts \<in> trees A" |
  "[] \<in> trees_list A" |
  "t \<in> trees A \<Longrightarrow> ts \<in> trees_list A \<Longrightarrow> (t # ts) \<in> trees_list A"

lemma trees_simps [iff]:
  "mk x ts \<in> trees A \<longleftrightarrow> x \<in> A \<and> ts \<in> trees_list A"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  {
    assume ?lhs hence ?rhs
      by (cases) (simp add: inject)
  } moreover {
    assume ?rhs hence ?lhs
      by (auto intro: trees_trees_list.intros)
  } ultimately show ?thesis by blast
qed

lemma trees_list_intro:
  "\<forall>t\<in>set ts. t \<in> trees A \<Longrightarrow> ts \<in> trees_list A"
  by (induct ts) (auto intro: trees_trees_list.intros)

inductive_set
  rec_set
and
  list_rec_set
for f g h where
  "x \<in> A \<Longrightarrow>
    ts \<in> trees_list A \<Longrightarrow>
    (ts, y) \<in> list_rec_set f g h \<Longrightarrow>
    (mk x ts, f x ts y) \<in> rec_set f g h" |
  "([], g) \<in> list_rec_set f g h" |
  "t \<in> trees A \<Longrightarrow>
    (t, y) \<in> rec_set f g h \<Longrightarrow>
    ts \<in> trees_list A \<Longrightarrow>
    (ts, y') \<in> list_rec_set f g h \<Longrightarrow>
    (t # ts, h t ts y y') \<in> list_rec_set f g h"

lemma rec_setD:
  assumes "(mk x ts, y) \<in> rec_set f g h"
  shows "\<exists>z. (ts, z) \<in> list_rec_set f g h \<and> y = f x ts z"
  using assms
  by (cases rule: rec_set.cases) (auto simp: inject)

lemma list_rec_set_Nil [iff]:
  "([], x) \<in> list_rec_set f g h \<longleftrightarrow> x = g" (is "?lhs = ?rhs")
proof
  assume ?lhs thus ?rhs by (cases) simp
next
  assume ?rhs thus ?lhs by (simp) (rule rec_set_list_rec_set.intros)
qed

lemma list_rec_set_ConsD:
  assumes "(t # ts, x) \<in> list_rec_set f g h"
  shows "\<exists>y z. (t, y) \<in> rec_set f g h \<and> (ts, z) \<in> list_rec_set f g h \<and>
    x = h t ts y z"
  using assms
  by (cases rule: list_rec_set.cases) auto

lemma functional:
  shows "t \<in> trees A \<Longrightarrow> \<exists>!y::'c. (t, y) \<in> rec_set f g h"
    and "ts \<in> trees_list A \<Longrightarrow> \<exists>!y::'d. (ts, y) \<in> list_rec_set f g h"
proof (induct t and ts rule: trees_trees_list.inducts)
  fix x ts
  assume 1: "x \<in> A" "ts \<in> trees_list A"
    and "\<exists>!y. (ts, y) \<in> list_rec_set f g h"
  then obtain y where 2: "(ts, y) \<in> list_rec_set f g h"
    and 3: "\<forall>x. (ts, x) \<in> list_rec_set f g h \<longrightarrow> x = y" by auto
  show "\<exists>!y. (mk x ts, y) \<in> rec_set f g h"
  proof
    show "(mk x ts, f x ts y) \<in> rec_set f g h"
     using 1 and 2 by (rule rec_set_list_rec_set.intros)
  next
    fix z
    assume "(mk x ts, z) \<in> rec_set f g h"
    from rec_setD [OF this] obtain u where "(ts, u) \<in> list_rec_set f g h"
      and "z = f x ts u" by auto
    moreover with 3 have "u = y" by auto
    ultimately show "z = f x ts y" by simp
  qed
next
  fix t ts
  assume 1: "t \<in> trees A"
    and *: "\<exists>!y. (t, y) \<in> rec_set f g h"
    and 3: "ts \<in> trees_list A"
    and **: "\<exists>!y. (ts, y) \<in> list_rec_set f g h"
  from * obtain u where 2: "(t, u) \<in> rec_set f g h"
    and uniq1: "\<forall>a. (t, a) \<in> rec_set f g h \<longrightarrow> a = u" by auto
  from ** obtain v where 4: "(ts, v) \<in> list_rec_set f g h"
    and uniq2: "\<forall>a. (ts, a) \<in> list_rec_set f g h \<longrightarrow> a = v" by auto
  show "\<exists>!y. (t # ts, y) \<in> list_rec_set f g h"
  proof
    show "(t # ts, h t ts u v) \<in> list_rec_set f g h"
      using 1 2 3 4 by (rule rec_set_list_rec_set.intros)
  next
    fix z
    assume "(t # ts, z) \<in> list_rec_set f g h"
    from list_rec_set_ConsD [OF this] obtain a b where
      "(t, a) \<in> rec_set f g h" and "(ts, b) \<in> list_rec_set f g h"
      and "z = h t ts a b" by auto
    moreover with uniq1 and uniq2 have "a = u" and "b = v" by auto
    ultimately show "z = h t ts u v" by auto
  qed
next
  show "\<exists>!y. ([], y) \<in> list_rec_set f g h"
  proof
    show "([], g) \<in> list_rec_set f g h" by simp
  next
    fix y
    assume "([], y) \<in> list_rec_set f g h"
    thus "y = g" by auto
  qed
qed

definition
  rec ::
    "('b \<Rightarrow> 'a list \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow>
      'c \<Rightarrow>
     ('a \<Rightarrow> 'a list \<Rightarrow> 'd \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow>
     'a \<Rightarrow>
     'd"
where
  "rec f g h t = (THE y. (t, y) \<in> rec_set f g h)"

definition
  list_rec ::
    "('b \<Rightarrow> 'a list \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow>
      'c \<Rightarrow>
      ('a \<Rightarrow> 'a list \<Rightarrow> 'd \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow>
      'a list \<Rightarrow>
      'c"
where
  "list_rec f g h ts = (THE y. (ts, y) \<in> list_rec_set f g h)"

lemma rec_simps [simp]:
  "x \<in> A \<Longrightarrow> ts \<in> trees_list A \<Longrightarrow> rec f g h (mk x ts) = f x ts (list_rec f g h ts)"
  unfolding rec_def list_rec_def
  using the1_equality [OF functional(1), of "mk x ts" A _ f g h]
    and the1_equality [OF functional(2), of ts A _ f g h]
  by (metis functional(2) rec_set_list_rec_set.intros(1) trees_trees_list.intros(1))

lemma list_rec_simps [simp]:
  "list_rec f g h [] = g"
  "t \<in> trees A \<Longrightarrow> ts \<in> trees_list A \<Longrightarrow> list_rec f g h (t # ts) = h t ts (rec f g h t) (list_rec f g h ts)"
  unfolding rec_def list_rec_def
  using the1_equality [OF functional(2), of "[]" A _ f g h]
  apply (metis rec_set_list_rec_set.intros(2) trees_trees_list.intros(2))
  using the1_equality [OF functional(2), of "t # ts" A _ f g h]
    and the1_equality [OF functional(2), of ts A _ f g h]
    and the1_equality [OF functional(1), of t A _ f g h]
  by (metis functional(1) functional(2) rec_set_list_rec_set.intros(3) trees_list.simps)

definition "nodes =
  rec (\<lambda>x ts N. {x} \<union> N) ({}) (\<lambda>t ts M N. M \<union> N)"

definition "nodes_list =
  list_rec (\<lambda>x ts N. {x} \<union> N) {} (\<lambda>t ts M N. M \<union> N)"

lemma nodes:
  "x \<in> A \<Longrightarrow> ts \<in> trees_list A \<Longrightarrow> nodes (mk x ts) = {x} \<union> nodes_list ts"
  "nodes_list [] = {}"
  "t \<in> trees A \<Longrightarrow> ts \<in> trees_list A \<Longrightarrow> nodes_list (t # ts) = nodes t \<union> nodes_list ts"
  by (simp_all add: nodes_def nodes_list_def)

lemma trees_list_Cons [iff]:
  "(t # ts) \<in> trees_list A \<longleftrightarrow> t \<in> trees A \<and> ts \<in> trees_list A"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  { assume ?lhs hence ?rhs
      by (cases) auto
  } moreover {
    assume ?rhs hence ?lhs
      by (auto intro: trees_trees_list.intros)
  } ultimately show ?thesis by blast
qed

lemma nodes_simps [simp]:
  "x \<in> A \<Longrightarrow> ts \<in> trees_list A \<Longrightarrow>
    nodes (mk x ts) = {x} \<union> \<Union>set (map nodes ts)"
  by (induct ts) (auto simp: nodes)

inductive
  subtree :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  base [intro]: "t \<in> set ts \<Longrightarrow> subtree t (mk x ts)" |
  step [intro]: "subtree s t \<Longrightarrow> t \<in> set ts \<Longrightarrow> subtree s (mk x ts)"

definition size :: "'a \<Rightarrow> nat" where
  "size = rec (\<lambda>x ts n. n + Suc 0) 0 (\<lambda>t ts m n. m + n + Suc 0)"

definition size_list :: "'a list \<Rightarrow> nat" where
  "size_list = list_rec (\<lambda>x ts n. Suc n) 0 (\<lambda>t ts m n. Suc (m + n))"

lemma size:
  "x \<in> A \<Longrightarrow> ts \<in> trees_list A \<Longrightarrow> size (mk x ts) = Suc (size_list ts)"
  "size_list [] = 0"
  "t \<in> trees A \<Longrightarrow> ts \<in> trees_list A \<Longrightarrow> size_list (t # ts) = Suc (size t + size_list ts)"
  by (simp_all add: size_def size_list_def)

lemma size_simps [simp]:
  "x \<in> A \<Longrightarrow> ts \<in> trees_list A \<Longrightarrow>
    size (mk x ts) = Suc (list_size size ts)"
  by (induct ts) (auto simp: size)

lemma size_simp1:
  "s \<in> set ss \<Longrightarrow> subtree t s \<Longrightarrow> size t < size s \<Longrightarrow> size t < Suc (list_size size ss)"
  by (induct ss) auto

lemma size_simp2:
  "t \<in> set ts \<Longrightarrow> size t < Suc (list_size size ts)"
  by (induct ts) auto

lemmas size_simps' = size_simp1 size_simp2

lemma set_trees_list_trees [simp]:
  "t \<in> set ts \<Longrightarrow> ts \<in> trees_list A \<Longrightarrow> t \<in> trees A"
  by (induct ts arbitrary: t) auto

lemma subtree_size:
  "subtree t s \<Longrightarrow> s \<in> trees A \<Longrightarrow> size t < size s"
  by (induct rule: subtree.induct) (auto simp: size_simps')

lemma mk_trees_trees_list [simp]:
  "mk x ts \<in> trees A \<Longrightarrow> x \<in> A \<Longrightarrow> ts \<in> trees_list A"
  by auto

lemma subtree_trees:
  "subtree s t \<Longrightarrow> t \<in> trees A \<Longrightarrow> s \<in> trees A"
  by (induct rule: subtree.induct) auto

abbreviation subtreeeq where "subtreeeq \<equiv> subtree\<^sup>=\<^sup>="

lemma subtreeeq_trees:
  "subtreeeq s t \<Longrightarrow> t \<in> trees A \<Longrightarrow> s \<in> trees A"
  using subtree_trees by auto

lemma trees_intros:
  "x \<in> A \<Longrightarrow>
    \<forall>t\<in>set ts. t \<in> trees A \<Longrightarrow>
    mk x ts \<in> trees A"
  by (induct ts) (auto intro: trees_trees_list.intros)

lemma trees_cases [consumes 1, cases set: trees]:
  assumes "t \<in> trees A"
    and "\<And>f ts. \<lbrakk>f \<in> A; \<forall>t\<in>set ts. t \<in> trees A; t = mk f ts\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms by (cases rule: trees.cases) (auto intro: subtree_trees)

lemma root_succs:
  assumes "t \<in> trees A"
  shows "mk (root t) (succs t) = t"
  using assms by (cases t) simp_all

lemma in_succs_imp_subtree:
  assumes "t \<in> trees A" and "s \<in> set (succs t)"
  shows "subtree s t"
  using assms by (cases t) (auto)
lemma restrict_to_trees_eq_measure_on_trees [simp]:
  "restrict_to (\<lambda>x y. f x < f y) (trees A) = measure_on f (trees A)"
  by (intro ext) (auto)

lemma wfp_on_subtree:
  "wfp_on subtree (trees A)"
proof -
  let ?P = "\<lambda>x y. size x < size y"
  have *: "wfp_on ?P (trees A)"
    by (rule wfp_on_restrict_to [THEN iffD1]) simp
  show ?thesis
    by (auto simp: *
      intro!: wfp_on_mono [OF subset_refl, of "trees A" subtree ?P] subtree_size)
qed

lemma subtree_trans:
  assumes "subtree s t" and "subtree t u" shows "subtree s u"
  using assms(2, 1)
  by (induct rule: subtree.induct) (auto)

lemma subtree_nodes_subset:
  assumes "subtree s t" and "t \<in> trees A" shows "nodes s \<subseteq> nodes t"
  using assms by (induct) force+

lemma trees_induct_aux:
  assumes "\<And>f ts. f \<in> A \<Longrightarrow> (\<And>t. \<lbrakk>t \<in> set ts\<rbrakk> \<Longrightarrow> t \<in> trees A \<and> P t) \<Longrightarrow> P (mk f ts)"
  shows "t \<in> trees A \<Longrightarrow> P t" and "ts \<in> trees_list A \<Longrightarrow> \<forall>t\<in>set ts. P t"
  by (induct t and ts rule: trees_trees_list.inducts [where ?P2.0 = "\<lambda>ts. \<forall>t\<in>set ts. P t"])
     (rule assms, auto)

lemma trees_induct [consumes 1, case_names mk, induct set: trees]:
  assumes "t \<in> trees A"
    and "\<And>f ts. f \<in> A \<Longrightarrow> (\<And>t. \<lbrakk>t \<in> set ts\<rbrakk> \<Longrightarrow> t \<in> trees A \<and> P t) \<Longrightarrow> P (mk f ts)"
  shows "P t"
  using assms and trees_induct_aux(1) by metis

lemma sublisteq_size:
  assumes "sublisteq ss ts"
  shows "list_size size ss \<le> list_size size ts"
  using assms by (induct) auto

lemma not_sublisteq_size: "list_size size ys < list_size size xs \<Longrightarrow> \<not> sublisteq xs ys"
  by (metis sublisteq_size linorder_not_less)

lemma trees_list_insert:
  assumes "ss @ ts \<in> trees_list A" and "t \<in> trees A"
  shows "ss @ t # ts \<in> trees_list A"
  using assms by (induct ss) auto

lemma list_hembeq_mono:
  assumes "\<And>s t. P s t \<longrightarrow> Q s t"
  shows "list_hembeq P s t \<longrightarrow> list_hembeq Q s t"
proof
  assume "list_hembeq P s t" thus "list_hembeq Q s t"
    by (induct) (auto simp: assms)
qed

lemma reflclp_mono:
  assumes "\<And>s t. P s t \<longrightarrow> Q s t"
  shows "P\<^sup>=\<^sup>= s t \<longrightarrow> Q\<^sup>=\<^sup>= s t"
  using assms by auto

text {*Homeomorphic embedding on trees.*}
inductive
  tree_hembeq :: "('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  for P :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
where
  tree_hembeq_base [intro]: "t \<in> set ts \<Longrightarrow> tree_hembeq P t (mk f ts)" |
  tree_hembeq_sublisteq [intro]: "P\<^sup>=\<^sup>= f g \<Longrightarrow> sublisteq ss ts \<Longrightarrow> tree_hembeq P (mk f ss) (mk g ts)" |
  tree_hembeq_trans [intro]: "tree_hembeq P s t \<Longrightarrow> tree_hembeq P t u \<Longrightarrow> tree_hembeq P s u" |
  tree_hembeq_ctxt [intro]: "tree_hembeq P s t \<Longrightarrow> tree_hembeq P (mk f (ss1 @ s # ss2)) (mk f (ss1 @ t # ss2))"

lemma tree_hembeq_reflclp [simp]:
  "tree_hembeq (P\<^sup>=\<^sup>=) = tree_hembeq P" (is "?P = ?Q")
proof (intro ext)
  fix s t
  show "?P s t = ?Q s t"
  proof
    assume "?P s t" then show "?Q s t" by (induct) auto
  next
    assume "?Q s t" then show "?P s t" by (induct) auto
  qed
qed

lemma tree_hembeq_mono:
  assumes "\<And>s t. P s t \<longrightarrow> Q s t"
  shows "tree_hembeq P s t \<longrightarrow> tree_hembeq Q s t"
proof
  assume "tree_hembeq P s t" then show "tree_hembeq Q s t"
  proof (induct)
    case (tree_hembeq_sublisteq f g ss ts)
    show ?case
    proof (rule tree_hembeq.tree_hembeq_sublisteq)
      show "Q\<^sup>=\<^sup>= f g" using `P\<^sup>=\<^sup>= f g` by (auto simp: assms)
    next
      show "sublisteq ss ts" by fact
    qed
  qed force+
qed

lemma tree_hembeq_subtree:
  assumes "tree_hembeq P s t" and "subtree t u" shows "tree_hembeq P s u"
  using assms(2, 1)
  by (induct rule: subtree.induct) auto

lemma list_hembeq_tree_hembeq_imp_sublisteq:
  assumes "list_hembeq (tree_hembeq P) xs zs"
    (is "list_hembeq ?P xs zs")
  shows "\<exists>ys. sublisteq ys zs \<and> length ys = length xs \<and>
    (\<forall>i<length xs. (tree_hembeq P)\<^sup>=\<^sup>= (xs ! i) (ys ! i))"
using assms
proof (induct)
  case (list_hembeq_Nil ys)
  thus ?case by auto
next
  case (list_hembeq_Cons xs zs z)
  then obtain ys where *: "sublisteq ys zs" and "length ys = length xs"
    and "\<forall>i<length xs. ?P\<^sup>=\<^sup>= (xs ! i) (ys ! i)" by auto
  moreover have "sublisteq ys (z # zs)" using * by auto
  ultimately show ?case by blast
next
  case (list_hembeq_Cons2 x z xs zs)
  then obtain ys where *: "sublisteq ys zs"
    and len: "length ys = length xs"
    and **: "\<forall>i<length xs. ?P\<^sup>=\<^sup>= (xs ! i) (ys ! i)" by auto
  let ?ys = "z # ys" and ?xs = "x # xs"
  from * have "sublisteq ?ys (z # zs)" by auto
  moreover have "length ?ys = length ?xs" using len by auto
  moreover have "\<forall>i<length ?xs. ?P\<^sup>=\<^sup>= (?xs ! i) (?ys ! i)"
  proof (intro allI impI)
    fix i
    assume i: "i < length ?xs"
    show "?P\<^sup>=\<^sup>= (?xs ! i) (?ys ! i)"
      using i and ** and `?P\<^sup>=\<^sup>= x z`
      by (cases i) (auto)
  qed
  ultimately show ?case by blast
qed

lemma args_steps_imp_steps_gen:
  assumes ctxt: "\<And>s t ss1 ss2. r (length ss1) s t \<Longrightarrow>
    length ts = Suc (length ss1 + length ss2) \<Longrightarrow>
    R\<^sup>*\<^sup>* (mk f (ss1 @ s # ss2)) (mk f (ss1 @ t # ss2))"
    and len: "length ss = length ts"
    and args: "\<And>i. i < length ts \<Longrightarrow> (r i)\<^sup>*\<^sup>* (ss ! i) (ts ! i)"
  shows "R\<^sup>*\<^sup>* (mk f ss) (mk f ts)"
proof -
  let ?ts = "\<lambda>i. take i ts @ drop i ss"
  {
    fix s t and ss1 ss2 :: "'a list"
    assume "(r (length ss1))\<^sup>*\<^sup>* s t"
      and len: "length ts = Suc (length ss1 + length ss2)"
    then have "R\<^sup>*\<^sup>* (mk f (ss1 @ s # ss2)) (mk f (ss1 @ t # ss2))"
    proof (induct)
      case (step t u)
      from step(3) [OF len] and ctxt [OF step(2) len]
        show ?case by auto
    qed simp
  }
  note * = this
  have **: "\<forall>i\<le>length ts. R\<^sup>*\<^sup>* (mk f ss) (mk f (?ts i))"
  proof (intro allI impI)
    fix i assume "i \<le> length ts"
    then show "R\<^sup>*\<^sup>* (mk f ss) (mk f (?ts i))"
    proof (induct i)
      case 0
      then show ?case by simp
    next
      case (Suc i)
      then have IH: "R\<^sup>*\<^sup>* (mk f ss) (mk f (?ts i))"
        and i: "i < length ts" by auto
      have si: "?ts (Suc i) = take i ts @ ts ! i # drop (Suc i) ss"
        unfolding take_Suc_conv_app_nth [OF i] by simp
      have ii: "?ts i = take i ts @ ss ! i # drop (Suc i) ss"
        unfolding nth_drop' [OF i [unfolded len[symmetric]]] ..
      from i have i': "length (take i ts) < length ts"  and len': "length (take i ts) = i" by auto
      from len i have len'': "length ts = Suc (length (take i ts) + length (drop (Suc i) ss))" by simp
      from *[OF args [OF i'] len''] and IH
        show ?case unfolding si ii len' by auto
    qed
  qed
  from this [THEN spec, THEN mp[OF _ le_refl]]
  show ?thesis using len by auto
qed

lemma args_steps_imp_steps:
  assumes len: "length ss = length ts"
    and args: "\<forall>i<length ss. (tree_hembeq P)\<^sup>=\<^sup>= (ss ! i) (ts ! i)"
  shows "(tree_hembeq P)\<^sup>*\<^sup>* (mk f ss) (mk f ts)" (is "?P (mk f ss) (mk f ts)")
proof (rule args_steps_imp_steps_gen[OF _ len])
  fix i
  assume "i < length ts" thus "?P (ss ! i) (ts ! i)" using args and len by auto
qed auto

lemma reflp_on_tree_hembeq:
  "reflp_on (tree_hembeq P) (trees A)"
proof
  fix t
  assume "t \<in> trees A"
  thus "tree_hembeq P t t"
  proof (induct t)
    case (mk x ts)
    hence "\<forall>t \<in> set ts. tree_hembeq P t t"
      and "x \<in> A" by (auto simp: trees_def)
    from list_hembeq_refl
      have *: "list_hembeq (tree_hembeq P) ts ts" by (auto simp: reflp_on_def)
    moreover have "P\<^sup>=\<^sup>= x x" by simp
    ultimately show ?case by auto
  qed
qed

lemma tree_hembeq_tranclp [simp]:
  "(tree_hembeq P)\<^sup>+\<^sup>+ = tree_hembeq P" (is "?l = ?r")
proof (intro ext)
  fix s t
  {
    assume "?l s t"
    then have "?r s t"
      by (induct s t) blast+
  }
  then show "?l s t = ?r s t" by auto
qed

lemma tree_hembeq_rtranclp [simp]:
  assumes "s \<in> trees A" and "t \<in> trees A"
  shows "(tree_hembeq P)\<^sup>*\<^sup>* s t = tree_hembeq P s t" (is "?l = ?r")
proof -
  {
    assume "?l"
    then have "?r" using assms
      by (induct)
         (insert reflp_on_tree_hembeq, auto simp: reflclp_tranclp [symmetric] reflp_on_def)
  }
  then show "?l = ?r" by auto
qed

lemma tree_hembeq_list_hembeq:
  assumes "P\<^sup>=\<^sup>= f g" and "list_hembeq (tree_hembeq P) ss ts"
  shows "tree_hembeq P (mk f ss) (mk g ts)"
proof -
  from list_hembeq_tree_hembeq_imp_sublisteq [OF assms(2)]
    obtain us where "sublisteq us ts" and "length ss = length us"
    and *: "\<forall>i<length ss. (tree_hembeq P)\<^sup>=\<^sup>= (ss ! i) (us ! i)" by auto
  with args_steps_imp_steps have "(tree_hembeq P)\<^sup>*\<^sup>* (mk f ss) (mk f us)" by auto
  moreover from `P\<^sup>=\<^sup>= f g` and `sublisteq us ts` have "tree_hembeq P (mk f us) (mk g ts)" by blast
  ultimately have "(tree_hembeq P)\<^sup>+\<^sup>+ (mk f ss) (mk g ts)" by (rule rtranclp_into_tranclp1)
  then show ?thesis by simp
qed

lemma tree_hembeq_subtreeeq:
  assumes "tree_hembeq P s t" and "subtreeeq t u" shows "tree_hembeq P s u"
  using assms and tree_hembeq_subtree by auto

inductive_set
  terms :: "('b \<times> nat) set \<Rightarrow> 'a set"
  for F :: "('b \<times> nat) set"
where
  mk [intro]: "(f, n) \<in> F \<Longrightarrow> length ts = n \<Longrightarrow> \<forall>t\<in>set ts. t \<in> terms F \<Longrightarrow> mk f ts \<in> terms F"

lemma terms_imp_trees:
  assumes "t \<in> terms F" shows "t \<in> trees (fst ` F)"
  using assms
  by (induct, auto intro: trees_list_intro) (metis fst_conv imageI)

lemma mk_terms:
  assumes "mk f ts \<in> terms F" shows "(f, length ts) \<in> F \<and> (\<forall>t\<in>set ts. t \<in> terms F)"
  using assms by (cases) (auto simp: inject)
  
lemma mk_terms_iff:
  "mk f ts \<in> terms F \<longleftrightarrow> (f, length ts) \<in> F \<and> (\<forall>t\<in>set ts. t \<in> terms F)" (is "?l = ?r")
  by (auto dest: mk_terms)

lemma in_set_size:
  "mk f ts \<in> terms F \<Longrightarrow> t \<in> set ts \<Longrightarrow> size t < size (mk f ts)"
  by (auto dest: terms_imp_trees intro: subtree_size)

lemma in_set_size':
  "(f, length ts) \<in> F \<Longrightarrow> \<forall>t\<in>set ts. t \<in> terms F \<Longrightarrow> t \<in> set ts \<Longrightarrow> size t \<le> size (mk f ts)"
  by  (intro less_imp_le in_set_size) auto

lemma mk_size:
  "mk f ts \<in> terms F \<Longrightarrow> size (mk f ts) = Suc (list_size size ts)"
  by (auto intro: size_simps dest!: terms_imp_trees)

lemma mk_size' [simp]:
  "(f, length ts) \<in> F \<Longrightarrow> \<forall>t\<in>set ts. t \<in> terms F \<Longrightarrow> size (mk f ts) = Suc (list_size size ts)"
  by (rule mk_size) auto

lemma subtree_terms:
  assumes "subtree s t" and "t \<in> terms F" shows "s \<in> terms F"
  using assms by (induct) (auto iff: mk_terms_iff)

lemma subtreeeq_terms:
  assumes "subtreeeq s t" and "t \<in> terms F" shows "s \<in> terms F"
  using assms and subtree_terms by auto

lemma wfp_on_subtree_terms:
  "wfp_on subtree (terms F)"
  apply (rule wfp_on_mono [of _ "trees (fst ` F)" _ subtree])
  apply (rule subsetI [OF terms_imp_trees])
  apply (assumption)
  apply (assumption)
  apply (rule wfp_on_subtree)
done

lemma sublisteq_set_subset:
  assumes "sublisteq xs ys"
  shows "set xs \<subseteq> set ys"
  using assms by (induct) auto

lemma args_steps_imp_steps_gen_terms:
  assumes ctxt: "\<And>s t ss1 ss2. (f, Suc (length (ss1@ss2))) \<in> F \<Longrightarrow>
    \<forall>t\<in>set (ss1@ss2). t \<in> terms F \<Longrightarrow>
    r (length ss1) s t \<Longrightarrow>
    length ts = Suc (length ss1 + length ss2) \<Longrightarrow>
    R\<^sup>*\<^sup>* (mk f (ss1 @ s # ss2)) (mk f (ss1 @ t # ss2))"
    and F: "(f, length ss) \<in> F"
    and terms: "\<forall>t\<in>set (ss@ts). t \<in> terms F"
    and len: "length ss = length ts"
    and args: "\<And>i. i < length ts \<Longrightarrow> (r i)\<^sup>*\<^sup>* (ss ! i) (ts ! i)"
  shows "R\<^sup>*\<^sup>* (mk f ss) (mk f ts)"
proof -
  let ?ts = "\<lambda>i. take i ts @ drop i ss"
  {
    fix s t and ss1 ss2 :: "'a list"
    assume "(r (length ss1))\<^sup>*\<^sup>* s t"
      and F: "(f, Suc (length (ss1@ss2))) \<in> F"
      and terms: "\<forall>t\<in>set (ss1@ss2). t \<in> terms F"
      and len: "length ts = Suc (length ss1 + length ss2)"
    then have "R\<^sup>*\<^sup>* (mk f (ss1 @ s # ss2)) (mk f (ss1 @ t # ss2))"
    proof (induct)
      case (step t u)
      from step(3) [OF step(4) step(5) len]
        and ctxt [OF step(4) step(5) step(2) len]
        show ?case by auto
    qed simp
  }
  note * = this
  have **: "\<forall>i\<le>length ts. R\<^sup>*\<^sup>* (mk f ss) (mk f (?ts i))"
  proof (intro allI impI)
    fix i assume "i \<le> length ts"
    then show "R\<^sup>*\<^sup>* (mk f ss) (mk f (?ts i))"
    proof (induct i)
      case 0
      then show ?case by simp
    next
      case (Suc i)
      then have IH: "R\<^sup>*\<^sup>* (mk f ss) (mk f (?ts i))"
        and i: "i < length ts" by auto
      have si: "?ts (Suc i) = take i ts @ ts ! i # drop (Suc i) ss"
        unfolding take_Suc_conv_app_nth [OF i] by simp
      have ii: "?ts i = take i ts @ ss ! i # drop (Suc i) ss"
        unfolding nth_drop' [OF i [unfolded len [symmetric]]] ..
      from i have i': "length (take i ts) < length ts"  and len': "length (take i ts) = i" by auto
      from len i have len'': "length ts = Suc (length (take i ts) + length (drop (Suc i) ss))" by simp
      have **: "Suc (length (take i ts @ drop (Suc i) ss)) = length ss"
        using len and `i < length ts` by simp
      have ***: "\<forall>t\<in>set (take i ts @ drop (Suc i) ss). t \<in> terms F"
        using terms and `i < length ts` and len by (auto dest: in_set_takeD in_set_dropD)
      from * [OF args[OF i'] _ _ len''] and IH and F and ***
        show ?case unfolding si ii len' ** by auto
    qed
  qed
  from this [THEN spec, THEN mp[OF _ le_refl]]
  show ?thesis using len by auto
qed

end

end

