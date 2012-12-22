(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Example Instance of Kruskal's Tree Theorem *}

theory Kruskal_Tree
imports Kruskal
begin

text {*A datatype of finite (non-empty) trees.*}
datatype 'a tree = Node 'a "'a tree list"

lemma
  assumes "\<And>x ss. (\<And>s. s \<in> set ss \<Longrightarrow> P s) \<Longrightarrow> P (Node x ss)"
  shows tree_induct [case_names Node, induct type: tree]: "P t"
    and "\<And>t. t \<in> set ts \<Longrightarrow> P t"
  using assms by (induct t and ts) auto

fun root :: "'a tree \<Rightarrow> 'a" where
  "root (Node x ts) = x"

fun args :: "'a tree \<Rightarrow> 'a tree list" where
  "args (Node x ts) = ts"

fun elts :: "'a tree \<Rightarrow> 'a set" where
  "elts (Node x ts) = {x} \<union> \<Union>set(map elts ts)"

definition trees where
  "trees A \<equiv> {t. elts t \<subseteq> A}"

lemma trees_UNIV [simp]:
  "trees UNIV = UNIV"
  by (auto simp: trees_def)

lemma trees_Node [iff]:
  "Node x ts \<in> trees A \<longleftrightarrow> x \<in> A \<and> (\<forall>t\<in>set ts. t \<in> trees A)"
  by (auto simp: trees_def)

interpretation tree_instance: finite_tree Node root args
  by (unfold_locales) auto

lemma trees_conv [simp]:
  "finite_tree.trees Node A = trees A" (is "?L = ?R")
proof
  show "?L \<subseteq> ?R"
  proof
    fix t assume "t \<in> ?L"
    then show "t \<in> ?R" by (induct) auto
  qed
next
  show "?R \<subseteq> ?L"
  proof
    fix t assume "t \<in> ?R"
    then show "t \<in> ?L"
      by (induct) (auto intro: tree_instance.trees_list_intro)
  qed
qed

abbreviation hembeq where
  "hembeq P \<equiv> tree_instance.tree_hembeq P"

lemma wqo_on_trees:
  assumes "wqo_on P A"
  shows "wqo_on (hembeq P) (trees A)"
  using tree_instance.wqo_on_trees [OF assms] by simp

end

