theory Finite_Tree
imports Well_Quasi_Orders
begin

locale finite_tree =
  fixes mk :: "'b \<Rightarrow> 'a list \<Rightarrow> 'a"
    and root :: "'a \<Rightarrow> 'b"
    and succs :: "'a \<Rightarrow> 'a list"
  assumes inject: "mk x ts = mk x' ts' \<longleftrightarrow> x = x' \<and> ts = ts'"
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

lemma list_rec_set_ConsD:
  assumes "(t # ts, x) \<in> list_rec_set f g h"
  shows "\<exists>y z. (t, y) \<in> rec_set f g h \<and> (ts, z) \<in> list_rec_set f g h \<and>
    x = h t ts y z"
  using assms
  by (cases rule: list_rec_set.cases) auto

lemma functional:
  shows "t \<in> trees A \<Longrightarrow> \<exists>!y. (t, y) \<in> rec_set f g h"
    and "ts \<in> trees_list A \<Longrightarrow> \<exists>!y. (ts, y) \<in> list_rec_set f g h"
apply (induct t and ts rule: trees_trees_list.inducts)
apply (auto intro: rec_set_list_rec_set.intros)
apply (metis rec_set.simps root_mk succs_mk trees_trees_list.intros(2))
apply (metis list.simps(3) list_rec_set.simps)
by (metis list_rec_set_ConsD)

definition
  rec ::
    "('b \<Rightarrow> 'a list \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow>
      'c \<Rightarrow>
     ('a \<Rightarrow> 'a list \<Rightarrow> 'd \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow>
     'a \<Rightarrow>
     'd"
where
  "rec f g h t \<equiv> THE y. (t, y) \<in> rec_set f g h"

definition
  list_rec ::
    "('b \<Rightarrow> 'a list \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow>
      'c \<Rightarrow>
      ('a \<Rightarrow> 'a list \<Rightarrow> 'd \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow>
      'a list \<Rightarrow>
      'c"
where
  "list_rec f g h ts \<equiv> THE y. (ts, y) \<in> list_rec_set f g h"

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

definition "nodes \<equiv>
  rec (\<lambda>x ts N. {x} \<union> N) ({}) (\<lambda>t ts M N. M \<union> N)"

definition "nodes_list \<equiv>
  list_rec (\<lambda>x ts N. {x} \<union> N) {} (\<lambda>t ts M N. M \<union> N)"

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

lemma nodes:
  "x \<in> A \<Longrightarrow> ts \<in> trees_list A \<Longrightarrow> nodes (mk x ts) = {x} \<union> nodes_list ts"
  "nodes_list [] = {}"
  "t \<in> trees A \<Longrightarrow> ts \<in> trees_list A \<Longrightarrow> nodes_list (t # ts) = nodes t \<union> nodes_list ts"
  by (simp_all add: nodes_def nodes_list_def)

lemma nodes_simps [simp]:
  "x \<in> A \<Longrightarrow> ts \<in> trees_list A \<Longrightarrow>
    nodes (mk x ts) = {x} \<union> \<Union>set (map nodes ts)"
  by (induct ts) (auto simp: nodes)

inductive
  subtree :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  base: "t \<in> set ts \<Longrightarrow> subtree t (mk x ts)" |
  step: "subtree s t \<Longrightarrow> t \<in> set ts \<Longrightarrow> subtree s (mk x ts)"

lemma emb_mono:
  assumes "\<And>s t. P s t \<longrightarrow> Q s t"
  shows "emb P s t \<longrightarrow> emb Q s t"
proof
  assume "emb P s t" thus "emb Q s t"
    by (induct) (auto simp: assms)
qed

lemma reflclp_mono:
  assumes "\<And>s t. P s t \<longrightarrow> Q s t"
  shows "P\<^sup>=\<^sup>= s t \<longrightarrow> Q\<^sup>=\<^sup>= s t"
  using assms by auto

text {*Homeomorphic embedding on trees.*}
inductive
  hemb :: "('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  for P :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
where
  hemb_base [intro]: "t \<in> set ts \<Longrightarrow> hemb P t (mk f ts)" |
  hemb_emb [intro]: "P f g \<Longrightarrow> emb ((hemb P)\<^sup>=\<^sup>=) ss ts \<Longrightarrow> hemb P (mk f ss) (mk g ts)" |
  hemb_trans [intro]: "hemb P s t \<Longrightarrow> hemb P t u \<Longrightarrow> hemb P s u" |
  hemb_ctxt [intro]: "hemb P s t \<Longrightarrow> hemb P (mk f (ss1 @ s # ss2)) (mk f (ss1 @ t # ss2))"
monos emb_mono reflclp_mono

lemma hemb_subtree:
  assumes "hemb P s t" and "subtree t u" shows "hemb P s u"
  using assms(2, 1)
  by (induct rule: subtree.induct) auto

definition size :: "'a \<Rightarrow> nat" where
  "size \<equiv>
    rec (\<lambda>x ts n. n + Suc 0) 0 (\<lambda>t ts m n. m + n + Suc 0)"

definition size_list :: "'a list \<Rightarrow> nat" where
  "size_list \<equiv>
    list_rec (\<lambda>x ts n. n + Suc 0) 0 (\<lambda>t ts m n. m + n + Suc 0)"

lemma size:
  "x \<in> A \<Longrightarrow> ts \<in> trees_list A \<Longrightarrow> size (mk x ts) = size_list ts + Suc 0"
  "size_list [] = 0"
  "t \<in> trees A \<Longrightarrow> ts \<in> trees_list A \<Longrightarrow> size_list (t # ts) = size t + size_list ts + Suc 0"
  by (simp_all add: size_def size_list_def)

lemma size_simps [simp]:
  "x \<in> A \<Longrightarrow> ts \<in> trees_list A \<Longrightarrow>
    size (mk x ts) = list_size size ts + Suc 0"
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
    apply (rule wfp_on_mono [OF subset_refl, of "trees A" "subtree" ?P])
    apply (rule subtree_size [of _ _ A], assumption+)
    apply (insert *)
    apply assumption
  done
qed

lemma subtree_trans:
  assumes "subtree s t" and "subtree t u" shows "subtree s u"
  using assms(2, 1)
  by (induct rule: subtree.induct) (auto intro: subtree.intros)

lemma subtree_nodes_subset:
  assumes "subtree s t" and "t \<in> trees A" shows "nodes s \<subseteq> nodes t"
  using assms by (induct) force+

end

end
