(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Kruskal's Tree Theorem *}

theory Kruskal
imports Well_Quasi_Orders
begin

text {*A datatype of finite (non-empty) trees.*}
datatype 'a tree = Node 'a "'a tree list"

lemma
  assumes "\<And>x ss. (\<And>s. s \<in> set ss \<Longrightarrow> P s) \<Longrightarrow> P (Node x ss)"
  shows tree_induct [case_names Node, induct type: tree]: "P t"
    and "\<And>t. t \<in> set ts \<Longrightarrow> P t"
  using assms by (induct t and ts) auto

fun elts :: "'a tree \<Rightarrow> 'a set" where
  "elts (Node x ts) = {x} \<union> \<Union>set(map elts ts)"

definition trees where
  "trees A \<equiv> {t. elts t \<subseteq> A}"

lemma trees_UNIV [simp]:
  "trees UNIV = UNIV"
  by (auto simp: trees_def)

inductive
  subtree :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> bool"
where
  base: "s \<in> set ss \<Longrightarrow> subtree s (Node x ss)" |
  step: "subtree s t \<Longrightarrow> t \<in> set ts \<Longrightarrow> subtree s (Node x ts)"

lemma emb_mono:
  assumes "\<And>x y. P x y \<longrightarrow> Q x y"
  shows "emb P s t \<longrightarrow> emb Q s t"
proof
  assume "emb P s t"
  thus "emb Q s t"
    by (induct) (auto simp: assms)
qed

text {*Homomorphic embedding on trees.*}
inductive
  hemb :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a tree \<Rightarrow> 'a tree \<Rightarrow> bool"
  for P :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  hemb_base [intro]: "t \<in> set ts \<Longrightarrow> hemb P s (Node f ts)" |
  hemb_emb [intro]: "P f g \<Longrightarrow> emb (hemb P) ss ts \<Longrightarrow> hemb P (Node f ss) (Node g ts)" |
  hemb_trans [intro]: "hemb P s t \<Longrightarrow> hemb P t u \<Longrightarrow> hemb P u v"
monos emb_mono

abbreviation subtreeeq where "subtreeeq \<equiv> subtree\<^sup>=\<^sup>="

lemma subtree_NodeE:
  assumes "subtree s (Node x ts)"
  obtains t where "t \<in> set ts" and "subtreeeq s t"
  using assms by (cases) auto

lemma subtree_trans:
  assumes "subtree s t" and "subtree t u" shows "subtree s u"
  using assms(2, 1)
  by (induct rule: subtree.induct) (auto intro: subtree.intros)

lemma hemb_subtree:
  assumes "hemb P s t" and "subtree t u" shows "hemb P s u"
  using assms(2, 1)
  by (induct rule: subtree.induct) auto

lemma subtree_imp_hemb:
  assumes "subtree s t" shows "hemb P s t"
  using assms by (induct) auto

lemma subtreeeq_trans:
  "subtreeeq s t \<Longrightarrow> subtreeeq t u \<Longrightarrow> subtreeeq s u"
  using subtree_trans [of s t u] by auto

lemma size_simp1:
  "s \<in> set ss \<Longrightarrow> subtree t s \<Longrightarrow> size t < size s \<Longrightarrow> size t < Suc (list_size size ss)"
  by (induct ss) auto

lemma size_simp2: "t \<in> set ts \<Longrightarrow> size t < Suc (list_size size ts)"
  by (induct ts) auto

lemmas size_simps = size_simp1 size_simp2

lemma subtree_size: "subtree t s \<Longrightarrow> size t < size s"
  by (induct rule: subtree.induct) (auto simp: size_simps)

lemma wf_subtree: "wf {(x, y). subtree x y}"
  by (rule wf_subset) (auto intro: subtree_size)

lemma subtreeeq_elts_subset:
  assumes "subtreeeq s t" shows "elts s \<subseteq> elts t"
using assms
proof
  assume "s = t" thus ?thesis by auto
next
  assume "subtree s t" thus ?thesis
    by (induct rule: subtree.induct) auto
qed

lemma hemb_subtreeeq:
  assumes "hemb P s t" and "subtreeeq t u" shows "hemb P s u"
  using assms and hemb_subtree by auto

interpretation tree_mbs: mbs hemb subtree trees elts
apply (unfold_locales)
unfolding suffix_reflclp_conv
apply (simp add: hemb_subtreeeq)
apply (simp add: wf_subtree)
apply (metis subtreeeq_trans)
apply (simp add: subtreeeq_elts_subset)
apply (simp add: trees_def)
done

lemma reflp_on_hemb:
  assumes "reflp_on P A"
  shows "reflp_on (hemb P) (trees A)"
proof
  fix t
  assume "t \<in> trees A"
  thus "hemb P t t"
  proof (induct t)
    case (Node x ts)
    hence "\<forall>t\<in>set ts. hemb P t t" and "x \<in> A" by (auto simp: trees_def)
    hence "reflp_on (hemb P) (set ts)" by (auto simp: reflp_on_def)
    from reflp_on_emb [OF this] have "emb (hemb P) ts ts" by (auto simp: reflp_on_def)
    moreover from assms and `x \<in> A` have "P x x" by (auto simp: reflp_on_def)
    ultimately show ?case by auto
  qed
qed

fun root :: "'a tree \<Rightarrow> 'a" where
  "root (Node x ts) = x"

fun args :: "'a tree \<Rightarrow> 'a tree list" where
  "args (Node x ts) = ts"

lemma in_args_imp_subtree: "s \<in> set (args t) \<Longrightarrow> subtree s t"
  by (cases t) (auto intro: subtree.intros)

lemma Node_root_args:
  "Node (root t) (args t) = t"
  by (cases t) auto

lemma no_bad_of_special_shape_imp_goodp':
  assumes "\<not> (\<exists>R f::nat seq. (\<forall>i. R i \<in> set (B (f i)) \<and> f 0 \<le> f i) \<and> bad P R)"
    and refl: "reflp_on P {x. \<exists>i. x \<in> set (B i)}"
    and elts: "\<forall>i. f i \<in> {x. \<exists>i. x \<in> set (B i)}"
  shows "goodp P f"
proof (rule ccontr)
  let ?B = "\<lambda>i. set (B i)"
  assume "bad P f"
  from elts have "\<forall>i. \<exists>j. f i \<in> ?B j" by auto
  from choice [OF this] obtain g where B: "\<forall>i. f i \<in> ?B (g i)" by auto
  have "\<forall>i. \<exists>j>i. g 0 \<le> g j"
  proof (rule ccontr)
    assume "\<not> (\<forall>i. \<exists>j>i. g 0 \<le> g j)"
    then obtain i where *: "\<forall>j>i. g j < g 0" by force
    let ?I = "{j. j > i}"
    have "g ` ?I \<subseteq> {..<g 0}"
      using * unfolding image_subset_iff by (metis lessThan_iff mem_Collect_eq)
    moreover have "finite {..<g 0}" by auto
    ultimately have 1: "finite (g ` ?I)" using finite_subset by blast
    have 2: "infinite ?I" by (rule infinite_wo_prefix)
    from pigeonhole_infinite [OF 2 1]
      obtain k where "k > i" and 3: "infinite {j. j > i \<and> g j = g k}" by auto
    from this [unfolded infinite_nat_iff_unbounded]
      have "\<forall>m. \<exists>n>m. n > i \<and> g n = g k" by auto
    from choice [OF this] obtain h where
      **: "\<forall>m. h m > m \<and> h m > i \<and> g (h m) = g k" by auto
    let ?g = "g \<circ> h"
    let ?h = "\<lambda>i. (h ^^ Suc i) 0"
    from B have "\<forall>i. f (?h i) \<in> ?B ((g \<circ> ?h) i)" by auto
    with ** have "\<forall>i. f (?h i) \<in> ?B (g k)" by simp
    with pigeonhole_infinite_rel [of "UNIV::nat set" "?B (g k)" "\<lambda>a b. f (?h a) = b"]
      obtain x where "x \<in> ?B (g k)" and "infinite {a. f (?h a) = x}" by auto
    hence all: "\<forall>m. \<exists>n>m. f (?h n) = x" unfolding infinite_nat_iff_unbounded by auto
    from all obtain u where u: "f (?h u) = x" by auto
    from all obtain v where "v > u" and v: "f (?h v) = x" by auto

    from ** have "\<forall>i\<ge>0. h i > i" by auto
    from funpow_mono [OF this] have ***: "\<And>i j. i < j \<Longrightarrow> ?h i < ?h j" by best
    from this [OF `v > u`] have "?h u < ?h v" .
    moreover have "P (f (?h u)) (f (?h v))"
    proof -
      from refl and `x \<in> ?B (g k)` have "P x x" by (auto simp: reflp_on_def)
      thus ?thesis unfolding u v .
    qed
    ultimately show False using `bad P f` by (auto simp: goodp_def)
  qed
  from choice[OF this] obtain h
    where "\<forall>i. (h i) > i" and *: "\<And>i. g (h i) \<ge> g 0" by blast
  hence "\<forall>i\<ge>0. (h i) > i" by auto
  from funpow_mono[OF this] have **: "\<And>i j. i < j \<Longrightarrow> (h ^^ i) 0 < (h ^^ j) 0" by auto
  let ?i = "\<lambda>i. (h ^^ i) 0"
  let ?f = "\<lambda>i. g (?i i)"
  let ?R = "\<lambda>i. f (?i i)"
  have "\<forall>i. ?R i \<in> ?B (?f i)" using B by auto
  moreover have "\<forall>i. ?f i \<ge> ?f 0"
  proof
    fix i show "?f i \<ge> ?f 0" using * by (induct i) auto
  qed
  moreover have "bad P ?R"
  proof
    assume "goodp P ?R"
    then obtain i j where "i < j" and "P (?R i) (?R j)" by (auto simp: goodp_def)
    hence "P (f (?i i)) (f (?i j))" by simp
    moreover from **[OF `i < j`] have "?i i < ?i j" .
    ultimately show False using `bad P f` by (auto simp: goodp_def)
  qed
  ultimately have "(\<forall>i. ?R i \<in> ?B (?f i) \<and> ?f i \<ge> ?f 0) \<and> bad P ?R" by auto
  hence "\<exists>f. (\<forall>i. ?R i \<in> ?B (f i) \<and> f i \<ge> f 0) \<and> bad P ?R" by auto
  hence "\<exists>R f. (\<forall>i. R i \<in> ?B (f i) \<and> f i \<ge> f 0) \<and> bad P R" by metis
  with assms(1) show False by blast
qed


subsection {* Kruskal's Tree Theorem *}

lemma almost_full_on_trees:
  assumes "almost_full_on P A"
  shows "almost_full_on (hemb P) (trees A)"
    (is "almost_full_on ?P ?A")
proof -
  { from reflp_on_hemb [OF almost_full_on_imp_reflp_on [OF assms]] have "reflp_on ?P ?A" . }
  note refl = this
  {
    have "\<forall>f. (\<forall>i. f i \<in> ?A) \<longrightarrow> goodp ?P f"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain f where "\<forall>i. f i \<in> trees A" and "bad ?P f" by blast
      from tree_mbs.mbs [OF this] obtain m where
        bad: "bad ?P m" and
        mb: "\<And>n. mbs.min_at hemb subtree P m n" and
        in_trees: "\<And>i. m i \<in> trees A"
        by blast
      let ?A = m
      obtain a as where a: "\<forall>i. root (?A i) = a i \<and> args (?A i) = as i" by force
      let ?B = "\<lambda>i. set (args (?A i))"
      {
        assume "\<exists>R f::nat seq. (\<forall>i. R i \<in> ?B (f i) \<and> f i \<ge> f 0) \<and> bad ?P R"
        then obtain R and f :: "nat seq"
          where in_args: "\<forall>i. R i \<in> ?B (f i)"
          and ge: "\<forall>i. f i \<ge> f 0"
          and "bad ?P R" by auto
        let ?C = "\<lambda>i. if i < f 0 then ?A i else R (i - f 0)"
        have [simp]: "\<And>i. i < f 0 \<Longrightarrow> ?C i = ?A i" by auto
        have [simp]: "\<And>i. f 0 \<le> i \<Longrightarrow> ?C i = R (i - f 0)" by auto
        have "bad ?P ?C"
        proof
          assume "goodp ?P ?C"
          then obtain i j where "i < j" and *: "?P (?C i) (?C j)" by (auto simp: goodp_def)
          {
            assume "j < f 0" with `i < j` and * have "?P (?A i) (?A j)" by simp
            with `i < j` and `bad ?P ?A` have False by (auto simp: goodp_def)
          } moreover {
            assume "f 0 \<le> i" with `i < j` and * have "?P (R (i - f 0)) (R (j - f 0))" by simp
            moreover with `i < j` and `f 0 \<le> i` have "i - (f 0) < j - (f 0)" by auto
            ultimately have False using `bad ?P R` by (auto simp: goodp_def)
          } moreover {
            let ?i = "j - f 0"
            from in_args have "R ?i \<in> ?B (f ?i)" by simp
            from in_args_imp_subtree [OF this]
              have subtree: "subtreeeq (R ?i) (?A (f ?i))" by auto
            assume "i < f 0" and "f 0 \<le> j"
            with * have "?P (?A i) (R ?i)" by auto
            with subtree have "?P (?A i) (?A (f ?i))" using hemb_subtreeeq [of P] by blast
            moreover from ge[THEN spec[of _ "?i"]] and `i < f 0` have "i < f ?i" by auto
            ultimately have False using `bad ?P ?A` by (auto simp: goodp_def)
          } ultimately show False by arith
        qed
        have "\<forall>i<f 0. ?C i = ?A i" by simp
        moreover have "subtree (?C (f 0)) (?A (f 0))"
          using in_args_imp_subtree [OF in_args [THEN spec [of _ 0]]] by simp
        moreover have "\<forall>i\<ge>f 0. \<exists>j\<ge>f 0. subtree\<^sup>=\<^sup>= (?C i) (?A j)"
        proof (intro allI impI)
          fix i
          let ?i = "i - f 0"
          assume "f 0 \<le> i"
          with `\<forall>i. f 0 \<le> f i` have "f 0 \<le> f ?i" by auto
          from `f 0 \<le> i` have "?C i = R ?i" by auto
          with in_args_imp_subtree [OF in_args [THEN spec [of _ ?i]]]
            have "subtree\<^sup>=\<^sup>= (?C i) (?A (f ?i))" by auto
          thus "\<exists>j\<ge>f 0. subtree\<^sup>=\<^sup>= (?C i) (?A j)" using `f 0 \<le> f ?i` by auto
        qed
        ultimately have "goodp ?P ?C"
          using mb [of "f 0", unfolded tree_mbs.min_at_def, rule_format] by simp
        with `bad ?P ?C` have False by blast
      }
      hence no_special_bad_seq: "\<not> (\<exists>R f. (\<forall>i. R i \<in> ?B (f i) \<and> f 0 \<le> f i) \<and> bad ?P R)" by blast
      let ?B' = "{x. \<exists>i. x \<in> ?B i}"
      have subset: "?B' \<subseteq> trees A"
      proof
        fix x assume "x \<in> ?B'"
        then obtain i where B: "x \<in> ?B i" by auto
        from in_args_imp_subtree [OF this]
          have "subtreeeq x (?A i)" by auto
        with in_trees [of i] show "x \<in> trees A"
          using subtreeeq_elts_subset by (auto simp add: trees_def)
      qed
      have "almost_full_on ?P ?B'"
      proof
        from reflp_on_subset[OF subset refl] have refl: "reflp_on ?P ?B'" .
        fix f :: "'a tree seq" assume "\<forall>i. f i \<in> ?B'"
        from no_bad_of_special_shape_imp_goodp' [OF no_special_bad_seq refl this]
          show "goodp ?P f" .
      qed
      let ?a' = "{a i | i. True}"
      have "?a' \<subseteq> A"
      proof
        fix x assume "x \<in> ?a'"
        then obtain i where x: "x = a i" by auto
        with a [THEN spec [of _ i]]
          have "a i \<in> elts (?A i)" by (cases "m i") auto
        with in_trees [of i] show "x \<in> A" unfolding x by (auto simp: trees_def)
      qed
      from almost_full_on_subset[OF this assms]
        have "almost_full_on P ?a'" .

      from almost_full_on_lists [OF `almost_full_on ?P ?B'`]
        have lists: "almost_full_on (emb ?P) (lists ?B')" .

      let ?args = "{args (?A i) | i. True}"
      have "?args \<subseteq> lists ?B'" by auto
      from almost_full_on_subset [OF this lists]
        have "almost_full_on (emb ?P) ?args" .

      let ?P' = "prod_le P (emb ?P)"

      from almost_full_on_Sigma[OF `almost_full_on P ?a'` `almost_full_on (emb ?P) ?args`]
        have af: "almost_full_on ?P' (?a' \<times> ?args)" .
      
      let ?aB = "\<lambda>i. (a i, args (?A i))"

      have "\<forall>i. ?aB i \<in> (?a' \<times> ?args)" by auto
      with af have "goodp ?P' ?aB" unfolding almost_full_on_def by auto
      then obtain i j where "i < j" and *: "?P' (?aB i) (?aB j)"
        by (auto simp: goodp_def almost_full_on_def)

      from Node_root_args
        have root_args: "Node (root (?A i)) (args (?A i)) = ?A i"
          "Node (root (?A j)) (args (?A j)) = ?A j" by force+

      from * have "P (a i) (a j)" and "emb ?P (args (?A i)) (args (?A j))"
        by (auto simp: prod_le_def)
      from hemb_emb [OF this]
        have "?P (?A i) (?A j)" using a and root_args by auto
      with `i < j` and `bad ?P ?A` show False by (auto simp: goodp_def almost_full_on_def)
    qed
  }
  with trans show ?thesis unfolding wqo_on_def almost_full_on_def by blast
qed

lemma wqo_on_trees:
  assumes "wqo_on P A"
  shows "wqo_on (hemb P) (trees A)"
proof
  from hemb_trans show "transp_on (hemb P) (trees A)"
    by (auto simp: transp_on_def)
next
  fix f
  assume *: "\<forall>i::nat. f i \<in> trees A"
  from assms have "almost_full_on P A" by (auto simp: wqo_on_def)
  from almost_full_on_trees [OF this]
    show "goodp (hemb P) f" using * by (auto simp: almost_full_on_def)
qed

end
