theory Kruskal
imports
  Well_Quasi_Orders
  Finite_Tree
begin

context finite_tree
begin

lemma no_bad_of_special_shape_imp_good':
  assumes "\<not> (\<exists>R f::nat seq. (\<forall>i. R i \<in> set (B (f i)) \<and> f 0 \<le> f i) \<and> bad P R)"
    and refl: "reflp_on P {x. \<exists>i. x \<in> set (B i)}"
    and elts: "\<forall>i. f i \<in> {x. \<exists>i. x \<in> set (B i)}"
  shows "good P f"
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
    ultimately show False using `bad P f` by (auto simp: good_def)
  qed
  from choice [OF this] obtain h
    where "\<forall>i. (h i) > i" and *: "\<And>i. g (h i) \<ge> g 0" by blast
  hence "\<forall>i\<ge>0. (h i) > i" by auto
  from funpow_mono [OF this] have **: "\<And>i j. i < j \<Longrightarrow> (h ^^ i) 0 < (h ^^ j) 0" by auto
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
    assume "good P ?R"
    then obtain i j where "i < j" and "P (?R i) (?R j)" by (auto simp: good_def)
    hence "P (f (?i i)) (f (?i j))" by simp
    moreover from ** [OF `i < j`] have "?i i < ?i j" .
    ultimately show False using `bad P f` by (auto simp: good_def)
  qed
  ultimately have "(\<forall>i. ?R i \<in> ?B (?f i) \<and> ?f i \<ge> ?f 0) \<and> bad P ?R" by auto
  hence "\<exists>f. (\<forall>i. ?R i \<in> ?B (f i) \<and> f i \<ge> f 0) \<and> bad P ?R" by auto
  hence "\<exists>R f. (\<forall>i. R i \<in> ?B (f i) \<and> f i \<ge> f 0) \<and> bad P R" by metis
  with assms(1) show False by blast
qed


subsection {* Kruskal's Tree Theorem *}

lemma almost_full_on_trees:
  assumes "almost_full_on P A"
  shows "almost_full_on (tree_hembeq P) (trees A)"
    (is "almost_full_on ?P ?A")
proof -
  interpret tree_mbs: mbs tree_hembeq subtree trees
  proof -
    show "mbs tree_hembeq subtree trees"
      by (unfold_locales) (force
        simp: tree_hembeq_subtree wfp_on_subtree
        intro: subtree_trans elim!: subtree_trees)+
  qed
  { from reflp_on_tree_hembeq have "reflp_on ?P ?A" . }
  note refl = this
  {
    have "\<forall>f. (\<forall>i. f i \<in> ?A) \<longrightarrow> good ?P f"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain f where "\<forall>i. f i \<in> trees A" and "bad ?P f" by blast
      from tree_mbs.mbs [OF this] obtain m where
        bad: "bad ?P m" and
        mb: "\<And>n. mbs.min_at tree_hembeq subtree P m n" and
        in_trees: "\<And>i. m i \<in> trees A"
        by blast
      let ?A = m
      obtain a as
        where a: "\<forall>i. root (?A i) = a i \<and> succs (?A i) = as i" by force
      let ?B = "\<lambda>i. set (succs (?A i))"
      {
        assume "\<exists>R f::nat seq. (\<forall>i. R i \<in> ?B (f i) \<and> f i \<ge> f 0) \<and> bad ?P R"
        then obtain R and f :: "nat seq"
          where in_succs: "\<forall>i. R i \<in> ?B (f i)"
          and ge: "\<forall>i. f i \<ge> f 0"
          and "bad ?P R" by auto
        let ?C = "\<lambda>i. if i < f 0 then ?A i else R (i - f 0)"
        have [simp]: "\<And>i. i < f 0 \<Longrightarrow> ?C i = ?A i" by auto
        have [simp]: "\<And>i. f 0 \<le> i \<Longrightarrow> ?C i = R (i - f 0)" by auto
        have "bad ?P ?C"
        proof
          assume "good ?P ?C"
          then obtain i j where "i < j" and *: "?P (?C i) (?C j)" by (auto simp: good_def)
          {
            assume "j < f 0" with `i < j` and * have "?P (?A i) (?A j)" by simp
            with `i < j` and `bad ?P ?A` have False by (auto simp: good_def)
          } moreover {
            assume "f 0 \<le> i" with `i < j` and * have "?P (R (i - f 0)) (R (j - f 0))" by simp
            moreover with `i < j` and `f 0 \<le> i` have "i - (f 0) < j - (f 0)" by auto
            ultimately have False using `bad ?P R` by (auto simp: good_def)
          } moreover {
            let ?i = "j - f 0"
            from in_succs have "R ?i \<in> ?B (f ?i)" by simp
            from in_succs_imp_subtree [OF in_trees this]
              have subtree: "subtreeeq (R ?i) (?A (f ?i))" by auto
            assume "i < f 0" and "f 0 \<le> j"
            with * have "?P (?A i) (R ?i)" by auto
            with subtree have "?P (?A i) (?A (f ?i))" using tree_hembeq_subtreeeq [of P] by blast
            moreover from ge [THEN spec [of _ "?i"]] and `i < f 0` have "i < f ?i" by auto
            ultimately have False using `bad ?P ?A` by (auto simp: good_def)
          } ultimately show False by arith
        qed
        have "\<forall>i<f 0. ?C i = ?A i" by simp
        moreover have "subtree (?C (f 0)) (?A (f 0))"
          using in_succs_imp_subtree [OF in_trees in_succs [THEN spec, of 0]] by simp
        moreover have "\<forall>i\<ge>f 0. \<exists>j\<ge>f 0. subtree\<^sup>=\<^sup>= (?C i) (?A j)"
        proof (intro allI impI)
          fix i
          let ?i = "i - f 0"
          assume "f 0 \<le> i"
          with `\<forall>i. f 0 \<le> f i` have "f 0 \<le> f ?i" by auto
          from `f 0 \<le> i` have "?C i = R ?i" by auto
          with in_succs_imp_subtree [OF in_trees in_succs [THEN spec [of _ ?i]]]
            have "subtree\<^sup>=\<^sup>= (?C i) (?A (f ?i))" by auto
          thus "\<exists>j\<ge>f 0. subtree\<^sup>=\<^sup>= (?C i) (?A j)" using `f 0 \<le> f ?i` by auto
        qed
        ultimately have "good ?P ?C"
          using mb [of "f 0", unfolded tree_mbs.min_at_def, rule_format] by simp
        with `bad ?P ?C` have False by blast
      }
      hence no_special_bad_seq: "\<not> (\<exists>R f. (\<forall>i. R i \<in> ?B (f i) \<and> f 0 \<le> f i) \<and> bad ?P R)" by blast
      let ?B' = "{x. \<exists>i. x \<in> ?B i}"
      have subset: "?B' \<subseteq> trees A"
      proof
        fix x assume "x \<in> ?B'"
        then obtain i where B: "x \<in> ?B i" by auto
        from in_succs_imp_subtree [OF in_trees this]
          have "subtreeeq x (?A i)" by auto
        with in_trees [of i] show "x \<in> trees A"
          using subtreeeq_trees by blast
      qed
      have "almost_full_on ?P ?B'"
      proof
        from reflp_on_subset [OF subset refl] have refl: "reflp_on ?P ?B'" .
        fix f :: "'a seq" assume "\<forall>i. f i \<in> ?B'"
        from no_bad_of_special_shape_imp_good' [OF no_special_bad_seq refl this]
          show "good ?P f" .
      qed
      let ?a' = "{a i | i. True}"
      have "?a' \<subseteq> A"
      proof
        fix x assume "x \<in> ?a'"
        then obtain i where x: "x = a i" by auto
        from in_trees [of i] and a [THEN spec [of _ i]]
          show "x \<in> A" by (cases "m i") (simp add: x)
      qed
      from almost_full_on_subset [OF this assms]
        have "almost_full_on P ?a'" .

      from almost_full_on_lists [OF `almost_full_on ?P ?B'`]
        have lists: "almost_full_on (list_hembeq ?P) (lists ?B')" .

      let ?succs = "{succs (?A i) | i. True}"
      have "?succs \<subseteq> lists ?B'" by auto
      from almost_full_on_subset [OF this lists]
        have "almost_full_on (list_hembeq ?P) ?succs" .

      let ?P' = "prod_le P (list_hembeq ?P)"

      from almost_full_on_Sigma [OF `almost_full_on P ?a'` `almost_full_on (list_hembeq ?P) ?succs`]
        have af: "almost_full_on ?P' (?a' \<times> ?succs)" .
      
      let ?aB = "\<lambda>i. (a i, succs (?A i))"

      have "\<forall>i. ?aB i \<in> (?a' \<times> ?succs)" by auto
      with af have "good ?P' ?aB" unfolding almost_full_on_def by auto
      then obtain i j where "i < j" and *: "?P' (?aB i) (?aB j)"
        by (auto simp: good_def almost_full_on_def)

      from root_succs and in_trees
        have root_succs: "mk (root (?A i)) (succs (?A i)) = ?A i"
          "mk (root (?A j)) (succs (?A j)) = ?A j" by force+

      from * have "P\<^sup>=\<^sup>= (a i) (a j)" and "list_hembeq ?P (succs (?A i)) (succs (?A j))"
        by (auto simp: prod_le_def)
      from tree_hembeq_list_hembeq [OF this]
        have "?P (?A i) (?A j)" using a and root_succs by auto
      with `i < j` and `bad ?P ?A` show False by (auto simp: good_def almost_full_on_def)
    qed
  }
  with trans show ?thesis unfolding almost_full_on_def by blast
qed

lemma wqo_on_trees:
  assumes "wqo_on P A"
  shows "wqo_on (tree_hembeq P) (trees A)"
proof
  from tree_hembeq_trans show "transp_on (tree_hembeq P) (trees A)"
    by (auto simp: transp_on_def)
next
  fix f
  assume *: "\<forall>i::nat. f i \<in> trees A"
  from assms have "almost_full_on P A" by (auto simp: wqo_on_def)
  from almost_full_on_trees [OF this]
    show "good (tree_hembeq P) f" using * by (auto simp: almost_full_on_def)
qed

end

end

