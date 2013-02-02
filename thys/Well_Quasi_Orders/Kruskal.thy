(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Kruskal's Tree Theorem -- Infinite Version for Trees (i.e., Variadic Terms) *}

theory Kruskal
imports
  Well_Quasi_Orders
  Finite_Tree
  Kruskal_Auxiliaries
begin

context finite_tree
begin


subsection {* Kruskal's Tree Theorem *}

lemma almost_full_on_trees:
  assumes "almost_full_on P A"
  shows "almost_full_on (tree_hembeq P) (trees A)"
    (is "almost_full_on ?P ?A")
proof (rule ccontr)
  interpret tree_mbs: mbs "\<lambda>_. ?P" subtree trees
  proof -
    show "mbs (\<lambda>_. ?P) subtree trees"
      by (unfold_locales) (force
        simp: tree_hembeq_subtree wfp_on_subtree
        intro: subtree_trans elim!: subtree_trees)+
  qed
  note refl = reflp_on_tree_hembeq [of P A]
  
  assume "\<not> ?thesis"
  then obtain f where "\<forall>i. f i \<in> trees A" and "bad ?P f"
    unfolding almost_full_on_def by blast
  from tree_mbs.mbs [OF this] obtain m where bad: "bad ?P m"
    and mb: "\<And>n. mbs.min_at (\<lambda>_. ?P) subtree A m n"
    and in_trees: "\<And>i. m i \<in> trees A"
    by blast
  obtain r s where [simp]: "\<And>i. r i = root (m i)" "\<And>i. s i = succs (m i)" by force
  have [simp]: "\<And>i. mk (root (m i)) (succs (m i)) = m i" by (metis in_trees root_succs)

  {
    assume "\<exists>R \<phi>::nat seq. (\<forall>i. R i \<in> set (s (\<phi> i)) \<and> \<phi> i \<ge> \<phi> 0) \<and> bad ?P R"
    then obtain R and \<phi> :: "nat seq"
      where in_succs: "\<forall>i. R i \<in> set (s (\<phi> i))"
      and ge: "\<forall>i. \<phi> i \<ge> \<phi> 0"
      and "bad ?P R" by auto
    let ?C = "\<lambda>i. if i < \<phi> 0 then m i else R (i - \<phi> 0)"
    have [simp]: "\<And>i. i < \<phi> 0 \<Longrightarrow> ?C i = m i" by auto
    have [simp]: "\<And>i. \<phi> 0 \<le> i \<Longrightarrow> ?C i = R (i - \<phi> 0)" by auto
    have "bad ?P ?C"
    proof
      assume "good ?P ?C"
      then obtain i j where "i < j" and *: "?P (?C i) (?C j)" by (auto simp: good_def)
      {
        assume "j < \<phi> 0" with `i < j` and * have "?P (m i) (m j)" by simp
        with `i < j` and `bad ?P m` have False by (auto simp: good_def)
      } moreover {
        assume "\<phi> 0 \<le> i" with `i < j` and * have "?P (R (i - \<phi> 0)) (R (j - \<phi> 0))" by simp
        moreover with `i < j` and `\<phi> 0 \<le> i` have "i - (\<phi> 0) < j - (\<phi> 0)" by auto
        ultimately have False using `bad ?P R` by (auto simp: good_def)
      } moreover {
        let ?i = "j - \<phi> 0"
        from in_succs have "R ?i \<in> set (s (\<phi> ?i))" by simp
        with in_succs_imp_subtree [OF in_trees]
          have subtree: "subtreeeq (R ?i) (m (\<phi> ?i))" by auto
        assume "i < \<phi> 0" and "\<phi> 0 \<le> j"
        with * have "?P (m i) (R ?i)" by auto
        with subtree have "?P (m i) (m (\<phi> ?i))" using tree_hembeq_subtreeeq [of P] by blast
        moreover from ge [THEN spec [of _ "?i"]] and `i < \<phi> 0` have "i < \<phi> ?i" by auto
        ultimately have False using `bad ?P m` by (auto simp: good_def)
      } ultimately show False by arith
    qed
    have "\<forall>i<\<phi> 0. ?C i = m i" by simp
    moreover have "subtree (?C (\<phi> 0)) (m (\<phi> 0))"
      using in_succs_imp_subtree [OF in_trees] and in_succs by simp
    moreover have "\<forall>i\<ge>\<phi> 0. \<exists>j\<ge>\<phi> 0. subtree\<^sup>=\<^sup>= (?C i) (m j)"
    proof (intro allI impI)
      fix i
      let ?i = "i - \<phi> 0"
      assume "\<phi> 0 \<le> i"
      with `\<forall>i. \<phi> 0 \<le> \<phi> i` have "\<phi> 0 \<le> \<phi> ?i" by auto
      from `\<phi> 0 \<le> i` have "?C i = R ?i" by auto
      with in_succs_imp_subtree [OF in_trees] and in_succs
        have "subtree\<^sup>=\<^sup>= (?C i) (m (\<phi> ?i))" by auto
      thus "\<exists>j\<ge>\<phi> 0. subtree\<^sup>=\<^sup>= (?C i) (m j)" using `\<phi> 0 \<le> \<phi> ?i` by auto
    qed
    ultimately have "good ?P ?C"
      using mb [of "\<phi> 0", unfolded tree_mbs.min_at_def, rule_format] by simp
    with `bad ?P ?C` have False by blast
  }
  hence no_special_bad_seq: "\<not> (\<exists>R \<phi>. (\<forall>i. R i \<in> set (s (\<phi> i)) \<and> \<phi> 0 \<le> \<phi> i) \<and> bad ?P R)" by blast

  let ?R = "{r i | i. True}"
  let ?S = "{x. \<exists>i. x \<in> set (s i)}"
  have subset: "?S \<subseteq> trees A"
  proof
    fix x assume "x \<in> ?S"
    then obtain i where B: "x \<in> set (s i)" by auto
    with in_succs_imp_subtree [OF in_trees]
      have "subtreeeq x (m i)" by auto
    with in_trees [of i] show "x \<in> trees A"
      using subtreeeq_trees by blast
  qed
  have "almost_full_on ?P ?S"
  proof
    from reflp_on_subset [OF subset refl] have refl: "reflp_on ?P ?S" .
    fix f :: "'a seq" assume "\<forall>i. f i \<in> ?S"
    from bad_of_special_shape' [OF refl this] and no_special_bad_seq
      show "good ?P f" by blast
  qed
  have "?R \<subseteq> A"
  proof
    fix x assume "x \<in> ?R"
    then obtain i where x: "x = r i" by auto
    from in_trees [of i]
      show "x \<in> A" by (cases "m i") (simp add: x)
  qed
  from almost_full_on_subset [OF this assms]
    have "almost_full_on P ?R" .

  from almost_full_on_lists [OF `almost_full_on ?P ?S`]
    have lists: "almost_full_on (list_hembeq ?P) (lists ?S)" .

  let ?succs = "{s i | i. True}"
  have "?succs \<subseteq> lists ?S" by auto
  from almost_full_on_subset [OF this lists]
    have "almost_full_on (list_hembeq ?P) ?succs" .

  let ?P' = "prod_le P (list_hembeq ?P)"

  from almost_full_on_Sigma [OF `almost_full_on P ?R` `almost_full_on (list_hembeq ?P) ?succs`]
    have af: "almost_full_on ?P' (?R \<times> ?succs)" .
  
  let ?aB = "\<lambda>i. (r i, succs (m i))"

  have "\<forall>i. ?aB i \<in> (?R \<times> ?succs)" by auto
  with af have "good ?P' ?aB" unfolding almost_full_on_def by auto
  then obtain i j where "i < j" and *: "?P' (?aB i) (?aB j)"
    by (auto simp: good_def almost_full_on_def)

  from root_succs and in_trees
    have root_succs: "mk (root (m i)) (succs (m i)) = m i"
      "mk (root (m j)) (succs (m j)) = m j" by force+

  from * have "P\<^sup>=\<^sup>= (r i) (r j)" and "list_hembeq ?P (succs (m i)) (succs (m j))"
    by (auto simp: prod_le_def)
  from tree_hembeq_list_hembeq [OF this]
    have "?P (m i) (m j)" using root_succs by auto
  with `i < j` and `bad ?P m` show False by (auto simp: good_def almost_full_on_def)
qed

lemma wqo_on_trees:
  assumes "wqo_on P A"
  shows "wqo_on (tree_hembeq P) (trees A)"
proof
  from tree_hembeq_trans show "transp_on (tree_hembeq P) (trees A)"
    by (auto simp: transp_on_def)
next
  from assms have "almost_full_on P A" by (auto simp: wqo_on_def)
  from almost_full_on_trees [OF this]
    show "almost_full_on (tree_hembeq P) (trees A)" .
qed

end

end

