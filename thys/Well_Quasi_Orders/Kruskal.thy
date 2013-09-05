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

(*TODO: move*)
lemma list_hembeq_singleton [simp]:
  assumes "reflp_on P A" and "y \<in> A"
  shows "list_hembeq P [x] [y] = P x y"
  using assms by (auto simp: reflp_on_def elim!: list_hembeq.cases)

context finite_tree
begin


subsection {* Kruskal's Tree Theorem *}

lemma almost_full_on_trees:
  assumes "almost_full_on P A"
  shows "almost_full_on (tree_hembeq P) (trees A)"
proof (rule ccontr)
  let ?A = "trees A"
  let ?P = "tree_hembeq P"
  interpret tree_mbs: mbs subtree ?A
  proof -
    show "mbs subtree ?A"
      by (unfold_locales)
         (force simp: wfp_on_subtree intro: subtree_trans)+
  qed
  note refl = reflp_on_tree_hembeq [of P A]
  
  assume "\<not> ?thesis"
  then obtain f where "\<forall>i. f i \<in> trees A" and "bad ?P f"
    unfolding almost_full_on_def by blast
  from tree_mbs.mbs [OF this] obtain m where bad: "bad ?P m"
    and mb: "\<And>n. mbs.min_at subtree ?A ?P m n"
    and in_trees: "\<And>i. m i \<in> trees A"
    by blast
  obtain r s where [simp]: "\<And>i. r i = root (m i)" "\<And>i. s i = succs (m i)" by force
  have [simp]: "\<And>i. mk (root (m i)) (succs (m i)) = m i" by (metis in_trees root_succs)

  {
    assume "\<exists>t \<phi>::nat seq. (\<forall>i. t i \<in> set (s (\<phi> i)) \<and> \<phi> i \<ge> \<phi> 0) \<and> bad ?P t"
    then obtain t and \<phi> :: "nat seq"
      where in_succs: "\<And>i. t i \<in> set (s (\<phi> i))"
      and ge: "\<And>i. \<phi> i \<ge> \<phi> 0"
      and "bad ?P t" by auto
    let ?n = "\<phi> 0"
    def c \<equiv> "\<lambda>i. if i < ?n then m i else t (i - ?n)"
    have [simp]: "\<And>i. i < ?n \<Longrightarrow> c i = m i" by (auto simp: c_def)
    have [simp]: "\<And>i. ?n \<le> i \<Longrightarrow> c i = t (i - ?n)" by (auto simp: c_def)
    have "bad ?P c"
    proof
      assume "good ?P c"
      then obtain i j where "i < j" and *: "?P (c i) (c j)" by (auto simp: good_def)
      {
        assume "j < ?n" with `i < j` and * have "?P (m i) (m j)" by simp
        with `i < j` and `bad ?P m` have False by (auto simp: good_def)
      } moreover {
        let ?i' = "i - ?n" and ?j' = "j - ?n"
        assume "?n \<le> i" with `i < j` and * have "?P (t ?i') (t ?j')" by simp
        moreover with `i < j` and `?n \<le> i` have "?i' < ?j'" by auto
        ultimately have False using `bad ?P t` by (auto simp: good_def)
      } moreover {
        let ?j' = "j - ?n"
        from in_succs have "t ?j' \<in> set (s (\<phi> ?j'))" by simp
        with in_succs_imp_subtree [OF in_trees]
          have subtree: "subtreeeq (t ?j') (m (\<phi> ?j'))" by auto
        assume "i < ?n" and "?n \<le> j"
        with * have "?P (m i) (t ?j')" by auto
        with subtree have "?P (m i) (m (\<phi> ?j'))" using tree_hembeq_subtreeeq [of P] by blast
        moreover from ge [of "?j'"] and `i < ?n` have "i < \<phi> ?j'" by auto
        ultimately have False using `bad ?P m` by (auto simp: good_def)
      } ultimately show False by arith
    qed
    have "\<forall>i. c i \<in> trees A"
      using in_trees
      by (simp add: c_def)
         (metis `\<And>i. s i = succs (m i)` in_succs in_succs_imp_subtree subtree_trees)
    moreover have "\<forall>i<?n. c i = m i" by simp
    moreover have "subtree (c ?n) (m ?n)"
      using in_succs_imp_subtree [OF in_trees] and in_succs by simp
    ultimately have "good ?P c"
      using mb [of ?n, unfolded tree_mbs.min_at_def, rule_format] by simp
    with `bad ?P c` have False by blast
  }
  hence no_special_bad_seq: "\<not> (\<exists>t \<phi>. (\<forall>i. t i \<in> set (s (\<phi> i)) \<and> \<phi> 0 \<le> \<phi> i) \<and> bad ?P t)" by blast

  let ?R = "{r i | i. True}"
  let ?S = "{s i | i. True}"
  have "almost_full_on P ?R"
  proof -
    have "?R \<subseteq> A"
    proof
      fix x assume "x \<in> ?R"
      then obtain i where [simp]: "x = r i" by auto
      from in_trees [of i] show "x \<in> A" by (cases "m i") (simp)
    qed
    from almost_full_on_subset [OF this assms] show ?thesis .
  qed
  moreover have "almost_full_on (list_hembeq ?P) ?S"
  proof -
    let ?S' = "\<Union>(set ` ?S)"
    have "almost_full_on ?P ?S'"
    proof
      have "?S' \<subseteq> trees A"
      proof
        fix x assume "x \<in> ?S'"
        then obtain i where "x \<in> set (s i)" by auto
        with in_succs_imp_subtree [OF in_trees]
          have "subtreeeq x (m i)" by auto
        with in_trees [of i] show "x \<in> trees A"
          using subtreeeq_trees by blast
      qed
      from reflp_on_subset [OF this refl] have refl: "reflp_on ?P ?S'" .
      fix f :: "'a seq" assume "\<forall>i. f i \<in> ?S'"
      with bad_of_special_shape' [OF refl this] and no_special_bad_seq
        show "good ?P f" by blast
    qed
    moreover have "?S \<subseteq> lists ?S'" by auto
    ultimately show ?thesis
      using almost_full_on_lists [of ?P ?S']
        and almost_full_on_subset [of ?S "lists ?S'"]
        by blast
  qed
  ultimately
  have "almost_full_on (prod_le P (list_hembeq ?P)) (?R \<times> ?S)"
    by (rule almost_full_on_Sigma)
  moreover have "\<forall>i. (r i, s i) \<in> (?R \<times> ?S)" by auto
  ultimately have "good (prod_le P (list_hembeq ?P)) (\<lambda>i. (r i, s i))"
    by (auto simp: almost_full_on_def)
  then obtain i j where "i < j"
    and "prod_le P (list_hembeq ?P) (r i, s i) (r j, s j)"
    by (auto simp: good_def almost_full_on_def)
  then have "P\<^sup>=\<^sup>= (r i) (r j)" and "list_hembeq ?P (s i) (s j)"
    by (auto simp: prod_le_def)
  from tree_hembeq_list_hembeq [OF this]
    have "?P (m i) (m j)" by auto
  with `i < j` and `bad ?P m` show False by (auto simp: good_def)
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

lemmas kruskal = wqo_on_trees

end

end

