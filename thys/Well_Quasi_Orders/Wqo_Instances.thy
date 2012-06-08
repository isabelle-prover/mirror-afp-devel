(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Instances of Well-Quasi-Orders *}

theory Wqo_Instances
imports
  Well_Quasi_Orders
  Kruskal
begin

subsection {* The Sum Type is Well-Quasi-Ordered *}

instantiation sum :: (wqo, wqo) wqo
begin
definition "x \<le> y \<longleftrightarrow> sum_le (op \<le>) (op \<le>) x y"
definition "(x :: 'a + 'b) < y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)"

instance proof (rule wqo_class.intro)
  have 1: "wqo_on (op \<le>) (UNIV :: 'a set)"
    using order_trans and good
    by (auto simp: wqo_on_UNIV_conv class.wqo_def class.wqo_axioms_def class.preorder_def)
  have 2: "wqo_on (op \<le>) (UNIV :: 'b set)"
    using order_trans and good
    by (auto simp: wqo_on_UNIV_conv class.wqo_def class.wqo_axioms_def class.preorder_def)
  from wqo_on_Plus [OF 1 2]
    have wqo: "wqo_on (op \<le>) (UNIV :: ('a + 'b) set)"
      by (auto simp: less_eq_sum_def [abs_def])  
  hence "class.wqo (op \<le> :: 'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool) (op <)"
    unfolding wqo_on_UNIV_conv less_sum_def [abs_def] .
  thus "class.wqo_axioms (op \<le> :: 'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool)" by (auto simp: class.wqo_def)

  from wqo have refl: "reflp_on (op \<le>) (UNIV :: ('a + 'b) set)" by (simp add: wqo_on_def almost_full_on_imp_reflp_on)
  from wqo have trans: "transp_on (op \<le>) (UNIV :: ('a + 'b) set)" by (simp add: wqo_on_def)

  show "OFCLASS ('a + 'b, preorder_class)"
    by (intro_classes, simp add: less_sum_def)
       (insert refl, unfold reflp_on_def, force,
        insert trans, unfold transp_on_def, blast)
qed
end


subsection {* Pairs are Well-Quasi-Ordered *}

text {*If types @{typ "'a"} and @{typ "'b"} are well-quasi-ordered by @{text "P"}
and @{text "Q"}, then pairs of type @{typ "'a \<times> 'b"} are well-quasi-ordered by
the pointwise combination of @{text P} and @{text Q}.*}

instantiation prod :: (wqo, wqo) wqo
begin
definition "p \<le> q \<longleftrightarrow> fst p \<le> fst q \<and> snd p \<le> snd q"
definition "(p :: 'a \<times> 'b) < q \<longleftrightarrow> p \<le> q \<and> \<not> (q \<le> p)"

instance proof (rule wqo_class.intro)
  have 1: "wqo_on (op \<le>) (UNIV :: 'a set)"
    using order_trans and good
    by (auto simp: wqo_on_UNIV_conv class.wqo_def class.wqo_axioms_def class.preorder_def)
  have 2: "wqo_on (op \<le>) (UNIV :: 'b set)"
    using order_trans and good
    by (auto simp: wqo_on_UNIV_conv class.wqo_def class.wqo_axioms_def class.preorder_def)
  from wqo_on_Sigma [OF 1 2]
    have "wqo_on (op \<le>) (UNIV :: ('a \<times> 'b) set)"
      by (auto simp: less_eq_prod_def [abs_def] split_def prod_le_def)
  hence "class.wqo (op \<le> :: 'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool) (op <)"
    unfolding wqo_on_UNIV_conv less_prod_def [abs_def] .
  thus "class.wqo_axioms (op \<le> :: 'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool)" by (auto simp: class.wqo_def)
next
  show "OFCLASS ('a \<times> 'b, preorder_class)"
    by (intro_classes, auto simp: less_prod_def less_eq_prod_def)
       (blast intro: order_trans)+
qed
end


subsection {* Lists are Well-Quasi-Ordered *}

text {*If the type @{typ "'a"} is well-quasi-ordered by @{text "P"}, then
lists of type @{typ "'a list"} are well-quasi-ordered by the embedding
relation.*}

instantiation list :: (wqo) wqo
begin
definition "xs \<le> ys \<longleftrightarrow> emb (op \<le>) xs ys"
definition "(xs :: 'a list) < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> (ys \<le> xs)"

instance proof (rule wqo_class.intro)
  let ?P = "op \<le> :: 'a \<Rightarrow> 'a \<Rightarrow> bool"
  let ?P' = "op \<le> :: 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  have "class.wqo ?P (op <)" ..
  hence wqo: "wqo_on ?P UNIV"
    unfolding wqo_on_UNIV_conv less_le_not_le [abs_def] .
  from wqo_on_lists [OF this]
    have "wqo_on (emb ?P) (lists UNIV)" .
  hence "wqo_on ?P' UNIV"
    using `wqo_on ?P UNIV`
    unfolding wqo_on_def
    unfolding less_eq_list_def [abs_def]
    by auto
  hence "class.wqo ?P' (op <)"
    unfolding wqo_on_UNIV_conv less_list_def [abs_def] .
  thus "class.wqo_axioms ?P'" by (auto simp: class.wqo_def)

  from reflp_on_emb [OF wqo_on_imp_reflp_on [OF wqo]]
    have "reflp_on (emb ?P) (lists UNIV)" .
  hence refl: "reflp_on ?P' UNIV"
    unfolding reflp_on_def less_eq_list_def by auto

  from transp_on_emb [OF wqo_on_imp_transp_on [OF wqo]]
    have "transp_on (emb ?P) (lists UNIV)" .
  hence trans: "transp_on ?P' UNIV"
    unfolding transp_on_def less_eq_list_def by blast
  show "OFCLASS ('a list, preorder_class)"
    by (intro_classes, simp add: less_list_def)
       (insert refl, unfold reflp_on_def, force,
        insert trans, unfold transp_on_def, blast)
qed
end

text {*If the type @{typ "'a"} is well-quasi-ordered by @{text "P"}, then
lists of type @{typ "'a list"} are well-quasi-ordered by the embedding
relation.*}

instantiation tree :: (wqo) wqo
begin
definition "s \<le> t \<longleftrightarrow> hemb (op \<le>) s t"
definition "(s :: 'a tree) < t \<longleftrightarrow> s \<le> t \<and> \<not> (t \<le> s)"

instance proof (rule wqo_class.intro)
  let ?P = "op \<le> :: 'a \<Rightarrow> 'a \<Rightarrow> bool"
  let ?P' = "op \<le> :: 'a tree \<Rightarrow> 'a tree \<Rightarrow> bool"
  have "class.wqo ?P (op <)" ..
  hence wqo: "wqo_on ?P UNIV"
    unfolding wqo_on_UNIV_conv less_le_not_le [abs_def] .
  from wqo_on_trees [OF this]
    have "wqo_on (hemb ?P) (trees UNIV)" .
  hence "wqo_on ?P' UNIV"
    using `wqo_on ?P UNIV`
    unfolding wqo_on_def
    unfolding less_eq_tree_def [abs_def]
    by auto
  hence "class.wqo ?P' (op <)"
    unfolding wqo_on_UNIV_conv less_tree_def [abs_def] .
  thus "class.wqo_axioms ?P'" by (auto simp: class.wqo_def)

  from reflp_on_hemb [OF wqo_on_imp_reflp_on [OF wqo]]
    have "reflp_on (hemb ?P) (trees UNIV)" .
  hence refl: "reflp_on ?P' UNIV"
    unfolding reflp_on_def less_eq_tree_def by auto

  from hemb_trans
    have "transp_on (hemb ?P) (trees UNIV)" by (auto simp: transp_on_def)
  hence trans: "transp_on ?P' UNIV"
    unfolding transp_on_def less_eq_tree_def by blast
  show "OFCLASS ('a tree, preorder_class)"
    by (intro_classes, simp add: less_tree_def)
       (insert refl, unfold reflp_on_def, force,
        insert trans, unfold transp_on_def, blast)
qed
end

end
