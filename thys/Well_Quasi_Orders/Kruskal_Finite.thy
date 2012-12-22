(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Kruskal's Tree Theorem -- Finite Version for Terms *}

theory Kruskal_Finite
imports
  Well_Quasi_Orders
  Kruskal_Terms
  Finite_Tree
begin

context finite_tree
begin

text {*Embedding on trees.*}
inductive term_emb for F where
  term_emb_base [intro]:
    "\<lbrakk>(f, n) \<in> F; length ts = n; \<forall>t\<in>set ts. t \<in> terms F; t \<in> set ts\<rbrakk> \<Longrightarrow> term_emb F t (mk f ts)" |
  term_emb_trans [intro]: "term_emb F s t \<Longrightarrow> term_emb F t u \<Longrightarrow> term_emb F s u" |
  term_emb_ctxt [intro]:
    "\<lbrakk>term_emb F s t; (f, n) \<in> F; Suc (length (ss1@ss2)) = n; \<forall>t\<in>set (ss1@ss2). t \<in> terms F\<rbrakk> \<Longrightarrow>
    term_emb F (mk f (ss1 @ s # ss2)) (mk f (ss1 @ t # ss2))"

abbreviation term_embeq where
  "term_embeq F \<equiv> (term_emb F)\<^sup>=\<^sup>="

lemma term_emb_imp_terms:
  assumes "term_emb F s t"
  shows "s \<in> terms F \<and> t \<in> terms F"
  using assms by (induct) force+

lemma term_emb_size:
  assumes "term_emb F s t"
  shows "size s < size t"
  using assms
  by (induct)
     (auto simp: size_simp2 dest!: term_emb_imp_terms)

lemma term_emb_term_hemb_conv:
  "term_emb F = term_hemb F (\<lambda>_ _. False)" (is "?l = ?r")
proof (intro ext)
  fix s t show "?l s t = ?r s t"
  proof
    assume "?l s t" then show "?r s t" by (induct) auto
  next
    assume "?r s t" then show "?l s t" by (induct) auto
  qed
qed


subsection {* Kruskal's Tree Theorem -- Finite Version *}

lemma const_False_reflclp [simp]:
  "(\<lambda>_ _. False)\<^sup>=\<^sup>= = (op =)"
proof (intro ext)
  fix x y :: 'c
  show "(\<lambda>_ _. False)\<^sup>=\<^sup>= x y = op = x y" by simp
qed

lemma almost_full_on_terms_finite:
  assumes "finite F"
  shows "almost_full_on (term_embeq F) (terms F)"
proof -
  from eq_almost_full_on_finite_set [OF assms]
    have "almost_full_on (\<lambda>_ _. False)\<^sup>=\<^sup>= F" by simp
  from almost_full_on_terms [OF this]
    show ?thesis
    using term_hembeq_term_hemb_conv
    by (simp add: term_emb_term_hemb_conv almost_full_on_def good_def)
qed

end

end

