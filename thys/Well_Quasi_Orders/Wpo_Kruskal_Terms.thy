(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c.sternagel@gmail.com>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Kruskal's Tree Theorem for Terms *}

theory Wpo_Kruskal_Terms
imports
  Well_Partial_Orders
  Kruskal_Terms
begin

context finite_tree
begin

lemma wpo_on_terms:
  assumes "wpo_on P F"
  shows "wpo_on (term_hemb F P) (terms F)"
proof
  from irreflp_on_term_hemb_terms [OF assms [THEN wpo_on_imp_wfp_on]]
    show "irreflp_on (term_hemb F P) (terms F)" .
next
  from term_hemb_trans show "transp_on (term_hemb F P) (terms F)"
    by (auto simp: transp_on_def)
next
  from assms have "almost_full_on (P\<^sup>=\<^sup>=) F" by (auto simp: wpo_on_def)
  from almost_full_on_terms [OF this]
    show "almost_full_on (term_hemb F P)\<^sup>=\<^sup>= (terms F)"
    using term_hembeq_term_hemb_conv [of _ F P, symmetric]
    by (simp add: almost_full_on_def good_def)
qed

end

end

