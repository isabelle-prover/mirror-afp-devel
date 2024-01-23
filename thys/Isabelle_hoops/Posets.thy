section\<open>Some order tools: posets with explicit universe\<close>

theory Posets
imports Main "HOL-Library.LaTeXsugar"

begin

locale poset_on =
  fixes P :: "'b set"
  fixes P_lesseq :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<le>\<^sup>P" 60) 
  fixes P_less :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "<\<^sup>P" 60)
  assumes not_empty [simp]: "P \<noteq> \<emptyset>"
  and reflex: "reflp_on P (\<le>\<^sup>P)"
  and antisymm: "antisymp_on P (\<le>\<^sup>P)"
  and trans: "transp_on P (\<le>\<^sup>P)"
  and strict_iff_order: "x \<in> P \<Longrightarrow> y \<in> P \<Longrightarrow> x <\<^sup>P y = (x \<le>\<^sup>P y \<and> x \<noteq> y)"
begin

lemma strict_trans:
  assumes "a \<in> P" "b \<in> P" "c \<in> P" "a <\<^sup>P b" "b <\<^sup>P c"
  shows "a <\<^sup>P c"
  using antisymm antisymp_onD assms trans strict_iff_order transp_onD
  by smt 

end

locale bot_poset_on = poset_on +
  fixes bot :: "'b" ("0\<^sup>P")
  assumes bot_closed: "0\<^sup>P \<in> P"
  and bot_first: "x \<in> P \<Longrightarrow> 0\<^sup>P \<le>\<^sup>P x"

locale top_poset_on = poset_on +
  fixes top :: "'b" ("1\<^sup>P")
  assumes top_closed: "1\<^sup>P \<in> P"
  and top_last: "x \<in> P \<Longrightarrow> x \<le>\<^sup>P 1\<^sup>P"

locale bounded_poset_on  = bot_poset_on + top_poset_on

locale total_poset_on = poset_on +
  assumes total: "totalp_on P (\<le>\<^sup>P)"
begin

lemma trichotomy:
  assumes "a \<in> P" "b \<in> P"
  shows "(a <\<^sup>P b \<and> \<not>(a = b \<or> b <\<^sup>P a)) \<or>
         (a = b \<and> \<not>(a <\<^sup>P b \<or> b <\<^sup>P a)) \<or>
         (b <\<^sup>P a \<and> \<not>(a = b \<or> a <\<^sup>P b))"
  using  antisymm antisymp_onD assms strict_iff_order total totalp_onD by metis

lemma strict_order_equiv_not_converse: 
  assumes "a \<in> P" "b \<in> P"
  shows "a <\<^sup>P b \<longleftrightarrow> \<not>(b \<le>\<^sup>P a)"
  using assms strict_iff_order reflex reflp_onD strict_trans trichotomy by metis

end
     
end