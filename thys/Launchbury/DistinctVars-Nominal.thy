theory "DistinctVars-Nominal"
imports DistinctVars "Nominal-Utils"
begin

subsubsection {* Freshness lemmas related to associative lists *}

lemma heapVars_not_fresh:
  "x \<in> heapVars \<Gamma> \<Longrightarrow> \<not>(atom x \<sharp> \<Gamma>)"
  by (induct \<Gamma>, auto simp add: fresh_Cons fresh_Pair)

lemma fresh_delete:
  assumes "atom x \<sharp> \<Gamma>"
  shows "atom x \<sharp> (delete v \<Gamma>)"
using assms
by(induct \<Gamma>)(auto simp add: fresh_Cons)

lemma fresh_heap_expr:
  assumes "a \<sharp> \<Gamma>"
  and "(x,e) \<in> set \<Gamma>"
  shows "a \<sharp> e"
  using assms
  by (metis fresh_list_elem fresh_Pair)

lemma fresh_heap_expr':
  assumes "a \<sharp> \<Gamma>"
  and "e \<in> snd ` set \<Gamma>"
  shows "a \<sharp> e"
  using assms
  by (induct \<Gamma>, auto simp add: fresh_Cons fresh_Pair)

lemma fresh_star_heap_expr':
  assumes "S \<sharp>* \<Gamma>"
  and "e \<in> snd ` set \<Gamma>"
  shows "S \<sharp>* e"
  using assms
  by (metis fresh_star_def fresh_heap_expr')


subsubsection {* Equivariance lemmas *}

lemma heapVars[eqvt]:
  "\<pi> \<bullet> heapVars \<Gamma> = heapVars (\<pi> \<bullet> \<Gamma>)"
  by (simp add: heapVars_def)

lemma distinctVars_eqvt[eqvt]:
  "distinctVars \<Gamma> \<Longrightarrow> distinctVars (\<pi> \<bullet> \<Gamma>)"
  apply (induct \<Gamma> rule:distinctVars.induct)
  apply simp
  apply (simp add: distinctVars_Cons)
  by (metis (full_types) heapVars mem_permute_iff)

subsubsection {* Freshness and distinctness *}

lemma fresh_heapVars_distinct:
 assumes "atom ` heapVars \<Delta> \<sharp>* \<Gamma>"
 shows "heapVars \<Delta> \<inter> heapVars \<Gamma> = {}"
proof-
  { fix x
    assume "x \<in> heapVars \<Delta>"
    moreover
    assume "x \<in> heapVars \<Gamma>"
    hence "atom x \<in> supp \<Gamma>"
      by (induct \<Gamma>)(auto simp add: supp_Cons heapVars_def supp_Pair supp_at_base)
    ultimately
    have False
      using assms
      by (simp add: fresh_star_def fresh_def)
  }
  thus "heapVars \<Delta> \<inter> heapVars \<Gamma> = {}" by auto
qed
end
