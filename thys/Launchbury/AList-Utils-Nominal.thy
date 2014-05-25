theory "AList-Utils-Nominal"
imports "AList-Utils" "Nominal-Utils"
begin

subsubsection {* Freshness lemmas related to associative lists *}

lemma domA_not_fresh:
  "x \<in> domA \<Gamma> \<Longrightarrow> \<not>(atom x \<sharp> \<Gamma>)"
  by (induct \<Gamma>, auto simp add: fresh_Cons fresh_Pair)

lemma fresh_delete:
  assumes "atom x \<sharp> \<Gamma>"
  shows "atom x \<sharp> (delete v \<Gamma>)"
using assms
by(induct \<Gamma>)(auto simp add: fresh_Cons)

lemma fv_delete_subset:
  "fv (delete v \<Gamma>) \<subseteq> fv \<Gamma>"
  using fresh_delete unfolding fresh_def fv_def by auto

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

lemma fresh_map_of:
  assumes "x \<in> domA \<Gamma>"
  assumes "a \<sharp> \<Gamma>"
  shows "a \<sharp> the (map_of \<Gamma> x)"
  using assms
  by (induct \<Gamma>)(auto simp add: fresh_Cons fresh_Pair)

lemma fresh_star_map_of:
  assumes "x \<in> domA \<Gamma>"
  assumes "a \<sharp>* \<Gamma>"
  shows "a \<sharp>* the (map_of \<Gamma> x)"
  using assms by (simp add: fresh_star_def fresh_map_of)

lemma domA_fv_subset: "domA \<Gamma> \<subseteq> fv \<Gamma>"
  by (induction \<Gamma>) auto

lemma map_of_fv_subset: "x \<in> domA \<Gamma> \<Longrightarrow> fv (the (map_of \<Gamma> x)) \<subseteq> fv \<Gamma>"
  by (induction \<Gamma>) auto

subsubsection {* Equivariance lemmas *}

lemma domA[eqvt]:
  "\<pi> \<bullet> domA \<Gamma> = domA (\<pi> \<bullet> \<Gamma>)"
  by (simp add: domA_def)

subsubsection {* Freshness and distinctness *}

lemma fresh_distinct:
 assumes "atom ` S \<sharp>* \<Gamma>"
 shows "S \<inter> domA \<Gamma> = {}"
proof-
  { fix x
    assume "x \<in> S"
    moreover
    assume "x \<in> domA \<Gamma>"
    hence "atom x \<in> supp \<Gamma>"
      by (induct \<Gamma>)(auto simp add: supp_Cons domA_def supp_Pair supp_at_base)
    ultimately
    have False
      using assms
      by (simp add: fresh_star_def fresh_def)
  }
  thus "S \<inter> domA \<Gamma> = {}" by auto
qed

subsubsection {* Pure codomains *}

lemma domA_fv_pure:
  fixes \<Gamma> :: "('a::at_base \<times> 'b::pure) list"
  shows  "fv \<Gamma> = domA \<Gamma>"
  apply (induct \<Gamma>)
  apply simp
  apply (case_tac a)
  apply (simp)
  done

lemma domA_fresh_pure:
  fixes \<Gamma> :: "('a::at_base \<times> 'b::pure) list"
  shows  "x \<in> domA \<Gamma> \<longleftrightarrow> \<not>(atom x \<sharp> \<Gamma>)"
  unfolding domA_fv_pure[symmetric]
  by (auto simp add: fv_def fresh_def)

end
