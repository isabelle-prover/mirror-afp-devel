section \<open>Nondeterministic Büchi Automata Combinations\<close>

theory NBA_Combine
imports NBA NGBA
begin

  global_interpretation degeneralization: automaton_degeneralization_run
    ngba ngba.alphabet ngba.initial ngba.transition ngba.accepting "\<lambda> P w r p. gen infs P r"
    nba nba.alphabet nba.initial nba.transition nba.accepting "\<lambda> P w r p. infs P r"
    fst id
    defines degeneralize = degeneralization.degeneralize
    by (unfold_locales) (auto simp flip: sscan_smap)

  lemmas degeneralize_language[simp] = degeneralization.degeneralize_language[folded NBA.language_def]
  lemmas degeneralize_nodes_finite[iff] = degeneralization.degeneralize_nodes_finite[folded NBA.nodes_def]

  global_interpretation intersection: automaton_intersection_run
    nba nba.alphabet nba.initial nba.transition nba.accepting "\<lambda> P w r p. infs P r"
    nba nba.alphabet nba.initial nba.transition nba.accepting "\<lambda> P w r p. infs P r"
    ngba ngba.alphabet ngba.initial ngba.transition ngba.accepting "\<lambda> P w r p. gen infs P r"
    "\<lambda> c\<^sub>1 c\<^sub>2. [c\<^sub>1 \<circ> fst, c\<^sub>2 \<circ> snd]"
    defines intersect' = intersection.intersect
    by unfold_locales auto

  lemmas intersect'_language[simp] = intersection.intersect_language[folded NGBA.language_def]
  lemmas intersect'_nodes_finite[intro] = intersection.intersect_nodes_finite[folded NGBA.nodes_def]

  global_interpretation union: automaton_union_run
    nba nba.alphabet nba.initial nba.transition nba.accepting "\<lambda> P w r p. infs P r"
    nba nba.alphabet nba.initial nba.transition nba.accepting "\<lambda> P w r p. infs P r"
    nba nba.alphabet nba.initial nba.transition nba.accepting "\<lambda> P w r p. infs P r"
    case_sum
    defines union = union.union
    by (unfold_locales) (auto simp: comp_def)

  lemmas union_language = union.union_language
  lemmas union_nodes_finite = union.union_nodes_finite

  global_interpretation intersection_list: automaton_intersection_list_run
    nba nba.alphabet nba.initial nba.transition nba.accepting "\<lambda> P w r p. infs P r"
    ngba ngba.alphabet ngba.initial ngba.transition ngba.accepting "\<lambda> P w r p. gen infs P r"
    "\<lambda> cs. map (\<lambda> k ps. (cs ! k) (ps ! k)) [0 ..< length cs]"
    defines intersect_list' = intersection_list.intersect
  proof unfold_locales
    fix cs :: "('b \<Rightarrow> bool) list" and rs :: "'b stream list" and w :: "'a stream" and ps :: "'b list"
    assume 1: "length rs = length cs" "length ps = length cs"
    have "gen infs (map (\<lambda> k pp. (cs ! k) (pp ! k)) [0 ..< length cs]) (stranspose rs) \<longleftrightarrow>
      (\<forall> k < length cs. infs (\<lambda> pp. (cs ! k) (pp ! k)) (stranspose rs))"
      by (auto simp: gen_def)
    also have "\<dots> \<longleftrightarrow> (\<forall> k < length cs. infs (cs ! k) (smap (\<lambda> pp. pp ! k) (stranspose rs)))"
      by (simp add: comp_def)
    also have "\<dots> \<longleftrightarrow> (\<forall> k < length cs. infs (cs ! k) (rs ! k))" using 1 by simp
    also have "\<dots> \<longleftrightarrow> list_all (\<lambda> (c, r, p). infs c r) (cs || rs || ps)"
      using 1 unfolding list_all_length by simp
    finally show "gen infs (map (\<lambda> k ps. (cs ! k) (ps ! k)) [0 ..< length cs]) (stranspose rs) \<longleftrightarrow>
      list_all (\<lambda> (c, r, p). infs c r) (cs || rs || ps)" by this
  qed

  lemmas intersect_list'_language[simp] = intersection_list.intersect_language[folded NGBA.language_def]
  lemmas intersect_list'_nodes_finite[intro] = intersection_list.intersect_nodes_finite[folded NGBA.nodes_def]

  global_interpretation union_list: automaton_union_list_run
    nba nba.alphabet nba.initial nba.transition nba.accepting "\<lambda> P w r p. infs P r"
    nba nba.alphabet nba.initial nba.transition nba.accepting "\<lambda> P w r p. infs P r"
    "\<lambda> cs (k, p). (cs ! k) p"
    defines union_list = union_list.union
    by (unfold_locales) (auto simp: szip_sconst_smap_fst comp_def)

  lemmas union_list_language = union_list.union_language
  lemmas union_list_nodes_finite = union_list.union_nodes_finite

  abbreviation intersect where "intersect A B \<equiv> degeneralize (intersect' A B)"

  lemma intersect_language[simp]: "NBA.language (intersect A B) = NBA.language A \<inter> NBA.language B"
    by simp
  lemma intersect_nodes_finite[intro]:
    assumes "finite (NBA.nodes A)" "finite (NBA.nodes B)"
    shows "finite (NBA.nodes (intersect A B))"
    using intersect'_nodes_finite assms by simp

  abbreviation intersect_list where "intersect_list AA \<equiv> degeneralize (intersect_list' AA)"

  lemma intersect_list_language[simp]: "NBA.language (intersect_list AA) = \<Inter> (NBA.language ` set AA)"
    by simp
  lemma intersect_list_nodes_finite[intro]:
    assumes "list_all (finite \<circ> NBA.nodes) AA"
    shows "finite (NBA.nodes (intersect_list AA))"
    using intersect_list'_nodes_finite assms by simp

end