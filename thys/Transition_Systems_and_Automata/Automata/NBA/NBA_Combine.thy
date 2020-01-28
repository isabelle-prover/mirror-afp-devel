section \<open>Nondeterministic Büchi Automata Combinations\<close>

theory NBA_Combine
imports NBA NGBA
begin

  global_interpretation degeneralization: automaton_degeneralization_trace
    ngba ngba.alphabet ngba.initial ngba.transition ngba.accepting "gen infs"
    nba nba.alphabet nba.initial nba.transition nba.accepting infs
    defines degeneralize = degeneralization.degeneralize
    by unfold_locales auto

  lemmas degeneralize_language[simp] = degeneralization.degeneralize_language[folded NBA.language_def]
  lemmas degeneralize_nodes_finite[iff] = degeneralization.degeneralize_nodes_finite[folded NBA.nodes_def]

  global_interpretation intersection: automaton_intersection_trace
    nba nba.alphabet nba.initial nba.transition nba.accepting infs
    nba nba.alphabet nba.initial nba.transition nba.accepting infs
    ngba ngba.alphabet ngba.initial ngba.transition ngba.accepting "gen infs"
    "\<lambda> c\<^sub>1 c\<^sub>2. [c\<^sub>1 \<circ> fst, c\<^sub>2 \<circ> snd]"
    defines intersect' = intersection.intersect
    by unfold_locales auto

  lemmas intersect'_language[simp] = intersection.intersect_language[folded NGBA.language_def]
  lemmas intersect'_nodes_finite[intro] = intersection.intersect_nodes_finite[folded NGBA.nodes_def]

  global_interpretation intersection_list: automaton_intersection_list_trace
    nba nba.alphabet nba.initial nba.transition nba.accepting infs
    ngba ngba.alphabet ngba.initial ngba.transition ngba.accepting "gen infs"
    "\<lambda> cs. map (\<lambda> k pp. (cs ! k) (pp ! k)) [0 ..< length cs]"
    defines intersect_list' = intersection_list.intersect
  proof unfold_locales
    fix cs :: "('b \<Rightarrow> bool) list" and ws :: "'b stream list"
    assume 1: "length cs = length ws"
    have "gen infs (map (\<lambda> k pp. (cs ! k) (pp ! k)) [0 ..< length cs]) (stranspose ws) \<longleftrightarrow>
      (\<forall> k < length cs. infs (\<lambda> pp. (cs ! k) (pp ! k)) (stranspose ws))"
      by (auto simp: gen_def)
    also have "\<dots> \<longleftrightarrow> (\<forall> k < length cs. infs (cs ! k) (smap (\<lambda> pp. pp ! k) (stranspose ws)))"
      by (simp add: comp_def)
    also have "\<dots> \<longleftrightarrow> (\<forall> k < length cs. infs (cs ! k) (ws ! k))" using 1 by simp
    also have "\<dots> \<longleftrightarrow> list_all2 infs cs ws" using 1 unfolding list_all2_conv_all_nth by simp
    finally show "gen infs (map (\<lambda> k pp. (cs ! k) (pp ! k)) [0 ..< length cs]) (stranspose ws) \<longleftrightarrow>
      list_all2 infs cs ws" by this
  qed

  lemmas intersect_list'_language[simp] = intersection_list.intersect_language[folded NGBA.language_def]
  lemmas intersect_list'_nodes_finite[intro] = intersection_list.intersect_nodes_finite[folded NGBA.nodes_def]

  global_interpretation union: automaton_union_trace
    nba nba.alphabet nba.initial nba.transition nba.accepting infs
    nba nba.alphabet nba.initial nba.transition nba.accepting infs
    nba nba.alphabet nba.initial nba.transition nba.accepting infs
    case_sum
    defines union = union.union
    by (unfold_locales) (auto simp: comp_def)

  lemmas union_language = union.union_language
  lemmas union_nodes_finite = union.union_nodes_finite

  global_interpretation union_list: automaton_union_list_trace
    nba nba.alphabet nba.initial nba.transition nba.accepting infs
    nba nba.alphabet nba.initial nba.transition nba.accepting infs
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