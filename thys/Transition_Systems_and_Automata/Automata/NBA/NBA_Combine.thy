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

  global_interpretation intersection: automaton_intersection_trace
    nba nba.alphabet nba.initial nba.transition nba.accepting infs
    nba nba.alphabet nba.initial nba.transition nba.accepting infs
    ngba ngba.alphabet ngba.initial ngba.transition ngba.accepting "gen infs"
    "\<lambda> c\<^sub>1 c\<^sub>2. [c\<^sub>1 \<circ> fst, c\<^sub>2 \<circ> snd]"
    defines intersect' = intersection.intersect
    by unfold_locales auto

  lemmas intersect'_language[simp] = intersection.combine_language[folded NGBA.language_def]

  global_interpretation union: automaton_union_trace
    nba nba.alphabet nba.initial nba.transition nba.accepting infs
    nba nba.alphabet nba.initial nba.transition nba.accepting infs
    nba nba.alphabet nba.initial nba.transition nba.accepting infs
    case_sum
    defines union = union.union
    by (unfold_locales) (auto simp: comp_def)

  lemmas union_language = union.union_language

  abbreviation intersect where "intersect A B \<equiv> degeneralize (intersect' A B)"

  lemma intersect_language[simp]: "NBA.language (intersect A B) = NBA.language A \<inter> NBA.language B"
    by simp

end