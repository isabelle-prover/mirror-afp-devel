section \<open>Algorithms on Nondeterministic Generalized Büchi Automata\<close>

theory NGBA_Algorithms
imports
  NGBA_Implement
  NBA_Combine
  NBA_Algorithms
  Degeneralization_Refine
begin

  subsection \<open>Implementations\<close>

  context
  begin

    interpretation autoref_syn by this

    lemma degeneralize_alt_def: "degeneralize A = nba
      (ngba.alphabet A)
      ((\<lambda> p. (p, 0)) ` ngba.initial A)
      (\<lambda> a (p, k). (\<lambda> q. (q, Degeneralization.count (ngba.accepting A) p k)) ` ngba.transition A a p)
      (degen (ngba.accepting A))"
      unfolding degeneralization.degeneralize_def by auto

    schematic_goal ngba_degeneralize: "(?f :: ?'a, degeneralize) \<in> ?R"
      unfolding degeneralize_alt_def
      using degen_param[autoref_rules] count_param[autoref_rules]
      by autoref
    concrete_definition ngba_degeneralize uses ngba_degeneralize
    lemmas ngba_degeneralize_refine[autoref_rules] = ngba_degeneralize.refine

    schematic_goal nba_intersect':
      assumes [autoref_rules]: "(seq, HOL.eq) \<in> L \<rightarrow> L \<rightarrow> bool_rel"
      shows "(?f, intersect') \<in> \<langle>L, S\<rangle> nbai_nba_rel \<rightarrow> \<langle>L, T\<rangle> nbai_nba_rel \<rightarrow> \<langle>L, S \<times>\<^sub>r T\<rangle> ngbai_ngba_rel"
      unfolding intersection.product_def by autoref
    concrete_definition nba_intersect' uses nba_intersect'
    lemma nba_intersect'_refine[autoref_rules]:
      assumes "GEN_OP seq HOL.eq (L \<rightarrow> L \<rightarrow> bool_rel)"
      shows "(nba_intersect' seq, intersect') \<in>
        \<langle>L, S\<rangle> nbai_nba_rel \<rightarrow> \<langle>L, T\<rangle> nbai_nba_rel \<rightarrow> \<langle>L, S \<times>\<^sub>r T\<rangle> ngbai_ngba_rel"
      using nba_intersect'.refine assms unfolding autoref_tag_defs by this

  end

end