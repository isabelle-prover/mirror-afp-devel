theory MLSS_Decidable
  imports Place_Realisation Syntactic_Description
begin

theorem MLSS_decidable:
  "(\<exists>\<A>. satisfiable_normalized_MLSS_clause \<C> \<A>) \<longleftrightarrow>
   (\<exists>PI at\<^sub>p. adequate_place_framework \<C> PI at\<^sub>p)"  
proof
  assume "\<exists>\<A>. satisfiable_normalized_MLSS_clause \<C> \<A>"
  then obtain \<A> where "satisfiable_normalized_MLSS_clause \<C> \<A>" by blast
  with satisfiable_normalized_MLSS_clause.syntactic_description_is_adequate
  show "\<exists>PI at\<^sub>p. adequate_place_framework \<C> PI at\<^sub>p" by blast
next
  assume "\<exists>PI at\<^sub>p. adequate_place_framework \<C> PI at\<^sub>p"
  then obtain PI at\<^sub>p where "adequate_place_framework \<C> PI at\<^sub>p" by blast
  then have "finite PI"
    by (simp add: adequate_place_framework.finite_PI)
  with u_exists[of PI "card PI"] obtain u
    where "(\<forall>x\<in>PI. \<forall>y\<in>PI. x \<noteq> y \<longrightarrow> u x \<noteq> u y) \<and> (\<forall>x\<in>PI. card PI \<le> hcard (u x))"
    by presburger
  with \<open>adequate_place_framework \<C> PI at\<^sub>p\<close>
  have "place_realization \<C> PI at\<^sub>p u"
    unfolding place_realization_def place_realization_axioms_def by blast
  with place_realization.\<M>_sat_\<C> obtain \<M> where \<M>: "\<forall>lt\<in>\<C>. interp I\<^sub>s\<^sub>a \<M> lt"
    by blast
  have "satisfiable_normalized_MLSS_clause \<C> \<M>"
  proof -
    from \<open>adequate_place_framework \<C> PI at\<^sub>p\<close> have "normalized_MLSS_clause \<C>"
      unfolding adequate_place_framework_def by blast
    moreover
    from \<open>normalized_MLSS_clause \<C>\<close> have "finite (\<Union> (vars ` \<C>))"
      unfolding normalized_MLSS_clause_def
      by (simp add: finite_vars_fm)
    then have "proper_Venn_regions (\<Union> (vars ` \<C>))"
      by unfold_locales blast
    ultimately
    show ?thesis
      unfolding satisfiable_normalized_MLSS_clause_def satisfiable_normalized_MLSS_clause_axioms_def
      using \<M> by blast
  qed
  then show "\<exists>\<A>. satisfiable_normalized_MLSS_clause \<C> \<A>" by blast
qed

end