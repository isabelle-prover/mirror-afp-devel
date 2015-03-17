theory ArityAnalysisSig
imports "../Launchbury/Terms" AEnv "Arity-Nominal" "../Launchbury/Nominal-HOLCF"  "../Launchbury/Substitution"
begin

locale ArityAnalysis =
  fixes Aexp :: "exp \<Rightarrow> Arity \<rightarrow> AEnv"

locale ArityAnalysisHeap =
  fixes Aheap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> AEnv"

locale EdomArityAnalysis = ArityAnalysis + 
  assumes Aexp_edom: "edom (Aexp e\<cdot>a) \<subseteq> fv e"
begin

  lemma fup_Aexp_edom: "edom (fup\<cdot>(Aexp e)\<cdot>a) \<subseteq> fv e"
    by (cases a) (auto dest:set_mp[OF Aexp_edom])
  
  lemma Aexp_fresh_bot[simp]: assumes "atom v \<sharp> e" shows "(Aexp e\<cdot>a) v = \<bottom>"
  proof-
    from assms have "v \<notin> fv e" by (metis fv_not_fresh)
    with Aexp_edom have "v \<notin> edom (Aexp e\<cdot>a)" by auto
    thus ?thesis unfolding edom_def by simp
  qed
end

locale ArityAnalysisHeapEqvt = ArityAnalysisHeap + 
  assumes Aheap_eqvt[eqvt]: "\<pi> \<bullet> Aheap = Aheap"

end
