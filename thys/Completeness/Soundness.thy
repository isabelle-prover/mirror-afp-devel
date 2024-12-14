section "Soundness"

theory Soundness imports Completeness begin

lemma permutation_validS: "mset fs = mset gs \<Longrightarrow> (validS fs = validS gs)"
  unfolding validS_def evalS_def
  using mset_eq_setD by blast

lemma modelAssigns_vblcase: "phi \<in> modelAssigns M \<Longrightarrow> x \<in> objects M \<Longrightarrow> vblcase x phi \<in> modelAssigns M"
  unfolding modelAssigns_def mem_Collect_eq
  by (smt (verit) image_subset_iff mem_Collect_eq range_subsetD vbl_cases
      vblcase_nextX vblcase_zeroX)

lemma soundnessFAll:
    assumes "u \<notin> freeVarsFL (FAll Pos A # Gamma)"
    and "validS (instanceF u A # Gamma)"
  shows "validS (FAll Pos A # Gamma)"
unfolding validS_def
proof (intro strip)
  fix M phi
  assume \<phi>: "phi \<in> modelAssigns M"
  have "evalF M (vblcase x phi) A" 
    if x: "x \<in> objects M" and "\<not> evalS M phi Gamma" 
    for x
  proof -
    have "evalF M (vblcase x (\<lambda>y. if y = u then x else phi y)) A"
    proof -
      have "evalF M (vblcase x (\<lambda>y. if y = u then x else phi y)) A 
           \<or>evalS M (\<lambda>y. if y = u then x else phi y) Gamma"
        using \<phi> assms(2) evalF_instance image_subset_iff validS_def x by fastforce
      then show ?thesis
        using assms(1) equalOn_def evalS_equiv freeVarsFL_cons that(2) by fastforce
    qed
    moreover
    have "equalOn (freeVarsF A) (vblcase x (\<lambda>y. if y = u then x else phi y))
     (vblcase x phi)"
      by (smt (verit, best) Un_iff assms(1) equalOn_def equalOn_vblcaseI' freeVarsFAll
          freeVarsFL_cons)
    ultimately show ?thesis
      using evalF_equiv by force
  qed 
  then show "evalS M phi (FAll Pos A # Gamma) = True"
    by auto
qed

lemma soundnessFEx: "validS (instanceF x A # Gamma) \<Longrightarrow> validS (FAll Neg A # Gamma)"
  unfolding validS_def
  by (metis evalF_FEx evalF_instance evalS_cons modelAssigns_iff range_subsetD)

lemma soundnessFCut: "\<lbrakk>validS (C # Gamma); validS (FNot C # Delta)\<rbrakk> \<Longrightarrow> validS (Gamma @ Delta)"
  using evalF_FNot evalS_append validS_def by auto

lemma soundness: "fs : deductions(PC) \<Longrightarrow> validS fs"  
proof (induction fs rule: deductions.induct)
  case (inferI conc prems)
  then have vS: "\<forall>x \<in> prems. validS x"
    by auto
  have "validS conc"
    if \<section>: "(conc, prems) \<in> Perms"
  proof -
    obtain \<Delta> where \<Delta>: "prems = {\<Delta>}"
      using \<section> vS by (auto simp: Perms_def)
    then have "mset conc = mset \<Delta>"
      using Perms_def that by fastforce
    with \<Delta> permutation_validS vS show ?thesis
      by blast
  qed
  moreover have "validS conc"
    if "(conc, prems) \<in> Axioms"
    using that by (auto simp add: Axioms_def validS_def)
  moreover have "validS conc"
    if "(conc, prems) \<in> Conjs"
    using that vS inferI apply (simp add: validS_def Conjs_def)
    by (metis evalFConj evalS_append evalS_cons insertCI sign.simps(1))
  moreover have "validS conc"
    if "(conc, prems) \<in> Disjs"
    using that vS inferI by (fastforce simp add: validS_def Disjs_def)
  moreover have "validS conc"
    if "(conc, prems) \<in> Alls"
    using that vS inferI soundnessFAll 
    by (force simp add: validS_def Alls_def subset_iff)
  moreover have "validS conc"
    if "(conc, prems) \<in> Exs"
    using that vS inferI soundnessFEx
    by (force simp add: validS_def Exs_def subset_iff)
  moreover have "validS conc"
    if "(conc, prems) \<in> Weaks"
    using that vS by(force simp: Weaks_def validS_def evalS_def)
  moreover have "validS conc"
    if "(conc, prems) \<in> Contrs"
    using that vS by(fastforce simp add: Contrs_def validS_def evalS_def)
  moreover have "validS conc"
    if "(conc, prems) \<in> Cuts"
    using that vS by (force simp add: Cuts_def soundnessFCut)
  ultimately show ?case
    using inferI.hyps
    by (auto simp: PC_def subset_iff)
qed

theorem completeness: "fs \<in> deductions (PC) \<longleftrightarrow> validS fs"
  using adequacy mono_deductions rulesInPCs(18) soundness by blast

end
