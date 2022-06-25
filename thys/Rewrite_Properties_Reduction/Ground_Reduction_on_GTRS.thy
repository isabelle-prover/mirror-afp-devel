section \<open>Reducing Rewrite Properties to Properties on Ground Terms over Ground Systems\<close>
theory Ground_Reduction_on_GTRS
  imports
    Rewriting_Properties
    Rewriting_GTRS
    Rewriting_LLRG_LV_Mondaic
begin

lemma ground_sys_nf_eq_lift:
  fixes \<R> :: "('f, 'v) term rel" 
  assumes gtrs: "ground_sys \<R>" "ground_sys \<S>"
    and nf: "NF (gsrstep \<F> \<R>) = NF (gsrstep \<F> \<S>)"
  shows "NF (srstep \<F> \<R>) = NF (srstep \<F> \<S>)"
proof -
  {fix s \<U> \<V> assume ass: "ground_sys (\<U> :: ('f, 'v) term rel)" "ground_sys \<V>"
    "NF (gsrstep \<F> \<U>) = NF (gsrstep \<F> \<V>)" "s \<in> NF (srstep \<F> \<U>)"
    have "s \<in> NF (srstep \<F> \<V>)"
    proof (rule ccontr)
      assume "s \<notin> NF (srstep \<F> \<V>)"
      then obtain C l r \<sigma> where step: "(l, r) \<in> \<V>" and rep: "s = C\<langle>l \<cdot> \<sigma>\<rangle>"
        and funas: "funas_ctxt C \<subseteq> \<F>" "funas_term l \<subseteq> \<F>" "funas_term r \<subseteq> \<F>" using ass(2)
        by (auto simp: funas_term_subst NF_def sig_step_def dest!: rstep_imp_C_s_r) blast
      from step ass(2) rep have rep: "s = C\<langle>l\<rangle>" "ground l" "ground r"
        by (auto intro: ground_subst_apply)
      from step rep(2-) funas have "l \<notin> NF (gsrstep \<F> \<V>)"
        by (auto simp: NF_def sig_step_def Image_def)
      from this ass(3) have "l \<notin> NF (srstep \<F> \<U>)" by auto
      then obtain t where "(l, t) \<in> srstep \<F> \<U>" by auto
      from srstep_ctxt_closed[OF funas(1) this, unfolded rep(1)[symmetric]]
      show False using ass(4) 
        by auto
    qed}
    then show ?thesis using assms
      by (smt (verit, best) equalityI subsetI)
qed

lemma ground_sys_inv:
 "ground_sys \<R> \<Longrightarrow> ground_sys (\<R>\<inverse>)" by auto

lemma ground_sys_symcl:
 "ground_sys \<R> \<Longrightarrow> ground_sys (\<R>\<^sup>\<leftrightarrow>)" by auto

lemma ground_sys_comp_rrstep_rel'_ground:
  assumes "ground_sys \<R>" "ground_sys \<S>"
   and "(s, t) \<in> comp_rrstep_rel' \<F> \<R> \<S>"
 shows "ground s" "ground t"
proof -
  from assms(3) consider (a) "(s, t) \<in> srsteps_with_root_step \<F> \<R> O (srstep \<F> \<S>)\<^sup>+" |
    (b) "(s, t) \<in> (srstep \<F> \<R>)\<^sup>+ O srsteps_with_root_step \<F> \<S>"
    by auto
  then have "ground s \<and> ground t"
  proof cases
    case a
    then show ?thesis using srsteps_with_root_step_ground(1)[OF assms(1)]
      using srsteps_with_root_step_ground(2)[OF assms(1), THEN srsteps_pres_ground_l[OF assms(2)]]
      by blast
  next
    case b
    then show ?thesis using srsteps_with_root_step_ground(2)[OF assms(2)]
      using srsteps_with_root_step_ground(1)[OF assms(2), THEN srsteps_pres_ground_r[OF assms(1)]]
      by blast
  qed
  then show "ground s" "ground t" by simp_all
qed

lemma GTRS_commute:
  assumes "ground_sys \<R>" "ground_sys \<S>"
   and com: "commute (gsrstep \<F> \<R>) (gsrstep \<F> \<S>)"
  shows "commute (srstep \<F> \<R>) (srstep \<F> \<S>)"
proof -
  {fix s t assume ass: "(s, t) \<in> comp_rrstep_rel' \<F> (\<R>\<inverse>) \<S>"
    then obtain u where steps: "(s, u) \<in> (srstep \<F> (\<R>\<inverse>))\<^sup>+" "(u, t) \<in> (srstep \<F> \<S>)\<^sup>+"
      by (auto simp: sig_step_converse_rstep dest: srsteps_with_root_step_srstepsD)
    have gr: "ground s" "ground t" "ground u"
      using ground_sys_comp_rrstep_rel'_ground[OF ground_sys_inv[OF assms(1)] assms(2) ass]
      using srsteps_pres_ground_r[OF assms(2) _ steps(2)] by auto
    then have "(s, u) \<in>  (gsrstep \<F> (\<R>\<inverse>))\<^sup>*" "(u, t) \<in> (gsrstep \<F> \<S>)\<^sup>*" using steps
      by (auto dest!: trancl_into_rtrancl intro: ground_srsteps_eq_gsrsteps_eq)
    then have "(s, t) \<in> (gsrstep \<F> \<S>)\<^sup>* O (gsrstep \<F> (\<R>\<inverse>))\<^sup>*" using com steps
      by (auto simp: commute_def rew_converse_inwards)
    from gsrsteps_eq_relcomp_srsteps_relcompD[OF this]
    have "commute_redp \<F> \<R> \<S> s t" unfolding commute_redp_def
      by (simp add: rew_converse_inwards)}
  then show ?thesis by (intro commute_rrstep_intro) simp
qed

lemma GTRS_CR:
  assumes "ground_sys \<R>"
   and "CR (gsrstep \<F> \<R>)"
  shows "CR (srstep \<F> \<R>)" using GTRS_commute assms
  unfolding CR_iff_self_commute
  by blast


lemma GTRS_SCR:
  assumes gtrs: "ground_sys \<R>"
   and scr: "SCR (gsrstep \<F> \<R>)"
  shows "SCR (srstep \<F> \<R>)"
proof -
  {fix s t u assume ass: "(s, t) \<in> srstep \<F> \<R>" "(s, u) \<in> srstep \<F> \<R>"
    and root: "(s, t) \<in> sig_step \<F> (rrstep \<R>) \<or> (s, u) \<in> sig_step \<F> (rrstep \<R>)"
    from ass have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>" "funas_term u \<subseteq> \<F>" by blast+
    from root have gr: "ground s" "ground t" "ground u" using ass gtrs
      using srrstep_ground srstep_pres_ground_l srstep_pres_ground_r
      by metis+
    from scr obtain v where v: "(t, v) \<in> (gsrstep \<F> \<R>)\<^sup>= \<and> (u, v) \<in> (gsrstep \<F> \<R>)\<^sup>*"
      using gr unfolding SCR_on_def
      by (metis Int_iff UNIV_I ass mem_Collect_eq mem_Sigma_iff)
    then have "SCRp \<F> \<R> t u"
    by (metis (full_types) Int_iff Un_iff gsrsteps_eq_to_srsteps_eq)}
  then show ?thesis by (intro SCR_rrstep_intro) (metis srrstep_to_srestep)+ 
qed

lemma GTRS_WCR:
  assumes gtrs: "ground_sys \<R>"
   and wcr: "WCR (gsrstep \<F> \<R>)"
  shows "WCR (srstep \<F> \<R>)"
proof -
  {fix s t u assume ass: "(s, t) \<in> sig_step \<F> (rrstep \<R>)" "(s, u) \<in> srstep \<F> \<R>"
    from ass have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>" "funas_term u \<subseteq> \<F>" by blast+
    from srrstep_ground[OF gtrs ass(1)] have gr: "ground s" "ground t" "ground u"
      using srstep_pres_ground_l[OF gtrs _ ass(2)]
      by simp_all
    from this wcr have w: "(t, u) \<in> (gsrstep \<F> \<R>)\<^sup>\<down>" using ass funas
      unfolding WCR_on_def
      by (metis IntI SigmaI UNIV_I mem_Collect_eq srrstep_to_srestep)
    then have "(t, u) \<in> (srstep \<F> \<R>)\<^sup>\<down>" unfolding join_def
      by (metis (full_types) gsrsteps_eq_to_srsteps_eq joinD joinI join_def)}
  then show ?thesis by (intro WCR_rrstep_intro) simp
qed

lemma GTRS_UNF:
  assumes gtrs: "ground_sys \<R>"
   and unf: "UNF (gsrstep \<F> \<R>)"
  shows "UNF (srstep \<F> \<R>)"
proof -
  {fix s t assume ass: "(s, t) \<in> comp_rrstep_rel' \<F> (\<R>\<inverse>) \<R>"
    then obtain u where steps: "(s, u) \<in> (srstep \<F> (\<R>\<inverse>))\<^sup>+" "(u, t) \<in> (srstep \<F> \<R>)\<^sup>+"
      by (auto simp: sig_step_converse_rstep dest: srsteps_with_root_step_srstepsD)
    have gr: "ground s" "ground t" "ground u"
      using ground_sys_comp_rrstep_rel'_ground[OF ground_sys_inv[OF gtrs] gtrs ass]
      using srsteps_pres_ground_r[OF gtrs  _ steps(2)] by auto
    from steps(1) have f: "funas_term s \<subseteq> \<F>" by (simp add: srstepsD) 
    let ?\<sigma> = "\<lambda> _. s"
    from steps gr have "(s, u \<cdot> ?\<sigma>) \<in> (gsrstep \<F> (\<R>\<inverse>))\<^sup>+" "(u \<cdot> ?\<sigma>, t) \<in> (gsrstep \<F> \<R>)\<^sup>+"
      unfolding srstep_converse_dist Restr_converse trancl_converse
      using srsteps_subst_closed[where ?\<sigma> = ?\<sigma> and ?s = u, of _ \<F>] f
      by (force simp: ground_subst_apply intro: ground_srsteps_gsrsteps)+
    then have "UN_redp \<F> \<R> s t" using unf ground_NF_srstep_gsrstep[OF gr(1), of \<F> \<R>]
      using ground_NF_srstep_gsrstep[OF gr(2), of \<F> \<R>]
        by (auto simp: UNF_on_def UN_redp_def normalizability_def rew_converse_outwards)
           (meson trancl_into_rtrancl)}
  then show ?thesis by (intro UNF_rrstep_intro) simp
qed


lemma GTRS_UNC:
  assumes gtrs: "ground_sys \<R>"
   and unc: "UNC (gsrstep \<F> \<R>)"
  shows "UNC (srstep \<F> \<R>)"
proof -
  {fix s t assume ass: "(s, t) \<in> srsteps_with_root_step \<F> (\<R>\<^sup>\<leftrightarrow>)"
    from ass have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>"
      by (meson srstepsD srsteps_with_root_step_srstepsD)+
    from ass have "ground s" "ground t" using srsteps_with_root_step_ground[OF ground_sys_symcl[OF gtrs]]
      by auto
    then have "UN_redp \<F> \<R> s t" unfolding UN_redp_def using ass unc unfolding UNC_def
      by (simp add: ground_NF_srstep_gsrstep ground_srsteps_eq_gsrsteps_eq gsrstep_conversion_dist srsteps_with_root_step_sresteps_eqD)}
  then show ?thesis by (intro UNC_rrstep_intro) simp
qed


lemma GTRS_NFP:
  assumes "ground_sys \<R>"
   and nfp: "NFP (gsrstep \<F> \<R>)"
  shows "NFP (srstep \<F> \<R>)"
proof -
  {fix s t assume ass: "(s, t) \<in> comp_rrstep_rel' \<F> (\<R>\<inverse>) \<R>"
    from ass have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>"
      by (meson Un_iff relcompEpair srstepsD srsteps_with_root_step_srstepsD)+
    from ass have "ground s" "ground t"
      by (metis assms(1) ground_sys_comp_rrstep_rel'_ground ground_sys_inv)+
    from this ass have "(s, t) \<in> (gsrstep \<F> (\<R>\<inverse>))\<^sup>* O (gsrstep \<F> \<R>)\<^sup>*"
      by (intro srsteps_eq_relcomp_gsrsteps_relcomp) (auto dest!: srsteps_with_root_step_sresteps_eqD)
    then have "t \<in> NF (gsrstep \<F>  \<R>) \<Longrightarrow> (s, t) \<in> (gsrstep \<F> \<R>)\<^sup>*" using NFP_stepD[OF nfp]
      by (auto simp: rew_converse_outwards)
    then have "NFP_redp \<F> \<R> s t" unfolding NFP_redp_def
      by (simp add: \<open>ground t\<close> ground_NF_srstep_gsrstep gsrsteps_eq_to_srsteps_eq)}
  then show ?thesis by (intro NFP_rrstep_intro) simp
qed


lemma GTRS_NE_aux:
  assumes "(s, t) \<in> srsteps_with_root_step \<F> \<R>"
   and gtrs: "ground_sys \<R>" "ground_sys \<S>"
   and ne: "NE (gsrstep \<F> \<R>) (gsrstep \<F> \<S>)"
  shows "NE_redp \<F> \<R> \<S> s t"
proof -
  from assms(1) have gr: "ground s" "ground t"
    using srsteps_with_root_step_ground[OF gtrs(1)] by simp_all
  have "(s, t) \<in> (gsrstep \<F> \<R>)\<^sup>+" using gr assms(1)
    by (auto dest: srsteps_with_root_step_srstepsD intro: ground_srsteps_gsrsteps)
  then have "t \<in> NF (srstep \<F> \<R>) \<Longrightarrow> (s, t) \<in> (gsrstep \<F> \<S>)\<^sup>*"
    using gr ne unfolding NE_on_def
    by (auto simp: normalizability_def ground_subst_apply dest!: trancl_into_rtrancl) blast
  then show "NE_redp \<F> \<R> \<S> s t" unfolding NE_redp_def
    by (simp add: gsrsteps_eq_to_srsteps_eq)
qed

lemma GTRS_NE:
  assumes gtrs: "ground_sys \<R>" "ground_sys \<S>"
   and ne: "NE (gsrstep \<F> \<R>) (gsrstep \<F> \<S>)"
  shows "NE (srstep \<F> \<R>) (srstep \<F> \<S>)"
proof -
  {fix s t assume "(s, t) \<in> srsteps_with_root_step \<F> \<R>"
    from GTRS_NE_aux[OF this gtrs ne] have "NE_redp \<F> \<R> \<S> s t"
      by simp}
  moreover
  {fix s t assume "(s, t) \<in> srsteps_with_root_step \<F> \<S>"
    from GTRS_NE_aux[OF this gtrs(2, 1) NE_symmetric[OF ne]]
    have "NE_redp \<F> \<S> \<R> s t" by simp}
  ultimately show ?thesis
    using ground_sys_nf_eq_lift[OF gtrs NE_NF_eq[OF ne]]
    by (intro NE_rrstep_intro) auto
qed


lemma gtrs_CE_aux:
  assumes step:"(s, t) \<in> srsteps_with_root_step \<F> (\<R>\<^sup>\<leftrightarrow>)"
   and gtrs: "ground_sys \<R>" "ground_sys \<S>"
   and ce: "CE (gsrstep \<F> \<R>) (gsrstep \<F> \<S>)"
  shows "(s, t) \<in> (srstep \<F> \<S>)\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  from step gtrs(1) have "ground s" "ground t"
    by (metis ground_sys_symcl srsteps_with_root_step_ground)+
  then have "(s, t) \<in> (gsrstep \<F> \<R>)\<^sup>\<leftrightarrow>\<^sup>*" using step
    by (simp add: ground_srsteps_eq_gsrsteps_eq gsrstep_conversion_dist srsteps_with_root_step_sresteps_eqD)
  then have "(s, t) \<in> (gsrstep \<F> \<S>)\<^sup>\<leftrightarrow>\<^sup>*" using ce unfolding CE_on_def
    by blast
  then show "(s, t) \<in> (srstep \<F> \<S>)\<^sup>\<leftrightarrow>\<^sup>*"
    by (simp add: gsrstep_conversion_dist gsrsteps_eq_to_srsteps_eq symcl_srsteps_conversion)
qed


lemma gtrs_CE:
  assumes gtrs: "ground_sys \<R>" "ground_sys \<S>"
   and ce: "CE (gsrstep \<F> \<R>) (gsrstep \<F> \<S>)"
  shows "CE (srstep \<F> \<R>) (srstep \<F> \<S>)"
proof -
  {fix s t assume "(s, t) \<in> srsteps_with_root_step \<F> (\<R>\<^sup>\<leftrightarrow>)"
    from gtrs_CE_aux[OF this gtrs ce] have "(s, t) \<in> (srstep \<F> \<S>)\<^sup>\<leftrightarrow>\<^sup>*" by simp}
  moreover
  {fix s t assume "(s, t) \<in> srsteps_with_root_step \<F> (\<S>\<^sup>\<leftrightarrow>)"
    from gtrs_CE_aux[OF this gtrs(2, 1) CE_symmetric[OF ce]]
    have "(s, t) \<in> (srstep \<F> \<R>)\<^sup>\<leftrightarrow>\<^sup>*" by simp}
  ultimately show ?thesis
    by (intro CE_rrstep_intro) auto
qed

end