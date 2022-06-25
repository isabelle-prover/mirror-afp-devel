section \<open>Reducing Rewrite Properties to Properties on Ground Terms over Linear Variable-Separated Systems\<close>
theory Ground_Reduction_on_LV
  imports
    Rewriting_Properties
    Rewriting_LLRG_LV_Mondaic
begin

lemma lv_linear_sys: "lv \<R> \<Longrightarrow> linear_sys \<R>"
  by (auto simp: lv_def)

lemma comp_rrstep_rel'_sig_mono:
  "\<F> \<subseteq> \<G> \<Longrightarrow> comp_rrstep_rel' \<F> \<R> \<S> \<subseteq> comp_rrstep_rel' \<G> \<R> \<S>"
  by (meson Un_mono relcomp_mono srsteps_monp srsteps_with_root_step_sig_mono)

lemma srsteps_eqD: "(s, t) \<in> (srstep \<F> \<R>)\<^sup>* \<Longrightarrow> (s, t) \<in> (rstep \<R>)\<^sup>*"
  by (metis rtrancl_eq_or_trancl srstepsD)

section \<open>Linear-variable separated results\<close>

locale open_terms_two_const_lv =
  fixes \<R> :: "('f, 'v) term rel" and \<F> c d
  assumes lv: "lv \<R>" and sig: "funas_rel \<R> \<subseteq> \<F>"
    and fresh: "(c, 0) \<notin> \<F>" "(d, 0) \<notin> \<F>"
    and diff: "c \<noteq> d"
begin

abbreviation "\<H> \<equiv> insert (c, 0) (insert (d,0) \<F>)"
abbreviation "\<sigma>\<^sub>c \<equiv> const_subst c"
abbreviation "\<sigma>\<^sub>d \<equiv> const_subst d"

lemma sig_mono: "\<F> \<subseteq> \<H>" by auto
lemma fresh_sym_c: "(c, 0) \<notin> funas_rel \<R>" using sig fresh
  by (auto simp: funas_rel_def)
lemma fresh_sym_d: "(d, 0) \<notin> funas_rel \<R>" using sig fresh
  by (auto simp: funas_rel_def)
lemma fresh_sym_c_inv: "(c, 0) \<notin> funas_rel (\<R>\<inverse>)" using sig fresh
  by (auto simp: funas_rel_def)
lemma fresh_sym_d_inv: "(d, 0) \<notin> funas_rel (\<R>\<inverse>)" using sig fresh
  by (auto simp: funas_rel_def)

lemmas all_fresh = fresh_sym_c fresh_sym_d fresh_sym_c_inv fresh_sym_d_inv


lemma sig_inv: "funas_rel (\<R>\<inverse>) \<subseteq> \<F>" using sig unfolding funas_rel_def by auto
lemma lv_inv: "lv (\<R>\<inverse>)" using lv unfolding lv_def by auto
lemma well_subst:
  "\<And>x. funas_term ((const_subst c) x) \<subseteq> \<H>"
  "\<And>x. funas_term ((const_subst d) x) \<subseteq> \<H>"
  by auto

lemma srsteps_with_root_step_to_grsteps:
  assumes "(s, t) \<in> srsteps_with_root_step \<F> \<R>"
  shows "(s \<cdot> \<sigma>\<^sub>c, t \<cdot> \<sigma>\<^sub>d) \<in> (gsrstep \<H> \<R>)\<^sup>*"
proof -
  from assms have lift: "(s, t) \<in> srsteps_with_root_step \<H> \<R>"
    using srsteps_with_root_step_sig_mono[OF sig_mono]
    by blast
  note [dest!] = lv_srsteps_with_root_step_idep_subst[OF lv _ well_subst, THEN srsteps_with_root_step_sresteps_eqD]
  have "(s \<cdot> \<sigma>\<^sub>c, t \<cdot> \<sigma>\<^sub>d) \<in> (srstep \<H> \<R>)\<^sup>*" using lift
    using srsteps_eq_subst_closed[OF _ well_subst(1)]
    using srsteps_eq_subst_closed[OF _ well_subst(2)]
    by (auto dest: trancl_into_rtrancl)
  then show ?thesis
    by (intro ground_srsteps_eq_gsrsteps_eq) auto
qed

lemma comp_rrstep_rel'_to_grsteps:
  assumes "(s, t) \<in> comp_rrstep_rel' \<F> (\<R>\<inverse>) \<R>"
  shows "(s \<cdot> \<sigma>\<^sub>c, t \<cdot> \<sigma>\<^sub>d) \<in> (gsrstep \<H> (\<R>\<inverse>))\<^sup>* O (gsrstep \<H> \<R>)\<^sup>*"
proof -
  from assms have lift: "(s, t) \<in> comp_rrstep_rel' \<H> (\<R>\<inverse>) \<R>" using sig_mono
    by (meson in_mono relcomp_mono srsteps_monp srsteps_with_root_step_sig_mono sup_mono)
  note [dest!] = lv_srsteps_with_root_step_idep_subst[OF lv _ well_subst, THEN srsteps_with_root_step_sresteps_eqD]
  note [dest!] = lv_srsteps_with_root_step_idep_subst[OF lv_inv _ well_subst, THEN srsteps_with_root_step_sresteps_eqD]
  have "(s \<cdot> \<sigma>\<^sub>c, t \<cdot> \<sigma>\<^sub>d) \<in> (srstep \<H> (\<R>\<inverse>))\<^sup>* O (srstep \<H> \<R>)\<^sup>*" using lift
    using srsteps_eq_subst_closed[OF _ well_subst(1)]
    using srsteps_eq_subst_closed[OF _ well_subst(2)]
    by (auto dest!: trancl_into_rtrancl) blast
  then show ?thesis
    by (intro srsteps_eq_relcomp_gsrsteps_relcomp) auto
qed

lemma gsrsteps_eq_to_srsteps:
  assumes "(s \<cdot> \<sigma>\<^sub>c, t \<cdot> \<sigma>\<^sub>d) \<in> (gsrstep \<H> \<R>)\<^sup>*"
    and funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>"
  shows "(s, t) \<in> (srstep \<F> \<R>)\<^sup>*"
proof -
  from funas have d: "(d, 0) \<notin> funas_term s" and c: "(c, 0) \<notin> funas_term (t \<cdot> \<sigma>\<^sub>d)"
    using fresh diff by (auto simp: funas_term_subst)
  have "(s, t) \<in> (rstep \<R>)\<^sup>*" using c gsrsteps_eq_to_rsteps_eq[OF assms(1)]
    using remove_const_subst_steps_eq_lhs[OF lv_linear_sys[OF lv] fresh_sym_c,
        THEN remove_const_subst_steps_eq_rhs[OF lv_linear_sys[OF lv] fresh_sym_d d]]
    by auto
  then show ?thesis using funas sig by blast
qed

lemma convert_NF_to_GNF:
  "funas_term t \<subseteq> \<F> \<Longrightarrow> t \<in> NF (srstep \<F> \<R>) \<Longrightarrow> t \<cdot> \<sigma>\<^sub>c \<in> NF (gsrstep \<H> \<R>)"
  "funas_term t \<subseteq> \<F> \<Longrightarrow> t \<in> NF (srstep \<F> \<R>) \<Longrightarrow> t \<cdot> \<sigma>\<^sub>d \<in> NF (gsrstep \<H> \<R>)"
  using NF_to_fresh_const_subst_NF[OF lv_linear_sys[OF lv] fresh_sym_c sig]
  using NF_to_fresh_const_subst_NF[OF lv_linear_sys[OF lv] fresh_sym_d sig]
  by blast+


lemma convert_GNF_to_NF:
  "funas_term t \<subseteq> \<F> \<Longrightarrow> t \<cdot> \<sigma>\<^sub>c \<in> NF (gsrstep \<H> \<R>) \<Longrightarrow> t \<in> NF (srstep \<F> \<R>)"
  "funas_term t \<subseteq> \<F> \<Longrightarrow> t \<cdot> \<sigma>\<^sub>d \<in> NF (gsrstep \<H> \<R>) \<Longrightarrow> t \<in> NF (srstep \<F> \<R>)"
  using fresh_const_subst_NF_pres[OF fresh_sym_c sig]
  using fresh_const_subst_NF_pres[OF fresh_sym_d sig]
  using sig_mono by blast+


lemma lv_CR:
  assumes cr: "CR (gsrstep \<H> \<R>)"
  shows "CR (srstep \<F> \<R>)"
proof -
  {fix s t assume ass: "(s, t) \<in> (srstep \<F> (\<R>\<inverse>))\<^sup>+ O srsteps_with_root_step \<F> \<R>"
    from ass have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>"
      by (metis Pair_inject ass relcompE srstepsD srsteps_with_root_step_srstepsD)+
    have "(s \<cdot> \<sigma>\<^sub>c, t \<cdot> \<sigma>\<^sub>d) \<in> (gsrstep \<H> (\<R>\<inverse>))\<^sup>* O (gsrstep \<H> \<R>)\<^sup>*"
      using ass comp_rrstep_rel'_to_grsteps by auto
    then have s: "(s \<cdot> \<sigma>\<^sub>c, t \<cdot> \<sigma>\<^sub>d) \<in> (gsrstep \<H> \<R>)\<^sup>* O (gsrstep \<H> (\<R>\<inverse>))\<^sup>*"
      using cr unfolding CR_on_def
      by (auto simp: join_def rew_converse_outwards)
    from gsrsteps_eq_relcomp_to_rsteps_relcomp[OF this]
    have "commute_redp \<F> \<R> \<R> s t" unfolding commute_redp_def using funas fresh
      using remove_const_subst_relcomp[OF lv_linear_sys[OF lv] lv_linear_sys[OF lv_inv]
          all_fresh diff, THEN rsteps_eq_relcomp_srsteps_eq_relcompI[OF sig sig_inv funas]]
      by (metis srstep_converse_dist subsetD)}
  then show ?thesis by (intro CR_rrstep_intro) simp
qed

lemma lv_WCR:
  assumes wcr: "WCR (gsrstep \<H> \<R>)"
  shows "WCR (srstep \<F> \<R>)"
proof -
  note sig_trans_root = subsetD[OF srrstep_monp[OF sig_mono]]
  note sig_trans = subsetD[OF srstep_monp[OF sig_mono]]
  {fix s t u assume ass: "(s, t) \<in> sig_step \<F> (rrstep \<R>)" "(s, u) \<in> srstep \<F> \<R>"
    from ass have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>" "funas_term u \<subseteq> \<F>" by blast+
    then have free: "(d, 0) \<notin> funas_term u" "(c, 0) \<notin> funas_term t" using fresh by blast+
    have *: "ground (s \<cdot> \<sigma>\<^sub>c)" "ground (t \<cdot> \<sigma>\<^sub>d)" "ground (u \<cdot> \<sigma>\<^sub>c)" by auto
    moreover have "(s \<cdot> \<sigma>\<^sub>c, t \<cdot> \<sigma>\<^sub>d) \<in> srstep \<H> \<R>" using lv sig_trans_root[OF ass(1)]
      by (intro lv_root_step_idep_subst[THEN srrstep_to_srestep]) auto
    moreover have "(s \<cdot> \<sigma>\<^sub>c, u \<cdot> \<sigma>\<^sub>c) \<in> srstep \<H> \<R>"
      using srstep_subst_closed[OF sig_trans[OF ass(2)], of \<sigma>\<^sub>c]
      by auto
    ultimately have w: "(t \<cdot> \<sigma>\<^sub>d, u \<cdot> \<sigma>\<^sub>c) \<in> (gsrstep \<H> \<R>)\<^sup>\<down>" using wcr unfolding WCR_on_def
      by auto (metis (no_types, lifting) * )
    note join_unfolded = w[unfolded join_def rew_converse_inwards]
    have "(t, u) \<in> (srstep \<F> \<R>)\<^sup>\<down>" unfolding join_def
      using remove_const_subst_relcomp[OF lv_linear_sys[OF lv] lv_linear_sys[OF lv_inv]
          fresh_sym_d fresh_sym_c fresh_sym_d_inv fresh_sym_c_inv diff[symmetric] free
          gsrsteps_eq_relcomp_to_rsteps_relcomp[OF join_unfolded],
          THEN rsteps_eq_relcomp_srsteps_eq_relcompI[OF sig sig_inv funas(2-)]]
      by (metis (no_types, lifting) srstep_converse_dist)}
  then show ?thesis by (intro WCR_rrstep_intro) simp
qed

lemma lv_NFP:
  assumes nfp: "NFP (gsrstep \<H> \<R>)"
  shows "NFP (srstep \<F> \<R>)"
proof -
  {fix s t assume ass: "(s, t) \<in> comp_rrstep_rel' \<F> (\<R>\<inverse>) \<R>"
    from ass have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>"
      by (metis Un_iff ass relcompEpair srstepsD srsteps_with_root_step_srstepsD)+
    from comp_rrstep_rel'_to_grsteps[OF ass]
    have " (s \<cdot> \<sigma>\<^sub>c, t \<cdot> \<sigma>\<^sub>d) \<in> (gsrstep \<H> (\<R>\<inverse>))\<^sup>* O (gsrstep \<H> \<R>)\<^sup>*" by simp
    then have "t \<cdot> \<sigma>\<^sub>d \<in> NF (gsrstep \<H> \<R>) \<Longrightarrow> (s \<cdot> \<sigma>\<^sub>c, t \<cdot> \<sigma>\<^sub>d) \<in> (gsrstep \<H> \<R>)\<^sup>*" using NFP_stepD[OF nfp]
      by (auto simp: rew_converse_outwards)
    from gsrsteps_eq_to_srsteps[OF this funas]
    have "NFP_redp \<F> \<R> s t" unfolding NFP_redp_def
      using convert_NF_to_GNF(2)[OF funas(2)]
      by simp}
  then show ?thesis by (intro NFP_rrstep_intro) simp
qed

lemma lv_UNF:
  assumes unf: "UNF (gsrstep \<H> \<R>)"
  shows "UNF (srstep \<F> \<R>)"
proof -
  {fix s t assume ass: "(s, t) \<in> comp_rrstep_rel' \<F> (\<R>\<inverse>) \<R>"
    from ass have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>"
      by (metis Un_iff ass relcompEpair srstepsD srsteps_with_root_step_srstepsD)+
    from comp_rrstep_rel'_to_grsteps[OF ass]
    have " (s \<cdot> \<sigma>\<^sub>c, t \<cdot> \<sigma>\<^sub>d) \<in> (gsrstep \<H> (\<R>\<inverse>))\<^sup>* O (gsrstep \<H> \<R>)\<^sup>*" by simp
    then have "s \<cdot> \<sigma>\<^sub>c \<in> NF (gsrstep \<H> \<R>) \<Longrightarrow> t \<cdot> \<sigma>\<^sub>d \<in> NF (gsrstep \<H> \<R>) \<Longrightarrow> s \<cdot> \<sigma>\<^sub>c = t \<cdot> \<sigma>\<^sub>d"
      using unf unfolding UNF_on_def
      by (auto simp: normalizability_def rew_converse_outwards)
    then have "UN_redp \<F> \<R> s t" unfolding UN_redp_def
      using convert_NF_to_GNF(1)[OF funas(1)]
      using convert_NF_to_GNF(2)[OF funas(2)]
      by (metis NF_not_suc funas gsrsteps_eq_to_srsteps rtrancl_eq_or_trancl)}
  then show ?thesis by (intro UNF_rrstep_intro) simp
qed

lemma lv_UNC:
  assumes unc: "UNC (gsrstep \<H> \<R>)"
  shows "UNC (srstep \<F> \<R>)"
proof -
  have lv_conv: "lv (\<R>\<^sup>\<leftrightarrow>)" using lv by (auto simp: lv_def)
  {fix s t assume ass: "(s, t) \<in> srsteps_with_root_step \<F> (\<R>\<^sup>\<leftrightarrow>)"
    from ass have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>"
      by (metis Un_iff ass relcompEpair srstepsD srsteps_with_root_step_srstepsD)+
    have "(s \<cdot> \<sigma>\<^sub>c, t \<cdot> \<sigma>\<^sub>d) \<in> (gsrstep \<H> \<R>)\<^sup>\<leftrightarrow>\<^sup>*"
      using lv_srsteps_with_root_step_idep_subst[OF lv_conv srsteps_with_root_step_sig_mono[OF sig_mono, THEN subsetD, OF ass]
          well_subst,THEN srsteps_with_root_step_sresteps_eqD]
      unfolding conversion_def Restr_smycl_dist srstep_symcl_dist
      by (intro ground_srsteps_eq_gsrsteps_eq) auto
    then have "s \<cdot> \<sigma>\<^sub>c \<in> NF (gsrstep \<H> \<R>) \<Longrightarrow> t \<cdot> \<sigma>\<^sub>d \<in> NF (gsrstep \<H> \<R>) \<Longrightarrow> s \<cdot> \<sigma>\<^sub>c = t \<cdot> \<sigma>\<^sub>d"
      using unc unfolding UNC_def
      by (auto simp: normalizability_def sig_step_converse_rstep rtrancl_converse Restr_converse)
    then have "UN_redp \<F> \<R> s t" unfolding UN_redp_def
      using convert_NF_to_GNF(1)[OF funas(1)]
      using convert_NF_to_GNF(2)[OF funas(2)]
      by (metis NF_not_suc funas gsrsteps_eq_to_srsteps rtrancl_eq_or_trancl)}
  then show ?thesis by (intro UNC_rrstep_intro) simp
qed


lemma lv_SCR:
  assumes scr: "SCR (gsrstep \<H> \<R>)"
  shows "SCR (srstep \<F> \<R>)"
proof -
  note sig_trans_root = subsetD[OF srrstep_monp[OF sig_mono]]
  note sig_trans = subsetD[OF srstep_monp[OF sig_mono]]
  note cl_on_c = lin_fresh_rstep_const_replace_closed[OF lv_linear_sys[OF lv] fresh_sym_c]
    lin_fresh_rstep_const_replace_closed[OF lv_linear_sys[OF lv_inv] fresh_sym_c_inv]
  note cl_on_d = lin_fresh_rstep_const_replace_closed[OF lv_linear_sys[OF lv] fresh_sym_d]
    lin_fresh_rstep_const_replace_closed[OF lv_linear_sys[OF lv_inv] fresh_sym_d_inv]
  {fix s t u assume ass: "(s, t) \<in> srstep \<F> \<R>" "(s, u) \<in> srstep \<F> \<R>"
      and root: "(s, t) \<in> sig_step \<F> (rrstep \<R>) \<or> (s, u) \<in> sig_step \<F> (rrstep \<R>)"
    from ass have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>" "funas_term u \<subseteq> \<F>"
      by (force dest: sig_stepE)+
    then have fresh_c_t:"(c, 0) \<notin> funas_term (t \<cdot> \<sigma>\<^sub>d)" and fresh_d_u:"(d, 0) \<notin> funas_term u" using fresh diff
      by (auto simp: funas_term_subst) 
    have *: "(s, t) \<in> sig_step \<F> (rrstep \<R>) \<Longrightarrow> (s \<cdot> \<sigma>\<^sub>c, t \<cdot> \<sigma>\<^sub>d) \<in> gsrstep \<H> \<R> \<and> (s \<cdot> \<sigma>\<^sub>c, u \<cdot> \<sigma>\<^sub>c) \<in> gsrstep \<H> \<R>"
      "(s, u) \<in> sig_step \<F> (rrstep \<R>) \<Longrightarrow> (s \<cdot> \<sigma>\<^sub>d, t \<cdot> \<sigma>\<^sub>d) \<in> gsrstep \<H> \<R> \<and> (s \<cdot> \<sigma>\<^sub>d, u \<cdot> \<sigma>\<^sub>c) \<in> gsrstep \<H> \<R>"
      using srstep_subst_closed[OF sig_trans[OF ass(2)] well_subst(1)]
      using srstep_subst_closed[OF sig_trans[OF ass(2)] well_subst(2)]
      using lv_root_step_idep_subst[OF lv] sig_trans_root[of "(s, t)" \<R>] sig_trans_root[of "(s, u)" \<R>]
      by (simp_all add: ass(1) sig_trans srstep_subst_closed srrstep_to_srestep)
    from this scr have "(u \<cdot> \<sigma>\<^sub>c, t \<cdot> \<sigma>\<^sub>d) \<in> (gsrstep \<H> \<R>)\<^sup>* O ((gsrstep \<H> \<R>)\<^sup>=)\<inverse>"
      using root unfolding SCR_on_def by (meson UNIV_I converse_iff relcomp.simps) 
    then have v: "(u \<cdot> \<sigma>\<^sub>c, t \<cdot> \<sigma>\<^sub>d) \<in> (srstep \<H> \<R>)\<^sup>* O ((srstep \<H> \<R>)\<^sup>=)\<inverse>"
      by (auto dest: gsrsteps_eq_to_srsteps_eq)
    have [simp]: "funas_term v \<subseteq> \<F> \<Longrightarrow> term_to_sig \<F> x v = v" for x v
      by (simp add: subset_insertI2)
    have "(u, t) \<in> (srstep \<F> \<R>)\<^sup>* O ((srstep \<F> \<R>)\<^sup>=)\<inverse>"
    proof -
      from v have "(u, t \<cdot> \<sigma>\<^sub>d) \<in> (rstep \<R>)\<^sup>* O (rstep (\<R>\<inverse>))\<^sup>="
        using const_replace_closed_relcomp[THEN const_replace_closed_remove_subst_lhs, OF
         const_replace_closed_rtrancl[OF cl_on_c(1)]
         const_replace_closed_symcl[OF cl_on_c(2)] fresh_c_t, of u]
        by (auto simp: relcomp.relcompI srstepD simp flip: rstep_converse_dist dest: srsteps_eqD)
      then have "(u, t) \<in> (rstep \<R>)\<^sup>* O (rstep (\<R>\<inverse>))\<^sup>="
        using const_replace_closed_relcomp[THEN const_replace_closed_remove_subst_lhs, OF
          const_replace_closed_symcl[OF cl_on_d(1)]
          const_replace_closed_rtrancl[OF cl_on_d(2)] fresh_d_u, of t]
        using converse_relcomp[where ?s = "(rstep (\<R>\<inverse>))\<^sup>=" and ?r = "(rstep \<R>)\<^sup>*"]
        by (metis (no_types, lifting) converseD converse_Id converse_Un converse_converse rstep_converse_dist rtrancl_converse)
      then obtain v where "(u, v) \<in> (rstep \<R>)\<^sup>*" "(v, t) \<in> (rstep (\<R>\<inverse>))\<^sup>=" by auto
      then have "(u, term_to_sig \<F> x v) \<in> (srstep \<F> \<R>)\<^sup>*" "(term_to_sig \<F> x v, t) \<in> (srstep \<F> (\<R>\<inverse>))\<^sup>="
        using funas(2, 3) sig fresh
        by (auto simp: rtrancl_eq_or_trancl rstep_trancl_sig_step_r subset_insertI2
          rew_converse_outwards dest: fuans_term_term_to_sig[THEN subsetD]
          intro!: rstep_term_to_sig_r rstep_srstepI rsteps_eq_srsteps_eqI)
      then show ?thesis
        by (metis converse_Id converse_Un relcomp.relcompI srstep_converse_dist)
    qed
    then have "SCRp \<F> \<R> t u"
      by auto}
  then show ?thesis by (intro SCR_rrstep_intro) (metis srrstep_to_srestep)+ 
qed


end


locale open_terms_two_const_lv_two_sys =
  open_terms_two_const_lv \<R>
  for \<R> :: "('f, 'v) term rel" +
  fixes \<S> :: "('f, 'v) term rel"
  assumes lv_S: "lv \<S>" and sig_S: "funas_rel \<S> \<subseteq> \<F>"
begin

lemma fresh_sym_c_S: "(c, 0) \<notin> funas_rel \<S>" using sig_S fresh
  by (auto simp: funas_rel_def)
lemma fresh_sym_d_S: "(d, 0) \<notin> funas_rel \<S>" using sig_S fresh
  by (auto simp: funas_rel_def)

lemma lv_commute:
  assumes com: "commute (gsrstep \<H> \<R>) (gsrstep \<H> \<S>)"
  shows "commute (srstep \<F> \<R>) (srstep \<F> \<S>)"
proof -
  have linear: "linear_sys \<S>" "linear_sys (\<R>\<inverse>)" using lv lv_S unfolding lv_def by auto
  {fix s t assume ass: "(s, t) \<in> comp_rrstep_rel' \<F> (\<R>\<inverse>) \<S>"
    from ass have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>"
      by (metis Un_iff ass relcompEpair srstepsD srsteps_with_root_step_srstepsD)+
    have "(s \<cdot> \<sigma>\<^sub>c, t \<cdot> \<sigma>\<^sub>d) \<in> (gsrstep \<H> (\<R>\<inverse>))\<^sup>* O (gsrstep \<H> \<S>)\<^sup>*"
      using comp_rrstep_rel'_sig_mono[OF sig_mono, THEN subsetD, OF ass]
      using srsteps_eq_subst_closed[OF _ well_subst(1)] srsteps_eq_subst_closed[OF _ well_subst(2)]
      by (auto simp: rew_converse_inwards dest!: trancl_into_rtrancl
          lv_srsteps_with_root_step_idep_subst[OF lv_inv _ well_subst, THEN srsteps_with_root_step_sresteps_eqD]
          lv_srsteps_with_root_step_idep_subst[OF lv_S _ well_subst, THEN srsteps_with_root_step_sresteps_eqD]
          intro!: srsteps_eq_relcomp_gsrsteps_relcomp) blast
    then have w: "(s \<cdot> \<sigma>\<^sub>c, t \<cdot> \<sigma>\<^sub>d) \<in> (gsrstep \<H> \<S>)\<^sup>* O (gsrstep \<H> (\<R>\<inverse>))\<^sup>*" using com
      unfolding commute_def Restr_converse srstep_converse_dist
      by blast
    have "(s, t) \<in> (srstep \<F> \<S>)\<^sup>* O (srstep \<F> (\<R>\<inverse>))\<^sup>*" using funas sig_S sig_inv fresh
      using remove_const_subst_relcomp[OF linear fresh_sym_c_S fresh_sym_d_S fresh_sym_c_inv fresh_sym_d_inv diff _ _
          gsrsteps_eq_relcomp_to_rsteps_relcomp[OF w]]
      by (intro rsteps_eq_relcomp_srsteps_eq_relcompI) auto
    then have "commute_redp \<F> \<R> \<S> s t" unfolding commute_redp_def
      by (simp add: rew_converse_inwards)}
  then show ?thesis by (intro commute_rrstep_intro) simp
qed



lemma lv_NE:
  assumes ne: "NE (gsrstep \<H> \<R>) (gsrstep \<H> \<S>)"
  shows "NE (srstep \<F> \<R>) (srstep \<F> \<S>)"
proof -
  from NE_NF_eq[OF ne] have ne_eq: "NF (srstep \<F> \<R>) = NF (srstep \<F> \<S>)"
    using lv lv_S sig sig_S fresh_sym_c fresh_sym_c_S
    by (intro  linear_sys_gNF_eq_NF_eq) (auto dest: lv_linear_sys)
  {fix s t assume step: "(s, t) \<in> srsteps_with_root_step \<F> \<R>"
    then have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>"
      by (metis Un_iff step relcompEpair srstepsD srsteps_with_root_step_srstepsD)+
    then have fresh: "(c, 0) \<notin> funas_term t" "(d, 0) \<notin> funas_term s" using fresh by auto
    from srsteps_with_root_step_sig_mono[OF sig_mono, THEN subsetD, OF step]
    have "(s \<cdot> \<sigma>\<^sub>c, t \<cdot> \<sigma>\<^sub>d) \<in> (gsrstep \<H> \<R>)\<^sup>*"
      using lv_srsteps_with_root_step_idep_subst[OF lv _ well_subst, THEN srsteps_with_root_step_sresteps_eqD]
      by (intro ground_srsteps_eq_gsrsteps_eq) auto
    then have "t \<cdot> \<sigma>\<^sub>d \<in> NF (gsrstep \<H> \<S>) \<Longrightarrow> (s \<cdot> \<sigma>\<^sub>c, t \<cdot> \<sigma>\<^sub>d) \<in> (gsrstep \<H> \<S>)\<^sup>*"
      using ne NE_NF_eq[OF ne] unfolding NE_on_def
      by (auto simp: normalizability_def)
    from this[THEN gsrsteps_eq_to_rsteps_eq, THEN remove_const_subst_steps[OF lv_linear_sys[OF lv_S] fresh_sym_c_S fresh_sym_d_S diff fresh]]
    have "NE_redp \<F> \<R> \<S> s t" using NF_to_fresh_const_subst_NF[OF lv_linear_sys[OF lv_S] fresh_sym_d_S sig_S funas(2)]
      using funas sig_S unfolding NE_redp_def ne_eq
      by (auto intro: rsteps_eq_srsteps_eqI)}
  moreover
  {fix s t assume step: "(s, t) \<in> srsteps_with_root_step \<F> \<S>"
    then have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>"
      by (metis sig_S sig_stepE sig_step_rsteps_dist srsteps_with_root_step_srstepsD)+
    then have fresh: "(c, 0) \<notin> funas_term t" "(d, 0) \<notin> funas_term s" using fresh by auto
    from srsteps_with_root_step_sig_mono[OF sig_mono, THEN subsetD, OF step]
    have "(s \<cdot> \<sigma>\<^sub>c, t \<cdot> \<sigma>\<^sub>d) \<in> (gsrstep \<H> \<S>)\<^sup>*"
      using lv_srsteps_with_root_step_idep_subst[OF lv_S _ well_subst, THEN srsteps_with_root_step_sresteps_eqD]
      by (intro ground_srsteps_eq_gsrsteps_eq) auto
    then have "t \<cdot> \<sigma>\<^sub>d \<in> NF (gsrstep \<H> \<R>) \<Longrightarrow> (s \<cdot> \<sigma>\<^sub>c, t \<cdot> \<sigma>\<^sub>d) \<in> (gsrstep \<H> \<R>)\<^sup>*"
      using ne NE_NF_eq[OF ne] unfolding NE_on_def
      by (auto simp: normalizability_def)
    from this[THEN gsrsteps_eq_to_rsteps_eq, THEN remove_const_subst_steps[OF lv_linear_sys[OF lv] fresh_sym_c fresh_sym_d diff fresh]]
    have "NE_redp \<F> \<S> \<R> s t" using NF_to_fresh_const_subst_NF[OF lv_linear_sys[OF lv] fresh_sym_d sig funas(2), of \<H>]
      using funas sig unfolding NE_redp_def ne_eq
      by (auto intro: rsteps_eq_srsteps_eqI)}
  ultimately show ?thesis using ne_eq
    by (intro NE_rrstep_intro) auto
qed

end

\<comment> \<open>CE is special as it only needs one additional constant therefore not
   included in the locale\<close>
lemma lv_CE_aux:
  assumes "(s, t) \<in> srsteps_with_root_step \<F> (\<R>\<^sup>\<leftrightarrow>)"
    and sig: "funas_rel \<R> \<subseteq> \<F>" "funas_rel \<S> \<subseteq> \<F>"
    and fresh: "(c, 0) \<notin> \<F>" and const: "(a, 0) \<in> \<F>"
    and lv: "lv \<R>" "lv \<S>"
    and ce: "CE (gsrstep (insert (c, 0) \<F>) \<R>) (gsrstep (insert (c, 0) \<F>) \<S>)"
  shows "(s, t) \<in> (srstep \<F> \<S>)\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  let ?\<H> = "insert (c, 0) \<F>" have mono: "\<F> \<subseteq> ?\<H>" by auto
  have lv_conv: "lv (\<R>\<^sup>\<leftrightarrow>)" "lv (\<S>\<^sup>\<leftrightarrow>)" using lv by (auto simp: lv_def)
  have sig_conv: "funas_rel (\<S>\<^sup>\<leftrightarrow>) \<subseteq> \<F>" using sig(2) by (auto simp: funas_rel_def)
  from fresh have fresh_sys: "(c, 0) \<notin> funas_rel \<R>" "(c, 0) \<notin> funas_rel \<S>" "(c, 0) \<notin> funas_rel (\<S>\<^sup>\<leftrightarrow>)"
    using sig by (auto simp: funas_rel_def)
  from assms(1) have lift: "(s, t) \<in> srsteps_with_root_step ?\<H> (\<R>\<^sup>\<leftrightarrow>)"
    unfolding srsteps_with_root_step_def
    by (meson in_mono mono relcomp_mono rtrancl_mono srrstep_monp srstep_monp)
  from assms(1) have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>"
    by (meson srstepsD srsteps_with_root_step_srstepsD)+
  from srsteps_with_root_step_sresteps_eqD[OF assms(1), THEN subsetD[OF srsteps_eq_monp[OF mono]]]
  have "(s \<cdot> const_subst c, t \<cdot> const_subst c) \<in> (srstep ?\<H> \<R>)\<^sup>\<leftrightarrow>\<^sup>*"
    by (auto simp: sig_step_conversion_dist intro: srsteps_eq_subst_closed)
  moreover have "(s \<cdot> const_subst c, t \<cdot> const_subst a) \<in> (srstep ?\<H> \<R>)\<^sup>\<leftrightarrow>\<^sup>*"
    unfolding sig_step_conversion_dist using const
    by (intro lv_srsteps_with_root_step_idep_subst[OF lv_conv(1) lift, THEN srsteps_with_root_step_sresteps_eqD]) auto
  moreover have "ground (s \<cdot> const_subst c)" "ground (t \<cdot> const_subst a)" "ground (t \<cdot> const_subst a)"
    by auto
  ultimately have toS:"(s \<cdot> const_subst c, t \<cdot> const_subst c) \<in> (gsrstep ?\<H> \<S>)\<^sup>\<leftrightarrow>\<^sup>*"
    "(s \<cdot> const_subst c, t \<cdot> const_subst a) \<in> (gsrstep ?\<H> \<S>)\<^sup>\<leftrightarrow>\<^sup>*"
    using ground_srsteps_eq_gsrsteps_eq[where ?\<F> = ?\<H> and ?\<R> = "\<R>\<^sup>\<leftrightarrow>"]
    using ce unfolding CE_on_def
    by (auto simp: Restr_smycl_dist conversion_def srstep_symcl_dist)
  then have *: "(t \<cdot> const_subst a, t \<cdot> const_subst c) \<in> (gsrstep ?\<H> \<S>)\<^sup>\<leftrightarrow>\<^sup>*"
    by (metis (no_types, lifting) conversion_inv conversion_rtrancl rtrancl.rtrancl_into_rtrancl)
  have "(t \<cdot> const_subst a, t) \<in> (srstep \<F> \<S>)\<^sup>\<leftrightarrow>\<^sup>*" using const
    using funas(2) fresh
    using remove_const_subst_steps_eq_rhs[OF lv_linear_sys[OF lv_conv(2)] fresh_sys(3) _
        gsrsteps_eq_to_rsteps_eq[OF *[unfolded gsrstep_conversion_dist]]]
    by (cases "vars_term t = {}")
      (auto simp: funas_term_subst sig_step_conversion_dist split: if_splits intro!: rsteps_eq_srsteps_eqI[OF sig_conv])
  moreover have "(s, t \<cdot> const_subst a) \<in> (srstep \<F> \<S>)\<^sup>\<leftrightarrow>\<^sup>*" using const
    using funas fresh
    using remove_const_subst_steps_eq_lhs[OF lv_linear_sys[OF lv_conv(2)] fresh_sys(3) _
        gsrsteps_eq_to_rsteps_eq[OF toS(2)[unfolded gsrstep_conversion_dist]]]
    by (cases "vars_term t = {}")
      (auto simp: sig_step_conversion_dist funas_term_subst split: if_splits intro!: rsteps_eq_srsteps_eqI[OF sig_conv])
  ultimately show "(s, t) \<in> (srstep \<F> \<S>)\<^sup>\<leftrightarrow>\<^sup>*"
    by (meson conversionE conversionI rtrancl_trans)
qed


lemma lv_CE:
  assumes sig: "funas_rel \<R> \<subseteq> \<F>" "funas_rel \<S> \<subseteq> \<F>"
    and fresh: "(c, 0) \<notin> \<F>" and const: "(a, 0) \<in> \<F>"
    and lv: "lv \<R>" "lv \<S>"
    and ce: "CE (gsrstep (insert (c, 0) \<F>) \<R>) (gsrstep (insert (c, 0) \<F>) \<S>)"
  shows "CE (srstep \<F> \<R>) (srstep \<F> \<S>)"
proof -
  {fix s t assume "(s, t) \<in> srsteps_with_root_step \<F> (\<R>\<^sup>\<leftrightarrow>)"
    from lv_CE_aux[OF this assms] have "(s, t) \<in> (srstep \<F> \<S>)\<^sup>\<leftrightarrow>\<^sup>*" by simp}
  moreover
  {fix s t assume "(s, t) \<in> srsteps_with_root_step \<F> (\<S>\<^sup>\<leftrightarrow>)"
    from lv_CE_aux[OF this sig(2, 1) fresh const lv(2, 1) CE_symmetric[OF ce]]
    have "(s, t) \<in> (srstep \<F> \<R>)\<^sup>\<leftrightarrow>\<^sup>*" by simp}
  ultimately show ?thesis
    by (intro CE_rrstep_intro) auto
qed


subsection \<open>Specialized for monadic signature\<close>

lemma lv_NE_aux:
  assumes "(s, t) \<in> srsteps_with_root_step \<F> \<R>" and fresh: "(c, 0) \<notin> \<F>"
    and sig: "funas_rel \<R> \<subseteq> \<F>" "funas_rel \<S> \<subseteq> \<F>"
    and lv: "lv \<R>" "lv \<S>"
    and mon: "monadic \<F>"
    and ne: "NE (gsrstep (insert (c, 0) \<F>) \<R>) (gsrstep (insert (c, 0) \<F>) \<S>)"
  shows "NE_redp \<F> \<R> \<S> s t"
proof -
  let ?\<sigma> = "const_subst c" let ?\<H> = "insert (c, 0) \<F>"
  have mono: "\<F> \<subseteq> ?\<H>" by auto
  from mon have mh: "monadic ?\<H>" by (auto simp: monadic_def)
  from fresh have fresh_sys: "(c, 0) \<notin> funas_rel \<R>" "(c, 0) \<notin> funas_rel \<S>" using sig
    by (auto simp: funas_rel_def)
  from assms have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>"
    by (meson srstepsD srsteps_with_root_step_srstepsD)+
  from funas have fresh_t: "(c, 0) \<notin> funas_term t" using fresh by auto
  from srsteps_subst_closed[OF srsteps_monp[OF mono, THEN subsetD, OF srsteps_with_root_step_srstepsD[OF assms(1)]], of ?\<sigma>]
  have gstep: "(s \<cdot> ?\<sigma>, t \<cdot> ?\<sigma>) \<in> (gsrstep (insert (c, 0) \<F>) \<R>)\<^sup>+"
    by (auto simp: ground_subst_apply intro!: ground_srsteps_gsrsteps)
  then have neq: "t \<in> NF (srstep \<F> \<R>) \<Longrightarrow> s \<cdot> ?\<sigma> \<noteq> t \<cdot> ?\<sigma>"
    using NF_to_fresh_const_subst_NF[OF lv_linear_sys[OF lv(1)] fresh_sys(1) sig(1) funas(2), of ?\<H>]
    by (metis NF_no_trancl_step)
  then have "t \<in> NF (srstep \<F> \<R>) \<Longrightarrow> (s \<cdot> ?\<sigma>, t \<cdot> ?\<sigma>) \<in> (gsrstep (insert (c, 0) \<F>) \<S>)\<^sup>+" using gstep
    using NF_to_fresh_const_subst_NF[OF lv_linear_sys[OF lv(1)] fresh_sys(1) sig(1) funas(2), of ?\<H>]
    using NE_NF_eq[OF ne, symmetric] ne unfolding NE_on_def
    by (auto simp: normalizability_def ground_subst_apply) (meson rtrancl_eq_or_trancl)
  then show ?thesis unfolding NE_redp_def
    using remove_const_lv_mondaic_steps[OF lv(2) fresh_sys(2) mh, THEN srstepsD[THEN conjunct1],
        THEN rsteps_srstepsI[OF sig(2) funas]]
    by (auto dest!: gsrsteps_to_srsteps)
qed

lemma lv_NE:
  assumes sig: "funas_rel \<R> \<subseteq> \<F>" "funas_rel \<S> \<subseteq> \<F>"
    and mon: "monadic \<F>" and fresh: "(c, 0) \<notin> \<F>"
    and lv: "lv \<R>" "lv \<S>"
    and ne: "NE (gsrstep (insert (c, 0) \<F>) \<R>) (gsrstep (insert (c, 0) \<F>) \<S>)"
  shows "NE (srstep \<F> \<R>) (srstep \<F> \<S>)"
proof -
  from fresh have fresh_sys: "(c, 0) \<notin> funas_rel \<R>" "(c, 0) \<notin> funas_rel \<S>"
    using sig by (auto simp: funas_rel_def)
  from NE_NF_eq[OF ne] have ne_eq: "NF (srstep \<F> \<R>) = NF (srstep \<F> \<S>)" using lv sig fresh_sys
    by (intro  linear_sys_gNF_eq_NF_eq) (auto dest: lv_linear_sys)
  {fix s t assume "(s, t) \<in> srsteps_with_root_step \<F> \<R>"
    from lv_NE_aux[OF this fresh sig lv mon ne] have "NE_redp \<F> \<R> \<S> s t" by simp}
  moreover
  {fix s t assume ass: "(s, t) \<in> srsteps_with_root_step \<F> \<S>"
    from lv_NE_aux[OF this fresh sig(2, 1) lv(2, 1) mon NE_symmetric[OF ne]] have "NE_redp \<F> \<S> \<R> s t" by simp}
  ultimately show ?thesis using ne_eq
    by (intro NE_rrstep_intro) auto
qed

end