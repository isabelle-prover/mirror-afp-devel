section \<open>Reducing Rewrite Properties to Properties on Ground Terms over Left-Linear Right-Ground Systems\<close>
theory Ground_Reduction_on_LLRG
  imports
    Rewriting_Properties
    Rewriting_LLRG_LV_Mondaic
begin

lemma llrg_linear_sys:
  "llrg \<R> \<Longrightarrow> linear_sys \<R>"
  by (auto simp: llrg_def)

section \<open>LLRG results\<close>

lemma llrg_commute:
  assumes sig: "funas_rel \<R> \<subseteq> \<F>" "funas_rel \<S> \<subseteq> \<F>"
   and fresh: "(c, 0) \<notin> \<F>"
   and llrg: "llrg \<R>" "llrg \<S>"
   and com: "commute (gsrstep (insert (c, 0) \<F>) \<R>) (gsrstep (insert (c, 0) \<F>) \<S>)"
  shows "commute (srstep \<F> \<R>) (srstep \<F> \<S>)"
proof -
  let ?\<sigma> = "\<lambda> _. Fun c []" let ?\<H> = "insert (c, 0) \<F>"
  from fresh have fresh_sys: "(c, 0) \<notin> funas_rel \<S>" "(c, 0) \<notin> funas_rel (\<R>\<inverse>)" using sig
    by (auto simp: funas_rel_def)
  have linear: "linear_sys \<S>" "linear_sys (\<R>\<inverse>)" using llrg unfolding llrg_def by auto
  have sig': "funas_rel \<S> \<subseteq> \<F>" "funas_rel (\<R>\<inverse>) \<subseteq> \<F>" using sig by (auto simp: funas_rel_def)
  have mono: "\<F> \<subseteq> ?\<H>" by auto
  {fix s t assume ass: "(s, t) \<in> comp_rrstep_rel' \<F> (\<R>\<inverse>) \<S>"
    from ass have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>"
      by (metis Un_iff relcomp.cases srstepsD srsteps_with_root_step_srstepsD)+
    from ass have m: "(s, t) \<in> (srstep ?\<H> (\<R>\<inverse>))\<^sup>* O (srstep ?\<H> \<S>)\<^sup>*"
      using rtrancl_mono[OF sig_step_mono[OF mono]]
      by (auto dest!: srsteps_with_root_step_sresteps_eqD trancl_into_rtrancl)
    have gr: "ground s \<or> ground t" using ass llrg 
      unfolding srstep_converse_dist trancl_converse
      by (auto simp: llrg_srsteps_with_root_step_inv_ground llrg_srsteps_with_root_step_ground)
    have gstep: "(s \<cdot> ?\<sigma>, t \<cdot> ?\<sigma>) \<in> (gsrstep ?\<H> \<S>)\<^sup>* O (gsrstep ?\<H> (\<R>\<inverse>))\<^sup>*"
      using srsteps_eq_subst_relcomp_closed[OF m, THEN srsteps_eq_relcomp_gsrsteps_relcomp, of ?\<sigma>,
        THEN subsetD[OF com[unfolded commute_def], unfolded rew_converse_inwards]]
      by (auto simp: ground_substI)
    have [simp]: "ground s \<Longrightarrow> (c, 0) \<notin> funas_term s" "ground t \<Longrightarrow> (c, 0) \<notin> funas_term t"
      using funas fresh by auto
    have "(s, t) \<in> (rstep \<S>)\<^sup>* O (rstep (\<R>\<inverse>))\<^sup>*"
      using remove_const_subst_relcomp_lhs[OF linear fresh_sys, of t s]
      using gsrsteps_eq_relcomp_to_rsteps_relcomp[OF gstep] gr
      using remove_const_subst_relcomp_lhs[OF linear fresh_sys, of t s]
      using remove_const_subst_relcomp_rhs[OF linear fresh_sys, of s t]
        by (cases "ground s") (simp_all add: ground_subst_apply)
    from rsteps_eq_relcomp_srsteps_eq_relcompI[OF sig' funas this]
    have "commute_redp \<F> \<R> \<S> s t" unfolding commute_redp_def
      by (simp add: rew_converse_inwards)}
  then show ?thesis by (intro commute_rrstep_intro) simp
qed

lemma llrg_CR:
  assumes sig: "funas_rel \<R> \<subseteq> \<F>"
   and fresh: "(c, 0) \<notin> \<F>"
   and llrg: "llrg \<R>"
   and com: "CR (gsrstep (insert (c, 0) \<F>) \<R>)"
  shows "CR (srstep \<F> \<R>)"
  using assms llrg_commute unfolding CR_iff_self_commute
  by metis


lemma llrg_SCR:
  assumes sig: "funas_rel \<R> \<subseteq> \<F>" and fresh: "(c, 0) \<notin> \<F>"
   and llrg: "llrg \<R>"
   and scr: "SCR (gsrstep (insert (c, 0) \<F>) \<R>)"
  shows "SCR (srstep \<F> \<R>)"
proof -
  let ?\<sigma> = "const_subst c" let ?\<H> = "insert (c, 0) \<F>"
  from fresh have fresh_sys: "(c, 0) \<notin> funas_rel \<R>" using sig
    by (auto simp: funas_rel_def)
  have mono: "\<F> \<subseteq> ?\<H>" by auto note sig_trans = subsetD[OF srstep_monp[OF mono]]
  {fix s t u assume ass: "(s, t) \<in> srstep \<F> \<R>" "(s, u) \<in> srstep \<F> \<R>"
    and root: "(s, t) \<in> sig_step \<F> (rrstep \<R>) \<or> (s, u) \<in> sig_step \<F> (rrstep \<R>)"
    from ass have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>" "funas_term u \<subseteq> \<F>"
      by (force dest: sig_stepE)+
    from root have gr: "ground t \<or> ground u" using ass llrg llrg_rrsteps_groundness
      unfolding srstep_converse_dist trancl_converse by blast
    have *: "ground (s \<cdot> ?\<sigma>)" "ground (t \<cdot> ?\<sigma>)" "ground (u \<cdot> ?\<sigma>)" by auto
    from this scr obtain v where v: "(t \<cdot> ?\<sigma>, v) \<in> (gsrstep ?\<H> \<R>)\<^sup>= \<and> (u \<cdot> ?\<sigma>, v) \<in> (gsrstep ?\<H> \<R>)\<^sup>*"
      using srstep_subst_closed[OF sig_trans[OF ass(1)], of ?\<sigma>]
      using srstep_subst_closed[OF sig_trans[OF ass(2)], of ?\<sigma>]
      using ass unfolding SCR_on_def
      by auto (metis (no_types, lifting) * )
    then have fv: "funas_term v \<subseteq> \<F>" using gr llrg_funas_term_step_pres[OF llrg, of _ v]
      using llrg_funas_term_steps_pres[OF llrg, of _ v] funas sig
      by (auto simp: ground_subst_apply elim!: sig_stepE dest!: gsrsteps_eq_to_rsteps_eq) blast+
    then have c_free: "(c, 0) \<notin> funas_term v" using fresh by blast
    then have "v = t \<cdot> const_subst c \<Longrightarrow> ground t" using arg_cong[of v "t \<cdot> ?\<sigma>" funas_term]
      by (auto simp: funas_term_subst vars_term_empty_ground split: if_splits)
    from this v have "(t, v) \<in> (srstep \<F> \<R>)\<^sup>=" "(u, v) \<in> (srstep \<F> \<R>)\<^sup>*"
      using remove_const_subst_steps_eq_lhs[OF llrg_linear_sys[OF llrg] fresh_sys c_free, of u,
        THEN rsteps_eq_srsteps_eqI[OF sig funas(3) fv]]
      using remove_const_subst_step_lhs[OF llrg_linear_sys[OF llrg] fresh_sys c_free, of t,
        THEN sig_stepI[OF funas(2) fv]]
      by (auto simp: ground_subst_apply dest: srstepD gsrsteps_eq_to_rsteps_eq)
    then have "SCRp \<F> \<R> t u" by blast}
  then show ?thesis by (intro SCR_rrstep_intro) (metis srrstep_to_srestep)+ 
qed

lemma llrg_WCR:
  assumes sig: "funas_rel \<R> \<subseteq> \<F>" and fresh: "(c, 0) \<notin> \<F>"
   and llrg: "llrg \<R>"
   and wcr: "WCR (gsrstep (insert (c, 0) \<F>) \<R>)"
  shows "WCR (srstep \<F> \<R>)"
proof -
  let ?\<sigma> = "const_subst c" let ?\<H> = "insert (c, 0) \<F>"
  from fresh have fresh_sys: "(c, 0) \<notin> funas_rel \<R>" "(c, 0) \<notin> funas_rel (\<R>\<inverse>)" using sig
    by (auto simp: funas_rel_def)
  have lin: "linear_sys \<R>" "linear_sys (\<R>\<inverse>)" using llrg unfolding llrg_def by auto
  have mono: "\<F> \<subseteq> ?\<H>" by auto note sig_trans = subsetD[OF srstep_monp[OF mono]]
  {fix s t u assume ass: "(s, t) \<in> sig_step \<F> (rrstep \<R>)" "(s, u) \<in> srstep \<F> \<R>"
    from ass have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>" "funas_term u \<subseteq> \<F>"
      by blast+
    then have c_free: "(c, 0) \<notin> funas_term t" using fresh by blast
    from ass have gr: "ground t" using ass llrg llrg_rrsteps_groundness by blast
    have *: "ground (s \<cdot> ?\<sigma>)" "ground (u \<cdot> ?\<sigma>)" by auto
    from this wcr have w: "(t, u \<cdot> ?\<sigma>) \<in> (gsrstep ?\<H> \<R>)\<^sup>\<down>"
      using srstep_subst_closed[OF sig_trans[OF srrstep_to_srestep[OF ass(1)]], of ?\<sigma>]
      using srstep_subst_closed[OF sig_trans[OF ass(2)], of ?\<sigma>]
      using ass unfolding WCR_on_def
      by auto (metis * gr ground_subst_apply)
    have "(t, u) \<in> (srstep \<F> \<R>)\<^sup>\<down>" unfolding join_def
      using remove_const_subst_relcomp_rhs[OF lin fresh_sys c_free
        gsrsteps_eq_relcomp_to_rsteps_relcomp[OF w[unfolded join_def rew_converse_inwards]],
        THEN rsteps_eq_relcomp_srsteps_eq_relcompI[OF sig funas_rel_converse[OF sig] funas(2-)]]
      by (metis (no_types, lifting) srstep_converse_dist)}
  then show ?thesis by (intro WCR_rrstep_intro) simp
qed


lemma llrg_UNF:
  assumes sig: "funas_rel \<R> \<subseteq> \<F>" and fresh: "(c, 0) \<notin> \<F>"
   and llrg: "llrg \<R>"
   and unf: "UNF (gsrstep (insert (c, 0) \<F>) \<R>)"
  shows "UNF (srstep \<F> \<R>)"
proof -
  let ?\<sigma> = "const_subst c" let ?\<H> = "insert (c, 0) \<F>"
  from fresh have fresh_sys: "(c, 0) \<notin> funas_rel \<R>" using sig
    by (auto simp: funas_rel_def)
  have mono: "\<F> \<subseteq> ?\<H>" by auto
  {fix s t assume ass: "(s, t) \<in> comp_rrstep_rel' \<F> (\<R>\<inverse>) \<R>"
    from ass have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>"
      by (metis Un_iff relcomp.cases srstepsD srsteps_with_root_step_srstepsD)+
    from ass have m: "(s, t) \<in> (srstep ?\<H> (\<R>\<inverse>))\<^sup>* O (srstep ?\<H> \<R>)\<^sup>*"
      using rtrancl_mono[OF sig_step_mono[OF mono]]
      by (auto dest!: srsteps_with_root_step_sresteps_eqD trancl_into_rtrancl)
    have gr: "ground s \<or> ground t" using ass llrg 
      unfolding srstep_converse_dist trancl_converse
      by (auto simp: llrg_srsteps_with_root_step_inv_ground llrg_srsteps_with_root_step_ground)
    have wit: "s \<cdot> ?\<sigma> \<in> NF (gsrstep ?\<H> \<R>) \<Longrightarrow> t \<cdot> ?\<sigma> \<in> NF (gsrstep ?\<H> \<R>) \<Longrightarrow> s \<cdot> ?\<sigma> = t \<cdot> ?\<sigma>" using unf
      using srsteps_eq_subst_relcomp_closed[OF m, THEN srsteps_eq_relcomp_gsrsteps_relcomp, of ?\<sigma>]
      by (auto simp: UNF_on_def rew_converse_outwards normalizability_def)
    from funas NF_to_fresh_const_subst_NF[OF llrg_linear_sys[OF llrg] fresh_sys sig(1)]
    have "s \<in> NF (srstep \<F> \<R>) \<Longrightarrow> s \<cdot> ?\<sigma> \<in> NF (gsrstep ?\<H> \<R>)" "t \<in> NF (srstep \<F> \<R>) \<Longrightarrow> t \<cdot> ?\<sigma> \<in> NF (gsrstep ?\<H> \<R>)"
      by auto
    moreover have "s \<cdot> ?\<sigma> = t \<cdot> ?\<sigma> \<Longrightarrow> s = t" using gr funas fresh
      by (cases "ground s") (auto simp: ground_subst_apply funas_term_subst vars_term_empty_ground split: if_splits)
    ultimately have "UN_redp \<F> \<R> s t" using wit unfolding UN_redp_def
      by auto}
  then show ?thesis by (intro UNF_rrstep_intro) simp
qed


lemma llrg_NFP:
  assumes sig: "funas_rel \<R> \<subseteq> \<F>" and fresh: "(c, 0) \<notin> \<F>"
   and llrg: "llrg \<R>"
   and nfp: "NFP (gsrstep (insert (c, 0) \<F>) \<R>)"
  shows "NFP (srstep \<F> \<R>)"
proof -
  let ?\<sigma> = "const_subst c" let ?\<H> = "insert (c, 0) \<F>"
  from fresh have fresh_sys: "(c, 0) \<notin> funas_rel \<R>"
    using sig by (auto simp: funas_rel_def)
  have mono: "\<F> \<subseteq> ?\<H>" by auto
  {fix s t assume ass: "(s, t) \<in> comp_rrstep_rel' \<F> (\<R>\<inverse>) \<R>"
    from ass have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>"
      by (metis Un_iff relcomp.cases srstepsD srsteps_with_root_step_srstepsD)+
    from ass have m: "(s, t) \<in> (srstep ?\<H> (\<R>\<inverse>))\<^sup>* O (srstep ?\<H> \<R>)\<^sup>*"
      using rtrancl_mono[OF sig_step_mono[OF mono]]
      by (auto dest!: srsteps_with_root_step_sresteps_eqD trancl_into_rtrancl)
    have gr: "ground s \<or> ground t" using ass llrg 
      unfolding srstep_converse_dist trancl_converse
      by (auto simp: llrg_srsteps_with_root_step_inv_ground llrg_srsteps_with_root_step_ground)
    have wit: "t \<cdot> ?\<sigma> \<in> NF (gsrstep ?\<H> \<R>) \<Longrightarrow> (s \<cdot> ?\<sigma>, t \<cdot> ?\<sigma>) \<in> (gsrstep (insert (c, 0) \<F>) \<R>)\<^sup>*"
      using NFP_stepD[OF nfp]
      using srsteps_eq_subst_relcomp_closed[OF m, THEN srsteps_eq_relcomp_gsrsteps_relcomp, of ?\<sigma>]
      by (auto simp: rew_converse_outwards)
    from funas NF_to_fresh_const_subst_NF[OF llrg_linear_sys[OF llrg] fresh_sys(1) sig(1)]
    have "t \<in> NF (srstep \<F> \<R>) \<Longrightarrow> t \<cdot> ?\<sigma> \<in> NF (gsrstep ?\<H> \<R>)" by auto
    moreover have "(s \<cdot> ?\<sigma>, t \<cdot> ?\<sigma>) \<in> (rstep \<R>)\<^sup>* \<Longrightarrow> (s, t) \<in> (srstep \<F> \<R>)\<^sup>*" using gr funas fresh
      using remove_const_subst_steps_eq_lhs[OF llrg_linear_sys[OF llrg] fresh_sys, THEN rsteps_eq_srsteps_eqI[OF sig funas]]
      using remove_const_subst_steps_eq_rhs[OF llrg_linear_sys[OF llrg] fresh_sys, THEN rsteps_eq_srsteps_eqI[OF sig funas]]
      by (cases "ground s") (auto simp: ground_subst_apply)
    ultimately have "NFP_redp \<F> \<R> s t" using wit unfolding NFP_redp_def
      by (auto dest: gsrsteps_eq_to_rsteps_eq)}
  then show ?thesis by (intro NFP_rrstep_intro) simp
qed



lemma llrg_NE_aux:
  assumes "(s, t) \<in> srsteps_with_root_step \<F> \<R>"
   and  sig: "funas_rel \<R> \<subseteq> \<F>" "funas_rel \<S> \<subseteq> \<F>" and fresh: "(c, 0) \<notin> \<F>"
   and llrg: "llrg \<R>" "llrg \<S>"
   and ne: "NE (gsrstep (insert (c, 0) \<F>) \<R>) (gsrstep (insert (c, 0) \<F>) \<S>)"
  shows "NE_redp \<F> \<R> \<S> s t"
proof -
  from fresh have fresh_sys: "(c, 0) \<notin> funas_rel \<R>" "(c, 0) \<notin> funas_rel \<S>"
    using sig by (auto simp: funas_rel_def)
  let ?\<sigma> = "const_subst c" let ?\<H> = "insert (c, 0) \<F>"
  let ?\<H> = "insert (c, 0) \<F>"  have mono: "\<F> \<subseteq> ?\<H>" by auto
  from assms(1) have gr: "ground t" and funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>"
    using llrg_srsteps_with_root_step_ground[OF llrg(1)]
    by (meson srstepsD srsteps_with_root_step_srstepsD)+
  from funas have fresh_t: "(c, 0) \<notin> funas_term t" using fresh by auto
  from srsteps_subst_closed[OF srsteps_monp[OF mono, THEN subsetD, OF srsteps_with_root_step_srstepsD[OF assms(1)]], of ?\<sigma>]
  have "(s \<cdot> ?\<sigma>, t) \<in> (gsrstep?\<H> \<R>)\<^sup>+" using gr
    by (auto simp: ground_subst_apply intro!: ground_srsteps_gsrsteps)
  then have "t \<in> NF (srstep \<F> \<R>) \<Longrightarrow> (s \<cdot> ?\<sigma>, t) \<in> (gsrstep (insert (c, 0) \<F>) \<S>)\<^sup>*"
    using NF_to_fresh_const_subst_NF[OF llrg_linear_sys[OF llrg(1)] fresh_sys(1) sig(1) funas(2), of ?\<H>]
    using gr NE_NF_eq[OF ne, symmetric] ne unfolding NE_on_def
    by (auto simp: normalizability_def ground_subst_apply dest!: trancl_into_rtrancl)
  then show "NE_redp \<F> \<R> \<S> s t" unfolding NE_redp_def
    using remove_const_subst_steps_eq_lhs[OF llrg_linear_sys[OF llrg(2)] fresh_sys(2) fresh_t,
      THEN rsteps_eq_srsteps_eqI[OF sig(2) funas]]
    by (auto dest: gsrsteps_eq_to_rsteps_eq)
qed

lemma llrg_NE:
  assumes sig: "funas_rel \<R> \<subseteq> \<F>" "funas_rel \<S> \<subseteq> \<F>" and fresh: "(c, 0) \<notin> \<F>"
   and llrg: "llrg \<R>" "llrg \<S>"
   and ne: "NE (gsrstep (insert (c, 0) \<F>) \<R>) (gsrstep (insert (c, 0) \<F>) \<S>)"
  shows "NE (srstep \<F> \<R>) (srstep \<F> \<S>)"
proof -
  have f: "(c, 0) \<notin> funas_rel \<R>" "(c, 0) \<notin> funas_rel \<S>" using fresh sig
    by (auto simp: funas_rel_def)
  {fix s t assume "(s, t) \<in> srsteps_with_root_step \<F> \<R>"
    from llrg_NE_aux[OF this sig fresh llrg ne] have "NE_redp \<F> \<R> \<S> s t"
      by simp}
  moreover
  {fix s t assume "(s, t) \<in> srsteps_with_root_step \<F> \<S>"
    from llrg_NE_aux[OF this sig(2, 1) fresh llrg(2, 1) NE_symmetric[OF ne]]
    have "NE_redp \<F> \<S> \<R> s t" by simp}
  ultimately show ?thesis using linear_sys_gNF_eq_NF_eq[OF llrg_linear_sys[OF llrg(1)]
    llrg_linear_sys[OF llrg(2)] sig f _ _ NE_NF_eq[OF ne]]
    by (intro NE_rrstep_intro) auto
qed

subsection \<open>Specialized for monadic signature\<close>

lemma monadic_commute:
  assumes "llrg \<R>" "llrg \<S>" "monadic \<F>"
   and com: "commute (gsrstep \<F> \<R>) (gsrstep \<F> \<S>)"
  shows "commute (srstep \<F> \<R>) (srstep \<F> \<S>)"
proof -
  {fix s t assume ass: "(s, t) \<in> comp_rrstep_rel' \<F> (\<R>\<inverse>) \<S>"
    then obtain u where steps: "(s, u) \<in> (srstep \<F> (\<R>\<inverse>))\<^sup>+" "(u, t) \<in> (srstep \<F> \<S>)\<^sup>+"
      by (auto simp: sig_step_converse_rstep dest: srsteps_with_root_step_srstepsD)
    have gr: "ground s" "ground t" using steps assms(1 - 3)
      unfolding rew_converse_outwards
      by (auto simp: llrg_srsteps_with_root_step_ground llrg_monadic_rsteps_groundness)
    from steps(1) have f: "funas_term s \<subseteq> \<F>" using srstepsD by blast 
    let ?\<sigma> = "\<lambda> _. s"
    from steps gr have "(s, u \<cdot> ?\<sigma>) \<in> (gsrstep \<F> (\<R>\<inverse>))\<^sup>+" "(u \<cdot> ?\<sigma>, t) \<in> (gsrstep \<F> \<S>)\<^sup>+"
      unfolding rew_converse_outwards
      using srsteps_subst_closed[where ?\<sigma> = ?\<sigma> and ?s = u, of _ \<F>] f
      by (force simp: ground_subst_apply intro: ground_srsteps_gsrsteps)+
    then have "(s, t) \<in> (gsrstep \<F> \<S>)\<^sup>* O (gsrstep \<F> (\<R>\<inverse>))\<^sup>*" using com
      unfolding commute_def rew_converse_inwards
      by (meson relcomp.relcompI subsetD trancl_into_rtrancl)
    from gsrsteps_eq_relcomp_srsteps_relcompD[OF this]
    have "commute_redp \<F> \<R> \<S> s t" unfolding commute_redp_def
      by (simp add: rew_converse_inwards)}
  then show ?thesis by (intro commute_rrstep_intro) simp
qed

lemma monadic_CR:
  assumes "llrg \<R>" "monadic \<F>"
   and "CR (gsrstep \<F> \<R>)"
  shows "CR (srstep \<F> \<R>)" using monadic_commute assms
  unfolding CR_iff_self_commute
  by blast


lemma monadic_SCR:
  assumes sig: "funas_rel \<R> \<subseteq> \<F>" "monadic \<F>"
   and llrg: "llrg \<R>"
   and scr: "SCR (gsrstep \<F> \<R>)"
  shows "SCR (srstep \<F> \<R>)"
proof -
  {fix s t u assume ass: "(s, t) \<in> srstep \<F> \<R>" "(s, u) \<in> srstep \<F> \<R>"
    and root: "(s, t) \<in> sig_step \<F> (rrstep \<R>) \<or> (s, u) \<in> sig_step \<F> (rrstep \<R>)"
    from ass have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>" "funas_term u \<subseteq> \<F>" by blast+
    from root have gr: "ground t" "ground u" using ass sig(2) llrg
      by (metis llrg_monadic_rstep_pres_groundness)+
    let ?\<sigma> = "\<lambda> _. t" have grs: "ground (s \<cdot> ?\<sigma>)" using gr by auto
    from this scr obtain v where v: "(t, v) \<in> (gsrstep \<F> \<R>)\<^sup>= \<and> (u, v) \<in> (gsrstep \<F> \<R>)\<^sup>*"
      using srstep_subst_closed[OF ass(1), of ?\<sigma>]
      using srstep_subst_closed[OF ass(2), of ?\<sigma>]
      using gr unfolding SCR_on_def
      by (metis Int_iff UNIV_I funas(2) ground_subst_apply mem_Collect_eq mem_Sigma_iff)
    then have "SCRp \<F> \<R> t u"
      by (metis Int_iff Un_iff gsrsteps_eq_to_srsteps_eq)}
  then show ?thesis by (intro SCR_rrstep_intro) (metis srrstep_to_srestep)+ 
qed

lemma monadic_WCR:
  assumes sig: "funas_rel \<R> \<subseteq> \<F>" "monadic \<F>"
   and llrg: "llrg \<R>"
   and wcr: "WCR (gsrstep \<F> \<R>)"
  shows "WCR (srstep \<F> \<R>)"
proof -
  {fix s t u assume ass: "(s, t) \<in> sig_step \<F> (rrstep \<R>)" "(s, u) \<in> srstep \<F> \<R>"
    from ass have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>" "funas_term u \<subseteq> \<F>" by blast+
    from srrstep_to_srestep ass have gr: "ground t" "ground u"using ass sig(2) llrg
      by (metis llrg_monadic_rstep_pres_groundness)+
    let ?\<sigma> = "\<lambda> _. t" have grs: "ground (s \<cdot> ?\<sigma>)" using gr by auto
    from this wcr have w: "(t, u) \<in> (gsrstep \<F> \<R>)\<^sup>\<down>" using gr ass(2) funas
      using srstep_subst_closed[OF srrstep_to_srestep[OF ass(1)], of ?\<sigma>]
      using srstep_subst_closed[OF ass(2), of ?\<sigma>]
      unfolding WCR_on_def
      by (metis IntI SigmaI UNIV_I ground_subst_apply mem_Collect_eq)
    then have "(t, u) \<in> (srstep \<F> \<R>)\<^sup>\<down>" unfolding join_def
      by (metis gsrsteps_eq_to_srsteps_eq joinD joinI join_def)}
  then show ?thesis by (intro WCR_rrstep_intro) simp
qed

lemma monadic_UNF:
  assumes "llrg \<R>" "monadic \<F>"
   and unf: "UNF (gsrstep \<F> \<R>)"
  shows "UNF (srstep \<F> \<R>)"
proof -
  {fix s t assume ass: "(s, t) \<in> comp_rrstep_rel' \<F> (\<R>\<inverse>) \<R>"
    then obtain u where steps: "(s, u) \<in> (srstep \<F> (\<R>\<inverse>))\<^sup>+" "(u, t) \<in> (srstep \<F> \<R>)\<^sup>+"
      by (auto simp: sig_step_converse_rstep dest: srsteps_with_root_step_srstepsD)
    have gr: "ground s" "ground t" using steps assms(1, 2)
      unfolding rew_converse_outwards
      by (auto simp: llrg_srsteps_with_root_step_ground llrg_monadic_rsteps_groundness)
    from steps(1) have f: "funas_term s \<subseteq> \<F>" using srstepsD by blast 
    let ?\<sigma> = "\<lambda> _. s"
    from steps gr have "(s, u \<cdot> ?\<sigma>) \<in> (gsrstep \<F> (\<R>\<inverse>))\<^sup>+" "(u \<cdot> ?\<sigma>, t) \<in> (gsrstep \<F> \<R>)\<^sup>+"
      unfolding rew_converse_outwards
      using srsteps_subst_closed[where ?\<sigma> = ?\<sigma> and ?s = u, of _ \<F>] f
      by (force simp: ground_subst_apply intro: ground_srsteps_gsrsteps)+
    then have "UN_redp \<F> \<R> s t" using unf ground_NF_srstep_gsrstep[OF gr(1), of \<F> \<R>]
      using ground_NF_srstep_gsrstep[OF gr(2), of \<F> \<R>]
        by (auto simp: UNF_on_def UN_redp_def normalizability_def rew_converse_outwards)
           (meson trancl_into_rtrancl)}
  then show ?thesis by (intro UNF_rrstep_intro) simp
qed


lemma monadic_UNC:
  assumes "llrg \<R>" "monadic \<F>"
   and well: "funas_rel \<R> \<subseteq> \<F>"
   and unc: "UNC (gsrstep \<F> \<R>)"
  shows "UNC (srstep \<F> \<R>)"
proof -
  {fix s t assume ass: "(s, t) \<in> (srstep \<F> \<R>)\<^sup>\<leftrightarrow>\<^sup>*" "s \<in> NF (srstep \<F> \<R>)" "t \<in> NF (srstep \<F> \<R>)"
    then have "s = t"
    proof (cases "s = t")
      case False
      then have "\<exists> s' t'. (s, t) \<in> (srstep \<F> \<R>)\<^sup>\<leftrightarrow>\<^sup>* \<and> (s', s) \<in> (srstep \<F> \<R>) \<and> (t', t) \<in> (srstep \<F> \<R>)"
        using ass by (auto simp: conversion_def rtrancl_eq_or_trancl dest: tranclD tranclD2)
      then obtain s' t' where split: "(s, t) \<in> (srstep \<F> \<R>)\<^sup>\<leftrightarrow>\<^sup>*" "(s', s) \<in> (srstep \<F> \<R>)" "(t', t) \<in> (srstep \<F> \<R>)" by blast
      from split(2, 3) have gr: "ground s" "ground t" using llrg_monadic_rstep_pres_groundness[OF assms(1, 2)]
        by blast+
      from ground_srsteps_eq_gsrsteps_eq[OF this ass(1)[unfolded sig_step_conversion_dist]]
      have "(s, t) \<in> (gsrstep \<F> \<R>)\<^sup>\<leftrightarrow>\<^sup>*"
        unfolding conversion_def Restr_smycl_dist
        by (simp add: rstep_converse_dist srstep_symcl_dist)
      then show ?thesis using ass(2-) unc gr
        by (auto simp: UNC_def ground_NF_srstep_gsrstep)
    qed auto}
  then show ?thesis by (auto simp: UNC_def UN_redp_def)
qed


lemma monadic_NFP:
  assumes "llrg \<R>" "monadic \<F>"
   and nfp: "NFP (gsrstep \<F> \<R>)"
  shows "NFP (srstep \<F> \<R>)"
proof -
  {fix s t u assume ass: "(s, t) \<in> (srstep \<F> \<R>)\<^sup>*" "(s, u) \<in> (srstep \<F> \<R>)\<^sup>*" "u \<in> NF (srstep \<F> \<R>)"
    have "(t, u) \<in> (srstep \<F> \<R>)\<^sup>*"
    proof (cases "s = u \<or> s = t")
      case [simp]: True show ?thesis using ass
        by (metis NF_not_suc True rtrancl.rtrancl_refl)
    next
      case False
      then have steps:"(s, t) \<in> (srstep \<F> \<R>)\<^sup>+" "(s, u) \<in> (srstep \<F> \<R>)\<^sup>+" using ass(1, 2)
        by (auto simp add: rtrancl_eq_or_trancl)
      then have gr: "ground t" "ground u" using assms(1, 2) llrg_monadic_rsteps_groundness
        by blast+
      let ?\<sigma> = "\<lambda> _. t" from steps gr have "(s \<cdot> ?\<sigma>, t) \<in> (gsrstep \<F> \<R>)\<^sup>+" "(s \<cdot> ?\<sigma>, u) \<in> (gsrstep \<F> \<R>)\<^sup>+"
        by (auto intro!: ground_srsteps_gsrsteps)
           (metis ground_subst_apply srstepsD srsteps_subst_closed)+
      then have "(t, u) \<in> (gsrstep \<F> \<R>)\<^sup>*" using nfp ass(3) gr
        by (auto simp: NFP_on_def) (metis ground_NF_srstep_gsrstep normalizability_I trancl_into_rtrancl)
      then show ?thesis by (auto dest: gsrsteps_eq_to_srsteps_eq)
    qed}
  then show ?thesis unfolding NFP_on_def
    by auto
qed


end