section \<open>Rewriting\<close>
theory Rewriting
  imports Terms_Positions
begin

subsection \<open>Basic rewrite definitions\<close>

subsubsection \<open>Rewrite steps with implicit signature declaration (encoded in the type)\<close>

inductive_set rrstep :: "('f, 'v) term rel \<Rightarrow> ('f, 'v) term rel" for \<R> where
  [intro]: "(l, r) \<in> \<R> \<Longrightarrow> (l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> rrstep \<R>"

inductive_set rstep :: "('f, 'v) term rel \<Rightarrow> ('f, 'v) term rel" for \<R> where
  "(s, t) \<in> rrstep \<R> \<Longrightarrow> (C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> rstep \<R>"


subsubsection \<open>Restrict relations to terms induced by a given signature\<close>

definition "sig_step \<F> \<R> = Restr \<R> (Collect (\<lambda> s. funas_term s \<subseteq> \<F>))"

subsubsection \<open>Rewriting under a given signature/restricted to ground terms\<close>

abbreviation "srrstep \<F> \<R> \<equiv> sig_step \<F> (rrstep \<R>)"
abbreviation "srstep \<F> \<R> \<equiv> sig_step \<F> (rstep \<R>)"
abbreviation "gsrstep \<F> \<R> \<equiv> Restr (sig_step \<F> (rstep \<R>)) (Collect ground)"


subsubsection \<open>Rewriting sequences involving a root step\<close>

abbreviation (input) relto :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "relto R S \<equiv> S^* O R O S^*"
definition "srsteps_with_root_step \<F> \<R> \<equiv> relto (sig_step \<F> (rrstep \<R>)) (srstep \<F> \<R>)"


subsection \<open>Monotonicity laws\<close>

lemma Restr_mono: "Restr r A \<subseteq> r" by auto

lemma Restr_trancl_mono_set: "(Restr r A)\<^sup>+ \<subseteq> A \<times> A"
  by (simp add: trancl_subset_Sigma)

lemma rrstep_rstep_mono: "rrstep \<R> \<subseteq> rstep \<R>"
  by (auto intro: rstep.intros[where ?C = \<box>, simplified])

lemma sig_step_mono:
  "\<F> \<subseteq> \<G> \<Longrightarrow> sig_step \<F> \<R> \<subseteq> sig_step \<G> \<R>"
  by (auto simp: sig_step_def)

lemma sig_step_mono2:
  "\<R> \<subseteq> \<L> \<Longrightarrow> sig_step \<F> \<R> \<subseteq> sig_step \<F> \<L>"
  by (auto simp: sig_step_def)

lemma srrstep_monp:
  "\<F> \<subseteq> \<G> \<Longrightarrow> srrstep \<F> \<R> \<subseteq> srrstep \<G> \<R>"
  by (simp add: sig_step_mono)

lemma srstep_monp:
  "\<F> \<subseteq> \<G> \<Longrightarrow> srstep \<F> \<R> \<subseteq> srstep \<G> \<R>"
  by (simp add: sig_step_mono)

lemma srsteps_monp:
  "\<F> \<subseteq> \<G> \<Longrightarrow> (srstep \<F> \<R>)\<^sup>+ \<subseteq> (srstep \<G> \<R>)\<^sup>+"
  by (simp add: sig_step_mono trancl_mono_set)

lemma srsteps_eq_monp:
  "\<F> \<subseteq> \<G> \<Longrightarrow> (srstep \<F> \<R>)\<^sup>* \<subseteq> (srstep \<G> \<R>)\<^sup>*"
  by (meson rtrancl_mono sig_step_mono subrelI subsetD trancl_into_rtrancl)
  
lemma srsteps_with_root_step_sig_mono:
   "\<F> \<subseteq> \<G> \<Longrightarrow> srsteps_with_root_step \<F> \<R> \<subseteq> srsteps_with_root_step \<G> \<R>"
  unfolding srsteps_with_root_step_def
  by (simp add: relcomp_mono srrstep_monp srsteps_eq_monp)


subsection \<open>Introduction, elimination, and destruction rules for @{const sig_step}, @{const rstep}, @{const rrstep},
   @{const srrstep}, and @{const srstep}\<close>

lemma sig_stepE [elim, consumes 1]:
  "(s, t) \<in> sig_step \<F> \<R> \<Longrightarrow> \<lbrakk>(s, t) \<in> \<R> \<Longrightarrow> funas_term s \<subseteq> \<F> \<Longrightarrow> funas_term t \<subseteq> \<F> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: sig_step_def)

lemma sig_stepI [intro]:
  "funas_term s \<subseteq> \<F> \<Longrightarrow> funas_term t \<subseteq> \<F> \<Longrightarrow> (s, t) \<in> \<R> \<Longrightarrow> (s, t) \<in> sig_step \<F> \<R>"
  by (auto simp: sig_step_def)

lemma rrstep_subst [elim, consumes 1]:
  assumes "(s, t) \<in> rrstep \<R>"
  obtains l r \<sigma> where "(l, r) \<in> \<R>" "s = l \<cdot> \<sigma>" "t = r \<cdot> \<sigma>" using assms
  by (meson rrstep.simps)
  
lemma rstep_imp_C_s_r:
  assumes "(s, t) \<in> rstep \<R>"
  shows "\<exists>C \<sigma> l r. (l,r) \<in> \<R> \<and> s = C\<langle>l\<cdot>\<sigma>\<rangle> \<and> t = C\<langle>r\<cdot>\<sigma>\<rangle>"using assms
  by (metis rrstep.cases rstep.simps)

  
lemma rstep_imp_C_s_r' [elim, consumes 1]:
  assumes "(s, t) \<in> rstep \<R>"
  obtains C l r \<sigma> where "(l,r) \<in> \<R>" "s = C\<langle>l\<cdot>\<sigma>\<rangle>" "t = C\<langle>r\<cdot>\<sigma>\<rangle>" using assms
  using rstep_imp_C_s_r by blast

lemma rrstep_basicI [intro]:
  "(l, r) \<in> \<R> \<Longrightarrow> (l, r) \<in> rrstep \<R>"
  by (metis rrstepp.intros rrstepp_rrstep_eq subst_apply_term_empty)

lemma rstep_ruleI [intro]:
  "(l, r) \<in> \<R> \<Longrightarrow> (l, r) \<in> rstep \<R>"
  using rrstep_rstep_mono by blast

lemma rstepI [intro]:
  "(l, r) \<in> \<R> \<Longrightarrow> s = C\<langle>l \<cdot> \<sigma>\<rangle> \<Longrightarrow> t = C\<langle>r \<cdot> \<sigma>\<rangle> \<Longrightarrow> (s, t) \<in> rstep \<R>"
  by (simp add: rrstep.intros rstep.intros)

lemma rstep_substI [intro]:
  "(s, t) \<in> rstep \<R> \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> rstep \<R>"
  by (auto elim!: rstep_imp_C_s_r' simp flip: subst_subst_compose)

lemma rstep_ctxtI [intro]:
  "(s, t) \<in> rstep \<R> \<Longrightarrow> (C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> rstep \<R>"
  by (auto elim!: rstep_imp_C_s_r' simp flip: ctxt_ctxt_compose)

lemma srrstepD:
  "(s, t) \<in> srrstep \<F> \<R> \<Longrightarrow> (s, t) \<in> rrstep \<R> \<and> funas_term s \<subseteq> \<F> \<and> funas_term t \<subseteq> \<F>"
  by (auto simp: sig_step_def)

lemma srstepD:
  "(s, t) \<in> (srstep \<F> \<R>) \<Longrightarrow> (s, t) \<in> rstep \<R> \<and> funas_term s \<subseteq> \<F> \<and> funas_term t \<subseteq> \<F>"
  by (auto simp: sig_step_def)

lemma srstepsD:
  "(s, t) \<in> (srstep \<F> \<R>)\<^sup>+ \<Longrightarrow> (s, t) \<in> (rstep \<R>)\<^sup>+ \<and> funas_term s \<subseteq> \<F> \<and> funas_term t \<subseteq> \<F>"
  unfolding sig_step_def using trancl_mono_set[OF Restr_mono] 
  by (auto simp: sig_step_def dest: subsetD[OF Restr_trancl_mono_set])


subsubsection \<open>Transitive and relfexive closure distribution over @{const sig_step}\<close>

lemma funas_rel_converse:
  "funas_rel \<R> \<subseteq> \<F> \<Longrightarrow> funas_rel (\<R>\<inverse>) \<subseteq> \<F>" unfolding funas_rel_def
  by auto

lemma rstep_term_to_sig_r:
  assumes "(s, t) \<in> rstep \<R>" and "funas_rel \<R> \<subseteq> \<F>" and "funas_term s \<subseteq> \<F>"
  shows "(s, term_to_sig \<F> v t) \<in> rstep \<R>"
proof -
  from assms(1) obtain C l r \<sigma> where
    *: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>" "(l, r) \<in> \<R>" by auto
  from assms(2, 3) *(3) have "funas_ctxt C \<subseteq> \<F>" "funas_term l \<subseteq> \<F>" "funas_term r \<subseteq> \<F>"
    by (auto simp: *(1) funas_rel_def funas_term_subst subset_eq)
  then have "(term_to_sig \<F> v s, term_to_sig \<F> v t) \<in> rstep \<R>" using *(3)
    by (auto simp: *(1, 2) funas_ctxt_ctxt_well_def_hole_path)
  then show ?thesis using assms(3) by auto
qed

lemma rstep_term_to_sig_l:
  assumes "(s, t) \<in> rstep \<R>" and "funas_rel \<R> \<subseteq> \<F>" and "funas_term t \<subseteq> \<F>"
  shows "(term_to_sig \<F> v s, t) \<in> rstep \<R>"
proof -
  from assms(1) obtain C l r \<sigma> where
    *: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>" "(l, r) \<in> \<R>" by auto
  from assms(2, 3) *(3) have "funas_ctxt C \<subseteq> \<F>" "funas_term l \<subseteq> \<F>" "funas_term r \<subseteq> \<F>"
    by (auto simp: *(2) funas_rel_def funas_term_subst subset_eq)
  then have "(term_to_sig \<F> v s, term_to_sig \<F> v t) \<in> rstep \<R>" using *(3)
    by (auto simp: *(1, 2) funas_ctxt_ctxt_well_def_hole_path)
  then show ?thesis using assms(3) by auto
qed

lemma rstep_trancl_sig_step_r:
  assumes "(s, t) \<in> (rstep \<R>)\<^sup>+" and "funas_rel \<R> \<subseteq> \<F>" and "funas_term s \<subseteq> \<F>"
  shows "(s, term_to_sig \<F> v t) \<in> (srstep \<F> \<R>)\<^sup>+" using assms
proof (induct)
  case (base t)
  then show ?case using subsetD[OF fuans_term_term_to_sig, of _ \<F> v]
    by (auto simp: rstep_term_to_sig_r sig_step_def intro!: r_into_trancl)
next
  case (step t u)
  then have st: "(s, term_to_sig \<F> v t) \<in> (srstep \<F> \<R>)\<^sup>+" by auto
  from step(2) obtain  C l r \<sigma> where
    *: "t = C\<langle>l \<cdot> \<sigma>\<rangle>" "u = C\<langle>r \<cdot> \<sigma>\<rangle>" "(l, r) \<in> \<R>" by auto
  show ?case
  proof (cases "ctxt_well_def_hole_path \<F> C")
    case True
    from *(3) step(4) have "funas_term l \<subseteq> \<F>" "funas_term r \<subseteq> \<F>" by (auto simp: funas_rel_def)
    then have "(term_to_sig \<F> v t, term_to_sig \<F> v u) \<in> rstep \<R>"
      using True step(2) *(3) unfolding *
      by auto
    then have "(term_to_sig \<F> v t, term_to_sig \<F> v u) \<in> srstep \<F> \<R>"
      by (auto simp:_ sig_step_def)
    then show ?thesis using st by auto
  next
    case False
    then have "term_to_sig \<F> v t = term_to_sig \<F> v u" unfolding * by auto
    then show ?thesis using st by auto
  qed
qed

lemma rstep_trancl_sig_step_l:
  assumes "(s, t) \<in> (rstep \<R>)\<^sup>+" and "funas_rel \<R> \<subseteq> \<F>" and "funas_term t \<subseteq> \<F>"
  shows "(term_to_sig \<F> v s, t) \<in> (srstep \<F> \<R>)\<^sup>+" using assms
proof (induct rule: converse_trancl_induct)
  case (base t)
  then show ?case using subsetD[OF fuans_term_term_to_sig, of _ \<F> v]
    by (auto simp: rstep_term_to_sig_l sig_step_def intro!: r_into_trancl)
next
  case (step s u)
  then have st: "(term_to_sig \<F> v u, t) \<in> (srstep \<F> \<R>)\<^sup>+" by auto
  from step(1) obtain C l r \<sigma> where
    *: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "u = C\<langle>r \<cdot> \<sigma>\<rangle>" "(l, r) \<in> \<R>" by auto
  show ?case
  proof (cases "ctxt_well_def_hole_path \<F> C")
    case True
    from *(3) step(4) have "funas_term l \<subseteq> \<F>" "funas_term r \<subseteq> \<F>" by (auto simp: funas_rel_def)
    then have "(term_to_sig \<F> v s, term_to_sig \<F> v u) \<in> rstep \<R>"
      using True step(2) *(3) unfolding *
      by auto
    then have "(term_to_sig \<F> v s, term_to_sig \<F> v u) \<in> srstep \<F> \<R>"
      by (auto simp:_ sig_step_def)
    then show ?thesis using st by auto
  next
    case False
    then have "term_to_sig \<F> v s = term_to_sig \<F> v u" unfolding * by auto
    then show ?thesis using st by auto
  qed
qed

lemma rstep_srstepI [intro]:
  "funas_rel \<R> \<subseteq> \<F> \<Longrightarrow> funas_term s \<subseteq> \<F> \<Longrightarrow> funas_term t \<subseteq> \<F> \<Longrightarrow> (s, t) \<in> rstep \<R> \<Longrightarrow> (s, t) \<in> srstep \<F> \<R>"
  by blast

lemma rsteps_srstepsI [intro]:
  "funas_rel \<R> \<subseteq> \<F> \<Longrightarrow> funas_term s \<subseteq> \<F> \<Longrightarrow> funas_term t \<subseteq> \<F> \<Longrightarrow> (s, t) \<in> (rstep \<R>)\<^sup>+ \<Longrightarrow> (s, t) \<in> (srstep \<F> \<R>)\<^sup>+"
  using rstep_trancl_sig_step_r[of s t \<R> \<F>]
  by auto


lemma rsteps_eq_srsteps_eqI [intro]:
  "funas_rel \<R> \<subseteq> \<F> \<Longrightarrow> funas_term s \<subseteq> \<F> \<Longrightarrow> funas_term t \<subseteq> \<F> \<Longrightarrow> (s, t) \<in> (rstep \<R>)\<^sup>* \<Longrightarrow> (s, t) \<in> (srstep \<F> \<R>)\<^sup>*"
  by (auto simp add: rtrancl_eq_or_trancl)

lemma rsteps_eq_relcomp_srsteps_eq_relcompI [intro]:
  assumes "funas_rel \<R> \<subseteq> \<F>" "funas_rel \<S> \<subseteq> \<F>"
    and funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>"
    and steps: "(s, t) \<in> (rstep \<R>)\<^sup>* O (rstep \<S>)\<^sup>*"
  shows "(s, t) \<in> (srstep \<F> \<R>)\<^sup>* O (srstep \<F> \<S>)\<^sup>*"
proof -
  from steps obtain u where "(s, u) \<in> (rstep \<R>)\<^sup>*" "(u, t) \<in> (rstep \<S>)\<^sup>*" by auto
  then have "(s, term_to_sig \<F> v u) \<in> (srstep \<F> \<R>)\<^sup>*" "(term_to_sig \<F> v u, t) \<in> (srstep \<F> \<S>)\<^sup>*"
    using rstep_trancl_sig_step_l[OF _ assms(2) funas(2), of u v]
    using rstep_trancl_sig_step_r[OF _ assms(1) funas(1), of u v] funas
    by (auto simp: rtrancl_eq_or_trancl)
  then show ?thesis by auto
qed    


subsubsection \<open>Distributivity laws\<close>

lemma rstep_smycl_dist:
  "(rstep \<R>)\<^sup>\<leftrightarrow> = rstep (\<R>\<^sup>\<leftrightarrow>)"
  by (auto simp: sig_step_def)

lemma sig_step_symcl_dist:
  "(sig_step \<F> \<R>)\<^sup>\<leftrightarrow> = sig_step \<F> (\<R>\<^sup>\<leftrightarrow>)"
  by (auto simp: sig_step_def)

lemma srstep_symcl_dist:
  "(srstep \<F> \<R>)\<^sup>\<leftrightarrow> = srstep \<F> (\<R>\<^sup>\<leftrightarrow>)"
  by (auto simp: sig_step_def)

lemma Restr_smycl_dist:
  "(Restr \<R> \<A>)\<^sup>\<leftrightarrow> = Restr (\<R>\<^sup>\<leftrightarrow>) \<A>"
  by auto

lemmas rew_symcl_inwards = rstep_smycl_dist sig_step_symcl_dist srstep_symcl_dist Restr_smycl_dist
lemmas rew_symcl_outwards = rew_symcl_inwards[symmetric]

lemma rstep_converse_dist:
  "(rstep \<R>)\<inverse> = rstep (\<R>\<inverse>)"
  by auto

lemma srrstep_converse_dist:
  "(srrstep \<F> \<R>)\<inverse> = srrstep \<F> (\<R>\<inverse>)"
  by (fastforce simp: sig_step_def)

lemma sig_step_converse_rstep:
  "(srstep \<F> \<R>)\<inverse> = sig_step \<F> ((rstep \<R>)\<inverse>)"
  by (meson converse.simps set_eq_subset sig_stepE(1) sig_stepE sig_stepI subrelI)

lemma srstep_converse_dist:
  "(srstep \<F> \<R>)\<inverse> = srstep \<F> (\<R>\<inverse>)"
  by (auto simp: sig_step_def)

lemma Restr_converse: "(Restr \<R> A)\<inverse> = Restr (\<R>\<inverse>) A"
  by auto

lemmas rew_converse_inwards = rstep_converse_dist srrstep_converse_dist sig_step_converse_rstep
   srstep_converse_dist Restr_converse trancl_converse[symmetric] rtrancl_converse[symmetric]
lemmas rew_converse_outwards = rew_converse_inwards[symmetric]

lemma sig_step_rsteps_dist:
  "funas_rel \<R> \<subseteq> \<F> \<Longrightarrow> sig_step \<F> ((rstep \<R>)\<^sup>+) = (srstep \<F> \<R>)\<^sup>+"
  by (auto elim!: sig_stepE dest: srstepsD)

lemma sig_step_rsteps_eq_dist:
  "funas_rel \<R> \<subseteq> \<F> \<Longrightarrow> sig_step \<F> ((rstep \<R>)\<^sup>+) \<union> Id = (srstep \<F> \<R>)\<^sup>*"
  by (auto simp: rtrancl_eq_or_trancl sig_step_rsteps_dist)

lemma sig_step_conversion_dist:
  "(srstep \<F> \<R>)\<^sup>\<leftrightarrow>\<^sup>* = (srstep \<F> (\<R>\<^sup>\<leftrightarrow>))\<^sup>*"
  by (auto simp: rtrancl_eq_or_trancl sig_step_rsteps_dist conversion_def srstep_symcl_dist)

lemma gsrstep_conversion_dist:
  "(gsrstep \<F> \<R>)\<^sup>\<leftrightarrow>\<^sup>* = (gsrstep \<F> (\<R>\<^sup>\<leftrightarrow>))\<^sup>*"
  by (auto simp: conversion_def rew_symcl_inwards)
                                                                                         
lemma sig_step_grstep_dist:
  "gsrstep \<F> \<R> = sig_step \<F> (Restr (rstep \<R>) (Collect ground))"
  by (auto simp: sig_step_def)

subsection \<open>Substitution closure of @{const srstep}\<close>

lemma srstep_subst_closed:
  assumes "(s, t) \<in> srstep \<F> \<R>" "\<And> x. funas_term (\<sigma> x) \<subseteq> \<F>"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> srstep \<F> \<R>" using assms
  by (auto simp: sig_step_def funas_term_subst)

lemma srsteps_subst_closed:
  assumes "(s, t) \<in> (srstep \<F> \<R>)\<^sup>+" "\<And> x. funas_term (\<sigma> x) \<subseteq> \<F>"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (srstep \<F> \<R>)\<^sup>+" using assms(1)
proof (induct rule: trancl.induct)
  case (r_into_trancl s t) show ?case
    using srstep_subst_closed[OF r_into_trancl assms(2)]
    by auto
next
  case (trancl_into_trancl s t u)
  from trancl_into_trancl(2) show ?case
    using srstep_subst_closed[OF trancl_into_trancl(3) assms(2)]
    by (meson rtrancl_into_trancl1 trancl_into_rtrancl)  
qed

lemma srsteps_eq_subst_closed:
  assumes "(s, t) \<in> (srstep \<F> \<R>)\<^sup>*" "\<And> x. funas_term (\<sigma> x) \<subseteq> \<F>"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (srstep \<F> \<R>)\<^sup>*" using assms srsteps_subst_closed
  by (metis rtrancl_eq_or_trancl)

lemma srsteps_eq_subst_relcomp_closed:
  assumes "(s, t) \<in> (srstep \<F> \<R>)\<^sup>* O (srstep \<F> \<S>)\<^sup>*" "\<And> x. funas_term (\<sigma> x) \<subseteq> \<F>"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (srstep \<F> \<R>)\<^sup>* O (srstep \<F> \<S>)\<^sup>*"
proof -
  from assms(1) obtain u where "(s, u) \<in> (srstep \<F> \<R>)\<^sup>*" "(u, t) \<in> (srstep \<F> \<S>)\<^sup>*" by auto
  then have "(s \<cdot> \<sigma>, u \<cdot> \<sigma>) \<in> (srstep \<F> \<R>)\<^sup>*" "(u \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (srstep \<F> \<S>)\<^sup>*"
    using assms srsteps_eq_subst_closed
    by metis+
  then show ?thesis by auto
qed


subsection \<open>Context closure of @{const srstep}\<close>

lemma srstep_ctxt_closed:
  assumes "funas_ctxt C \<subseteq> \<F>" and "(s, t) \<in> srstep \<F> \<R>"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> srstep \<F> \<R>" using assms
  by (intro sig_stepI) (auto dest: srstepD)

lemma srsteps_ctxt_closed:
  assumes "funas_ctxt C \<subseteq> \<F>" and "(s, t) \<in> (srstep \<F> \<R>)\<^sup>+"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> (srstep \<F> \<R>)\<^sup>+" using assms(2) srstep_ctxt_closed[OF assms(1)]
  by (induct) force+

lemma srsteps_eq_ctxt_closed:
  assumes "funas_ctxt C \<subseteq> \<F>" and "(s, t) \<in> (srstep \<F> \<R>)\<^sup>*"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> (srstep \<F> \<R>)\<^sup>*" using srsteps_ctxt_closed[OF assms(1)] assms(2)
  by (metis rtrancl_eq_or_trancl)

lemma sig_steps_join_ctxt_closed:
  assumes "funas_ctxt C \<subseteq> \<F>" and "(s, t) \<in> (srstep \<F> \<R>)\<^sup>\<down>"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> (srstep \<F> \<R>)\<^sup>\<down>" using srsteps_eq_ctxt_closed[OF assms(1)] assms(2)
  unfolding join_def rew_converse_inwards
  by auto
                                 

text \<open>The following lemma shows that every rewrite sequence either contains a root step or is root stable\<close>

lemma nsrsteps_with_root_step_step_on_args:
  assumes "(s, t) \<in> (srstep \<F> \<R>)\<^sup>+" "(s, t) \<notin> srsteps_with_root_step \<F> \<R>"
  shows "\<exists> f ss ts. s = Fun f ss \<and> t = Fun f ts \<and> length ss = length ts \<and>
    (\<forall> i < length ts. (ss ! i, ts ! i) \<in> (srstep \<F> \<R>)\<^sup>*)" using assms
proof (induct)
  case (base t)
  obtain C l r \<sigma> where [simp]: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>" and r: "(l, r) \<in> \<R>"
    using base(1) unfolding sig_step_def
    by blast
  then have funas: "funas_ctxt C \<subseteq> \<F>" "funas_term (l \<cdot> \<sigma>) \<subseteq> \<F>" "funas_term (r \<cdot> \<sigma>) \<subseteq> \<F>"
    using base(1) by (auto simp: sig_step_def)
  from funas(2-) r have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> srrstep \<F> \<R>"
    by (auto simp: sig_step_def)
  then have "C = Hole \<Longrightarrow> False" using base(2) r
    by (auto simp: srsteps_with_root_step_def)
  then obtain f ss D ts where [simp]: "C = More f ss D ts" by (cases C) auto
  have "(D\<langle>l \<cdot> \<sigma>\<rangle>, D\<langle>r \<cdot> \<sigma>\<rangle>) \<in> (srstep \<F> \<R>)" using base(1) r funas
    by (auto simp: sig_step_def)
  then show ?case using funas by (auto simp: nth_append_Cons)
next
  case (step t u) show ?case
  proof (cases "(s, t) \<in> srsteps_with_root_step \<F> \<R> \<or> (t, u) \<in> sig_step \<F> (rrstep \<R>)")
    case True then show ?thesis using step(1, 2, 4)
      by (auto simp add: relcomp3_I rtrancl.rtrancl_into_rtrancl srsteps_with_root_step_def)
  next
    case False
    obtain C l r \<sigma> where *[simp]: "t = C\<langle>l \<cdot> \<sigma>\<rangle>" "u = C\<langle>r \<cdot> \<sigma>\<rangle>" and r: "(l, r) \<in> \<R>"
      using step(2) unfolding sig_step_def by blast
    then have funas: "funas_ctxt C \<subseteq> \<F>" "funas_term (l \<cdot> \<sigma>) \<subseteq> \<F>" "funas_term (r \<cdot> \<sigma>) \<subseteq> \<F>"
      using step(2) by (auto simp: sig_step_def)
    from False have "C \<noteq> Hole" using funas r by (force simp: sig_step_def)
    then obtain f ss D ts where c[simp]: "C = More f ss D ts" by (cases C) auto
    from step(3, 1) False obtain g sss tss where
      **[simp]: "s = Fun g sss" "t = Fun g tss" and l: "length sss = length tss" and
      inv: "\<forall> i < length tss. (sss ! i, tss ! i) \<in> (srstep \<F> \<R>)\<^sup>*"
      by auto
    have [simp]: "g = f" and lc: "Suc (length ss + length ts) = length sss"
      using l *(1) unfolding c using **(2) by auto
    then have "\<forall> i < Suc (length ss + length ts). ((ss @ D\<langle>l \<cdot> \<sigma>\<rangle> # ts) ! i, (ss @ D\<langle>r \<cdot> \<sigma>\<rangle> # ts) ! i) \<in> (srstep \<F> \<R>)\<^sup>*"
      using * funas r by (auto simp: nth_append_Cons r_into_rtrancl rstep.intros rstepI sig_stepI)
    then have "i < length tss \<Longrightarrow> (sss ! i, (ss @ D\<langle>r \<cdot> \<sigma>\<rangle> # ts) ! i) \<in> (srstep \<F> \<R>)\<^sup>*" for i
      using inv * l lc funas **
      by (auto simp: nth_append_Cons simp del: ** * split!: if_splits)
    then show ?thesis using inv l lc * unfolding c
      by auto
  qed
qed

lemma rstep_to_pos_replace:
  assumes "(s, t) \<in> rstep \<R>"
  shows "\<exists> p l r \<sigma>. p \<in> poss s \<and> (l, r) \<in> \<R> \<and> s |_ p = l \<cdot> \<sigma> \<and> t = s[p \<leftarrow> r \<cdot> \<sigma>]"
proof -
  from assms obtain C l r \<sigma> where st: "(l, r) \<in> \<R>" "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    using rstep_imp_C_s_r by fastforce
  from st(2, 3) have *: "t = s[hole_pos C \<leftarrow> r \<cdot> \<sigma>]" by simp
  from this st show ?thesis unfolding *
    by (intro exI[of _ "hole_pos C"]) auto
qed

lemma pos_replace_to_rstep:
  assumes "p \<in> poss s" "(l, r) \<in> \<R>" 
    and "s |_ p = l \<cdot> \<sigma>" "t = s[p \<leftarrow> r \<cdot> \<sigma>]"
  shows "(s, t) \<in> rstep \<R>"
  using assms(1, 3-) replace_term_at_subt_at_id [of s p]
  by (intro rstepI[OF assms(2), of s "ctxt_at_pos s p" \<sigma>])
     (auto simp add: ctxt_of_pos_term_apply_replace_at_ident)

end