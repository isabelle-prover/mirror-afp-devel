(* License: LGPL *)

section \<open>\<open>\<eta>\<close>-Bisimilarity and \<open>\<eta>\<close>-Similarity\<close>

theory Eta_Bisimilarity
  imports Expressiveness_Price
begin

text \<open>
  \<open>\<eta>\<close>-Bisimilarity and \<open>\<eta>\<close>-Similarity are comparably arcane notions of behavioral equivalence. We show that they are characterized by coordinates \<^term>\<open>E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>\<close> and \<^term>\<open>E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0\<close> as an illustration of how to connect coordinates and relational characterizations of equivalences.
\<close>

subsection \<open>Definition and Properties of \<open>\<eta>\<close>-(Bi-)Similarity\<close>

context lts_tau
begin

text \<open>We characterize \<open>\<eta>\<close>-bisimilarity through symmetric \<open>\<eta>\<close>-simulations.\<close>

definition eta_simulation :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>eta_simulation R \<equiv> \<forall>p \<alpha> p' q. R p q \<longrightarrow> p \<mapsto> \<alpha> p' \<longrightarrow>
    (\<alpha> = \<tau> \<and> R p' q)
    \<or> (\<exists>q' q'' q'''. q \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> q'' \<Zsurj> q'''  \<and> R p q' \<and> R p' q''')\<close>

definition eta_bisimulated :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> (infix \<open>~\<eta>\<close> 40) where
  \<open>p ~\<eta> q \<equiv> \<exists>R. eta_simulation R \<and> symp R \<and> R p q\<close>

lemma eta_bisim_sim:
  shows \<open>eta_simulation (~\<eta>)\<close>
  unfolding eta_bisimulated_def eta_simulation_def by blast

lemma eta_bisim_sym:
  assumes \<open>p ~\<eta> q\<close>
  shows \<open>q ~\<eta> p\<close>
  using assms unfolding eta_bisimulated_def
  by (meson sympD)

lemma silence_retains_eta_sim:
assumes
  \<open>eta_simulation R\<close>
  \<open>R p q\<close>
  \<open>p \<Zsurj> p'\<close>
shows \<open>\<exists>q'. R p' q' \<and> q \<Zsurj> q'\<close>
  using assms(3,2)
proof (induct arbitrary: q)
  case (refl p)
  then show ?case
    using silent_reachable.refl by blast
next
  case (step p p' p'')
  then obtain q' where \<open>R p' q'\<close> \<open>q \<Zsurj> q'\<close>
    using \<open>eta_simulation R\<close> silent_reachable.refl
      silent_reachable_append_\<tau> silent_reachable_trans
    unfolding eta_simulation_def by blast
  then obtain q'' where \<open>R p'' q''\<close> \<open>q' \<Zsurj> q''\<close> using step by blast
  then show ?case
    using \<open>q \<Zsurj> q'\<close> silent_reachable_trans by blast
qed

lemma eta_bisimulated_silently_retained:
  assumes
    \<open>p ~\<eta> q\<close>
    \<open>p \<Zsurj> p'\<close>
  shows
    \<open>\<exists>q'. q \<Zsurj> q' \<and> p' ~\<eta> q'\<close> using assms(2,1)
  using silence_retains_eta_sim unfolding eta_bisimulated_def by blast

subsection \<open>Logical Characterization of \<open>\<eta>\<close>-Bisimilarity through Expressiveness Price\<close>

lemma logic_eta_bisim_invariant:
  assumes
    \<open>p0 ~\<eta> q0\<close>
    \<open>\<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
    \<open>p0 \<Turnstile>SRBB \<phi>\<close>
  shows \<open>q0 \<Turnstile>SRBB \<phi>\<close>
proof -
  have \<open>\<And>\<phi> \<chi> \<psi>.
    (\<forall>p q. p ~\<eta> q \<longrightarrow> \<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) \<longrightarrow> p \<Turnstile>SRBB \<phi> \<longrightarrow> q \<Turnstile>SRBB \<phi>) \<and>
    (\<forall>p q. p ~\<eta> q \<longrightarrow> \<chi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)
      \<longrightarrow> hml_srbb_inner_models p \<chi> \<longrightarrow> (\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>)) \<and>
    (\<forall>p q. p ~\<eta> q \<longrightarrow> \<psi> \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)
      \<longrightarrow> hml_srbb_conjunct_models p \<psi> \<longrightarrow> hml_srbb_conjunct_models q \<psi>)\<close>
  proof -
    fix \<phi> \<chi> \<psi>
    show
      \<open>(\<forall>p q. p ~\<eta> q \<longrightarrow> \<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) \<longrightarrow> p \<Turnstile>SRBB \<phi> \<longrightarrow> q \<Turnstile>SRBB \<phi>) \<and>
      (\<forall>p q. p ~\<eta> q \<longrightarrow> \<chi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)
        \<longrightarrow> hml_srbb_inner_models p \<chi> \<longrightarrow> (\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>)) \<and>
      (\<forall>p q. p ~\<eta> q \<longrightarrow> \<psi> \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)
        \<longrightarrow> hml_srbb_conjunct_models p \<psi> \<longrightarrow> hml_srbb_conjunct_models q \<psi>)\<close>
    proof (induct rule: hml_srbb_hml_srbb_inner_hml_srbb_conjunct.induct)
      case TT
      then show ?case by simp
    next
      case (Internal \<chi>)
      show ?case
      proof safe
        fix p q
        assume case_assms:
          \<open>p ~\<eta> q\<close> \<open>p \<Turnstile>SRBB hml_srbb.Internal \<chi>\<close> \<open>Internal \<chi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
        then obtain p' where p'_spec: \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' \<chi>\<close> by auto
        have \<open>\<chi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          using case_assms(3) unfolding \<O>_inner_def \<O>_def by auto
        hence \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>\<close>
          using Internal case_assms(1) p'_spec eta_bisimulated_silently_retained
          by (meson  silent_reachable_trans)
        thus \<open>q \<Turnstile>SRBB hml_srbb.Internal \<chi>\<close> by auto
      qed
    next
      case (ImmConj I \<Psi>)
      then show ?case unfolding \<O>_inner_def \<O>_def by auto
    next
      case (Obs \<alpha> \<phi>)
      then show ?case
      proof (safe)
        fix p q
        assume case_assms:
          \<open>p ~\<eta> q\<close>
          \<open>Obs \<alpha> \<phi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          \<open>hml_srbb_inner_models p (hml_srbb_inner.Obs \<alpha> \<phi>)\<close>
        hence \<open>\<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close> unfolding \<O>_inner_def \<O>_def by auto
        hence no_imm_conj: \<open>\<nexists>I \<Psi>. \<phi> = ImmConj I \<Psi> \<and> I \<noteq> {}\<close> unfolding \<O>_def by force
        have back_step: \<open>\<forall>p0 p1. p1 \<Turnstile>SRBB \<phi> \<longrightarrow> p0 \<Zsurj> p1 \<longrightarrow> p0 \<Turnstile>SRBB \<phi>\<close>
        proof (cases \<phi>)
          case TT
          then show ?thesis by auto
        next
          case (Internal _)
          then show ?thesis
            using silent_reachable_trans by auto
        next
          case (ImmConj _ _)
          then show ?thesis using no_imm_conj by auto
        qed
        from case_assms obtain p' where \<open>p \<mapsto>a \<alpha> p'\<close> \<open>p' \<Turnstile>SRBB \<phi>\<close> by auto
        then obtain q' q'' q''' where \<open>q \<Zsurj> q'\<close> \<open>q' \<mapsto>a \<alpha> q''\<close> \<open>q'' \<Zsurj> q'''\<close>  \<open>p' ~\<eta> q'''\<close>
          using \<open>p ~\<eta> q\<close> eta_bisim_sim unfolding eta_simulation_def
          using silent_reachable.refl by blast
        hence \<open>q''' \<Turnstile>SRBB \<phi>\<close>
          using \<open>p' \<Turnstile>SRBB \<phi>\<close> Obs \<open>\<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close> by blast
        hence \<open>hml_srbb_inner_models q' (hml_srbb_inner.Obs \<alpha> \<phi>)\<close>
          using \<open>q' \<mapsto>a \<alpha> q''\<close> \<open>q'' \<Zsurj> q'''\<close> back_step by auto
        thus \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' (hml_srbb_inner.Obs \<alpha> \<phi>)\<close>
          using \<open>q \<Zsurj> q'\<close> by blast
      qed
    next
      case (Conj I \<Psi>)
      show ?case
      proof safe
        fix p q
        assume case_assms:
          \<open>p ~\<eta> q\<close>
          \<open>Conj I \<Psi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          \<open>hml_srbb_inner_models p (Conj I \<Psi>)\<close>
        hence conj_price: \<open>\<forall>i\<in>I. \<Psi> i \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          unfolding \<O>_conjunct_def \<O>_inner_def
          by (simp, metis SUP_bot_conv(1) le_zero_eq sup_bot_left sup_ge1)
        from case_assms have \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<Psi> i)\<close> by auto
        hence \<open>\<forall>i\<in>I. hml_srbb_conjunct_models q (\<Psi> i)\<close>
          using Conj \<open>p ~\<eta> q\<close> conj_price by blast
        hence \<open>hml_srbb_inner_models q (hml_srbb_inner.Conj I \<Psi>)\<close> by simp
        thus \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' (hml_srbb_inner.Conj I \<Psi>)\<close>
          using silent_reachable.refl by blast
      qed
    next
      case (StableConj I \<Psi>)
      thus ?case unfolding \<O>_inner_def \<O>_def by auto
    next
      case (BranchConj \<alpha> \<phi> I \<Psi>)
      show ?case
      proof safe
        fix p q
        assume case_assms:
          \<open>p ~\<eta> q\<close>
          \<open>BranchConj \<alpha> \<phi> I \<Psi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          \<open>hml_srbb_inner_models p (BranchConj \<alpha> \<phi> I \<Psi>)\<close>
        hence \<open>\<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close> unfolding \<O>_inner_def \<O>_def
          by (simp, metis le_zero_eq sup_ge1)
        hence no_imm_conj: \<open>\<nexists>I \<Psi>. \<phi> = ImmConj I \<Psi> \<and> I \<noteq> {}\<close> unfolding \<O>_def by force
        have back_step: \<open>\<forall>p0 p1. p1 \<Turnstile>SRBB \<phi> \<longrightarrow> p0 \<Zsurj> p1 \<longrightarrow> p0 \<Turnstile>SRBB \<phi>\<close>
        proof (cases \<phi>)
          case TT
          then show ?thesis by auto
        next
          case (Internal _)
          then show ?thesis
            using silent_reachable_trans by auto
        next
          case (ImmConj _ _)
          then show ?thesis using no_imm_conj by auto
        qed
        from case_assms have conj_price: \<open>\<forall>i\<in>I. \<Psi> i \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          unfolding \<O>_conjunct_def \<O>_inner_def
          by (simp, metis SUP_bot_conv(1) le_zero_eq sup_bot_left sup_ge1)
        from case_assms have \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<Psi> i)\<close>
              \<open>hml_srbb_inner_models p (Obs \<alpha> \<phi>)\<close>
          using branching_conj_parts branching_conj_obs by blast+
        then obtain p' where \<open>p \<mapsto>a \<alpha> p'\<close> \<open>p' \<Turnstile>SRBB \<phi>\<close> by auto
        then obtain q' q'' q''' where q'_q''_spec:
          \<open>q \<Zsurj> q'\<close> \<open>q' \<mapsto>a \<alpha> q''\<close> \<open>q'' \<Zsurj> q'''\<close>
          \<open>p ~\<eta> q'\<close> \<open>p' ~\<eta> q'''\<close>
          using eta_bisim_sim \<open>p ~\<eta> q\<close> silent_reachable.refl
          unfolding eta_simulation_def by blast
        hence \<open>q''' \<Turnstile>SRBB \<phi>\<close>
          using BranchConj.hyps \<open>p' \<Turnstile>SRBB \<phi>\<close> \<open>\<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close> by auto
        hence \<open>q'' \<Turnstile>SRBB \<phi>\<close> using back_step q'_q''_spec by blast
        hence \<open>hml_srbb_inner_models q' (Obs \<alpha> \<phi>)\<close> using q'_q''_spec by auto
        moreover have \<open>\<forall>i\<in>I. hml_srbb_conjunct_models q' (\<Psi> i)\<close>
          using BranchConj.hyps \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<Psi> i)\<close> q'_q''_spec conj_price
          by blast
        ultimately show \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' (BranchConj \<alpha> \<phi> I \<Psi>)\<close>
          using \<open>q \<Zsurj> q'\<close> by auto
      qed
    next
      case (Pos \<chi>)
      show ?case
      proof safe
        fix p q
        assume case_assms:
          \<open>p ~\<eta> q\<close>
          \<open>Pos \<chi> \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          \<open>hml_srbb_conjunct_models p (Pos \<chi>)\<close>
        hence \<open>\<chi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          unfolding \<O>_inner_def \<O>_conjunct_def by simp
        from case_assms obtain p' where \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' \<chi>\<close> by auto
        then obtain q' where \<open>q \<Zsurj> q'\<close> \<open>hml_srbb_inner_models q' \<chi>\<close>
          using Pos \<open>p ~\<eta> q\<close> \<open>\<chi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          by (meson eta_bisimulated_silently_retained silent_reachable_trans)
        thus \<open>hml_srbb_conjunct_models q (Pos \<chi>)\<close> by auto
      qed
    next
      case (Neg \<chi>)
      show ?case
      proof safe
        fix p q
        assume case_assms:
          \<open>p ~\<eta> q\<close>
          \<open>Neg \<chi> \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          \<open>hml_srbb_conjunct_models p (Neg \<chi>)\<close>
        hence \<open>\<chi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          unfolding \<O>_inner_def \<O>_conjunct_def by simp
        from case_assms have \<open>\<forall>p'. p \<Zsurj> p' \<longrightarrow> \<not>hml_srbb_inner_models p' \<chi>\<close> by simp
        moreover have
          \<open>(\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>)
            \<longrightarrow> (\<exists>p'. p \<Zsurj> p' \<and> hml_srbb_inner_models p' \<chi>)\<close>
          using Neg eta_bisim_sym[OF \<open>p ~\<eta> q\<close>] eta_bisimulated_silently_retained
            silent_reachable_trans \<open>\<chi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close> by blast
        ultimately have \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow> \<not>hml_srbb_inner_models q' \<chi>\<close> by blast
        thus \<open>hml_srbb_conjunct_models q (Neg \<chi>)\<close> by simp
      qed
    qed
  qed
  thus ?thesis using assms by blast
qed

lemma modal_eta_sim_eq: \<open>eta_simulation (equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)))\<close>
proof -
  have \<open>\<nexists>p \<alpha> p' q. (equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>))) p q \<and> p \<mapsto> \<alpha> p' \<and>
      (\<alpha> \<noteq> \<tau> \<or> \<not>(equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>))) p' q) \<and>
      (\<forall>q' q'' q'''. q \<Zsurj> q' \<longrightarrow> q' \<mapsto> \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q'''
    \<longrightarrow> \<not> equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p q'
      \<or> \<not> equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p' q''')\<close>
  proof clarify
    fix p \<alpha> p' q
    define Q\<alpha> where
      \<open>Q\<alpha> \<equiv> {q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. \<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)
        \<and> (distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p))}\<close>
    assume contradiction:
      \<open>equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p q\<close> \<open>p \<mapsto> \<alpha> p'\<close>
      \<open>\<forall>q' q'' q'''. q \<Zsurj> q' \<longrightarrow> q' \<mapsto> \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q'''
      \<longrightarrow> \<not> equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p q'
        \<or> \<not> equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p' q'''\<close>
      \<open>\<alpha> \<noteq> \<tau> \<or> \<not> equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p' q\<close>
    hence distinctions: \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow>
      (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p) \<or>
      (\<forall>q'' q'''. q' \<mapsto>a \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q'''
      \<longrightarrow> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>).
            distinguishes \<phi> p' q''' \<or> distinguishes \<phi> q''' p'))\<close>
      unfolding equivalent_no_distinction
      by (metis silent_reachable.cases silent_reachable.refl)
    hence \<open>\<forall>q'' q''' . \<forall>q'\<in>Q\<alpha>. q' \<mapsto>a \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q'''
      \<longrightarrow> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>).
             distinguishes \<phi> p' q''' \<or> distinguishes \<phi> q''' p')\<close>
      unfolding Q\<alpha>_def using silent_reachable.refl by fastforce
    hence \<open>\<forall>q'' q'''. q'' \<Zsurj> q''' \<longrightarrow> (\<exists>q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. \<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)
              \<and> (distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)) \<and> q' \<mapsto>a \<alpha> q'')
        \<longrightarrow> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>).
              distinguishes \<phi> p' q''' \<or> distinguishes \<phi> q''' p')\<close>
      unfolding Q\<alpha>_def by blast
    hence \<open>\<forall>q'''. (\<exists>q' q''. q \<Zsurj> q' \<and> (\<nexists>\<phi>. \<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)
              \<and> (distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)) \<and> q' \<mapsto>a \<alpha> q'' \<and>  q'' \<Zsurj> q''')
        \<longrightarrow> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>).
              distinguishes \<phi> p' q''' \<or> distinguishes \<phi> q''' p')\<close>
      by blast
    then obtain \<Phi>\<alpha> where \<Phi>\<alpha>_def:
      \<open>\<forall>q'''. (\<exists>q' q''. q \<Zsurj> q' \<and> (\<nexists>\<phi>. \<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)
              \<and> (distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)) \<and> q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q''')
        \<longrightarrow> (\<Phi>\<alpha> q''') \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)
          \<and> (distinguishes (\<Phi>\<alpha> q''') p' q''' \<or> distinguishes (\<Phi>\<alpha> q''') q''' p')\<close> by metis
    hence distinctions_\<alpha>: \<open>\<forall>q'\<in>Q\<alpha>. \<forall>q'' q'''.
        q' \<mapsto>a \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q'''
        \<longrightarrow> distinguishes (\<Phi>\<alpha> q''') p' q''' \<or> distinguishes (\<Phi>\<alpha> q''') q''' p'\<close>
      unfolding Q\<alpha>_def by blast
    from distinctions obtain \<Phi>\<eta> where
      \<open>\<forall>q'. q'\<in>{q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>).
        distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)}
        \<longrightarrow> (distinguishes (\<Phi>\<eta> q') p q' \<or> distinguishes (\<Phi>\<eta> q') q' p)
          \<and> (\<Phi>\<eta> q') \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
      unfolding mem_Collect_eq by moura
    hence
      \<open>\<forall>q'\<in>{q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>).
          distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)}.
        (distinguishes (\<Phi>\<eta> q') p q' \<or> distinguishes (\<Phi>\<eta> q') q' p)\<close>
      \<open>\<forall>q'\<in>{q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>).
          distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)}.
        (\<Phi>\<eta> q') \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
      by blast+
    from distinction_conjunctification_two_way[OF this(1)]
      distinction_conjunctification_two_way_price[OF this]
    have \<open>\<forall>q'\<in>{q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>).
            distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)}.
        hml_srbb_conj.distinguishes (
         (if distinguishes (\<Phi>\<eta> q') p q'
          then conjunctify_distinctions
          else conjunctify_distinctions_dual) \<Phi>\<eta> p q') p q'
        \<and> (if distinguishes (\<Phi>\<eta> q') p q'
          then conjunctify_distinctions
          else conjunctify_distinctions_dual) \<Phi>\<eta> p q' \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
        by fastforce
    then obtain \<Psi>\<eta> where distinctions_\<eta>:
      \<open>\<forall>q'\<in>{q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>).
            distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)}.
        hml_srbb_conj.distinguishes (\<Psi>\<eta> q') p q'
        \<and> \<Psi>\<eta> q' \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
      by auto
    have \<open>p \<mapsto>a \<alpha> p'\<close> using \<open>p \<mapsto> \<alpha> p'\<close> by simp
    from distinction_combination_eta_two_way[OF this, of q \<Phi>\<alpha>] distinctions_\<alpha> have obs_dist:
      \<open>\<forall>q'\<in>Q\<alpha>.
        hml_srbb_inner.distinguishes (
          Obs \<alpha> (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
            (\<lambda>q'''. (if distinguishes (\<Phi>\<alpha> q''') p' q'''
                     then conjunctify_distinctions else conjunctify_distinctions_dual) \<Phi>\<alpha> p'
                   q''')))
          ) p q'\<close>
      unfolding Q\<alpha>_def by fastforce
    have \<open>Q\<alpha> \<noteq> {}\<close>
      using Q\<alpha>_def contradiction(1) silent_reachable.refl by fastforce
    hence conjunct_prices: \<open>\<forall>q'''\<in>{q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}.
       ((if distinguishes (\<Phi>\<alpha> q''') p' q'''
        then conjunctify_distinctions
        else conjunctify_distinctions_dual) \<Phi>\<alpha> p' q'''
        ) \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
      using distinction_conjunctification_two_way_price[of
         \<open>{q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}\<close>]
      using Q\<alpha>_def \<Phi>\<alpha>_def by auto
    have \<open>(Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
      (\<lambda>q'''. (if distinguishes (\<Phi>\<alpha> q''') p' q'''
               then conjunctify_distinctions else conjunctify_distinctions_dual)
             \<Phi>\<alpha> p' q''')) \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
    proof (cases \<open>{q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} = {}\<close>)
      case True
      then show ?thesis
        unfolding \<O>_inner_def \<O>_conjunct_def
        by (auto simp add: True bot_enat_def)
    next
      case False
      then show ?thesis
        using conjunct_prices
        unfolding \<O>_inner_def \<O>_conjunct_def by force
    qed
    hence obs_price: \<open>(Obs \<alpha> (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
         (\<lambda>q'''. (if distinguishes (\<Phi>\<alpha> q''') p' q'''
                  then conjunctify_distinctions else conjunctify_distinctions_dual
                  ) \<Phi>\<alpha> p'  q''')))) \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
      using distinction_conjunctification_price distinctions_\<alpha>
      unfolding \<O>_inner_def \<O>_def by simp
    from obs_dist distinctions_\<eta> have
      \<open>hml_srbb_inner_models p (BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
               (\<lambda>q'''. (if distinguishes (\<Phi>\<alpha> q''') p' q'''
                        then conjunctify_distinctions else conjunctify_distinctions_dual
                        ) \<Phi>\<alpha> p' q''')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>).
            distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)} \<Psi>\<eta>)\<close>
      using \<open>Q\<alpha> \<noteq> {}\<close> silent_reachable.refl
      unfolding hml_srbb_conj.distinguishes_def hml_srbb_inner.distinguishes_def
      by (smt (verit) Q\<alpha>_def empty_Collect_eq hml_srbb_inner_models.simps(1,4) mem_Collect_eq)
    moreover have \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow> \<not> hml_srbb_inner_models q'
        (BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
             (\<lambda>q'''. (if distinguishes (\<Phi>\<alpha> q''') p' q'''
                      then conjunctify_distinctions
                      else conjunctify_distinctions_dual) \<Phi>\<alpha> p'
             q''')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>).
            distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)} \<Psi>\<eta>)\<close>
    proof safe
      fix q'
      assume contradiction: \<open>q \<Zsurj> q'\<close>
        \<open>hml_srbb_inner_models q' (BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
             (\<lambda>q'''. (if distinguishes (\<Phi>\<alpha> q''') p' q'''
                      then conjunctify_distinctions
                      else conjunctify_distinctions_dual) \<Phi>\<alpha> p'
             q''')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>).
            distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)} \<Psi>\<eta>)\<close>
      thus \<open>False\<close>
        using obs_dist distinctions_\<eta>  branching_conj_obs branching_conj_parts
        unfolding distinguishes_def hml_srbb_conj.distinguishes_def
          hml_srbb_inner.distinguishes_def Q\<alpha>_def
        by blast
    qed
    moreover have branch_price:
      \<open>(BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
             (\<lambda>q'''. (if distinguishes (\<Phi>\<alpha> q''') p' q'''
                      then conjunctify_distinctions
                      else conjunctify_distinctions_dual) \<Phi>\<alpha> p'
             q''')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>).
          distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)} \<Psi>\<eta>)
        \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
      using distinctions_\<eta> obs_price
      unfolding Q\<alpha>_def \<O>_inner_def \<O>_def \<O>_conjunct_def \<Phi>\<alpha>_def
      by (simp, metis (mono_tags, lifting) SUP_bot_conv(2) bot_enat_def sup_bot_left)
    ultimately have \<open>distinguishes (Internal (BranchConj \<alpha>
        (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
          (\<lambda>q'''. (if distinguishes (\<Phi>\<alpha> q''') p' q'''
                   then conjunctify_distinctions else conjunctify_distinctions_dual) \<Phi>\<alpha> p'
          q''')))
        {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>).
          distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)} \<Psi>\<eta>)) p q\<close>
      unfolding distinguishes_def Q\<alpha>_def
      using silent_reachable.refl hml_srbb_models.simps(2) by blast
    moreover have \<open>(Internal (BranchConj \<alpha>
        (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
           (\<lambda>q'''. (if distinguishes (\<Phi>\<alpha> q''') p' q'''
                    then conjunctify_distinctions else conjunctify_distinctions_dual) \<Phi>\<alpha> p'
            q''')))
        {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>).
          distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)} \<Psi>\<eta>))
      \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
      using branch_price
      unfolding Q\<alpha>_def \<O>_def \<O>_conjunct_def
      by (metis (no_types, lifting) \<O>_inner_def expr_internal_eq mem_Collect_eq)
    ultimately show False using contradiction(1) equivalent_no_distinction by blast
  qed
  thus ?thesis
    unfolding eta_simulation_def by blast
qed

theorem eta_bisim_coordinate: \<open>(p ~\<eta> q) = (p \<sim> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) q)\<close>
  using modal_eta_sim_eq logic_eta_bisim_invariant sympD equivalent_no_distinction
  unfolding eta_bisimulated_def expr_equiv_def distinguishes_def
  by (smt (verit, best) equivalent_equiv equivpE)

subsection \<open>\<open>\<eta>\<close>-Similarity\<close>

\<comment>\<open>The following two proofs essentially are a simpler version of the proof for \<open>\<eta>\<close>-bisimilarity. In a paper, one would just say “analogously”.\<close>

lemma logic_eta_sim_invariant:
  assumes
    \<open>\<exists>R. eta_simulation R \<and>  R p0 q0\<close>
    \<open>\<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close>
    \<open>p0 \<Turnstile>SRBB \<phi>\<close>
  shows \<open>q0 \<Turnstile>SRBB \<phi>\<close>
proof -
  have \<open>\<And>\<phi> \<chi> \<psi>.
    (\<forall>p q. (\<exists>R. eta_simulation R \<and>  R p q) \<longrightarrow> \<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)
      \<longrightarrow> p \<Turnstile>SRBB \<phi> \<longrightarrow> q \<Turnstile>SRBB \<phi>) \<and>
    (\<forall>p q. (\<exists>R. eta_simulation R \<and>  R p q) \<longrightarrow> \<chi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)
      \<longrightarrow> hml_srbb_inner_models p \<chi> \<longrightarrow> (\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>)) \<and>
    (\<forall>p q. (\<exists>R. eta_simulation R \<and>  R p q) \<longrightarrow> \<psi> \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)
      \<longrightarrow> hml_srbb_conjunct_models p \<psi> \<longrightarrow> hml_srbb_conjunct_models q \<psi>)\<close>
  proof -
    fix \<phi> \<chi> \<psi>
    show
      \<open>(\<forall>p q. (\<exists>R. eta_simulation R \<and> R p q) \<longrightarrow> \<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)
        \<longrightarrow> p \<Turnstile>SRBB \<phi> \<longrightarrow> q \<Turnstile>SRBB \<phi>) \<and>
       (\<forall>p q. (\<exists>R. eta_simulation R \<and> R p q) \<longrightarrow> \<chi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)
        \<longrightarrow> hml_srbb_inner_models p \<chi> \<longrightarrow> (\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>)) \<and>
       (\<forall>p q. (\<exists>R. eta_simulation R \<and> R p q) \<longrightarrow> \<psi> \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)
        \<longrightarrow> hml_srbb_conjunct_models p \<psi> \<longrightarrow> hml_srbb_conjunct_models q \<psi>)\<close>
    proof (induct rule: hml_srbb_hml_srbb_inner_hml_srbb_conjunct.induct)
      case TT
      then show ?case by simp
    next
      case (Internal \<chi>)
      show ?case
      proof safe
        fix p q R
        assume case_assms:
          \<open>eta_simulation R\<close> \<open>R p q\<close>  \<open>p \<Turnstile>SRBB hml_srbb.Internal \<chi>\<close>
          \<open>Internal \<chi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close>
        then obtain p' where p'_spec: \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' \<chi>\<close> by auto
        have \<open>\<chi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close>
          using case_assms(4) unfolding \<O>_inner_def \<O>_def by auto
        hence \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>\<close>
          using Internal case_assms(1,2) p'_spec silence_retains_eta_sim
          by (metis silent_reachable_trans)
        thus \<open>q \<Turnstile>SRBB hml_srbb.Internal \<chi>\<close> by auto
      qed
    next
      case (ImmConj I \<Psi>)
      then show ?case unfolding \<O>_inner_def \<O>_def by auto
    next
      case (Obs \<alpha> \<phi>)
      then show ?case
      proof (safe)
        fix p q R
        assume case_assms:
          \<open>eta_simulation R\<close> \<open>R p q\<close>
          \<open>Obs \<alpha> \<phi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close>
          \<open>hml_srbb_inner_models p (hml_srbb_inner.Obs \<alpha> \<phi>)\<close>
        hence \<open>\<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close> unfolding \<O>_inner_def \<O>_def by auto
        hence no_imm_conj: \<open>\<nexists>I \<Psi>. \<phi> = ImmConj I \<Psi> \<and> I \<noteq> {}\<close> unfolding \<O>_def by force
        have back_step: \<open>\<forall>p0 p1. p1 \<Turnstile>SRBB \<phi> \<longrightarrow> p0 \<Zsurj> p1 \<longrightarrow> p0 \<Turnstile>SRBB \<phi>\<close>
        proof (cases \<phi>)
          case TT
          then show ?thesis by auto
        next
          case (Internal _)
          then show ?thesis
            using silent_reachable_trans by auto
        next
          case (ImmConj _ _)
          then show ?thesis using no_imm_conj by auto
        qed
        from case_assms obtain p' where \<open>p \<mapsto>a \<alpha> p'\<close> \<open>p' \<Turnstile>SRBB \<phi>\<close> by auto
        then obtain q' q'' q''' where \<open>q \<Zsurj> q'\<close> \<open>q' \<mapsto>a \<alpha> q''\<close> \<open>q'' \<Zsurj> q'''\<close>  \<open>R p' q'''\<close>
          using \<open>eta_simulation R\<close> \<open>R p q\<close> unfolding eta_simulation_def
          using silent_reachable.refl by blast
        hence \<open>q''' \<Turnstile>SRBB \<phi>\<close> using \<open>p' \<Turnstile>SRBB \<phi>\<close> Obs \<open>\<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close>
          using case_assms(1) by blast
        hence \<open>hml_srbb_inner_models q' (hml_srbb_inner.Obs \<alpha> \<phi>)\<close>
          using \<open>q' \<mapsto>a \<alpha> q''\<close> \<open>q'' \<Zsurj> q'''\<close> back_step by auto
        thus \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' (hml_srbb_inner.Obs \<alpha> \<phi>)\<close>
          using \<open>q \<Zsurj> q'\<close> by blast
      qed
    next
      case (Conj I \<Psi>)
      show ?case
      proof safe
        fix p q R
        assume case_assms:
          \<open>eta_simulation R\<close> \<open>R p q\<close>
          \<open>Conj I \<Psi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close>
          \<open>hml_srbb_inner_models p (Conj I \<Psi>)\<close>
        hence conj_price: \<open>\<forall>i\<in>I. \<Psi> i \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close>
          unfolding \<O>_conjunct_def \<O>_inner_def
          by (simp, metis SUP_bot_conv(1) le_zero_eq sup_bot_left sup_ge1)
        from case_assms have \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<Psi> i)\<close> by auto
        hence \<open>\<forall>i\<in>I. hml_srbb_conjunct_models q (\<Psi> i)\<close>
          using Conj \<open>eta_simulation R\<close> \<open>R p q\<close> conj_price by blast
        hence \<open>hml_srbb_inner_models q (hml_srbb_inner.Conj I \<Psi>)\<close> by simp
        thus \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' (hml_srbb_inner.Conj I \<Psi>)\<close>
          using silent_reachable.refl by blast
      qed
    next
      case (StableConj I \<Psi>)
      thus ?case unfolding \<O>_inner_def \<O>_def by auto
    next
      case (BranchConj \<alpha> \<phi> I \<Psi>)
      show ?case
      proof safe
        fix p q R
        assume case_assms:
          \<open>eta_simulation R\<close> \<open>R p q\<close>
          \<open>BranchConj \<alpha> \<phi> I \<Psi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close>
          \<open>hml_srbb_inner_models p (BranchConj \<alpha> \<phi> I \<Psi>)\<close>
        hence \<open>\<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close> unfolding \<O>_inner_def \<O>_def
          by (simp, metis le_zero_eq sup_ge1)
        hence no_imm_conj: \<open>\<nexists>I \<Psi>. \<phi> = ImmConj I \<Psi> \<and> I \<noteq> {}\<close> unfolding \<O>_def by force
        have back_step: \<open>\<forall>p0 p1. p1 \<Turnstile>SRBB \<phi> \<longrightarrow> p0 \<Zsurj> p1 \<longrightarrow> p0 \<Turnstile>SRBB \<phi>\<close>
        proof (cases \<phi>)
          case TT
          then show ?thesis by auto
        next
          case (Internal _)
          then show ?thesis
            using silent_reachable_trans by auto
        next
          case (ImmConj _ _)
          then show ?thesis using no_imm_conj by auto
        qed
        from case_assms have conj_price: \<open>\<forall>i\<in>I. \<Psi> i \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close>
          unfolding \<O>_conjunct_def \<O>_inner_def
          by (simp, metis SUP_bot_conv(1) bot_enat_def bot_eq_sup_iff)
        from case_assms have \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<Psi> i)\<close>
              \<open>hml_srbb_inner_models p (Obs \<alpha> \<phi>)\<close>
          using branching_conj_parts branching_conj_obs by blast+
        then obtain p' where \<open>p \<mapsto>a \<alpha> p'\<close> \<open>p' \<Turnstile>SRBB \<phi>\<close> by auto
        then obtain q' q'' q''' where q'_q''_spec:
          \<open>q \<Zsurj> q'\<close> \<open>q' \<mapsto>a \<alpha> q''\<close> \<open>q'' \<Zsurj> q'''\<close>
          \<open>R p q'\<close> \<open>R p' q'''\<close>
          using \<open>eta_simulation R\<close> \<open>R p q\<close> silent_reachable.refl
          unfolding eta_simulation_def by blast
        hence \<open>q''' \<Turnstile>SRBB \<phi>\<close>
          using BranchConj \<open>p' \<Turnstile>SRBB \<phi>\<close> \<open>\<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close> case_assms by auto
        hence \<open>q'' \<Turnstile>SRBB \<phi>\<close> using back_step q'_q''_spec by blast
        hence \<open>hml_srbb_inner_models q' (Obs \<alpha> \<phi>)\<close> using q'_q''_spec by auto
        moreover have \<open>\<forall>i\<in>I. hml_srbb_conjunct_models q' (\<Psi> i)\<close>
          using BranchConj q'_q''_spec conj_price case_assms
            \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<Psi> i)\<close>
          by blast
        ultimately show \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' (BranchConj \<alpha> \<phi> I \<Psi>)\<close>
          using \<open>q \<Zsurj> q'\<close> by auto
      qed
    next
      case (Pos \<chi>)
      show ?case
      proof safe
        fix p q R
        assume case_assms:
          \<open>eta_simulation R\<close> \<open>R p q\<close>
          \<open>Pos \<chi> \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close>
          \<open>hml_srbb_conjunct_models p (Pos \<chi>)\<close>
        hence \<open>\<chi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close>
          unfolding \<O>_inner_def \<O>_conjunct_def by simp
        from case_assms obtain p' where \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' \<chi>\<close> by auto
        then obtain q' where \<open>q \<Zsurj> q'\<close> \<open>hml_srbb_inner_models q' \<chi>\<close>
          using Pos case_assms \<open>\<chi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close> silence_retains_eta_sim
          by (smt (verit, ccfv_threshold) silent_reachable_trans)
        thus \<open>hml_srbb_conjunct_models q (Pos \<chi>)\<close> by auto
      qed
    next
      case (Neg \<chi>)
      show ?case
      proof safe
        fix p q R
        assume case_assms:
          \<open>eta_simulation R\<close> \<open>R p q\<close>
          \<open>Neg \<chi> \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close>
          \<open>hml_srbb_conjunct_models p (Neg \<chi>)\<close>
        hence False unfolding \<O>_conjunct_def by auto
        thus \<open>hml_srbb_conjunct_models q (Neg \<chi>)\<close> by simp
      qed
    qed
  qed
  thus ?thesis using assms by blast
qed

lemma modal_eta_sim: \<open>eta_simulation (preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)))\<close>
proof -
  have \<open>\<nexists>p \<alpha> p' q. (preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0))) p q \<and> p \<mapsto> \<alpha> p' \<and>
      (\<alpha> \<noteq> \<tau> \<or> \<not>(preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0))) p' q) \<and>
      (\<forall>q' q'' q'''. q \<Zsurj> q' \<longrightarrow> q' \<mapsto> \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q'''
    \<longrightarrow> \<not> preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)) p q'
      \<or> \<not> preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)) p' q''')\<close>
  proof clarify
    have less_obs:
      \<open>modal_depth (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0) \<le> pos_conjuncts (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close>
      by simp
    fix p \<alpha> p' q
    define Q\<alpha> where
      \<open>Q\<alpha> \<equiv> {q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. \<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0) \<and> distinguishes \<phi> p q')}\<close>
    assume contradiction:
      \<open>preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)) p q\<close> \<open>p \<mapsto> \<alpha> p'\<close>
      \<open>\<forall>q' q'' q'''. q \<Zsurj> q' \<longrightarrow> q' \<mapsto> \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q'''
      \<longrightarrow> \<not> preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)) p q'
        \<or> \<not> preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)) p' q'''\<close>
      \<open>\<alpha> \<noteq> \<tau> \<or> \<not> preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)) p' q\<close>
    hence distinctions: \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow>
      (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0). distinguishes \<phi> p q') \<or>
      (\<forall>q'' q'''. q' \<mapsto>a \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q'''
        \<longrightarrow> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0). distinguishes \<phi> p' q'''))\<close>
      unfolding preordered_no_distinction
      by (metis silent_reachable.cases silent_reachable.refl)
    hence \<open>\<forall>q'' q''' . \<forall>q'\<in>Q\<alpha>.
        q' \<mapsto>a \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q'''
        \<longrightarrow> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0). distinguishes \<phi> p' q''')\<close>
      unfolding Q\<alpha>_def using silent_reachable.refl by fastforce
    hence \<open>\<forall>q'' q'''. q'' \<Zsurj> q''' \<longrightarrow>
      (\<exists>q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. \<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0) \<and> distinguishes \<phi> p q')
        \<and> q' \<mapsto>a \<alpha> q'')
        \<longrightarrow> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0). distinguishes \<phi> p' q''')\<close>
      unfolding Q\<alpha>_def by blast
    hence \<open>\<forall>q'''. (\<exists>q' q''. q \<Zsurj> q' \<and>
      (\<nexists>\<phi>. \<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0) \<and> distinguishes \<phi> p q') \<and> q' \<mapsto>a \<alpha> q''
        \<and>  q'' \<Zsurj> q''')
      \<longrightarrow> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0). distinguishes \<phi> p' q''')\<close>
      by blast
    then obtain \<Phi>\<alpha> where \<Phi>\<alpha>_def:
      \<open>\<forall>q'''. (\<exists>q' q''. q \<Zsurj> q' \<and>
        (\<nexists>\<phi>. \<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0) \<and> distinguishes \<phi> p q')
          \<and> q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q''')
        \<longrightarrow> (\<Phi>\<alpha> q''') \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0) \<and> distinguishes (\<Phi>\<alpha> q''') p' q'''\<close>
      by metis
    hence distinctions_\<alpha>: \<open>\<forall>q'\<in>Q\<alpha>. \<forall>q'' q'''.
        q' \<mapsto>a \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q''' \<longrightarrow> distinguishes (\<Phi>\<alpha> q''') p' q'''\<close>
      unfolding Q\<alpha>_def by blast
    from distinctions obtain \<Phi>\<eta> where
      \<open>\<forall>q'. q'\<in>{q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0). distinguishes \<phi> p q')}
        \<longrightarrow> distinguishes (\<Phi>\<eta> q') p q' \<and> (\<Phi>\<eta> q') \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close>
      unfolding mem_Collect_eq by moura
    then obtain \<Psi>\<eta> where distinctions_\<eta>:
      \<open>\<forall>q'\<in>{q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0). distinguishes \<phi> p q')}.
        hml_srbb_conj.distinguishes (\<Psi>\<eta> q') p q' \<and> (\<Psi>\<eta> q')
          \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close>
      using less_obs  distinction_conjunctification distinction_conjunctification_price
      by (smt (verit, del_insts))
    have \<open>p \<mapsto>a \<alpha> p'\<close> using \<open>p \<mapsto> \<alpha> p'\<close> by auto
    from distinction_combination_eta[OF this] distinctions_\<alpha> have obs_dist:
      \<open>\<forall>q'\<in>Q\<alpha>. hml_srbb_inner.distinguishes
          (Obs \<alpha> (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
                                 (conjunctify_distinctions \<Phi>\<alpha> p')))) p q'\<close>
      unfolding Q\<alpha>_def by blast
    have \<open>Q\<alpha> \<noteq> {}\<close>
      using Q\<alpha>_def contradiction(1) silent_reachable.refl by fastforce
    hence conjunct_prices: \<open>\<forall>q'''\<in>{q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}.
        (conjunctify_distinctions \<Phi>\<alpha> p' q''') \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close>
      using distinction_conjunctification_price[of
              \<open>{q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}\<close>]
      using Q\<alpha>_def \<Phi>\<alpha>_def by auto
    have \<open>(Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
          (conjunctify_distinctions \<Phi>\<alpha> p')) \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close>
    proof (cases \<open>{q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} = {}\<close>)
      case True
      then show ?thesis
        unfolding \<O>_inner_def \<O>_conjunct_def
        by (auto simp add: True bot_enat_def)
    next
      case False
      then show ?thesis
        using conjunct_prices
        unfolding \<O>_inner_def \<O>_conjunct_def by force
    qed
    hence obs_price: \<open>(Obs \<alpha> (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
         (conjunctify_distinctions \<Phi>\<alpha> p')))) \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close>
      using distinction_conjunctification_price distinctions_\<alpha>
      unfolding \<O>_inner_def \<O>_def by simp
    from obs_dist distinctions_\<eta> have
      \<open>hml_srbb_inner_models p (BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
                   (conjunctify_distinctions \<Phi>\<alpha> p')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0). distinguishes \<phi> p q')} \<Psi>\<eta>)\<close>
      using contradiction(1) silent_reachable.refl
      unfolding Q\<alpha>_def by force
    moreover have \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow> \<not> hml_srbb_inner_models q'
        (BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
                   (conjunctify_distinctions \<Phi>\<alpha> p')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0). distinguishes \<phi> p q')} \<Psi>\<eta>)\<close>
    proof safe
      fix q'
      assume contradiction: \<open>q \<Zsurj> q'\<close>
        \<open>hml_srbb_inner_models q' (BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
                   (conjunctify_distinctions \<Phi>\<alpha> p')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0). distinguishes \<phi> p q')} \<Psi>\<eta>)\<close>
      thus \<open>False\<close>
        using obs_dist distinctions_\<eta>
        unfolding distinguishes_def hml_srbb_conj.distinguishes_def
          hml_srbb_inner.distinguishes_def Q\<alpha>_def
        by (auto) blast+
    qed
    moreover have branch_price: \<open>(BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
                   (conjunctify_distinctions \<Phi>\<alpha> p')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0). distinguishes \<phi> p q')} \<Psi>\<eta>)
      \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close>
      using distinctions_\<eta> obs_price
      unfolding Q\<alpha>_def \<O>_inner_def \<O>_def \<O>_conjunct_def \<Phi>\<alpha>_def
      by (simp, metis (mono_tags, lifting) SUP_bot_conv(2) bot_enat_def sup_bot_left)
    ultimately have \<open>distinguishes (Internal (BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
                   (conjunctify_distinctions \<Phi>\<alpha> p')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0). distinguishes \<phi> p q')} \<Psi>\<eta>)) p q\<close>
      unfolding distinguishes_def Q\<alpha>_def
      using silent_reachable.refl hml_srbb_models.simps(2) by blast
    moreover have \<open>(Internal (BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
                   (conjunctify_distinctions \<Phi>\<alpha> p')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0). distinguishes \<phi> p q')} \<Psi>\<eta>))
      \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0)\<close>
      using branch_price
      unfolding Q\<alpha>_def \<O>_def \<O>_conjunct_def
      by (metis (no_types, lifting) \<O>_inner_def expr_internal_eq mem_Collect_eq)
    ultimately show False using contradiction(1) preordered_no_distinction by blast
  qed
  thus ?thesis
    unfolding eta_simulation_def by blast
qed

theorem eta_sim_coordinate:
    \<open>(p \<preceq> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0) q) = (\<exists>R. eta_simulation R \<and> R p q)\<close>
  using modal_eta_sim logic_eta_sim_invariant unfolding expr_preord_def
  by auto

end

end
