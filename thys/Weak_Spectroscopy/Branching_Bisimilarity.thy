(* License: LGPL *)

section \<open>Branching Bisimilarity\<close>

theory Branching_Bisimilarity
  imports Eta_Bisimilarity
begin

text \<open>
  The whole of the modal logic of \<^type>\<open>hml_srbb\<close> precisely characterizes stability-respecting branching bisimilarity.
\<close>

subsection \<open>Definitions of (Stability-Respecting) Branching Bisimilarity\<close>

context lts_tau
begin

definition branching_simulation :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>branching_simulation R \<equiv> \<forall>p \<alpha> p' q. R p q \<longrightarrow> p \<mapsto> \<alpha> p' \<longrightarrow>
    ((\<alpha> = \<tau> \<and> R p' q) \<or> (\<exists>q' q''. q \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> R p q' \<and> R p' q''))\<close>

lemma branching_simulation_intro:
  assumes
    \<open>\<And>p \<alpha> p' q. R p q \<Longrightarrow> p \<mapsto> \<alpha> p' \<Longrightarrow>
      ((\<alpha> = \<tau> \<and> R p' q) \<or> (\<exists>q' q''. q \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> R p q' \<and> R p' q''))\<close>
  shows
    \<open>branching_simulation R\<close>
  using assms unfolding branching_simulation_def by simp

definition branching_simulated :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>branching_simulated p q \<equiv> \<exists>R. branching_simulation R \<and> R p q\<close>

definition branching_bisimulated :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>branching_bisimulated p q \<equiv> \<exists>R. branching_simulation R \<and> symp R \<and> R p q\<close>

definition sr_branching_bisimulated :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> (infix \<open>~SRBB\<close> 40) where
  \<open>p ~SRBB q \<equiv> \<exists>R. branching_simulation R \<and> symp R \<and> stability_respecting R \<and> R p q\<close>

subsection \<open>Properties of Branching Bisimulation Equivalences\<close>

lemma branching_bisimilarity_branching_sim: \<open>branching_simulation (~SRBB)\<close>
  unfolding sr_branching_bisimulated_def branching_simulation_def by blast

lemma branching_sim_eta_sim:
  assumes \<open>branching_simulation R\<close>
  shows \<open>eta_simulation R\<close>
  using assms silent_reachable.refl
  unfolding branching_simulation_def eta_simulation_def by blast

lemma silence_retains_branching_sim:
assumes
  \<open>branching_simulation R\<close>
  \<open>R p q\<close>
  \<open>p \<Zsurj> p'\<close>
shows \<open>\<exists>q'. R p' q' \<and> q \<Zsurj> q'\<close>
  using assms silence_retains_eta_sim branching_sim_eta_sim by blast

lemma branching_bisimilarity_stability: \<open>stability_respecting (~SRBB)\<close>
  unfolding sr_branching_bisimulated_def stability_respecting_def by blast

lemma sr_branching_bisimulation_silently_retained:
  assumes
    \<open>p ~SRBB q\<close>
    \<open>p \<Zsurj> p'\<close>
  shows
    \<open>\<exists>q'. q \<Zsurj> q' \<and> p' ~SRBB q'\<close> using assms(2,1)
  using branching_bisimilarity_branching_sim silence_retains_branching_sim by blast

lemma sr_branching_bisimulation_sim:
  assumes
    \<open>p ~SRBB q\<close>
    \<open>p \<Zsurj> p'\<close> \<open>p' \<mapsto>a \<alpha> p''\<close>
  shows
    \<open>\<exists>q' q''. q \<Zsurj> q' \<and> q' \<mapsto>a \<alpha> q'' \<and> p' ~SRBB q' \<and> p'' ~SRBB q''\<close>
proof -
  obtain q' where \<open>q \<Zsurj> q'\<close> \<open>sr_branching_bisimulated p' q'\<close>
    using assms sr_branching_bisimulation_silently_retained by blast
  thus ?thesis
    using assms(3) branching_bisimilarity_branching_sim silent_reachable_trans
    unfolding branching_simulation_def
    by blast
qed

lemma sr_branching_bisimulated_sym:
  assumes
    \<open>p ~SRBB q\<close>
  shows
    \<open>q ~SRBB p\<close>
  using assms unfolding sr_branching_bisimulated_def by (meson sympD)

lemma sr_branching_bisimulated_symp:
  shows \<open>symp (~SRBB)\<close>
  using sr_branching_bisimulated_sym
  using sympI by blast

lemma sr_branching_bisimulated_reflp:
  shows \<open>reflp (~SRBB)\<close>
    unfolding sr_branching_bisimulated_def stability_respecting_def reflp_def
    using silence_retains_branching_sim silent_reachable.refl
    by (smt (verit) DEADID.rel_symp branching_simulation_intro)

lemma establish_sr_branching_bisim:
  assumes
    \<open>\<forall>\<alpha> p'. p \<mapsto> \<alpha> p' \<longrightarrow>
    ((\<alpha> = \<tau> \<and> p' ~SRBB q) \<or> (\<exists>q' q''. q \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> p ~SRBB q' \<and> p' ~SRBB q''))\<close>
    \<open>\<forall>\<alpha> q'. q \<mapsto> \<alpha> q' \<longrightarrow>
    ((\<alpha> = \<tau> \<and> p ~SRBB q') \<or> (\<exists>p' p''. p \<Zsurj> p' \<and> p' \<mapsto> \<alpha> p'' \<and> p' ~SRBB q \<and> p'' ~SRBB q'))\<close>
    \<open>stable_state p \<longrightarrow> (\<exists>q'. q \<Zsurj> q' \<and> p ~SRBB q' \<and> stable_state q')\<close>
    \<open>stable_state q \<longrightarrow> (\<exists>p'. p \<Zsurj> p' \<and> p' ~SRBB q \<and> stable_state p')\<close>
  shows \<open>p ~SRBB q\<close>
proof -
  define R where \<open>R \<equiv> \<lambda>pp qq. pp ~SRBB qq \<or> (pp = p \<and> qq = q) \<or> (pp = q \<and> qq = p)\<close>
  hence
    R_cases: \<open>\<And>pp qq. R pp qq \<Longrightarrow> pp ~SRBB qq \<or> (pp = p \<and> qq = q) \<or> (pp = q \<and> qq = p)\<close> and
    bisim_extension: \<open>\<forall>pp qq. pp ~SRBB qq \<longrightarrow> R pp qq\<close> by blast+
  have \<open>symp R\<close>
    unfolding symp_def R_def sr_branching_bisimulated_def
    by blast
  moreover have \<open>stability_respecting R\<close>
    unfolding stability_respecting_def
  proof safe
    fix pp qq
    assume \<open>R pp qq\<close> \<open>stable_state pp\<close>
    then consider \<open>pp ~SRBB qq\<close> | \<open>pp = p \<and> qq = q\<close> | \<open>pp = q \<and> qq = p\<close>
      using R_cases by blast
    thus \<open>\<exists>q'. qq \<Zsurj> q' \<and> R pp q' \<and> stable_state q'\<close>
    proof cases
      case 1
      then show ?thesis
        using branching_bisimilarity_stability \<open>stable_state pp\<close> bisim_extension
        unfolding stability_respecting_def
        by blast
    next
      case 2
      then show ?thesis
        using assms(3) \<open>stable_state pp\<close> unfolding R_def by blast
    next
      case 3
      then show ?thesis
        using assms(4) \<open>stable_state pp\<close> \<open>symp R\<close> unfolding R_def
        by (meson sr_branching_bisimulated_sym)
    qed
  qed
  moreover have \<open>branching_simulation R\<close> unfolding branching_simulation_def
  proof clarify
    fix pp \<alpha> p' qq
    assume bc:
      \<open>R pp qq\<close> \<open>pp \<mapsto> \<alpha> p'\<close>
      \<open>\<nexists>q' q''. qq \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> R pp q' \<and> R p' q''\<close>
    then consider \<open>pp ~SRBB qq\<close> | \<open>pp = p \<and> qq = q\<close> | \<open>pp = q \<and> qq = p\<close>
      using R_cases by blast
    thus \<open>\<alpha> = \<tau> \<and> R p' qq\<close>
    proof cases
      case 1
      then show ?thesis
        by (smt (verit, del_insts) bc bisim_extension
            branching_bisimilarity_branching_sim branching_simulation_def)
    next
      case 2
      then show ?thesis
        using bc assms(1) bisim_extension by blast
    next
      case 3
      then show ?thesis
        using bc assms(2) bisim_extension sr_branching_bisimulated_sym by metis
    qed
  qed
  moreover have \<open>R p q\<close> unfolding R_def by blast
  ultimately show ?thesis
    unfolding sr_branching_bisimulated_def by blast
qed

lemma sr_branching_bisimulation_stuttering:
  assumes
    \<open>pp \<noteq> []\<close>
    \<open>\<forall>i < length pp - 1.  pp!i \<mapsto> \<tau> pp!(Suc i)\<close>
    \<open>hd pp ~SRBB last pp\<close>
    \<open>i < length pp\<close>
  shows
    \<open>hd pp ~SRBB pp!i\<close>
proof -
  have chain_reachable: \<open>\<forall>j < length pp. \<forall>i \<le> j. pp!i \<Zsurj> pp!j\<close>
    using tau_chain_reachabilty assms(2) .
  hence chain_hd_last:
    \<open>\<forall>i < length pp. hd pp \<Zsurj> pp!i\<close>
    \<open>\<forall>i < length pp.  pp!i \<Zsurj> last pp\<close>
    by (auto simp add: assms(1) hd_conv_nth last_conv_nth)
  define R where
    \<open>R \<equiv> \<lambda>p q. (p = hd pp \<and> (\<exists>i < length pp. pp!i = q))
        \<or> ((q = hd pp \<and> (\<exists>i < length pp. pp!i = p))) \<or> p ~SRBB q\<close>
  have later_hd_sim: \<open>\<And>i p' \<alpha>. i < length pp \<Longrightarrow> pp!i \<mapsto> \<alpha> p'
    \<Longrightarrow> (hd pp) \<Zsurj> (pp!i) \<and> (pp!i) \<mapsto> \<alpha> p' \<and> R (pp!i) (pp!i) \<and> R p' p'\<close>
    using chain_hd_last sr_branching_bisimulated_reflp
    unfolding R_def
    by (simp add: reflp_def)
  have hd_later_sim: \<open>\<And>i p' \<alpha>. i < length pp - 1 \<Longrightarrow> (hd pp) \<mapsto> \<alpha> p'
    \<Longrightarrow> (\<exists>q' q''. (pp!i) \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> R (hd pp) q' \<and> R p' q'')\<close>
  proof -
    fix i p' \<alpha>
    assume case_assm: \<open>i < length pp - 1\<close> \<open>(hd pp) \<mapsto> \<alpha> p'\<close>
    hence \<open>(\<alpha> = \<tau> \<and> p' ~SRBB (last pp))
        \<or> (\<exists>q' q''. (last pp) \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> (hd pp) ~SRBB q' \<and> p' ~SRBB q'')\<close>
      using assms branching_bisimilarity_branching_sim branching_simulation_def
      by auto
    thus \<open>(\<exists>q' q''. (pp!i) \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> R (hd pp) q' \<and> R p' q'')\<close>
    proof
      assume tau_null_step: \<open>\<alpha> = \<tau> \<and> p' ~SRBB last pp\<close>
      have \<open>pp ! i \<Zsurj> (pp!(length pp - 2))\<close>
        using case_assm(1) chain_reachable by force
      moreover have \<open>pp!(length pp - 2) \<mapsto> \<alpha> (last pp)\<close>
        using assms(1,2) case_assm(1) last_conv_nth tau_null_step
        by (metis Nat.lessE Suc_1 Suc_diff_Suc less_Suc_eq zero_less_Suc zero_less_diff)
      moreover have \<open>R (hd pp) (pp!(length pp - 2)) \<and> R p' (last pp)\<close>
        unfolding R_def
        by (metis assms(1) diff_less length_greater_0_conv less_2_cases_iff tau_null_step)
      ultimately show \<open>\<exists>q' q''. pp ! i \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> R (hd pp) q' \<and> R p' q''\<close>
        by blast
    next
      assume \<open>\<exists>q' q''. last pp \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> hd pp ~SRBB q' \<and> p' ~SRBB q''\<close>
      hence \<open>\<exists>q' q''. last pp \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> R (hd pp) q' \<and> R p' q''\<close>
        unfolding R_def by blast
      moreover have \<open>i < length pp\<close> using case_assm by auto
      ultimately show \<open>\<exists>q' q''. pp ! i \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> R (hd pp) q' \<and> R p' q''\<close>
        using chain_hd_last silent_reachable_trans by blast
    qed
  qed
  have \<open>branching_simulation R\<close>
  proof (rule branching_simulation_intro)
    fix p \<alpha> p' q
    assume challenge: \<open>R p q\<close> \<open>p \<mapsto> \<alpha> p'\<close>
    from this(1) consider
      \<open>(p = hd pp \<and> (\<exists>i < length pp. pp!i = q))\<close> |
      \<open>(q = hd pp \<and> (\<exists>i < length pp. pp!i = p))\<close> |
      \<open> p ~SRBB q\<close> unfolding R_def by blast
    thus \<open>\<alpha> = \<tau> \<and> R p' q \<or> (\<exists>q' q''. q \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> R p q' \<and> R p' q'')\<close>
    proof cases
      case 1
      then obtain i where i_spec: \<open>i < length pp\<close> \<open>pp ! i = q\<close> by blast
      from 1 have \<open>p = hd pp\<close> ..
      show ?thesis
      proof (cases \<open>i = length pp - 1\<close>)
        case True
        then have \<open>q = last pp\<close> using i_spec assms(1)
          by (simp add: last_conv_nth)
        then show ?thesis using challenge(2) assms(3) branching_bisimilarity_branching_sim
          unfolding R_def branching_simulation_def \<open>p = hd pp\<close>
          by metis
      next
        case False
        hence \<open>i < length pp - 1\<close> using i_spec by auto
        then show ?thesis using \<open>p = hd pp\<close> i_spec hd_later_sim challenge(2) by blast
      qed
    next
      case 2
      then show ?thesis
        using later_hd_sim challenge(2) by blast
    next
      case 3
      then show ?thesis
        using challenge(2) branching_bisimilarity_branching_sim
        unfolding branching_simulation_def R_def by metis
    qed
  qed
  moreover have \<open>symp R\<close>
    using sr_branching_bisimulated_sym
    unfolding R_def sr_branching_bisimulated_def
    by (smt (verit, best) sympI)
  moreover have \<open>stability_respecting R\<close>
    using assms(3) stable_state_stable sr_branching_bisimulated_sym
      branching_bisimilarity_stability
    unfolding R_def stability_respecting_def
    by (metis chain_hd_last)
  moreover have \<open>\<And>i. i < length pp \<Longrightarrow> R (hd pp) (pp!i)\<close> unfolding R_def by auto
  ultimately show ?thesis
    using assms(4) sr_branching_bisimulated_def by blast
qed

lemma sr_branching_bisimulation_stabilizes:
  assumes
    \<open>sr_branching_bisimulated p q\<close>
    \<open>stable_state p\<close>
  shows
    \<open>\<exists>q'. q \<Zsurj> q' \<and> sr_branching_bisimulated p q' \<and> stable_state q'\<close>
proof -
  from assms obtain R where
    R_spec: \<open>branching_simulation R\<close> \<open>symp R\<close> \<open>stability_respecting R\<close> \<open>R p q\<close>
    unfolding sr_branching_bisimulated_def by blast
  then obtain q' where \<open>q \<Zsurj> q'\<close> \<open>stable_state q'\<close>
    using assms(2) unfolding stability_respecting_def by blast
  moreover have \<open>sr_branching_bisimulated p q'\<close>
    using sr_branching_bisimulation_stuttering
     assms(1) calculation(1) sr_branching_bisimulated_def sympD
    by (metis assms(2) sr_branching_bisimulation_silently_retained stable_state_stable)
  ultimately show ?thesis by blast
qed

lemma sr_branching_bisim_stronger:
  assumes
    \<open>sr_branching_bisimulated p q\<close>
  shows
    \<open>branching_bisimulated p q\<close>
  using assms unfolding sr_branching_bisimulated_def branching_bisimulated_def by auto

subsection \<open>\<^type>\<open>hml_srbb\<close> as Modal Characterization of Stability-Respecting Branching Bisimilarity\<close>

lemma modal_sym: \<open>symp (preordered UNIV)\<close>
proof -
  have \<open>\<nexists> p q. preordered UNIV p q \<and> \<not>preordered UNIV q p\<close>
  proof safe
    fix p q
    assume contradiction:
      \<open>preordered UNIV p q\<close>
      \<open>\<not>preordered UNIV q p\<close>
    then obtain \<phi> where \<phi>_distinguishes: \<open>distinguishes \<phi> q p\<close> by auto
    thus False
    proof (cases \<phi>)
      case TT
      then show ?thesis using \<phi>_distinguishes by auto
    next
      case (Internal \<chi>)
      hence \<open>distinguishes (ImmConj {undefined} (\<lambda>i. Neg \<chi>)) p q\<close>
        using \<phi>_distinguishes by simp
      then show ?thesis using contradiction preordered_no_distinction by blast
    next
      case (ImmConj I \<Psi>)
      then obtain i where i_def: \<open>i \<in> I\<close> \<open>hml_srbb_conj.distinguishes (\<Psi> i) q p\<close>
        using \<phi>_distinguishes srbb_dist_imm_conjunction_implies_dist_conjunct by auto
      then show ?thesis
      proof (cases \<open>\<Psi> i\<close>)
        case (Pos \<chi>)
        hence \<open>distinguishes (ImmConj {undefined} (\<lambda>i. Neg \<chi>)) p q\<close> using i_def by simp
        thus ?thesis using contradiction preordered_no_distinction by blast
      next
        case (Neg \<chi>)
        hence \<open>distinguishes (Internal \<chi>) p q\<close> using i_def by simp
        thus ?thesis using contradiction preordered_no_distinction by blast
      qed
    qed
  qed
  thus ?thesis unfolding symp_def by blast
qed

lemma modal_branching_sim: \<open>branching_simulation (preordered UNIV)\<close>
proof -
  have \<open>\<nexists>p \<alpha> p' q. (preordered UNIV) p q \<and> p \<mapsto> \<alpha> p' \<and>
      (\<alpha> \<noteq> \<tau> \<or> \<not>(preordered UNIV) p' q) \<and>
      (\<forall>q' q''. q \<Zsurj> q' \<longrightarrow> q' \<mapsto> \<alpha> q''
        \<longrightarrow> \<not> preordered UNIV p q' \<or> \<not> preordered UNIV p' q'')\<close>
  proof clarify
    fix p \<alpha> p' q
    define Q\<alpha> where \<open>Q\<alpha> \<equiv> {q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. distinguishes \<phi> p q')}\<close>
    assume contradiction:
      \<open>preordered UNIV p q\<close> \<open>p \<mapsto> \<alpha> p'\<close>
      \<open>\<forall>q' q''. q \<Zsurj> q' \<longrightarrow> q' \<mapsto> \<alpha> q''
        \<longrightarrow> \<not> preordered UNIV p q' \<or> \<not> preordered UNIV p' q''\<close>
      \<open>\<alpha> \<noteq> \<tau> \<or> \<not> preordered UNIV p' q\<close>
    hence distinctions: \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow>
      (\<exists>\<phi>. distinguishes \<phi> p q') \<or>
      (\<forall>q''. q' \<mapsto>a \<alpha> q'' \<longrightarrow> (\<exists>\<phi>. distinguishes \<phi> p' q''))\<close>
      using preordered_no_distinction
      by (metis equivpI equivp_def lts_semantics.preordered_preord modal_sym)
    hence \<open>\<forall>q''. \<forall>q'\<in>Q\<alpha>.
        q' \<mapsto>a \<alpha> q'' \<longrightarrow> (\<exists>\<phi>. distinguishes \<phi> p' q'')\<close>
      unfolding Q\<alpha>_def by auto
    hence \<open>\<forall>q''. (\<exists>q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. distinguishes \<phi> p q') \<and> q' \<mapsto>a \<alpha> q'')
        \<longrightarrow> (\<exists>\<phi>. distinguishes \<phi> p' q'')\<close>
      unfolding Q\<alpha>_def by blast
    then obtain \<Phi>\<alpha> where
      \<open>\<forall>q''. (\<exists>q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. distinguishes \<phi> p q') \<and> q' \<mapsto>a \<alpha> q'')
        \<longrightarrow> distinguishes (\<Phi>\<alpha> q'') p' q''\<close> by metis
    hence distinctions_\<alpha>: \<open>\<forall>q'\<in>Q\<alpha>. \<forall>q''.
        q' \<mapsto>a \<alpha> q'' \<longrightarrow> distinguishes (\<Phi>\<alpha> q'') p' q''\<close>
      unfolding Q\<alpha>_def by blast
    from distinctions obtain \<Phi>\<eta> where
      \<open>\<forall>q'. q'\<in>{q'. q \<Zsurj> q' \<and> (\<exists>\<phi>. distinguishes \<phi> p q')}
        \<longrightarrow> distinguishes (\<Phi>\<eta> q') p q'\<close> unfolding mem_Collect_eq by moura
    with distinction_conjunctification obtain \<Psi>\<eta> where distinctions_\<eta>:
      \<open>\<forall>q'\<in>{q'. q \<Zsurj> q' \<and> (\<exists>\<phi>. distinguishes \<phi> p q')}.
        hml_srbb_conj.distinguishes (\<Psi>\<eta> q') p q'\<close>
      by blast
    have \<open>p \<mapsto>a \<alpha> p'\<close> using \<open>p \<mapsto> \<alpha> p'\<close> by auto
    from distinction_combination[OF this] distinctions_\<alpha> have obs_dist:
      \<open>\<forall>q'\<in>Q\<alpha>.
        hml_srbb_inner.distinguishes (Obs \<alpha> (ImmConj {q''. \<exists>q'''\<in>Q\<alpha>. q''' \<mapsto>a \<alpha> q''}
                                                     (conjunctify_distinctions \<Phi>\<alpha> p'))) p q'\<close>
      unfolding Q\<alpha>_def by blast
    with distinctions_\<eta> have
      \<open>hml_srbb_inner_models p (BranchConj \<alpha>
          (ImmConj {q''. \<exists>q'''\<in>Q\<alpha>. q''' \<mapsto>a \<alpha> q''}
                   (conjunctify_distinctions \<Phi>\<alpha> p'))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>. distinguishes \<phi> p q')} \<Psi>\<eta>)\<close>
      using contradiction(1) silent_reachable.refl
      unfolding Q\<alpha>_def distinguishes_def hml_srbb_conj.distinguishes_def
        hml_srbb_inner.distinguishes_def preordered_def
      by simp force
    moreover have \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow> \<not> hml_srbb_inner_models q'
      (BranchConj \<alpha> (ImmConj {q''. \<exists>q'''\<in>Q\<alpha>. q''' \<mapsto>a \<alpha> q''}
          (conjunctify_distinctions \<Phi>\<alpha> p')) {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>. distinguishes \<phi> p q')} \<Psi>\<eta>)\<close>
    proof safe
      fix q'
      assume contradiction: \<open>q \<Zsurj> q'\<close>
        \<open>hml_srbb_inner_models q' (BranchConj \<alpha> (ImmConj {q''. \<exists>q'''\<in>Q\<alpha>. q''' \<mapsto>a \<alpha> q''}
          (conjunctify_distinctions \<Phi>\<alpha> p')) {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>. distinguishes \<phi> p q')} \<Psi>\<eta>)\<close>
      thus \<open>False\<close>
        using obs_dist distinctions_\<eta>
        unfolding distinguishes_def hml_srbb_conj.distinguishes_def
          hml_srbb_inner.distinguishes_def Q\<alpha>_def
        by (auto) blast+
    qed
    ultimately have \<open>distinguishes (Internal (BranchConj \<alpha>
          (ImmConj {q''. \<exists>q'''\<in>Q\<alpha>. q''' \<mapsto>a \<alpha> q''} (conjunctify_distinctions \<Phi>\<alpha> p'))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>. distinguishes \<phi> p q')} \<Psi>\<eta>)) p q\<close>
      unfolding distinguishes_def Q\<alpha>_def
      using silent_reachable.refl by (auto) blast+
    thus False using contradiction(1) preordered_no_distinction by blast
  qed
  thus ?thesis
    unfolding branching_simulation_def by blast
qed

lemma logic_sr_branching_bisim_invariant:
  assumes
    \<open>sr_branching_bisimulated p0 q0\<close>
    \<open>p0 \<Turnstile>SRBB \<phi>\<close>
  shows \<open>q0 \<Turnstile>SRBB \<phi>\<close>
proof -
  have \<open>\<And>\<phi> \<chi> \<psi>.
    (\<forall>p q. sr_branching_bisimulated p q \<longrightarrow> p \<Turnstile>SRBB \<phi> \<longrightarrow> q \<Turnstile>SRBB \<phi>) \<and>
    (\<forall>p q. sr_branching_bisimulated p q \<longrightarrow> hml_srbb_inner_models p \<chi>
        \<longrightarrow> (\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>)) \<and>
    (\<forall>p q. sr_branching_bisimulated p q \<longrightarrow> hml_srbb_conjunct_models p \<psi>
        \<longrightarrow> hml_srbb_conjunct_models q \<psi>)\<close>
  proof -
    fix \<phi> \<chi> \<psi>
    show
      \<open>(\<forall>p q. sr_branching_bisimulated p q \<longrightarrow> p \<Turnstile>SRBB \<phi> \<longrightarrow> q \<Turnstile>SRBB \<phi>) \<and>
      (\<forall>p q. sr_branching_bisimulated p q \<longrightarrow> hml_srbb_inner_models p \<chi>
        \<longrightarrow> (\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>)) \<and>
      (\<forall>p q. sr_branching_bisimulated p q \<longrightarrow> hml_srbb_conjunct_models p \<psi>
        \<longrightarrow> hml_srbb_conjunct_models q \<psi>)\<close>
    proof (induct rule: hml_srbb_hml_srbb_inner_hml_srbb_conjunct.induct)
      case TT
      then show ?case by simp
    next
      case (Internal \<chi>)
      show ?case
      proof safe
        fix p q
        assume \<open>sr_branching_bisimulated p q\<close> \<open>p \<Turnstile>SRBB hml_srbb.Internal \<chi>\<close>
        then obtain p' where \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' \<chi>\<close> by auto
        hence \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>\<close>
          using Internal \<open>hml_srbb_inner_models p' \<chi>\<close>
          by (meson lts_tau.silent_reachable_trans \<open>p ~SRBB q\<close>
              sr_branching_bisimulation_silently_retained)
        thus \<open>q \<Turnstile>SRBB hml_srbb.Internal \<chi>\<close> by auto
      qed
    next
      case (ImmConj I \<Psi>)
      then show ?case by auto
    next
      case (Obs \<alpha> \<phi>)
      then show ?case
      proof (safe)
        fix p q
        assume
          \<open>sr_branching_bisimulated p q\<close>
          \<open>hml_srbb_inner_models p (hml_srbb_inner.Obs \<alpha> \<phi>)\<close>
        then obtain p' where \<open>p \<mapsto>a \<alpha> p'\<close> \<open>p' \<Turnstile>SRBB \<phi>\<close> by auto
        then obtain q' q'' where \<open>q \<Zsurj> q'\<close> \<open>q' \<mapsto>a \<alpha> q''\<close> \<open>sr_branching_bisimulated p' q''\<close>
          using sr_branching_bisimulation_sim[OF \<open>sr_branching_bisimulated p q\<close>]
              silent_reachable.refl
          by blast
        hence \<open>q'' \<Turnstile>SRBB \<phi>\<close> using \<open>p' \<Turnstile>SRBB \<phi>\<close> Obs by blast
        hence \<open>hml_srbb_inner_models q' (hml_srbb_inner.Obs \<alpha> \<phi>)\<close>
          using \<open>q' \<mapsto>a \<alpha> q''\<close> by auto
        thus \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' (hml_srbb_inner.Obs \<alpha> \<phi>)\<close>
          using \<open>q \<Zsurj> q'\<close> by blast
      qed
    next
      case (Conj I \<Psi>)
      show ?case
      proof safe
        fix p q
        assume
          \<open>sr_branching_bisimulated p q\<close>
          \<open>hml_srbb_inner_models p (hml_srbb_inner.Conj I \<Psi>)\<close>
        hence \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<Psi> i)\<close> by auto
        hence \<open>\<forall>i\<in>I. hml_srbb_conjunct_models q (\<Psi> i)\<close>
          using Conj \<open>sr_branching_bisimulated p q\<close> by blast
        hence \<open>hml_srbb_inner_models q (hml_srbb_inner.Conj I \<Psi>)\<close> by simp
        thus \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' (hml_srbb_inner.Conj I \<Psi>)\<close>
          using silent_reachable.refl by blast
      qed
    next
      case (StableConj I \<Psi>) show ?case
      proof safe
        fix p q
        assume
          \<open>sr_branching_bisimulated p q\<close>
          \<open>hml_srbb_inner_models p (StableConj I \<Psi>)\<close>
        hence \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<Psi> i)\<close>
          using stable_conj_parts by blast
        from \<open>hml_srbb_inner_models p (StableConj I \<Psi>)\<close> have \<open>stable_state p\<close> by auto
        then obtain q' where \<open>q \<Zsurj> q'\<close> \<open>stable_state q'\<close> \<open>sr_branching_bisimulated p q'\<close>
          using \<open>sr_branching_bisimulated p q\<close> sr_branching_bisimulation_stabilizes by blast
        hence \<open>\<forall>i\<in>I. hml_srbb_conjunct_models q' (\<Psi> i)\<close>
          using \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<Psi> i)\<close> StableConj by blast
        hence \<open>hml_srbb_inner_models q' (StableConj I \<Psi>)\<close> using \<open>stable_state q'\<close> by simp
        thus \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' (StableConj I \<Psi>)\<close>
          using \<open>q \<Zsurj> q'\<close> by blast
      qed
    next
      case (BranchConj \<alpha> \<phi> I \<Psi>)
      show ?case
      proof safe
        fix p q
        assume
          \<open>sr_branching_bisimulated p q\<close>
          \<open>hml_srbb_inner_models p (BranchConj \<alpha> \<phi> I \<Psi>)\<close>
        hence \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<Psi> i)\<close>
              \<open>hml_srbb_inner_models p (Obs \<alpha> \<phi>)\<close>
          using branching_conj_parts branching_conj_obs by blast+
        then obtain p' where \<open>p \<mapsto>a \<alpha> p'\<close> \<open>p' \<Turnstile>SRBB \<phi>\<close> by auto
        then obtain q' q'' where q'_q''_spec:
          \<open>q \<Zsurj> q'\<close> \<open>q' \<mapsto>a \<alpha> q''\<close>
          \<open>sr_branching_bisimulated p q'\<close> \<open>sr_branching_bisimulated p' q''\<close>
          using sr_branching_bisimulation_sim[OF \<open>sr_branching_bisimulated p q\<close>]
            silent_reachable.refl[of p]
          by blast
        hence \<open>q'' \<Turnstile>SRBB \<phi>\<close> using BranchConj.hyps \<open>p' \<Turnstile>SRBB \<phi>\<close> by auto
        hence \<open>hml_srbb_inner_models q' (Obs \<alpha> \<phi>)\<close> using q'_q''_spec by auto
        moreover have \<open>\<forall>i\<in>I. hml_srbb_conjunct_models q' (\<Psi> i)\<close>
          using BranchConj.hyps \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<Psi> i)\<close> q'_q''_spec by blast
        ultimately show \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' (BranchConj \<alpha> \<phi> I \<Psi>)\<close>
          using \<open>q \<Zsurj> q'\<close> by auto
      qed
    next
      case (Pos \<chi>)
      show ?case
      proof safe
        fix p q
        assume
          \<open>sr_branching_bisimulated p q\<close>
          \<open>hml_srbb_conjunct_models p (Pos \<chi>)\<close>
        then obtain p' where \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' \<chi>\<close> by auto
        then obtain q' where \<open>q \<Zsurj> q'\<close> \<open>hml_srbb_inner_models q' \<chi>\<close>
          using Pos \<open>p ~SRBB q\<close> sr_branching_bisimulation_silently_retained
          by (meson  silent_reachable_trans)
        thus \<open>hml_srbb_conjunct_models q (Pos \<chi>)\<close> by auto
      qed
    next
      case (Neg \<chi>)
      show ?case
      proof safe
        fix p q
        assume
          \<open>sr_branching_bisimulated p q\<close>
          \<open>hml_srbb_conjunct_models p (Neg \<chi>)\<close>
        hence \<open>\<forall>p'. p \<Zsurj> p' \<longrightarrow> \<not>hml_srbb_inner_models p' \<chi>\<close> by simp
        moreover have
          \<open>(\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>)
            \<longrightarrow> (\<exists>p'. p \<Zsurj> p' \<and> hml_srbb_inner_models p' \<chi>)\<close>
          using Neg sr_branching_bisimulated_sym[OF \<open>sr_branching_bisimulated p q\<close>]
            sr_branching_bisimulation_silently_retained
          by (meson silent_reachable_trans)
        ultimately have \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow> \<not>hml_srbb_inner_models q' \<chi>\<close> by blast
        thus \<open>hml_srbb_conjunct_models q (Neg \<chi>)\<close> by simp
      qed
    qed
  qed
  thus ?thesis using assms by blast
qed

lemma sr_branching_bisim_is_hmlsrbb: \<open>sr_branching_bisimulated p q = preordered UNIV p q\<close>
  using modal_stability_respecting modal_sym modal_branching_sim
    logic_sr_branching_bisim_invariant \<O>_sup preordered_def
  unfolding sr_branching_bisimulated_def by metis

lemma sr_branching_bisimulated_transitive:
  assumes
    \<open>p ~SRBB q\<close>
    \<open>q ~SRBB r\<close>
  shows
    \<open>p ~SRBB r\<close>
  using assms unfolding sr_branching_bisim_is_hmlsrbb by simp

lemma sr_branching_bisimulated_equivalence: \<open>equivp (~SRBB)\<close>
proof (rule equivpI)
  show \<open>symp (~SRBB)\<close> using sr_branching_bisimulated_symp .
  show \<open>reflp (~SRBB)\<close> using sr_branching_bisimulated_reflp .
  show \<open>transp (~SRBB)\<close>
    unfolding transp_def using sr_branching_bisimulated_transitive by blast
qed

lemma sr_branching_bisimulation_stuttering_all:
  assumes
    \<open>pp \<noteq> []\<close>
    \<open>\<forall>i < length pp - 1.  pp!i \<mapsto> \<tau> pp!(Suc i)\<close>
    \<open>hd pp ~SRBB last pp\<close>
    \<open>i \<le> j\<close> \<open>j < length pp\<close>
  shows
    \<open>pp!i ~SRBB pp!j\<close>
  using assms equivp_def sr_branching_bisimulated_equivalence equivp_def order_le_less_trans
    sr_branching_bisimulation_stuttering
  by metis

theorem sr_branching_bisim_coordinate: \<open>(p ~SRBB q) = (p \<preceq> (E \<infinity> \<infinity> \<infinity> \<infinity> \<infinity> \<infinity> \<infinity> \<infinity>) q)\<close>
  using sr_branching_bisim_is_hmlsrbb \<O>_sup
  unfolding expr_preord_def by auto

end

end
