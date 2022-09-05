section \<open>Completeness\<close>

theory Completeness imports Prover Semantics begin

subsection \<open>Hintikka Counter Model\<close>

locale Hintikka =
  fixes A B :: \<open>fm set\<close>
  assumes
    Basic: \<open>\<^bold>\<ddagger>P ts \<in> A \<Longrightarrow> \<^bold>\<ddagger>P ts \<in> B \<Longrightarrow> False\<close> and
    FlsA: \<open>\<^bold>\<bottom> \<notin> A\<close> and
    ImpA: \<open>p \<^bold>\<longrightarrow> q \<in> A \<Longrightarrow> p \<in> B \<or> q \<in> A\<close> and
    ImpB: \<open>p \<^bold>\<longrightarrow> q \<in> B \<Longrightarrow> p \<in> A \<and> q \<in> B\<close> and
    UniA: \<open>\<^bold>\<forall>p \<in> A \<Longrightarrow> \<forall>t. \<langle>t\<rangle>p \<in> A\<close> and
    UniB: \<open>\<^bold>\<forall>p \<in> B \<Longrightarrow> \<exists>t. \<langle>t\<rangle>p \<in> B\<close>

abbreviation \<open>M A \<equiv> \<lbrakk>\<^bold>#, \<^bold>\<dagger>, \<lambda>P ts. \<^bold>\<ddagger>P ts \<in> A\<rbrakk>\<close>

lemma id_tm [simp]: \<open>\<lparr>\<^bold>#, \<^bold>\<dagger>\<rparr> t = t\<close>
  by (induct t) (auto cong: map_cong)

lemma size_sub_fm [simp]: \<open>size (sub_fm s p) = size p\<close>
  by (induct p arbitrary: s) auto

theorem Hintikka_counter_model:
  assumes \<open>Hintikka A B\<close>
  shows \<open>(p \<in> A \<longrightarrow> M A p) \<and> (p \<in> B \<longrightarrow> \<not> M A p)\<close>
proof (induct p rule: wf_induct [where r=\<open>measure size\<close>])
  case 1
  then show ?case ..
next
  case (2 x)
  then show ?case
  proof (cases x; safe del: notI)
    case Falsity
    show \<open>\<^bold>\<bottom> \<in> A \<Longrightarrow> M A \<^bold>\<bottom>\<close> \<open>\<^bold>\<bottom> \<in> B \<Longrightarrow> \<not> M A \<^bold>\<bottom>\<close>
      using Hintikka.FlsA assms by simp_all
  next
    case (Pre P ts)
    show \<open>\<^bold>\<ddagger>P ts \<in> A \<Longrightarrow> M A (\<^bold>\<ddagger>P ts)\<close> \<open>\<^bold>\<ddagger>P ts \<in> B \<Longrightarrow> \<not> M A (\<^bold>\<ddagger>P ts)\<close>
      using Hintikka.Basic assms by (auto cong: map_cong)
  next
    case (Imp p q)
    show \<open>p \<^bold>\<longrightarrow> q \<in> A \<Longrightarrow> M A (p \<^bold>\<longrightarrow> q)\<close> \<open>p \<^bold>\<longrightarrow> q \<in> B \<Longrightarrow> \<not> M A (p \<^bold>\<longrightarrow> q)\<close>
      using assms Hintikka.ImpA[of A B p q] Hintikka.ImpB[of A B p q] Imp 2 by auto
  next
    case (Uni p)
    have \<open>\<langle>t\<rangle>p \<in> A \<Longrightarrow> M A (\<langle>t\<rangle>p)\<close> \<open>\<langle>t\<rangle>p \<in> B \<Longrightarrow> \<not> M A (\<langle>t\<rangle>p)\<close> for t
      using Uni 2 by (metis fm.size(8) in_measure lessI less_add_same_cancel1 size_sub_fm)+
    then show \<open>\<^bold>\<forall>p \<in> A \<Longrightarrow> M A (\<^bold>\<forall>p)\<close> \<open>\<^bold>\<forall>p \<in> B \<Longrightarrow> \<not> M A (\<^bold>\<forall>p)\<close>
      using assms Hintikka.UniA[of A B p] Hintikka.UniB[of A B p] by auto
  qed
qed

subsection \<open>Escape Paths Form Hintikka Sets\<close>

lemma sset_sdrop: \<open>sset (sdrop n s) \<subseteq> sset s\<close>
  by (induct n arbitrary: s) (auto intro: stl_sset in_mono)

lemma epath_sdrop: \<open>epath steps \<Longrightarrow> epath (sdrop n steps)\<close>
  by (induct n) (auto elim: epath.cases)

lemma eff_preserves_Pre:
  assumes \<open>effStep ((A, B), r) ss\<close> \<open>(A', B') |\<in>| ss\<close>
  shows \<open>(\<^bold>\<ddagger>P ts [\<in>] A \<Longrightarrow> \<^bold>\<ddagger>P ts [\<in>] A')\<close> \<open>\<^bold>\<ddagger>P ts [\<in>] B \<Longrightarrow> \<^bold>\<ddagger>P ts [\<in>] B'\<close>
  using assms by (induct r \<open>(A, B)\<close> rule: eff.induct) (auto split: if_splits)

lemma epath_eff:
  assumes \<open>epath steps\<close> \<open>effStep (shd steps) ss\<close>
  shows \<open>fst (shd (stl steps)) |\<in>| ss\<close>
  using assms by (auto elim: epath.cases)

abbreviation \<open>lhs s \<equiv> fst (fst s)\<close>
abbreviation \<open>rhs s \<equiv> snd (fst s)\<close>
abbreviation \<open>lhsd s \<equiv> lhs (shd s)\<close>
abbreviation \<open>rhsd s \<equiv> rhs (shd s)\<close>

lemma epath_Pre_sdrop:
  assumes \<open>epath steps\<close> shows
    \<open>\<^bold>\<ddagger>P ts [\<in>] lhs (shd steps) \<Longrightarrow> \<^bold>\<ddagger>P ts [\<in>] lhsd (sdrop m steps)\<close>
    \<open>\<^bold>\<ddagger>P ts [\<in>] rhs (shd steps) \<Longrightarrow> \<^bold>\<ddagger>P ts [\<in>] rhsd (sdrop m steps)\<close>
  using assms eff_preserves_Pre
  by (induct m arbitrary: steps) (simp; metis (no_types, lifting) epath.cases surjective_pairing)+

lemma Saturated_sdrop:
  assumes \<open>Saturated steps\<close>
  shows \<open>Saturated (sdrop n steps)\<close>
  using assms unfolding Saturated_def saturated_def by (simp add: alw_iff_sdrop)

definition treeA :: \<open>(sequent \<times> rule) stream \<Rightarrow> fm set\<close> where
  \<open>treeA steps \<equiv> \<Union>s \<in> sset steps. set (lhs s)\<close>

definition treeB :: \<open>(sequent \<times> rule) stream \<Rightarrow> fm set\<close> where
  \<open>treeB steps \<equiv> \<Union>s \<in> sset steps. set (rhs s)\<close>

lemma treeA_snth: \<open>p \<in> treeA steps \<Longrightarrow> \<exists>n. p [\<in>] lhsd (sdrop n steps)\<close>
  unfolding treeA_def using sset_range[of steps] by simp

lemma treeB_snth: \<open>p \<in> treeB steps \<Longrightarrow> \<exists>n. p [\<in>] rhsd (sdrop n steps)\<close>
  unfolding treeB_def using sset_range[of steps] by simp

lemma treeA_sdrop: \<open>treeA (sdrop n steps) \<subseteq> treeA steps\<close>
  unfolding treeA_def by (induct n) (simp, metis SUP_subset_mono order_refl sset_sdrop)

lemma treeB_sdrop: \<open>treeB (sdrop n steps) \<subseteq> treeB steps\<close>
  unfolding treeB_def by (induct n) (simp, metis SUP_subset_mono order_refl sset_sdrop)

lemma enabled_ex_taken:
  assumes \<open>epath steps\<close> \<open>Saturated steps\<close> \<open>enabled r (fst (shd steps))\<close>
  shows \<open>\<exists>k. takenAtStep r (shd (sdrop k steps))\<close>
  using assms unfolding Saturated_def saturated_def UNIV_rules by (auto simp: ev_iff_sdrop)

lemma Hintikka_epath:
  assumes \<open>epath steps\<close> \<open>Saturated steps\<close>
  shows \<open>Hintikka (treeA steps) (treeB steps)\<close>
proof
  fix P ts
  assume \<open>\<^bold>\<ddagger>P ts \<in> treeA steps\<close>
  then obtain m where m: \<open>\<^bold>\<ddagger>P ts [\<in>] lhsd (sdrop m steps)\<close>
    using treeA_snth by auto

  assume \<open>\<^bold>\<ddagger>P ts \<in> treeB steps\<close>
  then obtain k where k: \<open>\<^bold>\<ddagger>P ts [\<in>] rhsd (sdrop k steps)\<close>
    using treeB_snth by auto

  let ?j = \<open>m + k\<close>
  let ?jstep = \<open>shd (sdrop ?j steps)\<close>

  have \<open>\<^bold>\<ddagger>P ts [\<in>] lhs ?jstep\<close>
    using assms m epath_sdrop epath_Pre_sdrop by (metis (no_types, lifting) sdrop_add)
  moreover have \<open>\<^bold>\<ddagger>P ts [\<in>] rhs ?jstep\<close>
    using assms k epath_sdrop epath_Pre_sdrop by (metis (no_types, lifting) add.commute sdrop_add)
  ultimately have \<open>enabled (Axiom P ts) (fst ?jstep)\<close>
    unfolding enabled_def by (metis eff.simps(2) prod.exhaust_sel)
  then obtain j' where \<open>takenAtStep (Axiom P ts) (shd (sdrop j' steps))\<close>
    using enabled_ex_taken[OF epath_sdrop[OF assms(1)] Saturated_sdrop[OF assms(2)]] by auto
  then have \<open>eff (snd (shd (sdrop j' steps))) (fst (shd (sdrop j' steps))) = None\<close>
    using assms(1) epath_sdrop epath_eff
    by (metis (no_types, lifting) eff.simps(2) epath.simps equalsffemptyD surjective_pairing)
  then show False
    using assms(1) epath_sdrop by (metis epath.cases option.discI)
next
  show \<open>\<^bold>\<bottom> \<notin> treeA steps\<close>
  proof
    assume \<open>\<^bold>\<bottom> \<in> treeA steps\<close>
    then have \<open>\<exists>j. enabled FlsL (fst (shd (sdrop j steps)))\<close>
      unfolding enabled_def using treeA_snth by (metis eff.simps(3) prod.exhaust_sel sdrop_simps(1))
    then obtain j where \<open>takenAtStep FlsL (shd (sdrop j steps))\<close> (is \<open>takenAtStep _ (shd ?steps)\<close>)
      using enabled_ex_taken[OF epath_sdrop[OF assms(1)] Saturated_sdrop[OF assms(2)]] by auto
    then have \<open>eff (snd (shd ?steps)) (fst (shd ?steps)) = None\<close>
      using assms(1) epath_sdrop epath_eff
      by (metis (no_types, lifting) eff.simps(3) epath.simps equalsffemptyD surjective_pairing)
    then show False
      using assms(1) epath_sdrop by (metis epath.cases option.discI)
  qed
next
  fix p q
  assume \<open>p \<^bold>\<longrightarrow> q \<in> treeA steps\<close>
  then have \<open>\<exists>k. enabled (ImpL p q) (fst (shd (sdrop k steps)))\<close>
    unfolding enabled_def using treeA_snth by (metis eff.simps(5) prod.exhaust_sel sdrop_simps(1))
  then obtain j where \<open>takenAtStep (ImpL p q) (shd (sdrop j steps))\<close> (is \<open>takenAtStep _ (shd ?s)\<close>)
    using enabled_ex_taken[OF epath_sdrop[OF assms(1)] Saturated_sdrop[OF assms(2)]] by auto
  then have \<open>fst (shd (stl ?s)) |\<in>|
      {| (lhsd ?s [\<div>] (p \<^bold>\<longrightarrow> q), p # rhsd ?s), (q # lhsd ?s [\<div>] (p \<^bold>\<longrightarrow> q), rhsd ?s) |}\<close>
    using assms(1) epath_sdrop epath_eff
    by (metis (no_types, lifting) eff.simps(5) epath.cases option.distinct(1) prod.collapse)
  then have \<open>p [\<in>] rhs (shd (stl ?s)) \<or> q [\<in>] lhs (shd (stl ?s))\<close>
    by auto
  then have \<open>p \<in> treeB (stl ?s) \<or> q \<in> treeA (stl ?s)\<close>
    unfolding treeA_def treeB_def by (meson UN_I shd_sset)
  then show \<open>p \<in> treeB steps \<or> q \<in> treeA steps\<close>
    using treeA_sdrop treeB_sdrop by (metis sdrop_simps(2) subsetD)
next
  fix p q
  assume \<open>p \<^bold>\<longrightarrow> q \<in> treeB steps\<close>
  then have \<open>\<exists>k. enabled (ImpR p q) (fst (shd (sdrop k steps)))\<close>
    unfolding enabled_def using treeB_snth by (metis eff.simps(6) prod.exhaust_sel sdrop_simps(1))
  then obtain j where \<open>takenAtStep (ImpR p q) (shd (sdrop j steps))\<close> (is \<open>takenAtStep _ (shd ?s)\<close>)
    using enabled_ex_taken[OF epath_sdrop[OF assms(1)] Saturated_sdrop[OF assms(2)]] by auto
  then have \<open>fst (shd (stl ?s)) |\<in>| {| (p # lhsd ?s, q # rhsd ?s [\<div>] (p \<^bold>\<longrightarrow> q)) |}\<close>
    using assms(1) epath_sdrop epath_eff
    by (metis (no_types, lifting) eff.simps(6) epath.cases option.distinct(1) prod.collapse)
  then have \<open>p [\<in>] lhs (shd (stl ?s)) \<and> q [\<in>] rhs (shd (stl ?s))\<close>
    by auto
  then have \<open>p \<in> treeA (stl ?s) \<and> q \<in> treeB (stl ?s)\<close>
    unfolding treeA_def treeB_def by (meson UN_I shd_sset)
  then show \<open>p \<in> treeA steps \<and> q \<in> treeB steps\<close>
    using treeA_sdrop treeB_sdrop by (metis sdrop_simps(2) subsetD)
next
  fix p
  assume *: \<open>\<^bold>\<forall>p \<in> treeA steps\<close>
  show \<open>\<forall>t. \<langle>t\<rangle>p \<in> treeA steps\<close>
  proof
    fix t
    from * have \<open>\<exists>k. enabled (UniL t p) (fst (shd (sdrop k steps)))\<close>
      unfolding enabled_def using treeA_snth by (metis eff.simps(7) prod.exhaust_sel sdrop_simps(1))
    then obtain j where \<open>takenAtStep (UniL t p) (shd (sdrop j steps))\<close>(is \<open>takenAtStep _ (shd ?s)\<close>)
      using enabled_ex_taken[OF epath_sdrop[OF assms(1)] Saturated_sdrop[OF assms(2)]] by auto
    then have \<open>fst (shd (stl ?s)) |\<in>| {| (\<langle>t\<rangle>p # lhsd ?s, rhsd ?s) |}\<close>
      using assms(1) epath_sdrop epath_eff
      by (metis (no_types, lifting) eff.simps(7) epath.cases option.distinct(1) prod.collapse)
    then have \<open>\<langle>t\<rangle>p [\<in>] lhs (shd (stl ?s))\<close>
      by auto
    then have \<open>\<langle>t\<rangle>p \<in> treeA (stl ?s)\<close>
      unfolding treeA_def by (meson UN_I shd_sset)
    then show \<open>\<langle>t\<rangle>p \<in> treeA steps\<close>
      using treeA_sdrop by (metis sdrop_simps(2) subsetD)
  qed
next
  fix p
  assume *: \<open>\<^bold>\<forall>p \<in> treeB steps\<close>
  then have \<open>\<exists>k. enabled (UniR p) (fst (shd (sdrop k steps)))\<close>
    unfolding enabled_def using treeB_snth by (metis eff.simps(8) prod.exhaust_sel sdrop_simps(1))
  then obtain j where \<open>takenAtStep (UniR p) (shd (sdrop j steps))\<close>(is \<open>takenAtStep _ (shd ?s)\<close>)
    using enabled_ex_taken[OF epath_sdrop[OF assms(1)] Saturated_sdrop[OF assms(2)]] by auto
  then have \<open>fst (shd (stl ?s)) |\<in>|
        {| (lhsd ?s, \<langle>\<^bold>#(fresh (lhsd ?s @ rhsd ?s))\<rangle>p # rhsd ?s [\<div>] \<^bold>\<forall>p) |}\<close>
    using assms(1) epath_sdrop epath_eff
    by (metis (no_types, lifting) eff.simps(8) epath.cases option.distinct(1) prod.collapse)
  then have \<open>\<exists>t. \<langle>t\<rangle>p [\<in>] rhs (shd (stl ?s))\<close>
    by auto
  then have \<open>\<exists>t. \<langle>t\<rangle>p \<in> treeB (stl ?s)\<close>
    unfolding treeB_def by (meson UN_I shd_sset)
  then show \<open>\<exists>t. \<langle>t\<rangle>p \<in> treeB steps\<close>
    using treeB_sdrop by (metis sdrop_simps(2) subsetD)
qed

subsection \<open>Completeness\<close>

lemma fair_stream_rules: \<open>Fair_Stream.fair rules\<close>
  unfolding rules_def using fair_stream surj_rule_of_nat .

lemma fair_rules: \<open>fair rules\<close>
  using fair_stream_rules unfolding Fair_Stream.fair_def fair_def alw_iff_sdrop ev_holds_sset
  by (metis dual_order.refl le_Suc_ex sdrop_snth snth_sset)

lemma epath_prover:
  fixes A B :: \<open>fm list\<close>
  defines \<open>t \<equiv> prover (A, B)\<close>
  shows \<open>(fst (root t) = (A, B) \<and> wf t \<and> tfinite t) \<or>
    (\<exists>steps. fst (shd steps) = (A, B) \<and> epath steps \<and> Saturated steps)\<close> (is \<open>?A \<or> ?B\<close>)
proof -
  { assume \<open>\<not> ?A\<close>
    with assms have \<open>\<not> tfinite (mkTree rules (A, B))\<close>
      unfolding prover_def using wf_mkTree fair_rules by simp
    then obtain steps where \<open>ipath (mkTree rules (A, B)) steps\<close> using Konig by blast
    with assms have \<open>fst (shd steps) = (A, B) \<and> epath steps \<and> Saturated steps\<close>
      by (metis (no_types, lifting) fair_rules UNIV_I fst_conv ipath.cases
          ipath_mkTree_Saturated mkTree.simps(1) wf_ipath_epath wf_mkTree)
    then have ?B by blast
  }
  then show ?thesis by blast
qed

lemma epath_countermodel:
  assumes \<open>fst (shd steps) = (A, B)\<close> \<open>epath steps\<close> \<open>Saturated steps\<close>
  shows \<open>\<exists>(E :: _ \<Rightarrow> tm) F G. \<not> sc (E, F, G) (A, B)\<close>
proof -
  have \<open>Hintikka (treeA steps) (treeB steps)\<close> (is \<open>Hintikka ?A ?B\<close>)
    using assms Hintikka_epath assms by simp
  moreover have \<open>\<forall>p [\<in>] A. p \<in> ?A\<close> \<open>\<forall>p [\<in>] B. p \<in> ?B\<close>
    using assms shd_sset unfolding treeA_def treeB_def by fastforce+
  ultimately have \<open>\<forall>p [\<in>] A. M ?A p\<close> \<open>\<forall>p [\<in>] B. \<not> M ?A p\<close>
    using Hintikka_counter_model assms by blast+
  then show ?thesis
    by auto
qed

theorem prover_completeness:
  assumes \<open>\<forall>(E :: _ \<Rightarrow> tm) F G. sc (E, F, G) (A, B)\<close>
  defines \<open>t \<equiv> prover (A, B)\<close>
  shows \<open>fst (root t) = (A, B) \<and> wf t \<and> tfinite t\<close>
  using assms epath_prover epath_countermodel by blast

corollary
  assumes \<open>\<forall>(E :: _ \<Rightarrow> tm) F G. \<lbrakk>E, F, G\<rbrakk> p\<close>
  defines \<open>t \<equiv> prover ([], [p])\<close>
  shows \<open>fst (root t) = ([], [p]) \<and> wf t \<and> tfinite t\<close>
  using assms prover_completeness by simp

end
