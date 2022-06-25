section\<open>The main theorem\<close>

theory Forcing_Main
  imports
    Ordinals_In_MG
    Choice_Axiom
    ZF_Trans_Interpretations

begin

subsection\<open>The generic extension is countable\<close>

lemma (in forcing_data1) surj_nat_MG : "\<exists>f. f \<in> surj(\<omega>,M[G])"
proof -
  let ?f="\<lambda>n\<in>\<omega>. val(P,G,enum`n)"
  have "x \<in> \<omega> \<Longrightarrow> val(P,G, enum ` x)\<in> M[G]" for x
    using GenExt_iff[THEN iffD2, of _ G] bij_is_fun[OF M_countable] by force
  then
  have "?f: \<omega> \<rightarrow> M[G]"
    using lam_type[of \<omega> "\<lambda>n. val(P,G,enum`n)" "\<lambda>_.M[G]"] by simp
  moreover
  have "\<exists>n\<in>\<omega>. ?f`n = x" if "x\<in>M[G]" for x
    using that GenExt_iff[of _ G] bij_is_surj[OF M_countable]
    unfolding surj_def by auto
  ultimately
  show ?thesis
    unfolding surj_def by blast
qed

lemma (in G_generic1) MG_eqpoll_nat: "M[G] \<approx> \<omega>"
proof -
  obtain f where "f \<in> surj(\<omega>,M[G])"
    using surj_nat_MG by blast
  then
  have "M[G] \<lesssim> \<omega>"
    using well_ord_surj_imp_lepoll well_ord_Memrel[of \<omega>] by simp
  moreover
  have "\<omega> \<lesssim> M[G]"
    using ext.nat_into_M subset_imp_lepoll by (auto del:lepollI)
  ultimately
  show ?thesis
    using eqpollI by simp
qed

subsection\<open>Extensions of ctms of fragments of $\ZFC$\<close>

lemma M_satT_imp_M_ZF2: "(M \<Turnstile> ZF) \<Longrightarrow> M_ZF2(M)"
proof -
  assume "M \<Turnstile> ZF"
  then
  have fin: "upair_ax(##M)" "Union_ax(##M)" "power_ax(##M)"
    "extensionality(##M)" "foundation_ax(##M)" "infinity_ax(##M)"
    unfolding ZF_def ZF_fin_def ZFC_fm_defs satT_def
    using ZFC_fm_sats[of M] by simp_all
  {
    fix \<phi> env
    assume "\<phi> \<in> formula" "env\<in>list(M)"
    moreover from \<open>M \<Turnstile> ZF\<close>
    have "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_separation_fm(p)))"
      "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_replacement_fm(p)))"
      unfolding ZF_def ZF_schemes_def by auto
    moreover from calculation
    have "arity(\<phi>) \<le> succ(length(env)) \<Longrightarrow> separation(##M, \<lambda>x. (M, Cons(x, env) \<Turnstile> \<phi>))"
      "arity(\<phi>) \<le> succ(succ(length(env))) \<Longrightarrow> strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,Cons(x,Cons(y, env))))"
      using sats_ZF_separation_fm_iff sats_ZF_replacement_fm_iff by simp_all
  }
  with fin
  show "M_ZF2(M)"
    by unfold_locales (simp_all add:replacement_assm_def ground_replacement_assm_def)
qed

lemma M_satT_imp_M_ZFC2:
  shows "(M \<Turnstile> ZFC) \<longrightarrow> M_ZFC2(M)"
proof -
  have "(M \<Turnstile> ZF) \<and> choice_ax(##M) \<longrightarrow> M_ZFC2(M)"
    using M_satT_imp_M_ZF2[of M] unfolding M_ZF2_def M_ZFC1_def M_ZFC2_def
      M_ZC_basic_def M_ZF1_def M_AC_def by auto
  then
  show ?thesis
    unfolding ZFC_def by auto
qed

lemma M_satT_instances12_imp_M_ZF2:
  assumes "(M \<Turnstile> \<cdot>Z\<cdot> \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> instances1_fms \<union> instances2_fms})"
  shows "M_ZF2(M)"
proof -
  from assms
  have fin: "upair_ax(##M)" "Union_ax(##M)" "power_ax(##M)"
    "extensionality(##M)" "foundation_ax(##M)" "infinity_ax(##M)"
    unfolding ZF_fin_def Zermelo_fms_def ZFC_fm_defs satT_def
    using ZFC_fm_sats[of M] by simp_all
  moreover
  {
    fix \<phi> env
    from \<open>M \<Turnstile> \<cdot>Z\<cdot> \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> instances1_fms \<union> instances2_fms}\<close>
    have "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_separation_fm(p)))"
      unfolding Zermelo_fms_def ZF_def instances1_fms_def
        instances2_fms_def by auto
    moreover
    assume "\<phi> \<in> formula" "env\<in>list(M)"
    ultimately
    have "arity(\<phi>) \<le> succ(length(env)) \<Longrightarrow> separation(##M, \<lambda>x. (M, Cons(x, env) \<Turnstile> \<phi>))"
      using sats_ZF_separation_fm_iff by simp_all
  }
  moreover
  {
    fix \<phi> env
    assume "\<phi> \<in> instances1_fms \<union> instances2_fms" "env\<in>list(M)"
    moreover from this and \<open>M \<Turnstile> \<cdot>Z\<cdot> \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> instances1_fms \<union> instances2_fms}\<close>
    have "M, [] \<Turnstile> \<cdot>Replacement(\<phi>)\<cdot>" by auto
    ultimately
    have "arity(\<phi>) \<le> succ(succ(length(env))) \<Longrightarrow> strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,Cons(x,Cons(y, env))))"
      using sats_ZF_replacement_fm_iff[of \<phi>] instances1_fms_type instances2_fms_type by auto
  }
  ultimately
  show ?thesis
    unfolding instances1_fms_def instances2_fms_def
    by unfold_locales (simp_all add:replacement_assm_def ground_replacement_assm_def)
qed

context G_generic1
begin

lemma sats_ground_repl_fm_imp_sats_ZF_replacement_fm:
  assumes
    "\<phi>\<in>formula" "M, [] \<Turnstile> \<cdot>Replacement(ground_repl_fm(\<phi>))\<cdot>"
  shows
    "M[G], [] \<Turnstile> \<cdot>Replacement(\<phi>)\<cdot>"
  using assms sats_ZF_replacement_fm_iff
  by (auto simp:replacement_assm_def ground_replacement_assm_def
      intro:strong_replacement_in_MG[simplified])

lemma satT_ground_repl_fm_imp_satT_ZF_replacement_fm:
  assumes
    "\<Phi> \<subseteq> formula" "M \<Turnstile> { \<cdot>Replacement(ground_repl_fm(\<phi>))\<cdot> . \<phi> \<in> \<Phi>}"
  shows
    "M[G] \<Turnstile> { \<cdot>Replacement(\<phi>)\<cdot> . \<phi> \<in> \<Phi>}"
  using assms sats_ground_repl_fm_imp_sats_ZF_replacement_fm
  by auto

end \<comment> \<open>\<^locale>\<open>G_generic1\<close>\<close>

theorem extensions_of_ctms:
  assumes
    "M \<approx> \<omega>" "Transset(M)" "M \<Turnstile> \<cdot>Z\<cdot> \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> instances1_fms \<union> instances2_fms}"
    "\<Phi> \<subseteq> formula" "M \<Turnstile> { \<cdot>Replacement(ground_repl_fm(\<phi>))\<cdot> . \<phi> \<in> \<Phi>}"
  shows
    "\<exists>N.
      M \<subseteq> N \<and> N \<approx> \<omega> \<and> Transset(N) \<and> M\<noteq>N \<and>
      (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> (\<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N)) \<and>
      ((M, []\<Turnstile> \<cdot>AC\<cdot>) \<longrightarrow> N, [] \<Turnstile> \<cdot>AC\<cdot>) \<and> N \<Turnstile> \<cdot>Z\<cdot> \<union> { \<cdot>Replacement(\<phi>)\<cdot> . \<phi> \<in> \<Phi>}"
proof -
  from \<open>M \<Turnstile> \<cdot>Z\<cdot> \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> instances1_fms \<union> instances2_fms}\<close>
  interpret M_ZF2 M
    using M_satT_instances12_imp_M_ZF2
    by simp
  from \<open>Transset(M)\<close>
  interpret M_ZF1_trans M
    using M_satT_imp_M_ZF2
    by unfold_locales
  from \<open>M \<approx> \<omega>\<close>
  obtain enum where "enum \<in> bij(\<omega>,M)"
    using eqpoll_sym unfolding eqpoll_def by blast
  then
  interpret M_ctm2 M enum by unfold_locales simp_all
  interpret forcing_data1 "2\<^bsup><\<omega>\<^esup>" seqle 0 M enum
    using nat_into_M seqspace_closed seqle_in_M
    by unfold_locales simp
  obtain G where "M_generic(G)" "M \<noteq> M\<^bsup>s\<^esup>[G]"
    using cohen_extension_is_proper
    by blast
  txt\<open>Recall that \<^term>\<open>M\<^bsup>s\<^esup>[G]\<close> denotes the generic extension \<^term>\<open>M\<^bsup>2\<^bsup><\<omega>\<^esup>\<^esup>[G]\<close>
  of \<^term>\<open>M\<close> using the poset of sequences \<^term>\<open>2\<^bsup><\<omega>\<^esup>\<close>.\<close>
  then
  interpret G_generic1 "2\<^bsup><\<omega>\<^esup>" seqle 0 _ enum G by unfold_locales
  interpret MG: M_Z_basic "M\<^bsup>s\<^esup>[G]"
    using generic pairing_in_MG
      Union_MG  extensionality_in_MG power_in_MG
      foundation_in_MG replacement_assm_MG
      separation_in_MG infinity_in_MG replacement_ax1
    by unfold_locales simp
  have "M, []\<Turnstile> \<cdot>AC\<cdot> \<Longrightarrow> M\<^bsup>s\<^esup>[G], [] \<Turnstile> \<cdot>AC\<cdot>"
  proof -
    assume "M, [] \<Turnstile> \<cdot>AC\<cdot>"
    then
    have "choice_ax(##M)"
      unfolding ZF_choice_fm_def using ZF_choice_auto by simp
    then
    have "choice_ax(##M\<^bsup>s\<^esup>[G])" using choice_in_MG by simp
    then
    show "M\<^bsup>s\<^esup>[G], [] \<Turnstile> \<cdot>AC\<cdot>"
      using ZF_choice_auto sats_ZFC_iff_sats_ZF_AC
      unfolding ZF_choice_fm_def by simp
  qed
  moreover
  note \<open>M \<noteq> M\<^bsup>s\<^esup>[G]\<close> \<open>M \<Turnstile> { \<cdot>Replacement(ground_repl_fm(\<phi>))\<cdot> . \<phi> \<in> \<Phi>}\<close> \<open>\<Phi> \<subseteq> formula\<close>
  moreover
  have "Transset(M\<^bsup>s\<^esup>[G])" using Transset_MG .
  moreover
  have "M \<subseteq> M\<^bsup>s\<^esup>[G]" using M_subset_MG[OF one_in_G] generic by simp
  ultimately
  show ?thesis
    using Ord_MG_iff MG_eqpoll_nat ext.M_satT_Zermelo_fms
      satT_ground_repl_fm_imp_satT_ZF_replacement_fm[of \<Phi>]
    by (rule_tac x="M\<^bsup>s\<^esup>[G]" in exI, auto)
qed

lemma ZF_replacement_instances12_sub_ZF: "{\<cdot>Replacement(p)\<cdot> . p \<in> instances1_fms \<union> instances2_fms} \<subseteq> ZF"
  using instances1_fms_type instances2_fms_type unfolding ZF_def ZF_schemes_def by auto

theorem extensions_of_ctms_ZF:
  assumes
    "M \<approx> \<omega>" "Transset(M)" "M \<Turnstile> ZF"
  shows
    "\<exists>N.
      M \<subseteq> N \<and> N \<approx> \<omega> \<and> Transset(N) \<and> N \<Turnstile> ZF \<and> M\<noteq>N \<and>
      (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> (\<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N)) \<and>
      ((M, []\<Turnstile> \<cdot>AC\<cdot>) \<longrightarrow> N \<Turnstile> ZFC)"
proof -
  from assms
  have "\<exists>N.
      M \<subseteq> N \<and> N \<approx> \<omega> \<and> Transset(N) \<and> M\<noteq>N \<and>
      (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> (\<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N)) \<and>
      ((M, []\<Turnstile> \<cdot>AC\<cdot>) \<longrightarrow> N, [] \<Turnstile> \<cdot>AC\<cdot>) \<and> N \<Turnstile> \<cdot>Z\<cdot> \<union> { \<cdot>Replacement(\<phi>)\<cdot> . \<phi> \<in> formula}"
    using extensions_of_ctms[of M formula] satT_ZF_imp_satT_Z[of M]
      satT_mono[OF _ ground_repl_fm_sub_ZF, of M]
      satT_mono[OF _ ZF_replacement_instances12_sub_ZF, of M]
    by (auto simp: satT_Un_iff)
  then
  obtain N where "N \<Turnstile> \<cdot>Z\<cdot> \<union> { \<cdot>Replacement(\<phi>)\<cdot> . \<phi> \<in> formula}" "M \<subseteq> N" "N \<approx> \<omega>" "Transset(N)"
    "M \<noteq> N" "(\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> \<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N)"
    "(M, []\<Turnstile> \<cdot>AC\<cdot>) \<longrightarrow> N, [] \<Turnstile> \<cdot>AC\<cdot>"
    by blast
  moreover from \<open>N \<Turnstile> \<cdot>Z\<cdot> \<union> { \<cdot>Replacement(\<phi>)\<cdot> . \<phi> \<in> formula}\<close>
  have "N \<Turnstile> ZF"
    using satT_Z_ZF_replacement_imp_satT_ZF by auto
  moreover from this and \<open>(M, []\<Turnstile> \<cdot>AC\<cdot>) \<longrightarrow> N, [] \<Turnstile> \<cdot>AC\<cdot>\<close>
  have "(M, []\<Turnstile> \<cdot>AC\<cdot>) \<longrightarrow> N \<Turnstile> ZFC"
    using sats_ZFC_iff_sats_ZF_AC by simp
  ultimately
  show ?thesis
    by auto
qed

end