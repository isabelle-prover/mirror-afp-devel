section \<open>Fair Streams\<close>

theory Fair_Stream imports "HOL-Library.Stream" begin

definition upt_lists :: \<open>nat list stream\<close> where
  \<open>upt_lists \<equiv> smap (upt 0) (stl nats)\<close>

definition fair_nats :: \<open>nat stream\<close> where
  \<open>fair_nats \<equiv> flat upt_lists\<close>

definition fair :: \<open>'a stream \<Rightarrow> bool\<close> where
  \<open>fair s \<equiv> \<forall>x \<in> sset s. \<forall>m. \<exists>n \<ge> m. s !! n = x\<close>

lemma upt_lists_snth: \<open>x \<le> n \<Longrightarrow> x \<in> set (upt_lists !! n)\<close>
  unfolding upt_lists_def by auto

lemma all_ex_upt_lists: \<open>\<exists>n \<ge> m. x \<in> set (upt_lists !! n)\<close>
  using upt_lists_snth by (meson dual_order.strict_trans1 gt_ex nle_le)

lemma upt_lists_ne: \<open>\<forall>xs \<in> sset upt_lists. xs \<noteq> []\<close>
  unfolding upt_lists_def by (simp add: sset_range)

lemma sset_flat_stl: \<open>sset (flat (stl s)) \<subseteq> sset (flat s)\<close>
proof (cases s)
  case (SCons x xs)
  then show ?thesis
    by (cases x) (simp add: stl_sset subsetI, auto)
qed

lemma flat_snth_nth:
  assumes \<open>x = s !! n ! m\<close> \<open>m < length (s !! n)\<close> \<open>\<forall>xs \<in> sset s. xs \<noteq> []\<close>
  shows \<open>\<exists>n' \<ge> n. x = flat s !! n'\<close>
  using assms
proof (induct n arbitrary: s)
  case 0
  then show ?case
    using flat_snth by fastforce
next
  case (Suc n)
  have \<open>?case = (\<exists>n' \<ge> n. x = flat s !! Suc n')\<close>
    by (metis Suc_le_D Suc_le_mono)
  also have \<open>\<dots> = (\<exists>n' \<ge> n. x = stl (flat s) !! n')\<close>
    by simp
  finally have \<open>?case = (\<exists>n' \<ge> n. x = (tl (shd s) @- flat (stl s)) !! n')\<close>
    using Suc.prems flat_unfold by (simp add: shd_sset)
  then have ?case if \<open>\<exists>n' \<ge> n. x = flat (stl s) !! n'\<close>
    using that by (metis (no_types, opaque_lifting) add.commute add_diff_cancel_left'
        dual_order.trans le_add2 shift_snth_ge)
  moreover {
    have \<open>x = stl s !! n ! m\<close> \<open> m < length (stl s !! n)\<close>
      using Suc.prems by simp_all
    moreover have \<open>\<forall>xs \<in> sset (stl s). xs \<noteq> []\<close>
      using Suc.prems by (cases s) simp_all
    ultimately have \<open>\<exists>n' \<ge> n. x = flat (stl s) !! n'\<close>
      using Suc.hyps by blast }
  ultimately show ?case .
qed

lemma all_ex_fair_nats: \<open>\<exists>n \<ge> m. fair_nats !! n = x\<close>
proof -
  have \<open>\<exists>n \<ge> m. x \<in> set (upt_lists !! n)\<close>
    using all_ex_upt_lists .
  then have \<open>\<exists>n \<ge> m. \<exists>k < length (upt_lists !! n). upt_lists !! n ! k = x\<close>
    by (simp add: in_set_conv_nth)
  then obtain n k where \<open>m \<le> n\<close> \<open>k < length (upt_lists !! n)\<close> \<open>upt_lists !! n ! k = x\<close>
    by blast
  then obtain n' where \<open>n \<le> n'\<close> \<open>x = flat upt_lists !! n'\<close>
    using flat_snth_nth upt_lists_ne by metis
  moreover have \<open>m \<le> n'\<close>
    using \<open>m \<le> n\<close> \<open>n \<le> n'\<close> by simp
  ultimately show ?thesis
    unfolding fair_nats_def by blast
qed

lemma fair_surj:
  assumes \<open>surj f\<close>
  shows \<open>fair (smap f fair_nats)\<close>
  using assms unfolding fair_def by (metis UNIV_I all_ex_fair_nats imageE snth_smap)

definition fair_stream :: \<open>(nat \<Rightarrow> 'a) \<Rightarrow> 'a stream\<close> where
  \<open>fair_stream f \<equiv> smap f fair_nats\<close>

theorem fair_stream: \<open>surj f \<Longrightarrow> fair (fair_stream f)\<close>
  unfolding fair_stream_def using fair_surj .

theorem UNIV_stream: \<open>surj f \<Longrightarrow> sset (fair_stream f) = UNIV\<close>
  unfolding fair_stream_def using all_ex_fair_nats by (metis sset_range stream.set_map surjI)

end
