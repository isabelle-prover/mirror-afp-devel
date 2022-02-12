theory Context_RR2
  imports Context_Extensions
    Ground_MCtxt
    Regular_Tree_Relations.RRn_Automata
begin

subsection \<open>Auxiliary lemmas\<close>
(* TODO Move *)
lemma gpair_gctxt:
  assumes "gpair s t = u"
  shows "(map_gctxt (\<lambda> f .(Some f, Some f)) C)\<langle>u\<rangle>\<^sub>G = gpair C\<langle>s\<rangle>\<^sub>G C\<langle>t\<rangle>\<^sub>G" using assms
  by (induct C arbitrary: s t u) (auto simp add: gpair_context1 comp_def map_funs_term_some_gpair intro!: nth_equalityI)

lemma gpair_gctxt':
  assumes "gpair C\<langle>v\<rangle>\<^sub>G C\<langle>w\<rangle>\<^sub>G = u"
  shows "u = (map_gctxt (\<lambda> f .(Some f, Some f)) C)\<langle>gpair v w\<rangle>\<^sub>G"
  using assms by (simp add: gpair_gctxt)

lemma gpair_gmctxt:
  assumes "\<forall> i < length us. gpair (ss ! i) (ts ! i) = us ! i"
    and "num_gholes C = length ss" "length ss = length ts" "length ts = length us"
  shows "fill_gholes (map_gmctxt (\<lambda>f . (Some f, Some f)) C) us = gpair (fill_gholes C ss) (fill_gholes C ts)"
  using assms
proof (induct C arbitrary: ss ts us)
  case GMHole
  then show ?case by (cases ss; cases ts; cases us) auto
next
  case (GMFun f Cs)
  show ?case using GMFun(2-)
    using GMFun(1)[OF nth_mem, of i "partition_gholes us Cs ! i" "partition_gholes ss Cs ! i" "partition_gholes ts Cs ! i" for i]
    using length_partition_gholes_nth[of Cs] partition_by_nth_nth[of "map num_gholes Cs" us]
    using partition_by_nth_nth[of "map num_gholes Cs" ss] partition_by_nth_nth[of "map num_gholes Cs" ts]
    by (auto simp: partition_holes_fill_gholes_conv' gpair_context1 simp del: fill_gholes.simps intro!: nth_equalityI)
      (simp add: length_partition_gholes_nth)
qed
(*Finished Move section*)


lemma gctxtex_onp_gpair_set_conv:
  "{gpair t u |t u. (t, u) \<in> gctxtex_onp P \<R>} =
    {(map_gctxt (\<lambda> f .(Some f, Some f)) C)\<langle>s\<rangle>\<^sub>G | C s. P C \<and> s \<in> {gpair t u |t u. (t, u) \<in> \<R>}}" (is "?Ls = ?Rs")
proof
  show "?Ls \<subseteq> ?Rs" using gpair_gctxt'
    by (auto elim!: gctxtex_onpE) blast
next
  show "?Rs \<subseteq> ?Ls"
    by (auto simp add: gctxtex_onpI gpair_gctxt)
qed

lemma gmctxtex_onp_gpair_set_conv:
  "{gpair t u |t u. (t, u) \<in> gmctxtex_onp P \<R>} =
    {fill_gholes (map_gmctxt (\<lambda> f .(Some f, Some f)) C) ss | C ss. num_gholes C = length ss \<and> P C \<and>
     (\<forall> i < length ss. ss ! i \<in> {gpair t u |t u. (t, u) \<in> \<R>})}" (is "?Ls = ?Rs")
proof
  {fix u assume "u \<in> ?Ls" then obtain s t
      where *: "u = gpair s t" "(s, t) \<in> gmctxtex_onp P \<R>"
      by auto
    from gmctxtex_onpE[OF *(2)] obtain C us vs where
      **: "s = fill_gholes C us" "t = fill_gholes C vs" and
      inv: "num_gholes C = length us" "length us = length vs" "P C"
       "\<forall> i < length vs. (us ! i, vs ! i) \<in> \<R>"
      by blast
    define ws where "ws \<equiv> map2 gpair us vs"
    from inv(1, 2) have "\<forall> i < length ws. gpair (us ! i) (vs ! i) =  ws ! i"
      by(auto simp: ws_def)
    from gpair_gmctxt[OF this inv(1, 2)] inv
    have "u \<in> ?Rs" unfolding * **
      by (auto simp: ws_def intro!: exI[of _ ws] exI[of _ C])}
  then show "?Ls \<subseteq> ?Rs" by blast
next
  {fix u assume "u \<in> ?Rs" then obtain C ss where
    *: "u = fill_gholes (map_gmctxt (\<lambda>f. (Some f, Some f)) C) ss" and
    inv: "P C" "num_gholes C = length ss" "\<forall> i < length ss. \<exists> t u. ss ! i = gpair t u \<and> (t, u) \<in> \<R>"
      by auto
    define us where "us \<equiv> map gfst ss" define vs where "vs \<equiv> map gsnd ss"
    then have len: "length ss = length us" "length us = length vs" and
      rec: "\<forall> i < length ss. gpair (us ! i) (vs ! i) = ss ! i"
        "\<forall> i < length vs. (us ! i, vs ! i) \<in> \<R>"
      by (auto simp: us_def vs_def) (metis gfst_gpair gsnd_gpair inv(3))+
    from len have l: "length vs = length ss" by auto
    have "u \<in> ?Ls" unfolding * using inv(2) len
      using gmctxtex_onpI[of P C us vs \<R>, OF inv(1) _ len(2) rec(2)]
      using gpair_gmctxt[OF rec(1) _ len(2) l, of C]
      by simp}
  then show "?Rs \<subseteq> ?Ls" by blast
qed


(* Results about lifting signature to RR2
  TODO rework, as this is not the RR2 signature more like
  the context signature, so closing a RR2 term under this signature
  leads a RR2 term
*)

abbreviation "lift_sig_RR2 \<equiv> \<lambda> (f, n). ((Some f, Some f), n)"
abbreviation "lift_fun \<equiv> (\<lambda> f. (Some f, Some f))"
abbreviation "unlift_fst \<equiv> (\<lambda> f. the (fst f))"
abbreviation "unlift_snd \<equiv> (\<lambda> f. the (snd f))"

lemma RR2_gterm_unlift_lift_id [simp]:
  "funas_gterm t \<subseteq> lift_sig_RR2 ` \<F> \<Longrightarrow> map_gterm (lift_fun \<circ> unlift_fst) t = t"
  by (induct t) (auto simp add: SUP_le_iff map_idI)

lemma RR2_gterm_unlift_funas [simp]:
  "funas_gterm t \<subseteq> lift_sig_RR2 ` \<F> \<Longrightarrow> funas_gterm (map_gterm unlift_fst t) \<subseteq> \<F>"
  by (induct t) (auto simp add: SUP_le_iff map_idI)

lemma gterm_funas_lift_RR2_funas [simp]:
  "funas_gterm t \<subseteq> \<F> \<Longrightarrow> funas_gterm (map_gterm lift_fun t) \<subseteq> lift_sig_RR2 ` \<F>"
  by (induct t) (auto simp add: SUP_le_iff map_idI)

lemma RR2_gctxt_unlift_lift_id [simp, intro]:
  "funas_gctxt C \<subseteq> lift_sig_RR2 ` \<F> \<Longrightarrow> (map_gctxt (lift_fun \<circ> unlift_fst) C) = C"
  by (induct C) (auto simp add: all_set_conv_all_nth SUP_le_iff map_idI intro!: nth_equalityI)

lemma RR2_gctxt_unlift_funas [simp, intro]:
  "funas_gctxt C \<subseteq> lift_sig_RR2 ` \<F> \<Longrightarrow> funas_gctxt (map_gctxt unlift_fst C) \<subseteq> \<F>"
  by (induct C) (auto simp add: all_set_conv_all_nth SUP_le_iff map_idI intro!: nth_equalityI)

lemma gctxt_funas_lift_RR2_funas [simp, intro]:
  "funas_gctxt C \<subseteq> \<F> \<Longrightarrow> funas_gctxt (map_gctxt lift_fun C) \<subseteq> lift_sig_RR2 ` \<F>"
  by (induct C) (auto simp add: all_set_conv_all_nth SUP_le_iff map_idI intro!: nth_equalityI)

lemma RR2_gmctxt_unlift_lift_id [simp, intro]:
  "funas_gmctxt C \<subseteq> lift_sig_RR2 ` \<F> \<Longrightarrow> (map_gmctxt (lift_fun \<circ> unlift_fst) C) = C"
  by (induct C) (auto simp add: all_set_conv_all_nth SUP_le_iff map_idI intro!: nth_equalityI)

lemma RR2_gmctxt_unlift_funas [simp, intro]:
  "funas_gmctxt C \<subseteq> lift_sig_RR2 ` \<F> \<Longrightarrow> funas_gmctxt (map_gmctxt unlift_fst C) \<subseteq> \<F>"
  by (induct C) (auto simp add: all_set_conv_all_nth SUP_le_iff map_idI intro!: nth_equalityI)

lemma gmctxt_funas_lift_RR2_funas [simp, intro]:
  "funas_gmctxt C \<subseteq> \<F> \<Longrightarrow> funas_gmctxt (map_gmctxt lift_fun C) \<subseteq> lift_sig_RR2 ` \<F>"
  by (induct C) (auto simp add: all_set_conv_all_nth SUP_le_iff map_idI intro!: nth_equalityI)

lemma RR2_gctxt_cl_to_gctxt:
  assumes "\<And> C. P C \<Longrightarrow> funas_gctxt C \<subseteq> lift_sig_RR2 ` \<F>"
    and "\<And> C. P C \<Longrightarrow> R (map_gctxt unlift_fst C)"
    and "\<And> C. R C \<Longrightarrow> P (map_gctxt lift_fun C)"
  shows "{C\<langle>s\<rangle>\<^sub>G |C s. P C \<and> Q s} = {(map_gctxt lift_fun C)\<langle>s\<rangle>\<^sub>G |C s. R C \<and> Q s}" (is "?Ls = ?Rs")
proof
  {fix u assume "u \<in> ?Ls" then obtain C s where
    *:"u = C\<langle>s\<rangle>\<^sub>G" and inv: "P C" "Q s" by blast
    then have "funas_gctxt C \<subseteq> lift_sig_RR2 ` \<F>" using assms by auto
    from RR2_gctxt_unlift_lift_id[OF this] have "u \<in> ?Rs" using inv assms unfolding * 
      by (auto intro!: exI[of _ "map_gctxt unlift_fst C"] exI[of _ s])}
  then show "?Ls \<subseteq> ?Rs" by blast
next
  {fix u assume "u \<in> ?Rs" then obtain C s where
    *:"u = (map_gctxt lift_fun C)\<langle>s\<rangle>\<^sub>G" and inv: "R C" "Q s"
      by blast
    have "u \<in> ?Ls" unfolding * using inv assms
      by (auto intro!: exI[of _ "map_gctxt lift_fun C"])}
  then show "?Rs \<subseteq> ?Ls" by blast
qed

lemma RR2_gmctxt_cl_to_gmctxt:
  assumes "\<And> C. P C \<Longrightarrow> funas_gmctxt C \<subseteq> lift_sig_RR2 ` \<F>"
    and "\<And> C. P C \<Longrightarrow> R (map_gmctxt (\<lambda> f. the (fst f)) C)"
    and "\<And> C. R C \<Longrightarrow> P (map_gmctxt (\<lambda> f. (Some f, Some f)) C)"
  shows "{fill_gholes C ss |C ss. num_gholes C = length ss \<and> P C \<and> (\<forall> i < length ss. Q (ss ! i))} =
    {fill_gholes (map_gmctxt (\<lambda>f. (Some f, Some f)) C) ss |C ss. num_gholes C = length ss \<and>
     R C \<and> (\<forall> i < length ss. Q (ss ! i))}" (is "?Ls = ?Rs")
proof
  {fix u assume "u \<in> ?Ls" then obtain C ss where
    *:"u = fill_gholes C ss" and inv: "num_gholes C = length ss" "P C" "\<forall> i < length ss. Q (ss ! i)"
      by blast
    then have "funas_gmctxt C \<subseteq> lift_sig_RR2 ` \<F>" using assms by auto
    from RR2_gmctxt_unlift_lift_id[OF this] have "u \<in> ?Rs" using inv assms unfolding * 
      by (auto intro!: exI[of _ "map_gmctxt unlift_fst C"] exI[of _ ss])}
  then show "?Ls \<subseteq> ?Rs" by blast
next
  {fix u assume "u \<in> ?Rs" then obtain C ss where
    *:"u = fill_gholes (map_gmctxt lift_fun C) ss" and inv: "num_gholes C = length ss" "R C"
      "\<forall> i < length ss. Q (ss ! i)"
      by blast
    have "u \<in> ?Ls" unfolding * using inv assms
      by (auto intro!: exI[of _ "map_gmctxt lift_fun C"])}
  then show "?Rs \<subseteq> ?Ls" by blast
qed

lemma RR2_id_terms_gpair_set [simp]:
 "\<T>\<^sub>G (lift_sig_RR2 ` \<F>) = {gpair t u |t u. (t, u) \<in> Restr Id (\<T>\<^sub>G \<F>)}"
 apply (auto simp: map_funs_term_some_gpair \<T>\<^sub>G_equivalent_def)
 apply (smt RR2_gterm_unlift_funas RR2_gterm_unlift_lift_id gterm.map_comp)
 using funas_gterm_map_gterm by blast

end