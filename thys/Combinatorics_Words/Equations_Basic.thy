(*  Title:      CoW_Equations/Equations_Basic.thy
    Author:     Štěpán Holub, Charles University
    Author:     Martin Raška, Charles University
    Author:     Štěpán Starosta, CTU in Prague

Part of Combinatorics on Words Formalized. See https://gitlab.com/formalcow/combinatorics-on-words-formalized/

*)

theory Equations_Basic
  imports
    Periodicity_Lemma
    Lyndon_Schutzenberger
    Submonoids
    Binary_Code_Morphisms
begin

chapter "Equations on words - basics"

text
\<open>Contains various nontrivial auxiliary or rudimentary facts related to equations. Often moderately advanced or even fairly advanced.
 May change significantly in the future.\<close>


section Miscellanea

subsection \<open>Mismatch additions\<close>

lemma mismatch_pref_comm_len: assumes "w1 \<in> \<langle>{u,v}\<rangle>" and "w2 \<in> \<langle>{u,v}\<rangle>" and "p \<le>p w1"
  "u \<cdot> p \<le>p v \<cdot> w2" and "\<^bold>|v\<^bold>| \<le> \<^bold>|p\<^bold>|"
shows "u \<cdot> v = v \<cdot> u"
proof (rule ccontr)
  assume "u \<cdot> v \<noteq> v \<cdot> u"
  then interpret binary_code u v
    by unfold_locales
  show False
    using bin_code_prefs[OF \<open>w1 \<in> \<langle>{u,v}\<rangle>\<close> \<open>p \<le>p w1\<close> \<open>w2 \<in> \<langle>{u,v}\<rangle>\<close> \<open>\<^bold>|v\<^bold>| \<le> \<^bold>|p\<^bold>|\<close>]
      \<open>u \<cdot> p \<le>p v \<cdot> w2\<close>
    by blast
qed

lemma mismatch_pref_comm: assumes "w1 \<in> \<langle>{u,v}\<rangle>" and "w2 \<in> \<langle>{u,v}\<rangle>" and
  "u \<cdot> w1 \<cdot> v \<le>p v \<cdot> w2 \<cdot> u"
shows "u \<cdot> v = v \<cdot> u"
  using assms  by mismatch

lemma mismatch_eq_comm: assumes "w1 \<in> \<langle>{u,v}\<rangle>" and "w2 \<in> \<langle>{u,v}\<rangle>" and
  "u \<cdot> w1 = v \<cdot> w2"
shows "u \<cdot> v = v \<cdot> u"
  using assms  by mismatch

lemmas mismatch_suf_comm = mismatch_pref_comm[reversed] and
       mismatch_suf_comm_len = mismatch_pref_comm_len[reversed, unfolded rassoc]

subsection  \<open>Conjugate words with conjugate periods\<close>

lemma conj_pers_conj_comm_aux:
  assumes "(u \<cdot> v)\<^sup>@k \<cdot> u = r \<cdot> s" and "(v \<cdot> u)\<^sup>@l \<cdot> v = (s \<cdot> r)\<^sup>@m" and "0 < k" "0 < l" and "2 \<le> m"
  shows "u \<cdot> v =  v \<cdot> u"
proof (rule nemp_comm)
  assume "u \<noteq> \<epsilon>" and "v \<noteq> \<epsilon>" hence "u \<cdot> v \<noteq> \<epsilon>" and "v \<cdot> u \<noteq> \<epsilon>" by blast+
  have "l \<noteq> 1" \<comment> \<open>impossible by a length argument\<close>
  proof (rule notI)
    assume "l = 1"
    hence "v \<cdot> u \<cdot> v = (s \<cdot> r)\<^sup>@m"
      using assms(2) by simp
    have "\<^bold>|v \<cdot> u\<^bold>| + \<^bold>|u\<^bold>| \<le> \<^bold>|r \<cdot> s\<^bold>|"
      unfolding lenmorph add.commute[of "\<^bold>|u\<^bold>|"]
      lenarg[OF assms(1), unfolded lenmorph pow_len, symmetric]
      using \<open>0 < k\<close> by simp
    hence "\<^bold>|v \<cdot> u \<cdot> v \<cdot> u\<^bold>| \<le> 2*\<^bold>|r \<cdot> s\<^bold>|"
      unfolding lenmorph pow_len by simp
    hence "\<^bold>|v \<cdot> u \<cdot> v\<^bold>| < 2*\<^bold>|r \<cdot> s\<^bold>|"
      unfolding lenmorph pow_len using nemp_len[OF \<open>u \<noteq> \<epsilon>\<close>] by linarith
    from this[unfolded \<open>v \<cdot> u \<cdot> v = (s \<cdot> r)\<^sup>@m\<close>]
    show False
      using mult_le_mono1[OF \<open>2 \<le> m\<close>, of "\<^bold>|r\<^bold>| + \<^bold>|s\<^bold>|"]
      unfolding lenmorph pow_len add.commute[of "\<^bold>|s\<^bold>|"] by force
  qed
    \<comment> \<open>we can therefore use the periodicity lemma\<close>
  hence "2 \<le> l"
    using \<open>0 < l\<close> by force
  let ?w = "(v \<cdot> u)\<^sup>@l \<cdot> v"
  have per1: "?w \<le>p (v \<cdot> u) \<cdot> ?w"
    unfolding lassoc pow_comm[symmetric] by force
  have per2: "?w \<le>p (s \<cdot> r) \<cdot> ?w"
    unfolding  assms(2) using pref_pow_ext' by blast
  have len: "\<^bold>|v \<cdot> u\<^bold>| + \<^bold>|s \<cdot> r\<^bold>|  \<le> \<^bold>|?w\<^bold>|"
  proof-
    have  len1: "2*\<^bold>|s \<cdot> r\<^bold>| \<le> \<^bold>|?w\<^bold>|"
      using mult_le_mono1[OF \<open>2 \<le> m\<close>, of "\<^bold>|s\<^bold>| + \<^bold>|r\<^bold>|"]
      unfolding \<open>(v \<cdot> u)\<^sup>@l \<cdot> v = (s \<cdot> r)\<^sup>@m\<close> lenmorph pow_len.
    moreover have len2: "2*\<^bold>|v \<cdot> u\<^bold>|  \<le> \<^bold>|?w\<^bold>|"
      using mult_le_mono1[OF \<open>2 \<le> l\<close>, of "\<^bold>|v\<^bold>| + \<^bold>|u\<^bold>|"]
      unfolding lenmorph pow_len by linarith
    ultimately show ?thesis
      using len1 len2 by linarith
  qed
  from two_pers[OF per1 per2 len]
  have "(v \<cdot> u) \<cdot> (s \<cdot> r) = (s \<cdot> r) \<cdot> (v \<cdot> u)".
  hence "(v \<cdot> u)\<^sup>@l \<cdot> (s \<cdot> r)\<^sup>@m = (s \<cdot> r)\<^sup>@m \<cdot> (v \<cdot> u)\<^sup>@l"
    using comm_pows_comm by blast
  from comm_drop_exp'[OF this[folded assms(2), unfolded rassoc cancel] \<open>0 < l\<close>]
  show "u \<cdot> v = v \<cdot> u"
    unfolding rassoc cancel by blast
qed

lemma conj_pers_conj_comm: assumes "\<rho> (v \<cdot> (u \<cdot> v)\<^sup>@k) \<sim> \<rho> ((u \<cdot> v)\<^sup>@m \<cdot> u)" and "0 < k" and "0 < m"
  shows "u \<cdot> v = v \<cdot> u"
proof (rule nemp_comm)
  let ?v = "v \<cdot> (u \<cdot> v)\<^sup>@k" and ?u = "(u \<cdot> v)\<^sup>@m \<cdot> u"
  assume "u \<noteq> \<epsilon>" and "v \<noteq> \<epsilon>"
  hence "u \<cdot> v \<noteq> \<epsilon>" and "?v \<noteq> \<epsilon>" and "?u \<noteq> \<epsilon>" by simp_all
  obtain r s where "r \<cdot> s = \<rho> ?v" and "s \<cdot> r = \<rho> ?u"
    using conjugE[OF assms(1)].
  then obtain k1 k2 where "?v = (r \<cdot> s)\<^sup>@k1" and "?u = (s \<cdot> r)\<^sup>@k2" and "0 < k1" and "0 < k2"
    using primroot_expE[of ?u] primroot_expE[of ?v] unfolding shift_pow by metis
  hence eq: "(s \<cdot> r)\<^sup>@k2 \<cdot> (r \<cdot> s)\<^sup>@k1 = (u \<cdot> v)\<^sup>@(m + 1 + k)"
    unfolding pow_add pow_list_one rassoc by simp
  have ineq: "2 \<le> m + 1 + k"
    using \<open>0 < k\<close> by simp
  consider (two_two) "2 \<le> k1 \<and> 2 \<le> k2"|
    (one_one) "k1 = 1 \<and> k2 = 1" |
    (two_one) "2 \<le> k1 \<and> k2 = 1" |
    (one_two) "k1 = 1 \<and> 2 \<le> k2"
    using  \<open>0 < k1\<close> \<open>0 < k2\<close> by linarith
  then show "u \<cdot> v = v \<cdot> u"
  proof (cases)
    case (two_two)
    with Lyndon_Schutzenberger(1)[OF eq _ _ ineq]
    have "(s \<cdot> r) \<cdot> (r \<cdot> s) = (r \<cdot> s) \<cdot> (s \<cdot> r)"
      using eqd_eq[of "s \<cdot> r" "r \<cdot> s" "r \<cdot> s" "s \<cdot> r"] by fastforce

    from comm_pows_comm[OF this, of k2 k1, folded \<open>?v = (r \<cdot> s)\<^sup>@k1\<close> \<open>?u = (s \<cdot> r)\<^sup>@k2\<close>]
    show "u \<cdot> v =  v \<cdot> u"
      by mismatch
  next
    case (one_one)
    hence "(s \<cdot> r) \<^sup>@ k2 \<cdot> (r \<cdot> s) \<^sup>@ k1 = (s \<cdot> r) \<cdot> (r \<cdot> s)"
       by simp
    from eq[unfolded conjunct1[OF one_one] conjunct2[OF one_one] pow_list_1]
         pow_nemp_imprim[OF ineq, folded eq[unfolded this]]
         Lyndon_Schutzenberger_conjug[of "s \<cdot> r" "r \<cdot> s", OF conjugI']
    have "(s \<cdot> r) \<cdot> (r \<cdot> s) = (r \<cdot> s) \<cdot> (s \<cdot> r)" by metis

    from comm_pows_comm[OF this, of k2 k1, folded \<open>?v = (r \<cdot> s)\<^sup>@k1\<close> \<open>?u = (s \<cdot> r)\<^sup>@k2\<close>, folded shift_pow]
    show "u \<cdot> v =  v \<cdot> u"
      by mismatch
  next
    case (two_one)
    hence "?u = s \<cdot> r"
      using \<open>?u = (s \<cdot> r)\<^sup>@k2\<close>
      by simp
               from \<open>?v = (r \<cdot> s)\<^sup>@k1\<close>[folded shift_pow, unfolded this]
    have "(v \<cdot> u) \<^sup>@ k \<cdot> v = (r \<cdot> s)\<^sup>@k1".
    from conj_pers_conj_comm_aux[OF \<open>?u = s \<cdot> r\<close> this \<open>0 < m\<close> \<open>0 < k\<close> ]
    show "u \<cdot> v = v \<cdot> u"
      using two_one by auto
  next
    case (one_two)
    hence "?v = r \<cdot> s"
      using \<open>?v = (r \<cdot> s)\<^sup>@k1\<close> by simp
               from \<open>?u = (s \<cdot> r)\<^sup>@k2\<close>[unfolded this]
    have "(u \<cdot> v) \<^sup>@ m \<cdot> u = (s \<cdot> r) \<^sup>@ k2".
    from conj_pers_conj_comm_aux[OF \<open>?v = r \<cdot> s\<close>[folded shift_pow] this \<open>0 < k\<close> \<open>0 < m\<close>]
    show "u \<cdot> v = v \<cdot> u"
      using one_two by argo
  qed
qed

hide_fact conj_pers_conj_comm_aux

subsection \<open>Covering uvvu\<close>

lemma uv_fac_uvv: assumes "p \<cdot> u \<cdot> v \<le>p u \<cdot> v \<cdot> v" and "p \<noteq> \<epsilon>" and "p \<le>s w" and "w \<in> \<langle>{u,v}\<rangle>"
  shows "u \<cdot> v = v \<cdot> u"
proof (rule nemp_comm)
  assume "u \<noteq> \<epsilon>" and "v \<noteq> \<epsilon>"
  obtain s where "u \<cdot> v \<cdot> v = p \<cdot> u \<cdot> v \<cdot> s"
    using \<open>p \<cdot> u \<cdot> v \<le>p u \<cdot> v \<cdot> v\<close> by (auto simp add: prefix_def)
  obtain p' where "u \<cdot> p' = p \<cdot> u" and "p' \<cdot> v \<cdot> s = v \<cdot> v"
    using eqdE[of  u "v \<cdot> v" "p \<cdot> u" "v \<cdot> s", unfolded rassoc, OF \<open>u \<cdot> v \<cdot> v = p \<cdot> u \<cdot> v \<cdot> s\<close> suf_len'].
  hence "p' \<noteq> \<epsilon>"
    using \<open>p \<noteq> \<epsilon>\<close> by force
  have "p' \<cdot> v \<cdot> s = v \<cdot> v"
    using \<open>u \<cdot> v \<cdot> v = p \<cdot> u \<cdot> v \<cdot> s\<close> \<open>u \<cdot> p' = p \<cdot> u\<close> cancel rassoc by metis
  from mid_sq[OF this]
  have "v \<cdot> p' = p' \<cdot> v" by simp
  from this comm_primroots[OF \<open>v \<noteq> \<epsilon>\<close> \<open>p' \<noteq> \<epsilon>\<close>]
  have "\<rho> v = \<rho> p'"
    by simp
  obtain m where "p' = \<rho> v\<^sup>@m" "0 < m"
    using primroot_expE unfolding \<open>\<rho> v = \<rho> p'\<close> by metis
  have "(u \<cdot> \<rho> v\<^sup>@(m-1)) \<cdot> \<rho> v \<le>s (\<rho> v \<cdot> w) \<cdot> u"
    using \<open>p \<le>s w\<close>
    unfolding rassoc pow_pos2[OF \<open>0 < m\<close>, symmetric] \<open>p' = \<rho> v\<^sup>@m\<close>[symmetric] \<open>u \<cdot> p' = p \<cdot> u\<close> suffix_def by force
  thus "u \<cdot> v = v \<cdot> u"
    using \<open>w \<in> \<langle>{u, v}\<rangle>\<close> by mismatch
qed

lemmas uv_fac_uvv_suf = uv_fac_uvv[reversed, unfolded rassoc]



lemma "u \<le>p v \<Longrightarrow> u' \<le>p v' \<Longrightarrow> u \<and>\<^sub>p u' \<noteq> u \<Longrightarrow> u \<and>\<^sub>p u' \<noteq> u' \<Longrightarrow> u \<and>\<^sub>p u' = v \<and>\<^sub>p v'"
  using lcp.absorb2 lcp.orderE lcp_rulers pref_compE by metis

lemma comm_puv_pvs_eq_uq: assumes "p \<cdot> u \<cdot> v = u \<cdot> v \<cdot> p" and "p \<cdot> v \<cdot> s = u \<cdot> q" and
  "p \<le>p u" "q \<le>p w" and "s \<le>p  w'" and
  "w \<in> \<langle>{u,v}\<rangle>" and "w' \<in> \<langle>{u,v}\<rangle>" and "\<^bold>|u\<^bold>| \<le> \<^bold>|s\<^bold>|"
shows "u \<cdot> v = v \<cdot> u"
proof (rule ccontr)
  assume "u \<cdot> v \<noteq> v \<cdot> u"
  then interpret binary_code u v
    by unfold_locales
  write bin_code_lcp ("\<alpha>") and
    bin_code_mismatch_fst ("c\<^sub>0") and
    bin_code_mismatch_snd ("c\<^sub>1")
  have "\<^bold>|\<alpha>\<^bold>| < \<^bold>|v \<cdot> s\<^bold>|"
    using \<open>\<^bold>|u\<^bold>| \<le> \<^bold>|s\<^bold>|\<close> bin_lcp_short by force
  show False
  proof (cases)
    assume "p = \<epsilon>"
    hence "v \<cdot> s = u \<cdot> q"
      using \<open>p \<cdot> v \<cdot> s = u \<cdot> q\<close> by fastforce
    with \<open>\<^bold>|\<alpha>\<^bold>| < \<^bold>|v \<cdot> s\<^bold>|\<close> \<open>\<^bold>|\<alpha>\<^bold>| < \<^bold>|v \<cdot> s\<^bold>|\<close>[unfolded this]
    have "\<alpha> \<cdot> [c\<^sub>1] \<le>p v \<cdot> s" and "\<alpha> \<cdot> [c\<^sub>0] \<le>p u \<cdot> q"
      using \<open>s \<le>p  w'\<close> \<open>w' \<in> \<langle>{u,v}\<rangle>\<close> \<open>q \<le>p w\<close> \<open>w \<in> \<langle>{u,v}\<rangle>\<close>
        bin_lcp_mismatch_pref_all_snd bin_lcp_mismatch_pref_all_fst \<open>v \<cdot> s = u \<cdot> q\<close>
      by blast+
    thus False
      unfolding \<open>v \<cdot> s = u \<cdot> q\<close> using  bin_mismatch_neq
      by (simp add: same_sing_pref)
  next
    assume "p \<noteq> \<epsilon>"
    show False
    proof-
      \<comment> \<open>Preliminaries\<close>
      have "u \<noteq> \<epsilon>" and "v \<noteq> \<epsilon>" and "u \<cdot> v \<noteq> v \<cdot> u"
        by (simp_all add: bin_fst_nemp bin_snd_nemp non_comm)
      have "w \<cdot> u \<cdot> v \<in> \<langle>{u, v}\<rangle>"
        using  \<open>w \<in> \<langle>{u, v}\<rangle>\<close> by blast
      have "\<^bold>|w \<cdot> u \<cdot> v\<^bold>| \<ge> \<^bold>|\<alpha>\<^bold>|"
        using  bin_lcp_short by auto
          \<comment> \<open>The main idea: compare maximum @{term p}-prefixes\<close>
          \<comment> \<open>the maximum @{term p}-prefix of @{term "p \<cdot> v \<cdot> s"}\<close>
      have p_pref1: "p \<cdot> v \<cdot> s \<and>\<^sub>p p \<cdot> p \<cdot> v \<cdot> s = p \<cdot> \<alpha>"
        using bin_per_root_max_pref_short[of p s w', OF _ \<open>s \<le>p w'\<close> \<open>w' \<in> \<langle>{u, v}\<rangle>\<close>]
          \<open>p \<noteq> \<epsilon>\<close> \<open>p \<cdot> u \<cdot> v = u \<cdot> v \<cdot> p\<close> unfolding lcp_ext_left cancel take_all[OF less_imp_le[OF\<open>\<^bold>|\<alpha>\<^bold>| <\<^bold>|v \<cdot> s\<^bold>|\<close>]] by force
          \<comment> \<open>the maximum @{term p}-prefix of @{term "u \<cdot> w \<cdot> u \<cdot> v"} is at least @{term "u \<cdot> \<alpha>"}\<close>
      have p_pref2: "u \<cdot> \<alpha> \<le>p u \<cdot> (w \<cdot> u \<cdot> v) \<and>\<^sub>p p \<cdot> u \<cdot> (w \<cdot> u \<cdot> v)"
        using  bin_root_max_pref_long[OF \<open>p \<cdot> u \<cdot> v = u \<cdot> v \<cdot> p\<close> self_pref \<open>w \<cdot> u \<cdot> v \<in> \<langle>{u, v}\<rangle>\<close> \<open>\<^bold>|\<alpha>\<^bold>| \<le> \<^bold>|w \<cdot> u \<cdot> v\<^bold>| \<close>].
          \<comment> \<open>But those maximum @{term p}-prefixes are equal\<close>
      have "u \<cdot> w \<cdot> u \<cdot> v \<and>\<^sub>p p \<cdot> u \<cdot> w \<cdot> u \<cdot> v = p \<cdot> v \<cdot> s \<and>\<^sub>p p \<cdot> p \<cdot> v \<cdot> s"
      proof(rule lcp_rulers')
        show "\<not> p \<cdot> v \<cdot> s \<bowtie>  p \<cdot> p \<cdot> v \<cdot> s"
        proof (rule notI)
          assume "p \<cdot> v \<cdot> s \<bowtie>  p \<cdot> p \<cdot> v \<cdot> s"
          hence "p \<cdot> v \<cdot> s \<and>\<^sub>p  p \<cdot> p \<cdot> v \<cdot> s = p \<cdot> v \<cdot> s"
            using \<open>p \<noteq> \<epsilon>\<close> lcp.absorb1 pref_compE same_sufix_nil by meson
          from this[unfolded p_pref1 cancel]
          show False
            using bin_lcp_short \<open>\<^bold>|u\<^bold>| \<le> \<^bold>|s\<^bold>|\<close> by force
        qed
        show "p \<cdot> v \<cdot> s \<le>p u \<cdot> (w \<cdot> u \<cdot> v)"  "p \<cdot> p \<cdot> v \<cdot> s \<le>p p \<cdot> u \<cdot> w \<cdot> u \<cdot> v"
          by (simp_all add: assms(2) assms(4))
      qed
      from p_pref2[unfolded rassoc this p_pref1]
      have "p = u"
        using \<open>p \<le>p u\<close>  pref_cancel_right by force
      thus False
        using \<open>p \<cdot> u \<cdot> v = u \<cdot> v \<cdot> p\<close> non_comm by blast
    qed
  qed
qed


lemma assumes "u \<cdot> v \<cdot> v \<cdot> u = p \<cdot> u \<cdot> v \<cdot> u \<cdot> q" and "p \<noteq> \<epsilon>" and "q \<noteq> \<epsilon>"
  shows "u \<cdot> v = v \<cdot> u"
  oops \<comment> \<open>counterexample: v = abaaba, u = a, p = aab, q = baa; aab.a.abaaba.a.baa = a.abaaba.abaaba.a\<close>


lemma uvu_pref_uvv: assumes "p \<cdot> u \<cdot> v \<cdot> v \<cdot> s = u \<cdot> v \<cdot> u \<cdot> q" and
  "p \<le>p u" and "q \<le>p w" and  "s \<le>p  w'" and
  "w \<in> \<langle>{u,v}\<rangle>" and "w' \<in> \<langle>{u,v}\<rangle>" and "\<^bold>|u\<^bold>| \<le> \<^bold>|s\<^bold>|"
shows "u \<cdot> v = v \<cdot> u"
proof(rule nemp_comm)
  have "\<^bold>|p \<cdot> u \<cdot> v\<^bold>| \<le> \<^bold>|u \<cdot> v \<cdot> u\<^bold>|"
    using \<open>p \<le>p u\<close> unfolding lenmorph
    by (simp add: prefix_length_le)

\<comment> \<open>p commutes with @{term "u \<cdot> v"}\<close>
  have "p \<cdot> (u \<cdot> v) = (u \<cdot> v) \<cdot> p"
    by (rule pref_marker[of "u \<cdot> v \<cdot> u"], force)
    (rule eq_le_pref, use assms in force, fact)

  have "p \<cdot> v \<cdot> s = u  \<cdot> q"
  proof-
    have "((u \<cdot> v) \<cdot> p) \<cdot> v \<cdot>  s = (u \<cdot> v) \<cdot> u \<cdot> q"
      unfolding \<open>p \<cdot> u \<cdot> v = (u \<cdot> v) \<cdot> p\<close>[symmetric] unfolding rassoc by fact
    from this[unfolded rassoc cancel]
    show ?thesis.
  qed

  from comm_puv_pvs_eq_uq[OF \<open>p \<cdot> (u \<cdot> v) = (u \<cdot> v) \<cdot> p\<close>[unfolded rassoc] this assms(2-)]
  show "u \<cdot> v = v \<cdot> u".
qed


lemma uvu_pref_uvvu: assumes "p \<cdot> u \<cdot> v \<cdot> v \<cdot> u = u \<cdot> v \<cdot> u \<cdot> q" and
  "p \<le>p u" and "q \<le>p w" and  " w \<in> \<langle>{u,v}\<rangle>"
shows "u \<cdot> v = v \<cdot> u"
  using uvu_pref_uvv[OF \<open>p \<cdot> u \<cdot> v \<cdot> v \<cdot> u = u \<cdot> v \<cdot> u \<cdot> q\<close> \<open>p \<le>p u\<close> \<open>q \<le>p w\<close> _ \<open>w \<in> \<langle>{u,v}\<rangle>\<close>, of u]
  by blast


lemma uvu_pref_uvvu_interp: assumes interp: "p u \<cdot> v \<cdot> v \<cdot> u s \<sim>\<^sub>\<I> ws" and
  "[u, v, u] \<le>p  ws" and "ws \<in> lists {u,v}"
shows "u \<cdot> v = v \<cdot> u"
proof-
  note fac_interpD[OF interp]
  obtain ws' where "[u,v,u] \<cdot> ws' = ws" and "ws' \<in> lists {u,v}"
    using \<open>[u, v, u] \<le>p  ws\<close> \<open>ws \<in> lists {u,v}\<close> by (force simp add: prefix_def)
  have "p \<cdot> u \<cdot> v \<cdot> v \<cdot> u \<cdot> s = u \<cdot> v \<cdot> u \<cdot> concat ws'"
    using \<open>p \<cdot> (u \<cdot> v \<cdot> v \<cdot> u) \<cdot> s = concat ws\<close>[folded \<open>[u,v,u] \<cdot> ws' = ws\<close>, unfolded concat_morph rassoc]
    by simp
  from lenarg[OF this, unfolded lenmorph]
  have "\<^bold>|s\<^bold>| \<le> \<^bold>|concat ws'\<^bold>|"
    by auto
  hence "s \<le>s concat ws'"
    using eqd[reversed, OF \<open>p \<cdot> u \<cdot> v \<cdot> v \<cdot> u \<cdot> s = u \<cdot> v \<cdot> u \<cdot> concat ws'\<close>[unfolded lassoc]]
    by blast
  note local_rule = uvu_pref_uvv[of p u v u "concat ws'\<^sup><\<inverse>s" "concat ws'" u]
  show "u \<cdot> v = v \<cdot> u"
  proof (rule local_rule)
    show "p \<le>p u"
      using \<open>p <p hd ws\<close> pref_hd_eq[OF \<open>[u, v, u] \<le>p  ws\<close> list.distinct(1)[of u "[v,u]", symmetric]]
      by force
    have "p \<cdot> u \<cdot> v \<cdot> v \<cdot> u \<cdot> s = u \<cdot> v \<cdot> u \<cdot> (concat ws'\<^sup><\<inverse>s) \<cdot> s"
      using \<open>p \<cdot> u \<cdot> v \<cdot> v \<cdot> u \<cdot> s = u \<cdot> v \<cdot> u \<cdot> concat ws'\<close> unfolding rq_suf[OF \<open>s \<le>s concat ws'\<close>].
    thus "p \<cdot> u \<cdot> v \<cdot> v \<cdot> u = u \<cdot> v \<cdot> u \<cdot> concat ws'\<^sup><\<inverse>s"
      by simp
    show "concat ws' \<in> \<langle>{u,v}\<rangle>"
      using \<open>ws' \<in> lists {u,v}\<close> by blast
    show "concat ws'\<^sup><\<inverse>s  \<le>p concat ws'"
      using rq_suf[OF \<open>s \<le>s concat ws'\<close>] by force
  qed auto
qed

lemmas uvu_suf_uvvu = uvu_pref_uvvu[reversed, unfolded rassoc] and
  uvu_suf_uvv = uvu_pref_uvv[reversed, unfolded rassoc]

lemma uvu_suf_uvvu_interp: "p u \<cdot> v \<cdot> v \<cdot> u s \<sim>\<^sub>\<I> ws \<Longrightarrow> [u, v, u] \<le>s  ws
  \<Longrightarrow> ws \<in> lists {u,v} \<Longrightarrow> u \<cdot> v = v \<cdot> u"
  by (rule uvu_pref_uvvu_interp[reversed, unfolded rassoc emp_simps, symmetric, of p u v s ws],
      simp, force, simp add: image_iff rev_in_lists rev_map)

subsection \<open>Conjugate words\<close>

lemma conjug_pref_suf_mismatch: assumes "w1 \<in> \<langle>{r\<cdot>s,s\<cdot>r}\<rangle>" and "w2 \<in> \<langle>{r\<cdot>s,s\<cdot>r}\<rangle>" and "r \<cdot> w1 = w2 \<cdot> s"
  shows "r = s \<or> r = \<epsilon> \<or> s = \<epsilon>"
proof (rule ccontr)
  assume "\<not> (r = s \<or> r = \<epsilon> \<or> s = \<epsilon>)"
  hence "r \<noteq> s" and "r \<noteq> \<epsilon>" and "s \<noteq> \<epsilon>" by simp_all
  from assms
  show False
  proof (induct "\<^bold>|w1\<^bold>|" arbitrary: w1 w2 rule: less_induct)
    case less
    have "w1 \<in> \<langle>{r,s}\<rangle>"
      using \<open>w1 \<in> \<langle>{r\<cdot>s,s\<cdot>r}\<rangle>\<close> by force
    obtain w1' where "(w1 = \<epsilon> \<or> w1 = r \<cdot> s \<cdot> w1' \<or> w1 = s \<cdot> r \<cdot> w1') \<and> w1' \<in> \<langle>{r\<cdot>s,s\<cdot>r}\<rangle>"
      using hull.cases[OF \<open>w1 \<in> \<langle>{r\<cdot>s,s\<cdot>r}\<rangle>\<close>]  empty_iff insert_iff rassoc \<open>w1 \<in> \<langle>{r \<cdot> s, s \<cdot> r}\<rangle>\<close> by metis
    hence "w1' \<in> \<langle>{r\<cdot>s,s\<cdot>r}\<rangle>" and cases1: "(w1 = \<epsilon> \<or> w1 = r \<cdot> s \<cdot> w1' \<or> w1 = s \<cdot> r \<cdot> w1')" by blast+
    hence "w1' \<in> \<langle>{r,s}\<rangle>" by force
    obtain w2' where "(w2 = \<epsilon> \<or> w2 = r \<cdot> s \<cdot> w2' \<or> w2 = s \<cdot> r \<cdot> w2') \<and> w2' \<in> \<langle>{r\<cdot>s,s\<cdot>r}\<rangle>"
      using hull.cases[OF \<open>w2 \<in> \<langle>{r\<cdot>s,s\<cdot>r}\<rangle>\<close>]  empty_iff insert_iff rassoc \<open>w1 \<in> \<langle>{r \<cdot> s, s \<cdot> r}\<rangle>\<close> by metis
    hence "w2' \<in> \<langle>{r\<cdot>s,s\<cdot>r}\<rangle>" and cases2: "(w2 = \<epsilon> \<or> w2 = r \<cdot> s \<cdot> w2' \<or> w2 = s \<cdot> r \<cdot> w2')" by blast+
    hence "w2' \<in> \<langle>{r,s}\<rangle>" by force
    consider (empty2) "w2 = \<epsilon>" | (sr2) "w2 = s \<cdot> r \<cdot> w2'" | (rs2) "w2 = r \<cdot> s \<cdot> w2'"using cases2 by blast
    thus False
    proof (cases)
      case empty2
      consider (empty1) "w1 = \<epsilon>" | (sr1) "w1 = s \<cdot> r \<cdot> w1'" | (rs1) "w1 = r \<cdot> s \<cdot> w1'"
        using cases1 by blast
      thus False
      proof (cases)
        case empty1
        show False
          using \<open>r \<cdot> w1 = w2 \<cdot> s\<close>[unfolded empty1 empty2 rassoc] \<open>r \<noteq> s\<close> by simp
      next
        case sr1
        show False
          using \<open>r \<cdot> w1 = w2 \<cdot> s\<close>[unfolded sr1 empty2 rassoc] \<open>r \<noteq> \<epsilon>\<close> fac_triv by auto
      next
        case rs1
        show False
          using \<open>r \<cdot> w1 = w2 \<cdot> s\<close>[unfolded rs1 empty2 rassoc emp_simps] \<open>r \<noteq> \<epsilon>\<close>
            fac_triv[of "r \<cdot> r" s w1', unfolded rassoc] by force
      qed
    next
      case sr2
      have "r \<cdot> s = s \<cdot> r"
        using \<open>w2' \<in> \<langle>{r,s}\<rangle>\<close> \<open>w1 \<in> \<langle>{r,s}\<rangle>\<close> \<open>r \<cdot> w1 = w2 \<cdot> s\<close>[unfolded sr2 rassoc]
        by (mismatch)
      consider (empty1) "w1 = \<epsilon>" | (sr1) "w1 = s \<cdot> r \<cdot> w1'" | (rs1) "w1 = r \<cdot> s \<cdot> w1'" using cases1 by blast
      thus False
      proof (cases)
        case empty1
        then show False
          using \<open>r \<cdot> w1 = w2 \<cdot> s\<close>[unfolded sr2 empty1 rassoc cancel emp_simps, symmetric] \<open>s \<noteq> \<epsilon>\<close> fac_triv by blast
      next
        case rs1
        then have "r \<cdot> s = s \<cdot> r"
          using \<open>w2' \<in> \<langle>{r,s}\<rangle>\<close> \<open>w1' \<in> \<langle>{r,s}\<rangle>\<close> \<open>r \<cdot> w1 = w2 \<cdot> s\<close>[unfolded rs1 sr2 rassoc cancel]
          by mismatch
        hence "r \<cdot> w1' = w2' \<cdot> s"
          using \<open>r \<cdot> w1 = w2 \<cdot> s\<close>[unfolded rs1 sr2] rassoc cancel by metis
        from less.hyps[OF _ \<open>w1' \<in> \<langle>{r \<cdot> s, s \<cdot> r}\<rangle>\<close> \<open>w2' \<in> \<langle>{r \<cdot> s, s \<cdot> r}\<rangle>\<close> this]
        show False
          using lenarg[OF \<open>w1 = r \<cdot> s \<cdot> w1'\<close>, unfolded lenmorph] nemp_len[OF \<open>s \<noteq> \<epsilon>\<close>] by linarith
      next
        case sr1
        then have "r \<cdot> s = s \<cdot> r"
          using \<open>w2' \<in> \<langle>{r,s}\<rangle>\<close> \<open>w1' \<in> \<langle>{r,s}\<rangle>\<close> \<open>r \<cdot> w1 = w2 \<cdot> s\<close>[unfolded sr1 sr2 rassoc cancel]
          by mismatch
        hence "r \<cdot> w1' = w2' \<cdot> s"
          using \<open>r \<cdot> w1 = w2 \<cdot> s\<close>[unfolded sr1 sr2] rassoc cancel by metis
        from less.hyps[OF _ \<open>w1' \<in> \<langle>{r \<cdot> s, s \<cdot> r}\<rangle>\<close> \<open>w2' \<in> \<langle>{r \<cdot> s, s \<cdot> r}\<rangle>\<close> this]
        show False
          using less.hyps[OF _ \<open>w1' \<in> \<langle>{r \<cdot> s, s \<cdot> r}\<rangle>\<close> \<open>w2' \<in> \<langle>{r \<cdot> s, s \<cdot> r}\<rangle>\<close> \<open>r \<cdot> w1' = w2' \<cdot> s\<close>]
            lenarg[OF \<open>w1 = s \<cdot> r \<cdot> w1'\<close>, unfolded lenmorph] nemp_len[OF \<open>s \<noteq> \<epsilon>\<close>] by linarith
      qed
    next
      case rs2
      consider (empty1) "w1 = \<epsilon>" | (sr1) "w1 = s \<cdot> r \<cdot> w1'" | (rs1) "w1 = r \<cdot> s \<cdot> w1'" using cases1 by blast
      thus False
      proof (cases)
        case empty1
        then show False
          using \<open>r \<cdot> w1 = w2 \<cdot> s\<close>[unfolded rs2 empty1 rassoc cancel] \<open>s \<noteq> \<epsilon>\<close> by blast
      next
        case rs1
        then have "r \<cdot> s = s \<cdot> r"
          using \<open>w2' \<in> \<langle>{r,s}\<rangle>\<close> \<open>w1' \<in> \<langle>{r,s}\<rangle>\<close> \<open>r \<cdot> w1 = w2 \<cdot> s\<close>[unfolded rs2 rs1 rassoc cancel]
          by mismatch
        hence "r \<cdot> w1' = w2' \<cdot> s"
          using \<open>r \<cdot> w1 = w2 \<cdot> s\<close>[unfolded rs1 rs2] rassoc cancel by metis
        from less.hyps[OF _ \<open>w1' \<in> \<langle>{r \<cdot> s, s \<cdot> r}\<rangle>\<close> \<open>w2' \<in> \<langle>{r \<cdot> s, s \<cdot> r}\<rangle>\<close> this]
        show False
          using less.hyps[OF _ \<open>w1' \<in> \<langle>{r \<cdot> s, s \<cdot> r}\<rangle>\<close> \<open>w2' \<in> \<langle>{r \<cdot> s, s \<cdot> r}\<rangle>\<close> \<open>r \<cdot> w1' = w2' \<cdot> s\<close>]
            lenarg[OF \<open>w1 = r \<cdot> s \<cdot> w1'\<close>, unfolded lenmorph] nemp_len[OF \<open>s \<noteq> \<epsilon>\<close>] by linarith
      next
        case sr1
        then show False
          using less.hyps[OF _ \<open>w1' \<in> \<langle>{r \<cdot> s, s \<cdot> r}\<rangle>\<close> \<open>w2' \<in> \<langle>{r \<cdot> s, s \<cdot> r}\<rangle>\<close> \<open>r \<cdot> w1 = w2 \<cdot> s\<close>[unfolded rs2 sr1 rassoc cancel]]
            lenarg[OF \<open>w1 = s \<cdot> r \<cdot> w1'\<close>, unfolded lenmorph] nemp_len[OF \<open>s \<noteq> \<epsilon>\<close>] by linarith
      qed
    qed
  qed
qed

lemma conjug_conjug_primroots: assumes "u \<noteq> \<epsilon>" and "r \<noteq> \<epsilon>" and "\<rho> (u \<cdot> v) = r \<cdot> s" and "\<rho> (v \<cdot> u) = s \<cdot> r"
  obtains k m where "(r \<cdot> s)\<^sup>@k \<cdot> r = u" and "(s \<cdot> r)\<^sup>@m \<cdot> s = v"
proof-
  have "v \<cdot> u \<noteq> \<epsilon>" and "u \<cdot> v \<noteq> \<epsilon>"
    using \<open>u \<noteq> \<epsilon>\<close> by blast+
  have "\<rho> (s \<cdot> r) = s \<cdot> r"
    using primroot_idemp[of "v \<cdot> u", unfolded \<open>\<rho> (v \<cdot> u) = s \<cdot> r\<close>].
  obtain n where "(r \<cdot> s)\<^sup>@n = u \<cdot> v" "0 < n"
    using  primroot_expE[unfolded \<open>\<rho> (u \<cdot> v) = r \<cdot> s\<close>]
    using assms(3) by metis
  obtain n' where "(s \<cdot> r)\<^sup>@ n' = v \<cdot> u" "0 < n'"
    using  primroot_expE[of "v \<cdot> u",unfolded \<open>\<rho> (v \<cdot> u) = s \<cdot> r\<close>].
  have "(s \<cdot> u) \<cdot> (s \<cdot> r) = (s \<cdot> r) \<cdot> (s \<cdot> u)"
  proof (rule pref_marker)
    show "(s \<cdot> u) \<cdot> s \<cdot> r \<le>p s \<cdot> (r \<cdot> s)\<^sup>@(n+ n)"
      unfolding rassoc pow_add \<open>(r \<cdot> s)\<^sup>@n = u \<cdot> v\<close>
      unfolding lassoc \<open>(s \<cdot> r)\<^sup>@n' = v \<cdot> u\<close>[symmetric] using \<open>0 < n'\<close> by comparison
    show "s \<cdot> (r \<cdot> s) \<^sup>@ (n + n) \<le>p (s \<cdot> r) \<cdot> s \<cdot> (r \<cdot> s) \<^sup>@ (n + n)"
      by comparison
  qed
  from comm_primroot_exp[OF primroot_nemp[OF \<open>v \<cdot> u \<noteq> \<epsilon>\<close>, unfolded \<open>\<rho> (v \<cdot> u) = s \<cdot> r\<close>] this]
  obtain k where "(s \<cdot> r)\<^sup>@k = s \<cdot> u"
    unfolding \<open>\<rho> (s \<cdot> r) = s \<cdot> r\<close>.
  from suf_nemp[OF \<open>u \<noteq> \<epsilon>\<close>, of s, folded this]
  have  "0 < k"
    by blast
  have u: "(r \<cdot> s)\<^sup>@(k-1) \<cdot> r = u"
    using \<open>(s \<cdot> r)\<^sup>@k = s \<cdot> u\<close> unfolding pow_pos[OF \<open>0 < k\<close>] rassoc cancel shift_pow by fast
  from exp_pref_cancel[OF \<open>(r \<cdot> s)\<^sup>@n = u \<cdot> v\<close>[folded this, unfolded rassoc, symmetric]]
  have "r \<cdot> v = (r \<cdot> s) \<^sup>@ (n + 1 - k)"
    using \<open>0 < k\<close> by fastforce
  from pref_nemp[OF \<open>r \<noteq> \<epsilon>\<close>, of v, unfolded this]
  have "0 < n + 1 - k"
    by blast
  from \<open>r \<cdot> v = (r \<cdot> s) \<^sup>@ (n + 1 - k)\<close>[unfolded pow_pos[OF \<open>0 < n + 1 - k\<close>] rassoc cancel shift_pow[symmetric], symmetric]
  have v: "(s \<cdot> r)\<^sup>@(n + 1 - k - 1) \<cdot> s = v".
  show thesis
    using that[OF u v].
qed

subsection \<open>Predicate ``commutes''\<close>

definition commutes :: "'a list set \<Rightarrow> bool"
  where "commutes A = (\<forall>x y. x \<in> A \<longrightarrow> y \<in> A \<longrightarrow> x\<cdot>y = y\<cdot>x)"

lemma commutesE: "commutes A \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x\<cdot>y = y\<cdot>x"
  using commutes_def by blast


lemma commutes_root: assumes "commutes A"
  obtains r where "\<And>x. x \<in> A \<Longrightarrow> x \<in> \<langle>{r}\<rangle>"
  using assms comm_primroots emp_in sing_gen_primroot
  unfolding commutes_def
  by metis

lemma commutes_primroot: assumes "commutes A"
  obtains r where "\<And>x. x \<in> A \<Longrightarrow> x \<in> \<langle>{r}\<rangle>" and "primitive r"
  by (cases "\<forall> x \<in> A. x = \<epsilon>", fast)
  (use assms[unfolded commutes_def] comm_primroots emp_in sing_gen_primroot
    primroot_prim in metis)

lemma commutesI [intro]: "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x\<cdot>y = y\<cdot>x) \<Longrightarrow> commutes A"
  unfolding commutes_def
  by blast

lemma commutesI': assumes "x \<noteq> \<epsilon>" and "\<And>y. y \<in> A \<Longrightarrow> x\<cdot>y = y\<cdot>x"
  shows "commutes A"
proof-
  have "\<And>x' y'. x' \<in> A \<Longrightarrow> y' \<in> A \<Longrightarrow> x'\<cdot>y' = y'\<cdot>x'"
  proof-
    fix x' y'
    assume "x' \<in> A" "y' \<in> A"
    hence "x'\<cdot>x = x\<cdot>x'" and "y'\<cdot>x = x\<cdot>y'"
      using assms(2) by auto+
    from comm_trans[OF this assms(1)]
    show "x'\<cdot>y' = y'\<cdot>x'".
  qed
  thus ?thesis
    by (simp add: commutesI)
qed

lemma commutesI_root[intro]: "(\<And> x. x \<in> A \<Longrightarrow> x \<in> \<langle>{t}\<rangle>) \<Longrightarrow> commutes A"
  by (meson comm_rootI commutesI)

lemma commutesI_ex_root: "\<exists> t. \<forall> x \<in> A. x \<in> \<langle>{t}\<rangle> \<Longrightarrow> commutes A"
  by fast

lemma commutes_sub: "commutes A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> commutes B"
  by (simp add: commutes_def subsetD)

lemma commutes_insert: "commutes A \<Longrightarrow> x \<in> A \<Longrightarrow> x \<noteq> \<epsilon> \<Longrightarrow>  x\<cdot>y = y\<cdot>x \<Longrightarrow> commutes (insert y A)"
  using commutesE[of A x] commutesI'[of x "insert y A"] insertE
  by blast

lemma commutes_emp [simp]: "commutes {\<epsilon>, w}"
  by (simp add: commutes_def)

lemma commutes_emp'[simp]: "commutes {w, \<epsilon>}"
  by (simp add: commutes_def)

lemma commutes_cancel: assumes "y \<in> A" and "x \<cdot> y \<in> A" and "commutes A"
  shows "commutes (insert x A)"
proof-
  from commutes_root[OF \<open>commutes A\<close>]
  obtain r where "(\<And>x. x \<in> A \<Longrightarrow> x \<in> \<langle>{r}\<rangle>)"
    by metis
  hence "y \<in> \<langle>{r}\<rangle>" and "(x \<cdot> y) \<in> \<langle>{r}\<rangle>"
    using \<open>y \<in> A\<close> \<open>x \<cdot> y \<in> A\<close> by blast+
  hence "x \<in> \<langle>{r}\<rangle>"
    by force
  thus "commutes (insert x A)"
    using \<open>\<And>x. x \<in> A \<Longrightarrow> x \<in> \<langle>{r}\<rangle>\<close> by blast
qed

lemma commutes_cancel': assumes "x \<in> A" and "x \<cdot> y \<in> A" and "commutes A"
  shows "commutes (insert y A)"
proof-
  from commutes_root[OF \<open>commutes A\<close>]
  obtain r where "(\<And>x. x \<in> A \<Longrightarrow> x \<in> \<langle>{r}\<rangle>)"
    by metis
  hence "x \<in> \<langle>{r}\<rangle>" and "x \<cdot> y \<in> \<langle>{r}\<rangle>"
    using \<open>x \<in> A\<close> \<open>x \<cdot> y \<in> A\<close> by blast+
  hence "y \<in> \<langle>{r}\<rangle>"
    using sing_gen_pref_cancel by auto
  thus "commutes (insert y A)"
    using \<open>\<And>x. x \<in> A \<Longrightarrow>  x \<in> \<langle>{r}\<rangle>\<close> by blast
qed




subsection \<open>Strong elementary lemmas\<close>

text\<open>Discovered by smt\<close>

lemma xyx_per_comm: assumes "x\<cdot>y\<cdot>x \<le>p q\<cdot>x\<cdot>y\<cdot>x"
  and "q \<noteq> \<epsilon>" and "q \<le>p y \<cdot> q"
shows "x\<cdot>y = y\<cdot>x"
   proof(cases)
  assume "x \<cdot> y \<le>p q"
  from pref_marker[OF \<open>q \<le>p y \<cdot> q\<close> this]
  show "x \<cdot> y = y \<cdot> x".
next
  have "(x \<cdot> y) \<cdot> x \<le>p q \<cdot> x \<cdot> y \<cdot> x" unfolding rassoc by fact
  assume "\<not> x \<cdot> y \<le>p q"
  hence "q \<le>p  x \<cdot> y"
    using ruler_prefE[OF \<open>(x \<cdot> y) \<cdot> x \<le>p q \<cdot> x \<cdot> y \<cdot> x\<close>] by argo
  from pref_prolong[OF \<open>q \<le>p y \<cdot> q\<close> this, unfolded lassoc]
  have"q \<le>p (y \<cdot> x) \<cdot> y".
  from ruler_pref'[OF this, THEN disjE] \<open>q \<le>p x \<cdot> y\<close>
  have "q \<le>p y \<cdot> x"
    using pref_trans[OF _ \<open>q \<le>p x \<cdot> y\<close>, of "y \<cdot> x", THEN pref_comm_eq] by metis
  from pref_cancel'[OF this, of x]
  have "x \<cdot> q = q \<cdot> x"
    using  pref_marker[OF \<open>x \<cdot> y \<cdot> x \<le>p q \<cdot> x \<cdot> y \<cdot> x\<close>, of x] by blast
  hence "x \<cdot> y \<cdot> x \<le>p x \<cdot> x \<cdot> y \<cdot> x"
    using root_comm_root[OF _ _ \<open>q \<noteq> \<epsilon>\<close>, of "x \<cdot> y \<cdot> x" x] \<open>x \<cdot> y \<cdot> x \<le>p q \<cdot> x \<cdot> y \<cdot> x\<close> by fast
  thus "x\<cdot>y = y\<cdot>x"
    by mismatch
qed

lemma two_elem_root_suf_comm: assumes "u \<le>p v \<cdot> u" and "v \<le>s p \<cdot> u" and "p \<in> \<langle>{u,v}\<rangle>"
  shows "u \<cdot> v = v \<cdot> u"
  using root_suf_comm[OF \<open>u \<le>p v \<cdot> u\<close> two_elem_suf[OF \<open>v \<le>s p \<cdot> u\<close> \<open>p \<in> \<langle>{u,v}\<rangle>\<close>], symmetric].







subsection \<open>Binary words without a letter square\<close>

lemma no_repetition_list:
  assumes "set ws \<subseteq> {a,b}"
    and not_per:  "\<not> ws \<le>p [a,b] \<cdot> ws" "\<not> ws \<le>p [b,a] \<cdot> ws"
    and not_square:  "\<not> [a,a] \<le>f ws" and "\<not> [b,b] \<le>f ws"
  shows False
  using assms
proof (induction ws)
  case (Cons d ws)
  show ?case
  proof (rule "Cons.IH")
    show "set ws \<subseteq> {a,b}"
      using \<open>set (d # ws) \<subseteq> {a, b}\<close> by auto
    have "ws \<noteq> \<epsilon>"
      using "Cons.IH" Cons.prems by force
    from hd_tl[OF this]
    have "hd ws \<noteq> d"
      using Cons.prems(1,4-5) hd_pref[OF \<open>ws \<noteq> \<epsilon>\<close>] by force
    thus "\<not> [a, a] \<le>f ws" and "\<not> [b, b] \<le>f ws"
      using Cons.prems(4-5) unfolding sublist_code(3) by blast+
    show "\<not> ws \<le>p [a, b] \<cdot> ws"
    proof (rule notI)
      assume "ws \<le>p [a, b] \<cdot> ws"
      from pref_hd_eq[OF this \<open>ws \<noteq> \<epsilon>\<close>]
      have "hd ws = a" by simp
      hence  "d = b"
        using \<open>set (d # ws) \<subseteq> {a, b}\<close> \<open>hd ws \<noteq> d\<close> by auto
      show False
        using \<open>ws \<le>p [a, b] \<cdot> ws\<close>  \<open>\<not> d # ws \<le>p [b, a] \<cdot> d # ws\<close>[unfolded \<open>d = b\<close>] by force
    qed
    show "\<not> ws \<le>p [b, a] \<cdot> ws"
    proof (rule notI)
      assume "ws \<le>p [b, a] \<cdot> ws"
      from pref_hd_eq[OF this \<open>ws \<noteq> \<epsilon>\<close>]
      have "hd ws = b" by simp
      hence  "d = a"
        using \<open>set (d # ws) \<subseteq> {a, b}\<close> \<open>hd ws \<noteq> d\<close> by auto
      show False
        using \<open>ws \<le>p [b, a] \<cdot> ws\<close>  \<open>\<not> d # ws \<le>p [a, b] \<cdot> d # ws\<close>[unfolded \<open>d = a\<close>] by force
    qed
  qed
qed simp

lemma no_repetition_list_bin:
  fixes ws :: "binA list"
  assumes not_square:  "\<And> c. \<not> [c,c] \<le>f ws"
  shows "ws \<le>p [hd ws, 1-(hd ws)] \<cdot> ws"
proof (cases "ws = \<epsilon>")
  assume "ws \<noteq> \<epsilon>"
  have set: "set ws \<subseteq> {hd ws, 1-hd ws}"
    using swap_UNIV by auto
  have "\<not> ws \<le>p [1 - hd ws, hd ws] \<cdot> ws"
    using pref_hd_eq[OF _ \<open>ws \<noteq> \<epsilon>\<close>, of "[1 - hd ws, hd ws] \<cdot> ws"] bin_swap_neq'
    unfolding hd_Cons_append by blast
  from no_repetition_list[OF set _ this not_square not_square]
  show "ws \<le>p [hd ws, 1-(hd ws)] \<cdot> ws" by blast
qed simp

lemma per_root_hd_last_root: assumes "ws \<le>p [a,b] \<cdot> ws" and "hd ws \<noteq> last ws"
  shows "ws \<in> \<langle>{[a,b]}\<rangle>"
  using assms
proof (induction "\<^bold>|ws\<^bold>|" arbitrary: ws rule: less_induct)
  case less
  then show ?case
  proof (cases "ws = \<epsilon>")
    assume "ws \<noteq> \<epsilon>"
    with \<open>hd ws \<noteq> last ws\<close>
    have *: "[hd ws, hd (tl ws)] \<cdot> tl (tl ws) = ws"
      using append_Cons last_ConsL[of "tl ws" "hd ws"] list.exhaust_sel[of ws] hd_tl by metis
    have ind: "\<^bold>|tl (tl ws)\<^bold>| < \<^bold>|ws\<^bold>|" using \<open>ws \<noteq> \<epsilon>\<close> by auto
    have "[hd ws, hd (tl ws)] \<cdot> tl (tl ws) \<le>p [a,b] \<cdot> ws "
      unfolding * using  \<open>ws \<le>p [a, b] \<cdot> ws\<close>.
    hence "[a,b] = [hd ws, hd (tl ws)]" by simp
    hence "hd ws = a" by simp
    have "tl (tl ws) \<le>p [a,b] \<cdot> tl (tl ws)"
      unfolding pref_cancel_conv[of "[a,b]" "tl (tl ws)", symmetric] \<open>[a,b] = [hd ws, hd (tl ws)]\<close> *
      using \<open>ws \<le>p [a, b] \<cdot> ws\<close>[unfolded \<open>[a,b] = [hd ws, hd (tl ws)]\<close>].
    have "(tl (tl ws)) \<in> \<langle>{[a, b]}\<rangle> "
    proof (cases "tl (tl ws) = \<epsilon>")
      assume "tl (tl ws) \<noteq> \<epsilon>"
      from pref_hd_eq[OF \<open>tl (tl ws) \<le>p [a, b] \<cdot> tl (tl ws)\<close> this]
      have "hd (tl (tl ws)) = a" by simp
      have "last (tl (tl ws)) = last ws"
        using \<open>tl (tl ws) \<noteq> \<epsilon>\<close> last_tl tl_Nil by metis
      from \<open>hd ws \<noteq> last ws\<close>[unfolded \<open>hd ws =a\<close>, folded this \<open>hd (tl (tl ws)) = a\<close>]
      have "hd (tl (tl ws)) \<noteq> last (tl (tl ws))".
      from less.hyps[OF ind \<open>tl (tl ws) \<le>p [a,b] \<cdot> tl (tl ws)\<close> this]
      show "(tl (tl ws)) \<in> \<langle>{[a, b]}\<rangle>".
    qed simp
    from prod_cl[OF singletonI this]
    show "ws \<in> \<langle>{[a,b]}\<rangle>"
      unfolding  *[folded \<open>[a,b] = [hd ws, hd (tl ws)]\<close>].
  qed simp
qed

lemma no_cyclic_repetition_list:
  assumes  "set ws \<subseteq> {a,b}" "ws \<notin> \<langle>{[a,b]}\<rangle>" "ws \<notin> \<langle>{[b,a]}\<rangle>" "hd ws \<noteq> last ws"
    "\<not> [a,a] \<le>f ws" "\<not> [b,b] \<le>f ws"
  shows False
  using per_root_hd_last_root[OF _ \<open>hd ws \<noteq> last ws\<close>] \<open>ws \<notin> \<langle>{[a,b]}\<rangle>\<close> \<open>ws \<notin> \<langle>{[b,a]}\<rangle>\<close>
        no_repetition_list[OF assms(1) _ _ assms(5-6)] by blast

subsection \<open>Three covers\<close>

\<comment> \<open>Example:
$v = a$
$t = (b a^(j+1))^k b a$
$r = a b (a^(j+1) b)^k$
$t' = $
$w = (a (b a^(j+1))^l b) a^(j+1) ((b a^(j+1))^m b a)$
\<close>

lemma three_covers_example:
  assumes
    v: "v = \<aa>" and
    t: "t = (\<bb> \<cdot> \<aa>\<^sup>@(j+1))\<^sup>@(m + l + 1) \<cdot> \<bb> \<cdot> \<aa> " and
    r: "r = \<aa> \<cdot> \<bb> \<cdot> (\<aa>\<^sup>@(j+1) \<cdot> \<bb>)\<^sup>@(m + l + 1)" and
    t': "t' = (\<bb> \<cdot> \<aa>\<^sup>@(j + 1))\<^sup>@m \<cdot> \<bb> \<cdot> \<aa> " and
    r': "r' = \<aa> \<cdot> \<bb> \<cdot> (\<aa>\<^sup>@(j + 1) \<cdot> \<bb>)\<^sup>@l" and
    w: "w = \<aa> \<cdot> (\<bb> \<cdot> \<aa>\<^sup>@(j + 1))\<^sup>@(m + l + 1) \<cdot> \<bb> \<cdot> \<aa>  "
  shows "w = v \<cdot> t" and "w = r \<cdot> v" and "w = r' \<cdot> v\<^sup>@(j + 1) \<cdot> t'" and "t' <p t" and "r' <s r"
proof-
  show "w = v \<cdot> t"
    unfolding w v t..
  show "w = r \<cdot> v"
    unfolding  w r v by comparison
  find_theorems "?u \<cdot> ?u\<^sup>@?j = ?u\<^sup>@?j \<cdot> ?u"
  show "t' <p t"
    unfolding t t' unfolding add.assoc unfolding add.commute[of l]
    unfolding pow_add rassoc spref_cancel_conv unfolding pow_list_1
    unfolding rassoc spref_cancel_conv
    unfolding lassoc shifts(20)
    unfolding rassoc by blast
  have "r = \<aa> \<cdot> \<bb> \<cdot> (\<aa>\<^sup>@Suc j \<cdot> \<bb>)\<^sup>@ m \<cdot> \<aa>\<^sup>@j \<cdot>  r'"
    unfolding r' r by comparison
  thus "r' <s r"
    by force
  show "w = r' \<cdot> v\<^sup>@(j + 1) \<cdot> t'"
    unfolding w r' v t'
    by comparison
qed

lemma three_covers_pers: \<comment> \<open>alias Old Good Lemma\<close>
  assumes "w = v \<cdot> t" and "w = r' \<cdot> v\<^sup>@j \<cdot> t'" and "w = r \<cdot> v" and "0 < j" and
    "r' <s r" and "t' <p t"
  shows "period w (\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|)" and "period w (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|)" and
    "(\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|) + (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|) = \<^bold>|w\<^bold>| + j*\<^bold>|v\<^bold>| - 2*\<^bold>|v\<^bold>|"
proof-
  let ?per_r = "\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|"
  let ?per_t = "\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|"
  let ?gcd = "gcd (\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|) (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|)"
  have "w \<noteq> \<epsilon>"
    using \<open>w = v \<cdot> t\<close> \<open>t' <p t\<close> by auto
  obtain "r''" where "r'' \<cdot> r' = r" and "r'' \<noteq> \<epsilon>"
    using  ssufD[OF \<open>r' <s r\<close>] sufD by blast
  have "w <p r'' \<cdot> w"
    using per_rootI[OF _ \<open>r'' \<noteq> \<epsilon>\<close>, of w] \<open>w = r \<cdot> v\<close> \<open>w = r' \<cdot> v \<^sup>@ j \<cdot> t'\<close> \<open>r'' \<cdot> r' = r\<close>
    unfolding pow_pos[OF \<open>0 < j\<close>] using rassoc triv_pref  by metis
  thus "period w ?per_r"
    using lenarg[OF \<open>r'' \<cdot> r' = r\<close>] sprefD1[OF \<open>w <p r'' \<cdot> w\<close>] diff_add_inverse2 periodI_pref'
    unfolding lenmorph by metis
  have "\<^bold>|r'\<^bold>| < \<^bold>|r\<^bold>|"
    using suffix_length_less[OF \<open>r' <s r\<close>].
  have "\<^bold>|t'\<^bold>| < \<^bold>|t\<^bold>|"
    using prefix_length_less[OF \<open>t' <p t\<close>].
  obtain t'' where "t' \<cdot> t'' = t" and "t'' \<noteq> \<epsilon>"
    using \<open>t' <p t\<close> by blast
  have "w <s w \<cdot> t''"
    using per_rootI[reversed, OF _ \<open>t'' \<noteq> \<epsilon>\<close>, of w]
     \<open>w = v \<cdot> t\<close> \<open>w = r' \<cdot> v \<^sup>@ j \<cdot> t'\<close> \<open>t' \<cdot> t'' = t\<close>
     unfolding pow_pos2[OF \<open>0 < j\<close>] using rassoc triv_suf by metis
   show "period w ?per_t"
    using lenarg[OF \<open>t' \<cdot> t'' = t\<close>] ssufD1[OF \<open>w <s w \<cdot> t''\<close>] periodI_suf' diff_add_inverse
    unfolding lenmorph  by metis
  show eq: "?per_t + ?per_r = \<^bold>|w\<^bold>| + j*\<^bold>|v\<^bold>| - 2*\<^bold>|v\<^bold>|"
    using lenarg[OF \<open>w = r' \<cdot> v\<^sup>@ j \<cdot> t'\<close>]
      lenarg[OF \<open>w = v \<cdot> t\<close>] lenarg[OF \<open>w = r \<cdot> v\<close>] \<open>\<^bold>|t'\<^bold>| < \<^bold>|t\<^bold>|\<close> \<open>\<^bold>|r'\<^bold>| < \<^bold>|r\<^bold>|\<close>
    unfolding pow_len lenmorph by force
qed

lemma three_covers_per0: assumes "w = v \<cdot> t" and "w = r' \<cdot> v\<^sup>@ j \<cdot> t'" and "w = r \<cdot> v" and "0 < j"
  "r' <s r" and "t' <p t" and "\<^bold>|t'\<^bold>| \<le> \<^bold>|r'\<^bold>|"
  and "primitive v"
shows "period w (gcd (\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|) (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|))"
  using assms
proof (induct "\<^bold>|w\<^bold>|" arbitrary: w t r t' r' v rule: less_induct)
  case less
  then show ?case
  proof-
    let ?per_r = "\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|"
    let ?per_t = "\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|"
    let ?gcd = "gcd (\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|) (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|)"
    have "v \<noteq> \<epsilon>" using prim_nemp[OF \<open>primitive v\<close>].
    have "w \<noteq> \<epsilon>"
      using \<open>w = v \<cdot> t\<close> \<open>v \<noteq> \<epsilon>\<close> by blast
    note prefix_length_less[OF \<open>t' <p t\<close>] prefix_length_less[reversed, OF \<open>r' <s r\<close>]
    have  "?gcd \<noteq> 0"
      using gcd_eq_0_iff zero_less_diff'[OF \<open>\<^bold>|t'\<^bold>| < \<^bold>|t\<^bold>|\<close>] by simp
    have "period w ?per_t" and "period w ?per_r"
          and eq: "?per_t + ?per_r = \<^bold>|w\<^bold>| + j*\<^bold>|v\<^bold>| - 2*\<^bold>|v\<^bold>|"
      using three_covers_pers[OF \<open>w = v \<cdot> t\<close> \<open>w = r' \<cdot> v \<^sup>@ j \<cdot> t'\<close> \<open>w = r \<cdot> v\<close> \<open>0 < j\<close> \<open>r' <s r\<close> \<open>t' <p t\<close>].

    obtain "r''" where "r'' \<cdot> r' = r" and "r'' \<noteq> \<epsilon>"
      using  ssufD[OF \<open>r' <s r\<close>] sufD by blast
    hence "w \<le>p r'' \<cdot> w"
      using less.prems unfolding pow_pos[OF \<open>0 < j\<close>] using rassoc triv_pref by metis
    obtain "t''" where "t' \<cdot> t'' = t" and "t'' \<noteq> \<epsilon>"
      using  sprefD[OF \<open>t' <p t\<close>] prefD by blast

    show "period w ?gcd"
    proof (cases)
      have local_rule: "a - c \<le> b \<Longrightarrow> k + a - c - b \<le> k" for a b c k :: nat
        by simp
      assume "j*\<^bold>|v\<^bold>| - 2*\<^bold>|v\<^bold>| \<le> ?gcd" \<comment> \<open>Condition allowing to use the periodicity lemma\<close>
      from local_rule[OF this]
      have len: "?per_t + ?per_r - ?gcd \<le> \<^bold>|w\<^bold>|"
        unfolding eq.
      show "period w ?gcd"
        using per_lemma[OF \<open>period w ?per_t\<close> \<open>period w ?per_r\<close> len].
    next
      assume "\<not> j*\<^bold>|v\<^bold>| - 2*\<^bold>|v\<^bold>| \<le> ?gcd"  \<comment> \<open>Periods are too long for the periodicity lemma\<close>
      hence "?gcd \<le> \<^bold>|v\<^sup>@j\<^bold>| - 2*\<^bold>|v\<^bold>|"  \<comment> \<open>But then we have a potential for using the periodicity lemma on the power of v's\<close>
        unfolding pow_len by linarith
                                   hence "?gcd + \<^bold>|v\<^bold>| \<le> \<^bold>|v \<^sup>@  j\<^bold>|"
        using \<open>?gcd \<noteq> 0\<close> by linarith


      show "period w ?gcd"
      proof (cases)
        assume "\<^bold>|r'\<^bold>| = \<^bold>|t'\<^bold>|" \<comment> \<open>The trivial case\<close>
        hence "\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>| = \<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|"
          using eq_conjug_len[OF \<open>w = v \<cdot> t\<close>[unfolded \<open>w = r \<cdot> v\<close>]] by force
        show "period w (gcd (\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|) (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|))"
          unfolding \<open>\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>| = \<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|\<close>  gcd_idem_nat using \<open>period w (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|)\<close>.
      next
        assume "\<^bold>|r'\<^bold>| \<noteq> \<^bold>|t'\<^bold>|" \<comment> \<open>The nontrivial case\<close>
        hence "\<^bold>|t'\<^bold>| < \<^bold>|r'\<^bold>|"
          using \<open>\<^bold>|t'\<^bold>| \<le> \<^bold>|r'\<^bold>|\<close> by force
        have "r' \<cdot> v <p w"
          using \<open>\<^bold>|r'\<^bold>| < \<^bold>|r\<^bold>|\<close> \<open>r'' \<cdot> r' = r\<close> \<open>w \<le>p r'' \<cdot> w\<close> \<open>w = r \<cdot> v\<close> by force
        obtain p where "r' \<cdot> v = v \<cdot> p"
          using   ruler_le[OF triv_pref[of v t , folded \<open>w = v \<cdot> t\<close>], of "r' \<cdot> v"]
          unfolding lenmorph \<open>w = r' \<cdot> v\<^sup>@j \<cdot> t'\<close>[unfolded pow_pos[OF \<open>0 < j\<close>]] rassoc
          by (force simp add: prefix_def)
        from \<open>w = r' \<cdot> v\<^sup>@j \<cdot> t'\<close>[unfolded pow_pos[OF \<open>0 < j\<close>] lassoc this \<open>w = v \<cdot> t\<close>, unfolded rassoc cancel]
        have "p \<le>p t"
          by blast
        have "\<^bold>|v \<cdot> p\<^bold>| < \<^bold>|w\<^bold>|"
          using prefix_length_less[OF \<open>r' \<cdot> v <p w\<close>, unfolded \<open>r' \<cdot> v = v \<cdot> p\<close>].
        have "v \<cdot> p \<le>s w" \<comment> \<open>r'v is a long border of w\<close>
          using \<open>r' \<cdot> v = v \<cdot> p\<close> \<open>w = r \<cdot> v\<close> \<open>r' <s r\<close> same_suffix_suffix ssufD by metis
        have "\<^bold>|r'\<^bold>| = \<^bold>|p\<^bold>|"
          using eq_conjug_len[OF \<open>r' \<cdot> v = v \<cdot> p\<close>].
        note \<open>\<^bold>|t'\<^bold>| \<le> \<^bold>|r'\<^bold>|\<close>[unfolded \<open>\<^bold>|r'\<^bold>| = \<^bold>|p\<^bold>|\<close>]
        hence "t' <p p"
          using \<open>t = p \<cdot> v \<^sup>@ (j - 1) \<cdot> t'\<close> \<open>t' \<cdot> t'' = t\<close> \<open>\<^bold>|r'\<^bold>| = \<^bold>|p\<^bold>|\<close> \<open>\<^bold>|t'\<^bold>| < \<^bold>|r'\<^bold>|\<close> \<open>p \<le>p t\<close> pref_prod_long_less by metis
        hence "p \<noteq> \<epsilon>"
            by auto
        show ?thesis
        proof (cases)
          assume "\<^bold>|v \<cdot> p\<^bold>| \<le> \<^bold>|v\<^sup>@j \<cdot> t'\<^bold>|" \<comment> \<open>The border does not cover the whole power of v's.
                                              In this case, everything commutes\<close>
          have "\<rho> (rev v) = rev (\<rho> v)"
            using \<open>v \<noteq> \<epsilon>\<close> primroot_rev by auto
          from pref_marker_ext[reversed, OF \<open>\<^bold>|t'\<^bold>| \<le> \<^bold>|p\<^bold>|\<close> \<open>v \<noteq> \<epsilon>\<close>]
            suf_prod_le[OF \<open>v \<cdot> p \<le>s w\<close>[unfolded \<open>w = r' \<cdot> v\<^sup>@j \<cdot> t'\<close>] \<open>\<^bold>|v \<cdot> p\<^bold>| \<le> \<^bold>|v\<^sup>@j \<cdot> t'\<^bold>|\<close>]
          obtain k where "p = v\<^sup>@k \<cdot> t'"
            unfolding  prim_primroot[OF \<open>primitive v\<close>].
          hence "p \<le>p v\<^sup>@k \<cdot> p"
            using \<open>t' <p p\<close> by simp
          from root_comm_root[OF this pow_comm[symmetric]]
          have "p \<le>p v \<cdot> p"
            using \<open>\<^bold>|r'\<^bold>| = \<^bold>|p\<^bold>|\<close> \<open>\<^bold>|r'\<^bold>| \<noteq> \<^bold>|t'\<^bold>|\<close> \<open>p = v \<^sup>@ k \<cdot> t'\<close> by force
          hence "p = r'"
            using \<open>\<^bold>|r'\<^bold>| = \<^bold>|p\<^bold>|\<close> \<open>r' \<cdot> v = v \<cdot> p\<close> pref_prod_eq by metis
          note \<open>r' \<cdot> v = v \<cdot> p\<close>[folded this] \<open>r' \<cdot> v = v \<cdot> p\<close>[unfolded this]
          then obtain er' where "r' = v\<^sup>@er'"
            using \<open>primitive v\<close> by auto
          from \<open>p \<cdot> v = v \<cdot> p\<close>[unfolded \<open>p = v\<^sup>@k \<cdot> t'\<close> lassoc pow_comm[symmetric], unfolded rassoc cancel]
          have "t' \<cdot> v = v \<cdot> t'".
          then obtain et' where "t' = v\<^sup>@et'"
            using \<open>primitive v\<close> by auto
          have "t \<cdot> v = v \<cdot> t"
            by (simp add: pow_comm \<open>p = r'\<close> \<open>r' \<cdot> v = v \<cdot> r'\<close> \<open>t = p \<cdot> v \<^sup>@ (j - 1) \<cdot> t'\<close> \<open>t' \<cdot> v = v \<cdot> t'\<close>)
          then obtain et where "t = v\<^sup>@et"
            using \<open>primitive v\<close> by auto
          have "r \<cdot> v = v \<cdot> r"
            using \<open>t \<cdot> v = v \<cdot> t\<close> cancel_right \<open>w = v \<cdot> t\<close> \<open>w = r \<cdot> v\<close> by metis
          then obtain er where "r = v\<^sup>@er"
            using \<open>primitive v\<close> by auto
          have "w \<cdot> v = v \<cdot> w"
            by (simp add: \<open>r \<cdot> v = v \<cdot> r\<close> \<open>w = r \<cdot> v\<close>)
          then obtain ew where "w = v\<^sup>@ew"
            using \<open>primitive v\<close> by auto
          hence "period w \<^bold>|v\<^bold>|"
            using \<open>v \<noteq> \<epsilon>\<close> \<open>w \<cdot> v = v \<cdot> w\<close> \<open>w \<noteq> \<epsilon>\<close> by blast
          have dift: "\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>| = (et - et')*\<^bold>|v\<^bold>|"
            using lenarg[OF \<open>t = v\<^sup>@et\<close>] lenarg[OF \<open>t' = v\<^sup>@et'\<close>] unfolding lenmorph pow_len
            by (simp add: diff_mult_distrib)
          have difr: "(\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|) = (er - er')*\<^bold>|v\<^bold>|"
            using lenarg[OF \<open>r = v\<^sup>@er\<close>] lenarg[OF \<open>r' = v\<^sup>@er'\<close>] unfolding lenmorph pow_len
            by (simp add: diff_mult_distrib)
          obtain g where g: "g*\<^bold>|v\<^bold>| = ?gcd"
            unfolding dift difr mult.commute[of _ "\<^bold>|v\<^bold>|"]
              gcd_mult_distrib_nat[symmetric] by blast
          from per_mult[OF \<open>period w \<^bold>|v\<^bold>|\<close>, of g]
          show ?thesis
            unfolding g.
        next
          assume "\<not> \<^bold>|v \<cdot> p\<^bold>| \<le> \<^bold>|v \<^sup>@ j \<cdot> t'\<^bold>|"  \<comment> \<open>The border covers the whole power. An induction is available.\<close>
          then obtain ri' where "v \<cdot> p = ri'\<cdot> v\<^sup>@j \<cdot> t'" and "ri' \<le>s r'"
            using \<open>v \<cdot> p \<le>s w\<close> unfolding \<open>w = r' \<cdot> v\<^sup>@j \<cdot> t'\<close>
            using suffix_append suffix_length_le by blast
          from len_less_neq[OF \<open>\<^bold>|v \<cdot> p\<^bold>| < \<^bold>|w\<^bold>|\<close>, unfolded this(1) \<open>w = r' \<cdot> v\<^sup>@j \<cdot> t'\<close>] this(2)
          have "ri' <s r'"
            by blast

          have gcd_eq: "gcd (\<^bold>|p\<^bold>| - \<^bold>|t'\<^bold>|) (\<^bold>|r'\<^bold>| - \<^bold>|ri'\<^bold>|) = ?gcd" \<comment> \<open>The two gcd's are the same\<close>
          proof-
            have "\<^bold>|r'\<^bold>| \<le> \<^bold>|r\<^bold>|"
              by (simp add: \<open>\<^bold>|r'\<^bold>| < \<^bold>|r\<^bold>|\<close> dual_order.strict_implies_order)
            have "\<^bold>|t\<^bold>| = \<^bold>|r\<^bold>|"
              using lenarg[OF \<open>w = v \<cdot> t\<close>] unfolding lenarg[OF \<open>w = r \<cdot> v\<close>]  lenmorph by auto
            have e1: "\<^bold>|r'\<^bold>| - \<^bold>|ri'\<^bold>| = \<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|"
              using lenarg[OF \<open>v \<cdot> p = ri'\<cdot>v\<^sup>@ j \<cdot> t'\<close>[folded \<open>r' \<cdot> v = v \<cdot> p\<close>]]
                lenarg[OF \<open>w = r \<cdot> v\<close>[unfolded \<open>w = r' \<cdot> v\<^sup>@ j \<cdot> t'\<close>]]
              unfolding lenmorph pow_len by (simp add: add.commute diff_add_inverse diff_diff_add)
            have "\<^bold>|t\<^bold>| = \<^bold>|p\<^bold>| + \<^bold>|r'\<^bold>| - \<^bold>|ri'\<^bold>|"
              unfolding add_diff_assoc[OF suffix_length_le[OF \<open>ri' \<le>s r'\<close>], unfolded e1, symmetric]
                \<open>\<^bold>|t\<^bold>| = \<^bold>|r\<^bold>|\<close> unfolding \<open>\<^bold>|r'\<^bold>| = \<^bold>|p\<^bold>|\<close>
              using \<open>\<^bold>|r'\<^bold>| < \<^bold>|r\<^bold>|\<close>[unfolded \<open>\<^bold>|r'\<^bold>| = \<^bold>|p\<^bold>|\<close>] by linarith
            hence e2: "\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>| = (\<^bold>|p\<^bold>| - \<^bold>|t'\<^bold>|) + (\<^bold>|r'\<^bold>| - \<^bold>|ri'\<^bold>|)"
              unfolding add_diff_assoc2[OF \<open>\<^bold>|t'\<^bold>| \<le> \<^bold>|p\<^bold>|\<close>] \<open>\<^bold>|t\<^bold>| = \<^bold>|p\<^bold>| + \<^bold>|r'\<^bold>| - \<^bold>|ri'\<^bold>|\<close>
              using suf_len[OF \<open>ri' \<le>s r'\<close>] by force
            show ?thesis
              unfolding e2 e1 gcd_add1..
          qed

          have per_vp: "period (v \<cdot> p) ?gcd"
          proof (cases)
            assume "\<^bold>|t'\<^bold>| \<le> \<^bold>|ri'\<^bold>|"
              \<comment> \<open>By induction.\<close>
            from less.hyps[OF \<open>\<^bold>|v \<cdot> p\<^bold>| < \<^bold>|w\<^bold>|\<close> refl \<open>v \<cdot> p = ri'\<cdot>v\<^sup>@ j \<cdot> t'\<close> \<open>r' \<cdot> v = v \<cdot> p\<close>[symmetric] \<open>0 < j\<close>
            \<open>ri' <s r'\<close> \<open>t' <p p\<close> this \<open>primitive v\<close>]
            show "period (v \<cdot> p) ?gcd"
              unfolding gcd_eq by blast
          next \<comment> \<open>...(using symmetry)\<close>
            assume "\<not> \<^bold>|t'\<^bold>| \<le> \<^bold>|ri'\<^bold>|" hence "\<^bold>|ri'\<^bold>| \<le> \<^bold>|t'\<^bold>|" by simp
            have "period (rev p \<cdot> rev v) (gcd (\<^bold>|rev r'\<^bold>| - \<^bold>|rev ri'\<^bold>|) (\<^bold>|rev p\<^bold>| - \<^bold>|rev t'\<^bold>|))"
            proof (rule less.hyps[OF _ _ _ refl])
              show "\<^bold>|rev p \<cdot> rev v\<^bold>| < \<^bold>|w\<^bold>|"
                using \<open>\<^bold>|v \<cdot> p\<^bold>| < \<^bold>|w\<^bold>|\<close> by simp
              show "rev p \<cdot> rev v = rev v \<cdot> rev r'"
                using \<open>r' \<cdot> v = v \<cdot> p\<close> unfolding rev_append[symmetric] by simp
              show "rev p \<cdot> rev v = rev t' \<cdot> rev v \<^sup>@ j \<cdot> rev ri'"
                using \<open>v \<cdot> p = ri'\<cdot>v\<^sup>@ j \<cdot> t'\<close> unfolding rev_append[symmetric] rev_pow[symmetric] rassoc by simp
              show "rev t' <s rev p"
                using \<open>t' <p p\<close> by (auto simp add: prefix_def)
              show "rev ri' <p rev r'"
                using \<open>ri' <s r'\<close> strict_suffix_to_prefix by blast
              show "\<^bold>|rev ri'\<^bold>| \<le> \<^bold>|rev t'\<^bold>|"
                by (simp add: \<open>\<^bold>|ri'\<^bold>| \<le> \<^bold>|t'\<^bold>|\<close>)
              show "primitive (rev v)"
                by (simp add: \<open>primitive v\<close> prim_rev_iff)
            qed fact
            thus ?thesis
              unfolding length_rev rev_append[symmetric] period_rev_conv gcd.commute[of "\<^bold>|r'\<^bold>| - \<^bold>|ri'\<^bold>|"] gcd_eq.
          qed

          have "period (v\<^sup>@ j) (gcd \<^bold>|v\<^bold>| ?gcd)"
          proof (rule per_lemma)
            show " \<^bold>|v\<^bold>| + ?gcd - gcd \<^bold>|v\<^bold>| (gcd (\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|) (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|)) \<le> \<^bold>|v \<^sup>@ j\<^bold>|"
              using \<open>?gcd + \<^bold>|v\<^bold>| \<le> \<^bold>|v \<^sup>@  j\<^bold>|\<close> by linarith
            show "period (v \<^sup>@ j) \<^bold>|v\<^bold>|"
              using \<open>v \<noteq> \<epsilon>\<close> \<open>0 < j\<close>
              by blast
            find_theorems "?v\<^sup>@?n" "?w = \<epsilon>"
            have "v \<^sup>@ j \<noteq> \<epsilon>"
               using  \<open>0 < j\<close> \<open>v \<noteq> \<epsilon>\<close> by blast
            from period_fac_period[OF per_vp[unfolded \<open>v \<cdot> p = ri' \<cdot> v \<^sup>@ j \<cdot> t'\<close>]]
            show "period (v \<^sup>@ j) ?gcd".
          qed

          have per_vp': "period (v \<cdot> p) (gcd \<^bold>|v\<^bold>| ?gcd)"
          proof (rule refine_per)
            show "gcd \<^bold>|v\<^bold>| ?gcd dvd ?gcd" by blast
            show "?gcd \<le> \<^bold>|v\<^sup>@j\<^bold>|"
              using \<open>?gcd + \<^bold>|v\<^bold>| \<le> \<^bold>|v \<^sup>@ j\<^bold>|\<close> add_leE by blast
            show "v \<^sup>@ j \<le>f v \<cdot> p"
              using  facI'[OF \<open>v \<cdot> p = ri' \<cdot> v \<^sup>@ j \<cdot> t'\<close>[symmetric]].
          qed fact+

          have "period w (gcd \<^bold>|v\<^bold>| ?gcd)"
          proof (rule per_glue)
            show "v \<cdot> p \<le>p w"
              using \<open>p \<le>p t\<close> \<open>w = v \<cdot> t\<close> by auto
            have "\<^bold>|v \<^sup>@ j\<^bold>| + \<^bold>|t'\<^bold>| \<le> \<^bold>|v\<^bold>| + \<^bold>|p\<^bold>|"
              using \<open>\<not> \<^bold>|v \<cdot> p\<^bold>| \<le> \<^bold>|v \<^sup>@ j \<cdot> t'\<^bold>|\<close> by auto
            moreover have "\<^bold>|r'\<^bold>| + gcd \<^bold>|v\<^bold>| ?gcd \<le> \<^bold>|v\<^bold>| + \<^bold>|p\<^bold>|"
              using lenarg[OF \<open>r' \<cdot> v = v \<cdot> p\<close>, unfolded lenmorph]
                \<open>v \<noteq> \<epsilon>\<close> gcd_le1_nat length_0_conv nat_add_left_cancel_le by metis
            ultimately show "\<^bold>|w\<^bold>| + gcd \<^bold>|v\<^bold>| ?gcd \<le> \<^bold>|v \<cdot> p\<^bold>| + \<^bold>|v \<cdot> p\<^bold>|"
              unfolding lenarg[OF \<open>w = r' \<cdot> v \<^sup>@ j \<cdot> t'\<close>] lenmorph add.commute[of "\<^bold>|r'\<^bold>|"] by linarith
          qed fact+

          obtain k where k: "?gcd = k*(gcd \<^bold>|v\<^bold>| ?gcd)"
            using gcd_dvd2 unfolding dvd_def mult.commute[of _ "gcd \<^bold>|v\<^bold>| ?gcd"] by blast
          hence "k \<noteq> 0"
            using \<open>?gcd \<noteq> 0\<close> by algebra
          from per_mult[OF \<open>period w (gcd \<^bold>|v\<^bold>| ?gcd)\<close>, of k, folded k]
          show ?thesis.
        qed
      qed
    qed
  qed
qed

lemma three_covers_per: assumes "w = v \<cdot> t" and "w = r' \<cdot> v\<^sup>@j \<cdot> t'" and "w = r \<cdot> v"
  "r' <s r" and "t' <p t" and "0 < j"
shows "period w (gcd (\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|) (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|))"
proof-
  let ?per_r = "\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|"
  let ?per_t = "\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|"
  let ?gcd = "gcd (\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|) (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|)"
  have "period w ?per_t" and "period w ?per_r" and len: "(\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|) + (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|) = \<^bold>|w\<^bold>| + j*\<^bold>|v\<^bold>| - 2*\<^bold>|v\<^bold>|"
    using three_covers_pers[OF \<open>w = v \<cdot> t\<close> \<open>w = r' \<cdot> v \<^sup>@ j \<cdot> t'\<close> \<open>w = r \<cdot> v\<close> \<open>0 < j\<close> \<open>r' <s r\<close> \<open>t' <p t\<close>] by blast+

  show ?thesis
  proof(cases)
    assume "v = \<epsilon>"
    have "\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>| + (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|) = \<^bold>|w\<^bold>|"
      using \<open>w = v \<cdot> t\<close> \<open>w = r' \<cdot> v\<^sup>@j \<cdot> t'\<close> \<open>w = r \<cdot> v\<close> unfolding \<open>v = \<epsilon>\<close> emp_simps  by force
    from per_lemma[OF \<open>period w ?per_t\<close> \<open>period w ?per_r\<close>, unfolded this]
    show "period w ?gcd"
      by fastforce
  next
    assume "v \<noteq> \<epsilon>"
    show ?thesis
    proof (cases)
      assume "j \<le> 1"
      hence "(j = 0 \<Longrightarrow> P) \<Longrightarrow> (j = 1 \<Longrightarrow> P) \<Longrightarrow> P" for P by force
      hence "\<^bold>|w\<^bold>| + j*\<^bold>|v\<^bold>| - 2*\<^bold>|v\<^bold>| - ?gcd \<le> \<^bold>|w\<^bold>|" \<comment> \<open>Condition allowing to use the periodicity lemma\<close>
        by (cases, simp_all)
      thus "period w ?gcd"
        using per_lemma[OF \<open>period w ?per_t\<close> \<open>period w ?per_r\<close>] unfolding len by blast
    next
      assume "\<not> j \<le> 1" hence "2 \<le> j" by simp
      obtain e where "v = \<rho> v\<^sup>@e" "0 < e"
        using  primroot_expE by metis
      have "w = \<rho> v \<cdot> \<rho> v\<^sup>@(e -1) \<cdot> t"
        unfolding lassoc pow_pos[OF \<open>0 < e\<close>, symmetric] \<open>v = \<rho> v\<^sup>@e\<close>[symmetric] by fact
      have "w = (r \<cdot> \<rho> v\<^sup>@(e - 1)) \<cdot> \<rho> v"
        unfolding rassoc pow_pos2[OF \<open>0 < e\<close>, symmetric] \<open>v = \<rho> v\<^sup>@e\<close>[symmetric] by fact
      note aux = add_less_mono[OF diff_less[OF zero_less_one \<open>0 < e\<close>] diff_less[OF zero_less_one \<open>0 < e\<close>]]
      have "(e-1) + (e-1) < j*e"
        using  less_le_trans[OF aux mult_le_mono1[OF \<open>2 \<le> j\<close>, unfolded mult_2]].
      then obtain e' where  "(e-1) + (e-1) + e' = j*e" "0 < e'"
        using less_imp_add_positive by blast
      hence aux_sum: "(e - 1) + e' + (e - 1) = j*e"
        by presburger
      have cover3: "w = (r' \<cdot> (\<rho> v)\<^sup>@(e-1)) \<cdot> (\<rho> v) \<^sup>@e' \<cdot> ((\<rho> v)\<^sup>@(e-1) \<cdot> t')"
        unfolding  \<open>w = r' \<cdot> v\<^sup>@ j \<cdot> t'\<close> rassoc cancel unfolding lassoc cancel_right
          unfolding pow_add[symmetric]
          pow_mult unfolding  aux_sum unfolding mult.commute[of j]
          pow_mult \<open>v = \<rho> v\<^sup>@e\<close>[symmetric]..
      show ?thesis
      proof(cases)
        assume "\<^bold>|t'\<^bold>| \<le> \<^bold>|r'\<^bold>|"
        have dif1: "\<^bold>|\<rho> v \<^sup>@ (e -1) \<cdot> t\<^bold>| - \<^bold>|\<rho> v \<^sup>@ (e - 1) \<cdot> t'\<^bold>| = \<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|"
          unfolding lenmorph by simp
        have dif2: "\<^bold>|r \<cdot> \<rho> v \<^sup>@ (e-1)\<^bold>| - \<^bold>|r' \<cdot> \<rho> v \<^sup>@ (e-1)\<^bold>| = \<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|"
          unfolding lenmorph by simp

        show ?thesis
        proof (rule  three_covers_per0[OF \<open>w = \<rho> v \<cdot> (\<rho> v\<^sup>@(e -1) \<cdot> t)\<close>
              cover3 \<open>w = (r \<cdot> \<rho> v\<^sup>@(e - 1)) \<cdot> \<rho> v\<close> \<open>0 < e'\<close> _ _ _ primroot_prim[OF \<open>v \<noteq> \<epsilon>\<close>],
               unfolded dif1 dif2])
          show "r' \<cdot> \<rho> v \<^sup>@ (e -1) <s r \<cdot> \<rho> v \<^sup>@ (e -1)"
            using \<open>r' <s r\<close> by auto
          show "\<rho> v \<^sup>@ (e - 1) \<cdot> t' <p \<rho> v \<^sup>@ (e - 1) \<cdot> t"
            using \<open>t' <p t\<close> by auto
          show "\<^bold>|\<rho> v \<^sup>@ (e -1) \<cdot> t'\<^bold>| \<le> \<^bold>|r' \<cdot> \<rho> v \<^sup>@ (e - 1)\<^bold>|"
            unfolding lenmorph using \<open>\<^bold>|t'\<^bold>| \<le> \<^bold>|r'\<^bold>|\<close> by auto
        qed
      next
        let ?w = "rev w" and ?r = "rev t" and ?t = "rev r" and ?\<rho> = "rev (\<rho> v)" and ?r' = "rev t'" and ?t' = "rev r'"
        assume "\<not> \<^bold>|t'\<^bold>| \<le> \<^bold>|r'\<^bold>|"
        hence "\<^bold>|?t'\<^bold>| \<le> \<^bold>|?r'\<^bold>|" by auto
        have "?w = (?r \<cdot> ?\<rho>\<^sup>@(e-1)) \<cdot> ?\<rho>"
          unfolding rev_pow[symmetric] rev_append[symmetric] \<open>w = \<rho> v \<cdot> (\<rho> v\<^sup>@(e-1) \<cdot> t)\<close> rassoc..
        have "?w = ?\<rho> \<cdot> (?\<rho>\<^sup>@(e-1) \<cdot> ?t)"
          unfolding rev_pow[symmetric] rev_append[symmetric] \<open>w = (r \<cdot> \<rho> v\<^sup>@(e-1)) \<cdot> \<rho> v\<close>..
        have "?w = (?r' \<cdot> ?\<rho>\<^sup>@(e-1)) \<cdot> ?\<rho>\<^sup>@e' \<cdot> (?\<rho>\<^sup>@(e-1) \<cdot> ?t')"
          unfolding rev_pow[symmetric] rev_append[symmetric] \<open>w = (r' \<cdot> \<rho> v\<^sup>@(e-1)) \<cdot> \<rho> v \<^sup>@e' \<cdot> (\<rho> v\<^sup>@(e-1) \<cdot> t')\<close> rassoc..
        have dif1: "\<^bold>|?\<rho> \<^sup>@ (e-1) \<cdot> ?t\<^bold>| - \<^bold>|?\<rho> \<^sup>@ (e-1) \<cdot> ?t'\<^bold>| = \<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|"
          unfolding lenmorph by simp
        have dif2: "\<^bold>|?r \<cdot> ?\<rho> \<^sup>@ (e-1)\<^bold>| - \<^bold>|?r' \<cdot> ?\<rho> \<^sup>@ (e-1)\<^bold>| = \<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|"
          unfolding lenmorph by simp
        show ?thesis
        proof(rule three_covers_per0[OF \<open>?w = ?\<rho> \<cdot> (?\<rho>\<^sup>@(e-1) \<cdot> ?t)\<close>
              \<open>?w = (?r' \<cdot> ?\<rho>\<^sup>@(e-1)) \<cdot> ?\<rho>\<^sup>@e' \<cdot> (?\<rho>\<^sup>@(e-1) \<cdot> ?t')\<close> \<open>?w = (?r \<cdot> ?\<rho>\<^sup>@(e-1)) \<cdot> ?\<rho>\<close> \<open>0 < e'\<close>,
              unfolded dif1 dif2 period_rev_conv gcd.commute[of "\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|"]])
          show "?r' \<cdot> ?\<rho> \<^sup>@ (e-1) <s ?r \<cdot> ?\<rho> \<^sup>@ (e-1)"
            using \<open>t' <p t\<close> by (auto simp add: prefix_def)
          show "?\<rho> \<^sup>@ (e-1) \<cdot> ?t' <p ?\<rho> \<^sup>@ (e-1) \<cdot> ?t"
            using \<open>r' <s r\<close> by (auto simp add: suffix_def)
          show "\<^bold>|?\<rho> \<^sup>@ (e-1) \<cdot> ?t'\<^bold>| \<le> \<^bold>|?r' \<cdot> ?\<rho> \<^sup>@ (e-1)\<^bold>|"
            unfolding lenmorph using \<open>\<^bold>|?t'\<^bold>| \<le> \<^bold>|?r'\<^bold>|\<close> by auto
          show "primitive ?\<rho>"
            using primroot_prim[OF \<open>v \<noteq> \<epsilon>\<close>] by (simp add: prim_rev_iff)
        qed
      qed
    qed
  qed
qed

thm per_root_modE'

lemma assumes "w \<le>p r \<cdot> w" "r \<noteq> \<epsilon>"
  obtains p q i where "w = (p \<cdot> q)\<^sup>@i \<cdot> p" "p \<cdot> q = r"
  using assms by blast









lemma three_coversE: assumes "w = v \<cdot> t" and "w = r' \<cdot> v \<cdot> t'" and "w = r \<cdot> v" and
  "r' <s r" and "t' <p t"
obtains p q i k m where "t = (q \<cdot> p)\<^sup>@(m+k)" and "r = (p \<cdot> q)\<^sup>@(m+k)" and
                            "t' = (q \<cdot> p)\<^sup>@k" and "r' = (p \<cdot> q)\<^sup>@m" and "v = (p \<cdot> q)\<^sup>@i \<cdot> p" and
                            "w = (p \<cdot> q)\<^sup>@(m + i + k) \<cdot> p" and "primitive (p \<cdot> q)" and "q \<noteq> \<epsilon>"
                            and "0 < m" and "0 < k"
proof-
  let ?d = "gcd \<^bold>|r'\<^bold>| \<^bold>|t'\<^bold>|"
  have "r' \<noteq> \<epsilon>" "t' \<noteq> \<epsilon>"
    using assms by force+
  have "0 < ?d"
    using nemp_len[OF \<open>r' \<noteq> \<epsilon>\<close>] by simp
  have diffs_eq: "\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>| = \<^bold>|r'\<^bold>|" "\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>| = \<^bold>|t'\<^bold>|"
    using lenarg[OF \<open>w = v \<cdot> t\<close>] lenarg[OF \<open>w = r \<cdot> v\<close>]
    unfolding lenarg[OF \<open>w = r' \<cdot> v \<cdot> t'\<close>] lenmorph by simp_all
  have "take (gcd \<^bold>|r'\<^bold>| \<^bold>|t'\<^bold>|) w \<noteq> \<epsilon>"
    by (simp add: \<open>r' \<noteq> \<epsilon>\<close> assms(2))
  hence "w <p take (gcd \<^bold>|r'\<^bold>| \<^bold>|t'\<^bold>|) w \<cdot> w"
    using three_covers_per[of _ _ _ _1, unfolded cow_simps, OF assms order.refl, unfolded  diffs_eq period_def] by blast
  from per_root_mod_primE[OF \<open>w <p take (gcd \<^bold>|r'\<^bold>| \<^bold>|t'\<^bold>|) w \<cdot> w\<close>]
  obtain l p q  where "p \<cdot> q = \<rho> (take ?d w)" "(p \<cdot> q)\<^sup>@l \<cdot> p = w" "q \<noteq> \<epsilon>".
  hence "primitive (p \<cdot> q)" by auto
  define e  where  "e = e\<^sub>\<rho> (take ?d w)"
  have "e \<noteq> 0"
    unfolding e_def
    using \<open>w <p take (gcd \<^bold>|r'\<^bold>| \<^bold>|t'\<^bold>|) w \<cdot> w\<close> primroot_exp_nemp by blast
  have "(p \<cdot> q)\<^sup>@e = take ?d w"
    unfolding e_def \<open>p \<cdot> q = \<rho> (take ?d w)\<close> by force
  have "\<^bold>|(p \<cdot> q)\<^sup>@e\<^bold>| \<le> \<^bold>|w\<^bold>|"
    unfolding \<open>(p \<cdot> q)\<^sup>@e = take ?d w\<close>
    using len_take2 by blast
  have swap_e: "\<^bold>|(p \<cdot> q)\<^sup>@e\<^bold>| = \<^bold>|(q \<cdot> p)\<^sup>@e\<^bold>|"
    unfolding pow_len swap_len..
  have "\<^bold>|(p \<cdot> q)\<^sup>@e\<^bold>| = ?d"
    unfolding \<open>(p \<cdot> q)\<^sup>@e = take ?d w\<close>
    by (rule take_len, unfold lenarg[OF \<open>w = r' \<cdot> v \<cdot> t'\<close>, unfolded lenmorph],
    use gcd_le1_nat[OF nemp_len_not0[OF \<open>r' \<noteq> \<epsilon>\<close>]] trans_le_add1 in blast)

  hence "(p \<cdot> q)\<^sup>@e \<le>p r'"
    unfolding pref_take_conv[of "(p \<cdot> q)\<^sup>@e" r', symmetric] using \<open>w = r' \<cdot> v \<cdot> t'\<close>
     \<open>(p \<cdot> q)\<^sup>@e = take ?d w\<close>[symmetric]  gcd_le1_nat[OF nemp_len_not0[OF \<open>r' \<noteq> \<epsilon>\<close>]] short_take_append by metis
  hence "(p \<cdot> q)\<^sup>@e = take ?d  r'"
    using pref_take_conv \<open>\<^bold>|(p \<cdot> q)\<^sup>@e\<^bold>| = ?d\<close> by metis
  have "r' \<le>p (p \<cdot> q)\<^sup>@e \<cdot> r'"
    using pref_keeps_per_root[OF sprefD1[OF \<open>w <p take ?d w \<cdot> w\<close>]]
    unfolding  \<open>(p \<cdot> q)\<^sup>@e = take (gcd \<^bold>|r'\<^bold>| \<^bold>|t'\<^bold>|) w\<close>
    using \<open>w = r' \<cdot> v \<cdot> t'\<close> by blast
  define m where "m = e*(\<^bold>|r'\<^bold>| div gcd \<^bold>|r'\<^bold>| \<^bold>|t'\<^bold>|)"
  have "(p \<cdot> q)\<^sup>@m = r'"
    using per_div[OF gcd_dvd1 periodI[OF \<open>r' \<le>p (p \<cdot> q)\<^sup>@e \<cdot> r'\<close>[unfolded \<open>(p \<cdot> q)\<^sup>@e = take ?d  r'\<close>]]]
    unfolding \<open>(p \<cdot> q)\<^sup>@e = take ?d  r'\<close>[symmetric] pow_list_mult m_def.
  have "p \<le>s (q \<cdot> p) \<^sup>@ e"
    unfolding pow_Suc2[of "e-1" "q \<cdot> p", unfolded Suc_minus[OF \<open>e \<noteq> 0\<close>] lassoc] by blast
  note \<open>\<^bold>|(p \<cdot> q)\<^sup>@e\<^bold>| \<le> \<^bold>|w\<^bold>|\<close>[unfolded swap_e, folded \<open>(p \<cdot> q)\<^sup>@l \<cdot> p = w\<close>, unfolded shift_pow]
  have "(q \<cdot> p)\<^sup>@e \<le>s (r' \<cdot> v) \<cdot> t'"
    unfolding rassoc \<open>w = r' \<cdot> v \<cdot> t'\<close>[symmetric, folded \<open>(p \<cdot> q)\<^sup>@l \<cdot> p = w\<close>, unfolded shift_pow]
    using suf_prod_suf_short[OF _ \<open>p \<le>s (q \<cdot> p) \<^sup>@ e\<close> \<open> \<^bold>|(q \<cdot> p) \<^sup>@ e\<^bold>| \<le> \<^bold>|p \<cdot> (q \<cdot> p) \<^sup>@ l\<^bold>|\<close>]
    unfolding pows_comm[of e "(q \<cdot> p)" l] by blast
  have "\<^bold>|(q \<cdot> p) \<^sup>@ e\<^bold>| \<le> \<^bold>|t'\<^bold>|"
    using gcd_le2_nat[OF nemp_len_not0[OF \<open>t' \<noteq> \<epsilon>\<close>], of "\<^bold>|r'\<^bold>|", folded \<open>\<^bold>|(p \<cdot> q)\<^sup>@e\<^bold>| = ?d\<close>]
    unfolding swap_len[of p q] pow_len.
  have "(q \<cdot> p)\<^sup>@e \<le>s t'"
    unfolding \<open>w = r' \<cdot> v \<cdot> t'\<close>[unfolded lassoc]
    using suf_prod_le[OF \<open>(q \<cdot> p)\<^sup>@e \<le>s (r' \<cdot> v) \<cdot> t'\<close> \<open>\<^bold>|(q \<cdot> p) \<^sup>@ e\<^bold>| \<le> \<^bold>|t'\<^bold>|\<close>].
  have "t' \<le>s  t' \<cdot> (q \<cdot> p)\<^sup>@e"
  proof (rule pref_keeps_per_root[reversed, of w])
    show "w \<le>s w \<cdot> (q \<cdot> p)\<^sup>@e"
      unfolding \<open>(p \<cdot> q)\<^sup>@l \<cdot> p = w\<close>[symmetric, unfolded shift_pow] rassoc pows_comm
      unfolding lassoc shift_pow[symmetric]
      unfolding rassoc unfolding shift_pow by blast
    show "t' \<le>s w"
      unfolding \<open>w = r' \<cdot> v \<cdot> t'\<close> lassoc by blast
  qed
  have t_drop: "(q \<cdot> p)\<^sup>@e = drop (\<^bold>|t'\<^bold>| - ?d) t'"
    using \<open>\<^bold>|(p \<cdot> q)\<^sup>@e\<^bold>| = ?d\<close>[unfolded swap_e, symmetric] \<open>(q \<cdot> p)\<^sup>@e \<le>s t'\<close>[unfolded suf_drop_conv, symmetric]
    by argo
  define k where "k = (e * (\<^bold>|t'\<^bold>| div gcd \<^bold>|r'\<^bold>| \<^bold>|t'\<^bold>|))"
  have "(q \<cdot> p)\<^sup>@k = t'"
    using per_div[reversed, OF gcd_dvd2, OF periodI[reversed], OF \<open>t' \<le>s  t' \<cdot> (q \<cdot> p)\<^sup>@e\<close>[unfolded t_drop]]
    unfolding t_drop[symmetric] pow_mult[symmetric] k_def.
  have "m + k \<le> l"
    unfolding linorder_not_less[symmetric]
  proof (rule notI)
    assume "l < m + k"
    hence "l + 1 \<le> m + k"
      by force
    from trans_le_add1[OF mult_le_mono1[OF this]]
    have "(l + 1)* \<^bold>|p \<cdot> q\<^bold>| \<le> (m + k) * \<^bold>|p\<cdot>q\<^bold>| + \<^bold>|v\<^bold>|".
    with lenarg[OF \<open>w = r' \<cdot> v \<cdot> t'\<close>[folded \<open>(p \<cdot> q)\<^sup>@l \<cdot> p = w\<close>, folded \<open>(q \<cdot> p)\<^sup>@k = t'\<close> \<open>(p \<cdot> q)\<^sup>@m = r'\<close>],
        unfolded lenmorph, unfolded pow_len add.assoc[symmetric], symmetric]
    show False
      unfolding distrib_right add.commute[of _ "\<^bold>|v\<^bold>|"] lenmorph
      unfolding distrib_left using nemp_len[OF \<open>q \<noteq> \<epsilon>\<close>] by linarith
  qed
  then obtain i where "l = m + i + k"
    by (metis add.assoc add.commute le_Suc_ex)

  have "v = (p \<cdot> q)\<^sup>@i \<cdot> p"
    using \<open>w = r' \<cdot> v \<cdot> t'\<close>
    unfolding \<open>(p \<cdot> q)\<^sup>@l \<cdot> p = w\<close>[symmetric] \<open>(q \<cdot> p)\<^sup>@k = t'\<close>[symmetric] \<open>(p \<cdot> q)\<^sup>@m = r'\<close>[symmetric] \<open>l = m + i + k\<close> pow_add
              rassoc cancel cancel_right
    unfolding lassoc shift_pow cancel_right by simp

  have "r = (p \<cdot> q)\<^sup>@(m + k)"
    using \<open>w = r \<cdot> v\<close> unfolding \<open>(p \<cdot> q)\<^sup>@l \<cdot> p = w\<close>[symmetric] \<open>v = (p \<cdot> q)\<^sup>@i \<cdot> p\<close> \<open>l = m + i + k\<close>
    unfolding lassoc cancel_right add.commute[of _ k] add.assoc[symmetric] pow_add by simp

  have "t = (q \<cdot> p)\<^sup>@(m + k)"
    using \<open>w = v \<cdot> t\<close> unfolding \<open>(p \<cdot> q)\<^sup>@l \<cdot> p = w\<close>[symmetric] \<open>v = (p \<cdot> q)\<^sup>@i \<cdot> p\<close> \<open>l = m + i + k\<close>
    unfolding rassoc cancel add.commute[of m] add.assoc[symmetric] pow_add
    unfolding shift_pow unfolding lassoc shift_pow unfolding rassoc cancel
    unfolding pows_comm by simp

  have "0 < m"
    using \<open>(p \<cdot> q)\<^sup>@m = r'\<close> \<open>r' \<noteq> \<epsilon>\<close> by blast

  have "0 < k"
    using \<open>(q \<cdot> p)\<^sup>@k = t'\<close> \<open>t' \<noteq> \<epsilon>\<close> by blast
  thm that
  from that[OF \<open>t = (q \<cdot> p)\<^sup>@(m + k)\<close> \<open>r = (p \<cdot> q)\<^sup>@(m + k)\<close> \<open>(q \<cdot> p)\<^sup>@k = t'\<close>[symmetric] \<open>(p \<cdot> q)\<^sup>@m = r'\<close>[symmetric] \<open>v = (p \<cdot> q)\<^sup>@i \<cdot> p\<close>
       \<open>(p \<cdot> q)\<^sup>@l \<cdot> p = w\<close>[symmetric, unfolded \<open>l = m + i + k\<close>] \<open>primitive (p \<cdot> q)\<close> \<open>q \<noteq> \<epsilon>\<close> \<open>0 < m\<close> \<open>0 < k\<close>]
  show thesis.
qed



lemma three_covers_pref_suf_pow: assumes "x \<cdot> y \<le>p w" and "y \<cdot> x \<le>s w" and "w \<le>f y\<^sup>@k" and  "\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|"
  shows "x \<cdot> y =  y \<cdot> x"
  using fac_marker_suf[OF fac_trans[OF pref_fac[OF \<open>x \<cdot> y \<le>p w\<close>] \<open>w \<le>f y\<^sup>@k\<close>]]
    fac_marker_pref[OF fac_trans[OF suf_fac[OF \<open>y \<cdot> x \<le>s w\<close>] \<open>w \<le>f y\<^sup>@k\<close>]]
    root_suf_comm'[OF _ suf_prod_long, OF _ _ \<open>\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|\<close>, of x] by presburger

subsection \<open>Binary Equality Words\<close>


\<comment> \<open>translation of a combinatorial lemma into the language of "something is not BEW"\<close>

definition binary_equality_generator :: "binA list \<Rightarrow> bool" where
  "binary_equality_generator w \<equiv> (set w = UNIV) \<and> (\<exists> (g :: binA list \<Rightarrow> nat list) h. binary_code_morphism g \<and> binary_code_morphism h \<and> g \<noteq> h \<and> w \<in> g =\<^sub>M h)"

definition canonical_binary_equality_generator :: "binA list \<Rightarrow> bool" where
  "canonical_binary_equality_generator w = (\<exists> (g :: binA list \<Rightarrow> nat list) h. binary_code_morphism g \<and> binary_code_morphism h \<and> w \<in> g =\<^sub>M h \<and> \<^bold>|h \<aa>\<^bold>| < \<^bold>|g \<aa>\<^bold>| \<and> \<^bold>|g \<bb>\<^bold>| < \<^bold>|h \<bb>\<^bold>| \<and> \<^bold>|g \<aa>\<^bold>| \<le> \<^bold>|h \<bb>\<^bold>|)"

lemma begE: assumes "binary_equality_generator w"
  obtains g h where "binary_code_morphism (g :: binA list \<Rightarrow> nat list)" and "binary_code_morphism h" and "g \<noteq> h" and "w \<in> g =\<^sub>M h" and "set w = UNIV"
  using assms binary_equality_generator_def by auto

lemma cbegE: assumes "canonical_binary_equality_generator w"
  obtains g h where "binary_code_morphism (g :: binA list \<Rightarrow> nat list)" and "binary_code_morphism h" and "w \<in> g =\<^sub>M h" and "\<^bold>|h \<aa>\<^bold>| < \<^bold>|g \<aa>\<^bold>|" and "\<^bold>|g \<bb>\<^bold>| < \<^bold>|h \<bb>\<^bold>|" and "\<^bold>|g \<aa>\<^bold>| \<le> \<^bold>|h \<bb>\<^bold>|"
  using assms canonical_binary_equality_generator_def by auto

lemma cbeg_is_beg: assumes "canonical_binary_equality_generator w" shows "binary_equality_generator w"
proof-
  from cbegE[OF assms]
  obtain g h where gh:  "binary_code_morphism (g :: binA list \<Rightarrow> nat list)" "binary_code_morphism h" "w \<in> g =\<^sub>M h" and "\<^bold>|h \<aa>\<^bold>| < \<^bold>|g \<aa>\<^bold>|" "\<^bold>|g \<bb>\<^bold>| < \<^bold>|h \<bb>\<^bold>|" "\<^bold>|g \<aa>\<^bold>| \<le> \<^bold>|h \<bb>\<^bold>|".
  interpret g: binary_code_morphism g
    by fact
  interpret h: binary_code_morphism h
    by fact
  interpret two_binary_morphisms g h
    using two_binary_morphisms_def two_morphisms_def g.morphism_axioms h.morphism_axioms by blast
  have "g \<noteq> h"
    using \<open>\<^bold>|h \<aa>\<^bold>| < \<^bold>|g \<aa>\<^bold>|\<close> by blast
  have "set w = UNIV"
    using \<open>\<^bold>|h \<aa>\<^bold>| < \<^bold>|g \<aa>\<^bold>|\<close> \<open>\<^bold>|g \<bb>\<^bold>| < \<^bold>|h \<bb>\<^bold>|\<close> solution_UNIV[OF min_solD'[OF \<open>w \<in> g =\<^sub>M h\<close>] min_solD[OF \<open>w \<in> g =\<^sub>M h\<close>] bin_induct[of "\<lambda> c. g[c] \<noteq> h[c]"]] by force
  then show "binary_equality_generator w"
    unfolding binary_equality_generator_def using gh \<open>g \<noteq> h\<close> by blast
qed

lemma beg_productE: assumes "binary_equality_generator (u\<cdot>v)" and "u \<noteq> \<epsilon>" and "v \<noteq> \<epsilon>"
  obtains g h where "binary_code_morphism (g :: binA list \<Rightarrow> nat list)" and "binary_code_morphism h" and "g \<noteq> h" and " (u\<cdot>v) \<in> g =\<^sub>M h" and "\<^bold>|g u\<^bold>| < \<^bold>|h u\<^bold>|" and "\<^bold>|h v\<^bold>| < \<^bold>|g v\<^bold>|"
proof-
  from begE[OF assms(1)]
  obtain g h where gh: "binary_code_morphism (g :: binA list \<Rightarrow> nat list)" "binary_code_morphism h" "g \<noteq> h" "(u \<cdot> v) \<in> g =\<^sub>M h".
  interpret g: binary_code_morphism g
    by fact
  interpret h: binary_code_morphism h
    by fact
  have "\<^bold>|g u\<^bold>| \<noteq> \<^bold>|h u\<^bold>|"
    using  min_solD_min[OF \<open>(u \<cdot> v) \<in> g =\<^sub>M h\<close> \<open>u \<noteq> \<epsilon>\<close> triv_pref] \<open>v \<noteq> \<epsilon>\<close> eqd_eq(1)[OF min_solD[OF \<open>(u \<cdot> v) \<in> g =\<^sub>M h\<close>, unfolded g.morph h.morph]] by blast
  let ?g = "if \<^bold>|g u\<^bold>| \<le> \<^bold>|h u\<^bold>| then g else h"
  let ?h = "if \<^bold>|g u\<^bold>| \<le> \<^bold>|h u\<^bold>| then h else g"
  have "?g \<noteq> ?h" "binary_code_morphism ?g" "binary_code_morphism ?h" "(u\<cdot>v) \<in> ?g =\<^sub>M ?h"
    using gh by (simp_all add: min_sol_sym)
  interpret g': binary_code_morphism ?g
    by fact
  interpret h': binary_code_morphism ?h
    by fact
  have "\<^bold>|?g u\<^bold>| < \<^bold>|?h u\<^bold>|"
    using \<open>\<^bold>|g u\<^bold>| \<noteq> \<^bold>|h u\<^bold>|\<close> by simp
  with  lenarg[OF min_solD[OF \<open>(u \<cdot> v) \<in> ?g =\<^sub>M ?h\<close>, unfolded g'.morph h'.morph]]
  have "\<^bold>|?h v\<^bold>| < \<^bold>|?g v\<^bold>|"
    unfolding lenmorph by linarith
  show thesis
    by (rule that[of ?g ?h]) fact+
qed

lemma bew_baiba_eq': assumes  "\<^bold>|y\<^bold>| < \<^bold>|v\<^bold>|" and  "x \<le>s y" and "u \<le>s v" and
  "y \<cdot> x \<^sup>@ k \<cdot> y = v \<cdot> u \<^sup>@ k \<cdot> v"
shows "commutes {x,y,u,v}"
proof-
  obtain p where "y\<cdot>p = v"
    using eqdE[OF \<open>y \<cdot> x \<^sup>@ k \<cdot> y = v \<cdot> u \<^sup>@ k \<cdot> v\<close> less_imp_le[OF \<open>\<^bold>|y\<^bold>| < \<^bold>|v\<^bold>|\<close>]] by blast
  have "\<^bold>|u \<^sup>@ k \<cdot> v\<^bold>| \<le> \<^bold>|x \<^sup>@ k \<cdot> y\<^bold>|"
    using lenarg[OF \<open>y \<cdot> x \<^sup>@ k \<cdot> y = v \<cdot> u \<^sup>@ k \<cdot> v\<close>] \<open>\<^bold>|y\<^bold>| < \<^bold>|v\<^bold>|\<close> unfolding lenmorph
    by linarith
  obtain s where "s\<cdot>y = v"
    using eqdE[reversed, OF \<open>y \<cdot> x \<^sup>@ k \<cdot> y = v \<cdot> u \<^sup>@ k \<cdot> v\<close>[unfolded lassoc] less_imp_le[OF \<open>\<^bold>|y\<^bold>| < \<^bold>|v\<^bold>|\<close>]].

  have "s \<noteq> \<epsilon>"
    using \<open>\<^bold>|y\<^bold>| < \<^bold>|v\<^bold>|\<close> \<open>s \<cdot> y = v\<close> by force
  have "p \<noteq> \<epsilon>"
    using \<open>\<^bold>|y\<^bold>| < \<^bold>|v\<^bold>|\<close> \<open>y \<cdot> p = v\<close> by force

  have "s \<cdot> y = y \<cdot> p"
    by (simp add: \<open>s \<cdot> y = v\<close> \<open>y \<cdot> p = v\<close>)
  obtain w w' q t where p_def: "p = (w'\<cdot>w)\<^sup>@q" and s_def: "s = (w\<cdot>w')\<^sup>@q"
    and y_def: "y = (w\<cdot>w')\<^sup>@t\<cdot>w" and "w' \<noteq> \<epsilon>" and "primitive (w\<cdot>w')" and \<open>0 < q\<close>
    using conjug_eq_primrootE[OF \<open>s \<cdot> y = y \<cdot> p\<close> \<open>s \<noteq> \<epsilon>\<close>, of thesis]
    by blast
  have "primitive (w'\<cdot>w)"
    using \<open>primitive (w \<cdot> w')\<close> prim_conjug by auto

  have "y \<cdot> x \<^sup>@ k \<cdot> y = y\<cdot> p \<cdot> u \<^sup>@ k \<cdot> s \<cdot> y"
    using \<open>s \<cdot> y = v\<close> \<open>y \<cdot> p = v\<close> \<open>y \<cdot> x \<^sup>@ k \<cdot> y = v \<cdot> u \<^sup>@ k \<cdot> v\<close> by auto
  hence "x\<^sup>@k = p\<cdot>u\<^sup>@k\<cdot>s"
    by auto
  hence "x \<noteq> \<epsilon>"
    using \<open>p \<noteq> \<epsilon>\<close> by force

  have "w\<cdot>w' \<le>s x\<^sup>@k"
    using \<open>x \<^sup>@ k = p \<cdot> u \<^sup>@ k \<cdot> s\<close>[unfolded s_def]
    unfolding pow_pos2[OF \<open>0 < q\<close>]
    using sufI[of "p \<cdot> u \<^sup>@ k \<cdot> (w \<cdot> w') \<^sup>@ (q - 1)" "w \<cdot> w'" "x\<^sup>@k", unfolded rassoc]
    by argo

  have "\<^bold>|w\<cdot>w'\<^bold>| \<le> \<^bold>|x\<^bold>|"
  proof(intro leI notI)
    assume "\<^bold>|x\<^bold>| < \<^bold>|w \<cdot> w'\<^bold>|"
    have "x \<le>s (w\<cdot>w')\<cdot>y"
      using  \<open>x \<le>s y\<close>  by (auto simp add: suffix_def)
    have "(w'\<cdot>w) \<le>s (w\<cdot>w')\<cdot>y"
      unfolding \<open>y = (w\<cdot>w')\<^sup>@t\<cdot>w\<close> lassoc pow_comm[symmetric] suf_cancel_conv
      by blast

    from ruler_le[reversed, OF \<open>x \<le>s (w\<cdot>w')\<cdot>y\<close> this
        less_imp_le[OF \<open>\<^bold>|x\<^bold>| < \<^bold>|w \<cdot> w'\<^bold>|\<close>[unfolded swap_len]]]
    have "x \<le>s w'\<cdot> w".
    hence "x \<le>s p"
      unfolding p_def pow_pos2[OF \<open>0 < q\<close>] suffix_append by blast
    from root_suf_comm[OF _ suf_ext[OF this]]
    have "x\<cdot>p = p\<cdot>x"
      using pref_pow_root[OF prefI[OF \<open>x \<^sup>@ k = p \<cdot> u \<^sup>@ k \<cdot> s\<close>[symmetric]]] by blast
    from  comm_drop_exp[OF _ this[unfolded \<open>p = (w' \<cdot> w) \<^sup>@ q\<close>]]
    have "x \<cdot> (w' \<cdot> w) = (w' \<cdot> w) \<cdot> x"
      using \<open>0 < q\<close> by force
    from prim_comm_short_emp[OF \<open>primitive (w'\<cdot>w)\<close> this \<open>\<^bold>|x\<^bold>| < \<^bold>|w\<cdot>w'\<^bold>|\<close>[unfolded swap_len]]
    show False
      using \<open>x \<noteq> \<epsilon>\<close> by blast
  qed

  hence "w\<cdot>w' \<le>s x"
    using  suf_prod_le[OF suf_prod_root[OF \<open>w \<cdot> w' \<le>s x \<^sup>@ k\<close>]] by blast
  from suffix_order.trans[OF this \<open>x \<le>s y\<close>]
  have "w \<cdot> w' \<le>s y".
  hence "\<^bold>|w \<cdot> w'\<^bold>| \<le> \<^bold>|y\<^bold>|"
    using suffix_length_le by blast
  then obtain t' where  "t = Suc t'"
    unfolding  y_def lenmorph pow_len \<open>w' \<noteq> \<epsilon>\<close> add.commute[of _ "\<^bold>|w\<^bold>|"] nat_add_left_cancel_le
    using \<open>w' \<noteq> \<epsilon>\<close> mult_0[of "\<^bold>|w\<^bold>| + \<^bold>|w'\<^bold>|"] npos_len[of w'] not0_implies_Suc[of t] by force
  from ruler_eq_len[reversed, OF \<open>w \<cdot> w' \<le>s y\<close> _ swap_len, unfolded y_def this pow_Suc2 rassoc]
  have "w \<cdot> w' = w'\<cdot> w"
    unfolding lassoc suf_cancel_conv by blast
  from comm_not_prim[OF _ \<open>w' \<noteq> \<epsilon>\<close> this]
  have "w = \<epsilon>"
    using  \<open>primitive (w \<cdot> w')\<close> by blast
  hence "primitive w'"
    using \<open>primitive (w' \<cdot> w)\<close> by auto

  have "0 < k"
    using \<open>\<^bold>|y\<^bold>| < \<^bold>|v\<^bold>|\<close> lenarg[OF \<open>y \<cdot> x \<^sup>@ k \<cdot> y = v \<cdot> u \<^sup>@ k \<cdot> v\<close>, unfolded lenmorph pow_len]
    by (intro gr_zeroI) force

  have "y = w'\<^sup>@t"
    using y_def \<open>w = \<epsilon>\<close>  by force
  hence "y\<in> \<langle>{w'}\<rangle>"
    by blast

  have "s \<in> \<langle>{w'}\<rangle>"
    using s_def \<open>w = \<epsilon>\<close> by blast
  hence "v \<in> \<langle>{w'}\<rangle>"
    using \<open>s \<cdot> y = v\<close>  \<open>y \<in> \<langle>{w'}\<rangle>\<close>  by blast
  have "w' \<le>p x"
    using \<open>x\<^sup>@k = p\<cdot>u\<^sup>@k\<cdot>s\<close>[symmetric] eq_le_pref[OF _ \<open>\<^bold>|w\<cdot>w'\<^bold>| \<le> \<^bold>|x\<^bold>|\<close>, of "w' \<^sup>@ (q -1) \<cdot> u \<cdot> u \<^sup>@ (k - 1) \<cdot> s" "x \<^sup>@ (k - 1)"]
    unfolding p_def \<open>w = \<epsilon>\<close> emp_simps pow_pos[OF \<open>0 < k\<close>] pow_pos[OF \<open>0 < q\<close>]  pow_pos rassoc by argo

  have "x \<cdot> w' = w' \<cdot> x"
    using  \<open>x \<le>s y\<close> \<open>w' \<le>p x\<close> unfolding   y_def[unfolded \<open>w = \<epsilon>\<close> \<open>t = Suc t'\<close> emp_simps]
    using suf_prod_root[THEN suf_root_pref_comm] by meson
  from prim_comm_exp[OF \<open>primitive w'\<close> this]
  have "x \<in> \<langle>{w'}\<rangle>"
    unfolding sing_gen_pow_ex_conv by blast


  have "p \<in> \<langle>{w'}\<rangle>"
    using \<open>s \<in> \<langle>{w'}\<rangle>\<close> \<open>y \<in> \<langle>{w'}\<rangle>\<close> \<open>s \<cdot> y = v\<close>[folded \<open>y \<cdot> p = v\<close>] \<open>w \<cdot> w' = w' \<cdot> w\<close>
    unfolding p_def s_def by argo

  have "v \<cdot> u\<^sup>@k \<cdot> v \<in> \<langle>{w'}\<rangle>"
    unfolding \<open>y \<cdot> x \<^sup>@ k \<cdot> y = v \<cdot> u \<^sup>@ k \<cdot> v\<close>[symmetric]
    using \<open>y \<in> \<langle>{w'}\<rangle>\<close>  \<open>v \<in> \<langle>{w'}\<rangle>\<close> hull_closed power_in[OF \<open>x \<in> \<langle>{w'}\<rangle>\<close>] by meson
  have "u\<^sup>@k \<in> \<langle>{w'}\<rangle>"
    using sing_gen_pref_cancel[OF \<open>v \<cdot> u\<^sup>@k \<cdot> v \<in> \<langle>{w'}\<rangle>\<close> \<open>v \<in> \<langle>{w'}\<rangle>\<close>] sing_gen_suf_cancel[OF _ \<open>v \<in> \<langle>{w'}\<rangle>\<close>] by blast

  from prim_root_drop_exp[OF this \<open>0 < k\<close> \<open>primitive w'\<close>]
  have "u \<in> \<langle>{w'}\<rangle>".

  have "\<forall>x\<in>{x,y,u,v}. x \<in> \<langle>{w'}\<rangle>"
    using \<open>x \<in> \<langle>{w'}\<rangle>\<close> \<open>y \<in> \<langle>{w'}\<rangle>\<close> \<open>u \<in> \<langle>{w'}\<rangle>\<close> \<open>v \<in> \<langle>{w'}\<rangle>\<close> by blast
  then show "commutes {x,y,u,v}"
    using commutesI_ex_root by auto
qed

lemma bew_baiba_eq: assumes  "y \<cdot> x \<noteq> v \<cdot> u" and
  "y \<cdot> x \<^sup>@ (k+1) \<cdot> y \<cdot> x = v \<cdot> u \<^sup>@ (k+1) \<cdot> v \<cdot> u"
shows "commutes {x,y,u,v}"
proof-
  have eq':"(y \<cdot> x) \<cdot> x \<^sup>@ k \<cdot> y \<cdot> x = (v \<cdot> u)\<cdot> u \<^sup>@ k \<cdot> v \<cdot> u" and
       eq: "(y \<cdot> x \<^sup>@ (k+1)) \<cdot> y \<cdot> x = (v \<cdot> u \<^sup>@ (k+1)) \<cdot> v \<cdot> u" and
       perm: "{u, v \<cdot> u, x, y \<cdot> x} = {x, y \<cdot> x, u, v \<cdot> u}"
    using assms(2) unfolding rassoc by (simp_all add: insert_commute)
  from eqd_eq(1)[reversed,OF eq]
  have "\<^bold>|y \<cdot> x\<^bold>| \<noteq> \<^bold>|v \<cdot> u\<^bold>|"
    using assms(1) by blast
  hence "commutes {x, y \<cdot> x, u, v \<cdot> u}"
     using bew_baiba_eq'[OF _ triv_suf triv_suf eq']
     bew_baiba_eq'[OF _ triv_suf triv_suf eq'[symmetric], unfolded perm] by linarith
  from commutes_root[OF this]
  obtain t where roots: "\<And> z. z \<in>{x, y \<cdot> x, u, v \<cdot> u} \<Longrightarrow> z \<in> \<langle>{t}\<rangle>"
    by blast
  have "y \<in> \<langle>{t}\<rangle>"
    using roots[of x] roots[of "y\<cdot>x"] by force
  have "v \<in> \<langle>{t}\<rangle>"
    using roots[of u] roots[of "v\<cdot>u"] by force
  have "\<forall> z \<in> {x, y, u, v}. z \<in> \<langle>{t}\<rangle>"
    using  roots[of u] roots[of x] \<open>v \<in> \<langle>{t}\<rangle>\<close>  \<open>y \<in> \<langle>{t}\<rangle>\<close> by blast
  thus "commutes {x,y,u,v}"
    using commutesI_ex_root[of "{x, y \<cdot> x, u, v \<cdot> u}"] by auto
qed

lemmas less_mult_le [intro] = mult_le_mono1[OF Suc_leI, unfolded mult_Suc]
lemma less_mult_le' [intro]: "m < (k::nat) \<Longrightarrow> m*r + r \<le> k*r"
  by (simp add: add.commute less_mult_le)

lemma bew_baibaib_eq_aux: assumes "\<^bold>|x\<^bold>| < \<^bold>|u\<^bold>|" and "1 < i" and
 eq: "x \<cdot> y\<^sup>@i\<cdot> x \<cdot> y\<^sup>@i \<cdot> x = u \<cdot> v\<^sup>@i\<cdot> u \<cdot> v\<^sup>@i \<cdot> u"
shows "commutes {x,y,u,v}"
proof-
  from lenarg[OF \<open>x \<cdot> y\<^sup>@i\<cdot> x \<cdot> y\<^sup>@i \<cdot> x = u \<cdot> v\<^sup>@i\<cdot> u \<cdot> v\<^sup>@i \<cdot> u\<close>]
  have "\<^bold>|u \<cdot> v\<^sup>@i\<^bold>| < \<^bold>|x \<cdot> y\<^sup>@i\<^bold>|"
    using \<open>\<^bold>|x\<^bold>| < \<^bold>|u\<^bold>|\<close> by fastforce
  have "0 < i"
    using \<open>1 < i\<close> by force

  have "(x\<cdot>y\<^sup>@i) \<cdot> (u\<cdot>v\<^sup>@i) = (u\<cdot>v\<^sup>@i) \<cdot> (x\<cdot>y\<^sup>@i)"
  proof (rule two_pers)
    show "x \<cdot> y\<^sup>@i\<cdot> x \<cdot> y\<^sup>@i \<cdot> x \<le>p (u \<cdot> v \<^sup>@ i) \<cdot> (x \<cdot> y\<^sup>@i\<cdot> x \<cdot> y\<^sup>@i \<cdot> x)"
      unfolding eq rassoc pref_cancel_conv by blast
    show "x \<cdot> y\<^sup>@i\<cdot> x \<cdot> y\<^sup>@i \<cdot> x \<le>p (x \<cdot> y \<^sup>@ i) \<cdot> x \<cdot> y\<^sup>@i\<cdot> x \<cdot> y\<^sup>@i \<cdot> x"
      unfolding rassoc pref_cancel_conv by blast
    show "\<^bold>|x \<cdot> y \<^sup>@ i\<^bold>| + \<^bold>|u \<cdot> v \<^sup>@ i\<^bold>| \<le> \<^bold>|x \<cdot> y \<^sup>@ i \<cdot> x \<cdot> y \<^sup>@ i \<cdot> x\<^bold>|"
      using \<open>\<^bold>|u \<cdot> v\<^sup>@i\<^bold>| < \<^bold>|x \<cdot> y\<^sup>@i\<^bold>|\<close> unfolding lenmorph by auto
  qed

  from comm_primrootE'[OF this]
  obtain r m k where "x\<cdot>y\<^sup>@i = r\<^sup>@k" "u\<cdot>v\<^sup>@i = r\<^sup>@m"  "primitive r".
  note prim_nemp[OF \<open>primitive r\<close>]

  have "\<^bold>|y\<^bold>| + \<^bold>|r\<^bold>| \<le> \<^bold>|y \<^sup>@ i\<^bold>|"
  proof-
    have "\<^bold>|u \<cdot> v \<^sup>@ i \<cdot> u \<cdot> v \<^sup>@ i\<^bold>| \<le> \<^bold>|x \<cdot> y \<^sup>@ i \<cdot> x \<cdot> y \<^sup>@ i\<^bold>|" "\<^bold>|v \<^sup>@ i \<cdot> u\<^bold>| \<le> \<^bold>|y \<^sup>@ i \<cdot> x\<^bold>|"
      using \<open>\<^bold>|u \<cdot> v \<^sup>@ i\<^bold>| < \<^bold>|x \<cdot> y \<^sup>@ i\<^bold>|\<close> unfolding lenmorph by linarith+
    from eqdE[of  "u \<cdot> v\<^sup>@i \<cdot> u \<cdot> v\<^sup>@i" u "x \<cdot> y\<^sup>@i \<cdot> x \<cdot> y\<^sup>@i" "x",
        unfolded rassoc, OF eq[symmetric] this(1)]
    obtain t' where t': "u \<cdot> v \<^sup>@ i \<cdot> u \<cdot> v \<^sup>@ i \<cdot> t' = x \<cdot> y \<^sup>@ i \<cdot> x \<cdot> y \<^sup>@ i" "t' \<cdot> x = u".
    from eqdE[reversed, of "u \<cdot> v\<^sup>@i \<cdot> u" "v\<^sup>@i \<cdot> u" "x \<cdot> y\<^sup>@i \<cdot> x" "y\<^sup>@i\<cdot>x",
        unfolded rassoc, OF eq[symmetric] \<open>\<^bold>|v \<^sup>@ i \<cdot> u\<^bold>| \<le> \<^bold>|y \<^sup>@ i \<cdot> x\<^bold>|\<close>]
    obtain t where t: "t \<cdot> v \<^sup>@ i \<cdot> u = y \<^sup>@ i \<cdot> x" "x \<cdot> y \<^sup>@ i \<cdot> x \<cdot> t = u \<cdot> v \<^sup>@ i \<cdot> u".
    have "(x \<cdot> y \<^sup>@ i \<cdot> x \<cdot> t) \<cdot> (v \<^sup>@ i \<cdot> t' \<cdot> x) = x \<cdot> y \<^sup>@ i \<cdot> x \<cdot> y \<^sup>@ i \<cdot> x"
      unfolding t' t rassoc eq..
    hence "y\<^sup>@i = t\<cdot>v\<^sup>@i\<cdot>t'"
      by force

    have "m < k"
      using \<open>\<^bold>|u \<cdot> v \<^sup>@ i\<^bold>| < \<^bold>|x \<cdot> y \<^sup>@ i\<^bold>|\<close>
      unfolding \<open>u \<cdot> v \<^sup>@ i = r \<^sup>@ m\<close> \<open>x \<cdot> y \<^sup>@ i = r \<^sup>@ k\<close> pow_len
      by simp
    hence "\<^bold>|u \<cdot> v \<^sup>@ i\<^bold>| + \<^bold>|r\<^bold>| \<le> \<^bold>|x \<cdot> y \<^sup>@ i\<^bold>|"
      unfolding \<open>u \<cdot> v \<^sup>@ i = r \<^sup>@ m\<close> \<open>x \<cdot> y \<^sup>@ i = r \<^sup>@ k\<close> pow_len by blast
    hence "2*\<^bold>|r\<^bold>| \<le> \<^bold>|y\<^sup>@i\<^bold>|"
      using \<open>\<^bold>|u \<cdot> v \<^sup>@ i\<^bold>| + \<^bold>|r\<^bold>| \<le> \<^bold>|x \<cdot> y \<^sup>@ i\<^bold>|\<close> lenarg[OF t'(1)]
      unfolding lenarg[OF \<open>y\<^sup>@i = t\<cdot>v\<^sup>@i\<cdot>t'\<close>] lenmorph by force
    thus ?thesis
      using mult_le_mono1[OF Suc_leI[OF \<open>1 < i\<close>], of "\<^bold>|y\<^bold>|"]
      unfolding pow_len mult_Suc by force
  qed

  have "r \<cdot> y = y \<cdot> r"
  proof (rule two_pers[reversed])
  show "y\<^sup>@i \<le>s y\<^sup>@i\<cdot>r"
    using triv_suf[of "y \<^sup>@ i" x, unfolded \<open>x \<cdot> y \<^sup>@ i = r \<^sup>@ k\<close>, THEN suf_prod_root].
  show "y\<^sup>@i \<le>s y\<^sup>@i\<cdot>y"
    by (simp add: suf_pow_ext')
  qed fact
  note comm_pow_comm[OF this[symmetric], of i, symmetric]

  have "r \<cdot> x = x \<cdot> r"
  proof (rule comm_cancel_suf)
    show "r \<cdot> x \<cdot> y\<^sup>@i = x \<cdot> y\<^sup>@i \<cdot> r"
      using \<open>x\<cdot>y\<^sup>@i = r\<^sup>@k\<close>
      by (simp add: lassoc pow_comm)
    show "r \<cdot> y \<^sup>@ i = y \<^sup>@ i \<cdot> r"
      by fact
  qed

  have "r \<cdot> u = u \<cdot> r"
  proof (rule comm_cancel_pref)
    show "r \<cdot> ((u \<cdot> v\<^sup>@i) \<cdot> (u \<cdot> v\<^sup>@i)) = ((u \<cdot> v\<^sup>@i) \<cdot> (u \<cdot> v\<^sup>@i)) \<cdot> r"
      unfolding \<open>u\<cdot>v\<^sup>@i = r\<^sup>@m\<close> by comparison
    have comm_aux: "r \<cdot> (u \<cdot> v \<^sup>@ i \<cdot> u \<cdot> v \<^sup>@ i \<cdot> u) = (u \<cdot> v \<^sup>@ i \<cdot> u \<cdot> v \<^sup>@ i \<cdot> u) \<cdot> r"
      unfolding eq[symmetric]
      using \<open>x\<cdot>y\<^sup>@i = r\<^sup>@k\<close> \<open>r \<cdot> x = x \<cdot> r\<close> \<open>r \<cdot> y \<^sup>@ i = y \<^sup>@ i \<cdot> r\<close> rassoc by metis
    show "r \<cdot> ((u \<cdot> v \<^sup>@ i) \<cdot> u \<cdot> v \<^sup>@ i) \<cdot> u = ((u \<cdot> v \<^sup>@ i) \<cdot> u \<cdot> v \<^sup>@ i) \<cdot> u \<cdot> r"
      using comm_aux unfolding rassoc.
  qed

  have "r \<cdot> v = v \<cdot> r"
  proof(rule comm_drop_exp[OF \<open>0 < i\<close>, symmetric])
    show "r \<cdot> v\<^sup>@i = v\<^sup>@i \<cdot> r"
    proof (rule comm_cancel_pref)
      show "r \<cdot> u \<cdot> v\<^sup>@i = u \<cdot> v\<^sup>@i \<cdot> r"
        using \<open>u\<cdot>v\<^sup>@i = r\<^sup>@m\<close> pow_comm rassoc by metis
    qed fact
  qed

  show "commutes {x,y,u,v}"
    by (rule commutesI'[OF \<open>r \<noteq> \<epsilon>\<close>])
    (auto simp: \<open>r \<cdot> u = u \<cdot> r\<close> \<open>r \<cdot> v = v \<cdot> r\<close> \<open>r \<cdot> x = x \<cdot> r\<close> \<open>r \<cdot> y = y \<cdot> r\<close>)
qed

lemma bew_baibaib_eq: assumes "1 < i" and "x \<noteq> u" and
 eq: "x \<cdot> y\<^sup>@i\<cdot> x \<cdot> y\<^sup>@i \<cdot> x = u \<cdot> v\<^sup>@i\<cdot> u \<cdot> v\<^sup>@i \<cdot> u"
shows "commutes {x,y,u,v}"
proof (rule linorder_cases[of "\<^bold>|x\<^bold>|" "\<^bold>|u\<^bold>|"])
  assume "\<^bold>|x\<^bold>| < \<^bold>|u\<^bold>|"
  from bew_baibaib_eq_aux[OF this assms(1,3)]
  show "commutes {x,y,u,v}".
next
  assume "\<^bold>|u\<^bold>| < \<^bold>|x\<^bold>|"
  from bew_baibaib_eq_aux[OF this \<open>1 < i\<close> eq[symmetric]]
  show "commutes {x,y,u,v}"
    by (simp add: insert_commute)
qed (use eqd_eq(1)[OF eq] \<open>x \<noteq> u\<close> in blast)

theorem not_beg_abiab: "\<not> binary_equality_generator (\<aa> \<cdot> \<bb>\<^sup>@(i+1) \<cdot> \<aa> \<cdot> \<bb>)"
proof
  have nemp: "\<aa> \<cdot> \<bb> \<^sup>@ (i + 1) \<noteq> \<epsilon>" "\<aa> \<cdot> \<bb> \<noteq> \<epsilon>"
    by simp_all
  assume "binary_equality_generator (\<aa> \<cdot> \<bb> \<^sup>@ (i+1) \<cdot> \<aa> \<cdot> \<bb>)"
  from beg_productE[of "\<aa> \<cdot> \<bb>\<^sup>@(i+1)" "\<aa> \<cdot> \<bb>", unfolded rassoc, OF this nemp]
   obtain g h where "binary_code_morphism (g :: binA list \<Rightarrow> nat list)" "binary_code_morphism h" "g \<noteq> h" "(\<aa> \<cdot> \<bb> \<^sup>@ (i + 1) \<cdot> \<aa> \<cdot> \<bb>) \<in> g =\<^sub>M h" "\<^bold>|g (\<aa> \<cdot> \<bb> \<^sup>@ (i + 1))\<^bold>| < \<^bold>|h (\<aa> \<cdot> \<bb> \<^sup>@ (i + 1))\<^bold>|" "\<^bold>|h (\<aa> \<cdot> \<bb>)\<^bold>| < \<^bold>|g (\<aa> \<cdot> \<bb>)\<^bold>|".
  interpret g: binary_code_morphism g
    by fact
  interpret h: binary_code_morphism h
    by fact
  have " g \<aa> \<cdot> g \<bb> \<noteq> h \<aa> \<cdot> h \<bb>"
    using \<open>\<^bold>|h (\<aa> \<cdot> \<bb>)\<^bold>| < \<^bold>|g (\<aa> \<cdot> \<bb>)\<^bold>|\<close> unfolding g.morph h.morph by fastforce
  from bew_baiba_eq[OF this]  min_solD[OF \<open>(\<aa> \<cdot> \<bb> \<^sup>@ (i + 1) \<cdot> \<aa> \<cdot> \<bb>) \<in> g =\<^sub>M h\<close>]
  have "commutes {g \<bb>, g \<aa>, h \<bb>, h \<aa>}"
    unfolding g.morph h.morph g.pow_morph h.pow_morph by blast
  from commutesE[OF this, of "g \<aa>" "g \<bb>"]
  show False
    using g.non_comm_morph[of bina] by simp
qed

theorem not_beg_baibaib: assumes "1 < i"
  shows "\<not> binary_equality_generator (\<bb> \<cdot> \<aa>\<^sup>@i \<cdot> \<bb> \<cdot> \<aa>\<^sup>@i \<cdot> \<bb>)"
proof
  have nemp: "\<bb> \<cdot> \<aa>\<^sup>@i \<cdot> \<bb> \<cdot> \<aa>\<^sup>@i \<noteq> \<epsilon>" "\<bb> \<noteq> \<epsilon>"
    by simp_all
  assume "binary_equality_generator (\<bb> \<cdot> \<aa>\<^sup>@i \<cdot> \<bb> \<cdot> \<aa>\<^sup>@i \<cdot> \<bb>)"
  from beg_productE[of "\<bb> \<cdot> \<aa>\<^sup>@i \<cdot> \<bb> \<cdot> \<aa>\<^sup>@i" "\<bb>", unfolded rassoc, OF this nemp]
  obtain g h where "binary_code_morphism (g :: binA list \<Rightarrow> nat list)" "binary_code_morphism h" "g \<noteq> h" "(\<bb> \<cdot> \<aa> \<^sup>@ i \<cdot> \<bb> \<cdot> \<aa> \<^sup>@ i \<cdot> \<bb>) \<in> g =\<^sub>M h" "\<^bold>|g (\<bb> \<cdot> \<aa> \<^sup>@ i \<cdot> \<bb> \<cdot> \<aa> \<^sup>@ i)\<^bold>| < \<^bold>|h (\<bb> \<cdot> \<aa> \<^sup>@ i \<cdot> \<bb> \<cdot> \<aa> \<^sup>@ i)\<^bold>|" "\<^bold>|h \<bb>\<^bold>| < \<^bold>|g \<bb>\<^bold>|".
   interpret g: binary_code_morphism g
    by fact
  interpret h: binary_code_morphism h
    by fact
  have "g \<bb> \<noteq> h \<bb>"
    using \<open>\<^bold>|h \<bb>\<^bold>| < \<^bold>|g \<bb>\<^bold>|\<close> by fastforce
  from bew_baibaib_eq[OF assms this]  min_solD[OF \<open>(\<bb> \<cdot> \<aa> \<^sup>@ i \<cdot> \<bb> \<cdot> \<aa> \<^sup>@ i \<cdot> \<bb>) \<in> g =\<^sub>M h\<close>]
  have "commutes {g \<bb>, g \<aa>, h \<bb>, h \<aa>}"
    unfolding g.morph h.morph g.pow_morph h.pow_morph by blast
  from commutesE[OF this, of "g \<aa>" "g \<bb>"]
  show False
    using g.non_comm_morph[of bina] by simp
qed

end
