(*  Title:      Binary Square Interpretation
    File:       Combinatorics_Words_Interpretations.Binary_Square_Interpretation
    Author:     Štěpán Holub, Charles University
    Author:     Martin Raška, Charles University

Part of Combinatorics on Words Formalized. See https://gitlab.com/formalcow/combinatorics-on-words-formalized/
*)

theory Binary_Square_Interpretation

imports
    Combinatorics_Words.Equations_Basic 
begin

section \<open>Lemmas for covered x square\<close>

text \<open>This section explores various variants of the situation when @{term "x \<cdot> x"} is covered with
 @{term "x\<cdot>y\<^sup>@k\<cdot>u \<cdot> v\<cdot>y\<^sup>@l\<cdot>x"}, with @{term "y = u\<cdot>v"}, and the displayed dots being synchronized. 
\<close>

subsection \<open>Two particular cases\<close>

\<comment> \<open>Very short and very large overlap\<close>

lemma pref_suf_pers_short: assumes "x \<le>p v \<cdot> x" and "\<^bold>|v \<cdot> u\<^bold>| < \<^bold>|x\<^bold>|" and "x \<le>s p \<cdot> u \<cdot> v \<cdot> u" and "p \<in> \<langle>{u,v}\<rangle>"   
  \<comment> \<open>@{term "x \<cdot> x"} is covered by @{term "(p\<cdot>u\<cdot>v\<cdot>u) \<cdot> (v\<cdot>x)"}, the displayed dots being synchronized\<close>
  \<comment> \<open>That is, the condition on the first @{term x} in @{term "x\<cdot>y\<^sup>@k\<cdot>u \<cdot> v\<cdot>y\<^sup>@l\<cdot>x"} is relaxed\<close>
  shows "u\<cdot>v = v\<cdot>u"
proof (rule nemp_comm)
  have "v \<cdot> u <s x" 
    using suf_prod_long_less[OF _  \<open>\<^bold>|v \<cdot> u\<^bold>| < \<^bold>|x\<^bold>|\<close>, of "p \<cdot> u", unfolded rassoc, OF \<open>x \<le>s p \<cdot> u \<cdot> v \<cdot> u\<close>].
  assume "u \<noteq> \<epsilon>" and "v \<noteq> \<epsilon>"
  obtain q where "x = q \<cdot> v \<cdot> u" and "q \<noteq> \<epsilon>"
    using \<open>v \<cdot> u <s x\<close>  by (auto simp add: suf_def)
  hence "q \<le>s p \<cdot> u"
    using \<open>x \<le>s p \<cdot> u \<cdot> v \<cdot> u\<close> by (auto simp add: suf_def)
  have "q \<cdot> v = v \<cdot> q"
    using pref_marker[OF \<open>x \<le>p v\<cdot>x\<close>, of q ] \<open>x = q \<cdot> v \<cdot> u\<close> by simp
  from suf_marker_per_root[OF \<open>x \<le>p v \<cdot> x\<close>, of q u, unfolded rassoc \<open>x = q \<cdot> v \<cdot> u\<close>]
  have "u \<le>p v \<cdot> u" 
    by blast
  from root_comm_root[OF this \<open>q\<cdot>v = v\<cdot>q\<close> \<open>v \<noteq> \<epsilon>\<close>]
  have  "u \<le>p q \<cdot> u" by simp 

  consider  "u \<le>s q" | "q \<le>s u"
    using \<open>q \<le>s p \<cdot> u\<close> suffix_same_cases by blast 
  thus "u\<cdot>v = v\<cdot>u"
  proof (cases)
    assume "u \<le>s q"
    from two_elem_root_suf_comm'[OF \<open>u \<le>p v \<cdot> u\<close> _ _ \<open>p \<in> \<langle>{u,v}\<rangle>\<close>, of "q\<^sup><\<inverse>u", unfolded rq_suf[OF this] lassoc, OF _ \<open>q \<cdot> v = v \<cdot> q\<close>] 
    show ?thesis
      using \<open>q \<le>s p \<cdot> u\<close>  rq_suf[OF \<open>u \<le>s q\<close>] same_suffix_suffix by metis
  next
    assume "q \<le>s u"
    from root_suf_comm[OF \<open>u \<le>p q \<cdot> u\<close> suffix_appendI[OF this]]
    have "q\<cdot>u = u\<cdot>q". 
    from comm_trans[OF \<open>q \<cdot> u = u \<cdot> q\<close>[symmetric] \<open>q \<cdot> v = v \<cdot> q\<close>[symmetric] \<open>q \<noteq> \<epsilon>\<close>]
    show "u\<cdot>v = v\<cdot>u".
  qed
qed 

lemma pref_suf_pers_large_overlap: 
  assumes
    "p \<le>p x" and "s \<le>s x" and "p \<le>p r \<cdot> p" and "s \<le>s s \<cdot> r" and "\<^bold>|x\<^bold>| + \<^bold>|r\<^bold>| \<le> \<^bold>|p\<^bold>| + \<^bold>|s\<^bold>|"
  shows "x \<cdot> r = r \<cdot> x"      
  using assms
proof (cases "r = \<epsilon>", force)
  assume "r \<noteq> \<epsilon>" hence "r \<noteq> \<epsilon>" by blast
  have "\<^bold>|s\<^bold>| \<le> \<^bold>|x\<^bold>|"
    using \<open>s \<le>s x\<close> unfolding suf_def by force
  have "\<^bold>|p\<^bold>| \<le> \<^bold>|x\<^bold>|"
    using \<open>p \<le>p x\<close> by (force simp add: prefix_def)
  have "\<^bold>|r\<^bold>| \<le> \<^bold>|p\<^bold>|"
    using \<open>\<^bold>|x\<^bold>| + \<^bold>|r\<^bold>| \<le> \<^bold>|p\<^bold>| + \<^bold>|s\<^bold>|\<close> \<open>\<^bold>|s\<^bold>| \<le> \<^bold>|x\<^bold>|\<close> unfolding lenmorph by linarith 
  have "\<^bold>|r\<^bold>| \<le> \<^bold>|s\<^bold>|"
    using \<open>\<^bold>|x\<^bold>| + \<^bold>|r\<^bold>| \<le> \<^bold>|p\<^bold>| + \<^bold>|s\<^bold>|\<close> \<open>\<^bold>|p\<^bold>| \<le> \<^bold>|x\<^bold>|\<close> unfolding lenmorph by linarith 
  obtain p1 ov s1 where "p1 \<cdot> ov \<cdot> s1 = x"  and "p1 \<cdot> ov = p" and "ov \<cdot> s1 = s"  
    using pref_suf_overlapE[OF \<open>p \<le>p x\<close> \<open>s \<le>s x\<close>] using \<open>\<^bold>|x\<^bold>| + \<^bold>|r\<^bold>| \<le> \<^bold>|p\<^bold>| + \<^bold>|s\<^bold>|\<close> by auto
  have "\<^bold>|r\<^bold>| \<le> \<^bold>|ov\<^bold>|" 
    using \<open>\<^bold>|x\<^bold>| + \<^bold>|r\<^bold>| \<le> \<^bold>|p\<^bold>| + \<^bold>|s\<^bold>|\<close>[folded \<open>p1 \<cdot> ov \<cdot> s1 = x\<close> \<open>p1 \<cdot> ov = p\<close> \<open>ov \<cdot> s1 = s\<close>]
    unfolding lenmorph by force
  have "r \<le>p p"
    using \<open>\<^bold>|r\<^bold>| \<le> \<^bold>|p\<^bold>|\<close>[unfolded swap_len] pref_prod_long[OF \<open>p \<le>p r \<cdot> p\<close>] by blast 
  hence "r \<le>p x"
    using \<open>p \<le>p x\<close> by auto
  have "r \<le>s s"
    using \<open>\<^bold>|r\<^bold>| \<le> \<^bold>|s\<^bold>|\<close>[unfolded swap_len] pref_prod_long[reversed, OF \<open>s \<le>s s \<cdot> r\<close>] by blast 
  hence "r \<le>s x"
    using \<open>s \<le>s x\<close> by auto
  obtain k where "p \<le>p r\<^sup>@k"
    using per_prefE[OF \<open>p \<le>p r \<cdot> p\<close> \<open>r \<noteq> \<epsilon>\<close>]. 
  hence "p1 \<cdot> ov \<le>f r\<^sup>@k"
    unfolding \<open>p1 \<cdot> ov = p\<close> by blast
  obtain l where "s \<le>s r\<^sup>@l"
    using per_prefE[reversed, OF \<open>s \<le>s s \<cdot> r\<close> \<open>r \<noteq> \<epsilon>\<close>].
  hence "ov \<cdot> s1 \<le>f r\<^sup>@l"
    unfolding \<open>ov \<cdot> s1 = s\<close> by blast
  from per_glue_facs[OF \<open>p1 \<cdot> ov \<le>f r\<^sup>@k\<close> \<open>ov \<cdot> s1 \<le>f r\<^sup>@l\<close> \<open>\<^bold>|r\<^bold>| \<le> \<^bold>|ov\<^bold>|\<close>, unfolded \<open>p1 \<cdot> ov \<cdot> s1 = x\<close>]
  obtain m where "x \<le>f r \<^sup>@ m".
  show "x \<cdot> r = r \<cdot> x" 
    using root_suf_comm[OF
        pref_prod_root[OF marker_fac_pref[OF \<open>x \<le>f r \<^sup>@ m\<close> \<open>r \<le>p x\<close>]]
        suffix_appendI[OF \<open>r \<le>s x\<close>]]..  
qed

subsection \<open>Main cases\<close>

locale pref_suf_pers = 
  fixes x u v k m
  assumes 
    x_pref:  "x \<le>p (v \<cdot> (u \<cdot> v)\<^sup>@(Suc k)) \<cdot> x" \<comment> \<open>@{term "x \<le>p p \<cdot> x"} and @{term "p \<le>p q \<cdot> p"} where @{term "q \<le>p v \<cdot> u"}\<close> 
 and
    x_suf:  "x \<le>s x \<cdot> (u \<cdot> v)\<^sup>@(Suc m) \<cdot> u" \<comment> \<open>@{term "x \<le>s s \<cdot> x"} and @{term "s \<le>s q' \<cdot> s"} where @{term "q' \<le>p u \<cdot> v"}\<close>
begin

lemma pref_suf_commute_all_commutes:
  assumes  "\<^bold>|u \<cdot> v\<^bold>| \<le> \<^bold>|x\<^bold>|" and "u \<cdot> v = v \<cdot> u"
  shows "commutes {u,v,x}"
  using assms
proof (cases "u \<cdot> v = \<epsilon>", force)
  let ?p = "(v \<cdot> (u \<cdot> v)\<^sup>@(Suc k))"
  let ?s = "(u \<cdot> v)\<^sup>@(Suc m) \<cdot> u"
  note x_pref x_suf

  assume "u \<cdot> v \<noteq> \<epsilon>"
  have "?p \<noteq> \<epsilon>" and "?s \<noteq> \<epsilon>" and "v \<cdot> u \<noteq> \<epsilon>"
    using \<open>u \<cdot> v \<noteq> \<epsilon>\<close> by force+
  obtain r where "u \<in> r*" and "v \<in> r*" and "primitive r"
    using \<open>u \<cdot> v = v \<cdot> u\<close> comm_primrootE by metis
  hence "r \<noteq> \<epsilon>"
    by force

  have "?p \<in> r*" and "?s \<in> r*" and "v \<cdot> u \<in> r*" and "u \<cdot> v \<in> r*" 
    using \<open>u \<in> r*\<close> \<open>v \<in> r*\<close> by fast+

  have "x \<le>p r \<cdot> x"
    using  \<open>?p \<in> r*\<close> \<open>x \<le>p ?p \<cdot> x\<close> \<open>?p \<noteq> \<epsilon>\<close> by blast 
  have "v \<cdot> u \<le>s x"
    using ruler_le[reversed, OF _ _ \<open>\<^bold>|u \<cdot> v\<^bold>| \<le> \<^bold>|x\<^bold>|\<close>[unfolded swap_len[of u]], 
        of  "(x \<cdot> (u \<cdot> v) \<^sup>@ m \<cdot> u) \<cdot> v \<cdot> u", OF triv_suf, unfolded rassoc, OF \<open>x \<le>s x \<cdot> ?s\<close>[unfolded pow_Suc2 rassoc]]. 
  have "r \<le>s  v \<cdot> u" 
    using  \<open>v \<cdot> u \<noteq> \<epsilon>\<close> \<open>v \<cdot> u \<in> r*\<close> by blast
  have "r \<le>s r \<cdot> x"
    using suf_trans[OF \<open>r \<le>s  v \<cdot> u\<close> \<open>v \<cdot> u \<le>s x\<close>, THEN suffix_appendI] by blast 
  have "x \<cdot> r  = r \<cdot> x"
    using  root_suf_comm[OF \<open>x \<le>p r \<cdot> x\<close> \<open>r \<le>s r \<cdot> x\<close>, symmetric].
  hence "x \<in> r*"
    by (simp add: \<open>primitive r\<close> prim_comm_root) 
  thus "commutes {u,v,x}" 
    using \<open>u \<in> r*\<close> \<open>v \<in> r*\<close> commutesI_root[of "{u,v,x}"] by blast
qed

lemma no_overlap:
  assumes
    len: "\<^bold>|v \<cdot> (u \<cdot> v)\<^sup>@(Suc k)\<^bold>| + \<^bold>|(u \<cdot> v)\<^sup>@(Suc m) \<cdot> u\<^bold>| \<le> \<^bold>|x\<^bold>|" (is "\<^bold>|?p\<^bold>| + \<^bold>|?s\<^bold>| \<le> \<^bold>|x\<^bold>|")
  shows "commutes {u,v,x}"
  using assms
proof (cases "u \<cdot> v = \<epsilon>", force)
  note x_pref x_suf
  assume "u \<cdot> v \<noteq> \<epsilon>"
  have "?p \<noteq> \<epsilon>" and "?s \<noteq> \<epsilon>"
    using \<open>u \<cdot> v \<noteq> \<epsilon>\<close> by force+
  from \<open>\<^bold>|?p\<^bold>| + \<^bold>|?s\<^bold>| \<le> \<^bold>|x\<^bold>|\<close>  
  have "\<^bold>|?p\<^bold>| + \<^bold>|?s\<^bold>| - (gcd \<^bold>|?p\<^bold>| \<^bold>|?s\<^bold>|) \<le> \<^bold>|x\<^bold>|"
    by linarith
  from per_lemma_pref_suf[OF \<open>x \<le>p ?p \<cdot> x\<close> \<open>x \<le>s x \<cdot> ?s\<close> \<open>?p \<noteq> \<epsilon>\<close> \<open>?s \<noteq> \<epsilon>\<close> this]
  obtain r s kp ks mw where "?p = (r \<cdot> s)\<^sup>@kp" and "?s = (s \<cdot> r)\<^sup>@ks" and "x = (r \<cdot> s)\<^sup>@mw \<cdot> r" and "primitive (r \<cdot> s)".
  hence "\<rho> ?p = r \<cdot> s"
    using \<open>v \<cdot> (u \<cdot> v) \<^sup>@ Suc k \<noteq> \<epsilon>\<close> comm_primroots nemp_pow_nemp pow_comm prim_self_root by metis
  moreover have "\<rho> ?s = s \<cdot> r" 
    using   pow_prim_primroot[OF \<open>?s \<noteq> \<epsilon>\<close> _ \<open>?s = (s \<cdot> r)\<^sup>@ks\<close>] prim_conjug[OF \<open>primitive (r \<cdot> s)\<close>] by blast
  ultimately have "\<rho> ?p \<sim> \<rho> ?s" 
    by force
  from conj_pers_conj_comm[OF this]
  have "u \<cdot> v = v \<cdot> u".

  from pref_suf_commute_all_commutes[OF _ this]
  show "commutes {u,v,x}" 
    using len by auto
qed

lemma no_overlap':
  assumes
    len: "\<^bold>|v \<cdot> (u \<cdot> v)\<^sup>@(Suc k)\<^bold>| + \<^bold>|(u \<cdot> v)\<^sup>@(Suc m) \<cdot> u\<^bold>| \<le> \<^bold>|x\<^bold>|" (is "\<^bold>|?p\<^bold>| + \<^bold>|?s\<^bold>| \<le> \<^bold>|x\<^bold>|")
  shows "u \<cdot> v = v \<cdot> u"
  by (rule commutesE[of "{u,v,x}"], simp_all add: no_overlap[OF len]) 

lemma short_overlap: 
  assumes
    len1: "\<^bold>|x\<^bold>| < \<^bold>|v \<cdot> (u \<cdot> v)\<^sup>@(Suc k)\<^bold>| + \<^bold>|(u \<cdot> v)\<^sup>@(Suc m) \<cdot> u\<^bold>|" (is "\<^bold>|x\<^bold>| < \<^bold>|?p\<^bold>| + \<^bold>|?s\<^bold>|") and
    len2: "\<^bold>|v \<cdot> (u \<cdot> v)\<^sup>@(Suc k)\<^bold>| + \<^bold>|(u \<cdot> v)\<^sup>@(Suc m) \<cdot> u\<^bold>| \<le> \<^bold>|x\<^bold>| + \<^bold>|u\<^bold>|" (is "\<^bold>|?p\<^bold>| + \<^bold>|?s\<^bold>| \<le> \<^bold>|x\<^bold>| + \<^bold>|u\<^bold>|")
  shows "commutes {u,v,x}"
proof (rule pref_suf_commute_all_commutes)
  show "\<^bold>|u \<cdot> v\<^bold>| \<le> \<^bold>|x\<^bold>|"
    using len2  by force
next
  note x_pref x_suf
    \<comment> \<open>obtain the overlap\<close>

  have "\<^bold>|?p\<^bold>| \<le> \<^bold>|x\<^bold>|"
    using  len2 unfolding lenmorph by linarith
  hence "?p \<le>p x"
    using \<open>x \<le>p ?p \<cdot> x\<close> pref_prod_long by blast 

  have "\<^bold>|?s\<^bold>| \<le> \<^bold>|x\<^bold>|"
    using  len2 unfolding pow_len lenmorph by auto
  hence "?s \<le>s x"
    using suf_prod_long[OF \<open>x \<le>s x \<cdot> ?s\<close>] by blast 

  from  pref_suf_overlapE[OF \<open>?p \<le>p x\<close> \<open>?s \<le>s x\<close> less_imp_le[OF len1]]
  obtain p1 ov s1 where "p1 \<cdot> ov \<cdot> s1 = x" and "p1 \<cdot> ov = ?p" and "ov \<cdot> s1 = ?s".

  from len1[folded this]
  have "ov \<noteq> \<epsilon>"
    by fastforce 

  have "\<^bold>|ov\<^bold>| \<le> \<^bold>|u\<^bold>|"
    using len2[folded \<open>p1 \<cdot> ov \<cdot> s1 = x\<close> \<open>p1 \<cdot> ov = ?p\<close> \<open>ov \<cdot> s1 = ?s\<close>] unfolding lenmorph by auto

  then obtain s' where "ov \<cdot> s' = u" and "s' \<cdot> v \<cdot> (u \<cdot> v) \<^sup>@ m \<cdot> u = s1"
    using eqdE[OF \<open>ov \<cdot> s1 = ?s\<close>[unfolded pow_Suc rassoc]] by auto

\<comment> \<open>obtain the left complement\<close>

  from   eqdE[reversed, of p1 ov "v \<cdot> (u \<cdot> v)\<^sup>@k" "u \<cdot> v", unfolded rassoc, 
      OF \<open>p1 \<cdot> ov = ?p\<close>[unfolded pow_Suc2]]  \<open>\<^bold>|ov\<^bold>| \<le> \<^bold>|u\<^bold>|\<close>
  have "v \<cdot> (u \<cdot> v) \<^sup>@ k  \<le>p p1" by (auto simp add: prefix_def)

  then obtain q where "v \<cdot> (u \<cdot> v)\<^sup>@k \<cdot> q = p1" 
    by (force simp add: prefix_def)

\<comment> \<open>main proof using the lemma @{thm uvu_suf_uvvu}\<close>

  show "u \<cdot> v = v \<cdot> u"
  proof (rule sym, rule uvu_suf_uvvu)
    show "s' <s u" 
      using \<open>ov \<cdot> s' = u\<close> \<open>ov \<noteq> \<epsilon>\<close> by blast
    show "u \<cdot> v \<cdot> v \<cdot> u \<cdot> s' = q \<cdot> u \<cdot> v \<cdot> u" \<comment> \<open>the main fact: the overlap situation\<close>
    proof-
      have "u \<cdot> v \<cdot> u \<le>p ?s"
        unfolding pow_Suc rassoc pref_cancel_conv shift_pow by blast
      hence "p1 \<cdot> u \<cdot> v \<cdot> u \<le>p x"
        unfolding \<open>p1 \<cdot> ov \<cdot> s1 = x\<close>[symmetric] \<open>ov \<cdot> s1 = ?s\<close> pref_cancel_conv.
      hence "v \<cdot> (u \<cdot> v)\<^sup>@k \<cdot> q \<cdot> u \<cdot> v \<cdot> ov \<le>p x"
        using \<open>v \<cdot> (u \<cdot> v)\<^sup>@k \<cdot> q = p1\<close> \<open>ov \<cdot> s' = u\<close> by (force simp add: prefix_def)

      have "v \<cdot> u \<le>p x"
        using \<open>?p \<le>p x\<close>[unfolded pow_Suc] by (auto simp add: prefix_def)
      have "\<^bold>|?p \<cdot> v \<cdot> u\<^bold>| \<le> \<^bold>|x\<^bold>|"
        using len2 unfolding lenmorph by force  
      hence "?p \<cdot> v \<cdot> u \<le>p x"
        using \<open>x \<le>p ?p \<cdot> x\<close> \<open>v \<cdot> u \<le>p x\<close> pref_prod_longer by blast
      hence "v \<cdot> (u \<cdot> v)\<^sup>@k \<cdot> u \<cdot> v \<cdot> v \<cdot> u \<le>p x"
        unfolding pow_Suc2 rassoc.

      have "\<^bold>|v \<cdot> (u \<cdot> v)\<^sup>@k \<cdot> u \<cdot> v \<cdot> v \<cdot> u\<^bold>| = \<^bold>|v \<cdot> (u \<cdot> v)\<^sup>@k \<cdot> q \<cdot> u \<cdot> v \<cdot> ov\<^bold>|"
        using lenarg[OF \<open>p1 \<cdot> ov = ?p\<close>[folded \<open>v \<cdot> (u \<cdot> v)\<^sup>@k \<cdot> q = p1\<close>, unfolded pow_Suc2 rassoc cancel]]
        by force

      from ruler_eq_len[OF  \<open>v \<cdot> (u \<cdot> v)\<^sup>@k \<cdot> u \<cdot> v \<cdot> v \<cdot> u \<le>p x\<close> \<open>v \<cdot> (u \<cdot> v)\<^sup>@k \<cdot> q \<cdot> u \<cdot> v \<cdot> ov \<le>p x\<close> this, unfolded cancel]
      have "u \<cdot> v \<cdot> v \<cdot> u = q \<cdot> u \<cdot> v \<cdot> ov".

      thus  "u \<cdot> v \<cdot> v \<cdot> u \<cdot> s' = q \<cdot> u \<cdot> v \<cdot> u"
        using \<open>ov \<cdot> s' = u\<close> by auto
    qed
    show "q \<le>s v \<cdot> u"
    proof (rule ruler_le[reversed])
      show "q \<le>s x"
      proof (rule suf_trans)
        show "p1 \<le>s x"
          using \<open>p1 \<cdot> ov \<cdot> s1 = x\<close>[unfolded \<open>ov \<cdot> s1 = ?s\<close>] \<open>x \<le>s x \<cdot> ?s\<close>  same_suffix_suffix by blast
        show "q \<le>s p1"
          using \<open>v \<cdot> (u \<cdot> v) \<^sup>@ k \<cdot> q = p1\<close> by auto 
      qed                                                  
      show "v \<cdot> u \<le>s x"
        using \<open>?s \<le>s x\<close>[unfolded pow_Suc2 rassoc] suffix_appendD by metis  
      show "\<^bold>|q\<^bold>| \<le> \<^bold>|v \<cdot> u\<^bold>|" 
        using lenarg[OF \<open>u \<cdot> v \<cdot> v \<cdot> u \<cdot> s' = q \<cdot> u \<cdot> v \<cdot> u\<close>] lenarg[OF \<open>ov \<cdot> s' = u\<close>] by force
    qed
  qed auto
qed

lemma medium_overlap:
  assumes 
    len1: "\<^bold>|x\<^bold>| + \<^bold>|u\<^bold>| < \<^bold>|v \<cdot> (u \<cdot> v)\<^sup>@(Suc k)\<^bold>| + \<^bold>|(u \<cdot> v)\<^sup>@(Suc m) \<cdot> u\<^bold>|" (is "\<^bold>|x\<^bold>| + \<^bold>|u\<^bold>| < \<^bold>|?p\<^bold>| + \<^bold>|?s\<^bold>|") and
    len2: "\<^bold>|v \<cdot> (u \<cdot> v)\<^sup>@(Suc k)\<^bold>| + \<^bold>|(u \<cdot> v)\<^sup>@(Suc m) \<cdot> u\<^bold>| < \<^bold>|x\<^bold>| + \<^bold>|u \<cdot> v\<^bold>|" (is "\<^bold>|?p\<^bold>| + \<^bold>|?s\<^bold>| < \<^bold>|x\<^bold>| + \<^bold>|u \<cdot> v\<^bold>|")
  shows "commutes {u,v,x}"
proof (rule pref_suf_commute_all_commutes)
  show "\<^bold>|u \<cdot> v\<^bold>| \<le> \<^bold>|x\<^bold>|"
    using len2  by force
next
  note x_pref x_suf
  have "\<^bold>|?p\<^bold>| \<le> \<^bold>|x\<^bold>|"
    using  len2 by auto 
  hence "?p \<le>p x"
    using \<open>x \<le>p ?p \<cdot> x\<close> pref_prod_long by blast 
  hence  "v \<cdot> (u \<cdot> v)\<^sup>@k \<cdot> u \<cdot> v \<cdot> v \<le>p ?p \<cdot> x"
    using \<open>x \<le>p ?p \<cdot> x\<close>  unfolding pow_Suc2 rassoc  by (auto simp add: prefix_def)

  have "\<^bold>|?s\<^bold>| \<le> \<^bold>|x\<^bold>|"
    using  len2 unfolding pow_len lenmorph by auto
  hence "?s \<le>s x"
    using suf_prod_long[OF \<open>x \<le>s x \<cdot> ?s\<close>] by blast
  then obtain p' where "p' \<cdot> u \<cdot> v \<le>p x" and "p' \<cdot> ?s = x"
    by (auto simp add: suf_def)

  have "\<^bold>|p' \<cdot> u \<cdot> v\<^bold>| \<le> \<^bold>|?p \<cdot> v\<^bold>|"
    using len1[folded \<open>p' \<cdot> ?s = x\<close>] by force

  have "\<^bold>|v \<cdot> (u \<cdot> v)\<^sup>@k\<^bold>|  < \<^bold>|p'\<^bold>|"
    using len2[folded \<open>p' \<cdot> ?s = x\<close>] by force

  from less_imp_le[OF this]
  obtain p where "v \<cdot> (u \<cdot> v)\<^sup>@k \<cdot> p = p'"
    using ruler_le[OF \<open>?p \<le>p x\<close> \<open>p' \<cdot> u \<cdot> v \<le>p x\<close>, unfolded pow_Suc2 lassoc, THEN pref_cancel_right, THEN pref_cancel_right]  
    by (auto simp add: prefix_def)

  have "\<^bold>|p\<^bold>| \<le> \<^bold>|v\<^bold>|"
    using \<open>v \<cdot> (u \<cdot> v)\<^sup>@k \<cdot> p = p'\<close> \<open>\<^bold>|p' \<cdot> u \<cdot> v\<^bold>| \<le> \<^bold>|?p \<cdot> v\<^bold>|\<close> by force

  show "u \<cdot> v = v \<cdot> u"
  proof (rule uv_fac_uvv)
    show "p \<cdot> u \<cdot> v \<le>p u \<cdot> v \<cdot> v"
    proof (rule pref_cancel[of "v \<cdot> (u \<cdot> v)\<^sup>@k"], rule ruler_le)
      show "(v \<cdot> (u \<cdot> v) \<^sup>@ k) \<cdot> p \<cdot> u \<cdot> v \<le>p ?p \<cdot> x"
        unfolding lassoc \<open>v \<cdot> (u \<cdot> v)\<^sup>@k \<cdot> p = p'\<close>[unfolded lassoc]
        using \<open>p' \<cdot> u \<cdot> v \<le>p x\<close> \<open>x \<le>p ?p \<cdot> x\<close> by force 
      show "(v \<cdot> (u \<cdot> v) \<^sup>@ k) \<cdot> u \<cdot> v \<cdot> v \<le>p (v \<cdot> (u \<cdot> v) \<^sup>@ Suc k) \<cdot> x"
        unfolding pow_Suc2 rassoc
        using \<open>v \<cdot> (u \<cdot> v) \<^sup>@ Suc k \<le>p x\<close> by (auto simp add: prefix_def)    
      show "\<^bold>|(v \<cdot> (u \<cdot> v) \<^sup>@ k) \<cdot> p \<cdot> u \<cdot> v\<^bold>| \<le> \<^bold>|(v \<cdot> (u \<cdot> v) \<^sup>@ k) \<cdot> u \<cdot> v \<cdot> v\<^bold>|" 
        using \<open>v \<cdot> (u \<cdot> v)\<^sup>@k \<cdot> p = p'\<close> \<open>\<^bold>|p' \<cdot> u \<cdot> v\<^bold>| \<le> \<^bold>|?p \<cdot> v\<^bold>|\<close> by force
    qed

    have "p \<le>s x" 
      using  \<open>p' \<cdot> ?s = x\<close>[folded \<open>v \<cdot> (u \<cdot> v)\<^sup>@k \<cdot> p = p'\<close>] \<open>x \<le>s x \<cdot> ?s\<close> suf_cancel suffix_appendD by metis 

    from ruler_le[reversed, OF this \<open>?s \<le>s x\<close>, unfolded pow_Suc2 rassoc]
    show "p \<le>s (u \<cdot> v) \<^sup>@ m \<cdot> u \<cdot> v \<cdot> u"
      using  \<open>\<^bold>|p\<^bold>| \<le> \<^bold>|v\<^bold>|\<close> unfolding lenmorph by auto

    show "(u \<cdot> v) \<^sup>@ m \<cdot> u \<cdot> v \<cdot> u \<in> \<langle>{u, v}\<rangle>"
      by (simp add: gen_in hull_closed power_in)

    show "p \<noteq> \<epsilon>" 
      using \<open>\<^bold>|v \<cdot> (u \<cdot> v)\<^sup>@k\<^bold>|  < \<^bold>|p'\<^bold>|\<close> \<open>v \<cdot> (u \<cdot> v)\<^sup>@k \<cdot> p = p'\<close> by force
  qed
qed

thm 
  no_overlap
  short_overlap
  medium_overlap

end

thm 
  pref_suf_pers.no_overlap
  pref_suf_pers.short_overlap
  pref_suf_pers.medium_overlap
  pref_suf_pers_large_overlap

section \<open>Square interpretation\<close>

text \<open>In this section fundamental description is given of (the only) 
possible @{term "{x,y}"}-interpretation of the square @{term "x\<cdot>x"}, where @{term "\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|"}. 
The proof is divided into several locales.
\<close>

\<comment> \<open>An example motivating disjointness: an interpretation which is not disjoint.\<close>
lemma cover_not_disjoint:
  shows "primitive [0::nat,1,0,1,0,1,0]" (is "primitive ?x") and
    "primitive[0::nat, 1]" (is "primitive ?y") and
    "[0::nat,1,0,1,0,1,0] \<cdot> [0,1] \<noteq> [0,1] \<cdot> [0,1,0,1,0,1,0]" 
    (is "?x \<cdot> ?y \<noteq> ?y \<cdot> ?x") and 
    "\<epsilon> [0::nat,1,0,1,0,1,0] \<cdot> [0,1,0,1,0,1,0] [1,0,1,0] \<sim>\<^sub>\<I> [[0,1,0,1,0,1,0],[0,1],[0,1],[0,1,0,1,0,1,0]]"
    (is "\<epsilon> ?x \<cdot> ?x ?s \<sim>\<^sub>\<I> [?x,?y,?y,?x]") 
  unfolding factor_interpretation_def  
  by (primitivity_inspection+) force

subsection \<open>Locale: interpretation\<close>

locale square_interp =
  \<comment> \<open>The basic set of assumptions\<close>
  \<comment> \<open>The goal is to arrive at @{term "ws = [x] \<cdot> [y]\<^sup>@k \<cdot> [x]"} including the description 
   of the interpretation in terms of the first and the second occurrence of x in the interpreted square.\<close>
  fixes x y p s ws  
  assumes
    prim_x: "primitive x" and prim_y: "primitive y" and
    y_le_x: "\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|" and
    ws_lists: "ws \<in> lists {x,y}" and
    nconjug: "\<not> x \<sim> y" and
    disjoint:   "\<And> p1 p2. p1 \<le>p [x,x] \<Longrightarrow> p2 \<le>p ws \<Longrightarrow> p \<cdot> concat p1 \<noteq> concat p2" and
    interp: "p (x\<cdot>x) s \<sim>\<^sub>\<I> ws"

begin

interpretation binary_code x y
  using binary_code_def comm_prim nconjug nconjug_neq prim_x prim_y by metis

lemmas interpret_concat = fac_interpretE(3)[OF interp]

lemma p_nemp:  "p \<noteq> \<epsilon>"
  using disjoint[of \<epsilon> \<epsilon>] by auto

lemma s_nemp: "s \<noteq> \<epsilon>"
  using disjoint[of "[x,x]" ws] interpret_concat by force

lemma x_root: "\<rho> x = x"
  using prim_x by blast

lemma y_root: "\<rho> y = y"
  using prim_y by blast

lemma ws_nemp: "ws \<noteq> \<epsilon>"
  using bin_fst_nemp fac_interpret_nemp interp by blast

lemma hd_ws_lists: "hd ws \<in> {x, y}"
  using lists_hd_in_set ws_lists ws_nemp by auto

lemma last_ws_lists: "last ws \<in> {x, y}"
  using lists_hd_in_set[reversed, OF ws_nemp ws_lists].

lemma kE: obtains k where "[hd ws] \<cdot> [y]\<^sup>@k \<cdot> [last ws] = ws"
proof-
  from  list.collapse[OF ws_nemp] hd_word
  obtain ws' where "ws = [hd ws] \<cdot> ws'"
    by metis
  hence "\<^bold>|hd ws\<^bold>| \<le> \<^bold>|x\<^bold>|"
    using  two_elem_cases[OF lists_hd_in_set[OF ws_nemp ws_lists]] y_le_x by blast
  hence "\<^bold>|x\<^bold>| \<le> \<^bold>|concat ws'\<^bold>|"
    using lenarg[OF interpret_concat, unfolded lenmorph]
    unfolding concat.simps clean_emp  arg_cong[OF \<open>ws = [hd ws] \<cdot> ws'\<close>, of "\<lambda> x. \<^bold>|concat x\<^bold>|", unfolded concat_morph lenmorph] 
    by linarith  
  hence "ws' \<noteq> \<epsilon>"
    using nemp_len[OF bin_fst_nemp] by fastforce
  then obtain mid_ws where "ws' = mid_ws \<cdot> [last ws]"
    using \<open>ws = [hd ws] \<cdot> ws'\<close> append_butlast_last_id last_appendR by metis
  note \<open>ws = [hd ws] \<cdot> ws'\<close>[unfolded this]
       fac_interpretE[OF interp]
  obtain p' where [symmetric]:"p \<cdot> p' = hd ws" and "p' \<noteq> \<epsilon>" 
    using sprefE[OF \<open>p <p hd ws\<close>].
  obtain s' where  [symmetric]: "s'\<cdot> s  = last ws" and "s' \<noteq> \<epsilon>" 
    using sprefE[reversed, OF \<open>s <s last ws\<close>].
  have "p' \<cdot> concat mid_ws \<cdot> s' = x \<cdot> x"  
    using \<open>ws = [hd ws] \<cdot> mid_ws \<cdot> [last ws]\<close>[unfolded \<open>hd ws = p \<cdot> p'\<close> \<open>last ws  = s'\<cdot> s\<close>] 
           \<open>p \<cdot> (x \<cdot> x) \<cdot> s = concat ws\<close> by simp
  note over = prim_overlap_sqE[OF prim_x, folded this]
  have "mid_ws \<in> lists {x,y}"
    using \<open>ws = [hd ws] \<cdot> ws'\<close> \<open>ws' = mid_ws \<cdot> [last ws]\<close> append_in_lists_conv ws_lists by metis 
  have "x \<notin> set mid_ws" 
  proof
    assume "x \<in> set mid_ws"
    then obtain r q where "concat mid_ws = r \<cdot> x \<cdot> q"
      using concat.simps(2) concat_morph in_set_conv_decomp_first by metis
    have "(p' \<cdot> r)  \<cdot> x \<cdot> (q \<cdot> s') = x \<cdot> x" 
      using \<open>p' \<cdot> concat mid_ws \<cdot> s' = x \<cdot> x\<close>[unfolded \<open>concat mid_ws = r \<cdot> x \<cdot> q\<close>]
      unfolding rassoc.
    from prim_overlap_sqE[OF prim_x this]
    show False
      using \<open>p' \<noteq> \<epsilon>\<close> \<open>s' \<noteq> \<epsilon>\<close> by blast
  qed
  hence "mid_ws \<in> lists {y}"
    using \<open>mid_ws \<in> lists {x,y}\<close> by force
  from that sing_lists_exp[OF this]
  show thesis 
    using \<open>ws = [hd ws] \<cdot> mid_ws \<cdot> [last ws]\<close> by metis
qed

lemma l_mE: obtains m u v l where "(hd ws)\<cdot>y\<^sup>@m\<cdot>u = p\<cdot>x" and "v \<cdot> y\<^sup>@l \<cdot> (last ws) = x \<cdot> s" and
  "u\<cdot>v = y"  and "u \<cdot> v \<noteq> v \<cdot> u"
proof-
  note fac_interpretE[OF interp]
  obtain k where "[hd ws] \<cdot> [y]\<^sup>@k \<cdot> [last ws] = ws"
    using kE.
  from arg_cong[OF this, of concat, folded interpret_concat, unfolded concat_morph rassoc concat_sing' concat_sing_pow]
  have "hd ws \<cdot> y\<^sup>@k \<cdot> last ws = p \<cdot> x \<cdot> x \<cdot> s". 
  have "\<^bold>|hd ws\<^bold>| \<le> \<^bold>|p \<cdot> x\<^bold>|"
   unfolding lenmorph using y_le_x two_elem_cases[OF hd_ws_lists] using dual_order.trans by fastforce
  from eqd[OF _ this]
  obtain ya where "hd ws \<cdot> ya = p \<cdot> x"
    using \<open>hd ws \<cdot> y\<^sup>@k \<cdot> last ws = p \<cdot> x \<cdot> x \<cdot> s\<close>  by auto 
  have "\<^bold>|last ws\<^bold>| \<le> \<^bold>|x\<^bold>|"
    unfolding lenmorph using dual_order.trans last_ws_lists y_le_x by auto 
  hence "\<^bold>|last ws\<^bold>| < \<^bold>|x \<cdot> s\<^bold>|"
    unfolding lenmorph using nemp_len[OF s_nemp] by linarith  
  from eqd[reversed, OF _ less_imp_le[OF this]]                                            
  obtain yb where "yb \<cdot> (last ws) = x \<cdot> s"
    using \<open>(hd ws) \<cdot> y\<^sup>@k \<cdot> (last ws) = p \<cdot> x \<cdot> x \<cdot> s\<close> rassoc by metis 
  hence "yb \<noteq> \<epsilon>"  
    using s_nemp \<open>\<^bold>|last ws\<^bold>| < \<^bold>|x \<cdot> s\<^bold>|\<close> by force 
  have "ya \<cdot> yb = y\<^sup>@k"
    using \<open>(hd ws) \<cdot> y\<^sup>@k \<cdot> (last ws) = p \<cdot> x \<cdot> x \<cdot> s\<close>[folded \<open>yb \<cdot> (last ws) = x \<cdot> s\<close>, unfolded lassoc cancel_right, folded \<open>(hd ws) \<cdot> ya = p \<cdot> x\<close>, unfolded rassoc cancel, symmetric].  
  then obtain m u where "m < k" and "u <p y" and "y\<^sup>@m \<cdot> u = ya" 
    using pref_mod_power[of ya y k] \<open>yb \<noteq> \<epsilon>\<close>  by blast
  have "y\<^sup>@m \<cdot> u \<cdot> (u\<inverse>\<^sup>>y) \<cdot> y\<^sup>@(k - m - 1) = y\<^sup>@m \<cdot> y \<cdot> y\<^sup>@(k - m - 1)"
    using \<open>u <p y\<close>  by (auto simp add: prefix_def) 
  also have "... = y\<^sup>@(m + 1 + (k-m-1))"
    using mult_assoc add_exps pow_one' by metis
  also have "... = y\<^sup>@k"
    using \<open>m < k\<close>  by auto
  then obtain l v where "u\<cdot>v = y" and "y\<^sup>@m \<cdot> u \<cdot> v \<cdot> y\<^sup>@l = y\<^sup>@k"
    using \<open>y \<^sup>@ m \<cdot> u \<cdot> u\<inverse>\<^sup>>y \<cdot> y \<^sup>@ (k - m - 1) = y \<^sup>@ m \<cdot> y \<cdot> y \<^sup>@ (k - m - 1)\<close> calculation by auto
  have "concat ([hd ws]\<cdot>[y] \<^sup>@ m) = hd ws \<cdot> y \<^sup>@ m"
    by simp

  have "v \<noteq> \<epsilon>"
    using \<open>u <p y\<close> \<open>u\<cdot>v = y\<close> by fast

  have "[hd ws] \<cdot> [y] \<^sup>@ m \<le>p ws"
    using \<open>[hd ws] \<cdot> [y]\<^sup>@k \<cdot> [last ws] = ws\<close>[folded pop_pow[OF less_imp_le[OF \<open>m < k\<close>]]] by fastforce 
  from disjoint[OF _ this, of "[x]", unfolded \<open>concat ([hd ws] \<cdot> [y] \<^sup>@ m) = hd ws \<cdot> y \<^sup>@ m\<close>]
  have "u \<noteq> \<epsilon>"
    using \<open>(hd ws) \<cdot> ya = p \<cdot> x\<close>[folded \<open>y\<^sup>@m \<cdot> u = ya\<close>] s_nemp by force
  have "u\<cdot>v \<noteq> v\<cdot>u"
    using comm_not_prim[OF \<open>u \<noteq> \<epsilon>\<close> \<open>v \<noteq> \<epsilon>\<close>]  prim_y \<open>u\<cdot>v = y\<close> by blast

  from that[of m u "u\<inverse>\<^sup>>y" l, OF \<open>hd ws \<cdot> ya = p \<cdot> x\<close>[folded \<open>y \<^sup>@ m \<cdot> u = ya\<close>], folded \<open>yb \<cdot> last ws = x \<cdot> s\<close> \<open>u \<cdot> v = y\<close>,
      unfolded lq_triv lassoc cancel_right, OF _ _ this] 
  show thesis
    using \<open>y \<^sup>@ m \<cdot> u \<cdot> v \<cdot> y \<^sup>@ l = y \<^sup>@ k\<close>[folded \<open>ya \<cdot> yb = y \<^sup>@ k\<close> \<open>y \<^sup>@ m \<cdot> u =  ya\<close>, unfolded rassoc cancel, folded \<open>u \<cdot> v = y\<close>] by blast
qed

lemma last_ws: "last ws = x"
proof(rule ccontr)
  assume "last ws \<noteq> x"
  hence "last ws = y"
    using last_ws_lists by blast 
  obtain l m u v where "(hd ws)\<cdot>y\<^sup>@m\<cdot>u = p\<cdot>x" and "v \<cdot> y\<^sup>@l \<cdot> (last ws) = x \<cdot> s" and
    "u\<cdot>v = y" and "u \<cdot> v \<noteq> v \<cdot> u"
    using l_mE by metis
  note y_le_x[folded \<open>u \<cdot> v = y\<close>,unfolded swap_len[of u]]

  from \<open>v \<cdot> y\<^sup>@l \<cdot> (last ws) = x \<cdot> s\<close>[unfolded \<open>last ws = y\<close>, folded \<open>u \<cdot> v = y\<close>]
  have "x \<le>p (v \<cdot> u)\<^sup>@Suc l \<cdot> v"
    unfolding pow_Suc2 rassoc using append_eq_appendI prefix_def shift_pow by metis 
  moreover have "(v \<cdot> u) \<^sup>@ Suc l \<cdot> v \<le>p (v \<cdot> u) \<cdot> (v \<cdot> u) \<^sup>@ Suc l \<cdot> v"
    unfolding lassoc pow_comm[symmetric] using rassoc by blast
  ultimately have "x \<le>p (v \<cdot> u) \<cdot> x"
    using pref_keeps_root by blast

  thus False
  proof (cases "m = 0")
    assume "m \<noteq> 0"
    then obtain m' where "m = Suc m'"
      using not0_implies_Suc by blast
    have "v \<cdot> u \<le>s x"
      using \<open>(hd ws)\<cdot>y\<^sup>@m\<cdot>u = p\<cdot>x\<close>[folded \<open>u \<cdot> v = y\<close>, unfolded \<open>m = Suc m'\<close> pow_Suc2 rassoc] 
        suffix_appendD[THEN suf_prod_long[OF _ \<open>\<^bold>|v \<cdot> u\<^bold>| \<le> \<^bold>|x\<^bold>|\<close>], of p "hd ws \<cdot> (u \<cdot> v) \<^sup>@ m' \<cdot> u", unfolded rassoc] by simp   
    have "(v \<cdot> u) \<cdot> x = x \<cdot> (v \<cdot> u)"
      using root_suf_comm'[OF  \<open>x \<le>p (v \<cdot> u) \<cdot> x\<close> \<open>(v \<cdot> u) \<le>s x\<close>].
    thus False
      using \<open>u \<cdot> v = y\<close> comm_prim conjugI nconjug prim_conjug prim_x prim_y by metis 
  next
    assume "m = 0"  
    thus False
    proof (cases "hd ws = y")
      assume "hd ws = y"
      have "p \<cdot> (x \<cdot> x) \<cdot> s = y\<^sup>@Suc (Suc (Suc (m+l)))"
        unfolding rassoc \<open>v \<cdot> y\<^sup>@l \<cdot> (last ws) = x \<cdot> s\<close>[unfolded \<open>last ws = y\<close>, symmetric] power_Suc2
        unfolding lassoc \<open>(hd ws)\<cdot>y\<^sup>@m\<cdot>u = p\<cdot>x\<close>[unfolded \<open>hd ws = y\<close>, symmetric]
           \<open>u \<cdot> v = y\<close>[symmetric]
        by comparison
      have "\<rho> x \<sim> \<rho> y"
      proof (rule fac_two_conjug_primroot)
        show "x \<noteq> \<epsilon>" and "y \<noteq> \<epsilon>" using bin_fst_nemp bin_snd_nemp.
        show "x \<cdot> x \<le>f  y\<^sup>@Suc (Suc (Suc (m+l)))"
          using facI[of "x\<cdot>x" p s,unfolded \<open>p \<cdot> (x \<cdot> x) \<cdot> s = y\<^sup>@Suc (Suc (Suc (m+l)))\<close>].
        show "x \<cdot> x \<le>f x\<^sup>@2" 
          unfolding pow_two by blast
        show "\<^bold>|x\<^bold>| + \<^bold>|y\<^bold>| - (gcd \<^bold>|x\<^bold>| \<^bold>|y\<^bold>|) \<le> \<^bold>|x \<cdot> x\<^bold>|"
          using y_le_x unfolding lenmorph by auto
      qed
      thus False
        unfolding x_root y_root using nconjug by blast
    next
      assume "hd ws \<noteq> y"
      hence "hd ws = x"
        using hd_ws_lists by auto

      have "u \<cdot> v = v \<cdot> u"
      proof (rule pref_suf_pers_short[reversed])
        show "x \<le>s x \<cdot> u"
          using  \<open>(hd ws)\<cdot>y\<^sup>@m\<cdot>u = p\<cdot>x\<close>[unfolded \<open>m = 0\<close> \<open>hd ws = x\<close> pow_zero clean_emp]
          by (simp add: suf_def)
        have "v \<cdot> u \<le>p x"
          using \<open>x \<le>p (v \<cdot> u) \<cdot> x\<close> y_le_x[folded \<open>u \<cdot> v = y\<close>,unfolded swap_len[of u]]
            pref_prod_long by blast
        thus "\<^bold>|v \<cdot> u\<^bold>| < \<^bold>|x\<^bold>|"
          using  nconjug conjugI[OF _ \<open>u \<cdot> v = y\<close>, of x] \<open>\<^bold>|v \<cdot> u\<^bold>| \<le> \<^bold>|x\<^bold>|\<close>
                 le_neq_implies_less pref_same_len by blast 
        from \<open>x \<le>p (v \<cdot> u)\<^sup>@Suc l \<cdot> v\<close>  
        show "x \<le>p ((v \<cdot> u) \<cdot> v) \<cdot> (u \<cdot> v)\<^sup>@l"
          by comparison
        show "(u \<cdot> v) \<^sup>@ l \<in> \<langle>{v, u}\<rangle>" 
          by blast
      qed
      thus False 
        using prim_y \<open>u \<cdot> v \<noteq> v \<cdot> u\<close> by simp
    qed
  qed
qed

lemma rev_square_interp: 
  "square_interp (rev x) (rev y) (rev s) (rev p) (rev (map rev ws))"
proof (unfold_locales)
  show "rev (map rev ws) \<in> lists {rev x, rev y}"
    using ws_lists  by force
  show "(rev s) (rev x \<cdot> rev x) (rev p) \<sim>\<^sub>\<I> rev (map rev ws)"
    using interp rev_fac_interp by fastforce 
  show "\<^bold>|rev y\<^bold>| \<le> \<^bold>|rev x\<^bold>|"
    using y_le_x by simp
  show "\<not> (rev x) \<sim> (rev y)"
    by (simp add: conjug_rev_conv nconjug) 
  show "primitive (rev x)" and "primitive (rev y)"
    using prim_x prim_y by (simp_all add: prim_rev_iff) 
  show "\<And>p1 p2. p1 \<le>p [rev x, rev x] \<Longrightarrow> p2 \<le>p rev (map rev ws) \<Longrightarrow> rev s \<cdot> concat p1 \<noteq> concat p2"
  proof
    fix p1' p2' assume "p1' \<le>p [rev x, rev x]" and "p2' \<le>p rev (map rev ws)" and "rev s \<cdot> concat p1' = concat p2'"
    obtain p1 p2 where "p1' \<cdot> p1 = [rev x, rev x]" and "p2'\<cdot>p2 = rev (map rev ws)"
      using \<open>p1' \<le>p [rev x, rev x]\<close> \<open>p2' \<le>p rev (map rev ws)\<close> by (auto simp add: prefix_def)
    hence "rev s \<cdot> (concat p1' \<cdot> concat p1) \<cdot> rev p = concat p2' \<cdot> concat p2"
      unfolding concat_morph[symmetric] using \<open>(rev s) (rev x \<cdot> rev x) (rev p) \<sim>\<^sub>\<I> rev (map rev ws)\<close> fac_interpretE(3) by force
    from this[unfolded lassoc, folded \<open>rev s \<cdot> concat p1' = concat p2'\<close>, unfolded rassoc cancel]
    have "concat p1 \<cdot> rev p = concat p2".
    hence "p \<cdot> (concat (rev  (map rev p1))) = concat (rev (map rev p2))"
      using rev_append rev_concat rev_map rev_rev_ident by metis
    have "rev  (map rev p1) \<le>p [x,x]" 
      using arg_cong[OF \<open>p1' \<cdot> p1 = [rev x, rev x]\<close>, of "\<lambda> x. rev (map rev x)", unfolded map_append rev_append]
      by fastforce
    have "rev  (map rev p2) \<le>p ws"
      using arg_cong[OF \<open>p2'\<cdot>p2 = rev (map rev ws)\<close>, of "\<lambda> x. rev (map rev x)", unfolded map_append rev_append rev_map
          rev_rev_ident map_rev_involution, folded rev_map] by blast
    from disjoint[OF \<open>rev  (map rev p1) \<le>p [x,x]\<close> \<open>rev  (map rev p2) \<le>p ws\<close>]
    show False
      using \<open>p \<cdot> (concat (rev  (map rev p1))) = concat (rev (map rev p2))\<close> by blast
  qed
qed

lemma hd_ws: "hd ws = x"
using square_interp.last_ws[reversed, OF rev_square_interp]
unfolding hd_map[OF ws_nemp]
  by simp 

lemma p_pref: "p <p x"
  using fac_interpretE(1) hd_ws interp by auto

lemma s_suf: "s <s x"
  using fac_interpretE(2) last_ws interp by auto

end

subsection \<open>Locale with additional parameters\<close>
  \<comment> \<open>Obtained parameters added into the context, we show that there is just one @{term y} in @{term ws},
      that is, that @{term "m = 0"} and @{term "l = 0"}.
      The proof harvests results obtained in the section "Lemmas for covered x square" 
\<close>

locale square_interp_plus = square_interp +
  fixes l m u v 
  assumes fst_x: "x \<cdot> y\<^sup>@m \<cdot> u = p \<cdot> x" and
    snd_x: "v \<cdot> y\<^sup>@l \<cdot> x = x \<cdot> s" and 
    uv_y:  "u \<cdot> v = y" and
    uv_code: "u \<cdot> v \<noteq> v \<cdot> u"
begin

interpretation  binary_code x y
  using binary_code.intro comm_prim nconjug nconjug_neq prim_x prim_y by metis

interpretation uv: binary_code u v
  using uv_code by (simp add: binary_code.intro) 

lemma rev_square_interpret_plus:  "square_interp_plus (rev x) (rev y) (rev s) (rev p) (rev (map rev ws)) m l (rev v) (rev u)" 
proof-
  note fac_interpretE[OF interp, unfolded hd_ws last_ws]
  note \<open>s <s x\<close>[unfolded strict_suffix_to_prefix]
  note \<open>p <p x\<close>[unfolded spref_rev_suf_iff]

  interpret i: square_interp "(rev x)" "(rev y)" "(rev s)" "(rev p)" "(rev (map rev ws))"
    using rev_square_interp.
  show ?thesis
    apply standard
       apply (simp_all del: rev_append add: rev_pow[symmetric] rev_append[symmetric])
    by (simp_all only: uv_code, simp_all add: fst_x snd_x uv_y)
qed

subsubsection \<open>Exactly one of the exponents is zero: impossible.\<close>

text \<open>Uses lemma @{thm pref_suf_pers_short} and exploits the symmetric interpretation.\<close>

lemma fst_exp_zero: assumes "m = 0" and "l \<noteq> 0" shows "False"
proof (rule notE[OF uv_code])
  note y_le_x[folded uv_y, unfolded swap_len[of u]]
  have "x \<le>p (v \<cdot> (u \<cdot> v) \<^sup>@ l) \<cdot> x"
    unfolding rassoc using snd_x[folded uv_y] by fast 
  moreover have "v \<cdot> (u \<cdot> v) \<^sup>@ l \<noteq> \<epsilon>"
    using uv_code by force
  ultimately obtain exp where "x \<le>p (v \<cdot> (u \<cdot> v) \<^sup>@ l)\<^sup>@exp"
    using per_prefE by blast
  hence "exp \<noteq> 0"
    using pow_zero bin_fst_nemp[folded prefix_Nil] by metis

  show "u \<cdot> v = v \<cdot> u"
  proof (rule pref_suf_pers_short[reversed])
    show "x \<le>s x \<cdot> u"
      using fst_x[unfolded \<open>m = 0\<close>  pow_zero clean_emp] by (simp add: suf_def)
    have "((v \<cdot> u) \<cdot> v) \<cdot> ((u \<cdot> v)\<^sup>@(l-1)) \<cdot> (v \<cdot> (u \<cdot> v) \<^sup>@ l)\<^sup>@(exp -1) = (v \<cdot> (u \<cdot> v) \<^sup>@ l)\<^sup>@exp"
      (is "((v \<cdot> u) \<cdot> v) \<cdot> ?suf = (v \<cdot> (u \<cdot> v) \<^sup>@ l)\<^sup>@exp")
      by (simp add: \<open>exp \<noteq> 0\<close> \<open>l \<noteq> 0\<close> pop_pow_one)
    show "((u \<cdot> v)\<^sup>@(l-1)) \<cdot> (v \<cdot> (u \<cdot> v) \<^sup>@ l)\<^sup>@(exp -1) \<in> \<langle>{v,u}\<rangle>"
      by (simp add: gen_in hull_closed power_in)
    have "v \<cdot> u \<le>p x"
      using pref_prod_longer[OF \<open>x \<le>p (v \<cdot> (u \<cdot> v) \<^sup>@ l) \<cdot> x\<close>[unfolded rassoc] _ \<open>\<^bold>|v \<cdot> u\<^bold>| \<le> \<^bold>|x\<^bold>|\<close>]
      unfolding pop_pow_one[OF \<open>l \<noteq> 0\<close>] rassoc by blast
    thus "\<^bold>|v \<cdot> u\<^bold>| < \<^bold>|x\<^bold>|"
      using  nconjug conjugI[OF _ uv_y, of x] \<open>\<^bold>|v \<cdot> u\<^bold>| \<le> \<^bold>|x\<^bold>|\<close>
             le_neq_implies_less pref_same_len by blast 
    show "x \<le>p ((v \<cdot> u) \<cdot> v) \<cdot> ?suf" 
      unfolding \<open>((v \<cdot> u) \<cdot> v) \<cdot> ?suf = (v \<cdot> (u \<cdot> v) \<^sup>@ l)\<^sup>@exp\<close> by fact
  qed
qed

lemma snd_exp_zero: assumes "m \<noteq> 0" and "l = 0" shows "False"
using square_interp_plus.fst_exp_zero[OF rev_square_interpret_plus, reversed,
  rotated, OF assms]. 

subsubsection \<open>Both exponents positive: impossible\<close>

lemma both_exps_pos: assumes "m \<noteq> 0" and "l \<noteq> 0" shows "False"
proof-
  note fac_interpretE[OF interp, unfolded hd_ws last_ws]
  have "\<^bold>|p\<^bold>| \<le> \<^bold>|x\<^bold>|" and "\<^bold>|s\<^bold>| \<le> \<^bold>|x\<^bold>|" 
    using pref_len[OF sprefD1[OF \<open>p <p x\<close>]] suf_len[OF ssufD1[OF \<open>s <s x\<close>]].

  obtain m' l' where "Suc m' = m" and "Suc l' = l"
    using assms predE by metis
  have "x \<le>p (v \<cdot> (u \<cdot> v)\<^sup>@Suc l') \<cdot> x" 
    (is "x \<le>p ?pref \<cdot> x")
    using snd_x[folded uv_y \<open>Suc l' = l\<close>] by force
  moreover have "x \<le>s x \<cdot> ((u \<cdot> v)\<^sup>@Suc m' \<cdot> u)"
    (is "x \<le>s x \<cdot> ?suf") 
    using fst_x[folded uv_y \<open>Suc m' = m\<close>] by force 

  ultimately interpret pref_suf_pers x u v l' m'
    by (unfold_locales)

  have "?pref \<le>p x"
    using snd_x[folded uv_y \<open>Suc l' = l\<close> rassoc, symmetric]  eqd[reversed,  OF _ \<open>\<^bold>|s\<^bold>| \<le> \<^bold>|x\<^bold>|\<close>]  by blast
  have "?suf \<le>s x"  
    using fst_x[folded uv_y \<open>Suc m' = m\<close>, symmetric]  eqd[OF _ \<open>\<^bold>|p\<^bold>| \<le> \<^bold>|x\<^bold>|\<close>]  by blast

  have in_particular: "commutes {u,v,x} \<Longrightarrow> u \<cdot> v = v \<cdot> u"
    using commutes_def insertCI by metis
  have in_particular': "x \<cdot> v \<cdot> u = (v \<cdot> u) \<cdot> x \<Longrightarrow> x \<sim> y"
    using comm_prim conjugI' prim_conjug prim_x prim_y uv_y by metis

\<comment>  \<open>Case analysis based on (slightly modified) lemmas for covered x square.\<close>

  note  no_overlap_comm = no_overlap[THEN in_particular] and
    short_overlap_comm = short_overlap[THEN in_particular] and
    medium_overlap_comm = medium_overlap[THEN in_particular] and
    large_overlap_conjug = pref_suf_pers_large_overlap[OF \<open>?pref \<le>p x\<close> \<open>?suf \<le>s x\<close>,THEN in_particular']

  consider
    (no_overlap)     "\<^bold>|?pref\<^bold>| + \<^bold>|?suf\<^bold>| \<le> \<^bold>|x\<^bold>|" |
    (short_overlap)  "\<^bold>|x\<^bold>| <  \<^bold>|?pref\<^bold>| + \<^bold>|?suf\<^bold>| \<and>  \<^bold>|?pref\<^bold>| + \<^bold>|?suf\<^bold>| \<le> \<^bold>|x\<^bold>| + \<^bold>|u\<^bold>|" |
    (medium_overlap) "\<^bold>|x\<^bold>| + \<^bold>|u\<^bold>| < \<^bold>|?pref\<^bold>| + \<^bold>|?suf\<^bold>| \<and>  \<^bold>|?pref\<^bold>| + \<^bold>|?suf\<^bold>| < \<^bold>|x\<^bold>| + \<^bold>|u \<cdot> v\<^bold>|" | 
    (large_overlap)  "\<^bold>|x\<^bold>| + \<^bold>|v \<cdot> u\<^bold>| \<le>  \<^bold>|?pref\<^bold>| + \<^bold>|?suf\<^bold>|"
    unfolding swap_len[of v] by linarith
  thus False 
  proof (cases)
    case no_overlap
    then show False         
      using no_overlap_comm uv_code by blast
  next
    case short_overlap
    then show False         
      using short_overlap_comm uv_code by blast
  next
    case medium_overlap
    then show False         
      using medium_overlap_comm uv_code by blast
  next
    case large_overlap
    show False
      thm large_overlap_conjug nconjug 
    proof (rule notE[OF nconjug], rule large_overlap_conjug[OF _ _ large_overlap])
      have "(u \<cdot> v) \<^sup>@ l' \<le>p (u \<cdot> v) \<^sup>@ Suc l'"
        using pref_pow_ext by blast  
      thus "v \<cdot> (u \<cdot> v) \<^sup>@ Suc l' \<le>p (v \<cdot> u) \<cdot> v \<cdot> (u \<cdot> v) \<^sup>@ Suc l'"
        unfolding pow_Suc rassoc pref_cancel_conv.
      show "(u \<cdot> v) \<^sup>@ Suc m' \<cdot> u \<le>s ((u \<cdot> v) \<^sup>@ Suc m' \<cdot> u) \<cdot> v \<cdot> u"
        by comparison 
    qed
  qed
qed  

thm suf_cancel_conv

end 

subsection \<open>Back to the main locale\<close>

context square_interp

begin

definition u where "u = x\<inverse>\<^sup>>(p \<cdot> x)"
definition v where "v = (x \<cdot> s)\<^sup><\<inverse>x"

lemma cover_xyx: "ws = [x,y,x]" and uv_code: "u \<cdot> v \<noteq> v \<cdot> u" and uv_y: "u \<cdot> v = y" and
  px_xu:  "p \<cdot> x = x \<cdot> u" and  vx_xs:  "v \<cdot> x = x \<cdot> s"
proof-
  note prim_nemp[OF prim_y] 
  obtain k where ws: "[x] \<cdot> [y]\<^sup>@k \<cdot> [x] = ws"
    using kE[unfolded hd_ws last_ws].
  obtain m u' v' l where  "x \<cdot> y \<^sup>@ m \<cdot> u' = p \<cdot> x" and "v' \<cdot> y \<^sup>@ l \<cdot> x = x \<cdot> s" and "u' \<cdot> v' = y" and "u' \<cdot> v' \<noteq> v' \<cdot> u'"
    using l_mE[unfolded hd_ws last_ws].    
  then interpret square_interp_plus x y p s ws l m u' v'
    by (unfold_locales)
  have "m = 0" and "l = 0"
    using both_exps_pos snd_exp_zero fst_exp_zero by blast+
  have "u' = u"
    unfolding u_def
    using conjug_lq[OF fst_x[unfolded \<open>m = 0\<close> pow_zero clean_emp, symmetric]].
  have "v' = v"
    unfolding v_def
    using conjug_lq[reversed, OF snd_x[unfolded \<open>l = 0\<close> pow_zero clean_emp, symmetric]].
  have "x \<cdot> y \<^sup>@ m \<cdot> (u' \<cdot> v') \<cdot> y\<^sup>@l \<cdot> x = concat ws"
    unfolding interpret_concat[symmetric] using fst_x snd_x by force
  from this[folded ws, unfolded \<open>u' \<cdot> v' = y\<close> \<open>m = 0\<close> \<open>l = 0\<close> pow_zero clean_emp]
  have "k = 1"
    unfolding eq_pow_exp[OF \<open>y \<noteq> \<epsilon>\<close>, of k 1, symmetric] pow_one' concat_morph concat_pow 
    by simp
  from ws[unfolded this pow_one']
  show "ws = [x,y,x]" by simp
  show "u \<cdot> v  = y" and "u \<cdot> v \<noteq> v \<cdot> u"
    unfolding \<open>u' = u\<close>[symmetric] \<open>v' = v\<close>[symmetric] by fact+
  show  "p \<cdot> x = x \<cdot> u"
    using \<open>x \<cdot> y \<^sup>@ m \<cdot> u' = p \<cdot> x\<close>[unfolded \<open>m = 0\<close> \<open>u' = u\<close> pow_zero clean_emp, symmetric].
  show  " v \<cdot> x = x \<cdot> s"
    using \<open>v' \<cdot> y \<^sup>@ l \<cdot> x = x \<cdot> s\<close>[unfolded \<open>l = 0\<close> \<open>v' = v\<close> pow_zero clean_emp].
qed

lemma u_nemp: "u \<noteq> \<epsilon>" and v_nemp: "v \<noteq> \<epsilon>"
  using uv_code by force+

lemma cover: "x \<cdot> y \<cdot> x = p \<cdot> x \<cdot> x \<cdot> s"
  using interpret_concat cover_xyx by auto 

lemma conjug_facs: "\<rho> u \<sim> \<rho> v"
proof-
  note sufI[OF px_xu]
  have "u \<noteq> \<epsilon>"
    using p_nemp px_xu by force 
  obtain expu where "x \<le>f u\<^sup>@expu"
    using per_prefE[reversed, OF \<open> x \<le>s x \<cdot> u\<close> \<open>u \<noteq> \<epsilon>\<close> pref_fac[reversed,elim_format]].

  note prefI[OF vx_xs[symmetric]]
  have "v \<noteq> \<epsilon>"
    using s_nemp vx_xs by force
  obtain expv where "x \<le>f v\<^sup>@expv"
    using per_prefE[OF \<open>x \<le>p v \<cdot> x\<close> \<open>v \<noteq> \<epsilon>\<close> pref_fac[elim_format]].

  show "\<rho> u \<sim> \<rho> v"
  proof(rule fac_two_conjug_primroot[OF \<open>x \<le>f u\<^sup>@expu\<close> \<open>x \<le>f v\<^sup>@expv\<close> \<open>u \<noteq> \<epsilon>\<close> \<open>v \<noteq> \<epsilon>\<close>])
    show "\<^bold>|u\<^bold>| + \<^bold>|v\<^bold>| - (gcd \<^bold>|u\<^bold>| \<^bold>|v\<^bold>|) \<le> \<^bold>|x\<^bold>|"
      using y_le_x[folded uv_y, unfolded lenmorph] by fastforce
  qed 
qed

term square_interp.v

\<comment> \<open>We have a detailed information about all words\<close>
lemma bin_sq_interpE: obtains r t m k l
  where "(t \<cdot> r)\<^sup>@Suc k = u" and  "(r \<cdot> t)\<^sup>@Suc l = v" and
    "(r \<cdot> t)\<^sup>@Suc m \<cdot> r = x" and "(t \<cdot> r)\<^sup>@Suc k \<cdot> (r \<cdot> t)\<^sup>@Suc l = y"
    and "(r \<cdot> t)\<^sup>@Suc k = p" and  "(t \<cdot> r)\<^sup>@Suc l = s"  and "r \<cdot> t \<noteq> t \<cdot> r"
proof-

  obtain r t k m where "(r \<cdot> t)\<^sup>@Suc k = p" and "(t \<cdot> r)\<^sup>@Suc k = u" and "(r \<cdot> t)\<^sup>@m \<cdot> r = x" and
    "t \<noteq> \<epsilon>" and "primitive (r \<cdot> t)" 
    using conjug_eq_primrootE[OF px_xu p_nemp]. 
  have "t \<cdot> r = \<rho> u"
    using  prim_conjug[OF \<open>primitive (r \<cdot> t)\<close>, THEN pow_prim_primroot[OF u_nemp], OF conjugI' \<open>(t \<cdot> r)\<^sup>@Suc k = u\<close>[symmetric]]..

  have "m \<noteq> 0"
  proof
    assume "m = 0"
    hence "x = r" using \<open>(r \<cdot> t)\<^sup>@m \<cdot> r = x\<close> by simp
    from y_le_x[folded uv_y, folded \<open>(t \<cdot> r)\<^sup>@Suc k = u\<close>, unfolded lenmorph pow_len this]
    show False
      using nemp_len[OF \<open>t \<noteq> \<epsilon>\<close>] by force
  qed

  then obtain pred_m where "m = Suc pred_m"
    using not0_implies_Suc by auto

  from \<open>(r \<cdot> t)\<^sup>@m \<cdot> r = x\<close>[unfolded this]
  have "r \<cdot> t \<le>p x"
    by auto

  have "r \<cdot> t = \<rho> v"
  proof (rule ruler_eq_len[of "\<rho> v" "x" "r \<cdot> t", symmetric])
    have "\<^bold>|\<rho> v\<^bold>| \<le> \<^bold>|x\<^bold>|"
      unfolding conjug_len[OF conjug_facs, symmetric] \<open>t \<cdot> r = \<rho> u\<close>[symmetric]
      unfolding \<open>(r \<cdot> t)\<^sup>@m \<cdot> r = x\<close>[symmetric]
        lenmorph pow_len
      using \<open>m = Suc pred_m\<close> by auto         
    from ruler_le[OF _ _ this, of "v \<cdot> x"]
    show "\<rho> v \<le>p x"
      using vx_xs prefI prefix_prefix primroot_pref v_nemp by metis 
    show "r \<cdot> t \<le>p x" by fact
    show "\<^bold>|\<rho> v\<^bold>| = \<^bold>|r \<cdot> t\<^bold>|"
      unfolding conjug_len[OF conjug_facs, symmetric, folded \<open>t \<cdot> r = \<rho> u\<close>] lenmorph by simp
  qed

  then obtain l where "(r \<cdot> t)\<^sup>@Suc l = v"
    using primroot_expE v_nemp by metis

  have "(t \<cdot> r)\<^sup>@Suc l = s" 
    using vx_xs[folded \<open>(r \<cdot> t)\<^sup>@m \<cdot> r = x\<close> \<open>(r \<cdot> t)\<^sup>@Suc l = v\<close>, unfolded lassoc pows_comm[of _ _ m],
        unfolded rassoc cancel, unfolded shift_pow cancel]. 

  have "r \<cdot> t \<noteq> t \<cdot> r"
    using \<open>(t \<cdot> r) \<^sup>@ Suc k = u\<close> \<open>(r \<cdot> t) \<^sup>@ Suc l = v\<close> pows_comm[of "t \<cdot> r" "Suc k" "Suc l"] uv_code by force

  show thesis
    using that[OF \<open>(t \<cdot>r)\<^sup>@Suc k = u\<close> \<open>(r \<cdot> t) \<^sup>@ Suc l = v\<close> \<open>(r \<cdot> t)\<^sup>@m \<cdot> r = x\<close>[unfolded \<open>m = Suc pred_m\<close>]
        uv_y[folded \<open>(t \<cdot>r)\<^sup>@Suc k = u\<close> \<open>(r \<cdot> t) \<^sup>@ Suc l = v\<close>] \<open>(r \<cdot> t) \<^sup>@ Suc k = p\<close> \<open>(t \<cdot> r) \<^sup>@ Suc l = s\<close>  \<open>r \<cdot> t \<noteq> t \<cdot> r\<close>].
qed

end

subsection \<open>Locale: Extendable interpretation\<close>
text \<open>Further specification follows from the assumption that the interpretation is extendable,
 that is, the covered @{term "x\<cdot>x"} is a factor of a word composed of @{term "{x,y}"}. Namely, @{term u} and @{term v} are then conjugate by @{term x}.\<close>

locale square_interp_ext = square_interp +
  assumes p_extend: "\<exists> pe. pe \<in> \<langle>{x,y}\<rangle> \<and> p \<le>s pe" and
    s_extend: "\<exists> se. se \<in> \<langle>{x,y}\<rangle> \<and> s \<le>p se"

begin

lemma s_pref_y: "s \<le>p y"
proof-
  obtain sy ry eu ev ex
    where "(ry \<cdot> sy)\<^sup>@Suc eu = u" and  "(sy \<cdot> ry)\<^sup>@Suc ev = v" and
      "(sy \<cdot> ry)\<^sup>@Suc eu = p" and  "(ry \<cdot> sy)\<^sup>@Suc ev = s" and
      "(sy \<cdot> ry)\<^sup>@Suc ex \<cdot> sy = x" and "sy \<cdot> ry \<noteq> ry \<cdot> sy"
    using bin_sq_interpE.

  obtain se where "se \<in> \<langle>{x,y}\<rangle>" and  "s \<le>p se"
    using s_extend by blast
  hence "se \<noteq> \<epsilon>" using s_nemp by force

  from \<open>(sy \<cdot> ry)\<^sup>@Suc ex \<cdot> sy = x\<close>
  have "sy \<cdot> ry \<le>p x"
    unfolding pow_Suc rassoc by force

  have "x \<le>p se \<or> y \<le>p se"
    using  \<open>se \<noteq> \<epsilon>\<close> hull.cases[OF \<open>se \<in> \<langle>{x,y}\<rangle>\<close>, of "x \<le>p se \<or> y \<le>p se"]
      prefix_append triv_pref two_elem_cases by blast 
  moreover have "\<not> x \<le>p se"
  proof
    assume "x \<le>p se"
    from ruler_eq_len[of "sy \<cdot> ry" se "ry \<cdot> sy", OF pref_trans[OF \<open>sy \<cdot> ry \<le>p x\<close> this]]
    show False  
      using \<open>s \<le>p se\<close>[folded \<open>(ry \<cdot> sy)\<^sup>@Suc ev = s\<close>[unfolded pow_Suc]] \<open>sy \<cdot> ry \<noteq> ry \<cdot> sy\<close> by (force simp add: prefix_def)
  qed
  ultimately have y_pref_se: "y \<le>p se" by blast

  from ruler_le[OF \<open>s \<le>p se\<close> this] 
  show "s \<le>p y"
    using lenarg[OF vx_xs] unfolding uv_y[symmetric] lenmorph by linarith
qed

lemma rev_square_interpret_ext: "square_interp_ext (rev x) (rev y) (rev s) (rev p) (rev (map rev ws))"
proof-
  interpret i: square_interp "(rev x)" "(rev y)" "(rev s)" "(rev p)" "(rev (map rev ws))"
    using rev_square_interp.
  show ?thesis
  proof 
    show "\<exists>pe. pe \<in> \<langle>{rev x, rev y}\<rangle> \<and> rev s \<le>s pe"
      using pref_rev_suf_iff s_pref_y by blast
    obtain pe where "pe \<in> \<langle>{x, y}\<rangle>" and  "p \<le>s pe"
      using p_extend by blast
    hence "rev pe \<in> \<langle>{rev x, rev y}\<rangle>"
      by (simp add: rev_hull rev_in_conv) 
    thus "\<exists>se. se \<in> \<langle>{rev x, rev y}\<rangle> \<and> rev p \<le>p se"
      using \<open>p \<le>s pe\<close>[unfolded suf_rev_pref_iff prefix_def] rev_rev_ident by blast
  qed
qed

lemma p_suf_y: "p \<le>s y"
proof-
  interpret i: square_interp_ext "(rev x)" "(rev y)" "(rev s)" "(rev p)" "(rev (map rev ws))"
    using rev_square_interpret_ext.

  from i.s_pref_y[reversed]
  show "p \<le>s y".
qed   

theorem bin_sq_interpret_extE: obtains r t k m where  "(r \<cdot> t)\<^sup>@Suc m \<cdot> r = x" and  "(t \<cdot> r)\<^sup>@Suc k \<cdot> (r \<cdot> t)\<^sup>@ Suc k = y"
  "(r \<cdot> t)\<^sup>@Suc k = p" and "(t \<cdot> r)\<^sup>@ Suc k = s" and "r \<cdot> t \<noteq> t \<cdot> r" and "u = s" and "v = p" and "\<^bold>|p\<^bold>| = \<^bold>|s\<^bold>|"
proof-  
  obtain r t k k' m
    where u: "(t \<cdot> r)\<^sup>@Suc k = u" and v:  "(r \<cdot> t)\<^sup>@Suc k' = v" and
      p: "(r \<cdot> t)\<^sup>@Suc k = p" and s: "(t \<cdot> r)\<^sup>@Suc k' = s" and
      x: "(r \<cdot> t)\<^sup>@Suc m \<cdot> r = x" and code: "r \<cdot> t \<noteq> t \<cdot> r"
    using bin_sq_interpE. 
  have "\<^bold>|u \<cdot> v\<^bold>| = \<^bold>|s \<cdot> p\<^bold>|"
    using lenarg[OF px_xu, unfolded lenmorph] lenarg[OF vx_xs, unfolded lenmorph] by simp
  hence "u \<cdot> v = s \<cdot> p"
    unfolding uv_y using s_pref_y p_suf_y by (auto simp add: prefix_def suf_def)
  note eq = \<open>u \<cdot> v = s \<cdot> p\<close>[unfolded  \<open>(t \<cdot> r)\<^sup>@Suc k = u\<close>[symmetric] \<open>(r \<cdot> t)\<^sup>@Suc k' = v\<close>[symmetric],
      unfolded \<open>(t \<cdot> r)\<^sup>@Suc k' = s\<close>[symmetric] \<open>(r \<cdot> t)\<^sup>@Suc k = p\<close>[symmetric]]
  from pows_eq_comm[OF this, THEN comm_add_exps, of "Suc k" "Suc k'"]
  have "k = k'"
    unfolding \<open>(t \<cdot> r) \<^sup>@ Suc k = u\<close> \<open>(r \<cdot> t) \<^sup>@ Suc k' = v\<close> using uv_code by blast  
  have "\<^bold>|p\<^bold>| = \<^bold>|s\<^bold>|"
    using lenarg[OF p] lenarg[OF s] unfolding \<open>k = k'\<close> pow_len lenmorph add.commute[of "\<^bold>|r\<^bold>|"] by fastforce
  thus thesis
    using that[OF x uv_y[folded u v \<open>k = k'\<close>] p s[folded \<open>k = k'\<close>] code] u v p s unfolding \<open>k = k'\<close> by argo   
qed

lemma ps_len: "\<^bold>|p\<^bold>| = \<^bold>|s\<^bold>|" and p_eq_v: "p = v" and s_eq_u: "s = u"
  using bin_sq_interpret_extE by blast+

lemma v_x_x_u: "v \<cdot> x = x \<cdot> u"
  using vx_xs unfolding s_eq_u.

lemma sp_y: "s \<cdot> p = y"
  using p_eq_v s_eq_u uv_y by auto 

lemma p_x_x_s: "p \<cdot> x = x \<cdot> s"
  by (simp add: px_xu s_eq_u)

lemma xxy_root: "x \<cdot> x \<cdot> y = (x \<cdot> p) \<cdot> (x \<cdot> p)"
  using p_x_x_s sp_y by force

theorem sq_ext_interp: "ws = [x, y, x]" "s \<cdot> p = y" "p \<cdot> x = x \<cdot> s"
  using cover_xyx sp_y p_x_x_s.

end

theorem bin_sq_interpE:  
  assumes "primitive x" and "primitive y" and "\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|" and "ws \<in> lists {x, y}" and "\<not> x \<sim> y" and 
    "\<And> p1 p2. p1 \<le>p [x, x] \<Longrightarrow> p2 \<le>p ws \<Longrightarrow> p \<cdot> concat p1 \<noteq> concat p2" and "p x \<cdot> x s \<sim>\<^sub>\<I> ws"
  obtains r t m k l where "(r \<cdot> t)\<^sup>@Suc m \<cdot> r = x" and "(t \<cdot> r)\<^sup>@Suc k \<cdot> (r \<cdot> t)\<^sup>@ Suc l = y"
    "(r \<cdot> t)\<^sup>@Suc k = p" and "(t \<cdot> r)\<^sup>@ Suc l = s" and "r \<cdot> t \<noteq> t \<cdot> r"
  using  square_interp.bin_sq_interpE[OF square_interp.intro, OF assms, of thesis].

theorem bin_sq_interpret_extE:  
  assumes "primitive x" and "primitive y" and "\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|" and "ws \<in> lists {x, y}"  and "\<not> x \<sim> y" and
    "\<And> p1 p2. p1 \<le>p [x, x] \<Longrightarrow> p2 \<le>p ws \<Longrightarrow> p \<cdot> concat p1 \<noteq> concat p2"  and "p x \<cdot> x s \<sim>\<^sub>\<I> ws" and
    p_extend: "\<exists> pe. pe \<in> \<langle>{x,y}\<rangle> \<and> p \<le>s pe" and
    s_extend: "\<exists> se. se \<in> \<langle>{x,y}\<rangle> \<and> s \<le>p se"
  obtains r t m k where "(r \<cdot> t)\<^sup>@Suc m \<cdot> r = x" and "(t \<cdot> r)\<^sup>@Suc k \<cdot> (r \<cdot> t)\<^sup>@ Suc k = y"
    "(r \<cdot> t)\<^sup>@Suc k = p" and "(t \<cdot> r)\<^sup>@ Suc k = s" and "r \<cdot> t \<noteq> t \<cdot> r"
  using  square_interp_ext.bin_sq_interpret_extE[OF square_interp_ext.intro, OF square_interp.intro square_interp_ext_axioms.intro, OF assms, of thesis].

end