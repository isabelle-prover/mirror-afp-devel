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

section \<open>Factor interpretation\<close>

definition factor_interpretation :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list \<Rightarrow> bool" ("_ _ _ \<sim>\<^sub>\<I> _" [51,51,51,51] 60)
  where "factor_interpretation p u s ws = (p <p hd ws \<and> s <s last ws \<and> p \<cdot> u \<cdot> s = concat ws)"

lemma fac_interpret_nemp:  "u \<noteq> \<epsilon> \<Longrightarrow> p u s \<sim>\<^sub>\<I> ws \<Longrightarrow> ws \<noteq> \<epsilon>"
  unfolding factor_interpretation_def by auto

lemma fac_interpretE: assumes "p u s \<sim>\<^sub>\<I> ws"
  shows "p <p hd ws" and "s <s last ws" and "p \<cdot> u \<cdot> s = concat ws"
  using assms unfolding factor_interpretation_def by blast+ 

lemma fac_interpretI: 
  "p <p hd ws \<Longrightarrow> s <s last ws \<Longrightarrow> p \<cdot> u \<cdot> s = concat ws \<Longrightarrow> p u s \<sim>\<^sub>\<I> ws"
  unfolding factor_interpretation_def by blast

lemma obtain_fac_interpret: assumes  "pu \<cdot> u \<cdot> su = concat ws" and "u \<noteq> \<epsilon>" 
  obtains ps ss p s vs where "p u s \<sim>\<^sub>\<I> vs" and "ps \<cdot> vs \<cdot> ss = ws" and "concat ps \<cdot> p = pu" and
    "s \<cdot> concat ss = su"  
  using assms
proof (induction "\<^bold>|ws\<^bold>|" arbitrary: ws pu su thesis rule: less_induct)
  case less
  then show ?case
  proof-
    have "ws \<noteq> \<epsilon>"
      using \<open>u \<noteq> \<epsilon>\<close> \<open>pu \<cdot> u \<cdot> su = concat ws\<close> by force
    have "\<^bold>|tl ws\<^bold>| < \<^bold>|ws\<^bold>|" and "\<^bold>|butlast ws\<^bold>| < \<^bold>|ws\<^bold>|"
      using \<open>ws \<noteq> \<epsilon>\<close> by force+
    show thesis
    proof (cases) 
      assume "hd ws \<le>p pu \<or> last ws \<le>s su"
      then show thesis
      proof 
        assume "hd ws \<le>p pu"
        from prefixE[OF this]
        obtain pu' where "pu = hd ws \<cdot> pu'".
        from \<open>pu \<cdot> u \<cdot> su = concat ws\<close>[unfolded this, folded arg_cong[OF hd_tl[OF \<open>ws \<noteq> \<epsilon>\<close>], of concat]]
        have "pu' \<cdot> u \<cdot> su = concat (tl ws)"
          by force
        from less.hyps[OF \<open>\<^bold>|tl ws\<^bold>| < \<^bold>|ws\<^bold>|\<close> _ \<open>pu' \<cdot> u \<cdot> su = concat (tl ws)\<close> \<open>u \<noteq> \<epsilon>\<close>] 
        obtain p s vs ps' ss where "p u s \<sim>\<^sub>\<I> vs" and  "ps' \<cdot> vs \<cdot> ss = tl ws" and  "concat ps' \<cdot> p = pu'" 
          and "s \<cdot> concat ss = su".
        have "(hd ws # ps') \<cdot> vs \<cdot> ss = ws" 
          using \<open>ws \<noteq> \<epsilon>\<close> \<open>ps' \<cdot> vs \<cdot> ss = tl ws\<close> by auto
        have "concat (hd ws # ps') \<cdot> p = pu"
          using \<open>concat ps' \<cdot> p = pu'\<close> unfolding \<open>pu = hd ws \<cdot> pu'\<close> by fastforce
        from less.prems(1)[OF \<open>p u s \<sim>\<^sub>\<I> vs\<close> \<open>(hd ws # ps') \<cdot> vs \<cdot> ss = ws\<close> \<open>concat (hd ws # ps') \<cdot> p = pu\<close> \<open>s \<cdot> concat ss = su\<close>]
        show thesis.
      next
        assume "last ws \<le>s su"
        from suffixE[OF this]
        obtain su' where "su = su' \<cdot> last ws".
        from \<open>pu \<cdot> u \<cdot> su = concat ws\<close>[unfolded this, folded arg_cong[OF hd_tl[reversed, OF \<open>ws \<noteq> \<epsilon>\<close>], of concat]]
        have "pu \<cdot> u \<cdot> su' = concat (butlast ws)"
          by force
        from less.hyps[OF \<open>\<^bold>|butlast ws\<^bold>| < \<^bold>|ws\<^bold>|\<close> _ \<open>pu \<cdot> u \<cdot> su' = concat (butlast ws)\<close> \<open>u \<noteq> \<epsilon>\<close>] 
        obtain p s vs ps ss' where "p u s \<sim>\<^sub>\<I> vs" and  "ps \<cdot> vs \<cdot> ss' = butlast ws" and "concat ps \<cdot> p = pu" and "s \<cdot> concat ss' = su'".
        have "ps \<cdot> vs \<cdot> (ss' \<cdot> [last ws]) = ws" 
          using  append_butlast_last_id[OF \<open>ws \<noteq> \<epsilon>\<close>, folded \<open>ps \<cdot> vs \<cdot> ss' = butlast ws\<close>] unfolding rassoc. 
        have "s \<cdot> concat (ss' \<cdot> [last ws]) = su"
          using \<open>s \<cdot> concat ss' = su'\<close> \<open>su = su' \<cdot> last ws\<close> by fastforce
        from less.prems(1)[OF \<open>p u s \<sim>\<^sub>\<I> vs\<close> \<open>ps \<cdot> vs \<cdot> (ss' \<cdot> [last ws]) = ws\<close> \<open>concat ps \<cdot> p = pu\<close>  \<open>s \<cdot> concat (ss' \<cdot> [last ws]) = su\<close>] 
        show thesis.
      qed
    next
      assume not_or: "\<not> (hd ws \<le>p pu \<or> last ws \<le>s su)"
      hence "pu <p hd ws" and "su <s last ws"
        using ruler[OF concat_hd_pref[OF \<open>ws \<noteq> \<epsilon>\<close>] prefI'[OF \<open>pu \<cdot> u \<cdot> su = concat ws\<close>[symmetric]]] 
          ruler[reversed, OF concat_hd_pref[reversed, OF \<open>ws \<noteq> \<epsilon>\<close>] prefI'[reversed, OF \<open>pu \<cdot> u \<cdot> su = concat ws\<close>[symmetric, unfolded lassoc]]] by auto 
      from fac_interpretI[OF this \<open>pu \<cdot> u \<cdot> su = concat ws\<close>]
      have "pu u su \<sim>\<^sub>\<I> ws".
      from less.prems(1)[OF this, of \<epsilon> \<epsilon>]
      show thesis by simp
    qed
  qed
qed

lemma obtain_fac_interp': assumes "u \<le>f concat ws" and "u \<noteq> \<epsilon>" 
  obtains p s vs where "p u s \<sim>\<^sub>\<I> vs" and "vs \<le>f ws" 
proof-
  from facE[OF \<open>u \<le>f concat ws\<close>]
  obtain pu su where "concat ws = pu \<cdot> u \<cdot> su".
  from obtain_fac_interpret[OF this[symmetric] \<open>u \<noteq> \<epsilon>\<close>] that
  show thesis
    using facI' by metis 
qed     

lemma rev_in_set_map_rev_conv: "rev u \<in> set (map rev ws) \<longleftrightarrow> u \<in> set ws"
  by auto

lemma rev_fac_interp: assumes "p u s \<sim>\<^sub>\<I> ws" shows "(rev s) (rev u) (rev p) \<sim>\<^sub>\<I> rev (map rev ws)"
proof (rule fac_interpretI)
  note fac_interpretE[OF assms]
  show \<open>rev s <p hd (rev (map rev ws))\<close>
    using \<open>s <s last ws\<close>
    by (metis \<open>p <p hd ws\<close> \<open>p \<cdot> u \<cdot> s = concat ws\<close> append_is_Nil_conv concat.simps(1) hd_rev last_map list.simps(8) rev_is_Nil_conv strict_suffix_to_prefix)
  show "rev p <s last (rev (map rev ws))"
    using \<open> p <p hd ws\<close>
    by (metis \<open>p \<cdot> u \<cdot> s = concat ws\<close> \<open>s <s last ws\<close> append_is_Nil_conv concat.simps(1) last_rev list.map_sel(1) list.simps(8) rev_is_Nil_conv spref_rev_suf_iff)
  show "rev s \<cdot> rev u \<cdot> rev p = concat (rev (map rev ws))"
    using \<open>p \<cdot> u \<cdot> s = concat ws\<close>
    by (metis append_assoc rev_append rev_concat rev_map)
qed       

lemma rev_fac_interp_iff [reversal_rule]: "(rev s) (rev u) (rev p) \<sim>\<^sub>\<I> rev (map rev ws) \<longleftrightarrow> p u s \<sim>\<^sub>\<I> ws"
  using rev_fac_interp
  by (metis (no_types, lifting) map_rev_involution rev_map rev_rev_ident) 

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
    using bin_code_prefs bin_code_prefs[OF \<open>w1 \<in> \<langle>{u,v}\<rangle>\<close> \<open>p \<le>p w1\<close> \<open>w2 \<in> \<langle>{u,v}\<rangle>\<close> \<open>\<^bold>|v\<^bold>| \<le> \<^bold>|p\<^bold>|\<close>]
      \<open>u \<cdot> p \<le>p v \<cdot> w2\<close> bin_code_prefs
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
  assumes "(u \<cdot> v)\<^sup>@Suc k \<cdot> u = r \<cdot> s" and "(v \<cdot> u)\<^sup>@Suc l \<cdot> v = (s \<cdot> r)\<^sup>@Suc (Suc m)"
  shows "u \<cdot> v =  v \<cdot> u"
proof (rule nemp_comm)
  assume "u \<noteq> \<epsilon>" and "v \<noteq> \<epsilon>" hence "u \<cdot> v \<noteq> \<epsilon>" and "v \<cdot> u \<noteq> \<epsilon>" by blast+
  have "l \<noteq> 0" \<comment> \<open>impossible by a length argument\<close>
  proof (rule notI)
    assume "l = 0"
    hence "v \<cdot> u \<cdot> v = (s \<cdot> r)\<^sup>@ Suc(Suc m)"
      using assms(2) by simp
    from lenarg[OF assms(1)] \<open>u \<noteq> \<epsilon>\<close>
    have "\<^bold>|v \<cdot> u\<^bold>| + \<^bold>|u\<^bold>| \<le> \<^bold>|r \<cdot> s\<^bold>|" 
      unfolding lenmorph pow_len by simp 
    hence "\<^bold>|v \<cdot> u \<cdot> v \<cdot> u\<^bold>| \<le> 2*\<^bold>|r \<cdot> s\<^bold>|"
      unfolding lenmorph pow_len by simp 
    hence "\<^bold>|v \<cdot> u \<cdot> v\<^bold>| < 2*\<^bold>|r \<cdot> s\<^bold>|"
      unfolding lenmorph pow_len using nemp_len[OF \<open>u \<noteq> \<epsilon>\<close>] by linarith
    from this[unfolded \<open>v \<cdot> u \<cdot> v = (s \<cdot> r)\<^sup>@ Suc(Suc m)\<close>]
    show False
      unfolding lenmorph pow_len by simp
  qed
    \<comment> \<open>we can therefore use the Periodicity lemma\<close>
  then obtain l' where "l = Suc l'"
    using not0_implies_Suc by auto
  let ?w = "(v \<cdot> u)\<^sup>@Suc l \<cdot> v"
  have per1: "?w \<le>p (v \<cdot> u) \<cdot> ?w"
    using \<open>v \<cdot> u \<noteq> \<epsilon>\<close>  per_rootD[of ?w "v \<cdot> u", unfolded per_eq] by blast
  have per2: "?w \<le>p (s \<cdot> r) \<cdot> ?w"
    unfolding  assms(2) using pref_pow_ext' by blast 
  have len: "\<^bold>|v \<cdot> u\<^bold>| + \<^bold>|s \<cdot> r\<^bold>|  \<le> \<^bold>|?w\<^bold>|"
  proof-
    have  len1: "2*\<^bold>|s \<cdot> r\<^bold>| \<le> \<^bold>|?w\<^bold>|"
      unfolding \<open>(v \<cdot> u)\<^sup>@Suc l \<cdot> v = (s \<cdot> r)\<^sup>@Suc (Suc m)\<close> lenmorph pow_len by simp
    moreover have len2: "2*\<^bold>|v \<cdot> u\<^bold>|  \<le> \<^bold>|?w\<^bold>|"
      unfolding lenmorph pow_len \<open>l = Suc l'\<close> by simp 
    ultimately show ?thesis
      using len1 len2 by linarith
  qed
  from two_pers[OF per1 per2 len]
  have "(v \<cdot> u) \<cdot> (s \<cdot> r) = (s \<cdot> r) \<cdot> (v \<cdot> u)".
  hence "(v \<cdot> u)\<^sup>@Suc l \<cdot> (s \<cdot> r)\<^sup>@Suc (Suc m) = (s \<cdot> r)\<^sup>@Suc (Suc m) \<cdot> (v \<cdot> u)\<^sup>@Suc l"
    using comm_add_exps by blast
  from comm_drop_exp'[OF this[folded assms(2), unfolded rassoc cancel]]
  show "u \<cdot> v = v \<cdot> u"
    unfolding rassoc cancel.
qed

lemma conj_pers_conj_comm: assumes "\<rho> (v \<cdot> (u \<cdot> v)\<^sup>@(Suc k)) \<sim> \<rho> ((u \<cdot> v)\<^sup>@(Suc m) \<cdot> u)"
  shows "u \<cdot> v = v \<cdot> u"
proof (rule nemp_comm)
  let ?v = "v \<cdot> (u \<cdot> v)\<^sup>@(Suc k)" and ?u = "(u \<cdot> v)\<^sup>@(Suc m) \<cdot> u"
  assume "u \<noteq> \<epsilon>" and "v \<noteq> \<epsilon>"
  hence "u \<cdot> v \<noteq> \<epsilon>" and "?v \<noteq> \<epsilon>" and "?u \<noteq> \<epsilon>" by simp_all
  obtain r s where "r \<cdot> s = \<rho> ?v" and "s \<cdot> r = \<rho> ?u"
    using conjugE[OF assms]. 
  then obtain k1 k2 where "?v = (r \<cdot> s)\<^sup>@Suc k1" and "?u = (s \<cdot> r)\<^sup>@Suc k2"
    using primroot_expE[OF  \<open>?v \<noteq> \<epsilon>\<close>] primroot_expE[OF \<open>?u \<noteq> \<epsilon>\<close>] by metis 
  hence eq: "(s \<cdot> r)\<^sup>@Suc k2 \<cdot> (r \<cdot> s)\<^sup>@Suc k1 = (u \<cdot> v)\<^sup>@(Suc m + Suc 0 + Suc k)" 
    unfolding add_exps pow_one rassoc by simp
  have ineq: "2 \<le> Suc m + Suc 0 + Suc k"
    by simp
  consider (two_two) "2 \<le> Suc k1 \<and> 2 \<le> Suc k2"|
    (one_one) "Suc k1 = 1 \<and> Suc k2 = 1" |
    (two_one) "2 \<le> Suc k1 \<and> Suc k2 = 1" |
    (one_two) "Suc k1 = 1 \<and> 2 \<le> Suc k2"
    unfolding numerals One_nat_def Suc_le_mono by fastforce    
  then show "u \<cdot> v = v \<cdot> u" 
  proof (cases)
    case (two_two)
    with Lyndon_Schutzenberger(1)[OF eq _ _ ineq]
    have "(s \<cdot> r) \<cdot> (r \<cdot> s) = (r \<cdot> s) \<cdot> (s \<cdot> r)"
      using eqd_eq[of "s \<cdot> r" "r \<cdot> s" "r \<cdot> s" "s \<cdot> r"] by fastforce

    from comm_add_exps[OF this, of "Suc k2" "Suc k1", folded \<open>?v = (r \<cdot> s)\<^sup>@Suc k1\<close> \<open>?u = (s \<cdot> r)\<^sup>@Suc k2\<close>, folded shift_pow, unfolded pow_Suc]
    have "(u \<cdot> v) \<cdot> ((u \<cdot> v) \<^sup>@ m \<cdot> u) \<cdot> ((v \<cdot> u) \<cdot> (v \<cdot> u) \<^sup>@ k \<cdot> v) = (v \<cdot> u) \<cdot> (((v \<cdot> u) \<^sup>@ k) \<cdot> v) \<cdot> ((u \<cdot> v) \<cdot> (u \<cdot> v) \<^sup>@ m \<cdot> u)"
      unfolding rassoc.
    from eqd_eq[OF this, unfolded lenmorph]
    show "u \<cdot> v =  v \<cdot> u"
      by fastforce
  next
    case (one_one)
    hence "(s \<cdot> r) \<^sup>@ Suc k2 \<cdot> (r \<cdot> s) \<^sup>@ Suc k1 = (s \<cdot> r) \<cdot> (r \<cdot> s)" 
      using pow_one by simp
    from eq[unfolded conjunct1[OF one_one] conjunct2[OF one_one] pow_one']
         pow_nemp_imprim[OF ineq, folded eq[unfolded this]] 
         Lyndon_Schutzenberger_conjug[of "s \<cdot> r" "r \<cdot> s", OF conjugI']  
    have "(s \<cdot> r) \<cdot> (r \<cdot> s) = (r \<cdot> s) \<cdot> (s \<cdot> r)" by metis

    from comm_add_exps[OF this, of "Suc k2" "Suc k1", folded \<open>?v = (r \<cdot> s)\<^sup>@Suc k1\<close> \<open>?u = (s \<cdot> r)\<^sup>@Suc k2\<close>, folded shift_pow, unfolded pow_Suc]
    have "(u \<cdot> v) \<cdot> ((u \<cdot> v) \<^sup>@ m \<cdot> u) \<cdot> ((v \<cdot> u) \<cdot> (v \<cdot> u) \<^sup>@ k \<cdot> v) = (v \<cdot> u) \<cdot> (((v \<cdot> u) \<^sup>@ k) \<cdot> v) \<cdot> ((u \<cdot> v) \<cdot> (u \<cdot> v) \<^sup>@ m \<cdot> u)"
      unfolding rassoc.
    from eqd_eq[OF this, unfolded lenmorph]
    show "u \<cdot> v =  v \<cdot> u"
      by fastforce
  next
    case (two_one)
    hence "?u = s \<cdot> r"
      using \<open>?u = (s \<cdot> r)\<^sup>@Suc k2\<close> by simp
    obtain l where "Suc k1 = Suc (Suc l)"
      using conjunct1[OF two_one, unfolded numerals(2)] Suc_le_D le_Suc_eq by metis 
    from \<open>?v = (r \<cdot> s)\<^sup>@Suc k1\<close>[folded shift_pow, unfolded this]  
    have "(v \<cdot> u) \<^sup>@ Suc k \<cdot> v = (r \<cdot> s)\<^sup>@Suc (Suc l)".
    from conj_pers_conj_comm_aux[OF \<open>?u = s \<cdot> r\<close> this]
    show "u \<cdot> v = v \<cdot> u".
  next
    case (one_two)
    hence "?v = r \<cdot> s"
      using \<open>?v = (r \<cdot> s)\<^sup>@Suc k1\<close> by simp
    obtain l where "Suc k2 = Suc (Suc l)"
      using conjunct2[OF one_two, unfolded numerals(2)] Suc_le_D le_Suc_eq by metis 
    from \<open>?u = (s \<cdot> r)\<^sup>@Suc k2\<close>[unfolded this]  
    have "(u \<cdot> v) \<^sup>@ Suc m \<cdot> u = (s \<cdot> r) \<^sup>@ Suc (Suc l)".
    from conj_pers_conj_comm_aux[OF \<open>?v = r \<cdot> s\<close>[folded shift_pow] this, symmetric] 
    show "u \<cdot> v = v \<cdot> u".
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
  from this primroot_prim[OF \<open>v \<noteq> \<epsilon>\<close>]
  obtain r where "r = \<rho> v" and "r = \<rho> p'" and "primitive r"
    unfolding comm_primroots[OF \<open>v \<noteq> \<epsilon>\<close> \<open>p' \<noteq> \<epsilon>\<close>] by blast+  
  have "w \<in> \<langle>{u, v}\<rangle>" by fact
  obtain m where "p' = r\<^sup>@m \<cdot> r"
    using   primroot_expE[OF \<open>p' \<noteq> \<epsilon>\<close>, folded \<open>r = \<rho> p'\<close>] power_Suc2 by metis
  hence "(u \<cdot> r\<^sup>@m) \<cdot> r \<le>s (r \<cdot> w) \<cdot> u"
    using \<open>u \<cdot> p' = p \<cdot> u\<close> \<open>p \<le>s w\<close> unfolding suf_def by force

  note mismatch_rule = mismatch_suf_comm_len[OF _ _ _ this, of "u \<cdot> r\<^sup>@m"]
  have "u \<cdot> r = r \<cdot> u"
  proof (rule mismatch_rule)  
    have "w \<in> \<langle>{r, u}\<rangle>" 
      using \<open>w \<in> \<langle>{u, v}\<rangle>\<close> \<open>r = \<rho> v\<close> \<open>v \<noteq> \<epsilon>\<close> doubleton_eq_iff gen_prim by metis
    thus "r \<cdot> w \<in> \<langle>{r, u}\<rangle>" by blast 
    show "\<^bold>|u\<^bold>| \<le> \<^bold>|u \<cdot> r \<^sup>@ m\<^bold>|" by simp
    show "u \<cdot> r\<^sup>@m \<in> \<langle>{r, u}\<rangle>"
      by (simp add: gen_in hull.prod_cl power_in) 
  qed simp
  thus "u \<cdot> v = v \<cdot> u"
    using \<open>r = \<rho> v\<close> comm_primroot_conv by auto
qed

lemmas uv_fac_uvv_suf = uv_fac_uvv[reversed, unfolded rassoc]

lemma assumes "p \<cdot> u \<cdot> v \<cdot> u \<cdot> q = u \<cdot> v \<cdot> v \<cdot> u" and "p \<noteq> \<epsilon>" and "q \<noteq> \<epsilon>"
  shows "u \<cdot> v = v \<cdot> u"
  oops \<comment> \<open>counterexample: v = abaaba, u = a, p = aab, q = baa; aab.a.abaaba.a.baa = a.abaaba.abaaba.a\<close>

lemma uvu_pref_uvv: assumes "p \<cdot> u \<cdot> v \<cdot> v \<cdot> s = u \<cdot> v \<cdot> u \<cdot> q" and
  "p <p u" and "q \<le>p w" and  "s \<le>p  w'" and 
  "w \<in> \<langle>{u,v}\<rangle>" and "w' \<in> \<langle>{u,v}\<rangle>" and "\<^bold>|u\<^bold>| \<le> \<^bold>|s\<^bold>|"
shows "u \<cdot> v = v \<cdot> u"
proof(rule nemp_comm)
  \<comment> \<open>Preliminaries\<close>
  assume "u \<noteq> \<epsilon>" and "v \<noteq> \<epsilon>"
  hence "u \<cdot> v \<noteq> \<epsilon>" by blast
  have "\<^bold>|p \<cdot> u \<cdot> v\<^bold>| \<le> \<^bold>|u \<cdot> v \<cdot> u\<^bold>|"
    using \<open>p <p u\<close> unfolding lenmorph  by (simp add: prefix_length_less less_imp_le)

\<comment> \<open>p commutes with @{term "u \<cdot> v"}\<close>  
  have "p \<cdot> (u \<cdot> v) = (u \<cdot> v) \<cdot> p"
    by (rule pref_marker[of "u \<cdot> v \<cdot> u"], simp, rule eq_le_pref, unfold rassoc, fact+)

\<comment> \<open>equality which will yield the main result\<close>
  have "p \<cdot> v \<cdot> s = u  \<cdot> q" 
  proof- 
    have "((u \<cdot> v) \<cdot> p) \<cdot> v \<cdot>  s = (u \<cdot> v) \<cdot> u \<cdot> q"
      unfolding \<open>p \<cdot> u \<cdot> v = (u \<cdot> v) \<cdot> p\<close>[symmetric] unfolding rassoc by fact 
    from this[unfolded rassoc cancel]
    show ?thesis.
  qed
  hence "p \<cdot> v \<cdot> s \<le>p u \<cdot> w"
    using \<open>q \<le>p w\<close> by force

  then show "u \<cdot> v = v \<cdot> u"
  proof (cases "p = \<epsilon>")
    assume "p = \<epsilon>"
    thm mismatch_pref_comm 
    note local_rule = mismatch_pref_comm_len[OF _ _ \<open>s \<le>p w'\<close> _ \<open>\<^bold>|u\<^bold>| \<le> \<^bold>|s\<^bold>|\<close>, of v w, symmetric]
    show "u \<cdot> v = v \<cdot> u"
    proof (rule local_rule)
      show "w \<in> \<langle>{v, u}\<rangle>"
        using \<open>w \<in> \<langle>{u,v}\<rangle>\<close> by (simp add: insert_commute) 
      show "v \<cdot> s \<le>p u \<cdot> w"
        using \<open>p = \<epsilon>\<close> \<open>p \<cdot> v \<cdot> s = u \<cdot> q\<close> \<open>q \<le>p w\<close> by simp 
      show "w' \<in> \<langle>{v, u}\<rangle>" 
        using \<open>w' \<in> \<langle>{u, v}\<rangle>\<close> insert_commute by metis 
    qed 
  next
    assume "p \<noteq> \<epsilon>" 
    show "u \<cdot> v = v \<cdot> u"
    proof (rule ccontr)
      obtain r where "r = \<rho> p" and "r = \<rho> (u \<cdot> v)"
        using  \<open>p \<cdot> u \<cdot> v = (u \<cdot> v) \<cdot> p\<close>[symmetric, unfolded comm_primroots[OF \<open>u \<cdot> v \<noteq> \<epsilon>\<close> \<open>p \<noteq> \<epsilon>\<close>]] by blast
      obtain k m where "r\<^sup>@k = p" and "r\<^sup>@m = u \<cdot> v"
        using \<open>u \<cdot> v \<noteq> \<epsilon>\<close> \<open>p \<noteq> \<epsilon>\<close> \<open>r = \<rho> p\<close> \<open>r = \<rho> (u \<cdot> v)\<close> primroot_expE by metis 
          \<comment> \<open>Idea:
        maximal r-prefix of @{term "p \<cdot> v \<cdot> s"} is @{term "p \<cdot> bin_code_lcp"}, since the maximal r-prefix of 
        @{term "v \<cdot> u"} is @{term "v \<cdot> u \<and>\<^sub>p u \<cdot> v"};
        on the other hand, maximal r-prefix of @{term "u \<cdot> w \<cdot> bin_code_lcp"} is at least @{term "u \<cdot> bin_code_lcp"}, 
        since this is, in particular, a prefix of @{term "u \<cdot> v \<cdot> u \<cdot> v \<in> r*"}\<close> 
      assume "u \<cdot> v \<noteq> v \<cdot> u"                                    
      then interpret binary_code u v
        by (unfold_locales)
      term "p \<cdot> v \<cdot> s = u  \<cdot> q"
      have "p \<cdot> bin_code_lcp \<cdot> [bin_code_mismatch_snd] \<le>p u \<cdot> w \<cdot> bin_code_lcp"
      proof-
        have "p \<cdot> bin_code_lcp \<cdot> [bin_code_mismatch_snd] \<le>p p \<cdot> v \<cdot> w' \<cdot> bin_code_lcp"
          unfolding pref_cancel_conv
          using pref_prolong[OF  bin_snd_mismatch bin_lcp_pref_all_hull, OF \<open>w' \<in> \<langle>{u,v}\<rangle>\<close>].
        note local_rule = ruler_le[OF this] 
        have "p \<cdot> bin_code_lcp \<cdot> [bin_code_mismatch_snd] \<le>p p \<cdot> v \<cdot> s"
        proof (rule local_rule)
          show "p \<cdot> v \<cdot> s \<le>p p \<cdot> v \<cdot> w' \<cdot> bin_code_lcp"
            using \<open>s \<le>p w'\<close> by fastforce 
          show "\<^bold>|p \<cdot> bin_code_lcp \<cdot> [bin_code_mismatch_snd]\<^bold>| \<le> \<^bold>|p \<cdot> v \<cdot> s\<^bold>|"
            using bin_lcp_short \<open>\<^bold>|u\<^bold>| \<le> \<^bold>|s\<^bold>|\<close>  by force
        qed
        from pref_ext[OF pref_trans[OF this \<open>p \<cdot> v \<cdot> s \<le>p u \<cdot> w\<close>]]
        show "p \<cdot> bin_code_lcp \<cdot> [bin_code_mismatch_snd] \<le>p u \<cdot> w \<cdot> bin_code_lcp"
          by force
      qed
      moreover 
      have "p \<cdot> bin_code_lcp \<cdot> [bin_code_mismatch_fst] \<le>p u \<cdot> w \<cdot> bin_code_lcp" 
      proof (rule pref_trans[of _ "u \<cdot> bin_code_lcp"])
        show "u \<cdot> bin_code_lcp \<le>p u \<cdot> w \<cdot> bin_code_lcp"
          using  bin_lcp_pref_all_hull[OF \<open>w \<in> \<langle>{u,v}\<rangle>\<close>]  by auto
        show "p \<cdot> bin_code_lcp \<cdot> [bin_code_mismatch_fst] \<le>p u \<cdot> bin_code_lcp"  
        proof (rule ruler_le)
          show "\<^bold>|p \<cdot> bin_code_lcp \<cdot> [bin_code_mismatch_fst]\<^bold>| \<le> \<^bold>|u \<cdot> bin_code_lcp\<^bold>|"
            unfolding lenmorph using prefix_length_less[OF \<open>p <p u\<close>] by simp
          show "u \<cdot> bin_code_lcp \<le>p r \<^sup>@ (m + m)"
            unfolding add_exps \<open>r\<^sup>@m = u \<cdot> v\<close> rassoc pref_cancel_conv
            using bin_lcp_pref_snd_fst pref_prolong prefix_def by metis
          show "p \<cdot> bin_code_lcp \<cdot> [bin_code_mismatch_fst] \<le>p r \<^sup>@ (m + m)"
          proof (rule pref_trans)
            show "p \<cdot> bin_code_lcp \<cdot> [bin_code_mismatch_fst] \<le>p r\<^sup>@(k+m)"
              unfolding  power_add  \<open>r \<^sup>@ k = p\<close> \<open>r \<^sup>@ m = u \<cdot> v\<close> pref_cancel_conv 
              using bin_fst_mismatch'.
            show "r \<^sup>@ (k + m) \<le>p r \<^sup>@ (m + m)"
              unfolding  power_add  \<open>r \<^sup>@ k = p\<close> \<open>r \<^sup>@ m = u \<cdot> v\<close> \<open>p \<cdot> u \<cdot> v = (u \<cdot> v) \<cdot> p\<close> 
              using \<open>p <p u\<close> by force  
          qed
        qed
      qed
      ultimately show False
        using  bin_mismatch_neq by (force simp add: prefix_def)
    qed
  qed
qed

lemma uvu_pref_uvvu: assumes "p \<cdot> u \<cdot> v \<cdot> v \<cdot> u = u \<cdot> v \<cdot> u \<cdot> q" and
  "p <p u" and "q \<le>p w" and  " w \<in> \<langle>{u,v}\<rangle>"
shows "u \<cdot> v = v \<cdot> u"
  using uvu_pref_uvv[OF \<open>p \<cdot> u \<cdot> v \<cdot> v \<cdot> u = u \<cdot> v \<cdot> u \<cdot> q\<close> \<open>p <p u\<close> \<open>q \<le>p w\<close> _ \<open>w \<in> \<langle>{u,v}\<rangle>\<close>, of u]
  by blast


lemma uvu_pref_uvvu_interpret: assumes interp: "p u \<cdot> v \<cdot> v \<cdot> u s \<sim>\<^sub>\<I> ws" and
  "[u, v, u] \<le>p  ws" and "ws \<in> lists {u,v}"
shows "u \<cdot> v = v \<cdot> u"
proof-
  note fac_interpretE[OF interp]
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
    show "p <p u"
      using \<open>p <p hd ws\<close> pref_hd_eq[OF \<open>[u, v, u] \<le>p  ws\<close> list.distinct(1)[of u "[v,u]", symmetric]]
      by force
    have "p \<cdot> u \<cdot> v \<cdot> v \<cdot> u \<cdot> s = u \<cdot> v \<cdot> u \<cdot> (concat ws'\<^sup><\<inverse>s) \<cdot> s"
      using \<open>p \<cdot> u \<cdot> v \<cdot> v \<cdot> u \<cdot> s = u \<cdot> v \<cdot> u \<cdot> concat ws'\<close> unfolding rq_suf[OF \<open>s \<le>s concat ws'\<close>]. 
    thus "p \<cdot> u \<cdot> v \<cdot> v \<cdot> u = u \<cdot> v \<cdot> u \<cdot> concat ws'\<^sup><\<inverse>s" 
      by simp
    show "concat ws' \<in> \<langle>{u,v}\<rangle>"
      using \<open>ws' \<in> lists {u,v}\<close> by blast
    show "concat ws'\<^sup><\<inverse>s  \<le>p concat ws'"
      using rq_suf[OF \<open>s \<le>s concat ws'\<close>] by fast
  qed auto  
qed

lemmas uvu_suf_uvvu = uvu_pref_uvvu[reversed, unfolded rassoc] and
  uvu_suf_uvv = uvu_pref_uvv[reversed, unfolded rassoc]

lemma uvu_suf_uvvu_interp: "p u \<cdot> v \<cdot> v \<cdot> u s \<sim>\<^sub>\<I> ws \<Longrightarrow> [u, v, u] \<le>s  ws
  \<Longrightarrow> ws \<in> lists {u,v} \<Longrightarrow> u \<cdot> v = v \<cdot> u"
  by (rule uvu_pref_uvvu_interpret[reversed, unfolded rassoc clean_emp, symmetric, of p u v s ws], 
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
      using hull.cases[OF \<open>w1 \<in> \<langle>{r\<cdot>s,s\<cdot>r}\<rangle>\<close>]  empty_iff insert_iff mult_assoc \<open>w1 \<in> \<langle>{r \<cdot> s, s \<cdot> r}\<rangle>\<close> by metis  
    hence "w1' \<in> \<langle>{r\<cdot>s,s\<cdot>r}\<rangle>" and cases1: "(w1 = \<epsilon> \<or> w1 = r \<cdot> s \<cdot> w1' \<or> w1 = s \<cdot> r \<cdot> w1')" by blast+
    hence "w1' \<in> \<langle>{r,s}\<rangle>" by force
    obtain w2' where "(w2 = \<epsilon> \<or> w2 = r \<cdot> s \<cdot> w2' \<or> w2 = s \<cdot> r \<cdot> w2') \<and> w2' \<in> \<langle>{r\<cdot>s,s\<cdot>r}\<rangle>"
      using hull.cases[OF \<open>w2 \<in> \<langle>{r\<cdot>s,s\<cdot>r}\<rangle>\<close>]  empty_iff insert_iff mult_assoc \<open>w1 \<in> \<langle>{r \<cdot> s, s \<cdot> r}\<rangle>\<close> by metis  
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
          using \<open>r \<cdot> w1 = w2 \<cdot> s\<close>[unfolded rs1 empty2 rassoc clean_emp] \<open>r \<noteq> \<epsilon>\<close>
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
          using \<open>r \<cdot> w1 = w2 \<cdot> s\<close>[unfolded sr2 empty1 rassoc cancel clean_emp, symmetric] \<open>s \<noteq> \<epsilon>\<close> fac_triv by blast 
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
    using primroot_idemp[OF \<open>v \<cdot> u \<noteq> \<epsilon>\<close>, unfolded \<open>\<rho> (v \<cdot> u) = s \<cdot> r\<close>].
  obtain n where "(r \<cdot> s)\<^sup>@Suc n = u \<cdot> v"
    using  primroot_expE[OF \<open>u \<cdot> v \<noteq> \<epsilon>\<close>, unfolded \<open>\<rho> (u \<cdot> v) = r \<cdot> s\<close>].
  obtain n' where "(s \<cdot> r)\<^sup>@Suc n' = v \<cdot> u"
    using  primroot_expE[OF \<open>v \<cdot> u \<noteq> \<epsilon>\<close>, unfolded \<open>\<rho> (v \<cdot> u) = s \<cdot> r\<close>].
  have "(s \<cdot> u) \<cdot> (s \<cdot> r) = (s \<cdot> r) \<cdot> (s \<cdot> u)"
  proof (rule pref_marker)
    show "(s \<cdot> u) \<cdot> s \<cdot> r \<le>p s \<cdot> (r \<cdot> s)\<^sup>@(Suc n+ Suc n)"
      unfolding rassoc add_exps \<open>(r \<cdot> s)\<^sup>@Suc n = u \<cdot> v\<close> 
      unfolding lassoc \<open>(s \<cdot> r)\<^sup>@Suc n' = v \<cdot> u\<close>[symmetric] pow_Suc by force
    have aux: "(s \<cdot> r) \<cdot> s \<cdot> (r \<cdot> s) \<^sup>@ (Suc n + Suc n) = s \<cdot> (r \<cdot> s)\<^sup>@(Suc  n + Suc n) \<cdot> (r \<cdot> s)"
      by (simp add: pow_comm)
    show "s \<cdot> (r \<cdot> s) \<^sup>@ (Suc n + Suc n) \<le>p (s \<cdot> r) \<cdot> s \<cdot> (r \<cdot> s) \<^sup>@ (Suc n + Suc n)"
      unfolding aux pref_cancel_conv by blast
  qed
  from comm_primroot_exp[OF primroot_nemp[OF \<open>v \<cdot> u \<noteq> \<epsilon>\<close>, unfolded \<open>\<rho> (v \<cdot> u) = s \<cdot> r\<close>] this]
  obtain k where "(s \<cdot> r)\<^sup>@Suc k = s \<cdot> u"
    using  nemp_pow_SucE[OF suf_nemp[OF \<open>u \<noteq> \<epsilon>\<close>, of s]] \<open>\<rho> (s \<cdot> r) =  s \<cdot> r\<close> by metis
  hence u: "(r \<cdot> s)\<^sup>@k \<cdot> r = u"
    unfolding pow_Suc rassoc cancel shift_pow by fast
  from exp_pref_cancel[OF \<open>(r \<cdot> s)\<^sup>@Suc n = u \<cdot> v\<close>[folded this, unfolded rassoc, symmetric]]
  have "r \<cdot> v = (r \<cdot> s) \<^sup>@ (Suc n - k)".   
  from nemp_pow_SucE[OF _ this]
  obtain m where "r \<cdot> v = (r \<cdot> s)\<^sup>@Suc m"
    using \<open>r \<noteq> \<epsilon>\<close> by blast 
  from this[unfolded pow_Suc rassoc cancel shift_pow[symmetric], symmetric]
  have v: "(s \<cdot> r)\<^sup>@m \<cdot> s = v".
  show thesis
    using that[OF u v].
qed      

subsection \<open>Predicate ``commutes''\<close>

definition commutes :: "'a list set \<Rightarrow> bool"
  where "commutes A = (\<forall>x y. x \<in> A \<longrightarrow> y \<in> A \<longrightarrow> x\<cdot>y = y\<cdot>x)"

lemma commutesE: "commutes A \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x\<cdot>y = y\<cdot>x"
  using commutes_def by blast

lemma commutes_root: assumes "commutes A"
  obtains r where "\<And>x. x \<in> A \<Longrightarrow> x \<in> r*"
  using assms comm_primroots emp_all_roots primroot_is_root
  unfolding commutes_def
  by metis

lemma commutes_primroot: assumes "commutes A"
  obtains r where "\<And>x. x \<in> A \<Longrightarrow> x \<in> r*" and "primitive r"
  using commutes_root[OF assms] emp_all_roots prim_sing 
    primroot_is_root primroot_prim root_trans
  by metis

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

lemma commutesI_root: "\<forall>x \<in> A. x \<in> t* \<Longrightarrow> commutes A"
  by (meson comm_root commutesI)

lemma commutes_sub: "commutes A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> commutes B"
  by (simp add: commutes_def subsetD)

lemma commutes_insert: "commutes A \<Longrightarrow> x \<in> A \<Longrightarrow> x \<noteq> \<epsilon> \<Longrightarrow>  x\<cdot>y = y\<cdot>x \<Longrightarrow> commutes (insert y A)"
  using commutesE[of A x] commutesI'[of x "insert y A"] insertE
  by blast

lemma commutes_emp [simp]: "commutes {\<epsilon>, w}"
  by (simp add: commutes_def)

lemma commutes_emp'[simp]: "commutes {w, \<epsilon>}" 
  by (simp add: commutes_def)

lemma commutes_cancel: "commutes (insert y (insert (x \<cdot> y) A)) \<Longrightarrow> commutes (insert y (insert x A))"
proof
  fix u v 
  assume com: "commutes (insert y (insert (x \<cdot> y) A))" and
         "u \<in> insert y (insert x A)" "v \<in> insert y (insert x A)"
  then consider "u = y" | "u = x" | "u \<in> A"
    by blast
  note u_cases = this
  consider "v = y" | "v = x" | "v \<in> A"
    using \<open>v \<in> insert y (insert x A)\<close> by blast
  note v_cases = this
  have "y \<cdot> (x \<cdot> y) = (x \<cdot> y) \<cdot> y" 
    using \<open>commutes (insert y (insert (x \<cdot> y) A))\<close> commutesE by blast 
  hence "x \<cdot> y = y \<cdot> x" 
    by simp
  have[simp]: "w \<in> A \<Longrightarrow> y \<cdot> w = w \<cdot> y" for w
    using com by (simp add: commutesE) 
  hence[simp]: "w \<in> A \<Longrightarrow> x \<cdot> w = w \<cdot> x" for w
    using \<open>x \<cdot> y = y \<cdot> x\<close>  com commutesE
    comm_trans insertCI shifts_rev(37) by metis 
  have[simp]: "u \<in> A \<Longrightarrow> v \<in> A \<Longrightarrow> u \<cdot> v = v \<cdot> u"
     using com commutesE by blast
  show "u \<cdot> v = v \<cdot> u"
    by (rule u_cases, (rule v_cases, simp_all add: \<open>x \<cdot> y = y \<cdot> x\<close> com)+)
qed


subsection \<open>Strong elementary lemmas\<close>

text\<open>Discovered by smt\<close>

lemma xyx_per_comm: assumes "x\<cdot>y\<cdot>x \<le>p q\<cdot>x\<cdot>y\<cdot>x"
  and "q \<noteq> \<epsilon>" and "q \<le>p y \<cdot> q"
shows "x\<cdot>y = y\<cdot>x"
  (* by (smt (verit, best) assms(1) assms(2) assms(3) pref_cancel pref_cancel' pref_marker pref_prolong prefix_same_cases root_comm_root triv_pref) *) 
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

lemma two_elem_root_suf_comm': assumes "u \<le>p v \<cdot> u" and "q \<le>s p" and "q \<cdot> u \<cdot> v = v \<cdot> q \<cdot> u" and "p \<in> \<langle>{u,v}\<rangle>"
  shows "u \<cdot> v = v \<cdot> u"
proof (rule nemp_comm)
  assume "u \<noteq> \<epsilon>" and "v \<noteq> \<epsilon>" 
  have "p \<in> \<langle>{u, \<rho> v}\<rangle>"
    using gen_prim[OF \<open>v \<noteq> \<epsilon>\<close> \<open>p \<in> \<langle>{u,v}\<rangle>\<close>].

  have "(q \<cdot> u) \<cdot> v = v \<cdot> (q \<cdot> u)"
    using \<open>q \<cdot> u \<cdot> v = v \<cdot> q \<cdot> u\<close> by fastforce
  hence "(q \<cdot> u) \<cdot> \<rho> v = \<rho> v \<cdot> (q \<cdot> u)"
    unfolding comm_primroot_conv[OF \<open>v \<noteq> \<epsilon>\<close>].

  have "u \<le>p \<rho> v \<cdot> u"
    using \<open>u \<le>p v \<cdot> u\<close> \<open>v \<noteq> \<epsilon>\<close> comm_primroot_conv root_comm_root by metis 

  have "\<rho> v \<le>s q \<cdot> u"
    using suf_nemp[OF \<open>u \<noteq> \<epsilon>\<close>] primroot_suf \<open>(q \<cdot> u) \<cdot> v = v \<cdot> q \<cdot> u\<close> \<open>v \<noteq> \<epsilon>\<close> comm_primroots by metis
  hence "\<rho> v \<le>s p \<cdot> u"
    using suf_trans \<open>q \<le>s p\<close> by (auto simp add: suf_def)

  from two_elem_root_suf_comm[OF \<open>u \<le>p \<rho> v \<cdot> u\<close> this \<open>p \<in> \<langle>{u,\<rho> v}\<rangle>\<close>]
  have "u \<cdot> \<rho> v = \<rho> v \<cdot> u".
  thus "u \<cdot> v = v \<cdot> u"
    using \<open>v \<noteq> \<epsilon>\<close> comm_primroot_conv by metis
qed


subsection \<open>Binary words without a letter square\<close>

lemma no_repetition_list:  
  assumes "set ws \<subseteq> {a,b}"
    and not_per:  "\<not> ws \<le>p [a,b] \<cdot> ws" "\<not> ws \<le>p [b,a] \<cdot> ws"
    and not_square:  "\<not> [a,a] \<le>f ws" and "\<not> [b,b] \<le>f ws" 
  shows False
  using assms
proof (induction ws, simp)
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
qed

lemma hd_Cons_append[intro,simp]: "hd ((a#v) \<cdot> u) = a" 
  by simp

lemma no_repetition_list_bin:  
  fixes ws :: "binA list"
  assumes not_square:  "\<And> c. \<not> [c,c] \<le>f ws" 
  shows "ws \<le>p [hd ws, 1-(hd ws)] \<cdot> ws"
proof (cases "ws = \<epsilon>", simp)
  assume "ws \<noteq> \<epsilon>"
  have set: "set ws \<subseteq> {hd ws, 1-hd ws}"
    using swap_UNIV by auto 
  have "\<not> ws \<le>p [1 - hd ws, hd ws] \<cdot> ws"
    using pref_hd_eq[OF _ \<open>ws \<noteq> \<epsilon>\<close>, of "[1 - hd ws, hd ws] \<cdot> ws"] bin_swap_neq'
    unfolding hd_Cons_append by blast 
  from no_repetition_list[OF set _ this not_square not_square] 
  show "ws \<le>p [hd ws, 1-(hd ws)] \<cdot> ws" by blast  
qed

lemma per_root_hd_last_root: assumes "ws \<le>p [a,b] \<cdot> ws" and "hd ws \<noteq> last ws" 
  shows "ws \<in> [a,b]*"
  using assms
proof (induction "\<^bold>|ws\<^bold>|" arbitrary: ws rule: less_induct)
  case less
  then show ?case
  proof (cases "ws = \<epsilon>", simp)
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
    have "tl (tl ws) \<in> [a, b]*"
    proof (cases "tl (tl ws) = \<epsilon>", simp)
      assume "tl (tl ws) \<noteq> \<epsilon>"
      from pref_hd_eq[OF \<open>tl (tl ws) \<le>p [a, b] \<cdot> tl (tl ws)\<close> this]
      have "hd (tl (tl ws)) = a" by simp
      have "last (tl (tl ws)) = last ws"
        using \<open>tl (tl ws) \<noteq> \<epsilon>\<close> last_tl tl_Nil by metis 
      from \<open>hd ws \<noteq> last ws\<close>[unfolded \<open>hd ws =a\<close>, folded this \<open>hd (tl (tl ws)) = a\<close>]
      have "hd (tl (tl ws)) \<noteq> last (tl (tl ws))".
      from less.hyps[OF ind \<open>tl (tl ws) \<le>p [a,b] \<cdot> tl (tl ws)\<close> this]
      show "tl (tl ws) \<in> [a, b]*".
    qed
    thus "ws \<in> [a,b]*"
      unfolding add_root[of "[a,b]" "tl(tl ws)", symmetric]
       *[folded \<open>[a,b] = [hd ws, hd (tl ws)]\<close> ].
  qed
qed

lemma no_cyclic_repetition_list: 
  assumes  "set ws \<subseteq> {a,b}" "ws \<notin> [a,b]*" "ws \<notin> [b,a]*" "hd ws \<noteq> last ws"
    "\<not> [a,a] \<le>f ws" "\<not> [b,b] \<le>f ws" 
  shows False
  using per_root_hd_last_root[OF _ \<open>hd ws \<noteq> last ws\<close>] \<open>ws \<notin> [a,b]*\<close> \<open>ws \<notin> [b,a]*\<close>
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
    v: "v = [0::nat]" and 
    t: "t = ([1] \<cdot> [0]\<^sup>@Suc j)\<^sup>@Suc (m + l) \<cdot> [1,0] " and
    r: "r = [0,1] \<cdot> ([0]\<^sup>@Suc j \<cdot> [1])\<^sup>@Suc (m + l)" and
    t': "t' = ([1] \<cdot> [0]\<^sup>@Suc j)\<^sup>@m \<cdot> [1,0] " and
    r': "r' = [0,1] \<cdot> ([0]\<^sup>@Suc j \<cdot> [1])\<^sup>@l" and
    w: "w = [0] \<cdot> ([1] \<cdot> [0]\<^sup>@Suc j)\<^sup>@Suc (m + l) \<cdot> [1,0]"
  shows "w = v \<cdot> t" and "w = r \<cdot> v" and "w = r' \<cdot> v\<^sup>@Suc j \<cdot> t'" and "t' <p t" and "r' <s r"
proof-
  show "w = v \<cdot> t"
    unfolding w v t..
  show "w = r \<cdot> v"
    unfolding  w r v by comparison
  show "t' <p t"
    unfolding t t' pow_Suc2[of _ "m+l"] add_exps rassoc spref_cancel_conv 
    unfolding lassoc unfolding rassoc[of _ "[1]"] pow_comm
    unfolding pow_Suc rassoc by simp 
  have "r = [0,1] \<cdot> ([0]\<^sup>@Suc j \<cdot> [1])\<^sup>@ m \<cdot> [0]\<^sup>@j \<cdot>  r'" 
    unfolding r' r by comparison
  thus "r' <s r" 
    by force
  show "w = r' \<cdot> v\<^sup>@Suc j \<cdot> t'"
    unfolding w r' v t'  
    by comparison 
qed

lemma three_covers_pers: \<comment> \<open>alias Old Good Lemma\<close>
  assumes "w = v \<cdot> t" and "w = r' \<cdot> v\<^sup>@Suc j \<cdot> t'" and "w = r \<cdot> v" and
    "r' <s r" and "t' <p t"
  shows "period w (\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|)" and "period w (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|)" and
    "(\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|) + (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|) = \<^bold>|w\<^bold>| + Suc j*\<^bold>|v\<^bold>| - 2*\<^bold>|v\<^bold>|"              
proof-
  let ?per_r = "\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|" 
  let ?per_t = "\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|" 
  let ?gcd = "gcd (\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|) (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|)"
  have "w \<noteq> \<epsilon>"
    using \<open>w = v \<cdot> t\<close> \<open>t' <p t\<close> by auto 
  obtain "r''" where "r'' \<cdot> r' = r" and "r'' \<noteq> \<epsilon>"
    using  ssufD[OF \<open>r' <s r\<close>] sufD by blast    
  hence "w \<le>p r'' \<cdot> w" 
    using assms unfolding pow_Suc using rassoc triv_pref by metis
  thus "period w ?per_r"
    using lenarg[OF \<open>r'' \<cdot> r' = r\<close>]  period_I[OF \<open>w \<noteq> \<epsilon>\<close> \<open>r'' \<noteq> \<epsilon>\<close> \<open>w \<le>p r'' \<cdot> w\<close>] unfolding lenmorph
    by (metis add_diff_cancel_right')  
  have "\<^bold>|r'\<^bold>| < \<^bold>|r\<^bold>|"
    using suffix_length_less[OF \<open>r' <s r\<close>].
  obtain "t''" where "t' \<cdot> t'' = t" and "t'' \<noteq> \<epsilon>" 
    using  sprefD[OF \<open>t' <p t\<close>] prefD by blast
  hence "w \<le>s w \<cdot> t''" 
    using assms unfolding pow_Suc2 using rassoc triv_suf by metis 
  have "\<^bold>|t'\<^bold>| < \<^bold>|t\<^bold>|"
    using prefix_length_less[OF \<open>t' <p t\<close>].
  show "period w ?per_t"
    using lenarg[OF \<open>t' \<cdot> t'' = t\<close>]  period_I[reversed, OF \<open>w \<noteq> \<epsilon>\<close> \<open>t'' \<noteq> \<epsilon>\<close> \<open>w \<le>s w \<cdot> t''\<close> ] unfolding lenmorph
    by (metis add_diff_cancel_left')  
  show eq: "?per_t + ?per_r = \<^bold>|w\<^bold>| + Suc j*\<^bold>|v\<^bold>| - 2*\<^bold>|v\<^bold>|"
    using lenarg[OF \<open>w = r' \<cdot> v\<^sup>@Suc j \<cdot> t'\<close>]
      lenarg[OF \<open>w = v \<cdot> t\<close>] lenarg[OF \<open>w = r \<cdot> v\<close>] \<open>\<^bold>|t'\<^bold>| < \<^bold>|t\<^bold>|\<close> \<open>\<^bold>|r'\<^bold>| < \<^bold>|r\<^bold>|\<close>
    unfolding pow_len lenmorph by force
qed

lemma three_covers_per0: assumes "w = v \<cdot> t" and "w = r' \<cdot> v\<^sup>@Suc j \<cdot> t'" and "w = r \<cdot> v" and
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
    have "w \<noteq> \<epsilon>" using \<open>w = v \<cdot> t\<close> \<open>t' <p t\<close>  by blast
    note prefix_length_less[OF \<open>t' <p t\<close>] prefix_length_less[reversed, OF \<open>r' <s r\<close>] 
    have  "?gcd \<noteq> 0"
      using \<open>\<^bold>|t'\<^bold>| < \<^bold>|t\<^bold>|\<close> gcd_eq_0_iff zero_less_diff' by metis
    have "period w ?per_t" and "period w ?per_r"  and eq: "?per_t + ?per_r = \<^bold>|w\<^bold>| + Suc j*\<^bold>|v\<^bold>| - 2*\<^bold>|v\<^bold>|"
      using three_covers_pers[OF \<open>w = v \<cdot> t\<close> \<open>w = r' \<cdot> v \<^sup>@ Suc j \<cdot> t'\<close> \<open>w = r \<cdot> v\<close> \<open>r' <s r\<close> \<open>t' <p t\<close>]. 

    obtain "r''" where "r'' \<cdot> r' = r" and "r'' \<noteq> \<epsilon>"
      using  ssufD[OF \<open>r' <s r\<close>] sufD by blast    
    hence "w \<le>p r'' \<cdot> w" 
      using less.prems unfolding pow_Suc using rassoc triv_pref by metis
    obtain "t''" where "t' \<cdot> t'' = t" and "t'' \<noteq> \<epsilon>" 
      using  sprefD[OF \<open>t' <p t\<close>] prefD by blast

    show "period w ?gcd"
    proof (cases)
      have local_rule: "a - c \<le> b \<Longrightarrow> k + a - c - b \<le> k" for a b c k :: nat
        by simp
      assume "Suc j*\<^bold>|v\<^bold>| - 2*\<^bold>|v\<^bold>| \<le> ?gcd" \<comment> \<open>Condition allowing to use the Periodicity lemma\<close>
      from local_rule[OF this] 
      have len: "?per_t + ?per_r - ?gcd \<le> \<^bold>|w\<^bold>|"
        unfolding eq.  
      show "period w ?gcd"
        using per_lemma[OF \<open>period w ?per_t\<close> \<open>period w ?per_r\<close> len].
    next 
      assume "\<not> Suc j*\<^bold>|v\<^bold>| - 2*\<^bold>|v\<^bold>| \<le> ?gcd"  \<comment> \<open>Periods are too long for the Periodicity lemma\<close>
      hence "?gcd \<le> \<^bold>|v\<^sup>@Suc j\<^bold>| - 2*\<^bold>|v\<^bold>|"  \<comment> \<open>But then we have a potential for using the Periodicity lemma on the power of v's\<close>
        unfolding pow_len by linarith
      have "\<^bold>|v \<^sup>@ Suc j\<^bold>| - Suc (Suc 0) * \<^bold>|v\<^bold>| + \<^bold>|v\<^bold>| \<le> \<^bold>|v \<^sup>@ Suc j\<^bold>|"
        by simp
      with add_le_mono1[OF \<open>?gcd \<le> \<^bold>|v\<^sup>@Suc j\<^bold>| - 2*\<^bold>|v\<^bold>|\<close>, of "\<^bold>|v\<^bold>|"]
      have "?gcd + \<^bold>|v\<^bold>| \<le> \<^bold>|v \<^sup>@ Suc j\<^bold>|"
        unfolding numerals using le_trans by blast

      show "period w ?gcd"
      proof (cases)
        assume "\<^bold>|r'\<^bold>| = \<^bold>|t'\<^bold>|" \<comment> \<open>The trivial case\<close>
        hence "\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>| = \<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|"
          using conj_len[OF \<open>w = v \<cdot> t\<close>[unfolded \<open>w = r \<cdot> v\<close>]] by force
        show "period w (gcd (\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|) (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|))"
          unfolding \<open>\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>| = \<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|\<close>  gcd_idem_nat using \<open>period w (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|)\<close>.
      next
        assume "\<^bold>|r'\<^bold>| \<noteq> \<^bold>|t'\<^bold>|" \<comment> \<open>The nontrivial case\<close>
        hence "\<^bold>|t'\<^bold>| < \<^bold>|r'\<^bold>|" using \<open>\<^bold>|t'\<^bold>| \<le> \<^bold>|r'\<^bold>|\<close> by force
        have "r' \<cdot> v <p w" 
          using \<open>\<^bold>|r'\<^bold>| < \<^bold>|r\<^bold>|\<close> \<open>r'' \<cdot> r' = r\<close> \<open>w \<le>p r'' \<cdot> w\<close> \<open>w = r \<cdot> v\<close> by force 
        obtain p where "r' \<cdot> v = v \<cdot> p" 
          using   ruler_le[OF triv_pref[of v t , folded \<open>w = v \<cdot> t\<close>], of "r' \<cdot> v"] 
          unfolding lenmorph \<open>w = r' \<cdot> v\<^sup>@Suc j \<cdot> t'\<close>[unfolded pow_Suc] rassoc 
          by (force simp add: prefix_def)
        from \<open>w = r' \<cdot> v\<^sup>@Suc j \<cdot> t'\<close>[unfolded pow_Suc lassoc this \<open>w = v \<cdot> t\<close>, unfolded rassoc cancel]
        have "p \<le>p t"
          by blast  
        have "\<^bold>|v \<cdot> p\<^bold>| < \<^bold>|w\<^bold>|"
          using prefix_length_less[OF \<open>r' \<cdot> v <p w\<close>, unfolded \<open>r' \<cdot> v = v \<cdot> p\<close>].
        have "v \<cdot> p \<le>s w" \<comment> \<open>r'v is a long border of w\<close>
          using \<open>r' \<cdot> v = v \<cdot> p\<close> \<open>w = r \<cdot> v\<close> \<open>r' <s r\<close> same_suffix_suffix ssufD by metis
        have "\<^bold>|r'\<^bold>| = \<^bold>|p\<^bold>|"
          using conj_len[OF \<open>r' \<cdot> v = v \<cdot> p\<close>].
        note \<open>\<^bold>|t'\<^bold>| \<le> \<^bold>|r'\<^bold>|\<close>[unfolded \<open>\<^bold>|r'\<^bold>| = \<^bold>|p\<^bold>|\<close>] 
        hence "t' <p p"
          using \<open>t = p \<cdot> v \<^sup>@ j \<cdot> t'\<close> \<open>t' \<cdot> t'' = t\<close> \<open>\<^bold>|r'\<^bold>| = \<^bold>|p\<^bold>|\<close> \<open>\<^bold>|t'\<^bold>| < \<^bold>|r'\<^bold>|\<close> \<open>p \<le>p t\<close> pref_prod_long_less by metis
        show ?thesis
        proof (cases)                                 
          assume "\<^bold>|v \<cdot> p\<^bold>| \<le> \<^bold>|v\<^sup>@Suc j \<cdot> t'\<^bold>|" \<comment> \<open>The border does not cover the whole power of v's. 
                                              In this case, everything commutes\<close>
          have "\<rho> (rev v) = rev (\<rho> v)"
            using \<open>v \<noteq> \<epsilon>\<close> primroot_rev by auto
          from pref_marker_ext[reversed, OF \<open>\<^bold>|t'\<^bold>| \<le> \<^bold>|p\<^bold>|\<close> \<open>v \<noteq> \<epsilon>\<close>]
            suf_prod_le[OF \<open>v \<cdot> p \<le>s w\<close>[unfolded \<open>w = r' \<cdot> v\<^sup>@Suc j \<cdot> t'\<close>] \<open>\<^bold>|v \<cdot> p\<^bold>| \<le> \<^bold>|v\<^sup>@Suc j \<cdot> t'\<^bold>|\<close>]
          obtain k where "p = v\<^sup>@k \<cdot> t'" 
            unfolding  prim_self_root[OF \<open>primitive v\<close>].
          hence "p \<le>p v\<^sup>@k \<cdot> p"
            using \<open>t' <p p\<close> by simp
          from root_comm_root[OF this power_commutes[symmetric]]
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
            by (simp add: pow_comm \<open>p = r'\<close> \<open>r' \<cdot> v = v \<cdot> r'\<close> \<open>t = p \<cdot> v \<^sup>@ j \<cdot> t'\<close> \<open>t' \<cdot> v = v \<cdot> t'\<close>)
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
          hence "g \<noteq> 0"
            using  nemp_len[OF \<open>v \<noteq> \<epsilon>\<close>] per_positive[OF \<open>period w (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|)\<close>] gcd_nat.neutr_eq_iff mult_is_0 by metis
          from per_mult[OF \<open>period w \<^bold>|v\<^bold>|\<close> this]
          show ?thesis
            unfolding g.  
        next
          assume "\<not> \<^bold>|v \<cdot> p\<^bold>| \<le> \<^bold>|v \<^sup>@ Suc j \<cdot> t'\<^bold>|"  \<comment> \<open>The border covers the whole power. An induction is available.\<close>
          then obtain ri' where "v \<cdot> p = ri'\<cdot>v\<^sup>@Suc j \<cdot> t'" and "ri' \<le>s r'" 
            using \<open>v \<cdot> p \<le>s w\<close> unfolding \<open>w = r' \<cdot> v\<^sup>@Suc j \<cdot> t'\<close>
            using suffix_append suffix_length_le by blast 
          hence "ri' <s r'"
            using \<open>r' \<cdot> v = v \<cdot> p\<close> cancel_right less.prems(2) less.prems(3) less.prems(4) suffix_order.le_neq_trans by metis

          have gcd_eq: "gcd (\<^bold>|p\<^bold>| - \<^bold>|t'\<^bold>|) (\<^bold>|r'\<^bold>| - \<^bold>|ri'\<^bold>|) = ?gcd" \<comment> \<open>The two gcd's are the same\<close>
          proof-
            have "\<^bold>|r'\<^bold>| \<le> \<^bold>|r\<^bold>|"
              by (simp add: \<open>\<^bold>|r'\<^bold>| < \<^bold>|r\<^bold>|\<close> dual_order.strict_implies_order)  
            have "\<^bold>|t\<^bold>| = \<^bold>|r\<^bold>|"
              using lenarg[OF \<open>w = v \<cdot> t\<close>] unfolding lenarg[OF \<open>w = r \<cdot> v\<close>]  lenmorph by auto
            have e1: "\<^bold>|r'\<^bold>| - \<^bold>|ri'\<^bold>| = \<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|"
              using lenarg[OF \<open>v \<cdot> p = ri'\<cdot>v\<^sup>@Suc j \<cdot> t'\<close>[folded \<open>r' \<cdot> v = v \<cdot> p\<close>]]
                lenarg[OF \<open>w = r \<cdot> v\<close>[unfolded \<open>w = r' \<cdot> v\<^sup>@Suc j \<cdot> t'\<close>]]
              unfolding lenmorph pow_len by (simp add: add.commute diff_add_inverse diff_diff_add)
            have "\<^bold>|t\<^bold>| = \<^bold>|p\<^bold>| + \<^bold>|r'\<^bold>| - \<^bold>|ri'\<^bold>|"
              unfolding add_diff_assoc[OF suffix_length_le[OF \<open>ri' \<le>s r'\<close>], unfolded e1, symmetric]
                \<open>\<^bold>|t\<^bold>| = \<^bold>|r\<^bold>|\<close> unfolding \<open>\<^bold>|r'\<^bold>| = \<^bold>|p\<^bold>|\<close>   
              using \<open>\<^bold>|r'\<^bold>| < \<^bold>|r\<^bold>|\<close>[unfolded \<open>\<^bold>|r'\<^bold>| = \<^bold>|p\<^bold>|\<close>] by linarith
            (* TODO *)
            hence e2: "\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>| = (\<^bold>|p\<^bold>| - \<^bold>|t'\<^bold>|) + (\<^bold>|r'\<^bold>| - \<^bold>|ri'\<^bold>|)"
              using \<open>\<^bold>|t'\<^bold>| \<le> \<^bold>|p\<^bold>|\<close> diff_commute \<open>ri' \<le>s r'\<close> \<open>\<^bold>|r'\<^bold>| = \<^bold>|p\<^bold>|\<close> \<open>\<^bold>|r'\<^bold>| \<le> \<^bold>|r\<^bold>|\<close> \<open>\<^bold>|t\<^bold>| = \<^bold>|r\<^bold>|\<close>
               by linarith 
            show ?thesis  
              unfolding e2 e1 gcd_add1..
          qed

          have per_vp: "period (v \<cdot> p) ?gcd" 
          proof (cases)
            assume "\<^bold>|t'\<^bold>| \<le> \<^bold>|ri'\<^bold>|" 
              \<comment> \<open>By induction.\<close>
            from less.hyps[OF \<open>\<^bold>|v \<cdot> p\<^bold>| < \<^bold>|w\<^bold>|\<close> refl \<open>v \<cdot> p = ri'\<cdot>v\<^sup>@Suc j \<cdot> t'\<close> \<open>r' \<cdot> v = v \<cdot> p\<close>[symmetric] \<open>ri' <s r'\<close> \<open>t' <p p\<close> this \<open>primitive v\<close>]
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
              show "rev p \<cdot> rev v = rev t' \<cdot> rev v \<^sup>@ Suc j \<cdot> rev ri'"
                using \<open>v \<cdot> p = ri'\<cdot>v\<^sup>@Suc j \<cdot> t'\<close> unfolding rev_append[symmetric] rev_pow[symmetric] rassoc by simp
              show "rev t' <s rev p"
                using \<open>t' <p p\<close> by (auto simp add: prefix_def) 
              show "rev ri' <p rev r'"
                using \<open>ri' <s r'\<close> strict_suffix_to_prefix by blast
              show "\<^bold>|rev ri'\<^bold>| \<le> \<^bold>|rev t'\<^bold>|"
                by (simp add: \<open>\<^bold>|ri'\<^bold>| \<le> \<^bold>|t'\<^bold>|\<close>) 
              show "primitive (rev v)"
                by (simp add: \<open>primitive v\<close> prim_rev_iff)
            qed 
            thus ?thesis
              unfolding length_rev rev_append[symmetric] period_rev_conv gcd.commute[of "\<^bold>|r'\<^bold>| - \<^bold>|ri'\<^bold>|"] gcd_eq. 
          qed

          have "period (v\<^sup>@Suc j) (gcd \<^bold>|v\<^bold>| ?gcd)"
          proof (rule per_lemma)
            show " \<^bold>|v\<^bold>| + ?gcd - gcd \<^bold>|v\<^bold>| (gcd (\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|) (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|)) \<le> \<^bold>|v \<^sup>@ Suc j\<^bold>|"
              using \<open>?gcd + \<^bold>|v\<^bold>| \<le> \<^bold>|v \<^sup>@ Suc j\<^bold>|\<close> by linarith
            show "period (v \<^sup>@ Suc j) \<^bold>|v\<^bold>|"
              using \<open>v \<noteq> \<epsilon>\<close> pow_per by blast
            have "v \<^sup>@ Suc j \<noteq> \<epsilon>"
              using \<open>v \<noteq> \<epsilon>\<close> by auto
            from period_fac[OF per_vp[unfolded \<open>v \<cdot> p = ri' \<cdot> v \<^sup>@ Suc j \<cdot> t'\<close>] this]
            show "period (v \<^sup>@ Suc j) ?gcd".
          qed

          have per_vp': "period (v \<cdot> p) (gcd \<^bold>|v\<^bold>| ?gcd)"
          proof (rule refine_per)
            show "gcd \<^bold>|v\<^bold>| ?gcd dvd ?gcd" by blast
            show "?gcd \<le> \<^bold>|v\<^sup>@Suc j\<^bold>|"
              using \<open>?gcd + \<^bold>|v\<^bold>| \<le> \<^bold>|v \<^sup>@ Suc j\<^bold>|\<close> add_leE by blast
            show "v \<^sup>@ Suc j \<le>f v \<cdot> p"
              using  facI'[OF \<open>v \<cdot> p = ri' \<cdot> v \<^sup>@ Suc j \<cdot> t'\<close>[symmetric]].
          qed fact+

          have "period w (gcd \<^bold>|v\<^bold>| ?gcd)"
          proof (rule per_glue)
            show "v \<cdot> p \<le>p w"
              using \<open>p \<le>p t\<close> \<open>w = v \<cdot> t\<close> by auto
            have "\<^bold>|v \<^sup>@ Suc j\<^bold>| + \<^bold>|t'\<^bold>| \<le> \<^bold>|v\<^bold>| + \<^bold>|p\<^bold>|"
              using \<open>\<not> \<^bold>|v \<cdot> p\<^bold>| \<le> \<^bold>|v \<^sup>@ Suc j \<cdot> t'\<^bold>|\<close> by auto
            moreover have "\<^bold>|r'\<^bold>| + gcd \<^bold>|v\<^bold>| ?gcd \<le> \<^bold>|v\<^bold>| + \<^bold>|p\<^bold>|"
              using lenarg[OF \<open>r' \<cdot> v = v \<cdot> p\<close>, unfolded lenmorph]
                \<open>v \<noteq> \<epsilon>\<close> gcd_le1_nat length_0_conv nat_add_left_cancel_le by metis 
            ultimately show "\<^bold>|w\<^bold>| + gcd \<^bold>|v\<^bold>| ?gcd \<le> \<^bold>|v \<cdot> p\<^bold>| + \<^bold>|v \<cdot> p\<^bold>|"
              unfolding lenarg[OF \<open>w = r' \<cdot> v \<^sup>@ Suc j \<cdot> t'\<close>] lenmorph add.commute[of "\<^bold>|r'\<^bold>|"] by linarith
          qed fact+

          obtain k where k: "?gcd = k*(gcd \<^bold>|v\<^bold>| ?gcd)"
            using gcd_dvd2 unfolding dvd_def mult.commute[of _ "gcd \<^bold>|v\<^bold>| ?gcd"] by blast
          hence "k \<noteq> 0"
            using \<open>?gcd \<noteq> 0\<close> by algebra

          from per_mult[OF \<open>period w (gcd \<^bold>|v\<^bold>| ?gcd)\<close> this, folded k] 
          show ?thesis.
        qed
      qed
    qed
  qed
qed

lemma three_covers_per: assumes "w = v \<cdot> t" and "w = r' \<cdot> v\<^sup>@Suc j \<cdot> t'" and "w = r \<cdot> v" and
  "r' <s r" and "t' <p t"
shows "period w (gcd (\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|) (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|))"
proof-
  let ?per_r = "\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|" 
  let ?per_t = "\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|" 
  let ?gcd = "gcd (\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|) (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|)"
  have "period w ?per_t" and "period w ?per_r" and len: "(\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|) + (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|) = \<^bold>|w\<^bold>| + Suc j*\<^bold>|v\<^bold>| - 2*\<^bold>|v\<^bold>|"
    using three_covers_pers[OF \<open>w = v \<cdot> t\<close> \<open>w = r' \<cdot> v \<^sup>@ Suc j \<cdot> t'\<close> \<open>w = r \<cdot> v\<close> \<open>r' <s r\<close> \<open>t' <p t\<close>] by blast+
  show ?thesis
  proof(cases)
    assume "v = \<epsilon>"
    have "\<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>| + (\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|) = \<^bold>|w\<^bold>|"
      using \<open>w = v \<cdot> t\<close> \<open>w = r' \<cdot> v\<^sup>@Suc j \<cdot> t'\<close> \<open>w = r \<cdot> v\<close> unfolding \<open>v = \<epsilon>\<close> emp_pow clean_emp  by force
    from per_lemma[OF \<open>period w ?per_t\<close> \<open>period w ?per_r\<close>, unfolded this]
    show "period w ?gcd"
      by fastforce  
  next
    assume "v \<noteq> \<epsilon>"
    show ?thesis
    proof (cases)
      assume "j \<le> 1"
      hence "(j = 0 \<Longrightarrow> P) \<Longrightarrow> (j = 1 \<Longrightarrow> P) \<Longrightarrow> P" for P by force
      hence "\<^bold>|w\<^bold>| + Suc j*\<^bold>|v\<^bold>| - 2*\<^bold>|v\<^bold>| - ?gcd \<le> \<^bold>|w\<^bold>|" \<comment> \<open>Condition allowing to use the Periodicity lemma\<close>
        by (cases, simp_all)  
      thus "period w ?gcd"
        using per_lemma[OF \<open>period w ?per_t\<close> \<open>period w ?per_r\<close>] unfolding len by blast
    next   
      assume "\<not> j \<le> 1" hence "2 \<le> j" by simp
      obtain e where "v = \<rho> v\<^sup>@Suc e"
        using \<open>v \<noteq> \<epsilon>\<close> primroot_expE by metis 
      have "e + (Suc e * (Suc j - 2) + 2 + e) = Suc e * (Suc j - 2) + Suc e + Suc e"
        by auto
      also have "... = Suc e * (Suc j - 2 + Suc 0 + Suc 0)" 
        unfolding add_mult_distrib2 by simp
      also have "... = Suc e * Suc j"  
        using \<open>2 \<le> j\<close> by auto  
      finally have calc: "e + (Suc e * (Suc j - 2) + 2 + e) = Suc e * Suc j".
      have "w = \<rho> v \<cdot> (\<rho> v\<^sup>@e \<cdot> t)"
        using \<open>v = \<rho> v \<^sup>@ Suc e\<close> \<open>w = v \<cdot> t\<close> by fastforce
      have "w = (r \<cdot> \<rho> v\<^sup>@e) \<cdot> \<rho> v"
        unfolding rassoc pow_Suc2[symmetric] \<open>v = \<rho> v \<^sup>@ Suc e\<close>[symmetric] by fact 
      obtain e' where e': "Suc e' = Suc e * (Suc j - 2) + 2"
        by auto 
      have "w = (r' \<cdot> \<rho> v\<^sup>@e) \<cdot> \<rho> v \<^sup>@Suc e' \<cdot> (\<rho> v\<^sup>@e \<cdot> t')"
        unfolding e'\<open>w = r' \<cdot> v\<^sup>@Suc j \<cdot> t'\<close> rassoc cancel unfolding lassoc cancel_right add_exps[symmetric] calc
          pow_mult \<open>v = \<rho> v\<^sup>@Suc e\<close>[symmetric].. 

      show ?thesis   
      proof(cases)
        assume "\<^bold>|t'\<^bold>| \<le> \<^bold>|r'\<^bold>|"
        have dif1: "\<^bold>|\<rho> v \<^sup>@ e \<cdot> t\<^bold>| - \<^bold>|\<rho> v \<^sup>@ e \<cdot> t'\<^bold>| = \<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|"
          unfolding lenmorph by simp
        have dif2: "\<^bold>|r \<cdot> \<rho> v \<^sup>@ e\<^bold>| - \<^bold>|r' \<cdot> \<rho> v \<^sup>@ e\<^bold>| = \<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|"
          unfolding lenmorph by simp
        show ?thesis
        proof (rule  three_covers_per0[OF \<open>w = \<rho> v \<cdot> (\<rho> v\<^sup>@e \<cdot> t)\<close>
              \<open>w = (r' \<cdot> \<rho> v\<^sup>@e) \<cdot> \<rho> v \<^sup>@Suc e' \<cdot> (\<rho> v\<^sup>@e \<cdot> t')\<close> \<open>w = (r \<cdot> \<rho> v\<^sup>@e) \<cdot> \<rho> v\<close>, unfolded dif1 dif2])
          show "r' \<cdot> \<rho> v \<^sup>@ e <s r \<cdot> \<rho> v \<^sup>@ e"
            using \<open>r' <s r\<close> by auto  
          show "\<rho> v \<^sup>@ e \<cdot> t' <p \<rho> v \<^sup>@ e \<cdot> t"
            using \<open>t' <p t\<close> by auto  
          show "\<^bold>|\<rho> v \<^sup>@ e \<cdot> t'\<^bold>| \<le> \<^bold>|r' \<cdot> \<rho> v \<^sup>@ e\<^bold>|"
            unfolding lenmorph using \<open>\<^bold>|t'\<^bold>| \<le> \<^bold>|r'\<^bold>|\<close> by auto  
          show "primitive (\<rho> v)"
            using primroot_prim[OF \<open>v \<noteq> \<epsilon>\<close>].
        qed
      next
        let ?w = "rev w" and ?r = "rev t" and ?t = "rev r" and ?\<rho> = "rev (\<rho> v)" and ?r' = "rev t'" and ?t' = "rev r'"
        assume "\<not> \<^bold>|t'\<^bold>| \<le> \<^bold>|r'\<^bold>|" 
        hence "\<^bold>|?t'\<^bold>| \<le> \<^bold>|?r'\<^bold>|" by auto
        have "?w = (?r \<cdot> ?\<rho>\<^sup>@e) \<cdot> ?\<rho>" 
          unfolding rev_pow[symmetric] rev_append[symmetric] \<open>w = \<rho> v \<cdot> (\<rho> v\<^sup>@e \<cdot> t)\<close> rassoc..
        have "?w = ?\<rho> \<cdot> (?\<rho>\<^sup>@e \<cdot> ?t)"
          unfolding rev_pow[symmetric] rev_append[symmetric] \<open>w = (r \<cdot> \<rho> v\<^sup>@e) \<cdot> \<rho> v\<close>.. 
        have "?w = (?r' \<cdot> ?\<rho>\<^sup>@e) \<cdot> ?\<rho>\<^sup>@Suc e' \<cdot> (?\<rho>\<^sup>@e \<cdot> ?t')"
          unfolding rev_pow[symmetric] rev_append[symmetric] \<open>w = (r' \<cdot> \<rho> v\<^sup>@e) \<cdot> \<rho> v \<^sup>@Suc e' \<cdot> (\<rho> v\<^sup>@e \<cdot> t')\<close> rassoc.. 
        have dif1: "\<^bold>|?\<rho> \<^sup>@ e \<cdot> ?t\<^bold>| - \<^bold>|?\<rho> \<^sup>@ e \<cdot> ?t'\<^bold>| = \<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|"
          unfolding lenmorph by simp
        have dif2: "\<^bold>|?r \<cdot> ?\<rho> \<^sup>@ e\<^bold>| - \<^bold>|?r' \<cdot> ?\<rho> \<^sup>@ e\<^bold>| = \<^bold>|t\<^bold>| - \<^bold>|t'\<^bold>|"
          unfolding lenmorph by simp
        show ?thesis
        proof (rule  three_covers_per0[OF \<open>?w = ?\<rho> \<cdot> (?\<rho>\<^sup>@e \<cdot> ?t)\<close>
              \<open>?w = (?r' \<cdot> ?\<rho>\<^sup>@e) \<cdot> ?\<rho>\<^sup>@Suc e' \<cdot> (?\<rho>\<^sup>@e \<cdot> ?t')\<close> \<open>?w = (?r \<cdot> ?\<rho>\<^sup>@e) \<cdot> ?\<rho>\<close>, 
              unfolded dif1 dif2 period_rev_conv gcd.commute[of "\<^bold>|r\<^bold>| - \<^bold>|r'\<^bold>|"]])
          show "?r' \<cdot> ?\<rho> \<^sup>@ e <s ?r \<cdot> ?\<rho> \<^sup>@ e"
            using \<open>t' <p t\<close> by (auto simp add: prefix_def) 
          show "?\<rho> \<^sup>@ e \<cdot> ?t' <p ?\<rho> \<^sup>@ e \<cdot> ?t"
            using \<open>r' <s r\<close> by (auto simp add: suf_def)  
          show "\<^bold>|?\<rho> \<^sup>@ e \<cdot> ?t'\<^bold>| \<le> \<^bold>|?r' \<cdot> ?\<rho> \<^sup>@ e\<^bold>|"
            unfolding lenmorph using \<open>\<^bold>|?t'\<^bold>| \<le> \<^bold>|?r'\<^bold>|\<close> by auto  
          show "primitive ?\<rho>"
            using primroot_prim[OF \<open>v \<noteq> \<epsilon>\<close>] by (simp add: prim_rev_iff) 
        qed
      qed
    qed
  qed
qed

hide_fact three_covers_per0

lemma three_covers_pref_suf_pow: assumes "x \<cdot> y \<le>p w" and "y \<cdot> x \<le>s w" and "w \<le>f y\<^sup>@k" and  "\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|"
  shows "x \<cdot> y =  y \<cdot> x" 
  using fac_marker_suf[OF fac_trans[OF pref_fac[OF \<open>x \<cdot> y \<le>p w\<close>] \<open>w \<le>f y\<^sup>@k\<close>]]
    fac_marker_pref[OF fac_trans[OF suf_fac[OF \<open>y \<cdot> x \<le>s w\<close>] \<open>w \<le>f y\<^sup>@k\<close>]]
    root_suf_comm'[OF _ suf_prod_long, OF _ _ \<open>\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|\<close>, of x] by presburger  

subsection \<open>Binary Equality Words\<close>

(*rudimentary material for classification of binary equality words *)

\<comment> \<open>translation of a combinatorial lemma into the language of "something is not BEW"\<close>

definition binary_equality_word :: "binA list \<Rightarrow> bool" where
  "binary_equality_word w = (\<exists> (g :: binA list \<Rightarrow> nat list) h. binary_code_morphism g \<and> binary_code_morphism h \<and> g \<noteq> h \<and> w \<in> g =\<^sub>M h)"

lemma not_bew_baiba: assumes  "\<^bold>|y\<^bold>| < \<^bold>|v\<^bold>|" and  "x \<le>s y" and "u \<le>s v" and 
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
  obtain w w' q t where p_def: "p = (w'\<cdot>w)\<^sup>@Suc q" and s_def: "s = (w\<cdot>w')\<^sup>@Suc q" and y_def: "y = (w\<cdot>w')\<^sup>@t\<cdot>w" and "w' \<noteq> \<epsilon>" and "primitive (w\<cdot>w')"
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
    unfolding CoWBasic.power_Suc2
    using sufI[of "p \<cdot> u \<^sup>@ k \<cdot> (w \<cdot> w') \<^sup>@ q" "w \<cdot> w'" "x\<^sup>@k", unfolded rassoc]
    by argo

  have "\<^bold>|w\<cdot>w'\<^bold>| \<le> \<^bold>|x\<^bold>|"
  proof(intro leI notI)
    assume "\<^bold>|x\<^bold>| < \<^bold>|w \<cdot> w'\<^bold>|" 
    have "x \<le>s (w\<cdot>w')\<cdot>y"
      using  \<open>x \<le>s y\<close>  by (auto simp add: suf_def)
    have "(w'\<cdot>w) \<le>s (w\<cdot>w')\<cdot>y"
      unfolding \<open>y = (w\<cdot>w')\<^sup>@t\<cdot>w\<close> lassoc pow_comm[symmetric] suf_cancel_conv
      by blast
     
    from ruler_le[reversed, OF \<open>x \<le>s (w\<cdot>w')\<cdot>y\<close> this 
        less_imp_le[OF \<open>\<^bold>|x\<^bold>| < \<^bold>|w \<cdot> w'\<^bold>|\<close>[unfolded swap_len]]]
    have "x \<le>s w'\<cdot> w".
    hence "x \<le>s p"
      unfolding p_def pow_Suc2 suffix_append by blast  
    from root_suf_comm[OF _ suf_ext[OF this]]
    have "x\<cdot>p = p\<cdot>x"
      using pref_prod_root[OF prefI[OF \<open>x \<^sup>@ k = p \<cdot> u \<^sup>@ k \<cdot> s\<close>[symmetric]]] by blast
    from  comm_drop_exp[OF _ this[unfolded \<open>p = (w' \<cdot> w) \<^sup>@ Suc q\<close>]]
    have "x \<cdot> (w' \<cdot> w) = (w' \<cdot> w) \<cdot> x"
      by force
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

  have "k \<noteq> 0"
    using \<open>\<^bold>|y\<^bold>| < \<^bold>|v\<^bold>|\<close> lenarg[OF \<open>y \<cdot> x \<^sup>@ k \<cdot> y = v \<cdot> u \<^sup>@ k \<cdot> v\<close>, unfolded lenmorph pow_len]
      not_add_less1 by fastforce 

  have "y = w'\<^sup>@t"
    using y_def \<open>w = \<epsilon>\<close>  by force 
  hence "y \<in> w'*"
    using rootI by blast

  have "s \<in> w'*"
    using s_def \<open>w = \<epsilon>\<close> rootI by force
  hence "v \<in> w'*"
    using \<open>s \<cdot> y = v\<close>  \<open>y \<in> w'*\<close> add_roots by blast

  have "w' \<le>p x"
    using \<open>x\<^sup>@k = p\<cdot>u\<^sup>@k\<cdot>s\<close> eq_le_pref[OF _ \<open>\<^bold>|w\<cdot>w'\<^bold>| \<le> \<^bold>|x\<^bold>|\<close>, of "w' \<^sup>@ q \<cdot> u \<cdot> u \<^sup>@ (k - 1) \<cdot> s" "x \<^sup>@ (k - 1)"] 
    unfolding p_def \<open>w = \<epsilon>\<close> clean_emp pop_pow_one[OF \<open>k \<noteq> 0\<close>] pow_Suc rassoc
    by argo

  have "x \<cdot> w' = w' \<cdot> x"
    using  \<open>x \<le>s y\<close>  \<open>w' \<le>p x\<close> y_def[unfolded \<open>w = \<epsilon>\<close> \<open>t = Suc t'\<close> clean_emp]
      pref_suf_pows_comm[of w' x 0 0 0 t', unfolded pow_zero clean_emp, folded y_def[unfolded \<open>w = \<epsilon>\<close> \<open>t = Suc t'\<close>, unfolded clean_emp]]
    by force
  hence "x \<in> w'*"
    using  prim_comm_exp[OF \<open>primitive w'\<close>, of x]
    unfolding root_def
    by metis

  have "p \<in> w'*"
    using \<open>s \<in> w'*\<close> \<open>y \<in> w'*\<close> \<open>s \<cdot> y = v\<close>[folded \<open>y \<cdot> p = v\<close>]
    by (simp add: \<open>s \<cdot> y = y \<cdot> p\<close> \<open>s \<in> w'*\<close> \<open>y \<in> w'*\<close> \<open>w \<cdot> w' = w' \<cdot> w\<close> p_def s_def)

  obtain k' where "k = Suc k'" using \<open>k \<noteq> 0\<close> not0_implies_Suc by auto 

  have "u\<^sup>@k \<in> w'*"
    using root_suf_cancel[OF \<open>s \<in> w'*\<close>, of "p \<cdot> u \<^sup>@ k", THEN root_pref_cancel[OF _ \<open>p \<in> w'*\<close>], unfolded rassoc, folded \<open>x\<^sup>@k = p\<cdot>u\<^sup>@k\<cdot>s\<close>, OF root_pow_root[OF \<open>x \<in> w'*\<close>]].
  from prim_root_drop_exp[OF \<open>k \<noteq> 0\<close> \<open>primitive w'\<close> this]  
  have "u \<in> w'*".      

  show "commutes {x,y,u,v}"
    by (intro commutesI_root[of _ w'], unfold Set.ball_simps(7), simp add: \<open>x \<in> w'*\<close> \<open>y \<in> w'*\<close> \<open>u \<in> w'*\<close> \<open>v \<in> w'*\<close>)
qed

lemma not_bew_baibaib: assumes "\<^bold>|x\<^bold>| < \<^bold>|u\<^bold>|" and "1 < i" and 
  "x \<cdot> y\<^sup>@i\<cdot> x \<cdot> y\<^sup>@i \<cdot> x = u \<cdot> v\<^sup>@i\<cdot> u \<cdot> v\<^sup>@i \<cdot> u"
shows "commutes {x,y,u,v}"
proof-
  have "i \<noteq> 0"
    using assms(2) by auto

  from lenarg[OF \<open>x \<cdot> y\<^sup>@i\<cdot> x \<cdot> y\<^sup>@i \<cdot> x = u \<cdot> v\<^sup>@i\<cdot> u \<cdot> v\<^sup>@i \<cdot> u\<close>]
  have "2*\<^bold>|x \<cdot> y\<^sup>@i\<^bold>| + \<^bold>|x\<^bold>| = 2*\<^bold>|u \<cdot> v\<^sup>@i\<^bold>| + \<^bold>|u\<^bold>|"
    by auto
  hence "\<^bold>|u \<cdot> v\<^sup>@i\<^bold>| < \<^bold>|x \<cdot> y\<^sup>@i\<^bold>|"
    using \<open>\<^bold>|x\<^bold>| < \<^bold>|u\<^bold>|\<close> by fastforce
  hence "u \<cdot> v\<^sup>@i <p x \<cdot> y\<^sup>@i"
    using assms(3) eq_le_pref less_or_eq_imp_le mult_assoc sprefI2 by metis

  have "x\<cdot>y\<^sup>@i \<noteq> \<epsilon>"
    by (metis \<open>u \<cdot> v \<^sup>@ i <p x \<cdot> y \<^sup>@ i\<close> strict_prefix_simps(1))
  have "u\<cdot>v\<^sup>@i \<noteq> \<epsilon>"
    using assms(1) gr_implies_not0 by blast

  have "(u\<cdot>v\<^sup>@i) \<cdot> (x\<cdot>y\<^sup>@i) = (x\<cdot>y\<^sup>@i) \<cdot> (u\<cdot>v\<^sup>@i)"
  proof(rule sq_short_per)
    have eq: "(x \<cdot> y \<^sup>@ i) \<cdot> (x \<cdot> y \<^sup>@ i) \<cdot> x = (u \<cdot> v \<^sup>@ i) \<cdot> (u \<cdot> v \<^sup>@ i) \<cdot> u"
      using assms(3) by auto
    from lenarg[OF this] 
    have "\<^bold>|u \<cdot> v\<^sup>@i \<cdot> u\<^bold>| < \<^bold>|x \<cdot> y\<^sup>@i \<cdot> x \<cdot> y\<^sup>@i\<^bold>|"
      unfolding lenmorph using \<open>\<^bold>|x\<^bold>| < \<^bold>|u\<^bold>|\<close> by linarith
    from eq_le_pref[OF _ less_imp_le[OF this]]
    have "(u \<cdot> v\<^sup>@i)\<cdot>u \<le>p (x \<cdot> y\<^sup>@i) \<cdot> (x \<cdot> y\<^sup>@i)"
      using eq[symmetric] unfolding rassoc by blast 
    hence "(u \<cdot> v \<^sup>@ i) \<cdot> (u \<cdot> v\<^sup>@i) \<cdot> u \<le>p (u \<cdot> v \<^sup>@ i) \<cdot> ((x \<cdot> y\<^sup>@i) \<cdot> (x \<cdot> y\<^sup>@i))"
      unfolding same_prefix_prefix.  
    from pref_trans[OF prefI[of "(x \<cdot> y \<^sup>@ i) \<cdot> (x \<cdot> y \<^sup>@ i)" x "(x \<cdot> y \<^sup>@ i) \<cdot> (x \<cdot> y \<^sup>@ i) \<cdot> x"]
        this[folded \<open>(x \<cdot> y \<^sup>@ i) \<cdot> (x \<cdot> y \<^sup>@ i) \<cdot> x = (u \<cdot> v \<^sup>@ i) \<cdot> (u \<cdot> v \<^sup>@ i) \<cdot> u\<close>],
        unfolded rassoc, OF refl]
    show "(x \<cdot> y\<^sup>@i)\<cdot>(x \<cdot> y\<^sup>@i) \<le>p (u \<cdot> v\<^sup>@i) \<cdot> ((x \<cdot> y\<^sup>@i) \<cdot> (x \<cdot> y\<^sup>@i))"
      by fastforce
    show "\<^bold>|u \<cdot> v \<^sup>@ i\<^bold>| \<le> \<^bold>|x \<cdot> y \<^sup>@ i\<^bold>|"
      using less_imp_le_nat[OF \<open>\<^bold>|u \<cdot> v \<^sup>@ i\<^bold>| < \<^bold>|x \<cdot> y \<^sup>@ i\<^bold>|\<close>].
  qed

  obtain r m k where "x\<cdot>y\<^sup>@i = r\<^sup>@k" "u\<cdot>v\<^sup>@i = r\<^sup>@m" "primitive r"
    using \<open>(u \<cdot> v \<^sup>@ i) \<cdot> x \<cdot> y \<^sup>@ i = (x \<cdot> y \<^sup>@ i) \<cdot> u \<cdot> v \<^sup>@ i\<close>[unfolded 
        comm_primroots[OF \<open>u \<cdot> v \<^sup>@ i \<noteq> \<epsilon>\<close> \<open>x \<cdot> y \<^sup>@ i \<noteq> \<epsilon>\<close>]]
      \<open>u \<cdot> v \<^sup>@ i \<noteq> \<epsilon>\<close> \<open>x \<cdot> y \<^sup>@ i \<noteq> \<epsilon>\<close> primroot_expE primroot_prim by metis

  have "m < k"
    using \<open>\<^bold>|u \<cdot> v \<^sup>@ i\<^bold>| < \<^bold>|x \<cdot> y \<^sup>@ i\<^bold>|\<close>
    unfolding strict_prefix_def \<open>u \<cdot> v \<^sup>@ i = r \<^sup>@ m\<close> \<open>x \<cdot> y \<^sup>@ i = r \<^sup>@ k\<close>
      pow_len
    by simp

  have "x\<cdot>y\<^sup>@i = u\<cdot>v\<^sup>@i\<cdot>r\<^sup>@(k-m)"
    by (simp add: \<open>m < k\<close> \<open>u \<cdot> v \<^sup>@ i = r \<^sup>@ m\<close> \<open>x \<cdot> y \<^sup>@ i = r \<^sup>@ k\<close> lassoc less_imp_le_nat pop_pow)

  have "\<^bold>|y \<^sup>@ i\<^bold>| = \<^bold>|v \<^sup>@ i\<^bold>| + 3 * \<^bold>|r \<^sup>@ (k - m)\<^bold>|" and "\<^bold>|r\<^bold>| \<le> \<^bold>|y\<^sup>@(i-1)\<^bold>|"
  proof-
    have "\<^bold>|x \<cdot> y\<^sup>@i\<^bold>| = \<^bold>|r\<^sup>@(k-m)\<^bold>| + \<^bold>|u \<cdot> v\<^sup>@i\<^bold>|"
      using lenarg[OF \<open>x\<cdot>y\<^sup>@i = u\<cdot>v\<^sup>@i\<cdot>r\<^sup>@(k-m)\<close>]
      by auto

    have "\<^bold>|u\<^bold>| = 2 * \<^bold>|r \<^sup>@ (k - m)\<^bold>| + \<^bold>|x\<^bold>|"
      using \<open>2*\<^bold>|x \<cdot> y\<^sup>@i\<^bold>| + \<^bold>|x\<^bold>| = 2*\<^bold>|u \<cdot> v\<^sup>@i\<^bold>| + \<^bold>|u\<^bold>|\<close>
      unfolding \<open>\<^bold>|x \<cdot> y\<^sup>@i\<^bold>| = \<^bold>|r\<^sup>@(k-m)\<^bold>| + \<^bold>|u \<cdot> v\<^sup>@i\<^bold>|\<close>
        add_mult_distrib2
      by simp

    have "2*\<^bold>|y\<^sup>@i\<^bold>| + 3*\<^bold>|x\<^bold>| = 2*\<^bold>|v\<^sup>@i\<^bold>| + 3*\<^bold>|u\<^bold>|"
      using lenarg[OF \<open>x \<cdot> y\<^sup>@i\<cdot> x \<cdot> y\<^sup>@i \<cdot> x = u \<cdot> v\<^sup>@i\<cdot> u \<cdot> v\<^sup>@i \<cdot> u\<close>]
      unfolding lenmorph numeral_3_eq_3 numerals(2)
      by linarith

    have "2 * \<^bold>|y \<^sup>@ i\<^bold>| = 2 * \<^bold>|v \<^sup>@ i\<^bold>| + 3 * (2 * \<^bold>|r \<^sup>@ (k - m)\<^bold>|)"
      using \<open>2*\<^bold>|y\<^sup>@i\<^bold>| + 3*\<^bold>|x\<^bold>| = 2*\<^bold>|v\<^sup>@i\<^bold>| + 3*\<^bold>|u\<^bold>|\<close>
      unfolding \<open>\<^bold>|u\<^bold>| = 2 * \<^bold>|r \<^sup>@ (k - m)\<^bold>| + \<^bold>|x\<^bold>|\<close> add_mult_distrib2
      by simp
    hence "2 * \<^bold>|y \<^sup>@ i\<^bold>| = 2 * \<^bold>|v \<^sup>@ i\<^bold>| + 2 * (3 * \<^bold>|r \<^sup>@ (k - m)\<^bold>|)"
      by presburger
    hence "2 * \<^bold>|y \<^sup>@ i\<^bold>| = 2 * (\<^bold>|v \<^sup>@ i\<^bold>| + (3 * \<^bold>|r \<^sup>@ (k - m)\<^bold>|))"
      by simp
    thus "\<^bold>|y \<^sup>@ i\<^bold>| = \<^bold>|v \<^sup>@ i\<^bold>| + 3 * \<^bold>|r \<^sup>@ (k - m)\<^bold>|"
      using nat_mult_eq_cancel1[of 2] zero_less_numeral
      by force
    hence "3 * \<^bold>|r \<^sup>@ (k - m)\<^bold>| \<le> \<^bold>|y \<^sup>@ i\<^bold>|"
      using le_add2 by presburger
    moreover have "\<^bold>|r\<^bold>| \<le> \<^bold>|r \<^sup>@ (k - m)\<^bold>|"
      by (metis CoWBasic.power.power_Suc CoWBasic.power_Suc2 \<open>primitive r\<close> \<open>u \<cdot> v \<^sup>@ i <p x \<cdot> y \<^sup>@ i\<close> \<open>x \<cdot> y \<^sup>@ i = u \<cdot> v \<^sup>@ i \<cdot> r \<^sup>@ (k - m)\<close> not_le prim_comm_short_emp self_append_conv strict_prefix_def)
    ultimately have "3 * \<^bold>|r\<^bold>| \<le> \<^bold>|y \<^sup>@ i\<^bold>|"
      by (meson le_trans mult_le_mono2)
    hence "3 * \<^bold>|r\<^bold>| \<le> i*\<^bold>|y\<^bold>|"
      by (simp add: pow_len)
    moreover have "i \<le> 3*(i-1)"
      using assms(2) by linarith
    ultimately have "3*\<^bold>|r\<^bold>| \<le> 3*((i-1)*\<^bold>|y\<^bold>|)"
      by (metis (no_types, lifting) le_trans mult.assoc mult_le_mono1)
    hence "\<^bold>|r\<^bold>| \<le> (i-1)*\<^bold>|y\<^bold>|"
      by (meson nat_mult_le_cancel1 zero_less_numeral)
    thus "\<^bold>|r\<^bold>| \<le> \<^bold>|y\<^sup>@(i-1)\<^bold>|"
      unfolding pow_len.
  qed
  have "\<^bold>|r\<^bold>| + \<^bold>|y\<^bold>| \<le> \<^bold>|y \<^sup>@ i\<^bold>|"
    using \<open>\<^bold>|r\<^bold>| \<le> \<^bold>|y\<^sup>@(i-1)\<^bold>|\<close> 
    unfolding pow_len nat_add_left_cancel_le[of "\<^bold>|y\<^bold>|" "\<^bold>|r\<^bold>|", symmetric]
    using add.commute \<open>i \<noteq> 0\<close> mult_eq_if
    by force

  have "y\<^sup>@i \<le>s y\<^sup>@i\<cdot>r"
    using triv_suf[of "y \<^sup>@ i" x, unfolded \<open>x \<cdot> y \<^sup>@ i = r \<^sup>@ k\<close>,
        THEN suf_prod_root].
  have "y\<^sup>@i \<le>s y\<^sup>@i\<cdot>y"
    by (simp add: suf_pow_ext')

  from two_pers[reversed, OF \<open>y\<^sup>@i \<le>s y\<^sup>@i\<cdot>r\<close> \<open>y\<^sup>@i \<le>s y\<^sup>@i\<cdot>y\<close> \<open>\<^bold>|r\<^bold>| + \<^bold>|y\<^bold>| \<le> \<^bold>|y \<^sup>@ i\<^bold>|\<close>]
  have "y \<cdot> r = r \<cdot> y".

  have "x \<cdot> y \<^sup>@ i \<cdot> r = r \<cdot> x \<cdot> y \<^sup>@ i"
    by (simp add: power_commutes \<open>x \<cdot> y \<^sup>@ i = r \<^sup>@ k\<close> lassoc)
  hence "x \<cdot> r \<cdot> y \<^sup>@ i  = r \<cdot> x \<cdot> y \<^sup>@ i"
    by (simp add: \<open>y \<cdot> r = r \<cdot> y\<close> comm_add_exp)
  hence "x \<cdot> r = r \<cdot> x"
    by auto

  obtain n where "y = r\<^sup>@n"
    using \<open>primitive r\<close> \<open>y \<cdot> r = r \<cdot> y\<close> by blast
  hence "\<^bold>|y\<^sup>@i\<^bold>| = i*n*\<^bold>|r\<^bold>|"
    by (simp add: pow_len)
  hence "\<^bold>|v \<^sup>@ i\<^bold>| = i*n*\<^bold>|r\<^bold>| - 3 * \<^bold>|r \<^sup>@ (k - m)\<^bold>|"
    using \<open>\<^bold>|y \<^sup>@ i\<^bold>| = \<^bold>|v \<^sup>@ i\<^bold>| + 3 * \<^bold>|r \<^sup>@ (k - m)\<^bold>|\<close>
      diff_add_inverse2 by presburger
  hence "\<^bold>|v \<^sup>@ i\<^bold>| = (i*n - 3*(k-m))*\<^bold>|r\<^bold>|"
    by (simp add: \<open>\<^bold>|v \<^sup>@ i\<^bold>| = i * n * \<^bold>|r\<^bold>| - 3 * \<^bold>|r \<^sup>@ (k - m)\<^bold>|\<close> ab_semigroup_mult_class.mult_ac(1) left_diff_distrib' pow_len)

  have "v\<^sup>@i \<in> r*"
    using per_exp_eq[reversed, OF _ \<open>\<^bold>|v \<^sup>@ i\<^bold>| = (i*n - 3*(k-m))*\<^bold>|r\<^bold>|\<close>]
      \<open>u \<cdot> v \<^sup>@ i = r \<^sup>@ m\<close> suf_prod_root triv_suf by metis

  have "u \<cdot> r = r \<cdot> u"
    using  root_suf_cancel[OF \<open>v \<^sup>@ i \<in> r*\<close> rootI[of r m, folded \<open>u \<cdot> v \<^sup>@ i = r \<^sup>@ m\<close>]]
      self_root[of r] unfolding comm_root
    by blast

  have "v \<cdot> r = r \<cdot> v"
    using comm_drop_exp[OF \<open>i \<noteq> 0\<close>, 
        OF comm_rootI[OF self_root \<open>v\<^sup>@i \<in> r*\<close>]].

  show ?thesis
    using commutesI_root[of "{x, y, u, v}" r]
      prim_comm_root[OF \<open>primitive r\<close> \<open>u \<cdot> r = r \<cdot> u\<close>]
      prim_comm_root[OF \<open>primitive r\<close> \<open>v \<cdot> r = r \<cdot> v\<close>]
      prim_comm_root[OF \<open>primitive r\<close> \<open>x \<cdot> r = r \<cdot> x\<close>]
      prim_comm_root[OF \<open>primitive r\<close> \<open>y \<cdot> r = r \<cdot> y\<close>]
    by auto
qed

theorem "\<not> binary_equality_word (\<zero> \<cdot> \<one>\<^sup>@Suc k \<cdot> \<zero> \<cdot> \<one>)"
proof
  assume "binary_equality_word (\<zero> \<cdot> \<one> \<^sup>@ Suc k \<cdot> \<zero> \<cdot> \<one>)"
  then obtain g' h' where g'_morph: "binary_code_morphism (g' :: binA list \<Rightarrow> nat list)" and h'_morph: "binary_code_morphism h'" and "g' \<noteq> h'" and 
    msol': "(\<zero> \<cdot> \<one> \<^sup>@ Suc k \<cdot> \<zero> \<cdot> \<one>) \<in> g' =\<^sub>M h'"
    using binary_equality_word_def by blast
  interpret g': binary_code_morphism g'
    by fact 
  interpret h': binary_code_morphism h'
    by fact 
  interpret gh: two_morphisms g' h'
    by (simp add: g'.morphism_axioms h'.morphism_axioms two_morphisms_def)
  have "\<^bold>|g'(\<zero> \<cdot> \<one>)\<^bold>| \<noteq> \<^bold>|h'(\<zero> \<cdot> \<one>)\<^bold>|"
  proof
    assume len: "\<^bold>|g'(\<zero> \<cdot> \<one>)\<^bold>| = \<^bold>|h'(\<zero> \<cdot> \<one>)\<^bold>|"
    hence eq1: "g'(\<zero> \<cdot> \<one>) = h'(\<zero> \<cdot> \<one>)" and eq2: "g' (\<one>\<^sup>@k \<cdot> \<zero> \<cdot> \<one>) = h' (\<one>\<^sup>@k \<cdot> \<zero> \<cdot> \<one>)"
      using msol' eqd_eq[OF _ len, of "g' (\<one>\<^sup>@k \<cdot> \<zero> \<cdot> \<one>)" "h' (\<one>\<^sup>@k \<cdot> \<zero> \<cdot> \<one>) "]  
      unfolding minsoldef pow_Suc pow_one g'.morph[symmetric] h'.morph[symmetric] rassoc
      by blast+
    hence "g' (\<one>\<^sup>@k) = h' (\<one>\<^sup>@k)"
      by (simp add: g'.morph h'.morph)
    show False
    proof (cases "k = 0")
      assume "k = 0"
      from minsolD_min[OF msol' _ _ eq1, unfolded \<open>k = 0\<close> pow_one]
      show False by simp
    next
      assume "k \<noteq> 0"
      hence "g' (\<one>) = h' (\<one>)"
        using \<open>g' (\<one>\<^sup>@k) = h' (\<one>\<^sup>@k)\<close>
        unfolding g'.pow_morph h'.pow_morph using  pow_eq_eq by blast
      hence "g' (\<zero>) = h' (\<zero>)" 
        using \<open>g'(\<zero> \<cdot> \<one>) = h'(\<zero> \<cdot> \<one>)\<close> unfolding g'.morph h'.morph
        by simp
      show False 
        using gh.def_on_sings_eq[OF finite_2.induct[of "\<lambda> a. g'[a] = h'[a]", OF \<open>g' (\<zero>) = h' (\<zero>)\<close> \<open>g' (\<one>) = h' (\<one>)\<close>]]
          \<open>g' \<noteq> h'\<close> by blast
    qed
  qed
  then have less': "\<^bold>|(if \<^bold>|g' (\<zero> \<cdot> \<one>)\<^bold>| < \<^bold>|h' (\<zero> \<cdot> \<one>)\<^bold>| then g' else h') (\<zero> \<cdot> \<one>)\<^bold>|
    < \<^bold>|(if \<^bold>|g' (\<zero> \<cdot> \<one>)\<^bold>| < \<^bold>|h' (\<zero> \<cdot> \<one>)\<^bold>| then h' else g') (\<zero> \<cdot> \<one>)\<^bold>|"
    by simp 
  obtain g h where g_morph: "binary_code_morphism (g :: binA list \<Rightarrow> nat list)" and h_morph: "binary_code_morphism h"
    and msol: "g (\<zero> \<cdot> \<one> \<^sup>@ Suc k \<cdot> \<zero> \<cdot> \<one>) = h (\<zero> \<cdot> \<one> \<^sup>@ Suc k \<cdot> \<zero> \<cdot> \<one>)" and less: "\<^bold>|g(\<zero> \<cdot> \<one>)\<^bold>| < \<^bold>|h(\<zero> \<cdot> \<one>)\<^bold>|"
    using that[of "(if \<^bold>|g' (\<zero> \<cdot> \<one>)\<^bold>| < \<^bold>|h' (\<zero> \<cdot> \<one>)\<^bold>| then g' else h')" "(if \<^bold>|g' (\<zero> \<cdot> \<one>)\<^bold>| < \<^bold>|h' (\<zero> \<cdot> \<one>)\<^bold>| then h' else g')", OF _ _ _ less']
      g'_morph h'_morph minsolD[OF msol']  by presburger  
  interpret g: binary_code_morphism g
    using g_morph by blast
  interpret h: binary_code_morphism h
    using h_morph by blast
  have "g \<one> \<le>s g (\<zero> \<cdot> \<one>)" and "h \<one> \<le>s h (\<zero> \<cdot> \<one>)" 
    unfolding g.morph h.morph by blast+
  from not_bew_baiba[OF less this, of k] msol
  have "commutes {g \<one>, g (\<zero> \<cdot> \<one>), h \<one>, h (\<zero> \<cdot> \<one>)}"
    unfolding g.morph h.morph g.pow_morph h.pow_morph pow_Suc rassoc by blast
  hence "g \<one> \<cdot> g (\<zero> \<cdot> \<one>) = g (\<zero> \<cdot> \<one>) \<cdot> g \<one>"
    unfolding commutes_def by blast
  from this[unfolded g.morph lassoc cancel_right]
  show False
    using g.non_comm_morph by simp
qed

end