(*  Title:      CoW/Periodicity_Lemma.thy
    Author:     Štěpán Holub, Charles University

Part of Combinatorics on Words Formalized. See https://gitlab.com/formalcow/combinatorics-on-words-formalized/
*)

theory Periodicity_Lemma
  imports CoWBasic
begin

chapter "The Periodicity Lemma"

text\<open>The Periodicity Lemma says that if a sufficiently long word has two periods p and q,
then the period can be refined to @{term "gcd p q"}.
The consequence is equivalent to the fact that the corresponding periodic roots commute.
``Sufficiently long'' here means at least @{term "p + q - gcd p q"}.
It is also known as the Fine and Wilf theorem due to its authors @{cite FineWilf}.\<close>

text\<open>
If we relax the requirement to @{term "p + q"}, then the claim becomes easy, and it is proved in @{theory Combinatorics_Words.CoWBasic} as @{term two_pers_root}: @{thm[names_long] two_pers_root[no_vars]}.
\<close>

theorem per_lemma_relaxed:
  assumes "period w p" and  "period w q" and  "p + q \<le> \<^bold>|w\<^bold>|"
  shows "(take p w)\<cdot>(take q w) = (take q w)\<cdot>(take p w)"
  using   two_pers_root[OF
      \<open>period w p\<close>[unfolded period_def[of w p]]
      \<open>period w q\<close>[unfolded period_def[of w q]], unfolded
      take_len[OF add_leD1[OF \<open>p + q \<le> \<^bold>|w\<^bold>|\<close>]]
      take_len[OF add_leD2[OF \<open>p + q \<le> \<^bold>|w\<^bold>|\<close>]], OF \<open>p + q \<le> \<^bold>|w\<^bold>|\<close>].

text\<open>Also in terms of the numeric period:\<close>

thm two_periods

section \<open>Main claim\<close>

text\<open>We first formulate the claim of the Periodicity lemma in terms of commutation of two periodic roots.
For trivial reasons we can also drop the requirement that the roots are nonempty.
\<close>

theorem per_lemma_comm:
  assumes "w \<le>p r \<cdot> w" and "w \<le>p s \<cdot> w"
    and len: "\<^bold>|r\<^bold>| + \<^bold>|s\<^bold>| - (gcd \<^bold>|r\<^bold>| \<^bold>|s\<^bold>|) \<le> \<^bold>|w\<^bold>|"
  shows "r \<cdot> s = s \<cdot> r"
  using assms
proof (induction "\<^bold>|s\<^bold>| + \<^bold>|s\<^bold>| + \<^bold>|r\<^bold>|" arbitrary: w r s rule: less_induct)
  case less
  consider (empty) "s = \<epsilon>" | (short)  "\<^bold>|r\<^bold>| < \<^bold>|s\<^bold>|" | (step) "s \<noteq> \<epsilon> \<and> \<^bold>|s\<^bold>| \<le> \<^bold>|r\<^bold>|" by force
  then show ?case
  proof (cases)
    case (empty)
    thus "r \<cdot> s = s \<cdot> r" by fastforce
  next
    case (short)
    thus "r \<cdot> s = s \<cdot> r"
      using  "less.hyps"[OF  _ \<open> w \<le>p s \<cdot> w\<close> \<open> w \<le>p r \<cdot> w\<close>
      \<open>\<^bold>|r\<^bold>| + \<^bold>|s\<^bold>| - (gcd \<^bold>|r\<^bold>| \<^bold>|s\<^bold>|) \<le> \<^bold>|w\<^bold>|\<close>[unfolded gcd.commute[of "\<^bold>|r\<^bold>|"] add.commute[of "\<^bold>|r\<^bold>|"]]] by fastforce
   next
     case (step)
    hence  "s \<noteq> \<epsilon>" and "\<^bold>|s\<^bold>| \<le> \<^bold>|r\<^bold>|" by blast+
    from le_add_diff[OF gcd_le2_nat[OF \<open>s \<noteq> \<epsilon>\<close>[folded length_0_conv], of "\<^bold>|r\<^bold>|"], unfolded gcd.commute[of "\<^bold>|r\<^bold>|"], of "\<^bold>|r\<^bold>|"]
    have "\<^bold>|r\<^bold>| \<le> \<^bold>|w\<^bold>|"
      using  \<open>\<^bold>|r\<^bold>| + \<^bold>|s\<^bold>| - (gcd \<^bold>|r\<^bold>| \<^bold>|s\<^bold>|) \<le> \<^bold>|w\<^bold>|\<close>[unfolded gcd.commute[of "\<^bold>|r\<^bold>|"] add.commute[of "\<^bold>|r\<^bold>|"]] order.trans by blast
    hence "\<^bold>|s\<^bold>| \<le> \<^bold>|w\<^bold>|"
      using \<open>\<^bold>|s\<^bold>| \<le> \<^bold>|r\<^bold>|\<close> order.trans by blast
    from pref_prod_long[OF  \<open>w \<le>p s \<cdot> w\<close> this]
    have "s \<le>p w".

    obtain w' where "s \<cdot> w' = w" and "\<^bold>|w'\<^bold>| < \<^bold>|w\<^bold>|"
      using \<open>s \<noteq> \<epsilon>\<close> \<open>s \<le>p w\<close>[unfolded prefix_def]
      by force
    have "w' \<le>p w"
      using \<open>w \<le>p s \<cdot> w\<close> unfolding \<open>s \<cdot> w' = w\<close>[symmetric] pref_cancel_conv.
    from this[folded \<open>s \<cdot> w' = w\<close>]
    have "w' \<le>p s\<cdot>w'".

    have "s \<le>p r"
      using pref_prod_le[OF prefix_order.trans[OF \<open>s \<le>p w\<close> \<open>w \<le>p r \<cdot> w\<close>] \<open>\<^bold>|s\<^bold>| \<le> \<^bold>|r\<^bold>|\<close>].
    hence  "w' \<le>p (s\<inverse>\<^sup>>r) \<cdot> w'"
      using \<open>w \<le>p r \<cdot> w\<close> \<open>s \<cdot> w' = w\<close> pref_prod_pref[OF _ \<open>w' \<le>p w\<close>, of "s\<inverse>\<^sup>>r"]
      unfolding prefix_def by fastforce

   have ind_len: "\<^bold>|s\<inverse>\<^sup>>r\<^bold>| + \<^bold>|s\<^bold>|  - (gcd \<^bold>|s\<inverse>\<^sup>>r\<^bold>| \<^bold>|s\<^bold>|) \<le> \<^bold>|w'\<^bold>|"
      using \<open>\<^bold>|r\<^bold>| + \<^bold>|s\<^bold>| - (gcd \<^bold>|r\<^bold>| \<^bold>|s\<^bold>|) \<le> \<^bold>|w\<^bold>|\<close>[folded \<open>s \<cdot> w' = w\<close>]
      unfolding pref_gcd_lq[OF \<open>s \<le>p r\<close>, unfolded gcd.commute[of "\<^bold>|s\<^bold>|"]] lenmorph lq_short_len[OF \<open>s \<le>p r\<close>, unfolded add.commute[of "\<^bold>|s\<^bold>|"]] by force

    have "s \<cdot> s\<inverse>\<^sup>>r = s\<inverse>\<^sup>>r \<cdot> s"
      using "less.hyps"[OF  _ \<open>w' \<le>p (s\<inverse>\<^sup>>r) \<cdot> w'\<close>  \<open>w' \<le>p s \<cdot> w'\<close> ind_len] \<open>s \<le>p r\<close> \<open>\<^bold>|w'\<^bold>| < \<^bold>|w\<^bold>|\<close>
        unfolding prefix_def
        by force

    thus "r \<cdot> s = s \<cdot> r"
       using \<open>s \<le>p r\<close> by (fastforce simp add: prefix_def)
  qed
qed

lemma per_lemma_comm_pref:
  assumes "u \<le>p r\<^sup>@k" "u \<le>p s\<^sup>@l"
      and len: "\<^bold>|r\<^bold>| + \<^bold>|s\<^bold>| - gcd (\<^bold>|r\<^bold>|) (\<^bold>|s\<^bold>|) \<le> \<^bold>|u\<^bold>|"
    shows "r \<cdot> s = s \<cdot> r"
  using  pref_prod_root[OF assms(2)] pref_prod_root[OF assms(1)] per_lemma_comm[OF _ _ len] by blast

text\<open>We can now prove the numeric version.\<close>

theorem per_lemma: assumes "period w p" and "period w q" and len: "p + q - gcd p q \<le> \<^bold>|w\<^bold>|"
  shows  "period w (gcd p q)"
proof-
  have takep: "w \<le>p (take p w) \<cdot> w" and takeq: "w \<le>p (take q w) \<cdot> w"
    using \<open>period w p\<close> \<open>period w q\<close> per_pref by blast+
  have "p \<le> \<^bold>|w\<^bold>|"
    using per_lemma_len_le[OF len] per_not_zero[OF \<open>period w q\<close>].
  have lenp: "\<^bold>|take p w\<^bold>| = p"
    using gcd_le2_pos[OF per_not_zero[OF \<open>period w q\<close>], of p] len take_len
    by auto
  have lenq: "\<^bold>|take q w\<^bold>| = q"
    using gcd_le1_pos[OF per_not_zero[OF \<open>period w p\<close>], of q] len take_len
    by simp
  obtain t where "take p w \<in> t*" and "take q w \<in> t*"
    using comm_rootE[OF per_lemma_comm[OF takep takeq, unfolded lenp lenq, OF len], of thesis] by blast
  have "w <p t \<cdot> w"
    using \<open>period w p\<close>[unfolded period_def, THEN per_root_trans, OF \<open>take p w \<in> t*\<close>].
  with per_nemp[OF \<open>period w q\<close>]
  have "period w \<^bold>|t\<^bold>|"
    by (rule periodI)
  have "\<^bold>|t\<^bold>| dvd (gcd p q)"
    using  common_root_len_gcd[OF \<open>take p w \<in> t*\<close> \<open>take q w \<in> t*\<close>] unfolding  lenp lenq.
  from dvd_div_mult_self[OF this]
  have "gcd p q div \<^bold>|t\<^bold>| * \<^bold>|t\<^bold>| = gcd p q".
  have "gcd p q \<noteq> 0"
    using \<open>period w p\<close> by auto
  from this[folded dvd_div_eq_0_iff[OF \<open>\<^bold>|t\<^bold>| dvd (gcd p q)\<close>]]
  show "period w (gcd p q)"
    using  per_mult[OF \<open>period w \<^bold>|t\<^bold>|\<close>, of "gcd p q div \<^bold>|t\<^bold>|", unfolded dvd_div_mult_self[OF \<open>\<^bold>|t\<^bold>| dvd (gcd p q)\<close>]] by blast
qed

section \<open>Optimality\<close>

text\<open>@{term "FW_word"} (where FW stands for  Fine and Wilf) yields a word which show the optimality of the bound in the Periodicity lemma.
    Moreover, the obtained word has maximum possible letters (each equality of letters is forced by periods). The latter is not proved here.\<close>

term "butlast ([0..<(gcd p q)]\<^sup>@(p div (gcd p q)))\<cdot>[gcd p q]\<cdot>(butlast ([0..<(gcd p q)]\<^sup>@(p div (gcd p q))))"

\<comment> \<open>an auxiliary claim\<close>
lemma ext_per_sum: assumes "period w p" and "period w q" and  "p \<le> \<^bold>|w\<^bold>|"
  shows "period ((take p w) \<cdot> w) (p+q)"
proof-
  have nemp: "take p w \<cdot> take q w \<noteq> \<epsilon>"
    using \<open>period w p\<close> by auto
  have "take (p + q) (take p w \<cdot> w) = take p (take p w \<cdot> w) \<cdot> take q (drop p (take p w \<cdot> w))"
    using take_add by blast
  also have "... = take p w \<cdot> take q w"
    by (simp add: \<open>p \<le> \<^bold>|w\<^bold>|\<close>)
  ultimately have sum: "take (p + q) (take p w \<cdot> w) = take p w \<cdot> take q w"
    by presburger
  note assms[unfolded period_def]
  show ?thesis
    unfolding period_def sum rassoc
    using pref_spref_prolong[OF self_pref spref_spref_prolong[OF \<open>w <p take q w \<cdot> w\<close> \<open>w <p take p w \<cdot> w\<close>]].
qed

definition "fw_p_per p q \<equiv> butlast ([0..<(gcd p q)]\<^sup>@(p div (gcd p q)))"
definition "fw_base p q \<equiv> fw_p_per p q \<cdot> [gcd p q]\<cdot> fw_p_per p q"

fun FW_word :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  FW_word_def: "FW_word p q =
\<comment>\<open>symmetry\<close>           (if q < p then  FW_word q p else
\<comment>\<open>artificial value\<close>   if p = 0 then \<epsilon> else
\<comment>\<open>artificial value\<close>   if p = q then \<epsilon> else
\<comment>\<open>base case\<close>          if gcd p q = q - p then fw_base p q
\<comment>\<open>step\<close>               else (take p (FW_word p (q-p))) \<cdot> FW_word p (q-p))"

lemma FW_sym: "FW_word p q = FW_word q p"
  by (cases rule: linorder_cases[of p q]) simp+

theorem fw_word': "\<not> p dvd q \<Longrightarrow> \<not> q dvd p \<Longrightarrow>
 \<^bold>|FW_word p q\<^bold>| = p + q - gcd p q - 1 \<and> period (FW_word p q) p \<and> period (FW_word p q) q \<and> \<not> period (FW_word p q) (gcd p q)"
proof (induction "p + p + q" arbitrary: p q rule: less_induct)
  case less
  have "p \<noteq> 0"
    using  \<open>\<not> q dvd p\<close> dvd_0_right[of q] by meson
  have "p \<noteq> q"
    using \<open>\<not> p dvd q\<close> by auto
  then consider "q < p" | "p < q"
    by linarith
  then show ?case
  proof (cases)
    assume "q < p"
    have less: "q + q + p < p + p + q"
      by (simp add: \<open>q < p\<close>)
    thus ?case
      using "less.hyps"[OF _ \<open>\<not> q dvd p\<close> \<open>\<not> p dvd q\<close>]
      unfolding FW_sym[of p q] gcd.commute[of p q] add.commute[of p q] by blast
  next
    let ?d = "gcd p q"
    let ?dw = "[0..<(gcd p q)]"
    let ?pd = "p div (gcd p q)"
    assume "p < q"
    thus ?thesis
    proof (cases "?d = q - p")
      assume "?d = q - p" hence "p + ?d = q" using \<open>p < q\<close> by auto
      hence "p \<noteq> q" and "\<not> q < p" using \<open>p \<noteq> 0\<close> \<open>p < q\<close> by fastforce+
      hence fw: "FW_word p q = fw_base p q"
        unfolding FW_word_def[of p q] using \<open>p \<noteq> 0\<close>  \<open>gcd p q = q - p\<close> by presburger


      have "\<^bold>|[0..<gcd p q]\<^bold>| = gcd p q"
        by simp
      hence *: "p div gcd p q * \<^bold>|[0..<gcd p q]\<^bold>| = p"
        by fastforce
      have ppref: "\<^bold>|butlast (?dw\<^sup>@?pd)\<cdot>[?d]\<^bold>| = p"
        using  \<open>p \<noteq> 0\<close> unfolding lenmorph pow_len length_butlast sing_len * by fastforce
      note ppref' = this[unfolded lenmorph]
      have qpref: "\<^bold>|butlast (?dw\<^sup>@?pd)\<cdot>[?d]\<cdot>?dw\<^bold>| = q"
        unfolding lassoc lenmorph ppref' using  \<open>p + gcd p q = q\<close> by simp
      have "butlast (?dw\<^sup>@?pd)\<cdot>[?d] \<le>p FW_word p q"
        unfolding fw fw_base_def fw_p_per_def lassoc  using triv_pref.
      from pref_take[OF this]
      have takep: "take p (FW_word p q) = butlast (?dw\<^sup>@?pd)\<cdot>[?d]"
        unfolding ppref.

      have "?dw \<noteq> \<epsilon>" and "\<^bold>|?dw\<^bold>| = ?d"
        using \<open>p \<noteq> 0\<close> by auto
      have "?pd \<noteq> 0"
        by (simp add: \<open>p \<noteq> 0\<close> dvd_div_eq_0_iff)
      from not0_implies_Suc[OF this]
      obtain e where "?pd = Suc e"  by blast
      have "gcd p q \<noteq> p"
        using \<open>\<not> p dvd q\<close> gcd_dvd2[of p q] by force
      hence "Suc e \<noteq> 1"
        using dvd_mult_div_cancel[OF gcd_dvd1[of p q], unfolded \<open>?pd = Suc e\<close>] by force
      hence "e \<noteq> 0" by simp

      have "[0..<gcd p q] \<^sup>@ e \<noteq> \<epsilon>"
        using \<open>[0..<gcd p q] \<noteq> \<epsilon>\<close> \<open>e \<noteq> 0\<close> nonzero_pow_emp by blast
      hence but_dec: "butlast (?dw\<^sup>@?pd) = ?dw \<cdot> butlast (?dw\<^sup>@e)"
        unfolding \<open>?pd = Suc e\<close> pow_Suc butlast_append  if_not_P[OF \<open>[0..<gcd p q] \<^sup>@ e \<noteq> \<epsilon>\<close>] by blast
      have but_dec_b: "butlast (?dw\<^sup>@?pd) = ?dw\<^sup>@e \<cdot> butlast ?dw"
        unfolding \<open>?pd = Suc e\<close> pow_Suc' butlast_append if_not_P[OF \<open>?dw \<noteq> \<epsilon>\<close>] by blast
      have "butlast (?dw\<^sup>@?pd)\<cdot>[?d]\<cdot>?dw \<le>p FW_word p q"
        unfolding fw but_dec lassoc fw_base_def fw_p_per_def by blast
      note takeq = pref_take[OF this, unfolded qpref]

      have "\<^bold>|FW_word p q\<^bold>| = p + q - gcd p q - 1"
      proof-
        have "p + q - (q - p) = p + p"
          using \<open>p + gcd p q = q\<close> by auto
        hence "\<^bold>|?dw\<^sup>@?pd\<^bold>| = p"
           unfolding pow_len \<open>\<^bold>|[0..<gcd p q]\<^bold>| = gcd p q\<close> by force
        hence "\<^bold>|butlast (?dw\<^sup>@?pd)\<^bold>| = p - 1"
          unfolding length_butlast by argo
        hence "\<^bold>|FW_word p q\<^bold>| = (p - 1) + 1 +  (p - 1)"
          unfolding fw lenmorph sing_len fw_base_def fw_p_per_def by presburger
        thus "\<^bold>|FW_word p q\<^bold>| = p + q - gcd p q - 1"
          unfolding \<open>gcd p q = q - p\<close> \<open>p + q - (q - p) = p + p\<close>  using \<open>p \<noteq> 0\<close> by fastforce
      qed

      have "period (FW_word p q) p"
        unfolding period_def
      proof (rule per_rootI)
        show "take p (FW_word p q) \<noteq> \<epsilon>"
          using \<open>p \<noteq> 0\<close>  unfolding length_0_conv[symmetric] ppref[folded takep].
        have "fw_base p q \<le>p fw_p_per p q \<cdot> [gcd p q] \<cdot> fw_base p q"
          unfolding rassoc pref_cancel_conv fw_base_def fw_p_per_def by blast
        thus "FW_word p q \<le>p take p (FW_word p q) \<cdot> FW_word p q"
          unfolding fw rassoc fw_p_per_def takep[unfolded fw].
      qed

      have "period (FW_word p q) q"
        unfolding period_def
      proof (rule per_rootI)
        show "take q (FW_word p q) \<noteq> \<epsilon>"
          unfolding length_0_conv[symmetric] qpref[folded takeq] using \<open>p \<noteq> 0\<close> \<open>p < q\<close> by linarith
        have "butlast ([0..<gcd p q] \<^sup>@ (p div gcd p q)) \<le>p [0..<gcd p q] \<cdot> butlast ([0..<gcd p q] \<^sup>@ (p div gcd p q))"
          using pref_prod_root[OF prefixeq_butlast[of "[0..<gcd p q] \<^sup>@ (p div gcd p q)"]].
        from pref_ext[OF this, unfolded rassoc]
        have "fw_base p q \<le>p fw_p_per p q \<cdot> [gcd p q] \<cdot> [0..<gcd p q] \<cdot> fw_base p q"
          unfolding rassoc pref_cancel_conv fw_base_def fw_p_per_def.
        thus "FW_word p q \<le>p take q (FW_word p q) \<cdot> FW_word p q"
          unfolding fw rassoc fw_p_per_def takeq[unfolded fw].
      qed

      have "\<not> period (FW_word p q) ?d"
      proof-
        have last_a: "last (take p (FW_word p q)) = ?d"
          unfolding takep nth_append_length[of "butlast (?dw \<^sup>@ ?pd)" "?d" \<epsilon>]
            last_snoc by blast
        have "?dw \<le>p FW_word p q"
          unfolding fw but_dec rassoc fw_base_def fw_p_per_def by blast
        from pref_take[OF this, unfolded \<open>\<^bold>|?dw\<^bold>| = ?d\<close>]
        have takegcd:  "take (gcd p q) (FW_word p q) = [0..<gcd p q]".
        have fw_dec_b: "FW_word p q = [0..<gcd p q]\<^sup>@e \<cdot> butlast ([0..<gcd p q]) \<cdot> [?d] \<cdot> (butlast ([0..<gcd p q]\<^sup>@(p div gcd p q)))"
          unfolding fw but_dec_b rassoc fw_base_def fw_p_per_def ..
        have gcdepref:  "[0..<gcd p q]\<^sup>@ Suc e \<le>p take (gcd p q) (FW_word p q) \<cdot> FW_word p q"
          unfolding takegcd pow_Suc pref_cancel_conv unfolding fw_dec_b by blast
        have "\<^bold>|[0..<gcd p q]\<^sup>@ Suc e\<^bold>| = p"
          unfolding pow_len \<open>\<^bold>|?dw\<^bold>| = ?d\<close> \<open>?pd = Suc e\<close>[symmetric] using
            dvd_div_mult_self[OF gcd_dvd1].
        from pref_take[OF gcdepref, unfolded this]
        have takegcdp:  "take p (take (gcd p q) (FW_word p q) \<cdot> (FW_word p q)) = [0..<gcd p q]\<^sup>@e \<cdot> [0..<gcd p q]"
          unfolding pow_Suc'.
        have "0 < gcd p q" by (simp add: \<open>p \<noteq> 0\<close>)
        from last_upt[OF this]
        have last_b: "last (take p (take (gcd p q) (FW_word p q) \<cdot> (FW_word p q))) = gcd p q - 1"
          unfolding takegcdp  last_appendR[of "[0..<gcd p q]" "[0..<gcd p q]\<^sup>@e", OF \<open>[0..<gcd p q] \<noteq> \<epsilon>\<close>].
        have "p \<le> \<^bold>|FW_word p q\<^bold>|"
          unfolding \<open>\<^bold>|FW_word p q\<^bold>| = p + q - gcd p q - 1\<close> \<open>gcd p q = q - p\<close> using  \<open>p < q\<close> by auto
        have "gcd p q \<noteq> gcd p q - 1"
          using \<open>gcd p q = q - p\<close> \<open>p < q\<close> by linarith
        hence "take p (FW_word p q) \<noteq> take p (take (gcd p q) (FW_word p q) \<cdot> (FW_word p q))"
          unfolding last_b[symmetric] unfolding last_a[symmetric] using arg_cong[of _ _ last] by blast
        hence "\<not> FW_word p q \<le>p take (gcd p q) (FW_word p q) \<cdot> FW_word p q "
          using pref_share_take[OF _ \<open>p \<le> \<^bold>|FW_word p q\<^bold>|\<close>, of "take (gcd p q) (FW_word p q) \<cdot> FW_word p q"] by blast
        thus "\<not> period (FW_word p q) (gcd p q)"
          unfolding period_def by blast
      qed

      show ?thesis
        using \<open>period (FW_word p q) p\<close> \<open>period (FW_word p q) q\<close>
          \<open>\<^bold>|FW_word p q\<^bold>| = p + q - gcd p q - 1\<close> \<open>\<not> period (FW_word p q) (gcd p q)\<close> by blast
    next
      let ?d' = "gcd p (q-p)"
      assume "gcd p q \<noteq> q - p"
      hence fw: "FW_word p q = (take p (FW_word p (q-p))) \<cdot> FW_word p (q-p)"
        using FW_word_def \<open>p \<noteq> 0\<close> \<open>p \<noteq> q\<close> \<open>p < q\<close> by (meson less_Suc_eq not_less_eq)

      have divhyp1: "\<not> p dvd q - p"
        using \<open>\<not> p dvd q\<close> \<open>p < q\<close> dvd_minus_self by auto

      have divhyp2: "\<not> q - p dvd p"
      proof (rule notI)
        assume "q - p dvd p"
        have "q = p + (q - p)"
          by (simp add: \<open>p < q\<close> less_or_eq_imp_le)
        from gcd_add2[of p "q - p", folded  this, unfolded gcd_nat.absorb2[of "q - p" p, OF \<open>q - p dvd p\<close>]]
        show "False"
          using \<open>gcd p q \<noteq> q - p\<close> by blast
      qed

      have lenhyp: "p + p + (q - p) < p + p + q"
        using \<open>p < q\<close> \<open>p \<noteq> 0\<close> by linarith

\<comment> \<open>induction assumption\<close>
      have "\<^bold>|FW_word p (q - p)\<^bold>| = p + (q - p) - ?d' - 1" and "period (FW_word p (q-p)) p" and "period (FW_word p (q-p)) (q-p)" and
        "\<not> period (FW_word p (q-p)) (gcd p (q-p))"
        using "less.hyps"[OF _ divhyp1 divhyp2] lenhyp
        by blast+

\<comment> \<open>auxiliary facts\<close>
      have "p + (q - p) = q"
         using divhyp1 dvd_minus_self by auto
      have "?d = ?d'"
        using  gcd_add2[of p "q-p", unfolded le_add_diff_inverse[OF less_imp_le[OF \<open>p < q\<close>]]].
      have "?d \<noteq> q"
        using  \<open>\<not> q dvd p\<close>  gcd_dvd2[of q p, unfolded gcd.commute[of q]] by force
      from this[unfolded nat_neq_iff]
      have "?d < q"
        using  gr_implies_not0 \<open>p < q\<close> nat_dvd_not_less by blast
      hence "1 \<le> q - ?d"
        by linarith
      have "?d' < q - p"
        using  gcd_le2_pos[OF per_not_zero[OF \<open>period (FW_word p (q - p)) (q - p)\<close>], of p]  divhyp2[unfolded  gcd_nat.absorb_iff2] nat_less_le by blast
      hence "p \<le> \<^bold>|(FW_word p (q - p))\<^bold>|"
        unfolding  \<open>\<^bold>|FW_word p (q - p)\<^bold>| = p + (q - p) - ?d' - 1\<close>  diff_diff_left discrete by linarith
      have "FW_word p (q - p) \<noteq> \<epsilon>"
        unfolding length_0_conv[symmetric] using  \<open>p \<le> \<^bold>|FW_word p (q - p)\<^bold>|\<close> \<open>p \<noteq> 0\<close>[folded le_zero_eq]
        by linarith

\<comment> \<open>claim 1\<close>
      have "\<^bold>|FW_word p q\<^bold>| = p + q - ?d - 1"
      proof-
        have "p + (q - p) = q" using less_imp_le[OF \<open>p < q\<close>] by fastforce
        have "\<^bold>|FW_word p q\<^bold>| = \<^bold>|take p (FW_word p (q - p))\<^bold>| + \<^bold>|FW_word p (q - p)\<^bold>|"
          using fw lenmorph[of "take p (FW_word p (q - p))" "FW_word p (q - p)"]
          by presburger
        also have "... = p + (p + (q - p) - ?d' - 1)"
          unfolding \<open>\<^bold>|FW_word p (q - p)\<^bold>| = p + (q - p) - ?d' - 1\<close>
            take_len[OF \<open>p \<le> \<^bold>|FW_word p (q - p)\<^bold>|\<close>] by blast
        also have "... = p + (q - ?d  - 1)"
          unfolding \<open>?d = ?d'\<close> \<open>p + (q - p) = q\<close>..
        also have "... = p + (q - ?d) - 1"
          using Nat.add_diff_assoc[OF \<open>1 \<le> q - ?d\<close>].
        also have "... = p + q - ?d - 1"
          by (simp add: \<open>?d < q\<close> less_or_eq_imp_le)
        finally show "\<^bold>|FW_word p q\<^bold>| = p + q - ?d - 1"
          by presburger
      qed

\<comment> \<open>claim 2\<close>
      have "period (FW_word p q) p"
        using fw  ext_per_left[OF \<open>period (FW_word p (q-p)) p\<close> \<open>p \<le> \<^bold>|FW_word p (q - p)\<^bold>|\<close>]
        by presburger

\<comment> \<open>claim 3\<close>
      have "period (FW_word p q) q"
        using ext_per_sum[OF \<open>period (FW_word p (q - p)) p\<close> \<open>period (FW_word p (q - p)) (q - p)\<close> \<open>p \<le> \<^bold>|FW_word p (q - p)\<^bold>|\<close>, folded fw, unfolded \<open>p + (q-p) = q\<close>].

\<comment> \<open>claim 4\<close>
      have "\<not> period (FW_word p q) ?d"
        using \<open>\<not> period (FW_word p (q -p)) (gcd p (q-p))\<close>
        unfolding \<open>?d = ?d'\<close>[symmetric]
        using period_fac[of "take p (FW_word p (q - p))" "FW_word p (q - p)" \<epsilon> "?d", unfolded append_Nil2,
                          OF _ \<open>FW_word p (q - p) \<noteq> \<epsilon>\<close>, folded fw] by blast
      thus ?thesis
        using \<open>period (FW_word p q) p\<close> \<open>period (FW_word p q) q\<close> \<open>\<^bold>|FW_word p q\<^bold>| = p + q - ?d - 1\<close> by blast
    qed
  qed
qed

theorem fw_word: assumes "\<not> p dvd q" "\<not> q dvd p"
  shows "\<^bold>|FW_word p q\<^bold>| = p + q - gcd p q - 1" and "period (FW_word p q) p" and  "period (FW_word p q) q" and "\<not> period (FW_word p q) (gcd p q)"
  using fw_word'[OF assms] by blast+

text\<open>Calculation examples\<close>


section "Other variants of the periodicity lemma"

text \<open>Periodicity lemma is one of the most frequent tools in Combinatorics on words.
   Here are some useful variants.\<close>

text\<open>Note that the following lemmas are stronger versions of @{thm per_lemma_pref_suf fac_two_conjug_primroot fac_two_conjug_primroot' fac_two_conjug_primroot'' fac_two_prim_conjug} that have a relaxed length assumption @{term "\<^bold>|p\<^bold>| + \<^bold>|q\<^bold>| \<le> \<^bold>|w\<^bold>|"} instead of @{term "\<^bold>|p\<^bold>| + \<^bold>|q\<^bold>| - (gcd \<^bold>|p\<^bold>| \<^bold>|q\<^bold>|) \<le> \<^bold>|w\<^bold>|"} (and which follow from the relaxed version of periodicity lemma @{thm two_pers}.\<close>


lemma per_lemma_pref_suf_gcd: assumes "w <p p \<cdot> w" and "w <s w \<cdot> q" and
  fw: "\<^bold>|p\<^bold>| + \<^bold>|q\<^bold>| - (gcd \<^bold>|p\<^bold>| \<^bold>|q\<^bold>|) \<le> \<^bold>|w\<^bold>|"
obtains r s k l m where "p = (r \<cdot> s)\<^sup>@k" and "q = (s \<cdot> r)\<^sup>@l" and "w = (r \<cdot> s)\<^sup>@m \<cdot> r" and "primitive (r\<cdot>s)"
proof-
  let ?q = "(w \<cdot> q)\<^sup><\<inverse>w"
  have "w <p ?q \<cdot> w"
    using ssufD1[OF \<open>w <s w \<cdot> q\<close>] rq_suf[symmetric, THEN per_rootI[OF prefI rq_ssuf[OF \<open>w <s w \<cdot> q\<close>]]]
    by argo
  have "q \<sim> ?q"
    by (meson assms(2) conjugI1 conjug_sym rq_suf suffix_order.less_imp_le)

  have nemps': "p \<noteq> \<epsilon>" "?q \<noteq> \<epsilon>"
    using assms(1) \<open>w <p ?q\<cdot>w\<close> by fastforce+
  have "\<^bold>|p\<^bold>| + \<^bold>|?q\<^bold>| - gcd (\<^bold>|p\<^bold>|) (\<^bold>|?q\<^bold>|) \<le> \<^bold>|w\<^bold>|" using fw
    unfolding conjug_len[OF \<open>q \<sim> ?q\<close>].
  from per_lemma_comm[OF sprefD1[OF \<open>w <p p \<cdot> w\<close>] sprefD1[OF \<open>w <p ?q\<cdot>w\<close>] this]
  have "p \<cdot> ?q = ?q \<cdot> p".
  then have "\<rho> p = \<rho> ?q" using comm_primroots[OF nemps'] by force
  hence [symmetric]: "\<rho> q \<sim> \<rho> p"
    using conjug_primroot[OF \<open>q \<sim> (w \<cdot> q)\<^sup><\<inverse>w\<close>]
    by argo
  from conjug_primrootsE[OF this]
  obtain r s k l where
    "p = (r \<cdot> s) \<^sup>@ k" and
    "q = (s \<cdot> r) \<^sup>@ l" and
    "primitive (r \<cdot> s)".
  have "w \<le>p (r\<cdot>s)\<cdot>w"
    using assms per_root_drop_exp  sprefD1 \<open>p = (r \<cdot> s) \<^sup>@ k\<close>
    by meson
  have "w \<le>s w\<cdot>(s\<cdot>r)"
    using assms(2) per_root_drop_exp[reversed] ssufD1 \<open>q = (s \<cdot> r) \<^sup>@ l\<close>
    by meson
  have "\<^bold>|r \<cdot> s\<^bold>| \<le> \<^bold>|w\<^bold>|"
    using conjug_nemp_iff[OF \<open>q \<sim> ?q\<close>] dual_order.trans length_0_conv  nemps' per_lemma_len_le[OF fw] primroot_len_le[OF nemps'(1)]
    unfolding primroot_unique[OF nemps'(1) \<open>primitive (r \<cdot> s)\<close> \<open>p = (r \<cdot> s) \<^sup>@ k\<close>]
    by blast
  from root_suf_conjug[OF \<open>primitive (r \<cdot> s)\<close> \<open>w \<le>p (r\<cdot>s)\<cdot>w\<close> \<open>w \<le>s w\<cdot>(s\<cdot>r)\<close> this]
  obtain m where "w = (r \<cdot> s) \<^sup>@ m \<cdot> r".
  from that[OF \<open>p = (r \<cdot> s) \<^sup>@ k\<close> \<open>q = (s \<cdot> r) \<^sup>@ l\<close> this \<open>primitive (r \<cdot> s)\<close>]
  show ?thesis.
qed

lemma fac_two_conjug_primroot_gcd:
  assumes facs: "w \<le>f p\<^sup>@k" "w \<le>f q\<^sup>@l" and nemps: "p \<noteq> \<epsilon>" "q \<noteq> \<epsilon>" and len: "\<^bold>|p\<^bold>| + \<^bold>|q\<^bold>| - gcd (\<^bold>|p\<^bold>|) (\<^bold>|q\<^bold>|) \<le> \<^bold>|w\<^bold>|"
  obtains r s m where "\<rho> p \<sim> r \<cdot> s" and "\<rho> q \<sim> r \<cdot> s" and "w = (r \<cdot> s)\<^sup>@m \<cdot> r" and "primitive (r\<cdot>s)"
proof -
  obtain p' where "w <p p'\<cdot>w" "p \<sim> p'" "p' \<noteq> \<epsilon>"
    using conjug_nemp_iff fac_pow_pref_conjug[OF facs(1)] nemps(1) per_rootI' by metis
  obtain q' where "w <s w\<cdot>q'" "q \<sim> q'" "q' \<noteq> \<epsilon>"
    using fac_pow_pref_conjug[reversed, OF \<open>w \<le>f q\<^sup>@l\<close>] conjug_nemp_iff  nemps(2) per_rootI'[reversed] by metis
  from per_lemma_pref_suf_gcd[OF \<open>w <p p'\<cdot>w\<close> \<open>w <s w\<cdot>q'\<close>]
  obtain r s k l m where
    "p' = (r \<cdot> s) \<^sup>@ k" and
    "q' = (s \<cdot> r) \<^sup>@ l" and
    "w = (r \<cdot> s) \<^sup>@ m \<cdot> r" and
    "primitive (r \<cdot> s)"
    using len[unfolded conjug_len[OF \<open>p \<sim> p'\<close>] conjug_len[OF \<open>q \<sim> q'\<close>]]
    by blast
  moreover have "\<rho> p' = r\<cdot>s"
    using \<open>p' = (r \<cdot> s) \<^sup>@ k\<close> \<open>primitive (r \<cdot> s)\<close> \<open>p' \<noteq> \<epsilon>\<close> primroot_unique by blast
  hence "\<rho> p \<sim> r\<cdot>s"
    using conjug_primroot[OF \<open>p \<sim> p'\<close>]
    by simp
  moreover have "\<rho> q' = s\<cdot>r"
    using \<open>q' = (s \<cdot> r) \<^sup>@ l\<close> \<open>primitive (r \<cdot> s)\<close>[unfolded conjug_prim_iff'[of r]] \<open>q' \<noteq> \<epsilon>\<close> primroot_unique by blast
  hence "\<rho> q \<sim> s\<cdot>r"
    using conjug_primroot[OF \<open>q \<sim> q'\<close>]  by simp
  hence "\<rho> q \<sim> r\<cdot>s"
    using conjug_trans[OF _ conjugI']
    by meson
  ultimately show ?thesis
    using that by blast
qed

corollary fac_two_conjug_primroot'_gcd:
   assumes facs: "u \<le>f r\<^sup>@k" "u \<le>f s\<^sup>@l" and nemps: "r \<noteq> \<epsilon>" "s \<noteq> \<epsilon>" and len: "\<^bold>|r\<^bold>| + \<^bold>|s\<^bold>| - gcd (\<^bold>|r\<^bold>|) (\<^bold>|s\<^bold>|) \<le> \<^bold>|u\<^bold>|"
   shows "\<rho> r \<sim> \<rho> s"
  using fac_two_conjug_primroot_gcd[OF assms] conjug_trans[OF _ conjug_sym[of "\<rho> s"]].

lemma fac_two_conjug_primroot''_gcd:
  assumes facs: "u \<le>f r\<^sup>@k" "u \<le>f s\<^sup>@l" and "u \<noteq> \<epsilon>" and len: "\<^bold>|r\<^bold>| + \<^bold>|s\<^bold>| - gcd (\<^bold>|r\<^bold>|) (\<^bold>|s\<^bold>|) \<le> \<^bold>|u\<^bold>|"
  shows "\<rho> r \<sim> \<rho> s"
proof -
  have nemps: "r \<noteq> \<epsilon>" "s \<noteq> \<epsilon>" using facs \<open>u \<noteq> \<epsilon>\<close> by auto
  show "conjugate (\<rho> r) (\<rho> s)" using fac_two_conjug_primroot'_gcd[OF facs nemps len].
qed

lemma  fac_two_prim_conjug_gcd:
  assumes "w \<le>f u\<^sup>@n" "w \<le>f v\<^sup>@m" "primitive u" "primitive v" "\<^bold>|u\<^bold>| + \<^bold>|v\<^bold>| - gcd (\<^bold>|u\<^bold>|) (\<^bold>|v\<^bold>|) \<le> \<^bold>|w\<^bold>|"
  shows "u \<sim> v"
  using fac_two_conjug_primroot'_gcd[OF assms(1-2) _ _ assms(5)] prim_nemp[OF \<open>primitive u\<close>] prim_nemp[OF \<open>primitive v\<close>]
  unfolding prim_self_root[OF \<open>primitive u\<close>] prim_self_root[OF \<open>primitive v\<close>].

lemma two_pers_1:
  assumes pu: "w \<le>p u \<cdot> w" and pv: "w \<le>p v \<cdot> w" and len: "\<^bold>|u\<^bold>| + \<^bold>|v\<^bold>| - 1 \<le> \<^bold>|w\<^bold>|"
  shows "u \<cdot> v = v \<cdot> u"
proof
  assume "u \<noteq> \<epsilon>" "v \<noteq> \<epsilon>"
  hence "1 \<le> gcd \<^bold>|u\<^bold>| \<^bold>|v\<^bold>|"
    using nemp_len by (simp add: Suc_leI)
  thus ?thesis
    using per_lemma_comm[OF pu pv] len by linarith
qed


end
