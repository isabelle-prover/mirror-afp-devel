(*  Title:      CoW/Periodicity_Lemma.thy
    Author:     Štěpán Holub, Charles University

Part of Combinatorics on Words Formalized. See https://gitlab.com/formalcow/combinatorics-on-words-formalized/

A version of the theory is included in the AFP. See https://www.isa-afp.org/entries/Combinatorics_Words.html
*)

theory Periodicity_Lemma
  imports CoWBasic
begin

chapter "The Periodicity Lemma"

text\<open>The Periodicity Lemma says that if a sufficiently long word has two periods p and q,
then the period can be refined to @{term "gcd p q"}.
The consequence is equivalent to the fact that the corresponding periodic roots commute.
``Sufficiently long'' here means at least @{term "p + q - gcd p q"}.
It is also known as the Fine and Wilf theorem due to its authors \cite{ FineWilf}.\<close>

text\<open>
If we relax the requirement to @{term "p + q"}, then the claim becomes easy, and it is proved in theory Combinatorics_Words.CoWBasic as @{term two_pers_root}: @{thm[names_long] two_pers_root[no_vars]}.
\<close>

theorem per_lemma_relaxed:
  assumes "period w p" and  "period w q" and  "p + q \<le> \<^bold>|w\<^bold>|"
  shows "(take p w)\<cdot>(take q w) = (take q w)\<cdot>(take p w)"
  using   two_pers_root[OF
      \<open>period w p\<close>[unfolded period_def[of w p]]
      \<open>period w q\<close>[unfolded period_def[of w q]], unfolded
      take_len[OF add_leD1[OF \<open>p + q \<le> \<^bold>|w\<^bold>|\<close>]]
      take_len[OF add_leD2[OF \<open>p + q \<le> \<^bold>|w\<^bold>|\<close>]], OF \<open>p + q \<le> \<^bold>|w\<^bold>|\<close>].

section \<open>Main claim\<close>

text\<open>We first formulate the claim of the Periodicity lemma in terms of commutation of two periodic roots.
For trivial reasons we can also drop the requirement that the roots are nonempty.

The proof is by induction which mimics the Euclidean algorithm. The step is given by the following lemma:
\<close>

lemma per_lemma_step:
  fixes u v' w' :: "'a list"
  defines "w \<equiv> u \<cdot> w'" and "v \<equiv> u \<cdot> v'"
  shows
  per_lemma_step_pers: "w \<le>p u \<cdot> w \<and> w \<le>p v \<cdot> w \<longleftrightarrow>  w' \<le>p u \<cdot> w' \<and> w' \<le>p v' \<cdot> w'"
        proof
  assume a1: "w' \<le>p u \<cdot> w' \<and> w' \<le>p v' \<cdot> w'"
  show "w \<le>p u \<cdot> w \<and> w \<le>p v \<cdot> w"
    unfolding w_def v_def
    by (rule conjI, unfold pref_cancel_conv rassoc) (use a1 pref_prolong in blast)+
next
  assume a2: "w \<le>p u \<cdot> w \<and> w \<le>p v \<cdot> w"
  hence "w' \<le>p u \<cdot> w'" "w' \<le>p v' \<cdot> w"
    unfolding w_def v_def
    by force+
  then show "w' \<le>p u \<cdot> w' \<and> w' \<le>p v' \<cdot> w'"
    unfolding w_def
    using pref_prod_pref by blast
qed

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
    thus "r \<cdot> s = s \<cdot> r"
      by fastforce
  next
    case (short)
    show "r \<cdot> s = s \<cdot> r"
    proof (rule "less.hyps"[symmetric])
      show "\<^bold>|r\<^bold>| + \<^bold>|r\<^bold>| + \<^bold>|s\<^bold>| < \<^bold>|s\<^bold>| + \<^bold>|s\<^bold>| + \<^bold>|r\<^bold>|"
        using short by simp
      show "\<^bold>|s\<^bold>| + \<^bold>|r\<^bold>| - (gcd \<^bold>|s\<^bold>| \<^bold>|r\<^bold>|) \<le> \<^bold>|w\<^bold>|"
        unfolding gcd.commute[of "\<^bold>|s\<^bold>|"] add.commute[of "\<^bold>|s\<^bold>|"] by fact
    qed fact+
   next
     case (step)
     hence  "s \<noteq> \<epsilon>" and "\<^bold>|s\<^bold>| \<le> \<^bold>|r\<^bold>|"
       by blast+

    from le_add_diff[OF gcd_le2_nat[OF \<open>s \<noteq> \<epsilon>\<close>[folded length_0_conv], of "\<^bold>|r\<^bold>|"], unfolded gcd.commute[of "\<^bold>|r\<^bold>|"], of "\<^bold>|r\<^bold>|"]
    have "\<^bold>|r\<^bold>| \<le> \<^bold>|w\<^bold>|"
      using  \<open>\<^bold>|r\<^bold>| + \<^bold>|s\<^bold>| - (gcd \<^bold>|r\<^bold>| \<^bold>|s\<^bold>|) \<le> \<^bold>|w\<^bold>|\<close>[unfolded gcd.commute[of "\<^bold>|r\<^bold>|"] add.commute[of "\<^bold>|r\<^bold>|"]] order.trans by blast
    hence "\<^bold>|s\<^bold>| \<le> \<^bold>|w\<^bold>|"
      using \<open>\<^bold>|s\<^bold>| \<le> \<^bold>|r\<^bold>|\<close> order.trans by blast
    from pref_prod_long[OF  \<open>w \<le>p s \<cdot> w\<close> this]
    have "s \<le>p r"
      using prefix_order.trans[OF _ \<open>w \<le>p r \<cdot> w\<close>] pref_prod_le  \<open>\<^bold>|s\<^bold>| \<le> \<^bold>|r\<^bold>|\<close>
      by blast
    hence r: "s \<cdot> s\<inverse>\<^sup>>r = r" and w': "s \<cdot> s\<inverse>\<^sup>>w = w"
      using \<open>s \<le>p w\<close> by simp_all

    \<comment> \<open>induction step\<close>
    from per_lemma_step[of s "s\<inverse>\<^sup>>w" "s\<inverse>\<^sup>>r", unfolded w' r]
    have new_pers:  "s\<inverse>\<^sup>>w \<le>p s\<inverse>\<^sup>>r \<cdot> s\<inverse>\<^sup>>w" "s\<inverse>\<^sup>>w \<le>p s \<cdot> s\<inverse>\<^sup>>w"
      using \<open>w \<le>p s \<cdot> w\<close> \<open>w \<le>p r \<cdot> w\<close> unfolding w' by blast+

    have ind_len: "\<^bold>|s\<inverse>\<^sup>>r\<^bold>| + \<^bold>|s\<^bold>|  - (gcd \<^bold>|s\<inverse>\<^sup>>r\<^bold>| \<^bold>|s\<^bold>|) \<le> \<^bold>|s\<inverse>\<^sup>>w\<^bold>|"
      using \<open>\<^bold>|r\<^bold>| + \<^bold>|s\<^bold>| - (gcd \<^bold>|r\<^bold>| \<^bold>|s\<^bold>|) \<le> \<^bold>|w\<^bold>|\<close>[folded lenarg[OF \<open>s \<cdot> s\<inverse>\<^sup>>w = w\<close>]]
      unfolding pref_gcd_lq[OF \<open>s \<le>p r\<close>, unfolded gcd.commute[of "\<^bold>|s\<^bold>|"]] lenmorph lq_short_len[OF \<open>s \<le>p r\<close>, unfolded add.commute[of "\<^bold>|s\<^bold>|"]] by force

    have "s \<cdot> s\<inverse>\<^sup>>r = s\<inverse>\<^sup>>r \<cdot> s"
      using "less.hyps"[OF  _ new_pers ind_len] \<open>s \<le>p r\<close>
        unfolding prefix_def
        by force

    thus "r \<cdot> s = s \<cdot> r"
      using \<open>s \<le>p r\<close> by (fastforce simp add: prefix_def)
  qed
qed

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
  obtain t k m where "take p w = t\<^sup>@k" and "take q w = t\<^sup>@m" and "t \<noteq> \<epsilon>"
    using commE[OF per_lemma_comm[OF takep takeq, unfolded lenp lenq, OF len]].
  have "w <p t \<cdot> w"
    using per_root_drop_exp[OF \<open>period w p\<close>[unfolded period_def \<open>take p w = t\<^sup>@k\<close>]].
  with per_nemp[OF \<open>period w q\<close>]
  have "period w \<^bold>|t\<^bold>|"
    by (rule periodI)
  have "\<^bold>|t\<^bold>| dvd (gcd p q)"
    using lenp[unfolded \<open>take p w = t\<^sup>@k\<close>] lenq[unfolded \<open>take q w = t\<^sup>@m\<close>] nemp_len[OF \<open>t \<noteq> \<epsilon>\<close>]
    unfolding lenmorph pow_len by force
  from dvd_div_mult_self[OF this]
  have "gcd p q div \<^bold>|t\<^bold>| * \<^bold>|t\<^bold>| = gcd p q".
  have "gcd p q \<noteq> 0"
    using \<open>period w p\<close> by auto
  from this[folded dvd_div_eq_0_iff[OF \<open>\<^bold>|t\<^bold>| dvd (gcd p q)\<close>]]
  show "period w (gcd p q)"
    using  per_mult[OF \<open>period w \<^bold>|t\<^bold>|\<close>, of "gcd p q div \<^bold>|t\<^bold>|", unfolded dvd_div_mult_self[OF \<open>\<^bold>|t\<^bold>| dvd (gcd p q)\<close>]] by blast
qed

section \<open>Optimality of the bound by construction of the Fine and Wilf word.\<close>

text\<open>\<open>FW_word\<close> (where FW stands for  Fine and Wilf) yields a word which shows the optimality of the bound in the Periodicity lemma.\<close>

definition "fw_per k d \<equiv> [0..<d]\<^sup>@k \<cdot> [0..<(d-1)]"
definition "fw_base k d \<equiv> fw_per k d \<cdot> [d] \<cdot> fw_per k d"

fun FW_word :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  FW_word_def: "FW_word p q =
\<comment>\<open>symmetry\<close>           (if q < p then  FW_word q p else
\<comment>\<open>artificial value\<close>   if p = 0 then \<epsilon> else
\<comment>\<open>artificial value\<close>   if p dvd q then \<epsilon> else
\<comment>\<open>base case\<close>          if gcd p q = q - p then fw_base (p div (gcd p q) -1) (gcd p q)
\<comment>\<open>step\<close>               else (take p (FW_word p (q-p))) \<cdot> FW_word p (q-p))"

lemma FW_sym: "FW_word p q = FW_word q p"
  by (cases rule: linorder_cases[of p q]) simp+

lemma FW_dvd: assumes "p dvd q" shows "FW_word p q = \<epsilon>"
proof (cases "q = 0", use FW_word_def[of p q] in force)
  assume "q \<noteq> 0"
  hence "\<not> q < p"
    using assms by auto
  thus ?thesis
    using FW_word_def \<open>p dvd q\<close> by auto
qed

lemma upt_minus_pref: "[i..< j-d] \<le>p [i..< j]"
  by (rule le_cases[of j d], force)
  (use upt_add_eq_append[of i "j-d" d] in fastforce)

lemma fw_per_pref: "fw_per k d \<le>p take d (fw_per k d) \<cdot> (fw_per k d)"
proof-
  consider "k = 0 \<or> d = 0" | "0 < k \<and> 0 < d"
    by fastforce
  thus ?thesis
  proof(cases)
    assume "k = 0 \<or> d = 0"
    then show ?thesis
      unfolding fw_per_def by fastforce
  next
    assume "0 < k \<and> 0 < d"
    hence "0 < k" "0 < d"
      by blast+
    hence nemp: "[0..<d] \<^sup>@ k \<noteq> \<epsilon>"
      using emp_pow_pos_emp[OF _ \<open>0 < k\<close>, of "[0..<d]"]
      unfolding upt_eq_Nil_conv[of 0 d] by blast
    have t: "take d (fw_per k d) = [0..<d]"
      unfolding fw_per_def pow_pos[OF \<open>0 < k\<close>]
        butlast_append if_not_P[OF nemp] by auto
    show ?thesis
      unfolding t unfolding fw_per_def
      unfolding lassoc pow_comm[symmetric]
      unfolding rassoc pref_cancel_conv
      using upt_minus_pref by simp
  qed
qed

lemma fw_per_len: shows "\<^bold>|fw_per k d\<^bold>| = (k+1)*d - 1"
 unfolding fw_per_def lenmorph pow_len
  by (cases "d = 0") fastforce+

lemma fw_base_len: assumes "0 < d" shows "\<^bold>|fw_base k d\<^bold>| = (k+1)*d + (k+1)*d - 1"
  unfolding fw_base_def lenmorph fw_per_len sing_len using assms by simp

lemma fw_base_per1: assumes "0 < d"
  shows "period (fw_base k d) ((k+1)*d)"
proof-
  have take: "take ((k+1)*d) (fw_base k d) = fw_per k d \<cdot> [d]"
    unfolding fw_base_def lassoc using fw_per_len \<open>0 < d\<close> by force
  show "period (fw_base k d) ((k+1)*d)"
    unfolding period_def take unfolding fw_base_def by force
qed

lemma fw_base_per2: assumes "0 < d"
  shows "period (fw_base k d) ((k+1)*d + d)"
  unfolding period_def
proof (rule per_rootI)
  show "take ((k+1)*d + d) (fw_base k d) \<noteq> \<epsilon>"
    using \<open>0 < d\<close> unfolding fw_base_def by simp
  have t1: "take ((k+1)*d) (fw_base k d) = fw_per k d \<cdot> [d]"
    unfolding fw_base_def lassoc using fw_per_len \<open>0 < d\<close> by force
  have "\<^bold>|fw_per k d \<cdot> [d]\<^bold>| = (k+1)*d"
    using fw_per_len unfolding lenmorph sing_len using \<open>0 < d\<close> by simp
  hence d: "drop ((k+1)*d) (fw_per k d \<cdot> [d] \<cdot> fw_per k d) = fw_per k d"
    unfolding lassoc using drop_pref by metis
  show "fw_base k d \<le>p take (((k+1)*d) + d) (fw_base k d) \<cdot> fw_base k d"
    unfolding take_add t1 unfolding fw_base_def rassoc pref_cancel_conv d
    using fw_per_pref pref_prolong triv_pref by meson
qed

lemma fw_base_not_per: assumes "0 < d" "0 < k"
  shows "\<not> period (fw_base k d) d" (is "\<not> period ?w d")
proof
  have u: "take d ?w = [0..< d]"
    unfolding fw_base_def fw_per_def pow_pos[OF \<open>0 < k\<close>] by force
  have suc: "[0..<d] = [0..<d-1]\<cdot>[d-1]"
    using \<open>0 < d\<close> upt_Suc_append[of 0 "d-1"] by fastforce
  assume "period ?w d"
  hence "?w \<le>p [0..< d] \<cdot> ?w"
    unfolding period_def u[symmetric] by blast
  hence "fw_per k d \<cdot> [d] \<le>p [0..< d] \<cdot> fw_per k d \<cdot> [d]"
    unfolding fw_base_def lassoc
    using  pref_cancel_right by blast
  hence " [0..<d-1] \<cdot> [d] \<le>p [0..<d] \<cdot> [0..<d-1] \<cdot> [d]"
    unfolding u fw_per_def pow_pos[OF \<open>0 < k\<close>]
    unfolding lassoc pow_comm[symmetric] by fastforce
  from pref_prod_eq[OF this]
  have eq: "[0..<d-1] \<cdot> [d] = [0..<d]"
    using \<open>0 < d\<close> by simp
  thus False
    using \<open>0 < d\<close> unfolding suc cancel by fastforce
qed

lemma per_mod: "period w n \<Longrightarrow> i < \<^bold>|w\<^bold>| \<Longrightarrow> w!i = w!(i mod n)"
proof (induct i rule: less_induct)
  case (less i)
  then show ?case
  proof (cases "i < n", unfold mod_less[of i n], blast)
    assume "\<not> i < n"
    with per_not_zero[OF \<open>period w n\<close>]
    have "i - n + n = i" "i - n < i" "i - n < \<^bold>|w\<^bold>|" "(i - n) mod n = i mod n"
      using \<open>i < \<^bold>|w\<^bold>|\<close> mod_add_self2[of "i-n" n] by force+
    from less.hyps[OF \<open>i - n < i\<close> \<open>period w n\<close> \<open>i - n < \<^bold>|w\<^bold>|\<close>]
    show "w ! i = w ! (i mod n)"
      unfolding period_indeces[OF \<open>period w n\<close>, of "i-n", unfolded \<open>i - n + n = i\<close>, OF \<open>i < \<^bold>|w\<^bold>|\<close>] \<open>(i - n) mod n = i mod n\<close>.
  qed
qed

lemma fw_per_per: assumes "fw_per k d \<noteq> \<epsilon>"
  shows "period (fw_per k d) d"
  unfolding period_def
proof (rule per_rootI[OF fw_per_pref])
  show "take d (fw_per k d) \<noteq> \<epsilon>"
  using assms unfolding take_eq_Nil fw_per_def by fastforce
qed

lemma fw_per_nth: assumes "i < \<^bold>|fw_per k d\<^bold>|"
  shows "(fw_per k d)!i = i mod d"
proof (cases "k = 0")
  assume "k = 0"
  then show ?thesis
  using assms unfolding fw_per_def by force
next
  assume "k \<noteq> 0"
  hence "0 < k"
    by blast
  have "fw_per k d \<noteq> \<epsilon>"
    using assms by fastforce
  hence "0 < d"
    unfolding fw_per_def by force
  from per_mod[OF fw_per_per[OF \<open>fw_per k d \<noteq> \<epsilon>\<close>] assms]
  have mod: "fw_per k d ! i = fw_per k d ! (i mod d)".
  show ?thesis
    using assms nth_upt[of 0 "i mod d" d, unfolded add_0] mod_less_divisor[OF \<open>0 < d\<close>]
    unfolding mod
    unfolding fw_per_def pow_pos[OF \<open>0 < k\<close>] rassoc
    using length_upt[of 0 d, unfolded diff_zero] unfolding nth_append by presburger
qed

lemma fw_base_nth: assumes "i < \<^bold>|fw_base k d\<^bold>|"
  shows "(fw_base k d)!i = (if i = \<^bold>|fw_per k d\<^bold>| then d else i mod d)"
proof-
  note formula = nth_append[of "fw_per k d \<cdot> [d]" "fw_per k d" i, unfolded rassoc, folded fw_base_def]
  show ?thesis
  proof (rule linorder_cases[of i " \<^bold>|fw_per k d\<^bold>|"])
    assume "i = \<^bold>|fw_per k d\<^bold>|"
    hence  "i < \<^bold>|fw_per k d \<cdot> [d]\<^bold>|"
      by auto
    show ?thesis
      unfolding if_P[OF \<open>i = \<^bold>|fw_per k d\<^bold>|\<close>] formula if_P[OF \<open>i < \<^bold>|fw_per k d \<cdot> [d]\<^bold>|\<close>]
      unfolding \<open>i = \<^bold>|fw_per k d\<^bold>|\<close> by simp
  next
    assume "i < \<^bold>|fw_per k d\<^bold>|"
    hence  "i < \<^bold>|fw_per k d \<cdot> [d]\<^bold>|" "i \<noteq> \<^bold>|fw_per k d\<^bold>|"
      by auto
    show ?thesis
      unfolding formula if_not_P[OF \<open>i \<noteq> \<^bold>|fw_per k d\<^bold>|\<close>] if_P[OF \<open>i < \<^bold>|fw_per k d \<cdot> [d]\<^bold>|\<close>]
      using nth_append[of "fw_per k d" "[d]" i]
      unfolding if_P[OF \<open>i < \<^bold>|fw_per k d\<^bold>|\<close>] fw_per_nth[OF \<open>i < \<^bold>|fw_per k d\<^bold>|\<close>].
  next
    assume "\<^bold>|fw_per k d\<^bold>| < i"
    hence  "\<not> i < \<^bold>|fw_per k d \<cdot> [d]\<^bold>|" "i \<noteq> \<^bold>|fw_per k d\<^bold>|" "\<^bold>|fw_per k d \<cdot> [d]\<^bold>| \<le> i"
      by auto
    have diff_less: "i - \<^bold>|fw_per k d \<cdot> [d]\<^bold>| < \<^bold>|fw_per k d\<^bold>|"
      using diff_less_mono[OF assms \<open>\<^bold>|fw_per k d \<cdot> [d]\<^bold>| \<le> i\<close>]
      unfolding fw_base_def by force
    have "d \<noteq> 0"
    proof
      assume "d = 0"
      show False
        using assms \<open>\<^bold>|fw_per k d\<^bold>| < i\<close> unfolding fw_base_def fw_per_def pow_len lenmorph
          sing_len \<open>d = 0\<close> by force
    qed
    hence "(k + 1) * d - 1 + 1 = (k+1)*d"
      by simp
    have "(k+1)*d \<le> i"
      using \<open>\<^bold>|fw_per k d\<^bold>| < i\<close> unfolding fw_per_len by force
    show ?thesis
      unfolding formula if_not_P[OF \<open>i \<noteq> \<^bold>|fw_per k d\<^bold>|\<close>] if_not_P[OF \<open>\<not> i < \<^bold>|fw_per k d \<cdot> [d]\<^bold>|\<close>]
      fw_per_nth[OF diff_less]
      unfolding lenmorph fw_per_len sing_len \<open>(k + 1) * d - 1 + 1 = (k+1)*d\<close>
      using mod_mult_self3[of "k+1" d "i - (k + 1) * d"]
      unfolding le_add_diff_inverse[OF \<open>(k+1)*d \<le> i\<close>] by force
  qed
qed

lemma fw_base_match: assumes "i < \<^bold>|fw_base k d\<^bold>|" "j < \<^bold>|fw_base k d\<^bold>|" "i \<noteq> j" and
     eq:  "(fw_base k d)!i = (fw_base k d)!j"
    shows "i mod d = j mod d" and "i \<noteq> \<^bold>|fw_per k d\<^bold>|" and "j \<noteq> \<^bold>|fw_per k d\<^bold>|"
proof (atomize (full), cases)
  assume "d = 0"
  hence "fw_base k d = [0]"
    unfolding fw_base_def fw_per_def by simp
  have "i = j"
    using assms(1-3) unfolding \<open>fw_base k d = [0]\<close> sing_len by blast
  thus "i mod d = j mod d \<and> i \<noteq> \<^bold>|fw_per k d\<^bold>| \<and> j \<noteq> \<^bold>|fw_per k d\<^bold>|"
    using \<open>i \<noteq> j\<close> by blast
next
  assume "d \<noteq> 0"
  hence "i mod d \<noteq> d" for i
    using mod_less_divisor[of d i] by force
  with eq[unfolded fw_base_nth[OF \<open>i < \<^bold>|fw_base k d\<^bold>|\<close>] fw_base_nth[OF \<open>j < \<^bold>|fw_base k d\<^bold>|\<close>]]
  show "i mod d = j mod d \<and> i \<noteq> \<^bold>|fw_per k d\<^bold>| \<and> j \<noteq> \<^bold>|fw_per k d\<^bold>|"
    using \<open>i \<noteq> j\<close> by metis
qed

\<comment> \<open>A numeric formulation of the induction step\<close>
lemma ext_per_sum: assumes "period w p" and "period w q" and  "p \<le> \<^bold>|w\<^bold>|"
  shows "period ((take p w) \<cdot> w) (p+q)"
proof-
  have sum: "take (p + q) (take p w \<cdot> w) = take p w \<cdot> take q w"
    unfolding take_add  by (simp add: \<open>p \<le> \<^bold>|w\<^bold>|\<close>)
  show ?thesis
    unfolding period_def sum rassoc
    using pref_spref_prolong[OF self_pref spref_spref_prolong[OF assms(2,1)[unfolded period_def]]].
qed

lemma drop_per_diff: assumes "period w p" and "period w q" and "p < q" and "p < \<^bold>|w\<^bold>|"
  shows "period (drop p w) (q-p)"
proof-
  have nemp: "take (q - p) (drop p w) \<noteq> \<epsilon>"
    using \<open>p < \<^bold>|w\<^bold>|\<close> \<open>p < q\<close>  by force
  have t1: "take p w \<cdot> drop p (take q w) = take q w"
    unfolding drop_take take_add[symmetric] using \<open>p < q\<close> by simp
  from per_lemma_step[of "take p w" "drop p w" "drop p (take q w)",
       unfolded  append_take_drop_id t1,
       unfolded drop_take]
  have "drop p w \<le>p take (q - p) (drop p w) \<cdot> drop p w"
    using assms unfolding period_def using sprefD1 by blast
  hence "drop p w <p take (q - p) (drop p w) \<cdot> drop p w"
    using nemp by blast
  thus ?thesis
    unfolding period_def.
qed

theorem fw_word: assumes "\<not> p dvd q" "\<not> q dvd p"
  shows "\<^bold>|FW_word p q\<^bold>| = p + q - gcd p q - 1"
        "period (FW_word p q) p" and  "period (FW_word p q) q"
        "\<not> period (FW_word p q) (gcd p q)"
  using assms
proof (atomize (full),  induction "p + p + q" arbitrary: p q rule: less_induct)
  case less
  have "p \<noteq> 0"
    using  \<open>\<not> q dvd p\<close> dvd_0_right[of q] by meson
  hence "0 < p"
    by simp
  have "p \<noteq> q"
    using \<open>\<not> p dvd q\<close> by auto
  then consider "q < p" | "p < q"
    by linarith
  then show ?case
  proof (cases)
    assume "q < p"
    hence "q + q + p < p + p + q"
      by simp
    from  "less.hyps"[OF this \<open>\<not> q dvd p\<close> \<open>\<not> p dvd q\<close>]
    show ?case
      unfolding FW_sym[of p q] gcd.commute[of p q] add.commute[of p q] by blast
  next
    assume "p < q"
    \<comment> \<open>auxiliary\<close>
    hence "\<not> q < p" "p + (q - p) = q" "p \<ge> gcd p q" "q - p \<ge> 1" "q -p \<noteq> 0"
      using \<open>p \<noteq> 0\<close> \<open>p < q\<close> by auto
    have "q - p \<ge> gcd p q"
      using \<open>p < q\<close> \<open>p + (q - p) = q\<close> \<open>q -p \<noteq> 0\<close> gcd_add2 gcd_le2_nat by metis
    hence "q \<ge> gcd p q + 1"
      using \<open>0 < p\<close> \<open>p + (q - p) = q\<close> \<open>p \<ge> gcd p q\<close> \<open>q - p \<ge> 1\<close> by linarith

    let ?w = "FW_word p q"
    let ?d = "gcd p q"
    let ?k = "p div gcd p q - 1"
    let ?dw = "[0..<(gcd p q)]"
    let ?pd = "p div (gcd p q)"
    show ?thesis
    proof (cases "?d = q - p")
      assume "?d = q - p"
      hence "p + ?d = q" "p + q - ?d = p + p" "0 < ?d" "?d \<noteq> q" "?d < q" "1 \<le> q - ?d"
        using \<open>p \<noteq> 0\<close> \<open>p < q\<close> by auto
      have "?d \<noteq> p"
        using \<open>\<not> p dvd q\<close>  \<open>gcd p q = q - p\<close> gcd_unique_nat by metis
      have kdp: "(?k + 1) * ?d = p"
        by (metis \<open>p \<noteq> 0\<close> add.commute dvd_mult_div_cancel gcd_dvd1 less_one linordered_semidom_class.add_diff_inverse mult.commute mult_zero_right)
      hence "0 < ?k"
        using \<open>?d \<noteq> p\<close> add_0[of 1] mult_1 not_gr_zero by metis
      let ?per  = "fw_per ?k ?d"
      have fw_base: "?w = fw_base ?k ?d"
        unfolding FW_word_def[of p q] if_not_P[OF \<open>\<not> q < p\<close>] if_not_P[OF \<open>p \<noteq> 0\<close>]
          if_not_P[OF \<open>p \<noteq> q\<close>] if_P[OF \<open>?d = q - p\<close>] using less.prems(1) by argo
      hence fw: "?w = ?per\<cdot>[?d]\<cdot>?per"
        unfolding fw_base_def.
      show "(\<^bold>|?w\<^bold>| = p + q - ?d - 1 \<and>
          period ?w p) \<and> period ?w q \<and>
          \<not> period ?w ?d"
        unfolding conj_assoc[symmetric]
      proof (rule conjI)+
        show "\<^bold>|?w\<^bold>| = p + q - ?d - 1"
          unfolding fw_base fw_base_len[OF \<open>0 < ?d\<close>]
            \<open>p + q - ?d = p + p\<close> kdp..
        show "period ?w p"
          unfolding fw_base using fw_base_per1[OF \<open>0 < ?d\<close>, of ?k, unfolded kdp].
        show "period ?w q"
          unfolding fw_base using
          fw_base_per2[OF \<open>0 < ?d\<close>, of ?k, unfolded kdp \<open>p + gcd p q = q\<close>].
        show "\<not> period ?w ?d"
          using fw_base_not_per[OF \<open>0 < ?d\<close> \<open>0 < ?k\<close>] unfolding fw_base.
      qed
    next
      assume "gcd p q \<noteq> q - p"
      hence "q - p > gcd p q"
         using \<open>q - p \<ge> gcd p q\<close> by force
      let ?w' = "FW_word p (q-p)"
      have "gcd p (q-p) = ?d"
        using  gcd_add2[of p "q-p", unfolded le_add_diff_inverse[OF less_imp_le[OF \<open>p < q\<close>]], symmetric].
      have fw: "?w = take p ?w' \<cdot> ?w'"
        using FW_word_def \<open>p \<noteq> 0\<close> \<open>p \<noteq> q\<close> \<open>p < q\<close> \<open>gcd p q \<noteq> q - p\<close>
        \<open>\<not> q < p\<close> \<open>\<not> p dvd q\<close> by meson
      show "(\<^bold>|?w\<^bold>| = p + q - ?d - 1 \<and>
          period ?w p) \<and> period ?w q \<and>
          \<not> period ?w ?d"
        unfolding conj_assoc[symmetric]
      proof (rule conjI)+

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
        have len_w': "\<^bold>|?w'\<^bold>| = p + (q - p) - ?d - 1" and "period ?w' p" and "period ?w' (q-p)" and
          "\<not> period ?w' (gcd p (q-p))"
          using "less.hyps"[OF _ divhyp1 divhyp2] lenhyp
          unfolding \<open>gcd p (q-p) = ?d\<close> by blast+

        have "p \<le> \<^bold>|?w'\<^bold>|"
          unfolding  len_w' using \<open>q - p > gcd p q\<close> by force
        have "?w' \<noteq> \<epsilon>"
          using period_nemp[OF \<open>period ?w' p\<close>].

        show "\<not> period ?w ?d"
          using \<open>\<not> period (FW_word p (q -p)) (gcd p (q-p))\<close>
          unfolding \<open>gcd p (q-p) = ?d\<close>
          using period_fac[of "take p ?w'" "?w'" \<epsilon> "?d", unfolded append_Nil2,
              OF _ \<open>?w' \<noteq> \<epsilon>\<close>, folded fw] by blast

        show "\<^bold>|?w\<^bold>| = p + q - ?d - 1"
          unfolding fw lenmorph len_w' take_len[OF \<open>p \<le> \<^bold>|?w'\<^bold>|\<close>] \<open>p + (q - p) = q\<close>
          using \<open>q \<ge> gcd p q + 1\<close> by simp

        show "period ?w p"
          using fw  ext_per_left[OF \<open>period (FW_word p (q-p)) p\<close> \<open>p \<le> \<^bold>|?w'\<^bold>|\<close>]
          by presburger

        show "period ?w q"
          using ext_per_sum[OF \<open>period ?w' p\<close> \<open>period ?w' (q - p)\<close> \<open>p \<le> \<^bold>|?w'\<^bold>|\<close>, folded fw, unfolded \<open>p + (q-p) = q\<close>].

      qed
    qed
  qed
qed


text\<open>Calculation examples\<close>

value "FW_word 3 4"
value "FW_word 4 7"
value "FW_word 3 7"
value "FW_word 5 7"
value "FW_word 5 13"
value "FW_word 4 6"
value "FW_word 12 18"

section \<open>Optimality of the Fine and Wilf word.\<close>

text\<open>The \<open>FW_word\<close> is the most general word having the two desired properties. That is,
each equality of letters is forced by periods.\<close>

lemma fw_base_mod_aux: assumes "(i :: nat) < p + p - 1" "i \<noteq> p - 1"
  shows "i mod p < p - 1"
proof (cases p i rule: le_less_cases)
  assume "p \<le> i"
  have "i - p < p" "i - p < p - 1"
    using diff_less_mono[OF \<open>i < p + p - 1\<close> \<open>p \<le> i\<close>] unfolding diff_cancel2 diff_diff_eq by simp_all
  from le_mod_geq[OF \<open>p \<le> i\<close>]
  have "i mod p = i - p"
    unfolding mod_less[OF \<open>i - p < p\<close>].
  thus ?thesis
    using \<open>i - p < p - 1\<close> by argo
next
  assume "i < p"
  show ?thesis
    unfolding mod_less[OF \<open>i < p\<close>]
    using \<open>i < p\<close> \<open>i \<noteq> p - 1\<close> by linarith
qed

theorem fw_minimal: assumes "period w p" and "period w q" and "\<^bold>|w\<^bold>| = \<^bold>|FW_word p q\<^bold>|" and
       "i < \<^bold>|w\<^bold>|" and "j < \<^bold>|w\<^bold>|" and "(FW_word p q)!i = (FW_word p q)!j"
    shows "w!i = w!j"
  using assms
proof (induct "p + p + q" arbitrary: w i j p q rule: less_induct)
  case less
  \<comment> \<open>preliminaries\<close>
  have "FW_word p q \<noteq> \<epsilon>"
    using \<open>j < \<^bold>|w\<^bold>|\<close>  \<open>\<^bold>|w\<^bold>| = \<^bold>|FW_word p q\<^bold>|\<close> emp_len[of "FW_word p q"] by linarith+
  hence "\<not> p dvd q" "0 < p"
    using FW_dvd per_not_zero[OF less.prems(1)] by blast+
  hence "1 < p"
    using less_one nat_neq_iff one_dvd by metis
  have "\<not> q dvd p"
    using FW_dvd \<open>FW_word p q \<noteq> \<epsilon>\<close>[unfolded FW_sym[of p]] by blast
  note fw_word[OF \<open>\<not> p dvd q\<close> \<open>\<not> q dvd p\<close>]
  have w_len: "\<^bold>|w\<^bold>| = p + q - gcd p q - 1"
    using fw_word(1)[OF \<open>\<not> p dvd q\<close> \<open>\<not> q dvd p\<close> ] unfolding \<open>\<^bold>|w\<^bold>| = \<^bold>|FW_word p q\<^bold>|\<close>.

  show "w ! i = w ! j"
  proof (cases "i = j", blast)
    assume "i \<noteq> j"
    show "w ! i = w ! j"
    proof (cases "q < p")
      assume "q < p"
      then show "w ! i = w ! j"
        using less.hyps[OF _  less.prems(2,1) less.prems(3-6)[unfolded FW_sym[of p]]] by simp
    next
      assume "\<not> q < p"
      hence "p < q"
        using \<open>\<not> p dvd q\<close> linorder_neqE_nat by fastforce+
      show "w ! i = w ! j"
      proof (cases "gcd p q = q - p")
        assume "gcd p q = q - p"
        hence base: "FW_word p q = fw_base (p div (gcd p q) - 1) (gcd p q)" \<comment> \<open>This is the base case.\<close>
          using FW_word_def[of p q] \<open>\<not> q < p\<close> \<open>0 < p\<close> \<open>\<not> p dvd q\<close>  by presburger
        let ?d = "gcd p q"
        let ?pref = "take (p-1) w"
        let ?FW = "FW_word p q"


        \<comment> \<open>Auxiliary facts\<close>
        from \<open>0 < p\<close> dvd_div_eq_0_iff[OF gcd_nat.cobounded1, of p q]
        have per_len: "\<^bold>|fw_per (p div ?d - 1) ?d\<^bold>| = p - 1"
          unfolding fw_per_len
          using dvd_mult_div_cancel[OF gcd_nat.cobounded1, of p q, unfolded mult.commute[of "?d"]] by force
        have w_len': "\<^bold>|w\<^bold>| = p + p - 1"
          unfolding w_len \<open>?d = q - p\<close> using \<open>p < q\<close> by auto
        hence "p < \<^bold>|w\<^bold>|" "p - 1 \<le> \<^bold>|w\<^bold>|"
          using \<open>1 < p\<close> by simp_all
        have "i mod p mod ?d = i mod ?d"
          using  mod_mod_cancel[OF gcd_nat.cobounded1].
        have ij_less: "i < \<^bold>|?FW\<^bold>|" "j < \<^bold>|?FW\<^bold>|"
          using \<open>i < \<^bold>|w\<^bold>|\<close> \<open>j < \<^bold>|w\<^bold>|\<close> unfolding \<open>\<^bold>|w\<^bold>| = \<^bold>|?FW\<^bold>|\<close> by force+
        have "\<^bold>|?pref\<^bold>| = p - 1"
          using \<open>p - 1 \<le> \<^bold>|w\<^bold>|\<close> by simp

        \<comment> \<open>Indeces which agree on FW are as follows:\<close>
        have mod_d_eq: "i mod ?d = j mod ?d" and not_max: "i \<noteq> p-1" "j \<noteq> p-1"
          using fw_base_match[OF ij_less[unfolded base] \<open>i \<noteq> j\<close> \<open>?FW ! i = ?FW ! j\<close>[unfolded base]]
                 unfolding per_len  by blast+
        have "i mod p < p - 1" "j mod p < p - 1"   \<comment> \<open>Key fact: taking modulo p, we avoid the non-periodic element [d]\<close>
          using fw_base_mod_aux \<open>i < \<^bold>|w\<^bold>|\<close> \<open>j < \<^bold>|w\<^bold>|\<close> not_max unfolding \<open>\<^bold>|w\<^bold>| = p + p - 1\<close> by blast+
        have  "period ?pref ?d" \<comment> \<open>The prefix of w has a short period: the standard reduction step\<close>
        proof-
          have "drop p w = ?pref"
          proof-
            have "drop p w \<le>p w"
              using \<open>period w p\<close> unfolding per_shift by blast
            moreover have "\<^bold>|drop p w\<^bold>| = p - 1"
              using \<open>\<^bold>|w\<^bold>| = p + p - 1\<close> unfolding length_drop by force
            ultimately show ?thesis
              using pref_take_conv by metis
          qed
          show ?thesis
            using drop_per_diff[OF \<open>period w p\<close> \<open>period w q\<close> \<open>p < q\<close> \<open>p < \<^bold>|w\<^bold>|\<close>]
            unfolding \<open>drop p w = ?pref\<close> \<open>?d = q - p\<close>.
        qed

        \<comment> \<open>Therefore letters can be mapped to the first period.\<close>
        have mod_pref_reduce: "?pref ! (i mod p) = ?pref ! (i mod ?d)" "?pref ! (j mod p) = ?pref ! (j mod ?d)"
          using per_mod[OF \<open>period ?pref ?d\<close>, unfolded \<open>\<^bold>|?pref\<^bold>| = p - 1\<close>, OF \<open>i mod p < p-1\<close>, unfolded mod_mod_cancel[OF gcd_nat.cobounded1]]
          per_mod[OF \<open>period ?pref ?d\<close>, unfolded \<open>\<^bold>|?pref\<^bold>| = p - 1\<close>, OF \<open>j mod p < p-1\<close>, unfolded mod_mod_cancel[OF gcd_nat.cobounded1]].


        have "?pref ! (i mod p) = ?pref ! (j mod p)" \<comment> \<open>Hence they are the same, because the indeces coincide modulo d\<close>
          unfolding mod_pref_reduce mod_d_eq..
        thus "w ! i = w ! j"
          unfolding nth_take[OF \<open>i mod p < p-1\<close>, of w] nth_take[OF \<open>j mod p < p-1\<close>, of w] \<comment> \<open>Since w has period p, equality for the prefix is equality for the whole word\<close>
          unfolding per_mod[OF \<open>period w p\<close> \<open>i < \<^bold>|w\<^bold>|\<close>] per_mod[OF \<open>period w p\<close> \<open>j < \<^bold>|w\<^bold>|\<close>].  \<comment> \<open>Equality in the whole word can be tested modulo p\<close>
      next
        assume "gcd p q \<noteq> q - p" \<comment> \<open>Non-base case\<close>
        hence step: "FW_word p q = take p (FW_word p (q-p)) \<cdot> FW_word p (q-p)"
          unfolding FW_word_def[of p q] using \<open>\<not> q < p\<close> \<open>0 < p\<close> \<open>\<not> p dvd q\<close> by presburger

        have "\<not> p dvd (q-p)"
          unfolding dvd_minus_self using \<open>\<not> q < p\<close> \<open>\<not> p dvd q\<close> by blast
        have "\<not> (q-p) dvd p"
          using FW_dvd[of "q-p" p] FW_dvd[of "q-p" p, THEN Nil_take_Nil]
          \<open>FW_word p q \<noteq> \<epsilon>\<close> unfolding step[unfolded FW_sym[of _ "q-p"]] by blast
        have "gcd p (q - p) < (q - p)"
          using  \<open>\<not> q - p dvd p\<close>[unfolded gcd_nat.absorb_iff2[of "q-p" p]]
          nat_dvd_not_less[OF \<open>p < q\<close>[folded zero_less_diff[of q]], of "gcd p (q-p)"] by fastforce
        hence "p \<le> \<^bold>|FW_word p (q - p)\<^bold>|"
          unfolding fw_word(1)[OF \<open>\<not> p dvd (q-p)\<close> \<open>\<not> (q-p) dvd p\<close>] by linarith
        from drop_take_inv[OF this]
        have fw': "FW_word p (q -p) = drop p (FW_word p q)"
          using step by metis
        have "p \<le> \<^bold>|drop p w\<^bold>|"
          using \<open>p \<le> \<^bold>|FW_word p (q - p)\<^bold>|\<close> less.prems(3) unfolding fw' length_drop by argo
        hence "p < \<^bold>|w\<^bold>|"
          using \<open>0 < p\<close> by fastforce

        have "FW_word p (q - p) <p FW_word p q"
          using \<open>period (FW_word p q) p\<close> unfolding per_shift fw'.
        from sprefD1[OF this]
        have "FW_word p (q - p) ! (i mod p) = FW_word p q ! (i mod p)" "FW_word p (q - p) ! (j mod p) = FW_word p q ! (j mod p)"
          using  pref_index[OF \<open>FW_word p (q - p) \<le>p FW_word p q\<close>] less_le_trans[OF  mod_less_divisor[OF \<open>0 < p\<close>] \<open>p \<le> \<^bold>|FW_word p (q-p)\<^bold>|\<close>]
          by blast+
        with per_mod[OF \<open>period (FW_word p q) p\<close> \<open>j < \<^bold>|w\<^bold>|\<close>[unfolded \<open>\<^bold>|w\<^bold>| = \<^bold>|FW_word p q\<^bold>|\<close>]]
             per_mod[OF \<open>period (FW_word p q) p\<close> \<open>i < \<^bold>|w\<^bold>|\<close>[unfolded \<open>\<^bold>|w\<^bold>| = \<^bold>|FW_word p q\<^bold>|\<close>]]
        have reduce_fw: "FW_word p (q - p) ! (j mod p) = (FW_word p q) ! j" "FW_word p (q - p) ! (i mod p) = (FW_word p q) ! i"
          by argo+

        have "drop p w <p w"
          using \<open>period w p\<close> unfolding per_shift.
        from sprefD1[OF this]
        have "drop p w ! (i mod p) = w ! (i mod p)" "drop p w ! (j mod p) = w ! (j mod p)"
          using  pref_index[OF \<open>drop p w \<le>p w\<close>] less_le_trans[OF  mod_less_divisor[OF \<open>0 < p\<close>] \<open>p \<le> \<^bold>|drop p w\<^bold>|\<close>]
          by blast+
        with per_mod[OF \<open>period w p\<close> \<open>j < \<^bold>|w\<^bold>|\<close>] per_mod[OF \<open>period w p\<close> \<open>i < \<^bold>|w\<^bold>|\<close>]
        have reduce_w: "w ! j = drop p w ! (j mod p)" "w ! i = drop p w ! (i mod p)"
          by argo+

        show "w ! i = w ! j"
          unfolding reduce_w
        proof(rule less.hyps[of p "q-p" "drop p w" "i mod p" "j mod p"])
          show " p + p + (q - p) < p + p + q"
            using \<open>p < q\<close> \<open>0 < p\<close> by linarith
          show "period (drop p w) p"
            using   period_drop[OF \<open>period w p\<close> \<open>p < \<^bold>|w\<^bold>|\<close>].
          show "period (drop p w) (q - p)"
            using  drop_per_diff[OF \<open>period w p\<close> \<open>period w q\<close> \<open>p < q\<close> \<open>p < \<^bold>|w\<^bold>|\<close>].
          show "\<^bold>|drop p w\<^bold>| = \<^bold>|FW_word p (q - p)\<^bold>|"
            using fw' length_drop \<open>\<^bold>|w\<^bold>| = \<^bold>|FW_word p q\<^bold>|\<close> by metis
          show "i mod p < \<^bold>|drop p w\<^bold>|" "j mod p < \<^bold>|drop p w\<^bold>|"
            using less_le_trans[OF mod_less_divisor[OF \<open>0 < p\<close>] \<open>p \<le> \<^bold>|drop p w\<^bold>|\<close>] by blast+
          show "FW_word p (q - p) ! (i mod p) = FW_word p (q - p) ! (j mod p)"
            unfolding reduce_fw by fact
        qed
      qed
    qed
  qed
qed

theorem fw_minimal_set: assumes "period w p" and "period w q" and "\<^bold>|w\<^bold>| = \<^bold>|FW_word p q\<^bold>|"
  shows "card(set w) \<le> card(set (FW_word p q))"
proof-
  let ?f = "\<lambda> n. (w ! (LEAST k.((FW_word p q)!k = n)))"
  have map_f0: "?f ((FW_word p q)!i) = w!i" if "i < \<^bold>|w\<^bold>|" for i
    using fw_minimal[OF assms _ that LeastI[of "\<lambda> k.(FW_word p q ! k = FW_word p q ! i)", OF refl]]
    Least_le[of "\<lambda> k.(FW_word p q ! k = FW_word p q ! i)", OF refl] that by linarith
  have map_f: "map ?f (FW_word p q) = w"
    by (rule nth_equalityI, unfold length_map, simp add: assms(3))
    (use  nth_map[of _ "FW_word p q" ?f] map_f0 assms(3) in presburger)
  then have "set w = ?f ` (set (FW_word p q))"
    using  set_map[of ?f "FW_word p q"] by presburger
  then show ?thesis
    using  card_image_le[of "set (FW_word p q)" ?f, OF finite_set] fw_minimal[OF assms]  by presburger
qed


section "Other variants of the periodicity lemma"

text \<open>Periodicity lemma is one of the most frequent tools in Combinatorics on words.
   Here are some useful variants.\<close>

text\<open>Note that the following lemmas are stronger versions of @{thm per_lemma_pref_suf fac_two_conjug_primroot fac_two_conjug_primroot  fac_two_prim_conjug} that have a relaxed length assumption @{term "\<^bold>|p\<^bold>| + \<^bold>|q\<^bold>| \<le> \<^bold>|w\<^bold>|"} instead of @{term "\<^bold>|p\<^bold>| + \<^bold>|q\<^bold>| - (gcd \<^bold>|p\<^bold>| \<^bold>|q\<^bold>|) \<le> \<^bold>|w\<^bold>|"} (and which follow from the relaxed version of periodicity lemma @{thm two_pers}.\<close>

lemma per_lemma_comm_pref:
  assumes "u \<le>p r\<^sup>@k" "u \<le>p s\<^sup>@l"
    and len: "\<^bold>|r\<^bold>| + \<^bold>|s\<^bold>| - gcd (\<^bold>|r\<^bold>|) (\<^bold>|s\<^bold>|) \<le> \<^bold>|u\<^bold>|"
  shows "r \<cdot> s = s \<cdot> r"
  using  pref_pow_root[OF assms(2)] pref_pow_root[OF assms(1)] per_lemma_comm[OF _ _ len] by blast

lemma per_lemma_pref_suf_gcd: assumes "w <p p \<cdot> w" and "w <s w \<cdot> q" and
  fw: "\<^bold>|p\<^bold>| + \<^bold>|q\<^bold>| - (gcd \<^bold>|p\<^bold>| \<^bold>|q\<^bold>|) \<le> \<^bold>|w\<^bold>|"
obtains r s k l m where "p = (r \<cdot> s)\<^sup>@k" and "q = (s \<cdot> r)\<^sup>@l" and "w = (r \<cdot> s)\<^sup>@m \<cdot> r" and "primitive (r\<cdot>s)"
proof-
  let ?q = "(w \<cdot> q)\<^sup><\<inverse>w"
  have "w <p ?q \<cdot> w"
    using ssufD1[OF \<open>w <s w \<cdot> q\<close>] rq_suf[symmetric, THEN per_rootI[OF prefI rq_ssuf_nemp[OF \<open>w <s w \<cdot> q\<close>]]]
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
    by fastforce
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
    using \<open>p' = (r \<cdot> s) \<^sup>@ k\<close> \<open>primitive (r \<cdot> s)\<close> \<open>p' \<noteq> \<epsilon>\<close> primroot_unique
    by meson
  hence "\<rho> p \<sim> r\<cdot>s"
    using conjug_primroot[OF \<open>p \<sim> p'\<close>]
    by simp
  moreover have "\<rho> q' = s\<cdot>r"
    using \<open>q' = (s \<cdot> r) \<^sup>@ l\<close> \<open>primitive (r \<cdot> s)\<close>[unfolded conjug_prim_iff'[of r]] \<open>q' \<noteq> \<epsilon>\<close> primroot_unique
     by meson
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
  unfolding prim_primroot[OF \<open>primitive u\<close>] prim_primroot[OF \<open>primitive v\<close>].

lemma two_pers_1:
  assumes pu: "w \<le>p u \<cdot> w" and pv: "w \<le>p v \<cdot> w" and len: "\<^bold>|u\<^bold>| + \<^bold>|v\<^bold>| - 1 \<le> \<^bold>|w\<^bold>|"
  shows "u \<cdot> v = v \<cdot> u"
proof (rule nemp_comm)
  assume "u \<noteq> \<epsilon>" "v \<noteq> \<epsilon>"
  hence "1 \<le> gcd \<^bold>|u\<^bold>| \<^bold>|v\<^bold>|"
    using nemp_len by (simp add: Suc_leI)
  thus ?thesis
    using per_lemma_comm[OF pu pv] len by linarith
qed

end
