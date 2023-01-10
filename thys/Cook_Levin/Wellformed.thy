section \<open>Well-formedness of lists\label{s:tm-wellformed}\<close>

theory Wellformed
  imports Symbol_Ops Lists_Lists
begin

text \<open>
In the representations introduced in Section~\ref{s:tm-numlist} and
Section~\ref{s:tm-numlistlist}, not every symbol sequence over @{text "\<zero>\<one>\<bar>"}
represents a list of numbers, and not every symbol sequence over @{text
"\<zero>\<one>\<bar>\<sharp>"} represents a list of lists of numbers. In this section we prove
criteria for symbol sequences to represent such lists and devise Turing machines
to check these criteria efficiently.
\<close>


subsection \<open>A criterion for well-formed lists\<close>

text \<open>
From the definition of @{const numlist} it is easy to see that a symbol sequence
representing a list of numbers is either empty or not, and that in the latter
case it ends with a @{text "\<bar>"} symbol. Moreover it can only contain the symbols
@{text "\<zero>\<one>\<bar>"} and cannot contain the symbol sequence @{text "\<zero>\<bar>"} because
canonical number representations cannot end in @{text \<zero>}. That these properties
are not only necessary but also sufficient for the symbol sequence to represent
a list of numbers is shown in this section.

A symbol sequence is well-formed if it represents a list of numbers.
\<close>

definition numlist_wf :: "symbol list \<Rightarrow> bool" where
  "numlist_wf zs \<equiv> \<exists>ns. numlist ns = zs"

lemma numlist_wf_append:
  assumes "numlist_wf xs" and "numlist_wf ys"
  shows "numlist_wf (xs @ ys)"
proof -
  obtain ms ns where "numlist ms = xs" and "numlist ns = ys"
    using assms numlist_wf_def by auto
  then have "numlist (ms @ ns) = xs @ ys"
    using numlist_append by simp
  then show ?thesis
    using numlist_wf_def by auto
qed

lemma numlist_wf_canonical:
  assumes "canonical xs"
  shows "numlist_wf (xs @ [\<bar>])"
proof -
  obtain n where "canrepr n = xs"
    using assms canreprI by blast
  then have "numlist [n] = xs @ [\<bar>]"
    using numlist_def by simp
  then show ?thesis
    using numlist_wf_def by auto
qed

text \<open>
Well-formed symbol sequences can be unambiguously decoded to lists of numbers.
\<close>

definition zs_numlist :: "symbol list \<Rightarrow> nat list" where
  "zs_numlist zs \<equiv> THE ns. numlist ns = zs"

lemma zs_numlist_ex1:
  assumes "numlist_wf zs"
  shows "\<exists>!ns. numlist ns = zs"
  using assms numlist_wf_def numlist_inj by blast

lemma numlist_zs_numlist:
  assumes "numlist_wf zs"
  shows "numlist (zs_numlist zs) = zs"
  using assms zs_numlist_def zs_numlist_ex1 by (smt (verit, del_insts) the_equality)

text \<open>
Count the number of occurrences of an element in a list:
\<close>

fun count :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "count [] z = 0" |
  "count (x # xs) z = (if x = z then 1 else 0) + count xs z"

lemma count_append: "count (xs @ ys) z = count xs z + count ys z"
  by (induction xs) simp_all

lemma count_0: "count xs z = 0 \<longleftrightarrow> (\<forall>x\<in>set xs. x \<noteq> z)"
proof
  show "count xs z = 0 \<Longrightarrow> \<forall>x\<in>set xs. x \<noteq> z"
    by (induction xs) auto
  show "\<forall>x\<in>set xs. x \<noteq> z \<Longrightarrow> count xs z = 0"
    by (induction xs) auto
qed

lemma count_gr_0_take:
  assumes "count xs z > 0"
  shows "\<exists>j.
    j < length xs \<and>
    xs ! j = z \<and>
    (\<forall>i<j. xs ! i \<noteq> z) \<and>
    count (take (Suc j) xs) z = 1 \<and>
    count (drop (Suc j) xs) z = count xs z - 1"
proof -
  let ?P = "\<lambda>i. i < length xs \<and> xs ! i = z"
  have ex: "\<exists>i. ?P i"
    using assms(1) count_0 by (metis bot_nat_0.not_eq_extremum in_set_conv_nth)
  define j where "j = Least ?P"
  have 1: "j < length xs"
    using j_def ex by (metis (mono_tags, lifting) LeastI)
  moreover have 2: "xs ! j = z"
    using j_def ex by (metis (mono_tags, lifting) LeastI)
  moreover have 3: "\<forall>i<j. xs ! i \<noteq> z"
    using j_def ex 1 not_less_Least order_less_trans by blast
  moreover have 4: "count (take (Suc j) xs) z = 1"
  proof -
    have "\<forall>x\<in>set (take j xs). x \<noteq> z"
      using 3 1 by (metis in_set_conv_nth length_take less_imp_le_nat min_absorb2 nth_take)
    then have "count (take j xs) z = 0"
      using count_0 by simp
    moreover have "count [xs ! j] z = 1"
      using 2 by simp
    moreover have "take (Suc j) xs = take j xs @ [xs ! j]"
      using 1 take_Suc_conv_app_nth by auto
    ultimately show "count (take (Suc j) xs) z = 1"
      using count_append by simp
  qed
  moreover have "count (drop (Suc j) xs) z = count xs z - 1"
  proof -
    have "xs = take (Suc j) xs @ drop (Suc j) xs"
      using 1 by simp
    then show ?thesis
      using count_append 4 by (metis add_diff_cancel_left')
  qed
  ultimately show ?thesis
    by auto
qed

definition has2 :: "symbol list \<Rightarrow> symbol \<Rightarrow> symbol \<Rightarrow> bool" where
  "has2 xs y z \<equiv> \<exists>i<length xs - 1. xs ! i = y \<and> xs ! (Suc i) = z"

lemma not_has2_take:
  assumes "\<not> has2 xs y z"
  shows "\<not> has2 (take m xs) y z"
proof (rule ccontr)
  let ?ys = "take m xs"
  assume "\<not> \<not> has2 ?ys y z"
  then have "has2 ?ys y z"
    by simp
  then have "has2 xs y z"
    using has2_def by fastforce
  then show False
    using assms by simp
qed

lemma not_has2_drop:
  assumes "\<not> has2 xs y z"
  shows "\<not> has2 (drop m xs) y z"
proof (rule ccontr)
  let ?ys = "drop m xs"
  assume "\<not> \<not> has2 ?ys y z"
  then have "has2 ?ys y z"
    by simp
  then have "has2 xs y z"
    using has2_def by fastforce
  then show False
    using assms by simp
qed

lemma numlist_wf_has2:
  assumes "proper_symbols xs" "symbols_lt 5 xs" "\<not> has2 xs \<zero> \<bar>" "xs \<noteq> [] \<longrightarrow> last xs = \<bar>"
  shows "numlist_wf xs"
  using assms
proof (induction "count xs \<bar>" arbitrary: xs)
  case 0
  then have "xs = []"
    using count_0 by simp
  then show ?case
    using numlist_wf_def numlist_Nil by blast
next
  case (Suc n)
  then obtain j :: nat where j:
    "j < length xs"
    "xs ! j = \<bar>"
    "\<forall>i<j. xs ! i \<noteq> \<bar>"
    "count (take (Suc j) xs) \<bar> = 1"
    "count (drop (Suc j) xs) \<bar> = count xs \<bar> - 1"
    by (metis count_gr_0_take zero_less_Suc)
  then have "xs \<noteq> []"
    by auto
  then have "last xs = \<bar>"
    using Suc.prems by simp

  let ?ys = "drop (Suc j) xs"
  have "count ?ys \<bar> = n"
    using j(5) Suc by simp
  moreover have "proper_symbols ?ys"
    using Suc.prems by simp
  moreover have "symbols_lt 5 ?ys"
    using Suc.prems by simp
  moreover have "\<not> has2 ?ys \<zero> \<bar>"
    using not_has2_drop Suc.prems(3) by simp
  moreover have "?ys \<noteq> [] \<longrightarrow> last ?ys = \<bar>"
    using j by (simp add: \<open>last xs = \<bar>\<close>)
  ultimately have wf_ys: "numlist_wf ?ys"
    using Suc by simp

  let ?zs = "take j xs"
  have "canonical ?zs"
  proof -
    have "?zs ! i \<ge> \<zero>" if "i < length ?zs" for i
      using that Suc.prems(1) j by (metis One_nat_def Suc_1 Suc_leI length_take min_less_iff_conj nth_take)
    moreover have "?zs ! i \<le> \<one>" if "i < length ?zs" for i
    proof -
      have "?zs ! i < \<bar>"
        using that Suc.prems(1,2) j
        by (metis eval_nat_numeral(3) length_take less_Suc_eq_le min_less_iff_conj nat_less_le nth_take)
      then show ?thesis
        by simp
    qed
    ultimately have "bit_symbols ?zs"
      by fastforce
    moreover have "?zs = [] \<or> last ?zs = \<one>"
    proof (cases "?zs = []")
      case True
      then show ?thesis
        by simp
    next
      case False
      then have "last ?zs = ?zs ! (j - 1)"
        by (metis add_diff_inverse_nat j(1) last_length length_take less_imp_le_nat less_one
          min_absorb2 plus_1_eq_Suc take_eq_Nil)
      then have last: "last ?zs = xs ! (j - 1)"
        using False by simp
      have "xs ! (j - 1) \<noteq> \<bar>"
        using j(3) False by simp
      moreover have "xs ! (j - 1) < \<sharp>"
        using Suc.prems(2) j(1) by simp
      moreover have "xs ! (j - 1) \<ge> \<zero>"
        using Suc.prems(1) j(1) by (metis One_nat_def Suc_1 Suc_leI less_imp_diff_less)
      moreover have "xs ! (j - 1) \<noteq> \<zero>"
      proof (rule ccontr)
        assume "\<not> xs ! (j - 1) \<noteq> \<zero>"
        then have "xs ! (j - 1) = \<zero>"
          by simp
        moreover have "xs ! j = \<bar>"
          using j by simp
        ultimately have "has2 xs \<zero> \<bar>"
          using has2_def j False
          by (metis (no_types, lifting) Nat.lessE add_diff_cancel_left' less_Suc_eq_0_disj not_less_eq plus_1_eq_Suc take_eq_Nil)
        then show False
          using Suc.prems(3) by simp
      qed
      ultimately have "xs ! (j - 1) = \<one>"
        by simp
      then have "last ?zs = \<one>"
        using last by simp
      then show ?thesis
        by simp
    qed
    ultimately show "canonical ?zs"
      using canonical_def by simp
  qed

  let ?ts = "take (Suc j) xs"
  have "?ts = ?zs @ [\<bar>]"
    using j by (metis take_Suc_conv_app_nth)
  then have "numlist_wf ?ts"
    using numlist_wf_canonical `canonical ?zs` by simp
  moreover have "xs = ?ts @ ?ys"
    by simp
  ultimately show "numlist_wf xs"
    using wf_ys numlist_wf_append by fastforce
qed

lemma last_numlist_4: "numlist ns \<noteq> [] \<Longrightarrow> last (numlist ns) = \<bar>"
proof (induction ns)
  case Nil
  then show ?case
    using numlist_def by simp
next
  case (Cons n ns)
  then show ?case
    using numlist_def by (cases "numlist ns = []") simp_all
qed

lemma numlist_not_has2:
  assumes "i < length (numlist ns) - 1" and "numlist ns ! i = \<zero>"
  shows "numlist ns ! (Suc i) \<noteq> \<bar>"
  using assms
proof (induction ns arbitrary: i)
  case Nil
  then show ?case
    by (simp add: numlist_Nil)
next
  case (Cons n ns)
  show "numlist (n # ns) ! (Suc i) \<noteq> \<bar>"
  proof (cases "i < length (numlist [n])")
    case True
    have "numlist (n # ns) ! i = (numlist [n] @ numlist ns) ! i"
      using numlist_def by simp
    then have "numlist (n # ns) ! i = numlist [n] ! i"
      using True by (simp add: nth_append)
    then have "numlist (n # ns) ! i = (canrepr n @ [\<bar>]) ! i"
      using numlist_def by simp
    moreover have "numlist (n # ns) ! i = \<zero>"
      using Cons by simp
    ultimately have "(canrepr n @ [\<bar>]) ! i = \<zero>"
      by simp
    moreover have "(canrepr n @ [\<bar>]) ! (length (canrepr n @ [\<bar>]) - 1) = \<bar>"
      by simp
    ultimately have "i \<noteq> length (canrepr n @ [\<bar>]) - 1"
      by auto
    then have *: "i \<noteq> length (numlist [n]) - 1"
      using numlist_def by simp

    have 3: "canrepr n ! j = numlist (n # ns) ! j" if "j < nlength n" for j
    proof -
      have j: "j < length (numlist [n])"
        using that numlist_def by simp
      have "numlist (n # ns) ! j = (numlist [n] @ numlist ns) ! j"
        using numlist_def by simp
      then have "numlist (n # ns) ! j = numlist [n] ! j"
        using j by (simp add: nth_append)
      then have "numlist (n # ns) ! j = (canrepr n @ [\<bar>]) ! j"
        using numlist_def by simp
      then show ?thesis
        by (simp add: nth_append that)
    qed

    have neq0: "n \<noteq> 0"
    proof -
      have "length (numlist [0]) = 1"
        using numlist_def by simp
      then show ?thesis
        using * True by (metis diff_self_eq_0 less_one)
    qed
    then have "i < length (numlist [n]) - 1"
      using * True by simp
    then have "i < length (canrepr n @ [\<bar>]) - 1"
      using numlist_def by simp
    then have "i < length (canrepr n)"
      by simp
    then have "canrepr n ! i = \<zero>"
      by (metis \<open>(canrepr n @ [\<bar>]) ! i = \<zero>\<close> nth_append)
    moreover have "last (canrepr n) \<noteq> \<zero>"
      using canonical_canrepr canonical_def
      by (metis neq0 length_0_conv n_not_Suc_n nlength_0 numeral_2_eq_2 numeral_3_eq_3)
    ultimately have "i \<noteq> nlength n - 1"
      by (metis \<open>i < nlength n\<close> last_conv_nth less_zeroE list.size(3))
    then have "i < nlength n - 1"
      using \<open>i < nlength n\<close> by linarith
    then have "Suc i < nlength n"
      by simp
    then have "canrepr n ! Suc i \<le> \<one>"
      using bit_symbols_canrepr by fastforce
    moreover have "canrepr n ! Suc i = numlist (n # ns) ! Suc i"
      using 3 \<open>Suc i < nlength n\<close> by blast
    ultimately show ?thesis
      by simp
  next
    case False
    let ?i = "i - length (numlist [n])"
    have "numlist (n # ns) ! i = (numlist [n] @ numlist ns) ! i"
      using numlist_def by simp
    then have "numlist (n # ns) ! i = numlist ns ! ?i"
      using False by (simp add: nth_append)
    then have "numlist ns ! ?i = \<zero>"
      using Cons by simp
    moreover have "?i < length (numlist ns) - 1"
    proof -
      have "length (numlist (n # ns)) = length (numlist [n]) + length (numlist ns)"
        using numlist_def by simp
      then show ?thesis
        using False Cons by simp
    qed
    ultimately have "numlist ns ! Suc ?i \<noteq> \<bar>"
      using Cons by simp
    moreover have "numlist (n # ns) ! Suc i = numlist ns ! Suc ?i"
      using False numlist_append
      by (smt (verit, del_insts) Suc_diff_Suc Suc_lessD append_Cons append_Nil diff_Suc_Suc not_less_eq nth_append)
    ultimately show ?thesis
      by simp
  qed
qed

lemma numlist_wf_has2':
  assumes "numlist_wf xs"
  shows "proper_symbols_lt 5 xs \<and> \<not> has2 xs \<zero> \<bar> \<and> (xs \<noteq> [] \<longrightarrow> last xs = \<bar>)"
proof -
  obtain ns where ns: "numlist ns = xs"
    using numlist_wf_def assms by auto
  have "proper_symbols xs"
    using proper_symbols_numlist ns by auto
  moreover have "symbols_lt 5 xs"
    using ns numlist_234
    by (smt (verit, best) One_nat_def Suc_1 eval_nat_numeral(3) in_mono insertE less_Suc_eq_le
      linorder_le_less_linear nle_le not_less0 nth_mem numeral_less_iff semiring_norm(76)
      semiring_norm(89) semiring_norm(90) singletonD)
  moreover have "\<not> has2 xs \<zero> \<bar>"
    using numlist_not_has2 ns has2_def by auto
  moreover have "xs \<noteq> [] \<longrightarrow> last xs = \<bar>"
    using last_numlist_4 ns by auto
  ultimately show ?thesis
    by simp
qed

lemma numlist_wf_iff:
  "numlist_wf xs \<longleftrightarrow> proper_symbols_lt 5 xs \<and> \<not> has2 xs \<zero> \<bar> \<and> (xs \<noteq> [] \<longrightarrow> last xs = \<bar>)"
  using numlist_wf_has2 numlist_wf_has2' by auto


subsection \<open>A criterion for well-formed lists of lists\<close>

text \<open>
The criterion for lists of lists of numbers is similar to the one for lists of
numbers. A non-empty symbol sequence must end in @{text \<sharp>}. All symbols must be
from @{text "\<zero>\<one>\<bar>\<sharp>"} and the sequences @{text "\<zero>\<bar>"}, @{text "\<zero>\<sharp>"}, and @{text
"\<one>\<sharp>"} are forbidden.

A symbol sequence is well-formed if it represents a list of lists of numbers.
\<close>

definition numlistlist_wf :: "symbol list \<Rightarrow> bool" where
  "numlistlist_wf zs \<equiv> \<exists>nss. numlistlist nss = zs"

lemma numlistlist_wf_append:
  assumes "numlistlist_wf xs" and "numlistlist_wf ys"
  shows "numlistlist_wf (xs @ ys)"
proof -
  obtain ms ns where "numlistlist ms = xs" and "numlistlist ns = ys"
    using assms numlistlist_wf_def by auto
  then have "numlistlist (ms @ ns) = xs @ ys"
    using numlistlist_append by simp
  then show ?thesis
    using numlistlist_wf_def by auto
qed

lemma numlistlist_wf_numlist_wf:
  assumes "numlist_wf xs"
  shows "numlistlist_wf (xs @ [\<sharp>])"
proof -
  obtain ns where "numlist ns = xs"
    using assms numlist_wf_def by auto
  then have "numlistlist [ns] = xs @ [\<sharp>]"
    using numlistlist_def by simp
  then show ?thesis
    using numlistlist_wf_def by auto
qed

lemma numlistlist_wf_has2:
  assumes "proper_symbols xs" "symbols_lt 6 xs" "xs \<noteq> [] \<longrightarrow> last xs = \<sharp>"
    and "\<not> has2 xs \<zero> \<bar>"
    and "\<not> has2 xs \<zero> \<sharp>"
    and "\<not> has2 xs \<one> \<sharp>"
  shows "numlistlist_wf xs"
  using assms
proof (induction "count xs \<sharp>" arbitrary: xs)
  case 0
  then have "xs = []"
    using count_0 by simp
  then show ?case
    using numlistlist_wf_def numlistlist_Nil by auto
next
  case (Suc n)
  then obtain j :: nat where j:
    "j < length xs"
    "xs ! j = \<sharp>"
    "\<forall>i<j. xs ! i \<noteq> \<sharp>"
    "count (take (Suc j) xs) \<sharp> = 1"
    "count (drop (Suc j) xs) \<sharp> = count xs \<sharp> - 1"
    by (metis count_gr_0_take zero_less_Suc)
  then have "xs \<noteq> []"
    by auto
  then have "last xs = \<sharp>"
    using Suc.prems by simp
  let ?ys = "drop (Suc j) xs"
  have "count ?ys \<sharp> = n"
    using j(5) Suc by simp
  moreover have "proper_symbols ?ys"
    using Suc.prems(1) by simp
  moreover have "symbols_lt 6 ?ys"
    using Suc.prems(2) by simp
  moreover have "?ys \<noteq> [] \<longrightarrow> last ?ys = \<sharp>"
    using j by (simp add: \<open>last xs = \<sharp>\<close>)
  moreover have "\<not> has2 ?ys \<zero> \<bar>"
    using not_has2_drop Suc.prems(4) by simp
  moreover have "\<not> has2 ?ys \<zero> \<sharp>"
    using not_has2_drop Suc.prems(5) by simp
  moreover have "\<not> has2 ?ys \<one> \<sharp>"
    using not_has2_drop Suc.prems(6) by simp
  ultimately have wf_ys: "numlistlist_wf ?ys"
    using Suc by simp

  let ?zs = "take j xs"
  have len: "length ?zs = j"
    using j(1) by simp
  have "numlist_wf ?zs"
  proof -
    have "proper_symbols ?zs"
      using Suc.prems(1) by simp
    moreover have "symbols_lt 5 ?zs"
    proof standard+
      fix i :: nat
      assume "i < length ?zs"
      then have "i < j"
        using j by simp
      then have "?zs ! i < 6"
        using Suc.prems(2) j by simp
      moreover have "?zs ! i \<noteq> \<sharp>"
        using `i < j` j by simp
      ultimately show "?zs ! i < \<sharp>"
        by simp
    qed
    moreover have "\<not> has2 ?zs \<zero> \<bar>"
      using not_has2_take Suc.prems(4) by simp
    moreover have "?zs \<noteq> [] \<longrightarrow> last ?zs = \<bar>"
    proof
      assume neq_Nil: "?zs \<noteq> []"
      then have "j > 0"
        by simp
      moreover have "xs ! j = \<sharp>"
        using j by simp
      ultimately have "xs ! Suc (j - 1) = \<sharp>"
        by simp
      moreover have "j - 1 < length xs - 1"
        by (simp add: Suc_leI \<open>0 < j\<close> diff_less_mono j(1))
      ultimately have "xs ! (j - 1) \<noteq> \<zero>" "xs ! (j - 1) \<noteq> \<one>"
        using Suc.prems has2_def by auto
      then have "?zs ! (j - 1) \<noteq> \<zero>" "?zs ! (j - 1) \<noteq> \<one>"
        by (simp_all add: \<open>0 < j\<close>)
      moreover have "?zs ! (j - 1) < \<sharp>"
        using `symbols_lt 5 ?zs` `0 < j ` j(1) len
        by simp
      moreover have "?zs ! (j - 1) \<ge> \<zero>"
        using `proper_symbols ?zs` len \<open>0 < j\<close> by (metis One_nat_def Suc_1 Suc_leI diff_less zero_less_one)
      ultimately have "?zs ! (j - 1) = \<bar>"
        by simp
      then show "last ?zs = \<bar>"
        using len by (metis last_conv_nth neq_Nil)
    qed
    ultimately show "numlist_wf ?zs"
      using numlist_wf_iff by simp
  qed

  let ?ts = "take (Suc j) xs"
  have "?ts = ?zs @ [\<sharp>]"
    using j by (metis take_Suc_conv_app_nth)
  then have "numlistlist_wf ?ts"
    using numlistlist_wf_numlist_wf `numlist_wf ?zs` by simp
  moreover have "xs = ?ts @ ?ys"
    by simp
  ultimately show "numlistlist_wf xs"
    using wf_ys numlistlist_wf_append by fastforce
qed

lemma numlistlist_not_has2:
  assumes "i < length (numlistlist nss) - 1" and "numlistlist nss ! i = \<zero>"
  shows "numlistlist nss ! (Suc i) \<noteq> \<bar>"
  using assms
proof (induction nss arbitrary: i)
  case Nil
  then show ?case
    by (simp add: numlistlist_Nil)
next
  case (Cons ns nss)
  show "numlistlist (ns # nss) ! (Suc i) \<noteq> \<bar>"
  proof (cases "i < length (numlistlist [ns])")
    case True
    have "numlistlist (ns # nss) ! i = (numlistlist [ns] @ numlistlist nss) ! i"
      using numlistlist_def by simp
    then have "numlistlist (ns # nss) ! i = numlistlist [ns] ! i"
      using True by (simp add: nth_append)
    then have "numlistlist (ns # nss) ! i = (numlist ns @ [\<sharp>]) ! i"
      using numlistlist_def by simp
    moreover have "numlistlist (ns # nss) ! i = \<zero>"
      using Cons by simp
    ultimately have "(numlist ns @ [\<sharp>]) ! i = \<zero>"
      by simp
    moreover have "(numlist ns @ [\<sharp>]) ! (length (numlist ns @ [\<sharp>]) - 1) = \<sharp>"
      by simp
    ultimately have "i \<noteq> length (numlist ns @ [\<sharp>]) - 1"
      by auto
    then have *: "i \<noteq> length (numlistlist [ns]) - 1"
      using numlistlist_def by simp
    then have **: "i < length (numlistlist [ns]) - 1"
      using True by simp
    then have ***: "i < length (numlist ns)"
      using numlistlist_def by simp
    then have "ns \<noteq> []"
      using numlist_Nil by auto
    then have "last (numlist ns) = \<bar>"
      by (metis last_numlist_4 numlist_Nil numlist_inj)

    have 3: "numlist ns ! j = numlistlist (ns # nss) ! j" if "j < length (numlist ns)" for j
    proof -
      have j: "j < length (numlistlist [ns])"
        using that numlistlist_def by simp
      have "numlistlist (ns # nss) ! j = (numlistlist [ns] @ numlistlist nss) ! j"
        using numlistlist_def by simp
      then have "numlistlist (ns # nss) ! j = numlistlist [ns] ! j"
        using j by (simp add: nth_append)
      then have "numlistlist (ns # nss) ! j = (numlist ns @ [\<sharp>]) ! j"
        using numlistlist_def by simp
      then show ?thesis
        by (simp add: nth_append that)
    qed
    have 4: "numlistlist (ns # nss) ! (length (numlist ns)) = \<sharp>"
      by (simp add: numlistlist_def)

    show ?thesis
    proof (cases "i = length (numlist ns) - 1")
      case True
      then show ?thesis
        using 3 4 *** by (metis Suc_le_D Suc_le_eq diff_Suc_1 eval_nat_numeral(3) n_not_Suc_n)
    next
      case False
      then have "i < length (numlist ns) - 1"
        using *** by simp
      then show ?thesis
        using numlist_not_has2 *** 3 \<open>ns \<noteq> []\<close>
        by (metis Cons.prems(2) Suc_diff_1 length_greater_0_conv not_less_eq numlist_Nil numlist_inj)
    qed
  next
    case False
    then have "i \<ge> length (numlistlist [ns])"
      by simp
    let ?i = "i - length (numlistlist [ns])"
    have "numlistlist (ns # nss) ! i = (numlistlist [ns] @ numlistlist nss) ! i"
      using numlistlist_def by simp
    then have "numlistlist (ns # nss) ! i = numlistlist nss ! ?i"
      using False by (simp add: nth_append)
    then have "numlistlist nss ! ?i = \<zero>"
      using Cons by simp
    moreover have "?i < length (numlistlist nss) - 1"
    proof -
      have "length (numlistlist (ns # nss)) = length (numlistlist [ns]) + length (numlistlist nss)"
        using numlistlist_def by simp
      then show ?thesis
        using False Cons by simp
    qed
    ultimately have "numlistlist nss ! Suc ?i \<noteq> \<bar>"
      using Cons by simp
    moreover have "numlistlist (ns # nss) ! Suc i = numlistlist nss ! Suc ?i"
      using False numlistlist_append
      by (smt (verit, del_insts) Suc_diff_Suc Suc_lessD append_Cons append_Nil diff_Suc_Suc not_less_eq nth_append)
    ultimately show ?thesis
      by simp
  qed
qed

lemma numlistlist_not_has2':
  assumes "i < length (numlistlist nss) - 1" and "numlistlist nss ! i = \<zero> \<or> numlistlist nss ! i = \<one>"
  shows "numlistlist nss ! (Suc i) \<noteq> \<sharp>"
  using assms
proof (induction nss arbitrary: i)
  case Nil
  then show ?case
    by (simp add: numlistlist_Nil)
next
  case (Cons ns nss)
  show "numlistlist (ns # nss) ! (Suc i) \<noteq> \<sharp>"
  proof (cases "i < length (numlistlist [ns])")
    case True
    have "numlistlist (ns # nss) ! i = (numlistlist [ns] @ numlistlist nss) ! i"
      using numlistlist_def by simp
    then have "numlistlist (ns # nss) ! i = numlistlist [ns] ! i"
      using True by (simp add: nth_append)
    then have "numlistlist (ns # nss) ! i = (numlist ns @ [\<sharp>]) ! i"
      using numlistlist_def by simp
    moreover have "numlistlist (ns # nss) ! i = \<zero> \<or> numlistlist (ns # nss) ! i = \<one>"
      using Cons by simp
    ultimately have "(numlist ns @ [\<sharp>]) ! i = \<zero> \<or> (numlist ns @ [\<sharp>]) ! i = \<one>"
      by simp
    moreover have "(numlist ns @ [\<sharp>]) ! (length (numlist ns @ [\<sharp>]) - 1) = \<sharp>"
      by simp
    ultimately have "i \<noteq> length (numlist ns @ [\<sharp>]) - 1"
      by auto
    then have "i \<noteq> length (numlistlist [ns]) - 1"
      using numlistlist_def by simp
    then have "i < length (numlistlist [ns]) - 1"
      using True by simp
    then have *: "i < length (numlist ns)"
      using numlistlist_def by simp
    then have "ns \<noteq> []"
      using numlist_Nil by auto
    then have "last (numlist ns) = \<bar>"
      by (metis last_numlist_4 numlist_Nil numlist_inj)

    have **: "numlist ns ! j = numlistlist (ns # nss) ! j" if "j < length (numlist ns)" for j
    proof -
      have j: "j < length (numlistlist [ns])"
        using that numlistlist_def by simp
      have "numlistlist (ns # nss) ! j = (numlistlist [ns] @ numlistlist nss) ! j"
        using numlistlist_def by simp
      then have "numlistlist (ns # nss) ! j = numlistlist [ns] ! j"
        using j by (simp add: nth_append)
      then have "numlistlist (ns # nss) ! j = (numlist ns @ [\<sharp>]) ! j"
        using numlistlist_def by simp
      then show ?thesis
        by (simp add: nth_append that)
    qed

    show ?thesis
    proof (cases "i = length (numlist ns) - 1")
      case True
      then show ?thesis
        using \<open>last (numlist ns) = \<bar>\<close> \<open>ns \<noteq> []\<close> Cons.prems(2) * ** numlist_Nil numlist_inj
        by (metis last_conv_nth num.simps(8) numeral_eq_iff semiring_norm(83) verit_eq_simplify(8))
    next
      case False
      then have "i < length (numlist ns) - 1"
        using * by simp
      then show ?thesis
        using * ** symbols_lt_numlist numlist_not_has2 by (metis Suc_lessI diff_Suc_1 less_irrefl_nat)
    qed
  next
    case False
    then have "i \<ge> length (numlistlist [ns])"
      by simp
    let ?i = "i - length (numlistlist [ns])"
    have "numlistlist (ns # nss) ! i = (numlistlist [ns] @ numlistlist nss) ! i"
      using numlistlist_def by simp
    then have "numlistlist (ns # nss) ! i = numlistlist nss ! ?i"
      using False by (simp add: nth_append)
    then have "numlistlist nss ! ?i = \<zero> \<or> numlistlist nss ! ?i = \<one>"
      using Cons by simp
    moreover have "?i < length (numlistlist nss) - 1"
    proof -
      have "length (numlistlist (ns # nss)) = length (numlistlist [ns]) + length (numlistlist nss)"
        using numlistlist_def by simp
      then show ?thesis
        using False Cons by simp
    qed
    ultimately have "numlistlist nss ! Suc ?i \<noteq> \<sharp>"
      using Cons by simp
    moreover have "numlistlist (ns # nss) ! Suc i = numlistlist nss ! Suc ?i"
      using False numlistlist_append
      by (smt (verit, del_insts) Suc_diff_Suc Suc_lessD append_Cons append_Nil diff_Suc_Suc not_less_eq nth_append)
    ultimately show ?thesis
      by simp
  qed
qed

lemma last_numlistlist_5: "numlistlist nss \<noteq> [] \<Longrightarrow> last (numlistlist nss) = \<sharp>"
  using numlistlist_def by (induction nss) simp_all

lemma numlistlist_wf_has2':
  assumes "numlistlist_wf xs"
  shows "proper_symbols_lt 6 xs \<and> (xs \<noteq> [] \<longrightarrow> last xs = \<sharp>) \<and> \<not> has2 xs \<zero> \<bar> \<and> \<not> has2 xs \<zero> \<sharp> \<and> \<not> has2 xs \<one> \<sharp>"
proof -
  obtain nss where nss: "numlistlist nss = xs"
    using numlistlist_wf_def assms by auto
  have "proper_symbols xs"
    using nss proper_symbols_numlistlist by auto
  moreover have "symbols_lt 6 xs"
    using nss symbols_lt_numlistlist by auto
  moreover have "xs \<noteq> [] \<longrightarrow> last xs = \<sharp>"
    using nss last_numlistlist_5 by auto
  moreover have "\<not> has2 xs \<zero> \<bar>" and "\<not> has2 xs \<zero> \<sharp>" and "\<not> has2 xs \<one> \<sharp>"
    using numlistlist_not_has2 numlistlist_not_has2' has2_def nss by auto
  ultimately show ?thesis
    by simp
qed

lemma numlistlist_wf_iff:
  "numlistlist_wf xs \<longleftrightarrow>
   proper_symbols_lt 6 xs \<and> (xs \<noteq> [] \<longrightarrow> last xs = \<sharp>) \<and> \<not> has2 xs \<zero> \<bar> \<and> \<not> has2 xs \<zero> \<sharp> \<and> \<not> has2 xs \<one> \<sharp>"
  using numlistlist_wf_has2 numlistlist_wf_has2' by blast


subsection \<open>A Turing machine to check for subsequences of length two\<close>

text \<open>
In order to implement the well-formedness criteria we need to be able to check a
symbol sequence for subsequences of length two. The next Turing machine has
symbol parameters $y$ and $z$ and checks whether the sequence @{term "[y, z]"}
exists on tape $j_1$. It writes to tape $j_2$ the number~0 or~1 if the sequence
is present or not, respectively.
\<close>

definition tm_not_has2 :: "symbol \<Rightarrow> symbol \<Rightarrow> tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_not_has2 y z j1 j2 \<equiv>
    tm_set j2 [\<zero>, \<zero>] ;;
    WHILE [] ; \<lambda>rs. rs ! j1 \<noteq> \<box> DO
      IF \<lambda>rs. rs ! j2 = \<one> \<and> rs ! j1 = z THEN
        tm_right j2 ;;
        tm_write j2 \<one> ;;
        tm_left j2
      ELSE
        []
      ENDIF ;;
      tm_trans2 j1 j2 (\<lambda>h. if h = y then \<one> else \<zero>) ;;
      tm_right j1
    DONE ;;
    tm_right j2 ;;
    IF \<lambda>rs. rs ! j2 = \<one> THEN
      tm_set j2 (canrepr 1)
    ELSE
      tm_set j2 (canrepr 0)
    ENDIF ;;
    tm_cr j1 ;;
    tm_not j2"

lemma tm_not_has2_tm:
  assumes "k \<ge> 2" and "G \<ge> 4" and "0 < j2" and "j1 < k" and "j2 < k"
  shows "turing_machine k G (tm_not_has2 y z j1 j2)"
proof -
  have "symbols_lt G [\<zero>, \<zero>]"
    using assms(2) by (simp add: nth_Cons')
  moreover have "symbols_lt G (canrepr 0)"
    using assms(2) by simp
  moreover have "symbols_lt G (canrepr 1)"
    using assms(2) canrepr_1 by simp
  ultimately show ?thesis
  unfolding tm_not_has2_def
  using assms tm_right_tm tm_write_tm tm_left_tm tm_cr_tm Nil_tm tm_trans2_tm tm_set_tm
    turing_machine_loop_turing_machine turing_machine_branch_turing_machine tm_not_tm
  by simp
qed

locale turing_machine_has2 =
  fixes y z :: symbol and j1 j2 :: tapeidx
begin

context
  fixes tps0 :: "tape list" and xs :: "symbol list" and k :: nat
  assumes xs: "proper_symbols xs"
  assumes yz: "y > 1" "z > 1"
  assumes jk: "j1 < k" "j2 < k" "j1 \<noteq> j2" "0 < j2" "length tps0 = k"
  assumes tps0:
    "tps0 ! j1 = (\<lfloor>xs\<rfloor>, 1)"
    "tps0 ! j2 = (\<lfloor>[]\<rfloor>, 1)"
begin

definition "tm1 \<equiv> tm_set j2 [\<zero>, \<zero>]"

definition "tmT1 \<equiv> tm_right j2"
definition "tmT2 \<equiv> tmT1 ;; tm_write j2 \<one>"
definition "tmT3 \<equiv> tmT2 ;; tm_left j2"

definition "tmL1 \<equiv> IF \<lambda>rs. rs ! j2 = \<one> \<and> rs ! j1 = z THEN tmT3 ELSE [] ENDIF"
definition "tmL2 \<equiv> tmL1 ;; tm_trans2 j1 j2 (\<lambda>h. if h = y then \<one> else \<zero>)"
definition "tmL3 \<equiv> tmL2 ;; tm_right j1"
definition "tmL \<equiv> WHILE [] ; \<lambda>rs. rs ! j1 \<noteq> \<box> DO tmL3 DONE"

definition "tm2 \<equiv> tm1 ;; tmL"
definition "tm3 \<equiv> tm2 ;; tm_right j2"
definition "tm34 \<equiv> IF \<lambda>rs. rs ! j2 = \<one> THEN tm_set j2 (canrepr 1) ELSE tm_set j2 (canrepr 0) ENDIF"
definition "tm4 \<equiv> tm3 ;; tm34"
definition "tm5 \<equiv> tm4 ;; tm_cr j1"
definition "tm6 \<equiv> tm5 ;; tm_not j2"

lemma tm6_eq_tm_not_has2: "tm6 = tm_not_has2 y z j1 j2"
  unfolding tm6_def tm5_def tm4_def tm34_def tm3_def tm2_def tmL_def tmL3_def tmL2_def tmL1_def
    tmT3_def tmT2_def tmT1_def tm1_def tm_not_has2_def
  by simp

definition tps1 :: "tape list" where
  "tps1 \<equiv> tps0
    [j1 := (\<lfloor>xs\<rfloor>, 1),
     j2 := (\<lfloor>[\<zero>, \<zero>]\<rfloor>, 1)]"

lemma tm1: "transforms tm1 tps0 14 tps1"
  unfolding tm1_def
proof (tform tps: tps0 tps1_def jk)
  show "\<forall>i<length [\<zero>, \<zero>]. Suc 0 < [\<zero>, \<zero>] ! i"
    by (simp add: nth_Cons')
  show "tps1 = tps0[j2 := (\<lfloor>[\<zero>, \<zero>]\<rfloor>, 1)]"
    using tps1_def tps0 jk by (metis list_update_id)
qed

abbreviation has_at :: "nat \<Rightarrow> bool" where
  "has_at i \<equiv> xs ! i = y \<and> xs ! Suc i = z"

definition tpsL :: "nat \<Rightarrow> tape list" where
  "tpsL t \<equiv> tps0
    [j1 := (\<lfloor>xs\<rfloor>, Suc t),
     j2 := (\<lfloor>[if \<lfloor>xs\<rfloor> t = y then \<one> else \<zero>, if \<exists>i<t - 1. has_at i then \<one> else \<zero>]\<rfloor>, 1)]"

lemma tpsL_eq_tps1: "tpsL 0 = tps1"
  unfolding tps1_def tpsL_def using yz jk by simp

lemma tm1' [transforms_intros]: "transforms tm1 tps0 14 (tpsL 0)"
  using tm1 tpsL_eq_tps1 by simp

definition tpsT1 :: "nat \<Rightarrow> tape list" where
  "tpsT1 t \<equiv> tps0
    [j1 := (\<lfloor>xs\<rfloor>, Suc t),
     j2 := (\<lfloor>[if \<lfloor>xs\<rfloor> t = y then \<one> else \<zero>, if \<exists>i<t - 1. has_at i then \<one> else \<zero>]\<rfloor>, 2)]"

definition tpsT2 :: "nat \<Rightarrow> tape list" where
  "tpsT2 t \<equiv> tps0
    [j1 := (\<lfloor>xs\<rfloor>, Suc t),
     j2 := (\<lfloor>[if \<lfloor>xs\<rfloor> t = y then \<one> else \<zero>, if \<exists>i<t. has_at i then \<one> else \<zero>]\<rfloor>, 2)]"

definition tpsT3 :: "nat \<Rightarrow> tape list" where
  "tpsT3 t \<equiv> tps0
    [j1 := (\<lfloor>xs\<rfloor>, Suc t),
     j2 := (\<lfloor>[if \<lfloor>xs\<rfloor> t = y then \<one> else \<zero>, if \<exists>i<t. has_at i then \<one> else \<zero>]\<rfloor>, 1)]"

lemma contents_1_update: "(\<lfloor>[a, b]\<rfloor>, 1) |:=| v = (\<lfloor>[v, b]\<rfloor>, 1)" for a b v :: symbol
  using contents_def by auto

lemma contents_2_update: "(\<lfloor>[a, b]\<rfloor>, 2) |:=| v = (\<lfloor>[a, v]\<rfloor>, 2)" for a b v :: symbol
  using contents_def by auto

context
  fixes t :: nat
  assumes then_branch: "\<lfloor>xs\<rfloor> t = y" "xs ! t = z"
begin

lemma tmT1 [transforms_intros]: "transforms tmT1 (tpsL t) 1 (tpsT1 t)"
  unfolding tmT1_def
proof (tform tps: tpsL_def tpsT1_def jk)
  have "tpsL t ! j2 |+| 1 = (\<lfloor>[if \<lfloor>xs\<rfloor> t = y then \<one> else \<zero>, if \<exists>i<t - 1. has_at i then \<one> else \<zero>]\<rfloor>, 2)"
    using jk tpsL_def by simp
  moreover have "tpsT1 t = (tpsL t)[j2 := (\<lfloor>[if \<lfloor>xs\<rfloor> t = y then \<one> else \<zero>, if \<exists>i<t - 1. has_at i then \<one> else \<zero>]\<rfloor>, 2)]"
    unfolding tpsT1_def tpsL_def by simp
  ultimately show "tpsT1 t = (tpsL t)[j2 := tpsL t ! j2 |+| 1]"
    by presburger
qed

lemma tmT2 [transforms_intros]: "transforms tmT2 (tpsL t) 2 (tpsT2 t)"
  unfolding tmT2_def
proof (tform tps: tpsT1_def tpsT2_def jk)
  have 1: "tpsT1 t ! j2 = (\<lfloor>[if \<lfloor>xs\<rfloor> t = y then \<one> else \<zero>, if \<exists>i<t - 1. has_at i then \<one> else \<zero>]\<rfloor>, 2)"
    using tpsT1_def jk by simp
  have 2: "tpsT1 t ! j2 |:=| \<one> = (\<lfloor>[if \<lfloor>xs\<rfloor> t = y then \<one> else \<zero>, \<one>]\<rfloor>, 2)"
    using tpsT1_def jk contents_2_update by simp
  have 3: "tpsT2 t ! j2 = (\<lfloor>[if \<lfloor>xs\<rfloor> t = y then \<one> else \<zero>, if \<exists>i<t. has_at i then \<one> else \<zero>]\<rfloor>, 2)"
    using tpsT2_def jk by simp

  have "\<exists>i<t. has_at i"
  proof -
    have "t > 0"
      using then_branch(1) yz(1) by (metis contents_at_0 gr0I less_numeral_extra(4))
    then have "y = xs ! (t - 1)"
      using then_branch(1) by (metis contents_def nat_neq_iff not_one_less_zero yz(1))
    moreover have "z = xs ! t"
      using then_branch(2) by simp
    ultimately have "has_at (t - 1)"
      using `0 < t` by simp
    then show "\<exists>i<t. has_at i"
      using `0 < t` by (metis Suc_pred' lessI)
  qed
  then have "(if \<exists>i<t. has_at i then \<one> else \<zero>) = \<one>"
    by simp
  then have "tpsT1 t ! j2 |:=| \<one> = (\<lfloor>[if \<lfloor>xs\<rfloor> t = y then \<one> else \<zero>, if \<exists>i<t. has_at i then \<one> else \<zero>]\<rfloor>, 2)"
    using 2 3 by (smt (verit, ccfv_threshold))
  then show "tpsT2 t = (tpsT1 t)[j2 := tpsT1 t ! j2 |:=| \<one>]"
    unfolding tpsT2_def tpsT1_def using jk by simp
qed

lemma tmT3 [transforms_intros]: "transforms tmT3 (tpsL t) 3 (tpsT3 t)"
  unfolding tmT3_def by (tform tps: tpsT2_def tpsT3_def jk)

end

lemma tmL1 [transforms_intros]:
  assumes "ttt = 5" and "t < length xs"
  shows "transforms tmL1 (tpsL t) ttt (tpsT3 t)"
  unfolding tmL1_def
proof (tform tps: assms(1) tpsL_def tpsT3_def jk)
  have "read (tpsL t) ! j1 = tpsL t :.: j1"
    using jk tpsL_def tapes_at_read'[of j1 "tpsL t"] by simp
  then have 1: "read (tpsL t) ! j1 = xs ! t"
    using jk tpsL_def assms(2) by simp
  then show "read (tpsL t) ! j2 = \<one> \<and> read (tpsL t) ! j1 = z \<Longrightarrow> xs ! t = z"
    by simp
  have "read (tpsL t) ! j2 = tpsL t :.: j2"
    using jk tpsL_def tapes_at_read'[of j2 "tpsL t"] by simp
  then have 2: "read (tpsL t) ! j2 = (if \<lfloor>xs\<rfloor> t = y then \<one> else \<zero>)"
    using jk tpsL_def by simp
  then show "read (tpsL t) ! j2 = \<one> \<and> read (tpsL t) ! j1 = z \<Longrightarrow> \<lfloor>xs\<rfloor> t = y"
    by presburger
  show "tpsT3 t = tpsL t" if "\<not> (read (tpsL t) ! j2 = \<one> \<and> read (tpsL t) ! j1 = z)"
  proof -
    have "(\<exists>i<t. has_at i) = (\<exists>i<t - 1. has_at i)"
    proof (cases "t = 0")
      case True
      then show ?thesis
        by simp
    next
      case False
      have "\<not> ((if \<lfloor>xs\<rfloor> t = y then 0::symbol else 1) = 0 \<and> xs ! t = z)"
        using 1 2 that by simp
      then have "\<not> (\<lfloor>xs\<rfloor> t = y \<and> xs ! t = z)"
        by auto
      then have "\<not> (has_at (t - 1))"
        using False Suc_pred' assms(2) contents_inbounds less_imp_le_nat by simp
      moreover have "(\<exists>i<t. has_at i) = (\<exists>i<t - Suc 0. has_at i) \<or> has_at (t - 1)"
        using False by (metis One_nat_def add_diff_inverse_nat less_Suc_eq less_one plus_1_eq_Suc)
      ultimately show ?thesis
        by auto
    qed
    then have eq: "(if \<exists>i<t - 1. has_at i then \<one> else \<zero>) = (if \<exists>i<t. has_at i then \<one> else \<zero>)"
      by simp
    show ?thesis
      unfolding tpsT3_def tpsL_def by (simp only: eq)
  qed
qed

definition tpsL2 :: "nat \<Rightarrow> tape list" where
  "tpsL2 t \<equiv> tps0
    [j1 := (\<lfloor>xs\<rfloor>, Suc t),
     j2 := (\<lfloor>[if \<lfloor>xs\<rfloor> (Suc t) = y then \<one> else \<zero>, if \<exists>i<t. has_at i then \<one> else \<zero>]\<rfloor>, 1)]"

lemma tmL2 [transforms_intros]:
  assumes "ttt = 6" and "t < length xs"
  shows "transforms tmL2 (tpsL t) ttt (tpsL2 t)"
  unfolding tmL2_def
proof (tform tps: assms tpsL_def tpsT3_def jk)
  have "tpsT3 t ! j2 = (\<lfloor>[if \<lfloor>xs\<rfloor> t = y then \<one> else \<zero>, if \<exists>i<t. has_at i then \<one> else \<zero>]\<rfloor>, 1)"
    using jk tpsT3_def by simp
  then have "tpsT3 t ! j2 |:=| (if tpsT3 t :.: j1 = y then \<one> else \<zero>) =
      (\<lfloor>[if tpsT3 t :.: j1 = y then \<one> else \<zero>, if \<exists>i<t. has_at i then \<one> else \<zero>]\<rfloor>, 1)"
    using contents_1_update by simp
  moreover have "tpsT3 t :.: j1 = \<lfloor>xs\<rfloor> (Suc t)"
    using assms(2) tpsT3_def jk by simp
  ultimately have "tpsT3 t ! j2 |:=| (if tpsT3 t :.: j1 = y then \<one> else \<zero>) =
      (\<lfloor>[if \<lfloor>xs\<rfloor> (Suc t) = y then \<one> else \<zero>, if \<exists>i<t. has_at i then \<one> else \<zero>]\<rfloor>, 1)"
    by auto
  moreover have "tpsL2 t = (tpsT3 t)[j2 := (\<lfloor>[if \<lfloor>xs\<rfloor> (Suc t) = y then \<one> else \<zero>, if \<exists>i<t. has_at i then \<one> else \<zero>]\<rfloor>, 1)]"
    using tpsL2_def tpsT3_def by simp
  ultimately show "tpsL2 t = (tpsT3 t)[j2 := tpsT3 t ! j2 |:=| (if tpsT3 t :.: j1 = y then \<one> else \<zero>)]"
    by presburger
qed

lemma tmL3 [transforms_intros]:
  assumes "ttt = 7" and "t < length xs"
  shows "transforms tmL3 (tpsL t) ttt (tpsL (Suc t))"
  unfolding tmL3_def
proof (tform tps: assms tpsL_def tpsL2_def jk)
  have "tpsL2 t ! j1 = (\<lfloor>xs\<rfloor>, Suc t)"
    using tpsL2_def jk by simp
  then show "tpsL (Suc t) = (tpsL2 t)[j1 := tpsL2 t ! j1 |+| 1]"
    using tpsL2_def tpsL_def jk by (simp add: list_update_swap)
qed

lemma tmL [transforms_intros]:
  assumes "ttt = 9 * length xs + 1"
  shows "transforms tmL (tpsL 0) ttt (tpsL (length xs))"
  unfolding tmL_def
proof (tform time: assms)
  have "read (tpsL t) ! j1 = tpsL t :.: j1" for t
    using tpsL_def tapes_at_read' jk
    by (metis (no_types, lifting) length_list_update)
  then have "read (tpsL t) ! j1 = \<lfloor>xs\<rfloor> (Suc t)" for t
    using tpsL_def jk by simp
  then show "\<And>t. t < length xs \<Longrightarrow> read (tpsL t) ! j1 \<noteq> \<box>" and "\<not> read (tpsL (length xs)) ! j1 \<noteq> \<box>"
    using xs by auto
qed

lemma tm2 [transforms_intros]:
  assumes "ttt = 9 * length xs + 15"
  shows "transforms tm2 tps0 ttt (tpsL (length xs))"
  unfolding tm2_def by (tform tps: assms tpsL_def jk)

definition tps3 :: "tape list" where
  "tps3 \<equiv> tps0
    [j1 := (\<lfloor>xs\<rfloor>, Suc (length xs)),
     j2 := (\<lfloor>[if \<lfloor>xs\<rfloor> (length xs) = y then \<one> else \<zero>, if \<exists>i<length xs - 1. has_at i then \<one> else \<zero>]\<rfloor>, 2)]"

lemma tm3 [transforms_intros]:
  assumes "ttt = 9 * length xs + 16"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: assms tpsL_def jk)
  show "tps3 = (tpsL (length xs))[j2 := tpsL (length xs) ! j2 |+| 1]"
    unfolding tps3_def tpsL_def
    using jk
    by (metis (no_types, lifting) One_nat_def Suc_1 add.right_neutral add_Suc_right fst_conv length_list_update
      list_update_overwrite nth_list_update_eq snd_conv)
qed

definition tps4 :: "tape list" where
  "tps4 \<equiv> tps0
    [j1 := (\<lfloor>xs\<rfloor>, Suc (length xs)),
     j2 := (\<lfloor>\<exists>i<length xs - Suc 0. has_at i\<rfloor>\<^sub>B, 1)]"

lemma tm34 [transforms_intros]:
  assumes "ttt = 19"
  shows "transforms tm34 tps3 ttt tps4"
  unfolding tm34_def
proof (tform tps: assms tps4_def tps3_def jk)
  let ?pair = "[if \<lfloor>xs\<rfloor> (length xs) = y then \<one> else \<zero>, if \<exists>i<length xs - Suc 0. has_at i then \<one> else \<zero>]"
  show 1: "proper_symbols ?pair" and "proper_symbols ?pair"
    by (simp_all add: nth_Cons')
  show "proper_symbols (canrepr 1)"
    using proper_symbols_canrepr by simp

  have "read tps3 ! j2 = (if \<exists>i<length xs - Suc 0. has_at i then \<one> else \<zero>)"
    using jk tps3_def tapes_at_read'[of j2 tps3] by simp
  then have *: "read tps3 ! j2 = \<one> \<longleftrightarrow> (\<exists>i<length xs - Suc 0. has_at i)"
    by simp

  show "clean_tape (tps3 ! j2)" "clean_tape (tps3 ! j2)"
    using jk tps3_def clean_contents_proper[OF 1] by simp_all
  show "tps4 = tps3[j2 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]" if "read tps3 ! j2 = \<one>"
  proof -
    have "\<exists>i<length xs - Suc 0. has_at i"
      using that * by simp
    then have "(\<lfloor>\<exists>i<length xs - Suc 0. has_at i\<rfloor>\<^sub>B, 1) = (\<lfloor>1\<rfloor>\<^sub>N, 1)"
      by simp
    then have "tps4 = tps0
        [j1 := (\<lfloor>xs\<rfloor>, Suc (length xs)),
         j2 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"
      using tps4_def by simp
    then show ?thesis
      using tps3_def by simp
  qed
  show "tps4 = tps3[j2 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]" if "read tps3 ! j2 \<noteq> \<one>"
  proof -
    have "\<not> (\<exists>i<length xs - Suc 0. has_at i)"
      using that * by simp
    then have "(\<lfloor>\<exists>i<length xs - Suc 0. has_at i\<rfloor>\<^sub>B, 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
      by auto
    then have "tps4 = tps0
        [j1 := (\<lfloor>xs\<rfloor>, Suc (length xs)),
         j2 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"
      using tps4_def by simp
    then show ?thesis
      using tps3_def by simp
  qed

  have "tps3 :#: j2 = 2"
    using jk tps3_def by simp
  then show "8 + tps3 :#: j2 + 2 * length ?pair + Suc (2 * nlength 1) + 2 \<le> ttt"
    and "8 + tps3 :#: j2 + 2 * length ?pair + Suc (2 * nlength 0) + 1 \<le> ttt"
    using assms nlength_1_simp by simp_all
qed

lemma tm4:
  assumes "ttt = 9 * length xs + 35"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def by (tform tps: assms)

definition tps4' :: "tape list" where
  "tps4' \<equiv> tps0
    [j1 := (\<lfloor>xs\<rfloor>, Suc (length xs)),
     j2 := (\<lfloor>has2 xs y z\<rfloor>\<^sub>B, 1)]"

lemma tps4': "tps4 = tps4'"
  using has2_def tps4_def tps4'_def by simp

lemma tm4' [transforms_intros]:
  assumes "ttt = 9 * length xs + 35"
  shows "transforms tm4 tps0 ttt tps4'"
  using assms tm4 tps4' by simp

definition tps5 :: "tape list" where
  "tps5 \<equiv> tps0
    [j1 := (\<lfloor>xs\<rfloor>, 1),
     j2 := (\<lfloor>has2 xs y z \<rfloor>\<^sub>B, 1)]"

lemma tm5:
  assumes "ttt = 10 * length xs + 38"
  shows "transforms tm5 tps0 ttt tps5"
  unfolding tm5_def
proof (tform tps: assms tps4'_def jk)
  show "clean_tape (tps4' ! j1)"
    using tps4'_def jk xs by simp
  have "tps4' ! j1 |#=| 1 = (\<lfloor>xs\<rfloor>, 1)"
    using tps4'_def jk by simp
  then show "tps5 = tps4'[j1 := tps4' ! j1 |#=| 1]"
    using tps5_def tps4'_def jk by (simp add: list_update_swap)
qed

definition tps5' :: "tape list" where
  "tps5' \<equiv> tps0
    [j2 := (\<lfloor>has2 xs y z\<rfloor>\<^sub>B, 1)]"

lemma tm5' [transforms_intros]:
  assumes "ttt = 10 * length xs + 38"
  shows "transforms tm5 tps0 ttt tps5'"
proof -
  have "tps5 = tps5'"
    using tps5_def tps5'_def jk tps0(1) by (metis list_update_id)
  then show ?thesis
    using assms tm5 by simp
qed

definition tps6 :: "tape list" where
  "tps6 \<equiv> tps0
    [j2 := (\<lfloor>\<not> has2 xs y z\<rfloor>\<^sub>B, 1)]"

lemma tm6:
  assumes "ttt = 10 * length xs + 41"
  shows "transforms tm6 tps0 ttt tps6"
  unfolding tm6_def
proof (tform tps: assms tps5'_def jk)
  have "tps5'[j2 := (\<lfloor>(if has2 xs y z then 1::nat else 0) \<noteq> 1\<rfloor>\<^sub>B, 1)] =
      tps5'[j2 := (\<lfloor>\<not> has2 xs y z\<rfloor>\<^sub>B, 1)]"
    by simp
  also have "... = tps0[j2 := (\<lfloor>\<not> has2 xs y z\<rfloor>\<^sub>B, 1)]"
    using tps5'_def by simp
  also have "... = tps6"
    using tps6_def by simp
  finally show "tps6 = tps5'
      [j2 := (\<lfloor>(if has2 xs y z then 1::nat else 0) \<noteq> 1\<rfloor>\<^sub>B, 1)]"
    by simp
qed

end  (* context *)

end  (* locale *)

lemma transforms_tm_not_has2I [transforms_intros]:
  fixes y z :: symbol and j1 j2 :: tapeidx
  fixes tps tps' :: "tape list" and xs :: "symbol list" and ttt k :: nat
  assumes "j1 < k" "j2 < k" "j1 \<noteq> j2" "0 < j2" "length tps = k" "y > 1" "z > 1"
    and "proper_symbols xs"
  assumes
    "tps ! j1 = (\<lfloor>xs\<rfloor>, 1)"
    "tps ! j2 = (\<lfloor>[]\<rfloor>, 1)"
  assumes "ttt = 10 * length xs + 41"
  assumes "tps' = tps
    [j2 := (\<lfloor>\<not> has2 xs y z\<rfloor>\<^sub>B, 1)]"
  shows "transforms (tm_not_has2 y z j1 j2) tps ttt tps'"
proof -
  interpret loc: turing_machine_has2 y z j1 j2 .
  show ?thesis
    using loc.tps6_def loc.tm6 loc.tm6_eq_tm_not_has2 assms by metis
qed


subsection \<open>Checking well-formedness for lists\<close>

text \<open>
The next Turing machine checks all conditions from the criterion in lemma @{thm
[source] numlist_wf_iff} one after another for the symbols on tape $j_1$ and
writes to tape $j_2$ either the number~1 or~0 depending on whether all
conditions were met. It assumes tape $j_2$ is initialized with~0.
\<close>

definition tm_numlist_wf :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_numlist_wf j1 j2 \<equiv>
     tm_proper_symbols_lt j1 j2 5 ;;
     tm_not_has2 \<zero> \<bar> j1 (j2 + 1) ;;
     tm_and j2 (j2 + 1) ;;
     tm_setn (j2 + 1) 0 ;;
     tm_empty_or_endswith j1 (j2 + 1) \<bar> ;;
     tm_and j2 (j2 + 1) ;;
     tm_setn (j2 + 1) 0"

lemma tm_numlist_wf_tm:
  assumes "k \<ge> 2" and "G \<ge> 5" and "0 < j2" "0 < j1" and "j1 < k" "j2 + 1 < k"
  shows "turing_machine k G (tm_numlist_wf j1 j2)"
  using tm_numlist_wf_def tm_proper_symbols_lt_tm tm_not_has2_tm tm_and_tm tm_setn_tm tm_empty_or_endswith_tm assms
  by simp

locale turing_machine_numlist_wf =
  fixes j1 j2 :: tapeidx
begin

definition "tm1 \<equiv> tm_proper_symbols_lt j1 j2 5"
definition "tm2 \<equiv> tm1 ;; tm_not_has2 \<zero> \<bar> j1 (j2 + 1)"
definition "tm3 \<equiv> tm2 ;; tm_and j2 (j2 + 1)"
definition "tm4 \<equiv> tm3 ;; tm_setn (j2 + 1) 0"
definition "tm5 \<equiv> tm4 ;; tm_empty_or_endswith j1 (j2 + 1) \<bar>"
definition "tm6 \<equiv> tm5 ;; tm_and j2 (j2 + 1)"
definition "tm7 \<equiv> tm6 ;; tm_setn (j2 + 1) 0"

lemma tm7_eq_tm_numlist_wf: "tm7 = tm_numlist_wf j1 j2"
  unfolding tm7_def tm6_def tm5_def tm4_def tm3_def tm2_def tm1_def tm_numlist_wf_def
  by simp

context
  fixes tps0 :: "tape list" and zs :: "symbol list" and k :: nat
  assumes zs: "proper_symbols zs"
  assumes jk: "0 < j1" "j1 < k" "j2 + 1 < k" "j1 \<noteq> j2" "0 < j2" "j1 \<noteq> j2 + 1" "length tps0 = k"
  assumes tps0:
    "tps0 ! j1 = (\<lfloor>zs\<rfloor>, 1)"
    "tps0 ! j2 = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j2 + 1) = (\<lfloor>[]\<rfloor>, 1)"
begin

definition "tps1 \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt 5 zs\<rfloor>\<^sub>B, 1)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = 5 + 7 * length zs"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
  by (tform tps: zs tps0 assms tps1_def jk)

definition "tps2 \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt 5 zs\<rfloor>\<^sub>B, 1),
   j2 + 1 := (\<lfloor>if has2 zs \<zero> \<bar> then 0 else 1\<rfloor>\<^sub>N, 1)]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 46 + 17 * length zs"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
  by (tform tps: zs tps0 assms tps1_def tps2_def jk)

definition "tps3 \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt 5 zs \<and> \<not> has2 zs \<zero> \<bar>\<rfloor>\<^sub>B, 1),
   j2 + 1 := (\<lfloor>if has2 zs \<zero> \<bar> then 0 else 1\<rfloor>\<^sub>N, 1)]"

lemma tm3 [transforms_intros]:
  assumes "ttt = 46 + 17 * length zs + 3"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def by (tform tps: assms tps2_def tps3_def jk)

definition "tps4 \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt 5 zs \<and> \<not> has2 zs \<zero> \<bar>\<rfloor>\<^sub>B, 1),
   j2 + 1 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"

lemma tm4:
  assumes "ttt = 46 + 17 * length zs + 13 + 2 * nlength (if has2 zs \<zero> \<bar> then 0 else 1)"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def by (tform tps: assms tps3_def tps4_def jk)

lemma tm4' [transforms_intros]:
  assumes "ttt = 46 + 17 * length zs + 15"
  shows "transforms tm4 tps0 ttt tps4"
  using assms nlength_0 nlength_1_simp tm4 transforms_monotone by simp

definition "tps5 \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt 5 zs \<and> \<not> has2 zs \<zero> \<bar>\<rfloor>\<^sub>B, 1),
   j2 + 1 := (\<lfloor>zs = [] \<or> last zs = \<bar>\<rfloor>\<^sub>B, 1)]"

lemma tm5 [transforms_intros]:
  assumes "ttt = 79 + 19 * length zs"
  shows "transforms tm5 tps0 ttt tps5"
  unfolding tm5_def by (tform tps: tps4_def tps5_def jk zs tps0 assms)

definition "tps6 \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt 5 zs \<and> \<not> has2 zs \<zero> \<bar> \<and> (zs = [] \<or> last zs = \<bar>)\<rfloor>\<^sub>B, 1),
   j2 + 1 := (\<lfloor>zs = [] \<or> last zs = \<bar>\<rfloor>\<^sub>B, 1)]"

lemma tm6 [transforms_intros]:
  assumes "ttt = 82 + 19 * length zs"
  shows "transforms tm6 tps0 ttt tps6"
  unfolding tm6_def by (tform tps: tps5_def tps6_def jk time: assms)

definition "tps7 \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt 5 zs \<and> \<not> has2 zs \<zero> \<bar> \<and> (zs = [] \<or> last zs = \<bar>)\<rfloor>\<^sub>B, 1),
   j2 + 1 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"

lemma tm7:
  assumes "ttt = 92 + 19 * length zs + 2 * nlength (if zs = [] \<or> last zs = \<bar> then 1 else 0)"
  shows "transforms tm7 tps0 ttt tps7"
  unfolding tm7_def by (tform tps: assms tps6_def tps7_def jk)

definition "tps7' \<equiv> tps0
  [j2 := (\<lfloor>numlist_wf zs\<rfloor>\<^sub>B, 1),
   j2 + 1 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"

lemma tm7':
  assumes "ttt = 94 + 19 * length zs"
  shows "transforms tm7 tps0 ttt tps7'"
proof -
  have "ttt \<ge> 92 + 19 * length zs + 2 * nlength (if zs = [] \<or> last zs = \<bar> then 1 else 0)"
    using assms nlength_1_simp by auto
  moreover have "tps7' = tps7"
    using tps7'_def tps7_def numlist_wf_iff by auto
  ultimately show ?thesis
   using transforms_monotone tm7 by simp
qed

definition "tps7'' \<equiv> tps0
  [j2 := (\<lfloor>numlist_wf zs\<rfloor>\<^sub>B, 1)]"

lemma tm7'' [transforms_intros]:
  assumes "ttt = 94 + 19 * length zs"
  shows "transforms tm7 tps0 ttt tps7''"
proof -
  have "tps7'' = tps7'"
    unfolding tps7''_def tps7'_def using tps0 jk canrepr_0
    by (metis add_gr_0 less_add_same_cancel1 list_update_id list_update_swap_less zero_less_two)
  then show ?thesis
    using tm7' assms by simp
qed

end  (* context *)

end  (* locale *)

lemma transforms_tm_numlist_wfI [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps tps' :: "tape list" and zs :: "symbol list" and ttt k :: nat
  assumes "0 < j1" "j1 < k" "j2 + 1 < k" "j1 \<noteq> j2" "0 < j2" "j1 \<noteq> j2 + 1" "length tps = k"
    and "proper_symbols zs"
  assumes
    "tps ! j1 = (\<lfloor>zs\<rfloor>, 1)"
    "tps ! j2 = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j2 + 1) = (\<lfloor>[]\<rfloor>, 1)"
  assumes "ttt = 94 + 19 * length zs"
  assumes "tps' = tps
    [j2 := (\<lfloor>numlist_wf zs\<rfloor>\<^sub>B, 1)]"
  shows "transforms (tm_numlist_wf j1 j2) tps ttt tps'"
proof -
  interpret loc: turing_machine_numlist_wf j1 j2 .
  show ?thesis
    using assms loc.tps7''_def loc.tm7'' loc.tm7_eq_tm_numlist_wf by simp
qed


subsection \<open>Checking well-formedness for lists of lists\<close>

text \<open>
The next Turing machine checks all conditions from the criterion in lemma @{thm
[source] numlistlist_wf_iff} one after another for the symbols on tape $j_1$ and
writes to tape $j_2$ either the number~1 or~0 depending on whether all
conditions were met. It assumes tape $j_2$ is initialized with~0.
\<close>

definition tm_numlistlist_wf :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_numlistlist_wf j1 j2 \<equiv>
     tm_proper_symbols_lt j1 j2 6 ;;
     tm_not_has2 \<zero> \<bar> j1 (j2 + 1) ;;
     tm_and j2 (j2 + 1) ;;
     tm_setn (j2 + 1) 0 ;;
     tm_empty_or_endswith j1 (j2 + 1) \<sharp> ;;
     tm_and j2 (j2 + 1) ;;
     tm_setn (j2 + 1) 0 ;;
     tm_not_has2 \<zero> \<sharp> j1 (j2 + 1) ;;
     tm_and j2 (j2 + 1) ;;
     tm_setn (j2 + 1) 0 ;;
     tm_not_has2 \<one> \<sharp> j1 (j2 + 1) ;;
     tm_and j2 (j2 + 1) ;;
     tm_setn (j2 + 1) 0"

lemma tm_numlistlist_wf_tm:
  assumes "k \<ge> 2" and "G \<ge> 6" and "0 < j2" "0 < j1" and "j1 < k" "j2 + 1 < k"
  shows "turing_machine k G (tm_numlistlist_wf j1 j2)"
  using tm_numlistlist_wf_def tm_proper_symbols_lt_tm tm_not_has2_tm tm_and_tm tm_setn_tm tm_empty_or_endswith_tm assms
  by simp

locale turing_machine_numlistlist_wf =
  fixes j1 j2 :: tapeidx
begin

definition "tm1 \<equiv> tm_proper_symbols_lt j1 j2 6"
definition "tm2 \<equiv> tm1 ;; tm_not_has2 \<zero> \<bar> j1 (j2 + 1)"
definition "tm3 \<equiv> tm2 ;; tm_and j2 (j2 + 1)"
definition "tm4 \<equiv> tm3 ;; tm_setn (j2 + 1) 0"
definition "tm5 \<equiv> tm4 ;; tm_empty_or_endswith j1 (j2 + 1) \<sharp>"
definition "tm6 \<equiv> tm5 ;; tm_and j2 (j2 + 1)"
definition "tm7 \<equiv> tm6 ;; tm_setn (j2 + 1) 0"
definition "tm8 \<equiv> tm7 ;; tm_not_has2 \<zero> \<sharp> j1 (j2 + 1)"
definition "tm9 \<equiv> tm8 ;; tm_and j2 (j2 + 1)"
definition "tm10 \<equiv> tm9 ;; tm_setn (j2 + 1) 0"
definition "tm11 \<equiv> tm10 ;; tm_not_has2 \<one> \<sharp> j1 (j2 + 1)"
definition "tm12 \<equiv> tm11 ;; tm_and j2 (j2 + 1)"
definition "tm13 \<equiv> tm12 ;; tm_setn (j2 + 1) 0"

lemma tm13_eq_tm_numlistlist_wf: "tm13 = tm_numlistlist_wf j1 j2"
  unfolding tm13_def tm12_def tm11_def tm10_def tm9_def tm8_def tm7_def tm6_def tm5_def
    tm4_def tm3_def tm2_def tm1_def tm_numlistlist_wf_def
  by simp

context
  fixes tps0 :: "tape list" and zs :: "symbol list" and k :: nat
  assumes zs: "proper_symbols zs"
  assumes jk: "0 < j1" "j1 < k" "j2 + 1 < k" "j1 \<noteq> j2" "0 < j2" "j1 \<noteq> j2 + 1" "length tps0 = k"
  assumes tps0:
    "tps0 ! j1 = (\<lfloor>zs\<rfloor>, 1)"
    "tps0 ! j2 = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j2 + 1) = (\<lfloor>[]\<rfloor>, 1)"
begin

definition "tps1 \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt 6 zs\<rfloor>\<^sub>B, 1)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = 5 + 7 * length zs"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def by (tform tps: tps0 tps1_def zs jk time: assms)

definition "tps2 \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt 6 zs\<rfloor>\<^sub>B, 1),
   j2 + 1 := (\<lfloor>if has2 zs \<zero> \<bar> then 0 else 1\<rfloor>\<^sub>N, 1)]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 46 + 17 * length zs"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def by (tform tps: zs tps0 assms tps1_def tps2_def jk)

definition "tps3 \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt 6 zs \<and> \<not> has2 zs \<zero> \<bar>\<rfloor>\<^sub>B, 1),
   j2 + 1 := (\<lfloor>if has2 zs \<zero> \<bar> then 0 else 1\<rfloor>\<^sub>N, 1)]"

lemma tm3 [transforms_intros]:
  assumes "ttt = 46 + 17 * length zs + 3"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def by (tform tps: tps2_def tps3_def jk time: assms)

definition "tps4 \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt 6 zs \<and> \<not> has2 zs \<zero> \<bar>\<rfloor>\<^sub>B, 1),
   j2 + 1 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"

lemma tm4:
  assumes "ttt = 46 + 17 * length zs + 13 + 2 * nlength (if has2 zs \<zero> \<bar> then 0 else 1)"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def by (tform tps: tps3_def assms tps4_def jk)

lemma tm4' [transforms_intros]:
  assumes "ttt = 46 + 17 * length zs + 15"
  shows "transforms tm4 tps0 ttt tps4"
  using assms nlength_0 nlength_1_simp tm4 transforms_monotone by simp

definition "tps5 \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt 6 zs \<and> \<not> has2 zs \<zero> \<bar>\<rfloor>\<^sub>B, 1),
   j2 + 1 := (\<lfloor>zs = [] \<or> last zs = \<sharp>\<rfloor>\<^sub>B, 1)]"

lemma tm5 [transforms_intros]:
  assumes "ttt = 79 + 19 * length zs"
  shows "transforms tm5 tps0 ttt tps5"
  unfolding tm5_def by (tform tps: tps0 tps4_def tps5_def jk zs time: assms)

definition "tps6 \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt 6 zs \<and> \<not> has2 zs \<zero> \<bar> \<and> (zs = [] \<or> last zs = \<sharp>)\<rfloor>\<^sub>B, 1),
   j2 + 1 := (\<lfloor>zs = [] \<or> last zs = \<sharp>\<rfloor>\<^sub>B, 1)]"

lemma tm6 [transforms_intros]:
  assumes "ttt = 82 + 19 * length zs"
  shows "transforms tm6 tps0 ttt tps6"
  unfolding tm6_def by (tform tps: tps5_def tps6_def jk time: assms)

definition "tps7 \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt 6 zs \<and> \<not> has2 zs \<zero> \<bar> \<and> (zs = [] \<or> last zs = \<sharp>)\<rfloor>\<^sub>B, 1),
   j2 + 1 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"

lemma tm7:
  assumes "ttt = 92 + 19 * length zs + 2 * nlength (if zs = [] \<or> last zs = \<sharp> then 1 else 0)"
  shows "transforms tm7 tps0 ttt tps7"
  unfolding tm7_def by (tform tps: assms tps6_def tps7_def jk)

lemma tm7' [transforms_intros]:
  assumes "ttt = 94 + 19 * length zs"
  shows "transforms tm7 tps0 ttt tps7"
  using transforms_monotone tm7 nlength_1_simp assms by simp

definition "tps8 \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt 6 zs \<and> \<not> has2 zs \<zero> \<bar> \<and> (zs = [] \<or> last zs = \<sharp>)\<rfloor>\<^sub>B, 1),
   j2 + 1 := (\<lfloor>if has2 zs \<zero> \<sharp> then 0 else 1\<rfloor>\<^sub>N, 1)]"

lemma tm8 [transforms_intros]:
  assumes "ttt = 135 + 29 * length zs"
  shows "transforms tm8 tps0 ttt tps8"
  unfolding tm8_def by (tform tps: canrepr_0 zs tps0 assms tps7_def tps8_def jk)

definition "tps9 \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt 6 zs \<and> \<not> has2 zs \<zero> \<bar> \<and> (zs = [] \<or> last zs = \<sharp>) \<and> \<not> has2 zs \<zero> \<sharp>\<rfloor>\<^sub>B, 1),
   j2 + 1 := (\<lfloor>if has2 zs \<zero> \<sharp> then 0 else 1\<rfloor>\<^sub>N, 1)]"

lemma tm9 [transforms_intros]:
  assumes "ttt = 138 + 29 * length zs"
  shows "transforms tm9 tps0 ttt tps9"
  unfolding tm9_def by (tform tps: tps8_def tps9_def jk time: assms)

definition "tps10 \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt 6 zs \<and> \<not> has2 zs \<zero> \<bar> \<and> (zs = [] \<or> last zs = \<sharp>) \<and> \<not> has2 zs \<zero> \<sharp>\<rfloor>\<^sub>B, 1),
   j2 + 1 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"

lemma tm10:
  assumes "ttt = 148 + 29 * length zs + 2 * nlength (if has2 zs \<zero> \<sharp> then 0 else 1)"
  shows "transforms tm10 tps0 ttt tps10"
  unfolding tm10_def by (tform tps: assms tps9_def tps10_def jk)

lemma tm10' [transforms_intros]:
  assumes "ttt = 150 + 29 * length zs"
  shows "transforms tm10 tps0 ttt tps10"
  using transforms_monotone tm10 nlength_1_simp assms by simp

definition "tps11 \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt 6 zs \<and> \<not> has2 zs \<zero> \<bar> \<and> (zs = [] \<or> last zs = \<sharp>) \<and> \<not> has2 zs \<zero> \<sharp>\<rfloor>\<^sub>B, 1),
   j2 + 1 := (\<lfloor>if has2 zs \<one> \<sharp> then 0 else 1\<rfloor>\<^sub>N, 1)]"

lemma tm11 [transforms_intros]:
  assumes "ttt = 191 + 39 * length zs"
  shows "transforms tm11 tps0 ttt tps11"
  unfolding tm11_def by (tform tps: canrepr_0 zs tps0 assms tps10_def tps11_def jk)

definition "tps12 \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt 6 zs \<and> \<not> has2 zs \<zero> \<bar> \<and> (zs = [] \<or> last zs = \<sharp>) \<and> \<not> has2 zs \<zero> \<sharp> \<and> \<not> has2 zs \<one> \<sharp>\<rfloor>\<^sub>B, 1),
   j2 + 1 := (\<lfloor>if has2 zs \<one> \<sharp> then 0 else 1\<rfloor>\<^sub>N, 1)]"

lemma tm12 [transforms_intros]:
  assumes "ttt = 194 + 39 * length zs"
  shows "transforms tm12 tps0 ttt tps12"
  unfolding tm12_def by (tform tps: assms tps11_def tps12_def jk)

definition "tps13 \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt 6 zs \<and> \<not> has2 zs \<zero> \<bar> \<and> (zs = [] \<or> last zs = \<sharp>) \<and> \<not> has2 zs \<zero> \<sharp> \<and> \<not> has2 zs \<one> \<sharp>\<rfloor>\<^sub>B, 1),
   j2 + 1 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"

lemma tm13:
  assumes "ttt = 204 + 39 * length zs + 2 * nlength (if has2 zs \<one> \<sharp> then 0 else 1)"
  shows "transforms tm13 tps0 ttt tps13"
  unfolding tm13_def by (tform tps: assms tps12_def tps13_def jk)

lemma tm13':
  assumes "ttt = 206 + 39 * length zs"
  shows "transforms tm13 tps0 ttt tps13"
  using transforms_monotone tm13 nlength_1_simp assms by simp

definition "tps13' \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt 6 zs \<and> \<not> has2 zs \<zero> \<bar> \<and> (zs = [] \<or> last zs = \<sharp>) \<and> \<not> has2 zs \<zero> \<sharp> \<and> \<not> has2 zs \<one> \<sharp>\<rfloor>\<^sub>B, 1)]"

lemma tm13'':
  assumes "ttt = 206 + 39 * length zs"
  shows "transforms tm13 tps0 ttt tps13'"
proof -
  have "tps13' = tps13"
    unfolding tps13'_def tps13_def
    using tps0(3) jk canrepr_0 list_update_id[of tps0 "Suc j2"]
    by (simp add: list_update_swap)
  then show ?thesis
    using tm13' assms by simp
qed

definition "tps13'' \<equiv> tps0
  [j2 := (\<lfloor>numlistlist_wf zs\<rfloor>\<^sub>B, 1)]"

lemma tm13''':
  assumes "ttt = 206 + 39 * length zs"
  shows "transforms tm13 tps0 ttt tps13''"
proof -
  have "tps13'' = tps13'"
    using numlistlist_wf_iff tps13''_def tps13'_def by auto
  then show ?thesis
    using assms tm13'' numlistlist_wf_iff by simp
qed

end  (* context *)

end  (* locale *)

lemma transforms_tm_numlistlist_wfI [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps tps' :: "tape list" and zs :: "symbol list" and ttt k :: nat
  assumes "0 < j1" "j1 < k" "j2 + 1 < k" "j1 \<noteq> j2" "0 < j2" "j1 \<noteq> j2 + 1" "length tps = k"
    and "proper_symbols zs"
  assumes
    "tps ! j1 = (\<lfloor>zs\<rfloor>, 1)"
    "tps ! j2 = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j2 + 1) = (\<lfloor>[]\<rfloor>, 1)"
  assumes "ttt = 206 + 39 * length zs"
  assumes "tps' = tps
    [j2 := (\<lfloor>numlistlist_wf zs\<rfloor>\<^sub>B, 1)]"
  shows "transforms (tm_numlistlist_wf j1 j2) tps ttt tps'"
proof -
  interpret loc: turing_machine_numlistlist_wf j1 j2 .
  show ?thesis
    using assms loc.tps13''_def loc.tm13''' loc.tm13_eq_tm_numlistlist_wf by simp
qed

end
