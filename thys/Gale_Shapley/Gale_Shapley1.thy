(*
Stepwise refinement of the Gale-Shapley algorithm down to executable functional code.

Author: Tobias Nipkow
*)

section "Part 1: Refinement down to lists"

theory Gale_Shapley1
imports Main
  "HOL-Hoare.Hoare_Logic"
  "List-Index.List_Index"
  "HOL-Library.While_Combinator"
  "HOL-Library.LaTeXsugar"
begin

subsection \<open>Misc\<close>

lemmas conj12 = conjunct1 conjunct2

syntax
  "_assign_list" :: "idt \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> 'com"  ("(2_[_] :=/ _)" [70, 0, 65] 61)

translations
  "xs[n] := e" \<rightharpoonup> "xs := CONST list_update xs n e"

abbreviation upt_set :: "nat \<Rightarrow> nat set" ("{<_}") where
"{<n} \<equiv> {0..<n}"

(* Maybe also require y : set P? *)
definition prefers :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"prefers P x y = (index P x < index P y)"

abbreviation prefa :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("(_ \<turnstile>/ _ < _)" [50,50,50] 50) where
"P \<turnstile> x < y \<equiv> prefers P x y"

lemma prefers_asym: "P \<turnstile> x < y \<Longrightarrow> \<not> P \<turnstile> y < x"
by(simp add: prefers_def)

lemma prefers_trans: "P \<turnstile> x < y \<Longrightarrow> P \<turnstile> y < z \<Longrightarrow> P \<turnstile> x < z"
by (meson order_less_trans prefers_def)

fun rk_of_pref :: "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
"rk_of_pref r rs (n#ns) = (rk_of_pref (r+1) rs ns)[n := r]" |
"rk_of_pref r rs [] = rs"

definition ranking :: "nat list \<Rightarrow> nat list" where
"ranking P = rk_of_pref 0 (replicate (length P) 0) P"

lemma length_rk_of_pref[simp]: "length(rk_of_pref v vs P) = length vs"
by(induction P arbitrary: v)(auto)

lemma nth_rk_of_pref: "\<lbrakk> length P \<le> length rs; i \<in> set P; distinct P; set P \<subseteq> {<length rs} \<rbrakk>
 \<Longrightarrow> rk_of_pref r rs P ! i = index P i + r"
by(induction P arbitrary: r i) (auto simp add: nth_list_update)

lemma ranking_index: "\<lbrakk> length P = n; set P = {<n} \<rbrakk> \<Longrightarrow> ranking P = map (index P) [0..<length P]"
by(simp add: list_eq_iff_nth_eq ranking_def card_distinct nth_rk_of_pref)

lemma ranking_iff_pref:  "\<lbrakk> set P = {<length P}; i < length P; j < length P \<rbrakk>
 \<Longrightarrow> ranking P ! i < ranking P ! j \<longleftrightarrow> P \<turnstile> i < j"
by(simp add: ranking_index prefers_def)


subsection \<open>Fixing the preference lists\<close>
 
type_synonym prefs = "nat list list"

locale Pref =
fixes n
fixes P :: prefs
fixes Q :: prefs
defines "n \<equiv> length P"
assumes length_Q: "length Q = n"
assumes P_set: "a < n  \<Longrightarrow> length(P!a) = n \<and> set(P!a) = {<n}"
assumes Q_set: "b < n \<Longrightarrow> length(Q!b) = n \<and> set(Q!b) = {<n}"
begin


abbreviation wf :: "nat list \<Rightarrow> bool" where
"wf xs \<equiv> length xs = n \<and> set xs \<subseteq> {<n}"

lemma wf_less_n: "\<lbrakk> wf A; a < n \<rbrakk> \<Longrightarrow> A!a < n"
by (simp add: subset_eq)

corollary wf_le_n1: "\<lbrakk> wf A; a < n \<rbrakk> \<Longrightarrow> A!a \<le> n-1"
using wf_less_n by fastforce

lemma sumA_ub: "wf A \<Longrightarrow> (\<Sum>a<n. A!a) \<le> n*(n-1)"
using sum_bounded_above[of "{..<n}" "((!) A)" "n-1"] wf_le_n1[of A] by (simp)


subsection \<open>The (termination) variant(s)\<close>

text \<open>Basic idea: either some \<open>A!a\<close> is incremented or size of \<open>M\<close> is incremented, but this cannot
go on forever because in the worst case all \<open>A!a = n-1\<close> and \<open>M = n\<close>. Because \<open>n*(n-1) + n = n^2\<close>,
this leads to the following simple variant:\<close>

definition var0 :: "nat list \<Rightarrow> nat set \<Rightarrow> nat" where
[simp]: "var0 A M = (n^2 - ((\<Sum>a<n. A!a) + card M))"

lemma var0_match:
assumes "wf A" "M \<subseteq> {<n}" "a < n \<and> a \<notin> M"
shows "var0 A (M \<union> {a}) < var0 A M"
proof -
  have 2: "M \<subset> {<n}" using assms(2-3) by auto
  have 3: "card M < n" using psubset_card_mono[OF _ 2] by simp
  then show ?thesis
    using sumA_ub[OF assms(1)] assms(3) finite_subset[OF assms(2)]
    by (simp add: power2_eq_square algebra_simps le_diff_conv2)
qed

lemma var0_next:
assumes "wf A" "M \<subseteq> {<n}" "M \<noteq> {<n}" "a' < n"
shows "var0 (A[a' := A ! a' + 1]) M < var0 A M"
proof -
  have 0: "card M < n" using assms(2,3)
    by (metis atLeast0LessThan card_lessThan card_subset_eq finite_lessThan lessThan_iff nat_less_le
              subset_eq_atLeast0_lessThan_card)
  have *: "1 + (\<Sum>a<n. A!a) + card M \<le> n*n"
    using sumA_ub[OF assms(1)] 0 by (simp add: algebra_simps le_diff_conv2)
  have "var0 (A[a' := A ! a' + 1]) M = n*n - (1 + (A ! a' + sum ((!) A) ({<n} - {a'})) + card M)"
    using assms by(simp add: power2_eq_square nth_list_update sum.If_cases lessThan_atLeast0 flip:Diff_eq)
  also have "\<dots> = n^2 - (1 + (\<Sum>a<n. A!a) + card M)"
    using sum.insert_remove[of "{<n}" "nth A" a',simplified,symmetric] assms(4)
    by (simp add:insert_absorb lessThan_atLeast0 power2_eq_square)
  also have "\<dots> < n^2 - ((\<Sum>a<n. A!a) + card M)" unfolding power2_eq_square using * by linarith
  finally show ?thesis unfolding var0_def .
qed

definition var :: "nat list \<Rightarrow> nat set \<Rightarrow> nat" where
[simp]: "var A M = (n^2 - n + 1 - ((\<Sum>a<n. A!a) + card M))"

lemma sumA_ub2:
assumes "a' < n" "A!a' \<le> n-1" "\<forall>a < n. a \<noteq> a' \<longrightarrow> A!a \<le> n-2"
shows "(\<Sum>a<n. A!a) \<le> (n-1)*(n-1)"
proof -
  have "(\<Sum>a<n. A!a) = (\<Sum>a \<in> ({<n}-{a'}) \<union> {a'}. A!a)"
    by (simp add: assms(1) atLeast0LessThan insert_absorb)
  also have "\<dots> =(\<Sum>a \<in> {<n}-{a'}. A!a) + A!a'"
    by (simp add: sum.insert_remove)
  also have "\<dots> \<le> (\<Sum>a \<in> {<n}-{a'}. A!a) + (n-1)" using assms(2) by linarith
  also have "\<dots> \<le> (n-1)*(n-2) + (n-1)"
    using sum_bounded_above[of "{..<n}-{a'}" "((!) A)" "n-2"] assms(1,3)
    by (simp add: atLeast0LessThan)
  also have "\<dots> = (n-1)*(n-1)"
    by (metis Suc_diff_Suc Suc_eq_plus1 add.commute diff_is_0_eq' linorder_not_le mult_Suc_right mult_cancel_left nat_1_add_1)
  finally show ?thesis .
qed

definition "match A a = P ! a ! (A ! a)"

lemma match_less_n: "\<lbrakk> wf A; a < n \<rbrakk> \<Longrightarrow> match A a < n"
by (metis P_set atLeastLessThan_iff match_def nth_mem subset_eq)

lemma match_upd_neq: "\<lbrakk> wf A; a < n; a \<noteq> a' \<rbrakk> \<Longrightarrow> match (A[a := b]) a' = match A a'"
by (simp add: match_def)

definition stable :: "nat list \<Rightarrow> nat set \<Rightarrow> bool" where
"stable A M = (\<not>(\<exists>a\<in>M. \<exists>a'\<in>M. P ! a \<turnstile> match A a' < match A a \<and> Q ! match A a' \<turnstile> a < a'))"

text \<open>The set of Bs that an A would prefer to its current match,
i.e. all Bs above its current match \<open>A!a\<close>.\<close>
abbreviation preferred where
"preferred A a == nth (P!a) ` {<A!a}"

definition matching where [simp]:
"matching A M = (wf A \<and> inj_on (match A) M)"


text \<open>If \<open>a'\<close> is unmatched and final then all other \<open>a\<close> are matched:\<close>

lemma final_last:
assumes M: "M \<subseteq> {<n}" and inj: "inj_on (match A) M" and pref_match': "preferred A a \<subseteq> match A ` M"
and a: "a < n \<and> a \<notin> M" and final: "A ! a + 1 = n"
shows "insert a M = {<n}"
proof -
  let ?B = "preferred A a"
  have "(!) (P ! a) ` {<n} = {<n}" by (metis P_set a map_nth set_map set_upt)
  hence "inj_on ((!) (P ! a)) {<n}" by(simp add: eq_card_imp_inj_on)
  hence "inj_on ((!) (P ! a)) {<A!a}" using final by(simp add: subset_inj_on)
  hence 1: "Suc(card ?B) = n" using final by (simp add: card_image)
  have 2: "card ?B \<le> card M"
    by(rule surj_card_le[OF subset_eq_atLeast0_lessThan_finite[OF M] pref_match'])
  have 3: "card M < n" using M a
    by (metis atLeast0LessThan card_seteq order.refl finite_atLeastLessThan le_neq_implies_less lessThan_iff subset_eq_atLeast0_lessThan_card)
  have "Suc (card M) = n" using 1 2 3 by simp
  thus ?thesis using M a by (simp add: card_subset_eq finite_subset)
qed

lemma more_choices:
assumes A: "wf A" and M: "M \<subseteq> {<n}" "M \<noteq> {<n}"
and pref_match': "preferred A a \<subseteq> match A ` M"
and "a < n" and matched: "match A a \<in> match A ` M"
shows "A ! a + 1 < n"
proof (rule ccontr)
  assume "\<not> A ! a + 1 < n"
  hence "A ! a + 1 = n" using A \<open>a < n\<close> unfolding matching_def
    by (metis add.commute wf_less_n linorder_neqE_nat not_less_eq plus_1_eq_Suc)
  hence *: "nth (P ! a) ` {<n} \<subseteq> match A ` M"
    using pref_match' matched less_Suc_eq match_def by fastforce
  have "nth (P!a) ` {<n} = {<n}"
    using P_set[OF  \<open>a < n\<close>] by (metis map_nth set_map set_upt)
  hence "{<n} \<subseteq> match A ` M" using * by metis
  hence "card {<n} \<le> card M"
    using finite_subset[OF \<open>M \<subseteq> {<n}\<close> finite_atLeastLessThan] by (metis surj_card_le)
  then show False using M card_seteq by blast
qed

corollary more_choices_matched:
assumes "wf A" "M \<subseteq> {<n}" "M \<noteq> {<n}"
and "preferred A a \<subseteq> match A ` M" and "a \<in> M"
shows "A ! a + 1 < n"
using more_choices[OF assms(1-4)] \<open>a \<in> M\<close> \<open>M \<subseteq> {<n}\<close> atLeastLessThan_iff by blast

lemma atmost1_final: assumes M: "M \<subseteq> {<n}" and inj: "inj_on (match A) M"
and "\<forall>a<n. preferred A a \<subseteq> match A ` M"
shows "\<exists>\<^sub>\<le>\<^sub>1 a. a < n \<and> a \<notin> M \<and> A ! a + 1 = n"
apply rule
subgoal for x y
using final_last[OF M inj, of x] final_last[OF M inj, of y] assms(3) by blast
done

lemma sumA_UB:
assumes "matching A M" "M \<subseteq> {<n}" "M \<noteq> {<n}" "\<forall>a<n. preferred A a \<subseteq> match A ` M"
shows "(\<Sum>a<n. A!a) \<le> (n-1)^2"
proof -
  have "wf A" using assms(1) by(simp)
  have M: "\<forall>a\<in>M. A!a + 1 < n" using more_choices_matched[OF \<open>wf A\<close> assms(2-3)] assms(4)
    \<open>M \<subseteq> {<n}\<close> atLeastLessThan_iff by blast
  note Ainj = conj12[OF assms(1)[unfolded matching_def]]
  show ?thesis
  proof (cases "\<exists>a'<n. a' \<notin> M \<and> A!a' + 1 = n")
    case True
    then obtain a' where a': "a'<n" "a' \<notin> M" "A!a' + 1 = n" using \<open>M \<subseteq> {<n}\<close> \<open>M \<noteq> {<n}\<close> by blast
    hence "\<forall>a<n. a \<noteq> a' \<longrightarrow> A!a \<le> n-2"
      using Uniq_D[OF atmost1_final[OF assms(2) Ainj(2) assms(4)], of a'] M wf_le_n1[OF Ainj(1)]
      by (metis Suc_1 Suc_eq_plus1 add_diff_cancel_right' add_le_imp_le_diff diff_diff_left less_eq_Suc_le order_less_le)
    from sumA_ub2[OF a'(1) _ this] a'(3) show ?thesis unfolding power2_eq_square by linarith
  next
    case False
    hence "\<forall>a'<n. a' \<notin> M \<longrightarrow> A ! a' + 1 < n"
      by (metis Suc_eq_plus1 Suc_lessI wf_less_n[OF Ainj(1)])
    with M have "\<forall>a<n. A ! a + 1 < n" by blast
    hence "(\<Sum>a<n. A!a) \<le> n*(n-2)" using sum_bounded_above[of "{..<n}" "((!) A)" "n-2"] by fastforce
    also have "\<dots> \<le> (n-1)*(n-1)" by(simp add: algebra_simps)
    finally show ?thesis unfolding power2_eq_square .
  qed
qed

lemma var_ub:
assumes "matching A M" "M \<subseteq> {<n}" "M \<noteq> {<n}" "\<forall>a<n. preferred A a \<subseteq> match A ` M"
shows "(\<Sum>a<n. A!a) + card M  < n^2 - n + 1"
proof -
  have 1: "M \<subset> {<n}" using assms(2,3) by auto
  have 2: "card M < n" using psubset_card_mono[OF _ 1] by simp
  have 3: "sum ((!) A) {..<n} \<le> n^2 + 1 - 2*n"
    using sumA_UB[OF assms(1-4)]  by (simp add: power2_eq_square algebra_simps)
  have 4: "2*n \<le> Suc (n^2)" using le_square[of n] unfolding power2_eq_square
    by (metis Suc_1 add_mono_thms_linordered_semiring(1) le_SucI mult_2 mult_le_mono1 not_less_eq_eq plus_1_eq_Suc)
  show "(\<Sum>a<n. A!a) + card M  < n^2 - n + 1" using 2 3 4 by linarith
qed

lemma var_match:
assumes "matching A M" "M \<subseteq> {<n}" "M \<noteq> {<n}" "\<forall>a<n. preferred A a \<subseteq> match A ` M" "a \<notin> M"
shows "var A (M \<union> {a}) < var A M"
proof -
  have 2: "M \<subset> {<n}" using assms(2,3) by auto
  have 3: "card M < n" using psubset_card_mono[OF _ 2] by simp
  have 4: "sum ((!) A) {..<n} \<le> n^2 + 1 - 2*n"
    using sumA_UB[OF assms(1-4)]  by (simp add: power2_eq_square algebra_simps)
  have 5: "2*n \<le> Suc (n^2)" using le_square[of n] unfolding power2_eq_square
    by (metis Suc_1 add_mono_thms_linordered_semiring(1) le_SucI mult_2 mult_le_mono1 not_less_eq_eq plus_1_eq_Suc)
  have 6: "(\<Sum>a<n. A!a) + card M  < n^2 + 1 - n" using 3 4 5 by linarith
  from var_ub[OF assms(1-4)] show ?thesis using \<open>a \<notin> M\<close> finite_subset[OF assms(2)] by(simp)
qed

lemma var_next:
assumes"matching A M" "M \<subseteq> {<n}" "M \<noteq> {<n}" "\<forall>a<n. preferred A a \<subseteq> match A ` M"
 "a < n"
shows "var (A[a := A ! a + 1]) M < var A M"
proof -
  have "var (A[a := A ! a + 1]) M = n*n - n + 1 - (1 + (A ! a + sum ((!) A) ({<n} - {a})) + card M)"
    using assms(1,5) by(simp add: power2_eq_square nth_list_update sum.If_cases lessThan_atLeast0 flip:Diff_eq)
  also have "\<dots> = n^2 - n + 1 - (1 + (\<Sum>a<n. A!a) + card M)"
    using sum.insert_remove[of "{<n}" "nth A" a,simplified,symmetric] assms(5)
    by (simp add:insert_absorb lessThan_atLeast0 power2_eq_square)
  also have "\<dots> < n^2 - n + 1 - ((\<Sum>a<n. A!a) + card M)" using var_ub[OF assms(1-4)] unfolding power2_eq_square
    by linarith
  finally show ?thesis unfolding var_def .
qed


subsection \<open>Auxiliary Predicates\<close>

text \<open>The following two predicates express the same property:
if \<open>a\<close> prefers \<open>b\<close> over \<open>a\<close>'s current match,
then \<open>b\<close> is matched with an \<open>a'\<close> that \<open>b\<close> prefers to \<open>a\<close>.\<close>

definition pref_match where
"pref_match A M = (\<forall>a<n. \<forall>b<n. P!a \<turnstile> b < match A a \<longrightarrow> (\<exists>a'\<in>M. b = match A a' \<and> Q ! b \<turnstile> a' < a))"

definition pref_match' where
"pref_match' A M = (\<forall>a<n. \<forall>b \<in> preferred A a. \<exists>a'\<in>M. b = match A a' \<and> Q ! b \<turnstile> a' < a)"

lemma pref_match'_iff: "wf A \<Longrightarrow> pref_match' A M = pref_match A M"
apply (auto simp add: pref_match'_def pref_match_def imp_ex prefers_def match_def)
  apply (smt (verit) P_set atLeast0LessThan order.strict_trans index_first lessThan_iff linorder_neqE_nat nth_index)
  by (smt (verit, best) P_set atLeast0LessThan card_atLeastLessThan card_distinct diff_zero in_mono index_nth_id lessThan_iff less_trans nth_mem)

definition opti\<^sub>a where
"opti\<^sub>a A = (\<nexists>A'. matching A' {<n} \<and> stable A' {<n} \<and>
                (\<exists>a<n. P ! a \<turnstile> match A' a < match A a))"

definition pessi\<^sub>b where
"pessi\<^sub>b A = (\<nexists>A'. matching A' {<n} \<and> stable A' {<n} \<and>
                 (\<exists>a<n. \<exists>a'<n. match A a = match A' a' \<and> Q ! match A a \<turnstile> a < a'))"

lemma opti\<^sub>a_pessi\<^sub>b: assumes "opti\<^sub>a A" shows "pessi\<^sub>b A"
unfolding pessi\<^sub>b_def
proof (safe, goal_cases)
  case (1 A' a a')
  have "\<not> P!a \<turnstile>  match A a <  match A' a" using 1
    by (metis atLeast0LessThan lessThan_iff stable_def)
  with 1 \<open>opti\<^sub>a A\<close> show ?case using P_set match_less_n opti\<^sub>a_def prefers_def unfolding matching_def
    by (metis (no_types) atLeast0LessThan inj_on_contraD lessThan_iff less_not_refl linorder_neqE_nat nth_index)
qed

lemma opti\<^sub>a_inv:
assumes A: "wf A" and a: "a < n" and a': "a' < n" and same_match: "match A a' = match A a"
and pref: "Q ! match A a' \<turnstile> a' < a" and "opti\<^sub>a A"
shows "opti\<^sub>a (A[a := A ! a + 1])"
proof (unfold opti\<^sub>a_def matching_def, rule notI, elim exE conjE)
  note opti\<^sub>a = \<open>opti\<^sub>a A\<close>[unfolded opti\<^sub>a_def matching_def]
  let ?A = "A[a := A ! a + 1]"
  fix A' a''
  assume "a'' < n" and A': "length A' = n" "set A' \<subseteq> {<n}" "stable A' {<n}" "inj_on (match A') {<n}"
  and pref_a'': "P ! a'' \<turnstile> match A' a'' < match ?A a''"
  show False
  proof cases
    assume [simp]: "a'' = a"
    have "A!a < n" using A a by(simp add: subset_eq)
    with A A' a pref_a'' have "P ! a \<turnstile> match A' a < match A a \<or> match A' a = match A a"
      apply(auto simp: prefers_def match_def)
      by (smt (verit) P_set wf_less_n card_atLeastLessThan card_distinct diff_zero index_nth_id
              not_less_eq not_less_less_Suc_eq)
    thus False
    proof
      assume "P ! a \<turnstile> match A' a < match A a " thus False using opti\<^sub>a A' \<open>a < n\<close> by(fastforce) 
    next
      assume "match A' a = match A a"
      have "a \<noteq> a'" using pref a' by(auto simp: prefers_def)
      hence "P ! a' \<turnstile> match A' a < match A' a' \<and> Q ! match A' a \<turnstile> a' < a" using opti\<^sub>a pref A' same_match \<open>match A' a = match A a\<close> a a'
        by (metis P_set atLeast0LessThan match_less_n inj_onD lessThan_iff linorder_neqE_nat nth_index prefers_def)
      thus False using a a' \<open>a \<noteq> a'\<close> A'(3) by (metis stable_def atLeastLessThan_iff zero_le)
    qed
  next
    assume "a'' \<noteq> a" thus False using opti\<^sub>a A' pref_a'' \<open>a'' < n\<close> by(metis match_def nth_list_update_neq)
  qed
qed

lemma pref_match_stable:
  "\<lbrakk> matching A {<n}; pref_match A {<n} \<rbrakk> \<Longrightarrow> stable A {<n}"
unfolding pref_match_def stable_def matching_def
by (metis atLeast0LessThan match_less_n inj_onD lessThan_iff prefers_asym)


subsection \<open>Algorithm 1\<close>

definition invAM where
[simp]: "invAM A M = (matching A M \<and> M \<subseteq> {<n} \<and> pref_match A M \<and> opti\<^sub>a A)"

lemma invAM_match:
  "\<lbrakk> invAM A M;  a < n \<and> a \<notin> M;  match A a \<notin> match A ` M \<rbrakk> \<Longrightarrow> invAM A (M \<union> {a})"
by(simp add: pref_match_def)

lemma invAM_swap:
assumes "invAM A M"
assumes a: "a < n \<and> a \<notin> M" and a': "a' \<in> M \<and> match A a' = match A a" and pref: "Q ! match A a' \<turnstile> a < a'"
shows "invAM (A[a' := A!a'+1]) (M - {a'} \<union> {a})"
proof -
  have A: "wf A" and M : "M \<subseteq> {<n}" and inj: "inj_on (match A) M" and pref_match: "pref_match A M"
  and "opti\<^sub>a A" by(insert \<open>invAM A M\<close>) (auto)
  have "M \<noteq> {<n}" "a' < n" "a \<noteq> a'" using a' a M by auto
  have pref_match': "pref_match' A M" using pref_match pref_match'_iff[OF A] by blast
  let ?A = "A[a' := A!a'+1]" let ?M = "M - {a'} \<union> {a}"
  have neq_a': "\<forall>x. x \<in> ?M \<longrightarrow> a' \<noteq> x" using \<open>a \<noteq> a'\<close> by blast
  have \<open>set ?A \<subseteq> {<n}\<close>
    apply(rule set_update_subsetI[OF A[THEN conjunct2]])
    using more_choices[OF _ M \<open>M \<noteq> {<n}\<close>] A inj pref_match' a' subsetD[OF M, of a']
    by(fastforce simp: pref_match'_def)
  hence "wf ?A" using A by(simp)
  moreover have "inj_on (match ?A) ?M" using a a' inj
    by(simp add: match_def inj_on_def)(metis Diff_iff insert_iff nth_list_update_neq)
  moreover have "pref_match' ?A ?M" using a a' pref_match' A pref \<open>a' < n\<close>
    apply(simp add: pref_match'_def match_upd_neq neq_a' Ball_def Bex_def image_iff imp_ex nth_list_update less_Suc_eq
            flip: match_def)
    by (metis prefers_trans)
  moreover have "opti\<^sub>a ?A" using opti\<^sub>a_inv[OF A \<open>a' < n\<close> _ _ _ \<open>opti\<^sub>a A\<close>] a a'[THEN conjunct2] pref by auto
  ultimately show ?thesis using a a' M pref_match'_iff by auto
qed

(* TODO: could also be used in invAM_next *)
lemma preferred_subset_match_if_invAM:
assumes "invAM A M"
shows "\<forall>a<n. preferred A a \<subseteq> match A ` M" (is ?P)
proof -
  have A: "wf A" and pref_match: "pref_match A M" using assms(1) by auto
  note pref_match' = pref_match[THEN pref_match'_iff[OF A, THEN iffD2]]
  thus pref_match1: "\<forall>a<n. preferred A a \<subseteq> match A ` M" unfolding pref_match'_def by blast
qed

lemma invAM_next:
assumes "invAM A M"
assumes a: "a < n \<and> a \<notin> M" and a': "a' \<in> M \<and> match A a' = match A a" and pref: "\<not> Q ! match A a' \<turnstile> a < a'"
shows "invAM (A[a := A!a + 1]) M"
proof -
  have A: "wf A" and M : "M \<subseteq> {<n}" and inj: "inj_on (match A) M" and pref_match: "pref_match A M"
  and opti\<^sub>a: "opti\<^sub>a A" and "a' < n"
    by(insert \<open>invAM A M\<close> a') (auto)
  hence pref': "Q ! match A a' \<turnstile> a' < a"
    using pref a a' Q_set unfolding prefers_def
    by (metis match_def match_less_n index_eq_index_conv linorder_less_linear subsetD)
  have "M \<noteq> {<n}" using a by fastforce
  have neq_a: "\<forall>x. x\<in> M \<longrightarrow> a \<noteq> x" using a by blast
  have pref_match': "pref_match' A M" using pref_match pref_match'_iff[OF A,of M] by blast
  hence "\<forall>a<n. preferred A a \<subseteq> match A ` M" unfolding pref_match'_def by blast
  hence "A!a + 1 < n"
    using more_choices[OF _ M \<open>M \<noteq> {<n}\<close>] A inj a a' unfolding matching_def by (metis (no_types, lifting) imageI)
  let ?A = "A[a := A!a+1]"
  have "wf ?A" using A \<open>A!a + 1 < n\<close> by(simp add: set_update_subsetI)
  moreover have "inj_on (match ?A) M" using a inj
    by(simp add: match_def inj_on_def) (metis nth_list_update_neq)
  moreover have "pref_match' ?A M" using a pref_match' pref' A a' neq_a
    by(auto simp: match_upd_neq pref_match'_def Ball_def Bex_def image_iff nth_list_update imp_ex less_Suc_eq
            simp flip: match_def)
  moreover have  "opti\<^sub>a ?A" using opti\<^sub>a_inv[OF A conjunct1[OF a] \<open>a' < n\<close> conjunct2[OF a'] pref' opti\<^sub>a] .
  ultimately show ?thesis using M by (simp add: pref_match'_iff)
qed


lemma Gale_Shapley1: "VARS M A a a' b
 [M = {} \<and> A = replicate n 0]
 WHILE M \<noteq> {<n}
 INV { invAM A M }
 VAR {var A M}
 DO a := (SOME a. a < n \<and> a \<notin> M); b := match A a;
  IF b \<notin> match A ` M
  THEN M := M \<union> {a}
  ELSE a' := (SOME a'. a' \<in> M \<and> match A a' = b);
       IF Q ! match A a' \<turnstile> a < a'
       THEN A[a'] := A!a'+1; M := M - {a'} \<union> {a}
       ELSE A[a] := A!a+1
       FI
  FI 
 OD
 [matching A {<n} \<and> stable A {<n} \<and> opti\<^sub>a A]"
proof (vcg_tc, goal_cases)
  case 1 thus ?case
   by(auto simp: stable_def opti\<^sub>a_def pref_match_def P_set card_distinct match_def index_nth_id prefers_def)
next
  case 3 thus ?case using pref_match_stable by auto
next
  case (2 v M A a)
  hence invAM: "invAM A M" and m: "matching A M" and M: "M \<subseteq> {<n}" "M \<noteq> {<n}" and "opti\<^sub>a A"
    and v: "var A M = v" by auto
  note Ainj = conj12[OF m[unfolded matching_def]]
  note pref_match1 = preferred_subset_match_if_invAM[OF invAM]
  define a where "a = (SOME a. a < n \<and> a \<notin> M)"
  have a: "a < n \<and> a \<notin> M" unfolding a_def using M
    by (metis (no_types, lifting) atLeastLessThan_iff someI_ex subsetI subset_antisym)
  show ?case (is "?P((SOME a. a < n \<and> a \<notin> M))") unfolding a_def[symmetric]
  proof -
    show "?P a" (is "(?not_matched \<longrightarrow> ?THEN) \<and> (\<not> ?not_matched \<longrightarrow> ?ELSE)")
    proof (rule; rule)
      assume ?not_matched
      show ?THEN
      proof(simp only:mem_Collect_eq prod.case, rule conjI, goal_cases)
        case 1 show ?case using invAM_match[OF invAM a \<open>?not_matched\<close>] .

        case 2 show ?case
          using var_match[OF m M pref_match1] var0_match[OF Ainj(1) M(1)] a unfolding v by blast
      qed
    next
      assume matched: "\<not> ?not_matched"
      define a' where "a' = (SOME a'.  a' \<in> M \<and> match A a' = match A a)"
      have a': "a' \<in> M \<and> match A a' = match A a" unfolding a'_def using matched
        by (smt (verit) image_iff someI_ex)
      hence "a' < n" "a \<noteq> a'" using a M atLeast0LessThan by auto
      show ?ELSE (is "?P((SOME a'. a' \<in> M \<and> match A a' = match A a))") unfolding a'_def[symmetric]
      proof -
        show "?P a'" (is "(?pref \<longrightarrow> ?THEN) \<and> (\<not> ?pref \<longrightarrow> ?ELSE)")
        proof (rule; rule)
          assume ?pref
          show ?THEN
          proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
            case 1 show ?case by(rule invAM_swap[OF invAM a a' \<open>?pref\<close>])

            case 2
            have "card(M - {a'} \<union> {a}) = card M"
              using a a' card.remove subset_eq_atLeast0_lessThan_finite[OF M(1)] by fastforce
            thus ?case using v var_next[OF m M pref_match1 \<open>a' < n\<close>] var0_next[OF Ainj(1) M \<open>a' < n\<close>]
              by simp
          qed
        next
          assume "\<not> ?pref"
          show ?ELSE
          proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
            case 1 show ?case using invAM_next[OF invAM a a' \<open>\<not> ?pref\<close>] .

            case 2
            show ?case using a v var_next[OF m M pref_match1, of a] var0_next[OF Ainj(1) M, of a]
              by simp
          qed
        qed
      qed
    qed
  qed
qed

text \<open>Proof also works for @{const var0} instead of @{const var}.\<close>


subsection \<open>Algorithm 2: List of unmatched As\<close>

abbreviation invas where
"invas as == (set as \<subseteq> {<n} \<and> distinct as)"

lemma Gale_Shapley2: "VARS A a a' as b
 [as = [0..<n] \<and> A = replicate n 0]
 WHILE as \<noteq> []
 INV { invAM A ({<n} - set as) \<and> invas as}
 VAR {var A ({<n} - set as)}
 DO a := hd as; b := match A a;
  IF b \<notin> match A ` ({<n} - set as)
  THEN as := tl as
  ELSE a' := (SOME a'. a' \<in> {<n} - set as \<and> match A a' = b);
       IF Q ! match A a' \<turnstile> a < a'
       THEN A[a'] := A!a'+1; as := a' # tl as
       ELSE A[a] := A!a+1
       FI
  FI 
 OD
 [matching A {<n} \<and> stable A {<n} \<and> opti\<^sub>a A]"
proof (vcg_tc, goal_cases)
  case 1 thus ?case
   by(auto simp: stable_def opti\<^sub>a_def pref_match_def P_set card_distinct match_def index_nth_id prefers_def)
next
  case 3 thus ?case using pref_match_stable by auto
next
  case (2 v A _ a' as)
  let ?M = "{<n} - set as"
  have invAM: "invAM A ?M" and m: "matching A ?M" and A: "wf A" and M: "?M \<subseteq> {<n}"
    and "as \<noteq> []" and as: "invas as" and v: "var A ?M = v" using 2 by auto
  note pref_match1 = preferred_subset_match_if_invAM[OF invAM]
  from \<open>as \<noteq> []\<close> obtain a as' where aseq: "as = a # as'" by (fastforce simp: neq_Nil_conv)
  have set_as: "?M \<union> {a} = {<n} - set as'" using as aseq by force
  have a: "a < n \<and> a \<notin> ?M" using as unfolding aseq by (simp)
  show ?case
  proof (simp only: aseq list.sel, goal_cases)
    case 1 show ?case (is "(?not_matched \<longrightarrow> ?THEN) \<and> (\<not> ?not_matched \<longrightarrow> ?ELSE)")
    proof (rule; rule)
      assume ?not_matched
      then have nm: "match A a \<notin> match A ` ?M" unfolding aseq .
      show ?THEN
      proof(simp only:mem_Collect_eq prod.case, rule conjI, goal_cases)
        case 1 show ?case using invAM_match[OF invAM a nm] as unfolding set_as by (simp add: aseq)
        case 2 show ?case
          using var_match[OF m M _ pref_match1, of a] a atLeast0LessThan
          unfolding set_as v by blast 
      qed
    next
      assume matched: "\<not> ?not_matched"
      define a' where "a' = (SOME a'.  a' \<in> ?M \<and> match A a' = match A a)"
      have a': "a' \<in> ?M \<and> match A a' = match A a" unfolding a'_def aseq using matched
        by (smt (verit) image_iff someI_ex)
      hence "a' < n" "a \<noteq> a'" using a M atLeast0LessThan by auto
      show ?ELSE unfolding aseq[symmetric] a'_def[symmetric]
      proof (goal_cases)
        case 1
        show ?case (is "(?pref \<longrightarrow> ?THEN) \<and> (\<not> ?pref \<longrightarrow> ?ELSE)")
        proof (rule; rule)
          assume ?pref
          show ?THEN
          proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
            have *: "{<n} - set as - {a'} \<union> {a} = {<n} - set (a' # as')" using a a' as aseq by auto
            case 1 show ?case using invAM_swap[OF invAM a a' \<open>?pref\<close>] unfolding *
              using a' as aseq by force
            case 2
            have "card({<n} - set as) = card({<n} - set (a' # as'))" using a a' as aseq by auto
            thus ?case using v var_next[OF m M _ pref_match1, of a'] \<open>a' < n\<close> a atLeast0LessThan
              by (metis Suc_eq_plus1 lessThan_iff var_def)
          qed
        next
          assume "\<not> ?pref"
          show ?ELSE
          proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
            case 1 show ?case using invAM_next[OF \<open>invAM A ?M\<close> a a' \<open>\<not> ?pref\<close>] as by blast

            case 2
            show ?case using a v var_next[OF m M _ pref_match1, of a]
              by (metis Suc_eq_plus1 atLeast0LessThan lessThan_iff) 
          qed
        qed
      qed
    qed
  qed
qed


subsection \<open>Algorithm 3: Record matching of Bs to As\<close>

abbreviation invAB :: "nat list \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> nat set \<Rightarrow> bool" where
"invAB A B M == (ran B = M \<and> (\<forall>b a. B b = Some a \<longrightarrow> match A a = b))"

lemma invAB_swap:
assumes invAB: "invAB A B M"
assumes a: "a < n \<and> a \<notin> M" and a': "a' \<in> M \<and> match A a' = match A a"
  and "inj_on B (dom B)" "B(match A a) = Some a'"
shows "invAB (A[a' := A!a'+1]) (B(match A a := Some a)) (M - {a'} \<union> {a})"
proof -
  have "\<forall>b x. b \<noteq> match A a \<longrightarrow> B b = Some x \<longrightarrow> a'\<noteq> x" using invAB a' by blast
  moreover have "a \<noteq> a'" using a a' by auto 
  ultimately show ?thesis using assms by(simp add: ran_map_upd_Some match_def)
qed


lemma Gale_Shapley3: "VARS A B a a' as b
 [as = [0..<n] \<and> A = replicate n 0 \<and> B = (\<lambda>_. None)]
 WHILE as \<noteq> []
 INV { invAM A ({<n} - set as) \<and> invAB A B ({<n} - set as) \<and> invas as}
 VAR {var A ({<n} - set as)}
 DO a := hd as; b := match A a;
  IF B b = None
  THEN B := B(b := Some a); as := tl as
  ELSE a' := the(B b);
       IF Q ! match A a' \<turnstile> a < a'
       THEN B := B(b := Some a); A[a'] := A!a'+1; as := a' # tl as
       ELSE A[a] := A!a+1
       FI
  FI 
 OD
 [matching A {<n} \<and> stable A {<n} \<and> opti\<^sub>a A]"
proof (vcg_tc, goal_cases)
  case 1 thus ?case
    by(auto simp: stable_def opti\<^sub>a_def pref_match_def P_set card_distinct match_def index_nth_id prefers_def)
next
  case 3 thus ?case using pref_match_stable by auto
next
  case (2 v A B _ a' as)
  let ?M = "{<n} - set as"
  have invAM: "invAM A ?M" and m: "matching A ?M" and A: "wf A" and M: "?M \<subseteq> {<n}"
    and "as \<noteq> []" and as: "invas as" and invAB: "invAB A B ?M" and v: "var A ?M = v"
    using 2 by auto
  note pref_match1 = preferred_subset_match_if_invAM[OF invAM]
  from \<open>as \<noteq> []\<close> obtain a as' where aseq: "as = a # as'" by (fastforce simp: neq_Nil_conv)
  have set_as: "?M \<union> {a} = {<n} - set as'" using as aseq by force
  have a: "a < n \<and> a \<notin> ?M" using as unfolding aseq by (simp)
  show ?case
  proof (simp only: aseq list.sel, goal_cases)
    case 1 show ?case (is "(?not_matched \<longrightarrow> ?THEN) \<and> (\<not> ?not_matched \<longrightarrow> ?ELSE)")
    proof (rule; rule)
      assume ?not_matched
      then have nm: "match A a \<notin> match A ` ?M" using invAB unfolding aseq ran_def
        apply (clarsimp simp: set_eq_iff) using not_None_eq by blast
      show ?THEN
      proof(simp only:mem_Collect_eq prod.case, rule conjI, goal_cases)
        have invAM': "invAM A ({<n} - set as')"
          using invAM_match[OF invAM a nm] unfolding set_as[symmetric] by simp
        have invAB': "invAB A (B(match A a := Some a)) ({<n} - set as')"
          using invAB \<open>?not_matched\<close> set_as by (simp)
        case 1 show ?case using invAM' as invAB' unfolding set_as aseq
          by (metis distinct.simps(2) insert_subset list.simps(15))
        case 2 show ?case
          using var_match[OF m M _ pref_match1, of a] a atLeast0LessThan
          unfolding set_as v by blast 
      qed
    next
      assume matched: "\<not> ?not_matched"
      then obtain a' where a'eq: "B(match A a) = Some a'" by auto
      have a': "a' \<in> ?M \<and> match A a' = match A a" unfolding aseq using a'eq invAB
        by (metis ranI aseq)
      hence "a' < n" "a \<noteq> a'" using a M atLeast0LessThan by auto
      show ?ELSE unfolding aseq[symmetric] a'eq option.sel
      proof (goal_cases)
        have inj_dom: "inj_on B (dom B)" by (metis (mono_tags) domD inj_onI invAB)
        case 1
        show ?case (is "(?pref \<longrightarrow> ?THEN) \<and> (\<not> ?pref \<longrightarrow> ?ELSE)")
        proof (rule; rule)
          assume ?pref
          show ?THEN
          proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
            have *: "{<n} - set as - {a'} \<union> {a} = {<n} - set (a' # as')" using a a' as aseq by auto
            have a'neq: "\<forall>b x. b \<noteq> match A a \<longrightarrow> B b = Some x \<longrightarrow> a'\<noteq> x"
              using invAB a' by blast
            have invAB': "invAB (A[a' := A ! a' + 1]) (B(match A a := Some a)) ({<n} - insert a' (set as'))"
              using invAB_swap[OF invAB a a' inj_dom a'eq] * by simp
            case 1 show ?case using invAM_swap[OF invAM a a' \<open>?pref\<close>] invAB' unfolding *
              using a' as aseq by simp
            case 2
            have "card({<n} - set as) = card({<n} - set (a' # as'))" using a a' as aseq by auto
            thus ?case using v var_next[OF m M _ pref_match1, of a'] \<open>a' < n\<close> a atLeast0LessThan
              by (metis Suc_eq_plus1 lessThan_iff var_def)
          qed
        next
          assume "\<not> ?pref"
          show ?ELSE
          proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
            case 1
            have "invAB (A[a := A ! a + 1]) B ?M" using invAB a
              by (metis match_def nth_list_update_neq ranI)
            thus ?case using invAM_next[OF invAM a a' \<open>\<not> ?pref\<close>] as by blast
            case 2
            show ?case using a v var_next[OF m M _ pref_match1, of a]
              by (metis Suc_eq_plus1 atLeast0LessThan lessThan_iff) 
          qed
        qed
      qed
    qed
  qed
qed


subsection \<open>Unused data refinement step\<close>

(* begin unused: directly implement function B via lists B and M (data refinement);
   also done in Alg. 4 in a more principled manner *)

abbreviation invAB' :: "nat list \<Rightarrow> nat list \<Rightarrow> bool list \<Rightarrow> nat set \<Rightarrow> bool" where
"invAB' A B M M' == (length B = n \<and> length M = n \<and> M' = nth B ` {b. b < n \<and> M!b}
 \<and> (\<forall>b<n. M!b \<longrightarrow> B!b < n \<and> match A (B!b) = b))"

lemma Gale_Shapley4_unused: "VARS A B M a a' as b
 [as = [0..<n] \<and> A = replicate n 0 \<and> B = replicate n 0 \<and> M = replicate n False]
 WHILE as \<noteq> []
 INV { invAM A ({<n} - set as) \<and> invAB' A B M ({<n} - set as) \<and> invas as}
 VAR {var A ({<n} - set as)}
 DO a := hd as; b := match A a;
  IF \<not> (M ! b)
  THEN M[b] := True; B[b] := a; as := tl as
  ELSE a' := B ! b;
       IF Q ! match A a' \<turnstile> a < a'
       THEN B[b] := a; A[a'] := A!a'+1; as := a' # tl as
       ELSE A[a] := A!a+1
       FI
  FI 
 OD
 [wf A \<and> inj_on (match A) {<n} \<and> stable A {<n} \<and> opti\<^sub>a A]"
proof (vcg_tc, goal_cases)
  case 1 thus ?case
   by(auto simp: stable_def opti\<^sub>a_def pref_match_def P_set card_distinct match_def index_nth_id prefers_def)
next
  case 3 thus ?case using pref_match_stable by auto
next
  case (2 v A B M _ a' as)
  let ?M = "{<n} - set as"
  have invAM: "invAM A ?M" and m: "matching A ?M" and A: "wf A" and M: "?M \<subseteq> {<n}"
    and notall: "as \<noteq> []" and as: "invas as" and invAB: "invAB' A B M ?M" and v: "var A ?M = v"
    using 2 by auto
  note pref_match1 = preferred_subset_match_if_invAM[OF invAM]
  from notall obtain a as' where aseq: "as = a # as'" by (fastforce simp: neq_Nil_conv)
  have set_as: "?M \<union> {a} = {<n} - set as'" using as aseq by force
  have a: "a < n \<and> a \<notin> ?M" using as unfolding aseq by (simp)
  show ?case
  proof (simp only: aseq list.sel, goal_cases)
    case 1 show ?case (is "(?not_matched \<longrightarrow> ?THEN) \<and> (\<not> ?not_matched \<longrightarrow> ?ELSE)")
    proof (rule; rule)
      assume ?not_matched
      then have nm: "match A a \<notin> match A ` ?M" using invAB set_as unfolding aseq by force
      show ?THEN
      proof(simp only:mem_Collect_eq prod.case, rule conjI, goal_cases)
        have invAM': "invAM A ({<n} - set as')"
          using invAM_match[OF invAM a nm] unfolding set_as[symmetric] by simp
        then have invAB': "invAB' A (B[match A a := a]) (M[match A a := True]) ({<n} - set as')"
          using invAB \<open>?not_matched\<close> set_as match_less_n[OF A] a
          by (auto simp add: image_def nth_list_update)
        case 1 show ?case using invAM' invAB as invAB' unfolding set_as aseq
          by (metis distinct.simps(2) insert_subset list.simps(15))
        case 2 show ?case
          using var_match[OF m M _ pref_match1, of a] a atLeast0LessThan
          unfolding set_as v by blast 
      qed
    next
      assume matched: "\<not> ?not_matched"
      hence "match A a \<in> match A ` ({<n} - insert a (set as'))" using  match_less_n[OF A] a invAB
        apply(auto) by (metis (lifting) image_eqI list.simps(15) mem_Collect_eq aseq)
      hence "Suc(A!a) < n" using more_choices[OF A M, of a] a pref_match1
        using aseq atLeast0LessThan by auto
      let ?a = "B ! match A a"
      have a': "?a \<in> ?M \<and> match A ?a = match A a"
        using invAB match_less_n[OF A] matched a by blast
      hence "?a < n" "a \<noteq> ?a" using a by auto
      show ?ELSE unfolding aseq option.sel
      proof (goal_cases)
        case 1
        show ?case (is "(?pref \<longrightarrow> ?THEN) \<and> (\<not> ?pref \<longrightarrow> ?ELSE)")
        proof (rule; rule)
          assume ?pref
          show ?THEN
          proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
            have *: "{<n} - set as - {?a} \<union> {a} = {<n} - set (?a # as')" using a a' as aseq by auto
            have a'neq: "\<forall>b<n. b \<noteq> match A a \<longrightarrow> M!b \<longrightarrow> ?a \<noteq> B!b"
              using invAB a' by metis
            have invAB': "invAB' (A[?a := A ! ?a + 1]) (B[match A a := a]) M ({<n} - set (?a#as'))"
              using invAB aseq * \<open>a \<noteq> ?a\<close> a' match_less_n[OF A, of a] a
              apply (simp add: nth_list_update)
              apply rule
               apply(auto simp add:  image_def)[]
              apply (clarsimp simp add: match_def)
              apply (metis (opaque_lifting) nth_list_update_neq)
              done
            case 1 show ?case using invAM_swap[OF invAM a a' \<open>?pref\<close>] invAB' unfolding *
              using a' as aseq by (auto)
            case 2
            have "card({<n} - set as) = card({<n} - set (?a # as'))" using a a' as aseq by simp
            thus ?case using v var_next[OF m M _ pref_match1, of ?a] \<open>?a < n\<close> a atLeast0LessThan
              by (metis Suc_eq_plus1 lessThan_iff var_def)
          qed
        next
          assume "\<not> ?pref"
          show ?ELSE
          proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
            case 1
            have "invAB' (A[a := A ! a + 1]) B M ({<n} - set as)" using invAB a \<open>a \<noteq> ?a\<close>
              by (metis match_def nth_list_update_neq)
            thus ?case using invAM_next[OF invAM a a' \<open>\<not> ?pref\<close>] as aseq by fastforce
            case 2
            show ?case using a v var_next[OF m M _ pref_match1, of a] aseq
              by (metis Suc_eq_plus1 atLeast0LessThan lessThan_iff) 
          qed
        qed
      qed
    qed
  qed
qed


subsection \<open>Algorithm 4: remove list of unmatched As\<close>

subsubsection \<open>An initial version\<close>

text \<open>The inner variant appears intuitive but complicates the derivation of an overall complexity bound
because the inner variant also depends on a variable that is modified by the outer loop.\<close>

lemma Gale_Shapley4:
"VARS A B ai a a'
 [ai = 0 \<and> A = replicate n 0 \<and> B = (\<lambda>_. None)]
 WHILE ai < n
 INV { invAM A {<ai} \<and> invAB A B {<ai} \<and> ai \<le> n }
 VAR {z = n - ai}
 DO a := ai;
  WHILE B (match A a) \<noteq> None
  INV { invAM A ({<ai+1} - {a}) \<and> invAB A B ({<ai+1} - {a}) \<and> (a \<le> ai \<and> ai < n) \<and> z = n-ai }
  VAR {var A {<ai}}
  DO a' := the(B (match A a));
     IF Q ! match A a' \<turnstile> a < a'
     THEN B := B(match A a := Some a); A[a'] := A!a'+1; a := a'
     ELSE A[a] := A!a+1
     FI
  OD;
  B := B(match A a := Some a); ai := ai+1
 OD
 [matching A {<n} \<and> stable A {<n} \<and> opti\<^sub>a A]"
proof (vcg_tc, goal_cases)
  case 1 thus ?case  (* outer invar holds initially *)
   by(auto simp: stable_def pref_match_def P_set card_distinct match_def index_nth_id prefers_def opti\<^sub>a_def)[]
next
  case 2 (* outer invar and b implies inner invar *)
  thus ?case by (auto simp: atLeastLessThanSuc_atLeastAtMost simp flip: atLeastLessThan_eq_atLeastAtMost_diff)
next
  case (4 z A B ai a) (* inner invar' and not b implies outer invar *)
  note inv = 4[THEN conjunct1]
  note invAM = inv[THEN conjunct1]
  note aai = inv[THEN conjunct2,THEN conjunct2]
  show ?case
  proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
    case 1
    have *: "{<Suc ai} = insert a ({<Suc ai} - {a})" using aai by (simp add: insert_absorb)
    have **: "inj_on (match A) {<Suc ai} = (inj_on (match A) ({<Suc ai} - {a}) \<and> match A a \<notin> match A ` ({<Suc ai} - {a}))"
      by (metis "*" Diff_idemp inj_on_insert)
    have nm: "match A a \<notin> match A ` ({<Suc ai} - {a})" using 4 unfolding ran_def
        apply (clarsimp simp: set_eq_iff) by (metis not_None_eq)
    have invAM': "invAM A {<ai+1}"
      using invAM_match[OF invAM, of a] aai nm by (simp add: ** insert_absorb)
    show ?case using 4 invAM' by (simp add: insert_absorb)
  next
    case 2 thus ?case using 4 by auto
  qed
next
  case 5 (* outer invar and not b implies post *)
  thus ?case using pref_match_stable unfolding invAM_def by (metis le_neq_implies_less)
next
  case (3 z v A B ai a a') (* preservation of inner invar *)
  let ?M = "{<ai+1} - {a}"
  have invAM: "invAM A ?M" and m: "matching A ?M" and A: "wf A" and M: "?M \<subseteq> {<n}"
    and matched: "B(match A a) \<noteq> None" and as: "a \<le> ai \<and> ai < n" and invAB: "invAB A B ?M"
    and v: "var A ?M = v" using 3 by auto
  note invar = 3[THEN conjunct1,THEN conjunct1]
  note pref_match1 = preferred_subset_match_if_invAM[OF invAM]
  from matched obtain a' where a'eq: "B(match A a) = Some a'" by auto
  have a': "a' \<in> ?M \<and> match A a' = match A a" using a'eq invAB by (metis ranI)
  have a: "a < n \<and> a \<notin> ?M" using invar by auto
  have "?M \<noteq> {<n}" and "a' < n" using M a a' atLeast0LessThan by auto
  have card: "card {<ai} = card ?M" using as by simp
  show ?case unfolding a'eq option.sel
  proof (goal_cases)
    case 1
    show ?case (is "(?unstab \<longrightarrow> ?THEN) \<and> (\<not> ?unstab \<longrightarrow> ?ELSE)")
    proof (rule; rule)
      assume ?unstab
      have *: "{<ai + 1} - {a} - {a'} \<union> {a} = {<ai + 1} - {a'}" using invar a' by auto
      show ?THEN
      proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
        have inj_dom: "inj_on B (dom B)" by (metis (mono_tags) domD inj_onI invAB)
        have invAB': "invAB (A[a' := A ! a' + 1]) (B(match A a \<mapsto> a)) ({<ai + 1} - {a'})"
          using invAB_swap[OF invAB a a' inj_dom a'eq] * by simp
        case 1 show ?case
          using invAM_swap[OF invAM a a' \<open>?unstab\<close>] invAB' invar a' unfolding * by (simp)
      next
        case 2
        show ?case using v var_next[OF m M \<open>?M \<noteq> {<n}\<close> pref_match1 \<open>a' < n\<close>] card
          by (metis var_def Suc_eq_plus1 psubset_eq)
      qed
    next
      assume "\<not> ?unstab"
      show ?ELSE
      proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
        have *: "\<forall>b a'. B b = Some a' \<longrightarrow> a \<noteq> a'" by (metis invAB ranI a) 
        case 1 show ?case using invAM_next[OF invAM a a' \<open>\<not> ?unstab\<close>] invar * by (simp add: match_def)
      next
        case 2
        show ?case using v var_next[OF m M \<open>?M \<noteq> {<n}\<close> pref_match1, of a] a card
          by (metis Suc_eq_plus1 var_def)
      qed
    qed
  qed
qed

subsubsection \<open>A better inner variant\<close>

text \<open>This is the definitive version of Algorithm 4.
The inner variant is changed to support the easy derivation of the precise upper bound
of the number of executed actions.
This variant shows that the algorithm can at most execute @{term "n^2 - n + 1"}
basic actions (match, swap, next).\<close>

definition var2 :: "nat list \<Rightarrow> nat" where
[simp]: "var2 A = (n-1)^2 - (\<Sum>a<n. A!a)"

text \<open>Because \<open>A\<close> is not changed by the outer loop, the initial value of @{term "var2 A"},
which is @{term "(n-1)^2"}, is an upper bound of the number of iterations of the inner loop.
To this we need to add \<open>n\<close> because the outer loop executes additional \<open>n\<close> match actions
at the end of the loop body.
Thus at most @{prop "(n-1)^2 + n = n^2 - n + 1"} actions are executed, exactly as in the earlier algorithms.\<close>

lemma var2_next:
assumes "invAM (A[a := A!a + 1]) M" "M \<noteq> {<n}" "a < n"
shows "var2 (A[a := A!a + 1]) < var2 A"
proof -
  let ?A = "A[a := A!a + 1]"
  have "wf ?A" using assms(1) by auto
  have 1: "(\<Sum>a<n. ?A!a) = (\<Sum>a<n. A!a) + 1"
  proof -
    have "(\<Sum>a<n. ?A!a) = 1 + (A ! a + sum ((!) A) ({<n} - {a}))"
      using \<open>wf ?A\<close> \<open>a < n\<close> by(simp add: nth_list_update sum.If_cases lessThan_atLeast0 flip:Diff_eq)
    also have "\<dots> = (\<Sum>a<n. A!a) + 1"
      using \<open>a < n\<close> member_le_sum[of a "{<n}" "nth A"] by(simp add: sum_diff1_nat lessThan_atLeast0)
    finally show ?thesis .
  qed
  have "(\<Sum>a<n. ?A!a) \<le> (n-1)^2"
    using sumA_UB[of ?A M] assms(1,2) by (meson invAM_def preferred_subset_match_if_invAM)
  with 1 show ?thesis unfolding var2_def by auto
qed

lemma Gale_Shapley4_var2:
"VARS A B ai a a'
 [ai = 0 \<and> A = replicate n 0 \<and> B = (\<lambda>_. None)]
 WHILE ai < n
 INV { invAM A {<ai} \<and> invAB A B {<ai} \<and> ai \<le> n }
 VAR {z = n - ai}
 DO a := ai;
  WHILE B (match A a) \<noteq> None
  INV { invAM A ({<ai+1} - {a}) \<and> invAB A B ({<ai+1} - {a}) \<and> (a \<le> ai \<and> ai < n) \<and> z = n-ai }
  VAR {var2 A}
  DO a' := the(B (match A a));
     IF Q ! match A a' \<turnstile> a < a'
     THEN B := B(match A a := Some a); A[a'] := A!a'+1; a := a'
     ELSE A[a] := A!a+1
     FI
  OD;
  B := B(match A a := Some a); ai := ai+1
 OD
 [matching A {<n} \<and> stable A {<n} \<and> opti\<^sub>a A]"
proof (vcg_tc, goal_cases)
  case 1 thus ?case  (* outer invar holds initially *)
   by(auto simp: stable_def pref_match_def P_set card_distinct match_def index_nth_id prefers_def opti\<^sub>a_def)[]
next
  case 2 (* outer invar and b implies inner invar *)
  thus ?case by (auto simp: atLeastLessThanSuc_atLeastAtMost simp flip: atLeastLessThan_eq_atLeastAtMost_diff)
next
  case (4 z A B ai a) (* inner invar' and not b implies outer invar *)
  note inv = 4[THEN conjunct1]
  note invAM = inv[THEN conjunct1]
  note aai = inv[THEN conjunct2,THEN conjunct2]
  show ?case
  proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
    case 1
    have *: "{<Suc ai} = insert a ({<Suc ai} - {a})" using aai by (simp add: insert_absorb)
    have **: "inj_on (match A) {<Suc ai} = (inj_on (match A) ({<Suc ai} - {a}) \<and> match A a \<notin> match A ` ({<Suc ai} - {a}))"
      by (metis "*" Diff_idemp inj_on_insert)
    have nm: "match A a \<notin> match A ` ({<Suc ai} - {a})" using 4 unfolding ran_def
        apply (clarsimp simp: set_eq_iff) by (metis not_None_eq)
    have invAM': "invAM A {<ai+1}"
      using invAM_match[OF invAM, of a] aai nm by (simp add: ** insert_absorb)
    show ?case using 4 invAM' by (simp add: insert_absorb)
  next
    case 2 thus ?case using 4 by auto
  qed
next
  case 5 (* outer invar and not b implies post *)
  thus ?case using pref_match_stable unfolding invAM_def by (metis le_neq_implies_less)
next
  case (3 z v A B ai a a') (* preservation of inner invar *)
  let ?M = "{<ai+1} - {a}"
  have invAM: "invAM A ?M" and m: "matching A ?M" and A: "wf A" and M: "?M \<subseteq> {<n}"
    and matched: "B(match A a) \<noteq> None" and as: "a \<le> ai \<and> ai < n" and invAB: "invAB A B ?M"
    and v: "var2 A = v" using 3 by auto
  note invar = 3[THEN conjunct1,THEN conjunct1]
  from matched obtain a' where a'eq: "B(match A a) = Some a'" by auto
  have a': "a' \<in> ?M \<and> match A a' = match A a" using a'eq invAB by (metis ranI)
  have a: "a < n \<and> a \<notin> ?M" using invar by auto
  have "?M \<noteq> {<n}" and "a' < n" using M a a' atLeast0LessThan by auto
  show ?case unfolding a'eq option.sel
  proof (goal_cases)
    case 1
    show ?case (is "(?unstab \<longrightarrow> ?THEN) \<and> (\<not> ?unstab \<longrightarrow> ?ELSE)")
    proof (rule; rule)
      assume ?unstab
      have *: "{<ai + 1} - {a} - {a'} \<union> {a} = {<ai + 1} - {a'}" using invar a' by auto
      show ?THEN
      proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
        note invAM' = invAM_swap[OF invAM a a' \<open>?unstab\<close>]
        have inj_dom: "inj_on B (dom B)" by (metis (mono_tags) domD inj_onI invAB)
        have invAB': "invAB (A[a' := A ! a' + 1]) (B(match A a \<mapsto> a)) ({<ai + 1} - {a'})"
          using invAB_swap[OF invAB a a' inj_dom a'eq] * by simp
        case 1 show ?case using invAM' invAB' invar a' unfolding * by (simp)
        case 2 show ?case using v var2_next[OF invAM'] \<open>a' < n\<close> * atLeast0LessThan by auto
      qed
    next
      assume "\<not> ?unstab"
      show ?ELSE
      proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
        note invAM' = invAM_next[OF invAM a a' \<open>\<not> ?unstab\<close>]
        have *: "\<forall>b a'. B b = Some a' \<longrightarrow> a \<noteq> a'" by (metis invAB ranI a) 
        case 1 show ?case using invAM' invar * by (simp add: match_def)
        case 2 show ?case using v var2_next[OF invAM'] a \<open>?M \<noteq> {<n}\<close> by blast
      qed
    qed
  qed
qed


subsubsection \<open>Algorithm 4.1: single-loop variant\<close>

text \<open>A bit of a relic because it is an instance of a general program transformation for
merging nested loops by an additional test inside the single loop.\<close>

lemma Gale_Shapley4_1: "VARS A B a a' ai b
 [ai = 0 \<and> a = 0 \<and> A = replicate n 0 \<and> B = (\<lambda>_. None)]
 WHILE ai < n
 INV { invAM A ({<ai+1} - {a}) \<and> invAB A B ({<ai+1} - {a}) \<and> (a \<le> ai \<and> ai \<le> n) \<and> (ai=n \<longrightarrow> a=ai)}
 VAR {var A ({<ai+1} - {a})}
 DO b := match A a;
  IF B b = None
  THEN B := B(b := Some a); ai := ai + 1; a := ai
  ELSE a' := the(B b);
       IF Q ! match A a' \<turnstile> a < a'
       THEN B := B(b := Some a); A[a'] := A!a'+1; a := a'
       ELSE A[a] := A!a+1
       FI
  FI 
 OD
 [matching A {<n} \<and> stable A {<n} \<and> opti\<^sub>a A]"
proof (vcg_tc, goal_cases)
  case 1 thus ?case
    by(auto simp: stable_def opti\<^sub>a_def pref_match_def P_set card_distinct match_def index_nth_id prefers_def)
next
  case 3 thus ?case using pref_match_stable
    using atLeast0_lessThan_Suc by force
next
  case (2 v A B a a' ai b)
  let ?M = "{<ai+1} - {a}"
  have invAM: "invAM A ?M" and m: "matching A ?M" and A: "wf A" and M: "?M \<subseteq> {<n}"
    and as: "a \<le> ai \<and> ai < n" and invAB: "invAB A B ?M" and v: "var A ?M = v" using 2 by auto
  note invar = 2[THEN conjunct1,THEN conjunct1]
  note pref_match1 = preferred_subset_match_if_invAM[OF invAM]
  have a: "a < n \<and> a \<notin> ?M" using as by (simp)
  show ?case (is "(?not_matched \<longrightarrow> ?THEN) \<and> (\<not> ?not_matched \<longrightarrow> ?ELSE)")
  proof (rule; rule)
    assume ?not_matched
    then have nm: "match A a \<notin> match A ` ?M" using invAB unfolding ran_def
      apply (clarsimp simp: set_eq_iff) using not_None_eq by blast
    show ?THEN
    proof(simp only:mem_Collect_eq prod.case, rule conjI, goal_cases)
      have *: "{<ai + 1 + 1} - {ai + 1} = {<ai + 1}" by auto
      have **: "{<ai + 1} - {a} \<union> {a} = {<ai + 1}" using as by auto
      hence invAM': "invAM A {<ai+1}"using invAM_match[OF invAM a nm] by simp
      have invAB': "invAB A (B(match A a := Some a)) {<ai+1}"
        using invAB \<open>?not_matched\<close> ** by (simp)
      case 1 show ?case using invAM' as invAB' * by presburger
      case 2 show ?case
        using var_match[OF m M _ pref_match1, of a] a atLeast0LessThan * **
        unfolding v by (metis lessThan_iff)
    qed
  next
    assume matched: "\<not> ?not_matched"
    then obtain a' where a'eq: "B(match A a) = Some a'" by auto
    have a': "a' \<in> ?M \<and> match A a' = match A a" using a'eq invAB by (metis ranI)
    hence "a' < n" "a \<noteq> a'" using a M atLeast0LessThan by auto
    show ?ELSE unfolding a'eq option.sel
    proof (goal_cases)
      have inj_dom: "inj_on B (dom B)" by (metis (mono_tags) domD inj_onI invAB)
      case 1
      show ?case (is "(?pref \<longrightarrow> ?THEN) \<and> (\<not> ?pref \<longrightarrow> ?ELSE)")
      proof (rule; rule)
        assume ?pref
        show ?THEN
        proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
          have *: "{<ai + 1} - {a} - {a'} \<union> {a} = {<ai + 1} - {a'}" using a a' as by auto
          have a'neq: "\<forall>b x. b \<noteq> match A a \<longrightarrow> B b = Some x \<longrightarrow> a'\<noteq> x"
            using invAB a' by blast
          have invAB': "invAB (A[a' := A ! a' + 1]) (B(match A a := Some a)) ({<ai + 1} - {a'})"
            using invAB_swap[OF invAB a a' inj_dom a'eq] * by simp
          case 1 show ?case using invAM_swap[OF invAM a a' \<open>?pref\<close>] invAB' unfolding *
            using a' as by simp
          case 2
          have "card({<ai + 1} - {a'}) = card({<ai + 1} - {a})" using a a' as by auto
          thus ?case using v var_next[OF m M _ pref_match1, of a'] \<open>a' < n\<close> a atLeast0LessThan
            by (metis Suc_eq_plus1 lessThan_iff var_def)
        qed
      next
        assume "\<not> ?pref"
        show ?ELSE
        proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
          case 1
          have "invAB (A[a := A ! a + 1]) B ?M" using invAB a
            by (metis match_def nth_list_update_neq ranI)
          thus ?case using invAM_next[OF invAM a a' \<open>\<not> ?pref\<close>] using "2" by presburger
          case 2
          show ?case using a v var_next[OF m M _ pref_match1, of a]
            by (metis Suc_eq_plus1 atLeast0LessThan lessThan_iff) 
        qed
      qed
    qed
  qed
qed


subsection \<open>Algorithm 5: Data refinement of \<open>B\<close>\<close>

definition "\<alpha> B N = (\<lambda>b. if b < n \<and> N!b then Some(B!b) else None)"

lemma \<alpha>_Some[simp]: "\<alpha> B N b = Some a \<longleftrightarrow> b < n \<and> N!b \<and> a = B!b"
by(auto simp add: \<alpha>_def)

lemma \<alpha>update1: "\<lbrakk> \<not> N ! b; b < length B; b < length N; n = length N \<rbrakk>
 \<Longrightarrow> ran(\<alpha> (B[b := a]) (N[b := True])) = ran(\<alpha> B N) \<union> {a}"
by(force simp add: \<alpha>_def ran_def nth_list_update)

lemma \<alpha>update2: "\<lbrakk> N!b; b < length B; b < length N; length N = n \<rbrakk>
 \<Longrightarrow> \<alpha> (B[b := a]) N = (\<alpha> B N)(b := Some a)"
by(force simp add: \<alpha>_def nth_list_update)


abbreviation invAB2 :: "nat list \<Rightarrow> nat list \<Rightarrow> bool list \<Rightarrow> nat set \<Rightarrow> bool" where
"invAB2 A B N M == (invAB A (\<alpha> B N) M \<and> (length B = n \<and> length N = n))"

definition invar1 where
[simp]: "invar1 A B N ai = (invAM A {<ai} \<and> invAB2 A B N {<ai} \<and> ai \<le> n)"

definition invar2 where
[simp]: "invar2 A B N ai a \<equiv> (invAM A ({<ai+1} - {a}) \<and> invAB2 A B N ({<ai+1} - {a}) \<and> a \<le> ai \<and> ai < n)"

text \<open>First, the `old' version with the more complicated inner variant:\<close>

lemma Gale_Shapley5:
"VARS A B N ai a a'
 [ai = 0 \<and> A = replicate n 0 \<and> length B = n \<and> N = replicate n False]
 WHILE ai < n
 INV { invar1 A B N ai }
 VAR { z = n - ai}
 DO a := ai;
  WHILE N ! match A a
  INV { invar2 A B N ai a \<and> z = n-ai }
  VAR {var A {<ai}}
  DO a' := B ! match A a;
     IF Q ! match A a' \<turnstile> a < a'
     THEN B[match A a] := a; A[a'] := A!a'+1; a := a'
     ELSE A[a] := A!a+1
     FI
  OD;
  B[match A a] := a; N[match A a] := True; ai := ai+1
 OD
 [matching A {<n} \<and> stable A {<n} \<and> opti\<^sub>a A]"
proof (vcg_tc, goal_cases)
  case 1 thus ?case  (* outer invar holds initially *)
   by(auto simp: pref_match_def P_set card_distinct match_def index_nth_id prefers_def opti\<^sub>a_def \<alpha>_def cong: conj_cong)
next
  case 2 (* outer invar and b implies inner invar *)
  thus ?case by (auto simp: atLeastLessThanSuc_atLeastAtMost simp flip: atLeastLessThan_eq_atLeastAtMost_diff)
next
  case (4 z A B M ai a) (* inner invar' and not b implies outer invar *)
  note inv = 4[THEN conjunct1, unfolded invar2_def]
  note invAM = inv[THEN conjunct1,THEN conjunct1]
  note aai = inv[THEN conjunct1, THEN conjunct2, THEN conjunct2]
  show ?case
  proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
    case 1
    have *: "{<Suc ai} = insert a ({<Suc ai} - {a})" using aai by (simp add: insert_absorb)
    have **: "inj_on (match A) {<Suc ai} = (inj_on (match A) ({<Suc ai} - {a}) \<and> match A a \<notin> match A ` ({<Suc ai} - {a}))"
      by (metis "*" Diff_idemp inj_on_insert)
    have nm: "match A a \<notin> match A ` ({<Suc ai} - {a})" using 4 unfolding invar2_def ran_def
        apply (clarsimp simp: set_eq_iff) by (metis)
    have invAM': "invAM A {<ai+1}"
      using invAM_match[OF invAM, of a] aai nm by (simp add: ** insert_absorb)
    show ?case using 4 invAM' by (simp add: \<alpha>update1 match_less_n insert_absorb nth_list_update)
  next
    case 2 thus ?case using 4 by auto
  qed
next
  case 5 (* outer invar and not b implies post *)
  thus ?case using pref_match_stable unfolding invAM_def invar1_def by(metis le_neq_implies_less)
next
  case (3 z v A B N ai a) (* preservation of inner invar *)
  let ?M = "{<ai+1} - {a}"
  have invAM: "invAM A ?M" and m: "matching A ?M" and A: "wf A" and M: "?M \<subseteq> {<n}"
    and matched: "N ! match A a" and as: "a \<le> ai \<and> ai < n" and invAB: "invAB2 A B N ?M"
    and v: "var A {<ai} = v" using 3 by auto
  note invar = 3[THEN conjunct1, THEN conjunct1, unfolded invar2_def]
  note pref_match1 = preferred_subset_match_if_invAM[OF invAM]
  let ?a = "B ! match A a"
  have a: "a < n \<and> a \<notin> ?M" using invar by auto
  have a': "?a \<in> ?M \<and> match A ?a = match A a"
    using invAB match_less_n[OF A] a matched by (metis \<alpha>_Some ranI)
  have "?M \<noteq> {<n}" and "?a < n" using M a a' atLeast0LessThan by auto
  have card: "card {<ai} = card ?M" using as by simp
  have *: "{<ai + 1} - {a} - {?a} \<union> {a} = {<ai + 1} - {?a}" using invar a' by auto
  show ?case
  proof (simp only: mem_Collect_eq prod.case, goal_cases)
    case 1
    show ?case
    proof ((rule;rule;rule), goal_cases)
      case unstab: 1
      have inj_dom: "inj_on (\<alpha> B N) (dom (\<alpha> B N))" by (metis (mono_tags) domD inj_onI invAB)
      have invAB': "invAB (A[B ! match A a := A ! ?a + 1]) (\<alpha> (B[match A a := a]) N) ({<ai + 1} - {?a})"
        using invAB_swap[OF invAB[THEN conjunct1] a a' inj_dom] * match_less_n[OF A] a matched invAB
        by(simp add:\<alpha>update2)
      show ?case using invAM_swap[OF invAM a a' unstab] invAB' invar a'
        unfolding * by (simp add: insert_absorb \<alpha>update2)

      case 2
      show ?case using v var_next[OF m M \<open>?M \<noteq> {<n}\<close> pref_match1 \<open>?a < n\<close>] card
        by (metis var_def Suc_eq_plus1)
    next
      case stab: 3
      have *: "\<forall>b. b < n \<and> N!b \<longrightarrow> a \<noteq> B!b" by (metis invAB ranI \<alpha>_Some a) 
      show ?case using invAM_next[OF invAM a a' stab] invar * by (simp add: match_def)

      case 4
      show ?case using v var_next[OF m M \<open>?M \<noteq> {<n}\<close> pref_match1, of a] a card
        by (metis Suc_eq_plus1 var_def)
    qed
  qed
qed

text \<open>The definitive version with variant @{const var2}:\<close>

lemma Gale_Shapley5_var2:
"VARS A B N ai a a'
 [ai = 0 \<and> A = replicate n 0 \<and> length B = n \<and> N = replicate n False]
 WHILE ai < n
 INV { invar1 A B N ai }
 VAR { z = n - ai}
 DO a := ai;
  WHILE N ! match A a
  INV { invar2 A B N ai a \<and> z = n-ai }
  VAR {var2 A}
  DO a' := B ! match A a;
     IF Q ! match A a' \<turnstile> a < a'
     THEN B[match A a] := a; A[a'] := A!a'+1; a := a'
     ELSE A[a] := A!a+1
     FI
  OD;
  B[match A a] := a; N[match A a] := True; ai := ai+1
 OD
 [matching A {<n} \<and> stable A {<n} \<and> opti\<^sub>a A]"
proof (vcg_tc, goal_cases)
  case 1 thus ?case  (* outer invar holds initially *)
   by(auto simp: pref_match_def P_set card_distinct match_def index_nth_id prefers_def opti\<^sub>a_def \<alpha>_def cong: conj_cong)
next
  case 2 (* outer invar and b implies inner invar *)
  thus ?case by (auto simp: atLeastLessThanSuc_atLeastAtMost simp flip: atLeastLessThan_eq_atLeastAtMost_diff)
next
  case (4 z A B N ai a) (* inner invar' and not b implies outer invar *)
  note inv = 4[THEN conjunct1, unfolded invar2_def]
  note invAM = inv[THEN conjunct1,THEN conjunct1]
  note aai = inv[THEN conjunct1, THEN conjunct2, THEN conjunct2]
  show ?case
  proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
    case 1
    have *: "{<Suc ai} = insert a ({<Suc ai} - {a})" using aai by (simp add: insert_absorb)
    have **: "inj_on (match A) {<Suc ai} = (inj_on (match A) ({<Suc ai} - {a}) \<and> match A a \<notin> match A ` ({<Suc ai} - {a}))"
      by (metis "*" Diff_idemp inj_on_insert)
    have nm: "match A a \<notin> match A ` ({<Suc ai} - {a})" using 4 unfolding invar2_def ran_def
        apply (clarsimp simp: set_eq_iff) by (metis)
    have invAM': "invAM A {<ai+1}"
      using invAM_match[OF invAM, of a] aai nm by (simp add: ** insert_absorb)
    show ?case using 4 invAM' by (simp add: \<alpha>update1 match_less_n insert_absorb nth_list_update)
  next
    case 2 thus ?case using 4 by auto
  qed
next
  case 5 (* outer invar and not b implies post *)
  thus ?case using pref_match_stable unfolding invAM_def invar1_def by(metis le_neq_implies_less)
next
  case (3 z v A B N ai a) (* preservation of inner invar *)
  let ?M = "{<ai+1} - {a}"
  have invAM: "invAM A ?M" and m: "matching A ?M" and A: "wf A" and M: "?M \<subseteq> {<n}"
    and matched: "N ! match A a" and as: "a \<le> ai \<and> ai < n" and invAB: "invAB2 A B N ?M"
    and v: "var2 A = v" using 3 by auto
  note invar = 3[THEN conjunct1, THEN conjunct1, unfolded invar2_def]
  let ?a = "B ! match A a"
  have a: "a < n \<and> a \<notin> ?M" using invar by auto
  have a': "?a \<in> ?M \<and> match A ?a = match A a"
    using invAB match_less_n[OF A] a matched by (metis \<alpha>_Some ranI)
  have "?M \<noteq> {<n}" and "?a < n" using M a a' atLeast0LessThan by auto
  have card: "card {<ai} = card ?M" using as by simp
  have *: "{<ai + 1} - {a} - {?a} \<union> {a} = {<ai + 1} - {?a}" using invar a' by auto
  show ?case
  proof (simp only: mem_Collect_eq prod.case, goal_cases)
    case 1
    show ?case
    proof ((rule;rule;rule), goal_cases)
      case unstab: 1
      note invAM' = invAM_swap[OF invAM a a' unstab]
      have inj_dom: "inj_on (\<alpha> B N) (dom (\<alpha> B N))" by (metis (mono_tags) domD inj_onI invAB)
      have invAB': "invAB (A[B ! match A a := A ! ?a + 1]) (\<alpha> (B[match A a := a]) N) ({<ai + 1} - {?a})"
        using invAB_swap[OF invAB[THEN conjunct1] a a' inj_dom] * match_less_n[OF A] a matched invAB
        by(simp add:\<alpha>update2)
      show ?case using invAM' invAB' invar a' unfolding * by (simp add: insert_absorb \<alpha>update2)
       (* case 2 show ?case using v var2_next[OF invAM'] \<open>a' < n\<close> * atLeast0LessThan by auto*)

      case 2
      show ?case using v var2_next[OF invAM'] * M \<open>?a < n\<close> a' by (metis subset_Diff_insert)
    next
      case stab: 3
      note invAM' = invAM_next[OF invAM a a' stab]
      have "\<forall>b. b < n \<and> N!b \<longrightarrow> a \<noteq> B!b" by (metis invAB ranI \<alpha>_Some a) 
      thus ?case using invAM' invar by (simp add: match_def)

      case 4
      show ?case using v var2_next[OF invAM'] a \<open>?M \<noteq> {<n}\<close> by blast
    qed
  qed
qed


subsubsection \<open>Algorithm 5.1: single-loop variant\<close>

definition invar2' where
[simp]: "invar2' A B N ai a \<equiv> (invAM A ({<ai+1} - {a}) \<and> invAB2 A B N ({<ai+1} - {a}) \<and> a \<le> ai \<and> ai \<le> n)"

lemma pres2':
assumes "invar2' A B N ai a" "ai < n" "var A ({<ai + 1} - {a}) = v"
and after[simp]: "b = match A a" "a' = B ! b" "A1 = A[a' := A ! a' + 1]" "A2 = A[a := A ! a + 1]"
shows
  "(\<not> N ! b \<longrightarrow>
    invar2' A (B[b := a]) (N[b := True]) (ai + 1) (ai + 1) \<and> var A ({<ai + 1 + 1} - {ai + 1}) < v) \<and>
   (N ! b \<longrightarrow>
    (Q ! match A a' \<turnstile> a < a' \<longrightarrow> invar2' A1 (B[b := a]) N ai a' \<and> var A1 ({<ai + 1} - {a'}) < v) \<and>
    (\<not> Q ! match A a' \<turnstile> a < a' \<longrightarrow> invar2' A2 B N ai a \<and> var A2 ({<ai + 1} - {a}) < v))"
proof -
  let ?M = "{<ai+1} - {a}"
  have invAM: "invAM A ?M" and m: "matching A ?M" and A: "wf A" and M: "?M \<subseteq> {<n}"
    and v: "var A ?M = v" and as: "a \<le> ai \<and> ai < n" and invAB: "invAB2 A B N ?M"
    using assms by auto
  note invar = assms(1)
  note pref_match1 = preferred_subset_match_if_invAM[OF invAM]
  have a: "a < n \<and> a \<notin> ?M" using as by (simp)
  show ?thesis (is "(\<not> ?matched \<longrightarrow> ?THEN) \<and> (?matched \<longrightarrow> ?ELSE)")
  proof (rule; rule)
    assume "\<not> ?matched"
    then have nm: "match A a \<notin> match A ` ?M" using invAB unfolding ran_def
      apply (clarsimp simp: set_eq_iff) by metis
    show ?THEN
    proof(rule conjI, goal_cases)
      have *: "{<ai + 1 + 1} - {ai + 1} = {<ai + 1}" by auto
      have **: "{<ai + 1} - {a} \<union> {a} = {<ai + 1}" using as by auto
      hence invAM': "invAM A {<ai+1}" using invAM_match[OF invAM a nm] by simp
      have invAB': "invAB2 A (B[match A a := a]) (N[match A a := True]) {<ai+1}"
        using invAB \<open>\<not> ?matched\<close> **
        by (simp add: A a \<alpha>update1 match_less_n nth_list_update)
      case 1 show ?case using invAM' as invAB' *
        by (simp add: Suc_le_eq plus_1_eq_Suc)
      case 2 show ?case
        using var_match[OF m M _ pref_match1, of a] a atLeast0LessThan * **
        unfolding v by (metis lessThan_iff)
    qed
  next
    assume matched: "?matched"
    let ?a = "B ! match A a"
    have a': "?a \<in> ?M \<and> match A ?a = match A a"
      using invAB match_less_n[OF A] a matched after by (metis \<alpha>_Some ranI)
    hence "?a < n" "a \<noteq> ?a" using a M atLeast0LessThan by auto
    have inj_dom: "inj_on (\<alpha> B N) (dom (\<alpha> B N))" by (metis (mono_tags) domD inj_onI invAB)
    show ?ELSE (is "(?pref \<longrightarrow> ?THEN) \<and> (\<not> ?pref \<longrightarrow> ?ELSE)")
    proof (rule; rule)
      assume ?pref
      show ?THEN
      proof (rule conjI, goal_cases)
        have *: "{<ai + 1} - {a} - {?a} \<union> {a} = {<ai + 1} - {?a}" using a a' as by auto
        have a'neq: "\<forall>b<n. b \<noteq> match A a \<longrightarrow> N!b \<longrightarrow> ?a \<noteq> B!b"
          using invAB a' by force
        have invAB': "invAB (A[B ! match A a := A ! ?a + 1]) (\<alpha> (B[match A a := a]) N) ({<ai + 1} - {?a})"
          using invAB_swap[OF invAB[THEN conjunct1] a a' inj_dom] * match_less_n[OF A] a matched invAB
          by(simp add:\<alpha>update2)
        case 1 show ?case using invAM_swap[OF invAM a a'] \<open>?pref\<close> invAB invAB' unfolding *
          using a' as by simp
        case 2
        have "card({<ai + 1} - {?a}) = card({<ai + 1} - {a})" using a a' as by auto
        thus ?case using v var_next[OF m M _ pref_match1, of ?a] \<open>?a < n\<close> a atLeast0LessThan
          by (metis Suc_eq_plus1 lessThan_iff var_def after)
      qed
    next
      assume "\<not> ?pref"
      show ?ELSE
      proof (rule conjI, goal_cases)
        case 1
        have "invAB2 (A[a := A ! a + 1]) B N ?M" using invAB a
          by (metis match_def nth_list_update_neq ranI)
        thus ?case using invAM_next[OF invAM a a'] \<open>\<not> ?pref\<close> invar after
          by (meson invar2'_def)
        case 2
        show ?case using a v var_next[OF m M _ pref_match1, of a] after
          by (metis Suc_eq_plus1 atLeast0LessThan lessThan_iff) 
      qed
    qed
  qed
qed

lemma Gale_Shapley5_1: "VARS A B N a a' ai b
 [ai = 0 \<and> a = 0 \<and> A = replicate n 0 \<and> length B = n \<and> N = replicate n False]
 WHILE ai < n
 INV { invar2' A B N ai a }
 VAR {var A ({<ai+1} - {a})}
 DO b := match A a;
  IF \<not> N ! b
  THEN B[b] := a; N[b] := True; ai := ai + 1; a := ai
  ELSE a' := B ! b;
       IF Q ! match A a' \<turnstile> a < a'
       THEN B[b] := a; A[a'] := A!a'+1; a := a'
       ELSE A[a] := A!a+1
       FI
  FI 
 OD
 [matching A {<n} \<and> stable A {<n} \<and> opti\<^sub>a A]"
proof (vcg_tc, goal_cases)
  case 1 thus ?case
   by(auto simp: pref_match_def P_set card_distinct match_def index_nth_id prefers_def opti\<^sub>a_def \<alpha>_def cong: conj_cong)
next
  case 3 thus ?case using pref_match_stable
    using atLeast0_lessThan_Suc by force
next
  case (2 v A B N a a' ai b)
  thus ?case using pres2'
    by (simp only:mem_Collect_eq prod.case) blast
qed


subsection \<open>Algorithm 6: replace \<open>Q\<close> by ranking \<open>R\<close>\<close>

lemma inner_to_outer:
assumes inv: "invar2 A B N ai a \<and> b = match A a" and not_b: "\<not> N ! b"
shows "invar1 A (B[b := a]) (N[b := True]) (ai+1)"
proof -
  note invAM = inv[unfolded invar2_def, THEN conjunct1,THEN conjunct1]
  have *: "{<Suc ai} = insert a ({<Suc ai} - {a})" using inv by (simp add: insert_absorb)
  have **: "inj_on (match A) {<Suc ai} = (inj_on (match A) ({<Suc ai} - {a}) \<and> match A a \<notin> match A ` ({<Suc ai} - {a}))"
    by (metis "*" Diff_idemp inj_on_insert)
  have nm: "match A a \<notin> match A ` ({<Suc ai} - {a})" using inv not_b unfolding invar2_def ran_def
      apply (clarsimp simp: set_eq_iff) by (metis)
  have invAM': "invAM A {<ai+1}"
    using invAM_match[OF invAM, of a] inv nm by (simp add: ** insert_absorb)
  show ?thesis using inv not_b invAM' match_less_n by (clarsimp simp: \<alpha>update1 insert_absorb nth_list_update)
qed

lemma inner_pres:
assumes R: "\<forall>b<n. \<forall>a1<n. \<forall>a2<n. R ! b ! a1 < R ! b ! a2 \<longleftrightarrow> Q ! b \<turnstile> a1 < a2" and
  inv: "invar2 A B N ai a" and m: "N ! b" and v: "var A {<ai} = v"
  and after: "A1 = A[a' := A ! a' + 1]" "A2 = A[a := A ! a + 1]"
    "a' = B!b" "r = R ! match A a'" "b = match A a"
shows "(r ! a < r ! a' \<longrightarrow> invar2 A1 (B[b:=a]) N ai a' \<and> var A1 {<ai} < v) \<and>
  (\<not> r ! a < r ! a' \<longrightarrow> invar2 A2 B N ai a \<and> var A2 {<ai} < v)"
proof -
  let ?M = "{<ai+1} - {a}"
  note [simp] = after
  note inv' = inv[unfolded invar2_def]
  have A: "wf A" and M: "?M \<subseteq> {<n}" and invAM: "invAM A ?M" and invAB: "invAB A (\<alpha> B N) ?M"
    and mat: "matching A ?M" and as: "a \<le> ai \<and> ai < n" using inv' by auto
  note pref_match1 = preferred_subset_match_if_invAM[OF invAM]
  let ?a = "B ! match A a"
  have a: "a < n \<and> a \<notin> ?M" using inv by auto
  have a': "?a \<in> ?M \<and> match A ?a = match A a"
    using invAB match_less_n[OF A] a m inv by (metis \<alpha>_Some ranI \<open>b = _\<close>)
  have "?M \<noteq> {<n}" and "?a < n" using M a a' atLeast0LessThan by auto
  have card: "card {<ai} = card ?M" using as by simp
  show ?thesis
  proof ((rule;rule;rule), goal_cases)
    have *: "{<ai + 1} - {a} - {?a} \<union> {a} = {<ai + 1} - {?a}" using inv a' by auto
    case 1
    hence unstab: "Q ! match A a' \<turnstile> a < a'"
      using R a a' as Q_set P_set match_less_n[OF A] n_def length_Q R by (simp)
    have inj_dom: "inj_on (\<alpha> B N) (dom (\<alpha> B N))" by (metis (mono_tags) domD inj_onI invAB)
    have invAB': "invAB A1 (\<alpha> (B[match A a := a]) N) ({<ai + 1} - {?a})"
      using invAB_swap[OF invAB a a' inj_dom] * match_less_n[OF A] a m
      by (simp add: \<alpha>update2 inv')
    show ?case using invAM_swap[OF invAM a a'] unstab invAB' inv a'
      unfolding * by (simp)
  next
    case 2
      show ?case using v var_next[OF mat M \<open>?M \<noteq> {<n}\<close> pref_match1 \<open>?a < n\<close>] card assms(5,7,9)
        by (metis Suc_eq_plus1 var_def)
  next
    have *: "\<forall>b. b < n \<and> N!b \<longrightarrow> a \<noteq> B!b" by (metis invAB ranI \<alpha>_Some a)
    case 3
    hence unstab: "\<not> Q ! match A a' \<turnstile> a < a'"
      using R a a' as Q_set P_set match_less_n[OF A] n_def length_Q
      by (simp add: ranking_iff_pref)
    then show ?case using invAM_next[OF invAM a a'] 3 inv * by (simp add: match_def)
  next
    case 4
      show ?case using v var_next[OF mat M \<open>?M \<noteq> {<n}\<close> pref_match1, of a] a card assms(6)
        by (metis Suc_eq_plus1 var_def)
  qed
qed

text \<open>First, the `old' version with the more complicated inner variant:\<close>

lemma Gale_Shapley6:
assumes "R = map ranking Q"
shows
"VARS A B N ai a a' b r
 [ai = 0 \<and> A = replicate n 0 \<and> length B = n \<and> N = replicate n False]
 WHILE ai < n
 INV { invar1 A B N ai }
 VAR {z = n - ai}
 DO a := ai; b := match A a;
  WHILE N ! b
  INV { invar2 A B N ai a \<and> b = match A a \<and> z = n-ai }
  VAR {var A {<ai}}
  DO a' := B ! b; r := R ! match A a';
     IF r ! a < r ! a'
     THEN B[b] := a; A[a'] := A!a'+1; a := a'
     ELSE A[a] := A!a+1
     FI;
     b := match A a
  OD;
  B[b] := a; N[b] := True; ai := ai+1
 OD
 [matching A {<n} \<and> stable A {<n} \<and> opti\<^sub>a A]"
proof (vcg_tc, goal_cases)
  case 1 thus ?case  (* outer invar holds initially *)
   by(auto simp: stable_def pref_match_def P_set card_distinct match_def index_nth_id prefers_def opti\<^sub>a_def \<alpha>_def cong: conj_cong)
next
  case 2 (* outer invar and b implies inner invar *)
  thus ?case by (auto simp: atLeastLessThanSuc_atLeastAtMost simp flip: atLeastLessThan_eq_atLeastAtMost_diff)
next
  case 3 (* preservation of inner invar *)
  have R: "\<forall>b<n. \<forall>a1<n. \<forall>a2<n. R ! b ! a1 < R ! b ! a2 \<longleftrightarrow> Q ! b \<turnstile> a1 < a2"
    by (simp add: Q_set \<open>R = _\<close> length_Q ranking_iff_pref)
  show ?case
  proof (simp only: mem_Collect_eq prod.case, goal_cases)
    case 1 show ?case using inner_pres[OF R _ _ refl refl refl] 3 by blast
  qed
next
  case 4 (* inner invar' and not b implies outer invar *)
  show ?case
  proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
    case 1 show ?case using 4 inner_to_outer by blast
  next
    case 2 thus ?case using 4 by auto
  qed
next
  case 5 (* outer invar and not b implies post *)
  thus ?case using pref_match_stable unfolding invAM_def invar1_def by(metis le_neq_implies_less)
qed

lemma inner_pres_var2:
assumes R: "\<forall>b<n. \<forall>a1<n. \<forall>a2<n. R ! b ! a1 < R ! b ! a2 \<longleftrightarrow> Q ! b \<turnstile> a1 < a2" and
  inv: "invar2 A B N ai a" and m: "N ! b" and v: "var2 A = v"
  and after: "A1 = A[a' := A ! a' + 1]" "A2 = A[a := A ! a + 1]"
    "a' = B!b" "r = R ! match A a'" "b = match A a"
shows "(r ! a < r ! a' \<longrightarrow> invar2 A1 (B[b:=a]) N ai a' \<and> var2 A1 < v) \<and>
  (\<not> r ! a < r ! a' \<longrightarrow> invar2 A2 B N ai a \<and> var2 A2 < v)"
proof -
  let ?M = "{<ai+1} - {a}"
  note [simp] = after
  note inv' = inv[unfolded invar2_def]
  have A: "wf A" and M: "?M \<subseteq> {<n}" and invAM: "invAM A ?M" and invAB: "invAB A (\<alpha> B N) ?M"
    and mat: "matching A ?M" and as: "a \<le> ai \<and> ai < n" using inv' by auto
  let ?a = "B ! match A a"
  have a: "a < n \<and> a \<notin> ?M" using inv by auto
  have a': "?a \<in> ?M \<and> match A ?a = match A a"
    using invAB match_less_n[OF A] a m inv by (metis \<alpha>_Some ranI \<open>b = _\<close>)
  have "?M \<noteq> {<n}" and "?a < n" using M a a' atLeast0LessThan by auto
  have card: "card {<ai} = card ?M" using as by simp
  show ?thesis
  proof ((rule;rule;rule), goal_cases)
    have *: "{<ai + 1} - {a} - {?a} \<union> {a} = {<ai + 1} - {?a}" using inv a' by auto
    note invAM' =  invAM_swap[OF invAM a a']
    case 1
    hence unstab: "Q ! match A a' \<turnstile> a < a'"
      using R a a' as Q_set P_set match_less_n[OF A] n_def length_Q R by (simp)
    have inj_dom: "inj_on (\<alpha> B N) (dom (\<alpha> B N))" by (metis (mono_tags) domD inj_onI invAB)
    have invAB': "invAB A1 (\<alpha> (B[match A a := a]) N) ({<ai + 1} - {?a})"
      using invAB_swap[OF invAB a a' inj_dom] * match_less_n[OF A] a m
      by (simp add: \<alpha>update2 inv')
    show ?case using invAM' unstab invAB' inv a' unfolding * by (simp)

    case 2
      show ?case using v var2_next[OF invAM'] assms(5,7,9) * M \<open>?a < n\<close> a'
        by (metis subset_Diff_insert unstab)
  next
    have *: "\<forall>b. b < n \<and> N!b \<longrightarrow> a \<noteq> B!b" by (metis invAB ranI \<alpha>_Some a)
    note invAM' = invAM_next[OF invAM a a']
    case 3
    hence unstab: "\<not> Q ! match A a' \<turnstile> a < a'"
      using R a a' as Q_set P_set match_less_n[OF A] n_def length_Q
      by (simp add: ranking_iff_pref)
    then show ?case using invAM' 3 inv * by (simp add: match_def)

    case 4
      show ?case using v var2_next[OF invAM'] a assms(6,7,9) \<open>?M \<noteq> {<n}\<close> unstab by fastforce
  qed
qed

text \<open>The definitive version with variant @{const var2}:\<close>

lemma Gale_Shapley6_var2:
assumes "R = map ranking Q"
shows
"VARS A B N ai a a' b r
 [ai = 0 \<and> A = replicate n 0 \<and> length B = n \<and> N = replicate n False]
 WHILE ai < n
 INV { invar1 A B N ai }
 VAR {z = n - ai}
 DO a := ai; b := match A a;
  WHILE N ! b
  INV { invar2 A B N ai a \<and> b = match A a \<and> z = n-ai }
  VAR {var2 A}
  DO a' := B ! b; r := R ! match A a';
     IF r ! a < r ! a'
     THEN B[b] := a; A[a'] := A!a'+1; a := a'
     ELSE A[a] := A!a+1
     FI;
     b := match A a
  OD;
  B[b] := a; N[b] := True; ai := ai+1
 OD
 [matching A {<n} \<and> stable A {<n} \<and> opti\<^sub>a A]"
proof (vcg_tc, goal_cases)
  case 1 thus ?case  (* outer invar holds initially *)
   by(auto simp: stable_def pref_match_def P_set card_distinct match_def index_nth_id prefers_def opti\<^sub>a_def \<alpha>_def cong: conj_cong)
next
  case 2 (* outer invar and b implies inner invar *)
  thus ?case by (auto simp: atLeastLessThanSuc_atLeastAtMost simp flip: atLeastLessThan_eq_atLeastAtMost_diff)
next
  case 3 (* preservation of inner invar *)
  have R: "\<forall>b<n. \<forall>a1<n. \<forall>a2<n. R ! b ! a1 < R ! b ! a2 \<longleftrightarrow> Q ! b \<turnstile> a1 < a2"
    by (simp add: Q_set \<open>R = _\<close> length_Q ranking_iff_pref)
  show ?case
  proof (simp only: mem_Collect_eq prod.case, goal_cases)
    case 1 show ?case using inner_pres_var2[OF R _ _ refl refl refl] 3 by blast
  qed
next
  case 4 (* inner invar' and not b implies outer invar *)
  show ?case
  proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
    case 1 show ?case using 4 inner_to_outer by blast
  next
    case 2 thus ?case using 4 by auto
  qed
next
  case 5 (* outer invar and not b implies post *)
  thus ?case using pref_match_stable unfolding invAM_def invar1_def by(metis le_neq_implies_less)
qed

text \<open>A less precise version where the inner variant does not depend on variables changed in the outer loop.
Thus the inner variant is an upper bound on the number of executions of the inner loop test/body.
Superseded by the @{const var2} version.\<close>

lemma var0_next2:
assumes "wf (A[a' := A ! a' + 1])" "a' < n"
shows "var0 (A[a' := A ! a' + 1]) {<n} < var0 A {<n}"
proof -
  let ?A = "A[a' := A ! a' + 1]"
  have 0: "card {<n} = n" by simp
  have *: "(\<Sum>a<n. ?A!a) + card {<n} \<le> n^2"
    using sumA_ub[OF assms(1)] 0 by (simp add: power2_eq_square algebra_simps le_diff_conv2)
  have "(\<Sum>a<n. A!a) < (\<Sum>a<n. ?A!a) "
    using assms sum.remove[of "{<n}" a' "(!) A"]
    by(simp add: nth_list_update sum.If_cases lessThan_atLeast0 Diff_eq)
  thus ?thesis using * unfolding var0_def by linarith
qed


lemma inner_pres2:
assumes R: "\<forall>b<n. \<forall>a1<n. \<forall>a2<n. R ! b ! a1 < R ! b ! a2 \<longleftrightarrow> Q ! b \<turnstile> a1 < a2" and
  inv: "invar2 A B N ai a" and m: "N ! b" and v: "var0 A {<n} = v"
  and after: "A1 = A[a' := A ! a' + 1]" "A2 = A[a := A ! a + 1]"
    "a' = B!b" "r = R ! match A a'" "b = match A a"
shows "(r ! a < r ! a' \<longrightarrow> invar2 A1 (B[b:=a]) N ai a' \<and> var0 A1 {<n} < v) \<and>
  (\<not> r ! a < r ! a' \<longrightarrow> invar2 A2 B N ai a \<and> var0 A2 {<n} < v)"
proof -
  let ?M = "{<ai+1} - {a}"
  note [simp] = after
  note inv' = inv[unfolded invar2_def]
  have A: "wf A" and M: "?M \<subseteq> {<n}" and invAM: "invAM A ?M" and invAB: "invAB A (\<alpha> B N) ?M"
    and mat: "matching A ?M"
    and as: "a \<le> ai \<and> ai < n" using inv' by auto
  note pref_match1 = preferred_subset_match_if_invAM[OF invAM]
  let ?a = "B ! match A a"
  have a: "a < n \<and> a \<notin> ?M" using inv by auto
  have a': "?a \<in> ?M \<and> match A ?a = match A a"
    using invAB match_less_n[OF A] a m inv by (metis \<alpha>_Some ranI \<open>b = _\<close>)
  have "?M \<noteq> {<n}" and "?a < n" using M a a' atLeast0LessThan by auto
  have card: "card {<ai} = card ?M" using as by simp
  show ?thesis
  proof ((rule;rule;rule), goal_cases)
    have *: "{<ai + 1} - {a} - {?a} \<union> {a} = {<ai + 1} - {?a}" using inv a' by auto
    case 1
    hence unstab: "Q ! match A a' \<turnstile> a < a'"
      using R a a' as Q_set P_set match_less_n[OF A] n_def length_Q R by (simp)
    have inj_dom: "inj_on (\<alpha> B N) (dom (\<alpha> B N))" by (metis (mono_tags) domD inj_onI invAB)
    have invAB': "invAB A1 (\<alpha> (B[match A a := a]) N) ({<ai + 1} - {?a})"
      using invAB_swap[OF invAB a a' inj_dom] * match_less_n[OF A] a m
      by (simp add: \<alpha>update2 inv')
    show ?case using invAM_swap[OF invAM a a'] unstab invAB' inv a'
      unfolding * by (simp add: insert_absorb \<alpha>update2)
  next
    case 2
    hence unstab: "Q ! match A a' \<turnstile> a < a'"
      using R a a' as Q_set P_set match_less_n[OF A] n_def length_Q R by (simp)
    from invAM_swap[OF invAM a a'] unstab have wf: "wf (A[a' := A ! a' + 1])" by auto
    show ?case using v var0_next2[OF wf] using \<open>B ! match A a < n\<close> assms(5,7,9) by blast
  next
    have *: "\<forall>b. b < n \<and> N!b \<longrightarrow> a \<noteq> B!b" by (metis invAB ranI \<alpha>_Some a)
    case 3
    hence unstab: "\<not> Q ! match A a' \<turnstile> a < a'"
      using R a a' as Q_set P_set match_less_n[OF A] n_def length_Q
      by (simp add: ranking_iff_pref)
    then show ?case using invAM_next[OF invAM a a'] 3 inv * by (simp add: match_def)
  next
    case 4
    hence unstab: "\<not> Q ! match A a' \<turnstile> a < a'"
      using R a a' as Q_set P_set match_less_n[OF A] n_def length_Q
      by (simp add: ranking_iff_pref)
    from invAM_next[OF invAM a a'] unstab have wf: "wf (A[a := A ! a + 1])" by auto
    show ?case using v var0_next2[OF wf] a using assms(6) by presburger
  qed
qed

lemma Gale_Shapley6':
assumes "R = map ranking Q"
shows
"VARS A B N ai a a' b r
 [ai = 0 \<and> A = replicate n 0 \<and> length B = n \<and> N = replicate n False]
 WHILE ai < n
 INV { invar1 A B N ai }
 VAR {z = n - ai}
 DO a := ai; b := match A a;
  WHILE N ! b
  INV { invar2 A B N ai a \<and> b = match A a \<and> z = n-ai }
  VAR {var0 A {<n}}
  DO a' := B ! b; r := R ! match A a';
     IF r ! a < r ! a'
     THEN B[b] := a; A[a'] := A!a'+1; a := a'
     ELSE A[a] := A!a+1
     FI;
     b := match A a
  OD;
  B[b] := a; N[b] := True; ai := ai+1
 OD
 [matching A {<n} \<and> stable A {<n} \<and> opti\<^sub>a A]"
proof (vcg_tc, goal_cases)
  case 1 thus ?case  (* outer invar holds initially *)
   by(auto simp: stable_def pref_match_def P_set card_distinct match_def index_nth_id prefers_def opti\<^sub>a_def \<alpha>_def cong: conj_cong)
next
  case 2 (* outer invar and b implies inner invar *)
  thus ?case by (auto simp: atLeastLessThanSuc_atLeastAtMost simp flip: atLeastLessThan_eq_atLeastAtMost_diff)
next
  case 3 (* preservation of inner invar *)
  have R: "\<forall>b<n. \<forall>a1<n. \<forall>a2<n. R ! b ! a1 < R ! b ! a2 \<longleftrightarrow> Q ! b \<turnstile> a1 < a2"
    by (simp add: Q_set \<open>R = _\<close> length_Q ranking_iff_pref)
  show ?case
  proof (simp only: mem_Collect_eq prod.case, goal_cases)
    case 1 show ?case using inner_pres2[OF R _ _ refl refl refl] 3 by blast
  qed
next
  case 4 (* inner invar' and not b implies outer invar *)
  show ?case
  proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
    case 1 show ?case using 4 inner_to_outer by blast
  next
    case 2 thus ?case using 4 by auto
  qed
next
  case 5 (* outer invar and not b implies post *)
  thus ?case using pref_match_stable unfolding invAM_def invar1_def by(metis le_neq_implies_less)
qed


subsubsection \<open>Algorithm 6.1: single-loop variant\<close>

lemma R_iff_P:
assumes "R = map ranking Q" "invar2' A B N ai a" "ai < n" "N ! match A a"
shows "(R ! match A (B ! match A a) ! a < R ! match A (B ! match A a) ! (B ! match A a)) =
  (Q ! match A (B ! match A a) \<turnstile> a < B ! match A a)"
proof -
  have R: "\<forall>b<n. \<forall>a1<n. \<forall>a2<n. R ! b ! a1 < R ! b ! a2 \<longleftrightarrow> Q ! b \<turnstile> a1 < a2"
    by (simp add: Q_set \<open>R = _\<close> length_Q ranking_iff_pref)
  let ?M = "{<ai+1} - {a}"
  have A: "wf A" and M: "?M \<subseteq> {<n}" and as: "a < n" and invAB: "invAB2 A B N ?M"
      using assms(2,3) by auto
  have a': "B ! match A a \<in> ?M"
    using invAB match_less_n[OF A] as \<open>N!match A a\<close> by (metis \<alpha>_Some ranI)
  hence "B ! match A a < n" using M by auto
  thus ?thesis using assms R match_less_n by auto
qed


lemma Gale_Shapley6_1:
assumes "R = map ranking Q"
shows "VARS A B N a a' ai b r
 [ai = 0 \<and> a = 0 \<and> A = replicate n 0 \<and> length B = n \<and> N = replicate n False]
 WHILE ai < n
 INV { invar2' A B N ai a }
 VAR {var A ({<ai+1} - {a})}
 DO b := match A a;
  IF \<not> N ! b
  THEN B[b] := a; N[b] := True; ai := ai + 1; a := ai
  ELSE a' := B ! b; r := R ! match A a';
       IF r ! a < r ! a'
       THEN B[b] := a; A[a'] := A!a'+1; a := a'
       ELSE A[a] := A!a+1
       FI
  FI 
 OD
 [matching A {<n} \<and> stable A {<n} \<and> opti\<^sub>a A]"
proof (vcg_tc, goal_cases)
  case 1 thus ?case
   by(auto simp: pref_match_def P_set card_distinct match_def index_nth_id prefers_def opti\<^sub>a_def \<alpha>_def cong: conj_cong)
next
  case 3 thus ?case using pref_match_stable atLeast0_lessThan_Suc by force
next
  case (2 v A B N a a' ai)
  have R': "N ! match A a \<Longrightarrow>
    (R ! match A (B ! match A a) ! a < R ! match A (B ! match A a) ! (B ! match A a)) =
     (Q ! match A (B ! match A a) \<turnstile> a < B ! match A a)"
    using R_iff_P 2 assms by blast
  show ?case
    apply(simp only:mem_Collect_eq prod.case)
    using 2 R' pres2'[of A B N ai a] by presburger
qed

(* TODO: rm? *)
lemma Gale_Shapley6_1_explicit:
assumes "R = map ranking Q"
shows "VARS A B N a a' ai b r
 [ai = 0 \<and> a = 0 \<and> A = replicate n 0 \<and> length B = n \<and> N = replicate n False]
 WHILE ai < n
 INV { invar2' A B N ai a }
 VAR {var A ({<ai+1} - {a})}
 DO b := match A a;
  IF \<not> N ! b
  THEN B[b] := a; N[b] := True; ai := ai + 1; a := ai
  ELSE a' := B ! b; r := R ! match A a';
       IF r ! a < r ! a'
       THEN B[b] := a; A[a'] := A!a'+1; a := a'
       ELSE A[a] := A!a+1
       FI
  FI 
 OD
 [matching A {<n} \<and> stable A {<n} \<and> opti\<^sub>a A]"
proof (vcg_tc, goal_cases)
  case 1 thus ?case
   by(auto simp: pref_match_def P_set card_distinct match_def index_nth_id prefers_def opti\<^sub>a_def \<alpha>_def cong: conj_cong)
next
  case 3 thus ?case using pref_match_stable atLeast0_lessThan_Suc by force
next
  case (2 v A B N a a' ai b)
  let ?M = "{<ai+1} - {a}"
  have invAM: "invAM A ?M" and m: "matching A ?M" and A: "wf A" and M: "?M \<subseteq> {<n}"
    and pref_match: "pref_match A ?M"
    and v: "var A ?M = v" and as: "a \<le> ai \<and> ai < n" and invAB: "invAB2 A B N ?M"
    using 2 by auto
  note invar = 2[THEN conjunct1,THEN conjunct1]
  note pref_match' = pref_match[THEN pref_match'_iff[OF A, THEN iffD2]]
  hence pref_match1: "\<forall>a<n. preferred A a \<subseteq> match A ` ?M" unfolding pref_match'_def by blast
  have a: "a < n \<and> a \<notin> ?M" using as by (simp)
  show ?case (is "(?not_matched \<longrightarrow> ?THEN) \<and> (\<not> ?not_matched \<longrightarrow> ?ELSE)")
  proof (rule; rule)
    assume ?not_matched
    then have nm: "match A a \<notin> match A ` ?M" using invAB unfolding ran_def
      apply (clarsimp simp: set_eq_iff) by metis
    show ?THEN
    proof(simp only:mem_Collect_eq prod.case, rule conjI, goal_cases)
      have *: "{<ai + 1 + 1} - {ai + 1} = {<ai + 1}" by auto
      have **: "{<ai + 1} - {a} \<union> {a} = {<ai + 1}" using as by auto
      hence invAM': "invAM A {<ai+1}" using invAM_match[OF invAM a nm] by simp
      have invAB': "invAB2 A (B[match A a := a]) (N[match A a := True]) {<ai+1}"
        using invAB \<open>?not_matched\<close> **
        by (simp add: A a \<alpha>update1 match_less_n nth_list_update)
      case 1 show ?case using invAM' as invAB' *
        by (simp add: Suc_le_eq plus_1_eq_Suc)
      case 2 show ?case
        using var_match[OF m M _ pref_match1, of a] a atLeast0LessThan * **
        unfolding v by (metis lessThan_iff)
    qed
  next
    assume matched: "\<not> ?not_matched"
    let ?a = "B ! match A a"
    have a': "?a \<in> ?M \<and> match A ?a = match A a"
      using invAB match_less_n[OF A] a matched by (metis \<alpha>_Some ranI)
    hence "?a < n" "a \<noteq> ?a" using a M atLeast0LessThan by auto
    have inj_dom: "inj_on (\<alpha> B N) (dom (\<alpha> B N))" by (metis (mono_tags) domD inj_onI invAB)
    show ?ELSE (is "(?pref \<longrightarrow> ?THEN) \<and> (\<not> ?pref \<longrightarrow> ?ELSE)")
    proof (rule; rule)
      assume ?pref
      show ?THEN
      proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
        have *: "{<ai + 1} - {a} - {?a} \<union> {a} = {<ai + 1} - {?a}" using a a' as by auto
        have a'neq: "\<forall>b<n. b \<noteq> match A a \<longrightarrow> N!b \<longrightarrow> ?a \<noteq> B!b"
          using invAB a' by force
        have invAB': "invAB (A[B ! match A a := A ! ?a + 1]) (\<alpha> (B[match A a := a]) N) ({<ai + 1} - {?a})"
          using invAB_swap[OF invAB[THEN conjunct1] a a' inj_dom] * match_less_n[OF A] a matched invAB
          by(simp add:\<alpha>update2)
        have pref: "Q ! match A ?a \<turnstile> a < ?a" using A Q_set \<open>?a < n\<close> \<open>?pref\<close> a assms length_Q
          by(auto simp: match_less_n ranking_iff_pref)
        case 1 show ?case (* changed *)
          using invAM_swap[OF invAM a a' pref] invAB invAB' a' as unfolding *
          by (simp add: match_less_n ranking_iff_pref)
        case 2
        have "card({<ai + 1} - {?a}) = card({<ai + 1} - {a})" using a a' as by auto
        thus ?case using v var_next[OF m M _ pref_match1, of ?a] \<open>?a < n\<close> a atLeast0LessThan
          by (metis Suc_eq_plus1 lessThan_iff var_def)
      qed
    next
      assume "\<not> ?pref"
      show ?ELSE
      proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
        case 1
        have "invAB2 (A[a := A ! a + 1]) B N ?M" using invAB a
          by (metis match_def nth_list_update_neq ranI)
        thus ?case using invAM_next[OF invAM a a'] \<open>\<not> ?pref\<close>  \<open>B ! match A a < n\<close> Q_set 2 assms
          by (simp add: invar2'_def length_Q match_less_n ranking_iff_pref) (* changed *)
        case 2
        show ?case using a v var_next[OF m M _ pref_match1, of a]
          by (metis Suc_eq_plus1 atLeast0LessThan lessThan_iff) 
      qed
    qed
  qed
qed

end


subsection \<open>Functional implementation\<close>

definition
"gs_inner P R N =
  while (\<lambda>(A,B,a,b). N!b)
    (\<lambda>(A,B,a,b).
      let a' = B ! b;
          r = R ! (P ! a' ! (A ! a')) in
      let (A, B, a) =
        if r ! a < r ! a'
        then (A[a' := A!a' + 1], B[b := a], a')
        else (A[a := A!a + 1], B, a)
      in (A, B, a, P ! a ! (A ! a)))"

definition
"gs n P R =
  while (\<lambda>(A,B,N,ai). ai < n)
   (\<lambda>(A,B,N,ai).
     let (A,B,a,b) = gs_inner P R N (A, B, ai, P ! ai ! (A ! ai))
     in (A, B[b:=a], N[b:=True], ai+1))
  (replicate n 0, replicate n 0, replicate n False,0)"

definition
"gs1 n P R =
  while (\<lambda>(A,B,N,ai,a). ai < n)
   (\<lambda>(A,B,N,ai,a).
     let b = P ! a ! (A ! a) in
     if \<not> N ! b
     then (A, B[b := a], N[b := True], ai+1, ai+1)
     else let a' = B ! b; r = R ! (P ! a' ! (A ! a')) in
       if r ! a < r ! a'
       then (A[a' := A!a'+1], B[b := a], N, ai, a')
       else (A[a := A!a+1], B, N, ai, a))
  (replicate n 0, replicate n 0, replicate n False, 0, 0)"

context Pref
begin

lemma gs_inner:
assumes "R = map ranking Q"
assumes "invar2 A B N ai a" "b = match A a"
shows "gs_inner P R N (A, B, a, b) = (A',B',a',b') \<longrightarrow> invar1 A' (B'[b' := a']) (N[b' := True]) (ai+1)"
unfolding gs_inner_def
proof(rule while_rule2[where P = "\<lambda>(A,B,a,b). invar2 A B N ai a \<and> b = match A a"
 and r = "measure (%(A, B, a, b). Pref.var P A {<ai})"], goal_cases)
  case 1
  show ?case using assms unfolding var_def by simp
next
  case inv: (2 s)
  obtain A B a b where s: "s =  (A, B, a, b)"
    using prod_cases4 by blast
  have R: "\<forall>b<n. \<forall>a1<n. \<forall>a2<n. R ! b ! a1 < R ! b ! a2 \<longleftrightarrow> Q ! b \<turnstile> a1 < a2"
    by (simp add: Q_set \<open>R = _\<close> length_Q ranking_iff_pref)
  show ?case
  proof(rule, goal_cases)
    case 1 show ?case
    using inv apply(simp only: s prod.case Let_def split: if_split)
    using inner_pres[OF R _ _ refl refl refl refl refl, of A B N ai a b]
    unfolding invar2_def match_def by presburger
    case 2 show ?case
    using inv apply(simp only: s prod.case Let_def in_measure split: if_split)
    using inner_pres[OF R _ _ refl refl refl refl refl, of A B N ai a b]
    unfolding invar2_def match_def by presburger
  qed
next
  case 3
  show ?case
  proof (rule, goal_cases)
    case 1 show ?case by(rule inner_to_outer[OF 3[unfolded 1 prod.case]])
  qed
next
  case 4
  show ?case by simp
qed

lemma gs: assumes "R = map ranking Q"
shows "gs n P R = (A,BNai) \<longrightarrow> matching A {<n} \<and> stable A {<n} \<and> opti\<^sub>a A"
unfolding gs_def
proof(rule while_rule2[where P = "\<lambda>(A,B,N,ai). invar1 A B N ai"
  and r = "measure(\<lambda>(A,B,N,ai). n - ai)"], goal_cases)
  case 1 show ?case
   by(auto simp: stable_def pref_match_def P_set card_distinct match_def index_nth_id prefers_def opti\<^sub>a_def \<alpha>_def cong: conj_cong)
next
  case (2 s)
  obtain A B N ai where s: "s =  (A, B, N, ai)"
    using prod_cases4 by blast
  have 1: "invar2 A B N ai ai" using 2 s
    by (auto simp: atLeastLessThanSuc_atLeastAtMost simp flip: atLeastLessThan_eq_atLeastAtMost_diff)
  show ?case using 2 s gs_inner[OF \<open>R = _ \<close> 1] by (auto simp: match_def simp del: invar1_def split: prod.split)
next
  case 3
  thus ?case using pref_match_stable by auto
next
  case 4
  show ?case by simp
qed


lemma gs1: assumes "R = map ranking Q"
shows "gs1 n P R = (A,BNaia) \<longrightarrow> matching A {<n} \<and> stable A {<n} \<and> opti\<^sub>a A"
unfolding gs1_def
proof(rule while_rule2[where P = "\<lambda>(A,B,N,ai,a). invar2' A B N ai a"
  and r = "measure (%(A, B, N, ai, a). Pref.var P A ({<ai+1} - {a}))"], goal_cases)
  case 1 show ?case
    by(auto simp: stable_def pref_match_def P_set card_distinct match_def index_nth_id prefers_def opti\<^sub>a_def \<alpha>_def cong: conj_cong)
next
  case (2 s)
  obtain A B N ai a where s: "s =  (A, B, N, ai, a)"
    using prod_cases5 by blast
  hence 1: "invar2' A B N ai a" "ai < n" using 2 by (simp_all)
  have R': "N ! match A a \<Longrightarrow>
    (R ! match A (B ! match A a) ! a < R ! match A (B ! match A a) ! (B ! match A a)) =
     (Q ! match A (B ! match A a) \<turnstile> a < B ! match A a)"
    using R_iff_P[OF assms 1] by linarith
  show ?case 
    using 1 R' pres2'[OF 1]
    apply(simp only: s mem_Collect_eq prod.case Let_def in_measure match_def split: if_split)
    by blast
next
  case (3 s)
  obtain B N ai a where "BNaia =  (B, N, ai, a)"
    using prod_cases4 by blast
  with 3 show ?case
    using pref_match_stable atLeast0_lessThan_Suc by force
next
  case 4
  show ?case by simp
qed


end


subsection \<open>Executable functional Code\<close>

definition
"Gale_Shapley P Q = (if Pref P Q then Some (fst (gs (length P) P (map ranking Q))) else None)"

theorem gs: "\<lbrakk> Pref P Q; n = length P \<rbrakk> \<Longrightarrow>
 \<exists>A. Gale_Shapley P Q = Some(A) \<and> Pref.matching P A {<n} \<and>
   Pref.stable P Q A {<n} \<and> Pref.opti\<^sub>a P Q A"
unfolding Gale_Shapley_def using Pref.gs
by (metis fst_conv surj_pair)

declare Pref_def [code]

definition
"Gale_Shapley1 P Q = (if Pref P Q then Some (fst (gs1 (length P) P (map ranking Q))) else None)"

theorem gs1: "\<lbrakk> Pref P Q; n = length P \<rbrakk> \<Longrightarrow>
 \<exists>A. Gale_Shapley1 P Q = Some(A) \<and> Pref.matching P A {<n} \<and>
   Pref.stable P Q A {<n} \<and> Pref.opti\<^sub>a P Q A"
unfolding Gale_Shapley1_def using Pref.gs1
by (metis fst_conv surj_pair)

declare Pref_def [code]

text \<open>Two examples from Gusfield and Irving:\<close>

lemma "Gale_Shapley
  [[3,0,1,2], [1,2,0,3], [1,3,2,0], [2,0,3,1]]
  [[3,0,2,1], [0,2,1,3], [0,1,2,3], [3,0,2,1]]
  = Some[0,1,0,1]"
by eval

lemma "Gale_Shapley1
  [[4,6,0,1,5,7,3,2], [1,2,6,4,3,0,7,5], [7,4,0,3,5,1,2,6], [2,1,6,3,0,5,7,4],
   [6,1,4,0,2,5,7,3], [0,5,6,4,7,3,1,2], [1,4,6,5,2,3,7,0], [2,7,3,4,6,1,5,0]]
  [[4,2,6,5,0,1,7,3], [7,5,2,4,6,1,0,3], [0,4,5,1,3,7,6,2], [7,6,2,1,3,0,4,5],
   [5,3,6,2,7,0,1,4], [1,7,4,2,3,5,6,0], [6,4,1,0,7,5,3,2], [6,3,0,4,1,2,5,7]]
  = Some [0, 1, 0, 5, 0, 0, 0, 2]"
by eval

end