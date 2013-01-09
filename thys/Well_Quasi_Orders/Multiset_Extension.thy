(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Multiset Extension of Orders (as Binary Predicates) *}

(*TODO: move theory (and maybe rename)*)

theory Multiset_Extension
imports
  "Restricted_Predicates"
  "~~/src/HOL/Library/Multiset"
begin

definition multisets :: "'a set \<Rightarrow> 'a multiset set" where
  "multisets A \<equiv> {M. set_of M \<subseteq> A}"

lemma empty_multisets [simp]:
  "{#} \<in> multisets F"
  by (simp add: multisets_def)

lemma multisets_union [simp]:
  "M \<in> multisets A \<Longrightarrow> N \<in> multisets A \<Longrightarrow> M + N \<in> multisets A"
  by (auto simp: multisets_def)

definition mulex1 :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "mulex1 P = (\<lambda>M N. (M, N) \<in> mult1 {(x, y). P x y})"

lemma mulex1_empty [iff]:
  "mulex1 P M {#} \<longleftrightarrow> False"
  using not_less_empty [of M "{(x, y). P x y}"]
  by (auto simp: mulex1_def)

lemma mulex1_add: "mulex1 P N (M0 + {#a#}) \<Longrightarrow>
  (\<exists>M. mulex1 P M M0 \<and> N = M + {#a#}) \<or>
  (\<exists>K. (\<forall>b. b \<in># K \<longrightarrow> P b a) \<and> N = M0 + K)"
  using less_add [of N M0 a "{(x, y). P x y}"]
  by (auto simp: mulex1_def)

lemma mulex1_self_add_right [simp]:
  "mulex1 P A (A + {#a#})"
proof -
  let ?R = "{(x, y). P x y}"
  thm mult1_def
  have "A + {#a#} = A + {#a#}" by simp
  moreover have "A = A + {#}" by simp
  moreover have "\<forall>b. b \<in># {#} \<longrightarrow> (b, a) \<in> ?R" by simp
  ultimately have "(A, A + {#a#}) \<in> mult1 ?R"
    unfolding mult1_def by blast
  then show ?thesis by (simp add: mulex1_def)
qed

lemma empty_mult1 [simp]:
  "({#}, {#a#}) \<in> mult1 R"
proof -
  have "{#a#} = {#} + {#a#}" by simp
  moreover have "{#} = {#} + {#}" by simp
  moreover have "\<forall>b. b \<in># {#} \<longrightarrow> (b, a) \<in> R" by simp
  ultimately show ?thesis unfolding mult1_def by force
qed

lemma empty_mulex1 [simp]:
  "mulex1 P {#} {#a#}"
  using empty_mult1 [of a "{(x, y). P x y}"] by (simp add: mulex1_def)

definition
  mulex_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool"
where
  "mulex_on P A = (restrict_to (mulex1 P) (multisets A))\<^sup>+\<^sup>+"

lemma mulex_on_self_add_singleton_right [simp]:
  assumes "a \<in> A" and "M \<in> multisets A"
  shows "mulex_on P A M (M + {#a#})"
proof -
  have "mulex1 P M (M + {#a#})" by simp
  with assms have "restrict_to (mulex1 P) (multisets A) M (M + {#a#})"
    by (auto simp: multisets_def)
  then show ?thesis unfolding mulex_on_def by blast
qed

lemma singleton_multisets [iff]:
  "{#x#} \<in> multisets A \<longleftrightarrow> x \<in> A"
  by (auto simp: multisets_def)

lemma union_multisetsD:
  assumes "M + N \<in> multisets A"
  shows "M \<in> multisets A \<and> N \<in> multisets A"
  using assms by (auto simp: multisets_def)
lemma mulex_on_imp_multisets:
  assumes "mulex_on P F M N"
  shows "M \<in> multisets F \<and> N \<in> multisets F"
  using assms
  unfolding mulex_on_def
  by (induct) auto

lemma union_multisets_iff [iff]:
  "M + N \<in> multisets A \<longleftrightarrow> M \<in> multisets A \<and> N \<in> multisets A"
  by (auto dest: union_multisetsD)

lemma mulex_on_trans:
  "mulex_on P A L M \<Longrightarrow> mulex_on P A M N \<Longrightarrow> mulex_on P A L N"
  unfolding mulex_on_def by auto
  
lemma mulex_on_add_right [simp]:
  assumes "mulex_on P A M N" and "a \<in> A"
  shows "mulex_on P A M (N + {#a#})"
proof -
  from assms have "a \<in> A" and "N \<in> multisets A" by (auto dest: mulex_on_imp_multisets)
  then have "mulex_on P A N (N + {#a#})" by simp
  with `mulex_on P A M N` show ?thesis by (rule mulex_on_trans)
qed

lemma empty_mulex_on [simp]:
  assumes "M \<noteq> {#}" and "M \<in> multisets A"
  shows "mulex_on P A {#} M"
using assms
proof (induct M)
  case (add M a)
  show ?case
  proof (cases "M = {#}")
    assume "M = {#}"
    with add show ?thesis by (auto simp: mulex_on_def)
  next
    assume "M \<noteq> {#}"
    with add show ?thesis by (auto intro: mulex_on_trans)
  qed
qed simp

lemma mulex_on_self_add_right [simp]:
  assumes "M \<in> multisets A" and "K \<in> multisets A" and "K \<noteq> {#}"
  shows "mulex_on P A M (M + K)"
  using assms
proof (induct K)
  case empty
  then show ?case by (cases "K = {#}") auto
next
  case (add M a)
  show ?case
  proof (cases "M = {#}")
    assume "M = {#}" with add show ?thesis by auto
  next
    assume "M \<noteq> {#}" with add show ?thesis
      by (auto dest: mulex_on_add_right simp add: ac_simps)
  qed
qed

lemma mult1_singleton [iff]:
  "({#x#}, {#y#}) \<in> mult1 R \<longleftrightarrow> (x, y) \<in> R"
proof
  assume "(x, y) \<in> R"
  then have "{#y#} = {#} + {#y#}"
    and "{#x#} = {#} + {#x#}"
    and "\<forall>b. b \<in># {#x#} \<longrightarrow> (b, y) \<in> R" by auto
  then show "({#x#}, {#y#}) \<in> mult1 R" unfolding mult1_def by blast
next
  assume "({#x#}, {#y#}) \<in> mult1 R"
  then obtain M0 K a
    where "{#y#} = M0 + {#a#}"
    and "{#x#} = M0 + K"
    and "\<forall>b. b \<in># K \<longrightarrow> (b, a) \<in> R"
    unfolding mult1_def by blast
  then show "(x, y) \<in> R" by (auto simp: single_is_union)
qed

lemma mulex1_singleton [iff]:
  "mulex1 P {#x#} {#y#} \<longleftrightarrow> P x y"
  using mult1_singleton [of x y "{(x, y). P x y}"] by (simp add: mulex1_def)

lemma singleton_mulex_onI:
  "P x y \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> mulex_on P A {#x#} {#y#}"
  by (auto simp: mulex_on_def)

lemma reflclp_mulex_on_add_right [simp]:
  assumes "(mulex_on P A)\<^sup>=\<^sup>= M N" and "M \<in> multisets A" and "a \<in> A"
  shows "mulex_on P A M (N + {#a#})"
  using assms by (cases "M = N") simp_all

lemma reflclp_mulex_on_add_right' [simp]:
  assumes "(mulex_on P A)\<^sup>=\<^sup>= M N" and "M \<in> multisets A" and "a \<in> A"
  shows "mulex_on P A M ({#a#} + N)"
  using reflclp_mulex_on_add_right [OF assms] by (simp add: ac_simps)

lemma mulex_on_union_right [simp]:
  assumes "mulex_on P F A B" and "K \<in> multisets F"
  shows "mulex_on P F A (K + B)"
using assms
proof (induct K)
  case (add K a)
  then have "a \<in> F" and "mulex_on P F A (B + K)" by (auto simp: multisets_def ac_simps)
  then have "mulex_on P F A ((B + K) + {#a#})" by simp
  then show ?case by (simp add: ac_simps)
qed simp

lemma mulex_on_union_right' [simp]:
  assumes "mulex_on P F A B" and "K \<in> multisets F"
  shows "mulex_on P F A (B + K)"
  using mulex_on_union_right [OF assms] by (simp add: ac_simps)

text {*Adapted from @{thm all_accessible} in @{theory Multiset}.*}
lemma accessible_on_mulex1_multisets:
  assumes wf: "wfp_on P A"
  shows "\<forall>M\<in>multisets A. accessible_on (mulex1 P) (multisets A) M"
proof
  let ?P = "mulex1 P"
  let ?A = "multisets A"
  let ?acc = "accessible_on ?P ?A"
  {
    fix M M0 a
    assume M0: "?acc M0"
      and "a \<in> A"
      and "M0 \<in> ?A"
      and wf_hyp: "\<And>b. \<lbrakk>b \<in> A; P b a\<rbrakk> \<Longrightarrow> (\<forall>M. ?acc (M) \<longrightarrow> ?acc (M + {#b#}))"
      and acc_hyp: "\<forall>M. M \<in> ?A \<and> ?P M M0 \<longrightarrow> ?acc (M + {#a#})"
    then have "M0 + {#a#} \<in> ?A" by (auto simp: multisets_def)
    then have "?acc (M0 + {#a#})"
    proof (rule accessible_onI [of "M0 + {#a#}"])
      fix N
      assume "N \<in> ?A"
        and "?P N (M0 + {#a#})"
      then have "((\<exists>M. M \<in> ?A \<and> ?P M M0 \<and> N = M + {#a#}) \<or>
          (\<exists>K. (\<forall>b. b \<in># K \<longrightarrow> P b a) \<and> N = M0 + K))"
        using mulex1_add [of P N M0 a] by (auto simp: multisets_def)
      then show "?acc (N)"
      proof (elim exE disjE conjE)
        fix M assume "M \<in> ?A" and "?P M M0" and N: "N = M + {#a#}"
        from acc_hyp have "M \<in> ?A \<and> ?P M M0 \<longrightarrow> ?acc (M + {#a#})" ..
        with `M \<in> ?A` and `?P M M0` have "?acc (M + {#a#})" by blast
        then show "?acc (N)" by (simp only: N)
      next
        fix K
        assume N: "N = M0 + K"
        assume "\<forall>b. b \<in># K \<longrightarrow> P b a"
        moreover from N and `N \<in> ?A` have "K \<in> ?A" by (auto simp: multisets_def)
        ultimately have "?acc (M0 + K)"
        proof (induct K)
          case empty
          from M0 show "?acc (M0 + {#})" by simp
        next
          case (add K x)
          from add.prems have "x \<in> A" and "P x a" by (auto simp: multisets_def)
          with wf_hyp have "\<forall>M. ?acc M \<longrightarrow> ?acc (M + {#x#})" by blast
          moreover from add have "?acc (M0 + K)" by (auto simp: multisets_def)
          ultimately have "?acc ((M0 + K) + {#x#})" by auto
          then show "?acc (M0 + (K + {#x#}))" by (simp only: add_assoc)
        qed
        then show "?acc N" by (simp only: N)
      qed
    qed
  } note tedious_reasoning = this

  fix M
  assume "M \<in> ?A"
  then show "?acc M"
  proof (induct M)
    show "?acc {#}"
    proof (rule accessible_onI)
      show "{#} \<in> ?A" by (auto simp: multisets_def)
    next
      fix b assume "?P b {#}" then show "?acc b" by simp
    qed
  next
    case (add M a)
    then have "?acc M" by (auto simp: multisets_def)
    from add have "a \<in> A" by (auto simp: multisets_def)
    with wf have "\<forall>M. ?acc M \<longrightarrow> ?acc (M + {#a#})"
    proof (induct)
      case (less a)
      then have r: "\<And>b. \<lbrakk>b \<in> A; P b a\<rbrakk> \<Longrightarrow> (\<forall>M. ?acc M \<longrightarrow> ?acc (M + {#b#}))" by auto
      show "\<forall>M. ?acc M \<longrightarrow> ?acc (M + {#a#})"
      proof (intro allI impI)
        fix M'
        assume "?acc M'"
        moreover then have "M' \<in> ?A" by (blast dest: accessible_on_imp_mem)
        ultimately show "?acc (M' + {#a#})"
          by (induct) (rule tedious_reasoning [OF _ `a \<in> A` _ r], auto)
      qed
    qed
    with `?acc (M)` show "?acc (M + {#a#})" by blast
  qed
qed

lemmas wfp_on_mulex1_multisets =
  accessible_on_mulex1_multisets [THEN accessible_on_imp_wfp_on]

lemmas irreflp_on_mulex1 =
  wfp_on_mulex1_multisets [THEN wfp_on_imp_irreflp_on]

lemma wfp_on_mulex_on_multisets:
  assumes "wfp_on P A"
  shows "wfp_on (mulex_on P A) (multisets A)"
  using wfp_on_mulex1_multisets [OF assms]
  unfolding mulex_on_def wfp_on_restrict_to_tranclp_wfp_on_conv .

lemmas irreflp_on_mulex_on =
  wfp_on_mulex_on_multisets [THEN wfp_on_imp_irreflp_on]

lemma mulex1_union:
  "mulex1 P M N \<Longrightarrow> mulex1 P (K + M) (K + N)"
  unfolding mulex1_def by (auto simp: mult1_union)

lemma mulex_on_union:
  assumes "mulex_on P A M N" and "K \<in> multisets A"
  shows "mulex_on P A (K + M) (K + N)"
  using assms
  unfolding mulex_on_def
proof (induct)
  case (base N)
  then have "mulex1 P (K + M) (K + N)" by (blast dest: mulex1_union)
  moreover from base have "(K + M) \<in> multisets A"
    and "(K + N) \<in> multisets A" by (auto simp: multisets_def)
  ultimately have "restrict_to (mulex1 P) (multisets A) (K + M) (K + N)" by auto
  then show ?case by blast
next
  case (step L N)
  then have "mulex1 P (K + L) (K + N)" by (blast dest: mulex1_union)
  moreover from step have "(K + L) \<in> multisets A" and "(K + N) \<in> multisets A"
    by (auto simp: multisets_def)
  ultimately have "(restrict_to (mulex1 P) (multisets A))\<^sup>+\<^sup>+ (K + L) (K + N)" by auto
  moreover have "(restrict_to (mulex1 P) (multisets A))\<^sup>+\<^sup>+ (K + M) (K + L)" using step by blast
  ultimately show ?case by (metis transitive_closurep_trans'(1))
qed

lemma mulex_on_union':
  assumes "mulex_on P A M N" and "K \<in> multisets A"
  shows "mulex_on P A (M + K) (N + K)"
  using mulex_on_union [OF assms] by (simp add: ac_simps)

lemma union_mulex_on_mono:
  "mulex_on P F A C \<Longrightarrow> mulex_on P F B D \<Longrightarrow> mulex_on P F (A + B) (C + D)"
  by (metis mulex_on_imp_multisets mulex_on_trans mulex_on_union mulex_on_union')

lemma union_mulex_on_mono1:
  "A \<in> multisets F \<Longrightarrow> (mulex_on P F)\<^sup>=\<^sup>= A C \<Longrightarrow> mulex_on P F B D \<Longrightarrow>
    mulex_on P F (A + B) (C + D)"
  by (auto intro: union_mulex_on_mono mulex_on_union)

lemma union_mulex_on_mono2:
  "B \<in> multisets F \<Longrightarrow> mulex_on P F A C \<Longrightarrow> (mulex_on P F)\<^sup>=\<^sup>= B D \<Longrightarrow>
    mulex_on P F (A + B) (C + D)"
  by (auto intro: union_mulex_on_mono mulex_on_union')

lemma mult1_mono:
  assumes "\<And>x y. \<lbrakk>x \<in> A; y \<in> A; (x, y) \<in> R\<rbrakk> \<Longrightarrow> (x, y) \<in> S"
    and "M \<in> multisets A"
    and "N \<in> multisets A"
    and "(M, N) \<in> mult1 R"
  shows "(M, N) \<in> mult1 S"
  using assms 
  unfolding mult1_def multisets_def
  by (auto) (metis (full_types) mem_set_of_iff set_mp)

lemma mulex1_mono:
  assumes "\<And>x y. \<lbrakk>x \<in> A; y \<in> A; P x y\<rbrakk> \<Longrightarrow> Q x y"
    and "M \<in> multisets A"
    and "N \<in> multisets A"
    and "mulex1 P M N"
  shows "mulex1 Q M N"
  using mult1_mono [of A "{(x, y). P x y}" "{(x, y). Q x y}" M N]
    and assms unfolding mulex1_def by blast

lemma mulex_on_mono:
  assumes *: "\<And>x y. \<lbrakk>x \<in> A; y \<in> A; P x y\<rbrakk> \<Longrightarrow> Q x y"
    and "mulex_on P A M N"
  shows "mulex_on Q A M N"
proof -
  let ?rel = "\<lambda>P. (restrict_to (mulex1 P) (multisets A))"
  from `mulex_on P A M N` have "(?rel P)\<^sup>+\<^sup>+ M N" by (simp add: mulex_on_def)
  then have "(?rel Q)\<^sup>+\<^sup>+ M N"
  proof (induct rule: tranclp.induct)
    case (r_into_trancl M N)
    then have "M \<in> multisets A" and "N \<in> multisets A" by auto
    from mulex1_mono [OF * this] and r_into_trancl
      show ?case by auto
  next
    case (trancl_into_trancl L M N)
    then have "M \<in> multisets A" and "N \<in> multisets A" by auto
    from mulex1_mono [OF * this] and trancl_into_trancl
      have "?rel Q M N" by auto
    with `(?rel Q)\<^sup>+\<^sup>+ L M` show ?case by (rule tranclp.trancl_into_trancl)
  qed
  then show ?thesis by (simp add: mulex_on_def)
qed

lemma mult1_reflcl:
  assumes "(M, N) \<in> mult1 R"
  shows "(M, N) \<in> mult1 (R\<^sup>=)"
  using assms by (auto simp: mult1_def)

lemma mulex1_reflclp:
  assumes "mulex1 P M N"
  shows "mulex1 (P\<^sup>=\<^sup>=) M N"
  using mulex1_mono [of UNIV P "P\<^sup>=\<^sup>=" M N, OF _ _ _ assms]
  by (auto simp: multisets_def)

lemma mulex_on_reflclp:
  assumes "mulex_on P A M N"
  shows "mulex_on (P\<^sup>=\<^sup>=) A M N"
  using mulex_on_mono [OF _ assms, of "P\<^sup>=\<^sup>="] by auto

lemma surj_on_multisets_multiset_of:
  "\<forall>M\<in>multisets A. \<exists>xs\<in>lists A. M = multiset_of xs"
proof
  fix M
  assume "M \<in> multisets A"
  then show "\<exists>xs\<in>lists A. M = multiset_of xs"
  proof (induct M)
    case empty show ?case by simp
  next
    case (add M a)
    then obtain xs where "xs \<in> lists A" and "M = multiset_of xs" by auto
    then have "M + {#a#} = multiset_of (a # xs)" by simp
    moreover have "a # xs \<in> lists A" using `xs \<in> lists A` and add by auto
    ultimately show ?case by blast
  qed
qed

lemma image_multiset_of_lists [simp]:
  "multiset_of ` lists A = multisets A"
  using surj_on_multisets_multiset_of [of A]
  by auto (metis mem_Collect_eq multisets_def set_of_multiset_of subsetI)

end

