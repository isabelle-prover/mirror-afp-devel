section \<open>Examples\<close>

text \<open>In this file, we prove that the two examples from section IV satisfy resp. violate GNI,
using the proof outlines from appendix A.\<close>

theory Examples
  imports Logic
begin

definition GNI where
  "GNI l h S \<longleftrightarrow> (\<forall>\<phi>1 \<phi>2. \<phi>1 \<in> S \<and> \<phi>2 \<in> S
  \<longrightarrow> (\<exists>\<phi> \<in> S. snd \<phi> h = snd \<phi>1 h \<and> snd \<phi> l = snd \<phi>2 l))"

lemma GNI_I:
  assumes "\<And>\<phi>1 \<phi>2. \<phi>1 \<in> S \<and> \<phi>2 \<in> S
  \<Longrightarrow> (\<exists>\<phi> \<in> S. snd \<phi> h = snd \<phi>1 h \<and> snd \<phi> l = snd \<phi>2 l)"
  shows "GNI l h S"
  by (simp add: GNI_def assms)

lemma program_1_sat_gni:
  assumes "y \<noteq> l \<and> y \<noteq> h \<and> l \<noteq> h"
  shows "\<turnstile> { (\<lambda>S. True) } Seq (Havoc y) (Assign l (\<lambda>\<sigma>. (\<sigma> h :: int) + \<sigma> y)) { GNI l h }"
proof (rule RuleSeq)
  let ?R = "\<lambda>S. \<forall>\<phi>1 \<phi>2. \<phi>1 \<in> S \<and> \<phi>2 \<in> S
  \<longrightarrow> (\<exists>\<phi> \<in> S. (snd \<phi> h :: int) = snd \<phi>1 h \<and> snd \<phi> h + snd \<phi> y = snd \<phi>2 h + snd \<phi>2 y )"

  show "\<turnstile> {(\<lambda>S. True)} Havoc y {?R}"
  proof (rule RuleCons)
    show "\<turnstile> {(\<lambda>S. ?R {(l, \<sigma>(y := v)) |l \<sigma> v. (l, \<sigma>) \<in> S})} Havoc y {?R}"
      using RuleHavoc[of ?R] by blast
    show "entails (\<lambda>S. True) (\<lambda>S. ?R {(l, \<sigma>(y := v)) |l \<sigma> (v :: int). (l, \<sigma>) \<in> S})"
    proof (rule entailsI)
      fix S
      show "?R {(l, \<sigma>(y := v)) |l \<sigma> (v :: int). (l, \<sigma>) \<in> S}"
      proof (clarify)
        fix a b aa ba l la \<sigma> \<sigma>' v va
        assume asm0: "(l, \<sigma>) \<in> S" "(la, \<sigma>') \<in> S"
        let ?v = "(\<sigma>'(y := va)) h + (\<sigma>'(y := va)) y + - \<sigma> h"
        let ?\<phi> = "(l, \<sigma>(y := ?v))"
        have "snd ?\<phi> h = snd (l, \<sigma>(y := v)) h \<and> snd ?\<phi> h + snd ?\<phi> y = snd (la, \<sigma>'(y := va)) h + snd (la, \<sigma>'(y := va)) y"
          using assms by force
        then show "\<exists>\<phi>\<in>{(l, \<sigma>(y := v)) |l \<sigma> v. (l, \<sigma>) \<in> S}.
          snd \<phi> h = snd (l, \<sigma>(y := v)) h \<and> snd \<phi> h + snd \<phi> y = snd (la, \<sigma>'(y := va)) h + snd (la, \<sigma>'(y := va)) y"
          using asm0(1) by blast
      qed
    qed
    show "entails ?R ?R"
      by (meson entailsI)
  qed
  show "\<turnstile> {?R} (Assign l (\<lambda>\<sigma>. \<sigma> h + \<sigma> y)) {GNI l h}"
  proof (rule RuleCons)
    show "\<turnstile> {(\<lambda>S. GNI l h {(la, \<sigma>(l := \<sigma> h + \<sigma> y)) |la \<sigma>. (la, \<sigma>) \<in> S})} Assign l (\<lambda>\<sigma>. \<sigma> h + \<sigma> y) {GNI l h}"
      using RuleAssign[of "GNI l h" l "\<lambda>\<sigma>. \<sigma> h + \<sigma> y"] by blast
    show "entails (GNI l h) (GNI l h)"
      by (simp add: entails_def)


    show "entails ?R (\<lambda>S. GNI l h {(la, \<sigma>(l := \<sigma> h + \<sigma> y)) |la \<sigma>. (la, \<sigma>) \<in> S})"
    proof (rule entailsI)
      fix S
      assume asm0: "\<forall>\<phi>1 \<phi>2. \<phi>1 \<in> S \<and> \<phi>2 \<in> S \<longrightarrow> (\<exists>\<phi>\<in>S. snd \<phi> h = snd \<phi>1 h \<and> snd \<phi> h + snd \<phi> y = snd \<phi>2 h + snd \<phi>2 y)"
      show "GNI l h {(la, \<sigma>(l := \<sigma> h + \<sigma> y)) |la \<sigma>. (la, \<sigma>) \<in> S}"
      proof (rule GNI_I)
        fix \<phi>1 \<phi>2
        assume asm1: "\<phi>1 \<in> {(la, \<sigma>(l := \<sigma> h + \<sigma> y)) |la \<sigma>. (la, \<sigma>) \<in> S} \<and> \<phi>2 \<in> {(la, \<sigma>(l := \<sigma> h + \<sigma> y)) |la \<sigma>. (la, \<sigma>) \<in> S}"
        then obtain la \<sigma> la' \<sigma>' where "(la, \<sigma>) \<in> S" "(la', \<sigma>') \<in> S" "\<phi>1 = (la, \<sigma>(l := \<sigma> h + \<sigma> y))" "\<phi>2 = (la', \<sigma>'(l := \<sigma>' h + \<sigma>' y))" 
          by blast
        then obtain \<phi> where "\<phi>\<in>S" "snd \<phi> h = \<sigma> h" "snd \<phi> h + snd \<phi> y = \<sigma>' h + \<sigma>' y"
          using asm0 snd_conv by force
        let ?\<phi> = "(fst \<phi>, (snd \<phi>)(l := snd \<phi> h + snd \<phi> y))"
        have "snd ?\<phi> h = snd \<phi>1 h \<and> snd ?\<phi> l = snd \<phi>2 l"
          using \<open>\<phi>1 = (la, \<sigma>(l := \<sigma> h + \<sigma> y))\<close> \<open>\<phi>2 = (la', \<sigma>'(l := \<sigma>' h + \<sigma>' y))\<close>
            \<open>snd \<phi> h + snd \<phi> y = \<sigma>' h + \<sigma>' y\<close> \<open>snd \<phi> h = \<sigma> h\<close> assms by force
        then show "\<exists>\<phi>\<in>{(la, \<sigma>(l := \<sigma> h + \<sigma> y)) |la \<sigma>. (la, \<sigma>) \<in> S}. snd \<phi> h = snd \<phi>1 h \<and> snd \<phi> l = snd \<phi>2 l"
          using \<open>\<phi> \<in> S\<close> mem_Collect_eq[of ?\<phi>]
          by (metis (mono_tags, lifting) prod.collapse)
      qed
    qed
  qed
qed


lemma program_2_violates_gni:
  assumes "y \<noteq> l \<and> y \<noteq> h \<and> l \<noteq> h"
  shows "\<turnstile> { (\<lambda>S. \<exists>a \<in> S. \<exists>b \<in> S. (snd a h :: nat) \<noteq> snd b h) }
  Seq (Seq (Havoc y) (Assume (\<lambda>\<sigma>. \<sigma> y \<ge> (0 :: nat) \<and> \<sigma> y \<le> (100 :: nat)))) (Assign l (\<lambda>\<sigma>. \<sigma> h + \<sigma> y))
  {\<lambda>(S :: (('lvar \<Rightarrow> 'lval) \<times> ('a \<Rightarrow> nat)) set). \<not> GNI l h S}"
proof (rule RuleSeq)

  let ?R0 = "\<lambda>(S :: (('lvar \<Rightarrow> 'lval) \<times> ('a \<Rightarrow> nat)) set).
    (\<exists>a \<in> S. \<exists>b \<in> S. snd b h > snd a h \<and> snd a y \<ge> (0 :: nat) \<and> snd a y \<le> 100 \<and> snd b y = 100)"
  let ?R1 = "\<lambda>(S :: (('lvar \<Rightarrow> 'lval) \<times> ('a \<Rightarrow> nat)) set).
    (\<exists>a \<in> S. \<exists>b \<in> S. snd b h > snd a h \<and> snd b y = 100) \<and> (\<forall>c \<in> S. snd c y \<le> 100)"
  let ?R2 = "\<lambda>(S :: (('lvar \<Rightarrow> 'lval) \<times> ('a \<Rightarrow> nat)) set).
    \<exists>a \<in> S. \<exists>b \<in> S. \<forall>c \<in> S. snd c h = snd a h \<longrightarrow> snd c h + snd c y = snd b h + snd b y"

  show "\<turnstile> {(\<lambda>S. \<exists>a\<in>S. \<exists>b\<in>S. snd a h \<noteq> snd b h)} Seq (Havoc y) (Assume (\<lambda>\<sigma>. 0 \<le> \<sigma> y \<and> \<sigma> y \<le> (100 :: nat))) {?R1}"
  proof (rule RuleSeq)
    show "\<turnstile> {(\<lambda>S. \<exists>a\<in>S. \<exists>b\<in>S. snd a h \<noteq> snd b h)} Havoc y { ?R0 }"
    proof (rule RuleCons)
      show "\<turnstile> {(\<lambda>S. ?R0 {(l, \<sigma>(y := v)) |l \<sigma> v. (l, \<sigma>) \<in> S})} Havoc y {?R0}"
        using RuleHavoc[of _ y] by fast
      show "entails ?R0 ?R0"
        by (simp add: entailsI)
      show "entails (\<lambda>S. \<exists>a\<in>S. \<exists>b\<in>S. snd a h \<noteq> snd b h) (\<lambda>S. ?R0 {(l, \<sigma>(y := v)) |l \<sigma> v. (l, \<sigma>) \<in> S})"
      proof (rule entailsI)
        fix S :: "(('lvar \<Rightarrow> 'lval) \<times> ('a \<Rightarrow> nat)) set"
        assume "\<exists>a\<in>S. \<exists>b\<in>S. snd a h \<noteq> snd b h"
        then obtain a b where "a \<in> S" "b \<in> S" "snd b h > snd a h"
          by (meson linorder_neq_iff)
        let ?a = "(fst a, (snd a)(y := 100))"
        let ?b = "(fst b, (snd b)(y := 100))"
        have "?a \<in> {(l, \<sigma>(y := v)) |l \<sigma> v. (l, \<sigma>) \<in> S} \<and> ?b \<in> {(l, \<sigma>(y := v)) |l \<sigma> v. (l, \<sigma>) \<in> S}"
          using \<open>a \<in> S\<close> \<open>b \<in> S\<close> by fastforce
        moreover have "snd ?b h > snd ?a h \<and> snd ?a y \<ge> (0 :: nat) \<and> snd ?a y \<le> 100 \<and> snd ?b y = 100"
          using \<open>snd a h < snd b h\<close> assms by force
        ultimately show "?R0 {(l, \<sigma>(y := v)) |l \<sigma> v. (l, \<sigma>) \<in> S}" by blast
      qed
    qed
    show "\<turnstile> {?R0} Assume (\<lambda>\<sigma>. 0 \<le> \<sigma> y \<and> \<sigma> y \<le> 100) {?R1}"
    proof (rule RuleCons)
      show "\<turnstile> {(\<lambda>S. ?R1 (Set.filter ((\<lambda>\<sigma>. 0 \<le> \<sigma> y \<and> \<sigma> y \<le> 100) \<circ> snd)
              S))} Assume (\<lambda>\<sigma>. 0 \<le> \<sigma> y \<and> \<sigma> y \<le> 100) {?R1}"
        using RuleAssume[of _ "\<lambda>\<sigma>. 0 \<le> \<sigma> y \<and> \<sigma> y \<le> 100"]
        by fast
      show "entails ?R1 ?R1"
        by (simp add: entailsI)
      show "entails ?R0 (\<lambda>S. ?R1 (Set.filter ((\<lambda>\<sigma>. 0 \<le> \<sigma> y \<and> \<sigma> y \<le> 100) \<circ> snd) S))"
      proof (rule entailsI)
        fix S :: "(('lvar \<Rightarrow> 'lval) \<times> ('a \<Rightarrow> nat)) set"
        assume asm0: "?R0 S"
        then obtain a b where "a\<in>S" "b\<in>S" "snd a h < snd b h \<and> 0 \<le> snd a y \<and> snd a y \<le> (100 :: nat) \<and> snd b y = 100 "
          by blast
        then have "a \<in> Set.filter ((\<lambda>\<sigma>. 0 \<le> \<sigma> y \<and> \<sigma> y \<le> 100) \<circ> snd) S \<and> b \<in> Set.filter ((\<lambda>\<sigma>. 0 \<le> \<sigma> y \<and> \<sigma> y \<le> 100) \<circ> snd) S"
          by (simp add: \<open>a \<in> S\<close> \<open>b \<in> S\<close>)
        then show "?R1 (Set.filter ((\<lambda>\<sigma>. 0 \<le> \<sigma> y \<and> \<sigma> y \<le> 100) \<circ> snd) S)"
          using \<open>snd a h < snd b h \<and> 0 \<le> snd a y \<and> snd a y \<le> 100 \<and> snd b y = 100\<close> by force
      qed
    qed
  qed
  show "\<turnstile> { ?R1 } Assign l (\<lambda>\<sigma>. \<sigma> h + \<sigma> y) {\<lambda>S. \<not> GNI l h S}"
  proof (rule RuleCons)
    show "\<turnstile> {(\<lambda>S. \<not> GNI l h {(la, \<sigma>(l := \<sigma> h + \<sigma> y)) |la \<sigma>. (la, \<sigma>) \<in> S})} Assign l (\<lambda>\<sigma>. \<sigma> h + \<sigma> y) {\<lambda>S. \<not> GNI l h S}"
      using RuleAssign[of "\<lambda>S. \<not> GNI l h S" l "\<lambda>\<sigma>. \<sigma> h + \<sigma> y"]
      by blast
    show "entails (\<lambda>S. \<not> GNI l h S) (\<lambda>S. \<not> GNI l h S)"
      by (simp add: entails_def)
    show "entails (\<lambda>S. (\<exists>a\<in>S. \<exists>b\<in>S. snd a h < snd b h \<and> snd b y = 100) \<and> (\<forall>c\<in>S. snd c y \<le> 100))
        (\<lambda>(S :: (('lvar \<Rightarrow> 'lval) \<times> ('a \<Rightarrow> nat)) set). \<not> GNI l h {(la, \<sigma>(l := \<sigma> h + \<sigma> y)) |la \<sigma>. (la, \<sigma>) \<in> S})"
    proof (rule entailsI)
      fix S :: "(('lvar \<Rightarrow> 'lval) \<times> ('a \<Rightarrow> nat)) set"
      assume asm0: "(\<exists>a\<in>S. \<exists>b\<in>S. snd a h < snd b h \<and> snd b y = 100) \<and> (\<forall>c\<in>S. snd c y \<le> 100)"
      then obtain a b where asm1: "a\<in>S" "b\<in>S" "snd a h < snd b h \<and> snd b y = 100" by blast
      let ?a = "(fst a, (snd a)(l := snd a h + snd a y))"
      let ?b = "(fst b, (snd b)(l := snd b h + snd b y))"
      have "\<And>la \<sigma>. (la, \<sigma>) \<in> S \<Longrightarrow> (\<sigma>(l := \<sigma> h + \<sigma> y)) h = snd ?a h \<Longrightarrow> (\<sigma>(l := \<sigma> h + \<sigma> y)) l \<noteq> snd ?b l"
        using asm0 asm1(3) assms by fastforce
      moreover have r: "?a \<in> {(la, \<sigma>(l := \<sigma> h + \<sigma> y)) |la \<sigma>. (la, \<sigma>) \<in> S} \<and> ?b \<in> {(la, \<sigma>(l := \<sigma> h + \<sigma> y)) |la \<sigma>. (la, \<sigma>) \<in> S}"
        using asm1(1) asm1(2) by fastforce
      show "\<not> GNI l h {(la, \<sigma>(l := \<sigma> h + \<sigma> y)) |la \<sigma>. (la, \<sigma>) \<in> S}"
      proof (rule ccontr)
        assume "\<not> \<not> GNI l h {(la, \<sigma>(l := \<sigma> h + \<sigma> y)) |la \<sigma>. (la, \<sigma>) \<in> S}"
        then have "GNI l h {(la, \<sigma>(l := \<sigma> h + \<sigma> y)) |la \<sigma>. (la, \<sigma>) \<in> S}"
          by blast
        then obtain \<phi> where "\<phi> \<in> {(la, \<sigma>(l := \<sigma> h + \<sigma> y)) |la \<sigma>. (la, \<sigma>) \<in> S}" "snd \<phi> h = snd ?a h" "snd \<phi> l = snd ?b l"
          using GNI_def[of l h "{(la, \<sigma>(l := \<sigma> h + \<sigma> y)) |la \<sigma>. (la, \<sigma>) \<in> S}"] r
          by meson
        then show False
          using calculation by auto
      qed
    qed
  qed
qed

end