section \<open>Examples\<close>

text \<open>In this file, we prove the correctness of the two compositionality
proofs presented in Appendix D.2.\<close>

theory ExamplesCompositionality
  imports Logic Compositionality
begin

definition low where
  "low l S \<longleftrightarrow> (\<forall>\<phi>1 \<phi>2. \<phi>1 \<in> S \<and> \<phi>2 \<in> S \<longrightarrow> snd \<phi>1 l = snd \<phi>2 l)"

subsection \<open>Examples using the core rules.\<close>

definition GNI where
  "GNI l h S \<longleftrightarrow> (\<forall>\<phi>1 \<phi>2. \<phi>1 \<in> S \<and> \<phi>2 \<in> S
  \<longrightarrow> (\<exists>\<phi> \<in> S. snd \<phi> h = snd \<phi>1 h \<and> snd \<phi> l = snd \<phi>2 l))"

lemma GNI_I:
  assumes "\<And>\<phi>1 \<phi>2. \<phi>1 \<in> S \<and> \<phi>2 \<in> S
  \<Longrightarrow> (\<exists>\<phi> \<in> S. snd \<phi> h = snd \<phi>1 h \<and> snd \<phi> l = snd \<phi>2 l)"
  shows "GNI l h S"
  by (simp add: GNI_def assms)

subsection \<open>Examples using the compositionality rules\<close>



definition has_minimum :: "'c \<Rightarrow> ('d \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a, 'b, 'c, 'd) chyperassertion" where
  "has_minimum x leq S \<longleftrightarrow> (\<exists>\<omega>\<in>S. \<forall>\<omega>'\<in>S. leq (snd \<omega> x) (snd \<omega>' x))"

lemma has_minimumI:
  assumes "\<omega> \<in> S"
      and "\<And>\<omega>'. \<omega>' \<in> S \<Longrightarrow> leq (snd \<omega> x) (snd \<omega>' x)"
    shows "has_minimum x leq S"
  by (metis assms(1) assms(2) has_minimum_def)

definition is_monotonic where
  "is_monotonic i x one two leq S \<longleftrightarrow> (\<forall>\<omega>\<in>S. \<forall>\<omega>'\<in>S. fst \<omega> i = one \<and> fst \<omega>' i = two \<longrightarrow> leq (snd \<omega> x) (snd \<omega>' x))"

lemma is_monotonicI:
  assumes "\<And>\<omega> \<omega>'. \<omega> \<in> S \<Longrightarrow> \<omega>' \<in> S \<Longrightarrow> fst \<omega> i = one \<and> fst \<omega>' i = two \<Longrightarrow> leq (snd \<omega> x) (snd \<omega>' x)"
  shows "is_monotonic i x one two leq S"
  by (simp add: assms is_monotonic_def)



lemma update_logical_equal_outside:
  "equal_outside_set {i} (snd \<omega>) (snd (update_logical \<omega> i v))"
  by (simp add: equal_outside_set_def update_logical_def)

lemma update_logical_read:
  "fst (update_logical \<omega> i v) i = v"
  by (simp add: update_logical_def)

lemma snd_update_logical_same:
  "snd (update_logical \<omega> i v) = snd \<omega>"
  by (simp add: update_logical_def)

text \<open>Figure 12\<close>
proposition composing_monotonicity_and_minimum:
  fixes P :: "((('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set \<Rightarrow> bool)"
  fixes i :: 'a
  fixes x :: 'c
  fixes y :: 'c
  fixes leq :: "'d \<Rightarrow> 'd \<Rightarrow> bool"
  fixes one :: 'b
  fixes two :: 'b

  assumes "\<Turnstile> { P } C1 { has_minimum x leq }"
      and "\<Turnstile> { is_monotonic i x one two leq } C2 { is_monotonic i y one two leq }"
      and "\<Turnstile> { (is_singleton :: ((('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set \<Rightarrow> bool)) } C2 { is_singleton }"
      and "one \<noteq> two"

      and "\<And>x. leq x x" \<comment>\<open>reflexivity\<close>

    shows "\<Turnstile> { P } C1 ;; C2 { has_minimum y leq }"
  using assms(1)
proof (rule seq_rule)

  let ?P1 = "is_singleton \<circ> (Set.filter (\<lambda>\<omega>. fst \<omega> i = one))"
  let ?P2 = "is_monotonic i x one two leq"
  let ?P3 = "\<lambda>S. \<forall>\<omega>\<in>S. fst \<omega> i = one \<or> fst \<omega> i = two"

  let ?P = "conj ?P1 (conj ?P2 ?P3)"

  let ?Q1 = "is_singleton \<circ> (Set.filter (\<lambda>\<omega>. fst \<omega> i = one))"
  let ?Q2 = "is_monotonic i y one two leq"
  let ?Q3 = "\<lambda>S. \<forall>\<omega>\<in>S. fst \<omega> i = one \<or> fst \<omega> i = two"

  let ?Q = "conj ?Q1 (conj ?Q2 ?Q3)"


  show "\<Turnstile> { (has_minimum x leq :: ((('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set \<Rightarrow> bool)) } C2 { has_minimum y leq }"
  proof (rule rule_LUpdate)

    show "entails_with_updates {i} (has_minimum x leq) ?P"
    proof (rule entails_with_updatesI)
      fix S :: "(('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set"
      assume asm0: "has_minimum x leq S"
      then obtain \<omega> where minimum: "\<omega> \<in> S" "\<And>\<omega>'. \<omega>' \<in> S \<Longrightarrow> leq (snd \<omega> x) (snd \<omega>' x)"
        by (metis has_minimum_def)
      let ?\<omega> = "update_logical \<omega> i one"
      let ?S = "{ update_logical \<omega>' i two |\<omega>'. \<omega>' \<in> S } \<union> {?\<omega>}"
      have "same_mod_updates {i} S ?S"
      proof (rule same_mod_updatesI)
        fix \<omega>' assume asm1: "\<omega>' \<in> S"
        then have "update_logical \<omega>' i two \<in> ?S"
          by blast
        moreover have "snd \<omega>' = snd (update_logical \<omega>' i two) \<and> equal_outside_set {i} (fst \<omega>') (fst (update_logical \<omega>' i two))"
          by (metis equal_outside_setI fst_eqD fun_upd_other singletonI snd_update_logical_same update_logical_def)
        ultimately show "\<exists>\<omega>''\<in>?S. snd \<omega>' = snd \<omega>'' \<and> equal_outside_set {i} (fst \<omega>') (fst \<omega>'')"
          by blast
      next
        fix \<omega>'
        assume asm1: "\<omega>' \<in> {update_logical \<omega>' i two |\<omega>'. \<omega>' \<in> S} \<union> {update_logical \<omega> i one}"
        show "\<exists>\<omega>\<in>S. snd \<omega> = snd \<omega>' \<and> equal_outside_set {i} (fst \<omega>') (fst \<omega>)"
        proof (cases "\<omega>' \<in> {update_logical \<omega>' i two |\<omega>'. \<omega>' \<in> S}")
          case True
          then obtain \<omega>'' where "\<omega>' = update_logical \<omega>'' i two" "\<omega>'' \<in> S"
            by blast
          then show ?thesis
            by (metis (mono_tags, lifting) equal_outside_set_def fst_conv fun_upd_other insertCI snd_update_logical_same update_logical_def)
        next
          case False
          then show ?thesis
            by (metis (mono_tags, lifting) UnE asm1 equal_outside_setI fst_eqD fun_upd_other minimum(1) singletonD singletonI snd_update_logical_same update_logical_def)
        qed
      qed
      moreover have "is_singleton (Set.filter (\<lambda>\<omega>. fst \<omega> i = one) ?S)"
      proof -
        have "Set.filter (\<lambda>\<omega>. fst \<omega> i = one) ?S \<subseteq> {?\<omega>}"
        proof
          fix \<omega> assume "\<omega> \<in> Set.filter (\<lambda>\<omega>. fst \<omega> i = one) ?S"
          then have "\<omega> \<in> ?S \<and> fst \<omega> i = one"
            by simp
          then show "\<omega> \<in> {?\<omega>}"
            using assms(4) update_logical_read by force
        qed
        moreover have "{?\<omega>} \<subseteq> Set.filter (\<lambda>\<omega>. fst \<omega> i = one) ?S"
          by (simp add: update_logical_read)
        ultimately show ?thesis
          by (simp add: is_singleton_def order_antisym_conv)
      qed
      moreover have "is_monotonic i x one two leq ?S"
      proof (rule is_monotonicI)
        fix \<omega>' \<omega>'' assume asm1: "\<omega>' \<in> ?S" "\<omega>'' \<in> ?S" "fst \<omega>' i = one \<and> fst \<omega>'' i = two"
        then have " \<omega>' \<in> {update_logical \<omega> i one} \<and> \<omega>'' \<in> {update_logical \<omega>' i two |\<omega>'. \<omega>' \<in> S}"
          using assms(4) update_logical_read by fastforce
        then show "leq (snd \<omega>' x) (snd \<omega>'' x)"
          by (metis (no_types, lifting) asm1(2) calculation(1) minimum(2) same_mod_updates_def singletonD snd_update_logical_same subset_mod_updatesE)
      qed
      moreover have "\<And>\<omega>'. \<omega>' \<in> ?S \<Longrightarrow> fst \<omega>' i = one \<or> fst \<omega>' i = two"
        using update_logical_read by fastforce
      ultimately have "same_mod_updates {i} S ?S \<and> ?P ?S"
        using comp_eq_dest_lhs[of is_singleton "Set.filter (\<lambda>\<omega>. fst \<omega> i = one)"] conj_def[of ?P1 "conj ?P2 ?P3"] conj_def[of ?P2 ?P3]
        by simp
      then show "\<exists>S'. same_mod_updates {i} S S' \<and> ?P S'"
        by blast
    qed

    show "invariant_on_updates {i} (has_minimum y leq :: ((('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set \<Rightarrow> bool))"
    proof (rule invariant_on_updatesI)
      fix S :: "(('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set"
      fix S'
      assume asm0: "same_mod_updates {i} S S'" "has_minimum y leq S"
      then show "has_minimum y leq S'"
        using has_minimum_def[of y leq S'] has_minimum_def[of y leq S] same_mod_updates_def[of "{i}" S S'] subset_mod_updatesE[of "{i}"]
          by metis
    qed

    show "\<Turnstile> { ?P } C2 { has_minimum y leq }"
    proof (rule consequence_rule)
      show "entails ?Q (has_minimum y leq)"
      proof (rule entailsI)
        fix S :: "(('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set"
        assume "?Q S"
        then obtain asm0: "is_singleton (Set.filter (\<lambda>\<omega>. fst \<omega> i = one) S)" "is_monotonic i y one two leq S"
          "\<And>\<omega>'. \<omega>' \<in> S \<Longrightarrow> fst \<omega>' i = one \<or> fst \<omega>' i = two"
          by (simp add: conj_def)
        then obtain \<omega> where "Set.filter (\<lambda>\<omega>. fst \<omega> i = one) S = {\<omega>}"
          by (metis is_singleton_def)
        then have "\<omega> \<in> S" by auto
        then show "has_minimum y leq S"
        proof (rule has_minimumI)
          fix \<omega>'
          assume asm1: "\<omega>' \<in> S"
          show "leq (snd \<omega> y) (snd \<omega>' y)"
          proof (cases "fst \<omega>' i = one")
            case True
            then show ?thesis
              using \<open>Set.filter (\<lambda>\<omega>. fst \<omega> i = one) S = {\<omega>}\<close> asm1 assms(5) by fastforce
          next
            case False
            then have "fst \<omega>' i = two"
              using asm0(3) asm1 by blast
            then show ?thesis
              using \<open>Set.filter (\<lambda>\<omega>. fst \<omega> i = one) S = {\<omega>}\<close> asm0(2) asm1 is_monotonic_def[of i y one two leq S] member_filter singleton_iff
              by force
          qed
        qed
      qed
      show "\<Turnstile> { ?P } C2 { ?Q }"
      proof (rule rule_and3)
        show " \<Turnstile> {is_singleton \<circ> Set.filter (\<lambda>\<omega>. fst \<omega> i = one)} C2 {is_singleton \<circ> Set.filter (\<lambda>\<omega>. fst \<omega> i = one)}"
        proof (rule rule_apply)
          show "\<Turnstile> { (is_singleton :: ((('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set \<Rightarrow> bool)) } C2 {is_singleton}"
            using assms(3) by blast
          show "commute_with_sem (Set.filter (\<lambda>\<omega>. fst \<omega> i = one))"
            by (simp add: filter_prop_commute)
        qed
        show "\<Turnstile> {is_monotonic i x one two leq} C2 {is_monotonic i y one two leq}"
          by (simp add: assms(2))
  
        show "\<Turnstile> {(\<lambda>S. \<forall>\<omega>\<in>S. fst \<omega> i = one \<or> fst \<omega> i = two)} C2 {\<lambda>S. \<forall>\<omega>\<in>S. fst \<omega> i = one \<or> fst \<omega> i = two}"
          using rule_lframe_single by fast
      qed
    qed (auto simp add: entails_refl)
  qed
qed

text \<open>In this definition, we use a logical variable for h, which records the initial value of the program variable h\<close>

definition lGNI :: "'pvar \<Rightarrow> 'lvar \<Rightarrow> (('lvar, 'lval, 'pvar, 'pval) state) set \<Rightarrow> bool" where
  "lGNI l h S \<longleftrightarrow> (\<forall>\<phi>1 \<in> S. (\<forall>\<phi>2 \<in> S. \<exists>\<phi> \<in> S. fst \<phi> h = fst \<phi>1 h \<and> snd \<phi> l = snd \<phi>2 l))"

text \<open>Figure 13\<close>
proposition composing_GNI_with_SNI:
  fixes h :: 'lvar
  fixes l :: 'pvar

  assumes "\<Turnstile> { (low l :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion) } C2 { low l }"
      and "\<Turnstile> { (not_empty :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion) } C2 { not_empty }"
      and "\<Turnstile> { (low l :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion) } C1 { lGNI l h }"
    shows "\<Turnstile> { (low l :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion) } C1;; C2 { lGNI l h }"
  using assms(3)
proof (rule seq_rule)
  show "\<Turnstile> { (lGNI l h :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion)} C2 {lGNI l h}"
    unfolding lGNI_def
  proof (rule rule_linking)
    fix \<phi>1 \<phi>1' :: "('lvar, 'lval, 'pvar, 'pval) state"
    assume asm0: "fst \<phi>1 = fst \<phi>1' \<and> \<Turnstile> { (in_set \<phi>1 :: ('lvar, 'lval, 'pvar, 'pval) state hyperassertion)} C2 {in_set \<phi>1'}"
    show "\<Turnstile> {(\<lambda>S. \<forall>\<phi>2\<in>S. \<exists>\<phi>\<in>S. fst \<phi> h = fst \<phi>1 h \<and> snd \<phi> l = snd \<phi>2 l)} C2 {\<lambda>S. \<forall>\<phi>2\<in>S. \<exists>\<phi>\<in>S. fst \<phi> h = fst \<phi>1' h \<and> snd \<phi> l = snd \<phi>2 l}"
    proof (rule consequence_rule)
      let ?ex = "\<lambda>S. \<exists>\<phi> \<in> S. fst \<phi> h = fst \<phi>1 h"
      let ?P = "general_union (conj (low l) ?ex)"
      show "\<Turnstile> { (?P :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion) } C2 {?P}"
      proof (rule rule_BigUnion; rule rule_And)
        show "\<Turnstile> {(low l :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion)} C2 {low l}"
          using assms(1) by blast
        show "\<Turnstile> { ?ex } C2 { ?ex }"
        proof (rule consequence_rule)
          let ?b = "\<lambda>\<phi>0. \<phi>0 h = fst \<phi>1 h"  
          show "\<Turnstile> {not_empty \<circ> Set.filter (?b \<circ> fst)} C2 { not_empty \<circ> Set.filter (?b \<circ> fst)}"
            using assms(2) rule_LFilter by auto
          show "entails (\<lambda>S. \<exists>\<phi>\<in>S. fst \<phi> h = fst \<phi>1 h) (not_empty \<circ> Set.filter ((\<lambda>\<phi>0. \<phi>0 h = fst \<phi>1 h) \<circ> fst))"
            using CollectI Set.filter_def comp_apply empty_iff not_empty_def
              entailsI[of "(\<lambda>S. \<exists>\<phi>\<in>S. fst \<phi> h = fst \<phi>1 h)" "(not_empty \<circ> Set.filter ((\<lambda>\<phi>0. \<phi>0 h = fst \<phi>1 h) \<circ> fst))"]
            by fastforce
          show "entails (not_empty \<circ> Set.filter ((\<lambda>\<phi>0. \<phi>0 h = fst \<phi>1 h) \<circ> fst)) (\<lambda>S. \<exists>\<phi>\<in>S. fst \<phi> h = fst \<phi>1 h)"
          proof (rule entailsI)
            fix S assume "(not_empty \<circ> Set.filter ((\<lambda>\<phi>0. \<phi>0 h = fst \<phi>1 h) \<circ> fst)) S"
            then obtain \<phi> where "\<phi> \<in> Set.filter ((\<lambda>\<phi>0. \<phi>0 h = fst \<phi>1 h) \<circ> fst) S"
              by (metis comp_apply equals0I not_empty_def)
            then show "\<exists>\<phi>\<in>S. fst \<phi> h = fst \<phi>1 h"
              by auto
          qed
        qed
      qed
      show "entails (\<lambda>S. \<forall>\<phi>2\<in>S. \<exists>\<phi>\<in>S. fst \<phi> h = fst \<phi>1 h \<and> snd \<phi> l = snd \<phi>2 l) ?P"
      proof (rule entailsI)
        fix S assume asm0: "\<forall>\<phi>2\<in>S. \<exists>\<phi>\<in>S. fst \<phi> h = fst \<phi>1 h \<and> snd \<phi> l = snd \<phi>2 l"
        thm general_unionI
        let ?F = "{ {\<phi>, \<phi>2} |\<phi> \<phi>2. \<phi> \<in> S \<and> \<phi>2 \<in> S \<and> snd \<phi> l = snd \<phi>2 l \<and> fst \<phi> h = fst \<phi>1 h }"
        show "general_union (Logic.conj (low l) (\<lambda>S. \<exists>\<phi>\<in>S. fst \<phi> h = fst \<phi>1 h)) S"
        proof (rule general_unionI)
          show "S = \<Union> ?F"
          proof
            show "S \<subseteq> \<Union> ?F"
            proof
              fix \<phi>2 assume "\<phi>2 \<in> S"
              then obtain \<phi> where "\<phi>\<in>S" "fst \<phi> h = fst \<phi>1 h \<and> snd \<phi> l = snd \<phi>2 l"
                using asm0 by blast
              then have "{\<phi>, \<phi>2} \<in> ?F"
                using \<open>\<phi>2 \<in> S\<close> by blast
              then show "\<phi>2 \<in> \<Union> ?F" by blast
            qed
            show "\<Union> ?F \<subseteq> S" by blast
          qed
          fix S' assume asm1: "S' \<in> {{\<phi>, \<phi>2} |\<phi> \<phi>2. \<phi> \<in> S \<and> \<phi>2 \<in> S \<and> snd \<phi> l = snd \<phi>2 l \<and> fst \<phi> h = fst \<phi>1 h}"
          then obtain \<phi> \<phi>2 where "S' = {\<phi>, \<phi>2}" "\<phi> \<in> S \<and> \<phi>2 \<in> S \<and> snd \<phi> l = snd \<phi>2 l \<and> fst \<phi> h = fst \<phi>1 h"
            by blast
          then show "Logic.conj (low l) (\<lambda>S. \<exists>\<phi>\<in>S. fst \<phi> h = fst \<phi>1 h) S'"
            using conj_def[of "low l" "\<lambda>S. \<exists>\<phi>\<in>S. fst \<phi> h = fst \<phi>1 h"] insert_iff low_def singletonD
            by fastforce
        qed
      qed
      show "entails ?P (\<lambda>S. \<forall>\<phi>2\<in>S. \<exists>\<phi>\<in>S. fst \<phi> h = fst \<phi>1' h \<and> snd \<phi> l = snd \<phi>2 l)"
      proof (rule entailsI)
        fix S assume "general_union (Logic.conj (low l) (\<lambda>S. \<exists>\<phi>\<in>S. fst \<phi> h = fst \<phi>1 h)) S"
        then obtain F where "S = \<Union> F" "\<And>S'. S' \<in> F \<Longrightarrow> low l S' \<and> (\<exists>\<phi>\<in>S'. fst \<phi> h = fst \<phi>1 h)"
          using conj_def[of "low l" "\<lambda>S. \<exists>\<phi>\<in>S. fst \<phi> h = fst \<phi>1 h"]
            general_unionE[of "Logic.conj (low l) (\<lambda>S. \<exists>\<phi>\<in>S. fst \<phi> h = fst \<phi>1 h)" S]
          by (metis (mono_tags, lifting))
        then show "\<forall>\<phi>2\<in>S. \<exists>\<phi>\<in>S. fst \<phi> h = fst \<phi>1' h \<and> snd \<phi> l = snd \<phi>2 l"
          by (metis (mono_tags, lifting) Union_iff asm0 low_def)
      qed
    qed
  qed
qed


subsection \<open>Other examples\<close>

lemma program_1_sat_gni:
  assumes "y \<noteq> l \<and> y \<noteq> h \<and> l \<noteq> h"
  shows "\<turnstile> { low l } Seq (Havoc y) (Assign l (\<lambda>\<sigma>. (\<sigma> h :: int) + \<sigma> y)) { GNI l h }"
proof (rule RuleSeq)
  let ?R = "\<lambda>S. \<forall>\<phi>1 \<phi>2. \<phi>1 \<in> S \<and> \<phi>2 \<in> S
  \<longrightarrow> (\<exists>\<phi> \<in> S. (snd \<phi> h :: int) = snd \<phi>1 h \<and> snd \<phi> h + snd \<phi> y = snd \<phi>2 h + snd \<phi>2 y )"

  show "\<turnstile> { low l } Havoc y {?R}"
  proof (rule RuleCons)
    show "\<turnstile> {(\<lambda>S. ?R {(l, \<sigma>(y := v)) |l \<sigma> v. (l, \<sigma>) \<in> S})} Havoc y {?R}"
      using RuleHavoc[of ?R] by blast
    show "entails (low l) (\<lambda>S. ?R {(l, \<sigma>(y := v)) |l \<sigma> (v :: int). (l, \<sigma>) \<in> S})"
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
  shows "\<turnstile> { conj (low l) (\<lambda>S. \<exists>a \<in> S. \<exists>b \<in> S. (snd a h :: nat) \<noteq> snd b h) }
  Seq (Seq (Havoc y) (Assume (\<lambda>\<sigma>. \<sigma> y \<ge> (0 :: nat) \<and> \<sigma> y \<le> (100 :: nat)))) (Assign l (\<lambda>\<sigma>. \<sigma> h + \<sigma> y))
  {\<lambda>(S :: (('lvar \<Rightarrow> 'lval) \<times> ('a \<Rightarrow> nat)) set). \<not> GNI l h S}"
proof (rule RuleSeq)

  let ?R0 = "\<lambda>(S :: (('lvar \<Rightarrow> 'lval) \<times> ('a \<Rightarrow> nat)) set).
    (\<exists>a \<in> S. \<exists>b \<in> S. snd b h > snd a h \<and> snd a y \<ge> (0 :: nat) \<and> snd a y \<le> 100 \<and> snd b y = 100)"
  let ?R1 = "\<lambda>(S :: (('lvar \<Rightarrow> 'lval) \<times> ('a \<Rightarrow> nat)) set).
    (\<exists>a \<in> S. \<exists>b \<in> S. snd b h > snd a h \<and> snd b y = 100) \<and> (\<forall>c \<in> S. snd c y \<le> 100)"
  let ?R2 = "\<lambda>(S :: (('lvar \<Rightarrow> 'lval) \<times> ('a \<Rightarrow> nat)) set).
    \<exists>a \<in> S. \<exists>b \<in> S. \<forall>c \<in> S. snd c h = snd a h \<longrightarrow> snd c h + snd c y = snd b h + snd b y"

  show "\<turnstile> { conj (low l) (\<lambda>S. \<exists>a\<in>S. \<exists>b\<in>S. snd a h \<noteq> snd b h)} Seq (Havoc y) (Assume (\<lambda>\<sigma>. 0 \<le> \<sigma> y \<and> \<sigma> y \<le> (100 :: nat))) {?R1}"
  proof (rule RuleSeq)
    show "\<turnstile> {conj (low l) (\<lambda>S. \<exists>a\<in>S. \<exists>b\<in>S. snd a h \<noteq> snd b h)} Havoc y { ?R0 }"
    proof (rule RuleCons)
      show "\<turnstile> {(\<lambda>S. ?R0 {(l, \<sigma>(y := v)) |l \<sigma> v. (l, \<sigma>) \<in> S})} Havoc y {?R0}"
        using RuleHavoc[of _ y] by fast
      show "entails ?R0 ?R0"
        by (simp add: entailsI)
      show "entails (conj (low l) (\<lambda>S. \<exists>a\<in>S. \<exists>b\<in>S. snd a h \<noteq> snd b h)) (\<lambda>S. ?R0 {(l, \<sigma>(y := v)) |l \<sigma> v. (l, \<sigma>) \<in> S})"
      proof (rule entailsI)
        fix S :: "(('lvar \<Rightarrow> 'lval) \<times> ('a \<Rightarrow> nat)) set"
        assume "conj (low l) (\<lambda>S. \<exists>a\<in>S. \<exists>b\<in>S. snd a h \<noteq> snd b h) S"
        then have "\<exists>a\<in>S. \<exists>b\<in>S. snd a h \<noteq> snd b h" using conj_def[of "low l" "\<lambda>S. \<exists>a\<in>S. \<exists>b\<in>S. snd a h \<noteq> snd b h"]
          by blast
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