(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Well-Quasi-Orders *}

theory Well_Quasi_Orders
imports
  Almost_Full_Relations
  "../Regular-Sets/Regexp_Method"
begin

subsection {* Basic Definitions *}

definition wqo_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "wqo_on P A \<longleftrightarrow> transp_on P A \<and> almost_full_on P A"

lemma wqo_onI [Pure.intro]:
  "\<lbrakk>transp_on P A; almost_full_on P A\<rbrakk> \<Longrightarrow> wqo_on P A"
  unfolding wqo_on_def almost_full_on_def by blast

lemma wqo_on_imp_reflp_on:
  "wqo_on P A \<Longrightarrow> reflp_on P A"
  using almost_full_on_imp_reflp_on by (auto simp: wqo_on_def)

lemma wqo_on_imp_transp_on:
  "wqo_on P A \<Longrightarrow> transp_on P A"
  by (auto simp: wqo_on_def)

lemma wqo_on_imp_almost_full_on:
  "wqo_on P A \<Longrightarrow> almost_full_on P A"
  by (auto simp: wqo_on_def)

lemma wqo_on_imp_good:
  "wqo_on P A \<Longrightarrow> \<forall>i. f i \<in> A \<Longrightarrow> good P f"
  by (auto simp: wqo_on_def almost_full_on_def)

lemma wqo_on_subset:
  "A \<subseteq> B \<Longrightarrow> wqo_on P B \<Longrightarrow> wqo_on P A"
  using almost_full_on_subset [of A B P]
    and transp_on_subset [of A B P]
  unfolding wqo_on_def by blast

subsection {* Equivalent Definitions *}

text {*The following statements are equivalent:
\begin{enumerate}
\item @{term P} is a well-quasi-order.
\item @{term P} does neither allow decreasing chains nor antichains.
\item Every quasi-order extending @{term P} is well-founded.
\end{enumerate}
*}

lemma wqo_not_decr_not_anti:
  assumes "wqo_on P A"
  shows wqo_on_imp_wfp_on: "wfp_on (strict P) A"
    and wqo_on_imp_no_antichain_on: "\<not> (\<exists>f. antichain_on P f A)"
proof -
  show "wfp_on (strict P) A"
  proof (unfold wfp_on_def, rule notI)
    assume "\<exists>f. \<forall>i. f i \<in> A \<and> strict P (f (Suc i)) (f i)"
    then obtain f where *: "chain_on ((strict P)\<inverse>\<inverse>) f A" by blast
    from chain_on_transp_on_less [OF this]
      and transp_on_strict [THEN transp_on_converse, OF assms [THEN wqo_on_imp_transp_on]]
      have "\<forall>i j. i < j \<longrightarrow> \<not> P (f i) (f j)" by blast
    with assms show False
      using * by (auto simp: wqo_on_def almost_full_on_def good_def) blast
  qed
next
  from almost_full_on_imp_no_antichain_on [of P A] and assms
    show "\<not> (\<exists>f. antichain_on P f A)"
    by (auto simp: wqo_on_def)
qed

lemma every_extension_wf_imp_wqo:
  assumes ext: "\<forall>Q. (\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> Q x y) \<and>
    reflp_on Q A \<and> transp_on Q A \<longrightarrow> wfp_on (strict Q) A"
    and "qo_on P A"
  shows "wqo_on P A"
proof
  from `qo_on P A`
    have refl: "reflp_on P A"
    and trans: "transp_on P A"
    by (auto intro: qo_on_imp_reflp_on qo_on_imp_transp_on)
  show "transp_on P A" by fact
  show "almost_full_on P A"
  proof
    fix f :: "nat \<Rightarrow> 'a"
    assume "\<forall>i. f i \<in> A"
    then have A: "\<And>i. f i \<in> A" ..
    show "good P f"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have bad: "\<forall>i j. i < j \<longrightarrow> \<not> P (f i) (f j)" by (auto simp: good_def)
      then have *: "\<And>i j. P (f i) (f j) \<Longrightarrow> i \<ge> j" by (metis not_leE)
  
      def [simp]: D \<equiv> "\<lambda>x y. \<exists>i. x = f (Suc i) \<and> y = f i"
      def P' \<equiv> "restrict_to P A"
      def [simp]: Q \<equiv> "(sup P' D)\<^sup>*\<^sup>*"

      have **: "\<And>i j. (D OO P'\<^sup>*\<^sup>*)\<^sup>+\<^sup>+ (f i) (f j) \<Longrightarrow> i > j"
      proof -
        fix i j
        assume "(D OO P'\<^sup>*\<^sup>*)\<^sup>+\<^sup>+ (f i) (f j)"
        then show "i > j"
          apply (induct "f i" "f j" arbitrary: j)
          apply (insert A, auto dest!: * simp: P'_def restrict_to_rtranclp [OF refl trans])
          apply (metis "*" dual_order.strict_trans1 less_Suc_eq_le refl reflp_on_def)
          by (metis le_imp_less_Suc less_trans)
      qed

      have "\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> Q x y" by (auto simp: P'_def)
      moreover have "reflp_on Q A" by (auto simp: reflp_on_def)
      moreover have "transp_on Q A" by (auto simp: transp_on_def)
      ultimately have "wfp_on (strict Q) A"
        using ext [THEN spec, of Q] by blast
      moreover have "\<forall>i. f i \<in> A \<and> strict Q (f (Suc i)) (f i)"
      proof
        fix i
        have "\<not> Q (f i) (f (Suc i))"
        proof
          assume "Q (f i) (f (Suc i))"
          then have "(sup P' D)\<^sup>*\<^sup>* (f i) (f (Suc i))" by auto
          moreover have "(sup P' D)\<^sup>*\<^sup>* = sup (P'\<^sup>*\<^sup>*) (P'\<^sup>*\<^sup>* OO (D OO P'\<^sup>*\<^sup>*)\<^sup>+\<^sup>+)"
          proof -
            have "\<And>A B. (A \<union> B)\<^sup>* = A\<^sup>* \<union> A\<^sup>* O (B O A\<^sup>*)\<^sup>+" by regexp
            from this [to_pred] show ?thesis by blast
          qed
          ultimately have "sup (P'\<^sup>*\<^sup>*) (P'\<^sup>*\<^sup>* OO (D OO P'\<^sup>*\<^sup>*)\<^sup>+\<^sup>+) (f i) (f (Suc i))" by simp
          then have "(P'\<^sup>*\<^sup>* OO (D OO P'\<^sup>*\<^sup>*)\<^sup>+\<^sup>+) (f i) (f (Suc i))" by auto
          then have "Suc i < i"
            using ** apply auto
            by (metis (lifting, mono_tags) max.semilattice_strict_iff_order relcompp.relcompI tranclp_into_tranclp2)
          then show False by auto
        qed
        with A [of i] show "f i \<in> A \<and> strict Q (f (Suc i)) (f i)" by auto
      qed
      ultimately show False unfolding wfp_on_def by blast  
    qed
  qed
qed

lemma wqo_extension:
  assumes wf: "wfp_on P A"
    and anti: "\<not> (\<exists>f. antichain_on P f A)"
    and subrel: "\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> Q x y"
    and refl: "reflp_on Q A"
    and trans: "transp_on Q A"
  shows "wfp_on (strict Q) A"
proof (rule ccontr)
  have "transp_on (strict Q) A"
    using trans unfolding transp_on_def by blast
  then have *: "transp_on ((strict Q)\<inverse>\<inverse>) A" by (rule transp_on_converse)
  assume "\<not> wfp_on (strict Q) A"
  then obtain f :: "nat \<Rightarrow> 'a" where A: "\<And>i. f i \<in> A"
    and "\<forall>i. strict Q (f (Suc i)) (f i)" unfolding wfp_on_def by blast+
  then have "chain_on ((strict Q)\<inverse>\<inverse>) f A" by auto
  from chain_on_transp_on_less [OF this *]
    have *: "\<And>i j. i < j \<Longrightarrow> \<not> P (f i) (f j)"
    using subrel and A by blast
  show False
  proof (cases)
    assume "\<exists>k. \<forall>i>k. \<exists>j>i. P (f j) (f i)"
    then obtain k where "\<forall>i>k. \<exists>j>i. P (f j) (f i)" by auto
    from subchain [of k _ f, OF this] obtain g
      where "\<And>i j. i < j \<Longrightarrow> g i < g j"
      and "\<And>i. P (f (g (Suc i))) (f (g i))" by auto
    with * have "\<And>i. P (f (g (Suc i))) (f (g i))" by blast
    with wf [unfolded wfp_on_def not_ex, THEN spec, of "\<lambda>i. f (g i)"] and A
      show False by fast
  next
    assume "\<not> (\<exists>k. \<forall>i>k. \<exists>j>i. P (f j) (f i))"
    then have "\<forall>k. \<exists>i>k. \<forall>j>i. \<not> P (f j) (f i)" by auto
    from choice [OF this] obtain h
      where "\<forall>k. h k > k"
      and **: "\<forall>k. (\<forall>j>h k. \<not> P (f j) (f (h k)))" by auto
    def [simp]: \<phi> \<equiv> "\<lambda>i. (h ^^ Suc i) 0"
    have "\<And>i. \<phi> i < \<phi> (Suc i)"
      using `\<forall>k. h k > k` by (induct_tac i) auto
    then have mono: "\<And>i j. i < j \<Longrightarrow> \<phi> i < \<phi> j" by (metis lift_Suc_mono_less)
    then have "\<forall>i j. i < j \<longrightarrow> \<not> P (f (\<phi> j)) (f (\<phi> i))"
      using ** by auto
    with mono [THEN *]
      have "\<forall>i j. i < j \<longrightarrow> incomparable P (f (\<phi> j)) (f (\<phi> i))" by blast
    moreover have "\<exists>i j. i < j \<and> \<not> incomparable P (f (\<phi> i)) (f (\<phi> j))"
      using anti [unfolded not_ex, THEN spec, of "\<lambda>i. f (\<phi> i)"] and A by blast
    ultimately show False by blast
  qed
qed

text {*The homomorphic image of a wqo set is wqo.*}
lemma wqo_on_hom:
  assumes "transp_on Q (h ` A)"
    and "\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> Q (h x) (h y)"
    and "wqo_on P A"
  shows "wqo_on Q (h ` A)"
  using assms and almost_full_on_hom [of A P Q h]
  unfolding wqo_on_def by blast

text {*The monomorphic preimage of a wqo set is wqo.*}
lemma wqo_on_mon:
  assumes trans: "transp_on P A"
    and mon: "\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longleftrightarrow> Q (h x) (h y)" "bij_betw h A B"
    and wqo: "wqo_on Q B"
  shows "wqo_on P A"
  using assms and almost_full_on_mon [of A P Q h]
  unfolding wqo_on_def by blast


subsection {* A Typeclass for Well-Quasi-Orders *}

text {*In a well-quasi-order (wqo) every infinite sequence is good.*}
class wqo = preorder +
  assumes good: "good (op \<le>) f"

text {*The following lemma converts between @{const wqo_on} (for the special
case that the domain is the universe of a type) and the class predicate
@{const class.wqo}.*}
lemma wqo_on_UNIV_conv:
  "wqo_on P UNIV \<longleftrightarrow> class.wqo P (strict P)" (is "?lhs = ?rhs")
proof
  assume "?lhs" thus "?rhs"
    unfolding wqo_on_def class.wqo_def class.preorder_def class.wqo_axioms_def
    using almost_full_on_imp_reflp_on [of P UNIV]
    by (auto simp: reflp_on_def almost_full_on_def)
       (unfold transp_on_def, blast)
next
  assume "?rhs" thus "?lhs"
    unfolding class.wqo_def class.preorder_def class.wqo_axioms_def
    by (auto simp: wqo_on_def almost_full_on_def transp_on_def)
qed

text {*The strict part of a wqo is well-founded.*}
lemma (in wqo) "wfP (op <)"
proof -
  have "class.wqo (op \<le>) (op <)" ..
  hence "wqo_on (op \<le>) UNIV"
    unfolding less_le_not_le [abs_def] wqo_on_UNIV_conv [symmetric] .
  from wqo_on_imp_wfp_on [OF this]
    show ?thesis unfolding less_le_not_le [abs_def] wfp_on_UNIV .
qed

lemma wqo_on_with_bot:
  assumes "wqo_on P A"
  shows "wqo_on (option_le P) A\<^sub>\<bottom>"
    (is "wqo_on ?P ?A")
proof -
  {
    from assms have trans [unfolded transp_on_def]: "transp_on P A"
      by (auto simp: wqo_on_def)
    have "transp_on ?P ?A"
      unfolding transp_on_def by (auto, insert trans) (blast+)
  } moreover {
    from assms and almost_full_on_with_bot
      have "almost_full_on ?P ?A" by (auto simp: wqo_on_def)
  } ultimately show ?thesis by (auto simp: wqo_on_def)
qed

text {*When two sets are wqo, then their disjoint sum is wqo.*}
lemma wqo_on_Plus:
  assumes "wqo_on P A" and "wqo_on Q B"
  shows "wqo_on (sum_le P Q) (A <+> B)"
    (is "wqo_on ?P ?A")
proof -
  {
    from assms have trans [unfolded transp_on_def]: "transp_on P A" "transp_on Q B"
      by (auto simp: wqo_on_def)
    have "transp_on ?P ?A"
      unfolding transp_on_def by (auto, insert trans) (blast+)
  } moreover {
    from assms and almost_full_on_Plus have "almost_full_on ?P ?A" by (auto simp: wqo_on_def)
  } ultimately show ?thesis by (auto simp: wqo_on_def)
qed


subsection {* Dickson's Lemma *}

lemma wqo_on_Sigma:
  fixes A1 :: "'a set" and A2 :: "'b set"
  assumes "wqo_on P1 A1" and "wqo_on P2 A2"
  shows "wqo_on (prod_le P1 P2) (A1 \<times> A2)"
    (is "wqo_on ?P ?A")
proof -
  {
    from assms have "transp_on P1 A1" and "transp_on P2 A2" by (auto simp: wqo_on_def)
    hence "transp_on ?P ?A" unfolding transp_on_def prod_le_def by blast
  } moreover {
    from assms and almost_full_on_Sigma [of P1 A1 P2 A2]
      have "almost_full_on ?P ?A" by (auto simp: wqo_on_def)
  } ultimately show ?thesis by (auto simp: wqo_on_def)
qed

lemmas dickson = wqo_on_Sigma


subsection {* Higman's Lemma *}

lemma wqo_on_lists:
  assumes "wqo_on P A" shows "wqo_on (list_hembeq P) (lists A)"
  using assms and almost_full_on_lists
    and transp_on_list_hembeq by (auto simp: wqo_on_def)

lemmas higman = wqo_on_lists

text {*Every reflexive and transitive relation on a finite set is a wqo.*}
lemma finite_wqo_on:
  assumes "finite A"
    and refl: "reflp_on P A" and "transp_on P A"
  shows "wqo_on P A"
  using assms and finite_almost_full_on by (auto simp: wqo_on_def)

lemma finite_eq_wqo_on:
  assumes "finite A"
  shows "wqo_on (op =) A"
  using finite_wqo_on [OF assms, of "op ="]
  by (auto simp: reflp_on_def transp_on_def)

lemma wqo_on_lists_over_finite_sets:
  "wqo_on (list_hembeq (op =)) (UNIV::('a::finite) list set)"
  using wqo_on_lists [OF finite_eq_wqo_on [OF finite [of "UNIV::('a::finite) set"]]] by simp

end

