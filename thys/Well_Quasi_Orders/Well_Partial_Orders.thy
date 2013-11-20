(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Well-Partial-Orders *}

theory Well_Partial_Orders
imports
  Almost_Full_Relations
  "~~/src/HOL/Cardinals/Wellorder_Extension"
begin

subsection {* Basic Definitions *}

definition wpo_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "wpo_on P A = (po_on P A \<and> almost_full_on (P\<^sup>=\<^sup>=) A)"

lemma wpo_onI [Pure.intro]:
  "\<lbrakk>irreflp_on P A; transp_on P A; almost_full_on (P\<^sup>=\<^sup>=) A\<rbrakk> \<Longrightarrow> wpo_on P A"
  unfolding wpo_on_def po_on_def by blast

subsection {* Equivalent Definitions *}

text {*Given a partial-order @{term P}, the following statements are equivalent:
\begin{enumerate}
\item @{term P} is a almost-full.
\item @{term P} does neither allow decreasing chains nor antichains.
\item Every partial-order extending @{term P} is well-founded.
\end{enumerate}
*}

lemma wpo_af_conv:
  assumes "po_on P A"
  shows "wpo_on P A \<longleftrightarrow> almost_full_on (P\<^sup>=\<^sup>=) A"
  using assms by (metis wpo_on_def)

lemma wpo_wf_and_no_antichain_conv:
  assumes "po_on P A"
  shows "wpo_on P A \<longleftrightarrow> wfp_on P A \<and> \<not> (\<exists>f. antichain_on (P\<^sup>=\<^sup>=) f A)"
  unfolding wpo_af_conv [OF assms]
  using po_af_imp_wf_and_no_antichain [OF assms]
    and wf_and_no_antichain_imp_po_extension_wf [of P A]
    and every_po_extension_wf_imp_af [OF _ assms]
    by blast

lemma wpo_extensions_wf_conv:
  assumes "po_on P A"
  shows "wpo_on P A \<longleftrightarrow>
    (\<forall>Q. (\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> Q x y) \<and>
    po_on Q A \<longrightarrow> wfp_on Q A)"
  unfolding wpo_af_conv [OF assms]
  using po_af_imp_wf_and_no_antichain [OF assms]
    and wf_and_no_antichain_imp_po_extension_wf [of P A]
    and every_po_extension_wf_imp_af [OF _ assms]
    by blast

lemma wpo_onD:
  "wpo_on P A \<Longrightarrow> irreflp_on P A \<and> transp_on P A \<and> almost_full_on (P\<^sup>=\<^sup>=) A"
  unfolding wpo_on_def po_on_def by blast

lemma wpo_on_imp_irreflp_on:
  "wpo_on P A \<Longrightarrow> irreflp_on P A"
  by (blast dest: wpo_onD)

lemma wpo_on_imp_transp_on:
  "wpo_on P A \<Longrightarrow> transp_on P A"
  by (blast dest: wpo_onD)

lemma wpo_on_imp_almost_full_on:
  "wpo_on P A \<Longrightarrow> almost_full_on (P\<^sup>=\<^sup>=) A"
  by (blast dest: wpo_onD)

lemma wpo_on_imp_good:
  "wpo_on P A \<Longrightarrow> \<forall>i. f i \<in> A \<Longrightarrow> good (P\<^sup>=\<^sup>=) f"
  by (auto simp: wpo_on_def almost_full_on_def)

lemma wpo_on_subset:
  "A \<subseteq> B \<Longrightarrow> wpo_on P B \<Longrightarrow> wpo_on P A"
  using almost_full_on_subset [of A B "P\<^sup>=\<^sup>="]
    and transp_on_subset [of A B P]
    and irreflp_on_subset [of A B P]
  unfolding wpo_on_def po_on_def by blast

lemma wpo_on_imp_po_on:
  assumes "wpo_on P A" shows "po_on P A"
  using assms by (simp add: wpo_on_def)

lemma wpo_on_imp_antisymp_on:
  assumes "wpo_on P A"
  shows "antisymp_on (P\<^sup>=\<^sup>=) A"
  using assms and transp_on_irreflp_on_imp_antisymp_on [of P A]
  unfolding wpo_on_def po_on_def by blast

lemma wpo_on_imp_wfp_on:
  assumes "wpo_on P A"
  shows "wfp_on P A"
proof (rule ccontr)
  have "transp_on P A" by (rule wpo_on_imp_transp_on [OF assms])
  hence "transp_on P\<inverse>\<inverse> A" by (rule transp_on_converse)
  have "antisymp_on (P\<^sup>=\<^sup>=) A" by (rule wpo_on_imp_antisymp_on [OF assms])
  from wpo_on_imp_irreflp_on [OF assms]
    have "irreflp_on P A" .
  assume "\<not> wfp_on P A"
  then obtain f where *: "\<forall>i. f i \<in> A"
    and **: "\<forall>i. P (f (Suc i)) (f i)" by (auto simp: wfp_on_def)
  from chain_on_transp_on_less [of f A "P\<inverse>\<inverse>", OF _ `transp_on P\<inverse>\<inverse> A`] and * and **
    have "\<forall>i j. i < j \<longrightarrow> P (f j) (f i)" by auto
  with `irreflp_on P A` and `antisymp_on (P\<^sup>=\<^sup>=) A`
    have "\<forall>i j. i < j \<longrightarrow> \<not> (P\<^sup>=\<^sup>= (f i) (f j))"
    unfolding irreflp_on_def antisymp_on_def using *
    by (metis sup2CI)
  hence "bad (P\<^sup>=\<^sup>=) f" by (auto simp: good_def)
  with * and assms show False
    unfolding wpo_on_def almost_full_on_def by blast
qed


subsection {* A Typeclass for Well-Partial-Orders *}

text {*In a well-partial-order (wpo) every infinite sequence is good.*}
class wpo = order +
  assumes good: "good (op \<le>) f"

text {*The following lemma converts between @{const wpo_on} (for the special
case that the domain is the universe of a type) and the class predicate
@{const class.wpo}.*}
lemma wpo_on_UNIV_conv:
  "wpo_on P UNIV \<longleftrightarrow> class.wpo P\<^sup>=\<^sup>= P" (is "?lhs = ?rhs")
proof
  assume "?lhs"
  then have irrefl: "irreflp_on P UNIV"
    and trans: "transp_on P UNIV"
    and af: "almost_full_on (P\<^sup>=\<^sup>=) UNIV"
    by (blast dest: wpo_onD)+
  from irrefl and trans have "\<And>x y. P x y = strict (P\<^sup>=\<^sup>=) x y"
    by (unfold irreflp_on_def transp_on_def) blast
  moreover
  from af have "reflp_on (P\<^sup>=\<^sup>=) UNIV" by (rule almost_full_on_imp_reflp_on)
  moreover
  from trans have "transp_on (P\<^sup>=\<^sup>=) UNIV" by (unfold transp_on_def) blast
  moreover
  from trans and irrefl have "antisymp_on (P\<^sup>=\<^sup>=) UNIV"
    by (rule transp_on_irreflp_on_imp_antisymp_on)
  ultimately
  show "?rhs"
    using af
    unfolding reflp_on_def transp_on_def antisymp_on_def almost_full_on_def
    by (unfold_locales) fast+
next
  assume "?rhs" thus "?lhs"
    unfolding class.wpo_def class.preorder_def class.order_def class.order_axioms_def class.wpo_axioms_def
    by (auto simp: wpo_on_def po_on_def almost_full_on_def transp_on_def irreflp_on_def) metis
qed

lemma (in wpo) le_less_eq:
  "x \<le> y = op <\<^sup>=\<^sup>= x y"
  by (auto simp: less_le_not_le)

text {*A wpo is well-founded.*}
lemma (in wpo) "wfP (op <)"
proof -
  have "class.wpo (op \<le>) (op <)" ..
  hence "wpo_on (op <) UNIV"
    unfolding le_less_eq [abs_def] wpo_on_UNIV_conv [symmetric] .
  from wpo_on_imp_wfp_on [OF this]
    show ?thesis unfolding less_le_not_le [abs_def] wfp_on_UNIV .
qed

lemma wpo_on_with_bot:
  assumes "wpo_on P A"
  shows "wpo_on (option_less P) A\<^sub>\<bottom>"
    (is "wpo_on ?P ?A")
proof -
  {
    from assms have "irreflp_on P A" by (rule wpo_on_imp_irreflp_on)
    then have "irreflp_on ?P ?A"
      unfolding irreflp_on_def by (auto split: option.splits)
  }
  moreover {
    from assms have trans [unfolded transp_on_def]: "transp_on P A"
      by (auto simp: po_on_def wpo_on_def)
    have "transp_on ?P ?A"
      unfolding transp_on_def by (auto, insert trans) (blast+)
  }
  moreover {
    from assms have af: "almost_full_on P\<^sup>=\<^sup>= A" by (rule wpo_on_imp_almost_full_on)
    from almost_full_on_with_bot [OF af]
      have "almost_full_on ?P\<^sup>=\<^sup>= ?A" by simp
  } ultimately show ?thesis by (auto simp: po_on_def wpo_on_def)
qed

text {*When two sets are wpo, then their disjoint sum is wpo.*}
lemma wpo_on_Plus:
  assumes "wpo_on P A" and "wpo_on Q B"
  shows "wpo_on (sum_less P Q) (A <+> B)"
    (is "wpo_on ?P ?A")
proof -
  {
    from assms have "irreflp_on P A" and "irreflp_on Q B" by (auto elim: wpo_on_imp_irreflp_on)
    then have "irreflp_on ?P ?A"
      unfolding irreflp_on_def by auto
  } moreover {
    from assms have trans [unfolded transp_on_def]: "transp_on P A" "transp_on Q B"
      by (auto simp: po_on_def wpo_on_def)
    have "transp_on ?P ?A"
      unfolding transp_on_def by (auto, insert trans) (blast+)
  } moreover {
    from assms(1) have af1: "almost_full_on P\<^sup>=\<^sup>= A" by (rule wpo_on_imp_almost_full_on)
    from assms(2) have af2: "almost_full_on Q\<^sup>=\<^sup>= B" by (rule wpo_on_imp_almost_full_on)
    from almost_full_on_Plus [OF af1 af2]
      have "almost_full_on ?P\<^sup>=\<^sup>= ?A" by simp
  } ultimately show ?thesis by (auto simp: po_on_def wpo_on_def)
qed


subsection {* Dickson's Lemma for Well-Partial-Orders *}

lemma wpo_on_Sigma:
  fixes A1 :: "'a set" and A2 :: "'b set"
  assumes "wpo_on P1 A1" and "wpo_on P2 A2"
  shows "wpo_on (prod_less P1 P2) (A1 \<times> A2)"
    (is "wpo_on ?P ?A")
proof -
  {
    from assms have "irreflp_on P1 A1" and "irreflp_on P2 A2" by (auto elim: wpo_on_imp_irreflp_on)
    then have "irreflp_on ?P ?A" unfolding irreflp_on_def by (auto simp: prod_less_def)
  } moreover {
    from assms have "transp_on P1 A1" and "transp_on P2 A2" by (auto simp: po_on_def wpo_on_def)
    hence "transp_on ?P ?A" unfolding transp_on_def prod_less_def by blast
  } moreover {
    from assms(1) have af1: "almost_full_on P1\<^sup>=\<^sup>= A1" by (rule wpo_on_imp_almost_full_on)
    from assms(2) have af2: "almost_full_on P2\<^sup>=\<^sup>= A2" by (rule wpo_on_imp_almost_full_on)
    from almost_full_on_Sigma [OF af1 af2]
      have "almost_full_on ?P\<^sup>=\<^sup>= ?A" by simp
  } ultimately show ?thesis by (auto simp: po_on_def wpo_on_def)
qed


subsection {* Higman's Lemma for Well-Partial-Orders *}

lemma irreflp_on_list_hemb:
  "irreflp_on (list_hemb P) (lists A)"
  by (auto simp: irreflp_on_def list_hemb_def)

lemma wpo_on_lists:
  assumes "wpo_on P A" shows "wpo_on (list_hemb P) (lists A)"
  using assms
    and irreflp_on_list_hemb
    and almost_full_on_list_hemb
    and transp_on_list_hemb
    unfolding po_on_def wpo_on_def by auto

text {*Every irreflexive and transitive relation on a finite set is a wpo.*}
lemma finite_wpo_on:
  assumes "finite A"
    and "irreflp_on P A" and "transp_on P A"
  shows "wpo_on P A"
  using assms
    and finite_almost_full_on [OF `finite A` reflp_on_reflclp]
    by (auto simp: po_on_def wpo_on_def)

lemma finite_wpo_on_empty:
  fixes A :: "('a::finite) set"
  shows "wpo_on (\<lambda>_ _. False) A"
    (is "wpo_on ?P A")
proof
  show "irreflp_on ?P A" by (auto simp: irreflp_on_def)
next
  show "transp_on ?P A" by (auto simp: transp_on_def)
next
  show "almost_full_on ?P\<^sup>=\<^sup>= A"
    using finite_almost_full_on [OF finite reflp_on_reflclp, of ?P A]
    by (simp add: almost_full_on_def)
qed

lemmas wpo_on_lists_over_finite_sets =
  finite_wpo_on [THEN wpo_on_lists]

(*TODO: move*)
lemma nat_le_less_eq [simp]:
  "(op <\<^sup>=\<^sup>= :: nat \<Rightarrow> nat \<Rightarrow> bool) = op \<le>"
  by (intro ext) auto

lemma wpo_on_UNIV_nat:
  "wpo_on (op <) (UNIV :: nat set)"
  unfolding wpo_on_def po_on_def irreflp_on_def transp_on_def
  using almost_full_on_UNIV_nat by simp

text {*There is a well-order on any set.*}
lemma well_order_on:
  "\<exists>P. po_on P A \<and> wfp_on P A \<and> total_on P A"
proof -
  from Zorn.well_order_on [of A] obtain R where "well_order_on A R" by blast
  then have wf_R: "wf (R - Id)" and refl_R: "refl_on A R"
    and antisym_R: "antisym R" and total_R: "Relation.total_on A R"
    and trans_R: "trans R"
    by (auto simp: well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def)
  def Q \<equiv> "\<lambda>x y. (x, y) \<in> R - Id"
  have "wfp_on Q UNIV"
    by (rule inductive_on_imp_wfp_on, insert wf_R, simp only: inductive_on_def wf_def Q_def)
       (metis UNIV_I)
  with wfp_on_subset have "wfp_on Q A" by (metis (full_types) subset_UNIV)
  have antisym_Q: "antisymp_on Q\<^sup>=\<^sup>= UNIV"
    using antisym_R by (auto simp: antisym_def antisymp_on_def Q_def)
  have "total_on Q\<^sup>=\<^sup>= A"
    using total_R by (auto simp: Relation.total_on_def total_on_def Q_def)
  then have "total_on Q A" by (auto simp: total_on_def)
  have "irreflp_on Q A" by (metis `wfp_on Q A` wfp_on_imp_irreflp_on)
  have "transp_on Q\<^sup>=\<^sup>= UNIV"
    using trans_R by (simp only: trans_def transp_on_def Q_def) blast
  with transp_on_subset have "transp_on Q\<^sup>=\<^sup>= A" by (metis (full_types) subset_UNIV)
  then have "transp_on Q A"
    unfolding transp_on_def
    by (auto) (metis (full_types) UNIV_I antisym_Q antisymp_on_def antisymp_on_reflclp)
  with `irreflp_on Q A`
    have "po_on Q A" by (auto simp: po_on_def)
  with `total_on Q A` and `wfp_on Q A`
    show ?thesis by blast
qed

lemma wpo_on_map:
  fixes P and Q and h
  defines "P' \<equiv> \<lambda>x y. P x y \<and> Q\<^sup>=\<^sup>= (h x) (h y)"
  assumes "wpo_on P A"
    and "wpo_on Q B"
    and subset: "h ` A \<subseteq> B"
  shows "wpo_on P' A"
proof
  let ?Q = "\<lambda>x y. Q\<^sup>=\<^sup>= (h x) (h y)"
  from `wpo_on P A` have "irreflp_on P A"
    by (rule wpo_on_imp_irreflp_on)

  then show "irreflp_on P' A"
    unfolding irreflp_on_def P'_def by blast

  from `wpo_on P A` have "transp_on P A"
    by (rule wpo_on_imp_transp_on)
  then have "transp_on P\<^sup>=\<^sup>= A" by (metis transp_on_imp_transp_on_reflclp)
  from `wpo_on Q B` have "transp_on Q\<^sup>=\<^sup>= B"
    by (metis transp_on_imp_transp_on_reflclp wpo_on_imp_transp_on)
  from transp_on_map [OF this subset]
    have "transp_on ?Q A" .

  with `transp_on P A` show "transp_on P' A"
    unfolding transp_on_def P'_def by blast
    
  from `wpo_on P A` have "almost_full_on P\<^sup>=\<^sup>= A"
    by (rule wpo_on_imp_almost_full_on)
  from `wpo_on Q B` have "almost_full_on Q\<^sup>=\<^sup>= B"
    by (rule wpo_on_imp_almost_full_on)

  show "almost_full_on P'\<^sup>=\<^sup>= A"
  proof
    fix f
    presume *: "\<And>i::nat. f i \<in> A"
    from almost_full_on_imp_subchain [OF `almost_full_on P\<^sup>=\<^sup>= A` this, of id] obtain g :: "nat \<Rightarrow> nat"
      where g: "\<And>i j. i < j \<Longrightarrow> g i < g j"
      and **: "\<forall>i. f (g i) \<in> A \<and> P\<^sup>=\<^sup>= (f (g i)) (f (g (Suc i)))"
      using *
      by auto
    from chain_on_transp_on_less [OF ** `transp_on P\<^sup>=\<^sup>= A`]
      have **: "\<And>i j. i < j \<Longrightarrow> P\<^sup>=\<^sup>= (f (g i)) (f (g j))" .
    let ?g = "\<lambda>i. h (f (g i))"
    from * and subset have B: "\<And>i. ?g i \<in> B" by auto
    with `almost_full_on Q\<^sup>=\<^sup>= B` [unfolded almost_full_on_def good_def, THEN spec, of ?g]
      obtain i j :: nat
      where "i < j" and "Q\<^sup>=\<^sup>= (?g i) (?g j)" by blast
    with ** [OF `i < j`] have "P'\<^sup>=\<^sup>= (f (g i)) (f (g j))"
      by (auto simp: P'_def)
    with g [OF `i < j`] show "good P'\<^sup>=\<^sup>= f" by (auto simp: good_def)
  qed simp
qed

end

