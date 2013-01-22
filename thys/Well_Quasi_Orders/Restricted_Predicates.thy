(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Binary Predicates Restricted to Elements of a given Set *}

theory Restricted_Predicates
imports Main
begin

definition restrict_to :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)" where
  "restrict_to P A = (\<lambda>x y. x \<in> A \<and> y \<in> A \<and> P x y)"

definition reflp_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "reflp_on P A = (\<forall>a\<in>A. P a a)"

definition transp_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "transp_on P A = (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A. P x y \<and> P y z \<longrightarrow> P x z)"

definition
  mono_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "mono_on P Q f A = (\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> Q (f x) (f y))"

definition total_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "total_on P A = (\<forall>x\<in>A. \<forall>y\<in>A. x = y \<or> P x y \<or> P y x)"

lemma mono_onI [Pure.intro]:
  assumes "\<And>x y. \<lbrakk>x \<in> A; y \<in> A; P x y\<rbrakk> \<Longrightarrow> Q (f x) (f y)"
  shows "mono_on P Q f A"
  using assms by (auto simp: mono_on_def)

abbreviation strict where
  "strict P \<equiv> \<lambda>x y. P x y \<and> \<not> (P y x)"

lemma strict_reflclp_conv [simp]:
  "strict (P\<^sup>=\<^sup>=) = strict P" by auto

abbreviation chain_on where
  "chain_on P f A \<equiv> \<forall>i. f i \<in> A \<and> P (f i) (f (Suc i))"

abbreviation incomparable where
  "incomparable P \<equiv> \<lambda>x y. \<not> P x y \<and> \<not> P y x"

abbreviation antichain_on where
  "antichain_on P f A \<equiv> \<forall>(i::nat) j. f i \<in> A \<and> (i < j \<longrightarrow> incomparable P (f i) (f j))"

lemma reflp_onI [Pure.intro]:
  "(\<And>a. a \<in> A \<Longrightarrow> P a a) \<Longrightarrow> reflp_on P A"
  unfolding reflp_on_def by blast

lemma transp_onI [Pure.intro]:
  "(\<And>x y z. \<lbrakk>x \<in> A; y \<in> A; z \<in> A; P x y; P y z\<rbrakk> \<Longrightarrow> P x z) \<Longrightarrow> transp_on P A"
  unfolding transp_on_def by blast

lemma total_onI [Pure.intro]:
  "(\<And>x y. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> x = y \<or> P x y \<or> P y x) \<Longrightarrow> total_on P A"
  unfolding total_on_def by blast

lemma reflp_on_reflclp_simp [simp]:
  assumes "reflp_on P A" and "a \<in> A" and "b \<in> A"
  shows "P\<^sup>=\<^sup>= a b = P a b"
  using assms by (auto simp: reflp_on_def)

lemma reflp_on_reflclp:
  "reflp_on (P\<^sup>=\<^sup>=) A"
  by (auto simp: reflp_on_def)

lemma transp_on_tranclp:
  assumes "transp_on P A"
  shows "(\<lambda>x y. x \<in> A \<and> y \<in> A \<and> P x y)\<^sup>+\<^sup>+ a b \<longleftrightarrow> a \<in> A \<and> b \<in> A \<and> P a b"
    (is "?lhs = ?rhs")
  by (rule iffI, induction rule: tranclp.induct)
     (insert assms, auto simp: transp_on_def)

lemma reflp_on_converse:
  "reflp_on P A \<Longrightarrow> reflp_on P\<inverse>\<inverse> A"
  unfolding reflp_on_def by blast

lemma transp_on_converse:
  "transp_on P A \<Longrightarrow> transp_on P\<inverse>\<inverse> A"
  unfolding transp_on_def by blast

lemma transp_on_reflclp:
  "transp_on P A \<Longrightarrow> transp_on P\<^sup>=\<^sup>= A"
  unfolding transp_on_def by blast

lemma transp_on_strict:
  "transp_on P A \<Longrightarrow> transp_on (strict P) A"
  unfolding transp_on_def by blast

lemma reflp_on_subset:
  "A \<subseteq> B \<Longrightarrow> reflp_on P B \<Longrightarrow> reflp_on P A"
  by (auto simp: reflp_on_def)

lemma transp_on_subset:
  "A \<subseteq> B \<Longrightarrow> transp_on P B \<Longrightarrow> transp_on P A"
  by (auto simp: transp_on_def)

definition wfp_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "wfp_on P A = (\<not> (\<exists>f. \<forall>i. f i \<in> A \<and> P (f (Suc i)) (f i)))"

definition inductive_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "inductive_on P A = (\<forall>Q. (\<forall>y\<in>A. (\<forall>x\<in>A. P x y \<longrightarrow> Q x) \<longrightarrow> Q y) \<longrightarrow> (\<forall>x\<in>A. Q x))"

lemma inductive_onI [Pure.intro]:
  assumes "\<And>Q x. \<lbrakk>x \<in> A; (\<And>y. \<lbrakk>y \<in> A; \<And>x. \<lbrakk>x \<in> A; P x y\<rbrakk> \<Longrightarrow> Q x\<rbrakk> \<Longrightarrow> Q y)\<rbrakk> \<Longrightarrow>  Q x"
  shows "inductive_on P A"
  using assms unfolding inductive_on_def by metis

text {*If @{term P} is well-founded on @{term A} then every non-empty subset @{term Q}
of @{term A} has a minimal element @{term z} w.r.t. @{term P}, i.e., all elements
that are @{term P}-smaller than @{term z} are not in @{term Q}.*}
lemma wfp_on_imp_minimal:
  assumes "wfp_on P A"
  shows "\<forall>Q x. x \<in> Q \<and> Q \<subseteq> A \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. P y z \<longrightarrow> y \<notin> Q)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain Q x where *: "x \<in> Q" "Q \<subseteq> A"
    and "\<forall>z. \<exists>y. z \<in> Q \<longrightarrow> P y z \<and> y \<in> Q" by metis
  from choice [OF this(3)] obtain f
    where **: "\<forall>x\<in>Q. P (f x) x \<and> f x \<in> Q" by blast
  let ?S = "\<lambda>i. (f ^^ i) x"
  have ***: "\<forall>i. ?S i \<in> Q"
  proof
    fix i show "?S i \<in> Q" by (induct i) (auto simp: * **)
  qed
  hence "\<forall>i. ?S i \<in> A" using * by blast
  moreover have "\<forall>i. P (?S (Suc i)) (?S i)"
  proof
    fix i show "P (?S (Suc i)) (?S i)"
      by (induct i) (auto simp: * ** ***)
  qed
  ultimately have "\<forall>i. ?S i \<in> A \<and> P (?S (Suc i)) (?S i)" by blast
  with assms(1) show False
    unfolding wfp_on_def by fast
qed

lemma minimal_imp_inductive_on:
  assumes "\<forall>Q x. x \<in> Q \<and> Q \<subseteq> A \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. P y z \<longrightarrow> y \<notin> Q)" 
  shows "inductive_on P A"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain Q x
    where *: "\<forall>y\<in>A. (\<forall>x\<in>A. P x y \<longrightarrow> Q x) \<longrightarrow> Q y"
    and **: "x \<in> A" "\<not> Q x"
    by (auto simp: inductive_on_def)
  let ?Q = "{x\<in>A. \<not> Q x}"
  from ** have "x \<in> ?Q" by auto
  moreover have "?Q \<subseteq> A" by auto
  ultimately obtain z where "z \<in> ?Q"
    and min: "\<forall>y. P y z \<longrightarrow> y \<notin> ?Q"
    using assms [THEN spec [of _ ?Q], THEN spec [of _ x]] by blast
  from `z \<in> ?Q` have "z \<in> A" and "\<not> Q z" by auto
  with * obtain y where "y \<in> A" and "P y z" and "\<not> Q y" by auto
  hence "y \<in> ?Q" by auto
  with `P y z` and min show False by auto
qed

lemmas wfp_on_imp_inductive_on =
  wfp_on_imp_minimal [THEN minimal_imp_inductive_on]

lemma inductive_on_induct [consumes 2, case_names less, induct pred: inductive_on]:
  assumes "inductive_on P A" and "x \<in> A"
    and "\<And>y. \<lbrakk> y \<in> A; \<And>x. \<lbrakk> x \<in> A; P x y \<rbrakk> \<Longrightarrow> Q x \<rbrakk> \<Longrightarrow> Q y"
  shows "Q x"
  using assms unfolding inductive_on_def by metis

lemma inductive_on_imp_wfp_on:
  assumes "inductive_on P A"
  shows "wfp_on P A"
proof -
  let ?Q = "\<lambda>x. \<not> (\<exists>f. f 0 = x \<and> (\<forall>i. f i \<in> A \<and> P (f (Suc i)) (f i)))"
  { fix x assume "x \<in> A"
    with assms have "?Q x"
    proof (induct rule: inductive_on_induct)
      fix y assume "y \<in> A" and IH: "\<And>x. x \<in> A \<Longrightarrow> P x y \<Longrightarrow> ?Q x"
      show "?Q y"
      proof (rule ccontr)
        assume "\<not> ?Q y"
        then obtain f where *: "f 0 = y"
          "\<forall>i. f i \<in> A \<and> P (f (Suc i)) (f i)" by auto
        hence "P (f (Suc 0)) (f 0)" and "f (Suc 0) \<in> A" by auto
        with IH and * have "?Q (f (Suc 0))" by auto
        with * show False by auto
      qed
    qed }
  thus ?thesis unfolding wfp_on_def by blast
qed

definition antisymp_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "antisymp_on P A = (\<forall>a\<in>A. \<forall>b\<in>A. P a b \<and> P b a \<longrightarrow> a = b)"

lemma antisymp_onI [Pure.intro]:
  "(\<And>a b. \<lbrakk> a \<in> A; b \<in> A; P a b; P b a\<rbrakk> \<Longrightarrow> a = b) \<Longrightarrow> antisymp_on P A"
  by (auto simp: antisymp_on_def)

lemma antisymp_on_reflclp [simp]:
  "antisymp_on P\<^sup>=\<^sup>= A = antisymp_on P A"
  by (auto simp: antisymp_on_def)

lemma transp_on_imp_transp_on_reflclp:
  "transp_on P A \<Longrightarrow> transp_on P\<^sup>=\<^sup>= A"
  unfolding transp_on_def
  by (metis (hide_lams, mono_tags) sup2CI sup2E)

definition qo_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "qo_on P A = (reflp_on P A \<and> transp_on P A)"

definition orderp_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "orderp_on P A = (antisymp_on P A \<and> reflp_on P A \<and> transp_on P A)"

definition irreflp_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "irreflp_on P A = (\<forall>a\<in>A. \<not> P a a)"

definition po_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "po_on P A = (irreflp_on P A \<and> transp_on P A)"

lemma po_onI [Pure.intro]:
  "\<lbrakk>irreflp_on P A; transp_on P A\<rbrakk> \<Longrightarrow> po_on P A"
  by (auto simp: po_on_def)

lemma irreflp_onI [Pure.intro]:
  "(\<And>a. a \<in> A \<Longrightarrow> \<not> P a a) \<Longrightarrow> irreflp_on P A"
  unfolding irreflp_on_def by blast

lemma po_on_imp_irreflp_on:
  "po_on P A \<Longrightarrow> irreflp_on P A"
  by (auto simp: po_on_def)

lemma po_on_imp_transp_on:
  "po_on P A \<Longrightarrow> transp_on P A"
  by (auto simp: po_on_def)

lemma mono_on_irreflp_on:
  assumes "irreflp_on Q B"
    and "f ` A \<subseteq> B"
    and "mono_on P Q f A"
  shows "irreflp_on P A"
  using assms by (auto simp: irreflp_on_def mono_on_def)

lemma irreflp_on_subset:
  assumes "A \<subseteq> B" and "irreflp_on P B"
  shows "irreflp_on P A"
  using assms by (auto simp: irreflp_on_def)

lemma po_on_subset:
  assumes "A \<subseteq> B" and "po_on P B"
  shows "po_on P A"
  using transp_on_subset and irreflp_on_subset and assms
  unfolding po_on_def by blast

lemma transp_on_irreflp_on_imp_antisymp_on:
  assumes "transp_on P A" and "irreflp_on P A"
  shows "antisymp_on (P\<^sup>=\<^sup>=) A"
proof
  fix a b assume "a \<in> A"
    and "b \<in> A" and "P\<^sup>=\<^sup>= a b" and "P\<^sup>=\<^sup>= b a"
  show "a = b"
  proof (rule ccontr)
    assume "a \<noteq> b"
    with `P\<^sup>=\<^sup>= a b` and `P\<^sup>=\<^sup>= b a` have "P a b" and "P b a" by auto
    with `transp_on P A` and `a \<in> A` and `b \<in> A` have "P a a" unfolding transp_on_def by blast
    with `irreflp_on P A` and `a \<in> A` show False unfolding irreflp_on_def by blast
  qed
qed

lemma po_on_imp_antisymp_on:
  assumes "po_on P A"
  shows "antisymp_on (P\<^sup>=\<^sup>=) A"
  using transp_on_irreflp_on_imp_antisymp_on [of P A]
    and assms
  unfolding po_on_def by blast

lemma strict_reflclp [simp]:
  assumes "x \<in> A" and "y \<in> A"
    and "transp_on P A" and "irreflp_on P A"
  shows "strict (P\<^sup>=\<^sup>=) x y = P x y"
  using assms unfolding transp_on_def irreflp_on_def
  by blast

lemma qo_on_imp_reflp_on:
  "qo_on P A \<Longrightarrow> reflp_on P A"
  by (auto simp: qo_on_def)

lemma qo_on_imp_transp_on:
  "qo_on P A \<Longrightarrow> transp_on P A"
  by (auto simp: qo_on_def)

lemma qo_on_subset:
  "A \<subseteq> B \<Longrightarrow> qo_on P B \<Longrightarrow> qo_on P A"
  unfolding qo_on_def
  using reflp_on_subset
    and transp_on_subset by blast

text {*Quasi-orders are instances of the @{class preorder} class.*}
lemma qo_on_UNIV_conv:
  "qo_on P UNIV \<longleftrightarrow> class.preorder P (strict P)" (is "?lhs = ?rhs")
proof
  assume "?lhs" thus "?rhs"
    unfolding qo_on_def class.preorder_def
    using qo_on_imp_reflp_on [of P UNIV]
      and qo_on_imp_transp_on [of P UNIV]
    by (auto simp: reflp_on_def) (unfold transp_on_def, blast)
next
  assume "?rhs" thus "?lhs"
    unfolding class.preorder_def
    by (auto simp: qo_on_def reflp_on_def transp_on_def)
qed

lemma wfp_on_iff_inductive_on:
  "wfp_on P A \<longleftrightarrow> inductive_on P A"
  by (blast intro: inductive_on_imp_wfp_on wfp_on_imp_inductive_on)

lemma wfp_on_iff_minimal:
  "wfp_on P A \<longleftrightarrow> (\<forall>Q x.
     x \<in> Q \<and> Q \<subseteq> A \<longrightarrow>
     (\<exists>z\<in>Q. \<forall>y. P y z \<longrightarrow> y \<notin> Q))"
  using wfp_on_imp_minimal [of P A]
    and minimal_imp_inductive_on [of A P]
    and inductive_on_imp_wfp_on [of P A]
    by blast

text {*Every non-empty well-founded set @{term A} has a minimal element, i.e., an
element that is not greater than any other element.*}
lemma wfp_on_imp_has_min_elt:
  assumes "wfp_on (strict P) A" and "A \<noteq> {}"
  shows "\<exists>x\<in>A. \<forall>y\<in>A. \<not> strict P y x"
  using assms unfolding wfp_on_iff_minimal by force

lemma wfp_on_induct [consumes 2, case_names less, induct pred: wfp_on]:
  assumes "wfp_on P A" and "x \<in> A"
    and "\<And>y. \<lbrakk> y \<in> A; \<And>x. \<lbrakk> x \<in> A; P x y \<rbrakk> \<Longrightarrow> Q x \<rbrakk> \<Longrightarrow> Q y"
  shows "Q x"
  using assms and inductive_on_induct [of P A x]
  unfolding wfp_on_iff_inductive_on by blast

lemma wfp_on_UNIV [simp]:
  "wfp_on P UNIV \<longleftrightarrow> wfP P"
  unfolding wfp_on_iff_inductive_on inductive_on_def wfP_def wf_def by force


subsection {*Measures on Sets (Instead of Full Types)*}

definition
  inv_image_betw ::
    "('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)"
where
  "inv_image_betw P f A B = (\<lambda>x y. x \<in> A \<and> y \<in> A \<and> f x \<in> B \<and> f y \<in> B \<and> P (f x) (f y))"

definition
  measure_on :: "('a \<Rightarrow> nat) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "measure_on f A = inv_image_betw (op <) f A UNIV"

lemma in_inv_image_betw [simp]:
  "inv_image_betw P f A B x y \<longleftrightarrow> x \<in> A \<and> y \<in> A \<and> f x \<in> B \<and> f y \<in> B \<and> P (f x) (f y)"
  by (auto simp: inv_image_betw_def)

lemma in_measure_on [simp, code_unfold]:
  "measure_on f A x y \<longleftrightarrow> x \<in> A \<and> y \<in> A \<and> f x < f y"
  by (simp add: measure_on_def)

lemma wfp_on_inv_image_betw [simp, intro!]:
  assumes "wfp_on P B"
  shows "wfp_on (inv_image_betw P f A B) A"
    (is "wfp_on ?P A")
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain g where "\<forall>i. g i \<in> A \<and> ?P (g (Suc i)) (g i)"
    unfolding wfp_on_def by auto
  with assms show False unfolding wfp_on_def by auto
qed

lemma wfp_less:
  "wfp_on (op <) (UNIV :: nat set)"
  using wf_less by (auto simp: wfP_def)

lemma wfp_on_measure_on [iff]:
  "wfp_on (measure_on f A) A"
  unfolding measure_on_def
  by (rule wfp_less [THEN wfp_on_inv_image_betw])

lemma wfp_on_mono:
  "A \<subseteq> B \<Longrightarrow> (\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> P x y \<Longrightarrow> Q x y) \<Longrightarrow> wfp_on Q B \<Longrightarrow> wfp_on P A"
  unfolding wfp_on_def by (metis set_mp)

lemma wfp_on_subset:
  "A \<subseteq> B \<Longrightarrow> wfp_on P B \<Longrightarrow> wfp_on P A"
  using wfp_on_mono by blast

lemma restrict_to_iff [iff]:
  "restrict_to P A x y \<longleftrightarrow> x \<in> A \<and> y \<in> A \<and> P x y"
  by (simp add: restrict_to_def)

lemma wfp_on_restrict_to [simp]:
  "wfp_on (restrict_to P A) A = wfp_on P A"
  unfolding wfp_on_def by auto

lemma irreflp_on_strict [simp, intro]:
  "irreflp_on (strict P) A"
  by (auto simp: irreflp_on_def)

lemma transp_on_map:
  assumes "transp_on Q B"
    and "h ` A \<subseteq> B"
  shows "transp_on (\<lambda>x y. Q (h x) (h y)) A"
  using assms unfolding transp_on_def
  by auto (metis image_eqI set_mp)

lemma irreflp_on_map:
  assumes "irreflp_on Q B"
    and "h ` A \<subseteq> B"
  shows "irreflp_on (\<lambda>x y. Q (h x) (h y)) A"
  using assms unfolding irreflp_on_def by auto

lemma po_on_map:
  assumes "po_on Q B"
    and "h ` A \<subseteq> B"
  shows "po_on (\<lambda>x y. Q (h x) (h y)) A"
  using assms and transp_on_map and irreflp_on_map
  unfolding po_on_def by auto

lemma transp_on_imp_transp_on_strict:
  "transp_on P A \<Longrightarrow> transp_on (strict P) A"
  unfolding transp_on_def by blast

lemma chain_on_transp_on_less:
  assumes "chain_on P f A" and "transp_on P A" and "i < j"
  shows "P (f i) (f j)"
using `i < j`
proof (induct j)
  case 0 thus ?case by simp
next
  case (Suc j)
  show ?case
  proof (cases "i = j")
    case True
    with Suc show ?thesis using assms(1) by simp
  next
    case False
    with Suc have "P (f i) (f j)" by force
    moreover from assms have "P (f j) (f (Suc j))" by auto
    ultimately show ?thesis using assms(1, 2) unfolding transp_on_def by blast
  qed
qed

lemma restrict_to_reflclp:
  "restrict_to P\<^sup>=\<^sup>= A x y \<Longrightarrow> (restrict_to P A)\<^sup>=\<^sup>= x y"
  by (auto simp: restrict_to_def)

lemma wfp_on_imp_irreflp_on:
  assumes "wfp_on P A"
  shows "irreflp_on P A"
proof
  fix x
  assume "x \<in> A"
  show "\<not> P x x"
  proof
    let ?f = "\<lambda>_. x"
    assume "P x x"
    then have "\<forall>i. P (?f (Suc i)) (?f i)" by blast
    with `x \<in> A` have "\<not> wfp_on P A" by (auto simp: wfp_on_def)
    with assms show False by contradiction
  qed
qed

inductive
  accessible_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  for P and A
where
  accessible_onI [Pure.intro]:
    "\<lbrakk>x \<in> A; \<And>y. \<lbrakk>y \<in> A; P y x\<rbrakk> \<Longrightarrow> accessible_on P A y\<rbrakk> \<Longrightarrow> accessible_on P A x"

lemma accessible_on_imp_mem:
  assumes "accessible_on P A a"
  shows "a \<in> A"
  using assms by (induct) auto

lemma accessible_on_induct [consumes 1, induct pred: accessible_on]:
  assumes *: "accessible_on P A a"
    and IH: "\<And>x. \<lbrakk>accessible_on P A x; \<And>y. \<lbrakk>y \<in> A; P y x\<rbrakk> \<Longrightarrow> Q y\<rbrakk> \<Longrightarrow> Q x"
  shows "Q a"
  apply (rule * [THEN accessible_on.induct])
  apply (rule IH)
  apply (rule accessible_onI)
  by auto

lemma accessible_on_downward:
  "accessible_on P A b \<Longrightarrow> a \<in> A \<Longrightarrow> P a b \<Longrightarrow> accessible_on P A a"
  by (cases rule: accessible_on.cases) fast

lemma accessible_on_restrict_to_downwards:
  assumes "(restrict_to P A)\<^sup>+\<^sup>+ a b" and "accessible_on P A b"
  shows "accessible_on P A a"
  using assms
  by (induct) (auto dest: accessible_on_imp_mem accessible_on_downward)

lemma accessible_on_imp_inductive_on:
  assumes "\<forall>x\<in>A. accessible_on P A x"
  shows "inductive_on P A"
proof
  fix Q x
  assume "x \<in> A"
    and *: "\<And>y. \<lbrakk>y \<in> A; \<And>x. \<lbrakk>x \<in> A; P x y\<rbrakk> \<Longrightarrow> Q x\<rbrakk> \<Longrightarrow> Q y"
  with assms have "accessible_on P A x" by auto
  then show "Q x"
  proof (induct)
    case (1 z)
    then have "z \<in> A" by (blast dest: accessible_on_imp_mem)
    show ?case by (rule *) fact+
  qed
qed

lemmas accessible_on_imp_wfp_on = accessible_on_imp_inductive_on [THEN inductive_on_imp_wfp_on]

lemma wfp_on_tranclp_imp_wfp_on:
  assumes "wfp_on (P\<^sup>+\<^sup>+) A"
  shows "wfp_on P A"
  by (rule ccontr) (insert assms, auto simp: wfp_on_def)

lemma inductive_on_imp_accessible_on:
  assumes "inductive_on P A"
  shows "\<forall>x\<in>A. accessible_on P A x"
proof
  fix x
  assume "x \<in> A"
  with assms show "accessible_on P A x"
    by (induct) (auto intro: accessible_onI)
qed

lemma inductive_on_accessible_on_conv:
  "inductive_on P A \<longleftrightarrow> (\<forall>x\<in>A. accessible_on P A x)"
  using inductive_on_imp_accessible_on
    and accessible_on_imp_inductive_on
    by blast

lemmas wfp_on_imp_accessible_on =
  wfp_on_imp_inductive_on [THEN inductive_on_imp_accessible_on]

lemma accessible_on_tranclp:
  assumes "accessible_on P A x"
  shows "accessible_on ((restrict_to P A)\<^sup>+\<^sup>+) A x"
    (is "accessible_on ?P A x")
  using assms
proof (induct)
  case (1 x)
  then have "x \<in> A" by (blast dest: accessible_on_imp_mem)
  then show ?case
  proof (rule accessible_onI)
    fix y
    assume "y \<in> A"
    assume "?P y x"
    then show "accessible_on ?P A y"
    proof (cases)
      assume "restrict_to P A y x"
      with 1 and `y \<in> A` show ?thesis by blast
    next
      fix z
      assume "?P y z" and "restrict_to P A z x"
      with 1 have "accessible_on ?P A z" by (auto simp: restrict_to_def)
      from accessible_on_downward [OF this `y \<in> A` `?P y z`]
        show ?thesis .
    qed
  qed
qed

lemma wfp_on_restrict_to_tranclp:
  assumes "wfp_on P A"
  shows "wfp_on ((restrict_to P A)\<^sup>+\<^sup>+) A"
  using wfp_on_imp_accessible_on [OF assms]
    and accessible_on_tranclp [of P A]
    and accessible_on_imp_wfp_on [of A "(restrict_to P A)\<^sup>+\<^sup>+"]
    by blast

lemma wfp_on_restrict_to_tranclp':
  assumes "wfp_on (restrict_to P A)\<^sup>+\<^sup>+ A"
  shows "wfp_on P A"
  by (rule ccontr) (insert assms, auto simp: wfp_on_def)

lemma wfp_on_restrict_to_tranclp_wfp_on_conv:
  "wfp_on (restrict_to P A)\<^sup>+\<^sup>+ A \<longleftrightarrow> wfp_on P A"
  using wfp_on_restrict_to_tranclp [of P A]
    and wfp_on_restrict_to_tranclp' [of P A]
    by blast

lemma tranclp_idemp [simp]:
  "(P\<^sup>+\<^sup>+)\<^sup>+\<^sup>+ = P\<^sup>+\<^sup>+" (is "?l = ?r")
proof (intro ext)
  fix x y
  show "?l x y = ?r x y"
  proof
    assume "?l x y" then show "?r x y" by (induct) auto
  next
    assume "?r x y" then show "?l x y" by (induct) auto
  qed
qed


(*TODO: move the following 3 lemmas to Transitive_Closure?*)
lemma stepfun_imp_tranclp:
  assumes "f 0 = x" and "f (Suc n) = z"
    and "\<forall>i\<le>n. P (f i) (f (Suc i))"
  shows "P\<^sup>+\<^sup>+ x z"
  using assms
  by (induct n arbitrary: x z)
     (auto intro: tranclp.trancl_into_trancl)

lemma tranclp_imp_stepfun:
  assumes "P\<^sup>+\<^sup>+ x z"
  shows "\<exists>f n. f 0 = x \<and> f (Suc n) = z \<and> (\<forall>i\<le>n. P (f i) (f (Suc i)))"
    (is "\<exists>f n. ?P x z f n")
  using assms
proof (induct rule: tranclp_induct)
  case (base y)
  let ?f = "(\<lambda>_. y)(0 := x)"
  have "?f 0 = x" and "?f (Suc 0) = y" by auto
  moreover have "\<forall>i\<le>0. P (?f i) (?f (Suc i))"
    using base by auto
  ultimately show ?case by blast
next
  case (step y z)
  then obtain f n where IH: "?P x y f n" by blast
  then have *: "\<forall>i\<le>n. P (f i) (f (Suc i))"
    and [simp]: "f 0 = x" "f (Suc n) = y"
    by auto
  let ?n = "Suc n"
  let ?f = "f(Suc ?n := z)"
  have "?f 0 = x" and "?f (Suc ?n) = z" by auto
  moreover have "\<forall>i\<le>?n. P (?f i) (?f (Suc i))"
    using `P y z` and * by auto
  ultimately show ?case by blast
qed

lemma tranclp_stepfun_conv:
  "P\<^sup>+\<^sup>+ x y \<longleftrightarrow> (\<exists>f n. f 0 = x \<and> f (Suc n) = y \<and> (\<forall>i\<le>n. P (f i) (f (Suc i))))"
  using tranclp_imp_stepfun and stepfun_imp_tranclp by metis

end

