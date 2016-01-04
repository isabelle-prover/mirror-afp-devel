(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c.sternagel@gmail.com>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

section \<open>The Almost-Full Property\<close>

theory Almost_Full
imports
  "~~/src/HOL/Library/Sublist"
  "~~/src/HOL/Library/Ramsey"
  "../Regular-Sets/Regexp_Method"
  "../Abstract-Rewriting/Seq"
  Least_Enum
  Infinite_Sequences
  Restricted_Predicates
begin

subsection \<open>Basic Definitions and Facts\<close>

text \<open>
  An infinite sequence is \emph{good} whenever there are indices @{term "i < j"} such that
  @{term "P (f i) (f j)"}.
\<close>
definition good :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "good P f \<longleftrightarrow> (\<exists>i j. i < j \<and> P (f i) (f j))"

text \<open>A sequence that is not good is called \emph{bad}.\<close>
abbreviation "bad P f \<equiv> \<not> good P f"

lemma goodI:
  "\<lbrakk>i < j; P (f i) (f j)\<rbrakk> \<Longrightarrow> good P f"
by (auto simp: good_def)

lemma goodE [elim]:
  "good P f \<Longrightarrow> (\<And>i j. \<lbrakk>i < j; P (f i) (f j)\<rbrakk> \<Longrightarrow> Q) \<Longrightarrow> Q"
 by (auto simp: good_def)

lemma badE [elim]:
  "bad P f \<Longrightarrow> ((\<And>i j. i < j \<Longrightarrow> \<not> P (f i) (f j)) \<Longrightarrow> Q) \<Longrightarrow> Q"
by (auto simp: good_def)


definition almost_full_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "almost_full_on P A \<longleftrightarrow> (\<forall>f \<in> SEQ A. good P f)"

lemma almost_full_on_UNIV:
  "almost_full_on (\<lambda>_ _. True) UNIV"
by (auto simp: almost_full_on_def good_def)

lemma almost_full_onD:
  fixes f :: "nat \<Rightarrow> 'a" and A :: "'a set"
  assumes "almost_full_on P A" and "\<And>i. f i \<in> A"
  obtains i j where "i < j" and "P (f i) (f j)"
using assms unfolding almost_full_on_def by blast

lemma almost_full_onI [Pure.intro]:
  "(\<And>f. \<forall>i. f i \<in> A \<Longrightarrow> good P f) \<Longrightarrow> almost_full_on P A"
unfolding almost_full_on_def by blast

lemma almost_full_on_imp_reflp_on:
  assumes "almost_full_on P A"
  shows "reflp_on P A"
using assms by (auto simp: almost_full_on_def reflp_on_def)

lemma almost_full_on_subset:
  "A \<subseteq> B \<Longrightarrow> almost_full_on P B \<Longrightarrow> almost_full_on P A"
by (auto simp: almost_full_on_def)

lemma almost_full_on_mono:
  assumes "A \<subseteq> B" and "\<And>x y. Q x y \<Longrightarrow> P x y"
    and "almost_full_on Q B"
  shows "almost_full_on P A"
  using assms by (metis almost_full_on_def almost_full_on_subset good_def)

text \<open>
  Every sequence over elements of an almost-full set has a homogeneous subsequence.
\<close>
lemma almost_full_on_imp_homogeneous_subseq:
  assumes "almost_full_on P A"
    and "\<forall>i::nat. f i \<in> A"
  shows "\<exists>\<phi>::nat \<Rightarrow> nat. \<forall>i j. i < j \<longrightarrow> \<phi> i < \<phi> j \<and> P (f (\<phi> i)) (f (\<phi> j))"
proof -
  def X \<equiv> "{{i, j} | i j::nat. i < j \<and> P (f i) (f j)}"
  def Y \<equiv> "- X"
  def h \<equiv> "\<lambda>Z. if Z \<in> X then 0 else Suc 0"

  have [iff]: "\<And>x y. h {x, y} = 0 \<longleftrightarrow> {x, y} \<in> X" by (auto simp: h_def)
  have [iff]: "\<And>x y. h {x, y} = Suc 0 \<longleftrightarrow> {x, y} \<in> Y" by (auto simp: h_def Y_def)

  have "\<forall>x\<in>UNIV. \<forall>y\<in>UNIV. x \<noteq> y \<longrightarrow> h {x, y} < 2" by (simp add: h_def)
  from Ramsey2 [OF infinite_UNIV_nat this] obtain I c
    where "infinite I" and "c < 2"
    and *: "\<forall>x\<in>I. \<forall>y\<in>I. x \<noteq> y \<longrightarrow> h {x, y} = c" by blast
  then interpret infinitely_many1 "\<lambda>i. i \<in> I"
    by (unfold_locales) (simp add: infinite_nat_iff_unbounded)

  have "c = 0 \<or> c = 1" using \<open>c < 2\<close> by arith
  then show ?thesis
  proof
    assume [simp]: "c = 0"
    have "\<forall>i j. i < j \<longrightarrow> P (f (enum i)) (f (enum j))"
    proof (intro allI impI)
      fix i j :: nat
      assume "i < j"
      from * and enum_P and enum_less [OF \<open>i < j\<close>] have "{enum i, enum j} \<in> X" by auto
      with enum_less [OF \<open>i < j\<close>]
        show "P (f (enum i)) (f (enum j))" by (auto simp: X_def doubleton_eq_iff)
    qed
    then show ?thesis using enum_less by blast
  next
    assume [simp]: "c = 1"
    have "\<forall>i j. i < j \<longrightarrow> \<not> P (f (enum i)) (f (enum j))"
    proof (intro allI impI)
      fix i j :: nat
      assume "i < j"
      from * and enum_P and enum_less [OF \<open>i < j\<close>] have "{enum i, enum j} \<in> Y" by auto
      with enum_less [OF \<open>i < j\<close>]
        show "\<not> P (f (enum i)) (f (enum j))" by (auto simp: Y_def X_def doubleton_eq_iff)
    qed
    then have "\<not> good P (f \<circ> enum)" by auto
    moreover have "\<forall>i. f (enum i) \<in> A" using assms by auto
    ultimately show ?thesis using \<open>almost_full_on P A\<close> by (simp add: almost_full_on_def)
  qed
qed

text \<open>
  Almost full relations do not admit infinite antichains.
\<close>
lemma almost_full_on_imp_no_antichain_on:
  assumes "almost_full_on P A"
  shows "\<not> antichain_on P f A"
proof
  assume *: "antichain_on P f A"
  then have "\<forall>i. f i \<in> A" by simp
  with assms have "good P f" by (auto simp: almost_full_on_def)
  then obtain i j where "i < j" and "P (f i) (f j)"
    unfolding good_def by auto
  moreover with * have "incomparable P (f i) (f j)" by auto
  ultimately show False by blast
qed

text \<open>
  If the image of a function is almost-full then also its preimage is almost-full.
\<close>
lemma almost_full_on_map:
  assumes "almost_full_on Q B"
    and "h ` A \<subseteq> B"
  shows "almost_full_on (\<lambda>x y. Q (h x) (h y)) A" (is "almost_full_on ?P A")
proof
  fix f
  assume "\<forall>i::nat. f i \<in> A"
  then have "\<And>i. h (f i) \<in> B" using \<open>h ` A \<subseteq> B\<close> by auto
  with \<open>almost_full_on Q B\<close> [unfolded almost_full_on_def, THEN bspec, of "h \<circ> f"]
    show "good ?P f" unfolding good_def comp_def by blast
qed

text \<open>
  The homomorphic image of an almost-full set is almost-full.
\<close>
lemma almost_full_on_hom:
  fixes h :: "'a \<Rightarrow> 'b"
  assumes hom: "\<And>x y. \<lbrakk>x \<in> A; y \<in> A; P x y\<rbrakk> \<Longrightarrow> Q (h x) (h y)"
    and af: "almost_full_on P A"
  shows "almost_full_on Q (h ` A)"
proof
  fix f :: "nat \<Rightarrow> 'b"
  assume "\<forall>i. f i \<in> h ` A"
  then have "\<forall>i. \<exists>x. x \<in> A \<and> f i = h x" by (auto simp: image_def)
  from choice [OF this] obtain g
    where *: "\<forall>i. g i \<in> A \<and> f i = h (g i)" by blast
  show "good Q f"
  proof (rule ccontr)
    assume bad: "bad Q f"
    { fix i j :: nat
      assume "i < j"
      from bad have "\<not> Q (f i) (f j)" using \<open>i < j\<close> by (auto simp: good_def)
      with hom have "\<not> P (g i) (g j)" using * by auto }
    then have "bad P g" by (auto simp: good_def)
    with af and * show False by (auto simp: good_def almost_full_on_def)
  qed
qed

text \<open>
  The monomorphic preimage of an almost-full set is almost-full.
\<close>
lemma almost_full_on_mon:
  assumes mon: "\<And>x y. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> P x y = Q (h x) (h y)" "bij_betw h A B"
    and af: "almost_full_on Q B"
  shows "almost_full_on P A"
proof
  fix f :: "nat \<Rightarrow> 'a"
  assume *: "\<forall>i. f i \<in> A"
  then have **: "\<forall>i. (h \<circ> f) i \<in> B" using mon by (auto simp: bij_betw_def)
  show "good P f"
  proof (rule ccontr)
    assume bad: "bad P f"
    { fix i j :: nat
      assume "i < j"
      from bad have "\<not> P (f i) (f j)" using \<open>i < j\<close> by (auto simp: good_def)
      with mon have "\<not> Q (h (f i)) (h (f j))"
        using * by (auto simp: bij_betw_def inj_on_def) }
    then have "bad Q (h \<circ> f)" by (auto simp: good_def)
    with af and ** show False by (auto simp: good_def almost_full_on_def)
  qed
qed

text \<open>
  Every total and well-founded relation is almost-full.
\<close>
lemma total_on_and_wfp_on_imp_almost_full_on:
  assumes "total_on P A" and "wfp_on P A"
  shows "almost_full_on P\<^sup>=\<^sup>= A"
proof (rule ccontr)
  assume "\<not> almost_full_on P\<^sup>=\<^sup>= A"
  then obtain f :: "nat \<Rightarrow> 'a" where *: "\<And>i. f i \<in> A"
    and "\<forall>i j. i < j \<longrightarrow> \<not> P\<^sup>=\<^sup>= (f i) (f j)"
    unfolding almost_full_on_def by (auto dest: badE)
  with \<open>total_on P A\<close> have "\<forall>i j. i < j \<longrightarrow> P (f j) (f i)"
    unfolding total_on_def by blast
  then have "\<And>i. P (f (Suc i)) (f i)" by auto
  with \<open>wfp_on P A\<close> and * show False
    unfolding wfp_on_def by blast
qed

lemma Nil_imp_good_list_emb [simp]:
  assumes "f i = []"
  shows "good (list_emb P) f"
proof (rule ccontr)
  assume "bad (list_emb P) f"
  moreover have "(list_emb P) (f i) (f (Suc i))"
    unfolding assms by auto
  ultimately show False
    unfolding good_def by auto
qed

lemma ne_lists:
  assumes "xs \<noteq> []" and "xs \<in> lists A"
  shows "hd xs \<in> A" and "tl xs \<in> lists A"
  using assms by (case_tac [!] xs) simp_all

lemma list_emb_eq_length_induct [consumes 2, case_names Nil Cons]:
  assumes "length xs = length ys"
    and "list_emb P xs ys"
    and "Q [] []"
    and "\<And>x y xs ys. \<lbrakk>P x y; list_emb P xs ys; Q xs ys\<rbrakk> \<Longrightarrow> Q (x#xs) (y#ys)"
  shows "Q xs ys"
  using assms(2, 1, 3-) by (induct) (auto dest: list_emb_length)

lemma list_emb_eq_length_P:
  assumes "length xs = length ys"
    and "list_emb P xs ys"
  shows "\<forall>i<length xs. P (xs ! i) (ys ! i)"
using assms
proof (induct rule: list_emb_eq_length_induct)
  case (Cons x y xs ys)
  show ?case
  proof (intro allI impI)
    fix i assume "i < length (x # xs)"
    with Cons show "P ((x#xs)!i) ((y#ys)!i)"
      by (cases i) simp_all
  qed
qed simp


subsection \<open>Special Case: Finite Sets\<close>

text \<open>
  Every reflexive relation on a finite set is almost-full.
\<close>
lemma finite_almost_full_on:
  assumes finite: "finite A"
    and refl: "reflp_on P A"
  shows "almost_full_on P A"
proof
  fix f :: "nat \<Rightarrow> 'a"
  assume *: "\<forall>i. f i \<in> A"
  let ?I = "UNIV::nat set"
  have "f ` ?I \<subseteq> A" using * by auto
  with finite and finite_subset have 1: "finite (f ` ?I)" by blast
  have "infinite ?I" by auto
  from pigeonhole_infinite [OF this 1]
    obtain k where "infinite {j. f j = f k}" by auto
  then obtain l where "k < l" and "f l = f k"
    unfolding infinite_nat_iff_unbounded by auto
  then have "P (f k) (f l)" using refl and * by (auto simp: reflp_on_def)
  with \<open>k < l\<close> show "good P f" by (auto simp: good_def)
qed

lemma eq_almost_full_on_finite_set:
  assumes "finite A"
  shows "almost_full_on (op =) A"
  using finite_almost_full_on [OF assms, of "op ="]
  by (auto simp: reflp_on_def)


subsection \<open>Further Results\<close>

lemma af_trans_imp_wf:
  assumes af: "almost_full_on P A"
    and trans: "transp_on P A"
  shows "wfp_on (strict P) A"
proof -
  show "wfp_on (strict P) A"
  proof (unfold wfp_on_def, rule notI)
    assume "\<exists>f. \<forall>i. f i \<in> A \<and> strict P (f (Suc i)) (f i)"
    then obtain f where *: "\<forall>i. f i \<in> A \<and> ((strict P)\<inverse>\<inverse>) (f i) (f (Suc i))" by blast
    from chain_transp_on_less [OF this]
      and transp_on_strict [THEN transp_on_converse, OF trans]
      have "\<forall>i j. i < j \<longrightarrow> \<not> P (f i) (f j)" by blast
    with af show False
      using * by (auto simp: almost_full_on_def good_def)
  qed
qed

lemma wf_and_no_antichain_imp_qo_extension_wf:
  assumes wf: "wfp_on (strict P) A"
    and anti: "\<not> (\<exists>f. antichain_on P f A)"
    and subrel: "\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> Q x y"
    and qo: "qo_on Q A"
  shows "wfp_on (strict Q) A"
proof (rule ccontr)
  have "transp_on (strict Q) A"
    using qo unfolding qo_on_def transp_on_def by blast
  then have *: "transp_on ((strict Q)\<inverse>\<inverse>) A" by (rule transp_on_converse)
  assume "\<not> wfp_on (strict Q) A"
  then obtain f :: "nat \<Rightarrow> 'a" where A: "\<And>i. f i \<in> A"
    and "\<forall>i. strict Q (f (Suc i)) (f i)" unfolding wfp_on_def by blast+
  then have "\<forall>i. f i \<in> A \<and> ((strict Q)\<inverse>\<inverse>) (f i) (f (Suc i))" by auto
  from chain_transp_on_less [OF this *]
    have *: "\<And>i j. i < j \<Longrightarrow> \<not> P (f i) (f j)"
    using subrel and A by blast
  show False
  proof (cases)
    assume "\<exists>k. \<forall>i>k. \<exists>j>i. P (f j) (f i)"
    then obtain k where "\<forall>i>k. \<exists>j>i. P (f j) (f i)" by auto
    from subchain [of k _ f, OF this] obtain g
      where "\<And>i j. i < j \<Longrightarrow> g i < g j"
      and "\<And>i. P (f (g (Suc i))) (f (g i))" by auto
    with * have "\<And>i. strict P (f (g (Suc i))) (f (g i))" by blast
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
      using \<open>\<forall>k. h k > k\<close> by (induct_tac i) auto
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

lemma every_qo_extension_wf_imp_af:
  assumes ext: "\<forall>Q. (\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> Q x y) \<and>
    qo_on Q A \<longrightarrow> wfp_on (strict Q) A"
    and "qo_on P A"
  shows "almost_full_on P A"
proof
  from \<open>qo_on P A\<close>
    have refl: "reflp_on P A"
    and trans: "transp_on P A"
    by (auto intro: qo_on_imp_reflp_on qo_on_imp_transp_on)

  fix f :: "nat \<Rightarrow> 'a"
  assume "\<forall>i. f i \<in> A"
  then have A: "\<And>i. f i \<in> A" ..
  show "good P f"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have bad: "\<forall>i j. i < j \<longrightarrow> \<not> P (f i) (f j)" by (auto simp: good_def)
    then have *: "\<And>i j. P (f i) (f j) \<Longrightarrow> i \<ge> j" by (metis not_le_imp_less)
  
    def [simp]: D \<equiv> "\<lambda>x y. \<exists>i. x = f (Suc i) \<and> y = f i"
    def P' \<equiv> "restrict_to P A"
    def [simp]: Q \<equiv> "(sup P' D)\<^sup>*\<^sup>*"

    have **: "\<And>i j. (D OO P'\<^sup>*\<^sup>*)\<^sup>+\<^sup>+ (f i) (f j) \<Longrightarrow> i > j"
    proof -
      fix i j
      assume "(D OO P'\<^sup>*\<^sup>*)\<^sup>+\<^sup>+ (f i) (f j)"
      then show "i > j"
        apply (induct "f i" "f j" arbitrary: j)
        apply (insert A, auto dest!: * simp: P'_def reflp_on_restrict_to_rtranclp [OF refl trans])
        apply (metis "*" dual_order.strict_trans1 less_Suc_eq_le refl reflp_on_def)
        by (metis le_imp_less_Suc less_trans)
    qed

    have "\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> Q x y" by (auto simp: P'_def)
    moreover have "qo_on Q A" by (auto simp: qo_on_def reflp_on_def transp_on_def)
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
          by (metis (lifting, mono_tags) less_le relcompp.relcompI tranclp_into_tranclp2)
        then show False by auto
      qed
      with A [of i] show "f i \<in> A \<and> strict Q (f (Suc i)) (f i)" by auto
    qed
    ultimately show False unfolding wfp_on_def by blast  
  qed
qed

end
