(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c.sternagel@gmail.com>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

section {* Almost-Full Relations *}

theory Almost_Full_Relations
imports
  "~~/src/HOL/Library/Sublist"
  "~~/src/HOL/Library/Ramsey"
  "../Regular-Sets/Regexp_Method"
  "../Abstract-Rewriting/Seq"
  Least_Enum
  Minimal_Bad_Sequences
begin

subsection {* Basic Definitions and Facts *}

definition almost_full_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "almost_full_on P A \<longleftrightarrow> (\<forall>f \<in> SEQ A. good P f)"

lemma almost_full_on_UNIV:
  "almost_full_on (\<lambda>_ _. True) UNIV"
  by (auto simp: almost_full_on_def good_def)

lemma (in mbs) mbs':
  assumes "\<not> almost_full_on P A"
  shows "\<exists>m \<in> BAD P. \<forall>g. (m, g) \<in> gseq \<longrightarrow> good P g"
  using assms and mbs
  unfolding almost_full_on_def by blast

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

text {*
  Every sequence over elements of an almost-full set has a homogeneous subsequence.
*}
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

  have "c = 0 \<or> c = 1" using `c < 2` by arith
  then show ?thesis
  proof
    assume [simp]: "c = 0"
    have "\<forall>i j. i < j \<longrightarrow> P (f (enum i)) (f (enum j))"
    proof (intro allI impI)
      fix i j :: nat
      assume "i < j"
      from * and enum_P and enum_less [OF `i < j`] have "{enum i, enum j} \<in> X" by auto
      with enum_less [OF `i < j`]
        show "P (f (enum i)) (f (enum j))" by (auto simp: X_def doubleton_eq_iff)
    qed
    then show ?thesis using enum_less by blast
  next
    assume [simp]: "c = 1"
    have "\<forall>i j. i < j \<longrightarrow> \<not> P (f (enum i)) (f (enum j))"
    proof (intro allI impI)
      fix i j :: nat
      assume "i < j"
      from * and enum_P and enum_less [OF `i < j`] have "{enum i, enum j} \<in> Y" by auto
      with enum_less [OF `i < j`]
        show "\<not> P (f (enum i)) (f (enum j))" by (auto simp: Y_def X_def doubleton_eq_iff)
    qed
    then have "\<not> good P (f \<circ> enum)" by auto
    moreover have "\<forall>i. f (enum i) \<in> A" using assms by auto
    ultimately show ?thesis using `almost_full_on P A` by (simp add: almost_full_on_def)
  qed
qed

text {*
  Almost full relations do not admit infinite antichains.
*}
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

text {*
  If the image of a function is almost-full then also its preimage is almost-full.
*}
lemma almost_full_on_map:
  assumes "almost_full_on Q B"
    and "h ` A \<subseteq> B"
  shows "almost_full_on (\<lambda>x y. Q (h x) (h y)) A" (is "almost_full_on ?P A")
proof
  fix f
  assume "\<forall>i::nat. f i \<in> A"
  then have "\<And>i. h (f i) \<in> B" using \<open>h ` A \<subseteq> B\<close> by auto
  with `almost_full_on Q B` [unfolded almost_full_on_def, THEN bspec, of "h \<circ> f"]
    show "good ?P f" unfolding good_def comp_def by blast
qed

text {*
  The homomorphic image of an almost-full set is almost-full.
*}
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
      from bad have "\<not> Q (f i) (f j)" using `i < j` by (auto simp: good_def)
      with hom have "\<not> P (g i) (g j)" using * by auto }
    then have "bad P g" by (auto simp: good_def)
    with af and * show False by (auto simp: good_def almost_full_on_def)
  qed
qed

text {*
  The monomorphic preimage of an almost-full set is almost-full.
*}
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
      from bad have "\<not> P (f i) (f j)" using `i < j` by (auto simp: good_def)
      with mon have "\<not> Q (h (f i)) (h (f j))"
        using * by (auto simp: bij_betw_def inj_on_def) }
    then have "bad Q (h \<circ> f)" by (auto simp: good_def)
    with af and ** show False by (auto simp: good_def almost_full_on_def)
  qed
qed

text {*
  Every total and well-founded relation is almost-full.
*}
lemma total_on_and_wfp_on_imp_almost_full_on:
  assumes "total_on P A" and "wfp_on P A"
  shows "almost_full_on P\<^sup>=\<^sup>= A"
proof (rule ccontr)
  assume "\<not> almost_full_on P\<^sup>=\<^sup>= A"
  then obtain f :: "nat \<Rightarrow> 'a" where *: "\<And>i. f i \<in> A"
    and "\<forall>i j. i < j \<longrightarrow> \<not> P\<^sup>=\<^sup>= (f i) (f j)"
    unfolding almost_full_on_def by (auto dest: badE)
  with `total_on P A` have "\<forall>i j. i < j \<longrightarrow> P (f j) (f i)"
    unfolding total_on_def by blast
  then have "\<And>i. P (f (Suc i)) (f i)" by auto
  with `wfp_on P A` and * show False
    unfolding wfp_on_def by blast
qed


(*TODO: move to Option.thy of Isabelle/HOL?*)
subsection {* Adding a Bottom Element to a Set *}

definition with_bot :: "'a set \<Rightarrow> 'a option set" ("_\<^sub>\<bottom>" [1000] 1000)
where
  "A\<^sub>\<bottom> = {None} \<union> Some ` A"

lemma with_bot_iff [iff]:
  "Some x \<in> A\<^sub>\<bottom> \<longleftrightarrow> x \<in> A"
  by (auto simp: with_bot_def)

lemma NoneI [simp, intro]:
  "None \<in> A\<^sub>\<bottom>"
  by (simp add: with_bot_def)

lemma not_None_the_mem [simp]:
  "x \<noteq> None \<Longrightarrow> the x \<in> A \<longleftrightarrow> x \<in> A\<^sub>\<bottom>"
  by auto

lemma with_bot_cases:
  "u \<in> A\<^sub>\<bottom> \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> u = Some x \<Longrightarrow> P) \<Longrightarrow> (u = None \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma with_bot_empty_conv [iff]:
  "A\<^sub>\<bottom> = {None} \<longleftrightarrow> A = {}"
  by (auto elim: with_bot_cases)

lemma with_bot_UNIV [simp]:
  "UNIV\<^sub>\<bottom> = UNIV"
proof (rule set_eqI)
  fix x :: "'a option"
  show "x \<in> UNIV\<^sub>\<bottom> \<longleftrightarrow> x \<in> UNIV" by (cases x) auto
qed


subsection {* Adding a Bottom Element to an Almost-Full Set *}

fun
  option_le :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> bool"
where
  "option_le P None y = True" |
  "option_le P (Some x) None = False" |
  "option_le P (Some x) (Some y) = P x y"

lemma None_imp_good_option_le [simp]:
  assumes "f i = None"
  shows "good (option_le P) f"
  by (rule goodI [of i "Suc i"]) (auto simp: assms)

lemma almost_full_on_with_bot:
  assumes "almost_full_on P A"
  shows "almost_full_on (option_le P) A\<^sub>\<bottom>" (is "almost_full_on ?P ?A")
proof
  fix f :: "nat \<Rightarrow> 'a option"
  assume *: "\<forall>i. f i \<in> ?A"
  show "good ?P f"
  proof (cases "\<forall>i. f i \<noteq> None")
    case True
    then have **: "\<And>i. Some (the (f i)) = f i"
      and "\<And>i. the (f i) \<in> A" using * by auto
    with almost_full_onD [OF assms, of "the \<circ> f"] obtain i j where "i < j"
      and "P (the (f i)) (the (f j))" by auto
    then have "?P (Some (the (f i))) (Some (the (f j)))" by simp
    then have "?P (f i) (f j)" unfolding ** .
    with `i < j` show "good ?P f" by (auto simp: good_def)
  qed auto
qed


subsection {* Disjoint Union of Almost-Full Sets *}

fun
  sum_le :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool"
where
  "sum_le P Q (Inl x) (Inl y) = P x y" |
  "sum_le P Q (Inr x) (Inr y) = Q x y" |
  "sum_le P Q x y = False"

lemma not_sum_le_cases:
  assumes "\<not> sum_le P Q a b"
    and "\<And>x y. \<lbrakk>a = Inl x; b = Inl y; \<not> P x y\<rbrakk> \<Longrightarrow> thesis"
    and "\<And>x y. \<lbrakk>a = Inr x; b = Inr y; \<not> Q x y\<rbrakk> \<Longrightarrow> thesis"
    and "\<And>x y. \<lbrakk>a = Inl x; b = Inr y\<rbrakk> \<Longrightarrow> thesis"
    and "\<And>x y. \<lbrakk>a = Inr x; b = Inl y\<rbrakk> \<Longrightarrow> thesis"
  shows thesis
  using assms by (cases a b rule: sum.exhaust [case_product sum.exhaust]) auto

text {*
  When two sets are almost-full, then their disjoint sum is almost-full.
*}
lemma almost_full_on_Plus:
  assumes "almost_full_on P A" and "almost_full_on Q B"
  shows "almost_full_on (sum_le P Q) (A <+> B)" (is "almost_full_on ?P ?A")
proof
  fix f :: "nat \<Rightarrow> ('a + 'b)"
  let ?I = "f -` Inl ` A"
  let ?J = "f -` Inr ` B"
  assume "\<forall>i. f i \<in> ?A"
  then have *: "?J = (UNIV::nat set) - ?I" by (fastforce)
  show "good ?P f"
  proof (rule ccontr)
    assume bad: "bad ?P f"
    show False
    proof (cases "finite ?I")
      assume "finite ?I"
      then have "infinite ?J" by (auto simp: *)
      then interpret infinitely_many1 "\<lambda>i. f i \<in> Inr ` B"
        by (unfold_locales) (simp add: infinite_nat_iff_unbounded)
      have [dest]: "\<And>i x. f (enum i) = Inl x \<Longrightarrow> False"
        using enum_P by (auto simp: image_iff) (metis Inr_Inl_False)
      let ?f = "\<lambda>i. projr (f (enum i))"
      have B: "\<And>i. ?f i \<in> B" using enum_P by (auto simp: image_iff) (metis sum.sel(2))
      { fix i j :: nat
        assume "i < j"
        then have "enum i < enum j" using enum_less by auto
        with bad have "\<not> ?P (f (enum i)) (f (enum j))" by (auto simp: good_def)
        then have "\<not> Q (?f i) (?f j)" by (auto elim: not_sum_le_cases) }
      then have "bad Q ?f" by (auto simp: good_def)
      moreover from `almost_full_on Q B` and B
        have "good Q ?f" by (auto simp: good_def almost_full_on_def)
      ultimately show False by blast
    next
      assume "infinite ?I"
      then interpret infinitely_many1 "\<lambda>i. f i \<in> Inl ` A"
        by (unfold_locales) (simp add: infinite_nat_iff_unbounded)
      have [dest]: "\<And>i x. f (enum i) = Inr x \<Longrightarrow> False"
        using enum_P by (auto simp: image_iff) (metis Inr_Inl_False)
      let ?f = "\<lambda>i. projl (f (enum i))"
      have A: "\<forall>i. ?f i \<in> A" using enum_P by (auto simp: image_iff) (metis sum.sel(1))
      { fix i j :: nat
        assume "i < j"
        then have "enum i < enum j" using enum_less by auto
        with bad have "\<not> ?P (f (enum i)) (f (enum j))" by (auto simp: good_def)
        then have "\<not> P (?f i) (?f j)" by (auto elim: not_sum_le_cases) }
      then have "bad P ?f" by (auto simp: good_def)
      moreover from `almost_full_on P A` and A
        have "good P ?f" by (auto simp: good_def almost_full_on_def)
      ultimately show False by blast
    qed
  qed
qed


subsection {* Dickson's Lemma for Almost-Full Relations *}

text {*
  When two sets are almost-full, then their Cartesian product is almost-full.
*}

definition
  prod_le :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
where
  "prod_le P1 P2 = (\<lambda>(p1, p2) (q1, q2). P1 p1 q1 \<and> P2 p2 q2)"

lemma prod_le_True [simp]:
  "prod_le P (\<lambda>_ _. True) a b = P (fst a) (fst b)"
  by (auto simp: prod_le_def)

lemma almost_full_on_Sigma:
  assumes "almost_full_on P1 A1" and "almost_full_on P2 A2"
  shows "almost_full_on (prod_le P1 P2) (A1 \<times> A2)" (is "almost_full_on ?P ?A")
proof (rule ccontr)
  assume "\<not> almost_full_on ?P ?A"
  then obtain f where f: "\<forall>i. f i \<in> ?A"
    and bad: "bad ?P f" by (auto simp: almost_full_on_def)
  let ?W = "\<lambda>x y. P1 (fst x) (fst y)"
  let ?B = "\<lambda>x y. P2 (snd x) (snd y)"
  from f have fst: "\<forall>i. fst (f i) \<in> A1" and snd: "\<forall>i. snd (f i) \<in> A2"
    by (metis SigmaE fst_conv, metis SigmaE snd_conv)
  from almost_full_on_imp_homogeneous_subseq [OF assms(1) fst]
    obtain \<phi> :: "nat \<Rightarrow> nat" where mono: "\<And>i j. i < j \<Longrightarrow> \<phi> i < \<phi> j"
    and *: "\<And>i j. i < j \<Longrightarrow> ?W (f (\<phi> i)) (f (\<phi> j))" by auto
  from snd have "\<forall>i. snd (f (\<phi> i)) \<in> A2" by auto
  then have "snd \<circ> f \<circ> \<phi> \<in> SEQ A2" by auto
  with assms(2) have "good P2 (snd \<circ> f \<circ> \<phi>)" by (auto simp: almost_full_on_def)
  then obtain i j :: nat
    where "i < j" and "?B (f (\<phi> i)) (f (\<phi> j))" by auto
  with * [OF `i < j`] have "?P (f (\<phi> i)) (f (\<phi> j))" by (simp add: case_prod_beta prod_le_def)
  with mono [OF `i < j`] and bad show False by auto
qed


subsection {* Higman's Lemma for Almost-Full Relations *}

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

lemma almost_full_on_lists:
  assumes "almost_full_on P A"
  shows "almost_full_on (list_emb P) (lists A)" (is "almost_full_on ?P ?A")
proof (rule ccontr)
  interpret mbs ?A .
  assume "\<not> ?thesis"
  from mbs' [OF this] obtain m
    where bad: "m \<in> BAD ?P"
    and min: "\<forall>g. (m, g) \<in> gseq \<longrightarrow> good ?P g" ..
  then have lists: "\<And>i. m i \<in> lists A"
    and ne: "\<And>i. m i \<noteq> []" by auto

  def h \<equiv> "\<lambda>i. hd (m i)"
  def t \<equiv> "\<lambda>i. tl (m i)"

  have m: "\<And>i. m i = h i # t i" using ne by (simp add: h_def t_def)
  
  have "\<forall>i. h i \<in> A" using ne_lists [OF ne] and lists by (auto simp add: h_def)
  from almost_full_on_imp_homogeneous_subseq [OF assms this] obtain \<phi> :: "nat \<Rightarrow> nat"
    where less: "\<And>i j. i < j \<Longrightarrow> \<phi> i < \<phi> j"
      and P: "\<forall>i j. i < j \<longrightarrow> P (h (\<phi> i)) (h (\<phi> j))" by blast

  have bad_t: "bad ?P (t \<circ> \<phi>)"
  proof
    assume "good ?P (t \<circ> \<phi>)"
    then obtain i j where "i < j" and "?P (t (\<phi> i)) (t (\<phi> j))" by auto
    moreover with P have "P (h (\<phi> i)) (h (\<phi> j))" by blast
    ultimately have "?P (m (\<phi> i)) (m (\<phi> j))"
      by (subst (1 2) m) (rule list_emb_Cons2, auto)
    with less and `i < j` have "good ?P m" by (auto simp: good_def)
    with bad show False by blast
  qed
  
  def m' \<equiv> "\<lambda>i. if i < \<phi> 0 then m i else t (\<phi> (i - \<phi> 0))"

  have m'_less: "\<And>i. i < \<phi> 0 \<Longrightarrow> m' i = m i" by (simp add: m'_def)
  have m'_geq: "\<And>i. i \<ge> \<phi> 0 \<Longrightarrow> m' i = t (\<phi> (i - \<phi> 0))" by (simp add: m'_def)

  have "\<forall>i. m' i \<in> lists A" using ne_lists [OF ne] and lists by (auto simp: m'_def t_def)
  moreover have "length (m' (\<phi> 0)) < length (m (\<phi> 0))" using ne by (simp add: t_def m'_geq)
  moreover have "\<forall>j<\<phi> 0. m' j = m j" by (auto simp: m'_less)
  ultimately have "(m, m') \<in> gseq" using lists by (auto simp: gseq_def)
  moreover have "bad ?P m'"
  proof
    assume "good ?P m'"
    then obtain i j where "i < j" and emb: "?P (m' i) (m' j)" by (auto simp: good_def)
    { assume "j < \<phi> 0"
      with `i < j` and emb have "?P (m i) (m j)" by (auto simp: m'_less)
      with `i < j` and bad have False by blast }
    moreover
    { assume "\<phi> 0 \<le> i"
      with `i < j` and emb have "?P (t (\<phi> (i - \<phi> 0))) (t (\<phi> (j - \<phi> 0)))"
        and "i - \<phi> 0 < j - \<phi> 0" by (auto simp: m'_geq)
      with bad_t have False by auto }
    moreover
    { assume "i < \<phi> 0" and "\<phi> 0 \<le> j"
      with `i < j` and emb have "?P (m i) (t (\<phi> (j - \<phi> 0)))" by (simp add: m'_less m'_geq)
      from list_emb_Cons [OF this, of "h (\<phi> (j - \<phi> 0))"]
        have "?P (m i) (m (\<phi> (j - \<phi> 0)))" using ne by (simp add: h_def t_def)
      moreover have "i < \<phi> (j - \<phi> 0)"
        using less [of 0 "j - \<phi> 0"] and `i < \<phi> 0` and `\<phi> 0 \<le> j`
        by (cases "j = \<phi> 0") auto
      ultimately have False using bad by blast }
    ultimately show False using `i < j` by arith
  qed
  ultimately show False using min by blast
qed

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


subsection {* Special Case: Finite Sets *}

text {*
  Every reflexive relation on a finite set is almost-full.
*}
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
  with `k < l` show "good P f" by (auto simp: good_def)
qed

lemma eq_almost_full_on_finite_set:
  assumes "finite A"
  shows "almost_full_on (op =) A"
  using finite_almost_full_on [OF assms, of "op ="]
  by (auto simp: reflp_on_def)


subsection {* Natural Numbers *}

lemma almost_full_on_UNIV_nat:
  "almost_full_on (op \<le>) (UNIV :: nat set)"
proof -
  let ?P = "sublisteq :: bool list \<Rightarrow> bool list \<Rightarrow> bool"
  have *: "length ` (UNIV :: bool list set) = (UNIV :: nat set)"
    by (metis Ex_list_of_length surj_def)
  have "almost_full_on (op \<le>) (length ` (UNIV :: bool list set))"
  proof (rule almost_full_on_hom)
    fix xs ys :: "bool list"
    assume "?P xs ys"
    then show "length xs \<le> length ys"
      by (metis list_emb_length)
  next
    have "finite (UNIV :: bool set)" by auto
    from almost_full_on_lists [OF eq_almost_full_on_finite_set [OF this]]
      show "almost_full_on ?P UNIV" unfolding lists_UNIV .
  qed
  then show ?thesis unfolding * .
qed


subsection {* Further Results *}

lemma af_trans_imp_wf:
  assumes af: "almost_full_on P A"
    and trans: "transp_on P A"
  shows "wfp_on (strict P) A"
proof -
  show "wfp_on (strict P) A"
  proof (unfold wfp_on_def, rule notI)
    assume "\<exists>f. \<forall>i. f i \<in> A \<and> strict P (f (Suc i)) (f i)"
    then obtain f where *: "chain_on ((strict P)\<inverse>\<inverse>) f A" by blast
    from chain_on_transp_on_less [OF this]
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

lemma every_qo_extension_wf_imp_af:
  assumes ext: "\<forall>Q. (\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> Q x y) \<and>
    qo_on Q A \<longrightarrow> wfp_on (strict Q) A"
    and "qo_on P A"
  shows "almost_full_on P A"
proof
  from `qo_on P A`
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

