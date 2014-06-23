(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c.sternagel@gmail.com>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Almost-Full Relations *}

theory Almost_Full_Relations
imports
  Least_Enum
  "~~/src/HOL/Library/Sublist"
  "~~/src/HOL/Library/Ramsey"
  Minimal_Bad_Sequences
  "../Regular-Sets/Regexp_Method"
begin

subsection {* Basic Definitions and Facts *}

definition almost_full_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "almost_full_on P A \<longleftrightarrow> (\<forall>f \<in> SEQ A. good P f)"

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
proof
  fix x
  assume "x \<in> A"
  let ?f = "\<lambda>i. x"
  have "\<forall>i. ?f i \<in> A" using `x \<in> A` by simp
  with assms obtain i j :: nat where "i < j"
    and "P (?f i) (?f j)" by (auto simp: Ball_def almost_full_on_def good_def)
  then show "P x x" by simp
qed

lemma almost_full_on_subset:
  "A \<subseteq> B \<Longrightarrow> almost_full_on P B \<Longrightarrow> almost_full_on P A"
  by (auto simp: almost_full_on_def)

text {*Every sequence over elements of an almost-full set has a homogeneous subsequence.*}
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
  from Ramsey2 [OF infinite_UNIV_nat this] obtain B t
    where "infinite B" and "t < 2"
    and *: "\<forall>x\<in>B. \<forall>y\<in>B. x \<noteq> y \<longrightarrow> h {x, y} = t" by blast
  then interpret infinitely_many1 "\<lambda>i. i \<in> B"
    by (unfold_locales) (simp add: infinite_nat_iff_unbounded)

  have "t = 0 \<or> t = 1" using `t < 2` by arith
  then show ?thesis
  proof
    assume [simp]: "t = 0"
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
    assume [simp]: "t = 1"
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

text {*Almost full relations do not admit infinite antichains.*}
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

text {*If the image of a function is almost-full then also its
preimage is almost-full.*}
lemma almost_full_on_map:
  assumes "almost_full_on Q B"
    and subset: "h ` A \<subseteq> B"
  shows "almost_full_on (\<lambda>x y. Q (h x) (h y)) A"
    (is "almost_full_on ?P A")
proof
  fix f
  presume *: "\<And>i::nat. f i \<in> A"
  let ?f = "\<lambda>i. h (f i)"
  from * and subset have "\<And>i. h (f i) \<in> B" by auto
  with `almost_full_on Q B` [unfolded almost_full_on_def, THEN bspec, of ?f]
    show "good ?P f" unfolding good_def by blast
qed simp

text {*The homomorphic image of an almost full set is almost full.*}
lemma almost_full_on_hom:
  fixes h :: "'a \<Rightarrow> 'b"
  assumes hom: "\<And>x y. \<lbrakk>x \<in> A; y \<in> A; P x y\<rbrakk> \<Longrightarrow> Q (h x) (h y)"
    and af: "almost_full_on P A"
  shows "almost_full_on Q (h ` A)"
proof
  fix f :: "'b seq"
  assume "\<forall>i. f i \<in> h ` A"
  then have "\<forall>i. \<exists>x. x \<in> A \<and> f i = h x" by (auto simp: image_def)
  from choice [OF this] obtain g
    where *: "\<forall>i. g i \<in> A \<and> f i = h (g i)" by blast
  show "good Q f"
  proof (rule ccontr)
    assume bad: "bad Q f"
    {
      fix i j :: nat
      assume "i < j"
      from bad have "\<not> Q (f i) (f j)" using `i < j` by (auto simp: good_def)
      with hom have "\<not> P (g i) (g j)" using * by auto
    }
    then have "bad P g" by (auto simp: good_def)
    with af and * show False by (auto simp: good_def almost_full_on_def)
  qed
qed

text {*The monomorphic preimage of an almost full set is almost full.*}
lemma almost_full_on_mon:
  assumes mon: "\<And>x y. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> P x y = Q (h x) (h y)" "bij_betw h A B"
    and af: "almost_full_on Q B"
  shows "almost_full_on P A"
proof
  fix f :: "'a seq"
  assume *: "\<forall>i. f i \<in> A"
  then have **: "\<forall>i. (h \<circ> f) i \<in> B" using mon by (auto simp: bij_betw_def)
  show "good P f"
  proof (rule ccontr)
    assume bad: "bad P f"
    {
      fix i j :: nat
      assume "i < j"
      from bad have "\<not> P (f i) (f j)" using `i < j` by (auto simp: good_def)
      with mon have "\<not> Q (h (f i)) (h (f j))"
        using * by (auto simp: bij_betw_def inj_on_def)
    }
    then have "bad Q (h \<circ> f)" by (auto simp: good_def)
    with af and ** show False by (auto simp: good_def almost_full_on_def)
  qed
qed

text {*Every total and well-founded relation is almost-full.*}
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

definition with_bot :: "'a set \<Rightarrow> 'a option set" ("_\<^sub>\<bottom>" [1000] 1000) where
  "A\<^sub>\<bottom> \<equiv> {None} \<union> Some ` A"

lemma SomeI [intro!]:
  "x \<in> A \<Longrightarrow> Some x \<in> A\<^sub>\<bottom>"
  by (simp add: with_bot_def)

lemma NoneI [intro!]:
  "None \<in> A\<^sub>\<bottom>"
  by (simp add: with_bot_def)

lemma with_botE [elim!]:
  "u \<in> A\<^sub>\<bottom> \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> u = Some x \<Longrightarrow> P) \<Longrightarrow> (u = None \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: with_bot_def)

lemma with_bot_empty_conv [simp]:
  "A\<^sub>\<bottom> = {None} \<longleftrightarrow> A = {}"
  by auto

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

fun
  option_less :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> bool"
where
  "option_less P None None = False" |
  "option_less P None (Some y) = True" |
  "option_less P (Some x) None = False" |
  "option_less P (Some x) (Some y) = P x y"

lemma reflclp_option_less [simp]:
  "(option_less P)\<^sup>=\<^sup>= = option_le (P\<^sup>=\<^sup>=)"
proof (intro ext)
  fix x y
  show "(option_less P)\<^sup>=\<^sup>= x y = option_le (P\<^sup>=\<^sup>=) x y"
  by (cases x, auto) (cases y, auto)+
qed

lemma reflclp_option_le [simp]:
  "(option_le P)\<^sup>=\<^sup>= = option_le (P\<^sup>=\<^sup>=)"
proof (intro ext)
  fix x y
  show "(option_le P)\<^sup>=\<^sup>= x y = option_le (P\<^sup>=\<^sup>=) x y"
  by (cases x, auto) (cases y, auto)+
qed

lemma almost_full_on_with_bot:
  assumes "almost_full_on P A"
  shows "almost_full_on (option_le P) A\<^sub>\<bottom>"
    (is "almost_full_on ?P ?A")
proof
  fix f :: "'a option seq"
  assume *: "\<forall>i. f i \<in> A\<^sub>\<bottom>"
  show "good ?P f"
  proof (rule ccontr)
    assume "bad ?P f"
    then have **: "\<And>i j. i < j \<Longrightarrow> \<not> ?P (f i) (f j)" by (auto simp: good_def)
    let ?f = "\<lambda>i. Option.the (f i)"
    have "\<forall>i j. i < j \<longrightarrow> \<not> P (?f i) (?f j)"
    proof (intro allI impI)
      fix i j :: nat
      assume "i < j"
      from ** [of i] and ** [of j] obtain x y where
        "f i = Some x" and "f j = Some y" by force
      with ** [OF `i < j`] show "\<not> P (?f i) (?f j)" by simp
    qed
    then have "bad P ?f" by (auto simp: good_def)
    moreover have "\<forall>i. ?f i \<in> A"
    proof
      fix i :: nat
      from ** [of i] obtain x where "f i = Some x" by force
      with * [THEN spec, of i] show "?f i \<in> A" by auto
    qed
    ultimately show False using assms by (auto simp: almost_full_on_def)
  qed
qed

lemma almost_full_on_reflclp_option_less:
  assumes "almost_full_on (P\<^sup>=\<^sup>=) A"
  shows "almost_full_on ((option_less P)\<^sup>=\<^sup>=) A\<^sub>\<bottom>"
  using almost_full_on_with_bot [OF assms] by simp


subsection {* Disjoint Union of Almost-Full Sets *}

fun
  sum_le :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool"
where
  "sum_le P Q (Inl x) (Inl y) = P x y" |
  "sum_le P Q (Inr x) (Inr y) = Q x y" |
  "sum_le P Q x y = False"

fun
  sum_less :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool"
where
  "sum_less P Q (Inl x) (Inl y) = P x y" |
  "sum_less P Q (Inr x) (Inr y) = Q x y" |
  "sum_less P Q x y = False"

text {*Note that all proofs below involving @{const sum_le} and @{const sum_less} work as they are,
when in the last clause of each function definition @{const True} is used instead of @{const False}.
I'm not sure which variant is preferable.*}

lemma reflclp_sum_less [simp]:
  "(sum_less P Q)\<^sup>=\<^sup>= = sum_le (P\<^sup>=\<^sup>=) (Q\<^sup>=\<^sup>=)"
proof (intro ext)
  fix x y
  show "(sum_less P Q)\<^sup>=\<^sup>= x y = sum_le (P\<^sup>=\<^sup>=) (Q\<^sup>=\<^sup>=) x y"
  by (cases x, auto) (cases y, auto)+
qed

lemma reflclp_sum_le [simp]:
  "(sum_le P Q)\<^sup>=\<^sup>= = sum_le (P\<^sup>=\<^sup>=) (Q\<^sup>=\<^sup>=)"
proof (intro ext)
  fix x y
  show "(sum_le P Q)\<^sup>=\<^sup>= x y = sum_le (P\<^sup>=\<^sup>=) (Q\<^sup>=\<^sup>=) x y"
  by (cases x, auto) (cases y, auto)+
qed

text {*When two sets are almost full, then their disjoint sum is almost full.*}
lemma almost_full_on_Plus:
  assumes "almost_full_on P A" and "almost_full_on Q B"
  shows "almost_full_on (sum_le P Q) (A <+> B)"
    (is "almost_full_on ?P ?A")
proof
  fix f :: "('a + 'b) seq"
  assume *: "\<forall>i. f i \<in> ?A"
  let ?I = "{i. f i \<in> Inl ` A}"
  let ?J = "{i. f i \<in> Inr ` B}"
  have **: "(UNIV::nat set) - ?I = ?J" using * by auto
  show "good ?P f"
  proof (rule ccontr)
    assume bad: "bad ?P f"
    show False
    proof (cases "finite ?I")
      assume "finite ?I"
      moreover have "infinite (UNIV::nat set)" by auto
      ultimately have "infinite ?J" unfolding ** [symmetric] by (rule Diff_infinite_finite)
      then have "\<forall>i. \<exists>j>i. j \<in> ?J" by (simp add: infinite_nat_iff_unbounded)
      then interpret infinitely_many1 "\<lambda>i. i \<in> ?J" by (unfold_locales) assumption
      let ?f = "\<lambda>i. projr (f (enum i))"
      have ***: "\<forall>i. \<exists>x\<in>B. f (enum i) = Inr x" using enum_P by auto
      have B: "\<forall>i. ?f i \<in> B"
      proof
        fix i
        from *** obtain x where "x \<in> B" and "f (enum i) = Inr x" by blast
        then show "?f i \<in> B" by simp
      qed
      {
        fix i j :: nat
        assume "i < j"
        then have "enum i < enum j" using enum_less by auto
        with bad have not: "\<not> ?P (f (enum i)) (f (enum j))" by (auto simp: good_def)
        have "\<not> Q (?f i) (?f j)"
        proof
          assume "Q (?f i) (?f j)"
          moreover with *** obtain x y where "x \<in> B" and "y \<in> B"
            and "f (enum i) = Inr x" and "f (enum j) = Inr y" by blast
          ultimately have "?P (f (enum i)) (f (enum j))" by simp
          then show False using not by simp
        qed
      }
      then have "bad Q ?f" by (auto simp: good_def)
      moreover from `almost_full_on Q B` and B
        have "good Q ?f" by (auto simp: good_def almost_full_on_def)
      ultimately show False by blast
    next
      assume "infinite ?I"
      then have "\<forall>i. \<exists>j>i. j \<in> ?I" by (simp add: infinite_nat_iff_unbounded)
      then interpret infinitely_many1 "\<lambda>i. i \<in> ?I" by (unfold_locales) assumption
      let ?f = "\<lambda>i. projl (f (enum i))"
      have ***: "\<forall>i. \<exists>x\<in>A. f (enum i) = Inl x" using enum_P by auto
      have A: "\<forall>i. ?f i \<in> A"
      proof
        fix i
        from *** obtain x where "x \<in> A" and "f (enum i) = Inl x" by blast
        then show "?f i \<in> A" by simp
      qed
      {
        fix i j :: nat
        assume "i < j"
        then have "enum i < enum j" using enum_less by auto
        with bad have not: "\<not> ?P (f (enum i)) (f (enum j))" by (auto simp: good_def)
        have "\<not> P (?f i) (?f j)"
        proof
          assume "P (?f i) (?f j)"
          moreover with *** obtain x y where "x \<in> A" and "y \<in> A"
            and "f (enum i) = Inl x" and "f (enum j) = Inl y" by blast
          ultimately have "?P (f (enum i)) (f (enum j))" by simp
          then show False using not by simp
        qed
      }
      then have "bad P ?f" by (auto simp: good_def)
      moreover from `almost_full_on P A` and A
        have "good P ?f" by (auto simp: good_def almost_full_on_def)
      ultimately show False by blast
    qed
  qed
qed

lemma almost_full_on_sum_less:
  assumes "almost_full_on (P\<^sup>=\<^sup>=) A" and "almost_full_on (Q\<^sup>=\<^sup>=) B"
  shows "almost_full_on ((sum_less P Q)\<^sup>=\<^sup>=) (A <+> B)"
  using almost_full_on_Plus [OF assms] by simp


subsection {* Dickson's Lemma for Almost-Full Relations *}

text {*When two sets are almost-full, then their Cartesian product is almost-full.*}

definition
  prod_le :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
where
  "prod_le P1 P2 \<equiv> \<lambda>(p1, p2) (q1, q2). P1 p1 q1 \<and> P2 p2 q2"

definition
  prod_less :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
where
  "prod_less P1 P2 = (\<lambda>(p1, p2) (q1, q2).
    (P1\<^sup>=\<^sup>= p1 q1 \<and> P2 p2 q2) \<or> (P1 p1 q1 \<and> P2\<^sup>=\<^sup>= p2 q2))"

lemma reflclp_prod_less [simp]:
  "(prod_less P Q)\<^sup>=\<^sup>= = prod_le (P\<^sup>=\<^sup>=) (Q\<^sup>=\<^sup>=)"
proof (intro ext)
  fix x y
  show "(prod_less P Q)\<^sup>=\<^sup>= x y = prod_le (P\<^sup>=\<^sup>=) (Q\<^sup>=\<^sup>=) x y"
  by (cases x, cases y)
     (auto simp add: prod_le_def prod_less_def)
qed

lemma almost_full_on_Sigma:
  assumes "almost_full_on P1 A1" and "almost_full_on P2 A2"
  shows "almost_full_on (prod_le P1 P2) (A1 \<times> A2)"
    (is "almost_full_on ?P ?A")
proof (rule ccontr)
  assume "\<not> almost_full_on ?P ?A"
  then obtain f where f: "\<forall>i. f i \<in> ?A"
    and bad: "bad ?P f" by (auto simp: almost_full_on_def)
  let ?W = "\<lambda>x y. P1 (fst x) (fst y)"
  let ?B = "\<lambda>x y. P2 (snd x) (snd y)"
  from f have fst: "\<forall>i. fst (f i) \<in> A1" and snd: "\<forall>i. snd (f i) \<in> A2"
    by (metis SigmaE fst_conv, metis SigmaE snd_conv)
  from almost_full_on_imp_homogeneous_subseq [OF assms(1) fst]
    obtain \<phi> :: "nat seq" where mono: "\<And>i j. i < j \<Longrightarrow> \<phi> i < \<phi> j"
    and *: "\<And>i j. i < j \<Longrightarrow> ?W (f (\<phi> i)) (f (\<phi> j))" by auto
  from snd have "\<forall>i. snd (f (\<phi> i)) \<in> A2" by auto
  then have "snd \<circ> f \<circ> \<phi> \<in> SEQ A2" by auto
  with assms(2) have "good P2 (snd \<circ> f \<circ> \<phi>)" by (auto simp: almost_full_on_def)
  then obtain i j :: nat
    where "i < j" and "?B (f (\<phi> i)) (f (\<phi> j))" by auto
  with * [OF `i < j`] have "?P (f (\<phi> i)) (f (\<phi> j))" by (simp add: case_prod_beta prod_le_def)
  with mono [OF `i < j`] and bad show False by auto
qed

lemma almost_full_on_prod_less:
  assumes "almost_full_on (P1\<^sup>=\<^sup>=) A1" and "almost_full_on (P2\<^sup>=\<^sup>=) A2"
  shows "almost_full_on ((prod_less P1 P2)\<^sup>=\<^sup>=) (A1 \<times> A2)"
  using almost_full_on_Sigma [OF assms] by simp


subsection {* List Embedding *}

lemma reflp_on_list_hembeq:
  shows "reflp_on (list_hembeq P) (lists A)"
  using list_hembeq_refl
  unfolding reflp_on_def by blast

lemma transp_on_list_hembeq:
  assumes "transp_on P A"
  shows "transp_on (list_hembeq P) (lists A)"
  using assms and list_hembeq_trans [of A P]
    unfolding transp_on_def by metis


subsection {* Higman's Lemma for Almost-Full Relations *}

lemma Nil_imp_good_list_hembeq [simp]:
  assumes "f i = []"
  shows "good (list_hembeq P) f"
proof (rule ccontr)
  assume "bad (list_hembeq P) f"
  moreover have "(list_hembeq P) (f i) (f (Suc i))"
    unfolding assms by auto
  ultimately show False
    unfolding good_def by auto
qed

lemma wf_length:
  "wf {(x, y). length x < length y}"
  unfolding wf_def using length_induct by auto

lemma wfp_on_length:
  "wfp_on (\<lambda>x y. length x < length y) (lists A)"
  using wf_length [to_pred, unfolded wfp_on_UNIV [symmetric]]
    and wfp_on_subset [of "lists A" UNIV] by blast

lemma ne_lists:
  assumes "xs \<noteq> []" and "xs \<in> lists A"
  shows "hd xs \<in> A" and "tl xs \<in> lists A"
  using assms by (case_tac [!] xs) simp_all

lemma almost_full_on_lists:
  assumes "almost_full_on P A"
  shows "almost_full_on (list_hembeq P) (lists A)" (is "almost_full_on ?P ?A")
proof (rule ccontr)
  interpret mbs "\<lambda>xs ys. length xs < length ys" ?A
    by (unfold_locales) (auto simp: wfp_on_length)
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
    moreover with P have "P\<^sup>=\<^sup>= (h (\<phi> i)) (h (\<phi> j))" by blast
    ultimately have "?P (m (\<phi> i)) (m (\<phi> j))"
      by (subst (1 2) m) (rule list_hembeq_Cons2, auto)
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
      from list_hembeq_Cons [OF this, of "h (\<phi> (j - \<phi> 0))"]
        have "?P (m i) (m (\<phi> (j - \<phi> 0)))" using ne by (simp add: h_def t_def)
      moreover have "i < \<phi> (j - \<phi> 0)"
        using less [of 0 "j - \<phi> 0"] and `i < \<phi> 0` and `\<phi> 0 \<le> j`
        by (cases "j = \<phi> 0") auto
      ultimately have False using bad by blast }
    ultimately show False using `i < j` by arith
  qed
  ultimately show False using min by blast
qed

definition
  list_hemb :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "list_hemb P xs ys = (list_hembeq P xs ys \<and> xs \<noteq> ys)"

lemma list_hembeq_eq_length_induct [consumes 2, case_names Nil Cons]:
  assumes "length xs = length ys"
    and "list_hembeq P xs ys"
    and "\<And>ys. Q [] ys"
    and "\<And>x y xs ys. \<lbrakk>P\<^sup>=\<^sup>= x y; list_hembeq P xs ys; Q xs ys\<rbrakk> \<Longrightarrow> Q (x#xs) (y#ys)"
  shows "Q xs ys"
  using assms(2, 1)
proof (induct)
  case (list_hembeq_Nil ys)
  show ?case by fact
next
  case (list_hembeq_Cons xs ys y)
  with list_hembeq_length have "length xs \<le> length ys" by blast
  with `length xs = length (y#ys)` show ?case by auto
next
  case (list_hembeq_Cons2 x y xs ys)
  with assms(4) show ?case by auto
qed

lemma list_hembeq_eq_length_le:
  assumes "length xs = length ys"
    and "list_hembeq P xs ys"
  shows "\<forall>i<length xs. P\<^sup>=\<^sup>= (xs ! i) (ys ! i)"
  using assms
proof (induct rule: list_hembeq_eq_length_induct)
  case Nil show ?case by simp
next
  case (Cons x y xs ys)
  show ?case
  proof (intro allI impI)
    fix i assume "i < length (x # xs)"
    with Cons show "P\<^sup>=\<^sup>= ((x#xs)!i) ((y#ys)!i)"
      by (cases i) simp_all
  qed
qed

lemma transp_on_list_hemb:
  assumes irrefl: "irreflp_on P A"
    and trans: "transp_on P A"
  shows "transp_on (list_hemb P) (lists A)"
    (is "transp_on ?P ?A")
proof
  fix xs ys zs
  assume "xs \<in> ?A" and "ys \<in> ?A" and "zs \<in> ?A"
    and "?P xs ys" and "?P ys zs"
  moreover then have "list_hembeq P xs ys" and "list_hembeq P ys zs"
    and "xs \<noteq> ys" and "ys \<noteq> zs" unfolding list_hemb_def by auto
  ultimately have "list_hembeq P xs zs"
    using transp_on_list_hembeq [OF trans]
    unfolding transp_on_def by blast
  moreover have "xs \<noteq> zs"
  proof
    assume "xs = zs"
    moreover from list_hembeq_length and `list_hembeq P xs ys` and `list_hembeq P ys zs`
      have "length xs \<le> length ys" and "length ys \<le> length zs" by blast+
    ultimately have "length xs = length ys" and "length ys = length zs" by auto
    with list_hembeq_eq_length_le and `list_hembeq P xs ys` and `list_hembeq P ys zs`
      have *: "\<forall>i<length xs. P\<^sup>=\<^sup>= (xs!i) (ys!i)"
      and **: "\<forall>i<length ys. P\<^sup>=\<^sup>= (ys!i) (zs!i)" by blast+
    show False
    proof (cases "\<exists>i<length xs. P (xs!i) (ys!i) \<and> P (ys!i) (zs!i)")
      case True
      then obtain i where "i < length xs"
        and "P (xs ! i) (ys ! i)" and "P (ys ! i) (zs ! i)" by blast+
      moreover have "xs ! i \<in> A" and "ys ! i \<in> A" and "zs ! i \<in> A"
        using `xs \<in> ?A` and `ys \<in> ?A` and `zs \<in> ?A`
        and `i < length xs`
        and `length xs = length ys`
        and `length ys = length zs`
        by auto
      ultimately have "P (xs ! i) (zs ! i)"
        using trans
        unfolding transp_on_def
        by blast
      with irrefl and `xs ! i \<in> A` and `zs ! i \<in> A`
        have "xs ! i \<noteq> zs ! i" unfolding irreflp_on_def by auto
      with `xs = zs` and `i < length xs`
        and `length xs = length ys`
        and `length ys = length zs`
        show False by auto
    next
      case False
      with * and ** and `length xs = length ys`
        have "\<forall>i<length xs. xs ! i = ys ! i \<or> ys ! i = zs ! i" by auto
      with `xs = zs` and `xs \<noteq> ys` and `ys \<noteq> zs`
        show False using `length xs = length ys`
        by (metis list_eq_iff_nth_eq)
    qed
  qed
  ultimately show "?P xs zs" by (auto simp: list_hemb_def)
qed

lemma list_hembeq_reflclp [simp]:
  "list_hembeq (P\<^sup>=\<^sup>=) = list_hembeq P" (is "?l = ?r")
proof (intro ext)
  fix s t
  show "?l s t = ?r s t"
  proof
    assume "?l s t" then show "?r s t" by (induct) auto
  next
    assume "?r s t" then show "?l s t" by (induct) auto
  qed
qed

lemma reflclp_list_hemb [simp]:
  "(list_hemb P)\<^sup>=\<^sup>= = list_hembeq P" (is "?l = ?r")
  by (intro ext) (auto simp: list_hemb_def)

lemma almost_full_on_list_hemb:
  assumes "almost_full_on (P\<^sup>=\<^sup>=) A"
  shows "almost_full_on ((list_hemb P)\<^sup>=\<^sup>=) (lists A)"
  using almost_full_on_lists [OF assms] by simp


subsection {* Special Case: Finite Sets *}

text {*Every reflexive relation on a finite set is almost full.*}
lemma finite_almost_full_on:
  assumes finite: "finite A"
  assumes refl: "reflp_on P A"
  shows "almost_full_on P A"
proof
  fix f :: "'a seq"
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
      by (metis list_hembeq_length)
  next
    have "finite (UNIV :: bool set)" by auto
    from almost_full_on_lists [OF eq_almost_full_on_finite_set [OF this]]
      show "almost_full_on ?P UNIV" unfolding lists_UNIV .
  qed
  then show ?thesis unfolding * .
qed


subsection {* Further Results *}

text {*Given a quasi-order @{term P}, the following statements are equivalent:
\begin{enumerate}
\item @{term P} is almost-full.
\item @{term P} does neither allow decreasing chains nor antichains.
\item Every quasi-order extending @{term P} is well-founded.
\end{enumerate}
*}

lemma qo_af_imp_wf_and_no_antichain:
  assumes qo: "qo_on P A"
    and af: "almost_full_on P A"
  shows qo_af_imp_wf: "wfp_on (strict P) A"
    and qo_af_imp_no_antichain: "\<not> (\<exists>f. antichain_on P f A)"
proof -
  show "wfp_on (strict P) A"
  proof (unfold wfp_on_def, rule notI)
    assume "\<exists>f. \<forall>i. f i \<in> A \<and> strict P (f (Suc i)) (f i)"
    then obtain f where *: "chain_on ((strict P)\<inverse>\<inverse>) f A" by blast
    from chain_on_transp_on_less [OF this]
      and transp_on_strict [THEN transp_on_converse, OF qo [THEN qo_on_imp_transp_on]]
      have "\<forall>i j. i < j \<longrightarrow> \<not> P (f i) (f j)" by blast
    with af show False
      using * by (auto simp: almost_full_on_def good_def)
  qed
next
  from almost_full_on_imp_no_antichain_on [of P A] and assms
    show "\<not> (\<exists>f. antichain_on P f A)" by (auto)
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
          by (metis (lifting, mono_tags) max.semilattice_strict_iff_order relcompp.relcompI tranclp_into_tranclp2)
        then show False by auto
      qed
      with A [of i] show "f i \<in> A \<and> strict Q (f (Suc i)) (f i)" by auto
    qed
    ultimately show False unfolding wfp_on_def by blast  
  qed
qed

lemma po_af_imp_wf_and_no_antichain:
  assumes po: "po_on P A"
    and af: "almost_full_on (P\<^sup>=\<^sup>=) A"
  shows po_af_imp_wf: "wfp_on P A"
    and po_af_imp_no_antichain: "\<not> (\<exists>f. antichain_on (P\<^sup>=\<^sup>=) f A)"
proof -
  show "wfp_on P A"
  proof (unfold wfp_on_def, rule notI)
    assume "\<exists>f. \<forall>i. f i \<in> A \<and> P (f (Suc i)) (f i)"
    then obtain f where A: "\<And>i. f i \<in> A"
      and *: "chain_on (P\<inverse>\<inverse>) f A" by blast
    from chain_on_transp_on_less [OF * transp_on_converse [OF po [THEN po_on_imp_transp_on]]]
      have "\<forall>i j. i < j \<longrightarrow> P (f j) (f i)" by blast
    then have "\<forall>i j. i < j \<longrightarrow> \<not> P\<^sup>=\<^sup>= (f i) (f j)"
      using po_on_imp_antisymp_on [OF po] and A
      and po_on_imp_irreflp_on [OF po]
      unfolding antisymp_on_def irreflp_on_def
      by (metis sup2CI)
    with af show False
      using * by (auto simp: almost_full_on_def good_def)
  qed
next
  from almost_full_on_imp_no_antichain_on [of "P\<^sup>=\<^sup>=" A] and assms
    show "\<not> (\<exists>f. antichain_on (P\<^sup>=\<^sup>=) f A)" by (auto)
qed

lemma wf_and_no_antichain_imp_po_extension_wf:
  assumes wf: "wfp_on P A"
    and anti: "\<not> (\<exists>f. antichain_on (P\<^sup>=\<^sup>=) f A)"
    and subrel: "\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> Q x y"
    and po: "po_on Q A"
  shows "wfp_on Q A"
proof (rule ccontr)
  have "transp_on Q A"
    using po unfolding po_on_def transp_on_def by blast
  then have *: "transp_on (Q\<inverse>\<inverse>) A" by (rule transp_on_converse)
  assume "\<not> wfp_on Q A"
  then obtain f :: "nat \<Rightarrow> 'a" where A: "\<And>i. f i \<in> A"
    and "\<forall>i. Q (f (Suc i)) (f i)" unfolding wfp_on_def by blast+
  then have "chain_on (Q\<inverse>\<inverse>) f A" by auto
  from chain_on_transp_on_less [OF this *]
    have "\<And>i j. i < j \<Longrightarrow> Q (f j) (f i)" by blast
  then have "\<And>i j. i < j \<Longrightarrow> \<not> Q\<^sup>=\<^sup>= (f i) (f j)"
      using po_on_imp_antisymp_on [OF po] and A
      and po_on_imp_irreflp_on [OF po]
      unfolding antisymp_on_def irreflp_on_def
      by (metis sup2CI)
  then have *: "\<And>i j. i < j \<Longrightarrow> \<not> P\<^sup>=\<^sup>= (f i) (f j)"
    using subrel and A by blast
  show False
  proof (cases)
    assume "\<exists>k. \<forall>i>k. \<exists>j>i. P\<^sup>=\<^sup>= (f j) (f i)"
    then obtain k where "\<forall>i>k. \<exists>j>i. P\<^sup>=\<^sup>= (f j) (f i)" by auto
    from subchain [of k _ f, OF this] obtain g
      where "\<And>i j. i < j \<Longrightarrow> g i < g j"
      and "\<And>i. P\<^sup>=\<^sup>= (f (g (Suc i))) (f (g i))" by auto
    with * have "\<And>i. P (f (g (Suc i))) (f (g i))"
    by (metis lessI strict_reflclp_conv)
    with wf [unfolded wfp_on_def not_ex, THEN spec, of "\<lambda>i. f (g i)"] and A
      show False by fast
  next
    assume "\<not> (\<exists>k. \<forall>i>k. \<exists>j>i. P\<^sup>=\<^sup>= (f j) (f i))"
    then have "\<forall>k. \<exists>i>k. \<forall>j>i. \<not> P\<^sup>=\<^sup>= (f j) (f i)" by auto
    from choice [OF this] obtain h
      where "\<forall>k. h k > k"
      and **: "\<forall>k. (\<forall>j>h k. \<not> P\<^sup>=\<^sup>= (f j) (f (h k)))" by auto
    def [simp]: \<phi> \<equiv> "\<lambda>i. (h ^^ Suc i) 0"
    have "\<And>i. \<phi> i < \<phi> (Suc i)"
      using `\<forall>k. h k > k` by (induct_tac i) auto
    then have mono: "\<And>i j. i < j \<Longrightarrow> \<phi> i < \<phi> j" by (metis lift_Suc_mono_less)
    then have "\<forall>i j. i < j \<longrightarrow> \<not> P\<^sup>=\<^sup>= (f (\<phi> j)) (f (\<phi> i))"
      using ** by auto
    with mono [THEN *]
      have "\<forall>i j. i < j \<longrightarrow> incomparable (P\<^sup>=\<^sup>=) (f (\<phi> j)) (f (\<phi> i))" by blast
    moreover have "\<exists>i j. i < j \<and> \<not> incomparable (P\<^sup>=\<^sup>=) (f (\<phi> i)) (f (\<phi> j))"
      using anti [unfolded not_ex, THEN spec, of "\<lambda>i. f (\<phi> i)"] and A by blast
    ultimately show False by blast
  qed
qed

lemma every_po_extension_wf_imp_af:
  assumes ext: "\<forall>Q. (\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> Q x y) \<and>
    po_on Q A \<longrightarrow> wfp_on Q A"
    and "po_on P A"
  shows "almost_full_on (P\<^sup>=\<^sup>=) A"
proof
  from `po_on P A`
    have irrefl: "irreflp_on P A"
    and trans: "transp_on P A"
    by (auto intro: po_on_imp_irreflp_on po_on_imp_transp_on)

  fix f :: "nat \<Rightarrow> 'a"
  assume "\<forall>i. f i \<in> A"
  then have A: "\<And>i. f i \<in> A" ..
  show "good (P\<^sup>=\<^sup>=) f"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have bad: "\<forall>i j. i < j \<longrightarrow> \<not> P\<^sup>=\<^sup>= (f i) (f j)" by (auto simp: good_def)
    then have *: "\<And>i j. P\<^sup>=\<^sup>= (f i) (f j) \<Longrightarrow> i \<ge> j" by (metis not_leE)
  
    def [simp]: D \<equiv> "\<lambda>x y. \<exists>i. x = f (Suc i) \<and> y = f i"
    def P' \<equiv> "restrict_to P A"
    def [simp]: Q \<equiv> "(sup P' D)\<^sup>+\<^sup>+"

    have **: "\<And>i j. (D OO P'\<^sup>*\<^sup>*)\<^sup>+\<^sup>+ (f i) (f j) \<Longrightarrow> i > j"
    proof -
      fix i j
      assume "(D OO P'\<^sup>*\<^sup>*)\<^sup>+\<^sup>+ (f i) (f j)"
      then show "i > j"
        apply (induct "f i" "f j" arbitrary: j)
        apply (insert A, auto dest!: * simp: P'_def)
        apply (simp only: restrict_to_rtranclp [OF trans])
        apply (metis (full_types) "*" Suc_n_not_le_n le_trans not_le sup2CI)
        by (metis (hide_lams, no_types) "*" dual_order.strict_trans less_Suc_eq_le restrict_to_rtranclp trans)
    qed

    have "irreflp_on Q A"
    proof
      fix x
      assume *: "x \<in> A"
      show "\<not> Q x x"
      proof
        assume "Q x x"
        then have "(sup P' D)\<^sup>+\<^sup>+ x x" by auto
        moreover have "(sup P' D)\<^sup>+\<^sup>+ = sup (P'\<^sup>+\<^sup>+) (P'\<^sup>*\<^sup>* OO (D OO P'\<^sup>*\<^sup>*)\<^sup>+\<^sup>+)"
        proof -
          have "\<And>A B. (A \<union> B)\<^sup>+ = A\<^sup>+ \<union> A\<^sup>* O (B O A\<^sup>*)\<^sup>+" by regexp
          from this [to_pred] show ?thesis by blast
        qed
        ultimately have "sup (P'\<^sup>+\<^sup>+) (P'\<^sup>*\<^sup>* OO (D OO P'\<^sup>*\<^sup>*)\<^sup>+\<^sup>+) x x" by simp
        then have "(P'\<^sup>*\<^sup>* OO (D OO P'\<^sup>*\<^sup>*)\<^sup>+\<^sup>+) x x"
          using * and `po_on P A`
          by (metis P'_def ext irreflp_on_def sup2E wfp_on_imp_irreflp_on wfp_on_restrict_to_tranclp_wfp_on_conv)
        then obtain b where "P'\<^sup>*\<^sup>* x b" and "(D OO P'\<^sup>*\<^sup>*)\<^sup>+\<^sup>+ b x" by blast
        moreover from `(D OO P'\<^sup>*\<^sup>*)\<^sup>+\<^sup>+ b x` obtain i
          where [simp]: "b = f i" by (induct) auto
        ultimately have "((D OO P'\<^sup>*\<^sup>*)\<^sup>+\<^sup>+ OO P'\<^sup>*\<^sup>*) (f i) (f i)" by auto
        moreover have "(D OO P'\<^sup>*\<^sup>*)\<^sup>+\<^sup>+ OO P'\<^sup>*\<^sup>* = (D OO P'\<^sup>*\<^sup>*)\<^sup>+\<^sup>+"
        proof -
          have "\<And>A B. (A O B\<^sup>*)\<^sup>+ O B\<^sup>* = (A O B\<^sup>*)\<^sup>+" by regexp
          from this [to_pred] show ?thesis .
        qed
        ultimately have "(D OO P'\<^sup>*\<^sup>*)\<^sup>+\<^sup>+ (f i) (f i)" by auto
        with ** show False by blast
      qed
    qed
    moreover have "transp_on Q A" by (auto simp: transp_on_def)
    ultimately have "po_on Q A" by (auto simp: po_on_def)
    moreover have "\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> Q x y" by (auto simp: P'_def)
    ultimately have "wfp_on Q A"
        using ext [THEN spec, of Q] by blast
    moreover have "\<forall>i. Q (f (Suc i)) (f i)" by auto
    ultimately show False using A unfolding wfp_on_def by blast
  qed
qed

end

